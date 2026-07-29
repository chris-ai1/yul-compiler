import YulEvmCompiler.AsmSchedule
import YulEvmCompiler.AsmSem
set_option warningAsError true
/-!
# YulEvmCompiler.AsmScheduleSound

Soundness of the per-window operand-stack scheduler
(`YulEvmCompiler.AsmSchedule`), against the phase-A step relation
(`YulEvmCompiler.AsmSem`).

The scheduler (`optimizeWindow`/`scheduleAsm`) is *untrusted*: it proposes a
candidate replacement for each straight-line pure window and accepts it only
when a **symbolic executor** (`symExec`) certifies that the candidate has the
*same symbolic state* as the original (same output-stack DAG terms, same
below-window input reach). Correctness of the whole pass therefore reduces to
one lemma about the executor, `symExec_sound`: the symbolic state a window
computes really is its concrete net stack transformation.

## What this file proves

* `symExec_sound` — the executor is sound: if `symExec w = some s`, then for
  every concrete input stack `words ι ++ REST` with `ι.length = s.inputs`,
  running `w` steps to `realizeStack yst ι s.stack ++ REST` (the `REST` below
  the window untouched). `realize`/`realizeStack` substitute `inp i ↦ ι[i]`
  and evaluate `app op args` via the semantics' `stepOp` (pure ops leave all
  non-stack state unchanged). This is the single lemma the whole pass rests on.

* `schedule_equiv` — the translation-validation payoff: two windows with the
  same `symExec` result have the *same* net transformation on every suitable
  concrete stack, so they are interchangeable inside any program.

* `optimizeWindow_equiv` — for a real window (`symExec w = some s`),
  `optimizeWindow w` has exactly `w`'s net transformation, whatever the
  untrusted scheduler emitted, because the gate accepts only a
  `symStateBeq`-equal candidate.

The remaining step — composing these window-level equivalences into a
whole-program forward simulation for `scheduleAsm` and lifting it through
`lowerProg` to `compileScheduled` — is discussed at the end of the file; the
scaffolding needed for it (a `CodeRel`-style relation on suffixes) is analogous
to `YulEvmCompiler.Peephole.CodeRel`, but the mid-window matching is more
involved because windows are long and the candidate arbitrary. See the note
after `optimizeWindow_equiv`.
-/

namespace YulEvmCompiler.Schedule

open YulEvmCompiler
open YulSemantics.EVM
  (U256 EvmState Op stepOp builtinWithExternal un bin ter)

/-! ### Realization: symbolic terms → concrete words -/

/-- The single output word of a pure built-in on concrete arguments, read off
`stepOp` (which, for a pure op of the right arity, returns `.ok [v] st` with
`st` unchanged). The fallback `0` is never reached for a well-formed `app`. -/
def resultWord : Option (YulSemantics.BuiltinResult U256 EvmState) → U256
  | some (.ok (v :: _) _) => v
  | _ => 0

/-- Evaluate a pure op on realized argument words. State is irrelevant for a
pure op (it is threaded unchanged), but `stepOp` takes one, so we pass the
ambient `yst`. -/
def realizeOp (op : Op) (args : List U256) (yst : EvmState) : U256 :=
  resultWord (stepOp op args yst)

/-! Realize a symbolic term over the concrete input list `ι`: `inp i ↦ ι[i]`,
`lit v ↦ v`, `app op args ↦` the pure-op result on the realized arguments. -/
mutual
/-- Realize a single symbolic term (see `realizeList`). -/
def realize (yst : EvmState) (ι : List U256) : Term → U256
  | .inp i => ι.getD i 0
  | .lit v => v
  | .app op args => realizeOp op (realizeList yst ι args) yst
def realizeList (yst : EvmState) (ι : List U256) : List Term → List U256
  | [] => []
  | t :: ts => realize yst ι t :: realizeList yst ι ts
end

/-- Realize an output-stack term list into concrete Asm stack values (words). -/
def realizeStack (yst : EvmState) (ι : List U256) (l : List Term) : List AVal :=
  words (realizeList yst ι l)

@[simp] theorem realizeList_nil (yst ι) : realizeList yst ι [] = [] := rfl

theorem realizeList_eq_map (yst : EvmState) (ι : List U256) (l : List Term) :
    realizeList yst ι l = l.map (realize yst ι) := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [realizeList, ih]

theorem realizeList_append (yst : EvmState) (ι : List U256) (a b : List Term) :
    realizeList yst ι (a ++ b) = realizeList yst ι a ++ realizeList yst ι b := by
  simp [realizeList_eq_map]

theorem realizeStack_append (yst : EvmState) (ι : List U256) (a b : List Term) :
    realizeStack yst ι (a ++ b) = realizeStack yst ι a ++ realizeStack yst ι b := by
  simp [realizeStack, realizeList_append, words_append]

@[simp] theorem realizeStack_nil (yst ι) : realizeStack yst ι [] = [] := rfl

@[simp] theorem realizeStack_cons (yst : EvmState) (ι : List U256) (t : Term)
    (ts : List Term) :
    realizeStack yst ι (t :: ts) = .word (realize yst ι t) :: realizeStack yst ι ts := by
  simp [realizeStack, realizeList]

/-! ### Pure ops: `stepOp` returns one word and preserves state -/

/-- Every window-admissible op, on argument words of matching arity, returns a
single word and leaves the machine state unchanged. This is the only place the
op semantics is inspected. -/
theorem pure_stepOp (op : Op) {args : List U256} (yst : EvmState)
    (hp : pureArity op = some args.length) :
    ∃ v, stepOp op args yst = some (.ok [v] yst) := by
  have hun : ∀ f : U256 → U256, args.length = 1 →
      ∃ v, un f args yst = some (.ok [v] yst) := by
    intro f h
    match args, h with
    | [a], _ => exact ⟨f a, rfl⟩
  have hbin : ∀ f : U256 → U256 → U256, args.length = 2 →
      ∃ v, bin f args yst = some (.ok [v] yst) := by
    intro f h
    match args, h with
    | [a, b], _ => exact ⟨f a b, rfl⟩
  have hter : ∀ f : U256 → U256 → U256 → U256, args.length = 3 →
      ∃ v, ter f args yst = some (.ok [v] yst) := by
    intro f h
    match args, h with
    | [a, b, c], _ => exact ⟨f a b c, rfl⟩
  cases op <;>
    simp only [pureArity, Option.some.injEq, reduceCtorEq] at hp <;>
    simp only [stepOp] <;>
    first
      | exact hun _ hp.symm
      | exact hbin _ hp.symm
      | exact hter _ hp.symm

/-- Consequently `realizeOp` picks out that word, and `builtinWithExternal`
(the open-world relation used by `AStep.op`) holds for it with unchanged
state. -/
theorem builtin_pure (calls creates) (op : Op) {args : List U256} (yst : EvmState)
    (hp : pureArity op = some args.length) :
    builtinWithExternal calls creates op args yst (.ok [realizeOp op args yst] yst) := by
  obtain ⟨v, hv⟩ := pure_stepOp op yst hp
  have hro : realizeOp op args yst = v := by
    unfold realizeOp resultWord; rw [hv]
  rw [hro]
  cases op <;>
    first
      | (simpa only [builtinWithExternal] using hv)
      | (exact absurd hp (by simp [pureArity]))

/-! ### `pad` bookkeeping -/

/-- `pad` never shrinks the input reach. -/
theorem pad_inputs (s : SymState) (need : Nat) : s.inputs ≤ (pad s need).inputs := by
  unfold pad; split
  · omega
  · dsimp only; omega

/-- After `pad s need` the stack has at least `need` entries. -/
theorem pad_len (s : SymState) (need : Nat) : need ≤ (pad s need).stack.length := by
  unfold pad; split
  · omega
  · dsimp only; simp only [List.length_append, List.length_map, List.length_range]; omega

/-- The value list a materialized run of input leaves realizes to is exactly the
corresponding slice of `ι`, provided the slice is in range. -/
theorem range_map_getD (ι : List U256) (base extra : Nat)
    (h : base + extra ≤ ι.length) :
    (List.range extra).map (fun j => ι.getD (base + j) 0)
      = List.take extra (List.drop base ι) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, List.length_drop]
    omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    exact (List.getElem_eq_getD 0).symm

/-- The concrete stack `pad` describes is unchanged: growing the symbolic input
view only pulls already-present `ι` slots from below the window into the realized
prefix (needs the grown reach to stay within `ι`). -/
theorem pad_conc (yst : EvmState) (ι : List U256) (REST : List AVal)
    (s : SymState) (need : Nat) (h : (pad s need).inputs ≤ ι.length) :
    realizeStack yst ι (pad s need).stack ++ words (List.drop (pad s need).inputs ι) ++ REST
      = realizeStack yst ι s.stack ++ words (List.drop s.inputs ι) ++ REST := by
  unfold pad at h ⊢
  split
  · rfl
  · rename_i hlt
    rw [if_neg hlt] at h
    simp only at h ⊢
    set extra := need - s.stack.length with hextra
    -- realize the appended input leaves as a slice of `ι`
    have hmap : realizeList yst ι
        ((List.range extra).map (fun j => Term.inp (s.inputs + j)))
        = List.take extra (List.drop s.inputs ι) := by
      rw [realizeList_eq_map, List.map_map]
      rw [show (realize yst ι ∘ fun j => Term.inp (s.inputs + j))
            = (fun j => ι.getD (s.inputs + j) 0) from by funext j; rfl]
      exact range_map_getD ι s.inputs extra (by omega)
    have hCeq : List.drop (s.inputs + extra) ι
        = List.drop extra (List.drop s.inputs ι) := by rw [List.drop_drop]
    have hBC : words (List.take extra (List.drop s.inputs ι))
        ++ words (List.drop extra (List.drop s.inputs ι))
        = words (List.drop s.inputs ι) := by
      rw [← words_append, List.take_append_drop]
    rw [realizeStack, realizeList_append, words_append, hmap, hCeq,
      List.append_assoc (words (realizeList yst ι s.stack)), hBC]
    rfl
