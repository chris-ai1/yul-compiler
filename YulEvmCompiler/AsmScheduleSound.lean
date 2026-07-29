import YulEvmCompiler.AsmSchedule
import YulEvmCompiler.AsmSem
set_option warningAsError true
set_option maxRecDepth 4000
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

/-! ### List helpers for the per-instruction cases -/

@[simp] theorem realizeStack_length (yst : EvmState) (ι : List U256) (l : List Term) :
    (realizeStack yst ι l).length = l.length := by
  simp [realizeStack, words, realizeList_eq_map]

theorem realizeList_set (yst : EvmState) (ι : List U256) (l : List Term) (i : Nat)
    (t : Term) :
    realizeList yst ι (l.set i t) = (realizeList yst ι l).set i (realize yst ι t) := by
  simp [realizeList_eq_map, List.map_set]

theorem words_set (l : List U256) (i : Nat) (v : U256) :
    words (l.set i v) = (words l).set i (.word v) := by
  simp [words, List.map_set]

/-- Split a realized stack at index `n` into prefix / element / suffix. -/
theorem realizeStack_split (yst : EvmState) (ι : List U256) (P : List Term) (n : Nat)
    (h : n < P.length) :
    realizeStack yst ι P
      = realizeStack yst ι (P.take n)
        ++ .word (realize yst ι P[n]) :: realizeStack yst ι (P.drop (n + 1)) := by
  conv_lhs => rw [← List.take_append_drop n P]
  rw [realizeStack_append]
  congr 1
  rw [List.drop_eq_getElem_cons h, realizeStack_cons]

/-- Split a realized stack at indices `0` and `n+1` (for the `swap` case). The
middle block `(P.take (n+1)).drop 1` has length `n`. -/
theorem realizeStack_split2 (yst : EvmState) (ι : List U256) (P : List Term) (n : Nat)
    (h : n + 1 < P.length) :
    realizeStack yst ι P
      = .word (realize yst ι P[0])
        :: (realizeStack yst ι ((P.take (n + 1)).drop 1)
            ++ .word (realize yst ι P[n + 1]) :: realizeStack yst ι (P.drop (n + 2))) := by
  rw [realizeStack_split yst ι P (n + 1) h]
  have h0 : (0 : Nat) < (P.take (n + 1)).length := by rw [List.length_take]; omega
  rw [realizeStack_split yst ι (P.take (n + 1)) 0 h0,
    show n + 1 + 1 = n + 2 from by omega]
  simp only [List.take_zero, realizeStack_nil, List.nil_append, Nat.zero_add,
    List.getElem_take, List.cons_append]

/-- The two `List.set`s a symbolic `swap` performs realise to an actual
top/deep exchange. -/
theorem swap_set_eq {α : Type _} {n : Nat} (a b : α) (τ ρ : List α)
    (h : τ.length = n) :
    (((a :: (τ ++ b :: ρ)).set 0 b).set (n + 1) a) = b :: (τ ++ a :: ρ) := by
  rw [List.set_cons_zero, List.set_cons_succ, List.set_append, if_neg (by omega), h,
    Nat.sub_self, List.set_cons_zero]

/-- Realizing a doubly-`set` term list. -/
theorem realizeStack_setset (yst : EvmState) (ι : List U256) (P : List Term)
    (i j : Nat) (a b : Term) :
    realizeStack yst ι ((P.set i a).set j b)
      = ((realizeStack yst ι P).set i (.word (realize yst ι a))).set j
          (.word (realize yst ι b)) := by
  simp only [realizeStack, realizeList_set, words_set]

/-! ### Per-instruction `AStep` packages

Each window instruction's concrete effect, phrased against the realized stack
`realizeStack yst ι P ++ tail`. The `symStep_sound` cases below just supply the
padded stack for `P` and `words (drop …) ++ REST` for `tail`. -/

/-- `dup` copies the realized term at depth `n`. -/
theorem astep_dup_realize [model : ExternalModel] {prog : List Asm}
    (yst : EvmState) (ι : List U256) (tail : List AVal) (P : List Term) (n : Nat)
    (hn16 : n < 16) (h : n < P.length) {rest : List Asm} :
    ASteps (model := model) prog
      ⟨.dup ⟨n, hn16⟩ :: rest, realizeStack yst ι P ++ tail, yst⟩
      ⟨rest, .word (realize yst ι P[n]) :: (realizeStack yst ι P ++ tail), yst⟩ := by
  have hsrc : realizeStack yst ι P ++ tail
      = realizeStack yst ι (P.take n)
        ++ .word (realize yst ι P[n]) :: (realizeStack yst ι (P.drop (n + 1)) ++ tail) := by
    rw [realizeStack_split yst ι P n h]; simp only [List.cons_append, List.append_assoc]
  rw [hsrc]
  exact .single (AStep.dup (n := ⟨n, hn16⟩) (v := .word (realize yst ι P[n]))
    (τ := realizeStack yst ι (P.take n))
    (ρ := realizeStack yst ι (P.drop (n + 1)) ++ tail)
    (by show (realizeStack yst ι (P.take n)).length = n
        rw [realizeStack_length, List.length_take]; omega))

/-- `swap` exchanges the realized top with the realized term at depth `n+1`. -/
theorem astep_swap_realize [model : ExternalModel] {prog : List Asm}
    (yst : EvmState) (ι : List U256) (tail : List AVal) (P : List Term) (n : Nat)
    (hn16 : n < 16) (h : n + 1 < P.length) {rest : List Asm} :
    ASteps (model := model) prog
      ⟨.swap ⟨n, hn16⟩ :: rest, realizeStack yst ι P ++ tail, yst⟩
      ⟨rest, realizeStack yst ι ((P.set 0 P[n + 1]).set (n + 1) P[0]) ++ tail, yst⟩ := by
  have hτlen : (realizeStack yst ι ((P.take (n + 1)).drop 1)).length = n := by
    rw [realizeStack_length, List.length_drop, List.length_take]; omega
  have hsrc : realizeStack yst ι P ++ tail
      = .word (realize yst ι P[0])
        :: (realizeStack yst ι ((P.take (n + 1)).drop 1)
            ++ .word (realize yst ι P[n + 1])
               :: (realizeStack yst ι (P.drop (n + 2)) ++ tail)) := by
    rw [realizeStack_split2 yst ι P n h]; simp only [List.cons_append, List.append_assoc]
  have htgt : realizeStack yst ι ((P.set 0 P[n + 1]).set (n + 1) P[0]) ++ tail
      = .word (realize yst ι P[n + 1])
        :: (realizeStack yst ι ((P.take (n + 1)).drop 1)
            ++ .word (realize yst ι P[0])
               :: (realizeStack yst ι (P.drop (n + 2)) ++ tail)) := by
    rw [realizeStack_setset, realizeStack_split2 yst ι P n h,
      swap_set_eq (.word (realize yst ι P[0])) (.word (realize yst ι P[n + 1]))
        (realizeStack yst ι ((P.take (n + 1)).drop 1))
        (realizeStack yst ι (P.drop (n + 2))) hτlen]
    simp only [List.cons_append, List.append_assoc]
  rw [hsrc, htgt]
  exact .single (AStep.swap (n := ⟨n, hn16⟩) (a := .word (realize yst ι P[0]))
    (b := .word (realize yst ι P[n + 1]))
    (τ := realizeStack yst ι ((P.take (n + 1)).drop 1))
    (ρ := realizeStack yst ι (P.drop (n + 2)) ++ tail) hτlen)

/-- A pure `op` consumes the realized top `k` terms and pushes the realized
`app` term (which is the same pure-op result on their realizations). -/
theorem astep_op_realize [model : ExternalModel] {prog : List Asm}
    (yst : EvmState) (ι : List U256) (tail : List AVal) (P : List Term) (yop : Op)
    (k : Nat) (hpa : pureArity yop = some k) (hk : k ≤ P.length) {rest : List Asm} :
    ASteps (model := model) prog
      ⟨.op yop :: rest, realizeStack yst ι P ++ tail, yst⟩
      ⟨rest, realizeStack yst ι (.app yop (P.take k) :: P.drop k) ++ tail, yst⟩ := by
  have hargk : (realizeList yst ι (P.take k)).length = k := by
    rw [realizeList_eq_map, List.length_map, List.length_take]; omega
  have hsrc : realizeStack yst ι P ++ tail
      = words (realizeList yst ι (P.take k)) ++ (realizeStack yst ι (P.drop k) ++ tail) := by
    conv_lhs => rw [← List.take_append_drop k P, realizeStack_append]
    rw [List.append_assoc]; rfl
  have htgt : realizeStack yst ι (.app yop (P.take k) :: P.drop k) ++ tail
      = .word (realizeOp yop (realizeList yst ι (P.take k)) yst)
        :: (realizeStack yst ι (P.drop k) ++ tail) := by
    rw [realizeStack_cons, realize, List.cons_append]
  rw [hsrc, htgt]
  have hbp := builtin_pure model.calls model.creates yop yst (by rw [hargk]; exact hpa)
  have hstep := AStep.op (model := model) (prog := prog) (yop := yop)
    (args := realizeList yst ι (P.take k)) (rets := [realizeOp yop (realizeList yst ι (P.take k)) yst])
    (c := rest) (σ := realizeStack yst ι (P.drop k) ++ tail) (yst := yst) (yst' := yst) hbp
  simpa [words] using ASteps.single hstep

/-! ### `symStep` equation lemmas

`simp only [symStep]` loops on `symStep`'s generated equation lemmas (the nested
`pad`/`match` structure), so we expose the reductions as plain `rfl` lemmas and
`rw` with them instead. -/

theorem symStep_push (s : SymState) (v : U256) :
    symStep s (.push v) = some { s with stack := .lit v :: s.stack } := rfl

theorem symStep_pop (s : SymState) :
    symStep s .pop = some { (pad s 1) with stack := (pad s 1).stack.drop 1 } := rfl

theorem symStep_dup (s : SymState) (n : Nat) (hn : n < 16) :
    symStep s (.dup ⟨n, hn⟩) =
      (match (pad s (n + 1)).stack[n]? with
       | some t => some { (pad s (n + 1)) with stack := t :: (pad s (n + 1)).stack }
       | none => none) := rfl

theorem symStep_swap (s : SymState) (n : Nat) (hn : n < 16) :
    symStep s (.swap ⟨n, hn⟩) =
      (match (pad s (n + 2)).stack[0]?, (pad s (n + 2)).stack[n + 1]? with
       | some a, some b =>
           some { (pad s (n + 2)) with
             stack := ((pad s (n + 2)).stack.set 0 b).set (n + 1) a }
       | _, _ => none) := rfl

theorem symStep_op (s : SymState) (yop : Op) :
    symStep s (.op yop) =
      (match pureArity yop with
       | some k =>
           some { stack := .app yop ((pad s k).stack.take k) :: (pad s k).stack.drop k,
                  inputs := (pad s k).inputs,
                  opExposed := ((pad s k).stack.take k).filterMap
                      (fun t => match t with | .inp i => some i | _ => none)
                    ++ (pad s k).opExposed }
       | none => none) := rfl

theorem symStep_label (s : SymState) (l : Label) : symStep s (.label l) = none := rfl
theorem symStep_jump (s : SymState) (l : Label) : symStep s (.jump l) = none := rfl
theorem symStep_jumpi (s : SymState) (l : Label) : symStep s (.jumpi l) = none := rfl
theorem symStep_pushLabel (s : SymState) (l : Label) :
    symStep s (.pushLabel l) = none := rfl
theorem symStep_dynJump (s : SymState) : symStep s .dynJump = none := rfl

/-! ### Single symbolic step is sound -/

/-- One symbolic step of a window-admissible instruction is realised by one
concrete `AStep`. The invariant is that the concrete stack is
`realizeStack yst ι s.stack ++ words (drop s.inputs ι) ++ REST`: the realized
output terms on top, then the `ι` slots the window has not yet reached, then the
untouched `REST`. -/
theorem symStep_sound [model : ExternalModel] {prog : List Asm}
    (yst : EvmState) (ι : List U256) (REST : List AVal)
    {s0 s1 : SymState} {i : Asm} {rest : List Asm}
    (hstep : symStep s0 i = some s1) (hle : s1.inputs ≤ ι.length) :
    ASteps (model := model) prog
      ⟨i :: rest, realizeStack yst ι s0.stack ++ words (List.drop s0.inputs ι) ++ REST, yst⟩
      ⟨rest, realizeStack yst ι s1.stack ++ words (List.drop s1.inputs ι) ++ REST, yst⟩ := by
  cases i with
  | push v =>
    rw [symStep_push, Option.some.injEq] at hstep
    subst hstep
    simp only [realizeStack_cons, realize, List.cons_append]
    exact .single AStep.push
  | pop =>
    rw [symStep_pop, Option.some.injEq] at hstep
    subst hstep
    dsimp only
    have hle' : (pad s0 1).inputs ≤ ι.length := hle
    rw [← pad_conc yst ι REST s0 1 hle']
    obtain ⟨x, xs, hxs⟩ : ∃ x xs, (pad s0 1).stack = x :: xs := by
      have := pad_len s0 1
      match hp : (pad s0 1).stack with
      | [] => rw [hp] at this; simp at this
      | y :: ys => exact ⟨y, ys, rfl⟩
    rw [hxs]
    simp only [realizeStack_cons, List.drop_succ_cons, List.drop_zero, List.cons_append]
    exact .single AStep.pop
  | dup m =>
    obtain ⟨n, hn⟩ := m
    have hpl : n + 1 ≤ (pad s0 (n + 1)).stack.length := pad_len s0 (n + 1)
    have hnth : (pad s0 (n + 1)).stack[n]? = some ((pad s0 (n + 1)).stack[n]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    rw [symStep_dup, hnth, Option.some.injEq] at hstep
    have hle' : (pad s0 (n + 1)).inputs ≤ ι.length := by rw [← hstep] at hle; exact hle
    rw [← hstep]
    dsimp only
    rw [← pad_conc yst ι REST s0 (n + 1) hle']
    set P := (pad s0 (n + 1)).stack with hP
    rw [realizeStack_cons, List.append_assoc, List.append_assoc]
    exact astep_dup_realize yst ι (words (List.drop (pad s0 (n + 1)).inputs ι) ++ REST) P n hn
      (by omega)
  | swap m =>
    obtain ⟨n, hn⟩ := m
    have hpl : n + 2 ≤ (pad s0 (n + 2)).stack.length := pad_len s0 (n + 2)
    have hnth0 : (pad s0 (n + 2)).stack[0]? = some ((pad s0 (n + 2)).stack[0]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hnth1 : (pad s0 (n + 2)).stack[n + 1]? = some ((pad s0 (n + 2)).stack[n + 1]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    rw [symStep_swap, hnth0, hnth1, Option.some.injEq] at hstep
    have hle' : (pad s0 (n + 2)).inputs ≤ ι.length := by rw [← hstep] at hle; exact hle
    rw [← hstep]
    dsimp only
    rw [← pad_conc yst ι REST s0 (n + 2) hle']
    set P := (pad s0 (n + 2)).stack with hP
    rw [List.append_assoc, List.append_assoc]
    exact astep_swap_realize yst ι (words (List.drop (pad s0 (n + 2)).inputs ι) ++ REST) P n hn
      (by omega)
  | op yop =>
    rw [symStep_op] at hstep
    cases hpa : pureArity yop with
    | none => rw [hpa] at hstep; simp at hstep
    | some k =>
      rw [hpa, Option.some.injEq] at hstep
      subst hstep
      dsimp only
      have hle' : (pad s0 k).inputs ≤ ι.length := hle
      rw [← pad_conc yst ι REST s0 k hle']
      set P := (pad s0 k).stack with hP
      rw [List.append_assoc, List.append_assoc]
      exact astep_op_realize yst ι (words (List.drop (pad s0 k).inputs ι) ++ REST) P yop k hpa
        (by have := pad_len s0 k; omega)
  | label l => rw [symStep_label] at hstep; exact absurd hstep (by simp)
  | jump l => rw [symStep_jump] at hstep; exact absurd hstep (by simp)
  | jumpi l => rw [symStep_jumpi] at hstep; exact absurd hstep (by simp)
  | pushLabel l => rw [symStep_pushLabel] at hstep; exact absurd hstep (by simp)
  | dynJump => rw [symStep_dynJump] at hstep; exact absurd hstep (by simp)

/-! ### The window executor is sound -/

/-- A symbolic step never shrinks the input reach. -/
theorem symStep_inputs {s0 s1 : SymState} {i : Asm} (h : symStep s0 i = some s1) :
    s0.inputs ≤ s1.inputs := by
  cases i with
  | push v =>
    rw [symStep_push, Option.some.injEq] at h; have : s1.inputs = s0.inputs := by rw [← h]
    omega
  | pop =>
    rw [symStep_pop, Option.some.injEq] at h
    have : s1.inputs = (pad s0 1).inputs := by rw [← h]
    rw [this]; exact pad_inputs s0 1
  | dup m =>
    obtain ⟨n, hn⟩ := m
    have hpl := pad_len s0 (n + 1)
    have hnth : (pad s0 (n + 1)).stack[n]? = some ((pad s0 (n + 1)).stack[n]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    rw [symStep_dup, hnth, Option.some.injEq] at h
    have : s1.inputs = (pad s0 (n + 1)).inputs := by rw [← h]
    rw [this]; exact pad_inputs s0 (n + 1)
  | swap m =>
    obtain ⟨n, hn⟩ := m
    have hpl := pad_len s0 (n + 2)
    have hnth0 : (pad s0 (n + 2)).stack[0]? = some ((pad s0 (n + 2)).stack[0]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hnth1 : (pad s0 (n + 2)).stack[n + 1]? = some ((pad s0 (n + 2)).stack[n + 1]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    rw [symStep_swap, hnth0, hnth1, Option.some.injEq] at h
    have : s1.inputs = (pad s0 (n + 2)).inputs := by rw [← h]
    rw [this]; exact pad_inputs s0 (n + 2)
  | op yop =>
    rw [symStep_op] at h
    cases hpa : pureArity yop with
    | none => rw [hpa] at h; simp at h
    | some k =>
      rw [hpa, Option.some.injEq] at h
      have : s1.inputs = (pad s0 k).inputs := by rw [← h]
      rw [this]; exact pad_inputs s0 k
  | label l => rw [symStep_label] at h; exact absurd h (by simp)
  | jump l => rw [symStep_jump] at h; exact absurd h (by simp)
  | jumpi l => rw [symStep_jumpi] at h; exact absurd h (by simp)
  | pushLabel l => rw [symStep_pushLabel] at h; exact absurd h (by simp)
  | dynJump => rw [symStep_dynJump] at h; exact absurd h (by simp)

/-- Folding symbolic steps never shrinks the input reach. -/
theorem foldlM_inputs_mono : ∀ (ws : List Asm) (s0 s : SymState),
    ws.foldlM symStep s0 = some s → s0.inputs ≤ s.inputs := by
  intro ws
  induction ws with
  | nil =>
    intro s0 s h
    rw [List.foldlM_nil] at h
    obtain rfl : s0 = s := by simpa using h
    exact Nat.le_refl _
  | cons i ws ih =>
    intro s0 s h
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    exact le_trans (symStep_inputs h1) (ih s1 s h2)

/-- The executor run, strengthened over an arbitrary starting symbolic state and
window suffix. The concrete stack is always
`realizeStack yst ι s.stack ++ words (drop s.inputs ι) ++ REST`. -/
theorem symExec_run [model : ExternalModel] {prog : List Asm}
    (yst : EvmState) (ι : List U256) (REST : List AVal) :
    ∀ (ws : List Asm) (s0 s : SymState) (c : List Asm),
      ws.foldlM symStep s0 = some s → s.inputs ≤ ι.length →
      ASteps (model := model) prog
        ⟨ws ++ c, realizeStack yst ι s0.stack ++ words (List.drop s0.inputs ι) ++ REST, yst⟩
        ⟨c, realizeStack yst ι s.stack ++ words (List.drop s.inputs ι) ++ REST, yst⟩ := by
  intro ws
  induction ws with
  | nil =>
    intro s0 s c h hle
    rw [List.foldlM_nil] at h
    obtain rfl : s0 = s := by simpa using h
    exact .refl _
  | cons i ws ih =>
    intro s0 s c h hle
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    have hle1 : s1.inputs ≤ ι.length := le_trans (foldlM_inputs_mono ws s1 s h2) hle
    have hstep := symStep_sound (prog := prog) (model := model) yst ι REST (rest := ws ++ c) h1 hle1
    have hrec := ih s1 s c h2 hle
    rw [List.cons_append]
    exact hstep.trans hrec

/-- **Executor soundness.** If `symExec w = some s`, then on every concrete input
stack `words ι ++ REST` with `ι.length = s.inputs`, the window `w` steps to
`realizeStack yst ι s.stack ++ REST`: the realized output terms on top and the
`REST` below the window untouched (and the machine state `yst` unchanged, since a
window is pure). -/
theorem symExec_sound [model : ExternalModel] {prog : List Asm}
    {w : List Asm} {s : SymState} (h : symExec w = some s)
    (ι : List U256) (hlen : ι.length = s.inputs) (REST : List AVal)
    (yst : EvmState) (c : List Asm) :
    ASteps (model := model) prog
      ⟨w ++ c, words ι ++ REST, yst⟩
      ⟨c, realizeStack yst ι s.stack ++ REST, yst⟩ := by
  have hrun := symExec_run (prog := prog) (model := model) yst ι REST w
    { stack := [], inputs := 0, opExposed := [] } s c h (le_of_eq hlen.symm)
  simp only [realizeStack_nil, List.drop_zero, List.nil_append] at hrun
  rw [show s.inputs = ι.length from hlen.symm, List.drop_length, words_nil,
    List.append_nil] at hrun
  exact hrun

/-- **Executor soundness at a deeper input count (pad-soundness).** The same
window, fed a stack that supplies *more* words than it reaches (`s.inputs ≤
ι.length`), transforms `words ι ++ REST` to `realizeStack yst ι s.stack ++
words (drop s.inputs ι) ++ REST`: the reached slots are realized and the extra
`ι` slots below the reach pass through as themselves (the window acts as the
identity on slots deeper than `s.inputs`).

This is the net-transform characterization a `symStateEquiv`-style gate needs:
a candidate reaching `c.inputs ≤ s.inputs` slots, when compared after padding its
`SymState` up to `s.inputs`, has this very transform at input count `s.inputs`,
so equal padded states ⇒ equal transforms. It is a pure specialization of
`symExec_run` (which was already stated with `≤`, not `=`), hence gate-agnostic
and true of the current `symExec`. -/
theorem symExec_sound_pad [model : ExternalModel] {prog : List Asm}
    {w : List Asm} {s : SymState} (h : symExec w = some s)
    (ι : List U256) (hle : s.inputs ≤ ι.length) (REST : List AVal)
    (yst : EvmState) (c : List Asm) :
    ASteps (model := model) prog
      ⟨w ++ c, words ι ++ REST, yst⟩
      ⟨c, realizeStack yst ι s.stack ++ words (List.drop s.inputs ι) ++ REST, yst⟩ := by
  have hrun := symExec_run (prog := prog) (model := model) yst ι REST w
    { stack := [], inputs := 0, opExposed := [] } s c h hle
  simpa only [realizeStack_nil, List.drop_zero, List.nil_append] using hrun

/-! ### Translation-validation corollaries

The gate accepts a candidate only when its `SymState` is `symStateBeq`-equal to
the original's. Since `symStateBeq`/`Term.beq` are structural equality, an
accepted candidate has *literally the same* `SymState`, hence — by
`symExec_sound` — the same net transformation. -/

theorem Term.beq_inp (x y : Nat) : Term.beq (.inp x) (.inp y) = (x == y) := rfl
theorem Term.beq_lit (x y : U256) : Term.beq (.lit x) (.lit y) = (x == y) := rfl
theorem Term.beq_app (o1 o2 : Op) (as1 as2 : List Term) :
    Term.beq (.app o1 as1) (.app o2 as2) = (o1 == o2 && Term.beqList as1 as2) := rfl
theorem Term.beqList_cons (x : Term) (xs : List Term) (y : Term) (ys : List Term) :
    Term.beqList (x :: xs) (y :: ys) = (Term.beq x y && Term.beqList xs ys) := rfl

/-! `Term.beq` is genuine structural equality. -/
mutual
theorem Term.beq_eq : ∀ {a b : Term}, Term.beq a b = true → a = b
  | .inp x, .inp y, h => by rw [Term.beq_inp] at h; rw [eq_of_beq h]
  | .lit x, .lit y, h => by rw [Term.beq_lit] at h; rw [eq_of_beq h]
  | .app o1 as1, .app o2 as2, h => by
      rw [Term.beq_app, Bool.and_eq_true] at h
      obtain ⟨ho, has⟩ := h
      rw [of_decide_eq_true ho, Term.beqList_eq has]
  | .inp _, .lit _, h => Bool.noConfusion h
  | .inp _, .app _ _, h => Bool.noConfusion h
  | .lit _, .inp _, h => Bool.noConfusion h
  | .lit _, .app _ _, h => Bool.noConfusion h
  | .app _ _, .inp _, h => Bool.noConfusion h
  | .app _ _, .lit _, h => Bool.noConfusion h
theorem Term.beqList_eq : ∀ {a b : List Term}, Term.beqList a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
      rw [Term.beqList_cons, Bool.and_eq_true] at h
      obtain ⟨hx, hxs⟩ := h
      rw [Term.beq_eq hx, Term.beqList_eq hxs]
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
end

/-- **Translation validation.** Two windows with the same `symExec` result have
the *same* net transformation on every suitable concrete stack — they reach an
identical endpoint. Hence they are interchangeable inside any program. -/
theorem schedule_equiv [model : ExternalModel] {prog : List Asm}
    {w w' : List Asm} {s : SymState}
    (hw : symExec w = some s) (hw' : symExec w' = some s)
    (ι : List U256) (hlen : ι.length = s.inputs) (REST : List AVal)
    (yst : EvmState) (c : List Asm) :
    ASteps (model := model) prog ⟨w ++ c, words ι ++ REST, yst⟩
        ⟨c, realizeStack yst ι s.stack ++ REST, yst⟩
      ∧ ASteps (model := model) prog ⟨w' ++ c, words ι ++ REST, yst⟩
        ⟨c, realizeStack yst ι s.stack ++ REST, yst⟩ :=
  ⟨symExec_sound hw ι hlen REST yst c, symExec_sound hw' ι hlen REST yst c⟩

/-- Realizing the identity-leaf block `pad` appends: it is the corresponding
slice of `ι` (as words). -/
theorem realizeStack_idLeaves (yst : EvmState) (ι : List U256) (base m : Nat)
    (h : base + m ≤ ι.length) :
    realizeStack yst ι ((List.range m).map (fun j => Term.inp (base + j)))
      = words (List.take m (List.drop base ι)) := by
  rw [realizeStack, realizeList_eq_map, List.map_map,
    show ((realize yst ι) ∘ fun j => Term.inp (base + j))
        = (fun j => ι.getD (base + j) 0) from by funext j; rfl,
    range_map_getD ι base m h]

/-- **`symStateEquiv` is net-transform equality.** Two symbolic states the gate
deems `symStateEquiv` induce the *same* concrete transform on any word stack that
supplies at least `max a.inputs b.inputs` slots: the reached outputs realize
equally and the deeper `ι`/`REST` pass through identically. -/
theorem symStateEquiv_transform_eq {a b : SymState} (h : symStateEquiv a b = true)
    (yst : EvmState) (ι : List U256) (hK : Nat.max a.inputs b.inputs ≤ ι.length)
    (REST : List AVal) :
    realizeStack yst ι a.stack ++ words (List.drop a.inputs ι) ++ REST
      = realizeStack yst ι b.stack ++ words (List.drop b.inputs ι) ++ REST := by
  set K := Nat.max a.inputs b.inputs with hKdef
  have hle_a : a.inputs ≤ K := Nat.le_max_left _ _
  have hle_b : b.inputs ≤ K := Nat.le_max_right _ _
  have hpad : a.stack ++ (List.range (K - a.inputs)).map (fun j => Term.inp (a.inputs + j))
            = b.stack ++ (List.range (K - b.inputs)).map (fun j => Term.inp (b.inputs + j)) := by
    apply Term.beqList_eq
    unfold symStateEquiv at h
    simpa [hKdef] using h
  have hr : realizeStack yst ι a.stack ++ words (List.take (K - a.inputs) (List.drop a.inputs ι))
          = realizeStack yst ι b.stack ++ words (List.take (K - b.inputs) (List.drop b.inputs ι)) := by
    have e := congrArg (realizeStack yst ι) hpad
    rw [realizeStack_append, realizeStack_append,
      realizeStack_idLeaves yst ι a.inputs (K - a.inputs) (by omega),
      realizeStack_idLeaves yst ι b.inputs (K - b.inputs) (by omega)] at e
    exact e
  have expand : ∀ m, m ≤ K →
      words (List.drop m ι) = words (List.take (K - m) (List.drop m ι)) ++ words (List.drop K ι) := by
    intro m hm
    conv_lhs => rw [← List.take_append_drop (K - m) (List.drop m ι)]
    rw [words_append, List.drop_drop, show m + (K - m) = K from by omega]
  rw [expand a.inputs hle_a, expand b.inputs hle_b]
  simp only [← List.append_assoc]
  rw [hr]

/-- The gate-fold spec: `optimizeWindow w` is either the original `w`, or a
candidate that is `symStateEquiv` to `target`, has `opExposed ⊆ target.opExposed`,
and does not grow bytes. This is all soundness needs from the untrusted fold. -/
theorem optimizeWindow_spec {w : List Asm} {target : SymState}
    (hw : symExec w = some target) :
    optimizeWindow w = w ∨
      ∃ tcand, symExec (optimizeWindow w) = some tcand
        ∧ symStateEquiv tcand target = true
        ∧ (∀ i ∈ tcand.opExposed, i ∈ target.opExposed)
        ∧ codeSize (optimizeWindow w) ≤ codeSize w := by
  unfold optimizeWindow
  split
  · exact Or.inl rfl
  · rw [hw]
    dsimp only
    split
    · exact Or.inl rfl
    · refine List.foldlRecOn (motive := fun best => best = w ∨
          ∃ tcand, symExec best = some tcand ∧ symStateEquiv tcand target = true
            ∧ (∀ i ∈ tcand.opExposed, i ∈ target.opExposed) ∧ codeSize best ≤ codeSize w)
        _ _ (Or.inl rfl) ?_
      intro best hbest cand _hcand
      split
      · split
        · rename_i tcand hc hgate
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hgate
          obtain ⟨⟨⟨heq, hsub⟩, -⟩, hcs⟩ := hgate
          exact Or.inr ⟨tcand, hc, heq,
            fun i hi => of_decide_eq_true (List.all_eq_true.mp hsub i hi), of_decide_eq_true hcs⟩
        · exact hbest
      · exact hbest

/-- **Window optimization is sound** (against the `symStateEquiv` + `opExposed`
gate). Whatever the untrusted scheduler emitted, `optimizeWindow w` has exactly
`w`'s net transformation over any word stack deep enough for both the original
reach (`target.inputs`) and the optimized window's own reach (`hcand`). The
`symStateEquiv` gate can admit a candidate reaching *deeper* than the original
(leaving the extra slots as identities), so the depth bound is on the optimized
window; the whole-program bridge supplies it from the actual runtime stack. -/
theorem optimizeWindow_equiv [model : ExternalModel] {prog : List Asm}
    {w : List Asm} {target : SymState} (hw : symExec w = some target)
    (ι : List U256) (hle : target.inputs ≤ ι.length)
    (hcandLe : ∀ tcand, symExec (optimizeWindow w) = some tcand → tcand.inputs ≤ ι.length)
    (REST : List AVal) (yst : EvmState) (c : List Asm) :
    ASteps (model := model) prog ⟨optimizeWindow w ++ c, words ι ++ REST, yst⟩
      ⟨c, realizeStack yst ι target.stack ++ words (List.drop target.inputs ι) ++ REST, yst⟩ := by
  rcases optimizeWindow_spec hw with hopt | ⟨tcand, htc, heq, -, -⟩
  · rw [hopt]; exact symExec_sound_pad hw ι hle REST yst c
  · have hti : tcand.inputs ≤ ι.length := hcandLe tcand htc
    have hKle : Nat.max tcand.inputs target.inputs ≤ ι.length := Nat.max_le.mpr ⟨hti, hle⟩
    have hc := symExec_sound_pad (prog := prog) (model := model) htc ι hti REST yst c
    rw [symStateEquiv_transform_eq heq yst ι hKle REST] at hc
    exact hc

/-! ### Structural preservation by `scheduleAsm`

`scheduleAsm` only rewrites label/jump-free windows into label/jump-free code and
copies everything else verbatim, so it preserves `labelDefs`, `labelRefs`, and
never grows `codeSize` — hence it preserves `WFProg`. This is the label-structure
half of what an end-to-end `compileScheduled` correctness proof needs (the other
half — the whole-program forward simulation — is discussed in the closing note). -/

theorem schedulable_op_eq (yop : Op) : schedulable (.op yop) = (pureArity yop).isSome := rfl
theorem schedulable_label_eq (l : Label) : schedulable (.label l) = false := rfl
theorem schedulable_jump_eq (l : Label) : schedulable (.jump l) = false := rfl
theorem schedulable_jumpi_eq (l : Label) : schedulable (.jumpi l) = false := rfl
theorem schedulable_pushLabel_eq (l : Label) : schedulable (.pushLabel l) = false := rfl
theorem schedulable_dynJump_eq : schedulable .dynJump = false := rfl

theorem schedulable_defines {i : Asm} (h : schedulable i = true) : i.defines = none := by
  cases i with
  | label l => rw [schedulable_label_eq] at h; exact absurd h (by simp)
  | _ => rfl

theorem schedulable_references {i : Asm} (h : schedulable i = true) : i.references = none := by
  cases i with
  | jump l => rw [schedulable_jump_eq] at h; exact absurd h (by simp)
  | jumpi l => rw [schedulable_jumpi_eq] at h; exact absurd h (by simp)
  | pushLabel l => rw [schedulable_pushLabel_eq] at h; exact absurd h (by simp)
  | label l => rw [schedulable_label_eq] at h; exact absurd h (by simp)
  | _ => rfl

/-- A successful symbolic step only fires on window-admissible instructions. -/
theorem symStep_some_schedulable {s s' : SymState} {i : Asm}
    (h : symStep s i = some s') : schedulable i = true := by
  cases i with
  | push v => rfl
  | pop => rfl
  | dup n => rfl
  | swap n => rfl
  | op yop =>
    rw [symStep_op] at h
    cases hpa : pureArity yop with
    | none => rw [hpa] at h; exact absurd h (by simp)
    | some k => rw [schedulable_op_eq, hpa]; rfl
  | label l => rw [symStep_label] at h; exact absurd h (by simp)
  | jump l => rw [symStep_jump] at h; exact absurd h (by simp)
  | jumpi l => rw [symStep_jumpi] at h; exact absurd h (by simp)
  | pushLabel l => rw [symStep_pushLabel] at h; exact absurd h (by simp)
  | dynJump => rw [symStep_dynJump] at h; exact absurd h (by simp)

/-- A window-admissible instruction always steps symbolically. -/
theorem symStep_isSome_of_schedulable (s : SymState) {i : Asm}
    (h : schedulable i = true) : (symStep s i).isSome := by
  cases i with
  | push v => rw [symStep_push]; rfl
  | pop => rw [symStep_pop]; rfl
  | dup n =>
    obtain ⟨n, hn⟩ := n
    rw [symStep_dup,
      List.getElem?_eq_getElem (l := (pad s (n+1)).stack) (i := n)
        (by have := pad_len s (n+1); omega)]
    rfl
  | swap n =>
    obtain ⟨n, hn⟩ := n
    rw [symStep_swap,
      List.getElem?_eq_getElem (l := (pad s (n+2)).stack) (i := 0)
        (by have := pad_len s (n+2); omega),
      List.getElem?_eq_getElem (l := (pad s (n+2)).stack) (i := n+1)
        (by have := pad_len s (n+2); omega)]
    rfl
  | op yop =>
    rw [symStep_op]
    cases hpa : pureArity yop with
    | none => rw [schedulable_op_eq, hpa] at h; exact absurd h (by simp)
    | some k => rfl
  | label l => rw [schedulable_label_eq] at h; exact absurd h (by simp)
  | jump l => rw [schedulable_jump_eq] at h; exact absurd h (by simp)
  | jumpi l => rw [schedulable_jumpi_eq] at h; exact absurd h (by simp)
  | pushLabel l => rw [schedulable_pushLabel_eq] at h; exact absurd h (by simp)
  | dynJump => rw [schedulable_dynJump_eq] at h; exact absurd h (by simp)

/-- Every instruction reached by a successful `foldlM symStep` is admissible. -/
theorem foldlM_all_schedulable : ∀ (w : List Asm) {s0 s : SymState},
    w.foldlM symStep s0 = some s → ∀ i ∈ w, schedulable i = true := by
  intro w
  induction w with
  | nil => intro s0 s _ i hi; exact absurd hi (by simp)
  | cons j w ih =>
    intro s0 s h i hi
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    rcases List.mem_cons.mp hi with rfl | hi
    · exact symStep_some_schedulable h1
    · exact ih h2 i hi

/-- A window of admissible instructions always symbolically executes. -/
theorem symExec_isSome_of_schedulable {w : List Asm}
    (h : ∀ i ∈ w, schedulable i = true) : (symExec w).isSome := by
  unfold symExec
  suffices hgen : ∀ (v : List Asm) (s0 : SymState), (∀ i ∈ v, schedulable i = true) →
      (v.foldlM symStep s0).isSome by exact hgen w _ h
  intro v
  induction v with
  | nil => intro s0 _; rw [List.foldlM_nil]; rfl
  | cons j v ih =>
    intro s0 hv
    rw [List.foldlM_cons]
    obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.mp
      (symStep_isSome_of_schedulable s0 (hv j List.mem_cons_self))
    rw [hs1]
    exact ih s1 (fun i hi => hv i (List.mem_cons_of_mem _ hi))

theorem labelDefs_eq_nil_of_schedulable {w : List Asm}
    (h : ∀ i ∈ w, schedulable i = true) : labelDefs w = [] := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [labelDefs_cons, schedulable_defines (h i List.mem_cons_self), Option.toList_none,
      List.nil_append]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem labelRefs_eq_nil_of_schedulable {w : List Asm}
    (h : ∀ i ∈ w, schedulable i = true) : labelRefs w = [] := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [labelRefs_cons, schedulable_references (h i List.mem_cons_self), Option.toList_none,
      List.nil_append]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- `optimizeWindow` output is label-free (every instruction is admissible,
because `symExec` accepts it — the original when unchanged, the candidate only
when it symbolically executes). -/
theorem optimizeWindow_all_schedulable {w : List Asm}
    (hw : ∀ i ∈ w, schedulable i = true) : ∀ i ∈ optimizeWindow w, schedulable i = true := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (symExec_isSome_of_schedulable hw)
  have hos : symExec (optimizeWindow w) = some s ∨
      ∃ tcand, symExec (optimizeWindow w) = some tcand := by
    rcases optimizeWindow_spec hs with h | ⟨tc, htc, -⟩
    · exact Or.inl (by rw [h]; exact hs)
    · exact Or.inr ⟨tc, htc⟩
  obtain ⟨t, ht⟩ : ∃ t, symExec (optimizeWindow w) = some t := by
    rcases hos with h | h
    · exact ⟨s, h⟩
    · exact h
  exact foldlM_all_schedulable (optimizeWindow w) ht

theorem labelDefs_optimizeWindow {w : List Asm} (hw : ∀ i ∈ w, schedulable i = true) :
    labelDefs (optimizeWindow w) = [] :=
  labelDefs_eq_nil_of_schedulable (optimizeWindow_all_schedulable hw)

theorem labelRefs_optimizeWindow {w : List Asm} (hw : ∀ i ∈ w, schedulable i = true) :
    labelRefs (optimizeWindow w) = [] :=
  labelRefs_eq_nil_of_schedulable (optimizeWindow_all_schedulable hw)

/-- `optimizeWindow` never grows the lowered byte size (the gate requires
`codeSize cand ≤ codeSize w`; otherwise it keeps the original). -/
theorem codeSize_optimizeWindow_le (w : List Asm) :
    codeSize (optimizeWindow w) ≤ codeSize w := by
  unfold optimizeWindow
  split
  · exact Nat.le_refl _
  · cases symExec w with
    | none => exact Nat.le_refl _
    | some target =>
      dsimp only
      split
      · exact Nat.le_refl _
      · refine List.foldlRecOn (motive := fun best => codeSize best ≤ codeSize w)
          _ _ (Nat.le_refl _) ?_
        intro best hbest cand _hcand
        split
        · split
          · rename_i tcand hc hgate
            rw [Bool.and_eq_true] at hgate
            exact of_decide_eq_true hgate.2
          · exact hbest
        · exact hbest

/-- Every element of a `takeWhile schedulable` prefix is admissible. -/
theorem takeWhile_all_schedulable : ∀ (p : List Asm),
    ∀ i ∈ p.takeWhile schedulable, schedulable i = true := by
  intro p
  induction p with
  | nil => intro i hi; exact absurd hi (by simp [List.takeWhile])
  | cons j p ih =>
    intro i hi
    rw [List.takeWhile_cons] at hi
    split at hi
    · rename_i hj
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hj
      · exact ih i hi
    · exact absurd hi (by simp)

/-- `cutLen` never exceeds the (nonempty) run it cuts. -/
theorem cutLen_le {run : List Asm} (h : 0 < run.length) : cutLen run ≤ run.length := by
  unfold cutLen
  have hcap : Nat.min run.length maxWindowLen ≤ run.length := Nat.min_le_left _ _
  have hcap1 : 1 ≤ Nat.min run.length maxWindowLen := Nat.le_min.mpr ⟨h, by decide⟩
  dsimp only
  split
  · rename_i j hj
    have hmap := (List.mem_filter.mp (List.mem_of_getLast? hj)).1
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hmap
    have := List.mem_range.mp hk
    omega
  · exact Nat.max_le.mpr ⟨h, hcap⟩

/-- The window `scheduleAsmFuel` cuts (`run.take (cutLen run)`, `run` the maximal
admissible prefix) and the tail it recurses on recombine to the original. -/
theorem window_split (i : Asm) (rest : List Asm) (hi : schedulable i = true) :
    ((i :: rest).takeWhile schedulable).take (cutLen ((i :: rest).takeWhile schedulable))
        ++ (i :: rest).drop (cutLen ((i :: rest).takeWhile schedulable)) = i :: rest := by
  set run := (i :: rest).takeWhile schedulable with hrun
  have hne : 0 < run.length := by rw [hrun, List.takeWhile_cons_of_pos hi]; simp
  have hlen := cutLen_le hne
  obtain ⟨t, ht⟩ := List.takeWhile_prefix (l := i :: rest) schedulable
  rw [← hrun] at ht
  rw [← ht, List.drop_append_of_le_length hlen, ← List.append_assoc, List.take_append_drop]

/-- The cut window is all-admissible (a prefix of the `takeWhile` run). -/
theorem window_all_sched (i : Asm) (rest : List Asm) :
    ∀ x ∈ ((i :: rest).takeWhile schedulable).take
        (cutLen ((i :: rest).takeWhile schedulable)), schedulable x = true :=
  fun x hx => takeWhile_all_schedulable _ x (List.mem_of_mem_take hx)

/-- `scheduleAsmFuel` preserves the defined labels. -/
theorem labelDefs_scheduleAsmFuel : ∀ (fuel : Nat) (p : List Asm),
    labelDefs (scheduleAsmFuel fuel p) = labelDefs p := by
  intro fuel
  induction fuel with
  | zero => intro p; rfl
  | succ fuel ih =>
    intro p
    cases p with
    | nil => rfl
    | cons i rest =>
      rw [scheduleAsmFuel]
      split
      · rename_i hi
        dsimp only
        rw [labelDefs_append, labelDefs_optimizeWindow (window_all_sched i rest), ih,
          List.nil_append]
        conv_rhs => rw [← window_split i rest hi]
        rw [labelDefs_append, labelDefs_eq_nil_of_schedulable (window_all_sched i rest),
          List.nil_append]
      · rw [labelDefs_cons, ih, ← labelDefs_cons]

theorem labelRefs_scheduleAsmFuel : ∀ (fuel : Nat) (p : List Asm),
    labelRefs (scheduleAsmFuel fuel p) = labelRefs p := by
  intro fuel
  induction fuel with
  | zero => intro p; rfl
  | succ fuel ih =>
    intro p
    cases p with
    | nil => rfl
    | cons i rest =>
      rw [scheduleAsmFuel]
      split
      · rename_i hi
        dsimp only
        rw [labelRefs_append, labelRefs_optimizeWindow (window_all_sched i rest), ih,
          List.nil_append]
        conv_rhs => rw [← window_split i rest hi]
        rw [labelRefs_append, labelRefs_eq_nil_of_schedulable (window_all_sched i rest),
          List.nil_append]
      · rw [labelRefs_cons, ih, ← labelRefs_cons]

theorem codeSize_scheduleAsmFuel_le : ∀ (fuel : Nat) (p : List Asm),
    codeSize (scheduleAsmFuel fuel p) ≤ codeSize p := by
  intro fuel
  induction fuel with
  | zero => intro p; exact Nat.le_refl _
  | succ fuel ih =>
    intro p
    cases p with
    | nil => exact Nat.le_refl _
    | cons i rest =>
      rw [scheduleAsmFuel]
      split
      · rename_i hi
        dsimp only
        rw [codeSize_append]
        have h1 := codeSize_optimizeWindow_le
          (((i :: rest).takeWhile schedulable).take
            (cutLen ((i :: rest).takeWhile schedulable)))
        have h2 := ih ((i :: rest).drop (cutLen ((i :: rest).takeWhile schedulable)))
        have h3 : codeSize (((i :: rest).takeWhile schedulable).take
              (cutLen ((i :: rest).takeWhile schedulable)))
            + codeSize ((i :: rest).drop (cutLen ((i :: rest).takeWhile schedulable)))
            = codeSize (i :: rest) := by
          rw [← codeSize_append, window_split i rest hi]
        omega
      · rw [codeSize_cons, codeSize_cons]
        exact Nat.add_le_add (Nat.le_refl _) (ih rest)

/-- `scheduleAsm` preserves the program's defined labels. -/
theorem labelDefs_scheduleAsm (p : List Asm) : labelDefs (scheduleAsm p) = labelDefs p :=
  labelDefs_scheduleAsmFuel _ p

/-- `scheduleAsm` preserves the program's referenced labels. -/
theorem labelRefs_scheduleAsm (p : List Asm) : labelRefs (scheduleAsm p) = labelRefs p :=
  labelRefs_scheduleAsmFuel _ p

/-- `scheduleAsm` never grows the lowered byte size. -/
theorem codeSize_scheduleAsm_le (p : List Asm) : codeSize (scheduleAsm p) ≤ codeSize p :=
  codeSize_scheduleAsmFuel_le _ p

/-- **`scheduleAsm` preserves whole-program well-formedness**, so a
`compileScheduled` that inserts it before lowering still lowers (its `WFProg`
premise survives, `codeRel_wf`-style). -/
theorem wfProg_scheduleAsm {p : List Asm} (hw : WFProg p) : WFProg (scheduleAsm p) where
  nodup := by rw [labelDefs_scheduleAsm]; exact hw.nodup
  refsDefined := by
    rw [labelRefs_scheduleAsm, labelDefs_scheduleAsm]; exact hw.refsDefined
  small := by have := codeSize_scheduleAsm_le p; have := hw.small; omega

/-! ## Remaining gap: whole-program forward simulation for `compileScheduled`

What is proved here reduces the pass to the executor and discharges it:

* `symExec_sound` — the executor is sound (the one lemma the design targets);
* `schedule_equiv` / `optimizeWindow_equiv` — the translation-validation gate is
  sound: an accepted window is step-equivalent to the original on every suitable
  concrete stack;
* `wfProg_scheduleAsm` (+ `labelDefs`/`labelRefs`/`codeSize` preservation) — the
  label-structure/size half of `compileScheduled`: inserting `scheduleAsm` before
  `lowerProg` keeps `WFProg`, so lowering still succeeds and the address bound
  holds.

The one remaining step to upgrade the unverified `compileScheduled`
(`Compile.lean`) / `compileObjectScheduled` (`ObjectCompile.lean`) to the
`compile`-level correctness statement is a **whole-program forward simulation**
`scheduleAsm_asteps`/`_ahalt` in the shape of
`Peephole.optimizeAsm_asteps`/`optimizeAsm_ahalt`, i.e. a `steps_sim` over a
`CodeRel`-style relation on suffixes (`SchedRel`, with a `window` constructor
pairing `w` with `optimizeWindow w`). The *control-flow* half is clean — windows
are label/jump-free (`labelDefs_optimizeWindow`/`labelRefs_optimizeWindow`), so
`findLabel` is preserved (a `codeRel_findLabel` analogue) and `StkRefs` carries
over from `AsmPeepholeSound`. The *simulation* half runs into a **genuine
soundness subtlety, not mere plumbing**, described here so it is not lost:

**`symExec`-equality does NOT imply operational equality over stacks that hold
code addresses.** Counterexample: `w = [pop]` and `w' = [op iszero, pop]` both
have `symExec = { stack := [], inputs := 1 }` (the reached leaf `inp 0` is
dropped either way). On a concrete stack `.code L :: σ`, `w` steps to `σ`, but
`w'` gets **stuck** — `AStep.op` requires `words args`, and `.code L` is not a
word. So a candidate that *drops* a reached slot via an op instead of a `pop` is
symbolically indistinguishable yet behaviorally different when that slot is a
code address. `symExec_sound`/`schedule_equiv`/`optimizeWindow_equiv` are
therefore, correctly, stated over **word** stacks (`words ι`) only.

This matters because compiled runs *do* put code addresses in window reach: the
calling convention (`Compile.lean` `compileExpr`/`compileArgs`, the
`pushLabel Lret ; push 0×k ; <args>` shape) computes arguments in a window whose
`dup ⟨off + 1 + rets + idx⟩` reaches **past** the pushed return address
(`.code Lret`); the function epilogue's `pop×n ; retRot k` window likewise reaches
the return address. In the actual backend those code-address slots are always
*preserved* (a bare `inp` leaf in the output, reproduced by any
symbolically-equal candidate only via `dup`/`swap`, never an op) and the slots a
window *drops* are locals (words) — so the pass is in fact sound. But that is a
property of the **backend's stack discipline**, not of the acceptance gate: the
gate (`symStateBeq`, or the incoming `symStateEquiv`) cannot see it.

**Resolved design (Route 2 — strengthened gate, `opExposed`).** `SymState` gains
`opExposed : List Nat`, the input indices ever passed *directly* to an op during
`symExec`; the gate additionally requires `opExposed(candidate) ⊆
opExposed(original)`. This makes the word-typing *compositional*:

* A successful **source** run of the original window proves every
  `opExposed(original)` slot is a word (`AStep.op` demands `words args`) — the
  word-typing hypothesis, now recovered from the source run instead of a backend
  invariant.
* The candidate applies ops only to inputs in `opExposed(candidate) ⊆
  opExposed(original)`, all words; `push`/`dup`/`swap`/`pop` are `AVal`-untyped, so
  shuffling/dropping code addresses is safe on both sides. `AVal`-level
  equivalence then follows from acceptance.
* Counterexample dispatched: `w = [pop]`, `w' = [iszero, pop]` have
  `opExposed = ∅` vs `{0}`, and `{0} ⊄ ∅`, so `w'` is rejected.

Recording only *direct* bare-`inp` op-args is inductively **complete**: an `inp i`
nested inside an arg term `app …[… inp i …]` was necessarily a direct bare arg to
the op that first wrapped it (term-building happens only at op steps), so it was
exposed then; `dup` merely copies exposure-status. The formal invariant to prove
is: for every `app` subterm anywhere in `s.stack`, all its `inp` indices ∈
`s.opExposed`.

Remaining proof work, once the `opExposed` interface lands (bundled with
`symStateEquiv`): (1) generalize `realize`/`symExec_sound` to `AVal` under the
`opExposed`-are-words hypothesis; (2) re-prove `optimizeWindow_equiv` against
`symStateEquiv` (net-effect, via `symExec_sound_pad`) ∧ the `opExposed ⊆` subset
condition; (3) the source-stuttering `scheduleAsm_asteps`/`_ahalt`, firing each
`optimizeWindow w` atomically at the window boundary via pure-`AStep`
determinism. A `sorry` is disallowed here (`warningAsError`), so this is
documented rather than stubbed until the interface is in place. -/
