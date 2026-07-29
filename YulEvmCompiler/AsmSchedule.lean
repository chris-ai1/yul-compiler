import YulEvmCompiler.Asm
set_option warningAsError true
/-!
# YulEvmCompiler.AsmSchedule

**PROTOTYPE, UNPROVEN.** An Asm→Asm *per-window operand-stack scheduler*,
designed around a translation-validation architecture so that soundness later
reduces to a single lemma about the symbolic executor (not about the
scheduler's cleverness).

The pipeline (`scheduleAsm`) splits the program into maximal **windows** —
straight-line runs of pure, label-free, jump-free instructions (`push`, pure
`op`, `dup`, `swap`, `pop`). Everything outside a window is copied verbatim, so
labels, jumps, calls, and every effectful op are untouched.

For each window it:

1. runs a **symbolic executor** (`symExec`) that evaluates the window over a
   symbolic stack (`Term` DAGs over input leaves `inp i` and literal words),
   producing a `SymState` — the output stack as DAG terms plus `inputs`, the
   number of below-window slots the window reaches into;
2. asks an **untrusted scheduler** (`scheduleWindow`) for a cheaper candidate;
3. **validates** the candidate by re-running `symExec` on it and accepting only
   if the resulting `SymState` is *syntactically equal* (same terms, same
   `inputs`) — this is what guarantees the net stack transformation is
   identical, including that the untouched REST below the window is preserved
   (equal `inputs` ⇒ equal split point);
4. additionally requires the candidate to be strictly cheaper by the gas model
   **and** no larger in bytes (so `codeSize` never grows and every lowering /
   `wfCheck` size invariant is preserved).

Because acceptance is gated on validation + strict gas improvement + size
non-growth, the pass is behavior-preserving (modulo the future executor
soundness lemma) and can never regress a window: on any doubt it keeps the
original. Depth limits are enforced by construction — `dup`/`swap` indices are
`Fin 16`, so a scheduler needing a deeper reach simply cannot emit it.

## Future soundness (the one lemma)

`symExec_sound`: if `symExec w = some s`, then for any concrete `AVal` stack
`ι ++ REST` with `ι.length = s.inputs`, `ASteps prog ⟨w ++ c, ι ++ REST, yst⟩
⟨c, realize s.stack ι ++ REST, yst⟩` where `realize` substitutes `inp i ↦ ι[i]`
and evaluates pure ops via `stepOp`. Given that, `symExec w = symExec w'`
(structurally) implies `w` and `w'` have the same net transformation on every
concrete stack, hence are interchangeable inside `prog` — the translation
validation is discharged once, for the executor, independent of the scheduler.
-/

namespace YulEvmCompiler.Schedule

open YulSemantics.EVM (U256 Op)

/-! ### Symbolic terms -/

/-- A symbolic stack value: an input leaf (`inp i` = the `i`-th slot the window
reaches into, counted from the incoming top), a literal word, or a pure op
applied to argument terms (first argument = top-of-stack at the op). -/
inductive Term
  | inp (i : Nat)
  | lit (v : U256)
  | app (op : Op) (args : List Term)

mutual
/-- Structural equality on `Term`. -/
def Term.beq : Term → Term → Bool
  | .inp a,      .inp b      => a == b
  | .lit a,      .lit b      => a == b
  | .app o1 as1, .app o2 as2 => o1 == o2 && Term.beqList as1 as2
  | _,           _           => false
/-- Structural equality on term lists. -/
def Term.beqList : List Term → List Term → Bool
  | [],      []      => true
  | x :: xs, y :: ys => Term.beq x y && Term.beqList xs ys
  | _,       _       => false
end

instance : BEq Term := ⟨Term.beq⟩

/-! ### Op purity / arity

Only deterministic, state-independent, single-output ops are admitted into a
window; every other `op` (memory, storage, env, hashing, calls, halts) is a
window barrier. The arities mirror `YulSemantics.EVM.stepOp` (`bin`/`ter`/`un`).
-/

/-- Argument count of a pure op, or `none` if the op is not window-admissible. -/
def pureArity : Op → Option Nat
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod | .exp | .signextend
  | .lt | .gt | .slt | .sgt | .eq
  | .and | .or | .xor | .byte | .shl | .shr | .sar => some 2
  | .addmod | .mulmod => some 3
  | .clz | .iszero | .not => some 1
  | _ => none

/-- A rough per-instruction gas cost for choosing between candidates. For pure
windows this is the exact runtime gas of one execution (no dynamic/memory
costs), so minimizing it minimizes real per-execution gas. -/
def opGas : Op → Nat
  | .mul | .div | .sdiv | .mod | .smod | .signextend => 5
  | .addmod | .mulmod => 8
  -- `exp` is really `10 + 50·(exponent bytes)`; this static underestimate is
  -- safe because candidates are only ever compared against the ORIGINAL window
  -- (strictly-cheaper, never accepted on estimated ties), so a candidate that
  -- recomputes an `exp` instead of reusing it scores no better here.
  | .exp => 10
  | _ => 3

/-- Per-instruction gas (window instructions; others default to 3). -/
def instrGas : Asm → Nat
  | .push v => if v = 0 then 2 else 3
  | .op yop => opGas yop
  | .dup _ => 3
  | .swap _ => 3
  | .pop => 2
  | _ => 3

/-- Total gas of an instruction sequence under `instrGas`. -/
def windowGas (w : List Asm) : Nat := (w.map instrGas).sum

/-- Is an instruction window-admissible (pure, straight-line)? -/
def schedulable : Asm → Bool
  | .push _ | .dup _ | .swap _ | .pop => true
  | .op yop => (pureArity yop).isSome
  | _ => false

/-! ### Symbolic executor -/

/-- The symbolic state during window execution: the realized stack (top first),
the number of input leaves materialized so far (= how deep the window has reached
below its start), and `opExposed` — the set of input indices that have appeared
as a DIRECT argument of a pure op. An op requires WORD operands, so a run in
which `inp i ∈ opExposed` is only well-defined when the concrete value at slot
`i` is a word (not a `.code` return address); `pop`/`dup`/`swap` are untyped and
impose no such requirement. This is why the gate demands the candidate's
`opExposed` be a SUBSET of the original's: the original's successful run witnesses
that its op-exposed slots are words, and the candidate may only op-touch a
subset. Without it, `symExec`-equality would wrongly accept e.g. `[pop]` vs
`[iszero, pop]` (equal net effect symbolically, but the latter is stuck on a
`.code` value). -/
structure SymState where
  stack : List Term
  inputs : Nat
  opExposed : List Nat

/-- Materialize input leaves at the bottom until the realized stack has at least
`need` elements, so an access at depth `need-1` is in range. Growth increments
`inputs`; `opExposed` is unaffected (materialization is not an op use). -/
def pad (s : SymState) (need : Nat) : SymState :=
  if s.stack.length ≥ need then s
  else
    let extra := need - s.stack.length
    { s with
      stack := s.stack ++ (List.range extra).map (fun j => Term.inp (s.inputs + j)),
      inputs := s.inputs + extra }

/-- One symbolic step. Mirrors `AStep`: `push`/`pop`/`dup`/`swap` shuffle the
stack; a pure `op` consumes `k` argument terms (first = top) and pushes one
`app` term. Any non-admissible instruction yields `none` (should not occur
inside an extracted window). -/
def symStep (s : SymState) : Asm → Option SymState
  | .push v => some { s with stack := .lit v :: s.stack }
  | .pop =>
      let s := pad s 1
      some { s with stack := s.stack.drop 1 }
  | .dup ⟨n, _⟩ =>
      let s := pad s (n + 1)
      match s.stack[n]? with
      | some t => some { s with stack := t :: s.stack }
      | none => none
  | .swap ⟨n, _⟩ =>
      let s := pad s (n + 2)
      match s.stack[0]?, s.stack[n + 1]? with
      | some a, some b => some { s with stack := (s.stack.set 0 b).set (n + 1) a }
      | _, _ => none
  | .op yop =>
      match pureArity yop with
      | some k =>
          let s := pad s k
          let args := s.stack.take k
          -- record every input that appears as a DIRECT op argument (a bare
          -- `inp i`); nested inputs were already recorded when their containing
          -- subterm was formed by an earlier op.
          let exposed := args.filterMap (fun t => match t with | .inp i => some i | _ => none)
          some { stack := .app yop args :: s.stack.drop k,
                 inputs := s.inputs,
                 opExposed := exposed ++ s.opExposed }
      | none => none
  | _ => none

/-- Run a window symbolically from the empty stack. `none` if it contains any
non-admissible instruction. -/
def symExec (w : List Asm) : Option SymState :=
  w.foldlM symStep { stack := [], inputs := 0, opExposed := [] }

/-- Structural equality of symbolic states: same output terms and same input
reach (the latter guarantees the untouched REST below the window lines up).
Requiring equal `inputs` is conservative — it rejects a candidate that
legitimately reaches FEWER below-window slots than the original. A future
relaxation would normalize both states to the max input reach (materializing the
extra deep leaves as identities) before comparing. -/
def symStateBeq (a b : SymState) : Bool :=
  a.inputs == b.inputs && Term.beqList a.stack b.stack

/-- **INTERFACE (authorized gate relaxation).** Net-effect equality of two
symbolic states, normalizing input reach. A state that reaches only `inputs`
slots leaves the deeper slots `inp inputs, inp (inputs+1), …` untouched below its
output, so its full effect over `K ≥ inputs` slots is
`stack ++ [inp inputs, …, inp (K-1)]`. Padding both to `K = max` and comparing is
the true net-stack equality — sound, and (unlike `symStateBeq`) it admits a
candidate that leaves/consumes fewer deep slots than the original. This is what
lets the store-in-place scheduler (which leaves identity slots untouched,
reaching fewer inputs) pass the gate. The proof agent re-proves
`optimizeWindow_equiv` against this. -/
def symStateEquiv (a b : SymState) : Bool :=
  let K := Nat.max a.inputs b.inputs
  let padTo (s : SymState) : List Term :=
    s.stack ++ (List.range (K - s.inputs)).map (fun j => .inp (s.inputs + j))
  Term.beqList (padTo a) (padTo b)

/-! ### The scheduler (untrusted) + validation gate -/

/-! ### The DAG rescheduler (untrusted)

Correctness never depends on any of this — the validation gate below re-checks
every candidate. The scheduler targets canonical→canonical windows (`m = k`,
non-changed slots are identity), which is exactly the shape the backend emits for
straight-line reassignment blocks (e.g. TickMath's log2 section, where symbolic
execution collapses 14 store/reload cycles into one DAG per updated slot). It
computes each *changed* slot's collapsed DAG once (with common-subexpression
sharing via the running model stack, consuming shared values in place) and stores
it, instead of the backend's per-statement DUP/store/reload. On any difficulty
(a move/permutation, a needed reach past `DUP16`/`SWAP16`, `m ≠ k`) it returns
`none` and the original window is kept. -/

/-! Structural size of a term (for a topological fuel bound). -/
mutual
def Term.size : Term → Nat
  | .inp _ | .lit _ => 1
  | .app _ args => 1 + Term.sizeList args
def Term.sizeList : List Term → Nat
  | [] => 0
  | x :: xs => Term.size x + Term.sizeList xs
end

/-- First index of a structurally-equal term in the model stack. -/
def findIdxBeq (t : Term) : List Term → Option Nat
  | [] => none
  | x :: xs => if Term.beq t x then some 0 else (findIdxBeq t xs).map (· + 1)

/-- Emitter state: emitted code (reversed) and the running symbolic model. -/
structure ES where
  rcode : List Asm
  model : SymState

def ES.code (es : ES) : List Asm := es.rcode.reverse

/-- Append one instruction, keeping the model in lockstep via `symStep`. -/
def emit (es : ES) (i : Asm) : Option ES :=
  (symStep es.model i).map (fun m => ⟨i :: es.rcode, m⟩)

/-! `genValue` emits code leaving the value of `t` on top of the model stack
(model height +1). It reuses any structurally-equal value already on the stack
(`DUP`), otherwise builds it: literals via `PUSH`, `app` by emitting its
arguments (reversed, so the first argument ends on top) then the op. It fails
past the `DUP16` reach or on an input leaf that is not present (should not occur
from the seeded model). -/
mutual
def genValue : Nat → ES → Term → Option ES
  | 0, _, _ => none
  | fuel + 1, es, t =>
      match findIdxBeq t es.model.stack with
      | some d => if h : d < 16 then emit es (.dup ⟨d, h⟩) else none
      | none =>
          match t with
          | .lit v => emit es (.push v)
          | .inp _ => none
          | .app op args =>
              match genArgs fuel es args with
              | some es' => emit es' (.op op)
              | none => none
/-- Build an op's arguments so the top-n become `[arg0, …, arg(n-1)]`. The
deepest operand `arg(n-1)` is built first; if it is an already-computed
INTERMEDIATE (`app`) sitting on top of the model, it is CONSUMED IN PLACE (no
`DUP`) — the op will take it as its deepest operand — instead of copied. This is
the chain-accumulator win: `mul(r,r)` on an intermediate `r` becomes `dup;mul`
(1 DUP, `r` consumed) instead of two DUPs leaving `r` behind. Only intermediates
are consumed this way, so the fixed `k`-input cleanup is unaffected; the gate
rejects any consume that was not actually a last use. -/
def genArgs : Nat → ES → List Term → Option ES
  | 0, _, _ => none
  | fuel + 1, es, args =>
      match args.reverse with
      | [] => some es
      | first :: restRev =>
          let firstES :=
            match first, es.model.stack.head? with
            | .app _ _, some h => if Term.beq first h then some es else genValue fuel es first
            | _, _ => genValue fuel es first
          match firstES with
          | none => none
          | some e => restRev.foldlM (fun acc a => genValue fuel acc a) e
end

/-- Emit `n` pops. -/
def emitPops : ES → Nat → Option ES
  | es, 0 => some es
  | es, n + 1 => (emit es .pop).bind (fun es' => emitPops es' n)

/-- The window's inputs sit below the freshly-built `m` outputs. Remove them
with `swap⟨m-1⟩; pop`, repeated `b` times: each iteration deletes the shallowest
input and rotates the top-`m` block left by one, so after `b = k` iterations the
inputs are gone and the outputs are rotated left by `k` (which the builder
pre-compensates). Requires `0 < m ≤ 16`. -/
def emitCleanup (m : Nat) : ES → Nat → Option ES
  | es, 0 => some es
  | es, b + 1 =>
      if h : 0 < m ∧ m - 1 < 16 then
        match emit es (.swap ⟨m - 1, h.2⟩) with
        | some es' =>
            match emit es' .pop with
            | some es'' => emitCleanup m es'' b
            | none => none
        | none => none
      else none

/-- The DAG rescheduler proper. Rebuilds the window's `m` symbolic outputs from
its `k` inputs, with common-subexpression sharing inside each output (so a
collapsed reassignment chain is computed once instead of via the backend's
per-statement store/reload), then removes the inputs. Outputs are built
pre-rotated by `k mod m` so the `emitCleanup` rotation lands them in order. -/
def scheduleWindowReal (target : SymState) : Option (List Asm) :=
  let k := target.inputs
  let T := target.stack
  let m := T.length
  if m > 16 then none else
  let fuel := 8 * (Term.sizeList T) + 100
  let init : ES := ⟨[], { stack := (List.range k).map Term.inp, inputs := k, opExposed := [] }⟩
  if m == 0 then
    (emitPops init k).map ES.code
  else
    let rot := k % m
    -- build O[m-1] (deepest) first … O[0] (top) last, where the cleanup rotation
    -- makes the final top-m equal T:  O[j] = T[(j + (m - rot)) % m].
    match (List.range m).reverse.foldlM
        (fun es j => genValue fuel es ((T[(j + (m - rot)) % m]?).getD (.lit 0))) init with
    | none => none
    | some es1 => (emitCleanup m es1 k).map ES.code

/-- Store-in-place scheduler for canonical windows (`m = k`, non-changed slots
are identity `inp j`): leave every identity slot exactly where it is (0 ops,
unlike the rebuild which DUPs it then cleans it up) and, for each CHANGED slot,
compute its value and write it in with `swap; pop`. This is the key to not
rebuilding identity slots. Candidates reach fewer inputs than the original, so
acceptance needs `symStateEquiv`'s input normalization. -/
def scheduleStoreInPlace (target : SymState) : Option (List Asm) :=
  let k := target.inputs
  let T := target.stack
  let m := T.length
  if m != k then none else
  let slots := T.zipIdx
  let hasMove := slots.any (fun (t, j) => match t with | .inp i => i != j | _ => false)
  if hasMove then none else
  let changed := slots.filterMap (fun (t, j) =>
    match t with | .inp _ => none | _ => some (j, t))
  let fuel := 8 * (Term.sizeList T) + 100
  let init : ES := ⟨[], { stack := (List.range k).map Term.inp, inputs := k, opExposed := [] }⟩
  match changed.foldlM (fun es (p : Nat × Term) => genValue fuel es p.2) init with
  | none => none
  | some es1 =>
      match changed.reverse.foldlM (fun es (p : Nat × Term) =>
          match findIdxBeq (Term.inp p.1) es.model.stack with
          | none => none
          | some d =>
              if h : 0 < d ∧ d - 1 < 16 then
                match emit es (.swap ⟨d - 1, h.2⟩) with
                | some es' => emit es' .pop
                | none => none
              else none) es1 with
      | none => none
      | some es2 => some es2.code

/-- Candidate schedules for a window; the gate keeps the cheapest that validates
and beats the original. Store-in-place first (best on identity-heavy canonical
windows), then the general rebuild (handles `m ≠ k` / permutations). -/
def scheduleCandidates (target : SymState) : List (List Asm) :=
  (scheduleStoreInPlace target).toList ++ (scheduleWindowReal target).toList

/-- Skip windows longer than this. `Term` is a tree, so a long run of squarings
(`r := shr(127, mul(r,r))`, no barrier between blocks) would build terms of size
~2^(#blocks); capping the window length splits such a run into per-block windows
(where the backend's per-statement DUP/store/reload waste actually lives) and
keeps `symExec`/`Term.beq`/`Term.size` cost bounded, so the pass adds only
bounded compile time. -/
def maxWindowLen : Nat := 48

/-- Bail out of scheduling a window whose symbolic output DAG exceeds this many
nodes (belt-and-suspenders against tree blowup within the length cap). -/
def maxTermNodes : Nat := 4096

/-- Optimize one extracted window: among the candidate schedules, keep the
cheapest that (1) is net-effect-equal to the original (`symStateEquiv`), (2)
op-exposes only a SUBSET of the inputs the original op-exposed (so it never feeds
an op a slot the original proved is a word — the `.code`-value soundness fix),
and (3) does not grow bytes. Otherwise keep the original. Accepting only
candidates STRICTLY cheaper than the ORIGINAL (never on estimated ties) is what
makes the `opGas` `exp` underestimate safe. -/
def optimizeWindow (w : List Asm) : List Asm :=
  if w.length > maxWindowLen then w else
  match symExec w with
  | none => w
  | some target =>
      if Term.sizeList target.stack > maxTermNodes then w else
      (scheduleCandidates target).foldl (fun best cand =>
        match symExec cand with
        | some tcand =>
            if symStateEquiv tcand target
                && tcand.opExposed.all (· ∈ target.opExposed)
                && windowGas cand < windowGas best
                && codeSize cand ≤ codeSize w then cand else best
        | none => best) w

/-- Is a prefix height-preserving (`m = k`, a canonical/statement-boundary cut)
with a bounded output DAG? Store-in-place needs this shape. -/
def isCanonicalWindow (w : List Asm) : Bool :=
  match symExec w with
  | some s => s.stack.length == s.inputs && Term.sizeList s.stack ≤ maxTermNodes
  | none => false

/-- Window length inside a schedulable run: the LARGEST canonical (`m = k`,
bounded-DAG) prefix up to `maxWindowLen`, so whole blocks become one
store-in-place window instead of `m ≠ k` mid-computation fragments. Falls back to
`maxWindowLen` (general rebuild) when no canonical prefix exists. Always ≥ 1. -/
def cutLen (run : List Asm) : Nat :=
  let cap := Nat.min run.length maxWindowLen
  match (((List.range cap).map (· + 1)).filter (fun j => isCanonicalWindow (run.take j))).getLast? with
  | some j => j
  | none => Nat.max 1 cap

/-- Split the program into windows (cut at canonical boundaries) and non-window
instructions, running `optimizeWindow` on each. Fuel-bounded for a trivial
termination argument; the bound `p.length + 1` always suffices. -/
def scheduleAsmFuel : Nat → List Asm → List Asm
  | 0, p => p
  | _ + 1, [] => []
  | fuel + 1, i :: rest =>
      if schedulable i then
        let run := (i :: rest).takeWhile schedulable
        let len := cutLen run
        let win := run.take len
        let tail := (i :: rest).drop len
        optimizeWindow win ++ scheduleAsmFuel fuel tail
      else
        i :: scheduleAsmFuel fuel rest

/-- The Asm-level window scheduler run by `compile`, after `optimizeAsm` and
before the `stackOK2` overflow gate (so the bound is checked on the final code).
Total; on any doubt it returns its input unchanged. -/
def scheduleAsm (p : List Asm) : List Asm := scheduleAsmFuel (p.length + 1) p

end YulEvmCompiler.Schedule
