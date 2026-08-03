import YulEvmCompiler.Asm
import Std.Data.HashMap
set_option warningAsError true
/-!
# YulEvmCompiler.AsmSchedule  (DAG prototype — child branch agent/uv4-sched-dag)

**PROTOTYPE, UNPROVEN.** Asm→Asm per-window operand-stack scheduler, now over a
**hash-consed DAG** of symbolic terms instead of tree terms. Structural sharing
makes a symbolic term's *storage* and equality check linear in window length
rather than ~2^(#blocks), so whole-block windows no longer blow up.

Data-structure change vs the parent (agent/uv4-stack-sched @ 439022f), for the
eventual proof port:
* `Term` (tree) → `NodeF` (an `inp`/`lit`/`app` node whose `app` children are
  node **ids**) held in a `Dag` (node array + hash-cons memo). A term is a `Nat`
  id; structural equality is **id equality** because interning is canonical.
* `symExec`/`pad`/`symStep` now **thread a `Dag`** and return `SymState × Dag`.
  The gate runs the original then each candidate into the SAME `Dag`, so equal
  structures share ids across both.
* The **gate/window/program layers keep identical acceptance semantics**:
  `symStateEquiv` (net-effect equality, input-normalized) + `opExposed` subset +
  strictly-cheaper gas + non-growing bytes. Only the executor's data structure
  changed; the executor lemmas will need re-proving over DAG nodes, the
  gate/window/program layers should not.

The scheduler (`scheduleWindow…`) is untrusted; the gate re-checks every
candidate, so correctness never depends on it.
-/

namespace YulEvmCompiler.Schedule

open YulSemantics.EVM (U256 Op)

/-! ### Hash-consed DAG of symbolic terms -/

/-- `Op` is a finite enum without a `Hashable` instance upstream; hash via its
`Repr` so `NodeF` can key the hash-cons memo. -/
instance : Hashable Op := ⟨fun o => hash (reprStr o)⟩

/-- A DAG node: an input leaf (`inp i`), a literal word, or a pure op applied to
argument **node ids** (first argument = top-of-stack at the op). Children are
always interned before their parent, so a child's id is always `<` its parent's. -/
inductive NodeF
  | inp (i : Nat)
  | lit (v : U256)
  | app (op : Op) (args : List Nat)
  deriving DecidableEq, Hashable, Inhabited

/-- The hash-cons table: `nodes[id]` is the node, `memo` maps a node structure to
its canonical id. -/
structure Dag where
  nodes : Array NodeF := #[]
  memo : Std.HashMap NodeF Nat := {}

/-- Intern a node, returning its canonical id (creating it if new). -/
def Dag.intern (d : Dag) (n : NodeF) : Nat × Dag :=
  match d.memo[n]? with
  | some id => (id, d)
  | none =>
      let id := d.nodes.size
      (id, { nodes := d.nodes.push n, memo := d.memo.insert n id })

/-- The node at an id (`inp 0` for an out-of-range id, which never occurs). -/
def Dag.node (d : Dag) (id : Nat) : NodeF := d.nodes[id]?.getD (.inp 0)

/-! ### Op purity / arity (unchanged from the parent) -/

/-- Argument count of a pure op, or `none` if the op is not window-admissible. -/
def pureArity : Op → Option Nat
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod | .exp | .signextend
  | .lt | .gt | .slt | .sgt | .eq
  | .and | .or | .xor | .byte | .shl | .shr | .sar => some 2
  | .addmod | .mulmod => some 3
  | .clz | .iszero | .not => some 1
  | _ => none

/-- Binary ops whose result is unchanged by swapping the two operands. Their DAG
nodes are canonicalized (args sorted by id) at intern, so `op(a,b)` and `op(b,a)`
share one id — letting the scheduler emit whichever operand order is cheaper to
arrange and still validate. Sound: these are commutative `BitVec` operations
(`op(a,b) = op(b,a)`), which the eventual executor↔AStep proof discharges per op. -/
def commutative : Op → Bool
  | .add | .mul | .and | .or | .xor | .eq => true
  | _ => false

/-- Per-op gas for choosing between candidates (exact for pure windows). -/
def opGas : Op → Nat
  | .mul | .div | .sdiv | .mod | .smod | .signextend => 5
  | .addmod | .mulmod => 8
  -- `exp` underestimate is safe: candidates are compared only against the
  -- ORIGINAL (strictly cheaper, never on ties).
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

/-- Total gas of an instruction sequence. -/
def windowGas (w : List Asm) : Nat := (w.map instrGas).sum

/-- Is an instruction window-admissible (pure, straight-line)? -/
def schedulable : Asm → Bool
  | .push _ | .dup _ | .swap _ | .pop => true
  | .op yop => (pureArity yop).isSome
  | _ => false

/-! ### Symbolic executor (threads a `Dag`) -/

/-- Symbolic state: the realized stack of node ids (top first), the number of
input leaves materialized so far, and `opExposed` — input indices that have been
a DIRECT argument of a pure op (see the gate for why this is tracked). -/
structure SymState where
  stack : List Nat
  inputs : Nat
  opExposed : List Nat

/-- Materialize input leaves at the bottom until the stack has ≥ `need` elements.
Interns the new `inp` leaves into the dag; increments `inputs`. -/
def pad (d : Dag) (s : SymState) (need : Nat) : SymState × Dag :=
  if s.stack.length ≥ need then (s, d)
  else
    let extra := need - s.stack.length
    let (ids, d) := (List.range extra).foldl
      (fun (acc : List Nat × Dag) j =>
        let (id, d') := acc.2.intern (.inp (s.inputs + j))
        (acc.1 ++ [id], d')) ([], d)
    ({ s with stack := s.stack ++ ids, inputs := s.inputs + extra }, d)

/-- One symbolic step, mirroring `AStep`. Threads the dag (interning literals and
op-result nodes). `none` on a non-admissible instruction. -/
def symStep (d : Dag) (s : SymState) : Asm → Option (SymState × Dag)
  | .push v => let (id, d) := d.intern (.lit v); some ({ s with stack := id :: s.stack }, d)
  | .pop =>
      let (s, d) := pad d s 1
      some ({ s with stack := s.stack.drop 1 }, d)
  | .dup ⟨n, _⟩ =>
      let (s, d) := pad d s (n + 1)
      match s.stack[n]? with
      | some t => some ({ s with stack := t :: s.stack }, d)
      | none => none
  | .swap ⟨n, _⟩ =>
      let (s, d) := pad d s (n + 2)
      match s.stack[0]?, s.stack[n + 1]? with
      | some a, some b => some ({ s with stack := (s.stack.set 0 b).set (n + 1) a }, d)
      | _, _ => none
  | .op yop =>
      match pureArity yop with
      | some k =>
          let (s, d) := pad d s k
          let args := s.stack.take k
          let exposed := args.filterMap (fun id =>
            match d.node id with | .inp i => some i | _ => none)
          -- canonicalize commutative ops so op(a,b) and op(b,a) share one id
          let canonArgs := if commutative yop then (args.toArray.qsort (· < ·)).toList else args
          let (rid, d) := d.intern (.app yop canonArgs)
          some ({ stack := rid :: s.stack.drop k,
                  inputs := s.inputs,
                  opExposed := exposed ++ s.opExposed }, d)
      | none => none
  | _ => none

/-- Run a window symbolically starting from a given dag (so the gate can share a
table across original and candidate). `none` on any non-admissible instruction. -/
def symExecFrom (d0 : Dag) (w : List Asm) : Option (SymState × Dag) :=
  w.foldlM (fun (sd : SymState × Dag) i => symStep sd.2 sd.1 i)
    (({ stack := [], inputs := 0, opExposed := [] } : SymState), d0)

/-- Run a window from an empty dag. -/
def symExec (w : List Asm) : Option (SymState × Dag) := symExecFrom {} w

/-- Number of distinct nodes reachable from `ids` (a linear-in-window-length cost
proxy, using that children have smaller ids than parents). -/
def reachCount (d : Dag) (ids : List Nat) : Nat :=
  -- mark reachable ids top-down; since child < parent, one descending sweep works
  let maxId := d.nodes.size
  let seed : Array Bool := (Array.replicate maxId false)
  let seed := ids.foldl (fun a id => if id < maxId then a.set! id true else a) seed
  -- sweep from high ids to low, propagating to children
  let marks := (List.range maxId).reverse.foldl (fun (a : Array Bool) id =>
    if a[id]?.getD false then
      match d.node id with
      | .app _ args => args.foldl (fun a c => if c < maxId then a.set! c true else a) a
      | _ => a
    else a) seed
  (List.range maxId).foldl (fun n id => if marks[id]?.getD false then n + 1 else n) 0

/-- Structural equality of symbolic states within one dag (id equality). -/
def symStateBeq (a b : SymState) : Bool :=
  a.inputs == b.inputs && a.stack == b.stack

/-- **Net-effect equality, input-normalized** (same acceptance meaning as the
parent). A state reaching only `inputs` slots leaves deeper slots untouched, so
its effect over `K = max` slots is `stack ++ [inp inputs … inp (K-1)]`; interning
those padding leaves into `d` and comparing id lists is the net-stack equality. -/
def symStateEquiv (d : Dag) (a b : SymState) : Bool :=
  let K := Nat.max a.inputs b.inputs
  let (idOf, _) := (List.range K).foldl
    (fun (acc : Array Nat × Dag) j =>
      let (id, d') := acc.2.intern (.inp j)
      (acc.1.push id, d')) ((#[] : Array Nat), d)
  let padTo (s : SymState) : List Nat :=
    s.stack ++ (List.range (K - s.inputs)).map (fun t => idOf[s.inputs + t]!)
  padTo a == padTo b

/-! ### The scheduler (untrusted) — threads the dag for CSE via id equality -/

/-- First index of `id` in the model stack (CSE lookup; id equality = structural). -/
def findIdx (id : Nat) : List Nat → Option Nat
  | [] => none
  | x :: xs => if x == id then some 0 else (findIdx id xs).map (· + 1)

/-- Emitter state: emitted code (reversed), the running model, and the shared dag
(so nodes built while emitting get the SAME ids as the target's nodes). -/
structure ES where
  rcode : List Asm
  model : SymState
  dag : Dag

def ES.code (es : ES) : List Asm := es.rcode.reverse

/-- Append one instruction, keeping model + dag in lockstep via `symStep`. -/
def emit (es : ES) (i : Asm) : Option ES :=
  (symStep es.dag es.model i).map (fun (m, d) => ⟨i :: es.rcode, m, d⟩)

/-! `genValue` emits code leaving the value of node `t` on top. It reuses a
structurally-equal value already on the stack (`DUP` via id equality); else
builds it (literal → `PUSH`, app → args reversed then op; the deepest app-arg
already on top is consumed in place). Fails past the `DUP16` reach; fuel-bounded
(bails → gate keeps original). -/
mutual
def genValue : Nat → ES → Nat → Option ES
  | 0, _, _ => none
  | fuel + 1, es, t =>
      match findIdx t es.model.stack with
      | some d => if h : d < 16 then emit es (.dup ⟨d, h⟩) else none
      | none =>
          match es.dag.node t with
          | .lit v => emit es (.push v)
          | .inp _ => none
          | .app op args =>
              match genArgs fuel es args with
              | some es' => emit es' (.op op)
              | none => none
def genArgs : Nat → ES → List Nat → Option ES
  | 0, _, _ => none
  | fuel + 1, es, args =>
      match args.reverse with
      | [] => some es
      | first :: restRev =>
          let firstES :=
            match es.dag.node first, es.model.stack.head? with
            | .app _ _, some h => if h == first then some es else genValue fuel es first
            | _, _ => genValue fuel es first
          match firstES with
          | none => none
          | some e => restRev.foldlM (fun acc a => genValue fuel acc a) e
end

/-- DUP a node already present on the model stack to the top. -/
def dupToTop (es : ES) (node : Nat) : Option ES :=
  match findIdx node es.model.stack with
  | some d => if h : d < 16 then emit es (.dup ⟨d, h⟩) else none
  | none => none

/-- DUP a list of nodes (already present) to the top in order, so after the
sequence the top holds them with the LAST list element deepest. Used with an
op's `args.reverse` so the top becomes `[arg0, …, arg(n-1)]`. -/
def dupArgsToTop : ES → List Nat → Option ES
  | es, [] => some es
  | es, a :: rest => (dupToTop es a).bind (fun es' => dupArgsToTop es' rest)

/-! `ensure` materializes a node's value SOMEWHERE on the stack (computing it once
if absent) WITHOUT consuming existing values — ops consume DUPs, so each node is
computed at most once (no exponential rebuild). This is the CSE core. It fails
(→ bail, gate keeps original) if a needed value sits past the `DUP16` reach. -/
mutual
def ensure : Nat → ES → Nat → Option ES
  | 0, _, _ => none
  | fuel + 1, es, node =>
      match findIdx node es.model.stack with
      | some _ => some es
      | none =>
          match es.dag.node node with
          | .lit v => emit es (.push v)
          | .inp _ => none
          | .app op args =>
              match ensureArgs fuel es args with
              | none => none
              | some es1 =>
                  match dupArgsToTop es1 args.reverse with
                  | none => none
                  | some es2 => emit es2 (.op op)
def ensureArgs : Nat → ES → List Nat → Option ES
  | _, es, [] => some es
  | 0, _, _ => none
  | fuel + 1, es, a :: rest =>
      match ensure fuel es a with
      | none => none
      | some es1 => ensureArgs fuel es1 rest
end

/-- Emit `n` pops. -/
def emitPops : ES → Nat → Option ES
  | es, 0 => some es
  | es, n + 1 => (emit es .pop).bind (fun es' => emitPops es' n)

/-- Emit `swap⟨m-1⟩; pop` `b` times (removes `b` inputs below the top-`m` block,
rotating it left by `b`; the builder pre-rotates to compensate). Needs `0<m≤16`. -/
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

/-- Initial emitter seeded with `[inp0 … inp(k-1)]` in the given dag. -/
def initES (d : Dag) (k : Nat) : ES :=
  let (ids, d) := (List.range k).foldl
    (fun (acc : List Nat × Dag) j => let (id, d') := acc.2.intern (.inp j); (acc.1 ++ [id], d'))
    ([], d)
  ⟨[], { stack := ids, inputs := k, opExposed := [] }, d⟩

/-- General rebuild scheduler: rebuild all `m` outputs (CSE via id equality) then
remove the `k` inputs, outputs pre-rotated so the cleanup lands them in order. -/
def scheduleRebuild (d : Dag) (target : SymState) (fuel : Nat) : Option (List Asm) :=
  let T := target.stack
  let m := T.length
  let k := target.inputs
  if m > 16 then none else
  let init := initES d k
  if m == 0 then
    (emitPops init k).map ES.code
  else
    let rot := k % m
    match (List.range m).reverse.foldlM
        (fun es j => genValue fuel es (T[(j + (m - rot)) % m]?.getD 0)) init with
    | none => none
    | some es1 => (emitCleanup m es1 k).map ES.code

/-- Store-in-place scheduler for canonical windows (`m = k`, non-changed slots
identity): leave identity slots in place, compute+store only changed slots. -/
def scheduleStoreInPlace (d : Dag) (target : SymState) (fuel : Nat) : Option (List Asm) :=
  let T := target.stack
  let m := T.length
  let k := target.inputs
  if m != k then none else
  -- classify: identity slot j has node `inp j`; a slot with `inp i (i≠j)` is a move (bail)
  let slots := T.zipIdx
  let hasMove := slots.any (fun (id, j) =>
    match d.node id with | .inp i => i != j | _ => false)
  if hasMove then none else
  let changed := slots.filterMap (fun (id, j) =>
    match d.node id with | .inp _ => none | _ => some (j, id))
  let init := initES d k
  match changed.foldlM (fun es (p : Nat × Nat) => genValue fuel es p.2) init with
  | none => none
  | some es1 =>
      match changed.reverse.foldlM (fun es (p : Nat × Nat) =>
          -- find the current depth of input `inp (p.1)` and store into it
          match es.model.stack.findIdx? (fun id => match es.dag.node id with
                                                    | .inp i => i == p.1 | _ => false) with
          | none => none
          | some depth =>
              if h : 0 < depth ∧ depth - 1 < 16 then
                match emit es (.swap ⟨depth - 1, h.2⟩) with
                | some es' => emit es' .pop
                | none => none
              else none) es1 with
      | none => none
      | some es2 => some es2.code

/-- CSE-materializing linear scheduler. `ensure` computes every reachable node
ONCE (ops consume DUPs, originals stay memoized), so there is no exponential
rebuild — the whole win of the DAG. Then it DUPs the outputs into place
(pre-rotated by the pre-cleanup height `b`) and removes everything below with the
rotating cleanup. Bails (→ gate keeps original) whenever a needed value would sit
past the `DUP16`/`SWAP16` reach, which bounds the live-set depth. -/
def scheduleLinear (d : Dag) (target : SymState) (fuel : Nat) : Option (List Asm) :=
  let T := target.stack
  let m := T.length
  let k := target.inputs
  if m > 16 then none else
  let init := initES d k
  if m == 0 then (emitPops init k).map ES.code else
  -- 1. materialize every output's value on the stack (each node computed once)
  match T.foldlM (fun es node => ensure fuel es node) init with
  | none => none
  | some es1 =>
      let b := es1.model.stack.length        -- everything currently on the stack is cleaned
      let rot := b % m
      -- 2. DUP outputs to the top, pre-rotated so the cleanup's left-rotate lands T:
      --    build O[m-1] (deepest) first … O[0] (top) last, O[j] = T[(j + (m-rot)) % m].
      match (List.range m).reverse.foldlM
          (fun es j => dupToTop es (T[(j + (m - rot)) % m]?.getD 0)) es1 with
      | none => none
      | some es2 =>
          -- 3. remove the b memoized/intermediate/input values below the top-m block
          (emitCleanup m es2 b).map ES.code

/-! ### Eviction-aware linear scheduler (`scheduleEvict`)

Consumes each value at its LAST use instead of memoizing everything, so the live
set stays small (the log2 chain's is ~4) and big windows don't drown in cleanup.
`remUses[n]` = (op-arg references of `n`) + (appearances of `n` in the target `T`);
a value with a `T` appearance keeps `remUses ≥ 1` through phase 1, so it is never
consumed before the final layout. All correctness is absorbed by the gate. -/

/-- Total use-count per node: `T` appearances plus op-arg references among the
reachable sub-DAG (descending sweep; children have smaller ids). -/
def computeRem (d : Dag) (T : List Nat) : Array Nat :=
  let n := d.nodes.size
  let rem0 : Array Nat := Array.replicate n 0
  let rem1 := T.foldl (fun a id => if id < n then a.set! id (a[id]! + 1) else a) rem0
  (List.range n).reverse.foldl (fun a id =>
    if a[id]! > 0 then
      match d.node id with
      | .app _ args => args.foldl (fun a c => if c < n then a.set! c (a[c]! + 1) else a) a
      | _ => a
    else a) rem1

/-- Emitter + remaining-use table. -/
structure EvSt where
  es : ES
  rem : Array Nat

def emitEv (ev : EvSt) (i : Asm) : Option EvSt := (emit ev.es i).map (fun es => ⟨es, ev.rem⟩)
def EvSt.dec (ev : EvSt) (a : Nat) : EvSt := ⟨ev.es, ev.rem.set! a (ev.rem[a]! - 1)⟩

/-! `ensureEv node` ensures `node`'s value is present on the stack (computing it
once if absent), then leaves it there. `arrange1` brings one op-arg to the top:
within DUP16 reach it MOVEs at last use (`remUses ≤ 1`, consuming) or else DUPs;
BEYOND reach (or absent) it EVICT-BY-RECOMPUTEs — `recompute` rebuilds a fresh
copy on top, `bringDup` supplies its sub-values (DUP if shallow, else recompute),
never consuming, so it cannot over-consume a shared value. Recompute bails on an
`inp` leaf (a pinned input can't be rebuilt); this is also the assertion that we
never op-expose an input the original didn't (the original computed the same node
from the same leaves, so `opExposed(cand) ⊆ opExposed(orig)` holds, and the gate
re-checks it regardless). -/
mutual
def ensureEv : Nat → EvSt → Nat → Option EvSt
  | 0, _, _ => none
  | fuel + 1, ev, node =>
      match findIdx node ev.es.model.stack with
      | some _ => some ev
      | none =>
          match ev.es.dag.node node with
          | .lit v => emitEv ev (.push v)
          | .inp _ => none
          | .app op args =>
              match ensureArgsEv fuel ev args with
              | none => none
              | some ev1 =>
                  match arrangeArgs fuel ev1 args.reverse with
                  | none => none
                  | some ev2 => emitEv ev2 (.op op)
def ensureArgsEv : Nat → EvSt → List Nat → Option EvSt
  | _, ev, [] => some ev
  | 0, _, _ => none
  | fuel + 1, ev, a :: rest =>
      match ensureEv fuel ev a with
      | none => none
      | some ev1 => ensureArgsEv fuel ev1 rest
def arrangeArgs : Nat → EvSt → List Nat → Option EvSt
  | _, ev, [] => some ev
  | 0, _, _ => none
  | fuel + 1, ev, a :: rest =>
      match arrange1 fuel ev a with
      | none => none
      | some ev' => arrangeArgs fuel ev' rest
def arrange1 : Nat → EvSt → Nat → Option EvSt
  | 0, _, _ => none
  | fuel + 1, ev, a =>
      match findIdx a ev.es.model.stack with
      | none => recompute fuel ev a
      | some depth =>
          -- input leaves are NEVER consumed (always DUP): the k inputs stay pinned
          -- at their canonical positions so the store-in-place writeback can find
          -- and overwrite them. Only intermediates are moved/consumed at last use.
          let isInp := match ev.es.dag.node a with | .inp _ => true | _ => false
          if h : depth < 16 then
            if ev.rem[a]! ≤ 1 && !isInp then
              if depth == 0 then some (ev.dec a)
              else (emitEv ev (.swap ⟨depth - 1, by omega⟩)).map (fun ev => ev.dec a)
            else (emitEv ev (.dup ⟨depth, h⟩)).map (fun ev => ev.dec a)
          else if isInp then none else recompute fuel ev a
def recompute : Nat → EvSt → Nat → Option EvSt
  | 0, _, _ => none
  | fuel + 1, ev, a =>
      match ev.es.dag.node a with
      | .lit v => emitEv ev (.push v)
      | .inp _ => none
      | .app op args =>
          match args.reverse.foldlM (fun ev x => bringDup fuel ev x) ev with
          | none => none
          | some ev' => emitEv ev' (.op op)
def bringDup : Nat → EvSt → Nat → Option EvSt
  | 0, _, _ => none
  | fuel + 1, ev, a =>
      match findIdx a ev.es.model.stack with
      | some d => if h : d < 16 then emitEv ev (.dup ⟨d, h⟩) else recompute fuel ev a
      | none => recompute fuel ev a
end

/-- **Interleaved topological driver.** Node-id order is a topological order (a
child is interned before its parent, so has a smaller id) AND it is program
order (symExec interned in program order). Computing every reachable `app` in
ascending id order therefore interleaves the outputs' shared sub-chains: a value
(e.g. a log2 block's `f_i`) is produced and then consumed by BOTH its consumers
(the next r-chain step and the log_2 accumulation, which are adjacent in program
order) right away — so it dies within its block and the live set stays small
(~4 + the k inputs), instead of the output-by-output driver keeping every `f_i`
alive until a later output. Consumers MOVE at last use via `arrange1`. -/
def scheduleTopo (d : Dag) (target : SymState) (fuel : Nat) : Option (List Asm) :=
  let T := target.stack
  let m := T.length
  let k := target.inputs
  if m > 16 then none else
  let rem := computeRem d T
  let n := d.nodes.size
  let ev0 : EvSt := ⟨initES d k, rem⟩
  if m == 0 then (emitPops ev0.es k).map ES.code else
  match (List.range n).foldlM (fun ev id =>
      if rem[id]! > 0 then
        match d.node id with
        | .app op args =>
            if (findIdx id ev.es.model.stack).isSome then some ev
            else match arrangeArgs fuel ev args.reverse with
                 | none => none
                 | some ev' => emitEv ev' (.op op)
        | _ => some ev
      else some ev) ev0 with
  | none => none
  | some ev1 =>
      let b := ev1.es.model.stack.length
      let rot := b % m
      match (List.range m).reverse.foldlM
          (fun ev j => bringDup fuel ev (T[(j + (m - rot)) % m]?.getD 0)) ev1 with
      | none => none
      | some ev2 => (emitCleanup m ev2.es b).map ES.code

/-- Stack index of the input leaf `inp j`. -/
def findInpSlot (d : Dag) (j : Nat) (stack : List Nat) : Option Nat :=
  stack.findIdx? (fun x => match d.node x with | .inp i => i == j | _ => false)

/-- Write the (already-computed) value `id` into canonical slot `j`: bring `id`
to the top (consuming it — last use), then `swap; pop` it into `inp j`'s
position, overwriting the dead input there. -/
def storeChanged (fuel : Nat) (ev : EvSt) (jid : Nat × Nat) : Option EvSt :=
  match arrange1 fuel ev jid.2 with
  | none => none
  | some ev =>
      match findInpSlot ev.es.dag jid.1 ev.es.model.stack with
      | none => none
      | some depth =>
          if h : 0 < depth ∧ depth - 1 < 16 then
            (emitEv ev (.swap ⟨depth - 1, h.2⟩)).bind (fun ev => emitEv ev .pop)
          else none

/-- **Topo phase-1 + store-into-canonical-slots phase-2** (the decisive combine).
Canonical windows only (`m = k`, non-changed slots identity). Phase-1 computes
every reachable node once in id order (interleaved → small live set; inputs kept
intact by `arrange1`). Phase-2 `swap;pop`s each changed output into its slot,
overwriting the dead input; identity slots are never touched — no relocate, no
rotating cleanup, no separate output DUP. -/
def scheduleTopoStore (d : Dag) (target : SymState) (fuel : Nat) : Option (List Asm) :=
  let T := target.stack
  let m := T.length
  let k := target.inputs
  if m != k then none else
  let slots := T.zipIdx
  let hasMove := slots.any (fun (id, j) => match d.node id with | .inp i => i != j | _ => false)
  if hasMove then none else
  let changed := slots.filterMap (fun (id, j) =>
    match d.node id with | .inp _ => none | _ => some (j, id))
  let rem := computeRem d T
  let n := d.nodes.size
  let ev0 : EvSt := ⟨initES d k, rem⟩
  match (List.range n).foldlM (fun ev id =>
      if rem[id]! > 0 then
        match d.node id with
        | .app op args =>
            if (findIdx id ev.es.model.stack).isSome then some ev
            else match arrangeArgs fuel ev args.reverse with
                 | none => none
                 | some ev' => emitEv ev' (.op op)
        | _ => some ev
      else some ev) ev0 with
  | none => none
  | some ev1 => (changed.foldlM (fun ev jid => storeChanged fuel ev jid) ev1).map
      (fun ev => ev.es.code)

/-- Eviction-aware scheduler: compute every output (consuming intermediates at
last use), then DUP the outputs into pre-rotated place and remove the (now small)
remainder with the rotating cleanup. -/
def scheduleEvict (d : Dag) (target : SymState) (fuel : Nat) : Option (List Asm) :=
  let T := target.stack
  let m := T.length
  let k := target.inputs
  if m > 16 then none else
  let ev0 : EvSt := ⟨initES d k, computeRem d T⟩
  if m == 0 then (emitPops ev0.es k).map ES.code else
  match T.foldlM (fun ev node => ensureEv fuel ev node) ev0 with
  | none => none
  | some ev1 =>
      let b := ev1.es.model.stack.length
      let rot := b % m
      match (List.range m).reverse.foldlM
          (fun ev j => bringDup fuel ev (T[(j + (m - rot)) % m]?.getD 0)) ev1 with
      | none => none
      | some ev2 => (emitCleanup m ev2.es b).map ES.code

/-- Candidate schedules; the gate keeps the cheapest valid one. -/
def scheduleCandidates (d : Dag) (target : SymState) : List (List Asm) :=
  let fuel := 16 * (reachCount d target.stack) + 200
  (scheduleTopoStore d target fuel).toList
    ++ (scheduleTopo d target fuel).toList
    ++ (scheduleEvict d target fuel).toList
    ++ (scheduleLinear d target fuel).toList
    ++ (scheduleStoreInPlace d target fuel).toList
    ++ (scheduleRebuild d target fuel).toList

/-! ### Window extraction + gate -/

/-- Window length cap. The DAG keeps `symExec` linear, but the current scheduler
still rebuilds (no CSE materialization), so bigger windows rebuild more and
measure WORSE (128 → +1600 on the sweep); 48 is the empirical sweet spot until a
CSE-materializing linear scheduler lands, at which point this should rise. -/
def maxWindowLen : Nat := 48

/-- Reachable-node budget guarding scheduler cost. -/
def maxTermNodes : Nat := 4096

/-- Optimize one window: keep the cheapest candidate that is net-effect-equal
(`symStateEquiv`), op-exposes ⊆ the original's inputs, reaches no DEEPER than the
original (`tcand.inputs ≤ target.inputs`, so it can't underflow a shallow stack
the source handled — `symStateEquiv` is symmetric and would otherwise miss this),
is strictly cheaper, and does not grow bytes; else keep the original. -/
def optimizeWindow (w : List Asm) : List Asm :=
  if w.length > maxWindowLen then w else
  match symExec w with
  | none => w
  | some (target, d1) =>
      if reachCount d1 target.stack > maxTermNodes then w else
      (scheduleCandidates d1 target).foldl (fun best cand =>
        match symExecFrom d1 cand with
        | some (tcand, d2) =>
            if symStateEquiv d2 tcand target
                && tcand.opExposed.all (· ∈ target.opExposed)
                && tcand.inputs ≤ target.inputs
                && windowGas cand < windowGas best
                && codeSize cand ≤ codeSize w then cand else best
        | none => best) w

/-- Is a prefix height-preserving (`m = k`) with a bounded DAG? -/
def isCanonicalWindow (w : List Asm) : Bool :=
  match symExec w with
  | some (s, d) => s.stack.length == s.inputs && reachCount d s.stack ≤ maxTermNodes
  | none => false

/-- Largest canonical prefix (≤ `maxWindowLen`), else the cap. Always ≥ 1. -/
def cutLen (run : List Asm) : Nat :=
  let cap := Nat.min run.length maxWindowLen
  match (((List.range cap).map (· + 1)).filter (fun j => isCanonicalWindow (run.take j))).getLast? with
  | some j => j
  | none => Nat.max 1 cap

/-- Split into windows (cut at canonical boundaries) and non-window instructions,
optimizing each window. Fuel-bounded; `p.length + 1` suffices. -/
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

/-- The Asm-level window scheduler run by `compile` (after `optimizeAsm`, before
the `stackOK2` gate). Total; keeps its input on any doubt. -/
def scheduleAsm (p : List Asm) : List Asm := scheduleAsmFuel (p.length + 1) p

end YulEvmCompiler.Schedule
