import YulIR.Analysis
import YulIR.Effects
import YulIR.Structural

/-!
# YulIR.StoreElim — dead *store* elimination for `sstore` / `mstore` / `tstore`

The `YulIR.DeadStore` pass removes dead *variable* assignments (`x := <pure rhs>`). This pass
is its counterpart for the three memory-like **stores** that Yul emits as value-less effect
statements — `sstore(key, val)`, `mstore(off, val)` and `tstore(key, val)` — i.e. solc's
`unusedStoreEliminator` / `equalStoreEliminator` in the *overwritten-store* direction.

## What is removed

A store `D-store(loc, val)` is removed when, on **every** forward path, `loc` is overwritten by a
later `D`-store to the provably-same location before any operation can **observe domain `D`** (no
read of `D`, no call/create/… that could observe it). The later store makes this one's value
unobservable, so the final `D`-contents are unchanged and dropping it changes nothing observable.

The source `yul-semantics` is **gas-free**: it does not model gas or the EVM `SSTORE` refund
counter, so those are not part of the observable *results* this pass must preserve (the differential
harness likewise ignores the refund — see `YulEvmCompilerTests.SolcDifferential`). Removal is
therefore uniform across the three domains and independent of the stored *value*; only the location
must match. Because the killing store is to the *same* slot, final contents and — for memory — the
active-word count / `msize` (which `yul-semantics` *does* model, and the round-trip fingerprint
samples) are preserved exactly.

## Aliasing model (why syntactic equality is sound here)

Two locations are treated as equal only when their `Atom`s are syntactically equal *and* stable:
a literal, or a variable never reassigned anywhere in the program (`mutatedVars`). Running after
`valueNumber` (which canonicalises constants/copies of *immutable* values) means equal syntactic
atoms denote equal runtime values; the immutability side-condition rules out
`sstore(x,a); x := f(); sstore(x,b)`, where the two `x`s are different slots.

## Analysis

A backward pass mirroring `YulIR.DeadStore`'s liveness, computing per domain the set of locations
known to be overwritten-before-observed downstream ("clobbered"):

* a kept store to a stable `loc` **adds** `loc` to its domain's clobber set;
* any op that **reads** a domain (or a call/create/user-call that may observe everything) **clears**
  the relevant set(s) — a downstream reader means an earlier store is observable, hence not dead;
* a **terminator** (`stop`/`invalid`/`return`/`revert`/`selfdestruct`) resets to the empty clobber
  state: control leaves, storage/transient persist (observable) and returned memory is read;
* `if`/`switch` **intersect** their branches (must-overwrite on *all* paths; a `switch` with no
  `default`, and every `if`, includes the fall-through path);
* **loops** and function bodies are analysed with an empty incoming clobber state (conservative: a
  store before a loop, or spanning a call boundary, is never assumed dead), so only local overwrites
  inside them are caught.

Only ever removing a *provably overwritten* store, so any imprecision costs an opportunity, never
correctness.
-/

namespace YulIR

open YulSemantics (Ident Literal)

/-- The three store domains this pass tracks. -/
inductive Dom
  | storage | transient | memory
  deriving DecidableEq

/-- Syntactic atom equality (via the derived `DecidableEq`), avoiding a `BEq Atom` instance. -/
def atomEq (a b : Atom) : Bool := decide (a = b)

/-- Membership of an atom in a list, by syntactic equality. -/
def atomMem (a : Atom) (l : List Atom) : Bool := l.any (atomEq a)

/-- Per-domain sets of locations known to be overwritten-before-observed downstream. -/
structure Clob where
  sClob : List Atom := []
  tClob : List Atom := []
  mClob : List Atom := []

/-- Nothing known to be clobbered (the safe/empty state). -/
def Clob.empty : Clob := {}

/-- Read the clobber set for a domain. -/
def Clob.get : Clob → Dom → List Atom
  | c, .storage   => c.sClob
  | c, .transient => c.tClob
  | c, .memory    => c.mClob

/-- Is `loc` known clobbered in domain `d`? -/
def Clob.has (c : Clob) (d : Dom) (loc : Atom) : Bool := atomMem loc (c.get d)

/-- Record `loc` as clobbered in domain `d`. -/
def Clob.add (c : Clob) (d : Dom) (loc : Atom) : Clob :=
  match d with
  | .storage   => { c with sClob := loc :: c.sClob }
  | .transient => { c with tClob := loc :: c.tClob }
  | .memory    => { c with mClob := loc :: c.mClob }

/-- Meet (path intersection): a slot stays clobbered only if clobbered on both incoming paths. -/
def Clob.meet (a b : Clob) : Clob :=
  { sClob := a.sClob.filter (fun x => atomMem x b.sClob)
    tClob := a.tClob.filter (fun x => atomMem x b.tClob)
    mClob := a.mClob.filter (fun x => atomMem x b.mClob) }

/-- Intersect a list of clobber states (empty ⇒ nothing known). -/
def Clob.meetAll : List Clob → Clob
  | []      => Clob.empty
  | c :: cs => cs.foldl Clob.meet c

open YulSemantics.EVM (Op)

/-- The domain a store operation writes (only meaningful for the three store ops). -/
def storeDom : Op → Option Dom
  | .sstore => some .storage
  | .tstore => some .transient
  | .mstore => some .memory
  | _       => none

/-- How an op observes the tracked domains. `escape` clears everything (calls/creates may read and
re-enter); the `rd*` flags clear the corresponding domain (a downstream read makes an earlier store
to that domain observable). Ops that only touch untracked state (calldata, world, gas, external
accounts) — and blind writers like `mstore8` / the `*copy`-into-memory ops, which never read the
prior contents — are neutral. See `YulSemantics.EVM.effects` for the audited read/write table. -/
structure OpObs where
  escape      : Bool := false
  rdStorage   : Bool := false
  rdTransient : Bool := false
  rdMemory    : Bool := false

/-- Observation classification of a built-in (assumed not a terminator, handled separately). -/
def opObs : Op → OpObs
  -- may observe and mutate the whole world, and re-enter this contract
  | .call | .callcode | .delegatecall | .staticcall | .create | .create2 =>
      { escape := true }
  | .sload => { rdStorage := true }
  | .tload => { rdTransient := true }
  -- read memory *contents* (mload/keccak/mcopy) or memory *size* (msize, which observes the
  -- expansion an mstore causes); log* read the logged memory region.
  | .mload | .keccak256 | .mcopy | .msize
  | .log0 | .log1 | .log2 | .log3 | .log4 => { rdMemory := true }
  | _ => {}

/-- Apply an op's observation to the incoming (downstream) clobber state. -/
def applyObs (after : Clob) (o : OpObs) : Clob :=
  if o.escape then Clob.empty
  else
    { sClob := if o.rdStorage   then [] else after.sClob
      tClob := if o.rdTransient then [] else after.tClob
      mClob := if o.rdMemory    then [] else after.mClob }

/-- Clobber effect of evaluating an rhs (for its reads/escapes; store *writes* are handled by the
statement transfer, not here). User calls are conservatively full escapes. -/
def rhsObs (after : Clob) : Rhs → Clob
  | .atom _        => after
  | .call _ _      => Clob.empty
  | .builtin op _  => if Op.isHalting op then Clob.empty else applyObs after (opObs op)

/-- Context threaded through the backward pass: the globally-immutable variables (whose `.var`
atoms are stable locations), and the clobber states at the targets of `break`/`continue`. -/
structure SCtx where
  mutated : List Ident
  brk     : Clob
  cont    : Clob

/-- Is `loc` a stable location? A literal, or a variable never reassigned program-wide. -/
def SCtx.stable (c : SCtx) : Atom → Bool
  | .lit _ => true
  | .var x => ! c.mutated.contains x

mutual
/-- Backward transfer for one statement: rewritten statement (or `none` if the store is removed)
and the clobber state *before* it, given the state `after` it. -/
partial def storeStmt (c : SCtx) (after : Clob) : Stmt → (Option Stmt × Clob)
  | .effect (.builtin op [loc, val]) =>
      match storeDom op with
      | some d =>
          let stable := c.stable loc
          if stable && after.has d loc then
            (none, after)                                   -- overwritten downstream: drop
          else
            let after' := if stable then after.add d loc else after
            (some (.effect (.builtin op [loc, val])), after')
      | none =>
          if Op.isHalting op then (some (.effect (.builtin op [loc, val])), Clob.empty)
          else (some (.effect (.builtin op [loc, val])), applyObs after (opObs op))
  | .effect rhs =>
      (some (.effect rhs), rhsObs after rhs)
  | .letD xs rhs   => (some (.letD xs rhs), rhsObs after rhs)
  | .assign xs rhs => (some (.assign xs rhs), rhsObs after rhs)
  | .cond cnd body =>
      let (body', clobBody) := storeBlock c after body
      (some (.cond cnd body'), Clob.meet clobBody after)    -- taken vs skipped
  | .switch cnd cases dflt =>
      let cases' := cases.map (fun p => let (b', cb) := storeBlock c after p.2; ((p.1, b'), cb))
      let dfltRes := dflt.map (fun b => storeBlock c after b)
      -- no `default` ⇒ an unmatched value falls straight through to `after`
      let dfltClob := (dfltRes.map (·.2)).getD after
      let merged := Clob.meetAll ((cases'.map (·.2)) ++ [dfltClob])
      (some (.switch cnd (cases'.map (·.1)) (dfltRes.map (·.1))), merged)
  | .loop post body =>
      -- `break` exits to after the loop; the back-edge (fall-through / `continue`) re-enters the
      -- head, analysed conservatively with an empty state. Nothing is assumed clobbered before a
      -- loop (its body may read on the first iteration).
      let cInner : SCtx := { mutated := c.mutated, brk := after, cont := Clob.empty }
      let (post', _) := storeBlock cInner Clob.empty post
      let (body', _) := storeBlock cInner Clob.empty body
      (some (.loop post' body'), Clob.empty)
  | .block body =>
      let (body', clobIn) := storeBlock c after body
      (some (.block body'), clobIn)
  | .funDef n ps rs body =>
      -- a fresh control scope; return to the caller may observe every domain
      let (body', _) := storeBlock { mutated := c.mutated, brk := Clob.empty, cont := Clob.empty }
                          Clob.empty body
      (some (.funDef n ps rs body'), after)                 -- declaring a function clobbers nothing
  | .«break»    => (some .«break», c.brk)
  | .«continue» => (some .«continue», c.cont)
  | .leave      => (some .leave, Clob.empty)

/-- Backward transfer over a block: rewritten block and the clobber state at its entry. -/
partial def storeBlock (c : SCtx) (after : Clob) : Block → (Block × Clob)
  | []      => ([], after)
  | s :: rest =>
      let (rest', clobMid) := storeBlock c after rest
      let (s', clobIn) := storeStmt c clobMid s
      match s' with
      | some st => (st :: rest', clobIn)
      | none    => (rest', clobIn)
end

/-- Overwritten-store elimination over a whole program. The top level observes no domain by
overwrite, so the last store to each slot is always kept. -/
def storeElim (b : Block) : Block :=
  (storeBlock { mutated := mutatedVars b, brk := Clob.empty, cont := Clob.empty } Clob.empty b).1

end YulIR
