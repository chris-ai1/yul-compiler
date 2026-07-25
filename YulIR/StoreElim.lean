import YulIR.Analysis
import YulIR.Effects
import YulIR.Structural

/-!
# YulIR.StoreElim — dead *store* elimination for `sstore` / `mstore` / `tstore`

The `YulIR.DeadStore` pass removes dead *variable* assignments (`x := <pure rhs>`). This pass
is its counterpart for the three memory-like **stores** that Yul emits as value-less effect
statements — `sstore(key, val)`, `mstore(off, val)` and `tstore(key, val)` — i.e. solc's
`unusedStoreEliminator` / `equalStoreEliminator` in the *overwritten-store* direction.

## What is removed, and the storage-refund subtlety

A store `D-store(loc, val)` is a candidate for removal when, on **every** forward path, `loc` is
overwritten by a later `D`-store to the provably-same location before any operation can **observe
domain `D`** (no read of `D`, no call/create/… that could observe it). Removing it leaves the final
`D`-contents unchanged. The catch is **EVM storage gas refunds**: for *storage* (and only storage),
the intermediate value written is observable through `SSTORE`'s refund accounting, which depends on
the `(original, current, new)` value transitions of the slot — so dropping an overwritten `sstore`
whose value *differs* from the one that overwrites it changes the transaction's refund, and hence
observable gas. (See `equalStoreEliminator/value_change.yul` in Solidity's corpus, marked "cannot be
removed".) The rule is therefore split by domain:

* **memory** (`mstore`) and **transient** (`tstore`): no refund mechanism exists, so an overwritten
  store is removed on a **location-only** match. Because the killing store is to the *same* slot,
  the final contents and — for memory — the active-word count / `msize` (which the round-trip
  correctness fingerprint samples) are preserved exactly.
* **storage** (`sstore`): removed only when the overwriting store writes a **provably-equal value**
  (`equalStoreEliminator`). Collapsing two same-slot, same-value stores separated only by
  storage-non-observing statements leaves every `(original, current, new)` transition — and thus the
  refund — identical. Different-value overwrites are kept.

## Aliasing model (why syntactic equality is sound here)

Two locations/values are treated as equal only when their `Atom`s are syntactically equal *and*
stable: a literal, or a variable never reassigned anywhere in the program (`mutatedVars`). Running
after `valueNumber` (which canonicalises constants/copies of *immutable* values) means equal
syntactic atoms denote equal runtime values; the immutability side-condition rules out
`sstore(x,a); x := f(); sstore(x,b)`, where the two `x`s are different slots (and likewise for the
value atom, so `value_change.yul` — whose value `y` is reassigned — is correctly not touched).

## Analysis

A backward pass mirroring `YulIR.DeadStore`'s liveness, computing per domain the locations known to
be overwritten-before-observed downstream ("clobbered"); for storage the overwriting *value* is
tracked too:

* a kept store to a stable `loc` **adds** it to its domain's clobber set (storage records `(loc,val)`);
* any op that **reads** a domain (or a call/create/user-call that may observe everything) **clears**
  the relevant set(s) — a downstream reader means an earlier store is observable, hence not dead;
* a **terminator** (`stop`/`invalid`/`return`/`revert`/`selfdestruct`) resets to the empty clobber
  state: control leaves, storage/transient persist (observable) and returned memory is read;
* `if`/`switch` **intersect** their branches (must-overwrite on *all* paths; a `switch` with no
  `default`, and every `if`, includes the fall-through path);
* **loops** and function bodies are analysed with an empty incoming clobber state (conservative: a
  store before a loop, or spanning a call boundary, is never assumed dead), so only local overwrites
  inside them are caught.

Only ever removing a *provably overwritten* store (value-equal, for storage), so any imprecision
costs an opportunity, never correctness.
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

/-- Per-domain "clobbered downstream" sets. Storage carries the overwriting *value* alongside the
slot (removal requires value-equality, to preserve the SSTORE refund); memory and transient carry
the location only (no refund exists for them). -/
structure Clob where
  sClob : List (Atom × Atom) := []   -- (slot, value)
  tClob : List Atom := []
  mClob : List Atom := []

/-- Nothing known to be clobbered (the safe/empty state). -/
def Clob.empty : Clob := {}

/-- Is `(loc, val)` a redundant *storage* store — a downstream same-slot store of an equal value? -/
def Clob.hasStorage (c : Clob) (loc val : Atom) : Bool :=
  c.sClob.any (fun p => atomEq p.1 loc && atomEq p.2 val)

/-- Is `loc` clobbered in transient/memory (location-only)? -/
def Clob.hasLoc (c : Clob) : Dom → Atom → Bool
  | .transient, loc => atomMem loc c.tClob
  | .memory,    loc => atomMem loc c.mClob
  | .storage,   _   => false      -- storage uses `hasStorage`

/-- Record a kept store as clobbering its slot for statements before it. -/
def Clob.add (c : Clob) : Dom → Atom → Atom → Clob
  | .storage,   loc, val => { c with sClob := (loc, val) :: c.sClob }
  | .transient, loc, _   => { c with tClob := loc :: c.tClob }
  | .memory,    loc, _   => { c with mClob := loc :: c.mClob }

/-- Meet (path intersection): a fact survives only if present on both incoming paths. Storage
requires the same `(slot, value)`; memory/transient the same location. -/
def Clob.meet (a b : Clob) : Clob :=
  { sClob := a.sClob.filter (fun p => b.sClob.any (fun q => atomEq p.1 q.1 && atomEq p.2 q.2))
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
atoms are stable locations/values), and the clobber states at the targets of `break`/`continue`. -/
structure SCtx where
  mutated : List Ident
  brk     : Clob
  cont    : Clob

/-- Is `a` a stable atom — a literal, or a variable never reassigned program-wide? -/
def SCtx.stable (c : SCtx) : Atom → Bool
  | .lit _ => true
  | .var x => ! c.mutated.contains x

/-- Decide a candidate store: `none` result means "remove it". Also returns the clobber state to
propagate to statements before it. -/
def SCtx.storeStep (c : SCtx) (after : Clob) (d : Dom) (op : Op) (loc val : Atom) :
    Option Stmt × Clob :=
  let kept := some (.effect (.builtin op [loc, val]))
  match d with
  | .storage =>
      -- refund-safe: remove only when the overwriting store writes an equal value
      if c.stable loc && c.stable val then
        if after.hasStorage loc val then (none, after)
        else (kept, after.add .storage loc val)
      else (kept, after)                             -- unstable ⇒ can't track this slot/value
  | _ =>
      -- memory / transient: location-only overwrite (no refund)
      if c.stable loc then
        if after.hasLoc d loc then (none, after)
        else (kept, after.add d loc val)
      else (kept, after)

mutual
/-- Backward transfer for one statement: rewritten statement (or `none` if the store is removed)
and the clobber state *before* it, given the state `after` it. -/
partial def storeStmt (c : SCtx) (after : Clob) : Stmt → (Option Stmt × Clob)
  | .effect (.builtin op [loc, val]) =>
      match storeDom op with
      | some d => c.storeStep after d op loc val
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
