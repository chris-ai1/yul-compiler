import YulEvmCompiler.Optimizer.Implementation.InlineHelpersResolve
import YulEvmCompiler.Optimizer.Implementation.PropagateResolve
import YulEvmCompiler.Optimizer.Implementation.DeadLitsResolve
import YulEvmCompiler.Optimizer.Implementation.InlineCallsResolve
import YulEvmCompiler.Optimizer.Implementation.DeadPureResolve
import YulEvmCompiler.Optimizer.Implementation.DeadResultsResolve
import YulEvmCompiler.Optimizer.Implementation.FreshenCallsResolve
import YulEvmCompiler.Optimizer.Implementation.HoistCallsResolve
import YulEvmCompiler.Optimizer.Implementation.StorageForwardResolve
import YulEvmCompiler.Optimizer.Implementation.ObjectPass
import YulEvmCompiler.Optimizer.Implementation.Normalization.HoistForInitResolve
set_option warningAsError true
/-!
# Production optimizer pipeline

The production pipeline simplifies expressions (constant folding, neutral
identities including the open-operand forms), propagates known bindings
(`Propagate`: constant propagation plus depth-gated copy propagation, both
binding-preserving), inlines pure expression-body helpers through the Core
boundary (`InlineHelpers`), hoists direct unary nested calls and freshens
result sites before inlining call-free statement-body helpers (`HoistCalls`,
`FreshenCalls`, `InlineCalls`), forwards cheap values written to literal storage
slots through later loads (`StorageForward`), simplifies again, prunes dead pure
bindings and self-assignments (`DeadPure`, subsuming the earlier `DeadLits`),
and removes
unused result slots together with adjacent total, state-preserving readback
regions (`DeadResults`). The whole round is **iterated** (`pipelineRounds`): statement-level inlining collapses
helper chains leaf-first — a call-free callee inlines this round, which makes
its caller call-free for the next round — and each round's leftovers
(parameter/result copy bindings, zero-initialized returns) feed the next
round's propagation and pruning, which in turn shrink helper bodies back
under the inlining guards.

Stage order differs by path, deliberately:

* **block path** (`optimizerPipeline`): `simplify → propagate → inline(litOK)
  → hoistCalls → freshenCalls → inlineCalls → storageForward → simplify
  → deadPure → deadResults`.
  Propagation runs *before* the inliner
  because the block-path inliner accepts literal arguments (`litOK := true`) —
  substituted constants make more call sites flat and inlinable.
* **object path** (`objectPipeline`): `simplify → inline(var-only) →
  propagate → hoistCalls → freshenCalls → inlineCalls → storageForward →
  simplify → deadPure → deadResults`. The object-path inliner is
  variable-only (`litOK := false`, the resolution-stable mode), so propagation
  runs *after* it — running first would turn variable arguments into literals
  and starve it. `Propagate`, `DeadPure`, and `InlineCalls` need no restricted
  object mode: their soundness is proven for relations closed under layout
  resolution, so the whole-tree object correctness theorem composes with the
  full passes.

The object path additionally needs each stage to commute with layout
resolution up to `EquivBlock` — bundled per stage as `RPass` and composed over
the whole iterated pipeline by `RPass.resolve_equiv_ofList`.
-/

namespace YulEvmCompiler.Optimizer

open EvmSemantics EvmSemantics.EVM
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### Resolution-congruent passes -/

/-- A verified pass bundled with its layout-resolution congruence: running the
pass before resolution is equivalent (pointwise) to not running it, *on the
resolved code*. This is the per-stage fact `optimizerPipelineObject_correct`
composes over the whole pipeline. -/
structure RPass (calls : ExternalCalls) (creates : ExternalCreates) where
  pass : LocalPass (evmWithExternal calls creates)
  resolve_equiv : ∀ (L : Layout) (b : Block Op),
    EquivBlock (evmWithExternal calls creates)
      (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (pass.run b))

/-- The resolution congruence extends from stages to a whole pipeline. -/
theorem RPass.resolve_equiv_ofList (ps : List (RPass calls creates))
    (L : Layout) (b : Block Op) :
    EquivBlock D
      (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L ((LocalPass.ofList (ps.map (·.pass))).run b)) := by
  induction ps generalizing b with
  | nil => exact EquivBlock.refl _
  | cons p rest ih =>
      exact (p.resolve_equiv L b).trans (ih (p.pass.run b))

/-! ### The stage lists -/

/-- Rounds of the iterated pipeline. Helper chains in solc's unoptimized IR
are ~5 calls deep (`external_fun_*` → `abi_decode_tuple_*` → `abi_decode_t_*`
→ `validator_revert_*` → `cleanup_*`); each round collapses the current
call-free leaves. -/
def pipelineRounds : Nat := 6

/-- One block-path round. `hoistForInit` runs first so the pulled-out
initializers become ordinary block statements the later stages optimize. -/
def blockRound : List (LocalPass D) :=
  [hoistForInit, simplify, propagate, inlineHelpersPass true, hoistCalls, freshenCalls, inlineCalls,
   storageForward, simplify, deadPure, deadResults]

/-- Verified block pipeline at an explicit round count. Iterated inlining can
push a caller's live locals past the backend's `DUP16`/`SWAP16` reach; fewer
rounds keep frames shallower, so `compileSource` retries a **light**
(one-round) pipeline before giving up on optimization entirely. -/
def optimizerPipelineRounds (n : Nat) : LocalPass D :=
  LocalPass.ofList ((List.replicate n (blockRound (calls := calls)
    (creates := creates))).flatten)

/-- Verified production pipeline for top-level blocks: the round, iterated. -/
def optimizerPipeline : LocalPass D :=
  optimizerPipelineRounds pipelineRounds

/-- The light (one-round) block pipeline, the middle compile fallback. -/
def optimizerPipelineLight : LocalPass D :=
  optimizerPipelineRounds 1

/-- One object-path round, with each stage's resolution congruence. -/
def objectRound : List (RPass calls creates) :=
  [⟨hoistForInit, fun L b => resolveHoistForInitBlock_equiv L b⟩,
   ⟨simplify, fun L b => resolveSimplifyBlock_equiv L b⟩,
   ⟨inlineHelpersPass false, fun L b => by
      have hi := (inlineHelpersPass (calls := calls) (creates := creates) false).sound
        (resolveForLayoutStmts L b)
      change EquivBlock D (resolveForLayoutStmts L b)
        (inlineHelpersBlock (calls := calls) (creates := creates) false ([] : FunEnv D)
          (resolveForLayoutStmts L b)) at hi
      rw [← resolve_inlineHelpersBlock_nil L b] at hi
      exact hi⟩,
   ⟨propagate, fun L b => by
      have hp := resolvePropagateBlock_equiv (calls := calls) (creates := creates) L b
      simpa [propagateBlock] using hp⟩,
   ⟨hoistCalls, fun L b => resolveHoistCallsBlock_equiv L b⟩,
   ⟨freshenCalls, fun L b => resolveFreshenCallsBlock_equiv L b⟩,
   ⟨inlineCalls, fun L b => resolveInlineCallsBlock_equiv L b⟩,
   ⟨storageForward, fun L b => resolveStorageForwardBlock_equiv L b⟩,
   ⟨simplify, fun L b => resolveSimplifyBlock_equiv L b⟩,
   ⟨deadPure, fun L b => resolveDeadPureBlock_equiv L b⟩,
   ⟨deadResults, fun L b => resolveDeadResultsBlock_equiv L b⟩]

/-- Verified object pipeline at an explicit round count (see
`optimizerPipelineRounds` for why the count varies). -/
def objectPipelineRounds (n : Nat) : LocalPass D :=
  LocalPass.ofList (((List.replicate n (objectRound (calls := calls)
    (creates := creates))).flatten).map (·.pass))

/-- Verified pipeline for object code blocks: the round, iterated. -/
def objectPipeline : LocalPass D :=
  objectPipelineRounds pipelineRounds

/-- Resolution congruence for the iterated object pipeline, any round count. -/
theorem resolveObjectPipelineRoundsBlock_equiv (n : Nat) (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L
        ((objectPipelineRounds (calls := calls) (creates := creates) n).run b)) :=
  RPass.resolve_equiv_ofList _ L b

/-- Resolution congruence for the complete iterated object pipeline. -/
theorem resolveObjectPipelineBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L
        ((objectPipeline (calls := calls) (creates := creates)).run b)) :=
  RPass.resolve_equiv_ofList _ L b

mutual
  /-- Run the verified object pipeline (at a round count) on every object
  code block. -/
  def optimizerPipelineObjectRounds (n : Nat) : Object Op → Object Op
    | .mk name code subs segs =>
        .mk name
          ((objectPipelineRounds (calls := calls) (creates := creates) n).run code)
          (optimizerPipelineObjectsRounds n subs) segs

  /-- Run the verified object pipeline on every object in a list. -/
  def optimizerPipelineObjectsRounds (n : Nat) : List (Object Op) → List (Object Op)
    | [] => []
    | o :: rest =>
        optimizerPipelineObjectRounds n o :: optimizerPipelineObjectsRounds n rest
end

/-- Run the verified object pipeline on every object code block. -/
def optimizerPipelineObject : Object Op → Object Op :=
  optimizerPipelineObjectRounds (calls := calls) (creates := creates)
    pipelineRounds

/-- The light (one-round) whole-tree optimizer, the middle compile fallback. -/
def optimizerPipelineObjectLight : Object Op → Object Op :=
  optimizerPipelineObjectRounds (calls := calls) (creates := creates) 1

@[simp] theorem optimizerPipelineObjectRounds_codeBlock (n : Nat) (o : Object Op) :
    (optimizerPipelineObjectRounds (calls := calls) (creates := creates) n o).codeBlock =
      (objectPipelineRounds (calls := calls) (creates := creates) n).run o.codeBlock := by
  cases o
  rfl

@[simp] theorem optimizerPipelineObject_codeBlock (o : Object Op) :
    (optimizerPipelineObject (calls := calls) (creates := creates) o).codeBlock =
      (objectPipeline (calls := calls) (creates := creates)).run o.codeBlock := by
  cases o
  rfl

/-- The recursively optimized artifact (any round count) is covered directly
by the verified object compiler theorem. -/
theorem optimizerPipelineObjectRounds_compileObject_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model) (n : Nat)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject
      (optimizerPipelineObjectRounds (calls := model.calls) (creates := model.creates) n o)
        = some L)
    {V : VEnv (evmWithExternal model.calls model.creates)}
    {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject
      (optimizerPipelineObjectRounds (calls := model.calls) (creates := model.creates) n o)
      L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) :=
  compileObject_correct hexternal hcomp hrun

/-- The recursively optimized artifact is covered directly by the verified
object compiler theorem. -/
theorem optimizerPipelineObject_compileObject_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject
      (optimizerPipelineObject (calls := model.calls) (creates := model.creates) o)
        = some L)
    {V : VEnv (evmWithExternal model.calls model.creates)}
    {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject
      (optimizerPipelineObject (calls := model.calls) (creates := model.creates) o)
      L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) :=
  compileObject_correct hexternal hcomp hrun

/-- Every object's own code block is pointwise equivalent to its source block
(any round count). -/
theorem optimizerPipelineObjectRounds_topEquiv (n : Nat) (o : Object Op) :
    EquivBlock D o.codeBlock
      (optimizerPipelineObjectRounds (calls := calls) (creates := creates) n o).codeBlock := by
  rw [optimizerPipelineObjectRounds_codeBlock]
  exact (objectPipelineRounds (calls := calls) (creates := creates) n).sound o.codeBlock

/-- Every object's own code block is pointwise equivalent to its source block. -/
theorem optimizerPipelineObject_topEquiv (o : Object Op) :
    EquivBlock D o.codeBlock
      (optimizerPipelineObject (calls := calls) (creates := creates) o).codeBlock :=
  optimizerPipelineObjectRounds_topEquiv pipelineRounds o

/-- End-to-end correctness for the recursively optimized object tree (any
round count), relative to the original object's resolved execution under the
optimized layout. -/
theorem optimizerPipelineObjectRounds_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model) (n : Nat)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject
      (optimizerPipelineObjectRounds (calls := model.calls) (creates := model.creates) n o)
        = some L)
    {V : VEnv (evmWithExternal model.calls model.creates)}
    {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject o L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) := by
  have hb := resolveObjectPipelineRoundsBlock_equiv
    (calls := model.calls) (creates := model.creates) n L o.codeBlock
  have hrun' : RunResolvedObject
      (optimizerPipelineObjectRounds (calls := model.calls) (creates := model.creates) n o)
      L V yst out := by
    show Run (evmWithExternal model.calls model.creates)
      (resolveForLayoutStmts L
        (optimizerPipelineObjectRounds (calls := model.calls)
          (creates := model.creates) n o).codeBlock)
      L.initState V yst out
    rw [optimizerPipelineObjectRounds_codeBlock]
    exact hb.run_iff.mp hrun
  exact compileObject_correct hexternal hcomp hrun'

/-- End-to-end correctness for the recursively optimized object tree, relative
to the original object's resolved execution under the optimized layout. -/
theorem optimizerPipelineObject_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject
      (optimizerPipelineObject (calls := model.calls) (creates := model.creates) o)
        = some L)
    {V : VEnv (evmWithExternal model.calls model.creates)}
    {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject o L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) :=
  optimizerPipelineObjectRounds_correct hexternal pipelineRounds hcomp hrun

end YulEvmCompiler.Optimizer
