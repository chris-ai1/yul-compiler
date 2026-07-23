import YulEvmCompiler.Optimizer.Implementation.Normalization.SourceCheck
import YulEvmCompiler.Optimizer.Implementation.Normalization.HoistFunDefsPass
import YulEvmCompiler.Optimizer.Implementation.Normalization.FlattenBlocksSound
/-!
# The normalization passes, as verified `GlobalPass`es

Wires the proven normalization passes into unconditionally-sound whole-program
passes via the `GlobalPass.ofGuardedBlock` combinator (apply when the decidable
guard implying the pass's soundness preconditions holds, else identity), and
composes them in dependency order:

1. **`disambiguatePass`** — rename every declared variable and function to a
   globally fresh name (`disambiguate`; soundness `disambiguate_runEquivBlock`,
   guarded by the source-validity checks of `SourceCheck`);
2. **`Normalization.hoistFunDefsPass`** — hoist all function definitions to the
   root block (upstream, already guarded);
3. **`flattenBlocksPass`** — splice bare blocks into their parents
   (`Flatten.flattenBlock`; soundness `flattenBlock_sound`, which needs the
   hoisted/disambiguated normal form the earlier passes establish — its guard
   re-checks them, so the composition stays unconditionally sound).

`hoistForInit` (the `for`-init rewriter) is an unconditional `LocalPass` and is
wired separately at the head of every optimizer round in `Pipeline.lean`.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {Op : Type}

/-! ### The disambiguation pass -/

/-- Decidable source validity: everything `disambiguate_runEquivBlock` needs.
Valid Yul (as produced by the parser/`solc`) passes all of these. -/
def disambiguateGuard (b : Block Op) : Bool :=
  chkSVStmts b && decide (funNames b).Nodup && chkWFStmts b &&
  chkScopedStmts [] (NormalForm.funDefNames b) b &&
  chkWScopedStmts [] b && chkFScopedStmts (funNames b) b

theorem disambiguateGuard_sound {b : Block Op} (h : disambiguateGuard b = true) :
    SVStmts b ∧ WellFormed b ∧ NormalForm.WellScoped b ∧
      WScopedStmts ([] : List Ident) b ∧ FScopedStmts (funNames b) b := by
  simp only [disambiguateGuard, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨chkSVStmts_sound h.1.1.1.1.1, ⟨h.1.1.1.1.2, chkWFStmts_sound h.1.1.1.2⟩,
    chkScopedStmts_sound h.1.1.2, chkWScopedStmts_sound h.1.2, chkFScopedStmts_sound h.2⟩

/-- Disambiguation is *needed* only when some name is declared twice — `solc`'s
IR is already disambiguated, and renaming an already-unique program to opaque
fresh names only hurts downstream heuristics. -/
def disambiguateNeeded (b : Block Op) : Bool :=
  !(decide (NormalForm.declaredNamesStmts b).Nodup)

/-- The pass fires only on valid programs that actually need it. -/
def disambiguateFullGuard (b : Block Op) : Bool :=
  disambiguateNeeded b && disambiguateGuard b

/-- **Disambiguation as a verified global pass**: rename every declared name to
a globally fresh one wherever names are not yet unique and the source-validity
check passes; sound unconditionally by `disambiguate_runEquivBlock` behind the
guard. -/
def disambiguatePass {D : Dialect} [DecidableEq D.Value] : Optimizer.GlobalPass D :=
  Optimizer.GlobalPass.ofGuardedBlock disambiguateFullGuard disambiguate (fun b hg => by
    obtain ⟨hsv, hwf, hns, hws, hfs⟩ :=
      disambiguateGuard_sound (Bool.and_eq_true .. ▸ hg).2
    exact disambiguate_runEquivBlock b hsv hwf hns hws hfs)

/-! ### The block flattener -/

/-- Decidable guard for the flattener's normal-form preconditions (established
by the passes before it; re-checked so the pass is standalone-sound). -/
def flattenGuard (b : Block Op) : Bool :=
  chkFunctionsHoisted b && chkScopedStmts [] (NormalForm.funDefNames b) b &&
  decide (NormalForm.declaredNamesStmts b).Nodup && chkForInitEmptyStmts b

theorem flattenGuard_sound {b : Block Op} (h : flattenGuard b = true) :
    NormalForm.FunctionsHoisted b ∧ NormalForm.WellScoped b ∧
      NormalForm.UniqueNames b ∧ NormalForm.ForInitEmpty b := by
  simp only [flattenGuard, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨chkFunctionsHoisted_sound h.1.1.1, chkScopedStmts_sound h.1.1.2, h.1.2,
    chkForInitEmptyStmts_sound h.2⟩

variable {calls : YulSemantics.EVM.ExternalCalls} {creates : YulSemantics.EVM.ExternalCreates}

open YulSemantics.EVM in
/-- **Block flattening as a verified global pass** (guarded by the normal-form
preconditions its soundness theorem needs). -/
def flattenBlocksPass : Optimizer.GlobalPass (evmWithExternal calls creates) :=
  Optimizer.GlobalPass.ofGuardedBlock flattenGuard Flatten.flattenBlock (fun b hg => by
    obtain ⟨hFH, hsc, huniq, hFIE⟩ := flattenGuard_sound hg
    exact Optimizer.RunEquivBlock.of_equivBlock
      (Optimizer.flattenBlock_sound b hFH hsc huniq hFIE))

/-! ### The composed normalization prefix -/

open YulSemantics.EVM in
/-- **All whole-program normalization passes, in dependency order**:
disambiguate, then hoist function definitions, then flatten blocks
(`GlobalPass.ofList` runs the head first). Each pass is individually guarded,
so the composition is unconditionally sound. -/
def normalizationPasses : Optimizer.GlobalPass (evmWithExternal calls creates) :=
  Optimizer.GlobalPass.ofList
    [disambiguatePass]  -- ISOLATION TEST

/-! ### Block-level normalization (for the bare-block compile path)

The same three passes as per-block transforms, for a top-level bare block (a
whole program in itself, so `Run`-equivalence is the right notion there too). -/

/-- Disambiguation as a guarded block transform (fires only when needed). -/
def disambiguateBlock {D : Dialect} [DecidableEq D.Value] : Block D.Op → Block D.Op :=
  Optimizer.guardedBlock disambiguateFullGuard disambiguate

theorem disambiguateBlock_runEquiv {D : Dialect} [DecidableEq D.Value] (b : Block D.Op) :
    Optimizer.RunEquivBlock D b (disambiguateBlock b) := by
  unfold disambiguateBlock Optimizer.guardedBlock
  by_cases hg : disambiguateFullGuard b = true
  · rw [if_pos hg]
    obtain ⟨hsv, hwf, hns, hws, hfs⟩ :=
      disambiguateGuard_sound (Bool.and_eq_true .. ▸ hg).2
    exact disambiguate_runEquivBlock b hsv hwf hns hws hfs
  · rw [if_neg hg]
    exact Optimizer.RunEquivBlock.refl b

open YulSemantics.EVM in
/-- The function hoister's guarded block transform preserves whole-program
behaviour (the per-block content of `hoistFunDefsPass`). -/
theorem hoistBlock_runEquiv {D : Dialect} [DecidableEq D.Value] (b : Block D.Op) :
    Optimizer.RunEquivBlock D b (Optimizer.Normalization.hoistBlock b) := by
  unfold Optimizer.Normalization.hoistBlock Optimizer.guardedBlock
  by_cases hg : Optimizer.Normalization.hoistGuard b = true
  · rw [if_pos hg]
    exact fun st0 V' st' o => Optimizer.Normalization.liftFunDefs_run_equiv
      (Optimizer.Normalization.hoistGuard_sound hg).1
      (Optimizer.Normalization.hoistGuard_sound hg).2
  · rw [if_neg hg]
    exact Optimizer.RunEquivBlock.refl b

open YulSemantics.EVM in
/-- Block flattening as a guarded block transform. -/
def flattenBlockChecked : Block (evmWithExternal calls creates).Op →
    Block (evmWithExternal calls creates).Op :=
  Optimizer.guardedBlock flattenGuard Flatten.flattenBlock

open YulSemantics.EVM in
theorem flattenBlockChecked_runEquiv (b : Block (evmWithExternal calls creates).Op) :
    Optimizer.RunEquivBlock (evmWithExternal calls creates) b
      (flattenBlockChecked (calls := calls) (creates := creates) b) := by
  unfold flattenBlockChecked Optimizer.guardedBlock
  by_cases hg : flattenGuard b = true
  · rw [if_pos hg]
    obtain ⟨hFH, hsc, huniq, hFIE⟩ := flattenGuard_sound hg
    exact Optimizer.RunEquivBlock.of_equivBlock
      (Optimizer.flattenBlock_sound b hFH hsc huniq hFIE)
  · rw [if_neg hg]
    exact Optimizer.RunEquivBlock.refl b

open YulSemantics.EVM in
/-- **Whole-program block normalization**: disambiguate, hoist function
definitions, flatten blocks — the per-block form of `normalizationPasses`,
for the bare-block compile path. -/
def normalizeBlock (b : Block (evmWithExternal calls creates).Op) :
    Block (evmWithExternal calls creates).Op :=
  disambiguateBlock b  -- ISOLATION TEST

open YulSemantics.EVM in
/-- The block normalizer preserves whole-program behaviour. -/
theorem normalizeBlock_runEquiv (b : Block (evmWithExternal calls creates).Op) :
    Optimizer.RunEquivBlock (evmWithExternal calls creates) b
      (normalizeBlock (calls := calls) (creates := creates) b) :=
  disambiguateBlock_runEquiv b  -- ISOLATION TEST

end YulEvmCompiler.Optimizer.Normalize
