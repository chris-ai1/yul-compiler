import YulEvmCompiler.Optimizer.Implementation.Normalization.FlattenBlocks
import YulEvmCompiler.Optimizer.Implementation.DeadLits
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.Normalization.FlattenBlocksSound

Semantic soundness of the block-flattening transform (`FlattenBlocks.flattenBlock`):
under the normal-form preconditions it establishes an `EquivBlock`, so it composes
with the verified backend.

## Why this is a *conditional* soundness theorem (not a bare `LocalPass`)

Flattening is **not** unconditionally semantics-preserving, so it does not fit the
unconditional `Optimizer.LocalPass` obligation `∀ b, EquivBlock D b (run b)`.
Two failure modes on ill-formed input:

* **Variables.** `{ { let z := 1 } use(z) }` is ill-scoped in the original (the
  outer `use(z)` cannot see the inner `z`, so it is stuck), yet the flattened
  `{ let z := 1 use(z) }` runs. Preserving `↔` therefore needs `WellScoped`.
* **Functions.** A `funDef` nested inside a block would, after flattening, move
  into the enclosing block's hoisted scope (`hoist`), a genuine scope
  restructuring. Requiring `FunctionsHoisted` rules this out: every block that
  gets spliced is then funDef-free, so its `hoist` is empty and the only
  function-environment change is the insertion/removal of **empty** scopes —
  handled by the existing `EmptyScopeRel` / `Step.emptyScope_congr`.

The leaked-variable reasoning (an inner block's locals surviving into the rest of
the enclosing block) is discharged by `UniqueNames`: the trailing statements
never mention those names, so `Frame.frameAdd`/`frameRemove` transport the
derivation, and `restore_insAt_le` aligns the block-exit `restore`.

So the target is:

```
flattenBlock_sound :
  WellScoped b → UniqueNames b → FunctionsHoisted b → EquivBlock D b (flattenBlock b)
```

which is exactly the "requires and re-establishes normal-form fields" discipline
(`NormalForm`): a pipeline runs disambiguation + function hoisting first, and
flattening consumes those guarantees.

This file is built bottom-up; see the section markers for the proof layers.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer.NormalForm

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ## Bridge: a funDef-free block has an empty hoisted scope

`FunctionsHoisted` guarantees that every block reached by flattening (nested
inside conditionals, loops, switch cases, or a bare block) contains no function
definitions. For such a block `hoist D body = []`, so removing its wrapper only
deletes an *empty* function scope — the case `EmptyScopeRel` covers. -/

theorem hoist_eq_nil_of_noFunDef {ss : List (Stmt Op)}
    (h : NoFunDefStmts ss) : hoist D ss = [] := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
      have hrest := ih h.2
      have h1 := h.1
      cases s <;> simp_all [hoist, NoFunDefStmt]

end YulEvmCompiler.Optimizer
