import YulEvmCompiler.Optimizer.Implementation.Normalization.FlattenBlocks
import YulEvmCompiler.Optimizer.Implementation.DeadLits
import YulEvmCompiler.Optimizer.Implementation.StackLayoutSound
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
open YulEvmCompiler.Optimizer.Flatten

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

/-! ## Bridge: flattening preserves funDef-freeness

So a funDef-free block stays funDef-free after flattening; combined with the
previous lemma, both a spliced block and its flattening have empty `hoist`. -/

theorem noFunDefStmts_append {a b : List (Stmt Op)}
    (ha : NoFunDefStmts a) (hb : NoFunDefStmts b) : NoFunDefStmts (a ++ b) := by
  induction a with
  | nil => simpa using hb
  | cons s rest ih => exact ⟨ha.1, ih ha.2⟩

mutual
theorem noFunDef_flattenStmt {s : Stmt Op} (h : NoFunDefStmt s) :
    NoFunDefStmts (flattenStmt s) := by
  cases s with
  | funDef n ps rs body => exact absurd h (by simp [NoFunDefStmt])
  | block body =>
      simpa [flattenStmt] using noFunDef_flattenStmts (by simpa [NoFunDefStmt] using h)
  | cond c body =>
      simp only [flattenStmt, NoFunDefStmts, NoFunDefStmt, and_true]
      exact noFunDef_flattenStmts (by simpa [NoFunDefStmt] using h)
  | «switch» c cs d =>
      simp only [flattenStmt, NoFunDefStmts, NoFunDefStmt, and_true]
      exact ⟨noFunDef_flattenCases (by simpa [NoFunDefStmt] using h.1),
             noFunDef_flattenDflt (by simpa [NoFunDefStmt] using h.2)⟩
  | forLoop i c p b =>
      simp only [flattenStmt, NoFunDefStmts, NoFunDefStmt, and_true]
      obtain ⟨hi, hp, hb⟩ := (by simpa [NoFunDefStmt] using h :
        NoFunDefStmts i ∧ NoFunDefStmts p ∧ NoFunDefStmts b)
      exact ⟨noFunDef_flattenStmts hi, noFunDef_flattenStmts hp, noFunDef_flattenStmts hb⟩
  | letDecl vars v => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
  | assign vars v => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
  | exprStmt e => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
  | «break» => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
  | «continue» => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
  | «leave» => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
theorem noFunDef_flattenStmts {ss : List (Stmt Op)} (h : NoFunDefStmts ss) :
    NoFunDefStmts (flattenStmts ss) := by
  cases ss with
  | nil => trivial
  | cons s rest =>
      simp only [flattenStmts]
      exact noFunDefStmts_append (noFunDef_flattenStmt h.1) (noFunDef_flattenStmts h.2)
theorem noFunDef_flattenCases {cs : List (Literal × List (Stmt Op))}
    (h : NoFunDefCases cs) : NoFunDefCases (flattenCases cs) := by
  cases cs with
  | nil => trivial
  | cons hd tl =>
      obtain ⟨l, b⟩ := hd
      exact ⟨noFunDef_flattenStmts h.1, noFunDef_flattenCases h.2⟩
theorem noFunDef_flattenDflt {d : Option (List (Stmt Op))}
    (h : NoFunDefDflt d) : NoFunDefDflt (flattenDflt d) := by
  cases d with
  | none => trivial
  | some b => simpa [flattenDflt, NoFunDefDflt] using noFunDef_flattenStmts h

end

/-- Both a funDef-free block and its flattening have an empty hoisted scope. -/
theorem hoist_flatten_eq_nil {ss : List (Stmt Op)} (h : NoFunDefStmts ss) :
    hoist D (flattenStmts ss) = [] :=
  hoist_eq_nil_of_noFunDef (noFunDef_flattenStmts h)

/-! ## Unwrapping a funDef-free block

Executing a bare `block body` whose `body` is funDef-free is exactly executing
`body`'s statements inline (its hoisted scope is empty, transparent by
`EmptyScopeRel`), with the block's exit `restore` made explicit. This is the
seam that flattening removes. -/

theorem block_unwrap {funs : FunEnv D} {V st V' st' o} {body : List (Stmt Op)}
    (hnf : NoFunDefStmts body) :
    Step D funs V st (.stmt (.block body)) (.sres V' st' o) ↔
      ∃ Vb, V' = restore V Vb ∧ Step D funs V st (.stmts body) (.sres Vb st' o) := by
  have hh : hoist D body = [] := hoist_eq_nil_of_noFunDef hnf
  constructor
  · intro h
    cases h with
    | block hbody =>
        rw [hh] at hbody
        exact ⟨_, rfl, Step.emptyScope_congr hbody (EmptyScopeRel.drop funs)⟩
  · rintro ⟨Vb, rfl, hbody⟩
    have hpush : Step D ([] :: funs) V st (.stmts body) (.sres Vb st' o) :=
      Step.emptyScope_congr hbody (EmptyScopeRel.add funs)
    rw [← hh] at hpush
    exact Step.block hpush

end YulEvmCompiler.Optimizer
