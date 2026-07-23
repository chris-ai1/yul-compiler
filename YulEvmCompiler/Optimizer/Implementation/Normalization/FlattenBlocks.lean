import YulEvmCompiler.Optimizer.Implementation.Normalization.NormalForm
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.Normalization.FlattenBlocks

The **block-flattening** normalization: splice every bare `block` statement's
statements directly into its enclosing statement list, removing the wrapper. The
grammar-required blocks (function/loop/conditional bodies, switch-case bodies,
`for` init/post) are `List (Stmt Op)` payloads, not `block` statements, so they
stay — but the pass recurses into them to flatten any `block` statements nested
inside.

The transform (`flattenStmts` / `flattenBlock`) is dialect-generic over `{Op}`.
This module establishes the two **syntactic** guarantees:

* `flattenBlock_flattened`  — the result satisfies `NormalForm.Flattened`
  (the postcondition this pass exists to establish);
* `flattenBlock_uniqueNames` — the result preserves `NormalForm.UniqueNames`
  (flattening only relocates declarations; it neither adds, drops, nor renames a
  declared name, so the declared-name list is preserved verbatim).

## Soundness (semantic) is deliberately not here yet

Packaging this as a verified `Optimizer.LocalPass` additionally requires the
`Sound` obligation `∀ b, EquivBlock D b (flattenBlock b)`. That proof is the
substantial part: relative to the source big-step semantics, splicing a block
changes two things — nested `funDef`s move into the enclosing block's hoisted
scope (`YulSemantics.hoist`), and the inner block's variable `restore` is
dropped, so inner locals leak into the rest of the enclosing block. Both are
harmless **only under global name uniqueness** (`NormalForm.UniqueNames`): leaked
locals are never referenced later, and hoisted function names never collide. The
`LocalPass` packaging lands in a follow-up once that `EquivBlock` proof is
discharged; it will take `UniqueNames` as its stated precondition.
-/

namespace YulEvmCompiler.Optimizer.Flatten

open YulSemantics
open YulEvmCompiler.Optimizer.NormalForm

variable {Op : Type}

/-! ## The transform -/

mutual
/-- Flatten a single statement into a list: a bare `block` splices its (flattened)
statements in place; every other statement is kept with its grammar-required
sub-blocks flattened. -/
def flattenStmt : Stmt Op → List (Stmt Op)
  | .block body => flattenStmts body
  | .funDef n ps rs body => [.funDef n ps rs (flattenStmts body)]
  | .cond c body => [.cond c (flattenStmts body)]
  | .switch c cases dflt => [.switch c (flattenCases cases) (flattenDflt dflt)]
  | .forLoop init c post body =>
      [.forLoop (flattenStmts init) c (flattenStmts post) (flattenStmts body)]
  | s => [s]
def flattenStmts : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => flattenStmt s ++ flattenStmts rest
def flattenCases : List (Literal × List (Stmt Op)) → List (Literal × List (Stmt Op))
  | [] => []
  | (l, b) :: cs => (l, flattenStmts b) :: flattenCases cs
def flattenDflt : Option (List (Stmt Op)) → Option (List (Stmt Op))
  | none => none
  | some b => some (flattenStmts b)
end

/-- Flatten every bare `block` in a top-level block. -/
def flattenBlock (b : Block Op) : Block Op := flattenStmts b

/-! ## Postcondition: the result is flattened -/

/-- `Flattened` distributes over statement-list append. -/
theorem flattenedStmts_append : ∀ {a b : List (Stmt Op)},
    FlattenedStmts a → FlattenedStmts b → FlattenedStmts (a ++ b)
  | [], _, _, hb => hb
  | _ :: _, _, ha, hb => ⟨ha.1, flattenedStmts_append ha.2 hb⟩

mutual
theorem flattenStmt_flattened (s : Stmt Op) : FlattenedStmts (flattenStmt s) := by
  cases s with
  | block body => simpa [flattenStmt] using flattenStmts_flattened body
  | funDef n ps rs body =>
      simp only [flattenStmt, FlattenedStmts, FlattenedStmt, and_true]
      exact flattenStmts_flattened body
  | cond c body =>
      simp only [flattenStmt, FlattenedStmts, FlattenedStmt, and_true]
      exact flattenStmts_flattened body
  | switch c cases dflt =>
      simp only [flattenStmt, FlattenedStmts, FlattenedStmt, and_true]
      exact ⟨flattenCases_flattened cases, flattenDflt_flattened dflt⟩
  | forLoop init c post body =>
      simp only [flattenStmt, FlattenedStmts, FlattenedStmt, and_true]
      exact ⟨flattenStmts_flattened init, flattenStmts_flattened post,
             flattenStmts_flattened body⟩
  | letDecl vars v => simp [flattenStmt, FlattenedStmts, FlattenedStmt]
  | assign vars v => simp [flattenStmt, FlattenedStmts, FlattenedStmt]
  | exprStmt e => simp [flattenStmt, FlattenedStmts, FlattenedStmt]
  | «break» => simp [flattenStmt, FlattenedStmts, FlattenedStmt]
  | «continue» => simp [flattenStmt, FlattenedStmts, FlattenedStmt]
  | leave => simp [flattenStmt, FlattenedStmts, FlattenedStmt]
theorem flattenStmts_flattened (ss : List (Stmt Op)) : FlattenedStmts (flattenStmts ss) := by
  cases ss with
  | nil => trivial
  | cons s rest =>
      simp only [flattenStmts]
      exact flattenedStmts_append (flattenStmt_flattened s) (flattenStmts_flattened rest)
theorem flattenCases_flattened (cs : List (Literal × List (Stmt Op))) :
    FlattenedCases (flattenCases cs) := by
  cases cs with
  | nil => trivial
  | cons hd tl =>
      obtain ⟨l, b⟩ := hd
      simp only [flattenCases, FlattenedCases]
      exact ⟨flattenStmts_flattened b, flattenCases_flattened tl⟩
theorem flattenDflt_flattened (d : Option (List (Stmt Op))) :
    FlattenedDflt (flattenDflt d) := by
  cases d with
  | none => trivial
  | some b => simpa [flattenDflt, FlattenedDflt] using flattenStmts_flattened b
end

/-- **Postcondition.** Flattening produces a program in flattened normal form. -/
theorem flattenBlock_flattened (b : Block Op) : Flattened (flattenBlock b) :=
  flattenStmts_flattened b

/-! ## Preservation: the declared-name list is unchanged -/

theorem declaredNamesStmts_append : ∀ (a b : List (Stmt Op)),
    declaredNamesStmts (a ++ b) = declaredNamesStmts a ++ declaredNamesStmts b
  | [], b => by simp [declaredNamesStmts]
  | s :: rest, b => by
      simp [declaredNamesStmts, declaredNamesStmts_append rest b, List.append_assoc]

mutual
theorem declaredNames_flattenStmt (s : Stmt Op) :
    declaredNamesStmts (flattenStmt s) = declaredNamesStmt s := by
  cases s with
  | block body => simpa [flattenStmt, declaredNamesStmt] using declaredNames_flattenStmts body
  | funDef n ps rs body =>
      simp [flattenStmt, declaredNamesStmts, declaredNamesStmt, declaredNames_flattenStmts body]
  | cond c body =>
      simp [flattenStmt, declaredNamesStmts, declaredNamesStmt, declaredNames_flattenStmts body]
  | switch c cases dflt =>
      simp [flattenStmt, declaredNamesStmts, declaredNamesStmt,
            declaredNames_flattenCases cases, declaredNames_flattenDflt dflt]
  | forLoop init c post body =>
      simp [flattenStmt, declaredNamesStmts, declaredNamesStmt,
            declaredNames_flattenStmts init, declaredNames_flattenStmts post,
            declaredNames_flattenStmts body]
  | letDecl vars v => simp [flattenStmt, declaredNamesStmts, declaredNamesStmt]
  | assign vars v => simp [flattenStmt, declaredNamesStmts, declaredNamesStmt]
  | exprStmt e => simp [flattenStmt, declaredNamesStmts, declaredNamesStmt]
  | «break» => simp [flattenStmt, declaredNamesStmts, declaredNamesStmt]
  | «continue» => simp [flattenStmt, declaredNamesStmts, declaredNamesStmt]
  | leave => simp [flattenStmt, declaredNamesStmts, declaredNamesStmt]
theorem declaredNames_flattenStmts (ss : List (Stmt Op)) :
    declaredNamesStmts (flattenStmts ss) = declaredNamesStmts ss := by
  cases ss with
  | nil => rfl
  | cons s rest =>
      simp only [flattenStmts, declaredNamesStmts_append, declaredNames_flattenStmt s,
                 declaredNames_flattenStmts rest, declaredNamesStmts]
theorem declaredNames_flattenCases (cs : List (Literal × List (Stmt Op))) :
    declaredNamesCases (flattenCases cs) = declaredNamesCases cs := by
  cases cs with
  | nil => rfl
  | cons hd tl =>
      obtain ⟨l, b⟩ := hd
      simp [flattenCases, declaredNamesCases, declaredNames_flattenStmts b,
            declaredNames_flattenCases tl]
theorem declaredNames_flattenDflt (d : Option (List (Stmt Op))) :
    declaredNamesDflt (flattenDflt d) = declaredNamesDflt d := by
  cases d with
  | none => rfl
  | some b => simpa [flattenDflt, declaredNamesDflt] using declaredNames_flattenStmts b
end

/-- **Precondition preserved.** Flattening keeps global name uniqueness (it only
relocates declarations; the declared-name list is unchanged). -/
theorem flattenBlock_uniqueNames (b : Block Op) (h : UniqueNames b) :
    UniqueNames (flattenBlock b) := by
  have : declaredNamesStmts (flattenBlock b) = declaredNamesStmts b :=
    declaredNames_flattenStmts b
  unfold UniqueNames
  rw [this]
  exact h

end YulEvmCompiler.Optimizer.Flatten
