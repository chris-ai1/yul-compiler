import YulEvmCompiler.Optimizer.Spec.PrePostPass
import YulEvmCompiler.Optimizer.Implementation.Normalization.NormalForm
import Mathlib.Data.List.Perm.Subperm

set_option warningAsError true

/-!
# YulEvmCompiler.Optimizer.Spec.DeclPreserving

**Declaration-non-generative passes preserve name-uniqueness normal forms for
free** — no per-pass structural induction.

## The idea

`NormalForm.UniqueNames b` is `(declaredNamesStmts b).Nodup`, and `Nodup` is
*downward closed under sub-multiset*: if `l₁ <+~ l₂` and `l₂` is `Nodup`, so is
`l₁`. So **any** transform whose output declares only names that were already
declared in the input — its declared-name multiset is a sub-multiset of the
input's — preserves `UniqueNames` automatically. We call such a transform
**declaration-non-generative** (`PreservesDecls`).

That single fact is the reusable kernel: a pass proves at most that it does not
*invent* declared names, and preservation follows. This replaces the bespoke
`declaredNamesStmts (run b) <+ declaredNamesStmts b` ⇒ `Nodup` inductions that
each pass would otherwise carry (`SimplifyUniqueNames`, `DeadCodeUniqueNames`).

## Proven-once traversal skeletons

Better still, most passes need not even prove the sub-multiset fact themselves:
they are instances of a **generic non-generative traversal** whose declared-name
bound is proved here once and inherited by every instance.

* `mapExprsBlock fe` — rewrite every expression operand by `fe`, leaving all
  binders and block structure intact. Declared names are *unchanged*
  (`declaredNamesStmts_mapExprs`). This is the shape of constant folding,
  algebraic/peephole simplification, strength reduction, copy/constant
  propagation's substitution core — the whole pure-expression-rewriting family.

* `filterStmtsDeep keep` — recurse through the tree keeping only statements
  satisfying `keep` (and, within kept statements, their filtered sub-blocks).
  Declared names can only shrink (`declaredNamesStmts_filterStmts_sublist`).
  This is the shape of dead- and unreachable-code elimination.

`PreservesDecls` is closed under `id`/`comp`/`ofList`, so a whole *segment* of
non-generative passes preserves `UniqueNames` from the segment-level fact.

## Scope (what does *not* fit)

Passes that **mint fresh** declarations (`hoistCalls`, `freshenCalls`; future
CSE, LICM) preserve uniqueness by *freshness*, not by non-increase — a separate
kernel. Passes that **duplicate** existing declarations (`inlineCalls` inserting
a callee body unchanged) do not preserve `UniqueNames` at all and must
re-establish it. See the `Optimizer` AGENTS notes.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open scoped List

/-! ## The kernel: sub-multiset of declared names ⇒ `Nodup` preserved -/

/-- `Nodup` is downward closed under `Subperm` (sub-multiset): a sub-multiset of a
duplicate-free list is duplicate-free. -/
theorem nodup_of_subperm {α} {l₁ l₂ : List α} (h : l₁ <+~ l₂) (hn : l₂.Nodup) : l₁.Nodup := by
  obtain ⟨l, hp, hs⟩ := h
  exact hp.nodup_iff.mp (hs.nodup hn)

variable {D : Dialect}

/-- A block transform is **declaration-non-generative** when it never introduces a
declared name: the output's declared-name multiset is a sub-multiset (`Subperm`) of
the input's. This is the single hypothesis from which `UniqueNames` preservation —
and preservation of any invariant downward-closed under `Subperm` of declared names
— follows with no further per-pass work. -/
def PreservesDecls (run : Block D.Op → Block D.Op) : Prop :=
  ∀ b, (NormalForm.declaredNamesStmts (run b)).Subperm (NormalForm.declaredNamesStmts b)

/-- A transform whose declared names are always a **sublist** (the common
delete/select case) is declaration-non-generative. -/
theorem PreservesDecls.of_sublist {run : Block D.Op → Block D.Op}
    (h : ∀ b, (NormalForm.declaredNamesStmts (run b)).Sublist
                (NormalForm.declaredNamesStmts b)) : PreservesDecls run :=
  fun b => (h b).subperm

/-- A transform that leaves the declared-name list **unchanged** is
declaration-non-generative. -/
theorem PreservesDecls.of_eq {run : Block D.Op → Block D.Op}
    (h : ∀ b, NormalForm.declaredNamesStmts (run b) = NormalForm.declaredNamesStmts b) :
    PreservesDecls run :=
  PreservesDecls.of_sublist (fun b => (h b) ▸ List.Sublist.refl _)

/-- **The kernel.** A declaration-non-generative transform preserves
`NormalForm.UniqueNames` — no per-pass induction. -/
theorem Preserves.uniqueNames_of_preservesDecls {run : Block D.Op → Block D.Op}
    (h : PreservesDecls run) : Preserves NormalForm.UniqueNames run :=
  fun b hb => nodup_of_subperm (h b) hb

/-- The kernel, generalized to **any** invariant `I` that is antitone under a
sub-multiset of declared names (`UniqueNames` is the canonical instance; "no
shadowing", "declared names ⊆ a fixed set", … are others). -/
theorem Preserves.of_preservesDecls {I : Block D.Op → Prop}
    (hmono : ∀ {b b' : Block D.Op},
      (NormalForm.declaredNamesStmts b').Subperm (NormalForm.declaredNamesStmts b) → I b → I b')
    {run : Block D.Op → Block D.Op} (h : PreservesDecls run) : Preserves I run :=
  fun b hb => hmono (h b) hb

/-! ## `PreservesDecls` is compositional -/

/-- The identity is declaration-non-generative. -/
theorem PreservesDecls.id : PreservesDecls (D := D) _root_.id :=
  fun _ => List.Subperm.refl _

/-- Composition of non-generative transforms is non-generative (`Subperm`
transitivity). Matches `LocalPass.comp` (`run₁ ∘ run₂` runs `run₂` first). -/
theorem PreservesDecls.comp {run₁ run₂ : Block D.Op → Block D.Op}
    (h₁ : PreservesDecls run₁) (h₂ : PreservesDecls run₂) : PreservesDecls (run₁ ∘ run₂) :=
  fun b => (h₁ (run₂ b)).trans (h₂ b)

/-- A whole pipeline is non-generative when each stage is (folded as
`LocalPass.ofList` folds passes). -/
theorem PreservesDecls.ofList {rs : List (Block D.Op → Block D.Op)}
    (h : ∀ r ∈ rs, PreservesDecls r) :
    PreservesDecls (rs.foldr (fun r acc => acc ∘ r) _root_.id) := by
  induction rs with
  | nil => exact PreservesDecls.id
  | cons r rs ih =>
      exact (ih fun r' hr' => h r' (List.mem_cons.2 (Or.inr hr'))).comp
        (h r (List.mem_cons.2 (Or.inl rfl)))

/-! ## Skeleton 1 — `mapExprsBlock`: rewrite expressions, keep every binder -/

mutual
/-- Rewrite the expression operands of a statement by `fe`, recursing into
sub-blocks; binder lists and block structure are untouched. -/
def mapExprsStmt (fe : Expr D.Op → Expr D.Op) : Stmt D.Op → Stmt D.Op
  | .letDecl vs (some e) => .letDecl vs (some (fe e))
  | .letDecl vs none => .letDecl vs none
  | .assign vs e => .assign vs (fe e)
  | .exprStmt e => .exprStmt (fe e)
  | .cond c body => .cond (fe c) (mapExprsStmts fe body)
  | .switch c cases dflt => .switch (fe c) (mapExprsCases fe cases) (mapExprsDflt fe dflt)
  | .forLoop init c post body =>
      .forLoop (mapExprsStmts fe init) (fe c) (mapExprsStmts fe post) (mapExprsStmts fe body)
  | .funDef n ps rs body => .funDef n ps rs (mapExprsStmts fe body)
  | .block b => .block (mapExprsStmts fe b)
  | .«break» => .«break»
  | .«continue» => .«continue»
  | .leave => .leave
def mapExprsStmts (fe : Expr D.Op → Expr D.Op) : List (Stmt D.Op) → List (Stmt D.Op)
  | [] => []
  | s :: rest => mapExprsStmt fe s :: mapExprsStmts fe rest
def mapExprsCases (fe : Expr D.Op → Expr D.Op) :
    List (Literal × Block D.Op) → List (Literal × Block D.Op)
  | [] => []
  | (l, b) :: rest => (l, mapExprsStmts fe b) :: mapExprsCases fe rest
def mapExprsDflt (fe : Expr D.Op → Expr D.Op) : Option (Block D.Op) → Option (Block D.Op)
  | none => none
  | some b => some (mapExprsStmts fe b)
end

/-- A pure expression-rewriting pass over a block. -/
def mapExprsBlock (fe : Expr D.Op → Expr D.Op) : Block D.Op → Block D.Op := mapExprsStmts fe

mutual
theorem declaredNamesStmt_mapExprs (fe : Expr D.Op → Expr D.Op) : ∀ s : Stmt D.Op,
    NormalForm.declaredNamesStmt (mapExprsStmt fe s) = NormalForm.declaredNamesStmt s
  | .letDecl _ (some _) => rfl
  | .letDecl _ none => rfl
  | .assign _ _ => rfl
  | .exprStmt _ => rfl
  | .«break» => rfl
  | .«continue» => rfl
  | .leave => rfl
  | .cond _ body => by
      simp only [mapExprsStmt, NormalForm.declaredNamesStmt, declaredNamesStmts_mapExprs fe body]
  | .block b => by
      simp only [mapExprsStmt, NormalForm.declaredNamesStmt, declaredNamesStmts_mapExprs fe b]
  | .funDef n ps rs body => by
      simp only [mapExprsStmt, NormalForm.declaredNamesStmt, declaredNamesStmts_mapExprs fe body]
  | .switch _ cases dflt => by
      simp only [mapExprsStmt, NormalForm.declaredNamesStmt, declaredNamesCases_mapExprs fe cases,
        declaredNamesDflt_mapExprs fe dflt]
  | .forLoop init _ post body => by
      simp only [mapExprsStmt, NormalForm.declaredNamesStmt, declaredNamesStmts_mapExprs fe init,
        declaredNamesStmts_mapExprs fe post, declaredNamesStmts_mapExprs fe body]
theorem declaredNamesStmts_mapExprs (fe : Expr D.Op → Expr D.Op) : ∀ b : List (Stmt D.Op),
    NormalForm.declaredNamesStmts (mapExprsStmts fe b) = NormalForm.declaredNamesStmts b
  | [] => rfl
  | s :: rest => by
      simp only [mapExprsStmts, NormalForm.declaredNamesStmts, declaredNamesStmt_mapExprs fe s,
        declaredNamesStmts_mapExprs fe rest]
theorem declaredNamesCases_mapExprs (fe : Expr D.Op → Expr D.Op) :
    ∀ cs : List (Literal × Block D.Op),
    NormalForm.declaredNamesCases (mapExprsCases fe cs) = NormalForm.declaredNamesCases cs
  | [] => rfl
  | (_, b) :: rest => by
      simp only [mapExprsCases, NormalForm.declaredNamesCases, declaredNamesStmts_mapExprs fe b,
        declaredNamesCases_mapExprs fe rest]
theorem declaredNamesDflt_mapExprs (fe : Expr D.Op → Expr D.Op) : ∀ d : Option (Block D.Op),
    NormalForm.declaredNamesDflt (mapExprsDflt fe d) = NormalForm.declaredNamesDflt d
  | none => rfl
  | some b => by
      simp only [mapExprsDflt, NormalForm.declaredNamesDflt, declaredNamesStmts_mapExprs fe b]
end

/-- **`mapExprsBlock` is declaration-non-generative** (declared names unchanged),
proved once for all expression-rewriting passes. -/
theorem preservesDecls_mapExprsBlock (fe : Expr D.Op → Expr D.Op) :
    PreservesDecls (mapExprsBlock fe) :=
  PreservesDecls.of_eq (fun b => declaredNamesStmts_mapExprs fe b)

/-- Any expression-rewriting pass preserves `UniqueNames`, with no induction. -/
theorem preserves_uniqueNames_mapExprsBlock (fe : Expr D.Op → Expr D.Op) :
    Preserves NormalForm.UniqueNames (mapExprsBlock fe) :=
  Preserves.uniqueNames_of_preservesDecls (preservesDecls_mapExprsBlock fe)

/-! ## Skeleton 2 — `filterStmtsDeep`: keep a statement subset, recurse -/

mutual
/-- Recurse into a kept statement's sub-blocks, filtering each. -/
def filterStmt (keep : Stmt D.Op → Bool) : Stmt D.Op → Stmt D.Op
  | .cond c body => .cond c (filterStmts keep body)
  | .block b => .block (filterStmts keep b)
  | .funDef n ps rs body => .funDef n ps rs (filterStmts keep body)
  | .switch c cases dflt => .switch c (filterCases keep cases) (filterDflt keep dflt)
  | .forLoop init c post body =>
      .forLoop (filterStmts keep init) c (filterStmts keep post) (filterStmts keep body)
  | s => s
/-- Drop statements failing `keep`; recurse into those kept. -/
def filterStmts (keep : Stmt D.Op → Bool) : List (Stmt D.Op) → List (Stmt D.Op)
  | [] => []
  | s :: rest =>
      if keep s then filterStmt keep s :: filterStmts keep rest else filterStmts keep rest
def filterCases (keep : Stmt D.Op → Bool) :
    List (Literal × Block D.Op) → List (Literal × Block D.Op)
  | [] => []
  | (l, b) :: rest => (l, filterStmts keep b) :: filterCases keep rest
def filterDflt (keep : Stmt D.Op → Bool) : Option (Block D.Op) → Option (Block D.Op)
  | none => none
  | some b => some (filterStmts keep b)
end

/-- Deep statement filter over a block. -/
def filterStmtsDeep (keep : Stmt D.Op → Bool) : Block D.Op → Block D.Op := filterStmts keep

mutual
theorem declaredNamesStmt_filterStmt_sublist (keep : Stmt D.Op → Bool) : ∀ s : Stmt D.Op,
    (NormalForm.declaredNamesStmt (filterStmt keep s)).Sublist (NormalForm.declaredNamesStmt s)
  | .cond _ body => by
      simp only [filterStmt, NormalForm.declaredNamesStmt]
      exact declaredNamesStmts_filterStmts_sublist keep body
  | .block b => by
      simp only [filterStmt, NormalForm.declaredNamesStmt]
      exact declaredNamesStmts_filterStmts_sublist keep b
  | .funDef n ps rs body => by
      simp only [filterStmt, NormalForm.declaredNamesStmt]
      exact ((declaredNamesStmts_filterStmts_sublist keep body).append_left (ps ++ rs)).cons_cons n
  | .switch _ cases dflt => by
      simp only [filterStmt, NormalForm.declaredNamesStmt]
      exact (declaredNamesCases_filterCases_sublist keep cases).append
        (declaredNamesDflt_filterDflt_sublist keep dflt)
  | .forLoop init _ post body => by
      simp only [filterStmt, NormalForm.declaredNamesStmt]
      exact ((declaredNamesStmts_filterStmts_sublist keep init).append
        (declaredNamesStmts_filterStmts_sublist keep post)).append
        (declaredNamesStmts_filterStmts_sublist keep body)
  | .letDecl _ _ => List.Sublist.refl _
  | .assign _ _ => List.Sublist.refl _
  | .exprStmt _ => List.Sublist.refl _
  | .«break» => List.Sublist.refl _
  | .«continue» => List.Sublist.refl _
  | .leave => List.Sublist.refl _
theorem declaredNamesStmts_filterStmts_sublist (keep : Stmt D.Op → Bool) : ∀ b : List (Stmt D.Op),
    (NormalForm.declaredNamesStmts (filterStmts keep b)).Sublist (NormalForm.declaredNamesStmts b)
  | [] => List.Sublist.refl _
  | s :: rest => by
      simp only [filterStmts]
      by_cases h : keep s
      · rw [if_pos h]
        simp only [NormalForm.declaredNamesStmts]
        exact (declaredNamesStmt_filterStmt_sublist keep s).append
          (declaredNamesStmts_filterStmts_sublist keep rest)
      · rw [if_neg h]
        simp only [NormalForm.declaredNamesStmts]
        exact (declaredNamesStmts_filterStmts_sublist keep rest).trans
          (List.sublist_append_right _ _)
theorem declaredNamesCases_filterCases_sublist (keep : Stmt D.Op → Bool) :
    ∀ cs : List (Literal × Block D.Op),
    (NormalForm.declaredNamesCases (filterCases keep cs)).Sublist
      (NormalForm.declaredNamesCases cs)
  | [] => List.Sublist.refl _
  | (_, b) :: rest => by
      simp only [filterCases, NormalForm.declaredNamesCases]
      exact (declaredNamesStmts_filterStmts_sublist keep b).append
        (declaredNamesCases_filterCases_sublist keep rest)
theorem declaredNamesDflt_filterDflt_sublist (keep : Stmt D.Op → Bool) :
    ∀ d : Option (Block D.Op),
    (NormalForm.declaredNamesDflt (filterDflt keep d)).Sublist (NormalForm.declaredNamesDflt d)
  | none => List.Sublist.refl _
  | some b => by
      simp only [filterDflt, NormalForm.declaredNamesDflt]
      exact declaredNamesStmts_filterStmts_sublist keep b
end

/-- **`filterStmtsDeep` is declaration-non-generative** (declared names can only
shrink), proved once for all statement-pruning passes. -/
theorem preservesDecls_filterStmtsDeep (keep : Stmt D.Op → Bool) :
    PreservesDecls (filterStmtsDeep keep) :=
  PreservesDecls.of_sublist (fun b => declaredNamesStmts_filterStmts_sublist keep b)

/-- Any statement-pruning pass preserves `UniqueNames`, with no induction. -/
theorem preserves_uniqueNames_filterStmtsDeep (keep : Stmt D.Op → Bool) :
    Preserves NormalForm.UniqueNames (filterStmtsDeep keep) :=
  Preserves.uniqueNames_of_preservesDecls (preservesDecls_filterStmtsDeep keep)

/-! ## Demonstration — zero-induction preservation, including for a composite

A pass that rewrites expressions (`fe`) and then prunes statements (`keep`) — the
shape of a fold-then-DCE round — preserves `UniqueNames` purely by composition of
the two proven-once skeletons, with no new induction. -/
example (fe : Expr D.Op → Expr D.Op) (keep : Stmt D.Op → Bool) :
    Preserves NormalForm.UniqueNames (filterStmtsDeep keep ∘ mapExprsBlock fe) :=
  Preserves.uniqueNames_of_preservesDecls
    ((preservesDecls_filterStmtsDeep keep).comp (preservesDecls_mapExprsBlock fe))

end YulEvmCompiler.Optimizer
