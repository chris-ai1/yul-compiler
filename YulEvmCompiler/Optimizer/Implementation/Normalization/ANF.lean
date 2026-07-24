import YulEvmCompiler.Optimizer.Implementation.Normalization.NormalForm
import YulEvmCompiler.Optimizer.Spec.PrePostPass
set_option warningAsError true
/-!
# ANF normalization — establishing `NormalForm.IsANF`

An **optimizer pass that ensures administrative normal form**: after it, every
operand of a `let`/assignment/`if`/`switch`/expression statement is *flat* — an
atom (variable or literal) or a single operator applied to atoms — matching the
shared `NormalForm.IsANF` predicate. `for`-loop conditions are left as-is (ANF
exempts them: they are re-evaluated each iteration and cannot be hoisted).

## The transform

`flatten each nested sub-expression into a fresh `let`, innermost first, and use
the bound variable in its place:

```text
sstore(add(x, 1), mul(y, 2))   ⟶   let t0 := add(x, 1)
                                    let t1 := mul(y, 2)
                                    sstore(t0, t1)
let x := f(g(y))               ⟶   let t0 := g(y)
                                    let x := f(t0)
```

The right-hand side of a statement keeps its *top* operator with atomized
arguments (that is already `IsFlatRhs`); only strictly-nested operands are
lifted to `let`s. Prelude `let`s are inserted at the enclosing block level.

Temporaries are named `P ++ toString i` for a caller-supplied prefix `P` and a
threaded counter `i`. The **`IsANF` guarantee is independent of `P`** — it is a
purely syntactic shape property — so it is proved here for every `P`
(`anf_isANF`, `anf_establishes_isANF`). Choosing `P` *fresh* for the program
(e.g. `FreshenCalls.freshPrefix (stmtsIdents b)`) is what additionally makes the
pass preserve `UniqueNames` and be semantically sound. Operand preludes are
already emitted in Yul's **right-to-left** argument-evaluation order (see
`atomizeArgs`), so lifting a nested sub-expression to a `let` does not reorder
effects; the remaining soundness obligation is therefore fresh-binding
non-capture (the `anf-normalizer` branch's `ANFSound` fresh-binding weakening is
its foundation). That `EquivBlock` proof is the separate, larger obligation and
is **not** discharged here.

This module establishes the normal form; wiring the pass into the pipeline waits
on that soundness proof.
-/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics
open YulEvmCompiler.Optimizer.NormalForm

variable {Op : Type}

/-- Temporary name for the `i`-th lifted sub-expression under prefix `P`. -/
def tmp (P : String) (i : Nat) : Ident := P ++ toString i

/-! ### The flattener -/

mutual
/-- Flatten an expression to an **atom**, emitting a prelude of flat `let`s for
every nested operator application. -/
def atomize (P : String) : Nat → Expr Op → Nat × List (Stmt Op) × Expr Op
  | i, .var x => (i, [], .var x)
  | i, .lit l => (i, [], .lit l)
  | i, .builtin op args =>
      let r := atomizeArgs P i args
      (r.1 + 1, r.2.1 ++ [.letDecl [tmp P r.1] (some (.builtin op r.2.2))], .var (tmp P r.1))
  | i, .call f args =>
      let r := atomizeArgs P i args
      (r.1 + 1, r.2.1 ++ [.letDecl [tmp P r.1] (some (.call f r.2.2))], .var (tmp P r.1))
/-- Flatten a list of expressions to atoms, concatenating preludes in Yul's
**right-to-left** argument-evaluation order (rightmost operand's prelude first),
so lifting a nested sub-expression to a `let` preserves effect order. The atom
list stays positional. -/
def atomizeArgs (P : String) : Nat → List (Expr Op) → Nat × List (Stmt Op) × List (Expr Op)
  | i, [] => (i, [], [])
  | i, e :: rest =>
      let r₂ := atomizeArgs P i rest
      let r₁ := atomize P r₂.1 e
      (r₁.1, r₂.2.1 ++ r₁.2.1, r₁.2.2 :: r₂.2.2)
end

/-- Flatten a statement's right-hand-side operand: keep its top operator, atomize
its arguments (an atom is left untouched). The result is `IsFlatRhs`. -/
def flatRhs (P : String) (i : Nat) : Expr Op → Nat × List (Stmt Op) × Expr Op
  | .var x => (i, [], .var x)
  | .lit l => (i, [], .lit l)
  | .builtin op args => let r := atomizeArgs P i args; (r.1, r.2.1, .builtin op r.2.2)
  | .call f args => let r := atomizeArgs P i args; (r.1, r.2.1, .call f r.2.2)

mutual
/-- ANF-normalize one statement into a list of statements (prelude ++ rewritten). -/
def anfStmt (P : String) : Nat → Stmt Op → Nat × List (Stmt Op)
  | i, .letDecl vs (some e) =>
      let r := flatRhs P i e; (r.1, r.2.1 ++ [.letDecl vs (some r.2.2)])
  | i, .letDecl vs none => (i, [.letDecl vs none])
  | i, .assign vs e => let r := flatRhs P i e; (r.1, r.2.1 ++ [.assign vs r.2.2])
  | i, .exprStmt e => let r := flatRhs P i e; (r.1, r.2.1 ++ [.exprStmt r.2.2])
  | i, .cond c body =>
      let r := flatRhs P i c
      let b := anfStmts P r.1 body
      (b.1, r.2.1 ++ [.cond r.2.2 b.2])
  | i, .switch c cases dflt =>
      let r := flatRhs P i c
      let cs := anfCases P r.1 cases
      let d := anfDflt P cs.1 dflt
      (d.1, r.2.1 ++ [.switch r.2.2 cs.2 d.2])
  | i, .forLoop init c post body =>
      let ri := anfStmts P i init
      let rp := anfStmts P ri.1 post
      let rb := anfStmts P rp.1 body
      (rb.1, [.forLoop ri.2 c rp.2 rb.2])
  | i, .funDef n ps rs body => let r := anfStmts P i body; (r.1, [.funDef n ps rs r.2])
  | i, .block b => let r := anfStmts P i b; (r.1, [.block r.2])
  | i, .«break» => (i, [.«break»])
  | i, .«continue» => (i, [.«continue»])
  | i, .leave => (i, [.leave])
def anfStmts (P : String) : Nat → List (Stmt Op) → Nat × List (Stmt Op)
  | i, [] => (i, [])
  | i, s :: rest =>
      let r := anfStmt P i s
      let rr := anfStmts P r.1 rest
      (rr.1, r.2 ++ rr.2)
def anfCases (P : String) : Nat → List (Literal × Block Op) → Nat × List (Literal × Block Op)
  | i, [] => (i, [])
  | i, (l, b) :: rest =>
      let r := anfStmts P i b
      let rr := anfCases P r.1 rest
      (rr.1, (l, r.2) :: rr.2)
def anfDflt (P : String) : Nat → Option (Block Op) → Nat × Option (Block Op)
  | i, none => (i, none)
  | i, some b => let r := anfStmts P i b; (r.1, some r.2)
end

/-- ANF-normalize a block under prefix `P`. -/
def anfBlock (P : String) (b : Block Op) : Block Op := (anfStmts P 0 b).2

/-! ### Establishment of `NormalForm.IsANF` -/

/-- `AnfStmts` distributes over `++`. -/
theorem anfStmts_append : ∀ (a b : List (Stmt Op)),
    AnfStmts (a ++ b) ↔ (AnfStmts a ∧ AnfStmts b)
  | [], b => by simp [AnfStmts]
  | s :: a', b => by
      simp only [List.cons_append, AnfStmts, anfStmts_append a' b]
      tauto

mutual
theorem atomize_atom (P : String) : ∀ (i : Nat) (e : Expr Op), IsAtom (atomize P i e).2.2
  | _, .var _ => by simp [atomize, IsAtom]
  | _, .lit _ => by simp [atomize, IsAtom]
  | _, .builtin _ args => by simp [atomize, IsAtom]
  | _, .call _ args => by simp [atomize, IsAtom]
theorem atomizeArgs_atomic (P : String) : ∀ (i : Nat) (args : List (Expr Op)),
    AtomicArgs (atomizeArgs P i args).2.2
  | _, [] => by simp [atomizeArgs, AtomicArgs]
  | i, e :: rest => by
      simp only [atomizeArgs, AtomicArgs]
      exact ⟨atomize_atom P _ e, atomizeArgs_atomic P i rest⟩
theorem atomize_pre (P : String) : ∀ (i : Nat) (e : Expr Op), AnfStmts (atomize P i e).2.1
  | _, .var _ => by simp [atomize, AnfStmts]
  | _, .lit _ => by simp [atomize, AnfStmts]
  | i, .builtin op args => by
      simp only [atomize]
      rw [anfStmts_append]
      refine ⟨atomizeArgs_pre P i args, ?_⟩
      simp [AnfStmts, AnfStmt, IsFlatRhs, atomizeArgs_atomic P i args]
  | i, .call f args => by
      simp only [atomize]
      rw [anfStmts_append]
      refine ⟨atomizeArgs_pre P i args, ?_⟩
      simp [AnfStmts, AnfStmt, IsFlatRhs, atomizeArgs_atomic P i args]
theorem atomizeArgs_pre (P : String) : ∀ (i : Nat) (args : List (Expr Op)),
    AnfStmts (atomizeArgs P i args).2.1
  | _, [] => by simp [atomizeArgs, AnfStmts]
  | i, e :: rest => by
      simp only [atomizeArgs]
      rw [anfStmts_append]
      exact ⟨atomizeArgs_pre P i rest, atomize_pre P _ e⟩
end

theorem flatRhs_flat (P : String) (i : Nat) (e : Expr Op) : IsFlatRhs (flatRhs P i e).2.2 := by
  cases e with
  | var _ => simp [flatRhs, IsFlatRhs]
  | lit _ => simp [flatRhs, IsFlatRhs]
  | builtin op args => simp [flatRhs, IsFlatRhs, atomizeArgs_atomic P i args]
  | call f args => simp [flatRhs, IsFlatRhs, atomizeArgs_atomic P i args]

theorem flatRhs_pre (P : String) (i : Nat) (e : Expr Op) : AnfStmts (flatRhs P i e).2.1 := by
  cases e with
  | var _ => simp [flatRhs, AnfStmts]
  | lit _ => simp [flatRhs, AnfStmts]
  | builtin op args => simpa [flatRhs] using atomizeArgs_pre P i args
  | call f args => simpa [flatRhs] using atomizeArgs_pre P i args

mutual
theorem anfStmt_anf (P : String) : ∀ (i : Nat) (s : Stmt Op), AnfStmts (anfStmt P i s).2
  | i, .letDecl vs (some e) => by
      simp only [anfStmt]; rw [anfStmts_append]
      exact ⟨flatRhs_pre P i e, by simp [AnfStmts, AnfStmt, flatRhs_flat P i e]⟩
  | _, .letDecl _ none => by simp [anfStmt, AnfStmts, AnfStmt]
  | i, .assign vs e => by
      simp only [anfStmt]; rw [anfStmts_append]
      exact ⟨flatRhs_pre P i e, by simp [AnfStmts, AnfStmt, flatRhs_flat P i e]⟩
  | i, .exprStmt e => by
      simp only [anfStmt]; rw [anfStmts_append]
      exact ⟨flatRhs_pre P i e, by simp [AnfStmts, AnfStmt, flatRhs_flat P i e]⟩
  | i, .cond c body => by
      simp only [anfStmt]; rw [anfStmts_append]
      exact ⟨flatRhs_pre P i c,
        by simp only [AnfStmts, AnfStmt, and_true]
           exact ⟨flatRhs_flat P i c, anfStmts_anf P _ body⟩⟩
  | i, .switch c cases dflt => by
      simp only [anfStmt]; rw [anfStmts_append]
      refine ⟨flatRhs_pre P i c, ?_⟩
      simp only [AnfStmts, AnfStmt, and_true]
      exact ⟨flatRhs_flat P i c, anfCases_anf P _ cases, anfDflt_anf P _ dflt⟩
  | i, .forLoop init c post body => by
      simp only [anfStmt, AnfStmts, AnfStmt, and_true]
      exact ⟨anfStmts_anf P i init, anfStmts_anf P _ post, anfStmts_anf P _ body⟩
  | i, .funDef n ps rs body => by
      simp only [anfStmt, AnfStmts, AnfStmt, and_true]; exact anfStmts_anf P i body
  | i, .block b => by
      simp only [anfStmt, AnfStmts, AnfStmt, and_true]; exact anfStmts_anf P i b
  | _, .«break» => by simp [anfStmt, AnfStmts, AnfStmt]
  | _, .«continue» => by simp [anfStmt, AnfStmts, AnfStmt]
  | _, .leave => by simp [anfStmt, AnfStmts, AnfStmt]
theorem anfStmts_anf (P : String) : ∀ (i : Nat) (b : List (Stmt Op)), AnfStmts (anfStmts P i b).2
  | _, [] => by simp [anfStmts, AnfStmts]
  | i, s :: rest => by
      simp only [anfStmts]; rw [anfStmts_append]
      exact ⟨anfStmt_anf P i s, anfStmts_anf P _ rest⟩
theorem anfCases_anf (P : String) : ∀ (i : Nat) (cs : List (Literal × Block Op)),
    AnfCases (anfCases P i cs).2
  | _, [] => by simp [anfCases, AnfCases]
  | i, (l, b) :: rest => by
      simp only [anfCases, AnfCases]
      exact ⟨anfStmts_anf P i b, anfCases_anf P _ rest⟩
theorem anfDflt_anf (P : String) : ∀ (i : Nat) (d : Option (Block Op)), AnfDflt (anfDflt P i d).2
  | _, none => by simp [anfDflt, AnfDflt]
  | i, some b => by simp only [anfDflt, AnfDflt]; exact anfStmts_anf P i b
end

/-- **The ANF pass establishes administrative normal form**, for every prefix `P`
and every input block. -/
theorem anf_isANF (P : String) (b : Block Op) : IsANF (anfBlock P b) :=
  anfStmts_anf P 0 b

/-! ### Framework integration -/

section
open YulEvmCompiler.Optimizer
variable {D : Dialect}

/-- ANF as an invariant **establisher** (`Spec/PrePostPass.lean`): from any input
(`pre = True`) it reaches `NormalForm.IsANF`. Composed with the `Preserves`-side
discipline, this is the one pass that has to *reach* ANF; downstream passes need
only keep it. -/
theorem anf_establishes_isANF (P : String) :
    Establishes (D := D) (fun _ => True) NormalForm.IsANF (anfBlock P) :=
  fun b _ => anf_isANF P b

end

end YulEvmCompiler.Optimizer.ANF
