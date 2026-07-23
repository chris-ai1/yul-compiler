import YulEvmCompiler.Optimizer.Implementation.Normalization.ANF
/-!
# ANF pass 1 — block-scoped operand flattening

The first of two passes (see `ANFFlattenBlocks` for pass 2). This pass flattens
each **straight-line** statement's operands into atoms, scoping the introduced
temporaries in a fresh sub-block so the enclosing `restore` discharges them
locally — no persistent-temporary frame invariant needed:

```text
sstore(add(a,b), c)  ⟶  { let t := add(a,b); sstore(t, c) }
x := f(g(y))         ⟶  { let t := g(y); x := f(t) }
let x := f(g(y))     ⟶  let x; { let t := g(y); x := f(t) }
```

The `let` case is the subtle one: the *binding* `x` must survive past the
temporaries, so it is declared **outside** the block (`let x;`) and assigned
**inside** it (`x := f(t)`), where the temporaries are in scope. A statement can
therefore expand to a *list* of statements, so the transform is `Stmt → List Stmt`
(and `bsStmts` flat-maps it). Control-flow statements recurse into their bodies;
the condition/scrutinee is left unchanged (atomizing those is a later refinement).

Pass 2 (block flattening / inlining) then lifts the sub-blocks back out, and the
two compose to the persistent-temporary form. Soundness of each per-statement
rewrite is a local `EquivStmts [s] (bsStmt1 P s)` (via `restore_prefix` and the
empty-scope congruence), composed with an `EquivStmts` append congruence.

This file: the transform. The `EquivStmts` soundness lives in
`ANFBlockScopedSound`.
-/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics YulSemantics.EVM

/-- Block-scoped flattening of one statement into a list of statements.
Straight-line statements have their operands flattened inside a fresh sub-block;
`let` additionally declares its binding outside the block. Everything else is
returned unchanged (control-flow recursion is added in a later refinement). -/
def bsStmt1 (P : String) : Stmt Op → List (Stmt Op)
  | .assign vars e =>
      let (_, pre, e') := flattenTop P 0 e
      if pre.isEmpty then [.assign vars e]
      else [.block (pre ++ [.assign vars e'])]
  | .exprStmt e =>
      let (_, pre, e') := flattenTop P 0 e
      if pre.isEmpty then [.exprStmt e]
      else [.block (pre ++ [.exprStmt e'])]
  | s => [s]

/-- Block-scoped flattening of a statement list (flat-map of `bsStmt1`). -/
def bsStmts (P : String) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => bsStmt1 P s ++ bsStmts P rest

@[simp] theorem bsStmts_nil (P : String) : bsStmts P [] = [] := rfl

@[simp] theorem bsStmts_cons (P : String) (s : Stmt Op) (rest : List (Stmt Op)) :
    bsStmts P (s :: rest) = bsStmt1 P s ++ bsStmts P rest := rfl

end YulEvmCompiler.Optimizer.ANF
