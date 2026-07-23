import YulSemantics.Equiv

set_option warningAsError true

/-!
# Normalization: hoist all function definitions to the topmost block

`liftFunDefs b = collectStmts b ++ stripStmts b`:

* `collectStmts` gathers **every** `funDef` occurring anywhere in `b` (including
  inside other function bodies, loop parts, `if`/`switch`/nested blocks) and
  re-emits it with a body that has itself been stripped of nested definitions;
* `stripStmts` removes every `funDef` from its original position, recursing
  through the same structural positions.

So the result is a single top block: all functions first (each with a
definition-free body), then the original code with all definitions removed.
Because a Yul block *hoists* its `funDef`s into a fresh function scope, the top
block's scope ends up holding the whole program's functions, and every nested
block hoists the empty scope.

**Assumption.** This is only a semantics-preserving normalization when function
names are globally unique *and* the program is well scoped (every call resolves
to a function visible at the call site). Uniqueness makes the flattening
unambiguous and renaming-free; well-scopedness is what rules out the one
otherwise-broken direction — a call that is out of scope in the original (hence
stuck) but resolvable in the flattened program. See `HoistFunDefs.md` /
`Equiv.lean` in this directory for the equivalence statement and proof.

This file defines the transform and the syntactic predicates only.
-/

namespace YulEvmCompiler.Optimizer.Normalization

open YulSemantics

variable {D : Dialect}

/-! ### The transform -/

mutual

/-- All function definitions occurring in a statement, re-emitted with
definition-free bodies. -/
def collectStmt : Stmt D.Op → List (Stmt D.Op)
  | .funDef n ps rs body => .funDef n ps rs (stripStmts body) :: collectStmts body
  | .block b => collectStmts b
  | .cond _ b => collectStmts b
  | .switch _ cases dflt => collectCases cases ++ collectDflt dflt
  | .forLoop init _ post body =>
      collectStmts init ++ collectStmts post ++ collectStmts body
  | .letDecl _ _ => []
  | .assign _ _ => []
  | .exprStmt _ => []
  | .break => []
  | .continue => []
  | .leave => []

def collectStmts : List (Stmt D.Op) → List (Stmt D.Op)
  | [] => []
  | s :: rest => collectStmt s ++ collectStmts rest

def collectCases : List (Literal × Block D.Op) → List (Stmt D.Op)
  | [] => []
  | (_, b) :: rest => collectStmts b ++ collectCases rest

def collectDflt : Option (Block D.Op) → List (Stmt D.Op)
  | none => []
  | some b => collectStmts b

/-- Remove every `funDef`, recursing through nested blocks/`if`/`switch`/`for`. -/
def stripStmt : Stmt D.Op → Stmt D.Op
  | .block b => .block (stripStmts b)
  | .cond c b => .cond c (stripStmts b)
  | .switch c cases dflt => .switch c (stripCases cases) (stripDflt dflt)
  | .forLoop init c post body =>
      .forLoop (stripStmts init) c (stripStmts post) (stripStmts body)
  | .funDef n ps rs body => .funDef n ps rs (stripStmts body)
  | .letDecl vars val => .letDecl vars val
  | .assign vars e => .assign vars e
  | .exprStmt e => .exprStmt e
  | .break => .break
  | .continue => .continue
  | .leave => .leave

def stripStmts : List (Stmt D.Op) → List (Stmt D.Op)
  | [] => []
  | .funDef _ _ _ _ :: rest => stripStmts rest
  | s :: rest => stripStmt s :: stripStmts rest

def stripCases : List (Literal × Block D.Op) → List (Literal × Block D.Op)
  | [] => []
  | (l, b) :: rest => (l, stripStmts b) :: stripCases rest

def stripDflt : Option (Block D.Op) → Option (Block D.Op)
  | none => none
  | some b => some (stripStmts b)

end

/-- Hoist every function definition to the topmost block. -/
def liftFunDefs (b : Block D.Op) : Block D.Op :=
  collectStmts b ++ stripStmts b

/-! ### Syntactic conditions -/

mutual
/-- Every function name defined anywhere in a statement. -/
def funNamesStmt : Stmt D.Op → List Ident
  | .funDef n _ _ body => n :: funNamesStmts body
  | .block b => funNamesStmts b
  | .cond _ b => funNamesStmts b
  | .switch _ cases dflt => funNamesCases cases ++ funNamesDflt dflt
  | .forLoop init _ post body =>
      funNamesStmts init ++ funNamesStmts post ++ funNamesStmts body
  | _ => []
def funNamesStmts : List (Stmt D.Op) → List Ident
  | [] => []
  | s :: rest => funNamesStmt s ++ funNamesStmts rest
def funNamesCases : List (Literal × Block D.Op) → List Ident
  | [] => []
  | (_, b) :: rest => funNamesStmts b ++ funNamesCases rest
def funNamesDflt : Option (Block D.Op) → List Ident
  | none => []
  | some b => funNamesStmts b
end

/-- All function names in the program are distinct. -/
def UniqueFunNames (b : Block D.Op) : Prop := (funNamesStmts b).Nodup

end YulEvmCompiler.Optimizer.Normalization
