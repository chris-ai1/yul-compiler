import YulIR.Effects
import YulSemantics.Dialect.EVM

/-!
# YulIR.Simplify — local expression simplification (constant folding + identities)

The first IR optimization: a purely **local**, per-`Rhs` rewrite, so it needs no dataflow
or scoping analysis and is sound regardless of variable shadowing/mutation.

* **Constant folding.** A pure built-in applied to all-literal operands is evaluated by the
  *dialect's own* `stepOp` (the executable semantics), so the folded literal is exactly what
  the program would have computed — folding cannot diverge from the semantics.
* **Algebraic identities.** A small, conservative set that fires directly on ANF operands
  (`add(x,0)=x`, `mul(x,1)=x`, `mul(x,0)=0`, `sub(x,x)=0`, `xor(x,x)=0`, shift-by-0, …).
  Operands are atoms (side-effect-free), so dropping one (e.g. `mul(x,0)→0`) is sound.

This maps to Solidity's `expressionSimplifier` / `constantOptimiser` steps. It does *not*
propagate constants across `let`s (that needs value tracking, a later pass), so on ANF it
folds the innermost literal ops and every identity whose literal operand is inline.
-/

namespace YulIR

open YulSemantics.EVM (litValue stepOp)
open YulSemantics.EVM

/-- The literal value of an atom, if it is a literal. -/
def Atom.lit? : Atom → Option YulSemantics.Literal
  | .lit l => some l
  | .var _ => none

/-- All operands as literals, or `none` if any is a variable. -/
def allLits (as : List Atom) : Option (List YulSemantics.Literal) := as.mapM Atom.lit?

/-- Is the atom a literal equal to `n` (by dialect value)? -/
def Atom.isLitVal (a : Atom) (n : Nat) : Bool :=
  match a with
  | .lit l => litValue l == BitVec.ofNat 256 n
  | .var _ => false

/-- Evaluate a pure built-in on literal operands via the dialect's own evaluator. -/
def evalConst (op : Op) (lits : List YulSemantics.Literal) : Option YulSemantics.Literal :=
  match stepOp op (lits.map litValue) EvmState.init with
  | some (.ok [r] _) => some (.number r.toNat)
  | _ => none

private def zero : Atom := .lit (.number 0)

/-- Conservative algebraic identities on a pure built-in with atom operands. -/
def simplifyIdentity (op : Op) (args : List Atom) (orig : Rhs) : Rhs :=
  let z (a : Atom) : Bool := a.isLitVal 0
  let o (a : Atom) : Bool := a.isLitVal 1
  match op, args with
  | .add, [a, b] => if z a then .atom b else if z b then .atom a else orig
  | .sub, [a, b] => if z b then .atom a else if a == b then .atom zero else orig
  | .mul, [a, b] =>
      if z a || z b then .atom zero
      else if o a then .atom b else if o b then .atom a else orig
  | .div, [a, b] => if z b then .atom zero else if o b then .atom a else orig
  | .or,  [a, b] => if z a then .atom b else if z b then .atom a else if a == b then .atom a else orig
  | .and, [a, b] => if z a || z b then .atom zero else if a == b then .atom a else orig
  | .xor, [a, b] => if z a then .atom b else if z b then .atom a else if a == b then .atom zero else orig
  | .shl, [a, b] => if z a then .atom b else if z b then .atom zero else orig
  | .shr, [a, b] => if z a then .atom b else if z b then .atom zero else orig
  | .sar, [a, b] => if z a then .atom b else if z b then .atom zero else orig
  | _, _ => orig

/-- Simplify one right-hand side: fold pure literal ops, else apply identities. Impure
built-ins and user calls are left unchanged. -/
def simplifyRhs : Rhs → Rhs
  | .atom a => .atom a
  | .call fn args => .call fn args
  | .builtin op args =>
      let orig : Rhs := .builtin op args
      if ! Op.isPure op then orig
      else match allLits args with
        | some lits => match evalConst op lits with
            | some l => .atom (.lit l)
            | none   => simplifyIdentity op args orig
        | none => simplifyIdentity op args orig

mutual
/-- Apply `simplifyRhs` to every right-hand side in a statement, recursively. -/
def simplifyStmt (s : Stmt) : Stmt :=
  match s with
  | .block body        => .block (simplifyBlock body)
  | .funDef n ps rs b  => .funDef n ps rs (simplifyBlock b)
  | .letD vars rhs     => .letD vars (simplifyRhs rhs)
  | .assign vars rhs   => .assign vars (simplifyRhs rhs)
  | .effect rhs        => .effect (simplifyRhs rhs)
  | .cond c body       => .cond c (simplifyBlock body)
  | .switch c cases d  =>
      -- NOTE: `switch` case *bodies* are intentionally left untouched so this pass stays a clean
      -- `List Stmt`-only structural recursion, provable without pair-list termination machinery.
      -- (Minor completeness gap; the default branch is still simplified.) TODO: revisit.
      .switch c cases (match d with | none => none | some body => some (simplifyBlock body))
  | .loop post body    => .loop (simplifyBlock post) (simplifyBlock body)
  | .«break»           => .«break»
  | .«continue»        => .«continue»
  | .leave             => .leave
  termination_by 2 * sizeOf s + 1
  decreasing_by all_goals simp_wf <;> omega

/-- Simplify every statement in a block. -/
def simplifyBlock (b : List Stmt) : List Stmt :=
  match b with
  | []      => []
  | s :: ss => simplifyStmt s :: simplifyBlock ss
  termination_by 2 * sizeOf b
end

end YulIR
