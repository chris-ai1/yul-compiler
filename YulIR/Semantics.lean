import YulIR.Ast
import YulSemantics.Interp

/-!
# YulIR.Semantics — a definitional interpreter for the IR

The IR's own semantics: a total, fuel-indexed executable interpreter, delegating built-in
evaluation to the EVM dialect's `stepOp` (so EVM opcode behaviour is *inherited*, never
re-axiomatised) and mirroring the structure of `YulSemantics.Interp`. This is what optimization
soundness is proved against — being a `def`, pass-soundness proofs are equational rather than
inductions over a large relation.

Because the IR is ANF (built-in/call arguments are `Atom`s), argument evaluation is trivial and
side-effect-free — the entanglement between expression evaluation, effects, and halting that
complicates the Yul judgment is gone.

Relating this interpreter to the Yul semantics through `toYul` (translation soundness) is future
work; for now it is validated against the Yul interpreter by differential `#eval` (see
`YulIR/SemanticsExamples`).
-/

namespace YulIR.Sem

open YulSemantics (Result Outcome Ident Literal)
open YulSemantics.EVM

/-- IR runtime values are EVM words. -/
abbrev Val := U256

/-- Variable environment: a scoped stack of bindings, innermost first. -/
abbrev VEnv := List (Ident × Val)

/-- A user-defined function's signature and body. -/
structure FDecl where
  params : List Ident
  rets   : List Ident
  body   : Block

/-- One lexical scope's hoisted function declarations. -/
abbrev FScope := List (Ident × FDecl)

/-- Function environment: a stack of scopes, innermost first. -/
abbrev FEnv := List FScope

/-- Look up a variable (innermost binding). -/
def VEnv.get (env : VEnv) (x : Ident) : Option Val :=
  (env.find? (fun p => p.1 == x)).map (·.2)

/-- Update the innermost binding of `x` (no-op if unbound). -/
def VEnv.set (env : VEnv) (x : Ident) (v : Val) : VEnv :=
  match env with
  | [] => []
  | (y, w) :: rest => if y == x then (x, v) :: rest else (y, w) :: VEnv.set rest x v

/-- Update several variables in order. -/
def VEnv.setMany (env : VEnv) (xs : List Ident) (vs : List Val) : VEnv :=
  (xs.zip vs).foldl (fun acc p => VEnv.set acc p.1 p.2) env

/-- Bind each name to zero. -/
def bindZeros (xs : List Ident) : VEnv := xs.map (fun x => (x, (0 : Val)))

/-- Drop bindings introduced since `outer` (block exit), keeping outer ones. -/
def restore (outer inner : VEnv) : VEnv := inner.drop (inner.length - outer.length)

/-- Collect a block's `funDef`s into one hoisted scope. -/
def hoist (body : Block) : FScope :=
  body.filterMap (fun s => match s with
    | .funDef n ps rs b => some (n, { params := ps, rets := rs, body := b })
    | _ => none)

/-- Resolve a function name to its declaration and the environment visible at its definition. -/
def lookupFun : FEnv → Ident → Option (FDecl × FEnv)
  | [], _ => none
  | scope :: rest, f =>
    match scope.find? (fun p => p.1 == f) with
    | some p => some (p.2, scope :: rest)
    | none   => lookupFun rest f

/-- The block a constant `switch` value selects. -/
def selectSwitch (cv : Val) (cases : List (Literal × Block)) (dflt : Option Block) : Block :=
  match cases.find? (fun p => cv == litValue p.1) with
  | some p => p.2
  | none   => dflt.getD []

/-- Evaluate an atom (side-effect free; `none` if a variable is unbound). -/
def evalAtom (env : VEnv) : Atom → Option Val
  | .lit l => some (litValue l)
  | .var x => env.get x

/-- Evaluate an atom list. -/
def evalAtoms (env : VEnv) (as : List Atom) : Option (List Val) := as.mapM (evalAtom env)

/-- The result of evaluating an rhs: a value list with a new state, or a halt. -/
inductive RRes
  | vals (vs : List Val) (st : EvmState)
  | halt (st : EvmState)

mutual

/-- Evaluate a right-hand side. -/
def evalRhs (fuel : Nat) (funs : FEnv) (env : VEnv) (st : EvmState) : Rhs → Result RRes
  | .atom a =>
      match evalAtom env a with
      | some v => .ok (.vals [v] st)
      | none   => .stuck
  | .builtin op args =>
      match evalAtoms env args with
      | none => .stuck
      | some vals =>
          match stepOp op vals st with
          | some (.ok rets st') => .ok (.vals rets st')
          | some (.halt st')    => .ok (.halt st')
          | none                => .stuck
  | .call fn args =>
      match fuel with
      | 0 => .outOfFuel
      | n + 1 =>
        match evalAtoms env args with
        | none => .stuck
        | some argvals =>
          match lookupFun funs fn with
          | none => .stuck
          | some (decl, cenv) =>
              if argvals.length == decl.params.length then
                match execStmt n cenv (decl.params.zip argvals ++ bindZeros decl.rets) st
                    (.block decl.body) with
                | .ok (Vend, st2, .normal) | .ok (Vend, st2, .leave) =>
                    .ok (.vals (decl.rets.map (fun r => (VEnv.get Vend r).getD 0)) st2)
                | .ok (_, st2, .halt) => .ok (.halt st2)
                | .ok (_, _, _)       => .stuck
                | .stuck => .stuck
                | .outOfFuel => .outOfFuel
              else .stuck

/-- Execute a single statement. -/
def execStmt (fuel : Nat) (funs : FEnv) (env : VEnv) (st : EvmState) :
    Stmt → Result (VEnv × EvmState × Outcome)
  | .funDef .. => .ok (env, st, .normal)
  | .«break»    => .ok (env, st, .«break»)
  | .«continue» => .ok (env, st, .«continue»)
  | .leave      => .ok (env, st, .leave)
  | .letD vars rhs =>
      match evalRhs fuel funs env st rhs with
      | .ok (.vals vs st1) => if vs.length == vars.length then .ok (vars.zip vs ++ env, st1, .normal) else .stuck
      | .ok (.halt st1) => .ok (env, st1, .halt)
      | .stuck => .stuck
      | .outOfFuel => .outOfFuel
  | .assign vars rhs =>
      match evalRhs fuel funs env st rhs with
      | .ok (.vals vs st1) => if vs.length == vars.length then .ok (env.setMany vars vs, st1, .normal) else .stuck
      | .ok (.halt st1) => .ok (env, st1, .halt)
      | .stuck => .stuck
      | .outOfFuel => .outOfFuel
  | .effect rhs =>
      match evalRhs fuel funs env st rhs with
      | .ok (.vals [] st1) => .ok (env, st1, .normal)
      | .ok (.vals _ _)    => .stuck
      | .ok (.halt st1)    => .ok (env, st1, .halt)
      | .stuck => .stuck
      | .outOfFuel => .outOfFuel
  | .cond c body =>
      match evalAtom env c with
      | none => .stuck
      | some cv => if cv == 0 then .ok (env, st, .normal)
                   else match fuel with
                        | 0 => .outOfFuel
                        | n + 1 => execStmt n funs env st (.block body)
  | .switch c cases dflt =>
      match evalAtom env c with
      | none => .stuck
      | some cv => match fuel with
                   | 0 => .outOfFuel
                   | n + 1 => execStmt n funs env st (.block (selectSwitch cv cases dflt))
  | .block body =>
      match fuel with
      | 0 => .outOfFuel
      | n + 1 =>
        match execStmts n (hoist body :: funs) env st body with
        | .ok (Vb, stb, o) => .ok (restore env Vb, stb, o)
        | .stuck => .stuck
        | .outOfFuel => .outOfFuel
  | .loop post body =>
      match fuel with
      | 0 => .outOfFuel
      | n + 1 => execLoop n funs env st post body

/-- Execute a statement sequence, short-circuiting on a non-`normal` outcome. -/
def execStmts (fuel : Nat) (funs : FEnv) (env : VEnv) (st : EvmState) :
    Block → Result (VEnv × EvmState × Outcome)
  | [] => .ok (env, st, .normal)
  | s :: rest =>
      match fuel with
      | 0 => .outOfFuel
      | n + 1 =>
        match execStmt n funs env st s with
        | .ok (V1, st1, .normal) => execStmts n funs V1 st1 rest
        | .ok (V1, st1, o)       => .ok (V1, st1, o)
        | .stuck => .stuck
        | .outOfFuel => .outOfFuel

/-- Execute a loop body/post (the IR loop is `for {} 1 { post } { body }`). -/
def execLoop (fuel : Nat) (funs : FEnv) (env : VEnv) (st : EvmState) (post body : Block) :
    Result (VEnv × EvmState × Outcome) :=
  match fuel with
  | 0 => .outOfFuel
  | n + 1 =>
    match execStmt n funs env st (.block body) with
    | .ok (Vb, stb, .«break»)    => .ok (Vb, stb, .normal)
    | .ok (Vb, stb, .leave)      => .ok (Vb, stb, .leave)
    | .ok (Vb, stb, .halt)       => .ok (Vb, stb, .halt)
    | .ok (Vb, stb, .normal) | .ok (Vb, stb, .«continue») =>
        match execStmt n funs Vb stb (.block post) with
        | .ok (Vp, stp, .normal) => execLoop n funs Vp stp post body
        | .ok (Vp, stp, .halt)   => .ok (Vp, stp, .halt)
        | .ok (_, _, _)          => .stuck
        | .stuck => .stuck
        | .outOfFuel => .outOfFuel
    | .stuck => .stuck
    | .outOfFuel => .outOfFuel

end

/-- Run a whole IR program from an initial state. -/
def run (fuel : Nat) (prog : Block) (st0 : EvmState) : Result (VEnv × EvmState × Outcome) :=
  execStmt fuel [] [] st0 (.block prog)

end YulIR.Sem
