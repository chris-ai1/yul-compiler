import YulEvmCompiler.Optimizer.Implementation.InlineCallsCarry
import YulEvmCompiler.Optimizer.Implementation.InlineCallsResolve
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-!
# YulEvmCompiler.Optimizer.Implementation.InlineCallsCarryResolve

**Closure of the call-carrying inlining relation under layout resolution** —
the object-path bridge for `InlineCallsCarry`, the exact analogue of
`InlineCallsResolve` for the plain `InlineCalls` pass.

Layout resolution (`resolveForLayout*`) rewrites `dataoffset`/`datasize`
*builtins* into number literals; it never touches variable names, statement
shapes, or `.call` nodes.  Consequently every classifier and side condition of
the carry pass is resolution-invariant — `carryExpr`, `carryStmt(s)`,
`carryCases`, the call-name collectors `exprCallNames`/`stmtsCallNames`, the
classifier `carryClassifyDecl`, the shadow prune `carrySurvives`, the
profitability gate `carryOK` — and so the whole transform *commutes* with
resolution:

    resolveForLayoutStmts L (inlineCallsCarryBlock b)
      = inlineCallsCarryBlock (resolveForLayoutStmts L b).

The payoff `resolveInlineCallsCarryBlock_equiv'` then follows from the pass's
own soundness (`inlineCallsCarry.sound`) applied at the resolved block.

## House style

The site-rewrite facts (`inlineCore_resolve`, `siteOK_resolve`,
`lookupDelta_resolve`, `resolveIDecl`, `resolveDelta`, …) are *reused verbatim*
from `InlineCallsResolve` — the carry pass shares `inlineCore`/`siteOK`/site
shapes with `InlineCalls`, only the classifier differs.  The carry-specific
resolution-invariance lemmas below are near-verbatim copies of the
`scopedStmt_resolve`/`hoistDecls_resolve`/`deltaExtend_resolve` family from
`InlineCallsResolve`, adapted to the carry classifier (`carry*` for `scoped*`,
`carryDeltaExtend`/`carrySurvives` for `deltaExtend`).  Verbatim duplication is
the deliberate house style here, not a candidate for refactoring/sharing.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

/-! ### List-length and `liveMax` invariance (for the `carryOK` gate) -/

/-- Resolution preserves statement-sequence length. -/
theorem resolveForLayoutStmts_length (L : Layout) : ∀ ss : List (Stmt Op),
    (resolveForLayoutStmts L ss).length = ss.length
  | [] => by simp only [resolveForLayoutStmts]
  | s :: rest => by
      rw [resolveForLayoutStmts_cons, List.length_cons, List.length_cons,
        resolveForLayoutStmts_length L rest]

/-- Resolution of a `switch` statement, exposed as an equation (resolution is
well-founded, so this is not definitional). -/
theorem resolveForLayoutStmt_switch (L : Layout) (c : Expr Op)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    resolveForLayoutStmt L (.switch c cases dflt) =
      .switch (resolveForLayoutExpr L c) (resolveForLayoutCases L cases)
        (dflt.map (resolveForLayoutStmts L)) := by
  cases dflt with
  | none => simp only [resolveForLayoutStmt, Option.map_none]
  | some b => simp only [resolveForLayoutStmt, Option.map_some]

/-- Resolution of a `for` statement, exposed as an equation. -/
theorem resolveForLayoutStmt_forLoop (L : Layout) (init : Block Op) (c : Expr Op)
    (post body : Block Op) :
    resolveForLayoutStmt L (.forLoop init c post body) =
      .forLoop (resolveForLayoutStmts L init) (resolveForLayoutExpr L c)
        (resolveForLayoutStmts L post) (resolveForLayoutStmts L body) := by
  simp only [resolveForLayoutStmt]

mutual

/-- Resolution preserves the max-live-locals measure of a sequence. Because
`resolveForLayoutStmt` is well-founded (non-definitional), each head is first
rewritten to its constructor form so the structural `liveMax*` can reduce. -/
theorem liveMaxStmts_resolve (L : Layout) (acc : Nat) :
    ∀ ss : List (Stmt Op),
      liveMaxStmts acc (resolveForLayoutStmts L ss) = liveMaxStmts acc ss
  | [] => by simp only [resolveForLayoutStmts]
  | .letDecl xs v :: rest => by
      rw [resolveForLayoutStmts_cons, show resolveForLayoutStmt L (.letDecl xs v) =
        .letDecl xs (v.map (resolveForLayoutExpr L)) from by simp only [resolveForLayoutStmt]]
      show max acc (liveMaxStmts (acc + xs.length) (resolveForLayoutStmts L rest))
        = max acc (liveMaxStmts (acc + xs.length) rest)
      rw [liveMaxStmts_resolve L (acc + xs.length) rest]
  | .block b :: rest => by
      rw [resolveForLayoutStmts_cons, show resolveForLayoutStmt L (.block b) =
        .block (resolveForLayoutStmts L b) from by simp only [resolveForLayoutStmt]]
      show max (liveMaxStmts acc (resolveForLayoutStmts L b))
          (liveMaxStmts acc (resolveForLayoutStmts L rest))
        = max (liveMaxStmts acc b) (liveMaxStmts acc rest)
      rw [liveMaxStmts_resolve L acc b, liveMaxStmts_resolve L acc rest]
  | .cond c b :: rest => by
      rw [resolveForLayoutStmts_cons, show resolveForLayoutStmt L (.cond c b) =
        .cond (resolveForLayoutExpr L c) (resolveForLayoutStmts L b) from by
          simp only [resolveForLayoutStmt]]
      show max (liveMaxStmts acc (resolveForLayoutStmts L b))
          (liveMaxStmts acc (resolveForLayoutStmts L rest))
        = max (liveMaxStmts acc b) (liveMaxStmts acc rest)
      rw [liveMaxStmts_resolve L acc b, liveMaxStmts_resolve L acc rest]
  | .switch c cases dflt :: rest => by
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmt_switch]
      cases dflt with
      | none =>
          show max (max (liveMaxCases acc (resolveForLayoutCases L cases)) acc)
              (liveMaxStmts acc (resolveForLayoutStmts L rest))
            = max (max (liveMaxCases acc cases) acc) (liveMaxStmts acc rest)
          rw [liveMaxCases_resolve L acc cases, liveMaxStmts_resolve L acc rest]
      | some b =>
          show max (max (liveMaxCases acc (resolveForLayoutCases L cases))
                (liveMaxStmts acc (resolveForLayoutStmts L b)))
              (liveMaxStmts acc (resolveForLayoutStmts L rest))
            = max (max (liveMaxCases acc cases) (liveMaxStmts acc b))
                (liveMaxStmts acc rest)
          rw [liveMaxCases_resolve L acc cases, liveMaxStmts_resolve L acc b,
            liveMaxStmts_resolve L acc rest]
  | .forLoop init c post body :: rest => by
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmt_forLoop]
      show max (max (liveMaxStmts acc (resolveForLayoutStmts L init))
              (max (liveMaxStmts acc (resolveForLayoutStmts L post))
                (liveMaxStmts acc (resolveForLayoutStmts L body))))
            (liveMaxStmts acc (resolveForLayoutStmts L rest))
        = max (max (liveMaxStmts acc init)
              (max (liveMaxStmts acc post) (liveMaxStmts acc body)))
            (liveMaxStmts acc rest)
      rw [liveMaxStmts_resolve L acc init, liveMaxStmts_resolve L acc post,
        liveMaxStmts_resolve L acc body, liveMaxStmts_resolve L acc rest]
  | .assign xs e :: rest => by
      rw [resolveForLayoutStmts_cons, show resolveForLayoutStmt L (.assign xs e) =
        .assign xs (resolveForLayoutExpr L e) from by simp only [resolveForLayoutStmt]]
      show max acc (liveMaxStmts acc (resolveForLayoutStmts L rest))
        = max acc (liveMaxStmts acc rest)
      rw [liveMaxStmts_resolve L acc rest]
  | .exprStmt e :: rest => by
      rw [resolveForLayoutStmts_cons, show resolveForLayoutStmt L (.exprStmt e) =
        .exprStmt (resolveForLayoutExpr L e) from by simp only [resolveForLayoutStmt]]
      show max acc (liveMaxStmts acc (resolveForLayoutStmts L rest))
        = max acc (liveMaxStmts acc rest)
      rw [liveMaxStmts_resolve L acc rest]
  | .funDef n ps rs body :: rest => by
      rw [resolveForLayoutStmts_cons, show resolveForLayoutStmt L (.funDef n ps rs body) =
        .funDef n ps rs (resolveForLayoutStmts L body) from by simp only [resolveForLayoutStmt]]
      show max acc (liveMaxStmts acc (resolveForLayoutStmts L rest))
        = max acc (liveMaxStmts acc rest)
      rw [liveMaxStmts_resolve L acc rest]
  | .break :: rest => by
      rw [resolveForLayoutStmts_cons, show resolveForLayoutStmt L .break = .break from by
        simp only [resolveForLayoutStmt]]
      show max acc (liveMaxStmts acc (resolveForLayoutStmts L rest))
        = max acc (liveMaxStmts acc rest)
      rw [liveMaxStmts_resolve L acc rest]
  | .continue :: rest => by
      rw [resolveForLayoutStmts_cons, show resolveForLayoutStmt L .continue = .continue from by
        simp only [resolveForLayoutStmt]]
      show max acc (liveMaxStmts acc (resolveForLayoutStmts L rest))
        = max acc (liveMaxStmts acc rest)
      rw [liveMaxStmts_resolve L acc rest]
  | .leave :: rest => by
      rw [resolveForLayoutStmts_cons, show resolveForLayoutStmt L .leave = .leave from by
        simp only [resolveForLayoutStmt]]
      show max acc (liveMaxStmts acc (resolveForLayoutStmts L rest))
        = max acc (liveMaxStmts acc rest)
      rw [liveMaxStmts_resolve L acc rest]

/-- Resolution preserves the max-live-locals measure over `switch` cases. -/
theorem liveMaxCases_resolve (L : Layout) (acc : Nat) :
    ∀ cs : List (Literal × Block Op),
      liveMaxCases acc (resolveForLayoutCases L cs) = liveMaxCases acc cs
  | [] => by simp only [resolveForLayoutCases]
  | (l, b) :: rest => by
      rw [show resolveForLayoutCases L ((l, b) :: rest) =
        (l, resolveForLayoutStmts L b) :: resolveForLayoutCases L rest from by
          simp only [resolveForLayoutCases]]
      show max (liveMaxStmts acc (resolveForLayoutStmts L b))
          (liveMaxCases acc (resolveForLayoutCases L rest))
        = max (liveMaxStmts acc b) (liveMaxCases acc rest)
      rw [liveMaxStmts_resolve L acc b, liveMaxCases_resolve L acc rest]

end

/-- The carry profitability/pressure gate is resolution-invariant. -/
theorem carryOK_resolve (L : Layout) (d : IDecl) :
    carryOK (resolveIDecl L d) = carryOK d := by
  simp only [carryOK, resolveIDecl, resolveForLayoutStmts_length, liveMaxStmts_resolve]
  rfl

/-! ### `carryExpr`/`carryStmt` invariance (mirrors `scopedStmt_resolve`) -/

/-- Resolution preserves the carry-scoped-expression check. -/
theorem carryExpr_resolve (L : Layout) (bound : List Ident) (e : Expr Op) :
    carryExpr bound (resolveForLayoutExpr L e) = carryExpr bound e := by
  unfold carryExpr
  rw [exprVars_resolve]

mutual

/-- Resolution preserves the carry-scoped-statement check. -/
theorem carryStmt_resolve (L : Layout) (bound : List Ident) :
    ∀ s : Stmt Op, carryStmt bound (resolveForLayoutStmt L s) = carryStmt bound s
  | .letDecl xs none => by
      simp only [resolveForLayoutStmt, Option.map_none, carryStmt]
  | .letDecl xs (some e) => by
      simp only [resolveForLayoutStmt, Option.map_some, carryStmt, carryExpr_resolve]
  | .assign xs e => by
      simp only [resolveForLayoutStmt, carryStmt, carryExpr_resolve]
  | .exprStmt e => by
      simp only [resolveForLayoutStmt, carryStmt, carryExpr_resolve]
  | .block body => by
      simp only [resolveForLayoutStmt, carryStmt, carryStmts_resolve L bound body]
  | .cond c body => by
      simp only [resolveForLayoutStmt, carryStmt, carryExpr_resolve,
        carryStmts_resolve L bound body]
  | .switch c cases dflt => by
      cases dflt with
      | none =>
          simp only [resolveForLayoutStmt, carryStmt, carryExpr_resolve,
            carryCases_resolve L bound cases]
      | some body =>
          simp only [resolveForLayoutStmt, carryStmt, carryExpr_resolve,
            carryCases_resolve L bound cases, carryDflt,
            carryStmts_resolve L bound body]
          rfl
  | .funDef n ps rs body => by simp only [resolveForLayoutStmt, carryStmt]
  | .forLoop init c post body => by simp only [resolveForLayoutStmt, carryStmt]
  | .break => by simp only [resolveForLayoutStmt, carryStmt]
  | .continue => by simp only [resolveForLayoutStmt, carryStmt]
  | .leave => by simp only [resolveForLayoutStmt, carryStmt]

/-- Resolution preserves the carry-scoped-sequence check. -/
theorem carryStmts_resolve (L : Layout) (bound : List Ident) :
    ∀ ss : List (Stmt Op),
      carryStmts bound (resolveForLayoutStmts L ss) = carryStmts bound ss
  | [] => by simp only [resolveForLayoutStmts, carryStmts]
  | s :: rest => by
      rw [show resolveForLayoutStmts L (s :: rest) =
        resolveForLayoutStmt L s :: resolveForLayoutStmts L rest from by
          simp only [resolveForLayoutStmts]]
      simp only [carryStmts]
      rw [carryStmt_resolve L bound s]
      cases carryStmt bound s with
      | none => rfl
      | some bound' =>
          show carryStmts bound' (resolveForLayoutStmts L rest) = _
          rw [carryStmts_resolve L bound' rest]

/-- Resolution preserves the carry-scoped-cases check. -/
theorem carryCases_resolve (L : Layout) (bound : List Ident) :
    ∀ cs : List (Literal × Block Op),
      carryCases bound (resolveForLayoutCases L cs) = carryCases bound cs
  | [] => by simp only [resolveForLayoutCases, carryCases]
  | (l, b) :: rest => by
      rw [show resolveForLayoutCases L ((l, b) :: rest) =
        (l, resolveForLayoutStmts L b) :: resolveForLayoutCases L rest from by
          simp only [resolveForLayoutCases]]
      simp only [carryCases]
      rw [carryStmts_resolve L bound b, carryCases_resolve L bound rest]

end

/-! ### Call-name collectors are resolution-invariant

`resolveForLayoutExpr` maps a `dataoffset`/`datasize` builtin (whose only
argument is a string literal, hence call-free) to a number literal, and leaves
every `.call` node — name and arguments-modulo-resolution — intact.  So the
carried-call name multiset is unchanged. Mirrors `exprHasCall_resolve`. -/

mutual

/-- Resolution preserves the calls an expression names. -/
theorem exprCallNames_resolve (L : Layout) : ∀ e : Expr Op,
    exprCallNames (resolveForLayoutExpr L e) = exprCallNames e
  | .lit l => rfl
  | .var x => rfl
  | .builtin op args => by
      simp only [resolveForLayoutExpr]
      split
      · simp [exprCallNames, argsCallNames]
      · simp [exprCallNames, argsCallNames]
      · show argsCallNames (resolveForLayoutExprs L args) = argsCallNames args
        exact argsCallNames_resolve L args
  | .call f args => by
      show f :: argsCallNames (resolveForLayoutExprs L args) = f :: argsCallNames args
      rw [argsCallNames_resolve L args]

/-- Resolution preserves the calls an argument list names. -/
theorem argsCallNames_resolve (L : Layout) : ∀ es : List (Expr Op),
    argsCallNames (resolveForLayoutExprs L es) = argsCallNames es
  | [] => rfl
  | e :: rest => by
      show exprCallNames (resolveForLayoutExpr L e) ++
          argsCallNames (resolveForLayoutExprs L rest)
        = exprCallNames e ++ argsCallNames rest
      rw [exprCallNames_resolve L e, argsCallNames_resolve L rest]

end

mutual

/-- Resolution preserves the calls a statement names. -/
theorem stmtCallNames_resolve (L : Layout) : ∀ s : Stmt Op,
    stmtCallNames (resolveForLayoutStmt L s) = stmtCallNames s
  | .letDecl xs none => by simp only [resolveForLayoutStmt, Option.map_none, stmtCallNames]
  | .letDecl xs (some e) => by
      simp only [resolveForLayoutStmt, Option.map_some, stmtCallNames, exprCallNames_resolve]
  | .assign xs e => by
      simp only [resolveForLayoutStmt, stmtCallNames, exprCallNames_resolve]
  | .exprStmt e => by
      simp only [resolveForLayoutStmt, stmtCallNames, exprCallNames_resolve]
  | .block body => by
      simp only [resolveForLayoutStmt, stmtCallNames, stmtsCallNames_resolve L body]
  | .cond c body => by
      simp only [resolveForLayoutStmt, stmtCallNames, exprCallNames_resolve,
        stmtsCallNames_resolve L body]
  | .switch c cases dflt => by
      cases dflt with
      | none =>
          simp only [resolveForLayoutStmt, stmtCallNames, exprCallNames_resolve,
            casesCallNames_resolve L cases, dfltCallNames]
      | some body =>
          simp only [resolveForLayoutStmt, stmtCallNames, exprCallNames_resolve,
            casesCallNames_resolve L cases, dfltCallNames, stmtsCallNames_resolve L body]
  | .funDef n ps rs body => by simp only [resolveForLayoutStmt, stmtCallNames]
  | .forLoop init c post body => by
      simp only [resolveForLayoutStmt, stmtCallNames, stmtsCallNames_resolve L init,
        exprCallNames_resolve, stmtsCallNames_resolve L post, stmtsCallNames_resolve L body]
  | .break => by simp only [resolveForLayoutStmt, stmtCallNames]
  | .continue => by simp only [resolveForLayoutStmt, stmtCallNames]
  | .leave => by simp only [resolveForLayoutStmt, stmtCallNames]

/-- Resolution preserves the calls a statement sequence names. -/
theorem stmtsCallNames_resolve (L : Layout) : ∀ ss : List (Stmt Op),
    stmtsCallNames (resolveForLayoutStmts L ss) = stmtsCallNames ss
  | [] => by simp only [resolveForLayoutStmts, stmtsCallNames]
  | s :: rest => by
      rw [resolveForLayoutStmts_cons]
      simp only [stmtsCallNames]
      rw [stmtCallNames_resolve L s, stmtsCallNames_resolve L rest]

/-- Resolution preserves the calls `switch` case bodies name. -/
theorem casesCallNames_resolve (L : Layout) : ∀ cs : List (Literal × Block Op),
    casesCallNames (resolveForLayoutCases L cs) = casesCallNames cs
  | [] => by simp only [resolveForLayoutCases, casesCallNames]
  | (l, b) :: rest => by
      rw [show resolveForLayoutCases L ((l, b) :: rest) =
        (l, resolveForLayoutStmts L b) :: resolveForLayoutCases L rest from by
          simp only [resolveForLayoutCases]]
      simp only [casesCallNames]
      rw [stmtsCallNames_resolve L b, casesCallNames_resolve L rest]

end

/-! ### Classifier / hoist / prune commute with resolution
(mirrors `classifyDecl_resolve`, `hoistDecls_resolve`, `deltaExtend_resolve`) -/

/-- `carryClassifyDecl` commutes with resolution. -/
theorem carryClassifyDecl_resolve (L : Layout) (f : Ident) (ps rs : List Ident)
    (body : Block Op) :
    carryClassifyDecl f ps rs (resolveForLayoutStmts L body) =
      (carryClassifyDecl f ps rs body).map (resolveIDecl L) := by
  unfold carryClassifyDecl
  simp only [classifyDecl_resolve, dropTrailingLeave_resolve, carryStmts_resolve,
    stmtsCallNames_resolve]
  cases hcl : classifyDecl ps rs body with
  | some d0 => simp only [Option.map_some, Option.isSome_some, if_true, Option.map_none]
  | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, if_false]
      split_ifs <;> simp only [Option.map_some, Option.map_none, resolveIDecl]

/-- `carryHoistDecls` commutes with resolution. -/
theorem carryHoistDecls_resolve (L : Layout) : ∀ (body : List (Stmt Op))
    (seen : List Ident),
    carryHoistDecls seen (resolveForLayoutStmts L body) =
      (carryHoistDecls seen body).map (fun p => (p.1, resolveIDecl L p.2))
  | [], seen => by simp only [resolveForLayoutStmts, carryHoistDecls, List.map_nil]
  | s :: rest, seen => by
      rw [show resolveForLayoutStmts L (s :: rest) =
        resolveForLayoutStmt L s :: resolveForLayoutStmts L rest from by
          simp only [resolveForLayoutStmts]]
      cases s with
      | funDef f psf rsf b =>
          rw [show resolveForLayoutStmt L (.funDef f psf rsf b) =
            .funDef f psf rsf (resolveForLayoutStmts L b) from by
              simp only [resolveForLayoutStmt]]
          unfold carryHoistDecls
          split
          · exact carryHoistDecls_resolve L rest seen
          · rw [carryClassifyDecl_resolve]
            cases hcl : carryClassifyDecl f psf rsf b with
            | none =>
                simp only [Option.map_none]
                exact carryHoistDecls_resolve L rest (f :: seen)
            | some d =>
                simp only [Option.map_some]
                rw [carryHoistDecls_resolve L rest (f :: seen)]
                rfl
      | block b =>
          rw [show resolveForLayoutStmt L (.block b) =
            .block (resolveForLayoutStmts L b) from by simp only [resolveForLayoutStmt]]
          exact carryHoistDecls_resolve L rest seen
      | letDecl xs v =>
          rw [show resolveForLayoutStmt L (.letDecl xs v) =
            .letDecl xs (v.map (resolveForLayoutExpr L)) from by
              simp only [resolveForLayoutStmt]]
          exact carryHoistDecls_resolve L rest seen
      | assign xs e =>
          rw [show resolveForLayoutStmt L (.assign xs e) =
            .assign xs (resolveForLayoutExpr L e) from by simp only [resolveForLayoutStmt]]
          exact carryHoistDecls_resolve L rest seen
      | exprStmt e =>
          rw [show resolveForLayoutStmt L (.exprStmt e) =
            .exprStmt (resolveForLayoutExpr L e) from by simp only [resolveForLayoutStmt]]
          exact carryHoistDecls_resolve L rest seen
      | cond c b =>
          rw [show resolveForLayoutStmt L (.cond c b) =
            .cond (resolveForLayoutExpr L c) (resolveForLayoutStmts L b) from by
              simp only [resolveForLayoutStmt]]
          exact carryHoistDecls_resolve L rest seen
      | «switch» c cs dl =>
          cases dl with
          | none =>
              rw [show resolveForLayoutStmt L (.switch c cs none) =
                .switch (resolveForLayoutExpr L c) (resolveForLayoutCases L cs)
                  none from by simp only [resolveForLayoutStmt]]
              exact carryHoistDecls_resolve L rest seen
          | some b =>
              rw [show resolveForLayoutStmt L (.switch c cs (some b)) =
                .switch (resolveForLayoutExpr L c) (resolveForLayoutCases L cs)
                  (some (resolveForLayoutStmts L b)) from by
                    simp only [resolveForLayoutStmt]]
              exact carryHoistDecls_resolve L rest seen
      | forLoop i c po b =>
          rw [show resolveForLayoutStmt L (.forLoop i c po b) =
            .forLoop (resolveForLayoutStmts L i) (resolveForLayoutExpr L c)
              (resolveForLayoutStmts L po) (resolveForLayoutStmts L b) from by
              simp only [resolveForLayoutStmt]]
          exact carryHoistDecls_resolve L rest seen
      | «break» =>
          rw [show resolveForLayoutStmt L .break = .break from by
            simp only [resolveForLayoutStmt]]
          exact carryHoistDecls_resolve L rest seen
      | «continue» =>
          rw [show resolveForLayoutStmt L .continue = .continue from by
            simp only [resolveForLayoutStmt]]
          exact carryHoistDecls_resolve L rest seen
      | «leave» =>
          rw [show resolveForLayoutStmt L .leave = .leave from by
            simp only [resolveForLayoutStmt]]
          exact carryHoistDecls_resolve L rest seen

/-- Resolving a tracked pair leaves the carry-survives predicate unchanged. -/
theorem carrySurvives_resolveIDecl (L : Layout) (defs : List Ident)
    (p : Ident × IDecl) :
    carrySurvives defs (p.1, resolveIDecl L p.2) = carrySurvives defs p := by
  show (!defs.contains p.1 &&
      (stmtsCallNames (resolveForLayoutStmts L p.2.ss)).all (fun g => !defs.contains g))
    = (!defs.contains p.1 && (stmtsCallNames p.2.ss).all (fun g => !defs.contains g))
  rw [stmtsCallNames_resolve]

/-- The carry prune filter commutes with resolving declarations. -/
theorem resolveDelta_filter_carrySurvives (L : Layout) (Δ : DEnv)
    (defs : List Ident) :
    (resolveDelta L Δ).filter (carrySurvives defs) =
      resolveDelta L (Δ.filter (carrySurvives defs)) := by
  unfold resolveDelta
  induction Δ with
  | nil => rfl
  | cons p rest ih =>
      rw [List.map_cons, List.filter_cons, List.filter_cons,
        carrySurvives_resolveIDecl L defs p]
      by_cases hq : carrySurvives defs p
      · simp only [hq, if_true, List.map_cons]
        rw [ih]
      · simp only [hq, if_false]
        exact ih

/-- `carryDeltaExtend` commutes with resolution. -/
theorem carryDeltaExtend_resolve (L : Layout) (Δ : DEnv) (body : List (Stmt Op)) :
    carryDeltaExtend (resolveDelta L Δ) (resolveForLayoutStmts L body) =
      resolveDelta L (carryDeltaExtend Δ body) := by
  unfold carryDeltaExtend
  rw [carryHoistDecls_resolve, definedFuns_resolve,
    resolveDelta_filter_carrySurvives L Δ (definedFuns body)]
  show _ ++ _ = resolveDelta L (_ ++ _)
  unfold resolveDelta
  rw [List.map_append]

/-! ### The transform commutes with resolution (mirrors the `icStmt` family) -/

mutual

/-- Resolution commutes with the carry transform on one statement. -/
theorem cyStmt_resolve (L : Layout) (Δ : DEnv) :
    ∀ s : Stmt Op,
      resolveForLayoutStmts L (cyStmt Δ s) =
        cyStmt (resolveDelta L Δ) (resolveForLayoutStmt L s)
  | .letDecl xs (some (.call f as)) => by
      have hs : resolveForLayoutStmt L (.letDecl xs (some (.call f as)))
          = .letDecl xs (some (.call f (resolveForLayoutExprs L as))) := by
        simp only [resolveForLayoutStmt, Option.map_some, resolveForLayoutExpr]
      rw [hs, cyStmt, cyStmt, lookupDelta_resolve]
      cases hld : lookupDelta Δ f with
      | none =>
          simp only [Option.map_none]
          rw [resolveForLayoutStmts_singleton, hs]
      | some d =>
          simp only [Option.map_some]
          rw [carryOK_resolve, siteOK_resolve]
          by_cases hok : (carryOK d && siteOK d xs as true) = true
          · rw [if_pos hok, if_pos hok, resolveForLayoutStmts_cons,
              resolveForLayoutStmts_singleton, inlineCore_resolve,
              show resolveForLayoutStmt L (.letDecl xs none) = .letDecl xs none from by
                simp only [resolveForLayoutStmt, Option.map_none]]
          · rw [if_neg hok, if_neg hok, resolveForLayoutStmts_singleton, hs]
  | .assign xs (.call f as) => by
      have hs : resolveForLayoutStmt L (.assign xs (.call f as))
          = .assign xs (.call f (resolveForLayoutExprs L as)) := by
        simp only [resolveForLayoutStmt, resolveForLayoutExpr]
      rw [hs, cyStmt, cyStmt, lookupDelta_resolve]
      cases hld : lookupDelta Δ f with
      | none =>
          simp only [Option.map_none]
          rw [resolveForLayoutStmts_singleton, hs]
      | some d =>
          simp only [Option.map_some]
          rw [carryOK_resolve, siteOK_resolve]
          by_cases hok : (carryOK d && siteOK d xs as false) = true
          · rw [if_pos hok, if_pos hok, resolveForLayoutStmts_singleton,
              inlineCore_resolve]
          · rw [if_neg hok, if_neg hok, resolveForLayoutStmts_singleton, hs]
  | .exprStmt (.call f as) => by
      have hs : resolveForLayoutStmt L (.exprStmt (.call f as))
          = .exprStmt (.call f (resolveForLayoutExprs L as)) := by
        simp only [resolveForLayoutStmt, resolveForLayoutExpr]
      rw [hs, cyStmt, cyStmt, lookupDelta_resolve]
      cases hld : lookupDelta Δ f with
      | none =>
          simp only [Option.map_none]
          rw [resolveForLayoutStmts_singleton, hs]
      | some d =>
          simp only [Option.map_some]
          rw [carryOK_resolve, siteOK_resolve]
          by_cases hok : (carryOK d && siteOK d [] as false) = true
          · rw [if_pos hok, if_pos hok, resolveForLayoutStmts_singleton,
              inlineCore_resolve]
          · rw [if_neg hok, if_neg hok, resolveForLayoutStmts_singleton, hs]
  | .letDecl xs none => by
      simp only [cyStmt, resolveForLayoutStmts_singleton, resolveForLayoutStmt,
        Option.map_none]
  | .letDecl xs (some (.lit l)) => by
      simp only [cyStmt, resolveForLayoutStmts_singleton, resolveForLayoutStmt,
        Option.map_some, resolveForLayoutExpr]
  | .letDecl xs (some (.var y)) => by
      simp only [cyStmt, resolveForLayoutStmts_singleton, resolveForLayoutStmt,
        Option.map_some, resolveForLayoutExpr]
  | .letDecl xs (some (.builtin op es)) => by
      rw [show cyStmt Δ (.letDecl xs (some (.builtin op es))) =
        [.letDecl xs (some (.builtin op es))] from by simp only [cyStmt]]
      rw [resolveForLayoutStmts_singleton,
        show resolveForLayoutStmt L (.letDecl xs (some (.builtin op es))) =
          .letDecl xs (some (resolveForLayoutExpr L (.builtin op es))) from by
            simp only [resolveForLayoutStmt, Option.map_some]]
      simp only [resolveForLayoutExpr]
      split <;> simp only [cyStmt]
  | .assign xs (.lit l) => by
      simp only [cyStmt, resolveForLayoutStmts_singleton, resolveForLayoutStmt,
        resolveForLayoutExpr]
  | .assign xs (.var y) => by
      simp only [cyStmt, resolveForLayoutStmts_singleton, resolveForLayoutStmt,
        resolveForLayoutExpr]
  | .assign xs (.builtin op es) => by
      rw [show cyStmt Δ (.assign xs (.builtin op es)) =
        [.assign xs (.builtin op es)] from by simp only [cyStmt]]
      rw [resolveForLayoutStmts_singleton,
        show resolveForLayoutStmt L (.assign xs (.builtin op es)) =
          .assign xs (resolveForLayoutExpr L (.builtin op es)) from by
            simp only [resolveForLayoutStmt]]
      simp only [resolveForLayoutExpr]
      split <;> simp only [cyStmt]
  | .exprStmt (.lit l) => by
      simp only [cyStmt, resolveForLayoutStmts_singleton, resolveForLayoutStmt,
        resolveForLayoutExpr]
  | .exprStmt (.var y) => by
      simp only [cyStmt, resolveForLayoutStmts_singleton, resolveForLayoutStmt,
        resolveForLayoutExpr]
  | .exprStmt (.builtin op es) => by
      rw [show cyStmt Δ (.exprStmt (.builtin op es)) =
        [.exprStmt (.builtin op es)] from by simp only [cyStmt]]
      rw [resolveForLayoutStmts_singleton,
        show resolveForLayoutStmt L (.exprStmt (.builtin op es)) =
          .exprStmt (resolveForLayoutExpr L (.builtin op es)) from by
            simp only [resolveForLayoutStmt]]
      simp only [resolveForLayoutExpr]
      split <;> simp only [cyStmt]
  | .block body => by
      rw [show cyStmt Δ (.block body) = [.block (cyStmts (carryDeltaExtend Δ body) body)]
            from by simp only [cyStmt, cyBlock]]
      rw [resolveForLayoutStmts_singleton,
        show resolveForLayoutStmt L (.block (cyStmts (carryDeltaExtend Δ body) body)) =
          .block (resolveForLayoutStmts L (cyStmts (carryDeltaExtend Δ body) body))
            from by simp only [resolveForLayoutStmt]]
      rw [cyStmts_resolve L (carryDeltaExtend Δ body) body, ← carryDeltaExtend_resolve,
        show resolveForLayoutStmt L (.block body) =
          .block (resolveForLayoutStmts L body) from by simp only [resolveForLayoutStmt]]
      rw [cyStmt, cyBlock]
  | .funDef n ps rs body => by
      rw [show cyStmt Δ (.funDef n ps rs body) =
            [.funDef n ps rs (cyStmts (carryDeltaExtend Δ body) body)] from by
          simp only [cyStmt, cyBlock]]
      rw [resolveForLayoutStmts_singleton,
        show resolveForLayoutStmt L
            (.funDef n ps rs (cyStmts (carryDeltaExtend Δ body) body)) =
          .funDef n ps rs
            (resolveForLayoutStmts L (cyStmts (carryDeltaExtend Δ body) body))
            from by simp only [resolveForLayoutStmt]]
      rw [cyStmts_resolve L (carryDeltaExtend Δ body) body, ← carryDeltaExtend_resolve,
        show resolveForLayoutStmt L (.funDef n ps rs body) =
          .funDef n ps rs (resolveForLayoutStmts L body) from by
            simp only [resolveForLayoutStmt]]
      rw [cyStmt, cyBlock]
  | .cond c body => by
      rw [show cyStmt Δ (.cond c body) = [.cond c (cyStmts (carryDeltaExtend Δ body) body)]
            from by simp only [cyStmt, cyBlock]]
      rw [resolveForLayoutStmts_singleton,
        show resolveForLayoutStmt L (.cond c (cyStmts (carryDeltaExtend Δ body) body)) =
          .cond (resolveForLayoutExpr L c)
            (resolveForLayoutStmts L (cyStmts (carryDeltaExtend Δ body) body))
            from by simp only [resolveForLayoutStmt]]
      rw [cyStmts_resolve L (carryDeltaExtend Δ body) body, ← carryDeltaExtend_resolve,
        show resolveForLayoutStmt L (.cond c body) =
          .cond (resolveForLayoutExpr L c) (resolveForLayoutStmts L body) from by
            simp only [resolveForLayoutStmt]]
      rw [cyStmt, cyBlock]
  | .switch c cases dflt => by
      cases dflt with
      | none =>
          rw [show cyStmt Δ (.switch c cases none) =
                [.switch c (cyCases Δ cases) none] from by simp only [cyStmt, cyDflt]]
          rw [resolveForLayoutStmts_singleton,
            show resolveForLayoutStmt L (.switch c (cyCases Δ cases) none) =
              .switch (resolveForLayoutExpr L c)
                (resolveForLayoutCases L (cyCases Δ cases)) none from by
                simp only [resolveForLayoutStmt]]
          rw [cyCases_resolve L Δ cases,
            show resolveForLayoutStmt L (.switch c cases none) =
              .switch (resolveForLayoutExpr L c) (resolveForLayoutCases L cases) none
                from by simp only [resolveForLayoutStmt]]
          rw [cyStmt, cyDflt]
      | some body =>
          rw [show cyStmt Δ (.switch c cases (some body)) =
                [.switch c (cyCases Δ cases)
                  (some (cyStmts (carryDeltaExtend Δ body) body))] from by
              simp only [cyStmt, cyDflt, cyBlock]]
          rw [resolveForLayoutStmts_singleton,
            show resolveForLayoutStmt L (.switch c (cyCases Δ cases)
                  (some (cyStmts (carryDeltaExtend Δ body) body))) =
              .switch (resolveForLayoutExpr L c)
                (resolveForLayoutCases L (cyCases Δ cases))
                (some (resolveForLayoutStmts L
                  (cyStmts (carryDeltaExtend Δ body) body))) from by
                simp only [resolveForLayoutStmt]]
          rw [cyCases_resolve L Δ cases,
            cyStmts_resolve L (carryDeltaExtend Δ body) body, ← carryDeltaExtend_resolve,
            show resolveForLayoutStmt L (.switch c cases (some body)) =
              .switch (resolveForLayoutExpr L c) (resolveForLayoutCases L cases)
                (some (resolveForLayoutStmts L body)) from by
                simp only [resolveForLayoutStmt]]
          rw [cyStmt, cyDflt, cyBlock]
  | .forLoop init c post body => by
      rw [show cyStmt Δ (.forLoop init c post body) =
            [.forLoop init c
              (cyStmts (carryDeltaExtend (Δ.filter (carrySurvives (definedFuns init)))
                  post) post)
              (cyStmts (carryDeltaExtend (Δ.filter (carrySurvives (definedFuns init)))
                  body) body)] from by
          simp only [cyStmt, cyBlock]]
      rw [resolveForLayoutStmts_singleton,
        show resolveForLayoutStmt L (.forLoop init c
              (cyStmts (carryDeltaExtend (Δ.filter (carrySurvives (definedFuns init)))
                  post) post)
              (cyStmts (carryDeltaExtend (Δ.filter (carrySurvives (definedFuns init)))
                  body) body)) =
          .forLoop (resolveForLayoutStmts L init) (resolveForLayoutExpr L c)
            (resolveForLayoutStmts L
              (cyStmts (carryDeltaExtend (Δ.filter (carrySurvives (definedFuns init)))
                  post) post))
            (resolveForLayoutStmts L
              (cyStmts (carryDeltaExtend (Δ.filter (carrySurvives (definedFuns init)))
                  body) body)) from by simp only [resolveForLayoutStmt]]
      rw [cyStmts_resolve L
            (carryDeltaExtend (Δ.filter (carrySurvives (definedFuns init))) post) post,
        cyStmts_resolve L
            (carryDeltaExtend (Δ.filter (carrySurvives (definedFuns init))) body) body,
        ← carryDeltaExtend_resolve, ← carryDeltaExtend_resolve,
        ← resolveDelta_filter_carrySurvives,
        show resolveForLayoutStmt L (.forLoop init c post body) =
          .forLoop (resolveForLayoutStmts L init) (resolveForLayoutExpr L c)
            (resolveForLayoutStmts L post) (resolveForLayoutStmts L body) from by
            simp only [resolveForLayoutStmt]]
      rw [cyStmt, cyBlock, cyBlock, definedFuns_resolve]
  | .break => by simp only [cyStmt, resolveForLayoutStmts_singleton, resolveForLayoutStmt]
  | .continue => by
      simp only [cyStmt, resolveForLayoutStmts_singleton, resolveForLayoutStmt]
  | .leave => by simp only [cyStmt, resolveForLayoutStmts_singleton, resolveForLayoutStmt]

/-- Resolution commutes with the carry transform on a statement sequence. -/
theorem cyStmts_resolve (L : Layout) (Δ : DEnv) :
    ∀ ss : List (Stmt Op),
      resolveForLayoutStmts L (cyStmts Δ ss) =
        cyStmts (resolveDelta L Δ) (resolveForLayoutStmts L ss)
  | [] => by simp only [cyStmts, resolveForLayoutStmts]
  | s :: rest => by
      rw [cyStmts, resolveForLayoutStmts_append, cyStmt_resolve L Δ s,
        cyStmts_resolve L Δ rest, resolveForLayoutStmts_cons, cyStmts]

/-- Resolution commutes with the carry transform on `switch` cases. -/
theorem cyCases_resolve (L : Layout) (Δ : DEnv) :
    ∀ cs : List (Literal × Block Op),
      resolveForLayoutCases L (cyCases Δ cs) =
        cyCases (resolveDelta L Δ) (resolveForLayoutCases L cs)
  | [] => by simp only [cyCases, resolveForLayoutCases]
  | (l, b) :: rest => by
      rw [show cyCases Δ ((l, b) :: rest) =
            (l, cyStmts (carryDeltaExtend Δ b) b) :: cyCases Δ rest from by
          simp only [cyCases, cyBlock]]
      rw [show resolveForLayoutCases L
            ((l, cyStmts (carryDeltaExtend Δ b) b) :: cyCases Δ rest) =
          (l, resolveForLayoutStmts L (cyStmts (carryDeltaExtend Δ b) b)) ::
            resolveForLayoutCases L (cyCases Δ rest) from by
          simp only [resolveForLayoutCases]]
      rw [cyStmts_resolve L (carryDeltaExtend Δ b) b, ← carryDeltaExtend_resolve,
        cyCases_resolve L Δ rest,
        show resolveForLayoutCases L ((l, b) :: rest) =
          (l, resolveForLayoutStmts L b) :: resolveForLayoutCases L rest from by
            simp only [resolveForLayoutCases]]
      rw [cyCases, cyBlock]

end

/-! ### The payoff -/

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-- `cyBlock` commutes with resolution (thin wrapper over `cyStmts_resolve`). -/
theorem cyBlock_resolve (L : Layout) (Δ : DEnv) (b : List (Stmt Op)) :
    resolveForLayoutStmts L (cyBlock Δ b) =
      cyBlock (resolveDelta L Δ) (resolveForLayoutStmts L b) := by
  unfold cyBlock
  rw [cyStmts_resolve L (carryDeltaExtend Δ b) b, ← carryDeltaExtend_resolve]

/-- **Resolution congruence for `InlineCallsCarry`.** Resolving the source and
resolving the carry-inlined program are semantically equivalent — the
object-path bridge for the carry pass. The transform commutes with resolution
(`cyBlock_resolve`), so the goal reduces to the pass's own soundness at the
resolved block. -/
theorem resolveInlineCallsCarryBlock_equiv' (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (inlineCallsCarryBlock b)) := by
  have hcomm : resolveForLayoutStmts L (inlineCallsCarryBlock b)
      = inlineCallsCarryBlock (resolveForLayoutStmts L b) := by
    show resolveForLayoutStmts L (cyBlock [] b) = cyBlock [] (resolveForLayoutStmts L b)
    rw [cyBlock_resolve L [] b, show resolveDelta L ([] : DEnv) = [] from rfl]
  rw [hcomm]
  exact inlineCallsCarry.sound (resolveForLayoutStmts L b)

end YulEvmCompiler.Optimizer
