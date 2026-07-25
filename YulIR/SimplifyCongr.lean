import YulIR.SimplifySound

set_option linter.unusedSimpArgs false

/-!
# YulIR.SimplifyCongr — whole-program soundness of `Simplify`

Lifts the per-`Rhs` lemma `simplifyRhs_eval` to the whole interpreter: for every fuel, running
the simplified program under the simplified function environment yields exactly the same result
as running the original. Because `simplify` rewrites only right-hand sides and preserves every
binding, variable name, and control-flow shape, the result is *definitionally equal* — no
observational-equivalence quotient is needed.

The function environment must be simplified in lockstep (every hoisted function body is itself
simplified), captured by `simplifyFEnv`; the key commutation facts are that `hoist` and
`lookupFun` both commute with it.
-/

namespace YulIR

open YulSemantics YulSemantics.EVM
open YulIR.Sem

/-- Simplify one hoisted scope: rewrite every function body. -/
def simplifyFScope (sc : FScope) : FScope :=
  sc.map (fun p => (p.1, { p.2 with body := simplifyBlock p.2.body }))

/-- Simplify a whole function environment, scope by scope. -/
def simplifyFEnv (funs : FEnv) : FEnv := funs.map simplifyFScope

@[simp] theorem simplifyFEnv_cons (sc : FScope) (funs : FEnv) :
    simplifyFEnv (sc :: funs) = simplifyFScope sc :: simplifyFEnv funs := rfl

/-- Simplifying a statement does not change whether it is a `funDef`, nor its name/params/rets;
so `hoist` commutes with `simplifyBlock`. -/
theorem hoist_simplifyBlock (body : Block) :
    Sem.hoist (simplifyBlock body) = simplifyFScope (Sem.hoist body) := by
  induction body with
  | nil => simp [Sem.hoist, simplifyBlock, simplifyFScope]
  | cons s ss ih =>
    rw [simplifyBlock]
    cases s <;>
      (unfold simplifyStmt;
        simp_all [Sem.hoist, simplifyFScope, List.filterMap_cons])

/-- `find?` by first component commutes with mapping a name-preserving function over the list. -/
private theorem find?_simplifyFScope (sc : FScope) (fn : Ident) :
    (simplifyFScope sc).find? (fun p => p.1 == fn)
      = (sc.find? (fun p => p.1 == fn)).map (fun p => (p.1, { p.2 with body := simplifyBlock p.2.body })) := by
  induction sc with
  | nil => rfl
  | cons p rest ih =>
    simp only [simplifyFScope, List.map_cons, List.find?_cons]
    by_cases h : (p.1 == fn) = true <;> (simp [h, simplifyFScope] at ih ⊢) <;> simp_all

/-- `lookupFun` commutes with `simplifyFEnv`: the looked-up declaration has a simplified body and
the returned environment is itself simplified. -/
theorem lookupFun_simplify (funs : FEnv) (fn : Ident) :
    Sem.lookupFun (simplifyFEnv funs) fn
      = (Sem.lookupFun funs fn).map
          (fun p => ({ p.1 with body := simplifyBlock p.1.body }, simplifyFEnv p.2)) := by
  induction funs with
  | nil => rfl
  | cons sc rest ih =>
    rw [simplifyFEnv, List.map_cons, Sem.lookupFun, Sem.lookupFun, find?_simplifyFScope]
    cases h : sc.find? (fun p => p.1 == fn) with
    | none => simp only [h]; simpa [simplifyFEnv] using ih
    | some p => simp [h, simplifyFEnv]

/-- The block a constant `switch` selects commutes with simplification. -/
theorem selectSwitch_simplify (cv : Val) (cases : List (Literal × Block)) (d : Option Block) :
    Sem.selectSwitch cv (simplifyCases cases) (simplifyDefault d)
      = simplifyBlock (Sem.selectSwitch cv cases d) := by
  induction cases with
  | nil => cases d <;> simp [Sem.selectSwitch, simplifyCases, simplifyDefault, simplifyBlock]
  | cons p rest ih =>
    rw [simplifyCases]
    simp only [Sem.selectSwitch, List.find?_cons] at ih ⊢
    cases hb : (cv == litValue p.1) <;> simp_all

/-- `evalRhs` uses the function environment only for `call`; on any other rhs it is independent
of `funs`. -/
theorem evalRhs_funs_irrel (f : Nat) (g g' : FEnv) (env : VEnv) (st : EvmState) (r : Rhs)
    (h : ∀ fn args, r ≠ .call fn args) :
    evalRhs f g env st r = evalRhs f g' env st r := by
  cases r with
  | atom a => simp only [evalRhs]
  | builtin op args => simp only [evalRhs]
  | call fn args => exact absurd rfl (h fn args)

/-- Simplifying a built-in never produces a call (it yields an atom or a built-in). -/
theorem simplifyRhs_builtin_notCall (op : Op) (args : List Atom) :
    ∀ fn as, simplifyRhs (.builtin op args) ≠ .call fn as := by
  intro fn as
  simp only [simplifyRhs, simplifyIdentity]
  repeat' split
  all_goals simp

/-- **Whole-program soundness of `Simplify`** (bundled over the four mutually-recursive
interpreter functions, by strong induction on fuel). Running the simplified program under the
simplified function environment gives exactly the same result as the original. -/
theorem simplify_congr (f : Nat) :
    (∀ funs env st r,
        evalRhs f (simplifyFEnv funs) env st (simplifyRhs r) = evalRhs f funs env st r) ∧
    (∀ funs env st s,
        execStmt f (simplifyFEnv funs) env st (simplifyStmt s) = execStmt f funs env st s) ∧
    (∀ funs env st b,
        execStmts f (simplifyFEnv funs) env st (simplifyBlock b) = execStmts f funs env st b) ∧
    (∀ funs env st post body,
        execLoop f (simplifyFEnv funs) env st (simplifyBlock post) (simplifyBlock body)
          = execLoop f funs env st post body) := by
  induction f using Nat.strong_induction_on with
  | _ f IH =>
    -- (1) right-hand sides: funs matters only for calls
    have hRhs : ∀ funs env st r,
        evalRhs f (simplifyFEnv funs) env st (simplifyRhs r) = evalRhs f funs env st r := by
      intro funs env st r
      cases r with
      | atom a =>
          simp only [simplifyRhs]
          exact evalRhs_funs_irrel f _ _ env st (.atom a) (by simp)
      | builtin op args =>
          rw [evalRhs_funs_irrel f (simplifyFEnv funs) funs env st _
                (simplifyRhs_builtin_notCall op args)]
          exact simplifyRhs_eval f funs env st (.builtin op args)
      | call fn args =>
          cases f with
          | zero => simp only [simplifyRhs, evalRhs]
          | succ n =>
              simp only [simplifyRhs, evalRhs, lookupFun_simplify]
              cases evalAtoms env args with
              | none => rfl
              | some argvals =>
                  cases hl : Sem.lookupFun funs fn with
                  | none => simp [hl]
                  | some p =>
                      obtain ⟨decl, cenv⟩ := p
                      simp only [hl, Option.map_some]
                      have hb := (IH n (Nat.lt_succ_self n)).2.1 cenv
                        (decl.params.zip argvals ++ bindZeros decl.rets) st (.block decl.body)
                      simp only [simplifyStmt] at hb
                      rw [hb]
    -- (2) statements
    have hStmt : ∀ funs env st s,
        execStmt f (simplifyFEnv funs) env st (simplifyStmt s) = execStmt f funs env st s := by
      intro funs env st s
      cases s with
      | funDef n ps rs b => simp only [simplifyStmt, execStmt]
      | «break» => simp only [simplifyStmt, execStmt]
      | «continue» => simp only [simplifyStmt, execStmt]
      | leave => simp only [simplifyStmt, execStmt]
      | letD vars rhs => simp only [simplifyStmt, execStmt]; rw [hRhs funs env st rhs]
      | assign vars rhs => simp only [simplifyStmt, execStmt]; rw [hRhs funs env st rhs]
      | effect rhs => simp only [simplifyStmt, execStmt]; rw [hRhs funs env st rhs]
      | block body =>
          cases f with
          | zero => simp only [simplifyStmt, execStmt]
          | succ n =>
              simp only [simplifyStmt, execStmt, hoist_simplifyBlock, ← simplifyFEnv_cons]
              rw [(IH n (Nat.lt_succ_self n)).2.2.1 (Sem.hoist body :: funs) env st body]
      | cond c body =>
          cases f with
          | zero => simp [simplifyStmt, execStmt]
          | succ n =>
              have hb := (IH n (Nat.lt_succ_self n)).2.1 funs env st (.block body)
              simp only [simplifyStmt] at hb
              simp only [simplifyStmt, execStmt, hb]
      | switch c cases d =>
          cases f with
          | zero => unfold simplifyStmt; simp [execStmt]
          | succ n =>
              unfold simplifyStmt
              simp only [execStmt]
              cases evalAtom env c with
              | none => rfl
              | some cv =>
                  have hb := (IH n (Nat.lt_succ_self n)).2.1 funs env st
                    (.block (Sem.selectSwitch cv cases d))
                  simp only [simplifyStmt] at hb
                  simp only [selectSwitch_simplify, hb]
      | loop post body =>
          cases f with
          | zero => simp only [simplifyStmt, execStmt]
          | succ n =>
              simp only [simplifyStmt, execStmt]
              exact (IH n (Nat.lt_succ_self n)).2.2.2 funs env st post body
    -- (3) statement sequences
    have hStmts : ∀ funs env st b,
        execStmts f (simplifyFEnv funs) env st (simplifyBlock b) = execStmts f funs env st b := by
      intro funs env st b
      cases b with
      | nil => simp [simplifyBlock, execStmts]
      | cons s ss =>
          cases f with
          | zero => simp [simplifyBlock, execStmts]
          | succ n =>
              simp only [simplifyBlock, execStmts]
              rw [(IH n (Nat.lt_succ_self n)).2.1 funs env st s]
              cases execStmt n funs env st s with
              | ok r =>
                  obtain ⟨V1, st1, o⟩ := r
                  cases o <;>
                    first
                      | rfl
                      | exact (IH n (Nat.lt_succ_self n)).2.2.1 funs V1 st1 ss
              | stuck => rfl
              | outOfFuel => rfl
    -- (4) loops
    have hLoop : ∀ funs env st post body,
        execLoop f (simplifyFEnv funs) env st (simplifyBlock post) (simplifyBlock body)
          = execLoop f funs env st post body := by
      intro funs env st post body
      cases f with
      | zero => simp [execLoop]
      | succ n =>
          simp only [execLoop]
          have hbody := (IH n (Nat.lt_succ_self n)).2.1 funs env st (.block body)
          simp only [simplifyStmt] at hbody
          rw [hbody]
          cases execStmt n funs env st (.block body) with
          | ok r =>
              obtain ⟨Vb, stb, o⟩ := r
              cases o with
              | «break» => rfl
              | leave => rfl
              | halt => rfl
              | normal | «continue» =>
                  have hpost := (IH n (Nat.lt_succ_self n)).2.1 funs Vb stb (.block post)
                  simp only [simplifyStmt] at hpost
                  simp only [hpost]
                  cases execStmt n funs Vb stb (.block post) with
                  | ok r2 =>
                      obtain ⟨Vp, stp, o2⟩ := r2
                      cases o2 <;>
                        first
                          | rfl
                          | exact (IH n (Nat.lt_succ_self n)).2.2.2 funs Vp stp post body
                  | stuck => rfl
                  | outOfFuel => rfl
          | stuck => rfl
          | outOfFuel => rfl
    exact ⟨hRhs, hStmt, hStmts, hLoop⟩

/-- **`simplify` preserves the IR semantics.** For any fuel and initial state, running the
simplified program yields exactly the same result as the original (`Sem.run` uses an empty
function environment, and `simplifyFEnv [] = []`). -/
theorem simplify_run_eq (fuel : Nat) (prog : Block) (st0 : EvmState) :
    Sem.run fuel (simplifyBlock prog) st0 = Sem.run fuel prog st0 := by
  have h := (simplify_congr fuel).2.1 [] [] st0 (.block prog)
  simpa [Sem.run, simplifyStmt, simplifyFEnv] using h

end YulIR
