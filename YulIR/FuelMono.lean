import YulIR.Semantics

set_option linter.unusedSimpArgs false

/-!
# YulIR.FuelMono — fuel monotonicity of the IR interpreter

The interpreter's `fuel` is only a termination bound: once a run produces a *determined* result
(anything other than `outOfFuel`), giving it more fuel cannot change that result. This is the
foundation for the *observational* soundness of every structure-changing optimization (unlike the
structure-preserving `Simplify`, passes such as `structural` change the number of statements, so
they only agree with the original at *sufficient* fuel — which this lemma makes precise).

Stated as a disjunction — a `+1` step either leaves the result unchanged or the original was
`outOfFuel` — so every recursive case just `rcases` the inductive hypothesis. `fuel_mono` lifts it
to any `f ≤ f'`.
-/

namespace YulIR

open YulSemantics YulSemantics.EVM
open YulIR.Sem

/-- **One-step fuel monotonicity** (bundled over the four mutually-recursive interpreter
functions, by strong induction on fuel). -/
theorem fuel_mono_succ (f : Nat) :
    (∀ funs env st r,
        evalRhs (f + 1) funs env st r = evalRhs f funs env st r
          ∨ evalRhs f funs env st r = .outOfFuel) ∧
    (∀ funs env st s,
        execStmt (f + 1) funs env st s = execStmt f funs env st s
          ∨ execStmt f funs env st s = .outOfFuel) ∧
    (∀ funs env st b,
        execStmts (f + 1) funs env st b = execStmts f funs env st b
          ∨ execStmts f funs env st b = .outOfFuel) ∧
    (∀ funs env st post body,
        execLoop (f + 1) funs env st post body = execLoop f funs env st post body
          ∨ execLoop f funs env st post body = .outOfFuel) := by
  induction f using Nat.strong_induction_on with
  | _ f IH =>
    -- (1) right-hand sides
    have hRhs : ∀ funs env st r,
        evalRhs (f + 1) funs env st r = evalRhs f funs env st r
          ∨ evalRhs f funs env st r = .outOfFuel := by
      intro funs env st r
      cases r with
      | atom a => exact Or.inl (by simp only [evalRhs])
      | builtin op args => exact Or.inl (by simp only [evalRhs])
      | call fn args =>
          cases f with
          | zero => exact Or.inr (by simp only [evalRhs])
          | succ n =>
              simp only [evalRhs]
              cases evalAtoms env args with
              | none => exact Or.inl rfl
              | some argvals =>
                  cases hl : Sem.lookupFun funs fn with
                  | none => exact Or.inl rfl
                  | some p =>
                      obtain ⟨decl, cenv⟩ := p
                      by_cases hlen : (argvals.length == decl.params.length) = true
                      · rcases (IH n (Nat.lt_succ_self n)).2.1 cenv
                          (decl.params.zip argvals ++ bindZeros decl.rets) st (.block decl.body)
                          with h | h
                        · left;  simp only [hlen, if_true, h]
                        · right; simp only [hlen, if_true, h]
                      · exact Or.inl (by simp [hlen])
    -- (2) statements
    have hStmt : ∀ funs env st s,
        execStmt (f + 1) funs env st s = execStmt f funs env st s
          ∨ execStmt f funs env st s = .outOfFuel := by
      intro funs env st s
      cases s with
      | funDef n ps rs b => exact Or.inl (by simp only [execStmt])
      | «break» => exact Or.inl (by simp only [execStmt])
      | «continue» => exact Or.inl (by simp only [execStmt])
      | leave => exact Or.inl (by simp only [execStmt])
      | letD vars rhs =>
          rcases hRhs funs env st rhs with h | h
          · left;  simp only [execStmt, h]
          · right; simp only [execStmt, h]
      | assign vars rhs =>
          rcases hRhs funs env st rhs with h | h
          · left;  simp only [execStmt, h]
          · right; simp only [execStmt, h]
      | effect rhs =>
          rcases hRhs funs env st rhs with h | h
          · left;  simp only [execStmt, h]
          · right; simp only [execStmt, h]
      | block body =>
          cases f with
          | zero => exact Or.inr (by simp only [execStmt])
          | succ n =>
              rcases (IH n (Nat.lt_succ_self n)).2.2.1 (Sem.hoist body :: funs) env st body
                with h | h
              · left;  simp only [execStmt, h]
              · right; simp only [execStmt, h]
      | cond c body =>
          cases f with
          | zero =>
              simp only [execStmt]
              cases evalAtom env c with
              | none => simp
              | some cv => left; by_cases hcv : cv = 0#256 <;> simp [hcv]
          | succ n =>
              simp only [execStmt]
              cases evalAtom env c with
              | none => simp
              | some cv =>
                  by_cases hcv : cv = 0#256
                  · left; simp [hcv]
                  · rcases (IH n (Nat.lt_succ_self n)).2.1 funs env st (.block body) with h | h
                    · left;  simp only [execStmt] at h; simp [hcv, h]
                    · right; simp [hcv, h]
      | switch c cases d =>
          cases f with
          | zero =>
              simp only [execStmt]
              cases evalAtom env c with
              | none => simp
              | some cv => left; simp
          | succ n =>
              simp only [execStmt]
              cases evalAtom env c with
              | none => simp
              | some cv =>
                  rcases (IH n (Nat.lt_succ_self n)).2.1 funs env st
                    (.block (Sem.selectSwitch cv cases d)) with h | h
                  · left;  simp only [execStmt] at h; simp [h]
                  · right; simp [h]
      | loop post body =>
          cases f with
          | zero => exact Or.inr (by simp only [execStmt])
          | succ n =>
              rcases (IH n (Nat.lt_succ_self n)).2.2.2 funs env st post body with h | h
              · left;  simp only [execStmt, h]
              · right; simp only [execStmt, h]
    -- (3) statement sequences
    have hStmts : ∀ funs env st b,
        execStmts (f + 1) funs env st b = execStmts f funs env st b
          ∨ execStmts f funs env st b = .outOfFuel := by
      intro funs env st b
      cases b with
      | nil => exact Or.inl (by simp only [execStmts])
      | cons s ss =>
          cases f with
          | zero => exact Or.inr (by simp only [execStmts])
          | succ n =>
              simp only [execStmts]
              rcases (IH n (Nat.lt_succ_self n)).2.1 funs env st s with hs | hs
              · simp only [hs]
                cases hr : execStmt n funs env st s with
                | ok r =>
                    obtain ⟨V1, st1, o⟩ := r
                    cases o <;>
                      first
                        | exact Or.inl rfl
                        | exact (IH n (Nat.lt_succ_self n)).2.2.1 funs V1 st1 ss
                | stuck => exact Or.inl rfl
                | outOfFuel => exact Or.inl rfl
              · right; simp only [hs]
    -- (4) loops
    have hLoop : ∀ funs env st post body,
        execLoop (f + 1) funs env st post body = execLoop f funs env st post body
          ∨ execLoop f funs env st post body = .outOfFuel := by
      intro funs env st post body
      cases f with
      | zero => exact Or.inr (by simp only [execLoop])
      | succ n =>
          simp only [execLoop]
          rcases (IH n (Nat.lt_succ_self n)).2.1 funs env st (.block body) with hb | hb
          · simp only [hb]
            cases hr : execStmt n funs env st (.block body) with
            | ok r =>
                obtain ⟨Vb, stb, o⟩ := r
                cases o with
                | «break» => exact Or.inl rfl
                | leave => exact Or.inl rfl
                | halt => exact Or.inl rfl
                | normal | «continue» =>
                    rcases (IH n (Nat.lt_succ_self n)).2.1 funs Vb stb (.block post) with hp | hp
                    · simp only [hp]
                      cases hr2 : execStmt n funs Vb stb (.block post) with
                      | ok r2 =>
                          obtain ⟨Vp, stp, o2⟩ := r2
                          cases o2 with
                          | «break» => exact Or.inl rfl
                          | leave => exact Or.inl rfl
                          | «continue» => exact Or.inl rfl
                          | halt => exact Or.inl rfl
                          | normal =>
                              have hrec := (IH n (Nat.lt_succ_self n)).2.2.2 funs Vp stp post body
                              simp only [execLoop] at hrec
                              exact hrec
                      | stuck => exact Or.inl rfl
                      | outOfFuel => exact Or.inl rfl
                    · right; simp only [hp]
            | stuck => exact Or.inl rfl
            | outOfFuel => exact Or.inl rfl
          · right; simp only [hb]
    exact ⟨hRhs, hStmt, hStmts, hLoop⟩

/-- **Fuel monotonicity** for statements: a determined result is preserved by any amount of extra
fuel. -/
theorem execStmt_fuel_mono {f f' : Nat} (hle : f ≤ f') {funs env st s r}
    (h : execStmt f funs env st s = r) (hr : r ≠ .outOfFuel) :
    execStmt f' funs env st s = r := by
  induction hle with
  | refl => exact h
  | step _ ih =>
      rename_i m _
      rcases (fuel_mono_succ m).2.1 funs env st s with hm | hm
      · rw [hm]; exact ih
      · rw [ih] at hm; exact absurd hm hr

end YulIR
