import YulSemantics.Equiv
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.EmptyScope

Inserting **empty function scopes** into the function environment does not change
evaluation. This is the specialization of the function-environment congruence
(`FunCongr.lean`) that a block-scoped rewrite needs: wrapping a group of
straight-line statements in a fresh `.block` makes them execute under
`hoist D body :: funs`, and when `body` declares no functions `hoist D body = []`,
so the body runs under `[] :: funs`. To relate that execution to one under `funs`
we need exactly "an empty scope is transparent".

`EmptyExt f₁ f₂` holds when `f₂` is `f₁` with zero or more empty scopes inserted
anywhere. It is reflexive, closed under prepending a common scope, and — crucially
— empty scopes never satisfy a `lookupFun`, so a resolved function has the *same*
declaration on both sides (no body rewriting, unlike `FunsRel`) with `EmptyExt`-
related closure environments. `Step.emptyExt_congr` / `Step.emptyExt_congr'`
transport a derivation in both directions.

Generic Yul meta-theory; used only to discharge a pass's `Sound` obligation.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-- `f₂` is `f₁` with zero or more empty function scopes inserted. -/
inductive EmptyExt (D : Dialect) [DecidableEq D.Value] : FunEnv D → FunEnv D → Prop
  | nil : EmptyExt D [] []
  | cons (s : FScope D) {f₁ f₂} : EmptyExt D f₁ f₂ → EmptyExt D (s :: f₁) (s :: f₂)
  | empty {f₁ f₂} : EmptyExt D f₁ f₂ → EmptyExt D f₁ ([] :: f₂)

/-- Every environment relates to itself (insert no empty scopes). -/
theorem EmptyExt.refl : ∀ (f : FunEnv D), EmptyExt D f f
  | [] => .nil
  | s :: rest => .cons s (EmptyExt.refl rest)

/-- Prepending one empty scope. -/
theorem EmptyExt.head (f : FunEnv D) : EmptyExt D f ([] :: f) := .empty (EmptyExt.refl f)

/-! ### `lookupFun` transport

Empty scopes are skipped by `lookupFun`, so a name resolves to the *same*
declaration on both sides, with `EmptyExt`-related closure environments. -/

theorem lookupFun_emptyExt_fwd {f₁ f₂ : FunEnv D} (hE : EmptyExt D f₁ f₂) :
    ∀ {fn decl cenv₁}, lookupFun f₁ fn = some (decl, cenv₁) →
      ∃ cenv₂, lookupFun f₂ fn = some (decl, cenv₂) ∧ EmptyExt D cenv₁ cenv₂ := by
  induction hE with
  | nil => intro fn decl cenv₁ h; simp [lookupFun] at h
  | @cons s f₁ f₂ hE' ih =>
      intro fn decl cenv₁ h
      unfold lookupFun at h ⊢
      cases hfind : s.find? (fun p => p.1 = fn) with
      | some p =>
          rw [hfind] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hd, hc⟩ := h; subst hd; subst hc
          exact ⟨s :: f₂, rfl, .cons s hE'⟩
      | none =>
          rw [hfind] at h
          obtain ⟨cenv₂, hl, hEc⟩ := ih h
          exact ⟨cenv₂, hl, hEc⟩
  | @empty f₁ f₂ hE' ih =>
      intro fn decl cenv₁ h
      obtain ⟨cenv₂, hl, hEc⟩ := ih h
      exact ⟨cenv₂, by unfold lookupFun; simpa using hl, hEc⟩

theorem lookupFun_emptyExt_bwd {f₁ f₂ : FunEnv D} (hE : EmptyExt D f₁ f₂) :
    ∀ {fn decl cenv₂}, lookupFun f₂ fn = some (decl, cenv₂) →
      ∃ cenv₁, lookupFun f₁ fn = some (decl, cenv₁) ∧ EmptyExt D cenv₁ cenv₂ := by
  induction hE with
  | nil => intro fn decl cenv₂ h; simp [lookupFun] at h
  | @cons s f₁ f₂ hE' ih =>
      intro fn decl cenv₂ h
      unfold lookupFun at h ⊢
      cases hfind : s.find? (fun p => p.1 = fn) with
      | some p =>
          rw [hfind] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hd, hc⟩ := h; subst hd; subst hc
          exact ⟨s :: f₁, rfl, .cons s hE'⟩
      | none =>
          rw [hfind] at h
          obtain ⟨cenv₁, hl, hEc⟩ := ih h
          exact ⟨cenv₁, hl, hEc⟩
  | @empty f₁ f₂ hE' ih =>
      intro fn decl cenv₂ h
      have h' : lookupFun f₂ fn = some (decl, cenv₂) := by unfold lookupFun at h; simpa using h
      exact ih h'

/-! ### The congruence -/

/-- **Forward.** A derivation under `f₁` transports to one under any environment
with extra empty scopes. -/
theorem Step.emptyExt_congr {funs₁ : FunEnv D} {V st code res}
    (h : Step D funs₁ V st code res) :
    ∀ {funs₂}, EmptyExt D funs₁ funs₂ → Step D funs₂ V st code res := by
  induction h with
  | lit => intro _ _; exact Step.lit
  | var hv => intro _ _; exact Step.var hv
  | builtinOk _ hb iha => intro _ hE; exact Step.builtinOk (iha hE) hb
  | builtinHalt _ hb iha => intro _ hE; exact Step.builtinHalt (iha hE) hb
  | builtinArgsHalt _ iha => intro _ hE; exact Step.builtinArgsHalt (iha hE)
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hl hlen hbody ho iha ihbody =>
      intro funs₂ hE
      obtain ⟨cenv₂, hl', hEc⟩ := lookupFun_emptyExt_fwd hE hl
      exact Step.callOk (iha hE) hl' hlen (ihbody hEc) ho
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hl hlen hbody iha ihbody =>
      intro funs₂ hE
      obtain ⟨cenv₂, hl', hEc⟩ := lookupFun_emptyExt_fwd hE hl
      exact Step.callHalt (iha hE) hl' hlen (ihbody hEc)
  | callArgsHalt _ iha => intro _ hE; exact Step.callArgsHalt (iha hE)
  | argsNil => intro _ _; exact Step.argsNil
  | argsCons _ _ iha ihe => intro _ hE; exact Step.argsCons (iha hE) (ihe hE)
  | argsRestHalt _ iha => intro _ hE; exact Step.argsRestHalt (iha hE)
  | argsHeadHalt _ _ iha ihe => intro _ hE; exact Step.argsHeadHalt (iha hE) (ihe hE)
  | funDef => intro _ _; exact Step.funDef
  | @block funs V st body Vb stb o hbody ihbody =>
      intro funs₂ hE; exact Step.block (ihbody (.cons (hoist D body) hE))
  | letZero => intro _ _; exact Step.letZero
  | letVal _ hlen ihe => intro _ hE; exact Step.letVal (ihe hE) hlen
  | letHalt _ ihe => intro _ hE; exact Step.letHalt (ihe hE)
  | assignVal _ hlen ihe => intro _ hE; exact Step.assignVal (ihe hE) hlen
  | assignHalt _ ihe => intro _ hE; exact Step.assignHalt (ihe hE)
  | exprStmt _ ihe => intro _ hE; exact Step.exprStmt (ihe hE)
  | exprStmtHalt _ ihe => intro _ hE; exact Step.exprStmtHalt (ihe hE)
  | ifTrue _ hnz _ ihc ihb => intro _ hE; exact Step.ifTrue (ihc hE) hnz (ihb hE)
  | ifFalse _ hz ihc => intro _ hE; exact Step.ifFalse (ihc hE) hz
  | ifHalt _ ihc => intro _ hE; exact Step.ifHalt (ihc hE)
  | switchExec _ _ ihc ihb => intro _ hE; exact Step.switchExec (ihc hE) (ihb hE)
  | switchHalt _ ihc => intro _ hE; exact Step.switchHalt (ihc hE)
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs₂ hE
      exact Step.forLoop (ihinit (.cons (hoist D init) hE)) (ihloop (.cons (hoist D init) hE))
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro funs₂ hE
      exact Step.forInitHalt (ihinit (.cons (hoist D init) hE))
  | «break» => intro _ _; exact Step.break
  | «continue» => intro _ _; exact Step.continue
  | leave => intro _ _; exact Step.leave
  | seqNil => intro _ _; exact Step.seqNil
  | seqCons _ _ ihs ihrest => intro _ hE; exact Step.seqCons (ihs hE) (ihrest hE)
  | seqStop _ hne ihs => intro _ hE; exact Step.seqStop (ihs hE) hne
  | loopDone _ hz ihc => intro _ hE; exact Step.loopDone (ihc hE) hz
  | loopCondHalt _ ihc => intro _ hE; exact Step.loopCondHalt (ihc hE)
  | loopStep _ hnz _ hob _ _ ihc ihb ihp ihr =>
      intro _ hE; exact Step.loopStep (ihc hE) hnz (ihb hE) hob (ihp hE) (ihr hE)
  | loopPostHalt _ hnz _ hob _ ihc ihb ihp =>
      intro _ hE; exact Step.loopPostHalt (ihc hE) hnz (ihb hE) hob (ihp hE)
  | loopBreak _ hnz _ ihc ihb => intro _ hE; exact Step.loopBreak (ihc hE) hnz (ihb hE)
  | loopLeave _ hnz _ ihc ihb => intro _ hE; exact Step.loopLeave (ihc hE) hnz (ihb hE)
  | loopBodyHalt _ hnz _ ihc ihb => intro _ hE; exact Step.loopBodyHalt (ihc hE) hnz (ihb hE)

/-- **Backward.** A derivation under an environment with extra empty scopes
transports back to one under `f₁`. -/
theorem Step.emptyExt_congr' {funs₂ : FunEnv D} {V st code res}
    (h : Step D funs₂ V st code res) :
    ∀ {funs₁}, EmptyExt D funs₁ funs₂ → Step D funs₁ V st code res := by
  induction h with
  | lit => intro _ _; exact Step.lit
  | var hv => intro _ _; exact Step.var hv
  | builtinOk _ hb iha => intro _ hE; exact Step.builtinOk (iha hE) hb
  | builtinHalt _ hb iha => intro _ hE; exact Step.builtinHalt (iha hE) hb
  | builtinArgsHalt _ iha => intro _ hE; exact Step.builtinArgsHalt (iha hE)
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hl hlen hbody ho iha ihbody =>
      intro funs₁ hE
      obtain ⟨cenv₁, hl', hEc⟩ := lookupFun_emptyExt_bwd hE hl
      exact Step.callOk (iha hE) hl' hlen (ihbody hEc) ho
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hl hlen hbody iha ihbody =>
      intro funs₁ hE
      obtain ⟨cenv₁, hl', hEc⟩ := lookupFun_emptyExt_bwd hE hl
      exact Step.callHalt (iha hE) hl' hlen (ihbody hEc)
  | callArgsHalt _ iha => intro _ hE; exact Step.callArgsHalt (iha hE)
  | argsNil => intro _ _; exact Step.argsNil
  | argsCons _ _ iha ihe => intro _ hE; exact Step.argsCons (iha hE) (ihe hE)
  | argsRestHalt _ iha => intro _ hE; exact Step.argsRestHalt (iha hE)
  | argsHeadHalt _ _ iha ihe => intro _ hE; exact Step.argsHeadHalt (iha hE) (ihe hE)
  | funDef => intro _ _; exact Step.funDef
  | @block funs V st body Vb stb o hbody ihbody =>
      intro funs₁ hE; exact Step.block (ihbody (.cons (hoist D body) hE))
  | letZero => intro _ _; exact Step.letZero
  | letVal _ hlen ihe => intro _ hE; exact Step.letVal (ihe hE) hlen
  | letHalt _ ihe => intro _ hE; exact Step.letHalt (ihe hE)
  | assignVal _ hlen ihe => intro _ hE; exact Step.assignVal (ihe hE) hlen
  | assignHalt _ ihe => intro _ hE; exact Step.assignHalt (ihe hE)
  | exprStmt _ ihe => intro _ hE; exact Step.exprStmt (ihe hE)
  | exprStmtHalt _ ihe => intro _ hE; exact Step.exprStmtHalt (ihe hE)
  | ifTrue _ hnz _ ihc ihb => intro _ hE; exact Step.ifTrue (ihc hE) hnz (ihb hE)
  | ifFalse _ hz ihc => intro _ hE; exact Step.ifFalse (ihc hE) hz
  | ifHalt _ ihc => intro _ hE; exact Step.ifHalt (ihc hE)
  | switchExec _ _ ihc ihb => intro _ hE; exact Step.switchExec (ihc hE) (ihb hE)
  | switchHalt _ ihc => intro _ hE; exact Step.switchHalt (ihc hE)
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs₁ hE
      exact Step.forLoop (ihinit (.cons (hoist D init) hE)) (ihloop (.cons (hoist D init) hE))
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro funs₁ hE
      exact Step.forInitHalt (ihinit (.cons (hoist D init) hE))
  | «break» => intro _ _; exact Step.break
  | «continue» => intro _ _; exact Step.continue
  | leave => intro _ _; exact Step.leave
  | seqNil => intro _ _; exact Step.seqNil
  | seqCons _ _ ihs ihrest => intro _ hE; exact Step.seqCons (ihs hE) (ihrest hE)
  | seqStop _ hne ihs => intro _ hE; exact Step.seqStop (ihs hE) hne
  | loopDone _ hz ihc => intro _ hE; exact Step.loopDone (ihc hE) hz
  | loopCondHalt _ ihc => intro _ hE; exact Step.loopCondHalt (ihc hE)
  | loopStep _ hnz _ hob _ _ ihc ihb ihp ihr =>
      intro _ hE; exact Step.loopStep (ihc hE) hnz (ihb hE) hob (ihp hE) (ihr hE)
  | loopPostHalt _ hnz _ hob _ ihc ihb ihp =>
      intro _ hE; exact Step.loopPostHalt (ihc hE) hnz (ihb hE) hob (ihp hE)
  | loopBreak _ hnz _ ihc ihb => intro _ hE; exact Step.loopBreak (ihc hE) hnz (ihb hE)
  | loopLeave _ hnz _ ihc ihb => intro _ hE; exact Step.loopLeave (ihc hE) hnz (ihb hE)
  | loopBodyHalt _ hnz _ ihc ihb => intro _ hE; exact Step.loopBodyHalt (ihc hE) hnz (ihb hE)

/-- Prepending a **funDef-free** block body's hoisted scope is transparent: it is
the empty scope. Both directions of the resulting `.stmts` equivalence. -/
theorem step_emptyScope_iff {funs : FunEnv D} {V st ss res} :
    Step D ([] :: funs) V st (.stmts ss) res ↔ Step D funs V st (.stmts ss) res :=
  ⟨fun h => Step.emptyExt_congr' h (EmptyExt.head funs),
   fun h => Step.emptyExt_congr h (EmptyExt.head funs)⟩

end YulEvmCompiler.Optimizer
