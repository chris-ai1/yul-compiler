import YulEvmCompiler.Optimizer.Implementation.Normalization.HoistFunDefsEquiv
import YulEvmCompiler.Optimizer.Implementation.Normalization.NormalForm
import YulEvmCompiler.Optimizer.Spec.GlobalPass

/-!
# Function hoisting as a verified `GlobalPass`

Wraps the proven whole-program hoisting transform `liftFunDefs` (see
`Normalization/HoistFunDefsEquiv.lean`, theorem `liftFunDefs_run_equiv`) as a sound
`Optimizer.GlobalPass`.

`liftFunDefs` is semantics-preserving only when the program's function names are
**globally unique** (disambiguated) *and* it is **well scoped** — under those
assumptions hoisting every function to the top block changes no name resolution.
A `GlobalPass` must be *unconditionally* sound, so the pass **guards**: it applies
`liftFunDefs` exactly on inputs it can decide are unique-and-well-scoped, and is
the identity otherwise. Soundness is therefore total; on disambiguated,
well-scoped input the pass really does hoist. The guard is decided by the `Bool`
mirror of the `Scoped*` predicates (`wellScopedB`, sound by `wellScopedB_sound`)
together with the decidable `UniqueFunNames` (`Nodup`).
-/

namespace YulEvmCompiler.Optimizer.Normalization

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### A decidable mirror of well-scopedness -/

mutual
def scopedExprB (scope : List Ident) : Expr D.Op → Bool
  | .lit _ => true
  | .var _ => true
  | .builtin _ args => scopedArgsB scope args
  | .call f args => decide (f ∈ scope) && scopedArgsB scope args
def scopedArgsB (scope : List Ident) : List (Expr D.Op) → Bool
  | [] => true
  | e :: rest => scopedExprB scope e && scopedArgsB scope rest
end

mutual
def scopedStmtB (scope : List Ident) : Stmt D.Op → Bool
  | .funDef _ _ _ body => scopedStmtsB (funNamesTop body ++ scope) body
  | .block b => scopedStmtsB (funNamesTop b ++ scope) b
  | .cond c b => scopedExprB scope c && scopedStmtsB (funNamesTop b ++ scope) b
  | .switch c cases dflt =>
      scopedExprB scope c && scopedCasesB scope cases && scopedDfltB scope dflt
  | .forLoop init c post body =>
      scopedStmtsB (funNamesTop init ++ scope) init &&
      scopedExprB (funNamesTop init ++ scope) c &&
      scopedStmtsB (funNamesTop post ++ (funNamesTop init ++ scope)) post &&
      scopedStmtsB (funNamesTop body ++ (funNamesTop init ++ scope)) body
  | .letDecl _ val => match val with | none => true | some e => scopedExprB scope e
  | .assign _ e => scopedExprB scope e
  | .exprStmt e => scopedExprB scope e
  | .break => true
  | .continue => true
  | .leave => true
def scopedStmtsB (scope : List Ident) : List (Stmt D.Op) → Bool
  | [] => true
  | s :: rest => scopedStmtB scope s && scopedStmtsB scope rest
def scopedCasesB (scope : List Ident) : List (Literal × Block D.Op) → Bool
  | [] => true
  | (_, b) :: rest => scopedStmtsB (funNamesTop b ++ scope) b && scopedCasesB scope rest
def scopedDfltB (scope : List Ident) : Option (Block D.Op) → Bool
  | none => true
  | some b => scopedStmtsB (funNamesTop b ++ scope) b
end

/-- Decidable well-scopedness check. -/
def wellScopedB (b : Block D.Op) : Bool := scopedStmtsB (funNamesTop b) b

/-! ### Soundness of the mirror (`= true → Prop`) -/

mutual
theorem scopedExprB_sound : ∀ {scope : List Ident} (e : Expr D.Op),
    scopedExprB scope e = true → ScopedExpr scope e
  | _, .lit _, _ => by simp only [ScopedExpr]
  | _, .var _, _ => by simp only [ScopedExpr]
  | _, .builtin _ args, h => by
      simp only [scopedExprB] at h; simp only [ScopedExpr]; exact scopedArgsB_sound args h
  | _, .call _ args, h => by
      simp only [scopedExprB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [ScopedExpr]; exact ⟨h.1, scopedArgsB_sound args h.2⟩
theorem scopedArgsB_sound : ∀ {scope : List Ident} (es : List (Expr D.Op)),
    scopedArgsB scope es = true → ScopedArgs scope es
  | _, [], _ => by simp only [ScopedArgs]
  | _, e :: rest, h => by
      simp only [scopedArgsB, Bool.and_eq_true] at h
      simp only [ScopedArgs]; exact ⟨scopedExprB_sound e h.1, scopedArgsB_sound rest h.2⟩
end

mutual
theorem scopedStmtB_sound : ∀ {scope : List Ident} (s : Stmt D.Op),
    scopedStmtB scope s = true → ScopedStmt scope s
  | _, .funDef _ _ _ body, h => by
      simp only [scopedStmtB] at h; simp only [ScopedStmt]; exact scopedStmtsB_sound body h
  | _, .block b, h => by
      simp only [scopedStmtB] at h; simp only [ScopedStmt]; exact scopedStmtsB_sound b h
  | _, .cond c b, h => by
      simp only [scopedStmtB, Bool.and_eq_true] at h
      simp only [ScopedStmt]; exact ⟨scopedExprB_sound c h.1, scopedStmtsB_sound b h.2⟩
  | _, .switch c cases dflt, h => by
      simp only [scopedStmtB, Bool.and_eq_true] at h
      simp only [ScopedStmt]
      exact ⟨scopedExprB_sound c h.1.1, scopedCasesB_sound cases h.1.2, scopedDfltB_sound dflt h.2⟩
  | _, .forLoop init c post body, h => by
      simp only [scopedStmtB, Bool.and_eq_true] at h
      simp only [ScopedStmt]
      exact ⟨scopedStmtsB_sound init h.1.1.1, scopedExprB_sound c h.1.1.2,
        scopedStmtsB_sound post h.1.2, scopedStmtsB_sound body h.2⟩
  | _, .letDecl _ val, h => by
      cases val with
      | none => simp only [ScopedStmt]
      | some e => simp only [scopedStmtB] at h; simp only [ScopedStmt]; exact scopedExprB_sound e h
  | _, .assign _ e, h => by
      simp only [scopedStmtB] at h; simp only [ScopedStmt]; exact scopedExprB_sound e h
  | _, .exprStmt e, h => by
      simp only [scopedStmtB] at h; simp only [ScopedStmt]; exact scopedExprB_sound e h
  | _, .break, _ => by simp only [ScopedStmt]
  | _, .continue, _ => by simp only [ScopedStmt]
  | _, .leave, _ => by simp only [ScopedStmt]
theorem scopedStmtsB_sound : ∀ {scope : List Ident} (ss : List (Stmt D.Op)),
    scopedStmtsB scope ss = true → ScopedStmts scope ss
  | _, [], _ => by simp only [ScopedStmts]
  | _, s :: rest, h => by
      simp only [scopedStmtsB, Bool.and_eq_true] at h
      simp only [ScopedStmts]; exact ⟨scopedStmtB_sound s h.1, scopedStmtsB_sound rest h.2⟩
theorem scopedCasesB_sound : ∀ {scope : List Ident} (cs : List (Literal × Block D.Op)),
    scopedCasesB scope cs = true → ScopedCases scope cs
  | _, [], _ => by simp only [ScopedCases]
  | _, (_, b) :: rest, h => by
      simp only [scopedCasesB, Bool.and_eq_true] at h
      simp only [ScopedCases]; exact ⟨scopedStmtsB_sound b h.1, scopedCasesB_sound rest h.2⟩
theorem scopedDfltB_sound : ∀ {scope : List Ident} (d : Option (Block D.Op)),
    scopedDfltB scope d = true → ScopedDflt scope d
  | _, none, _ => by simp only [ScopedDflt]
  | _, some b, h => by simp only [scopedDfltB] at h; simp only [ScopedDflt]; exact scopedStmtsB_sound b h
end

theorem wellScopedB_sound {b : Block D.Op} (h : wellScopedB b = true) : WellScoped b :=
  scopedStmtsB_sound b h

/-! ### The guard and the pass -/

instance {b : Block D.Op} : Decidable (UniqueFunNames b) := by
  unfold UniqueFunNames; infer_instance

/-- Decidable guard implying the hypotheses of `liftFunDefs_run_equiv`. -/
def hoistGuard (b : Block D.Op) : Bool := decide (UniqueFunNames b) && wellScopedB b

theorem hoistGuard_sound {b : Block D.Op} (h : hoistGuard b = true) :
    UniqueFunNames b ∧ WellScoped b := by
  rw [hoistGuard, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, wellScopedB_sound h.2⟩

/-- The per-block transform: hoist all function definitions to the top **when**
the block is unique and well scoped, otherwise leave it unchanged. -/
def hoistBlock : Block D.Op → Block D.Op := guardedBlock hoistGuard liftFunDefs

/-- **Function hoisting as a verified global pass.** Applies `liftFunDefs` to
every code block of an object tree wherever the block is disambiguated and well
scoped; sound unconditionally (via the `ofGuardedBlock` combinator). -/
def hoistFunDefsPass : GlobalPass D :=
  GlobalPass.ofGuardedBlock hoistGuard liftFunDefs
    (fun _ hg _ _ _ _ => liftFunDefs_run_equiv (hoistGuard_sound hg).1 (hoistGuard_sound hg).2)

@[simp] theorem hoistFunDefsPass_run (o : Object D.Op) :
    (hoistFunDefsPass (D := D)).run o = mapObjCode hoistBlock o := rfl

/-! ### Postcondition: the output is function-hoisted (a `NormalForm` property)

`liftFunDefs` unconditionally produces a block in which every function definition
sits at the top level with a definition-free body — `NormalForm.FunctionsHoisted`.
(Unlike *soundness*, this syntactic property needs no disambiguation.) -/

/- The stripped block contains no function definition anywhere. -/
mutual
theorem noFunDef_stripStmts : ∀ (b : List (Stmt D.Op)), NormalForm.NoFunDefStmts (stripStmts b)
  | [] => trivial
  | s :: rest => by
      cases s with
      | funDef n ps rs body =>
          simp only [stripStmts]; exact noFunDef_stripStmts rest
      | block bb =>
          simp only [stripStmts, stripStmt, NormalForm.NoFunDefStmts, NormalForm.NoFunDefStmt]
          exact ⟨noFunDef_stripStmts bb, noFunDef_stripStmts rest⟩
      | cond c bb =>
          simp only [stripStmts, stripStmt, NormalForm.NoFunDefStmts, NormalForm.NoFunDefStmt]
          exact ⟨noFunDef_stripStmts bb, noFunDef_stripStmts rest⟩
      | switch c cases dflt =>
          simp only [stripStmts, stripStmt, NormalForm.NoFunDefStmts, NormalForm.NoFunDefStmt]
          exact ⟨⟨noFunDef_stripCases cases, noFunDef_stripDflt dflt⟩, noFunDef_stripStmts rest⟩
      | forLoop init c post body =>
          simp only [stripStmts, stripStmt, NormalForm.NoFunDefStmts, NormalForm.NoFunDefStmt]
          exact ⟨⟨noFunDef_stripStmts init, noFunDef_stripStmts post, noFunDef_stripStmts body⟩,
            noFunDef_stripStmts rest⟩
      | letDecl vs v =>
          simp only [stripStmts, stripStmt, NormalForm.NoFunDefStmts, NormalForm.NoFunDefStmt,
            true_and]
          exact noFunDef_stripStmts rest
      | assign vs e =>
          simp only [stripStmts, stripStmt, NormalForm.NoFunDefStmts, NormalForm.NoFunDefStmt,
            true_and]
          exact noFunDef_stripStmts rest
      | exprStmt e =>
          simp only [stripStmts, stripStmt, NormalForm.NoFunDefStmts, NormalForm.NoFunDefStmt,
            true_and]
          exact noFunDef_stripStmts rest
      | «break» =>
          simp only [stripStmts, stripStmt, NormalForm.NoFunDefStmts, NormalForm.NoFunDefStmt,
            true_and]
          exact noFunDef_stripStmts rest
      | «continue» =>
          simp only [stripStmts, stripStmt, NormalForm.NoFunDefStmts, NormalForm.NoFunDefStmt,
            true_and]
          exact noFunDef_stripStmts rest
      | leave =>
          simp only [stripStmts, stripStmt, NormalForm.NoFunDefStmts, NormalForm.NoFunDefStmt,
            true_and]
          exact noFunDef_stripStmts rest
theorem noFunDef_stripCases : ∀ (cs : List (Literal × Block D.Op)),
    NormalForm.NoFunDefCases (stripCases cs)
  | [] => trivial
  | (_, b) :: rest => by
      simp only [stripCases, NormalForm.NoFunDefCases]
      exact ⟨noFunDef_stripStmts b, noFunDef_stripCases rest⟩
theorem noFunDef_stripDflt : ∀ (d : Option (Block D.Op)), NormalForm.NoFunDefDflt (stripDflt d)
  | none => trivial
  | some b => by simp only [stripDflt, NormalForm.NoFunDefDflt]; exact noFunDef_stripStmts b
end

/-- Membership extraction from `NoFunDefStmts`. -/
theorem noFunDefStmt_of_mem : ∀ {ss : List (Stmt D.Op)}, NormalForm.NoFunDefStmts ss →
    ∀ {s}, s ∈ ss → NormalForm.NoFunDefStmt s
  | [], _, _, hs => by simp at hs
  | _ :: rest, h, s, hs => by
      simp only [NormalForm.NoFunDefStmts] at h
      rcases List.mem_cons.mp hs with rfl | hs
      · exact h.1
      · exact noFunDefStmt_of_mem h.2 hs

/- Every statement `collectStmt` emits is function-hoisted (a top funDef whose
body — a `stripStmts` — is definition-free). -/
mutual
theorem hoistedTop_collectStmt : ∀ (s : Stmt D.Op), ∀ x ∈ collectStmt s, NormalForm.HoistedTop x
  | .funDef n ps rs body, x, hx => by
      rw [collectStmt] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [NormalForm.HoistedTop]; exact noFunDef_stripStmts body
      · exact hoistedTop_collectStmts body x hx
  | .block b, x, hx => by rw [collectStmt] at hx; exact hoistedTop_collectStmts b x hx
  | .cond c b, x, hx => by rw [collectStmt] at hx; exact hoistedTop_collectStmts b x hx
  | .switch c cases dflt, x, hx => by
      rw [collectStmt, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hoistedTop_collectCases cases x hx
      · exact hoistedTop_collectDflt dflt x hx
  | .forLoop init c post body, x, hx => by
      rw [collectStmt, List.mem_append, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact hoistedTop_collectStmts init x hx
      · exact hoistedTop_collectStmts post x hx
      · exact hoistedTop_collectStmts body x hx
  | .letDecl _ _, x, hx => by rw [collectStmt] at hx; simp at hx
  | .assign _ _, x, hx => by rw [collectStmt] at hx; simp at hx
  | .exprStmt _, x, hx => by rw [collectStmt] at hx; simp at hx
  | .«break», x, hx => by rw [collectStmt] at hx; simp at hx
  | .«continue», x, hx => by rw [collectStmt] at hx; simp at hx
  | .leave, x, hx => by rw [collectStmt] at hx; simp at hx
theorem hoistedTop_collectStmts : ∀ (b : List (Stmt D.Op)), ∀ x ∈ collectStmts b,
    NormalForm.HoistedTop x
  | [], x, hx => by simp [collectStmts] at hx
  | s :: rest, x, hx => by
      rw [collectStmts, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hoistedTop_collectStmt s x hx
      · exact hoistedTop_collectStmts rest x hx
theorem hoistedTop_collectCases : ∀ (cs : List (Literal × Block D.Op)),
    ∀ x ∈ collectCases cs, NormalForm.HoistedTop x
  | [], x, hx => by simp [collectCases] at hx
  | (_, b) :: rest, x, hx => by
      rw [collectCases, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hoistedTop_collectStmts b x hx
      · exact hoistedTop_collectCases rest x hx
theorem hoistedTop_collectDflt : ∀ (d : Option (Block D.Op)),
    ∀ x ∈ collectDflt d, NormalForm.HoistedTop x
  | none, x, hx => by simp [collectDflt] at hx
  | some b, x, hx => by rw [collectDflt] at hx; exact hoistedTop_collectStmts b x hx
end

/-- **`liftFunDefs` produces a function-hoisted block, unconditionally.** After
the hoister runs, every function definition is at the top level of the block with
a definition-free body — the `FunctionsHoisted` component of the normal form. -/
theorem functionsHoisted_liftFunDefs (b : Block D.Op) :
    NormalForm.FunctionsHoisted (liftFunDefs b) := by
  intro s hs
  rw [liftFunDefs, List.mem_append] at hs
  rcases hs with hc | hst
  · exact hoistedTop_collectStmts b s hc
  · have hnf : NormalForm.NoFunDefStmt s := noFunDefStmt_of_mem (noFunDef_stripStmts b) hst
    cases s with
    | funDef n ps rs body => rw [NormalForm.NoFunDefStmt] at hnf; exact hnf.elim
    | _ => exact hnf

/-- On a disambiguated, well-scoped block the pass really hoists, so its output
is `FunctionsHoisted`. -/
theorem hoistBlock_functionsHoisted {b : Block D.Op} (hg : hoistGuard b = true) :
    NormalForm.FunctionsHoisted (hoistBlock b) := by
  simp only [hoistBlock, guardedBlock, if_pos hg]
  exact functionsHoisted_liftFunDefs b

end YulEvmCompiler.Optimizer.Normalization
