import YulEvmCompiler.Optimizer.Implementation.Normalization.HoistFunDefs

/-!
# Semantic equivalence of function hoisting

Main result: `liftFunDefs_run_equiv` — for a program with globally unique
function names that is well scoped, hoisting all function definitions to the top
block preserves whole-program semantics (`Run`-equivalence, in both directions).

Yul functions capture no variables (a callee runs with a fresh `VEnv`), only the
*function environment* (`cenv`, the scopes visible at the definition site). So
hoisting is sound exactly when name resolution is preserved:

* **unique names** ⇒ the flattening is unambiguous and needs no renaming (a name
  resolves to the one function with that name, wherever it sits);
* **well-scoped** ⇒ every call the *lifted* program can make (all functions are
  now globally visible) was already resolvable in the original, so the original
  is not stuck where the lifted program runs — the direction that would
  otherwise fail (`{ { function g(){} }  g() }` is stuck originally but runs
  after hoisting).

## Proof architecture (being built)

The lifted top block hoists `flat := hoist (collectStmts b)` — the whole
program's functions, each with a `stripStmts`-ed body — while every stripped
nested block hoists `[]`. The heart is a bidirectional `Step` simulation
(`step_lift_sim`) transporting a derivation across a relation `FEnvLift flat`
that couples the original scope *stack* to the *flat* scope, while the code is
simultaneously `stripStmts`-ed. This differs from `FunCongr`/`EmptyScope`
(same code, related envs): here code and environment transform together, and the
`callOk` case re-establishes `FEnvLift` between the callee's original `cenv` and
`flat`.
-/

namespace YulEvmCompiler.Optimizer.Normalization

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### Well-scopedness -/

/-- Top-level function names of a block (what `hoist` brings into scope). -/
def funNamesTop (b : List (Stmt D.Op)) : List Ident :=
  b.filterMap (fun s => match s with | .funDef n _ _ _ => some n | _ => none)

mutual
/-- Every user-call name in an expression is in `scope`. -/
def ScopedExpr (scope : List Ident) : Expr D.Op → Prop
  | .lit _ => True
  | .var _ => True
  | .builtin _ args => ScopedArgs scope args
  | .call f args => f ∈ scope ∧ ScopedArgs scope args
def ScopedArgs (scope : List Ident) : List (Expr D.Op) → Prop
  | [] => True
  | e :: rest => ScopedExpr scope e ∧ ScopedArgs scope rest
end

mutual
/-- Every call in a statement resolves in the accumulated function scope. A block
extends the scope with its own top-level function names (mirroring `hoist`). -/
def ScopedStmt (scope : List Ident) : Stmt D.Op → Prop
  | .funDef _ _ _ body => ScopedStmts (funNamesTop body ++ scope) body
  | .block b => ScopedStmts (funNamesTop b ++ scope) b
  | .cond c b => ScopedExpr scope c ∧ ScopedStmts (funNamesTop b ++ scope) b
  | .switch c cases dflt =>
      ScopedExpr scope c ∧ ScopedCases scope cases ∧ ScopedDflt scope dflt
  | .forLoop init c post body =>
      -- init's functions are visible in cond/post/body (they share the loop scope);
      -- post and body are each executed as a block, so hoist their own functions too.
      ScopedStmts (funNamesTop init ++ scope) init ∧
      ScopedExpr (funNamesTop init ++ scope) c ∧
      ScopedStmts (funNamesTop post ++ (funNamesTop init ++ scope)) post ∧
      ScopedStmts (funNamesTop body ++ (funNamesTop init ++ scope)) body
  | .letDecl _ val => match val with | none => True | some e => ScopedExpr scope e
  | .assign _ e => ScopedExpr scope e
  | .exprStmt e => ScopedExpr scope e
  | .break => True
  | .continue => True
  | .leave => True
def ScopedStmts (scope : List Ident) : List (Stmt D.Op) → Prop
  | [] => True
  | s :: rest => ScopedStmt scope s ∧ ScopedStmts scope rest
def ScopedCases (scope : List Ident) : List (Literal × Block D.Op) → Prop
  | [] => True
  | (_, b) :: rest => ScopedStmts (funNamesTop b ++ scope) b ∧ ScopedCases scope rest
def ScopedDflt (scope : List Ident) : Option (Block D.Op) → Prop
  | none => True
  | some b => ScopedStmts (funNamesTop b ++ scope) b
end

/-- The program is well scoped: every call resolves under the scope that starts
with the top block's own functions. -/
def WellScoped (b : Block D.Op) : Prop := ScopedStmts (funNamesTop b) b

/-! ### Structural facts about `strip`/`collect`/`hoist` -/

/-- The flat top scope the lifted program hoists: every function of `b`, each
with a `stripStmts`-ed body. -/
def flat (b : Block D.Op) : FScope D := hoist D (collectStmts b)

omit [DecidableEq D.Value] in
theorem hoist_append (a c : List (Stmt D.Op)) :
    hoist D (a ++ c) = hoist D a ++ hoist D c := by
  simp only [hoist, List.filterMap_append]

omit [DecidableEq D.Value] in
/-- Stripping removes every top-level `funDef`, so the stripped block hoists
nothing. -/
theorem hoist_stripStmts (b : List (Stmt D.Op)) : hoist D (stripStmts b) = [] := by
  induction b with
  | nil => rfl
  | cons s rest ih =>
      cases s with
      | funDef n ps rs body => rw [stripStmts]; exact ih
      | block bb => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | cond c bb => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | switch c cs d => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | forLoop i c p bb => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | letDecl vs v => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | assign vs e => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | exprStmt e => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | «break» => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | «continue» => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | leave => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih

omit [DecidableEq D.Value] in
/-- The lifted top block hoists exactly the flat scope. -/
theorem hoist_liftFunDefs (b : Block D.Op) : hoist D (liftFunDefs b) = flat b := by
  rw [liftFunDefs, hoist_append, hoist_stripStmts, List.append_nil, flat]

omit [DecidableEq D.Value] in
theorem hoist_map_fst (b : List (Stmt D.Op)) :
    (hoist D b).map (·.1) = funNamesTop b := by
  simp only [hoist, funNamesTop, List.map_filterMap]
  congr 1
  funext s
  cases s <;> rfl

omit [DecidableEq D.Value] in
theorem funNamesTop_append (a c : List (Stmt D.Op)) :
    funNamesTop (a ++ c) = funNamesTop a ++ funNamesTop c := by
  simp only [funNamesTop, List.filterMap_append]

omit [DecidableEq D.Value] in
theorem funNamesTop_cons_funDef (n ps rs bd) (rest : List (Stmt D.Op)) :
    funNamesTop (D := D) (.funDef n ps rs bd :: rest) = n :: funNamesTop rest := by
  simp only [funNamesTop, List.filterMap_cons]

/-- Every statement `collectStmts` emits is a function definition. -/
def IsFunDef : Stmt D.Op → Prop
  | .funDef _ _ _ _ => True
  | _ => False

/-- Running a prefix of function definitions is a no-op (each `funDef`
statement steps to `.normal` with the environment and state unchanged). -/
theorem funDefs_noop {funs : FunEnv D} {fds rest : List (Stmt D.Op)}
    (hall : ∀ s ∈ fds, IsFunDef (D := D) s) {V st V2 st2 o} :
    Step D funs V st (.stmts (fds ++ rest)) (.sres V2 st2 o) ↔
      Step D funs V st (.stmts rest) (.sres V2 st2 o) := by
  induction fds with
  | nil => simp
  | cons s fds' ih =>
      obtain ⟨n, ps, rs, body, rfl⟩ : ∃ n ps rs body, s = .funDef n ps rs body := by
        have hmem := hall s (by simp)
        cases s with
        | funDef n ps rs body => exact ⟨n, ps, rs, body, rfl⟩
        | _ => exact absurd hmem (by simp [IsFunDef])
      have hall' : ∀ s ∈ fds', IsFunDef (D := D) s :=
        fun s hs => hall s (List.mem_cons_of_mem _ hs)
      constructor
      · intro h
        rw [List.cons_append] at h
        cases h with
        | seqCons hs htail => cases hs; exact (ih hall').mp htail
        | seqStop hs hne => cases hs; exact absurd rfl hne
      · intro h
        rw [List.cons_append]
        exact Step.seqCons Step.funDef ((ih hall').mpr h)

/- `collectStmts` (and friends) yield only function definitions. -/
mutual
theorem collectStmt_allFunDef : ∀ (s : Stmt D.Op), ∀ x ∈ collectStmt s, IsFunDef (D := D) x
  | .funDef n ps rs body => by
      intro x hx; simp only [collectStmt, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp [IsFunDef]
      · exact collectStmts_allFunDef body x hx
  | .block b => by
      intro x hx; simp only [collectStmt] at hx; exact collectStmts_allFunDef b x hx
  | .cond c b => by
      intro x hx; simp only [collectStmt] at hx; exact collectStmts_allFunDef b x hx
  | .switch c cs d => by
      intro x hx; simp only [collectStmt, List.mem_append] at hx
      rcases hx with hx | hx
      · exact collectCases_allFunDef cs x hx
      · exact collectDflt_allFunDef d x hx
  | .forLoop i c p bd => by
      intro x hx; simp only [collectStmt, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact collectStmts_allFunDef i x hx
      · exact collectStmts_allFunDef p x hx
      · exact collectStmts_allFunDef bd x hx
  | .letDecl _ _ => by intro x hx; simp [collectStmt] at hx
  | .assign _ _ => by intro x hx; simp [collectStmt] at hx
  | .exprStmt _ => by intro x hx; simp [collectStmt] at hx
  | .break => by intro x hx; simp [collectStmt] at hx
  | .continue => by intro x hx; simp [collectStmt] at hx
  | .leave => by intro x hx; simp [collectStmt] at hx
theorem collectStmts_allFunDef :
    ∀ (b : List (Stmt D.Op)), ∀ x ∈ collectStmts b, IsFunDef (D := D) x
  | [] => by intro x hx; simp [collectStmts] at hx
  | s :: rest => by
      intro x hx; simp only [collectStmts, List.mem_append] at hx
      rcases hx with hx | hx
      · exact collectStmt_allFunDef s x hx
      · exact collectStmts_allFunDef rest x hx
theorem collectCases_allFunDef :
    ∀ (cs : List (Literal × Block D.Op)), ∀ x ∈ collectCases cs, IsFunDef (D := D) x
  | [] => by intro x hx; simp [collectCases] at hx
  | (_, b) :: rest => by
      intro x hx; simp only [collectCases, List.mem_append] at hx
      rcases hx with hx | hx
      · exact collectStmts_allFunDef b x hx
      · exact collectCases_allFunDef rest x hx
theorem collectDflt_allFunDef :
    ∀ (d : Option (Block D.Op)), ∀ x ∈ collectDflt d, IsFunDef (D := D) x
  | none => by intro x hx; simp [collectDflt] at hx
  | some b => by intro x hx; simp only [collectDflt] at hx; exact collectStmts_allFunDef b x hx
end


/-! ### The core simulation (Run-equivalence; base = []) -/

/-- A function declaration with its body stripped of nested definitions. -/
def stripDecl (d : FDecl D) : FDecl D := { d with body := stripStmts d.body }

/-- All function names bound anywhere in an environment (scope stack). -/
def funNamesEnv (funs : FunEnv D) : List Ident :=
  (funs.map (fun s => s.map (·.1))).flatten

/-- Resolve a name in the single flat scope. -/
def flatLookup (flatSc : FScope D) (f : Ident) : Option (FDecl D) :=
  (lookupFun [flatSc] f).map (·.1)

/-- Every function collected out of `code` is registered in the flat scope with
its (already-stripped) body. -/
def CodeInFlat (flatSc : FScope D) (code : List (Stmt D.Op)) : Prop :=
  ∀ n ps rs bd, (Stmt.funDef n ps rs bd) ∈ collectStmts code →
    flatLookup flatSc n = some { params := ps, rets := rs, body := bd }

/-- The original environment is a valid program scope stack for `flatSc`: every
function it resolves matches the flat scope (stripped), has a well-scoped body,
and a body whose own functions are registered in the flat scope. No ambient base
(this is the whole-program `Run` setting). -/
def GoodO (flatSc : FScope D) : FunEnv D → Prop
  | [] => True
  | s :: rest =>
      (∀ n d, (n, d) ∈ s →
        flatLookup flatSc n = some (stripDecl d) ∧
        ScopedStmts (funNamesTop d.body ++ funNamesEnv (s :: rest)) d.body ∧
        CodeInFlat flatSc d.body) ∧ GoodO flatSc rest

/-- The lifted environment resolves every name exactly as the single flat scope
does (nested stripped blocks only add empty scopes, transparent to lookup). -/
def ResEq (flatSc : FScope D) (funs_h : FunEnv D) : Prop :=
  ∀ f, lookupFun funs_h f = lookupFun [flatSc] f

/-- `stripStmt` on the `Code` wrapper. -/
def stripCode : Code D.Op → Code D.Op
  | .expr e => .expr e
  | .args es => .args es
  | .stmt s => .stmt (stripStmt s)
  | .stmts ss => .stmts (stripStmts ss)
  | .loop c post body => .loop c (stripStmts post) (stripStmts body)

/-- Well-scopedness lifted to the `Code` wrapper. -/
def ScopedCode (Γ : List Ident) : Code D.Op → Prop
  | .expr e => ScopedExpr Γ e
  | .args es => ScopedArgs Γ es
  | .stmt s => ScopedStmt Γ s
  | .stmts ss => ScopedStmts Γ ss
  | .loop c post body =>
      ScopedExpr Γ c ∧ ScopedStmts (funNamesTop post ++ Γ) post ∧
        ScopedStmts (funNamesTop body ++ Γ) body

/-- `CodeInFlat` lifted to the `Code` wrapper. -/
def CodeInFlatCode (flatSc : FScope D) : Code D.Op → Prop
  | .expr _ => True
  | .args _ => True
  | .stmt s => CodeInFlat flatSc [s]
  | .stmts ss => CodeInFlat flatSc ss
  | .loop _ post body => CodeInFlat flatSc post ∧ CodeInFlat flatSc body

omit [DecidableEq D.Value] in
theorem funNamesEnv_cons (s : FScope D) (rest : FunEnv D) :
    funNamesEnv (s :: rest) = s.map (·.1) ++ funNamesEnv rest := by
  simp only [funNamesEnv, List.map_cons, List.flatten_cons]

omit [DecidableEq D.Value] in
theorem funNamesEnv_append (a c : FunEnv D) :
    funNamesEnv (a ++ c) = funNamesEnv a ++ funNamesEnv c := by
  simp only [funNamesEnv, List.map_append, List.flatten_append]

omit [DecidableEq D.Value] in
theorem lookupFun_cenv_suffix : ∀ (funs : FunEnv D) {f d cenv},
    lookupFun funs f = some (d, cenv) → List.IsSuffix cenv funs
  | [], _, _, _, h => by simp [lookupFun] at h
  | s :: rest, f, d, cenv, h => by
      unfold lookupFun at h
      cases hfind : s.find? (fun p => p.1 = f) with
      | some p =>
          rw [hfind] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h; exact List.suffix_refl _
      | none =>
          rw [hfind] at h
          exact (lookupFun_cenv_suffix rest h).trans (List.suffix_cons _ _)

omit [DecidableEq D.Value] in
theorem goodO_append_right : ∀ (a : FunEnv D) {c : FunEnv D} {flatSc},
    GoodO flatSc (a ++ c) → GoodO flatSc c
  | [], _, _, h => h
  | _ :: a', _, _, h => goodO_append_right a' h.2

omit [DecidableEq D.Value] in
/-- `GoodO` is inherited by any closure environment a lookup returns (a suffix). -/
theorem goodO_cenv {flatSc : FScope D} {funs : FunEnv D} (hg : GoodO flatSc funs)
    {f d cenv} (hlk : lookupFun funs f = some (d, cenv)) : GoodO flatSc cenv := by
  obtain ⟨pre, hpre⟩ := lookupFun_cenv_suffix funs hlk
  rw [← hpre] at hg
  exact goodO_append_right pre hg

omit [DecidableEq D.Value] in
/-- Facts about the function a lookup resolves, with the correct (positional)
body scope, read off structural `GoodO`. -/
theorem goodO_lookup : ∀ {funs : FunEnv D} {flatSc : FScope D},
    GoodO flatSc funs → ∀ {fn d cenv}, lookupFun funs fn = some (d, cenv) →
      flatLookup flatSc fn = some (stripDecl d) ∧
      ScopedStmts (funNamesTop d.body ++ funNamesEnv cenv) d.body ∧
      CodeInFlat flatSc d.body
  | [], _, _, _, _, _, h => by simp [lookupFun] at h
  | s :: rest, flatSc, hg, fn, d, cenv, hlk => by
      unfold lookupFun at hlk
      cases hfind : s.find? (fun p => p.1 = fn) with
      | some p =>
          rw [hfind] at hlk; simp only [Option.some.injEq, Prod.mk.injEq] at hlk
          obtain ⟨hd, hc⟩ := hlk
          have hpmem := List.mem_of_find?_eq_some hfind
          have hpkey : p.1 = fn := by simpa using List.find?_some hfind
          have hmem : (fn, d) ∈ s := by
            have hp : p = (fn, d) := Prod.ext hpkey hd
            rw [← hp]; exact hpmem
          rw [← hc]
          exact hg.1 fn d hmem
      | none => rw [hfind] at hlk; exact goodO_lookup hg.2 hlk

omit [DecidableEq D.Value] in
theorem collectStmt_subset_collectStmts : ∀ {ss : List (Stmt D.Op)} {s},
    s ∈ ss → ∀ x ∈ collectStmt s, x ∈ collectStmts ss
  | [], _, h, _, _ => by simp at h
  | s' :: rest, s, h, x, hx => by
      rw [collectStmts, List.mem_append]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl hx
      · exact Or.inr (collectStmt_subset_collectStmts h x hx)

omit [DecidableEq D.Value] in
theorem mem_collectStmts_of_top {b : List (Stmt D.Op)} {f ps rs body}
    (h : (Stmt.funDef f ps rs body) ∈ b) :
    (Stmt.funDef f ps rs (stripStmts body)) ∈ collectStmts b := by
  refine collectStmt_subset_collectStmts h _ ?_
  rw [collectStmt]; exact List.mem_cons_self

omit [DecidableEq D.Value] in
theorem collectStmts_body_subset {b : List (Stmt D.Op)} {f ps rs body}
    (h : (Stmt.funDef f ps rs body) ∈ b) {x} (hx : x ∈ collectStmts body) :
    x ∈ collectStmts b := by
  refine collectStmt_subset_collectStmts h x ?_
  rw [collectStmt]; exact List.mem_cons_of_mem _ hx

omit [DecidableEq D.Value] in
theorem scopedStmts_funDef_body : ∀ {ss : List (Stmt D.Op)} {Γ},
    ScopedStmts Γ ss → ∀ {f ps rs body}, (Stmt.funDef f ps rs body) ∈ ss →
      ScopedStmts (funNamesTop body ++ Γ) body
  | [], _, _, _, _, _, _, h => by simp at h
  | s' :: rest, Γ, hsc, f, ps, rs, body, h => by
      obtain ⟨h1, h2⟩ := hsc
      rcases List.mem_cons.mp h with rfl | h
      · exact h1
      · exact scopedStmts_funDef_body h2 h

omit [DecidableEq D.Value] in
theorem mem_hoist_inv {b : List (Stmt D.Op)} {f} {d : FDecl D} (h : (f, d) ∈ hoist D b) :
    ∃ ps rs body, d = { params := ps, rets := rs, body := body } ∧
      (Stmt.funDef f ps rs body) ∈ b := by
  simp only [hoist, List.mem_filterMap] at h
  obtain ⟨s, hs, hg⟩ := h
  cases s with
  | funDef n ps rs body =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨hn, hd⟩ := hg; subst hn; subst hd
      exact ⟨ps, rs, body, rfl, hs⟩
  | _ => simp at hg

omit [DecidableEq D.Value] in
/-- `ResEq flatSc [flatSc]` — the flat scope resolves like itself. -/
theorem resEq_flat (flatSc : FScope D) : ResEq flatSc [flatSc] := fun _ => rfl

omit [DecidableEq D.Value] in
theorem funNamesEnv_hoist_cons (body : List (Stmt D.Op)) (funs : FunEnv D) :
    funNamesEnv (hoist D body :: funs) = funNamesTop body ++ funNamesEnv funs := by
  rw [funNamesEnv_cons, hoist_map_fst]

omit [DecidableEq D.Value] in
/-- Prepending an empty scope to the lifted env is transparent to resolution. -/
theorem resEq_cons_nil {flatSc : FScope D} {funs_h : FunEnv D} (h : ResEq flatSc funs_h) :
    ResEq flatSc ([] :: funs_h) := by
  intro f
  show lookupFun ([] :: funs_h) f = lookupFun [flatSc] f
  unfold lookupFun
  simp only [List.find?_nil]
  exact h f

omit [DecidableEq D.Value] in
/-- Establishing `GoodO` for a pushed block scope, from the block's functions
being in the flat scope and its body well scoped (used for `block`/`forLoop`). -/
theorem goodO_push {flatSc : FScope D} {funs_o : FunEnv D} {body : List (Stmt D.Op)}
    (hO : GoodO flatSc funs_o) (hcfb : CodeInFlat flatSc body)
    (hwsb : ScopedStmts (funNamesTop body ++ funNamesEnv funs_o) body) :
    GoodO flatSc (hoist D body :: funs_o) := by
  refine ⟨?_, hO⟩
  intro n d hmem
  obtain ⟨ps, rs, bdy, hdeq, hfd⟩ := mem_hoist_inv hmem
  refine ⟨?_, ?_, ?_⟩
  · rw [hdeq]
    have hst : stripDecl (D := D) { params := ps, rets := rs, body := bdy }
        = { params := ps, rets := rs, body := stripStmts bdy } := rfl
    rw [hst]
    exact hcfb n ps rs (stripStmts bdy) (mem_collectStmts_of_top hfd)
  · rw [hdeq, funNamesEnv_hoist_cons]
    exact scopedStmts_funDef_body hwsb hfd
  · rw [hdeq]
    intro n' ps' rs' bd' hmem'
    exact hcfb n' ps' rs' bd' (collectStmts_body_subset hfd hmem')

/-! ### `CodeInFlat` / `ScopedStmts` extraction helpers for the simulation cases -/

omit [DecidableEq D.Value] in
/-- `CodeInFlat` transports along a `collectStmts` inclusion. -/
theorem codeInFlat_mono {flatSc : FScope D} {sub code : List (Stmt D.Op)}
    (hsub : ∀ x ∈ collectStmts sub, x ∈ collectStmts code)
    (h : CodeInFlat flatSc code) : CodeInFlat flatSc sub :=
  fun n ps rs bd hm => h n ps rs bd (hsub _ hm)

omit [DecidableEq D.Value] in
theorem collectStmts_singleton (s : Stmt D.Op) : collectStmts [s] = collectStmt s := by
  simp only [collectStmts, List.append_nil]

omit [DecidableEq D.Value] in
theorem cif_block_inv {flatSc : FScope D} {body : List (Stmt D.Op)}
    (h : CodeInFlat flatSc [Stmt.block body]) : CodeInFlat flatSc body :=
  codeInFlat_mono (fun _ hx => by rw [collectStmts_singleton]; exact hx) h

omit [DecidableEq D.Value] in
theorem cif_block_wrap {flatSc : FScope D} {body : List (Stmt D.Op)}
    (h : CodeInFlat flatSc body) : CodeInFlat flatSc [Stmt.block body] :=
  codeInFlat_mono (fun _ hx => by rw [collectStmts_singleton] at hx; exact hx) h

omit [DecidableEq D.Value] in
theorem cif_cond_inv {flatSc : FScope D} {c} {body : List (Stmt D.Op)}
    (h : CodeInFlat flatSc [Stmt.cond c body]) : CodeInFlat flatSc body :=
  codeInFlat_mono (fun _ hx => by rw [collectStmts_singleton]; exact hx) h

omit [DecidableEq D.Value] in
theorem cif_head {flatSc : FScope D} {s} {rest : List (Stmt D.Op)}
    (h : CodeInFlat flatSc (s :: rest)) : CodeInFlat flatSc [s] :=
  codeInFlat_mono (fun x hx => by
    rw [collectStmts_singleton] at hx
    rw [collectStmts, List.mem_append]; exact Or.inl hx) h

omit [DecidableEq D.Value] in
theorem cif_tail {flatSc : FScope D} {s} {rest : List (Stmt D.Op)}
    (h : CodeInFlat flatSc (s :: rest)) : CodeInFlat flatSc rest :=
  codeInFlat_mono (fun x hx => by rw [collectStmts, List.mem_append]; exact Or.inr hx) h

omit [DecidableEq D.Value] in
theorem cif_for_init {flatSc : FScope D} {init c post body}
    (h : CodeInFlat flatSc [Stmt.forLoop init c post body]) : CodeInFlat flatSc init :=
  codeInFlat_mono (fun x hx => by
    rw [collectStmts_singleton, collectStmt, List.mem_append, List.mem_append]
    exact Or.inl (Or.inl hx)) h

omit [DecidableEq D.Value] in
theorem cif_for_post {flatSc : FScope D} {init c post body}
    (h : CodeInFlat flatSc [Stmt.forLoop init c post body]) : CodeInFlat flatSc post :=
  codeInFlat_mono (fun x hx => by
    rw [collectStmts_singleton, collectStmt, List.mem_append, List.mem_append]
    exact Or.inl (Or.inr hx)) h

omit [DecidableEq D.Value] in
theorem cif_for_body {flatSc : FScope D} {init c post body}
    (h : CodeInFlat flatSc [Stmt.forLoop init c post body]) : CodeInFlat flatSc body :=
  codeInFlat_mono (fun x hx => by
    rw [collectStmts_singleton, collectStmt, List.mem_append]
    exact Or.inr hx) h

/-- The block a `switch` selects has its collected functions among the cases'
and default's collected functions. -/
theorem collectStmts_selectSwitch_subset (cv) :
    ∀ {cases : List (Literal × Block D.Op)} {dflt : Option (Block D.Op)} {x},
      x ∈ collectStmts (selectSwitch D cv cases dflt) → x ∈ collectCases cases ++ collectDflt dflt
  | [], dflt, x, hx => by
      unfold selectSwitch at hx
      simp only [List.find?_nil] at hx
      cases dflt with
      | none => simp only [Option.getD_none, collectStmts, List.not_mem_nil] at hx
      | some b => simpa only [Option.getD_some, collectCases, collectDflt, List.nil_append] using hx
  | (l, b) :: rest, dflt, x, hx => by
      unfold selectSwitch at hx
      by_cases hcv : cv = D.litValue l
      · rw [List.find?_cons_of_pos (by simp [hcv])] at hx
        rw [collectCases]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx)))
      · rw [List.find?_cons_of_neg (by simp [hcv])] at hx
        have h2 := collectStmts_selectSwitch_subset cv (cases := rest) (dflt := dflt) hx
        rw [collectCases]
        rcases List.mem_append.mp h2 with h | h
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
        · exact List.mem_append.mpr (Or.inr h)

theorem cif_switch_sel {flatSc : FScope D} {c cv cases dflt}
    (h : CodeInFlat flatSc [Stmt.switch c cases dflt]) :
    CodeInFlat flatSc (selectSwitch D cv cases dflt) :=
  codeInFlat_mono (fun x hx => by
    rw [collectStmts_singleton, collectStmt]
    exact collectStmts_selectSwitch_subset cv hx) h

/-- `stripStmts` commutes with `selectSwitch`: stripping then selecting equals
selecting from the stripped cases/default. -/
theorem selectSwitch_strip (cv) :
    ∀ (cases : List (Literal × Block D.Op)) (dflt : Option (Block D.Op)),
      selectSwitch D cv (stripCases cases) (stripDflt dflt)
        = stripStmts (selectSwitch D cv cases dflt)
  | [], dflt => by
      simp only [stripCases]
      unfold selectSwitch
      simp only [List.find?_nil]
      cases dflt with
      | none => rfl
      | some b => rfl
  | (l, b) :: rest, dflt => by
      rw [stripCases]
      unfold selectSwitch
      by_cases hcv : cv = D.litValue l
      · rw [List.find?_cons_of_pos (by simp [hcv]), List.find?_cons_of_pos (by simp [hcv])]
      · rw [List.find?_cons_of_neg (by simp [hcv]), List.find?_cons_of_neg (by simp [hcv])]
        exact selectSwitch_strip cv rest dflt

/-- The selected `switch` block is well scoped (in the block-hoisted scope) when
the cases and default are. -/
theorem scopedStmts_selectSwitch {Γ} {cv} :
    ∀ {cases : List (Literal × Block D.Op)} {dflt : Option (Block D.Op)},
      ScopedCases Γ cases → ScopedDflt Γ dflt →
      ScopedStmts (funNamesTop (selectSwitch D cv cases dflt) ++ Γ) (selectSwitch D cv cases dflt)
  | [], dflt, _, hd => by
      unfold selectSwitch
      simp only [List.find?_nil]
      cases dflt with
      | none => exact trivial
      | some b => exact hd
  | (l, b) :: rest, dflt, hc, hd => by
      unfold selectSwitch
      by_cases hcv : cv = D.litValue l
      · rw [List.find?_cons_of_pos (by simp [hcv])]; exact hc.1
      · rw [List.find?_cons_of_neg (by simp [hcv])]; exact scopedStmts_selectSwitch hc.2 hd

omit [DecidableEq D.Value] in
theorem lookupFun_singleton (scope : FScope D) (n : Ident) :
    lookupFun [scope] n = (scope.find? (fun p => p.1 = n)).map (fun p => (p.2, [scope])) := by
  simp only [lookupFun]
  cases scope.find? (fun p => p.1 = n) <;> rfl

omit [DecidableEq D.Value] in
/-- The lifted environment resolves a name to the flat (stripped) declaration,
with the flat scope as its closure environment. -/
theorem flatLookup_lifted {flatSc : FScope D} {funs_h : FunEnv D} {fn} {d : FDecl D}
    (hf : flatLookup flatSc fn = some d) (hH : ResEq flatSc funs_h) :
    lookupFun funs_h fn = some (d, [flatSc]) := by
  rw [hH fn, lookupFun_singleton]
  rw [flatLookup, lookupFun_singleton] at hf
  cases hfd : flatSc.find? (fun p => p.1 = fn) with
  | none => rw [hfd] at hf; simp at hf
  | some p =>
      rw [hfd] at hf
      obtain ⟨pn, pd⟩ := p
      have hpd : pd = d := by change some pd = some d at hf; injection hf
      subst hpd
      rfl

/-- **Forward simulation.** Under `GoodO`/`ResEq`/well-scopedness/`CodeInFlat`,
an original derivation transports to one over the flat (lifted) environment on
the `stripCode`-ped code. -/
theorem step_lift_fwd {flatSc : FScope D} :
    ∀ {funs_o V st code res}, Step D funs_o V st code res →
    ∀ {funs_h}, GoodO flatSc funs_o → ResEq flatSc funs_h →
      ScopedCode (funNamesEnv funs_o) code → CodeInFlatCode flatSc code →
      Step D funs_h V st (stripCode code) res := by
  intro funs_o V st code res h
  induction h with
  | lit => intro funs_h hO hH hws hcf; exact Step.lit
  | var hv => intro funs_h hO hH hws hcf; exact Step.var hv
  | builtinOk ha hb iha =>
      intro funs_h hO hH hws hcf; exact Step.builtinOk (iha hO hH hws trivial) hb
  | builtinHalt ha hb iha =>
      intro funs_h hO hH hws hcf; exact Step.builtinHalt (iha hO hH hws trivial) hb
  | builtinArgsHalt ha iha =>
      intro funs_h hO hH hws hcf; exact Step.builtinArgsHalt (iha hO hH hws trivial)
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hlk hlen hbody ho iha ihbody =>
      intro funs_h hO hH hws hcf
      obtain ⟨hflat, hsc, hcfb⟩ := goodO_lookup hO hlk
      refine Step.callOk (decl := stripDecl decl) (iha hO hH hws.2 trivial)
        (flatLookup_lifted hflat hH) hlen ?_ ho
      exact ihbody (goodO_cenv hO hlk) (resEq_flat flatSc) hsc (cif_block_wrap hcfb)
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hlk hlen hbody iha ihbody =>
      intro funs_h hO hH hws hcf
      obtain ⟨hflat, hsc, hcfb⟩ := goodO_lookup hO hlk
      exact Step.callHalt (decl := stripDecl decl) (iha hO hH hws.2 trivial)
        (flatLookup_lifted hflat hH) hlen
        (ihbody (goodO_cenv hO hlk) (resEq_flat flatSc) hsc (cif_block_wrap hcfb))
  | callArgsHalt ha iha =>
      intro funs_h hO hH hws hcf; exact Step.callArgsHalt (iha hO hH hws.2 trivial)
  | argsNil => intro funs_h hO hH hws hcf; exact Step.argsNil
  | argsCons hrest he ihrest ihe =>
      intro funs_h hO hH hws hcf
      exact Step.argsCons (ihrest hO hH hws.2 trivial) (ihe hO hH hws.1 trivial)
  | argsRestHalt hrest ihrest =>
      intro funs_h hO hH hws hcf; exact Step.argsRestHalt (ihrest hO hH hws.2 trivial)
  | argsHeadHalt hrest he ihrest ihe =>
      intro funs_h hO hH hws hcf
      exact Step.argsHeadHalt (ihrest hO hH hws.2 trivial) (ihe hO hH hws.1 trivial)
  | funDef => intro funs_h hO hH hws hcf; exact Step.funDef
  | block hb ihb =>
      intro funs_h hO hH hws hcf
      refine Step.block ?_
      rw [hoist_stripStmts]
      exact ihb (goodO_push hO (cif_block_inv hcf) hws) (resEq_cons_nil hH)
        (by rw [funNamesEnv_hoist_cons]; exact hws) (cif_block_inv hcf)
  | letZero => intro funs_h hO hH hws hcf; exact Step.letZero
  | letVal hv hlen ihv =>
      intro funs_h hO hH hws hcf; exact Step.letVal (ihv hO hH hws trivial) hlen
  | letHalt hv ihv =>
      intro funs_h hO hH hws hcf; exact Step.letHalt (ihv hO hH hws trivial)
  | assignVal hv hlen ihv =>
      intro funs_h hO hH hws hcf; exact Step.assignVal (ihv hO hH hws trivial) hlen
  | assignHalt hv ihv =>
      intro funs_h hO hH hws hcf; exact Step.assignHalt (ihv hO hH hws trivial)
  | exprStmt he ihe =>
      intro funs_h hO hH hws hcf; exact Step.exprStmt (ihe hO hH hws trivial)
  | exprStmtHalt he ihe =>
      intro funs_h hO hH hws hcf; exact Step.exprStmtHalt (ihe hO hH hws trivial)
  | ifTrue hc hne hbody ihc ihbody =>
      intro funs_h hO hH hws hcf
      exact Step.ifTrue (ihc hO hH hws.1 trivial) hne
        (ihbody hO hH hws.2 (cif_block_wrap (cif_cond_inv hcf)))
  | ifFalse hc heq ihc =>
      intro funs_h hO hH hws hcf; exact Step.ifFalse (ihc hO hH hws.1 trivial) heq
  | ifHalt hc ihc =>
      intro funs_h hO hH hws hcf; exact Step.ifHalt (ihc hO hH hws.1 trivial)
  | switchExec hc hbody ihc ihbody =>
      intro funs_h hO hH hws hcf
      refine Step.switchExec (ihc hO hH hws.1 trivial) ?_
      rw [selectSwitch_strip]
      exact ihbody hO hH (scopedStmts_selectSwitch hws.2.1 hws.2.2)
        (cif_block_wrap (cif_switch_sel hcf))
  | switchHalt hc ihc =>
      intro funs_h hO hH hws hcf; exact Step.switchHalt (ihc hO hH hws.1 trivial)
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs_h hO hH hws hcf
      refine Step.forLoop (Vinit := Vinit) (stinit := stinit) ?_ ?_
      · rw [hoist_stripStmts]
        exact ihinit (goodO_push hO (cif_for_init hcf) hws.1) (resEq_cons_nil hH)
          (by rw [funNamesEnv_hoist_cons]; exact hws.1) (cif_for_init hcf)
      · rw [hoist_stripStmts]
        exact ihloop (goodO_push hO (cif_for_init hcf) hws.1) (resEq_cons_nil hH)
          (by rw [funNamesEnv_hoist_cons]; exact ⟨hws.2.1, hws.2.2.1, hws.2.2.2⟩)
          ⟨cif_for_post hcf, cif_for_body hcf⟩
  | forInitHalt hinit ihinit =>
      intro funs_h hO hH hws hcf
      refine Step.forInitHalt ?_
      rw [hoist_stripStmts]
      exact ihinit (goodO_push hO (cif_for_init hcf) hws.1) (resEq_cons_nil hH)
        (by rw [funNamesEnv_hoist_cons]; exact hws.1) (cif_for_init hcf)
  | «break» => intro funs_h hO hH hws hcf; exact Step.break
  | «continue» => intro funs_h hO hH hws hcf; exact Step.continue
  | leave => intro funs_h hO hH hws hcf; exact Step.leave
  | seqNil => intro funs_h hO hH hws hcf; exact Step.seqNil
  | @seqCons funs V st s rest V1 st1 V2 st2 o hs hrest ihs ihrest =>
      intro funs_h hO hH hws hcf
      cases s with
      | funDef n ps rs bd =>
          cases hs
          exact ihrest hO hH hws.2 (cif_tail hcf)
      | _ =>
          exact Step.seqCons (ihs hO hH hws.1 (cif_head hcf)) (ihrest hO hH hws.2 (cif_tail hcf))
  | @seqStop funs V st s rest V1 st1 o hs hne ihs =>
      intro funs_h hO hH hws hcf
      cases s with
      | funDef n ps rs bd => cases hs; exact absurd rfl hne
      | _ => exact Step.seqStop (ihs hO hH hws.1 (cif_head hcf)) hne
  | loopDone hc heq ihc =>
      intro funs_h hO hH hws hcf; exact Step.loopDone (ihc hO hH hws.1 trivial) heq
  | loopCondHalt hc ihc =>
      intro funs_h hO hH hws hcf; exact Step.loopCondHalt (ihc hO hH hws.1 trivial)
  | loopStep hc hne hbody hob hpost hrec ihc ihbody ihpost ihrec =>
      intro funs_h hO hH hws hcf
      exact Step.loopStep (ihc hO hH hws.1 trivial) hne
        (ihbody hO hH hws.2.2 (cif_block_wrap hcf.2)) hob
        (ihpost hO hH hws.2.1 (cif_block_wrap hcf.1))
        (ihrec hO hH hws hcf)
  | loopPostHalt hc hne hbody hob hpost ihc ihbody ihpost =>
      intro funs_h hO hH hws hcf
      exact Step.loopPostHalt (ihc hO hH hws.1 trivial) hne
        (ihbody hO hH hws.2.2 (cif_block_wrap hcf.2)) hob
        (ihpost hO hH hws.2.1 (cif_block_wrap hcf.1))
  | loopBreak hc hne hbody ihc ihbody =>
      intro funs_h hO hH hws hcf
      exact Step.loopBreak (ihc hO hH hws.1 trivial) hne
        (ihbody hO hH hws.2.2 (cif_block_wrap hcf.2))
  | loopLeave hc hne hbody ihc ihbody =>
      intro funs_h hO hH hws hcf
      exact Step.loopLeave (ihc hO hH hws.1 trivial) hne
        (ihbody hO hH hws.2.2 (cif_block_wrap hcf.2))
  | loopBodyHalt hc hne hbody ihc ihbody =>
      intro funs_h hO hH hws hcf
      exact Step.loopBodyHalt (ihc hO hH hws.1 trivial) hne
        (ihbody hO hH hws.2.2 (cif_block_wrap hcf.2))

/-! ### `strip` inversion (for the backward simulation)

`stripCode`/`stripStmt` preserve the outer constructor (expressions are left
untouched), so a stripped shape determines the original's shape up to the
recursive sub-parts. -/

omit [DecidableEq D.Value] in
theorem stripCode_expr_inv {code : Code D.Op} {e} (h : stripCode code = .expr e) :
    code = .expr e := by
  cases code with
  | expr e' => injection h with h; rw [h]
  | _ => simp [stripCode] at h

omit [DecidableEq D.Value] in
theorem stripCode_args_inv {code : Code D.Op} {es} (h : stripCode code = .args es) :
    code = .args es := by
  cases code with
  | args es' => injection h with h; rw [h]
  | _ => simp [stripCode] at h

omit [DecidableEq D.Value] in
theorem stripCode_stmt_inv {code : Code D.Op} {s'} (h : stripCode code = .stmt s') :
    ∃ s, code = .stmt s ∧ stripStmt s = s' := by
  cases code with
  | stmt s => exact ⟨s, rfl, Code.stmt.inj h⟩
  | _ => simp [stripCode] at h

omit [DecidableEq D.Value] in
theorem stripCode_stmts_inv {code : Code D.Op} {ss'} (h : stripCode code = .stmts ss') :
    ∃ ss, code = .stmts ss ∧ stripStmts ss = ss' := by
  cases code with
  | stmts ss => exact ⟨ss, rfl, Code.stmts.inj h⟩
  | _ => simp [stripCode] at h

omit [DecidableEq D.Value] in
theorem stripCode_loop_inv {code : Code D.Op} {c pp' bb'} (h : stripCode code = .loop c pp' bb') :
    ∃ pp bb, code = .loop c pp bb ∧ stripStmts pp = pp' ∧ stripStmts bb = bb' := by
  cases code with
  | loop c' pp bb =>
      injection h with hc hpp hbb; subst hc; exact ⟨pp, bb, rfl, hpp, hbb⟩
  | _ => simp [stripCode] at h

/- `stripStmt` inversions per outer statement constructor. -/
omit [DecidableEq D.Value] in
theorem stripStmt_block_inv {s : Stmt D.Op} {b'} (h : stripStmt s = .block b') :
    ∃ b, s = .block b ∧ stripStmts b = b' := by
  cases s with
  | block b => exact ⟨b, rfl, Stmt.block.inj h⟩
  | _ => simp [stripStmt] at h

omit [DecidableEq D.Value] in
theorem stripStmt_cond_inv {s : Stmt D.Op} {c b'} (h : stripStmt s = .cond c b') :
    ∃ b, s = .cond c b ∧ stripStmts b = b' := by
  cases s with
  | cond c₀ b => injection h with hc hb; subst hc; exact ⟨b, rfl, hb⟩
  | _ => simp [stripStmt] at h

omit [DecidableEq D.Value] in
theorem stripStmt_switch_inv {s : Stmt D.Op} {c cs' d'} (h : stripStmt s = .switch c cs' d') :
    ∃ cs d, s = .switch c cs d ∧ stripCases cs = cs' ∧ stripDflt d = d' := by
  cases s with
  | switch c₀ cs d => injection h with hc hcs hd; subst hc; exact ⟨cs, d, rfl, hcs, hd⟩
  | _ => simp [stripStmt] at h

omit [DecidableEq D.Value] in
theorem stripStmt_forLoop_inv {s : Stmt D.Op} {i' c p' b'} (h : stripStmt s = .forLoop i' c p' b') :
    ∃ i p b, s = .forLoop i c p b ∧ stripStmts i = i' ∧ stripStmts p = p' ∧ stripStmts b = b' := by
  cases s with
  | forLoop i c₀ p b =>
      injection h with hi hc hp hb; subst hc; exact ⟨i, p, b, rfl, hi, hp, hb⟩
  | _ => simp [stripStmt] at h

omit [DecidableEq D.Value] in
theorem stripStmt_funDef_inv {s : Stmt D.Op} {n ps rs b'} (h : stripStmt s = .funDef n ps rs b') :
    ∃ b, s = .funDef n ps rs b ∧ stripStmts b = b' := by
  cases s with
  | funDef n₀ ps₀ rs₀ b =>
      injection h with hn hps hrs hb; subst hn; subst hps; subst hrs; exact ⟨b, rfl, hb⟩
  | _ => simp [stripStmt] at h

omit [DecidableEq D.Value] in
theorem stripStmt_letDecl_inv {s : Stmt D.Op} {vars val} (h : stripStmt s = .letDecl vars val) :
    s = .letDecl vars val := by
  cases s with
  | letDecl v₀ vl₀ => injection h with hv hvl; rw [hv, hvl]
  | _ => simp [stripStmt] at h

omit [DecidableEq D.Value] in
theorem stripStmt_assign_inv {s : Stmt D.Op} {vars e} (h : stripStmt s = .assign vars e) :
    s = .assign vars e := by
  cases s with
  | assign v₀ e₀ => injection h with hv he; rw [hv, he]
  | _ => simp [stripStmt] at h

omit [DecidableEq D.Value] in
theorem stripStmt_exprStmt_inv {s : Stmt D.Op} {e} (h : stripStmt s = .exprStmt e) :
    s = .exprStmt e := by
  cases s with
  | exprStmt e₀ => injection h with he; rw [he]
  | _ => simp [stripStmt] at h

omit [DecidableEq D.Value] in
theorem stripStmt_break_inv {s : Stmt D.Op} (h : stripStmt s = .break) : s = .break := by
  cases s with
  | «break» => rfl
  | _ => simp [stripStmt] at h

omit [DecidableEq D.Value] in
theorem stripStmt_continue_inv {s : Stmt D.Op} (h : stripStmt s = .continue) : s = .continue := by
  cases s with
  | «continue» => rfl
  | _ => simp [stripStmt] at h

omit [DecidableEq D.Value] in
theorem stripStmt_leave_inv {s : Stmt D.Op} (h : stripStmt s = .leave) : s = .leave := by
  cases s with
  | leave => rfl
  | _ => simp [stripStmt] at h

/- If a statement list strips to empty, every statement in it is a `funDef`. -/
omit [DecidableEq D.Value] in
theorem stripStmts_nil_inv : ∀ {ss : List (Stmt D.Op)}, stripStmts ss = [] → ∀ x ∈ ss, IsFunDef x
  | [], _, _, hx => by simp at hx
  | s :: rest, h, x, hx => by
      cases s with
      | funDef n ps rs b =>
          have h' : stripStmts rest = [] := h
          rcases List.mem_cons.mp hx with rfl | hx
          · exact trivial
          · exact stripStmts_nil_inv h' x hx
      | _ => simp [stripStmts] at h

/- If a statement list strips to a cons, it is a run of `funDef`s followed by a
non-`funDef` head (which strips to the cons head) and a tail. -/
omit [DecidableEq D.Value] in
theorem stripStmts_cons_inv : ∀ {ss : List (Stmt D.Op)} {s' rest'}, stripStmts ss = s' :: rest' →
    ∃ fds s rest, ss = fds ++ s :: rest ∧ (∀ x ∈ fds, IsFunDef x) ∧
      stripStmt s = s' ∧ stripStmts rest = rest'
  | [], _, _, h => by simp [stripStmts] at h
  | s :: rest, s', rest', h => by
      cases s with
      | funDef n ps rs b =>
          have h' : stripStmts rest = s' :: rest' := h
          obtain ⟨fds, s₀, rest₀, hss, hfd, hs, hr⟩ := stripStmts_cons_inv h'
          exact ⟨.funDef n ps rs b :: fds, s₀, rest₀, by rw [hss, List.cons_append],
            fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hx
              · exact trivial
              · exact hfd x hx, hs, hr⟩
      | block bb =>
          injection h with h1 h2; exact ⟨[], .block bb, rest, rfl, by simp, h1, h2⟩
      | cond c bb =>
          injection h with h1 h2; exact ⟨[], .cond c bb, rest, rfl, by simp, h1, h2⟩
      | switch c cs d =>
          injection h with h1 h2; exact ⟨[], .switch c cs d, rest, rfl, by simp, h1, h2⟩
      | forLoop i c p bb =>
          injection h with h1 h2; exact ⟨[], .forLoop i c p bb, rest, rfl, by simp, h1, h2⟩
      | letDecl vs vl =>
          injection h with h1 h2; exact ⟨[], .letDecl vs vl, rest, rfl, by simp, h1, h2⟩
      | assign vs e =>
          injection h with h1 h2; exact ⟨[], .assign vs e, rest, rfl, by simp, h1, h2⟩
      | exprStmt e =>
          injection h with h1 h2; exact ⟨[], .exprStmt e, rest, rfl, by simp, h1, h2⟩
      | «break» =>
          injection h with h1 h2; exact ⟨[], .break, rest, rfl, by simp, h1, h2⟩
      | «continue» =>
          injection h with h1 h2; exact ⟨[], .continue, rest, rfl, by simp, h1, h2⟩
      | leave =>
          injection h with h1 h2; exact ⟨[], .leave, rest, rfl, by simp, h1, h2⟩

/-! ### Extra structural helpers for the backward direction -/

omit [DecidableEq D.Value] in
theorem collectStmts_append : ∀ (a b : List (Stmt D.Op)),
    collectStmts (a ++ b) = collectStmts a ++ collectStmts b
  | [], b => by simp [collectStmts]
  | s :: a', b => by
      rw [List.cons_append, collectStmts, collectStmts, collectStmts_append a' b,
        List.append_assoc]

omit [DecidableEq D.Value] in
theorem scopedStmts_append_right : ∀ (a : List (Stmt D.Op)) {b Γ},
    ScopedStmts Γ (a ++ b) → ScopedStmts Γ b
  | [], _, _, h => h
  | _ :: a', _, _, h => scopedStmts_append_right a' h.2

omit [DecidableEq D.Value] in
/-- A name occurring in the function environment resolves to some declaration. -/
theorem lookupFun_of_mem_funNamesEnv : ∀ {funs : FunEnv D} {fn}, fn ∈ funNamesEnv funs →
    ∃ d cenv, lookupFun funs fn = some (d, cenv)
  | [], fn, h => by simp [funNamesEnv] at h
  | s :: rest, fn, h => by
      unfold lookupFun
      cases hfind : s.find? (fun p => p.1 = fn) with
      | some p => exact ⟨p.2, s :: rest, rfl⟩
      | none =>
          rw [funNamesEnv_cons, List.mem_append] at h
          rcases h with hs | hrest
          · obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp hs
            have hcontra := List.find?_eq_none.mp hfind x hx
            simp only [hxeq, decide_true] at hcontra
            exact absurd trivial hcontra
          · exact lookupFun_of_mem_funNamesEnv hrest

/-- **Backward simulation.** A derivation over the flat (lifted) environment on
`stripCode code` transports back to one over the original environment on `code`. -/
theorem step_lift_bwd {flatSc : FScope D} :
    ∀ {funs_h V st code' res}, Step D funs_h V st code' res →
    ∀ {funs_o code}, stripCode code = code' → GoodO flatSc funs_o → ResEq flatSc funs_h →
      ScopedCode (funNamesEnv funs_o) code → CodeInFlatCode flatSc code →
      Step D funs_o V st code res := by
  intro funs_h V st code' res h
  induction h with
  | lit => intro funs_o code hstrip hO hH hws hcf; obtain rfl := stripCode_expr_inv hstrip; exact Step.lit
  | var hv => intro funs_o code hstrip hO hH hws hcf; obtain rfl := stripCode_expr_inv hstrip; exact Step.var hv
  | builtinOk ha hb iha =>
      intro funs_o code hstrip hO hH hws hcf; obtain rfl := stripCode_expr_inv hstrip
      exact Step.builtinOk (iha rfl hO hH hws trivial) hb
  | builtinHalt ha hb iha =>
      intro funs_o code hstrip hO hH hws hcf; obtain rfl := stripCode_expr_inv hstrip
      exact Step.builtinHalt (iha rfl hO hH hws trivial) hb
  | builtinArgsHalt ha iha =>
      intro funs_o code hstrip hO hH hws hcf; obtain rfl := stripCode_expr_inv hstrip
      exact Step.builtinArgsHalt (iha rfl hO hH hws trivial)
  | @callOk funs_h V st fn args argvals st1 decl_h cenv_h Vend st2 o ha hlk hlen hbody ho iha ihbody =>
      intro funs_o code hstrip hO hH hws hcf
      obtain rfl := stripCode_expr_inv hstrip
      obtain ⟨decl, cenv, hlk_o⟩ := lookupFun_of_mem_funNamesEnv hws.1
      obtain ⟨hflat, hsc, hcfb⟩ := goodO_lookup hO hlk_o
      have heq := flatLookup_lifted hflat hH
      rw [hlk] at heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨hdecl, hcenv⟩ := heq; subst hdecl; subst hcenv
      refine Step.callOk (decl := decl) (iha rfl hO hH hws.2 trivial) hlk_o hlen ?_ ho
      exact ihbody rfl (goodO_cenv hO hlk_o) (resEq_flat flatSc) hsc (cif_block_wrap hcfb)
  | @callHalt funs_h V st fn args argvals st1 decl_h cenv_h Vend st2 ha hlk hlen hbody iha ihbody =>
      intro funs_o code hstrip hO hH hws hcf
      obtain rfl := stripCode_expr_inv hstrip
      obtain ⟨decl, cenv, hlk_o⟩ := lookupFun_of_mem_funNamesEnv hws.1
      obtain ⟨hflat, hsc, hcfb⟩ := goodO_lookup hO hlk_o
      have heq := flatLookup_lifted hflat hH
      rw [hlk] at heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨hdecl, hcenv⟩ := heq; subst hdecl; subst hcenv
      exact Step.callHalt (decl := decl) (iha rfl hO hH hws.2 trivial) hlk_o hlen
        (ihbody rfl (goodO_cenv hO hlk_o) (resEq_flat flatSc) hsc (cif_block_wrap hcfb))
  | callArgsHalt ha iha =>
      intro funs_o code hstrip hO hH hws hcf; obtain rfl := stripCode_expr_inv hstrip
      exact Step.callArgsHalt (iha rfl hO hH hws.2 trivial)
  | argsNil => intro funs_o code hstrip hO hH hws hcf; obtain rfl := stripCode_args_inv hstrip; exact Step.argsNil
  | argsCons hrest he ihrest ihe =>
      intro funs_o code hstrip hO hH hws hcf; obtain rfl := stripCode_args_inv hstrip
      exact Step.argsCons (ihrest rfl hO hH hws.2 trivial) (ihe rfl hO hH hws.1 trivial)
  | argsRestHalt hrest ihrest =>
      intro funs_o code hstrip hO hH hws hcf; obtain rfl := stripCode_args_inv hstrip
      exact Step.argsRestHalt (ihrest rfl hO hH hws.2 trivial)
  | argsHeadHalt hrest he ihrest ihe =>
      intro funs_o code hstrip hO hH hws hcf; obtain rfl := stripCode_args_inv hstrip
      exact Step.argsHeadHalt (ihrest rfl hO hH hws.2 trivial) (ihe rfl hO hH hws.1 trivial)
  | funDef =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain ⟨b₀, rfl, _⟩ := stripStmt_funDef_inv hss
      exact Step.funDef
  | block hb ihb =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain ⟨body, rfl, hbody⟩ := stripStmt_block_inv hss
      subst hbody
      refine Step.block ?_
      exact ihb rfl (goodO_push hO (cif_block_inv hcf) hws) (by rw [hoist_stripStmts]; exact resEq_cons_nil hH)
        (by rw [funNamesEnv_hoist_cons]; exact hws) (cif_block_inv hcf)
  | letZero =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain rfl := stripStmt_letDecl_inv hss; exact Step.letZero
  | letVal hv hlen ihv =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain rfl := stripStmt_letDecl_inv hss
      exact Step.letVal (ihv rfl hO hH hws trivial) hlen
  | letHalt hv ihv =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain rfl := stripStmt_letDecl_inv hss
      exact Step.letHalt (ihv rfl hO hH hws trivial)
  | assignVal hv hlen ihv =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain rfl := stripStmt_assign_inv hss
      exact Step.assignVal (ihv rfl hO hH hws trivial) hlen
  | assignHalt hv ihv =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain rfl := stripStmt_assign_inv hss
      exact Step.assignHalt (ihv rfl hO hH hws trivial)
  | exprStmt he ihe =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain rfl := stripStmt_exprStmt_inv hss
      exact Step.exprStmt (ihe rfl hO hH hws trivial)
  | exprStmtHalt he ihe =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain rfl := stripStmt_exprStmt_inv hss
      exact Step.exprStmtHalt (ihe rfl hO hH hws trivial)
  | ifTrue hc hne hbody ihc ihbody =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain ⟨body, rfl, hb⟩ := stripStmt_cond_inv hss; subst hb
      exact Step.ifTrue (ihc rfl hO hH hws.1 trivial) hne
        (ihbody rfl hO hH hws.2 (cif_block_wrap (cif_cond_inv hcf)))
  | ifFalse hc heq ihc =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain ⟨body, rfl, hb⟩ := stripStmt_cond_inv hss; subst hb
      exact Step.ifFalse (ihc rfl hO hH hws.1 trivial) heq
  | ifHalt hc ihc =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain ⟨body, rfl, hb⟩ := stripStmt_cond_inv hss; subst hb
      exact Step.ifHalt (ihc rfl hO hH hws.1 trivial)
  | switchExec hc hbody ihc ihbody =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain ⟨cases, dflt, rfl, hcs, hd⟩ := stripStmt_switch_inv hss; subst hcs; subst hd
      refine Step.switchExec (ihc rfl hO hH hws.1 trivial) ?_
      refine ihbody ?_ hO hH (scopedStmts_selectSwitch hws.2.1 hws.2.2)
        (cif_block_wrap (cif_switch_sel hcf))
      show Code.stmt (Stmt.block (stripStmts (selectSwitch D _ cases dflt))) = _
      rw [← selectSwitch_strip]
  | switchHalt hc ihc =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain ⟨cases, dflt, rfl, hcs, hd⟩ := stripStmt_switch_inv hss; subst hcs; subst hd
      exact Step.switchHalt (ihc rfl hO hH hws.1 trivial)
  | @forLoop funs_h V st init' c post' body' Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain ⟨init, post, body, rfl, hi, hp, hb⟩ := stripStmt_forLoop_inv hss
      subst hi; subst hp; subst hb
      refine Step.forLoop (Vinit := Vinit) (stinit := stinit) ?_ ?_
      · exact ihinit rfl (goodO_push hO (cif_for_init hcf) hws.1)
          (by rw [hoist_stripStmts]; exact resEq_cons_nil hH)
          (by rw [funNamesEnv_hoist_cons]; exact hws.1) (cif_for_init hcf)
      · exact ihloop rfl (goodO_push hO (cif_for_init hcf) hws.1)
          (by rw [hoist_stripStmts]; exact resEq_cons_nil hH)
          (by rw [funNamesEnv_hoist_cons]; exact ⟨hws.2.1, hws.2.2.1, hws.2.2.2⟩)
          ⟨cif_for_post hcf, cif_for_body hcf⟩
  | @forInitHalt funs_h V st init' c post' body' Vinit stinit hinit ihinit =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain ⟨init, post, body, rfl, hi, hp, hb⟩ := stripStmt_forLoop_inv hss
      subst hi; subst hp; subst hb
      refine Step.forInitHalt (Vinit := Vinit) (stinit := stinit) ?_
      exact ihinit rfl (goodO_push hO (cif_for_init hcf) hws.1)
        (by rw [hoist_stripStmts]; exact resEq_cons_nil hH)
        (by rw [funNamesEnv_hoist_cons]; exact hws.1) (cif_for_init hcf)
  | «break» =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain rfl := stripStmt_break_inv hss; exact Step.break
  | «continue» =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain rfl := stripStmt_continue_inv hss; exact Step.continue
  | leave =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨s, rfl, hss⟩ := stripCode_stmt_inv hstrip
      obtain rfl := stripStmt_leave_inv hss; exact Step.leave
  | @seqNil funs_h V st =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨ss, rfl, hss⟩ := stripCode_stmts_inv hstrip
      have hnoop : Step D funs_o V st (.stmts (ss ++ [])) (.sres V st .normal) :=
        (funDefs_noop (stripStmts_nil_inv hss)).mpr Step.seqNil
      rw [List.append_nil] at hnoop; exact hnoop
  | @seqCons funs_h V st s' rest' V1 st1 V2 st2 o hs hrest ihs ihrest =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨ss, rfl, hss⟩ := stripCode_stmts_inv hstrip
      obtain ⟨fds, s, rest, rfl, hfds, hs_eq, hr_eq⟩ := stripStmts_cons_inv hss
      have hwsr := scopedStmts_append_right fds hws
      have hcfr : CodeInFlat flatSc (s :: rest) :=
        codeInFlat_mono (fun x hx => by
          rw [collectStmts_append]; exact List.mem_append.mpr (Or.inr hx)) hcf
      rw [funDefs_noop hfds]
      refine Step.seqCons (V1 := V1) (st1 := st1) ?_ ?_
      · exact ihs (by show Code.stmt (stripStmt s) = _; rw [hs_eq]) hO hH hwsr.1 (cif_head hcfr)
      · exact ihrest (by show Code.stmts (stripStmts rest) = _; rw [hr_eq]) hO hH hwsr.2 (cif_tail hcfr)
  | @seqStop funs_h V st s' rest' V1 st1 o hs hne ihs =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨ss, rfl, hss⟩ := stripCode_stmts_inv hstrip
      obtain ⟨fds, s, rest, rfl, hfds, hs_eq, hr_eq⟩ := stripStmts_cons_inv hss
      have hwsr := scopedStmts_append_right fds hws
      have hcfr : CodeInFlat flatSc (s :: rest) :=
        codeInFlat_mono (fun x hx => by
          rw [collectStmts_append]; exact List.mem_append.mpr (Or.inr hx)) hcf
      rw [funDefs_noop hfds]
      exact Step.seqStop (ihs (by show Code.stmt (stripStmt s) = _; rw [hs_eq]) hO hH hwsr.1 (cif_head hcfr)) hne
  | loopDone hc heq ihc =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨post, body, rfl, hp, hb⟩ := stripCode_loop_inv hstrip; subst hp; subst hb
      exact Step.loopDone (ihc rfl hO hH hws.1 trivial) heq
  | loopCondHalt hc ihc =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨post, body, rfl, hp, hb⟩ := stripCode_loop_inv hstrip; subst hp; subst hb
      exact Step.loopCondHalt (ihc rfl hO hH hws.1 trivial)
  | @loopStep funs_h V st c post' body' cv st1 Vb stb ob Vp stp Vend stend o
      hc hne hbody hob hpost hrec ihc ihbody ihpost ihrec =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨post, body, rfl, hp, hb⟩ := stripCode_loop_inv hstrip; subst hp; subst hb
      refine Step.loopStep (Vb := Vb) (stb := stb) (ob := ob) (Vp := Vp) (stp := stp)
        (ihc rfl hO hH hws.1 trivial) hne ?_ hob ?_ ?_
      · exact ihbody rfl hO hH hws.2.2 (cif_block_wrap hcf.2)
      · exact ihpost rfl hO hH hws.2.1 (cif_block_wrap hcf.1)
      · exact ihrec rfl hO hH hws hcf
  | @loopPostHalt funs_h V st c post' body' cv st1 Vb stb ob Vp stp hc hne hbody hob hpost
      ihc ihbody ihpost =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨post, body, rfl, hp, hb⟩ := stripCode_loop_inv hstrip; subst hp; subst hb
      refine Step.loopPostHalt (Vb := Vb) (stb := stb) (ob := ob)
        (ihc rfl hO hH hws.1 trivial) hne ?_ hob ?_
      · exact ihbody rfl hO hH hws.2.2 (cif_block_wrap hcf.2)
      · exact ihpost rfl hO hH hws.2.1 (cif_block_wrap hcf.1)
  | loopBreak hc hne hbody ihc ihbody =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨post, body, rfl, hp, hb⟩ := stripCode_loop_inv hstrip; subst hp; subst hb
      exact Step.loopBreak (ihc rfl hO hH hws.1 trivial) hne (ihbody rfl hO hH hws.2.2 (cif_block_wrap hcf.2))
  | loopLeave hc hne hbody ihc ihbody =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨post, body, rfl, hp, hb⟩ := stripCode_loop_inv hstrip; subst hp; subst hb
      exact Step.loopLeave (ihc rfl hO hH hws.1 trivial) hne (ihbody rfl hO hH hws.2.2 (cif_block_wrap hcf.2))
  | loopBodyHalt hc hne hbody ihc ihbody =>
      intro funs_o code hstrip hO hH hws hcf
      obtain ⟨post, body, rfl, hp, hb⟩ := stripCode_loop_inv hstrip; subst hp; subst hb
      exact Step.loopBodyHalt (ihc rfl hO hH hws.1 trivial) hne (ihbody rfl hO hH hws.2.2 (cif_block_wrap hcf.2))

theorem step_lift_sim {flatSc : FScope D} {funs_o funs_h : FunEnv D} {code V st res}
    (hO : GoodO flatSc funs_o) (hH : ResEq flatSc funs_h)
    (hws : ScopedCode (funNamesEnv funs_o) code)
    (hcf : CodeInFlatCode flatSc code) :
    Step D funs_o V st code res ↔ Step D funs_h V st (stripCode code) res :=
  ⟨fun h => step_lift_fwd h hO hH hws hcf,
   fun h => step_lift_bwd h rfl hO hH hws hcf⟩

omit [DecidableEq D.Value] in
theorem funNamesTop_cons_other {s : Stmt D.Op} (h : ∀ n ps rs bd, s ≠ .funDef n ps rs bd)
    (rest : List (Stmt D.Op)) : funNamesTop (s :: rest) = funNamesTop rest := by
  cases s with
  | funDef n ps rs bd => exact absurd rfl (h n ps rs bd)
  | _ => simp only [funNamesTop, List.filterMap_cons]

omit [DecidableEq D.Value] in
/-- The top-level function names are a sublist of all function names, so global
uniqueness gives top-level uniqueness. -/
theorem funNamesTop_sublist (b : List (Stmt D.Op)) :
    List.Sublist (funNamesTop b) (funNamesStmts b) := by
  induction b with
  | nil => exact List.nil_sublist _
  | cons s rest ih =>
      have hs : funNamesStmts (s :: rest) = funNamesStmt s ++ funNamesStmts rest := rfl
      rw [hs]
      cases s with
      | funDef n ps rs body =>
          rw [funNamesTop_cons_funDef]
          have hfs : funNamesStmt (.funDef n ps rs body) = n :: funNamesStmts body := rfl
          rw [hfs, List.cons_append]
          exact (ih.trans (List.sublist_append_right _ _)).cons₂ n
      | block _ => rw [funNamesTop_cons_other (by simp)]
                   exact ih.trans (List.sublist_append_right _ _)
      | cond _ _ => rw [funNamesTop_cons_other (by simp)]
                    exact ih.trans (List.sublist_append_right _ _)
      | switch _ _ _ => rw [funNamesTop_cons_other (by simp)]
                        exact ih.trans (List.sublist_append_right _ _)
      | forLoop _ _ _ _ => rw [funNamesTop_cons_other (by simp)]
                           exact ih.trans (List.sublist_append_right _ _)
      | letDecl _ _ => rw [funNamesTop_cons_other (by simp)]
                       exact ih.trans (List.sublist_append_right _ _)
      | assign _ _ => rw [funNamesTop_cons_other (by simp)]
                      exact ih.trans (List.sublist_append_right _ _)
      | exprStmt _ => rw [funNamesTop_cons_other (by simp)]
                      exact ih.trans (List.sublist_append_right _ _)
      | «break» => rw [funNamesTop_cons_other (by simp)]
                   exact ih.trans (List.sublist_append_right _ _)
      | «continue» => rw [funNamesTop_cons_other (by simp)]
                      exact ih.trans (List.sublist_append_right _ _)
      | leave => rw [funNamesTop_cons_other (by simp)]
                 exact ih.trans (List.sublist_append_right _ _)

/-! ### Lookup infrastructure -/

omit [DecidableEq D.Value] in
/-- In a key-`Nodup` association list, a member is exactly what `find?` returns. -/
theorem find?_nodup_mem {β : Type _} {l : List (Ident × β)}
    (hnd : (l.map (·.1)).Nodup) {a : Ident} {v : β} (hmem : (a, v) ∈ l) :
    l.find? (fun p => p.1 = a) = some (a, v) := by
  induction l with
  | nil => simp at hmem
  | cons p rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with h | h
      · subst h; simp [List.find?_cons_of_pos]
      · have hne : p.1 ≠ a := by
          intro heq; exact hnd.1 (heq ▸ (List.mem_map.mpr ⟨(a, v), h, rfl⟩))
        rw [List.find?_cons_of_neg (by simp [hne])]
        exact ih hnd.2 h

/- Names collected by `collectStmts` are exactly the program's function names. -/
mutual
theorem funNamesTop_collectStmt (s : Stmt D.Op) :
    funNamesTop (collectStmt s) = funNamesStmt s := by
  cases s with
  | funDef n ps rs body =>
      rw [collectStmt, funNamesTop_cons_funDef, funNamesTop_collectStmts body]
      simp only [funNamesStmt]
  | block b => rw [collectStmt]; simp only [funNamesStmt]; exact funNamesTop_collectStmts b
  | cond c b => rw [collectStmt]; simp only [funNamesStmt]; exact funNamesTop_collectStmts b
  | switch c cs d =>
      rw [collectStmt, funNamesTop_append, funNamesTop_collectCases cs,
        funNamesTop_collectDflt d]
      simp only [funNamesStmt]
  | forLoop i c p bd =>
      rw [collectStmt, funNamesTop_append, funNamesTop_append,
        funNamesTop_collectStmts i, funNamesTop_collectStmts p, funNamesTop_collectStmts bd]
      simp only [funNamesStmt]
  | letDecl _ _ => rfl
  | assign _ _ => rfl
  | exprStmt _ => rfl
  | «break» => rfl
  | «continue» => rfl
  | leave => rfl
theorem funNamesTop_collectStmts (b : List (Stmt D.Op)) :
    funNamesTop (collectStmts b) = funNamesStmts b := by
  cases b with
  | nil => rfl
  | cons s rest =>
      rw [collectStmts, funNamesTop_append, funNamesTop_collectStmt s,
        funNamesTop_collectStmts rest]
      simp only [funNamesStmts]
theorem funNamesTop_collectCases (cs : List (Literal × Block D.Op)) :
    funNamesTop (collectCases cs) = funNamesCases cs := by
  cases cs with
  | nil => rfl
  | cons p rest =>
      obtain ⟨l, b⟩ := p
      rw [collectCases, funNamesTop_append, funNamesTop_collectStmts b,
        funNamesTop_collectCases rest]
      simp only [funNamesCases]
theorem funNamesTop_collectDflt (d : Option (Block D.Op)) :
    funNamesTop (collectDflt d) = funNamesDflt d := by
  cases d with
  | none => rfl
  | some b => rw [collectDflt]; simp only [funNamesDflt]; exact funNamesTop_collectStmts b
end

omit [DecidableEq D.Value] in
theorem mem_hoist_of_mem {L : List (Stmt D.Op)} {n ps rs bd}
    (h : (Stmt.funDef n ps rs bd) ∈ L) :
    (n, ({ params := ps, rets := rs, body := bd } : FDecl D)) ∈ hoist D L := by
  simp only [hoist, List.mem_filterMap]
  exact ⟨.funDef n ps rs bd, h, rfl⟩

/-- The key fact: under unique names, the flat scope resolves a collected
function's name to exactly its (stripped-body) declaration. -/
theorem flatLookup_of_mem {b : Block D.Op} (huniq : UniqueFunNames b)
    {n ps rs bd} (hmem : (Stmt.funDef n ps rs bd) ∈ collectStmts b) :
    flatLookup (flat b) n = some { params := ps, rets := rs, body := bd } := by
  have hkeys : ((flat b).map (·.1)) = funNamesStmts b := by
    rw [flat, hoist_map_fst, funNamesTop_collectStmts]
  have hnd : ((flat b).map (·.1)).Nodup := by rw [hkeys]; exact huniq
  have hfind := find?_nodup_mem hnd (mem_hoist_of_mem (D := D) hmem)
  simp only [flatLookup, lookupFun_singleton, hfind, Option.map_some]

/-! ### Top-level bridges (base = []) -/

omit [DecidableEq D.Value] in
theorem funNamesEnv_singleton (b : Block D.Op) :
    funNamesEnv (D := D) (hoist D b :: []) = funNamesTop b := by
  simp only [funNamesEnv, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, hoist_map_fst]

/-- At the top block, the original scope stack is `GoodO` for the flat scope. -/
theorem goodO_top {b : Block D.Op} (huniq : UniqueFunNames b) (hws : WellScoped b) :
    GoodO (D := D) (flat b) (hoist D b :: []) := by
  refine ⟨?_, trivial⟩
  intro n d hmem
  obtain ⟨ps, rs, body, hdeq, hfd⟩ := mem_hoist_inv hmem
  refine ⟨?_, ?_, ?_⟩
  · rw [hdeq]
    have : stripDecl (D := D) { params := ps, rets := rs, body := body }
        = { params := ps, rets := rs, body := stripStmts body } := rfl
    rw [this]
    exact flatLookup_of_mem huniq (mem_collectStmts_of_top hfd)
  · rw [hdeq, funNamesEnv_singleton]
    exact scopedStmts_funDef_body hws hfd
  · rw [hdeq]
    intro n' ps' rs' bd' hmem'
    exact flatLookup_of_mem huniq (collectStmts_body_subset hfd hmem')

/-- At the top block, `b`'s functions are all registered in the flat scope. -/
theorem codeInFlat_top {b : Block D.Op} (huniq : UniqueFunNames b) :
    CodeInFlat (D := D) (flat b) b :=
  fun _ _ _ _ hmem => flatLookup_of_mem huniq hmem

/-! ### The equivalence -/

/-- **Hoisting all function definitions to the top preserves whole-program
semantics**, for programs with globally unique function names that are well
scoped. -/
theorem liftFunDefs_run_equiv {b : Block D.Op}
    (huniq : UniqueFunNames b) (hscoped : WellScoped b)
    {st0 : D.State} {V' st' o} :
    Run D b st0 V' st' o ↔ Run D (liftFunDefs b) st0 V' st' o := by
  have simIff : ∀ {r}, Step D (hoist D b :: []) [] st0 (.stmts b) r ↔
      Step D (flat b :: []) [] st0 (.stmts (stripStmts b)) r := by
    intro r
    have hwsEnv : ScopedCode (funNamesEnv (D := D) (hoist D b :: [])) (.stmts b) := by
      rw [funNamesEnv_singleton]; exact hscoped
    exact step_lift_sim (code := .stmts b) (res := r) (goodO_top huniq hscoped)
      (fun _ => rfl) hwsEnv (codeInFlat_top huniq)
  constructor
  · intro h
    cases h with
    | @block _ _ _ _ Vb stb _ hb =>
        refine Step.block ?_
        rw [hoist_liftFunDefs]
        simp only [liftFunDefs]
        rw [funDefs_noop (collectStmts_allFunDef b)]
        exact simIff.mp hb
  · intro h
    cases h with
    | @block _ _ _ _ Vb stb _ hb =>
        refine Step.block ?_
        rw [hoist_liftFunDefs] at hb
        simp only [liftFunDefs] at hb
        rw [funDefs_noop (collectStmts_allFunDef b)] at hb
        exact simIff.mpr hb

end YulEvmCompiler.Optimizer.Normalization
