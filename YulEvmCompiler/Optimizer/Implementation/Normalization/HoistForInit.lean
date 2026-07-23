import YulSemantics.Equiv
import YulEvmCompiler.Optimizer.Spec.LocalPass
import YulEvmCompiler.Optimizer.Implementation.EmptyScope
import YulEvmCompiler.Optimizer.Implementation.Frame
import YulEvmCompiler.Optimizer.Implementation.FunCongr

set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# YulEvmCompiler.Optimizer.Implementation.Normalization.HoistForInit

A single verified pass: **pull the `init` block out of a `for` loop**.

```
for { init } c { post } { body }   ⟿   { init  for {} c { post } { body } }
```

The transform fires only when `init` is a straight-line list of
`let`/`assign`/`exprStmt` statements (`SimpleInit`) — the shape solc emits
(`let i := 0`). That guarantees `init` can only finish `normal` or `halt`, never
`break`/`continue`/`leave` (which the `for` rule does not admit from `init`, so
lifting `init` into the enclosing block would otherwise change behaviour on a
`leave`-in-`init` program). `init` itself is left untouched; `post`/`body`
(and nested `block`/`cond`/`switch`) are recursed into. Function *bodies* are
left unchanged, so the enclosing block's hoisted function scope is preserved and
plain `EquivBlock.of_stmts` suffices (no `FunCongr`).

Soundness is the strong `EquivBlock` `LocalPass` tier. The one subtlety is that the
residual `for {}` still hoists an (empty) function scope, so the loop runs under
one extra `[]` scope; `EmptyScope.Step.emptyExt_congr(')` bridges it.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### Generic sequence-append lemmas (local copies) -/

theorem hfi_append_normal {funs : FunEnv D} {pre suf : List (Stmt D.Op)} {V st V1 st1 Vb st' o}
    (hpre : Step D funs V st (.stmts pre) (.sres V1 st1 .normal))
    (hsuf : Step D funs V1 st1 (.stmts suf) (.sres Vb st' o)) :
    Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o) := by
  induction pre generalizing V st with
  | nil => cases hpre with | seqNil => exact hsuf
  | cons s pre' ih =>
      cases hpre with
      | seqCons hs hpre' => exact Step.seqCons hs (ih hpre')
      | seqStop _ hne => exact absurd rfl hne

theorem hfi_append_early {funs : FunEnv D} {pre suf : List (Stmt D.Op)} {V st Vb st' o}
    (hpre : Step D funs V st (.stmts pre) (.sres Vb st' o)) (hne : o ≠ .normal) :
    Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o) := by
  induction pre generalizing V st with
  | nil => cases hpre with | seqNil => exact absurd rfl hne
  | cons s pre' ih =>
      cases hpre with
      | seqCons hs hpre' => exact Step.seqCons hs (ih hpre')
      | seqStop hs hne' => exact Step.seqStop hs hne'

theorem hfi_append_fwd {funs : FunEnv D} {pre suf : List (Stmt D.Op)} {V st Vb st' o}
    (h : Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o)) :
    (∃ V1 st1, Step D funs V st (.stmts pre) (.sres V1 st1 .normal) ∧
       Step D funs V1 st1 (.stmts suf) (.sres Vb st' o)) ∨
    (o ≠ .normal ∧ Step D funs V st (.stmts pre) (.sres Vb st' o)) := by
  induction pre generalizing V st with
  | nil => exact Or.inl ⟨V, st, Step.seqNil, h⟩
  | cons s pre' ih =>
      rw [List.cons_append] at h
      cases h with
      | seqCons hs htail =>
          rcases ih htail with ⟨V1, st1, hpre', hsuf⟩ | ⟨hne, hpre'⟩
          · exact Or.inl ⟨V1, st1, Step.seqCons hs hpre', hsuf⟩
          · exact Or.inr ⟨hne, Step.seqCons hs hpre'⟩
      | seqStop hs hne => exact Or.inr ⟨hne, Step.seqStop hs hne⟩

theorem hfi_singleton {funs : FunEnv D} {s} {V st V' st' o}
    (h : Step D funs V st (.stmt s) (.sres V' st' o)) :
    Step D funs V st (.stmts [s]) (.sres V' st' o) := by
  by_cases ho : o = .normal
  · subst ho; exact Step.seqCons h Step.seqNil
  · exact Step.seqStop h ho

theorem hfi_singleton_inv {funs : FunEnv D} {s} {V st V' st' o}
    (h : Step D funs V st (.stmts [s]) (.sres V' st' o)) :
    Step D funs V st (.stmt s) (.sres V' st' o) := by
  cases h with
  | seqCons hs htail => cases htail with | seqNil => exact hs
  | seqStop hs _ => exact hs

/-! ### `restore` composition and hoist over the appended `for {}` -/

theorem hfi_restore_restore {V Vinit Vend : VEnv D}
    (h1 : V.length ≤ Vinit.length) (h2 : Vinit.length ≤ Vend.length) :
    restore V (restore Vinit Vend) = restore V Vend := by
  have hlen : (restore Vinit Vend).length = Vinit.length := restore_length h2
  have e1 : restore V (restore Vinit Vend)
      = (restore Vinit Vend).drop ((restore Vinit Vend).length - V.length) := rfl
  have e2 : restore Vinit Vend = Vend.drop (Vend.length - Vinit.length) := rfl
  have e3 : restore V Vend = Vend.drop (Vend.length - V.length) := rfl
  rw [e1, hlen, e2, List.drop_drop, e3]
  congr 1
  omega

omit [DecidableEq D.Value] in
theorem hfi_hoist_append (init : List (Stmt D.Op)) (c : Expr D.Op) (post body : Block D.Op) :
    hoist D (init ++ [.forLoop [] c post body]) = hoist D init := by
  simp only [hoist, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
    List.append_nil]

/-! ### The `SimpleInit` guard and its outcome consequence -/

/-- A statement whose only possible outcomes are `normal`/`halt`. -/
def simpleInitStmt : Stmt D.Op → Bool
  | .letDecl _ _ => true
  | .assign _ _ => true
  | .exprStmt _ => true
  | _ => false

/-- `init` is a straight-line list of declarations/assignments/expression
statements — the shape solc emits for a `for` initializer. -/
def SimpleInit (init : List (Stmt D.Op)) : Bool := init.all simpleInitStmt

theorem simpleStmt_outcome {s : Stmt D.Op} (hs : simpleInitStmt (D := D) s = true)
    {funs : FunEnv D} {V st V' st' o} (h : Step D funs V st (.stmt s) (.sres V' st' o)) :
    o = .normal ∨ o = .halt := by
  cases s with
  | letDecl vars val =>
      cases h with
      | letZero => exact Or.inl rfl
      | letVal _ _ => exact Or.inl rfl
      | letHalt _ => exact Or.inr rfl
  | assign vars e =>
      cases h with
      | assignVal _ _ => exact Or.inl rfl
      | assignHalt _ => exact Or.inr rfl
  | exprStmt e =>
      cases h with
      | exprStmt _ => exact Or.inl rfl
      | exprStmtHalt _ => exact Or.inr rfl
  | block b => simp [simpleInitStmt] at hs
  | funDef n ps rs b => simp [simpleInitStmt] at hs
  | cond cc b => simp [simpleInitStmt] at hs
  | switch cc cs d => simp [simpleInitStmt] at hs
  | forLoop i cc p b => simp [simpleInitStmt] at hs
  | «break» => simp [simpleInitStmt] at hs
  | «continue» => simp [simpleInitStmt] at hs
  | leave => simp [simpleInitStmt] at hs

theorem simpleInit_outcome {init : List (Stmt D.Op)} (hsimple : SimpleInit (D := D) init = true)
    {funs : FunEnv D} {V st V' st' o} (h : Step D funs V st (.stmts init) (.sres V' st' o)) :
    o = .normal ∨ o = .halt := by
  induction init generalizing V st with
  | nil => cases h with | seqNil => exact Or.inl rfl
  | cons s rest ih =>
      simp only [SimpleInit, List.all_cons, Bool.and_eq_true] at hsimple
      obtain ⟨hhead, htail⟩ := hsimple
      cases h with
      | seqCons _ hrest => exact ih (by simp [SimpleInit, htail]) hrest
      | seqStop hs hne => exact simpleStmt_outcome hhead hs

/-! ### The core statement equivalence -/

/-- Pulling a `SimpleInit` `init` out of a `for` loop into an enclosing block is
semantics-preserving. `post`/`body` are arbitrary (already-transformed) blocks. -/
theorem hoistForInit_core {init : List (Stmt D.Op)} (c : Expr D.Op) (post body : Block D.Op)
    (hsimple : SimpleInit (D := D) init = true) :
    EquivStmt D (.forLoop init c post body) (.block (init ++ [.forLoop [] c post body])) := by
  intro funs V st Vres st' o
  constructor
  · -- forward: for-loop ⟹ block
    intro h
    cases h with
    | @forLoop _ _ _ _ _ _ _ Vinit _ Vend _ _ hinit hloop =>
        have hkey : restore V (restore Vinit Vend) = restore V Vend :=
          hfi_restore_restore (venvLen_mono hinit rfl) (venvLen_mono hloop rfl)
        have hinner : Step D (hoist D init :: funs) V st
            (.stmts (init ++ [Stmt.forLoop [] c post body]))
            (.sres (restore Vinit Vend) st' o) := by
          refine hfi_append_normal hinit (hfi_singleton ?_)
          exact Step.forLoop Step.seqNil
            (Step.emptyExt_congr hloop (EmptyExt.head (hoist D init :: funs)))
        have hblk := Step.block (by rw [hfi_hoist_append]; exact hinner)
        rw [hkey] at hblk
        exact hblk
    | @forInitHalt _ _ _ _ _ _ _ Vinit _ hinit =>
        have hinner : Step D (hoist D init :: funs) V st
            (.stmts (init ++ [Stmt.forLoop [] c post body]))
            (.sres Vinit st' .halt) :=
          hfi_append_early hinit (by decide)
        exact Step.block (by rw [hfi_hoist_append]; exact hinner)
  · -- backward: block ⟹ for-loop
    intro h
    cases h with
    | @block _ _ _ _ Vb _ _ hb =>
        rw [hfi_hoist_append] at hb
        rcases hfi_append_fwd hb with ⟨V1, st1, hinit, hsuf⟩ | ⟨hne, hinit⟩
        · have hfl0 := hfi_singleton_inv hsuf
          cases hfl0 with
          | @forLoop _ _ _ _ _ _ _ _ _ Vend' _ _ hinit0 hloop0 =>
              cases hinit0 with
              | seqNil =>
                  have hloopH := Step.emptyExt_congr' hloop0 (EmptyExt.head (hoist D init :: funs))
                  have hkey : restore V (restore V1 Vend') = restore V Vend' :=
                    hfi_restore_restore (venvLen_mono hinit rfl) (venvLen_mono hloopH rfl)
                  rw [hkey]
                  exact Step.forLoop hinit hloopH
          | @forInitHalt _ _ _ _ _ _ _ _ _ hinit0 => cases hinit0
        · have ho : o = .halt := by
            rcases simpleInit_outcome hsimple hinit with h1 | h1
            · exact absurd h1 hne
            · exact h1
          subst ho
          exact Step.forInitHalt hinit

/-! ### The transform -/

mutual

/-- Pull the `init` out of every non-empty `SimpleInit` `for` loop, recursing
into `post`/`body`, nested `block`/`cond`/`switch`, and **`funDef` bodies**.
Only a `for`-loop's own `init` is left untouched. -/
def hoistInitStmt : Stmt D.Op → Stmt D.Op
  | .forLoop init c post body =>
      if SimpleInit init && !init.isEmpty
      then .block (init ++ [.forLoop [] c (hoistInitStmts post) (hoistInitStmts body)])
      else .forLoop init c (hoistInitStmts post) (hoistInitStmts body)
  | .block b => .block (hoistInitStmts b)
  | .cond c b => .cond c (hoistInitStmts b)
  | .switch c cases dflt => .switch c (hoistInitCases cases) (hoistInitDflt dflt)
  | .funDef n ps rs b => .funDef n ps rs (hoistInitStmts b)
  | .letDecl vars val => .letDecl vars val
  | .assign vars e => .assign vars e
  | .exprStmt e => .exprStmt e
  | .break => .break
  | .continue => .continue
  | .leave => .leave

def hoistInitStmts : List (Stmt D.Op) → List (Stmt D.Op)
  | [] => []
  | s :: rest => hoistInitStmt s :: hoistInitStmts rest

def hoistInitCases : List (Literal × Block D.Op) → List (Literal × Block D.Op)
  | [] => []
  | (l, b) :: rest => (l, hoistInitStmts b) :: hoistInitCases rest

def hoistInitDflt : Option (Block D.Op) → Option (Block D.Op)
  | none => none
  | some b => some (hoistInitStmts b)

end

/-! ### Generic helpers -/

omit [DecidableEq D.Value] in
theorem hoist_cons (x : Stmt D.Op) (l : List (Stmt D.Op)) :
    hoist D (x :: l) = hoist D [x] ++ hoist D l := by
  cases x <;> rfl

omit [DecidableEq D.Value] in
theorem forall2_append {α β} {R : α → β → Prop} {a a' b b' : List _}
    (h1 : List.Forall₂ R a a') (h2 : List.Forall₂ R b b') :
    List.Forall₂ R (a ++ b) (a' ++ b') := by
  induction h1 with
  | nil => exact h2
  | cons hx _ ih => exact .cons hx ih

/-- A `funDef` executes as a no-op regardless of its body, so two `funDef`s with
the same signature are equivalent *as statements* whatever their bodies (body
differences matter only through the enclosing block's `hoist`, handled by
`scopeRel_hoistForInit`). -/
theorem hfi_funDef_equiv (n : Ident) (ps rs : List Ident) (b₁ b₂ : Block D.Op) :
    EquivStmt D (.funDef n ps rs b₁) (.funDef n ps rs b₂) := by
  intro funs V st V' st' o
  constructor <;> (intro h; cases h; exact Step.funDef)

omit [DecidableEq D.Value] in
/-- Recover `SimpleInit init` from the transform's firing condition. -/
theorem simpleInit_of_cond {init : List (Stmt D.Op)}
    (hcond : (SimpleInit (D := D) init && !init.isEmpty) = true) : SimpleInit (D := D) init = true := by
  cases hh : SimpleInit (D := D) init with
  | true => rfl
  | false => rw [hh, Bool.false_and] at hcond; exact absurd hcond (by decide)

/-! ### Soundness -/

mutual

theorem hoistInitStmt_equiv : ∀ s : Stmt D.Op, EquivStmt D s (hoistInitStmt s)
  | .forLoop init c post body => by
      have hpost : EquivBlock D post (hoistInitStmts post) :=
        EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (hoistInitStmts_forall2 post))
          (scopeRel_hoistForInit post)
      have hbody : EquivBlock D body (hoistInitStmts body) :=
        EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (hoistInitStmts_forall2 body))
          (scopeRel_hoistForInit body)
      simp only [hoistInitStmt]
      split
      · rename_i hcond
        have hsimple : SimpleInit init = true := simpleInit_of_cond hcond
        exact (EquivStmt.forLoop_congr init (EquivExpr.refl c) hpost hbody).trans
          (hoistForInit_core c (hoistInitStmts post) (hoistInitStmts body) hsimple)
      · exact EquivStmt.forLoop_congr init (EquivExpr.refl c) hpost hbody
  | .block b =>
      EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (hoistInitStmts_forall2 b))
        (scopeRel_hoistForInit b)
  | .cond c b =>
      EquivStmt.cond_congr (EquivExpr.refl c)
        (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (hoistInitStmts_forall2 b))
          (scopeRel_hoistForInit b))
  | .switch c cases dflt => by
      have hsw : EquivStmt D (.switch c cases dflt)
          (.switch c (hoistInitCases cases) (hoistInitDflt dflt)) := by
        apply EquivStmt.switch_congr (EquivExpr.refl c) (hoistInitCases_forall2 cases)
        cases dflt with
        | none => exact EquivBlock.refl _
        | some b =>
            exact EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (hoistInitStmts_forall2 b))
              (scopeRel_hoistForInit b)
      simpa only [hoistInitStmt] using hsw
  | .funDef n ps rs b => by
      simp only [hoistInitStmt]; exact hfi_funDef_equiv n ps rs b (hoistInitStmts b)
  | .letDecl vars val => by simp only [hoistInitStmt]; exact EquivStmt.refl _
  | .assign vars e => by simp only [hoistInitStmt]; exact EquivStmt.refl _
  | .exprStmt e => by simp only [hoistInitStmt]; exact EquivStmt.refl _
  | .break => by simp only [hoistInitStmt]; exact EquivStmt.refl _
  | .continue => by simp only [hoistInitStmt]; exact EquivStmt.refl _
  | .leave => by simp only [hoistInitStmt]; exact EquivStmt.refl _

theorem hoistInitStmts_forall2 : ∀ ss : List (Stmt D.Op),
    List.Forall₂ (EquivStmt D) ss (hoistInitStmts ss)
  | [] => .nil
  | s :: rest => .cons (hoistInitStmt_equiv s) (hoistInitStmts_forall2 rest)

theorem hoistInitCases_forall2 : ∀ cs : List (Literal × Block D.Op),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs (hoistInitCases cs)
  | [] => .nil
  | (_, b) :: rest =>
      .cons ⟨rfl, EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (hoistInitStmts_forall2 b))
        (scopeRel_hoistForInit b)⟩ (hoistInitCases_forall2 rest)

theorem hfi_scopeRel_single : ∀ s : Stmt D.Op,
    ScopeRel D (hoist D [s]) (hoist D [hoistInitStmt s])
  | .funDef n ps rs b => by
      simp only [hoistInitStmt]
      exact List.Forall₂.cons
        ⟨rfl, rfl, rfl,
          EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (hoistInitStmts_forall2 b))
            (scopeRel_hoistForInit b)⟩ .nil
  | .forLoop i cc p bd => by simp only [hoistInitStmt]; split <;> exact .nil
  | .block bd => by simp only [hoistInitStmt]; exact .nil
  | .cond cc bd => by simp only [hoistInitStmt]; exact .nil
  | .switch cc cs d => by simp only [hoistInitStmt]; exact .nil
  | .letDecl vars val => by simp only [hoistInitStmt]; exact .nil
  | .assign vars e => by simp only [hoistInitStmt]; exact .nil
  | .exprStmt e => by simp only [hoistInitStmt]; exact .nil
  | .break => by simp only [hoistInitStmt]; exact .nil
  | .continue => by simp only [hoistInitStmt]; exact .nil
  | .leave => by simp only [hoistInitStmt]; exact .nil

theorem scopeRel_hoistForInit : ∀ ss : List (Stmt D.Op),
    ScopeRel D (hoist D ss) (hoist D (hoistInitStmts ss))
  | [] => .nil
  | s :: rest => by
      simp only [hoistInitStmts]
      rw [hoist_cons s rest, hoist_cons (hoistInitStmt s) (hoistInitStmts rest)]
      exact forall2_append (hfi_scopeRel_single s) (scopeRel_hoistForInit rest)

end

/-- A block is equivalent to its transform. -/
theorem hoistForInit_blockEquiv (b : List (Stmt D.Op)) : EquivBlock D b (hoistInitStmts b) :=
  EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (hoistInitStmts_forall2 b))
    (scopeRel_hoistForInit b)

/-- The **hoist-for-init pass**: pull a non-empty `SimpleInit` initializer out of
every `for` loop (throughout, including function bodies), bundled with its
soundness proof. -/
def hoistForInit : LocalPass D where
  run := hoistInitStmts
  sound := hoistForInit_blockEquiv

/-! ### Normal form: every reachable `for` loop has its `init` hoisted

`ForInitOK` says every `for` loop reached without descending into another loop's
`init` has an already-hoisted initializer — `SimpleInit init → init = []`, i.e.
no non-empty simple init survives (that is exactly what the pass removes). It
recurses into `post`/`body`, nested `block`/`cond`/`switch`, and `funDef`
bodies — the same positions the transform rewrites. -/

mutual
def ForInitOK : Stmt D.Op → Prop
  | .forLoop init _ post body =>
      (SimpleInit init = true → init = []) ∧ ForInitOKs post ∧ ForInitOKs body
  | .block b => ForInitOKs b
  | .cond _ b => ForInitOKs b
  | .switch _ cases dflt => ForInitOKsCases cases ∧ ForInitOKsDflt dflt
  | .funDef _ _ _ b => ForInitOKs b
  | _ => True
def ForInitOKs : List (Stmt D.Op) → Prop
  | [] => True
  | s :: rest => ForInitOK s ∧ ForInitOKs rest
def ForInitOKsCases : List (Literal × Block D.Op) → Prop
  | [] => True
  | (_, b) :: rest => ForInitOKs b ∧ ForInitOKsCases rest
def ForInitOKsDflt : Option (Block D.Op) → Prop
  | none => True
  | some b => ForInitOKs b
end

omit [DecidableEq D.Value] in
theorem forInitOKs_append : ∀ {a b : List (Stmt D.Op)},
    ForInitOKs a → ForInitOKs b → ForInitOKs (a ++ b)
  | [], _, _, hb => hb
  | _ :: _, _, ha, hb => by
      simp only [List.cons_append, ForInitOKs] at ha ⊢
      exact ⟨ha.1, forInitOKs_append ha.2 hb⟩

/-- A `SimpleInit` list is all leaves, so it trivially satisfies the normal form. -/
theorem simpleInit_forInitOKs {init : List (Stmt D.Op)}
    (h : SimpleInit (D := D) init = true) : ForInitOKs (D := D) init := by
  induction init with
  | nil => exact True.intro
  | cons s rest ih =>
      simp only [SimpleInit, List.all_cons, Bool.and_eq_true] at h
      refine ⟨?_, ih (by simp [SimpleInit, h.2])⟩
      obtain ⟨hhead, _⟩ := h
      cases s with
      | letDecl _ _ => exact True.intro
      | assign _ _ => exact True.intro
      | exprStmt _ => exact True.intro
      | block _ => simp [simpleInitStmt] at hhead
      | funDef _ _ _ _ => simp [simpleInitStmt] at hhead
      | cond _ _ => simp [simpleInitStmt] at hhead
      | switch _ _ _ => simp [simpleInitStmt] at hhead
      | forLoop _ _ _ _ => simp [simpleInitStmt] at hhead
      | «break» => simp [simpleInitStmt] at hhead
      | «continue» => simp [simpleInitStmt] at hhead
      | leave => simp [simpleInitStmt] at hhead

mutual
theorem forInitOK_hoistInitStmt : ∀ s : Stmt D.Op, ForInitOK (hoistInitStmt s)
  | .forLoop init c post body => by
      simp only [hoistInitStmt]
      split
      · rename_i hcond
        have hsimple : SimpleInit init = true := simpleInit_of_cond hcond
        exact forInitOKs_append (simpleInit_forInitOKs hsimple)
          ⟨⟨fun _ => rfl, forInitOK_hoistInitStmts post, forInitOK_hoistInitStmts body⟩, True.intro⟩
      · rename_i hcond
        refine ⟨?_, forInitOK_hoistInitStmts post, forInitOK_hoistInitStmts body⟩
        intro hs
        by_contra hne
        apply hcond
        have hie : init.isEmpty = false := by
          cases init with
          | nil => exact absurd rfl hne
          | cons => rfl
        simp [hs, hie]
  | .block b => forInitOK_hoistInitStmts b
  | .cond c b => forInitOK_hoistInitStmts b
  | .switch c cases dflt => ⟨forInitOK_hoistInitCases cases, forInitOK_hoistInitDflt dflt⟩
  | .funDef n ps rs b => forInitOK_hoistInitStmts b
  | .letDecl _ _ => True.intro
  | .assign _ _ => True.intro
  | .exprStmt _ => True.intro
  | .break => True.intro
  | .continue => True.intro
  | .leave => True.intro
theorem forInitOK_hoistInitStmts : ∀ ss : List (Stmt D.Op), ForInitOKs (hoistInitStmts ss)
  | [] => True.intro
  | s :: rest => ⟨forInitOK_hoistInitStmt s, forInitOK_hoistInitStmts rest⟩
theorem forInitOK_hoistInitCases : ∀ cs : List (Literal × Block D.Op),
    ForInitOKsCases (hoistInitCases cs)
  | [] => True.intro
  | (_, b) :: rest => ⟨forInitOK_hoistInitStmts b, forInitOK_hoistInitCases rest⟩
theorem forInitOK_hoistInitDflt : ∀ d : Option (Block D.Op), ForInitOKsDflt (hoistInitDflt d)
  | none => True.intro
  | some b => forInitOK_hoistInitStmts b
end

/-- **The transform normalizes every reachable `for` loop**: after
`hoistForInit`, no `for` loop (outside another loop's initializer) has a
non-empty `SimpleInit` init. -/
theorem hoistForInit_forInitOK (b : List (Stmt D.Op)) :
    ForInitOKs (D := D) (hoistForInit.run b) :=
  forInitOK_hoistInitStmts b



