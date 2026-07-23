import YulEvmCompiler.Optimizer.Implementation.Normalization.FlattenBlocks
import YulEvmCompiler.Optimizer.Implementation.DeadLits
import YulEvmCompiler.Optimizer.Implementation.StackLayoutSound
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.Normalization.FlattenBlocksSound

Semantic soundness of the block-flattening transform (`FlattenBlocks.flattenBlock`):
under the normal-form preconditions it establishes an `EquivBlock`, so it composes
with the verified backend.

## Why this is a *conditional* soundness theorem (not a bare `LocalPass`)

Flattening is **not** unconditionally semantics-preserving, so it does not fit the
unconditional `Optimizer.LocalPass` obligation `∀ b, EquivBlock D b (run b)`.
Two failure modes on ill-formed input:

* **Variables.** `{ { let z := 1 } use(z) }` is ill-scoped in the original (the
  outer `use(z)` cannot see the inner `z`, so it is stuck), yet the flattened
  `{ let z := 1 use(z) }` runs. Preserving `↔` therefore needs `WellScoped`.
* **Functions.** A `funDef` nested inside a block would, after flattening, move
  into the enclosing block's hoisted scope (`hoist`), a genuine scope
  restructuring. Requiring `FunctionsHoisted` rules this out: every block that
  gets spliced is then funDef-free, so its `hoist` is empty and the only
  function-environment change is the insertion/removal of **empty** scopes —
  handled by the existing `EmptyScopeRel` / `Step.emptyScope_congr`.

The leaked-variable reasoning (an inner block's locals surviving into the rest of
the enclosing block) is discharged by `UniqueNames`: the trailing statements
never mention those names, so `Frame.frameAdd`/`frameRemove` transport the
derivation, and `restore_insAt_le` aligns the block-exit `restore`.

So the target is:

```
flattenBlock_sound :
  WellScoped b → UniqueNames b → FunctionsHoisted b → EquivBlock D b (flattenBlock b)
```

which is exactly the "requires and re-establishes normal-form fields" discipline
(`NormalForm`): a pipeline runs disambiguation + function hoisting first, and
flattening consumes those guarantees.

This file is built bottom-up; see the section markers for the proof layers.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer.NormalForm
open YulEvmCompiler.Optimizer.Flatten

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ## Bridge: a funDef-free block has an empty hoisted scope

`FunctionsHoisted` guarantees that every block reached by flattening (nested
inside conditionals, loops, switch cases, or a bare block) contains no function
definitions. For such a block `hoist D body = []`, so removing its wrapper only
deletes an *empty* function scope — the case `EmptyScopeRel` covers. -/

theorem hoist_eq_nil_of_noFunDef {ss : List (Stmt Op)}
    (h : NoFunDefStmts ss) : hoist D ss = [] := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
      have hrest := ih h.2
      have h1 := h.1
      cases s <;> simp_all [hoist, NoFunDefStmt]

/-- A funDef-free block hoists no function *names* either. -/
theorem funDefNames_nil_of_noFunDef {ss : List (Stmt Op)}
    (h : NoFunDefStmts ss) : funDefNames ss = [] := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
      have hrest := ih h.2
      have h1 := h.1
      cases s <;> simp_all [funDefNames, funDefName?, NoFunDefStmt]

/-! ## Bridge: flattening preserves funDef-freeness

So a funDef-free block stays funDef-free after flattening; combined with the
previous lemma, both a spliced block and its flattening have empty `hoist`. -/

theorem noFunDefStmts_append {a b : List (Stmt Op)}
    (ha : NoFunDefStmts a) (hb : NoFunDefStmts b) : NoFunDefStmts (a ++ b) := by
  induction a with
  | nil => simpa using hb
  | cons s rest ih => exact ⟨ha.1, ih ha.2⟩

mutual
theorem noFunDef_flattenStmt {s : Stmt Op} (h : NoFunDefStmt s) :
    NoFunDefStmts (flattenStmt s) := by
  cases s with
  | funDef n ps rs body => exact absurd h (by simp [NoFunDefStmt])
  | block body =>
      simpa [flattenStmt] using noFunDef_flattenStmts (by simpa [NoFunDefStmt] using h)
  | cond c body =>
      simp only [flattenStmt, NoFunDefStmts, NoFunDefStmt, and_true]
      exact noFunDef_flattenStmts (by simpa [NoFunDefStmt] using h)
  | «switch» c cs d =>
      simp only [flattenStmt, NoFunDefStmts, NoFunDefStmt, and_true]
      exact ⟨noFunDef_flattenCases (by simpa [NoFunDefStmt] using h.1),
             noFunDef_flattenDflt (by simpa [NoFunDefStmt] using h.2)⟩
  | forLoop i c p b =>
      simp only [flattenStmt, NoFunDefStmts, NoFunDefStmt, and_true]
      obtain ⟨hi, hp, hb⟩ := (by simpa [NoFunDefStmt] using h :
        NoFunDefStmts i ∧ NoFunDefStmts p ∧ NoFunDefStmts b)
      exact ⟨noFunDef_flattenStmts hi, noFunDef_flattenStmts hp, noFunDef_flattenStmts hb⟩
  | letDecl vars v => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
  | assign vars v => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
  | exprStmt e => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
  | «break» => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
  | «continue» => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
  | «leave» => simp [flattenStmt, NoFunDefStmts, NoFunDefStmt]
theorem noFunDef_flattenStmts {ss : List (Stmt Op)} (h : NoFunDefStmts ss) :
    NoFunDefStmts (flattenStmts ss) := by
  cases ss with
  | nil => trivial
  | cons s rest =>
      simp only [flattenStmts]
      exact noFunDefStmts_append (noFunDef_flattenStmt h.1) (noFunDef_flattenStmts h.2)
theorem noFunDef_flattenCases {cs : List (Literal × List (Stmt Op))}
    (h : NoFunDefCases cs) : NoFunDefCases (flattenCases cs) := by
  cases cs with
  | nil => trivial
  | cons hd tl =>
      obtain ⟨l, b⟩ := hd
      exact ⟨noFunDef_flattenStmts h.1, noFunDef_flattenCases h.2⟩
theorem noFunDef_flattenDflt {d : Option (List (Stmt Op))}
    (h : NoFunDefDflt d) : NoFunDefDflt (flattenDflt d) := by
  cases d with
  | none => trivial
  | some b => simpa [flattenDflt, NoFunDefDflt] using noFunDef_flattenStmts h

end

/-- Both a funDef-free block and its flattening have an empty hoisted scope. -/
theorem hoist_flatten_eq_nil {ss : List (Stmt Op)} (h : NoFunDefStmts ss) :
    hoist D (flattenStmts ss) = [] :=
  hoist_eq_nil_of_noFunDef (noFunDef_flattenStmts h)

/-! ## Unwrapping a funDef-free block

Executing a bare `block body` whose `body` is funDef-free is exactly executing
`body`'s statements inline (its hoisted scope is empty, transparent by
`EmptyScopeRel`), with the block's exit `restore` made explicit. This is the
seam that flattening removes. -/

theorem block_unwrap {funs : FunEnv D} {V st V' st' o} {body : List (Stmt Op)}
    (hnf : NoFunDefStmts body) :
    Step D funs V st (.stmt (.block body)) (.sres V' st' o) ↔
      ∃ Vb, V' = restore V Vb ∧ Step D funs V st (.stmts body) (.sres Vb st' o) := by
  have hh : hoist D body = [] := hoist_eq_nil_of_noFunDef hnf
  constructor
  · intro h
    cases h with
    | block hbody =>
        rw [hh] at hbody
        exact ⟨_, rfl, Step.emptyScope_congr hbody (EmptyScopeRel.drop funs)⟩
  · rintro ⟨Vb, rfl, hbody⟩
    have hpush : Step D ([] :: funs) V st (.stmts body) (.sres Vb st' o) :=
      Step.emptyScope_congr hbody (EmptyScopeRel.add funs)
    rw [← hh] at hpush
    exact Step.block hpush

/-! ## Framing an unmentioned prefix

The leaked locals of a spliced block form a prefix prepended above the block's
base environment. If a statement list mentions none of those names, running it
from the extended environment mirrors running it from the base — and, crucially,
`restore` to the base drops the same frame on both sides (each inserted binding
sits at depth ≥ the base length, so `restore_insAt_le` erases it). Proved by
iterating the single-variable `frameAdd`. -/

theorem framePrefixAdd_stmts {funs : FunEnv D} {ss : List (Stmt Op)} {V st Vb st' o}
    (h : Step D funs V st (.stmts ss) (.sres Vb st' o)) :
    ∀ (pre : VEnv D), (∀ p ∈ pre, stmtsMentions p.1 ss = false) →
      ∃ Vb', Step D funs (pre ++ V) st (.stmts ss) (.sres Vb' st' o) ∧
        restore V Vb = restore V Vb' := by
  intro pre
  induction pre with
  | nil => intro _; exact ⟨Vb, by simpa using h, rfl⟩
  | cons p pre' ih =>
      intro hm
      obtain ⟨Vb'', hstep'', hres''⟩ := ih (fun q hq => hm q (List.mem_cons_of_mem _ hq))
      have hins : InsAt (pre' ++ V).length p.1 p.2 (pre' ++ V) ((p.1, p.2) :: (pre' ++ V)) :=
        ⟨[], pre' ++ V, rfl, rfl, rfl⟩
      have hmp : codeMentions p.1 (Code.stmts ss) = false := by
        simpa [codeMentions] using hm p (by simp)
      obtain ⟨res2, hstep2, hrel⟩ := frameAdd hstep'' hins hmp
      obtain ⟨Vb3, rfl, hins3⟩ := hrel.sres
      refine ⟨Vb3, ?_, ?_⟩
      · have : ((p.1, p.2) :: (pre' ++ V)) = (p :: pre') ++ V := by simp
        rwa [this] at hstep2
      · rw [hres'']
        exact restore_insAt_le hins3 (by simp)

/-- Backward companion of `framePrefixAdd_stmts`: running a statement list from an
environment extended by an unmentioned prefix can be re-based to the shorter
environment, preserving `restore` to that base. -/
theorem framePrefixRemove_stmts {funs : FunEnv D} {ss : List (Stmt Op)} {V st st' o} :
    ∀ (pre : VEnv D) {Vb' : VEnv D},
    Step D funs (pre ++ V) st (.stmts ss) (.sres Vb' st' o) →
    (∀ p ∈ pre, stmtsMentions p.1 ss = false) →
    ∃ Vb, Step D funs V st (.stmts ss) (.sres Vb st' o) ∧ restore V Vb' = restore V Vb := by
  intro pre
  induction pre with
  | nil => intro Vb' h _; exact ⟨Vb', by simpa using h, rfl⟩
  | cons p pre' ih =>
      intro Vb' h hm
      have hins : InsAt (pre' ++ V).length p.1 p.2 (pre' ++ V) ((p.1, p.2) :: (pre' ++ V)) :=
        ⟨[], pre' ++ V, rfl, rfl, rfl⟩
      have hmp : codeMentions p.1 (Code.stmts ss) = false := by
        simpa [codeMentions] using hm p (by simp)
      have h' : Step D funs ((p.1, p.2) :: (pre' ++ V)) st (.stmts ss) (.sres Vb' st' o) := by
        have he : ((p.1, p.2) :: (pre' ++ V)) = (p :: pre') ++ V := by simp
        rw [he]; exact h
      obtain ⟨res1, hstep1, hrel⟩ := frameRemove h' hins hmp
      obtain ⟨Vb1, rfl, hins1⟩ := hrel.sres_right
      obtain ⟨Vb, hstepV, hres⟩ := ih hstep1 (fun q hq => hm q (List.mem_cons_of_mem _ hq))
      exact ⟨Vb, hstepV, (restore_insAt_le hins1 (by simp)).symm.trans hres⟩

/-! ## Flattening preserves `mentions`

Flattening relocates statements but neither adds nor removes a variable use or
declaration, so a name is mentioned in the flattening iff it is mentioned in the
original. Hence "unmentioned by `rest`" transfers to `flattenStmts rest`. -/

theorem stmtsMentions_append {x : Ident} {a b : List (Stmt Op)} :
    stmtsMentions x (a ++ b) = (stmtsMentions x a || stmtsMentions x b) := by
  induction a with
  | nil => simp [stmtsMentions]
  | cons s rest ih => simp [stmtsMentions, ih, Bool.or_assoc]

mutual
theorem mentions_flattenStmt {x : Ident} (s : Stmt Op) :
    stmtsMentions x (flattenStmt s) = stmtMentions x s := by
  cases s with
  | block body => simpa [flattenStmt, stmtMentions] using mentions_flattenStmts (x := x) body
  | funDef n ps rs body =>
      simp [flattenStmt, stmtsMentions, stmtMentions, mentions_flattenStmts (x := x) body]
  | cond c body =>
      simp [flattenStmt, stmtsMentions, stmtMentions, mentions_flattenStmts (x := x) body]
  | «switch» c cs d =>
      simp [flattenStmt, stmtsMentions, stmtMentions, mentions_flattenCases (x := x) cs,
            mentions_flattenDflt (x := x) d]
  | forLoop i c p b =>
      simp [flattenStmt, stmtsMentions, stmtMentions, mentions_flattenStmts (x := x) i,
            mentions_flattenStmts (x := x) p, mentions_flattenStmts (x := x) b]
  | letDecl vars v => simp [flattenStmt, stmtsMentions, stmtMentions]
  | assign vars v => simp [flattenStmt, stmtsMentions, stmtMentions]
  | exprStmt e => simp [flattenStmt, stmtsMentions, stmtMentions]
  | «break» => simp [flattenStmt, stmtsMentions, stmtMentions]
  | «continue» => simp [flattenStmt, stmtsMentions, stmtMentions]
  | «leave» => simp [flattenStmt, stmtsMentions, stmtMentions]
theorem mentions_flattenStmts {x : Ident} (ss : List (Stmt Op)) :
    stmtsMentions x (flattenStmts ss) = stmtsMentions x ss := by
  cases ss with
  | nil => rfl
  | cons s rest =>
      simp [flattenStmts, stmtsMentions_append, mentions_flattenStmt (x := x) s,
            mentions_flattenStmts (x := x) rest, stmtsMentions]
theorem mentions_flattenCases {x : Ident} (cs : List (Literal × List (Stmt Op))) :
    casesMentions x (flattenCases cs) = casesMentions x cs := by
  cases cs with
  | nil => rfl
  | cons hd tl =>
      obtain ⟨l, b⟩ := hd
      simp [flattenCases, casesMentions, mentions_flattenStmts (x := x) b,
            mentions_flattenCases (x := x) tl]
theorem mentions_flattenDflt {x : Ident} (d : Option (List (Stmt Op))) :
    optBlockMentions x (flattenDflt d) = optBlockMentions x d := by
  cases d with
  | none => rfl
  | some b => simpa [flattenDflt, optBlockMentions] using mentions_flattenStmts (x := x) b
end

/-! ## Well-scoped ⇒ every mentioned name is in scope or locally declared

Bridge from the `NormalForm.WellScoped` precondition to `mentions`: if a name is
mentioned (used or declared) in a well-scoped statement list, it is either in the
incoming variable scope `vs` or declared somewhere in the list. Consequently a
name declared *inside* a sibling block (hence not in `vs`, by uniqueness) and not
declared in the list is not mentioned — the fact the frame step needs. -/

mutual
theorem scopedExpr_mentions {vs fs : List Ident} {x : Ident} {e : Expr Op}
    (hsc : ScopedExpr vs fs e) (hm : exprMentions x e = true) : x ∈ vs := by
  cases e with
  | lit l => simp [exprMentions] at hm
  | var y =>
      simp only [exprMentions] at hm
      have : x = y := by simpa using hm
      subst this; simpa [ScopedExpr] using hsc
  | builtin op args =>
      exact scopedArgs_mentions (by simpa [ScopedExpr] using hsc) (by simpa [exprMentions] using hm)
  | call fn args =>
      simp only [ScopedExpr] at hsc
      exact scopedArgs_mentions hsc.2 (by simpa [exprMentions] using hm)
theorem scopedArgs_mentions {vs fs : List Ident} {x : Ident} {es : List (Expr Op)}
    (hsc : ScopedArgs vs fs es) (hm : argsMentions x es = true) : x ∈ vs := by
  cases es with
  | nil => simp [argsMentions] at hm
  | cons e rest =>
      simp only [ScopedArgs] at hsc
      simp only [argsMentions, Bool.or_eq_true] at hm
      rcases hm with h | h
      · exact scopedExpr_mentions hsc.1 h
      · exact scopedArgs_mentions hsc.2 h
end

theorem declTopVars_subset {s : Stmt Op} {x : Ident} (h : x ∈ declTopVars s) :
    x ∈ declaredNamesStmt s := by
  cases s <;> simp_all [declTopVars, declaredNamesStmt]

theorem declTopVarsL_subset {ss : List (Stmt Op)} {x : Ident} (h : x ∈ declTopVarsL ss) :
    x ∈ declaredNamesStmts ss := by
  induction ss with
  | nil => simp [declTopVarsL] at h
  | cons s rest ih =>
      simp only [declTopVarsL, List.flatMap_cons, List.mem_append] at h
      simp only [declaredNamesStmts, List.mem_append]
      rcases h with h | h
      · exact Or.inl (declTopVars_subset h)
      · exact Or.inr (ih (by simpa [declTopVarsL] using h))

mutual
theorem scopedStmt_mentions {vs fs : List Ident} {x : Ident} {s : Stmt Op}
    (hsc : ScopedStmt vs fs s) (hm : stmtMentions x s = true) :
    x ∈ vs ∨ x ∈ declaredNamesStmt s := by
  cases s with
  | block body =>
      simp only [ScopedStmt] at hsc
      simp only [stmtMentions] at hm
      simpa [declaredNamesStmt] using scopedStmts_mentions hsc hm
  | funDef n ps rs body =>
      simp only [ScopedStmt] at hsc
      simp only [stmtMentions, Bool.or_eq_true, decide_eq_true_eq] at hm
      simp only [declaredNamesStmt, List.mem_cons, List.mem_append]
      rcases hm with (hp | hp) | hb
      · tauto
      · tauto
      · have h2 := scopedStmts_mentions hsc hb
        rw [List.mem_append] at h2; tauto
  | letDecl vars val =>
      cases val with
      | none =>
          simp only [stmtMentions, optExprMentions, Bool.or_false, decide_eq_true_eq] at hm
          exact Or.inr (by simpa [declaredNamesStmt] using hm)
      | some e =>
          simp only [ScopedStmt] at hsc
          simp only [stmtMentions, optExprMentions, Bool.or_eq_true, decide_eq_true_eq] at hm
          rcases hm with hv | he
          · exact Or.inr (by simpa [declaredNamesStmt] using hv)
          · exact Or.inl (scopedExpr_mentions hsc he)
  | assign vars val =>
      simp only [ScopedStmt] at hsc
      simp only [stmtMentions, Bool.or_eq_true, decide_eq_true_eq] at hm
      rcases hm with hv | he
      · exact Or.inl (hsc.1 x hv)
      · exact Or.inl (scopedExpr_mentions hsc.2 he)
  | cond c body =>
      simp only [ScopedStmt] at hsc
      simp only [stmtMentions, Bool.or_eq_true] at hm
      rcases hm with hc | hb
      · exact Or.inl (scopedExpr_mentions hsc.1 hc)
      · simpa [declaredNamesStmt] using scopedStmts_mentions hsc.2 hb
  | «switch» c cs d =>
      simp only [ScopedStmt] at hsc
      simp only [stmtMentions, Bool.or_eq_true] at hm
      simp only [declaredNamesStmt, List.mem_append]
      rcases hm with (hc | hcs) | hdf
      · exact Or.inl (scopedExpr_mentions hsc.1 hc)
      · have := scopedCases_mentions hsc.2.1 hcs; tauto
      · have := scopedDflt_mentions hsc.2.2 hdf; tauto
  | forLoop init c post body =>
      simp only [ScopedStmt] at hsc
      obtain ⟨hi, hcnd, hp, hb⟩ := hsc
      simp only [stmtMentions, Bool.or_eq_true] at hm
      simp only [declaredNamesStmt, List.mem_append]
      rcases hm with ((hmi | hmc) | hmp) | hmb
      · have := scopedStmts_mentions hi hmi; tauto
      · have h2 := scopedExpr_mentions hcnd hmc
        rw [List.mem_append] at h2
        rcases h2 with hv | hv
        · exact Or.inl hv
        · have := declTopVarsL_subset hv; tauto
      · have h2 := scopedStmts_mentions hp hmp
        rcases h2 with hv | hd
        · rw [List.mem_append] at hv
          rcases hv with hv | hv
          · exact Or.inl hv
          · have := declTopVarsL_subset hv; tauto
        · tauto
      · have h2 := scopedStmts_mentions hb hmb
        rcases h2 with hv | hd
        · rw [List.mem_append] at hv
          rcases hv with hv | hv
          · exact Or.inl hv
          · have := declTopVarsL_subset hv; tauto
        · tauto
  | exprStmt e =>
      simp only [ScopedStmt] at hsc
      simp only [stmtMentions] at hm
      exact Or.inl (scopedExpr_mentions hsc hm)
  | «break» => simp [stmtMentions] at hm
  | «continue» => simp [stmtMentions] at hm
  | «leave» => simp [stmtMentions] at hm
theorem scopedStmts_mentions {vs fs : List Ident} {x : Ident} {ss : List (Stmt Op)}
    (hsc : ScopedStmts vs fs ss) (hm : stmtsMentions x ss = true) :
    x ∈ vs ∨ x ∈ declaredNamesStmts ss := by
  cases ss with
  | nil => simp [stmtsMentions] at hm
  | cons s rest =>
      simp only [ScopedStmts] at hsc
      simp only [stmtsMentions, Bool.or_eq_true] at hm
      simp only [declaredNamesStmts, List.mem_append]
      rcases hm with h | h
      · have := scopedStmt_mentions hsc.1 h; tauto
      · have h2 := scopedStmts_mentions hsc.2 h
        rcases h2 with hv | hd
        · rw [List.mem_append] at hv
          rcases hv with hv | hv
          · exact Or.inl hv
          · have := declTopVars_subset hv; tauto
        · tauto
theorem scopedCases_mentions {vs fs : List Ident} {x : Ident}
    {cs : List (Literal × List (Stmt Op))}
    (hsc : ScopedCases vs fs cs) (hm : casesMentions x cs = true) :
    x ∈ vs ∨ x ∈ declaredNamesCases cs := by
  cases cs with
  | nil => simp [casesMentions] at hm
  | cons hd tl =>
      obtain ⟨l, b⟩ := hd
      simp only [ScopedCases] at hsc
      simp only [casesMentions, Bool.or_eq_true] at hm
      simp only [declaredNamesCases, List.mem_append]
      rcases hm with h | h
      · have := scopedStmts_mentions hsc.1 h; tauto
      · have := scopedCases_mentions hsc.2 h; tauto
theorem scopedDflt_mentions {vs fs : List Ident} {x : Ident}
    {d : Option (List (Stmt Op))}
    (hsc : ScopedDflt vs fs d) (hm : optBlockMentions x d = true) :
    x ∈ vs ∨ x ∈ declaredNamesDflt d := by
  cases d with
  | none => simp [optBlockMentions] at hm
  | some b =>
      simp only [ScopedDflt] at hsc
      simp only [optBlockMentions] at hm
      simpa [declaredNamesDflt] using scopedStmts_mentions hsc hm
end

/-! ## Restore depends only on the base length

`restore base X` keeps the last `base.length` entries of `X`, so it is
insensitive to the *contents* of `base`; two bases of equal length restore
identically, and restoring twice (outer within inner) collapses to the outer. -/

theorem restore_len_eq {base1 base2 X : VEnv D} (h : base1.length = base2.length) :
    restore base1 X = restore base2 X := by
  simp only [restore, h]

/-- Executing a statement sequence never shrinks the environment. -/
theorem stmts_len {funs : FunEnv D} {ss : List (Stmt Op)} {V st Vb st' o}
    (h : Step D funs V st (.stmts ss) (.sres Vb st' o)) : V.length ≤ Vb.length :=
  venvLen_mono h rfl

/-! ## Added bindings are declared

The bindings a statement (sequence) prepends to the environment are named by its
declared names. This is what identifies the leaked locals of a spliced block as
that block's declared variables, so uniqueness can prove them unmentioned. -/

private theorem append_nil_of_eq {α} {A L : List α} (h : L = A ++ L) : A = [] := by
  have hlen := congrArg List.length h
  simp only [List.length_append] at hlen
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem stmt_added {funs : FunEnv D} {s : Stmt Op} {V st V1 st1 o}
    (h : Step D funs V st (.stmt s) (.sres V1 st1 o)) {A : List Ident}
    (hA : V1.map Prod.fst = A ++ V.map Prod.fst) : ∀ x ∈ A, x ∈ declaredNamesStmt s := by
  intro x hx
  have nilCase : V1.map Prod.fst = V.map Prod.fst → x ∈ declaredNamesStmt s := by
    intro hk; rw [hk] at hA; obtain rfl := append_nil_of_eq hA; exact absurd hx (by simp)
  have restoreCase : ∀ {Vb : VEnv D} {funs' body st'' o''},
      Step D funs' V st (.stmts body) (.sres Vb st'' o'') → V1 = restore V Vb →
      x ∈ declaredNamesStmt s := by
    intro Vb funs' body st'' o'' hb heq
    exact nilCase (by rw [heq, restore_keys (venvKeys_suffix hb rfl) (venvLen_mono hb rfl)])
  have blockStmtCase : ∀ {V' funs' body' stIn st'' o''},
      Step D funs' V stIn (.stmt (.block body')) (.sres V' st'' o'') → V1 = V' →
      x ∈ declaredNamesStmt s := by
    intro V' funs' body' stIn st'' o'' hb heq
    cases hb with
    | block hbody =>
        exact nilCase (by rw [heq, restore_keys (venvKeys_suffix hbody rfl) (venvLen_mono hbody rfl)])
  cases h with
  | @letZero _ _ _ vars =>
      rw [show (bindZeros D vars ++ V).map Prod.fst = vars ++ V.map Prod.fst from by
            simp [bindZeros, List.map_append, List.map_map, Function.comp_def]] at hA
      obtain rfl := List.append_cancel_right hA
      simpa [declaredNamesStmt] using hx
  | @letVal _ _ _ vars e vals _ _ =>
      rw [show (List.zip vars vals ++ V).map Prod.fst = (List.zip vars vals).map Prod.fst
            ++ V.map Prod.fst from by simp [List.map_append]] at hA
      obtain rfl := List.append_cancel_right hA
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      simpa [declaredNamesStmt] using (List.of_mem_zip hp).1
  | letHalt _ => exact nilCase rfl
  | assignVal _ => exact nilCase (by rw [VEnv.setMany_keys])
  | assignHalt _ => exact nilCase rfl
  | exprStmt _ => exact nilCase rfl
  | exprStmtHalt _ => exact nilCase rfl
  | funDef => exact nilCase rfl
  | block hb => exact restoreCase hb rfl
  | ifTrue _ _ hb => exact blockStmtCase hb rfl
  | ifFalse _ => exact nilCase rfl
  | ifHalt _ => exact nilCase rfl
  | switchExec _ hb => exact blockStmtCase hb rfl
  | switchHalt _ => exact nilCase rfl
  | forLoop hinit hloop => exact nilCase (by
      rw [restore_keys ((venvKeys_suffix hinit rfl).trans (venvKeys_suffix hloop rfl))
            (Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl))])
  | forInitHalt hinit => exact nilCase (by
      rw [restore_keys (venvKeys_suffix hinit rfl) (venvLen_mono hinit rfl)])
  | «break» => exact nilCase rfl
  | «continue» => exact nilCase rfl
  | «leave» => exact nilCase rfl

theorem stmts_added {funs : FunEnv D} : ∀ {ss : List (Stmt Op)} {V st Vb st' o},
    Step D funs V st (.stmts ss) (.sres Vb st' o) → ∀ {A : List Ident},
    Vb.map Prod.fst = A ++ V.map Prod.fst → ∀ x ∈ A, x ∈ declaredNamesStmts ss
  | [], V, st, Vb, st', o, h, A, hA, x, hx => by
      cases h with
      | seqNil => obtain rfl := append_nil_of_eq hA; exact absurd hx (by simp)
  | s :: rest, V, st, Vb, st', o, h, A, hA, x, hx => by
      cases h with
      | seqCons hs htail =>
          obtain ⟨As, hAs⟩ := venvKeys_suffix hs rfl
          obtain ⟨Ar, hAr⟩ := venvKeys_suffix htail rfl
          have key2 : Vb.map Prod.fst = (Ar ++ As) ++ V.map Prod.fst := by
            rw [← hAr, ← hAs]; exact (List.append_assoc Ar As (V.map Prod.fst)).symm
          obtain rfl := List.append_cancel_right (hA.symm.trans key2)
          simp only [declaredNamesStmts, List.mem_append]
          rcases List.mem_append.1 hx with hxr | hxs
          · exact Or.inr (stmts_added htail hAr.symm x hxr)
          · exact Or.inl (stmt_added hs hAs.symm x hxs)
      | seqStop hs _ =>
          simp only [declaredNamesStmts, List.mem_append]
          exact Or.inl (stmt_added hs hA x hx)
  termination_by ss => sizeOf ss

/-! ## Per-case extraction lemmas (for the `switch` case) -/

theorem noFunDefCases_mem {cs : List (Literal × List (Stmt Op))} (h : NoFunDefCases cs)
    {l b} (hm : (l, b) ∈ cs) : NoFunDefStmts b := by
  induction cs with
  | nil => simp at hm
  | cons hd tl ih =>
      obtain ⟨l0, b0⟩ := hd
      rcases List.mem_cons.1 hm with he | ht
      · simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he; exact h.1
      · exact ih h.2 ht

theorem scopedCases_mem {vs fs} {cs : List (Literal × List (Stmt Op))}
    (h : ScopedCases vs fs cs) {l b} (hm : (l, b) ∈ cs) :
    ScopedStmts vs (fs ++ funDefNames b) b := by
  induction cs with
  | nil => simp at hm
  | cons hd tl ih =>
      obtain ⟨l0, b0⟩ := hd
      rcases List.mem_cons.1 hm with he | ht
      · simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he; exact h.1
      · exact ih h.2 ht

theorem forInitCases_mem {cs : List (Literal × List (Stmt Op))} (h : ForInitEmptyCases cs)
    {l b} (hm : (l, b) ∈ cs) : ForInitEmptyStmts b := by
  induction cs with
  | nil => simp at hm
  | cons hd tl ih =>
      obtain ⟨l0, b0⟩ := hd
      rcases List.mem_cons.1 hm with he | ht
      · simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he; exact h.1
      · exact ih h.2 ht

theorem declaredCases_sublist {cs : List (Literal × List (Stmt Op))} {l b} (hm : (l, b) ∈ cs) :
    List.Sublist (declaredNamesStmts b) (declaredNamesCases cs) := by
  induction cs with
  | nil => simp at hm
  | cons hd tl ih =>
      obtain ⟨l0, b0⟩ := hd
      simp only [declaredNamesCases]
      rcases List.mem_cons.1 hm with he | ht
      · simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he
        exact List.sublist_append_left _ _
      · exact (ih ht).trans (List.sublist_append_right _ _)

theorem sizeOf_cases_mem {cs : List (Literal × List (Stmt Op))} {l b} (hm : (l, b) ∈ cs) :
    sizeOf b < sizeOf cs := by
  induction cs with
  | nil => simp at hm
  | cons hd tl ih =>
      obtain ⟨l0, b0⟩ := hd
      rcases List.mem_cons.1 hm with he | ht
      · simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he
        simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
      · have := ih ht; simp only [List.cons.sizeOf_spec]; omega

theorem flatten_cases_forall2 {cs : List (Literal × List (Stmt Op))}
    (hEB : ∀ l b, (l, b) ∈ cs → EquivBlock D b (flattenStmts b)) :
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs (flattenCases cs) := by
  induction cs with
  | nil => exact List.Forall₂.nil
  | cons hd tl ih =>
      obtain ⟨l, b⟩ := hd
      exact List.Forall₂.cons ⟨rfl, hEB l b (by simp)⟩
        (ih (fun l' b' hm => hEB l' b' (List.mem_cons_of_mem _ hm)))

/-! ## The core forward simulation

For a `FunctionsHoisted` + `ForInitEmpty` block, running the original statement
list forward-simulates running its flattening, with `restore` to the block base
preserved. Sub-blocks (bare-block inners, compound bodies) are handled by the
recursion `ih` (block-level `EquivBlock`); the bare-block splice uses
`framePrefixAdd_stmts` with the leak discharged by uniqueness. -/

/-- The recursion hypothesis: `EquivBlock` for every strictly-smaller funDef-free,
well-scoped, unique, empty-for-init block. -/
abbrev FlattenIH (calls : ExternalCalls) (creates : ExternalCreates)
    (ss : List (Stmt Op)) : Prop :=
  ∀ (b' : List (Stmt Op)), sizeOf b' < sizeOf ss → NoFunDefStmts b' →
    ∀ {vs' fs' : List Ident}, ScopedStmts vs' fs' b' →
      (∀ x ∈ vs', x ∉ declaredNamesStmts b') → (declaredNamesStmts b').Nodup →
      ForInitEmptyStmts b' → EquivBlock (evmWithExternal calls creates) b' (flattenStmts b')

theorem core_fwd {ss : List (Stmt Op)} (ih : FlattenIH calls creates ss)
    (hFH : FunctionsHoisted ss) {vs fs : List Ident} (hsc : ScopedStmts vs fs ss)
    (hfresh : ∀ x ∈ vs, x ∉ declaredNamesStmts ss) (huniq : (declaredNamesStmts ss).Nodup)
    (hFIE : ForInitEmptyStmts ss) {funs : FunEnv D} {V st Vb st' o}
    (h : Step D funs V st (.stmts ss) (.sres Vb st' o)) :
    ∃ Vb', Step D funs V st (.stmts (flattenStmts ss)) (.sres Vb' st' o) ∧
      restore V Vb = restore V Vb' := by
  match ss, ih, hFH, hsc, hfresh, huniq, hFIE, h with
  | [], _, _, _, _, _, _, h =>
      cases h with | seqNil => exact ⟨V, Step.seqNil, rfl⟩
  | s :: rest, ih, hFH, hsc, hfresh, huniq, hFIE, h =>
      -- Threading to `rest`.
      have hscP : ScopedStmt vs fs s ∧ ScopedStmts (vs ++ declTopVars s) fs rest := hsc
      have hnd := List.nodup_append.mp huniq
      have huniqR : (declaredNamesStmts rest).Nodup := hnd.2.1
      have hFHrest : FunctionsHoisted rest := fun x hx => hFH x (List.mem_cons_of_mem s hx)
      have hFIErest : ForInitEmptyStmts rest := hFIE.2
      have hfreshR : ∀ x ∈ vs ++ declTopVars s, x ∉ declaredNamesStmts rest := by
        intro x hx hxr
        rcases List.mem_append.1 hx with hv | hd
        · exact hfresh x hv (by simp only [declaredNamesStmts, List.mem_append]; exact Or.inr hxr)
        · exact hnd.2.2 x (declTopVars_subset hd) x hxr rfl
      have ihRest : FlattenIH calls creates rest := fun b' hb' => ih b' (by
        simp only [List.cons.sizeOf_spec]; omega)
      -- Finisher for a non-block head `s` with `flattenStmt s = [s']` and `EquivStmt s s'`.
      have finish : ∀ (s' : Stmt Op), flattenStmt s = [s'] → EquivStmt D s s' →
          ∃ Vb', Step D funs V st (.stmts (flattenStmts (s :: rest))) (.sres Vb' st' o) ∧
            restore V Vb = restore V Vb' := by
        intro s' hfe hEq
        have hflat : flattenStmts (s :: rest) = s' :: flattenStmts rest := by
          simp [flattenStmts, hfe]
        rw [hflat]
        cases h with
        | seqCons hs htail =>
            rename_i V1 st1
            obtain ⟨Vbr, hrestF, hres⟩ :=
              core_fwd ihRest hFHrest hscP.2 hfreshR huniqR hFIErest htail
            refine ⟨Vbr, Step.seqCons (hEq.mp hs) hrestF, ?_⟩
            have h1 : V.length ≤ V1.length := venvLen_mono hs rfl
            have h2 : V1.length ≤ Vb.length := stmts_len htail
            have h3 : V1.length ≤ Vbr.length := stmts_len hrestF
            rw [← restore_restore h1 h2, ← restore_restore h1 h3, hres]
        | seqStop hs hne =>
            exact ⟨Vb, Step.seqStop (hEq.mp hs) hne, rfl⟩
      -- Facts about the head under the hypotheses.
      have hHT : HoistedTop s := hFH s (by simp)
      cases s with
      | block inner =>
          -- Bare block: splice `inner` (funDef-free) and frame its leak over `rest`.
          have hnfInner : NoFunDefStmts inner := by
            have := hHT; simpa [HoistedTop, NoFunDefStmt] using this
          have hnfInnerF : NoFunDefStmts (flattenStmts inner) := noFunDef_flattenStmts hnfInner
          have hscInner : ScopedStmts vs fs inner := by
            have h2 : ScopedStmts vs (fs ++ funDefNames inner) inner := hscP.1
            rwa [funDefNames_nil_of_noFunDef hnfInner, List.append_nil] at h2
          have hEqInner : EquivBlock D inner (flattenStmts inner) :=
            ih inner (by simp only [List.cons.sizeOf_spec, Stmt.block.sizeOf_spec]; omega)
              hnfInner hscInner
              (fun x hv hx => hfresh x hv (by
                simp only [declaredNamesStmts, declaredNamesStmt, List.mem_append]; exact Or.inl hx))
              hnd.1 hFIE.1
          have hflatEq : flattenStmts (.block inner :: rest)
              = flattenStmts inner ++ flattenStmts rest := by simp [flattenStmts, flattenStmt]
          rw [hflatEq]
          cases h with
          | seqCons hs htail =>
              rename_i V1 st1
              obtain ⟨Vi, hV1, hInner⟩ := (block_unwrap hnfInner).1 hs
              have hblk : Step D funs V st (.stmt (.block inner)) (.sres (restore V Vi) st1 .normal) :=
                (block_unwrap hnfInner).2 ⟨Vi, rfl, hInner⟩
              have hblk' := EquivBlock.mp hEqInner hblk
              obtain ⟨Vi', hViEq, hInnerF⟩ := (block_unwrap hnfInnerF).1 hblk'
              have hlenVi : V.length ≤ Vi.length := venvLen_mono hInner rfl
              have hlenV1 : V1.length = V.length := by rw [hV1]; exact restore_length hlenVi
              obtain ⟨Vbr, hrestF, hres⟩ :=
                core_fwd ihRest hFHrest hscP.2 hfreshR huniqR hFIErest htail
              have hViV1 : restore V Vi' = V1 := by rw [hV1, hViEq]
              set A : VEnv D := Vi'.take (Vi'.length - V.length) with hA
              have hsplit : A ++ V1 = Vi' := by
                have hd : Vi'.drop (Vi'.length - V.length) = V1 := hViV1
                calc A ++ V1
                    = Vi'.take (Vi'.length - V.length) ++ Vi'.drop (Vi'.length - V.length) := by rw [hd]
                  _ = Vi' := List.take_append_drop _ _
              have hViKeys : Vi'.map Prod.fst = A.map Prod.fst ++ V.map Prod.fst := by
                have h0 : Vi'.map Prod.fst = (A ++ V1).map Prod.fst := by rw [hsplit]
                rw [h0, List.map_append]; congr 1
                rw [hV1]; exact restore_keys (venvKeys_suffix hInner rfl) hlenVi
              have hAdecl : ∀ p ∈ A, p.1 ∈ declaredNamesStmts inner := by
                intro p hp
                have := stmts_added hInnerF (A := A.map Prod.fst) hViKeys p.1
                  (List.mem_map.2 ⟨p, hp, rfl⟩)
                rwa [declaredNames_flattenStmts] at this
              have hframe : ∀ p ∈ A, stmtsMentions p.1 (flattenStmts rest) = false := by
                intro p hp
                rw [mentions_flattenStmts]
                by_contra hmen
                rw [Bool.not_eq_false] at hmen
                rcases scopedStmts_mentions hscP.2 hmen with hv | hd
                · exact hfresh p.1 (by simpa [declTopVars] using hv) (by
                    simp only [declaredNamesStmts, declaredNamesStmt, List.mem_append]
                    exact Or.inl (hAdecl p hp))
                · exact hnd.2.2 p.1 (hAdecl p hp) p.1 hd rfl
              obtain ⟨Vb'', hrestF', hresF⟩ := framePrefixAdd_stmts hrestF A hframe
              rw [hsplit] at hrestF'
              refine ⟨Vb'', stmts_append_normal hInnerF hrestF', ?_⟩
              calc restore V Vb = restore V1 Vb := restore_len_eq hlenV1.symm
                _ = restore V1 Vbr := hres
                _ = restore V1 Vb'' := hresF
                _ = restore V Vb'' := restore_len_eq hlenV1
          | seqStop hs hne =>
              obtain ⟨Vi, hVb, hInner⟩ := (block_unwrap hnfInner).1 hs
              have hblk : Step D funs V st (.stmt (.block inner)) (.sres (restore V Vi) st' o) :=
                (block_unwrap hnfInner).2 ⟨Vi, rfl, hInner⟩
              have hblk' := EquivBlock.mp hEqInner hblk
              obtain ⟨Vi', hViEq, hInnerF⟩ := (block_unwrap hnfInnerF).1 hblk'
              have hlenVi : V.length ≤ Vi.length := venvLen_mono hInner rfl
              refine ⟨Vi', stmts_append_early hInnerF hne, ?_⟩
              calc restore V Vb = restore V (restore V Vi) := by rw [hVb]
                _ = restore V Vi := restore_restore (le_refl _) hlenVi
                _ = restore V Vi' := hViEq
      | funDef n ps rs b =>
          refine finish (.funDef n ps rs (flattenStmts b)) rfl ?_
          intro funs' V'' st'' V3 st3 o3
          constructor <;> (intro hstep; cases hstep; exact Step.funDef)
      | letDecl vars val => exact finish _ rfl (EquivStmt.refl _)
      | assign vars val => exact finish _ rfl (EquivStmt.refl _)
      | exprStmt e => exact finish _ rfl (EquivStmt.refl _)
      | «break» => exact finish _ rfl (EquivStmt.refl _)
      | «continue» => exact finish _ rfl (EquivStmt.refl _)
      | «leave» => exact finish _ rfl (EquivStmt.refl _)
      | cond c body =>
          have hnfBody : NoFunDefStmts body := by
            simpa [HoistedTop, NoFunDefStmt] using hHT
          refine finish (.cond c (flattenStmts body)) rfl
            (EquivStmt.cond_congr (@EquivExpr.refl (evmWithExternal calls creates) _ c) ?_)
          exact ih body (by simp only [List.cons.sizeOf_spec, Stmt.cond.sizeOf_spec]; omega)
            hnfBody (by
              have h2 : ScopedExpr vs fs c ∧ ScopedStmts vs (fs ++ funDefNames body) body := hscP.1
              rw [funDefNames_nil_of_noFunDef hnfBody, List.append_nil] at h2
              exact h2.2)
            (fun x hv hx => hfresh x hv (by
              simp only [declaredNamesStmts, declaredNamesStmt, List.mem_append]; exact Or.inl hx))
            (by have := huniq; simp only [declaredNamesStmts, declaredNamesStmt] at this
                exact (List.nodup_append.mp this).1)
            hFIE.1
      | «switch» c cs d =>
          obtain ⟨hnfC, hnfD⟩ : NoFunDefCases cs ∧ NoFunDefDflt d := by
            have := hHT; simpa [HoistedTop, NoFunDefStmt] using this
          have hscSw : ScopedExpr vs fs c ∧ ScopedCases vs fs cs ∧ ScopedDflt vs fs d := hscP.1
          obtain ⟨hFIEc, hFIEd⟩ : ForInitEmptyCases cs ∧ ForInitEmptyDflt d := hFIE.1
          have hundSw : (declaredNamesCases cs ++ declaredNamesDflt d).Nodup := by
            have := hnd.1; simpa [declaredNamesStmt] using this
          have hmemSw : ∀ x, x ∈ declaredNamesCases cs ++ declaredNamesDflt d →
              x ∈ declaredNamesStmts (.switch c cs d :: rest) := fun x hx => by
            simp only [declaredNamesStmts, declaredNamesStmt]; exact List.mem_append_left _ hx
          have hEB : ∀ l b, (l, b) ∈ cs → EquivBlock D b (flattenStmts b) := by
            intro l b hm
            have hnfb := noFunDefCases_mem hnfC hm
            have hsub := declaredCases_sublist hm
            have hscb : ScopedStmts vs fs b := by
              have h2 := scopedCases_mem hscSw.2.1 hm
              rwa [funDefNames_nil_of_noFunDef hnfb, List.append_nil] at h2
            exact ih b
              (by have := sizeOf_cases_mem hm
                  simp only [List.cons.sizeOf_spec, Stmt.switch.sizeOf_spec]; omega)
              hnfb hscb
              (fun x hv hx => hfresh x hv (hmemSw x (List.mem_append_left _ (hsub.subset hx))))
              (List.Nodup.sublist hsub (List.nodup_append.mp hundSw).1)
              (forInitCases_mem hFIEc hm)
          refine finish (.switch c (flattenCases cs) (flattenDflt d)) rfl
            (EquivStmt.switch_congr (@EquivExpr.refl (evmWithExternal calls creates) _ c)
              (flatten_cases_forall2 hEB) ?_)
          cases d with
          | none => exact EquivBlock.refl _
          | some bd =>
              have hnfBd : NoFunDefStmts bd := by simpa [NoFunDefDflt] using hnfD
              have hsubD : List.Sublist (declaredNamesStmts bd) (declaredNamesDflt (some bd)) := by
                simp only [declaredNamesDflt]; exact List.Sublist.refl _
              have hscBd : ScopedStmts vs fs bd := by
                have h2 : ScopedStmts vs (fs ++ funDefNames bd) bd := by
                  simpa [ScopedDflt] using hscSw.2.2
                rwa [funDefNames_nil_of_noFunDef hnfBd, List.append_nil] at h2
              simp only [Option.getD, flattenDflt]
              exact ih bd
                (by have : sizeOf bd < sizeOf (Option.some bd) := by
                      simp only [Option.some.sizeOf_spec]; omega
                    simp only [List.cons.sizeOf_spec, Stmt.switch.sizeOf_spec]; omega)
                hnfBd hscBd
                (fun x hv hx => hfresh x hv (hmemSw x (List.mem_append_right _ (hsubD.subset hx))))
                (List.Nodup.sublist hsubD (List.nodup_append.mp hundSw).2.1)
                (by simpa [ForInitEmptyDflt] using hFIEd)
      | forLoop init c post body =>
          obtain ⟨hinit0, hpostFIE, hbodyFIE⟩ := hFIE.1
          subst hinit0
          have hnfAll : NoFunDefStmts ([] : List (Stmt Op)) ∧ NoFunDefStmts post ∧
              NoFunDefStmts body := by have := hHT; simpa [HoistedTop, NoFunDefStmt] using this
          obtain ⟨_, hnfPost, hnfBody⟩ := hnfAll
          have hf0 : funDefNames ([] : List (Stmt Op)) = [] := funDefNames_nil_of_noFunDef trivial
          have hscPB : ScopedStmts vs fs post ∧ ScopedStmts vs fs body := by
            have h2 := hscP.1
            simp only [ScopedStmt, hf0, funDefNames_nil_of_noFunDef hnfPost,
              funDefNames_nil_of_noFunDef hnfBody, declTopVarsL, List.flatMap_nil,
              List.append_nil] at h2
            exact ⟨h2.2.2.1, h2.2.2.2⟩
          have hunPB : (declaredNamesStmts post ++ declaredNamesStmts body).Nodup := by
            have := hnd.1
            simpa [declaredNamesStmt, declaredNamesStmts] using this
          have hmemPB : ∀ {x}, (x ∈ declaredNamesStmts post ∨ x ∈ declaredNamesStmts body) →
              x ∈ declaredNamesStmts (.forLoop [] c post body :: rest) := by
            intro x hx
            simp only [declaredNamesStmts, declaredNamesStmt, List.mem_append, List.nil_append]
            exact Or.inl hx
          refine finish (.forLoop [] c (flattenStmts post) (flattenStmts body)) (by simp [flattenStmt, flattenStmts])
            (EquivStmt.forLoop_congr [] (@EquivExpr.refl (evmWithExternal calls creates) _ c) ?_ ?_)
          · exact ih post (by simp only [List.cons.sizeOf_spec, Stmt.forLoop.sizeOf_spec]; omega)
              hnfPost hscPB.1 (fun x hv hx => hfresh x hv (hmemPB (Or.inl hx)))
              (List.nodup_append.mp hunPB).1 hpostFIE
          · exact ih body (by simp only [List.cons.sizeOf_spec, Stmt.forLoop.sizeOf_spec]; omega)
              hnfBody hscPB.2 (fun x hv hx => hfresh x hv (hmemPB (Or.inr hx)))
              (List.nodup_append.mp hunPB).2.1 hbodyFIE
  termination_by sizeOf ss
  decreasing_by all_goals (simp only [List.cons.sizeOf_spec]; omega)

end YulEvmCompiler.Optimizer
