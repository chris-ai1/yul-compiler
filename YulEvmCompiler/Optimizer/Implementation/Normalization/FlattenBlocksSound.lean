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

end YulEvmCompiler.Optimizer
