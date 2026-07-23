import YulEvmCompiler.Optimizer.Implementation.Normalization.DisambiguateRun
/-!
# Decidable validity checks for the disambiguation pass

The semantic soundness theorem `disambiguate_runEquivBlock` is conditional on
the source program's validity (all of which valid Yul guarantees):
`SVStmts`, `WellFormed`, `NormalForm.WellScoped`, `WScopedStmts []`,
`FScopedStmts`. To wire the pass into the optimizer pipeline — whose passes
must be *unconditionally* sound — we gate it behind a runtime check: this file
provides computable `Bool` checkers together with one-directional soundness
lemmas (`check = true → validity`), which is all the gate needs (on a failed
check the pass is the identity).
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {Op : Type}

/-! ### Deciding `NotFresh` -/

/-- A fresh name's length determines its index. -/
theorem dsName_length (k : Nat) : (dsName k).length = k + 2 := by
  simp only [dsName, String.length_ofList, List.length_cons, List.length_replicate]

/-- `NotFresh` is decidable: only indices below the identifier's length can
possibly produce it (longer indices give longer names). -/
instance decNotFresh (x : Ident) : Decidable (NotFresh x) :=
  decidable_of_iff (∀ k, k < x.length → x ≠ dsName k)
    ⟨fun h k hc => by
        by_cases hk : k < x.length
        · exact h k hk hc
        · have hlen := congrArg String.length hc
          rw [dsName_length] at hlen
          omega,
      fun h k _ => h k⟩

/-! ### Source validity (`SV*`) -/

mutual
def chkSVExpr : Expr Op → Bool
  | .lit _ => true
  | .var x => decide (NotFresh x)
  | .builtin _ args => chkSVArgs args
  | .call fn args => decide (NotFresh fn) && chkSVArgs args
def chkSVArgs : List (Expr Op) → Bool
  | [] => true
  | e :: rest => chkSVExpr e && chkSVArgs rest
end

mutual
def chkSVStmt : Stmt Op → Bool
  | .letDecl vars eo =>
      decide vars.Nodup && decide (∀ x ∈ vars, NotFresh x) &&
        (match eo with | none => true | some e => chkSVExpr e)
  | .assign vars e => decide (∀ x ∈ vars, NotFresh x) && chkSVExpr e
  | .exprStmt e => chkSVExpr e
  | .funDef fn ps rs body =>
      decide (NotFresh fn) && decide (ps ++ rs).Nodup &&
        decide (∀ x ∈ ps ++ rs, NotFresh x) && chkSVStmts body
  | .block body => chkSVStmts body
  | .cond c body => chkSVExpr c && chkSVStmts body
  | .switch c cases dflt => chkSVExpr c && chkSVCases cases && chkSVDflt dflt
  | .forLoop init c post body =>
      chkSVStmts init && chkSVExpr c && chkSVStmts post && chkSVStmts body
  | .«break» => true
  | .«continue» => true
  | .leave => true
def chkSVStmts : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => chkSVStmt s && chkSVStmts rest
def chkSVCases : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, body) :: rest => chkSVStmts body && chkSVCases rest
def chkSVDflt : Option (List (Stmt Op)) → Bool
  | none => true
  | some body => chkSVStmts body
end

mutual
theorem chkSVExpr_sound : ∀ {e : Expr Op}, chkSVExpr e = true → SVExpr e
  | .lit _, _ => trivial
  | .var x, h => by
      simp only [chkSVExpr, decide_eq_true_eq] at h
      exact h
  | .builtin _ args, h => chkSVArgs_sound (by simpa [chkSVExpr] using h)
  | .call fn args, h => by
      simp only [chkSVExpr, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkSVArgs_sound h.2⟩
theorem chkSVArgs_sound : ∀ {es : List (Expr Op)}, chkSVArgs es = true → SVArgs es
  | [], _ => trivial
  | e :: rest, h => by
      simp only [chkSVArgs, Bool.and_eq_true] at h
      exact ⟨chkSVExpr_sound h.1, chkSVArgs_sound h.2⟩
end

mutual
theorem chkSVStmt_sound : ∀ {s : Stmt Op}, chkSVStmt s = true → SVStmt s
  | .letDecl vars eo, h => by
      simp only [chkSVStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨h.1.1, h.1.2, ?_⟩
      intro e he
      subst he
      exact chkSVExpr_sound h.2
  | .assign vars e, h => by
      simp only [chkSVStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkSVExpr_sound h.2⟩
  | .exprStmt e, h => chkSVExpr_sound (by simpa [chkSVStmt] using h)
  | .funDef fn ps rs body, h => by
      simp only [chkSVStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1.1, h.1.1.2, h.1.2, chkSVStmts_sound h.2⟩
  | .block body, h => chkSVStmts_sound (by simpa [chkSVStmt] using h)
  | .cond c body, h => by
      simp only [chkSVStmt, Bool.and_eq_true] at h
      exact ⟨chkSVExpr_sound h.1, chkSVStmts_sound h.2⟩
  | .switch c cases dflt, h => by
      simp only [chkSVStmt, Bool.and_eq_true] at h
      exact ⟨chkSVExpr_sound h.1.1, chkSVCases_sound h.1.2, chkSVDflt_sound h.2⟩
  | .forLoop init c post body, h => by
      simp only [chkSVStmt, Bool.and_eq_true] at h
      exact ⟨chkSVStmts_sound h.1.1.1, chkSVExpr_sound h.1.1.2,
        chkSVStmts_sound h.1.2, chkSVStmts_sound h.2⟩
  | .«break», _ => trivial
  | .«continue», _ => trivial
  | .leave, _ => trivial
theorem chkSVStmts_sound : ∀ {ss : List (Stmt Op)}, chkSVStmts ss = true → SVStmts ss
  | [], _ => trivial
  | s :: rest, h => by
      simp only [chkSVStmts, Bool.and_eq_true] at h
      exact ⟨chkSVStmt_sound h.1, chkSVStmts_sound h.2⟩
theorem chkSVCases_sound : ∀ {cs : List (Literal × List (Stmt Op))},
    chkSVCases cs = true → SVCases cs
  | [], _ => trivial
  | (_, body) :: rest, h => by
      simp only [chkSVCases, Bool.and_eq_true] at h
      exact ⟨chkSVStmts_sound h.1, chkSVCases_sound h.2⟩
theorem chkSVDflt_sound : ∀ {dflt : Option (List (Stmt Op))},
    chkSVDflt dflt = true → SVDflt dflt
  | none, _ => trivial
  | some body, h => chkSVStmts_sound (by simpa [chkSVDflt] using h)
end

/-! ### Per-block distinct function names (`WellFormed`) -/

mutual
def chkWFStmt : Stmt Op → Bool
  | .funDef _ _ _ body => decide (funNames body).Nodup && chkWFStmts body
  | .block body => decide (funNames body).Nodup && chkWFStmts body
  | .cond _ body => decide (funNames body).Nodup && chkWFStmts body
  | .switch _ cases dflt => chkWFCases cases && chkWFDflt dflt
  | .forLoop init _ post body =>
      (decide (funNames init).Nodup && chkWFStmts init) &&
        (decide (funNames body).Nodup && chkWFStmts body) &&
        (decide (funNames post).Nodup && chkWFStmts post)
  | _ => true
def chkWFStmts : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => chkWFStmt s && chkWFStmts rest
def chkWFCases : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, body) :: rest => (decide (funNames body).Nodup && chkWFStmts body) && chkWFCases rest
def chkWFDflt : Option (List (Stmt Op)) → Bool
  | none => true
  | some body => decide (funNames body).Nodup && chkWFStmts body
end

mutual
theorem chkWFStmt_sound : ∀ {s : Stmt Op}, chkWFStmt s = true → WFInnerS s
  | .funDef _ _ _ body, h => by
      simp only [chkWFStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkWFStmts_sound h.2⟩
  | .block body, h => by
      simp only [chkWFStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkWFStmts_sound h.2⟩
  | .cond _ body, h => by
      simp only [chkWFStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkWFStmts_sound h.2⟩
  | .switch _ cases dflt, h => by
      simp only [chkWFStmt, Bool.and_eq_true] at h
      exact ⟨chkWFCases_sound h.1, chkWFDflt_sound h.2⟩
  | .forLoop init _ post body, h => by
      simp only [chkWFStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨⟨h.1.1.1, chkWFStmts_sound h.1.1.2⟩, ⟨h.1.2.1, chkWFStmts_sound h.1.2.2⟩,
        h.2.1, chkWFStmts_sound h.2.2⟩
  | .letDecl _ _, _ => trivial
  | .assign _ _, _ => trivial
  | .exprStmt _, _ => trivial
  | .«break», _ => trivial
  | .«continue», _ => trivial
  | .leave, _ => trivial
theorem chkWFStmts_sound : ∀ {ss : List (Stmt Op)}, chkWFStmts ss = true → WFInner ss
  | [], _ => trivial
  | s :: rest, h => by
      simp only [chkWFStmts, Bool.and_eq_true] at h
      exact ⟨chkWFStmt_sound h.1, chkWFStmts_sound h.2⟩
theorem chkWFCases_sound : ∀ {cs : List (Literal × List (Stmt Op))},
    chkWFCases cs = true → WFCases cs
  | [], _ => trivial
  | (_, body) :: rest, h => by
      simp only [chkWFCases, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨⟨h.1.1, chkWFStmts_sound h.1.2⟩, chkWFCases_sound h.2⟩
theorem chkWFDflt_sound : ∀ {dflt : Option (List (Stmt Op))},
    chkWFDflt dflt = true → WFDflt dflt
  | none, _ => trivial
  | some body, h => by
      simp only [chkWFDflt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkWFStmts_sound h.2⟩
end

/-! ### Reference-scoping (`NormalForm.Scoped*`) -/

mutual
def chkScopedExpr (vs fs : List Ident) : Expr Op → Bool
  | .lit _ => true
  | .var x => decide (x ∈ vs)
  | .builtin _ args => chkScopedArgs vs fs args
  | .call fn args => decide (fn ∈ fs) && chkScopedArgs vs fs args
def chkScopedArgs (vs fs : List Ident) : List (Expr Op) → Bool
  | [] => true
  | e :: rest => chkScopedExpr vs fs e && chkScopedArgs vs fs rest
end

mutual
theorem chkScopedExpr_sound : ∀ {vs fs : List Ident} {e : Expr Op},
    chkScopedExpr vs fs e = true → NormalForm.ScopedExpr vs fs e
  | _, _, .lit _, _ => trivial
  | _, _, .var x, h => by
      simp only [chkScopedExpr, decide_eq_true_eq] at h
      exact h
  | _, _, .builtin _ args, h => chkScopedArgs_sound (by simpa [chkScopedExpr] using h)
  | _, _, .call fn args, h => by
      simp only [chkScopedExpr, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkScopedArgs_sound h.2⟩
theorem chkScopedArgs_sound : ∀ {vs fs : List Ident} {es : List (Expr Op)},
    chkScopedArgs vs fs es = true → NormalForm.ScopedArgs vs fs es
  | _, _, [], _ => trivial
  | _, _, e :: rest, h => by
      simp only [chkScopedArgs, Bool.and_eq_true] at h
      exact ⟨chkScopedExpr_sound h.1, chkScopedArgs_sound h.2⟩
end

mutual
def chkScopedStmt (vs fs : List Ident) : Stmt Op → Bool
  | .block body => chkScopedStmts vs (fs ++ NormalForm.funDefNames body) body
  | .funDef _ ps rs body => chkScopedStmts (ps ++ rs) (fs ++ NormalForm.funDefNames body) body
  | .letDecl _ (some e) => chkScopedExpr vs fs e
  | .letDecl _ none => true
  | .assign vars e => decide (∀ x ∈ vars, x ∈ vs) && chkScopedExpr vs fs e
  | .cond c body =>
      chkScopedExpr vs fs c && chkScopedStmts vs (fs ++ NormalForm.funDefNames body) body
  | .switch c cases dflt =>
      chkScopedExpr vs fs c && chkScopedCases vs fs cases && chkScopedDflt vs fs dflt
  | .forLoop init c post body =>
      chkScopedStmts vs (fs ++ NormalForm.funDefNames init) init &&
      chkScopedExpr (vs ++ NormalForm.declTopVarsL init) (fs ++ NormalForm.funDefNames init) c &&
      chkScopedStmts (vs ++ NormalForm.declTopVarsL init)
        ((fs ++ NormalForm.funDefNames init) ++ NormalForm.funDefNames post) post &&
      chkScopedStmts (vs ++ NormalForm.declTopVarsL init)
        ((fs ++ NormalForm.funDefNames init) ++ NormalForm.funDefNames body) body
  | .exprStmt e => chkScopedExpr vs fs e
  | .«break» => true
  | .«continue» => true
  | .leave => true
def chkScopedStmts (vs fs : List Ident) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => chkScopedStmt vs fs s && chkScopedStmts (vs ++ NormalForm.declTopVars s) fs rest
def chkScopedCases (vs fs : List Ident) : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, b) :: rest =>
      chkScopedStmts vs (fs ++ NormalForm.funDefNames b) b && chkScopedCases vs fs rest
def chkScopedDflt (vs fs : List Ident) : Option (List (Stmt Op)) → Bool
  | none => true
  | some b => chkScopedStmts vs (fs ++ NormalForm.funDefNames b) b
end

mutual
theorem chkScopedStmt_sound : ∀ {vs fs : List Ident} {s : Stmt Op},
    chkScopedStmt vs fs s = true → NormalForm.ScopedStmt vs fs s
  | _, _, .block body, h => chkScopedStmts_sound (by simpa [chkScopedStmt] using h)
  | _, _, .funDef _ ps rs body, h => chkScopedStmts_sound (by simpa [chkScopedStmt] using h)
  | _, _, .letDecl _ (some e), h => chkScopedExpr_sound (by simpa [chkScopedStmt] using h)
  | _, _, .letDecl _ none, _ => trivial
  | _, _, .assign vars e, h => by
      simp only [chkScopedStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkScopedExpr_sound h.2⟩
  | _, _, .cond c body, h => by
      simp only [chkScopedStmt, Bool.and_eq_true] at h
      exact ⟨chkScopedExpr_sound h.1, chkScopedStmts_sound h.2⟩
  | _, _, .switch c cases dflt, h => by
      simp only [chkScopedStmt, Bool.and_eq_true] at h
      exact ⟨chkScopedExpr_sound h.1.1, chkScopedCases_sound h.1.2, chkScopedDflt_sound h.2⟩
  | _, _, .forLoop init c post body, h => by
      simp only [chkScopedStmt, Bool.and_eq_true] at h
      exact ⟨chkScopedStmts_sound h.1.1.1, chkScopedExpr_sound h.1.1.2,
        chkScopedStmts_sound h.1.2, chkScopedStmts_sound h.2⟩
  | _, _, .exprStmt e, h => chkScopedExpr_sound (by simpa [chkScopedStmt] using h)
  | _, _, .«break», _ => trivial
  | _, _, .«continue», _ => trivial
  | _, _, .leave, _ => trivial
theorem chkScopedStmts_sound : ∀ {vs fs : List Ident} {ss : List (Stmt Op)},
    chkScopedStmts vs fs ss = true → NormalForm.ScopedStmts vs fs ss
  | _, _, [], _ => trivial
  | _, _, s :: rest, h => by
      simp only [chkScopedStmts, Bool.and_eq_true] at h
      exact ⟨chkScopedStmt_sound h.1, chkScopedStmts_sound h.2⟩
theorem chkScopedCases_sound : ∀ {vs fs : List Ident} {cs : List (Literal × List (Stmt Op))},
    chkScopedCases vs fs cs = true → NormalForm.ScopedCases vs fs cs
  | _, _, [], _ => trivial
  | _, _, (_, b) :: rest, h => by
      simp only [chkScopedCases, Bool.and_eq_true] at h
      exact ⟨chkScopedStmts_sound h.1, chkScopedCases_sound h.2⟩
theorem chkScopedDflt_sound : ∀ {vs fs : List Ident} {dflt : Option (List (Stmt Op))},
    chkScopedDflt vs fs dflt = true → NormalForm.ScopedDflt vs fs dflt
  | _, _, none, _ => trivial
  | _, _, some b, h => chkScopedStmts_sound (by simpa [chkScopedDflt] using h)
end

/-! ### Variable no-shadowing (`WScoped*`) -/

mutual
def chkWScopedStmts (dom : List Ident) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => chkWScopedStmt dom s && chkWScopedStmts (declVars s ++ dom) rest
def chkWScopedStmt (dom : List Ident) : Stmt Op → Bool
  | .letDecl vars _ => decide (∀ x ∈ vars, x ∉ dom)
  | .block body => chkWScopedStmts dom body
  | .cond _ body => chkWScopedStmts dom body
  | .switch _ cases dflt => chkWScopedCases dom cases && chkWScopedDflt dom dflt
  | .funDef _ ps rs body => decide (ps ++ rs).Nodup && chkWScopedStmts (ps ++ rs) body
  | .forLoop init _ post body =>
      chkWScopedStmts dom init && chkWScopedStmts (declVarsSeq init ++ dom) body &&
        chkWScopedStmts (declVarsSeq init ++ dom) post
  | _ => true
def chkWScopedCases (dom : List Ident) : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, body) :: rest => chkWScopedStmts dom body && chkWScopedCases dom rest
def chkWScopedDflt (dom : List Ident) : Option (List (Stmt Op)) → Bool
  | none => true
  | some body => chkWScopedStmts dom body
end

mutual
theorem chkWScopedStmts_sound : ∀ {dom : List Ident} {ss : List (Stmt Op)},
    chkWScopedStmts dom ss = true → WScopedStmts dom ss
  | _, [], _ => trivial
  | _, s :: rest, h => by
      simp only [chkWScopedStmts, Bool.and_eq_true] at h
      exact ⟨chkWScopedStmt_sound h.1, chkWScopedStmts_sound h.2⟩
theorem chkWScopedStmt_sound : ∀ {dom : List Ident} {s : Stmt Op},
    chkWScopedStmt dom s = true → WScopedStmt dom s
  | _, .letDecl vars _, h => by
      simp only [chkWScopedStmt, decide_eq_true_eq] at h
      exact h
  | _, .block body, h => chkWScopedStmts_sound (by simpa [chkWScopedStmt] using h)
  | _, .cond _ body, h => chkWScopedStmts_sound (by simpa [chkWScopedStmt] using h)
  | _, .switch _ cases dflt, h => by
      simp only [chkWScopedStmt, Bool.and_eq_true] at h
      exact ⟨chkWScopedCases_sound h.1, chkWScopedDflt_sound h.2⟩
  | _, .funDef _ ps rs body, h => by
      simp only [chkWScopedStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkWScopedStmts_sound h.2⟩
  | _, .forLoop init _ post body, h => by
      simp only [chkWScopedStmt, Bool.and_eq_true] at h
      exact ⟨chkWScopedStmts_sound h.1.1, chkWScopedStmts_sound h.1.2,
        chkWScopedStmts_sound h.2⟩
  | _, .assign _ _, _ => trivial
  | _, .exprStmt _, _ => trivial
  | _, .«break», _ => trivial
  | _, .«continue», _ => trivial
  | _, .leave, _ => trivial
theorem chkWScopedCases_sound : ∀ {dom : List Ident} {cs : List (Literal × List (Stmt Op))},
    chkWScopedCases dom cs = true → WScopedCases dom cs
  | _, [], _ => trivial
  | _, (_, body) :: rest, h => by
      simp only [chkWScopedCases, Bool.and_eq_true] at h
      exact ⟨chkWScopedStmts_sound h.1, chkWScopedCases_sound h.2⟩
theorem chkWScopedDflt_sound : ∀ {dom : List Ident} {dflt : Option (List (Stmt Op))},
    chkWScopedDflt dom dflt = true → WScopedDflt dom dflt
  | _, none, _ => trivial
  | _, some body, h => chkWScopedStmts_sound (by simpa [chkWScopedDflt] using h)
end

/-! ### Function no-shadowing (`FScoped*`) -/

mutual
def chkFScopedStmts (fdom : List Ident) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => chkFScopedStmt fdom s && chkFScopedStmts fdom rest
def chkFScopedStmt (fdom : List Ident) : Stmt Op → Bool
  | .block body =>
      decide (∀ fn ∈ funNames body, fn ∉ fdom) && chkFScopedStmts (funNames body ++ fdom) body
  | .cond _ body =>
      decide (∀ fn ∈ funNames body, fn ∉ fdom) && chkFScopedStmts (funNames body ++ fdom) body
  | .funDef _ _ _ body =>
      decide (∀ fn ∈ funNames body, fn ∉ fdom) && chkFScopedStmts (funNames body ++ fdom) body
  | .switch _ cases dflt => chkFScopedCases fdom cases && chkFScopedDflt fdom dflt
  | .forLoop init _ post body =>
      (decide (∀ fn ∈ funNames init, fn ∉ fdom) &&
        chkFScopedStmts (funNames init ++ fdom) init) &&
      (decide (∀ fn ∈ funNames body, fn ∉ funNames init ++ fdom) &&
        chkFScopedStmts (funNames body ++ funNames init ++ fdom) body) &&
      (decide (∀ fn ∈ funNames post, fn ∉ funNames init ++ fdom) &&
        chkFScopedStmts (funNames post ++ funNames init ++ fdom) post)
  | _ => true
def chkFScopedCases (fdom : List Ident) : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, body) :: rest =>
      (decide (∀ fn ∈ funNames body, fn ∉ fdom) &&
        chkFScopedStmts (funNames body ++ fdom) body) && chkFScopedCases fdom rest
def chkFScopedDflt (fdom : List Ident) : Option (List (Stmt Op)) → Bool
  | none => true
  | some body =>
      decide (∀ fn ∈ funNames body, fn ∉ fdom) && chkFScopedStmts (funNames body ++ fdom) body
end

mutual
theorem chkFScopedStmts_sound : ∀ {fdom : List Ident} {ss : List (Stmt Op)},
    chkFScopedStmts fdom ss = true → FScopedStmts fdom ss
  | _, [], _ => trivial
  | _, s :: rest, h => by
      simp only [chkFScopedStmts, Bool.and_eq_true] at h
      exact ⟨chkFScopedStmt_sound h.1, chkFScopedStmts_sound h.2⟩
theorem chkFScopedStmt_sound : ∀ {fdom : List Ident} {s : Stmt Op},
    chkFScopedStmt fdom s = true → FScopedStmt fdom s
  | _, .block body, h => by
      simp only [chkFScopedStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkFScopedStmts_sound h.2⟩
  | _, .cond _ body, h => by
      simp only [chkFScopedStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkFScopedStmts_sound h.2⟩
  | _, .funDef _ _ _ body, h => by
      simp only [chkFScopedStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkFScopedStmts_sound h.2⟩
  | _, .switch _ cases dflt, h => by
      simp only [chkFScopedStmt, Bool.and_eq_true] at h
      exact ⟨chkFScopedCases_sound h.1, chkFScopedDflt_sound h.2⟩
  | _, .forLoop init _ post body, h => by
      simp only [chkFScopedStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1.1, chkFScopedStmts_sound h.1.1.2,
        ⟨h.1.2.1, chkFScopedStmts_sound h.1.2.2⟩,
        ⟨h.2.1, chkFScopedStmts_sound h.2.2⟩⟩
  | _, .letDecl _ _, _ => trivial
  | _, .assign _ _, _ => trivial
  | _, .exprStmt _, _ => trivial
  | _, .«break», _ => trivial
  | _, .«continue», _ => trivial
  | _, .leave, _ => trivial
theorem chkFScopedCases_sound : ∀ {fdom : List Ident} {cs : List (Literal × List (Stmt Op))},
    chkFScopedCases fdom cs = true → FScopedCases fdom cs
  | _, [], _ => trivial
  | _, (_, body) :: rest, h => by
      simp only [chkFScopedCases, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨⟨h.1.1, chkFScopedStmts_sound h.1.2⟩, chkFScopedCases_sound h.2⟩
theorem chkFScopedDflt_sound : ∀ {fdom : List Ident} {dflt : Option (List (Stmt Op))},
    chkFScopedDflt fdom dflt = true → FScopedDflt fdom dflt
  | _, none, _ => trivial
  | _, some body, h => by
      simp only [chkFScopedDflt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, chkFScopedStmts_sound h.2⟩
end

/-! ### `FunctionsHoisted` and `ForInitEmpty` (for the block flattener's guard) -/

mutual
def chkNoFunDefStmt : Stmt Op → Bool
  | .funDef _ _ _ _ => false
  | .block body => chkNoFunDefStmts body
  | .cond _ body => chkNoFunDefStmts body
  | .switch _ cases dflt => chkNoFunDefCases cases && chkNoFunDefDflt dflt
  | .forLoop init _ post body =>
      chkNoFunDefStmts init && chkNoFunDefStmts post && chkNoFunDefStmts body
  | _ => true
def chkNoFunDefStmts : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => chkNoFunDefStmt s && chkNoFunDefStmts rest
def chkNoFunDefCases : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, b) :: rest => chkNoFunDefStmts b && chkNoFunDefCases rest
def chkNoFunDefDflt : Option (List (Stmt Op)) → Bool
  | none => true
  | some b => chkNoFunDefStmts b
end

mutual
theorem chkNoFunDefStmt_sound : ∀ {s : Stmt Op},
    chkNoFunDefStmt s = true → NormalForm.NoFunDefStmt s
  | .funDef _ _ _ _, h => by simp [chkNoFunDefStmt] at h
  | .block body, h => chkNoFunDefStmts_sound (by simpa [chkNoFunDefStmt] using h)
  | .cond _ body, h => chkNoFunDefStmts_sound (by simpa [chkNoFunDefStmt] using h)
  | .switch _ cases dflt, h => by
      simp only [chkNoFunDefStmt, Bool.and_eq_true] at h
      exact ⟨chkNoFunDefCases_sound h.1, chkNoFunDefDflt_sound h.2⟩
  | .forLoop init _ post body, h => by
      simp only [chkNoFunDefStmt, Bool.and_eq_true] at h
      exact ⟨chkNoFunDefStmts_sound h.1.1, chkNoFunDefStmts_sound h.1.2,
        chkNoFunDefStmts_sound h.2⟩
  | .letDecl _ _, _ => trivial
  | .assign _ _, _ => trivial
  | .exprStmt _, _ => trivial
  | .«break», _ => trivial
  | .«continue», _ => trivial
  | .leave, _ => trivial
theorem chkNoFunDefStmts_sound : ∀ {ss : List (Stmt Op)},
    chkNoFunDefStmts ss = true → NormalForm.NoFunDefStmts ss
  | [], _ => trivial
  | s :: rest, h => by
      simp only [chkNoFunDefStmts, Bool.and_eq_true] at h
      exact ⟨chkNoFunDefStmt_sound h.1, chkNoFunDefStmts_sound h.2⟩
theorem chkNoFunDefCases_sound : ∀ {cs : List (Literal × List (Stmt Op))},
    chkNoFunDefCases cs = true → NormalForm.NoFunDefCases cs
  | [], _ => trivial
  | (_, b) :: rest, h => by
      simp only [chkNoFunDefCases, Bool.and_eq_true] at h
      exact ⟨chkNoFunDefStmts_sound h.1, chkNoFunDefCases_sound h.2⟩
theorem chkNoFunDefDflt_sound : ∀ {dflt : Option (List (Stmt Op))},
    chkNoFunDefDflt dflt = true → NormalForm.NoFunDefDflt dflt
  | none, _ => trivial
  | some b, h => chkNoFunDefStmts_sound (by simpa [chkNoFunDefDflt] using h)
end

def chkHoistedTop : Stmt Op → Bool
  | .funDef _ _ _ body => chkNoFunDefStmts body
  | .block body => chkNoFunDefStmts body
  | .cond _ body => chkNoFunDefStmts body
  | .switch _ cases dflt => chkNoFunDefCases cases && chkNoFunDefDflt dflt
  | .forLoop init _ post body =>
      chkNoFunDefStmts init && chkNoFunDefStmts post && chkNoFunDefStmts body
  | _ => true

theorem chkHoistedTop_sound : ∀ {s : Stmt Op},
    chkHoistedTop s = true → NormalForm.HoistedTop s
  | .funDef _ _ _ body, h => chkNoFunDefStmts_sound (by simpa [chkHoistedTop] using h)
  | .block body, h => chkNoFunDefStmt_sound (s := .block body)
      (by simpa [chkHoistedTop, chkNoFunDefStmt] using h)
  | .cond c body, h => chkNoFunDefStmt_sound (s := .cond c body)
      (by simpa [chkHoistedTop, chkNoFunDefStmt] using h)
  | .switch c cases dflt, h => chkNoFunDefStmt_sound (s := .switch c cases dflt)
      (by simpa [chkHoistedTop, chkNoFunDefStmt] using h)
  | .forLoop init c post body, h => chkNoFunDefStmt_sound (s := .forLoop init c post body)
      (by simpa [chkHoistedTop, chkNoFunDefStmt] using h)
  | .letDecl _ _, _ => trivial
  | .assign _ _, _ => trivial
  | .exprStmt _, _ => trivial
  | .«break», _ => trivial
  | .«continue», _ => trivial
  | .leave, _ => trivial

def chkFunctionsHoisted (b : Block Op) : Bool := b.all chkHoistedTop

theorem chkFunctionsHoisted_sound {b : Block Op} (h : chkFunctionsHoisted b = true) :
    NormalForm.FunctionsHoisted b := by
  intro s hs
  exact chkHoistedTop_sound (List.all_eq_true.mp h s hs)

mutual
def chkForInitEmptyStmt : Stmt Op → Bool
  | .forLoop init _ post body =>
      decide (init = []) && chkForInitEmptyStmts post && chkForInitEmptyStmts body
  | .block body => chkForInitEmptyStmts body
  | .funDef _ _ _ body => chkForInitEmptyStmts body
  | .cond _ body => chkForInitEmptyStmts body
  | .switch _ cases dflt => chkForInitEmptyCases cases && chkForInitEmptyDflt dflt
  | _ => true
def chkForInitEmptyStmts : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => chkForInitEmptyStmt s && chkForInitEmptyStmts rest
def chkForInitEmptyCases : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, b) :: rest => chkForInitEmptyStmts b && chkForInitEmptyCases rest
def chkForInitEmptyDflt : Option (List (Stmt Op)) → Bool
  | none => true
  | some b => chkForInitEmptyStmts b
end

mutual
theorem chkForInitEmptyStmt_sound : ∀ {s : Stmt Op},
    chkForInitEmptyStmt s = true → NormalForm.ForInitEmptyStmt s
  | .forLoop init _ post body, h => by
      simp only [chkForInitEmptyStmt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1, chkForInitEmptyStmts_sound h.1.2, chkForInitEmptyStmts_sound h.2⟩
  | .block body, h => chkForInitEmptyStmts_sound (by simpa [chkForInitEmptyStmt] using h)
  | .funDef _ _ _ body, h =>
      chkForInitEmptyStmts_sound (by simpa [chkForInitEmptyStmt] using h)
  | .cond _ body, h => chkForInitEmptyStmts_sound (by simpa [chkForInitEmptyStmt] using h)
  | .switch _ cases dflt, h => by
      simp only [chkForInitEmptyStmt, Bool.and_eq_true] at h
      exact ⟨chkForInitEmptyCases_sound h.1, chkForInitEmptyDflt_sound h.2⟩
  | .letDecl _ _, _ => trivial
  | .assign _ _, _ => trivial
  | .exprStmt _, _ => trivial
  | .«break», _ => trivial
  | .«continue», _ => trivial
  | .leave, _ => trivial
theorem chkForInitEmptyStmts_sound : ∀ {ss : List (Stmt Op)},
    chkForInitEmptyStmts ss = true → NormalForm.ForInitEmptyStmts ss
  | [], _ => trivial
  | s :: rest, h => by
      simp only [chkForInitEmptyStmts, Bool.and_eq_true] at h
      exact ⟨chkForInitEmptyStmt_sound h.1, chkForInitEmptyStmts_sound h.2⟩
theorem chkForInitEmptyCases_sound : ∀ {cs : List (Literal × List (Stmt Op))},
    chkForInitEmptyCases cs = true → NormalForm.ForInitEmptyCases cs
  | [], _ => trivial
  | (_, b) :: rest, h => by
      simp only [chkForInitEmptyCases, Bool.and_eq_true] at h
      exact ⟨chkForInitEmptyStmts_sound h.1, chkForInitEmptyCases_sound h.2⟩
theorem chkForInitEmptyDflt_sound : ∀ {dflt : Option (List (Stmt Op))},
    chkForInitEmptyDflt dflt = true → NormalForm.ForInitEmptyDflt dflt
  | none, _ => trivial
  | some b, h => chkForInitEmptyStmts_sound (by simpa [chkForInitEmptyDflt] using h)
end

end YulEvmCompiler.Optimizer.Normalize
