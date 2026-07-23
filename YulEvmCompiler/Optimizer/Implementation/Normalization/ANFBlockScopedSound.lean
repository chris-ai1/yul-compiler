import YulEvmCompiler.Optimizer.Implementation.Normalization.ANFSound
import YulEvmCompiler.Optimizer.Implementation.Normalization.ANFBlockScoped
import YulEvmCompiler.Optimizer.Implementation.EmptyScope
import YulEvmCompiler.Optimizer.Implementation.StorageForwardSound
/-!
# ANF pass 1 — block-scoped flattening, soundness

Per-statement soundness of `bsStmt1` (block-scoped operand flattening), built
from the flatten-correctness lemmas (`ANFSound`) plus the block rule,
`restore_prefix`, and the empty-scope congruence (`EmptyScope`).

The reordering of pure operands past effectful ones is sound only for
well-scoped code, so the straight-line rewrites carry a scope hypothesis
(`freeVarsExpr e ⊆ dom V`); it is discharged for closed programs.
-/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics YulSemantics.EVM
open YulEvmCompiler.Optimizer (LocalPass)

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### Small structural helpers -/

/-- A single statement, as a one-element sequence. -/
theorem stmt_as_stmts {funs : FunEnv D} {s : Stmt Op} {V st V' st' o} :
    Step D funs V st (.stmt s) (.sres V' st' o) ↔
    Step D funs V st (.stmts [s]) (.sres V' st' o) := by
  constructor
  · intro h
    by_cases ho : o = .normal
    · subst ho; exact Step.seqCons h Step.seqNil
    · exact Step.seqStop h ho
  · intro h
    cases h with
    | seqCons hs hrest => cases hrest with | seqNil => exact hs
    | seqStop hs _ => exact hs

/-- `hoist` distributes over append. -/
theorem hoist_append (a b : List (Stmt Op)) :
    hoist D (a ++ b) = hoist D a ++ hoist D b := by
  simp [hoist, List.filterMap_append]

/-- A single-variable `let`-prelude contributes no function scope. -/
theorem hoist_letPrelude {pre : List (Stmt Op)}
    (h : ∀ s ∈ pre, ∃ t rhs, s = .letDecl [t] (some rhs)) : hoist D pre = [] := by
  induction pre with
  | nil => rfl
  | cons s rest ih =>
      obtain ⟨t, rhs, rfl⟩ := h s (List.mem_cons_self ..)
      simp only [hoist, List.filterMap_cons]
      exact ih (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))

/-- The prelude produced by `flattenTop` consists of single-variable `let`s. -/
theorem flattenTop_prelude_lets (P : String) (k : Nat) (e : Expr Op) :
    ∀ s ∈ (flattenTop P k e).2.1, ∃ t rhs, s = .letDecl [t] (some rhs) :=
  fun s hs => preludeOK_shape ((flattenTop_ok P k e).2 s hs)

/-- After a `flattenTop` prelude runs (any outcome), the environment is a prefix
extension of the start — so the enclosing `restore` discharges it. -/
theorem flattenTop_restore {funs : FunEnv D} {P k e V st Va' stM o}
    (hpre : Step D funs V st (.stmts (flattenTop P k e).2.1) (.sres Va' stM o)) :
    restore V Va' = V := by
  obtain ⟨ext, rfl⟩ := letPrelude_prefix _ (flattenTop_prelude_lets P k e) hpre
  exact restore_prefix V ext

/-- `hoist` of a `flattenTop` prelude followed by a non-`funDef` straight-line
statement is empty (the block introduces no function scope). -/
theorem hoist_flattenTop_body {P k e} {s : Stmt Op}
    (hs : hoist D [s] = []) : hoist D ((flattenTop P k e).2.1 ++ [s]) = [] := by
  rw [hoist_append, hoist_letPrelude (flattenTop_prelude_lets P k e), hs, List.nil_append]

/-- Build a block execution from its (empty-hoist) body execution. -/
theorem block_of_body {funs : FunEnv D} {V st body Vb stb o} (hh : hoist D body = [])
    (hb : Step D ([] :: funs) V st (.stmts body) (.sres Vb stb o)) :
    Step D funs V st (.stmt (.block body)) (.sres (restore V Vb) stb o) :=
  Step.block (by rw [hh]; exact hb)

/-! ### Per-statement soundness: `exprStmt` -/

theorem bsExprStmt_sound {funs : FunEnv D} {P : String} {e : Expr Op}
    (hnt : noTempExpr P e = true) {V : VEnv D} {st V' st' o}
    (hsc : ∀ x, x ∈ freeVarsExpr e → (VEnv.get V x).isSome = true) :
    Step D funs V st (.stmt (.exprStmt e)) (.sres V' st' o) ↔
    Step D funs V st (.stmts (bsStmt1 P (.exprStmt e))) (.sres V' st' o) := by
  have hlets := flattenTop_prelude_lets P 0 e
  have hhoist : hoist D ((flattenTop P 0 e).2.1 ++ [.exprStmt (flattenTop P 0 e).2.2]) = [] :=
    hoist_flattenTop_body (by simp [hoist])
  -- the core block equivalence
  have hblock : Step D funs V st (.stmt (.exprStmt e)) (.sres V' st' o) ↔
      Step D funs V st
        (.stmt (.block ((flattenTop P 0 e).2.1 ++ [.exprStmt (flattenTop P 0 e).2.2])))
        (.sres V' st' o) := by
    constructor
    · intro h
      cases h with
      | exprStmt he =>
          have he0 := Step.emptyExt_congr he (EmptyExt.head funs)
          obtain ⟨Va', stMid, hpre, _, he'⟩ := flattenTop_correct 0 he0 hnt (TempExt.refl V)
          have hbody : Step D ([] :: funs) V st
              (.stmts ((flattenTop P 0 e).2.1 ++ [.exprStmt (flattenTop P 0 e).2.2]))
              (.sres Va' _ .normal) :=
            stmts_append_normal hpre (Step.seqCons (Step.exprStmt he') Step.seqNil)
          have hblk := block_of_body hhoist hbody
          rwa [flattenTop_restore hpre] at hblk
      | exprStmtHalt he =>
          have he0 := Step.emptyExt_congr he (EmptyExt.head funs)
          rcases flattenTop_halt 0 he0 hnt (TempExt.refl V) with ⟨Va', hph⟩ | ⟨Va', stMid, hpre, he'h, _⟩
          · have hbody : Step D ([] :: funs) V st
                (.stmts ((flattenTop P 0 e).2.1 ++ [.exprStmt (flattenTop P 0 e).2.2]))
                (.sres Va' _ .halt) := stmts_append_stop hph (by simp)
            have hblk := block_of_body hhoist hbody
            rwa [flattenTop_restore hph] at hblk
          · have hbody : Step D ([] :: funs) V st
                (.stmts ((flattenTop P 0 e).2.1 ++ [.exprStmt (flattenTop P 0 e).2.2]))
                (.sres Va' _ .halt) :=
              stmts_append_normal hpre (Step.seqStop (Step.exprStmtHalt he'h) (by simp))
            have hblk := block_of_body hhoist hbody
            rwa [flattenTop_restore hpre] at hblk
    · intro h
      cases h with
      | block hb =>
          rw [hhoist] at hb
          rcases stmts_append_inv hb with ⟨hne, hph⟩ | ⟨Vm, stm, hpre, htail⟩
          · rcases letPrelude_outcome _ hlets hph with rfl | rfl
            · exact absurd rfl hne
            · rw [flattenTop_restore hph]
              exact Step.emptyExt_congr'
                (Step.exprStmtHalt ((flattenTop_halt_bwd 0 hnt (TempExt.refl V) hsc).1 hph))
                (EmptyExt.head funs)
          · cases htail with
            | seqCons htl hnil =>
                cases hnil with
                | seqNil =>
                    cases htl with
                    | exprStmt he' =>
                        obtain ⟨he, _⟩ := flattenTop_correct_bwd 0 hnt (TempExt.refl V) hpre he'
                        rw [flattenTop_restore hpre]
                        exact Step.emptyExt_congr' (Step.exprStmt he) (EmptyExt.head funs)
            | seqStop htl hne =>
                cases htl with
                | exprStmt _ => exact absurd rfl hne
                | exprStmtHalt he'h =>
                    rw [flattenTop_restore hpre]
                    exact Step.emptyExt_congr'
                      (Step.exprStmtHalt ((flattenTop_halt_bwd 0 hnt (TempExt.refl V) hsc).2 hpre he'h))
                      (EmptyExt.head funs)
  -- assemble via the `if pre.isEmpty` branches
  simp only [bsStmt1]
  split
  · exact stmt_as_stmts
  · exact hblock.trans stmt_as_stmts

/-- `restore` past the `flattenTop` temp prefix, through an assignment to
(non-temporary) source variables: the assignment lands on the enclosing
variables. -/
theorem flattenTop_restore_setMany {funs : FunEnv D} {P e V st Va' stM o} {vars vals}
    (hnti : noTempIdents P vars = true)
    (hpre : Step D funs V st (.stmts (flattenTop P 0 e).2.1) (.sres Va' stM o)) :
    restore V (VEnv.setMany Va' vars vals) = VEnv.setMany V vars vals := by
  obtain ⟨ext, rfl, hmem⟩ := letPrelude_prefix_keys _ (flattenTop_prelude_lets P 0 e) hpre
  have hdisj : ∀ p ∈ ext, p.1 ∉ vars := by
    intro p hp hpin
    obtain ⟨t, rhs, hmemPre, hpt⟩ := hmem p hp
    obtain ⟨m, hm⟩ := flattenTop_prelude_decl t ⟨rhs, hmemPre⟩
    have h1 : isTemp P p.1 = true := by rw [hpt, hm]; exact isTemp_tempName P m
    simp [noTempIdents_mem hnti p.1 hpin] at h1
  rw [setMany_append_disjoint ext hdisj]
  exact restore_prefix_len ext (setMany_length V vars vals)

/-! ### Per-statement soundness: `assign` -/

theorem bsAssign_sound {funs : FunEnv D} {P : String} {vars : List Ident} {e : Expr Op}
    (hnti : noTempIdents P vars = true) (hnt : noTempExpr P e = true)
    {V : VEnv D} {st V' st' o}
    (hsc : ∀ x, x ∈ freeVarsExpr e → (VEnv.get V x).isSome = true) :
    Step D funs V st (.stmt (.assign vars e)) (.sres V' st' o) ↔
    Step D funs V st (.stmts (bsStmt1 P (.assign vars e))) (.sres V' st' o) := by
  have hhoist : hoist D ((flattenTop P 0 e).2.1 ++ [.assign vars (flattenTop P 0 e).2.2]) = [] :=
    hoist_flattenTop_body (by simp [hoist])
  have hblock : Step D funs V st (.stmt (.assign vars e)) (.sres V' st' o) ↔
      Step D funs V st
        (.stmt (.block ((flattenTop P 0 e).2.1 ++ [.assign vars (flattenTop P 0 e).2.2])))
        (.sres V' st' o) := by
    constructor
    · intro h
      cases h with
      | assignVal he hlen =>
          have he0 := Step.emptyExt_congr he (EmptyExt.head funs)
          obtain ⟨Va', stMid, hpre, _, he'⟩ := flattenTop_correct 0 he0 hnt (TempExt.refl V)
          have hbody := stmts_append_normal hpre (Step.seqCons (Step.assignVal he' hlen) Step.seqNil)
          have hblk := block_of_body hhoist hbody
          rwa [flattenTop_restore_setMany hnti hpre] at hblk
      | assignHalt he =>
          have he0 := Step.emptyExt_congr he (EmptyExt.head funs)
          rcases flattenTop_halt 0 he0 hnt (TempExt.refl V) with ⟨Va', hph⟩ | ⟨Va', stMid, hpre, he'h, _⟩
          · have hbody : Step D ([] :: funs) V st
                (.stmts ((flattenTop P 0 e).2.1 ++ [.assign vars (flattenTop P 0 e).2.2]))
                (.sres Va' _ .halt) := stmts_append_stop hph (by simp)
            have hblk := block_of_body hhoist hbody
            rwa [flattenTop_restore hph] at hblk
          · have hbody : Step D ([] :: funs) V st
                (.stmts ((flattenTop P 0 e).2.1 ++ [.assign vars (flattenTop P 0 e).2.2]))
                (.sres Va' _ .halt) :=
              stmts_append_normal hpre (Step.seqStop (Step.assignHalt he'h) (by simp))
            have hblk := block_of_body hhoist hbody
            rwa [flattenTop_restore hpre] at hblk
    · intro h
      cases h with
      | block hb =>
          rw [hhoist] at hb
          rcases stmts_append_inv hb with ⟨hne, hph⟩ | ⟨Vm, stm, hpre, htail⟩
          · rcases letPrelude_outcome _ (flattenTop_prelude_lets P 0 e) hph with rfl | rfl
            · exact absurd rfl hne
            · rw [flattenTop_restore hph]
              exact Step.emptyExt_congr'
                (Step.assignHalt ((flattenTop_halt_bwd 0 hnt (TempExt.refl V) hsc).1 hph))
                (EmptyExt.head funs)
          · cases htail with
            | seqCons htl hnil =>
                cases hnil with
                | seqNil =>
                    cases htl with
                    | assignVal he' hlen =>
                        obtain ⟨he, _⟩ := flattenTop_correct_bwd 0 hnt (TempExt.refl V) hpre he'
                        rw [flattenTop_restore_setMany hnti hpre]
                        exact Step.emptyExt_congr' (Step.assignVal he hlen) (EmptyExt.head funs)
            | seqStop htl hne =>
                cases htl with
                | assignVal _ _ => exact absurd rfl hne
                | assignHalt he'h =>
                    rw [flattenTop_restore hpre]
                    exact Step.emptyExt_congr'
                      (Step.assignHalt ((flattenTop_halt_bwd 0 hnt (TempExt.refl V) hsc).2 hpre he'h))
                      (EmptyExt.head funs)
  simp only [bsStmt1]
  split
  · exact stmt_as_stmts
  · exact hblock.trans stmt_as_stmts

/-! ### Per-statement soundness (all statement forms) -/

/-- The source variables a statement's flattened operands read (only the
straight-line forms that `bsStmt1` rewrites; identity forms need no scope). -/
def stmtFreeVars : Stmt Op → List Ident
  | .assign _ e => freeVarsExpr e
  | .exprStmt e => freeVarsExpr e
  | _ => []

theorem bsStmt1_sound {funs : FunEnv D} {P : String} {s : Stmt Op}
    (hnt : noTempStmt P s = true) {V : VEnv D} {st V' st' o}
    (hsc : ∀ x, x ∈ stmtFreeVars s → (VEnv.get V x).isSome = true) :
    Step D funs V st (.stmt s) (.sres V' st' o) ↔
    Step D funs V st (.stmts (bsStmt1 P s)) (.sres V' st' o) := by
  cases s with
  | assign vars e =>
      simp only [noTempStmt, Bool.and_eq_true] at hnt
      exact bsAssign_sound hnt.1 hnt.2 (by simpa [stmtFreeVars] using hsc)
  | exprStmt e =>
      exact bsExprStmt_sound (by simpa [noTempStmt] using hnt) (by simpa [stmtFreeVars] using hsc)
  | letDecl vars val => exact stmt_as_stmts
  | block body => exact stmt_as_stmts
  | funDef n ps rs b => exact stmt_as_stmts
  | cond c body => exact stmt_as_stmts
  | switch c cs dflt => exact stmt_as_stmts
  | forLoop init c post body => exact stmt_as_stmts
  | «break» => exact stmt_as_stmts
  | «continue» => exact stmt_as_stmts
  | leave => exact stmt_as_stmts

/-! ### Statement-sequence soundness -/

/-- Executing a statement (to `normal`) only grows the variable domain, by at
most its declared variables — and a `let`'s declared variables *are* added. -/
theorem stmt_keys_grow {funs : FunEnv D} {s : Stmt Op} {V st V1 st1}
    (h : Step D funs V st (.stmt s) (.sres V1 st1 .normal)) :
    ∀ x, (x ∈ declaredStmts [s] ∨ x ∈ V.map Prod.fst) → x ∈ V1.map Prod.fst := by
  intro x hx
  rcases hx with hdec | hold
  · cases s with
    | letDecl xs val =>
        cases h with
        | letVal hval hlen =>
            simp only [declaredStmts, List.append_nil] at hdec
            simp only [List.map_append, List.mem_append]
            exact Or.inl (by rw [List.map_fst_zip (by omega)]; exact hdec)
        | letZero =>
            simp only [declaredStmts, List.append_nil] at hdec
            simp only [bindZeros, List.map_append, List.map_map, List.mem_append]
            exact Or.inl (by simpa using hdec)
    | assign _ _ => simp [declaredStmts] at hdec
    | exprStmt _ => simp [declaredStmts] at hdec
    | block _ => simp [declaredStmts] at hdec
    | funDef _ _ _ _ => simp [declaredStmts] at hdec
    | cond _ _ => simp [declaredStmts] at hdec
    | switch _ _ _ => simp [declaredStmts] at hdec
    | forLoop _ _ _ _ => simp [declaredStmts] at hdec
    | «break» => simp [declaredStmts] at hdec
    | «continue» => simp [declaredStmts] at hdec
    | leave => simp [declaredStmts] at hdec
  · obtain ⟨ext, W, hV1, hWk, _⟩ := scopeFrame_stmt_normal h
    subst hV1
    simp only [List.map_append, List.mem_append]
    exact Or.inr (hWk ▸ hold)

/-- Well-scopedness of a statement list in scope `Γ`: each statement's flattened
operands read only in-scope variables; declarations extend the scope. -/
def WScoped : List Ident → List (Stmt Op) → Prop
  | _, [] => True
  | Γ, s :: rest => (∀ x ∈ stmtFreeVars s, x ∈ Γ) ∧ WScoped (declaredStmts [s] ++ Γ) rest

/-- No temporaries in a statement list. -/
def noTempStmtsL (P : String) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => noTempStmt P s && noTempStmtsL P rest

theorem bsStmts_sound {funs : FunEnv D} {P : String} :
    ∀ (ss : List (Stmt Op)) {V : VEnv D} {st V' st' o} (Γ : List Ident),
      noTempStmtsL P ss = true → WScoped Γ ss → (∀ x ∈ Γ, (VEnv.get V x).isSome = true) →
      (Step D funs V st (.stmts ss) (.sres V' st' o) ↔
        Step D funs V st (.stmts (bsStmts P ss)) (.sres V' st' o))
  | [], _, _, _, _, _, _, _, _, _ => by simp only [bsStmts_nil]
  | s :: rest, V, st, V', st', o, Γ, hnt, hws, hΓ => by
      simp only [noTempStmtsL, Bool.and_eq_true] at hnt
      simp only [bsStmts_cons]
      have hscS : ∀ x, x ∈ stmtFreeVars s → (VEnv.get V x).isSome = true :=
        fun x hx => hΓ x (hws.1 x hx)
      constructor
      · intro h
        cases h with
        | seqCons hs hrest =>
            rename_i V1 st1
            have hhead := (bsStmt1_sound hnt.1 hscS).mp hs
            have hΓ' : ∀ x ∈ declaredStmts [s] ++ Γ, (VEnv.get V1 x).isSome = true := by
              intro x hx
              rcases List.mem_append.mp hx with hd | hg
              · exact venvGet_isSome_of_mem_keys (stmt_keys_grow hs x (Or.inl hd))
              · exact venvGet_isSome_of_mem_keys (stmt_keys_grow hs x (Or.inr (mem_keys_of_isSome (hΓ x hg))))
            have htail := (bsStmts_sound rest (declaredStmts [s] ++ Γ) hnt.2 hws.2 hΓ').mp hrest
            exact stmts_append_normal hhead htail
        | seqStop hs hne =>
            have hhead := (bsStmt1_sound hnt.1 hscS).mp hs
            exact stmts_append_stop hhead hne
      · intro h
        rcases stmts_append_inv h with ⟨hne, hh⟩ | ⟨Vm, stm, hhead, htail⟩
        · exact Step.seqStop ((bsStmt1_sound hnt.1 hscS).mpr hh) hne
        · have hs := (bsStmt1_sound hnt.1 hscS).mpr hhead
          have hΓ' : ∀ x ∈ declaredStmts [s] ++ Γ, (VEnv.get Vm x).isSome = true := by
            intro x hx
            rcases List.mem_append.mp hx with hd | hg
            · exact venvGet_isSome_of_mem_keys (stmt_keys_grow hs x (Or.inl hd))
            · exact venvGet_isSome_of_mem_keys (stmt_keys_grow hs x (Or.inr (mem_keys_of_isSome (hΓ x hg))))
          exact Step.seqCons hs ((bsStmts_sound rest (declaredStmts [s] ++ Γ) hnt.2 hws.2 hΓ').mpr htail)

/-! ### Whole-block soundness (under freshness + closedness) -/

theorem hoist_bsStmt1 (P : String) (s : Stmt Op) : hoist D (bsStmt1 P s) = hoist D [s] := by
  cases s with
  | assign vars e => simp only [bsStmt1]; split
                     · rfl
                     · simp [hoist]
  | exprStmt e => simp only [bsStmt1]; split
                  · rfl
                  · simp [hoist]
  | _ => rfl

theorem hoist_bsStmts (P : String) : ∀ (ss : List (Stmt Op)),
    hoist D (bsStmts P ss) = hoist D ss
  | [] => rfl
  | s :: rest => by
      rw [bsStmts_cons, hoist_append, hoist_bsStmt1 P s, hoist_bsStmts P rest,
        show (s :: rest) = [s] ++ rest from rfl, hoist_append]

/-- **Block-scoped ANF preserves behavior**, for a well-scoped (closed) block
under a fresh temporary prefix. -/
theorem bsStmts_sound_block {P : String} {b : Block Op}
    (hnt : noTempStmtsL P b = true) (hcl : WScoped [] b) :
    EquivBlock D b (bsStmts P b) := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hb =>
        refine Step.block ?_
        rw [hoist_bsStmts]
        exact (bsStmts_sound b [] hnt hcl (by simp)).mp hb
  · intro h
    cases h with
    | block hb =>
        rw [hoist_bsStmts] at hb
        exact Step.block ((bsStmts_sound b [] hnt hcl (by simp)).mpr hb)

end YulEvmCompiler.Optimizer.ANF
