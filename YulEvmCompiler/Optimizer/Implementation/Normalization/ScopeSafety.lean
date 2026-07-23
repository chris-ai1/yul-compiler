import YulSemantics.BigStep
import YulEvmCompiler.Optimizer.Implementation.Normalization.ANF
/-!
# YulEvmCompiler.Optimizer.Implementation.Normalization.ScopeSafety

Reusable scope-safety meta-theory for the big-step semantics: **free variables**
of expressions, the fact that an **atom list never gets stuck** when its
variables are bound, and the **shape of a `let`-prelude's** resulting
environment (a prefix extension). These are the ingredients a source-to-source
pass needs when it hoists/reorders operands and must argue that a well-scoped
program's atoms remain evaluable.

They are dialect-generic and independent of any particular pass; the ANF
soundness (`ANFSound`) is the first consumer, but the redundant-store pass and
others will reuse the same facts.
-/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics
open YulSemantics.EVM (Op)

/-! ### Free variables -/

mutual
/-- The variables read by an expression. -/
def freeVarsExpr : Expr Op → List Ident
  | .var x => [x]
  | .lit _ => []
  | .builtin _ args => freeVarsArgs args
  | .call _ args => freeVarsArgs args
/-- The variables read by an argument list. -/
def freeVarsArgs : List (Expr Op) → List Ident
  | [] => []
  | e :: rest => freeVarsExpr e ++ freeVarsArgs rest
end

@[simp] theorem freeVarsArgs_cons (e : Expr Op) (rest : List (Expr Op)) :
    freeVarsArgs (e :: rest) = freeVarsExpr e ++ freeVarsArgs rest := rfl

/-- A variable-atom of a list is one of its free variables. -/
theorem mem_freeVars_of_mem_var {es : List (Expr Op)} {x : Ident}
    (h : Expr.var x ∈ es) : x ∈ freeVarsArgs es := by
  induction es with
  | nil => simp at h
  | cons e rest ih =>
      rcases List.mem_cons.mp h with rfl | hrest
      · simp [freeVarsExpr]
      · exact List.mem_append.mpr (Or.inr (ih hrest))

/-! ### `restore`/`setMany` past a temporary prefix (dialect-generic)

An assignment to source variables commutes with a prepended block of
temporaries (disjoint names), and `restore` then discharges the temporaries —
so a block-scoped rewrite's assignment lands on the enclosing variables exactly
as the un-rewritten assignment would. -/

section Generic
variable {D : Dialect}

/-- Membership in the key list is equivalent to being bound. -/
theorem venvGet_isSome_of_mem_keys {V : VEnv D} {x : Ident}
    (h : x ∈ V.map Prod.fst) : (VEnv.get V x).isSome = true := by
  induction V with
  | nil => simp at h
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyx : y = x
      · subst hyx; simp [VEnv.get]
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hyx
        · simpa [VEnv.get, List.find?, hyx] using ih h

theorem mem_keys_of_isSome {V : VEnv D} {x : Ident}
    (h : (VEnv.get V x).isSome = true) : x ∈ V.map Prod.fst := by
  induction V with
  | nil => simp [VEnv.get] at h
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyx : y = x
      · subst hyx; simp
      · simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih (by simpa [VEnv.get, List.find?, hyx] using h))

/-- `VEnv.set` preserves length. -/
theorem set_length' (V : VEnv D) (x : Ident) (v : D.Value) :
    (VEnv.set V x v).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases h : y = x
      · subst h; simp [VEnv.set]
      · simp [VEnv.set, h, ih]

/-- `VEnv.setMany` preserves length. -/
theorem setMany_length (V : VEnv D) (xs : List Ident) (vs : List D.Value) :
    (VEnv.setMany V xs vs).length = V.length := by
  unfold VEnv.setMany
  induction (xs.zip vs) generalizing V with
  | nil => rfl
  | cons p rest ih => simp only [List.foldl_cons]; rw [ih]; exact set_length' V p.1 p.2

/-- Setting a variable disjoint from a prepended block lands past the block. -/
theorem set_append_disjoint {V : VEnv D} {x : Ident} {v : D.Value} (ext : VEnv D)
    (hd : ∀ p ∈ ext, p.1 ≠ x) : VEnv.set (ext ++ V) x v = ext ++ VEnv.set V x v := by
  induction ext with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      have hyx : ¬ (y = x) := hd (y, w) (List.mem_cons_self ..)
      rw [List.cons_append]
      show VEnv.set ((y, w) :: (rest ++ V)) x v = (y, w) :: (rest ++ VEnv.set V x v)
      rw [VEnv.set, if_neg hyx, ih (fun q hq => hd q (List.mem_cons_of_mem _ hq))]

private theorem foldl_set_append_disjoint (ext : VEnv D) :
    ∀ (l : List (Ident × D.Value)),
      (∀ p ∈ ext, ∀ q ∈ l, p.1 ≠ q.1) → ∀ (V : VEnv D),
      l.foldl (fun acc p => VEnv.set acc p.1 p.2) (ext ++ V)
        = ext ++ l.foldl (fun acc p => VEnv.set acc p.1 p.2) V
  | [], _, _ => rfl
  | q :: rest, hd, V => by
      simp only [List.foldl_cons]
      rw [set_append_disjoint ext (fun p hp => hd p hp q (List.mem_cons_self ..))]
      exact foldl_set_append_disjoint ext rest
        (fun p hp r hr => hd p hp r (List.mem_cons_of_mem _ hr)) _

/-- `setMany` to variables disjoint from a prepended block lands past the block. -/
theorem setMany_append_disjoint {V : VEnv D} (ext : VEnv D) {xs : List Ident} {vs : List D.Value}
    (hd : ∀ p ∈ ext, p.1 ∉ xs) :
    VEnv.setMany (ext ++ V) xs vs = ext ++ VEnv.setMany V xs vs := by
  unfold VEnv.setMany
  refine foldl_set_append_disjoint ext _ (fun p hp q hq => ?_) V
  intro heq
  apply hd p hp
  rw [heq]
  exact (List.of_mem_zip hq).1

/-- One step of `setMany`. -/
theorem setMany_cons (W : VEnv D) (x : Ident) (xs : List Ident) (v : D.Value) (vs : List D.Value) :
    VEnv.setMany W (x :: xs) (v :: vs) = VEnv.setMany (VEnv.set W x v) xs vs := by
  simp only [VEnv.setMany, List.zip_cons_cons, List.foldl_cons]

/-- Declaring variables to zero and then assigning them (block-scoped) reproduces
the direct `let`-binding, for distinct variables. -/
theorem setMany_bindZeros : ∀ {vars : List Ident} {vals : List D.Value} {V : VEnv D},
    vals.length = vars.length → vars.Nodup →
    VEnv.setMany (bindZeros D vars ++ V) vars vals = vars.zip vals ++ V
  | [], [], V, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | x :: xs, [], _, hlen, _ => by simp at hlen
  | x :: xs, v :: vs, V, hlen, hnd => by
      have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hlen' : vs.length = xs.length := by simpa using hlen
      have hbz : bindZeros D (x :: xs) = (x, D.zero) :: bindZeros D xs := rfl
      rw [hbz, List.cons_append, setMany_cons]
      have hset : VEnv.set ((x, D.zero) :: (bindZeros D xs ++ V)) x v
          = (x, v) :: (bindZeros D xs ++ V) := by simp [VEnv.set]
      have hdisj : ∀ p ∈ ([(x, v)] : VEnv D), p.1 ∉ xs := by
        intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hx
      rw [hset,
        show (x, v) :: (bindZeros D xs ++ V) = [(x, v)] ++ (bindZeros D xs ++ V) from rfl,
        setMany_append_disjoint [(x, v)] hdisj, setMany_bindZeros hlen' hnd']
      simp [List.zip_cons_cons]

/-- `restore` past a prefix of a same-length replacement recovers the replacement
(generalizes `restore_prefix` to allow in-place updates in the suffix). -/
theorem restore_prefix_len {V W : VEnv D} (ext : VEnv D) (hlen : W.length = V.length) :
    restore V (ext ++ W) = W := by
  unfold restore
  rw [List.length_append, hlen, Nat.add_sub_cancel]
  induction ext with
  | nil => simp
  | cons a as ih => simpa using ih

end Generic

open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### Atoms never get stuck when bound

An atom (variable/literal) reads no state and makes no call, so as long as every
variable-atom is bound, the list evaluates — to some values, at the same state.
This is the "progress for atoms" fact the reordering argument needs. -/

theorem atomArgs_eval_of_bound {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {es : List (Expr Op)} (hatom : atomicArgs es = true)
    (hb : ∀ x, Expr.var x ∈ es → (VEnv.get V x).isSome = true) :
    ∃ vs, Step D funs V st (.args es) (.eres (.vals vs st)) := by
  induction es with
  | nil => exact ⟨[], Step.argsNil⟩
  | cons e rest ih =>
      simp only [atomicArgs, Bool.and_eq_true] at hatom
      obtain ⟨rvs, hrest⟩ := ih hatom.2 (fun x hx => hb x (List.mem_cons_of_mem _ hx))
      cases e with
      | var y =>
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hb y (List.mem_cons_self ..))
          exact ⟨v :: rvs, Step.argsCons hrest (Step.var hv)⟩
      | lit l => exact ⟨_, Step.argsCons hrest Step.lit⟩
      | builtin _ _ => simp [isAtom] at hatom
      | call _ _ => simp [isAtom] at hatom

/-- Prepending bindings never unbinds a variable: boundedness is preserved. -/
theorem get_append_isSome {V : VEnv D} {x : Ident} (ext : VEnv D)
    (h : (VEnv.get V x).isSome = true) : (VEnv.get (ext ++ V) x).isSome = true := by
  induction ext with
  | nil => simpa using h
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyx : y = x
      · subst hyx; simp [VEnv.get]
      · rw [List.cons_append]
        simpa [VEnv.get, List.find?, hyx] using ih

/-- An atom list never halts: atoms are variable reads / literals, which produce
values, so no `halt` result is derivable. -/
theorem atomArgs_no_halt {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {es : List (Expr Op)} {sth} (hatom : atomicArgs es = true)
    (h : Step D funs V st (.args es) (.eres (.halt sth))) : False := by
  induction es with
  | nil => cases h
  | cons e rest ih =>
      simp only [atomicArgs, Bool.and_eq_true] at hatom
      cases h with
      | argsRestHalt hrh => exact ih hatom.2 hrh
      | argsHeadHalt hrest hhead =>
          cases e with
          | var y => cases hhead
          | lit l => cases hhead
          | builtin _ _ => simp [isAtom] at hatom
          | call _ _ => simp [isAtom] at hatom

/-! ### The shape of a `let`-prelude's environment

Executing a list of single-variable `let`s only ever prepends bindings, so the
resulting environment is a prefix extension of the starting one — whatever the
outcome (a halting `let` prepends nothing). This is what lets the enclosing
block's length-based `restore` discharge exactly the introduced temporaries. -/

theorem letPrelude_prefix {funs : FunEnv D} :
    ∀ (pre : List (Stmt Op)) {V V' : VEnv D} {st st' o},
      (∀ s ∈ pre, ∃ t rhs, s = .letDecl [t] (some rhs)) →
      Step D funs V st (.stmts pre) (.sres V' st' o) →
      ∃ ext, V' = ext ++ V
  | [], _, _, _, _, _, _, h => by cases h with | seqNil => exact ⟨[], rfl⟩
  | s :: rest, _, _, _, _, _, hOK, h => by
      obtain ⟨t, rhs, rfl⟩ := hOK s (List.mem_cons_self ..)
      cases h with
      | seqCons hs hrest =>
          cases hs with
          | letVal hval hlen =>
              rename_i vals
              obtain ⟨v, rfl⟩ : ∃ v, vals = [v] := by
                cases vals with
                | nil => simp at hlen
                | cons b tl => cases tl with
                  | nil => exact ⟨b, rfl⟩
                  | cons _ _ => simp at hlen
              obtain ⟨ext, rfl⟩ := letPrelude_prefix rest
                (fun s' hs' => hOK s' (List.mem_cons_of_mem _ hs')) hrest
              exact ⟨ext ++ [(t, v)], by simp⟩
      | seqStop hs hne =>
          cases hs with
          | letVal _ _ => exact absurd rfl hne
          | letHalt _ => exact ⟨[], rfl⟩

/-- Like `letPrelude_prefix`, but also records that each prepended binding's name
is one of the prelude's declared variables. -/
theorem letPrelude_prefix_keys {funs : FunEnv D} :
    ∀ (pre : List (Stmt Op)) {V V' : VEnv D} {st st' o},
      (∀ s ∈ pre, ∃ t rhs, s = .letDecl [t] (some rhs)) →
      Step D funs V st (.stmts pre) (.sres V' st' o) →
      ∃ ext, V' = ext ++ V ∧
        ∀ p ∈ ext, ∃ t rhs, Stmt.letDecl [t] (some rhs) ∈ pre ∧ p.1 = t
  | [], _, _, _, _, _, _, h => by cases h with | seqNil => exact ⟨[], rfl, by simp⟩
  | s :: rest, _, _, _, _, _, hOK, h => by
      obtain ⟨t, rhs, rfl⟩ := hOK s (List.mem_cons_self ..)
      cases h with
      | seqCons hs hrest =>
          cases hs with
          | letVal hval hlen =>
              rename_i vals
              obtain ⟨v, rfl⟩ : ∃ v, vals = [v] := by
                cases vals with
                | nil => simp at hlen
                | cons b tl => cases tl with
                  | nil => exact ⟨b, rfl⟩
                  | cons _ _ => simp at hlen
              obtain ⟨ext, hrfl, hmem⟩ := letPrelude_prefix_keys rest
                (fun s' hs' => hOK s' (List.mem_cons_of_mem _ hs')) hrest
              refine ⟨ext ++ [(t, v)], by rw [hrfl]; simp, ?_⟩
              intro p hp
              rcases List.mem_append.mp hp with hpe | hpt
              · obtain ⟨t', rhs', hmem', hpt'⟩ := hmem p hpe
                exact ⟨t', rhs', List.mem_cons_of_mem _ hmem', hpt'⟩
              · rw [List.mem_singleton] at hpt; subst hpt
                exact ⟨t, rhs, List.mem_cons_self .., rfl⟩
      | seqStop hs hne =>
          cases hs with
          | letVal _ _ => exact absurd rfl hne
          | letHalt _ => exact ⟨[], rfl, by simp⟩

/-- A prelude of single-variable `let`s produces `normal` or `halt` — never a
loop control outcome (`break`/`continue`/`leave`). -/
theorem letPrelude_outcome {funs : FunEnv D} :
    ∀ (pre : List (Stmt Op)) {V V' : VEnv D} {st st' o},
      (∀ s ∈ pre, ∃ t rhs, s = .letDecl [t] (some rhs)) →
      Step D funs V st (.stmts pre) (.sres V' st' o) → o = .normal ∨ o = .halt
  | [], _, _, _, _, _, _, h => by cases h with | seqNil => exact Or.inl rfl
  | s :: rest, _, _, _, _, _, hOK, h => by
      obtain ⟨t, rhs, rfl⟩ := hOK s (List.mem_cons_self ..)
      cases h with
      | seqCons _ hrest =>
          exact letPrelude_outcome rest (fun s' hs' => hOK s' (List.mem_cons_of_mem _ hs')) hrest
      | seqStop hs hne =>
          cases hs with
          | letVal _ _ => exact absurd rfl hne
          | letHalt _ => exact Or.inr rfl

end YulEvmCompiler.Optimizer.ANF
