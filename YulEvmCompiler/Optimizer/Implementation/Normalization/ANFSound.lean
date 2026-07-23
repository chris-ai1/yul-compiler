import YulSemantics.BigStep
import YulEvmCompiler.Optimizer.Implementation.Normalization.ANF
import YulEvmCompiler.Optimizer.Implementation.Normalization.ScopeSafety
import YulEvmCompiler.Optimizer.Spec.LocalPass
/-!
# ANF normalizer — soundness foundations (`VEnv` weakening atoms)

The ANF normalizer introduces `let` temporaries that stay in scope, so proving
`EquivBlock b (anfBlock b)` needs a **fresh-binding weakening** lemma for `Step`:
a temporary that no code reads threads through execution unchanged and is popped
by the enclosing block's `restore`.

That lemma is a large mutual induction over the whole `Step` relation. It bottoms
out in how `VEnv.get`/`VEnv.set` behave across a prepended (fresh) binding — the
self-contained facts proved here. The `Step`-level weakening lemma and the ANF
temp-tracking simulation build on top; this file is their base.
-/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics
open YulSemantics.EVM (Op)

variable {D : Dialect}

/-- Reading a variable past a differently-named binding ignores that binding. -/
@[simp] theorem get_cons_ne {V : VEnv D} {x y : Ident} {w : D.Value} (h : y ≠ x) :
    VEnv.get ((y, w) :: V) x = VEnv.get V x := by
  simp [VEnv.get, List.find?, h]

/-- Reading a variable at its own (innermost) binding. -/
@[simp] theorem get_cons_self {V : VEnv D} {x : Ident} {w : D.Value} :
    VEnv.get ((x, w) :: V) x = some w := by
  simp [VEnv.get, List.find?]

/-- Assigning a variable past a differently-named binding leaves that binding and
recurses into the tail. -/
@[simp] theorem set_cons_ne {V : VEnv D} {x y : Ident} {w v : D.Value} (h : y ≠ x) :
    VEnv.set ((y, w) :: V) x v = (y, w) :: VEnv.set V x v := by
  simp [VEnv.set, h]

/-- Assigning a variable at its own (innermost) binding. -/
@[simp] theorem set_cons_self {V : VEnv D} {x : Ident} {w v : D.Value} :
    VEnv.set ((x, w) :: V) x v = (x, v) :: V := by
  simp [VEnv.set]

/-- A fresh binding is invisible to reads of any variable already in scope: if
`t` differs from `x`, prepending `(t, w)` does not change `x`'s value. This is
the read-side of the weakening lemma at a single binding. -/
theorem get_prepend_fresh {V : VEnv D} {x t : Ident} {w : D.Value} (h : t ≠ x) :
    VEnv.get ((t, w) :: V) x = VEnv.get V x :=
  get_cons_ne h

/-- Assigning an in-scope variable commutes with a fresh prepended binding: the
fresh binding is untouched and the assignment lands in the tail. This is the
write-side of the weakening lemma at a single binding. -/
theorem set_prepend_fresh {V : VEnv D} {x t : Ident} {w v : D.Value} (h : t ≠ x) :
    VEnv.set ((t, w) :: V) x v = (t, w) :: VEnv.set V x v :=
  set_cons_ne h

/-- `VEnv.set` preserves length — so `restore` (which truncates by length) is
insensitive to values written by an assignment. -/
theorem set_length (V : VEnv D) (x : Ident) (v : D.Value) :
    (VEnv.set V x v).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases h : y = x
      · subst h; simp [VEnv.set]
      · simp [VEnv.set, h, ih]

/-! ### Erasing temporaries: the environment "modulo fresh temps"

The simulation invariant relating the original and ANF'd executions is
`eraseTemps P Va = Vo`: the ANF environment with all temporary (prefix-`P`)
bindings removed equals the original environment. These lemmas show that
invariant is preserved by the environment operations — reads/writes of a
non-temp variable ignore the temps, declaring a temp is invisible to the
erasure, and declaring a non-temp commutes with it. -/

/-- `x` is a temporary of the ANF pass: its name starts with the fresh prefix.
Phrased on `toList` so prefix facts reduce to `List` reasoning. -/
def isTemp (P : String) (x : Ident) : Bool := (P.toList).isPrefixOf x.toList

/-- A list is a prefix of itself extended. -/
theorem List.isPrefixOf_append_self {α} [BEq α] [LawfulBEq α] (a b : List α) :
    a.isPrefixOf (a ++ b) = true := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, List.isPrefixOf, ih, beq_self_eq_true, Bool.and_true]

/-- Every temporary is `isTemp` (it starts with the prefix). -/
theorem isTemp_tempName (P : String) (k : Nat) : isTemp P (tempName P k) = true := by
  simp only [isTemp, tempName, String.toList_append]
  exact List.isPrefixOf_append_self _ _

/-- The environment with all temporary bindings removed. -/
def eraseTemps (P : String) (V : VEnv D) : VEnv D :=
  V.filter (fun p => ! isTemp P p.1)

@[simp] theorem eraseTemps_nil : eraseTemps P ([] : VEnv D) = [] := rfl

@[simp] theorem eraseTemps_cons_temp {V : VEnv D} {y : Ident} {w : D.Value}
    (h : isTemp P y = true) : eraseTemps P ((y, w) :: V) = eraseTemps P V := by
  simp [eraseTemps, h]

@[simp] theorem eraseTemps_cons_nonTemp {V : VEnv D} {y : Ident} {w : D.Value}
    (h : isTemp P y = false) :
    eraseTemps P ((y, w) :: V) = (y, w) :: eraseTemps P V := by
  simp [eraseTemps, h]

/-- Reading a non-temporary variable is unaffected by erasing temporaries. -/
theorem get_eraseTemps {V : VEnv D} {x : Ident} (h : isTemp P x = false) :
    VEnv.get (eraseTemps P V) x = VEnv.get V x := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases ht : isTemp P y = true
      · rw [eraseTemps_cons_temp ht, ih]
        have hyx : y ≠ x := by intro he; rw [he, h] at ht; exact absurd ht (by simp)
        rw [get_cons_ne hyx]
      · simp only [Bool.not_eq_true] at ht
        rw [eraseTemps_cons_nonTemp ht]
        by_cases hyx : y = x
        · subst hyx; simp
        · rw [get_cons_ne hyx, get_cons_ne hyx, ih]

/-- Assigning a non-temporary variable commutes with erasing temporaries. -/
theorem eraseTemps_set {V : VEnv D} {x : Ident} {v : D.Value} (h : isTemp P x = false) :
    eraseTemps P (VEnv.set V x v) = VEnv.set (eraseTemps P V) x v := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyx : y = x
      · subst hyx
        have hy : isTemp P y = false := h
        rw [set_cons_self, eraseTemps_cons_nonTemp hy, eraseTemps_cons_nonTemp hy, set_cons_self]
      · rw [set_cons_ne hyx]
        by_cases ht : isTemp P y = true
        · rw [eraseTemps_cons_temp ht, eraseTemps_cons_temp ht, ih]
        · simp only [Bool.not_eq_true] at ht
          rw [eraseTemps_cons_nonTemp ht, eraseTemps_cons_nonTemp ht, set_cons_ne hyx, ih]

/-! ### "No temporary appears here"

The weakening lemma applies to *original* (pre-ANF) code, which mentions no
temporary. `noTemp*` is that predicate over the syntax — a mutual `Bool`
recursion checking that no variable read, no declared/assigned variable, and no
function parameter/return uses a temporary name. (Function *names* live in a
separate namespace and are not temporaries.) -/

mutual
def noTempExpr (P : String) : Expr Op → Bool
  | .lit _ => true
  | .var x => ! isTemp P x
  | .builtin _ args => noTempArgs P args
  | .call _ args => noTempArgs P args
def noTempArgs (P : String) : List (Expr Op) → Bool
  | [] => true
  | e :: rest => noTempExpr P e && noTempArgs P rest
end

/-- No name in a list is a temporary. -/
def noTempIdents (P : String) : List Ident → Bool
  | [] => true
  | x :: rest => (! isTemp P x) && noTempIdents P rest

mutual
def noTempStmt (P : String) : Stmt Op → Bool
  | .block body | .funDef _ _ _ body => noTempStmts P body
  | .letDecl vars val => noTempIdents P vars && val.all (noTempExpr P)
  | .assign vars val => noTempIdents P vars && noTempExpr P val
  | .cond c body => noTempExpr P c && noTempStmts P body
  | .switch c cases dflt => noTempExpr P c && noTempCases P cases && noTempDflt P dflt
  | .forLoop init c post body =>
      noTempStmts P init && noTempExpr P c && noTempStmts P post && noTempStmts P body
  | .exprStmt e => noTempExpr P e
  | .break | .continue | .leave => true
def noTempStmts (P : String) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => noTempStmt P s && noTempStmts P rest
def noTempCases (P : String) : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, b) :: rest => noTempStmts P b && noTempCases P rest
def noTempDflt (P : String) : Option (List (Stmt Op)) → Bool
  | none => true
  | some b => noTempStmts P b
end

/-! ### Statement-sequence composition

`anfStmts (s :: rest) = anfStmt s ++ anfStmts rest`, so the list-level simulation
composes the executions of consecutive ANF'd statement-lists. These are the
generic `Step` composition bricks for `.stmts` over `++`. -/

/-- Running `l₁` to a *normal* completion then `l₂` equals running `l₁ ++ l₂`. -/
theorem stmts_append_normal [DecidableEq D.Value] :
    ∀ {l₁ : List (Stmt D.Op)} {funs V st Vm stm l₂ V' st' o},
      Step D funs V st (.stmts l₁) (.sres Vm stm .normal) →
      Step D funs Vm stm (.stmts l₂) (.sres V' st' o) →
      Step D funs V st (.stmts (l₁ ++ l₂)) (.sres V' st' o)
  | [], _, _, _, _, _, _, _, _, _, h1, h2 => by cases h1; exact h2
  | _ :: _, _, _, _, _, _, _, _, _, _, h1, h2 => by
      cases h1 with
      | seqCons hs hrest => exact Step.seqCons hs (stmts_append_normal hrest h2)
      | seqStop _ hne => exact absurd rfl hne

/-- Decompose a concatenated `.stmts` execution: either `l₁` stops (non-normal)
and reaches the final result, or `l₁` finishes normally to a midpoint and `l₂`
runs from there. The inverse of `stmts_append_normal`/`stmts_append_stop`. -/
theorem stmts_append_inv [DecidableEq D.Value] {l₂ : List (Stmt D.Op)} :
    ∀ {l₁ : List (Stmt D.Op)} {funs V st V' st' o},
      Step D funs V st (.stmts (l₁ ++ l₂)) (.sres V' st' o) →
      (o ≠ .normal ∧ Step D funs V st (.stmts l₁) (.sres V' st' o)) ∨
      (∃ Vm stm, Step D funs V st (.stmts l₁) (.sres Vm stm .normal) ∧
        Step D funs Vm stm (.stmts l₂) (.sres V' st' o))
  | [], _, _, _, _, _, _, h => Or.inr ⟨_, _, Step.seqNil, h⟩
  | _ :: _, _, _, _, _, _, _, h => by
      cases h with
      | seqCons hs hrest =>
          rcases stmts_append_inv hrest with ⟨hne, hr⟩ | ⟨Vm, stm, h1, h2⟩
          · exact Or.inl ⟨hne, Step.seqCons hs hr⟩
          · exact Or.inr ⟨Vm, stm, Step.seqCons hs h1, h2⟩
      | seqStop hs hne => exact Or.inl ⟨hne, Step.seqStop hs hne⟩

/-- If `l₁` halts / breaks / continues / leaves, `l₁ ++ l₂` stops there (`l₂` is
never reached). -/
theorem stmts_append_stop [DecidableEq D.Value] :
    ∀ {l₁ : List (Stmt D.Op)} {funs V st V' st' o l₂},
      Step D funs V st (.stmts l₁) (.sres V' st' o) → o ≠ .normal →
      Step D funs V st (.stmts (l₁ ++ l₂)) (.sres V' st' o)
  | [], _, _, _, _, _, _, _, h1, ho => by cases h1; exact absurd rfl ho
  | _ :: _, _, _, _, _, _, _, _, h1, ho => by
      cases h1 with
      | seqCons hs hrest => exact Step.seqCons hs (stmts_append_stop hrest ho)
      | seqStop hs hne => exact Step.seqStop hs hne

/-! ### The temp-extension relation — the simulation invariant

`TempExt P Vo Va` means the ANF environment `Va` is the original `Vo` with
temporary bindings *inserted*, the non-temp entries matching pairwise in name and
value and order. This is the structural invariant the `Step` simulation maintains
(stronger than value-agreement, which `restore`'s length-based truncation needs).
-/
inductive TempExt (P : String) : VEnv D → VEnv D → Prop
  | nil : TempExt P [] []
  | temp {Vo Va t w} : isTemp P t = true → TempExt P Vo Va → TempExt P Vo ((t, w) :: Va)
  | keep {Vo Va y v} : isTemp P y = false → TempExt P Vo Va →
      TempExt P ((y, v) :: Vo) ((y, v) :: Va)
  | keepTemp {Vo Va y v} : isTemp P y = true → TempExt P Vo Va →
      TempExt P ((y, v) :: Vo) ((y, v) :: Va)

/-- A temporary name and a non-temporary name are distinct. -/
theorem name_ne_of_isTemp {P : String} {t x : Ident}
    (ht : isTemp P t = true) (hx : isTemp P x = false) : t ≠ x := by
  intro he; subst he; rw [ht] at hx; simp at hx

/-- Reads of a non-temp variable agree across a temp-extension. -/
theorem TempExt.get {P : String} {Vo Va : VEnv D} {x : Ident}
    (hx : isTemp P x = false) (h : TempExt P Vo Va) :
    VEnv.get Va x = VEnv.get Vo x := by
  induction h with
  | nil => rfl
  | temp ht _ ih => rw [get_cons_ne (name_ne_of_isTemp ht hx)]; exact ih
  | keep hy hte ih =>
      rename_i _ _ y v
      by_cases hyx : y = x
      · subst hyx; simp
      · rw [get_cons_ne hyx, get_cons_ne hyx]; exact ih
  | keepTemp hy hte ih =>
      rename_i _ _ y v
      by_cases hyx : y = x
      · subst hyx; simp
      · rw [get_cons_ne hyx, get_cons_ne hyx]; exact ih

/-- Assigning a non-temp variable preserves the temp-extension. -/
theorem TempExt.set {P : String} {Vo Va : VEnv D} {x : Ident} {v : D.Value}
    (hx : isTemp P x = false) (h : TempExt P Vo Va) :
    TempExt P (VEnv.set Vo x v) (VEnv.set Va x v) := by
  induction h with
  | nil => exact .nil
  | temp ht _ ih => rw [set_cons_ne (name_ne_of_isTemp ht hx)]; exact .temp ht ih
  | keep hy hte ih =>
      rename_i _ _ y w
      by_cases hyx : y = x
      · subst hyx; rw [set_cons_self, set_cons_self]; exact .keep hy hte
      · rw [set_cons_ne hyx, set_cons_ne hyx]; exact .keep hy ih
  | keepTemp hy hte ih =>
      rename_i _ _ y w
      by_cases hyx : y = x
      · subst hyx; rw [set_cons_self, set_cons_self]; exact .keepTemp hy hte
      · rw [set_cons_ne hyx, set_cons_ne hyx]; exact .keepTemp hy ih

/-- Any environment temp-extends itself (no temporaries inserted). Unlike
`of_tempFree`, this holds for an *arbitrary* environment — even one that happens
to contain temp-named bindings — which is what the pass-level `EquivStmt` (with
its universally-quantified outer environment) needs. -/
theorem TempExt.refl {P : String} : ∀ (V : VEnv D), TempExt P V V
  | [] => .nil
  | (y, v) :: rest => by
      by_cases hy : isTemp P y = true
      · exact .keepTemp hy (TempExt.refl rest)
      · exact .keep (by simpa using hy) (TempExt.refl rest)

/-- Declaring a fresh temporary in the ANF environment only (invisible to the
original) preserves the extension. -/
theorem TempExt.temp_left {P : String} {Vo Va : VEnv D} {t : Ident} {w : D.Value}
    (ht : isTemp P t = true) (h : TempExt P Vo Va) : TempExt P Vo ((t, w) :: Va) :=
  .temp ht h

/-- Prepending the same block of non-temp declarations to both sides preserves
the extension (used for `let`/`for`-`init` declarations and block entry). -/
theorem TempExt.prepend_nonTemp {P : String} :
    ∀ {new : VEnv D} {Vo Va : VEnv D}, (∀ p ∈ new, isTemp P p.1 = false) →
      TempExt P Vo Va → TempExt P (new ++ Vo) (new ++ Va)
  | [], _, _, _, h => h
  | (y, v) :: rest, _, _, hnew, h => by
      refine .keep (hnew (y, v) (List.mem_cons_self ..)) ?_
      exact TempExt.prepend_nonTemp (fun p hp => hnew p (List.mem_cons_of_mem _ hp)) h

/-- `TempExt` is preserved by folding non-temp assignments. -/
theorem TempExt.foldl_set {P : String} :
    ∀ (l : List (Ident × D.Value)) {Vo Va : VEnv D}, TempExt P Vo Va →
      (∀ p ∈ l, isTemp P p.1 = false) →
      TempExt P (l.foldl (fun acc p => VEnv.set acc p.1 p.2) Vo)
        (l.foldl (fun acc p => VEnv.set acc p.1 p.2) Va)
  | [], _, _, h, _ => h
  | p :: rest, _, _, h, hnt => by
      simp only [List.foldl_cons]
      exact TempExt.foldl_set rest (TempExt.set (hnt p (List.mem_cons_self ..)) h)
        (fun q hq => hnt q (List.mem_cons_of_mem _ hq))

/-- `TempExt` is preserved by a multi-variable assignment to non-temp variables. -/
theorem TempExt.setMany {P : String} {xs : List Ident} {vs : List D.Value}
    {Vo Va : VEnv D} (hnt : ∀ x ∈ xs, isTemp P x = false) (h : TempExt P Vo Va) :
    TempExt P (VEnv.setMany Vo xs vs) (VEnv.setMany Va xs vs) := by
  unfold VEnv.setMany
  refine TempExt.foldl_set _ h ?_
  intro p hp
  obtain ⟨x, v⟩ := p
  exact hnt x (List.of_mem_zip hp).1

/-- A temp-free environment temp-extends itself (the base case at a program's
outermost scope, where no ANF temporary exists yet). -/
theorem TempExt.of_tempFree {P : String} :
    ∀ {V : VEnv D}, (∀ p ∈ V, isTemp P p.1 = false) → TempExt P V V
  | [], _ => .nil
  | (y, v) :: rest, h => by
      refine .keep (h (y, v) (List.mem_cons_self ..)) ?_
      exact TempExt.of_tempFree (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-! ### `restore` under a block-local prefix

`restore outer inner = inner.drop (inner.length - outer.length)`. The block-scoped
ANF design introduces temporaries as a *prefix* of the block-local environment,
so `restore` drops them: the observable post-block environment is exactly what it
would have been without the temporaries. -/

private theorem drop_length_append {α} (pre suf : List α) :
    (pre ++ suf).drop pre.length = suf := by
  induction pre with
  | nil => rfl
  | cons a as ih => simpa using ih

/-- Restoring past a block-local prefix recovers the enclosing environment. -/
theorem restore_prefix (V pre : VEnv D) : restore V (pre ++ V) = V := by
  unfold restore
  rw [List.length_append, Nat.add_sub_cancel]
  exact drop_length_append pre V

/-- `restore V V = V` (an empty block-local layer). -/
@[simp] theorem restore_self (V : VEnv D) : restore V V = V := by
  have := restore_prefix V ([] : VEnv D); simp only [List.nil_append] at this; exact this

end YulEvmCompiler.Optimizer.ANF

/-! ## The persistent-temporary normalizer (transform + form)

`anfNormalize`/`anfBlock` is the persistent-temporary ANF form together with its
structural (form) correctness `anfNormalize_isANF`. Its *semantic* soundness is
not stated here: with atoms kept, the unconditional `∀ b, EquivBlock b (anfBlock b)`
is false (reordering a pure but unbound operand past a halting one turns a stuck
program into a halting one), so no such theorem can hold.

The verified soundness instead lives in `ANFBlockScopedSound`, for the
*block-scoped* normalizer `bsStmts` (`bsStmts_sound_block : EquivBlock b (bsStmts P b)`
for a closed block under a fresh prefix), built on the flatten-correctness lemmas
below (forward/backward, normal/halt). Composing the block-scoped form with a
block-flattening pass recovers this persistent form. -/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-- A program-fresh temporary prefix. A NUL character cannot occur in a Yul
source identifier, so no program identifier starts with it. -/
def anfPrefix (_b : Block Op) : String := String.ofList [Char.ofNat 0] ++ "anf"

/-- The persistent-temporary ANF normalizer: flatten with a program-fresh prefix. -/
def anfNormalize (b : Block Op) : Block Op := anfBlock (anfPrefix b) b

/-- The normalizer's output is in ANF (from the structural proof). -/
theorem anfNormalize_isANF (b : Block Op) : isANFStmts (anfNormalize b) = true :=
  anfBlock_isANF _ b

/-! ### Expression weakening

A temp-free expression evaluates to exactly the same result under a
temp-extended environment: it reads only non-temp variables (`TempExt.get`), and
a `call` runs its callee in a fresh frame independent of the caller's
temporaries, so the callee derivation is reused verbatim (the function
environment `funs` is identical because ANF is the identity on `funDef`). -/
mutual
theorem weakenExpr {funs : FunEnv D} {P : String} {e : Expr Op}
    {Vo Va : VEnv D} {st : EvmState} {r} (hext : TempExt P Vo Va)
    (hnt : noTempExpr P e = true) (h : Step D funs Vo st (.expr e) (.eres r)) :
    Step D funs Va st (.expr e) (.eres r) := by
  cases e with
  | lit l => cases h with | lit => exact Step.lit
  | var x =>
      cases h with
      | var hv =>
          have hx : isTemp P x = false := by simpa [noTempExpr] using hnt
          exact Step.var (by rw [TempExt.get hx hext]; exact hv)
  | builtin op args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      cases h with
      | builtinOk ha hb => exact Step.builtinOk (weakenArgs hext hna ha) hb
      | builtinHalt ha hb => exact Step.builtinHalt (weakenArgs hext hna ha) hb
      | builtinArgsHalt ha => exact Step.builtinArgsHalt (weakenArgs hext hna ha)
  | call fn args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      cases h with
      | callOk ha hlk hlen hbody ho => exact Step.callOk (weakenArgs hext hna ha) hlk hlen hbody ho
      | callHalt ha hlk hlen hbody => exact Step.callHalt (weakenArgs hext hna ha) hlk hlen hbody
      | callArgsHalt ha => exact Step.callArgsHalt (weakenArgs hext hna ha)

theorem weakenArgs {funs : FunEnv D} {P : String} {es : List (Expr Op)}
    {Vo Va : VEnv D} {st : EvmState} {r} (hext : TempExt P Vo Va)
    (hnt : noTempArgs P es = true) (h : Step D funs Vo st (.args es) (.eres r)) :
    Step D funs Va st (.args es) (.eres r) := by
  cases es with
  | nil => cases h with | argsNil => exact Step.argsNil
  | cons e rest =>
      simp only [noTempArgs, Bool.and_eq_true] at hnt
      cases h with
      | argsCons hrest hhead =>
          exact Step.argsCons (weakenArgs hext hnt.2 hrest) (weakenExpr hext hnt.1 hhead)
      | argsRestHalt hrest => exact Step.argsRestHalt (weakenArgs hext hnt.2 hrest)
      | argsHeadHalt hrest hhead =>
          exact Step.argsHeadHalt (weakenArgs hext hnt.2 hrest) (weakenExpr hext hnt.1 hhead)
end

/-- Removing a prepended binding whose name is not a variable-atom of the list
preserves the atoms' evaluation (mirror of `atomArgs_prepend_cons`). -/
theorem atomArgs_remove_cons {funs : FunEnv D} {es : List (Expr Op)}
    {V : VEnv D} {t : Ident} {w : U256} {st r}
    (hatom : atomicArgs es = true) (hne : ∀ x, Expr.var x ∈ es → t ≠ x)
    (h : Step D funs ((t, w) :: V) st (.args es) (.eres r)) :
    Step D funs V st (.args es) (.eres r) := by
  induction es generalizing r with
  | nil => cases h with | argsNil => exact Step.argsNil
  | cons e rest ih =>
      simp only [atomicArgs, Bool.and_eq_true] at hatom
      cases h with
      | argsCons hrest hhead =>
          refine Step.argsCons (ih hatom.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hrest) ?_
          cases e with
          | var y =>
              cases hhead with
              | var hv =>
                  have : t ≠ y := hne y (List.mem_cons_self ..)
                  refine Step.var ?_
                  rw [get_cons_ne this] at hv; exact hv
          | lit l => cases hhead with | lit => exact Step.lit
          | builtin _ _ => simp [isAtom] at hatom
          | call _ _ => simp [isAtom] at hatom
      | argsRestHalt hrest =>
          exact Step.argsRestHalt (ih hatom.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hrest)
      | argsHeadHalt hrest hhead =>
          refine Step.argsHeadHalt
            (ih hatom.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hrest) ?_
          cases e with
          | var y => cases hhead
          | lit l => cases hhead
          | builtin _ _ => simp [isAtom] at hatom
          | call _ _ => simp [isAtom] at hatom

/-! ### Fresh-temp / atom range characterization

A source variable (temp-free) is never a temporary, and a temporary with index
`≥ result` is never one of the flattener's output atoms (its atoms use temp
indices `< result`). Together these give the non-shadowing the `cons` case needs. -/

theorem noTemp_ne_tempName {P : String} {x : Ident} {k : Nat}
    (h : isTemp P x = false) : x ≠ tempName P k := by
  intro he; rw [he, isTemp_tempName] at h; exact absurd h (by simp)

mutual
theorem flatten_atom_fresh {P : String} {k : Nat} {e : Expr Op} (hnt : noTempExpr P e = true) :
    ∀ j, (flatten P k e).1 ≤ j → (flatten P k e).2.2 ≠ Expr.var (tempName P j) := by
  intro j hj
  cases e with
  | var x =>
      simp only [flatten]
      have hx : isTemp P x = false := by simpa [noTempExpr] using hnt
      intro he; injection he with he'; exact noTemp_ne_tempName hx he'
  | lit l => simp [flatten]
  | builtin op args =>
      simp only [flatten] at hj ⊢
      intro he; injection he with he'
      have : (flattenArgs P k args).1 = j := tempName_inj he'
      omega
  | call fn args =>
      simp only [flatten] at hj ⊢
      intro he; injection he with he'
      have : (flattenArgs P k args).1 = j := tempName_inj he'
      omega

theorem flattenArgs_atom_fresh {P : String} {k : Nat} {es : List (Expr Op)}
    (hnt : noTempArgs P es = true) :
    ∀ j, (flattenArgs P k es).1 ≤ j → Expr.var (tempName P j) ∉ (flattenArgs P k es).2.2 := by
  intro j hj
  cases es with
  | nil => simp [flattenArgs]
  | cons e rest =>
      simp only [noTempArgs, Bool.and_eq_true] at hnt
      simp only [flattenArgs] at hj ⊢
      have hk1 : (flattenArgs P k rest).1 ≤ (flatten P (flattenArgs P k rest).1 e).1 :=
        flatten_k_mono P _ e
      intro hmem
      rcases List.mem_cons.mp hmem with heq | htail
      · exact flatten_atom_fresh hnt.1 j hj heq.symm
      · exact flattenArgs_atom_fresh hnt.2 j (by omega) htail
end

/-! ### Atom-list weakening

The flattener's atoms are variables/literals, so a binding whose name is not one
of the atoms' variables can be prepended without changing their evaluation — the
non-shadowing fact the flatten-correctness `cons` case needs (a later flatten's
fresh temporaries don't disturb the already-computed earlier atoms). -/
theorem atomArgs_prepend_cons {funs : FunEnv D} {es : List (Expr Op)}
    {V : VEnv D} {t : Ident} {w : U256} {st r}
    (hatom : atomicArgs es = true) (hne : ∀ x, Expr.var x ∈ es → t ≠ x)
    (h : Step D funs V st (.args es) (.eres r)) :
    Step D funs ((t, w) :: V) st (.args es) (.eres r) := by
  induction es generalizing r with
  | nil => cases h with | argsNil => exact Step.argsNil
  | cons e rest ih =>
      simp only [atomicArgs, Bool.and_eq_true] at hatom
      cases h with
      | argsCons hrest hhead =>
          refine Step.argsCons (ih hatom.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hrest) ?_
          -- head atom e evaluates unchanged under the prepended binding
          cases e with
          | var y =>
              cases hhead with
              | var hv =>
                  have : t ≠ y := hne y (List.mem_cons_self ..)
                  exact Step.var (by rw [get_cons_ne this]; exact hv)
          | lit l => cases hhead with | lit => exact Step.lit
          | builtin _ _ => simp [isAtom] at hatom
          | call _ _ => simp [isAtom] at hatom
      | argsRestHalt hrest =>
          exact Step.argsRestHalt (ih hatom.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hrest)
      | argsHeadHalt hrest hhead =>
          refine Step.argsHeadHalt
            (ih hatom.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hrest) ?_
          cases e with
          | var y =>
              cases hhead
          | lit l => cases hhead
          | builtin _ _ => simp [isAtom] at hatom
          | call _ _ => simp [isAtom] at hatom

/-- Evaluating a list of atoms is state-independent: the same values are produced
at any state (atoms read no state and cause no effects). -/
theorem atomArgs_state_indep {funs : FunEnv D} {es : List (Expr Op)} {V : VEnv D}
    {st : EvmState} {vs} (hatom : atomicArgs es = true)
    (h : Step D funs V st (.args es) (.eres (.vals vs st))) :
    ∀ st2, Step D funs V st2 (.args es) (.eres (.vals vs st2)) := by
  induction es generalizing vs st with
  | nil => intro st2; cases h with | argsNil => exact Step.argsNil
  | cons e rest ih =>
      simp only [atomicArgs, Bool.and_eq_true] at hatom
      intro st2
      cases e with
      | var y =>
          cases h with
          | argsCons hrest hhead =>
              cases hhead with
              | var hv => exact Step.argsCons (ih hatom.2 hrest st2) (Step.var hv)
      | lit l =>
          cases h with
          | argsCons hrest hhead =>
              cases hhead with
              | lit => exact Step.argsCons (ih hatom.2 hrest st2) Step.lit
      | builtin _ _ => simp [isAtom] at hatom
      | call _ _ => simp [isAtom] at hatom

/-- Running a prelude of single-variable `let`s whose bound variables are not
atoms preserves the atoms' evaluation across the resulting environment/state
change. -/
theorem prelude_preserves_atoms {funs : FunEnv D} {atoms : List (Expr Op)}
    (hatom : atomicArgs atoms = true) :
    ∀ (pre : List (Stmt Op)) {V V' : VEnv D} {st st' vs},
      (∀ s ∈ pre, ∃ t rhs, s = .letDecl [t] (some rhs)) →
      (∀ t, (∃ rhs, Stmt.letDecl [t] (some rhs) ∈ pre) → Expr.var t ∉ atoms) →
      Step D funs V st (.stmts pre) (.sres V' st' .normal) →
      Step D funs V st (.args atoms) (.eres (.vals vs st)) →
      Step D funs V' st' (.args atoms) (.eres (.vals vs st'))
  | [] => by intro _ _ hpre hae; cases hpre with | seqNil => exact hae
  | s :: rest => by
      intro hOK hfresh hpre hae
      obtain ⟨t, rhs, rfl⟩ := hOK s (List.mem_cons_self ..)
      have htne : ∀ x, Expr.var x ∈ atoms → t ≠ x :=
        fun x hx he => hfresh t ⟨rhs, List.mem_cons_self ..⟩ (he ▸ hx)
      cases hpre with
      | seqCons hs hrest =>
          cases hs with
          | letVal hval hlen =>
              rename_i stMid vals
              cases vals with
              | nil => simp at hlen
              | cons v tl =>
                  cases tl with
                  | cons _ _ => simp at hlen
                  | nil =>
                      have h1 := atomArgs_prepend_cons (w := v) hatom htne hae
                      have h2 := atomArgs_state_indep hatom h1 stMid
                      exact prelude_preserves_atoms hatom rest
                        (fun s' hs' => hOK s' (List.mem_cons_of_mem _ hs'))
                        (fun t' ht' => hfresh t' (ht'.imp fun r hr => List.mem_cons_of_mem _ hr))
                        hrest h2
      | seqStop hs hne => exact absurd rfl hne

/-! Every variable declared by a flatten prelude is a temporary with index ≥ the
input counter. -/
mutual
theorem flatten_prelude_decl {P : String} {k : Nat} {e : Expr Op} :
    ∀ t, (∃ rhs, Stmt.letDecl [t] (some rhs) ∈ (flatten P k e).2.1) →
      ∃ m, k ≤ m ∧ t = tempName P m := by
  intro t ht
  cases e with
  | var _ => obtain ⟨rhs, hm⟩ := ht; simp [flatten] at hm
  | lit _ => obtain ⟨rhs, hm⟩ := ht; simp [flatten] at hm
  | builtin op args =>
      obtain ⟨rhs, hm⟩ := ht
      simp only [flatten, List.mem_append, List.mem_singleton] at hm
      rcases hm with hpre | hlast
      · exact flattenArgs_prelude_decl t ⟨rhs, hpre⟩
      · injection hlast with h1 h2; injection h1 with h3
        exact ⟨(flattenArgs P k args).1, flattenArgs_k_mono P k args, h3⟩
  | call fn args =>
      obtain ⟨rhs, hm⟩ := ht
      simp only [flatten, List.mem_append, List.mem_singleton] at hm
      rcases hm with hpre | hlast
      · exact flattenArgs_prelude_decl t ⟨rhs, hpre⟩
      · injection hlast with h1 h2; injection h1 with h3
        exact ⟨(flattenArgs P k args).1, flattenArgs_k_mono P k args, h3⟩

theorem flattenArgs_prelude_decl {P : String} {k : Nat} {es : List (Expr Op)} :
    ∀ t, (∃ rhs, Stmt.letDecl [t] (some rhs) ∈ (flattenArgs P k es).2.1) →
      ∃ m, k ≤ m ∧ t = tempName P m := by
  intro t ht
  cases es with
  | nil => obtain ⟨rhs, hm⟩ := ht; simp [flattenArgs] at hm
  | cons e rest =>
      obtain ⟨rhs, hm⟩ := ht
      simp only [flattenArgs, List.mem_append] at hm
      rcases hm with hpre | hhead
      · exact flattenArgs_prelude_decl t ⟨rhs, hpre⟩
      · obtain ⟨m, hm1, hm2⟩ := flatten_prelude_decl t ⟨rhs, hhead⟩
        exact ⟨m, le_trans (flattenArgs_k_mono P k rest) hm1, hm2⟩
end

/-- Inversion for a call expression that yields values (stated with a *variable*
result list so `cases` can unify — `callOk`'s result `decl.rets.map …` is not a
variable). -/
theorem expr_call_inv {funs : FunEnv D} {V : VEnv D} {st fn args rr st1}
    (h : Step D funs V st (.expr (.call fn args)) (.eres (.vals rr st1))) :
    ∃ argvals sta decl cenv Vend o,
      Step D funs V st (.args args) (.eres (.vals argvals sta)) ∧
      lookupFun funs fn = some (decl, cenv) ∧
      argvals.length = decl.params.length ∧
      Step D cenv ((decl.params.zip argvals) ++ bindZeros D decl.rets) sta
        (.stmt (.block decl.body)) (.sres Vend st1 o) ∧
      (o = .normal ∨ o = .leave) ∧
      rr = decl.rets.map (fun r => (VEnv.get Vend r).getD (Dialect.zero D)) := by
  cases h with
  | callOk h1 h2 h3 h4 h5 => exact ⟨_, _, _, _, _, _, h1, h2, h3, h4, h5, rfl⟩

/-- Reverse of `prelude_preserves_atoms`: atoms evaluating after the prelude
implies they evaluate (to the same values) before it. -/
theorem prelude_preserves_atoms_bwd {funs : FunEnv D} {atoms : List (Expr Op)}
    (hatom : atomicArgs atoms = true) :
    ∀ (pre : List (Stmt Op)) {V V' : VEnv D} {st st' vs},
      (∀ s ∈ pre, ∃ t rhs, s = .letDecl [t] (some rhs)) →
      (∀ t, (∃ rhs, Stmt.letDecl [t] (some rhs) ∈ pre) → Expr.var t ∉ atoms) →
      Step D funs V st (.stmts pre) (.sres V' st' .normal) →
      Step D funs V' st' (.args atoms) (.eres (.vals vs st')) →
      Step D funs V st (.args atoms) (.eres (.vals vs st))
  | [], _, _, _, _, _, _, _, hpre, hae => by cases hpre with | seqNil => exact hae
  | s :: rest, _, _, st, _, _, hOK, hfresh, hpre, hae => by
      obtain ⟨t, rhs, rfl⟩ := hOK s (List.mem_cons_self ..)
      have htne : ∀ x, Expr.var x ∈ atoms → t ≠ x :=
        fun x hx he => hfresh t ⟨rhs, List.mem_cons_self ..⟩ (he ▸ hx)
      cases hpre with
      | seqCons hs hrest =>
          cases hs with
          | letVal hval hlen =>
              rename_i stMid vals
              cases vals with
              | nil => simp at hlen
              | cons v tl =>
                  cases tl with
                  | cons _ _ => simp at hlen
                  | nil =>
                      have h1 := prelude_preserves_atoms_bwd hatom rest
                        (fun s' hs' => hOK s' (List.mem_cons_of_mem _ hs'))
                        (fun t' ht' => hfresh t' (ht'.imp fun r hr => List.mem_cons_of_mem _ hr))
                        hrest hae
                      exact atomArgs_state_indep hatom (atomArgs_remove_cons hatom htne h1) st
      | seqStop hs hne => exact absurd rfl hne

/-! ### Flatten-correctness

Running a `flatten`/`flattenArgs` prelude from a temp-extended environment binds
the temporaries so that the resulting atom(s) evaluate to the same value(s) as
the original expression, leaving `TempExt` intact and ending at the same state. -/
mutual
theorem flatten_correct {funs : FunEnv D} {P : String} {e : Expr Op}
    {Vo Va : VEnv D} {st : EvmState} {v st1} (k : Nat)
    (hstep : Step D funs Vo st (.expr e) (.eres (.vals [v] st1)))
    (hnt : noTempExpr P e = true) (hext : TempExt P Vo Va) :
    ∃ Va', Step D funs Va st (.stmts (flatten P k e).2.1) (.sres Va' st1 .normal)
      ∧ TempExt P Vo Va'
      ∧ Step D funs Va' st1 (.expr (flatten P k e).2.2) (.eres (.vals [v] st1)) := by
  cases e with
  | var x =>
      cases hstep with
      | var hv =>
          refine ⟨Va, ?_, hext, ?_⟩
          · simp only [flatten]; exact Step.seqNil
          · simp only [flatten]
            exact weakenExpr hext hnt (Step.var hv)
  | lit l =>
      cases hstep with
      | lit =>
          refine ⟨Va, ?_, hext, ?_⟩
          · simp only [flatten]; exact Step.seqNil
          · simp only [flatten]; exact Step.lit
  | builtin op args =>
      cases hstep with
      | builtinOk hargs hb =>
          obtain ⟨Va_a, hpre, hext_a, hatoms⟩ :=
            flattenArgs_correct k hargs (by simpa [noTempExpr] using hnt) hext
          simp only [flatten]
          refine ⟨(tempName P (flattenArgs P k args).1, v) :: Va_a, ?_, ?_, ?_⟩
          · exact stmts_append_normal hpre
              (Step.seqCons (Step.letVal (Step.builtinOk hatoms hb) rfl) Step.seqNil)
          · exact TempExt.temp (isTemp_tempName P _) hext_a
          · exact Step.var get_cons_self
  | call fn args =>
      obtain ⟨argvals, sta, decl, cenv, Vend, o, hargs, hlk, hlen, hbody, ho, hmap⟩ :=
        expr_call_inv hstep
      obtain ⟨Va_a, hpre, hext_a, hatoms⟩ :=
        flattenArgs_correct k hargs (by simpa [noTempExpr] using hnt) hext
      have hcall : Step D funs Va_a sta
          (.expr (.call fn (flattenArgs P k args).2.2)) (.eres (.vals [v] st1)) := by
        rw [hmap]; exact Step.callOk hatoms hlk hlen hbody ho
      simp only [flatten]
      refine ⟨(tempName P (flattenArgs P k args).1, v) :: Va_a, ?_, ?_, ?_⟩
      · exact stmts_append_normal hpre
          (Step.seqCons (Step.letVal hcall rfl) Step.seqNil)
      · exact TempExt.temp (isTemp_tempName P _) hext_a
      · exact Step.var get_cons_self

theorem flattenArgs_correct {funs : FunEnv D} {P : String} {es : List (Expr Op)}
    {Vo Va : VEnv D} {st : EvmState} {argvals st1} (k : Nat)
    (hstep : Step D funs Vo st (.args es) (.eres (.vals argvals st1)))
    (hnt : noTempArgs P es = true) (hext : TempExt P Vo Va) :
    ∃ Va', Step D funs Va st (.stmts (flattenArgs P k es).2.1) (.sres Va' st1 .normal)
      ∧ TempExt P Vo Va'
      ∧ Step D funs Va' st1 (.args (flattenArgs P k es).2.2) (.eres (.vals argvals st1)) := by
  cases es with
  | nil =>
      cases hstep with
      | argsNil =>
          refine ⟨Va, ?_, hext, ?_⟩
          · simp only [flattenArgs]; exact Step.seqNil
          · simp only [flattenArgs]; exact Step.argsNil
  | cons e rest =>
      cases hstep with
      | argsCons hrest hhead =>
          simp only [noTempArgs, Bool.and_eq_true] at hnt
          obtain ⟨Va_r, hpreR, hextR, hatomsR⟩ := flattenArgs_correct k hrest hnt.2 hext
          obtain ⟨Va_h, hpreH, hextH, hatomH⟩ :=
            flatten_correct (flattenArgs P k rest).1 hhead hnt.1 hextR
          simp only [flattenArgs]
          refine ⟨Va_h, stmts_append_normal hpreR hpreH, hextH, Step.argsCons ?_ hatomH⟩
          refine prelude_preserves_atoms (flattenArgs_ok P k rest).1
            (flatten P (flattenArgs P k rest).1 e).2.1 ?_ ?_ hpreH hatomsR
          · exact fun s hs => preludeOK_shape ((flatten_ok P (flattenArgs P k rest).1 e).2 s hs)
          · intro t ht
            obtain ⟨rhs, hmem⟩ := ht
            obtain ⟨m, hm1, rfl⟩ := flatten_prelude_decl t ⟨rhs, hmem⟩
            exact flattenArgs_atom_fresh hnt.2 m hm1
end

/-- Head-expression flattening correctness: run the prelude (to some
intermediate state), then the flat right-hand side evaluates to the same values.
Unlike `flatten_correct`, the top operator is kept (no final temp), so the
result may be multi-valued and the prelude ends at the arguments' state. -/
theorem flattenTop_correct {funs : FunEnv D} {P : String} {e : Expr Op}
    {Vo Va : VEnv D} {st : EvmState} {vs st1} (k : Nat)
    (hstep : Step D funs Vo st (.expr e) (.eres (.vals vs st1)))
    (hnt : noTempExpr P e = true) (hext : TempExt P Vo Va) :
    ∃ Va' stMid, Step D funs Va st (.stmts (flattenTop P k e).2.1) (.sres Va' stMid .normal)
      ∧ TempExt P Vo Va'
      ∧ Step D funs Va' stMid (.expr (flattenTop P k e).2.2) (.eres (.vals vs st1)) := by
  cases e with
  | var x =>
      refine ⟨Va, st, ?_, hext, ?_⟩
      · simp only [flattenTop]; exact Step.seqNil
      · simpa only [flattenTop] using weakenExpr hext hnt hstep
  | lit l =>
      refine ⟨Va, st, ?_, hext, ?_⟩
      · simp only [flattenTop]; exact Step.seqNil
      · simpa only [flattenTop] using weakenExpr hext hnt hstep
  | builtin op args =>
      cases hstep with
      | builtinOk hargs hb =>
          obtain ⟨Va_a, hpre, hext_a, hatoms⟩ :=
            flattenArgs_correct k hargs (by simpa [noTempExpr] using hnt) hext
          simp only [flattenTop]
          exact ⟨Va_a, _, hpre, hext_a, Step.builtinOk hatoms hb⟩
  | call fn args =>
      obtain ⟨argvals, sta, decl, cenv, Vend, o, hargs, hlk, hlen, hbody, ho, hmap⟩ :=
        expr_call_inv hstep
      obtain ⟨Va_a, hpre, hext_a, hatoms⟩ :=
        flattenArgs_correct k hargs (by simpa [noTempExpr] using hnt) hext
      have hcall : Step D funs Va_a sta
          (.expr (.call fn (flattenArgs P k args).2.2)) (.eres (.vals vs st1)) := by
        rw [hmap]; exact Step.callOk hatoms hlk hlen hbody ho
      simp only [flattenTop]
      exact ⟨Va_a, _, hpre, hext_a, hcall⟩

/-- Evaluating a list of atoms leaves the state unchanged. -/
theorem atomArgs_end_eq {funs : FunEnv D} {es : List (Expr Op)} {V : VEnv D}
    {st st' : EvmState} {vs} (hatom : atomicArgs es = true)
    (h : Step D funs V st (.args es) (.eres (.vals vs st'))) : st' = st := by
  induction es generalizing vs st st' with
  | nil => cases h with | argsNil => rfl
  | cons e rest ih =>
      simp only [atomicArgs, Bool.and_eq_true] at hatom
      cases h with
      | argsCons hrest hhead =>
          have h1 := ih hatom.2 hrest
          cases e with
          | var y => cases hhead with | var _ => exact h1
          | lit l => cases hhead with | lit => exact h1
          | builtin _ _ => simp [isAtom] at hatom
          | call _ _ => simp [isAtom] at hatom

/-! ### Flatten-correctness, reverse direction

The mirror of `flatten_correct`/`flattenArgs_correct`: from an execution of the
flatten prelude (normal) plus the resulting atom(s), recover the *original*
expression's evaluation. Needed for the backward half of the per-statement
`EquivStmt`. (Only the normal case is needed: if any internal builtin/call
halted, the prelude itself would halt, contradicting the normal hypothesis.) -/
mutual
theorem flatten_correct_bwd {funs : FunEnv D} {P : String} {e : Expr Op}
    {Vo Va : VEnv D} {st : EvmState} (k : Nat)
    (hnt : noTempExpr P e = true) (hext : TempExt P Vo Va)
    {Va' stM stA v}
    (hpre : Step D funs Va st (.stmts (flatten P k e).2.1) (.sres Va' stM .normal))
    (hat : Step D funs Va' stM (.expr (flatten P k e).2.2) (.eres (.vals [v] stA))) :
    Step D funs Vo st (.expr e) (.eres (.vals [v] stA)) ∧ TempExt P Vo Va' := by
  cases e with
  | var x =>
      simp only [flatten] at hpre hat
      cases hpre with
      | seqNil =>
          cases hat with
          | var hv =>
              have hx : isTemp P x = false := by simpa [noTempExpr] using hnt
              exact ⟨Step.var (by rw [TempExt.get hx hext] at hv; exact hv), hext⟩
  | lit l =>
      simp only [flatten] at hpre hat
      cases hpre with
      | seqNil => cases hat with | lit => exact ⟨Step.lit, hext⟩
  | builtin op args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      simp only [flatten] at hpre hat
      rcases stmts_append_inv hpre with ⟨hne, _⟩ | ⟨Vm, stm, hpreA, htail⟩
      · exact absurd rfl hne
      · cases htail with
        | seqStop _ hne => exact absurd rfl hne
        | seqCons hlet hnil =>
            cases hnil with
            | seqNil =>
                cases hlet with
                | letVal hbe hlen =>
                    rename_i bvals
                    obtain ⟨bv, rfl⟩ : ∃ bv, bvals = [bv] := by
                      cases bvals with
                      | nil => simp at hlen
                      | cons b tl => cases tl with
                        | nil => exact ⟨b, rfl⟩
                        | cons _ _ => simp at hlen
                    cases hbe with
                    | builtinOk hatoms hb =>
                        obtain ⟨hargs, hextm⟩ :=
                          flattenArgs_correct_bwd k hna hext hpreA hatoms
                        cases hat with
                        | var hv =>
                            have h2 : VEnv.get ([tempName P (flattenArgs P k args).1].zip [bv] ++ Vm)
                                (tempName P (flattenArgs P k args).1) = some bv := get_cons_self
                            obtain rfl : v = bv := Option.some.inj (hv.symm.trans h2)
                            exact ⟨Step.builtinOk hargs hb, TempExt.temp (isTemp_tempName P _) hextm⟩
  | call fn args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      simp only [flatten] at hpre hat
      rcases stmts_append_inv hpre with ⟨hne, _⟩ | ⟨Vm, stm, hpreA, htail⟩
      · exact absurd rfl hne
      · cases htail with
        | seqStop _ hne => exact absurd rfl hne
        | seqCons hlet hnil =>
            cases hnil with
            | seqNil =>
                cases hlet with
                | letVal hce hlen =>
                    rename_i bvals
                    obtain ⟨bv, rfl⟩ : ∃ bv, bvals = [bv] := by
                      cases bvals with
                      | nil => simp at hlen
                      | cons b tl => cases tl with
                        | nil => exact ⟨b, rfl⟩
                        | cons _ _ => simp at hlen
                    obtain ⟨argvals, sta, decl, cenv, Vend, o, hatoms, hlk, hlen2, hbody, ho, hmap⟩ :=
                      expr_call_inv hce
                    obtain ⟨hargs, hextm⟩ :=
                      flattenArgs_correct_bwd k hna hext hpreA hatoms
                    cases hat with
                    | var hv =>
                        have h2 : VEnv.get ([tempName P (flattenArgs P k args).1].zip [bv] ++ Vm)
                            (tempName P (flattenArgs P k args).1) = some bv := get_cons_self
                        obtain rfl : v = bv := Option.some.inj (hv.symm.trans h2)
                        refine ⟨?_, TempExt.temp (isTemp_tempName P _) hextm⟩
                        rw [hmap]; exact Step.callOk hargs hlk hlen2 hbody ho

theorem flattenArgs_correct_bwd {funs : FunEnv D} {P : String} {es : List (Expr Op)}
    {Vo Va : VEnv D} {st : EvmState} (k : Nat)
    (hnt : noTempArgs P es = true) (hext : TempExt P Vo Va)
    {Va' stM stA argvals}
    (hpre : Step D funs Va st (.stmts (flattenArgs P k es).2.1) (.sres Va' stM .normal))
    (hat : Step D funs Va' stM (.args (flattenArgs P k es).2.2) (.eres (.vals argvals stA))) :
    Step D funs Vo st (.args es) (.eres (.vals argvals stA)) ∧ TempExt P Vo Va' := by
  cases es with
  | nil =>
      simp only [flattenArgs] at hpre hat
      cases hpre with
      | seqNil => cases hat with | argsNil => exact ⟨Step.argsNil, hext⟩
  | cons e rest =>
      simp only [noTempArgs, Bool.and_eq_true] at hnt
      simp only [flattenArgs] at hpre hat
      -- prelude = preRest ++ preHead
      rcases stmts_append_inv hpre with ⟨hne, _⟩ | ⟨Vr, str, hpreR, hpreH⟩
      · exact absurd rfl hne
      · -- atoms = atomHead :: atomsRest, evaluated at Va' stM
        cases hat with
        | argsCons hrestAt hheadAt =>
            rename_i rvals rst hv
            -- atomsRest are atomic; their eval ends where it starts
            have hatomsR_ok : atomicArgs (flattenArgs P k rest).2.2 = true := (flattenArgs_ok P k rest).1
            have hrst : rst = stM := atomArgs_end_eq hatomsR_ok hrestAt
            subst hrst
            -- move atomsRest evaluation back across preHead (freshness)
            have hback : Step D funs Vr str (.args (flattenArgs P k rest).2.2)
                (.eres (.vals rvals str)) := by
              refine prelude_preserves_atoms_bwd hatomsR_ok
                (flatten P (flattenArgs P k rest).1 e).2.1 ?_ ?_ hpreH hrestAt
              · exact fun s hs => preludeOK_shape ((flatten_ok P (flattenArgs P k rest).1 e).2 s hs)
              · intro t ht
                obtain ⟨rhs, hmem⟩ := ht
                obtain ⟨m, hm1, rfl⟩ := flatten_prelude_decl t ⟨rhs, hmem⟩
                exact flattenArgs_atom_fresh hnt.2 m hm1
            obtain ⟨hargsR, hextR⟩ := flattenArgs_correct_bwd k hnt.2 hext hpreR hback
            obtain ⟨hheadE, hextH⟩ := flatten_correct_bwd (flattenArgs P k rest).1 hnt.1 hextR hpreH hheadAt
            exact ⟨Step.argsCons hargsR hheadE, hextH⟩
end

/-- Reverse of `flattenTop_correct` (normal case): from the head-flattening
prelude (normal) plus the resulting flat expression, recover the original
expression's evaluation. The top operator is kept, so the flat expression may be
multi-valued. Unconditional (boundedness is witnessed by the flat expr's
evaluation of its atoms). -/
theorem flattenTop_correct_bwd {funs : FunEnv D} {P : String} {e : Expr Op}
    {Vo Va : VEnv D} {st : EvmState} (k : Nat)
    (hnt : noTempExpr P e = true) (hext : TempExt P Vo Va)
    {Va' stM stA vs}
    (hpre : Step D funs Va st (.stmts (flattenTop P k e).2.1) (.sres Va' stM .normal))
    (hat : Step D funs Va' stM (.expr (flattenTop P k e).2.2) (.eres (.vals vs stA))) :
    Step D funs Vo st (.expr e) (.eres (.vals vs stA)) ∧ TempExt P Vo Va' := by
  cases e with
  | var x =>
      simp only [flattenTop] at hpre hat
      cases hpre with
      | seqNil =>
          cases hat with
          | var hv =>
              have hx : isTemp P x = false := by simpa [noTempExpr] using hnt
              exact ⟨Step.var (by rw [TempExt.get hx hext] at hv; exact hv), hext⟩
  | lit l =>
      simp only [flattenTop] at hpre hat
      cases hpre with
      | seqNil => cases hat with | lit => exact ⟨Step.lit, hext⟩
  | builtin op args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      simp only [flattenTop] at hpre hat
      cases hat with
      | builtinOk hatoms hb =>
          obtain ⟨hargs, hextm⟩ := flattenArgs_correct_bwd k hna hext hpre hatoms
          exact ⟨Step.builtinOk hargs hb, hextm⟩
  | call fn args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      simp only [flattenTop] at hpre hat
      obtain ⟨argvals, sta, decl, cenv, Vend, o, hatoms, hlk, hlen, hbody, ho, hmap⟩ :=
        expr_call_inv hat
      obtain ⟨hargs, hextm⟩ := flattenArgs_correct_bwd k hna hext hpre hatoms
      exact ⟨by rw [hmap]; exact Step.callOk hargs hlk hlen hbody ho, hextm⟩

/-! ### Flatten-correctness, halt (forward)

If the original expression/args halt, the flatten prelude halts at the same
state. Unconditional; reuses the normal forward correctness for the
already-evaluated prefix and `stmts_append_stop`/`_normal` for propagation. -/
mutual
theorem flatten_halt {funs : FunEnv D} {P : String} {e : Expr Op}
    {Vo Va : VEnv D} {st sth : EvmState} (k : Nat)
    (hstep : Step D funs Vo st (.expr e) (.eres (.halt sth)))
    (hnt : noTempExpr P e = true) (hext : TempExt P Vo Va) :
    ∃ Va', Step D funs Va st (.stmts (flatten P k e).2.1) (.sres Va' sth .halt) := by
  cases e with
  | var x => cases hstep
  | lit l => cases hstep
  | builtin op args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      simp only [flatten]
      cases hstep with
      | builtinArgsHalt hah =>
          obtain ⟨Va', hpre⟩ := flattenArgs_halt k hah hna hext
          exact ⟨Va', stmts_append_stop hpre (by simp)⟩
      | builtinHalt hargs hb =>
          obtain ⟨Va_a, hpre, _, hatoms⟩ := flattenArgs_correct k hargs hna hext
          exact ⟨Va_a, stmts_append_normal hpre
            (Step.seqStop (Step.letHalt (Step.builtinHalt hatoms hb)) (by simp))⟩
  | call fn args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      simp only [flatten]
      cases hstep with
      | callArgsHalt hah =>
          obtain ⟨Va', hpre⟩ := flattenArgs_halt k hah hna hext
          exact ⟨Va', stmts_append_stop hpre (by simp)⟩
      | callHalt hargs hlk hlen hbody =>
          obtain ⟨Va_a, hpre, _, hatoms⟩ := flattenArgs_correct k hargs hna hext
          exact ⟨Va_a, stmts_append_normal hpre
            (Step.seqStop (Step.letHalt (Step.callHalt hatoms hlk hlen hbody)) (by simp))⟩

theorem flattenArgs_halt {funs : FunEnv D} {P : String} {es : List (Expr Op)}
    {Vo Va : VEnv D} {st sth : EvmState} (k : Nat)
    (hstep : Step D funs Vo st (.args es) (.eres (.halt sth)))
    (hnt : noTempArgs P es = true) (hext : TempExt P Vo Va) :
    ∃ Va', Step D funs Va st (.stmts (flattenArgs P k es).2.1) (.sres Va' sth .halt) := by
  cases es with
  | nil => cases hstep
  | cons e rest =>
      simp only [noTempArgs, Bool.and_eq_true] at hnt
      simp only [flattenArgs]
      cases hstep with
      | argsRestHalt hrh =>
          obtain ⟨Va', hpre⟩ := flattenArgs_halt k hrh hnt.2 hext
          exact ⟨Va', stmts_append_stop hpre (by simp)⟩
      | argsHeadHalt hrest hhead =>
          obtain ⟨Vr, hpreR, hextR, _⟩ := flattenArgs_correct k hrest hnt.2 hext
          obtain ⟨Vh, hpreH⟩ := flatten_halt (flattenArgs P k rest).1 hhead hnt.1 hextR
          exact ⟨Vh, stmts_append_normal hpreR hpreH⟩
end

/-- Head-flattening, halt (forward): if the original halts, either the
head-flattening prelude halts, or it completes and the resulting flat expression
halts. Serves the block-scoped statement's halt case. -/
theorem flattenTop_halt {funs : FunEnv D} {P : String} {e : Expr Op}
    {Vo Va : VEnv D} {st sth : EvmState} (k : Nat)
    (hstep : Step D funs Vo st (.expr e) (.eres (.halt sth)))
    (hnt : noTempExpr P e = true) (hext : TempExt P Vo Va) :
    (∃ Va', Step D funs Va st (.stmts (flattenTop P k e).2.1) (.sres Va' sth .halt)) ∨
    (∃ Va' stMid, Step D funs Va st (.stmts (flattenTop P k e).2.1) (.sres Va' stMid .normal) ∧
      Step D funs Va' stMid (.expr (flattenTop P k e).2.2) (.eres (.halt sth)) ∧
      TempExt P Vo Va') := by
  cases e with
  | var x => cases hstep
  | lit l => cases hstep
  | builtin op args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      simp only [flattenTop]
      cases hstep with
      | builtinArgsHalt hah =>
          obtain ⟨Va', hpre⟩ := flattenArgs_halt k hah hna hext
          exact Or.inl ⟨Va', hpre⟩
      | builtinHalt hargs hb =>
          obtain ⟨Va_a, hpre, hext_a, hatoms⟩ := flattenArgs_correct k hargs hna hext
          exact Or.inr ⟨Va_a, _, hpre, Step.builtinHalt hatoms hb, hext_a⟩
  | call fn args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      simp only [flattenTop]
      cases hstep with
      | callArgsHalt hah =>
          obtain ⟨Va', hpre⟩ := flattenArgs_halt k hah hna hext
          exact Or.inl ⟨Va', hpre⟩
      | callHalt hargs hlk hlen hbody =>
          obtain ⟨Va_a, hpre, hext_a, hatoms⟩ := flattenArgs_correct k hargs hna hext
          exact Or.inr ⟨Va_a, _, hpre, Step.callHalt hatoms hlk hlen hbody, hext_a⟩

/-! ### Atoms are evaluable after a normal prelude (progress under scoping)

After the flatten prelude runs normally, the resulting atoms all evaluate: each
is either a source variable (bound by well-scopedness, carried across the
prelude which only prepends) or a fresh temporary (bound by the very `let` that
introduced it). This is the progress fact the reordering-halt backward direction
needs, and it is the *only* place scoping enters. -/
theorem flatten_atom_eval {funs : FunEnv D} {P : String} {e : Expr Op}
    {Va : VEnv D} {st : EvmState} (k : Nat)
    (hsc : ∀ x, x ∈ freeVarsExpr e → (VEnv.get Va x).isSome = true)
    {Va' stM} (hpre : Step D funs Va st (.stmts (flatten P k e).2.1) (.sres Va' stM .normal)) :
    ∃ v, Step D funs Va' stM (.expr (flatten P k e).2.2) (.eres (.vals [v] stM)) := by
  cases e with
  | var x =>
      simp only [flatten] at hpre ⊢
      cases hpre with
      | seqNil =>
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hsc x (by simp [freeVarsExpr]))
          exact ⟨v, Step.var hv⟩
  | lit l =>
      simp only [flatten] at hpre ⊢
      cases hpre with | seqNil => exact ⟨_, Step.lit⟩
  | builtin op args =>
      simp only [flatten] at hpre ⊢
      rcases stmts_append_inv hpre with ⟨hne, _⟩ | ⟨Vm, stm, hpreA, htail⟩
      · exact absurd rfl hne
      · cases htail with
        | seqStop _ hne => exact absurd rfl hne
        | seqCons hlet hnil =>
            cases hnil with
            | seqNil =>
                cases hlet with
                | letVal hbe hlen =>
                    rename_i vals
                    obtain ⟨bv, rfl⟩ : ∃ bv, vals = [bv] := by
                      cases vals with
                      | nil => simp at hlen
                      | cons b tl => cases tl with
                        | nil => exact ⟨b, rfl⟩
                        | cons _ _ => simp at hlen
                    exact ⟨bv, Step.var get_cons_self⟩
  | call fn args =>
      simp only [flatten] at hpre ⊢
      rcases stmts_append_inv hpre with ⟨hne, _⟩ | ⟨Vm, stm, hpreA, htail⟩
      · exact absurd rfl hne
      · cases htail with
        | seqStop _ hne => exact absurd rfl hne
        | seqCons hlet hnil =>
            cases hnil with
            | seqNil =>
                cases hlet with
                | letVal hbe hlen =>
                    rename_i vals
                    obtain ⟨bv, rfl⟩ : ∃ bv, vals = [bv] := by
                      cases vals with
                      | nil => simp at hlen
                      | cons b tl => cases tl with
                        | nil => exact ⟨b, rfl⟩
                        | cons _ _ => simp at hlen
                    exact ⟨bv, Step.var get_cons_self⟩

theorem flattenArgs_atoms_eval {funs : FunEnv D} {P : String} {es : List (Expr Op)}
    {Va : VEnv D} {st : EvmState} (k : Nat) (hnt : noTempArgs P es = true)
    (hsc : ∀ x, x ∈ freeVarsArgs es → (VEnv.get Va x).isSome = true)
    {Va' stM} (hpre : Step D funs Va st (.stmts (flattenArgs P k es).2.1) (.sres Va' stM .normal)) :
    ∃ vs, Step D funs Va' stM (.args (flattenArgs P k es).2.2) (.eres (.vals vs stM)) := by
  cases es with
  | nil =>
      simp only [flattenArgs] at hpre ⊢
      cases hpre with | seqNil => exact ⟨[], Step.argsNil⟩
  | cons e rest =>
      simp only [noTempArgs, Bool.and_eq_true] at hnt
      simp only [flattenArgs] at hpre ⊢
      rcases stmts_append_inv hpre with ⟨hne, _⟩ | ⟨Vr, str, hpreR, hpreH⟩
      · exact absurd rfl hne
      · obtain ⟨rvs, hrestAt⟩ := flattenArgs_atoms_eval k hnt.2
          (fun x hx => hsc x (by simp only [freeVarsArgs_cons, List.mem_append]; exact Or.inr hx))
          hpreR
        have hatomsR_ok : atomicArgs (flattenArgs P k rest).2.2 = true := (flattenArgs_ok P k rest).1
        have hmove : Step D funs Va' stM (.args (flattenArgs P k rest).2.2)
            (.eres (.vals rvs stM)) := by
          refine prelude_preserves_atoms hatomsR_ok
            (flatten P (flattenArgs P k rest).1 e).2.1 ?_ ?_ hpreH hrestAt
          · exact fun s hs => preludeOK_shape ((flatten_ok P (flattenArgs P k rest).1 e).2 s hs)
          · intro t ht
            obtain ⟨rhs, hmem⟩ := ht
            obtain ⟨m, hm1, rfl⟩ := flatten_prelude_decl t ⟨rhs, hmem⟩
            exact flattenArgs_atom_fresh hnt.2 m hm1
        have hscHead : ∀ x, x ∈ freeVarsExpr e → (VEnv.get Vr x).isSome = true := by
          obtain ⟨ext, rfl⟩ := letPrelude_prefix (flattenArgs P k rest).2.1
            (fun s hs => preludeOK_shape ((flattenArgs_ok P k rest).2 s hs)) hpreR
          intro x hx
          exact get_append_isSome ext
            (hsc x (by simp only [freeVarsArgs_cons, List.mem_append]; exact Or.inl hx))
        obtain ⟨hv, hheadAt⟩ := flatten_atom_eval (flattenArgs P k rest).1 hscHead hpreH
        exact ⟨hv :: rvs, Step.argsCons hmove hheadAt⟩

/-! Free variables of a temp-free expression are non-temporary. -/
mutual
theorem freeVarsExpr_noTemp {P : String} {e : Expr Op} (h : noTempExpr P e = true) :
    ∀ x, x ∈ freeVarsExpr e → isTemp P x = false := by
  intro x hx
  cases e with
  | var y => simp only [freeVarsExpr, List.mem_singleton] at hx; subst hx; simpa [noTempExpr] using h
  | lit l => simp [freeVarsExpr] at hx
  | builtin op args =>
      exact freeVarsArgs_noTemp (by simpa [noTempExpr] using h) x (by simpa [freeVarsExpr] using hx)
  | call fn args =>
      exact freeVarsArgs_noTemp (by simpa [noTempExpr] using h) x (by simpa [freeVarsExpr] using hx)
theorem freeVarsArgs_noTemp {P : String} {es : List (Expr Op)} (h : noTempArgs P es = true) :
    ∀ x, x ∈ freeVarsArgs es → isTemp P x = false := by
  intro x hx
  cases es with
  | nil => simp [freeVarsArgs] at hx
  | cons e rest =>
      simp only [noTempArgs, Bool.and_eq_true] at h
      simp only [freeVarsArgs_cons, List.mem_append] at hx
      rcases hx with h1 | h2
      · exact freeVarsExpr_noTemp h.1 x h1
      · exact freeVarsArgs_noTemp h.2 x h2
end

/-! ### Flatten-correctness, halt (backward, under scoping)

If the flatten prelude halts, the original halts. The only subtle case is
`argsHeadHalt` (a later operand halts after earlier ones succeeded): recovering
the earlier operands' values needs them evaluable, which is where well-scopedness
(`hsc`) — via `flattenArgs_atoms_eval` — is used. -/
mutual
theorem flatten_halt_bwd {funs : FunEnv D} {P : String} {e : Expr Op}
    {Vo Va : VEnv D} {st : EvmState} (k : Nat)
    (hnt : noTempExpr P e = true) (hext : TempExt P Vo Va)
    (hsc : ∀ x, x ∈ freeVarsExpr e → (VEnv.get Vo x).isSome = true)
    {Va' sth} (hpre : Step D funs Va st (.stmts (flatten P k e).2.1) (.sres Va' sth .halt)) :
    Step D funs Vo st (.expr e) (.eres (.halt sth)) := by
  cases e with
  | var x => simp only [flatten] at hpre; cases hpre
  | lit l => simp only [flatten] at hpre; cases hpre
  | builtin op args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      simp only [flatten] at hpre
      rcases stmts_append_inv hpre with ⟨_, hph⟩ | ⟨Vm, stm, hpreA, htail⟩
      · exact Step.builtinArgsHalt (flattenArgs_halt_bwd k hna hext hsc hph)
      · cases htail with
        | seqCons _ hnil => cases hnil
        | seqStop hlet _ =>
            cases hlet with
            | letHalt hbe =>
                cases hbe with
                | builtinHalt hatoms hb =>
                    obtain ⟨hargs, _⟩ := flattenArgs_correct_bwd k hna hext hpreA hatoms
                    exact Step.builtinHalt hargs hb
                | builtinArgsHalt hah =>
                    exact absurd hah (fun h => (atomArgs_no_halt (flattenArgs_ok P k args).1 h).elim)
  | call fn args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      simp only [flatten] at hpre
      rcases stmts_append_inv hpre with ⟨_, hph⟩ | ⟨Vm, stm, hpreA, htail⟩
      · exact Step.callArgsHalt (flattenArgs_halt_bwd k hna hext hsc hph)
      · cases htail with
        | seqCons _ hnil => cases hnil
        | seqStop hlet _ =>
            cases hlet with
            | letHalt hce =>
                cases hce with
                | callHalt hatoms hlk hlen hbody =>
                    obtain ⟨hargs, _⟩ := flattenArgs_correct_bwd k hna hext hpreA hatoms
                    exact Step.callHalt hargs hlk hlen hbody
                | callArgsHalt hah =>
                    exact absurd hah (fun h => (atomArgs_no_halt (flattenArgs_ok P k args).1 h).elim)

theorem flattenArgs_halt_bwd {funs : FunEnv D} {P : String} {es : List (Expr Op)}
    {Vo Va : VEnv D} {st : EvmState} (k : Nat)
    (hnt : noTempArgs P es = true) (hext : TempExt P Vo Va)
    (hsc : ∀ x, x ∈ freeVarsArgs es → (VEnv.get Vo x).isSome = true)
    {Va' sth} (hpre : Step D funs Va st (.stmts (flattenArgs P k es).2.1) (.sres Va' sth .halt)) :
    Step D funs Vo st (.args es) (.eres (.halt sth)) := by
  cases es with
  | nil => simp only [flattenArgs] at hpre; cases hpre
  | cons e rest =>
      simp only [noTempArgs, Bool.and_eq_true] at hnt
      simp only [flattenArgs] at hpre
      -- well-scopedness transported to the prelude's starting env
      have hscVa : ∀ x, x ∈ freeVarsArgs (e :: rest) → (VEnv.get Va x).isSome = true := by
        intro x hx
        rw [TempExt.get (freeVarsArgs_noTemp (by simp [noTempArgs, hnt.1, hnt.2]) x hx) hext]
        exact hsc x hx
      rcases stmts_append_inv hpre with ⟨_, hph⟩ | ⟨Vr, str, hpreR, hpreH⟩
      · exact Step.argsRestHalt (flattenArgs_halt_bwd k hnt.2 hext
          (fun x hx => hsc x (by simp only [freeVarsArgs_cons, List.mem_append]; exact Or.inr hx)) hph)
      · obtain ⟨rvs, hrestAt⟩ := flattenArgs_atoms_eval k hnt.2
          (fun x hx => hscVa x (by simp only [freeVarsArgs_cons, List.mem_append]; exact Or.inr hx))
          hpreR
        obtain ⟨hargsRest, hextR⟩ := flattenArgs_correct_bwd k hnt.2 hext hpreR hrestAt
        have hheadHalt := flatten_halt_bwd (flattenArgs P k rest).1 hnt.1 hextR
          (fun x hx => hsc x (by simp only [freeVarsArgs_cons, List.mem_append]; exact Or.inl hx)) hpreH
        exact Step.argsHeadHalt hargsRest hheadHalt
end

/-- Head-flattening, halt (backward). Two forms: if the prelude halts, or if it
completes and the flat expression halts, the original expression halts. (The
prelude-halt half uses well-scopedness via `flattenArgs_halt_bwd`.) -/
theorem flattenTop_halt_bwd {funs : FunEnv D} {P : String} {e : Expr Op}
    {Vo Va : VEnv D} {st : EvmState} (k : Nat)
    (hnt : noTempExpr P e = true) (hext : TempExt P Vo Va)
    (hsc : ∀ x, x ∈ freeVarsExpr e → (VEnv.get Vo x).isSome = true) :
    (∀ {Va' sth}, Step D funs Va st (.stmts (flattenTop P k e).2.1) (.sres Va' sth .halt) →
        Step D funs Vo st (.expr e) (.eres (.halt sth))) ∧
    (∀ {Va' stM sth}, Step D funs Va st (.stmts (flattenTop P k e).2.1) (.sres Va' stM .normal) →
        Step D funs Va' stM (.expr (flattenTop P k e).2.2) (.eres (.halt sth)) →
        Step D funs Vo st (.expr e) (.eres (.halt sth))) := by
  cases e with
  | var x =>
      refine ⟨fun hph => ?_, fun _ hh => ?_⟩
      · simp only [flattenTop] at hph; cases hph
      · simp only [flattenTop] at hh; cases hh
  | lit l =>
      refine ⟨fun hph => ?_, fun _ hh => ?_⟩
      · simp only [flattenTop] at hph; cases hph
      · simp only [flattenTop] at hh; cases hh
  | builtin op args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      refine ⟨fun hph => ?_, fun hpre hh => ?_⟩
      · simp only [flattenTop] at hph
        exact Step.builtinArgsHalt (flattenArgs_halt_bwd k hna hext hsc hph)
      · simp only [flattenTop] at hpre hh
        cases hh with
        | builtinHalt hatoms hb =>
            obtain ⟨hargs, _⟩ := flattenArgs_correct_bwd k hna hext hpre hatoms
            exact Step.builtinHalt hargs hb
        | builtinArgsHalt hah =>
            exact absurd hah (fun h => (atomArgs_no_halt (flattenArgs_ok P k args).1 h).elim)
  | call fn args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      refine ⟨fun hph => ?_, fun hpre hh => ?_⟩
      · simp only [flattenTop] at hph
        exact Step.callArgsHalt (flattenArgs_halt_bwd k hna hext hsc hph)
      · simp only [flattenTop] at hpre hh
        cases hh with
        | callHalt hatoms hlk hlen hbody =>
            obtain ⟨hargs, _⟩ := flattenArgs_correct_bwd k hna hext hpre hatoms
            exact Step.callHalt hargs hlk hlen hbody
        | callArgsHalt hah =>
            exact absurd hah (fun h => (atomArgs_no_halt (flattenArgs_ok P k args).1 h).elim)

/-- Every variable bound by a `flattenTop` prelude is a temporary. -/
theorem flattenTop_prelude_decl {P : String} {k : Nat} {e : Expr Op} :
    ∀ t, (∃ rhs, Stmt.letDecl [t] (some rhs) ∈ (flattenTop P k e).2.1) → ∃ m, t = tempName P m := by
  intro t ht
  cases e with
  | var x => obtain ⟨rhs, hm⟩ := ht; simp [flattenTop] at hm
  | lit l => obtain ⟨rhs, hm⟩ := ht; simp [flattenTop] at hm
  | builtin op args =>
      obtain ⟨m, _, hm⟩ := flattenArgs_prelude_decl t (by simpa [flattenTop] using ht)
      exact ⟨m, hm⟩
  | call fn args =>
      obtain ⟨m, _, hm⟩ := flattenArgs_prelude_decl t (by simpa [flattenTop] using ht)
      exact ⟨m, hm⟩

/-- Members of a `noTempIdents` list are non-temporary. -/
theorem noTempIdents_mem {P : String} {vars : List Ident} (h : noTempIdents P vars = true) :
    ∀ x ∈ vars, isTemp P x = false := by
  intro x hx
  induction vars with
  | nil => simp at hx
  | cons y rest ih =>
      simp only [noTempIdents, Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases List.mem_cons.mp hx with rfl | hr
      · exact h.1
      · exact ih h.2 hr

end YulEvmCompiler.Optimizer.ANF
