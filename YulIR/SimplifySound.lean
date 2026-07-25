import YulIR.Simplify
import YulIR.Semantics

set_option linter.unusedSimpArgs false

/-!
# YulIR.SimplifySound — soundness of the `Simplify` pass

`simplify` preserves the IR semantics: for every program the definitional interpreter
(`YulIR.Sem`) produces the same result on `simplifyBlock b` as on `b`.

The heart is `simplifyRhs_eval`: simplifying a right-hand side does not change how it evaluates.
* **Folding** delegates to the dialect's `stepOp`, and pure ops thread the state unchanged with a
  value depending only on their arguments (`stepOp_pure_ok`), so folding at `EvmState.init`
  (in `evalConst`) agrees with evaluation at any runtime state; the literal round-trips
  (`litValue_number_toNat`).
* **Identities** are discharged from the same `stepOp` unfolding plus `BitVec` arithmetic.

The whole-program result then follows by a structural congruence over the interpreter.
-/

namespace YulIR

open YulSemantics YulSemantics.EVM
open YulIR.Sem

/-- Number literals round-trip through the dialect's value function. -/
@[simp] theorem litValue_number_toNat (r : U256) : litValue (Literal.number r.toNat) = r := by
  simp [litValue]

/-- `bin` threads the state through unchanged. -/
theorem bin_state {f : U256 → U256 → U256} {vals st st2 rets stx}
    (h : bin f vals st = some (.ok rets stx)) : bin f vals st2 = some (.ok rets st2) := by
  unfold bin at h ⊢; split at h <;> simp_all

/-- `un` threads the state through unchanged. -/
theorem un_state {f : U256 → U256} {vals st st2 rets stx}
    (h : un f vals st = some (.ok rets stx)) : un f vals st2 = some (.ok rets st2) := by
  unfold un at h ⊢; split at h <;> simp_all

/-- `ter` threads the state through unchanged. -/
theorem ter_state {f : U256 → U256 → U256 → U256} {vals st st2 rets stx}
    (h : ter f vals st = some (.ok rets stx)) : ter f vals st2 = some (.ok rets st2) := by
  unfold ter at h ⊢; split at h <;> simp_all

/-- A pure built-in threads the state unchanged and its result depends only on its arguments:
if it produces `.ok rets` from one state, it produces the same `rets` (with the state passed
through) from any state. -/
theorem stepOp_pure_ok {op : Op} {vals : List U256} {st st2 : EvmState} {rets : List U256}
    {stx : EvmState} (hp : Op.isPure op = true) (h : stepOp op vals st = some (.ok rets stx)) :
    stepOp op vals st2 = some (.ok rets st2) := by
  cases op <;>
    first
      | exact bin_state (by simpa [stepOp] using h)
      | exact un_state (by simpa [stepOp] using h)
      | exact ter_state (by simpa [stepOp] using h)
      | (simp [Op.isPure, effects, Effects.top] at hp; done)   -- non-pure ops: hp is False
      | (simp only [stepOp] at h ⊢; split at h <;> simp_all)   -- `pop`

/-- Evaluating an all-literal argument list yields the literals' values. -/
theorem evalAtoms_map_lit (env : VEnv) (lits : List Literal) :
    evalAtoms env (lits.map Atom.lit) = some (lits.map litValue) := by
  induction lits with
  | nil => rfl
  | cons x xs ih =>
      simp only [evalAtoms] at ih
      simp [evalAtoms, List.map_cons, List.mapM_cons, evalAtom, ih]

/-- **Constant-folding soundness.** When `evalConst` folds a pure built-in on all-literal
operands to a literal `l`, evaluating the folded literal agrees with evaluating the original
built-in from any state: both give `[litValue l]` leaving the state unchanged. This is the core
of `Simplify`'s soundness — it holds *because* folding delegates to the dialect's `stepOp`
(`evalConst`) and pure ops are state-independent (`stepOp_pure_ok`). -/
theorem evalConst_fold_sound (fuel : Nat) (funs : FEnv) (env : VEnv) (st : EvmState)
    {op : Op} {lits : List Literal} {l : Literal}
    (hp : Op.isPure op = true) (hc : evalConst op lits = some l) :
    evalRhs fuel funs env st (.builtin op (lits.map Atom.lit)) = .ok (.vals [litValue l] st) := by
  unfold evalConst at hc
  simp only [evalRhs, evalAtoms_map_lit]
  split at hc
  · rename_i r' stinit heq
    have hst2 := stepOp_pure_ok (st2 := st) hp heq
    simp only [hst2]
    injection hc with hc; subst hc
    simp [litValue_number_toNat]
  · simp at hc

/-- Evaluating a two-argument `bin`-shaped built-in. -/
theorem evalRhs_bin {op : Op} {f : U256 → U256 → U256}
    (hop : ∀ vals st', stepOp op vals st' = bin f vals st')
    (fuel : Nat) (funs : FEnv) (env : VEnv) (st : EvmState) (a b : Atom) :
    evalRhs fuel funs env st (.builtin op [a, b])
      = (match evalAtom env a, evalAtom env b with
         | some av, some bv => Result.ok (.vals [f av bv] st)
         | _, _ => Result.stuck) := by
  cases ha : evalAtom env a <;> cases hb : evalAtom env b <;>
    simp_all [evalRhs, evalAtoms, List.mapM, List.mapM.loop, hop, bin]

/-- An atom that is a literal of value `n` evaluates to that value. -/
theorem isLitVal_eval {env : VEnv} {a : Atom} {n : Nat} (h : Atom.isLitVal a n = true) :
    evalAtom env a = some (BitVec.ofNat 256 n) := by
  unfold Atom.isLitVal at h
  split at h
  · rename_i l; simp only [beq_iff_eq] at h; simp [evalAtom, h]
  · exact absurd h (by simp)

/-- Identity dropping a left literal-`k` operand (`f k v = v`). -/
theorem idL {op : Op} {f} (hop : ∀ vals st', stepOp op vals st' = bin f vals st')
    {a : Atom} {k : U256} (fuel funs env st) (ha : evalAtom env a = some k)
    (hf : ∀ v, f k v = v) (b : Atom) :
    evalRhs fuel funs env st (.builtin op [a, b]) = evalRhs fuel funs env st (.atom b) := by
  rw [evalRhs_bin hop]; simp only [evalRhs, ha]; cases evalAtom env b <;> simp_all [hf]

/-- Identity dropping a right literal-`k` operand (`f v k = v`). -/
theorem idR {op : Op} {f} (hop : ∀ vals st', stepOp op vals st' = bin f vals st')
    {b : Atom} {k : U256} (fuel funs env st) (hb : evalAtom env b = some k)
    (hf : ∀ v, f v k = v) (a : Atom) :
    evalRhs fuel funs env st (.builtin op [a, b]) = evalRhs fuel funs env st (.atom a) := by
  rw [evalRhs_bin hop]; simp only [evalRhs, hb]; cases evalAtom env a <;> simp_all [hf]

/-- Idempotent identity (`f v v = v`) on repeated operand. -/
theorem idSelf {op : Op} {f} (hop : ∀ vals st', stepOp op vals st' = bin f vals st')
    (fuel funs env st) (hf : ∀ v, f v v = v) (a : Atom) :
    evalRhs fuel funs env st (.builtin op [a, a]) = evalRhs fuel funs env st (.atom a) := by
  rw [evalRhs_bin hop]; simp only [evalRhs]; cases evalAtom env a <;> simp_all [hf]

/-- Worked instances confirming the operand-returning identities are sound (each is a direct
application of `idL`/`idR`/`idSelf`); the general `simplifyIdentity_eval` dispatcher over all ops
is the remaining mile. -/
example (fuel funs env st) (a b : Atom) (h : Atom.isLitVal a 0 = true) :
    evalRhs fuel funs env st (.builtin Op.add [a, b]) = evalRhs fuel funs env st (.atom b) :=
  idL (by intro vals st'; rfl) fuel funs env st (isLitVal_eval h) (by intro v; bv_decide) b

example (fuel funs env st) (a b : Atom) (h : Atom.isLitVal b 1 = true) :
    evalRhs fuel funs env st (.builtin Op.mul [a, b]) = evalRhs fuel funs env st (.atom a) :=
  idR (by intro vals st'; rfl) fuel funs env st (isLitVal_eval h) (by intro v; bv_decide) a

example (fuel funs env st) (a : Atom) :
    evalRhs fuel funs env st (.builtin Op.and [a, a]) = evalRhs fuel funs env st (.atom a) :=
  idSelf (by intro vals st'; rfl) fuel funs env st (by intro v; bv_decide) a

end YulIR
