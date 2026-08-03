import YulEvmCompiler.Optimizer.Implementation.RematSpill
import YulEvmCompiler.Optimizer.Implementation.ReuseValuesSound
import YulEvmCompiler.Optimizer.Implementation.Propagate
set_option warningAsError true
/-!
# Soundness of substitute-only rematerialization

**STATUS (2026-08): proof paused, green.** The reusable core is proven —
expression-level substitution congruence (`subst_expr_fwd`/`_bwd`,
`subst_args_fwd`/`_bwd`), `RematOk.frame` (invariant preserved under env
framing), and `RematOk.cons_let` (fact creation). The remaining statement-level
`Step` simulation + `EquivBlock`/object assembly are NOT done. Work was stood
down per the prove-what-pays policy: origin/main's SSA-CFG backend now races the
classic path per object and wins the hot uniswap objects (PoolSwap 51,030 via
SSA vs 55,267 classic), collapsing remat's residual justification on this
corpus. The `RematSpill` transform stays merged (it still wins the race on some
spill-path objects corpus-wide) and is empirically validated; only the machine
proof is deferred.

`RematSpill.rematSubstBlock` replaces reads of a single-def, pure-total,
stable-free-var producer variable `x` by its producer expression `e`, keeping
every binding in place (`DeadPure`, composed afterwards, deletes the now-dead
`let`s — its own proof discharges removal). Because the binding is kept, the
runtime environment is byte-identical to the input, and soundness reduces to a
per-use **substitution congruence**: at any reachable state, `x` and `e`
evaluate to the same value with the same state.

This file proves that congruence at the **expression** level first (the
reusable core): under the invariant `RematOk V σ` — every fact `(x, e)` has `x`
bound and `evalPure V e` equal to `x`'s value — evaluating `substExprR σ t`
Steps identically to evaluating `t`. `evalPure`/`evalPure_step`/
`evalPure_step_inv`/`evalPure_agree` are reused verbatim from
`ReuseValuesSound`; the fact producers are always in the pure-total fragment
(`RematOk` makes `evalPure` defined), so replaying them is total and
state-preserving.
-/

namespace YulEvmCompiler.Optimizer.RematSpill

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer (EnvFrame codeWriteSet)
open YulEvmCompiler.Optimizer.ReuseValues (evalPure evalPureArgs evalPure_step
  evalPure_step_inv evalPure_agree exprVarsRv)

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-- The substitution invariant: every fact `(x, e)` in `σ` has `x` bound to a
value that `e` also evaluates to (in the pure-total fragment). -/
def RematOk (V : VEnv D) (σ : RematMap) : Prop :=
  ∀ p ∈ σ, ∃ v : U256, VEnv.get V p.1 = some v ∧ evalPure V p.2 = some v

theorem RematOk.lookup {V : VEnv D} {σ : RematMap} (h : RematOk V σ)
    {x : Ident} {e : Expr Op} (hmem : (x, e) ∈ σ) :
    ∃ v : U256, VEnv.get V x = some v ∧ evalPure V e = some v :=
  h (x, e) hmem

/-- The variables a fact map speaks about: keys and producer free variables. -/
def factVars (σ : RematMap) : List Ident :=
  σ.flatMap (fun p => p.1 :: exprVarsRv p.2)

theorem factVars_of_mem {σ : RematMap} {p : Ident × Expr Op} (hp : p ∈ σ) :
    p.1 ∈ factVars σ ∧ ∀ z ∈ exprVarsRv p.2, z ∈ factVars σ := by
  refine ⟨?_, ?_⟩
  · exact List.mem_flatMap.mpr ⟨p, hp, by simp⟩
  · exact fun z hz => List.mem_flatMap.mpr ⟨p, hp, by simp [hz]⟩

/-- **Framing preserves the invariant.** If an environment step keeps every
fact variable's lookup fixed (it lies outside the framed write set), then
`RematOk` survives: each key's value is unchanged and each producer's `evalPure`
is unchanged (`evalPure` reads only its free variables). -/
theorem RematOk.frame {V V' : VEnv D} {σ : RematMap} {ws : List Ident}
    (hok : RematOk V σ) (hf : EnvFrame ws V V')
    (hdisj : ∀ w ∈ factVars σ, w ∉ ws) :
    RematOk V' σ := by
  intro p hp
  obtain ⟨v, hxv, hev⟩ := hok p hp
  obtain ⟨hkey, hfv⟩ := factVars_of_mem hp
  refine ⟨v, ?_, ?_⟩
  · rw [EnvFrame.get_eq hf (hdisj p.1 hkey)]; exact hxv
  · rw [evalPure_agree (fun z hz => EnvFrame.get_eq hf (hdisj z (hfv z hz)))]
    exact hev

/-- The producer chosen for `x` by `substExprR`, when `x` is a fact key. -/
theorem substExprR_var_mem {σ : RematMap} {x : Ident} {e : Expr Op}
    (hfind : σ.find? (fun p => p.1 = x) = some (x, e)) :
    substExprR σ (.var x) = e := by
  simp [substExprR, hfind]

/-- **Fact creation.** Binding a fresh key `x` (absent from the existing facts
and from its own producer's free vars) to `v = evalPure V e'` extends `RematOk`
with the new fact `(x, e')`; existing facts survive because the new binding
lies outside every fact variable. -/
theorem RematOk.cons_let {V : VEnv D} {σ : RematMap} {x : Ident} {e' : Expr Op}
    {v : U256} (hok : RematOk V σ) (hxfresh : x ∉ factVars σ)
    (hxnotfree : x ∉ exprVarsRv e') (hev : evalPure V e' = some v) :
    RematOk ((x, v) :: V) ((x, e') :: σ) := by
  have hget : ∀ y, y ≠ x → VEnv.get ((x, v) :: V) y = VEnv.get V y := by
    intro y hy; rw [VEnv.get_cons]; exact if_neg (fun h => hy h.symm)
  intro p hp
  rcases List.mem_cons.mp hp with hp | hp
  · subst hp
    refine ⟨v, ?_, ?_⟩
    · rw [VEnv.get_cons]; exact if_pos rfl
    · rw [evalPure_agree (fun z hz => hget z (fun h => hxnotfree (h ▸ hz)))]; exact hev
  · obtain ⟨w, hxw, hew⟩ := hok p hp
    obtain ⟨hkey, hfv⟩ := factVars_of_mem hp
    have hpx : p.1 ≠ x := fun h => hxfresh (h ▸ hkey)
    refine ⟨w, ?_, ?_⟩
    · rw [hget p.1 hpx]; exact hxw
    · rw [evalPure_agree (fun z hz => hget z (fun h => hxfresh (h ▸ hfv z hz)))]
      exact hew

/-! ### Expression-level substitution congruence (forward + backward) -/

mutual
/-- Forward: any evaluation of `t` is matched by an evaluation of
`substExprR σ t` to the same result. -/
theorem subst_expr_fwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    (hok : RematOk V σ) :
    ∀ {t : Expr Op} {res : EResult D},
      Step D funs V st (.expr t) (.eres res) →
      Step D funs V st (.expr (substExprR σ t)) (.eres res)
  | .lit l, res, h => by simpa [substExprR] using h
  | .var x, res, h => by
      unfold substExprR
      cases hfind : σ.find? (fun p => p.1 = x) with
      | none => exact h
      | some p =>
          -- `p.1 = x` since `find?` matched the predicate `p.1 = x`.
          have hpx : p.1 = x := by
            have := List.find?_some hfind; simpa using this
          have hmem : p ∈ σ := List.mem_of_find?_eq_some hfind
          obtain ⟨v, hxv, hev⟩ := hok p hmem
          rw [hpx] at hxv
          -- `t = .var x` Steps to `[v✝] st`; the producer replays it.
          cases h with
          | var hget =>
              have hvv : _ = v := Option.some.inj (hget.symm.trans hxv)
              subst hvv
              exact evalPure_step hev funs st
  | .builtin op args, res, h => by
      cases h with
      | builtinOk hargs hb =>
          exact Step.builtinOk (subst_args_fwd hok hargs) hb
      | builtinHalt hargs hb =>
          exact Step.builtinHalt (subst_args_fwd hok hargs) hb
      | builtinArgsHalt hargs =>
          exact Step.builtinArgsHalt (subst_args_fwd hok hargs)
  | .call f args, res, h => by
      cases h with
      | callOk hargs hlk hlen hbody ho =>
          exact Step.callOk (subst_args_fwd hok hargs) hlk hlen hbody ho
      | callHalt hargs hlk hlen hbody =>
          exact Step.callHalt (subst_args_fwd hok hargs) hlk hlen hbody
      | callArgsHalt hargs =>
          exact Step.callArgsHalt (subst_args_fwd hok hargs)

theorem subst_args_fwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    (hok : RematOk V σ) :
    ∀ {ts : List (Expr Op)} {res : EResult D},
      Step D funs V st (.args ts) (.eres res) →
      Step D funs V st (.args (substArgsR σ ts)) (.eres res)
  | [], res, h => by simpa [substArgsR] using h
  | t :: rest, res, h => by
      unfold substArgsR
      cases h with
      | argsCons hrest hhead =>
          exact Step.argsCons (subst_args_fwd hok hrest) (subst_expr_fwd hok hhead)
      | argsRestHalt hrest =>
          exact Step.argsRestHalt (subst_args_fwd hok hrest)
      | argsHeadHalt hrest hhead =>
          exact Step.argsHeadHalt (subst_args_fwd hok hrest) (subst_expr_fwd hok hhead)
end

mutual
/-- Backward: any evaluation of `substExprR σ t` is matched by an evaluation of
`t` to the same result. -/
theorem subst_expr_bwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    (hok : RematOk V σ) :
    ∀ {t : Expr Op} {res : EResult D},
      Step D funs V st (.expr (substExprR σ t)) (.eres res) →
      Step D funs V st (.expr t) (.eres res)
  | .lit l, res, h => by simpa [substExprR] using h
  | .var x, res, h => by
      revert h
      unfold substExprR
      cases hfind : σ.find? (fun p => p.1 = x) with
      | none => exact fun h => h
      | some p =>
          intro h
          have hpx : p.1 = x := by
            have := List.find?_some hfind; simpa using this
          have hmem : p ∈ σ := List.mem_of_find?_eq_some hfind
          obtain ⟨v, hxv, hev⟩ := hok p hmem
          rw [hpx] at hxv
          -- `substExprR = p.2` evaluated to `res`; totality pins `res = [v] st`.
          have := evalPure_step_inv hev funs st _ h
          rw [this]
          exact Step.var hxv
  | .builtin op args, res, h => by
      revert h; unfold substExprR; intro h
      cases h with
      | builtinOk hargs hb => exact Step.builtinOk (subst_args_bwd hok hargs) hb
      | builtinHalt hargs hb => exact Step.builtinHalt (subst_args_bwd hok hargs) hb
      | builtinArgsHalt hargs => exact Step.builtinArgsHalt (subst_args_bwd hok hargs)
  | .call f args, res, h => by
      revert h; unfold substExprR; intro h
      cases h with
      | callOk hargs hlk hlen hbody ho =>
          exact Step.callOk (subst_args_bwd hok hargs) hlk hlen hbody ho
      | callHalt hargs hlk hlen hbody =>
          exact Step.callHalt (subst_args_bwd hok hargs) hlk hlen hbody
      | callArgsHalt hargs => exact Step.callArgsHalt (subst_args_bwd hok hargs)

theorem subst_args_bwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    (hok : RematOk V σ) :
    ∀ {ts : List (Expr Op)} {res : EResult D},
      Step D funs V st (.args (substArgsR σ ts)) (.eres res) →
      Step D funs V st (.args ts) (.eres res)
  | [], res, h => by simpa [substArgsR] using h
  | t :: rest, res, h => by
      revert h; unfold substArgsR; intro h
      cases h with
      | argsCons hrest hhead =>
          exact Step.argsCons (subst_args_bwd hok hrest) (subst_expr_bwd hok hhead)
      | argsRestHalt hrest =>
          exact Step.argsRestHalt (subst_args_bwd hok hrest)
      | argsHeadHalt hrest hhead =>
          exact Step.argsHeadHalt (subst_args_bwd hok hrest) (subst_expr_bwd hok hhead)
end

end YulEvmCompiler.Optimizer.RematSpill
