import YulIR.SimplifyCongr
import YulIR.FuelMono

/-!
# YulIR.ObsEquiv — observational equivalence of IR programs

The soundness target for *structure-changing* optimizations. Two programs are observationally
equivalent when they terminate with exactly the same results (from any starting state). Because
the interpreter's fuel is just a termination bound (`FuelMono`), "terminates with result `res`"
is naturally phrased as *there exists* a fuel producing `res`.

`Simplify` already gives the stronger *per-fuel* equality (`simplify_run_eq`), which implies
observational equivalence via `obsEquiv_of_run_eq`. The remaining passes (`structural`, …) change
statement counts, so they can only be shown observationally equivalent — this is their target.
-/

namespace YulIR

open YulSemantics YulSemantics.EVM
open YulIR.Sem

/-- **Observational equivalence.** From every start state, the two programs terminate with exactly
the same results (`Sem.run` bundles the final VEnv/state/outcome; a program "terminates with `res`"
when some fuel yields `.ok res`). -/
def ObsEquiv (b1 b2 : Block) : Prop :=
  ∀ st0 res, (∃ f, Sem.run f b1 st0 = .ok res) ↔ (∃ f, Sem.run f b2 st0 = .ok res)

namespace ObsEquiv

theorem refl (b : Block) : ObsEquiv b b := fun _ _ => Iff.rfl

theorem symm {b1 b2 : Block} (h : ObsEquiv b1 b2) : ObsEquiv b2 b1 :=
  fun st res => (h st res).symm

theorem trans {b1 b2 b3 : Block} (h1 : ObsEquiv b1 b2) (h2 : ObsEquiv b2 b3) :
    ObsEquiv b1 b3 := fun st res => (h1 st res).trans (h2 st res)

end ObsEquiv

/-- Per-fuel equality of two programs implies observational equivalence. -/
theorem obsEquiv_of_run_eq {b1 b2 : Block}
    (h : ∀ f st, Sem.run f b1 st = Sem.run f b2 st) : ObsEquiv b1 b2 := by
  intro st res
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f, by rw [← h f st]; exact hf⟩
  · rintro ⟨f, hf⟩; exact ⟨f, by rw [h f st]; exact hf⟩

/-- **`Simplify` is observationally sound** (immediately, from the stronger per-fuel equality). -/
theorem simplify_obsEquiv (prog : Block) : ObsEquiv prog (simplifyBlock prog) :=
  obsEquiv_of_run_eq (fun f st => (simplify_run_eq f prog st).symm)

end YulIR
