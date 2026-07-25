import YulIR.Structural
import YulIR.FuelMono

set_option linter.unusedSimpArgs false

/-!
# YulIR.StructuralSound — building blocks for `structural`'s soundness

`structural = dropUnreachableBlock ∘ structuralBlock` is a *structure-changing* pass (it drops and
expands statements), so its soundness is observational (see `YulIR.ObsEquiv`), built on fuel
monotonicity. This file collects the reusable interpreter facts the eventual bisimulation needs;
the central one is that statements after a non-`normal` outcome are unreachable, which is exactly
what `dropUnreachableBlock` exploits.
-/

namespace YulIR

open YulSemantics YulSemantics.EVM
open YulIR.Sem

/-- A statement whose execution ends in a non-`normal` outcome makes the rest of its block
unreachable: the tail is never executed, so it may be dropped. -/
theorem execStmts_cons_nonNormal (f : Nat) (funs : FEnv) (env : VEnv) (st : EvmState)
    (s : Stmt) (rest : Block) {V : VEnv} {st' : EvmState} {o : Outcome}
    (h : execStmt f funs env st s = .ok (V, st', o)) (ho : o ≠ .normal) :
    execStmts (f + 1) funs env st (s :: rest) = .ok (V, st', o) := by
  cases o with
  | normal => exact absurd rfl ho
  | «break» => simp only [execStmts, h]
  | «continue» => simp only [execStmts, h]
  | leave => simp only [execStmts, h]
  | halt => simp only [execStmts, h]

/-- Consequently the tail is irrelevant: two blocks sharing a leading statement that ends
non-`normally` execute identically regardless of their (differing) tails. -/
theorem execStmts_cons_nonNormal_eq (f : Nat) (funs : FEnv) (env : VEnv) (st : EvmState)
    (s : Stmt) (rest rest' : Block) {V : VEnv} {st' : EvmState} {o : Outcome}
    (h : execStmt f funs env st s = .ok (V, st', o)) (ho : o ≠ .normal) :
    execStmts (f + 1) funs env st (s :: rest) = execStmts (f + 1) funs env st (s :: rest') := by
  rw [execStmts_cons_nonNormal f funs env st s rest h ho,
      execStmts_cons_nonNormal f funs env st s rest' h ho]

/-- `isTerminator` is a syntactic sufficient condition: `break`/`continue`/`leave` always execute
to their eponymous non-`normal` outcome (independent of fuel and state). -/
theorem execStmt_break (f funs env st) :
    execStmt f funs env st .«break» = .ok (env, st, .«break») := by simp only [execStmt]

theorem execStmt_continue (f funs env st) :
    execStmt f funs env st .«continue» = .ok (env, st, .«continue») := by simp only [execStmt]

theorem execStmt_leave (f funs env st) :
    execStmt f funs env st .leave = .ok (env, st, .leave) := by simp only [execStmt]

end YulIR
