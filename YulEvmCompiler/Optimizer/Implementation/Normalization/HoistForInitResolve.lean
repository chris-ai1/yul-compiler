import YulEvmCompiler.Optimizer.Implementation.Normalization.HoistForInit
import YulEvmCompiler.Optimizer.Implementation.InlineCallsResolve

set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# Layout-resolution congruence for `hoistForInit`

`hoistInitStmts` only restructures statements (it never touches an expression),
while `resolveForLayoutStmts` only rewrites `dataoffset`/`datasize` expressions,
so the two **strictly commute** (`resolve_hoistInitStmts`). The firing
conditions (`SimpleInit`, `isEmpty`) inspect statement shapes and list length,
both preserved by resolution, so the pass fires at exactly the same places
before and after resolving. The `RPass` congruence
(`resolveHoistForInitBlock_equiv`) then follows from block soundness.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "Dev" => evmWithExternal calls creates

/-! ### Resolution preserves the firing conditions -/

theorem simpleInitStmt_resolve (L : Layout) (s : Stmt Op) :
    simpleInitStmt (D := Dev) (resolveForLayoutStmt L s) = simpleInitStmt (D := Dev) s := by
  cases s <;> simp [simpleInitStmt]

theorem simpleInit_resolve (L : Layout) : ∀ init : List (Stmt Op),
    SimpleInit (D := Dev) (resolveForLayoutStmts L init) = SimpleInit (D := Dev) init
  | [] => by rw [resolveForLayoutStmts_nil]
  | s :: rest => by
      have ih := simpleInit_resolve L rest
      simp only [SimpleInit, resolveForLayoutStmts_cons, List.all_cons,
        simpleInitStmt_resolve] at ih ⊢
      rw [ih]

theorem isEmpty_resolve (L : Layout) (init : List (Stmt Op)) :
    (resolveForLayoutStmts L init).isEmpty = init.isEmpty := by
  cases init with
  | nil => rw [resolveForLayoutStmts_nil]
  | cons s rest => rw [resolveForLayoutStmts_cons]; rfl

/-! ### The strict commutation -/

mutual
theorem resolve_hoistInitStmt (L : Layout) : ∀ s : Stmt Op,
    resolveForLayoutStmt L (hoistInitStmt (D := Dev) s)
      = hoistInitStmt (D := Dev) (resolveForLayoutStmt L s)
  | .forLoop init c post body => by
      simp only [hoistInitStmt, resolveForLayoutStmt_forLoop, simpleInit_resolve, isEmpty_resolve]
      split <;>
        simp only [resolveForLayoutStmt_block, resolveForLayoutStmts_append,
          resolveForLayoutStmts_cons, resolveForLayoutStmts_nil,
          resolveForLayoutStmt_forLoop,
          resolve_hoistInitStmts L post, resolve_hoistInitStmts L body]
  | .block b => by
      simp only [hoistInitStmt, resolveForLayoutStmt_block, resolve_hoistInitStmts L b]
  | .cond c b => by
      simp only [hoistInitStmt, resolveForLayoutStmt_cond, resolve_hoistInitStmts L b]
  | .switch c cases dflt => by
      simp only [hoistInitStmt, resolveForLayoutStmt_switch, resolve_hoistInitCases L cases]
      cases dflt with
      | none => simp only [hoistInitDflt, Option.map_none]
      | some b => simp only [hoistInitDflt, Option.map_some, resolve_hoistInitStmts L b]
  | .funDef n ps rs b => by
      simp only [hoistInitStmt, resolveForLayoutStmt_funDef, resolve_hoistInitStmts L b]
  | .letDecl vars val => by simp only [hoistInitStmt, resolveForLayoutStmt_letDecl]
  | .assign vars e => by simp only [hoistInitStmt, resolveForLayoutStmt_assign]
  | .exprStmt e => by simp only [hoistInitStmt, resolveForLayoutStmt_exprStmt]
  | .break => by simp only [hoistInitStmt, resolveForLayoutStmt_break]
  | .continue => by simp only [hoistInitStmt, resolveForLayoutStmt_continue]
  | .leave => by simp only [hoistInitStmt, resolveForLayoutStmt_leave]
theorem resolve_hoistInitStmts (L : Layout) : ∀ ss : List (Stmt Op),
    resolveForLayoutStmts L (hoistInitStmts (D := Dev) ss)
      = hoistInitStmts (D := Dev) (resolveForLayoutStmts L ss)
  | [] => by simp only [hoistInitStmts, resolveForLayoutStmts_nil]
  | s :: rest => by
      simp only [hoistInitStmts, resolveForLayoutStmts_cons,
        resolve_hoistInitStmt L s, resolve_hoistInitStmts L rest]
theorem resolve_hoistInitCases (L : Layout) : ∀ cs : List (Literal × Block Op),
    resolveForLayoutCases L (hoistInitCases (D := Dev) cs)
      = hoistInitCases (D := Dev) (resolveForLayoutCases L cs)
  | [] => by simp only [hoistInitCases, resolveForLayoutCases]
  | (l, b) :: rest => by
      simp only [hoistInitCases, resolveForLayoutCases,
        resolve_hoistInitStmts L b, resolve_hoistInitCases L rest]
end

/-! ### The `RPass` congruence -/

theorem resolveHoistForInitBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock Dev (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L ((hoistForInit (D := Dev)).run b)) := by
  show EquivBlock Dev (resolveForLayoutStmts L b)
    (resolveForLayoutStmts L (hoistInitStmts (D := Dev) b))
  rw [resolve_hoistInitStmts L b]
  exact hoistForInit_blockEquiv (D := Dev) (resolveForLayoutStmts L b)

end YulEvmCompiler.Optimizer
