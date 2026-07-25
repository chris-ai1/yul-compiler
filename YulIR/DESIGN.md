# YulIR — an experimental optimizer IR for the Yul→EVM compiler

## Why

Optimizing Yul directly, and proving those optimizations correct against the
`yul-semantics` big-step judgment, is hard: expressions, effects and halting are
entangled, variables are named+mutable with scoped shadowing, and the meta-theory has
no `funDef` congruence. This experiment tests whether a small, ANF, structured IR makes
optimizations easier to write and (later) to prove, while producing EVM bytecode
competitive with the existing (solc-comparable) Yul optimizer.

**Goal:** IR optimizer performance comparable to solc's Yul optimizer.

## Pipeline

```
Yul  ──ofYul──▶  YulIR  ──optimize──▶  YulIR  ──toYul──▶  Yul  ──(verified backend)──▶  EVM
     (trusted)          (this work)          (erasure)         (YulEvmCompiler.compile)
```

`ofYul`/`toYul` are trusted (unproven) today; `toYul` is a structural **erasure**, so IR
optimizations are measured as real EVM code-size/gas changes through the existing verified
backend. Semantic soundness of `ofYul∘toYul` and of `optimize` is checked with the
`yul-semantics` interpreter (`YulIR/CheckBaseline.lean`), not yet proven.

## IR (`YulIR/Ast.lean`)

- **ANF**: every built-in/call argument is an `Atom` (literal or variable); nested
  expressions are lifted to `let`-temporaries. Fixes evaluation order syntactically.
- **Right-to-left** argument flattening in `ofYul` preserves Yul's observable arg order.
- **Structured control, no `for`-init**: `loop post body` ≙ `for {} 1 { post } { body }`,
  the condition folded into `body` as `if iszero(c) { break }`.
- **Named** variables (erasure to Yul is trivial). The intrinsically-scoped `Var Γ`
  refinement (à la `Optimizer.Core.Term`) is deferred to proof time.

## Passes (`YulIR/Optimize.lean` = `optimize`)

Order: `uniquify` → (`valueNumber` → `structural` → `deadStore` → `deadCode`) ×2.

| Pass | File | What | Provability notes |
|---|---|---|---|
| Uniquify | `Uniquify.lean` | α-rename every declaration to a globally fresh name; removes shadowing | α-renaming; behaviour-preserving |
| Simplify | `Simplify.lean` | local constant folding (via dialect `stepOp`) + algebraic identities | per-`Rhs`, local; folding delegates to the semantics |
| ValueNumber | `ValueNumber.lean` | const/copy propagation, folding across `let`s, CSE — tracks only *immutable* values so no invalidation is ever needed | forward, monotone; immutability = never an `assign` target |
| Structural | `Structural.lean` | dead-branch (`if 0`), constant `switch` selection, `if 1`→block, empty removal, and unreachable-code elimination (drop stmts after a terminator) | local, per-statement rewrites |
| DeadStore | `DeadStore.lean` | remove `x := <pure rhs>` whose value is never observed (backward liveness; conservative for loops/`break`/`continue`; return vars protected) | only removes a provably-dead pure store |
| DeadCode | `DeadCode.lean` | remove unused pure bindings, and pure statements like `pop(x)`; fixpoint | pure ⇒ no observable effect |

### Design decisions of note

- **CSE is kept on despite growing code on some categories** (`equalStoreEliminator`,
  `unusedStoreEliminator`): on a stack machine, reusing a value via a copy extends its live
  range and adds DUP/SWAP shuffling. A later **rematerialization / cost model** (and
  gas-weighted, not size-weighted, accounting on expensive reused ops) is expected to make
  CSE net-positive. See `ValueNumber.recordLet`.
- **Soundness by immutability**: value numbering only tracks variables that are never
  reassigned, so tracked facts never go stale — the key trick that keeps the pass simple and
  (later) provable without dataflow invalidation lemmas.

## Measuring

`current` = today's `YulEvmCompiler.Optimizer.optimizerPipeline` (solc-comparable, the target).

- **Correctness gate** (CI, fast): `YulIR/CheckBaseline.lean` — round-trip and `optimize`
  both preserve interpreter behaviour over `YulIR/Corpus.lean`.
- **Optimization tracking** (CI, drift-robust): `scripts/YulIRCorpus.lean check` over
  Solidity's `yulOptimizerTests`, per optimizer-step category, gated on a source-fingerprinted
  `test/yulir-corpus-size-baseline.txt`. Columns: `current` / `ir-noopt` / `ir-opt`.
- **Behaviour sweep** (local, slow): `scripts/YulIRCorpus.lean behaviour <dir>` — IR-opt
  vs current bytecode over the whole corpus (`compareBytecode`). Step-cap/gas-bound diffs are
  classified separately from real observable divergences.
- **Gas vs solc's optimizer** (local, slow): `scripts/YulIRCorpus.lean gas <dir> <solc> <ver>` —
  compiles each block fixture three ways from the *identical* Yul (`ir-opt`, `current`, and
  `solc --strict-assembly --optimize`), executes all three in the EVM, and sums gas over the
  scenarios where they halt with identical observable state. This measures the IR optimizer
  against **solc's actual Yul optimizer** — the true target — not merely the in-repo optimizer.
  Reports both `[ir-opt vs solc]` and a strict three-way total on an identical scenario set.

Run in the interpreter (`lake env lean --run …`); a native `lean_exe` would be faster at
runtime but requires compiling the whole mathlib closure with the C backend (~13 min), so it
is reserved for CI-cached heavy runs, not local iteration.

## Status & roadmap toward parity

Current, on Solidity's `yulOptimizerTests` (solc 0.8.35, `--evm-version osaka`; corpus
`argotorg/solidity` develop @ 96bdc548):

* **Gas ≈ parity with solc's Yul optimizer**: total EVM execution gas, summed over the 2,770
  scenarios (607/636 block fixtures) where `ir-opt` and `solc --strict-assembly --optimize` halt
  identically, is `ir-opt` 1,200,216,276 vs `solc` 1,200,204,507 — **+0.001%** (+11,769 gas).
  For reference the in-repo `current` optimizer is `1,200,120,698` on that same set, **−0.007%**
  vs solc; so `ir-opt` is **+0.008%** vs `current`. This is now measured against **solc's actual
  optimizer** (`scripts/YulIRCorpus.lean gas`), not just the in-repo baseline.
  * *Caveat:* the aggregate is dominated by a handful of very high-gas loop fixtures where all
    three do essentially identical work. Per scenario, `ir-opt` is cheaper than solc in 85,
    costlier in 2,319, equal in 366 — i.e. usually a few gas above solc, with the total pulled to
    parity by the big-gas fixtures. Dropped (logged, never silent): 1 solc-rejected `verbatim`,
    28 `ir-opt`-uncompilable and 26 `current`-uncompilable fixtures (mostly `verbatim`).
* **Code size within ~1.2%**: `ir-opt` 221,001 vs `current` 218,372 (**−9%** vs `ir-noopt` 240,892);
  several categories *beat* `current` (`structuralSimplifier`, `deadCodeEliminator`,
  `unusedAssignEliminator`, `unusedPruner`, `fullSuite`).
* **Correctness**: full-corpus behaviour sweep = **0 miscompiles**; interp gate green on 57 progs.

Done: uniquify · simplify · value-numbering (const/copy-prop, fold, CSE) · structural +
unreachable-code · dead-store (unused-assignment) · dead pure bindings/statements.

**Where the residual size gap is** (measured): dominated by `loopInvariantCodeMotion` (+4170) and
`equalStore`/`unusedStore`. It is *not* CSE alone — gating CSE to expensive ops did not remove it,
and it persists from copy-propagation/uniquify changing variable liveness/naming in ways the
**backend stack allocator** lowers less well. I.e. the remaining gap is now as much a *backend
stack-scheduling* problem as a missing IR pass.

Remaining to reach/exceed parity:

- [ ] **Function inlining** (`fullInliner`, `expressionInliner`, `functionSpecializer`):
      capture-avoiding (unique names make this clean); mainly valuable for *unlocking*
      cross-call propagation. `leave` handling is the crux (restrict to leave-free,
      non-recursive, small bodies first).
- [ ] **Load resolver** (`loadResolver`, `equalStoreEliminator`, `unusedStoreEliminator`):
      memory/storage store→load forwarding + redundant/overwritten-store elimination
      (needs an effect/aliasing model; the pure/effect split helps). Also recovers the
      CSE-inflated storage-store categories.
- [ ] **Rematerialization + a stack-aware cost model**: undo CSE (and later LICM) where the
      live-range extension costs more DUP/SWAP than recomputation saves. (CSE is kept on
      deliberately; this is its counterpart.)
- [ ] **Gas measurement** alongside code size: LICM and CSE trade size for gas, so the size
      metric under-credits them. Add a gas column (execution over the corpus; likely a native
      `lean_exe` since interpreter execution is minutes).
- [ ] **Loop-invariant code motion** (`loopInvariantCodeMotion`): gas-oriented; gate on the
      gas metric + cost model.
- [ ] If the backend's **stack allocation** is the bottleneck, improve the Yul→EVM
      DUP/SWAP/POP scheduling.

Each pass: implement → interpreter-validate → measure on the corpus → behaviour-sweep →
re-pin baseline → commit & push → update this file.
