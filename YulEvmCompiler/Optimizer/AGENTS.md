# Working in `YulEvmCompiler/Optimizer/`

Verified **Yul→Yul** optimizer — the largest subtree in the repo (~35k lines, ~64%).
Read the root `AGENTS.md` first for the whole pipeline and the trust-boundary
rules; this file is the local map. `IDEAS.md` is the running log of passes tried,
in progress, or considered, with the framework facts needed before adding one.

Every optimization is source-to-source and runs *in front of* the verified
backend. The optimizer never re-opens a backend proof: it meets `compile_correct`
at the `YulSemantics.Run` interface.

## The one contract that matters

`Spec/Pass.lean` defines `Optimizer.Pass`: a total `run : Block D.Op → Block D.Op`
bundled with its only proof obligation,

```
Sound D run  :=  ∀ b, EquivBlock D b (run b)
```

`EquivBlock` (from pinned `YulSemantics.Equiv`) is *pointwise big-step*
equivalence — same final `VEnv`, same machine state (hence same halt payload),
same outcome, from every function env / variable env / initial state. It is
strictly stronger than observational equivalence, which is the point: a sound
replacement is undetectable in any context, so passes compose (`Pass.comp`) and
local rewrites lift through the `YulSemantics.Equiv` congruences.

**Possessing a `Pass` value *is* possessing a verified optimizer.** An auditor who
trusts `Spec/Pass.lean` need not read any individual pass proof.

## Three layers

- `Spec/` — the stable, audited surface. `Pass.lean` (the contract above),
  `Backend.lean` (`Pass.optimize_then_compile_correct`: a sound pass composes with
  the backend), `Observe.lean` (the weaker **observational tier** `ObsPass` /
  `ObsEquivBlock` for passes `EquivBlock` cannot express — dead bindings, scratch
  memory, dead stores before `revert`), and `MemoryGuard.lean` /
  `MemoryGuardSound.lean` (the `memoryguard`-based scratch-reservation contract
  built on `ObsPass`, with the `OpMemorySafe` / reserved-interval premises that
  make raising the guard pointer honest rather than an unconditional weakening).
  Treat `Spec/` as near-frozen: changing a contract is a design decision, not a
  pass addition. `PrePostPass.lean` adds the orthogonal "preserve, don't require"
  framework (`SoundUnder pre` for soundness prerequisites, `Preserves I` for kept
  invariants, `Establishes pre I` for the normalizer that reaches them, all with
  `comp`/`ofList`). `DeclPreserving.lean` discharges the common `Preserves` case
  without per-pass induction: a **declaration-non-generative** transform
  (`PreservesDecls`: declared-name multiset never grows) preserves
  `NormalForm.UniqueNames` (and any sub-multiset-antitone invariant) via one
  kernel, and the proven-once traversal skeletons `mapExprsBlock` (expression
  rewriting) and `filterStmtsDeep` (statement pruning) give preservation for free
  to any pass expressed through them — the pattern that avoids re-proving
  normal-form preservation for each optimization step.
- `Core/` — the typed optimizer IR. `Basic.lean` is intrinsically-scoped ANF
  (arity-indexed pure ops; `ingest` is partial, `ingest_emit` erases back to the
  exact Yul input). `Rule.lean` is a generic first-match rewrite engine whose
  rules each carry an `EquivExpr` proof. `Subst.lean` is closed-term
  instantiation + `valueEval` (the β machinery behind the helper inliner).
- `Implementation/` — the concrete passes and `Pipeline.lean`, which assembles
  them into the iterated `pipelineRounds`.

## `Implementation/` file-naming convention

For a pass `Foo` you will typically see:

- `Foo.lean` — the pass `run` definition and its strong `EquivBlock` soundness
  (block path).
- `FooResolve.lean` — the **resolution congruence**: the pass commutes with
  object-layout resolution (`resolveForLayout*`) up to `EquivBlock`. This is the
  missing link for the **object compile path**, and is where `dataoffset`/`datasize`
  (outside the total state-preserving fragment) are handled.
- `FooSound.lean` — the heavy soundness simulation, split out when the proof is
  large (e.g. `StackLayoutSound`, `InlineCallsSound`, `StorageForwardSound`).

Shared foundations: `Frame.lean` (VEnv frame lemma — the basis for dropping
unused/effect-free bindings), `ResolveCongr.lean`, `FunCongr.lean`,
`BoundFunCongr.lean`, `InlineHelpers.lean`. Object-path variants: `ObjectPass.lean`,
`StackLayoutObject.lean`.

The `MemorySpill*` family is the guarded **memory-spilling** fallback (an
`ObsPass`/`MemoryGuard` optimization, *not* part of `pipelineRounds`): when stack
pressure would force an unsupported `DUP17+`/`SWAP17+`, `MemorySpill.lean` (the
mechanism) plus `MemorySpillSelect.lean` (pressure-based, lexically-scoped,
call-path slot allocation) move selected bindings into `memoryguard`-reserved
scratch memory. Its many `MemorySpill*Sound.lean` files prove the composed
direct-block and object theorems.

The production pipeline (`Pipeline.lean`) currently runs: `Simplify` → `Propagate`
→ `InlineHelpers` → `HoistCalls`/`FreshenCalls`/`InlineCalls` → `StorageForward` →
`Simplify` → `DeadPure` → `DeadResults`, iterated so leaf-first inlining and
per-round leftovers (copy bindings, zeroed returns) feed the next round.

## Adding a pass

1. Read `IDEAS.md` and the framework facts at its top (which EVM ops are pure and
   state-independent, when algebraic identities are sound, the Core boundary).
2. Write `run` as a total `Block → Block`. Leave unsupported syntax unchanged so
   the function stays total — that is why `Core.ingest` is partial.
3. Prove `Sound D run` (an `EquivBlock` for all `b`). Prefer local Core rewrites
   with proof-carrying `Rule`s and lift them through the `YulSemantics.Equiv`
   congruences over one giant tactic block.
4. If the pass must run on the object path, add its `FooResolve` congruence.
5. Wire it into `Pipeline.lean` and add examples/`#guard`s. A pass whose contract
   is only observational goes through `Spec/Observe.lean` and needs human sign-off
   before entering the audited roots.
6. If any of this moves the audited specification surface, **stop and surface it
   for a human** — see the trust-boundary section of the root `AGENTS.md`.
   `SpecClosure.lean` imports this subtree; do not re-pin it yourself.

No `sorry`, no `axiom`, no `unsafe` — the whole repo must stay axiom-clean.
