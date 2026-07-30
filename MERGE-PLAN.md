# Merge plan: wiring the Asm scheduler into the *verified* compile path

Status of the proof work (branch `agent/uv4-sched-proof`, file
`YulEvmCompiler/AsmScheduleSound.lean`, sorry-free, in the default build):

- `symExec_sound` — the window executor is sound (the single lemma the
  translation-validation design reduces to).
- `schedule_equiv` / `optimizeWindow_equiv` — an accepted window is
  step-equivalent to the original on every suitable concrete stack.
- `labelDefs_scheduleAsm` / `labelRefs_scheduleAsm` (equalities),
  `codeSize_scheduleAsm_le`, `wfProg_scheduleAsm` — `scheduleAsm` preserves the
  whole label structure and never grows byte size, so lowering + the address-fit
  bound survive.

This document is the checklist to promote the *untrusted* `compileScheduled`
glue into the verified pipeline at full rigor. It assumes the one remaining Lean
obligation below is discharged; everything after it is mechanical.

---

## 0. Prerequisite (the only remaining Lean obligation)

**Gate is finalized.** The acceptance gate now carries the two soundness
conjuncts (both landed / added): `opExposed(cand) ⊆ opExposed(target)` (from the
scheduler agent) and `tcand.inputs ≤ target.inputs` (added as an INTERFACE commit
by the proof agent — reconcile the scheduler's copy to match). Together they
close both code-address subtleties: an op-dropped reached code slot
(`[pop]` vs `[iszero,pop]` diverge on `.code L`), and a candidate reaching
strictly deeper than the original (underflow on a shallow stack). Compiled runs
do put return addresses in window reach (`compileArgs` dup past `pushLabel Lret`;
the epilogue `retRot` window), so both were real.

**Executor + gate soundness is complete and sorry-free** in
`AsmScheduleSound.lean`, over WORD *and* `AVal` stacks:
`symExec_sound`/`symExec_sound_pad`; `schedule_equiv`,
`symStateEquiv_transform_eq`, `optimizeWindow_spec`, `optimizeWindow_equiv`
(re-proved against the finalized gate); `realizeA`/`symStep_sound_AVal`/
`symExec_run_AVal` (soundness over code-address stacks under the
`opExposed`-are-words hypothesis that a source run supplies); and
`wfProg_scheduleAsm` + `labelDefs`/`labelRefs`/`codeSize` preservation.

**The single remaining obligation** is the whole-program forward simulation
`scheduleAsm_asteps`/`_ahalt`, in the exact shape of
`Peephole.optimizeAsm_asteps`/`optimizeAsm_ahalt`:

```
scheduleAsm_asteps :
  [model : ExternalModel] → (labelDefs asm).Nodup →
  ASteps asm ⟨asm, [], y⟩ ⟨[], σf, yf⟩ →
  ASteps (scheduleAsm asm) ⟨scheduleAsm asm, [], y⟩ ⟨[], σf, yf⟩
scheduleAsm_ahalt :  -- the halting-run counterpart
```

This is a standard `steps_sim` over a `CodeRel`-style `SchedRel` on suffixes
(`window` pairs `w` with `optimizeWindow w`; `keep` for non-window instructions),
with a `Match` whose mid-window constructor carries the symbolic state `s_pre` of
the consumed prefix, the reached `AVal` valuation `ξ`, the invariant that the
source stack is `realizeListA yst ξ s_pre.stack ++ ξ.drop s_pre.inputs ++ REST`,
and that `opExposed s_pre` slots are words (accumulated as source op steps reveal
words). Control flow is clean (windows label/jump-free → `findLabel` preserved,
`StkRefs` carries over). At the window boundary the optimized side fires
`optimizeWindow w` atomically via `symExec_run_AVal` + `optimizeWindow_spec` + an
`AVal` mirror of `symStateEquiv_transform_eq`. All per-window mathematical
content is proved; what remains is the (substantial but standard) forward-
simulation assembly mirroring `AsmPeepholeSound`. Until it lands, do **not** merge
on the executor lemmas alone.

## 1. Definition changes

**Recommended (Option A — minimal surface): fold the stage into `compile`.**
Change `YulEvmCompiler.compile` (`Compile.lean` ~L344) from

```lean
let opt := optimizeAsm asm
```
to
```lean
let opt := Schedule.scheduleAsm (optimizeAsm asm)
```

i.e. `compile`'s body becomes exactly today's `compileScheduled` body. Then
**delete** the now-redundant untrusted entry points `compileScheduled`
(`Compile.lean` ~L357) and `compileObjectScheduled` (`ObjectCompile.lean` ~L898),
and the `compileScheduled` calls inside `compileResolvedObject`
(`ObjectCompile.lean` L856/L884) revert to `compile`.

Why Option A: `compileObject` (= `compileResolvedObject`) and
`compileObject_correct` already route through `compile` /
`compile_correct_withPayload`. Changing `compile` alone makes the scheduler
covered by *every* existing headline theorem automatically — no new entry point,
no duplicated correctness statement.

Rejected (Option B): keep `compile` unchanged, prove a separate
`compileScheduled_correct`, and switch `compileObject` to it. This doubles the
audited entry-point surface and the theorem set for no benefit.

## 2. Audited SPEC-surface changes (needs human code-owner approval)

This is a **real spec-surface change**, not a line-ref re-pin. Regenerate with
`lake env lean SpecClosure.lean` and get sign-off on:

- **`YulEvmCompiler.compile` definition hash** (`SPEC.md` L164, currently
  `49a8d9e93773bc82`) — the body changes. A human must re-approve that `compile`
  now contains a `scheduleAsm` stage whose behavior preservation rests on
  `scheduleAsm_asteps`.
- **`YulEvmCompiler.compileObject` definition hash** (`SPEC.md` L165,
  `45cacb379f48e375`) — changes transitively (its closure now reaches
  `scheduleAsm`).
- **New data-defs entering the audited surface**: `scheduleAsm`,
  `scheduleAsmFuel`, `optimizeWindow`, `symExec`, `symStep`, `pad`, `Term`,
  `SymState`, `symStateBeq`, `pureArity`, `windowGas`/`instrGas`/`opGas`,
  `schedulable`, and the untrusted `scheduleWindow`/`scheduleWindowReal`
  (+ `genValue`/`emit`/…). These become part of "what a human reads to trust the
  statements."

**Headline *theorem-statement* hashes do NOT change** (`compile_correct`,
`compile_correct_withPayload`, `compile_correct_eval`, `compileObject_correct`,
`compileObject_consistent`): SpecClosure walks statements, and the statements are
textually identical (they still quantify over `compile prog = some is`). The
*guarantee* is unchanged and now covers the scheduled code, because `scheduleAsm`
is proven behavior-preserving. That is exactly the property to communicate to the
code-owner: the theorems say the same thing; only the `compile` definition they
are stated about grew a proven-sound stage.

**Surface-stability recommendation (important given stage 3 churn):** the
untrusted scheduler internals (`scheduleWindowReal`, `genValue`, `emit`,
`emitCleanup`, …) affect nothing but the *candidate proposal*; the gate
re-validates every candidate. To stop stage 3's ongoing edits to those bodies
from re-pinning `SPEC.md` on every commit, expose `scheduleWindow` to
`optimizeWindow` through a boundary SpecClosure treats as an **artifact
signature** (type-only, body free — the mechanism already used for the 4 existing
artifact signatures). Then only `scheduleWindow`'s *type* is audited; its body
churns freely. Correctness already does not depend on the body.

No axiom-base change: `AsmScheduleSound.lean` uses only `propext`,
`Classical.choice`, `Quot.sound` (the pinned three in `Checks.lean`).

## 3. Theorems that consume `optimizeAsm_asteps`-style lemmas

Compose the new forward simulation *after* the peephole one in each:

- `compile_correct` (`Correctness.lean`): `optimizeAsm_asteps` at L136,
  `optimizeAsm_ahalt` at L164.
- `compile_correct_withPayload` (`Correctness.lean`): L222 and L250.
- `compile_correct_eval` (`Correctness.lean` L268) — reduces to the above; no
  direct change beyond what they inherit.

Pattern (normal case): today
```lean
have hstepsO := Peephole.optimizeAsm_asteps hnodup hsteps0     -- ASteps in (optimizeAsm asm)
... asteps_sim ... hstepsO ... (List.suffix_refl (optimizeAsm asm)) ...
```
becomes
```lean
have hstepsO := Peephole.optimizeAsm_asteps hnodup hsteps0
have hnodupO : (labelDefs (optimizeAsm asm)).Nodup := <optimizeAsm preserves nodup>
have hstepsS := Schedule.scheduleAsm_asteps hnodupO hstepsO   -- ASteps in scheduleAsm (optimizeAsm asm)
... asteps_sim ... hstepsS ... (List.suffix_refl (scheduleAsm (optimizeAsm asm))) ...
```
and every `optimizeAsm asm` in that branch (`hsmallO`, `hlen`, `ConfMatch`,
`suffix_refl`, `stackOK2_run_bound`, the `hcomp : lowerProg … = some is`)
becomes `scheduleAsm (optimizeAsm asm)`. The `hnodupO` premise is
`optimizeAsm`'s nodup preservation (already available:
`Peephole.optimizeAsmRound_nodup` iterated, or a `labelDefs (optimizeAsm asm)`
sublist of `labelDefs asm` via `codeRel_labelDefs_sublist`). The halting branch
uses `scheduleAsm_ahalt` symmetrically.

## 4. `stackOK2` gate ordering

No reordering needed — Option A already runs `stackOK2` on the **post-schedule**
program (`opt = scheduleAsm (optimizeAsm asm)`), so the proven overflow bound
(`StackScalable.run_stack_bound2`, via `stackOK2_run_bound`) covers the code that
actually runs. This matters because `scheduleAsm` *reschedules* operand-stack
traffic: it does not merely shrink usage, so the bound must be re-checked on the
scheduled code, which the gate placement does. The proof's `stackOK2_run_bound
hstk` now takes `hstk : stackOK2 (scheduleAsm (optimizeAsm asm)) = true` and is
about the scheduled program — consistent with the `hstepsS` above running in the
same program. No monotonicity assumption about stack usage is required.

## 5. Size / label invariants (which lemma form lowering needs)

Lowering (`lowerProg`) and the `labelWidth`-address-fit bound need
`WFProg (scheduleAsm (optimizeAsm asm))`. Provide it with `wfProg_scheduleAsm`
(proven) applied to `WFProg (optimizeAsm asm)` (from `Peephole.codeRel_wf` of the
optimize round on `WFProg asm`, itself from `wfCheck`). Concretely the proof
needs:

- **codeSize (≤ form, matching `codeRel_codeSize_le`)**: `codeSize_scheduleAsm_le
  : codeSize (scheduleAsm p) ≤ codeSize p`. Chain it for `hsmallO`:
  `codeSize (scheduleAsm (optimizeAsm asm)) ≤ codeSize (optimizeAsm asm)
   ≤ codeSize asm < 256 ^ labelWidth`
  (the last two are `codeSize_optimizeAsm_le` and `wfCheck …|>.small`). This is
  the exact form `hsmallO` (Correctness L126) consumes.
- **labels (equality, stronger than `optimizeAsm`'s sublist/subset)**:
  `labelDefs_scheduleAsm : labelDefs (scheduleAsm p) = labelDefs p` and
  `labelRefs_scheduleAsm : labelRefs (scheduleAsm p) = labelRefs p`. Because
  `scheduleAsm` neither adds nor drops labels (windows are label-free and rewrite
  to label-free code), `Nodup` and `refsDefined` transfer *directly* — a cleaner
  invariant than the peephole's, whose dead-label elimination only gives a
  sublist. `wfProg_scheduleAsm` packages all three.
- `lowerProg` success then follows exactly as for `optimizeAsm asm` today
  (`lowerFrag_length` for `hlen`, unchanged shape).

**Load-bearing gate check:** `codeSize_scheduleAsm_le` holds *only because*
`optimizeWindow`'s acceptance gate requires `codeSize cand ≤ codeSize w`
(`codeSize_optimizeWindow_le`). Weakening or removing that gate condition would
break the address-fit bound and hence lowering — flag it as a correctness-
critical part of the untrusted scheduler's *specification* (not its
implementation).

## 6. Anti-vacuity / CI

`scheduleAsm` keeps the original window on any doubt (gate rejects), so accepted-
program coverage cannot shrink versus today's `compile`. Ensure the differential
corpora that enforce anti-vacuity run against the new `compile` (they will
automatically once the def changes); confirm no fixture that previously compiled
now returns `none` (only possible via the `stackOK2` gate on rescheduled code —
watch for a window whose reschedule happens to raise peak stack; the gate would
then reject where it previously accepted, a coverage regression to catch in CI).
