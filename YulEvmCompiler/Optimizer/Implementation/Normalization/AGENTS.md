# Working in `Optimizer/Implementation/Normalization/`

Yul→Yul **normalization**: passes that put a program into a canonical *normal
form* (ANF, unique names, hoisted functions, empty `for`-init, flattened blocks),
plus the shared specification of what those normal forms are. Read the root
`AGENTS.md` "Adding a real optimization or normalization pass" section first.

## `NormalForm.lean` — the shared spec (start here)

`NormalForm.lean` (namespace `YulEvmCompiler.Optimizer.NormalForm`) defines each
normal-form property as an independent `Prop`-valued predicate over the raw
`{Op}`-generic AST, and bundles them into `structure Normalized (b : Block Op)`:

| field | property |
| --- | --- |
| `WellScoped` | every referenced var/function name resolves in scope (Yul scoping: block-hoisted functions, function bodies can't see outer vars, `for`-init leaks into cond/post/body) |
| `UniqueNames` | no name declared twice anywhere (full disambiguation) |
| `FunctionsHoisted` | all function defs at the root top level |
| `IsANF` | call/operand args are flat (atoms or a single flat call); `for`-condition exempt |
| `ForInitEmpty` | every `for`-init block is empty |
| `Flattened` | no bare `block` statements remain |
| `ControlWellPlaced` | `break`/`continue` only in loop bodies, `leave` only in functions |

Also `NormalizedObject` (object trees) and a standalone `NoDeadCodeAtLevel`
(reachability) kept *out* of the bundle. These predicates are purely syntactic
and `Prop`-valued on purpose — they carry no `Bool`-decider or `DecidableEq`
baggage and compose directly in theorem statements.

## The convention passes follow

Keep the properties à la carte. A pass:

1. **Requires** only the fields it depends on, as ordinary hypotheses —
   `theorem foo_pass (h₁ : NormalForm.UniqueNames b) (h₂ : NormalForm.IsANF b) …`.
2. **Re-establishes** the whole bundle as a postcondition —
   `NormalForm.Normalized (foo_pass.run b)` — proved field-by-field via the named
   projections (`.uniqueNames`, `.anf`, …).

This syntactic obligation is **orthogonal** to the semantic `Spec.Pass` /
`Spec.ObsPass` contract (soundness / `EquivBlock`). A finished pass proves both:
it preserves meaning *and* keeps the program in normal form so the next pass's
preconditions hold.

## Correspondence to the individual passes

Each `NormalForm` field is established by a dedicated normalization pass; several
are currently on unmerged branches (targeting `powdr-labs`) in *different*
namespaces, which `NormalForm` deliberately does not import:

- `IsANF` → **establishment landed**: `Normalization/ANF.lean` — `anfBlock P`
  flattens every operand to an atom (top operator kept with atomized args;
  `for`-conditions exempt) and `anf_isANF` / `anf_establishes_isANF` prove it
  reaches `NormalForm.IsANF` for every prefix `P`. Operand preludes follow Yul's
  right-to-left evaluation order, so it is soundness-ready, but the `EquivBlock`
  soundness (fresh-binding non-capture) is **not** yet proved — so ANF is not yet
  in `Pipeline.lean`. The heavy fresh-binding weakening on the old
  `anf-normalizer` branch (`ANFSound`) is the reusable foundation for that step.
- `UniqueNames` → **landed**: `Disambiguate/` (`Disambiguated` via `.Nodup`,
  bridged by `disambiguate_uniqueNames`; whole-program soundness
  `disambiguate_runEquivBlock` is *conditional* on assumed `SourceValid`
  facts — no Bool deciders yet, so not a `GlobalPass`; see
  `Disambiguate/Pass.lean` and the IDEAS.md entry for the upgrade paths)
- `FunctionsHoisted` → **landed**: `HoistFunDefsPass.lean` (`liftFunDefs` as the
  guarded `hoistFunDefsPass : GlobalPass`)
- `ForInitEmpty` → `hoist-for-init` (`ForInitOKs`, a *conditional* variant)
- `WellScoped` → `normalization-hoist-funcs` (`HoistFunDefsEquiv.lean`, functions
  only — the *function-call-scoping fragment* of `NormalForm.WellScoped`)

## `Normalize.lean` — the combined front-end (what the pipeline runs first)

`Normalize.normalize` / `normalizeObject` chain the landed steps in
precondition order — **disambiguate, then hoist functions** — and are what
`compileSource`/`Pipeline.lean` run *before* the optimizer. Soundness is
conditional on the disambiguator's assumed `SourceValid` (hoisting adds nothing):
`sourceValid_normalize_runEquivBlock` / `normalizeObject_objEquiv`. Running
disambiguation first is what makes the guarded hoister actually fire (unique,
well-scoped input).

`NormalizeNormalForm.lean` reconciles the duplicated notions against the
canonical spec and states the front-end's postcondition:
`uniqueNames_uniqueFunNames` (canonical `UniqueNames` ⇒ hoist's `UniqueFunNames`),
`wellScoped_callsScoped` (canonical `WellScoped` ⇒ hoist's call-scoping
`WellScoped`, with `funNamesTop_eq_funDefNames`), and `normalize_uniqueNames`
(the front-end establishes `NormalForm.UniqueNames`).

When the remaining passes land, the follow-up is: (a) prove each pass establishes
its `NormalForm` field, adding a `↔ isANFStmts = true`-style bridge to the Bool
deciders, and prove `normalize` establishes `FunctionsHoisted` (needs
`Bool`-completeness of `wellScopedB` plus disambiguation preserving
`NormalForm.WellScoped`); (b) finish unifying the duplicated name/scope
collectors (the uniqueness and well-scopedness bridges above are the first
installments). Two `NormalForm` choices are **stronger** than today's passes on
purpose — `ForInitEmpty` demands a literally empty init (not "empty when
simple"), and `IsANF` recurses into function bodies (the ANF pass leaves them
un-normalized). They are the target to raise the passes to, not a description of
current behavior.

## Style notes

- Predicates are `{Op : Type}`-generic (the AST is parameterized by the bare
  operation type, not a `Dialect`). No `DecidableEq` is needed.
- Recursion over the AST uses explicit `…Stmt`/`…Stmts`/`…Cases`/`…Dflt` mutual
  helpers (not inline `flatMap`/`map` with the recursive call in a lambda) so the
  structural termination checker stays happy — follow that pattern.
- Type-check a single file without a full build: `lake env lean <file>`.
