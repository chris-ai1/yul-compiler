# Optimizer ideas log

A running log of Yul→Yul optimizer passes we have tried, are trying, or might try.
Each pass is a value of `Optimizer.Pass` (`Spec/Pass.lean`): a total
`run : Block → Block` bundled with `Sound D run : ∀ b, EquivBlock D b (run b)`.
Possessing a `Pass` *is* possessing a verified optimizer — soundness is the only
proof obligation, and it composes with the verified backend via
`Pass.optimize_then_compile_correct` (`Spec/Backend.lean`).

The goal is to reduce **runtime gas** of contracts compiled by this compiler.
The gas harnesses (see `AGENTS.md`) compile solc's *fully unoptimized* IR (or the
Yul corpora directly) and compare against solc's *optimized* output, so there is
a lot of structural slack to remove.

## Framework facts worth knowing before adding a pass

- `Optimizer/Core/Basic.lean` provides the first typed optimizer boundary:
  intrinsically scoped ANF values and arity-indexed pure operations. Successful
  ingestion erases exactly to its Yul input; unsupported, nested, effectful, and
  call syntax remains outside Core, and `Simplify` leaves it unchanged to keep
  the public pass total. `Core/Rule.lean` supplies a generic first-match engine
  whose rules carry their own `EquivExpr` proofs. `Simplify` now uses that path
  instead of retaining a second raw-AST rewrite driver.
- `Core/Subst.lean` provides closed-term instantiation of Core parameter
  contexts (`Term.substEmit`) plus the functional reflection `valueEval` of
  `Step` on value-shaped expressions — the β machinery behind the helper
  inliner. `Spec/Observe.lean` adds the **observational tier** (`ObsPass`,
  `ObsEquivBlock` over committed run observables, memory/`msize`/final-`VEnv`
  quantified away) with the strong tier embedded and the backend payoff
  restated; use it for passes `EquivBlock` cannot express (dead bindings,
  scratch memory), pending a human decision to admit it into the audited roots.
- `EquivExpr`/`EquivStmt`/`EquivStmts`/`EquivBlock` are pointwise big-step
  equivalences with congruence lemmas in `YulSemantics.Equiv`. Local expression
  rewrites lift through `builtin_congr`/`call_congr` and the statement
  congruences.
- Pure EVM ops (`add sub mul div sdiv mod smod addmod mulmod exp signextend clz
  lt gt slt sgt eq iszero and or xor not byte shl shr sar`) reduce via `stepOp`
  to `some (.ok [f args] st)` — **state-independent value, state unchanged**. This
  is exactly what makes constant folding and neutral-element rewrites sound.
- Algebraic identities are only sound when they **keep the operand on the RHS**
  (both sides then require the same variables to be bound). `add(x,0) ≈ x` is
  sound; `mul(x,0) ≈ 0` is **not** (RHS does not require `x` bound, so it differs
  on environments where `x` is unbound — `EquivExpr` quantifies over *all* envs).
  See the note in upstream `YulSemantics.Rewrites`.
- `EquivBlock.of_stmts` needs `hoist b₁ = hoist b₂`. Rewriting *inside a `funDef`
  body* changes `hoist`, so it is **not** liftable by the upstream congruences —
  there is no `funDef`-body congruence upstream (explicitly deferred). We prove
  that missing **function-environment congruence** locally in
  `Implementation/FunCongr.lean` (`FunsRel` + `Step.funs_congr` +
  `EquivBlock.of_stmts_funs`); it lets a pass rewrite inside `funDef` bodies and
  is the reusable foundation for every future pass that does so.
- Object path: `RunObject o L = Run evm o.codeBlock L.initState`, so an
  `EquivBlock` on a code block lifts to object behavior *under a fixed layout*.
  But optimizing a **sub-object** whose compiled byte length changes shifts
  `datasize`/`dataoffset` and therefore the layout `compileObject` produces — so
  the object path needs a length-stable argument or a cross-layout relation. Top
  code-block optimization under a fixed layout is the safe first step.

## Gas targets (which baseline a pass can move)

- `test/solidity-yul-optimizer-gas-baseline.txt` — `yulOptimizerTests`, ~552 rows,
  **644/651 fixtures block-rooted** → moved by a top-level `Block` pass through
  the `compile` (block) path. **Biggest, easiest target.**
- `test/solidity-yul-evm-code-transform-gas-baseline.txt` — `evmCodeTransform`,
  ~40 rows, mostly block-rooted (smaller, stack-transform oriented).
- `test/solidity-yul-object-compiler-gas-baseline.txt` — `objectCompiler`, mostly
  object-rooted → needs the object path.
- `test/solidity-gas-baseline.txt`, `test/solidity-semantic-gas-baseline.txt` —
  real `.sol` via solc `--via-ir`, object-rooted → needs the object path.
- `measureGas` runs the compiled bytecode *directly* (no deploy), so a block
  pass's savings show up immediately in the two Yul block-rooted baselines.

## Passes

### ✅ Full normalization front end (`Normalize.normalize`) — landed

`Normalize.disambiguate` renames every declared name (let-bounds, params,
returns, function names) to a globally fresh `NUL`-prefixed counter name, so no
two declarations in a root block share a name (`Disambiguated` /
`NormalForm.UniqueNames`). `sourceValidB` now decides all source-validity
preconditions; `disambiguateGuarded` is the identity when the guard fails, so
`disambiguatePass` is an unconditionally sound `GlobalPass`.

`Normalize.normalize` then runs the verified guarded function hoister, producing
`NormalForm.FunctionsHoisted`. Both steps are applied to every code block in an
object tree. `normalize_runEquivBlock`, `normalizeObject_objEquiv`, and the
composed `normalize_optimizerPipeline*` theorems are unconditional: no
`SourceValid` assumption survives at the public boundary. The remaining work is
performance/preservation of the full seven-field `NormalForm.Normalized`
bundle, not soundness of this landed front end. The main performance follow-ups
are pruning unreachable definitions and grouping the hoisted function section
to avoid a separate backend skip island for every retained definition.


### ✅ Dominance-local stack layout (`codex/swapmath-stack-layout`)

`SwapMath.sol` exposes two related failures after the existing smart layout:
the ABI wrapper materializes four call results in a multi-binder and then
copies them to four return slots, requiring `SWAP17`; after removing that
cliff, the exact-output branch evaluates
`getNextSqrtPriceFromOutput(current, liquidity, amountOut, zeroForOne)` with a
return address, return slot, and one pending argument above `amountOut`,
requiring `DUP17`.

The planned fix uses the same placement principle as dominator-tree/SSA work:
place a carrier at the lowest program point that dominates all of its uses.
For this local rewrite that point is the call statement itself, represented by
a fresh nested block, so the carrier live ranges cannot leak into the function
frame.  This is a structured-region specialization, not a claim that the pass
constructs a general CFG dominator tree: loops, early outcomes, and hoisted
functions still follow Yul's explicit syntax.  A backward syntactic
mention analysis supplies the local interference test.

The implementation grew into coordinated, verified rewrites in one
stack-layout pass:

1. **Multi-result copy-back coalescing.** Recognize the exact adjacent vector
   `let t₁…tₙ := f(as); d₁ := t₁; …; dₙ := tₙ` and retarget the call directly
   to `d₁…dₙ := f(as)`.  The rewrite handles singleton and multi-binder
   results; requires distinct, disjoint temporaries and destinations already
   bound at the site; and requires full read/write/declaration mention-freedom
   of every temporary in the suffix.  Adjacency is deliberate: textbook
   live-after alone cannot justify moving destination writes across arbitrary
   effects.  This removes the wrapper's four temporary slots.
2. **Right-to-left call-argument staging.** When the backend pressure model
   predicts a `DUP17+` while evaluating a direct **assignment-form** call,
   evaluate arguments once, right-to-left, into globally fresh carriers in a
   nested block, then call using the shallow carriers.  The call site is the
   lowest common dominator of those carrier uses; block restoration kills every
   carrier on normal and halt outcomes.  Let-form calls are not staged because
   predeclaring their results would change the environment on argument halts.
   The policy fires only when every staged evaluation and the final
   multi-assignment fit classic `DUP16`/`SWAP16`.  Call-bearing arguments are
   admitted only with a general proof that prepending the generated block's
   empty function scope preserves lookup and execution.

Soundness stays in the existing strong `Pass` tier.  Copy-back uses `MIns` and
`InsFree`: the source carries dead temporary bindings through the suffix while
the target does not, and enclosing `restore` erases the difference in both
directions, including halts.  Argument staging proves an `EvalArgs`
decomposition/recomposition lemma, preserving Yul's right-to-left order,
exact arity, state changes, and halts; globally fresh names make environment
   extension observationally inert.  One-rewrite drivers keep both proofs local.
3. **Dominance-local live-range splitting and slot reuse.** Backward liveness
   and syntactic declaration dominance identify acyclic block/conditional/
   switch regions where dead locals can be scoped away or a deep live value can
   be carried in a fresh shallow slot. Nested refinements descend through the
   already-generated dominator chain. Stable reads are split first; a second
   reverse-postorder pass prefers a writable deep value, keeping both the call
   input and result destination within `DUP16`/`SWAP16` in SwapMath.

The executable order is scheduling, adjacent copy-back to a fixed point,
early dead scoping, tail scoping, slot reuse, dominance-local splitting and
available-copy forwarding, then pressure-triggered staging against the final
layout. Its pressure traversal threads loop-init declarations and the init's
hoisted function-signature scope into the condition, post, and body.
The public pass first runs the established layout and retains it whenever that
program already compiles; the aggressive pipeline is selected only when the
legacy layout still hits a stack cliff. This preserves bytecode and gas for the
previously supported fragment while extending acceptance.
Function-body congruence is handled by `FunCongr`; a structural resolution
congruence lifts the pass over every object code block without changing object
names, data, or the audited specification.

Primary references: T. Lengauer and R. E. Tarjan, “A Fast Algorithm for
Finding Dominators in a Flowgraph,” TOPLAS 1(1), 1979,
<https://doi.org/10.1145/357062.357071>; R. Cytron et al., “Efficiently
Computing Static Single Assignment Form and the Control Dependence Graph,”
TOPLAS 13(4), 1991, <https://doi.org/10.1145/192030.192041>.

Result at this pass's landing: both block and object compilation paths used the
pass; the proof covers copy-back, argument evaluation and halts, nested acyclic
regions, function environments, and generated nested shadow scopes. The strict
Uniswap suite compiles 13/15 contracts and runs 39 comparable external-call
scenarios with no behavioral or gas regressions. `PoolLiquidity.sol` and
`SwapMath.sol` leave the exact known-failure set; SwapMath's
`computeSwapStep(uint160,uint160,uint128,int256,uint24)` is now exercised.
At that point, `PoolSwap.sol` remained blocked by five reads of the same
result-memory pointer across loop branches (the first needed `DUP21`), while
`PoolManager.sol` remained the larger integrated frontier. Supporting those
loop-carried regions needs a
separate control-flow proof rather than weakening this acyclic-region pass.
The full build, exact axiom guard, and unchanged audited specification closure
pass.

### ✅ `identity` (`Implementation/Identity.lean`) — landed
The do-nothing pass; validates the spec is inhabited. Sound by reflexivity.

### ✅ `FunCongr` (`Implementation/FunCongr.lean`) — landed (this branch)
The **function-environment congruence** upstream defers: `FunsRel` (related
function environments — equal signatures, `EquivBlock` bodies), `Step.funs_congr`
(a `Step` transports across `FunsRel`), and `EquivBlock.of_stmts_funs` (block
congruence that lets the hoisted scope change). Enables optimizing inside `funDef`
bodies. Reusable by any future pass.

### 🚧 `Simplify` (`Implementation/Simplify.lean`) — IN PROGRESS (this branch)
A local **constant-folding + neutral-element** expression simplifier that
recurses through the whole program, **including function bodies** (via
`FunCongr`). Only a `for`-loop's `init` is left untouched (it is both executed
and hoisted; changing it needs a `for`-specific congruence — see below).

- **Constant folding**: `builtin op args` with every arg a literal and `op` pure
  → replace with the literal `number (v.toNat)` where `v = f (args.map litValue)`.
  One uniform soundness lemma over the pure-op set (result value is a total
  function of the literal args, state unchanged).
- **Neutral-element identities** (operand is a `var`, kept on the RHS):
  `add(x,0)`, `add(0,x)`, `sub(x,0)`, `mul(x,1)`, `mul(1,x)`, `div(x,1)`,
  `or(x,0)`, `or(0,x)`, `xor(x,0)`, `xor(0,x)`, `and(x,MAX)`, `and(MAX,x)`,
  `shl(0,x)`, `shr(0,x)` → `x`. Collapsed to two parameterized lemmas
  (`[var,lit]` and `[lit,var]`) discharged by a per-identity `stepOp` reduction.
- **Wiring**: inserted into `compileSource`'s block branch (`compile (P.run …)`);
  soundness is `Pass.optimize_then_compile_correct`.
- **Constant control flow**: after expression simplification, literal `if`
  conditions select the body/empty block and literal `switch` conditions select
  the matching case/default block.
- **Target**: `solidity-yul-optimizer-gas-baseline.txt` (+ evmCodeTransform).
- **`for`-loop `init`**: left untouched. `init` is executed *and* hoisted into the
  loop's scope, and upstream `EquivStmt.forLoop_congr` fixes it. A `for`-specific
  congruence (init changes with a `ScopeRel` side condition, like
  `of_stmts_funs`) would let us reach it — small follow-up.

### ✅ `ObjectPass` + `simplifyObject` — object path WIRED (this branch)
`simplifyObject` (in `Simplify`) runs the pass on **every** code block of an
object tree — the deploy object *and* every nested sub-object (the `*_deployed`
runtime of a Solidity artifact). It is wired into `compileSource`'s object branch,
so **both deploy and runtime code are optimized**. Soundness (`ObjectPass`):
`simplifyObject_compileObject_correct` (the artifact is the verified compilation
of the optimized tree, via `compileObject_correct`) + `simplifyObject_topEquiv`
(every object's top code block is `EquivBlock`-equivalent to the original, via
`blockEquiv`). So the bytecode faithfully runs a program each of whose code blocks
is provably equivalent to the source.

**Full end-to-end soundness** (`simplifyObject_correct`): compiling
`simplifyObject o` yields bytecode that correctly simulates the **original**
object `o`'s resolved run under the compiler's layout — the object analogue of
`Pass.optimize_then_compile_correct`, with **no caveat**. The bridge is the
**resolution congruence** `ResolveCongr.resolveSimplifyBlock_equiv`:
`EquivBlock (resolveForLayoutStmts L b) (resolveForLayoutStmts L (simplifyStmts b))`
— proved by a structural induction using that expression rewrites are disjoint
from `dataoffset`/`datasize`, the pass never manufactures a string literal, and
resolving switch cases commutes with selecting a literal case.

Gas (real Solidity contracts, `checkSolidityGas`): `libsolidity/semanticTests`
619/648 down (−185,438 gas); `libsolidity/gasTests` 12/12 down; `objectCompiler`
3 down. All zero-regression.

`Pass.optimizeTopCode` + `Pass.optimizeTop_compileObject_correct` remain as an
alternative single-object theorem for the offset-free/leaf fragment.

### ✅ Constant control-flow folding (`agent/optimizer-control-flow`)

Extend `Simplify` with bottom-up folding of control flow whose condition becomes
literal after expression simplification:

- `if 0 { body }` → an empty block;
- `if <nonzero literal> { body }` → `body` as a block; and
- `switch <literal> ...` → the selected case/default as a block.

This removes the condition dispatch and, more importantly, all unreachable
branch bytecode.  It is distinct from the copy-propagation/dead-`let` work in
PR #52 and directly targets existing constant-control-flow fixtures in the Yul
optimizer and EVM code-transform gas suites.

Soundness is local and exact: invert the source `if`/`switch` big-step rule,
use literal evaluation to rule out the untaken `if` arm or fix the switch value,
and reconstruct the chosen block execution in both directions.  These local
equivalences compose after the existing expression/body congruences, including
the function-environment relation for rewritten function bodies.  The object
path additionally uses the structural fact that resolving a selected switch
block equals selecting from the resolved cases; this preserves
`resolveSimplifyBlock_equiv`, so the existing whole-tree object correctness
theorem continues to cover both deploy and runtime code.

Gas results are zero-regression: 9 `yulOptimizerTests` fixtures improve by
2,292 total gas, 2 `evmCodeTransform` fixtures improve by 240, and 11 real
Solidity `semanticTests` contracts improve by 15,400.  The largest local wins
are literal switches (up to 408 gas in the Yul scenarios); all solc fingerprint
columns are unchanged.  The curated Solidity `gasTests` and `objectCompiler`
rows are unchanged.

## The layout-coupling (why the end-to-end object theorem is subtle)

`planObject` derives every sub-object/data **offset** from the top code block's
compiled `codeSize`, and `resolveForLayoutStmts` bakes those offsets into the code
as `PUSH32` literals. Consequences (verified against the code, see the analysis
that produced `ObjectPass`):

- Optimizing code that any `dataoffset`/`datasize`/`datacopy` observes **shifts
  the layout** (`L → L'`). There is **no `EquivBlock`-congruence for resolution**,
  and none is generally provable (folding reads the offset immediates), so a raw
  `EquivBlock` on the code block does **not** lift across resolution to two
  different layouts.
- Sound optimization is clean **only** when the top block makes no layout
  references (`ObjectPass`'s `hres₀`/`hres₁`).
- Real solc output nests a **constructor** object (whose top code `datacopy`s the
  runtime — not offset-free) around the **runtime** sub-object (where execution
  gas is spent). Optimizing the runtime shifts the constructor's baked offsets;
  optimizing the constructor is offset-*ful* at the top. So neither the "top code
  only" nor the "leaf" fragment reaches real-contract runtime gas.

To move `solidity-gas`/`solidity-semantic` (object-rooted, the real solc
comparison) we need one of: (a) a **cross-layout object equivalence** relating the
offsets an optimization shifts (major); or (b) restructuring `planObject` to apply
the pass *after* resolution and recompute `codeSize` from its output (breaks the
current fixed-width-`PUSH32` layout fixpoint for offset-sensitive passes). This is
the real object-path frontier.

### ✅ `Propagate` — constant propagation, binding-preserving (this branch)

**Forward substitution of known bindings, keeping every binding in place.** After
`let x := <number literal>`, later reads of `x` (until invalidated) become the
literal; `let x` (no initializer) yields `x ↦ 0` (Yul zero-initializes); at
`x := <literal>` with `x` already tracked, the entry is *refreshed*
(σ-membership proves `x` is bound, so `VEnv.set` really updates) — capturing
solc's reassignment chains (`ssaPlusCleanup/multi_reassign.yul`). A
fold-at-let step (reusing `pureFold`) collapses literal chains in one
traversal, so copy chains rooted at a constant collapse too. (Bare *copy*
entries `y ↦ x` are proven sound but disabled in production — see the depth
lesson below.) Invalidation is syntactic and
conservative: shadowing lets, assignments (key *and* rhs-source of copy entries),
and, per construct, the assigned/declared sets of nested bodies; loops rewrite
cond/body/post under a σ pruned by the loop's whole write set (invariant by
construction); `funDef` bodies restart at σ = ∅ (fresh callee env).

**Why sound in the unchanged pointwise spec** (where binding *removal* died,
PR #52): the kept `let` guarantees the variable is bound to the known value in
every execution reaching the use site, on both sides — no stuckness asymmetry,
no well-scopedness assumption. Invariant: `Compat V σ` (each entry's key is bound
and agrees with its rhs). One bidirectional `Step` simulation, with `FunsRel`
(`FunCongr`) for rewritten function bodies.

**Object path without weakening**: soundness is proven for a *relation*
`PropRel σ ss ss'` (transform rules + skip alternatives; pruning mandatory), with
`propStmts` inhabiting it. Since resolution maps number literals and vars to
themselves and only rewrites `dataoffset`/`datasize` string-calls *into* number
literals, `PropRel` is closed under `resolveForLayoutStmts` by a purely syntactic
induction — the skip rules absorb resolution-created literals. So the object
pipeline gets the **full** pass (no `litOK`-style restriction), and the whole-tree
correctness theorem extends stage-wise as before.

**Why it pays**: vars are stack slots (read = DUP = 3 gas, literal = PUSH = 3 gas),
so each substitution is gas-neutral until the existing `Simplify` folding /
constant-control-flow folding / `InlineHelpers` fire — then folded sites save
~6 gas each, folded branches remove dispatch + dead bytecode, inlined calls save
~25+ gas. Corpus: 558 literal-lets (347 safe + 78 refresh-recoverable), ≥26
baseline fixtures with concrete fold unlocks, and the pervasive solc `let _N := 0`
idiom (also all over real via-IR output → object-rooted baselines). Substitution
also relieved the DUP16 depth limit (deep var reads failed to compile at that
stage).

**Pipelines**: block `[simplify, propagate, inline(litOK), simplify]` (propagate
first feeds the literal-friendly inliner); object
`[simplify, inline(var-only), propagate, simplify]` (inline first — propagation
would turn var args into literals and starve the var-only object inliner).

Known non-targets (left in this list): LICM, full inlining of multi-statement
helpers, block flattening — these dominate the largest remaining gas-ratio rows.

**Results** (with `DeadLits` below; re-pinned, zero regressions everywhere,
cumulative): `yulOptimizerTests` 179 rows −10,300 gas; `evmCodeTransform` 16
rows −840; Solidity `gasTests` 12/12 rows −1,733; `semanticTests` **534 rows
−616,030** plus **81 contracts that newly compile**; `objectCompiler` 1 row
−18. All solc columns unchanged; the axiom gate is clean.

### ✅ `DeadLits` — dead literal-binding elimination (this branch)

The removal companion: delete a singleton `let x := <literal>` (or zero-init
`let x`) whose variable never occurs afterward in its block — exactly the
leftovers `Propagate` creates, and exactly the removable class that needs **no
spec change**: a literal binding always evaluates, changes no state, and its
binding dies at the enclosing block's `restore` anyway, so the pointwise iff
holds with no `WellScoped` assumption (contrast PR #52, whose *arbitrary*-rhs
removal genuinely needed the rejected spec weakening — its `Frame.lean`
toolkit, `InsAt` with depth-from-the-bottom indexing plus
`frameAdd`/`frameRemove`, is salvaged verbatim as the semantic core here).
Soundness: the skip-rule relation `DlRel` (same architecture as `PropRel`;
closed under layout resolution, so the object path gets the full pass), with
removal steps discharged by `removeLit_equivBlock` — sequence split at the
binding, frame simulation across the insertion, `restore` alignment
(`restore_insAt_le`) — chained under an arbitrary common prefix, and kept
steps by the pointwise congruences. Wired as the final stage of both
pipelines. Each removed binding saves its PUSH+POP and **frees a stack
slot** — 81 real `semanticTests` contracts that used to die at the DUP16
limit now compile.

**The copy-propagation depth lesson** (measured the hard way): *copy* entries
(`y ↦ x`) are proven sound end-to-end — the relation, both simulations, and
the resolution closure all cover them — but the production transform creates
**literal entries only**. Substituting a copy replaces a read of a recently
bound (stack-shallow) variable with a read of an older (deeper) one, and this
backend's variable reads are `DUP`s hard-limited at depth 16: with copies
enabled, solc's `dispatch_*.sol` gasTests stopped compiling. Literal
substitution can only relieve depth (a literal is a `PUSH`, and folded sites
shrink expression stacks). Re-enabling copy entries behind a depth analysis
(only propagate copies whose source provably stays within `DUP16` at every
use site) is a logged follow-up; any future substitution-based pass must run
this same check.

### ✅ `InlineCalls` — statement-level inlining of call-free helpers (this branch)

**The dominant remaining gap is function-call protocol overhead.** The verified
backend's call protocol costs ≈ `24 + 2·|args| + 6·|rets|` gas per call (PUSH32
ret-addr, zeroed ret slots, jumps, JUMPDEST, param pops, ret rotation, dynJump,
+11 for `leave`), and solc's unoptimized IR routes every external call through
~15 tiny helpers (`external_fun_*` → `abi_decode_tuple_*` → `abi_decode_t_*` →
`validator_revert_*` → `cleanup_*`, `fun_X` → `fun_Y` wrappers, `zero_value_*`,
`revert_error_*`). Measured on the Uniswap v4 suite: `UnsafeMath.sol` ours
780 gas/tx vs solc 154 — ~75–85 % of the gap is call protocol + copy-`let`s.
solc's FullInliner collapses all of it; our `InlineHelpers` only inlines
single-*expression* bodies (var-only on the object path).

The pass inlines *statement-level* calls (`let xs := f(as)` / `xs := f(as)` /
`f(as)`) to functions whose body is **call-free** (no `.call` anywhere — the
body's execution is then independent of the function environment, killing all
closure/scope-resolution obligations), has **no
loops/funDefs/leave/break/continue** (`if`/`switch`/nested blocks fine; one
trailing `leave` allowed and dropped), and is **binder-aware well-scoped**
within `params ∪ rets` (a soundness condition, not hygiene: inlining an
ill-scoped body converts callee stuckness into caller execution). Replacement
(let-form): `let xs` then
`{ let rs (zero-init); let pₙ := aₙ; …; let p₁ := a₁; { ss }; x₁ := r₁; … }` —
the inner env is exactly `callOk`'s `params.zip argvals ++ bindZeros rets`, the
`{ ss }` wrap mirrors the call's body-block `restore`, arg evaluation stays
right-to-left, and per-site conditions (`(vars(as) ∪ xs) ∩ (ps ∪ rs) = ∅`,
`vars(as) ∩ xs = ∅` for let-form, `xs.Nodup`, exact arities) rule out the
capture/stuckness asymmetries. `for`-init sites are skipped (as in `DlRel`).
Helper chains collapse leaf-first by iterating the pipeline (a call-free
callee inlines this round, making its caller call-free for the next round).

Soundness: PropRel-style skip-rule relation `IcRel Δ` (Δ = syntactic decl map
from enclosing hoisted scopes; original decls, so `lookupFun funs₁ f` matches
Δ syntactically), fwd+bwd `Step` simulations with two new semantic tools:
`Step.funs_irrel` (call/funDef-free code ignores the function env) and
`Step.append_frame` (scoped weakening: well-scoped code runs identically with
an arbitrary caller env appended below — `frameAdd`'s mention-freeness cannot
work here since the caller env is arbitrary; shadowing-aware well-scopedness
is the right condition). Halt-in-body leaves the site's temporaries on the env
until the enclosing block's `restore` — a prefix generalization of DeadLits'
`ResRelAt`, confined to the `.stmts` class. Object path: `IcRel` is closed
under layout resolution (`dataoffset`/`datasize` are *builtins* in this AST,
so resolution never changes the call count; all classification conditions are
resolution-invariant), giving the full pass on object code, no litOK-style
weakening. Transform-only heuristics (skip rules absorb them): a size bound
and a live-local depth guard so aggressive inlining does not push callers past
the backend's DUP16/SWAP16 hard limit (see the known-compile-failures lists).

**Results** (fully proven, no sorries, axiom gate clean; pipelines iterated
6 rounds; transform-only guards `rets ≤ 2` and `liveMax ≤ 10` plus a
compile-fallback in `compileSource` — optimized program first, unoptimized if
the backend rejects it — so stack-pressure blowups cannot cost coverage):
`semanticTests` **842 rows −3,354,775 gas, zero regressions**; `gasTests`
12/12 rows −15,874 (e.g. `exp.sol` 3,576 → 2,700, `dispatch_large.sol`
92,572 → 88,362); Uniswap v4 6/6 rows −4,823 (`UnsafeMath.sol` 3,900 → 2,908,
`BitMath.sol` 6,186 → 4,902, `SafeCast.sol` 6,509 → 5,442);
`yulOptimizerTests` ~57 rows −16k; `evmCodeTransform` 6 rows −1,668;
`objectCompiler` 2 rows −240. All solc fingerprint columns unchanged.

Proof lessons for future passes: the **`scoped_transfer` engine** (one
induction giving funs-irrelevance + scoped weakening over an arbitrary
appended environment + the normal/halt outcome restriction for the checked
fragment) is reusable for any pass that relocates code between environments;
the **backward let-form reduction** (after the zero-init runs, a `let`-site
is exactly its assign-form site, so the backward simulation reuses the
`siteAssign` relation one statement in — no two-level induction needed); and
inlining bodies are inserted *unchanged* (call-free bodies contain no sites),
so `Δ` entries always match `lookupFun` on the source side syntactically.

Follow-ups logged, not in v1: bodies containing calls (needs Δ-compat across
closures), arg substitution instead of `let p := a` copies (capture/depth),
`InlineHelpers` litOK upgrade via a skip-rule relation (would inline
literal-bodied expression helpers — `shr(224, v)`, address masks — on the
object path; also unblocks chain collapse for non-uint256 cleanup types and
would let more `validator_revert_*` chains collapse), the
`if iszero(eq(x,x)) {halt-body}` → `pop(x)` validator residue, copy-chain
cleanup (`let _2 := var_x; let expr := _2` residue is now the dominant
remaining cost — copy propagation behind a depth analysis), and smarter
guards (whole-caller live-local analysis instead of the per-callee bound).

## Candidate next ideas

### ✅ Memory spilling for residual stack pressure ([#81](https://github.com/powdr-labs/yul-compiler/pull/81))

The production compiler now uses guarded memory spilling as its final fallback
after every existing compilation candidate fails.  It chooses bindings from
actual backend stack-pressure failures, keeps tuple bindings all-or-none,
colors fixed 32-byte cells across lexical lifetimes and the non-recursive call
graph, and rewrites selected definitions, reads, assignments, parameters,
returns, calls, loops, and control exits to `mstore`/`mload`.  A consistent
literal `memoryguard(n)` reserves the spill interval; `msize`, recursion,
malformed signatures, invalid selected-binding scopes, partial tuple groups,
and missing or inconsistent guards reject safely.  Existing successful
candidates still run first, so their bytecode and gas are unchanged.

The approved specification is deliberately guarded rather than an
unconditional strong optimizer pass.  `GuardedRun` and plan-indexed
`PlannedTopRun`, together with `GuardedExternals`, state the memoryguard scratch
contract.  The simulation relates source and rewritten states outside the
reserved interval and covers every source `Step` constructor, block scope
restoration, function calls and return copy-back, and recursively planned
object compilation.  The composed block and object backend theorems check with
no `sorry`, new axioms, `unsafe`, trust-boundary edits, or spec re-pinning.

`PoolSwap.sol`, `stackLimitEvader/function_arg.yul`, and
`stackLimitEvader/tree.yul` now compile.  The strict Uniswap and Aave gas suites
and all CI differential/gas shards pass without changed existing gas rows.
`PoolManager.sol`, `HubOperations.sol`, `LiquidationLogic.sol`, and
`SpokeOperations.sol` remain exact known failures because they reach separate
unsupported `gas`, immutable, or live-linker behavior after guarded pressure is
removed; `SpokeOperations.sol` also has an independent unguarded pressure site.
Those are follow-up features rather than unfinished memory spilling.

### ✅ `StackLayout` — expression scheduling and liveness-guided slot reuse ([#61](https://github.com/powdr-labs/yul-compiler/issues/61))

Treat block-local Yul bindings as virtual stack registers and color their
live ranges onto the existing local slots.  At a singleton `let y := e`, a
dead, reachable local `x` may be reused by emitting the source-level equivalent
`x := e` and consistently renaming the remainder of `y`'s live range to `x`.
The allocation policy is separate from the semantic mechanism. It searches
earlier block-owned slots that remain within `DUP16`, rejects any whose value
is live in the suffix, and runs only as a compilation fallback. This keeps the
common successful case byte-for-byte stable while compressing large solc IR
frames that otherwise fail at `DUP16`/`SWAP16`.

The all-live case needs scheduling rather than coalescing. Yul evaluates call
arguments right-to-left, so a left-associated `add` fold accumulates pending
right operands before reaching its oldest variable. The pass right-associates
addition spines: the leaf order is still exactly right-to-left, including for
state-changing and halting expressions, but pending-operand pressure becomes
constant. This is proved directly against `EvalExpr`, not assumed from purity.

A third rule handles a control-flow lifetime cliff at function tails. If a
singleton carrier declaration dominates a region ending in `result := e;
leave`, and the intervening locals are dead after that write, the region moves
into a nested block and writes `e` to the carrier. Block restoration then pops
the dead frame before a shallow `result := carrier` copy. The policy checks the
entry/result depths, declaration liveness, initializer freshness, and absence
of directly hoisted functions; the proof covers normal, early-control, and
halting executions in both directions.

The proof is a bidirectional `Step` simulation over a slot-renaming relation on
variable environments.  The overwritten value is unobservable because the
chosen slot is dead; the original environment's extra binding and the reused
environment agree on every renamed live variable; declarations and assignments
preserve that relation; and the enclosing block's `restore` erases the local
layout difference.  The transform is conservative around shadowing,
multi-value declarations, function boundaries, loop-carried values, and
  non-local control until their side conditions are proved. The implementation
  is an ordinary strong `Pass`; unsupported multi-value coalescing remains a
  later extension rather than an unproved acceptance path.

**Result:** issue #61's exact nine-local reproducer compiles and executes
differentially. The strict Uniswap v4 suite improves from 6/11 to 10/11:
FullMath, SqrtPriceMath, TickBitmap, and TickMath are newly accepted; SwapMath
remains a conservative rejection. Existing successful artifacts are unchanged
because the pass is fallback-only, yielding zero gas regressions; the four
newly comparable gas rows are pinned.

### ✅ Depth-aware copy propagation + scoped pure DCE + open-operand identities (this branch)

Issue #64, informed by the post-#63 dumps: after `InlineCalls`, the dominant
remaining cost is copy/rename residue (`let _2 := var_x; let expr := _2`),
dead parameter/result copy bindings, and one-open-operand identities
(`or(0, e)`, the `InlineHelpers` fence `add(f(…), 0)`) that gate further
inlining rounds. Three coordinated changes, one branch:

1. **Copy facts in production `Propagate`** behind a per-scope live-locals
   depth gate (mirroring `liveMaxStmts`): the relation side (`classify`,
   `PropRel`, both simulations, resolution closure) already covers `.var`
   facts; only `classifyProd`/policy threading changes. The resolution
   congruence transports a frozen relation instance, so the gate heuristic
   needs no resolution stability. `dispatch_*` (large frames) is the
   regression target the gate must protect.
2. **`DeadPure`** — DeadLits generalized to dead singleton `let y := rhs`
   where `rhs` *always evaluates in context*: literals, `bound`-vars
   (params/rets via the call rule's `callOk` env, plus earlier binders), and
   pure-total builtin trees over those. Proof: PropRel-style relation
   `DcRel bound` + bidirectional Step simulation carrying `BoundOK` and a
   multi-insertion generalization of `InsAt`; block-exit `restore` erases
   the extra bindings, keeping the strong `Pass` tier (no ObsPass).
3. **Open-operand neutral identities in `Simplify`** at the expression layer
   (outside Core): `add/sub/or/xor(e,0)`, `add/or/xor(0,e)`, `mul/div(e,1)`,
   `mul(1,e)` for arbitrary `e` including calls — the literal operand is
   total/stateless, `e` evaluates once on both sides. Rewriting the fence
   `add(f(…),0) → f(…)` re-exposes statement-level calls to `InlineCalls`,
   unblocking the `read_from_storage → extract → shift_right` chains in the
   top loop fixtures.

**Results after rebasing onto the smart-stack-layout main** (fully proven, no
sorries, axiom gate clean): on the 846 `semanticTests` rows shared with main,
**781 improve, none regress, −2,138,102 gas net**, and the regenerated combined
baseline contains **288 additional rows** (1,134 total). `gasTests` improve 12/12,
−3,855 total (`exp.sol` 2,700 → 2,352, `dispatch_large.sol` 88,362 → 87,677);
Uniswap v4 improves 10/10, −130,707 total (`TickMath.sol` 1,008,056 →
884,353, `UnsafeMath.sol` 2,908 → 2,434); the Yul optimizer corpus improves 27
rows, −2,941 total. At that stage, `SwapMath` remained the sole strict
Uniswap rejection.

Also on this branch: `compileSource` now combines its **light one-round
pipeline** (`optimizerPipeline*Rounds` generalization) with main's verified
smart stack layout. It tries the full pipeline, smart layout of that result,
the light pipeline, smart layout of the light result, and only then the
unoptimized source. Iterated inlining can push a caller past DUP16; this graded
ladder converts that cliff into a small gradient without losing the layout
fallback added by PR #68.

Also completed on this branch: a proved **call-site result freshening** pass
(`x := f(a)` → `{ let t := f(a); x := t }`, globally fresh `t`) removes the
common caller-result/callee-name collision before `InlineCalls`; the copy/DCE
passes consume its temporary. The gate is recomputed per block, and the
inlining live-local bound is 12. Argument-side shadowing and call-bearing
arguments remain deliberately unfreshened until their environment-extension
proof is available.

Findings for the follow-ups, from the post-branch dumps:

- **Argument-side collisions remain** where an argument reads a callee
  parameter/return name or itself contains a call. Extending freshening to
  hoist arguments right-to-left would unlock more of the remaining loop gap,
  but needs the stronger environment-extension proof for nested calls.
- **Gate granularity**: the per-function `copyGate` disables copy facts in
  large caller frames — precisely where iterated inlining lands its residue
  (visible in `fun_run` of `calling_other_functions.sol`). Per-enclosing-
  block gating or a per-fact lexical-window analysis is the second
  iteration; the gate is a parameter, so the relation is untouched.
- Dead non-self assignments, multi-binder lets, and dead `funDef` removal
  remain logged follow-ups (value-desync needs a different relation);
  whole-caller-aware `inlineOK` would recover the one softened regression.

### ✅ Dead read-only result regions (`codex/dead-region-dce`)

Post-#67 dumps of the three dominant dynamic-array fixtures show that call-site
freshening succeeds: their hot push loops are call-free.  The newly exposed
residue contains an adjacent zero-initialized result and nested computation
block whose result is never read:

```yul
let ignored
{
  // Inlined read_from_storage / extract / cleanup chain.
  let word := sload(slot)
  ...
  ignored := value
}
```

solc removes the entire readback.  Ours still executes a warm `sload` plus
shift/mask and stack scaffolding on every push iteration.  This is present in
all of `array_storage_length_access`, `array_storage_push_empty_length_address`,
and `array_storage_push_pop`, which together retain roughly 27.9M of the
post-#63 semantic gap and remain the highest-leverage measured target after
#67.

The `DeadResults` pass removes exactly an adjacent `let x` + block
when `x` is unmentioned in the remaining sequence and a scope-aware checker
proves that the block:

- always terminates normally and preserves the exact `EvmState`;
- reads only variables known bound at that point;
- writes only `x` or non-shadowing locals declared earlier in the region; and
- uses only singleton lets/assignments, nested blocks, exact-arity pure
  builtins, and deterministic state-preserving reads (`sload`, initially).

Calls, control flow, stores, memory-touching reads, Keccak, copies, layout
operations, `gas`, and every open-world operation are rejected.  The explicit
total-operation whitelist is intentional: the dialect effect flags alone do
not prove arity/totality, and `mload`/Keccak can change active memory.

Soundness stays in the strong `Pass` tier.  It is a contextual block theorem,
not a false standalone statement equivalence: the source executes the harmless
region and carries one inserted, possibly updated dead binding through the
`x`-free suffix; the enclosing block's `restore` erases that binding and
recovers exact `VEnv` equality.  The proof extends the `Frame`/`DeadPure`
simulation in both directions, recurses conservatively through all sub-blocks,
and proves structural layout-resolution closure for the object path.

State-read CSE and store-to-load forwarding are deliberately separate follow-
ups: they require alias/effect invalidation across stores, calls, control-flow
joins, and static-context halts.  Measure this directly evidenced rule first;
only add small cleanup needed to expose or consume more instances of the same
dead-result shape.

The final change also adds `HoistCalls`, the smallest argument-normalization
needed by the observed storage-cleanup chain: an assignment shaped
`x := f(g(args))` becomes a block-local fresh binding for `g(args)` followed by
`x := f(fresh)`. It fires only when both helpers pass `InlineCalls`' existing
stack-pressure gate and the inner arguments are call-free. This preserves the
exact evaluation order and lets the following freshen/inline stages consume
both sites; broader argument splitting remains a separate follow-up.

Measured on top of PR #67, the two passes improve 152/859 comparable semantic
fixtures with no regressions: **130,608,997 → 110,331,250** total gas
(−20,277,747), moving the aggregate ratio from **1.3390× to 1.1311×**.
The three dominant dynamic-array rows fall by 9,017,190, 9,482,520, and
884,962 gas respectively. The compiling Uniswap subset improves
23,889 → 23,700 (−189); its five stack-depth failures remain a separate
stack-compression target.

### ❌ Right-to-left call-argument splitting (measured, rejected)

Post-`DeadResults` dumps show that the remaining helper graph is often blocked
by a named call nested as an argument of another expression.  The hottest pop
chain contains, for example:

```yul
sstore(slot, update_byte_slice_dynamic32(sload(slot), offset, converted))
```

`InlineCalls` can consume the `update_byte_slice_dynamic32` helper once it is a
direct singleton call site, but cannot classify its caller as call-free while
the call remains under `sstore`.  That in turn keeps `storage_set_to_zero` and
`array_pop` out of line on every loop iteration.

A prototype generalized `HoistCalls` to split a minimal call-bearing argument
suffix into fresh singleton locals in Yul's right-to-left evaluation order.
Combined with the existing inliners it improved many fixtures, but also caused
36 small gas regressions from extra temporary stack traffic. Its aggregate gain
was modest compared with the storage-specific opportunity below, so the pass
was dropped rather than adding a broad normalization with a mixed gas result.

### ✅ Literal-slot storage value forwarding (`codex/expression-splitter`)

Post-`DeadResults` output made the remaining dominant array cost more precise.
After a dynamic-array length update, the inlined bounds-check path reloads the
same literal storage slot even though the just-written value is a cheap
literal, variable, or `add(variable, literal)` expression. This occurs inside
the hot loops of issue #65's three largest array fixtures.

`StorageForward` keeps a small cache from literal slot keys to those replayable
value shapes. A potentially aliasing store clears all old facts before adding
one exact fact; stateful expressions, calls, switches, and loops are barriers;
assignment kills values that depend on the assigned variable. A conditional
may preserve its incoming facts only when its condition is total and storage
neutral and its body is syntactically unable to complete normally. Loop post
and body blocks are optimized independently, so no fact crosses an iteration.
Regions containing unresolved `dataoffset` or `datasize` are unchanged; this
makes the pass resolution-congruent on the object compilation path.

The proof is a bidirectional big-step simulation carrying explicit variable-
binding and cache-validity invariants. It covers normal execution and every
halt/control outcome, lifts through nested function bodies and loop regions,
and has a separate layout-resolution congruence for object compilation.

Measured on top of the `DeadResults` branch, the semantic Solidity suite
improves 15/859 comparable fixtures with no regression: **110,331,250 →
109,038,844** total gas (−1,292,406), moving ours/solc from **1.13114× to
1.11789×** and removing 10.1% of the remaining aggregate gap. The three
dominant array rows improve by 384,930, 386,810, and 411,814 gas respectively
(−1,183,554 combined). The current Uniswap library scenarios are unchanged;
their remaining gap is dominated by arithmetic/stack layout rather than
persistent-storage reloads.

### ✅ Scoped storage-fact propagation (`codex/storage-scope-forward`)

Post-`StorageForward` output removes the reload immediately following a
literal-slot store, but the three dominant array loops still contain one warm
reload of the same slot through nested inliner scaffolding. The value travels
through a return slot and block-local copy before becoming an outer variable:

```yul
let expr {
  let length
  { length := sload(0) }
  expr := length
}
// Later nested push logic reloads slot 0 instead of reusing expr.
```

The previous pass intentionally dropped every cache fact at block exit and did
not establish facts from assignments. The extension treats these as one scoped
dataflow feature:

- `x := sload(literalKey)` establishes `literalKey ↦ x`;
- `x := cheapValue` rebinds structurally equal cached values to `x`, allowing
  facts to follow inlined return-slot copies; and
- block exit filters facts depending on direct block-local declarations, then
  exports the remainder across Yul's `restore`.

All existing aliasing, stateful-expression, control-flow, loop-iteration, and
layout-resolution barriers remain. Assignment facts are gated by `BoundOK`, so
an ill-scoped assignment whose `VEnv.set` would be a no-op cannot create a
fact. Rebinding compares the pre-assignment value before invalidating old
dependencies (covering `x := add(x, 1)`) and keeps literal facts as literals.
The block proof carries a declaration frame: the body environment is direct
locals over a key-preserving update of its entry environment, so filtering
dependencies on exactly those locals makes cache validity survive `restore`.

Measured on top of the first `StorageForward` change, the semantic Solidity
suite improves **20/859** comparable fixtures with no regression:
**109,038,844 → 107,663,034** total gas (−1,375,810), moving ours/solc from
**1.11789× to 1.10378×** and removing another **12.0%** of the remaining
aggregate gap. The three dominant array rows improve by 409,500, 411,500, and
438,100 gas respectively (−1,259,100 combined), each losing the targeted hot-
loop `sload`. The curated gas suite and current six compilable Uniswap scenarios
are unchanged with no regression; Uniswap remains orthogonal to PR #68's stack
work. Layout congruence, adversarial shadowing/unbound/rebinding guards, and the
bidirectional pass proof all type-check without changing the trust boundary.

### ❌ Dead-let lifetime shortening after `InlineCalls` (`dead-let-pop`)

Issue #64 is the right companion to `InlineCalls`, but directly enabling copy
substitution remains unsafe for this stack backend: replacing a recent copy by
an older source can turn a compiling `DUP16` into an unreachable `DUP17`.
The first production slice instead shortens dead binding lifetimes without
substitution.  A dead singleton initialized binding

```yul
let x := e
```

whose `x` is not mentioned by the rest of its block becomes

```yul
pop(e)
```

while the existing `DeadLits` cases still delete dead zero/literal bindings
entirely.  Keeping `e` under `pop` preserves its evaluation, effects, halt,
arity check, and unbound-variable stuckness under the unchanged pointwise
`EquivBlock` spec; removing the binding ends its operand-stack lifetime at the
declaration rather than at block exit.  This targets dead parameter/result and
copy scaffolding exposed by `InlineCalls`, may bring optimized programs back
under `DUP16`, and cannot deepen any remaining variable read.

Proof plan: add a bidirectional `let`/`pop` execution lemma, reuse the existing
`InsAt` frame simulation for the mention-free suffix, extend `DlRel` with a
guarded replacement rule, and transport it through object layout resolution
using the existing identifier-occurrence invariance.  The existing iterated
block/object pipelines then pick up the stronger stage without a spec change.
Measure all `dispatch_*` gas tests, the six compiling and five rejected Uniswap
fixtures, and the high-gap semantic cases before deciding whether the next
slice should be depth-aware copy facts or broader pure-expression deletion.

**Result:** fully implemented and proved experimentally, then rejected. The
curated `gasTests` had six regressions and no improvements: each
`dispatch_small*`/`medium*` row rose by 2 gas and each `dispatch_large*` row by
4. Moving the eventual block-exit `POP` to the declaration executes it on halt
paths where the old cleanup was unreachable. The proof/code was removed; the
measurement confirms lifetime shortening needs a profitability analysis, not
an unconditional rewrite.

### ✅ Self-equality validator residue (`if-self-eq`)

`InlineCalls` exposes Solidity validator guards of the form

```yul
if iszero(eq(x, x)) { <halt body> }
```

The condition is false whenever `x` is bound, but replacing the whole statement
by an empty block is unsound under pointwise `EquivStmt`: it would also run when
`x` is unbound. Replace it with a value discard that retains evaluation of the
original condition (and therefore the same stuckness) while removing the dead
branch dispatch and unreachable body. A later strengthening may reduce the
discard to `pop(x)` once that expression equivalence is packaged cleanly.

Proof plan: invert successful evaluation of `iszero(eq(x,x))` to show its sole
value is zero, then prove the conditional equivalent to discarding that exact
condition in both normal and halt cases. Extend `simplifyCond`, show the pattern
is stable under object layout resolution, and keep only zero-regression gas
improvements.

**Results** (fully proved in the unchanged strong `Pass` spec, object-resolution
congruence included): `semanticTests` 199/846 rows improve by **19,230 gas**
with zero regressions (`calling_other_functions.sol` −75; the top three
dynamic-array loops −90/−105/−90); curated `gasTests` 11/12 improve by
**1,125** with every `dispatch_*` row down; Uniswap v4 improves BitMath,
SafeCast, and UnsafeMath by **315** total. The Yul optimizer corpus newly emits
`fullSuite/abi2.yul` (456 gas), previously beyond the optimized backend's stack
frontier; its other 552 rows, all 23 object-compiler rows, and all 40
EVM-code-transform rows are unchanged. No solc fingerprint moved and no known
failure baseline changed.

### ✅ Scoped fact export across block exits (`optimizer/propagate-scoped-export`)

Issue #65's 2026-07-25 refresh showed the Aave `PositionStatusMap` hot loops
dominated by inliner readback scaffolding: shapes like

```yul
let x
{
    let z
    {
        z := 0
    }
    x := z
}
y := x
```

never folded because `Propagate` discarded **every** tracked fact at nested
block exit (`prune σ (writeSetStmts body)` from the *entry* environment).
Constants established inside a readback block died immediately, so
`DeadPure`/`DeadResults` had nothing to consume, helper bodies stayed above
the shared `liveMax ≤ 12` gates, and the hot helpers
(`getBucketWord`/`isBorrowing`/`isUsingAsCollateral`) never shrank or inlined.

The `.block` case of `propStmt` now threads the body's own **final**
environment out of the block, pruned of the block's direct locals
(`blockDecls`, the shared shallow scan formerly `StorageForward.declaredStmts`;
`MemorySpill.declaredStmts` is an unrelated deep scan, and its two
`MemorySpillSelect` uses are now explicitly qualified after a near-miss silent
re-resolution). This is the value-fact analog of the already-landed
"scoped storage-fact propagation": facts about outer variables — including
ones established or refreshed *inside* the block — survive exactly the
bindings `restore` removes. `PropRel.blockS` gains a `BlockExitRel` choice
(`skip` = the old conservative exit, `exportFacts` = the scoped export), the
simulation is proved with the same `ScopeFrame` block-framing argument
`StorageForward` uses (that machinery now lives in `Propagate.lean` and is
shared), and the resolution closure extends with `blockDecls_resolveStmts`
because resolution rewrites expressions, never binder lists. No spec change,
no new axioms.

A second, deliberately proof-free change follows from measurement: the export
turns whole *groups* of adjacent readback regions dead within one round, but
`deadResults` removes at most one region per statement sequence per
invocation. In `various/code_length_contract_member.sol` that pacing race
left two dead **cold `sload` regions** alive after six rounds (+4,171 gas,
the only regression in the first measurement; rounds 7–9 drained them one
per round). The round stage lists now run the verified `deadResults` stage
three times back-to-back, draining up to three regions per sequence per
round. `LocalPass` composition makes this free of new proof obligations.

**Results** (all four real-Solidity suites, solc 0.8.35, corpus `902f848`,
against the pre-pass baselines; zero regressions anywhere):

- **Aave v4: 53,889,601 → 47,918,164 (−5,971,437; all 10 rows improve).**
  `nextContinuousTenThousand` −2,524,464, `nextBorrowing…` −1,265,970,
  `nextCollateral…` −1,265,970, the two count scans −426,567/−426,567,
  `constants()` −10,504, `flsFullRange` −42,215. The Aave excess over solc
  falls 16.7%.
- semanticTests: 134,881,267 → 134,383,334 (−497,933; 1,005/1,237 rows
  improve, 0 regress — the pacing fix flipped the one interim regression).
- Uniswap v4: 1,950,079 → 1,778,850 (−171,229; 38/44 rows improve — the
  triple `deadResults` alone contributed −64,286).
- Curated gasTests: 485,175 → 483,580 (−1,595; 11/12 improve).
- `PositionStatusMap` runtime bytecode: 93,144 → 86,508 bytes (−7.1%);
  whole-object statement count −19%.
- Soundness gates: sorry scan, `Checks.lean` axiom footprint, `SpecClosure`,
  SPEC.md, YulIR round-trip, all three compile corpora (no new or stale
  failures), and the Yul interpreter suite all pass.

Remaining hot-loop cost (visible in fresh dumps): plain copy chains
(`let a := b` at the same level) are still gated off by `copyGate` in fat
bodies, the retained helpers still pay the call protocol in the inner loops,
and `let x { x := e }` declare-then-assign pairs whose value *is* read remain.
The natural follow-ups are generalized stack-aware inlining and
loop/state-aware dataflow, both of which now start from much smaller bodies.

### ✅ Adjacent copy-chain coalescing (`optimizer/aave-gas-next`, PR #111)

Post-#107 dumps of Aave `PositionStatusMap` show the next bottleneck plainly:
427 of the 1,033 optimized bindings are pure variable copies
(`let a := p  let b := a  let c := b`), 75% with a source that dies at the
copy — the statement inliner's parameter/readback scaffolding. Each copy
costs a `DUP` plus a live operand-stack slot inside 10,000-iteration loops,
and the extra live locals hold `isBorrowing`/`isUsingAsCollateral`/
`getBucketWord` above the shared `liveMax ≤ 12` gates, which keeps both
gated copy propagation and `InlineCalls` shut — the residual deadlock from
the issue #65 refresh.

`CoalesceCopies` merges the adjacent pair `let x := rhs; let y := x` to
`let y := rhs` when `x` is not mentioned afterwards (plus the zero-init
variant `let x; let y := x` → `let y`), sweeping left-to-right so whole
chains collapse in one invocation. Unlike copy *substitution* — the known
`DUP16` hazard that motivated the depth gates — binder forwarding removes a
live slot and never deepens any read, so it needs **no profitability gate**.
The stage runs between `simplify` and `deadPure` in both round lists.

Soundness is deliberately cheap: `rhs` evaluates identically on both sides,
and afterwards the source carries exactly one extra dead `(x, v)` binding
per merged pair — a single `InsAt` insertion, transported through the
mention-free suffix by the existing `frameAdd`/`frameRemove` frame lemmas
and erased by the enclosing block's `restore` (`InsChain.restore_eq`; every
statement sequence in the semantics runs under a block, including `callOk`
bodies, so the insertion never outlives its sequence and never reaches a
return readout). Scope changes lift with `FunCongr`'s
`EquivBlock.of_stmts_funs`; the object path is a *syntactic commutation*
with layout resolution (resolution creates literals, never bare variables,
so the pass fires at identical sites — `resolve_coalesceCopiesBlock`).
No spec change, no new axioms.

**Results** (vs the PR #107 baselines, solc 0.8.35, corpus `902f848`; zero
regressions on all 1,303 comparable rows):

- **Aave v4: 47,918,164 → 38,749,156 (−9,169,008, −19.1%; ratio 2.628x →
  2.125x; all 10 rows improve).** `nextContinuousTenThousand`
  18,666,506 → 14,315,572 (−4,350,934), `nextBorrowing…` −1,780,147,
  `nextCollateral…` −1,860,139, the count scans −576,463/−568,223,
  `constants()` −4,936, `flsFullRange` −18,296.
- semanticTests: 134,383,334 → 134,078,455 (−304,879; 348 rows improve).
- Uniswap v4: 1,778,850 → 1,703,107 (−75,743; 18/44 rows improve).
- Curated gasTests: unchanged (dispatch fixtures have no such chains).
- `PositionStatusMap` copies 427 → 120; bytecode 86,508 → 86,192 bytes;
  TickMath bytecode 34,459 → 34,336. PoolSwap's object is byte-identical:
  it still compiles through a fallback path, untouched by the pipeline.
- Gates: sorry scan, axiom footprint, `SpecClosure`, SPEC.md, interpreter
  suite, all three compile corpora, and the YulIR round-trip all pass.

Remaining hot-loop cost after coalescing: the loops still *call* the (now
much slimmer) helpers each iteration, keep the `iszero`-normalization
readbacks and checked-decrement panic blocks, and the helpers still redo the
scratch `mstore`/Keccak/`sload` address setup per call. The chain heads
(`let a := param`) also remain, one per collapsed chain. Next levers, in
issue #65's terms: recommendation 4 (the hot helper bodies should now fit
under `inlineOK` after another look at the gate arithmetic — check
`liveMaxStmts` on the post-coalesce bodies), then recommendation 5
(keccak/sload CSE and loop-invariant scratch setup).

### ✅ Hot-helper inline unlock + adjacent expression rejoining (`optimizer/aave-gas-3`, PR #117)

Two coupled changes finishing what #107/#111 started on issue #65's Aave rows.

**Gate 13.** Post-coalescing dumps put `isBorrowing`/`isUsingAsCollateral` at
`liveMax` exactly 13 — one over `InlineCalls`' ≤ 12 gate — stalling the
cleanup cascade one level from the hot loops. Raising the gate to 13 inlines
them (transform-only; gates never affect soundness): Aave −2,312,574 with
zero regressions everywhere including the full semantic suite; 14 adds
nothing on any suite.

**`RejoinPairs`.** With the helpers inline, the loops are chains of adjacent
single-use pure pairs (`let x := and(w, 1); let y := iszero(eq(x, 0))`) —
the "expression rejoining" half of recommendation 3. The pass merges
`let x := e; let y := f(…x…)` to `let y := f(…e…)` when the consumer is a
pure-total tree with exactly one `x` whose other leaves are literals or
**sequence-locally bound** variables, `x` is dead afterwards, `e` is
call-free, and the merged tree stays under an operand-depth budget
(`rjDepthLimit = 8`). Swept left-to-right, whole producer chains fold back
into expression trees, each merge removing a live stack slot and a `DUP`
from 10,000-iteration loops — and lowering `liveMax` further.

Three measured hazards shaped the guards:

- rejoined **calls** hide from `InlineCalls` (the `fls` fixtures regressed
  +3k until `e` was restricted call-free);
- rejoining merges the bindings the smart stack layout re-slots, which
  pushed `PoolLiquidity` off its `full+layout` rescue onto the light
  pipeline (+22k over four rows). Depth caps did not help; the fix is a new
  **full-pipeline-without-rejoin (+ layout)** candidate pair in
  `compileSource`'s fallback chain, which exactly recovers the old quality
  on stack-frontier objects;
- an outer-scope `bound` set is **not pointwise-sound** for the
  compositional (`EquivStmt` + `of_stmts_funs`) lifting — only variables
  declared by earlier `let`s of the *same sequence* are bound in every
  execution reaching the pair, so each sequence starts from an empty bound
  set. Almost nothing is lost: the consumer trees' sibling leaves are
  overwhelmingly literals.

Soundness follows `CoalesceCopies`' insertion skeleton: `e` evaluates at
the identical configuration on both sides (everything evaluated before the
consumed leaf is stateless and insertion-invariant), and afterwards the
source carries one dead `(x, v)` binding per merged pair — one `InsAt`
insertion through the mention-free suffix, erased by the enclosing block's
`restore`. Producer-halt runs are reconstructed with `dcEvalRun` from the
sequence-local bound set. The object path uses the `StorageForward` recipe
taken one step further: the transform is guarded by whole-block
`storageLayoutFreeStmts` and *preserves* it, so resolution is the identity
on both input and output and the RPass congruence is the pass's own
soundness. No spec change, no new axioms, no sorrys.

**Results** (vs post-#111 main, solc 0.8.35, corpus `902f848`; zero
regressions on every comparable row):

- **Aave v4: 38,749,156 → 35,808,661 (−2,940,495, −7.6%; all 10 rows).**
  Gate alone −2.31M; rejoining −630k on top.
- Uniswap v4: 1,703,107 → 1,640,265 (−62,842; 13/44 rows improve).
- semanticTests: −10,555 net (20 rows improve from the gate, 93 minus
  overlaps from rejoining), zero regressions on 1,264 rows.
- Curated gasTests unchanged.
- Cumulative since the issue refresh: Aave 53.89M → 35.81M (**−33.6%**,
  ratio 2.955x → 1.964x).

Remaining after this: the loops still pay one call per remaining fat helper
(`next`'s 3-return shape stays behind the `rets ≤ 2` gate), the duplicated
scratch `mstore`/keccak/`sload` group per iteration is now fully exposed
inline (recommendation 5's CSE, which needs value numbering with copy
tracking — note the DUP16 hazard analysis in the PR: value reuse at
distance needs backend/stack-layout support, not another rewrite pass),
and `PoolSwap` still compiles only through the spill fallback (all four
ordinary candidates fail), keeping its 417 KB bytecode and 706 definitions
out of the optimizer's reach entirely — likely the single biggest Uniswap
bytecode lever.

### 🚧 Aave/Uniswap gas 4: available-value reuse + dead-definition pruning + optimize-after-spill (`optimizer/aave-uniswap-gas-4`)

Three coordinated changes attacking the largest post-#117 Aave/Uniswap costs
(issue #65). Fresh ranking: Aave 35.81M vs 18.24M (1.96x) — the three
`next*TenThousand` rows plus the two count scans hold ~15.9M of the 17.6M
excess; Uniswap 1.64M vs 0.91M (1.81x) — TickMath sweeps ~343k excess,
PoolSwap ~218k, the ~25 small library rows ~1.5k each vs solc's ~250.

1. **`ReuseValues` — scoped available-value forwarding (state-read CSE).**
   Post-#117 dumps of the Aave hot loops show the fully inlined
   `mapping_index_access` group duplicated per iteration:
   `mstore(0, key); mstore(0x20, slot); let h := keccak256(0, 0x40);
   let w := sload(h)` — once for `isBorrowing`, once again (same key/slot)
   for `isUsingAsCollateral`, ~150 gas of keccak+warm-`sload` per inner
   iteration that solc CSEs away. A scoped cache tracks (a) **scratch-cell
   facts** `mstore(lit, shape)` (shape = var/literal), (b) **available
   state-reads** `keccak256(l₁,l₂) ↦ x`, `sload(k) ↦ x` with *symbolic* keys
   (extending `StorageForward`'s literal-only keys), and (c) **available pure
   expressions** over vars/lits (TickMath's repeated mask/shift trees). An
   `mstore` rewriting a cell with a value the cell-fact already proves equal
   is *kept* but does not invalidate (no store elimination — that is PR
   #84/#116 territory); any other memory writer, call, or loop boundary
   kills memory-dependent facts; `sstore` kills `sload` facts; assignment
   kills facts mentioning the variable. A second occurrence of an available
   expression becomes a var read (`let h₂ := h`), which `CoalesceCopies`
   then merges. Soundness: the `StorageForward`/scoped-export architecture —
   bidirectional Step simulation carrying cache validity ("evaluating the
   cached expression now yields the cached variable's value and preserves
   state" — the first evaluation already extended active memory, so
   re-evaluation is state-preserving), with the same block-exit export and
   layout-resolution closure.
2. **`PruneDefs` — unreachable function-definition removal.** Full
   normalization hoists every definition to the root and the backend emits a
   `PUSH32 skip; JUMP; …; JUMPDEST` island per definition (~12 gas per
   retained definition per call). After six inline rounds the artifacts
   retain almost all definitions (`PositionStatusMap` 150 vs solc 19,
   TickMath 177 vs 2, SafeCast ~68 vs 0) — for the small Uniswap library
   rows the dead-island tax is over half the row. On
   `UniqueNames + FunctionsHoisted` output, compute transitive
   call-reachability from the non-`funDef` root statements and drop uncalled
   root definitions. Soundness: a hoist-shrinking congruence — execution
   under a function environment with extra entries whose names occur nowhere
   in call position in the remaining program is pointwise equivalent
   (`Step.funs_irrel`-style invariant threaded through the run); resolution
   closure is syntactic (resolution never creates named calls).
3. **Optimize-after-spill.** `PoolSwap` (and every future spill-only object)
   compiles through `spillObjectWithFallback raw …`, which uses **raw
   unoptimized code** at spilled nodes — 706 definitions / 417 KB never see
   the optimizer. Run the object pipeline on the spilled result (ladder:
   optimized-spilled first, plain spilled as fallback), composing
   `compileObject_memorySpill_correct` with the pipeline's fixed-layout
   resolution congruence — the pipeline preserves the spilled block's exact
   semantics, so `ScratchRel`/observable equality transport unchanged.

Measured expectations: (1) is the multi-million Aave lever (rows 1–3, 5–6);
(2) is a broad fixed-cost win (small Uniswap/Aave rows, gasTests' +114k
normalization regression, bytecode size); (3) opens PoolSwap's 218k excess
to (1)+(2). The `rets ≤ 2` inline gate is *not* the current `next*` blocker —
their bodies contain `for` loops, which the statement inliner's classifier
rejects outright; loop-bearing inlining stays a non-goal here.

**What the dumps forced (mid-implementation redesign):** the duplicated
keccak/sload groups sit 4–5 inliner-readback blocks deep, and *every* useful
carrier (the hash, the word, even the `shr(7,·)` key) dies at a nested block
exit before the second group starts — no fact-forwarding pass can connect
them at any single level, and the same nesting is what starves
`CoalesceCopies`/`RejoinPairs` of adjacent pairs. Two structural passes were
added ahead of `ReuseValues`:

* **`Flatten`** — splices bare inliner blocks into the parent sequence,
  renaming *all* promoted binders to globally fresh names (`FreshenCalls`
  prefix scheme). Unconditional renaming makes the splice's mention-freeness
  hold by construction; the rename declines on shadowed or pre-decl-mentioned
  binders. Runs right after `InlineCalls`.
* **`FuseDeclAssign`** — sinks `let x; …(x-free)…; x := e` declarations to
  their first assignment and fuses `let x := lit; x := e`; converts the
  flattened assign-chains back into `let`-chains so `CoalesceCopies` and
  `RejoinPairs` can consume them.

All three (plus `ReuseValues`) are guarded by whole-block
`storageLayoutFreeStmts` on input **and output** (post-checked, falling back
to the input), so each object-path congruence reduces to the pass's block
soundness — no commutation proofs. `PruneDefs` commutes syntactically instead
(call names are resolution-invariant) and is **fully proved**
(`PruneDefsSound.lean`: the hoist-shrinking congruence — `PFunsRel` upper
segment of filtered scopes over a common tail, call-`R`-freeness invariant,
`reachFuel` closure with an everything-live fuel-exhaustion default;
`PruneDefsResolve.lean`: the commutation). The optimize-after-spill wiring
also skips the pipeline when the plain spilled object cannot compile, and
adds a stack-layout rung for the optimized-spilled candidate (this is what
admits PoolSwap).

**Measured (transforms complete; three soundness stubs remain —
`flattenBlock_sound`, `fuseDeclAssignBlock_sound`, `reuseValuesBlock_sound`):**

| Suite | Before | After | Δ | Ratio |
|---|---:|---:|---:|---:|
| Aave v4 | 35,808,661 | 27,330,370 | **−8,478,291 (−23.7%)** | 1.964x → 1.499x |
| Uniswap v4 | 1,640,265 | 1,277,046 | **−363,219 (−22.1%)** | 1.808x → 1.408x |
| gasTests | 483,580 | 404,348 | −79,232 | 1.436x → 1.200x |
| semanticTests | 195,793,881 | 186,959,210 | −8,834,671 | 1.146x → 1.094x |

All 10 Aave rows improve (`nextContinuousTenThousand` −3.18M); 43/44 Uniswap
rows improve — PoolSwap finally compiles through the optimizer
(`swapExactInputNoTick` 138,059 → 68,021) with one small `slot0` +993
counter-move; 12/12 gasTests; 1246/1264 semantic rows improve, 12 regress by
a combined ~13k (worst `dynamic_multi_array_cleanup` +9k — flatten/reuse live
-range extension in copy-heavy code; accepted pending a gate follow-up).

**Proof state — all four passes fully proved (zero sorries):**

* `PruneDefs` — done (`PruneDefsSound.lean`, `PruneDefsResolve.lean`).
* `fuseDeclAssignBlock_sound` — done (`FuseDeclAssignSound.lean`): the
  `MvRel` environment-reorder relation and its algebra, the 40-constructor
  `Step.mv_congr`/`mv_congr_bwd` transports, `sink`/`fuseSeqFuel`
  inversions, the `FuseChain` move-or-insert accumulation erased by the
  enclosing `restore`, and the structural lifting.
* `flattenBlock_sound` — done (`FlattenSound.lean`): the `RnRel` keyed
  single-binder rename transport (forward, and backward via the
  rename-involution role swap), the guard decomposition
  (`shadowedTop`/`mentionsBeforeDecl` → an unchanged prefix and a
  redeclaration-free suffix), the splice as a multi-insertion frame chain
  (`frameAddAll`/`frameRemoveAll` over `InsChain`, new surviving keys ⊆
  top-level binders, empty-scope transparency from `StackLayoutSound`),
  and the counter-threaded structural lifting.  Freshness is **checked**
  by the transform (`stmtsMentions` guards in `renameAll`/`spliceSeq`, the
  `RejoinPairs` recipe) instead of derived from a prefix-string invariant;
  the checks never fire in practice and gas is unchanged.
* `reuseValuesBlock_sound` — done (`ReuseValuesSound.lean`): a functional
  evaluator for the canonical pure fragment with `Step` totality/
  determinism bridges, cache validity (`RvOk`) over the five fact
  families, `MemNeutral` state transitions (`touchMemory` idempotence at
  active ranges), the word/byte decomposition keystone (equal covering
  `loadWord`s force equal `readBytes`, via byte-fold injectivity), the
  per-rhs rewrite transports and post-binding validity, and the
  `StorageForward`-shaped master inductions.  The proof surfaced and fixed
  four transform gaps: self-referential recordings (`let x := sload(x)`),
  assignment facts for unbound names (`bound` threading, `VEnv.set` is a
  no-op on unbound names), literal-address wrap-around (range guards on
  `mstoreLit`/`mloadLit`/`keccakLits`), and cache retention across a
  non-canonicalizable (possibly effectful) `sload` key.
* The optimize-after-spill wiring is covered by the existing composed
  correctness chain (`Checks.lean` pins the exact classical axiom set of
  `compile_correct`; the whole tree is sorry-free).

## Candidate next ideas (not started)

### 🚧 Aave/Uniswap gas 5: trial-gated copy propagation + strength reduction + literal-helper object inlining (in progress — PR #TBD)

Fresh dumps at post-#118 main (Aave 27.33M vs 18.24M, Uniswap 1.277M vs 907k)
show the three `PositionStatusMap` `next*ContinuousTenThousand` rows (7.96M of
the 9.09M Aave gap) stuck behind a copy-gate chicken-and-egg: the statement
inliner's helper bodies (`isBorrowing`/`isUsingAsCollateral`/`next`) carry
~13 copy/dead-init statements each, which pushes `liveMaxStmts` past
`Propagate.copyDepthLimit = 12`, so the copy facts that would let
`deadPure`/`coalesceCopies` delete that same bloat are never created — and the
bodies also stay above `InlineCalls.inlineOK`'s `liveMax ≤ 13`, so they cannot
inline into the 10k-iteration hot loops either. solc's optimized helpers are 3
statements and it *keeps* the calls; parity is body cleanup, and beating solc
is the per-iteration `ReuseValues` CSE of the duplicated scratch
`mstore`/`keccak256`/`sload` group once both helpers are inlined.

Three coordinated changes (this branch):

1. **Trial-gated `copyGate`** — enable copy facts when the *trial-shrunk* body
   (unverified propagate-with-copies clone + dead-pure-let sweep, used only
   inside the Bool policy) fits the depth budget. The soundness relation is
   gate-policy-agnostic (`propStmts_rel (copyGate 0 b) …` never unfolds the
   gate), so this is a transform-only change.
2. **Simplify strength reduction** — `eq(e,0)`/`eq(0,e)` → `iszero(e)` (saves
   a PUSH32 per site), `iszero³` → `iszero`, `mod(e,2^k)` → `and(e,2^k−1)`,
   `div(e,2^k)` → `shr(k,e)`, `mul(e,2^k)`/`mul(2^k,e)` → `shl(k,e)` — full
   pointwise `EquivExpr` top-level rewrites (both sides keep a builtin
   wrapper; the literal reorder across `e` is unobservable since literal
   evaluation is premise-free and effect-free).
3. **Guarded litOK=true object-path `InlineHelpers`** — run the literal-body
   classification on object code blocks under the
   `storageLayoutFreeStmts`-in/out double guard (the
   Flatten/FuseDeclAssign/ReuseValues recipe), unlocking `and(x, mask)`
   cleanup helpers (TickMath `_2` etc.) that `litOK=false` excludes today.

Deferred: hoisting calls out of *builtin* arguments (`eq(f(a), g(b))`)
overlaps open PR #86 (ANF normalizer); return-var entry zero-init removal is
optional follow-up (σ-seeding `funDefS` with `rets ↦ 0`, sound by
`bindZeros` at `callOk`).

Follow-up exposed by the trial-gate honesty work: **`DeadPure` does not treat
`for`-init declarations as bound in post/body** (`dpStmt`'s `forLoop` case
passes `bound` unchanged), so a dead `let x := i` copy of a loop counter
declared in the init survives forever — `alwaysEval` cannot certify `.var i`.
Strengthening `DcRel.forS` to thread `blockDecls init ++ bound` (init runs
first and scopes over the loop, so its top-level declarations are bound in
post/body) would let the copies-on propagation path fire in counter-loop
bodies too and remove the pre-existing dead copies the current pipeline
leaves in `array_storage_index_access`-style fixtures. Needs the `BoundOK`
invariant extended at the two `forLoop` master-induction cases plus the
`dpStmt_rel` constructor site; the trial sweep in `Propagate.lean`
(`trialDropStmts`) must be updated in the same commit to mirror the new
semantics, or the gate becomes dishonestly conservative.

### ✅ `InlineHelpers` (`Implementation/InlineHelpers.lean`) — landed (this branch)

Generalizes (and **replaces**) `InlineIdentity` through the Core boundary:
`helper?` classifies any `function f(ps) -> r { r := e }` whose body ingests
into `Core.Term ps 1` (nodup, all-read params; string-free). A bare-parameter
body keeps the old `f(e) → add(e, 0)` fence at any single-argument site; a
pure built-in body is **substituted** into flat (value-argument) call sites by
`Term.substEmit` — solc's `wrapping_*`/shift/cleanup wrapper helpers inline
without paying the call protocol. Recursion, effectful/multi-statement bodies,
and non-flat sites keep the call (the fragment Core does not yet cover). The
`litOK` flag separates the block pipeline (literals allowed in bodies and
arguments) from the object pipeline (variables only), because layout
resolution *creates* literals from `dataoffset`/`datasize`, and the
resolution commutation (`InlineHelpersResolve.lean`) needs classification and
the rewrite condition to be resolution-stable. Pipelines live in
`Implementation/Pipeline.lean` (`optimizerPipeline`, `objectPipeline`,
`optimizerPipelineObject_correct`).

### ✅ Inline exact identity helpers (`codex/semantic-gas-optimizer`) — superseded by `InlineHelpers`

Solc's unoptimized IR contains many helpers of the exact form
`function f(p) -> r { r := p }`.  Each use currently pays the full verified
Yul function-call protocol even though the body only returns its argument.  The
semantic gas rows with the largest current `ours / solc` ratios are especially
dense in these helpers: user-defined operator wrappers, cleanup/conversion
chains, and loop bookkeeping.

The planned pass preserves every declaration and rewrites a lexically resolved
identity call `f(e)` to `add(e, 0)`.  The `add` is intentional: unlike the
generally-unsound raw rewrite `f(e) → e`, it preserves the requirement that `e`
produce exactly one value, while also preserving stuckness, halts, value, and
state.  A following `Simplify` run can remove the `add` for the already-proved
variable/literal cases.  Lookup uses the same ordered stack of ordered hoisted
scopes as `lookupFun`, including first-definition behavior, shadowing, function
closures, and the special `for`-initializer scope.

Measurement-only prototype results on 15 of the highest-ratio semantic
benchmarks were all improvements, including:

- `operators/userDefined/all_possible_operators.sol`: 50,489 → 40,160
  (−10,329 gas);
- `statements/empty_for_loop.sol`: 6,580 → 3,095 (−3,485);
- `viaYul/conditional/conditional_multiple.sol`: 1,709 → 1,188 (−521); and
- `operators/userDefined/multiple_operator_definitions_different_types_different_functions_separate_directives.sol`:
  4,205 → 2,319 (−1,886).

The proof will be a bidirectional `Step` simulation indexed by the static scope
stack, because function bodies that call sibling identities are not pointwise
equivalent under arbitrary unrelated `FunEnv`s.  A local identity-call lemma
handles the rewrite; other calls recursively simulate transformed bodies under
corresponding closure environments.  The object path will prove that identity
classification and transformation commute with `resolveForLayoutStmts`, then
compose that result with the existing `Simplify` resolution congruence for the
`Simplify → InlineIdentity → Simplify` pipeline on every object code block.

- **`for`-loop `init`**: a `for`-specific congruence to simplify `init` too.
- **Higher-impact passes**: dead/unused-`let` elimination, redundant `pop`/store
  elimination, branch/switch folding, common-subexpression elimination.
- **Dead `pop`/unused `let` elimination**: remove `let x := <pure e>` when `x`
  is never used and `e` is side-effect-free; drop `pop(<pure e>)`.
- **`iszero(iszero(x))` in boolean position** → `x` when the value is only used
  for truthiness (condition of `if`/`for`, arg of `iszero`).
- **Double-negation / `not(not(x))` → x**, `xor(x,x) → 0`, `sub(x,x) → 0`
  (var-only, value-preserving where sound).
- **Block flattening** of nested `{ … }` with no `funDef`s and no shadowing.
- ~~**Asm-level peepholes** (separate, Asm→Asm soundness contract).~~ ✅
  **Landed** as `YulEvmCompiler/AsmPeephole.lean` (+ `AsmPeepholeSound.lean`):
  `optimizeAsm` runs inside `compile` between `compileProgram` and
  `lowerProg`, with its own whole-program forward simulation over `AStep`
  (`CodeRel` spec relation + `Match` configuration relation, threaded through
  `compile_correct`). Not an `Optimizer.Pass` — it works below the source
  tier, on patterns the Yul→Yul passes cannot express. Three rewrites, each
  mined from actually-emitted Asm (the classic `dup;pop`/`push;pop`/
  `swap n;swap n` peepholes never fire on this backend's output):
  1. `push v; swap1; pop → pop; push v` (constant top return-slot
     assignment; −1 byte, −3 gas each);
  2. `jumpi l; jump m; label l → op iszero; jumpi m; label l` (the
     `if c { break/continue/leave }` shape; −33 bytes each, −8 gas on the
     condition-false path, +3 on the taken path);
  3. drop unreferenced `label`s (~¼ of emitted labels; −1 byte, −1 gas per
     pass-through each).
  Next candidates at this tier: adjacent-label merging (needs global
  relabeling, a different argument than `CodeRel`'s in-place windows), and
  iterating the scan (a dropped branch's `jumpi` can orphan its label for a
  second round).

## Candidate next ideas (measured negatives — Pool* spill campaign)

Both entries below come from attacking the same target: the Pool* fixtures
(`test/uniswap-v4`, PoolSwap.sol) whose gas gap vs solc is dominated by
`MemorySpill` round-tripping ~637 bindings through memory (each spilled *use*
is an `mstore`/`mload`, ≈9 gas). The differential harness excludes final memory
from the gas comparison but compares it for behavior, so stores may not be
removed — only loads forwarded. Both levers below were confirmed
proof-free before measuring (see each entry) and both were measured negative.

### ❌ Cost-aware spill-victim selection (`agent/uv4-spill-select`, measured, rejected)

`MemorySpillSelect.selectLoop` spills the binding *witnessed at physical stack
depth ≥16* (a `DUP17+`/`SWAP17+` failure), to a fixpoint. Hypothesis: among the
candidates that could relieve a given pressure — the deep witness itself, or any
binding physically *above* it (spilling an above-binding drops the witness one
slot, since `physicalDecls` filters selected bindings out of the next layout) —
prefer the *cheapest* by a hotness cost model (weighted static use count,
`loopWeight^depth` per read + per decl/assign/param store), so hot accumulators
stay on the stack and cold bindings spill instead.

**Proof-impact: none (selection-independent).** `spillBlock?` runs `selectSpills`
then re-validates every certificate the soundness proof consumes (`selectedWF`,
`selectedBindingsWF`, `groupsClosedCheck`, `layoutCheck`, and the residual
`firstPressure [] rewritten = none`); `spillBlock_facts` proves `SpillFacts` by
`unfold spillBlock?` without unfolding `selectSpills`, and no `MemorySpill*Sound`
proof reads `SpillFacts.selected`. Rewriting the heuristic (new cost model, new
victim logic, `Pressure.batch` repurposed to carry above-candidates) kept the
whole proof family green.

**Result (vs pinned `test/uniswap-v4-gas-baseline.txt`):**
- Aggressive (spill cheapest above-binding per witness, batched):
  swapExactInputNoTick 60332 → **78984 (+18652)**, uniform PoolSwap regressions,
  total +46k. A shallow spill only lifts a witness one slot; with the usual
  deficit >1 the deep binding is spilled anyway, so diversion *adds* spills.
- Conservative (1-for-1 substitution only at `deficit == 1` with a strictly
  cheaper above-binding): flat, net −6 gas with ±4 noise. Hot accumulators sit
  well below the `DUP16` frontier (large deficit), so the frontier rule never
  reaches them.
- Shift-block one-at-a-time (shared relief, batch disabled): correct but the
  selection loop times out (>10 min) on PoolSwap's 637-spill object; the batch
  is a hard performance requirement.

**Diagnosis:** gas is dominated by spill *count* (uses-weighted), which
per-witness victim choice cannot reduce; the only count-reducer (coordinated
shift-block) either over-spills cold bindings whose aggregate cost exceeds the
one hot spill, or is too slow. The existing depth-victim policy is already near
cost-optimal for this stack structure.

### ❌ Pressure-gated (reduced) inlining (`agent/uv4-inline-gate`, measured, rejected)

`InlineCalls` inlines call-free helpers whenever `inlineOK d` holds
(`d.rs.length ≤ 2 && liveMaxStmts (…) d.ss ≤ 13`). Hypothesis: on Pool* objects
this packs so many live bindings into one frame that `MemorySpill` must spill
637 of them; inlining *less* would shrink frames, reduce spills, and (net of the
added call protocol) save gas.

**Proof-impact: none (gate-independent).** `InlineCallsSound.icStmts_rel` cases
on `(inlineOK d && siteOK …)` as an opaque `Bool` with both branches proven
(the relation's skip rules absorb any declined site); `inlineOK`'s definition is
never inspected. Changing the `≤ 13` threshold globally kept the whole repo
green.

**Result (global threshold sweep, `test/uniswap-v4 --per-scenario`):** reducing
the budget is *monotonically worse*, not better —
- `13` (baseline): swapExactInputNoTick 60332.
- `6`: 60437 (+105); broad small regressions (25 rows), total +1763.
- `1` (near-zero inlining): **70715 (+10383)**; all 44 rows regress, total +215k.

**Diagnosis (decisive):** at threshold 1 the PoolSwap trace still shows
**MSTORE count = 563 (identical to baseline)**, MLOAD 741 — i.e. the same ~637
bindings spill even with near-zero inlining. The spill is dominated by the main
function bodies' *own* locals (solc's unoptimized IR emits functions with very
large local sets), not by inlined helpers. Less inlining therefore cannot shrink
the spill; it only removes the beneficial helper-chain collapse and adds
call-protocol gas. The `≤ 13` gate is already near-optimal.

**Consequence for the campaign:** the Pool* spill count is intrinsic to
per-function local pressure. Reducing it would require shrinking a single
function body's live-local set — e.g. mem2reg/liveness-narrowing of the main
body, or splitting solc's mega-functions — not tuning inlining or spill-victim
selection.
