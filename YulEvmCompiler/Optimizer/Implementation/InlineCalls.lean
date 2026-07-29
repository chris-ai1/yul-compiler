import YulEvmCompiler.Optimizer.Spec.LocalPass
import YulEvmCompiler.Optimizer.Implementation.Frame
import YulSemantics.Dialect.EVM
set_option warningAsError true
set_option linter.unusedVariables false
/-!
# YulEvmCompiler.Optimizer.Implementation.InlineCalls

**Statement-level inlining of call-free helper functions.** The verified
backend's function-call protocol costs ≈ `24 + 2·|args| + 6·|rets|` gas per
call (return-address `PUSH32`, zeroed return slots, jumps, `JUMPDEST`s,
parameter pops, return rotation, dynamic return jump), and solc's unoptimized
IR — this compiler's input — routes every external call through a chain of
~15 tiny helpers (`external_fun_*` → `abi_decode_tuple_*` → `abi_decode_t_*`
→ `validator_revert_*`, `fun_X` → `fun_Y` wrappers, `zero_value_*`,
`revert_error_*`). solc's own FullInliner flattens all of it; `InlineHelpers`
only reaches single-expression bodies. This pass inlines *statement-level*
calls — `let xs := f(as)`, `xs := f(as)`, and bare `f(as)` — whose callee
body is:

* **call-free** (no `.call` anywhere): the body's execution then never
  consults the function environment, so the inlined copy needs no
  closure/scope-resolution reasoning (`Step` only reads `funs` in its
  `call*` rules);
* free of `funDef`/`forLoop`/`break`/`continue`/`leave` — except one optional
  *trailing* `leave`, which is dropped (`callOk` accepts `normal` and `leave`
  outcomes identically);
* **well-scoped within `params ∪ rets`**, checked binder-aware
  (`scopedStmts`). This is a soundness condition, not hygiene: the pointwise
  spec quantifies over all caller environments, and an ill-scoped body
  converts callee stuckness (read of an unbound name) or a callee no-op
  (assignment to an unbound name — `VEnv.set` skips) into a read/write of a
  caller variable of the same name.

## The rewrite

For an inlinable `function f(p₁…pₙ) -> r₁…rₘ { ss }`:

```
let xs := f(a₁…aₙ)   ⟶   let xs
                          { let r₁, …, rₘ            // zero-init, like bindZeros
                            let pₙ := aₙ … let p₁ := a₁ // right-to-left, Yul arg order
                            { ss }                    // own scope, like the call's body block
                            x₁ := r₁ … xₘ := rₘ }
```

(the assign form omits the leading `let xs`; the expression-statement form has
`m = 0` and no trailing assigns). The inner environment at `{ ss }` is
literally `callOk`'s callee environment `params.zip argvals ++ bindZeros rets`
stacked on the caller's; the `{ ss }` wrap reproduces the call's body-block
`restore`, so body locals die before the returns are read. Per-site side
conditions (checked syntactically):

* exact arities `|as| = |ps|`, `|xs| = |rs|` — the call is *stuck* otherwise,
  and the replacement must not run where the original is stuck;
* `(vars(as) ∪ xs) ∩ (ps ∪ rs) = ∅` — argument reads and result writes must
  not be captured by the freshly bound parameter/return names;
* for the `let` form additionally `vars(as) ∩ xs = ∅` — the original evaluates
  arguments *before* `xs` exist, the replacement after `let xs` zero-binds
  them;
* `xs.Nodup` — `letVal` binds `xs.zip vals` (first occurrence wins on read),
  while sequential assignment applies `VEnv.set` left-to-right (last write to
  a duplicate wins); the two disagree on duplicates.

`for`-loop `init` sites are left alone (mirroring `DeadLits`); helper *chains*
collapse leaf-first by iterating the pipeline — a call-free callee inlines
this round, which makes its caller call-free for the next round.

Function declarations visible at a site are threaded as a syntactic
environment `Δ` (most recent scope first), extended at each block by the
block's hoisted definitions and pruned of shadowed names — mirroring
`hoist`/`lookupFun`, so a `Δ` hit *is* the `lookupFun` result.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Syntactic side conditions -/

mutual

/-- Variable names read by an expression (with multiplicity; used only via
membership). -/
def exprVars : Expr Op → List Ident
  | .lit _ => []
  | .var x => [x]
  | .builtin _ args => varsList args
  | .call _ args => varsList args

/-- Variable names read by an argument list. -/
def varsList : List (Expr Op) → List Ident
  | [] => []
  | e :: rest => exprVars e ++ varsList rest

end

mutual
/-- Does a `.call` occur anywhere in the expression? (`dataoffset`/`datasize`
are *builtins* in this AST, so layout resolution never changes this
classification.) -/
def exprHasCall : Expr Op → Bool
  | .lit _ => false
  | .var _ => false
  | .builtin _ args => argsHaveCall args
  | .call _ _ => true

/-- Does a `.call` occur anywhere in the argument list? -/
def argsHaveCall : List (Expr Op) → Bool
  | [] => false
  | e :: rest => exprHasCall e || argsHaveCall rest
end

/-- Scoped well-formedness of an inlinable body: every variable *read* is
bound, every *assignment target* is bound, there are no calls, no function
definitions, no loops, and no `leave`/`break`/`continue`. `bound` grows with
`let` declarations, is restored at block exits, and assignment targets must
already be bound (an assignment to an unbound name is a `VEnv.set` no-op in
the callee's fresh environment but would write a caller variable once
inlined). -/
def scopedExpr (bound : List Ident) (e : Expr Op) : Bool :=
  !exprHasCall e && (exprVars e).all bound.contains

mutual

/-- Scope-check one statement of an inlinable body; `none` means rejected,
`some bound'` gives the binding context for the following statements. -/
def scopedStmt (bound : List Ident) : Stmt Op → Option (List Ident)
  | .letDecl xs none => some (xs ++ bound)
  | .letDecl xs (some e) =>
      if scopedExpr bound e then some (xs ++ bound) else none
  | .assign xs e =>
      if xs.all bound.contains && scopedExpr bound e then some bound else none
  | .exprStmt e => if scopedExpr bound e then some bound else none
  | .block body => if scopedStmts bound body then some bound else none
  | .cond c body =>
      if scopedExpr bound c && scopedStmts bound body then some bound else none
  | .switch c cases dflt =>
      if scopedExpr bound c && scopedCases bound cases && scopedDflt bound dflt
      then some bound else none
  | .funDef _ _ _ _ => none
  | .forLoop _ _ _ _ => none
  | .break => none
  | .continue => none
  | .leave => none

/-- Scope-check a statement sequence of an inlinable body. -/
def scopedStmts (bound : List Ident) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest =>
      match scopedStmt bound s with
      | some bound' => scopedStmts bound' rest
      | none => false

/-- Scope-check `switch` case bodies of an inlinable body. -/
def scopedCases (bound : List Ident) : List (Literal × Block Op) → Bool
  | [] => true
  | (_, b) :: rest => scopedStmts bound b && scopedCases bound rest

/-- Scope-check a `switch` default of an inlinable body. -/
def scopedDflt (bound : List Ident) : Option (Block Op) → Bool
  | none => true
  | some b => scopedStmts bound b

end

/-! ### Classification -/

/-- An inlinable helper: parameters, returns, and the body with any single
trailing `leave` already dropped. -/
structure IDecl where
  ps : List Ident
  rs : List Ident
  ss : List (Stmt Op)

/-- The syntactic declaration environment: innermost scope's survivors first.
An entry `(f, d)` asserts that `f` resolves, at every use site the transform
rewrites, to exactly this declaration. -/
abbrev DEnv := List (Ident × IDecl)

/-- Drop a single trailing `leave` (the body shape solc emits for functions
with an explicit `return`); `scopedStmts` rejects every other `leave`. -/
def dropTrailingLeave (body : Block Op) : Block Op :=
  match body.getLast? with
  | some .leave => body.dropLast
  | _ => body

/-- Classify a function declaration as inlinable. -/
def classifyDecl (ps rs : List Ident) (body : Block Op) : Option IDecl :=
  if (ps ++ rs).Nodup && scopedStmts (ps ++ rs) (dropTrailingLeave body) then
    some ⟨ps, rs, dropTrailingLeave body⟩
  else
    none

/-- Names of every function defined at the top level of a block. -/
def definedFuns : List (Stmt Op) → List Ident
  | [] => []
  | .funDef f _ _ _ :: rest => f :: definedFuns rest
  | _ :: rest => definedFuns rest

/-- The inlinable declarations a block hoists, in definition order (mirroring
`hoist`; on duplicate names `lookupFun`'s `find?` takes the first, and Yul
forbids duplicates anyway — we skip any name already seen). -/
def hoistDecls (seen : List Ident) : List (Stmt Op) → DEnv
  | [] => []
  | .funDef f ps rs body :: rest =>
      if seen.contains f then hoistDecls seen rest
      else
        match classifyDecl ps rs body with
        | some d => (f, d) :: hoistDecls (f :: seen) rest
        | none => hoistDecls (f :: seen) rest
  | _ :: rest => hoistDecls seen rest

/-- Entering a block: its own inlinable declarations shadow, and *any* of its
function definitions (inlinable or not) kill same-named outer entries. -/
def deltaExtend (Δ : DEnv) (body : List (Stmt Op)) : DEnv :=
  hoistDecls [] body ++ Δ.filter (fun p => !(definedFuns body).contains p.1)

/-- Look up an inlinable declaration. -/
def lookupDelta (Δ : DEnv) (f : Ident) : Option IDecl :=
  (Δ.find? (fun p => p.1 = f)).map (·.2)

/-! ### Transform-only profitability and stack-pressure guards

Neither guard affects soundness (the relation's skip rules absorb any site the
transform declines); they gate *when* inlining pays.

* **Benefit**: the call protocol costs ≈ `24 + 2·|ps| + 6·|rs|` gas; the
  inlined residue (return zero-inits, read-out assignments, block-exit pops)
  costs ≈ `2·|ps| + 13·|rs|`, so the net is ≈ `24 − 7·|rs|` — negative from
  three returns up (measured: `unusedFunctionParameterPruner/multiple_return`,
  `stackReuse/reuse_slots_function*`).
* **Stack pressure**: the backend keeps locals on the EVM stack with a hard
  `DUP16`/`SWAP16` reach; inlining stacks the callee frame on the caller's
  live locals, and iterated rounds compound nested frames (measured:
  `fullSuite/abi2.yul` stopped compiling without the bound). -/

-- `liveMax*` (the live-local analysis) lives in `Frame.lean`, shared with
-- the propagation depth gate.

/-- Profitability + stack-pressure gate (see the section notes). -/
def inlineOK (d : IDecl) : Bool :=
  d.rs.length ≤ 2 &&
  liveMaxStmts (d.ps.length + d.rs.length) d.ss ≤ 13

/-! ### The site rewrite -/

/-- Capture check for the argument bindings. The replacement binds
right-to-left (`let pₙ := aₙ … let p₁ := a₁` after `let rs`), matching Yul's
argument evaluation order, so `aᵢ` evaluates with `{p_{i+1}, …, pₙ} ∪ rs`
freshly bound above the caller's environment — those are the only names it
must avoid. In particular a callee parameter may share its name with the
argument that *feeds* it (solc's `validator_revert_t_uint256(value)` idiom):
the binding happens after the read. -/
def argsShadowOK (rs : List Ident) : List (Ident × Expr Op) → Bool
  | [] => true
  | (_, a) :: rest =>
      (exprVars a).all
        (fun v => !(rest.map Prod.fst).contains v && !rs.contains v) &&
      argsShadowOK rs rest

/-- Per-site side conditions (see the module notes). `isLet` marks the
`let xs := f(as)` form, which additionally must not read `xs` in the
arguments. -/
def siteOK (d : IDecl) (xs : List Ident) (as : List (Expr Op))
    (isLet : Bool) : Bool :=
  as.length = d.ps.length && xs.length = d.rs.length && xs.Nodup &&
  !argsHaveCall as &&
  argsShadowOK d.rs (d.ps.zip as) &&
  xs.all (fun v => !(d.ps ++ d.rs).contains v) &&
  (!isLet || (varsList as).all (fun v => !xs.contains v))

/-- The inlined copy: zero-init the returns, bind the parameters right-to-left
(Yul's argument order), run the body in its own scope, then read the returns
out. -/
def inlineCore (d : IDecl) (xs : List Ident) (as : List (Expr Op)) : Stmt Op :=
  .block
    ([.letDecl d.rs none]
      ++ ((d.ps.zip as).reverse.map (fun pa => .letDecl [pa.1] (some pa.2)))
      ++ [.block d.ss]
      ++ (xs.zip d.rs).map (fun xr => .assign [xr.1] (.var xr.2)))

/-! ### The transform -/

mutual

/-- Inline through one statement. The three site shapes rewrite (guarded by
`lookupDelta` + `siteOK`); everything else is rebuilt structurally, function
bodies included (their visible scope chain is the same `Δ` — Yul functions
close over the scopes of their defining block). `for`-loop `init` is left
untouched. The inserted copy is *not* revisited (chains collapse across
pipeline rounds). Every rewrite returns a statement *list* (the `let` form
becomes two statements). -/
def icStmt (Δ : DEnv) : Stmt Op → List (Stmt Op)
  | .letDecl xs (some (.call f as)) =>
      match lookupDelta Δ f with
      | some d =>
          if inlineOK d && siteOK d xs as true then
            [.letDecl xs none, inlineCore d xs as]
          else
            [.letDecl xs (some (.call f as))]
      | none => [.letDecl xs (some (.call f as))]
  | .assign xs (.call f as) =>
      match lookupDelta Δ f with
      | some d =>
          if inlineOK d && siteOK d xs as false then
            [inlineCore d xs as]
          else
            [.assign xs (.call f as)]
      | none => [.assign xs (.call f as)]
  | .exprStmt (.call f as) =>
      match lookupDelta Δ f with
      | some d =>
          if inlineOK d && siteOK d [] as false then
            [inlineCore d [] as]
          else
            [.exprStmt (.call f as)]
      | none => [.exprStmt (.call f as)]
  | .block body => [.block (icBlock Δ body)]
  | .funDef n ps rs body => [.funDef n ps rs (icBlock Δ body)]
  | .cond c body => [.cond c (icBlock Δ body)]
  | .switch c cases dflt => [.switch c (icCases Δ cases) (icDflt Δ dflt)]
  | .forLoop init c post body =>
      -- `init`'s function definitions are visible in `post`/`body` (the loop
      -- runs under `hoist init :: funs`) but `init` is left untouched, so its
      -- definitions only *shadow*: prune them from Δ, never extend with them.
      let ΔL := Δ.filter (fun p => !(definedFuns init).contains p.1)
      [.forLoop init c (icBlock ΔL post) (icBlock ΔL body)]
  | s => [s]

/-- Inline through a statement sequence (already under its block's `Δ`). -/
def icStmts (Δ : DEnv) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => icStmt Δ s ++ icStmts Δ rest

/-- Enter a block: extend `Δ` with its hoisted declarations, then inline. -/
def icBlock (Δ : DEnv) (body : List (Stmt Op)) : List (Stmt Op) :=
  icStmts (deltaExtend Δ body) body

/-- Inline through `switch` case bodies. -/
def icCases (Δ : DEnv) : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, icBlock Δ b) :: icCases Δ rest

/-- Inline through a `switch` default. -/
def icDflt (Δ : DEnv) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (icBlock Δ b)

end

/-- The pass entry point: a top-level block scopes its own definitions. -/
def inlineCallsBlock (b : Block Op) : Block Op := icBlock [] b

end YulEvmCompiler.Optimizer
