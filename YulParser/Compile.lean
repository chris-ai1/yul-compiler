import YulParser.Source
import YulEvmCompiler.ObjectCompile
import YulEvmCompiler.SsaCfg.Implementation.Compile
import YulEvmCompiler.SsaCfg.Implementation.Object
import YulEvmCompiler.Optimizer.Implementation.Pipeline
import YulEvmCompiler.Optimizer.Implementation.StackLayoutObject
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSound
set_option warningAsError true
/-!
# YulParser.Compile

The source-text entry point for the compiler. Brace-delimited programs assemble
directly. Object-rooted programs are recursively laid out with their child
objects and data bytes, and `dataoffset`/`datasize` are resolved to constants
in that concrete layout.
-/

namespace YulParser

open YulSemantics (Expr Stmt Object)

/-
The canonical parser retains string escape spelling so its printer can round
trip the exact token. Source execution needs the bytes denoted by that spelling
instead. Convert expression-position string literals to their left-aligned word
value before optimization/compilation; object/data names and the literal-name
arguments of layout/linker/immutable extensions remain spelling-sensitive.
-/

private def escapeHexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def decodeEscapedBytes : List Char → Option (List UInt8)
  | [] => some []
  | '\\' :: 'x' :: a :: b :: rest => do
      let hi ← escapeHexValue a
      let lo ← escapeHexValue b
      return UInt8.ofNat (16 * hi + lo) :: (← decodeEscapedBytes rest)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest => do
      let a ← escapeHexValue a
      let b ← escapeHexValue b
      let c ← escapeHexValue c
      let d ← escapeHexValue d
      let scalar := 4096 * a + 256 * b + 16 * c + d
      return (String.singleton (Char.ofNat scalar)).toUTF8.toList ++
        (← decodeEscapedBytes rest)
  | '\\' :: 'n' :: rest => return 10 :: (← decodeEscapedBytes rest)
  | '\\' :: 'r' :: rest => return 13 :: (← decodeEscapedBytes rest)
  | '\\' :: 't' :: rest => return 9 :: (← decodeEscapedBytes rest)
  | '\\' :: '"' :: rest => return 34 :: (← decodeEscapedBytes rest)
  | '\\' :: '\\' :: rest => return 92 :: (← decodeEscapedBytes rest)
  | '\\' :: _ => none
  | c :: rest => return c.toString.toUTF8.toList ++ (← decodeEscapedBytes rest)

/-- Decode an escape-preserving Yul string spelling to its left-aligned word. -/
def decodedStringValue? (s : String) : Option Nat := do
  let bytes ← decodeEscapedBytes s.toList
  if bytes.length > 32 then none
  else
    let value := bytes.foldl (fun n byte => n * 256 + byte.toNat) 0
    some (value * 2 ^ (8 * (32 - bytes.length)))

private def decodeValueLiteral : YulSemantics.Literal → YulSemantics.Literal
  | .string s => (decodedStringValue? s).map YulSemantics.Literal.number
      |>.getD (.string s)
  | literal => literal

private def literalNameCall (name : String) : Bool :=
  name == "linkersymbol" || name == "loadimmutable" || name == "setimmutable"

mutual
  def decodeValueExpr : Expr YulSemantics.EVM.Op → Expr YulSemantics.EVM.Op
    | .lit literal => .lit (decodeValueLiteral literal)
    | .var name => .var name
    -- Only `setimmutable`'s middle argument names the immutable; the target and
    -- the stored value are ordinary expressions and must be decoded, or an
    -- escaped string value would be patched in as its escape spelling.
    | .call "setimmutable" [base, .lit (.string key), value] =>
        .call "setimmutable"
          [decodeValueExpr base, .lit (.string key), decodeValueExpr value]
    | .call name args =>
        if literalNameCall name then .call name args
        else .call name (decodeValueArgs args)
    | .builtin op args =>
        if op == .dataoffset || op == .datasize || op == .loadimmutable then
          -- name-valued arguments stay spelling-sensitive
          .builtin op args
        else .builtin op (decodeValueArgs args)

  def decodeValueArgs : List (Expr YulSemantics.EVM.Op) →
      List (Expr YulSemantics.EVM.Op)
    | [] => []
    | arg :: rest => decodeValueExpr arg :: decodeValueArgs rest
end

mutual
  def decodeValueStmt : Stmt YulSemantics.EVM.Op → Stmt YulSemantics.EVM.Op
    | .block body => .block (decodeValueStmts body)
    | .funDef name params returns body =>
        .funDef name params returns (decodeValueStmts body)
    | .letDecl names value => .letDecl names (value.map decodeValueExpr)
    | .assign names value => .assign names (decodeValueExpr value)
    | .cond condition body =>
        .cond (decodeValueExpr condition) (decodeValueStmts body)
    | .switch condition cases dflt =>
        .switch (decodeValueExpr condition)
          (decodeValueCases cases)
          (match dflt with
          | some body => some (decodeValueStmts body)
          | none => none)
    | .forLoop init condition post body =>
        .forLoop (decodeValueStmts init) (decodeValueExpr condition)
          (decodeValueStmts post) (decodeValueStmts body)
    | .exprStmt expression => .exprStmt (decodeValueExpr expression)
    | .break => .break
    | .continue => .continue
    | .leave => .leave
    termination_by statement => 2 * sizeOf statement

  def decodeValueStmts : List (Stmt YulSemantics.EVM.Op) →
      List (Stmt YulSemantics.EVM.Op)
    | [] => []
    | statement :: rest => decodeValueStmt statement :: decodeValueStmts rest
    termination_by statements => 2 * sizeOf statements + 1

  def decodeValueCases :
      List (YulSemantics.Literal × List (Stmt YulSemantics.EVM.Op)) →
      List (YulSemantics.Literal × List (Stmt YulSemantics.EVM.Op))
    | [] => []
    | (literal, body) :: rest =>
        (decodeValueLiteral literal, decodeValueStmts body) ::
          decodeValueCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def decodeValueObject : Object YulSemantics.EVM.Op → Object YulSemantics.EVM.Op
    | .mk name code children segments =>
        .mk name (decodeValueStmts code) (decodeValueObjects children) segments

  def decodeValueObjects : List (Object YulSemantics.EVM.Op) →
      List (Object YulSemantics.EVM.Op)
    | [] => []
    | obj :: rest => decodeValueObject obj :: decodeValueObjects rest
end

#guard decodedStringValue? "`\\x01`\\x00\\xf3" ==
  some (0x60016000f3 * 2 ^ (8 * 27))

/-- Desugar solc-IR hint builtins that have no EVM value effect into core Yul
for the ordinary compilation candidates. `memoryguard(e)` returns `e` when no
optimizer scratch is reserved. The final spilling fallback instead retains the
raw marker, raises its result by the reserved call-path bound, and only then
hands the resulting core Yul to the compiler. Every other node is rebuilt
structurally, so programs that do not use such hints are unaffected. -/
def desugarExpr {Op : Type} : Expr Op → Expr Op :=
  YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardExpr

def desugarStmt {Op : Type} : Stmt Op → Stmt Op :=
  YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmt

def desugarObject {Op : Type} : Object Op → Object Op :=
  YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardObject

/-! ### Dead `linkersymbol` bindings

solc's unoptimized `--ir` output materializes every qualified mention of a
library (`Lib.f(x)` with `f` internal) as a dead placeholder binding
`let addr := linkersymbol("file:Lib")`, even though the call itself is a plain
internal Yul call and `addr` is never referenced. `linkersymbol` is a pure
link-time constant with no evaluation effect, so removing a binding whose
variable is never referenced anywhere afterwards cannot change behavior.

Only provably dead bindings are removed: the name must not occur — read or
written — anywhere else in the whole program (a conservative, shadowing-proof
over-approximation; solc generates globally unique names). A program that
actually uses a `linkersymbol` value keeps the call and is still rejected by
the compiler as unsupported, since with no linker there is no sound value to
give it. -/

/-- Variable names referenced by an expression. -/
partial def exprRefs {Op : Type} : Expr Op → List String
  | .var name => [name]
  | .call _ args => args.flatMap exprRefs
  | .builtin _ args => args.flatMap exprRefs
  | _ => []

/-- Names referenced by a statement: variable reads and assignment targets
(a later write to a declared name is a reference that keeps its declaration
alive). Declarations themselves do not count. -/
partial def stmtRefs {Op : Type} : Stmt Op → List String
  | .block body => body.flatMap stmtRefs
  | .funDef _ _ _ body => body.flatMap stmtRefs
  | .letDecl _ val => (val.map exprRefs).getD []
  | .assign vars val => vars ++ exprRefs val
  | .cond c body => exprRefs c ++ body.flatMap stmtRefs
  | .switch c cases dflt =>
      exprRefs c ++ cases.flatMap (fun cb => cb.2.flatMap stmtRefs) ++
        ((dflt.map (·.flatMap stmtRefs)).getD [])
  | .forLoop init c post body =>
      init.flatMap stmtRefs ++ exprRefs c ++ post.flatMap stmtRefs ++
        body.flatMap stmtRefs
  | .exprStmt e => exprRefs e
  | _ => []

partial def objectRefs {Op : Type} : Object Op → List String
  | .mk _ code subs _ => code.flatMap stmtRefs ++ subs.flatMap objectRefs

/-- Drop `let x := linkersymbol("…")` when `used x` is false. Every other
statement is rebuilt structurally. -/
partial def pruneLinkerStmts {Op : Type} (used : String → Bool) :
    List (Stmt Op) → List (Stmt Op)
  | [] => []
  | stmt :: stmts =>
      let rest := pruneLinkerStmts used stmts
      match stmt with
      | .letDecl [x] (some (.call "linkersymbol" _)) =>
          if used x then stmt :: rest else rest
      | .block body => .block (pruneLinkerStmts used body) :: rest
      | .funDef name params rets body =>
          .funDef name params rets (pruneLinkerStmts used body) :: rest
      | .cond c body => .cond c (pruneLinkerStmts used body) :: rest
      | .switch c cases dflt =>
          .switch c (cases.map (fun cb => (cb.1, pruneLinkerStmts used cb.2)))
            (dflt.map (pruneLinkerStmts used)) :: rest
      | .forLoop init c post body =>
          .forLoop (pruneLinkerStmts used init) c (pruneLinkerStmts used post)
            (pruneLinkerStmts used body) :: rest
      | s => s :: rest

partial def pruneLinkerObject {Op : Type} (used : String → Bool) :
    Object Op → Object Op
  | .mk name code subs segs =>
      .mk name (pruneLinkerStmts used code) (subs.map (pruneLinkerObject used)) segs

/-- Remove dead `linkersymbol` bindings from a block, per the module notes. -/
def pruneLinkerBlock {Op : Type} (block : List (Stmt Op)) : List (Stmt Op) :=
  let refs := block.flatMap stmtRefs
  pruneLinkerStmts (refs.contains ·) block

/-- Remove dead `linkersymbol` bindings from a whole object tree. -/
def pruneLinkerObjectTree {Op : Type} (o : Object Op) : Object Op :=
  let refs := objectRefs o
  pruneLinkerObject (refs.contains ·) o

/-! ### Live `linkersymbol`: link-time library addresses

A *used* `linkersymbol("file.sol:Lib")` is solc's placeholder for the address a
linker substitutes — the target of the `delegatecall` that a public/external
library function compiles to. Without a linker there is no sound value for it,
which is why the pruner above only removes provably dead bindings and every
remaining occurrence is rejected.

Supplying the addresses closes that gap. `LinkEnv` is exactly the information
solc's own `--libraries` flag carries, and resolution is a **substitution on
the source program**, performed before parsing hands anything to the optimizer
or the backend: after it, `linkersymbol` no longer occurs and what is compiled
is an ordinary Yul program. So the correctness story is unchanged and reads the
same way `dataoffset`/`datasize` resolution does — the guarantee is about the
*linked* program, the one whose library references are these addresses, and a
different link map is a different program. An unresolved live occurrence is
still rejected rather than given a default. -/

/-- Link-time library addresses, keyed by the fully qualified name solc emits
(`"file.sol:Lib"`). Values are the 160-bit addresses, as naturals. -/
abbrev LinkEnv := List (String × Nat)

/-- The address `name` links to, if the environment supplies one. -/
def linkAddress? (env : LinkEnv) (name : String) : Option Nat :=
  (List.find? (fun entry => entry.1 == name) env).map Prod.snd

mutual
  /-- Replace every `linkersymbol("name")` whose name the environment resolves
  with that address as a literal. Unresolved occurrences are left alone, so the
  compiler still rejects them. -/
  partial def linkExpr {Op : Type} (env : LinkEnv) : Expr Op → Expr Op
    | .call "linkersymbol" [.lit (.string name)] =>
        match linkAddress? env name with
        | some address => .lit (.number address)
        | none => .call "linkersymbol" [.lit (.string name)]
    | .call name args => .call name (args.map (linkExpr env))
    | .builtin op args => .builtin op (args.map (linkExpr env))
    | e => e

  partial def linkStmt {Op : Type} (env : LinkEnv) : Stmt Op → Stmt Op
    | .block body => .block (body.map (linkStmt env))
    | .funDef name params rets body =>
        .funDef name params rets (body.map (linkStmt env))
    | .letDecl names value => .letDecl names (value.map (linkExpr env))
    | .assign names value => .assign names (linkExpr env value)
    | .cond c body => .cond (linkExpr env c) (body.map (linkStmt env))
    | .switch c cases dflt =>
        .switch (linkExpr env c)
          (cases.map (fun cb => (cb.1, cb.2.map (linkStmt env))))
          (dflt.map (·.map (linkStmt env)))
    | .forLoop init c post body =>
        .forLoop (init.map (linkStmt env)) (linkExpr env c)
          (post.map (linkStmt env)) (body.map (linkStmt env))
    | .exprStmt e => .exprStmt (linkExpr env e)
    | s => s
end

/-- Resolve library addresses throughout an object tree. -/
partial def linkObject {Op : Type} (env : LinkEnv) : Object Op → Object Op
  | .mk name code subs segs =>
      .mk name (code.map (linkStmt env)) (subs.map (linkObject env)) segs

/-! ### `setimmutable`

`setimmutable(base, name, value)` writes `value` into the in-memory copy of the
deployed code the constructor is about to return, at every position where that
code reads the immutable. Those positions are the placeholder offsets the child
object's compiled layout records, so the call is **eliminable**: it expands to
one ordinary `mstore` per offset, before anything else runs.

That keeps the extension entirely in the front end — the object layer, its
layout-resolution proof and `compileObject_correct` never see it.

**What is proved, and what is not.** The offsets are a theorem:
`immutableOffsets_correct` shows every offset this expansion patches really does
locate that immutable's 32-byte immediate in the emitted code, so a wrong offset
— the silent-miscompilation risk — is ruled out.

What remains unproved is the *meaning*: `setimmutable` has no source semantics
(it is not an `Op`), so there is no source run to preserve and no
semantic-preservation theorem relates the original object to the expanded one.
The correctness theorem covers the **desugared** program, the one that performs
these `mstore`s. That is a front-end desugaring in the same family as
`memoryguard`, not a proved `Optimizer.Pass`; closing it would mean modeling
`setimmutable` upstream. -/

/-- Does this object tree read or write an immutable? -/
partial def usesImmutablesExpr : Expr YulSemantics.EVM.Op → Bool
  | .builtin .loadimmutable _ => true
  | .call "setimmutable" _ => true
  | .call _ args => args.any usesImmutablesExpr
  | .builtin _ args => args.any usesImmutablesExpr
  | _ => false

partial def usesImmutablesStmt : Stmt YulSemantics.EVM.Op → Bool
  | .block body | .funDef _ _ _ body => body.any usesImmutablesStmt
  | .letDecl _ v => (v.map usesImmutablesExpr).getD false
  | .assign _ v | .exprStmt v => usesImmutablesExpr v
  | .cond c body => usesImmutablesExpr c || body.any usesImmutablesStmt
  | .switch c cases dflt =>
      usesImmutablesExpr c || cases.any (fun cb => cb.2.any usesImmutablesStmt) ||
        ((dflt.map (·.any usesImmutablesStmt)).getD false)
  | .forLoop init c post body =>
      init.any usesImmutablesStmt || usesImmutablesExpr c ||
        post.any usesImmutablesStmt || body.any usesImmutablesStmt
  | _ => false

partial def usesImmutablesObject : Object YulSemantics.EVM.Op → Bool
  | .mk _ code subs _ => code.any usesImmutablesStmt || subs.any usesImmutablesObject

/-- Expand every `setimmutable` in an object tree against the placeholder
offsets of that object's own children, or reject the tree.

An immutable is patched by the **parent** of the object that reads it: the
parent copies the child's code into memory and stores over the placeholders.
Validation only pairs reads with writes *globally* across the whole tree, which
is too weak — a setter in an unrelated sibling patches nothing, and the reader
would deploy with the placeholder still zero. So the pairing is re-checked here
per scope, and a tree that fails it is rejected rather than silently
miscompiled. -/
partial def expandSetImmutablesObject (o : Object YulSemantics.EVM.Op) :
    Option (Object YulSemantics.EVM.Op) :=
  match o with
  | .mk name code subs segs => do
      let subs ← subs.mapM expandSetImmutablesObject
      let perChild := subs.map fun sub =>
        (YulEvmCompiler.objectImmutableOffsets sub).getD []
      -- every immutable a direct child reads must be written by *this* object
      let written := (collectImmutableCallsStmts code).2
      if !(perChild.flatten.all fun p => written.contains p.1) then none else
      -- `setimmutable(base, name, value)` names no child, and `base` points at a
      -- copy of one of them. If two children declare the same immutable the
      -- offsets are not comparable against a single base, so that name is left
      -- unexpanded and the backend rejects the program.
      let declaredBy (n : String) : Nat :=
        (perChild.filter fun offs => offs.any (fun p => p.1 == n)).length
      let all := perChild.flatten
      let ambiguous := (all.map Prod.fst).filter fun n => declaredBy n > 1
      let offsets := all.filter fun p => declaredBy p.1 == 1
      return .mk name
        (YulEvmCompiler.expandSetImmutablesStmts offsets ambiguous code) subs segs

/-- Parse and compile a complete Yul source program to executable EVM bytecode,
using the documented compatibility parser when the verified parser does not
apply. Hint builtins (`memoryguard`) are desugared for ordinary candidates and
retained as reservation authority for the final spilling fallback. `linkersymbol`
occurrences whose library `libraries` supplies are substituted with that
address; provably dead bindings among the rest are dropped, and any live
occurrence left over is still rejected.

Both block- and object-rooted programs first run the full **normalization**
front-end (`Normalize.normalize`: disambiguate every declared name, then hoist
every function definition to the root — semantics-preserving for valid source
programs, `normalize_optimizerPipelineRounds_runEquiv`; its `SourceValid`
hypotheses are assumed of the input, see `Normalization/Normalize.lean` and
`Normalization/Disambiguate/Pass.lean` for the limitation), then run the
verified production pipeline:
simplification and propagation, bounded helper/call inlining with the
normalization needed to expose it, then dead pure/result-region elimination.
The object path applies the pipeline's resolution-stable mode to every code
block in the tree. -/
def compileSource (source : String) (libraries : LinkEnv := []) :
    Option ByteArray := do
  match parseSource source with
  | some (.block block) =>
      -- A block-rooted program has no object tree, so nothing could ever patch a
      -- placeholder: a `loadimmutable` here would compile to a hard-coded zero.
      -- Reject instead. (The grammar still accepts it — this is a compilation
      -- limit, not a syntax rule, so the upstream syntax corpus is unaffected.)
      if !(collectImmutableCallsStmts block).1.isEmpty then none else
      -- The link pass is an expensive identity when no addresses are supplied,
      -- and these inputs are megabytes of generated Yul; skip it entirely.
      let decoded := decodeValueStmts block
      let raw := pruneLinkerBlock
        (if libraries.isEmpty then decoded else decoded.map (linkStmt libraries))
      let b := YulEvmCompiler.Optimizer.Normalize.normalize
        (D := YulSemantics.EVM.evmWithExternal YulSemantics.EVM.ExternalCalls.none
          YulSemantics.EVM.ExternalCreates.none .any)
        (raw.map desugarStmt)
      -- Preserve bytecode stability for programs the full pipeline can already
      -- compile. On stack pressure, first retry its verified smart layout;
      -- then retry the shallower one-round pipeline, with and without smart
      -- layout, before retaining the historical unoptimized fallback. Every
      -- choice is covered by its own correctness theorem.
      --
      -- The fallback candidates are computed inside their `<|>` arms (which
      -- `Option.orElse` thunks), not as up-front `let`s: Lean is strict, so
      -- eager bindings would run the no-rejoin and light pipelines on every
      -- program even though the first candidate compiles in the common case
      -- (measured ~2-3x of the total compile time on the corpus runners).
      -- The smart layout's slot reuse and live-range splitting introduce
      -- `x := y` copies and shared slots, and it runs *after* the pipeline, so
      -- nothing has cleaned up behind it. Sweep the laid-out program with the
      -- verified dead-store pass first, and keep the uncleaned layout as a
      -- further fallback so acceptance can only widen.
      let tryLayouts (blk : List (Stmt YulSemantics.EVM.Op)) :
          Option (List YulEvmCompiler.Instr) :=
        YulEvmCompiler.compile blk
          <|> YulEvmCompiler.compile
            (YulEvmCompiler.Optimizer.cleanupAfterLayoutBlock
              (calls := YulSemantics.EVM.ExternalCalls.none)
              (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)
              (YulEvmCompiler.Optimizer.stackLayoutBlock blk))
          <|> YulEvmCompiler.compile
            (YulEvmCompiler.Optimizer.stackLayoutBlock blk)
      -- The SSA-CFG backend compiles the same fully optimized Yul as the
      -- first classic candidate; both artifacts are kept and the cheaper
      -- one (by the static stack-traffic cost proxy, see
      -- `SsaCfg.instrCost`) wins. Any SSA rejection (construction, shuffle
      -- depth, certificate) simply leaves the classic chain's result.
      let pipelined := (YulEvmCompiler.Optimizer.optimizerPipeline
          (calls := YulSemantics.EVM.ExternalCalls.none)
          (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)).run b
      let ssa := YulEvmCompiler.SsaCfg.compileViaSsa pipelined
      let classic := tryLayouts pipelined
        <|> tryLayouts ((YulEvmCompiler.Optimizer.optimizerPipelineNoRejoin
          (calls := YulSemantics.EVM.ExternalCalls.none)
          (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)).run b)
        <|> tryLayouts ((YulEvmCompiler.Optimizer.optimizerPipelineLight
          (calls := YulSemantics.EVM.ExternalCalls.none)
          (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)).run b)
        <|> YulEvmCompiler.compile b
        <|> (match YulEvmCompiler.Optimizer.MemorySpillSelect.spillBlock? raw with
          | some spilled =>
              -- The spilled program is ordinary Yul; give the optimizer a
              -- chance before compiling it verbatim.
              let spilledOpt := (YulEvmCompiler.Optimizer.optimizerPipeline
                (calls := YulSemantics.EVM.ExternalCalls.none)
                (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)).run
                  (YulEvmCompiler.Optimizer.Normalize.normalize
                    (D := YulSemantics.EVM.evmWithExternal
                      YulSemantics.EVM.ExternalCalls.none
                      YulSemantics.EVM.ExternalCreates.none .any)
                    spilled.block)
              YulEvmCompiler.compile spilledOpt
                <|> YulEvmCompiler.compile spilled.block
          | none => none)
      let asm :=
        match ssa, classic with
        | some a, some b =>
            -- Prefer the statically cheaper candidate; break cost ties by
            -- assembled size and, on full ties, keep the classic artifact. A
            -- cost tie carries no information, and handing it to the other
            -- backend can flip loop-heavy fixtures onto a runtime-costlier
            -- lowering (measured: +79k gas on a corpus loop when an Asm
            -- peephole improvement tied the two candidates' costs).
            let ca := YulEvmCompiler.SsaCfg.instrCost a
            let cb := YulEvmCompiler.SsaCfg.instrCost b
            if ca < cb ∨ (ca = cb ∧
                (YulEvmCompiler.assembleBytes a).length
                  < (YulEvmCompiler.assembleBytes b).length)
            then some a else some b
        | some a, none => some a
        | none, cb => cb
      return YulEvmCompiler.assemble (← asm)
  | some (.object o) =>
      -- The root has no parent to copy and patch its code, so a `loadimmutable`
      -- in the root's *own* code could only ever read the unpatched placeholder,
      -- however many setters the tree contains. Reject it.
      let rootReads := match decodeValueObject o with
        | .mk _ code _ _ => (collectImmutableCallsStmts code).1
      if !rootReads.isEmpty then none else
      let decoded := decodeValueObject o
      let raw := pruneLinkerObjectTree
        (if libraries.isEmpty then decoded else linkObject libraries decoded)
      let o := YulEvmCompiler.Optimizer.Normalize.normalizeObject
        (D := YulSemantics.EVM.evmWithExternal YulSemantics.EVM.ExternalCalls.none
          YulSemantics.EVM.ExternalCreates.none .any)
        (desugarObject raw)
      -- `optimized` stays a named binding (the spill fallback below also
      -- consumes it); the no-rejoin and light pipelines are computed inside
      -- their thunked `<|>` arms so the common first-candidate success never
      -- pays for them (see the block path above).
      let optimized := YulEvmCompiler.Optimizer.optimizerPipelineObject
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any) o
      let tryLayouts (obj : Object YulSemantics.EVM.Op) :=
        (expandSetImmutablesObject obj).bind YulEvmCompiler.compileObject
          <|> (expandSetImmutablesObject
              (YulEvmCompiler.Optimizer.cleanupAfterLayoutObject
                (calls := YulSemantics.EVM.ExternalCalls.none)
                (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)
                (YulEvmCompiler.Optimizer.stackLayoutObject obj))).bind
              YulEvmCompiler.compileObject
          <|> (expandSetImmutablesObject
              (YulEvmCompiler.Optimizer.stackLayoutObject obj)).bind
              YulEvmCompiler.compileObject
      -- SSA-CFG backend on the object path too (same layout fixpoint, SSA
      -- per code block); both artifacts are kept and the cheaper bytecode
      -- (static stack-traffic cost) wins.
      -- The constructor's patch offsets are read off the *classic* plan
      -- (`objectImmutableOffsets`), but the SSA object path schedules its code
      -- independently and records no offsets, so a winning SSA artifact could
      -- be patched at the wrong positions. Withhold that candidate whenever the
      -- tree touches an immutable.
      let ssaLayout :=
        if usesImmutablesObject optimized then none
        else (expandSetImmutablesObject optimized).bind YulEvmCompiler.SsaCfg.compileObjectViaSsa
      let classicLayout := tryLayouts optimized
        <|> tryLayouts (YulEvmCompiler.Optimizer.optimizerPipelineObjectNoRejoin
          (calls := YulSemantics.EVM.ExternalCalls.none)
          (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any) o)
        <|> tryLayouts (YulEvmCompiler.Optimizer.optimizerPipelineObjectLight
          (calls := YulSemantics.EVM.ExternalCalls.none)
          (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any) o)
        <|> (expandSetImmutablesObject o).bind YulEvmCompiler.compileObject
        <|> (match YulEvmCompiler.Optimizer.MemorySpillSelect.spillObjectWithFallback
              raw optimized with
          | some spilled =>
              if spilled.selected = 0 then none
              else
                -- The spilled tree is ordinary Yul (guards resolved); give the
                -- optimizer a chance before compiling it verbatim. This is the
                -- only path large spill-only objects (PoolSwap) reach, so
                -- without it they never see the optimizer at all. Objects the
                -- plain spilled form cannot compile (live `gas`, immutables,
                -- linker symbols) skip the expensive pipeline entirely.
                match (expandSetImmutablesObject spilled.object).bind YulEvmCompiler.compileObject with
                | none => none
                | some plainLayout =>
                    let spilledOpt :=
                      YulEvmCompiler.Optimizer.optimizerPipelineObject
                        (calls := YulSemantics.EVM.ExternalCalls.none)
                        (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)
                        (YulEvmCompiler.Optimizer.Normalize.normalizeObject
                          (D := YulSemantics.EVM.evmWithExternal
                            YulSemantics.EVM.ExternalCalls.none
                            YulSemantics.EVM.ExternalCreates.none .any)
                          spilled.object)
                    (expandSetImmutablesObject spilledOpt).bind YulEvmCompiler.compileObject
                      <|> (expandSetImmutablesObject
                          (YulEvmCompiler.Optimizer.cleanupAfterLayoutObject
                            (calls := YulSemantics.EVM.ExternalCalls.none)
                            (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)
                            (YulEvmCompiler.Optimizer.stackLayoutObject spilledOpt))).bind
                          YulEvmCompiler.compileObject
                      <|> (expandSetImmutablesObject
                          (YulEvmCompiler.Optimizer.stackLayoutObject spilledOpt)).bind
                          YulEvmCompiler.compileObject
                      <|> some plainLayout
          | none => none)
      let layout ←
        match ssaLayout, classicLayout with
        | some a, some b =>
            -- Same tie-break discipline as the block path: cost, then bytes,
            -- then the classic artifact.
            let ca := YulEvmCompiler.SsaCfg.byteCodeCost a.code
            let cb := YulEvmCompiler.SsaCfg.byteCodeCost b.code
            if ca < cb ∨ (ca = cb ∧ a.code.length < b.code.length)
            then some a else some b
        | some a, none => some a
        | none, cb => cb
      return ByteArray.mk layout.code.toArray
  | none => none

end YulParser
