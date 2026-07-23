import YulParser.Source
import YulEvmCompiler.ObjectCompile
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

/-- Parse and compile a complete Yul source program to executable EVM bytecode,
using the documented compatibility parser when the verified parser does not
apply. Hint builtins (`memoryguard`) are desugared for ordinary candidates and
retained as reservation authority for the final spilling fallback. Provably
dead `linkersymbol` bindings are dropped before either path.

Both block- and object-rooted programs run the verified production pipeline:
simplification and propagation, bounded helper/call inlining with the
normalization needed to expose it, then dead pure/result-region elimination.
The object path applies the pipeline's resolution-stable mode to every code
block in the tree. -/
def compileSource (source : String) : Option ByteArray := do
  match parseSource source with
  | some (.block block) =>
      let raw := pruneLinkerBlock block
      let b := raw.map desugarStmt
      -- Preserve bytecode stability for programs the full pipeline can already
      -- compile. On stack pressure, first retry its verified smart layout;
      -- then retry the shallower one-round pipeline, with and without smart
      -- layout, before retaining the historical unoptimized fallback. Every
      -- choice is covered by its own correctness theorem.
      let normalized := YulEvmCompiler.Optimizer.Normalize.normalizeBlock
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none) b
      let optimized := (YulEvmCompiler.Optimizer.optimizerPipeline
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none)).run normalized
      let light := (YulEvmCompiler.Optimizer.optimizerPipelineLight
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none)).run normalized
      let asm := YulEvmCompiler.compile optimized
        <|> YulEvmCompiler.compile
          (YulEvmCompiler.Optimizer.stackLayoutBlock optimized)
        <|> YulEvmCompiler.compile light
        <|> YulEvmCompiler.compile
          (YulEvmCompiler.Optimizer.stackLayoutBlock light)
        <|> YulEvmCompiler.compile b
        <|> (match YulEvmCompiler.Optimizer.MemorySpillSelect.spillBlock? raw with
          | some spilled => YulEvmCompiler.compile spilled.block
          | none => none)
      return YulEvmCompiler.assemble (← asm)
  | some (.object o) =>
      let raw := pruneLinkerObjectTree o
      let o := desugarObject raw
      let optimized := YulEvmCompiler.Optimizer.optimizerPipelineObjectNormalized
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none) o
      let optimizedLayout :=
        YulEvmCompiler.Optimizer.stackLayoutObject optimized
      let light := YulEvmCompiler.Optimizer.optimizerPipelineObjectNormalizedLight
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none) o
      let layout ← YulEvmCompiler.compileObject optimized
        <|> YulEvmCompiler.compileObject optimizedLayout
        <|> YulEvmCompiler.compileObject light
        <|> YulEvmCompiler.compileObject
          (YulEvmCompiler.Optimizer.stackLayoutObject light)
        <|> YulEvmCompiler.compileObject o
        <|> (match YulEvmCompiler.Optimizer.MemorySpillSelect.spillObjectWithFallback
              raw optimized with
          | some spilled =>
              if spilled.selected = 0 then none
              else YulEvmCompiler.compileObject spilled.object
          | none => none)
      return ByteArray.mk layout.code.toArray
  | none => none

end YulParser
