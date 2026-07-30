import YulParser.Compile
import YulEvmCompilerTests.Solc
import YulEvmCompilerTests.SolidityCorpus
import YulSemantics.PrettyPrint
set_option warningAsError true

/-!
# DumpYul — debugging aid: print the optimized Yul we feed to the backend.

Reproduces the object-path optimization in `compileSource` (including the
memory-spill fallback that PoolSwap-class objects reach) and pretty-prints the
resulting optimized Yul so residual `mload`/`mstore` shapes can be inspected.
-/

open System YulParser
open YulSemantics
open YulEvmCompilerTests.Solc
open YulEvmCompilerTests.SolidityCorpus

private def NC := YulSemantics.EVM.ExternalCalls.none
private def NR := YulSemantics.EVM.ExternalCreates.none

/-- Optimized object tree exactly as `compileSource` would compile it (primary
candidate, then spill fallback). Returns the object whose code we actually feed
to the backend, along with a tag. -/
private def optimizedObject (o0 : Object YulSemantics.EVM.Op) :
    Object YulSemantics.EVM.Op × String :=
  let raw := pruneLinkerObjectTree (decodeValueObject o0)
  let o := YulEvmCompiler.Optimizer.Normalize.normalizeObject
    (D := YulSemantics.EVM.evmWithExternal NC NR) (desugarObject raw)
  let optimized := YulEvmCompiler.Optimizer.optimizerPipelineObject
    (calls := NC) (creates := NR) o
  match YulEvmCompiler.compileObject optimized with
  | some _ => (optimized, "primary")
  | none =>
    let rematRaw := YulEvmCompiler.Optimizer.RematSpill.rematObject raw
    match YulEvmCompiler.Optimizer.MemorySpillSelect.spillObjectWithFallback rematRaw rematRaw with
    | some spilled =>
        let spilledOptBase := YulEvmCompiler.Optimizer.optimizerPipelineObject
          (calls := NC) (creates := NR)
          (YulEvmCompiler.Optimizer.Normalize.normalizeObject
            (D := YulSemantics.EVM.evmWithExternal NC NR) spilled.object)
        (spilledOptBase, s!"remat-spilled(selected={spilled.selected})")
    | none => (optimized, "primary(uncompilable)")

/-! ### Pure-function call-CSE sizing (probe) -/

open YulSemantics.EVM (Op)
open YulEvmCompiler.Optimizer.ReuseValues (argsBeq exprVarsRv)

private def pureBuiltinOp : Op → Bool
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod | .addmod | .mulmod | .exp
  | .signextend | .clz | .lt | .gt | .slt | .sgt | .eq | .iszero | .and | .or
  | .xor | .not | .byte | .shl | .shr | .sar => true
  | _ => false

mutual
private def exprBuiltinsPure : Expr Op → Bool
  | .lit _ | .var _ => true
  | .builtin op args => pureBuiltinOp op && argsBuiltinsPure args
  | .call _ args => argsBuiltinsPure args
private def argsBuiltinsPure : List (Expr Op) → Bool
  | [] => true
  | e :: r => exprBuiltinsPure e && argsBuiltinsPure r
end
mutual
private def exprCallees : Expr Op → List Ident
  | .lit _ | .var _ => []
  | .builtin _ args => argsCallees args
  | .call f args => f :: argsCallees args
private def argsCallees : List (Expr Op) → List Ident
  | [] => []
  | e :: r => exprCallees e ++ argsCallees r
end

mutual
private partial def collectBody (body : List (Stmt Op)) : Bool × List Ident := Id.run do
  let mut ok := true; let mut cs : List Ident := []
  for s in body do
    let (o, c) := collectStmt s
    ok := ok && o; cs := cs ++ c
  return (ok, cs)
private partial def collectStmt : Stmt Op → Bool × List Ident
  | .letDecl _ (some e) => (exprBuiltinsPure e, exprCallees e)
  | .letDecl _ none => (true, [])
  | .assign _ e | .exprStmt e => (exprBuiltinsPure e, exprCallees e)
  | .block body => collectBody body
  | .cond c body => let (o,cs) := collectBody body; (exprBuiltinsPure c && o, exprCallees c ++ cs)
  | .switch c cases dflt =>
      let cc := cases.foldl (fun (a : Bool × List Ident) p =>
        let (o,cs) := collectBody p.2; (a.1 && o, a.2 ++ cs)) (exprBuiltinsPure c, exprCallees c)
      match dflt with | some b => let (o,cs) := collectBody b; (cc.1 && o, cc.2 ++ cs) | none => cc
  | .forLoop i c p b =>
      let (o1,c1) := collectBody i; let (o2,c2) := collectBody p; let (o3,c3) := collectBody b
      (exprBuiltinsPure c && o1 && o2 && o3, exprCallees c ++ c1 ++ c2 ++ c3)
  | .funDef _ _ _ _ => (true, [])  -- nested funcs handled separately
  | _ => (true, [])
end

/-- Collect all funDefs (recursively) as (name, params, rets, body). -/
private partial def gatherFuns : Stmt Op → List (Ident × List Ident × List Ident × List (Stmt Op))
  | .funDef f ps rs body =>
      (f, ps, rs, body) :: (body.flatMap gatherFuns)
  | .block body | .cond _ body => body.flatMap gatherFuns
  | .switch _ cases dflt => cases.flatMap (fun p => p.2.flatMap gatherFuns) ++
      (match dflt with | some b => b.flatMap gatherFuns | none => [])
  | .forLoop i _ p b => (i ++ p ++ b).flatMap gatherFuns
  | _ => []

private partial def objFuns : Object YulSemantics.EVM.Op →
    List (Ident × List Ident × List Ident × List (Stmt Op))
  | .mk _ code subs _ => code.flatMap gatherFuns ++ subs.flatMap objFuns

/-- Pure-function set via removal fixpoint. -/
private def purityOf (o : Object YulSemantics.EVM.Op) : Std.HashSet Ident := Id.run do
  let funs := objFuns o
  let mut cand : Std.HashSet Ident := {}
  let mut info : List (Ident × Bool × List Ident) := []
  for (f, _, _, body) in funs do
    let (ok, cs) := collectBody body
    info := (f, ok, cs) :: info
    if ok then cand := cand.insert f
  let mut changed := true
  while changed do
    changed := false
    for (f, _, cs) in info do
      if cand.contains f && !cs.all (fun c => cand.contains c) then
        cand := cand.erase f; changed := true
  return cand

/-- Count CSE opportunities: within each straight-line run, a pure-fn call with a
syntactically identical earlier call (no arg-var reassignment between). Returns
(hits, sumProtocol) where protocol ≈ 24 + 2·args + 6·rets per hit. -/
private partial def cseCount (pureSet : Std.HashSet Ident)
    (rets : Ident → Nat) : List (Stmt Op) → Nat × Nat := fun stmts => Id.run do
  -- seen : list of (callee, args) live in this block
  let mut hits := 0; let mut proto := 0
  let mut seen : List (Ident × List (Expr Op)) := []
  let mut sub := (0, 0)   -- accumulate nested
  let killVars := fun (seen : List (Ident × List (Expr Op))) (xs : List Ident) =>
    seen.filter (fun p => !xs.any (fun x => p.2.any (fun a => (exprVarsRv a).contains x)))
  for s in stmts do
    match s with
    | .letDecl xs (some e) =>
        for (f, as) in exprPureCalls pureSet e do
          if seen.any (fun p => p.1 == f && argsBeq p.2 as) then
            hits := hits + 1; proto := proto + (24 + 2 * as.length + 6 * rets f)
          seen := (f, as) :: seen
        seen := killVars seen xs
    | .assign xs e =>
        for (f, as) in exprPureCalls pureSet e do
          if seen.any (fun p => p.1 == f && argsBeq p.2 as) then
            hits := hits + 1; proto := proto + (24 + 2 * as.length + 6 * rets f)
          seen := (f, as) :: seen
        seen := killVars seen xs
    | .exprStmt e =>
        for (f, as) in exprPureCalls pureSet e do
          if seen.any (fun p => p.1 == f && argsBeq p.2 as) then
            hits := hits + 1; proto := proto + (24 + 2 * as.length + 6 * rets f)
          seen := (f, as) :: seen
    | .block body => let r := cseCount pureSet rets body; sub := (sub.1 + r.1, sub.2 + r.2); seen := []
    | .cond _ body => let r := cseCount pureSet rets body; sub := (sub.1 + r.1, sub.2 + r.2); seen := []
    | .switch _ cases dflt =>
        for p in cases do let r := cseCount pureSet rets p.2; sub := (sub.1 + r.1, sub.2 + r.2)
        match dflt with | some b => let r := cseCount pureSet rets b; sub := (sub.1 + r.1, sub.2 + r.2) | none => pure ()
        seen := []
    | .forLoop i _ p b =>
        for blk in [i, p, b] do let r := cseCount pureSet rets blk; sub := (sub.1 + r.1, sub.2 + r.2)
        seen := []
    | _ => seen := []
  return (hits + sub.1, proto + sub.2)
where
  /-- Top-level pure-fn calls in an expression (callee ∈ pure). -/
  exprPureCalls (pureSet : Std.HashSet Ident) : Expr Op → List (Ident × List (Expr Op))
  | .lit _ | .var _ => []
  | .builtin _ args => args.flatMap (exprPureCalls pureSet)
  | .call f args =>
      (if pureSet.contains f then [(f, args)] else []) ++ args.flatMap (exprPureCalls pureSet)

def main (args : List String) : IO UInt32 := do
  match args with
  | fixture :: solcPath :: rest => do
    let contents ← IO.FS.readFile fixture
    let source := fixtureSource contents
    let ir ← do
      match ← solcUnoptimizedIR solcPath source with
      | .ok ir => pure ir
      | .error e => IO.eprintln e; return 1
    match parseSource ir with
    | some (.object o) =>
        if rest.contains "--purecse" then
          let raw := pruneLinkerObjectTree (decodeValueObject o)
          let base := YulEvmCompiler.Optimizer.RematSpill.rematObject raw
          let pureSet := purityOf base
          let funs := objFuns base
          let retMap : Std.HashMap Ident Nat :=
            funs.foldl (fun m (f, _, rs, _) => m.insert f rs.length) {}
          let rets := fun f => retMap.getD f 0
          -- CSE over every function body plus each object's top code.
          let rec objCode : Object YulSemantics.EVM.Op → List (List (Stmt Op))
            | .mk _ code subs _ => code :: subs.flatMap objCode
          let bodies := (objCode base) ++ funs.map (fun (_,_,_,b) => b)
          let (hits, proto) := bodies.foldl
            (fun (a : Nat × Nat) b => let r := cseCount pureSet rets b; (a.1 + r.1, a.2 + r.2)) (0, 0)
          IO.println s!"pure funcs: {pureSet.size} / {funs.length}"
          IO.println s!"pure-call CSE hits: {hits}   protocol-only ceiling: {proto} gas (+ duplicate body work)"
          return 0
        if rest.contains "--spillcount" then
          let raw := pruneLinkerObjectTree (decodeValueObject o)
          let on := YulEvmCompiler.Optimizer.Normalize.normalizeObject
            (D := YulSemantics.EVM.evmWithExternal NC NR) (desugarObject raw)
          let optimized := YulEvmCompiler.Optimizer.optimizerPipelineObject
            (calls := NC) (creates := NR) on
          let selOf := fun ob =>
            match YulEvmCompiler.Optimizer.MemorySpillSelect.spillObjectWithFallback ob ob with
            | some r => r.selected | none => 0
          let rec declCount : Object YulSemantics.EVM.Op → Nat
            | .mk _ code subs _ =>
                (YulEvmCompiler.Optimizer.MemorySpill.declaredStmts code).length +
                  subs.foldl (fun a s => a + declCount s) 0
          let rematRaw := YulEvmCompiler.Optimizer.RematSpill.rematObject raw
          -- Mirror compileSource's spillCompile: spill `base` (fallback
          -- `optimized`), re-optimize, store-elim, compile; report code size.
          let spillCompile := fun (base : Object YulSemantics.EVM.Op) =>
            (match YulEvmCompiler.Optimizer.MemorySpillSelect.spillObjectWithFallback
              base optimized with
            | some spilled =>
                if spilled.selected = 0 then none
                else match YulEvmCompiler.compileObject spilled.object with
                  | none => none
                  | some plainLayout =>
                      let sOpt := YulEvmCompiler.Optimizer.SpillStoreElim.elimObject
                        (YulEvmCompiler.Optimizer.optimizerPipelineObject (calls := NC)
                          (creates := NR) (YulEvmCompiler.Optimizer.Normalize.normalizeObject
                            (D := YulSemantics.EVM.evmWithExternal NC NR) spilled.object))
                      YulEvmCompiler.compileObject sOpt
                        <|> YulEvmCompiler.compileObject
                          (YulEvmCompiler.Optimizer.stackLayoutObject sOpt)
                        <|> some plainLayout
            | none => none : Option YulSemantics.EVM.Layout)
          let szOf := fun (l : Option YulSemantics.EVM.Layout) =>
            match l with | some x => x.code.length | none => 0
          IO.println s!"raw:   spillCount={selOf raw}   codeSize={szOf (spillCompile raw)}"
          IO.println s!"remat: spillCount={selOf rematRaw}   codeSize={szOf (spillCompile rematRaw)}"
          return 0
        let (opt, tag) :=
          if rest.contains "--prespill" then
            let raw := pruneLinkerObjectTree (decodeValueObject o)
            let on := YulEvmCompiler.Optimizer.Normalize.normalizeObject
              (D := YulSemantics.EVM.evmWithExternal NC NR) (desugarObject raw)
            (YulEvmCompiler.Optimizer.optimizerPipelineObject (calls := NC) (creates := NR) on,
             "prespill-optimized")
          else optimizedObject o
        IO.println s!"-- optimized object path: {tag}"
        -- Dump only the deepest runtime code block unless --full given.
        if rest.contains "--full" then
          IO.println (EVM.printObject opt)
        else
          -- Find the runtime sub-object code (the one whose name ends in "_deployed").
          let rec findDeployed : Object YulSemantics.EVM.Op → Option (Object YulSemantics.EVM.Op)
            | o@(.mk n _ subs _) =>
                if n.endsWith "_deployed" then some o
                else subs.foldl (fun acc s => acc <|> findDeployed s) none
          match findDeployed opt with
          | some d => IO.println (EVM.printObject d)
          | none => IO.println (EVM.printObject opt)
        return 0
    | _ => IO.eprintln "expected an object"; return 1
  | _ => IO.eprintln "usage: dumpYul <fixture.sol> <solc> [--full]"; return 64
