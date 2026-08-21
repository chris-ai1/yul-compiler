import YulEvmCompiler.Compile
import YulEvmCompiler.StateRel
import YulEvmCompiler.Optimizer.Implementation.Pipeline
import YulEvmCompiler.Optimizer.Implementation.StackLayoutSound
import YulSemantics.Syntax
import YulSemantics.Interp
import YulSemantics.FibExample
import EvmSemantics.EVM.StepF
set_option warningAsError true
/-!
# YulEvmCompiler.Examples

Sanity checks for the labeled-assembly pipeline (`compileProgram` /
`compile`): loops, `break`/`continue`, `switch`, user-defined functions
(including recursion), multi-value returns/assignments, and `leave`.

Beyond "it compiles", the interesting checks here are **differential**: each
program is run through yul-semantics' fuel-indexed interpreter *and* the
compiled bytecode is run through evm-semantics' executable step function
(`stepF`), and the affected final state is compared. This exercises the
whole pipeline (labels, lowering, the calling convention) long before the
correctness proof covers it.
-/

namespace YulEvmCompiler.Examples

open YulSemantics
open YulSemantics.EVM (Op EvmState)
open YulEvmCompiler

/-! ### Test programs -/

/-- A counting loop: `1 + 2 + … + 5` into storage slot 0. -/
def sumLoop : Block Op := yul% {
  let sum := 0
  for { let i := 1 } lt(i, 6) { i := add(i, 1) } {
    sum := add(sum, i)
  }
  sstore(0, sum)
}

/-- `continue` skips 3, `break` stops at 6: `0+1+2+4+5 = 12` in slot 0. -/
def breakContinue : Block Op := yul% {
  let s := 0
  for { let i := 0 } lt(i, 10) { i := add(i, 1) } {
    if eq(i, 3) { continue }
    if eq(i, 6) { break }
    s := add(s, i)
  }
  sstore(0, s)
}

/-- `switch` dispatch: `x = 2` selects the matching case, `7*3 = 21` in slot 0. -/
def switchMatch : Block Op := yul% {
  let x := 2
  switch x
  case 1 { sstore(0, 10) }
  case 2 { sstore(0, mul(7, 3)) }
  case 3 { sstore(0, 30) }
  default { sstore(0, 99) }
}

/-- `switch` fall-through to `default` when no case matches: `99` in slot 0. -/
def switchDefault : Block Op := yul% {
  let x := 5
  switch x
  case 1 { sstore(0, 10) }
  case 2 { sstore(0, 20) }
  default { sstore(0, 99) }
}

/-- A multi-value-return function feeding a multi-value `let`:
`divmod(17, 5) = (3, 2)` into slots 0 and 1. -/
def multiRet : Block Op := yul% {
  function divmod(a, b) -> q, r {
    q := div(a, b)
    r := mod(a, b)
  }
  let x, y := divmod(17, 5)
  sstore(0, x)
  sstore(1, y)
}

/-- A multi-value-return function feeding a multi-value assignment (the
targets already exist): `x, y := swap2(x, y)` swaps `1, 2` to `2, 1`. -/
def multiAssign : Block Op := yul% {
  function swap2(a, b) -> c, d {
    c := b
    d := a
  }
  let x := 1
  let y := 2
  x, y := swap2(x, y)
  sstore(0, x)
  sstore(1, y)
}

/-- A three-value return, exercising the full `SWAP1;SWAP2;SWAP3` rotation:
`first3() = (7, 8, 9)` into slots 0, 1, 2. -/
def multiRet3 : Block Op := yul% {
  function first3() -> a, b, c {
    a := 7
    b := 8
    c := 9
  }
  let x, y, z := first3()
  sstore(0, x)
  sstore(1, y)
  sstore(2, z)
}

/-- A simple function: `double(21) = 42` in slot 0. -/
def funCall : Block Op := yul% {
  function double(x) -> y {
    y := add(x, x)
  }
  sstore(0, double(21))
}

/-- Identity helpers at top-level and inside a sibling function, plus a nested
non-identity shadow with the same name. -/
def identityHelpers : Block Op := yul% {
  function identity(x) -> y { y := x }
  function throughSibling(x) -> y { y := identity(x) }
  sstore(0, throughSibling(41))
  {
    function identity(x) -> y { y := add(x, 1) }
    sstore(1, identity(41))
  }
}

def optimizedIdentityHelpers : Block Op :=
  (Optimizer.optimizerPipeline
    (calls := YulSemantics.EVM.ExternalCalls.none)
    (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)).run identityHelpers

/-- Pure expression-body wrapper helpers — the shapes solc emits for scaling,
masking, and unchecked-arithmetic wrappers. The Core inliner substitutes the
arguments into the body at flat call sites; the trailing Simplify folds what
the substitution exposes. -/
def wrapperHelpers : Block Op := yul% {
  function scale(v) -> r { r := mul(v, 3) }
  function wadd(a, b) -> r { r := add(a, b) }
  let x := 14
  sstore(0, scale(x))
  sstore(1, wadd(x, scale(1)))
}

def optimizedWrapperHelpers : Block Op :=
  (Optimizer.optimizerPipeline
    (calls := YulSemantics.EVM.ExternalCalls.none)
    (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)).run wrapperHelpers

/-- A store followed by repeated literal-slot loads. `StorageForward` reuses
the stored cheap value instead of emitting warm `SLOAD`s. -/
def storageForwarding : Block Op := yul% {
  let base := 40
  sstore(0, add(base, 2))
  let first := sload(0)
  sstore(1, first)
  let second := sload(1)
  sstore(2, second)
}

def hasForwardedStorageLoads : Block Op → Bool
  | [.letDecl ["base"] (some (.lit (.number 40))),
      .exprStmt (.builtin .sstore _),
      .letDecl ["first"] (some (.builtin .add [.var "base", .lit (.number 2)])),
      .exprStmt (.builtin .sstore _),
      .letDecl ["second"] (some (.var "first")),
      .exprStmt (.builtin .sstore _)] => true
  | _ => false

/-- Loop bodies are separate forwarding regions; facts never cross iterations. -/
def storageForwardingLoop : Block Op := yul% {
  for {} 1 {} {
    sstore(0, 7)
    let loaded := sload(0)
    sstore(1, loaded)
    break
  }
}

def hasForwardedLoopLoad : Block Op → Bool
  | [.forLoop _ _ _
      [.exprStmt (.builtin .sstore _),
       .letDecl ["loaded"] (some (.lit (.number 7))),
       .exprStmt (.builtin .sstore _), .break]] => true
  | _ => false

/-- An outer return slot assigned inside an inliner-style nested block carries
the loaded storage fact back across block restoration. -/
def storageForwardingScope : Block Op := yul% {
  let outer
  { outer := sload(0) }
  let copied := sload(0)
  sstore(1, copied)
}

def hasForwardedScopedLoad : Block Op → Bool
  | [.letDecl ["outer"] none,
      .block [.assign ["outer"] (.builtin .sload [.lit (.number 0)])],
      .letDecl ["copied"] (some (.var "outer")),
      .exprStmt (.builtin .sstore _)] => true
  | _ => false

/-- Rebinding checks the pre-assignment value before invalidating dependencies:
the cached `add(x, 1)` becomes the new value of `x` itself. -/
def storageForwardingRebind : Block Op := yul% {
  let x := 40
  sstore(0, add(x, 1))
  x := add(x, 1)
  let copied := sload(0)
  sstore(1, copied)
}

def hasForwardedReboundLoad : Block Op → Bool
  | [.letDecl ["x"] _, .exprStmt (.builtin .sstore _),
      .assign ["x"] _, .letDecl ["copied"] (some (.var "x")),
      .exprStmt (.builtin .sstore _)] => true
  | _ => false

/-- A fact represented by a direct block-local binding must not escape that
binding's `restore`. -/
def storageForwardingShadow : Block Op := yul% {
  { let inner := sload(0) }
  let copied := sload(0)
  sstore(1, copied)
}

def keepsLoadAfterLocalRestore : Block Op → Bool
  | [.block [.letDecl ["inner"] (some (.builtin .sload _))],
      .letDecl ["copied"] (some (.builtin .sload _)),
      .exprStmt (.builtin .sstore _)] => true
  | _ => false

/-- A *recursive* function: `fact(5) = 120` in slot 0. -/
def factorial : Block Op := yul% {
  function fact(n) -> f {
    f := 1
    if gt(n, 1) {
      f := mul(n, fact(sub(n, 1)))
    }
  }
  sstore(0, fact(5))
}

/-- `leave` returns early: `f(0) = 1` in slot 0, `f(7) = 2` in slot 1. -/
def leaveEarly : Block Op := yul% {
  function f(a) -> r {
    r := 1
    if eq(a, 0) { leave }
    r := 2
  }
  sstore(0, f(0))
  sstore(1, f(7))
}

/-- Functions calling functions, calls nested inside expressions and loop
conditions; a zero-return function used as a statement. -/
def nested : Block Op := yul% {
  function sq(x) -> y {
    y := mul(x, x)
  }
  function store(k, v) {
    sstore(k, v)
  }
  let acc := 0
  for { let i := 1 } lt(i, add(sq(2), 1)) { i := add(i, 1) } {
    acc := add(acc, sq(i))
  }
  store(0, acc)
}

/-- A `for` whose body declares locals and `break`s from inside a nested
block (the pops must unwind both the inner block and the body). -/
def breakNested : Block Op := yul% {
  let r := 0
  for { let i := 0 } lt(i, 100) { i := add(i, 1) } {
    let d := add(i, i)
    {
      let e := add(d, 1)
      if gt(e, 7) { r := e break }
    }
  }
  sstore(0, r)
}

/-- The `n`-th Fibonacci number into storage slot 0, iteratively — the same
loop as yul-semantics' `FibExample.fibContract`, but reading `n` and writing
the result through **storage** (`sload`/`sstore`) instead of calldata/memory,
so it lands inside the verified op set. Here `n = 10`, so slot 0 ends at
`fib 10 = 55`. -/
def fibStorage : Block Op := yul% {
  let n := 10
  let a := 0
  let b := 1
  for { let i := 0 } lt(i, n) { i := add(i, 1) } {
    let t := add(a, b)
    a := b
    b := t
  }
  sstore(0, a)
}

/-- Low-byte storage followed by an overlapping memory copy. `MCOPY` must read
its complete source from the old memory before writing the destination. -/
def byteAndOverlapCopy : Block Op := yul% {
  mstore(0,
    0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00)
  mstore8(0, 0xaa)
  mcopy(8, 0, 24)
  sstore(0, mload(0))
  sstore(1, mload(8))
}

/-- Sign extension covers a negative byte, a positive byte, and an index at
which the EVM operation is the identity. -/
def signExtendCases : Block Op := yul% {
  sstore(0, signextend(0, 0x80))
  sstore(1, signextend(0, 0x7f))
  sstore(2, signextend(32, 0x80))
}

/-- Record calldata size, then copy a range across a word boundary. The final
byte is deliberately beyond the input and must be zero-padded. -/
def calldataOps : Block Op := yul% {
  sstore(0, calldatasize())
  calldatacopy(31, 1, 3)
  sstore(1, mload(0))
  sstore(2, mload(32))
}

/-- Record return-data size, then copy three in-bounds bytes across a memory
word boundary. A zero-length copy from exactly the end of the return buffer is
also in bounds and must not expand memory at its maximum destination offset. -/
def returndataOps : Block Op := yul% {
  sstore(0, returndatasize())
  returndatacopy(31, 1, 3)
  sstore(1, mload(0))
  sstore(2, mload(32))
  sstore(3, msize())
  returndatacopy(not(0), 4, 0)
  sstore(4, msize())
}

/-- `msize` reports the active-memory high-water mark in bytes. This covers
word reads, byte writes, both ranges of `mcopy`, and the EVM rule that a
zero-length range does not expand memory even at the maximum offset. The
values stored in slots 0 through 4 are `0`, `64`, `128`, `256`, and `256`. -/
def memorySizeOps : Block Op := yul% {
  sstore(0, msize())
  pop(mload(32))
  sstore(1, msize())
  mstore8(96, 0)
  sstore(2, msize())
  mcopy(160, 224, 1)
  sstore(3, msize())
  calldatacopy(not(0), 0, 0)
  sstore(4, msize())
}

/-- Hash the three bytes `"abc"`, then record the memory expansion caused by
the read. The source interpreter is configured below with the target
semantics' concrete Keccak implementation. -/
def keccakOps : Block Op := yul% {
  mstore8(0, 0x61)
  mstore8(1, 0x62)
  mstore8(2, 0x63)
  sstore(0, keccak256(0, 3))
  sstore(1, msize())
}

/-- Account and transaction-context reads: the executing balance, another
account's balance, one in-range blob hash, and one out-of-range blob hash. -/
def accountAndBlobReads : Block Op := yul% {
  sstore(0, selfbalance())
  sstore(1, balance(1))
  sstore(2, blobhash(0))
  sstore(3, blobhash(1))
}

/-- External-account code and historical block reads. The copy starts one
byte into the external code and straddles a memory-word boundary. -/
def externalCodeAndBlockReads : Block Op := yul% {
  sstore(0, extcodesize(1))
  extcodecopy(1, 31, 1, 3)
  sstore(1, mload(0))
  sstore(2, mload(32))
  sstore(3, extcodehash(1))
  sstore(4, blockhash(7))
}

/-- Emit every LOG arity over the same two-byte memory slice. This checks
opcode selection, topic order, data extraction across a word boundary, and
the memory expansion caused by reading log data. -/
def logOps : Block Op := yul% {
  mstore8(31, 0xaa)
  mstore8(32, 0xbb)
  log0(31, 2)
  log1(31, 2, 0x11)
  log2(31, 2, 0x21, 0x22)
  log3(31, 2, 0x31, 0x32, 0x33)
  log4(31, 2, 0x41, 0x42, 0x43, 0x44)
}

/-- All four open-world call forms. Execution needs an external model, but
compilation and opcode selection are independent of the callee code. -/
def externalCalls : Block Op := yul% {
  let a := call(100000, 1, 0, 0, 0, 0, 0)
  let b := callcode(100000, 2, 0, 0, 0, 0, 0)
  let c := delegatecall(100000, 3, 0, 0, 0, 0)
  let d := staticcall(100000, 4, 0, 0, 0, 0)
  sstore(0, add(add(a, b), add(c, d)))
}

/-- Both open-world creation forms. The copied byte is deliberately arbitrary
init code: compilation and correctness depend only on the realization
interface, not on knowing which contract it deploys. -/
def externalCreates : Block Op := yul% {
  mstore8(0, 0)
  let a := create(0, 0, 1)
  let b := create2(0, 0, 1, 7)
  sstore(0, add(a, b))
}

/-- Issue #61's all-live pressure case.  The left-associated sum makes `v0`
fall beyond `DUP16`; the smart layout preserves the right-to-left leaf order
while reassociating the tree, so all nine locals remain reachable. -/
def stackPressure : Block Op := yul% {
  function f(x) -> r {
    let v0 := add(x, 0)
    let v1 := add(x, 1)
    let v2 := add(x, 2)
    let v3 := add(x, 3)
    let v4 := add(x, 4)
    let v5 := add(x, 5)
    let v6 := add(x, 6)
    let v7 := add(x, 7)
    let v8 := add(x, 8)
    r := add(add(add(add(add(add(add(add(v0, v1), v2), v3), v4), v5), v6), v7), v8)
  }
  sstore(0, f(7))
}

def optimizedStackPressure : Block Op :=
  (Optimizer.optimizerPipeline
    (calls := YulSemantics.EVM.ExternalCalls.none)
    (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)).run stackPressure

def laidOutStackPressure : Block Op :=
  Optimizer.stackLayoutBlock optimizedStackPressure

/-- A result slot that is shallow on block entry but hidden below fourteen
locals at the terminal write. The tail-carrier policy recognizes that the
first local dominates the region and is the only value needed after it. -/
def tailCarrierCandidate : Block Op := yul% {
  let carrier := 1
  let a0 := 0
  let a1 := 1
  let a2 := 2
  let a3 := 3
  let a4 := 4
  let a5 := 5
  let a6 := 6
  let a7 := 7
  let a8 := 8
  let a9 := 9
  let a10 := 10
  let a11 := 11
  let a12 := 12
  let a13 := 13
  r := carrier
  leave
}

/-- A terminal world-state update. The unreachable store makes the halting behavior observable
in addition to the balance transfer and scheduled-destruction record checked below. -/
def selfdestructOps : Block Op := yul% {
  selfdestruct(1)
  sstore(0, 0xff)
}

#guard (compileProgram sumLoop).isSome
#guard (compileProgram breakContinue).isSome
#guard (compileProgram funCall).isSome
#guard (compileProgram factorial).isSome
#guard (compileProgram leaveEarly).isSome
#guard (compileProgram nested).isSome
#guard (compileProgram breakNested).isSome
#guard (compileProgram fibStorage).isSome
#guard (compile sumLoop).isSome
-- `factorial` is recursive; the `compile` stack-overflow gate (`StackBound`) rejects it, as the
-- analysis cannot bound the recursion depth statically. `compileProgram` (no gate) still succeeds.
#guard (compile factorial).isNone
#guard (compile fibStorage).isSome

-- The Asm peephole fires on `multiRet3`: the top return slot's constant
-- assignment (`push v; swap1; pop` → `pop; push v`, one byte and one `SWAP1`
-- cheaper) plus one dead return label. The `agreeOn`/`runYul` checks below
-- confirm behavior is unchanged.
#guard ((compileProgram multiRet3).map fun asm =>
    codeSize (optimizeAsm asm) + 2 == codeSize asm) = some true
-- Branch inversion: `breakContinue`'s two guarded control statements
-- (`if … { continue }`, `if … { break }`) each compile to
-- `jumpi l; jump m; label l` → `op iszero; jumpi m; label l` (dropping the
-- `labelWidth+2`-byte address push and reordering); the source conditions end
-- in `eq`, whose `iszero`d inversions then cancel against the source-level
-- `iszero`s in the follow-up round (double-`iszero` elimination), and the
-- orphaned labels drop. Under minimal-width label pushes the aggregate saving
-- is 12 bytes.
#guard ((compileProgram breakContinue).map fun asm =>
    codeSize (optimizeAsm asm) + 12 == codeSize asm) = some true
-- A switch dispatch tests each case with `eq`, inverted into the
-- fall-through `jumpi` — exactly the eq-sub window: each of the three case
-- guards drops its `iszero` for a `sub` (one byte and three gas apiece).
#guard ((compileProgram switchMatch).map fun asm =>
    codeSize (optimizeAsm asm) + 3 == codeSize asm) = some true
#guard (compile byteAndOverlapCopy).isSome
#guard (compileProgram signExtendCases).isSome
#guard (compile signExtendCases).isSome
#guard (compileProgram calldataOps).isSome
#guard (compile calldataOps).isSome
#guard (compileProgram returndataOps).isSome
#guard (compile returndataOps).isSome
#guard (compileProgram memorySizeOps).isSome
#guard (compile memorySizeOps).isSome
#guard (compileProgram keccakOps).isSome
#guard (compile keccakOps).isSome
#guard (compileProgram accountAndBlobReads).isSome
#guard (compile accountAndBlobReads).isSome
#guard (compileProgram externalCodeAndBlockReads).isSome
#guard (compile externalCodeAndBlockReads).isSome
#guard (compileProgram logOps).isSome
#guard (compile logOps).isSome
#guard (compileProgram externalCalls).isSome
#guard (compile externalCalls).isSome
#guard (compileProgram externalCreates).isSome
#guard (compile externalCreates).isSome
#guard (compileProgram selfdestructOps).isSome
#guard (compile selfdestructOps).isSome
#guard !(compile optimizedStackPressure).isSome
#guard (compile laidOutStackPressure).isSome
#guard (Optimizer.scopeTailHere ["x", "r"] tailCarrierCandidate).isSome

/-! ### The upstream Fibonacci contract

`YulSemantics.FibExample.fibContract` (the `n`-th Fibonacci contract proved
correct in yul-semantics) reads `n` from **calldata** (`calldataload`),
computes `fib n` in a `for` loop, writes it to **memory** (`mstore`), and
`return`s it. With `calldataload` and `mstore` now in the verified op set
(`opTable`) it compiles all the way to bytecode. -/
#guard (compileProgram FibExample.fibContract).isSome
#guard (compile FibExample.fibContract).isSome

/-! ### Differential execution: Yul interpreter vs. compiled bytecode -/

/-- Run the Yul-side interpreter to a final machine state. -/
def runYul (fuel : Nat) (prog : Block Op) : Option EvmState :=
  match Interp.run YulSemantics.EVM.exec fuel prog EvmState.init with
  | .ok (_, st, _) => some st
  | _ => none

/-- A minimal EVM state executing `code` on Osaka with plenty of gas. -/
def evmInit (code : ByteArray) : EvmSemantics.EVM.State :=
  let env : EvmSemantics.ExecutionEnv := Inhabited.default
  let s : EvmSemantics.EVM.State := Inhabited.default
  { s with
      pc := 0
      stack := []
      execLength := 0
      halt := .Running
      callStack := []
      gasAvailable := 100000000
      executionEnv := { env with
          code := code
          fork := .Osaka
          permitStateMutation := true } }

/-- Drive `stepF` until done (fuel-bounded). -/
def runEvm : Nat → EvmSemantics.EVM.State → EvmSemantics.EVM.State
  | 0, s => s
  | fuel + 1, s =>
    if s.isDone then s else runEvm fuel (EvmSemantics.EVM.stepF s)

/-- A representation-independent view of source logs for differential
comparison: emitting address, ordered topics, and exact data bytes. -/
def yulLogView (st : EvmState) : List (Nat × List Nat × List UInt8) :=
  st.logs.map fun entry =>
    (st.env.address.toNat, entry.topics.map BitVec.toNat, entry.data)

/-- The corresponding view of the target EVM log series. -/
def evmLogView (s : EvmSemantics.EVM.State) : List (Nat × List Nat × List UInt8) :=
  s.substate.logSeries.toList.map fun entry =>
    (entry.address.toUInt256.toNat, entry.topics.toList.map EvmSemantics.UInt256.toNat,
      entry.data.toList)

/-- Compile `prog`, run both sides with matching calldata and return-data
buffers, and compare the buffers, active-memory size, full log series, and
selected storage values (plus that the EVM run actually finished without an
exception). -/
def agreeOnWithInputs (prog : Block Op) (cd rd : List UInt8) (keys : List Nat) : Bool :=
  let yst0 : EvmState :=
    { EvmState.init with
      env := { EvmState.init.env with calldata := cd, keccakOf := targetKeccakOracle }
      returndata := rd }
  match compile prog, Interp.run YulSemantics.EVM.exec 100000 prog yst0 with
  | some is, .ok (_, yst, _) =>
      let s0 := evmInit (assemble is)
      let s := runEvm 100000
        { s0 with
          executionEnv := { s0.executionEnv with calldata := ⟨cd.toArray⟩ }
          returnData := ⟨rd.toArray⟩ }
      s.isDone
        && (s.halt matches .Success)
        && yst.returndata == s.returnData.toList
        && yst.activeWords.toNat == s.activeWords.toNat
        && yulLogView yst == evmLogView s
        && keys.all (fun k =>
          (yst.storage (BitVec.ofNat 256 k)).toNat
            == ((s.accountMap s.executionEnv.address).storage.get
                  (EvmSemantics.UInt256.ofNat k)).toNat)
  | _, _ => false

/-- Calldata-only specialization used by calldata examples. -/
def agreeOnWithCalldata (prog : Block Op) (cd : List UInt8) (keys : List Nat) : Bool :=
  agreeOnWithInputs prog cd [] keys

/-- Empty-calldata specialization used by the existing storage examples. -/
def agreeOn (prog : Block Op) (keys : List Nat) : Bool :=
  agreeOnWithCalldata prog [] keys

#guard agreeOn sumLoop [0]
#guard agreeOn breakContinue [0]
#guard agreeOn switchMatch [0]
#guard agreeOn switchDefault [0]
#guard agreeOn multiRet [0, 1]
#guard agreeOn multiAssign [0, 1]
#guard compile optimizedIdentityHelpers |>.isSome
#guard agreeOn optimizedIdentityHelpers [0, 1]
#guard compile optimizedWrapperHelpers |>.isSome
#guard agreeOn optimizedWrapperHelpers [0, 1]
#guard agreeOn wrapperHelpers [0, 1]
#guard hasForwardedStorageLoads (Optimizer.storageForwardBlock storageForwarding)
#guard hasForwardedLoopLoad (Optimizer.storageForwardBlock storageForwardingLoop)
#guard hasForwardedScopedLoad (Optimizer.storageForwardBlock storageForwardingScope)
#guard hasForwardedReboundLoad (Optimizer.storageForwardBlock storageForwardingRebind)
#guard keepsLoadAfterLocalRestore (Optimizer.storageForwardBlock storageForwardingShadow)
#guard (Optimizer.sfAssign [] [] ["missing"]
  (.builtin .sload [.lit (.number 0)])).2 == []
#guard compile ((Optimizer.storageForward
  (calls := YulSemantics.EVM.ExternalCalls.none)
  (creates := YulSemantics.EVM.ExternalCreates.none) (gasOracle := YulSemantics.EVM.ExternalGas.any)).run storageForwarding) |>.isSome
#guard agreeOn storageForwarding [0, 1, 2]
#guard agreeOn storageForwardingLoop [0, 1]
#guard agreeOn storageForwardingScope [0, 1]
#guard agreeOn storageForwardingRebind [0, 1]
#guard agreeOn storageForwardingShadow [0, 1]
#guard agreeOn multiRet3 [0, 1, 2]
#guard agreeOn funCall [0]
-- `factorial` (recursive) is rejected by the `compile` overflow gate, so it has no bytecode to
-- run through the EVM; its interpreter-level behaviour is still checked below (`runYul`).
#guard agreeOn leaveEarly [0, 1]
#guard agreeOn nested [0]
#guard agreeOn breakNested [0]
#guard agreeOn fibStorage [0]
#guard agreeOn byteAndOverlapCopy [0, 1]
#guard agreeOn signExtendCases [0, 1, 2]
#guard agreeOnWithCalldata calldataOps [0xaa, 0xbb, 0xcc] [0, 1, 2]
#guard agreeOnWithInputs returndataOps [] [0xaa, 0xbb, 0xcc, 0xdd] [0, 1, 2, 3, 4]
#guard agreeOn memorySizeOps [0, 1, 2, 3, 4]
#guard agreeOn keccakOps [0, 1]
#guard agreeOn logOps []
#guard agreeOn laidOutStackPressure [0]

/-- Differential check with the source's abstract balance/blob oracles and the
target's concrete account map/blob list initialized to matching values. -/
def agreeAccountAndBlobReads : Bool :=
  let ySelf : BitVec 256 := BitVec.ofNat 256 0x22223333
  let yOther : BitVec 256 := BitVec.ofNat 256 0x22222222
  let yBlob : BitVec 256 := BitVec.ofNat 256 0x123456
  let yst0 : EvmState :=
    { EvmState.init with env := { EvmState.init.env with
        selfBalance := ySelf
        balanceOf := fun a => if a = 1 then yOther else 0
        blobHashOf := fun i => if i = 0 then yBlob else 0 } }
  match compile accountAndBlobReads,
      Interp.run YulSemantics.EVM.exec 100000 accountAndBlobReads yst0 with
  | some is, .ok (_, yst, _) =>
      let s0 := evmInit (assemble is)
      let selfAccount : EvmSemantics.Account :=
        { EvmSemantics.Account.empty with balance := EvmSemantics.UInt256.ofNat ySelf.toNat }
      let otherAccount : EvmSemantics.Account :=
        { EvmSemantics.Account.empty with balance := EvmSemantics.UInt256.ofNat yOther.toNat }
      let otherAddress := EvmSemantics.AccountAddress.ofUInt256 (EvmSemantics.UInt256.ofNat 1)
      let accounts := EvmSemantics.AccountMap.empty
        |>.set s0.executionEnv.address selfAccount
        |>.set otherAddress otherAccount
      let s := runEvm 100000 { s0 with
        accountMap := accounts
        executionEnv := { s0.executionEnv with
          blobVersionedHashes := #[EvmSemantics.UInt256.ofNat yBlob.toNat] } }
      s.isDone
        && (s.halt matches .Success)
        && [0, 1, 2, 3].all (fun k =>
          (yst.storage (BitVec.ofNat 256 k)).toNat
            == ((s.accountMap s.executionEnv.address).storage.get
                  (EvmSemantics.UInt256.ofNat k)).toNat)
  | _, _ => false

#guard agreeAccountAndBlobReads

/-- Differential check with an external account's code, its concrete
EIP-161-aware target code hash, and a historical block hash initialized
consistently on both sides. -/
def agreeExternalCodeAndBlockReads : Bool :=
  let extBytes : List UInt8 := [0xaa, 0xbb, 0xcc, 0xdd, 0xee]
  let yBlock : BitVec 256 := BitVec.ofNat 256 0x123456
  let extAccount : EvmSemantics.Account :=
    { EvmSemantics.Account.empty with code := ⟨extBytes.toArray⟩ }
  let yst0 : EvmState :=
    { EvmState.init with env := { EvmState.init.env with
        extCodeOf := fun a => if a = 1 then extBytes else []
        keccakOf := targetKeccakOracle
        blockHashOf := fun n => if n = 7 then yBlock else 0 } }
  match compile externalCodeAndBlockReads,
      Interp.run YulSemantics.EVM.exec 100000 externalCodeAndBlockReads yst0 with
  | some is, .ok (_, yst, _) =>
      let s0 := evmInit (assemble is)
      let extAddress :=
        EvmSemantics.AccountAddress.ofUInt256 (EvmSemantics.UInt256.ofNat 1)
      let header := { s0.executionEnv.header with
        blockHash := fun n =>
          if n = EvmSemantics.UInt256.ofNat 7
          then EvmSemantics.UInt256.ofNat yBlock.toNat else 0 }
      let s := runEvm 100000 { s0 with
        accountMap := EvmSemantics.AccountMap.empty.set extAddress extAccount
        executionEnv := { s0.executionEnv with header := header } }
      s.isDone
        && (s.halt matches .Success)
        && yst.activeWords.toNat == s.activeWords.toNat
        && [0, 1, 2, 3, 4].all (fun k =>
          (yst.storage (BitVec.ofNat 256 k)).toNat
            == ((s.accountMap s.executionEnv.address).storage.get
                  (EvmSemantics.UInt256.ofNat k)).toNat)
  | _, _ => false

#guard agreeExternalCodeAndBlockReads

/-- End-to-end `SELFDESTRUCT` comparison, including both EIP-6780 same-beneficiary branches.
`createdThisTx` selects whether the transaction-initial target world contains the executing
contract; the current world always does. -/
def agreeSelfdestruct (beneficiary : Nat) (createdThisTx : Bool) : Bool :=
  let self : BitVec 256 := 0
  let ben : BitVec 256 := BitVec.ofNat 256 beneficiary
  let initialBalance (a : BitVec 256) : BitVec 256 :=
    if YulSemantics.EVM.accountKey a = YulSemantics.EVM.accountKey self then 7
    else if YulSemantics.EVM.accountKey a = YulSemantics.EVM.accountKey ben then 3
    else 0
  let yst0 : EvmState :=
    { EvmState.init with env := { EvmState.init.env with
        address := self
        selfBalance := 7
        balanceOf := initialBalance
        createdThisTx := createdThisTx } }
  match compile selfdestructOps,
      Interp.run YulSemantics.EVM.exec 100000 selfdestructOps yst0 with
  | some is, .ok (_, yst, _) =>
      let code := assemble is
      let s0 := evmInit code
      let selfAddr := s0.executionEnv.address
      let benAddr := EvmSemantics.AccountAddress.ofNat beneficiary
      let selfAccount : EvmSemantics.Account :=
        { EvmSemantics.Account.empty with
          balance := EvmSemantics.UInt256.ofNat 7
          code := code }
      let benAccount : EvmSemantics.Account :=
        { EvmSemantics.Account.empty with balance := EvmSemantics.UInt256.ofNat 3 }
      let accounts :=
        if benAddr = selfAddr then
          EvmSemantics.AccountMap.empty.set selfAddr selfAccount
        else
          EvmSemantics.AccountMap.empty
            |>.set selfAddr selfAccount
            |>.set benAddr benAccount
      let original :=
        if createdThisTx then EvmSemantics.AccountMap.empty
        else EvmSemantics.AccountMap.empty.set selfAddr selfAccount
      let s := runEvm 100000 { s0 with
        accountMap := accounts
        substate := { s0.substate with originalAccountMap := original } }
      s.isDone
        && (s.halt matches .Success)
        && yst.halted == some (.selfdestruct, [])
        && yst.env.balanceOf self == (s.accountMap selfAddr).balance.toNat
        && yst.env.balanceOf ben == (s.accountMap benAddr).balance.toNat
        && yst.selfdestructs.map (fun entry =>
          (YulSemantics.EVM.accountKey entry.1, entry.2)) ==
          s.substate.selfDestructList.toList.map (fun a =>
            (a.val, !(s.substate.originalAccountMap a).isContract))
        && yst.storage 0 == 0
        && (s.accountMap selfAddr).storage 0 == 0
  | _, _ => false

#guard agreeSelfdestruct 1 false
#guard agreeSelfdestruct 0 false
#guard agreeSelfdestruct 0 true

/-- Compile `prog`, run both sides with `cd` as calldata, and compare the
returned byte payload (for contracts that halt via `return`, like the
calldata/memory Fibonacci contract). -/
def agreeReturn (prog : Block Op) (cd : List UInt8) : Bool :=
  let yst0 : EvmState :=
    { EvmState.init with env := { EvmState.init.env with
        calldata := cd, keccakOf := targetKeccakOracle } }
  match compile prog, Interp.run YulSemantics.EVM.exec 100000 prog yst0 with
  | some is, .ok (_, yst, _) =>
      let s0 := evmInit (assemble is)
      let s := runEvm 100000
        { s0 with executionEnv := { s0.executionEnv with calldata := ⟨cd.toArray⟩ } }
      s.isDone
        && (match yst.halted, s.halt with
            | some (.ret, ybytes), .Returned => ybytes == s.hReturn.toList
            | _, _ => false)
  | _, _ => false

-- The compiled calldata/memory Fibonacci contract returns the same bytes as
-- the Yul interpreter, for several inputs (`fib 0/1/7/10`).
#guard agreeReturn FibExample.fibContract (List.replicate 31 0 ++ [0])
#guard agreeReturn FibExample.fibContract (List.replicate 31 0 ++ [1])
#guard agreeReturn FibExample.fibContract (List.replicate 31 0 ++ [7])
#guard agreeReturn FibExample.fibContract (List.replicate 31 0 ++ [10])

-- The Yul interpreter's view of the expected values (documentation).
#guard (runYul 100000 sumLoop).map (fun st => (st.storage 0).toNat) = some 15
#guard (runYul 100000 breakContinue).map (fun st => (st.storage 0).toNat) = some 12
#guard (runYul 100000 switchMatch).map (fun st => (st.storage 0).toNat) = some 21
#guard (runYul 100000 switchDefault).map (fun st => (st.storage 0).toNat) = some 99
#guard (runYul 100000 multiRet).map (fun st => (st.storage 0).toNat) = some 3
#guard (runYul 100000 multiRet).map (fun st => (st.storage 1).toNat) = some 2
#guard (runYul 100000 multiAssign).map (fun st => (st.storage 0).toNat) = some 2
#guard (runYul 100000 multiAssign).map (fun st => (st.storage 1).toNat) = some 1
#guard (runYul 100000 multiRet3).map (fun st => (st.storage 2).toNat) = some 9
#guard (runYul 100000 funCall).map (fun st => (st.storage 0).toNat) = some 42
#guard (runYul 100000 factorial).map (fun st => (st.storage 0).toNat) = some 120
#guard (runYul 100000 leaveEarly).map
    (fun st => ((st.storage 0).toNat, (st.storage 1).toNat)) = some (1, 2)
#guard (runYul 100000 nested).map (fun st => (st.storage 0).toNat) = some 30
#guard (runYul 100000 breakNested).map (fun st => (st.storage 0).toNat) = some 9
#guard (runYul 100000 fibStorage).map (fun st => (st.storage 0).toNat) = some 55
#guard (runYul 100000 signExtendCases).map
    (fun st => ((st.storage 0).toInt, (st.storage 1).toNat, (st.storage 2).toNat)) =
      some (-128, 127, 128)
#guard (runYul 100000 memorySizeOps).map
    (fun st => ((st.storage 0).toNat, (st.storage 1).toNat,
      (st.storage 2).toNat, (st.storage 3).toNat, (st.storage 4).toNat)) =
      some (0, 64, 128, 256, 256)

end YulEvmCompiler.Examples
