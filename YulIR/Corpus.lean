import YulIR
import YulSemantics.Syntax

/-!
# YulIR.Corpus — hand-picked test programs for the IR baseline

Fifty small Yul programs spanning arithmetic, bitwise/comparison, storage/transient,
memory + keccak, calldata, control flow (if/switch/loops), functions (multi-return,
nested, recursive, `leave`), and halting (`return`/`revert`/`stop`). Several are
deliberate future-optimization targets (`arith/cse-candidate`, `arith/const-fold`,
`arith/identity`, `storage/redundant`, `storage/forward`, `fn/inlinable`) so the
baseline will visibly improve as passes land.

Programs avoid code-reading (`codesize`/`codecopy`) and external-interaction built-ins
(`call*`/`create*`/`selfdestruct`), whose results legitimately differ between two
distinct compilations or need an external oracle.
-/

namespace YulIR.Corpus

open YulSemantics EVM

/-- The corpus: `(name, program)` pairs, in a stable order. -/
def corpus : List (String × YulSemantics.Block EVM.Op) :=
  [ ("arith/add", yul% { sstore(0, add(3, 4)) })
  , ("arith/sub-mul", yul% { sstore(0, mul(sub(10, 3), 2)) })
  , ("arith/div-mod", yul% {
      sstore(0, div(100, 7))
      sstore(1, mod(100, 7)) })
  , ("arith/addmod-mulmod", yul% {
      sstore(0, addmod(5, 7, 3))
      sstore(1, mulmod(5, 7, 3)) })
  , ("arith/exp", yul% { sstore(0, exp(2, 8)) })
  , ("arith/signextend", yul% { sstore(0, signextend(0, 255)) })
  , ("arith/nested-deep", yul% {
      sstore(0, add(mul(2, add(3, 4)), sub(10, div(20, 4)))) })
  , ("arith/cse-candidate", yul% {
      let a := add(sload(0), sload(1))
      let b := add(sload(0), sload(1))
      sstore(2, add(a, b)) })
  , ("arith/const-fold", yul% { sstore(0, add(add(1, 2), add(3, 4))) })
  , ("arith/identity", yul% {
      let x := sload(0)
      sstore(1, add(x, 0))
      sstore(2, mul(x, 1)) })
  , ("bitwise/and-or-xor", yul% {
      sstore(0, and(12, 10))
      sstore(1, or(12, 10))
      sstore(2, xor(12, 10)) })
  , ("bitwise/not", yul% { sstore(0, not(0)) })
  , ("bitwise/shifts", yul% {
      sstore(0, shl(4, 1))
      sstore(1, shr(4, 256))
      sstore(2, sar(1, not(0))) })
  , ("cmp/lt-gt-eq", yul% {
      sstore(0, lt(3, 4))
      sstore(1, gt(3, 4))
      sstore(2, eq(3, 3)) })
  , ("cmp/iszero", yul% { sstore(0, iszero(0)) })
  , ("storage/roundtrip", yul% {
      sstore(5, 42)
      sstore(6, sload(5)) })
  , ("storage/redundant", yul% {
      sstore(0, 1)
      sstore(0, 2) })
  , ("storage/forward", yul% {
      sstore(0, 7)
      let y := sload(0)
      sstore(1, y) })
  , ("storage/multi", yul% {
      sstore(0, 1)
      sstore(1, 2)
      sstore(2, 3) })
  , ("transient/roundtrip", yul% {
      tstore(0, 99)
      sstore(0, tload(0)) })
  , ("mem/store-load", yul% {
      mstore(0, 123)
      sstore(0, mload(0)) })
  , ("mem/mstore8", yul% {
      mstore8(0, 171)
      sstore(0, mload(0)) })
  , ("mem/keccak", yul% {
      mstore(0, 1)
      mstore(32, 2)
      sstore(0, keccak256(0, 64)) })
  , ("mem/mcopy", yul% {
      mstore(0, 57005)
      mcopy(64, 0, 32)
      sstore(0, mload(64)) })
  , ("mem/msize", yul% {
      mstore(96, 1)
      sstore(0, msize()) })
  , ("mem/order-sensitive", yul% {
      mstore(0, calldataload(0))
      mstore(32, calldataload(32))
      sstore(0, keccak256(0, 64)) })
  , ("calldata/load", yul% { sstore(0, calldataload(0)) })
  , ("calldata/size", yul% { sstore(0, calldatasize()) })
  , ("calldata/copy", yul% {
      calldatacopy(0, 0, 32)
      sstore(0, mload(0)) })
  , ("env/caller-timestamp", yul% {
      sstore(0, caller())
      sstore(1, timestamp()) })
  , ("if/true", yul% { if 1 { sstore(0, 1) } })
  , ("if/false", yul% {
      if 0 { sstore(0, 1) }
      sstore(1, 2) })
  , ("if/calldata", yul% { if calldataload(0) { sstore(0, 1) } })
  , ("switch/cases", yul% {
      switch calldataload(0)
      case 0 { sstore(0, 10) }
      case 1 { sstore(0, 11) }
      default { sstore(0, 12) } })
  , ("switch/no-default", yul% {
      switch 2
      case 1 { sstore(0, 1) }
      case 2 { sstore(0, 2) } })
  , ("nested-if", yul% {
      let x := calldataload(0)
      if x { if lt(x, 100) { sstore(0, x) } } })
  , ("loop/count", yul% {
      let s := 0
      for { let i := 0 } lt(i, 10) { i := add(i, 1) } { s := add(s, i) }
      sstore(0, s) })
  , ("loop/break", yul% {
      let s := 0
      for { let i := 0 } 1 { i := add(i, 1) } {
        if gt(i, 5) { break }
        s := add(s, i)
      }
      sstore(0, s) })
  , ("loop/continue", yul% {
      let s := 0
      for { let i := 0 } lt(i, 10) { i := add(i, 1) } {
        if mod(i, 2) { continue }
        s := add(s, i)
      }
      sstore(0, s) })
  , ("loop/nested", yul% {
      let s := 0
      for { let i := 0 } lt(i, 3) { i := add(i, 1) } {
        for { let j := 0 } lt(j, 3) { j := add(j, 1) } {
          s := add(s, mul(i, j))
        }
      }
      sstore(0, s) })
  , ("loop/sum-calldata", yul% {
      let s := 0
      for { let i := 0 } lt(i, 3) { i := add(i, 1) } {
        s := add(s, calldataload(mul(i, 32)))
      }
      sstore(0, s) })
  , ("fn/simple", yul% {
      function f(a, b) -> r { r := add(a, b) }
      sstore(0, f(3, 4)) })
  , ("fn/multi-return", yul% {
      function two() -> a, b { a := 1 b := 2 }
      let x, y := two()
      sstore(0, add(x, y)) })
  , ("fn/nested-call", yul% {
      function inc(a) -> r { r := add(a, 1) }
      sstore(0, inc(inc(inc(0)))) })
  , ("fn/recursive", yul% {
      function fact(n) -> r {
        switch n
        case 0 { r := 1 }
        default { r := mul(n, fact(sub(n, 1))) }
      }
      sstore(0, fact(5)) })
  , ("fn/leave", yul% {
      function f(a) -> r {
        r := a
        if gt(a, 10) { leave }
        r := mul(a, 2)
      }
      sstore(0, f(3))
      sstore(1, f(20)) })
  , ("fn/inlinable", yul% {
      function double(x) -> r { r := mul(x, 2) }
      sstore(0, double(21)) })
  , ("halt/return", yul% {
      mstore(0, 42)
      return(0, 32) })
  , ("halt/revert-cond", yul% {
      if calldataload(0) { revert(0, 0) }
      sstore(0, 1) })
  , ("halt/stop", yul% {
      sstore(0, 1)
      stop() })
  -- simplification targets: constant folding + algebraic identities
  , ("simplify/const-fold", yul% {
      sstore(0, add(mul(3, 4), 5))
      sstore(1, shl(2, 1))
      sstore(2, and(255, 4096)) })
  , ("simplify/identities", yul% {
      let x := calldataload(0)
      sstore(0, add(x, 0))
      sstore(1, mul(x, 1))
      sstore(2, mul(x, 0))
      sstore(3, sub(x, x))
      sstore(4, or(x, 0))
      sstore(5, xor(x, x))
      sstore(6, div(x, 1))
      sstore(7, shl(0, x)) })
  -- dead-store (unused-assignment) targets
  , ("deadstore/reassign", yul% {
      let x := calldataload(0)
      x := add(x, 1)
      x := calldataload(32)
      sstore(0, x) })
  , ("deadstore/branch", yul% {
      let x := calldataload(0)
      if calldataload(32) { x := 5 }
      x := 9
      sstore(0, x) })
  , ("deadstore/loop", yul% {
      let s := 0
      for { let i := 0 } lt(i, 3) { i := add(i, 1) } {
        let t := mul(i, 2)
        s := add(s, t)
      }
      sstore(0, s) })
  -- regression: a store before `break`/`continue` is live via the loop's exit/back edge
  , ("deadstore/break-live", yul% {
      let x := 1
      for { } calldataload(0) { } {
        if callvalue() { x := 2 break }
        x := 3
      }
      mstore(x, 66) })
  , ("deadstore/continue-live", yul% {
      let x := 1
      for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
        if eq(i, 2) { x := add(x, 10) continue }
        x := add(x, 1)
      }
      sstore(0, x) })
  -- store-elimination targets: an overwritten sstore/mstore/tstore is dead
  , ("storeElim/storage-overwrite", yul% {
      sstore(0, calldataload(0))
      sstore(0, calldataload(32)) })
  , ("storeElim/storage-triple", yul% {
      sstore(3, calldataload(0))
      sstore(3, calldataload(32))
      sstore(3, calldataload(64)) })
  , ("storeElim/mem-overwrite", yul% {
      mstore(64, calldataload(0))
      mstore(64, calldataload(32))
      sstore(0, mload(64)) })
  , ("storeElim/trans-overwrite", yul% {
      tstore(7, calldataload(0))
      tstore(7, calldataload(32))
      sstore(0, tload(7)) })
  -- store-elimination must NOT fire when the value is observable
  , ("storeElim/keep-read-between", yul% {
      sstore(0, calldataload(0))
      let z := sload(0)
      sstore(0, calldataload(32))
      sstore(1, z) })
  , ("storeElim/keep-conditional", yul% {
      sstore(0, 1)
      if calldataload(0) { sstore(0, 2) }
      sstore(1, sload(0)) })
  , ("storeElim/keep-mutated-key", yul% {
      let k := calldataload(0)
      sstore(k, 1)
      k := calldataload(32)
      sstore(k, 2)
      sstore(100, sload(0)) })
  , ("storeElim/keep-before-terminator", yul% {
      sstore(0, calldataload(0))
      if calldataload(32) { return(0, 0) }
      sstore(0, calldataload(64)) })
  , ("storeElim/mem-keep-across-keccak", yul% {
      mstore(0, calldataload(0))
      let h := keccak256(0, 32)
      mstore(0, calldataload(32))
      sstore(0, h) }) ]

end YulIR.Corpus
