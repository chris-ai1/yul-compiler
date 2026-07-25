import YulEvmCompilerTests.InterpreterFixture
set_option warningAsError true
/-!
# Differential execution against solc

Execute bytecode emitted for the same Yul source by this compiler and by solc
inside the same `evm-semantics` environment. The observation deliberately
ignores bytecode, program counters, operand stacks, remaining gas, zero-only
memory expansion, and gas-metering artifacts such as the SSTORE refund counter:
those may differ between correct compilers, and the gas-free `yul-semantics`
source does not model them. It compares termination, returned/revert bytes,
returndata, nonzero memory, account existence/nonces/balances/storage, logs, and
self-destructs — the observable *results*, not gas.

Each program runs from Solidity's interpreter-test default environment, a
fixed patterned state, and four states derived deterministically from its
fixture name. The generated states exercise calldata boundaries plus varied
call values and persistent/transient storage without making the moving corpus
non-reproducible.
-/

namespace YulEvmCompilerTests.SolcDifferential

open EvmSemantics
open YulEvmCompilerTests.InterpreterFixture

structure ObservedLog where
  address : AccountAddress
  topics : Array UInt256
  payload : ByteArray
  deriving BEq

structure ObservedAccount where
  address : AccountAddress
  nonce : UInt256
  balance : UInt256
  hasCode : Bool
  storage : Array Entry
  transientStorage : Array Entry
  deriving BEq, Repr

structure Observation where
  halt : HaltKind
  output : ByteArray
  returnData : ByteArray
  memory : Array Entry
  accounts : Array ObservedAccount
  logs : Array ObservedLog
  selfDestructs : Array AccountAddress
  deriving BEq

private def word (n : Nat) : UInt256 := UInt256.ofNat n

/-- Stable fixture-name hash used for generated states. This deliberately
avoids the runtime's implementation-dependent hash table hash, so a failure
always reproduces from its checked-in relative path. -/
def fixtureSeed (name : String) : Nat :=
  name.toList.foldl
    (fun hash char => (hash * 16777619 + char.toNat) % (2 ^ 64))
    2166136261

private def mixSeed (seed salt : Nat) : Nat :=
  (seed * 1664525 + salt * 1013904223 + 0x9e3779b9) % (2 ^ 64)

private def sortEntries (entries : Array Entry) : Array Entry :=
  entries.qsort (fun a b => a.key.toNat < b.key.toNat)

private def storageEntries (storage : Storage) : Array Entry :=
  storage.toList.foldl (init := #[]) fun entries (key, value) =>
    if value.toNat == 0 then entries else entries.push { key, value }
  |> sortEntries

private def accountObservation
    (executingAddress address : AccountAddress) (account : Account) : ObservedAccount :=
  {
    address
    nonce := account.nonce
    balance := account.balance
    -- The executing account necessarily contains the compiler output, whose
    -- encoding and even empty-program representation may differ. Code created
    -- at other addresses is still observed by presence, but not by exact bytes.
    hasCode := address != executingAddress && account.code.size != 0
    storage := storageEntries account.storage
    transientStorage := storageEntries account.tstorage
  }

private def accountIsObservable (account : ObservedAccount) : Bool :=
  account.nonce.toNat != 0 || account.balance.toNat != 0 || account.hasCode ||
    !account.storage.isEmpty || !account.transientStorage.isEmpty

private def observedAccounts (state : EVM.State) : Array ObservedAccount :=
  let accounts := state.accountMap.toList.foldl (init := #[]) fun accounts (address, account) =>
    let observed := accountObservation state.executionEnv.address address account
    if accountIsObservable observed then accounts.push observed else accounts
  accounts.qsort (fun a b => a.address.val < b.address.val)

private def observedLogs (state : EVM.State) : Array ObservedLog :=
  state.substate.logSeries.map fun entry =>
    { address := entry.address, topics := entry.topics, payload := entry.data }

def observe (state : EVM.State) : Observation :=
  let localState := actualState state
  {
    halt := state.halt
    output := state.hReturn
    returnData := state.returnData
    memory := localState.memory
    accounts := observedAccounts state
    logs := observedLogs state
    selfDestructs := state.substate.selfDestructList
  }

private def patternedCalldata : ByteArray :=
  Hex.hexToBytes
    "000102030405060708090a0b0c0d0e0f" ++
  Hex.hexToBytes
    "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0" ++
  Hex.hexToBytes
    "112233445566778899aabbccddeeff00"

/-- Add nontrivial calldata and storage while keeping the code-dependent parts
of `initialState` intact. `originalAccountMap` is updated with the same seeded
world so SSTORE gas/refund behavior starts from the correct original values. -/
private def patternedState (code : ByteArray) : EVM.State :=
  let state := initialState code
  let address := state.executionEnv.address
  let account := state.accountMap address
  let storage := account.storage
    |>.set (word 0) (word 7)
    |>.set (word 1) (word (2 ^ 255 + 19))
    |>.set (word 0x40) (word 0xdeadbeef)
  let tstorage := account.tstorage
    |>.set (word 0) (word 11)
    |>.set (word 2) (word 0xcafebabe)
  let accounts := state.accountMap.set address { account with storage, tstorage }
  {
    state with
    accountMap := accounts
    substate := { state.substate with originalAccountMap := accounts }
    executionEnv := {
      state.executionEnv with
      calldata := patternedCalldata
      weiValue := word 0x123456
      gasPrice := word 0xabcdef
    }
  }

private def generatedCalldata (seed variant length : Nat) : ByteArray := Id.run do
  let mut calldata := .empty
  for index in [:length] do
    calldata := calldata.push (UInt8.ofNat (mixSeed seed (variant * 257 + index) % 256))
  return calldata

/-- A reproducible nontrivial world derived from the fixture path. The four
variants cover calldata immediately below, at, and immediately above an EVM
word boundary, while seeding both common and sparse storage slots. -/
private def generatedState
    (seed variant calldataLength : Nat) (code : ByteArray) : EVM.State :=
  let state := initialState code
  let address := state.executionEnv.address
  let account := state.accountMap address
  let sparseSlot := word (0x100 + mixSeed seed (variant + 41) % 0x10000)
  let boundaryValue := match variant with
    | 0 => word (2 ^ 256 - 1)
    | 1 => word (2 ^ 255)
    | 2 => word 1
    | _ => word (2 ^ 128 + mixSeed seed 53)
  let storage := account.storage
    |>.set (word 0) boundaryValue
    |>.set (word (31 + variant)) (word (mixSeed seed (variant + 59)))
    |>.set sparseSlot (word (mixSeed seed (variant + 61)))
  let tstorage := account.tstorage
    |>.set (word variant) (word (mixSeed seed (variant + 67)))
    |>.set sparseSlot (word (mixSeed seed (variant + 71)))
  let weiValue := match variant with
    | 0 => word 0
    | 1 => word 1
    | 2 => word (2 ^ 128)
    | _ => word (2 ^ 256 - 1)
  -- Keep the post-transfer executing balance at least as large as CALLVALUE,
  -- so every generated state is a coherent transaction environment.
  let balance := match variant with
    | 0 => word 0
    | 1 => word (1 + mixSeed seed 73)
    | 2 => word (2 ^ 128 + mixSeed seed 73)
    | _ => word (2 ^ 256 - 1)
  let accounts := state.accountMap.set address { account with balance, storage, tstorage }
  {
    state with
    accountMap := accounts
    substate := { state.substate with originalAccountMap := accounts }
    executionEnv := {
      state.executionEnv with
      calldata := generatedCalldata seed variant calldataLength
      weiValue
      gasPrice := word (mixSeed seed (variant + 79))
    }
  }

private def scenarios (seed : Nat) : Array (String × (ByteArray → EVM.State)) := #[
  ("default", initialState),
  ("patterned-input", patternedState),
  ("seeded-1-byte", generatedState seed 0 1),
  ("seeded-31-byte", generatedState seed 1 31),
  ("seeded-32-byte", generatedState seed 2 32),
  ("seeded-33-byte", generatedState seed 3 33)
]

private inductive RunResult where
  | timedOut
  | halted (observation : Observation)

private def runToResult
    (scenario : ByteArray → EVM.State) (code : ByteArray) (fuel : Nat) : RunResult :=
  let state := runEvm fuel (scenario code)
  if state.isDone then .halted (observe state) else .timedOut

private def mismatchSection (ours solc : Observation) : String :=
  if ours.halt != solc.halt then
    s!"halt kind (Yul compiler: {repr ours.halt}; solc: {repr solc.halt})"
  else if ours.output != solc.output then "return/revert output"
  else if ours.returnData != solc.returnData then "returndata"
  else if ours.memory != solc.memory then "nonzero memory"
  else if ours.accounts != solc.accounts then "accounts/storage"
  else if ours.logs != solc.logs then "logs"
  else if ours.selfDestructs != solc.selfDestructs then "self-destruct list"
  else "unknown observation"

/-- Compare the observable behavior of two bytecode sequences under every
fixed and fixture-seeded scenario. The first bytecode is conventionally this
compiler's output and the second is solc's output. -/
def compareBytecode
    (ours solc : ByteArray) (fuel : Nat := 100000)
    (scenarioSeed : Nat := 0) : Except String Unit := do
  for (name, scenario) in scenarios scenarioSeed do
    match runToResult scenario ours fuel, runToResult scenario solc fuel with
    | .timedOut, .timedOut => pure ()
    | .timedOut, .halted solcObservation =>
        throw (s!"{name}: Yul compiler did not halt within {fuel} steps, " ++
          s!"but solc halted with {repr solcObservation.halt}")
    | .halted oursObservation, .timedOut =>
        throw (s!"{name}: solc did not halt within {fuel} steps, " ++
          s!"but Yul compiler halted with {repr oursObservation.halt}")
    | .halted oursObservation, .halted solcObservation =>
        if oursObservation != solcObservation then
          throw (s!"{name} observable-state mismatch: " ++
            mismatchSection oursObservation solcObservation)

/-- Gas charged for a run: the drop in the top-level `gasAvailable` between the
scenario's start state and its halted state. Only meaningful once the run has
halted, so callers gate on `isDone`. -/
def gasUsed (start final : EVM.State) : Nat :=
  start.gasAvailable - final.gasAvailable

/-- Per-scenario execution gas for two bytecode sequences compiled from the
same Yul source — conventionally this compiler's output first and solc's
second. Each entry carries the gas both programs spend under one scenario, or
`none` when that scenario is not gas-comparable: a comparison is only made
where both halt within `fuel` and reach identical observable behavior (the same
predicate `compareBytecode` enforces). Divergent or non-halting runs would
otherwise contribute meaningless gas.

A non-optimizing compiler is expected to spend strictly more gas than solc, so
this is a measurement, never an equality check. -/
def measureGas
    (ours solc : ByteArray) (fuel : Nat := 100000)
    (scenarioSeed : Nat := 0) : Array (String × Option (Nat × Nat)) := Id.run do
  let mut results := #[]
  for (name, scenario) in scenarios scenarioSeed do
    let oursStart := scenario ours
    let solcStart := scenario solc
    let oursFinal := runEvm fuel oursStart
    let solcFinal := runEvm fuel solcStart
    if oursFinal.isDone && solcFinal.isDone && observe oursFinal == observe solcFinal then
      results := results.push
        (name, some (gasUsed oursStart oursFinal, gasUsed solcStart solcFinal))
    else
      results := results.push (name, none)
  return results

/-- Empty bytecode and an explicit STOP are behaviorally equivalent even
though the executing account's code representation differs. -/
example : compareBytecode .empty (Hex.hexToBytes "00") 10 = .ok () := by
  native_decide

example : fixtureSeed "objectCompiler/example.yul" != fixtureSeed "optimizer/example.yul" := by
  native_decide

end YulEvmCompilerTests.SolcDifferential
