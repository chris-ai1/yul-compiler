import EvmSemantics.Data.Hex
set_option warningAsError true
/-!
# Driving a pinned `solc` as an external process

Shared helpers for the runners that compile the same strict-assembly Yul source
with `solc` and this compiler. Extracted so the behavioral differential and the
gas comparisons invoke `solc` identically: the same `--strict-assembly`,
`--evm-version osaka` invocation and the same pinned-version guard.
-/

namespace YulEvmCompilerTests.Solc

open EvmSemantics

private def isHexDigit (char : Char) : Bool :=
  ('0' <= char && char <= '9') ||
    ('a' <= char && char <= 'f') ||
    ('A' <= char && char <= 'F')

private def findBinary (marker : String) (afterMarker : Bool) : List String → Option String
  | [] => none
  | rawLine :: lines =>
      let line := rawLine.trimAscii.copy
      if afterMarker && !line.isEmpty then some line
      else findBinary marker (afterMarker || line == marker) lines

private def parseBinaryAfter (marker stdout : String) : Except String ByteArray := do
  let encoded ← match findBinary marker false (stdout.splitOn "\n") with
    | some encoded => pure encoded
    | none => throw s!"solc output did not contain '{marker}'"
  if encoded.isEmpty || !encoded.all isHexDigit || encoded.length % 2 != 0 then
    throw s!"solc returned malformed bytecode: {encoded}"
  return Hex.hexToBytes encoded

private def parseSolcBinary (stdout : String) : Except String ByteArray :=
  parseBinaryAfter "Binary representation:" stdout

/-- Compile one strict-assembly Yul source with `solc`, pinned to the same
Osaka target the executable EVM checks use, and return the emitted bytecode. -/
def compileWithSolc (solcPath source : String) : IO (Except String ByteArray) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--strict-assembly", "--bin", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc compilation failed: {output.stderr.trimAscii.copy}"
  return parseSolcBinary output.stdout

/-- Compile one strict-assembly Yul source with `solc`'s **Yul optimizer ON**
(`--strict-assembly --optimize`), pinned to the same Osaka target, and return the
emitted bytecode. This is the reference for measuring a *Yul optimizer* against
solc's: both sides start from the identical Yul program, so the bytecode
difference is purely optimizer-vs-optimizer (and backend codegen), unlike
`compileWithSolc`, which leaves solc's optimizer OFF (backend-codegen parity). -/
def compileOptimizedWithSolc (solcPath source : String) : IO (Except String ByteArray) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--strict-assembly", "--optimize", "--bin", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --optimize compilation failed: {output.stderr.trimAscii.copy}"
  return parseSolcBinary output.stdout

/-- Fully *unoptimized* Yul IR for a Solidity source (`--ir`, solc's `--via-ir`
lowering with the Yul optimizer OFF). Returned from the first `object` line so
it can be fed straight to this compiler. Using the unoptimized IR means the
comparison exercises only solc's Solidity→Yul front-end and none of solc's Yul
optimizer: our (non-optimizing) compiler is measured against solc's fully
optimized bytecode. -/
def solcUnoptimizedIR (solcPath source : String) : IO (Except String String) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--ir", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --ir failed: {output.stderr.trimAscii.copy}"
  -- With several contracts in one source (e.g. a contract plus libraries), solc
  -- emits one `IR:` block per contract, ordered by contract name. Keep only the
  -- first block — cut at the next unindented `IR:` header — so the result is a
  -- single well-formed object; the harness pairs it with the first `Binary:`
  -- section, which is the same contract.
  let lines := output.stdout.splitOn "\n"
  let ir := (lines.dropWhile (fun line => !line.startsWith "object ")).takeWhile
    (fun line => line != "IR:")
  if ir.isEmpty then
    return .error "solc --ir produced no object"
  return .ok (String.intercalate "\n" ir)

/-- External function selectors of a Solidity source (`solc --hashes`), each the
8-hex-digit selector. Used to build valid function-call calldata so the gas
comparison exercises the contract's real work instead of dispatch-and-revert. -/
def solcFunctionSelectors (solcPath source : String) : IO (Except String (List String)) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--hashes", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --hashes failed: {output.stderr.trimAscii.copy}"
  -- Lines look like "4018d9aa: setX(uint256)"; keep the 8-hex-digit prefix.
  let selectors := (output.stdout.splitOn "\n").filterMap fun rawLine =>
    let line := rawLine.trimAscii.copy
    match line.splitOn ": " with
    | sel :: _ :: _ =>
        if sel.length == 8 && sel.all isHexDigit then some sel else none
    | _ => none
  return .ok selectors

/-- solc's own optimized runtime bytecode for a Solidity source
(`--bin-runtime --optimize --via-ir`) — the reference for gas comparison. -/
def solcRuntimeBytecode (solcPath source : String) : IO (Except String ByteArray) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--bin-runtime", "--optimize", "--via-ir", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --bin-runtime failed: {output.stderr.trimAscii.copy}"
  return parseBinaryAfter "Binary of the runtime part:" output.stdout

/-- solc's own optimized creation bytecode (`--bin --optimize --via-ir`). Used
when a comparison must run the constructor (so constructor-initialized storage is
in place) before replaying calls. -/
def solcCreationBytecode (solcPath source : String) : IO (Except String ByteArray) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--bin", "--optimize", "--via-ir", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --bin failed: {output.stderr.trimAscii.copy}"
  return parseBinaryAfter "Binary:" output.stdout

/-- Reject any `solc` other than the pinned version, so every checked-in gas
figure and every differential result reproduces from a single toolchain. -/
def checkSolcVersion (solcPath expectedVersion : String) : IO (Except String Unit) := do
  let output ← IO.Process.output { cmd := solcPath, args := #["--version"] }
  if output.exitCode != 0 then
    return .error s!"solc --version failed: {output.stderr.trimAscii.copy}"
  let marker := s!"Version: {expectedVersion}+"
  if !output.stdout.contains marker then
    return .error (s!"expected solc {expectedVersion}, got:\n" ++ output.stdout.trimAscii.copy)
  return .ok ()

end YulEvmCompilerTests.Solc
