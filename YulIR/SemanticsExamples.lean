import YulIR
import YulIR.Corpus
import YulSemantics.Interp

/-!
# YulIR.SemanticsExamples — validate the IR interpreter against Yul

Differential check: for each corpus program, run the IR interpreter on the IR
(`Sem.run … (ofYul b)`) and the Yul interpreter on the erased IR
(`Interp.run … (toYul (ofYul b))`), and compare an observable fingerprint of the final
state + outcome. Agreement is evidence that `YulIR.Sem` is a faithful semantics for the IR
(consistent with Yul through `toYul`), so it is sound to prove optimizations against it.

Run: `lake env lean YulIR/SemanticsExamples.lean`.
-/

open YulSemantics YulSemantics.EVM

private def fp (st : EvmState) (o : Outcome) :
    Outcome × Option (HaltKind × List UInt8) × List U256 × List UInt8 :=
  (o, st.halted, (List.range 16).map (fun i => st.storage (BitVec.ofNat 256 i)), st.returndata)

private def scenarios : List EvmState :=
  [ EvmState.init
  , { EvmState.init with env := { EvmState.init.env with
        calldata := (List.range 64).map (fun i => UInt8.ofNat i) } } ]

#eval show IO Unit from do
  let fuel := 100000
  let mut fails := 0
  for (name, b) in YulIR.Corpus.corpus do
    let ir := YulIR.ofYul b
    for st0 in scenarios do
      let rIR  := (YulIR.Sem.run fuel ir st0).map (fun t => fp t.2.1 t.2.2)
      let rYul := (Interp.run EVM.exec fuel (YulIR.toYul ir) st0).map (fun t => fp t.2.1 t.2.2)
      unless rIR = rYul do
        fails := fails + 1
        IO.println s!"MISMATCH: {name}"
  IO.println s!"IR interpreter vs Yul-on-toYul: {YulIR.Corpus.corpus.length} programs, {fails} mismatches."
