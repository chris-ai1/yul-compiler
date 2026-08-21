import YulEvmCompiler.AsmSem
import YulEvmCompiler.AsmPeephole
set_option warningAsError true
/-!
# YulEvmCompiler.AsmPeepholeSound

Forward simulation for the Asm-level peephole optimizer
(`YulEvmCompiler.AsmPeephole`), against the phase-A step relation
(`YulEvmCompiler.AsmSem`).

`AStep` is parameterized by the *whole* program (jumps resolve labels to
suffixes via `findLabel`), so the soundness statement is a whole-program
forward simulation, not a local equivalence:

* `Match R` — the configuration relation. The rewrites change the
  intermediate code/stack shape mid-window, so `Match` carries three
  "in-flight" constructors besides the synchronized `sync` state: `mid1`/
  `mid2` inside a return-slot window and `brMid` inside an inverted branch
  (source about to take the `jump`; optimized holding the `iszero`d
  condition for its `jumpi`).
* The simulation threads three whole-run invariants: the executing code is a
  suffix of the program (`AStep.suffix`), label definitions are unique
  (`wfCheck`, so a branch-inversion window *knows* `findLabel` lands on its
  own label), and every code address on the stack is a referenced label
  (`StkRefs`, so `dynJump` targets survive dead-label elimination).
* `step_sim` / `steps_sim` / `halt_sim` — every source `AStep`/`AHalt` is
  matched by finitely many optimized steps preserving `Match`. The optimized
  side stutters (on window entry and dropped labels) and catches up within
  the window, so both runs reach the same endpoint.
* `optimizeAsm_asteps` / `optimizeAsm_ahalt` — the packaged bridge lemmas
  consumed by `YulEvmCompiler.Correctness`, which inserts `optimizeAsm`
  between `compileProgram` and `lowerProg`.
-/

namespace YulEvmCompiler.Peephole

open YulSemantics.EVM (U256 EvmState Op b2w)

/-! ### Whole-run invariants -/

/-- Every code address on the stack is a label that may be referenced. This
is what lets `dynJump` survive dead-label elimination: a `.code l` value can
only ever have been pushed by a `pushLabel l` instruction in the program (or
supplied in the initial stack, which the bridges take empty), so `l` is a
referenced label and its definition is never dropped. -/
def StkRefs (R : List Label) (σ : List AVal) : Prop :=
  ∀ l : Label, AVal.code l ∈ σ → l ∈ R

theorem StkRefs.nil {R : List Label} : StkRefs R [] := fun _ h => absurd h (by simp)

/-- Words carry no code addresses. -/
theorem code_not_mem_words {l : Label} {vs : List U256} :
    AVal.code l ∉ words vs := by
  intro h
  simp only [words, List.mem_map] at h
  obtain ⟨v, -, hv⟩ := h
  cases hv

/-- An executed instruction's label reference is a program reference. -/
theorem refs_of_suffix {prog : List Asm} {i : Asm} {c : List Asm}
    (hsuf : (i :: c) <:+ prog) {l : Label} (hi : i.references = some l) :
    l ∈ labelRefs prog := by
  obtain ⟨pre, rfl⟩ := hsuf
  rw [labelRefs_append]
  exact List.mem_append.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inl hi)))

/-- `AStep` preserves the code-address invariant: ordinary operations move
only words, `dup`/`swap` duplicate/permute existing values, and `pushLabel`
introduces exactly its own (referenced) label. -/
theorem astep_stkRefs [model : ExternalModel] {R : List Label}
    {prog : List Asm} {a b : AConf}
    (hstep : AStep (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hRefs : ∀ l ∈ labelRefs prog, l ∈ R) (hσ : StkRefs R a.stk) :
    StkRefs R b.stk := by
  cases hstep with
  | push =>
      intro l hl
      rcases List.mem_cons.mp hl with h | h
      · cases h
      · exact hσ l h
  | pushImmutable =>
      intro l hl
      rcases List.mem_cons.mp hl with h | h
      · cases h
      · exact hσ l h
  | @op yop args rets c σ yst yst' hb =>
      intro l hl
      rcases List.mem_append.mp hl with h | h
      · exact absurd h code_not_mem_words
      · exact hσ l (List.mem_append.mpr (Or.inr h))
  | @gasCall k g args rets c σ yst yst' hg hb =>
      intro l hl
      rcases List.mem_append.mp hl with h | h
      · exact absurd h code_not_mem_words
      · exact hσ l (List.mem_append.mpr (Or.inr h))
  | @dup n v τ ρ c yst hτ =>
      intro l hl
      rcases List.mem_cons.mp hl with h | h
      · exact hσ l (h ▸ List.mem_append.mpr (Or.inr (List.mem_cons_self)))
      · exact hσ l h
  | @swap n x z τ ρ c yst hτ =>
      intro l hl
      apply hσ
      simp only [List.mem_cons, List.mem_append] at hl ⊢
      tauto
  | pop =>
      intro l hl
      exact hσ l (List.mem_cons_of_mem _ hl)
  | label => exact hσ
  | jump _ => exact hσ
  | jumpiTaken _ _ =>
      intro l hl
      exact hσ l (List.mem_cons_of_mem _ hl)
  | jumpiFall _ =>
      intro l hl
      exact hσ l (List.mem_cons_of_mem _ hl)
  | @pushLabel l0 c σ yst hl0 =>
      intro l hl
      rcases List.mem_cons.mp hl with h | h
      · cases h
        exact hRefs _ (refs_of_suffix hsuf rfl)
      · exact hσ l h
  | dynJump _ =>
      intro l hl
      exact hσ l (List.mem_cons_of_mem _ hl)

/-! ### The configuration relation -/

/-- A configuration correspondence between a source run (in `prog`) and its
optimized run (in `optimizeAsm prog`). `sync` is the aligned state. `mid1`
(source has done the window's `push`, optimized has done nothing) and `mid2`
(source has done `push; swap1`, optimized has done `pop`) capture the two
in-flight states of a return-slot window. `brMid` captures the in-flight
state of an inverted branch: the source is about to take the `jump m` while
the optimized side holds the (nonzero) `iszero`d condition for its
`jumpi m`. -/
inductive Match [model : ExternalModel] (R : List Label) : AConf → AConf → Prop
  | sync {sc oc : List Asm} {σ : List AVal} {y : EvmState} :
      CodeRel R sc oc → Match R ⟨sc, σ, y⟩ ⟨oc, σ, y⟩
  | mid1 {v : U256} {n : Fin 16} (hn : n.val = 0) {S : List AVal}
      {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.swap n :: .pop :: sc, .word v :: S, y⟩
              ⟨.pop :: .push v :: oc, S, y⟩
  | mid2 {v : U256} {x : AVal} {ρ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.pop :: sc, x :: .word v :: ρ, y⟩ ⟨.push v :: oc, ρ, y⟩
  | brMid {l m : Label} {w : U256} (hw : w ≠ 0) {σ : List AVal}
      {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.jump m :: .label l :: sc, σ, y⟩
              ⟨.jumpi m :: .label l :: oc, .word w :: σ, y⟩
  | dz1 {l : Label} {v : U256} {σ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.op .iszero :: .jumpi l :: sc, .word (b2w (v = 0)) :: σ, y⟩
              ⟨.jumpi l :: oc, .word v :: σ, y⟩
  | dz2 {l : Label} {v : U256} {σ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.jumpi l :: sc, .word (b2w (b2w (v = 0) = 0)) :: σ, y⟩
              ⟨.jumpi l :: oc, .word v :: σ, y⟩
  /-- Eq-sub window: both sides have consumed the operands (source via `eq`,
  optimized via `sub`); the source still owes its `iszero`. -/
  | es1 {l : Label} {a b : U256} {σ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.op .iszero :: .jumpi l :: sc, .word (b2w (a = b)) :: σ, y⟩
              ⟨.jumpi l :: oc, .word (a - b) :: σ, y⟩
  /-- Eq-sub window: the source has normalized its comparison; both tops now
  agree on truthiness (`a - b` is zero exactly when `a = b`). -/
  | es2 {l : Label} {a b : U256} {σ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.jumpi l :: sc, .word (b2w (b2w (a = b) = 0)) :: σ, y⟩
              ⟨.jumpi l :: oc, .word (a - b) :: σ, y⟩
  /-- Sub-iszero window: the source has subtracted; the optimized side still
  holds both operands for its `eq`, whose result equals the source's zero
  test bit for bit. -/
  | si1 {a b : U256} {σ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.op .iszero :: sc, .word (a - b) :: σ, y⟩
              ⟨.op .eq :: oc, .word a :: .word b :: σ, y⟩
  /-- Push-dup window: both sides have materialized the constant once; the
  source re-pushes it, the optimized side duplicates it. -/
  | pd1 {v : U256} {σ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.push v :: sc, .word v :: σ, y⟩ ⟨.dup 0 :: oc, .word v :: σ, y⟩
  /-- Constant-taken branch window: the source has pushed its nonzero
  condition and is about to take the branch the optimized side jumps to
  unconditionally. -/
  | pj1 {v : U256} (hv : v ≠ 0) {l : Label} {σ : List AVal} {sc oc : List Asm}
      {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.jumpi l :: sc, .word v :: σ, y⟩ ⟨.jump l :: oc, σ, y⟩
  /-- Constant-fall branch window: the source has pushed its zero condition;
  the optimized side has already fallen through. -/
  | pj0 {l : Label} {σ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.jumpi l :: sc, .word 0 :: σ, y⟩ ⟨oc, σ, y⟩
  /-- Late constant push, deep `dup`: the source has pushed the literal and
  the optimized side has not started (it cannot `dup` yet — that the slot it
  reaches exists is exactly what the source's own `dup` is about to
  witness). -/
  | lp1 {v : U256} {n m : Fin 16} (hn : 0 < n.val) (hm : m.val = 0)
      {S : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.dup n :: .swap m :: sc, .word v :: S, y⟩
              ⟨.dup (dupPred n) :: .push v :: oc, S, y⟩
  /-- Late constant push, deep `dup`: both sides have duplicated; the source
  still owes its `swap1` and the optimized side its `push`. -/
  | lp2 {v : U256} {m : Fin 16} (hm : m.val = 0) {x : AVal} {S : List AVal}
      {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.swap m :: sc, x :: .word v :: S, y⟩ ⟨.push v :: oc, x :: S, y⟩
  /-- Late constant push, `dup1`: both sides have pushed the literal. -/
  | lp0a {v : U256} {n m : Fin 16} (hn : n.val = 0) (hm : m.val = 0)
      {S : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.dup n :: .swap m :: sc, .word v :: S, y⟩
              ⟨.dup n :: oc, .word v :: S, y⟩
  /-- Late constant push, `dup1`: both sides have duplicated the literal, so
  the source's `swap1` exchanges two equal words and the optimized side is
  already done with the window. -/
  | lp0b {v : U256} {m : Fin 16} (hm : m.val = 0) {S : List AVal}
      {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.swap m :: sc, .word v :: .word v :: S, y⟩
              ⟨oc, .word v :: .word v :: S, y⟩
  /-- Flipped comparison: the source has exchanged its two operands, the
  optimized side still holds the original order and reads it with the mirror
  opcode. -/
  | fc1 {yop yop' : Op} (hf : flipOp yop = some yop') {x z : AVal}
      {S : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.op yop :: sc, x :: z :: S, y⟩ ⟨.op yop' :: oc, z :: x :: S, y⟩
  /-- Fused gas-forwarding call window: the source has read its oracle-
  admitted gas word (remembered here — `gas()` leaves the state unchanged, so
  the admission still speaks about `y`); the optimized side is about to
  execute the fused instruction, which packages that admission with the
  call. -/
  | gasWin {k : GasCallKind} {g : U256} {σ : List AVal} {sc oc : List Asm}
      {y : EvmState} (hg : ExternalModel.gas.Gas y g) :
      CodeRel R sc oc →
      Match R ⟨.op k.op :: sc, .word g :: σ, y⟩ ⟨.gasCall k :: oc, σ, y⟩

/-- The `iszero` step the optimized side of an inverted branch executes. -/
theorem iszero_step [model : ExternalModel] {prog' c : List Asm}
    {v : U256} {σ : List AVal} {y : EvmState} :
    AStep (model := model) prog' ⟨.op .iszero :: c, .word v :: σ, y⟩
      ⟨c, .word (b2w (v = 0)) :: σ, y⟩ := by
  have h := AStep.op (model := model) (prog := prog') (yop := .iszero)
    (args := [v]) (rets := [b2w (v = 0)]) (c := c) (σ := σ) (yst := y) (yst' := y) rfl
  simpa [words] using h

/-- The `sub` step the optimized side of an eq-sub window executes. -/
theorem sub_step [model : ExternalModel] {prog' c : List Asm}
    {a b : U256} {σ : List AVal} {y : EvmState} :
    AStep (model := model) prog' ⟨.op .sub :: c, .word a :: .word b :: σ, y⟩
      ⟨c, .word (a - b) :: σ, y⟩ := by
  have h := AStep.op (model := model) (prog := prog') (yop := .sub)
    (args := [a, b]) (rets := [a - b]) (c := c) (σ := σ) (yst := y) (yst' := y) rfl
  simpa [words] using h

/-- The `eq` step the optimized side of a sub-iszero window executes. -/
theorem eq_step [model : ExternalModel] {prog' c : List Asm}
    {a b : U256} {σ : List AVal} {y : EvmState} :
    AStep (model := model) prog' ⟨.op .eq :: c, .word a :: .word b :: σ, y⟩
      ⟨c, .word (b2w (a = b)) :: σ, y⟩ := by
  have h := AStep.op (model := model) (prog := prog') (yop := .eq)
    (args := [a, b]) (rets := [b2w (a = b)]) (c := c) (σ := σ) (yst := y) (yst' := y) rfl
  simpa [words] using h

/-- Invert a successful `iszero` built-in step: one argument, the `b2w`
result, unchanged state. -/
theorem iszero_inv [model : ExternalModel] {args rets : List U256}
    {yst yst' : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas
      .iszero args yst (.ok rets yst')) :
    ∃ v, args = [v] ∧ rets = [b2w (v = 0)] ∧ yst' = yst := by
  match args with
  | [v] =>
      obtain ⟨rfl, rfl⟩ :
          [b2w (v = 0)] = rets ∧ yst = yst' := by
        have h := Option.some.inj hb
        cases h
        exact ⟨rfl, rfl⟩
      exact ⟨v, rfl, rfl, rfl⟩
  | [] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un])
  | _ :: _ :: _ => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un])

/-- Invert a successful `gas()` built-in step: no arguments, one
oracle-admitted result word, unchanged state. -/
theorem gas_inv [model : ExternalModel] {args rets : List U256}
    {yst yst' : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas
      .gas args yst (.ok rets yst')) :
    ∃ g, args = [] ∧ rets = [g] ∧ yst' = yst ∧ ExternalModel.gas.Gas yst g := by
  match args with
  | [] =>
      obtain ⟨g, hg, heq⟩ := hb
      injection heq with h1 h2
      exact ⟨g, rfl, h1, h2, hg⟩
  | _ :: _ => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal])

/-- `gas()` never halts. -/
theorem gas_no_halt [model : ExternalModel] {args : List U256}
    {yst yf : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas
      .gas args yst (.halt yf)) : False := by
  match args with
  | [] => obtain ⟨g, -, heq⟩ := hb; cases heq
  | _ :: _ => exact hb

/-- Invert a successful `eq` built-in step: two arguments, the `b2w`
comparison result, unchanged state. -/
theorem eq_inv [model : ExternalModel] {args rets : List U256}
    {yst yst' : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas
      .eq args yst (.ok rets yst')) :
    ∃ a b, args = [a, b] ∧ rets = [b2w (a = b)] ∧ yst' = yst := by
  match args with
  | [a, b] =>
      obtain ⟨rfl, rfl⟩ :
          [b2w (a = b)] = rets ∧ yst = yst' := by
        have h := Option.some.inj hb
        cases h
        exact ⟨rfl, rfl⟩
      exact ⟨a, b, rfl, rfl, rfl⟩
  | [] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])
  | [_] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])
  | _ :: _ :: _ :: _ => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])

/-- `eq` never halts. -/
theorem eq_no_halt [model : ExternalModel] {args : List U256}
    {yst yf : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas
      .eq args yst (.halt yf)) : False := by
  match args with
  | [] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])
  | [_] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])
  | [_, _] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])
  | _ :: _ :: _ :: _ => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])

/-- Invert a successful `sub` built-in step. -/
theorem sub_inv [model : ExternalModel] {args rets : List U256}
    {yst yst' : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas
      .sub args yst (.ok rets yst')) :
    ∃ a b, args = [a, b] ∧ rets = [a - b] ∧ yst' = yst := by
  match args with
  | [a, b] =>
      obtain ⟨rfl, rfl⟩ :
          [a - b] = rets ∧ yst = yst' := by
        have h := Option.some.inj hb
        cases h
        exact ⟨rfl, rfl⟩
      exact ⟨a, b, rfl, rfl, rfl⟩
  | [] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])
  | [_] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])
  | _ :: _ :: _ :: _ => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])

/-- `sub` never halts. -/
theorem sub_no_halt [model : ExternalModel] {args : List U256}
    {yst yf : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas
      .sub args yst (.halt yf)) : False := by
  match args with
  | [] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])
  | [_] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])
  | [_, _] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])
  | _ :: _ :: _ :: _ => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin])

/-- Words subtract to zero exactly when they are equal (`U256` is a group). -/
theorem u256_sub_eq_zero_iff {a b : U256} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg (· + b) h
    simpa using h'
  · rintro rfl
    simp

/-- The zero test of a subtraction computes exactly the equality's `b2w`. -/
theorem b2w_sub_eq {a b : U256} : b2w ((a - b : U256) = 0) = b2w (a = b) := by
  simp only [b2w, u256_sub_eq_zero_iff]

/-- `b2w_dbl_eq_zero_iff` for an arbitrary decidable proposition: the
double-`b2w` truthiness collapse an eq-sub window rests on. -/
theorem b2w_dbl_prop_eq_zero_iff {P : Prop} [Decidable P] :
    b2w (b2w P = 0) = 0 ↔ P := by
  by_cases h : P <;> simp [b2w, h]

/-- A fused call's built-in relation is empty at the argument count without
the gas word: every call op insists on its full arity. -/
theorem gasCall_arity_absurd [model : ExternalModel] {k : GasCallKind}
    {yst : EvmState}
    {r : YulSemantics.BuiltinResult YulSemantics.EVM.U256 EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas
      k.op [] yst r) : False := by
  cases k <;> exact hb

/-- `iszero` never halts. -/
theorem iszero_no_halt [model : ExternalModel] {args : List U256}
    {yst yf : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas
      .iszero args yst (.halt yf)) : False := by
  match args with
  | [] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un])
  | [v] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un])
  | _ :: _ :: _ => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un])

/-- Double `iszero` preserves truthiness: the normalized value is zero
exactly when the original is. -/
theorem b2w_dbl_eq_zero_iff {v : U256} : b2w (b2w (v = 0) = 0) = 0 ↔ v = 0 := by
  by_cases hv : v = 0 <;> simp [b2w, hv]

/-- Invert a step from a configuration headed by an operation (the stack need
not be in `words args ++ σ` form syntactically). -/
theorem astep_op_inv [model : ExternalModel] {prog : List Asm} {yop : Op}
    {c : List Asm} {σs : List AVal} {y : EvmState} {b : AConf}
    (h : AStep (model := model) prog ⟨.op yop :: c, σs, y⟩ b) :
    ∃ args rets σ' yst', σs = words args ++ σ'
      ∧ YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas yop args y
          (.ok rets yst')
      ∧ b = ⟨c, words rets ++ σ', yst'⟩ := by
  cases h with
  | op hb => exact ⟨_, _, _, _, rfl, hb, rfl⟩

/-- Invert a step from a configuration headed by a `dup` (the stack need not
be in `τ ++ x :: ρ` form syntactically). -/
theorem astep_dup_inv [model : ExternalModel] {prog : List Asm} {n : Fin 16}
    {c : List Asm} {σs : List AVal} {y : EvmState} {b : AConf}
    (h : AStep (model := model) prog ⟨.dup n :: c, σs, y⟩ b) :
    ∃ x τ ρ, σs = τ ++ x :: ρ ∧ τ.length = n.val ∧ b = ⟨c, x :: σs, y⟩ := by
  cases h with
  | dup hτ => exact ⟨_, _, _, rfl, hτ, rfl⟩

/-- Invert a step from a configuration headed by a `swap`. -/
theorem astep_swap_inv [model : ExternalModel] {prog : List Asm} {n : Fin 16}
    {c : List Asm} {σs : List AVal} {y : EvmState} {b : AConf}
    (h : AStep (model := model) prog ⟨.swap n :: c, σs, y⟩ b) :
    ∃ a bb τ ρ, σs = a :: (τ ++ bb :: ρ) ∧ τ.length = n.val
      ∧ b = ⟨c, bb :: (τ ++ a :: ρ), y⟩ := by
  cases h with
  | swap hτ => exact ⟨_, _, _, _, rfl, hτ, rfl⟩

/-- Invert a successful two-argument value built-in. -/
theorem bin_inv {f : U256 → U256 → U256} {args rets : List U256}
    {st st' : EvmState}
    (h : YulSemantics.EVM.bin f args st = some (.ok rets st')) :
    ∃ a b, args = [a, b] ∧ rets = [f a b] ∧ st' = st := by
  match args with
  | [a, b] =>
      refine ⟨a, b, rfl, ?_, ?_⟩ <;>
        · have h' := Option.some.inj h
          cases h'
          rfl
  | [] => exact absurd h (by simp [YulSemantics.EVM.bin])
  | [_] => exact absurd h (by simp [YulSemantics.EVM.bin])
  | _ :: _ :: _ :: _ => exact absurd h (by simp [YulSemantics.EVM.bin])

/-- A two-argument value built-in never halts. -/
theorem bin_no_halt {f : U256 → U256 → U256} {args : List U256}
    {st sf : EvmState} (h : YulSemantics.EVM.bin f args st = some (.halt sf)) :
    False := by
  match args with
  | [_, _] => exact absurd h (by simp [YulSemantics.EVM.bin])
  | [] => exact absurd h (by simp [YulSemantics.EVM.bin])
  | [_] => exact absurd h (by simp [YulSemantics.EVM.bin])
  | _ :: _ :: _ :: _ => exact absurd h (by simp [YulSemantics.EVM.bin])

/-- A built-in with a reversed twin (`flipOp`) is binary and pure, and the
twin computes the same result from the operands in the other order. This is
the whole semantic content of the flipped-comparison rewrite: the commutative
built-ins are their own twin, and `lt`/`gt` (`slt`/`sgt`) are defined as each
other's operand swap in the dialect (`b2w (a.ult b)` against
`b2w (b.ult a)`). -/
theorem flipOp_inv [model : ExternalModel] {yop yop' : Op}
    (hf : flipOp yop = some yop') {args rets : List U256} {yst yst' : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas yop args yst
      (.ok rets yst')) :
    ∃ a b, args = [a, b] ∧ yst' = yst ∧
      YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas yop' [b, a] yst
        (.ok rets yst) := by
  -- only the ten ops `flipOp` accepts survive; each is a `bin`
  cases yop <;> simp only [flipOp, Option.some.injEq, reduceCtorEq] at hf
  all_goals subst hf
  all_goals
    simp only [YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.stepOp] at hb
    obtain ⟨a, b, rfl, rfl, rfl⟩ := bin_inv hb
    refine ⟨a, b, rfl, rfl, ?_⟩
    -- the twin's own definition reads the operands the other way round, so the
    -- comparisons close by `rfl` and the commutative ops by their `comm` lemma
    simp only [YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.stepOp,
      YulSemantics.EVM.bin, add_comm b a, mul_comm b a,
      BitVec.and_comm b a, BitVec.or_comm b a, BitVec.xor_comm b a,
      eq_comm (a := b) (b := a)]

/-- A built-in with a reversed twin never halts. -/
theorem flipOp_no_halt [model : ExternalModel] {yop yop' : Op}
    (hf : flipOp yop = some yop') {args : List U256} {yst yf : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas yop args yst
      (.halt yf)) : False := by
  cases yop <;> simp only [flipOp, Option.some.injEq, reduceCtorEq] at hf
  all_goals
    simp only [YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.stepOp] at hb
    exact bin_no_halt hb

/-- Invert a halt from a configuration headed by an operation. -/
theorem ahalt_op_inv [model : ExternalModel] {prog : List Asm} {yop : Op}
    {c : List Asm} {σs : List AVal} {y yf : EvmState}
    (h : AHalt (model := model) prog ⟨.op yop :: c, σs, y⟩ yf) :
    ∃ args σ', σs = words args ++ σ'
      ∧ YulSemantics.EVM.builtinWithExternal model.calls model.creates model.gas yop args y
          (.halt yf) := by
  cases h with
  | op hb => exact ⟨_, _, rfl, hb⟩

/-- Entering a late-constant-push window. The two `latePush` shapes need
different first moves from the optimized side — a stutter when the `dup`
reaches below the literal (that the slot exists is exactly what the source's
own `dup` is about to witness) and the literal's `push` when it does not — so
the case split lives here rather than inline. -/
theorem latePush_entry [model : ExternalModel] {R : List Label} {prog' : List Asm}
    {v : U256} {n m : Fin 16} (hm : m.val = 0) {c c' : List Asm}
    (hc : CodeRel R c c') {σ : List AVal} {y : EvmState} :
    ∃ b', ASteps (model := model) prog' ⟨latePush v n ++ c', σ, y⟩ b'
      ∧ Match R ⟨.dup n :: .swap m :: c, .word v :: σ, y⟩ b' := by
  by_cases hn : 0 < n.val
  · rw [show latePush v n = [Asm.dup (dupPred n), Asm.push v] from by
      simp [YulEvmCompiler.latePush, hn]]
    exact ⟨_, .refl _, Match.lp1 hn hm hc⟩
  · have hn0 : n.val = 0 := by omega
    rw [show latePush v n = [Asm.push v, Asm.dup n] from by
      simp [YulEvmCompiler.latePush, hn]]
    exact ⟨_, .single .push, Match.lp0a hn0 hm hc⟩

/-! ### The forward simulation -/

/-- Single-step forward simulation: one source `AStep` is simulated by finitely
many optimized steps preserving `Match`. -/
theorem step_sim [model : ExternalModel] {R : List Label} {prog prog' : List Asm}
    (hnodup : (labelDefs prog).Nodup) (hRefs : ∀ l ∈ labelRefs prog, l ∈ R)
    (hpp : CodeRel R prog prog') {a b a' : AConf}
    (hstep : AStep (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hσ : StkRefs R a.stk) (hm : Match R a a') :
    ∃ b', ASteps (model := model) prog' a' b' ∧ Match R b b' := by
  cases hm with
  | @sync sc oc σ y hc =>
    cases hstep with
    | @push v c σ2 yst =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single .push, .sync hc'⟩
      | window hn hc' => exact ⟨_, .refl _, .mid1 hn hc'⟩
      | latePush hm hc' => exact latePush_entry hm hc'
      | pushDup hc' => exact ⟨_, .single .push, .pd1 hc'⟩
      | pushJumpiTaken hv hc' => exact ⟨_, .refl _, .pj1 hv hc'⟩
      | pushJumpiFall hc' => exact ⟨_, .refl _, .pj0 hc'⟩
    | @pushImmutable key c σ2 yst =>
      -- No peephole window ever opens on an immutable placeholder, so the pass
      -- can only `keep` it — which is exactly what must happen: folding one
      -- would move the 32 bytes the constructor patches.
      cases hc with
      | keep _ hc' => exact ⟨_, .single .pushImmutable, .sync hc'⟩
    | @op yop args rets c σ2 yst yst' hb =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.op hb), .sync hc'⟩
      | dblIszero hc' =>
        -- first `iszero` of a doomed pair: the optimized side stutters
        obtain ⟨v, rfl, rfl, rfl⟩ := iszero_inv hb
        exact ⟨_, .refl _, .dz1 hc'⟩
      | eqSubJumpi hc' =>
        -- both sides consume the operands: `eq` against `sub`
        obtain ⟨a, b, rfl, rfl, rfl⟩ := eq_inv hb
        exact ⟨_, .single sub_step, .es1 hc'⟩
      | subIszeroEq hc' =>
        -- the source subtracts; the optimized side waits with both operands
        obtain ⟨a, b, rfl, rfl, rfl⟩ := sub_inv hb
        exact ⟨_, .refl _, .si1 hc'⟩
      | gasFuse hc' =>
        -- window entry: the source reads its gas word, the optimized side
        -- stutters, remembering the oracle admission for the fused step
        obtain ⟨g, rfl, rfl, rfl, hg⟩ := gas_inv hb
        exact ⟨_, .refl _, .gasWin hg hc'⟩
    | @gasCall k g args rets c σ2 yst yst' hg hb =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.gasCall hg hb), .sync hc'⟩
    | @dup n v τ ρ c yst hτ =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.dup hτ), .sync hc'⟩
    | @swap n aa bb τ ρ c yst hτ =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.swap hτ), .sync hc'⟩
      | @flipCmp _ hn yop yop' hf c0 c0' hc' =>
        -- `swap1`, so the exchanged slots are the top two; the optimized side
        -- holds them the other way round and reads them with the mirror opcode
        obtain rfl : τ = [] := List.length_eq_zero_iff.mp (hτ.trans hn)
        exact ⟨_, .refl _, Match.fc1 hf hc'⟩
    | @pop v c σ2 yst =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single .pop, .sync hc'⟩
    | @label l c σ2 yst =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single .label, .sync hc'⟩
      | dropLabel _ hc' => exact ⟨_, .refl _, .sync hc'⟩
    | @jump l c c'0 σ2 yst hf =>
      cases hc with
      | keep _ hc' =>
        have hR : l ∈ R := hRefs l (refs_of_suffix hsuf rfl)
        obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
        exact ⟨_, .single (.jump ho), .sync hr⟩
      | @jumpNext _ ctail oc' hc' =>
        -- the jump's own label is next; source lands exactly there
        obtain ⟨pre0, hpre⟩ := hsuf
        have heq : prog = (pre0 ++ [Asm.jump l]) ++ Asm.label l :: ctail := by
          rw [← hpre]; simp
        have hfl : findLabel l prog = some ctail := by
          rw [heq]; exact findLabel_boundary (by rw [← heq]; exact hnodup)
        obtain rfl : c'0 = ctail := by
          rw [hf] at hfl; exact Option.some.inj hfl
        exact ⟨_, .single .label, .sync hc'⟩
    | @jumpiTaken l v c c'0 σ2 yst hv hf =>
      cases hc with
      | keep _ hc' =>
        have hR : l ∈ R := hRefs l (refs_of_suffix hsuf rfl)
        obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
        exact ⟨_, .single (.jumpiTaken hv ho), .sync hr⟩
      | @brInv _ m ctail oc' hc' =>
        -- the window's own label is the unique definition of `l`, so the
        -- source lands exactly at the window's continuation
        obtain ⟨pre0, hpre⟩ := hsuf
        have heq : prog = (pre0 ++ [Asm.jumpi l, Asm.jump m]) ++ Asm.label l :: ctail := by
          rw [← hpre]; simp
        have hfl : findLabel l prog = some ctail := by
          rw [heq]; exact findLabel_boundary (by rw [← heq]; exact hnodup)
        obtain rfl : c'0 = ctail := by
          rw [hf] at hfl; exact Option.some.inj hfl
        -- optimized: iszero (→ 0), fall through the jumpi, step the label
        refine ⟨_, ?_, .sync hc'⟩
        refine .head iszero_step (.head (.jumpiFall (by simp [b2w]; exact hv)) ?_)
        exact .single .label
      | @jumpiNext _ ctail oc' hc' =>
        -- the jumpi's own label is next; taken lands exactly there
        obtain ⟨pre0, hpre⟩ := hsuf
        have heq : prog = (pre0 ++ [Asm.jumpi l]) ++ Asm.label l :: ctail := by
          rw [← hpre]; simp
        have hfl : findLabel l prog = some ctail := by
          rw [heq]; exact findLabel_boundary (by rw [← heq]; exact hnodup)
        obtain rfl : c'0 = ctail := by
          rw [hf] at hfl; exact Option.some.inj hfl
        exact ⟨_, .head .pop (.single .label), .sync hc'⟩
    | @jumpiFall l v c σ2 yst hv =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.jumpiFall hv), .sync hc'⟩
      | @brInv _ m _ oc' hc' =>
        -- optimized: iszero (→ 1); hold it for the inverted jumpi
        subst hv
        refine ⟨_, .single iszero_step, Match.brMid ?_ hc'⟩
        simp [b2w]
      | @jumpiNext _ ctail oc' hc' =>
        -- not taken: fall into the label; optimized just pops the condition
        exact ⟨_, .single .pop, .sync (CodeRel.keep _ hc')⟩
    | @pushLabel l c σ2 yst hl =>
      cases hc with
      | keep _ hc' =>
        have hR : l ∈ R := hRefs l (refs_of_suffix hsuf rfl)
        exact ⟨_, .single (.pushLabel (codeRel_labelDefs_mem hpp hR hl)), .sync hc'⟩
    | @dynJump l c c'0 σ2 yst hf =>
      cases hc with
      | keep _ hc' =>
        have hR : l ∈ R := hσ l List.mem_cons_self
        obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
        exact ⟨_, .single (.dynJump ho), .sync hr⟩
  | @mid1 v n hn S sc oc y hc =>
    cases hstep with
    | @swap n2 aa bb τ ρ c yst hτ =>
      -- code head is `swap n`; τ.length = n.val = 0 ⇒ τ = []
      obtain rfl : τ = [] := List.length_eq_zero_iff.mp (hτ.trans hn)
      -- opt does one `pop`, landing in the `mid2` state
      exact ⟨_, .single .pop, .mid2 hc⟩
  | @mid2 v x ρ sc oc y hc =>
    cases hstep with
    | @pop v2 c σ2 yst =>
      exact ⟨_, .single .push, .sync hc⟩
  | @brMid l m w hw σ sc oc y hc =>
    cases hstep with
    | jump hf =>
      have hR : m ∈ R := hRefs m (refs_of_suffix hsuf rfl)
      obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
      exact ⟨_, .single (.jumpiTaken hw ho), .sync hr⟩
  | @dz1 l v σ sc oc y hc =>
    -- second `iszero` of the pair; the optimized side still stutters
    obtain ⟨args, rets, σ', yst', hσeq, hb, rfl⟩ := astep_op_inv hstep
    obtain ⟨u, rfl, rfl, rfl⟩ := iszero_inv hb
    obtain ⟨rfl, rfl⟩ : b2w (v = 0) = u ∧ σ = σ' := by
      simpa [words] using hσeq
    exact ⟨_, .refl _, .dz2 hc⟩
  | @dz2 l v σ sc oc y hc =>
    cases hstep with
    | @jumpiTaken _ _ c c'0 σ2 yst hv hf =>
      have hvne : v ≠ 0 := fun h => hv (b2w_dbl_eq_zero_iff.mpr h)
      have hR : l ∈ R := hRefs l (refs_of_suffix hsuf rfl)
      obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
      exact ⟨_, .single (.jumpiTaken hvne ho), .sync hr⟩
    | @jumpiFall _ _ c σ2 yst hv =>
      have hv0 : v = 0 := b2w_dbl_eq_zero_iff.mp hv
      exact ⟨_, .single (.jumpiFall hv0), .sync hc⟩
  | @es1 l a b σ sc oc y hc =>
    -- the source's `iszero`; the optimized side stutters
    obtain ⟨args, rets, σ', yst', hσeq, hb, rfl⟩ := astep_op_inv hstep
    obtain ⟨u, rfl, rfl, rfl⟩ := iszero_inv hb
    obtain ⟨rfl, rfl⟩ : b2w (a = b) = u ∧ σ = σ' := by
      simpa [words] using hσeq
    exact ⟨_, .refl _, .es2 hc⟩
  | @es2 l a b σ sc oc y hc =>
    cases hstep with
    | @jumpiTaken _ _ c c'0 σ2 yst hv hf =>
      have hne : a - b ≠ 0 := fun h =>
        hv (b2w_dbl_prop_eq_zero_iff.mpr (u256_sub_eq_zero_iff.mp h))
      have hR : l ∈ R := hRefs l (refs_of_suffix hsuf rfl)
      obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
      exact ⟨_, .single (.jumpiTaken hne ho), .sync hr⟩
    | @jumpiFall _ _ c σ2 yst hv =>
      have h0 : a - b = 0 :=
        u256_sub_eq_zero_iff.mpr (b2w_dbl_prop_eq_zero_iff.mp hv)
      exact ⟨_, .single (.jumpiFall h0), .sync hc⟩
  | @si1 a b σ sc oc y hc =>
    -- the source's `iszero`; the optimized side performs its `eq`
    obtain ⟨args, rets, σ', yst', hσeq, hb, rfl⟩ := astep_op_inv hstep
    obtain ⟨u, rfl, rfl, rfl⟩ := iszero_inv hb
    obtain ⟨rfl, rfl⟩ : a - b = u ∧ σ = σ' := by
      simpa [words] using hσeq
    refine ⟨_, .single eq_step, ?_⟩
    have hval : b2w ((a - b : U256) = 0) = b2w (a = b) := b2w_sub_eq
    rw [hval]
    exact .sync hc
  | @pd1 v σ sc oc y hc =>
    cases hstep with
    | push => exact ⟨_, .single (.dup (τ := []) rfl), .sync hc⟩
  | @pj1 v hv l σ sc oc y hc =>
    cases hstep with
    | @jumpiTaken _ _ c c'0 σ2 yst hv2 hf =>
      have hR : l ∈ R := hRefs l (refs_of_suffix hsuf rfl)
      obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
      exact ⟨_, .single (.jump ho), .sync hr⟩
    | @jumpiFall _ _ c σ2 yst hv0 => exact absurd hv0 hv
  | @pj0 l σ sc oc y hc =>
    cases hstep with
    | @jumpiTaken _ _ c c'0 σ2 yst hv hf => exact absurd rfl hv
    | @jumpiFall _ _ c σ2 yst hv0 => exact ⟨_, .refl _, .sync hc⟩
  | @lp1 v n m hn hm S sc oc y hc =>
    obtain ⟨x, τ, ρ, hσeq, hτ, rfl⟩ := astep_dup_inv hstep
    cases τ with
    | nil => simp at hτ; omega
    | cons a τ' =>
      obtain ⟨rfl, rfl⟩ : AVal.word v = a ∧ S = τ' ++ x :: ρ := by
        simpa using hσeq
      have hlen : τ'.length = (dupPred n).val := by
        simp only [dupPred, List.length_cons] at hτ ⊢; omega
      exact ⟨_, .single (.dup hlen), Match.lp2 hm hc⟩
  | @lp2 v m hm x S sc oc y hc =>
    obtain ⟨a, bb, τ, ρ, hσeq, hτ, rfl⟩ := astep_swap_inv hstep
    obtain rfl : τ = [] := List.length_eq_zero_iff.mp (hτ.trans hm)
    obtain ⟨rfl, rfl, rfl⟩ : x = a ∧ AVal.word v = bb ∧ S = ρ := by
      simpa using hσeq
    exact ⟨_, .single .push, .sync hc⟩
  | @lp0a v n m hn hm S sc oc y hc =>
    obtain ⟨x, τ, ρ, hσeq, hτ, rfl⟩ := astep_dup_inv hstep
    obtain rfl : τ = [] := List.length_eq_zero_iff.mp (hτ.trans hn)
    obtain ⟨rfl, rfl⟩ : AVal.word v = x ∧ S = ρ := by simpa using hσeq
    exact ⟨_, .single (.dup (n := n) (τ := []) (by simpa using hn.symm)),
      Match.lp0b hm hc⟩
  | @lp0b v m hm S sc oc y hc =>
    obtain ⟨a, bb, τ, ρ, hσeq, hτ, rfl⟩ := astep_swap_inv hstep
    obtain rfl : τ = [] := List.length_eq_zero_iff.mp (hτ.trans hm)
    obtain ⟨rfl, rfl, rfl⟩ : AVal.word v = a ∧ AVal.word v = bb ∧ S = ρ := by
      simpa using hσeq
    exact ⟨_, .refl _, .sync hc⟩
  | @fc1 yop yop' hf x z S sc oc y hc =>
    obtain ⟨args, rets, σ', yst', hσeq, hb, rfl⟩ := astep_op_inv hstep
    obtain ⟨a, b, rfl, rfl, hb'⟩ := flipOp_inv hf hb
    obtain ⟨rfl, rfl, rfl⟩ : x = AVal.word a ∧ z = AVal.word b ∧ S = σ' := by
      simpa [words] using hσeq
    exact ⟨_, .single (.op hb'), .sync hc⟩
  | @gasWin k g σ2 sc oc y hg hc =>
    -- window exit: the source performs the call at its read word; the fused
    -- step reproduces it from the remembered admission
    obtain ⟨args, rets, σ', yst', hσeq, hb, rfl⟩ := astep_op_inv hstep
    rcases args with _ | ⟨a, args'⟩
    · exact absurd hb (gasCall_arity_absurd (k := k))
    · obtain ⟨rfl, hσ2⟩ : g = a ∧ σ2 = words args' ++ σ' := by
        simpa [words] using hσeq
      subst hσ2
      exact ⟨_, .single (.gasCall hg hb), .sync hc⟩

/-- Multi-step forward simulation (reflexive-transitive closure), threading
the suffix and stack invariants along the source run. -/
theorem steps_sim [model : ExternalModel] {R : List Label} {prog prog' : List Asm}
    (hnodup : (labelDefs prog).Nodup) (hRefs : ∀ l ∈ labelRefs prog, l ∈ R)
    (hpp : CodeRel R prog prog') {a b a' : AConf}
    (hsteps : ASteps (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hσ : StkRefs R a.stk) (hm : Match R a a') :
    ∃ b', ASteps (model := model) prog' a' b' ∧ Match R b b' := by
  induction hsteps generalizing a' with
  | refl a => exact ⟨a', .refl _, hm⟩
  | @head a c b hstep hrest ih =>
    obtain ⟨c', hc', hmc⟩ := step_sim hnodup hRefs hpp hstep hsuf hσ hm
    obtain ⟨b', hb', hmb⟩ :=
      ih (hstep.suffix hsuf) (astep_stkRefs hstep hsuf hRefs hσ) hmc
    exact ⟨b', hc'.trans hb', hmb⟩

/-- Halting-step simulation. -/
theorem halt_sim [model : ExternalModel] {R : List Label} {prog prog' : List Asm}
    {b a' : AConf} {yf : EvmState}
    (hhalt : AHalt (model := model) prog b yf) (hm : Match R b a') :
    AHalt (model := model) prog' a' yf := by
  cases hm with
  | @sync sc oc σ2 y hc =>
    cases hhalt with
    | @op yop args c σ yst yst' hb =>
      cases hc with
      | keep _ hc' => exact .op hb
      | dblIszero _ => exact absurd hb iszero_no_halt
      | eqSubJumpi _ => exact absurd hb eq_no_halt
      | subIszeroEq _ => exact absurd hb sub_no_halt
      | gasFuse _ => exact absurd hb gas_no_halt
    | @gasCall k g args c σ yst yst' hg hb =>
      cases hc with
      | keep _ hc' => exact .gasCall hg hb
  | dz1 hc =>
    obtain ⟨args, σ', -, hb⟩ := ahalt_op_inv hhalt
    exact absurd hb iszero_no_halt
  | mid1 _ _ => exact absurd hhalt (by intro h; cases h)
  | mid2 _ => exact absurd hhalt (by intro h; cases h)
  | brMid _ _ => exact absurd hhalt (by intro h; cases h)
  | lp1 _ _ _ => exact absurd hhalt (by intro h; cases h)
  | lp2 _ _ => exact absurd hhalt (by intro h; cases h)
  | lp0a _ _ _ => exact absurd hhalt (by intro h; cases h)
  | lp0b _ _ => exact absurd hhalt (by intro h; cases h)
  | fc1 hf _ =>
    obtain ⟨args, σ', -, hb⟩ := ahalt_op_inv hhalt
    exact (flipOp_no_halt hf hb).elim
  | dz2 _ => exact absurd hhalt (by intro h; cases h)
  | es1 hc =>
    obtain ⟨args, σ', -, hb⟩ := ahalt_op_inv hhalt
    exact absurd hb iszero_no_halt
  | es2 _ => exact absurd hhalt (by intro h; cases h)
  | si1 hc =>
    obtain ⟨args, σ', -, hb⟩ := ahalt_op_inv hhalt
    exact absurd hb iszero_no_halt
  | pd1 _ => exact absurd hhalt (by intro h; cases h)
  | pj1 _ _ => exact absurd hhalt (by intro h; cases h)
  | pj0 _ => exact absurd hhalt (by intro h; cases h)
  | @gasWin k g σ2 sc oc y hg hc =>
    obtain ⟨args, σ', hσeq, hb⟩ := ahalt_op_inv hhalt
    rcases args with _ | ⟨a, args'⟩
    · exact absurd hb (gasCall_arity_absurd (k := k))
    · obtain ⟨rfl, hσ2⟩ : g = a ∧ σ2 = words args' ++ σ' := by
        simpa [words] using hσeq
      subst hσ2
      exact .gasCall hg hb

/-! ### Endpoint inversion and the packaged bridge lemmas -/

/-- With empty source code, `Match` forces the optimized configuration to be
identical (same empty code, stack, and state). -/
theorem match_empty_left [model : ExternalModel] {R : List Label} {σ : List AVal} {y : EvmState}
    {a' : AConf} (hm : Match (model := model) R ⟨[], σ, y⟩ a') :
    a' = ⟨[], σ, y⟩ := by
  cases hm with
  | sync hc => rw [codeRel_nil_left hc]

/-- **Round bridge (normal case).** A full source run from the whole program
(with an empty initial stack, unique label definitions) to empty code is
simulated by one optimization round to the same endpoint. -/
theorem optimizeAsmRound_asteps [model : ExternalModel] {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {σf : List AVal} {y yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ ⟨[], σf, yf⟩) :
    ASteps (model := model) (optimizeAsmRound asm)
      ⟨optimizeAsmRound asm, [], y⟩ ⟨[], σf, yf⟩ := by
  have hcr := codeRel_optimizeRound asm
  obtain ⟨b', hb', hmb⟩ := steps_sim hnodup (fun _ h => h) hcr hsteps
    (List.suffix_refl asm) StkRefs.nil (.sync hcr)
  rw [match_empty_left hmb] at hb'
  exact hb'

/-- **Round bridge (halt case).** -/
theorem optimizeAsmRound_ahalt [model : ExternalModel] {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {y : EvmState} {bconf : AConf} {yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ bconf)
    (hhalt : AHalt (model := model) asm bconf yf) :
    ∃ b', ASteps (model := model) (optimizeAsmRound asm)
        ⟨optimizeAsmRound asm, [], y⟩ b'
      ∧ AHalt (model := model) (optimizeAsmRound asm) b' yf := by
  have hcr := codeRel_optimizeRound asm
  obtain ⟨b', hb', hmb⟩ := steps_sim hnodup (fun _ h => h) hcr hsteps
    (List.suffix_refl asm) StkRefs.nil (.sync hcr)
  exact ⟨b', hb', halt_sim hhalt hmb⟩

/-- One round keeps label definitions unique, so the next round's bridge
applies. -/
theorem optimizeAsmRound_nodup {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) :
    (labelDefs (optimizeAsmRound asm)).Nodup :=
  hnodup.sublist (codeRel_labelDefs_sublist (codeRel_optimizeRound asm))

/-- **Bridge (normal case).** Round bridges compose along the bounded
iteration: a full source run is simulated by `optimizeAsm` (any number of
rounds) to the same endpoint. -/
theorem optimizeAsmN_asteps [model : ExternalModel] (k : Nat) {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {σf : List AVal} {y yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ ⟨[], σf, yf⟩) :
    ASteps (model := model) (optimizeAsmN k asm)
      ⟨optimizeAsmN k asm, [], y⟩ ⟨[], σf, yf⟩ := by
  induction k generalizing asm with
  | zero => exact hsteps
  | succ k ih =>
    rw [optimizeAsmN]
    split
    · exact hsteps
    · exact ih (optimizeAsmRound_nodup hnodup) (optimizeAsmRound_asteps hnodup hsteps)

/-- **Bridge (halt case).** -/
theorem optimizeAsmN_ahalt [model : ExternalModel] (k : Nat) {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {y : EvmState} {bconf : AConf} {yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ bconf)
    (hhalt : AHalt (model := model) asm bconf yf) :
    ∃ b', ASteps (model := model) (optimizeAsmN k asm)
        ⟨optimizeAsmN k asm, [], y⟩ b'
      ∧ AHalt (model := model) (optimizeAsmN k asm) b' yf := by
  induction k generalizing asm bconf with
  | zero => exact ⟨bconf, hsteps, hhalt⟩
  | succ k ih =>
    rw [optimizeAsmN]
    split
    · exact ⟨bconf, hsteps, hhalt⟩
    · obtain ⟨b1, hb1, hh1⟩ := optimizeAsmRound_ahalt hnodup hsteps hhalt
      exact ih (optimizeAsmRound_nodup hnodup) hb1 hh1

/-- The packaged bridges for `optimizeAsm` (the production four-round pass),
consumed by `YulEvmCompiler.Correctness`. -/
theorem optimizeAsm_asteps [model : ExternalModel] {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {σf : List AVal} {y yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ ⟨[], σf, yf⟩) :
    ASteps (model := model) (optimizeAsm asm) ⟨optimizeAsm asm, [], y⟩ ⟨[], σf, yf⟩ :=
  optimizeAsmN_asteps 4 hnodup hsteps

theorem optimizeAsm_ahalt [model : ExternalModel] {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {y : EvmState} {bconf : AConf} {yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ bconf)
    (hhalt : AHalt (model := model) asm bconf yf) :
    ∃ b', ASteps (model := model) (optimizeAsm asm) ⟨optimizeAsm asm, [], y⟩ b'
      ∧ AHalt (model := model) (optimizeAsm asm) b' yf :=
  optimizeAsmN_ahalt 4 hnodup hsteps hhalt

end YulEvmCompiler.Peephole
