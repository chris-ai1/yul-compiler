import YulEvmCompiler.Asm
set_option warningAsError true
/-!
# YulEvmCompiler.AsmPeephole

An **assembly-level (Asm → Asm) peephole optimizer**: the transform and its
label-structure preservation. This is the "separate, Asm→Asm soundness
contract" layer: unlike the source (Yul→Yul) optimizer, it rewrites the
compiler's labelled control-flow IR directly, so it can exploit patterns the
source optimizer cannot express — the backend's calling convention, its
branch layout, and its label placement.

## The rewrites

Eight rewrites, each mined from actually-emitted code (the classic
`dup;pop` / `push;pop` / `swap n;swap n` peepholes never fire on this
backend's output):

1. **Late constant push** — `push v ; dup n ; swap1 ⟶ dup (n-1) ; push v`
   (and `push v ; dup1 ; swap1 ⟶ push v ; dup1`, where the `SWAP1` exchanges
   two copies of `v`). Duplicating a value from below a freshly pushed
   literal and then exchanging leaves exactly the stack you get by
   duplicating first and pushing on top: one `SWAP1` (3 gas, 1 byte)
   cheaper. Both backends emit this window whenever an operation's *topmost*
   operand is a literal and a lower operand is still live afterwards, which
   is the dominant shape in shift/mask code — `shr(0x80, x)` keeping `x`
   compiles to `push 0x80 ; dup2 ; swap1 ; shr` where solc emits
   `dup1 ; push 0x80 ; shr`. Measured on the executed instruction stream
   this window is the largest single remaining difference against solc:
   3,143 executions in `TickMath.getTickAtSqrtPriceSweep` (whose whole gap
   to solc was 14,506 gas) and 30,168 in
   `PositionStatusMap.nextContinuousTenThousand`.
2. **Flipped comparison** — `swap1 ; lt ⟶ gt` and the `gt`/`slt`/`sgt`
   mirrors, plus `swap1 ; add|mul|and|or|xor|eq ⟶ op` for the commutative
   ops. The code generator already tries both operand orders for the
   commutative built-ins; the ordered comparisons have a reversed twin
   opcode instead, and a `SWAP1` immediately in front of one is always that
   twin. 3 gas and 1 byte per site, 11,458 executions across the profiled
   fixtures.
3. **Return-slot assignment** — `push v ; swap1 ; pop ⟶ pop ; push v`.
   Identical net effect ("replace the top of the stack with the literal
   `v`"), one `SWAP1` (3 gas, 1 byte) cheaper. Emitted whenever a function
   body writes a constant into its top return slot.
4. **Branch inversion** — `jumpi l ; jump m ; label l ⟶
   op iszero ; jumpi m ; label l`. The `if cond {break/continue/leave}`
   shape: enter the guarded body via fall-through instead of a jump. Drops
   one `labelWidth`-byte address push (`labelWidth + 2` bytes total), and
   saves 8 gas whenever the condition is false (the common path for
   guard-style `if`s) at the cost of 3 gas when it is true. The label stays
   (other references may exist); only the local entry becomes fall-through.
5. **Double-`iszero` elimination** — `op iszero ; op iszero ; jumpi l ⟶
   jumpi l`. A branch only tests truthiness, which `iszero ∘ iszero`
   preserves; 2 bytes and 6 gas per condition evaluation. Only sound in the
   `jumpi` context (elsewhere the normalized 0/1 value is observable).
   Branch inversion produces these whenever the source condition already
   ended in `iszero`, so iteration matters (below).
6. **Jump to next** — `jump l ; label l ⟶ label l` and `jumpi l ; label l
   ⟶ pop ; label l`: both branches land at the fall-through anyway.
7. **Dead label elimination** — drop `label l` when `l` is referenced
   nowhere in the program (about a quarter of emitted labels: loop-exit and
   return labels nothing jumps to). Saves the 1-byte `JUMPDEST` and 1 gas
   per pass-through.
8. **Iteration** — `optimizeAsm` runs up to four rounds (`optimizeAsmN`,
   early-stopping at a fixpoint): removing a double `iszero` uncovers a
   branch-inversion window, and an inverted branch orphans its `jumpi`'s
   label for dead-label elimination.

## Structure

* `peepRun R` — the concrete linear scan (`R` = labels that may be
  referenced; `optimizeAsm` instantiates `R := labelRefs p`).
* `CodeRel R` — a **spec** relation between a source suffix and an optimized
  suffix. `optimizeAsm` is one *implementation*; `codeRel_optimize` proves
  its output is always `CodeRel`-related. `CodeRel` keeps `labelDefs` a
  sublist (retaining every label in `R`), keeps `labelRefs` a subset,
  preserves `findLabel` for labels in `R` (`codeRel_findLabel`), and does
  not grow `codeSize`; hence it preserves `WFProg` (`codeRel_wf`).

The forward simulation against the phase-A step relation lives in
`YulEvmCompiler.AsmPeepholeSound` (this module stays byte- and
semantics-free); `YulEvmCompiler.Compile.compile` inserts `optimizeAsm`
between `compileProgram` and `lowerProg`.
-/

namespace YulEvmCompiler

open YulSemantics.EVM (U256 Op)

/-! ### The concrete transform -/

/-- One slot shallower: the `dup` index reaching the same value once the
literal above it is gone (`DUP(n+1) ↦ DUP n`). -/
def dupPred (n : Fin 16) : Fin 16 :=
  ⟨n.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩

/-- The late-constant-push replacement for `push v ; dup n ; swap1`.

For `n.val > 0` the `dup` copies a value from *below* the pushed literal and
the `swap1` then puts the literal back on top: the same two stack cells are
reached by duplicating one slot shallower and pushing the literal after.
For `n.val = 0` the `dup` copies the literal itself, so the `swap1` exchanges
two equal words and is simply dead. -/
def latePush (v : U256) (n : Fin 16) : List Asm :=
  if 0 < n.val then [.dup (dupPred n), .push v] else [.push v, .dup n]

/-- The opcode computing the same result on the reversed operand order, when
one exists: the commutative built-ins are their own mirror and the ordered
comparisons mirror each other. `sub`/`div`/`shl`/… have no twin. -/
def flipOp : Op → Option Op
  | .add => some .add | .mul => some .mul | .and => some .and
  | .or => some .or | .xor => some .xor | .eq => some .eq
  | .lt => some .gt | .gt => some .lt
  | .slt => some .sgt | .sgt => some .slt
  | _ => none

/-! `latePush` emits two label-free instructions, one byte shorter than the
three-instruction window it replaces; these are the facts the structural
lemmas below need about it. -/

@[simp] theorem labelDefs_latePush (v : U256) (n : Fin 16) :
    labelDefs (latePush v n) = [] := by
  unfold latePush; split <;> simp [labelDefs, Asm.defines]

@[simp] theorem labelRefs_latePush (v : U256) (n : Fin 16) :
    labelRefs (latePush v n) = [] := by
  unfold latePush; split <;> simp [labelRefs, Asm.references]

theorem codeSize_latePush (v : U256) (n : Fin 16) :
    codeSize (latePush v n) = (Asm.push v).size + 1 := by
  unfold latePush
  split
  · simp only [codeSize_cons, codeSize_nil, Asm.size]; omega
  · simp only [codeSize_cons, codeSize_nil, Asm.size]

theorem findLabel_latePush {l : Label} (v : U256) (n : Fin 16) (c : List Asm) :
    findLabel l (latePush v n ++ c) = findLabel l c := by
  unfold latePush; split <;> simp [findLabel]

/-- The Asm-level peephole scan, relative to the set `R` of labels that may
be referenced. Rewrites every `push v ; dup n ; swap1` window to its
`latePush`, every `swap1 ; op` window whose `op` has a reversed twin to that
twin, every `push v ; swap1 ; pop` window to `pop ; push v`, every
`jumpi l ; jump m ; label l` window to `op iszero ; jumpi m ; label l`,
every `op eq ; op iszero ; jumpi l` window to `op sub ; jumpi l` (equal
words subtract to zero, and `jumpi` only tests truthiness),
every `op gas ; op call-op` window to the fused `gasCall` (realizing the
`gas()` read as the target's own `GAS` instruction), and
drops `label l` when `l ∉ R`. Other instructions pass through.

The `gasCall` fusion is the *only* entry of the fused instruction into a
program, and it relies on adjacency: the classic backend evaluates call
arguments right-to-left, so a `gas()` first argument is pushed immediately
before its call. If a transformation ever separates the pair, the fusion
does not fire and the surviving bare `.op .gas` is rejected at lowering
(`opTable .gas = none`) — the failure mode is a compile rejection, never a
miscompilation. -/
def peepRun (R : List Label) : List Asm → List Asm
  | .push v :: .swap ⟨0, _⟩ :: .pop :: rest =>
      .pop :: .push v :: peepRun R rest
  | .push v :: .dup n :: .swap m :: rest =>
      if m.val = 0 then latePush v n ++ peepRun R rest
      else .push v :: peepRun R (.dup n :: .swap m :: rest)
  | .swap n :: .op yop :: rest =>
      match (if n.val = 0 then flipOp yop else none) with
      | some yop' => .op yop' :: peepRun R rest
      | none => .swap n :: peepRun R (.op yop :: rest)
  | .op .iszero :: .op .iszero :: .jumpi l :: rest =>
      .jumpi l :: peepRun R rest
  | .op .eq :: .op .iszero :: .jumpi l :: .jump m :: .label l' :: rest =>
      -- an eq-sub rewrite must not preempt a branch-inversion window: there
      -- the inserted iszero cancels against this one (eq;jumpi beats
      -- sub;iszero;jumpi), so step over the eq and let brInv fire
      if l = l' then .op .eq :: peepRun R (.op .iszero :: .jumpi l :: .jump m :: .label l' :: rest)
      else .op .sub :: .jumpi l :: peepRun R (.jump m :: .label l' :: rest)
  | .op .eq :: .op .iszero :: .jumpi l :: rest =>
      .op .sub :: .jumpi l :: peepRun R rest
  | .op .gas :: .op yop :: rest =>
      match gasCallKind? yop with
      | some k => .gasCall k :: peepRun R rest
      | none => .op .gas :: peepRun R (.op yop :: rest)
  | .jumpi l :: .jump m :: .label l' :: rest =>
      if l = l' then .op .iszero :: .jumpi m :: .label l' :: peepRun R rest
      else .jumpi l :: peepRun R (.jump m :: .label l' :: rest)
  | .jumpi l :: .label l' :: rest =>
      if l = l' then .pop :: .label l' :: peepRun R rest
      else .jumpi l :: peepRun R (.label l' :: rest)
  | .jump l :: .label l' :: rest =>
      if l = l' then .label l' :: peepRun R rest
      else .jump l :: peepRun R (.label l' :: rest)
  | .label l :: rest =>
      if l ∈ R then .label l :: peepRun R rest else peepRun R rest
  | i :: rest => i :: peepRun R rest
  | [] => []
  termination_by p => p.length

/-! ### Verified fast dead-label test

`peepRun`'s only use of `R` is the membership test at `.label l`, and `R` is the
program's whole reference list — thousands of entries — so the scan is
`O(labels × references)` per round, four rounds per compile. `peepRunP` takes the
test as a `Label → Bool`, and `peepRunFast` supplies a `Std.HashSet`. `peepRun`
stays the specification `CodeRel` and the soundness proofs are stated about;
`@[csimp]` installs the fast version in compiled code. -/

/-- `peepRun` with the dead-label test abstracted. -/
def peepRunP (mem : Label → Bool) : List Asm → List Asm
  | .push v :: .swap ⟨0, _⟩ :: .pop :: rest =>
      .pop :: .push v :: peepRunP mem rest
  | .push v :: .dup n :: .swap m :: rest =>
      if m.val = 0 then latePush v n ++ peepRunP mem rest
      else .push v :: peepRunP mem (.dup n :: .swap m :: rest)
  | .swap n :: .op yop :: rest =>
      match (if n.val = 0 then flipOp yop else none) with
      | some yop' => .op yop' :: peepRunP mem rest
      | none => .swap n :: peepRunP mem (.op yop :: rest)
  | .op .iszero :: .op .iszero :: .jumpi l :: rest =>
      .jumpi l :: peepRunP mem rest
  | .op .eq :: .op .iszero :: .jumpi l :: .jump m :: .label l' :: rest =>
      -- an eq-sub rewrite must not preempt a branch-inversion window: there
      -- the inserted iszero cancels against this one (eq;jumpi beats
      -- sub;iszero;jumpi), so step over the eq and let brInv fire
      if l = l' then .op .eq :: peepRunP mem (.op .iszero :: .jumpi l :: .jump m :: .label l' :: rest)
      else .op .sub :: .jumpi l :: peepRunP mem (.jump m :: .label l' :: rest)
  | .op .eq :: .op .iszero :: .jumpi l :: rest =>
      .op .sub :: .jumpi l :: peepRunP mem rest
  | .op .gas :: .op yop :: rest =>
      match gasCallKind? yop with
      | some k => .gasCall k :: peepRunP mem rest
      | none => .op .gas :: peepRunP mem (.op yop :: rest)
  | .jumpi l :: .jump m :: .label l' :: rest =>
      if l = l' then .op .iszero :: .jumpi m :: .label l' :: peepRunP mem rest
      else .jumpi l :: peepRunP mem (.jump m :: .label l' :: rest)
  | .jumpi l :: .label l' :: rest =>
      if l = l' then .pop :: .label l' :: peepRunP mem rest
      else .jumpi l :: peepRunP mem (.label l' :: rest)
  | .jump l :: .label l' :: rest =>
      if l = l' then .label l' :: peepRunP mem rest
      else .jump l :: peepRunP mem (.label l' :: rest)
  | .label l :: rest =>
      if mem l then .label l :: peepRunP mem rest else peepRunP mem rest
  | i :: rest => i :: peepRunP mem rest
  | [] => []
  termination_by p => p.length

/-- A membership test that agrees with `· ∈ R` gives exactly `peepRun R`. -/
theorem peepRunP_eq_peepRun (mem : Label → Bool) (R : List Label)
    (h : ∀ l, mem l = decide (l ∈ R)) :
    ∀ p : List Asm, peepRunP mem p = peepRun R p := by
  intro p
  -- `simp_all` uses `h` from the local context to line the dead-label test up
  -- with `· ∈ R` in the two `.label` cases.
  fun_induction peepRunP mem p <;> rw [peepRun] <;> simp_all

/-- `peepRun` with the dead-label test backed by a hash set. -/
def peepRunFast (R : List Label) (p : List Asm) : List Asm :=
  peepRunP (Std.HashSet.ofList R).contains p

@[csimp] theorem peepRun_eq_peepRunFast : @peepRun = @peepRunFast := by
  funext R p
  refine (peepRunP_eq_peepRun _ R ?_ p).symm
  intro l
  rw [Std.HashSet.contains_ofList]
  simp

/-- One round of the Asm-level peephole pass: scan with the program's own
reference set, so exactly the unreferenced labels are dropped. -/
def optimizeAsmRound (p : List Asm) : List Asm := peepRun (labelRefs p) p

/-- Iterate rounds up to a small fixed bound, stopping early at a fixpoint.
Later rounds catch windows the previous round exposes: removing a double
`iszero` uncovers a branch-inversion window, and an inverted branch orphans
its `jumpi`'s label for dead-label elimination. -/
def optimizeAsmN : Nat → List Asm → List Asm
  | 0, p => p
  | k + 1, p =>
      let q := optimizeAsmRound p
      if q = p then p else optimizeAsmN k q

/-- The Asm-level peephole pass run by `compile`: four rounds (empirically
past the fixpoint of the whole corpus). -/
def optimizeAsm (p : List Asm) : List Asm := optimizeAsmN 4 p

/-! ### The spec relation on code suffixes -/

namespace Peephole

/-- Relates a source program suffix to a valid optimized suffix, relative to
the set `R` of labels that may be referenced anywhere in the program.
`optimizeAsm` is a particular strategy; `codeRel_optimize` shows its output
is always `CodeRel`-related to its input. Keeping the relation separate from
the concrete function makes the simulation and the label-structure lemmas
independent of the scan order. -/
inductive CodeRel (R : List Label) : List Asm → List Asm → Prop
  /-- Empty programs are related. -/
  | nil : CodeRel R [] []
  /-- Keep an instruction verbatim. -/
  | keep (i : Asm) {c c' : List Asm} : CodeRel R c c' → CodeRel R (i :: c) (i :: c')
  /-- Rewrite a return-slot window. `n` is `swap1` (`n.val = 0`). -/
  | window {v : U256} {n : Fin 16} (hn : n.val = 0) {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.push v :: .swap n :: .pop :: c) (.pop :: .push v :: c')
  /-- Push a literal *after* the duplication it was pushed in front of.
  `m` is `swap1`; `latePush` covers both the `n.val > 0` case (the `dup`
  reaches below the literal) and the `n.val = 0` case (the `swap1`
  exchanges two copies of the literal and just goes away). -/
  | latePush {v : U256} {n m : Fin 16} (hm : m.val = 0) {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.push v :: .dup n :: .swap m :: c) (latePush v n ++ c')
  /-- Replace `swap1 ; op` by the opcode that reads the operands in the
  opposite order. -/
  | flipCmp {n : Fin 16} (hn : n.val = 0) {yop yop' : Op}
      (hf : flipOp yop = some yop') {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.swap n :: .op yop :: c) (.op yop' :: c')
  /-- Invert a `jumpi`-over-`jump` branch whose target is the very next
  label. The label stays in place (other references may exist). -/
  | brInv {l m : Label} {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.jumpi l :: .jump m :: .label l :: c)
                (.op .iszero :: .jumpi m :: .label l :: c')
  /-- Drop a double `iszero` feeding a `jumpi`: the branch only tests
  truthiness, which `iszero ∘ iszero` preserves. Only sound in this
  context — anywhere else the normalized 0/1 value is observable. -/
  | dblIszero {l : Label} {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.op .iszero :: .op .iszero :: .jumpi l :: c) (.jumpi l :: c')
  /-- Replace an equality test whose (inverted) result only feeds a `jumpi`
  with a subtraction: `a - b` is zero exactly when `a = b`, and the branch
  only tests truthiness. Only sound in this context — anywhere else the
  normalized 0/1 value is observable. -/
  | eqSubJumpi {l : Label} {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.op .eq :: .op .iszero :: .jumpi l :: c)
                (.op .sub :: .jumpi l :: c')
  /-- Fuse a `gas()` read directly consumed as a call's gas argument into
  the fused instruction. The fused step's rule is exactly the composite of
  the two source steps, so the simulation reproduces whichever admitted
  word the source read. -/
  | gasFuse {k : GasCallKind} {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.op .gas :: .op k.op :: c) (.gasCall k :: c')
  /-- Drop a `jump` to the immediately following label. -/
  | jumpNext {l : Label} {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.jump l :: .label l :: c) (.label l :: c')
  /-- A `jumpi` to the immediately following label lands there either way:
  only the condition pop remains. -/
  | jumpiNext {l : Label} {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.jumpi l :: .label l :: c) (.pop :: .label l :: c')
  /-- Drop a label no instruction may reference. -/
  | dropLabel {l : Label} (hl : l ∉ R) {c c' : List Asm} :
      CodeRel R c c' → CodeRel R (.label l :: c) c'

/-- `peepRun` always produces a `CodeRel`-related program. -/
theorem codeRel_peepRun (R : List Label) (p : List Asm) : CodeRel R p (peepRun R p) := by
  fun_induction peepRun R p with
  | case1 v isLt rest ih => exact CodeRel.window (n := ⟨0, isLt⟩) rfl ih
  | case2 v n m rest hm ih => exact CodeRel.latePush hm ih
  | case3 v n m rest hm ih => exact CodeRel.keep _ ih
  | case4 n yop rest yop' hf ih =>
      have hn : n.val = 0 := by
        by_cases h : n.val = 0
        · exact h
        · simp [h] at hf
      exact CodeRel.flipCmp hn (by simpa [hn] using hf) ih
  | case5 n yop rest hf ih => exact CodeRel.keep _ ih
  | case6 l rest ih => exact CodeRel.dblIszero ih
  | case7 m l' rest ih => exact CodeRel.keep _ ih
  | case8 l m l' rest hne ih => exact CodeRel.eqSubJumpi ih
  | case9 l rest hexcl ih => exact CodeRel.eqSubJumpi ih
  | case10 yop rest k heq ih =>
      obtain rfl := eq_op_of_gasCallKind? heq
      exact CodeRel.gasFuse ih
  | case11 yop rest heq ih => exact CodeRel.keep _ ih
  | case12 m l' rest ih => exact CodeRel.brInv ih
  | case13 l m l' rest hne ih => exact CodeRel.keep _ ih
  | case14 l' rest ih => exact CodeRel.jumpiNext ih
  | case15 l l' rest hne ih => exact CodeRel.keep _ ih
  | case16 l' rest ih => exact CodeRel.jumpNext ih
  | case17 l l' rest hne ih => exact CodeRel.keep _ ih
  | case18 l rest hmem ih => exact CodeRel.keep _ ih
  | case19 l rest hmem ih => exact CodeRel.dropLabel hmem ih
  | case20 i rest _ _ _ _ _ _ _ _ _ _ _ ih => exact CodeRel.keep i ih
  | case21 => exact CodeRel.nil

/-- One `optimizeAsmRound` is `CodeRel`-related to its input, relative to the
program's own reference set. -/
theorem codeRel_optimizeRound (p : List Asm) :
    CodeRel (labelRefs p) p (optimizeAsmRound p) :=
  codeRel_peepRun (labelRefs p) p

/-! ### `CodeRel` preserves label structure -/

/-- Optimization only ever *removes* label definitions (and preserves their
order). -/
theorem codeRel_labelDefs_sublist {R : List Label} {P Q : List Asm}
    (h : CodeRel R P Q) : List.Sublist (labelDefs Q) (labelDefs P) := by
  induction h with
  | nil => exact .refl _
  | keep i _ ih =>
      rw [labelDefs_cons, labelDefs_cons]
      exact ih.append_left i.defines.toList
  | window _ _ ih =>
      simpa only [labelDefs_cons, Asm.defines, Option.toList_none,
        List.nil_append] using ih
  | latePush _ _ ih =>
      simpa only [labelDefs_append, labelDefs_latePush, labelDefs_cons,
        Asm.defines, Option.toList_none, List.nil_append] using ih
  | flipCmp _ _ _ ih =>
      simpa only [labelDefs_cons, Asm.defines, Option.toList_none,
        List.nil_append] using ih
  | brInv _ ih =>
      simp only [labelDefs_cons, Asm.defines, Option.toList_none,
        Option.toList_some, List.nil_append, List.singleton_append]
      exact ih.cons_cons _
  | dblIszero _ ih =>
      simpa only [labelDefs_cons, Asm.defines, Option.toList_none,
        List.nil_append] using ih
  | eqSubJumpi _ ih =>
      simpa only [labelDefs_cons, Asm.defines, Option.toList_none,
        List.nil_append] using ih
  | gasFuse _ ih =>
      simpa only [labelDefs_cons, Asm.defines, Option.toList_none,
        List.nil_append] using ih
  | jumpNext _ ih =>
      simp only [labelDefs_cons, Asm.defines, Option.toList_none,
        Option.toList_some, List.nil_append, List.singleton_append]
      exact ih.cons_cons _
  | jumpiNext _ ih =>
      simp only [labelDefs_cons, Asm.defines, Option.toList_none,
        Option.toList_some, List.nil_append, List.singleton_append]
      exact ih.cons_cons _
  | dropLabel _ _ ih =>
      simp only [labelDefs_cons, Asm.defines, Option.toList_some,
        List.singleton_append]
      exact ih.cons _

/-- A label in `R` is never dropped. -/
theorem codeRel_labelDefs_mem {R : List Label} {P Q : List Asm}
    (h : CodeRel R P Q) {l : Label} (hR : l ∈ R) (hl : l ∈ labelDefs P) :
    l ∈ labelDefs Q := by
  induction h with
  | nil => exact hl
  | keep i _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact mem_labelDefs_cons.mpr (Or.inl h')
      · exact mem_labelDefs_cons.mpr (Or.inr (ih h'))
  | window _ _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp)
        · rcases mem_labelDefs_cons.mp h'' with h3 | h3
          · exact absurd h3 (by simp)
          · exact mem_labelDefs_cons.mpr (Or.inr
              (mem_labelDefs_cons.mpr (Or.inr (ih h3))))
  | latePush _ _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp)
        · rcases mem_labelDefs_cons.mp h'' with h3 | h3
          · exact absurd h3 (by simp)
          · simpa only [labelDefs_append, labelDefs_latePush,
              List.nil_append] using ih h3
  | flipCmp _ _ _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp)
        · exact mem_labelDefs_cons.mpr (Or.inr (ih h''))
  | brInv _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp)
        · rcases mem_labelDefs_cons.mp h'' with h3 | h3
          · exact mem_labelDefs_cons.mpr (Or.inr
              (mem_labelDefs_cons.mpr (Or.inr (mem_labelDefs_cons.mpr (Or.inl h3)))))
          · exact mem_labelDefs_cons.mpr (Or.inr
              (mem_labelDefs_cons.mpr (Or.inr (mem_labelDefs_cons.mpr (Or.inr (ih h3))))))
  | dblIszero _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp)
        · rcases mem_labelDefs_cons.mp h'' with h3 | h3
          · exact absurd h3 (by simp)
          · exact mem_labelDefs_cons.mpr (Or.inr (ih h3))
  | gasFuse _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp)
        · exact mem_labelDefs_cons.mpr (Or.inr (ih h''))
  | eqSubJumpi _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp)
        · rcases mem_labelDefs_cons.mp h'' with h3 | h3
          · exact absurd h3 (by simp)
          · exact mem_labelDefs_cons.mpr (Or.inr
              (mem_labelDefs_cons.mpr (Or.inr (ih h3))))
  | jumpNext _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact mem_labelDefs_cons.mpr (Or.inl h'')
        · exact mem_labelDefs_cons.mpr (Or.inr (ih h''))
  | jumpiNext _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact mem_labelDefs_cons.mpr (Or.inr (mem_labelDefs_cons.mpr (Or.inl h'')))
        · exact mem_labelDefs_cons.mpr (Or.inr (mem_labelDefs_cons.mpr (Or.inr (ih h''))))
  | dropLabel hdrop _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · cases h'; exact absurd hR hdrop
      · exact ih h'

/-- Membership in the referenced labels of a cons, by cases on the head. -/
theorem mem_labelRefs_cons {l : Label} {i : Asm} {p : List Asm} :
    l ∈ labelRefs (i :: p) ↔ i.references = some l ∨ l ∈ labelRefs p := by
  rw [labelRefs_cons, List.mem_append]
  cases h : i.references <;> simp [eq_comm]

/-- Optimization never introduces a label reference. -/
theorem codeRel_labelRefs_subset {R : List Label} {P Q : List Asm}
    (h : CodeRel R P Q) : ∀ l ∈ labelRefs Q, l ∈ labelRefs P := by
  induction h with
  | nil => exact fun l hl => hl
  | keep i _ ih =>
      intro l hl
      rcases mem_labelRefs_cons.mp hl with h' | h'
      · exact mem_labelRefs_cons.mpr (Or.inl h')
      · exact mem_labelRefs_cons.mpr (Or.inr (ih l h'))
  | window _ _ ih =>
      intro l hl
      rcases mem_labelRefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp [Asm.references])
      · rcases mem_labelRefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp [Asm.references])
        · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
            (mem_labelRefs_cons.mpr (Or.inr (ih l h''))))))
  | latePush _ _ ih =>
      intro l' hl'
      rw [labelRefs_append, labelRefs_latePush, List.nil_append] at hl'
      exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
        (mem_labelRefs_cons.mpr (Or.inr (ih l' hl'))))))
  | flipCmp _ _ _ ih =>
      intro l' hl'
      rcases mem_labelRefs_cons.mp hl' with h' | h'
      · exact absurd h' (by simp [Asm.references])
      · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr (ih l' h'))))
  | brInv _ ih =>
      intro l' hl'
      rcases mem_labelRefs_cons.mp hl' with h' | h'
      · exact absurd h' (by simp [Asm.references])
      · rcases mem_labelRefs_cons.mp h' with h'' | h''
        · -- the optimized `jumpi m` reference maps to the source `jump m`
          exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr
            (Or.inl (by simpa [Asm.references] using h''))))
        · rcases mem_labelRefs_cons.mp h'' with h3 | h3
          · exact absurd h3 (by simp [Asm.references])
          · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
              (mem_labelRefs_cons.mpr (Or.inr (ih l' h3))))))
  | dblIszero _ ih =>
      intro l' hl'
      rcases mem_labelRefs_cons.mp hl' with h' | h'
      · -- the kept `jumpi l` reference maps to the source `jumpi l`
        exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
          (mem_labelRefs_cons.mpr (Or.inl h')))))
      · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
          (mem_labelRefs_cons.mpr (Or.inr (ih l' h'))))))
  | gasFuse _ ih =>
      intro l' hl'
      rcases mem_labelRefs_cons.mp hl' with h' | h'
      · exact absurd h' (by simp [Asm.references])
      · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
          (ih l' h'))))
  | eqSubJumpi _ ih =>
      intro l' hl'
      rcases mem_labelRefs_cons.mp hl' with h' | h'
      · exact absurd h' (by simp [Asm.references])
      · rcases mem_labelRefs_cons.mp h' with h'' | h''
        · -- the kept `jumpi l` reference maps to the source `jumpi l`
          exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
            (mem_labelRefs_cons.mpr (Or.inl h'')))))
        · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
            (mem_labelRefs_cons.mpr (Or.inr (ih l' h''))))))
  | jumpNext _ ih =>
      intro l' hl'
      rcases mem_labelRefs_cons.mp hl' with h' | h'
      · exact absurd h' (by simp [Asm.references])
      · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr (ih l' h'))))
  | jumpiNext _ ih =>
      intro l' hl'
      rcases mem_labelRefs_cons.mp hl' with h' | h'
      · exact absurd h' (by simp [Asm.references])
      · rcases mem_labelRefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp [Asm.references])
        · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr (ih l' h''))))
  | dropLabel _ _ ih =>
      intro l' hl'
      exact mem_labelRefs_cons.mpr (Or.inr (ih l' hl'))

/-- Optimization never grows the lowered byte size. -/
theorem codeRel_codeSize_le {R : List Label} {P Q : List Asm}
    (h : CodeRel R P Q) : codeSize Q ≤ codeSize P := by
  induction h with
  | nil => simp
  | keep i _ ih => rw [codeSize_cons, codeSize_cons]; omega
  | window _ _ ih => simp only [codeSize_cons, Asm.size]; omega
  | @latePush v n m _ c c' _ ih =>
      have hsz := codeSize_latePush v n
      simp only [codeSize_append, codeSize_cons, Asm.size, hsz]
      omega
  | flipCmp _ _ _ ih => simp only [codeSize_cons, Asm.size]; omega
  | brInv _ ih => simp only [codeSize_cons, Asm.size]; omega
  | dblIszero _ ih => simp only [codeSize_cons, Asm.size]; omega
  | gasFuse _ ih => simp only [codeSize_cons, Asm.size]; omega
  | eqSubJumpi _ ih => simp only [codeSize_cons, Asm.size]; omega
  | jumpNext _ ih => simp only [codeSize_cons, Asm.size]; omega
  | jumpiNext _ ih => simp only [codeSize_cons, Asm.size]; omega
  | dropLabel _ _ ih => simp only [codeSize_cons, Asm.size]; omega

/-- `findLabel` is preserved for every label that may be referenced, and the
found suffixes are again related. -/
theorem codeRel_findLabel {R : List Label} {P Q : List Asm} (h : CodeRel R P Q)
    {l : Label} (hR : l ∈ R) :
    ∀ {tgt : List Asm}, findLabel l P = some tgt →
      ∃ otgt, findLabel l Q = some otgt ∧ CodeRel R tgt otgt := by
  induction h with
  | nil => intro tgt hf; simp [findLabel] at hf
  | keep i hc ih =>
      intro tgt hf
      rw [findLabel] at hf
      by_cases hi : i = .label l
      · subst hi; rw [if_pos rfl] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨_, by rw [findLabel, if_pos rfl], hc⟩
      · rw [if_neg hi] at hf
        obtain ⟨otgt, ho, hr⟩ := ih hf
        exact ⟨otgt, by rw [findLabel, if_neg hi]; exact ho, hr⟩
  | @brInv l0 m c c' hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp), findLabel] at hf
      by_cases hi : (Asm.label l0 : Asm) = .label l
      · rw [if_pos hi] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨_, by
          rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp),
            findLabel, if_pos hi], hc⟩
      · rw [if_neg hi] at hf
        obtain ⟨otgt, ho, hr⟩ := ih hf
        exact ⟨otgt, by
          rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp),
            findLabel, if_neg hi]; exact ho, hr⟩
  | window hn hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp),
        findLabel, if_neg (by simp)] at hf
      obtain ⟨otgt, ho, hr⟩ := ih hf
      exact ⟨otgt, by
        rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp)]
        exact ho, hr⟩
  | @latePush v n m _ c c' hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp),
        findLabel, if_neg (by simp)] at hf
      obtain ⟨otgt, ho, hr⟩ := ih hf
      exact ⟨otgt, by rw [findLabel_latePush]; exact ho, hr⟩
  | flipCmp hn hf' hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp)] at hf
      obtain ⟨otgt, ho, hr⟩ := ih hf
      exact ⟨otgt, by rw [findLabel, if_neg (by simp)]; exact ho, hr⟩
  | dblIszero hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp),
        findLabel, if_neg (by simp)] at hf
      obtain ⟨otgt, ho, hr⟩ := ih hf
      exact ⟨otgt, by rw [findLabel, if_neg (by simp)]; exact ho, hr⟩
  | gasFuse hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp)] at hf
      obtain ⟨otgt, ho, hr⟩ := ih hf
      exact ⟨otgt, by rw [findLabel, if_neg (by simp)]; exact ho, hr⟩
  | eqSubJumpi hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp),
        findLabel, if_neg (by simp)] at hf
      obtain ⟨otgt, ho, hr⟩ := ih hf
      exact ⟨otgt, by rw [findLabel, if_neg (by simp), findLabel,
        if_neg (by simp)]; exact ho, hr⟩
  | @jumpNext l0 c c' hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel] at hf
      by_cases hi : (Asm.label l0 : Asm) = .label l
      · rw [if_pos hi] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨_, by rw [findLabel, if_pos hi], hc⟩
      · rw [if_neg hi] at hf
        obtain ⟨otgt, ho, hr⟩ := ih hf
        exact ⟨otgt, by rw [findLabel, if_neg hi]; exact ho, hr⟩
  | @jumpiNext l0 c c' hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel] at hf
      by_cases hi : (Asm.label l0 : Asm) = .label l
      · rw [if_pos hi] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨_, by rw [findLabel, if_neg (by simp), findLabel, if_pos hi], hc⟩
      · rw [if_neg hi] at hf
        obtain ⟨otgt, ho, hr⟩ := ih hf
        exact ⟨otgt, by rw [findLabel, if_neg (by simp), findLabel, if_neg hi]; exact ho, hr⟩
  | @dropLabel l0 hdrop c c' hc ih =>
      intro tgt hf
      have hne : (Asm.label l0 : Asm) ≠ .label l := by
        intro hEq
        exact hdrop (by cases hEq; exact hR)
      rw [findLabel, if_neg hne] at hf
      exact ih hf

/-- `CodeRel` preserves whole-program well-formedness (when `R` covers the
program's references), so lowering the optimized program still succeeds. -/
theorem codeRel_wf {R : List Label} {P Q : List Asm} (h : CodeRel R P Q)
    (hRefs : ∀ l ∈ labelRefs P, l ∈ R) (hw : WFProg P) : WFProg Q where
  nodup := hw.nodup.sublist (codeRel_labelDefs_sublist h)
  refsDefined := by
    intro l hl
    have hlP := codeRel_labelRefs_subset h l hl
    exact codeRel_labelDefs_mem h (hRefs l hlP) (hw.refsDefined l hlP)
  small := by have := codeRel_codeSize_le h; have := hw.small; omega

/-- `CodeRel R [] Q` forces `Q = []`. -/
theorem codeRel_nil_left {R : List Label} {Q : List Asm}
    (h : CodeRel R [] Q) : Q = [] := by
  cases h; rfl

end Peephole

/-- Iterating peephole rounds never grows the lowered byte size. -/
theorem codeSize_optimizeAsmN_le (k : Nat) (p : List Asm) :
    codeSize (optimizeAsmN k p) ≤ codeSize p := by
  induction k generalizing p with
  | zero => simp [optimizeAsmN]
  | succ k ih =>
    simp only [optimizeAsmN]
    split
    · exact Nat.le_refl _
    · exact le_trans (ih _)
        (Peephole.codeRel_codeSize_le (Peephole.codeRel_optimizeRound p))

/-- The Asm peephole pass never grows the lowered byte size, so it preserves
`WFProg`'s `codeSize` bound (`codeRel_wf`) — restated for `optimizeAsm`. -/
theorem codeSize_optimizeAsm_le (p : List Asm) :
    codeSize (optimizeAsm p) ≤ codeSize p :=
  codeSize_optimizeAsmN_le 4 p

end YulEvmCompiler
