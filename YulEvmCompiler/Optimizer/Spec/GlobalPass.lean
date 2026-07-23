import YulEvmCompiler.Optimizer.Spec.LocalPass

set_option warningAsError true

/-!
# YulEvmCompiler.Optimizer.Spec.GlobalPass

The **global** tier of the optimizer-pass specification, complementing the local
tier in `Spec/LocalPass.lean`.

## Two tiers of pass

A `LocalPass` is a `Block → Block` rewrite whose obligation is `EquivBlock` —
*contextual* equivalence, quantified over **every** ambient function/variable
environment and state. That congruence is what lets a local rewrite be applied
to a nested subterm and composed through `YulSemantics.Equiv`'s syntax
congruences: it is sound in *any* position.

A `GlobalPass` is an `Object → Object` transform — a **whole-program
normalization**. Its obligation is stated at the `YulSemantics.Run` level (the
empty-environment, top-of-execution interface), because that is where an object's
code actually runs:

```
RunObject o L V st out  :=  Run evm o.codeBlock L.initState V st out   -- base = []
```

This is deliberately weaker than `EquivBlock`, and deliberately the *right* notion
for normalizations that are only sound at the root: e.g. hoisting a nested
function to the top changes name resolution relative to an enclosing block, so it
preserves behavior only where the ambient function environment is empty. Taking an
**`Object`** (never a bare `Block`) makes "root-only" a property of the *type* —
a global pass cannot even be named at a nested block — and lets it recurse into
sub-objects, each of which is its own root (a separately-deployed runtime).

Because `EquivBlock ⇒ Run`-equivalence (specialise `funs = []`, `V = []`), every
`LocalPass` lifts to a `GlobalPass` by mapping it over every code block of the
tree (`LocalPass.toGlobal`); so the object-observational level is the common
currency in which local and global passes compose.

## Normal-form pre/post-conditions

Whether a `GlobalPass` establishes (or requires) a normal-form property (see
`Normalization/NormalForm.lean`) is expressed **per pass**, as a separate theorem
about that pass — required as a precondition by some later passes but not all —
rather than as a field of this structure. The structure's sole obligation is
semantic (`sound`).
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### Whole-program (`Run`) equivalence of blocks -/

/-- Two blocks have identical whole-program behaviour: run from the empty
function/variable environment (the top-of-execution interface, `Run`), they yield
the same final environment, state, and outcome from every initial state. This is
the specialisation of `EquivBlock` to `funs = []`, `V = []`. -/
def RunEquivBlock (D : Dialect) [DecidableEq D.Value] (b b' : Block D.Op) : Prop :=
  ∀ st0 V' st' o, Run D b st0 V' st' o ↔ Run D b' st0 V' st' o

namespace RunEquivBlock

theorem refl (b : Block D.Op) : RunEquivBlock D b b := fun _ _ _ _ => Iff.rfl

theorem symm {b b' : Block D.Op} (h : RunEquivBlock D b b') : RunEquivBlock D b' b :=
  fun st0 V' st' o => (h st0 V' st' o).symm

theorem trans {b b' b'' : Block D.Op} (h : RunEquivBlock D b b') (h' : RunEquivBlock D b' b'') :
    RunEquivBlock D b b'' := fun st0 V' st' o => (h st0 V' st' o).trans (h' st0 V' st' o)

end RunEquivBlock

/-- `EquivBlock` (contextual equivalence) implies `RunEquivBlock` (whole-program
equivalence): the local-pass obligation is strictly stronger than the global one.
This is the bridge that lets a `LocalPass` become a `GlobalPass`. -/
theorem RunEquivBlock.of_equivBlock {b b' : Block D.Op} (h : EquivBlock D b b') :
    RunEquivBlock D b b' :=
  fun st0 V' st' o => h [] [] st0 V' st' o

/-! ### Whole-tree object equivalence -/

/- Two objects behave identically as programs: same name and data segments, their
top code blocks are `RunEquivBlock`, and their sub-objects are pairwise equivalent
(each sub-object is a separately-deployed runtime, i.e. its own root). -/
mutual
def ObjEquiv (D : Dialect) [DecidableEq D.Value] : Object D.Op → Object D.Op → Prop
  | .mk n c subs data, .mk n' c' subs' data' =>
      n = n' ∧ data = data' ∧ RunEquivBlock D c c' ∧ ObjEquivList D subs subs'
def ObjEquivList (D : Dialect) [DecidableEq D.Value] :
    List (Object D.Op) → List (Object D.Op) → Prop
  | [], [] => True
  | o :: os, o' :: os' => ObjEquiv D o o' ∧ ObjEquivList D os os'
  | _, _ => False
end

mutual
theorem ObjEquiv.refl : ∀ (o : Object D.Op), ObjEquiv D o o
  | .mk _ c subs _ => ⟨rfl, rfl, RunEquivBlock.refl c, ObjEquivList.refl subs⟩
theorem ObjEquivList.refl : ∀ (os : List (Object D.Op)), ObjEquivList D os os
  | [] => trivial
  | o :: os => ⟨ObjEquiv.refl o, ObjEquivList.refl os⟩
end

mutual
theorem ObjEquiv.trans : ∀ {x y z : Object D.Op}, ObjEquiv D x y → ObjEquiv D y z → ObjEquiv D x z
  | .mk _ _ _ _, .mk _ _ _ _, .mk _ _ _ _, h1, h2 =>
      ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1,
        h1.2.2.2.trans h2.2.2.2⟩
theorem ObjEquivList.trans : ∀ {xs ys zs : List (Object D.Op)},
    ObjEquivList D xs ys → ObjEquivList D ys zs → ObjEquivList D xs zs
  | [], [], [], _, _ => trivial
  | [], [], _ :: _, _, h2 => h2.elim
  | [], _ :: _, _, h1, _ => h1.elim
  | _ :: _, [], _, h1, _ => h1.elim
  | _ :: _, _ :: _, [], _, h2 => h2.elim
  | _ :: _, _ :: _, _ :: _, h1, h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
end

/-! ### The global pass -/

/-- A **verified global (whole-program) pass**: an `Object → Object` transform
bundled with a proof that it preserves whole-tree behaviour (`ObjEquiv`, i.e.
`Run`-equivalence of every code block, with object structure preserved). -/
structure GlobalPass (D : Dialect) [DecidableEq D.Value] where
  /-- The whole-object transformation. -/
  run : Object D.Op → Object D.Op
  /-- Proof obligation: the transform preserves whole-program semantics. -/
  sound : ∀ o, ObjEquiv D o (run o)

namespace GlobalPass

/-- The operative consequence at the object boundary: a global pass leaves the top
code block's whole-program behaviour unchanged (`RunObject`/`RunResolvedObject`
depend only on that block). -/
theorem soundTop (P : GlobalPass D) (o : Object D.Op) :
    RunEquivBlock D o.codeBlock (P.run o).codeBlock := by
  have h := P.sound o
  cases o with
  | mk n c subs data =>
      cases hr : P.run (.mk n c subs data) with
      | mk n' c' subs' data' => rw [hr] at h; exact h.2.2.1

/-- The do-nothing global pass. -/
def id : GlobalPass D where
  run := fun o => o
  sound := ObjEquiv.refl

@[simp] theorem id_run (o : Object D.Op) : (id (D := D)).run o = o := rfl

/-- Composition: `comp P Q` runs `Q` then `P`, sound by transitivity of `ObjEquiv`. -/
def comp (P Q : GlobalPass D) : GlobalPass D where
  run := fun o => P.run (Q.run o)
  sound := fun o => (Q.sound o).trans (P.sound (Q.run o))

@[simp] theorem comp_run (P Q : GlobalPass D) (o : Object D.Op) :
    (comp P Q).run o = P.run (Q.run o) := rfl

/-- Fold a list of global passes into one (head runs first), seeded by `id`. -/
def ofList (ps : List (GlobalPass D)) : GlobalPass D :=
  ps.foldr (fun p acc => comp acc p) id

@[simp] theorem ofList_nil : ofList ([] : List (GlobalPass D)) = id := rfl
@[simp] theorem ofList_cons (p : GlobalPass D) (ps : List (GlobalPass D)) :
    ofList (p :: ps) = comp (ofList ps) p := rfl

end GlobalPass

/-! ### Bridge: every local pass is a global pass -/

/- Apply a block transform to every code block of an object tree (the object's
own code and, recursively, every sub-object's). -/
mutual
def mapObjCode (f : Block D.Op → Block D.Op) : Object D.Op → Object D.Op
  | .mk n c subs data => .mk n (f c) (mapObjCodes f subs) data
def mapObjCodes (f : Block D.Op → Block D.Op) : List (Object D.Op) → List (Object D.Op)
  | [] => []
  | o :: os => mapObjCode f o :: mapObjCodes f os
end

mutual
theorem objEquiv_mapObjCode {f : Block D.Op → Block D.Op}
    (hf : ∀ b, RunEquivBlock D b (f b)) : ∀ (o : Object D.Op), ObjEquiv D o (mapObjCode f o)
  | .mk _ c subs _ => ⟨rfl, rfl, hf c, objEquiv_mapObjCodes hf subs⟩
theorem objEquiv_mapObjCodes {f : Block D.Op → Block D.Op}
    (hf : ∀ b, RunEquivBlock D b (f b)) :
    ∀ (os : List (Object D.Op)), ObjEquivList D os (mapObjCodes f os)
  | [] => trivial
  | o :: os => ⟨objEquiv_mapObjCode hf o, objEquiv_mapObjCodes hf os⟩
end

/-- **A local pass lifts to a global pass.** Apply it to every code block of the
tree; sound because `EquivBlock ⇒ RunEquivBlock`. -/
def LocalPass.toGlobal (P : LocalPass D) : GlobalPass D where
  run := mapObjCode P.run
  sound := objEquiv_mapObjCode (fun b => RunEquivBlock.of_equivBlock (P.sound b))

@[simp] theorem LocalPass.toGlobal_run (P : LocalPass D) (o : Object D.Op) :
    P.toGlobal.run o = mapObjCode P.run o := rfl

/-! ### Guard-and-no-op: lifting a conditionally-sound transform -/

/-- The block transform underlying a guarded global pass: apply `run` where the
`Bool` `guard` holds, else leave the block unchanged. -/
def guardedBlock (guard : Block D.Op → Bool) (run : Block D.Op → Block D.Op)
    (b : Block D.Op) : Block D.Op :=
  if guard b = true then run b else b

/-- **Guard-and-no-op combinator.** Turn a block transform that is only known
semantics-preserving under a decidable `guard` into an *unconditionally* sound
`GlobalPass`: it rewrites a code block exactly where `guard` holds (and where, by
`h`, the rewrite preserves whole-program behaviour) and is the identity
everywhere else. This packages the standard pattern for normalizations sound only
under a precondition (uniqueness, well-scopedness, …) — the caller supplies the
`guard`, the transform, and the conditional `RunEquivBlock`. -/
def GlobalPass.ofGuardedBlock (guard : Block D.Op → Bool) (run : Block D.Op → Block D.Op)
    (h : ∀ b, guard b = true → RunEquivBlock D b (run b)) : GlobalPass D where
  run := mapObjCode (guardedBlock guard run)
  sound := objEquiv_mapObjCode (fun b => by
    unfold guardedBlock
    by_cases hb : guard b = true
    · rw [if_pos hb]; exact h b hb
    · rw [if_neg hb]; exact RunEquivBlock.refl b)

@[simp] theorem GlobalPass.ofGuardedBlock_run (guard : Block D.Op → Bool)
    (run : Block D.Op → Block D.Op) (h) (o : Object D.Op) :
    (GlobalPass.ofGuardedBlock guard run h).run o = mapObjCode (guardedBlock guard run) o := rfl

end YulEvmCompiler.Optimizer
