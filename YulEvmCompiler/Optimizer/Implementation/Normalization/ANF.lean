import YulSemantics.Dialect.EVM
/-!
# ANF / expression-splitting normalizer — structural core

A shared normalization for the optimizer: rewrite Yul so **every operand is an
atom** (a variable or literal), by binding each nested sub-expression to a fresh
`let`. E.g. `sstore(add(x, 1), mul(y, 2))` becomes

```text
let t0 := add(x, 1)
let t1 := mul(y, 2)
sstore(t0, t1)
```

This is the front-end normal form the `Optimizer.Core` expression IR already
assumes (`Core.ingest` accepts exactly an atom or one operator applied to
atoms), so ANF maximizes the fragment `Simplify`/inlining can act on, and it
turns store/load reasoning into a variable-level analysis for the dataflow
passes.

This file is the **structural** core: the expression flattener `flatten` and a
machine-checked proof that its output really is in ANF — every emitted argument
is an atom, and every prelude statement is a single-variable `let` whose
right-hand side applies one operator to atoms (the `preludeOK` shape). The
statement/block wrapper and the *semantic* (`EquivBlock`)-preservation proof —
which must also get Yul's right-to-left argument evaluation order and fresh-name
non-capture right — are the following steps; `flatten` already fixes the binding
order to match evaluation so that proof is available.

Freshness follows `FreshenCalls`: temporaries share a prefix `P` chosen so no
program identifier starts with it, so distinct indices give distinct,
capture-free names with no counter threaded through the eventual proof.
-/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics YulSemantics.EVM

/-! ### The ANF shape predicates -/

/-- An **atom**: a variable or a literal — a leaf operand with no sub-expression
to split. (Forwarding separately restricts to `stringFree` values; ANF only
cares that operands are leaves.) -/
def isAtom : Expr Op → Bool
  | .var _ => true
  | .lit _ => true
  | _ => false

/-- Every element of an argument list is an atom. -/
def atomicArgs : List (Expr Op) → Bool
  | [] => true
  | e :: rest => isAtom e && atomicArgs rest

/-- A right-hand side allowed at the head of an ANF `let`: an atom, or a single
operator/`call` applied to atoms (no further nesting). -/
def isFlatRhs : Expr Op → Bool
  | .builtin _ args => atomicArgs args
  | .call _ args => atomicArgs args
  | e => isAtom e

/-- A well-formed prelude statement: `let t := rhs` binding exactly one variable
to a flat right-hand side. -/
def preludeOK : Stmt Op → Bool
  | .letDecl [_] (some rhs) => isFlatRhs rhs
  | _ => false

/-! ### Fresh temporaries -/

/-- The `k`-th temporary under prefix `P`. A unary suffix is used so that
distinctness of indices is a trivial `List.length` fact (rather than depending on
`Nat.repr` injectivity); every name starts with `P`. (A compact decimal suffix
can be substituted once `Nat`-`toString` injectivity is available.) -/
def tempName (P : String) (k : Nat) : Ident := P ++ String.ofList (List.replicate (k + 1) 't')

/-- Distinct temporary indices give distinct names. -/
theorem tempName_inj {P : String} {i j : Nat} (h : tempName P i = tempName P j) : i = j := by
  simp only [tempName, String.append_right_inj, String.ofList_inj] at h
  have := congrArg List.length h
  simp only [List.length_replicate] at this
  omega

/-! ### The flattener

`flatten P k e = (k', prelude, atom)`: `prelude` is a list of ANF `let`s that
must run before the result, and `atom` is the atom denoting `e`'s value. `k`
is the next-free temporary index, threaded left-to-right through the recursion;
arguments are flattened **right-to-left** (Yul's evaluation order) and their
preludes concatenated in that order, so the eventual semantic proof sees effects
in the original order. -/
mutual
def flatten (P : String) (k : Nat) : Expr Op → Nat × List (Stmt Op) × Expr Op
  | .var x => (k, [], .var x)
  | .lit l => (k, [], .lit l)
  | .builtin op args =>
      let (k1, pre, atoms) := flattenArgs P k args
      let t := tempName P k1
      (k1 + 1, pre ++ [.letDecl [t] (some (.builtin op atoms))], .var t)
  | .call f args =>
      let (k1, pre, atoms) := flattenArgs P k args
      let t := tempName P k1
      (k1 + 1, pre ++ [.letDecl [t] (some (.call f atoms))], .var t)

/-- Flatten an argument list right-to-left, returning the accumulated prelude
(in evaluation order) and the list of atoms in source order. -/
def flattenArgs (P : String) (k : Nat) : List (Expr Op) → Nat × List (Stmt Op) × List (Expr Op)
  | [] => (k, [], [])
  | e :: rest =>
      -- evaluate `rest` (to the right) first, then `e`
      let (k1, preRest, atomsRest) := flattenArgs P k rest
      let (k2, preHead, atomHead) := flatten P k1 e
      (k2, preRest ++ preHead, atomHead :: atomsRest)
end

/-! ### Temp-index monotonicity

`flatten`/`flattenArgs` only advance the fresh-temp counter, and each temporary
they emit uses an index in the half-open range `[k, result-counter)`. Disjoint
counter ranges therefore give distinct temporary names — the freshness fact the
soundness proof's flatten-correctness needs. -/
mutual
theorem flatten_k_mono (P : String) (k : Nat) (e : Expr Op) : k ≤ (flatten P k e).1 := by
  match e with
  | .var _ => exact Nat.le_refl _
  | .lit _ => exact Nat.le_refl _
  | .builtin _ args =>
      simp only [flatten]
      exact Nat.le_trans (flattenArgs_k_mono P k args) (Nat.le_succ _)
  | .call _ args =>
      simp only [flatten]
      exact Nat.le_trans (flattenArgs_k_mono P k args) (Nat.le_succ _)

theorem flattenArgs_k_mono (P : String) (k : Nat) (args : List (Expr Op)) :
    k ≤ (flattenArgs P k args).1 := by
  match args with
  | [] => exact Nat.le_refl _
  | e :: rest =>
      simp only [flattenArgs]
      exact Nat.le_trans (flattenArgs_k_mono P k rest) (flatten_k_mono P _ e)
end

/-! ### Structural correctness: the output is in ANF -/

mutual
/-- The result of `flatten` is an atom, and its prelude is all well-formed ANF
`let`s. -/
theorem flatten_ok (P : String) (k : Nat) (e : Expr Op) :
    isAtom (flatten P k e).2.2 = true ∧
      ∀ s ∈ (flatten P k e).2.1, preludeOK s = true := by
  match e with
  | .var x => exact ⟨rfl, by intro s hs; simp [flatten] at hs⟩
  | .lit l => exact ⟨rfl, by intro s hs; simp [flatten] at hs⟩
  | .builtin op args =>
      refine ⟨rfl, ?_⟩
      intro st hst
      simp only [flatten] at hst
      rcases List.mem_append.mp hst with hpre | htail
      · exact (flattenArgs_ok P k args).2 st hpre
      · rcases List.mem_singleton.mp htail with rfl
        simp only [preludeOK, isFlatRhs]
        exact (flattenArgs_ok P k args).1
  | .call f args =>
      refine ⟨rfl, ?_⟩
      intro st hst
      simp only [flatten] at hst
      rcases List.mem_append.mp hst with hpre | htail
      · exact (flattenArgs_ok P k args).2 st hpre
      · rcases List.mem_singleton.mp htail with rfl
        simp only [preludeOK, isFlatRhs]
        exact (flattenArgs_ok P k args).1

/-- The result atoms of `flattenArgs` are all atoms, and its prelude is
well-formed. -/
theorem flattenArgs_ok (P : String) (k : Nat) (args : List (Expr Op)) :
    atomicArgs (flattenArgs P k args).2.2 = true ∧
      ∀ s ∈ (flattenArgs P k args).2.1, preludeOK s = true := by
  match args with
  | [] => exact ⟨rfl, by intro s hs; simp [flattenArgs] at hs⟩
  | e :: rest =>
      have hrest := flattenArgs_ok P k rest
      have hhead := flatten_ok P (flattenArgs P k rest).1 e
      refine ⟨?_, ?_⟩
      · simp only [flattenArgs, atomicArgs, Bool.and_eq_true]
        exact ⟨hhead.1, hrest.1⟩
      · intro st hst
        simp only [flattenArgs] at hst
        rcases List.mem_append.mp hst with hpre | hpre
        · exact hrest.2 st hpre
        · exact hhead.2 st hpre
end

/-- A well-formed prelude statement is a single-variable `let` with an rhs. -/
theorem preludeOK_shape : ∀ {s : Stmt Op}, preludeOK s = true →
    ∃ t rhs, s = .letDecl [t] (some rhs)
  | .letDecl [t] (some rhs), _ => ⟨t, rhs, rfl⟩
  | .letDecl [] _, h => by simp [preludeOK] at h
  | .letDecl (_ :: _ :: _) _, h => by simp [preludeOK] at h
  | .letDecl [_] none, h => by simp [preludeOK] at h
  | .block _, h => by simp [preludeOK] at h
  | .funDef _ _ _ _, h => by simp [preludeOK] at h
  | .assign _ _, h => by simp [preludeOK] at h
  | .cond _ _, h => by simp [preludeOK] at h
  | .switch _ _ _, h => by simp [preludeOK] at h
  | .forLoop _ _ _ _, h => by simp [preludeOK] at h
  | .exprStmt _, h => by simp [preludeOK] at h
  | .break, h => by simp [preludeOK] at h
  | .continue, h => by simp [preludeOK] at h
  | .leave, h => by simp [preludeOK] at h

/-! ### Head-expression flattening

For a statement position that already allows one operator level (`let`/`assign`
right-hand sides, `exprStmt`, and `if`/`switch` conditions), we flatten only the
*arguments* — keeping a single flat `op(atoms)`/`call(atoms)` — and prepend the
prelude. -/
def flattenTop (P : String) (k : Nat) : Expr Op → Nat × List (Stmt Op) × Expr Op
  | .builtin op args =>
      let (k1, pre, atoms) := flattenArgs P k args
      (k1, pre, .builtin op atoms)
  | .call f args =>
      let (k1, pre, atoms) := flattenArgs P k args
      (k1, pre, .call f atoms)
  | e => (k, [], e)

theorem flattenTop_ok (P : String) (k : Nat) (e : Expr Op) :
    isFlatRhs (flattenTop P k e).2.2 = true ∧
      ∀ s ∈ (flattenTop P k e).2.1, preludeOK s = true := by
  match e with
  | .var x => exact ⟨rfl, by intro s hs; simp [flattenTop] at hs⟩
  | .lit l => exact ⟨rfl, by intro s hs; simp [flattenTop] at hs⟩
  | .builtin op args =>
      exact ⟨(flattenArgs_ok P k args).1, fun s hs => (flattenArgs_ok P k args).2 s hs⟩
  | .call f args =>
      exact ⟨(flattenArgs_ok P k args).1, fun s hs => (flattenArgs_ok P k args).2 s hs⟩

/-! ### The ANF form of statements and blocks

A statement is in ANF when its operand expressions are flat (`isFlatRhs`) and its
nested blocks are ANF. -/
mutual
def isANFStmt : Stmt Op → Bool
  | .block body => isANFStmts body
  | .funDef _ _ _ _ => true  -- function bodies left un-normalized (see ANF scope note)
  | .letDecl _ rhs => rhs.all isFlatRhs
  | .assign _ rhs | .exprStmt rhs => isFlatRhs rhs
  | .cond c body => isFlatRhs c && isANFStmts body
  | .switch c cases dflt => isFlatRhs c && isANFCases cases && isANFDflt dflt
  | .forLoop init _ post body =>  -- loop condition left un-normalized (re-evaluated per iteration)
      isANFStmts init && isANFStmts post && isANFStmts body
  | .break | .continue | .leave => true

def isANFStmts : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => isANFStmt s && isANFStmts rest

def isANFCases : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, b) :: rest => isANFStmts b && isANFCases rest

def isANFDflt : Option (List (Stmt Op)) → Bool
  | none => true
  | some b => isANFStmts b
end

/-! ### The statement/block transform

Each statement's operand expressions are flattened (prelude prepended); nested
blocks recurse. The `for` **condition** is re-evaluated every iteration, so it
cannot simply be hoisted before the loop: instead the loop condition becomes the
literal `1` and the real test moves to the top of the body as
`if iszero(cAtom) { break }`, with the condition's prelude inside the body where
it re-runs. A shared temporary index `k` is threaded so names stay distinct. -/
mutual
def anfStmt (P : String) (k : Nat) : Stmt Op → Nat × List (Stmt Op)
  | .block body => let (k1, body') := anfStmts P k body; (k1, [.block body'])
  | .funDef n ps rs body => (k, [.funDef n ps rs body])  -- identity: bodies left un-normalized
  | .letDecl vars none => (k, [.letDecl vars none])
  | .letDecl vars (some e) => let (k1, pre, e') := flattenTop P k e; (k1, pre ++ [.letDecl vars (some e')])
  | .assign vars e => let (k1, pre, e') := flattenTop P k e; (k1, pre ++ [.assign vars e'])
  | .exprStmt e => let (k1, pre, e') := flattenTop P k e; (k1, pre ++ [.exprStmt e'])
  | .cond c body =>
      let (k1, pre, c') := flattenTop P k c
      let (k2, body') := anfStmts P k1 body
      (k2, pre ++ [.cond c' body'])
  | .switch c cases dflt =>
      let (k1, pre, c') := flattenTop P k c
      let (k2, cases') := anfCases P k1 cases
      let (k3, dflt') := anfDflt P k2 dflt
      (k3, pre ++ [.switch c' cases' dflt'])
  | .forLoop init c post body =>
      -- condition left as-is (re-evaluated per iteration); flatten init/post/body
      let (k1, init') := anfStmts P k init
      let (k2, post') := anfStmts P k1 post
      let (k3, body') := anfStmts P k2 body
      (k3, [.forLoop init' c post' body'])
  | .break => (k, [.break])
  | .continue => (k, [.continue])
  | .leave => (k, [.leave])

def anfStmts (P : String) (k : Nat) : List (Stmt Op) → Nat × List (Stmt Op)
  | [] => (k, [])
  | s :: rest =>
      let (k1, s') := anfStmt P k s
      let (k2, rest') := anfStmts P k1 rest
      (k2, s' ++ rest')

def anfCases (P : String) (k : Nat) :
    List (Literal × List (Stmt Op)) → Nat × List (Literal × List (Stmt Op))
  | [] => (k, [])
  | (l, b) :: rest =>
      let (k1, b') := anfStmts P k b
      let (k2, rest') := anfCases P k1 rest
      (k2, (l, b') :: rest')

def anfDflt (P : String) (k : Nat) :
    Option (List (Stmt Op)) → Nat × Option (List (Stmt Op))
  | none => (k, none)
  | some b => let (k1, b') := anfStmts P k b; (k1, some b')
end

/-! ### Structural correctness: the transform produces ANF -/

theorem isANFStmts_append (a b : List (Stmt Op)) :
    isANFStmts (a ++ b) = (isANFStmts a && isANFStmts b) := by
  induction a with
  | nil => simp [isANFStmts]
  | cons s rest ih => simp only [List.cons_append, isANFStmts, ih, Bool.and_assoc]

theorem preludeOK_isANFStmt {s : Stmt Op} (h : preludeOK s = true) : isANFStmt s = true := by
  match s, h with
  | .letDecl [_] (some rhs), h => simpa [isANFStmt, preludeOK] using h

theorem isANFStmts_of_preludeOK {pre : List (Stmt Op)}
    (h : ∀ s ∈ pre, preludeOK s = true) : isANFStmts pre = true := by
  induction pre with
  | nil => rfl
  | cons s rest ih =>
      simp only [isANFStmts, Bool.and_eq_true]
      exact ⟨preludeOK_isANFStmt (h s (List.mem_cons_self ..)),
        ih (fun t ht => h t (List.mem_cons_of_mem _ ht))⟩

mutual
theorem anfStmt_ok (P : String) (k : Nat) (s : Stmt Op) :
    isANFStmts (anfStmt P k s).2 = true := by
  match s with
  | .block body =>
      have := anfStmts_ok P k body; simp [anfStmt, isANFStmts, isANFStmt, this]
  | .funDef n ps rs body => simp [anfStmt, isANFStmts, isANFStmt]
  | .letDecl vars none => simp [anfStmt, isANFStmts, isANFStmt]
  | .letDecl vars (some e) =>
      have hpre := isANFStmts_of_preludeOK (flattenTop_ok P k e).2
      have hflat := (flattenTop_ok P k e).1
      simp [anfStmt, isANFStmts_append, isANFStmts, isANFStmt, hpre, hflat]
  | .assign vars e =>
      have hpre := isANFStmts_of_preludeOK (flattenTop_ok P k e).2
      have hflat := (flattenTop_ok P k e).1
      simp [anfStmt, isANFStmts_append, isANFStmts, isANFStmt, hpre, hflat]
  | .exprStmt e =>
      have hpre := isANFStmts_of_preludeOK (flattenTop_ok P k e).2
      have hflat := (flattenTop_ok P k e).1
      simp [anfStmt, isANFStmts_append, isANFStmts, isANFStmt, hpre, hflat]
  | .cond c body =>
      have hpre := isANFStmts_of_preludeOK (flattenTop_ok P k c).2
      have hflat := (flattenTop_ok P k c).1
      have hbody := anfStmts_ok P (flattenTop P k c).1 body
      simp [anfStmt, isANFStmts_append, isANFStmts, isANFStmt, hpre, hflat, hbody]
  | .switch c cases dflt =>
      have hpre := isANFStmts_of_preludeOK (flattenTop_ok P k c).2
      have hflat := (flattenTop_ok P k c).1
      have hcases := anfCases_ok P (flattenTop P k c).1 cases
      have hdflt := anfDflt_ok P (anfCases P (flattenTop P k c).1 cases).1 dflt
      simp [anfStmt, isANFStmts_append, isANFStmts, isANFStmt, hpre, hflat, hcases, hdflt]
  | .forLoop init c post body =>
      have hinit := anfStmts_ok P k init
      have hpost := anfStmts_ok P (anfStmts P k init).1 post
      have hbody := anfStmts_ok P (anfStmts P (anfStmts P k init).1 post).1 body
      simp [anfStmt, isANFStmts, isANFStmt, hinit, hpost, hbody]
  | .break => simp [anfStmt, isANFStmts, isANFStmt]
  | .continue => simp [anfStmt, isANFStmts, isANFStmt]
  | .leave => simp [anfStmt, isANFStmts, isANFStmt]

theorem anfStmts_ok (P : String) (k : Nat) (ss : List (Stmt Op)) :
    isANFStmts (anfStmts P k ss).2 = true := by
  match ss with
  | [] => rfl
  | s :: rest =>
      have h1 := anfStmt_ok P k s
      have h2 := anfStmts_ok P (anfStmt P k s).1 rest
      simp [anfStmts, isANFStmts_append, h1, h2]

theorem anfCases_ok (P : String) (k : Nat) (cs : List (Literal × List (Stmt Op))) :
    isANFCases (anfCases P k cs).2 = true := by
  match cs with
  | [] => rfl
  | (l, b) :: rest =>
      have h1 := anfStmts_ok P k b
      have h2 := anfCases_ok P (anfStmts P k b).1 rest
      simp [anfCases, isANFCases, h1, h2]

theorem anfDflt_ok (P : String) (k : Nat) (d : Option (List (Stmt Op))) :
    isANFDflt (anfDflt P k d).2 = true := by
  match d with
  | none => rfl
  | some b => have := anfStmts_ok P k b; simp [anfDflt, isANFDflt, this]
end

/-- **The ANF normalizer** (structural form): flatten a block so every operand is
an atom. The prefix is a parameter here; the semantic-preservation step will
instantiate it with a program-fresh prefix (the `FreshenCalls` idiom) so the
introduced temporaries cannot capture or collide. -/
def anfBlock (P : String) (b : Block Op) : Block Op :=
  (anfStmts P 0 b).2

/-- **Form correctness**: the normalizer's output is in ANF, for any prefix. -/
theorem anfBlock_isANF (P : String) (b : Block Op) : isANFStmts (anfBlock P b) = true :=
  anfStmts_ok P 0 b

end YulEvmCompiler.Optimizer.ANF
