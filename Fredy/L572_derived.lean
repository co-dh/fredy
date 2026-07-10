/-
  LeetCode 572 — Subtree of Another Tree — DERIVED as TWO tree catamorphisms.

  `Fredy/L572.lean` WRITES `sameFn`/`subFn` by hand and verifies them by structural induction. HERE
  both folds EMERGE from `TB.treeFold_unique` (`Fredy/A6_GenFold.lean`, the general-carrier tree
  fold-uniqueness law used by `L100_derived`/`L543_derived`), on TWO different carriers:

  1. **`sameFn` — a FUNCTION carrier `Tree Int → Bool`** (`L100_derived`'s "curry the two-input
     recursion" trick, re-derived here for `L572.sameFn`, which is a fresh `def` in a fresh
     namespace even though its equations are identical to `L100.sameFn`'s). Folding the first tree
     produces a RESIDUAL decision procedure `sameFn t1 : Tree Int → Bool` still awaiting the second
     tree; base `g = sameFn nil` and step `step` are read off `sameFn`'s defining equations, curried
     in the second argument.

  2. **`subFn` — a PARAMORPHISM on the pair carrier `Bool × Tree Int`.** `subFn`'s `node` case calls
     `sameFn (node l a r) t` — the SAME-TREE check at the CURRENT node against the full node
     `Tree.node l a r`, not just against the children's `subFn` verdicts. A plain catamorphism only
     hands `step` the recursive RESULTS (`subFn l t`, `subFn r t` — plain `Bool`s), which is not
     enough to reconstruct `Tree.node l a r` and re-run `sameFn` on it. The classical fix (Meertens'
     paramorphism-as-catamorphism) is to carry the ORIGINAL subtree alongside the answer: carrier
     `C := Bool × Tree Int`, `q s := (subFn s t, s)`. The step then reads the retained subtrees off
     the `.2` projections of its two carrier arguments to rebuild the node, and calls `sameFn` on it —
     `stepSub (bl, l) a (br, r) := (sameFn (node l a r) t || bl || br, node l a r)`. Since `t` is
     held FIXED throughout one call `subFn s t`, this is a FAMILY of catamorphisms indexed by `t`
     (`gSub t`/`stepSub t`/`q t`), one per second tree, each an ordinary application of
     `TB.treeFold_unique` over the first tree alone.

  Correctness is REUSED, not re-proved: `sametree_derived_correct` reads off `L572.same_correct`,
  `subtree_derived_correct` reads off `L572.solve_correct` (both DECISION-shape `iff`s, S5-style).

  Complexity: `sameFn` costs O(min(|t1|,|t2|)) (lockstep, short-circuits on mismatch), and `subFn`
  calls it at EVERY node of `s`, so `subFn s t` costs O(|s| · |t|) — the inherent cost of a naive
  subtree search (no hashing/serialization shortcut here); this is what the carrier records, not an
  artifact of the derivation.

  Mathlib-free; axioms of the headlines ⊆ {propext, Quot.sound}. We route only through
  `TB.treeFold_unique`, never `cataR_eq_relCata` (which pulls `Classical.choice`).
-/
import Fredy.A6_GenFold
import Fredy.L572

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC572D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC572

/-! ## Part 1 — `sameFn` EMERGES on the function carrier `Tree Int → Bool`

  Carrier `C := Tree Int → Bool` — the RESIDUAL decision procedure that, having folded the first
  tree, still awaits the second (`L100_derived`'s trick, re-derived here for `LC572.sameFn`). -/

/-- The base of the emergent algebra: `g = sameFn nil` — accepts only the empty second tree. -/
def g : Tree Int → Bool := fun t =>
  match t with
  | Tree.nil        => true
  | Tree.node _ _ _ => false

/-- The step of the emergent algebra: from the children's residuals `fl = sameFn l`, `fr = sameFn r`
    and the root label `a`, the parent's residual answers `node l' a' r'` by
    `decide (a = a') && fl l' && fr r'` and rejects `nil`. Read off `sameFn`'s node clause, curried
    in the awaited second tree. -/
def step : (Tree Int → Bool) → Int → (Tree Int → Bool) → (Tree Int → Bool) :=
  fun fl a fr => fun t =>
    match t with
    | Tree.nil           => false
    | Tree.node l' a' r' => decide (a = a') && fl l' && fr r'

/-- The base condition: `sameFn nil = g`, by extensionality on the awaited second tree. -/
theorem hnil : sameFn Tree.nil = g := by
  funext t; cases t <;> rfl

/-- The step condition: `sameFn (node l a r) = step (sameFn l) a (sameFn r)` — the problem's
    first-order lockstep recurrence, proved not defined. -/
theorem hnode (l : Tree Int) (a : Int) (r : Tree Int) :
    sameFn (Tree.node l a r) = step (sameFn l) a (sameFn r) := by
  funext t; cases t <;> rfl

/-- **The residual same-tree decision procedure EMERGES.** `graph sameFn` equals the catamorphism of
    `treeScalarAlg g step` on the FUNCTION carrier `Tree Int → Bool`, PRODUCED by `TB.treeFold_unique`
    from the forced base `g` and step `step`. -/
theorem sametree_emerges :
    (graph sameFn : dTree Int ⟶ ⟨Tree Int → Bool⟩) = cataR (treeScalarAlg g step) :=
  TB.treeFold_unique g step sameFn hnil hnode

/-- **Correctness of the emergent same-tree fold**, reusing `LC572.same_correct` (no re-proof):
    for the residual `f` the emergent fold relates `t1` to, `f` decides `SameP t1` against every
    second tree. -/
theorem sametree_derived_correct :
    ((graph sameFn : dTree Int ⟶ ⟨Tree Int → Bool⟩) = cataR (treeScalarAlg g step)) ∧
    (∀ (t1 : Tree Int) (f : Tree Int → Bool),
        cataTreeFold (treeScalarAlg g step) t1 f → ∀ t2 : Tree Int, f t2 = true ↔ SameP t1 t2) := by
  refine ⟨sametree_emerges, ?_⟩
  intro t1 f hf t2
  have hgr : (graph sameFn : dTree Int ⟶ ⟨Tree Int → Bool⟩) t1 f := by
    rw [sametree_emerges]; exact hf
  have hfeq : f = sameFn t1 := hgr
  subst hfeq
  exact LC572.same_correct t1 t2

/-! ## Part 2 — `subFn` EMERGES as a PARAMORPHISM on the pair carrier `Bool × Tree Int`

  For each FIXED second tree `t2`, `q t2 : Tree Int → Bool × Tree Int` folds the first tree `s` to
  `(subFn s t2, s)` — the answer paired with the ORIGINAL subtree, so `step` can reconstruct
  `node l a r` from the retained `.2`-components and re-run `sameFn` on it (the paramorphism move: a
  catamorphism into `Answer × Data` simulates access to the original substructure). -/

/-- The base of the `t2`-indexed algebra: `subFn nil t2 = sameFn nil t2`, paired with the (empty)
    original subtree. -/
def gSub (t2 : Tree Int) : Bool × Tree Int := (sameFn Tree.nil t2, Tree.nil)

/-- The step of the `t2`-indexed algebra: given the children's `(answer, subtree)` pairs
    `(bl, l) = q t2 l`, `(br, r) = q t2 r` and label `a`, the parent's pair is
    `(sameFn (node l a r) t2 || bl || br, node l a r)` — the retained `.2`s rebuild the node so the
    SAME-TREE check can run at THIS node, exactly `subFn`'s node clause. -/
def stepSub (t2 : Tree Int) :
    Bool × Tree Int → Int → Bool × Tree Int → Bool × Tree Int :=
  fun pl a pr => (sameFn (Tree.node pl.2 a pr.2) t2 || pl.1 || pr.1, Tree.node pl.2 a pr.2)

/-- The paramorphism ansatz, for fixed `t2`: pair `subFn s t2` with the original subtree `s`. -/
def q (t2 s : Tree Int) : Bool × Tree Int := (subFn s t2, s)

/-- The base condition (a COMPUTATION, `rfl`): `q t2 nil = gSub t2`. -/
theorem hnilSub (t2 : Tree Int) : q t2 Tree.nil = gSub t2 := rfl

/-- The step condition (a COMPUTATION, `rfl`): `q t2 (node l a r) = stepSub t2 (q t2 l) a (q t2 r)` —
    the problem's first-order recurrence, proved not defined. -/
theorem hnodeSub (t2 : Tree Int) (l : Tree Int) (a : Int) (r : Tree Int) :
    q t2 (Tree.node l a r) = stepSub t2 (q t2 l) a (q t2 r) := rfl

/-- **The subtree-search paramorphism EMERGES**, for every fixed second tree `t2`: `graph (q t2)`
    equals the catamorphism of `treeScalarAlg (gSub t2) (stepSub t2)` on the pair carrier
    `Bool × Tree Int`, PRODUCED by `TB.treeFold_unique`. The `(answer, subtree)` pairing was never
    written by hand as a fold here. -/
theorem subtree_emerges (t2 : Tree Int) :
    (graph (q t2) : dTree Int ⟶ ⟨Bool × Tree Int⟩) = cataR (treeScalarAlg (gSub t2) (stepSub t2)) :=
  TB.treeFold_unique (gSub t2) (stepSub t2) (q t2) (hnilSub t2) (hnodeSub t2)

/-- **Correctness of the emergent subtree paramorphism**, reusing `LC572.solve_correct` (no
    re-proof): for ANY pair `v` the emergent fold relates `s` to (at fixed `t2`), `v`'s first slot
    decides `IsSubtree s t2`. -/
theorem subtree_derived_correct (t2 s : Tree Int) (v : Bool × Tree Int)
    (hv : cataTreeFold (treeScalarAlg (gSub t2) (stepSub t2)) s v) :
    v.1 = true ↔ IsSubtree s t2 := by
  have hgr : (graph (q t2) : dTree Int ⟶ ⟨Bool × Tree Int⟩) s v := by
    rw [subtree_emerges t2]; exact hv
  have hveq : v = q t2 s := hgr
  subst hveq
  show subFn s t2 = true ↔ IsSubtree s t2
  exact LC572.solve_correct s t2

/-! ## Connecting the emergent paramorphism back to the two-input `solve` -/

/-- The derived solver: read off the FIRST slot of the emergent paramorphism `q p.2 p.1` (fold the
    first tree `p.1` against the fixed second tree `p.2`). Definitionally `L572.solve`. -/
def derivedSolve : dTreePair ⟶ dBool :=
  graph (fun p : Tree Int × Tree Int => (q p.2 p.1).1)

/-- The derived solver IS `L572.solve` — `(q t2 s).1 = subFn s t2`, definitionally. -/
theorem derivedSolve_eq_solve : derivedSolve = LC572.solve := rfl

/-! ## Running / cross-checking the emergent folds against `Fredy/L572.lean`

  The relational catamorphisms have carriers `Tree Int → Bool` / `Bool × Tree Int` that are not, in
  general, `decide`-computable as RELATIONS, so we `decide` the extensionally-equal computable
  witnesses `sameFn`/`q` (equal by `sametree_emerges`/`subtree_emerges`) and separately PROVE the
  folds relate a tree to its witness. -/

example : sameFn (Tree.node (leaf 4) 5 (leaf 6)) (Tree.node (leaf 4) 5 (leaf 6)) = true := by decide
example : (q (Tree.node (leaf 4) 5 (leaf 6))
    (Tree.node (leaf 1) 2 (Tree.node (leaf 4) 5 (leaf 6)))).1 = true := by decide
example : (q (Tree.node (leaf 4) 5 (leaf 7))
    (Tree.node (leaf 1) 2 (Tree.node (leaf 4) 5 (leaf 6)))).1 = false := by decide
example : (q (Tree.nil : Tree Int) Tree.nil).1 = true := by decide

/-- The emergent function-carrier fold genuinely relates `node (leaf 4) 5 (leaf 6)` to its RESIDUAL
    decision procedure `sameFn (node (leaf 4) 5 (leaf 6))` (no `decide` on the function carrier). -/
example : cataTreeFold (treeScalarAlg g step)
    (Tree.node (leaf 4) 5 (leaf 6)) (sameFn (Tree.node (leaf 4) 5 (leaf 6))) := by
  have h : (graph sameFn : dTree Int ⟶ ⟨Tree Int → Bool⟩)
      (Tree.node (leaf 4) 5 (leaf 6)) (sameFn (Tree.node (leaf 4) 5 (leaf 6))) := rfl
  rw [sametree_emerges] at h
  exact h

/-- The emergent paramorphism genuinely relates `s = node(leaf 1, 2, node(leaf 4, 5, leaf 6))` (at
    fixed `t2 = node(leaf 4, 5, leaf 6)`) to `q t2 s` (whose first slot is `true`). -/
example : cataTreeFold (treeScalarAlg (gSub (Tree.node (leaf 4) 5 (leaf 6)))
    (stepSub (Tree.node (leaf 4) 5 (leaf 6))))
    (Tree.node (leaf 1) 2 (Tree.node (leaf 4) 5 (leaf 6)))
    (q (Tree.node (leaf 4) 5 (leaf 6)) (Tree.node (leaf 1) 2 (Tree.node (leaf 4) 5 (leaf 6)))) := by
  have h : (graph (q (Tree.node (leaf 4) 5 (leaf 6))) : dTree Int ⟶ ⟨Bool × Tree Int⟩)
      (Tree.node (leaf 1) 2 (Tree.node (leaf 4) 5 (leaf 6)))
      (q (Tree.node (leaf 4) 5 (leaf 6)) (Tree.node (leaf 1) 2 (Tree.node (leaf 4) 5 (leaf 6)))) :=
    rfl
  rw [subtree_emerges (Tree.node (leaf 4) 5 (leaf 6))] at h
  exact h

end Freyd.Alg.RelSet.LC572D
