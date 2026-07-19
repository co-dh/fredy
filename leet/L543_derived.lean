/-
  LeetCode 543 — Diameter of Binary Tree — DERIVED from the TREE TUPLING LAW.

  `leet/L543.lean` WRITES the pair-carrying fold `foldFn = (height, diam)` by hand and then verifies
  it against the relational spec `pathEdges` (`solveFn = max (≤) · Λ pathEdges`).  HERE the fold
  EMERGES.  The starting point is the NAIVE specification, which at every node RECOMPUTES both
  subtree heights from scratch:

    * `heightOf`  — the structural height (node-counted depth), recomputed per node;
    * `diamOf`    — the diameter, `0` at `nil` and, at `node l a r`, the best of the two children's
      diameters and the through-root path `heightOf l + heightOf r`, with the heights read via
      `heightOf` (a FRESH recursion at each node — the redundant O(n²) form).

  The tupling ansatz `p t = (heightOf t, diamOf t)` carries both.  Its base and step are FORCED (not
  guessed) by `hnil`/`hnode`, the problem's own recurrence proved as `rfl`.  Applying the tree tupling
  law `treeTupling gDiam stepDiam p hnil hnode` PRODUCES the single-pass fold
  `cataR (treePairAlg gDiam stepDiam)` — the `(height, diam)` fold `L543` wrote by hand emerges, with
  `stepDiam` DEFINITIONALLY the node step of `L543.foldFn` (`stepDiam_eq_foldFn`, `rfl`).  The naive
  `diamOf` equals `L543.solveFn` (`diamOf_eq_solveFn`), so reading off the SECOND component transports
  `L543.solve_correct` — `pathEdges t (v.2) ∧ ∀ k, pathEdges t k → k ≤ v.2` — onto the emergent fold.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.
-/
import AOP.A6_9_TreeTupling
import leet.L543
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LD543

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC543

/-! ## The naive spec: structural `heightOf` and `diamOf` (both recompute heights) -/

/-- `heightOf t` — the node-counted height (`L543`'s `heightFn` value, but as a STRUCTURAL recursion
    on the tree rather than a projection of the fold; proved `= heightFn` below). -/
def heightOf : Tree Int → Nat
  | Tree.nil => 0
  | Tree.node l _ r => 1 + imax (heightOf l) (heightOf r)

/-- `diamOf t` — the diameter, in NAIVE form: it RECOMPUTES `heightOf` of both subtrees at every node
    (the O(n²) computation the emergent fold will linearize).  Value-level mirror of `L543`'s
    `solveFn`; the bridge `diamOf_eq_solveFn` proves `diamOf t = solveFn t`. -/
def diamOf : Tree Int → Nat
  | Tree.nil => 0
  | Tree.node l _ r => imax (imax (diamOf l) (diamOf r)) (heightOf l + heightOf r)

/-- The structural height IS the fold's height, by induction. -/
theorem heightOf_eq_heightFn : ∀ t : Tree Int, heightOf t = heightFn t := by
  intro t
  induction t with
  | nil => rfl
  | node l a r ihl ihr =>
    show 1 + imax (heightOf l) (heightOf r) = 1 + imax (heightFn l) (heightFn r)
    rw [ihl, ihr]

/-- The naive diameter IS the fold's answer, by induction (using `heightOf = heightFn` for the
    through-root term). -/
theorem diamOf_eq_solveFn : ∀ t : Tree Int, diamOf t = solveFn t := by
  intro t
  induction t with
  | nil => rfl
  | node l a r ihl ihr =>
    show imax (imax (diamOf l) (diamOf r)) (heightOf l + heightOf r)
        = imax (imax (solveFn l) (solveFn r)) (heightFn l + heightFn r)
    rw [ihl, ihr, heightOf_eq_heightFn l, heightOf_eq_heightFn r]

/-! ## The tupling ANSATZ and its FORCED base/step -/

/-- Carry the pair `(height, diameter)` — the tupling ansatz. -/
def p (t : Tree Int) : Nat × Nat := (heightOf t, diamOf t)

/-- The base of the emergent algebra: `p nil = (0, 0)`, forced by the recurrence. -/
def gDiam : Nat × Nat := (0, 0)

/-- The step of the emergent algebra: carrying `(hl, dl)` and `(hr, dr)`, the parent pair is
    `(1 + imax hl hr, imax (imax dl dr) (hl + hr))` — read off the recurrence.  This is
    DEFINITIONALLY the node step of `L543.foldFn` (see `stepDiam_eq_foldFn`). -/
def stepDiam : Nat × Nat → Int → Nat × Nat → Nat × Nat :=
  fun pl _ pr => (1 + imax pl.1 pr.1, imax (imax pl.2 pr.2) (pl.1 + pr.1))

/-- The step condition (a COMPUTATION, `rfl`): `p nil = gDiam`. -/
theorem p_nil : p Tree.nil = gDiam := rfl

/-- The step condition (a COMPUTATION, `rfl`): `p (node l a r) = stepDiam (p l) a (p r)` — the
    problem's first-order lockstep recurrence, proved not defined. -/
theorem p_node (l r : Tree Int) (a : Int) : p (Tree.node l a r) = stepDiam (p l) a (p r) := rfl

/-- The emergent algebra's step IS `L543.foldFn`'s node step, DEFINITIONALLY (`rfl`) — the endpoint
    of the derivation coincides with the hand-written program's fold. -/
theorem stepDiam_eq_foldFn (l r : Tree Int) (a : Int) :
    LC543.foldFn (Tree.node l a r) = stepDiam (LC543.foldFn l) a (LC543.foldFn r) := rfl

/-! ## The fold EMERGES via the tree tupling law -/

/-- **The `(height, diam)` fold EMERGES.**  `graph p` equals the catamorphism of the emergent algebra
    `treePairAlg gDiam stepDiam = [ nil ↦ (0,0), (pl,a,pr) ↦ stepDiam pl a pr ]`, PRODUCED by the tree
    tupling law from the forced base `gDiam` and step `stepDiam`.  The pair-carrying single-pass fold
    was never written by hand here. -/
theorem diameter_emerges :
    (graph p : dTree Int ⟶ ⟨Nat × Nat⟩) = cataR (treePairAlg gDiam stepDiam) :=
  treeTupling gDiam stepDiam p p_nil (fun l a r => p_node l r a)

/-- **Correctness of the derived program** (the derived analogue of `L543.solve_correct`,
    `solve = max (≤) · Λ pathEdges`): for ANY pair `v` the EMERGENT fold relates `t` to, `v.2` is an
    achievable `pathEdges` value AND dominates every achievable one — for EVERY tree.  The emergence
    (`diameter_emerges`) pins `v = p t`, whose second slot is `diamOf t = solveFn t`
    (`diamOf_eq_solveFn`); `L543.solve_correct` then supplies the extremum property. -/
theorem diameter_derived_correct (t : Tree Int) (v : Nat × Nat)
    (hv : cataTreeFold (treePairAlg gDiam stepDiam) t v) :
    pathEdges t v.2 ∧ ∀ k, pathEdges t k → k ≤ v.2 := by
  have hgr : (graph p : dTree Int ⟶ ⟨Nat × Nat⟩) t v := by rw [diameter_emerges]; exact hv
  have hveq : v = p t := hgr
  subst hveq
  show pathEdges t (diamOf t) ∧ ∀ k, pathEdges t k → k ≤ diamOf t
  rw [diamOf_eq_solveFn t]
  exact LC543.solve_correct t

/-! ## Running / cross-checking the emergent fold against `leet/L543.lean`

  As in `L104_derived`/`L110_derived`, the relational catamorphism is not `decide`-computable, so we
  `decide` the extensionally-equal computable witness `p` (equal by `diameter_emerges`), cross-check
  its second slot against `L543.solveFn` on `L543`'s own example trees, and separately PROVE the fold
  relates each tree to `p t`. -/

/-- The derived answer agrees with `L543.solveFn` on every example tree of `leet/L543.lean`. -/
example : (p (Tree.node (Tree.node (leaf 4) 2 (leaf 5)) 1 (leaf 3))).2
    = LC543.solveFn (Tree.node (Tree.node (leaf 4) 2 (leaf 5)) 1 (leaf 3)) := by decide
example : (p (leaf 1)).2 = LC543.solveFn (leaf 1) := by decide
example : (p (Tree.nil : Tree Int)).2 = LC543.solveFn (Tree.nil : Tree Int) := by decide
example : (p (Tree.node (leaf 1) 2 Tree.nil)).2 = LC543.solveFn (Tree.node (leaf 1) 2 Tree.nil) := by
  decide

-- The derived answers, matching `L543`'s stated results.
example : (p (Tree.node (Tree.node (leaf 4) 2 (leaf 5)) 1 (leaf 3))).2 = 3 := by decide
example : (p (leaf 1)).2 = 0 := by decide
example : (p (Tree.nil : Tree Int)).2 = 0 := by decide
example : (p (Tree.node (leaf 1) 2 Tree.nil)).2 = 1 := by decide

/-- The emergent fold genuinely relates `node (node (leaf 4) 2 (leaf 5)) 1 (leaf 3)` to `p` of it
    (whose `.2` is `3`, the diameter). -/
example : cataTreeFold (treePairAlg gDiam stepDiam)
    (Tree.node (Tree.node (leaf 4) 2 (leaf 5)) 1 (leaf 3))
    (p (Tree.node (Tree.node (leaf 4) 2 (leaf 5)) 1 (leaf 3))) := by
  have h : (graph p : dTree Int ⟶ ⟨Nat × Nat⟩)
      (Tree.node (Tree.node (leaf 4) 2 (leaf 5)) 1 (leaf 3))
      (p (Tree.node (Tree.node (leaf 4) 2 (leaf 5)) 1 (leaf 3))) := rfl
  rw [diameter_emerges] at h
  exact h

end Freyd.Alg.RelSet.LD543
