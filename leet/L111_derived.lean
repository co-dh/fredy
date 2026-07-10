/-
  LeetCode 111 — Minimum Depth of Binary Tree — DERIVED as a single-value tree catamorphism.

  `leet/L111.lean` WRITES the three-way min-depth fold `minDepthFn : Tree Int → Nat` by hand
  (matching on which children are `nil`) and verifies it against the spec `IsRLDepth`.  HERE we do
  the reshaping the AOP way: the SAME first-order recursion is read off as a scalar tree algebra
  `[g, step]` over the bare carrier `C := Nat`, and the general-carrier fold-uniqueness law
  `TB.treeFold_unique` (`AOP/A6_GenFold.lean`) PRODUCES the catamorphism
  `cataR (treeScalarAlg g step)` and identifies it with `graph minDepthFn` (`mindepth_emerges`).

  The one-child nuance — a node with exactly ONE child is NOT a leaf, so its depth is `1 +` the
  present child's depth, never `1 + min(child, 0)` — is DETECTABLE inside a `Nat`-carrier fold:
  `minDepthFn nil = 0` and every real node has depth `≥ 1`, so a child result `= 0` means that
  child is `nil`.  The step therefore branches on `dl = 0` / `dr = 0` (the `= 0` nil-detector) and
  reproduces `minDepthFn`'s three real node clauses exactly.  The base `g := minDepthFn nil` and the
  step are then FORCED: `minDepthFn nil = g` (`hnil`) and
  `minDepthFn (node l a r) = step (minDepthFn l) a (minDepthFn r)` (`hnode`, by matching each
  concrete child shape and discharging the `= 0` guards with `minDepthFn_node_pos`).

  `derivedSolve := cataR (treeScalarAlg g step)` is `L111.solve` (`= graph minDepthFn`), and
  `L111.minDepth_correct` (the existing `IsRLDepth` correctness, NOT re-proved) transports onto the
  emergent fold (`mindepth_derived_correct`): the value the catamorphism relates a non-empty tree to
  is an achievable root-to-leaf depth and is `≤`-least among them.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataTreeFold` /
  `treeFold_unique` only, never the `cataR_eq_relCata` bridge (which pulls `Classical.choice`).
-/
import AOP.A6_GenFold
import leet.L111

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC111D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC111

/-! ## The base and step of the emergent scalar algebra, carrier `C := Nat`

  Read off `L111.minDepthFn`'s node clause.  A child result `= 0` is precisely a `nil` child
  (`minDepthFn_node_pos`: any real node folds to `≥ 1`), so the step detects the one-child case with
  the `= 0` test and never takes `min(_, 0)` at a one-child node. -/

/-- The base of the emergent algebra: `g = minDepthFn nil = 0`. -/
def g : Nat := minDepthFn Tree.nil

/-- The step: from the children's folded depths `dl, dr` and the label `a`, reproduce
    `minDepthFn (node l a r)` — a leaf (`dl = dr = 0`) `↦ 1`; a one-child node (exactly one of
    `dl, dr` is `0`) `↦ 1 +` the present child's depth; a two-child node `↦ 1 + imin dl dr`. -/
def step (dl : Nat) (a : Int) (dr : Nat) : Nat :=
  if dl = 0 then (if dr = 0 then 1 else 1 + dr)
  else (if dr = 0 then 1 + dl else 1 + imin dl dr)

/-! ## A real node folds to a positive depth (the `= 0` nil-detector is sound) -/

/-- Every non-empty tree has `minDepthFn ≥ 1`; equivalently `minDepthFn t = 0 ↔ t = nil`.  This is
    what makes the `= 0` child-test inside `step` detect a `nil` child.  Proved by matching the four
    concrete node shapes of `minDepthFn` (as in `L111.minDepthFn_le_of_isRL`). -/
theorem minDepthFn_node_pos : ∀ (l : Tree Int) (a : Int) (r : Tree Int),
    0 < minDepthFn (Tree.node l a r)
  | Tree.nil, a, Tree.nil => by show (0 : Nat) < 1; omega
  | Tree.nil, a, Tree.node rl ra rr => by
      show 0 < 1 + minDepthFn (Tree.node rl ra rr); omega
  | Tree.node ll la lr, a, Tree.nil => by
      show 0 < 1 + minDepthFn (Tree.node ll la lr); omega
  | Tree.node ll la lr, a, Tree.node rl ra rr => by
      show 0 < 1 + imin (minDepthFn (Tree.node ll la lr)) (minDepthFn (Tree.node rl ra rr)); omega

/-! ## The FORCED first-order recursion of `minDepthFn` -/

/-- The base condition: `minDepthFn nil = g`, definitionally. -/
theorem hnil : minDepthFn Tree.nil = g := rfl

/-- The step condition: `minDepthFn (node l a r) = step (minDepthFn l) a (minDepthFn r)`.  Matching
    the four concrete child shapes: for a present (`node`) child the `= 0` guard is discharged `false`
    by `minDepthFn_node_pos`, selecting the same clause `minDepthFn` uses. -/
theorem hnode : ∀ (l : Tree Int) (a : Int) (r : Tree Int),
    minDepthFn (Tree.node l a r) = step (minDepthFn l) a (minDepthFn r)
  | Tree.nil, a, Tree.nil => by
      -- LHS = 1; RHS = step 0 a 0 → 1.  `hnil0` tells omega both children fold to 0.
      have hnil0 : minDepthFn Tree.nil = 0 := rfl
      show (1 : Nat) = step (minDepthFn Tree.nil) a (minDepthFn Tree.nil)
      unfold step; split <;> (first | omega | (split <;> omega))
  | Tree.nil, a, Tree.node rl ra rr => by
      -- LHS = 1 + dr; RHS = step 0 a dr with dr > 0 → 1 + dr
      have hnil0 : minDepthFn Tree.nil = 0 := rfl
      have hpos := minDepthFn_node_pos rl ra rr
      show 1 + minDepthFn (Tree.node rl ra rr)
          = step (minDepthFn Tree.nil) a (minDepthFn (Tree.node rl ra rr))
      unfold step; split <;> (first | omega | (split <;> omega))
  | Tree.node ll la lr, a, Tree.nil => by
      -- LHS = 1 + dl; RHS = step dl a 0 with dl > 0 → 1 + dl
      have hnil0 : minDepthFn Tree.nil = 0 := rfl
      have hpos := minDepthFn_node_pos ll la lr
      show 1 + minDepthFn (Tree.node ll la lr)
          = step (minDepthFn (Tree.node ll la lr)) a (minDepthFn Tree.nil)
      unfold step; split <;> (first | omega | (split <;> omega))
  | Tree.node ll la lr, a, Tree.node rl ra rr => by
      -- LHS = 1 + imin dl dr; RHS = step dl a dr with dl, dr > 0 → 1 + imin dl dr
      have hl := minDepthFn_node_pos ll la lr
      have hr := minDepthFn_node_pos rl ra rr
      show 1 + imin (minDepthFn (Tree.node ll la lr)) (minDepthFn (Tree.node rl ra rr))
          = step (minDepthFn (Tree.node ll la lr)) a (minDepthFn (Tree.node rl ra rr))
      unfold step; split <;> (first | omega | (split <;> omega))

/-! ## The single-value catamorphism EMERGES via the general-carrier law -/

/-- **The min-depth fold EMERGES.**  `graph minDepthFn` equals the catamorphism of the scalar tree
    algebra `treeScalarAlg g step = [ nil ↦ g, (dl,a,dr) ↦ step dl a dr ]` on the carrier `Nat`,
    PRODUCED by `TB.treeFold_unique` from the forced base `g` and step `step`.  The three-way node
    recurrence — including the one-child nuance — is not written; it emerges as the unique fold. -/
theorem mindepth_emerges :
    (graph minDepthFn : dTree Int ⟶ ⟨Nat⟩) = cataR (treeScalarAlg g step) :=
  TB.treeFold_unique g step minDepthFn hnil hnode

/-! ## Connecting the emergent fold back to `L111.solve` -/

/-- The derived solver: the emergent catamorphism of the scalar min-depth algebra. -/
def derivedSolve : dTree Int ⟶ (⟨Nat⟩ : RelSet.{0}) := cataR (treeScalarAlg g step)

/-- The derived solver IS `L111.solve` (`= graph minDepthFn`): the hand-written program is exactly
    the emergent catamorphism. -/
theorem derivedSolve_eq_solve : derivedSolve = LC111.solve := mindepth_emerges.symm

/-! ## Correctness of the derived program, transported from `L111.minDepth_correct` -/

/-- **The Min-Depth program is the single-value catamorphism, and it is correct.**  The headline
    bundles:

    * `mindepth_emerges` — `graph minDepthFn = cataR (treeScalarAlg g step)`: the hand-written
      program IS the emergent catamorphism over the carrier `Nat`; and
    * the transported correctness — for any non-empty tree `t`, the value `n` the emergent fold
      relates `t` to (necessarily `minDepthFn t`, by emergence) is an achievable root-to-leaf depth
      and is `≤`-least among all achievable root-to-leaf depths.  `L111.minDepth_correct` (the
      existing correctness, NOT re-proved here) supplies both halves. -/
theorem mindepth_derived_correct :
    ((graph minDepthFn : dTree Int ⟶ ⟨Nat⟩) = cataR (treeScalarAlg g step)) ∧
    (∀ (t : Tree Int) (n : Nat), t ≠ Tree.nil →
        cataTreeFold (treeScalarAlg g step) t n →
        IsRLDepth t n ∧ ∀ m, IsRLDepth t m → n ≤ m) := by
  refine ⟨mindepth_emerges, ?_⟩
  intro t n ht hf
  have hgr : (graph minDepthFn : dTree Int ⟶ ⟨Nat⟩) t n := by
    rw [mindepth_emerges]; exact hf
  have hneq : n = minDepthFn t := hgr
  subst hneq
  exact LC111.minDepth_correct t ht

/-! ## Running / cross-checking the emergent fold against `leet/L111.lean` -/

-- The derived answers, matching `L111`'s stated results (the concrete `Nat` value is `decide`d).
example : minDepthFn (Tree.nil : Tree Int) = 0 := by decide
example : minDepthFn (Tree.node (leaf 2) 1 (leaf 3)) = 2 := by decide
-- The one-child gotcha: root `1` has ONLY a left child (leaf `2`); the shortest root-to-leaf path is
-- 1 → 2 (2 nodes), NOT 1 — the emergent step reads this off `dl = 2 ≠ 0`, `dr = 0`.
example : minDepthFn (Tree.node (leaf 2) 1 Tree.nil) = 2 := by decide

/-- The emergent single-value fold genuinely relates `node (leaf 2) 1 (leaf 3)` to its folded depth
    `2`, proved via `mindepth_emerges` (no re-computation). -/
example : cataTreeFold (treeScalarAlg g step) (Tree.node (leaf 2) 1 (leaf 3)) 2 := by
  have h : (graph minDepthFn : dTree Int ⟶ ⟨Nat⟩)
      (Tree.node (leaf 2) 1 (leaf 3)) 2 := rfl
  rw [mindepth_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC111D
