/-
  LeetCode 110 — Balanced Binary Tree — DERIVED from the TREE TUPLING LAW.

  `leet/L110.lean` WRITES the pair-carrying fold `foldFn = (height, balanced)` by hand and then
  verifies it.  HERE the fold EMERGES.  The starting point is the NAIVE specification, which at every
  node RECOMPUTES both subtree heights from scratch:

    * `heightOf`  (imported from `L110`) — the structural height, recomputed per node;
    * `balOf`     — the Boolean balance predicate, `true` at `nil` and, at `node l a r`, the two
      children's flags AND the local one-node gap test `imax hl hr − imin hl hr ≤ 1`, where the
      heights are read via `heightOf` (a FRESH recursion at each node — the redundant O(n²) form).

  The tupling ansatz `p t = (heightOf t, balOf t)` carries both.  Its base and step are FORCED (not
  guessed) by `hnil`/`hnode`, which are the problem's own recurrence proved as `rfl`.  Applying the
  tree tupling law `treeTupling gBal stepBal p hnil hnode` PRODUCES the single-pass fold
  `cataR (treePairAlg gBal stepBal)` — the `(height, balanced)` fold `L110` wrote by hand emerges,
  with `stepBal` DEFINITIONALLY the node step of `L110.foldFn` (`stepBal_eq_foldFn`, `rfl`).  Reading
  off the SECOND component recovers the decision `balOf t = true ↔ IsBalanced t` (`balOf_correct`),
  giving the derived analogue of `L110.solve_correct`.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.
-/
import AOP.A6_9_TreeTupling
import leet.L110
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LD110

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC110

/-! ## The naive spec: `heightOf` (imported) + the Boolean balance `balOf` -/

/-- `balOf t` — the Boolean balance predicate, in NAIVE form: it RECOMPUTES `heightOf` of both
    subtrees at every node (the O(n²) computation the emergent fold will linearize).  Boolean mirror
    of `L110.IsBalanced`; the bridge `balOf_correct` proves `balOf t = true ↔ IsBalanced t`. -/
def balOf : Tree Int → Bool
  | Tree.nil => true
  | Tree.node l _ r =>
      balOf l && balOf r &&
        decide (imax (heightOf l) (heightOf r) - imin (heightOf l) (heightOf r) ≤ 1)

/-- The Boolean spec IS the `Prop` spec: `balOf t = true ↔ IsBalanced t`, by structural induction —
    the `Bool.and`/`decide` reflection (exactly `L110.solve_correct`'s inner move, but on the naive
    `balOf`/`heightOf`, with no `foldFn_height` bridge since `balOf` already uses `heightOf`). -/
theorem balOf_correct : ∀ t : Tree Int, balOf t = true ↔ IsBalanced t := by
  intro t
  induction t with
  | nil => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | node l a r ihl ihr =>
    show (balOf l && balOf r &&
        decide (imax (heightOf l) (heightOf r) - imin (heightOf l) (heightOf r) ≤ 1)) = true ↔
      IsBalanced l ∧ IsBalanced r ∧
        imax (heightOf l) (heightOf r) - imin (heightOf l) (heightOf r) ≤ 1
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, ihl, ihr, and_assoc]

/-! ## The tupling ANSATZ and its FORCED base/step -/

/-- Carry the pair `(height, balanced)` — the tupling ansatz. -/
def p (t : Tree Int) : Nat × Bool := (heightOf t, balOf t)

/-- The base of the emergent algebra: `p nil = (0, true)`, forced by the recurrence. -/
def gBal : Nat × Bool := (0, true)

/-- The step of the emergent algebra: carrying `(hl, bl)` and `(hr, br)`, the parent pair is
    `(1 + imax hl hr, bl && br && decide (imax hl hr − imin hl hr ≤ 1))` — read off the recurrence.
    This is DEFINITIONALLY the node step of `L110.foldFn` (see `stepBal_eq_foldFn`). -/
def stepBal : Nat × Bool → Int → Nat × Bool → Nat × Bool :=
  fun pl _ pr =>
    (1 + imax pl.1 pr.1, pl.2 && pr.2 && decide (imax pl.1 pr.1 - imin pl.1 pr.1 ≤ 1))

/-- The step condition (a COMPUTATION, `rfl`): `p nil = gBal`. -/
theorem p_nil : p Tree.nil = gBal := rfl

/-- The step condition (a COMPUTATION, `rfl`): `p (node l a r) = stepBal (p l) a (p r)` — the
    problem's first-order lockstep recurrence, proved not defined. -/
theorem p_node (l r : Tree Int) (a : Int) : p (Tree.node l a r) = stepBal (p l) a (p r) := rfl

/-- The emergent algebra's step IS `L110.foldFn`'s node step, DEFINITIONALLY (`rfl`) — the endpoint
    of the derivation coincides with the hand-written program's fold. -/
theorem stepBal_eq_foldFn (l r : Tree Int) (a : Int) :
    LC110.foldFn (Tree.node l a r) = stepBal (LC110.foldFn l) a (LC110.foldFn r) := rfl

/-! ## The fold EMERGES via the tree tupling law -/

/-- **The `(height, balanced)` fold EMERGES.**  `graph p` equals the catamorphism of the emergent
    algebra `treePairAlg gBal stepBal = [ nil ↦ (0,true), (pl,a,pr) ↦ stepBal pl a pr ]`, PRODUCED by
    the tree tupling law from the forced base `gBal` and step `stepBal`.  The pair-carrying single-
    pass fold was never written by hand here. -/
theorem balanced_emerges :
    (graph p : dTree Int ⟶ ⟨Nat × Bool⟩) = cataR (treePairAlg gBal stepBal) :=
  treeTupling gBal stepBal p p_nil (fun l a r => p_node l r a)

/-- **Correctness of the derived program** (the derived analogue of `L110.solve_correct`): for ANY
    pair `v` the EMERGENT fold relates `t` to, `v.2 = true ↔ IsBalanced t`.  The emergence
    (`balanced_emerges`) pins `v = p t`, whose second slot is `balOf t`; `balOf_correct` reads off the
    decision.  No appeal to `L110.foldFn_height`. -/
theorem balanced_derived_correct (t : Tree Int) (v : Nat × Bool)
    (hv : cataTreeFold (treePairAlg gBal stepBal) t v) : v.2 = true ↔ IsBalanced t := by
  have hgr : (graph p : dTree Int ⟶ ⟨Nat × Bool⟩) t v := by rw [balanced_emerges]; exact hv
  have hveq : v = p t := hgr
  subst hveq
  exact balOf_correct t

/-! ## Running / cross-checking the emergent fold against `leet/L110.lean`

  The relational catamorphism `cataTreeFold (treePairAlg …)` is not `decide`-computable (its `node`
  case is an existential), so we `decide` the extensionally-equal computable witness `p` (equal by
  `balanced_emerges`), cross-check its second slot against `L110.solveFn` on the SAME trees as
  `L110`'s examples, and separately PROVE the fold relates each tree to `p t`. -/

/-- The derived answer agrees with `L110.solveFn` on every example tree of `leet/L110.lean`. -/
example : (p (Tree.node (leaf 1) 2 (leaf 3))).2 = LC110.solveFn (Tree.node (leaf 1) 2 (leaf 3)) := by
  decide
example : (p (Tree.node (Tree.node (leaf 1) 2 Tree.nil) 3 Tree.nil)).2
    = LC110.solveFn (Tree.node (Tree.node (leaf 1) 2 Tree.nil) 3 Tree.nil) := by decide
example : (p (leaf 5)).2 = LC110.solveFn (leaf 5) := by decide
example : (p (Tree.nil : Tree Int)).2 = LC110.solveFn (Tree.nil : Tree Int) := by decide

-- The derived answers, matching `L110`'s stated results.
example : (p (Tree.node (leaf 1) 2 (leaf 3))).2 = true := by decide
example : (p (Tree.node (Tree.node (leaf 1) 2 Tree.nil) 3 Tree.nil)).2 = false := by decide
example : (p (leaf 5)).2 = true := by decide
example : (p (Tree.nil : Tree Int)).2 = true := by decide

/-- The emergent fold genuinely relates `node (leaf 1) 2 (leaf 3)` to `p` of it (whose `.2` is
    `true`). -/
example : cataTreeFold (treePairAlg gBal stepBal)
    (Tree.node (leaf 1) 2 (leaf 3)) (p (Tree.node (leaf 1) 2 (leaf 3))) := by
  have h : (graph p : dTree Int ⟶ ⟨Nat × Bool⟩)
      (Tree.node (leaf 1) 2 (leaf 3)) (p (Tree.node (leaf 1) 2 (leaf 3))) := rfl
  rw [balanced_emerges] at h
  exact h

end Freyd.Alg.RelSet.LD110
