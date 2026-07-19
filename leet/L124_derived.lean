/-
  LeetCode 124 — Binary Tree Maximum Path Sum — DERIVED from the TREE TUPLING LAW.

  `leet/L124.lean` WRITES the pair-carrying fold `foldFn = (best, gain)` by hand and then verifies
  it against the relational spec `pathSum` (`solve = max (≤) · Λ pathSum`, whenever `some`).  HERE the
  single-pass fold EMERGES instead of being written and inductively re-verified.

  The state is the pair `(best, gain)` with carrier `Option Int × Int`:
    * `gain : Int`        — max sum of a non-bending path STARTING at the root and going strictly
      downward (`0` on the empty tree — no extension);
    * `best : Option Int` — max sum of ANY path anywhere in the (sub)tree (`none` only for the empty
      tree, since it has no path at all).

  The base `g = (none, 0)` and step `step` are READ OFF `L124.foldFn`'s two defining equations (the
  `nil` value and the `node` recurrence).  `foldFn` obeys the first-order lockstep recursion
  `foldFn nil = g`, `foldFn (node l a r) = step (foldFn l) a (foldFn r)` — both proved `rfl` (`hnil`,
  `hnode`).  The tree tupling law `TB.treeTupling g step foldFn hnil hnode` then PRODUCES the single-
  pass fold `cataR (treePairAlg g step)` and identifies it with `graph foldFn` (`maxpath_emerges`).
  Reading off the FIRST slot (`treeTupling_fst`) recovers `L124.solve` (`derivedSolve_eq_solve`), and
  `L124.solve_correct` then transports the max-path optimality onto the emergent fold
  (`maxpathsum_derived_correct`).  The carrier being `Option Int × Int` (an `Option-∞` best plus an
  `Int` gain) is irrelevant to the law — the tree tupling law is generic over the carrier.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataTreeFold` /
  `treeTupling` / `treeTupling_fst` only, never the `cataR_eq_relCata` bridge (which pulls
  `Classical.choice`).
-/
import AOP.A6_9_TreeTupling
import leet.L124
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC124D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC124

/-! ## The base and step, READ OFF `L124.foldFn` -/

/-- The base of the emergent algebra: `foldFn nil = (none, 0)` — no path (`none`) and no gain (`0`),
    forced by the recurrence. -/
def g : Option Int × Int := (none, 0)

/-- The step of the emergent algebra: carrying `(bl, gl)` and `(br, gr)`, the parent pair is
    `(omax (omax bl br) (some through), a + imax 0 (imax gl gr))` where `through = a + imax 0 gl +
    imax 0 gr` is the sum of the path that BENDS at this root.  Read off `L124.foldFn`'s node clause;
    it is DEFINITIONALLY that node step (see `hnode`). -/
def step : Option Int × Int → Int → Option Int × Int → Option Int × Int :=
  fun pl a pr =>
    (omax (omax pl.1 pr.1) (some (a + imax 0 pl.2 + imax 0 pr.2)),
     a + imax 0 (imax pl.2 pr.2))

/-! ## The FORCED lockstep recursion of `foldFn` (both `rfl`) -/

/-- The base condition (a COMPUTATION, `rfl`): `foldFn nil = g`. -/
theorem hnil : LC124.foldFn Tree.nil = g := rfl

/-- The step condition (a COMPUTATION, `rfl`): `foldFn (node l a r) = step (foldFn l) a (foldFn r)` —
    the problem's first-order lockstep recurrence, proved not defined. -/
theorem hnode (l r : Tree Int) (a : Int) :
    LC124.foldFn (Tree.node l a r) = step (LC124.foldFn l) a (LC124.foldFn r) := rfl

/-! ## The fold EMERGES via the tree tupling law -/

/-- **The `(best, gain)` fold EMERGES.**  `graph foldFn` equals the catamorphism of the emergent
    algebra `treePairAlg g step = [ nil ↦ (none,0), (pl,a,pr) ↦ step pl a pr ]`, PRODUCED by the tree
    tupling law from the forced base `g` and step `step`.  The pair-carrying single-pass fold was
    never re-written by hand here. -/
theorem maxpath_emerges :
    (graph LC124.foldFn : dTree Int ⟶ ⟨Option Int × Int⟩) = cataR (treePairAlg g step) :=
  treeTupling g step LC124.foldFn hnil (fun l a r => hnode l r a)

/-! ## Reading off the FIRST slot recovers `L124.solve` -/

/-- The derived solver: the emergent fold followed by the first projection (`best`). -/
def derivedSolve : dTree Int ⟶ dAns :=
  cataR (treePairAlg g step) ≫ graph (Prod.fst : Option Int × Int → Option Int)

/-- The derived solver IS `L124.solve`.  `treeTupling_fst` says the graph of `t ↦ (foldFn t).1` — i.e.
    `graph solveFn`, since `solveFn t := (foldFn t).1` — equals `cataR (treePairAlg g step) ≫
    graph Prod.fst = derivedSolve`. -/
theorem derivedSolve_eq_solve : derivedSolve = LC124.solve := by
  show cataR (treePairAlg g step) ≫ graph (Prod.fst : Option Int × Int → Option Int) = graph solveFn
  rw [← treeTupling_fst g step LC124.foldFn hnil (fun l a r => hnode l r a)]
  rfl

/-! ## Correctness of the derived program, transported from `L124.solve_correct` -/

/-- **Correctness of the derived program** (the derived analogue of `L124.solve_correct`,
    `solve = max (≤) · Λ pathSum`): for ANY pair `v` the EMERGENT fold relates a non-empty tree
    `node l a r` to, the first slot `v.1` is `some m` with `m` an achievable `pathSum` and `≤`-greatest
    among all achievable `pathSum`s.  The emergence (`maxpath_emerges`) pins `v = foldFn (node l a r)`,
    whose first slot is `solveFn (node l a r)`; `L124.solve_correct` supplies the extremum. -/
theorem maxpathsum_derived_correct (l r : Tree Int) (a : Int) (v : Option Int × Int)
    (hv : cataTreeFold (treePairAlg g step) (Tree.node l a r) v) :
    ∃ m, v.1 = some m ∧ pathSum (Tree.node l a r) m ∧
      ∀ w, pathSum (Tree.node l a r) w → w ≤ m := by
  have hgr : (graph LC124.foldFn : dTree Int ⟶ ⟨Option Int × Int⟩) (Tree.node l a r) v := by
    rw [maxpath_emerges]; exact hv
  have hveq : v = LC124.foldFn (Tree.node l a r) := hgr
  subst hveq
  exact LC124.solve_correct l r a

/-! ## Running / cross-checking the emergent fold against `leet/L124.lean`

  As in `L110_derived`/`L543_derived`, the relational catamorphism `cataTreeFold (treePairAlg …)` is
  not `decide`-computable (its `node` case is an existential), so we `decide` the extensionally-equal
  computable witness `foldFn` (equal by `maxpath_emerges`), cross-check its first slot against
  `L124.solveFn` on `L124`'s own example trees, and separately PROVE the fold relates a tree to
  `foldFn` of it. -/

/-- The derived answer (first slot of the emergent fold) agrees with `L124.solveFn` on `L124`'s
    example trees. -/
example : (LC124.foldFn (Tree.node (leaf 1) 2 (leaf 3))).1
    = LC124.solveFn (Tree.node (leaf 1) 2 (leaf 3)) := by decide
example : (LC124.foldFn (leaf (-3))).1 = LC124.solveFn (leaf (-3)) := by decide

-- The derived answers, matching `L124`'s stated results.
example : (LC124.foldFn (Tree.node (leaf 1) 2 (leaf 3))).1 = some 6 := by decide
example : (LC124.foldFn (Tree.node (leaf (-10)) 2 (Tree.node (leaf 9) 20 (leaf 7)))).1 = some 36 := by
  decide
example : (LC124.foldFn (leaf (-3))).1 = some (-3) := by decide

/-- The emergent fold genuinely relates `node (leaf 1) 2 (leaf 3)` to `foldFn` of it (whose `.1` is
    `some 6`, the maximum path sum). -/
example : cataTreeFold (treePairAlg g step)
    (Tree.node (leaf 1) 2 (leaf 3)) (LC124.foldFn (Tree.node (leaf 1) 2 (leaf 3))) := by
  have h : (graph LC124.foldFn : dTree Int ⟶ ⟨Option Int × Int⟩)
      (Tree.node (leaf 1) 2 (leaf 3)) (LC124.foldFn (Tree.node (leaf 1) 2 (leaf 3))) := rfl
  rw [maxpath_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC124D
