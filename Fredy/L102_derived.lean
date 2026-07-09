/-
  LeetCode 102 — Binary Tree Level Order Traversal — DERIVED as a tree catamorphism.

  `Fredy/L102.lean` WRITES the level-merging fold `levels : Tree Int → List (List Int)` by hand
  (`nil ↦ []`, `node l a r ↦ [a] :: mergeLevels (levels l) (levels r)`) and verifies it against the
  honest depth spec `atDepth`.  HERE we do the reshaping the AOP way: the SAME first-order recursion
  is read off as a scalar tree algebra `[g, step]` over the bare carrier `C := List (List Int)`, and
  the general-carrier fold-uniqueness law `TB.treeFold_unique` (`Fredy/A6_GenFold.lean`) PRODUCES the
  catamorphism `cataR (treeScalarAlg g step)` and identifies it with `graph levels`
  (`levels_emerges`).

  The carrier is nontrivial — a growing `List (List Int)` merged depth-by-depth by `mergeLevels`,
  not a fixed-width tuple — so this is a genuine derivation, not a wrapper: `L102` does NOT exhibit
  its `solve` as a `cataR`.  The step is unconditional (no nil-detector is needed, unlike `L111`):
  `g := []` and `step cl a cr := [a] :: mergeLevels cl cr` are FORCED by `levels`'s two defining
  equations, so `hnil`/`hnode` hold definitionally.

  `derivedSolve := cataR (treeScalarAlg g step)` is `L102.solve` (`= graph levels`), and
  `L102.solve_correct` (the existing `atDepth`/`height` correctness, NOT re-proved here) transports
  onto the emergent fold (`levels_derived_correct`): the level-list the catamorphism relates a tree
  to has, at every depth `d`, exactly the row `atDepth t d`, and has exactly `height t` rows.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataTreeFold` /
  `treeFold_unique` only, never the `cataR_eq_relCata` bridge (which pulls `Classical.choice`).
-/
import Fredy.A6_GenFold
import Fredy.L102

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC102D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC102

/-! ## The base and step of the emergent scalar algebra, carrier `C := List (List Int)`

  Read off `L102.levels`'s two clauses.  There is no branching: the node clause prepends the label's
  singleton row `[a]` and merges the two children's level-lists row-by-row with `mergeLevels`. -/

/-- The base of the emergent algebra: `g = levels nil = []`. -/
def g : List (List Int) := levels Tree.nil

/-- The step: from the children's folded level-lists `cl, cr` and the label `a`, reproduce
    `levels (node l a r)` — the row `[a]` at depth `0`, then the two children merged depth-by-depth. -/
def step (cl : List (List Int)) (a : Int) (cr : List (List Int)) : List (List Int) :=
  [a] :: mergeLevels cl cr

/-! ## The FORCED first-order recursion of `levels` -/

/-- The base condition: `levels nil = g`, definitionally. -/
theorem hnil : levels Tree.nil = g := rfl

/-- The step condition: `levels (node l a r) = step (levels l) a (levels r)`, definitionally
    (`levels`'s node clause IS `[a] :: mergeLevels (levels l) (levels r)`). -/
theorem hnode : ∀ (l : Tree Int) (a : Int) (r : Tree Int),
    levels (Tree.node l a r) = step (levels l) a (levels r) :=
  fun _ _ _ => rfl

/-! ## The level-order catamorphism EMERGES via the general-carrier law -/

/-- **The level-order fold EMERGES.**  `graph levels` equals the catamorphism of the scalar tree
    algebra `treeScalarAlg g step = [ nil ↦ [], (cl,a,cr) ↦ [a] :: mergeLevels cl cr ]` on the
    carrier `List (List Int)`, PRODUCED by `TB.treeFold_unique` from the forced base `g` and step
    `step`.  The level-merging recurrence is not written; it emerges as the unique fold. -/
theorem levels_emerges :
    (graph levels : dTree Int ⟶ dAns) = cataR (treeScalarAlg g step) :=
  TB.treeFold_unique g step levels hnil hnode

/-! ## Connecting the emergent fold back to `L102.solve` -/

/-- The derived solver: the emergent catamorphism of the scalar level-merging algebra. -/
def derivedSolve : dTree Int ⟶ dAns := cataR (treeScalarAlg g step)

/-- The derived solver IS `L102.solve` (`= graph levels`): the hand-written program is exactly the
    emergent catamorphism. -/
theorem derivedSolve_eq_solve : derivedSolve = LC102.solve := levels_emerges.symm

/-! ## Correctness of the derived program, transported from `L102.solve_correct` -/

/-- **The Level-Order program is the tree catamorphism, and it is correct.**  The headline bundles:

    * `levels_emerges` — `graph levels = cataR (treeScalarAlg g step)`: the hand-written program IS
      the emergent catamorphism over the carrier `List (List Int)`; and
    * the transported correctness — for any tree `t`, the level-list `L` the emergent fold relates
      `t` to (necessarily `levels t`, by emergence) has, at every depth `d`, exactly the row
      `atDepth t d`, and has exactly `height t` rows.  `L102.solve_correct` (the existing
      correctness, NOT re-proved here) supplies both halves. -/
theorem levels_derived_correct :
    ((graph levels : dTree Int ⟶ dAns) = cataR (treeScalarAlg g step)) ∧
    (∀ (t : Tree Int) (L : List (List Int)),
        cataTreeFold (treeScalarAlg g step) t L →
        (∀ d, rowAt L d = atDepth t d) ∧ L.length = height t) := by
  refine ⟨levels_emerges, ?_⟩
  intro t L hf
  have hgr : (graph levels : dTree Int ⟶ dAns) t L := by
    rw [levels_emerges]; exact hf
  have hLq : L = levels t := hgr
  subst hLq
  exact LC102.solve_correct t

/-! ## Running / cross-checking the emergent fold against `Fredy/L102.lean` -/

-- The derived answers, matching `L102`'s stated results (the concrete level-list is `decide`d).
example : levels (Tree.nil : Tree Int) = [] := by decide
example : levels (bal (1 : Int) 2 3) = [[1], [2, 3]] := by decide
-- The unbalanced tree exercises `mergeLevels`'s unequal-length branch (row `[4]` has no partner).
example : levels unbal = [[1], [2, 3], [4]] := by decide

/-- The emergent fold genuinely relates `bal 1 2 3` to its folded level-list `[[1],[2,3]]`, proved
    via `levels_emerges` (no re-computation). -/
example : cataTreeFold (treeScalarAlg g step) (bal (1 : Int) 2 3) [[1], [2, 3]] := by
  have h : (graph levels : dTree Int ⟶ dAns) (bal (1 : Int) 2 3) [[1], [2, 3]] := rfl
  rw [levels_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC102D
