/-
  LeetCode 230 — Kth Smallest Element in a BST — DERIVED as a tree catamorphism over `List Int`.

  `Fredy/L230.lean` WRITES the inorder traversal `inorder : Tree Int → List Int` by hand
  (`inorder nil = []`, `inorder (node l a r) = inorder l ++ a :: inorder r`) and then reads the
  answer off index `k-1` (`kthSmallestFn t k = (inorder t)[k-1]?`).  HERE we expose `inorder` as
  what it structurally IS: the catamorphism of the scalar tree algebra
  `treeScalarAlg g step = [ nil ↦ [], (cl,a,cr) ↦ cl ++ a :: cr ]` on the carrier `C := List Int`.

  The base `g = []` and step `step cl a cr = cl ++ a :: cr` are READ OFF `inorder`'s two defining
  equations (`inorder_nil`, `inorder_node`).  `inorder` obeys the structural recursion
  `inorder nil = g`, `inorder (node l a r) = step (inorder l) a (inorder r)` (both `rfl`), so the
  general-carrier fold-uniqueness law `TB.treeFold_unique` (`Fredy/A6_GenFold.lean`) PRODUCES the
  catamorphism `cataR (treeScalarAlg g step)` and identifies it with `graph inorder`
  (`inorder_emerges`): the sorted enumeration is not written, it emerges.

  The final program `LC230.solve` applies the index read-off `xs ↦ xs[k-1]?` to the fold's output
  (`solve_via_fold`).  Correctness is REUSED, not re-proved: `LC230.kthSmallest_correct` (the exact
  "`v` is a genuine label AND exactly `k-1` labels are strictly smaller" fact, from the strict-
  sortedness + membership + rank machinery of `L230`) transports onto the emergent fold's output
  (`kthSmallest_derived_correct`).

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataTreeFold` /
  `treeFold_unique` only, never the `cataR_eq_relCata` bridge (which pulls `Classical.choice`).
-/
import Fredy.A6_GenFold
import Fredy.L230

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC230D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC230
open Freyd.Alg.RelSet.LC98 (IsBST)

/-! ## The base and step, READ OFF `L230.inorder` (carrier `C := List Int`) -/

/-- The base of the emergent algebra: `g = inorder nil = []` — the empty tree enumerates nothing. -/
def g : List Int := []

/-- The step of the emergent algebra: from the two children's enumerations `cl = inorder l`,
    `cr = inorder r` and the root label `a`, the parent's enumeration is `cl ++ a :: cr` — left
    subtree, then the root, then the right subtree.  Read off `inorder`'s node clause. -/
def step : List Int → Int → List Int → List Int := fun cl a cr => cl ++ a :: cr

/-! ## The FORCED structural recursion of `inorder` -/

/-- The base condition: `inorder nil = g` (`inorder_nil`, definitional). -/
theorem hnil : inorder Tree.nil = g := rfl

/-- The step condition: `inorder (node l a r) = step (inorder l) a (inorder r)` — the inorder
    recurrence, `rfl` (`inorder`'s node clause is `inorder l ++ a :: inorder r = step …`). -/
theorem hnode (l : Tree Int) (a : Int) (r : Tree Int) :
    inorder (Tree.node l a r) = step (inorder l) a (inorder r) := rfl

/-! ## The catamorphism EMERGES via the general-carrier law -/

/-- **The inorder enumeration EMERGES.**  `graph inorder` equals the catamorphism of the scalar tree
    algebra `treeScalarAlg g step = [ nil ↦ [], (cl,a,cr) ↦ cl ++ a :: cr ]` on the carrier
    `List Int`, PRODUCED by `TB.treeFold_unique` from the forced base `g` and step `step`.  The
    hand-written traversal is now a single catamorphism over the tree, whose output is the sorted
    label list — the AOP way to expose a structural recursion as a fold. -/
theorem inorder_emerges :
    (graph inorder : dTree Int ⟶ ⟨List Int⟩) = cataR (treeScalarAlg g step) :=
  TB.treeFold_unique g step inorder hnil hnode

/-! ## Connecting the emergent fold back to `L230.solve` -/

/-- **`LC230.solve` reads the answer off the fold.**  `solve (t, k)` relates to `v` exactly when the
    emergent catamorphism folds `t` to some enumeration `xs` whose index `k-1` is `v`
    (`solve = graph solveFn`, `solveFn (t,k) = (inorder t)[k-1]?`, and emergence pins the fold's
    output to `inorder t`).  This is the index read-off `xs ↦ xs[k-1]?` post-composed with the
    fold — the honest shape of the whole program. -/
theorem solve_via_fold (t : Tree Int) (k : Nat) (v : Option Int) :
    LC230.solve (t, k) v ↔
      ∃ xs, cataTreeFold (treeScalarAlg g step) t xs ∧ xs[k - 1]? = v := by
  constructor
  · intro h
    refine ⟨inorder t, ?_, ?_⟩
    · have hgr : (graph inorder : dTree Int ⟶ ⟨List Int⟩) t (inorder t) := rfl
      rw [inorder_emerges] at hgr; exact hgr
    · exact (h : v = (inorder t)[k - 1]?).symm
  · rintro ⟨xs, hxs, hidx⟩
    have hgr : (graph inorder : dTree Int ⟶ ⟨List Int⟩) t xs := by
      rw [inorder_emerges]; exact hxs
    have hxeq : xs = inorder t := hgr
    subst hxeq
    exact (show v = (inorder t)[k - 1]? from hidx.symm)

/-! ## Correctness of the derived program, transported from `L230.kthSmallest_correct` -/

/-- **The Kth-Smallest program is the tree catamorphism, and it is correct.**  The honest headline
    bundles:

    * `inorder_emerges` — `graph inorder = cataR (treeScalarAlg g step)`: the enumeration IS the
      catamorphism over the carrier `List Int`; and
    * the transported correctness — for ANY enumeration `xs` the emergent fold relates a `BST` `t`
      to, whenever index `k-1` of `xs` is `some v`, `v` is a genuine label of `t` AND exactly `k-1`
      of `t`'s labels are strictly smaller than `v` (the precise meaning of "`v` is the `k`-th
      smallest").  Emergence pins `xs = inorder t`, and `L230.kthSmallest_correct` (the existing
      strict-sortedness + membership + rank fact, NOT re-proved here) supplies the rank. -/
theorem kthSmallest_derived_correct :
    ((graph inorder : dTree Int ⟶ ⟨List Int⟩) = cataR (treeScalarAlg g step)) ∧
    (∀ (t : Tree Int), IsBST t → ∀ (xs : List Int),
        cataTreeFold (treeScalarAlg g step) t xs →
        ∀ (k : Nat) (v : Int), xs[k - 1]? = some v →
          memT t v ∧ (xs.filter (fun y => decide (y < v))).length = k - 1) := by
  refine ⟨inorder_emerges, ?_⟩
  intro t hbst xs hxs k v hk
  have hgr : (graph inorder : dTree Int ⟶ ⟨List Int⟩) t xs := by
    rw [inorder_emerges]; exact hxs
  have hxeq : xs = inorder t := hgr
  subst hxeq
  exact kthSmallest_correct hbst hk

/-! ## Running / cross-checking the emergent fold against `Fredy/L230.lean` -/

-- The derived answers, matching `L230`'s stated results (only the final `Option Int` is `decide`d).
example : solveFn (sampleBST, 1) = some 2 := by decide
example : solveFn (sampleBST, 3) = some 4 := by decide
example : solveFn (sampleBST, 6) = some 9 := by decide
example : solveFn (sampleBST, 7) = none := by decide

/-- The emergent catamorphism genuinely relates `sampleBST` to its inorder enumeration
    `[2,3,4,5,8,9]` — the list the fold produces, proved via `inorder_emerges` (the carrier is
    `List Int`, so this cross-checks the fold's output directly, `decide`d). -/
example : cataTreeFold (treeScalarAlg g step) sampleBST [2, 3, 4, 5, 8, 9] := by
  have h : (graph inorder : dTree Int ⟶ ⟨List Int⟩) sampleBST [2, 3, 4, 5, 8, 9] :=
    show ([2, 3, 4, 5, 8, 9] : List Int) = inorder sampleBST by decide
  rw [inorder_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC230D
