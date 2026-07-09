/-
  LeetCode 230 — Kth Smallest Element in a BST — DERIVED as a tree catamorphism, O(n) via a
  DIFFERENCE-LIST carrier.

  `Fredy/L230.lean` WRITES the inorder traversal `inorder : Tree Int → List Int` by hand
  (`inorder nil = []`, `inorder (node l a r) = inorder l ++ a :: inorder r`).  Reading that as a
  fold on the carrier `C := List Int` gives the step `cl a cr ↦ cl ++ a :: cr`, which
  left-concatenates the whole left enumeration at EVERY node — **O(n²)** overall.  Inorder is O(n).

  HERE we expose `inorder` as a fold on the DIFFERENCE-LIST carrier `C := List Int → List Int`
  (a list represented as "prepend me to any tail `acc`"):

    * base (nil)  `g   := (id : List Int → List Int)`              — the empty tree prepends nothing;
    * step        `step kl a kr := fun acc => kl (a :: kr acc)`    — right enumeration onto `acc`,
      then the root `a`, then the left enumeration; each step is one `cons` + two function calls,
      **O(1)** — there is no `++` anywhere.

  `inorderDL t` is the difference list; the actual inorder list is read at the empty accumulator,
  `inorderDL t [] = inorder t` (helper induction `inorderDL t acc = inorder t ++ acc`).  The
  general-carrier fold-uniqueness law `TB.treeFold_unique` (`Fredy/A6_GenFold.lean`), instantiated at
  the FUNCTION carrier `List Int → List Int`, PRODUCES the catamorphism `cataR (treeScalarAlg g step)`
  and identifies it with `graph inorderDL` (`inorder_emerges`): the O(n) traversal is not written,
  it emerges from the base `g` and the O(1) step.

  The final program `LC230.solve` reads the answer off the fold's output at the empty accumulator
  (`solve_via_fold`: index `k-1` of `(inorderDL t) []`).  Correctness is REUSED, not re-proved:
  `LC230.kthSmallest_correct` (the exact "`v` is a genuine label AND exactly `k-1` labels are
  strictly smaller" fact, from the strict-sortedness + membership + rank machinery of `L230`)
  transports through `inorderDL t [] = inorder t` onto the emergent fold's output
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

/-! ## The base and step, on the DIFFERENCE-LIST carrier `C := List Int → List Int` -/

/-- The base of the emergent algebra: `g = id` — the empty tree prepends nothing to any tail. -/
def g : List Int → List Int := id

/-- The step of the emergent algebra, O(1): given the children's difference lists `kl = inorderDL l`,
    `kr = inorderDL r` and the root label `a`, the parent's difference list prepends, into any tail
    `acc`, first the right enumeration (`kr acc`), then the root `a`, then the left enumeration
    (`kl (a :: kr acc)`) — one `cons` and two function calls per node, NO `++`. -/
def step : (List Int → List Int) → Int → (List Int → List Int) → (List Int → List Int) :=
  fun kl a kr => fun acc => kl (a :: kr acc)

/-! ## The difference-list traversal and its FORCED structural recursion -/

/-- The inorder traversal as a difference list: `inorderDL t acc` prepends `t`'s inorder enumeration
    to `acc`.  Structural recursion, no fuel, O(n) total (the step is O(1)). -/
def inorderDL : Tree Int → (List Int → List Int)
  | Tree.nil => id
  | Tree.node l a r => fun acc => inorderDL l (a :: inorderDL r acc)

/-- The base condition: `inorderDL nil = g` (`id`, definitional). -/
theorem hnil : inorderDL Tree.nil = g := rfl

/-- The step condition: `inorderDL (node l a r) = step (inorderDL l) a (inorderDL r)` — the
    difference-list recurrence, `rfl` (`inorderDL`'s node clause is exactly `step`'s body). -/
theorem hnode (l : Tree Int) (a : Int) (r : Tree Int) :
    inorderDL (Tree.node l a r) = step (inorderDL l) a (inorderDL r) := rfl

/-! ## Reading the difference list at the empty accumulator recovers `L230.inorder` -/

/-- The defining property of the difference list: `inorderDL t acc = inorder t ++ acc`.  Proved by
    structural induction; the `++` lives ONLY in this correctness bridge, never in the program. -/
theorem inorderDL_append (t : Tree Int) (acc : List Int) :
    inorderDL t acc = inorder t ++ acc := by
  induction t generalizing acc with
  | nil => rfl
  | node l a r ihl ihr =>
      show inorderDL l (a :: inorderDL r acc) = (inorder l ++ a :: inorder r) ++ acc
      rw [ihl, ihr, List.append_assoc]
      rfl

/-- At the empty accumulator the difference list IS `L230.inorder`. -/
theorem inorderDL_nil_eq_inorder (t : Tree Int) : inorderDL t [] = inorder t := by
  rw [inorderDL_append, List.append_nil]

/-! ## The catamorphism EMERGES via the general-carrier law (function carrier) -/

/-- **The O(n) inorder traversal EMERGES.**  `graph inorderDL` equals the catamorphism of the scalar
    tree algebra `treeScalarAlg g step = [ nil ↦ id, (kl,a,kr) ↦ fun acc => kl (a :: kr acc) ]` on the
    DIFFERENCE-LIST carrier `List Int → List Int`, PRODUCED by `TB.treeFold_unique` from the forced
    base `g` and O(1) step `step`.  The hand-written traversal is now a single catamorphism whose
    O(1) step makes the whole fold O(n) — the AOP way to expose (and improve) a structural recursion
    as a fold. -/
theorem inorder_emerges :
    (graph inorderDL : dTree Int ⟶ ⟨List Int → List Int⟩) = cataR (treeScalarAlg g step) :=
  TB.treeFold_unique g step inorderDL hnil hnode

/-! ## Connecting the emergent fold back to `L230.solve` (read-off at the empty accumulator) -/

/-- **`LC230.solve` reads the answer off the fold at the empty accumulator.**  `solve (t, k)` relates
    to `v` exactly when the emergent catamorphism folds `t` to some difference list `f` whose value at
    the empty accumulator, indexed at `k-1`, is `v` (`solve = graph solveFn`,
    `solveFn (t,k) = (inorder t)[k-1]?`, and emergence pins the fold's output to `inorderDL t`, with
    `inorderDL t [] = inorder t`).  This is the index read-off `f ↦ (f [])[k-1]?` post-composed with
    the fold — the honest shape of the whole program. -/
theorem solve_via_fold (t : Tree Int) (k : Nat) (v : Option Int) :
    LC230.solve (t, k) v ↔
      ∃ f, cataTreeFold (treeScalarAlg g step) t f ∧ (f [])[k - 1]? = v := by
  constructor
  · intro h
    refine ⟨inorderDL t, ?_, ?_⟩
    · have hgr : (graph inorderDL : dTree Int ⟶ ⟨List Int → List Int⟩) t (inorderDL t) := rfl
      rw [inorder_emerges] at hgr; exact hgr
    · rw [inorderDL_nil_eq_inorder]; exact (h : v = (inorder t)[k - 1]?).symm
  · rintro ⟨f, hf, hidx⟩
    have hgr : (graph inorderDL : dTree Int ⟶ ⟨List Int → List Int⟩) t f := by
      rw [inorder_emerges]; exact hf
    have hfeq : f = inorderDL t := hgr
    subst hfeq
    rw [inorderDL_nil_eq_inorder] at hidx
    exact (show v = (inorder t)[k - 1]? from hidx.symm)

/-! ## Correctness of the derived program, transported from `L230.kthSmallest_correct` -/

/-- **The Kth-Smallest program is the O(n) tree catamorphism, and it is correct.**  The honest
    headline bundles:

    * `inorder_emerges` — `graph inorderDL = cataR (treeScalarAlg g step)`: the traversal IS the
      catamorphism over the DIFFERENCE-LIST carrier `List Int → List Int`, whose step is O(1); and
    * the transported correctness — for ANY difference list `f` the emergent fold relates a `BST` `t`
      to, reading it at the empty accumulator (`f []`), whenever index `k-1` is `some v`, `v` is a
      genuine label of `t` AND exactly `k-1` of `t`'s labels are strictly smaller than `v` (the
      precise meaning of "`v` is the `k`-th smallest").  Emergence pins `f = inorderDL t` and
      `inorderDL t [] = inorder t`, and `L230.kthSmallest_correct` (the existing strict-sortedness +
      membership + rank fact, NOT re-proved here) supplies the rank. -/
theorem kthSmallest_derived_correct :
    ((graph inorderDL : dTree Int ⟶ ⟨List Int → List Int⟩) = cataR (treeScalarAlg g step)) ∧
    (∀ (t : Tree Int), IsBST t → ∀ (f : List Int → List Int),
        cataTreeFold (treeScalarAlg g step) t f →
        ∀ (k : Nat) (v : Int), (f [])[k - 1]? = some v →
          memT t v ∧ ((f []).filter (fun y => decide (y < v))).length = k - 1) := by
  refine ⟨inorder_emerges, ?_⟩
  intro t hbst f hf k v hk
  have hgr : (graph inorderDL : dTree Int ⟶ ⟨List Int → List Int⟩) t f := by
    rw [inorder_emerges]; exact hf
  have hfeq : f = inorderDL t := hgr
  subst hfeq
  rw [inorderDL_nil_eq_inorder] at hk ⊢
  exact kthSmallest_correct hbst hk

/-! ## Running / cross-checking the emergent fold against `Fredy/L230.lean` -/

-- The derived answers, matching `L230`'s stated results (only the final `Option Int` is `decide`d).
example : solveFn (sampleBST, 1) = some 2 := by decide
example : solveFn (sampleBST, 3) = some 4 := by decide
example : solveFn (sampleBST, 6) = some 9 := by decide
example : solveFn (sampleBST, 7) = none := by decide

/-- The emergent catamorphism relates `sampleBST` to its difference list `inorderDL sampleBST`
    (proved via `inorder_emerges`; the carrier is the function type, so this cross-checks that the
    fold's output IS the difference list, not `decide`d — a function can't be `decide`d). -/
example : cataTreeFold (treeScalarAlg g step) sampleBST (inorderDL sampleBST) := by
  have h : (graph inorderDL : dTree Int ⟶ ⟨List Int → List Int⟩) sampleBST (inorderDL sampleBST) :=
    rfl
  rw [inorder_emerges] at h
  exact h

/-- Reading that difference list at the empty accumulator gives the inorder enumeration
    `[2,3,4,5,8,9]` — `decide`d on the APPLIED list `(inorderDL sampleBST) []`. -/
example : (inorderDL sampleBST) [] = [2, 3, 4, 5, 8, 9] := by decide

end Freyd.Alg.RelSet.LC230D
