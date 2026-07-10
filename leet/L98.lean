/-
  LeetCode 98 — Validate Binary Search Tree — as an ALLEGORY PROGRAM.

  Problem: decide whether a binary tree is a valid BST — every node's label lies strictly between
  the labels forced on it by its ancestors (not merely between its immediate parent and that one
  child, the classic bug).

  This is a DECISION (`Bool`) built on `AOP.A6_TreeBin`'s `Tree`, like `L20`/`L104`, but with a
  NEW recursion shape: the fold carries a BOUNDS ACCUMULATOR `(lo hi : Option Int)` PASSED DOWN
  the recursion (tightened at each node: `l` inherits `hi := some a`, `r` inherits `lo := some
  a`), in contrast to a normal bottom-up cata (`L104`'s depth, `L20`'s stack) whose state flows
  UP from the leaves. `none` is the sentinel "no bound yet" (the root call `within none none t`).

  1. **Data** — `Tree Int` (`AOP.A6_TreeBin`), `A = Int` (bounds are compared against labels).

  2. **Program** — `within lo hi t` : `nil` is trivially in range; `node l a r` requires `a` to
     respect both inherited bounds AND recurses with the TIGHTENED bounds `within lo (some a) l`,
     `within (some a) hi r`. `bstFn t := within none none t`; `solve := graph bstFn`.

  3. **Specification** — `BSTwithin lo hi t` is the `Prop` mirror of `within` (same shape, `∧`
     instead of `&&`); `IsBST t := BSTwithin none none t`.

  4. **Correctness** — `within_correct : within lo hi t = true ↔ BSTwithin lo hi t`, a genuine
     `Iff` (a decision, not an optimum — same shape as `L20`'s `solve_correct`). Proved by
     recursion DIRECTLY on `t`, with `lo hi` GENERALIZED (left as bound variables of the
     recursive theorem, never fixed before the recursion) — the node case's two recursive calls
     need the theorem at the TIGHTENED bounds `(lo, some a)` / `(some a, hi)`, not the original
     `(lo, hi)`, so an `induction t` with `lo hi` fixed in the context would leave the wrong
     induction hypothesis.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_TreeBin
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC98

open Freyd Freyd.Alg.RelSet.TB

/-! ## Object of `Bool` answers in `Rel(Set)` -/

abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## The program: a bounds-checking scan, bounds `(lo hi : Option Int)` threaded DOWN -/

/-- The concrete fold (structural recursion): `within lo hi t` decides whether every label in `t`
    respects the inherited bounds `lo < · < hi` (a `none` bound is "unconstrained"), TIGHTENING
    the bounds on the way down — `l` additionally bounded above by `a`, `r` additionally bounded
    below by `a`. This is an accumulator threaded DOWN the recursion, not a bottom-up fold. -/
def within : Option Int → Option Int → Tree Int → Bool
  | _, _, Tree.nil => true
  | lo, hi, Tree.node l a r =>
      (match lo with | none => true | some x => decide (x < a)) &&
      (match hi with | none => true | some y => decide (a < y)) &&
      within lo (some a) l && within (some a) hi r

@[simp] theorem within_nil (lo hi : Option Int) : within lo hi Tree.nil = true := rfl
@[simp] theorem within_node (lo hi : Option Int) (l r : Tree Int) (a : Int) :
    within lo hi (Tree.node l a r) =
      ((match lo with | none => true | some x => decide (x < a)) &&
       (match hi with | none => true | some y => decide (a < y)) &&
       within lo (some a) l && within (some a) hi r) := rfl

/-- The decision: `t` is a valid BST iff every label respects its inherited (initially
    unconstrained) bounds. -/
def bstFn (t : Tree Int) : Bool := within none none t

/-- **The allegory program**: LeetCode 98's decision as a morphism `dTree Int ⟶ Bool` in
    `Rel(Set)`. -/
def solve : dTree Int ⟶ dBool := graph bstFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map bstFn

/-! ## Specification: the `Prop` mirror of `within`, bounds threaded the same way -/

/-- `BSTwithin lo hi t` — the `Prop` mirror of `within`: every label in `t` lies strictly between
    the inherited bounds `lo` and `hi` (`none` = unconstrained). -/
def BSTwithin : Option Int → Option Int → Tree Int → Prop
  | _, _, Tree.nil => True
  | lo, hi, Tree.node l a r =>
      (match lo with | none => True | some x => x < a) ∧
      (match hi with | none => True | some y => a < y) ∧
      BSTwithin lo (some a) l ∧ BSTwithin (some a) hi r

/-- `t` is a valid BST: every label respects its inherited (initially unconstrained) bounds. -/
def IsBST (t : Tree Int) : Prop := BSTwithin none none t

/-- The **specification** as a morphism `dTree Int ⟶ Bool` in `Rel(Set)`: `r = true` iff `t` is a
    valid BST — a genuine `Iff`, since this is a DECISION problem, not an optimum to extremize. -/
def spec : dTree Int ⟶ dBool := fun t r => (r = true ↔ IsBST t)

/-! ## Correctness: `within` decides `BSTwithin`, bounds generalized -/

/-- **Correctness of the bounds scan**, `lo hi` GENERALIZED (recursed on directly, not fixed
    before an `induction t`): the two `node` recursive calls need the theorem at the TIGHTENED
    bounds `(lo, some a)`/`(some a, hi)`, so the bounds must vary across the recursion. -/
theorem within_correct : ∀ (lo hi : Option Int) (t : Tree Int),
    within lo hi t = true ↔ BSTwithin lo hi t
  | _, _, Tree.nil => by simp [within, BSTwithin]
  | lo, hi, Tree.node l a r => by
      have ihl := within_correct lo (some a) l
      have ihr := within_correct (some a) hi r
      simp only [within_node, BSTwithin, Bool.and_eq_true_iff]
      constructor
      · rintro ⟨⟨⟨hlo, hhi⟩, hl⟩, hr⟩
        refine ⟨?_, ?_, ihl.mp hl, ihr.mp hr⟩
        · cases lo with
          | none => trivial
          | some x => exact decide_eq_true_eq.mp hlo
        · cases hi with
          | none => trivial
          | some y => exact decide_eq_true_eq.mp hhi
      · rintro ⟨hlo, hhi, hl, hr⟩
        refine ⟨⟨⟨?_, ?_⟩, ihl.mpr hl⟩, ihr.mpr hr⟩
        · cases lo with
          | none => trivial
          | some x => exact decide_eq_true_eq.mpr hlo
        · cases hi with
          | none => trivial
          | some y => exact decide_eq_true_eq.mpr hhi

/-- **Correctness of the allegory program**: `t` is decided a valid BST iff it actually is one. -/
theorem solve_correct (t : Tree Int) : bstFn t = true ↔ IsBST t := within_correct none none t

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

example : bstFn (Tree.node (leaf (1 : Int)) 2 (leaf 3)) = true := by decide
example : bstFn (Tree.node (leaf (3 : Int)) 2 (leaf 1)) = false := by decide
-- the classic non-local violator: 4 < 5 but sits in 5's right subtree
example : bstFn (Tree.node (leaf (1 : Int)) 5 (Tree.node (leaf 4) 6 (leaf 7))) = false := by decide
example : bstFn (Tree.nil : Tree Int) = true := by decide

end Freyd.Alg.RelSet.LC98
