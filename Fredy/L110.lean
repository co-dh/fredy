/-
  LeetCode 110 — Balanced Binary Tree — as an ALLEGORY PROGRAM (tupled tree cata returning a
  DECISION).

  Problem: a tree is height-balanced iff at EVERY node the two subtree heights differ by `≤ 1`.

  This is L124's TUPLED tree-cata shape (`Fredy.A6_TreeBin`) specialised to a `Bool`-valued
  DECISION instead of an `Int`-valued optimum — the tree analogue of L100's reflection bridge
  (S16), now carrying an extra `Nat` height slot alongside the flag:

  1. **Program.**  `foldFn t = (height, balanced)`: `height` mirrors L104's `depthFn`
     (`nil ↦ 0`, `node l a r ↦ 1 + max(height l, height r)`); `balanced` is `true` for `nil` and,
     at `node l a r`, the conjunction of both children's `balanced` flags AND the local one-node
     test `imax height − imin height ≤ 1` (the `Nat` form of `|height l − height r| ≤ 1`, exact
     since `imax ≥ imin` never truncates).  `solveFn t := (foldFn t).2`;
     `solve : dTree Int ⟶ dBool := graph solveFn`.

  2. **Specification.**  `heightOf` (structural, matches L104's `depthFn`, proved equal to the
     fold's height slot FIRST — S18's "prove the scalar layer before reusing it" lesson) and
     `IsBalanced` (`nil` vacuously balanced; `node l a r` iff both children are balanced AND the
     root's own height gap is `≤ 1` — a Prop mirror of `foldFn`'s two fields, EVERY node checked,
     not just the root).

  3. **Correctness.**  `solve_correct : solveFn t = true ↔ IsBalanced t`, by structural induction
     on `t`: the `nil` case is trivial; the `node` case unfolds the `Bool` conjunction
     (`Bool.and_eq_true`/`decide_eq_true_eq`, NOT `omega` on the resulting `∧` — S3), rewrites the
     height fields via `foldFn_height`, applies the two IHs, and closes with `and_assoc` (exactly
     L100's `solve_correct` shape, one extra conjunct for the height test).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_TreeBin
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC110

open Freyd Freyd.Alg.RelSet.TB

/-! ## Mathlib-free `Nat` `min`/`max` (copied from `L104`/`L124`) -/

def imin (a b : Nat) : Nat := if a ≤ b then a else b
def imax (a b : Nat) : Nat := if a ≤ b then b else a

/-! ## Data/answer objects in `Rel(Set)` -/

/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## The program: the tupled fold `(height, balanced)` -/

/-- The tupled fold: `height` = longest root-to-`nil` path (mirrors L104's `depthFn`);
    `balanced` = `true` iff EVERY node's two subtree heights differ by `≤ 1`. -/
def foldFn : Tree Int → Nat × Bool
  | Tree.nil => (0, true)
  | Tree.node l _ r =>
    let (hl, bl) := foldFn l
    let (hr, br) := foldFn r
    (1 + imax hl hr, bl && br && decide (imax hl hr - imin hl hr ≤ 1))

/-- `heightFn t` — the first fold component: `t`'s height. -/
def heightFn (t : Tree Int) : Nat := (foldFn t).1

/-- `solveFn t` — the answer: `true` iff `t` is height-balanced. -/
def solveFn (t : Tree Int) : Bool := (foldFn t).2

@[simp] theorem heightFn_nil : heightFn Tree.nil = 0 := rfl
@[simp] theorem solveFn_nil : solveFn Tree.nil = true := rfl

theorem heightFn_node (l r : Tree Int) (a : Int) :
    heightFn (Tree.node l a r) = 1 + imax (heightFn l) (heightFn r) := rfl

theorem solveFn_node (l r : Tree Int) (a : Int) :
    solveFn (Tree.node l a r) =
      (solveFn l && solveFn r &&
        decide (imax (heightFn l) (heightFn r) - imin (heightFn l) (heightFn r) ≤ 1)) := rfl

/-- **The allegory program**: LeetCode 110's solution as a morphism `dTree Int ⟶ dBool` in
    `Rel(Set)`. -/
def solve : dTree Int ⟶ dBool := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## Specification: `heightOf` (matches `heightFn`) and `IsBalanced` (every node checked) -/

/-- `heightOf t` — the length of `t`'s longest root-to-`nil` path (matches L104's spec target;
    proved to equal `heightFn` below). -/
def heightOf : Tree Int → Nat
  | Tree.nil => 0
  | Tree.node l _ r => 1 + imax (heightOf l) (heightOf r)

/-- `IsBalanced t` — `t` is height-balanced: vacuously so for `nil`; at `node l a r`, BOTH
    children are balanced AND the root's own height gap is `≤ 1` — EVERY node is checked, not
    just the root. -/
def IsBalanced : Tree Int → Prop
  | Tree.nil => True
  | Tree.node l _ r =>
      IsBalanced l ∧ IsBalanced r ∧ imax (heightOf l) (heightOf r) - imin (heightOf l) (heightOf r) ≤ 1

@[simp] theorem IsBalanced_nil : IsBalanced Tree.nil := trivial

/-! ## Correctness -/

/-- **The height invariant, proved FIRST** (S18's lesson: prove the scalar layer before reusing
    it in the decision layer): the fold's first component IS `heightOf`. -/
theorem foldFn_height : ∀ t : Tree Int, heightFn t = heightOf t := by
  intro t
  induction t with
  | nil => rfl
  | node l a r ihl ihr =>
    show 1 + imax (heightFn l) (heightFn r) = 1 + imax (heightOf l) (heightOf r)
    rw [ihl, ihr]

/-- **Correctness of the allegory program**: `solveFn t = true ↔ IsBalanced t` — the DECISION
    shape (S5/S16), one extra `Nat` conjunct (the height test) beyond L100's `SameP` bridge. -/
theorem solve_correct : ∀ t : Tree Int, solveFn t = true ↔ IsBalanced t := by
  intro t
  induction t with
  | nil => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | node l a r ihl ihr =>
    show (solveFn l && solveFn r &&
        decide (imax (heightFn l) (heightFn r) - imin (heightFn l) (heightFn r) ≤ 1)) = true ↔
      IsBalanced l ∧ IsBalanced r ∧
        imax (heightOf l) (heightOf r) - imin (heightOf l) (heightOf r) ≤ 1
    rw [foldFn_height l, foldFn_height r, Bool.and_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, ihl, ihr, and_assoc]

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

example : solveFn (Tree.node (leaf 1) 2 (leaf 3)) = true := by decide
example : solveFn (Tree.node (Tree.node (leaf 1) 2 Tree.nil) 3 Tree.nil) = false := by decide
example : solveFn (leaf 5) = true := by decide
example : solveFn (Tree.nil : Tree Int) = true := by decide

end Freyd.Alg.RelSet.LC110
