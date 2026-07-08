/-
  LeetCode 102 — Binary Tree Level Order Traversal — as an ALLEGORY PROGRAM (level-merging cata).

  Problem: return the BFS level-order traversal of a binary tree: a `List (List Int)` whose `d`-th
  entry lists the values at depth `d`, left to right. `nil ↦ []`.

  No queue needed — this is a plain tree catamorphism (`Fredy.A6_TreeBin`) whose fold state IS the
  answer (state-is-answer, like `L104`/`L226`, contrast `L121`'s trailing projection):

  1. **Program.** `levels nil = []`, `levels (node l a r) = [a] :: mergeLevels (levels l) (levels
     r)`, where `mergeLevels` zips two level-lists depth-by-depth, concatenating same-depth rows and
     keeping the longer tail verbatim once the shorter side runs out.

  2. **Specification.** `atDepth t d` — the values at depth `d` in `t`, defined by structural
     recursion INDEPENDENT of `levels`/`mergeLevels` (an honest spec, not a restatement of the
     program). `rowAt L d` reads list `L`'s `d`-th row, defaulting to `[]` past the end — the same
     "out-of-range ↦ []" convention `atDepth` uses past a tree's height, so the two line up on
     EVERY `d`, not just in-range ones.

  3. **Correctness.** `levels_row_eq_atDepth : ∀ t d, rowAt (levels t) d = atDepth t d` — ONE
     universally-quantified equation that simultaneously pins every in-range output row to
     `atDepth` AND forces `atDepth` to vanish past the output's length (both directions fall out of
     the SAME statement, since `rowAt` already returns `[]` out of range). The crux is
     `mergeLevels`'s own row law, `mergeLevels_row : ∀ A B d, rowAt (mergeLevels A B) d = rowAt A d
     ++ rowAt B d`, proved by recursion mirroring `mergeLevels`'s three clauses; the tree induction's
     `node` case then reduces to: row `0` is `[a] = atDepth (node …) 0`, row `d+1` is
     `mergeLevels`'s row `d` = `atDepth l d ++ atDepth r d = atDepth (node …) (d+1)` by the two IHs.
     A companion law, `mergeLevels_length`/`levels_length_eq_height`, pins the OUTPUT LENGTH to the
     tree's height (number of nonempty levels), the fact `rowAt`'s per-row equation alone doesn't
     state.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_TreeBin
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC102

open Freyd Freyd.Alg.RelSet.TB

/-! ## Mathlib-free `Nat` `max` (copied from `L104`, control the rewrite set) -/

def imax (a b : Nat) : Nat := if a ≤ b then b else a

theorem imax_ge_left  (a b : Nat) : a ≤ imax a b := by unfold imax; split <;> omega
theorem imax_ge_right (a b : Nat) : b ≤ imax a b := by unfold imax; split <;> omega
theorem imax_eq_or (a b : Nat) : imax a b = a ∨ imax a b = b := by
  unfold imax; split; exacts [Or.inr rfl, Or.inl rfl]

/-- `imax` commutes with `+1` on both sides — the arithmetic engine behind `mergeLevels_length`. -/
theorem imax_succ (m n : Nat) : imax (m + 1) (n + 1) = imax m n + 1 := by
  unfold imax; split <;> split <;> omega

/-! ## Data/answer objects in `Rel(Set)` -/

/-- The answer object: level-by-level lists of node values. -/
abbrev dAns : RelSet.{0} := ⟨List (List Int)⟩

/-! ## `mergeLevels` — zip two level-lists depth-by-depth -/

/-- Merge two level-lists row-by-row: same-depth rows concatenate, the longer tail passes through
    once the shorter side is exhausted. -/
def mergeLevels : List (List Int) → List (List Int) → List (List Int)
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x ++ y) :: mergeLevels xs ys

/-! ## The program: the level fold `[ nil ↦ [],  (l,a,r) ↦ [a] :: mergeLevels l r ]` -/

/-- The concrete fold (structural recursion): level-order traversal, grouped by depth. -/
def levels : Tree Int → List (List Int)
  | Tree.nil => []
  | Tree.node l a r => [a] :: mergeLevels (levels l) (levels r)

/-- **The allegory program**: LeetCode 102's solution as a morphism `dTree ℤ ⟶ dAns` in
    `Rel(Set)` — a structural-output fold whose state already IS the answer (no projection). -/
def solve : dTree Int ⟶ dAns := graph levels

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map levels

/-! ## Specification: the values at a given depth, and reading a row out of a level-list -/

/-- `atDepth t d` — the values at depth `d` in `t`, left to right (`[]` past `t`'s height). -/
def atDepth : Tree Int → Nat → List Int
  | Tree.nil, _ => []
  | Tree.node _ a _, 0 => [a]
  | Tree.node l _ r, d + 1 => atDepth l d ++ atDepth r d

/-- `height t` — the number of nonempty levels of `t` (`0` for `nil`). -/
def height : Tree Int → Nat
  | Tree.nil => 0
  | Tree.node l _ r => 1 + imax (height l) (height r)

/-- `rowAt L d` — the `d`-th row of a level-list, defaulting to `[]` past the end (the SAME
    "out-of-range ↦ []" convention as `atDepth` past a tree's height). -/
def rowAt : List (List Int) → Nat → List Int
  | [], _ => []
  | x :: _, 0 => x
  | _ :: xs, d + 1 => rowAt xs d

/-! ## Crux: `mergeLevels`'s row law and length law -/

/-- **`mergeLevels`'s row law**: row `d` of the merge is the concatenation of row `d` of each side
    (with the out-of-range side contributing `[]`), for EVERY `d` — proved by recursion mirroring
    `mergeLevels`'s own three clauses. -/
theorem mergeLevels_row : ∀ (A B : List (List Int)) (d : Nat),
    rowAt (mergeLevels A B) d = rowAt A d ++ rowAt B d
  | [], B, d => by simp [mergeLevels, rowAt]
  | x :: xs, [], d => by simp [mergeLevels, rowAt]
  | x :: xs, y :: ys, 0 => by simp [mergeLevels, rowAt]
  | x :: xs, y :: ys, d + 1 => by
      show rowAt (mergeLevels xs ys) d = rowAt xs d ++ rowAt ys d
      exact mergeLevels_row xs ys d

/-- **`mergeLevels`'s length law**: the merge has as many rows as the longer side. -/
theorem mergeLevels_length : ∀ (A B : List (List Int)),
    (mergeLevels A B).length = imax A.length B.length
  | [], B => by
      show B.length = imax 0 B.length
      unfold imax; split <;> omega
  | x :: xs, [] => by
      show (x :: xs).length = imax (x :: xs).length 0
      unfold imax; split <;> omega
  | x :: xs, y :: ys => by
      have ih := mergeLevels_length xs ys
      show (mergeLevels xs ys).length + 1 = imax (x :: xs).length (y :: ys).length
      have hlen : (x :: xs).length = xs.length + 1 := rfl
      have hlen' : (y :: ys).length = ys.length + 1 := rfl
      rw [hlen, hlen', ih, imax_succ]

/-! ## Correctness: `levels` computes exactly `atDepth` at every depth, and its length is the
    tree's height -/

/-- **Headline (row correctness)**: the `d`-th row of `levels t` is EXACTLY `atDepth t d`, for
    EVERY `d` — simultaneously pinning every in-range output row to the honest depth-`d` spec, and
    (out of range) forcing `atDepth` to vanish past the output's length. -/
theorem levels_row_eq_atDepth : ∀ (t : Tree Int) (d : Nat), rowAt (levels t) d = atDepth t d
  | Tree.nil, d => by simp [levels, atDepth, rowAt]
  | Tree.node l a r, 0 => by simp [levels, atDepth, rowAt]
  | Tree.node l a r, d + 1 => by
      show rowAt (mergeLevels (levels l) (levels r)) d = atDepth l d ++ atDepth r d
      rw [mergeLevels_row, levels_row_eq_atDepth l d, levels_row_eq_atDepth r d]

/-- **Headline (length correctness)**: `levels t` has exactly `height t` rows — the number of
    nonempty depths. -/
theorem levels_length_eq_height : ∀ t : Tree Int, (levels t).length = height t
  | Tree.nil => rfl
  | Tree.node l a r => by
      show ([a] :: mergeLevels (levels l) (levels r)).length = 1 + imax (height l) (height r)
      have hlen : ([a] :: mergeLevels (levels l) (levels r)).length
          = (mergeLevels (levels l) (levels r)).length + 1 := rfl
      rw [hlen, mergeLevels_length, levels_length_eq_height l, levels_length_eq_height r]
      omega

/-- **Correctness of the allegory program**: `levels t`'s `d`-th row is `atDepth t d` for every
    `d`, and `levels t` has exactly `height t` rows — together these pin `levels` to LeetCode 102's
    spec (the level-by-level grouping of node values) on the nose. -/
theorem solve_correct (t : Tree Int) :
    (∀ d, rowAt (levels t) d = atDepth t d) ∧ (levels t).length = height t :=
  ⟨levels_row_eq_atDepth t, levels_length_eq_height t⟩

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil
/-- A balanced height-2 tree: root `a` with leaf children `b`, `c`. -/
def bal (a b c : Int) : Tree Int := Tree.node (leaf b) a (leaf c)

/-- An UNBALANCED tree — `1` at the root, `2`/`3` its children, `4` hanging off `2` — exercises
    `mergeLevels`'s unequal-length branch (row `[4]` has no partner on the right). -/
def unbal : Tree Int := Tree.node (Tree.node (leaf 4) 2 Tree.nil) 1 (leaf 3)

example : levels (Tree.nil : Tree Int) = [] := by decide
example : levels (bal (1 : Int) 2 3) = [[1], [2, 3]] := by decide
example : levels unbal = [[1], [2, 3], [4]] := by decide

end Freyd.Alg.RelSet.LC102
