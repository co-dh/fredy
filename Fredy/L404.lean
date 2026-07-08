/-
  LeetCode 404 — Sum of Left Leaves — as an ALLEGORY PROGRAM.

  Problem: given a binary tree, sum the values of all leaves that are a LEFT child of their
  parent.  A leaf is a node with BOTH children `nil` (`L112`'s convention); the tree's ROOT,
  even if it is itself a leaf, is NOT a left child and contributes nothing (LeetCode's own edge
  case: `sumLeftLeavesFn (leaf 5) = 0`).

  This is a fold over `Fredy.A6_TreeBin`'s `Tree`, with a NEW recursion shape relative to the
  Tree block so far: a Boolean flag `isLeft` — "is the CURRENT node a left child of its
  parent?" — is threaded DOWN the recursion (`L98`'s bounds-accumulator idiom, generalized from
  an `Option Int` pair to a single `Bool`), re-set at every node: a descent into a LEFT subtree
  always passes `true`, a descent into a RIGHT subtree always passes `false`, regardless of the
  flag the current node itself received — a leaf's left/right-ness is decided entirely by its
  IMMEDIATE parent, never by any ancestor further up.  Leaf-vs-non-leaf is matched by SHAPE
  (`L112`'s 5-way idiom: nil / leaf / left-only / right-only / both), so a one-child node is
  never mistaken for a leaf.

  1. **Data** — `Tree Int` (`Fredy.A6_TreeBin`).

  2. **Program** — `sumLL t isLeft`: `nil ↦ 0`; a genuine leaf `node nil a nil` contributes `a`
     iff `isLeft`; a non-leaf `node l a r` recurses `sumLL l true + sumLL r false`.
     `sumLeftLeavesFn t := sumLL t false` (the root has no parent, so it is not a left child).

  3. **Specification — two layers.** `leftLeafValues t isLeft : List Int` collects (in order)
     exactly the leaf values `sumLL t isLeft` would add up (`nil ↦ []`; leaf ↦ `[a]`/`[]` by
     `isLeft`; non-leaf ↦ `leftLeafValues l true ++ leftLeafValues r false`) — a
     DIFFERENT-looking (list-valued, not `Int`-valued) recursion, whose SUM is then proved to
     equal `sumLL` (`sumLL_eq_sum`).  On top of it, the inductive predicate `IsLeftLeaf t isLeft
     v` enumerates the TREE POSITIONS a value can come from (`leaf`; `goLeft`/`goRight`
     descending into a NON-`nil` child under a fixed flag, mirroring `L112`'s `PathSum`) — proved
     to characterize `leftLeafValues`'s membership EXACTLY (`mem_leftLeafValues_iff`), so the sum
     is honestly "sum of the left-leaf values", not a mere restatement of the fold.

  4. **Correctness** — `sum_left_leaves_correct : sumLeftLeavesFn t = (leftLeafValues t
     false).sum`, together with `mem_leftLeafValues_iff` (the containment fact that makes the sum
     honest: `leftLeafValues` contains a value iff `IsLeftLeaf` witnesses it at a genuine
     left-leaf position).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_TreeBin
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC404

open Freyd Freyd.Alg.RelSet.TB

/-! ## Object of `Int` answers in `Rel(Set)` -/

abbrev dInt : RelSet.{0} := ⟨Int⟩

/-! ## The program: a leaf-checking fold, a `Bool` "is-left-child" flag threaded DOWN,
    shape matched 5-way (`L112`'s idiom: nil / leaf / left-only / right-only / both) -/

/-- `sumLL t isLeft` — sum of the left-leaf values in `t`, given whether `t` ITSELF is currently
    sitting as a left child of its (unseen) parent.  `nil` contributes nothing; a genuine leaf
    (`node nil a nil`) contributes `a` iff `isLeft`; a non-leaf recurses into its LEFT child under
    flag `true` and its RIGHT child under flag `false` — the flag is reset at every node, since
    "is a left child" is decided solely by the immediate parent. -/
def sumLL : Tree Int → Bool → Int
  | Tree.nil, _ => 0
  | Tree.node Tree.nil a Tree.nil, isLeft => if isLeft then a else 0
  | Tree.node (Tree.node ll la lr) a Tree.nil, _ => sumLL (Tree.node ll la lr) true
  | Tree.node Tree.nil a (Tree.node rl ra rr), _ => sumLL (Tree.node rl ra rr) false
  | Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr), _ =>
      sumLL (Tree.node ll la lr) true + sumLL (Tree.node rl ra rr) false

@[simp] theorem sumLL_nil (isLeft : Bool) : sumLL Tree.nil isLeft = 0 := rfl
@[simp] theorem sumLL_leaf (a : Int) (isLeft : Bool) :
    sumLL (Tree.node Tree.nil a Tree.nil) isLeft = if isLeft then a else 0 := rfl
@[simp] theorem sumLL_left_only (ll lr : Tree Int) (la a : Int) (isLeft : Bool) :
    sumLL (Tree.node (Tree.node ll la lr) a Tree.nil) isLeft =
      sumLL (Tree.node ll la lr) true := rfl
@[simp] theorem sumLL_right_only (rl rr : Tree Int) (ra a : Int) (isLeft : Bool) :
    sumLL (Tree.node Tree.nil a (Tree.node rl ra rr)) isLeft =
      sumLL (Tree.node rl ra rr) false := rfl
@[simp] theorem sumLL_both (ll lr rl rr : Tree Int) (la ra a : Int) (isLeft : Bool) :
    sumLL (Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr)) isLeft =
      sumLL (Tree.node ll la lr) true + sumLL (Tree.node rl ra rr) false := rfl

/-- The decision: sum of the LEFT-leaf values of `t`.  The root is not a left child, so it starts
    the fold with `isLeft := false`. -/
def sumLeftLeavesFn (t : Tree Int) : Int := sumLL t false

/-- **The allegory program**: LeetCode 404's solution as a morphism `dTree Int ⟶ ℤ` in
    `Rel(Set)`. -/
def solve : dTree Int ⟶ dInt := graph sumLeftLeavesFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map sumLeftLeavesFn

/-! ## Specification, layer 1: the list of contributing leaf values -/

/-- `leftLeafValues t isLeft` — the list of leaf values `sumLL t isLeft` sums, IN ORDER: `nil ↦
    []`; a genuine leaf contributes `[a]`/`[]` by `isLeft`; a non-leaf concatenates its left
    subtree's list (flag `true`) with its right subtree's list (flag `false`).  Deliberately
    LIST-valued (not `Int`-valued) so its equality with `sumLL`'s running total is genuine content,
    not a syntactic restatement. -/
def leftLeafValues : Tree Int → Bool → List Int
  | Tree.nil, _ => []
  | Tree.node Tree.nil a Tree.nil, isLeft => if isLeft then [a] else []
  | Tree.node (Tree.node ll la lr) a Tree.nil, _ => leftLeafValues (Tree.node ll la lr) true
  | Tree.node Tree.nil a (Tree.node rl ra rr), _ => leftLeafValues (Tree.node rl ra rr) false
  | Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr), _ =>
      leftLeafValues (Tree.node ll la lr) true ++ leftLeafValues (Tree.node rl ra rr) false

@[simp] theorem leftLeafValues_nil (isLeft : Bool) : leftLeafValues Tree.nil isLeft = [] := rfl
@[simp] theorem leftLeafValues_leaf (a : Int) (isLeft : Bool) :
    leftLeafValues (Tree.node Tree.nil a Tree.nil) isLeft = if isLeft then [a] else [] := rfl
@[simp] theorem leftLeafValues_left_only (ll lr : Tree Int) (la a : Int) (isLeft : Bool) :
    leftLeafValues (Tree.node (Tree.node ll la lr) a Tree.nil) isLeft =
      leftLeafValues (Tree.node ll la lr) true := rfl
@[simp] theorem leftLeafValues_right_only (rl rr : Tree Int) (ra a : Int) (isLeft : Bool) :
    leftLeafValues (Tree.node Tree.nil a (Tree.node rl ra rr)) isLeft =
      leftLeafValues (Tree.node rl ra rr) false := rfl
@[simp] theorem leftLeafValues_both (ll lr rl rr : Tree Int) (la ra a : Int) (isLeft : Bool) :
    leftLeafValues (Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr)) isLeft =
      leftLeafValues (Tree.node ll la lr) true ++ leftLeafValues (Tree.node rl ra rr) false := rfl

/-! ## Specification, layer 2: which tree positions a left-leaf value comes from -/

/-- `IsLeftLeaf t isLeft v` — `t`, seen under the inherited flag `isLeft`, has a left-leaf at
    value `v`: either `t` itself is a leaf and `isLeft` (`leaf`), or `v` comes from a NON-`nil`
    child, recursed into under that child's own fixed flag (`goLeft`/`goRight`) — the honest
    "enumerate the witnessing positions" mirror of `L112`'s `PathSum`. -/
inductive IsLeftLeaf : Tree Int → Bool → Int → Prop where
  | leaf (a : Int) : IsLeftLeaf (Tree.node Tree.nil a Tree.nil) true a
  | goLeft {l r : Tree Int} {a v : Int} {isLeft : Bool} (hl : l ≠ Tree.nil)
      (h : IsLeftLeaf l true v) : IsLeftLeaf (Tree.node l a r) isLeft v
  | goRight {l r : Tree Int} {a v : Int} {isLeft : Bool} (hr : r ≠ Tree.nil)
      (h : IsLeftLeaf r false v) : IsLeftLeaf (Tree.node l a r) isLeft v

/-- A `node` is never `nil` — the two `Tree` constructors are distinct (`L112`). -/
theorem node_ne_nil (l r : Tree Int) (a : Int) : Tree.node l a r ≠ Tree.nil := fun h => nomatch h

/-! ## Mathlib-free `Int` list-sum append lemma (Lean core only proves `sum_append` for
    `List Nat`; hand-rolled as in `L303`) -/

theorem sum_append_int (l1 l2 : List Int) : (l1 ++ l2).sum = l1.sum + l2.sum := by
  induction l1 with
  | nil => simp
  | cons x xs ih => rw [List.cons_append, List.sum_cons, List.sum_cons, ih, Int.add_assoc]

/-! ## Correctness -/

/-- **`sumLL` equals the sum of `leftLeafValues`**, by structural recursion mirroring `sumLL`'s
    own 5-way case split. -/
theorem sumLL_eq_sum :
    ∀ (t : Tree Int) (isLeft : Bool), sumLL t isLeft = (leftLeafValues t isLeft).sum
  | Tree.nil, isLeft => by rw [sumLL_nil, leftLeafValues_nil]; simp
  | Tree.node Tree.nil a Tree.nil, isLeft => by
      rw [sumLL_leaf, leftLeafValues_leaf]; cases isLeft <;> simp
  | Tree.node (Tree.node ll la lr) a Tree.nil, isLeft => by
      rw [sumLL_left_only, leftLeafValues_left_only]
      exact sumLL_eq_sum (Tree.node ll la lr) true
  | Tree.node Tree.nil a (Tree.node rl ra rr), isLeft => by
      rw [sumLL_right_only, leftLeafValues_right_only]
      exact sumLL_eq_sum (Tree.node rl ra rr) false
  | Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr), isLeft => by
      rw [sumLL_both, leftLeafValues_both, sum_append_int,
          sumLL_eq_sum (Tree.node ll la lr) true, sumLL_eq_sum (Tree.node rl ra rr) false]

/-- **`leftLeafValues` membership is EXACTLY `IsLeftLeaf`** — the honesty lemma: the list built by
    the program's own recursion contains a value iff that value genuinely sits at a witnessed
    left-leaf position.  Proved by structural recursion mirroring `leftLeafValues`'s own 5-way
    case split (the `L112` idiom): at every non-leaf shape the `leaf` constructor is excluded by
    Lean's own unification (its indices don't match a non-`(nil,nil)` child pair), and the
    `nil`-child side of `goLeft`/`goRight` is excluded by the explicit `hl`/`hr : _ ≠ Tree.nil`
    field. -/
theorem mem_leftLeafValues_iff :
    ∀ (t : Tree Int) (isLeft : Bool) (v : Int),
      v ∈ leftLeafValues t isLeft ↔ IsLeftLeaf t isLeft v
  | Tree.nil, isLeft, v => by
      rw [leftLeafValues_nil]
      exact ⟨fun h => (List.not_mem_nil h).elim, fun h => nomatch h⟩
  | Tree.node Tree.nil a Tree.nil, isLeft, v => by
      rw [leftLeafValues_leaf]
      cases isLeft with
      | true =>
        simp only [if_true]
        constructor
        · intro h
          have hv : v = a := List.mem_singleton.mp h
          rw [hv]; exact IsLeftLeaf.leaf a
        · intro h
          cases h with
          | leaf => simp
          | goLeft hl _ => exact absurd rfl hl
          | goRight hr _ => exact absurd rfl hr
      | false =>
        constructor
        · intro h; exact (List.not_mem_nil h).elim
        · intro h
          cases h with
          | goLeft hl _ => exact absurd rfl hl
          | goRight hr _ => exact absurd rfl hr
  | Tree.node (Tree.node ll la lr) a Tree.nil, isLeft, v => by
      rw [leftLeafValues_left_only]
      have ih := mem_leftLeafValues_iff (Tree.node ll la lr) true v
      constructor
      · intro h; exact IsLeftLeaf.goLeft (node_ne_nil ll lr la) (ih.mp h)
      · intro h
        cases h with
        | goLeft _ hh => exact ih.mpr hh
        | goRight hr _ => exact absurd rfl hr
  | Tree.node Tree.nil a (Tree.node rl ra rr), isLeft, v => by
      rw [leftLeafValues_right_only]
      have ih := mem_leftLeafValues_iff (Tree.node rl ra rr) false v
      constructor
      · intro h; exact IsLeftLeaf.goRight (node_ne_nil rl rr ra) (ih.mp h)
      · intro h
        cases h with
        | goLeft hl _ => exact absurd rfl hl
        | goRight _ hh => exact ih.mpr hh
  | Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr), isLeft, v => by
      rw [leftLeafValues_both, List.mem_append]
      have ihl := mem_leftLeafValues_iff (Tree.node ll la lr) true v
      have ihr := mem_leftLeafValues_iff (Tree.node rl ra rr) false v
      constructor
      · rintro (h | h)
        · exact IsLeftLeaf.goLeft (node_ne_nil ll lr la) (ihl.mp h)
        · exact IsLeftLeaf.goRight (node_ne_nil rl rr ra) (ihr.mp h)
      · intro h
        cases h with
        | goLeft _ hh => exact Or.inl (ihl.mpr hh)
        | goRight _ hh => exact Or.inr (ihr.mpr hh)

/-- **Correctness of the allegory program**: the sum of left-leaf values, read off the program's
    running total, equals the sum of `leftLeafValues t false` — combined with
    `mem_leftLeafValues_iff` above, this is genuinely "sum of the values at left-leaf positions",
    not a restatement of the fold. -/
theorem sum_left_leaves_correct (t : Tree Int) :
    sumLeftLeavesFn t = (leftLeafValues t false).sum :=
  sumLL_eq_sum t false

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

-- LeetCode's own example: root 3, left child 9 (a leaf), right child 20 with children 15, 7.
-- Left leaves: 9 (left child of 3) and 15 (left child of 20); 7 is a RIGHT leaf, excluded.
example :
    sumLeftLeavesFn (Tree.node (leaf 9) 3 (Tree.node (leaf 15) 20 (leaf 7))) = 24 := by decide

-- Lone root: a leaf, but not a LEFT child of anything (it has no parent) — contributes 0.
example : sumLeftLeavesFn (leaf (5 : Int)) = 0 := by decide

end Freyd.Alg.RelSet.LC404
