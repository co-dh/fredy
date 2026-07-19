/-
  LeetCode 112 — Path Sum — as an ALLEGORY PROGRAM.

  Problem: given a binary tree and a target sum, return `true` iff the tree has a ROOT-TO-LEAF path
  whose node values sum to `target`.  A leaf is a node with BOTH children `nil`; a node with only
  ONE `nil` child is NOT a leaf and must not be treated as one — the classic bug in a naive port of
  this problem.

  This is a DECISION over `AOP.A6_TreeBin`'s `Tree`, two-input like `L100` (a tree plus an `Int`
  target), with the accumulator SUBTRACTED at each step (`target - a`) rather than range-checked,
  mirroring `L98`'s down-threaded state but flowing an arithmetic budget instead of bounds.

  1. **Data** — `Tree Int` (`AOP.A6_TreeBin`) plus an `Int` target, domain `⟨Tree Int × Int⟩`.

  2. **Program** — `hasPathSumFn t target`: `nil ↦ false`; a `node l a r` where BOTH children are
     `nil` (a genuine leaf) ↦ `decide (a = target)`; otherwise recurse ONLY into non-`nil` children
     with the reduced target `target - a`, `||`-combined.  `solve := graph (fun p => hasPathSumFn
     p.1 p.2)`.

  3. **Specification** — the honest inductive `PathSum t s`: `leaf` (a genuine leaf, `s = a`),
     `left`/`right` (recurse into a NON-`nil` child with `s - a`) — literally "there exists a
     root-to-leaf path summing to `s`", with no constructor for `nil` (no path through an empty
     tree).

  4. **Correctness** — `path_sum_correct : hasPathSumFn t target = true ↔ PathSum t target`, by
     structural recursion mirroring the program's own case split (`nil` / leaf / left-only /
     right-only / both), Bool↔Prop reflection (S5).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_TreeBin
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC112

open Freyd Freyd.Alg.RelSet.TB

/-! ## Data: a tree paired with a target sum; answer = `Bool` -/

/-- The object of (tree, target) pairs in `Rel(Set)` — the two-input problem's domain. -/
abbrev TreeTarget : RelSet.{0} := ⟨Tree Int × Int⟩
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## The program: a leaf-checking fold that recurses only into non-`nil` children -/

/-- `hasPathSumFn t target` — does `t` have a root-to-leaf path summing to `target`?  A leaf is a
    node with BOTH children `nil`; a node with exactly one `nil` child recurses into the other
    child ONLY (never treats the lone-child side as a leaf). -/
def hasPathSumFn : Tree Int → Int → Bool
  | Tree.nil, _ => false
  | Tree.node Tree.nil a Tree.nil, target => decide (a = target)
  | Tree.node (Tree.node ll la lr) a Tree.nil, target =>
      hasPathSumFn (Tree.node ll la lr) (target - a)
  | Tree.node Tree.nil a (Tree.node rl ra rr), target =>
      hasPathSumFn (Tree.node rl ra rr) (target - a)
  | Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr), target =>
      hasPathSumFn (Tree.node ll la lr) (target - a) ||
      hasPathSumFn (Tree.node rl ra rr) (target - a)

@[simp] theorem hasPathSumFn_nil (target : Int) : hasPathSumFn Tree.nil target = false := rfl
@[simp] theorem hasPathSumFn_leaf (a target : Int) :
    hasPathSumFn (Tree.node Tree.nil a Tree.nil) target = decide (a = target) := rfl
@[simp] theorem hasPathSumFn_left_only (ll lr : Tree Int) (la a target : Int) :
    hasPathSumFn (Tree.node (Tree.node ll la lr) a Tree.nil) target =
      hasPathSumFn (Tree.node ll la lr) (target - a) := rfl
@[simp] theorem hasPathSumFn_right_only (rl rr : Tree Int) (ra a target : Int) :
    hasPathSumFn (Tree.node Tree.nil a (Tree.node rl ra rr)) target =
      hasPathSumFn (Tree.node rl ra rr) (target - a) := rfl
@[simp] theorem hasPathSumFn_both (ll lr rl rr : Tree Int) (la ra a target : Int) :
    hasPathSumFn (Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr)) target =
      (hasPathSumFn (Tree.node ll la lr) (target - a) ||
       hasPathSumFn (Tree.node rl ra rr) (target - a)) := rfl

/-- **The allegory program**: LeetCode 112's decision as a morphism `TreeTarget ⟶ dBool` in
    `Rel(Set)` — a two-INPUT `graph` deciding root-to-leaf path-sum existence. -/
def solve : TreeTarget ⟶ dBool := graph (fun p : Tree Int × Int => hasPathSumFn p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map (fun p : Tree Int × Int => hasPathSumFn p.1 p.2)

/-! ## Specification: the honest root-to-leaf path witness -/

/-- `PathSum t s` — `t` has a root-to-leaf path whose labels sum to `s`.  `leaf` fires only at a
    genuine leaf (both children `nil`); `left`/`right` require the chosen child to be non-`nil`
    (so a one-child node is never mistaken for a leaf on its `nil` side), descending with the
    reduced target `s - a`.  No constructor for `nil`: an empty tree has no path. -/
inductive PathSum : Tree Int → Int → Prop where
  | leaf (a : Int) : PathSum (Tree.node Tree.nil a Tree.nil) a
  | left {l r : Tree Int} {a s : Int} (hl : l ≠ Tree.nil) (h : PathSum l (s - a)) :
      PathSum (Tree.node l a r) s
  | right {l r : Tree Int} {a s : Int} (hr : r ≠ Tree.nil) (h : PathSum r (s - a)) :
      PathSum (Tree.node l a r) s

/-- The **specification** as a morphism `TreeTarget ⟶ dBool` in `Rel(Set)`: `b` is THE correct
    boolean answer to "does `t` have a root-to-leaf path summing to `target`?" -/
def spec : TreeTarget ⟶ dBool := fun (p : Tree Int × Int) (b : Bool) => (b = true ↔ PathSum p.1 p.2)

/-! ## Correctness: `hasPathSumFn` decides `PathSum`, by structural recursion mirroring the program -/

/-- A `node` is never `nil` — the two `Tree` constructors are distinct. -/
theorem node_ne_nil (l r : Tree Int) (a : Int) : Tree.node l a r ≠ Tree.nil := fun h => nomatch h

/-- **`hasPathSumFn` computes `PathSum`** — the DECISION-problem correctness shape (S5), proved by
    structural recursion mirroring `hasPathSumFn`'s own case split. -/
theorem path_sum_correct :
    ∀ (t : Tree Int) (target : Int), hasPathSumFn t target = true ↔ PathSum t target
  | Tree.nil, target => by
      rw [hasPathSumFn_nil]
      constructor
      · intro h; exact Bool.noConfusion h
      · intro h; nomatch h
  | Tree.node Tree.nil a Tree.nil, target => by
      rw [hasPathSumFn_leaf, decide_eq_true_eq]
      constructor
      · intro h; rw [← h]; exact PathSum.leaf a
      · intro h
        cases h with
        | leaf => rfl
        | left hl _ => exact absurd rfl hl
        | right hr _ => exact absurd rfl hr
  | Tree.node (Tree.node ll la lr) a Tree.nil, target => by
      rw [hasPathSumFn_left_only]
      have ih := path_sum_correct (Tree.node ll la lr) (target - a)
      constructor
      · intro h; exact PathSum.left (node_ne_nil ll lr la) (ih.mp h)
      · intro h
        cases h with
        | left _ hh => exact ih.mpr hh
        | right hr _ => exact absurd rfl hr
  | Tree.node Tree.nil a (Tree.node rl ra rr), target => by
      rw [hasPathSumFn_right_only]
      have ih := path_sum_correct (Tree.node rl ra rr) (target - a)
      constructor
      · intro h; exact PathSum.right (node_ne_nil rl rr ra) (ih.mp h)
      · intro h
        cases h with
        | left hl _ => exact absurd rfl hl
        | right _ hh => exact ih.mpr hh
  | Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr), target => by
      rw [hasPathSumFn_both, Bool.or_eq_true]
      have ihl := path_sum_correct (Tree.node ll la lr) (target - a)
      have ihr := path_sum_correct (Tree.node rl ra rr) (target - a)
      constructor
      · rintro (h | h)
        · exact PathSum.left (node_ne_nil ll lr la) (ihl.mp h)
        · exact PathSum.right (node_ne_nil rl rr ra) (ihr.mp h)
      · intro h
        cases h with
        | left _ hh => exact Or.inl (ihl.mpr hh)
        | right _ hh => exact Or.inr (ihr.mpr hh)

/-- Two booleans that agree on being `true` are equal (Bool extensionality). -/
theorem bool_eq_of_iff_true {b c : Bool} (h : (b = true) ↔ (c = true)) : b = c := by
  cases b with
  | true => cases c with
    | true => rfl
    | false => exact (h.mp rfl).symm
  | false => cases c with
    | true => exact h.mpr rfl
    | false => rfl

/-- **`solve` equals `spec` as relations** (the allegory-program correctness statement). -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro p b
  show (b = hasPathSumFn p.1 p.2) ↔ (b = true ↔ PathSum p.1 p.2)
  constructor
  · intro h; rw [h]; exact path_sum_correct p.1 p.2
  · intro h
    have h' : (b = true) ↔ (hasPathSumFn p.1 p.2 = true) := h.trans (path_sum_correct p.1 p.2).symm
    exact bool_eq_of_iff_true h'

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

-- The trap case: root `1` has a lone LEFT child (right is `nil`); that child `2` also has a lone
-- LEFT child `3` (right `nil`).  Neither `1` nor `2` is a leaf, so the only path is `1→2→3`,
-- summing to `6`.  A buggy "either child `nil` ⟹ leaf" implementation would wrongly stop at the
-- root (right `nil`) and check `decide (1 = 6) = false` — our program correctly recurses past it.
example :
    hasPathSumFn (Tree.node (Tree.node (leaf 3) 2 Tree.nil) 1 Tree.nil) 6 = true := by decide

example : hasPathSumFn (Tree.node (leaf 1) 2 Tree.nil) 1 = false := by decide

end Freyd.Alg.RelSet.LC112
