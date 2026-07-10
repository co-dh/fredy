/-
  LeetCode 572 — Subtree of Another Tree — as an ALLEGORY PROGRAM.

  Problem: given two binary trees `s` and `t`, return `true` iff `t` occurs as the subtree rooted
  at some node of `s` (structurally identical, labels included).

  A DECISION problem (`leet/L217.lean`'s S5 shape, `spec`-free `iff` version), but with a NEW
  twist: the program is a fold that at every node calls a SECOND, independent fold
  (`sameFn`, a per-node structural-equality check) and combines it with recursion into the
  children — a nested-relation composition, not a single flat scan:

  1. **Data** — `Tree Int` (`AOP.A6_TreeBin`), the initial algebra of `F X = 1 + X×A×X`.

  2. **Program** — `sameFn t t'` (Bool "are `t`, `t'` structurally identical?", itself a fold over
     BOTH trees in lockstep) and `subFn s t` (Bool "is `t` a subtree of `s`?"; the `node` case
     checks `sameFn (node l a r) t || subFn l t || subFn r t` — either `t` matches right here, or
     `t` is a subtree of the left child, or of the right child). `solve := graph (fun p => subFn
     p.1 p.2) : ⟨Tree Int × Tree Int⟩ ⟶ ⟨Bool⟩` is the allegory program (`(s, t) ↦ subFn s t`).

  3. **Specification** — `SameP` (Prop mirror of `sameFn`: structural tree equality) and
     `IsSubtree s t` (Prop mirror of `subFn`: some node of `s` roots a `SameP`-copy of `t`),
     defined structurally in lockstep with the Bool folds.

  4. **Correctness** — a same-tree bridge `same_correct : sameFn t t' = true ↔ SameP t t'`
     (double induction, lockstep on both trees), then `solve_correct s t : subFn s t = true ↔
     IsSubtree s t` (induction on `s` alone, `t` universally quantified; the `node` case composes
     the bridge at the current node with the two recursive IHs via `Bool.or_eq_true`).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_TreeBin
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC572

open Freyd Freyd.Alg.RelSet.TB

/-! ## Data: trees of `Int`; answer = `Bool` -/

/-- The object of `(s, t)` tree pairs in `Rel(Set)`. -/
abbrev dTreePair : RelSet.{0} := ⟨Tree Int × Tree Int⟩
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## The program: a per-node same-tree check, then a subtree-search fold that calls it -/

/-- `sameFn t t'` — are `t` and `t'` structurally identical (same shape, same labels)? A fold in
    LOCKSTEP over both trees. -/
def sameFn : Tree Int → Tree Int → Bool
  | Tree.nil, Tree.nil => true
  | Tree.node l a r, Tree.node l' a' r' => decide (a = a') && sameFn l l' && sameFn r r'
  | _, _ => false

/-- `subFn s t` — is `t` a subtree of `s` (rooted at some node of `s`)? A fold over `s` that at
    every node calls the independent fold `sameFn`. -/
def subFn : Tree Int → Tree Int → Bool
  | Tree.nil, t => sameFn Tree.nil t
  | Tree.node l a r, t => sameFn (Tree.node l a r) t || subFn l t || subFn r t

/-- The answer function: `(s, t) ↦` is `t` a subtree of `s`?. -/
def solveFn (p : Tree Int × Tree Int) : Bool := subFn p.1 p.2

/-- **The allegory program**: LeetCode 572's solution as a morphism `dTreePair ⟶ dBool` in
    `Rel(Set)`. -/
def solve : dTreePair ⟶ dBool := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## Specification: structural tree equality, and "is a subtree of" -/

/-- `SameP t t'` — the Prop mirror of `sameFn`: `t` and `t'` are structurally identical. -/
def SameP : Tree Int → Tree Int → Prop
  | Tree.nil, Tree.nil => True
  | Tree.node l a r, Tree.node l' a' r' => a = a' ∧ SameP l l' ∧ SameP r r'
  | _, _ => False

/-- `IsSubtree s t` — the Prop mirror of `subFn`: some node of `s` roots a `SameP`-copy of `t`. -/
def IsSubtree : Tree Int → Tree Int → Prop
  | Tree.nil, t => SameP Tree.nil t
  | Tree.node l a r, t => SameP (Tree.node l a r) t ∨ IsSubtree l t ∨ IsSubtree r t

/-- The **specification** as a morphism `dTreePair ⟶ dBool` in `Rel(Set)`: `b` is THE correct
    boolean answer to "is `t` a subtree of `s`?" -/
def spec : dTreePair ⟶ dBool := fun p b => (b = true ↔ IsSubtree p.1 p.2)

/-! ## Bridge: the boolean same-tree fold reflects the Prop relation -/

/-- **The bridge lemma**: `sameFn` computes `SameP`. -/
theorem same_correct : ∀ t t' : Tree Int, sameFn t t' = true ↔ SameP t t' := by
  intro t
  induction t with
  | nil =>
    intro t'
    cases t' with
    | nil =>
      show (true : Bool) = true ↔ True
      exact ⟨fun _ => trivial, fun _ => rfl⟩
    | node l' a' r' =>
      show (false : Bool) = true ↔ False
      exact ⟨fun h => (nomatch h), False.elim⟩
  | node l a r ihl ihr =>
    intro t'
    cases t' with
    | nil =>
      show (false : Bool) = true ↔ False
      exact ⟨fun h => (nomatch h), False.elim⟩
    | node l' a' r' =>
      show (decide (a = a') && sameFn l l' && sameFn r r') = true ↔
        (a = a' ∧ SameP l l' ∧ SameP r r')
      constructor
      · intro h
        rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨h.1.1, (ihl l').mp h.1.2, (ihr r').mp h.2⟩
      · intro h
        rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        obtain ⟨ha, hl, hr⟩ := h
        exact ⟨⟨ha, (ihl l').mpr hl⟩, (ihr r').mpr hr⟩

/-! ## Correctness: `solve` decides `IsSubtree` -/

/-- **`subFn` computes `IsSubtree`**: the DECISION-problem correctness shape — an `iff`, not an
    extremum; the `node` case composes the same-tree bridge (checked HERE) with the two
    recursive subtree searches (checked in the CHILDREN). -/
theorem solve_correct : ∀ s t : Tree Int, subFn s t = true ↔ IsSubtree s t := by
  intro s
  induction s with
  | nil =>
    intro t
    show sameFn Tree.nil t = true ↔ SameP Tree.nil t
    exact same_correct Tree.nil t
  | node l a r ihl ihr =>
    intro t
    show (sameFn (Tree.node l a r) t || subFn l t || subFn r t) = true ↔
      (SameP (Tree.node l a r) t ∨ IsSubtree l t ∨ IsSubtree r t)
    rw [Bool.or_eq_true, Bool.or_eq_true, same_correct (Tree.node l a r) t, ihl t, ihr t, or_assoc]

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
  show (b = solveFn p) ↔ (b = true ↔ IsSubtree p.1 p.2)
  constructor
  · intro h; rw [h]; exact solve_correct p.1 p.2
  · intro h
    have h' : (b = true) ↔ (solveFn p = true) := h.trans (solve_correct p.1 p.2).symm
    exact bool_eq_of_iff_true h'

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

/-- `s = node(leaf 1, 2, node(leaf 4, 5, leaf 6))`, `t = node(leaf 4, 5, leaf 6)` — `t` occurs as
    `s`'s right subtree. -/
example : subFn (Tree.node (leaf 1) 2 (Tree.node (leaf 4) 5 (leaf 6)))
    (Tree.node (leaf 4) 5 (leaf 6)) = true := by decide

/-- Same `s`, a non-matching `t` (wrong label) — not a subtree. -/
example : subFn (Tree.node (leaf 1) 2 (Tree.node (leaf 4) 5 (leaf 6)))
    (Tree.node (leaf 4) 5 (leaf 7)) = false := by decide

/-- A whole tree is its own subtree (rooted at itself). -/
example : subFn (Tree.node (leaf 1) 2 (Tree.node (leaf 4) 5 (leaf 6)))
    (Tree.node (leaf 1) 2 (Tree.node (leaf 4) 5 (leaf 6))) = true := by decide

/-- `nil` is a subtree of `nil`. -/
example : subFn (Tree.nil : Tree Int) Tree.nil = true := by decide

end Freyd.Alg.RelSet.LC572
