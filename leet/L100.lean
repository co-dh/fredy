/-
  LeetCode 100 — Same Tree — as an ALLEGORY PROGRAM.

  Problem: given the roots of two binary trees, return `true` iff the trees are structurally
  identical (same shape, same node values).

  Unlike `leet/L104.lean` (a single-tree fold) or `leet/L217.lean` (a single-input Bool
  decision), this is a TWO-INPUT decision: the program is the `graph` of a function on a PAIR of
  trees, `Tree Int × Tree Int → Bool` (`Rel(Set)`'s objects are just Lean types, so the pair
  needs no categorical product — `A6_TreeBin`'s `Tree`).  The reflection bridge is proved by
  DOUBLE structural induction (induct on both trees at once, generalizing over the other), with
  the `nil`/`node` mismatch cases closed by `simp`.

  1. **Data** — inputs live in `⟨Tree Int × Tree Int⟩`; answer `⟨Bool⟩`.

  2. **Program** — `sameFn` recurses on both trees together: `nil,nil ↦ true`;
     `node l a r, node l' a' r' ↦ decide (a=a') && sameFn l l' && sameFn r r'`; any `nil`/`node`
     mismatch `↦ false`.  `solve : ⟨Tree Int × Tree Int⟩ ⟶ ⟨Bool⟩ := graph (fun p => sameFn p.1 p.2)`.

  3. **Specification** — `SameP` is the Prop mirror: structural equality of two trees.

  4. **Correctness** — `solve_correct t t' : sameFn t t' = true ↔ SameP t t'`, by induction on
     BOTH `t` and `t'` simultaneously.  The `nil` vs `node` cross cases are vacuous both ways
     (`sameFn` returns `false`, `SameP` is `False`), closed by `simp`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_TreeBin
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC100

open Freyd Freyd.Alg.RelSet.TB

/-! ## Data: a pair of `Tree Int`; answer = `Bool` -/

/-- The object of tree pairs in `Rel(Set)` — the two-input problem's domain. -/
abbrev TreePair : RelSet.{0} := ⟨Tree Int × Tree Int⟩
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## The program: a two-input structural-equality fold -/

/-- `sameFn t t'` — do `t` and `t'` have the same shape and the same node values? -/
def sameFn : Tree Int → Tree Int → Bool
  | Tree.nil, Tree.nil => true
  | Tree.node l a r, Tree.node l' a' r' => decide (a = a') && sameFn l l' && sameFn r r'
  | Tree.nil, Tree.node _ _ _ => false
  | Tree.node _ _ _, Tree.nil => false

/-- **The allegory program**: LeetCode 100's solution as a morphism `TreePair ⟶ dBool` in
    `Rel(Set)` — a two-INPUT Bool `graph` deciding structural tree equality. -/
def solve : TreePair ⟶ dBool := graph (fun p : Tree Int × Tree Int => sameFn p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map (fun p : Tree Int × Tree Int => sameFn p.1 p.2)

/-! ## Specification: structural equality -/

/-- `SameP t t'` — the Prop mirror of `sameFn`: `t` and `t'` are structurally identical. -/
def SameP : Tree Int → Tree Int → Prop
  | Tree.nil, Tree.nil => True
  | Tree.node l a r, Tree.node l' a' r' => a = a' ∧ SameP l l' ∧ SameP r r'
  | Tree.nil, Tree.node _ _ _ => False
  | Tree.node _ _ _, Tree.nil => False

/-- The **specification** as a morphism `TreePair ⟶ dBool` in `Rel(Set)`: `b` is THE correct
    boolean answer to "are `t`, `t'` the same tree?" -/
def spec : TreePair ⟶ dBool := fun (p : Tree Int × Tree Int) (b : Bool) => (b = true ↔ SameP p.1 p.2)

/-! ## Correctness: `solve` decides `SameP`, by DOUBLE structural induction -/

/-- **`sameFn` computes `SameP`** — the DECISION-problem correctness shape, now over a *binary*
    relation: induction on BOTH trees, with the `nil`/`node` cross cases vacuous both sides. -/
theorem solve_correct : ∀ t t' : Tree Int, sameFn t t' = true ↔ SameP t t' := by
  intro t
  induction t with
  | nil =>
    intro t'
    cases t' with
    | nil => simp [sameFn, SameP]
    | node l' a' r' => simp [sameFn, SameP]
  | node l a r ihl ihr =>
    intro t'
    cases t' with
    | nil => simp [sameFn, SameP]
    | node l' a' r' =>
      show (decide (a = a') && sameFn l l' && sameFn r r') = true ↔ (a = a' ∧ SameP l l' ∧ SameP r r')
      rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, ihl l', ihr r', and_assoc]

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
  show (b = sameFn p.1 p.2) ↔ (b = true ↔ SameP p.1 p.2)
  constructor
  · intro h; rw [h]; exact solve_correct p.1 p.2
  · intro h
    have h' : (b = true) ↔ (sameFn p.1 p.2 = true) := h.trans (solve_correct p.1 p.2).symm
    exact bool_eq_of_iff_true h'

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

example : sameFn (leaf (1 : Int)) (leaf 1) = true := by decide
example : sameFn (Tree.node (leaf 1) 2 (leaf 3)) (Tree.node (leaf 1) 2 (leaf 3)) = true := by decide
example : sameFn (Tree.node (leaf 1) 2 (leaf 3)) (Tree.node (leaf 1) 2 (leaf 4)) = false := by decide
example : sameFn (Tree.node (leaf 1) 2 Tree.nil) (Tree.node (leaf 1) 2 (leaf 3)) = false := by decide
example : sameFn (Tree.nil : Tree Int) Tree.nil = true := by decide

end Freyd.Alg.RelSet.LC100
