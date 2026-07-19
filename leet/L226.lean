/-
  LeetCode 226 — Invert Binary Tree — as an ALLEGORY PROGRAM, the STRUCTURAL-OUTPUT case.

  Problem: given a binary tree, swap every node's left and right subtree (recursively).

  Every solve so far (`L104`, `L121`, `L191`, …) has a SCALAR/Bool answer object (`ℕ`, `Bool`, a
  pair).  Here the answer IS a `Tree A` again: `solve` is an ENDOMORPHISM `dTree A ⟶ dTree A` in
  `Rel(Set)`, source and target the SAME initial-algebra object.  Two consequences:

  1. **Program** — `invertFn` is the two-branch fold `[ nil ↦ nil,  (l,a,r) ↦ node r a l ]`
     (`A6_TreeBin`'s `F X = 1 + X×A×X`), packaged as `solve : dTree A ⟶ dTree A := graph invertFn`;
     `solve_eq_cata` shows it equals the relational catamorphism `cataR alg` of the swap algebra —
     no trailing projection, mirrors `L104`'s `solve_eq_cata` but with `c := dTree A` instead of
     `c := ℕ`.

  2. **Specification** — a STRUCTURAL relation `IsMirror t t'` ("`t'` is `t` with every node's
     children swapped") replaces the numeric predicates (`pathLen`, …) of the scalar problems: no
     order to refine into, so correctness is not a refinement+domination `⊑` extremum but a direct
     structural fact.

  3. **Correctness** — `solve_correct : IsMirror t (invertFn t)` (the program produces the mirror)
     plus the law with no scalar analogue, `invert_invert : invertFn (invertFn t) = t`
     (inverting twice is the identity) — the natural extra content of a program whose answer lives
     in the same object as its input.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_TreeBin
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC226

open Freyd Freyd.Alg.RelSet.TB

-- Derived after the fact (not in `A6_TreeBin`, which stays `Rel(Set)`-only) so the `decide`
-- checks below have `DecidableEq (Tree A)` for `A := Nat`.
deriving instance DecidableEq for Tree

variable {A : Type}

/-! ## The program: the swap fold `[ nil ↦ nil,  (l,a,r) ↦ node r a l ]` -/

/-- The concrete fold (structural recursion): swap left/right at every node. -/
def invertFn : Tree A → Tree A
  | Tree.nil => Tree.nil
  | Tree.node l a r => Tree.node (invertFn r) a (invertFn l)

/-- **The allegory program**: LeetCode 226's solution as an ENDOMORPHISM `dTree A ⟶ dTree A` in
    `Rel(Set)` — the STRUCTURAL-OUTPUT case, source and target the SAME object. -/
def solve : dTree A ⟶ dTree A := graph invertFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map (solve : dTree A ⟶ dTree A) := graph_map invertFn

/-- The swap algebra `[ nil ↦ nil,  (l,a,r) ↦ node r a l ] : F(Tree A) → Tree A`. -/
def algFn : (TFobj A (dTree A : RelSet.{0})).carrier → Tree A
  | Sum.inl _ => Tree.nil
  | Sum.inr (l, a, r) => Tree.node r a l

/-- The algebra as a morphism (a `Map`) `F(dTree A) ⟶ dTree A` in `Rel(Set)`. -/
def alg : TFobj A (dTree A : RelSet.{0}) ⟶ (dTree A : RelSet.{0}) := graph algFn

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree. -/
theorem cataTreeFold_alg : ∀ (t : Tree A) (r : Tree A), cataTreeFold alg t r ↔ r = invertFn t := by
  intro t; induction t with
  | nil => intro r; exact Iff.rfl
  | node l a r ihl ihr =>
    intro res
    simp only [cataTreeFold_node]
    constructor
    · rintro ⟨rl, rr, hl, hr, hf⟩
      rw [ihl rl] at hl; rw [ihr rr] at hr; subst hl; subst hr; exact hf
    · intro h; exact ⟨invertFn l, invertFn r, (ihl (invertFn l)).mpr rfl, (ihr (invertFn r)).mpr rfl, h⟩

/-- **The program is a catamorphism**: `solve = ⦇[nil ↦ nil, (l,a,r) ↦ node r a l]⦈`, with NO
    trailing projection — the fold's state already IS the answer, and here the answer lives in the
    SAME object `dTree A` as the input (contrast `L104`'s `c := ℕ`). -/
theorem solve_eq_cata : (solve : dTree A ⟶ dTree A) = cataR alg := by
  apply hom_ext; intro t v
  show v = invertFn t ↔ cataTreeFold alg t v
  exact (cataTreeFold_alg t v).symm

/-! ## Specification: the structural mirror relation -/

/-- `IsMirror t t'` — `t'` is the structural mirror of `t`: `nil` mirrors `nil`; `node l a r`
    mirrors `node l' a' r'` iff the labels agree and the children are mirrored CROSSWISE
    (`t`'s left mirrors `t'`'s right, `t`'s right mirrors `t'`'s left). -/
def IsMirror : Tree A → Tree A → Prop
  | Tree.nil, Tree.nil => True
  | Tree.nil, Tree.node _ _ _ => False
  | Tree.node _ _ _, Tree.nil => False
  | Tree.node l a r, Tree.node l' a' r' => a = a' ∧ IsMirror l r' ∧ IsMirror r l'

/-! ## Correctness: `solve` produces the mirror, and inverting twice is the identity -/

/-- **Correctness of the allegory program**: `invertFn t` is the structural mirror of `t`. -/
theorem solve_correct : ∀ t : Tree A, IsMirror t (invertFn t)
  | Tree.nil => trivial
  | Tree.node l a r => ⟨rfl, solve_correct l, solve_correct r⟩

/-- **Involutivity**: inverting twice is the identity.  The natural EXTRA law of a
    STRUCTURAL-OUTPUT program (no scalar/Bool answer object has this shape — there is nothing to
    "invert again" for a depth or a count). -/
theorem invert_invert : ∀ t : Tree A, invertFn (invertFn t) = t
  | Tree.nil => rfl
  | Tree.node l a r => by
    show Tree.node (invertFn (invertFn l)) a (invertFn (invertFn r)) = Tree.node l a r
    rw [invert_invert l, invert_invert r]

/-! ## Specification and the structural-output headline -/

/-- The **specification** as a morphism `dTree A ⟶ dTree A` in `Rel(Set)`: `out` is the structural
    mirror of `t`.  Stated via `IsMirror` (a program-independent relation), NOT via `invertFn`. -/
def spec : dTree A ⟶ (dTree A : RelSet.{0}) := fun t out => IsMirror t out

/-- **Uniqueness**: the mirror of a tree is unique — two mirrors of the same `t` are equal.  A
    STRUCTURAL-OUTPUT program needs this (alongside existence, `solve_correct`) to pin `spec` to a
    single answer, so the relation `spec` is actually the graph of the program.  Induction on `t`,
    the crosswise children matched by the two IHs. -/
theorem mirror_unique : ∀ (t o₁ o₂ : Tree A), IsMirror t o₁ → IsMirror t o₂ → o₁ = o₂ := by
  intro t
  induction t with
  | nil =>
    intro o₁ o₂ h₁ h₂
    cases o₁ with
    | nil => cases o₂ with
      | nil => rfl
      | node _ _ _ => exact h₂.elim
    | node _ _ _ => exact h₁.elim
  | node l a r ihl ihr =>
    intro o₁ o₂ h₁ h₂
    cases o₁ with
    | nil => exact h₁.elim
    | node p b q =>
      cases o₂ with
      | nil => exact h₂.elim
      | node p' b' q' =>
        obtain ⟨hab, hlq, hrp⟩ := h₁
        obtain ⟨hab', hlq', hrp'⟩ := h₂
        rw [← hab, ← hab', ihl q q' hlq hlq', ihr p p' hrp hrp']

/-- **`solve` equals `spec` as relations** — the STRUCTURAL-OUTPUT headline: existence
    (`solve_correct`) plus uniqueness (`mirror_unique`) make the program exactly the mirror
    relation. -/
theorem solve_eq_spec : (solve : dTree A ⟶ dTree A) = spec := by
  apply hom_ext; intro t v
  show (v = invertFn t) ↔ IsMirror t v
  constructor
  · intro h; rw [h]; exact solve_correct t
  · intro h; exact mirror_unique t v (invertFn t) h (solve_correct t)

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : A) : Tree A := Tree.node Tree.nil a Tree.nil

/-- A small asymmetric tree: root `2`, left child a leaf `1`, right child `node (leaf 3) 4 nil`. -/
def asym : Tree Nat := Tree.node (leaf 1) 2 (Tree.node (leaf 3) 4 Tree.nil)

/-- The hand-computed mirror of `asym`. -/
def asymMirror : Tree Nat := Tree.node (Tree.node Tree.nil 4 (leaf 3)) 2 (leaf 1)

example : invertFn (leaf (5 : Nat)) = leaf 5 := by decide
example : invertFn (Tree.nil : Tree Nat) = Tree.nil := by decide
example : invertFn asym = asymMirror := by decide
example : invertFn (invertFn asym) = asym := by decide

end Freyd.Alg.RelSet.LC226
