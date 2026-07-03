/-
  LeetCode 104 — Maximum Depth of Binary Tree — as an ALLEGORY PROGRAM.

  Problem: given a binary tree, return the length of the longest root-to-`nil` path (depth).

  This is the SEED example for the Tree block of `Fredy/leetcode.md`, built on the new reusable
  engine `Fredy.A6_TreeBin` (the tree-shaped counterpart of `A6_SnocList`'s `SnocList`/`cataFold`):

  1. **Data** — a binary tree is `Tree A` (`A6_TreeBin`), the initial algebra of
     `F X = 1 + X×A×X` (`nil` an empty leaf, `node l a r` an `A`-labelled internal node).  A
     root-to-leaves recursion *is* a catamorphism.

  2. **Program** — `depthFn` is the two-branch fold `[ () ↦ 0,  (dl,_,dr) ↦ 1 + max dl dr ]`,
     packaged as `solve : dTree A ⟶ ℕ := graph depthFn`; `solve_eq_cata` shows it equals the
     relational catamorphism `cataR alg` — no trailing projection, the fold's state IS the answer
     (contrast L121's `≫ snd`; matches L191's shape).

  3. **Specification** — `pathLen t n` says `n` is the length of SOME root-to-`nil` path in `t`.
     LeetCode's "the" depth is the `≤`-maximum of this relation, `max (≤) · Λ pathLen`.

  4. **Correctness** — `solve_correct` : `depthFn t` is an achievable path length
     (`pathLen t (depthFn t)`) and dominates every achievable path length
     (`∀ n, pathLen t n → n ≤ depthFn t`) — exactly the extremum shape of L121/L53's optimization
     scans, now over a TREE fold instead of a list scan.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_TreeBin
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC104

open Freyd Freyd.Alg.RelSet.TB

variable {A : Type}

/-! ## Mathlib-free `Nat` `min`/`max` (copied from `L121`, control the rewrite set) -/

def imin (a b : Nat) : Nat := if a ≤ b then a else b
def imax (a b : Nat) : Nat := if a ≤ b then b else a

theorem imin_le_left  (a b : Nat) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Nat) : imin a b ≤ b := by unfold imin; split <;> omega
theorem imin_eq_or (a b : Nat) : imin a b = a ∨ imin a b = b := by
  unfold imin; split; exacts [Or.inl rfl, Or.inr rfl]
theorem imax_ge_left  (a b : Nat) : a ≤ imax a b := by unfold imax; split <;> omega
theorem imax_ge_right (a b : Nat) : b ≤ imax a b := by unfold imax; split <;> omega
theorem imax_eq_or (a b : Nat) : imax a b = a ∨ imax a b = b := by
  unfold imax; split; exacts [Or.inr rfl, Or.inl rfl]

/-! ## Object of `Nat` answers in `Rel(Set)` -/

abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## The program: the depth fold `[ () ↦ 0,  (dl,_,dr) ↦ 1 + max dl dr ]` -/

/-- The fold algebra `[ () ↦ 0,  (dl,_,dr) ↦ 1 + imax dl dr ] : F(ℕ) → ℕ`. -/
def algFn : (TFobj A (dNat : RelSet.{0})).carrier → Nat
  | Sum.inl _ => 0
  | Sum.inr (dl, _, dr) => 1 + imax dl dr

/-- The algebra as a morphism (a `Map`) `F(ℕ) ⟶ ℕ` in `Rel(Set)`. -/
def alg : TFobj A (dNat : RelSet.{0}) ⟶ (dNat : RelSet.{0}) := graph algFn

/-- The concrete fold (structural recursion): the length of the longest root-to-`nil` path. -/
def depthFn : Tree A → Nat
  | Tree.nil => 0
  | Tree.node l _ r => 1 + imax (depthFn l) (depthFn r)

/-- **The allegory program**: LeetCode 104's solution as a morphism `dTree A ⟶ ℕ` in `Rel(Set)`. -/
def solve : dTree A ⟶ dNat := graph depthFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map (solve : dTree A ⟶ dNat) := graph_map depthFn

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree. -/
theorem cataTreeFold_alg : ∀ (t : Tree A) (r : Nat), cataTreeFold alg t r ↔ r = depthFn t := by
  intro t; induction t with
  | nil => intro r; exact Iff.rfl
  | node l a r ihl ihr =>
    intro res
    simp only [cataTreeFold_node]
    constructor
    · rintro ⟨rl, rr, hl, hr, hf⟩
      rw [ihl rl] at hl; rw [ihr rr] at hr; subst hl; subst hr; exact hf
    · intro h; exact ⟨depthFn l, depthFn r, (ihl (depthFn l)).mpr rfl, (ihr (depthFn r)).mpr rfl, h⟩

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈`, with NO trailing projection —
    the fold's state already IS the answer (mirrors L191, contrast L121's `≫ snd`). -/
theorem solve_eq_cata : (solve : dTree A ⟶ dNat) = cataR alg := by
  apply hom_ext; intro t v
  show v = depthFn t ↔ cataTreeFold alg t v
  exact (cataTreeFold_alg t v).symm

/-! ## Specification: the length of an achievable root-to-`nil` path -/

/-- `pathLen t n` — `n` is the length of SOME root-to-`nil` path in `t`. -/
def pathLen : Tree A → Nat → Prop
  | Tree.nil => fun n => n = 0
  | Tree.node l _ r => fun n => ∃ m, (pathLen l m ∨ pathLen r m) ∧ n = m + 1

/-- The **specification** as a morphism `dTree A ⟶ ℕ` in `Rel(Set)`: the relation of achievable
    root-to-`nil` path lengths.  LeetCode 104 asks for its `≤`-maximum, `max (≤) · Λ pathLen`. -/
def spec : dTree A ⟶ dNat := fun t n => pathLen t n

/-! ## Correctness: `solve` computes the maximum achievable path length -/

/-- The depth is itself an achievable path length (walk down the `imax`-larger side). -/
theorem pathLen_depth : ∀ t : Tree A, pathLen t (depthFn t)
  | Tree.nil => by show depthFn (A := A) Tree.nil = 0; rfl
  | Tree.node l a r => by
    show ∃ m, (pathLen l m ∨ pathLen r m) ∧ depthFn (Tree.node l a r) = m + 1
    show ∃ m, (pathLen l m ∨ pathLen r m) ∧ 1 + imax (depthFn l) (depthFn r) = m + 1
    cases imax_eq_or (depthFn l) (depthFn r) with
    | inl he => exact ⟨depthFn l, Or.inl (pathLen_depth l), by rw [he]; omega⟩
    | inr he => exact ⟨depthFn r, Or.inr (pathLen_depth r), by rw [he]; omega⟩

/-- The depth dominates every achievable path length. -/
theorem pathLen_le_depth : ∀ (t : Tree A) (n : Nat), pathLen t n → n ≤ depthFn t
  | Tree.nil, n, h => by have hn : n = 0 := h; omega
  | Tree.node l a r, n, h => by
    obtain ⟨m, hm, hn⟩ := h
    show n ≤ 1 + imax (depthFn l) (depthFn r)
    have hgl := imax_ge_left (depthFn l) (depthFn r)
    have hgr := imax_ge_right (depthFn l) (depthFn r)
    cases hm with
    | inl hml => have hle := pathLen_le_depth l m hml; omega
    | inr hmr => have hle := pathLen_le_depth r m hmr; omega

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ spec`, pointwise in
    `Rel(Set)`): `depthFn t` is an achievable path length and is `≤`-greatest among all
    achievable path lengths. -/
theorem solve_correct (t : Tree A) :
    pathLen t (depthFn t) ∧ ∀ n, pathLen t n → n ≤ depthFn t :=
  ⟨pathLen_depth t, fun n h => pathLen_le_depth t n h⟩

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : A) : Tree A := Tree.node Tree.nil a Tree.nil
/-- A balanced height-2 tree: root `a` with leaf children `b`, `c`. -/
def bal (a b c : A) : Tree A := Tree.node (leaf b) a (leaf c)

example : depthFn (leaf (5 : Nat)) = 1 := by decide
example : depthFn (bal (1 : Nat) 2 3) = 2 := by decide
example : depthFn (Tree.nil : Tree Nat) = 0 := by decide
example : depthFn (Tree.node (leaf (1 : Nat)) 2 Tree.nil) = 2 := by decide

end Freyd.Alg.RelSet.LC104
