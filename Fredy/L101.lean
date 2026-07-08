/-
  LeetCode 101 — Symmetric Tree — as an ALLEGORY PROGRAM.

  Problem: given the root of a binary tree, return `true` iff it is a mirror of itself (a
  symmetric reflection around its center).

  A tree is symmetric iff its left subtree is the MIRROR image of its right subtree — a
  TWO-tree crosswise reflection, exactly `Fredy/L100.lean`'s "Same Tree" bridge (`S16`) but with
  the CROSS-swapped recursion of `Fredy/L226.lean`'s `IsMirror` (`S15`) instead of a literal
  structural match.  So `mirrorFn`/`Mirror` below are `L226.invertFn`/`IsMirror` read as a
  BINARY relation between two trees (crosswise child comparison) rather than a unary swap, then
  `isSymmetricFn` applies that binary decision to a single tree's own two children — the L100
  reflection-bridge technique (double structural induction, one tree fixed by `induction`, the
  other universally quantified and `cases` per shape) carries over unchanged.

  1. **Data** — input lives in `dTree Int`; answer `⟨Bool⟩`.

  2. **Program** — `mirrorFn t1 t2` decides whether `t1`, `t2` are mirror images of each other
     CROSSWISE: `nil,nil ↦ true`; `node l1 a1 r1, node l2 a2 r2 ↦ decide (a1=a2) && mirrorFn l1 r2
     && mirrorFn r1 l2` (`l1` against `r2`, `r1` against `l2`); any `nil`/`node` mismatch ↦
     `false`. `isSymmetricFn t := match t with | nil => true | node l _ r => mirrorFn l r`.
     `solve : dTree Int ⟶ ⟨Bool⟩ := graph isSymmetricFn`.

  3. **Specification** — `Mirror` is the Prop mirror of `mirrorFn` (an honest INDUCTIVE relation,
     not a tautological restatement): `mnil : Mirror nil nil`; `mnode : a1=a2 → Mirror l1 r2 →
     Mirror r1 l2 → Mirror (node l1 a1 r1) (node l2 a2 r2)`. `IsSymmetric t := match t with
     | nil => True | node l _ r => Mirror l r`.

  4. **Correctness** — `mirror_correct : mirrorFn t1 t2 = true ↔ Mirror t1 t2`, by the L100
     double-induction reflection bridge (induct on `t1`, `t2` universally quantified, `cases t2`
     per shape; nil/node cross cases vacuous both sides via `simp`/`nomatch`; the node/node case
     splits the Bool `&&` into a Prop `∧` via `Bool.and_eq_true`/`decide_eq_true_eq` and feeds the
     two crosswise IHs into `Mirror.mnode`).  The headline `symmetric_correct : isSymmetricFn t =
     true ↔ IsSymmetric t` is then a one-line `cases t` unfolding into `mirror_correct`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_TreeBin

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC101

open Freyd Freyd.Alg.RelSet.TB

/-! ## The program: a two-input crosswise-mirror fold, applied to a tree's own children -/

/-- `mirrorFn t1 t2` — are `t1` and `t2` mirror images of each other, CROSSWISE (`t1`'s left
    against `t2`'s right, `t1`'s right against `t2`'s left)? -/
def mirrorFn : Tree Int → Tree Int → Bool
  | Tree.nil, Tree.nil => true
  | Tree.node l1 a1 r1, Tree.node l2 a2 r2 => decide (a1 = a2) && mirrorFn l1 r2 && mirrorFn r1 l2
  | Tree.nil, Tree.node _ _ _ => false
  | Tree.node _ _ _, Tree.nil => false

/-- `isSymmetricFn t` — is `t`'s left subtree the mirror image of its right subtree? -/
def isSymmetricFn (t : Tree Int) : Bool :=
  match t with
  | Tree.nil => true
  | Tree.node l _ r => mirrorFn l r

/-- **The allegory program**: LeetCode 101's solution as a morphism `dTree Int ⟶ ⟨Bool⟩` in
    `Rel(Set)`. -/
def solve : dTree Int ⟶ (⟨Bool⟩ : RelSet.{0}) := graph isSymmetricFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map isSymmetricFn

/-! ## Specification: the crosswise mirror relation -/

/-- `Mirror t1 t2` — `t1` and `t2` are mirror images of each other, CROSSWISE: `nil` mirrors
    `nil`; `node l1 a1 r1` mirrors `node l2 a2 r2` iff the labels agree and the children mirror
    CROSSWISE (`t1`'s left against `t2`'s right, `t1`'s right against `t2`'s left). -/
inductive Mirror : Tree Int → Tree Int → Prop where
  | mnil : Mirror Tree.nil Tree.nil
  | mnode {l1 r1 l2 r2 : Tree Int} {a1 a2 : Int} :
      a1 = a2 → Mirror l1 r2 → Mirror r1 l2 → Mirror (Tree.node l1 a1 r1) (Tree.node l2 a2 r2)

/-- `IsSymmetric t` — `t`'s left subtree is the mirror image of its right subtree. -/
def IsSymmetric (t : Tree Int) : Prop :=
  match t with
  | Tree.nil => True
  | Tree.node l _ r => Mirror l r

/-! ## Correctness: `mirrorFn` computes `Mirror`, by DOUBLE structural induction (the L100 bridge) -/

/-- **`mirrorFn` computes `Mirror`** — induction on `t1`, with `t2` universally quantified and
    `cases` per shape (the `L100`/`S16` reflection-bridge technique). -/
theorem mirror_correct : ∀ t1 t2 : Tree Int, mirrorFn t1 t2 = true ↔ Mirror t1 t2 := by
  intro t1
  induction t1 with
  | nil =>
    intro t2
    cases t2 with
    | nil => exact ⟨fun _ => Mirror.mnil, fun _ => rfl⟩
    | node l2 a2 r2 =>
      constructor
      · intro h; simp [mirrorFn] at h
      · intro h; exact nomatch h
  | node l1 a1 r1 ihl ihr =>
    intro t2
    cases t2 with
    | nil =>
      constructor
      · intro h; simp [mirrorFn] at h
      · intro h; exact nomatch h
    | node l2 a2 r2 =>
      constructor
      · intro h
        have h' : (decide (a1 = a2) && mirrorFn l1 r2 && mirrorFn r1 l2) = true := h
        rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h'
        exact Mirror.mnode h'.1 ((ihl r2).mp h'.2.1) ((ihr l2).mp h'.2.2)
      · intro h
        cases h with
        | mnode heq hml hmr =>
          show (decide (a1 = a2) && mirrorFn l1 r2 && mirrorFn r1 l2) = true
          rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨heq, (ihl r2).mpr hml⟩, (ihr l2).mpr hmr⟩

/-- **The headline**: `isSymmetricFn` decides `IsSymmetric` — a tree is symmetric iff its left
    subtree mirrors its right subtree, which is exactly `mirror_correct` at the two children. -/
theorem symmetric_correct : ∀ t : Tree Int, isSymmetricFn t = true ↔ IsSymmetric t := by
  intro t
  cases t with
  | nil => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | node l a r =>
    show mirrorFn l r = true ↔ Mirror l r
    exact mirror_correct l r

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

/-- LeetCode's symmetric example: `[1,2,2,3,4,4,3]`. -/
def symTree : Tree Int :=
  Tree.node (Tree.node (leaf 3) 2 (leaf 4)) 1 (Tree.node (leaf 4) 2 (leaf 3))

/-- LeetCode's asymmetric example: `[1,2,2,null,3,null,3]`. -/
def asymTree : Tree Int :=
  Tree.node (Tree.node Tree.nil 2 (leaf 3)) 1 (Tree.node Tree.nil 2 (leaf 3))

example : isSymmetricFn symTree = true := by decide
example : isSymmetricFn asymTree = false := by decide

end Freyd.Alg.RelSet.LC101
