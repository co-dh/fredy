/-
  LeetCode 617 — Merge Two Binary Trees — as an ALLEGORY PROGRAM.

  Problem: overlay two binary trees.  Where both trees have a node at the same position, sum the
  values; where only one has a node, keep it (verbatim, subtree and all); where neither has a
  node, the result has none there either.

  This combines the two prior tree-program shapes: TWO INPUTS (`L100`'s `TreePair`, a two-input
  decision) and a STRUCTURAL OUTPUT (`L226`'s `dTree A ⟶ dTree A` endomorphism, but here from a
  PAIR of trees).  Unlike `L100`'s `sameFn` (also two-tree, but Bool-valued), `mergeT`'s
  recursive case shrinks BOTH trees together at every step — exactly `List.zipWith`'s shape, so
  it compiles as ordinary STRUCTURAL recursion on the first tree (the second tree is pattern
  matched inside each minor premise, "along for the ride", never itself required to decrease) —
  no fuel parameter needed (contrast `L21`/`L1143`'s genuinely alternating two-argument descent).

  1. **Program** — `mergeT`: `nil t = t`; `t nil = t` (this SECOND clause only fires once the
     first tree is known non-nil — together the two base clauses give nil-nil ↦ nil for free);
     `node l1 a1 r1, node l2 a2 r2 ↦ node (mergeT l1 l2) (a1+a2) (mergeT r1 r2)`.

  2. **Specification — honest, via POSITION lookup, not a re-statement of the program.**
     `getPath t p` navigates a tree by a `List Bool` path (`false` = left, `true` = right),
     returning `none` off the tree and `some` the label at `p`.  `combine` is the four-case
     Option-merge matching the problem's prose EXACTLY: absent/absent ↦ absent,
     present/absent ↦ the present one, present/present ↦ the sum.  The headline
     `merge_correct : getPath (mergeT t1 t2) p = combine (getPath t1 p) (getPath t2 p)` says: at
     *every* position `p`, the merged tree's value is the position-wise overlay of the two
     inputs' values — this pins the overlay semantics exactly (not merely "some fold that looks
     plausible"), since `getPath`/`combine` are defined independently of `mergeT`.

  3. **Correctness proof** — induction on `t1`, generalizing `t2` and `p` (both trees + the path
     are threaded freely through the IH, `L100`-double-induction style but one-sided since only
     `t1` drives the recursion).  The `t1 = nil` and `t2 = nil` base cases each reduce to a
     one-line fact about `combine none x` / `combine x none`, closed by `cases … <;> rfl` — no
     `omega`, no classical reasoning, purely `Tree`/`Option` pattern matching.

  4. **Packaging** — `solve : TreePair ⟶ dTree Int := graph (fun p => mergeT p.1 p.2)`, a two-
     input `Rel(Set)` endomorphism-shaped program (`L100`'s domain, `L226`'s codomain-is-`Tree`
     shape); `solve_map` records it is a `Map`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound} — `merge_correct` itself is pure structural
  `Tree`/`Option` reasoning and needs neither.
-/
import Fredy.A6_TreeBin

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC617

open Freyd Freyd.Alg.RelSet.TB

-- Derived after the fact (not in `A6_TreeBin`, which stays `Rel(Set)`-only) so the `decide`
-- checks below have `DecidableEq (Tree Int)`.
deriving instance DecidableEq for Tree

/-! ## Data: a pair of `Tree Int`; answer = `Tree Int` -/

/-- The object of tree pairs in `Rel(Set)` — the two-input problem's domain. -/
abbrev TreePair : RelSet.{0} := ⟨Tree Int × Tree Int⟩

/-! ## The program: a two-tree structural-recursion fold (`List.zipWith`'s shape) -/

/-- `mergeT t1 t2` — overlay `t1` and `t2`: sum values where both have a node, keep the lone
    node where only one does, `nil` where neither does.  Structural recursion on `t1` (`t2` is
    pattern matched inside each minor premise, never itself required to decrease — the same
    shape as `List.zipWith`, NOT the fuel-needing alternating descent of `L21`/`L1143`). -/
def mergeT : Tree Int → Tree Int → Tree Int
  | Tree.nil, t => t
  | t, Tree.nil => t
  | Tree.node l1 a1 r1, Tree.node l2 a2 r2 => Tree.node (mergeT l1 l2) (a1 + a2) (mergeT r1 r2)

/-! ## Specification: position-wise overlay, via a path lookup independent of `mergeT` -/

/-- `getPath t p` — the label at the position reached by following `p` from `t`'s root
    (`false` = go left, `true` = go right); `none` if `p` runs off the tree. -/
def getPath : Tree Int → List Bool → Option Int
  | Tree.nil, _ => none
  | Tree.node _ a _, [] => some a
  | Tree.node l _ _, false :: p => getPath l p
  | Tree.node _ _ r, true :: p => getPath r p

/-- `combine` — the problem's overlay rule on a SINGLE position: absent/absent ↦ absent,
    present/absent (either side) ↦ the present value verbatim, present/present ↦ the sum. -/
def combine : Option Int → Option Int → Option Int
  | none, none => none
  | some x, none => some x
  | none, some y => some y
  | some x, some y => some (x + y)

/-! ## Correctness: `mergeT` computes the position-wise `combine` of the two inputs' `getPath` -/

/-- **The headline theorem.** At every position `p`, the merged tree's value is exactly the
    `combine` of the two input trees' values at `p` — the honest overlay semantics, pinned down
    independently of `mergeT`'s own recursive shape. Induction on `t1`, generalizing `t2`
    and `p`; the `nil` cases (either tree) need only `combine`'s own `none`-absorbing equations. -/
theorem merge_correct : ∀ (t1 t2 : Tree Int) (p : List Bool),
    getPath (mergeT t1 t2) p = combine (getPath t1 p) (getPath t2 p) := by
  intro t1
  induction t1 with
  | nil =>
    intro t2 p
    show getPath t2 p = combine none (getPath t2 p)
    cases getPath t2 p <;> rfl
  | node l1 a1 r1 ihl ihr =>
    intro t2 p
    cases t2 with
    | nil =>
      show getPath (Tree.node l1 a1 r1) p = combine (getPath (Tree.node l1 a1 r1) p) none
      cases getPath (Tree.node l1 a1 r1) p <;> rfl
    | node l2 a2 r2 =>
      cases p with
      | nil => rfl
      | cons b p' =>
        cases b with
        | false => exact ihl l2 p'
        | true => exact ihr r2 p'

/-! ## Packaging: the allegory program -/

/-- **The allegory program**: LeetCode 617's solution as a morphism `TreePair ⟶ dTree Int` in
    `Rel(Set)` — a two-input, tree-structural-OUTPUT `graph` (`L100`'s two-tree domain feeding
    `L226`'s tree-valued codomain shape). -/
def solve : TreePair ⟶ (dTree Int : RelSet.{0}) := graph (fun p : Tree Int × Tree Int => mergeT p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map (fun p : Tree Int × Tree Int => mergeT p.1 p.2)

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

/-- LeetCode's own example 1, tree 1:  `1` with left `3`(left leaf `5`) and right leaf `2`. -/
def ex1 : Tree Int := Tree.node (Tree.node (leaf 5) 3 Tree.nil) 1 (leaf 2)

/-- LeetCode's own example 1, tree 2:  `2` with left `1`(right leaf `4`) and right `3`(right leaf `7`). -/
def ex2 : Tree Int := Tree.node (Tree.node Tree.nil 1 (leaf 4)) 2 (Tree.node Tree.nil 3 (leaf 7))

/-- The hand-computed overlay of `ex1`/`ex2` (LeetCode's stated answer for example 1). -/
def exMerged : Tree Int :=
  Tree.node (Tree.node (leaf 5) 4 (leaf 4)) 3 (Tree.node Tree.nil 5 (leaf 7))

example : mergeT ex1 ex2 = exMerged := by decide
example : mergeT (Tree.nil : Tree Int) ex2 = ex2 := by decide

end Freyd.Alg.RelSet.LC617
