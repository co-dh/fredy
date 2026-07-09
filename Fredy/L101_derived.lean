/-
  LeetCode 101 — Symmetric Tree — DERIVED from the GENERAL-CARRIER TREE FOLD LAW.

  `Fredy/L101.lean` WRITES the two-input crosswise-mirror recursion `mirrorFn : Tree Int → Tree Int →
  Bool` by hand (`mirrorFn t1 t2` decides whether `t1`, `t2` are mirror images, crosswise) and verifies
  it against the inductive spec `Mirror` (`mirror_correct`).  HERE the recursion EMERGES instead as a
  single catamorphism over the FIRST tree, whose CARRIER is the residual predicate `Tree Int → Bool`
  awaiting the second tree — the two-input recursion collapses to a one-input fold into a higher-order
  carrier.

  Read `mirrorFn` curried on its FIRST argument: `mirrorFn : Tree Int → (Tree Int → Bool)`, so
  `h := mirrorFn`, `C := Tree Int → Bool`.  The base `g = mirrorFn nil` and step `step` are READ OFF
  `mirrorFn`'s two clauses; the crossing is copied EXACTLY from `L101.mirrorFn`'s node equation
  (`decide (a1 = a2) && mirrorFn l1 r2 && mirrorFn r1 l2`): the left residual `fl = mirrorFn l1` is
  applied to the OTHER tree's RIGHT (`r2`), the right residual `fr = mirrorFn r1` to its LEFT (`l2`).
  `mirrorFn` obeys the first-order structural recursion `mirrorFn nil = g`,
  `mirrorFn (node l a r) = step (mirrorFn l) a (mirrorFn r)` (both proved by `funext`/`cases`/`rfl`,
  `hnil`/`hnode`).  The general-carrier tree fold law `TB.treeFold_unique g step mirrorFn hnil hnode`
  then PRODUCES the single fold `cataR (treeScalarAlg g step)` and identifies it with `graph mirrorFn`
  (`mirror_emerges`) — the higher-order carrier `Tree Int → Bool` is irrelevant to the law, which is
  generic over the carrier.

  `L101.isSymmetricFn t` (nil ↦ true, `node l _ r ↦ mirrorFn l r`) then asks whether `t`'s left subtree
  mirrors its right.  The headline `symmetric_derived_correct` says: whenever the EMERGENT fold relates
  the left subtree `l` to a residual predicate `fl`, applying `fl` to the right subtree `r` yields
  exactly `isSymmetricFn (node l a r)`, which — via `L101.mirror_correct` (reused, not re-proved) —
  decides `IsSymmetric (node l a r)`.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataTreeFold` /
  `treeFold_unique` only, never the `cataR_eq_relCata` bridge (which pulls `Classical.choice`).
-/
import Fredy.A6_GenFold
import Fredy.L101

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC101D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC101

/-! ## The base and step, READ OFF `L101.mirrorFn`, over the residual carrier `Tree Int → Bool` -/

/-- The base of the emergent algebra: `mirrorFn nil` as a residual predicate — the empty tree mirrors
    exactly the empty tree (`nil ↦ true`, any `node ↦ false`).  Read off `L101.mirrorFn`'s `nil` clauses. -/
def g : Tree Int → Bool :=
  fun t2 => match t2 with
    | Tree.nil          => true
    | Tree.node _ _ _   => false

/-- The step of the emergent algebra, over the higher-order carrier.  Carrying the left/right residual
    predicates `fl = mirrorFn l`, `fr = mirrorFn r`, the parent residual awaits a second tree `t2`:
    against `nil` it is `false`; against `node l2 a2 r2` it is `decide (a = a2) && fl r2 && fr l2` —
    the CROSSWISE comparison of `L101.mirrorFn`'s node clause (`fl` against the OTHER tree's RIGHT `r2`,
    `fr` against its LEFT `l2`).  It is DEFINITIONALLY `mirrorFn`'s node step (see `hnode`). -/
def step : (Tree Int → Bool) → Int → (Tree Int → Bool) → (Tree Int → Bool) :=
  fun fl a fr => fun t2 => match t2 with
    | Tree.nil             => false
    | Tree.node l2 a2 r2   => decide (a = a2) && fl r2 && fr l2

/-! ## The FORCED structural recursion of `mirrorFn` (both `funext`/`cases`/`rfl`) -/

/-- The base condition: `mirrorFn nil = g`, matching `mirrorFn`'s inner match on the second tree. -/
theorem hnil : LC101.mirrorFn Tree.nil = g := by
  funext t2; cases t2 <;> rfl

/-- The step condition: `mirrorFn (node l a r) = step (mirrorFn l) a (mirrorFn r)` — the problem's
    first-order crosswise recurrence, proved not defined (matching the inner match on the second
    tree). -/
theorem hnode (l : Tree Int) (a : Int) (r : Tree Int) :
    LC101.mirrorFn (Tree.node l a r) = step (LC101.mirrorFn l) a (LC101.mirrorFn r) := by
  funext t2; cases t2 <;> rfl

/-! ## The fold EMERGES via the general-carrier tree fold law -/

/-- **The crosswise-mirror recursion EMERGES.**  `graph mirrorFn` — the curried
    `Tree Int → (Tree Int → Bool)` — equals the catamorphism of the emergent algebra
    `treeScalarAlg g step`, PRODUCED by the general-carrier tree fold law from the forced base `g` and
    step `step`.  The two-input recursion was never re-written; it collapses to a one-input fold into
    the residual-predicate carrier `Tree Int → Bool`. -/
theorem mirror_emerges :
    (graph LC101.mirrorFn : dTree Int ⟶ ⟨Tree Int → Bool⟩) = cataR (treeScalarAlg g step) :=
  TB.treeFold_unique g step LC101.mirrorFn hnil hnode

/-! ## Correctness of the derived program, transported from `L101.mirror_correct` -/

/-- **Correctness of the derived program.**  Whenever the EMERGENT fold relates the left subtree `l`
    to a residual predicate `fl` (`cataTreeFold (treeScalarAlg g step) l fl`), applying `fl` to the
    right subtree `r` is exactly `L101.isSymmetricFn (node l a r)` — and, via `L101.mirror_correct`
    (reused), it decides `L101.IsSymmetric (node l a r)`.  The emergence (`mirror_emerges`) pins
    `fl = mirrorFn l`; the symmetric decision then reads the residual at the sibling subtree. -/
theorem symmetric_derived_correct (l r : Tree Int) (a : Int) (fl : Tree Int → Bool)
    (hfl : cataTreeFold (treeScalarAlg g step) l fl) :
    fl r = LC101.isSymmetricFn (Tree.node l a r) ∧
      (fl r = true ↔ LC101.IsSymmetric (Tree.node l a r)) := by
  have hgr : (graph LC101.mirrorFn : dTree Int ⟶ ⟨Tree Int → Bool⟩) l fl := by
    rw [mirror_emerges]; exact hfl
  have hfleq : fl = LC101.mirrorFn l := hgr
  subst hfleq
  refine ⟨rfl, ?_⟩
  show LC101.mirrorFn l r = true ↔ LC101.Mirror l r
  exact LC101.mirror_correct l r

/-! ## Running / cross-checking the emergent fold against `Fredy/L101.lean`

  The relational catamorphism `cataTreeFold (treeScalarAlg …)` is not `decide`-computable (its `node`
  case is an existential over the residual carrier, a function), so we `decide` only the Bool answers of
  the extensionally-equal computable `mirrorFn`/`isSymmetricFn` (equal by `mirror_emerges`), never the
  function carrier. -/

/-- The derived symmetric decision on `L101`'s symmetric example `[1,2,2,3,4,4,3]`. -/
example : LC101.isSymmetricFn LC101.symTree = true := by decide

/-- The derived symmetric decision on `L101`'s asymmetric example `[1,2,2,null,3,null,3]`. -/
example : LC101.isSymmetricFn LC101.asymTree = false := by decide

/-- The CROSSING made explicit: `node (leaf 1) 2 (leaf 3)` mirrors `node (leaf 3) 2 (leaf 1)`
    crosswise (left `leaf 1` against right `leaf 1`; right `leaf 3` against left `leaf 3`). -/
example : LC101.mirrorFn (Tree.node (LC101.leaf 1) 2 (LC101.leaf 3))
    (Tree.node (LC101.leaf 3) 2 (LC101.leaf 1)) = true := by decide

end Freyd.Alg.RelSet.LC101D
