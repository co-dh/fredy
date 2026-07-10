/-
  LeetCode 98 — Validate Binary Search Tree — DERIVED as a HIGHER-ORDER (residual-bounds) tree
  catamorphism.

  `leet/L98.lean` WRITES the bounds scan `within : Option Int → Option Int → Tree Int → Bool` by
  hand — the bounds `(lo, hi)` are an accumulator threaded DOWN the recursion (tightened at each
  node), which is NOT the shape of a bottom-up catamorphism over the tree.  It becomes one once you
  CURRY the bounds to the OTHER side: read `within` as `Tree Int → (Option Int → Option Int → Bool)`,
  i.e. fold the tree FIRST into a RESIDUAL bounds-checker `withinC t : Option Int → Option Int → Bool`
  that still awaits the `(lo, hi)` bounds.  With carrier `C := Option Int → Option Int → Bool` this
  residual is an ordinary structural fold of the tree, and the AOP way to expose it is the
  general-carrier fold-uniqueness law `TB.treeFold_unique` (`AOP/A6_GenFold.lean`) — the same law
  whose `C = C₁ × C₂` instance is the tupling law (`L110`/`L124`), but here the carrier is a FUNCTION
  type, so the accumulator-threaded scan collapses to a single catamorphism over the tree.

  The base `g = withinC nil` and step `step = (withinC node recurrence)` are READ OFF `within`'s two
  defining equations (curried on the awaited bounds): `g = fun _ _ => true`, and `step fl a fr` checks
  `lo < a`, `a < hi` (a `none` bound is unconstrained) AND applies the two children's residuals at the
  TIGHTENED bounds `fl lo (some a)`, `fr (some a) hi` — the exact bound-tightening of `within`'s node
  clause.  `withinC` obeys the structural recursion `withinC nil = g`,
  `withinC (node l a r) = step (withinC l) a (withinC r)` — both proved by `funext` on the awaited
  bounds (`hnil`, `hnode`).  The law `TB.treeFold_unique g step withinC hnil hnode` then PRODUCES the
  higher-order catamorphism `cataR (treeScalarAlg g step)` and identifies it with `graph withinC`
  (`bst_emerges`): the curried bounds-checker is not written, it emerges.  `LC98.solve` FEEDS the
  initial bounds `(none, none)` into this residual (`bstFn t = withinC t none none`), and
  `LC98.solve_correct` (the existing bounds-generalized `Iff`, NOT re-proved here) transports the
  BST-decision correctness onto the emergent fold (`bst_derived_correct`).

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataTreeFold` /
  `treeFold_unique` only, never the `cataR_eq_relCata` bridge (which pulls `Classical.choice`).
-/
import AOP.A6_GenFold
import leet.L98

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC98D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC98

/-! ## `within` with the tree curried to the FRONT: the residual bounds-checker

  Carrier `C := Option Int → Option Int → Bool` — the RESIDUAL bounds-checker that, having folded the
  tree, still awaits the inherited bounds `(lo, hi)`. -/

/-- View `within` as a fold of the tree into a residual: `withinC t = fun lo hi => within lo hi t`.
    Folding `t` produces a bounds-checker still awaiting `(lo, hi)`. -/
def withinC (t : Tree Int) : Option Int → Option Int → Bool := fun lo hi => within lo hi t

/-! ## The base and step, READ OFF `L98.within` (curried on the awaited bounds) -/

/-- The base of the emergent algebra: `g = withinC nil` — the residual after folding the empty tree
    answers `true` at ANY bounds (`nil` is trivially in range). -/
def g : Option Int → Option Int → Bool := fun _ _ => true

/-- The step of the emergent algebra: from the two children's residuals `fl = withinC l`,
    `fr = withinC r` and the root label `a`, the parent's residual `withinC (node l a r)` answers the
    bounds `(lo, hi)` by requiring `lo < a` and `a < hi` (a `none` bound unconstrained) AND applying
    the children's residuals at the TIGHTENED bounds `fl lo (some a)`, `fr (some a) hi`.  Read off
    `within`'s node clause, curried in the awaited bounds. -/
def step : (Option Int → Option Int → Bool) → Int → (Option Int → Option Int → Bool) →
    (Option Int → Option Int → Bool) :=
  fun fl a fr => fun lo hi =>
    (match lo with | none => true | some x => decide (x < a)) &&
    (match hi with | none => true | some y => decide (a < y)) &&
    fl lo (some a) && fr (some a) hi

/-! ## The FORCED structural recursion of the curried `within` -/

/-- The base condition: `withinC nil = g`, by extensionality on the awaited bounds. -/
theorem hnil : withinC Tree.nil = g := by
  funext lo hi; rfl

/-- The step condition: `withinC (node l a r) = step (withinC l) a (withinC r)` — the problem's
    bound-tightening recurrence in curried form, proved not defined (extensionality on the awaited
    bounds, then `rfl`: `within`'s node clause reduced with the tree in front). -/
theorem hnode (l : Tree Int) (a : Int) (r : Tree Int) :
    withinC (Tree.node l a r) = step (withinC l) a (withinC r) := by
  funext lo hi; rfl

/-! ## The higher-order catamorphism EMERGES via the general-carrier law -/

/-- **The residual bounds-checker EMERGES.**  `graph withinC` equals the catamorphism of the scalar
    tree algebra `treeScalarAlg g step = [ nil ↦ g, (fl,a,fr) ↦ step fl a fr ]` on the FUNCTION
    carrier `Option Int → Option Int → Bool`, PRODUCED by `TB.treeFold_unique` from the forced base
    `g` and step `step`.  The accumulator-threaded bounds scan is now a single catamorphism over the
    tree, whose output is the residual `withinC t : Option Int → Option Int → Bool` awaiting the
    bounds — the AOP curry that turns a downward-accumulator scan into a fold. -/
theorem bst_emerges :
    (graph withinC : dTree Int ⟶ ⟨Option Int → Option Int → Bool⟩) = cataR (treeScalarAlg g step) :=
  TB.treeFold_unique g step withinC hnil hnode

/-! ## Connecting the emergent residual back to `L98.solve` -/

/-- The derived solver: feed the INITIAL (unconstrained) bounds `(none, none)` into the residual
    `withinC t` that the emergent higher-order catamorphism produces from the tree.  Definitionally
    `L98.solve` — the bounds scan is exactly "fold the tree to a residual, then apply it at the root
    bounds `(none, none)`" (`bstFn t = within none none t = withinC t none none`). -/
def derivedSolve : dTree Int ⟶ dBool :=
  graph (fun t : Tree Int => withinC t none none)

/-- The derived solver IS `L98.solve` — the bounds scan is the emergent residual applied at the root
    bounds (`withinC t none none = within none none t = bstFn t`, definitionally). -/
theorem derivedSolve_eq_solve : derivedSolve = LC98.solve := rfl

/-! ## Correctness of the derived program, transported from `L98.solve_correct` -/

/-- **The Validate-BST program is the higher-order catamorphism, and it is correct.**  The honest
    headline bundles:

    * `bst_emerges` — `graph withinC = cataR (treeScalarAlg g step)`: the curried program IS the
      higher-order catamorphism over the FUNCTION carrier `Option Int → Option Int → Bool`; and
    * the transported correctness — for ANY residual `f : Option Int → Option Int → Bool` the emergent
      fold relates the tree `t` to, `f` decides BST at the root bounds `(none, none)`
      (`f none none = true ↔ IsBST t`).  Emergence pins `f = withinC t`, and `L98.solve_correct` (the
      existing bounds-generalized `Iff`, NOT re-proved here) supplies the decision. -/
theorem bst_derived_correct :
    ((graph withinC : dTree Int ⟶ ⟨Option Int → Option Int → Bool⟩) =
        cataR (treeScalarAlg g step)) ∧
    (∀ (t : Tree Int) (f : Option Int → Option Int → Bool),
        cataTreeFold (treeScalarAlg g step) t f → (f none none = true ↔ IsBST t)) := by
  refine ⟨bst_emerges, ?_⟩
  intro t f hf
  have hgr : (graph withinC : dTree Int ⟶ ⟨Option Int → Option Int → Bool⟩) t f := by
    rw [bst_emerges]; exact hf
  have hfeq : f = withinC t := hgr
  subst hfeq
  exact LC98.solve_correct t

/-! ## Running / cross-checking the emergent fold against `leet/L98.lean`

  The relational catamorphism `cataTreeFold (treeScalarAlg …)` has a FUNCTION carrier, so equality on
  it is not decidable — we never `decide` a residual.  Instead we `decide` the extensionally-equal
  computable `bstFn` on concrete trees (its RESULT `Bool`, from applying the residual at the root
  bounds), and separately PROVE the higher-order fold relates a tree to its residual. -/

-- The derived answers, matching `L98`'s stated results (only the final `Bool` is `decide`d).
example : bstFn (Tree.node (leaf (1 : Int)) 2 (leaf 3)) = true := by decide
example : bstFn (Tree.node (leaf (3 : Int)) 2 (leaf 1)) = false := by decide
-- the classic non-local violator: 4 < 5 but sits in 5's right subtree
example : bstFn (Tree.node (leaf (1 : Int)) 5 (Tree.node (leaf 4) 6 (leaf 7))) = false := by decide

/-- The emergent higher-order fold genuinely relates `node (leaf 1) 2 (leaf 3)` to its RESIDUAL
    bounds-checker `withinC (node (leaf 1) 2 (leaf 3))` — the function the fold produces, proved via
    `bst_emerges` (no `decide` on the function carrier). -/
example : cataTreeFold (treeScalarAlg g step)
    (Tree.node (leaf 1) 2 (leaf 3)) (withinC (Tree.node (leaf 1) 2 (leaf 3))) := by
  have h : (graph withinC : dTree Int ⟶ ⟨Option Int → Option Int → Bool⟩)
      (Tree.node (leaf 1) 2 (leaf 3)) (withinC (Tree.node (leaf 1) 2 (leaf 3))) := rfl
  rw [bst_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC98D
