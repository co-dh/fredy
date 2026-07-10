/-
  LeetCode 100 — Same Tree — DERIVED as a HIGHER-ORDER (lockstep) tree catamorphism.

  `leet/L100.lean` WRITES the two-input recursion `sameFn : Tree Int → Tree Int → Bool` by hand and
  verifies it by DOUBLE structural induction.  A two-tree recursion is not a catamorphism over one
  tree — until you CURRY it.  Read `sameFn` as `Tree Int → (Tree Int → Bool)`: folding the FIRST tree
  `t1` produces a RESIDUAL decision procedure `sameFn t1 : Tree Int → Bool` that still awaits the
  second tree.  With carrier `C := Tree Int → Bool` this residual is an ordinary structural fold, and
  the AOP way to expose it is the general-carrier fold-uniqueness law
  `TB.treeFold_unique` (`AOP/A6_GenFold.lean`) — the same law's `C = C₁ × C₂` instance is the
  tupling law used by `L110`/`L124`, but here the carrier is a FUNCTION type, so the two-input
  recursion collapses to a single catamorphism.

  The base `g = sameFn nil` and step `step = (fⁿᵒᵈᵉ recurrence)` are READ OFF `sameFn`'s two defining
  equations (curried in the second argument).  `sameFn` obeys the first-order recursion
  `sameFn nil = g`, `sameFn (node l a r) = step (sameFn l) a (sameFn r)` — both proved by `funext` +
  `cases` on the awaited second tree (`hnil`, `hnode`).  The law
  `TB.treeFold_unique g step sameFn hnil hnode` then PRODUCES the higher-order catamorphism
  `cataR (treeScalarAlg g step)` and identifies it with `graph sameFn` (`sametree_emerges`): the
  curried decision procedure is not written, it emerges.  The two-input `solve` FEEDS the second tree
  into this residual (`derivedSolve`, `= L100.solve` by `rfl`), and `L100.solve_correct` transports
  the same-tree correctness onto the emergent fold (`sametree_derived_correct`).

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataTreeFold` /
  `treeFold_unique` only, never the `cataR_eq_relCata` bridge (which pulls `Classical.choice`).
-/
import AOP.A6_GenFold
import leet.L100

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC100D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC100

/-! ## The base and step, READ OFF `L100.sameFn` (curried on the second tree)

  Carrier `C := Tree Int → Bool` — the RESIDUAL decision procedure that, having folded the first
  tree, still awaits the second. -/

/-- The base of the emergent algebra: `g = sameFn nil` — the residual decision procedure after
    folding the empty first tree.  It answers `true` exactly when the second tree is ALSO empty. -/
def g : Tree Int → Bool := fun t =>
  match t with
  | Tree.nil        => true
  | Tree.node _ _ _ => false

/-- The step of the emergent algebra: from the two children's residuals `fl = sameFn l`,
    `fr = sameFn r` and the root label `a`, the parent's residual is `sameFn (node l a r)` — it
    answers a `node l' a' r'` by `decide (a = a') && fl l' && fr r'` (labels agree AND the left/right
    residuals accept the corresponding subtrees) and rejects `nil`.  Read off `sameFn`'s node clause,
    curried in the awaited second tree. -/
def step : (Tree Int → Bool) → Int → (Tree Int → Bool) → (Tree Int → Bool) :=
  fun fl a fr => fun t =>
    match t with
    | Tree.nil              => false
    | Tree.node l' a' r'    => decide (a = a') && fl l' && fr r'

/-! ## The FORCED first-order recursion of the curried `sameFn` -/

/-- The base condition: `sameFn nil = g`, by extensionality on the awaited second tree. -/
theorem hnil : sameFn Tree.nil = g := by
  funext t; cases t <;> rfl

/-- The step condition: `sameFn (node l a r) = step (sameFn l) a (sameFn r)` — the problem's
    first-order lockstep recurrence in curried form, proved not defined (extensionality on the
    awaited second tree, then its two cases are `rfl`). -/
theorem hnode (l : Tree Int) (a : Int) (r : Tree Int) :
    sameFn (Tree.node l a r) = step (sameFn l) a (sameFn r) := by
  funext t; cases t <;> rfl

/-! ## The higher-order catamorphism EMERGES via the general-carrier law -/

/-- **The residual decision procedure EMERGES.**  `graph sameFn` equals the catamorphism of the
    scalar tree algebra `treeScalarAlg g step = [ nil ↦ g, (fl,a,fr) ↦ step fl a fr ]` on the FUNCTION
    carrier `Tree Int → Bool`, PRODUCED by `TB.treeFold_unique` from the forced base `g` and step
    `step`.  The two-tree recursion is now a single catamorphism over the first tree, whose output is
    the residual `sameFn t1 : Tree Int → Bool` awaiting the second tree — the AOP curry that turns a
    two-input decision into a fold. -/
theorem sametree_emerges :
    (graph sameFn : dTree Int ⟶ ⟨Tree Int → Bool⟩) = cataR (treeScalarAlg g step) :=
  TB.treeFold_unique g step sameFn hnil hnode

/-! ## Connecting the emergent residual back to the two-input `solve` -/

/-- The derived solver: feed the SECOND tree `p.2` into the residual `sameFn p.1` that the emergent
    higher-order catamorphism produces from the first tree.  Definitionally `L100.solve` — the
    two-input program is exactly "fold the first tree to a residual, then apply it to the second". -/
def derivedSolve : TreePair ⟶ dBool :=
  graph (fun p : Tree Int × Tree Int => (sameFn p.1) p.2)

/-- The derived solver IS `L100.solve` — the two-input `solve` is the emergent residual applied to
    the second tree (`sameFn p.1 p.2 = (sameFn p.1) p.2`, definitionally). -/
theorem derivedSolve_eq_solve : derivedSolve = LC100.solve := rfl

/-! ## Correctness of the derived program, transported from `L100.solve_correct` -/

/-- **The Same-Tree program is the higher-order catamorphism, and it is correct.**  The honest
    headline bundles:

    * `sametree_emerges` — `graph sameFn = cataR (treeScalarAlg g step)`: the curried program IS the
      higher-order catamorphism over the FUNCTION carrier `Tree Int → Bool`; and
    * the transported correctness — for ANY residual `f : Tree Int → Bool` the emergent fold relates
      the first tree `t1` to, `f` decides same-tree against every second tree `t2`
      (`f t2 = true ↔ SameP t1 t2`).  Emergence pins `f = sameFn t1`, and `L100.solve_correct` (the
      existing DOUBLE-induction correctness, NOT re-proved here) supplies the decision. -/
theorem sametree_derived_correct :
    ((graph sameFn : dTree Int ⟶ ⟨Tree Int → Bool⟩) = cataR (treeScalarAlg g step)) ∧
    (∀ (t1 : Tree Int) (f : Tree Int → Bool),
        cataTreeFold (treeScalarAlg g step) t1 f → ∀ t2 : Tree Int, f t2 = true ↔ SameP t1 t2) := by
  refine ⟨sametree_emerges, ?_⟩
  intro t1 f hf t2
  have hgr : (graph sameFn : dTree Int ⟶ ⟨Tree Int → Bool⟩) t1 f := by
    rw [sametree_emerges]; exact hf
  have hfeq : f = sameFn t1 := hgr
  subst hfeq
  exact LC100.solve_correct t1 t2

/-! ## Running / cross-checking the emergent fold against `leet/L100.lean`

  The relational catamorphism `cataTreeFold (treeScalarAlg …)` has a FUNCTION carrier, so equality on
  it is not decidable — we never `decide` a residual.  Instead we `decide` the extensionally-equal
  computable `sameFn` on concrete tree pairs (its RESULT `Bool`, from applying the residual to the
  second tree), and separately PROVE the higher-order fold relates a first tree to its residual. -/

-- The derived answers, matching `L100`'s stated results (only the final `Bool` is `decide`d).
example : sameFn (leaf 1) (leaf 1) = true := by decide
example : sameFn (Tree.node (leaf 1) 2 (leaf 3)) (Tree.node (leaf 1) 2 (leaf 4)) = false := by decide
example : sameFn (Tree.node (leaf 1) 2 Tree.nil) (Tree.node (leaf 1) 2 (leaf 3)) = false := by decide
example : sameFn (Tree.nil : Tree Int) Tree.nil = true := by decide

/-- The emergent higher-order fold genuinely relates `node (leaf 1) 2 (leaf 3)` to its RESIDUAL
    decision procedure `sameFn (node (leaf 1) 2 (leaf 3)) : Tree Int → Bool` — the function the fold
    produces, proved via `sametree_emerges` (no `decide` on the function carrier). -/
example : cataTreeFold (treeScalarAlg g step)
    (Tree.node (leaf 1) 2 (leaf 3)) (sameFn (Tree.node (leaf 1) 2 (leaf 3))) := by
  have h : (graph sameFn : dTree Int ⟶ ⟨Tree Int → Bool⟩)
      (Tree.node (leaf 1) 2 (leaf 3)) (sameFn (Tree.node (leaf 1) 2 (leaf 3))) := rfl
  rw [sametree_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC100D
