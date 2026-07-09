/-
  LeetCode 112 — Path Sum — DERIVED as a HIGHER-ORDER (residual-target) tree catamorphism.

  `Fredy/L112.lean` WRITES `hasPathSumFn : Tree Int → Int → Bool` by hand, threading the target sum
  DOWN the recursion (subtracting the node label at each step) — not the shape of a bottom-up
  catamorphism over the tree.  It becomes one once you CURRY the target to the OTHER side: read
  `hasPathSumFn` as `Tree Int → (Int → Bool)`, i.e. fold the tree FIRST into a RESIDUAL decider
  `foldC t : Int → Bool` that still awaits the target.  This is the same higher-order-fold trick as
  `L98`/`L100` — carrier a FUNCTION type — but with one extra wrinkle unique to Path Sum: the program
  case-splits on whether each CHILD is `nil` (a leaf is a node with BOTH children `nil`; a lone-`nil`
  child must NOT be read as a leaf).  A bare residual `Int → Bool` cannot recover "was this subtree
  `nil`", so the carrier carries an explicit nil FLAG alongside the residual:

      C := Bool × (Int → Bool)      -- (was-the-subtree-nil, residual awaiting the target)

  (the skill's "carry an explicit `isNil` flag" recipe for the nil-vs-leaf ambiguity).

  The base `g = (true, fun _ => false)` (nil: flag `true`, residual always `false`) and the step
  `step (bl,fl) a (br,fr) = (false, …)` are READ OFF `hasPathSumFn`'s clauses.  Using the two child
  flags `bl,br`, the step reconstructs the exact case split: both-nil ⟹ leaf `decide (a = target)`;
  one child non-nil ⟹ recurse into it at `target - a`; both non-nil ⟹ `||` of the two.  `foldC`
  obeys the structural recursion `foldC nil = g`, `foldC (node l a r) = step (foldC l) a (foldC r)`
  (both `rfl`), so `TB.treeFold_unique g step foldC hnil hnode` PRODUCES the higher-order catamorphism
  `cataR (treeScalarAlg g step)` and identifies it with `graph foldC` (`path_sum_emerges`): the
  target-threaded decider is not written, it emerges.  `foldC_snd` bridges the residual back to
  `hasPathSumFn` (`(foldC t).2 target = hasPathSumFn t target`), so `derivedSolve` (feed the target
  into the residual) is `LC112.solve`, and `LC112.solve_eq_spec` (the existing decision correctness,
  NOT re-proved here) transports onto the emergent fold (`path_sum_derived_correct`).

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataTreeFold` /
  `treeFold_unique` only, never the `cataR_eq_relCata` bridge (which pulls `Classical.choice`).
-/
import Fredy.A6_GenFold
import Fredy.L112

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC112D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC112

/-! ## Carrier: `Bool × (Int → Bool)` — the nil flag paired with the residual target-decider -/

/-- The base of the emergent algebra: `g = foldC nil` — folding the empty tree gives flag `true`
    (the subtree WAS `nil`) and a residual that answers `false` at every target (no path through
    `nil`). -/
def g : Bool × (Int → Bool) := (true, fun _ => false)

/-- The step of the emergent algebra, READ OFF `hasPathSumFn`'s node clauses.  From the two children's
    results `(bl, fl) = foldC l`, `(br, fr) = foldC r` and the root label `a`, the parent's flag is
    `false` (a node is never `nil`) and its residual answers the target by the SAME case split as
    `hasPathSumFn`, keyed on the child nil-flags `bl, br`:

    * both children `nil` (`true, true`) — a genuine LEAF — decide `a = target`;
    * left non-`nil` only (`false, true`) — recurse left at `target - a`;
    * right non-`nil` only (`true, false`) — recurse right at `target - a`;
    * both non-`nil` (`false, false`) — `||` of both children at `target - a`. -/
def step : (Bool × (Int → Bool)) → Int → (Bool × (Int → Bool)) → (Bool × (Int → Bool)) :=
  fun cl a cr => (false, fun target =>
    match cl.1, cr.1 with
    | true,  true  => decide (a = target)
    | false, true  => cl.2 (target - a)
    | true,  false => cr.2 (target - a)
    | false, false => cl.2 (target - a) || cr.2 (target - a))

/-- View `hasPathSumFn` as a fold of the tree into `(nil-flag, residual)`: folding `t` produces a
    decider `(foldC t).2 : Int → Bool` still awaiting the target, tagged with whether `t` was `nil`. -/
def foldC : Tree Int → Bool × (Int → Bool)
  | Tree.nil        => g
  | Tree.node l a r => step (foldC l) a (foldC r)

/-! ## The FORCED structural recursion of `foldC` -/

/-- The base condition of `treeFold_unique`: `foldC nil = g` — definitional. -/
theorem hnil : foldC Tree.nil = g := rfl

/-- The step condition of `treeFold_unique`: `foldC (node l a r) = step (foldC l) a (foldC r)` —
    definitional. -/
theorem hnode (l : Tree Int) (a : Int) (r : Tree Int) :
    foldC (Tree.node l a r) = step (foldC l) a (foldC r) := rfl

/-! ## The higher-order catamorphism EMERGES via the general-carrier law -/

/-- **The residual target-decider EMERGES.**  `graph foldC` equals the catamorphism of the scalar
    tree algebra `treeScalarAlg g step = [ nil ↦ g, (cl,a,cr) ↦ step cl a cr ]` on the carrier
    `Bool × (Int → Bool)`, PRODUCED by `TB.treeFold_unique` from the forced base `g` and step `step`.
    The target-threaded top-down scan is now a single bottom-up catamorphism over the tree whose
    output is the residual `(foldC t).2 : Int → Bool` awaiting the target — the AOP curry that turns
    a downward-accumulator scan into a fold. -/
theorem path_sum_emerges :
    (graph foldC : dTree Int ⟶ ⟨Bool × (Int → Bool)⟩) = cataR (treeScalarAlg g step) :=
  TB.treeFold_unique g step foldC hnil hnode

/-! ## Bridging the emergent residual back to `L112.hasPathSumFn` -/

/-- The residual produced by the emergent fold, applied at a target, is exactly `hasPathSumFn` — by
    structural recursion mirroring `hasPathSumFn`'s own 5-way case split.  The child nil-flags carried
    in the first component reduce the `step` match to the matching `hasPathSumFn` clause. -/
theorem foldC_snd : ∀ (t : Tree Int) (target : Int), (foldC t).2 target = hasPathSumFn t target
  | Tree.nil, target => rfl
  | Tree.node Tree.nil a Tree.nil, target => rfl
  | Tree.node (Tree.node ll la lr) a Tree.nil, target => by
      show (foldC (Tree.node ll la lr)).2 (target - a) = hasPathSumFn (Tree.node ll la lr) (target - a)
      exact foldC_snd (Tree.node ll la lr) (target - a)
  | Tree.node Tree.nil a (Tree.node rl ra rr), target => by
      show (foldC (Tree.node rl ra rr)).2 (target - a) = hasPathSumFn (Tree.node rl ra rr) (target - a)
      exact foldC_snd (Tree.node rl ra rr) (target - a)
  | Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr), target => by
      show ((foldC (Tree.node ll la lr)).2 (target - a) || (foldC (Tree.node rl ra rr)).2 (target - a))
         = (hasPathSumFn (Tree.node ll la lr) (target - a) || hasPathSumFn (Tree.node rl ra rr) (target - a))
      rw [foldC_snd (Tree.node ll la lr) (target - a), foldC_snd (Tree.node rl ra rr) (target - a)]

/-! ## Connecting the emergent residual back to `L112.solve` -/

/-- The derived solver: feed the target into the residual `(foldC t).2` that the emergent
    higher-order catamorphism produces from the tree.  A two-INPUT `graph` over `(tree, target)`. -/
def derivedSolve : TreeTarget ⟶ dBool :=
  graph (fun p : Tree Int × Int => (foldC p.1).2 p.2)

/-- The derived solver IS `L112.solve` — applying the emergent residual at the target is exactly
    `hasPathSumFn` (`foldC_snd`). -/
theorem derivedSolve_eq_solve : derivedSolve = LC112.solve := by
  apply hom_ext; intro p b
  show (b = (foldC p.1).2 p.2) ↔ (b = hasPathSumFn p.1 p.2)
  rw [foldC_snd p.1 p.2]

/-! ## Correctness of the derived program, transported from `L112.solve_eq_spec` -/

/-- **The Path-Sum program is the higher-order catamorphism, and it is correct.**  The honest
    headline bundles:

    * `path_sum_emerges` — `graph foldC = cataR (treeScalarAlg g step)`: the curried program IS the
      higher-order catamorphism over the FUNCTION-typed carrier `Bool × (Int → Bool)`; and
    * `derivedSolve = LC112.spec` — the derived two-input solver equals the specification relation
      `spec p b := (b = true ↔ PathSum p.1 p.2)`, obtained by chaining `derivedSolve = LC112.solve`
      (the emergent residual applied at the target) with `LC112.solve_eq_spec` (the existing decision
      correctness, NOT re-proved here). -/
theorem path_sum_derived_correct :
    ((graph foldC : dTree Int ⟶ ⟨Bool × (Int → Bool)⟩) = cataR (treeScalarAlg g step)) ∧
    (derivedSolve = LC112.spec) :=
  ⟨path_sum_emerges, derivedSolve_eq_solve.trans LC112.solve_eq_spec⟩

/-! ## Running / cross-checking the emergent fold against `Fredy/L112.lean`

  The relational catamorphism `cataTreeFold (treeScalarAlg …)` has a FUNCTION-typed carrier, so
  equality on it is not decidable — we never `decide` a residual.  Instead we `decide` the
  extensionally-equal computable `hasPathSumFn` on concrete trees (its RESULT `Bool`), and separately
  PROVE the higher-order fold relates a tree to its residual. -/

-- The trap case (from `L112`): root `1` has only a lone LEFT child, which itself has only a lone LEFT
-- child `3`; neither `1` nor `2` is a leaf, so the sole path `1→2→3` sums to `6`.
example : hasPathSumFn (Tree.node (Tree.node (leaf 3) 2 Tree.nil) 1 Tree.nil) 6 = true := by decide
example : hasPathSumFn (Tree.node (leaf 1) 2 Tree.nil) 1 = false := by decide
-- a balanced tree: path `5→4→11→2` sums to `22`
example : hasPathSumFn (Tree.node (Tree.node (leaf 11) 4 Tree.nil) 5 (leaf 8)) 20 = true := by decide

/-- The emergent higher-order fold genuinely relates `node (leaf 1) 2 (leaf 3)` to its RESIDUAL
    decider `foldC (node (leaf 1) 2 (leaf 3))` — the value the fold produces, proved via
    `path_sum_emerges` (no `decide` on the function-typed carrier). -/
example : cataTreeFold (treeScalarAlg g step)
    (Tree.node (leaf 1) 2 (leaf 3)) (foldC (Tree.node (leaf 1) 2 (leaf 3))) := by
  have h : (graph foldC : dTree Int ⟶ ⟨Bool × (Int → Bool)⟩)
      (Tree.node (leaf 1) 2 (leaf 3)) (foldC (Tree.node (leaf 1) 2 (leaf 3))) := rfl
  rw [path_sum_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC112D
