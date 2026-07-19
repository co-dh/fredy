/-
  LeetCode 404 — Sum of Left Leaves — DERIVED from the TREE TUPLING LAW.

  `leet/L404.lean` WRITES the naive program `sumLL : Tree Int → Bool → Int` by hand — a leaf-checking
  fold with a `Bool` "is-this-node-a-left-child" flag threaded DOWN the recursion (five structural
  cases: nil / leaf / left-only / right-only / both).  Its carrier is really `Bool → Int`, i.e. the
  PAIR of its values at `true` and `false` (`sumLL t true`, `sumLL t false`) — a genuine tupling
  candidate.  BUT the pair alone is NOT enough to run a single bottom-up fold: the node step must tell
  a genuine leaf (`node nil a nil`, whose carried pair is `(a, 0)`) apart from a one-child node whose
  carried pair happens to also read `0` on one side, and both look identical from the pair values.  So
  we ALSO carry a nil/leaf flag.  The tupling carrier is the TRIPLE

    `p t = (isNilOf t, sumLL t true, sumLL t false) : Bool × Int × Int`

  i.e. `C₁ := Bool` (the nil flag) and `C₂ := Int × Int` (the two carried sums).  Its base `g` and step
  `step` are FORCED (not guessed) by `p_nil`/`p_node`, the problem's own recurrence — `p_nil` is `rfl`,
  and `p_node` is a 4-way case split on the two children's shapes matching `sumLL`'s five clauses (the
  crux: a `node l a r` is a LEAF iff both children are `nil`, i.e. `nl && nr`; otherwise the answer is
  `sumLL l true + sumLL r false = tl + fr`, independent of the flag).  Applying the tree tupling law
  `treeTupling g step p p_nil p_node` PRODUCES the single-pass fold `cataR (treePairAlg g step)`.  The
  decision reads off the SECOND carried sum: `sumLL t false = (p t).2.2`, so the derived solution is
  `cataR (treePairAlg g step) ≫ graph (·.2.2)`, PROVED equal to `L404.solve`
  (`derivedSolve_eq_solve`); correctness then transports through the existing `L404`
  characterisation (`sum_left_leaves_correct` / `mem_leftLeafValues_iff`) unchanged.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.
-/
import AOP.A6_9_TreeTupling
import leet.L404
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC404D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC404

/-! ## The nil detector and the tupling ANSATZ -/

/-- `isNilOf t` — `true` iff `t` is `nil`.  The extra bit the pair `(sumLL t true, sumLL t false)`
    cannot supply: it is what lets the node step tell a genuine leaf apart from a one-child node whose
    carried sum reads `0` on the same side. -/
def isNilOf : Tree Int → Bool
  | Tree.nil => true
  | Tree.node _ _ _ => false

/-- Carry the TRIPLE `(isNil, sumLL·true, sumLL·false)` — the tupling ansatz.  `C₁ = Bool`,
    `C₂ = Int × Int`. -/
def p (t : Tree Int) : Bool × Int × Int := (isNilOf t, sumLL t true, sumLL t false)

/-- The base of the emergent algebra: `p nil = (true, 0, 0)`, forced by the recurrence. -/
def g : Bool × Int × Int := (true, 0, 0)

/-- The step of the emergent algebra, read off `sumLL`: carrying `(nl, tl, fl)` and `(nr, tr, fr)`, a
    `node l a r` is a LEAF exactly when both children are `nil` (`nl && nr`), and then contributes
    `(false, a, 0)`; otherwise it is a non-leaf whose two carried sums both equal
    `sumLL l true + sumLL r false = tl + fr` (independent of the descended flag), giving
    `(false, tl + fr, tl + fr)`.  `isNilOf (node …) = false` always. -/
def step : Bool × Int × Int → Int → Bool × Int × Int → Bool × Int × Int :=
  fun pl a pr =>
    if pl.1 && pr.1 then (false, a, 0)
    else (false, pl.2.1 + pr.2.2, pl.2.1 + pr.2.2)

/-! ## The FORCED base/step conditions (the problem's own recurrence, PROVED) -/

/-- The step condition at `nil` (a COMPUTATION, `rfl`): `p nil = g`. -/
theorem p_nil : p Tree.nil = g := rfl

/-- The step condition at a node: `p (node l a r) = step (p l) a (p r)`.  THE CRUX — a 4-way case
    split on whether each child is `nil` or a `node`, matching `sumLL`'s five clauses:
    * both `nil` (leaf): `nl && nr = true`, `p = (false, a, 0)` — the `if`'s then-branch;
    * left-only (`l` a node, `r = nil`): `nl && nr = false`, `fr = sumLL nil false = 0`, so
      `tl + fr = tl + 0 = tl`;
    * right-only (`l = nil`, `r` a node): `nl && nr = false`, `tl = sumLL nil true = 0`, so
      `tl + fr = 0 + fr = fr`;
    * both nodes: `nl && nr = false`, `p = (false, tl + fr, tl + fr)` exactly. -/
theorem p_node (l r : Tree Int) (a : Int) :
    p (Tree.node l a r) = step (p l) a (p r) := by
  cases l with
  | nil =>
    cases r with
    | nil => rfl
    | node rl ra rr =>
      show (false, sumLL (Tree.node Tree.nil a (Tree.node rl ra rr)) true,
            sumLL (Tree.node Tree.nil a (Tree.node rl ra rr)) false)
          = (false, (0 : Int) + sumLL (Tree.node rl ra rr) false,
             (0 : Int) + sumLL (Tree.node rl ra rr) false)
      rw [sumLL_right_only, sumLL_right_only, Int.zero_add]
  | node ll la lr =>
    cases r with
    | nil =>
      show (false, sumLL (Tree.node (Tree.node ll la lr) a Tree.nil) true,
            sumLL (Tree.node (Tree.node ll la lr) a Tree.nil) false)
          = (false, sumLL (Tree.node ll la lr) true + (0 : Int),
             sumLL (Tree.node ll la lr) true + (0 : Int))
      rw [sumLL_left_only, sumLL_left_only, Int.add_zero]
    | node rl ra rr => rfl

/-! ## The fold EMERGES via the tree tupling law -/

/-- **The `(isNil, sumLL·true, sumLL·false)` triple fold EMERGES.**  `graph p` equals the catamorphism
    of the emergent algebra `treePairAlg g step`, PRODUCED by the tree tupling law from the forced base
    `g` and step `step`.  The triple-carrying single-pass fold was never written by hand here. -/
theorem sumleftleaves_emerges :
    (graph p : dTree Int ⟶ ⟨Bool × Int × Int⟩) = cataR (treePairAlg g step) :=
  treeTupling g step p p_nil (fun l a r => p_node l r a)

/-- **The derived solution**: the emergent fold followed by reading off the SECOND carried sum
    (`t ↦ (p t).2.2 = sumLL t false`). -/
def derivedSolve : dTree Int ⟶ dInt :=
  cataR (treePairAlg g step) ≫ graph (fun t : Bool × Int × Int => t.2.2)

/-- **The derivation reaches `L404.solve`.**  Rewriting the emergent fold back to `graph p`
    (`sumleftleaves_emerges`) and composing graphs, the second-slot projection of `p t` is exactly
    `sumLL t false = sumLeftLeavesFn t`. -/
theorem derivedSolve_eq_solve : derivedSolve = LC404.solve := by
  show cataR (treePairAlg g step) ≫ graph (fun t : Bool × Int × Int => t.2.2) = LC404.solve
  rw [← sumleftleaves_emerges]
  apply hom_ext; intro t y
  constructor
  · rintro ⟨z, hz, hy⟩; subst hz; exact hy
  · intro hy; exact ⟨p t, rfl, hy⟩

/-! ## Correctness -/

/-- **Correctness of the derived program** (the derived analogue of `L404.sum_left_leaves_correct`):
    the derived solution relates every tree `t` to the sum of its left-leaf values — where, by the
    existing `mem_leftLeafValues_iff`, `leftLeafValues t false` contains exactly the values at genuine
    left-leaf positions.  `derivedSolve_eq_solve` identifies the derived program with `L404.solve`, and
    `sum_left_leaves_correct` reads off the sum. -/
theorem sumleftleaves_derived_correct (t : Tree Int) :
    derivedSolve t (leftLeafValues t false).sum := by
  rw [derivedSolve_eq_solve]
  show (leftLeafValues t false).sum = sumLeftLeavesFn t
  exact (sum_left_leaves_correct t).symm

/-! ## Running / cross-checking the emergent fold against `leet/L404.lean`

  The relational catamorphism `cataTreeFold (treePairAlg …)` is not `decide`-computable (its `node`
  case is an existential), so we `decide` the extensionally-equal computable witness `p` (equal by
  `sumleftleaves_emerges`), reading off its second carried sum `(p t).2.2` and cross-checking against
  `L404.sumLeftLeavesFn` on `L404`'s own example trees. -/

-- LeetCode's own example: root 3, left child 9 (a leaf), right child 20 with children 15, 7.
-- Left leaves 9 and 15 sum to 24.
example :
    (p (Tree.node (leaf 9) 3 (Tree.node (leaf 15) 20 (leaf 7)))).2.2 = 24 := by decide

example :
    (p (Tree.node (leaf 9) 3 (Tree.node (leaf 15) 20 (leaf 7)))).2.2
      = sumLeftLeavesFn (Tree.node (leaf 9) 3 (Tree.node (leaf 15) 20 (leaf 7))) := by decide

-- Lone root: a leaf, but not a LEFT child of anything — contributes 0.
example : (p (leaf (5 : Int))).2.2 = 0 := by decide

end Freyd.Alg.RelSet.LC404D
