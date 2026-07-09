/-
  LeetCode 198 — House Robber — DERIVED from the tupling law.

  `Fredy/L198.lean` WRITES the pair-carrying DP fold `foldFn` (state `(best, prevBest)`) by hand and
  verifies it by induction (`cataFold_alg`, `solve_eq_cata`).  This file makes that fold EMERGE from
  the reusable tupling / linearization law `Freyd.Alg.RelSet.SL.tupling` (`Fredy/A6_8_Tupling.lean`),
  exactly as `Fredy/L70_derived.lean` (Fibonacci) and `Fredy/L1137_derived.lean` (Tribonacci) do.

  The House-Robber recurrence "looks back one step but keeps two quantities": the optimum of the
  whole list depends on the optimum of the prefix AND the optimum of the prefix with its last house
  forbidden.  The tupling ANSATZ = carry that pair `(best, prevBest)`.  Its base and step are then
  FORCED — they are `foldFn`'s own defining equations (both hold by `rfl`):

    * base   `g x = (max x 0, 0)`                              = `foldFn (wrap x)`
    * step   `step (best, prev) p = (max best (prev + p), best)` = `foldFn (snoc xs p)` with
             `(best, prev) = foldFn xs`.

  Feeding `g`/`step`/`foldFn` to `tupling` PRODUCES the pair-carrying fold as
  `cataR (pairAlg g step)` — we never write the recursive fold; it is the law's catamorphism.
  Projecting the first component (`tupling_fst`) recovers the scalar answer `solve` of `L198.lean`,
  so the derived program `derivedSolve` equals the hand-written `LC198.solve`, and the existing
  correctness (`LC198.solve_correct`: `solve = max (≤) · Λ robSpec`, pointwise) carries over
  unchanged — the derived fold computes the House-Robber optimum.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_8_Tupling
import Fredy.L198

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC198D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The tupling ANSATZ and its FORCED base/step

  The carrier of the tupling law is `C₁ × C₂` with `C₁ = C₂ = ℤ`; the pair carried is
  `(best, prevBest)` — the creative choice (which two quantities to keep).  The base `g` and step
  `step` below are not guesses: they are `LC198.foldFn`'s defining equations, so both conditions
  hold by `rfl`. -/

/-- The base of the emergent algebra: `foldFn (wrap x) = (max x 0, 0)`. -/
def g : Int → Int × Int := fun x => (LC198.imax x 0, 0)

/-- The step of the emergent algebra: carrying `(best, prev)`, the next pair is
    `(max best (prev + p), best)` — the House-Robber transition. -/
def step : Int × Int → Int → Int × Int := fun st p => (LC198.imax st.1 (st.2 + p), st.1)

/-- The base condition is a COMPUTATION, not a guess: `foldFn (wrap x) = g x`. -/
theorem foldFn_wrap : ∀ l : Int, LC198.foldFn (SnocList.wrap l) = g l := fun l => rfl

/-- The step condition IS `foldFn`'s snoc equation: `foldFn (snoc xs p) = step (foldFn xs) p`. -/
theorem foldFn_snoc : ∀ (xs : SnocList Int Int) (e : Int),
    LC198.foldFn (SnocList.snoc xs e) = step (LC198.foldFn xs) e := fun xs e => rfl

/-! ## The fold EMERGES via the tupling law -/

/-- **The derivation.**  The pair-carrying DP fold is PRODUCED by the tupling law from the base `g`
    and step `step` — it was never written by hand: `graph foldFn` equals the catamorphism of the
    emergent algebra `pairAlg g step = [ x ↦ (max x 0, 0), ((best,prev),p) ↦ (max best (prev+p), best) ]`. -/
theorem fold_derived :
    (graph LC198.foldFn : dSL Int Int ⟶ ⟨Int × Int⟩) = cataR (pairAlg g step) :=
  tupling g step LC198.foldFn foldFn_wrap foldFn_snoc

/-- The derived allegory program: the emergent fold followed by the first projection (`best`). -/
def derivedSolve : LC198.Arr ⟶ LC198.dZ :=
  cataR (pairAlg g step) ≫ graph (Prod.fst : Int × Int → Int)

/-- The derived program equals the hand-written `LC198.solve`: projecting `best` off the
    tupling-produced fold recovers the scalar House-Robber answer (`tupling_fst`). -/
theorem derivedSolve_eq_solve : derivedSolve = LC198.solve := by
  show cataR (pairAlg g step) ≫ graph (Prod.fst : Int × Int → Int) = LC198.solve
  rw [← tupling_fst g step LC198.foldFn foldFn_wrap foldFn_snoc]
  rfl

/-! ## Correctness carries over from `L198.lean` (no re-proof of the optimization argument) -/

/-- **Headline.**  The tupling-derived fold computes the House-Robber optimum: `derivedSolve`
    relates each array `xs` to a value `m` that is an achievable robbery (`robSpec`) and dominates
    every achievable robbery — i.e. the `≤`-maximum `max (≤) · Λ robSpec`.  The optimization
    argument is REUSED from `LC198.solve_correct` (via `derivedSolve_eq_solve`), not re-proved. -/
theorem rob_derived_correct (xs : SnocList Int Int) :
    ∃ m, derivedSolve xs m ∧ LC198.robSpec xs m ∧ ∀ v, LC198.robSpec xs v → v ≤ m := by
  refine ⟨LC198.solveFn xs, ?_, (LC198.solve_correct xs).1, (LC198.solve_correct xs).2⟩
  rw [derivedSolve_eq_solve]
  exact rfl

/-! ## Running / cross-checking the emergent fold against `Fredy/L198.lean`

  As in `L70_derived`/`L1137_derived`, the relational catamorphism `cataFold (pairAlg …)` is not
  `decide`-computable (its `snoc` case is an existential over `ℤ × ℤ`), so we `decide` the
  extensionally-equal computable witness `LC198.foldFn`/`LC198.solveFn` (equal by `fold_derived`),
  and separately PROVE that the emergent fold relates a concrete array to `foldFn` of it. -/

-- The scalar answers `decide` on the computable witness (LeetCode 198 examples):
example : LC198.solveFn (LC198.ofList 1 [2, 3, 1]) = 4 := by decide
example : LC198.solveFn (LC198.ofList 2 [7, 9, 3, 1]) = 12 := by decide
example : (LC198.foldFn (LC198.ofList 2 [7, 9, 3, 1])).1 = 12 := by decide
example : LC198.solveFn (LC198.ofList (-3) [-1]) = 0 := by decide

/-- The emergent fold genuinely relates the array `[1,2,3,1]` to `foldFn` of it (whose `.1` is 4). -/
example :
    cataFold (pairAlg g step) (LC198.ofList 1 [2, 3, 1])
      (LC198.foldFn (LC198.ofList 1 [2, 3, 1])) := by
  have h : (graph LC198.foldFn : dSL Int Int ⟶ ⟨Int × Int⟩)
      (LC198.ofList 1 [2, 3, 1]) (LC198.foldFn (LC198.ofList 1 [2, 3, 1])) := rfl
  rw [fold_derived] at h
  exact h

end Freyd.Alg.RelSet.LC198D
