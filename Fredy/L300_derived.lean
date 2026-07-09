/-
  LeetCode 300 — Longest Increasing Subsequence — DERIVED from the general-carrier fold law.

  `Fredy/L300.lean` WRITES the tabulating DP fold `foldFn` by hand (state `(records, best)` with
  `records : List (ℤ × ℕ)` the UNBOUNDED history of `(value, LIS-length-ending-here)` pairs) and
  verifies it by a bespoke induction (`cataFold_alg`, `solve_eq_cata`).  This file makes that fold
  EMERGE from the reusable general-carrier law `Freyd.Alg.RelSet.SL.snocFold_unique`
  (`Fredy/A6_GenFold.lean`), exactly as `Fredy/L198_derived.lean` (House Robber) does for the
  fixed-width tupling law.

  The point is the CARRIER.  House Robber carries a fixed-width pair `(best, prevBest)`, so the
  fixed-arity `tupling` law fits it.  LIS carries `List (ℤ × ℕ) × ℕ`, whose FIRST component is the
  UNBOUNDED HISTORY — every `(value, lisLenEndingHere)` record seen so far — and the step `lisEnd`
  SCANS that whole history (`dp[i]` depends on ALL earlier `dp[j]`, not a fixed window).  No
  fixed-width tuple can express this; only the arbitrary-carrier `snocFold_unique` (carrier `C`
  free) produces the fold.  Its base and step are then FORCED — they are `foldFn`'s own defining
  equations (both hold by `rfl`):

    * base   `g x = ([(x,1)], 1)`                              = `foldFn (wrap x)`
    * step   `st (records,best) p =
                (records ++ [(p, lisEnd records p)], nmax best (lisEnd records p))`
                                                              = `foldFn (snoc xs p)` with
             `(records,best) = foldFn xs`.

  Feeding `g`/`st`/`foldFn` to `snocFold_unique` PRODUCES the tabulating fold as
  `cataR (scalarAlg g st)` — we never write the recursive fold; it is the law's catamorphism.
  Projecting the second component (`best`) recovers the scalar answer `solve` of `L300.lean`, so
  the derived program `derivedSolve` equals the hand-written `LC300.solve`, and the existing
  correctness (`LC300.solve_correct`: `solve = max (≤) · Λ isSubseqInc`, pointwise) carries over
  unchanged — the derived fold computes the LIS optimum.  The LIS optimality/subsequence facts are
  REUSED from `L300.lean`, not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.L300

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC300D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The tabulating ANSATZ and its FORCED base/step

  The carrier of `snocFold_unique` is a bare type `C`; here `C = List (ℤ × ℕ) × ℕ` — the running
  `records` history paired with the running `best`.  The unbounded first component is what a
  fixed-width tupling law cannot carry.  The base `g` and step `st` below are not guesses: they are
  `LC300.foldFn`'s defining equations, so both conditions hold by `rfl`. -/

/-- The base of the emergent algebra: `foldFn (wrap x) = ([(x,1)], 1)` — a one-element history whose
    single record has LIS-length 1, and running best 1. -/
def g : Int → List (Int × Nat) × Nat := fun x => ([(x, 1)], 1)

/-- The step of the emergent algebra: carrying `(records, best)`, appending the new element `p`
    scans the WHOLE history via `lisEnd` to find its LIS-length-ending-here, records it, and updates
    the best — `(records ++ [(p, lisEnd records p)], nmax best (lisEnd records p))`. -/
def st : List (Int × Nat) × Nat → Int → List (Int × Nat) × Nat :=
  fun s p => (s.1 ++ [(p, LC300.lisEnd s.1 p)], LC300.nmax s.2 (LC300.lisEnd s.1 p))

/-- The base condition is a COMPUTATION, not a guess: `foldFn (wrap x) = g x`. -/
theorem foldFn_wrap : ∀ x : Int, LC300.foldFn (SnocList.wrap x) = g x := fun x => rfl

/-- The step condition IS `foldFn`'s snoc equation: `foldFn (snoc xs p) = st (foldFn xs) p`. -/
theorem foldFn_snoc : ∀ (xs : SnocList Int Int) (p : Int),
    LC300.foldFn (SnocList.snoc xs p) = st (LC300.foldFn xs) p := fun xs p => rfl

/-! ## The tabulating fold EMERGES via the general-carrier law -/

/-- **The derivation.**  The tabulating DP fold is PRODUCED by `snocFold_unique` from the base `g`
    and step `st` — it was never written by hand: `graph foldFn` equals the catamorphism of the
    emergent scalar algebra `scalarAlg g st`.  The arbitrary carrier `List (ℤ × ℕ) × ℕ` is essential:
    the first component is the unbounded history the step scans, which no fixed-width tupling carrier
    can hold. -/
theorem lis_emerges :
    (graph LC300.foldFn : dSL Int Int ⟶ ⟨List (Int × Nat) × Nat⟩) = cataR (scalarAlg g st) :=
  SL.snocFold_unique g st LC300.foldFn foldFn_wrap foldFn_snoc

/-- The derived allegory program: the emergent tabulating fold followed by the second projection
    (`best`). -/
def derivedSolve : LC300.Arr ⟶ LC300.dNat :=
  cataR (scalarAlg g st) ≫ graph (fun s : List (Int × Nat) × Nat => s.2)

/-- The derived program equals the hand-written `LC300.solve`: projecting `best` off the
    law-produced fold recovers the scalar LIS answer. -/
theorem derivedSolve_eq_solve : derivedSolve = LC300.solve := by
  show cataR (scalarAlg g st) ≫ graph (fun s : List (Int × Nat) × Nat => s.2) = LC300.solve
  rw [← lis_emerges]
  apply hom_ext; intro xs v
  show (∃ s, s = LC300.foldFn xs ∧ v = s.2) ↔ v = LC300.solveFn xs
  constructor
  · rintro ⟨s, hs, hv⟩; rw [hs] at hv; exact hv
  · intro hv; exact ⟨LC300.foldFn xs, rfl, hv⟩

/-! ## Correctness carries over from `L300.lean` (no re-proof of the optimization argument) -/

/-- **Headline.**  The law-derived tabulating fold computes the LIS optimum: `derivedSolve` relates
    each array `xs` to a value `m` that is an achievable increasing-subsequence length
    (`isSubseqInc`) and dominates every achievable increasing-subsequence length — i.e. the
    `≤`-maximum `max (≤) · Λ isSubseqInc`.  The optimization argument is REUSED from
    `LC300.solve_correct` (via `derivedSolve_eq_solve`), not re-proved. -/
theorem lis_derived_correct (xs : SnocList Int Int) :
    ∃ m, derivedSolve xs m ∧ LC300.isSubseqInc xs m ∧ ∀ k, LC300.isSubseqInc xs k → k ≤ m := by
  refine ⟨LC300.solveFn xs, ?_, (LC300.solve_correct xs).1, (LC300.solve_correct xs).2⟩
  rw [derivedSolve_eq_solve]
  exact rfl

/-! ## Running / cross-checking the emergent fold against `Fredy/L300.lean`

  As in `L198_derived`, the relational catamorphism `cataFold (scalarAlg …)` is not
  `decide`-computable (its `snoc` case is an existential over the carrier), so we `decide` the
  extensionally-equal computable witness `LC300.solveFn`/`LC300.foldFn` (equal by `lis_emerges`),
  and separately PROVE that the emergent fold relates a concrete array to `foldFn` of it. -/

-- The scalar answers `decide` on the computable witness (LeetCode 300 examples):
example : LC300.solveFn (LC300.ofList 10 [9, 2, 5, 3, 7, 101, 18]) = 4 := by decide
example : LC300.solveFn (LC300.ofList 0 [1, 0, 3, 2, 3]) = 4 := by decide
example : LC300.solveFn (LC300.ofList 7 [7, 7, 7, 7, 7, 7]) = 1 := by decide

/-- The emergent fold genuinely relates the array `[10,9,2,5,3,7,101,18]` to `foldFn` of it (whose
    `.2` is 4). -/
example :
    cataFold (scalarAlg g st) (LC300.ofList 10 [9, 2, 5, 3, 7, 101, 18])
      (LC300.foldFn (LC300.ofList 10 [9, 2, 5, 3, 7, 101, 18])) := by
  have h : (graph LC300.foldFn : dSL Int Int ⟶ ⟨List (Int × Nat) × Nat⟩)
      (LC300.ofList 10 [9, 2, 5, 3, 7, 101, 18])
      (LC300.foldFn (LC300.ofList 10 [9, 2, 5, 3, 7, 101, 18])) := rfl
  rw [lis_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC300D
