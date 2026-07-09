/-
  LeetCode 746 — Min Cost Climbing Stairs — DERIVED from the tupling law.

  `Fredy/L746.lean` WRITES the pair-carrying DP fold `foldFn` (state `(reachHere, reachPrev)`) by
  hand and then verifies it against the relational spec.  This file instead makes that fold EMERGE
  from `Freyd.Alg.RelSet.SL.tupling` (`Fredy/A6_8_Tupling.lean`), exactly as `L70_derived` /
  `L1137_derived` do for Fibonacci / Tribonacci — the recursion is NOT hand-written.

  The DP recurrence
    `minCost[i]     = cost[i]`                                        (single step)
    `minCost'[i]    = cost[i] + min(reachHere, reachPrev)`           (append a step)
  is a lockstep recursion on the state pair.  Read its base and step OFF `LC746.foldFn`:
    * base   `g x           = (x, 0)`                                   (= `foldFn (wrap x)`)
    * step   `step (h,p) c  = (c + imin h p, h)`                        (= `foldFn (snoc _ c)`)
  Then `SL.tupling g step LC746.foldFn` PRODUCES the pair fold:
    `graph LC746.foldFn = cataR (pairAlg g step)`
  the base/step conditions being `rfl` (they are literally the two `foldFn` equations).

  Unlike Fibonacci, the LeetCode answer is NOT a projection of the fold but the `imin` of BOTH
  carried components (step off from either of the last two steps).  So the derived solution is the
  emergent fold post-composed with `imin`:
    `derivedSolve := cataR (pairAlg g step) ≫ graph (fun p => imin p.1 p.2)`.
  We prove `derivedSolve = LC746.solve` (the emergent algebra `pairAlg g step` IS `LC746.alg`), and
  then inherit optimality — `⊑ spec` and `min (≤) · Λ costOf` — from the EXISTING `LC746`
  correctness theorems; nothing about optimality is re-proved here.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_8_Tupling
import Fredy.L746

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC746D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The base and step, read OFF `LC746.foldFn` -/

/-- The base of the emergent algebra: forced by `foldFn (wrap x) = (x, 0)`. -/
def g : Int → Int × Int := fun x => (x, 0)

/-- The step of the emergent algebra: forced by `foldFn (snoc xs c) = (c + imin h p, h)` where
    `(h, p) = foldFn xs` (`reachHere, reachPrev`). -/
def step : Int × Int → Int → Int × Int := fun st c => (c + LC746.imin st.1 st.2, st.1)

/-- The base condition IS the `wrap` equation of `foldFn` — definitional. -/
theorem foldFn_wrap : ∀ x : Int, LC746.foldFn (SnocList.wrap x) = g x := fun _ => rfl

/-- The step condition IS the `snoc` equation of `foldFn` — definitional. -/
theorem foldFn_snoc : ∀ (xs : SnocList Int Int) (c : Int),
    LC746.foldFn (SnocList.snoc xs c) = step (LC746.foldFn xs) c := fun _ _ => rfl

/-! ## The pair fold EMERGES via the tupling law -/

/-- The pair-carrying fold is PRODUCED by the tupling law from `g` and `step`; it was never written
    by hand.  `graph LC746.foldFn` equals the catamorphism of the emergent algebra
    `pairAlg g step = [ x ↦ (x,0), ((h,p),c) ↦ (c + imin h p, h) ]`. -/
theorem foldFn_derived :
    (graph LC746.foldFn : dSL Int Int ⟶ ⟨Int × Int⟩) = cataR (pairAlg g step) :=
  tupling g step LC746.foldFn foldFn_wrap foldFn_snoc

/-- The emergent algebra `pairAlg g step` is exactly `LC746.alg` (both are the graph of the same
    case split), so their catamorphisms coincide. -/
theorem pairAlg_eq_alg : pairAlg g step = LC746.alg := by
  apply hom_ext; rintro (l | ⟨p, e⟩) v <;> exact Iff.rfl

/-! ## The derived solution: emergent fold post-composed with `imin` -/

/-- **The derived program.**  Since the answer is the `imin` of the two carried components (not a
    projection), the solution is the emergent fold followed by `imin`. -/
def derivedSolve : LC746.Arr ⟶ LC746.dZ :=
  cataR (pairAlg g step) ≫ graph (fun p : Int × Int => LC746.imin p.1 p.2)

/-- The derived program equals the hand-written `LC746.solve`. -/
theorem derived_eq_solve : derivedSolve = LC746.solve := by
  show cataR (pairAlg g step) ≫ graph (fun p : Int × Int => LC746.imin p.1 p.2) = LC746.solve
  rw [pairAlg_eq_alg]; exact LC746.solve_eq_cata.symm

/-! ## Correctness — inherited from `LC746`, optimality NOT re-proved -/

/-- **Headline.**  The derived program (the emergent tupling fold post-composed with `imin`) equals
    `LC746.solve`, refines the specification (`⊑ spec`), and computes the `≤`-minimum achievable
    near-end landing cost (`min (≤) · Λ costOf`).  The `⊑ spec` and min facts are REUSED verbatim
    from `LC746.solve_le_spec` / `LC746.solve_correct` — no optimality argument is re-proved. -/
theorem mincost_derived_correct :
    derivedSolve = LC746.solve
      ∧ derivedSolve ⊑ LC746.spec
      ∧ ∀ xs : SnocList Int Int,
          LC746.costOf xs (LC746.solveFn xs)
            ∧ ∀ v, LC746.costOf xs v → LC746.solveFn xs ≤ v := by
  refine ⟨derived_eq_solve, ?_, fun xs => LC746.solve_correct xs⟩
  rw [derived_eq_solve]; exact LC746.solve_le_spec

/-! ## Running the derived program

  `derivedSolve` is a relational composition (its fold step is an existential), so it is not
  `decide`-computable directly.  We `decide` the extensionally-equal computable answer `solveFn`,
  and separately show `derivedSolve` genuinely relates a concrete array to that value (via
  `derived_eq_solve`). -/

example : LC746.solveFn (LC746.ofList 10 [15, 20]) = 15 := by decide
example : LC746.solveFn (LC746.ofList 1 [100, 1, 1, 1, 100, 1, 1, 100, 1]) = 6 := by decide
example : LC746.solveFn (LC746.ofList 5 []) = 0 := by decide

/-- The derived relation genuinely relates the concrete array to its answer `15`. -/
example : derivedSolve (LC746.ofList 10 [15, 20]) 15 := by
  rw [derived_eq_solve]; show (15 : Int) = LC746.solveFn (LC746.ofList 10 [15, 20]); decide

end Freyd.Alg.RelSet.LC746D
