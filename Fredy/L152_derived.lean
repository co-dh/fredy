/-
  LeetCode 152 — Maximum Product Subarray — DERIVED from the tupling law.

  Unlike `Fredy/L152.lean` (which WRITES the triple-carrying fold `foldFn` by hand and then verifies
  it against the specification `subProd`), this file makes the fold EMERGE via the tupling law
  (`Fredy/A6_8_Tupling.lean`, `SL.tupling`).  The Maximum-Product sweep must track THREE running
  quantities at once — the running minimum product `minEnd`, the running maximum product `maxEnd`
  (both needed because a negative multiplicand swaps `min ↔ max`), and the best-so-far `best`.  So
  this is the L91-shaped case: a triple carrier `ℤ × ℤ × ℤ = ℤ × (ℤ × ℤ)`, i.e. `C₁ = ℤ` (the
  answer `best`), `C₂ = ℤ × ℤ` (`minEnd` and `maxEnd`).

  The tupling law linearizes the sweep:

    * pick the tupling ANSATZ `(minEnd, maxEnd, best)` — the three quantities the sweep
      cross-references (each new step reads all three, and `best` reads the freshly-computed
      `maxEnd`).  Carrying them in one state is the whole move;
    * COMPUTE its base and step — FORCED by the recurrence, not guessed:
        `wrap x   ↦ (x, x, x)`                                                   =: `g x`
        `snoc st p ↦ (imin p (imin (m*p) (M*p)), imax p (imax (m*p) (M*p)), imax b hi)`
      where `(m, M, b) := st` and `hi := imax p (imax (m*p) (M*p))`             =: `step st p`
      — exactly the two branches of the maximum-product recurrence, read off `st`;
    * APPLY `tupling g step LC152.foldFn` — the triple-carrying fold `cataR (pairAlg g step)` is
      then PRODUCED by the law from `g`/`step`; we did not write it.  `g`/`step` are exactly
      `foldFn`'s own defining equations, so `hwrap`/`hsnoc` hold by `rfl`.

  Projecting the third component (`best`) recovers the scalar answer `solve`, and reusing
  `Fredy/L152.lean`'s optimality proof (`solve_correct`) — NOT re-proved here — shows the emergent
  program computes the maximum achievable subarray product.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound} (the tupling law is choice-free).
-/
import Fredy.A6_8_Tupling
import Fredy.L152

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC152D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The tupling ANSATZ and its FORCED base/step

  The three quantities the naive sweep cross-references are `minEnd`, `maxEnd`, `best`.  Tupling
  them into one triple `ℤ × ℤ × ℤ` (`C₁ = ℤ` is `best`, `C₂ = ℤ × ℤ` is `(minEnd, maxEnd)`) is the
  insight.  The ansatz itself is `Fredy/L152.lean`'s `foldFn` (imported), so we read the base/step
  straight off its defining equations. -/

/-- The base of the emergent algebra: forced by `foldFn (wrap x) = (x, x, x)`. -/
def g : Int → Int × Int × Int := fun x => (x, x, x)

/-- The step of the emergent algebra: forced by the maximum-product recurrence.  Carrying
    `(m, M, b) = (minEnd, maxEnd, best)`, the new candidate suffix products are `p`, `m*p`, `M*p`;
    `lo`/`hi` take their `min`/`max`, and `best` becomes `imax b hi`.  (`imin`/`imax` reused from
    `Fredy/L152.lean`.) -/
def step : Int × Int × Int → Int → Int × Int × Int := fun st p =>
  let m := st.1; let M := st.2.1; let b := st.2.2
  let lo := LC152.imin p (LC152.imin (m*p) (M*p))
  let hi := LC152.imax p (LC152.imax (m*p) (M*p))
  (lo, hi, LC152.imax b hi)

/-- The base condition is a COMPUTATION, not a guess: `foldFn (wrap x) = g x`.  Both sides are
    `(x, x, x)` — `foldFn`'s own `wrap` equation. -/
theorem hwrap : ∀ x : Int, LC152.foldFn (SnocList.wrap x) = g x := fun x => rfl

/-- The step condition is the maximum-product recurrence made first-order:
    `foldFn (snoc xs p) = step (foldFn xs) p`.  It holds definitionally — `step`'s body is textually
    `foldFn`'s recursive `snoc` body with `st := foldFn xs`. -/
theorem hsnoc : ∀ (xs : SnocList Int Int) (p : Int),
    LC152.foldFn (SnocList.snoc xs p) = step (LC152.foldFn xs) p := fun xs p => rfl

/-! ## The fold EMERGES via the tupling law -/

/-- **The fold is PRODUCED by the tupling law** from the base `g` and step `step` — it was never
    written by hand.  `graph foldFn` equals the catamorphism of the emergent algebra
    `pairAlg g step`. -/
theorem foldFn_derived :
    (graph LC152.foldFn : LC152.Arr ⟶ (⟨Int × Int × Int⟩ : RelSet.{0})) = cataR (pairAlg g step) :=
  tupling g step LC152.foldFn hwrap hsnoc

/-! ## Projecting `best` recovers the scalar solution -/

/-- The derived program: the emergent triple-fold followed by the projection onto `best` (the third
    component).  This is `Fredy/L152.lean`'s `solve`, but with the fold PRODUCED by the tupling law
    rather than written by hand. -/
def derivedSolve : LC152.Arr ⟶ LC152.dZ :=
  cataR (pairAlg g step) ≫ graph (fun t : Int × Int × Int => t.2.2)

/-- The derived program equals `Fredy/L152.lean`'s hand-written `solve`.  `cataR (pairAlg g step)`
    is `graph foldFn` (the tupling law `foldFn_derived`), and post-composing the `best` projection
    reproduces `graph solveFn = solve`. -/
theorem derivedSolve_eq_solve : derivedSolve = LC152.solve := by
  show cataR (pairAlg g step) ≫ graph (fun t : Int × Int × Int => t.2.2) = LC152.solve
  rw [← foldFn_derived]
  apply hom_ext; intro xs v
  show (∃ w, w = LC152.foldFn xs ∧ v = w.2.2) ↔ v = LC152.solveFn xs
  constructor
  · rintro ⟨w, rfl, hv⟩; exact hv
  · intro hv; exact ⟨LC152.foldFn xs, rfl, hv⟩

/-- The derived program refines the specification (`derivedSolve ⊑ spec`): every value it returns is
    an achievable subarray product.  Reuses `L152.solve_le_spec` through `derivedSolve_eq_solve`. -/
theorem derivedSolve_le_spec : derivedSolve ⊑ LC152.spec := by
  rw [derivedSolve_eq_solve]; exact LC152.solve_le_spec

/-- **LeetCode 152, derived by tupling.**  The emergent program equals the hand-written `solve`, and
    (reusing `L152.solve_correct`, NOT re-proved) its output is an achievable subarray product AND is
    the `≤`-greatest such — i.e. `max (≤) · Λ subProd`.  The load-bearing new content is
    `foldFn_derived`: the triple-carrying sweep is PRODUCED by the tupling law, not written. -/
theorem maxprod_derived_correct :
    derivedSolve = LC152.solve
    ∧ ∀ xs : SnocList Int Int,
        LC152.subProd xs (LC152.solveFn xs) ∧ ∀ v, LC152.subProd xs v → v ≤ LC152.solveFn xs :=
  ⟨derivedSolve_eq_solve, LC152.solve_correct⟩

/-! ## Running / cross-checking the emergent fold against `Fredy/L152.lean`

  The relational catamorphism `cataFold (pairAlg …)` is not `decide`-computable (its `snoc` case is
  an existential over `ℤ × ℤ × ℤ`), so we `decide` the extensionally-equal computable witness
  `foldFn` (equal by `foldFn_derived`) and separately PROVE that the fold relates a sample list to
  `foldFn` of it. -/

example : LC152.solveFn (LC152.ofList 2 [3, -2, 4]) = 6 := by decide
example : LC152.solveFn (LC152.ofList (-2) [3, -4]) = 24 := by decide
example : (LC152.foldFn (LC152.ofList (-2) [0, -1])).2.2 = 0 := by decide

/-- The emergent fold genuinely relates `ofList 2 [3,-2,4]` to `foldFn` of it (whose `.2.2` is the
    answer 6). -/
example : cataFold (pairAlg g step) (LC152.ofList 2 [3, -2, 4]) (LC152.foldFn (LC152.ofList 2 [3, -2, 4])) := by
  have h : (graph LC152.foldFn : LC152.Arr ⟶ (⟨Int × Int × Int⟩ : RelSet.{0}))
      (LC152.ofList 2 [3, -2, 4]) (LC152.foldFn (LC152.ofList 2 [3, -2, 4])) := rfl
  rw [foldFn_derived] at h
  exact h

end Freyd.Alg.RelSet.LC152D
