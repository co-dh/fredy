/-
  LeetCode 20 — Valid Parentheses — DERIVED from the general snoc-fold law.

  `leet/L20.lean` writes the depth-scan fold `foldFn : SnocList Bool Bool → Int × Bool` by hand
  (state `(depth, ok)`) and verifies `solve_correct` by two invariant lemmas.  This file makes
  that SAME pair-carrying fold EMERGE from the general fold-uniqueness law
  `Freyd.Alg.RelSet.SL.snocFold_unique` (`AOP/A6_GenFold.lean`), which — unlike the product-only
  `tupling` law — states catamorphism uniqueness for an ARBITRARY carrier `C`; here `C := Int ×
  Bool` happens to be a product, but the law used is the general one.

  `foldFn`'s own defining equations (`leet/L20.lean`, `foldFn_wrap`/`foldFn_snoc_true`/
  `foldFn_snoc_false`) ARE the base/step of the emergent algebra — both hold by `rfl`, so nothing
  is guessed:

    * base   `g b       = (1, true)` if `b` (open) else `(0, false)`      = `foldFn (wrap b)`
    * step   `step (d,ok) b = (d+1, ok)` if `b` (open)
                            = `(d-1, ok && (1 ≤ d))` if not (close)        = `foldFn (snoc xs b)`
             with `(d, ok) = foldFn xs`.

  Feeding `g`/`step`/`foldFn` to `SL.snocFold_unique` PRODUCES the depth-scan fold as
  `cataR (scalarAlg g step)` — the recursion is never hand-written; it is the law's catamorphism.
  Projecting `proj (d, ok) := ok && decide (d = 0)` recovers the scalar decision `LC20.solve`, so
  the derived program `derivedSolve` equals the hand-written one, and the existing correctness
  (`LC20.solve_correct : validFn xs = true ↔ balancedP xs`, a genuine `Iff` — this is a DECISION
  problem, not an optimum) carries over unchanged.  Headline shape 3 (decision `b = true ↔ P`); no
  re-derivation of the `neverNegP`/`depthP` invariants.

  One structural pass over the bracket sequence: `O(n)` time, `O(1)` extra state (the pair
  `(depth, ok)`) — no efficiency trap (never `acc ++ [x]`; the carrier is a fixed-width pair).

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.  Routed only through `SL.snocFold_unique`
  (a plain uniqueness induction), never `cataR_eq_relCata` (which pulls `Classical.choice`).
-/
import AOP.A6_GenFold
import leet.L20

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC20D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The pair carrier and its FORCED base/step

  Carrier `C := Int × Bool` — the pair `(depth, ok)` `LC20.foldFn` already carries.  The base `g`
  and step `step` are read off `LC20.foldFn`'s own `wrap`/`snoc` equations verbatim. -/

/-- The base of the emergent algebra: `foldFn (wrap b) = (1, true)` if `b` is open, else
    `(0, false)`. -/
def g : Bool → Int × Bool := fun b => if b then (1, true) else (0, false)

/-- The step of the emergent algebra: carrying `(depth, ok)`, an open bracket increments the
    depth; a close bracket decrements it and requires the PRIOR depth `≥ 1` to stay `ok`. -/
def step : Int × Bool → Bool → Int × Bool :=
  fun st b => if b then (st.1 + 1, st.2) else (st.1 - 1, st.2 && decide (1 ≤ st.1))

/-- The base condition is a COMPUTATION, not a guess: `foldFn (wrap b) = g b`. -/
theorem foldFn_wrap : ∀ b : Bool, LC20.foldFn (SnocList.wrap b) = g b := fun b => rfl

/-- The step condition IS `foldFn`'s snoc equation: `foldFn (snoc xs b) = step (foldFn xs) b`. -/
theorem foldFn_snoc : ∀ (xs : SnocList Bool Bool) (b : Bool),
    LC20.foldFn (SnocList.snoc xs b) = step (LC20.foldFn xs) b := fun xs b => rfl

/-! ## The fold EMERGES via the general snoc-fold law -/

/-- **The derivation.**  The depth-scan fold is PRODUCED by `SL.snocFold_unique` from the base `g`
    and step `step` — it was never written as a recursion to be verified: `graph foldFn` equals
    the catamorphism of the emergent algebra `scalarAlg g step`. -/
theorem fold_derived :
    (graph LC20.foldFn : LC20.Toks ⟶ (⟨Int × Bool⟩ : RelSet.{0})) = cataR (scalarAlg g step) :=
  snocFold_unique g step LC20.foldFn foldFn_wrap foldFn_snoc

/-! ## Connecting the emergent fold back to `L20.solve` -/

/-- The final projection: a state `(depth, ok)` decides `true` iff it never went negative (`ok`)
    and ends exactly balanced (`depth = 0`) — `LC20.validFn`'s own defining expression. -/
def proj : Int × Bool → Bool := fun st => st.2 && decide (st.1 = 0)

/-- The derived allegory program: the emergent pair fold followed by `proj`. -/
def derivedSolve : LC20.Toks ⟶ LC20.dBool := cataR (scalarAlg g step) ≫ graph proj

/-- The derived solver IS `LC20.solve`: replacing the emergent catamorphism by `graph foldFn`
    (`fold_derived`) and composing with `proj` gives `graph (fun xs => proj (foldFn xs)) = graph
    validFn = solve`, since `proj (foldFn xs)` is `validFn xs` by definition. -/
theorem derivedSolve_eq_solve : derivedSolve = LC20.solve := by
  unfold derivedSolve
  rw [← fold_derived]
  apply hom_ext; intro xs b
  constructor
  · rintro ⟨v, hv, hb⟩
    show b = LC20.validFn xs
    rw [hb, hv]
    rfl
  · intro hb
    have hb' : b = LC20.validFn xs := hb
    exact ⟨LC20.foldFn xs, rfl, hb'⟩

/-! ## Correctness of the derived program, transported from `L20.solve_correct` -/

/-- **The Valid-Parentheses decision is the emergent pair-carrying catamorphism, and it is
    correct.**  The honest headline bundles:

    * `fold_derived` — `graph foldFn = cataR (scalarAlg g step)`: the depth-scan program IS the
      catamorphism over the carrier `Int × Bool`; and
    * the transported decision — for ANY state `v` the emergent fold relates a sequence `xs` to,
      its projection `proj v` decides validity, `proj v = true ↔ balancedP xs`.  Emergence pins
      `v = foldFn xs`, and `LC20.solve_correct` (the existing decision `Iff`, NOT re-proved here)
      finishes. -/
theorem valid_derived_correct :
    ((graph LC20.foldFn : LC20.Toks ⟶ (⟨Int × Bool⟩ : RelSet.{0})) = cataR (scalarAlg g step)) ∧
    (∀ (xs : SnocList Bool Bool) (v : Int × Bool),
        cataFold (scalarAlg g step) xs v → (proj v = true ↔ LC20.balancedP xs)) := by
  refine ⟨fold_derived, ?_⟩
  intro xs v hv
  have hgr : (graph LC20.foldFn : LC20.Toks ⟶ (⟨Int × Bool⟩ : RelSet.{0})) xs v := by
    rw [fold_derived]; exact hv
  have hveq : v = LC20.foldFn xs := hgr
  subst hveq
  exact LC20.solve_correct xs

/-! ## Running / cross-checking the emergent fold against `leet/L20.lean` -/

example : LC20.validFn (LC20.ofOpens true [false]) = true := by decide                 -- "()"
example : LC20.validFn (LC20.ofOpens true [true, false, false]) = true := by decide    -- "(())"
example : LC20.validFn (LC20.ofOpens true [true]) = false := by decide                 -- "(("

/-- The emergent fold genuinely relates the sequence `"(())"` to `foldFn` of it. -/
example :
    cataFold (scalarAlg g step) (LC20.ofOpens true [true, false, false])
      (LC20.foldFn (LC20.ofOpens true [true, false, false])) := by
  have h : (graph LC20.foldFn : LC20.Toks ⟶ (⟨Int × Bool⟩ : RelSet.{0}))
      (LC20.ofOpens true [true, false, false])
      (LC20.foldFn (LC20.ofOpens true [true, false, false])) := rfl
  rw [fold_derived] at h
  exact h

end Freyd.Alg.RelSet.LC20D
