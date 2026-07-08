/-
  LeetCode 70 — Climbing Stairs / Fibonacci — DERIVED from the tupling law.

  Unlike `Fredy/L70.lean` (which WRITES the pair-carrying fold `fibPair` by hand and then verifies
  it), this file makes the fold EMERGE.  The spec is the second-order recurrence
  `climb (n+2) = climb (n+1) + climb n` (`LC70.climb`, imported).  A second-order recurrence is
  NOT the catamorphism of `1 + X` on its own — it looks back two steps.  The tupling law
  (`Fredy/A6_8_Tupling.lean`) linearizes it:

    * pick the tupling ANSATZ  `pclimb d = (climb (natOf d), climb (natOf d + 1))`  (carry the pair
      of consecutive values), where `natOf : SnocList Unit Unit → ℕ` reads a snoc-list as `ℕ`
      (`SnocList Unit Unit` is the initial algebra of `1 + X`, i.e. `ℕ`);
    * COMPUTE its base and step — these are forced, not guessed:
        `pclimb (wrap ())   = (climb 0, climb 1)        = (1, 1)`          =: `gFib ()`
        `pclimb (snoc xs ()) = (climb (n+1), climb (n+2)) = (b, a + b)`     =: `stepFib (a,b) ()`
      the second component `climb (n+2) = climb (n+1) + climb n = b + a = a + b` is exactly the
      book recurrence (reordered by `Nat.add_comm`);
    * APPLY `tupling gFib stepFib pclimb` — the pair-carrying fold `cataR (pairAlg gFib stepFib)`
      is then PRODUCED by the law from `gFib`/`stepFib`; we did not write it.

  Projecting the first component recovers the scalar `climb`.  Mathlib-free; axioms of the
  headline ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_8_Tupling
import Fredy.L70

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LD70

open Freyd Freyd.Alg.RelSet.SL

/-! ## The tupling ANSATZ and its FORCED base/step

  `natOf : SnocList Unit Unit → ℕ` (`SnocList Unit Unit ≅ ℕ`) is shared from `A6_8_Tupling`. -/

/-- Carry the pair `(climb n, climb (n+1))` — the tupling ansatz for a second-order recurrence. -/
def pclimb (d : SnocList Unit Unit) : Nat × Nat :=
  (LC70.climb (natOf d), LC70.climb (natOf d + 1))

/-- The base of the emergent algebra: forced by `pclimb (wrap ()) = (climb 0, climb 1) = (1,1)`. -/
def gFib : Unit → Nat × Nat := fun _ => (1, 1)

/-- The step of the emergent algebra: forced by the book recurrence — carrying `(a,b)`, the next
    pair is `(b, a+b)` because `climb (n+2) = climb (n+1) + climb n`. -/
def stepFib : Nat × Nat → Unit → Nat × Nat := fun p _ => (p.2, p.1 + p.2)

/-- The base condition is a COMPUTATION, not a guess: `pclimb (wrap ()) = gFib ()`. -/
theorem pclimb_wrap : ∀ l : Unit, pclimb (SnocList.wrap l) = gFib l := by
  intro l; cases l; rfl

/-- The step condition is the book recurrence: `pclimb (snoc xs ()) = stepFib (pclimb xs) ()`.
    The only non-definitional move is `Nat.add_comm`, reordering `climb (n+1) + climb n` into the
    `a + b` shape of `stepFib`. -/
theorem pclimb_snoc (xs : SnocList Unit Unit) (e : Unit) :
    pclimb (SnocList.snoc xs e) = stepFib (pclimb xs) e := by
  cases e
  show (LC70.climb (natOf xs + 1), LC70.climb (natOf xs + 1) + LC70.climb (natOf xs))
      = (LC70.climb (natOf xs + 1), LC70.climb (natOf xs) + LC70.climb (natOf xs + 1))
  rw [Nat.add_comm (LC70.climb (natOf xs + 1)) (LC70.climb (natOf xs))]

/-! ## The fold EMERGES via the tupling law -/

/-- **Headline.**  The pair-carrying fold is PRODUCED by the tupling law from the base `gFib` and
    step `stepFib` — it was never written by hand.  `graph pclimb` equals the catamorphism of the
    emergent algebra `pairAlg gFib stepFib = [ () ↦ (1,1), ((a,b),()) ↦ (b, a+b) ]`. -/
theorem fib_derived_correct :
    (graph pclimb : dSL Unit Unit ⟶ ⟨Nat × Nat⟩) = cataR (pairAlg gFib stepFib) :=
  tupling gFib stepFib pclimb pclimb_wrap pclimb_snoc

/-- Projecting the first component of the emergent fold recovers the scalar spec `climb`:
    whatever pair the fold relates `d` to, its first component is `climb (natOf d)`. -/
theorem climb_derived (d : SnocList Unit Unit) (v : Nat × Nat)
    (hv : cataFold (pairAlg gFib stepFib) d v) : v.1 = LC70.climb (natOf d) := by
  have hgr : (graph pclimb : dSL Unit Unit ⟶ ⟨Nat × Nat⟩) d v := by
    rw [fib_derived_correct]; exact hv
  have hveq : v = pclimb d := hgr
  subst hveq
  rfl

/-- The scalar answer as a morphism: `graph (climb ∘ natOf) = cataR (pairAlg gFib stepFib) ≫ fst`. -/
theorem climb_scalar :
    (graph (fun d => (pclimb d).1) : dSL Unit Unit ⟶ ⟨Nat⟩)
      = cataR (pairAlg gFib stepFib) ≫ graph (Prod.fst : Nat × Nat → Nat) :=
  tupling_fst gFib stepFib pclimb pclimb_wrap pclimb_snoc

/-! ## Running / cross-checking the emergent fold against `Fredy/L70.lean`

  The relational catamorphism `cataFold (pairAlg …)` is not `decide`-computable (its `snoc` case
  is an existential over `ℕ × ℕ`), so we `decide` the extensionally-equal computable witness
  `pclimb` (equal by `fib_derived_correct`), and separately PROVE that the fold relates `s5` to
  `pclimb s5`.  `(pclimb 5).1 = 8` matches `LC70.solveFn 5 = 8`. -/

-- `snocs 5` is the datatype encoding of 5; `climb` is cheap at n = 5 (naive Fibonacci tree).
example : natOf (snocs 5) = 5 := by decide
example : (pclimb (snocs 5)).1 = 8 := by decide
example : (pclimb (snocs 5)).1 = LC70.solveFn 5 := by decide
example : (pclimb (snocs 5)) = (8, 13) := by decide

/-- The emergent fold genuinely relates `snocs 5` to the pair `pclimb (snocs 5)` (whose `.1` is 8). -/
example : cataFold (pairAlg gFib stepFib) (snocs 5) (pclimb (snocs 5)) := by
  have h : (graph pclimb : dSL Unit Unit ⟶ ⟨Nat × Nat⟩) (snocs 5) (pclimb (snocs 5)) := rfl
  rw [fib_derived_correct] at h
  exact h

end Freyd.Alg.RelSet.LD70
