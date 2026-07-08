/-
  LeetCode 1137 — N-th Tribonacci Number — DERIVED from the SAME binary tupling law.

  `Fredy/L70_derived.lean` linearized a second-order recurrence by carrying a PAIR; Tribonacci is
  third-order (`trib (n+3) = trib (n+2) + trib (n+1) + trib n`, `LC1137.trib`), so we carry a
  TRIPLE.  The tupling law (`Fredy/A6_8_Tupling.lean`) is unchanged — its carrier `C₁ × C₂` is
  taken with `C₁ = ℕ`, `C₂ = ℕ × ℕ`:

    * ansatz  `ptrib d = (trib (natOf d), trib (natOf d + 1), trib (natOf d + 2))`;
    * FORCED base/step (computed, not guessed):
        `ptrib (wrap ())    = (trib 0, trib 1, trib 2)          = (0, 1, 1)`        =: `gTrib ()`
        `ptrib (snoc xs ()) = (trib (n+1), trib (n+2), trib (n+3))
                            = (b, c, a + b + c)`                                    =: `stepTrib (a,b,c) ()`
      the last component `trib (n+3) = trib (n+2) + trib (n+1) + trib n = a + b + c` is the book
      recurrence (reordered by `Nat.add_comm`/`Nat.add_assoc`);
    * APPLY `tupling gTrib stepTrib ptrib` — the triple-carrying fold EMERGES from `gTrib`/`stepTrib`.

  Projecting the first component recovers the scalar `trib`.  Mathlib-free; headline axioms
  ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_8_Tupling
import Fredy.L1137

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LD1137

open Freyd Freyd.Alg.RelSet.SL

/-! ## The tupling ANSATZ and its FORCED base/step

  `natOf : SnocList Unit Unit → ℕ` (`SnocList Unit Unit ≅ ℕ`) is shared from `A6_8_Tupling`. -/

/-- Carry the triple `(trib n, trib (n+1), trib (n+2))` — the tupling ansatz one dimension up. -/
def ptrib (d : SnocList Unit Unit) : Nat × Nat × Nat :=
  (LC1137.trib (natOf d), LC1137.trib (natOf d + 1), LC1137.trib (natOf d + 2))

/-- The base of the emergent algebra: `ptrib (wrap ()) = (trib 0, trib 1, trib 2) = (0,1,1)`. -/
def gTrib : Unit → Nat × Nat × Nat := fun _ => (0, 1, 1)

/-- The step of the emergent algebra: carrying `(a,b,c)`, the next triple is `(b, c, a+b+c)`
    because `trib (n+3) = trib (n+2) + trib (n+1) + trib n`. -/
def stepTrib : Nat × Nat × Nat → Unit → Nat × Nat × Nat :=
  fun p _ => (p.2.1, p.2.2, p.1 + p.2.1 + p.2.2)

/-- The base condition, a COMPUTATION: `ptrib (wrap ()) = gTrib ()`. -/
theorem ptrib_wrap : ∀ l : Unit, ptrib (SnocList.wrap l) = gTrib l := by
  intro l; cases l; rfl

/-- The step condition IS the book recurrence: `ptrib (snoc xs ()) = stepTrib (ptrib xs) ()`.
    The only non-definitional move reorders `trib (n+2) + trib (n+1) + trib n` into the `a+b+c`
    shape of `stepTrib` (`Nat.add_comm`/`Nat.add_assoc`). -/
theorem ptrib_snoc (xs : SnocList Unit Unit) (e : Unit) :
    ptrib (SnocList.snoc xs e) = stepTrib (ptrib xs) e := by
  cases e
  show (LC1137.trib (natOf xs + 1), LC1137.trib (natOf xs + 2),
        LC1137.trib (natOf xs + 2) + LC1137.trib (natOf xs + 1) + LC1137.trib (natOf xs))
      = (LC1137.trib (natOf xs + 1), LC1137.trib (natOf xs + 2),
        LC1137.trib (natOf xs) + LC1137.trib (natOf xs + 1) + LC1137.trib (natOf xs + 2))
  rw [Nat.add_comm (LC1137.trib (natOf xs + 2) + LC1137.trib (natOf xs + 1)) (LC1137.trib (natOf xs)),
      Nat.add_comm (LC1137.trib (natOf xs + 2)) (LC1137.trib (natOf xs + 1)),
      ← Nat.add_assoc (LC1137.trib (natOf xs)) (LC1137.trib (natOf xs + 1)) (LC1137.trib (natOf xs + 2))]

/-! ## The fold EMERGES via the SAME binary tupling law -/

/-- **Headline.**  The triple-carrying fold is PRODUCED by the tupling law from `gTrib`/`stepTrib`;
    `graph ptrib` equals the catamorphism of the emergent algebra
    `pairAlg gTrib stepTrib = [ () ↦ (0,1,1), ((a,b,c),()) ↦ (b, c, a+b+c) ]`. -/
theorem trib_derived_correct :
    (graph ptrib : dSL Unit Unit ⟶ ⟨Nat × Nat × Nat⟩) = cataR (pairAlg gTrib stepTrib) :=
  tupling gTrib stepTrib ptrib ptrib_wrap ptrib_snoc

/-- Projecting the first component of the emergent fold recovers the scalar spec `trib`. -/
theorem trib_derived (d : SnocList Unit Unit) (v : Nat × Nat × Nat)
    (hv : cataFold (pairAlg gTrib stepTrib) d v) : v.1 = LC1137.trib (natOf d) := by
  have hgr : (graph ptrib : dSL Unit Unit ⟶ ⟨Nat × Nat × Nat⟩) d v := by
    rw [trib_derived_correct]; exact hv
  have hveq : v = ptrib d := hgr
  subst hveq
  rfl

/-- The scalar answer as a morphism: `graph (trib ∘ natOf) = cataR (pairAlg gTrib stepTrib) ≫ fst`. -/
theorem trib_scalar :
    (graph (fun d => (ptrib d).1) : dSL Unit Unit ⟶ ⟨Nat⟩)
      = cataR (pairAlg gTrib stepTrib) ≫ graph (Prod.fst : Nat × Nat × Nat → Nat) :=
  tupling_fst gTrib stepTrib ptrib ptrib_wrap ptrib_snoc

/-! ## Running / cross-checking the emergent fold against `Fredy/L1137.lean`

  As in `L70_derived`, the relational catamorphism is not `decide`-computable, so we exercise the
  extensionally-equal computable witness `ptrib` and PROVE the fold relates `snocs 25` to
  `ptrib (snocs 25)`.  NOTE: `ptrib` carries the NAIVE exponential `trib`, so `decide`-ing
  `(ptrib (snocs 25)).1` directly would evaluate `trib 25` naively (infeasible).  We therefore
  (a) `decide` the emergent scalar directly only at a small `n = 4`, and (b) reach `n = 25` by
  routing through `LC1137.solveFn` (the O(n) tabulated solver), whose value `decide`s fast. -/

-- (a) Direct decide of the emergent scalar at small n (naive `trib 4` is cheap):
example : natOf (snocs 4) = 4 := by decide
example : (ptrib (snocs 4)).1 = 4 := by decide          -- matches LC1137.solveFn 4 = 4

-- (b) The emergent scalar equals the L1137 O(n) solver everywhere; hence 1389537 at n = 25:
example (d : SnocList Unit Unit) : (ptrib d).1 = LC1137.solveFn (natOf d) :=
  (LC1137.solve_correct (natOf d)).symm

example : (ptrib (snocs 25)).1 = 1389537 := by
  have h : (ptrib (snocs 25)).1 = LC1137.solveFn (natOf (snocs 25)) :=
    (LC1137.solve_correct (natOf (snocs 25))).symm
  rw [h]; decide

/-- The emergent fold genuinely relates `snocs 25` to `ptrib (snocs 25)` (whose `.1` is 1389537). -/
example : cataFold (pairAlg gTrib stepTrib) (snocs 25) (ptrib (snocs 25)) := by
  have h : (graph ptrib : dSL Unit Unit ⟶ ⟨Nat × Nat × Nat⟩) (snocs 25) (ptrib (snocs 25)) := rfl
  rw [trib_derived_correct] at h
  exact h

end Freyd.Alg.RelSet.LD1137
