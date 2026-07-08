/-
  LeetCode 91 — Decode Ways — DERIVED from the tupling law.

  Unlike `Fredy/L91.lean` (which WRITES the triple-carrying fold `foldFn` by hand and then verifies
  it against the specification), this file makes the fold EMERGE.  We start from the SPECIFICATION —
  the mutually-recursive TEXTBOOK decode-ways recurrence `decode`/`decodePrev` (plus the trivial
  `lastDigit`), all imported from `Fredy/L91.lean`.  That recurrence is exponential: `decode (snoc
  xs d)`'s "the last group is a valid pair" branch calls `decodePrev xs`, which peels one further
  digit, so each step recurses into two overlapping smaller lists.  Neither `decode` nor
  `decodePrev` is on its own the catamorphism of `F X = ℕ + X × ℕ` — each looks back further than
  one step.  The tupling law (`Fredy/A6_8_Tupling.lean`, `SL.tupling`) linearizes them:

    * pick the tupling ANSATZ  `p xs = (decode xs, decodePrev xs, lastDigit xs)`  (carry the THREE
      quantities the recurrence cross-references).  This is a triple `ℕ × (ℕ × ℕ)`, i.e. `C₁ = ℕ`
      (the answer `ways`), `C₂ = ℕ × ℕ` (`prevWays` and `lastDigit`).  Choosing WHICH three
      quantities to tuple is the whole insight;
    * COMPUTE its base and step — these are FORCED by the recurrence, not guessed:
        `p (wrap d)   = (decode (wrap d), decodePrev (wrap d), lastDigit (wrap d))
                      = (if 1≤d≤9 then 1 else 0, 1, d)`                         =: `gDecode d`
        `p (snoc xs d) = (decode (snoc xs d), decode xs, d)
                      = stepDecode (p xs) d`  where, writing `(w,wp,ld) := p xs`,
          `stepDecode (w,wp,ld) d = (single + double, w, d)`,
          `single = if 1≤d≤9 then w else 0`, `double = if 10 ≤ ld*10+d ≤ 26 then wp else 0`
      the first component is exactly the decode-ways recurrence with `decode xs`, `decodePrev xs`
      substituted (both READ OFF `p xs`), so the second-order dependence collapses to first order;
    * APPLY `tupling gDecode stepDecode p` — the triple-carrying fold `cataR (pairAlg gDecode
      stepDecode)` is then PRODUCED by the law from `gDecode`/`stepDecode`; we did not write it.

  Projecting the first component recovers the scalar answer `decode` (`decode_scalar`), the derived
  analogue of `L91.solve_eq_cata`.  The emergent algebra equals `Fredy/L91.lean`'s hand-written
  `alg`/`foldFn` DEFINITIONALLY (`gDecode`/`stepDecode` are exactly `foldFn`'s own defining
  equations — `foldFn_base_eq`, `foldFn_step_eq`, `pairAlg_eq_alg`, all `rfl`).

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound} (the tupling law is choice-free).
-/
import Fredy.A6_8_Tupling
import Fredy.L91

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC91D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The tupling ANSATZ and its FORCED base/step

  The three quantities the naive recurrence cross-references are `decode`, `decodePrev` and
  `lastDigit` (all from `Fredy/L91.lean`).  Tupling them into one state is the insight. -/

/-- Carry the triple `(decode xs, decodePrev xs, lastDigit xs)` — the tupling ansatz for the
    (second-order, mutually recursive) decode-ways recurrence.  `C₁ = ℕ` is `ways`, `C₂ = ℕ × ℕ`
    is `(prevWays, lastDigit)`. -/
def p (xs : SnocList Nat Nat) : Nat × Nat × Nat :=
  (LC91.decode xs, LC91.decodePrev xs, LC91.lastDigit xs)

/-- The base of the emergent algebra: forced by
    `p (wrap d) = (decode (wrap d), decodePrev (wrap d), lastDigit (wrap d)) = (if 1≤d≤9 then 1 else 0, 1, d)`. -/
def gDecode : Nat → Nat × Nat × Nat := fun d => ((if 1 ≤ d ∧ d ≤ 9 then 1 else 0), 1, d)

/-- The step of the emergent algebra: forced by the decode-ways recurrence.  Carrying `(w,wp,ld) =
    (decode xs, decodePrev xs, lastDigit xs)`, the next triple is `(single + double, w, d)` with
    `single = if 1≤d≤9 then w else 0` (single-digit group) and `double = if 10 ≤ ld*10+d ≤ 26 then
    wp else 0` (two-digit group) — the two branches of the recurrence, now first-order. -/
def stepDecode : Nat × Nat × Nat → Nat → Nat × Nat × Nat := fun st d =>
  let (w, wp, ld) := st
  let single := if 1 ≤ d ∧ d ≤ 9 then w else 0
  let two := ld * 10 + d
  let double := if 10 ≤ two ∧ two ≤ 26 then wp else 0
  (single + double, w, d)

/-- The base condition is a COMPUTATION, not a guess: `p (wrap d) = gDecode d`.  Both sides unfold to
    `((if 1≤d≤9 then 1 else 0), 1, d)` — `decode (wrap d)`, `decodePrev (wrap d) = 1`,
    `lastDigit (wrap d) = d` are the wrap equations of the imported spec. -/
theorem p_wrap : ∀ l : Nat, p (SnocList.wrap l) = gDecode l := fun l => rfl

/-- The step condition is the decode-ways recurrence made first-order: `p (snoc xs d) = stepDecode
    (p xs) d`.  It holds definitionally — `decode (snoc xs d)` unfolds to `single + double` with
    `decode xs`/`decodePrev xs`/`lastDigit xs` read off `p xs`, `decodePrev (snoc xs d) = decode xs`,
    `lastDigit (snoc xs d) = d`; the tupling has REMOVED the second-order recursion. -/
theorem p_snoc (xs : SnocList Nat Nat) (d : Nat) :
    p (SnocList.snoc xs d) = stepDecode (p xs) d := rfl

/-! ## The fold EMERGES via the tupling law -/

/-- **Headline.**  The triple-carrying fold is PRODUCED by the tupling law from the base `gDecode`
    and step `stepDecode` — it was never written by hand.  `graph p` equals the catamorphism of the
    emergent algebra `pairAlg gDecode stepDecode`. -/
theorem decode_derived_correct :
    (graph p : LC91.Digits ⟶ (⟨Nat × Nat × Nat⟩ : RelSet.{0})) = cataR (pairAlg gDecode stepDecode) :=
  tupling gDecode stepDecode p p_wrap p_snoc

/-! ## The emergent algebra IS `Fredy/L91.lean`'s hand-written fold (definitionally) -/

/-- `gDecode` is `foldFn`'s own `wrap` equation, `rfl`: the base the law needs was already L91's. -/
theorem foldFn_base_eq (d : Nat) : LC91.foldFn (SnocList.wrap d) = gDecode d := rfl

/-- `stepDecode` is `foldFn`'s own `snoc` equation, `rfl`: `foldFn (snoc xs d) = stepDecode (foldFn
    xs) d`.  `stepDecode`'s body is textually `foldFn`'s recursive body, so the fold the law produces
    steps exactly as L91's hand-written `foldFn`. -/
theorem foldFn_step_eq (xs : SnocList Nat Nat) (d : Nat) :
    LC91.foldFn (SnocList.snoc xs d) = stepDecode (LC91.foldFn xs) d := rfl

/-- The whole emergent algebra equals L91's hand-written algebra `alg`: `pairAlg gDecode stepDecode
    = LC91.alg`.  Each branch is definitional (`Iff.rfl`) — `gDecode`/`stepDecode` reproduce
    `algFn`'s two cases exactly; `hom_ext` is needed only because the two `graph`ed case-splits
    compile their `match` differently as whole terms (so `rfl` on the packaged morphism does not
    fire, but every fibre `r = gDecode d ↔ r = algFn (inl d)` / `r = stepDecode st d ↔ r = algFn
    (inr (st,d))` is `Iff.rfl`). -/
theorem pairAlg_eq_alg : pairAlg gDecode stepDecode = LC91.alg := by
  apply hom_ext; intro u r
  cases u with
  | inl d => exact Iff.rfl
  | inr q => obtain ⟨st, d⟩ := q; exact Iff.rfl

/-! ## Projecting the first component recovers the scalar answer `decode` -/

/-- Whatever triple the emergent fold relates `xs` to, its first component is `decode xs` — the
    scalar decode-ways count.  (Relational form, since `cataFold (pairAlg …)` is a relation.) -/
theorem decode_pointwise (xs : SnocList Nat Nat) (v : Nat × Nat × Nat)
    (hv : cataFold (pairAlg gDecode stepDecode) xs v) : v.1 = LC91.decode xs := by
  have hgr : (graph p : LC91.Digits ⟶ (⟨Nat × Nat × Nat⟩ : RelSet.{0})) xs v := by
    rw [decode_derived_correct]; exact hv
  have hveq : v = p xs := hgr
  subst hveq
  rfl

/-- **The scalar answer as a morphism** (derived analogue of `L91.solve_eq_cata`): the graph of
    `decode` is the emergent fold followed by the projection onto `ways`,
    `graph decode = cataR (pairAlg gDecode stepDecode) ≫ fst`.  Produced by projecting the tupling
    law's first component (`tupling_fst`); `(p d).1 = decode d` definitionally. -/
theorem decode_scalar :
    (graph LC91.decode : LC91.Digits ⟶ LC91.dN)
      = cataR (pairAlg gDecode stepDecode) ≫ graph (Prod.fst : Nat × Nat × Nat → Nat) :=
  tupling_fst gDecode stepDecode p p_wrap p_snoc

/-! ## Running / cross-checking the emergent fold against `Fredy/L91.lean`

  The relational catamorphism `cataFold (pairAlg …)` is not `decide`-computable (its `snoc` case is
  an existential over `ℕ × ℕ × ℕ`), so we `decide` the extensionally-equal computable witness `p`
  (equal by `decode_derived_correct`), and separately PROVE that the fold relates the sample list to
  `p` of it.  `(p (ofList 2 [2,6])).1 = 3` matches `LC91.solveFn (ofList 2 [2,6]) = 3`, the sample
  from `Fredy/L91.lean`. -/

-- The ansatz's first component (= `decode`) agrees with L91's hand-written `solveFn` on the samples.
example : (p (LC91.ofList 2 [2, 6])).1 = LC91.solveFn (LC91.ofList 2 [2, 6]) := by decide
example : (p (LC91.ofList 2 [2, 6])).1 = 3 := by decide
example : (p (LC91.ofList 1 [2])).1 = LC91.solveFn (LC91.ofList 1 [2]) := by decide
example : (p (LC91.ofList 1 [0])).1 = LC91.solveFn (LC91.ofList 1 [0]) := by decide

/-- The emergent fold genuinely relates `ofList 2 [2,6]` to the triple `p (ofList 2 [2,6])` (whose
    `.1` is the decode count 3). -/
example : cataFold (pairAlg gDecode stepDecode) (LC91.ofList 2 [2, 6]) (p (LC91.ofList 2 [2, 6])) := by
  have h : (graph p : LC91.Digits ⟶ (⟨Nat × Nat × Nat⟩ : RelSet.{0}))
      (LC91.ofList 2 [2, 6]) (p (LC91.ofList 2 [2, 6])) := rfl
  rw [decode_derived_correct] at h
  exact h

end Freyd.Alg.RelSet.LC91D
