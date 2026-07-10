/-
  LeetCode 66 — Plus One — DERIVED as a PARAMORPHISM-AS-FOLD via `CL.consFold_unique`.

  `Fredy/L66.lean` hand-writes `plusOneRev`, the carry-ripple over the LITTLE-ENDIAN digit list:

    `plusOneRev [] = [1]`,  `plusOneRev (d :: ds) = if d + 1 = 10 then 0 :: plusOneRev ds else
    (d + 1) :: ds`.

  The ELSE branch returns `(d + 1) :: ds` — the ORIGINAL, untouched tail `ds`, not a recursive call
  on it. That makes `plusOneRev` a genuine PARAMORPHISM (para, not cata): the step needs the SUBTERM
  `ds` itself, not merely its fold `plusOneRev ds`. A bare `E → C → C` step, fed only the folded
  answer on the tail, cannot express "stop consuming/propagating carry and hand back the raw tail
  unchanged" — the raw tail has already been thrown away by the time a plain fold reaches the step.

  **The paramorphism-as-fold trick**: widen the carrier to `C := List Int × List Int`, pairing
  (result-so-far, the tail RECONSTRUCTED alongside it).  `pr ds = (plusOneRev ds, ds)` — the second
  slot is a bookkeeping copy of the very list being consumed, so the ELSE branch can read it off the
  carrier instead of recursing.  `pr` now obeys a bona fide `E → C → C` step (`st`), and
  `CL.consFold_unique` (`Fredy/A6_GenFold.lean`) EMITS `pr` as `cataR (consScalarAlg g st)` — one
  structural pass, O(n), the fold never hand-written as a `cataR`.

  Correctness (`valueLE`/`value`) is REUSED, not re-derived: `pr_ofList` bridges the emergent fold's
  first coordinate back to `L66.plusOneRev` verbatim, and `L66.valueLE_plusOneRev` /
  `L66.plusOne_correct` finish the job unchanged.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.A6_ConsList
import Fredy.L66

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC66D

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.LC66

/-! ## The paramorphism ansatz: carry `(result-so-far, rebuilt raw tail)` -/

/-- The base of the emergent algebra: `pr (wrap ())` must equal `(plusOneRev [], [])`. -/
def g : Unit → List Int × List Int := fun _ => ([1], [])

/-- The step of the emergent algebra. Carrying `(r, raw)` for the tail (`r` = its `plusOneRev`,
    `raw` = the tail ITSELF, reconstructed), the step for `cons d ‹tail›` is: on carry
    (`d + 1 = 10`), roll to `0` and keep propagating (`0 :: r`); otherwise STOP — bump `d` and hand
    back the raw tail `raw` unchanged, exactly `L66.plusOneRev`'s else-branch, now legal because `raw`
    is sitting on the carrier instead of needing a fresh recursive call.  Either way the raw slot
    itself always just grows by `d`. -/
def st : Int → List Int × List Int → List Int × List Int :=
  fun d rp => (if d + 1 = 10 then 0 :: rp.1 else (d + 1) :: rp.2, d :: rp.2)

/-- `pr`: carry `(plusOneRev ‹suffix›, ‹suffix›)` down the `ConsList`, mirroring `wrap`/`cons`
    directly so `pr_wrap`/`pr_cons` below are `rfl`. -/
def pr : ConsList Unit Int → List Int × List Int
  | ConsList.wrap u => g u
  | ConsList.cons d ds => st d (pr ds)

/-- The step condition (a COMPUTATION, `rfl`): `pr (wrap u) = g u`. -/
theorem pr_wrap (u : Unit) : pr (ConsList.wrap u) = g u := rfl

/-- The step condition (a COMPUTATION, `rfl`): `pr (cons d ds) = st d (pr ds)`. -/
theorem pr_cons (d : Int) (ds : ConsList Unit Int) : pr (ConsList.cons d ds) = st d (pr ds) := rfl

/-! ## The fold EMERGES via the general cons-list fold-uniqueness law -/

/-- **`pr` EMERGES as a catamorphism.** `graph pr` equals the catamorphism of the emergent algebra
    `consScalarAlg g st = [ wrap ↦ g, (d, c) ↦ st d c ]`, PRODUCED by `CL.consFold_unique` from the
    forced base `g` and step `st`. The pair-carrying fold implementing the paramorphism was never
    written by hand as a `cataR` term. -/
theorem plusOneRev_emerges :
    (graph pr : dCL Unit Int ⟶ ⟨List Int × List Int⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st pr pr_wrap pr_cons

/-! ## Bridge: `pr` on `ofList xs` reconstructs `(L66.plusOneRev xs, xs)` -/

/-- **The bridge.** Folding `pr` over the SHARED `CL.ofList xs` recovers exactly the pair
    `(plusOneRev xs, xs)`: the first slot is `L66.plusOneRev`'s own answer, the second is the raw
    input, faithfully reconstructed step by step. Proved by induction on `xs`, matching `st`'s two
    branches against `plusOneRev`'s own `if`. -/
theorem pr_ofList (xs : List Int) : pr (ofList xs) = (plusOneRev xs, xs) := by
  induction xs with
  | nil => rfl
  | cons d ds ih =>
    show st d (pr (ofList ds)) = (plusOneRev (d :: ds), d :: ds)
    rw [ih]
    by_cases hd : d + 1 = 10
    · simp only [st, plusOneRev, if_pos hd]
    · simp only [st, plusOneRev, if_neg hd]

/-! ## Correctness of the emergent fold, reused from `L66.valueLE_plusOneRev` -/

/-- **Correctness of the derived fold** (the derived analogue of `L66.valueLE_plusOneRev`): for ANY
    pair `v` the emergent fold relates `ds` to, `v.1`'s little-endian value is `ds`'s plus one. The
    emergence (`plusOneRev_emerges`) pins `v = pr (ofList ds)`; `pr_ofList` identifies `v.1` with
    `L66.plusOneRev ds`; `L66.valueLE_plusOneRev` finishes it — no fresh induction. -/
theorem plusOneRev_derived_correct (ds : List Int) (v : List Int × List Int)
    (hv : cataFold (consScalarAlg g st) (ofList ds) v) :
    valueLE v.1 = valueLE ds + 1 := by
  have hgr : (graph pr : dCL Unit Int ⟶ ⟨List Int × List Int⟩) (ofList ds) v := by
    rw [plusOneRev_emerges]; exact hv
  have hveq : v = pr (ofList ds) := hgr
  rw [hveq, pr_ofList]
  exact valueLE_plusOneRev ds

/-! ## `Rel(Set)` packaging: the derived `plusOneFn`, reusing `L66.plusOne_correct` -/

/-- The derived, LITTLE-ENDIAN increment: read off `pr`'s first slot after reshaping onto `ConsList`
    via the shared `CL.ofList`. -/
def derivedPlusOneRev (xs : List Int) : List Int := (pr (ofList xs)).1

/-- `derivedPlusOneRev` agrees with `L66.plusOneRev` pointwise — immediate from `pr_ofList`. -/
theorem derivedPlusOneRev_eq (xs : List Int) : derivedPlusOneRev xs = plusOneRev xs := by
  show (pr (ofList xs)).1 = plusOneRev xs
  rw [pr_ofList]

/-- **The derived program**: increment a BIG-ENDIAN digit list by one — reverse to little-endian,
    run the emergent fold, reverse back. Mirrors `L66.plusOneFn` verbatim, `plusOneRev` replaced by
    `derivedPlusOneRev`. -/
def derivedPlusOneFn (xs : List Int) : List Int := (derivedPlusOneRev xs.reverse).reverse

/-- `derivedPlusOneFn` agrees with `L66.plusOneFn` pointwise. -/
theorem derivedPlusOneFn_eq (xs : List Int) : derivedPlusOneFn xs = plusOneFn xs := by
  show (derivedPlusOneRev xs.reverse).reverse = (plusOneRev xs.reverse).reverse
  rw [derivedPlusOneRev_eq]

/-- The derived program as a morphism `dDigits ⟶ dDigits` in `Rel(Set)`; it equals `L66.solve`. -/
def derivedSolve : dDigits ⟶ dDigits := graph derivedPlusOneFn

/-- The derived morphism IS `L66.solve` — the paramorphism-as-fold derivation changes nothing
    observable. -/
theorem derivedSolve_eq_solve : derivedSolve = solve :=
  congrArg graph (funext derivedPlusOneFn_eq)

/-- **Headline: correctness of the derived program, REUSED from `L66.plusOne_correct`.**
    `derivedPlusOneFn` preserves value plus one — the digit list of `value xs + 1` — with no fresh
    correctness proof, only the pointwise bridge `derivedPlusOneFn_eq` and the solved file's own
    theorem. -/
theorem derived_plusOne_correct (xs : List Int) :
    value (derivedPlusOneFn xs) = value xs + 1 := by
  rw [derivedPlusOneFn_eq]
  exact plusOne_correct xs

/-! ## Running the derived program -/

example : derivedPlusOneFn ([1, 2, 3] : List Int) = [1, 2, 4] := by decide
example : derivedPlusOneFn ([9, 9] : List Int) = [1, 0, 0] := by decide

end Freyd.Alg.RelSet.LC66D
