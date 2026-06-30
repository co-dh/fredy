/-
  Freyd & Scedrov, *Categories and Allegories* §2.536.

      "An amenable quotient of a division allegory is a division allegory."

  Given a DIVISION ALLEGORY `𝒜` and an `AmenableCongruence amen` on it, the
  quotient allegory `QuotAllegory 𝒜 amen.cong` (§2.5) carries a right division.
  On classes it is

      R̄ / S̄  :=  overline(R⁺ / S⁺)        ( = `Quotient.mk _ (largest R / largest S)` )

  where `R⁺ = amen.largest R` is the largest element of `R`'s congruence class
  (§2.53) and `R⁺ / S⁺` is the BASE division.  Since `⁺` depends only on the
  congruence class (`amenable_largest_class_invariant`), this is well-defined.

  The division adjunction `T̄ ⊑ R̄/S̄ ↔ T̄S̄ ⊑ R̄` is the book's argument:

    * `(R⁺/S⁺)S⁺ ⊑ R⁺` gives `(overline(R⁺/S⁺))S̄ ⊑ R̄`            [div_comp_le];
    * if `overline(TS) ⊑ R̄` then `(TS)⁺ ⊑ R⁺` by §2.533, hence `T⁺S⁺ ⊑ R⁺`
      by §2.534, so `T⁺ ⊑ R⁺/S⁺` by the BASE adjunction, hence
      `T̄ ⊑ overline(R⁺/S⁺) = R̄/S̄`                                  [le_div].

  The quotient order is detected by the largest-element calculus
  (`quotLe_iff_largest`, a repackaging of §2.532/§2.533): in the quotient
  `[R] ⊑ [S] ↔ R⁺ ⊑ S⁺`.

  STRICTLY mathlib-free; only `Fredy.*` + Lean core.
-/

import Fredy.S2_3
import Fredy.S2_5_QuotAllegory

universe v u

namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ## The quotient order via the largest-element calculus

  In the quotient allegory `QuotAllegory 𝒜 amen.cong`, `[R] ⊑ [S]` holds iff
  `R⁺ ⊑ S⁺` (§2.533).  This is the only fact about the order we need; it is
  proven elementarily from §2.532 `(R∩S)⁺ = R⁺ ∩ S⁺` and the class-invariance of
  `⁺`.  The instance is PINNED to `QuotAllegory.instAllegory` (rather than left to
  typeclass search) so it cannot be confused with the under-construction division
  structure below. -/

/-- §2.533 (order form).  In `QuotAllegory 𝒜 amen.cong`,
    `[R] ⊑ [S]  ↔  R⁺ ⊑ S⁺`. -/
theorem quotLe_iff_largest (amen : AmenableCongruence 𝒜) {a b : 𝒜} (R S : a ⟶ b) :
    @le (QuotAllegory 𝒜 amen.cong) a b (QuotAllegory.instAllegory amen.cong)
        (Quotient.mk (congSetoid amen.cong) R) (Quotient.mk (congSetoid amen.cong) S)
      ↔ amen.largest R ⊑ amen.largest S := by
  -- `[R] ⊑ [S]` unfolds to `[R] ∩ [S] = [R]`, and `[R] ∩ [S] = [R ∩ S]`.
  show (Quotient.mk (congSetoid amen.cong) (R ∩ S) = Quotient.mk (congSetoid amen.cong) R)
        ↔ amen.largest R ⊑ amen.largest S
  constructor
  · intro h
    -- `[R ∩ S] = [R]` means `R ∩ S ≡ R`, so `(R ∩ S)⁺ = R⁺`; and `(R ∩ S)⁺ = R⁺ ∩ S⁺`.
    have hrel : amen.cong.rel (R ∩ S) R := Quotient.exact h
    have e1 : amen.largest (R ∩ S) = amen.largest R := amenable_largest_class_invariant amen hrel
    have e2 : amen.largest (R ∩ S) = amen.largest R ∩ amen.largest S := amenable_inter_largest amen R S
    show amen.largest R ∩ amen.largest S = amen.largest R
    rw [← e2, e1]
  · intro h
    -- `R⁺ ∩ S⁺ = R⁺` and `(R ∩ S)⁺ = R⁺ ∩ S⁺` give `(R ∩ S)⁺ = R⁺`, hence `R ∩ S ≡ R`.
    have e2 : amen.largest (R ∩ S) = amen.largest R ∩ amen.largest S := amenable_inter_largest amen R S
    have e1 : amen.largest (R ∩ S) = amen.largest R := by rw [e2]; exact h
    have hRS : amen.cong.rel (R ∩ S) (amen.largest (R ∩ S)) := amen.largest_rel (R ∩ S)
    rw [e1] at hRS
    exact Quotient.sound (amen.cong.trans hRS (amen.cong.symm (amen.largest_rel R)))


/-! ## §2.536  The quotient division allegory

  `R̄ / S̄ := overline(R⁺ / S⁺)`, well-defined by class-invariance of `⁺`.  The
  adjunction is the book's proof, routed through `quotLe_iff_largest`. -/

/-- §2.536  An amenable quotient of a division allegory is a division allegory.

    `R̄ / S̄ = overline(R⁺ / S⁺)`; the distributive structure is
    `QuotAllegory.instDistributiveAllegory` (using `amen.union_congr`). -/
def QuotAllegory.instDivisionAllegory (amen : AmenableCongruence 𝒜) :
    DivisionAllegory (QuotAllegory 𝒜 amen.cong) :=
  { QuotAllegory.instDistributiveAllegory amen.cong
      (fun hR hS => amen.union_congr hR hS) with
    div := fun {_ _ _} Rq Sq =>
      Quotient.lift₂
        (fun R S => Quotient.mk (congSetoid amen.cong) (amen.largest R / amen.largest S))
        (fun _ _ _ _ hR hS => by
          refine congrArg (Quotient.mk (congSetoid amen.cong)) ?_
          rw [amenable_largest_class_invariant amen hR,
            amenable_largest_class_invariant amen hS])
        Rq Sq
    -- §2.536: `(R⁺/S⁺)S⁺ ⊑ R⁺` implies `(overline(R⁺/S⁺))S̄ ⊑ R̄`.
    div_comp_le := by
      intro a b c Rq Sq
      refine Quotient.inductionOn₂ Rq Sq (fun R S => ?_)
      -- Goal (defeq): `[(R⁺/S⁺) ≫ S] ⊑ [R]`.  By `quotLe_iff_largest`:
      --   `((R⁺/S⁺) ≫ S)⁺ ⊑ R⁺`.
      refine (quotLe_iff_largest amen ((amen.largest R / amen.largest S) ≫ S) R).mpr ?_
      -- Base triangle `(R⁺/S⁺) ≫ S⁺ ⊑ R⁺`.
      have base : (amen.largest R / amen.largest S) ≫ amen.largest S ⊑ amen.largest R :=
        DivisionAllegory.div_comp_le (amen.largest R) (amen.largest S)
      -- `S ≡ S⁺`, so `((R⁺/S⁺) ≫ S)⁺ = ((R⁺/S⁺) ≫ S⁺)⁺`.
      have heq : amen.largest ((amen.largest R / amen.largest S) ≫ S)
               = amen.largest ((amen.largest R / amen.largest S) ≫ amen.largest S) :=
        amenable_largest_class_invariant amen
          (amen.cong.comp_congr (amen.cong.refl _) (amen.largest_rel S))
      -- `((R⁺/S⁺) ≫ S⁺)⁺ ⊑ R⁺⁺ = R⁺`.
      have hmono : amen.largest ((amen.largest R / amen.largest S) ≫ amen.largest S)
                 ⊑ amen.largest (amen.largest R) := amenable_le_largest amen base
      rw [largest_idem amen R] at hmono
      rw [heq]; exact hmono
    -- §2.536: if `overline(TS) ⊑ R̄` then `T̄ ⊑ overline(R⁺/S⁺)`.
    le_div := by
      intro a b c Tq Rq Sq
      refine Quotient.inductionOn₃ Tq Rq Sq (fun T R S => ?_)
      intro h
      -- `h : [T ≫ S] ⊑ [R]`, i.e. `(TS)⁺ ⊑ R⁺` by §2.533.
      have hTS : amen.largest (T ≫ S) ⊑ amen.largest R :=
        (quotLe_iff_largest amen (T ≫ S) R).mp h
      -- §2.534: `T⁺S⁺ ⊑ (TS)⁺`, so `T⁺S⁺ ⊑ R⁺`.
      have hcomp : amen.largest T ≫ amen.largest S ⊑ amen.largest R :=
        le_trans (largest_comp_le amen T S) hTS
      -- Base adjunction: `T⁺ ⊑ R⁺/S⁺`.
      have hdiv : amen.largest T ⊑ amen.largest R / amen.largest S :=
        (le_div_iff _ _ _).mpr hcomp
      -- `⁺`-monotone (§2.531): `T⁺⁺ ⊑ (R⁺/S⁺)⁺`, and `T⁺⁺ = T⁺`.
      have hmono : amen.largest (amen.largest T)
                 ⊑ amen.largest (amen.largest R / amen.largest S) := amenable_le_largest amen hdiv
      rw [largest_idem amen T] at hmono
      -- Goal (defeq): `[T] ⊑ [R⁺/S⁺]`.  By `quotLe_iff_largest`: `T⁺ ⊑ (R⁺/S⁺)⁺`.
      exact (quotLe_iff_largest amen T (amen.largest R / amen.largest S)).mpr hmono }

/-- §2.536 (statement of the delivered adjunction).  In the amenable quotient,
    `T̄ ⊑ R̄/S̄  ↔  T̄ ≫ S̄ ⊑ R̄`, where `R̄/S̄ = overline(R⁺/S⁺)`.  This is the
    division-allegory law `le_div_iff` re-exported against
    `QuotAllegory.instDivisionAllegory`. -/
theorem quotient_le_div_iff (amen : AmenableCongruence 𝒜) {a b c : 𝒜}
    (Tq : @Cat.Hom (QuotAllegory 𝒜 amen.cong) _ a b)
    (Rq : @Cat.Hom (QuotAllegory 𝒜 amen.cong) _ a c)
    (Sq : @Cat.Hom (QuotAllegory 𝒜 amen.cong) _ b c) :
    letI := QuotAllegory.instDivisionAllegory amen
    Tq ⊑ Rq / Sq ↔ Tq ≫ Sq ⊑ Rq := by
  letI := QuotAllegory.instDivisionAllegory amen
  exact le_div_iff Tq Rq Sq

end Freyd.Alg
