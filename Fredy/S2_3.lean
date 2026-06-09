/-
  Freyd & Scedrov, *Categories and Allegories* §2.3  Division allegories.

  §2.31 DIVISION ALLEGORY — right division R/S
  §2.331 SYMMETRIC DIVISION R/ₛS
  §2.35 STRAIGHT morphism, simple part, domain of simplicity
-/

import Fredy.S1_1
import Fredy.S2_1
import Fredy.S2_2


universe v u

namespace Freyd

/-! ## §2.31  Division allegory

  A DIVISION ALLEGORY is a distributive allegory with a binary partial
  operation R/S (right division) defined when R□ = S□, characterized by:
  T ⊑ R/S  iff  TS ⊑ R.

  Equivalently: (R/S)S ⊑ R (semi-commutative triangle) and R/S is
  maximal among such morphisms. -/

/-- A DIVISION ALLEGORY (§2.31): distributive allegory with right division R/S,
    the right adjoint to composition (-) ≫ S. -/
class DivisionAllegory (𝒜 : Type u) extends DistributiveAllegory 𝒜 where
  /-- Right division R/S : □R → □S, defined when R□ = S□. -/
  div {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : a ⟶ b

  /-- The semi-commutative triangle: (R/S)S ⊑ R (§2.31). -/
  div_comp_le {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : (div R S ≫ S) ⊑ R

  /-- The adjointness: if TS ⊑ R then T ⊑ R/S (§2.31). -/
  le_div {a b c : 𝒜} (T : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) (h : T ≫ S ⊑ R) : T ⊑ div R S

/-! ### Notation -/

/-- Right division notation R / S -/
infixl:70 " / " => DivisionAllegory.div

end Freyd

namespace Freyd

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ### Derived properties of division -/

/-- The defining equivalence: T ⊑ R/S iff TS ⊑ R (§2.31). -/
theorem le_div_iff {a b c : 𝒜} (T : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) :
    T ⊑ R / S ↔ T ≫ S ⊑ R := by
  constructor
  · intro h
    -- T ⊑ R/S → TS ⊑ (R/S)S ⊑ R
    apply le_trans ?_ (DivisionAllegory.div_comp_le R S)
    exact comp_mono_right h S
  · exact DivisionAllegory.le_div T R S

/-- (R/S)S ⊑ R (§2.31). -/
theorem div_comp_eq_le {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : (R / S) ≫ S ⊑ R :=
  DivisionAllegory.div_comp_le R S

/-- (R ∩ R')/S ⊑ (R/S) ∩ (R'/S) (§2.31). -/
theorem div_inter_le {a b c : 𝒜} (R R' : a ⟶ c) (S : b ⟶ c) :
    (R ∩ R') / S ⊑ (R / S) ∩ (R' / S) := by
  apply le_inter
  · apply (le_div_iff _ _ _).mpr
    -- ((R ∩ R') / S) ≫ S ⊑ R ∩ R' ⊑ R
    apply le_trans (div_comp_eq_le _ _)
    exact inter_lb_left _ _
  · apply (le_div_iff _ _ _).mpr
    apply le_trans (div_comp_eq_le _ _)
    exact inter_lb_right _ _

/-- R/1 = R (§2.314). -/
theorem div_one {a b : 𝒜} (R : a ⟶ b) : R / Cat.id b = R := by
  apply le_antisymm
  · -- (R/1) ⊑ R: div_comp_eq_le gives (R/1)≫1 ⊑ R, and (R/1)≫1 = R/1
    have h := div_comp_eq_le R (Cat.id b)
    simpa [Cat.comp_id] using h
  · -- R ⊑ R/1: by le_div_iff, this is equivalent to R≫1 ⊑ R
    rw [le_div_iff]
    simpa [Cat.comp_id] using le_refl R

/-- 1 ⊑ R/R (§2.314). -/
theorem one_le_div_self {a b : 𝒜} (R : a ⟶ b) : Cat.id a ⊑ R / R := by
  apply (le_div_iff _ _ _).mpr
  rw [Cat.id_comp]
  exact le_refl _

/-- (R/R)R ⊑ R (§2.314). -/
theorem div_self_comp_le {a b : 𝒜} (R : a ⟶ b) : (R / R) ≫ R ⊑ R :=
  div_comp_eq_le R R

/-- (R/S)(S/T) ⊑ R/T (§2.314). -/
theorem div_comp {a b c d : 𝒜} (R : a ⟶ d) (S : b ⟶ d) (T : c ⟶ d) :
    (R / S) ≫ (S / T) ⊑ R / T := by
  apply (le_div_iff _ _ _).mpr
  apply le_trans ?_ (div_comp_eq_le R S)
  rw [Cat.assoc]
  exact comp_mono_left (R / S) (div_comp_eq_le S T)

/-! ## §2.331  Symmetric division

  R/ₛS = (R/S) ∩ (S/R)° (§2.35).  Characterized by:
  T ⊑ R/ₛS  iff  TS ⊑ R and T°R ⊑ S. -/

/-- SYMMETRIC DIVISION: R/ₛS = (R/S) ∩ (S/R)° (§2.35, §2.331). -/
def symmDiv {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : a ⟶ b :=
  (R / S) ∩ ((S / R)°)

infixl:70 " /ₛ " => symmDiv

/-- Characterizing property of symmetric division (§2.35). -/
theorem le_symmDiv_iff {a b c : 𝒜} (T : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) :
    T ⊑ R /ₛ S ↔ T ≫ S ⊑ R ∧ T° ≫ R ⊑ S := by
  dsimp [symmDiv]
  constructor
  · intro h
    have h1 : T ⊑ R / S := le_trans h (inter_lb_left _ _)
    have h2 : T ⊑ (S / R)° := le_trans h (inter_lb_right _ _)
    constructor
    · exact ((le_div_iff _ _ _).mp h1)
    · -- T ⊑ (S/R)° → T° ⊑ S/R → T°R ⊑ S
      have h2' : T° ⊑ S / R := by
        -- T ⊑ (S/R)° → T° ⊑ (S/R)°° = S/R
        calc
          T° ⊑ ((S / R)°)° := recip_mono h2
          _ = S / R := by rw [Allegory.recip_recip]
      exact ((le_div_iff _ _ _).mp h2')
  · intro ⟨hTS, hTR⟩
    apply le_inter
    · exact ((le_div_iff _ _ _).mpr hTS)
    · -- T ⊑ (S/R)° ↔ T° ⊑ S/R
      have hTR_div : T° ⊑ S / R := (le_div_iff _ _ _).mpr hTR
      calc
        T = (T°)° := by rw [Allegory.recip_recip]
        _ ⊑ (S / R)° := recip_mono hTR_div

/-! ## §2.35  Straight morphism, simple part

  R is STRAIGHT if R/ₛR ⊑ 1 (§2.351).
  In a division allegory, for any R, R/(R/ₛR) is the simple part. -/

/-- R is STRAIGHT if R/ₛR ⊑ 1 (§2.351). -/
def Straight {a b : 𝒜} (R : a ⟶ b) : Prop := R /ₛ R ⊑ Cat.id a

/-- In a division allegory, (R/R)R = R (§2.314). -/
theorem div_self_comp {a b : 𝒜} (R : a ⟶ b) : (R / R) ≫ R = R := by
  apply le_antisymm (div_comp_eq_le R R)
  -- R ⊑ (R/R)R: since 1 ⊑ R/R, we have R = 1R ⊑ (R/R)R
  have h : R ⊑ (R / R) ≫ R := by
    calc
      R = (Cat.id a) ≫ R := by rw [Cat.id_comp]
      _ ⊑ (R / R) ≫ R := comp_mono_right (one_le_div_self R) R
  exact h

end Freyd
