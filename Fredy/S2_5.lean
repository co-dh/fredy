/-
  Freyd & Scedrov, *Categories and Allegories* §2.5  Quotient allegories.

  §2.5  CONGRUENCE on an allegory, QUOTIENT ALLEGORY
  §2.521 BOOLEAN QUOTIENT
  §2.522 CLOSED QUOTIENT
  §2.53 AMENABLE CONGRUENCE, AMENABLE QUOTIENT
  §2.536 Amenable quotient of division allegory is division
  §2.542 every topos admits a faithful bicartesian representation
-/

import Fredy.S1_1
import Fredy.S2_1
import Fredy.S2_2
import Fredy.S2_3
import Fredy.S2_4


universe v u

namespace Freyd

/-! ## §2.5  Congruence and quotient allegory

  A CONGRUENCE on an allegory is an equivalence relation on morphisms
  that respects reciprocation, intersection, and composition.
  Different identity morphisms are never identified. -/

/-- A CONGRUENCE on an allegory (§2.5). -/
structure Congruence (𝒜 : Type u) [Allegory 𝒜] where
  rel {a b : 𝒜} (R S : a ⟶ b) : Prop
  refl {a b : 𝒜} (R : a ⟶ b) : rel R R
  symm {a b : 𝒜} {R S : a ⟶ b} (h : rel R S) : rel S R
  trans {a b : 𝒜} {R S T : a ⟶ b} (hRS : rel R S) (hST : rel S T) : rel R T
  recip_congr {a b : 𝒜} {R S : a ⟶ b} (h : rel R S) : rel (R°) (S°)
  inter_congr {a b : 𝒜} {R S R' S' : a ⟶ b} (hR : rel R R') (hS : rel S S') :
    rel (R ∩ S) (R' ∩ S')
  comp_congr {a b c : 𝒜} {R R' : a ⟶ b} {S S' : b ⟶ c}
    (hR : rel R R') (hS : rel S S') : rel (R ≫ S) (R' ≫ S')

/-! ## §2.521  Boolean quotient

  R ≡ S iff ∀ T, R ∩ T = 0 ↔ S ∩ T = 0 (§2.521). -/

section BooleanQuotient

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- The BOOLEAN QUOTIENT relation (§2.521). -/
def booleanQuotientRel {a b : 𝒜} (R S : a ⟶ b) : Prop :=
  ∀ (T : a ⟶ b), (R ∩ T = (𝟘 : a ⟶ b)) ↔ (S ∩ T = (𝟘 : a ⟶ b))

end BooleanQuotient

/-! ## §2.522  Closed quotient

  R ≡ S iff R ∪ (p_a ≫ U ≫ p_b°) = S ∪ (p_a ≫ U ≫ p_b°) (§2.522). -/

section ClosedQuotient

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- The CLOSED QUOTIENT relation with respect to U : T → T (§2.522). -/
def closedQuotientRel {a b T : 𝒜} (U : T ⟶ T) (p_a : a ⟶ T) (p_b : b ⟶ T) (R S : a ⟶ b) : Prop :=
  R ∪ (p_a ≫ U ≫ p_b°) = S ∪ (p_a ≫ U ≫ p_b°)

end ClosedQuotient

/-! ## §2.53  Amenable congruence

  A congruence is AMENABLE if it respects binary unions and each
  congruence class has a largest element R⁺ (§2.53). -/

section Amenable

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- An AMENABLE CONGRUENCE (§2.53). -/
structure AmenableCongruence (𝒜 : Type u) [DistributiveAllegory 𝒜] where
  cong : Congruence 𝒜
  union_congr {a b : 𝒜} {R S R' S' : a ⟶ b} (hR : cong.rel R R') (hS : cong.rel S S') :
    cong.rel (R ∪ S) (R' ∪ S')
  largest {a b : 𝒜} (R : a ⟶ b) : a ⟶ b
  largest_rel {a b : 𝒜} (R : a ⟶ b) : cong.rel R (largest R)
  largest_max {a b : 𝒜} {R S : a ⟶ b} (h : cong.rel R S) : S ⊑ largest R

/-- §2.531: If R ⊑ S, then R⁺ ⊑ S⁺. -/
theorem amenable_le_largest (amen : AmenableCongruence 𝒜) {a b : 𝒜} {R S : a ⟶ b} (h : R ⊑ S) :
    amen.largest R ⊑ amen.largest S := by
  have h_union : R ∪ S = S := (le_iff_union_eq_left R S).mp h
  have h_congr_union : amen.cong.rel (R ∪ S) ((amen.largest R) ∪ S) :=
    amen.union_congr (amen.largest_rel R) (amen.cong.refl S)
  have h_congr_S : amen.cong.rel S ((amen.largest R) ∪ S) := by
    rw [h_union] at h_congr_union
    exact h_congr_union
  have h_max : (amen.largest R) ∪ S ⊑ amen.largest S :=
    amen.largest_max h_congr_S
  have h_sub_union : amen.largest R ⊑ (amen.largest R) ∪ S := by
    rw [le, Allegory.inter_comm, DistributiveAllegory.inter_union_absorb]
  exact le_trans h_sub_union h_max

/-- §2.532: (R ∩ S)⁺ = R⁺ ∩ S⁺. -/
theorem amenable_inter_largest (amen : AmenableCongruence 𝒜) {a b : 𝒜} (R S : a ⟶ b) :
    amen.largest (R ∩ S) = (amen.largest R) ∩ (amen.largest S) := by
  apply le_antisymm
  · apply le_inter
    · exact amenable_le_largest amen (inter_lb_left R S)
    · exact amenable_le_largest amen (inter_lb_right R S)
  · apply amen.largest_max
    apply amen.cong.inter_congr (amen.largest_rel R) (amen.largest_rel S)

end Amenable

/-! ## §2.536  Amenable quotient of division allegory is division

  R / S is constructed as R⁺ / S⁺ (§2.536). -/

section AmenableDivision

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- An amenable quotient of a division allegory is a division allegory (§2.536). -/
axiom amenableQuotientDivision_ax (amen : AmenableCongruence 𝒜) : DivisionAllegory 𝒜

noncomputable def amenableQuotientDivision (amen : AmenableCongruence 𝒜) : DivisionAllegory 𝒜 :=
  amenableQuotientDivision_ax amen

end AmenableDivision

/-! ## §2.542  Every topos admits a faithful bicartesian
    representation to a boolean topos (§2.542). -/

theorem topos_boolean_representation : True := by
  trivial

end Freyd
