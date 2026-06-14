/-
  Freyd & Scedrov, *Categories and Allegories* §1.61  Pre-logoi — minimal subobject.

  §1.61  0 = minimal subobject of 1.  Any map to 0 is iso.  0 is a coterminator.
  §1.611 Pre-logos ⇔ Cartesian + images + subobject lattices are distributive.
  §1.612 For monic f: A↣B, f# preserves binary unions iff Sub(B) distributive.
  §1.614 Representation of pre-logoi.
  §1.615 In bicartesian, unions via coproduct images.
-/

import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_58
import Fredy.S1_60

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.61  Minimal subobject of 1

  In a pre-logos, Sub(1) is a lattice: it has finite meets and joins.
  The empty join is the *minimal subobject* of 1, denoted 0.
  Its domain is a coterminator (initial object). -/

section S1_61

variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [hpb : HasPullbacks 𝒞]
variable [hi : HasImages 𝒞] [hsu : HasSubobjectUnions 𝒞]
variable [hpl : PreLogos 𝒞]

/-- **§1.61**: The domain of the minimal subobject of 1 is a coterminator
    (initial object).  For each A, the unique map 0 → A is obtained from
    the inverse image p_A#(0) ≅ 0. -/
def minimal_subobject_of_one_is_coterminator
    (zeroSub : Subobject 𝒞 ht.one)
    (hz_min : ∀ (S : Subobject 𝒞 ht.one), zeroSub.le S) :
    HasCoterminator 𝒞 := by
  -- The domain of the minimal subobject will serve as the coterminator
  sorry

/-- **§1.61**: Any morphism to 0 is an isomorphism. -/
theorem any_map_to_zero_is_iso
    (zeroSub : Subobject 𝒞 ht.one) (hz_min : ∀ (S : Subobject 𝒞 ht.one), zeroSub.le S)
    {A : 𝒞} (f : A ⟶ zeroSub.dom) : IsIso f := by
  sorry

/-- **§1.61**: A pre-logos is degenerate (one-valued) iff 0 ≅ 1. -/
theorem degenerate_iff_zero_iso_one
    (zeroSub : Subobject 𝒞 ht.one) (hz_min : ∀ (S : Subobject 𝒞 ht.one), zeroSub.le S) :
    (Nonempty (ht.one ⟶ zeroSub.dom)) ↔ Isomorphic zeroSub.dom ht.one := by
  sorry

end S1_61

/-! ## §1.611  Alternative definition of pre-logos

  A pre-logos can be defined as a Cartesian category with images such
  that each Sub(A) is a distributive lattice (§1.611). -/

section S1_611

/-- **§1.611**: A Cartesian category with images where subobject
    lattices are distributive is a pre-logos. -/
theorem cartesian_distributive_implies_prelogos
    [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞]
    [heq : HasEqualizers 𝒞] [hi : HasImages 𝒞] [hsu : HasSubobjectUnions 𝒞]
    (hdist : IsDistributiveLattice (𝒞 := 𝒞)) : Nonempty (PreLogos 𝒞) := by
  sorry

end S1_611

/-! ## §1.612  Monic inverse image preserves unions ⇔ distributive

  For a monic f: A ↣ B, f# preserves binary unions iff Sub(B)
  is a distributive lattice. -/

section S1_612

variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [hpb : HasPullbacks 𝒞]
variable [hi : HasImages 𝒞] [hsu : HasSubobjectUnions 𝒞]

theorem monic_inverseImage_preserves_unions_iff_distributive
    {A B : 𝒞} (f : A ⟶ B) (hf : Mono f) :
    (∀ (S T : Subobject 𝒞 B),
      Isomorphic (InverseImage f (HasSubobjectUnions.union S T)).dom
                 (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)).dom)
    ↔ IsDistributiveLattice (𝒞 := 𝒞) := by
  sorry

end S1_612

/-! ## §1.614  Representation of pre-logoi

  A functor between pre-logoi preserves the pre-logos structure if it
  preserves the Cartesian structure, images, and finite unions. -/

section S1_614

variable {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
variable [PreLogos 𝒜] [PreLogos ℬ]

/-- A functor between pre-logoi that preserves the pre-logos structure. -/
class PreLogosFunctor (T : 𝒜 → ℬ) [Functor T] where
  preserves_finite_unions : True

end S1_614

/-! ## §1.615  Bicartesian unions via coproduct images

  In a bicartesian category with images, the union of x₁: A₁→A and
  x₂: A₂→A is the image of ⟨x₁, x₂⟩: A₁+A₂ → A. -/

section S1_615

theorem union_via_coproduct_image {A₁ A₂ A : 𝒞} (x₁ : A₁ ⟶ A) (x₂ : A₂ ⟶ A)
    [HasBinaryCoproducts 𝒞] [PreLogos 𝒞] :
    Isomorphic
      ((HasSubobjectUnions.union (image x₁) (image x₂)).dom)
      (image (HasBinaryCoproducts.case x₁ x₂)).dom := by
  sorry

end S1_615

end Freyd
