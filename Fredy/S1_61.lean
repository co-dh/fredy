/-
  Freyd & Scedrov, *Categories and Allegories* §1.61  Pre-logoi — minimal subobject.
-/

import Fredy.S1_60

open Freyd

universe v u
variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-- **§1.61**: 0 is a coterminator (initial object). -/
noncomputable def minimal_subobject_of_one_is_coterminator (h : PreLogos 𝒞) : HasCoterminator 𝒞 :=
  let one : 𝒞 := h.toHasTerminal.one
  let zeroSub : Subobject 𝒞 one := h.bottom one
  let zeroObj : 𝒞 := zeroSub.dom
  let bot (A : 𝒞) : Subobject 𝒞 A := h.bottom A
  have bot_min {A : 𝒞} (S : Subobject 𝒞 A) : (bot A).le S := h.bottom_min S
  have bot_dom_iso (A : 𝒞) : Isomorphic (bot A).dom zeroObj :=
    h.bottom_dom_iso A one
  -- map 0 → A
  have mk (A : 𝒞) : zeroObj ⟶ A :=
    let iso := bot_dom_iso A
    let inv : zeroObj ⟶ (bot A).dom := iso.choose_spec.choose
    inv ≫ (bot A).arr
  --- uniqueness
  have uniq {A : 𝒞} (f g : zeroObj ⟶ A) : f = g := by
    sorry
  { zero := zeroObj
    init := mk
    init_uniq := uniq }

/-- **§1.61**: Any morphism to 0 is an isomorphism. -/
theorem any_map_to_zero_is_iso (h : PreLogos 𝒞) {A : 𝒞} (f : A ⟶ (minimal_subobject_of_one_is_coterminator h).zero) : IsIso f :=
  sorry

/-- **§1.61**: Degenerate iff 0 ≅ 1. -/
theorem degenerate_iff_zero_iso_one (h : PreLogos 𝒞) :
    (Nonempty (h.toHasTerminal.one ⟶ (minimal_subobject_of_one_is_coterminator h).zero)) ↔
    Isomorphic (minimal_subobject_of_one_is_coterminator h).zero h.toHasTerminal.one := by
  sorry

/-- §1.611 deferred. -/
theorem cartesian_distributive_implies_prelogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasEqualizers 𝒞] [HasImages 𝒞]
    [HasSubobjectUnions 𝒞] (hdist : IsDistributiveLattice (𝒞 := 𝒞)) : Nonempty (PreLogos 𝒞) := sorry

/-- §1.612 deferred. -/
theorem monic_iff_distributive {A B : 𝒞} [PreLogos 𝒞] (f : A ⟶ B) (hf : Mono f) : True := sorry

/-- §1.614 -/
class PreLogosFunctor {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] [PreLogos 𝒜] [PreLogos ℬ]
    (T : 𝒜 → ℬ) [Functor T] where preserves_finite_unions : True

/-- §1.615 deferred. -/
theorem union_via_coproduct_image {A₁ A₂ A : 𝒞} [PreLogos 𝒞] [HasBinaryCoproducts 𝒞]
    (x₁ : A₁ ⟶ A) (x₂ : A₂ ⟶ A) : True := sorry

end Freyd
