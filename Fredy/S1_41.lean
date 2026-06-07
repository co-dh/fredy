/-
  Freyd & Scedrov, *Categories and Allegories* §1.41  Monic (§1.41), §1.17  Isomorphism.

  Mono (§1.41): a morphism is monic if it is left-cancellable.
  IsIso (§1.17): invertible morphism.  Composition of isos is iso.
-/

import Fredy.S1_1

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

def Mono {X Y : 𝒞} (m : X ⟶ Y) : Prop :=
  ∀ {W : 𝒞} (g h : W ⟶ X), g ≫ m = h ≫ m → g = h

def IsIso {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, f ≫ g = Cat.id X ∧ g ≫ f = Cat.id Y

/-- Isomorphisms are closed under composition; the inverse is `g⁻¹ ≫ f⁻¹`. -/
theorem isIso_comp {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsIso f) (hg : IsIso g) :
    IsIso (f ≫ g) := by
  obtain ⟨f', hf1, hf2⟩ := hf
  obtain ⟨g', hg1, hg2⟩ := hg
  exact ⟨g' ≫ f',
    by rw [Cat.assoc, ← Cat.assoc g, hg1, Cat.id_comp, hf1],
    by rw [Cat.assoc, ← Cat.assoc f', hf2, Cat.id_comp, hg2]⟩
