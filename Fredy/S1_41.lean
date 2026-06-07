/-
  Freyd & Scedrov, *Categories and Allegories* §1.41  Monic (§1.41), §1.17  Isomorphism.

  Mono (§1.41): a morphism is monic if it is left-cancellable.
  IsIso (§1.17): invertible morphism.  Composition of isos is iso.
-/

import Fredy.S1_1

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

/-- A split mono is monic: a map with a retraction is left-cancellable. -/
theorem mono_of_retraction {X Y : 𝒞} (m : X ⟶ Y) (r : Y ⟶ X)
    (hr : m ≫ r = Cat.id X) : Mono m := by
  intro W g h hgh
  calc g = g ≫ m ≫ r   := by rw [hr, Cat.comp_id]
    _    = (g ≫ m) ≫ r := (Cat.assoc _ _ _).symm
    _    = (h ≫ m) ≫ r := by rw [hgh]
    _    = h ≫ m ≫ r   := Cat.assoc _ _ _
    _    = h           := by rw [hr, Cat.comp_id]
