/-
  Freyd & Scedrov, *Categories and Allegories* §1.18  Functors, §1.181.

  §1.18  A functor F : A → B preserves source, target, and composition.
         In object-centric form: object map + morphism map preserving id/comp.
  §1.181 Any functor preserves left- and right-invertibility.
         Moreover, the image of an inverse is an inverse of the image.
-/

import Fredy.S1_1
import Fredy.S1_41

set_option linter.unusedSectionVars false

open Freyd

universe v u w

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type w} [Cat.{v} 𝒟]

namespace Freyd

/-- §1.18  A functor from `𝒞` to `𝒟`. -/
class Functor (F : 𝒞 → 𝒟) where
  map  : {X Y : 𝒞} → (X ⟶ Y) → (F X ⟶ F Y)
  map_id : ∀ (X : 𝒞), map (Cat.id X) = Cat.id (F X)
  map_comp : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

/-- The identity functor. -/
def idFunctor : Functor (λ X : 𝒞 => X) where
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of functors `G ∘ F` (explicit, not a global instance). -/
def compFunctor {ℰ : Type _} [Cat.{v} ℰ] {F : 𝒞 → 𝒟} {G : 𝒟 → ℰ}
    [hf : Functor F] [hg : Functor G] : Functor (G ∘ F) where
  map f := hg.map (hf.map f)
  map_id X := by dsimp; rw [hf.map_id, hg.map_id]
  map_comp f g := by rw [hf.map_comp, hg.map_comp]

/-- **§1.181**: a functor preserves isomorphisms. -/
theorem functor_preserves_iso {F : 𝒞 → 𝒟} [h : Functor F] {X Y : 𝒞} (f : X ⟶ Y) (hf : IsIso f) :
    IsIso (h.map f) := by
  obtain ⟨g, hfg, hgf⟩ := hf
  refine ⟨h.map g, ?_, ?_⟩
  · rw [← h.map_comp, hfg, h.map_id]
  · rw [← h.map_comp, hgf, h.map_id]

/-- **§1.181**: the image of the inverse is an inverse of the image. -/
theorem functor_map_inv {F : 𝒞 → 𝒟} [h : Functor F] {X Y : 𝒞} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : f ≫ g = Cat.id X) (hgf : g ≫ f = Cat.id Y) :
    h.map f ≫ h.map g = Cat.id (F X) ∧
    h.map g ≫ h.map f = Cat.id (F Y) := by
  constructor
  · rw [← h.map_comp, hfg, h.map_id]
  · rw [← h.map_comp, hgf, h.map_id]

/-- **§1.181 (left-invertible)**.  If `g ≫ f = id` then `Fg ≫ Ff = id`. -/
theorem functor_preserves_left_inv {F : 𝒞 → 𝒟} [h : Functor F] {X Y : 𝒞} (f : X ⟶ Y) (g : Y ⟶ X)
    (h_eq : g ≫ f = Cat.id Y) : h.map g ≫ h.map f = Cat.id (F Y) := by
  rw [← h.map_comp, h_eq, h.map_id]

/-- **§1.181 (right-invertible)**.  If `f ≫ g = id` then `Ff ≫ Fg = id`. -/
theorem functor_preserves_right_inv {F : 𝒞 → 𝒟} [h : Functor F] {X Y : 𝒞} (f : X ⟶ Y) (g : Y ⟶ X)
    (h_eq : f ≫ g = Cat.id X) : h.map f ≫ h.map g = Cat.id (F X) := by
  rw [← h.map_comp, h_eq, h.map_id]
