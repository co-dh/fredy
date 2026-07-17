/-
  Freyd & Scedrov, *Categories and Allegories* §1.18–§1.19.

  Mathlib migration spike: a functor is one bundled value `F : C ⥤ D`.
-/

import Fredy.S1_1
import Fredy.S1_41
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Opposites

open CategoryTheory

universe v u u₁ u₂

namespace Freyd

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒟 : Type u} [Category.{v} 𝒟]

/-- Transitional unbundled functor structure for chapters not yet migrated.
New code in this worktree uses Mathlib's bundled `C ⥤ D` directly. -/
class Functor {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D] (F : C → D) where
  map : {X Y : C} → (X ⟶ Y) → (F X ⟶ F Y)
  map_id : ∀ X, map (𝟙 X) = 𝟙 (F X)
  map_comp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

/-- Bundle a transitional object-function plus its legacy functor instance as a
Mathlib functor.  This bridge disappears once the remaining chapters use `C ⥤ D`. -/
def bundledFunctor {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
    (F : C → D) [hF : Functor F] : C ⥤ D where
  obj := F
  map := hF.map
  map_id := hF.map_id
  map_comp := hF.map_comp

instance legacyIdentityFunctor {C : Type u₁} [Category.{v} C] :
    Functor (fun X : C ↦ X) where
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Transitional compatibility name for the legacy identity-functor witness. -/
def idFunctor {C : Type u₁} [Category.{v} C] : Functor (fun X : C => X) :=
  legacyIdentityFunctor

instance legacyCompFunctor {C : Type u₁} [Category.{v} C]
    {D : Type u₂} [Category.{v} D] {E : Type*} [Category.{v} E]
    {F : C → D} [hF : Functor F] {G : D → E} [hG : Functor G] :
    Functor (G ∘ F) where
  map f := hG.map (hF.map f)
  map_id X := by
    change hG.map (hF.map (𝟙 X)) = 𝟙 (G (F X))
    rw [hF.map_id, hG.map_id]
  map_comp f g := by rw [hF.map_comp, hG.map_comp]

/-- Transitional name for the unbundled composite functor used by chapters that
have not yet been rewritten to Mathlib's bundled `F ⋙ G`. -/
def compFunctor {C : Type u₁} [Category.{v} C]
    {D : Type u₂} [Category.{v} D] {E : Type*} [Category.{v} E]
    (F : C → D) (G : D → E) [hf : Functor F] [hg : Functor G] :
    Functor (G ∘ F) := legacyCompFunctor

/- Mathlib supplies identity and composite functors as `𝟭 C` and `F ⋙ G`.
   Their identity/composition laws are `F.map_id` and `F.map_comp`. -/

/-- A property of morphisms, uniform across categories in these universes. -/
abbrev MorphProp := ∀ {𝒜 : Type u} [Category.{v} 𝒜] {X Y : 𝒜}, (X ⟶ Y) → Prop

/-- `F` preserves the morphism property `P`. -/
def Preserves {ℰ ℱ : Type u} [Category.{v} ℰ] [Category.{v} ℱ]
    (F : ℰ ⥤ ℱ) (P : MorphProp.{v,u}) : Prop :=
  ∀ {X Y : ℰ} {f : X ⟶ Y}, P f → P (F.map f)

/-- `F` reflects the morphism property `P`. -/
def Reflects {ℰ ℱ : Type u} [Category.{v} ℰ] [Category.{v} ℱ]
    (F : ℰ ⥤ ℱ) (P : MorphProp.{v,u}) : Prop :=
  ∀ {X Y : ℰ} {f : X ⟶ Y}, P (F.map f) → P f

def PreservesMono {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
    (F : C ⥤ D) : Prop :=
  ∀ {X Y : C} {f : X ⟶ Y}, Monic f → Monic (F.map f)

def ReflectsMono {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
    (F : C ⥤ D) : Prop :=
  ∀ {X Y : C} {f : X ⟶ Y}, Monic (F.map f) → Monic f

/-- A morphism has a right inverse. -/
def HasRightInv : MorphProp.{v,u} :=
  fun {_} _ {X Y} f => ∃ g : Y ⟶ X, f ≫ g = 𝟙 X

/-- A morphism has a left inverse. -/
def HasLeftInv : MorphProp.{v,u} :=
  fun {_} _ {X Y} f => ∃ g : Y ⟶ X, g ≫ f = 𝟙 Y

/-- §1.181: every functor preserves isomorphisms. -/
theorem preserves_iso (F : 𝒞 ⥤ 𝒟) : Preserves F @IsIso := by
  rintro X Y f ⟨g, hfg, hgf⟩
  exact ⟨F.map g,
    by rw [← F.map_comp, hfg, F.map_id],
    by rw [← F.map_comp, hgf, F.map_id]⟩

/-- §1.181: every functor preserves right-invertibility. -/
theorem preserves_has_right_inv (F : 𝒞 ⥤ 𝒟) : Preserves F HasRightInv := by
  rintro X Y f ⟨g, hfg⟩
  exact ⟨F.map g, by rw [← F.map_comp, hfg, F.map_id]⟩

/-- §1.181: every functor preserves left-invertibility. -/
theorem preserves_has_left_inv (F : 𝒞 ⥤ 𝒟) : Preserves F HasLeftInv := by
  rintro X Y f ⟨g, hgf⟩
  exact ⟨F.map g, by rw [← F.map_comp, hgf, F.map_id]⟩

/-- Pointwise form of preservation of isomorphisms. -/
theorem functor_preserves_iso (F : 𝒞 ⥤ 𝒟) {X Y : 𝒞} (f : X ⟶ Y) (hf : IsIso f) :
    IsIso (F.map f) := preserves_iso F hf

/-- The image of a specified inverse is an inverse of the image. -/
theorem functor_map_inv (F : 𝒞 ⥤ 𝒟) {X Y : 𝒞} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : f ≫ g = 𝟙 X) (hgf : g ≫ f = 𝟙 Y) :
    F.map f ≫ F.map g = 𝟙 (F.obj X) ∧ F.map g ≫ F.map f = 𝟙 (F.obj Y) := by
  constructor
  · rw [← F.map_comp, hfg, F.map_id]
  · rw [← F.map_comp, hgf, F.map_id]

/-! ## §1.182 Opposite category

Mathlib supplies `Cᵒᵖ`, `Opposite.op`, and `Opposite.unop`; no new category
instance or reversed-composition proof is required.
-/

abbrev OppCat (C : Type u) [Category.{v} C] := Cᵒᵖ

abbrev toOpp {C : Type u} [Category.{v} C] (X : C) : OppCat C := Opposite.op X

abbrev fromOpp {C : Type u} [Category.{v} C] (X : OppCat C) : C := Opposite.unop X

/-! ## §1.19 Identity morphisms and the induced object map -/

def IdMorphs (C : Type u) [Category.{v} C] := C

def functor_on_idMorphs {C : Type u₁} [Category.{v} C]
    {D : Type u₂} [Category.{v} D] (F : C ⥤ D) : IdMorphs C → IdMorphs D := F.obj

end Freyd
