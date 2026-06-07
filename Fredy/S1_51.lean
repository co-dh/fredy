/-
  Freyd & Scedrov, *Categories and Allegories* §1.51  Covers, regular categories.

  §1.51  Subobject, Allows, Image, Cover (§1.512), Cover factorization.
-/


import Fredy.S1_1
import Fredy.S1_41


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.51 Subobjects -/

/-- A subobject of B: a domain and a monic morphism into B. -/
structure Subobject (𝒞 : Type u) [Cat.{v} 𝒞] (B : 𝒞) where
  dom   : 𝒞
  arr   : dom ⟶ B
  monic : Mono arr

/-- Order on subobjects: S ≤ T if S factors through T. -/
def Subobject.le {B : 𝒞} (S T : Subobject 𝒞 B) : Prop :=
  ∃ h : S.dom ⟶ T.dom, h ≫ T.arr = S.arr

/-- The entire (maximal) subobject: represented by id_B. -/
def Subobject.entire (B : 𝒞) : Subobject 𝒞 B :=
  ⟨B, Cat.id B, by
    intro X f g h; simpa [Cat.id_comp, Cat.comp_id] using h⟩

/-- S is ENTIRE iff its representing mono is an isomorphism. -/
def Subobject.IsEntire {B : 𝒞} (S : Subobject 𝒞 B) : Prop := IsIso S.arr

/-! ## §1.51 Allows

  A subobject B' → B ALLOWS f : A → B if f factors through B'. -/

def Allows {A B : 𝒞} (B' : Subobject 𝒞 B) (f : A ⟶ B) : Prop :=
  ∃ g : A ⟶ B'.dom, g ≫ B'.arr = f

/-! ## §1.51 Image

  The IMAGE of f is the smallest subobject of B that allows f.
  A category HAS IMAGES if every morphism has an image. -/

def IsImage {A B : 𝒞} (f : A ⟶ B) (I : Subobject 𝒞 B) : Prop :=
  Allows I f ∧ ∀ S : Subobject 𝒞 B, Allows S f → I.le S

class HasImages (𝒞 : Type u) [Cat.{v} 𝒞] where
  image   : ∀ {A B : 𝒞} (f : A ⟶ B), Subobject 𝒞 B
  isImage : ∀ {A B : 𝒞} (f : A ⟶ B), IsImage f (image f)

/-! ## §1.512 Cover

  A morphism is a COVER if every monic it factors through is iso.
  Defined directly — no images needed.  With images, equivalent to
  "its image is entire" (proved below). -/

def Cover {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∀ {C : 𝒞} (m : C ⟶ Y) (g : X ⟶ C), Mono m → g ≫ m = f → IsIso m

theorem monic_cover_iso {X Y : 𝒞} (f : X ⟶ Y) (hc : Cover f) (hm : Mono f) : IsIso f :=
  hc f (Cat.id X) hm (Cat.id_comp f)

/-! ## Image API (requires HasImages) -/

variable [HasImages 𝒞]

def image {A B : 𝒞} (f : A ⟶ B) : Subobject 𝒞 B := HasImages.image f

theorem image_allows {A B : 𝒞} (f : A ⟶ B) : Allows (image f) f :=
  (HasImages.isImage f).1

noncomputable def image.lift {A B : 𝒞} (f : A ⟶ B) : A ⟶ (image f).dom :=
  (image_allows f).choose

theorem image.lift_fac {A B : 𝒞} (f : A ⟶ B) : image.lift f ≫ (image f).arr = f :=
  (image_allows f).choose_spec

theorem image_min {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 B) (h : Allows S f) :
    (image f).le S :=
  (HasImages.isImage f).2 S h

/-- With images, f is a cover iff its image is entire (§1.512). -/
theorem cover_iff_image_entire {X Y : 𝒞} (f : X ⟶ Y) : Cover f ↔ Subobject.IsEntire (image f) := by
  constructor
  · intro hc; exact hc (image f).arr (image.lift f) (image f).monic (image.lift_fac f)
  · intro hIso
    rcases hIso with ⟨inv, hinv1, hinv2⟩
    intro C m g hm hfac
    have hallow : Allows (Subobject.mk C m hm) f := ⟨g, hfac⟩
    have him_le : (image f).le (Subobject.mk C m hm) := image_min f _ hallow
    rcases him_le with ⟨h, hh⟩
    have hinv_m : (inv ≫ h) ≫ m = Cat.id Y := by
      calc
        (inv ≫ h) ≫ m = inv ≫ (h ≫ m) := by simp [Cat.assoc]
        _ = inv ≫ (image f).arr := by rw [hh]
        _ = Cat.id Y := hinv2
    have h_right : m ≫ (inv ≫ h) = Cat.id C :=
      hm (m ≫ (inv ≫ h)) (Cat.id C) (by
        calc
          (m ≫ (inv ≫ h)) ≫ m = m ≫ ((inv ≫ h) ≫ m) := by simp [Cat.assoc]
          _ = m ≫ Cat.id Y := by rw [hinv_m]
          _ = m := Cat.comp_id _
          _ = Cat.id C ≫ m := (Cat.id_comp m).symm)
    exact ⟨inv ≫ h, h_right, hinv_m⟩

/-! ## §1.514 Epic

  A finite family {xᵢ : Aᵢ → B} is EPIC (jointly epimorphic) if
  for any g,h : B → X, agreeing on all xᵢ ≫ g = xᵢ ≫ h implies g = h. -/

def IsEpic {n : Nat} (x : Fin n → Σ A : 𝒞, A ⟶ B) : Prop :=
  ∀ (X : 𝒞) (g h : B ⟶ X), (∀ i : Fin n, (x i).2 ≫ g = (x i).2 ≫ h) → g = h

end Freyd
