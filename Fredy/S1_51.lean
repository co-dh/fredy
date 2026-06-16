/-
  Freyd & Scedrov, *Categories and Allegories* §1.51  Covers, regular categories.

  §1.51  Subobject, Allows, Image, Cover (§1.512), Cover factorization.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_33
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

/-- Pre-composing a cover with an isomorphism is still a cover: any monic `m`
    that `i ≫ h` factors through, `h` also factors through (via `i⁻¹ ≫ g`), so
    `h` being a cover forces `m` iso.  Lets us reduce a pullback-square cover to a
    canonical-pullback cover (the two projections differ by the comparison iso). -/
theorem cover_precomp_iso {X X' Y : 𝒞} {i : X ⟶ X'} (hi : IsIso i) {h : X' ⟶ Y}
    (hc : Cover h) : Cover (i ≫ h) := by
  obtain ⟨i', _, hi2⟩ := hi
  intro C m g hm hgm
  refine hc m (i' ≫ g) hm ?_
  calc (i' ≫ g) ≫ m = i' ≫ (g ≫ m) := Cat.assoc _ _ _
    _ = i' ≫ (i ≫ h) := by rw [hgm]
    _ = (i' ≫ i) ≫ h := (Cat.assoc _ _ _).symm
    _ = Cat.id _ ≫ h := by rw [hi2]
    _ = h := Cat.id_comp _

/-- Two images of the same morphism are isomorphic via *any* comparison map that
    is compatible with their inclusions.  Concretely: if `P` and `Q` are both
    images of `g`, and `c : P.dom → Q.dom` satisfies `c ≫ Q.arr = P.arr`, then `c`
    is an isomorphism.  This packages the up-to-unique-iso uniqueness of images and
    is the key lemma for §1.511. -/
theorem image_comparison_iso {A B : 𝒞} {g : A ⟶ B} {P Q : Subobject 𝒞 B}
    (hP : IsImage g P) (hQ : IsImage g Q) (c : P.dom ⟶ Q.dom) (hc : c ≫ Q.arr = P.arr) :
    IsIso c := by
  -- `Q` is minimal and `P` allows `g`, so `Q ≤ P`: get the reverse comparison `d`.
  obtain ⟨d, hd⟩ := hQ.2 P hP.1
  refine ⟨d, ?_, ?_⟩
  · exact P.monic (c ≫ d) (Cat.id P.dom) (by rw [Cat.assoc, hd, hc, Cat.id_comp])
  · exact Q.monic (d ≫ c) (Cat.id Q.dom) (by rw [Cat.assoc, hc, hd, Cat.id_comp])

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

/-! ## §1.511 A faithful, image-preserving functor reflects images

  The book: *"If A has images and T : A → B is faithful and preserves images,
  then T reflects images."*  The engine is that **A already has images**: a
  candidate subobject `J` that allows `f` is compared to the genuine image of `f`
  in A; `T` sends that comparison to an iso (image uniqueness in B), and
  faithfulness reflects it back. -/

/-- Push a subobject of `B` forward along a mono-preserving functor `T`, landing as
    a subobject of `T B`. -/
def Subobject.map {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] (T : 𝒜 → ℬ) [hT : Functor T]
    (hpm : PreservesMono T) {B : 𝒜} (S : Subobject 𝒜 B) : Subobject ℬ (T B) where
  dom   := T S.dom
  arr   := hT.map S.arr
  monic := hpm S.monic

/-- `T` PRESERVES IMAGES: it carries every image factorization in `𝒜` to an image
    factorization in `ℬ`. -/
def PreservesImages {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] (T : 𝒜 → ℬ) [hT : Functor T]
    (hpm : PreservesMono T) : Prop :=
  ∀ {A B : 𝒜} (f : A ⟶ B) (I : Subobject 𝒜 B), IsImage f I → IsImage (hT.map f) (Subobject.map T hpm I)

/-- **§1.511**: if `𝒜` has images and `T : 𝒜 → ℬ` is faithful and preserves images,
    then `T` reflects images.  Given `f` and a subobject `J` that allows `f`, if the
    pushforward `T J` is the image of `T f`, then `J` is already the image of `f`. -/
theorem faithful_preserves_images_reflects_images
    {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] [HasImages 𝒜]
    (T : 𝒜 → ℬ) [hT : Functor T] (hfaithful : Faithful T) (hpm : PreservesMono T)
    (hpres : PreservesImages T hpm)
    {A B : 𝒜} (f : A ⟶ B) (J : Subobject 𝒜 B)
    (hJallows : Allows J f) (hJimg : IsImage (hT.map f) (Subobject.map T hpm J)) :
    IsImage f J := by
  -- the genuine 𝒜-image of `f`, and its minimality
  have hI : IsImage f (image f) := HasImages.isImage f
  -- `J` allows `f`, so the 𝒜-image is below `J`: comparison `k : image → J`.
  obtain ⟨k, hk⟩ := hI.2 J hJallows
  -- `T` preserves the 𝒜-image, so `T(image f)` is an image of `T f` too.
  have hTI : IsImage (hT.map f) (Subobject.map T hpm (image f)) := hpres f (image f) hI
  -- `T k` is a comparison between two images of `T f`, hence an iso…
  have hTk_fac : hT.map k ≫ (Subobject.map T hpm J).arr = (Subobject.map T hpm (image f)).arr := by
    show hT.map k ≫ hT.map J.arr = hT.map (image f).arr
    rw [← hT.map_comp, hk]
  have hTk_iso : IsIso (hT.map k) := image_comparison_iso hTI hJimg (hT.map k) hTk_fac
  -- …and faithfulness reflects it: `k` is an iso, with inverse `kinv : J → image f`.
  obtain ⟨kinv, _hk1, hk2⟩ := hfaithful.2 k hTk_iso
  refine ⟨hJallows, ?_⟩
  -- `J` is minimal: for any `S` allowing `f`, factor `J ≤ image f ≤ S`.
  intro S hS
  obtain ⟨t, ht⟩ := hI.2 S hS
  exact ⟨kinv ≫ t, by
    calc (kinv ≫ t) ≫ S.arr = kinv ≫ t ≫ S.arr     := Cat.assoc _ _ _
      _ = kinv ≫ (image f).arr                       := by rw [ht]
      _ = kinv ≫ k ≫ J.arr                           := by rw [hk]
      _ = (kinv ≫ k) ≫ J.arr                         := (Cat.assoc _ _ _).symm
      _ = Cat.id J.dom ≫ J.arr                       := by rw [hk2]
      _ = J.arr                                      := Cat.id_comp _⟩

/-! ## §1.514 Epic

  A finite family {xᵢ : Aᵢ → B} is EPIC (jointly epimorphic) if
  for any g,h : B → X, agreeing on all xᵢ ≫ g = xᵢ ≫ h implies g = h. -/

def Epic {n : Nat} (x : Fin n → Σ A : 𝒞, A ⟶ B) : Prop :=
  ∀ (X : 𝒞) (g h : B ⟶ X), (∀ i : Fin n, (x i).2 ≫ g = (x i).2 ≫ h) → g = h

end Freyd
