/-
# The slice of a pre-topos is a pre-topos (§1.65 / Diaconescu support)

  This file builds, for a base object `B` of a category `𝒞`, the structures on the
  slice `Over B` that a pre-topos `𝒞` induces, by transporting them along the *faithful*
  forgetful functor `Σ_B : Over B → 𝒞` (`SliceForget B`, `X ↦ X.dom`).

  The forgetful functor creates these structures because it is faithful, preserves and
  reflects monos (`sigma_preserves_mono` / `sigma_reflects_mono`, §1.531), preserves and
  reflects covers (`cover_f_of_cover` / `cover_of_cover_f`, §1.531), and preserves
  pullbacks (`sliceForget_preserves_isPullback`).  Concretely:

  * `HasImages (Over B)` — the image of `m : X ⟶ Y` is the `𝒞`-image of `m.f`, equipped
    with its induced map to `B`.  Bidirectional mono/cover transport make it the smallest
    slice subobject allowing `m`.  This is the FOUNDATION the relational calculus needs.

  The remaining tower (`EffectiveRegular (Over B)`, `DisjointBinaryCoproduct (Over B)`,
  `HasReflTransClosure (Over B)`) and the final Diaconescu transport are tracked in the
  trailing doc-comment; this file lands the image foundation sorry-free.
-/
import Fredy.S1_44
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.SliceRegular

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

variable [HasPullbacks 𝒞]

/-! ## Subobject correspondence `Subobject (Over B) Y ≃ Subobject 𝒞 Y.dom`

  A slice subobject of `Y : Over B` is a slice-monic `S.arr : S.dom ↣ Y`; its underlying
  arrow `S.arr.f : S.dom.dom ↣ Y.dom` is a `𝒞`-mono (Σ preserves monos).  Conversely a
  `𝒞`-mono `m : C ↣ Y.dom` lifts to the slice object `⟨C, m ≫ Y.hom⟩` with slice-monic
  inclusion `⟨m, rfl⟩` (Σ reflects monos). -/

variable {B : 𝒞}

/-- The underlying `𝒞`-subobject of a slice subobject `S` of `Y`. -/
def Subobject.forgetSlice (Y : Over B) (S : Subobject (Over B) Y) : Subobject 𝒞 Y.dom where
  dom := S.dom.dom
  arr := S.arr.f
  monic := sigma_preserves_mono S.arr S.monic

/-- Lift a `𝒞`-subobject `T` of `Y.dom` to a slice subobject of `Y`. -/
def Subobject.liftSlice (Y : Over B) (T : Subobject 𝒞 Y.dom) : Subobject (Over B) Y where
  dom := ⟨T.dom, T.arr ≫ Y.hom⟩
  arr := ⟨T.arr, rfl⟩
  monic := sigma_reflects_mono (⟨T.arr, rfl⟩ : OverHom ⟨T.dom, T.arr ≫ Y.hom⟩ Y) T.monic

/-- A slice subobject `S` allows a slice arrow `m` iff its underlying `𝒞`-subobject allows
    the underlying arrow `m.f`. -/
theorem allows_forgetSlice_iff {Y X : Over B} (S : Subobject (Over B) Y) (m : OverHom X Y) :
    Allows S m ↔ Allows (Subobject.forgetSlice Y S) m.f := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.f, congrArg OverHom.f hg⟩
  · rintro ⟨g, hg⟩
    -- `g : X.dom → S.dom.dom` with `g ≫ S.arr.f = m.f`; promote to a slice arrow.
    have hgf : g ≫ S.arr.f = m.f := hg
    have hgw : g ≫ S.dom.hom = X.hom := by
      have : g ≫ (S.arr.f ≫ Y.hom) = m.f ≫ Y.hom := by rw [← Cat.assoc, hgf]
      rwa [S.arr.w, m.w] at this
    exact ⟨⟨g, hgw⟩, OverHom.ext hg⟩

/-! ## `HasImages (Over B)`

  The image of `m : X ⟶ Y` in `Over B` is the lift of the `𝒞`-image of `m.f`. -/

/-- The slice image of `m : X ⟶ Y`: lift the `𝒞`-image of `m.f` to a slice subobject of `Y`. -/
def sliceImage [HasImages 𝒞] {X Y : Over B} (m : OverHom X Y) : Subobject (Over B) Y :=
  Subobject.liftSlice Y (image m.f)

/-- The slice image is an image: it allows `m` and is below any slice subobject allowing `m`. -/
theorem sliceImage_isImage [HasImages 𝒞] {X Y : Over B} (m : OverHom X Y) :
    IsImage m (sliceImage m) := by
  refine ⟨?_, ?_⟩
  · -- allows `m`: the underlying subobject of the lift of `image m.f` is `image m.f`.
    have hund : Allows (Subobject.forgetSlice Y (Subobject.liftSlice Y (image m.f))) m.f :=
      image_allows m.f
    exact (allows_forgetSlice_iff (Subobject.liftSlice Y (image m.f)) m).mpr hund
  · intro S hS
    -- `S` allows `m` ⟹ underlying allows `m.f` ⟹ `image m.f ≤ S.forgetSlice` ⟹ slice `≤`.
    have hund : Allows (Subobject.forgetSlice Y S) m.f :=
      (allows_forgetSlice_iff S m).mp hS
    obtain ⟨h, hh⟩ := image_min m.f (Subobject.forgetSlice Y S) hund
    -- `h : (image m.f).dom → S.dom.dom`, `h ≫ S.arr.f = (image m.f).arr`.
    have hhf : h ≫ S.arr.f = (image m.f).arr := hh
    have hw : h ≫ S.dom.hom = (Subobject.liftSlice Y (image m.f)).dom.hom := by
      show h ≫ S.dom.hom = (image m.f).arr ≫ Y.hom
      have : h ≫ (S.arr.f ≫ Y.hom) = (image m.f).arr ≫ Y.hom := by rw [← Cat.assoc, hhf]
      rwa [S.arr.w] at this
    exact ⟨⟨h, hw⟩, OverHom.ext hhf⟩

/-- **The slice of a category with images has images.**  Built by transporting the
    `𝒞`-image along the faithful forgetful functor `Σ_B`. -/
instance overHasImages [HasImages 𝒞] (B : 𝒞) : HasImages (Over B) where
  image := sliceImage
  isImage := sliceImage_isImage

end Freyd
