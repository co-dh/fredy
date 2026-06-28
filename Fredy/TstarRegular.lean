/-
  Freyd & Scedrov, *Categories and Allegories* — §1.634 / §1.635 (stalk FAMILY).

  **The product stalk functor `T⋆ : 𝒞 → Set^I` is a representation of REGULAR categories.**

  `S1_62` builds the ultra-filter stalk family `Tstar A = (F̂ ↦ T_F̂ A)` into the power
  `(StalkIndex 𝒞 → Type u)`, and `StalkRegular` proves that for EACH ultra-filter `F̂` the fibre
  functor `T_F̂ = TF F̂.val` is a `RegularFunctor` (`TF_regularFunctor`).  Here we package the FAMILY:
  since `Tstar` is, at every fibre `F̂`, exactly the functor `TF F̂.val`, and limits / images / monos
  / covers in the power `Set^I` are computed FIBREWISE, each of the five `RegularFunctor` fields for
  `Tstar` reduces — definitionally at each fibre — to the corresponding per-fibre `TF_*` lemma.

  Cover- and image-preservation need the elements of each ultra-filter to be PROJECTIVE; in a CAPITAL
  positive pre-logos that is §1.633 (`capital_filter_projective`), so the only hypothesis is
  `Capital`.  The members of an ultra-filter are complemented subterminators (the 2nd component of
  `IsUltraFilter`), and §1.633 turns that into projectivity.
-/
import Fredy.StalkRegular
import Fredy.S2_218
import Fredy.StalkDetect

universe u v w

namespace Freyd

open PreLogosHorn.Stalk SetRegular

/-! ## Fibrewise bridges for the power category `Set^I = (I → Type w)`

  Three elementary facts: an iso / image / pullback in the power is exactly a fibrewise iso / image /
  pullback.  (Monos and covers already have `power_monic_iff` / `power_cover_iff` in `S1_62`.)  These
  let us reduce each `Preserves*` for `Tstar` to the per-fibre `TF_*` lemma. -/

/-- A power morphism is an iso iff it is fibrewise an iso. -/
theorem power_isIso_iff {I : Type w} {X Y : I → Type w} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i, @IsIso (Type w) _ (X i) (Y i) (f i) := by
  constructor
  · rintro ⟨g, h1, h2⟩ i
    exact ⟨g i, congrFun h1 i, congrFun h2 i⟩
  · intro h
    refine ⟨fun i => (h i).choose, ?_, ?_⟩
    · funext i x; exact congrFun (h i).choose_spec.1 x
    · funext i x; exact congrFun (h i).choose_spec.2 x

/-- A power cone is a pullback as soon as it is a pullback in every fibre. -/
theorem power_isPullback_of_fibrewise {I : Type w} {A B C : I → Type w}
    {f : A ⟶ C} {g : B ⟶ C} (c : Cone f g)
    (h : ∀ i, (Cone.mk (c.pt i) (c.π₁ i) (c.π₂ i) (congrFun c.w i)).IsPullback) :
    c.IsPullback := by
  intro d
  let fibreD : ∀ i, Cone (f i) (g i) :=
    fun i => Cone.mk (d.pt i) (d.π₁ i) (d.π₂ i) (congrFun d.w i)
  refine ⟨fun i => (h i (fibreD i)).choose, ⟨?_, ?_⟩, ?_⟩
  · funext i x; exact congrFun (h i (fibreD i)).choose_spec.1.1 x
  · funext i x; exact congrFun (h i (fibreD i)).choose_spec.1.2 x
  · intro u hu1 hu2
    funext i x
    exact congrFun ((h i (fibreD i)).choose_spec.2 (u i) (congrFun hu1 i) (congrFun hu2 i)) x

/-- A subobject of a power object is the image of `f` as soon as it is, fibrewise, the image of
    `f i`.  The fibre subobject of `J` at `i` is `⟨J.dom i, J.arr i, …⟩`. -/
theorem power_isImage_of_fibrewise {I : Type w} {A B : I → Type w} (f : A ⟶ B)
    (J : Subobject (I → Type w) B)
    (h : ∀ i, IsImage (f i)
      ⟨J.dom i, J.arr i, (set_monic_iff_injective _).mpr ((power_monic_iff J.arr).mp J.monic i)⟩) :
    IsImage f J := by
  refine ⟨⟨fun i => (h i).1.choose, ?_⟩, ?_⟩
  · funext i x; exact congrFun (h i).1.choose_spec x
  · intro S hS
    obtain ⟨t, ht⟩ := hS
    have key : ∀ i, ∃ r : J.dom i ⟶ S.dom i, r ≫ S.arr i = J.arr i := fun i =>
      (h i).2 (@Subobject.mk (Type w) _ (B i) (S.dom i) (S.arr i)
                ((set_monic_iff_injective (S.arr i)).mpr ((power_monic_iff S.arr).mp S.monic i)))
              ⟨t i, congrFun ht i⟩
    refine ⟨fun i => (key i).choose, ?_⟩
    funext i x
    exact congrFun (key i).choose_spec x

/-! ## The five `RegularFunctor` fields for `Tstar`, lifted fibrewise from `TF_*`. -/

variable {𝒞 : Type u} [Cat.{u} 𝒞] [DisjointBinaryCoproduct 𝒞]

/-- `T⋆` preserves binary products: fibrewise this is `TF_preserves_binaryProducts`. -/
theorem Tstar_preservesBinaryProducts :
    PreservesBinaryProducts (Tstar (𝒞 := 𝒞)) := by
  intro A B
  rw [power_isIso_iff]
  intro F
  exact TF_preserves_binaryProducts F.val F.property.1.1

/-- `T⋆` preserves pullbacks: fibrewise this is `TF_preserves_pullbacks`. -/
theorem Tstar_preservesPullbacks :
    PreservesPullbacks (Tstar (𝒞 := 𝒞)) := by
  intro A B C f g c hc
  apply power_isPullback_of_fibrewise
  intro F
  exact TF_preserves_pullbacks F.val F.property.1.1 f g c hc

/-- `T⋆` preserves monos: fibrewise this is `TF_preserves_mono`. -/
theorem Tstar_preservesMono :
    PreservesMono (Tstar (𝒞 := 𝒞)) := by
  intro X Y f hf
  rw [power_monic_iff]
  intro F
  exact (set_monic_iff_injective _).mp (TF_preserves_mono F.val F.property.1.1 hf)

/-- `T⋆` preserves covers.  Each ultra-filter member is a complemented subterminator
    (`F.property.2.1`), hence projective in a capital pre-logos (`capital_filter_projective`,
    §1.633), so the per-fibre `TF_preserves_covers_of_projective` applies. -/
theorem Tstar_preservesCovers (hcap : Capital (𝒞 := 𝒞)) :
    PreservesCovers (Tstar (𝒞 := 𝒞)) := by
  intro A B f hf
  rw [power_cover_iff]
  intro F
  have hproj := capital_filter_projective hcap F.val F.property.2.1
  exact (set_cover_iff_surjective _).mp
    (TF_preserves_covers_of_projective F.val hproj f hf)

/-- `T⋆` preserves images, fibrewise from `TF_preserves_images` (projectivity via §1.633). -/
theorem Tstar_preservesImages (hcap : Capital (𝒞 := 𝒞)) :
    PreservesImages (Tstar (𝒞 := 𝒞)) Tstar_preservesMono := by
  intro A B f I hI
  apply power_isImage_of_fibrewise
  intro F
  have hproj := capital_filter_projective hcap F.val F.property.2.1
  exact TF_preserves_images F.val F.property.1.1 hproj f I hI

/-- **§1.635 — the product stalk functor `T⋆ : 𝒞 → Set^I` is a regular functor.**

  For a CAPITAL positive (disjoint-coproduct) pre-logos, the ultra-filter stalk FAMILY
  `Tstar A = (F̂ ↦ T_F̂ A)` preserves binary products, pullbacks, covers, monos, and images — each
  field lifting fibrewise from the per-fibre `TF_regularFunctor` (`StalkRegular`), with cover/image
  projectivity supplied by §1.633 (`capital_filter_projective`). -/
theorem Tstar_regularFunctor (hcap : Capital (𝒞 := 𝒞)) :
    RelFunctor.RegularFunctor (Tstar (𝒞 := 𝒞)) where
  pres_prod := Tstar_preservesBinaryProducts
  pres_pullback := Tstar_preservesPullbacks
  pres_covers := Tstar_preservesCovers hcap
  pres_mono := Tstar_preservesMono
  pres_image := Tstar_preservesImages hcap

end Freyd
