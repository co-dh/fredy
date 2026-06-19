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
import Fredy.S1_56
import Fredy.S1_59
import Fredy.S1_62
import Fredy.S1_77
import Fredy.S1_64
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

/-! ## `RegularCategory (Over B)`

  With `HasImages (Over B)` now in hand, all four `RegularCategory` mixins for `Over B`
  are available: `HasTerminal` (`overHasTerminal`, §1.44), `HasBinaryProducts`
  (`overHasBinaryProducts`, §1.441), `HasPullbacks` (`overHasPullbacks`, §1.441), and
  `PullbacksTransferCovers` (`overPullbacksTransferCovers`, §1.52).  The slice of a regular
  category is regular. -/
instance overRegular (B : 𝒞) [RegularCategory 𝒞] : RegularCategory (Over B) where

/-! ## Rung 1: the forgetful functor on binary relations

  `Σ_B` sends a slice relation `R : BinRel (Over B) X Y` to the `𝒞`-relation on
  `X.dom, Y.dom` with columns `R.colA.f, R.colB.f`.  Joint monicity transports by the
  same object-promotion trick as `sigma_preserves_mono`: a bare span `f, g : W ⟶ R.src.dom`
  equalising both forgotten columns promotes to a slice span (give `W` the structure map
  `f ≫ R.src.hom`), where `R.isMonicPair` cancels it. -/

/-- The underlying `𝒞`-relation of a slice relation `R : BinRel (Over B) X Y`. -/
def BinRel.forgetSlice {X Y : Over B} (R : BinRel (Over B) X Y) :
    BinRel 𝒞 X.dom Y.dom where
  src := R.src.dom
  colA := R.colA.f
  colB := R.colB.f
  isMonicPair := by
    intro W f g hA hB
    -- Promote `f` to the slice span `⟨W, f ≫ R.src.hom⟩ ⟶ R.src`.
    have hgw : g ≫ R.src.hom = f ≫ R.src.hom := by
      have : f ≫ (R.colA.f ≫ X.hom) = g ≫ (R.colA.f ≫ X.hom) := by
        rw [← Cat.assoc, ← Cat.assoc, hA]
      rw [R.colA.w] at this; exact this.symm
    let Wo : Over B := ⟨W, f ≫ R.src.hom⟩
    let fo : OverHom Wo R.src := ⟨f, rfl⟩
    let go : OverHom Wo R.src := ⟨g, hgw⟩
    have := R.isMonicPair fo go (OverHom.ext hA) (OverHom.ext hB)
    exact congrArg OverHom.f this

@[simp] theorem BinRel.forgetSlice_src {X Y : Over B} (R : BinRel (Over B) X Y) :
    R.forgetSlice.src = R.src.dom := rfl
@[simp] theorem BinRel.forgetSlice_colA {X Y : Over B} (R : BinRel (Over B) X Y) :
    R.forgetSlice.colA = R.colA.f := rfl
@[simp] theorem BinRel.forgetSlice_colB {X Y : Over B} (R : BinRel (Over B) X Y) :
    R.forgetSlice.colB = R.colB.f := rfl

/-- `Σ_B` commutes with `reciprocal` on the nose. -/
theorem forgetSlice_reciprocal {X Y : Over B} (R : BinRel (Over B) X Y) :
    (reciprocal R).forgetSlice = reciprocal R.forgetSlice := rfl

/-- `Σ_B` commutes with `graph` on the nose: `Σ_B (graph m) = graph m.f`. -/
theorem forgetSlice_graph {X Y : Over B} (m : OverHom X Y) :
    (graph m).forgetSlice = graph m.f := rfl

/-- `Σ_B` is monotone on relations: a slice `RelHom R ⟶ S` forgets to a `𝒞`
    `RelHom R.forgetSlice ⟶ S.forgetSlice` (its witness arrow is `.f`). -/
theorem forgetSlice_mono_relLe {X Y : Over B} {R S : BinRel (Over B) X Y}
    (h : R ⊂ S) : R.forgetSlice ⊂ S.forgetSlice := by
  obtain ⟨k, hA, hB⟩ := h
  exact ⟨⟨k.f, congrArg OverHom.f hA, congrArg OverHom.f hB⟩⟩

/-- `Σ_B` reflects relation containment: a `𝒞` `RelHom` between forgotten relations
    promotes (object-promotion trick) to a slice `RelHom`. -/
theorem forgetSlice_reflects_relLe {X Y : Over B} {R S : BinRel (Over B) X Y}
    (h : R.forgetSlice ⊂ S.forgetSlice) : R ⊂ S := by
  obtain ⟨k, hA, hB⟩ := h
  -- `k : R.src.dom ⟶ S.src.dom`, `k ≫ S.colA.f = R.colA.f`, etc.  Promote `k`.
  have hkf : k ≫ S.colA.f = R.colA.f := hA
  have hkw : k ≫ S.src.hom = R.src.hom := by
    have : k ≫ (S.colA.f ≫ X.hom) = R.colA.f ≫ X.hom := by rw [← Cat.assoc, hkf]
    rwa [S.colA.w, R.colA.w] at this
  exact ⟨⟨⟨k, hkw⟩, OverHom.ext hA, OverHom.ext hB⟩⟩

/-! ### `Σ_B` commutes with `⊚` up to the canonical comparison iso

  The slice composite `R ⊚ S` is the slice image of the slice span over the *slice* pullback
  `R.colB ×_Y S.colA`; forgetting, the underlying span lives over the base pullback
  `R.colB.f ×_{Y.dom} S.colA.f`, and the slice image forgets to the base image (definitionally,
  by `overHasImages = liftSlice ∘ image`).  The base composite `Σ_B R ⊚ Σ_B S` is the base image
  of the base span over the *base* pullback `R.colB.f ×_{Y.dom} S.colA.f`.  Both spans land on the
  same legs once the two chosen pullbacks are compared; `relLe_of_cover_factor` (cover⊥mono) gives
  the containment each way without identifying the chosen pullbacks/images on the nose. -/

section composeComparison
variable [RegularCategory 𝒞] {X Y Z : Over B}

/-- `Σ_B (R ⊚ S) ⊂ (Σ_B R) ⊚ (Σ_B S)`: the slice composite forgets into the base composite. -/
theorem forgetSlice_compose_le (R : BinRel (Over B) X Y) (S : BinRel (Over B) Y Z) :
    (R ⊚ S).forgetSlice ⊂ (R.forgetSlice ⊚ S.forgetSlice) := by
  -- slice pullback of the inner legs, and its forgotten (base) span
  let pbs := HasPullbacks.has R.colB S.colA
  let spans : pbs.cone.pt ⟶ (overProdPt X Z) :=
    pair (pbs.cone.π₁ ⊚ R.colA) (pbs.cone.π₂ ⊚ S.colB)
  -- base pullback of the forgotten legs, with its comparison map from `pbs.cone.pt.dom`
  let pbc := HasPullbacks.has R.colB.f S.colA.f
  have hpbsw : (pbs.cone.π₁).f ≫ R.colB.f = (pbs.cone.π₂).f ≫ S.colA.f :=
    congrArg OverHom.f pbs.cone.w
  let cmp : pbs.cone.pt.dom ⟶ pbc.cone.pt :=
    pbc.lift ⟨pbs.cone.pt.dom, (pbs.cone.π₁).f, (pbs.cone.π₂).f, hpbsw⟩
  have hcmp₁ : cmp ≫ pbc.cone.π₁ = (pbs.cone.π₁).f := pbc.lift_fst _
  have hcmp₂ : cmp ≫ pbc.cone.π₂ = (pbs.cone.π₂).f := pbc.lift_snd _
  let spanc : pbc.cone.pt ⟶ prod X.dom Z.dom :=
    pair (pbc.cone.π₁ ≫ R.colA.f) (pbc.cone.π₂ ≫ S.colB.f)
  -- the cover onto `(R⊚S).forgetSlice.src = (image spans.f).dom` is `image.lift spans.f`
  refine relLe_of_cover_factor (Y := R.forgetSlice ⊚ S.forgetSlice)
    (image.lift spans.f) (image_lift_cover spans.f)
    (cmp ≫ image.lift spanc) ?_ ?_
  · -- column A
    show (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ fst)
        = image.lift spans.f ≫ ((R ⊚ S).forgetSlice.colA)
    have hL : (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ fst)
        = (pbs.cone.π₁).f ≫ R.colA.f := by
      calc (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ fst)
          = cmp ≫ ((image.lift spanc ≫ (image spanc).arr) ≫ fst) := by
            rw [Cat.assoc cmp, ← Cat.assoc (image.lift spanc)]
        _ = cmp ≫ (spanc ≫ fst) := by rw [image.lift_fac]
        _ = cmp ≫ (pbc.cone.π₁ ≫ R.colA.f) := by rw [show spanc ≫ fst = _ from fst_pair _ _]
        _ = (cmp ≫ pbc.cone.π₁) ≫ R.colA.f := (Cat.assoc _ _ _).symm
        _ = (pbs.cone.π₁).f ≫ R.colA.f := by rw [hcmp₁]
    have hR : image.lift spans.f ≫ ((R ⊚ S).forgetSlice.colA)
        = (pbs.cone.π₁).f ≫ R.colA.f := by
      calc image.lift spans.f ≫ ((image spans.f).arr ≫ (overProdFst X Z).f)
          = (image.lift spans.f ≫ (image spans.f).arr) ≫ (overProdFst X Z).f := (Cat.assoc _ _ _).symm
        _ = spans.f ≫ (overProdFst X Z).f := by rw [image.lift_fac]
        _ = (spans ⊚ overProdFst X Z).f := rfl
        _ = (pbs.cone.π₁ ⊚ R.colA).f := by
            rw [show spans ⊚ overProdFst X Z = _ from overProdPair_fst _ _]
        _ = (pbs.cone.π₁).f ≫ R.colA.f := rfl
    rw [hL, hR]
  · -- column B (mirror)
    show (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ snd)
        = image.lift spans.f ≫ ((R ⊚ S).forgetSlice.colB)
    have hL : (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ snd)
        = (pbs.cone.π₂).f ≫ S.colB.f := by
      calc (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ snd)
          = cmp ≫ ((image.lift spanc ≫ (image spanc).arr) ≫ snd) := by
            rw [Cat.assoc cmp, ← Cat.assoc (image.lift spanc)]
        _ = cmp ≫ (spanc ≫ snd) := by rw [image.lift_fac]
        _ = cmp ≫ (pbc.cone.π₂ ≫ S.colB.f) := by rw [show spanc ≫ snd = _ from snd_pair _ _]
        _ = (cmp ≫ pbc.cone.π₂) ≫ S.colB.f := (Cat.assoc _ _ _).symm
        _ = (pbs.cone.π₂).f ≫ S.colB.f := by rw [hcmp₂]
    have hR : image.lift spans.f ≫ ((R ⊚ S).forgetSlice.colB)
        = (pbs.cone.π₂).f ≫ S.colB.f := by
      calc image.lift spans.f ≫ ((image spans.f).arr ≫ (overProdSnd X Z).f)
          = (image.lift spans.f ≫ (image spans.f).arr) ≫ (overProdSnd X Z).f := (Cat.assoc _ _ _).symm
        _ = spans.f ≫ (overProdSnd X Z).f := by rw [image.lift_fac]
        _ = (spans ⊚ overProdSnd X Z).f := rfl
        _ = (pbs.cone.π₂ ⊚ S.colB).f := by
            rw [show spans ⊚ overProdSnd X Z = _ from overProdPair_snd _ _]
        _ = (pbs.cone.π₂).f ≫ S.colB.f := rfl
    rw [hL, hR]

/-- `(Σ_B R) ⊚ (Σ_B S) ⊂ Σ_B (R ⊚ S)`: the base composite forgets back into the slice
    composite.  The base pullback `pbc` maps into the forgotten slice pullback (a base
    pullback by `sliceForget_preserves_isPullback`); the rest mirrors `forgetSlice_compose_le`. -/
theorem le_forgetSlice_compose (R : BinRel (Over B) X Y) (S : BinRel (Over B) Y Z) :
    (R.forgetSlice ⊚ S.forgetSlice) ⊂ (R ⊚ S).forgetSlice := by
  let pbs := HasPullbacks.has R.colB S.colA
  let spans : pbs.cone.pt ⟶ (overProdPt X Z) :=
    pair (pbs.cone.π₁ ⊚ R.colA) (pbs.cone.π₂ ⊚ S.colB)
  let pbc := HasPullbacks.has R.colB.f S.colA.f
  let spanc : pbc.cone.pt ⟶ prod X.dom Z.dom :=
    pair (pbc.cone.π₁ ≫ R.colA.f) (pbc.cone.π₂ ≫ S.colB.f)
  -- the forgotten slice pullback is a base pullback; lift `pbc.cone` into it.
  have hsforget : (sliceConeForget pbs.cone).IsPullback :=
    sliceForget_preserves_isPullback pbs.cone pbs.cone_isPullback
  obtain ⟨cmp, ⟨hcmp₁0, hcmp₂0⟩, _⟩ := hsforget pbc.cone
  -- restate with the defeq-normalised legs `(pbs.cone.π·).f`.
  have hcmp₁ : cmp ≫ (pbs.cone.π₁).f = pbc.cone.π₁ := hcmp₁0
  have hcmp₂ : cmp ≫ (pbs.cone.π₂).f = pbc.cone.π₂ := hcmp₂0
  refine relLe_of_cover_factor (X := R.forgetSlice ⊚ S.forgetSlice)
    (image.lift spanc) (image_lift_cover spanc)
    (cmp ≫ image.lift spans.f) ?_ ?_
  · show (cmp ≫ image.lift spans.f) ≫ ((R ⊚ S).forgetSlice.colA)
        = image.lift spanc ≫ ((image spanc).arr ≫ fst)
    have hL : (cmp ≫ image.lift spans.f) ≫ ((R ⊚ S).forgetSlice.colA)
        = pbc.cone.π₁ ≫ R.colA.f := by
      calc (cmp ≫ image.lift spans.f) ≫ ((image spans.f).arr ≫ (overProdFst X Z).f)
          = cmp ≫ ((image.lift spans.f ≫ (image spans.f).arr) ≫ (overProdFst X Z).f) := by
            rw [Cat.assoc cmp, ← Cat.assoc (image.lift spans.f)]
        _ = cmp ≫ (spans.f ≫ (overProdFst X Z).f) := by rw [image.lift_fac]
        _ = cmp ≫ ((spans ⊚ overProdFst X Z).f) := rfl
        _ = cmp ≫ ((pbs.cone.π₁ ⊚ R.colA).f) := by
            rw [show spans ⊚ overProdFst X Z = _ from overProdPair_fst _ _]
        _ = cmp ≫ ((pbs.cone.π₁).f ≫ R.colA.f) := rfl
        _ = (cmp ≫ (pbs.cone.π₁).f) ≫ R.colA.f := (Cat.assoc _ _ _).symm
        _ = pbc.cone.π₁ ≫ R.colA.f := by rw [hcmp₁]
    have hR : image.lift spanc ≫ ((image spanc).arr ≫ fst) = pbc.cone.π₁ ≫ R.colA.f := by
      calc image.lift spanc ≫ ((image spanc).arr ≫ fst)
          = (image.lift spanc ≫ (image spanc).arr) ≫ fst := (Cat.assoc _ _ _).symm
        _ = spanc ≫ fst := by rw [image.lift_fac]
        _ = pbc.cone.π₁ ≫ R.colA.f := fst_pair _ _
    rw [hL, hR]
  · show (cmp ≫ image.lift spans.f) ≫ ((R ⊚ S).forgetSlice.colB)
        = image.lift spanc ≫ ((image spanc).arr ≫ snd)
    have hL : (cmp ≫ image.lift spans.f) ≫ ((R ⊚ S).forgetSlice.colB)
        = pbc.cone.π₂ ≫ S.colB.f := by
      calc (cmp ≫ image.lift spans.f) ≫ ((image spans.f).arr ≫ (overProdSnd X Z).f)
          = cmp ≫ ((image.lift spans.f ≫ (image spans.f).arr) ≫ (overProdSnd X Z).f) := by
            rw [Cat.assoc cmp, ← Cat.assoc (image.lift spans.f)]
        _ = cmp ≫ (spans.f ≫ (overProdSnd X Z).f) := by rw [image.lift_fac]
        _ = cmp ≫ ((spans ⊚ overProdSnd X Z).f) := rfl
        _ = cmp ≫ ((pbs.cone.π₂ ⊚ S.colB).f) := by
            rw [show spans ⊚ overProdSnd X Z = _ from overProdPair_snd _ _]
        _ = cmp ≫ ((pbs.cone.π₂).f ≫ S.colB.f) := rfl
        _ = (cmp ≫ (pbs.cone.π₂).f) ≫ S.colB.f := (Cat.assoc _ _ _).symm
        _ = pbc.cone.π₂ ≫ S.colB.f := by rw [hcmp₂]
    have hR : image.lift spanc ≫ ((image spanc).arr ≫ snd) = pbc.cone.π₂ ≫ S.colB.f := by
      calc image.lift spanc ≫ ((image spanc).arr ≫ snd)
          = (image.lift spanc ≫ (image spanc).arr) ≫ snd := (Cat.assoc _ _ _).symm
        _ = spanc ≫ snd := by rw [image.lift_fac]
        _ = pbc.cone.π₂ ≫ S.colB.f := snd_pair _ _
    rw [hL, hR]

end composeComparison

/-! ## Residual: completing the slice pre-topos tower (toward §1.662 Diaconescu)

  With `HasImages (Over B)` and `RegularCategory (Over B)` above, the slice now supports the
  full relational calculus of §1.56 (`BinRel (Over B)`, `⊚`, `reciprocal`, `graph`, `RelLe`,
  `EquivalenceRelation`, `IsEffective`), because that calculus is generic over any category
  with `HasBinaryProducts + HasPullbacks + HasImages`.  What remains for the prompt's target
  `one_one_choice_to_boolean` (`S1_64`, §1.662) — i.e. for `∀ A, DecidableObject A` from
  `Choice (1+1)` — is the following tower, each step well-defined but substantial:

  1. **Forget commutes with the calculus.**  The forgetful `Σ_B : Over B → 𝒞` preserves
     pullbacks (`sliceForget_preserves_isPullback`) and images (`overHasImages`, this file),
     so for slice relations `R, S` on `X` there are RelHom-isos
       `Σ_B(R ⊚ S) ≅ Σ_B R ⊚ Σ_B S`,  `Σ_B(R°) ≅ (Σ_B R)°`,  `Σ_B(graph m) ≅ graph m.f`.
     PROVING these on the nose is the bulk: `compose` is defined via the *chosen* pullback and
     *chosen* image of a span, and `Σ_B` lands on a different chosen pullback/image of the
     forwarded span, so the identification is up-to-the-canonical-comparison-iso, not `rfl`.
     (Engine: `image_comparison_iso` + `sliceForget_preserves_isPullback` per operation.)

  2. **`EffectiveRegular (Over B)`.**  Given an equivalence relation `E : BinRel (Over B) X X`,
     its underlying `E̅ : BinRel 𝒞 X.dom X.dom` (columns `E.colA.f`, `E.colB.f`) is an
     equivalence relation in `𝒞` by step 1.  KEY: the two legs automatically equalize `X.hom`
     (both `E.colA.f ≫ X.hom` and `E.colB.f ≫ X.hom` equal `E.src.hom`, since `colA, colB`
     are slice arrows).  `𝒞`'s `EffectiveRegular.effective` gives a cover `q : X.dom ↠ Q₀` with
     `E̅ = level q`; the leg-equalisation lets `X.hom` factor as `q ≫ b` (`b : Q₀ → B`,
     `cover_is_coequalizer_of_level` / `cover_epi`).  Then `q : X → ⟨Q₀, b⟩` is a slice cover
     (`cover_of_cover_f`) whose slice level is `E` (step 1 + `sliceForget_preserves_isPullback`
     on the kernel pair).  Hence `IsEffective E`, giving `EffectiveRegular (Over B)` and so
     `PreTopos (Over B)` once `PositivePreLogos (Over B)` is supplied.

  3. **`DisjointBinaryCoproduct (Over B)`.**  Slice coproducts are `𝒞`-coproducts over `B`
     (`X + Y → B` by copairing the two structure maps); the positive/disjointness data
     (`inlSub`, `inrSub`, `inl_inter_inr_le_bottom`, `inl_union_inr_entire`, §1.62) transports
     because forget preserves the union/intersection of subobjects (it preserves images and
     pullbacks, the ingredients of `PreLogos`).  Needs `PositivePreLogos (Over B)` first.

  4. **`HasReflTransClosure (Over B)`.**  The rtc of a slice relation `R` is the slice lift of
     `rtc (Σ_B R)`: reflexivity/transitivity/minimality transport along the RelHom-isos of
     step 1, so `transRefClos` for `Over B` is built from `𝒞`'s.

  5. **Diaconescu transport (final).**  `preTopos_boolean_iff_all_decidable.mpr` reduces the
     `S1_64` goal to `∀ A, DecidableObject A`.  Decidability of `A` is the diagonal
     `Δ : A ↣ A×A` complemented; working in the slice `𝒮(A×A)` (now a pre-topos by 2–4),
     `Δ` is a subobject of the slice terminal, and `Choice (1+1)` in `𝒞` transports to
     `Choice (1_𝒮 + 1_𝒮)` in `𝒮(A×A)` (this is `Choice ((A×A) + (A×A) → A×A)`, the codiagonal
     slice object — a projectivity-transport step, NOT automatic from `Choice (1+1)` in `𝒞`).
     Then the §1.658 engine `subobject_complemented_of_decidable` / `preTopos_boolean_iff_all_decidable`
     run *inside the slice* to complement `Δ`, i.e. make `A` decidable.

  Steps 1–4 are mechanical transport (no new mathematical idea, but ~several hundred lines).
  Step 5's projectivity transport (`Choice (1+1)` ⇒ slice codiagonal choice) is the one genuinely
  delicate point and the true residual flagged in the `one_one_choice_to_boolean` doc-comment. -/

end Freyd
