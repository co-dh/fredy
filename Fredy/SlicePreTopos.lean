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

section rung01
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

/-- `Σ_B (R ⊚ S)` and `(Σ_B R) ⊚ (Σ_B S)` are mutually contained: the comparison iso. -/
theorem forgetSlice_compose_iso (R : BinRel (Over B) X Y) (S : BinRel (Over B) Y Z) :
    ((R ⊚ S).forgetSlice ⊂ (R.forgetSlice ⊚ S.forgetSlice)) ∧
    ((R.forgetSlice ⊚ S.forgetSlice) ⊂ (R ⊚ S).forgetSlice) :=
  ⟨forgetSlice_compose_le R S, le_forgetSlice_compose R S⟩

end composeComparison

end rung01

variable {B : 𝒞}

/-! ## Rung 2: `EffectiveRegular (Over B)`

  A slice equivalence relation `E` forgets to a `𝒞`-equivalence relation `E̅` (reflexivity and
  symmetry transport on the nose; transitivity uses the rung-1 comparison).  `𝒞`'s effectiveness
  hands a cover `q̄ : X.dom ↠ Q₀` with `E̅ ≅ q̄q̄°`.  Both legs `E.colA.f, E.colB.f` equalise
  `X.hom`, and `q̄` coequalises them (`cover_is_coequalizer_of_level`), so `X.hom = q̄ ≫ b` for a
  unique `b : Q₀ ⟶ B`.  Then `q : X ↠ ⟨Q₀, b⟩` is a slice cover whose slice level forgets back to
  `E̅`; reflecting the `𝒞`-iso through `Σ_B` (faithful) and the rung-1 comparison gives the slice
  iso `E ≅ q q°`, i.e. `IsEffective E`. -/

section effective
-- `EffectiveRegular 𝒞` bundles `HasPullbacks`/`HasImages`/`HasBinaryProducts`; using it as the
-- sole source (no standalone `[HasPullbacks 𝒞]` here) keeps a single instance, so the slice
-- relation predicates and `EffectiveRegular.effective` agree without a diamond.
variable [EffectiveRegular 𝒞] {X : Over B}

/-- `kernelPairRel g ⊂ (graph g) ⊚ (graph g)°` (re-proved here; the `S1_64` copy is `private`).
    The kernel-pair legs cone over `g, g`, lift into the composition's pullback, then through
    `image.lift`. -/
theorem kernelPairRel_le_graphComp [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    [HasImages 𝒞] {A Q : 𝒞} (g : A ⟶ Q) :
    RelLe (kernelPairRel g) ((graph g) ⊚ (graph g)°) := by
  let pb := HasPullbacks.has (graph g).colB ((graph g)°).colA
  let a' := pb.cone.π₁ ≫ (graph g).colA
  let c' := pb.cone.π₂ ≫ ((graph g)°).colB
  let sp : pb.cone.pt ⟶ prod A A := pair a' c'
  have hcone : kp₁ (f := g) ≫ (graph g).colB = kp₂ (f := g) ≫ ((graph g)°).colA := by
    simp only [graph, reciprocal]; exact kp_sq
  let v := pb.lift ⟨_, kp₁ (f := g), kp₂ (f := g), hcone⟩
  have hv1 : v ≫ pb.cone.π₁ = kp₁ (f := g) := pb.lift_fst _
  have hv2 : v ≫ pb.cone.π₂ = kp₂ (f := g) := pb.lift_snd _
  refine ⟨⟨v ≫ image.lift sp, ?_, ?_⟩⟩
  · show (v ≫ image.lift sp) ≫ ((image sp).arr ≫ fst) = kp₁ (f := g)
    calc (v ≫ image.lift sp) ≫ ((image sp).arr ≫ fst)
        = v ≫ ((image.lift sp ≫ (image sp).arr) ≫ fst) := by simp [Cat.assoc]
      _ = v ≫ (sp ≫ fst) := by rw [image.lift_fac]
      _ = v ≫ a' := by rw [fst_pair]
      _ = (v ≫ pb.cone.π₁) ≫ (graph g).colA := by dsimp [a']; rw [Cat.assoc]
      _ = kp₁ (f := g) := by rw [hv1]; simp [graph, Cat.comp_id]
  · show (v ≫ image.lift sp) ≫ ((image sp).arr ≫ snd) = kp₂ (f := g)
    calc (v ≫ image.lift sp) ≫ ((image sp).arr ≫ snd)
        = v ≫ ((image.lift sp ≫ (image sp).arr) ≫ snd) := by simp [Cat.assoc]
      _ = v ≫ (sp ≫ snd) := by rw [image.lift_fac]
      _ = v ≫ c' := by rw [snd_pair]
      _ = (v ≫ pb.cone.π₂) ≫ ((graph g)°).colB := by dsimp [c']; rw [Cat.assoc]
      _ = kp₂ (f := g) := by rw [hv2]; simp [graph, reciprocal, Cat.comp_id]

/-- The forgotten relation of a slice equivalence relation is a `𝒞`-equivalence relation. -/
theorem forgetSlice_equivalenceRelation (E : BinRel (Over B) X X)
    (hE : EquivalenceRelation E) : EquivalenceRelation E.forgetSlice := by
  obtain ⟨⟨ho, hoA, hoB⟩, hsym, htrans⟩ := hE
  refine ⟨⟨ho.f, ?_, ?_⟩, ?_, ?_⟩
  · -- reflexivity, column A: `ho.f ≫ E.colA.f = (ho ⊚ E.colA).f = id`
    show ho.f ≫ E.colA.f = Cat.id X.dom
    exact congrArg OverHom.f hoA
  · show ho.f ≫ E.colB.f = Cat.id X.dom
    exact congrArg OverHom.f hoB
  · -- symmetry: forget the slice `RelHom E ⟶ E°`; `(E°).forgetSlice = (E.forgetSlice)°` (rfl).
    exact forgetSlice_mono_relLe hsym
  · -- transitivity: `E̅ ⊚ E̅ ⊂ (E ⊚ E).forgetSlice ⊂ E̅`.
    exact rel_le_trans (le_forgetSlice_compose E E) (forgetSlice_mono_relLe htrans)

/-- Both legs of `E̅ = E.forgetSlice` equalise `X.hom` (both compose to `E.src.hom`). -/
theorem forgetSlice_legs_equalise (E : BinRel (Over B) X X) :
    E.forgetSlice.colA ≫ X.hom = E.forgetSlice.colB ≫ X.hom := by
  show E.colA.f ≫ X.hom = E.colB.f ≫ X.hom
  rw [E.colA.w, E.colB.w]

/-- `Σ_B (graph q ⊚ (graph q)°) ` versus `graph q.f ⊚ (graph q.f)°`: contained each way
    via rung 1 and the on-the-nose `forgetSlice_graph` / `forgetSlice_reciprocal`. -/
theorem forgetSlice_graphComp_iso {Q : Over B} (q : OverHom X Q) :
    ((graph q ⊚ (graph q)°).forgetSlice ⊂ (graph q.f ⊚ (graph q.f)°)) ∧
    ((graph q.f ⊚ (graph q.f)°) ⊂ (graph q ⊚ (graph q)°).forgetSlice) := by
  have he : (graph q).forgetSlice = graph q.f := forgetSlice_graph q
  have hr : ((graph q)°).forgetSlice = (graph q.f)° := by
    rw [forgetSlice_reciprocal, he]
  refine ⟨?_, ?_⟩
  · have := forgetSlice_compose_le (graph q) ((graph q)°)
    rwa [he, hr] at this
  · have := le_forgetSlice_compose (graph q) ((graph q)°)
    rwa [he, hr] at this

/-- **Rung 2: every slice equivalence relation is effective.**  Forget to `𝒞`, apply `𝒞`'s
    effectiveness for the cover `q̄`, factor `X.hom = q̄ ≫ b` (leg-equalisation + coequaliser),
    lift `q̄` to a slice cover `q : X ↠ ⟨Q₀, b⟩`, and reflect the `𝒞`-iso `E̅ ≅ q̄q̄°` back through
    `Σ_B` (faithful) using rung 1. -/
theorem sliceIsEffective (E : BinRel (Over B) X X) (hE : EquivalenceRelation E) :
    IsEffective E := by
  -- forget and apply 𝒞-effectiveness
  obtain ⟨_, Q₀, qbar, hqcov, hf1, hf2⟩ :=
    EffectiveRegular.effective E.forgetSlice (forgetSlice_equivalenceRelation E hE)
  -- hf1 : E̅ ⊂ graph q̄ ⊚ graph q̄°,  hf2 : graph q̄ ⊚ graph q̄° ⊂ E̅
  -- `X.hom` equalises `q̄`'s kernel pair, so it factors `q̄ ≫ b`.
  have hkpb : kp₁ (f := qbar) ≫ X.hom = kp₂ (f := qbar) ≫ X.hom := by
    obtain ⟨w, hwA0, hwB0⟩ := rel_le_trans (kernelPairRel_le_graphComp qbar) hf2
    -- restate with the defeq-normalised kernel-pair legs.
    have hwA : w ≫ E.forgetSlice.colA = kp₁ (f := qbar) := hwA0
    have hwB : w ≫ E.forgetSlice.colB = kp₂ (f := qbar) := hwB0
    calc kp₁ (f := qbar) ≫ X.hom = (w ≫ E.forgetSlice.colA) ≫ X.hom := by rw [hwA]
      _ = w ≫ (E.forgetSlice.colA ≫ X.hom) := Cat.assoc _ _ _
      _ = w ≫ (E.forgetSlice.colB ≫ X.hom) := by rw [forgetSlice_legs_equalise]
      _ = (w ≫ E.forgetSlice.colB) ≫ X.hom := (Cat.assoc _ _ _).symm
      _ = kp₂ (f := qbar) ≫ X.hom := by rw [hwB]
  obtain ⟨b, hqb, _⟩ := cover_is_coequalizer_of_level qbar hqcov X.hom hkpb
  -- slice quotient object and slice cover
  let Q : Over B := ⟨Q₀, b⟩
  let q : OverHom X Q := ⟨qbar, hqb⟩
  have hqcov_slice : Cover (𝒞 := Over B) q := cover_of_cover_f q hqcov
  obtain ⟨hgc1, hgc2⟩ := forgetSlice_graphComp_iso q
  refine ⟨hE, Q, q, hqcov_slice, ?_, ?_⟩
  · -- E ⊂ graph q ⊚ graph q°  (reflect: E̅ ⊂ (graph q ⊚ graph q°).forgetSlice)
    apply forgetSlice_reflects_relLe
    exact rel_le_trans hf1 hgc2
  · -- graph q ⊚ graph q° ⊂ E  (reflect: (...).forgetSlice ⊂ E̅)
    apply forgetSlice_reflects_relLe
    exact rel_le_trans hgc1 hf2

end effective

/-- **The slice of an effective regular category is effective regular** (rung 2). -/
instance overEffectiveRegular (B : 𝒞) [EffectiveRegular 𝒞] : EffectiveRegular (Over B) where
  effective E hE := sliceIsEffective E hE

/-! ## Rung 4: `HasReflTransClosure (Over B)`

  The reflexive-transitive closure of a slice relation `R` is the slice lift of `rtc R̄`
  (`R̄ = R.forgetSlice`).  `R̄`'s legs equalise `A.hom` (they come from slice arrows), and
  `kernelPairRel A.hom` is a reflexive+transitive relation containing `R̄`, so by `rtc`-minimality
  `rtc R̄`'s legs *also* equalise `A.hom`; hence `rtc R̄` lifts to a slice relation `M` with
  `M.forgetSlice = rtc R̄` (on the nose).  Reflexivity/transitivity/minimality then transport
  through `forgetSlice_reflects_relLe` and the rung-1 comparison. -/

section rtc
variable [RegularCategory 𝒞] [HasReflTransClosure 𝒞] {A : Over B}

/-- Lift a `𝒞`-relation on `A.dom` whose legs equalise `A.hom` back to a slice relation on `A`.
    Round-trips with `forgetSlice` on the nose. -/
def BinRel.liftSlice (M : BinRel 𝒞 A.dom A.dom)
    (hleg : M.colA ≫ A.hom = M.colB ≫ A.hom) : BinRel (Over B) A A where
  src := ⟨M.src, M.colA ≫ A.hom⟩
  colA := ⟨M.colA, rfl⟩
  colB := ⟨M.colB, hleg.symm⟩
  isMonicPair := by
    intro W f g hA hB
    apply OverHom.ext
    exact M.isMonicPair f.f g.f (congrArg OverHom.f hA) (congrArg OverHom.f hB)

@[simp] theorem BinRel.forgetSlice_liftSlice (M : BinRel 𝒞 A.dom A.dom)
    (hleg : M.colA ≫ A.hom = M.colB ≫ A.hom) :
    (BinRel.liftSlice M hleg).forgetSlice = M := rfl

/-- `R.forgetSlice`'s legs equalise `A.hom` (they are slice arrows). -/
theorem forgetSlice_endo_legs_equalise (R : BinRel (Over B) A A) :
    R.forgetSlice.colA ≫ A.hom = R.forgetSlice.colB ≫ A.hom := by
  show R.colA.f ≫ A.hom = R.colB.f ≫ A.hom
  rw [R.colA.w, R.colB.w]

/-- `kernelPairRel A.hom`'s legs equalise `A.hom` (`kp₁ ≫ A.hom = kp₂ ≫ A.hom`). -/
theorem kernelPairRel_legs_equalise (A : Over B) :
    (kernelPairRel A.hom).colA ≫ A.hom = (kernelPairRel A.hom).colB ≫ A.hom :=
  kp_sq

/-- `rtc R̄`'s legs equalise `A.hom`: `rtc R̄ ⊂ kernelPairRel A.hom` (a reflexive+transitive
    relation containing `R̄`), and the latter equalises by `kp_sq`. -/
theorem rtc_forgetSlice_legs_equalise (R : BinRel (Over B) A A) :
    (rtc R.forgetSlice).colA ≫ A.hom = (rtc R.forgetSlice).colB ≫ A.hom := by
  -- `R̄ ⊂ kernelPairRel A.hom`: the kernel-pair lift of `R̄`'s (equalising) legs is the witness.
  have hRle : RelLe R.forgetSlice (kernelPairRel A.hom) :=
    ⟨⟨(HasPullbacks.has A.hom A.hom).lift
        ⟨R.forgetSlice.src, R.forgetSlice.colA, R.forgetSlice.colB,
          forgetSlice_endo_legs_equalise R⟩,
      kp_lift_p₁ _ _ (forgetSlice_endo_legs_equalise R),
      kp_lift_p₂ _ _ (forgetSlice_endo_legs_equalise R)⟩⟩
  -- `kernelPairRel A.hom` is reflexive + transitive
  obtain ⟨hrefl, _, htrans⟩ := level_is_equivalence_relation A.hom
  have hreflD : IsReflexive (kernelPairRel A.hom) := by
    obtain ⟨h, hA, hB⟩ := hrefl
    exact ⟨⟨h, by simpa [graph, Cat.id_comp] using hA, by simpa [graph, Cat.id_comp] using hB⟩⟩
  -- `rtc R̄ ⊂ kernelPairRel A.hom`
  obtain ⟨w, hwA, hwB⟩ := rtc_minimal R.forgetSlice (kernelPairRel A.hom) hRle hreflD htrans
  calc (rtc R.forgetSlice).colA ≫ A.hom
      = (w ≫ (kernelPairRel A.hom).colA) ≫ A.hom := by rw [hwA]
    _ = w ≫ ((kernelPairRel A.hom).colA ≫ A.hom) := Cat.assoc _ _ _
    _ = w ≫ ((kernelPairRel A.hom).colB ≫ A.hom) := by rw [kernelPairRel_legs_equalise]
    _ = (w ≫ (kernelPairRel A.hom).colB) ≫ A.hom := (Cat.assoc _ _ _).symm
    _ = (rtc R.forgetSlice).colB ≫ A.hom := by rw [hwB]

/-- The slice reflexive-transitive closure: lift `rtc R̄` back to the slice. -/
def sliceTransRefClos (R : BinRel (Over B) A A) : TransRefClos R where
  clos := BinRel.liftSlice (rtc R.forgetSlice) (rtc_forgetSlice_legs_equalise R)
  le := by
    apply forgetSlice_reflects_relLe
    rw [BinRel.forgetSlice_liftSlice]
    exact le_rtc R.forgetSlice
  refl := by
    -- `1_A ⊂ M`: reflect `graph (id A.dom) ⊂ rtc R̄`; `(graph (id A)).forgetSlice = graph (id A.dom)`.
    have h := forgetSlice_reflects_relLe (R := graph (Cat.id A))
      (S := BinRel.liftSlice (rtc R.forgetSlice) (rtc_forgetSlice_legs_equalise R))
    apply h
    rw [BinRel.forgetSlice_liftSlice]
    -- `(graph (Cat.id A)).forgetSlice = graph (Cat.id A.dom)` on the nose.
    show graph (Cat.id A.dom) ⊂ rtc R.forgetSlice
    exact rtc_reflexive R.forgetSlice
  trans := by
    -- `M ⊚ M ⊂ M`: reflect to `(M ⊚ M).forgetSlice ⊂ M̄`; forward-compare then `rtc`-transitivity.
    apply forgetSlice_reflects_relLe
    rw [BinRel.forgetSlice_liftSlice]
    refine rel_le_trans (forgetSlice_compose_le _ _) ?_
    rw [BinRel.forgetSlice_liftSlice]
    exact rtc_transitive R.forgetSlice
  minimal := by
    intro T hRT hReflT hTransT
    -- reflect `M̄ ⊂ T̄` via `rtc`-minimality on `R̄ ⊂ T̄`, `T̄` reflexive + transitive.
    apply forgetSlice_reflects_relLe
    rw [BinRel.forgetSlice_liftSlice]
    refine rtc_minimal R.forgetSlice T.forgetSlice (forgetSlice_mono_relLe hRT) ?_ ?_
    · -- `T̄` reflexive: reflect `graph (id A.dom) ⊂ T̄` from slice `1_A ⊂ T`.
      have := forgetSlice_mono_relLe hReflT
      -- `(graph (Cat.id A)).forgetSlice = graph (Cat.id A.dom)`.
      exact this
    · -- `T̄` transitive: `T̄ ⊚ T̄ ⊂ (T ⊚ T).forgetSlice ⊂ T̄`.
      exact rel_le_trans (le_forgetSlice_compose T T) (forgetSlice_mono_relLe hTransT)

end rtc

/-- **The slice of a category with reflexive-transitive closures has them** (rung 4). -/
instance overHasReflTransClosure (B : 𝒞) [RegularCategory 𝒞] [HasReflTransClosure 𝒞] :
    HasReflTransClosure (Over B) where
  transRefClos R := sliceTransRefClos R

/-! ## Residual: completing the slice pre-topos tower (toward §1.662 Diaconescu)

  Rungs 1, 2, 4 are now DONE sorry-free above:

  1. ✅ **Forget commutes with the calculus** (`BinRel.forgetSlice`, `forgetSlice_graph`,
     `forgetSlice_reciprocal` on the nose; `forgetSlice_compose_le` + `le_forgetSlice_compose`
     for `⊚` up to the comparison iso; `forgetSlice_mono_relLe` / `forgetSlice_reflects_relLe`
     for faithfulness).
  2. ✅ **`EffectiveRegular (Over B)`** (`overEffectiveRegular`, via `sliceIsEffective`).
  4. ✅ **`HasReflTransClosure (Over B)`** (`overHasReflTransClosure`, via `sliceTransRefClos`).

  REMAINING (next-rung residual):

  3. **`DisjointBinaryCoproduct (Over B)`** — NOT yet built.  This is the heaviest rung: it
     extends `PositivePreLogos (Over B)`, which in turn needs `HasBinaryCoproducts (Over B)`
     (slice coproduct `X + Y → B` by copairing the two structure maps), `HasSubobjectUnions
     (Over B)`, and the full `PreLogos (Over B)` data (`bottom`, `bottom_min`, `bottom_dom_iso`,
     `invImage_preserves_union`, `invImage_preserves_bottom`).  NONE of these slice instances
     exist yet in the repo.  Only after `PositivePreLogos (Over B)` is in hand can the three
     §1.621 disjointness fields (`inl_monic`, `inr_monic`, `inl_inter_inr`, `inl_union_inr`)
     be transported.  Combined with rung 2 this would give `PreToposDisjoint (Over B)`; with
     rung 4 it closes the §1.662 Diaconescu hypotheses.  This is a self-contained multi-hundred-
     line PreLogos-transport (slice coproducts + subobject-union transport along the faithful
     forgetful functor `Σ_B`, which preserves images and pullbacks) and is the exact next task.

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
