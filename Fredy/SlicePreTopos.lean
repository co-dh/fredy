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
  trailing doc-comment; this file lands the image foundation Sorry-free.
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
import Fredy.Complement
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

/-! ## Rung 3: `DisjointBinaryCoproduct (Over B)`

  The heaviest rung.  Its mathematical content is entirely *transport along the faithful
  forgetful functor* `Σ_B`: a slice subobject of `Y : Over B` IS a `𝒞`-subobject of `Y.dom`
  (the structure map rides along), via the round-tripping pair `Subobject.forgetSlice` /
  `Subobject.liftSlice` (`forgetSlice (liftSlice T) = T` on the nose).  So the ENTIRE
  `PreLogos (Over B)` lattice structure is the `𝒞` one re-attached to the structure map:

  * `bottom A := liftSlice (bottom A.dom)`,
  * `union S T := liftSlice (union (forgetSlice S) (forgetSlice T))`,
  * `InverseImage` transports because `Σ_B` preserves pullbacks
    (`sliceForget_preserves_isPullback`).

  The only genuinely new construction is the slice coproduct `X + Y` = `X.dom + Y.dom` with
  structure map `case X.hom Y.hom` (copairing); the four §1.621 disjointness fields then
  transport from `𝒞`'s `DisjointBinaryCoproduct` through the subobject identification. -/

section rung3
variable {B : 𝒞} [HasPullbacks 𝒞]

/-! ### Subobject correspondence is an order-iso `Sub (Over B) Y ≃ Sub 𝒞 Y.dom`

  `forgetSlice`/`liftSlice` are mutually monotone and `forgetSlice ∘ liftSlice = id` on the
  nose, so each lattice operation transports field-for-field. -/

/-- `forgetSlice` is monotone: a slice `S ≤ T` forgets to `S.forgetSlice ≤ T.forgetSlice`. -/
theorem Subobject.forgetSlice_mono {Y : Over B} {S T : Subobject (Over B) Y}
    (h : S.le T) : (Subobject.forgetSlice Y S).le (Subobject.forgetSlice Y T) := by
  obtain ⟨g, hg⟩ := h; exact ⟨g.f, congrArg OverHom.f hg⟩

/-- `forgetSlice` reflects `≤`: promote the underlying factorization arrow to a slice arrow. -/
theorem Subobject.forgetSlice_reflects {Y : Over B} {S T : Subobject (Over B) Y}
    (h : (Subobject.forgetSlice Y S).le (Subobject.forgetSlice Y T)) : S.le T := by
  obtain ⟨g, hg⟩ := h
  have hgf : g ≫ T.arr.f = S.arr.f := hg
  have hgw : g ≫ T.dom.hom = S.dom.hom := by
    have : g ≫ (T.arr.f ≫ Y.hom) = S.arr.f ≫ Y.hom := by rw [← Cat.assoc, hgf]
    rwa [T.arr.w, S.arr.w] at this
  exact ⟨⟨g, hgw⟩, OverHom.ext hgf⟩

/-- `liftSlice` is monotone: a `𝒞` `S ≤ T` lifts to a slice `liftSlice S ≤ liftSlice T`. -/
theorem Subobject.liftSlice_mono {Y : Over B} {S T : Subobject 𝒞 Y.dom}
    (h : S.le T) : (Subobject.liftSlice Y S).le (Subobject.liftSlice Y T) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨⟨g, ?_⟩, OverHom.ext hg⟩
  show g ≫ (T.arr ≫ Y.hom) = S.arr ≫ Y.hom
  rw [← Cat.assoc, hg]

/-- Mutual `≤` of `𝒞`-subobjects gives a `𝒞`-iso of their domains (subobject antisymmetry):
    the two factorization maps cancel by monicity of the respective subobject arrows. -/
theorem Subobject.le_antisymm_iso {W : 𝒞} {S T : Subobject 𝒞 W}
    (h1 : S.le T) (h2 : T.le S) : Isomorphic S.dom T.dom := by
  obtain ⟨a, ha⟩ := h1; obtain ⟨c, hc⟩ := h2
  refine ⟨a, c, ?_, ?_⟩
  · apply S.monic; rw [Cat.assoc, hc, ha, Cat.id_comp]
  · apply T.monic; rw [Cat.assoc, ha, hc, Cat.id_comp]

/-! ### `Σ_B` transports the inverse image (it preserves pullbacks)

  The slice inverse image `InverseImage (Over B) f S` is the slice pullback of `f` along
  `S.arr`; forgetting, that slice pullback is a *base* pullback of `(f.f, S.forgetSlice.arr)`
  (`sliceForget_preserves_isPullback`), hence mutually `≤` with the chosen base inverse image
  `InverseImage f.f S.forgetSlice`. -/

/-- The forgotten slice inverse image is below the base inverse image. -/
theorem forgetSlice_invImage_le {X Y : Over B} (f : OverHom X Y) (S : Subobject (Over B) Y) :
    Subobject.le (Subobject.forgetSlice X (InverseImage f S))
                 (InverseImage f.f (Subobject.forgetSlice Y S)) := by
  let pbc := HasPullbacks.has f.f (Subobject.forgetSlice Y S).arr
  exact ⟨pbc.lift (sliceConeForget (overPullbackCone f S.arr)),
    pbc.lift_fst (sliceConeForget (overPullbackCone f S.arr))⟩

/-- The base inverse image is below the forgotten slice inverse image. -/
theorem le_forgetSlice_invImage {X Y : Over B} (f : OverHom X Y) (S : Subobject (Over B) Y) :
    Subobject.le (InverseImage f.f (Subobject.forgetSlice Y S))
                 (Subobject.forgetSlice X (InverseImage f S)) := by
  have hfor : (sliceConeForget (B := B) (overPullbackCone f S.arr)).IsPullback :=
    sliceForget_preserves_isPullback _ ((overHasPullbacks B).has f S.arr).cone_isPullback
  obtain ⟨h, ⟨h₁, _⟩, _⟩ := hfor (HasPullbacks.has f.f (Subobject.forgetSlice Y S).arr).cone
  exact ⟨h, h₁⟩

end rung3

/-! ### Slice binary coproducts (the one genuinely new construction)

  `X + Y` in `Over B` is `X.dom + Y.dom` with structure map `case X.hom Y.hom`; the injections
  are the `𝒞` injections (as slice arrows), and the universal property copairs. -/

open HasBinaryCoproducts in
/-- **The slice of a category with binary coproducts has binary coproducts.**  The coproduct of
    `X→B`, `Y→B` is `X.dom + Y.dom → B` via the copairing `case X.hom Y.hom`. -/
instance overHasBinaryCoproducts (B : 𝒞) [HasBinaryCoproducts 𝒞] :
    HasBinaryCoproducts (Over B) where
  coprod X Y := ⟨coprod X.dom Y.dom, case X.hom Y.hom⟩
  inl {X Y} := ⟨inl, case_inl _ _⟩
  inr {X Y} := ⟨inr, case_inr _ _⟩
  case {W X Y} f g := ⟨case f.f g.f, by
    apply case_uniq
    · rw [← Cat.assoc, case_inl, f.w]
    · rw [← Cat.assoc, case_inr, g.w]⟩
  case_inl {W X Y} f g := OverHom.ext (case_inl _ _)
  case_inr {W X Y} f g := OverHom.ext (case_inr _ _)
  case_uniq {W X Y} f g h h1 h2 :=
    OverHom.ext (case_uniq _ _ h.f (congrArg OverHom.f h1) (congrArg OverHom.f h2))

/-! ### `PreLogos (Over B)` by domain transport

  Every lattice field is the `𝒞` operation on `Y.dom`'s subobject lattice, re-attached to the
  structure map.  `bottom`/`union`/`inverse image` all round-trip through `forgetSlice`. -/

section overPreLogos
variable [PreLogos 𝒞]

/-- `forgetSlice` is a retraction of `liftSlice` on the nose. -/
@[simp] theorem forgetSlice_liftSlice (Y : Over B) (T : Subobject 𝒞 Y.dom) :
    Subobject.forgetSlice Y (Subobject.liftSlice Y T) = T := rfl

/-- Slice subobject unions: lift the `𝒞`-union of the forgotten subobjects. -/
instance overHasSubobjectUnions (B : 𝒞) : HasSubobjectUnions (Over B) where
  union {Y} S T := Subobject.liftSlice Y
    (HasSubobjectUnions.union (Subobject.forgetSlice Y S) (Subobject.forgetSlice Y T))
  union_left {Y} S T := by
    apply Subobject.forgetSlice_reflects
    rw [forgetSlice_liftSlice]
    exact HasSubobjectUnions.union_left _ _
  union_right {Y} S T := by
    apply Subobject.forgetSlice_reflects
    rw [forgetSlice_liftSlice]
    exact HasSubobjectUnions.union_right _ _
  union_min {Y} S T U hSU hTU := by
    apply Subobject.forgetSlice_reflects
    rw [forgetSlice_liftSlice]
    exact HasSubobjectUnions.union_min _ _ _
      (Subobject.forgetSlice_mono hSU) (Subobject.forgetSlice_mono hTU)

@[simp] theorem forgetSlice_union (Y : Over B) (S T : Subobject (Over B) Y) :
    Subobject.forgetSlice Y (HasSubobjectUnions.union S T)
      = HasSubobjectUnions.union (Subobject.forgetSlice Y S) (Subobject.forgetSlice Y T) := rfl

/-- `𝒞`-union is monotone in both arguments (from `union_min`/`union_left`/`union_right`). -/
theorem union_mono {W : 𝒞} {S S' T T' : Subobject 𝒞 W}
    (hS : S.le S') (hT : T.le T') :
    (HasSubobjectUnions.union S T).le (HasSubobjectUnions.union S' T') :=
  HasSubobjectUnions.union_min _ _ _
    (subLe_trans' hS (HasSubobjectUnions.union_left S' T'))
    (subLe_trans' hT (HasSubobjectUnions.union_right S' T'))

/-- **The slice of a pre-logos is a pre-logos.**  Subobject lattices, bottom, and inverse-image
    preservation all transport from `𝒞`'s lattice on `Y.dom` along the subobject identification
    `Sub (Over B) Y ≃ Sub 𝒞 Y.dom`. -/
instance overPreLogos (B : 𝒞) : PreLogos (Over B) where
  bottom A := Subobject.liftSlice A (PreLogos.bottom A.dom)
  bottom_min {A} S := by
    apply Subobject.forgetSlice_reflects
    rw [forgetSlice_liftSlice]
    exact PreLogos.bottom_min _
  bottom_dom_iso A A' := by
    -- both slice-bottom domains have `𝒞`-domain the coterminator `0`, hence iso; promote
    -- the `𝒞`-iso to a slice iso using uniqueness of maps out of an initial object.
    letI hCot := minimal_subobject_of_one_is_coterminator (𝒞 := 𝒞) ‹PreLogos 𝒞›
    have h1 : Isomorphic (PreLogos.bottom A.dom).dom hCot.zero := PreLogos.bottom_dom_iso A.dom _
    have h2 : Isomorphic (PreLogos.bottom A'.dom).dom hCot.zero := PreLogos.bottom_dom_iso A'.dom _
    obtain ⟨g, ginv, hgg, hgg'⟩ := isomorphic_trans h1 (isomorphic_symm h2)
    obtain ⟨φ, φinv, hφ, _⟩ := h1
    have uniqA : ∀ {Z : 𝒞} (p q : (PreLogos.bottom A.dom).dom ⟶ Z), p = q := fun p q => by
      have : φinv ≫ p = φinv ≫ q := hCot.init_uniq _ _
      calc p = (φ ≫ φinv) ≫ p := by rw [hφ, Cat.id_comp]
        _ = φ ≫ (φinv ≫ q) := by rw [Cat.assoc, this]
        _ = q := by rw [← Cat.assoc, hφ, Cat.id_comp]
    obtain ⟨ψ, ψinv, hψ, _⟩ := h2
    have uniqA' : ∀ {Z : 𝒞} (p q : (PreLogos.bottom A'.dom).dom ⟶ Z), p = q := fun p q => by
      have : ψinv ≫ p = ψinv ≫ q := hCot.init_uniq _ _
      calc p = (ψ ≫ ψinv) ≫ p := by rw [hψ, Cat.id_comp]
        _ = ψ ≫ (ψinv ≫ q) := by rw [Cat.assoc, this]
        _ = q := by rw [← Cat.assoc, hψ, Cat.id_comp]
    exact ⟨⟨g, uniqA _ _⟩, ⟨ginv, uniqA' _ _⟩, OverHom.ext hgg, OverHom.ext hgg'⟩
  invImage_preserves_union {X Y} f S T := by
    -- forget both sides to `𝒞`, chain through `𝒞`'s preservation and the `Σ_B`-invImage
    -- transport (`forgetSlice_invImage_le` / `le_forgetSlice_invImage`), reflect back.
    refine ⟨?_, ?_⟩
    · apply Subobject.forgetSlice_reflects
      show Subobject.le
          (Subobject.forgetSlice X (InverseImage f (HasSubobjectUnions.union S T)))
          (HasSubobjectUnions.union (Subobject.forgetSlice X (InverseImage f S))
                                    (Subobject.forgetSlice X (InverseImage f T)))
      refine subLe_trans' (forgetSlice_invImage_le f _) ?_
      refine subLe_trans' (PreLogos.invImage_preserves_union f.f
        (Subobject.forgetSlice Y S) (Subobject.forgetSlice Y T)).1 ?_
      exact union_mono (le_forgetSlice_invImage f S) (le_forgetSlice_invImage f T)
    · apply Subobject.forgetSlice_reflects
      show Subobject.le
          (HasSubobjectUnions.union (Subobject.forgetSlice X (InverseImage f S))
                                    (Subobject.forgetSlice X (InverseImage f T)))
          (Subobject.forgetSlice X (InverseImage f (HasSubobjectUnions.union S T)))
      refine subLe_trans'
        (union_mono (forgetSlice_invImage_le f S) (forgetSlice_invImage_le f T)) ?_
      refine subLe_trans' ?_ (le_forgetSlice_invImage f _)
      exact (PreLogos.invImage_preserves_union f.f
        (Subobject.forgetSlice Y S) (Subobject.forgetSlice Y T)).2
  invImage_preserves_bottom {X Y} f := by
    -- domain iso `(f# ⊥).dom ≅ ⊥.dom` in `𝒞` (from invImage transport + `𝒞`'s preservation),
    -- promoted to a slice iso using uniqueness of maps out of the initial bottom-domain.
    letI hCot := minimal_subobject_of_one_is_coterminator (𝒞 := 𝒞) ‹PreLogos 𝒞›
    let S : Subobject (Over B) Y := Subobject.liftSlice Y (PreLogos.bottom Y.dom)
    have hAC : Isomorphic (Subobject.forgetSlice X (InverseImage f S)).dom
                          (InverseImage f.f (PreLogos.bottom Y.dom)).dom :=
      Subobject.le_antisymm_iso (forgetSlice_invImage_le f S) (le_forgetSlice_invImage f S)
    have hABD : Isomorphic (Subobject.forgetSlice X (InverseImage f S)).dom
                           (PreLogos.bottom X.dom).dom :=
      isomorphic_trans hAC (PreLogos.invImage_preserves_bottom f.f)
    have hD0 : Isomorphic (PreLogos.bottom X.dom).dom hCot.zero := PreLogos.bottom_dom_iso X.dom _
    obtain ⟨φ, φinv, hφ, _⟩ := isomorphic_trans hABD hD0
    obtain ⟨g, ginv, hgg, hgg'⟩ := hABD
    have uniqA : ∀ {Z : 𝒞}
        (p q : (Subobject.forgetSlice X (InverseImage f S)).dom ⟶ Z), p = q := fun p q => by
      have : φinv ≫ p = φinv ≫ q := hCot.init_uniq _ _
      calc p = (φ ≫ φinv) ≫ p := by rw [hφ, Cat.id_comp]
        _ = φ ≫ (φinv ≫ q) := by rw [Cat.assoc, this]
        _ = q := by rw [← Cat.assoc, hφ, Cat.id_comp]
    obtain ⟨ψ, ψinv, hψ, _⟩ := hD0
    have uniqD : ∀ {Z : 𝒞} (p q : (PreLogos.bottom X.dom).dom ⟶ Z), p = q := fun p q => by
      have : ψinv ≫ p = ψinv ≫ q := hCot.init_uniq _ _
      calc p = (ψ ≫ ψinv) ≫ p := by rw [hψ, Cat.id_comp]
        _ = ψ ≫ (ψinv ≫ q) := by rw [Cat.assoc, this]
        _ = q := by rw [← Cat.assoc, hψ, Cat.id_comp]
    exact ⟨⟨g, uniqA _ _⟩, ⟨ginv, uniqD _ _⟩, OverHom.ext hgg, OverHom.ext hgg'⟩

end overPreLogos

/-! ### `PositivePreLogos (Over B)` and the §1.621 disjointness fields

  With `PreLogos (Over B)` and `HasBinaryCoproducts (Over B)` in hand, `PositivePreLogos
  (Over B)` is immediate.  The four §1.621 disjointness fields transport from `𝒞`'s
  `DisjointBinaryCoproduct` through the subobject identification:  the slice injection `inl`
  is `⟨inl, …⟩`, monic by `sigma_reflects_mono`; disjointness `inl ∩ inr ≤ ⊥` and the cover
  `⊤ ≤ inl ∪ inr` reflect from the corresponding `𝒞` facts. -/

section overDisjoint
variable [DisjointBinaryCoproduct 𝒞]

instance overPositivePreLogos (B : 𝒞) : PositivePreLogos (Over B) where

/-- The slice left injection `inl : X ⟶ X+Y` is monic (`Σ_B` reflects monos). -/
theorem over_inl_monic {X Y : Over B} :
    Mono (HasBinaryCoproducts.inl (𝒞 := Over B) (A := X) (B := Y)) :=
  sigma_reflects_mono (HasBinaryCoproducts.inl (𝒞 := Over B)) DisjointBinaryCoproduct.inl_monic

/-- The slice right injection `inr : Y ⟶ X+Y` is monic. -/
theorem over_inr_monic {X Y : Over B} :
    Mono (HasBinaryCoproducts.inr (𝒞 := Over B) (A := X) (B := Y)) :=
  sigma_reflects_mono (HasBinaryCoproducts.inr (𝒞 := Over B)) DisjointBinaryCoproduct.inr_monic

/-- The forgotten slice intersection is below the `𝒞`-intersection of the forgotten subobjects
    (`Σ_B` preserves the defining pullback): lift the forgotten slice pullback into the chosen
    base pullback. -/
theorem forgetSlice_inter_le {Y : Over B} (S T : Subobject (Over B) Y) :
    Subobject.le (Subobject.forgetSlice Y (Subobject.inter S T))
                 (Subobject.inter (Subobject.forgetSlice Y S) (Subobject.forgetSlice Y T)) := by
  let pbc := HasPullbacks.has (Subobject.forgetSlice Y S).arr (Subobject.forgetSlice Y T).arr
  refine ⟨pbc.lift (sliceConeForget (overPullbackCone S.arr T.arr)), ?_⟩
  show pbc.lift _ ≫ (pbc.cone.π₁ ≫ (Subobject.forgetSlice Y S).arr) = _
  rw [← Cat.assoc, pbc.lift_fst]; rfl

/-- **Rung 3: the slice of a disjoint-binary-coproduct pre-topos has disjoint binary coproducts.**
    The four §1.621 fields transport through the subobject identification `Sub (Over B) Y ≃
    Sub 𝒞 Y.dom`:  injections are monic by `sigma_reflects_mono`; `inl ∩ inr ≤ ⊥` forgets to the
    `𝒞` disjointness through `forgetSlice_inter_le`; `⊤ ≤ inl ∪ inr` forgets to the `𝒞` union
    cover (the slice union/bottom/entire forget on the nose). -/
instance overDisjointBinaryCoproduct (B : 𝒞) : DisjointBinaryCoproduct (Over B) where
  inl_monic := over_inl_monic
  inr_monic := over_inr_monic
  inl_inter_inr {X Y} := by
    apply Subobject.forgetSlice_reflects
    show Subobject.le
        (Subobject.forgetSlice (HasBinaryCoproducts.coprod X Y)
          (Subobject.inter (inlSub over_inl_monic) (inrSub over_inr_monic)))
        (PreLogos.bottom (HasBinaryCoproducts.coprod X Y).dom)
    exact subLe_trans' (forgetSlice_inter_le _ _) inl_inter_inr_le_bottom
  inl_union_inr {X Y} := by
    apply Subobject.forgetSlice_reflects
    show Subobject.le
        (Subobject.forgetSlice (HasBinaryCoproducts.coprod X Y)
          (Subobject.entire (HasBinaryCoproducts.coprod X Y)))
        (HasSubobjectUnions.union
          (Subobject.forgetSlice (HasBinaryCoproducts.coprod X Y) (inlSub over_inl_monic))
          (Subobject.forgetSlice (HasBinaryCoproducts.coprod X Y) (inrSub over_inr_monic)))
    exact inl_union_inr_entire

end overDisjoint

/-! ## Slice-choice transport (one verified rung of the Diaconescu argument)

  A *base* choice object lifts to a *slice* choice object: if `Y.dom` is choice in `𝒞`,
  then `Y` is choice in `Over B`.  The point is that a base map realized inside a slice
  relation is automatically a slice arrow, because the relation's legs already commute with
  the structure maps. -/

section sliceChoice
variable [RegularCategory 𝒞] {B : 𝒞}

/-- **Slice-choice from base-choice.**  If `Y.dom` is `Choice` in `𝒞`, then `Y` is `Choice`
    in `Over B`.  An entire slice relation `R : X → Y` forgets to an entire base relation
    `R.forgetSlice : X.dom → Y.dom` (entirety is "left leg is a cover", and `Σ_B` preserves
    covers, `cover_f_of_cover`); base choice extracts a map `f : X.dom → Y.dom` with a section
    `h`.  Both `f` and `h` are *automatically* slice arrows: `f ≫ Y.hom = h ≫ R.colB.f ≫ Y.hom
    = h ≫ R.src.hom = h ≫ R.colA.f ≫ X.hom = X.hom`, using that `R`'s legs are slice arrows. -/
theorem slice_choice_of_dom_choice (Y : Over B) (hY : Choice Y.dom) : Choice Y := by
  intro X R hent
  have hcov : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  have hcovf : Cover R.colA.f := cover_f_of_cover R.colA hcov
  have hentf : Entire R.forgetSlice := by
    rw [show R.forgetSlice
          = BinRel.mk R.src.dom R.colA.f R.colB.f R.forgetSlice.isMonicPair from rfl]
    exact (tabulated_is_entire_iff_left_cover _ _ _).mpr hcovf
  obtain ⟨f, h, hA, hB⟩ := hY R.forgetSlice hentf
  simp only [BinRel.forgetSlice_colA, BinRel.forgetSlice_colB] at hA hB
  have hsecw : h ≫ R.src.hom = X.hom := by
    have e2 : h ≫ (R.colA.f ≫ X.hom) = h ≫ R.src.hom := by rw [R.colA.w]
    rw [← Cat.assoc, hA, Cat.id_comp] at e2; rw [← e2]
  have hfw : f ≫ Y.hom = X.hom := by
    have e1 : h ≫ (R.colB.f ≫ Y.hom) = f ≫ Y.hom := by rw [← Cat.assoc, hB]
    rw [R.colB.w, hsecw] at e1; rw [← e1]
  exact ⟨⟨f, hfw⟩, ⟨h, hsecw⟩, OverHom.ext hA, OverHom.ext hB⟩

end sliceChoice

/-! ## Residual: completing the slice pre-topos tower (toward §1.662 Diaconescu)

  Rungs 1, 2, 3, 4 are now DONE Sorry-free above:

  1. ✅ **Forget commutes with the calculus** (`BinRel.forgetSlice`, `forgetSlice_graph`,
     `forgetSlice_reciprocal` on the nose; `forgetSlice_compose_le` + `le_forgetSlice_compose`
     for `⊚` up to the comparison iso; `forgetSlice_mono_relLe` / `forgetSlice_reflects_relLe`
     for faithfulness).
  2. ✅ **`EffectiveRegular (Over B)`** (`overEffectiveRegular`, via `sliceIsEffective`).
  3. ✅ **`DisjointBinaryCoproduct (Over B)`** (`overDisjointBinaryCoproduct`).  Built by
     domain-transport along the faithful `Σ_B`: the order-iso `Sub (Over B) Y ≃ Sub 𝒞 Y.dom`
     (`Subobject.forgetSlice`/`liftSlice`, mutually monotone with `forgetSlice ∘ liftSlice = id`)
     transports the WHOLE `PreLogos (Over B)` lattice — `overHasSubobjectUnions`,
     `overPreLogos` (`bottom`/`bottom_min`/`bottom_dom_iso`/`invImage_preserves_union`/
     `invImage_preserves_bottom`) — from `𝒞`'s lattice on `Y.dom`.  The one new construction is
     `overHasBinaryCoproducts` (`X + Y = X.dom + Y.dom` with structure map `case X.hom Y.hom`);
     `overPositivePreLogos` and the four §1.621 disjointness fields then transport from `𝒞`'s
     `DisjointBinaryCoproduct` through the subobject identification.
  4. ✅ **`HasReflTransClosure (Over B)`** (`overHasReflTransClosure`, via `sliceTransRefClos`).

  REMAINING (final residual) — SHARPENED, with the precise wall located:

  5. **Diaconescu transport (final).**  `preTopos_boolean_iff_all_decidable.mpr` reduces the
     `S1_64` goal to `∀ A, DecidableObject A`.  Decidability of `A` is the diagonal
     `Δ : A ↣ A×A` complemented; the slice `𝒮(A×A)` is now a pre-topos (rungs 2–4) and `Δ` is
     a subterminal there.  Running Freyd's `U ⊆ 1` argument inside `𝒮(A×A)` (form `P = 1_𝒮 +_Δ
     1_𝒮`, a quotient of `1_𝒮 + 1_𝒮`; choice splits the quotient so `P ⊆ 1_𝒮 + 1_𝒮`;
     `1_𝒮 + 1_𝒮` decidable ⟹ `P` decidable ⟹ `Δ` complemented) needs **slice choice of the
     codiagonal `1_𝒮 + 1_𝒮`**.

     WALL ANALYSIS (refined; a tempting "pinning" shortcut was investigated and REJECTED — record
     so it is not re-attempted).  `slice_choice_of_dom_choice` reduces slice choice of `1_𝒮+1_𝒮` to
     base `Choice ((A×A)+(A×A))`.  That object distributes: `(A×A)+(A×A) ≅ (1+1)×(A×A)`
     (`coprodProdDistrib one one (A×A)`), under which `∇` becomes `pr₂`.  It is TEMPTING to think a
     slice map `X → 1_𝒮+1_𝒮` is "just" a base decision `d : X.dom → 1+1` with the `pr₂`-coordinate
     FORCED to `X.hom`, so that base `Choice (1+1)` alone (extract `d`, pin the `C`-coordinate to
     `X.hom`) would suffice — replacing the `prod_choice_is_choice` second extraction `Choice (C)` by
     a pin.  **This FAILS at witness-recovery.**  `Choice (T)` produces a *section into the relation's
     source* `h : X.dom → R.src` only when applied to a relation TARGETED at `T`.  `R.forgetSlice`
     targets `C+C`, not `1+1`; to retarget it to `1+1` one composes with `δ := case (term C ≫ inl)
     (term C ≫ inr) : C+C → 1+1`, but `δ` is not monic, so `R.forgetSlice ⊚ graph δ` has source
     `image(…)` — a QUOTIENT of `R.forgetSlice.src`.  `Choice (1+1)` then yields a section into that
     image, from which NO map back into `R.forgetSlice.src` exists (the image collapses the witness).
     Pinning the `C`-coordinate removes exactly the `Choice (C)` that, in `prod_choice_is_choice`,
     SUPPLIED the section `w`.  Hence base `Choice (1+1)` genuinely cannot section a relation targeted
     at `C+C`: slice-choice of `1_𝒮+1_𝒮` really does need `Choice ((A×A)+(A×A))`, NOT available.
     (Scaffolding `entire_comp_graph`/`entire_refine`/`comp_recip_pin` were un-privatised in S1_64
     during this investigation; they remain useful general-purpose relational lemmas.)

     CONSEQUENCE.  Freyd's pushout argument must NOT be run inside the slice (it would need this
     unavailable slice-choice).  His "(2a) inherited by slices ⟹ suffices `Sub(1)` boolean" is a
     pure LATTICE transport: the pushout/choice step is done ONCE in the BASE (`Sub(1)` boolean from
     `Choice (1+1)`), and the slice versions of `Sub(1)` boolean come from (2a) transported along the
     choice-free `forgetSlice`/`liftSlice` lattice iso.  The genuinely open residual is therefore the
     lattice implication **(2a)-in-slice ⟹ `Sub_𝒮(1_𝒮)` boolean** WITHOUT re-deriving the pushout —
     i.e. transporting "`Sub(1)` complemented" from base to every slice using only (2a) and the
     subobject lattice iso.  Note (2a) ALONE does not complement a subobject (taking the cover
     `(U, ⊤)` only yields `U' ⊊ U`); the transport must additionally use that the base `Sub(1)` is
     already boolean.  Pinning down this lattice transport is the true remaining mathematical step of
     `one_one_choice_to_boolean`; the slice-choice and base-change routes are both blind alleys. -/

end Freyd
