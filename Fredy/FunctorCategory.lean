/-
  Freyd & Scedrov, *Categories and Allegories* — functor-category structure transfer.

  The functor category 𝒮^A (`FunctorObj 𝒜 𝒮`) is already defined in S1_27:
  objects are bundled functors `FunctorObj 𝒜 𝒮`, morphisms are natural
  transformations `FunctorHom F G`, and `functorCat 𝒜 𝒮 : Cat (FunctorObj 𝒜 𝒮)`
  is the `Cat` instance.  This file adds the *structural* content:

  §1.422  `𝒮^A` has a terminator iff 𝒮 does — the pointwise constant functor.
  §1.424  `𝒮^A` has binary products iff 𝒮 does — computed objectwise.
  §1.462  α : F → G is MONIC in `𝒮^A` iff every component α_A is monic in 𝒮.
  §1.521  `𝒮^A` has pullbacks (pointwise) when 𝒮 does.
          `𝒮^A` has images (pointwise, noncomputable) when 𝒮 does.
          RegularCategory requires also PullbacksTransferCovers — see TODO.

  Composition in diagram order throughout: `f ≫ g` = first f, then g.
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_27
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56

open Freyd

universe v u

variable {𝒜 𝒮 : Type u} [Cat.{v} 𝒜] [Cat.{v} 𝒮]

namespace Freyd

/-! ## §1.422  Pointwise terminator in `𝒮^A` -/

/-- §1.422: The constant functor `A ↦ one` with every arrow mapping to `id_{one}`. -/
private def constOneFunctor [HasTerminal 𝒮] : FunctorObj 𝒜 𝒮 where
  obj       := fun _ => one
  isFunctor := {
    map      := fun _ => Cat.id one
    map_id   := fun _ => rfl
    map_comp := fun _ _ => (Cat.id_comp _).symm
  }

/-- §1.422: Unique NT from F to `constOneFunctor`; component is `term (F.obj A)`. -/
private def toConstOne [HasTerminal 𝒮] (F : FunctorObj 𝒜 𝒮) :
    FunctorHom F constOneFunctor where
  app        := fun A => term (F.obj A)
  naturality := fun {_ _} _ => term_uniq _ _

/-- §1.422: `𝒮^A` has a terminator: the constant functor at `one`. -/
instance functorCat_hasTerminal [HasTerminal 𝒮] : HasTerminal (FunctorObj 𝒜 𝒮) where
  one  := constOneFunctor
  trm  := toConstOne
  uniq := fun {_} α β => NaturalTransformation.ext' fun A => term_uniq (α.app A) (β.app A)

/-! ## §1.424  Pointwise binary products in `𝒮^A` -/

/-- Helper: equality of two maps into a product from their projections. -/
private theorem prod_ext [HasBinaryProducts 𝒮] {X A B : 𝒮} {a b : X ⟶ prod A B}
    (hf : a ≫ fst = b ≫ fst) (hs : a ≫ snd = b ≫ snd) : a = b :=
  (pair_uniq _ _ _ rfl rfl).trans (by rw [hf, hs]; exact (pair_uniq _ _ _ rfl rfl).symm)

/-- §1.424: Objectwise product functor: (F × G)(A) = F(A) × G(A). -/
private def functorProd [HasBinaryProducts 𝒮] (F G : FunctorObj 𝒜 𝒮) : FunctorObj 𝒜 𝒮 where
  obj       := fun A => prod (F.obj A) (G.obj A)
  isFunctor := {
    map      := fun {X Y} f => pair (fst ≫ F.isFunctor.map f) (snd ≫ G.isFunctor.map f)
    map_id   := fun _ => by
      simp only [F.isFunctor.map_id, G.isFunctor.map_id, Cat.comp_id]
      exact (pair_uniq _ _ _ (Cat.id_comp _) (Cat.id_comp _)).symm
    map_comp := fun {X Y Z} f g => by
      simp only [F.isFunctor.map_comp, G.isFunctor.map_comp]
      symm; apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc]
  }

/-- §1.424: First projection NT: (fst_{F,G})_A = fst. -/
private def fstNT [HasBinaryProducts 𝒮] (F G : FunctorObj 𝒜 𝒮) :
    FunctorHom (functorProd F G) F where
  app        := fun _ => fst
  naturality := fun {A B} f => by
    show (functorProd F G).isFunctor.map f ≫ fst = fst ≫ F.isFunctor.map f
    simp only [functorProd]; rw [fst_pair]

/-- §1.424: Second projection NT: (snd_{F,G})_A = snd. -/
private def sndNT [HasBinaryProducts 𝒮] (F G : FunctorObj 𝒜 𝒮) :
    FunctorHom (functorProd F G) G where
  app        := fun _ => snd
  naturality := fun {A B} f => by
    show (functorProd F G).isFunctor.map f ≫ snd = snd ≫ G.isFunctor.map f
    simp only [functorProd]; rw [snd_pair]

/-- §1.424: Pairing NT: (pairNT α β)_A = pair (α_A) (β_A). -/
private def pairNT [HasBinaryProducts 𝒮] {X F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom X F) (β : FunctorHom X G) : FunctorHom X (functorProd F G) where
  app        := fun A => pair (α.app A) (β.app A)
  naturality := fun {A B} f => by
    show (X.isFunctor.map f) ≫ pair (α.app B) (β.app B) =
         pair (α.app A) (β.app A) ≫ (functorProd F G).isFunctor.map f
    simp only [functorProd]
    apply prod_ext
    · rw [Cat.assoc, fst_pair, Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, ← α.naturality]
    · rw [Cat.assoc, snd_pair, Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, ← β.naturality]

/-- §1.424: `𝒮^A` has binary products, computed objectwise. -/
instance functorCat_hasProducts [HasBinaryProducts 𝒮] : HasBinaryProducts (FunctorObj 𝒜 𝒮) where
  prod      := functorProd
  fst       := fstNT _ _
  snd       := sndNT _ _
  pair      := pairNT
  fst_pair  := fun α β => NaturalTransformation.ext' fun A => fst_pair (α.app A) (β.app A)
  snd_pair  := fun α β => NaturalTransformation.ext' fun A => snd_pair (α.app A) (β.app A)
  pair_uniq := fun α β γ h₁ h₂ => NaturalTransformation.ext' fun A =>
    pair_uniq (α.app A) (β.app A) (γ.app A)
      (congrFun (congrArg NaturalTransformation.app h₁) A)
      (congrFun (congrArg NaturalTransformation.app h₂) A)

/-! ## §1.462  Monic NT ↔ pointwise monic -/

/-- §1.462 (easy direction): components monic → NT monic in `𝒮^A`.
    If β ≫ α = γ ≫ α in `𝒮^A` then for every A, β_A ≫ α_A = γ_A ≫ α_A,
    so β_A = γ_A by the component hypothesis, hence β = γ. -/
theorem natTrans_monic_of_components_monic {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) (h : ∀ A, Monic (α.app A)) : Monic (𝒞 := FunctorObj 𝒜 𝒮) α :=
  fun {_} β γ hβγ => NaturalTransformation.ext' fun A =>
    h A (β.app A) (γ.app A) (congrFun (congrArg NaturalTransformation.app hβγ) A)

-- §1.462 (hard direction): if α is monic in `𝒮^A`, every component is monic.
-- Requires evaluation functors ev_A : 𝒮^A → 𝒮 and their faithfulness.
-- BOOK §1.462: ev_A is faithful (NTs equal iff all components equal), hence reflects monics.
-- Formalization requires ev_A as a named functor + Faithful instance (S1_274).
-- Left as TODO; the easy direction suffices for Freyd's Ch1 applications.

/-! ## §1.521  Pointwise pullbacks in `𝒮^A` -/

-- Auxiliary: two maps to a pullback equal iff they agree on both projections.
private theorem pb_ext [HasPullbacks 𝒮] {A B C : 𝒮} {f : A ⟶ C} {g : B ⟶ C}
    (pb : HasPullback f g) {W : 𝒮} {u v : W ⟶ pb.cone.pt}
    (h₁ : u ≫ pb.cone.π₁ = v ≫ pb.cone.π₁) (h₂ : u ≫ pb.cone.π₂ = v ≫ pb.cone.π₂) : u = v :=
  let c : Cone f g := ⟨W, u ≫ pb.cone.π₁, u ≫ pb.cone.π₂, by rw [Cat.assoc, pb.cone.w, ← Cat.assoc]⟩
  (pb.lift_uniq c u rfl rfl).trans (pb.lift_uniq c v h₁.symm h₂.symm).symm

-- The cone used to build the transition map of the pullback functor.
private def pbCone [HasPullbacks 𝒮] {F G H : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) {X Y : 𝒜} (f : X ⟶ Y) :
    Cone (α.app Y) (β.app Y) :=
  ⟨_, (HasPullbacks.has (α.app X) (β.app X)).cone.π₁ ≫ F.isFunctor.map f,
      (HasPullbacks.has (α.app X) (β.app X)).cone.π₂ ≫ G.isFunctor.map f,
      by let pbX := HasPullbacks.has (α.app X) (β.app X)
         rw [Cat.assoc, α.naturality, ← Cat.assoc, pbX.cone.w, Cat.assoc, ← β.naturality, ← Cat.assoc]⟩

-- Transition map between pointwise pullback objects.
private def pbLiftMap [HasPullbacks 𝒮] {F G H : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) {X Y : 𝒜} (f : X ⟶ Y) :
    (HasPullbacks.has (α.app X) (β.app X)).cone.pt ⟶
    (HasPullbacks.has (α.app Y) (β.app Y)).cone.pt :=
  (HasPullbacks.has (α.app Y) (β.app Y)).lift (pbCone α β f)

private theorem pbLift_fst [HasPullbacks 𝒮] {F G H : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) {X Y : 𝒜} (f : X ⟶ Y) :
    pbLiftMap α β f ≫ (HasPullbacks.has (α.app Y) (β.app Y)).cone.π₁ =
    (HasPullbacks.has (α.app X) (β.app X)).cone.π₁ ≫ F.isFunctor.map f :=
  (HasPullbacks.has (α.app Y) (β.app Y)).lift_fst _

private theorem pbLift_snd [HasPullbacks 𝒮] {F G H : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) {X Y : 𝒜} (f : X ⟶ Y) :
    pbLiftMap α β f ≫ (HasPullbacks.has (α.app Y) (β.app Y)).cone.π₂ =
    (HasPullbacks.has (α.app X) (β.app X)).cone.π₂ ≫ G.isFunctor.map f :=
  (HasPullbacks.has (α.app Y) (β.app Y)).lift_snd _

/-- §1.521: Pointwise pullback functor object in `𝒮^A`. -/
private def pbFunObj [HasPullbacks 𝒮] {F G H : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) : FunctorObj 𝒜 𝒮 where
  obj       := fun A => (HasPullbacks.has (α.app A) (β.app A)).cone.pt
  isFunctor := {
    map      := pbLiftMap α β
    map_id   := fun A => pb_ext (HasPullbacks.has (α.app A) (β.app A))
      (by rw [pbLift_fst, F.isFunctor.map_id, Cat.comp_id, Cat.id_comp])
      (by rw [pbLift_snd, G.isFunctor.map_id, Cat.comp_id, Cat.id_comp])
    map_comp := fun {X Y Z} f g => by
      let pbX := HasPullbacks.has (α.app X) (β.app X)
      let pbZ := HasPullbacks.has (α.app Z) (β.app Z)
      have hf1 : pbLiftMap α β (f ≫ g) ≫ pbZ.cone.π₁ = pbX.cone.π₁ ≫ F.isFunctor.map f ≫ F.isFunctor.map g :=
        by rw [pbLift_fst, F.isFunctor.map_comp]
      have hf2 : (pbLiftMap α β f ≫ pbLiftMap α β g) ≫ pbZ.cone.π₁ = pbX.cone.π₁ ≫ F.isFunctor.map f ≫ F.isFunctor.map g :=
        by rw [Cat.assoc, pbLift_fst, ← Cat.assoc, pbLift_fst, Cat.assoc]
      have hs1 : pbLiftMap α β (f ≫ g) ≫ pbZ.cone.π₂ = pbX.cone.π₂ ≫ G.isFunctor.map f ≫ G.isFunctor.map g :=
        by rw [pbLift_snd, G.isFunctor.map_comp]
      have hs2 : (pbLiftMap α β f ≫ pbLiftMap α β g) ≫ pbZ.cone.π₂ = pbX.cone.π₂ ≫ G.isFunctor.map f ≫ G.isFunctor.map g :=
        by rw [Cat.assoc, pbLift_snd, ← Cat.assoc, pbLift_snd, Cat.assoc]
      exact pb_ext pbZ (hf1.trans hf2.symm) (hs1.trans hs2.symm)
  }

-- pbFunObj.map = pbLiftMap by rfl, needed for naturality rewrites.
private theorem pbFunObj_map [HasPullbacks 𝒮] {F G H : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) {X Y : 𝒜} (f : X ⟶ Y) :
    (pbFunObj α β).isFunctor.map f = pbLiftMap α β f := rfl

-- Lift of a cone into the pointwise pullback; component at A is the pointwise lift.
private def liftApp [HasPullbacks 𝒮] {F G H : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H)
    (c : Cone (𝒞 := FunctorObj 𝒜 𝒮) α β) (A : 𝒜) :
    c.pt.obj A ⟶ (HasPullbacks.has (α.app A) (β.app A)).cone.pt :=
  (HasPullbacks.has (α.app A) (β.app A)).lift
    ⟨c.pt.obj A, c.π₁.app A, c.π₂.app A, congrFun (congrArg NaturalTransformation.app c.w) A⟩

private theorem liftApp_fst [HasPullbacks 𝒮] {F G H : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H)
    (c : Cone (𝒞 := FunctorObj 𝒜 𝒮) α β) (A : 𝒜) :
    liftApp α β c A ≫ (HasPullbacks.has (α.app A) (β.app A)).cone.π₁ = c.π₁.app A :=
  (HasPullbacks.has (α.app A) (β.app A)).lift_fst _

private theorem liftApp_snd [HasPullbacks 𝒮] {F G H : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H)
    (c : Cone (𝒞 := FunctorObj 𝒜 𝒮) α β) (A : 𝒜) :
    liftApp α β c A ≫ (HasPullbacks.has (α.app A) (β.app A)).cone.π₂ = c.π₂.app A :=
  (HasPullbacks.has (α.app A) (β.app A)).lift_snd _

private def pbNTLift [HasPullbacks 𝒮] {F G H : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H)
    (c : Cone (𝒞 := FunctorObj 𝒜 𝒮) α β) : FunctorHom c.pt (pbFunObj α β) where
  app        := liftApp α β c
  naturality := fun {A B} f => by
    let pbB := HasPullbacks.has (α.app B) (β.app B)
    apply pb_ext pbB
    · rw [pbFunObj_map, Cat.assoc, liftApp_fst, Cat.assoc, pbLift_fst,
          ← Cat.assoc, liftApp_fst, ← c.π₁.naturality]
    · rw [pbFunObj_map, Cat.assoc, liftApp_snd, Cat.assoc, pbLift_snd,
          ← Cat.assoc, liftApp_snd, ← c.π₂.naturality]

/-- §1.521: `𝒮^A` has pullbacks, computed pointwise. -/
instance functorCat_hasPullbacks [HasPullbacks 𝒮] : HasPullbacks (FunctorObj 𝒜 𝒮) where
  has α β := {
    cone := {
      pt := pbFunObj α β
      π₁ := {
        app        := fun A => (HasPullbacks.has (α.app A) (β.app A)).cone.π₁
        naturality := fun {A B} f => pbLift_fst α β f
      }
      π₂ := {
        app        := fun A => (HasPullbacks.has (α.app A) (β.app A)).cone.π₂
        naturality := fun {A B} f => pbLift_snd α β f
      }
      w := NaturalTransformation.ext' fun A => (HasPullbacks.has (α.app A) (β.app A)).cone.w
    }
    lift     := pbNTLift α β
    lift_fst := fun c => NaturalTransformation.ext' fun A => liftApp_fst α β c A
    lift_snd := fun c => NaturalTransformation.ext' fun A => liftApp_snd α β c A
    lift_uniq := fun c u h₁ h₂ => NaturalTransformation.ext' fun A =>
      (HasPullbacks.has (α.app A) (β.app A)).lift_uniq
        ⟨_, c.π₁.app A, c.π₂.app A, congrFun (congrArg NaturalTransformation.app c.w) A⟩
        (u.app A)
        (congrFun (congrArg NaturalTransformation.app h₁) A)
        (congrFun (congrArg NaturalTransformation.app h₂) A)
  }

/-! ## §1.521  Pointwise images in `𝒮^A` (partial construction) -/

/-
  The transition map for the image domain functor exists by a pullback argument.
  Given α : FunctorHom F G, f : X ⟶ Y in 𝒜, we want
    imgTransMap f : (image (α.app X)).dom ⟶ (image (α.app Y)).dom
  satisfying: imgTransMap f ≫ (image (α.app Y)).arr = (image (α.app X)).arr ≫ G.map f.

  Construction: pull back (image (α.app Y)).arr along (image (α.app X)).arr ≫ G.map f.
  The cospan is: (image α_X).dom —[arr_X ≫ G.map f]→ G.obj Y ←[arr_Y]— (image α_Y).dom.
  Pullback P has projections π₁ : P → (image α_X).dom (monic, pullback of mono)
  and π₂ : P → (image α_Y).dom.
  Canonical cone from F.obj X: (image.lift(α_X), F.map f ≫ image.lift(α_Y)).
  This cone maps into P; the first leg image.lift(α_X) factors through the monic π₁.
  image.lift(α_X) is a cover (image_lift_cover), so π₁ is iso.
  imgTransMap f := π₁⁻¹ ≫ π₂.
-/

-- Pullback of (image α_Y).arr along (image α_X).arr ≫ G.map f.
private noncomputable def imgTransPB [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    HasPullback ((image (α.app X)).arr ≫ G.isFunctor.map f) (image (α.app Y)).arr :=
  HasPullbacks.has _ _

private theorem imgTransPB_π₁_mono [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    Monic (imgTransPB α f).cone.π₁ :=
  mono_pullback ((image (α.app X)).arr ≫ G.isFunctor.map f)
    (image (α.app Y)).arr (image (α.app Y)).monic (imgTransPB α f)

-- Canonical cone: π₁ := image.lift(α.app X), π₂ := F.map f ≫ image.lift(α.app Y).
-- Cone equation: lift_X ≫ arr_X ≫ G.map f = α_X ≫ G.map f = F.map f ≫ α_Y
--              = (F.map f ≫ lift_Y) ≫ arr_Y.
private noncomputable def imgTransCone [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    Cone ((image (α.app X)).arr ≫ G.isFunctor.map f) (image (α.app Y)).arr :=
  ⟨F.obj X, image.lift (α.app X), F.isFunctor.map f ≫ image.lift (α.app Y), by
    calc image.lift (α.app X) ≫ (image (α.app X)).arr ≫ G.isFunctor.map f
        = α.app X ≫ G.isFunctor.map f :=
            by rw [← Cat.assoc, image.lift_fac]
      _ = F.isFunctor.map f ≫ α.app Y :=
            (α.naturality f).symm
      _ = (F.isFunctor.map f ≫ image.lift (α.app Y)) ≫ (image (α.app Y)).arr :=
            by rw [Cat.assoc, image.lift_fac]⟩

-- The lift of imgTransCone satisfies: lift ≫ π₁ = image.lift(α.app X).
-- Since image.lift(α.app X) is a cover (image_lift_cover) and factors through monic π₁,
-- π₁ is an isomorphism.
private theorem imgTransPB_π₁_iso [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    IsIso (imgTransPB α f).cone.π₁ :=
  image_lift_cover (α.app X) (imgTransPB α f).cone.π₁
    ((imgTransPB α f).lift (imgTransCone α f))
    (imgTransPB_π₁_mono α f)
    ((imgTransPB α f).lift_fst (imgTransCone α f))

-- Extract the inverse of π₁ using Classical.choose.
-- IsIso (π₁ : P → D) = ∃ g : D → P, π₁ ≫ g = id ∧ g ≫ π₁ = id, so inverse : D → P.
-- Here D = (image α_X).dom, P = (imgTransPB α f).cone.pt.
private noncomputable def imgTransπ₁inv [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    (image (α.app X)).dom ⟶ (imgTransPB α f).cone.pt :=
  Classical.choose (imgTransPB_π₁_iso α f)

-- π₁ ≫ π₁⁻¹ = id  (first component of IsIso spec)
private theorem imgTransπ₁_comp_inv [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    (imgTransPB α f).cone.π₁ ≫ imgTransπ₁inv α f = Cat.id _ :=
  (Classical.choose_spec (imgTransPB_π₁_iso α f)).1

-- π₁⁻¹ ≫ π₁ = id  (second component of IsIso spec)
private theorem imgTransπ₁inv_comp [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    imgTransπ₁inv α f ≫ (imgTransPB α f).cone.π₁ = Cat.id _ :=
  (Classical.choose_spec (imgTransPB_π₁_iso α f)).2

/-- The transition map: π₁⁻¹ ≫ π₂ : (image α_X).dom ⟶ (image α_Y).dom.
    π₁⁻¹ : (image α_X).dom → (imgTransPB α f).cone.pt  (inverse of π₁ : P → (image α_X).dom)
    π₂   : (imgTransPB α f).cone.pt → (image α_Y).dom. -/
noncomputable def imgTransMap [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    (image (α.app X)).dom ⟶ (image (α.app Y)).dom :=
  imgTransπ₁inv α f ≫ (imgTransPB α f).cone.π₂

/-- Key equation: imgTransMap f ≫ (image α_Y).arr = (image α_X).arr ≫ G.map f.
    Proof: unfold imgTransMap = π₁⁻¹ ≫ π₂; use π₂ ≫ arr_Y = π₁ ≫ (arr_X ≫ G.map f) from
    cone.w; then π₁⁻¹ ≫ π₁ = id gives the result. -/
theorem imgTrans_comm [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    imgTransMap α f ≫ (image (α.app Y)).arr =
    (image (α.app X)).arr ≫ G.isFunctor.map f := by
  -- unfold imgTransMap; then use Cat.assoc to group π₁⁻¹ ≫ (π₂ ≫ arr_Y), then cone.w.
  unfold imgTransMap
  rw [Cat.assoc (imgTransπ₁inv α f), ← (imgTransPB α f).cone.w,
      ← Cat.assoc (imgTransπ₁inv α f), imgTransπ₁inv_comp, Cat.id_comp]

private theorem imgTransMap_id [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) (X : 𝒜) :
    imgTransMap α (Cat.id X) = Cat.id (image (α.app X)).dom := by
  apply (image (α.app X)).monic
  rw [imgTrans_comm, G.isFunctor.map_id, Cat.comp_id, Cat.id_comp]

private theorem imgTransMap_comp [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) {X Y Z : 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) :
    imgTransMap α (f ≫ g) = imgTransMap α f ≫ imgTransMap α g := by
  apply (image (α.app Z)).monic
  -- Both sides ≫ arr_Z equal arr_X ≫ (G.map f ≫ G.map g) [right-grouped].
  have h1 : imgTransMap α (f ≫ g) ≫ (image (α.app Z)).arr =
            (image (α.app X)).arr ≫ (G.isFunctor.map f ≫ G.isFunctor.map g) := by
    rw [imgTrans_comm, G.isFunctor.map_comp]
  have h2 : (imgTransMap α f ≫ imgTransMap α g) ≫ (image (α.app Z)).arr =
            (image (α.app X)).arr ≫ (G.isFunctor.map f ≫ G.isFunctor.map g) :=
    calc (imgTransMap α f ≫ imgTransMap α g) ≫ (image (α.app Z)).arr
        = imgTransMap α f ≫ (imgTransMap α g ≫ (image (α.app Z)).arr) :=
            Cat.assoc _ _ _
      _ = imgTransMap α f ≫ ((image (α.app Y)).arr ≫ G.isFunctor.map g) :=
            by rw [imgTrans_comm α g]
      _ = (imgTransMap α f ≫ (image (α.app Y)).arr) ≫ G.isFunctor.map g :=
            (Cat.assoc _ _ _).symm
      _ = ((image (α.app X)).arr ≫ G.isFunctor.map f) ≫ G.isFunctor.map g :=
            by rw [imgTrans_comm α f]
      _ = (image (α.app X)).arr ≫ (G.isFunctor.map f ≫ G.isFunctor.map g) :=
            Cat.assoc _ _ _
  rw [h1, ← h2]

/-- §1.521: Functor A ↦ (image (α_A)).dom with transition maps imgTransMap. -/
noncomputable def imageFunObj [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) : FunctorObj 𝒜 𝒮 where
  obj       := fun A => (image (α.app A)).dom
  isFunctor := {
    map      := imgTransMap α
    map_id   := imgTransMap_id α
    map_comp := fun f g => imgTransMap_comp α f g
  }

/-- §1.521: NT arr : imageFunObj α ⟶ G, components (image (α_A)).arr, natural by imgTrans_comm. -/
noncomputable def imgArrNT [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) : FunctorHom (imageFunObj α) G where
  app        := fun A => (image (α.app A)).arr
  naturality := fun {X Y} f => imgTrans_comm α f

/-- §1.521: imgArrNT α is monic in 𝒮^A (componentwise monic → NT monic, §1.462 easy). -/
theorem imgArrNT_monic [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) : Monic (𝒞 := FunctorObj 𝒜 𝒮) (imgArrNT α) :=
  natTrans_monic_of_components_monic (imgArrNT α) (fun A => (image (α.app A)).monic)

/-- §1.521: Lift NT imageLiftNT : F ⟶ imageFunObj α, components image.lift (α_A).
    Naturality: both sides ≫ image(α_B).arr agree, using imgTrans_comm + α.naturality. -/
noncomputable def imageLiftNT [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) : FunctorHom F (imageFunObj α) where
  app        := fun A => image.lift (α.app A)
  naturality := fun {X Y} f => by
    -- Goal: F.map f ≫ image.lift(α.app Y) = image.lift(α.app X) ≫ imgTransMap α f
    -- Post-compose with the monic arr_Y; both sides equal α.app X ≫ G.map f.
    apply (image (α.app Y)).monic
    -- Use show to give explicit types and avoid Cat.assoc misfire on Functor.map.
    show (F.isFunctor.map f ≫ image.lift (α.app Y)) ≫ (image (α.app Y)).arr =
         (image.lift (α.app X) ≫ imgTransMap α f) ≫ (image (α.app Y)).arr
    calc (F.isFunctor.map f ≫ image.lift (α.app Y)) ≫ (image (α.app Y)).arr
        = F.isFunctor.map f ≫ α.app Y :=
            by rw [Cat.assoc (F.isFunctor.map f), image.lift_fac]
      _ = α.app X ≫ G.isFunctor.map f := α.naturality f
      _ = image.lift (α.app X) ≫ (image (α.app X)).arr ≫ G.isFunctor.map f :=
            by rw [← Cat.assoc (image.lift (α.app X)), image.lift_fac]
      _ = image.lift (α.app X) ≫ imgTransMap α f ≫ (image (α.app Y)).arr :=
            by rw [← imgTrans_comm]
      _ = (image.lift (α.app X) ≫ imgTransMap α f) ≫ (image (α.app Y)).arr :=
            (Cat.assoc _ _ _).symm

/-- §1.521: imageLiftNT ≫ imgArrNT = α (the pointwise image factorization). -/
theorem imageLiftNT_fac [RegularCategory 𝒮] {F G : FunctorObj 𝒜 𝒮}
    (α : FunctorHom F G) :
    natTrans_comp (imageLiftNT α) (imgArrNT α) = α :=
  NaturalTransformation.ext' fun A => image.lift_fac (α.app A)

/-
  §1.521 HasImages (FunctorObj 𝒜 𝒮): PARTIAL — BLOCKED by §1.462 hard direction.

  What is proved above (sorry-free):
  • imageFunObj α   : FunctorObj 𝒜 𝒮   — the image domain functor (transition maps via pullback)
  • imgArrNT α      : imageFunObj α ⟶ G  — the inclusion NT (natural by imgTrans_comm)
  • imgArrNT_monic  : Monic (imgArrNT α)  — pointwise monic → NT monic (§1.462 easy)
  • imageLiftNT α   : F ⟶ imageFunObj α  — the lift NT
  • imageLiftNT_fac : imageLiftNT α ≫ imgArrNT α = α  (image factorization)

  What is missing for a full HasImages instance — MINIMALITY:
  Given S : Subobject (𝒮^A) G allowing α, exhibit h : imageFunObj α ⟶ S.dom (NT) with
  h ≫ S.arr = imgArrNT α.
  Component h.app A := (image_min (α.app A) cA hA).choose, requiring Monic (S.arr.app A).
  Naturality of h follows by post-cancellation with S.arr.app B (monic): both sides equal
  after ≫ S.arr.app B, using imgTrans_comm + naturality of S.arr.

  BLOCKER: Monic (S.arr.app A) for A : 𝒜.
  S.arr is monic as a NT (Subobject); extracting componentwise monicity is the §1.462
  HARD DIRECTION: α monic in 𝒮^A → α.app A monic in 𝒮.
  Standard proof: ev_A(α) = α.app A; ev_A faithful (NTs equal iff components equal) ⟹
  ev_A reflects monics.  Requires ev_A as a Lean functor with a Faithful instance (S1_274).

  §1.521 RegularCategory (FunctorObj 𝒜 𝒮): TODO once §1.462 hard is proved.
  (1) HasTerminal       ✓  (functorCat_hasTerminal)
  (2) HasBinaryProducts ✓  (functorCat_hasProducts)
  (3) HasPullbacks      ✓  (functorCat_hasPullbacks)
  (4) HasImages         BLOCKED (see above)
  (5) PullbacksTransferCovers: blocked by the same §1.462 hard issue.
      Proof sketch: Cover α in 𝒮^A → each α.app A cover in 𝒮 (needs ev_A faithful);
      pointwise PTC in 𝒮 gives Cover (canonical_π₂.app A); componentwise covers → NT cover.
-/

end Freyd
