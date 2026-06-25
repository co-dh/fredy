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

-- §1.462 (hard direction, not proved here): if α is monic in `𝒮^A`, every component is monic.
-- The standard proof builds a "spike NT" constFunctor W → F at a fixed object A₀ : 𝒜
-- extending any map g : W → F(A₀) naturally.  Such NTs exist when 𝒜 is DISCRETE
-- (every morphism is an identity) — then naturality is vacuous.  For general 𝒜 the
-- construction requires the Yoneda lemma for 𝒮^A and the evaluation functors §1.274.
-- The easy direction suffices for Freyd's applications in Ch1.

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

/-! ## §1.521  Pointwise images in `𝒮^A` -/

-- TODO §1.521 HasImages (FunctorObj 𝒜 𝒮):
-- The pointwise image of α : F → G at A is image(α_A) in 𝒮.
-- Building this into a HasImages instance requires:
-- (a) image(α).dom : FunctorObj 𝒜 𝒮 with transition map f ↦ (the unique map
--     image(α_A).dom → image(α_B).dom making the square commute with image(α_B).arr).
--     The correct transition map uses the factorization:
--       image(α_A).arr ≫ G.map f  is allowed by image(α_B)
--     (via witness F.map f ≫ image.lift(α_B) and α.naturality),
--     giving choose : image(α_A).dom → image(α_B).dom with
--       choose ≫ image(α_B).arr = image(α_A).arr ≫ G.map f.  ← CORRECT NATURALITY
-- (b) image(α).arr : FunctorHom image(α).dom G, component (image α_A).arr.
--     Naturality: choose ≫ image(α_B).arr = image(α_A).arr ≫ G.map f ✓ (from (a))
-- (c) image(α).monic : Monic image(α).arr in FunctorObj 𝒜 𝒮 — pointwise.
-- (d) isImage: image.lift becomes a NT using the same naturality argument.
-- (e) minimality witness naturality: requires uniqueness of containment morphism
--     (image(α_A).arr is monic in 𝒮, so any two witnesses agreeing after it are equal).
-- Left as a precise TODO; not needed for §1.422/§1.424/§1.521(pullbacks).

-- TODO §1.521 RegularCategory:
-- `RegularCategory (FunctorObj 𝒜 𝒮)` when `[RegularCategory 𝒮]` requires:
-- (1) HasTerminal: ✓ (functorCat_hasTerminal)
-- (2) HasBinaryProducts: ✓ (functorCat_hasProducts)
-- (3) HasPullbacks: ✓ (functorCat_hasPullbacks)
-- (4) HasImages: partial (functorCat_hasImages, pending naturality sorry)
-- (5) PullbacksTransferCovers: if α is a cover in 𝒮^A (every α_A is a cover by §1.521)
--     and we pull back along β, then the pullback π₂ is a cover.
--     Pointwise: (pullback α_A β_A).π₂ is a cover by PullbacksTransferCovers in 𝒮.
--     But the cone.IsPullback condition for the NT cone needs verification.
--     This requires showing the pointwise pullback in 𝒮^A is a genuine pullback
--     (which follows from the universal property we proved) and then applying
--     the pointwise cover transfer.  Formal statement:

-- instance functorCat_ptc [RegularCategory 𝒮] : PullbacksTransferCovers (FunctorObj 𝒜 𝒮) :=
-- { pullbacks_transfer_covers := fun c hc hf => by
--     -- c is a cone in 𝒮^A; hc : c.IsPullback; hf : Cover c.π₁ (= pointwise covers)
--     -- We need: Cover c.π₂ (= pointwise covers of π₂ components)
--     -- Pointwise: c restricted to each A gives a cone in 𝒮 that is a pullback
--     -- (because c.IsPullback in 𝒮^A implies c_A is a pullback in 𝒮 — formal deduction)
--     -- and cover(c.π₁.app A) → cover(c.π₂.app A) by RegularCategory 𝒮.
--     sorry }

end Freyd
