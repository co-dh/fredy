/-
  Freyd & Scedrov, *Categories and Allegories* §1.82–§1.83

  §1.82     DIAGONAL FUNCTOR Δ : B → B^D (constant-diagram functor)
  §1.821    DiagCone / DiagCocone — compatible families of maps
  §1.822    HasLimit / HasColimit — universal cone / cocone
            limit_cone_unique — limits unique up to iso (PROVED)
  §1.823    Complete / Cocomplete
  §1.825    complete_iff_eq_prod — iff equalizers + products
            (⇐ hard direction PROVED; ⇒ easy direction sorry)
  §1.827    IsContinuous / IsCocontinuous
  §1.828    HasWeakLimit / WeaklyComplete
            complete_imp_weaklyComplete (PROVED)
  §1.829    preserves_weaklim_iff_preserves_lim (partial; uniqueness sorry)
  §1.82(10) HasPreLimit / PreComplete
            complete_imp_preComplete (PROVED)
  §1.83     PreAdjointObj / PreAdjointFunctor
            general_adjoint_functor_theorem (sorry)
  §1.831    IsUniformlyContinuous
            uniformly_continuous_preserves_prelimits (PROVED)
            more_general_adjoint_functor_theorem (sorry)
  §1.837    PreCocomplete
            complete_cocomplete_iff_precocomplete (sorry)
  §1.838    WellPowered / SubobjectIso
  §1.83(10) IsCoGeneratingSet
            special_adjoint_functor_theorem (sorry)
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_8
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43  -- canonical `HasEqualizers` (§1.428)
import Fredy.S1_51  -- canonical `Subobject` (§1.51)

universe v u u₁ u₂

namespace Freyd

-- ---------------------------------------------------------------------------
-- §1.82  Diagrams and cones
-- ---------------------------------------------------------------------------

/-! ### Diagrams (§1.821)

  A DIAGRAM of shape 𝒟 in ℬ is a functor D : 𝒟 → ℬ.
  A CONE with apex B is a natural transformation Δ(B) ⟹ D. -/

/-- A CONE of a diagram D : 𝒟 → ℬ with apex B: compatible family
    {π_i : B → D i} such that for x : i → j, π i ≫ D(x) = π j (§1.821). -/
structure DiagCone {𝒟 : Type u} [Cat.{v} 𝒟] {ℬ : Type u₁} [Cat.{v} ℬ]
    (D : 𝒟 → ℬ) [Functor D] where
  apex : ℬ
  π    : (i : 𝒟) → apex ⟶ D i
  nat  : ∀ {i j : 𝒟} (x : i ⟶ j), π i ≫ Functor.map x = π j

/-- A COCONE of D with nadir B: compatible family {ι_i : D i → B} (§1.821). -/
structure DiagCocone {𝒟 : Type u} [Cat.{v} 𝒟] {ℬ : Type u₁} [Cat.{v} ℬ]
    (D : 𝒟 → ℬ) [Functor D] where
  nadir : ℬ
  ι     : (i : 𝒟) → D i ⟶ nadir
  nat   : ∀ {i j : 𝒟} (x : i ⟶ j), Functor.map x ≫ ι j = ι i

-- ---------------------------------------------------------------------------
-- §1.822  Limit and Colimit
-- ---------------------------------------------------------------------------

/-- A LIMIT of D: a cone with a unique factorization for every other cone (§1.822). -/
structure HasLimit {𝒟 : Type u} [Cat.{v} 𝒟] {ℬ : Type u₁} [Cat.{v} ℬ]
    (D : 𝒟 → ℬ) [Functor D] where
  cone  : DiagCone D
  lift  : (c : DiagCone D) → c.apex ⟶ cone.apex
  fac   : ∀ (c : DiagCone D) (i : 𝒟), lift c ≫ cone.π i = c.π i
  uniq  : ∀ (c : DiagCone D) (u : c.apex ⟶ cone.apex),
            (∀ i, u ≫ cone.π i = c.π i) → u = lift c

/-- A COLIMIT of D: a cocone with a unique factorization for every other cocone (§1.822). -/
structure HasColimit {𝒟 : Type u} [Cat.{v} 𝒟] {ℬ : Type u₁} [Cat.{v} ℬ]
    (D : 𝒟 → ℬ) [Functor D] where
  cocone : DiagCocone D
  lift   : (c : DiagCocone D) → cocone.nadir ⟶ c.nadir
  fac    : ∀ (c : DiagCocone D) (i : 𝒟), cocone.ι i ≫ lift c = c.ι i
  uniq   : ∀ (c : DiagCocone D) (u : cocone.nadir ⟶ c.nadir),
             (∀ i, cocone.ι i ≫ u = c.ι i) → u = lift c

-- ---------------------------------------------------------------------------
-- §1.823  Complete and Cocomplete
-- ---------------------------------------------------------------------------

/-- ℬ is COMPLETE: every small diagram (shape in universe v) has a limit (§1.823). -/
class Complete (ℬ : Type u₁) [Cat.{v} ℬ] where
  hasLimit : {𝒟 : Type v} → [Cat.{v} 𝒟] → (D : 𝒟 → ℬ) → [Functor D] → HasLimit D

/-- ℬ is COCOMPLETE: every small diagram has a colimit (§1.823). -/
class Cocomplete (ℬ : Type u₁) [Cat.{v} ℬ] where
  hasColimit : {𝒟 : Type v} → [Cat.{v} 𝒟] → (D : 𝒟 → ℬ) → [Functor D] → HasColimit D

-- ---------------------------------------------------------------------------
-- §1.825  Complete iff equalizers + all products
-- ---------------------------------------------------------------------------

-- (HasEqualizers is defined canonically in S1_43 §1.428; reused here via import.)

/-- ℬ has all small products: for every I : Type v and F : I → ℬ a product exists (§1.825). -/
class HasProducts (ℬ : Type u₁) [Cat.{v} ℬ] where
  prodObj  : {I : Type v} → (I → ℬ) → ℬ
  proj     : {I : Type v} → {F : I → ℬ} → (i : I) → prodObj F ⟶ F i
  tupling  : {I : Type v} → {F : I → ℬ} → {X : ℬ} → ((i : I) → X ⟶ F i) → X ⟶ prodObj F
  tupling_fac  : ∀ {I : Type v} {F : I → ℬ} {X : ℬ} (legs : (i : I) → X ⟶ F i) (i : I),
                  tupling legs ≫ proj i = legs i
  tupling_uniq : ∀ {I : Type v} {F : I → ℬ} {X : ℬ} (legs : (i : I) → X ⟶ F i)
                   (u : X ⟶ prodObj F), (∀ i, u ≫ proj i = legs i) → u = tupling legs

-- ---------------------------------------------------------------------------
-- Helpers for §1.825 proof: discrete category
-- ---------------------------------------------------------------------------

/-- The DISCRETE CATEGORY on a type I: only identity morphisms (§1.821). -/
private instance discCat82 {I : Type v} : Cat.{v} I where
  Hom i j    := ULift.{v} (PLift (i = j))
  id _       := ⟨⟨rfl⟩⟩
  comp f g   := ⟨⟨f.down.down.trans g.down.down⟩⟩
  id_comp _  := rfl
  comp_id _  := rfl
  assoc _ _ _ := rfl

/-- Every function I → ℬ is a functor on the discrete category. -/
private instance discreteFunctor {I : Type v} {ℬ : Type u₁} [Cat.{v} ℬ] (F : I → ℬ) :
    @Functor I discCat82 ℬ _ F where
  map {i j} h   := h.down.down ▸ Cat.id (F i)
  map_id _      := rfl
  map_comp f g  := by
    obtain ⟨⟨hij⟩⟩ := f; obtain ⟨⟨hjk⟩⟩ := g
    subst hij; subst hjk; exact (Cat.id_comp _).symm

-- ---------------------------------------------------------------------------
-- §1.825 proof (both directions)
-- ---------------------------------------------------------------------------

/-- Helper: build a discrete-diagram cone from object legs. -/
private def discreteCone {I : Type v} {ℬ : Type u₁} [Cat.{v} ℬ] (F : I → ℬ)
    (B : ℬ) (legs : (i : I) → B ⟶ F i) :
    @DiagCone I discCat82 ℬ _ F (discreteFunctor F) where
  apex := B
  π := legs
  nat := by
    intro i j x; obtain ⟨⟨hij⟩⟩ := x; subst hij
    -- After subst, x was consumed; Functor.map ⟨⟨rfl⟩⟩ = id F i
    simp [Functor.map, Cat.comp_id]

/-- Easy (⇒): a complete category has all products (limits of discrete diagrams). -/
private def complete_hasProducts {ℬ : Type u₁} [Cat.{v} ℬ] (hc : Complete ℬ) :
    HasProducts ℬ where
  prodObj F := (@hc.hasLimit _ discCat82 F (discreteFunctor F)).cone.apex
  proj {I} {F} i := (@hc.hasLimit I discCat82 F (discreteFunctor F)).cone.π i
  tupling {I} {F} {X} legs :=
    (@hc.hasLimit I discCat82 F (discreteFunctor F)).lift (discreteCone F X legs)
  tupling_fac := fun {I} {F} {X} legs i =>
    (@hc.hasLimit I discCat82 F (discreteFunctor F)).fac (discreteCone F X legs) i
  tupling_uniq := fun {I} {F} {X} legs u hu =>
    (@hc.hasLimit I discCat82 F (discreteFunctor F)).uniq (discreteCone F X legs) u hu

/-- Walking-parallel-pair category: two objects with two parallel arrows 0→1. -/
private inductive WPP : Type where | src | tgt

/-- Morphisms of the walking parallel pair. -/
private inductive WPPHom : WPP → WPP → Type where
  | idS  : WPPHom .src .src
  | idT  : WPPHom .tgt .tgt
  | arr0 : WPPHom .src .tgt
  | arr1 : WPPHom .src .tgt

private def wppComp : {X Y Z : WPP} → WPPHom X Y → WPPHom Y Z → WPPHom X Z
  | _, _, _, .idS, g => g
  | _, _, _, f, .idT => f

private instance wppCat : Cat.{0} WPP where
  Hom := WPPHom
  id  := fun | .src => .idS | .tgt => .idT
  comp := wppComp
  id_comp := by intro X Y f; cases f <;> rfl
  comp_id := by intro X Y f; cases f <;> rfl
  assoc := by intro W X Y Z f g h; cases f <;> cases g <;> cases h <;> rfl

/-- Walking-parallel-pair shape lifted to universe `v` (so it is a legal `Complete`
    diagram shape).  Objects = `ULift WPP`, morphisms = `ULift` of the WPP homs. -/
private abbrev WPPv : Type v := ULift.{v} WPP

private instance wppCatV : Cat.{v} WPPv where
  Hom X Y    := ULift.{v} (WPPHom X.down Y.down)
  id X       := ⟨wppCat.id X.down⟩
  comp f g   := ⟨wppComp f.down g.down⟩
  id_comp := by rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩; cases f <;> rfl
  comp_id := by rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩; cases f <;> rfl
  assoc := by
    rintro ⟨W⟩ ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩ ⟨h⟩
    cases f <;> cases g <;> cases h <;> rfl

/-- The parallel-pair diagram `D : WPPv → ℬ` for a pair `f, g : A ⟶ B`:
    `src ↦ A`, `tgt ↦ B`, `arr0 ↦ f`, `arr1 ↦ g`. -/
private def wppDiagObj {ℬ : Type u₁} [Cat.{v} ℬ] {A B : ℬ} (_f _g : A ⟶ B) :
    WPPv → ℬ
  | ⟨.src⟩ => A
  | ⟨.tgt⟩ => B

private def wppDiagMap {ℬ : Type u₁} [Cat.{v} ℬ] {A B : ℬ} (f g : A ⟶ B) :
    {X Y : WPPv} → (X ⟶ Y) → (wppDiagObj f g X ⟶ wppDiagObj f g Y)
  | ⟨.src⟩, ⟨.src⟩, _ => Cat.id A
  | ⟨.tgt⟩, ⟨.tgt⟩, _ => Cat.id B
  | ⟨.src⟩, ⟨.tgt⟩, ⟨.arr0⟩ => f
  | ⟨.src⟩, ⟨.tgt⟩, ⟨.arr1⟩ => g

private instance wppDiagFunctor {ℬ : Type u₁} [Cat.{v} ℬ] {A B : ℬ} (f g : A ⟶ B) :
    Functor (wppDiagObj f g) where
  map := wppDiagMap f g
  map_id := by rintro ⟨X⟩; cases X <;> rfl
  map_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨p⟩ ⟨q⟩
    cases p <;> cases q <;>
      first
        | rfl
        | exact (Cat.id_comp _).symm
        | exact (Cat.comp_id _).symm

/-- Easy (⇒): a complete category has equalizers, obtained as the limit of the
    walking-parallel-pair diagram (§1.825).  Given `f, g : A ⟶ B`, the limit cone
    apex is the equalizer object, its leg at `src` is the equalizing map, and the
    lift / fac / uniqueness all come from the universal property of the limit. -/
private def complete_hasEqualizers {ℬ : Type u₁} [Cat.{v} ℬ] (hc : Complete ℬ) :
    HasEqualizers ℬ where
  eq A B f g :=
    let lim := @hc.hasLimit _ wppCatV (wppDiagObj f g) (wppDiagFunctor f g)
    -- the `src`-leg of the limit cone is the equalizing map
    let e : lim.cone.apex ⟶ A := lim.cone.π ⟨.src⟩
    -- `e ≫ f = e ≫ g`: both equal the `tgt`-leg by cone naturality on arr0 / arr1
    have hf : e ≫ f = lim.cone.π ⟨.tgt⟩ := lim.cone.nat (⟨.arr0⟩ : (⟨.src⟩ : WPPv) ⟶ ⟨.tgt⟩)
    have hg : e ≫ g = lim.cone.π ⟨.tgt⟩ := lim.cone.nat (⟨.arr1⟩ : (⟨.src⟩ : WPPv) ⟶ ⟨.tgt⟩)
    have he : e ≫ f = e ≫ g := hf.trans hg.symm
    -- a cone over the parallel pair from an equalizer cone `c`:
    -- src-leg `c.map`, tgt-leg `c.map ≫ f`
    let coneOf : EqualizerCone f g → DiagCone (wppDiagObj f g) := fun c =>
      { apex := c.dom
        π := fun X => match X with | ⟨.src⟩ => c.map | ⟨.tgt⟩ => c.map ≫ f
        nat := by
          rintro ⟨X⟩ ⟨Y⟩ ⟨x⟩
          cases x <;> (try exact Cat.comp_id _) <;> (try rfl) <;> exact c.eq.symm }
    { cone := { dom := lim.cone.apex, map := e, eq := he }
      lift := fun c => lim.lift (coneOf c)
      fac := fun c => lim.fac (coneOf c) ⟨.src⟩
      uniq := fun c m hm => by
        apply lim.uniq (coneOf c)
        rintro ⟨X⟩
        cases X
        · exact hm
        · show m ≫ lim.cone.π ⟨.tgt⟩ = c.map ≫ f
          rw [← hf, ← Cat.assoc, hm] }

/-- Hard (⇐): equalizers + products → complete.

    For diagram D : 𝒟 → ℬ, form P = Π D i, Q = Π_{x:i→j} D j,
    with maps f,g: P → Q (f's x-comp = proj i ≫ D(x); g's = proj j).
    Then lim D = eq(f,g) with projections eqMap ≫ proj i (§1.825). -/
private def eq_prod_complete {ℬ : Type u₁} [Cat.{v} ℬ]
    (heq : HasEqualizers ℬ) (hp : HasProducts ℬ) : Complete ℬ where
  hasLimit {𝒟} _ D hD :=
    -- Σ of arrows in 𝒟
    let Arr := Σ (i : 𝒟) (j : 𝒟), (i ⟶ j)
    let tgtOf : Arr → 𝒟 := fun a => a.snd.fst
    let srcOf : Arr → 𝒟 := fun a => a.fst
    let arrOf : (a : Arr) → srcOf a ⟶ tgtOf a := fun a => a.snd.snd
    let P   := hp.prodObj D
    let Q   := hp.prodObj (fun a => D (tgtOf a))
    -- mapF's a-component = proj(src a) ≫ D(arr a); mapG's = proj(tgt a)
    let mapF : P ⟶ Q := hp.tupling (fun a => hp.proj (srcOf a) ≫ hD.map (arrOf a))
    let mapG : P ⟶ Q := hp.tupling (fun a => hp.proj (tgtOf a))
    let e    := eqMap mapF mapG (𝒞 := ℬ)
    let πi : (i : 𝒟) → eqObj mapF mapG ⟶ D i := fun i => e ≫ hp.proj i
    -- Naturality: (e ≫ proj i) ≫ D(x) = e ≫ proj j
    have nat_pf : ∀ {i j : 𝒟} (x : i ⟶ j), πi i ≫ hD.map x = πi j := by
      intro i j x
      show (e ≫ hp.proj i) ≫ hD.map x = e ≫ hp.proj j
      rw [Cat.assoc]
      have heq_fg : e ≫ mapF = e ≫ mapG := eqMap_eq mapF mapG (𝒞 := ℬ)
      -- proj i ≫ D(x) = mapF ≫ proj⟨i,j,x⟩
      have step1 : hp.proj i ≫ hD.map x = mapF ≫ hp.proj ⟨i, j, x⟩ := by
        rw [hp.tupling_fac]
      -- mapG ≫ proj⟨i,j,x⟩ = proj j
      have step2 : mapG ≫ hp.proj ⟨i, j, x⟩ = hp.proj j := hp.tupling_fac _ _
      rw [step1, ← Cat.assoc, heq_fg, Cat.assoc, step2]
    -- Given cone c, tupling c.π equalizes mapF and mapG
    have tupling_eq : ∀ (c : DiagCone D), hp.tupling c.π ≫ mapF = hp.tupling c.π ≫ mapG := by
      intro c
      -- Both sides equal tupling of components; those agree by naturality
      have hF : hp.tupling c.π ≫ mapF = hp.tupling (fun a => c.π (srcOf a) ≫ hD.map (arrOf a)) := by
        apply hp.tupling_uniq; intro a
        rw [Cat.assoc, hp.tupling_fac, ← Cat.assoc, hp.tupling_fac]
      have hG : hp.tupling c.π ≫ mapG = hp.tupling (fun a => c.π (tgtOf a)) := by
        apply hp.tupling_uniq; intro a
        rw [Cat.assoc, hp.tupling_fac]; exact hp.tupling_fac _ _
      rw [hF, hG]; congr 1; funext ⟨i, j, x⟩; exact c.nat x
    { cone  := { apex := eqObj mapF mapG, π := πi, nat := nat_pf }
      lift  := fun c => eqLift mapF mapG (hp.tupling c.π) (tupling_eq c)
      fac   := fun c i => by
        show eqLift mapF mapG (hp.tupling c.π) (tupling_eq c) ≫ πi i = c.π i
        dsimp only [πi]
        rw [← Cat.assoc, eqLift_fac, hp.tupling_fac]
      uniq  := fun c u hu => by
        apply eqLift_uniq
        -- need: u ≫ e = hp.tupling c.π
        apply hp.tupling_uniq; intro i
        rw [Cat.assoc]; exact hu i }

/-- §1.825: A category is complete iff it has equalizers and all products. -/
theorem complete_iff_eq_prod (ℬ : Type u₁) [Cat.{v} ℬ] :
    Nonempty (Complete ℬ) ↔ (Nonempty (HasEqualizers ℬ) ∧ Nonempty (HasProducts ℬ)) := by
  constructor
  · intro ⟨hc⟩
    exact ⟨⟨complete_hasEqualizers hc⟩, ⟨complete_hasProducts hc⟩⟩
  · intro ⟨⟨heq⟩, ⟨hp⟩⟩
    exact ⟨eq_prod_complete heq hp⟩

-- ---------------------------------------------------------------------------
-- §1.827  Continuous and Cocontinuous functors
-- ---------------------------------------------------------------------------

/-! ### §1.827  Continuous / Cocontinuous

  A functor F : ℬ → 𝒞 is CONTINUOUS if it preserves all small limits;
  COCONTINUOUS if it preserves all small colimits. -/

/-- F : ℬ → 𝒞 is CONTINUOUS if it maps every small limit to a limit (§1.827):
    for every limit lim of D, the mapped family {F(π_i)} is a limit of F∘D. -/
def IsContinuous {ℬ : Type u₁} [Cat.{v} ℬ] {𝒞 : Type u₂} [Cat.{v} 𝒞]
    (F : ℬ → 𝒞) [hF : Functor F] : Prop :=
  ∀ {𝒟 : Type v} [Cat.{v} 𝒟] {D : 𝒟 → ℬ} [hD : Functor D] (lim : HasLimit D),
    -- apex is F lim.cone.apex; legs are hF.map (lim.cone.π i)
    -- every cone over F∘D factors uniquely through (F lim.cone.apex, hF.map∘π)
    ∀ (W : 𝒞) (legs : (i : 𝒟) → W ⟶ F (D i))
      (_ : ∀ {i j : 𝒟} (x : i ⟶ j), legs i ≫ hF.map (hD.map x) = legs j),
      ∃ u : W ⟶ F lim.cone.apex,
        (∀ i, u ≫ hF.map (lim.cone.π i) = legs i) ∧
        ∀ u' : W ⟶ F lim.cone.apex, (∀ i, u' ≫ hF.map (lim.cone.π i) = legs i) → u' = u

/-- F : ℬ → 𝒞 is COCONTINUOUS if it maps every small colimit to a colimit (§1.827). -/
def IsCocontinuous {ℬ : Type u₁} [Cat.{v} ℬ] {𝒞 : Type u₂} [Cat.{v} 𝒞]
    (F : ℬ → 𝒞) [hF : Functor F] : Prop :=
  ∀ {𝒟 : Type v} [Cat.{v} 𝒟] {D : 𝒟 → ℬ} [hD : Functor D] (colim : HasColimit D),
    ∀ (W : 𝒞) (legs : (i : 𝒟) → F (D i) ⟶ W)
      (_ : ∀ {i j : 𝒟} (x : i ⟶ j), hF.map (hD.map x) ≫ legs j = legs i),
      ∃ u : F colim.cocone.nadir ⟶ W,
        (∀ i, hF.map (colim.cocone.ι i) ≫ u = legs i) ∧
        ∀ u' : F colim.cocone.nadir ⟶ W,
          (∀ i, hF.map (colim.cocone.ι i) ≫ u' = legs i) → u' = u

-- ---------------------------------------------------------------------------
-- §1.828  Weak-limit and Weakly-complete
-- ---------------------------------------------------------------------------

/-! ### §1.828  Weak-limit

  A WEAK-LIMIT is a cone admitting (not necessarily unique) factorizations. -/

structure HasWeakLimit {𝒟 : Type u} [Cat.{v} 𝒟] {ℬ : Type u₁} [Cat.{v} ℬ]
    (D : 𝒟 → ℬ) [Functor D] where
  cone  : DiagCone D
  exist : (c : DiagCone D) → ∃ u : c.apex ⟶ cone.apex, ∀ i, u ≫ cone.π i = c.π i

/-- A category is WEAKLY-COMPLETE if every small diagram has a weak-limit (§1.828). -/
class WeaklyComplete (ℬ : Type u₁) [Cat.{v} ℬ] where
  hasWeakLimit : {𝒟 : Type v} → [Cat.{v} 𝒟] → (D : 𝒟 → ℬ) → [Functor D] → HasWeakLimit D

/-- Every complete category is weakly-complete. -/
instance complete_imp_weaklyComplete {ℬ : Type u₁} [Cat.{v} ℬ] [hc : Complete ℬ] :
    WeaklyComplete ℬ where
  hasWeakLimit := fun {_} _ D _ =>
    let hl := hc.hasLimit D
    { cone := hl.cone, exist := fun c => ⟨hl.lift c, hl.fac c⟩ }

-- ---------------------------------------------------------------------------
-- §1.82(10)  Pre-limit and Pre-complete
-- ---------------------------------------------------------------------------

/-! ### §1.82(10)  Pre-limit

  A PRE-LIMIT for D is a J-indexed family of cones cofinal in all cones:
  for every cone {B → D i} some member cone admits a (non-unique) factorization. -/

structure HasPreLimit {𝒟 : Type u} [Cat.{v} 𝒟] {ℬ : Type u₁} [Cat.{v} ℬ]
    (D : 𝒟 → ℬ) [Functor D] where
  J       : Type v
  cones   : J → DiagCone D
  cofinal : (c : DiagCone D) →
              ∃ (j : J) (u : c.apex ⟶ (cones j).apex), ∀ i, u ≫ (cones j).π i = c.π i

/-- A category is PRE-COMPLETE if every small diagram has a pre-limit (§1.82(10)). -/
class PreComplete (ℬ : Type u₁) [Cat.{v} ℬ] where
  hasPreLimit : {𝒟 : Type v} → [Cat.{v} 𝒟] → (D : 𝒟 → ℬ) → [Functor D] → HasPreLimit D

/-- Every complete category is pre-complete (singleton pre-limit). -/
instance complete_imp_preComplete {ℬ : Type u₁} [Cat.{v} ℬ] [hc : Complete ℬ] :
    PreComplete ℬ where
  hasPreLimit := fun {_} _ D _ =>
    let hl := hc.hasLimit D
    { J := PUnit.{v+1},
      cones := fun _ => hl.cone,
      cofinal := fun c => ⟨PUnit.unit, hl.lift c, hl.fac c⟩ }

-- ---------------------------------------------------------------------------
-- §1.83  Pre-adjoint and General Adjoint Functor Theorem
-- ---------------------------------------------------------------------------

/-! ### §1.83  Pre-adjoint for an object

  Given G : ℬ → 𝒜 and A ∈ 𝒜, a PRE-ADJOINT for A is a set
  {A —φ_i→ G(B_i)} cofinal in all maps A → G(B): for every A —f→ G(B)
  there exist i and x : B_i → B with φ_i ≫ G(x) = f (§1.83). -/

structure PreAdjointObj {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [hG : Functor G] (A : 𝒜) where
  I       : Type v
  obj     : I → ℬ
  maps    : (i : I) → A ⟶ G (obj i)
  cofinal : ∀ {B : ℬ} (f : A ⟶ G B),
              ∃ (i : I) (x : obj i ⟶ B), maps i ≫ hG.map x = f

/-- G : ℬ → 𝒜 is a PRE-ADJOINT FUNCTOR if every A ∈ 𝒜 has a pre-adjoint (§1.83). -/
structure PreAdjointFunctor {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [Functor G] where
  preAdj : (A : 𝒜) → PreAdjointObj G A

/-! ### §1.83  GENERAL ADJOINT FUNCTOR THEOREM

  If ℬ is locally small (automatic in our type-theoretic formulation) and complete,
  then G : ℬ → 𝒜 has a left adjoint iff it is continuous and pre-adjoint. -/

/-- §1.83 EASY HALF (pre-adjoint side): a left adjoint is a pre-adjoint functor.
    The unit `η_A : A → G(F A)` is itself a *singleton* pre-adjoint family for `A`:
    every `f : A → G B` factors as `η_A ≫ G x` with `x := ψ f` (§1.83, §1.817). -/
def preAdjointFunctor_of_adjunction
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    {G : ℬ → 𝒜} [hG : Functor G] {F : 𝒜 → ℬ} [Functor F] (adj : F ⊣ G) :
    PreAdjointFunctor G where
  preAdj A :=
    { I       := PUnit.{v+1}
      obj     := fun _ => F A
      maps    := fun _ => unit adj A
      cofinal := fun {B} f =>
        ⟨PUnit.unit, adj.ψ f, by
          -- η_A ≫ G(ψ f) = φ(ψ f) = f
          rw [← φ_eq adj (adj.ψ f), adj.φψ]⟩ }

/-- §1.83 EASY HALF (continuity side): a left adjoint's right adjoint is continuous —
    a right adjoint preserves all limits (§1.829/§1.834). The mediating map over a cone
    `{W → G(D i)}` is obtained by transposing to a cone `{F W → D i}`, lifting through the
    limit, and transposing back via the unit. -/
theorem isContinuous_of_adjunction
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    {G : ℬ → 𝒜} [hG : Functor G] {F : 𝒜 → ℬ} [hF : Functor F] (adj : F ⊣ G) :
    IsContinuous G := by
  intro 𝒟 _ D hD lim W legs hnat
  -- Transpose the W-legs to F W-legs : F W → D i.  tlegs i := ψ (legs i).
  -- These form a cone over D: ψ(legs i) ≫ D x = ψ(legs i ≫ G(D x)) = ψ(legs j).
  have tnat : ∀ {i j : 𝒟} (x : i ⟶ j),
      adj.ψ (legs i) ≫ hD.map x = adj.ψ (legs j) := by
    intro i j x
    rw [← ψ_nat_right adj (legs i) (hD.map x), hnat x]
  -- Lift the F W-cone through the limit, getting w : F W → lim.apex.
  let c : DiagCone D := { apex := F W, π := fun i => adj.ψ (legs i), nat := tnat }
  let w := lim.lift c
  have hwfac : ∀ i, w ≫ lim.cone.π i = adj.ψ (legs i) := lim.fac c
  -- Transpose w back: u := φ w = η_W ≫ G w : W → G(lim.apex).
  refine ⟨adj.φ w, ?_, ?_⟩
  · intro i
    -- u ≫ G(π i) = φ(w) ≫ G(π i) = φ(w ≫ π i) = φ(ψ(legs i)) = legs i.
    rw [← adj.φ_nat_right w (lim.cone.π i), hwfac i, adj.φψ]
  · intro u' hu'
    -- u' is determined: ψ u' is a mediating map for the cone c, so ψ u' = w by lim.uniq,
    -- hence u' = φ(ψ u') = φ w.
    have hψfac : ∀ i, adj.ψ u' ≫ lim.cone.π i = adj.ψ (legs i) := by
      intro i
      -- ψ u' ≫ π i = ψ(u' ≫ G(π i)) = ψ(legs i).
      rw [← ψ_nat_right adj u' (lim.cone.π i), hu' i]
    have hwu : adj.ψ u' = w := lim.uniq c (adj.ψ u') hψfac
    calc u' = adj.φ (adj.ψ u') := (adj.φψ u').symm
      _ = adj.φ w := by rw [hwu]

/-- §1.83 GENERAL ADJOINT FUNCTOR THEOREM. -/
theorem general_adjoint_functor_theorem
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [hG : Functor G]
    [Complete ℬ] :
    (∃ (F : 𝒜 → ℬ) (hF : Functor F), Nonempty (F ⊣ G)) ↔
    (IsContinuous G ∧ Nonempty (PreAdjointFunctor G)) := by
  constructor
  · -- (⇒) EASY: a left adjoint is continuous and pre-adjoint (proved above).
    rintro ⟨F, hF, ⟨adj⟩⟩
    exact ⟨isContinuous_of_adjunction adj, ⟨preAdjointFunctor_of_adjunction adj⟩⟩
  · -- (⇐) HARD: continuous + pre-adjoint ⟹ left adjoint, via the solution-set /
    -- representability construction (§1.834). Not yet formalized — see S1_82.md.
    rintro ⟨_hcont, ⟨_pre⟩⟩
    sorry

-- ---------------------------------------------------------------------------
-- §1.838  Well-powered
-- ---------------------------------------------------------------------------

/-! ### §1.838  Well-powered

  ℬ is WELL-POWERED if for every B ∈ ℬ the class of subobjects of B is small (§1.838). -/

-- (SUBOBJECT is defined canonically in S1_51 §1.51 as `Subobject ℬ B`; reused here.)

/-- Two subobjects of B are isomorphic if there is a compatible iso on domains. -/
def SubobjectIso {ℬ : Type u₁} [Cat.{v} ℬ] {B : ℬ} (s t : Subobject ℬ B) : Prop :=
  ∃ (i : s.dom ⟶ t.dom), IsIso i ∧ i ≫ t.arr = s.arr

/-- ℬ is WELL-POWERED: for every B the class of subobjects is essentially a set (§1.838). -/
class WellPowered (ℬ : Type u₁) [Cat.{v} ℬ] : Prop where
  small : ∀ (B : ℬ), ∃ (I : Type v) (repr : I → Subobject ℬ B),
            ∀ s : Subobject ℬ B, ∃ i : I, SubobjectIso s (repr i)

-- ---------------------------------------------------------------------------
-- §1.83(10)  Cogenerating set and Special Adjoint Functor Theorem
-- ---------------------------------------------------------------------------

/-! ### §1.83(10)  Cogenerating set

  {C_i} is a COGENERATING SET if {Hom(-, C_i)} is collectively faithful:
  f ≠ g : A → B implies ∃ i, ∃ h : B → C_i, f ≫ h ≠ g ≫ h.
  Equivalently (§1.83(10)): every object embeds into a product of the C_i's. -/

def IsCoGeneratingSet {ℬ : Type u₁} [Cat.{v} ℬ] {I : Type v} (C : I → ℬ) : Prop :=
  ∀ {A B : ℬ} (f g : A ⟶ B), f ≠ g →
    ∃ (i : I) (h : B ⟶ C i), f ≫ h ≠ g ≫ h

/-- §1.83(10) SPECIAL ADJOINT FUNCTOR THEOREM:
    If ℬ is complete, well-powered and has a cogenerating set,
    then every continuous G : ℬ → 𝒜 (𝒜 locally small) has a left adjoint. -/
theorem special_adjoint_functor_theorem
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [Functor G]
    [Complete ℬ] [WellPowered ℬ]
    {I : Type v} (C : I → ℬ) (_hcogen : IsCoGeneratingSet C)
    (hcont : IsContinuous G) :
    ∃ (F : 𝒜 → ℬ) (hF : Functor F), Nonempty (F ⊣ G) := by
  sorry

-- ---------------------------------------------------------------------------
-- Limit uniqueness up to isomorphism
-- ---------------------------------------------------------------------------

/-- Any two limit cones of the same diagram are canonically isomorphic:
    the mediating morphisms between them are mutual inverses (§1.822). -/
theorem limit_cone_unique {𝒟 : Type u} [Cat.{v} 𝒟] {ℬ : Type u₁} [Cat.{v} ℬ]
    {D : 𝒟 → ℬ} [Functor D] (L₁ L₂ : HasLimit D) :
    IsIso (L₁.lift L₂.cone) := by
  -- L₁.lift L₂.cone : L₁.cone.apex → L₂.cone.apex
  -- L₂.lift L₁.cone : L₂.cone.apex → L₁.cone.apex
  -- Compositions = id by uniqueness: Cat.id = L.lift (same cone)
  have id1 : L₁.lift L₁.cone = Cat.id L₁.cone.apex :=
    (L₁.uniq L₁.cone (Cat.id _) (fun i => Cat.id_comp _)).symm
  have id2 : L₂.lift L₂.cone = Cat.id L₂.cone.apex :=
    (L₂.uniq L₂.cone (Cat.id _) (fun i => Cat.id_comp _)).symm
  -- L₁.lift L₂.cone : L₂.cone.apex ⟶ L₁.cone.apex
  -- L₂.lift L₁.cone : L₁.cone.apex ⟶ L₂.cone.apex
  -- Prove compositions = id using uniqueness of mediating map
  -- L₁.lift L₂.cone ≫ L₂.lift L₁.cone : L₂.cone.apex ⟶ L₂.cone.apex
  have h12 : L₁.lift L₂.cone ≫ L₂.lift L₁.cone = Cat.id L₂.cone.apex := by
    rw [← id2]; apply L₂.uniq; intro i
    -- goal: L₁.lift L₂.cone ≫ L₂.lift L₁.cone ≫ L₂.cone.π i = L₂.cone.π i
    -- L₂.lift L₁.cone ≫ L₂.cone.π i = L₁.cone.π i (L₂.fac L₁.cone i)
    -- L₁.lift L₂.cone ≫ L₁.cone.π i = L₂.cone.π i (L₁.fac L₂.cone i)
    rw [Cat.assoc, L₂.fac, L₁.fac]
  have h21 : L₂.lift L₁.cone ≫ L₁.lift L₂.cone = Cat.id L₁.cone.apex := by
    rw [← id1]; apply L₁.uniq; intro i
    rw [Cat.assoc, L₁.fac, L₂.fac]
  exact ⟨L₂.lift L₁.cone, h12, h21⟩

-- ---------------------------------------------------------------------------
-- §1.829  A functor preserving weak-limits preserves limits
-- ---------------------------------------------------------------------------

/-! ### §1.829  Weak-continuity implies continuity

  If T : ℬ → 𝒞 carries every weak-limit to a weak-limit
  (i.e. the image is still a weak-limit), then it carries every limit to a limit (§1.829).

  The book's proof: if {L → D i} is a limit and T preserves the weak-limit condition,
  then the image is a weak-limit with monic family (from limit ⟹ monic), hence a limit. -/

/-! **Monic-family shape** (book's J-poset, §1.829).

  Given a diagram shape `𝒟`, `MFShape 𝒟` adjoins to the *discrete* poset on `𝒟`
  two new bottom points `botL`, `botR`, each below every `pt i`.  With a diagram
  sending `pt i ↦ Dᵢ` and `botL, botR ↦ L` (and both `botL→i`, `botR→i ↦ πᵢ`),
  the canonical lower bound is a weak-limit **iff** `{πᵢ}` is a monic family.
  Preservation of weak-limits therefore preserves monic families — exactly the
  ingredient that upgrades a preserved weak-limit to a genuine limit. -/
private inductive MFShape (𝒟 : Type v) : Type v
  | pt   : 𝒟 → MFShape 𝒟
  | botL : MFShape 𝒟
  | botR : MFShape 𝒟

/-- Morphisms of `MFShape`: identities, plus `botL → pt i` and `botR → pt i`. -/
private inductive MFHom {𝒟 : Type v} : MFShape 𝒟 → MFShape 𝒟 → Type v
  | idPt  : (i : 𝒟) → MFHom (.pt i) (.pt i)
  | idL   : MFHom .botL .botL
  | idR   : MFHom .botR .botR
  | arrL  : (i : 𝒟) → MFHom .botL (.pt i)
  | arrR  : (i : 𝒟) → MFHom .botR (.pt i)

/-- Composition in `MFShape`: every non-identity arrow has an identity on one side,
    so composition is determined by absorbing the identity. -/
private def mfComp {𝒟 : Type v} : {X Y Z : MFShape 𝒟} →
    MFHom X Y → MFHom Y Z → MFHom X Z
  | _, _, _, .idPt _, g => g
  | _, _, _, .idL,    g => g
  | _, _, _, .idR,    g => g
  | _, _, _, .arrL i, .idPt _ => .arrL i
  | _, _, _, .arrR i, .idPt _ => .arrR i

private instance mfShapeCat {𝒟 : Type v} : Cat.{v} (MFShape 𝒟) where
  Hom := MFHom
  id  := fun | .pt i => .idPt i | .botL => .idL | .botR => .idR
  comp := mfComp
  id_comp := by rintro X Y f; cases f <;> rfl
  comp_id := by rintro X Y f; cases f <;> rfl
  assoc := by rintro W X Y Z f g h; cases f <;> cases g <;> cases h <;> rfl

/-- The monic-family diagram for a family `{π i : L ⟶ D i}`:
    `pt i ↦ D i`, `botL, botR ↦ L`. -/
private def mfDiagObj {ℬ : Type u₁} [Cat.{v} ℬ] {𝒟 : Type v} (D : 𝒟 → ℬ) (L : ℬ) :
    MFShape 𝒟 → ℬ
  | .pt i => D i
  | .botL => L
  | .botR => L

private def mfDiagMap {ℬ : Type u₁} [Cat.{v} ℬ] {𝒟 : Type v} (D : 𝒟 → ℬ) {L : ℬ}
    (π : (i : 𝒟) → L ⟶ D i) :
    {X Y : MFShape 𝒟} → (X ⟶ Y) → (mfDiagObj D L X ⟶ mfDiagObj D L Y)
  | _, _, .idPt i => Cat.id (D i)
  | _, _, .idL    => Cat.id L
  | _, _, .idR    => Cat.id L
  | _, _, .arrL i => π i
  | _, _, .arrR i => π i

private instance mfDiagFunctor {ℬ : Type u₁} [Cat.{v} ℬ] {𝒟 : Type v} (D : 𝒟 → ℬ)
    {L : ℬ} (π : (i : 𝒟) → L ⟶ D i) : Functor (mfDiagObj D L) where
  map := mfDiagMap D π
  map_id := by rintro (i | _ | _) <;> rfl
  map_comp := by
    rintro X Y Z f g
    cases f <;> cases g <;>
      first
        | rfl
        | exact (Cat.id_comp _).symm
        | exact (Cat.comp_id _).symm

/-- §1.829: A functor that preserves weak-limits preserves limits.

    Proof (book's argument): the image `{T(πᵢ)}` of a limit cone is automatically a
    weak-limit; it is a genuine limit iff it is *collectively monic*.  Preservation of
    weak-limits forces collective monicity via the `MFShape` diagram above, which gives
    the missing uniqueness. -/
theorem preserves_weaklim_iff_preserves_lim
    {ℬ : Type u₁} [Cat.{v} ℬ] {𝒞 : Type u₂} [Cat.{v} 𝒞]
    (T : ℬ → 𝒞) [hT : Functor T] :
    -- If T sends every weak-limit to a weak-limit, then T is continuous
    (∀ {𝒟 : Type v} [Cat.{v} 𝒟] {D : 𝒟 → ℬ} [hD : Functor D] (wl : HasWeakLimit D),
       ∀ (W : 𝒞) (legs : (i : 𝒟) → W ⟶ T (D i))
         (_ : ∀ {i j : 𝒟} (x : i ⟶ j), legs i ≫ hT.map (hD.map x) = legs j),
         ∃ u : W ⟶ T wl.cone.apex, ∀ i, u ≫ hT.map (wl.cone.π i) = legs i) →
    IsContinuous T := by
  intro hpwl
  intro 𝒟 _ D hD lim W legs hnat
  -- Use the limit as a weak-limit
  let wl : HasWeakLimit D :=
    { cone := lim.cone, exist := fun c => ⟨lim.lift c, lim.fac c⟩ }
  -- T maps this weak-limit to a weak-limit-like structure by hypothesis
  obtain ⟨u, hu⟩ := hpwl wl W legs hnat
  refine ⟨u, hu, ?_⟩
  intro u' hu'
  -- Collective monicity of `{T(lim.cone.π i)}` upgrades existence to uniqueness:
  -- `u, u'` agree against every `T(π i)`, so they coincide.
  -- ── Build the `MFShape` diagram for the family `{lim.cone.π i}`. ──
  let L  := lim.cone.apex
  let πf : (i : 𝒟) → L ⟶ D i := lim.cone.π
  -- the limit projections are collectively monic
  have limMonic : ∀ {X : ℬ} (a b : X ⟶ L), (∀ i, a ≫ πf i = b ≫ πf i) → a = b := by
    intro X a b hab
    let cc : DiagCone D :=
      { apex := X, π := fun i => a ≫ πf i
        nat := fun {i j} x => by rw [Cat.assoc, lim.cone.nat x] }
    have ha : a = lim.lift cc := lim.uniq cc a (fun i => rfl)
    have hb : b = lim.lift cc := lim.uniq cc b (fun i => (hab i).symm)
    rw [ha, hb]
  let D' := mfDiagObj D L
  letI hD' : Functor D' := mfDiagFunctor D πf
  -- canonical lower bound with apex L: `botL, botR ↦ id`, `pt i ↦ π i`
  let c₀ : DiagCone D' :=
    { apex := L
      π := fun X => match X with | .pt i => πf i | .botL => Cat.id L | .botR => Cat.id L
      nat := by
        rintro X Y x
        cases x <;>
          first
            | rfl
            | exact Cat.comp_id _
            | exact Cat.id_comp _ }
  -- it is a weak-limit: a cone `c` factors through it iff `c.π botL = c.π botR`,
  -- which holds because `{π i}` is collectively monic (from `lim.uniq`).
  let wl' : HasWeakLimit D' :=
    { cone := c₀
      exist := fun c => by
        -- the `botL`-leg is a valid factorization
        refine ⟨c.π .botL, ?_⟩
        rintro (i | _ | _)
        · -- c.π botL ≫ π i = c.π (pt i): naturality of c on `arrL i`
          exact c.nat (MFHom.arrL i : (MFShape.botL : MFShape 𝒟) ⟶ .pt i)
        · exact Cat.comp_id _
        · -- need c.π botL ≫ id = c.π botR; both legs agree after composing with every π i
          have heq : c.π .botL = c.π .botR := by
            apply limMonic (c.π .botL) (c.π .botR)
            intro i
            have hL := c.nat (MFHom.arrL i : (MFShape.botL : MFShape 𝒟) ⟶ .pt i)
            have hR := c.nat (MFHom.arrR i : (MFShape.botR : MFShape 𝒟) ⟶ .pt i)
            -- both equal c.π (pt i)
            exact hL.trans hR.symm
          exact (Cat.comp_id (c.π .botL)).trans heq }
  -- T preserves this weak-limit: build the test cone over `T∘D'` with apex W,
  -- legs `u` at botL, `u'` at botR, `legs i` at pt i.
  let testLegs : (Z : MFShape 𝒟) → W ⟶ T (D' Z) :=
    fun Z => match Z with | .pt i => legs i | .botL => u | .botR => u'
  have hTnat : ∀ {X Y : MFShape 𝒟} (x : X ⟶ Y),
      testLegs X ≫ hT.map (hD'.map x) = testLegs Y := by
    rintro X Y x
    cases x with
    | idPt i => show legs i ≫ hT.map (Cat.id (D i)) = legs i
                rw [hT.map_id, Cat.comp_id]
    | idL    => show u ≫ hT.map (Cat.id L) = u
                rw [hT.map_id, Cat.comp_id]
    | idR    => show u' ≫ hT.map (Cat.id L) = u'
                rw [hT.map_id, Cat.comp_id]
    | arrL i => exact hu i
    | arrR i => exact hu' i
  obtain ⟨w, hw⟩ := hpwl wl' W testLegs hTnat
  -- `w ≫ T(c₀.π botL) = u` and `w ≫ T(c₀.π botR) = u'`, but both `c₀`-legs are `id L`.
  -- both `c₀`-legs at botL/botR are `Cat.id L`, so `T(id) = id` and `w` equals both `u`, `u'`
  have eL : w ≫ hT.map (Cat.id L) = u := hw .botL
  have eR : w ≫ hT.map (Cat.id L) = u' := hw .botR
  rw [hT.map_id, Cat.comp_id] at eL eR
  rw [← eL, ← eR]

-- ---------------------------------------------------------------------------
-- §1.831  Uniformly continuous functor (More General AFT)
-- ---------------------------------------------------------------------------

/-! ### §1.831  Uniformly continuous

  G : ℬ → 𝒜 is UNIFORMLY CONTINUOUS if for every small D : 𝒟 → ℬ,
  G sends the lower-bounds of D (i.e. cones over D) to a cofinal family of
  lower-bounds of G∘D: for every cone {A → G(Dᵢ)}, there is a cone {B → Dᵢ}
  and a map A → G(B) through which the original factors (§1.831). -/

def IsUniformlyContinuous {ℬ : Type u₁} [Cat.{v} ℬ] {𝒜 : Type u} [Cat.{v} 𝒜]
    (G : ℬ → 𝒜) [hG : Functor G] : Prop :=
  ∀ {𝒟 : Type v} [Cat.{v} 𝒟] {D : 𝒟 → ℬ} [hD : Functor D],
    ∀ (A : 𝒜) (legs : (i : 𝒟) → A ⟶ G (D i))
      (_ : ∀ {i j : 𝒟} (x : i ⟶ j), legs i ≫ hG.map (hD.map x) = legs j),
      -- there is a cone in ℬ and a map A → G(apex) factoring all legs
      ∃ (B : ℬ) (cone_legs : (i : 𝒟) → B ⟶ D i)
        (_ : ∀ {i j : 𝒟} (x : i ⟶ j), cone_legs i ≫ hD.map x = cone_legs j)
        (φ : A ⟶ G B),
        ∀ i, φ ≫ hG.map (cone_legs i) = legs i

/-- A uniformly continuous functor preserves pre-limits, hence weak-limits, hence limits
    (§1.831). If ℬ is complete then uniform continuity = continuity. -/
theorem uniformly_continuous_preserves_prelimits
    {ℬ : Type u₁} [Cat.{v} ℬ] {𝒜 : Type u} [Cat.{v} 𝒜]
    (G : ℬ → 𝒜) [hG : Functor G] (huc : IsUniformlyContinuous G) :
    ∀ {𝒟 : Type v} [Cat.{v} 𝒟] {D : 𝒟 → ℬ} [hD : Functor D] (pl : HasPreLimit D),
      ∀ (A : 𝒜) (legs : (i : 𝒟) → A ⟶ G (D i))
        (_ : ∀ {i j : 𝒟} (x : i ⟶ j), legs i ≫ hG.map (hD.map x) = legs j),
        ∃ (j : pl.J) (u : A ⟶ G (pl.cones j).apex),
          ∀ i, u ≫ hG.map ((pl.cones j).π i) = legs i := by
  intro 𝒟 _ D hD pl A legs hnat
  -- By uniform continuity, find B,cone,φ
  obtain ⟨B, cone_legs, cone_nat, φ, hφ⟩ := huc A legs hnat
  -- pl is cofinal: there exist j and u : B → apex(cones j)
  let c : DiagCone D := { apex := B, π := cone_legs, nat := cone_nat }
  obtain ⟨j, u, hu⟩ := pl.cofinal c
  refine ⟨j, φ ≫ hG.map u, ?_⟩
  intro i
  rw [Cat.assoc, ← hG.map_comp, hu i, hφ i]

/-- §1.831 EASY HALF (uniform-continuity side): a left adjoint is uniformly continuous.
    Given a cone `{A → G(D i)}`, take `B := F A`, `cone_legs i := ψ(legs i)` and the unit
    `η_A : A → G(F A)` as factoring map; `η_A ≫ G(ψ(legs i)) = φ(ψ(legs i)) = legs i`.
    No completeness is needed — this is strictly weaker than `isContinuous_of_adjunction`. -/
theorem isUniformlyContinuous_of_adjunction
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    {G : ℬ → 𝒜} [hG : Functor G] {F : 𝒜 → ℬ} [hF : Functor F] (adj : F ⊣ G) :
    IsUniformlyContinuous G := by
  intro 𝒟 _ D hD A legs hnat
  refine ⟨F A, fun i => adj.ψ (legs i), ?_, unit adj A, ?_⟩
  · -- cone_legs form a cone over D, by the same transpose-naturality argument.
    intro i j x
    rw [← ψ_nat_right adj (legs i) (hD.map x), hnat x]
  · -- η_A ≫ G(ψ(legs i)) = φ(ψ(legs i)) = legs i.
    intro i
    rw [← φ_eq adj (adj.ψ (legs i)), adj.φψ]

/-- §1.831 MORE GENERAL ADJOINT FUNCTOR THEOREM.
    If ℬ is locally small and idempotents split, then G : ℬ → 𝒜 has a left adjoint
    iff it is uniformly continuous and pre-adjoint. -/
theorem more_general_adjoint_functor_theorem
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [hG : Functor G] [PreComplete ℬ] :
    (∃ (F : 𝒜 → ℬ) (hF : Functor F), Nonempty (F ⊣ G)) ↔
    (IsUniformlyContinuous G ∧ Nonempty (PreAdjointFunctor G)) := by
  constructor
  · -- (⇒) EASY: a left adjoint is uniformly continuous and pre-adjoint (proved above).
    rintro ⟨F, hF, ⟨adj⟩⟩
    exact ⟨isUniformlyContinuous_of_adjunction adj, ⟨preAdjointFunctor_of_adjunction adj⟩⟩
  · -- (⇐) HARD: uniformly continuous + pre-adjoint ⟹ left adjoint, via the pre-limit
    -- construction + splitting idempotents (§1.834–§1.835). Not yet formalized — see S1_82.md.
    rintro ⟨_huc, ⟨_pre⟩⟩
    sorry

-- ---------------------------------------------------------------------------
-- §1.837  Complete + pre-cocomplete → cocomplete
-- ---------------------------------------------------------------------------

/-! ### §1.837  A complete locally small category is cocomplete iff pre-cocomplete.

  The book: if ℬ is complete then for any D, Δ : ℬ → ℬ^D is continuous.
  Hence a complete category is cocomplete iff it is pre-cocomplete (§1.837). -/

/-- A category is PRE-COCOMPLETE if every small diagram has a pre-colimit (§1.837). -/
class PreCocomplete (ℬ : Type u₁) [Cat.{v} ℬ] where
  hasPreColimit : {𝒟 : Type v} → [Cat.{v} 𝒟] → (D : 𝒟 → ℬ) → [Functor D] → HasPreLimit D

/-- §1.837: A complete locally small category is cocomplete iff it is pre-cocomplete. -/
theorem complete_cocomplete_iff_precocomplete
    (ℬ : Type u₁) [Cat.{v} ℬ] [Complete ℬ] :
    Nonempty (Cocomplete ℬ) ↔ Nonempty (PreCocomplete ℬ) := by
  sorry

end Freyd
