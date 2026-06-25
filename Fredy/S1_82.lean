/-
  Freyd & Scedrov, *Categories and Allegories* §1.82–§1.83

  §1.82     DIAGONAL FUNCTOR Δ : B → B^D (constant-diagram functor)
  §1.821    DiagCone / DiagCocone — compatible families of maps
  §1.822    HasLimit / HasColimit — universal cone / cocone
            limit_cone_unique — limits unique up to iso (PROVED)
  §1.823    Complete / Cocomplete
  §1.825    complete_iff_eq_prod — iff equalizers + products
            (⇐ hard direction PROVED; ⇒ easy direction Sorry)
  §1.827    IsContinuous / IsCocontinuous
  §1.828    HasWeakLimit / WeaklyComplete
            complete_imp_weaklyComplete (PROVED)
  §1.829    preserves_weaklim_iff_preserves_lim (partial; uniqueness Sorry)
  §1.82(10) HasPreLimit / PreComplete
            complete_imp_preComplete (PROVED)
  §1.83     PreAdjointObj / PreAdjointFunctor
            adjunction_of_representability — §1.817 ← bridge (PROVED, axiom-free)
            InitialElement / InitialElement.represents — initial element ⟹ representability (PROVED)
            wideEqualizer — joint equalizer via equalizers+products (PROVED)
            gaft_representability — §1.834–§1.835 representing-object engine (PROVED, axiom-clean:
            solution set ⟹ product P ⟹ wide equalizer R; continuity gives the element θ and
            uniqueness of factoring maps)
            general_adjoint_functor_theorem — FULLY PROVED (both directions; axioms = propext,
            Classical.choice)
  §1.831    IsUniformlyContinuous
            uniformly_continuous_preserves_prelimits (PROVED)
            IdempotentsSplit (§1.281)
            wforkDiag — wide-fork shape (weakly equalizes a small endo-family against id)
            mgaft_representability — §1.835 pre-limit/idempotent-splitting engine (PROVED): UC on
            a discrete pre-limit ⟹ weakly-initial (P,η); UC on a wide-fork pre-limit over the
            η-fixing endos ⟹ an idempotent e₀; IdempotentsSplit cuts (P,η) to an initial element
            more_general_adjoint_functor_theorem — FULLY PROVED (both directions; needs
            IdempotentsSplit, else FALSE per §1.836; axioms = propext, Classical.choice)
  §1.837    HasPreColimit (faithful colimit-dual) / PreCocomplete (re-modeled)
            cocomplete_imp_preCocomplete (PROVED, axiom-free)
            cocomplete_of_complete_precocomplete — FULLY PROVED (colimit-dual of the GAFT engine,
            built inside ℬ: product of pre-colimit nadirs ⟹ weakly-initial cocone ⟹ wide equalizer
            of cocone-endos ⟹ colimit; no functor category needed)
            complete_cocomplete_iff_precocomplete — FULLY PROVED (axioms = propext, Classical.choice)
  §1.838    WellPowered / SubobjectIso
            Cospan / gPullbackFactor — `G` continuous ⟹ `G` preserves pullbacks of monos (PROVED)
  §1.83(10) IsCoGeneratingSet
            cogenerating_embeds_in_product — every object embeds in a product of cogenerators (PROVED)
            saft_preadjoint — well-powered + cogenerating set ⟹ pre-adjoint solution set (PROVED)
            saft_representability — FULLY PROVED (saft_preadjoint fed to the GAFT engine)
            special_adjoint_functor_theorem — FULLY PROVED (axioms = propext, Classical.choice,
            Quot.sound)

  Remaining Sorries (0).  GAFT (§1.83), MGAFT (§1.831), SAFT (§1.83(10)) and §1.837 are all
  fully proved.  MGAFT's "pre-complete + split idempotents" weak-initial-object cutoff (which the
  full-`Complete` GAFT engine cannot supply) is built directly via wide-fork pre-limits and the
  `IdempotentsSplit` hypothesis.  See S1_82.md.
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

/-- §1.817 bridge (←): if `(A, G(-))` is representable for *every* `A`, then `G` has
    a left adjoint.  This is the representability-to-adjunction half of §1.817, proved
    here inline (the copy in `S1_8.lean` is still deferred).  No completeness is used —
    it is pure universal-property bookkeeping, the common engine that turns each hard
    adjoint-functor-theorem into "build a representing object for every `A`".

    Construction: `F A :=` the representing object; the *unit* `η_A : A → G(F A)` is
    `ψ (id (F A))`; `F` acts on `f : A ⟶ A'` by the unique map `φ (f ≫ η_{A'})`. -/
def adjunction_of_representability
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [hG : Functor G]
    (repr : ∀ A : 𝒜, Σ R : ℬ, RepresentedBy G A R) :
    Σ (F : 𝒜 → ℬ), Σ (_ : Functor F), F ⊣ G := by
  -- representing object and chosen representation for each `A`
  let F : 𝒜 → ℬ := fun A => (repr A).1
  let r : (A : 𝒜) → RepresentedBy G A (F A) := fun A => (repr A).2
  -- unit  η_A : A → G(F A) := ψ (id (F A))
  let η : (A : 𝒜) → A ⟶ G (F A) := fun A => (r A).ψ (Cat.id (F A))
  -- key bridge: for any `g : A ⟶ G B`, `η_A ≫ G ((r A).φ g) = g`
  have ηbridge : ∀ {A : 𝒜} {B : ℬ} (g : A ⟶ G B),
      η A ≫ hG.map ((r A).φ g) = g := by
    intro A B g
    -- η A ≫ G(φ g) = ψ (id ≫ φ g)  via reverse naturality of ψ = φ⁻¹ … do it via φ_nat
    -- Use: φ (η A ≫ G(φ g)) = φ (η A) ≫ φ g = id ≫ φ g = φ g, then apply ψ.
    have h1 : (r A).φ (η A ≫ hG.map ((r A).φ g)) = (r A).φ g := by
      rw [(r A).φ_nat (η A) ((r A).φ g)]
      -- φ (η A) = φ (ψ (id)) = id
      have : (r A).φ (η A) = Cat.id (F A) := (r A).φψ (Cat.id (F A))
      rw [this, Cat.id_comp]
    -- φ injective: φ (ψ φ) = …; use ψφ on both sides
    calc η A ≫ hG.map ((r A).φ g)
        = (r A).ψ ((r A).φ (η A ≫ hG.map ((r A).φ g))) := ((r A).ψφ _).symm
      _ = (r A).ψ ((r A).φ g) := by rw [h1]
      _ = g := (r A).ψφ g
  -- F on morphisms
  let Fmap : {A A' : 𝒜} → (A ⟶ A') → (F A ⟶ F A') :=
    fun {A A'} f => (r A).φ (f ≫ η A')
  -- functoriality
  have Fmap_id : ∀ A : 𝒜, Fmap (Cat.id A) = Cat.id (F A) := by
    intro A
    show (r A).φ (Cat.id A ≫ η A) = Cat.id (F A)
    rw [Cat.id_comp]; exact (r A).φψ (Cat.id (F A))
  have Fmap_comp : ∀ {A A' A'' : 𝒜} (f : A ⟶ A') (g : A' ⟶ A''),
      Fmap (f ≫ g) = Fmap f ≫ Fmap g := by
    intro A A' A'' f g
    show (r A).φ ((f ≫ g) ≫ η A'') = (r A).φ (f ≫ η A') ≫ (r A').φ (g ≫ η A'')
    -- RHS: φ (f ≫ η A') ≫ Fmap g = φ ((f ≫ η A') ≫ G (Fmap g))  by φ_nat
    rw [← (r A).φ_nat (f ≫ η A') ((r A').φ (g ≫ η A''))]
    -- now both sides are φ of something; compare arguments
    congr 1
    -- (f ≫ g) ≫ η A''  =  (f ≫ η A') ≫ G (φ (g ≫ η A''))
    rw [Cat.assoc, Cat.assoc, ηbridge (g ≫ η A'')]
  let hF : Functor F :=
    { map := Fmap, map_id := Fmap_id, map_comp := Fmap_comp }
  refine ⟨F, hF, ?_⟩
  -- φ on the representation is injective (it has a two-sided inverse ψ)
  have φinj : ∀ {A : 𝒜} {B : ℬ} {g₁ g₂ : A ⟶ G B},
      (r A).φ g₁ = (r A).φ g₂ → g₁ = g₂ := by
    intro A B g₁ g₂ h
    calc g₁ = (r A).ψ ((r A).φ g₁) := ((r A).ψφ g₁).symm
      _ = (r A).ψ ((r A).φ g₂) := by rw [h]
      _ = g₂ := (r A).ψφ g₂
  -- the adjunction; φ := ψ_A, ψ := φ_A
  refine
    { φ := fun {A B} h => (r A).ψ h
      ψ := fun {A B} g => (r A).φ g
      φψ := fun {A B} g => (r A).ψφ g
      ψφ := fun {A B} h => (r A).φψ h
      φ_nat_left := ?_
      φ_nat_right := ?_ }
  · -- φ (Fmap a ≫ h) = a ≫ φ h, i.e. ψ_{A'} (Fmap a ≫ h) = a ≫ ψ_A h.
    -- Apply the bijection (r A').φ to both sides and compare in hom(F A', B).
    intro A' A B a h
    show (r A').ψ (Fmap a ≫ h) = a ≫ (r A).ψ h
    apply φinj
    -- LHS: φ (ψ (Fmap a ≫ h)) = Fmap a ≫ h
    rw [(r A').φψ (Fmap a ≫ h)]
    -- RHS: φ (a ≫ ψ_A h).  Rewrite Fmap a = φ(a ≫ η A) and h = φ(ψ_A h).
    show Fmap a ≫ h = (r A').φ (a ≫ (r A).ψ h)
    have hh : h = (r A).φ ((r A).ψ h) := ((r A).φψ h).symm
    -- (r A').φ (a ≫ ψ_A h):  ψ_A h = η A ≫ G h  (from ηbridge with g := ψ_A h)
    have hψ : η A ≫ hG.map h = (r A).ψ h := by
      have := ηbridge ((r A).ψ h)
      rwa [(r A).φψ h] at this
    calc Fmap a ≫ h
        = (r A').φ (a ≫ η A) ≫ (r A).φ ((r A).ψ h) := by rw [← hh]
      _ = (r A').φ ((a ≫ η A) ≫ hG.map ((r A).φ ((r A).ψ h))) := by
            rw [(r A').φ_nat (a ≫ η A) ((r A).φ ((r A).ψ h))]
      _ = (r A').φ ((a ≫ η A) ≫ hG.map h) := by rw [(r A).φψ h]
      _ = (r A').φ (a ≫ (r A).ψ h) := by rw [Cat.assoc, hψ]
  · -- φ (h ≫ b) = φ h ≫ G b, i.e. ψ_A (h ≫ b) = ψ_A h ≫ G b.
    intro A B B' h b
    show (r A).ψ (h ≫ b) = (r A).ψ h ≫ hG.map b
    apply φinj
    rw [(r A).φψ (h ≫ b)]
    -- φ (ψ h ≫ G b) = φ (ψ h) ≫ b = h ≫ b  via φ_nat then φψ
    rw [(r A).φ_nat ((r A).ψ h) b, (r A).φψ h]

-- ---------------------------------------------------------------------------
-- §1.834–§1.835  Category of elements / initial element ⟹ representability
-- ---------------------------------------------------------------------------

/-! ### Initial element of `(A, G(-))` (= coterminator of the category of elements)

  The category of elements `El(A,G(-))` has objects `(B, g : A ⟶ G B)` and a morphism
  `(B,g) → (B',g')` is a `ℬ`-map `x : B ⟶ B'` with `g ≫ G x = g'`.  An INITIAL object is a
  pair `(R, θ)` such that every `(B, g)` receives a UNIQUE such morphism from it.  Packaging
  the two universal facts (existence + uniqueness of `x : R ⟶ B` with `θ ≫ G x = g`) is exactly
  the data of a `RepresentedBy G A R`, so the §1.817 bridge applies. -/

/-- `(R, θ)` is an INITIAL ELEMENT of `(A, G(-))`: `θ : A ⟶ G R`, and every `g : A ⟶ G B`
    is `θ ≫ G x` for a *unique* `x : R ⟶ B` (§1.834).  This is the coterminator of the
    category of elements `El(A,G(-))`. -/
structure InitialElement {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [hG : Functor G] (A : 𝒜) (R : ℬ) where
  θ      : A ⟶ G R
  exists_map : ∀ {B : ℬ} (g : A ⟶ G B), ∃ x : R ⟶ B, θ ≫ hG.map x = g
  uniq_map   : ∀ {B : ℬ} (x₁ x₂ : R ⟶ B), θ ≫ hG.map x₁ = θ ≫ hG.map x₂ → x₁ = x₂

/-- An initial element of `(A, G(-))` represents the functor (§1.817 / §1.834): the bijection
    `(A ⟶ G B) ≃ (R ⟶ B)` is `g ↦ (the unique factoring map)`, `x ↦ θ ≫ G x`. -/
noncomputable def InitialElement.represents {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    {G : ℬ → 𝒜} [hG : Functor G] {A : 𝒜} {R : ℬ} (ι : InitialElement G A R) :
    RepresentedBy G A R where
  φ {B} g  := (ι.exists_map g).choose
  ψ {B} h  := ι.θ ≫ hG.map h
  -- φ (ψ h) = h: both `(ι.exists_map (ψ h)).choose` and `h` factor `ψ h = θ ≫ G h`, so equal.
  φψ {B} h := by
    apply ι.uniq_map
    rw [(ι.exists_map (ι.θ ≫ hG.map h)).choose_spec]
  -- ψ (φ g) = g: the defining property of the chosen factoring map.
  ψφ {B} g := (ι.exists_map g).choose_spec
  -- naturality: φ (g ≫ G b) = φ g ≫ b, by uniqueness of factoring maps.
  φ_nat {B B'} g b := by
    apply ι.uniq_map
    rw [(ι.exists_map (g ≫ hG.map b)).choose_spec, hG.map_comp, ← Cat.assoc,
        (ι.exists_map g).choose_spec]

-- ---------------------------------------------------------------------------
-- Wide equalizer (joint equalizer of a small family against the identity)
-- ---------------------------------------------------------------------------

/-! ### Wide-equalizer (joint equalizer of a small family against the identity)

  For a small family `e : K → (P ⟶ P)` the WIDE EQUALIZER jointly equalizes every `eₖ`
  with `id_P`: an object `R` with `r : R ⟶ P` such that `r ≫ eₖ = r` for all `k`, universal
  among such maps.  We build it constructively from equalizers + products (both supplied by
  `Complete ℬ`) as the equalizer of `tupling e` and `tupling (const id)` into `∏ₖ P`, avoiding
  any bespoke diagram shape. -/

/-- The wide equalizer of `{eₖ}` against `id_P`: object `R`, map `r : R ⟶ P` with `r ≫ eₖ = r`
    for every `k`, universal among maps that equalize the whole family with the identity. -/
private structure WideEqualizer {ℬ : Type u₁} [Cat.{v} ℬ] {P : ℬ} {K : Type v}
    (e : K → (P ⟶ P)) where
  R    : ℬ
  r    : R ⟶ P
  spec : ∀ k, r ≫ e k = r
  lift : ∀ {X : ℬ} (m : X ⟶ P), (∀ k, m ≫ e k = m) → X ⟶ R
  fac  : ∀ {X : ℬ} (m : X ⟶ P) (h : ∀ k, m ≫ e k = m), lift m h ≫ r = m
  uniq : ∀ {X : ℬ} (m : X ⟶ P) (h : ∀ k, m ≫ e k = m) (u : X ⟶ R), u ≫ r = m → u = lift m h

/-- Build the wide equalizer from equalizers + products.  With `Q := ∏ₖ P`, `f := tupling e`,
    `g := tupling (const id)`, the equalizer `r : R ⟶ P` of `f, g` satisfies `r ≫ eₖ = r` (read
    off each projection), and its universal property transfers along the product. -/
private def wideEqualizer {ℬ : Type u₁} [Cat.{v} ℬ]
    (heq : HasEqualizers ℬ) (hp : HasProducts ℬ) {P : ℬ} {K : Type v}
    (e : K → (P ⟶ P)) : WideEqualizer e := by
  letI : HasEqualizers ℬ := heq
  let Q : ℬ := hp.prodObj (fun _ : K => P)
  let f : P ⟶ Q := hp.tupling e
  let g : P ⟶ Q := hp.tupling (fun _ : K => Cat.id P)
  -- a map `m : X ⟶ P` equalizes `f,g` iff it equalizes every `eₖ` with the identity.
  have key : ∀ {X : ℬ} (m : X ⟶ P), (m ≫ f = m ≫ g) ↔ (∀ k, m ≫ e k = m) := by
    intro X m
    constructor
    · intro hfg k
      have := congrArg (· ≫ hp.proj k) hfg
      simp only at this
      rw [Cat.assoc, hp.tupling_fac, Cat.assoc, hp.tupling_fac, Cat.comp_id] at this
      exact this
    · intro hk
      -- projections agree: `(m≫f)≫proj k = m≫eₖ = m = m≫id = (m≫g)≫proj k`; products are
      -- jointly monic (`tupling_uniq`), so `m≫f = m≫g`.
      have proj_eq : ∀ k, (m ≫ f) ≫ hp.proj k = (m ≫ g) ≫ hp.proj k := by
        intro k
        rw [Cat.assoc, hp.tupling_fac, Cat.assoc, hp.tupling_fac, Cat.comp_id, hk k]
      have e1 : m ≫ f = hp.tupling (fun k => (m ≫ g) ≫ hp.proj k) :=
        hp.tupling_uniq (fun k => (m ≫ g) ≫ hp.proj k) (m ≫ f) proj_eq
      have e2 : m ≫ g = hp.tupling (fun k => (m ≫ g) ≫ hp.proj k) :=
        hp.tupling_uniq (fun k => (m ≫ g) ≫ hp.proj k) (m ≫ g) (fun _ => rfl)
      exact e1.trans e2.symm
  let r : eqObj f g ⟶ P := eqMap f g
  have hr : ∀ k, r ≫ e k = r := (key r).1 (eqMap_eq f g)
  exact
  { R    := eqObj f g
    r    := r
    spec := hr
    lift := fun {X} m h => eqLift f g m ((key m).2 h)
    fac  := fun {X} m h => eqLift_fac f g m ((key m).2 h)
    uniq := fun {X} m h u hu => eqLift_uniq f g m ((key m).2 h) u hu }


/-- §1.834–§1.835 (the heart of the GAFT): for a *continuous* and *pre-adjoint* `G` out
    of a *complete* `ℬ`, the functor `(A, G(-))` is representable for every `A` — i.e. its
    category of elements has an initial object (= the representing object, §1.817).

    Construction (Freyd §1.834–§1.835, made constructive):
    * `P := lim obj` over the pre-adjoint solution set `{(obj i, maps i)}` (completeness ⟹ the
      discrete product exists; legs `proj i` are collectively monic).
    * `η : A ⟶ G P` from continuity applied to that product: the cone `{maps i}` over `G∘obj`
      factors uniquely as `η ≫ G(proj i) = maps i`.
    * `(P, η)` is WEAKLY initial: any `g : A ⟶ G B` factors through it via cofinality.
    * cut to the genuine initial object by the WIDE EQUALIZER `r : R ⟶ P` of all `A↓G`-endos
      `e : P ⟶ P` of `(P, η)` (i.e. `η ≫ G e = η`).  Continuity applied to this equalizer makes
      `η` factor as `θ ≫ G r` (the representing element `θ`); uniqueness of factoring maps out of
      `(R, θ)` follows by equalizing two candidates, factoring `θ` through that equalizer
      (continuity again), pulling back along a weakly-initial map, and using the wide-equalizer
      spec together with monicity of `r`. -/
private noncomputable def gaft_representability
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    {G : ℬ → 𝒜} [hG : Functor G] [hc : Complete ℬ]
    (hcont : IsContinuous G) (pre : PreAdjointFunctor G) :
    ∀ A : 𝒜, Σ R : ℬ, RepresentedBy G A R := by
  intro A
  classical
  -- equalizers + products from completeness (reused below for the wide equalizer)
  let heq : HasEqualizers ℬ := complete_hasEqualizers hc
  let hp  : HasProducts ℬ := complete_hasProducts hc
  -- ── solution set (pre-adjoint family) for A ──
  let pa := pre.preAdj A
  let I  : Type v := pa.I
  let obj : I → ℬ := pa.obj
  let maps : (i : I) → A ⟶ G (obj i) := pa.maps
  -- ── P := product of the solution objects, as a limit (so continuity applies) ──
  letI : Cat.{v} I := discCat82
  letI : Functor obj := discreteFunctor obj
  let dlim := hc.hasLimit obj
  let P : ℬ := dlim.cone.apex
  let proj : (i : I) → P ⟶ obj i := dlim.cone.π
  -- projections are collectively monic (limit cone)
  have projMonic : ∀ {X : ℬ} (u v : X ⟶ P), (∀ i, u ≫ proj i = v ≫ proj i) → u = v := by
    intro X u v huv
    let cc : DiagCone obj :=
      { apex := X, π := fun i => u ≫ proj i
        nat := by
          intro i j x; obtain ⟨⟨hij⟩⟩ := x; subst hij
          show (u ≫ proj i) ≫ Functor.map (Cat.id i) = u ≫ proj i
          rw [Functor.map_id, Cat.comp_id] }
    have hu : u = dlim.lift cc := dlim.uniq cc u (fun _ => rfl)
    have hv : v = dlim.lift cc := dlim.uniq cc v (fun i => (huv i).symm)
    rw [hu, hv]
  -- ── η : A ⟶ G P  from continuity applied to the product limit ──
  have hmapsnat : ∀ {i j : I} (x : i ⟶ j),
      maps i ≫ hG.map (Functor.map x) = maps j := by
    intro i j x; obtain ⟨⟨hij⟩⟩ := x; subst hij
    show maps i ≫ hG.map (Functor.map (Cat.id i)) = maps i
    rw [Functor.map_id, hG.map_id, Cat.comp_id]
  let ηex := hcont dlim A maps hmapsnat
  let η : A ⟶ G P := ηex.choose
  have hηfac : ∀ i, η ≫ hG.map (proj i) = maps i := ηex.choose_spec.1
  -- weak initiality of (P, η): every g : A ⟶ G B factors as η ≫ G w for some w : P ⟶ B
  have weakInit : ∀ {B : ℬ} (g : A ⟶ G B), ∃ w : P ⟶ B, η ≫ hG.map w = g := by
    intro B g
    obtain ⟨i, y, hy⟩ := pa.cofinal g
    refine ⟨proj i ≫ y, ?_⟩
    rw [hG.map_comp, ← Cat.assoc, hηfac i, hy]
  -- ── wide equalizer of all A↓G-endomorphisms of (P, η) ──
  let K : Type v := { e : P ⟶ P // η ≫ hG.map e = η }
  let we := wideEqualizer heq hp (fun (k : K) => k.1)
  let R : ℬ := we.R
  let r : R ⟶ P := we.r
  -- r is monic (it is an equalizer map: wideEqualizer.uniq is left-cancellation)
  have rMonic : ∀ {X : ℬ} (u v : X ⟶ R), u ≫ r = v ≫ r → u = v := by
    intro X u v huv
    have hm : ∀ k, (u ≫ r) ≫ (fun (k : K) => k.1) k = u ≫ r := by
      intro k; rw [Cat.assoc, we.spec k]
    have hu := we.uniq (u ≫ r) hm u rfl
    have hv := we.uniq (u ≫ r) (by rw [huv] at hm ⊢; exact hm) v huv.symm
    rw [hu]; rw [huv] at hm; rw [hv]
  -- ── G preserves equalizers: a reusable factoring lemma via the WPP limit ──
  -- for a,b : Y ⟶ Z and k : A ⟶ G Y with k ≫ G a = k ≫ G b, build E, m : E ⟶ Y (monic,
  -- m ≫ a = m ≫ b) and unique θ_E : A ⟶ G E with θ_E ≫ G m = k.
  let eqFactor : ∀ {Y Z : ℬ} (a b : Y ⟶ Z) (k : A ⟶ G Y),
      k ≫ hG.map a = k ≫ hG.map b →
      Σ' (E : ℬ) (m : E ⟶ Y),
        (m ≫ a = m ≫ b) ×'
        (∀ {W : ℬ} (s t : W ⟶ E), s ≫ m = t ≫ m → s = t) ×'
        Σ' θE : A ⟶ G E, θE ≫ hG.map m = k := by
    intro Y Z a b k hk
    let wlim := hc.hasLimit (wppDiagObj a b)
    let m : wlim.cone.apex ⟶ Y := wlim.cone.π ⟨.src⟩
    have hmsrc : m = wlim.cone.π ⟨.src⟩ := rfl
    -- m ≫ a = tgt-leg, m ≫ b = tgt-leg
    have hma : m ≫ a = wlim.cone.π ⟨.tgt⟩ :=
      wlim.cone.nat (⟨.arr0⟩ : (⟨.src⟩ : WPPv) ⟶ ⟨.tgt⟩)
    have hmb : m ≫ b = wlim.cone.π ⟨.tgt⟩ :=
      wlim.cone.nat (⟨.arr1⟩ : (⟨.src⟩ : WPPv) ⟶ ⟨.tgt⟩)
    have hmeq : m ≫ a = m ≫ b := hma.trans hmb.symm
    -- m monic: two maps agreeing after m lift the same cone
    have mMonic : ∀ {W : ℬ} (s t : W ⟶ wlim.cone.apex), s ≫ m = t ≫ m → s = t := by
      intro W s t hst
      let cc : DiagCone (wppDiagObj a b) :=
        { apex := W
          π := fun X => match X with | ⟨.src⟩ => s ≫ m | ⟨.tgt⟩ => (s ≫ m) ≫ a
          nat := by
            rintro ⟨X⟩ ⟨Yy⟩ ⟨x⟩
            cases x with
            | idS  => exact Cat.comp_id _
            | idT  => exact Cat.comp_id _
            | arr0 => rfl
            | arr1 =>
                show (s ≫ m) ≫ b = (s ≫ m) ≫ a
                rw [Cat.assoc, Cat.assoc, ← hmeq] }
      have hs : s = wlim.lift cc := wlim.uniq cc s (by
        rintro ⟨X⟩; cases X
        · show s ≫ m = s ≫ m; rfl
        · show s ≫ wlim.cone.π ⟨.tgt⟩ = (s ≫ m) ≫ a
          rw [← hma, Cat.assoc])
      have ht : t = wlim.lift cc := wlim.uniq cc t (by
        rintro ⟨X⟩; cases X
        · show t ≫ m = s ≫ m; exact hst.symm
        · show t ≫ wlim.cone.π ⟨.tgt⟩ = (s ≫ m) ≫ a
          rw [← hma, ← Cat.assoc, ← hst, Cat.assoc])
      rw [hs, ht]
    -- continuity: the cone {k at src, k≫Ga at tgt} over G∘D factors uniquely
    let glegs : (Z : WPPv) → A ⟶ G (wppDiagObj a b Z) :=
      fun Z => match Z with | ⟨.src⟩ => k | ⟨.tgt⟩ => k ≫ hG.map a
    have gnat : ∀ {X Yy : WPPv} (x : X ⟶ Yy),
        glegs X ≫ hG.map ((wppDiagFunctor a b).map x) = glegs Yy := by
      rintro ⟨X⟩ ⟨Yy⟩ ⟨x⟩
      cases x with
      | idS => show k ≫ hG.map (Cat.id Y) = k; rw [hG.map_id, Cat.comp_id]
      | idT => show (k ≫ hG.map a) ≫ hG.map (Cat.id Z) = k ≫ hG.map a
               rw [hG.map_id, Cat.comp_id]
      | arr0 => show k ≫ hG.map a = k ≫ hG.map a; rfl
      | arr1 => show k ≫ hG.map b = k ≫ hG.map a; rw [hk]
    let θex := hcont wlim A glegs gnat
    let θE : A ⟶ G wlim.cone.apex := θex.choose
    have hθfac : θE ≫ hG.map m = k := θex.choose_spec.1 ⟨.src⟩
    exact ⟨wlim.cone.apex, m, hmeq, mMonic, θE, hθfac⟩
  -- ── θ : A ⟶ G R, the representing element, via eqFactor on the wide-equalizer pair ──
  -- Build `Qprod := ∏ₖ P` AS A LIMIT (so continuity gives joint-monicity of `{G qproj_k}`),
  -- with `fmap, gmap : P ⟶ Qprod` the family-tuple and the constant-id tuple.
  let Kconst : K → ℬ := fun _ => P
  letI : Cat.{v} K := discCat82
  letI : Functor Kconst := discreteFunctor Kconst
  let Qlim := hc.hasLimit Kconst
  let Qprod : ℬ := Qlim.cone.apex
  let qproj : (k : K) → Qprod ⟶ P := Qlim.cone.π
  -- continuity ⟹ `{G qproj_k}` jointly monic
  have qprojGMonic : ∀ {X : 𝒜} (u v : X ⟶ G Qprod),
      (∀ k, u ≫ hG.map (qproj k) = v ≫ hG.map (qproj k)) → u = v := by
    intro X u v huv
    have hnatU : ∀ {i j : K} (x : i ⟶ j),
        (u ≫ hG.map (qproj i)) ≫ hG.map ((discreteFunctor Kconst).map x) = u ≫ hG.map (qproj j) := by
      intro i j x; obtain ⟨⟨hij⟩⟩ := x; subst hij
      show (u ≫ hG.map (qproj i)) ≫ hG.map ((discreteFunctor Kconst).map (Cat.id i)) = u ≫ hG.map (qproj i)
      rw [(discreteFunctor Kconst).map_id, hG.map_id, Cat.comp_id]
    obtain ⟨_, _, huniq⟩ := hcont Qlim X (fun k => u ≫ hG.map (qproj k)) hnatU
    have e1 := huniq u (fun _ => rfl)
    have e2 := huniq v (fun k => (huv k).symm)
    rw [e1, e2]
  -- the tuple maps via the limit's `lift` over discrete cones
  let fmap : P ⟶ Qprod := Qlim.lift (discreteCone Kconst P (fun (k : K) => k.1))
  let gmap : P ⟶ Qprod := Qlim.lift (discreteCone Kconst P (fun _ : K => Cat.id P))
  have hfproj : ∀ k, fmap ≫ qproj k = k.1 := fun k =>
    Qlim.fac (discreteCone Kconst P (fun (k : K) => k.1)) k
  have hgproj : ∀ k, gmap ≫ qproj k = Cat.id P := fun k =>
    Qlim.fac (discreteCone Kconst P (fun _ : K => Cat.id P)) k
  -- η equalizes `fmap, gmap` after `G`: post-compose with each `G qproj_k` and use `k ∈ K`.
  have hηfg : η ≫ hG.map fmap = η ≫ hG.map gmap := by
    apply qprojGMonic
    intro k
    rw [Cat.assoc, ← hG.map_comp, hfproj, Cat.assoc, ← hG.map_comp, hgproj, hG.map_id,
        Cat.comp_id, k.2]
  obtain ⟨E, m, hmeq, mMonic, θ, hθ⟩ := eqFactor fmap gmap η hηfg
  -- E with m : E ⟶ P, m ≫ fmap = m ≫ gmap, so m equalizes the family with id.
  have hmk : ∀ k : K, m ≫ k.1 = m := by
    intro k
    have hcong := congrArg (· ≫ qproj k) hmeq
    simp only at hcong
    rw [Cat.assoc, hfproj, Cat.assoc, hgproj, Cat.comp_id] at hcong
    exact hcong
  -- lift m through R, giving lm : E ⟶ R with lm ≫ r = m
  let lm : E ⟶ R := we.lift m hmk
  have hlm : lm ≫ r = m := we.fac m hmk
  -- representing element θR := θ ≫ G(lm)? No: we need element on R. Use η factors through G r.
  -- r ≫ fmap = r ≫ gmap (r equalizes the family with id), so η?  Actually build θR directly:
  -- η factors through G r since r is THE wide equalizer and η lies in its image via E.
  -- θ : A ⟶ G E with θ ≫ G m = η; and m = lm ≫ r, so (θ ≫ G lm) ≫ G r = η.
  let θR : A ⟶ G R := θ ≫ hG.map lm
  have hθR : θR ≫ hG.map r = η := by
    show (θ ≫ hG.map lm) ≫ hG.map r = η
    rw [Cat.assoc, ← hG.map_comp, hlm, hθ]
  -- ── assemble the InitialElement (R, θR) ──
  refine ⟨R, (InitialElement.represents (G := G) ⟨θR, ?_, ?_⟩)⟩
  · -- existence: every g : A ⟶ G B is θR ≫ G x
    intro B g
    obtain ⟨w, hw⟩ := weakInit g
    refine ⟨r ≫ w, ?_⟩
    rw [hG.map_comp, ← Cat.assoc, hθR, hw]
  · -- uniqueness: θR ≫ G x₁ = θR ≫ G x₂ → x₁ = x₂
    intro B x₁ x₂ hx
    -- equalize x₁, x₂ in ℬ; θR factors through it; pull back weak-initially; use we.spec + rMonic
    obtain ⟨E2, m2, hm2eq, m2Monic, θ2, hθ2⟩ := eqFactor x₁ x₂ θR hx
    -- m2 : E2 ⟶ R, m2 ≫ x₁ = m2 ≫ x₂, θ2 ≫ G m2 = θR
    -- (E2, θ2) is an A↓G-object; m2 ≫ r : E2 ⟶ P, with θ2 ≫ G(m2 ≫ r) = θR ≫ G r = η
    have hθ2r : θ2 ≫ hG.map (m2 ≫ r) = η := by
      rw [hG.map_comp, ← Cat.assoc, hθ2, hθR]
    -- weak-initiality: pick p : P ⟶ E2 with η ≫ G p = θ2
    obtain ⟨p, hp2⟩ := weakInit θ2
    -- e := p ≫ m2 ≫ r : P ⟶ P is an A↓G-endo: η ≫ G e = η
    let endo : P ⟶ P := p ≫ m2 ≫ r
    have hendo : η ≫ hG.map endo = η := by
      show η ≫ hG.map (p ≫ m2 ≫ r) = η
      rw [hG.map_comp, ← Cat.assoc, hp2, hθ2r]
    let kk : K := ⟨endo, hendo⟩
    -- wide-equalizer spec: r ≫ endo = r, i.e. r ≫ p ≫ m2 ≫ r = r = id ≫ r ⟹ (r≫p≫m2) = id (r monic)
    have hspec : r ≫ endo = r := we.spec kk
    have hsplit : (r ≫ p ≫ m2) ≫ r = Cat.id R ≫ r := by
      rw [Cat.id_comp, Cat.assoc, Cat.assoc]
      -- goal: r ≫ p ≫ m2 ≫ r = r, and p ≫ m2 ≫ r = endo
      show r ≫ (p ≫ m2 ≫ r) = r
      exact hspec
    have hsec : (r ≫ p ≫ m2) ≫ Cat.id R = Cat.id R := by
      have := rMonic (r ≫ p ≫ m2) (Cat.id R) hsplit
      rw [Cat.comp_id]; exact this
    -- so m2 is split epi with section (r ≫ p): (r≫p) ≫ m2 = id; hence x₁ = x₂
    have hsec2 : (r ≫ p) ≫ m2 = Cat.id R := by
      rw [Cat.comp_id] at hsec
      calc (r ≫ p) ≫ m2 = r ≫ p ≫ m2 := Cat.assoc _ _ _
        _ = Cat.id R := hsec
    calc x₁ = Cat.id R ≫ x₁ := (Cat.id_comp _).symm
      _ = ((r ≫ p) ≫ m2) ≫ x₁ := by rw [hsec2]
      _ = (r ≫ p) ≫ (m2 ≫ x₁) := Cat.assoc _ _ _
      _ = (r ≫ p) ≫ (m2 ≫ x₂) := by rw [hm2eq]
      _ = ((r ≫ p) ≫ m2) ≫ x₂ := (Cat.assoc _ _ _).symm
      _ = Cat.id R ≫ x₂ := by rw [hsec2]
      _ = x₂ := Cat.id_comp _


/-- §1.83 GENERAL ADJOINT FUNCTOR THEOREM. -/
theorem general_adjoint_functor_theorem
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [hG : Functor G]
    [Complete ℬ] :
    (∃ (F : 𝒜 → ℬ) (_hF : Functor F), Nonempty (F ⊣ G)) ↔
    (IsContinuous G ∧ Nonempty (PreAdjointFunctor G)) := by
  constructor
  · -- (⇒) EASY: a left adjoint is continuous and pre-adjoint (proved above).
    rintro ⟨F, hF, ⟨adj⟩⟩
    exact ⟨isContinuous_of_adjunction adj, ⟨preAdjointFunctor_of_adjunction adj⟩⟩
  · -- (⇐) HARD: continuous + pre-adjoint ⟹ left adjoint.  Via `adjunction_of_representability`
    -- the goal reduces to: for every `A`, the functor `(A, G(-))` is REPRESENTABLE (§1.817).
    -- That representing object is the terminal object of the category of elements
    -- `El(A, G(-))`, built by §1.834–§1.835: continuity ⟹ `El` has lower-bounds for every
    -- small diagram, pre-adjointness ⟹ `El` has a pre-coterminator, and completeness ⟹
    -- equalizers ⟹ idempotents split, so §1.835 produces the coterminator = representing
    -- object.  Only this representing-object construction remains (sharp blocker below).
    rintro ⟨hcont, ⟨pre⟩⟩
    refine ⟨?_, ?_, ?_⟩
    -- once a representing object is produced for every A, the left adjoint is assembled by
    -- the (now proven, axiom-free) bridge `adjunction_of_representability`:
    · exact fun A => (adjunction_of_representability G (gaft_representability hcont pre)).1 A
    · exact (adjunction_of_representability G (gaft_representability hcont pre)).2.1
    · exact ⟨(adjunction_of_representability G (gaft_representability hcont pre)).2.2⟩

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

/-- §1.83(10) — the EMBEDDING characterization (one direction, the one SAFT needs): in a category
    with all products, a cogenerating set `{Cᵢ}` makes every object `B` embeddable in a product of
    cogenerators.  Concretely the *evaluation* map into the product indexed by ALL maps `B → Cᵢ`,

      `eB := ⟨h⟩_{(i,h)} : B ⟶ ∏_{(i,h) : Σ i, (B ⟶ Cᵢ)} Cᵢ`,

    is monic: if `u ≫ eB = v ≫ eB` then `u ≫ h = v ≫ h` for every `h : B → Cᵢ` (read off the
    `(i,h)`-projection), so by collective faithfulness `u = v`.  No choice, no completeness. -/
theorem cogenerating_embeds_in_product {ℬ : Type u₁} [Cat.{v} ℬ] (hp : HasProducts ℬ)
    {I : Type v} {C : I → ℬ} (hcogen : IsCoGeneratingSet C) (B : ℬ) :
    Monic (hp.tupling (F := fun j : Σ i : I, (B ⟶ C i) => C j.1)
                     (fun j => j.2)) := by
  classical
  let eB := hp.tupling (F := fun j : Σ i : I, (B ⟶ C i) => C j.1) (fun j => j.2)
  intro X u v huv
  -- `(w ≫ eB) ≫ proj (i,h) = w ≫ h`, so equality after `eB` forces `u ≫ h = v ≫ h` for all `(i,h)`
  have key : ∀ (w : X ⟶ B) (j : Σ i : I, (B ⟶ C i)), (w ≫ eB) ≫ hp.proj j = w ≫ j.2 := by
    intro w j; dsimp only [eB]; rw [Cat.assoc, hp.tupling_fac]
  refine Classical.byContradiction (fun hne => ?_)
  obtain ⟨i, h, hh⟩ := hcogen u v hne
  apply hh
  have hu := key u ⟨i, h⟩
  have hv := key v ⟨i, h⟩
  have hproj : (u ≫ eB) ≫ hp.proj (⟨i, h⟩ : Σ i : I, (B ⟶ C i))
             = (v ≫ eB) ≫ hp.proj (⟨i, h⟩ : Σ i : I, (B ⟶ C i)) :=
    congrArg (· ≫ hp.proj (⟨i, h⟩ : Σ i : I, (B ⟶ C i))) huv
  rw [hu, hv] at hproj
  exact hproj

-- ---------------------------------------------------------------------------
-- Cospan (pullback) diagram and `G`-preserves-pullback factoring (SAFT infra)
-- ---------------------------------------------------------------------------

/-- Walking cospan: three objects `lft, rgt, mid` with arrows `lft → mid ← rgt`. -/
private inductive Cospan : Type where | lft | rgt | mid

/-- Morphisms of the walking cospan (only identities and the two legs into `mid`). -/
private inductive CospanHom : Cospan → Cospan → Type where
  | idL : CospanHom .lft .lft
  | idR : CospanHom .rgt .rgt
  | idM : CospanHom .mid .mid
  | inl : CospanHom .lft .mid
  | inr : CospanHom .rgt .mid

private def cospanComp : {X Y Z : Cospan} → CospanHom X Y → CospanHom Y Z → CospanHom X Z
  | _, _, _, .idL, g => g
  | _, _, _, .idR, g => g
  | _, _, _, .idM, g => g
  | _, _, _, f, .idM => f

private instance cospanCat : Cat.{0} Cospan where
  Hom := CospanHom
  id  := fun | .lft => .idL | .rgt => .idR | .mid => .idM
  comp := cospanComp
  id_comp := by intro X Y f; cases f <;> rfl
  comp_id := by intro X Y f; cases f <;> rfl
  assoc := by intro W X Y Z f g h; cases f <;> cases g <;> cases h <;> rfl

/-- Cospan shape lifted to universe `v` (a legal `Complete` diagram shape). -/
private abbrev Cospanv : Type v := ULift.{v} Cospan

private instance cospanCatV : Cat.{v} Cospanv where
  Hom X Y    := ULift.{v} (CospanHom X.down Y.down)
  id X       := ⟨cospanCat.id X.down⟩
  comp f g   := ⟨cospanComp f.down g.down⟩
  id_comp := by rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩; cases f <;> rfl
  comp_id := by rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩; cases f <;> rfl
  assoc := by
    rintro ⟨W⟩ ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩ ⟨h⟩
    cases f <;> cases g <;> cases h <;> rfl

/-- The cospan diagram for `w : L ⟶ M ← B : eB`: `lft ↦ L`, `rgt ↦ B`, `mid ↦ M`. -/
private def cospanDiagObj {ℬ : Type u₁} [Cat.{v} ℬ] {L B M : ℬ} (_w : L ⟶ M) (_eB : B ⟶ M) :
    Cospanv → ℬ
  | ⟨.lft⟩ => L
  | ⟨.rgt⟩ => B
  | ⟨.mid⟩ => M

private def cospanDiagMap {ℬ : Type u₁} [Cat.{v} ℬ] {L B M : ℬ} (w : L ⟶ M) (eB : B ⟶ M) :
    {X Y : Cospanv} → (X ⟶ Y) → (cospanDiagObj w eB X ⟶ cospanDiagObj w eB Y)
  | ⟨.lft⟩, ⟨.lft⟩, _ => Cat.id L
  | ⟨.rgt⟩, ⟨.rgt⟩, _ => Cat.id B
  | ⟨.mid⟩, ⟨.mid⟩, _ => Cat.id M
  | ⟨.lft⟩, ⟨.mid⟩, ⟨.inl⟩ => w
  | ⟨.rgt⟩, ⟨.mid⟩, ⟨.inr⟩ => eB

private instance cospanDiagFunctor {ℬ : Type u₁} [Cat.{v} ℬ] {L B M : ℬ}
    (w : L ⟶ M) (eB : B ⟶ M) : Functor (cospanDiagObj w eB) where
  map := cospanDiagMap w eB
  map_id := by rintro ⟨X⟩; cases X <;> rfl
  map_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨p⟩ ⟨q⟩
    cases p <;> cases q <;>
      first
        | rfl
        | exact (Cat.id_comp _).symm
        | exact (Cat.comp_id _).symm

/-- §1.838 helper — `G` continuous ⟹ `G` preserves the pullback of `eB` (mono) along `w`.
    From a complete `ℬ` build the pullback `S` of the cospan `L —w→ M ←eB— B` as a limit; its
    `lft`-leg `πL : S ⟶ L` is monic (pullback of the mono `eB`).  Given a pair `(η : A ⟶ G L,
    f : A ⟶ G B)` with `η ≫ G w = f ≫ G eB`, continuity makes it factor uniquely: there is
    `θ : A ⟶ G S` with `θ ≫ G πL = η` and `θ ≫ G πB = f`. -/
private noncomputable def gPullbackFactor {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    {G : ℬ → 𝒜} [hG : Functor G] [hc : Complete ℬ] (hcont : IsContinuous G)
    {A : 𝒜} {L B M : ℬ} (w : L ⟶ M) (eB : B ⟶ M) (heB : Monic eB)
    (η : A ⟶ G L) (f : A ⟶ G B) (hsq : η ≫ hG.map w = f ≫ hG.map eB) :
    Σ' (S : ℬ) (πL : S ⟶ L) (πB : S ⟶ B),
      (∀ {W : ℬ} (s t : W ⟶ S), s ≫ πL = t ≫ πL → s = t) ×'
      Σ' θ : A ⟶ G S, (θ ≫ hG.map πL = η) ×' (θ ≫ hG.map πB = f) := by
  classical
  let lim := hc.hasLimit (cospanDiagObj w eB)
  let S : ℬ := lim.cone.apex
  let πL : S ⟶ L := lim.cone.π ⟨.lft⟩
  let πB : S ⟶ B := lim.cone.π ⟨.rgt⟩
  -- the square commutes: πL ≫ w = mid-leg = πB ≫ eB
  have hLmid : πL ≫ w = lim.cone.π ⟨.mid⟩ :=
    lim.cone.nat (⟨.inl⟩ : (⟨.lft⟩ : Cospanv) ⟶ ⟨.mid⟩)
  have hRmid : πB ≫ eB = lim.cone.π ⟨.mid⟩ :=
    lim.cone.nat (⟨.inr⟩ : (⟨.rgt⟩ : Cospanv) ⟶ ⟨.mid⟩)
  have hcomm : πL ≫ w = πB ≫ eB := hLmid.trans hRmid.symm
  -- πL monic: two maps agreeing after πL also agree after πB (eB monic), hence lift the same cone.
  have πLMonic : ∀ {W : ℬ} (s t : W ⟶ S), s ≫ πL = t ≫ πL → s = t := by
    intro W s t hst
    -- s ≫ πB = t ≫ πB from (s≫πL)≫w = (t≫πL)≫w and eB monic
    have hsB : s ≫ πB = t ≫ πB := by
      apply heB
      calc (s ≫ πB) ≫ eB = s ≫ (πB ≫ eB) := Cat.assoc _ _ _
        _ = s ≫ (πL ≫ w) := by rw [hcomm]
        _ = (s ≫ πL) ≫ w := (Cat.assoc _ _ _).symm
        _ = (t ≫ πL) ≫ w := by rw [hst]
        _ = t ≫ (πL ≫ w) := Cat.assoc _ _ _
        _ = t ≫ (πB ≫ eB) := by rw [hcomm]
        _ = (t ≫ πB) ≫ eB := (Cat.assoc _ _ _).symm
    let cc : DiagCone (cospanDiagObj w eB) :=
      { apex := W
        π := fun X => match X with
          | ⟨.lft⟩ => s ≫ πL | ⟨.rgt⟩ => s ≫ πB | ⟨.mid⟩ => (s ≫ πL) ≫ w
        nat := by
          rintro ⟨X⟩ ⟨Yy⟩ ⟨x⟩
          cases x with
          | idL => exact Cat.comp_id _
          | idR => exact Cat.comp_id _
          | idM => exact Cat.comp_id _
          | inl => rfl
          | inr =>
              show (s ≫ πB) ≫ eB = (s ≫ πL) ≫ w
              rw [Cat.assoc, Cat.assoc, hcomm] }
    have hs : s = lim.lift cc := lim.uniq cc s (by
      rintro ⟨X⟩; cases X
      · rfl
      · rfl
      · show s ≫ lim.cone.π ⟨.mid⟩ = (s ≫ πL) ≫ w
        rw [← hLmid, Cat.assoc])
    have ht : t = lim.lift cc := lim.uniq cc t (by
      rintro ⟨X⟩; cases X
      · exact hst.symm
      · exact hsB.symm
      · show t ≫ lim.cone.π ⟨.mid⟩ = (s ≫ πL) ≫ w
        rw [← hLmid, ← Cat.assoc, ← hst, Cat.assoc])
    rw [hs, ht]
  -- continuity: the cone {η at lft, f at rgt, η≫Gw at mid} over G∘D factors uniquely
  let glegs : (Z : Cospanv) → A ⟶ G (cospanDiagObj w eB Z) :=
    fun Z => match Z with
      | ⟨.lft⟩ => η | ⟨.rgt⟩ => f | ⟨.mid⟩ => η ≫ hG.map w
  have gnat : ∀ {X Yy : Cospanv} (x : X ⟶ Yy),
      glegs X ≫ hG.map ((cospanDiagFunctor w eB).map x) = glegs Yy := by
    rintro ⟨X⟩ ⟨Yy⟩ ⟨x⟩
    cases x with
    | idL => show η ≫ hG.map (Cat.id L) = η; rw [hG.map_id, Cat.comp_id]
    | idR => show f ≫ hG.map (Cat.id B) = f; rw [hG.map_id, Cat.comp_id]
    | idM => show (η ≫ hG.map w) ≫ hG.map (Cat.id M) = η ≫ hG.map w
             rw [hG.map_id, Cat.comp_id]
    | inl => show η ≫ hG.map w = η ≫ hG.map w; rfl
    | inr => show f ≫ hG.map eB = η ≫ hG.map w; rw [hsq]
  let θex := hcont lim A glegs gnat
  let θ : A ⟶ G S := θex.choose
  have hθL : θ ≫ hG.map πL = η := θex.choose_spec.1 ⟨.lft⟩
  have hθB : θ ≫ hG.map πB = f := θex.choose_spec.1 ⟨.rgt⟩
  exact ⟨S, πL, πB, πLMonic, θ, hθL, hθB⟩

/-- §1.838 — the SOLUTION SET (pre-adjoint family) for SAFT.  For each `A`, index the family by
    `Σ (k : WPidx PA), (A ⟶ G (repr k).dom)` where `PA := ∏_{j : Σ i,(A⟶G(Cᵢ))} Cⱼ.₁` is the
    product of cogenerators indexed by ALL maps `A → G(Cᵢ)`, and `repr` enumerates (well-powered)
    the subobjects of `PA`.  Cofinality of `f : A ⟶ G B`: embed `B ↪ Q B` into a product of
    cogenerators (`cogenerating_embeds_in_product`), build the comparison `w : PA ⟶ Q B`, check the
    square `η ≫ G w = f ≫ G eB` componentwise (the `G`-images of the `Q B`-projections are jointly
    monic by continuity), pull back the mono `eB` along `w` (`gPullbackFactor`) to a subobject
    `S ↪ PA` with a factoring element `θ : A ⟶ G S`, then transport along the well-powered
    representative iso `S ≅ (repr k).dom`. -/
private noncomputable def saft_preadjoint
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    {G : ℬ → 𝒜} [hG : Functor G] [hc : Complete ℬ] [WellPowered ℬ]
    {I : Type v} (C : I → ℬ) (hcogen : IsCoGeneratingSet C) (hcont : IsContinuous G) :
    PreAdjointFunctor G where
  preAdj A := by
    classical
    let hp : HasProducts ℬ := complete_hasProducts hc
    -- ── PA := product of cogenerators indexed by all maps A → G(Cᵢ), built AS A LIMIT ──
    let J : Type v := Σ i : I, (A ⟶ G (C i))
    letI : Cat.{v} J := discCat82
    let Jobj : J → ℬ := fun j => C j.1
    letI Jfun : Functor Jobj := discreteFunctor Jobj
    let dlim := hc.hasLimit Jobj
    let PA : ℬ := dlim.cone.apex
    let projPA : (j : J) → PA ⟶ C j.1 := dlim.cone.π
    -- canonical element η : A ⟶ G PA with η ≫ G(projPA j) = j.2
    have hmapsnat : ∀ {i j : J} (x : i ⟶ j),
        (i.2 : A ⟶ G (Jobj i)) ≫ hG.map (Jfun.map x) = (j.2 : A ⟶ G (Jobj j)) := by
      intro i j x; obtain ⟨⟨hij⟩⟩ := x; subst hij
      show (i.2 : A ⟶ G (Jobj i)) ≫ hG.map (Jfun.map (Cat.id i)) = i.2
      rw [Jfun.map_id, hG.map_id, Cat.comp_id]
    let ηex := hcont dlim A (fun j : J => (j.2 : A ⟶ G (C j.1))) hmapsnat
    let η : A ⟶ G PA := ηex.choose
    have hηfac : ∀ j : J, η ≫ hG.map (projPA j) = j.2 := ηex.choose_spec.1
    -- ── well-powered enumeration of subobjects of PA (data extracted via choice) ──
    let wp := WellPowered.small (ℬ := ℬ) PA
    let WPidx : Type v := wp.choose
    let reprPA : WPidx → Subobject ℬ PA := wp.choose_spec.choose
    have reprCov : ∀ s : Subobject ℬ PA, ∃ i : WPidx, SubobjectIso s (reprPA i) :=
      wp.choose_spec.choose_spec
    -- ── joint monicity of `{G(hp.proj j')}` on any product `Q := ∏ⱼ' F j'` (continuity) ──
    have qGMonic : ∀ {Idx : Type v} (F : Idx → ℬ) {X : 𝒜}
        (u v : X ⟶ G (hp.prodObj F)),
        (∀ j', u ≫ hG.map (hp.proj j') = v ≫ hG.map (hp.proj j')) → u = v := by
      intro Idx F X u v huv
      letI : Cat.{v} Idx := discCat82
      letI : Functor F := discreteFunctor F
      let qlim := hc.hasLimit F
      -- hp.proj j' on `complete_hasProducts` IS `qlim.cone.π j'` definitionally
      have hnatU : ∀ {i j : Idx} (x : i ⟶ j),
          (u ≫ hG.map (qlim.cone.π i)) ≫ hG.map ((discreteFunctor F).map x)
            = u ≫ hG.map (qlim.cone.π j) := by
        intro i j x; obtain ⟨⟨hij⟩⟩ := x; subst hij
        show (u ≫ hG.map (qlim.cone.π i)) ≫ hG.map ((discreteFunctor F).map (Cat.id i))
            = u ≫ hG.map (qlim.cone.π i)
        rw [(discreteFunctor F).map_id, hG.map_id, Cat.comp_id]
      obtain ⟨_, _, huniq⟩ := hcont qlim X (fun j => u ≫ hG.map (qlim.cone.π j)) hnatU
      have e1 := huniq u (fun _ => rfl)
      have e2 := huniq v (fun j => (huv j).symm)
      rw [e1, e2]
    -- ── assemble the pre-adjoint family ──
    refine
      { I       := Σ k : WPidx, (A ⟶ G (reprPA k).dom)
        obj     := fun p => (reprPA p.1).dom
        maps    := fun p => p.2
        cofinal := ?_ }
    intro B f
    -- embed B into the product Q B of cogenerators over all maps B → Cᵢ
    let eB : B ⟶ hp.prodObj (fun j' : Σ i : I, (B ⟶ C i) => C j'.1) :=
      hp.tupling (fun j' => j'.2)
    have heB : Monic eB := cogenerating_embeds_in_product hp hcogen B
    -- comparison map w : PA ⟶ Q B, w ≫ projQ (i,h) = projPA ⟨i, f ≫ G h⟩
    let w : PA ⟶ hp.prodObj (fun j' : Σ i : I, (B ⟶ C i) => C j'.1) :=
      hp.tupling (fun j' => projPA ⟨j'.1, f ≫ hG.map j'.2⟩)
    have hwproj : ∀ j' : Σ i : I, (B ⟶ C i),
        w ≫ hp.proj j' = projPA ⟨j'.1, f ≫ hG.map j'.2⟩ := fun j' => hp.tupling_fac _ _
    have heBproj : ∀ j' : Σ i : I, (B ⟶ C i), eB ≫ hp.proj j' = j'.2 := fun j' => hp.tupling_fac _ _
    -- square: η ≫ G w = f ≫ G eB (check componentwise on `{G projQ}`)
    have hsq : η ≫ hG.map w = f ≫ hG.map eB := by
      apply qGMonic (fun j' : Σ i : I, (B ⟶ C i) => C j'.1)
      intro j'
      calc (η ≫ hG.map w) ≫ hG.map (hp.proj j')
          = η ≫ hG.map (w ≫ hp.proj j') := by rw [Cat.assoc, ← hG.map_comp]
        _ = η ≫ hG.map (projPA ⟨j'.1, f ≫ hG.map j'.2⟩) := by rw [hwproj]
        _ = (f ≫ hG.map j'.2 : A ⟶ G (C j'.1)) := hηfac ⟨j'.1, f ≫ hG.map j'.2⟩
        _ = f ≫ hG.map (eB ≫ hp.proj j') := by rw [heBproj]
        _ = (f ≫ hG.map eB) ≫ hG.map (hp.proj j') := by rw [hG.map_comp, Cat.assoc]
    -- pull back eB (mono) along w; get S ↪ PA and the factoring element θ
    obtain ⟨S, πP, πB, πPMono, θ, hθP, hθB⟩ := gPullbackFactor hcont w eB heB η f hsq
    -- S as a subobject of PA, located in the well-powered enumeration
    let sub : Subobject ℬ PA := ⟨S, πP, fun {W} s t h => πPMono s t h⟩
    obtain ⟨k, i₀, hi₀iso, hi₀arr⟩ := reprCov sub
    obtain ⟨g, hg1, hg2⟩ := hi₀iso
    -- index ⟨k, θ ≫ G i₀⟩, with member map `x := g ≫ πB : (reprPA k).dom ⟶ B`
    refine ⟨⟨k, θ ≫ hG.map i₀⟩, g ≫ πB, ?_⟩
    -- (θ ≫ G i₀) ≫ G(g ≫ πB) = θ ≫ G((i₀ ≫ g) ≫ πB) = θ ≫ G πB = f
    calc (θ ≫ hG.map i₀) ≫ hG.map (g ≫ πB)
        = θ ≫ hG.map (i₀ ≫ g ≫ πB) := by rw [Cat.assoc, ← hG.map_comp, hG.map_comp]
      _ = θ ≫ hG.map ((i₀ ≫ g) ≫ πB) := by rw [Cat.assoc]
      _ = θ ≫ hG.map (Cat.id S ≫ πB) := by rw [hg1]
      _ = θ ≫ hG.map πB := by rw [Cat.id_comp]
      _ = f := hθB

/-- §1.83(10) (the heart of the SAFT): for a *continuous* `G` out of a *complete*,
    *well-powered* `ℬ` with a *cogenerating set* `C`, the functor `(A, G(-))` is representable for
    every `A`.  Proved by building the SOLUTION SET (`saft_preadjoint`) — the minimal-subobject /
    cogenerating-set pre-adjoint family — and feeding it to the proven `gaft_representability`
    engine (solution set + product + wide equalizer ⟹ initial element ⟹ representing object). -/
private noncomputable def saft_representability
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    {G : ℬ → 𝒜} [hG : Functor G] [Complete ℬ] [WellPowered ℬ]
    {I : Type v} (C : I → ℬ) (hcogen : IsCoGeneratingSet C)
    (hcont : IsContinuous G) :
    ∀ A : 𝒜, Σ R : ℬ, RepresentedBy G A R :=
  gaft_representability hcont (saft_preadjoint C hcogen hcont)

/-- §1.83(10) SPECIAL ADJOINT FUNCTOR THEOREM:
    If ℬ is complete, well-powered and has a cogenerating set,
    then every continuous G : ℬ → 𝒜 (𝒜 locally small) has a left adjoint. -/
theorem special_adjoint_functor_theorem
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [Functor G]
    [Complete ℬ] [WellPowered ℬ]
    {I : Type v} (C : I → ℬ) (hcogen : IsCoGeneratingSet C)
    (hcont : IsContinuous G) :
    ∃ (F : 𝒜 → ℬ) (_hF : Functor F), Nonempty (F ⊣ G) := by
  -- once `(A, G(-))` is representable for every `A`, assemble the adjoint via the proven bridge.
  refine ⟨?_, ?_, ?_⟩
  · exact fun A => (adjunction_of_representability G (saft_representability C hcogen hcont)).1 A
  · exact (adjunction_of_representability G (saft_representability C hcogen hcont)).2.1
  · exact ⟨(adjunction_of_representability G (saft_representability C hcogen hcont)).2.2⟩

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

/-- An idempotent `e : B ⟶ B` (i.e. `e ≫ e = e`) SPLITS if it factors as `r ≫ s`
    through some `C` with `s ≫ r = id` (§1.281; same content as `S1_39.SplitIdempotent`,
    restated locally to avoid importing the heavy `S1_39` chain). -/
def IdempotentSplits {ℬ : Type u₁} [Cat.{v} ℬ] {B : ℬ} (e : B ⟶ B) : Prop :=
  e ≫ e = e → ∃ (C : ℬ) (r : B ⟶ C) (s : C ⟶ B), r ≫ s = e ∧ s ≫ r = Cat.id C

/-- ℬ has the property that ALL idempotents split (§1.281). Required by §1.831/§1.835:
    `more_general_adjoint_functor_theorem` is FALSE without it (Freyd §1.836 gives an explicit
    counterexample — the formal idempotent-splitting embedding is uniformly continuous and
    pre-adjoint yet has no left adjoint). -/
def IdempotentsSplit (ℬ : Type u₁) [Cat.{v} ℬ] : Prop :=
  ∀ {B : ℬ} (e : B ⟶ B), IdempotentSplits e

-- ---------------------------------------------------------------------------
-- Wide-fork shape (for the §1.835 weak wide-equalizer via pre-limit + UC)
-- ---------------------------------------------------------------------------

/-! The MGAFT must "weakly equalize" a small family `e : K → (P ⟶ P)` against the
    identity — i.e. find a map `q : Q ⟶ P` with `q ≫ e k = q` for every `k`, factoring a
    given element.  Under `PreComplete` no genuine wide equalizer exists, so we model it as a
    *cone* over a wide-parallel-pair diagram and apply `IsUniformlyContinuous` to a pre-limit.

    The shape `WFork` has two objects `src, tgt` and arrows `src → tgt` indexed by `Option K`:
    `none` carries the identity `id_P` (forcing the two legs equal), `some k` carries `e k`. -/

private inductive WForkObj : Type where | src | tgt

private inductive WForkHom (K : Type v) : WForkObj → WForkObj → Type v where
  | idS : WForkHom K .src .src
  | idT : WForkHom K .tgt .tgt
  | arr : Option K → WForkHom K .src .tgt

private def wforkComp {K : Type v} :
    {X Y Z : WForkObj} → WForkHom K X Y → WForkHom K Y Z → WForkHom K X Z
  | _, _, _, .idS, g => g
  | _, _, _, f, .idT => f

private abbrev WForkv (_K : Type v) : Type v := ULift.{v} WForkObj

private instance wforkCat (K : Type v) : Cat.{v} (WForkv K) where
  Hom X Y  := WForkHom K X.down Y.down
  id X     := match X.down with | .src => .idS | .tgt => .idT
  comp f g := wforkComp f g
  id_comp  := by rintro ⟨X⟩ ⟨Y⟩ f; cases f <;> rfl
  comp_id  := by rintro ⟨X⟩ ⟨Y⟩ f; cases f <;> rfl
  assoc    := by rintro ⟨W⟩ ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f g h; cases f <;> cases g <;> cases h <;> rfl

/-- Wide-fork diagram for `e : K → (P ⟶ P)`: `src ↦ P`, `tgt ↦ P`, `arr none ↦ id_P`,
    `arr (some k) ↦ e k`. -/
private def wforkDiagObj {ℬ : Type u₁} [Cat.{v} ℬ] {P : ℬ} {K : Type v}
    (_e : K → (P ⟶ P)) : WForkv K → ℬ
  | ⟨.src⟩ => P
  | ⟨.tgt⟩ => P

private def wforkDiagMap {ℬ : Type u₁} [Cat.{v} ℬ] {P : ℬ} {K : Type v}
    (e : K → (P ⟶ P)) :
    {X Y : WForkv K} → (X ⟶ Y) → (wforkDiagObj e X ⟶ wforkDiagObj e Y)
  | ⟨.src⟩, ⟨.src⟩, _ => Cat.id P
  | ⟨.tgt⟩, ⟨.tgt⟩, _ => Cat.id P
  | ⟨.src⟩, ⟨.tgt⟩, .arr none => Cat.id P
  | ⟨.src⟩, ⟨.tgt⟩, .arr (some k) => e k

private instance wforkDiagFunctor {ℬ : Type u₁} [Cat.{v} ℬ] {P : ℬ} {K : Type v}
    (e : K → (P ⟶ P)) : Functor (wforkDiagObj e) where
  map := wforkDiagMap e
  map_id := by rintro ⟨X⟩; cases X <;> rfl
  map_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ p q
    cases p <;> cases q <;>
      first
        | rfl
        | exact (Cat.id_comp _).symm
        | exact (Cat.comp_id _).symm

/-- §1.835 (the heart of the MGAFT): for a *uniformly continuous* and *pre-adjoint* `G` out of
    a *pre-complete* `ℬ` in which *idempotents split*, the functor `(A, G(-))` is representable
    for every `A`.

    Freyd's argument (§1.835), made constructive:

    * (weak initiality)  Pre-adjointness gives a solution set `{(obj i, maps i)}` for `A`.  Form
      its discrete pre-limit (`PreComplete`); uniform continuity makes the `G`-image cofinal,
      producing `(P, η)` with `η ≫ G(proj i) = maps i`.  Pre-adjoint cofinality then makes
      `(P, η)` *weakly initial* in `El(A,G(-))`: every `g : A ⟶ G B` is `η ≫ G w` for some `w`.

    * (idempotent)  Let `M := {e : P ⟶ P // η ≫ G e = η}` be the endos fixing `η`.  Weakly
      equalize the whole family `M` against `id_P` via a *wide-fork* pre-limit + uniform
      continuity: a `q : Q ⟶ P` with `q ≫ e = q` for every `e ∈ M`, and an element `η_Q` with
      `η_Q ≫ G q = η`.  Weak initiality factors `η_Q` as `η ≫ G s = η_Q`; then `e₀ := s ≫ q`
      satisfies `η ≫ G e₀ = η` (so `e₀ ∈ M`) and `e₀ ≫ e = e₀` for every `e ∈ M` (since
      `q ≫ e = q`).  In particular `e₀ ≫ e₀ = e₀`: `e₀` is *idempotent*.

    * (split ⟹ initial)  `IdempotentsSplit` splits `e₀ = ρ ≫ σ`, `σ ≫ ρ = id_R`.  Then
      `(R, θ_R)` with `θ_R := η ≫ G ρ` is an INITIAL element: `θ_R ≫ G σ = η`; existence factors
      through weak initiality; uniqueness uses `σ ≫ e = σ` for every `e ∈ M` (from `σ ≫ ρ = id`
      and `e₀ ≫ e = e₀`) together with a *fresh* wide-fork weak-equalizer of each candidate pair.

    This is exactly where `IdempotentsSplit` is load-bearing (without it the theorem is false,
    §1.836): it is what cuts the weakly-initial `(P, η)` down to a genuine initial element. -/
private noncomputable def mgaft_representability
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    {G : ℬ → 𝒜} [hG : Functor G] [hpc : PreComplete ℬ]
    (hsplit : IdempotentsSplit ℬ)
    (huc : IsUniformlyContinuous G) (pre : PreAdjointFunctor G) :
    ∀ A : 𝒜, Σ R : ℬ, RepresentedBy G A R := by
  classical
  intro A
  -- ── solution set (pre-adjoint family) for A ──
  let pa := pre.preAdj A
  let I  : Type v := pa.I
  let obj : I → ℬ := pa.obj
  let maps : (i : I) → A ⟶ G (obj i) := pa.maps
  -- ── pre-limit of the discrete diagram `obj`; UC makes its G-image cofinal ──
  letI : Cat.{v} I := discCat82
  letI : Functor obj := discreteFunctor obj
  let pl := hpc.hasPreLimit obj
  have hmapsnat : ∀ {i j : I} (x : i ⟶ j),
      maps i ≫ hG.map (Functor.map x) = maps j := by
    intro i j x; obtain ⟨⟨hij⟩⟩ := x; subst hij
    show maps i ≫ hG.map (Functor.map (Cat.id i)) = maps i
    rw [Functor.map_id, hG.map_id, Cat.comp_id]
  let upl := uniformly_continuous_preserves_prelimits G huc pl A maps hmapsnat
  let j₀ : pl.J := upl.choose
  let η : A ⟶ G (pl.cones j₀).apex := upl.choose_spec.choose
  have hηfac : ∀ i, η ≫ hG.map ((pl.cones j₀).π i) = maps i := upl.choose_spec.choose_spec
  let P : ℬ := (pl.cones j₀).apex
  let proj : (i : I) → P ⟶ obj i := (pl.cones j₀).π
  -- weak initiality of (P, η): every g : A ⟶ G B factors as η ≫ G w
  have weakInit : ∀ {B : ℬ} (g : A ⟶ G B), ∃ w : P ⟶ B, η ≫ hG.map w = g := by
    intro B g
    obtain ⟨i, y, hy⟩ := pa.cofinal g
    refine ⟨proj i ≫ y, ?_⟩
    rw [hG.map_comp, ← Cat.assoc, hηfac i, hy]
  -- ── weak wide-equalizer of a family `e : K → (P ⟶ P)` (all fixing η) against id ──
  -- via the wide-fork pre-limit + uniform continuity.  Returns `q : Q ⟶ P` with `q ≫ e k = q`
  -- and a factoring element `η_Q` of `η`.
  let weakFork : ∀ (K : Type v) (e : K → (P ⟶ P)),
      (∀ k, η ≫ hG.map (e k) = η) →
      Σ' (Q : ℬ) (q : Q ⟶ P) (_ : ∀ k, q ≫ e k = q) (ηQ : A ⟶ G Q), ηQ ≫ hG.map q = η := by
    intro K e he
    letI := wforkCat K
    letI := wforkDiagFunctor e
    let pl' := hpc.hasPreLimit (wforkDiagObj e)
    -- the cone `{η at src, η at tgt}` over `G ∘ wforkDiag` (legs use `η`, naturally compatible
    -- because every diagram arrow maps to either `id_P` or some `e k` and `η ≫ G(e k) = η`).
    let glegs : (Z : WForkv K) → A ⟶ G (wforkDiagObj e Z) :=
      fun Z => match Z with | ⟨.src⟩ => η | ⟨.tgt⟩ => η
    have gnat : ∀ {X Y : WForkv K} (x : X ⟶ Y),
        glegs X ≫ hG.map ((wforkDiagFunctor e).map x) = glegs Y := by
      rintro ⟨X⟩ ⟨Y⟩ x
      cases x with
      | idS => show η ≫ hG.map (Cat.id P) = η; rw [hG.map_id, Cat.comp_id]
      | idT => show η ≫ hG.map (Cat.id P) = η; rw [hG.map_id, Cat.comp_id]
      | arr o => cases o with
        | none => show η ≫ hG.map (Cat.id P) = η; rw [hG.map_id, Cat.comp_id]
        | some k => exact he k
    let upl' := uniformly_continuous_preserves_prelimits G huc pl' A glegs gnat
    let j : pl'.J := upl'.choose
    let ηQ : A ⟶ G (pl'.cones j).apex := upl'.choose_spec.choose
    have hη : ∀ z, ηQ ≫ hG.map ((pl'.cones j).π z) = glegs z := upl'.choose_spec.choose_spec
    let Q : ℬ := (pl'.cones j).apex
    let qsrc : Q ⟶ P := (pl'.cones j).π ⟨.src⟩
    -- `qsrc ≫ e k = qsrc`: cone naturality on `arr (some k)` then on `arr none`.
    have hqe : ∀ k, qsrc ≫ e k = qsrc := by
      intro k
      have h1 : qsrc ≫ e k = (pl'.cones j).π ⟨.tgt⟩ :=
        (pl'.cones j).nat (WForkHom.arr (some k) : (⟨.src⟩ : WForkv K) ⟶ ⟨.tgt⟩)
      have h0 : qsrc ≫ Cat.id P = (pl'.cones j).π ⟨.tgt⟩ :=
        (pl'.cones j).nat (WForkHom.arr none : (⟨.src⟩ : WForkv K) ⟶ ⟨.tgt⟩)
      rw [Cat.comp_id] at h0
      rw [h1, ← h0]
    have hηQ : ηQ ≫ hG.map qsrc = η := hη ⟨.src⟩
    exact ⟨Q, qsrc, hqe, ηQ, hηQ⟩
  -- ── build the canonical idempotent `e₀` from the wide fork over ALL of `M` ──
  let M : Type v := { e : P ⟶ P // η ≫ hG.map e = η }
  obtain ⟨Q, q, hqM, ηQ, hηQ⟩ := weakFork M (fun m => m.1) (fun m => m.2)
  -- factor `ηQ` weakly-initially: η ≫ G s = ηQ
  let wiQ := weakInit ηQ
  let s : P ⟶ Q := wiQ.choose
  have hs : η ≫ hG.map s = ηQ := wiQ.choose_spec
  let e₀ : P ⟶ P := s ≫ q
  have he₀M : η ≫ hG.map e₀ = η := by
    show η ≫ hG.map (s ≫ q) = η
    rw [hG.map_comp, ← Cat.assoc, hs, hηQ]
  -- `e₀ ≫ m = e₀` for every `m ∈ M` (because `q ≫ m = q`)
  have he₀absorb : ∀ m : M, e₀ ≫ m.1 = e₀ := by
    intro m
    show (s ≫ q) ≫ m.1 = s ≫ q
    rw [Cat.assoc, hqM m]
  -- in particular `e₀` is idempotent (apply absorption to `e₀ ∈ M`)
  have hidem : e₀ ≫ e₀ = e₀ := he₀absorb ⟨e₀, he₀M⟩
  -- ── split the idempotent: e₀ = ρ ≫ σ, σ ≫ ρ = id_R ──
  let spl := hsplit e₀ hidem
  let R : ℬ := spl.choose
  let ρ : P ⟶ R := spl.choose_spec.choose
  let σ : R ⟶ P := spl.choose_spec.choose_spec.choose
  have hρσ : ρ ≫ σ = e₀ := spl.choose_spec.choose_spec.choose_spec.1
  have hσρ : σ ≫ ρ = Cat.id R := spl.choose_spec.choose_spec.choose_spec.2
  -- representing element θR := η ≫ G ρ ; then θR ≫ G σ = η
  let θR : A ⟶ G R := η ≫ hG.map ρ
  have hθRσ : θR ≫ hG.map σ = η := by
    show (η ≫ hG.map ρ) ≫ hG.map σ = η
    rw [Cat.assoc, ← hG.map_comp, hρσ, he₀M]
  -- key: `σ ≫ m = σ` for every `m ∈ M`  (σ ≫ ρ = id, e₀ ≫ m = e₀)
  have hσabsorb : ∀ m : M, σ ≫ m.1 = σ := by
    intro m
    calc σ ≫ m.1 = (σ ≫ ρ ≫ σ) ≫ m.1 := by rw [← Cat.assoc σ ρ σ, hσρ, Cat.id_comp]
      _ = σ ≫ (ρ ≫ σ) ≫ m.1 := by rw [Cat.assoc, Cat.assoc]
      _ = σ ≫ e₀ ≫ m.1 := by rw [hρσ]
      _ = σ ≫ e₀ := by rw [he₀absorb m]
      _ = σ ≫ ρ ≫ σ := by rw [hρσ]
      _ = σ := by rw [← Cat.assoc, hσρ, Cat.id_comp]
  -- ── assemble the InitialElement (R, θR) ──
  refine ⟨R, (InitialElement.represents (G := G) ⟨θR, ?_, ?_⟩)⟩
  · -- existence: every g : A ⟶ G B is θR ≫ G x, with x := σ ≫ w from weak initiality
    intro B g
    obtain ⟨w, hw⟩ := weakInit g
    refine ⟨σ ≫ w, ?_⟩
    rw [hG.map_comp, ← Cat.assoc, hθRσ, hw]
  · -- uniqueness: θR ≫ G x₁ = θR ≫ G x₂ → x₁ = x₂
    intro B x₁ x₂ hx
    -- reduce to legs out of P: yₖ := ρ ≫ xₖ, with η ≫ G y₁ = η ≫ G y₂ and xₖ = σ ≫ yₖ
    let y₁ : P ⟶ B := ρ ≫ x₁
    let y₂ : P ⟶ B := ρ ≫ x₂
    have hηy : η ≫ hG.map y₁ = η ≫ hG.map y₂ := by
      show η ≫ hG.map (ρ ≫ x₁) = η ≫ hG.map (ρ ≫ x₂)
      rw [hG.map_comp, hG.map_comp, ← Cat.assoc, ← Cat.assoc]
      show θR ≫ hG.map x₁ = θR ≫ hG.map x₂
      exact hx
    have hx₁ : x₁ = σ ≫ y₁ := by
      show x₁ = σ ≫ ρ ≫ x₁; rw [← Cat.assoc, hσρ, Cat.id_comp]
    have hx₂ : x₂ = σ ≫ y₂ := by
      show x₂ = σ ≫ ρ ≫ x₂; rw [← Cat.assoc, hσρ, Cat.id_comp]
    -- weakly equalize the pair `y₁, y₂` via a fresh wide fork over the single endo built from it
    -- First weak-equalize `y₁, y₂` directly: cone over the parallel-pair `{η, η ≫ G y₁}`.
    -- Build `m : E ⟶ P` with `m ≫ y₁ = m ≫ y₂` and `θE ≫ G m = η`, via UC on a wide fork.
    -- (We package the parallel pair as a wide fork with K = PUnit and a derived endo; instead,
    --  use the direct wide-fork over `M` already weak-equalizes — but `y₁,y₂` need a fresh one.)
    -- Construct via weakFork on the singleton family won't see y₁,y₂; instead build the
    -- endo `e₁ ∈ M` that absorbs the pair, exactly as for e₀ but tracking the WPP.
    -- Pre-limit of the parallel pair `y₁,y₂ : P ⟶ B`:
    letI := wppDiagFunctor y₁ y₂
    let plp := hpc.hasPreLimit (wppDiagObj y₁ y₂)
    let glegs : (Z : WPPv) → A ⟶ G (wppDiagObj y₁ y₂ Z) :=
      fun Z => match Z with | ⟨.src⟩ => η | ⟨.tgt⟩ => η ≫ hG.map y₁
    have gnat : ∀ {X Y : WPPv} (x : X ⟶ Y),
        glegs X ≫ hG.map ((wppDiagFunctor y₁ y₂).map x) = glegs Y := by
      rintro ⟨X⟩ ⟨Y⟩ ⟨x⟩
      cases x with
      | idS => show η ≫ hG.map (Cat.id P) = η; rw [hG.map_id, Cat.comp_id]
      | idT => show (η ≫ hG.map y₁) ≫ hG.map (Cat.id B) = η ≫ hG.map y₁
               rw [hG.map_id, Cat.comp_id]
      | arr0 => show η ≫ hG.map y₁ = η ≫ hG.map y₁; rfl
      | arr1 => show η ≫ hG.map y₂ = η ≫ hG.map y₁; rw [hηy]
    obtain ⟨jp, θE, hθE⟩ :=
      uniformly_continuous_preserves_prelimits G huc plp A glegs gnat
    let E : ℬ := (plp.cones jp).apex
    let m : E ⟶ P := (plp.cones jp).π ⟨.src⟩
    have hmsrc : θE ≫ hG.map m = η := hθE ⟨.src⟩
    have hmy : m ≫ y₁ = m ≫ y₂ := by
      have h1 : m ≫ y₁ = (plp.cones jp).π ⟨.tgt⟩ :=
        (plp.cones jp).nat (⟨.arr0⟩ : (⟨.src⟩ : WPPv) ⟶ ⟨.tgt⟩)
      have h2 : m ≫ y₂ = (plp.cones jp).π ⟨.tgt⟩ :=
        (plp.cones jp).nat (⟨.arr1⟩ : (⟨.src⟩ : WPPv) ⟶ ⟨.tgt⟩)
      rw [h1, h2]
    -- factor θE weakly-initially: η ≫ G s' = θE, then e₁ := s' ≫ m ∈ M with e₁ ≫ y₁ = e₁ ≫ y₂
    obtain ⟨s', hs'⟩ := weakInit θE
    let e₁ : P ⟶ P := s' ≫ m
    have he₁M : η ≫ hG.map e₁ = η := by
      show η ≫ hG.map (s' ≫ m) = η
      rw [hG.map_comp, ← Cat.assoc, hs', hmsrc]
    have he₁y : e₁ ≫ y₁ = e₁ ≫ y₂ := by
      show (s' ≫ m) ≫ y₁ = (s' ≫ m) ≫ y₂
      rw [Cat.assoc, Cat.assoc, hmy]
    -- σ ≫ e₁ = σ, so σ ≫ y₁ = σ ≫ y₂, hence x₁ = x₂
    have key : σ ≫ y₁ = σ ≫ y₂ := by
      calc σ ≫ y₁ = (σ ≫ e₁) ≫ y₁ := by rw [hσabsorb ⟨e₁, he₁M⟩]
        _ = σ ≫ (e₁ ≫ y₁) := Cat.assoc _ _ _
        _ = σ ≫ (e₁ ≫ y₂) := by rw [he₁y]
        _ = (σ ≫ e₁) ≫ y₂ := (Cat.assoc _ _ _).symm
        _ = σ ≫ y₂ := by rw [hσabsorb ⟨e₁, he₁M⟩]
    rw [hx₁, hx₂, key]

/-- §1.831 MORE GENERAL ADJOINT FUNCTOR THEOREM.
    If ℬ is locally small and *idempotents split* in ℬ, then G : ℬ → 𝒜 has a left adjoint
    iff it is uniformly continuous and pre-adjoint.  (The `IdempotentsSplit` hypothesis is
    essential — without it the theorem is false, Freyd §1.836.) -/
theorem more_general_adjoint_functor_theorem
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [hG : Functor G] [PreComplete ℬ] (hsplit : IdempotentsSplit ℬ) :
    (∃ (F : 𝒜 → ℬ) (_hF : Functor F), Nonempty (F ⊣ G)) ↔
    (IsUniformlyContinuous G ∧ Nonempty (PreAdjointFunctor G)) := by
  constructor
  · -- (⇒) EASY: a left adjoint is uniformly continuous and pre-adjoint (proved above).
    rintro ⟨F, hF, ⟨adj⟩⟩
    exact ⟨isUniformlyContinuous_of_adjunction adj, ⟨preAdjointFunctor_of_adjunction adj⟩⟩
  · -- (⇐) HARD: uniformly continuous + pre-adjoint ⟹ left adjoint.  Reduced (via the proven
    -- bridge `adjunction_of_representability`) to representability of `(A, G(-))` for every `A`.
    rintro ⟨huc, ⟨pre⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · exact fun A => (adjunction_of_representability G (mgaft_representability hsplit huc pre)).1 A
    · exact (adjunction_of_representability G (mgaft_representability hsplit huc pre)).2.1
    · exact ⟨(adjunction_of_representability G (mgaft_representability hsplit huc pre)).2.2⟩

-- ---------------------------------------------------------------------------
-- §1.837  Complete + pre-cocomplete → cocomplete
-- ---------------------------------------------------------------------------

/-! ### §1.837  A complete locally small category is cocomplete iff pre-cocomplete.

  The book: if ℬ is complete then for any D, Δ : ℬ → ℬ^D is continuous.
  Hence a complete category is cocomplete iff it is pre-cocomplete (§1.837). -/

/-- A PRE-COLIMIT for `D` is a `J`-indexed family of COCONES cofinal in all cocones:
    for every cocone `{D i → B}` some member cocone admits a (non-unique) factorization
    (the colimit dual of `HasPreLimit`).  The previous modeling reused `HasPreLimit`
    (cofinal *cones* = lower bounds), which is wrong-variance for colimits; this is the
    faithful dual. -/
structure HasPreColimit {𝒟 : Type u} [Cat.{v} 𝒟] {ℬ : Type u₁} [Cat.{v} ℬ]
    (D : 𝒟 → ℬ) [Functor D] where
  J       : Type v
  cocones : J → DiagCocone D
  cofinal : (c : DiagCocone D) →
              ∃ (j : J) (u : (cocones j).nadir ⟶ c.nadir), ∀ i, (cocones j).ι i ≫ u = c.ι i

/-- A category is PRE-COCOMPLETE if every small diagram has a pre-colimit (§1.837). -/
class PreCocomplete (ℬ : Type u₁) [Cat.{v} ℬ] where
  hasPreColimit : {𝒟 : Type v} → [Cat.{v} 𝒟] → (D : 𝒟 → ℬ) → [Functor D] → HasPreColimit D

/-- Every cocomplete category is pre-cocomplete (singleton pre-colimit from the colimit) — the
    EASY half of §1.837, dual to `complete_imp_preComplete`. -/
def cocomplete_imp_preCocomplete {ℬ : Type u₁} [Cat.{v} ℬ] (hc : Cocomplete ℬ) :
    PreCocomplete ℬ where
  hasPreColimit := fun {_} _ D _ =>
    let hl := hc.hasColimit D
    { J := PUnit.{v+1}
      cocones := fun _ => hl.cocone
      cofinal := fun c => ⟨PUnit.unit, hl.lift c, hl.fac c⟩ }

/-- §1.837 (hard half, the heart): a *complete* pre-cocomplete category is cocomplete.

    Freyd's argument: for any shape `D`, the diagonal `Δ : ℬ → ℬ^D` is continuous (because `ℬ`
    is complete, limits in `ℬ^D` are computed pointwise), and pre-cocompleteness says exactly
    that `Δ` is pre-adjoint; the More General Adjoint Functor Theorem then gives `Δ` a left
    adjoint = the colimit functor.

    PROVED here CONSTRUCTIVELY without functor categories, as the colimit-dual of the GAFT
    initial-element engine (everything stays inside `ℬ`):
    * `P := ∏ⱼ Nⱼ` over the pre-colimit nadirs `Nⱼ := (cocones j).nadir` (completeness ⟹ products);
      `κ i := ⟨(cocones j).ι i⟩ⱼ : D i ⟶ P` is a cocone, WEAKLY INITIAL among cocones (any cocone
      `c` is reached by `projⱼ ≫ uⱼ` for the cofinal index `j`).
    * cut to the genuine colimit by the WIDE EQUALIZER `r : R ⟶ P` of all cocone-endomorphisms
      `e : P ⟶ P` of `(P, κ)` (i.e. `κ i ≫ e = κ i`).  Each `κ i` equalizes the family with the
      identity (joint monicity of the product — no continuity needed), so it factors as
      `ιR i ≫ r = κ i`, giving the colimit cocone `(R, ιR)`; uniqueness of mediating maps follows
      exactly as in `gaft_representability` (equalize two candidates, factor `ιR` through it,
      pull back weakly-initially, use the wide-equalizer spec + monicity of `r`). -/
private noncomputable def cocomplete_of_complete_precocomplete
    {ℬ : Type u₁} [Cat.{v} ℬ] [hc : Complete ℬ] (hpc : PreCocomplete ℬ) :
    Cocomplete ℬ := by
  refine ⟨fun {𝒟} _ D hD => ?_⟩
  classical
  let heq : HasEqualizers ℬ := complete_hasEqualizers hc
  let hp  : HasProducts ℬ := complete_hasProducts hc
  -- ── pre-colimit data ──
  let pc := hpc.hasPreColimit D
  let J : Type v := pc.J
  let N : J → ℬ := fun j => (pc.cocones j).nadir
  -- ── P := product of the nadirs ──
  let P : ℬ := hp.prodObj N
  let κ : (i : 𝒟) → D i ⟶ P := fun i => hp.tupling (fun j => (pc.cocones j).ι i)
  have hκproj : ∀ i j, κ i ≫ hp.proj j = (pc.cocones j).ι i := fun i j => hp.tupling_fac _ _
  -- `(P, κ)` is a cocone over D
  have κnat : ∀ {i i' : 𝒟} (x : i ⟶ i'), hD.map x ≫ κ i' = κ i := by
    intro i i' x
    apply hp.tupling_uniq
    intro j
    rw [Cat.assoc, hκproj]
    exact (pc.cocones j).nat x
  -- weak initiality: every cocone `c` is reached from `(P, κ)`
  have weakInit : ∀ (c : DiagCocone D), ∃ w : P ⟶ c.nadir, ∀ i, κ i ≫ w = c.ι i := by
    intro c
    obtain ⟨j, u, hu⟩ := pc.cofinal c
    refine ⟨hp.proj j ≫ u, ?_⟩
    intro i
    rw [← Cat.assoc, hκproj, hu i]
  -- ── wide equalizer of all cocone-endomorphisms of (P, κ) ──
  let K : Type v := { e : P ⟶ P // ∀ i, κ i ≫ e = κ i }
  let we := wideEqualizer heq hp (fun (k : K) => k.1)
  let R : ℬ := we.R
  let r : R ⟶ P := we.r
  have rMonic : ∀ {X : ℬ} (u v : X ⟶ R), u ≫ r = v ≫ r → u = v := by
    intro X u v huv
    have hm : ∀ k, (u ≫ r) ≫ (fun (k : K) => k.1) k = u ≫ r := fun k => by
      rw [Cat.assoc, we.spec k]
    have hu := we.uniq (u ≫ r) hm u rfl
    have hv := we.uniq (u ≫ r) (by rw [huv] at hm ⊢; exact hm) v huv.symm
    rw [hu]; rw [huv] at hm; rw [hv]
  -- each κ i equalizes the family with id (def of K → joint monic of the product), via fmap/gmap
  let Qprod : ℬ := hp.prodObj (fun _ : K => P)
  let fmap : P ⟶ Qprod := hp.tupling (fun (k : K) => k.1)
  let gmap : P ⟶ Qprod := hp.tupling (fun _ : K => Cat.id P)
  -- r is the equalizer of fmap, gmap (this is how `wideEqualizer` is built); we only need that
  -- κ i factors through r, which holds because κ i ≫ fmap = κ i ≫ gmap.
  have hκfg : ∀ i, κ i ≫ fmap = κ i ≫ gmap := by
    intro i
    have proj_eq : ∀ k : K, (κ i ≫ fmap) ≫ hp.proj k = (κ i ≫ gmap) ≫ hp.proj k := by
      intro k
      rw [Cat.assoc, hp.tupling_fac, Cat.assoc, hp.tupling_fac, Cat.comp_id, k.2 i]
    have e1 : κ i ≫ fmap = hp.tupling (fun k => (κ i ≫ gmap) ≫ hp.proj k) :=
      hp.tupling_uniq (fun k => (κ i ≫ gmap) ≫ hp.proj k) (κ i ≫ fmap) proj_eq
    have e2 : κ i ≫ gmap = hp.tupling (fun k => (κ i ≫ gmap) ≫ hp.proj k) :=
      hp.tupling_uniq (fun k => (κ i ≫ gmap) ≫ hp.proj k) (κ i ≫ gmap) (fun _ => rfl)
    exact e1.trans e2.symm
  -- lift each κ i through R = wide equalizer
  have hκk : ∀ i (k : K), κ i ≫ k.1 = κ i := fun i k => k.2 i
  let ιR : (i : 𝒟) → D i ⟶ R := fun i => we.lift (κ i) (hκk i)
  have hιR : ∀ i, ιR i ≫ r = κ i := fun i => we.fac (κ i) (hκk i)
  -- `(R, ιR)` is a cocone (push naturality through the monic `r`)
  have ιRnat : ∀ {i i' : 𝒟} (x : i ⟶ i'), hD.map x ≫ ιR i' = ιR i := by
    intro i i' x
    apply rMonic
    rw [Cat.assoc, hιR, hιR, κnat]
  -- ── uniqueness of cocone-mediating maps out of (R, ιR): any two agree ──
  -- (equalize x₁,x₂ in ℬ, factor ιR through it, pull back weakly-initially, use spec + r monic).
  have colimMonic : ∀ {V : ℬ} (x₁ x₂ : R ⟶ V),
      (∀ i, ιR i ≫ x₁ = ιR i ≫ x₂) → x₁ = x₂ := by
    intro V x₁ x₂ hιRfac
    let E : ℬ := eqObj x₁ x₂
    let m : E ⟶ R := eqMap x₁ x₂
    have hm12 : m ≫ x₁ = m ≫ x₂ := eqMap_eq x₁ x₂
    have mMonic : ∀ {W : ℬ} (s t : W ⟶ E), s ≫ m = t ≫ m → s = t := by
      intro W s t hst
      have hs := eqLift_uniq x₁ x₂ (s ≫ m) (by rw [Cat.assoc, hm12, Cat.assoc]) s rfl
      have ht := eqLift_uniq x₁ x₂ (s ≫ m) (by rw [Cat.assoc, hm12, Cat.assoc]) t hst.symm
      rw [hs, ht]
    let ιE : (i : 𝒟) → D i ⟶ E := fun i => eqLift x₁ x₂ (ιR i) (hιRfac i)
    have hιE : ∀ i, ιE i ≫ m = ιR i := fun i => eqLift_fac x₁ x₂ (ιR i) (hιRfac i)
    have ιEcocone : ∀ {i i' : 𝒟} (x : i ⟶ i'), hD.map x ≫ ιE i' = ιE i := by
      intro i i' x
      apply mMonic
      rw [Cat.assoc, hιE, hιE, ιRnat]
    obtain ⟨p, hp2⟩ := weakInit { nadir := E, ι := ιE, nat := fun {i i'} x => ιEcocone x }
    -- endo q := p ≫ m ≫ r is a cocone-endo of (P,κ); spec ⟹ r ≫ p ≫ m = id_R ⟹ m split epi
    let q : P ⟶ P := p ≫ m ≫ r
    have hq : ∀ i, κ i ≫ q = κ i := by
      intro i
      show κ i ≫ (p ≫ m ≫ r) = κ i
      rw [← Cat.assoc, hp2 i, ← Cat.assoc, hιE, hιR]
    have hspec : r ≫ q = r := we.spec ⟨q, hq⟩
    have hsplit : (r ≫ p ≫ m) ≫ r = Cat.id R ≫ r := by
      rw [Cat.id_comp, Cat.assoc, Cat.assoc]
      show r ≫ (p ≫ m ≫ r) = r
      exact hspec
    have hsec : (r ≫ p) ≫ m = Cat.id R := by
      have h := rMonic (r ≫ p ≫ m) (Cat.id R) hsplit
      rw [← Cat.assoc] at h; rw [h]
    calc x₁ = Cat.id R ≫ x₁ := (Cat.id_comp _).symm
      _ = ((r ≫ p) ≫ m) ≫ x₁ := by rw [hsec]
      _ = (r ≫ p) ≫ (m ≫ x₁) := Cat.assoc _ _ _
      _ = (r ≫ p) ≫ (m ≫ x₂) := by rw [hm12]
      _ = ((r ≫ p) ≫ m) ≫ x₂ := (Cat.assoc _ _ _).symm
      _ = Cat.id R ≫ x₂ := by rw [hsec]
      _ = x₂ := Cat.id_comp _
  -- ── assemble the colimit ──
  exact
    { cocone := { nadir := R, ι := ιR, nat := fun {i i'} x => ιRnat x }
      lift := fun c => r ≫ (weakInit c).choose
      fac := fun c i => by
        show ιR i ≫ (r ≫ (weakInit c).choose) = c.ι i
        rw [← Cat.assoc, hιR, (weakInit c).choose_spec i]
      uniq := fun c u hu => by
        apply colimMonic
        intro i
        rw [hu i]
        show c.ι i = ιR i ≫ (r ≫ (weakInit c).choose)
        rw [← Cat.assoc, hιR, (weakInit c).choose_spec i] }

-- BOOK §1.825 (dual): A category is cocomplete iff it has coequalizers and arbitrary
-- coproducts.  Not formalized here: needs `HasCoequalizers` (S1_58) and `HasAllCoproducts`
-- (S1_84), neither of which is imported into this file.  It is the exact dual of the
-- `complete_iff_products_equalizers` engine proved above (§1.825).

-- BOOK §1.825 (cartesian): A category is (co-)cartesian iff every finite diagram has a
-- (co-)limit.  Not formalized here: there is no `Cartesian` typeclass nor a `FiniteDiagram`
-- shape predicate in scope; it is the finite-shape restriction of the same engine.

/-- §1.834 GENERAL REPRESENTABILITY THEOREM (Freyd §1.834): for `ℬ` in which idempotents
    split and which is pre-complete, the functor `(A, G(-))` is representable for *every* `A`
    (i.e. `G` is representable in the pointwise sense) iff `G` is *pointwise continuous*
    (`IsUniformlyContinuous`) and *petty* (`PreAdjointFunctor`, the generating/solution-set
    condition).  The hard half is `mgaft_representability`; the easy half transports the
    representations into a left adjoint (`adjunction_of_representability`) whose right adjoint
    `G` is then uniformly continuous and pre-adjoint. -/
theorem general_representability_theorem
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [hG : Functor G] [PreComplete ℬ] (hsplit : IdempotentsSplit ℬ) :
    (∀ A : 𝒜, ∃ R : ℬ, Nonempty (RepresentedBy G A R)) ↔
    (IsUniformlyContinuous G ∧ Nonempty (PreAdjointFunctor G)) := by
  classical
  constructor
  · intro hrep
    have hrepr : ∀ A : 𝒜, Σ R : ℬ, RepresentedBy G A R :=
      fun A => ⟨(hrep A).choose, Classical.choice (hrep A).choose_spec⟩
    obtain ⟨F, hF, adj⟩ := adjunction_of_representability G hrepr
    exact ⟨isUniformlyContinuous_of_adjunction adj, ⟨preAdjointFunctor_of_adjunction adj⟩⟩
  · rintro ⟨huc, ⟨pre⟩⟩
    intro A
    exact ⟨(mgaft_representability hsplit huc pre A).1, ⟨(mgaft_representability hsplit huc pre A).2⟩⟩

/-! ### §1.835 / §1.83(10): the coterminator via the constant functor to the point.

  A *coterminator* (initial object) `R` is exactly a representing object for the constant
  functor `! : ℬ → PUnit` at the point: `RepresentedBy ! ⋆ R` gives a bijection
  `(⋆ ⟶ ⋆) ≅ (R ⟶ B)` for every `B`, and `⋆ ⟶ ⋆` is a one-element set, so every `R ⟶ B`
  is a singleton — `R` is initial.  We feed this constant functor to the adjoint-functor
  engines: MGAFT for §1.835, SAFT for §1.83(10). -/

/-- The one-object category (the terminal object of `Cat`). -/
private instance punitCat : Cat.{v} (PUnit.{v+1}) where
  Hom _ _ := ULift.{v} PUnit
  id _ := ⟨PUnit.unit⟩
  comp _ _ := ⟨PUnit.unit⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The constant functor `! : ℬ → PUnit`. -/
private instance constPUnitFunctor {ℬ : Type u₁} [Cat.{v} ℬ] :
    Functor (fun _ : ℬ => (PUnit.unit : PUnit.{v+1})) where
  map _ := ⟨PUnit.unit⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `RepresentedBy ! ⋆ R` says exactly that `R` is a coterminator (initial object):
    every `R ⟶ B` is the unique such map. -/
private theorem coterminator_of_representedBy {ℬ : Type u₁} [Cat.{v} ℬ] {R : ℬ}
    (r : RepresentedBy (fun _ : ℬ => (PUnit.unit : PUnit.{v+1})) PUnit.unit R) :
    ∀ X : ℬ, ∃ f : R ⟶ X, ∀ g : R ⟶ X, g = f := by
  intro X
  -- the single point's hom-set `⋆ ⟶ ⋆` is `ULift PUnit`, a subsingleton, so `φ` exhibits
  -- `R ⟶ X` as a one-element set.
  refine ⟨r.φ ⟨PUnit.unit⟩, fun g => ?_⟩
  have hg : g = r.φ (r.ψ g) := (r.φψ g).symm
  rw [hg]
  -- both `r.ψ g` and `⟨PUnit.unit⟩` are elements of `⋆ ⟶ ⋆ = ULift PUnit`, a subsingleton
  congr 1

/-- `!` is uniformly continuous whenever every small diagram has a lower-bound
    (`WeaklyComplete`): the lower-bound *is* the required ℬ-cone, and the factoring map in
    `PUnit` is forced (every hom of `PUnit` is the point). -/
private theorem constPUnit_uniformlyContinuous {ℬ : Type u₁} [Cat.{v} ℬ] [wc : WeaklyComplete ℬ] :
    IsUniformlyContinuous (fun _ : ℬ => (PUnit.unit : PUnit.{v+1})) := by
  intro 𝒟 _ D hD A legs hnat
  let wl := wc.hasWeakLimit D
  exact ⟨wl.cone.apex, wl.cone.π, wl.cone.nat, ⟨PUnit.unit⟩, fun _ => rfl⟩

/-- `!` is continuous whenever ℬ is complete: the target `PUnit` is a one-object category, so
    every required mediating map is forced (all of `PUnit`'s homs coincide). -/
private theorem constPUnit_continuous {ℬ : Type u₁} [Cat.{v} ℬ] :
    IsContinuous (fun _ : ℬ => (PUnit.unit : PUnit.{v+1})) := by
  intro 𝒟 _ D hD lim W legs hnat
  exact ⟨⟨PUnit.unit⟩, fun _ => rfl, fun _ _ => rfl⟩

/-- §1.835 (Freyd): a pre-complete category in which idempotents split, and in which every
    small diagram has a lower-bound (`WeaklyComplete`), has a coterminator (initial object) as
    soon as it has a *pre-coterminator* — a solution set `{Cᵢ}` such that every `X` admits a
    map from some `Cᵢ`, encoded as a pre-adjoint family for the constant functor `! : ℬ → PUnit`.
    Proved by feeding `!` to `mgaft_representability`. -/
theorem coterminator_of_precoterminator_lowerbounds
    {ℬ : Type u₁} [Cat.{v} ℬ] [PreComplete ℬ] [WeaklyComplete ℬ]
    (hsplit : IdempotentsSplit ℬ)
    (hpre : PreAdjointFunctor (fun _ : ℬ => (PUnit.unit : PUnit.{v+1}))) :
    ∃ R : ℬ, ∀ X : ℬ, ∃ f : R ⟶ X, ∀ g : R ⟶ X, g = f := by
  let rep := mgaft_representability hsplit constPUnit_uniformlyContinuous hpre PUnit.unit
  exact ⟨rep.1, coterminator_of_representedBy rep.2⟩

-- BOOK §1.83(10) helper: if `T : B → S` is continuous and `B` is complete and well-powered,
-- then the category of elements `El(T)` is complete and well-powered, and a cogenerating set
-- `{Cᵢ}` of `B` yields the cogenerating set `{⟨x, Cᵢ⟩ | x ∈ T(Cᵢ)}` of `El(T)`.  Not
-- formalized here: there is no `El(T)` (category-of-elements) construction in scope; it is the
-- structural bookkeeping that lets SAFT be applied object-wise.

/-- §1.83(10) (Freyd): a complete, well-powered category with a cogenerating set has a
    coterminator (initial object).  Proved by feeding the constant functor `! : ℬ → PUnit`
    (trivially continuous, since `PUnit` is a one-object category) to the
    `special_adjoint_functor_theorem`: a left adjoint `F` to `!` gives the representing object
    `F ⋆`, i.e. the coterminator. -/
theorem coterminator_of_complete_wellPowered_cogenerating
    {ℬ : Type u₁} [Cat.{v} ℬ] [Complete ℬ] [WellPowered ℬ]
    {I : Type v} (C : I → ℬ) (hcogen : IsCoGeneratingSet C) :
    ∃ R : ℬ, ∀ X : ℬ, ∃ f : R ⟶ X, ∀ g : R ⟶ X, g = f := by
  obtain ⟨F, hF, ⟨adj⟩⟩ :=
    special_adjoint_functor_theorem (fun _ : ℬ => (PUnit.unit : PUnit.{v+1}))
      C hcogen constPUnit_continuous
  exact ⟨F PUnit.unit, coterminator_of_representedBy (repr_of_adj adj PUnit.unit)⟩

-- BOOK §1.83(11) (dual of SAFT): if `𝒜` is cocomplete, well-co-powered and has a generating
-- set, then every cocontinuous functor `𝒜 → ℬ` (with `ℬ` locally small) has a right adjoint,
-- and every continuous *contravariant* functor (carrying colimits to limits) has a right
-- adjoint.  Not formalized here: there is no `WellCoPowered` class nor an `IsGeneratingSet`
-- predicate in scope; it is the formal dual of `special_adjoint_functor_theorem`.

/-- §1.837: A complete locally small category is cocomplete iff it is pre-cocomplete. -/
theorem complete_cocomplete_iff_precocomplete
    (ℬ : Type u₁) [Cat.{v} ℬ] [Complete ℬ] :
    Nonempty (Cocomplete ℬ) ↔ Nonempty (PreCocomplete ℬ) := by
  constructor
  · rintro ⟨hc⟩; exact ⟨cocomplete_imp_preCocomplete hc⟩
  · rintro ⟨hpc⟩; exact ⟨cocomplete_of_complete_precocomplete hpc⟩

end Freyd
