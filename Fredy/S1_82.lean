/-
  Freyd & Scedrov, *Categories and Allegories* §1.82–§1.83

  §1.82   DIAGONAL FUNCTOR Δ : B → B^D (constant-diagram functor)
  §1.821  Diagrams as functors; cones as maps from Δ(B) to a diagram
  §1.822  LIMIT and COLIMIT (cone formulation)
  §1.823  COMPLETE and COCOMPLETE category
  §1.825  Completeness = equalizers + all products (stated with sorry)
  §1.827  CONTINUOUS / COCONTINUOUS functor
  §1.828  WEAK-LIMIT, WEAKLY-COMPLETE
  §1.82(10) PRE-LIMIT, PRE-COMPLETE
  §1.83   PRE-ADJOINT (for an object) and PRE-ADJOINT FUNCTOR
          GENERAL ADJOINT FUNCTOR THEOREM (stated with sorry)
  §1.838  WELL-POWERED
  §1.83(10) COGENERATING SET
          SPECIAL ADJOINT FUNCTOR THEOREM (stated with sorry)
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

/-- §1.825: A category is complete iff it has equalizers and all products.
    (Equalizers + products yield all limits by the standard construction.
     Conversely limits specialize to each.) -/
theorem complete_iff_eq_prod (ℬ : Type u₁) [Cat.{v} ℬ] :
    Nonempty (Complete ℬ) ↔ (Nonempty (HasEqualizers ℬ) ∧ Nonempty (HasProducts ℬ)) := by
  sorry

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

/-- §1.83 GENERAL ADJOINT FUNCTOR THEOREM. -/
theorem general_adjoint_functor_theorem
    {𝒜 : Type u} [Cat.{v} 𝒜] {ℬ : Type u₁} [Cat.{v} ℬ]
    (G : ℬ → 𝒜) [hG : Functor G]
    [Complete ℬ] :
    (∃ (F : 𝒜 → ℬ) (hF : Functor F), Nonempty (F ⊣ G)) ↔
    (IsContinuous G ∧ Nonempty (PreAdjointFunctor G)) := by
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

end Freyd
