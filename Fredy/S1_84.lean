/-
  Freyd & Scedrov, *Categories, Allegories* §1.84
  Grothendieck topoi (Giraud definition) and immediate consequences.

  §1.84  GIRAUD DEFINITION of a Grothendieck topos.
  §1.843 A Grothendieck topos is well-powered (and well-copowered).
  §1.844 A Grothendieck topos is locally complete.
  §1.845 Coproducts in E remain coproducts in Rel(E).
  §1.846 A coequalizer in E remains a coequalizer in Rel(E).

  NOTE: We do not import S1_70 here because that file has a build error
  (logos_implies_preLogos is missing PreLogos fields).  The one class
  we need from §1.712 (LocallyComplete) is redefined locally below.
-/

import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58
import Fredy.S1_59
import Fredy.S1_60
import Fredy.S1_62
import Fredy.S1_64
import Fredy.S1_82

open Freyd

universe v u

namespace Freyd

variable {E : Type u} [Cat.{v} E]

/-! ## Local infrastructure ------------------------------------------------- -/

/-- Arbitrary-indexed coproduct: ΣAᵢ with injections uᵢ : Aᵢ → ΣAᵢ. -/
structure Coproduct {𝒞 : Type u} [Cat.{v} 𝒞] {I : Type v} (A : I → 𝒞) where
  obj  : 𝒞
  inj  : ∀ i, A i ⟶ obj
  desc : ∀ {X : 𝒞} (f : ∀ i, A i ⟶ X), obj ⟶ X
  fac  : ∀ {X : 𝒞} (f : ∀ i, A i ⟶ X) (i : I), inj i ≫ desc f = f i
  uniq : ∀ {X : 𝒞} (f : ∀ i, A i ⟶ X) (h : obj ⟶ X),
           (∀ i, inj i ≫ h = f i) → h = desc f

/-- A category has all small coproducts indexed by types in universe v. -/
class HasAllCoproducts (𝒞 : Type u) [Cat.{v} 𝒞] where
  coprod : ∀ {I : Type v} (A : I → 𝒞), Coproduct A

-- COCOMPLETE (§1.823) is defined canonically in S1_82.  For the Giraud bundle
-- below we require its two building blocks directly: `HasAllCoproducts` (above)
-- and `HasCoequalizers` (from S1_58), avoiding a duplicate `Cocomplete` class.

/-- LOCALLY COMPLETE (§1.712): each subobject lattice is a complete lattice.
    Redefined here to avoid importing the broken S1_70 build. -/
class LocallyComplete' (𝒞 : Type u) [Cat.{v} 𝒞] extends HasImages 𝒞 where
  sup : ∀ {A : 𝒞}, ((Subobject 𝒞 A) → Prop) → Subobject 𝒞 A
  sup_upper : ∀ {A : 𝒞} (S : (Subobject 𝒞 A) → Prop) (s : Subobject 𝒞 A),
    S s → Subobject.le s (sup S)
  sup_least : ∀ {A : 𝒞} (S : (Subobject 𝒞 A) → Prop) (U : Subobject 𝒞 A),
    (∀ s, S s → Subobject.le s U) → Subobject.le (sup S) U

/-! ## §1.84 Giraud Definition of a Grothendieck Topos ---------------------- -/

/-- DISJOINT COPRODUCTS (§1.845): for coproduct {uᵢ : Aᵢ → S},
    each uᵢ is monic, the family is jointly a cover, and
    the intersection A i ×_{S} A j is the zero subobject for i ≠ j.

    Book formulation: uᵢ uᵢ° = 1, uᵢ° uⱼ = 0 (i ≠ j), ⋃ uᵢ° uᵢ = 1. -/
structure DisjointCoproduct {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {I : Type v} {A : I → 𝒞} (cp : Coproduct A) : Prop where
  /-- Each injection is monic (expresses uᵢ uᵢ° = 1 as a map). -/
  inj_monic    : ∀ i, Mono (cp.inj i)
  /-- The injections are jointly a cover of the coproduct object. -/
  inj_cover    : Cover (cp.desc (fun i => cp.inj i))
  /-- Disjointness: the pullback of uᵢ and uⱼ (i ≠ j) is the zero subobject,
      i.e., for any X with f : X → Aᵢ, g : X → Aⱼ, f uᵢ = g uⱼ implies X ≅ 0.
      We express this by saying any h : X → Z factors through the initial morphism
      (X is the zero object in a canonical sense). -/
  inj_disjoint : ∀ (i j : I), i ≠ j →
    ∀ {X : 𝒞} (f : X ⟶ A i) (g : X ⟶ A j),
      f ≫ cp.inj i = g ≫ cp.inj j →
      ∀ {Z : 𝒞} (h k : X ⟶ Z), h = k

/-- PULLBACKS PRESERVE ARBITRARY UNIONS (§1.84): the inverse-image functor
    f# commutes with arbitrary suprema of subobjects.
    Concretely: if {Bₛ} is a family of subobjects of B whose supremum is all
    of B (i.e., the identity sub-object), then the inverse images f#(Bₛ)
    also have their supremum equal to all of A.

    We express "supremum = all of A" as: for any monic m : X → A, if every
    f#(Bₛ) ≤ X then m is an iso (i.e., X = A up to iso). -/
def PullbacksPreserveArbitraryUnions (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasPullbacks 𝒞] [HasImages 𝒞] : Prop :=
  ∀ {A B : 𝒞} (f : A ⟶ B) (S : (Subobject 𝒞 B) → Prop),
    -- hypothesis: the family S covers B (its upper bound is B)
    (∀ {X : 𝒞} (m : X ⟶ B) (hm : Mono m),
       (∀ s, S s → Subobject.le s ⟨X, m, hm⟩) → IsIso m) →
    -- conclusion: the inverse images f#(S) cover A
    (∀ {X : 𝒞} (m : X ⟶ A) (hm : Mono m),
       (∀ s, S s → Subobject.le (InverseImage f s) ⟨X, m, hm⟩) → IsIso m)

/-- THE GIRAUD DEFINITION (§1.84):
    A GROTHENDIECK TOPOS is a locally small, cocomplete, effective regular
    category with a generating set, disjoint coproducts, and pullbacks
    that preserve arbitrary unions. -/
class GrothendieckTopos (E : Type u) [Cat.{v} E] extends
    EffectiveRegular E, HasAllCoproducts E, HasCoequalizers E, LocallyComplete' E where
  /-- A small generating set (§1.84, §1.632). -/
  gen_set         : E → Prop
  has_gen_set     : IsGeneratingSet gen_set
  /-- All coproducts are disjoint (§1.845). -/
  coprod_disjoint : ∀ {I : Type v} (A : I → E),
    DisjointCoproduct (HasAllCoproducts.coprod A)
  /-- Pullbacks preserve arbitrary unions (§1.84).
      Note: PullbacksPreserveArbitraryUnions does not depend on LocallyComplete'. -/
  pullback_union  : PullbacksPreserveArbitraryUnions E

/-! ## §1.841–§1.842 Examples and the graphing-functor adjoint ---------------- -/

/-
  §1.841: The prime examples (presheaf topos YA and the topos of sheaves B☞(Y))
  satisfy the Giraud definition.
  MISSING: Cannot be stated without formalizing the presheaf construction.

  §1.842: If E is a Grothendieck topos, the graphing functor E → Rel(E) has a
  right adjoint.
  MISSING: Rel(E) as a category (with objects = objects of E and morphisms =
  equivalence classes of relations) is not yet formalized in this repo.
  The statement requires a `Cat` instance on Rel(E) and a `Functor` instance
  for the graphing map E → Rel(E).  See S1_84.md.
-/

/-! ## §1.843 A Grothendieck topos is well-powered (and well-copowered) ----- -/

/-- §1.843: A Grothendieck topos is WELL-POWERED: the collection Sub(A) of
    subobjects of each object A is a set (up to isomorphism, bounded by a
    type in universe v).

    BOOK PROOF: The generating set ℱ is also a basis in any pre-topos
    (every subobject appears as an equalizer, hence is detected by ℱ).
    Sub(A) embeds into Π_{G∈ℱ} 𝒫(Hom(G,A)), which is small. -/
instance grothendieck_topos_well_powered [GrothendieckTopos E] : WellPowered E where
  small := by
    -- Sub(A) is indexed by the set of pairs (G∈ℱ, G→A), via the basis property:
    -- two subobjects agree iff they agree on all generators.
    -- Full formal proof requires the pre-topos equalizer argument (§1.843).
    sorry

/-- Two covers A ↠ P and A ↠ Q are ISOMORPHIC if there is a commuting iso P ≅ Q. -/
def CoverIso {𝒞 : Type u} [Cat.{v} 𝒞] {A : 𝒞} {P Q : 𝒞}
    (p : A ⟶ P) (q : A ⟶ Q) : Prop :=
  ∃ (i : P ⟶ Q), IsIso i ∧ p ≫ i = q

/-- WELL-COPOWERED: for each A, the class of covers A ↠ Q (up to isomorphism)
    is bounded by a type in universe v. -/
class WellCopowered (𝒞 : Type u) [Cat.{v} 𝒞] : Prop where
  small : ∀ (A : 𝒞), ∃ (I : Type v) (codom : I → 𝒞) (cov : ∀ i, A ⟶ codom i)
            (hcov : ∀ i, Cover (cov i)),
            ∀ (Q : 𝒞) (q : A ⟶ Q) (_ : Cover q),
              ∃ i : I, CoverIso (cov i) q

/-- §1.843: A Grothendieck topos is WELL-COPOWERED.

    BOOK PROOF: In any effective regular category, covers coincide with
    comonics, and isomorphism-types of covers A ↠ Q correspond bijectively
    to equivalence relations on A.  These are bounded by Sub(A × A),
    which is a set since E is well-powered. -/
instance grothendieck_topos_well_copowered [GrothendieckTopos E] : WellCopowered E where
  small := by
    -- Isomorphism types of covers A ↠ Q ↔ equivalence relations on A ↔ Sub(A×A).
    -- Formal proof uses EffectiveRegular + grothendieck_topos_well_powered.
    sorry

/-! ## §1.844 A Grothendieck topos is locally complete ---------------------- -/

/-- §1.844: A Grothendieck topos is locally complete.
    This is already built into the `GrothendieckTopos` typeclass
    (extends `LocallyComplete'`).

    BOOK PROOF: Given a family {Aᵢ ↣ A} of subobjects, form the coproduct
    ΣAᵢ (which exists since E is cocomplete), and let u : ΣAᵢ → A be the
    induced map.  The image of u is the supremum ⋃Aᵢ.  Since pullbacks
    preserve arbitrary unions, the inverse-image functor f# also commutes
    with arbitrary suprema, establishing local completeness. -/
instance grothendieck_topos_locally_complete [GrothendieckTopos E] :
    LocallyComplete' E := inferInstance

/-! ## §1.845 Coproducts in E remain coproducts in Rel(E) ------------------- -/

/-- §1.845: If {uᵢ : Aᵢ → S} is a coproduct in E, it remains a coproduct
    in Rel(E): for any family of relations {Rᵢ : Aᵢ → B}, there is a unique
    R : S → B in Rel(E) such that (graph uᵢ) ⊚ R = Rᵢ for all i.

    BOOK PROOF:
    • uᵢ° (uᵢ) = 1_{Aᵢ}  (uᵢ monic ⟹ graph uᵢ is simple)
    • uᵢ° uⱼ = 0 for i ≠ j (disjoint coproducts, §1.845)
    • ⋃ uᵢ° uᵢ = 1_S (the uᵢ are collectively a cover)
    The candidate relation is R = ⋃ᵢ (reciprocal (graph uᵢ)) ⊚ Rᵢ.
    Verification uses local completeness (§1.844) for the union. -/
theorem coproduct_is_coproduct_in_Rel
    [GrothendieckTopos E]
    {I : Type v} {A : I → E} {B : E}
    (cp : Coproduct A)
    (R : ∀ i, BinRel E (A i) B) :
    ∃ (U : BinRel E cp.obj B),
      ∀ i, RelLe (graph (cp.inj i) ⊚ U) (R i) ∧
           RelLe (R i) (graph (cp.inj i) ⊚ U) := by
  -- The unique relation is U = ⋃ᵢ (graph uᵢ)° ⊚ Rᵢ.
  -- Proof requires arbitrary-union composition in Rel(E) (§1.844).
  sorry

/-! ## §1.846 A coequalizer in E remains a coequalizer in Rel(E) ------------ -/

/-- §1.846: If h : B ↠ C is a coequalizer of f, g : A → B in E,
    then h is a coequalizer in Rel(E): for any relation R : B → D with
    (graph f) ⊚ R ≡ (graph g) ⊚ R, there is a unique R' : C → D
    such that (graph h) ⊚ R' ≡ R.

    BOOK PROOF:
    • Uniqueness: h has a left-inverse in Rel(E) (cover ⟹ h°h = 1).
    • Existence: take R' = h° ⊚ R.  Must show hh°R = R under fR = gR.
      E is E-standard (effective regular + §1.844 distributivity):
      the smallest equivalence relation containing f°g is hh°.
      With S = g°f ∪ 1 ∪ f°g, induction gives Sⁿ R ⊆ R for all n,
      then (⋃ₙ Sⁿ)R ⊆ R by the distributivity of composition with
      arbitrary unions.  The other containment 1 ⊆ hh° gives R ⊆ hh°R. -/
theorem coequalizer_is_coequalizer_in_Rel
    [GrothendieckTopos E]
    {A B C : E} (f g : A ⟶ B) (h : B ⟶ C)
    (h_eq   : f ≫ h = g ≫ h)
    (h_univ : ∀ {X : E} (k : B ⟶ X), f ≫ k = g ≫ k →
                ∃ (k' : C ⟶ X), h ≫ k' = k ∧ ∀ (k'' : C ⟶ X), h ≫ k'' = k → k'' = k')
    {D : E} (R : BinRel E B D)
    (hfgR : RelLe (graph f ⊚ R) (graph g ⊚ R) ∧
            RelLe (graph g ⊚ R) (graph f ⊚ R)) :
    ∃ (R' : BinRel E C D),
      (RelLe (graph h ⊚ R') R ∧ RelLe R (graph h ⊚ R')) ∧
      ∀ (R'' : BinRel E C D),
        (RelLe (graph h ⊚ R'') R ∧ RelLe R (graph h ⊚ R'')) →
        RelLe R'' R' ∧ RelLe R' R'' := by
  -- The unique solution is R' = (reciprocal (graph h)) ⊚ R.
  -- Needs E-standard reasoning and distributivity with arbitrary unions.
  sorry

/-! ## §1.847 Special adjoint functor theorem applies ----------------------- -/

/-
  §1.847: A Grothendieck topos E is cocomplete (by definition), well-copowered
  (§1.843), and has a generating set (by definition).  Rel(E) is locally small
  (because E is well-powered: §1.843) and E → Rel(E) preserves coproducts
  (§1.845) and coequalizers (§1.846), hence is cocontinuous.
  By the special adjoint functor theorem (§1.83), the graphing functor
  E → Rel(E) has a right adjoint.

  MISSING: Requires Rel(E) as a formalized category (see §1.841–§1.842 note).
  Once Rel(E) has a `Cat` instance this will follow from
  `special_adjoint_functor_theorem` in S1_82.lean applied to the graphing functor.
-/

end Freyd
