/-
  Freyd & Scedrov, *Categories and Allegories* §1.62–§1.66
  Pasting Lemma, Positive pre-logoi, coproducts, generating set,
  pre-filter, Representation Theorem.

  §1.62 Pasting Lemma: union of subobjects is pushout of intersection.
  §1.623 Positive pre-logos = pre-logos with coproducts.
  §1.632 Generating set / basis.
  §1.634 Pre-filter, T_𝔉 functor.
  §1.635 Representation Theorem for pre-logoi.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58
import Fredy.S1_60

set_option linter.unusedSectionVars false

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.62 Pasting Lemma

  In a pre-logos, the union A₁∪A₂ is the pushout of A₁∩A₂. -/

variable [PreLogos 𝒞]

/-- Pasting Lemma (§1.62): for subobjects A₁,A₂ of A, the square
    A₁∩A₂ → A₁, A₁∩A₂ → A₂, A₁ → A₁∪A₂, A₂ → A₁∪A₂ is a pushout.

    The proof constructs R = x°f ∪ y°g and uses relation composition
    to show it satisfies the pushout universal property. -/
theorem pasting_lemma {A : 𝒞} (A₁ A₂ : Subobject 𝒞 A) : Nonempty (HasPushout (intersection A₁ A₂) (union A₁ A₂)) := by
  -- Let I = A₁ ∩ A₂ (pullback), U = A₁ ∪ A₂ (union).
  -- The maps are: I → A₁ (pullback proj₁), I → A₂ (pullback proj₂),
  -- A₁ → U (inclusion), A₂ → U (inclusion).
  -- To show: the resulting square is a pushout.
  -- The book's proof uses R = x°f ∪ y°g, shows 1 ⊆ RR° and R°R ⊆ 1,
  -- hence R is a map (entire + simple), and xR = f, yR = g uniquely.
  -- This requires the full relation composition + simple/entire identities.
  sorry

/-! ## §1.623 Positive pre-logoi

  A POSITIVE PRE-LOGOS has binary coproducts (equivalently:
  for every A,B there exists C with A,B as complemented subobjects). -/

class PositivePreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends PreLogos 𝒞, HasBinaryCoproducts 𝒞

/-- §1.624: In a positive pre-logos, f: A → B₁+B₂ decomposes as
    f₁+f₂ from A₁ → B₁, A₂ → B₂ where A = A₁+A₂. -/
theorem decompose_via_coproduct [PositivePreLogos 𝒞] {A B₁ B₂ : 𝒞} (f : A ⟶ coprod B₁ B₂) :
    ∃ (A₁ A₂ : 𝒞) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂), Isomorphic A (coprod A₁ A₂) := by
  -- f#(inl) and f#(inr) pull back the coproduct inclusions
  sorry

/-! ## §1.632 Generating set / basis

  A set ℱ of objects is GENERATING if the representable functors
  {(G, -)} form an embedding.  A BASIS is a collectively faithful set. -/

/-- ℱ is GENERATING if the functors Hom(G,-) for G∈ℱ are collectively
    an embedding (i.e., injective on morphisms). -/
def IsGeneratingSet (ℱ : Set 𝒞) : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B), (∀ G ∈ ℱ, ∀ h : G ⟶ A, h ≫ f = h ≫ g) → f = g

/-- ℱ is a BASIS if the functors Hom(G,-) for G∈ℱ are collectively
    faithful.  In a Cartesian category: for every proper A'↣A, ∃ G∈ℱ
    and G→A not factoring through A'. -/
def IsBasis [HasPullbacks 𝒞] (ℱ : Set 𝒞) : Prop :=
  IsGeneratingSet ℱ ∧
  ∀ {A' A : 𝒞} (m : A' ⟶ A), Mono m → ¬ IsIso m →
    ∃ G ∈ ℱ, ∃ (x : G ⟶ A), ¬ ∃ (y : G ⟶ A'), y ≫ m = x

/-! ## §1.634 Pre-filter

  A non-empty ℱ ⊆ Sub(1) is a PRE-FILTER if it's ↓-directed.
  For a pre-filter ℱ, define T_ℱ : A → 𝒮 the colimit of Hom(U,-). -/

/-- ℱ is a pre-filter in the subobject lattice of 1: non-empty and
    ∀ U,V ∈ ℱ, ∃ W ∈ ℱ with W ≤ U and W ≤ V. -/
def IsPreFilter (ℱ : Set (Subobject 𝒞 one)) : Prop :=
  ℱ.Nonempty ∧ ∀ U V ∈ ℱ, ∃ W ∈ ℱ, Subobject.le W U ∧ Subobject.le W V

/-- T_ℱ(A) = colim_{U∈ℱ} Hom(U, A).  For U projective, T_ℱ preserves
    finite products and equalizers; if ℱ is an ultra-filter in a Boolean
    algebra, T_ℱ preserves unions (§1.634-1.635). -/
def prefilter_functor (ℱ : Set (Subobject 𝒞 one)) (hℱ : IsPreFilter ℱ) : 𝒞 → Type u :=
  λ A => Σ' (U : Subobject 𝒞 one) (_ : U ∈ ℱ), U.dom ⟶ A
  -- Actually the elements are equivalence classes of maps U→A.
  -- Full definition requires a colimit of Hom-sets, which is set-theoretic.
  -- Placeholder.

/-! ## §1.635 Representation theorem for pre-logoi

  Every small positive pre-logos is faithfully representable in a
  power of the category of sets.  Proof via capital extension,
  complemented subterminators (which form a Boolean algebra),
  ultra-filters, and the T_ℱ construction. -/

theorem prelogos_representation_theorem (A : Type u) [Cat.{v} A] [PositivePreLogos A] : ∃ (T : A → ((A : Type u) → Type u)), IsFaithful (λ x => x) := by
  -- The deep proof uses: capital extension (§1.63) + Stone representation
  -- of Boolean algebras via ultra-filters → T_ℱ is a faithful representation.
  -- Requires axiom of choice for the ultra-filter theorem.
  sorry


/-- FILTER in a subobject lattice: up-closed pre-filter (§1.634).
def IsFilter (ℱ : Set (Subobject 𝒞 one)) : Prop :=
  IsPreFilter ℱ ∧ ∀ (U V : Subobject 𝒞 one), U ∈ ℱ → Subobject.le U V → V ∈ ℱ

end Freyd
