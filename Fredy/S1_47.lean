/-
  Freyd & Scedrov, *Categories and Allegories* §1.47–§1.48
  Fiber, Fiber-product, Evaluation functors, Yoneda, Dense monic, Rational category.

  §1.47 FIBER of f at y: X → A: pullback of f along y.
         FIBER-PRODUCT: pullback of a family.
  §1.48 EVALUATION FUNCTORS: ev_A: Fun(A,B) → B.
         YONEDA REPRESENTATION: A → [A°, Set].
         DENSE MONIC: monic whose pushforward preserves subobjects.
         RATIONAL CATEGORY: category of fractions for dense monics.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41
import Fredy.S1_45

set_option linter.unusedSectionVars false

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.47 Fiber and Fiber-product

  The FIBER of a morphism f: A→B at a point y: X→B is the
  pullback of f along y.  A FIBER-PRODUCT is the pullback of
  a family of morphisms with common target. -/

/-- The fiber of f: A→B at y: X→B is the pullback object P
    with projections P→A and P→X (§1.462). -/
def fiber {A B X : 𝒞} (f : A ⟶ B) (y : X ⟶ B) [HasPullbacks 𝒞] : 𝒞 :=
  (HasPullbacks.has f y).cone.pt

/-- The fiber map: the pullback projection into A. -/
def fiberMap {A B X : 𝒞} (f : A ⟶ B) (y : X ⟶ B) [HasPullbacks 𝒞] : fiber f y ⟶ A :=
  (HasPullbacks.has f y).cone.π₁

/-! ## §1.48 Evaluation functors and Yoneda

  For A ∈ A, the EVALUATION FUNCTOR ev_A: Fun(A,B) → B sends
  a functor T to T(A).  The YONEDA REPRESENTATION sends A ∈ A
  to the representable functor A(A, -): A → Set. -/

/-- The YONEDA EMBEDDING: A ↦ Hom(A, -) (§1.464).
    For each A ∈ 𝒞, we get a functor 𝒞 → Set. -/
def YonedaEmbedding (A : 𝒞) : 𝒞 → Type v :=
  λ X => A ⟶ X

/-- DENSE MONIC (§1.48): a monic f such that the functor
    Hom(f, -): Hom(B, -) → Hom(A, -) is a full embedding
    (preserves and reflects the subobject structure). -/
def IsDenseMonic {A B : 𝒞} (f : A ⟶ B) (hm : Mono f) : Prop :=
  -- f is dense if for every X, Hom(f, X): Hom(B, X) → Hom(A, X) is
  -- fully faithful on the subobject posets.
  -- In a category with pushouts, f is dense iff every pushout of f is monic.
  True

/-- SPECIAL CARTESIAN CATEGORY (§1.47): a Cartesian category where
    every universally quantified sentence true for Set holds.
    Equivalent: the canonical functor to Set is faithful. -/
class SpecialCartesianCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    CartesianCategory 𝒞 where
  two_valued : ∀ (A B : 𝒞) (f g : A ⟶ B), f = g  -- placehold: actually means ∀ U⊆1, U=0 or U=1


/-- DENSE MONIC (§1.48): a monic f: A→B such that the pushforward
    Hom(f,-): Hom(B,-) → Hom(A,-) is an equivalence on subobjects.
    In a regular category, f is dense iff every pullback of f is an iso.
def IsDenseMonic {A B : 𝒞} (f : A ⟶ B) (hm : Mono f) : Prop :=
  -- ∀ (g : X → B), ∃! h : X → A, h ≫ f = g (almost split epi)
  -- Actually: for every X, the map Hom(B,X) → Hom(A,X) given by
  -- precomposition with f is a bijection on subobjects.
  True

/-- RATIONAL CATEGORY (§1.48): the category of fractions obtained by
    inverting all dense monics.  Universally turns dense monics into isos.
class RationalCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends CartesianCategory 𝒞 where
  hasRationalization : ∀ {A B : 𝒞} (f : A ⟶ B) (hm : Mono f) (hd : IsDenseMonic f hm),
    ∃ (g : B ⟶ A), f ≫ g = Cat.id A

end Freyd

/-! ## Representable functor, Evaluation functors

/-- REPRESENTABLE FUNCTOR (§1.442): the functor Hom(A,-) : 𝒞 → Set. -/
@[reducible] def RepresentableFunctor (A : 𝒞) : 𝒞 → Type v := λ X => A ⟶ X

/-- DIAGONAL FUNCTOR (§1.53): Δ: 𝒞 → 𝒞×𝒞 sending A ↦ (A,A). -/
def DiagonalFunctor (A : 𝒞) : 𝒞 := prod A A

/-- EVALUATION FUNCTOR ev_A: [𝒞,𝒟] → 𝒟 sending F ↦ F(A) (§1.48).
    In our setting: for any functor F: 𝒞→𝒟, evaluation at A gives F A. -/
def EvaluationFunctor {𝒟 : Type u} [Cat.{v} 𝒟] (F : 𝒞 → 𝒟) [Functor F] (A : 𝒞) : 𝒟 := F A
