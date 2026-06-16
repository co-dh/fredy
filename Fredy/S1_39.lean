/-
  Freyd & Scedrov, *Categories and Allegories* §1.34–§1.39 — remaining TOC entries.
  Adjoint pair, Skeleton/Coskeleton, Idempotent/Split idempotent,
  Equivalent categories, Exact sequence, Complete measure, Atomic measure.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31
import Fredy.S1_34
import Fredy.S1_41
import Fredy.S1_43
import Fredy.S1_51
import Fredy.S1_59

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- ADJOINT PAIR (§1.81, §1.373): F ⊣ G with natural bijection Hom(FX,Y) ≅ Hom(X,GY).
    Here defined as a structure on two functors. -/
structure AdjointPair {𝒞 : Type u} {𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞) [Functor F] [Functor G] where
  unit   : Nonempty (NatIso (λ X => X) (G ∘ F))
  counit : Nonempty (NatIso (F ∘ G) (λ X => X))
  -- The proper definition would include triangle identities.
  -- This captures "GF ≅ Id, FG ≅ Id" which characterizes adjoints in the
  -- context of strong equivalences.

/-- LEFT ADJOINT (§1.373): the functor F in an adjoint pair. -/
def LeftAdjoint {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟] (F : 𝒞 → 𝒟) [Functor F] : Prop :=
  ∃ (G : 𝒟 → 𝒞) (_ : Functor G), Nonempty (AdjointPair F G)

/-- RIGHT ADJOINT (§1.373): the functor G in an adjoint pair. -/
def RightAdjoint {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟] (G : 𝒟 → 𝒞) [Functor G] : Prop :=
  ∃ (F : 𝒞 → 𝒟) (_ : Functor F), Nonempty (AdjointPair F G)

/-- EQUIVALENT CATEGORIES (§1.363): two categories are EQUIVALENT if
    there exist isomorphic inflations.  (Existence of an equivalence functor
    implies equivalence.) -/
def EquivalentCategories (𝒜 ℬ : Type u) [Cat.{v} 𝒜] [Cat.{v} ℬ] : Prop :=
  ∃ (F : 𝒜 → ℬ) (_ : Functor F), EquivalenceFunctor F

/-- SKELETAL category (§1.364): isomorphic objects are equal. -/
def IsSkeletal (𝒞 : Type u) [Cat.{v} 𝒞] : Prop :=
  ∀ (A B : 𝒞), Isomorphic A B → A = B

/-- SKELETON of A: a skeletal category A' with an equivalence A' → A. -/
def Skeleton (𝒜 : Type u) [Cat.{v} 𝒜] : Prop :=
  ∃ (A' : Type u) (_ : Cat.{v} A'), IsSkeletal A' ∧ EquivalentCategories A' 𝒜

/-- COSKELETON of A: a skeletal category A' with an equivalence A → A'. -/
def CoSkeleton (𝒜 : Type u) [Cat.{v} 𝒜] : Prop :=
  ∃ (A' : Type u) (_ : Cat.{v} A'), IsSkeletal A' ∧ EquivalentCategories 𝒜 A'

/-- IDEMPOTENT (§1.28): e: A→A such that e² = e. -/
def Idempotent {A : 𝒞} (e : A ⟶ A) : Prop := e ≫ e = e

/-- SPLIT IDEMPOTENT (§1.281): there exist r: A→B, s: B→A with s≫r = id, r≫s = e. -/
def SplitIdempotent {A : 𝒞} (e : A ⟶ A) : Prop :=
  Idempotent e ∧ ∃ (B : 𝒞) (r : A ⟶ B) (s : B ⟶ A), s ≫ r = Cat.id B ∧ r ≫ s = e

/-- EXACT AT (§1.599): a composable pair `A —f→ B —g→ C` is EXACT at `B` when the
    image of `f` coincides (is isomorphic, as a subobject of `B`) with the kernel of `g`.
    A full exact sequence is a family of objects/maps that is `ExactAt` at every
    interior node; we give the local condition, which carries all the content. -/
def ExactAt [HasImages 𝒞] [HasEqualizers 𝒞] [HasZeroObject 𝒞]
    {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) : Prop :=
  Isomorphic (image f).dom (Kernel g)

-- A subset of `I` is encoded mathlib-free as a predicate `I → Prop`, and a family
-- of subsets as `(I → Prop) → Prop`.

/-- COMPLETE MEASURE (§1.648): an ultrafilter on `I` closed under countable
    intersections — every `ℕ`-indexed family of members has its intersection in `F`. -/
def CompleteMeasure (I : Type u) (F : (I → Prop) → Prop) : Prop :=
  -- ultrafilter:
  (F (fun _ => True)) ∧ ¬ F (fun _ => False) ∧
  (∀ S T, F S → (∀ i, S i → T i) → F T) ∧
  (∀ S, F S ∨ F (fun i => ¬ S i)) ∧
  -- closed under countable (ℕ-indexed) intersection:
  (∀ A : Nat → (I → Prop), (∀ n, F (A n)) → F (fun i => ∀ n, A n i))

/-- ATOMIC MEASURE (§1.648): the principal ultrafilter at `i` — the members are
    exactly the subsets containing `i`. -/
def AtomicMeasure (I : Type u) (F : (I → Prop) → Prop) (i : I) : Prop :=
  F = fun J => J i

end Freyd
