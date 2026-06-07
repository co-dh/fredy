/-
  Freyd & Scedrov, *Categories and Allegories* §1.27  Small category, functor category,
  natural transformation (§1.27), right A-sets (§1.271), Cayley representation (§1.272),
  left A-sets (§1.273), natural equivalence (§1.274).

  §1.27  NaturalTransformation: a family α_X : F X → G X with naturality squares.
  §1.271 Right A-set = covariant functor A → Y.  In the single-sorted language this is
         a set X with a unary operation to |A| (the "source" map) and a partial binary
         operation x a defined iff source(x) = □a, satisfying the monoid-action laws.
  §1.272 CAYLEY REPRESENTATION: a small category A is a right A-set whose carriers
         are C(A) = {x | □x = A} (morphisms targeting A).  For f : A → B, C(f)(y) = y f.
         C is one-to-one (faithful): if C(f) = C(g) then f = g, taking y = A (id_A).
         In the object-centric setting: post-composition h ↦ h ≫ f faithfully encodes f
         because id_A ≫ f = f distinguishes f from any g ≠ f.
  §1.273 Left A-set = contravariant version: right A^op-set (§1.273).
  §1.274 Natural equivalence = natural transformation with iso components (§1.274).
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.27  Natural transformation -/

/-- A natural transformation α : F → G between parallel functors F, G : 𝒞 → 𝒟 (§1.27).
    For each X : 𝒞 a component α_X : F X → G X; for every f : X → Y,
    F(f) ≫ α_Y = α_X ≫ G(f) (naturality). -/
structure NaturalTransformation (F G : 𝒞 → 𝒟) [Functor F] [Functor G] where
  app : (X : 𝒞) → (F X ⟶ G X)
  naturality : ∀ {X Y : 𝒞} (f : X ⟶ Y), (Functor.map f) ≫ app Y = app X ≫ (Functor.map f)

infix:25 " ⟹ " => NaturalTransformation

/-! ## §1.274  Natural equivalence (isomorphism in the functor category) -/

/-- A natural equivalence (§1.274): a natural transformation whose every component is
    an isomorphism.  In the functor category this is precisely an isomorphism. -/
def NaturalIso (F G : 𝒞 → 𝒟) [Functor F] [Functor G] (α : F ⟹ G) : Prop :=
  ∀ X : 𝒞, IsIso (NaturalTransformation.app α X)

/-! ## §1.272  Cayley representation -/

section Cayley

variable {A B : 𝒞}

/-- **§1.272 Cayley representation — faithfulness**.
    In Freyd's single-sorted language: C sends A ↦ {y | □y = A}, f ↦ (y ↦ yf).
    C is one-to-one on morphisms because y = A (id_A) belongs to C(A) and A f = f.
    In the object-centric setting this translates to: if post-composition by f and g
    agree on all maps into A then f = g.  The witness is h = id_A : A → A. -/
theorem cayley_faithful (f g : A ⟶ B)
    (h : ∀ {X : 𝒞} (hX : X ⟶ A), hX ≫ f = hX ≫ g) : f = g := by
  have := h (Cat.id A)
  rwa [Cat.id_comp, Cat.id_comp] at this

/-- **§1.272 (contrapositive)**.  If f ≠ g then they are distinguished by
    some pre-composition — specifically id_A composed with each. -/
theorem cayley_faithful_contra (f g : A ⟶ B) (hne : f ≠ g) :
    ∃ (X : 𝒞) (hX : X ⟶ A), hX ≫ f ≠ hX ≫ g := by
  refine ⟨A, Cat.id A, ?_⟩
  intro h_eq
  apply hne
  rwa [Cat.id_comp, Cat.id_comp] at h_eq

end Cayley

end Freyd
