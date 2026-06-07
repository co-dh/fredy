/-
  Freyd & Scedrov, *Categories and Allegories* §1.31–§1.32
  Embedding, Full, Representative Image, Equivalence Functor,
  Strong equivalence.  Proofs assuming composed functor = compFunctor.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.31 Embedding, Full, Representative Image, Equivalence Functor -/

def IsEmbedding (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B), hF.map f = hF.map g → f = g

def IsFull (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  ∀ {A B : 𝒞} (h : F A ⟶ F B), ∃ f : A ⟶ B, hF.map f = h

def HasRepresentativeImage (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  ∀ B : 𝒟, ∃ A : 𝒞, ∃ (h : F A ⟶ B), IsIso h

def IsEquivalenceFunctor (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  IsEmbedding F ∧ IsFull F ∧ HasRepresentativeImage F

/-! ## §1.32 Composition and cancellation

  Embedding ∘ embedding = embedding; full ∘ full = full.
  With `hGF := compFunctor hF hG`, these are definitional. -/

section Composition
variable {F : 𝒞 → 𝒟} [hF : Functor F] {ℰ : Type u} [Cat.{v} ℰ] {G : 𝒟 → ℰ} [hG : Functor G]
variable [hGF : Functor (G ∘ F)]

theorem embedding_comp (embF : IsEmbedding F) (embG : IsEmbedding G) : IsEmbedding (G ∘ F) := by
  intro A B f g h
  -- h: hGF.map f = hGF.map g
  -- If hGF = compFunctor hF hG, then hGF.map f = hG.map (hF.map f)
  -- So hG.map (hF.map f) = hG.map (hF.map g) → hF.map f = hF.map g → f = g
  apply embF
  apply embG
  -- We need: hG.map (hF.map f) = hG.map (hF.map g)
  -- But h is about hGF.map.  This holds if hGF = compFunctor.
  -- For the general case, the statement requires the composed functor to be compFunctor.
  sorry

theorem full_comp (fullF : IsFull F) (fullG : IsFull G) : IsFull (G ∘ F) := by
  intro A B h
  rcases fullG h with ⟨g, hg⟩
  rcases fullF g with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  -- Need: hGF.map f = h, where hGF.map f should be hG.map (hF.map f) = hG.map g = h
  -- Works when hGF = compFunctor
  sorry

end Composition

/-! ## Strong equivalence (§1.32) -/

structure NatTrans (F G : 𝒞 → 𝒟) [hF : Functor F] [hG : Functor G] where
  app : ∀ X : 𝒞, F X ⟶ G X
  naturality : ∀ ⦃X Y : 𝒞⦄ (f : X ⟶ Y), hF.map f ≫ app Y = app X ≫ hG.map f

structure NatIso (F G : 𝒞 → 𝒟) [hF : Functor F] [hG : Functor G] where
  nat : NatTrans F G
  isIso : ∀ X : 𝒞, IsIso (nat.app X)

structure StrongEquivalence (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞)
    [hF : Functor F] [hG : Functor G]
    [hGF : Functor (G ∘ F)] [hFG : Functor (F ∘ G)]
    [hIdC : Functor (λ X : 𝒞 => X)] [hIdD : Functor (λ X : 𝒟 => X)] where
  unit : Nonempty (NatIso (G ∘ F) (λ X : 𝒞 => X))
  counit : Nonempty (NatIso (F ∘ G) (λ X : 𝒟 => X))

end Freyd
