/-
  Freyd & Scedrov, *Categories and Allegories* §1.31–§1.32
  Embedding, Full, Representative Image, Equivalence Functor,
  Strong equivalence.  Proofs assuming composed functor = compFunctor.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_27
import Fredy.S1_41


open Freyd

universe v u u₁ u₂

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.31 Embedding, Full, Representative Image, Equivalence Functor -/

def Embedding (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B), hF.map f = hF.map g → f = g

/-- The cross-universe form of `Embedding`: `T` SEPARATES MAPS if it is injective
    on each hom-set.  Same notion as `Embedding`, but with source and target in
    possibly different object universes — needed for representations `𝒞 → 𝒮^I`
    whose target lives one universe up (§1.55 Henkin-Lubkin). -/
def SeparatesMaps {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D]
    (T : C → D) [hT : Functor T] : Prop :=
  ∀ {A B : C} (f g : A ⟶ B), hT.map f = hT.map g → f = g

def Full (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  ∀ {A B : 𝒞} (h : F A ⟶ F B), ∃ f : A ⟶ B, hF.map f = h

def HasRepresentativeImage (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  ∀ B : 𝒟, ∃ A : 𝒞, ∃ (h : F A ⟶ B), IsIso h

def EquivalenceFunctor (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  Embedding F ∧ Full F ∧ HasRepresentativeImage F

/-! ## §1.32 Composition and cancellation

  Embedding ∘ embedding = embedding; full ∘ full = full.
  With `hGF := compFunctor hF hG`, these are definitional. -/

section Composition
variable {F : 𝒞 → 𝒟} [hF : Functor F] {ℰ : Type u} [Cat.{v} ℰ] {G : 𝒟 → ℰ} [hG : Functor G]

theorem embedding_comp (embF : Embedding F) (embG : Embedding G) : Embedding (G ∘ F) := by
  intro A B f g h
  -- h : (compFunctor.map : (G ∘ F) A → (G ∘ F) B) f = (compFunctor.map ...) g
  -- h reduces to hG.map (hF.map f) = hG.map (hF.map g)
  apply embF f g
  apply embG (hF.map f) (hF.map g)
  simpa using h

theorem full_comp (fullF : Full F) (fullG : Full G) : Full (G ∘ F) := by
  intro A B h
  rcases fullG h with ⟨g, hg⟩
  rcases fullF g with ⟨f, hf⟩
  have hgoal : (compFunctor (hf := hF) (hg := hG)).map f = h := by
    calc
      (compFunctor (hf := hF) (hg := hG)).map f = hG.map (hF.map f) := rfl
      _ = hG.map g := by rw [hf]
      _ = h := by rw [hg]
  exact ⟨f, hgoal⟩

end Composition

/-! ## Strong equivalence (§1.32) -/

structure NatIso (F G : 𝒞 → 𝒟) [hF : Functor F] [hG : Functor G] where
  nat : NaturalTransformation F G
  isIso : ∀ X : 𝒞, IsIso (nat.app X)

structure StrongEquivalence (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞)
    [hF : Functor F] [hG : Functor G] where
  unit : Nonempty (NatIso (G ∘ F) (λ X : 𝒞 => X))
  counit : Nonempty (NatIso (F ∘ G) (λ X : 𝒟 => X))

end Freyd
