/-
  Freyd & Scedrov, *Categories and Allegories* §1.34–§1.341
  Isomorphic objects, equinumerosity, isomorphism classes.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31
import Fredy.S1_41

set_option linter.unusedSectionVars false

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.34 Isomorphic objects -/

/-- Objects A and B are ISOMORPHIC (A ≅ B) if there exists an iso A → B. -/
def Isomorphic (A B : 𝒞) : Prop := ∃ (f : A ⟶ B), IsIso f

/-- Isomorphic is reflexive. -/
theorem isomorphic_refl (A : 𝒞) : Isomorphic A A :=
  ⟨Cat.id A, ⟨Cat.id A, Cat.id_comp _, Cat.id_comp _⟩⟩

/-- Isomorphic is symmetric. -/
theorem isomorphic_symm {A B : 𝒞} (h : Isomorphic A B) : Isomorphic B A := by
  rcases h with ⟨f, g, hfg, hgf⟩
  exact ⟨g, f, hgf, hfg⟩

/-- Isomorphic is transitive. -/
theorem isomorphic_trans {A B C : 𝒞} (hAB : Isomorphic A B) (hBC : Isomorphic B C) : Isomorphic A C := by
  rcases hAB with ⟨f, gf, hf1, hf2⟩
  rcases hBC with ⟨g, gg, hg1, hg2⟩
  exact ⟨f ≫ g, gg ≫ gf, by simp [Cat.assoc, hf1, hg1], by simp [Cat.assoc, hf2, hg2]⟩

/-- Functors preserve isomorphic objects. -/
theorem functor_preserves_iso_obj (F : 𝒞 → 𝒟) [hF : Functor F] {A B : 𝒞}
    (h : Isomorphic A B) : Isomorphic (F A) (F B) := by
  rcases h with ⟨f, g, hfg, hgf⟩
  exact functor_preserves_iso f ⟨g, hfg, hgf⟩

/-- Full embeddings reflect isomorphism of objects. -/
theorem full_embedding_reflects_iso_obj (F : 𝒞 → 𝒟) [hF : Functor F]
    (hEmb : IsEmbedding F) (hFull : IsFull F) {A B : 𝒞} (h : Isomorphic (F A) (F B)) : Isomorphic A B := by
  rcases h with ⟨h, ginv, h1, h2⟩
  rcases hFull h with ⟨f, hf⟩
  rcases hFull ginv with ⟨g, hg⟩
  refine ⟨f, g, ?_, ?_⟩
  · apply hEmb
    calc
      hF.map (f ≫ g) = hF.map f ≫ hF.map g := hF.map_comp _ _
      _ = h ≫ ginv := by rw [hf, hg]
      _ = Cat.id (F A) := h1
      _ = hF.map (Cat.id A) := (hF.map_id _).symm
  · apply hEmb
    calc
      hF.map (g ≫ f) = hF.map g ≫ hF.map f := hF.map_comp _ _
      _ = ginv ≫ h := by rw [hg, hf]
      _ = Cat.id (F B) := h2
      _ = hF.map (Cat.id B) := (hF.map_id _).symm

/-! ## §1.341 Equinumerosity and axiom of choice -/

-- (The axiom-of-choice equivalence of §1.341 is not formalised; it requires set-theoretic
--  equinumerosity that lies outside the scope of this categorical formalisation.)

end Freyd
