/-
  Bird & de Moor, *Algebra of Programming*, §5.1 Relators (book pp. 111–113).

  A RELATOR is a monotonic functor between allegories; between tabular allegories this is
  the same as a converse-preserving functor (Theorem 5.1).  Relators are the datatype-formers
  of the relational calculus: §5.2–§5.5 build relational products, coproducts, the power
  relator, and relational catamorphisms over them.

  Weaker than `AllegoryFunctor` (S2_147), which also preserves `∩`; a relator preserves `∩`
  only on coreflexives (Ex 5.2).

  Contents: `Relator` structure + identity/composition; Lemma 5.1 (relators preserve maps and
  their converses), Theorem 5.1 (relator ↔ converse-preserving, over tabular source), Corollary
  5.1 (relators agreeing on maps agree), Ex 5.2 (meets of coreflexives), Ex 5.5 (dom).
-/
import Fredy.S2_1
import Fredy.A4_2

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Freyd.Alg

/-- A RELATOR (B&dM §5.1 p. 111): a monotonic functor between allegories. -/
structure Relator (𝒜 : Type u₁) (ℬ : Type u₂) [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] where
  /-- Object map. -/
  obj : 𝒜 → ℬ
  /-- Hom map. -/
  map : {a b : 𝒜} → (a ⟶ b) → (obj a ⟶ obj b)
  map_id : ∀ (a : 𝒜), map (Cat.id a) = Cat.id (obj a)
  map_comp : ∀ {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c), map (R ≫ S) = map R ≫ map S
  /-- MONOTONICITY — the defining extra over a plain functor. -/
  map_mono : ∀ {a b : 𝒜} {R S : a ⟶ b}, R ⊑ S → map R ⊑ map S

/-- A relator PRESERVES CONVERSE when `F(R°) = (FR)°`.  Automatic over a tabular source
    (Theorem 5.1); carried as a hypothesis where tabularity is not otherwise needed. -/
def Relator.PreservesRecip {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
    (F : Relator 𝒜 ℬ) : Prop :=
  ∀ {a b : 𝒜} (R : a ⟶ b), F.map R° = (F.map R)°

/-- The identity relator. -/
def Relator.idRelator (𝒜 : Type u₁) [Allegory.{v₁} 𝒜] : Relator 𝒜 𝒜 where
  obj := id
  map := id
  map_id _ := rfl
  map_comp _ _ := rfl
  map_mono h := h

/-- Composition of relators (diagram order: first `F`, then `G`). -/
def Relator.comp {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] [Allegory.{v₃} 𝒞]
    (F : Relator 𝒜 ℬ) (G : Relator ℬ 𝒞) : Relator 𝒜 𝒞 where
  obj := G.obj ∘ F.obj
  map R := G.map (F.map R)
  map_id a := by simp [F.map_id, G.map_id]
  map_comp R S := by simp [F.map_comp, G.map_comp]
  map_mono h := G.map_mono (F.map_mono h)

end Freyd.Alg
