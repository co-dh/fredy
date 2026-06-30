/-
  Freyd & Scedrov, *Categories and Allegories* §2.551 (algebraic core).

  > 2.551. Disjoint unions in a globally complete allegory coincide with
  > coproducts (AND WITH PRODUCTS) [2.223, 2.214] ...

  `Fredy/S2_223_CoproductConverse.lean` together with `IndexedDisjointUnion.isCoproduct`
  (S2_22_Completions) establishes the COPRODUCT coincidence (both directions).  This
  file adds the PRODUCT coincidence, the other half of the §2.551 citation: a disjoint
  union is an indexed PRODUCT with projections the reciprocals `Uᵢ°` of its injections.

  This is the indexed instance of Freyd's §2.215 reciprocal duality ("any allegory is
  isomorphic, via reciprocation, to its opposite; `⟨U₁,U₂⟩` is a coproduct iff
  `⟨U₁°,U₂°⟩` is a product"): the product universal property for `(Uᵢ°)` is the
  coproduct universal property for `(Uᵢ)` read through `(·)°`.

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`.  Mathlib-free.
-/

import Fredy.S2_223_CoproductConverse

universe v u

namespace Freyd.Alg

open Cat

section LCDAProduct

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
variable {I : Type u} {α : I → 𝒜} {β : 𝒜}

/-- The indexed PRODUCT universal property for projections `p : ∀ i, β ⟶ αᵢ`
    (§2.215/§2.551, the reciprocal dual of `IsIndexedCoproduct`): every family
    `{Rᵢ : c → αᵢ}` factors uniquely through the projections. -/
def IsIndexedProduct (p : (i : I) → β ⟶ α i) : Prop :=
  ∀ (c : 𝒜) (R : (i : I) → c ⟶ α i),
    ∃ M : c ⟶ β, (∀ i, M ≫ p i = R i) ∧
      (∀ M' : c ⟶ β, (∀ i, M' ≫ p i = R i) → M' = M)

/-- **§2.551 (product coincidence).**  A disjoint union is an indexed PRODUCT with
    projections `Uᵢ°`.  By §2.215 reciprocal duality, the product mediator of a family
    `{Rᵢ : c → αᵢ}` is `N°`, where `N : β → c` is the coproduct mediator of the
    reciprocated family `{Rᵢ° : αᵢ → c}` (`IndexedDisjointUnion.isCoproduct`):
      `N° ≫ Uᵢ° = (Uᵢ ≫ N)° = (Rᵢ°)° = Rᵢ`,
    and uniqueness reciprocates the coproduct's. -/
theorem IndexedDisjointUnion.isProduct (du : IndexedDisjointUnion α β) :
    IsIndexedProduct (fun i => (du.U i)°) := by
  intro c R
  -- Coproduct mediator `N : β → c` of the reciprocated family `Rᵢ° : αᵢ → c`.
  obtain ⟨N, hN, hNuniq⟩ := du.isCoproduct c (fun i => (R i)°)
  refine ⟨N°, ?_, ?_⟩
  · -- `N° ≫ Uᵢ° = (Uᵢ ≫ N)° = (Rᵢ°)° = Rᵢ`.
    intro i
    rw [← Allegory.recip_comp, hN i, Allegory.recip_recip]
  · -- Uniqueness: `M' ≫ Uᵢ° = Rᵢ ⟹ Uᵢ ≫ M'° = Rᵢ° ⟹ M'° = N ⟹ M' = N°`.
    intro M' hM'
    have hM'rec : ∀ i, du.U i ≫ M'° = (R i)° := by
      intro i
      have hi : M' ≫ (du.U i)° = R i := hM' i
      rw [← hi, Allegory.recip_comp, Allegory.recip_recip]
    have : M'° = N := hNuniq M'° hM'rec
    rw [← Allegory.recip_recip M', this]

end LCDAProduct

end Freyd.Alg
