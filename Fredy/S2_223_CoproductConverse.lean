/-
  Freyd & Scedrov, *Categories and Allegories* — §2.223 (CONVERSE direction).

  `Fredy/S2_22_Completions.lean` proves the FORWARD half of §2.223: a disjoint
  union (a `IndexedDisjointUnion` datum) is an indexed coproduct, i.e. its
  injections enjoy the universal mapping property
  (`IndexedDisjointUnion.isCoproduct`).

  Here we prove the CONVERSE: an indexed family of injections `U : ∀ i, αᵢ → β`
  that enjoys the indexed COPRODUCT universal property (`IsIndexedCoproduct U`)
  is a disjoint union — it satisfies the three §2.223 equations

      `Uᵢ Uᵢ° = 1`,   `Uᵢ Uⱼ° = 0  (i ≠ j)`,   `⋃ᵢ Uᵢ° Uᵢ = 1`.

  This is the indexed extension of the binary `coproduct_of_universal_eqs`
  (`Fredy/S2_2.lean`).  The argument is the same:

  1. For each `i`, the universal property applied to the DELTA family
     `Δⁱ : (j) ↦ (if j = i then 1 else 0) : αⱼ → αᵢ` gives a mediator
     `pᵢ : β → αᵢ` with `Uᵢ pᵢ = 1` and `Uⱼ pᵢ = 0  (j ≠ i)`.
  2. Completeness: the universal property applied to the family `U` itself has a
     unique mediator; both `1_β` and `⋃ᵢ pᵢ Uᵢ` mediate it, so `⋃ᵢ pᵢ Uᵢ = 1`.
  3. Hence `pᵢ Uᵢ ⊑ 1`, and with `Uᵢ pᵢ = 1` the lemma `eq_recip_of_section`
     gives `pᵢ = Uᵢ°`.
  4. Rewriting `Uᵢ° = pᵢ` reads off the three equations.

  The delta family is encoded with the propositional `j = i` + `HEq` idiom (the
  same one used by `globalId` in `Fredy/S2_224_GlobalCompletion.lean`), so no
  `DecidableEq I` is needed.  Conventions: diagram-order composition `R ≫ S`,
  reciprocation `R°`, union `R ∪ S`, order `R ⊑ S`, supremum `Sup P`, bottom `𝟘`.
  Strictly mathlib-free.
-/

import Fredy.S2_22_Completions

universe v u

namespace Freyd.Alg

open Cat
open LocallyCompleteDistributiveAllegory

section LCDAConverse

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
variable {I : Type u} {α : I → 𝒜} {β : 𝒜}

/-- The `(i, j)` entry of the DELTA family: `1 : αⱼ → αᵢ` when `j = i`, else `0`.
    Encoded as a `Sup` over the propositional `j = i` + `HEq` to the identity, so
    no `DecidableEq I` is required (cf. `globalId`). -/
def deltaFamEntry (i j : I) : α j ⟶ α i :=
  Sup (fun T : α j ⟶ α i => ∃ (_ : j = i), HEq T (Cat.id (α i)))

/-- The diagonal entry of the delta family is the identity. -/
theorem deltaFamEntry_diag (i : I) : deltaFamEntry (α := α) i i = Cat.id (α i) := by
  apply le_antisymm
  · apply Sup_le; rintro T ⟨_, hT⟩; exact le_of_eq' (eq_of_heq hT)
  · exact le_Sup ⟨rfl, HEq.refl _⟩

/-- An off-diagonal entry of the delta family is `𝟘`. -/
theorem deltaFamEntry_off (i j : I) (hji : j ≠ i) :
    deltaFamEntry (α := α) i j = (𝟘 : α j ⟶ α i) := by
  apply le_antisymm
  · apply Sup_le; rintro T ⟨heq, _⟩; exact absurd heq hji
  · exact zero_le _

/-- **§2.223 (converse).**  An indexed family of injections `U : ∀ i, αᵢ → β` that
    enjoys the indexed COPRODUCT universal property is a DISJOINT UNION: it
    satisfies the three §2.223 equations
    `Uᵢ Uᵢ° = 1`, `Uᵢ Uⱼ° = 0 (i ≠ j)`, `⋃ᵢ Uᵢ° Uᵢ = 1`. -/
theorem indexedCoproduct_to_disjointUnion
    (U : (i : I) → α i ⟶ β) (h : IsIndexedCoproduct U) :
    (∀ i, U i ≫ (U i)° = Cat.id (α i)) ∧
    (∀ {i j : I}, i ≠ j → U i ≫ (U j)° = (𝟘 : α i ⟶ α j)) ∧
    (Sup (fun R : β ⟶ β => ∃ i, R = (U i)° ≫ U i) = Cat.id β) := by
  -- Step 1: per-`i` mediator `p i` of the delta family `Δⁱ`.
  have hp_all : ∀ i, ∃ M : β ⟶ α i, ∀ j, U j ≫ M = deltaFamEntry (α := α) i j := by
    intro i
    obtain ⟨M, hM, _⟩ := h (α i) (fun j => deltaFamEntry (α := α) i j)
    exact ⟨M, hM⟩
  let p : (i : I) → β ⟶ α i := fun i => Classical.choose (hp_all i)
  have hp : ∀ (i j : I), U j ≫ p i = deltaFamEntry (α := α) i j :=
    fun i => Classical.choose_spec (hp_all i)
  -- `U i ≫ p i = 1`  and  `U j ≫ p i = 0`  for `j ≠ i`.
  have hUp : ∀ i, U i ≫ p i = Cat.id (α i) :=
    fun i => (hp i i).trans (deltaFamEntry_diag i)
  have hUp_off : ∀ i j, j ≠ i → U j ≫ p i = (𝟘 : α j ⟶ α i) :=
    fun i j hji => (hp i j).trans (deltaFamEntry_off i j hji)
  -- Step 2: completeness `⋃ᵢ p i ≫ U i = 1_β`, by uniqueness of the mediator of `U`.
  obtain ⟨R0, _, hR0uniq⟩ := h β U
  have hSum : Sup (fun T : β ⟶ β => ∃ i, T = p i ≫ U i) = Cat.id β := by
    have hsum_med : ∀ j, U j ≫ Sup (fun T : β ⟶ β => ∃ i, T = p i ≫ U i) = U j := by
      intro j
      rw [comp_Sup_distrib]
      apply le_antisymm
      · apply Sup_le
        rintro T ⟨S, ⟨i, rfl⟩, rfl⟩
        by_cases hij : i = j
        · subst hij
          exact le_of_eq' (by rw [← Cat.assoc, hUp i, Cat.id_comp])
        · have h0 : U j ≫ (p i ≫ U i) = (𝟘 : α j ⟶ β) := by
            rw [← Cat.assoc, hUp_off i j (Ne.symm hij), DistributiveAllegory.zero_comp]
          rw [h0]; exact zero_le _
      · apply le_Sup
        exact ⟨p j ≫ U j, ⟨j, rfl⟩, by rw [← Cat.assoc, hUp j, Cat.id_comp]⟩
    have h1 : Sup (fun T : β ⟶ β => ∃ i, T = p i ≫ U i) = R0 := hR0uniq _ hsum_med
    have h2 : Cat.id β = R0 := hR0uniq _ (fun i => Cat.comp_id (U i))
    rw [h1, ← h2]
  -- Step 3: `p i ≫ U i ⊑ 1`, hence `U i° = p i`.
  have hpU_le : ∀ i, p i ≫ U i ⊑ Cat.id β := fun i => by
    have hle := le_Sup (P := fun T : β ⟶ β => ∃ i, T = p i ≫ U i)
      (R := p i ≫ U i) ⟨i, rfl⟩
    rwa [hSum] at hle
  have hpe : ∀ i, (U i)° = p i :=
    fun i => (eq_recip_of_section (U i) (p i) (hUp i) (hpU_le i)).symm
  -- Step 4: read off the three equations.
  refine ⟨fun i => by rw [hpe i]; exact hUp i, ?_, ?_⟩
  · intro i j hij
    rw [hpe j]; exact hUp_off j i hij
  · have hcongr : Sup (fun R : β ⟶ β => ∃ i, R = (U i)° ≫ U i)
        = Sup (fun T : β ⟶ β => ∃ i, T = p i ≫ U i) := by
      apply Sup_congr; intro T; constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, by rw [hpe i]⟩
      · rintro ⟨i, rfl⟩; exact ⟨i, by rw [hpe i]⟩
    rw [hcongr, hSum]

/-- **§2.223 (converse), packaged.**  Repackage the universal property as the
    `IndexedDisjointUnion` datum it determines. -/
def IsIndexedCoproduct.toDisjointUnion
    (U : (i : I) → α i ⟶ β) (h : IsIndexedCoproduct U) :
    IndexedDisjointUnion α β where
  U := U
  self := (indexedCoproduct_to_disjointUnion U h).1
  cross := (indexedCoproduct_to_disjointUnion U h).2.1
  complete := (indexedCoproduct_to_disjointUnion U h).2.2

end LCDAConverse

end Freyd.Alg
