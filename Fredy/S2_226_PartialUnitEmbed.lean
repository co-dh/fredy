/-
  Freyd & Scedrov, *Categories and Allegories* §2.226 — embedding a set of partial
  units in a single partial unit.

  §2.226 (the partial-unit-embedding statement).  In a GLOBALLY COMPLETE allegory in
  which equivalence relations split, for every set of partial units there is a partial
  unit in which they may all be embedded.

  BOOK PROOF (verbatim):  "Every object has a maximal endomorphism which is necessarily
  an equivalence relation.  If `M` is a maximal endomorphism and if `ff° = M`, `f°f = 1`,
  then the target of `f` is a partial unit.  Given any set of partial units we may apply
  this construction to their coproduct.  Hence for every set of partial units there is a
  partial unit in which they may all be embedded."

  CONSTRUCTION (mapping the book onto the repo machinery):

  1.  Form the COPRODUCT `Π = ⊕_j π_j` of the family with injections `Uⱼ : πⱼ → Π`.  In a
      `GloballyCompleteAllegory` this is `GloballyCompleteAllegory.disjointUnion`; the
      injections are MAPS (`IndexedDisjointUnion.inject_map`).
  2.  `M = topEndo Π` is the MAXIMAL ENDOMORPHISM (the top `⋃` of the complete hom-lattice
      `Π ⟶ Π`).  It is reflexive, symmetric, idempotent — an equivalence relation.
  3.  Split it (`hsplit`): a map `f : Π → ρ` with `f f° = M`, `f° f = 1_ρ`.
  4.  `ρ` is a PARTIAL UNIT (`target_max_partialUnit`).
  5.  The embedding `πⱼ → ρ` is `Uⱼ ≫ f`, a map (composite of maps), hence the embedding.

  This is the GLOBALLY-COMPLETE analogue of §2.423 (`S2_423_ConnectedUnit.lean`), which
  ran the same argument in a power allegory with `maxEndo = 1_α / 0_α`.  Here there is no
  division: the maximal endomorphism is the lattice top `Sup`, and the partial-unit step is
  recast on a maximality hypothesis `hMax` (Freyd's actual argument) instead of the
  division-specific `maxEndo`.  `hsplit` is §2.423's own "equivalence relations split"
  hypothesis (`EffectiveAllegory.split_symmetric_idempotent`).

  Conventions: diagram-order composition `≫`, reciprocation `°`, intersection `∩`,
  union/supremum `Sup`, order `⊑`, bottom `𝟘`.  Strictly mathlib-free.
-/

import Fredy.S2_22_Completions

universe v u

namespace Freyd.Alg

open Cat
open LocallyCompleteDistributiveAllegory

section LCDA

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-! ## §2.226  The maximal endomorphism as the lattice top -/

/-- §2.226: the MAXIMAL ENDOMORPHISM of `α` — the union `⋃` of every endomorphism, i.e. the
    top of the complete hom-lattice `α ⟶ α`.  This is the completeness analogue of §2.423's
    `maxEndo α = 1_α / 0_α`; in a globally (hence locally) complete allegory the maximal
    endomorphism is available without division. -/
def topEndo (α : 𝒜) : α ⟶ α := Sup (fun _ : α ⟶ α => True)

/-- §2.226: `topEndo α` is maximal — every `R : α → α` satisfies `R ⊑ topEndo α`. -/
theorem topEndo_max {α : 𝒜} (R : α ⟶ α) : R ⊑ topEndo α := le_Sup trivial

/-- §2.226: the maximal endomorphism is reflexive (`1 ⊑ M`). -/
theorem topEndo_reflexive {α : 𝒜} : Reflexive (topEndo α) := topEndo_max (Cat.id α)

/-- §2.226: the maximal endomorphism is symmetric (`M° ⊑ M`, since `M°` is also an
    endomorphism and `M` is maximal). -/
theorem topEndo_symmetric {α : 𝒜} : Symmetric (topEndo α) := topEndo_max ((topEndo α)°)

/-- §2.226: the maximal endomorphism is idempotent (`M M = M`): reflexive + transitive,
    transitivity `M M ⊑ M` being maximality.  So `M` is an equivalence relation. -/
theorem topEndo_idempotent {α : 𝒜} : (topEndo α) ≫ (topEndo α) = topEndo α :=
  reflexive_transitive_idempotent topEndo_reflexive (topEndo_max _)

/-! ## §2.226  Disjoint-union injections are maps -/

/-- The injections `Uᵢ : αᵢ → β` of a §2.223 disjoint union are MAPS.

    ENTIRE: `dom Uᵢ = 1_{αᵢ} ∩ Uᵢ Uᵢ° = 1_{αᵢ} ∩ 1_{αᵢ} = 1_{αᵢ}` (`self : Uᵢ Uᵢ° = 1`).
    SIMPLE: `Uᵢ° Uᵢ ⊑ ⋃ⱼ Uⱼ° Uⱼ = 1_β` (`complete`). -/
theorem IndexedDisjointUnion.inject_map {I : Type u} {α : I → 𝒜} {β : 𝒜}
    (du : IndexedDisjointUnion α β) (i : I) : Map (du.U i) := by
  refine ⟨?_, ?_⟩
  · -- Entire: dom (Uᵢ) = 1
    show dom (du.U i) = Cat.id (α i)
    dsimp [dom]
    rw [du.self i, Allegory.inter_idem]
  · -- Simple: Uᵢ° Uᵢ ⊑ 1_β
    show (du.U i)° ≫ du.U i ⊑ Cat.id β
    exact le_trans (le_Sup ⟨i, rfl⟩) (le_of_eq' du.complete)

/-! ## §2.226  The partial-unit step

  The book's "if `M` is a maximal endomorphism and `ff° = M`, `f°f = 1` then the target of
  `f` is a partial unit".  This duplicates the algebra of §2.423's `target_split_partialUnit`,
  but parametrised on a MAXIMALITY hypothesis `hMax` rather than the division-specific
  `maxEndo = 1/0`: §2.226 lives in a globally complete (non-division) allegory, where the
  maximal endomorphism is the lattice top.  (Do not dedup this back into the division
  version — the two run in different ambient structures.) -/

/-- §2.226 (partial-unit step).  If `M : α → α` is MAXIMAL (`∀ R, R ⊑ M`) and a map
    `f : α → β` splits it — `f f° = M`, `f° f = 1_β` — then its target `β` is a PARTIAL UNIT.

    Book chain: `R = f° (f R f°) f ⊑ f° M f = f° f f° f = 1_β`, using `f R f° ⊑ M`
    (maximality) for the inequality and `M = f f°`, `f° f = 1_β` for the equalities. -/
theorem target_max_partialUnit {α β : 𝒜} (M : α ⟶ α) (hMax : ∀ R : α ⟶ α, R ⊑ M)
    (f : α ⟶ β) (hff : f ≫ f° = M) (hf'f : f° ≫ f = Cat.id β) :
    PartialUnit β := by
  intro R
  -- f R f° ⊑ M  (every endo of α is below the maximal one)
  have hmax : (f ≫ R ≫ f°) ⊑ M := hMax _
  -- f° (f R f°) f ⊑ f° M f
  have h1 : f° ≫ (f ≫ R ≫ f°) ≫ f ⊑ f° ≫ M ≫ f :=
    comp_mono_left f° (comp_mono_right hmax f)
  -- f° M f = f° (f f°) f = (f° f)(f° f) = 1_β
  have h2 : f° ≫ M ≫ f = Cat.id β := by
    rw [← hff, Cat.assoc, hf'f, Cat.comp_id, hf'f]
  -- f° (f R f°) f = (f° f) R (f° f) = R
  have hXeq : f° ≫ (f ≫ R ≫ f°) ≫ f = R := by
    rw [Cat.assoc f (R ≫ f°) f, ← Cat.assoc f° f ((R ≫ f°) ≫ f), hf'f, Cat.id_comp,
        Cat.assoc R f° f, hf'f, Cat.comp_id]
  have hle : f° ≫ (f ≫ R ≫ f°) ≫ f ⊑ Cat.id β := h2 ▸ h1
  rwa [hXeq] at hle

end LCDA

/-! ## §2.226  Partial units embed in a single partial unit -/

section GloballyComplete

variable {𝒜 : Type u} [GloballyCompleteAllegory 𝒜]

/-- **§2.226.**  In a GLOBALLY COMPLETE allegory in which equivalence relations split, for
    every set of partial units there is a PARTIAL UNIT in which they may all be embedded.

    HYPOTHESIS-GATED on `hsplit` — every equivalence relation splits with an entire leg.
    This is §2.423's own hypothesis (Freyd's "coreflexives split" with §2.422), precisely
    `EffectiveAllegory.split_symmetric_idempotent`.

    The construction works for any family of objects; `_hπ` records that the family is a set
    of partial units (Freyd's §2.226 framing), but is not needed — the embedded objects need
    not be partial units for the embedding into the partial unit `ρ` to exist. -/
theorem partialUnits_embed_in_partialUnit
    {J : Type u} (π : J → 𝒜) (_hπ : ∀ j, PartialUnit (π j))
    (hsplit : ∀ {a : 𝒜} (E : a ⟶ a), Reflexive E → Symmetric E → E ≫ E = E →
       ∃ (b : 𝒜) (g : a ⟶ b), Map g ∧ g ≫ g° = E ∧ g° ≫ g = Cat.id b) :
    ∃ (ρ : 𝒜), PartialUnit ρ ∧ ∀ j, ∃ (e : π j ⟶ ρ), Map e := by
  -- 1. The coproduct Π = ⊕_j π_j with its injections U_j (maps).
  let du := GloballyCompleteAllegory.toIndexedDisjointUnion π
  -- 2-3. M = topEndo Π is an equivalence relation; split it: f : Π → ρ, f f° = M, f° f = 1_ρ.
  obtain ⟨ρ, f, hf, hff, hf'f⟩ :=
    hsplit (topEndo (GloballyCompleteAllegory.disjointUnion π))
      topEndo_reflexive topEndo_symmetric topEndo_idempotent
  -- 4. ρ is a partial unit, and 5. each U_j ≫ f : π_j → ρ is a map (the embedding).
  refine ⟨ρ, target_max_partialUnit _ topEndo_max f hff hf'f, fun j => ?_⟩
  exact ⟨du.U j ≫ f, map_comp (du.inject_map j) hf⟩

end GloballyComplete

end Freyd.Alg
