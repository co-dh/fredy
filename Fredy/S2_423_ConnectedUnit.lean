/-
  Freyd & Scedrov, *Categories and Allegories* §2.423.

  §2.423  If A is a connected power allegory in which coreflexives split then it has
          a unit.

  BECAUSE (Freyd): given an object α define the maximal endomorphism M = 1_α / 0_α of
  (α,α).  M is reflexive, symmetric and idempotent (an equivalence relation), so in a
  power allegory in which coreflexives split it splits — there is a map f : α → β with
  f f° = M and f° f = 1_β.  Its target β is a PARTIAL UNIT: for every R : β → β,

        R = f° (f R f°) f ⊑ f° M f = f° f f° f = 1_β

  (the middle step because f R f° ⊑ M is maximal).  Connectivity (which in any allegory
  implies strong connectivity) gives every object a map to α; composing with f gives every
  object a map to β, so β is a UNIT.

  Steps 1 and 2 (`maxEndo_max`, `target_split_partialUnit`) are UNCONDITIONAL pure algebra
  over a `DivisionAllegory`.  Step 3 (`connected_power_coreflexivesSplit_has_unit`) is
  HYPOTHESIS-GATED: it takes strong connectivity (`hconn`) and the splitting of equivalence
  relations (`hsplit`) as named hypotheses.  `hsplit` is exactly Freyd's
  "coreflexives split" combined with §2.422 (in a power allegory every equivalence relation
  is of the form `f f°`); §2.422 is not yet formalised here, so it is left as a hypothesis —
  it coincides with the field `EffectiveAllegory.split_symmetric_idempotent`.
-/

import Fredy.S2_4

universe v u

namespace Freyd.Alg

/-! ## §2.423  The maximal endomorphism `M = 1_α / 0_α` -/

section Division
variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- §2.423: the MAXIMAL endomorphism `M = 1_α / 0_α` of `(α,α)`. -/
def maxEndo (α : 𝒜) : α ⟶ α := Cat.id α / 𝟘

/-- §2.423: `M = 1_α / 0_α` is maximal in `(α,α)`: every `R : α → α` satisfies `R ⊑ M`.
    `R ⊑ 1/0 ↔ R≫0 ⊑ 1`, and `R≫0 = 0 ⊑ 1` holds always. -/
theorem maxEndo_max {α : 𝒜} (R : α ⟶ α) : R ⊑ maxEndo α := by
  apply (le_div_iff R (Cat.id α) (𝟘 : α ⟶ α)).mpr
  rw [DistributiveAllegory.comp_zero]
  exact zero_le _

/-- §2.423 (the partial-unit step, pure algebra).  If `f : α → β` splits the maximal
    endomorphism `M = 1_α/0_α` — `f f° = M` and `f° f = 1_β` — then its target `β` is a
    PARTIAL UNIT: every `R : β → β` satisfies `R ⊑ 1_β`.

    Book chain: `R = f° (f R f°) f ⊑ f° M f = f° f f° f = 1_β`, using `f R f° ⊑ M`
    (maximality) for the inequality and `M = f f°`, `f° f = 1_β` for the equalities. -/
theorem target_split_partialUnit {α β : 𝒜} (f : α ⟶ β)
    (hff : f ≫ f° = maxEndo α) (hf'f : f° ≫ f = Cat.id β) :
    PartialUnit β := by
  intro R
  -- f R f° ⊑ M  (every endo of α is below the maximal one)
  have hmax : (f ≫ R ≫ f°) ⊑ maxEndo α := maxEndo_max _
  -- f° (f R f°) f ⊑ f° M f
  have h1 : f° ≫ (f ≫ R ≫ f°) ≫ f ⊑ f° ≫ maxEndo α ≫ f :=
    comp_mono_left f° (comp_mono_right hmax f)
  -- f° M f = f° (f f°) f = (f° f)(f° f) = 1_β
  have h2 : f° ≫ maxEndo α ≫ f = Cat.id β := by
    rw [← hff, Cat.assoc, hf'f, Cat.comp_id, hf'f]
  -- f° (f R f°) f = (f° f) R (f° f) = R
  have hXeq : f° ≫ (f ≫ R ≫ f°) ≫ f = R := by
    rw [Cat.assoc f (R ≫ f°) f, ← Cat.assoc f° f ((R ≫ f°) ≫ f), hf'f, Cat.id_comp,
        Cat.assoc R f° f, hf'f, Cat.comp_id]
  have hle : f° ≫ (f ≫ R ≫ f°) ≫ f ⊑ Cat.id β := h2 ▸ h1
  rwa [hXeq] at hle

end Division

/-! ## §2.423  Strong connectivity -/

/-- §2.423: an allegory is STRONGLY CONNECTED if every object has a MAP to every object.
    Freyd: connectivity in any allegory implies strong connectivity, so this is the working
    form of "connected". -/
def StronglyConnectedAllegory (𝒜 : Type u) [Allegory 𝒜] : Prop :=
  ∀ (a b : 𝒜), ∃ (g : a ⟶ b), Map g

/-! ## §2.423  A connected power allegory in which coreflexives split has a unit -/

section Power
variable {𝒜 : Type u} [PowerAllegory 𝒜]

/-- **§2.423**: a CONNECTED POWER ALLEGORY in which coreflexives split has a UNIT.

    HYPOTHESIS-GATED on:
    * `hconn` — strong connectivity (Freyd's connectivity implies it);
    * `hsplit` — every equivalence relation splits with an entire leg.  In a power allegory
      this is Freyd's "coreflexives split" together with §2.422 (every equivalence relation
      is `f f°`); it is precisely `EffectiveAllegory.split_symmetric_idempotent`.

    Construction: split the maximal endomorphism `M = 1_α/0_α` (an equivalence relation) to
    get a map `f : α → π` with `f f° = M`, `f° f = 1_π`; then `π` is a partial unit
    (`target_split_partialUnit`) and connectivity gives every object a map to `π`. -/
theorem connected_power_coreflexivesSplit_has_unit
    (hconn : StronglyConnectedAllegory 𝒜)
    (hsplit : ∀ {a : 𝒜} (E : a ⟶ a), Reflexive E → Symmetric E → E ≫ E = E →
       ∃ (b : 𝒜) (g : a ⟶ b), Map g ∧ g ≫ g° = E ∧ g° ≫ g = Cat.id b)
    (α : 𝒜) :
    ∃ (π : 𝒜), IsUnit π := by
  -- M = 1_α/0_α is reflexive, symmetric, idempotent (an equivalence relation).
  have hRefl : Reflexive (maxEndo α) := maxEndo_max (Cat.id α)
  have hSym : Symmetric (maxEndo α) := maxEndo_max ((maxEndo α)°)
  have hIdem : (maxEndo α) ≫ (maxEndo α) = maxEndo α :=
    reflexive_transitive_idempotent hRefl (maxEndo_max _)
  -- Split it: f : α → π with f f° = M, f° f = 1_π.
  obtain ⟨π, f, hf, hff, hf'f⟩ := hsplit (maxEndo α) hRefl hSym hIdem
  -- π is a partial unit, and every object has a map to π (connectivity ≫ f).
  refine ⟨π, target_split_partialUnit f hff hf'f, fun a => ?_⟩
  obtain ⟨g, hg⟩ := hconn a α
  exact ⟨g ≫ f, (map_comp hg hf).1⟩

end Power

end Freyd.Alg
