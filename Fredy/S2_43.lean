/-
  Freyd & Scedrov, *Categories and Allegories* §2.435–§2.436.

  The diagonal proofs (Cantor) in algebraic form.

  §2.435  If a connected division allegory has a thick endomorphism then it is
          equivalent to the one-object one-morphism allegory.  Reduces to the
          one-object case, which is §2.436.
  §2.436  The equational theory of one-object pre-power allegories is
          INCONSISTENT: a thick endomorphism `T : a ⟶ a` forces `1_a = 𝟘`.

  Both are the algebraic recasting of Cantor's diagonal argument: the candidate
  "diagonal" relation `R = 𝟘 / (1 ∩ T)` (characterised by `S ⊑ R ↔ S(1∩T) = 𝟘`),
  fed through the §2.431 characterisation of thickness, collapses to `𝟘`, and its
  entireness then forces `1 ⊑ 𝟘`.

  This file lives on the §2.4 power-allegory infrastructure (S2_4: `Thick`,
  `PrePowerAllegory`, `thick_iff_existential` = §2.431) and the §2.3 division
  infrastructure (S2_3: right division, `le_div_iff`, `div_comp_le`).
-/

import Fredy.S1_1
import Fredy.S2_1
import Fredy.S2_2
import Fredy.S2_3
import Fredy.S2_4


universe v u

namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ## §2.436  The diagonal relation `R = 𝟘 / (1 ∩ T)`

  Freyd defines `R = 𝟘 / (1 ∩ T)`, "characterised by `S ⊑ R iff S(1∩T) = 𝟘`."
  Here `1 ∩ T` is the coreflexive cut of the endomorphism `T : a ⟶ a`. -/

/-- The "diagonal" relation of §2.436: `R = 𝟘 / (1 ∩ T)`. -/
def diag {a : 𝒜} (T : a ⟶ a) : a ⟶ a := (𝟘 : a ⟶ a) / (Cat.id a ∩ T)

/-- §2.436 characterisation of the diagonal relation: `S ⊑ R ↔ S(1∩T) = 𝟘`
    (the inequality `S(1∩T) ⊑ 𝟘` is an equality since `𝟘` is the minimum). -/
theorem le_diag_iff {a : 𝒜} (T : a ⟶ a) (S : a ⟶ a) :
    S ⊑ diag T ↔ S ≫ (Cat.id a ∩ T) = (𝟘 : a ⟶ a) := by
  rw [show diag T = (𝟘 : a ⟶ a) / (Cat.id a ∩ T) from rfl, le_div_iff]
  constructor
  · intro h; exact le_antisymm h (zero_le _)
  · intro h; rw [h]; exact le_refl _

/-- The diagonal absorbs `1 ∩ T` to `𝟘`: `(diag T)(1∩T) ⊑ 𝟘` (the
    `div_comp_le` half of §2.31 for `R = 𝟘 / (1 ∩ T)`). -/
theorem diag_comp_le_zero {a : 𝒜} (T : a ⟶ a) :
    diag T ≫ (Cat.id a ∩ T) ⊑ (𝟘 : a ⟶ a) :=
  div_comp_eq_le (𝟘 : a ⟶ a) (Cat.id a ∩ T)

/-- Right-domain factorization `R ⊑ R ≫ (1 ∩ R° R)` — the reciprocal of
    `le_dom_comp` (§2.122).  `dom (R°) = 1 ∩ R° R` is the codomain coreflexive. -/
theorem le_comp_codom {a b : 𝒜} (R : a ⟶ b) :
    R ⊑ R ≫ (Cat.id b ∩ R° ≫ R) := by
  -- Left-domain factorization for R° (modular law, R=1, S=R°, T=R°):
  --   R° = (1≫R°)∩R° ⊑ (1 ∩ R°≫R°°)≫R° = (1 ∩ R°R)≫R°.
  have h : R° ⊑ (Cat.id b ∩ R° ≫ R) ≫ R° := by
    have hm := modular_le (Cat.id b) (R°) (R°)
    rw [Cat.id_comp, Allegory.inter_idem, Allegory.recip_recip] at hm
    exact hm
  -- Reciprocate: R ⊑ R ≫ (1 ∩ R°R)°, then simplify the inner reciprocal.
  have hr := recip_mono h
  rw [Allegory.recip_comp, Allegory.recip_recip] at hr
  rwa [Allegory.recip_inter, recip_id, Allegory.recip_comp, Allegory.recip_recip] at hr

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ## §2.436  Inconsistency of one-object pre-power allegories

  The heart of §2.436.  Suppose `T : a ⟶ a` is a thick endomorphism.  By §2.431
  there is, for the diagonal `R = 𝟘 / (1 ∩ T)`, a witness `R̄` (`= R/T`) with

      (i)   `1 ⊑ R̄ R̄°`   (entire)
      (ii)  `R̄ T ⊑ R̄`
      (iii) `R̄° R̄ ⊑ T`
      and Freyd's "hence `R̄ ⊑ R`" (the witness lies below the diagonal).

  Freyd's chain:

      R̄ ⊑ R̄ (1 ∩ R̄° R̄) ⊑ R̄ (1 ∩ T) ⊑ R (1 ∩ T) ⊑ 𝟘,

  whence `R̄ = 𝟘`, and (i) forces `1 ⊑ 𝟘`.

  `inconsistency_core` isolates this algebra.  It uses exactly the containments
  that the chain consumes — entireness (i), `R̄°R̄ ⊑ T` (iii), and `R̄ ⊑ R`.  (The
  second §2.431 containment `R̄T ⊑ R̄` is what §2.431 needs to *manufacture* the
  witness, not what §2.436's collapse consumes, so it is not a hypothesis here.) -/

/-- §2.436 core (fully proved).  Given a §2.431 witness `R'` for the diagonal
    `R = 𝟘 / (1 ∩ T)` that lies below the diagonal (`R' ⊑ diag T`), is entire,
    and satisfies `R'°R' ⊑ T`, the diagonal argument collapses `R'` to `𝟘` and
    then forces `1_a = 𝟘`. -/
theorem inconsistency_core {a : 𝒜} (T : a ⟶ a) (R' : a ⟶ a)
    (hEnt : Cat.id a ⊑ R' ≫ R'°)
    (hRoR : R'° ≫ R' ⊑ T)
    (hDiag : R' ⊑ diag T) :
    Cat.id a = (𝟘 : a ⟶ a) := by
  -- Step 1: R' ⊑ R'(1 ∩ R'°R') ⊑ R'(1 ∩ T)  (codomain factorization + (iii)).
  have step1 : R' ⊑ R' ≫ (Cat.id a ∩ T) :=
    le_trans (le_comp_codom R') (comp_mono_left R' (le_inter (inter_lb_left _ _)
      (le_trans (inter_lb_right _ _) hRoR)))
  -- Step 2: R'(1 ∩ T) ⊑ (diag T)(1 ∩ T) ⊑ 𝟘   (R' ⊑ diag T, then div_comp_le).
  have step2 : R' ≫ (Cat.id a ∩ T) ⊑ (𝟘 : a ⟶ a) :=
    le_trans (comp_mono_right hDiag (Cat.id a ∩ T)) (diag_comp_le_zero T)
  -- Hence R' = 𝟘.
  have hR'zero : R' = (𝟘 : a ⟶ a) :=
    le_antisymm (le_trans step1 step2) (zero_le _)
  -- Step 3: entireness (i) forces 1 ⊑ R'R'° = 𝟘, so 1 = 𝟘.
  rw [hR'zero, DistributiveAllegory.zero_comp] at hEnt
  exact le_antisymm hEnt (zero_le _)

/-! ## §2.436  Main statement (via thickness)

  Freyd: "The equational theory of one-object pre-power allegories is
  inconsistent."  A single object carrying a thick endomorphism is exactly the
  one-object pre-power case; `inconsistency_core` shows its equational theory
  collapses (`1_a = 𝟘`).

  The §2.431 BECAUSE manufactures, for the diagonal `R = 𝟘 / (1 ∩ T)`, the
  witness `R̄ = R / T`, and verifies `1 ⊑ R̄R̄°`, `R̄T ⊑ R̄`, `R̄°R̄ ⊑ T`, together
  with `R̄ ⊑ R` (line 13814: "hence `R̄ ⊑ R`").  The three properties
  `inconsistency_core` consumes are precisely (i), (iii) and `R̄ ⊑ R`.

  FAITHFUL SORRY (one step).  S2_4's `thick_iff_existential` exposes a *different*
  witness shape (`R̄T ⊑ R`, `R̄°R ⊑ T`, via symmetric division) under a codomain-box
  guard, not Freyd's §2.431-construction witness `R̄ = R/T` with `R̄ ⊑ R` and
  `R̄°R̄ ⊑ T`.  Producing the latter — the entireness `1 ⊑ (R/T)(R/T)°` from
  thickness, the containment `R̄°R̄ ⊑ T`, and `R/T ⊑ R` — is the missing §2.431
  infrastructure (not exposed by S2_4).  The diagonal argument itself is complete
  in `inconsistency_core`; the `sorry` here is only that witness construction. -/

/-- §2.436 (main): a thick endomorphism on `a` forces `1_a = 𝟘` — the equational
    theory of one-object pre-power allegories is inconsistent.  The diagonal
    argument is `inconsistency_core` (proved); the single `sorry` is the §2.431
    construction of the witness `R̄ = (diag T)/T` and its three properties. -/
theorem one_object_pre_power_inconsistent {a : 𝒜} (T : a ⟶ a) (hT : Thick T) :
    Cat.id a = (𝟘 : a ⟶ a) := by
  -- §2.431 witness for R = diag T:  R̄ = (diag T) / T, with
  --   1 ⊑ R̄R̄°,  R̄° R̄ ⊑ T,  R̄ ⊑ diag T.
  obtain ⟨R', hEnt, hRoR, hDiag⟩ :
      ∃ R' : a ⟶ a, Cat.id a ⊑ R' ≫ R'° ∧ R'° ≫ R' ⊑ T ∧ R' ⊑ diag T := by
    sorry
  exact inconsistency_core T R' hEnt hRoR hDiag

end Freyd.Alg
