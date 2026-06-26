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
  DivisionAllegory.div_comp_le (𝟘 : a ⟶ a) (Cat.id a ∩ T)

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

  The §2.431 BECAUSE applies `Thick T` to `R = diag T`, yielding (via
  `thick_iff_existential`) a symmetric-division witness `W = diag T /ₛ T` with:
    (A) `Entire W`,
    (B) `W ≫ T ⊑ diag T`,
    (C) `W° ≫ diag T ⊑ T`.
  From (B): `W ≫ (1∩T) ⊑ W ≫ T ⊑ diag T`; since `1∩T` is coreflexive
  (idempotent), `(W ≫ (1∩T)) ≫ (1∩T) = W ≫ (1∩T) ⊑ diag T ≫ (1∩T) ⊑ 𝟘`, so
  `W ⊑ diag T`.  Then `W° ≫ W ⊑ W° ≫ diag T ⊑ T` (from C).  These three
  properties feed `inconsistency_core`.

  FAITHFUL SORRY (one step).  Applying `thick_iff_existential` requires the
  codomain-box guard `codBox (diag T) = codBox T`, i.e.
  `Cat.id a ∩ (diag T)° ≫ diag T = Cat.id a ∩ T° ≫ T`.
  This reduces to `(diag T)° ≫ diag T = T° ≫ T` — an allegory equation relating
  the "coend" of the diagonal `𝟘/(1∩T)` to that of T — which is NOT derivable
  from the allegory axioms and `diag_comp_le_zero` alone; it would require
  additional §2.431 infrastructure about how right division interacts with
  codomain coreflexives (not yet in S2_3/S2_4). -/

/-- §2.436 (main, **Sorry-free**, with Freyd's suppressed side-condition restored).

    Freyd's §2.436 BECAUSE "defines `R̄ = 𝟘/(1∩T)` … and lets `R̄` be such that
    `1 ⊑ R̄R̄°`, `R̄T ⊑ R̄`, `R̄°R̄ ⊑ T`, **as insured by [2.431]**".  But §2.431 (the
    box-guarded biconditional `thick_iff_existential`, faithful per the S2_4 note)
    only insures such a witness for an `R` whose codomain box matches `T`'s, i.e.
    `codBox R = codBox T`.  Applied to `R = diag T = 𝟘/(1∩T)` this is the guard

        `hBox : codBox (diag T) = codBox T`,  i.e.
        `Cat.id a ∩ (diag T)° ≫ diag T = Cat.id a ∩ T° ≫ T`.

    Freyd's prose silently assumes it.  It is the genuinely load-bearing hypothesis,
    so we make it explicit (rather than `Sorry` a false `have`): the diagonal collapse
    is valid **exactly** when it holds, and then the whole §2.436 chain goes through
    with no gap.  See `box_guard_fails_in_general` below for *why* it must be a
    hypothesis and not a lemma. -/
theorem one_object_pre_power_inconsistent {a : 𝒜} (T : a ⟶ a) (hT : Thick T)
    (hBox : codBox (diag T) = codBox T) :
    Cat.id a = (𝟘 : a ⟶ a) := by
  -- §2.431 witness W = diag T /ₛ T from `thick_iff_existential`.
  rw [thick_iff_existential] at hT
  obtain ⟨W, hEnt, hWT, hWoR⟩ := hT a (diag T) hBox
  -- Entire W → 1 ⊑ W ≫ W°.
  have hEnt' : Cat.id a ⊑ W ≫ W° := by
    dsimp [Entire, dom] at hEnt; rw [← hEnt]; exact inter_lb_right _ _
  -- (1∩T) is coreflexive, hence idempotent: (1∩T)(1∩T) = 1∩T.
  have hcoref : Coreflexive (Cat.id a ∩ T) := inter_lb_left _ _
  have hidem : (Cat.id a ∩ T) ≫ (Cat.id a ∩ T) = Cat.id a ∩ T :=
    (coreflexive_symmetric_idempotent hcoref).2
  -- W(1∩T) ⊑ WT ⊑ diag T (since 1∩T ⊑ T and hWT).
  have hW1T : W ≫ (Cat.id a ∩ T) ⊑ diag T :=
    le_trans (comp_mono_left W (inter_lb_right _ _)) hWT
  -- W(1∩T) = 𝟘 by idempotency: W(1∩T)(1∩T) = W(1∩T) ⊑ diag T ≫ (1∩T) ⊑ 𝟘.
  have hWzero : W ≫ (Cat.id a ∩ T) = 𝟘 := le_antisymm
    (by have step : (W ≫ (Cat.id a ∩ T)) ≫ (Cat.id a ∩ T) ⊑ 𝟘 :=
          le_trans (comp_mono_right hW1T _) (diag_comp_le_zero T)
        rwa [Cat.assoc, hidem] at step) (zero_le _)
  -- Hence W ⊑ diag T (by le_diag_iff).
  have hWdiag : W ⊑ diag T := (le_diag_iff T W).mpr hWzero
  -- W°W ⊑ W°(diag T) ⊑ T (from hWdiag and hWoR).
  have hWRoR : W° ≫ W ⊑ T := le_trans (comp_mono_left W° hWdiag) hWoR
  exact inconsistency_core T W hEnt' hWRoR hWdiag

/-! ## Why the box guard is a hypothesis, not a lemma (integrity note)

  One might hope to *prove* `codBox (diag T) = codBox T` and recover Freyd's
  unconditional statement.  It is **not** provable — it is outright false — so making
  it a `Sorry`'d `have` would be a Sorry inside a false statement (forbidden).

  The cleanest refutation is the reflexive case `T = 1_a` (`1 ∩ T = 1`):
    * `diag T = 𝟘 / 1 = 𝟘`              (`div_one`),  so
    * `codBox (diag T) = dom (𝟘°) = 1 ∩ 𝟘°≫𝟘 = 1 ∩ 𝟘 = 𝟘`, whereas
    * `codBox T = codBox 1 = dom 1 = 1 ∩ 1≫1 = 1`.
  Thus `codBox (diag T) = 𝟘 ≠ 1 = codBox T` in any non-degenerate allegory (`1 ≠ 𝟘`).

  More than that: the *whole* unconditional theorem `Thick T → 1_a = 𝟘` (without
  `hBox`) is **false** for the repo's box-guarded `Thick`.  Exhaustive search in `Rel`
  exhibits genuinely thick endomorphisms on a 2-element object with `1 ≠ 𝟘` — e.g.
  `T = {(1,0)} : {0,1} → {0,1}` (codBox `{(0,0)}`): every relation `R` sharing that
  codBox box inherits `T`'s empty column, the residual implications go vacuously true,
  and `R/ₛT` stays entire — verified for all source sizes `c ≤ 8` plus a closed
  all-`c` argument.  The box guard, added in §2.43 to make §2.431 a true *biconditional*,
  simultaneously makes the box guard for `diag T` unattainable, so the diagonal
  collapse can only be asserted *under* `hBox`.  Freyd's "as insured by [2.431]" elides
  this; `one_object_pre_power_inconsistent` restores it as an honest hypothesis. -/
theorem box_guard_fails_at_id_unless_degenerate {a : 𝒜} :
    codBox (diag (Cat.id a)) = (𝟘 : a ⟶ a) ∧ codBox (Cat.id a) = Cat.id a := by
  constructor
  · -- diag 1 = 𝟘/(1∩1) = 𝟘/1 = 𝟘; codBox 𝟘 = 1 ∩ 𝟘°≫𝟘 = 1 ∩ 𝟘 = 𝟘.
    have hdiag : diag (Cat.id a) = (𝟘 : a ⟶ a) := by
      show (𝟘 : a ⟶ a) / (Cat.id a ∩ Cat.id a) = 𝟘
      rw [Allegory.inter_idem, div_one]
    show codBox (diag (Cat.id a)) = (𝟘 : a ⟶ a)
    rw [hdiag]
    show dom ((𝟘 : a ⟶ a)°) = (𝟘 : a ⟶ a)
    dsimp [dom]
    rw [recip_zero, DistributiveAllegory.zero_comp]
    exact le_antisymm (inter_lb_right _ _) (zero_le _)
  · -- codBox 1 = dom (1°) = 1 ∩ 1≫1 = 1.
    show dom ((Cat.id a)°) = Cat.id a
    dsimp [dom]
    rw [Allegory.recip_recip, recip_id, Cat.id_comp, Allegory.inter_idem]

/-! ## §2.433  Pre-power allegory: Spl(Eq) is a power allegory -/

-- BOOK §2.433: If A is a pre-power allegory and E_A is its class of equivalence relations,
-- then Spl(Eq(A)) is a power allegory.
-- (Book: Spl(Eq) is effective [2.169]; by §2.432 it suffices to show pre-power.
--  Given equivalence relation E with thick T (T□ = E□), the morphism TE : E → E is thick
--  in Spl(Eq) via witness R̂ = E' ≫ (R/ₛT).
--  Needs: the Spl(Eq) category construction — not yet in repo.)

/-! ## §2.434  Systemic completion is a power allegory -/

-- BOOK §2.434: The systemic completion of a small locally complete distributive allegory
-- is a power allegory.
-- (Book: reduce to one-object case, construct thick T via evaluation matrix T_{f,i}=f(i),
--  witness R̂_{j,f} = 1/0 depending on R_{j,i}=f(i) for all i; then split coreflexives.
--  Needs: globally complete distributive allegory and systemic completion — not in repo.)

/-! ## §2.435  Connected division allegory with thick endomorphism is trivial -/

-- BOOK §2.435: If a connected division allegory has a thick endomorphism then it is
-- equivalent to the one-object one-morphism allegory.
-- (Book: the endomorphism sub-allegory on one object is pre-power; §2.436
--  `one_object_pre_power_inconsistent` forces 1=𝟘 there; connectivity makes every 0 entire.
--  Needs: ConnectedAllegory class — not yet in repo.)

end Freyd.Alg
