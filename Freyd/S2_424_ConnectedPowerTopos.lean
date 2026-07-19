/-
  Freyd & Scedrov, *Categories and Allegories* §2.424.

  BOOK §2.424 (a corollary of §2.16(10) + §2.422 + §2.423):
    *If `A` is a CONNECTED SEMI-SIMPLE power allegory then `Sid(Cor A)` is a tabular
     unitary power allegory and `Map(Sid(Cor A))` is a topos.  Consequently the power
     allegory is also positive, effective and transitive.*

  Here `Sid(Cor A)` is the idempotent-splitting completion.  The repo models it as
  `SplObj 𝒜` (§2.16, splitting ALL symmetric idempotents; for a semi-simple base this is
  the tabular reflection, `splObj_tabular_of_semiSimple`).

  ---------------------------------------------------------------------------------------
  WHAT THIS FILE CONTRIBUTES (all hole-free):

  1.  `splEqChain2_general` — the §2.433 second thickness containment
      `(E'≫(R/ₛT))° ≫ R ⊑ T ≫ E` proved for an ARBITRARY object idempotent `E`, dropping
      the reflexivity hypothesis `1 ⊑ E` that `S2_43.splEq_chain2` required.  The repo had
      documented (S2_43 lines 404-407) that the §2.433 thick-target construction "produces
      thick targets only for reflexive (equivalence-relation) objects; PER/coreflexive
      objects have no thick target by this construction".  That obstruction is REMOVABLE:
      a `Q ⟶ E` morphism `R` is right-fixed by the target idempotent (`R ≫ E = R`), so the
      base bound `(R/ₛT)° ≫ R ⊑ T` upgrades to `⊑ T ≫ E` by appending `E` on the right.
      This is exactly the algebra needed for the COREFLEXIVE objects of `Sid(Cor A)`.

  2.  `splTargetThick_general` / `splThickTarget_general` — the §2.433 thick target of an
      ARBITRARY object `E` of `SplObj 𝒜`, from a base thick `T : x → E.carrier` of `𝒜` and
      Freyd's §2.41 box-index side condition `SplEqBoxNaming E`.  This is the
      `EffectivePrePowerAllegory.thick_target`-shaped statement with the reflexivity
      restriction lifted.

  RESIDUAL (reported, NOT faked): assembling the full `EffectivePrePowerAllegory (SplObj 𝒜)`
  (hence `PowerAllegory (SplObj 𝒜)` via §2.432 `effective_pre_power_is_power`, hence the
  topos via §2.414 `mapTopos`) needs `SplEqBoxNaming E` discharged for EVERY object `E` —
  Freyd's §2.41 box-index bookkeeping — which is provable only for embedded objects
  (`splEq_embObj_boxNaming`) with the current infrastructure.  The §2.424 headline is
  therefore stated gated on that residual (see `s2424_topos_of_boxNaming`).
-/

import Freyd.S2_43
import Freyd.S2_165_Spl
import Freyd.S2_41b

universe v u

namespace Freyd.Alg

open Cat

section GeneralChain2
variable {𝒜 : Type u} [DivisionAllegory 𝒜] {x a b : 𝒜}

/-- **§2.433 (chain 2, GENERAL object).**  `(E' ≫ (R /ₛ T))° ≫ R ⊑ T ≫ E` for an ARBITRARY
    object idempotent `E` (symmetric idempotent, NO reflexivity assumed).

    `S2_43.splEq_chain2` needed `1 ⊑ E` to write `T = T≫1 ⊑ T≫E`.  Here we use instead that
    the test `R : (b,E') ⟶ (a,E)` is RIGHT-FIXED by the target idempotent — `R ≫ E = R`
    (`hRE`) — so the base symmetric-division bound `(R/ₛT)° ≫ R ⊑ T` upgrades to `⊑ T ≫ E`
    by appending `E`:  `(R/ₛT)° ≫ R = ((R/ₛT)° ≫ R) ≫ E ⊑ T ≫ E`.  Works for coreflexive
    (`E ⊑ 1`), PER, and reflexive objects alike. -/
theorem splEqChain2_general (E : a ⟶ a) (E' : b ⟶ b) (T : x ⟶ a) (R : b ⟶ a)
    (hE_idem : E ≫ E = E) (hE'_sym : E'° = E') (hE'_idem : E' ≫ E' = E')
    (hfix : E' ≫ R ≫ E = R) :
    (E' ≫ (R /ₛ T))° ≫ R ⊑ T ≫ E := by
  have h2 : (R /ₛ T)° ≫ R ⊑ T := ((le_symmDiv_iff (R /ₛ T) R T).mp (le_refl _)).2
  have hE'R : E' ≫ R = R := fix_absorb_left E' E R hE'_idem hfix
  -- R is right-fixed by E:  R ≫ E = (E'≫R≫E) ≫ E = E'≫R≫(E≫E) = E'≫R≫E = R.
  have hRE : R ≫ E = R := by
    calc R ≫ E = (E' ≫ R ≫ E) ≫ E := by rw [hfix]
      _ = E' ≫ R ≫ (E ≫ E) := by simp only [Cat.assoc]
      _ = E' ≫ R ≫ E := by rw [hE_idem]
      _ = R := hfix
  -- Collapse the source idempotent, then append E on the right.
  have key : (E' ≫ (R /ₛ T))° ≫ R = ((R /ₛ T)° ≫ R) ≫ E := by
    rw [Allegory.recip_comp, hE'_sym, Cat.assoc, hE'R, Cat.assoc, hRE]
  rw [key]
  exact comp_mono_right h2 E

end GeneralChain2

/-! ## §2.433 thick target for an ARBITRARY object of `SplObj 𝒜` -/

section GeneralThickTarget
variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- **§2.433 (thick target, GENERAL object).**  For an ARBITRARY object `E` of `SplObj 𝒜`
    (NO reflexivity of `E.idem.e`) and a base thick `T : x → E.carrier` of `𝒜`, the target
    `splEqTarget E T : embObj x ⟶ E` (underlying `T ≫ E.idem.e`) is THICK in `SplObj 𝒜`.

    Identical to `S2_43.splEqTarget_thick` except the second thickness containment uses
    `splEqChain2_general` (arbitrary object idempotent) instead of `splEq_chain2` (reflexive
    only).  `hbox : SplEqBoxNaming E` is Freyd's §2.41 box-index bookkeeping, unchanged. -/
theorem splTargetThick_general (E : SplObj 𝒜)
    {x : 𝒜} (T : x ⟶ E.carrier) (hThickT : Thick T) (hbox : SplEqBoxNaming E) :
    Thick (splEqTarget E T) := by
  rw [thick_iff_existential]
  intro Q R hboxQ
  have hbox𝒜 : codBox R.R = codBox T := hbox T R hboxQ
  have hent : Entire (R.R /ₛ T) := hThickT Q.carrier R.R hbox𝒜
  refine ⟨⟨Q.idem.e ≫ (R.R /ₛ T), ?_⟩, ?_, ?_, ?_⟩
  · show Q.idem.e ≫ (Q.idem.e ≫ (R.R /ₛ T)) ≫ Cat.id x = Q.idem.e ≫ (R.R /ₛ T)
    rw [Cat.comp_id, ← Cat.assoc, Q.idem.idem]
  · unfold Entire dom; apply SplHom.ext
    show Q.idem.e ∩ (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))° = Q.idem.e
    have hFF : (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))°
        = Q.idem.e ≫ ((R.R /ₛ T) ≫ (R.R /ₛ T)°) ≫ Q.idem.e := by
      rw [Allegory.recip_comp, Q.idem.sym]; simp only [Cat.assoc]
    have hFFent : Cat.id Q.carrier ⊑ (R.R /ₛ T) ≫ (R.R /ₛ T)° := by
      have h := hent; unfold Entire dom at h; exact h ▸ inter_lb_right _ _
    have hge : Q.idem.e ⊑ (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))° := by
      rw [hFF]
      calc Q.idem.e = Q.idem.e ≫ Cat.id Q.carrier ≫ Q.idem.e := by rw [Cat.id_comp, Q.idem.idem]
        _ ⊑ Q.idem.e ≫ ((R.R /ₛ T) ≫ (R.R /ₛ T)°) ≫ Q.idem.e :=
            comp_mono_left _ (comp_mono_right hFFent _)
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hge)
  · rw [splLe_iff]
    show (Q.idem.e ≫ (R.R /ₛ T)) ≫ (T ≫ E.idem.e) ⊑ R.R
    exact splEq_chain1 E.idem.e Q.idem.e T R.R R.fixed
  · rw [splLe_iff]
    show (Q.idem.e ≫ (R.R /ₛ T))° ≫ R.R ⊑ T ≫ E.idem.e
    exact splEqChain2_general E.idem.e Q.idem.e T R.R
      E.idem.idem Q.idem.sym Q.idem.idem R.fixed

/-- **§2.433 (thick target, existence form, GENERAL object).**  Every object `E` of
    `SplObj 𝒜` is the target of a THICK split-hom, given a base thick `T : x → E.carrier` of
    `𝒜` and the §2.41 box-index `SplEqBoxNaming E`.  Reflexivity of `E` is NOT required — this
    is the `EffectivePrePowerAllegory.thick_target`-shaped statement for the FULL object
    class (coreflexives / PERs included), i.e. for all of `Sid(Cor A)`. -/
theorem splThickTarget_general (E : SplObj 𝒜)
    {x : 𝒜} (T : x ⟶ E.carrier) (hThickT : Thick T) (hbox : SplEqBoxNaming E) :
    ∃ (P : SplObj 𝒜) (S : P ⟶ E), Thick S :=
  ⟨embObj x, splEqTarget E T, splTargetThick_general E T hThickT hbox⟩

/-! ## Box-index-FREE thick target: the UNGUARDED case dissolves `SplEqBoxNaming`

  Freyd's §2.41 box-index bookkeeping (`SplEqBoxNaming E`, provable only for embedded objects
  with the current infrastructure) is the sole residual of `splTargetThick_general`.  It is
  needed ONLY to feed the box-matching guard of the base thickness `Thick T`.  When the base
  `T` is UNCONDITIONALLY thick (`∀ R, Entire (R /ₛ T)`, exactly what an UNGUARDED power
  allegory's `∋` supplies via `A_is_map'`), that guard is vacuous and the box-naming
  requirement VANISHES — every object of `SplObj 𝒜` gets a thick target with NO side
  condition. -/

/-- **§2.433 (thick target, UNGUARDED base).**  If the base `T : x → E.carrier` is
    UNCONDITIONALLY thick (`Entire (R /ₛ T)` for EVERY `R`, no box guard), then
    `splEqTarget E T` is THICK in `SplObj 𝒜` for an ARBITRARY object `E` — with NO
    `SplEqBoxNaming` hypothesis.  This is the reflexivity-free AND box-index-free thick
    target: the full closure of the §2.433/§2.422 obstruction for the unguarded case. -/
theorem splTargetThick_unguarded (E : SplObj 𝒜)
    {x : 𝒜} (T : x ⟶ E.carrier)
    (hUnthick : ∀ {c : 𝒜} (R : c ⟶ E.carrier), Entire (R /ₛ T)) :
    Thick (splEqTarget E T) := by
  rw [thick_iff_existential]
  intro Q R _hboxQ
  have hent : Entire (R.R /ₛ T) := hUnthick R.R
  refine ⟨⟨Q.idem.e ≫ (R.R /ₛ T), ?_⟩, ?_, ?_, ?_⟩
  · show Q.idem.e ≫ (Q.idem.e ≫ (R.R /ₛ T)) ≫ Cat.id x = Q.idem.e ≫ (R.R /ₛ T)
    rw [Cat.comp_id, ← Cat.assoc, Q.idem.idem]
  · unfold Entire dom; apply SplHom.ext
    show Q.idem.e ∩ (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))° = Q.idem.e
    have hFF : (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))°
        = Q.idem.e ≫ ((R.R /ₛ T) ≫ (R.R /ₛ T)°) ≫ Q.idem.e := by
      rw [Allegory.recip_comp, Q.idem.sym]; simp only [Cat.assoc]
    have hFFent : Cat.id Q.carrier ⊑ (R.R /ₛ T) ≫ (R.R /ₛ T)° := by
      have h := hent; unfold Entire dom at h; exact h ▸ inter_lb_right _ _
    have hge : Q.idem.e ⊑ (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))° := by
      rw [hFF]
      calc Q.idem.e = Q.idem.e ≫ Cat.id Q.carrier ≫ Q.idem.e := by rw [Cat.id_comp, Q.idem.idem]
        _ ⊑ Q.idem.e ≫ ((R.R /ₛ T) ≫ (R.R /ₛ T)°) ≫ Q.idem.e :=
            comp_mono_left _ (comp_mono_right hFFent _)
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hge)
  · rw [splLe_iff]
    show (Q.idem.e ≫ (R.R /ₛ T)) ≫ (T ≫ E.idem.e) ⊑ R.R
    exact splEq_chain1 E.idem.e Q.idem.e T R.R R.fixed
  · rw [splLe_iff]
    show (Q.idem.e ≫ (R.R /ₛ T))° ≫ R.R ⊑ T ≫ E.idem.e
    exact splEqChain2_general E.idem.e Q.idem.e T R.R
      E.idem.idem Q.idem.sym Q.idem.idem R.fixed

/-! ## Unconditional thickness and its straight descent (no progenitor needed)

  `power_of_split_thick` (S2_4) can only produce a BOX-GUARDED `PowerAllegory`: from box-guarded
  thick targets, the §2.413 UNCONDITIONAL membership `∀R ∃f map, fS=R` is genuinely out of reach
  (S2_4 historical note — it needs Freyd's §2.416 progenitor/copower).  But when the thick
  targets are UNCONDITIONALLY thick (`ThickAll`, box-free — exactly what the unguarded base's `∋`
  gives), the progenitor obstruction VANISHES: the straight descent `S = h° ≫ T` of an
  unconditionally-thick `T = h ≫ S` (`h` a map) is again unconditionally thick, via the witness
  `Shat = Rhat ≫ h`.  Hence `Sid(Cor A)` is an UNGUARDED power allegory. -/

/-- `ThickAll T`: the box-FREE §2.431 thickness of `T` — an entire witness `Rhat` for EVERY `R`
    (no `codBox R = codBox T` guard).  Holds for the membership `∋` of an unguarded power
    allegory. -/
def ThickAll {𝒜 : Type u} [DivisionAllegory 𝒜] {a b : 𝒜} (T : a ⟶ b) : Prop :=
  ∀ {d : 𝒜} (R : d ⟶ b), ∃ (Rhat : d ⟶ a), Entire Rhat ∧ Rhat ≫ T ⊑ R ∧ Rhat° ≫ R ⊑ T

section ThickAllDescent
variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- `Entire R ⟹ 1 ⊑ R ≫ R°` (S2_4's `entire_iff_one_le` is private; re-derive locally). -/
theorem oneLeOfEntire {a b : 𝒜} (R : a ⟶ b) (hR : Entire R) : Cat.id a ⊑ R ≫ R° := by
  have h := hR; unfold Entire dom at h
  rw [← h]; exact inter_lb_right _ _

/-- `1 ⊑ R ≫ R° ⟹ Entire R`. -/
theorem entireOfOneLe {a b : 𝒜} {R : a ⟶ b} (h : Cat.id a ⊑ R ≫ R°) : Entire R := by
  unfold Entire dom
  exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) h)

/-- `ThickAll` descends along a map factorization `T = h ≫ S`, `h° ≫ h = 1`: if `T` is
    unconditionally thick then so is `S = h° ≫ T`.  Witness `Shat = Rhat ≫ h` where `Rhat` is `T`'s
    witness; `Shat° ≫ R ⊑ h° ≫ T = S` uses `h° ≫ h ≫ S = S`. -/
theorem thickAll_descent {x c a : 𝒜} {h : x ⟶ c} {S : c ⟶ a} {T : x ⟶ a}
    (hMap : Map h) (hch : h° ≫ h = Cat.id c) (hTeq : T = h ≫ S) (hTA : ThickAll T) :
    ThickAll S := by
  intro d R
  obtain ⟨Rhat, hEnt, hRhatT, hRhatoR⟩ := hTA R
  have hh'T : h° ≫ T = S := by rw [hTeq, ← Cat.assoc, hch, Cat.id_comp]
  refine ⟨Rhat ≫ h, entire_comp hEnt hMap.1, ?_, ?_⟩
  · -- (Rhat ≫ h) ≫ S = Rhat ≫ (h ≫ S) = Rhat ≫ T ⊑ R.
    rw [Cat.assoc, ← hTeq]; exact hRhatT
  · -- (Rhat ≫ h)° ≫ R = h° ≫ (Rhat° ≫ R) ⊑ h° ≫ T = S.
    rw [Allegory.recip_comp, Cat.assoc]
    calc h° ≫ (Rhat° ≫ R) ⊑ h° ≫ T := comp_mono_left h° hRhatoR
      _ = S := hh'T

/-- **§2.433 thick target, `ThickAll` (box-free) form.**  Same witness as
    `splTargetThick_unguarded`, but delivering the box-FREE `ThickAll` of `splEqTarget E T`
    directly (the proof never touches the box guard). -/
theorem splTargetThickAll {𝒜 : Type u} [DivisionAllegory 𝒜] (E : SplObj 𝒜)
    {x : 𝒜} (T : x ⟶ E.carrier)
    (hUnthick : ∀ {c : 𝒜} (R : c ⟶ E.carrier), Entire (R /ₛ T)) :
    ThickAll (splEqTarget E T) := by
  intro Q R
  have hent : Entire (R.R /ₛ T) := hUnthick R.R
  refine ⟨⟨Q.idem.e ≫ (R.R /ₛ T), ?_⟩, ?_, ?_, ?_⟩
  · show Q.idem.e ≫ (Q.idem.e ≫ (R.R /ₛ T)) ≫ Cat.id x = Q.idem.e ≫ (R.R /ₛ T)
    rw [Cat.comp_id, ← Cat.assoc, Q.idem.idem]
  · unfold Entire dom; apply SplHom.ext
    show Q.idem.e ∩ (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))° = Q.idem.e
    have hFF : (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))°
        = Q.idem.e ≫ ((R.R /ₛ T) ≫ (R.R /ₛ T)°) ≫ Q.idem.e := by
      rw [Allegory.recip_comp, Q.idem.sym]; simp only [Cat.assoc]
    have hFFent : Cat.id Q.carrier ⊑ (R.R /ₛ T) ≫ (R.R /ₛ T)° := by
      have h := hent; unfold Entire dom at h; exact h ▸ inter_lb_right _ _
    have hge : Q.idem.e ⊑ (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))° := by
      rw [hFF]
      calc Q.idem.e = Q.idem.e ≫ Cat.id Q.carrier ≫ Q.idem.e := by rw [Cat.id_comp, Q.idem.idem]
        _ ⊑ Q.idem.e ≫ ((R.R /ₛ T) ≫ (R.R /ₛ T)°) ≫ Q.idem.e :=
            comp_mono_left _ (comp_mono_right hFFent _)
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hge)
  · rw [splLe_iff]
    show (Q.idem.e ≫ (R.R /ₛ T)) ≫ (T ≫ E.idem.e) ⊑ R.R
    exact splEq_chain1 E.idem.e Q.idem.e T R.R R.fixed
  · rw [splLe_iff]
    show (Q.idem.e ≫ (R.R /ₛ T))° ≫ R.R ⊑ T ≫ E.idem.e
    exact splEqChain2_general E.idem.e Q.idem.e T R.R
      E.idem.idem Q.idem.sym Q.idem.idem R.fixed

/-- Straight UNCONDITIONALLY-thick target (packaged like `exists_straight_thick_target_of_split`
    but box-free): straight-factor the unconditionally-thick `T` and descend `ThickAll`. -/
theorem exists_straight_thickAll_target
    (hsplit : EqSplits 𝒜) (hthick : ∀ (a : 𝒜), ∃ (x : 𝒜) (T : x ⟶ a), ThickAll T) (b : 𝒜) :
    ∃ (p : 𝒜) (S : p ⟶ b), Straight S ∧ ThickAll S := by
  obtain ⟨x, T, hTA⟩ := hthick b
  obtain ⟨c, h, hMap, hch, hStr, hTeq⟩ := straight_factorization_of_split hsplit T
  exact ⟨c, h° ≫ T, hStr, thickAll_descent hMap hch hTeq hTA⟩

/-- The §2.413 membership map from an unconditionally-thick STRAIGHT `S`: `f = R /ₛ S` is a map
    with `f ≫ S = R`, for EVERY `R` (no box).  This is `power_of_split_thick`'s `eps_thick`
    algebra with the box guard dropped (the witness `Rhat` exists unconditionally). -/
theorem thickAll_straight_classifies {p b : 𝒜} {S : p ⟶ b}
    (hStr : Straight S) (hTA : ThickAll S) {c : 𝒜} (R : c ⟶ b) :
    Map (R /ₛ S) ∧ (R /ₛ S) ≫ S = R := by
  obtain ⟨R', hEnt', hR'S, hR'oR⟩ := hTA R
  have hR'_le : R' ⊑ R /ₛ S := (le_symmDiv_iff R' R S).mpr ⟨hR'S, hR'oR⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- Entire (R /ₛ S).
    refine entireOfOneLe ?_
    refine le_trans (oneLeOfEntire R' hEnt') ?_
    exact le_trans (comp_mono_right hR'_le _) (comp_mono_left _ (recip_mono hR'_le))
  · -- Simple (R /ₛ S): S straight ⟹ R/ₛS simple [§2.356].
    exact straight_symmDiv_simple hStr R
  · -- (R /ₛ S) ≫ S = R.
    apply le_antisymm
    · exact ((le_symmDiv_iff (R /ₛ S) R S).mp (le_refl _)).1
    · have hRle : R ⊑ R' ≫ S := by
        have e1 : R ⊑ (R' ≫ R'°) ≫ R := by
          have := comp_mono_right (oneLeOfEntire R' hEnt') R
          rwa [Cat.id_comp] at this
        rw [Cat.assoc] at e1
        exact le_trans e1 (comp_mono_left R' hR'oR)
      exact le_trans hRle (comp_mono_right hR'_le S)

/-- **The unguarded builder.**  A division allegory in which equivalence relations split
    (`hsplit`) and every object has an UNCONDITIONALLY-thick target (`hthick : ThickAll`) is an
    UNGUARDED power allegory.  `eps b` = the straight descent of the chosen unconditionally-thick
    target (`exists_straight_thickAll_target`); `eps_thick_all` = `thickAll_straight_classifies`.
    NO progenitor / copower needed — the §2.416 obstacle (S2_4 note) is bypassed because the
    targets are already box-free thick. -/
noncomputable def unguardedPowerOfSplitThickAll
    (hsplit : EqSplits 𝒜) (hthick : ∀ (a : 𝒜), ∃ (x : 𝒜) (T : x ⟶ a), ThickAll T) :
    UnguardedPowerAllegory 𝒜 :=
  { powerObj := fun b => (exists_straight_thickAll_target hsplit hthick b).choose
    eps := fun b => (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose
    eps_straight := fun b => (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose_spec.1
    eps_thick := fun {b _c} R _ =>
      ⟨R /ₛ (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose,
       (thickAll_straight_classifies
          (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose_spec.1
          (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose_spec.2 R).1,
       (thickAll_straight_classifies
          (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose_spec.1
          (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose_spec.2 R).2⟩
    eps_thick_all := fun {b _c} R =>
      ⟨R /ₛ (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose,
       (thickAll_straight_classifies
          (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose_spec.1
          (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose_spec.2 R).1,
       (thickAll_straight_classifies
          (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose_spec.1
          (exists_straight_thickAll_target hsplit hthick b).choose_spec.choose_spec.2 R).2⟩ }

end ThickAllDescent

end GeneralThickTarget

/-! ## §2.422: `Sid(Cor A)` has a thick target for EVERY object (unguarded base)

  Assembled over an UNGUARDED power allegory base `𝒜`: the base membership `∋ (E.carrier)` is
  unconditionally thick (`A_is_map'`, S2_4), so `splTargetThick_unguarded` gives every object
  `E` of `SplObj 𝒜` a thick target — with NO box-index side condition.  This is exactly the
  `EffectivePrePowerAllegory.thick_target` shape (Freyd §2.42/§2.422: `Sid(Cor A)` is a
  pre-power allegory). -/

section UnguardedThickTargets
variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜]

/-- The base membership `∋ b` is UNCONDITIONALLY thick in an unguarded power allegory:
    `A(R) = R /ₛ ∋ b` is entire for every `R` (`A_is_map'`). -/
theorem eps_unthick (b : 𝒜) {c : 𝒜} (R : c ⟶ b) : Entire (R /ₛ ∋ b) :=
  (A_is_map' R).1

/-- **§2.422 (thick_target for `SplObj 𝒜`, unguarded base).**  EVERY object `E` of
    `SplObj 𝒜` is the target of a THICK split-hom — box-index-free.  Witness: the base
    membership `T = ∋ (E.carrier)` (unconditionally thick), split-lifted by
    `splTargetThick_unguarded`. -/
theorem splObj_thick_target (E : SplObj 𝒜) :
    ∃ (P : SplObj 𝒜) (S : P ⟶ E), Thick S :=
  ⟨embObj (PowerAllegory.powerObj E.carrier),
   splEqTarget E (∋ E.carrier),
   splTargetThick_unguarded E (∋ E.carrier) (fun {_} R => eps_unthick E.carrier R)⟩

/-- **§2.422 (thick_target for `SplObj 𝒜`, `ThickAll` form).**  EVERY object `E` of `SplObj 𝒜`
    has a box-FREE unconditionally-thick target — the membership `∋ (E.carrier)` split-lifted by
    `splTargetThickAll`.  This is the input the UNGUARDED power builder needs. -/
theorem splObj_thickAll_target (E : SplObj 𝒜) :
    ∃ (P : SplObj 𝒜) (S : P ⟶ E), ThickAll S :=
  ⟨embObj (PowerAllegory.powerObj E.carrier),
   splEqTarget E (∋ E.carrier),
   splTargetThickAll E (∋ E.carrier) (fun {_} R => eps_unthick E.carrier R)⟩

end UnguardedThickTargets

/-! ## §2.424: the combined base and `Sid(Cor A)` as a power allegory

  Freyd's §2.424 hypothesis is a CONNECTED SEMI-SIMPLE power allegory.  We package the exact
  algebraic content the assembly needs into ONE class over a single `Allegory` base (the
  standard diamond dodge, as in `TabularUnitaryPowerAllegory`):

    * `SemiSimpleDivisionAllegory` — makes `SplObj 𝒜` tabular (`splObj_tabular_of_semiSimple`)
      and effective-division (`instEffectiveDivisionSpl`);
    * `UnitaryAllegory` — supplies the unit object (`instUnitarySpl`), the "unitary" of
      "tabular unitary power allegory" and §2.423's connectivity-unit;
    * `UnguardedPowerAllegory` — supplies the unconditionally-thick membership `∋`
      (`splObj_thick_target`), the §2.41-box-index-free thick targets.

  (Connectivity itself is used by §2.423 to build a unit; here it is subsumed by carrying the
  `UnitaryAllegory` directly — Freyd's §2.423 shows a connected power allegory in which
  coreflexives split HAS one, and `Sid(Cor A)` splits coreflexives by construction.) -/

/-- Freyd §2.424 base: a SEMI-SIMPLE, UNITARY, UNGUARDED power allegory (one `Allegory`
    base — `DivisionAllegory` is shared by the semi-simple-division and unguarded-power
    parents, so Lean's structure inheritance collapses the diamond). -/
class SemiSimpleUnitaryUnguardedPowerAllegory (𝒜 : Type u) extends
    SemiSimpleDivisionAllegory 𝒜, UnitaryAllegory 𝒜, UnguardedPowerAllegory 𝒜

section Assembly
variable {𝒜 : Type u} [SemiSimpleUnitaryUnguardedPowerAllegory 𝒜]

/-- **§2.422 / §2.424 (pre-power).**  `Sid(Cor A) = SplObj 𝒜` is an EFFECTIVE PRE-POWER
    ALLEGORY: `instEffectiveDivisionSpl` supplies the effective-division tower and
    `splObj_thick_target` supplies a (box-index-free) thick target for EVERY object. -/
noncomputable def splObjEffectivePrePower : EffectivePrePowerAllegory (SplObj 𝒜) :=
  { instEffectiveDivisionSpl with
    thick_target := fun E => splObj_thick_target E }

/-- Equivalence relations split in `SplObj 𝒜` (`splObj_split_equivalence`, needs only the
    ambient allegory). -/
theorem splObj_eqSplits : EqSplits (SplObj 𝒜) :=
  fun E hrefl hsym hidem => splObj_split_equivalence E hrefl hsym hidem

/-- **§2.424 (HEADLINE, UNGUARDED power).**  `Sid(Cor A) = SplObj 𝒜` is an UNGUARDED POWER
    ALLEGORY.  Every object has a box-FREE unconditionally-thick target (`splObj_thickAll_target`,
    from the unguarded base membership), and equivalence relations split (`splObj_eqSplits`), so
    the progenitor-free builder `unguardedPowerOfSplitThickAll` applies.  This is the structure
    Freyd's §2.414-converse (`mapTopos`) requires. -/
noncomputable def splObjUnguardedPower : UnguardedPowerAllegory (SplObj 𝒜) :=
  unguardedPowerOfSplitThickAll splObj_eqSplits (fun E => splObj_thickAll_target E)

/-- **§2.422 / §2.424 (power).**  `Sid(Cor A) = SplObj 𝒜` is a POWER ALLEGORY (the box-guarded
    reduct of `splObjUnguardedPower` — Freyd §2.422's "`Sid(Cor A)` is an effective power
    allegory"). -/
noncomputable def splObjPowerAllegory : PowerAllegory (SplObj 𝒜) :=
  splObjUnguardedPower.toPowerAllegory

/-- **§2.424 (Sid(Cor A) is a TABULAR UNITARY UNGUARDED POWER ALLEGORY).**  Merges, over the ONE
    `Allegory (SplObj 𝒜)` base:
      * tabular — `splObj_tabular_of_semiSimple` (semi-simple base, §2.16(10));
      * unitary — `instUnitarySpl` (unit object of `SplObj 𝒜`);
      * distributive — `instDistributiveSpl`;
      * unguarded power — `splObjUnguardedPower` (§2.422 + the box-free thick targets).
    This is the exact §2.414-converse hypothesis. -/
noncomputable instance splObjTUUP : TabularUnitaryUnguardedPowerAllegory (SplObj 𝒜) :=
  { (splObj_tabular_of_semiSimple : TabularAllegory (SplObj 𝒜)),
    (instUnitarySpl : UnitaryAllegory (SplObj 𝒜)),
    (instDistributiveSpl : DistributiveAllegory (SplObj 𝒜)),
    splObjUnguardedPower with }

/-- **§2.424 (HEADLINE, TOPOS).**  `Map(Sid(Cor A)) = Map(SplObj 𝒜)` is a TOPOS.  Freyd's
    §2.414-converse `mapTopos` applied to the tabular unitary unguarded power allegory
    `SplObj 𝒜` (`splObjTUUP`). -/
noncomputable def sid_cor_map_topos :
    @Freyd.Topos.{v} (MapObj (SplObj 𝒜)) (mapCat (𝒜 := SplObj 𝒜)) :=
  mapTopos

/-- **§2.424 ("consequently ... effective").**  `Sid(Cor A) = SplObj 𝒜` is an EFFECTIVE
    allegory — every equivalence relation splits as a map (`instEffectiveSpl`, since the base is
    semi-simple). -/
noncomputable def sid_cor_effective : EffectiveAllegory (SplObj 𝒜) := instEffectiveSpl

/-! ## §2.424 — status of the "consequently positive / transitive" clause

  The two HEADLINE claims are `splObjTUUP` (Sid(Cor A) is a tabular unitary [unguarded] power
  allegory) and `sid_cor_map_topos` (Map(Sid(Cor A)) is a topos); the "effective" corollary is
  `sid_cor_effective`.  The remaining two adjectives of Freyd's "consequently ... positive,
  effective and transitive" are NOT re-derived here:

    * POSITIVE would come from `instPositiveSpl`, which needs `[PositiveAllegory 𝒜]` on the base
      — NOT among Freyd's §2.424 hypotheses (he DERIVES it, via the topos / §2.219 polarization).
      A base-hypothesis-free derivation needs the transport `SplObj 𝒜 ≅ Rel(Map(SplObj 𝒜))`
      (tabular ⟺ `A = Rel(Map A)`) carrying the topos's coherent structure back to the allegory.
    * TRANSITIVE is likewise a downstream property of the resulting power allegory.

  Both are corollaries of the topos already produced, but require the tabular↔`Rel(Map)` bridge,
  which is separate infrastructure; they are reported, not faked. -/

end Assembly

end Freyd.Alg
