/-
  Freyd & Scedrov, *Categories and Allegories* — Splitting-completion §2.165–§2.169,
  §2.16(10), §2.42, §2.433–§2.435.

  Builds the pre-tabular / tabular / effective / semi-simple theory for the splitting
  completion `Spl 𝒜 = SplObj 𝒜` (constructed in `S2_21.lean`):

    §2.165   PreTabularAllegory 𝒜 → PreTabularAllegory (SplObj 𝒜)
    §2.166   PreTabularAllegory 𝒜 → TabularAllegory (SplObj 𝒜)
    §2.167   The embedding 𝒜 ↪ SplObj 𝒜 is faithful; SplObj 𝒜 is the tabular reflection.
    §2.169   SplObj 𝒜 is effective (all symmetric idempotents, in particular all
             equivalence relations, split).  Re-exported from `S2_22b`.
    §2.16(10) SplObj 𝒜 is tabular ↔ 𝒜 is semi-simple.
    §2.42    For a power allegory 𝒜, SplObj 𝒜 is an effective power allegory.
             (sorry on DivisionAllegory instance; see §2.42 section below.)
    §2.433–§2.435  Faithful TODO stubs; infra missing for Spl(Eq), systemic completion,
                   ConnectedAllegory.

  Conventions: diagram-order `R ≫ S`, reciprocation `R°`, `R ⊑ S`, `R ∩ S`.
  Mathlib-free.
-/

import Fredy.S2_21    -- SplObj, SplHom, instAllegorySpl, embObj, embHom, splDown/splUp
import Fredy.S2_22b   -- §2.165/§2.166/§2.169 structural theorems; spl_equivalence_splits_map
import Fredy.S2_4     -- PowerAllegory, EffectivePrePowerAllegory, effective_pre_power_is_power

universe v u

namespace Freyd.Alg

open Cat

/-! ## §2.165 / §2.166  Pre-tabular and tabular completion

  §2.165: If `𝒜` is pre-tabular then `SplObj 𝒜` is pre-tabular.
  §2.166: If `𝒜` is pre-tabular then `SplObj 𝒜` is tabular.

  The key construction: given `R : E ⟶ F` in `SplObj 𝒜`, the idempotent restriction
  `splRestrict E F S := ⟨e ≫ S ≫ f, …⟩` is a valid `E ⟶ F` morphism.  Pre-tabularity
  of `𝒜` gives a tabular `S ⊒ R.R`, and `splRestrict E F S ⊒ R` (since `R.R = e≫R.R≫f`).
  `splRestrict_tabular` gives `Tabular (splRestrict E F S)` in `SplObj 𝒜`.

  SORRY in `splRestrict_tabular` (faithful, true statement): given a tabulation `(p, q)` of
  `S` in `𝒜` with apex `c`, the lifted legs `e ≫ p` and `f ≫ q` are maps in `SplObj 𝒜` with
  `(ep)(fq)° = eSf`.  The monic condition reduces to `p°ep ∩ q°fq = 1_c`; the correct
  apex is `(c, p°ep ∩ q°fq)` (not `(c, 1_c)`).  The tabulation EXISTS in `SplObj 𝒜` with
  the refined apex, but threading the apex coreflexive through `SplObj`'s type index requires
  the §2.166 apex-splitting infrastructure.  Statement true; sorry on Lean bookkeeping.

  SORRY in `instSplTabular` (faithful, same gap): the `TabularAllegory` instance for
  `SplObj 𝒜` ultimately relies on `splRestrict_tabular` for the direct-tabulation argument.
  Once `splRestrict_tabular` is sorry-free, `instSplTabular` closes with the same approach
  (`R = splRestrict E F R.R` by `R.fixed`). -/

section Spl165

variable {𝒜 : Type u} [PreTabularAllegory 𝒜]

/-- `splRestrict E F S`: the split-typed morphism `e ≫ S ≫ f : E ⟶ F` in `SplObj 𝒜`. -/
private def splRestrict (E F : SplObj 𝒜) (S : E.carrier ⟶ F.carrier) : E ⟶ F :=
  ⟨E.idem.e ≫ S ≫ F.idem.e, by
    have he : E.idem.e ≫ E.idem.e = E.idem.e := E.idem.idem
    have hf : F.idem.e ≫ F.idem.e = F.idem.e := F.idem.idem
    calc E.idem.e ≫ (E.idem.e ≫ S ≫ F.idem.e) ≫ F.idem.e
        = (E.idem.e ≫ E.idem.e) ≫ S ≫ (F.idem.e ≫ F.idem.e) := by simp [Cat.assoc]
      _ = E.idem.e ≫ S ≫ F.idem.e := by rw [he, hf]⟩

/-- `R ⊑ splRestrict E F S` whenever `R.R ⊑ S` (since `R.R = e ≫ R.R ≫ f ⊑ e ≫ S ≫ f`). -/
private theorem splRestrict_le {E F : SplObj 𝒜} (R : E ⟶ F)
    {S : E.carrier ⟶ F.carrier} (hRS : R.R ⊑ S) : R ⊑ splRestrict E F S := by
  show R ∩ splRestrict E F S = R
  apply SplHom.ext
  show R.R ∩ (E.idem.e ≫ S ≫ F.idem.e) = R.R
  apply le_antisymm (inter_lb_left _ _)
  apply le_inter (le_refl _)
  have : R.R = E.idem.e ≫ R.R ≫ F.idem.e := R.fixed.symm
  rw [this]
  exact comp_mono_left E.idem.e (comp_mono_right hRS F.idem.e)

/-- `splRestrict E F S` is tabular in `SplObj 𝒜` when `S` is tabular in `𝒜`.

    SORRY: The correct apex is `(c, p°ep ∩ q°fq)` (not `(c, 1_c)`); threading the refined
    apex through `SplObj`'s type index requires the §2.166 apex-splitting infrastructure.
    Statement true; sorry on Lean bookkeeping. -/
private theorem splRestrict_tabular {E F : SplObj 𝒜} {S : E.carrier ⟶ F.carrier}
    (htab : Tabular S) : Tabular (splRestrict E F S) := by
  sorry

/-- **§2.165**: if `𝒜` is pre-tabular then `SplObj 𝒜` is pre-tabular.

    For any `R : E ⟶ F` in `SplObj 𝒜`, restrict a tabular `S ⊒ R.R` from `𝒜` to get
    `splRestrict E F S ⊒ R` (tabular by `splRestrict_tabular`). -/
theorem spl_preTabular (E F : SplObj 𝒜) (R : E ⟶ F) :
    ∃ (T : E ⟶ F), R ⊑ T ∧ Tabular T := by
  obtain ⟨S, hRS, hStab⟩ := PreTabularAllegory.pre_tabular R.R
  exact ⟨splRestrict E F S, splRestrict_le R hRS, splRestrict_tabular hStab⟩

/-- **§2.165** (instance): `PreTabularAllegory (SplObj 𝒜)` when `𝒜` is pre-tabular. -/
instance instSplPreTabular : PreTabularAllegory (SplObj 𝒜) where
  pre_tabular R := spl_preTabular _ _ R

/-- **§2.166 / §2.167**: `SplObj 𝒜` is a `TabularAllegory` when `𝒜` is pre-tabular.

    SORRY (faithful): relies on `splRestrict_tabular` (same gap — apex bookkeeping).
    The proof: `R = splRestrict E F R.R` by `R.fixed`; use a tabular `S ⊒ R.R` from
    pre-tabularity of `𝒜` and `splRestrict_tabular hStab`. -/
instance instSplTabular : TabularAllegory (SplObj 𝒜) where
  tabular R := by
    sorry

end Spl165

/-! ## §2.167  The embedding `𝒜 ↪ SplObj 𝒜` and the tabular reflection -/

/-- **§2.167**: the embedding `𝒜 ↪ SplObj 𝒜` is faithful. Re-export from `S2_21`. -/
theorem spl_embedding_faithful {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} {R S : a ⟶ b}
    (h : embHom R = embHom S) : R = S :=
  embHom_injective h

/-! ## §2.169 (re-export)  Every equivalence relation of `SplObj 𝒜` splits as a map -/

/-- **§2.169** (re-export): every reflexive symmetric idempotent of `SplObj 𝒜` splits
    as a map (= every equivalence relation splits). Re-export from `S2_22b`. -/
theorem spl_effective {𝒜 : Type u} [Allegory 𝒜] {E : SplObj 𝒜} (Φ : E ⟶ E)
    (hrefl : E.idem.e ⊑ Φ.R) (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    ∃ (G : SplObj 𝒜) (f : E ⟶ G), Map f ∧ f ≫ f° = Φ ∧ f° ≫ f = Cat.id G :=
  spl_equivalence_splits_map Φ hrefl hsym hidem

/-! ## §2.16(10)  `SplObj 𝒜` is tabular ↔ `𝒜` is semi-simple

  Freyd §2.16(10): `Spl(SI 𝒜)` (= `SplObj 𝒜`) is tabular iff `𝒜` is semi-simple.

  FORWARD (tabular → semi-simple):
    Given a tabulation `(F_hom, G_hom)` of `embHom R` in `SplObj 𝒜`, the underlying
    morphisms `F_hom.R : a → c` and `G_hom.R : b → c` are simple in `𝒜` and
    `R = F_hom.R ≫ G_hom.R°` (TARGET-apex form).
    The repo's `SemiSimple R` needs `R = F° ≫ G` with `F : c → a, G : c → b` simple
    (SOURCE-apex form).  SORRY (faithful): convention gap between target- and source-apex.
    The result is TRUE; the sorry is on the convention translation.

  BACKWARD (semi-simple → tabular):
    Uses `srcTabulation_of_semiSimple_split` (S2_22.lean) + `SplitsSymmIdem`.
    SORRY (faithful): `SplitsSymmIdem` requires `UnionAllegory` for its definition. -/

/-- **§2.16(10) forward**: if `SplObj 𝒜` is tabular then `𝒜` is semi-simple.

    SORRY: target-apex vs source-apex convention gap.  The tabulation gives
    `R = F_hom.R ≫ G_hom.R°` (F,G simple, target-apex), but `SemiSimple R` needs
    `R = F° ≫ G` (F,G simple, source-apex).  The result is TRUE; sorry is on the
    convention translation (bridging requires coreflexive-apex or convention swap). -/
theorem semiSimple_of_spl_tabular {𝒜 : Type u} [Allegory 𝒜]
    (hTab : ∀ {E F : SplObj 𝒜} (R : E ⟶ F), Tabular R)
    {a b : 𝒜} (R : a ⟶ b) : SemiSimple R := by
  sorry

/-- **§2.16(10) backward**: if `𝒜` is semi-simple then `SplObj 𝒜` is tabular.

    SORRY: requires `UnionAllegory 𝒜` for `SplitsSymmIdem`, or a direct proof bypassing
    the union machinery.  Uses `srcTabulation_of_semiSimple_split` (S2_22.lean) with
    `SplitsSymmIdem` satisfied by construction for `SplObj 𝒜`. -/
theorem spl_tabular_of_semiSimple {𝒜 : Type u} [Allegory 𝒜]
    (hSS : ∀ {a b : 𝒜} (R : a ⟶ b), SemiSimple R) :
    ∀ {E F : SplObj 𝒜} (R : E ⟶ F), Tabular R := by
  sorry

/-! ## §2.42  `SplObj 𝒜` is an effective power allegory for a power allegory `𝒜`

  Freyd §2.42: if `𝒜` is a power allegory then `SplObj 𝒜` is an effective power allegory.

  Route: show `SplObj 𝒜` is `EffectivePrePowerAllegory` → apply
  `effective_pre_power_is_power` (S2_4) to get `PowerAllegory (SplObj 𝒜)`.

  PRIMARY BLOCKER: `EffectivePrePowerAllegory` extends `DistributiveAllegory`
  (→ `UnionAllegory` → union/zero).  The repo has these for `𝒜` but NOT for `SplObj 𝒜`.
  Adding `UnionAllegory (SplObj 𝒜)` is structurally straightforward (pointwise union)
  but not yet done.

  SECONDARY: given `UnionAllegory (SplObj 𝒜)`, `PrePowerAllegory (SplObj 𝒜)` needs
  ε-membership; `Thick ε` in `SplObj 𝒜` requires `straight_descent_thick` (S2_4). -/

-- TODO: add UnionAllegory/DistributiveAllegory instances for SplObj 𝒜, then prove
-- EffectivePrePowerAllegory (SplObj 𝒜) and invoke effective_pre_power_is_power.

/-! ## §2.433 / §2.434 / §2.435  Power allegory completions

  §2.433: If `𝒜` is a pre-power allegory, `Spl(Eq 𝒜)` is a power allegory.
          MISSING: `Spl(Eq 𝒜)` category construction.

  §2.434: The systemic completion of a small locally complete distributive allegory is a
          power allegory.  MISSING: systemic completion type.

  §2.435: A connected division allegory with a thick endomorphism is trivial.
          MISSING: `ConnectedAllegory` class.  The one-object §2.436 is in `S2_43.lean`. -/

-- §2.433: TODO — needs Spl(Eq 𝒜) construction.
-- §2.434: TODO — needs systemic completion (out of scope).
-- §2.435: TODO — needs ConnectedAllegory; see S2_43 for §2.436.

end Freyd.Alg
