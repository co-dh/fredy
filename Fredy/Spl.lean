/-
  Freyd & Scedrov, *Categories and Allegories* — Splitting-completion §2.165–§2.169,
  §2.16(10), §2.42, §2.433–§2.435.

  Builds the pre-tabular / tabular / effective / semi-simple theory for the splitting
  completion `Spl 𝒜 = SplObj 𝒜` (constructed in `S2_21.lean`):

    §2.165   PreTabularAllegory (SplObj 𝒜) when 𝒜 is pre-tabular.
             [TODO: source-apex legs require coreflexive E.e; blocked for full SplObj]
    §2.166   TabularAllegory (SplObj 𝒜) when 𝒜 is pre-tabular.
             [TODO: relies on §2.165]
    §2.167   The embedding 𝒜 ↪ SplObj 𝒜 is faithful.                [PROVED]
    §2.169   SplObj 𝒜 is effective.                                  [PROVED; re-export]
    §2.16(10) SplObj 𝒜 is tabular ↔ 𝒜 is semi-simple.
              Forward: [TODO: apex convention gap]
              Backward: [TODO: needs SemiSimple in SplObj + UnionAllegory (SplObj 𝒜)]
    §2.42    For a power allegory 𝒜, SplObj 𝒜 is an effective power allegory.
             [TODO: needs UnionAllegory/DistributiveAllegory for SplObj 𝒜]
    §2.433–§2.435  [TODO: infra missing]

  ---

  WHY §2.165/§2.166 are TODO — DESIGN SCOPE MISMATCH:

  `SplObj 𝒜` splits ALL symmetric idempotents `e : a → a` (SymIdem: `e° = e`, `ee = e`).
  This combines Freyd's TWO-STEP process:
    §2.167  PM(Corefl 𝒜): split coreflexive SymIdem only (`e ⊑ id_a`).
    §2.169  PM(ER 𝒜):     split equivalence-relation SymIdem only (`id_a ⊑ e`).
  The repo's `SplObj 𝒜` is the COMBINED completion. §2.165/§2.166 apply to the
  COREFLEXIVE sub-completion only.

  For `R : E ⟶ F` in `SplObj 𝒜` (with `E = ⟨a, E.e⟩`, `F = ⟨b, F.e⟩`), the source-apex
  tabulation route requires — after extracting legs `(P : t → a, Q : t → b)` from a
  pre-tabulation of `R.R` in `𝒜` — that the legs into `SplObj 𝒜` are MAPS (Simple).
  For the leg `legA : (t, id_t) ⟶ E` with `legA.R = P ≫ E.e`, Simple(legA) reduces to
  `P° ≫ E.e ≫ P ⊑ id_t`.  This holds when `E.e ⊑ id_a` (coreflexive), but FAILS when
  `id_a ⊑ E.e` (equivalence relation): `P° E.e P ≥ P°P = id_t` gives equality, not `⊑`.

  Fix: restrict §2.165/§2.166 to `CoreflSplObj 𝒜` (splitting only coreflexive SymIdem),
  or show that every morphism in `SplObj 𝒜` has a tabulation using a coreflexive apex
  `(t, id_t)` with legs satisfying the stronger hypothesis that `E.e ⊑ P ≫ P°` (which
  is NOT the same as coreflexive E.e).  Neither construction is yet in the repo.

  WHY §2.16(10) forward is TODO:

  A tabulation of `embHom R` in `SplObj 𝒜` gives `P : embObj a ⟶ C`, `Q : embObj b ⟶ C`
  maps with `R = P.R ≫ Q.R°` and `P.R°P.R = C.idem.e = Q.R°Q.R`.  For `SemiSimple R` one
  needs simple `F₀ : c₀ → a` and `G₀ : c₀ → b` with `R = F₀° ≫ G₀`.  Setting `F₀ = P.R°`
  and `G₀ = Q.R°` gives `R = F₀° ≫ G₀` ✓, but `Simple F₀` requires `P.R ≫ P.R° ≤ 1_a`,
  while `Entire P` gives `1_a ≤ P.R ≫ P.R°`.  These are incompatible unless `P.R` is an
  isomorphism, so no direct conversion is possible without further work.

  WHY §2.16(10) backward is TODO:

  From semi-simplicity of `𝒜`, a morphism `R : E ⟶ F` in `SplObj 𝒜` has `R.R = F₀° ≫ G₀`
  with `F₀, G₀` simple.  The source-apex construction needs
  `SemiSimple R` in `SplObj 𝒜` (requiring `F₀` to absorb `E.idem.e` on the left, which is
  not guaranteed) and `[UnionAllegory (SplObj 𝒜)]` (pointwise union, not yet an instance).
  Both can be added with additional work.

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

  Both results are TODO; see file header for the design-scope analysis. -/

-- BOOK §2.165: If 𝒜 is pre-tabular then SplObj 𝒜 is pre-tabular.
-- TODO §2.165: Source-apex route (Freyd §2.165): take legs `(P : t → a, Q : t → b)` from
--   a pre-tabulation of `R.R` in 𝒜, then form `legA : (t, id_t) ⟶ E` with `legA.R = P ≫ E.e`.
--   Simple(legA) requires `P° ≫ E.e ≫ P ⊑ id_t`.  This holds when E.e coreflexive
--   (`E.e ⊑ id_a`), but FAILS for ER objects (`id_a ⊑ E.e`): `P°EP ≥ P°P = id_t`.
--   Blocked for full `SplObj 𝒜`.  Fix: restrict to coreflexive sub-completion.

-- BOOK §2.166: 𝒜 pre-tabular → SplObj 𝒜 tabular (§2.166: tabular ↔ pre-tabular + coref split).
-- TODO §2.166: Relies on §2.165.  The coreflexive-splitting half is available
--   (`spl_coreflexive_splits`, `tabulation_of_split_apex`) but §2.165 is blocked.

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

  Both directions are TODO pending further infrastructure; see file header for the precise gaps.

  For the BACKWARD direction, the available route is:
    (a) Build `UnionAllegory (SplObj 𝒜)` (pointwise union).
    (b) Build `SemiSimple R` in `SplObj 𝒜` from semi-simplicity of `𝒜`.
    (c) Show `SplitsSymmIdem (SplObj 𝒜)` from `SplHom.split_symmetric_idempotent`.
    (d) Apply `srcTabulation_of_semiSimple_split` (S2_22.lean).
  Steps (a)–(b) require ≈ 50 additional lines of infrastructure. -/

-- BOOK §2.16(10) forward: SplObj 𝒜 tabular → 𝒜 semi-simple.
-- TODO §2.16(10)-fwd: A tabulation (P, Q) of embHom R in SplObj 𝒜 gives R = P.R ≫ Q.R°
--   with P.R°P.R = C.idem.e.  Setting F₀ = P.R° and G₀ = Q.R° gives R = F₀° ≫ G₀ ✓,
--   but Simple F₀ needs P.R ≫ P.R° ≤ 1_a, while Entire P gives 1_a ≤ P.R ≫ P.R°.
--   These only agree when P.R is an isomorphism; no direct conversion available.

-- BOOK §2.16(10) backward: 𝒜 semi-simple → SplObj 𝒜 tabular.
-- TODO §2.16(10)-bwd: Needs (a) UnionAllegory (SplObj 𝒜) (pointwise) and
--   (b) SemiSimple R for R : E ⟶ F in SplObj 𝒜 from hSS about 𝒜 (requires
--   the typed restriction F₀|_{E} = E.idem.e ≫ F₀° satisfying the SplHom fixed
--   condition, which needs F₀ to "absorb" E.idem.e on the left — not guaranteed).

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

-- TODO §2.42: add UnionAllegory/DistributiveAllegory instances for SplObj 𝒜, then prove
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
