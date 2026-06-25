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

/-! ## §2.165 / §2.166 for `SplCorObj 𝒜`  (coreflexive splitting completion)

  `SplObj 𝒜` splits ALL symmetric idempotents. Freyd's §2.165/§2.166 apply only to the
  COREFLEXIVE sub-completion `SplCorObj 𝒜 = { E : SplObj 𝒜 // E.idem.e ⊑ 1_{E.carrier} }`,
  which splits only the coreflexive symmetric idempotents (`e° = e, ee = e, e ⊑ 1`).

  This section:
    §2.165  `Allegory (SplCorObj 𝒜)`          [PROVED: Cat + Allegory instances]
            `PreTabularAllegory (SplCorObj 𝒜)` [TODO: needs source-apex pre-tabulations]
    §2.166  `TabularAllegory (SplCorObj 𝒜)`    [TODO: relies on §2.165]

  WHY §2.165 (pre-tabulation) is TODO
  ─────────────────────────────────────
  Freyd's proof (book §2.165, "because" paragraph) takes a SOURCE-APEX tabulation of U ≥ R.R
  in 𝒜: `P : t ⟶ a`, `Q : t ⟶ b` (legs FROM the apex t TO the objects), `Map P`, `Map Q`,
  `R.R ≤ P°≫Q`, `PP°∩QQ° = id_t`. It then defines:

    C  =  Dom(P≫ee) ∩ Dom(Q≫fe)  =  P≫ee≫P° ∩ Q≫fe≫Q°  :  t ⟶ t

  and shows C is coreflexive (using P,Q jointly monic: `PP°∩QQ° = id_t` forces C ≤ id_t),
  then exhibits source-apex legs `CfA : (t,C) ⟶ (a,ee)` with `CfA.R = C≫P≫ee`:
    • Entire CfA: `id_{(t,C)} = C ≤ C≫(P≫ee≫P°)≫C = C` — trivially C ≤ C. ✓
    • Simple CfA: `CfA°≫CfA = ee≫P°≫C≫P≫ee ≤ ee≫P°P≫ee ≤ ee`     (P simple) ✓

  The repo's `PreTabularAllegory` provides TARGET-APEX legs `f : a ⟶ t, g : b ⟶ t`
  (not source-apex). Converting via `P = f°` gives Entire P but NOT Simple P in source-apex
  (since `PP° = f°f ≤ id_t` holds but `P°P = ff° ≥ id_a` is reflexive, not coreflexive).
  And without `PP°∩QQ° = id_t` (the joint-monicity condition missing from pre-tabulations),
  C = P≫ee≫P° ∩ Q≫fe≫Q° is NOT coreflexive.

  The fix is to assume the repo's pre-tabulation gives JOINTLY-MONIC source-apex pairs, i.e.,
  `PreTabularAllegory` in Freyd's original sense (every morphism is contained in a TABULAR
  one). The repo's class is strictly weaker (no joint-monicity condition), so §2.165 requires
  a stronger hypothesis here. -/

/-- The COREFLEXIVE splitting completion of `𝒜`: restrict `SplObj 𝒜` to objects whose
    symmetric idempotent `E.idem.e` is coreflexive (`E.idem.e ⊑ Cat.id E.carrier`).
    This is Freyd's `ℬℳ(𝒞𝑜𝓇ℯ𝒻𝓁 𝒜)` (§2.167): split only the coreflexive SymIdem. -/
def SplCorObj (𝒜 : Type u) [Allegory 𝒜] : Type u :=
  { E : SplObj 𝒜 // Coreflexive E.idem.e }

namespace SplCorObj

variable {𝒜 : Type u} [Allegory 𝒜]

/-- Category structure on `SplCorObj 𝒜`: homs and composition inherited from `SplObj 𝒜`. -/
instance instCatSplCor : Cat (SplCorObj 𝒜) where
  Hom E F     := SplHom E.1 F.1
  id E        := splId E.1
  comp R S    := splComp R S
  id_comp R   := SplHom.ext R.fixed_left
  comp_id R   := SplHom.ext R.fixed_right
  assoc R S T := SplHom.ext (Cat.assoc _ _ _)

/-- Allegory structure on `SplCorObj 𝒜`: reciprocation and intersection inherited
    from `SplObj 𝒜`; all axioms reduce to the underlying `𝒜` axioms via `SplHom.ext`. -/
instance instAllegorySplCor : Allegory (SplCorObj 𝒜) where
  recip R             := splRecip R
  inter R S           := splInter R S
  recip_recip R       := SplHom.ext (Allegory.recip_recip _)
  recip_comp R S      := SplHom.ext (Allegory.recip_comp _ _)
  recip_inter R S     := SplHom.ext (Allegory.recip_inter _ _)
  inter_idem R        := SplHom.ext (Allegory.inter_idem _)
  inter_comm R S      := SplHom.ext (Allegory.inter_comm _ _)
  inter_assoc R S T   := SplHom.ext (Allegory.inter_assoc _ _ _)
  semidistrib R S T   := SplHom.ext (Allegory.semidistrib _ _ _)
  modular R S T       := SplHom.ext (Allegory.modular _ _ _)

-- BOOK §2.165: If 𝒜 is pre-tabular then SplCorObj 𝒜 is pre-tabular.
-- TODO §2.165: Freyd's proof uses a SOURCE-APEX tabulation `P : t ⟶ a, Q : t ⟶ b` with
--   `Map P, Map Q, R.R ≤ P°≫Q, PP°∩QQ° = id_t`.  The SplCorObj apex is `(t, C)` where
--   `C = P≫ee≫P° ∩ Q≫fe≫Q°` (coreflexive: follows from `PP°∩QQ° = id_t ≤ PP°∩QQ°`).
--   Legs: `CfA : (t,C) ⟶ (a,ee)` with `CfA.R = C≫P≫ee`, shown to be Maps.
--   The repo's `PreTabularAllegory 𝒜` gives TARGET-APEX legs `f : a ⟶ t` (not source-apex
--   `P : t ⟶ a`), and lacks the joint-monicity `ff°∩gg° = id_t` needed for C coreflexive.
--   Blocked until the repo has either (a) a source-apex PreTabular class, or (b) a proof
--   that every target-apex pre-tabulation can be refined to a joint-monic source-apex span.

-- BOOK §2.166: SplCorObj 𝒜 is tabular iff it is pre-tabular and coreflexives split.
-- TODO §2.166: Relies on §2.165.  Coreflexive splitting is available via
--   `spl_coreflexive_splits` + `tabulation_of_split_apex`; only §2.165 is blocked.

end SplCorObj

end Freyd.Alg
