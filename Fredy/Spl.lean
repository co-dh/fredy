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
            `PreTabularAllegory (SplCorObj 𝒜)` [PROVED via §2.166]
    §2.166  `TabularAllegory (SplCorObj 𝒜)`    [PROVED]

  Construction (source-apex convention `Tabulates p q R := R = p°≫q ∧ p≫p° ∩ q≫q° = id`):
  given a tabulation `(f, g)` of `Ψ.R` in `𝒜` (`Ψ.R = f°≫g`, `f≫f° ∩ g≫g° = id_c`), the
  object idempotents `E.e`, `F.e` (coreflexive) are absorbed into the legs `p = f≫E.e`,
  `q = g≫F.e`.  These only PRE-tabulate `Ψ.R`, so the apex is the coreflexive
  `D = 1 ∩ p≫p° ∩ q≫q° = 1 ∩ f≫E.e≫f° ∩ g≫F.e≫g°` on `c`, split in `SplCorObj 𝒜` as
  `C = ⟨c, D⟩`.  The source-apex legs are `legA = D≫p : C ⟶ E`, `legB = D≫q : C ⟶ F`.
  Map/joint laws follow from `D ⊑ id`, `D ⊑ p≫p°`, `D ⊑ q≫q°`, and `f≫f° ∩ g≫g° = id`;
  the relation law `Ψ = legA°≫legB` is the factoring `p°≫q ⊑ p°≫D≫q` (`splCor_factor`). -/

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

end SplCorObj

/-! ## §2.165 / §2.166 for `SplCorObj 𝒜` under `[TabularAllegory 𝒜]`

  With a full tabular allegory we can build tabulations directly, bypassing the source-apex
  issue that blocks the pre-tabular version. -/

-- §2.136 dual: for a SYMMETRIC SIMPLE `A`, `(R ∩ S) ≫ A = R≫A ∩ S≫A`.
-- (Reciprocate `simple_dist_inter` applied to `A°` and use `A° = A`.)
private theorem splCor_dist_inter_right {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} {A : b ⟶ b}
    (hAsym : A° = A) (hsimpleA : Simple A) (R S : a ⟶ b) :
    (R ∩ S) ≫ A = (R ≫ A) ∩ (S ≫ A) := by
  -- ((R∩S)≫A)° = A≫(R∩S)° = A≫(R°∩S°) = A≫R° ∩ A≫S° = (R≫A)° ∩ (S≫A)°
  have key : ((R ∩ S) ≫ A)° = ((R ≫ A) ∩ (S ≫ A))° := by
    rw [Allegory.recip_comp, Allegory.recip_inter, hAsym, simple_dist_inter hsimpleA R° S°,
        Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp, hAsym]
  have := congrArg (·°) key
  simpa only [Allegory.recip_recip] using this

private theorem splCor_entire_to_le {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} {f : a ⟶ b}
    (h : Entire f) : Cat.id a ⊑ f ≫ f° := by
  unfold Entire dom at h; exact h ▸ inter_lb_right _ _

-- `R ⊑ dom R ≫ R` (= `R ⊑ (1 ∩ R≫R°) ≫ R`); §2.122 helper (re-derived; the S2_1 one is private).
private theorem le_dom_comp' {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    R ⊑ (Cat.id a ∩ R ≫ R°) ≫ R := by
  have h := modular_le (Cat.id a) R R
  simp only [Cat.id_comp, Allegory.inter_idem] at h
  exact h

-- `cod` factoring (dual): `R ⊑ R ≫ (1 ∩ R°≫R)`.
private theorem le_comp_cod {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    R ⊑ R ≫ (Cat.id b ∩ R° ≫ R) := by
  have h := recip_mono (le_dom_comp' R°)
  -- le_dom_comp' R° : R° ⊑ (1 ∩ R°≫R°°)≫R°;  reciprocate.
  rw [Allegory.recip_comp, Allegory.recip_inter, recip_id, Allegory.recip_comp,
      Allegory.recip_recip] at h
  exact h

-- §2.166 factoring: `p°≫q` factors through the coreflexive `1 ∩ p≫p° ∩ q≫q°`.
-- (Insert `cod p° = 1∩p≫p°` after `p°`, then `dom q = 1∩q≫q°` before `q`; the two coreflexives
--  compose to their intersection by `coreflexive_comp_eq_inter`.)
private theorem splCor_factor {𝒜 : Type u} [Allegory 𝒜] {c x y : 𝒜} (p : c ⟶ x) (q : c ⟶ y) :
    p° ≫ q ⊑ p° ≫ (Cat.id c ∩ p ≫ p° ∩ q ≫ q°) ≫ q := by
  have hcodp : p° ⊑ p° ≫ (Cat.id c ∩ p ≫ p°) := by
    have := le_comp_cod p°
    rwa [Allegory.recip_recip] at this
  have hdomq : q ⊑ (Cat.id c ∩ q ≫ q°) ≫ q := le_dom_comp' q
  have hcorL : Coreflexive (Cat.id c ∩ p ≫ p°) := inter_lb_left _ _
  have hcorR : Coreflexive (Cat.id c ∩ q ≫ q°) := inter_lb_left _ _
  -- p°≫q ⊑ (p°≫(1∩pp°))≫q ⊑ (p°≫(1∩pp°))≫((1∩qq°)≫q)
  have h1 : p° ≫ q ⊑ p° ≫ (Cat.id c ∩ p ≫ p°) ≫ q := by
    rw [← Cat.assoc]; exact comp_mono_right hcodp q
  have h2 : p° ≫ (Cat.id c ∩ p ≫ p°) ≫ q
      ⊑ p° ≫ (Cat.id c ∩ p ≫ p°) ≫ (Cat.id c ∩ q ≫ q°) ≫ q :=
    comp_mono_left p° (comp_mono_left _ hdomq)
  refine le_trans h1 (le_trans h2 ?_)
  -- merge the two coreflexives:  (1∩pp°)≫(1∩qq°) = (1∩pp°) ∩ (1∩qq°) = 1∩pp°∩qq°.
  rw [← Cat.assoc (Cat.id c ∩ p ≫ p°) (Cat.id c ∩ q ≫ q°) q,
      coreflexive_comp_eq_inter hcorL hcorR]
  refine comp_mono_left p° (comp_mono_right ?_ q)
  -- (1∩pp°) ∩ (1∩qq°) = 1∩pp°∩qq°  (drop the redundant second `1`); show ⊑.
  refine le_inter (le_inter ?_ ?_) ?_
  · exact le_trans (inter_lb_left _ _) (inter_lb_left _ _)
  · exact le_trans (inter_lb_left _ _) (inter_lb_right _ _)
  · exact le_trans (inter_lb_right _ _) (inter_lb_right _ _)

/-- **§2.166**: If `𝒜` is a tabular allegory then `SplCorObj 𝒜` is a tabular allegory.

    Source-apex convention (`Tabulates p q R := … ∧ R = p°≫q ∧ p≫p° ∩ q≫q° = id`).
    Given `Ψ : E ⟶ F` in `SplCorObj 𝒜`, extract a tabulation `(f, g)` of `Ψ.R` in `𝒜`
    (`Ψ.R = f°≫g`, `f≫f° ∩ g≫g° = id_c`).  Freyd §2.166: the coreflexive
    `A = 1 ∩ f≫Ψ.R≫g°` on `c` is a symmetric idempotent; in `SplCorObj 𝒜` it splits as
    the apex object `C = ⟨c, A⟩`.  The source-apex legs are `legA = A≫f : C ⟶ E` and
    `legB = A≫g : C ⟶ F` (each `A`-fixed on the left and `E.e/F.e`-fixed on the right).
    The three tabulation laws are Freyd's two displayed computations:
    `f°≫A≫g = Ψ.R` (sandwich, since `Ψ.R = f°≫g`) and
    `legA≫legA° ∩ legB≫legB° = A≫(f≫f° ∩ g≫g°)≫A = A≫A = A = id_C`. -/
instance SplCorObj.instTabularAllegorySplCor {𝒜 : Type u} [TabularAllegory 𝒜] :
    TabularAllegory (SplCorObj 𝒜) :=
  { SplCorObj.instAllegorySplCor with
    tabular := fun {E F} Ψ => by
      obtain ⟨c, f, g, hMapf, hMapg, hRfg, htab⟩ := TabularAllegory.tabular Ψ.R
      -- Entireness of the two legs, read off the joint-monicity `htab`.
      have hfent : Cat.id c ⊑ f ≫ f° := htab ▸ inter_lb_left (f ≫ f°) (g ≫ g°)
      have hgent : Cat.id c ⊑ g ≫ g° := htab ▸ inter_lb_right (f ≫ f°) (g ≫ g°)
      -- Object idempotents (E.e on E.carrier, F.e on F.carrier), symmetric idempotent + coreflexive.
      have hEcor : E.1.idem.e ⊑ Cat.id E.1.carrier := E.2
      have hFcor : F.1.idem.e ⊑ Cat.id F.1.carrier := F.2
      have hEsym : E.1.idem.e° = E.1.idem.e := E.1.idem.sym
      have hFsym : F.1.idem.e° = F.1.idem.e := F.1.idem.sym
      have hEidem : E.1.idem.e ≫ E.1.idem.e = E.1.idem.e := E.1.idem.idem
      have hFidem : F.1.idem.e ≫ F.1.idem.e = F.1.idem.e := F.1.idem.idem
      -- The two *absorbed* legs `f≫E.e`, `g≫F.e` only pre-tabulate Ψ.R; the apex idempotent is
      -- the coreflexive `D = 1 ∩ (f≫E.e≫f° ∩ g≫F.e≫g°)` on c (the domain of the absorbed pair).
      -- `legX≫legX° = (·≫E.e)≫(·≫E.e)° = ·≫E.e≫·°` (E.e sym+idem).
      let M : c ⟶ c := f ≫ E.1.idem.e ≫ f° ∩ g ≫ F.1.idem.e ≫ g°
      let D : c ⟶ c := Cat.id c ∩ M
      have hDcor : Coreflexive D := inter_lb_left _ _
      have hDsym : D° = D := symmetric_eq (coreflexive_symmetric_idempotent hDcor).1
      have hDidem : D ≫ D = D := (coreflexive_symmetric_idempotent hDcor).2
      have hDsimple : Simple D := by dsimp [Simple]; rw [hDsym, hDidem]; exact hDcor
      have hDle : D ⊑ Cat.id c := hDcor
      have hDM1 : D ⊑ f ≫ E.1.idem.e ≫ f° :=
        le_trans (inter_lb_right (Cat.id c) M) (inter_lb_left _ _)
      have hDM2 : D ⊑ g ≫ F.1.idem.e ≫ g° :=
        le_trans (inter_lb_right (Cat.id c) M) (inter_lb_right _ _)
      -- `legA≫legA° = D≫(f≫E.e≫f°)≫D`  (E.e sym+idem, D sym).
      have hLA : (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° = D ≫ (f ≫ E.1.idem.e ≫ f°) ≫ D := by
        simp only [Allegory.recip_comp, hDsym, hEsym, Cat.assoc]
        rw [← Cat.assoc E.1.idem.e E.1.idem.e (f° ≫ D), hEidem]
      have hLB : (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° = D ≫ (g ≫ F.1.idem.e ≫ g°) ≫ D := by
        simp only [Allegory.recip_comp, hDsym, hFsym, Cat.assoc]
        rw [← Cat.assoc F.1.idem.e F.1.idem.e (g° ≫ D), hFidem]
      -- `D ⊑ legA≫legA°`  (and `D ⊑ legB≫legB°`):  D = D≫D≫D ⊑ D≫(f≫E.e≫f°)≫D.
      have hEntA : D ⊑ (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° := by
        rw [hLA]
        calc D = D ≫ D ≫ D := by rw [hDidem, hDidem]
          _ ⊑ D ≫ (f ≫ E.1.idem.e ≫ f°) ≫ D := comp_mono_left D (comp_mono_right hDM1 D)
      have hEntB : D ⊑ (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° := by
        rw [hLB]
        calc D = D ≫ D ≫ D := by rw [hDidem, hDidem]
          _ ⊑ D ≫ (g ≫ F.1.idem.e ≫ g°) ≫ D := comp_mono_left D (comp_mono_right hDM2 D)
      -- `legA≫legA° ⊑ f≫f°`  (D ⊑ id both ends, E.e ⊑ id):  for joint `⊑ id_c`.
      -- `D≫X≫D ⊑ X` (both ends D ⊑ id):
      have hsandwich : ∀ {X : c ⟶ c}, D ≫ X ≫ D ⊑ X := by
        intro X
        have h1 : D ≫ X ≫ D ⊑ Cat.id c ≫ X ≫ Cat.id c := by
          refine le_trans (comp_mono_right hDle (X ≫ D)) ?_
          rw [Cat.id_comp, Cat.id_comp]
          exact comp_mono_left X hDle
        rwa [Cat.id_comp, Cat.comp_id] at h1
      have hLAf : (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° ⊑ f ≫ f° := by
        rw [hLA]
        refine le_trans hsandwich ?_
        calc f ≫ E.1.idem.e ≫ f° ⊑ f ≫ Cat.id E.1.carrier ≫ f° :=
              comp_mono_left f (comp_mono_right hEcor f°)
          _ = f ≫ f° := by rw [Cat.id_comp]
      have hLBg : (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° ⊑ g ≫ g° := by
        rw [hLB]
        refine le_trans hsandwich ?_
        calc g ≫ F.1.idem.e ≫ g° ⊑ g ≫ Cat.id F.1.carrier ≫ g° :=
              comp_mono_left g (comp_mono_right hFcor g°)
          _ = g ≫ g° := by rw [Cat.id_comp]
      -- Apex object `C = ⟨c, D⟩` in SplCorObj (D is its identity, splitting the coreflexive D).
      let C : SplCorObj 𝒜 := ⟨⟨c, ⟨D, hDsym, hDidem⟩⟩, hDcor⟩
      -- Legs `D≫f≫E.e : C ⟶ E`, `D≫g≫F.e : C ⟶ F` (D-fixed left, E.e/F.e-fixed right).
      let legA : C ⟶ E := ⟨D ≫ f ≫ E.1.idem.e, by
            show D ≫ (D ≫ f ≫ E.1.idem.e) ≫ E.1.idem.e = D ≫ f ≫ E.1.idem.e
            simp only [Cat.assoc]; rw [hEidem, ← Cat.assoc D D (f ≫ E.1.idem.e), hDidem]⟩
      let legB : C ⟶ F := ⟨D ≫ g ≫ F.1.idem.e, by
            show D ≫ (D ≫ g ≫ F.1.idem.e) ≫ F.1.idem.e = D ≫ g ≫ F.1.idem.e
            simp only [Cat.assoc]; rw [hFidem, ← Cat.assoc D D (g ≫ F.1.idem.e), hDidem]⟩
      -- `legA≫legA° ⊑ f≫E.e≫f°` and `legB≫legB° ⊑ g≫F.e≫g°` (both ends D ⊑ id):
      have hLAM : (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° ⊑ f ≫ E.1.idem.e ≫ f° := by
        rw [hLA]; exact hsandwich
      have hLBM : (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° ⊑ g ≫ F.1.idem.e ≫ g° := by
        rw [hLB]; exact hsandwich
      refine ⟨C, legA, legB, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      -- Map legA: Entire — id_C = D ⊑ legA≫legA° = D≫(f≫E.e≫f°)≫D.
      · unfold Entire dom; apply SplHom.ext
        show D ∩ (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° = D
        exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hEntA)
      -- Map legA: Simple — legA°≫legA = E.e≫f°≫D≫f≫E.e ⊑ id_E = E.e.
      · unfold Simple; apply SplHom.ext
        show (D ≫ f ≫ E.1.idem.e)° ≫ (D ≫ f ≫ E.1.idem.e) ⊑ E.1.idem.e
        -- normalise to `E.e≫f°≫D≫D≫f≫E.e`, collapse `D≫D=D`, bound `f°≫D≫f ⊑ f°≫f ⊑ id`.
        rw [Allegory.recip_comp, Allegory.recip_comp, hDsym, hEsym]
        simp only [Cat.assoc]
        rw [← Cat.assoc D D (f ≫ E.1.idem.e), hDidem]
        -- goal: E.e≫f°≫D≫f≫E.e ⊑ E.e
        have key : E.1.idem.e ≫ f° ≫ D ≫ f ≫ E.1.idem.e ⊑ E.1.idem.e ≫ (f° ≫ f) ≫ E.1.idem.e := by
          have hDf : f° ≫ D ≫ f ⊑ f° ≫ f := by
            refine comp_mono_left f° ?_
            have h := comp_mono_right hDle f; rwa [Cat.id_comp] at h
          have := comp_mono_left E.1.idem.e (comp_mono_right hDf E.1.idem.e)
          simpa only [Cat.assoc] using this
        refine le_trans key ?_
        have hsf : f° ≫ f ⊑ Cat.id E.1.carrier := hMapf.2
        calc E.1.idem.e ≫ (f° ≫ f) ≫ E.1.idem.e
            ⊑ E.1.idem.e ≫ Cat.id E.1.carrier ≫ E.1.idem.e :=
              comp_mono_left _ (comp_mono_right hsf _)
          _ = E.1.idem.e := by rw [Cat.id_comp, hEidem]
      -- Map legB: Entire.
      · unfold Entire dom; apply SplHom.ext
        show D ∩ (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° = D
        exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hEntB)
      -- Map legB: Simple.
      · unfold Simple; apply SplHom.ext
        show (D ≫ g ≫ F.1.idem.e)° ≫ (D ≫ g ≫ F.1.idem.e) ⊑ F.1.idem.e
        rw [Allegory.recip_comp, Allegory.recip_comp, hDsym, hFsym]
        simp only [Cat.assoc]
        rw [← Cat.assoc D D (g ≫ F.1.idem.e), hDidem]
        have key : F.1.idem.e ≫ g° ≫ D ≫ g ≫ F.1.idem.e ⊑ F.1.idem.e ≫ (g° ≫ g) ≫ F.1.idem.e := by
          have hDg : g° ≫ D ≫ g ⊑ g° ≫ g := by
            refine comp_mono_left g° ?_
            have h := comp_mono_right hDle g; rwa [Cat.id_comp] at h
          have := comp_mono_left F.1.idem.e (comp_mono_right hDg F.1.idem.e)
          simpa only [Cat.assoc] using this
        refine le_trans key ?_
        have hsg : g° ≫ g ⊑ Cat.id F.1.carrier := hMapg.2
        calc F.1.idem.e ≫ (g° ≫ g) ≫ F.1.idem.e
            ⊑ F.1.idem.e ≫ Cat.id F.1.carrier ≫ F.1.idem.e :=
              comp_mono_left _ (comp_mono_right hsg _)
          _ = F.1.idem.e := by rw [Cat.id_comp, hFidem]
      -- Ψ = legA° ≫ legB:  Ψ.R = E.e≫f°≫D≫g≫F.e.  The `⊒` step is the §2.166 factoring
      -- `(f≫E.e)°≫(g≫F.e) ⊑ (f≫E.e)°≫D≫(g≫F.e)`; `⊑` is `D ⊑ id`.
      · apply SplHom.ext
        show Ψ.R = (D ≫ f ≫ E.1.idem.e)° ≫ (D ≫ g ≫ F.1.idem.e)
        -- abbreviations p = f≫E.e, q = g≫F.e
        have hpp : (f ≫ E.1.idem.e) ≫ (f ≫ E.1.idem.e)° = f ≫ E.1.idem.e ≫ f° := by
          rw [Allegory.recip_comp, hEsym]; simp only [Cat.assoc]
          rw [← Cat.assoc E.1.idem.e E.1.idem.e f°, hEidem]
        have hqq : (g ≫ F.1.idem.e) ≫ (g ≫ F.1.idem.e)° = g ≫ F.1.idem.e ≫ g° := by
          rw [Allegory.recip_comp, hFsym]; simp only [Cat.assoc]
          rw [← Cat.assoc F.1.idem.e F.1.idem.e g°, hFidem]
        -- D' (the factoring's coreflexive) equals D.
        have hD' : Cat.id c ∩ (f ≫ E.1.idem.e) ≫ (f ≫ E.1.idem.e)°
                       ∩ (g ≫ F.1.idem.e) ≫ (g ≫ F.1.idem.e)° = D := by
          show Cat.id c ∩ (f ≫ E.1.idem.e) ≫ (f ≫ E.1.idem.e)°
                 ∩ (g ≫ F.1.idem.e) ≫ (g ≫ F.1.idem.e)° = Cat.id c ∩ M
          rw [hpp, hqq, Allegory.inter_assoc]
        -- the factoring, with D' rewritten to D.
        have hfac : (f ≫ E.1.idem.e)° ≫ (g ≫ F.1.idem.e)
            ⊑ (f ≫ E.1.idem.e)° ≫ D ≫ (g ≫ F.1.idem.e) := by
          have := splCor_factor (f ≫ E.1.idem.e) (g ≫ F.1.idem.e)
          rwa [hD'] at this
        -- expand both sides to E.e≫f°≫…  and prove equality by `le_antisymm`.
        have hL : (f ≫ E.1.idem.e)° ≫ (g ≫ F.1.idem.e) = E.1.idem.e ≫ f° ≫ g ≫ F.1.idem.e := by
          rw [Allegory.recip_comp, hEsym]; simp only [Cat.assoc]
        have hR : (D ≫ f ≫ E.1.idem.e)° ≫ (D ≫ g ≫ F.1.idem.e)
            = E.1.idem.e ≫ f° ≫ D ≫ g ≫ F.1.idem.e := by
          rw [Allegory.recip_comp, Allegory.recip_comp, hDsym, hEsym]; simp only [Cat.assoc]
          rw [← Cat.assoc D D (g ≫ F.1.idem.e), hDidem]
        rw [hR]
        -- Ψ.R = E.e≫f°≫g≫F.e (Ψ.R = f°≫g, Ψ E.e/F.e-fixed);  then sandwich-insert D.
        have hΨ : Ψ.R = E.1.idem.e ≫ f° ≫ g ≫ F.1.idem.e := by
          have hfix : E.1.idem.e ≫ Ψ.R ≫ F.1.idem.e = Ψ.R := Ψ.fixed
          rw [hRfg] at hfix ⊢; rw [← hfix]; simp only [Cat.assoc]
        rw [hΨ]
        apply le_antisymm
        · -- E.e≫f°≫g≫F.e ⊑ E.e≫f°≫D≫g≫F.e  (factoring; via hL, hfac)
          have := hfac; rw [hL] at this
          -- this : E.e≫f°≫g≫F.e ⊑ (f≫E.e)°≫D≫(g≫F.e); rewrite RHS
          have hRHS : (f ≫ E.1.idem.e)° ≫ D ≫ (g ≫ F.1.idem.e)
              = E.1.idem.e ≫ f° ≫ D ≫ g ≫ F.1.idem.e := by
            rw [Allegory.recip_comp, hEsym]; simp only [Cat.assoc]
          rwa [hRHS] at this
        · -- E.e≫f°≫D≫g≫F.e ⊑ E.e≫f°≫g≫F.e  (D ⊑ id)
          refine comp_mono_left E.1.idem.e (comp_mono_left f° ?_)
          have hDg : D ≫ g ≫ F.1.idem.e ⊑ g ≫ F.1.idem.e := by
            have h := comp_mono_right hDle (g ≫ F.1.idem.e); rwa [Cat.id_comp] at h
          simpa only [Cat.assoc] using hDg
      -- Joint: legA≫legA° ∩ legB≫legB° = D = id_C.
      · apply SplHom.ext
        show (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° ∩
             (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° = D
        apply le_antisymm
        · -- joint ⊑ D = id_c ∩ M
          apply le_inter
          · -- ⊑ id_c : joint ⊑ f≫f° ∩ g≫g° = id_c
            refine le_trans (le_inter (le_trans (inter_lb_left _ _) hLAf)
              (le_trans (inter_lb_right _ _) hLBg)) ?_
            rw [htab]; exact le_refl _
          · -- ⊑ M : joint ⊑ f≫E.e≫f° ∩ g≫F.e≫g°
            exact le_inter (le_trans (inter_lb_left _ _) hLAM)
              (le_trans (inter_lb_right _ _) hLBM)
        · exact le_inter hEntA hEntB
  }

/-- **§2.165**: If `𝒜` is a tabular allegory then `SplCorObj 𝒜` is pre-tabular.
    (Every morphism is already tabular, witnessed by `instTabularAllegorySplCor`.) -/
instance SplCorObj.instPreTabularAllegorySplCor {𝒜 : Type u} [TabularAllegory 𝒜] :
    PreTabularAllegory (SplCorObj 𝒜) :=
  { SplCorObj.instAllegorySplCor with
    pre_tabular := fun {E F} R =>
      ⟨R, le_refl _,
        @TabularAllegory.tabular (SplCorObj 𝒜) SplCorObj.instTabularAllegorySplCor E F R⟩ }

end Freyd.Alg
