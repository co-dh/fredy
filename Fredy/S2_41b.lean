/-
  Freyd & Scedrov, *Categories and Allegories* §2.414 (CONVERSE direction).

  §2.414: "If C is a topos then Rel(C) is a power allegory.  Conversely, if A is a
  unitary tabular power allegory then Map(A) is a topos."

  The FORWARD direction (`Topos C ⟹ PowerAllegory (Rel C)`) is `relPowerAllegory`
  in `Fredy.S2_41`.  This file is the CONVERSE: from a *unitary tabular power
  allegory* `A` we assemble the topos structure on `Map(A)`.

  The topos data of `Map(A)`:
    • finite limits — already proved in `Fredy.MapCat` (`mapPreLogos`): terminal =
      the unit object, binary products / pullbacks via tabulations.
    • power objects — `[C] = powerObj C` with membership `∋_C = eps C`; the §1.9
      universal relation is the tabulation of `eps C` as a jointly-monic span of
      maps in `Map(A)`.
    • subobject classifier — `Ω = [1] = powerObj (unit)`, classifying maps via the
      transpose `A(R) = R /ₛ ∋`.

  Diamond management: `TabularUnitaryAllegory` and `PowerAllegory` are separate
  classes over the same `Allegory` base, so carrying both as independent instances
  would give two `Allegory A` routes (the "synthesized instance not definitionally
  equal" diamond).  Following the repo's blessed pattern
  (`TabularUnitaryDistributiveAllegory`), we MERGE them into one class
  `TabularUnitaryPowerAllegory` extending `TabularUnitaryDistributiveAllegory`
  (which `mapPreLogos` and friends require) and `PowerAllegory` (which supplies
  `powerObj`/`eps`); the shared `DistributiveAllegory`→`Allegory` grandparent is
  unified by structure inheritance.  `PowerAllegory extends DivisionAllegory extends
  DistributiveAllegory`, so a power allegory is automatically distributive — the
  merge is well-formed.
-/

import Fredy.S2_147_MapCat
import Fredy.S2_4
import Fredy.S2_41
import Fredy.S1_9

universe v u

namespace Freyd.Alg

/-! ## §2.414  A TABULAR UNITARY POWER ALLEGORY

  Merged class: `TabularUnitaryDistributiveAllegory` + `PowerAllegory` over one
  `Allegory` base.  `PowerAllegory` already extends `DistributiveAllegory`, so the
  `DistributiveAllegory` grandparent is shared and the `Allegory` diamond collapses
  to a single instance — exactly the `TabularUnitaryDistributiveAllegory` pattern. -/

/-- A **TABULAR UNITARY POWER ALLEGORY** (§2.414 hypotheses): a tabular, unitary,
    (distributive) power allegory packaged as ONE class so the `Allegory` base is
    unique.  Freyd's converse: `Map(A)` of such an `A` is a topos. -/
class TabularUnitaryPowerAllegory (𝒜 : Type u) extends
    TabularUnitaryDistributiveAllegory 𝒜, PowerAllegory 𝒜

/-- A unitary tabular power allegory whose membership is UNGUARDED — Freyd's §2.414-converse
    hypothesis made precise (the EXTRA structure beyond a bare power allegory).  Both parents
    share one `PowerAllegory`/`Allegory` base (structure inheritance unifies the diamond), so
    `A`/`eps`/`mapCat` all resolve on the same instance.  `Map(A)` of such an `A` has FULL
    power objects (the universal-property half of the topos), via `A_is_map'`/`A_eps_eq'`. -/
class TabularUnitaryUnguardedPowerAllegory (𝒜 : Type u) extends
    TabularUnitaryPowerAllegory 𝒜, UnguardedPowerAllegory 𝒜

section
variable {𝒜 : Type u} [TabularUnitaryPowerAllegory 𝒜]

/-- Diamond check: under `[TabularUnitaryPowerAllegory 𝒜]` the `mapPreLogos` finite-limit
    instances (which need `TabularUnitaryDistributiveAllegory`) and the `PowerAllegory`
    operations resolve on the SAME `Allegory 𝒜` / `mapCat`.  If the two `Allegory`
    routes did not merge, the `eps`/`powerObj` (Power side) used next to `mapCat`
    (TUD side) would fail to typecheck. -/
noncomputable example : @HasBinaryProducts (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) := inferInstance
noncomputable example : @HasPullbacks (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) := inferInstance
noncomputable example : @HasTerminal (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) := inferInstance
example (C : 𝒜) : 𝒜 := PowerAllegory.powerObj C
example (C : 𝒜) : PowerAllegory.powerObj C ⟶ C := PowerAllegory.eps C

end

/-! ## §2.414  The membership span `∋_C ⊆ [C] × C` in `Map(A)`

  In `Rel(Set)`, `∋_C ⊆ P(C) × C` is the membership relation.  Allegorically, `eps C`
  IS that relation `[C] → C`; its tabulation `(p, q)` (a jointly-monic span of MAPS,
  source-apex convention `p : src → [C]`, `q : src → C`, with `p° ≫ q = eps C`) is the
  §1.9 jointly-monic span presentation of the membership — a `BinRel (Map A) [C] C`.
  Tabulation exists for EVERY morphism (tabular allegory), with no box-guard. -/

section MemSpan
variable {𝒜 : Type u} [TabularUnitaryPowerAllegory 𝒜]

/-- The apex of a chosen tabulation of `eps C`. -/
noncomputable def memSrc (C : 𝒜) : 𝒜 :=
  (TabularAllegory.tabular (𝒜 := 𝒜) (PowerAllegory.eps C)).choose

/-- First leg `src → [C]` of the membership tabulation (a map). -/
noncomputable def memP (C : 𝒜) : memSrc C ⟶ PowerAllegory.powerObj C :=
  (TabularAllegory.tabular (𝒜 := 𝒜) (PowerAllegory.eps C)).choose_spec.choose

/-- Second leg `src → C` of the membership tabulation (a map). -/
noncomputable def memQ (C : 𝒜) : memSrc C ⟶ C :=
  (TabularAllegory.tabular (𝒜 := 𝒜) (PowerAllegory.eps C)).choose_spec.choose_spec.choose

/-- The membership legs tabulate `eps C`: `Map (memP), Map (memQ), eps C = memP° ≫ memQ`,
    and `memP ≫ memP° ∩ memQ ≫ memQ° = id`. -/
theorem memTab (C : 𝒜) : Tabulates (memP C) (memQ C) (PowerAllegory.eps C) :=
  (TabularAllegory.tabular (𝒜 := 𝒜)
    (PowerAllegory.eps C)).choose_spec.choose_spec.choose_spec

/-- The allegory relation of the membership span is exactly `eps C` (`memP° ≫ memQ = ∋_C`). -/
theorem memSpan_rel (C : 𝒜) : (memP C)° ≫ (memQ C) = PowerAllegory.eps C :=
  ((memTab C).2.2.1).symm

/-- **§2.414**: the MEMBERSHIP RELATION `∋_C ⊆ [C] × C` of `Map(A)`, as a §1.9 binary
    relation (jointly-monic span of maps `[C] ← src → C`).  This is the topos-side
    universal relation targeted at `C`; its allegory relation is `eps C` (`memSpan_rel`).
    Joint-monicity in `Map(A)` is the allegory condition `pp° ∩ qq° = id` (§2.141,
    `tabulates_monic_pair`). -/
noncomputable def mapMem (C : 𝒜) :
    @BinRel (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) (PowerAllegory.powerObj C) C :=
  @BinRel.mk (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) (PowerAllegory.powerObj C) C
    (memSrc C) ⟨memP C, (memTab C).1⟩ ⟨memQ C, (memTab C).2.1⟩
    (by
      intro W f g hA hB
      apply Subtype.ext
      exact tabulates_monic_pair (memTab C).1 (memTab C).2.1 (memTab C).2.2.2
        f.val g.val f.property g.property (congrArg Subtype.val hA) (congrArg Subtype.val hB))

end MemSpan

/-! ## §2.414  Box-guarded universal property of `∋_C` in `Map(A)`

  The §1.9 universal-relation property says: for every relation `R̄ : A → C` there is a
  UNIQUE map `A → [C]` classifying it.  Allegorically the classifier is `A(R̄) = R̄ /ₛ ∋`,
  the unique map with `A(R̄) ≫ ∋_C = R̄` (`A_eps_eq` / `A_unique`).  Existence of the map
  carries Freyd's BOX-GUARD `codBox R̄ = codBox (∋_C)` (the `∋_R□ = R□` side-condition of
  §2.413/§2.431): the membership `∋_R` is defined only on the box `R□`.

  `mapTranspose_existsUnique` packages this as the box-restricted universal property of
  the membership span (`∋_C ≫ classifier = R̄`, uniquely, in `Map(A)`). -/

section UniversalProperty
variable {𝒜 : Type u} [TabularUnitaryPowerAllegory 𝒜]

/-- **§2.414 (box-guarded universal property)**: for a relation `R̄ : A → C` whose box
    matches the membership box (`codBox R̄ = codBox (∋_C)`), there is a UNIQUE
    `Map(A)`-morphism `f : A → [C]` with `f ≫ ∋_C = R̄` — the classifying map `A(R̄)`.
    This is the §1.9 power-object universal property of `∋_C` RESTRICTED to the box of
    the membership (cf. the gap note below). -/
theorem mapTranspose_existsUnique (C : 𝒜) {a : 𝒜} (R : a ⟶ C)
    (hbox : codBox R = codBox (PowerAllegory.eps C)) :
    ∃ f : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (PowerAllegory.powerObj C),
      f.val ≫ PowerAllegory.eps C = R ∧
      ∀ g : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (PowerAllegory.powerObj C),
        g.val ≫ PowerAllegory.eps C = R → g = f := by
  refine ⟨⟨A R, A_is_map R hbox⟩, A_eps_eq R hbox, ?_⟩
  intro g hgeq
  exact Subtype.ext (A_unique R g.val g.property hgeq)

/-- The classifying `Map(A)`-morphism `A → [C]` for a box-matched relation `R̄ : A → C`. -/
noncomputable def mapClassify (C : 𝒜) {a : 𝒜} (R : a ⟶ C)
    (hbox : codBox R = codBox (PowerAllegory.eps C)) :
    @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (PowerAllegory.powerObj C) :=
  ⟨A R, A_is_map R hbox⟩

/-- The classifier transposes back to `R̄`: `mapClassify(R̄) ≫ ∋_C = R̄`. -/
theorem mapClassify_eps (C : 𝒜) {a : 𝒜} (R : a ⟶ C)
    (hbox : codBox R = codBox (PowerAllegory.eps C)) :
    (mapClassify C R hbox).val ≫ PowerAllegory.eps C = R :=
  A_eps_eq R hbox

end UniversalProperty

/-! ## §2.414  Unguarded universal property — FULL power objects of `Map(A)`

  Under the UNGUARDED hypothesis (`TabularUnitaryUnguardedPowerAllegory`, Freyd's actual
  §2.414-converse structure), `∋_C` classifies EVERY relation, so the §1.9 universal property
  holds for all `R̄` — `Map(A)` has full (not box-restricted) power objects.  This closes the
  box-guard wall of the converse's universal-property half; the remaining half is `Ω = [1]`. -/

section UnguardedUP
variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerAllegory 𝒜]

/-- **§2.414-converse (full power objects)**: in a unitary tabular UNGUARDED power allegory,
    the membership `∋_C` of `Map(A)` has the §1.9 universal property for EVERY relation
    `R̄ : A → C` — a UNIQUE `Map(A)`-morphism `f : A → [C]` with `f ≫ ∋_C = R̄`.  No box guard
    (cf. the box-restricted `mapTranspose_existsUnique`); the `∅`-naming case (`R̄ = 𝟘`) is now
    included.  This is the universal-property half of "`Map(A)` is a topos". -/
theorem mapTranspose_existsUnique_all (C : 𝒜) {a : 𝒜} (R : a ⟶ C) :
    ∃ f : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (PowerAllegory.powerObj C),
      f.val ≫ PowerAllegory.eps C = R ∧
      ∀ g : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (PowerAllegory.powerObj C),
        g.val ≫ PowerAllegory.eps C = R → g = f := by
  refine ⟨⟨A R, A_is_map' R⟩, A_eps_eq' R, ?_⟩
  intro g hgeq
  exact Subtype.ext (A_unique R g.val g.property hgeq)

end UnguardedUP

/-! ## §2.414  STATUS — the FULL `Topos (MapObj A)` is assembled

  Assembled below, sorry-free (axioms `[propext, Classical.choice]`):
    • `TabularUnitaryUnguardedPowerAllegory` — Freyd's §2.414-converse hypothesis (one `Allegory`
      base); the UNGUARDED `∋` (`eps_thick_all`) closes the box-guard, so `A(R̄)` is a map and
      `A(R̄) ≫ ∋ = R̄` for EVERY relation `R̄` (`A_is_map'`/`A_eps_eq'`), the empty-naming case
      included.  `mapTranspose_existsUnique_all` is the resulting unrestricted §1.9 universal
      property of `∋_C`.
    • finite limits of `Map(A)` (`mapPreLogos`: `HasTerminal = unit`, products/pullbacks via
      tabulations);
    • **the SUBOBJECT CLASSIFIER** `Ω = [1]`, `true = A(1_1)`, with `classify`/`classify_sq`/
      `classify_pullback`/`classify_unique` — i.e. `HasSubobjectClassifier (MapObj 𝒜)`
      (`mapHasSubobjectClassifier`).  The keystone is `unit_eps_eq_singleton_recip` (`∋_1 = true°`).
    • **POWER OBJECTS** `[C] = powerObj C` with `mem = mapMem C` the §1.9 universal relation
      (`mapHasPowerObject`), and the **full `Topos (MapObj 𝒜)`** (`mapTopos`).

  The `has_pow` closure (`§2.414  POWER OBJECTS` section below).  `HasPowerObject` (S1_9) demands
  `IsUniversalRel (mem)`, phrased with `relPullback f mem ≅ R` (mutual `RelHom`) for every §1.9
  binary relation `R : BinRel (Map A) a C`.  This is bridged to the composition form
  `f.val ≫ ∋_C = R̄` (`mapTranspose_existsUnique_all`) WITHOUT the §2.41 `[Logos]`
  `relPullback ≅ graph f ⊚ U` machinery: `relOf_relPullback_of_tab` (`relOf (relPullback f U) =
  f.val ≫ relOf U`, via the §2.147 pullback CROSS-term `mapPullback_cross`) computes the allegory
  relation of `relPullback f (mapMem C)` directly, and the §2.217(2) BinRel↔allegory dictionary
  (`relOf_le_of_relLe`/`relLe_of_relOf_le`) converts "equal allegory relation" ⟺ "mutual `RelHom`". -/

/-! ## §2.414  SUBOBJECT CLASSIFIER  `Ω = [1]`  of `Map(A)`

  The §2.415 subobject classifier of the topos `Map(A)`: `Ω = [1] = powerObj (unit)`,
  with `true : 1 → Ω` the name `A(1_1)` of the maximal subobject of the unit.  A `Map(A)`-monic
  `m : C → a` is classified by `χ_m = A(m° ≫ p_C) : a → Ω` where `p_C = term C : C → 1`; the
  classifying square is the tabulation of `χ_m ≫ true°`, which equals the span `(m, term C)`.

  The whole construction rests on ONE allegory identity special to the unit:
  `∋_1 = (A 1_1)°`  (membership of the unit = reciprocal of its singleton), proved from
  `A_simple`/`A_eps_eq'` and `PartialUnit` (every endo of the unit `⊑ 1`). -/

section Classifier
variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerAllegory 𝒜]

/-- **§2.415 (crux)**: the membership `∋_1` of the unit equals the reciprocal of its singleton
    `A(1_1)`.  Both directions are elementary:
    (⊒) `(A 1)° = (A 1)° ≫ (A 1 ≫ ∋) = ((A 1)° ≫ A 1) ≫ ∋ ⊑ ∋`, using `A 1 ≫ ∋ = 1` (`A_eps_eq'`)
        and `A 1` simple (`A_simple`);
    (⊑) `∋° ⊑ A 1 = 1 /ₛ ∋` by `le_symmDiv_iff`: `∋° ≫ ∋ ⊑ 1` is exactly `PartialUnit` (an endo of
        the unit), and `∋ ≫ 1 ⊑ ∋` is reflexivity; reciprocate. -/
theorem unit_eps_eq_singleton_recip :
    (A (Cat.id (UnitaryAllegory.unit_obj : 𝒜)))°
      = PowerAllegory.eps (UnitaryAllegory.unit_obj : 𝒜) := by
  have hse : A (Cat.id (UnitaryAllegory.unit_obj : 𝒜)) ≫ PowerAllegory.eps _ = Cat.id _ :=
    A_eps_eq' (Cat.id (UnitaryAllegory.unit_obj : 𝒜))
  have hssimp : (A (Cat.id (UnitaryAllegory.unit_obj : 𝒜)))° ≫ A (Cat.id _) ⊑ Cat.id _ :=
    A_simple (Cat.id (UnitaryAllegory.unit_obj : 𝒜))
  apply le_antisymm
  · -- (A 1)° ⊑ ∋
    calc (A (Cat.id (UnitaryAllegory.unit_obj : 𝒜)))°
        = (A (Cat.id _))° ≫ (A (Cat.id _) ≫ PowerAllegory.eps _) := by rw [hse, Cat.comp_id]
      _ = ((A (Cat.id _))° ≫ A (Cat.id _)) ≫ PowerAllegory.eps _ := by rw [Cat.assoc]
      _ ⊑ Cat.id _ ≫ PowerAllegory.eps _ := comp_mono_right hssimp _
      _ = PowerAllegory.eps _ := Cat.id_comp _
  · -- ∋ ⊑ (A 1)°
    have he_le : (PowerAllegory.eps (UnitaryAllegory.unit_obj : 𝒜))°
        ⊑ A (Cat.id (UnitaryAllegory.unit_obj : 𝒜)) := by
      refine (le_symmDiv_iff _ (Cat.id _) (PowerAllegory.eps _)).mpr ⟨?_, ?_⟩
      · exact (UnitaryAllegory.unit_prop (𝒜 := 𝒜)).1 _
      · rw [Allegory.recip_recip, Cat.comp_id]; exact le_refl _
    have hrec := recip_mono he_le
    rwa [Allegory.recip_recip] at hrec

/-- A `Map(𝒜)`-monic `m` is a relational split mono: `m ≫ m° = 1_C`.  Injectivity
    (`m ≫ m° ⊑ 1`) is the kernel-pair argument (re-derived here, since `MapCat`'s `mapMonic_inj`
    is private), and `1 ⊑ m ≫ m°` is entirety of the map `m`. -/
theorem mapMonic_retract {C a : 𝒜}
    (m : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a)
    (hm : @Monic (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a m) :
    m.val ≫ m.val° = Cat.id C := by
  apply le_antisymm
  · obtain ⟨k, s, t, ht⟩ := TabularAllegory.tabular (𝒜 := 𝒜) (m.val ≫ m.val°)
    have hs : Map s := ht.1
    have htt : Map t := ht.2.1
    have hcone : s ≫ m.val = t ≫ m.val :=
      tab_pullback_cone' (f := m.val) (g := m.val) m.property m.property ht
    have hst : s = t := congrArg Subtype.val
      (hm ⟨s, hs⟩ ⟨t, htt⟩ (Subtype.ext hcone))
    calc m.val ≫ m.val° = s° ≫ t := ht.2.2.1
      _ = s° ≫ s := by rw [hst]
      _ ⊑ Cat.id C := hs.2
  · have h := m.property.1; rw [Entire, dom] at h; exact h ▸ inter_lb_right _ _

/-- **§2.415**: the subobject classifier `Ω = [1] = powerObj (unit)` of `Map(A)`. -/
noncomputable def mapOmega : MapObj 𝒜 := PowerAllegory.powerObj (UnitaryAllegory.unit_obj : 𝒜)

/-- **§2.415**: `true : 1 → Ω` is the name `A(1_1)` of the maximal subobject of the unit
    (the singleton map of the unit). -/
noncomputable def mapTrue :
    @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) (UnitaryAllegory.unit_obj : 𝒜) (mapOmega (𝒜 := 𝒜)) :=
  ⟨A (Cat.id (UnitaryAllegory.unit_obj : 𝒜)), A_is_map' _⟩

/-- `mapTrue` is a relational split mono on the nose: `true.val ≫ true.val° = 1_1`
    (singleton monic `singletonMap_monic` + entire `A_is_map'`). -/
theorem mapTrue_retract :
    (mapTrue (𝒜 := 𝒜)).val ≫ (mapTrue (𝒜 := 𝒜)).val° = Cat.id (UnitaryAllegory.unit_obj : 𝒜) := by
  apply le_antisymm
  · exact singletonMap_monic (a := (UnitaryAllegory.unit_obj : 𝒜))
  · have h := (A_is_map' (Cat.id (UnitaryAllegory.unit_obj : 𝒜))).1
    rw [Entire, dom] at h; exact h ▸ inter_lb_right _ _

/-- **§2.415**: `true : 1 → Ω` is monic in `Map(A)` (it is a relational split mono). -/
theorem mapTrue_monic :
    @Monic (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) _ _ (mapTrue (𝒜 := 𝒜)) := by
  intro W u v huv
  apply Subtype.ext
  have hval : u.val ≫ (mapTrue (𝒜 := 𝒜)).val = v.val ≫ (mapTrue (𝒜 := 𝒜)).val :=
    congrArg Subtype.val huv
  calc u.val
      = u.val ≫ ((mapTrue (𝒜 := 𝒜)).val ≫ (mapTrue (𝒜 := 𝒜)).val°) := by
        rw [mapTrue_retract, Cat.comp_id]
    _ = (u.val ≫ (mapTrue (𝒜 := 𝒜)).val) ≫ (mapTrue (𝒜 := 𝒜)).val° := by rw [Cat.assoc]
    _ = (v.val ≫ (mapTrue (𝒜 := 𝒜)).val) ≫ (mapTrue (𝒜 := 𝒜)).val° := by rw [hval]
    _ = v.val ≫ ((mapTrue (𝒜 := 𝒜)).val ≫ (mapTrue (𝒜 := 𝒜)).val°) := by rw [Cat.assoc]
    _ = v.val := by rw [mapTrue_retract, Cat.comp_id]

/-- The `Map(A)` terminal projection `C → 1 = term C`, retyped with the syntactic target
    `unit_obj` (the terminal `one` of `Map(A)` is `unit_obj` on the nose, `rfl`).  Pinning the
    target as `unit_obj` keeps `∋`/`powerObj` at `unit_obj` syntactically throughout, while
    `mapTerm C` is DEFINITIONALLY `term C`, so it slots into the `classify_sq` field. -/
noncomputable def mapTerm (C : MapObj 𝒜) :
    @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C (UnitaryAllegory.unit_obj : 𝒜) :=
  @Freyd.term (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) inferInstance C

/-- **§2.415**: the characteristic map `χ_m = A(m° ≫ p_C) : a → Ω` of a `Map(A)`-monic
    `m : C → a`, where `p_C = term C : C → 1`.  It names the relation `a → 1` whose extension is
    the image of `m`. -/
noncomputable def mapClassifyChi {C a : 𝒜}
    (m : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a)
    (_hm : @Monic (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a m) :
    @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (mapOmega (𝒜 := 𝒜)) :=
  ⟨A (m.val° ≫ (mapTerm C).val), A_is_map' _⟩

/-- **§2.415 (classifying square commutes)**: `m ≫ χ_m = (term C) ≫ true`.  Both sides are maps
    `C → Ω` whose composite with `∋_1` is `term C` (LHS uses `m ≫ m° = 1`; RHS uses `true ≫ ∋ = 1`),
    so both equal `A(term C)` by `A_unique`. -/
theorem mapClassify_sq {C a : 𝒜}
    (m : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a)
    (hm : @Monic (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a m) :
    @Cat.comp (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a (mapOmega (𝒜 := 𝒜)) m (mapClassifyChi m hm)
      = @Cat.comp (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C (UnitaryAllegory.unit_obj : 𝒜)
          (mapOmega (𝒜 := 𝒜)) (mapTerm C) (mapTrue (𝒜 := 𝒜)) := by
  apply Subtype.ext
  show m.val ≫ A (m.val° ≫ (mapTerm C).val)
      = (mapTerm C).val ≫ A (Cat.id (UnitaryAllegory.unit_obj : 𝒜))
  have hmm : m.val ≫ m.val° = Cat.id C := mapMonic_retract m hm
  have hLmap : Map (m.val ≫ A (m.val° ≫ (mapTerm C).val)) :=
    map_comp m.property (A_is_map' _)
  have hRmap : Map ((mapTerm C).val ≫ A (Cat.id (UnitaryAllegory.unit_obj : 𝒜))) :=
    map_comp (mapTerm C).property (A_is_map' _)
  have hL : (m.val ≫ A (m.val° ≫ (mapTerm C).val))
        ≫ PowerAllegory.eps (UnitaryAllegory.unit_obj : 𝒜) = (mapTerm C).val := by
    rw [Cat.assoc, A_eps_eq', ← Cat.assoc, hmm, Cat.id_comp]
  have hR : ((mapTerm C).val ≫ A (Cat.id (UnitaryAllegory.unit_obj : 𝒜)))
        ≫ PowerAllegory.eps (UnitaryAllegory.unit_obj : 𝒜) = (mapTerm C).val := by
    rw [Cat.assoc, A_eps_eq', Cat.comp_id]
  rw [A_unique _ _ hLmap hL, A_unique _ _ hRmap hR]

/-- **§2.415**: the classifying span `(m, term C)` TABULATES `χ_m ≫ true°`.  Relation condition:
    `χ_m ≫ true° = A(R̄) ≫ ∋_1 = R̄ = m° ≫ p_C` (crux `true° = ∋_1`, then `A_eps_eq'`).  Joint
    monicity: `m ≫ m° ∩ p_C ≫ p_C° = 1_C ∩ X = 1_C` (`mapMonic_retract` + entire `p_C`). -/
theorem mapClassify_tabulates {C a : 𝒜}
    (m : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a)
    (hm : @Monic (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a m) :
    Tabulates m.val (mapTerm C).val
      ((mapClassifyChi m hm).val ≫ (mapTrue (𝒜 := 𝒜)).val°) := by
  refine ⟨m.property, (mapTerm C).property, ?_, ?_⟩
  · show A (m.val° ≫ (mapTerm C).val) ≫ (A (Cat.id (UnitaryAllegory.unit_obj : 𝒜)))°
        = m.val° ≫ (mapTerm C).val
    rw [unit_eps_eq_singleton_recip, A_eps_eq']
  · rw [mapMonic_retract m hm]
    have hent : Cat.id C ⊑ (mapTerm C).val ≫ (mapTerm C).val° := by
      have h := (mapTerm C).property.1; rw [Entire, dom] at h; exact h ▸ inter_lb_right _ _
    exact inter_eq_left hent

/-- The classifying cone `(C, m, term C)` over `(χ_m, true)`, with the `Cat` instance pinned to
    `mapCat` (the priority-0 instance is otherwise mis-synthesized in the anonymous constructor). -/
noncomputable def mapClassifyCone {C a : 𝒜}
    (m : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a)
    (hm : @Monic (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a m) :
    @Cone (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (UnitaryAllegory.unit_obj : 𝒜) (mapOmega (𝒜 := 𝒜))
      (mapClassifyChi m hm) (mapTrue (𝒜 := 𝒜)) :=
  @Cone.mk (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (UnitaryAllegory.unit_obj : 𝒜) (mapOmega (𝒜 := 𝒜))
    (mapClassifyChi m hm) (mapTrue (𝒜 := 𝒜)) C m (mapTerm C) (mapClassify_sq m hm)

/-- **§2.415 (classifying square is a pullback)**: the cone `(C, m, term C)` over
    `(χ_m, true)` is a pullback in `Map(A)`.  Transports the §2.147 tabulation pullback UMP
    (`tab_pullback_UMP`) for the tabulation `(m, term C)` of `χ_m ≫ true°` into `Cone.IsPullback`. -/
theorem mapClassify_pullback {C a : 𝒜}
    (m : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a)
    (hm : @Monic (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a m) :
    @Cone.IsPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (UnitaryAllegory.unit_obj : 𝒜)
      (mapOmega (𝒜 := 𝒜)) (mapClassifyChi m hm) (mapTrue (𝒜 := 𝒜))
      (mapClassifyCone m hm) := by
  intro d
  have htab := mapClassify_tabulates m hm
  -- Pin every cone-field access to `mapCat` (priority-0 instance is otherwise mis-synthesized).
  let dπ₁ := @Cone.π₁ (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (UnitaryAllegory.unit_obj : 𝒜)
    (mapOmega (𝒜 := 𝒜)) (mapClassifyChi m hm) (mapTrue (𝒜 := 𝒜)) d
  let dπ₂ := @Cone.π₂ (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (UnitaryAllegory.unit_obj : 𝒜)
    (mapOmega (𝒜 := 𝒜)) (mapClassifyChi m hm) (mapTrue (𝒜 := 𝒜)) d
  have hcone_val := congrArg Subtype.val (@Cone.w (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a
    (UnitaryAllegory.unit_obj : 𝒜) (mapOmega (𝒜 := 𝒜)) (mapClassifyChi m hm) (mapTrue (𝒜 := 𝒜)) d)
  obtain ⟨hlift, hlift_map, h1, h2, huniq⟩ :=
    tab_pullback_UMP (f := (mapClassifyChi m hm).val) (g := (mapTrue (𝒜 := 𝒜)).val)
      (mapClassifyChi m hm).property (mapTrue (𝒜 := 𝒜)).property htab
      dπ₁.property dπ₂.property hcone_val
  refine ⟨⟨hlift, hlift_map⟩, ⟨Subtype.ext h1, Subtype.ext h2⟩, ?_⟩
  intro v hv1 hv2
  exact Subtype.ext (huniq v.val v.property (congrArg Subtype.val hv1) (congrArg Subtype.val hv2))

/-- **§2.415 (uniqueness of the characteristic map)**: any `χ : a → Ω` making `(C, m, term C)` a
    pullback of `(χ, true)` equals `χ_m`.  The classifying relation `χ ≫ ∋_1` is pinned to
    `m° ≫ p_C` by two inclusions — easy `m° ≫ p_C ⊑ χ ≫ ∋_1` from the square (`hsq`) + `m` simple;
    hard `χ ≫ ∋_1 ⊑ m° ≫ p_C` from the pullback's lift `ψ` of the tabulation cone of `χ ≫ ∋_1`,
    using `ψ` simple — so `χ = A(m° ≫ p_C) = χ_m` by `A_unique`. -/
theorem mapClassify_unique {C a : 𝒜}
    (m : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a)
    (hm : @Monic (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a m)
    (χ : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (mapOmega (𝒜 := 𝒜)))
    (hsq : @Cat.comp (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C a (mapOmega (𝒜 := 𝒜)) m χ
        = @Cat.comp (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) C (UnitaryAllegory.unit_obj : 𝒜)
            (mapOmega (𝒜 := 𝒜)) (mapTerm C) (mapTrue (𝒜 := 𝒜)))
    (hpb : @Cone.IsPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (UnitaryAllegory.unit_obj : 𝒜)
        (mapOmega (𝒜 := 𝒜)) χ (mapTrue (𝒜 := 𝒜))
        (@Cone.mk (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (UnitaryAllegory.unit_obj : 𝒜)
          (mapOmega (𝒜 := 𝒜)) χ (mapTrue (𝒜 := 𝒜)) C m (mapTerm C) hsq)) :
    χ = mapClassifyChi m hm := by
  have hsq_val : m.val ≫ χ.val = (mapTerm C).val ≫ (mapTrue (𝒜 := 𝒜)).val :=
    congrArg Subtype.val hsq
  have hcrux : (mapTrue (𝒜 := 𝒜)).val° = PowerAllegory.eps (UnitaryAllegory.unit_obj : 𝒜) :=
    unit_eps_eq_singleton_recip
  -- easy inclusion: m° ≫ p_C ⊑ χ ≫ true°
  have p_eq : (mapTerm C).val = m.val ≫ (χ.val ≫ (mapTrue (𝒜 := 𝒜)).val°) := by
    calc (mapTerm C).val
        = (mapTerm C).val ≫ ((mapTrue (𝒜 := 𝒜)).val ≫ (mapTrue (𝒜 := 𝒜)).val°) := by
          rw [mapTrue_retract, Cat.comp_id]
      _ = ((mapTerm C).val ≫ (mapTrue (𝒜 := 𝒜)).val) ≫ (mapTrue (𝒜 := 𝒜)).val° := by rw [Cat.assoc]
      _ = (m.val ≫ χ.val) ≫ (mapTrue (𝒜 := 𝒜)).val° := by rw [← hsq_val]
      _ = m.val ≫ (χ.val ≫ (mapTrue (𝒜 := 𝒜)).val°) := Cat.assoc _ _ _
  have easy : m.val° ≫ (mapTerm C).val ⊑ χ.val ≫ (mapTrue (𝒜 := 𝒜)).val° := by
    rw [p_eq, ← Cat.assoc]
    calc (m.val° ≫ m.val) ≫ (χ.val ≫ (mapTrue (𝒜 := 𝒜)).val°)
        ⊑ Cat.id a ≫ (χ.val ≫ (mapTrue (𝒜 := 𝒜)).val°) := comp_mono_right m.property.2 _
      _ = χ.val ≫ (mapTrue (𝒜 := 𝒜)).val° := Cat.id_comp _
  -- hard inclusion: χ ≫ true° ⊑ m° ≫ p_C, via the pullback's lift of the tabulation cone
  obtain ⟨P, π₁, π₂, ht_tab⟩ := TabularAllegory.tabular (𝒜 := 𝒜)
    (χ.val ≫ (mapTrue (𝒜 := 𝒜)).val°)
  have hpc : π₁ ≫ χ.val = π₂ ≫ (mapTrue (𝒜 := 𝒜)).val :=
    tab_pullback_cone' (f := χ.val) (g := (mapTrue (𝒜 := 𝒜)).val) χ.property
      (mapTrue (𝒜 := 𝒜)).property ht_tab
  obtain ⟨ψ, ⟨hψm, hψt⟩, _⟩ := hpb (@Cone.mk (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a
    (UnitaryAllegory.unit_obj : 𝒜) (mapOmega (𝒜 := 𝒜)) χ (mapTrue (𝒜 := 𝒜)) P
    ⟨π₁, ht_tab.1⟩ ⟨π₂, ht_tab.2.1⟩ (Subtype.ext hpc))
  have hψ₁ : ψ.val ≫ m.val = π₁ := congrArg Subtype.val hψm
  have hψ₂ : ψ.val ≫ (mapTerm C).val = π₂ := congrArg Subtype.val hψt
  have hard : χ.val ≫ (mapTrue (𝒜 := 𝒜)).val° ⊑ m.val° ≫ (mapTerm C).val := by
    calc χ.val ≫ (mapTrue (𝒜 := 𝒜)).val°
        = π₁° ≫ π₂ := ht_tab.2.2.1
      _ = (ψ.val ≫ m.val)° ≫ π₂ := by rw [hψ₁]
      _ = m.val° ≫ (ψ.val° ≫ π₂) := by rw [Allegory.recip_comp, Cat.assoc]
      _ = m.val° ≫ (ψ.val° ≫ (ψ.val ≫ (mapTerm C).val)) := by rw [hψ₂]
      _ = m.val° ≫ ((ψ.val° ≫ ψ.val) ≫ (mapTerm C).val) := by
          rw [← Cat.assoc ψ.val° ψ.val (mapTerm C).val]
      _ ⊑ m.val° ≫ (Cat.id C ≫ (mapTerm C).val) :=
          comp_mono_left _ (comp_mono_right ψ.property.2 _)
      _ = m.val° ≫ (mapTerm C).val := by rw [Cat.id_comp]
  -- combine and identify χ with A(m° ≫ p_C)
  have hχ : χ.val ≫ PowerAllegory.eps (UnitaryAllegory.unit_obj : 𝒜)
      = m.val° ≫ (mapTerm C).val := by
    rw [← hcrux]; exact le_antisymm hard easy
  exact Subtype.ext (A_unique (m.val° ≫ (mapTerm C).val) χ.val χ.property hχ)

/-- **§2.414/§2.415**: `Map(A)` of a tabular unitary UNGUARDED power allegory has a SUBOBJECT
    CLASSIFIER `Ω = [1]`, with universal monic `true = A(1_1) : 1 → Ω`.  Every `Map(A)`-monic `m`
    has a unique characteristic map `χ_m = A(m° ≫ p)` whose classifying square is a pullback
    (`mapClassifyChi`/`mapClassify_sq`/`mapClassify_pullback`/`mapClassify_unique`).  The terminal
    and pullback parents are the finite-limit structure of `mapPreLogos`. -/
noncomputable instance mapHasSubobjectClassifier :
    @HasSubobjectClassifier (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) :=
  @HasSubobjectClassifier.mk (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasTerminal mapHasPullbacks
    mapOmega mapTrue
    (fun {A A'} m hm => mapClassifyChi (C := A') (a := A) m hm)
    (fun {A A'} m hm => mapClassify_sq (C := A') (a := A) m hm)
    (fun {A A'} m hm => mapClassify_pullback (C := A') (a := A) m hm)
    (fun {A A'} m hm χ hsq hcone => mapClassify_unique (C := A') (a := A) m hm χ hsq hcone)

-- Usability check: the classifier is found by instance resolution, and `Map(A)`'s topos data is
-- complete except `has_pow`.
noncomputable example : @HasSubobjectClassifier (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) := inferInstance
noncomputable example : @HasBinaryProducts (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) := inferInstance

end Classifier

/-! ## §2.414  POWER OBJECTS  `[C]`  of `Map(A)` — the final `has_pow` gap

  The §1.9 power object `[C]` of `Map(A)` is `PowerAllegory.powerObj C` with membership the
  span `mapMem C` (allegory relation `∋_C = eps C`).  `HasPowerObject` demands the §1.9
  `IsUniversalRel (mapMem C)`, phrased with `relPullback f (mapMem C) ≅ R` (mutual `RelHom`)
  for every §1.9 binary relation `R : BinRel (Map A) A C`.  We bridge this to the composition
  form `f.val ≫ ∋_C = R̄` (`mapTranspose_existsUnique_all`) WITHOUT the §2.41 `[Logos]`
  `relPullback ≅ graph f ⊚ U` machinery: the §2.147 pullback CROSS-term (`mapPullback_cross`,
  `pb.π₁°≫pb.π₂ = f≫g°`) computes the allegory relation of `relPullback f (mapMem C)` directly,
  and the §2.217(2) BinRel↔allegory dictionary (`relOf_le_of_relLe`/`relLe_of_relOf_le`) turns
  "equal allegory relation" into "mutual `RelHom`" and back.

  `HasPullbacks` pinning: `IsUniversalRel`/`HasPowerObject` take `[HasPullbacks 𝒞]` as a
  parameter, so the `relPullback` inside them uses whichever instance is inferred.  We pin
  `mapHasPullbacks` in the bridge lemma, in `@IsUniversalRel`, and in `@HasPowerObject.mk`, so
  all three see the SAME pullback route (Freyd's tabulation pullbacks) and unify. -/

section RelPullbackRelOf
variable {𝒜 : Type u} [TabularUnitaryDistributiveAllegory 𝒜]

/-- **§2.414 bridge (general)**: the allegory relation of a §1.9 relation-pullback in `Map(A)`
    is `relOf (relPullback f U) = f.val ≫ relOf U`.  Proof (over a bare distributive tabular
    allegory, so the `relColA`/`relColB` dictionary applies with no `PowerAllegory` diamond):
    `relPullback f U` has legs `π₁ : pb → a` and `π₂ ≫ U.colB : pb → c`, so its `relOf` is
    `π₁.val° ≫ (π₂.val ≫ U.colB.val) = (π₁.val° ≫ π₂.val) ≫ U.colB.val = (f.val ≫ U.colA.val°)
    ≫ U.colB.val = f.val ≫ (U.colA.val° ≫ U.colB.val) = f.val ≫ relOf U`, using the §2.147
    pullback cross-term `mapPullback_cross` (`π₁°≫π₂ = f≫g°`). -/
theorem relOf_relPullback_of_tab {a p c : 𝒜}
    (f : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a p)
    (U : @BinRel (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) p c) :
    relOf (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks p c a f U)
      = f.val ≫ relOf U := by
  -- Pin cone projections via `@Cone.π₁/π₂` (the dot form `pb.cone.π₁` mis-resolves the priority-0
  -- `mapCat`; see `relOf_compose`).
  let uA := @BinRel.colA (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) p c U
  let pb := @HasPullbacks.has (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks a
              (@BinRel.src (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) p c U) p f uA
  let π₁ := @Cone.π₁ (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) _ _ _ f uA pb.cone
  let π₂ := @Cone.π₂ (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) _ _ _ f uA pb.cone
  have hcross : π₁.val° ≫ π₂.val = f.val ≫ (relColA U)° := mapPullback_cross f uA pb
  have hcA : relColA (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks p c a f U)
      = π₁.val := rfl
  have hcB : relColB (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks p c a f U)
      = π₂.val ≫ relColB U := rfl
  calc relOf (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks p c a f U)
      = (relColA (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks p c a f U))°
          ≫ relColB (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks p c a f U) :=
        rfl
    _ = π₁.val° ≫ (π₂.val ≫ relColB U) := by rw [hcA, hcB]
    _ = (π₁.val° ≫ π₂.val) ≫ relColB U := by rw [← Cat.assoc]
    _ = (f.val ≫ (relColA U)°) ≫ relColB U := by rw [hcross]
    _ = f.val ≫ ((relColA U)° ≫ relColB U) := by rw [Cat.assoc]
    _ = f.val ≫ relOf U := rfl

/-- Allegory-order reflexivity from equality (`R = S ⟹ R ⊑ S`). -/
theorem relLe_of_eq {a b : 𝒜} {R S : a ⟶ b} (h : R = S) : R ⊑ S := h ▸ le_refl R

/-- **§2.217(2) dictionary**: equal allegory relation ⟹ mutual `RelHom` in `Map(A)`.  Both
    directions of `relLe_of_relOf_le` (the reverse dictionary), one per inequality. -/
theorem mutual_relHom_of_relOf_eq {a b : 𝒜}
    (E F : @BinRel (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a b) (h : relOf E = relOf F) :
    @RelHom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a b E F
      ∧ @RelHom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a b F E := by
  obtain ⟨w1⟩ := relLe_of_relOf_le (relLe_of_eq h)
  obtain ⟨w2⟩ := relLe_of_relOf_le (relLe_of_eq h.symm)
  exact ⟨w1, w2⟩

end RelPullbackRelOf

section PowerObjects
variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerAllegory 𝒜]

/-- `relOf (mapMem C) = ∋_C = eps C`: the allegory relation of the membership span is the
    epsilon (`relColA° ≫ relColB = memP° ≫ memQ = eps C`, `memSpan_rel`). -/
theorem relOf_mapMem (C : 𝒜) : relOf (mapMem C) = PowerAllegory.eps C := memSpan_rel C

/-- **§2.414 bridge (A)**: the allegory relation of the §1.9 pullback `relPullback f (mapMem C)`
    (in `Map(A)`) is `f.val ≫ ∋_C`.  Immediate from the general `relOf_relPullback_of_tab`
    (`relOf (relPullback f U) = f.val ≫ relOf U`) plus `relOf_mapMem` (`relOf (mapMem C) = ∋_C`). -/
theorem relOf_relPullback_mem (C : 𝒜) {a : 𝒜}
    (f : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (PowerAllegory.powerObj C)) :
    relOf (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
        (PowerAllegory.powerObj C) C a f (mapMem C))
      = f.val ≫ PowerAllegory.eps C := by
  rw [relOf_relPullback_of_tab f (mapMem C), relOf_mapMem]

/-- **§2.414 (universality, existence)**: every §1.9 relation `R : BinRel (Map A) a C` is
    classified by a UNIQUE map `f : a → [C]` with `R ≅ relPullback f (mapMem C)`.  The classifier
    is the transpose `f = A(R̄)` (`mapTranspose_existsUnique_all`) of `R̄ = relOf R`; the iso
    `R ≅ relPullback f (mapMem C)` is "equal allegory relation" (bridge A: `relOf (relPullback f
    (mapMem C)) = f.val ≫ ∋_C = R̄ = relOf R`) turned into mutual `RelHom` by the dictionary. -/
theorem mapClassifyExists (C : 𝒜) (a : 𝒜)
    (R : @BinRel (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a C) :
    ∃ f : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (PowerAllegory.powerObj C),
      @RelHom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a C R
          (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
            (PowerAllegory.powerObj C) C a f (mapMem C))
        ∧ @RelHom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a C
          (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
            (PowerAllegory.powerObj C) C a f (mapMem C)) R := by
  obtain ⟨f, hf, _⟩ := mapTranspose_existsUnique_all C (relOf R)
  have key : relOf (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
      (PowerAllegory.powerObj C) C a f (mapMem C)) = relOf R := by
    rw [relOf_relPullback_mem]; exact hf
  obtain ⟨w1, w2⟩ := mutual_relHom_of_relOf_eq R _ key.symm
  exact ⟨f, w1, w2⟩

/-- **§2.414 (universality, uniqueness)**: the classifying map is unique.  If `f, g : a → [C]`
    both present `R` as `relPullback · (mapMem C)`, then `f.val ≫ ∋_C = relOf R = g.val ≫ ∋_C`
    (bridge A + the dictionary), so `f = g` by `mapTranspose_existsUnique_all`'s uniqueness. -/
theorem mapClassifyUnique (C : 𝒜) (a : 𝒜)
    (R : @BinRel (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a C)
    (f g : @Cat.Hom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a (PowerAllegory.powerObj C))
    (hf : @RelHom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a C R
            (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
              (PowerAllegory.powerObj C) C a f (mapMem C))
          ∧ @RelHom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a C
            (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
              (PowerAllegory.powerObj C) C a f (mapMem C)) R)
    (hg : @RelHom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a C R
            (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
              (PowerAllegory.powerObj C) C a g (mapMem C))
          ∧ @RelHom (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) a C
            (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
              (PowerAllegory.powerObj C) C a g (mapMem C)) R) :
    f = g := by
  obtain ⟨f0, _, huniq⟩ := mapTranspose_existsUnique_all C (relOf R)
  have hfe : relOf (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
      (PowerAllegory.powerObj C) C a f (mapMem C)) = relOf R :=
    le_antisymm (relOf_le_of_relLe ⟨hf.2⟩) (relOf_le_of_relLe ⟨hf.1⟩)
  have hge : relOf (@Freyd.relPullback (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
      (PowerAllegory.powerObj C) C a g (mapMem C)) = relOf R :=
    le_antisymm (relOf_le_of_relLe ⟨hg.2⟩) (relOf_le_of_relLe ⟨hg.1⟩)
  have hfeps : f.val ≫ PowerAllegory.eps C = relOf R := by rw [← relOf_relPullback_mem C f]; exact hfe
  have hgeps : g.val ≫ PowerAllegory.eps C = relOf R := by rw [← relOf_relPullback_mem C g]; exact hge
  rw [huniq f hfeps, huniq g hgeps]

/-- **§2.414-converse (power objects)**: `∋_C = mapMem C` is a §1.9 UNIVERSAL relation targeted
    at `C` (`mapClassifyExists`/`mapClassifyUnique`). -/
theorem mapIsUniversal (C : 𝒜) :
    @IsUniversalRel (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
      (PowerAllegory.powerObj C) C (mapMem C) :=
  @IsUniversalRel.mk (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks
    (PowerAllegory.powerObj C) C (mapMem C)
    (fun a R => mapClassifyExists C a R)
    (fun a R f g hf hg => mapClassifyUnique C a R f g hf hg)

/-- **§2.414-converse (has_pow)**: every object `C` of `Map(A)` has a POWER OBJECT
    `[C] = PowerAllegory.powerObj C` with membership span `mapMem C` (allegory relation `∋_C`) as
    its §1.9 universal relation. -/
noncomputable instance mapHasPowerObject (C : 𝒜) :
    @HasPowerObject (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks C :=
  @HasPowerObject.mk (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasPullbacks C
    (PowerAllegory.powerObj C) (mapMem C) (mapIsUniversal C)

/-- **§2.414-converse (TOPOS)**: `Map(A)` of a tabular unitary UNGUARDED power allegory is a
    TOPOS.  Finite limits + `HasBinaryProducts` are `mapPreLogos`; the subobject classifier
    `Ω = [1]` is `mapHasSubobjectClassifier`; power objects are `mapHasPowerObject`. -/
noncomputable instance mapTopos : @Topos.{v} (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) :=
  @Topos.mk (MapObj 𝒜) (mapCat (𝒜 := 𝒜)) mapHasBinaryProducts mapHasSubobjectClassifier
    (fun C => mapHasPowerObject C)

end PowerObjects

end Freyd.Alg
