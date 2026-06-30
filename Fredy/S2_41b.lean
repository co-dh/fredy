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

import Fredy.MapCat
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

/-! ## §2.414  STATUS — the box-guard gap to the FULL topos

  Assembled here, sorry-free:
    • `TabularUnitaryPowerAllegory` — the merged hypothesis class (one `Allegory` base);
    • finite limits of `Map(A)` (from `mapPreLogos`, re-confirmed under the merged class);
    • `mapMem C` — the membership relation `∋_C ⊆ [C] × C` as a §1.9 `BinRel (Map A) [C] C`
      (jointly-monic span of maps, allegory relation `= eps C`, `memSpan_rel`);
    • `mapTranspose_existsUnique` — the §1.9 power-object universal property of `∋_C`
      RESTRICTED to relations of the membership's box.

  NOT assembled: the unrestricted `Topos (MapObj A)` (`has_pow` with `IsUniversalRel`, and
  `HasSubobjectClassifier`).  PRECISE BLOCKER: `IsUniversalRel mem` (S1_9) quantifies over
  ALL `R : BinRel (Map A) A C`, i.e. all allegory relations `R̄ : A → C`; classifying `R̄`
  needs a map `f` with `f ≫ ∋_C = R̄`, which `PowerAllegory.eps_thick` supplies ONLY when
  `codBox R̄ = codBox (∋_C)`.  This box-guard is FAITHFUL to Freyd (§2.41/§2.413/§2.431):
  his membership is box-indexed (`∋_R□ = R□`), so a single `eps C` is the membership on ONE
  box.  Concretely it fails for the EMPTY relation `𝟘 : A → C` (`codBox 𝟘 = 𝟘 ≠ codBox ∋_C`)
  — i.e. naming the empty subset `∅ ∈ [C]` — and for any non-co-entire `R̄`.

  Closing the gap needs ONE of:
    (i)  the box-indexed membership family `∋_K : [C]_K → C` for every coreflexive box
         `K ⊑ 1_C` (Freyd's `∋_{R□}`), constructible in a tabular allegory where
         coreflexives split, but NOT a field of the current `PowerAllegory` class; or
    (ii) an UNGUARDED thickness `∀ R̄, ∃ map f, f ≫ ∋_C = R̄` strengthening `eps_thick`
         (equivalently: `A(𝟘)` is a map — `[C]` has a bottom point `∅`).
  Both are genuine additions to the `PowerAllegory` interface, not derivable from its
  box-guarded `eps_thick`; hence the converse is delivered up to exactly this box-guard.

  This is the SAME interface gap recorded independently in `Fredy/Spl.lean` (Goal-B note,
  ~line 752): `codBox (∋ b) = 1` (i.e. `eps_entire : Entire (∋ b)`) "is NOT a consequence
  of the current `PowerAllegory` axioms".  NOTE that `eps_entire`/`codBox(∋)=1` alone is
  NECESSARY but NOT SUFFICIENT here: it only makes the matched box the FULL box `1_C`, which
  still excludes the non-co-entire relations (e.g. `𝟘`).  The full §1.9 universal property
  needs the strictly stronger (i)/(ii) above. -/

end Freyd.Alg
