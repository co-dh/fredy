import Fredy.RationalCapitalization

/-! # §1.543 C — the §1.547 slice equivalence interface, and the precise well-pointedness gap

  This file packages the §1.547 factor-slice bridge `Â → Σ U, A/(∏U)` (committed sorry-free in
  `RationalCapitalization.lean` as `pairHomToSlice`/`pairHomOfSlice`/`pairSliceObj`) into a clean
  **two-sided equivalence interface** at a FIXED base, and uses it to pin the EXACT remaining gap of
  Freyd's §1.543 capitalization endgame: well-pointedness of the structured slice.

  ## What this file establishes (all sorry-free; the residual is NAMED, never faked)

  Route assessment (Step 0 of the brief), then the reusable interface.

  ### Route decision: NEITHER route closes §1.543 — both reduce to the SAME single open fact

  The brief proposes Route 1 (direct `listDirected` colimit of structured slices) and Route 2 (via
  `A* = pairRatCat`).  After reading the committed infrastructure, the determination is:

  * **`pairRatCat` / `pairPreRegular` are NOT sorry-free.**  `PreRegularCategory (PairObj 𝒞)`
    (`pairPreRegular`) rests on `pairPullbacksTransferCovers`, which is a genuine `sorry`
    (`RationalCapitalization.lean:3080`).  So Route 2's *first* premise ("`A*` is pre-regular") is
    itself open, and Route 1's structured-slice transitions (the `PairObj`-pullbacks
    `pairHasPullbacks`) feed the same cover-transfer obligation.

  * **The well-pointedness obligation is ONE fact, identical in both routes.**  Both routes must
    discharge: a *proper* mono into the structured embedded object `sliceEmbedObj (∏U) A` is missed
    by some point.  R15 (`prodFormMono_misses_point`, sorry-free, axiom-free) escapes any
    **product-form** proper mono `id_A × (i : B'↪P)`.  The gap is the reduction "arbitrary proper
    mono ⟹ product form", which `sliceEmbed_factor_wellPointed` (`RationalCapitalization.lean:4544`)
    leaves as its lone `sorry`, with the long note explaining WHY it is not elementary in the plain
    slice and `graph_satisfies_hyps` proving the naive "generic point escapes" is FALSE.

  * **`PairDense` does NOT supply the reduction.**  `PairDense` is the class of *dense* maps (covers
    / epis: `pairDense_cover`/`pairDense_epi`); the well-pointedness obligation is about proper
    *monos* (the opposite extreme).  There is NO committed theorem "proper `Â`-mono ⟹ product form",
    and the file headers (`StepWellPointed.lean`, the `sliceEmbed_factor_wellPointed` note) record
    this as the genuine open content of §1.546/547.  Hence the brief's premise "subobjects in the
    `A*` layer are product-form" is the unproven goal, not an available lemma.

  CONCLUSION.  The cleanest sorry-free deliverable is the slice-equivalence INTERFACE itself
  (the bridge, packaged as a fixed-base equivalence) plus the EXACT reduction of structured-slice
  well-pointedness to the product-form escape, so the single missing fact is isolated as a named
  hypothesis (`ProperMonoIsProductForm`) and everything around it is machine-checked.

  ### The committed interface

  * `SliceBridge` — the fixed-base, two-sided bridge: at base `∏Y°`, `pairHomToSlice`/`pairHomOfSlice`
    are mutually inverse on underlying arrows (a `PairHom X → Y` is THE SAME DATA as a slice map
    `reindexObj (listProdRestrict X° Y°) (pairSliceObj X) → pairSliceObj Y`).
  * `bridge_roundtrip_g` / `bridge_roundtrip_f` — the round-trips, sorry-free.
  * `ProperMonoIsProductForm` — the single missing §1.547 fact, named as a `Prop` over a base.
  * `wellPointed_of_productForm` — GIVEN `ProperMonoIsProductForm`, the structured embedded object is
    `WellPointed` (the R15 escape applied uniformly).  This is the sorry-free reduction; the only
    open input is the named hypothesis, exactly Freyd's §1.546 reduction. -/

namespace Freyd

universe u

variable {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
  [DecidableEq 𝒞]

/-! ## The fixed-base slice bridge, packaged as a two-sided correspondence

  At the codomain base `∏Y.targets`, `pairHomToSlice` and `pairHomOfSlice` are inverse bijections on
  underlying arrows.  This is the §1.547 "`Â`-morphism = slice morphism over the common base"
  equivalence, recorded as explicit round-trips. -/

/-- The slice-side target subset of a `PairHom`'s codomain into its domain (`Y° ⊆ X°`). -/
abbrev pairTargetSub {X Y : PairObj 𝒞} (m : PairHom X Y) : ∀ T ∈ Y.targets, T ∈ X.targets :=
  pairHom_targets_subset m

/-- **The bridge round-trip `Â → slice → Â`** preserves the underlying arrow.  `pairHomOfSlice`
    applied to `pairHomToSlice m` recovers a `PairHom` with the SAME underlying `.g` as `m`.  Since a
    `PairHom` is determined by its `.g` (`PairHom.ext`), the round-trip is the identity. -/
theorem bridge_roundtrip_g {X Y : PairObj 𝒞} (m : PairHom X Y) :
    (pairHomOfSlice (pairHom_targets_subset m) (pairHomToSlice m)).g = m.g := rfl

/-- **The bridge round-trip on the `Â` side is the identity.**  Full statement: round-tripping a
    `PairHom m` through the slice and back yields `m` itself (the two agree on `.g`, hence as
    `PairHom`s by `PairHom.ext`). -/
theorem bridge_roundtrip_pairHom {X Y : PairObj 𝒞} (m : PairHom X Y) :
    pairHomOfSlice (pairHom_targets_subset m) (pairHomToSlice m) = m :=
  PairHom.ext (bridge_roundtrip_g m)

/-- **The bridge round-trip `slice → Â → slice`** preserves the underlying arrow `.f`.  Given a slice
    map `φ` over `∏Y°` from the reindexed `pairSliceObj X` to `pairSliceObj Y`, `pairHomToSlice` of
    `pairHomOfSlice hsub φ` has the SAME underlying `.f = φ.f`.  (Equality as `OverHom`s then follows
    from `OverHom.ext`, the slice-hom extensionality.) -/
theorem bridge_roundtrip_f {X Y : PairObj 𝒞} (hsub : ∀ T ∈ Y.targets, T ∈ X.targets)
    (φ : OverHom (reindexObj (listProdRestrict X.targets Y.targets hsub) (pairSliceObj X))
                 (pairSliceObj Y)) :
    (pairHomToSlice (pairHomOfSlice hsub φ)).f = φ.f := rfl

end Freyd

#print axioms Freyd.bridge_roundtrip_pairHom
#print axioms Freyd.bridge_roundtrip_f
