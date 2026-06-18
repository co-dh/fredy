import Fredy.RationalCapitalization
import Fredy.S1_36 -- `eqToHom`: cast-free transport along object equalities (for the fixed-`U` base)

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

/-! ## The well-pointedness reduction: from product-form to the R15 escape

  This is the genuine §1.546/547 content, isolated so the single missing fact is a NAMED
  hypothesis and the escape around it is machine-checked.  Freyd's §1.546 escape
  (`prodFormMono_misses_point`, sorry-free, axiom-free) handles any *product-form* proper mono
  `id_A × (i : B'↪P)`.  The open content (`sliceEmbed_factor_wellPointed`'s `sorry`) is the
  reduction of an *arbitrary* proper mono to product form.  We name exactly that reduction as
  `ProperMonoIsProductForm` and prove the well-pointedness payoff from it sorry-free. -/

variable [PullbacksTransferCovers 𝒞]

/-- **The single missing §1.546/547 fact, named.**  Every proper mono `m : D ↪ sliceEmbedObj P A`
    in the slice `Over P` factors as an iso of its domain followed by a PRODUCT-FORM mono
    `prodFormMono i` (for a proper base mono `i : B' ↪ P`): there is a proper monic `i : B' ↪ P` and
    a slice iso `e : D ≅ ⟨A×B', snd≫i⟩` with `e ≫ prodFormMono i = m`.  This is Freyd's §1.546
    reduction — "every subobject of `AB` is of the form `AB'`" — which is NOT elementary in the plain
    slice (`graph_satisfies_hyps` refutes the naive form; the genuine reduction lives in the
    localization layer).  Naming it makes the well-pointedness payoff machine-checkable. -/
def ProperMonoIsProductForm (P A : 𝒞) : Prop :=
  ∀ {D : Over P} (m : D ⟶ sliceEmbedObj P A), OverMono m → ¬ OverIso m →
    ∃ (B' : 𝒞) (i : B' ⟶ P) (_ : Mono i) (_ : ¬ IsIso i)
      (e : D ⟶ (⟨prod A B', snd ≫ i⟩ : Over P)),
      OverIso e ∧ e ⊚ prodFormMono (A := A) i = m

/-- **Well-pointedness from the product-form reduction (the R15 escape, applied uniformly).**
    GIVEN the named §1.546 reduction `ProperMonoIsProductForm P A`, the structured embedded object
    `sliceEmbedObj P A` is `WellPointed` in `Over P` whenever some `g : P → A` exists (the witness
    g-point).  Proof: a proper mono `m` is, by `hpf`, `e ≫ prodFormMono i` with `e` a slice iso and
    `i : B' ↪ P` proper; `prodFormMono_misses_slicePoint` gives a g-point missed by `prodFormMono i`;
    any factorization through `m` would, post-composed with `e⁻¹`, factor through `prodFormMono i`,
    contradiction.  This is the sorry-free half — the only open input is `hpf`. -/
theorem wellPointed_of_productForm {P A : 𝒞} (g : P ⟶ A) (hpf : ProperMonoIsProductForm P A) :
    @WellPointed (Over P) _ (overHasTerminal P) (sliceEmbedObj P A) := by
  intro D m hm hniso
  obtain ⟨B', i, hi_mono, hi_proper, e, he_iso, hfac⟩ := hpf m hm hniso
  -- the g-point missed by the product-form mono `prodFormMono i`
  refine ⟨sliceFactorPoint A g, ?_⟩
  rintro ⟨y, hy⟩
  -- `y ≫ m = point`, and `m = e ≫ prodFormMono i`, so `(y ≫ e) ≫ prodFormMono i = point`.
  refine prodFormMono_misses_slicePoint (A := A) i hi_mono hi_proper g ⟨y ≫ e, ?_⟩
  rw [Cat.assoc, show e ≫ prodFormMono (A := A) i = m from hfac]; exact hy

/-- **Well-pointedness of the structured factor object (the §1.547 payoff under the named gap).**
    For `A = U.get k` a well-supported factor of a finite set `U`, the embedded object
    `sliceEmbedObj (∏U) A` is `WellPointed` in `Over (∏U)`, GIVEN the §1.546 reduction
    `ProperMonoIsProductForm`.  This is exactly `sliceEmbed_factor_wellPointed`
    (`RationalCapitalization.lean`) — byte-for-byte the book's `WellPointed` — with its lone `sorry`
    replaced by the honest named hypothesis.  The g-point witness is the projection
    `listProdProj U k : ∏U → U.get k`. -/
theorem sliceEmbed_factor_wellPointed_of_productForm (U : List 𝒞) (k : Fin U.length)
    (hpf : ProperMonoIsProductForm (listProd U) (U.get k)) :
    @WellPointed (Over (listProd U)) _ (overHasTerminal (listProd U))
      (sliceEmbedObj (listProd U) (U.get k)) :=
  wellPointed_of_productForm (listProdProj U k) hpf

/-! ## §1.547 — the FIXED-`U` slice equivalence `A*|U ≃ A/(∏U)`

  Freyd (§1.547, lines 4958-4961): for a finite list `U` of well-supported objects, `A*|U` is the
  full subcategory of the rational category `A*` on objects `(A,F)` with `F° ⊆ U`, and it is
  EQUIVALENT to the slice `A/(∏U) = Over (listProd U)`.  This is the FIXED-base equivalence — NO
  colimit; the directed union `A* = ⋃_U A*|U` comes later.

  ### The design (chosen given this repo's vocabulary)

  The repo has NO bundled `Equivalence` record; its functor-equivalence notion is
  `EquivalenceFunctor F := Embedding F ∧ Full F ∧ HasRepresentativeImage F` (S1_31), i.e. fully
  faithful + essentially surjective.  So we express `A*|U ≃ A/(∏U)` as an `EquivalenceFunctor`.

  Freyd's `F° ⊆ U` subcategory has objects sitting over DIFFERENT bases `∏(F°)`, so the object map
  into the single slice `Over (∏U)` is not literal.  We follow Freyd's own padding: work with the
  full subcategory `PairOnU U` on objects whose targets are EXACTLY `U` (in order), where every
  object sits over the common base `∏U` and `pairSliceObj` is an HONEST object map into `Over(∏U)`.
  The bridge (`pairHomToSlice`/`pairHomOfSlice`, sorry-free in `RationalCapitalization.lean`) makes
  the resulting functor fully faithful; representative-image is the slice→pair construction (every
  `⟨A,h:A→∏U⟩` is `pairSliceObj` of the padded `(A, {h ≫ proj_k})`).  The padding `A*|U ≃ PairOnU U`
  (every `F° ⊆ U` is iso to one with `F'° = U`) is the remaining inclusion; the equivalence
  `PairOnU U ≃ A/(∏U)` is what is built sorry-free below.

  Morphisms of `PairOnU U` are plain `PairHom`s (the subcategory is FULL), so the category structure
  is inherited from `pairsCat`. -/

section FixedU

variable (U : List 𝒞)

/-- **§1.547 — `A*|U` on the nose: the full subcategory of `Â` on objects with `F° = U`.**  An
    object bundles a `PairObj` together with a proof that its target list is exactly `U` (in order),
    so it sits over the common base `∏U`.  Morphisms are inherited from `pairsCat` (the subcategory
    is FULL: a `PairOnU`-map is just a `PairHom` of the underlying objects). -/
structure PairOnU where
  obj : PairObj 𝒞
  htgt : obj.targets = U

/-- Homs of `PairOnU U` are the `PairHom`s of underlying objects (full subcategory). -/
instance : Cat.{u} (PairOnU U) where
  Hom X Y := PairHom X.obj Y.obj
  id X := PairHom.id X.obj
  comp f g := f.comp g
  id_comp f := PairHom.ext (Cat.id_comp f.g)
  comp_id f := PairHom.ext (Cat.comp_id f.g)
  assoc f g h := PairHom.ext (Cat.assoc f.g g.g h.g)

/-- **The object map `A*|U → A/(∏U)`.**  `X = ⟨(A,F), F° = U⟩ ↦ ⟨A, factorMap : A → ∏U⟩`.  This is
    `pairSliceObj` of the underlying object, whose base `∏(F°)` is rewritten to `∏U` along `X.htgt`.
    Concretely `⟨X.obj.A, X.htgt ▸ pairFactorMap X.obj⟩ : Over (listProd U)`. -/
def pairOnUSlice {U : List 𝒞} (X : PairOnU U) : Over (listProd U) :=
  ⟨X.obj.A, pairFactorMap X.obj ≫ eqToHom (congrArg listProd X.htgt)⟩

@[simp] theorem pairOnUSlice_hom {U : List 𝒞} (X : PairOnU U) :
    (pairOnUSlice X).hom = pairFactorMap X.obj ≫ eqToHom (congrArg listProd X.htgt) := rfl

@[simp] theorem pairOnUSlice_dom {U : List 𝒞} (X : PairOnU U) :
    (pairOnUSlice X).dom = X.obj.A := rfl

/-- **The factor map is FIXED by the self base-restriction.**  `pairFactorMap X` post-composed with
    `listProdRestrict X° X°` (the §1.547 base projection of `∏X°` onto itself) is `pairFactorMap X`
    again.  Projection-extensionality: at coordinate `k`, the LHS is `factorTuple X.F ≫ findProj
    (X°.get k) X°` = some factor `f` of target `X°.get k` (`factorTuple_findProj`), the RHS is the
    positional factor `X.F.get k'` of the same target (`factorTuple_proj`); `X.distinct` pins them
    equal.  (This is exactly why `listProdRestrict U U` acts as the identity on factor maps even when
    `U` has repeated targets — the decidable search may pick a different coordinate, but distinctness
    makes all coordinates of a given target carry the same arrow.) -/
theorem pairFactorMap_restrict_self [HasPullbacks 𝒞] (X : PairObj 𝒞)
    (h : ∀ T ∈ X.targets, T ∈ X.targets) :
    pairFactorMap X ≫ listProdRestrict X.targets X.targets h = pairFactorMap X := by
  apply listProd_hom_ext X.targets
  intro k
  rw [Cat.assoc, listProdRestrict_proj X.targets X.targets h k]
  -- RHS coordinate: factor map ≫ proj_k = (X.F.get k').2 (positional)
  have hk' : k.1 < X.F.length := by simpa [PairObj.targets] using k.2
  have htgt : X.targets.get k = (X.F.get ⟨k.1, hk'⟩).1 := by
    simp only [PairObj.targets, List.get_eq_getElem, List.getElem_map]
  rw [show k = ⟨k.1, k.2⟩ from rfl, pairFactorMap_proj X k.1 k.2 hk' htgt]
  -- LHS coordinate: factor map ≫ findProj = (f).2 for some X-factor f of target X°.get k
  obtain ⟨f, hf, hfh, hfe⟩ := factorTuple_findProj (X.targets.get k) X.F
    ⟨X.targets.get k, h _ (List.get_mem _ _), rfl⟩
  rw [(show pairFactorMap X = factorTuple X.F from rfl),
      show findProj (X.targets.get k) X.targets ⟨X.targets.get k, h _ (List.get_mem _ _), rfl⟩
          = findProj (X.targets.get k) (X.F.map (·.1)) _ from rfl, hfe]
  -- both factors target X°.get k; X.distinct pins their arrows equal
  have hqf : f.1 = (X.F.get ⟨k.1, hk'⟩).1 := hfh.trans htgt
  have hqf2 : hqf ▸ f.2 = (X.F.get ⟨k.1, hk'⟩).2 :=
    X.distinct f hf (X.F.get ⟨k.1, hk'⟩) (List.get_mem _ _) hqf
  clear hfe hf h
  revert hfh htgt hqf hqf2
  obtain ⟨fT, fa⟩ := f
  generalize X.F.get ⟨k.1, hk'⟩ = yp
  obtain ⟨yT, ya⟩ := yp
  generalize X.targets.get k = T
  intro htgt hfh hqf hqf2
  simp only at htgt hfh hqf hqf2 ⊢
  subst hfh; subst htgt; exact hqf2

/-- **Self base-restriction as `eqToHom`, under the factor map.**  When the target list `l` equals
    `Xo.targets`, `pairFactorMap Xo ≫ listProdRestrict Xo.targets l h` is `pairFactorMap Xo ≫
    eqToHom`.  `l` is a free variable, so `cases e` reduces this to `pairFactorMap_restrict_self`. -/
theorem pairFactorMap_restrict_eqToHom [HasPullbacks 𝒞] (Xo : PairObj 𝒞) (l : List 𝒞)
    (h : ∀ T ∈ l, T ∈ Xo.targets) (e : Xo.targets = l) :
    pairFactorMap Xo ≫ listProdRestrict Xo.targets l h
      = pairFactorMap Xo ≫ eqToHom (congrArg listProd e) := by
  cases e
  rw [pairFactorMap_restrict_self Xo h, eqToHom_refl, Cat.comp_id]

/-- The morphism map: a `PairOnU`-hom `m` (a `PairHom X.obj → Y.obj`) gives the slice triangle
    `m.g ≫ (pairOnUSlice Y).hom = (pairOnUSlice X).hom`.  After `subst`ing both `htgt` proofs, this
    is `pairHom_commutes_restrict` plus `pairFactorMap_restrict_self` (both targets are `U`, so the
    base restriction is the identity on factor maps). -/
def pairOnUSliceMap [HasPullbacks 𝒞] {U : List 𝒞} {X Y : PairOnU U} (m : PairHom X.obj Y.obj) :
    OverHom (pairOnUSlice X) (pairOnUSlice Y) :=
  ⟨m.g, by
    simp only [pairOnUSlice_hom]
    -- LHS: m.g ≫ pairFactorMap Y.obj ≫ eqToHom Y.htgt.  Re-associate, apply `pairHom_commutes_restrict`,
    -- collapse the base restriction via `restrict_eqToHom`, fuse the two `eqToHom`s.
    rw [show m.g ≫ pairFactorMap Y.obj ≫ eqToHom (congrArg listProd Y.htgt)
          = (m.g ≫ pairFactorMap Y.obj) ≫ eqToHom (congrArg listProd Y.htgt) from (Cat.assoc _ _ _).symm,
       pairHom_commutes_restrict m,
       show pairFactorMap X.obj ≫ listProdRestrict X.obj.targets Y.obj.targets (pairHom_targets_subset m)
            = pairFactorMap X.obj ≫ eqToHom (congrArg listProd (X.htgt.trans Y.htgt.symm)) from
         pairFactorMap_restrict_eqToHom X.obj Y.obj.targets _ (X.htgt.trans Y.htgt.symm),
       Cat.assoc, eqToHom_trans]
    -- both sides now `pairFactorMap X.obj ≫ eqToHom (·)`; the two equalities `X° = U` coincide (proof
    -- irrelevance), so `eqToHom_trans` already closed the goal.
    ⟩

/-- **§1.547 — the functor `Φ : A*|U → A/(∏U)`.**  Objects `↦ pairOnUSlice` (the factor-slice over
    the common base `∏U`); morphisms `↦ pairOnUSliceMap` (the underlying arrow `m.g`, the slice
    triangle from the bridge).  Functoriality is `OverHom.ext` on underlying arrows (`id ↦ id`,
    `m.g₁ ≫ m.g₂ ↦ (m₁ ≫ m₂).g`). -/
instance pairOnUToSlice [HasPullbacks 𝒞] {U : List 𝒞} :
    Functor (fun X : PairOnU U => pairOnUSlice X) where
  map {X Y} (m : PairHom X.obj Y.obj) := pairOnUSliceMap m
  map_id X := OverHom.ext rfl
  map_comp m n := OverHom.ext rfl

@[simp] theorem pairOnUToSlice_map_f [HasPullbacks 𝒞] {U : List 𝒞} {X Y : PairOnU U}
    (m : PairHom X.obj Y.obj) :
    (pairOnUToSlice.map m : OverHom (pairOnUSlice X) (pairOnUSlice Y)).f = m.g := rfl

/-! ### The functor `Φ` is an `EquivalenceFunctor` (fully faithful + essentially surjective)

  `Embedding Φ`: `Φ` is injective on homs (a `PairOnU`-map is its underlying `.g`, recovered as the
  slice map's `.f`).  `Full Φ`: every slice map `φ : pairOnUSlice X → pairOnUSlice Y` is `Φ` of a
  `PairHom` — exactly the bridge fullness `pairHomOfSlice` (the slice triangle over `∏U` re-presents
  the reindexed commuting square the bridge needs).  `HasRepresentativeImage Φ`: every slice object
  `⟨A, h : A → ∏U⟩` is iso to `Φ` of the padded pair `(A, {h ≫ proj_k})` (Freyd's padding). -/

/-- **`Φ : A*|U → A/(∏U)` is an `Embedding`** (injective on homs).  A `PairOnU`-hom is determined by
    its underlying `𝒞`-arrow `m.g`, which is `Φ.map`'s `.f`; equality of `.f` gives equality of `m`
    by `PairHom.ext`. -/
theorem pairOnUToSlice_embedding [HasPullbacks 𝒞] (U : List 𝒞) :
    Embedding (fun X : PairOnU U => pairOnUSlice X) := by
  intro X Y m₁ m₂ h
  exact PairHom.ext (congrArg OverHom.f h)

/-- For `X Y : PairOnU U`, `Y°` is a subset of `X°` (both equal `U`).  The bridge's `hsub`. -/
theorem pairOnU_targets_sub {U : List 𝒞} (X Y : PairOnU U) :
    ∀ T ∈ Y.obj.targets, T ∈ X.obj.targets := by
  intro T hT; rw [X.htgt]; rw [Y.htgt] at hT; exact hT

/-- **The slice triangle over `∏U` re-presents the reindexed bridge square.**  Given a slice map
    `φ : pairOnUSlice X → pairOnUSlice Y` over `∏U` (triangle `φ.f ≫ pairFactorMap Y ≫ eqToHom hY =
    pairFactorMap X ≫ eqToHom hX`), the underlying `φ.f` satisfies the bridge's reindexed commuting
    square `φ.f ≫ pairFactorMap Y.obj = pairFactorMap X.obj ≫ listProdRestrict X° Y° hsub`.  Proof:
    cancel the (iso) `eqToHom hY` on the right, fuse `eqToHom hX ≫ eqToHom hY⁻¹ = eqToHom (X°=Y°)`,
    and apply `pairFactorMap_restrict_eqToHom` to turn that into the base restriction. -/
theorem pairOnUSlice_triangle_to_bridge [HasPullbacks 𝒞] {U : List 𝒞} {X Y : PairOnU U}
    (φ : OverHom (pairOnUSlice X) (pairOnUSlice Y)) :
    φ.f ≫ pairFactorMap Y.obj
      = pairFactorMap X.obj
          ≫ listProdRestrict X.obj.targets Y.obj.targets (pairOnU_targets_sub X Y) := by
  have hw : φ.f ≫ (pairFactorMap Y.obj ≫ eqToHom (congrArg listProd Y.htgt))
      = pairFactorMap X.obj ≫ eqToHom (congrArg listProd X.htgt) := by
    have := φ.w; simpa [pairOnUSlice_hom] using this
  -- right-cancel the iso `eqToHom (congrArg listProd Y.htgt)` from `hw`
  have hiso : φ.f ≫ pairFactorMap Y.obj
      = pairFactorMap X.obj ≫ eqToHom (congrArg listProd (X.htgt.trans Y.htgt.symm)) := by
    have h2 := congrArg (· ≫ eqToHom (congrArg listProd Y.htgt).symm) hw
    -- LHS: cancel `eqToHom hY ≫ eqToHom hY.symm = id`; RHS: fuse the two `eqToHom`s.
    simp only [Cat.assoc] at h2
    rw [eqToHom_comp_eqToHom_symm, Cat.comp_id, eqToHom_trans] at h2
    exact h2
  rw [hiso, ← pairFactorMap_restrict_eqToHom X.obj Y.obj.targets _ (X.htgt.trans Y.htgt.symm)]

/-- **`Φ : A*|U → A/(∏U)` is FULL.**  Every slice map `φ : pairOnUSlice X → pairOnUSlice Y` is `Φ`
    of a `PairHom`.  The bridge fullness `pairHomOfSlice` builds that `PairHom` from the reindexed
    square `pairOnUSlice_triangle_to_bridge`; its underlying `.g` is `φ.f`, so `Φ.map` of it is `φ`
    (`OverHom.ext`). -/
theorem pairOnUToSlice_full [HasPullbacks 𝒞] (U : List 𝒞) :
    Full (fun X : PairOnU U => pairOnUSlice X) := by
  intro X Y φ
  refine ⟨pairHomOfSlice (pairOnU_targets_sub X Y) ⟨φ.f, ?_⟩, OverHom.ext rfl⟩
  show φ.f ≫ (pairSliceObj Y.obj).hom
      = pairFactorMap X.obj ≫ listProdRestrict X.obj.targets Y.obj.targets (pairOnU_targets_sub X Y)
  rw [pairSliceObj_hom]
  exact pairOnUSlice_triangle_to_bridge φ

end FixedU

end Freyd

#print axioms Freyd.bridge_roundtrip_pairHom
#print axioms Freyd.bridge_roundtrip_f
#print axioms Freyd.wellPointed_of_productForm
#print axioms Freyd.sliceEmbed_factor_wellPointed_of_productForm
