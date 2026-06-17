/-
  Freyd & Scedrov, *Categories and Allegories* §1.48 / §1.547
  THE RATIONAL CATEGORY `A[𝒟⁻¹]` AS A CALCULUS-OF-FRACTIONS CATEGORY,
  and the CHOICE-FREE relative capitalization `A ⊆ A*` of §1.547.

  ── WHY THIS FILE EXISTS (milestone R1) ────────────────────────────────────────

  The transfinite §1.546 capitalization (`CapitalizationTransfinite.lean`) and the
  ω-tower §1.544/§1.545 successor (`Capitalization.lean`, `RelativeCapitalization.lean`)
  both model `A*` as a *directed colimit of slice categories* — a `Colim.CatSystem`.
  That framework demands the directed transitions be **strictly** functorial
  (`CatSystem.F_refl : F (refl) X = X` and `F_trans` on the nose, CatColimit.lean:33).
  The §1.547 transition `A/(∏V) → A/(∏U)` for `V ⊆ U` is BASE-CHANGE (the pullback that
  grows the embedding domain `B×∏V ↝ B×∏U`); base-change is only *pseudo*-functorial,
  so `CatSystem.F_refl`/`F_trans` are FALSE for it (machine-checked, documented at
  `RelativeCapitalization.lean` `StrictBaseChange`/ROUTE-1).  Hence the slice-colimit
  model of `A*` hits a strictness wall, NOT sidestepped by §1.547.

  This file takes the OTHER route the book actually uses (§1.48, and which §1.547 cites):
  build the rational category `A[𝒟⁻¹]` **directly** as a calculus-of-fractions category —
  same objects as `A`; a morphism `A → B` is an equivalence class of spans
  `A ←[denom ∈ 𝒟]— • —num→ B`; composition by pullback.  There is NO directed colimit
  and hence NO transition-strictness obligation: the rational category is a *single*
  `Cat` built by quotienting each hom-set.  This is exactly why §1.547 phrases the
  inter-slice transitions as equivalences (up-to-iso) yet still gets a genuine category.

  ── WHAT THIS FILE DELIVERS ────────────────────────────────────────────────────

  The §1.48 scaffolding (`DenseClass`/`Fraction`/`FractionEquiv`/`RationalCategory`)
  already lives in `S1_47.lean` as DEFINITIONS + a universal-property record, but the
  actual category (composition by pullback, well-definedness, the `Cat` instance) was
  never built.  Here:

    * `denseMonos 𝒞`          — SORRY-FREE (`propext` only).  The dense class of ALL
                                monics (closed under iso/comp/pb; §1.48(i)-(iii) from
                                `mono_pullback`).  The working dense class for `A[𝒟⁻¹]`.
    * `FractionEquiv` EQUIVALENCE RELATION — SORRY-FREE over `denseMonos 𝒞`.  Reflexivity,
                                symmetry, AND transitivity all proven; transitivity closes
                                via the pullback-roof whose dense leg is monic because
                                `r₁`,`s₂` are mono left-factors and pullbacks of monics are
                                monic (`mono_of_comp_mono`/`mono_pullback`/`mono_comp'`).
    * `RatHom A B`/`ratId`/`locMap` — SORRY-FREE (`propext`).  `Quotient (fractionSetoid …)`,
                                the hom-set of `A[𝒟⁻¹]`; identity span; localisation of an
                                ordinary arrow.
    * `compFraction`         — SORRY-FREE.  The composite span by pullback of `(num₁,denom₂)`,
                                with its denominator dense by pb+comp closure.
    * `ratComp`              — SORRY-FREE (milestone R2).  Composition on equivalence classes;
                                the `Quotient.lift₂` WELL-DEFINEDNESS (independence of names +
                                pullback choice, §1.48) is discharged by the two single-span
                                congruences `compFraction_congr_left`/`_right` (each a single
                                pullback roof) glued by `fractionEquiv_trans`.  Axioms: `propext`,
                                `Quot.sound`.
    * `compFraction_idFraction_left/right`, `compFraction_assoc` — SORRY-FREE (R2).  Unit and
                                associativity laws of `compFraction` up to `FractionEquiv`.
    * `Rat 𝒞` / `ratCat`     — SORRY-FREE (R2).  The rational category `A[denseMonos⁻¹]` as a
                                genuine `Cat` (objects = a structure wrapper of `𝒞`'s objects so
                                its `Cat` instance does not collapse onto `𝒞`'s; homs = `RatHom`;
                                comp = `ratComp`; the three laws lifted from `compFraction`).
    * `locFunctor`           — SORRY-FREE (R2).  The localisation functor `T_𝒟 : 𝒞 → A[denseMonos⁻¹]`
                                (identity on objects, `f ↦ locMap f`); `map_id` definitional,
                                `map_comp` via `locMap_comp_equiv` (pullback-against-identity roof).
    * FAITHFULNESS FINDING (R2, machine-checked) — at the ALL-MONICS class, `T_𝒟` is NEITHER an
                                `Embedding` (left-cancelling a dense MONIC roof leg would need it
                                EPIC) NOR conservative (it inverts every monic).  So the repo's
                                `Faithful` — hence `CapStep.stepFaithful`, hence a genuine
                                `ratCap S : CapStep S` with `step = T_𝒟` — is GATED on §1.547's
                                dense-class refinement (invert only the slice-embedding monics).
                                No `ratCap` is asserted here: doing so at this class would require
                                faking `stepFaithful`, which the integrity rules forbid.  See the
                                "§1.547 FAITHFULNESS FINDING" block at the localisation section.
    * Cartesian / pre-regular `PreRegularCategory (Rat 𝒞)` — NOT built in R2.  Transporting
                                finite limits + covers through `T_𝒟` is a large separate effort
                                and, per the faithfulness finding, would still not yield `ratCap`
                                without the refined class; left for R3 rather than stubbed.
    * `ratStep_points_every_factor` / `slice_factor_point_acquired` — SORRY-FREE.  The §1.547
                                per-step PAYOFF: the product-slice `A/(∏U)` carries a global
                                point of every factor (re-exposed `listProdSliceAcquiresEvery
                                Factor`).
    * `sliceEmbed_factor_wellPointed` — the §1.547 well-pointedness CORE, stated with the
                                slice's genuine `HasTerminal` (overHasTerminal) — NO sorry in
                                the type, so it is the book's real `WellPointed`.  The descent
                                of an arbitrary subobject to the downstairs proper `B'` and the
                                missed-point extraction is the isolated `sorry`.

  ── MILESTONE R3 (§1.547 pairs category + refined dense class + FAITHFULNESS) ──────

    * `PairObj`/`PairHom`/`pairsCat` — the §1.547 INTERMEDIATE category `Â`: objects `(A,F)` with
                                `F` a finite set of morphisms to well-supported targets; morphisms
                                `g : A₁→A₂` with `F₂° ⊆ F₁°` and the compatibility square.  A
                                genuine `Cat`, SORRY-FREE, NO axioms (homs determined by `g`).
    * `pairForget`/`pairForget_embedding` — the forgetful `Â → A` is a functor and an `Embedding`
                                (faithful by `PairHom.ext`).  SORRY-FREE, NO axioms.
    * `PairDense` — the §1.547 REFINED dense class: `x` is dense iff it + the surviving factors
                                form a PRODUCT DIAGRAM (witnessed by `X.A ≅ Y.A × W`, `W` the
                                well-supported product of surviving targets, `x.g = fst`).
    * `pairDense_cover` — every dense morphism's underlying arrow is a COVER (`fst` onto a
                                well-supported factor; `prod_fst_cover`+`cover_precomp_iso`).
                                SORRY-FREE, NO axioms.  This is the cancellability R2 lacked.
    * `pairDense_of_iso`/`pairDense_of_isIso` (isos dense) and `pairDense_comp` (dense closed
                                under composition, surviving object `W_y × Wₓ`) — the dense-class
                                closure laws.  SORRY-FREE, NO axioms (choice-free).
    * `pairDense_epi` / **`pairLocalisation_faithful_criterion`** — THE DECISIVE R3 RESULT:
                                dense morphisms are EPIC in `Â` (their underlying cover is epic,
                                `cover_epi`), so two parallel `Â`-arrows identified by a common
                                DENSE roof are equal — this IS the FAITHFULNESS of the §1.547
                                localisation `Â → Â[dense⁻¹] = A*`.  SORRY-FREE, NO axioms,
                                choice-free.  R2's all-monics route FAILED exactly here (a monic
                                roof leg is not epic); §1.547's product-projection dense legs are
                                covers, hence epic — faithfulness re-established.

  ── MILESTONE R4 (§1.547 `Â` IS CARTESIAN — terminal + binary products, sorry-free) ──────────────

    * `WideEq`/`wideEqNil`/`wideEqCons`/`wideEq` — the reusable WIDE EQUALIZER of a finite LIST of
                                parallel pairs over `X`: the maximal subobject `w : D ↪ X`
                                equalizing all listed pairs, universal.  Built by iterated binary
                                equalizer (`products_pullbacks_implies_equalizers`).  This is the
                                `D ↪ A₁×A₂` kernel of Freyd's §1.547 product formula.  SORRY-FREE,
                                choice-free (`propext`,`Quot.sound`).
    * `pairHasTerminal` — `Â` HAS A TERMINAL OBJECT `(1,∅)` (terminator of `A`, no factors); the
                                unique arrow is `term`, unique by `term_uniq`.  SORRY-FREE, NO axioms.
    * `crossConstraints`/`pairProdD`/`pairProdW`/`pairProdK`/`pairProdObj` — the §1.547 PRODUCT
                                OBJECT `(A₁,F₁)×(A₂,F₂) = (D,K)`: `D = wideEq` of the cross
                                constraints `(fst≫f, snd≫f')` for matched factors `f∈F₁`,`f'∈F₂`
                                (`f°=f'°`, decided by `DecidableEq 𝒞` = Freyd's "equal targets"),
                                `w : D ↪ A₁×A₂`, `K = {w≫h | h∈H}`.  Projections `pairProjFst/Snd`.
                                SORRY-FREE, choice-free.
    * `pairProd_hom_ext` — UNIQUENESS of the product pairing (unconditional): agreement after both
                                projections + `w` monic + `prod_hom_ext` ⟹ equality.  SORRY-FREE.
    * `pairPair`/`pairPair_fst`/`pairPair_snd`/`pairProd_lift` — EXISTENCE of the pairing (data,
                                choice-free) under the book's target-distinctness `Z.DistinctTargets`.
    * `PairTargetsDistinct` + `pairHasBinaryProducts` — `Â` HAS BINARY PRODUCTS, under the book's
                                STANDING ASSUMPTION (`PairTargetsDistinct 𝒞`: every object of `Â`
                                has factors to DISTINCT targets — Freyd builds this into objects of
                                `Â`; R3's `PairObj` recorded only well-supportedness, so it is made
                                an explicit class here, NOT a weakening).  SORRY-FREE, choice-free.

  THE DISTINCTNESS GATE — RESOLVED (R5).  Freyd's §1.547 objects of `Â` carry factors to DISTINCT
  well-supported targets.  R5 adds distinctness as a FIELD of `PairObj` (`PairObj.distinct`), NOT a
  side class.  Reason: `nextStep : ∀ S, CapStep S` must be unconditional in `S`, and `PairObj S` is
  free to list two factors to one target, so a standing class `PairTargetsDistinct S` is NOT derivable
  for arbitrary `S` — only by recording distinctness on the object itself is the §1.547 product
  pairing total with no hypothesis.  Hence `pairHasBinaryProducts` is now UNCONDITIONAL, and the
  whole pre-regular structure (below) needs no extra typeclass on `S` beyond `S`'s own pre-regularity.

  ── MILESTONE R5 (§1.547 `Â` PRE-REGULAR + refined dense class; pullbacks/equalizers sorry-free) ──

    * `pairHasEqualizers`/`pairHasPullbacks` — `Â` HAS EQUALIZERS and PULLBACKS, UNCONDITIONAL,
                                SORRY-FREE.  The equalizer of `a,b : (A,F)→(B,G)` is `(E, e^*F)` with
                                `e = eqMap a.g b.g` and `e^*F` the factor set pulled back along `e`
                                (`pairForget` CREATES equalizers); pullbacks by §1.432
                                (products+equalizers ⟹ pullbacks).
    * `pairCover_underlying` — SORRY-FREE.  An `Â`-cover has an `A`-cover underlying arrow: any
                                `A`-monic `m` factoring `f.g` LIFTS to an `Â`-monic (`liftObj`/
                                `liftMono`, factor set `m^*F`) factoring `f`, so the `Â`-cover forces
                                `m` iso.  Freyd's "`pairForget` preserves covers", forward half.
    * `pairPullbacksTransferCovers` / `pairPreRegular` — `Â` IS `PreRegularCategory`.  The cover
                                TRANSFER is the one isolated obstruction: its STATEMENT is the genuine
                                §1.52 condition; the forward bridge reduces the underlying square to
                                `A`'s transfer, but promoting back to an `Â`-cover is the direction
                                `pairForget` does NOT reflect monos — exactly Freyd's slice-equivalence
                                verification ("`A*` = directed union of pre-regular slices", §1.547 =
                                the directed-colimit route's strictness wall, R1).  ONE `sorry`, true
                                statement, sharply documented.
    * `pairEmbed`/`pairEmbed_faithful` — SORRY-FREE.  The §1.547 FULL EMBEDDING `A ↪ Â`, `A ↦ (A,∅)`,
                                full + faithful (the `S → Â` half of the capitalization `step`).
    * `pairDenseClass : DenseClass (PairObj 𝒞)` — the refined §1.547 dense class packaged as the
                                record the §1.48 rational category consumes: `mem := Nonempty PairDense`,
                                isos dense + composition-closed sorry-free (R3); `pairDense_pb` (§1.48(iii)
                                pullback-closure: base change of a product projection is a projection onto
                                the same well-supported `W`) the one isolated obstruction, true statement.

  ── MILESTONE R6 (generic monic skeleton + the EPIC-class wall on `ratCap`) ───────────────────────

    * `MonicDense 𝒟` / `denseMonos_monic` / `MonicDense.leg_mono` — the calculus-of-fractions skeleton
                                GENERALISED.  R2 hard-wired `fractionEquiv_trans`/`fractionSetoid`/`ratComp`
                                to `denseMonos`; `fractionEquiv_trans` is now generic over ANY monic dense
                                class `(𝒟, hD : MonicDense 𝒟)` (members ↔ monics), with `denseMonos` the
                                canonical instance re-fed downstream.  Sorry-free (`propext`); `ratCat`
                                keeps its `propext`/`Quot.sound` profile.
    * `pairDense_mono_epic_collapse` — THE R6 OBSTRUCTION, machine-checked AXIOM-FREE.  A `pairDense`
                                morphism is EPIC in `Â` (`pairDense_epi`); a `MonicDense pairDenseClass`
                                would force it MONIC too, collapsing the dense class to the isos.  Hence
                                §1.547's `A* = Â[pairDense⁻¹]` localises at an EPIC class and is NOT
                                modelled by this monic LEFT-fraction skeleton — it requires the DUAL
                                RIGHT-fraction (co-span) calculus.  This is the precise, sorry-free form
                                of the R1/R2 monic/epic wall, pinned to the `MonicDense` hypothesis.

  STILL OPEN (the `ratCap` spill, NOT faked).  `ratCap S : CapStep S` is BLOCKED, not by missing
  bookkeeping but by the monic/epic mismatch above: the R2 monic skeleton (`ratCat`/`locFunctor`) is
  faithful only for monic classes, while §1.547's `A*` inverts EPIC projections (`pairDenseClass`).
  Building `A*` therefore needs the DUAL right-fraction calculus (co-spans, composition by cover-
  factorisation) — a separate skeleton, not the R2 one.  The faithfulness OBLIGATION for the epic class
  is already discharged (`pairLocalisation_faithful_criterion`); the embedding half is
  `pairEmbed_faithful`.  No fake `ratCap` is asserted, and instantiating the monic skeleton on
  `pairDenseClass` is provably impossible (`pairDense_mono_epic_collapse`), so it is NOT attempted.

  ── INTEGRITY ──────────────────────────────────────────────────────────────────

  No `axiom`, no `: True`, no `sorry` on a false statement, no `sorry` in any STATEMENT/type.
  THREE `sorry`s, each on the book's genuine statement, sharply documented: (1) the R2 residual
  `sliceEmbed_factor_wellPointed` (§1.547 subobject-descent); (2) `pairPullbacksTransferCovers` (the
  `Â` cover transfer = slice equivalence); (3) `pairDense_pb` (§1.48(iii) dense pullback-closure).
  The protected types of `capData_exists`/`CapData`/`CapStep` are not touched.  No fake `ratCap`.

  mathlib-free; built on this repo's hand-built `Cat`.
-/

import Fredy.S1_45
import Fredy.S1_47
import Fredy.S1_52
import Fredy.SliceRegular
import Fredy.RelativeCapitalization

namespace Freyd

universe u

open Freyd

variable {𝒞 : Type u} [Cat.{u} 𝒞]

/-! ## §1.48  The dense class of ALL monics

  Freyd's §1.48 dense class needs only (i) all isos, (ii) closure under composition,
  (iii) closure under pullback.  The class of *all* monics satisfies these: isos are
  monic, monics compose, and the pullback of a monic is monic (`mono_pullback`,
  S1_45.lean).  §1.547's "dense monics" are a *sub*-class of this (the dense morphisms
  `x` that, with the surviving factors, form a product diagram); for the rational
  category as a localisation we may take the largest dense class that still inverts what
  we need — and the all-monics class is the cleanest concrete instance, sorry-free. -/

section DenseAllMonos
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- A monic is preserved by composition (both legs monic ⇒ composite monic). -/
theorem mono_comp' {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (hf : Mono f) (hg : Mono g) :
    Mono (f ≫ g) := by
  intro W u v huv
  apply hf; apply hg
  rw [Cat.assoc, Cat.assoc]
  exact huv

/-- An isomorphism is monic (it is a split mono / retraction: `f ≫ inv = id`). -/
theorem mono_of_isIso {A B : 𝒞} {f : A ⟶ B} (hf : IsIso f) : Mono f := by
  obtain ⟨inv, hinv₁, _⟩ := hf
  exact mono_of_retraction f inv hinv₁

/-- **Mono left-factor.**  If `g ≫ f` is monic then `g` is monic.  (`u ≫ g = v ≫ g`
    implies `u ≫ (g ≫ f) = v ≫ (g ≫ f)`, cancel the composite mono.) -/
theorem mono_of_comp_mono {A B C : 𝒞} {g : A ⟶ B} {f : B ⟶ C} (h : Mono (g ≫ f)) : Mono g := by
  intro W u v huv
  apply h
  rw [← Cat.assoc, ← Cat.assoc, huv]

/-- **§1.48 — the class of all monics is a `DenseClass`.**  (i) isos are monic
    (`mono_of_isIso`); (ii) monics compose (`mono_comp'`); (iii) the pullback `π₁` of a
    monic is monic (`mono_pullback`).  This is the working dense class for the rational
    category `A[𝒟⁻¹]` below.  Sorry-free. -/
def denseMonos (𝒞 : Type u) [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] : DenseClass 𝒞 where
  mem {A B} f := Mono f
  iso_mem f hf := mono_of_isIso hf
  comp_mem f g hf hg := mono_comp' f g hf hg
  pb_mem f g hf := mono_pullback g f hf (HasPullbacks.has g f)

end DenseAllMonos

/-! ## §1.48  `FractionEquiv` is an equivalence relation

  Two fraction spans name the same morphism of `A[𝒟⁻¹]` iff they share a common
  dense-monic roof commuting both squares (`FractionEquiv`, S1_47.lean).  We show this
  is reflexive, symmetric, and transitive — so the hom-set is a genuine `Quotient`.
  Reflexivity: the identity roof (`id ∈ 𝒟`).  Symmetry: swap the roof legs.
  Transitivity: the pullback of the two roofs, glued over the shared apex; the composite
  denominator stays in `𝒟` by the dense class's composition + pullback closure. -/

section Equiv
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] (G : DenseClass 𝒞)

/-- Reflexivity of `FractionEquiv`: a fraction is equivalent to itself via the identity
    roof (its own denominator is dense, and both squares commute trivially). -/
theorem fractionEquiv_refl {A B : 𝒞} (f : Fraction G A B) : FractionEquiv f f :=
  ⟨f.apex, Cat.id f.apex, Cat.id f.apex,
    by rw [Cat.id_comp]; exact f.denom_dense,
    by rw [Cat.id_comp],
    by rw [Cat.id_comp]⟩

/-- Symmetry of `FractionEquiv`: swap the two roof legs.  The shared-denominator
    density is symmetric because `r₁ ≫ f₁.denom = r₂ ≫ f₂.denom`. -/
theorem fractionEquiv_symm {A B : 𝒞} {f₁ f₂ : Fraction G A B}
    (h : FractionEquiv f₁ f₂) : FractionEquiv f₂ f₁ := by
  obtain ⟨R, r₁, r₂, hd, hden, hnum⟩ := h
  exact ⟨R, r₂, r₁, hden ▸ hd, hden.symm, hnum.symm⟩

end Equiv

/-! ## §1.48  The rational category's hom-sets and identities

  With `FractionEquiv` reflexive + symmetric (above), the hom-set `A[𝒟⁻¹](A,B)` is the
  quotient of fraction spans.  Transitivity (needed for `Quotient`) is the dense-class
  pullback-roof argument, isolated below as `fractionEquiv_trans` with its precise
  obstruction. -/

/-! ### §1.48  GENERALISING THE SKELETON — the monic dense-class interface `MonicDense`

  R2 hard-wired the calculus-of-fractions (equivalence, composition, well-definedness, units,
  associativity, localisation functor) to `denseMonos 𝒞`.  In fact the §1.48 proofs use only:
  (i) the three `DenseClass` closures (`iso_mem`/`comp_mem`/`pb_mem`); and (ii) `𝒟.mem f ↔ Mono f`,
  to extract `Mono` from a dense roof leg (`mono_of_comp_mono`) and to repackage the rebuilt roof
  denominator as dense.  We isolate (ii) as `MonicDense 𝒟` and parametrise the skeleton over a
  GENERIC monic dense class `𝒟` with `(hD : MonicDense 𝒟)`.  `denseMonos` is the canonical instance
  (`denseMonos_monic`, `mem ↔ Mono` is `Iff.rfl`); the all-monics development of R2 is recovered by
  feeding `denseMonos`/`denseMonos_monic` (`fractionSetoid` etc. below).

  WHY ONLY MONIC CLASSES (and why this skeleton does NOT model §1.547's `A*`).  Transitivity rebuilds
  the roof denominator as `π ≫ r ≫ d` with `π` the pullback projection of a roof leg `r`; the only
  handle on `r` is that `r ≫ d` is dense, and concluding `π ≫ r ≫ d` dense needs: extract `Mono r`
  from `Mono (r ≫ d)`, pull the mono through the pullback, repackage as `mem` — all requiring
  `mem ↔ Mono`.  §1.547's refined dense class (`pairDenseClass`) is EPIC, not monic: its members are
  product projections onto well-supported factors, hence COVERS (`pairDense_cover`) and EPIs
  (`pairDense_epi`).  A cover that is also monic is an iso, so `MonicDense pairDenseClass` is FALSE
  for any class with a non-iso projection (`not_monicDense_pairDenseClass`).  Therefore the §1.547
  localisation `A* = Â[pairDense⁻¹]` is a localisation at an EPIC class and is NOT modelled by this
  monic left-fraction skeleton; it requires the DUAL right-fraction (co-span) calculus.  This is the
  same monic/epic wall R1/R2 documented, now pinned to the exact `MonicDense` hypothesis.  See the
  report at `not_monicDense_pairDenseClass` and the `ratCap` note. -/

/-- A dense class whose members are EXACTLY the monics — the §1.48 "dense monic" hypothesis, the one
    extra fact (beyond the `DenseClass` record) the calculus-of-fractions skeleton needs.  `denseMonos`
    is the canonical instance. -/
structure MonicDense [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] (𝒟 : DenseClass 𝒞) :
    Prop where
  mem_iff_mono : ∀ {A B : 𝒞} (f : A ⟶ B), 𝒟.mem f ↔ Mono f

/-- `denseMonos` is a monic dense class (`mem` is `Mono` definitionally). -/
theorem denseMonos_monic [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] :
    MonicDense (denseMonos 𝒞) := ⟨fun _ => Iff.rfl⟩

/-- A dense roof leg `r` (one with `𝒟.mem (r ≫ d)`) is monic, in a monic dense class. -/
theorem MonicDense.leg_mono [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    {𝒟 : DenseClass 𝒞} (hD : MonicDense 𝒟) {A B C : 𝒞} {r : A ⟶ B} {d : B ⟶ C}
    (h : 𝒟.mem (r ≫ d)) : Mono r :=
  mono_of_comp_mono ((hD.mem_iff_mono _).1 h)

section RatHom
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- **§1.48 — Transitivity of `FractionEquiv` for a MONIC dense class `𝒟`.**  Given roofs
    `R : f₁ ≈ f₂` (legs `r₁,r₂`) and `S : f₂ ≈ f₃` (legs `s₂,s₃`), form the pullback `P` of
    `(r₂, s₂)` over `f₂.apex`.  Its two legs compose with `r₁`/`s₃` to give a roof `f₁ ≈ f₃`; the
    declared-dense leg `(P.π₁ ≫ r₁) ≫ f₁.denom` is monic (`r₁`/`s₂` monic as dense roof legs,
    `P.π₁` the pullback of monic `s₂`, `f₁.denom` monic) and repackaged as dense via `mem_iff_mono`.
    Sorry-free for any `MonicDense 𝒟`; instantiated at `denseMonos`/`denseMonos_monic` below. -/
theorem fractionEquiv_trans {𝒟 : DenseClass 𝒞} (hD : MonicDense 𝒟) {A B : 𝒞}
    {f₁ f₂ f₃ : Fraction 𝒟 A B}
    (h₁₂ : FractionEquiv f₁ f₂) (h₂₃ : FractionEquiv f₂ f₃) : FractionEquiv f₁ f₃ := by
  obtain ⟨R, r₁, r₂, hRd, hRden, hRnum⟩ := h₁₂
  obtain ⟨S, s₂, s₃, hSd, hSden, hSnum⟩ := h₂₃
  -- pullback of the two middle legs `r₂ : R → f₂.apex` and `s₂ : S → f₂.apex`
  let P := (HasPullbacks.has r₂ s₂).cone
  refine ⟨P.pt, P.π₁ ≫ r₁, P.π₂ ≫ s₃, ?_, ?_, ?_⟩
  · -- composite denominator `(P.π₁ ≫ r₁) ≫ f₁.denom` dense, via monicity.
    have hr₁ : Mono r₁ := hD.leg_mono hRd
    have hs₂ : Mono s₂ := hD.leg_mono hSd
    have hP₁ : Mono P.π₁ := mono_pullback r₂ s₂ hs₂ (HasPullbacks.has r₂ s₂)
    have hd₁ : Mono f₁.denom := (hD.mem_iff_mono _).1 f₁.denom_dense
    exact (hD.mem_iff_mono _).2 (mono_comp' _ _ (mono_comp' _ _ hP₁ hr₁) hd₁)
  · -- denominators agree: `(P.π₁ ≫ r₁) ≫ f₁.denom = (P.π₂ ≫ s₃) ≫ f₃.denom`.
    -- Chase: `P.π₁ ≫ r₁ ≫ f₁.denom = P.π₁ ≫ r₂ ≫ f₂.denom` (hRden)
    --        `= P.π₂ ≫ s₂ ≫ f₂.denom` (pullback square `P.cone.w` ▸)
    --        `= P.π₂ ≫ s₃ ≫ f₃.denom` (hSden).
    have hw : P.π₁ ≫ r₂ = P.π₂ ≫ s₂ := P.w
    calc (P.π₁ ≫ r₁) ≫ f₁.denom
        = P.π₁ ≫ (r₁ ≫ f₁.denom) := by rw [Cat.assoc]
      _ = P.π₁ ≫ (r₂ ≫ f₂.denom) := by rw [hRden]
      _ = (P.π₁ ≫ r₂) ≫ f₂.denom := by rw [Cat.assoc]
      _ = (P.π₂ ≫ s₂) ≫ f₂.denom := by rw [hw]
      _ = P.π₂ ≫ (s₂ ≫ f₂.denom) := by rw [Cat.assoc]
      _ = P.π₂ ≫ (s₃ ≫ f₃.denom) := by rw [hSden]
      _ = (P.π₂ ≫ s₃) ≫ f₃.denom := by rw [Cat.assoc]
  · -- numerators agree: same chase via the numerator squares `hRnum`/`hSnum`.
    have hw : P.π₁ ≫ r₂ = P.π₂ ≫ s₂ := P.w
    calc (P.π₁ ≫ r₁) ≫ f₁.num
        = P.π₁ ≫ (r₁ ≫ f₁.num) := by rw [Cat.assoc]
      _ = P.π₁ ≫ (r₂ ≫ f₂.num) := by rw [hRnum]
      _ = (P.π₁ ≫ r₂) ≫ f₂.num := by rw [Cat.assoc]
      _ = (P.π₂ ≫ s₂) ≫ f₂.num := by rw [hw]
      _ = P.π₂ ≫ (s₂ ≫ f₂.num) := by rw [Cat.assoc]
      _ = P.π₂ ≫ (s₃ ≫ f₃.num) := by rw [hSnum]
      _ = (P.π₂ ≫ s₃) ≫ f₃.num := by rw [Cat.assoc]

/-- The setoid on fraction spans `A → B`: `FractionEquiv` with its three laws. -/
def fractionSetoid {A B : 𝒞} : Setoid (Fraction (denseMonos 𝒞) A B) where
  r := FractionEquiv
  iseqv := ⟨fractionEquiv_refl (denseMonos 𝒞), fractionEquiv_symm (denseMonos 𝒞),
    fractionEquiv_trans denseMonos_monic⟩

/-- **§1.48 — the hom-set `A[𝒟⁻¹](A,B)`**: equivalence classes of fraction spans
    (for the all-monics dense class `denseMonos 𝒞`).  Sorry-free `Quotient`. -/
def RatHom (A B : 𝒞) : Type u := Quotient (fractionSetoid (𝒞 := 𝒞) (A := A) (B := B))

/-- The IDENTITY span `A → A`: `A ←[id]— A —id→ A` (denominator the identity, dense). -/
def idFraction (G : DenseClass 𝒞) (A : 𝒞) : Fraction G A A :=
  ⟨A, Cat.id A, Cat.id A, G.iso_mem (Cat.id A) ⟨Cat.id A, Cat.id_comp _, Cat.id_comp _⟩⟩

/-- The identity morphism of `A[𝒟⁻¹]` at `A`. -/
def ratId (A : 𝒞) : RatHom (𝒞 := 𝒞) A A :=
  Quotient.mk _ (idFraction (denseMonos 𝒞) A)

/-- The localisation on objects is the identity-on-objects map. -/
def loc (A : 𝒞) : 𝒞 := A

/-- The localisation of an ordinary arrow `f : A → B` is the span `A ←[id]— A —f→ B`. -/
def locFraction (G : DenseClass 𝒞) {A B : 𝒞} (f : A ⟶ B) : Fraction G A B :=
  ⟨A, Cat.id A, f, G.iso_mem (Cat.id A) ⟨Cat.id A, Cat.id_comp _, Cat.id_comp _⟩⟩

/-- The localisation functor on arrows: `f ↦ [A ←id— A —f→ B]`. -/
def locMap {A B : 𝒞} (f : A ⟶ B) : RatHom (𝒞 := 𝒞) A B :=
  Quotient.mk _ (locFraction (denseMonos 𝒞) f)

end RatHom

/-! ## §1.48  Composition by pullback

  The composite of spans `A ←[d₁]— P₁ —n₁→ B` and `B ←[d₂]— P₂ —n₂→ C` is formed by
  pulling back `n₁` against `d₂` over `B`: with `Q` the pullback of `(n₁, d₂)`,

        A ←[d₁]— P₁ ←[π₁]— Q —[π₂]— P₂ —n₂→ C
                                  composite denom = π₁ ≫ d₁  (dense: pb of d₂ then comp d₁)
                                  composite num   = π₂ ≫ n₂

  The composite denominator is dense because `π₁` is the pullback of the dense `d₂`
  (closure (iii)) and `d₁` is dense (closure (ii)).  Well-definedness on equivalence
  classes (independence of representative names and of the pullback choice) is §1.48's
  "the named morphism is independent of the choice of names and pullback" — the genuine
  calculus-of-fractions content, isolated below. -/

section Comp
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] (G : DenseClass 𝒞)

/-- The composite span of two fraction spans, by pullback of `(num₁, denom₂)`. -/
def compFraction {A B C : 𝒞} (f : Fraction G A B) (g : Fraction G B C) : Fraction G A C :=
  let Q := (HasPullbacks.has f.num g.denom).cone
  { apex := Q.pt
    denom := Q.π₁ ≫ f.denom
    num := Q.π₂ ≫ g.num
    denom_dense :=
      -- `Q.π₁` is the pullback of `g.denom` along `f.num`; dense by (iii), then `f.denom`
      -- dense gives the composite dense by (ii).
      G.comp_mem Q.π₁ f.denom
        (G.pb_mem g.denom f.num g.denom_dense) f.denom_dense }

/-! ### §1.48 well-definedness of composition

  `ratComp` needs `compFraction` to respect `FractionEquiv` in BOTH arguments.  We split
  the binary congruence into two single-variable congruences and glue with transitivity:

    `compFraction f g ≈ compFraction f' g`   (LEFT — replace the first span)
    `compFraction f' g ≈ compFraction f' g'`  (RIGHT — replace the second span)

  Each is a SINGLE pullback roof.  Write `Q := pb(f.num, g.denom)` for `compFraction f g`'s
  apex; the roof witnessing `f ≈ f'` (resp. `g ≈ g'`) is pulled back against the relevant
  projection of `Q`, and the comparison leg into `Q' := pb(f'.num, g.denom)` (resp.
  `pb(f.num, g'.denom)`) is produced by `Q'`'s universal property.  Density of the declared
  roof-denominator is `Mono`-closure: the roof leg is a pullback of the mono left-factor
  (`mono_of_comp_mono` on the roof's dense denominator), and `compFraction`'s own denom is
  already mono (`compFraction.denom_dense`). -/

/-- **RIGHT congruence**: replacing the second span by an equivalent one yields an equivalent
    composite.  Roof = pullback of `compFraction f g`'s `Q.π₂` against the `g ≈ g'` roof leg
    `s : S → g.apex`; the leg into `Q' := pb(f.num, g'.denom)` is built by `Q'`'s lift. -/
theorem compFraction_congr_right {A B C : 𝒞} (f : Fraction (denseMonos 𝒞) A B)
    {g g' : Fraction (denseMonos 𝒞) B C} (hg : FractionEquiv g g') :
    FractionEquiv (compFraction (denseMonos 𝒞) f g) (compFraction (denseMonos 𝒞) f g') := by
  obtain ⟨S, s, s', hSd, hSden, hSnum⟩ := hg
  let Q := (HasPullbacks.has f.num g.denom).cone
  let Q' := (HasPullbacks.has f.num g'.denom).cone
  -- `R := pb(Q.π₂, s)` over `g.apex`
  let R := (HasPullbacks.has Q.π₂ s).cone
  -- comparison cone into `Q'`
  have sq : (R.π₁ ≫ Q.π₁) ≫ f.num = (R.π₂ ≫ s') ≫ g'.denom := by
    calc (R.π₁ ≫ Q.π₁) ≫ f.num
        = R.π₁ ≫ (Q.π₁ ≫ f.num) := by rw [Cat.assoc]
      _ = R.π₁ ≫ (Q.π₂ ≫ g.denom) := by rw [Q.w]
      _ = (R.π₁ ≫ Q.π₂) ≫ g.denom := by rw [Cat.assoc]
      _ = (R.π₂ ≫ s) ≫ g.denom := by rw [R.w]
      _ = R.π₂ ≫ (s ≫ g.denom) := by rw [Cat.assoc]
      _ = R.π₂ ≫ (s' ≫ g'.denom) := by rw [hSden]
      _ = (R.π₂ ≫ s') ≫ g'.denom := by rw [Cat.assoc]
  let ρ' := (HasPullbacks.has f.num g'.denom).lift ⟨R.pt, R.π₁ ≫ Q.π₁, R.π₂ ≫ s', sq⟩
  have hρ'1 : ρ' ≫ Q'.π₁ = R.π₁ ≫ Q.π₁ := (HasPullbacks.has f.num g'.denom).lift_fst _
  have hρ'2 : ρ' ≫ Q'.π₂ = R.π₂ ≫ s' := (HasPullbacks.has f.num g'.denom).lift_snd _
  refine ⟨R.pt, R.π₁, ρ', ?_, ?_, ?_⟩
  · -- dense: `R.π₁ ≫ (Q.π₁ ≫ f.denom)` mono.  `s` mono ⇒ `R.π₁ = pb(s)` mono; comp mono.
    have hs : Mono s := mono_of_comp_mono hSd
    have hR₁ : Mono R.π₁ := mono_pullback Q.π₂ s hs (HasPullbacks.has Q.π₂ s)
    show Mono (R.π₁ ≫ (Q.π₁ ≫ f.denom))
    exact mono_comp' _ _ hR₁ (compFraction (denseMonos 𝒞) f g).denom_dense
  · -- denoms agree
    show R.π₁ ≫ (Q.π₁ ≫ f.denom) = ρ' ≫ (Q'.π₁ ≫ f.denom)
    calc R.π₁ ≫ (Q.π₁ ≫ f.denom)
        = (R.π₁ ≫ Q.π₁) ≫ f.denom := by rw [Cat.assoc]
      _ = (ρ' ≫ Q'.π₁) ≫ f.denom := by rw [hρ'1]
      _ = ρ' ≫ (Q'.π₁ ≫ f.denom) := by rw [Cat.assoc]
  · -- nums agree
    show R.π₁ ≫ (Q.π₂ ≫ g.num) = ρ' ≫ (Q'.π₂ ≫ g'.num)
    calc R.π₁ ≫ (Q.π₂ ≫ g.num)
        = (R.π₁ ≫ Q.π₂) ≫ g.num := by rw [Cat.assoc]
      _ = (R.π₂ ≫ s) ≫ g.num := by rw [R.w]
      _ = R.π₂ ≫ (s ≫ g.num) := by rw [Cat.assoc]
      _ = R.π₂ ≫ (s' ≫ g'.num) := by rw [hSnum]
      _ = (R.π₂ ≫ s') ≫ g'.num := by rw [Cat.assoc]
      _ = (ρ' ≫ Q'.π₂) ≫ g'.num := by rw [hρ'2]
      _ = ρ' ≫ (Q'.π₂ ≫ g'.num) := by rw [Cat.assoc]

/-- **LEFT congruence**: replacing the first span by an equivalent one yields an equivalent
    composite.  Roof = pullback of `compFraction f g`'s `Q.π₁` against the `f ≈ f'` roof leg
    `t : T → f.apex`; the leg into `Q' := pb(f'.num, g.denom)` is built by `Q'`'s lift. -/
theorem compFraction_congr_left {A B C : 𝒞} {f f' : Fraction (denseMonos 𝒞) A B}
    (g : Fraction (denseMonos 𝒞) B C) (hf : FractionEquiv f f') :
    FractionEquiv (compFraction (denseMonos 𝒞) f g) (compFraction (denseMonos 𝒞) f' g) := by
  obtain ⟨T, t, t', hTd, hTden, hTnum⟩ := hf
  let Q := (HasPullbacks.has f.num g.denom).cone
  let Q' := (HasPullbacks.has f'.num g.denom).cone
  -- `R := pb(Q.π₁, t)` over `f.apex`
  let R := (HasPullbacks.has Q.π₁ t).cone
  -- comparison cone into `Q'`
  have sq : (R.π₂ ≫ t') ≫ f'.num = (R.π₁ ≫ Q.π₂) ≫ g.denom := by
    calc (R.π₂ ≫ t') ≫ f'.num
        = R.π₂ ≫ (t' ≫ f'.num) := by rw [Cat.assoc]
      _ = R.π₂ ≫ (t ≫ f.num) := by rw [hTnum]
      _ = (R.π₂ ≫ t) ≫ f.num := by rw [Cat.assoc]
      _ = (R.π₁ ≫ Q.π₁) ≫ f.num := by rw [R.w]
      _ = R.π₁ ≫ (Q.π₁ ≫ f.num) := by rw [Cat.assoc]
      _ = R.π₁ ≫ (Q.π₂ ≫ g.denom) := by rw [Q.w]
      _ = (R.π₁ ≫ Q.π₂) ≫ g.denom := by rw [Cat.assoc]
  let ρ' := (HasPullbacks.has f'.num g.denom).lift ⟨R.pt, R.π₂ ≫ t', R.π₁ ≫ Q.π₂, sq⟩
  have hρ'1 : ρ' ≫ Q'.π₁ = R.π₂ ≫ t' := (HasPullbacks.has f'.num g.denom).lift_fst _
  have hρ'2 : ρ' ≫ Q'.π₂ = R.π₁ ≫ Q.π₂ := (HasPullbacks.has f'.num g.denom).lift_snd _
  refine ⟨R.pt, R.π₁, ρ', ?_, ?_, ?_⟩
  · -- dense: `R.π₁ ≫ (Q.π₁ ≫ f.denom)` mono.  `t` mono ⇒ `R.π₁ = pb(t)` mono; comp mono.
    have ht : Mono t := mono_of_comp_mono hTd
    have hR₁ : Mono R.π₁ := mono_pullback Q.π₁ t ht (HasPullbacks.has Q.π₁ t)
    show Mono (R.π₁ ≫ (Q.π₁ ≫ f.denom))
    exact mono_comp' _ _ hR₁ (compFraction (denseMonos 𝒞) f g).denom_dense
  · -- denoms agree
    show R.π₁ ≫ (Q.π₁ ≫ f.denom) = ρ' ≫ (Q'.π₁ ≫ f'.denom)
    calc R.π₁ ≫ (Q.π₁ ≫ f.denom)
        = (R.π₁ ≫ Q.π₁) ≫ f.denom := by rw [Cat.assoc]
      _ = (R.π₂ ≫ t) ≫ f.denom := by rw [R.w]
      _ = R.π₂ ≫ (t ≫ f.denom) := by rw [Cat.assoc]
      _ = R.π₂ ≫ (t' ≫ f'.denom) := by rw [hTden]
      _ = (R.π₂ ≫ t') ≫ f'.denom := by rw [Cat.assoc]
      _ = (ρ' ≫ Q'.π₁) ≫ f'.denom := by rw [hρ'1]
      _ = ρ' ≫ (Q'.π₁ ≫ f'.denom) := by rw [Cat.assoc]
  · -- nums agree
    show R.π₁ ≫ (Q.π₂ ≫ g.num) = ρ' ≫ (Q'.π₂ ≫ g.num)
    calc R.π₁ ≫ (Q.π₂ ≫ g.num)
        = (R.π₁ ≫ Q.π₂) ≫ g.num := by rw [Cat.assoc]
      _ = (ρ' ≫ Q'.π₂) ≫ g.num := by rw [hρ'2]
      _ = ρ' ≫ (Q'.π₂ ≫ g.num) := by rw [Cat.assoc]

/-- **§1.48 — composition in `A[𝒟⁻¹]` is well-defined** (on equivalence classes).
    The binary congruence is the composite of the LEFT and RIGHT single-span congruences
    (`compFraction_congr_left`/`_right`) via transitivity — Freyd's "the named morphism is
    independent of the choice of names for `A → B` and `B → C`, and of the choice of
    pullback" (§1.48).  Sorry-free over `denseMonos 𝒞`. -/
def ratComp {A B C : 𝒞} (m : RatHom (𝒞 := 𝒞) A B)
    (n : RatHom (𝒞 := 𝒞) B C) : RatHom (𝒞 := 𝒞) A C :=
  Quotient.lift₂ (fun f g => Quotient.mk _ (compFraction (denseMonos 𝒞) f g))
    (by
      intro f g f' g' hf hg
      apply Quotient.sound
      exact fractionEquiv_trans denseMonos_monic
        (compFraction_congr_left g hf) (compFraction_congr_right f' hg))
    m n

/-! ### §1.48  Identity and associativity laws — the `Cat` instance

  `RatHom` with `ratComp`/`ratId` is a category.  The unit laws are one-line roofs
  (composing with the identity span `A ←id— A —id→ A` just re-bases along the iso
  pullback-of-identity).  Associativity is the standard pasting of the two composite
  pullbacks. -/

/-- LEFT UNIT: `[idFraction A] ∘ f ≈ f`.  Composite apex `Q = pb(id_A, f.denom)`; the roof
    `(id, Q.π₂)` to `f` works because `Q.π₁ = Q.π₂ ≫ f.denom` (the square with `id_A`). -/
theorem compFraction_idFraction_left {A B : 𝒞} (f : Fraction (denseMonos 𝒞) A B) :
    FractionEquiv (compFraction (denseMonos 𝒞) (idFraction (denseMonos 𝒞) A) f) f := by
  let Q := (HasPullbacks.has (idFraction (denseMonos 𝒞) A).num f.denom).cone
  -- `idFraction A`.num = id_A, .denom = id_A, .apex = A; square: `Q.π₁ ≫ id_A = Q.π₂ ≫ f.denom`
  have hw : Q.π₁ = Q.π₂ ≫ f.denom := by
    have := Q.w; simp only [idFraction, Cat.comp_id] at this; exact this
  refine ⟨Q.pt, Cat.id Q.pt, Q.π₂, ?_, ?_, ?_⟩
  · -- dense: `id ≫ (Q.π₁ ≫ id_A) = Q.π₁` mono — pullback of mono `f.denom` along `id_A`
    have hm : Mono Q.π₁ :=
      mono_pullback (idFraction (denseMonos 𝒞) A).num f.denom f.denom_dense
        (HasPullbacks.has (idFraction (denseMonos 𝒞) A).num f.denom)
    have he : Cat.id Q.pt ≫ (compFraction (denseMonos 𝒞) (idFraction (denseMonos 𝒞) A) f).denom
        = Q.π₁ := by
      show Cat.id Q.pt ≫ (Q.π₁ ≫ Cat.id A) = Q.π₁
      rw [Cat.id_comp]; exact Cat.comp_id Q.π₁
    rw [he]; exact (hm : (denseMonos 𝒞).mem Q.π₁)
  · show Cat.id Q.pt ≫ (Q.π₁ ≫ (idFraction (denseMonos 𝒞) A).denom) = Q.π₂ ≫ f.denom
    simp only [idFraction, Cat.comp_id, Cat.id_comp]; exact hw
  · show Cat.id Q.pt ≫ (Q.π₂ ≫ f.num) = Q.π₂ ≫ f.num
    rw [Cat.id_comp]

/-- RIGHT UNIT: `f ∘ [idFraction B] ≈ f`.  Composite apex `Q = pb(f.num, id_B)`; roof
    `(id, Q.π₁)` to `f` works because `Q.π₂ = Q.π₁ ≫ f.num` (the square with `id_B`). -/
theorem compFraction_idFraction_right {A B : 𝒞} (f : Fraction (denseMonos 𝒞) A B) :
    FractionEquiv (compFraction (denseMonos 𝒞) f (idFraction (denseMonos 𝒞) B)) f := by
  let Q := (HasPullbacks.has f.num (idFraction (denseMonos 𝒞) B).denom).cone
  have hw : Q.π₁ ≫ f.num = Q.π₂ := by
    have := Q.w; simp only [idFraction, Cat.comp_id] at this; exact this
  refine ⟨Q.pt, Cat.id Q.pt, Q.π₁, ?_, ?_, ?_⟩
  · show Mono (Cat.id Q.pt ≫ (Q.π₁ ≫ f.denom))
    rw [Cat.id_comp]; exact (compFraction (denseMonos 𝒞) f (idFraction (denseMonos 𝒞) B)).denom_dense
  · show Cat.id Q.pt ≫ (Q.π₁ ≫ f.denom) = Q.π₁ ≫ f.denom
    rw [Cat.id_comp]
  · show Cat.id Q.pt ≫ (Q.π₂ ≫ (idFraction (denseMonos 𝒞) B).num) = Q.π₁ ≫ f.num
    simp only [idFraction, Cat.comp_id, Cat.id_comp]; exact hw.symm

/-- **ASSOCIATIVITY** of `compFraction` up to `FractionEquiv`: `(f∘g)∘h ≈ f∘(g∘h)`.
    Both composites are limits of the same length-3 cospan chain
    `f.apex →f.num B ←g.denom g.apex →g.num C ←h.denom h.apex`.  We take the LEFT composite's
    apex `Q₂.pt` as the roof, `r₁ := id`, and build the comparison `r₂ : Q₂.pt → P₂.pt`
    (`P₂.pt` = the RIGHT composite's apex) by the universal property of the inner pullback
    `P₁ := pb(g.num, h.denom)` then the outer `P₂ := pb(f.num, P₁.π₁ ≫ g.denom)`. -/
theorem compFraction_assoc {A B C D : 𝒞} (f : Fraction (denseMonos 𝒞) A B)
    (g : Fraction (denseMonos 𝒞) B C) (h : Fraction (denseMonos 𝒞) C D) :
    FractionEquiv
      (compFraction (denseMonos 𝒞) (compFraction (denseMonos 𝒞) f g) h)
      (compFraction (denseMonos 𝒞) f (compFraction (denseMonos 𝒞) g h)) := by
  -- LEFT composite: `Q₁ = pb(f.num, g.denom)`, `Q₂ = pb(Q₁.π₂ ≫ g.num, h.denom)`
  let Q₁ := (HasPullbacks.has f.num g.denom).cone
  let Q₂ := (HasPullbacks.has (Q₁.π₂ ≫ g.num) h.denom).cone
  -- RIGHT composite: `P₁ = pb(g.num, h.denom)`, `P₂ = pb(f.num, P₁.π₁ ≫ g.denom)`
  let P₁ := (HasPullbacks.has g.num h.denom).cone
  let P₂ := (HasPullbacks.has f.num (P₁.π₁ ≫ g.denom)).cone
  -- inner comparison `w₁ : Q₂.pt → P₁.pt`
  have sq₁ : (Q₂.π₁ ≫ Q₁.π₂) ≫ g.num = Q₂.π₂ ≫ h.denom := by
    rw [Cat.assoc]; exact Q₂.w
  let w₁ := (HasPullbacks.has g.num h.denom).lift ⟨Q₂.pt, Q₂.π₁ ≫ Q₁.π₂, Q₂.π₂, sq₁⟩
  have hw₁1 : w₁ ≫ P₁.π₁ = Q₂.π₁ ≫ Q₁.π₂ := (HasPullbacks.has g.num h.denom).lift_fst _
  have hw₁2 : w₁ ≫ P₁.π₂ = Q₂.π₂ := (HasPullbacks.has g.num h.denom).lift_snd _
  -- outer comparison `r₂ : Q₂.pt → P₂.pt`
  have sq₂ : (Q₂.π₁ ≫ Q₁.π₁) ≫ f.num = w₁ ≫ (P₁.π₁ ≫ g.denom) := by
    calc (Q₂.π₁ ≫ Q₁.π₁) ≫ f.num
        = Q₂.π₁ ≫ (Q₁.π₁ ≫ f.num) := by rw [Cat.assoc]
      _ = Q₂.π₁ ≫ (Q₁.π₂ ≫ g.denom) := by rw [Q₁.w]
      _ = (Q₂.π₁ ≫ Q₁.π₂) ≫ g.denom := by rw [Cat.assoc]
      _ = (w₁ ≫ P₁.π₁) ≫ g.denom := by rw [hw₁1]
      _ = w₁ ≫ (P₁.π₁ ≫ g.denom) := by rw [Cat.assoc]
  let r₂ := (HasPullbacks.has f.num (P₁.π₁ ≫ g.denom)).lift ⟨Q₂.pt, Q₂.π₁ ≫ Q₁.π₁, w₁, sq₂⟩
  have hr₂1 : r₂ ≫ P₂.π₁ = Q₂.π₁ ≫ Q₁.π₁ := (HasPullbacks.has f.num (P₁.π₁ ≫ g.denom)).lift_fst _
  have hr₂2 : r₂ ≫ P₂.π₂ = w₁ := (HasPullbacks.has f.num (P₁.π₁ ≫ g.denom)).lift_snd _
  refine ⟨Q₂.pt, Cat.id Q₂.pt, r₂, ?_, ?_, ?_⟩
  · -- dense: `id ≫ (LEFT).denom` mono = `(LEFT).denom_dense`
    show Mono (Cat.id Q₂.pt ≫ (compFraction (denseMonos 𝒞) (compFraction (denseMonos 𝒞) f g) h).denom)
    rw [Cat.id_comp]
    exact (compFraction (denseMonos 𝒞) (compFraction (denseMonos 𝒞) f g) h).denom_dense
  · -- denoms agree
    show Cat.id Q₂.pt ≫ (Q₂.π₁ ≫ (Q₁.π₁ ≫ f.denom)) = r₂ ≫ (P₂.π₁ ≫ f.denom)
    rw [Cat.id_comp]
    calc Q₂.π₁ ≫ (Q₁.π₁ ≫ f.denom)
        = (Q₂.π₁ ≫ Q₁.π₁) ≫ f.denom := by rw [Cat.assoc]
      _ = (r₂ ≫ P₂.π₁) ≫ f.denom := by rw [hr₂1]
      _ = r₂ ≫ (P₂.π₁ ≫ f.denom) := by rw [Cat.assoc]
  · -- nums agree
    show Cat.id Q₂.pt ≫ (Q₂.π₂ ≫ h.num) = r₂ ≫ (P₂.π₂ ≫ (P₁.π₂ ≫ h.num))
    rw [Cat.id_comp]
    calc Q₂.π₂ ≫ h.num
        = (w₁ ≫ P₁.π₂) ≫ h.num := by rw [hw₁2]
      _ = w₁ ≫ (P₁.π₂ ≫ h.num) := by rw [Cat.assoc]
      _ = (r₂ ≫ P₂.π₂) ≫ (P₁.π₂ ≫ h.num) := by rw [hr₂2]
      _ = r₂ ≫ (P₂.π₂ ≫ (P₁.π₂ ≫ h.num)) := by rw [Cat.assoc]

end Comp

/-! ### §1.48  The `Cat` instance on the rational category

  `RatHom` with `ratComp`/`ratId` is a category.  Each law is `Quotient.ind` reduction to the
  corresponding `compFraction` law (`compFraction_idFraction_left/right`, `compFraction_assoc`),
  then `Quotient.sound`.  Objects are the objects of `𝒞` (carried as `Rat 𝒞 := 𝒞`). -/

section CatInstance
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- The carrier of the rational category `A[denseMonos⁻¹]`: a one-field STRUCTURE wrapper of
    `𝒞`'s objects.  A genuine new type (not a `def` alias) so that `Cat (Rat 𝒞)` instance
    resolution does NOT collapse onto `𝒞`'s own `Cat` instance (a bare `def` alias whnf-reduces
    to `𝒞`, so `⟶` between `Rat 𝒞` objects would silently pick `𝒞`'s hom). -/
structure Rat (𝒞 : Type u) [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    where mk :: (obj : 𝒞)

/-- LEFT UNIT on `RatHom`: `ratId ∘ m = m`. -/
theorem ratComp_id_left {A B : 𝒞} (m : RatHom (𝒞 := 𝒞) A B) : ratComp (ratId A) m = m := by
  refine Quotient.inductionOn m (fun f => ?_)
  exact Quotient.sound (compFraction_idFraction_left f)

/-- RIGHT UNIT on `RatHom`: `m ∘ ratId = m`. -/
theorem ratComp_id_right {A B : 𝒞} (m : RatHom (𝒞 := 𝒞) A B) : ratComp m (ratId B) = m := by
  refine Quotient.inductionOn m (fun f => ?_)
  exact Quotient.sound (compFraction_idFraction_right f)

/-- ASSOCIATIVITY on `RatHom`. -/
theorem ratComp_assoc {A B C D : 𝒞} (m : RatHom (𝒞 := 𝒞) A B) (n : RatHom (𝒞 := 𝒞) B C)
    (p : RatHom (𝒞 := 𝒞) C D) : ratComp (ratComp m n) p = ratComp m (ratComp n p) := by
  refine Quotient.inductionOn₃ m n p (fun f g h => ?_)
  exact Quotient.sound (compFraction_assoc f g h)

/-- **§1.48 — the rational category `A[denseMonos⁻¹]` is a category.**  Objects = objects of
    `𝒞`; homs = `RatHom` (fraction quotients); composition = `ratComp`; identity = `ratId`.
    The three laws are the lifted `compFraction` unit/associativity laws.  Sorry-free. -/
instance ratCat : Cat.{u} (Rat 𝒞) where
  Hom A B := RatHom (𝒞 := 𝒞) A.obj B.obj
  id := fun A => ratId A.obj
  comp := fun m n => ratComp m n
  id_comp := fun m => ratComp_id_left m
  comp_id := fun m => ratComp_id_right m
  assoc := fun m n p => ratComp_assoc m n p

end CatInstance

/-! ### §1.48  The localisation functor `T_𝒟 : 𝒞 → A[denseMonos⁻¹]` and its faithfulness

  `T_𝒟` is identity-on-objects (`Rat 𝒞 := 𝒞`) and sends `f` to `locMap f = [A ←id— A —f→ B]`.
  It is a functor (`map_id` by `rfl`; `map_comp` by the pullback-against-identity roof
  `locMap_comp_equiv`) and — crucially for §1.547 — **FAITHFUL for the all-monics dense class**,
  with NO §1.547 pairs-refinement needed: if `locMap f = locMap g` then a common mono roof `r`
  with `r ≫ id = r' ≫ id` forces `r = r'` (it is mono, being in `denseMonos`), and `r ≫ f =
  r ≫ g` then cancels `r` to give `f = g`. -/

section Localisation
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- `T_𝒟 (f ≫ g) ≈ T_𝒟 f ∘ T_𝒟 g` at the fraction level: pullback of `f` against `id`
    re-bases to the identity-denominator span of `f ≫ g`. -/
theorem locMap_comp_equiv {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) :
    FractionEquiv
      (compFraction (denseMonos 𝒞) (locFraction (denseMonos 𝒞) f) (locFraction (denseMonos 𝒞) g))
      (locFraction (denseMonos 𝒞) (f ≫ g)) := by
  let Q := (HasPullbacks.has (locFraction (denseMonos 𝒞) f).num (locFraction (denseMonos 𝒞) g).denom).cone
  -- square: `Q.π₁ ≫ f = Q.π₂ ≫ id_B = Q.π₂`
  have hw : Q.π₁ ≫ f = Q.π₂ := by
    have := Q.w; simp only [locFraction, Cat.comp_id] at this; exact this
  refine ⟨Q.pt, Cat.id Q.pt, Q.π₁, ?_, ?_, ?_⟩
  · show Mono (Cat.id Q.pt ≫
      (compFraction (denseMonos 𝒞) (locFraction (denseMonos 𝒞) f) (locFraction (denseMonos 𝒞) g)).denom)
    rw [Cat.id_comp]
    exact (compFraction (denseMonos 𝒞) (locFraction (denseMonos 𝒞) f)
      (locFraction (denseMonos 𝒞) g)).denom_dense
  · show Cat.id Q.pt ≫ (Q.π₁ ≫ (locFraction (denseMonos 𝒞) f).denom)
        = Q.π₁ ≫ (locFraction (denseMonos 𝒞) (f ≫ g)).denom
    simp only [locFraction, Cat.comp_id, Cat.id_comp]
  · show Cat.id Q.pt ≫ (Q.π₂ ≫ (locFraction (denseMonos 𝒞) g).num)
        = Q.π₁ ≫ (locFraction (denseMonos 𝒞) (f ≫ g)).num
    simp only [locFraction, Cat.id_comp]
    rw [← Cat.assoc, hw]

/-- **§1.48 — `T_𝒟` is a functor** `𝒞 → A[denseMonos⁻¹]` (identity on objects, `f ↦ locMap f`).
    `map_id` is definitional (`idFraction = locFraction id`); `map_comp` is `locMap_comp_equiv`. -/
def locFunctor : Functor (fun A : 𝒞 => Rat.mk (𝒞 := 𝒞) A) where
  map {A B} f := locMap f
  map_id A := by
    show locMap (Cat.id A) = ratId A
    rfl
  map_comp {A B C} f g := by
    show locMap (f ≫ g) = ratComp (locMap f) (locMap g)
    exact Quotient.sound (fractionEquiv_symm (denseMonos 𝒞) (locMap_comp_equiv f g))

/-! ### §1.547 FAITHFULNESS FINDING (machine-checked obstruction; nothing faked)

  The repo's `Faithful F := Embedding F ∧ (∀ f, IsIso (map f) → IsIso f)` — i.e. injective on
  hom-sets AND conservative.  For the localisation `T_𝒟` at the **all-monics** dense class
  `denseMonos`, BOTH conjuncts FAIL, and the failures are structural, not a missing proof:

  • **`Embedding` (hom-injectivity) FAILS.**  `locMap f = locMap g` produces a roof `r₁,r₂ : R → A`
    with `r₁ = r₂` (the `id`-denominators agree), `r₁` MONIC (its dense denom `r₁ ≫ id = r₁` is in
    `denseMonos`), and `r₁ ≫ f = r₁ ≫ g` (the numerators agree).  To conclude `f = g` one must
    cancel `r₁` on the LEFT — that needs `r₁` EPIC, but `denseMonos` only gives `r₁` MONIC.  A monic
    that is not epic does not cancel, so `T_𝒟` need not separate `f` from `g`.

  • **conservativity FAILS.**  `T_𝒟` inverts every dense monic by construction; a non-iso monic `m`
    has `IsIso (locMap m)` while `m` is not iso.

  CONSEQUENCE for `ratCap S : CapStep S`: the `CapStep.stepFaithful` field (this repo's `Faithful`)
  is NOT dischargeable for `step = T_𝒟` at the all-monics class.  §1.547's REFINEMENT of the dense
  class — invert only the *specific* dense monics forced by the product-slice embeddings (the
  "pairs" refinement), each of which is there an ISO of the localised category whose backward leg
  is genuinely cancellable — is REQUIRED before `stepFaithful` holds.  The all-monics route built
  here delivers the rational *category* + localisation *functor* (sorry-free), but the conservative
  *faithful* step, hence the full `CapStep`, is gated on that refined dense class. -/

end Localisation

/-! ## §1.547  THE PAIRS CATEGORY `Â` AND ITS REFINED DENSE CLASS (milestone R3)

  R2 found that localising at ALL monics is not faithful: a common dense roof leg `r` is
  only MONIC, and cancelling it on the LEFT (to separate `f` from `g`) needs `r` EPIC.
  §1.547 fixes this by working in an INTERMEDIATE category `Â` whose dense morphisms are
  *product projections onto well-supported factors* — and the projection `C×W → C` onto a
  well-supported `W` is a COVER (`prod_fst_cover`), hence EPIC (`cover_epi`).  So the refined
  dense roof legs ARE left-cancellable, and the localisation `Â → Â[dense⁻¹]` is FAITHFUL.

  ── Objects of `Â` (§1.547) ────────────────────────────────────────────────────
  A pair `(A, F)`, `F` a finite set of morphisms from `A` to DISTINCT, WELL-SUPPORTED
  targets.  We carry `F` as a `List (Σ T : 𝒞, A ⟶ T)` together with the well-supportedness
  of every target.  `F°` (`PairObj.targets`) is the list of targets.

  ── Morphisms of `Â` (§1.547) ──────────────────────────────────────────────────
  `(A₁,F₁) → (A₂,F₂)` is a `𝒞`-morphism `g : A₁ → A₂` with `F₂° ⊆ F₁°` and the compatibility
  square: for every factor `f : A₂ → B` in `F₂`, the corresponding factor `f' : A₁ → B` in
  `F₁` (same target `B`) satisfies `g ≫ f = f'`.  We package this as: for every `⟨B,f⟩ ∈ F₂`
  there is `⟨B,f'⟩ ∈ F₁` with `g ≫ f = f'`.  The hom is DETERMINED by `g` (`PairHom.ext`),
  so the forgetful functor `Â → A`, `g ↦ g`, is faithful by construction. -/

section PairsCategory
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- **§1.547 object of `Â`** — a pair `(A, F)`: a base object `A`, a finite list `F` of
    morphisms out of `A` to DISTINCT well-supported targets.  `targets` is `F°`.

    The `distinct` field is Freyd's §1.547 standing requirement that the factors go to DISTINCT
    targets (two factors with the same target are equal).  It is recorded as a FIELD of the object
    (not a separate standing class) so that the §1.547 product pairing (`pairHasBinaryProducts`) is
    UNCONDITIONAL — this is what lets `ratCap S : CapStep S` be stated for an arbitrary pre-regular
    `S` with NO extra hypothesis on `S`.  See `pairHasBinaryProducts`/the DISTINCTNESS-GATE note. -/
structure PairObj (𝒞 : Type u) [Cat.{u} 𝒞] [HasTerminal 𝒞] where
  A : 𝒞
  F : List (Σ T : 𝒞, A ⟶ T)
  wsupp : ∀ p ∈ F, WellSupported p.1
  distinct : ∀ r ∈ F, ∀ r' ∈ F, ∀ h : r.1 = r'.1, h ▸ r.2 = r'.2

/-- `F°` — the list of TARGETS of the factors of an object of `Â`. -/
def PairObj.targets (X : PairObj 𝒞) : List 𝒞 := X.F.map (·.1)

/-- **§1.547 morphism of `Â`** — `(A₁,F₁) → (A₂,F₂)`: a `𝒞`-arrow `g : A₁ → A₂` such that
    every factor of `F₂` pulls back through `g` to a factor of `F₁` to the SAME target
    (`F₂° ⊆ F₁°` with the compatibility square `g ≫ f = f'`). -/
structure PairHom (X Y : PairObj 𝒞) where
  g : X.A ⟶ Y.A
  compat : ∀ p ∈ Y.F, ∃ q ∈ X.F, ∃ h : q.1 = p.1, g ≫ p.2 = h ▸ q.2

/-- A `PairHom` is DETERMINED by its underlying `𝒞`-arrow `g` (the compatibility is a `Prop`).
    This is what makes the forgetful functor `Â → A` faithful. -/
@[ext]
theorem PairHom.ext {X Y : PairObj 𝒞} {a b : PairHom X Y} (h : a.g = b.g) : a = b := by
  obtain ⟨ag, _⟩ := a; obtain ⟨bg, _⟩ := b; cases h; rfl

/-- Identity `PairHom`: underlying `id`, compatibility is `id ≫ f = f`. -/
def PairHom.id (X : PairObj 𝒞) : PairHom X X :=
  ⟨Cat.id X.A, fun p hp => ⟨p, hp, rfl, Cat.id_comp p.2⟩⟩

/-- Composition of `PairHom`s (diagram order): underlying `g₁ ≫ g₂`; compatibility chains
    the two factorisations through the shared middle factor.  For `p ∈ Z.F`, `b` gives
    `q ∈ Y.F` with `g₂ ≫ p = q` (same target), and `a` gives `r ∈ X.F` with `g₁ ≫ q = r`;
    then `(g₁ ≫ g₂) ≫ p = g₁ ≫ q = r`. -/
def PairHom.comp {X Y Z : PairObj 𝒞} (a : PairHom X Y) (b : PairHom Y Z) : PairHom X Z where
  g := a.g ≫ b.g
  compat p hp := by
    obtain ⟨q, hq, hqt, hqe⟩ := b.compat p hp
    obtain ⟨r, hr, hrt, hre⟩ := a.compat q hq
    refine ⟨r, hr, hrt.trans hqt, ?_⟩
    -- (a.g ≫ b.g) ≫ p.2 = a.g ≫ (b.g ≫ p.2) = a.g ≫ (hqt ▸ q.2) = (hrt.trans hqt) ▸ r.2
    cases p; cases q; cases r
    cases hqt; cases hrt
    simp only at hqe hre ⊢
    rw [Cat.assoc, hqe, hre]

/-- **§1.547 — `Â` is a category.**  Objects `PairObj`; homs `PairHom` (determined by the
    underlying `𝒞`-arrow); composition/identity inherited from `𝒞`.  All laws follow from
    `PairHom.ext` + the corresponding `Cat` laws of `𝒞` on the underlying arrows. -/
instance pairsCat : Cat.{u} (PairObj 𝒞) where
  Hom := PairHom
  id := PairHom.id
  comp a b := a.comp b
  id_comp a := PairHom.ext (Cat.id_comp a.g)
  comp_id a := PairHom.ext (Cat.comp_id a.g)
  assoc a b c := PairHom.ext (Cat.assoc a.g b.g c.g)

/-- The FORGETFUL functor `Â → A`, `(A,F) ↦ A`, `g ↦ g`.  Underlying-arrow extraction. -/
instance pairForget : Functor (fun X : PairObj 𝒞 => X.A) where
  map {X Y} a := a.g
  map_id _ := rfl
  map_comp a b := rfl

/-- **§1.547 full embedding `A ↪ Â`**, on objects: `A ↦ (A, ∅)` (no recorded factors). -/
def pairEmbedObj (A : 𝒞) : PairObj 𝒞 where
  A := A
  F := []
  wsupp := by intro p hp; exact absurd hp List.not_mem_nil
  distinct := by intro r hr; exact absurd hr List.not_mem_nil

/-- **§1.547 full embedding `A ↪ Â`**, on arrows: `g ↦ ⟨g, vacuous⟩` (the target `(B,∅)` has no
    factors, so compatibility is vacuous).  A genuine functor (`map_id`/`map_comp` by `PairHom.ext`).
    "A full embedding of `A` into `Â` is obtained by sending `A` to `(A,∅)`" (§1.547). -/
instance pairEmbed : Functor (fun A : 𝒞 => pairEmbedObj A) where
  map {A B} g := ⟨g, fun p hp => absurd hp List.not_mem_nil⟩
  map_id _ := PairHom.ext rfl
  map_comp f g := PairHom.ext rfl

/-- The §1.547 embedding `A ↪ Â` is an `Embedding` (faithful on homs): a `PairHom` is determined by
    its underlying `.g`, which is exactly the input arrow (`PairHom.ext`). -/
theorem pairEmbed_embedding : Embedding (fun A : 𝒞 => pairEmbedObj A) :=
  fun f g h => congrArg PairHom.g h

/-- The §1.547 embedding `A ↪ Â` is FULL: every `Â`-arrow `(A,∅) → (B,∅)` is `pairEmbed.map` of its
    underlying `.g` (no compatibility constraints between empty factor sets). -/
theorem pairEmbed_full : Full (fun A : 𝒞 => pairEmbedObj A) :=
  fun {A B} (a : PairHom (pairEmbedObj A) (pairEmbedObj B)) => ⟨a.g, PairHom.ext rfl⟩

/-- The §1.547 embedding `A ↪ Â` is FAITHFUL (full embedding ⟹ faithful, §1.33). -/
theorem pairEmbed_faithful : Faithful (fun A : 𝒞 => pairEmbedObj A) :=
  full_embedding_faithful _ pairEmbed_embedding pairEmbed_full

/-- The forgetful functor `Â → A` is an `Embedding` (faithful on homs): a `PairHom` is
    determined by its `.g` (`PairHom.ext`). -/
theorem pairForget_embedding : Embedding (fun X : PairObj 𝒞 => X.A) :=
  fun a b h => PairHom.ext h

/-! ### §1.547  The refined DENSE class on `Â`

  Book: `x : (A₁,F₁) → (A₂,F₂)` is DENSE in `Â` when `x` together with the SURVIVING factors
  `S = {f ∈ F₁ | f° ∉ F₂°}` forms a PRODUCT DIAGRAM in `A` (§1.425) — i.e. `A₁` is the product
  of `A₂` with the targets `S°` of the surviving factors, `x.g` being the projection onto `A₂`.

  We record this by the universal product-witness: a WELL-SUPPORTED object `W` (the product
  `∏ S°` of the surviving targets, well-supported because each `f° ∈ S°` is well-supported as a
  target in `F₁`) and an ISO `e : A₁ ≅ A₂ × W` carrying `x.g` to `fst : A₂ × W → A₂`.  This is
  the §1.425 product diagram for `A₁ = A₂ × ∏S°` written through the binary product `A₂ × W`.

  Crucial consequence (`pairDense_cover`): the underlying `x.g` is `e.hom ≫ fst` with `W`
  well-supported, hence `fst` a COVER (`prod_fst_cover`) and `x.g` a cover (`cover_precomp_iso`).
  Covers are EPIC (`cover_epi`) — this is exactly the left-cancellability the all-monics route
  lacked, and the engine of the faithfulness payoff below. -/

/-- **§1.547 DENSE morphism of `Â`.**  `x : X → Y` is dense iff `x` with the surviving factors
    forms a product diagram: a well-supported `W` and an iso `e : X.A ≅ Y.A × W` carrying `x.g`
    to `fst`.  (`W = ∏(surviving targets)`; the survivors are `e ≫ snd ≫ projections`.) -/
structure PairDense {X Y : PairObj 𝒞} (x : PairHom X Y) where
  W       : 𝒞
  wsupp   : WellSupported W
  e       : X.A ⟶ prod Y.A W
  einv    : prod Y.A W ⟶ X.A
  e_iso₁  : e ≫ einv = Cat.id X.A
  e_iso₂  : einv ≫ e = Cat.id (prod Y.A W)
  proj    : e ≫ (fst : prod Y.A W ⟶ Y.A) = x.g

/-- **§1.547 — every dense morphism's underlying arrow is a COVER.**  `x.g = e ≫ fst` with
    `e` an iso and `fst : Y.A × W → Y.A` a cover (`W` well-supported, `prod_fst_cover`); a cover
    pre-composed with an iso is a cover (`cover_precomp_iso`).  This is the left-cancellable
    "product projection" property §1.547 uses. -/
theorem pairDense_cover [PullbacksTransferCovers 𝒞] {X Y : PairObj 𝒞} {x : PairHom X Y}
    (d : PairDense x) : Cover x.g := by
  rw [← d.proj]
  exact cover_precomp_iso ⟨d.einv, d.e_iso₁, d.e_iso₂⟩ (prod_fst_cover d.wsupp)

/-- **§1.547 — every dense morphism is EPIC in `Â`.**  This is the decisive cancellability the
    all-monics route (R2) lacked.  For `Â`-arrows `a, b : Y → Z`, if `x.comp a = x.comp b` then
    their underlying arrows satisfy `x.g ≫ a.g = x.g ≫ b.g`; `x.g` is a COVER (`pairDense_cover`)
    hence EPIC (`cover_epi`), giving `a.g = b.g`, hence `a = b` by `PairHom.ext`. -/
theorem pairDense_epi [PullbacksTransferCovers 𝒞] {X Y : PairObj 𝒞} {x : PairHom X Y}
    (d : PairDense x) {Z : PairObj 𝒞} (a b : PairHom Y Z) (hab : x.comp a = x.comp b) :
    a = b := by
  apply PairHom.ext
  apply cover_epi (pairDense_cover d)
  have : (x.comp a).g = (x.comp b).g := congrArg PairHom.g hab
  simpa [PairHom.comp] using this

/-! ### §1.547  Dense-class closure laws on `Â`

  We now verify the three §1.48/§1.547 dense-class axioms for `PairDense` (insofar as they do
  not require the full `HasPullbacks (PairObj 𝒞)` — pullbacks IN `Â` are an R4 construction).
  ISO ⟹ DENSE and DENSE closed under COMPOSITION are proven here sorry-free; the pullback
  closure is stated with the precise obstruction (it needs `Â`'s own pullbacks). -/

/-- The identity is a COVER (any monic `m` it factors through is split-epic + monic = iso). -/
theorem cover_id (X : 𝒞) : Cover (Cat.id X) := by
  intro C m g hm hgm
  -- `g ≫ m = id` ⟹ `m` split epi; with `m` mono, `m` is iso: inverse `g`.
  refine ⟨g, ?_, hgm⟩
  -- `m ≫ g = id`: cancel mono `m` on right of `(m ≫ g) ≫ m = m ≫ (g ≫ m) = m ≫ id = id ≫ m`.
  apply hm
  rw [Cat.assoc, hgm, Cat.comp_id, Cat.id_comp]

/-- `1` (the terminator) is well-supported. -/
theorem wellSupported_one' : WellSupported (HasTerminal.one : 𝒞) := by
  show Cover (term (HasTerminal.one : 𝒞))
  rw [show term (HasTerminal.one : 𝒞) = Cat.id _ from term_uniq _ _]
  exact cover_id _

/-- Composite of covers is a cover (mathlib-free, only `HasPullbacks`; inlined from
    `cover_comp'`, Capitalization.lean — that file is not imported here). -/
theorem cover_comp'' {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Cover f) (hg : Cover g) :
    Cover (f ≫ g) := by
  intro C m h hm hfac
  let pb := HasPullbacks.has g m
  have hπmono : Mono pb.cone.π₁ := by
    intro W p q hpq
    have hpq2 : p ≫ pb.cone.π₂ = q ≫ pb.cone.π₂ := by
      apply hm
      calc (p ≫ pb.cone.π₂) ≫ m = p ≫ (pb.cone.π₁ ≫ g) := by rw [Cat.assoc, ← pb.cone.w]
        _ = (q ≫ pb.cone.π₁) ≫ g := by rw [← Cat.assoc, hpq]
        _ = (q ≫ pb.cone.π₂) ≫ m := by rw [Cat.assoc, pb.cone.w, ← Cat.assoc]
    let cn : Cone g m := ⟨W, p ≫ pb.cone.π₁, p ≫ pb.cone.π₂, by rw [Cat.assoc, Cat.assoc, pb.cone.w]⟩
    rw [pb.lift_uniq cn p rfl rfl, pb.lift_uniq cn q hpq.symm hpq2.symm]
  let u := pb.lift ⟨X, f, h, by rw [hfac]⟩
  have hu₁ : u ≫ pb.cone.π₁ = f := pb.lift_fst _
  obtain ⟨inv, _, hinvπ⟩ : IsIso pb.cone.π₁ := hf pb.cone.π₁ u hπmono hu₁
  refine hg m (inv ≫ pb.cone.π₂) hm ?_
  rw [Cat.assoc, ← pb.cone.w, ← Cat.assoc, hinvπ, Cat.id_comp]

/-- Product extensionality: two maps into a product agree iff they agree after both projections. -/
theorem prod_hom_ext {X A B : 𝒞} {u v : X ⟶ prod A B}
    (h₁ : u ≫ fst = v ≫ fst) (h₂ : u ≫ snd = v ≫ snd) : u = v := by
  rw [pair_eta u, pair_eta v, h₁, h₂]

/-- A binary product of well-supported objects is well-supported. -/
theorem wellSupported_prod' [PullbacksTransferCovers 𝒞] {B D : 𝒞}
    (hB : WellSupported B) (hD : WellSupported D) : WellSupported (prod B D) := by
  show Cover (term (prod B D))
  rw [show term (prod B D) = (fst : prod B D ⟶ B) ≫ term B from term_uniq _ _]
  exact cover_comp'' (prod_fst_cover hD) hB

/-- **§1.547 — every iso of `Â` is dense** (witness form).  Take surviving factor `W = 1`
    (terminal, well-supported `wellSupported_one'`); the iso `X.A ≅ Y.A × 1` is `pair x.g (term)`,
    with inverse `fst ≫ x⁻¹.g`, carrying `x.g` to `fst`.  Choice-free: the inverse arrow `x'` is
    passed explicitly (read off the `IsIso` witness in `pairDense_of_isIso`). -/
def pairDense_of_iso {X Y : PairObj 𝒞} {x : PairHom X Y}
    (x' : PairHom Y X) (hxx' : x.g ≫ x'.g = Cat.id X.A) (hx'x : x'.g ≫ x.g = Cat.id Y.A) :
    PairDense x :=
  { W := HasTerminal.one
    wsupp := wellSupported_one'
    e := pair x.g (term X.A)
    einv := fst ≫ x'.g
    e_iso₁ := by
      -- `pair x.g (term) ≫ (fst ≫ x'.g) = x.g ≫ x'.g = id`
      rw [← Cat.assoc, fst_pair]; exact hxx'
    e_iso₂ := by
      -- `(fst ≫ x'.g) ≫ pair x.g (term) = id` on `Y.A × 1`: agree on both projections
      apply prod_hom_ext
      · -- ≫ fst : `(fst ≫ x'.g) ≫ x.g = fst ≫ id = fst`
        rw [Cat.assoc, fst_pair, Cat.assoc, hx'x, Cat.comp_id, Cat.id_comp]
      · -- ≫ snd : both sides into `1`, unique
        apply HasTerminal.uniq
    proj := fst_pair _ _ }

/-- **§1.547 — every iso of `Â` is dense** (the `DenseClass.iso_mem` obligation), choice-free by
    destructing the `IsIso` witness into its explicit inverse arrow. -/
theorem pairDense_of_isIso {X Y : PairObj 𝒞} {x : PairHom X Y}
    (hx : @IsIso (PairObj 𝒞) _ X Y x) : Nonempty (PairDense x) := by
  obtain ⟨x', hxx', hx'x⟩ := hx
  exact ⟨pairDense_of_iso x' (congrArg PairHom.g hxx') (congrArg PairHom.g hx'x)⟩

/-- **§1.547 — dense morphisms are closed under COMPOSITION.**  `x : X→Y`, `y : Y→Z` dense with
    surviving objects `Wₓ`, `W_y`; `x.comp y` is dense with surviving object `W_y × Wₓ`
    (well-supported, `wellSupported_prod'`), the iso `X.A ≅ Z.A × (W_y × Wₓ)` being `dx.e`
    followed by the reassociator `r : (Z.A × W_y) × Wₓ ≅ Z.A × (W_y × Wₓ)` (built from `dy.e`
    on the left factor), carrying `x.g ≫ y.g` to `fst`. -/
def pairDense_comp [PullbacksTransferCovers 𝒞] {X Y Z : PairObj 𝒞}
    {x : PairHom X Y} {y : PairHom Y Z} (dx : PairDense x) (dy : PairDense y) :
    PairDense (x.comp y) :=
  -- `r` replaces `Y.A` by `Z.A × W_y` (via `dy.e`) inside `Y.A × Wₓ`, then reassociates to
  -- `Z.A × (W_y × Wₓ)`; `r'` is its inverse (using `dy.einv`).
  let r  : prod Y.A dx.W ⟶ prod Z.A (prod dy.W dx.W) :=
    pair (fst ≫ dy.e ≫ fst) (pair (fst ≫ dy.e ≫ snd) snd)
  let r' : prod Z.A (prod dy.W dx.W) ⟶ prod Y.A dx.W :=
    pair (pair fst (snd ≫ fst) ≫ dy.einv) (snd ≫ snd)
  have hrfst : r ≫ (fst : prod Z.A (prod dy.W dx.W) ⟶ Z.A) = fst ≫ dy.e ≫ fst := fst_pair _ _
  have hrsnd : r ≫ (snd : prod Z.A (prod dy.W dx.W) ⟶ prod dy.W dx.W)
      = pair (fst ≫ dy.e ≫ snd) snd := snd_pair _ _
  have hr'fst : r' ≫ (fst : prod Y.A dx.W ⟶ Y.A) = pair fst (snd ≫ fst) ≫ dy.einv := fst_pair _ _
  have hr'snd : r' ≫ (snd : prod Y.A dx.W ⟶ dx.W) = snd ≫ snd := snd_pair _ _
  -- key: `r ≫ pair fst (snd≫fst) = fst ≫ dy.e` (recover `(Z.A, W_y)` from the reassociated form)
  have hkey : r ≫ pair (fst : prod Z.A (prod dy.W dx.W) ⟶ Z.A) (snd ≫ fst) = fst ≫ dy.e := by
    apply prod_hom_ext
    · rw [Cat.assoc, fst_pair, hrfst, Cat.assoc]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, hrsnd, fst_pair, Cat.assoc]
  have hrr' : r ≫ r' = Cat.id (prod Y.A dx.W) := by
    apply prod_hom_ext
    · -- (r ≫ r') ≫ fst = fst
      rw [Cat.assoc, hr'fst, ← Cat.assoc, hkey, Cat.assoc, dy.e_iso₁, Cat.comp_id, Cat.id_comp]
    · -- (r ≫ r') ≫ snd = snd
      rw [Cat.assoc, hr'snd, ← Cat.assoc, hrsnd, snd_pair, Cat.id_comp]
  have hr'r : r' ≫ r = Cat.id (prod Z.A (prod dy.W dx.W)) := by
    apply prod_hom_ext
    · -- fst : (r'≫r)≫fst = r'≫(fst≫dy.e≫fst) = (pair…≫dy.einv)≫(dy.e≫fst) = pair…≫(dy.einv≫dy.e)≫fst
      rw [Cat.assoc, hrfst, ← Cat.assoc, hr'fst, Cat.assoc, ← Cat.assoc dy.einv dy.e fst,
        dy.e_iso₂, Cat.id_comp, fst_pair, Cat.id_comp]
    · -- snd: split further on the (W_y × Wₓ) product
      rw [Cat.assoc, hrsnd, Cat.id_comp]
      apply prod_hom_ext
      · -- ≫ fst
        rw [Cat.assoc, fst_pair, ← Cat.assoc, hr'fst, Cat.assoc, ← Cat.assoc dy.einv dy.e snd,
          dy.e_iso₂, Cat.id_comp, snd_pair]
      · -- ≫ snd
        rw [Cat.assoc, snd_pair, hr'snd]
  { W := prod dy.W dx.W
    wsupp := wellSupported_prod' dy.wsupp dx.wsupp
    e := dx.e ≫ r
    einv := r' ≫ dx.einv
    e_iso₁ := by
      rw [Cat.assoc, ← Cat.assoc r r', hrr', Cat.id_comp, dx.e_iso₁]
    e_iso₂ := by
      rw [Cat.assoc, ← Cat.assoc dx.einv dx.e, dx.e_iso₂, Cat.id_comp, hr'r]
    proj := by
      show (dx.e ≫ r) ≫ (fst : prod Z.A (prod dy.W dx.W) ⟶ Z.A) = x.g ≫ y.g
      rw [Cat.assoc, fst_pair, ← Cat.assoc, dx.proj, ← dy.proj, ← Cat.assoc] }

/-! ### §1.547  FAITHFULNESS of the localisation `Â → Â[dense⁻¹] = A*` (the decisive payoff)

  In a calculus-of-fractions localisation `Â → Â[dense⁻¹]`, the localisation functor is FAITHFUL
  exactly when the dense class is LEFT-CANCELLABLE: two parallel `Â`-arrows `u, v : X → Y` that
  become equal in `A*` are identified there by a common DENSE roof `r : R → X` (so `r ≫ u = r ≫ v`
  in `Â`), and faithfulness is the implication `r ≫ u = r ≫ v → u = v`, i.e. `r` EPIC.  R2's
  all-monics class FAILED here (a monic roof leg is not epic).  §1.547's refined dense class
  succeeds: dense roof legs are product projections onto WELL-SUPPORTED factors, hence COVERS
  (`pairDense_cover`), hence EPIC (`pairDense_epi`).  This `pairLocalisation_faithful_criterion`
  IS that implication — the decisive R3 result, sorry-free.  (The full localised category `A*`
  and the functor object are the R4 instantiation of the R2 generic skeleton on `(Â, PairDense)`;
  this theorem is the faithfulness obligation of that functor, discharged here in advance.) -/

/-- **§1.547 — FAITHFULNESS CRITERION for `Â → A*` (decisive payoff).**  Two parallel `Â`-arrows
    identified by a common DENSE roof are already equal.  This is the faithfulness of the §1.547
    localisation `Â → Â[dense⁻¹]`: the refined dense roof legs are product projections onto
    well-supported factors, hence covers (`pairDense_cover`), hence epic (`pairDense_epi`) — the
    exact left-cancellation the all-monics route (R2) lacked.  Sorry-free, choice-free. -/
theorem pairLocalisation_faithful_criterion [PullbacksTransferCovers 𝒞] {R X Y : PairObj 𝒞}
    {r : PairHom R X} (d : PairDense r) (u v : PairHom X Y)
    (hruv : r.comp u = r.comp v) : u = v :=
  pairDense_epi d u v hruv

/-! ### §1.547  WIDE EQUALIZER OF A FINITE LIST OF PARALLEL PAIRS (the `D ↪ A₁×A₂` kernel)

  The §1.547 product `(A₁,F₁)×(A₂,F₂) = (D,K)` takes `D ↪ A₁×A₂` to be the maximal subobject
  equalizing all morphisms in `H` with equal targets.  We realise this as the WIDE EQUALIZER of a
  finite LIST `L` of parallel pairs `(u,v : X ⟶ B)` over `X = A₁×A₂`: a mono `w : D ↪ X` with
  `w≫u = w≫v` for every listed pair, universal (any `k` equalizing all pairs factors uniquely
  through `w`).  Built by iterated binary equalizer (`products_pullbacks_implies_equalizers`).
  Avoiding `DecidableEq 𝒞`: instead of "morphisms with EQUAL targets" we list, for the product, the
  pairs `(fst≫f, snd≫f')` for matching factors — see `pairProd` below; the wide equalizer is the
  reusable kernel. -/

/-- Equalizer maps are monic (inlined; `S1_57.eqMap_mono` is in a later, un-imported file).
    `a ≫ e = b ≫ e` with `e = eqMap u v`: both factor `a≫e` through the equalizer; the lift is
    unique, so `a = lift = b`. -/
theorem eqMap_mono' [HasEqualizers 𝒞] {X B : 𝒞} (u v : X ⟶ B) : Mono (eqMap u v) := by
  intro W a b hab
  have ha : a ≫ eqMap u v ≫ u = a ≫ eqMap u v ≫ v := by rw [eqMap_eq]
  have hb : (a ≫ eqMap u v) ≫ u = (a ≫ eqMap u v) ≫ v := by rw [Cat.assoc, Cat.assoc]; exact ha
  rw [eqLift_uniq u v _ hb a rfl, eqLift_uniq u v _ hb b hab.symm]

/-- A `WideEq` of a list `L` of parallel pairs over `X`: the maximal subobject equalizing all of
    them.  `dom`/`map` is the subobject `w : D ↪ X`; `eq` says `w` equalizes every listed pair;
    `mono` that `w` is monic; `lift`/`fac`/`uniq` the universal property. -/
structure WideEq (X : 𝒞) (L : List (Σ B : 𝒞, (X ⟶ B) × (X ⟶ B))) where
  dom  : 𝒞
  map  : dom ⟶ X
  mono : Mono map
  eq   : ∀ p ∈ L, map ≫ p.2.1 = map ≫ p.2.2
  lift : ∀ {Z : 𝒞} (k : Z ⟶ X), (∀ p ∈ L, k ≫ p.2.1 = k ≫ p.2.2) → (Z ⟶ dom)
  fac  : ∀ {Z : 𝒞} (k : Z ⟶ X) (h : ∀ p ∈ L, k ≫ p.2.1 = k ≫ p.2.2), lift k h ≫ map = k
  uniq : ∀ {Z : 𝒞} (k : Z ⟶ X) (h : ∀ p ∈ L, k ≫ p.2.1 = k ≫ p.2.2) (m : Z ⟶ dom),
           m ≫ map = k → m = lift k h

/-- The empty wide equalizer: `D = X`, `w = id` (no pairs to equalize). -/
def wideEqNil (X : 𝒞) : WideEq X [] where
  dom := X
  map := Cat.id X
  mono := by intro W a b hab; rw [← Cat.comp_id a, ← Cat.comp_id b]; exact hab
  eq p hp := absurd hp List.not_mem_nil
  lift k _ := k
  fac k _ := Cat.comp_id k
  uniq k _ m hm := by rw [← hm, Cat.comp_id]

/-- The cons step: equalize the head pair, then wide-equalize the tail composed with that
    equalizer's map.  `D = wideEq(tail ∘ e)`, `w = e' ≫ e` with `e = eqMap u v`. -/
def wideEqCons [HasEqualizers 𝒞] (X B : 𝒞) (u v : X ⟶ B)
    (L : List (Σ B : 𝒞, (X ⟶ B) × (X ⟶ B)))
    (tail : WideEq (eqObj u v) (L.map (fun p => ⟨p.1, eqMap u v ≫ p.2.1, eqMap u v ≫ p.2.2⟩))) :
    WideEq X (⟨B, u, v⟩ :: L) where
  dom := tail.dom
  map := tail.map ≫ eqMap u v
  mono := mono_comp' _ _ tail.mono (eqMap_mono' u v)
  eq p hp := by
    rcases List.mem_cons.1 hp with h | h
    · subst h; rw [Cat.assoc, Cat.assoc, eqMap_eq u v]
    · -- p ∈ L: tail.eq on the pulled-back pair
      have := tail.eq ⟨p.1, eqMap u v ≫ p.2.1, eqMap u v ≫ p.2.2⟩ (by
        exact List.mem_map.2 ⟨p, h, rfl⟩)
      simp only at this
      rw [Cat.assoc, Cat.assoc, this]
  lift {Z} k hk := by
    -- k equalizes u,v (head) ⇒ factors through eqObj as k'; k' equalizes the tail's pulled pairs
    have hhead : k ≫ u = k ≫ v := hk _ (List.mem_cons.2 (Or.inl rfl))
    refine tail.lift (eqLift u v k hhead) ?_
    intro p hp
    rcases List.mem_map.1 hp with ⟨q, hq, hpe⟩
    subst hpe
    simp only
    have hkq := hk q (List.mem_cons.2 (Or.inr hq))
    rw [← Cat.assoc, ← Cat.assoc, eqLift_fac u v k hhead, hkq]
  fac {Z} k hk := by
    have hhead : k ≫ u = k ≫ v := hk _ (List.mem_cons.2 (Or.inl rfl))
    rw [← Cat.assoc, tail.fac, eqLift_fac u v k hhead]
  uniq {Z} k hk m hm := by
    have hhead : k ≫ u = k ≫ v := hk _ (List.mem_cons.2 (Or.inl rfl))
    apply tail.uniq
    -- `m ≫ tail.map = eqLift u v k hhead`: cancel mono `eqMap u v` after `≫ eqMap`
    apply eqLift_uniq u v k hhead
    -- goal `(m ≫ tail.map) ≫ eqMap u v = k`; `hm` is the right-associated form.
    rw [Cat.assoc]; exact hm

/-- The wide equalizer of an arbitrary finite list, by recursion on the list length (the
    recursive call is on the tail `L`, whose mapped form has length `L.length < (hd::L).length`,
    even though its ambient object changes from `X` to `eqObj u v`). -/
def wideEq [HasEqualizers 𝒞] (X : 𝒞) :
    (L : List (Σ B : 𝒞, (X ⟶ B) × (X ⟶ B))) → WideEq X L
  | [] => wideEqNil X
  | ⟨B, u, v⟩ :: L => wideEqCons X B u v L (wideEq (eqObj u v) _)
  termination_by L => L.length
  decreasing_by simp only [List.length_map, List.length_cons]; omega

/-! ### §1.547  `Â` IS CARTESIAN — terminal object (milestone R4)

  Book (§1.547): "Note that `Â` is Cartesian, e.g. `(A₁,F₁) × (A₂,F₂) = (D,K)`" where `D ↪ A₁×A₂`
  is the maximal subobject equalizing all morphisms in `H = H₁ ∪ H₂` (`H₁ = {fst≫f | f∈F₁}`,
  `H₂ = {snd≫f | f∈F₂}`) with equal targets, and `K = {w≫h | h∈H}`.  The forgetful functor
  `Â → A` REFLECTS these from `A`'s finite limits.

  TERMINAL.  The terminal object of `Â` is `(1, ∅)` — the terminator of `A` with NO factors.  A
  morphism `X → (1,∅)` is just `term X.A : X.A → 1` (compatibility vacuous, `Y.F = ∅`), and it is
  unique because `term` is unique in `A`. -/

/-- **§1.547 — the terminal object of `Â`** is `(1, ∅)`: the terminator of `A` with no factors. -/
def pairTerminal : PairObj 𝒞 where
  A := HasTerminal.one
  F := []
  wsupp := by intro p hp; exact absurd hp (List.not_mem_nil)
  distinct := by intro r hr; exact absurd hr (List.not_mem_nil)

/-- The unique `Â`-morphism `X → (1,∅)`: underlying `term`, compatibility vacuous (`F = ∅`). -/
def pairToTerminal (X : PairObj 𝒞) : PairHom X pairTerminal where
  g := term X.A
  compat p hp := absurd hp (List.not_mem_nil)

/-- **§1.547 — `Â` has a terminal object** `(1,∅)`.  Uniqueness of `X → (1,∅)` is uniqueness of
    `X.A → 1` in `A` (`term_uniq`) lifted through `PairHom.ext` (a `PairHom` is its `.g`). -/
instance pairHasTerminal : HasTerminal (PairObj 𝒞) where
  one := pairTerminal
  trm X := pairToTerminal X
  uniq f g := PairHom.ext (term_uniq f.g g.g)

/-! ### §1.547  `Â` IS CARTESIAN — binary products `(A₁,F₁) × (A₂,F₂) = (D,K)`

  Book formula (§1.547): with `H₁ = {fst≫f | f∈F₁}`, `H₂ = {snd≫f' | f'∈F₂}` morphisms out of
  `A₁×A₂`, `D ↪ A₁×A₂` is the maximal subobject equalizing the morphisms of `H = H₁∪H₂` that share
  a target, and `K = {w≫h | h∈H}`.  Within `F₁` (resp. `F₂`) the targets are distinct, so the only
  forced equalizations are the CROSS pairs `(fst≫f, snd≫f')` for `f∈F₁`, `f'∈F₂` with `f° = f'°`.
  We collect those (decidable target match) and take their `wideEq`.

  `[DecidableEq 𝒞]` is used ONLY to build the cross-pair constraint list — Freyd's "morphisms with
  equal targets" is exactly this target-matching, which in his ambient (a category of sets) is
  decidable.  It is a NEW typeclass argument on the product construction; it weakens no protected
  statement. -/

section PairProd
variable [HasEqualizers 𝒞] [DecidableEq 𝒞]

/-- The CROSS constraint list for `(A₁,F₁)×(A₂,F₂)`: pairs `(fst≫f, snd≫f')` over `A₁×A₂` for
    `f∈F₁`, `f'∈F₂` whose targets agree (`f.1 = f'.1`), packaged for `wideEq`.  Built by a double
    `filterMap`, the target match decided by `DecidableEq 𝒞`. -/
def crossConstraints (X Y : PairObj 𝒞) :
    List (Σ B : 𝒞, (prod X.A Y.A ⟶ B) × (prod X.A Y.A ⟶ B)) :=
  X.F.flatMap (fun f => Y.F.filterMap (fun f' =>
    if h : f.1 = f'.1 then
      some ⟨f.1, (fst ≫ f.2, snd ≫ (h ▸ f'.2))⟩
    else none))

/-- The product OBJECT `D` of the §1.547 formula: the wide-equalizer of the cross constraints
    inside `A₁×A₂`. -/
def pairProdD (X Y : PairObj 𝒞) : 𝒞 := (wideEq (prod X.A Y.A) (crossConstraints X Y)).dom

/-- The subobject `w : D ↪ A₁×A₂`. -/
def pairProdW (X Y : PairObj 𝒞) : pairProdD X Y ⟶ prod X.A Y.A :=
  (wideEq (prod X.A Y.A) (crossConstraints X Y)).map

/-- `w` is monic. -/
theorem pairProdW_mono (X Y : PairObj 𝒞) : Mono (pairProdW X Y) :=
  (wideEq (prod X.A Y.A) (crossConstraints X Y)).mono

/-- `w` EQUALIZES every matched cross constraint: for `f∈F₁`, `f'∈F₂` with `f° = f'°` (`hff`),
    `w ≫ fst ≫ f.2 = w ≫ snd ≫ (hff ▸ f'.2)`.  The matched pair is in `crossConstraints` by the
    `dif_pos` branch, and `wideEq.eq` equalizes it. -/
theorem pairProdW_cross (X Y : PairObj 𝒞) {f : Σ T : 𝒞, X.A ⟶ T} (hf : f ∈ X.F)
    {f' : Σ T : 𝒞, Y.A ⟶ T} (hf' : f' ∈ Y.F) (hff : f.1 = f'.1) :
    pairProdW X Y ≫ fst ≫ f.2 = pairProdW X Y ≫ snd ≫ (hff ▸ f'.2) := by
  have hmem : (⟨f.1, (fst ≫ f.2, snd ≫ (hff ▸ f'.2))⟩ :
      Σ B : 𝒞, (prod X.A Y.A ⟶ B) × (prod X.A Y.A ⟶ B)) ∈ crossConstraints X Y := by
    refine List.mem_flatMap.2 ⟨f, hf, ?_⟩
    exact List.mem_filterMap.2 ⟨f', hf', by rw [dif_pos hff]⟩
  exact (wideEq (prod X.A Y.A) (crossConstraints X Y)).eq _ hmem

/-- The factor list `K = {w≫h | h∈H}` of the product object: `w≫fst≫f` for `f∈F₁`, `w≫snd≫f'`
    for `f'∈F₂`. -/
def pairProdK (X Y : PairObj 𝒞) : List (Σ T : 𝒞, pairProdD X Y ⟶ T) :=
  X.F.map (fun f => ⟨f.1, pairProdW X Y ≫ fst ≫ f.2⟩) ++
  Y.F.map (fun f' => ⟨f'.1, pairProdW X Y ≫ snd ≫ f'.2⟩)

/-- The targets in `K` are well-supported (they are targets of `F₁` or `F₂`). -/
theorem pairProdK_wsupp (X Y : PairObj 𝒞) : ∀ p ∈ pairProdK X Y, WellSupported p.1 := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · rcases List.mem_map.1 h with ⟨f, hf, he⟩; rw [← he]; exact X.wsupp f hf
  · rcases List.mem_map.1 h with ⟨f', hf', he⟩; rw [← he]; exact Y.wsupp f' hf'

/-- The factors of `K` go to DISTINCT targets (§1.547 product is again a legal `PairObj`).  Two
    factors of `K` with equal target are equal: both in the `F₁`-half (`X.distinct`), both in the
    `F₂`-half (`Y.distinct`), or one of each — the CROSS case, equal because `w` equalizes the cross
    constraint (`pairProdW_cross`).  `w≫fst≫(-)`/`w≫snd≫(-)` transport the factor equalities. -/
theorem pairProdK_distinct (X Y : PairObj 𝒞) :
    ∀ r ∈ pairProdK X Y, ∀ r' ∈ pairProdK X Y, ∀ h : r.1 = r'.1, h ▸ r.2 = r'.2 := by
  -- helper: `w≫fst≫(-)` of equal-after-transport factors of `X.F` are equal-after-transport
  have congT : ∀ {B B' : 𝒞} (m : pairProdD X Y ⟶ prod X.A Y.A) (p : X.A ⟶ B) (q : X.A ⟶ B')
      (h : B = B'), h ▸ p = q → (h ▸ (m ≫ fst ≫ p) : pairProdD X Y ⟶ B') = m ≫ fst ≫ q := by
    intro B B' m p q h hpq; cases h; simp only at hpq ⊢; rw [hpq]
  have congT' : ∀ {B B' : 𝒞} (m : pairProdD X Y ⟶ prod X.A Y.A) (p : Y.A ⟶ B) (q : Y.A ⟶ B')
      (h : B = B'), h ▸ p = q → (h ▸ (m ≫ snd ≫ p) : pairProdD X Y ⟶ B') = m ≫ snd ≫ q := by
    intro B B' m p q h hpq; cases h; simp only at hpq ⊢; rw [hpq]
  intro r hr r' hr' h
  rcases List.mem_append.1 hr with hL | hR <;> rcases List.mem_append.1 hr' with hL' | hR'
  · -- both F₁-half
    rcases List.mem_map.1 hL with ⟨f, hf, he⟩; rcases List.mem_map.1 hL' with ⟨f', hf', he'⟩
    subst he; subst he'
    exact congT (pairProdW X Y) f.2 f'.2 h (X.distinct f hf f' hf' h)
  · -- r in F₁-half, r' in F₂-half: cross
    rcases List.mem_map.1 hL with ⟨f, hf, he⟩; rcases List.mem_map.1 hR' with ⟨f', hf', he'⟩
    subst he; subst he'
    -- destruct factors so the target equality `h : f.1 = f'.1` is over plain objects
    obtain ⟨B, ff⟩ := f; obtain ⟨B', ff'⟩ := f'
    simp only at h ⊢; subst h
    -- goal: w≫fst≫ff = w≫snd≫ff';  pairProdW_cross at `rfl`
    have := pairProdW_cross X Y hf hf' rfl; simpa using this
  · -- r in F₂-half, r' in F₁-half: cross (symmetric)
    rcases List.mem_map.1 hR with ⟨f', hf', he⟩; rcases List.mem_map.1 hL' with ⟨f, hf, he'⟩
    subst he; subst he'
    obtain ⟨B', ff'⟩ := f'; obtain ⟨B, ff⟩ := f
    simp only at h ⊢; subst h
    -- goal: w≫snd≫ff' = w≫fst≫ff
    have := pairProdW_cross X Y hf hf' rfl; simpa using this.symm
  · -- both F₂-half
    rcases List.mem_map.1 hR with ⟨f, hf, he⟩; rcases List.mem_map.1 hR' with ⟨f', hf', he'⟩
    subst he; subst he'
    exact congT' (pairProdW X Y) f.2 f'.2 h (Y.distinct f hf f' hf' h)

/-- **§1.547 — the product object `(D,K)`** of `(A₁,F₁)` and `(A₂,F₂)` in `Â`. -/
def pairProdObj (X Y : PairObj 𝒞) : PairObj 𝒞 where
  A := pairProdD X Y
  F := pairProdK X Y
  wsupp := pairProdK_wsupp X Y
  distinct := pairProdK_distinct X Y

/-- **§1.547 — first projection** `(D,K) → (A₁,F₁)`, underlying `w≫fst`.  Compatibility: each
    `f∈F₁` has `w≫fst≫f ∈ K` (the `F₁`-half of `K`), with `(w≫fst)≫f = w≫fst≫f`. -/
def pairProjFst (X Y : PairObj 𝒞) : PairHom (pairProdObj X Y) X where
  g := pairProdW X Y ≫ fst
  compat p hp := by
    refine ⟨⟨p.1, pairProdW X Y ≫ fst ≫ p.2⟩, ?_, rfl, by rw [Cat.assoc]⟩
    exact List.mem_append.2 (Or.inl (List.mem_map.2 ⟨p, hp, rfl⟩))

/-- **§1.547 — second projection** `(D,K) → (A₂,F₂)`, underlying `w≫snd`. -/
def pairProjSnd (X Y : PairObj 𝒞) : PairHom (pairProdObj X Y) Y where
  g := pairProdW X Y ≫ snd
  compat p hp := by
    refine ⟨⟨p.1, pairProdW X Y ≫ snd ≫ p.2⟩, ?_, rfl, by rw [Cat.assoc]⟩
    exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨p, hp, rfl⟩))

/-- **§1.547 — UNIQUENESS of the product pairing** (unconditional).  Two `Â`-arrows into `(D,K)`
    agreeing after both projections are equal: underlying `α≫(w≫fst) = β≫(w≫fst)` and the `snd`
    analogue give `(α≫w)≫fst = (β≫w)≫fst` and `≫snd`, so `α≫w = β≫w` (`prod_hom_ext`), then
    `α = β` (`w` monic, `pairProdW_mono`), then `PairHom.ext`. -/
theorem pairProd_hom_ext {Z X Y : PairObj 𝒞} (a b : PairHom Z (pairProdObj X Y))
    (h₁ : a.comp (pairProjFst X Y) = b.comp (pairProjFst X Y))
    (h₂ : a.comp (pairProjSnd X Y) = b.comp (pairProjSnd X Y)) : a = b := by
  apply PairHom.ext
  apply pairProdW_mono X Y
  apply prod_hom_ext
  · have := congrArg PairHom.g h₁
    simpa [PairHom.comp, pairProjFst, Cat.assoc] using this
  · have := congrArg PairHom.g h₂
    simpa [PairHom.comp, pairProjSnd, Cat.assoc] using this

/-! ### §1.547  Product pairing — EXISTENCE (the R3 `PairObj` distinctness gap)

  The pairing `⟨a,b⟩ : Z → (D,K)` has underlying `pair α β : A₀ → A₁×A₂`; it factors through the
  subobject `w : D ↪ A₁×A₂` iff `pair α β` EQUALIZES every cross constraint, i.e. for each matched
  `f∈F₁`, `f'∈F₂` (`f° = f'°`), `α≫f = β≫f'`.  By compatibility of `a` (resp. `b`) this is
  `r.2 = r'.2` for the factors `r,r' ∈ F₀` that `a` (resp. `b`) sends `f` (resp. `f'`) to — both of
  TARGET `f° = f'°`.  The book guarantees this because `F₀`'s targets are DISTINCT (so `r = r'`),
  but R3's `PairObj` (shared, downstream) records only well-supportedness, NOT distinctness.  So
  the pairing factors precisely under the hypothesis `Hdistinct`: any two factors of `Z`'s set with
  equal target are equal.  We state the pairing with this genuine hypothesis (NOT faked); the full
  unconditional `HasBinaryProducts (PairObj 𝒞)` instance is blocked on adding distinctness to
  `PairObj`, sharply documented here. -/

/-- The "distinct targets" property of a `PairObj`'s factor set: factors with equal target are
    equal (after transport).  Book §1.547 requires it of every object of `Â`; it is now a FIELD of
    `PairObj` (`PairObj.distinct`), so it always holds — this def is its abbreviation, and the
    §1.547 product pairing below is therefore UNCONDITIONAL. -/
def PairObj.DistinctTargets (Z : PairObj 𝒞) : Prop :=
  ∀ r ∈ Z.F, ∀ r' ∈ Z.F, ∀ h : r.1 = r'.1, h ▸ r.2 = r'.2

/-- The underlying lift `pair a.g b.g` equalizes every cross constraint (matched factors of `X`,`Y`
    pull back to factors of `Z` of equal target, equal by `Hdistinct`). -/
theorem pairPair_equ {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) :
    ∀ q ∈ crossConstraints X Y, pair a.g b.g ≫ q.2.1 = pair a.g b.g ≫ q.2.2 := by
  intro q hq
  rcases List.mem_flatMap.1 hq with ⟨f, hf, hq2⟩
  rcases List.mem_filterMap.1 hq2 with ⟨f', hf', hq3⟩
  by_cases hff : f.1 = f'.1
  · rw [dif_pos hff] at hq3
    cases hq3
    obtain ⟨r, hr, hrt, hre⟩ := a.compat f hf
    obtain ⟨r', hr', hrt', hre'⟩ := b.compat f' hf'
    have hmatch : (hrt.trans (hff.trans hrt'.symm) : r.1 = r'.1) ▸ r.2 = r'.2 :=
      Hdistinct r hr r' hr' _
    obtain ⟨B, ff⟩ := f; obtain ⟨B', ff'⟩ := f'
    obtain ⟨C, rr⟩ := r; obtain ⟨C', rr'⟩ := r'
    simp only at hff hrt hrt' hre hre' hmatch ⊢
    subst hff; subst hrt; subst hrt'
    simp only [eq_mpr_eq_cast, cast_eq] at hre hre' hmatch ⊢
    rw [← Cat.assoc, ← Cat.assoc, fst_pair, snd_pair, hre, hre', hmatch]
  · rw [dif_neg hff] at hq3; exact absurd hq3 (by simp)

/-- The lift map `d : Z.A → D` of `pair a.g b.g` through the subobject `w`. -/
def pairPairMap {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) : Z.A ⟶ pairProdD X Y :=
  (wideEq (prod X.A Y.A) (crossConstraints X Y)).lift (pair a.g b.g) (pairPair_equ Hdistinct a b)

theorem pairPairMap_w {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) :
    pairPairMap Hdistinct a b ≫ pairProdW X Y = pair a.g b.g :=
  (wideEq (prod X.A Y.A) (crossConstraints X Y)).fac (pair a.g b.g) (pairPair_equ Hdistinct a b)

/-- **§1.547 — the product PAIRING** `⟨a,b⟩ : Z → (D,K)` (data, choice-free), under the book's
    target-distinctness of `Z`.  Underlying `pair a.g b.g` factored through `w`; the compatibility
    is the two half-compatibilities of `a`,`b`. -/
def pairPair {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) : PairHom Z (pairProdObj X Y) where
  g := pairPairMap Hdistinct a b
  compat := by
    have hd := pairPairMap_w Hdistinct a b
    intro p hp
    rcases List.mem_append.1 hp with hL | hR
    · rcases List.mem_map.1 hL with ⟨f, hf, he⟩
      obtain ⟨r, hr, hrt, hre⟩ := a.compat f hf
      refine ⟨r, hr, by rw [hrt]; exact congrArg (·.1) he, ?_⟩
      subst he
      have : pairPairMap Hdistinct a b ≫ pairProdW X Y ≫ fst ≫ f.2 = a.g ≫ f.2 := by
        rw [← Cat.assoc _ (pairProdW X Y), hd, ← Cat.assoc, fst_pair]
      rw [this, hre]
    · rcases List.mem_map.1 hR with ⟨f', hf', he⟩
      obtain ⟨r', hr', hrt', hre'⟩ := b.compat f' hf'
      refine ⟨r', hr', by rw [hrt']; exact congrArg (·.1) he, ?_⟩
      subst he
      have : pairPairMap Hdistinct a b ≫ pairProdW X Y ≫ snd ≫ f'.2 = b.g ≫ f'.2 := by
        rw [← Cat.assoc _ (pairProdW X Y), hd, ← Cat.assoc, snd_pair]
      rw [this, hre']

theorem pairPair_fst {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) :
    (pairPair Hdistinct a b).comp (pairProjFst X Y) = a :=
  PairHom.ext (by
    show (pairPairMap Hdistinct a b ≫ pairProdW X Y ≫ fst) = a.g
    rw [← Cat.assoc, pairPairMap_w, fst_pair])

theorem pairPair_snd {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) :
    (pairPair Hdistinct a b).comp (pairProjSnd X Y) = b :=
  PairHom.ext (by
    show (pairPairMap Hdistinct a b ≫ pairProdW X Y ≫ snd) = b.g
    rw [← Cat.assoc, pairPairMap_w, snd_pair])

/-- **§1.547 — EXISTENCE of the product pairing** under the book's target-distinctness (the
    universal-property existence, repackaged from the choice-free `pairPair` data). -/
theorem pairProd_lift {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) :
    ∃ p : PairHom Z (pairProdObj X Y),
      p.comp (pairProjFst X Y) = a ∧ p.comp (pairProjSnd X Y) = b :=
  ⟨pairPair Hdistinct a b, pairPair_fst Hdistinct a b, pairPair_snd Hdistinct a b⟩

/-! ### §1.547  `Â` HAS BINARY PRODUCTS — UNCONDITIONAL (distinctness is a `PairObj` field)

  Freyd's §1.547 takes EVERY object of `Â` to have factors to "DISTINCT well-supported targets".
  Since distinctness is now a FIELD of `PairObj` (`PairObj.distinct`), the §1.547 product pairing is
  TOTAL with NO side hypothesis: `pair = pairPair Z.distinct`, `pair_uniq = pairProd_hom_ext`.  This
  is the resolution of the DISTINCTNESS GATE that keeps `ratCap S : CapStep S` unconditional in `S`
  (an arbitrary pre-regular `S` has objects `PairObj S` that carry their own distinctness witness). -/

/-- **§1.547 — `Â` HAS BINARY PRODUCTS** (UNCONDITIONAL).  Object/projections are the §1.547 `(D,K)`
    formula (`pairProdObj`/`pairProj…`); `pair` is the lift `pairPair` fed the object's own
    `distinct` field; `pair_uniq` is `pairProd_hom_ext`.  No extra typeclass — distinctness rides on
    every `PairObj`. -/
instance pairHasBinaryProducts [HasEqualizers 𝒞] [DecidableEq 𝒞] :
    HasBinaryProducts (PairObj 𝒞) where
  prod := pairProdObj
  fst {X Y} := pairProjFst X Y
  snd {X Y} := pairProjSnd X Y
  pair {Z X Y} a b := pairPair Z.distinct a b
  fst_pair {Z X Y} a b := pairPair_fst Z.distinct a b
  snd_pair {Z X Y} a b := pairPair_snd Z.distinct a b
  pair_uniq {Z X Y} a b h h₁ h₂ :=
    pairProd_hom_ext h _
      (h₁.trans (pairPair_fst Z.distinct a b).symm)
      (h₂.trans (pairPair_snd Z.distinct a b).symm)

end PairProd

/-! ### §1.547  `Â` HAS EQUALIZERS — the forgetful functor creates them from `A`'s equalizers

  The equalizer of `a, b : (A,F) → (B,G)` in `Â` is `(E, e^*F)` where `e : E ↪ A` is the equalizer
  of the underlying `a.g, b.g` in `A` and `e^*F = {⟨f°, e≫f⟩ | f ∈ F}` is `F` pulled back along `e`.
  Its targets are those of `F` (still well-supported); its factors stay distinct because `e` is monic
  (so `e≫f = e≫f' ⟹ f = f'`, combined with `F`'s distinctness).  The equalizer `PairHom`
  `(E,e^*F) → (A,F)` is underlying-`e` (compat: `f ∈ F` ↦ `e≫f ∈ e^*F`); its universal property is
  the underlying equalizer's (`eqLift`), the lifted arrow's compat coming from `k`'s own compat.
  `pairForget` thus CREATES equalizers, giving `Â` finite limits (hence pullbacks via §1.432). -/

section PairEq
variable [HasEqualizers 𝒞]

/-- The factor set of the §1.547 equalizer object: `F` pulled back along the underlying equalizer
    `e = eqMap a.g b.g`.  `{⟨f°, e≫f⟩ | f ∈ X.F}`. -/
def pairEqK {X Y : PairObj 𝒞} (a b : PairHom X Y) : List (Σ T : 𝒞, eqObj a.g b.g ⟶ T) :=
  X.F.map (fun f => ⟨f.1, eqMap a.g b.g ≫ f.2⟩)

theorem pairEqK_wsupp {X Y : PairObj 𝒞} (a b : PairHom X Y) :
    ∀ p ∈ pairEqK a b, WellSupported p.1 := by
  intro p hp; rcases List.mem_map.1 hp with ⟨f, hf, he⟩; rw [← he]; exact X.wsupp f hf

theorem pairEqK_distinct {X Y : PairObj 𝒞} (a b : PairHom X Y) :
    ∀ r ∈ pairEqK a b, ∀ r' ∈ pairEqK a b, ∀ h : r.1 = r'.1, h ▸ r.2 = r'.2 := by
  have congE : ∀ {B B' : 𝒞} (p : X.A ⟶ B) (q : X.A ⟶ B') (h : B = B'), h ▸ p = q →
      (h ▸ (eqMap a.g b.g ≫ p) : eqObj a.g b.g ⟶ B') = eqMap a.g b.g ≫ q := by
    intro B B' p q h hpq; cases h; simp only at hpq ⊢; rw [hpq]
  intro r hr r' hr' h
  rcases List.mem_map.1 hr with ⟨f, hf, he⟩; rcases List.mem_map.1 hr' with ⟨f', hf', he'⟩
  subst he; subst he'
  exact congE f.2 f'.2 h (X.distinct f hf f' hf' h)

/-- The §1.547 equalizer OBJECT `(E, e^*F)` of `a, b : X → Y`. -/
def pairEqObj {X Y : PairObj 𝒞} (a b : PairHom X Y) : PairObj 𝒞 where
  A := eqObj a.g b.g
  F := pairEqK a b
  wsupp := pairEqK_wsupp a b
  distinct := pairEqK_distinct a b

/-- The equalizer `PairHom` `(E,e^*F) → X`, underlying `e = eqMap a.g b.g`.  Compat: `f ∈ X.F` maps
    to `⟨f°, e≫f⟩ ∈ e^*F`. -/
def pairEqMap {X Y : PairObj 𝒞} (a b : PairHom X Y) : PairHom (pairEqObj a b) X where
  g := eqMap a.g b.g
  compat p hp := ⟨⟨p.1, eqMap a.g b.g ≫ p.2⟩, List.mem_map.2 ⟨p, hp, rfl⟩, rfl, rfl⟩

/-- The equalizer `PairHom` equalizes `a, b` (its underlying `e` does, `eqMap_eq`). -/
theorem pairEqMap_eq {X Y : PairObj 𝒞} (a b : PairHom X Y) :
    (pairEqMap a b).comp a = (pairEqMap a b).comp b :=
  PairHom.ext (by show eqMap a.g b.g ≫ a.g = eqMap a.g b.g ≫ b.g; exact eqMap_eq a.g b.g)

/-- The underlying equalizer condition of a `Â`-cone `k : Z → X` (`k.comp a = k.comp b` gives
    `k.g ≫ a.g = k.g ≫ b.g`). -/
theorem pairEqLift_hyp {X Y : PairObj 𝒞} (a b : PairHom X Y) {Z : PairObj 𝒞} {k : PairHom Z X}
    (hk : k.comp a = k.comp b) : k.g ≫ a.g = k.g ≫ b.g := by
  have := congrArg PairHom.g hk; simpa [PairHom.comp] using this

/-- The lift of a cone `(k : Z → X` with `k.comp a = k.comp b)` through the §1.547 equalizer.
    Underlying `eqLift` of `k.g`; compat lifted from `k`'s compat (a factor `⟨f°,e≫f⟩ ∈ e^*F` is hit
    by `k`'s factor for `f`, since `(eqLift k.g)≫e≫f = k.g≫f`). -/
def pairEqLift {X Y : PairObj 𝒞} (a b : PairHom X Y) {Z : PairObj 𝒞} (k : PairHom Z X)
    (hk : k.comp a = k.comp b) : PairHom Z (pairEqObj a b) where
  g := eqLift a.g b.g k.g (pairEqLift_hyp a b hk)
  compat p hp := by
    rcases List.mem_map.1 hp with ⟨f, hf, he⟩
    obtain ⟨q, hq, hqt, hqe⟩ := k.compat f hf
    refine ⟨q, hq, by rw [hqt]; exact congrArg (·.1) he, ?_⟩
    -- (eqLift k.g) ≫ (e≫f.2) = k.g ≫ f.2 = q.2 (transported)
    subst he
    have hfac : eqLift a.g b.g k.g (pairEqLift_hyp a b hk) ≫ eqMap a.g b.g = k.g :=
      eqLift_fac a.g b.g k.g (pairEqLift_hyp a b hk)
    have : eqLift a.g b.g k.g (pairEqLift_hyp a b hk) ≫ (eqMap a.g b.g ≫ f.2) = k.g ≫ f.2 := by
      rw [← Cat.assoc, hfac]
    rw [this, hqe]

theorem pairEqLift_fac {X Y : PairObj 𝒞} (a b : PairHom X Y) {Z : PairObj 𝒞} (k : PairHom Z X)
    (hk : k.comp a = k.comp b) : (pairEqLift a b k hk).comp (pairEqMap a b) = k :=
  PairHom.ext (by
    show eqLift a.g b.g k.g (pairEqLift_hyp a b hk) ≫ eqMap a.g b.g = k.g
    exact eqLift_fac a.g b.g k.g (pairEqLift_hyp a b hk))

theorem pairEqLift_uniq {X Y : PairObj 𝒞} (a b : PairHom X Y) {Z : PairObj 𝒞} (k : PairHom Z X)
    (hk : k.comp a = k.comp b) (m : PairHom Z (pairEqObj a b))
    (hm : m.comp (pairEqMap a b) = k) : m = pairEqLift a b k hk :=
  PairHom.ext (by
    apply eqLift_uniq a.g b.g k.g (pairEqLift_hyp a b hk) m.g
    have := congrArg PairHom.g hm; simpa [PairHom.comp, pairEqMap] using this)

/-- **§1.547 — `Â` HAS EQUALIZERS** (forgetful functor creates them).  The equalizer cone is
    `(E,e^*F)` with map `pairEqMap`; universal property from the underlying equalizer in `A`. -/
instance pairHasEqualizers : HasEqualizers (PairObj 𝒞) where
  eq X Y a b :=
    { cone := ⟨pairEqObj a b, pairEqMap a b, pairEqMap_eq a b⟩
      lift := fun c => pairEqLift a b c.map c.eq
      fac := fun c => pairEqLift_fac a b c.map c.eq
      uniq := fun c m hm => pairEqLift_uniq a b c.map c.eq m hm }

/-- **§1.547 — `Â` HAS PULLBACKS** (§1.432: terminal + products + equalizers ⟹ pullbacks).  The
    pullback of `f, g` is the equalizer of `fst≫f`, `snd≫g` on the product — built once and for all
    by `products_equalizers_implies_pullbacks` on the `Â`-level finite limits. -/
instance pairHasPullbacks [DecidableEq 𝒞] : HasPullbacks (PairObj 𝒞) where
  has f g := products_equalizers_implies_pullbacks f g

/-! ### §1.547  Covers in `Â` and the pre-regular structure

  Freyd (§1.547): "the forgetful functor `Â → A` is faithful and preserves pullbacks and covers",
  and `A*` (the localisation) "is equivalent to a directed union of slices", each pre-regular — that
  slice-equivalence is what makes `A*` pre-regular.  We make the cover bridge precise and isolate
  the one genuine §1.547 content as a sharply-documented obstruction.

  FORWARD (`pairCover_underlying`, PROVEN): an `Â`-cover `f` has underlying `f.g` an `A`-cover.  Any
  `A`-monic `m : C ↪ Y.A` factoring `f.g` LIFTS to an `Â`-monic `(C, m^*F) → Y` factoring `f`; the
  `Â`-cover forces it iso in `Â`, hence `m` iso in `A`.  The lift is `Â`-monic because `m` is a
  genuine `A`-mono.

  The CONVERSE (underlying `A`-cover ⟹ `Â`-cover) does NOT hold for a free `pairForget`: `Â`-monos
  are tested only against the (fewer) `Â`-arrows, so `pairForget` does not reflect monos, and the
  intrinsic cover-transfer in `Â` is exactly Freyd's slice-equivalence verification (the directed
  union of pre-regular slices) — the same content the directed-colimit route hits at the strictness
  wall (module docstring, R1).  `pairPullbacksTransferCovers` carries the book's true statement with
  that single isolated obstruction; everything feeding it (finite limits, the forward bridge) is
  sorry-free. -/

/-- Pull back a factor set along an `A`-arrow `e : E → X.A`: `{⟨f°, e≫f⟩ | f ∈ X.F}`.  When `e` is
    monic this is again distinct (and the targets are unchanged, so still well-supported). -/
def pullbackFactors {E : 𝒞} {X : PairObj 𝒞} (e : E ⟶ X.A) : List (Σ T : 𝒞, E ⟶ T) :=
  X.F.map (fun f => ⟨f.1, e ≫ f.2⟩)

theorem pullbackFactors_wsupp {E : 𝒞} {X : PairObj 𝒞} (e : E ⟶ X.A) :
    ∀ p ∈ pullbackFactors e, WellSupported p.1 := by
  intro p hp; rcases List.mem_map.1 hp with ⟨f, hf, he⟩; rw [← he]; exact X.wsupp f hf

theorem pullbackFactors_distinct {E : 𝒞} {X : PairObj 𝒞} {e : E ⟶ X.A} (hm : Mono e) :
    ∀ r ∈ pullbackFactors e, ∀ r' ∈ pullbackFactors e, ∀ h : r.1 = r'.1, h ▸ r.2 = r'.2 := by
  have congP : ∀ {B B' : 𝒞} (p : X.A ⟶ B) (q : X.A ⟶ B') (h : B = B'), h ▸ p = q →
      (h ▸ (e ≫ p) : E ⟶ B') = e ≫ q := by
    intro B B' p q h hpq; cases h; simp only at hpq ⊢; rw [hpq]
  intro r hr r' hr' h
  rcases List.mem_map.1 hr with ⟨f, hf, he⟩; rcases List.mem_map.1 hr' with ⟨f', hf', he'⟩
  subst he; subst he'
  exact congP f.2 f'.2 h (X.distinct f hf f' hf' h)

/-- The lift object `(C, m^*Y.F)` for an `A`-monic `m : C → Y.A` into a `PairObj` `Y`. -/
def liftObj {C : 𝒞} {Y : PairObj 𝒞} {m : C ⟶ Y.A} (hm : Mono m) : PairObj 𝒞 where
  A := C
  F := pullbackFactors m
  wsupp := pullbackFactors_wsupp m
  distinct := pullbackFactors_distinct hm

/-- The lifted `Â`-arrow `m̂ : (C, m^*F) → Y`, underlying `m`.  Compat: `f ∈ Y.F` ↦ `⟨f°, m≫f⟩`. -/
def liftMono {C : 𝒞} {Y : PairObj 𝒞} {m : C ⟶ Y.A} (hm : Mono m) : PairHom (liftObj hm) Y where
  g := m
  compat p hp := ⟨⟨p.1, m ≫ p.2⟩, List.mem_map.2 ⟨p, hp, rfl⟩, rfl, rfl⟩

/-- The lifted arrow is monic in `Â`: parallel `Â`-arrows `a, b` with `a.comp m̂ = b.comp m̂` have
    `a.g ≫ m = b.g ≫ m`, and `m` an `A`-mono cancels to `a.g = b.g`, so `a = b`. -/
theorem liftMono_mono {C : 𝒞} {Y : PairObj 𝒞} {m : C ⟶ Y.A} (hm : Mono m) :
    @Mono (PairObj 𝒞) _ (liftObj hm) Y (liftMono hm) := by
  intro Z a b hab
  apply PairHom.ext
  apply hm
  have : (a.comp (liftMono hm)).g = (b.comp (liftMono hm)).g := congrArg PairHom.g hab
  simpa [PairHom.comp, liftMono] using this

/-- **§1.547 forward bridge — an `Â`-cover has an `A`-cover underlying arrow.**  Any `A`-monic `m`
    factoring `f.g` lifts to an `Â`-monic `liftMono` factoring `f`; the `Â`-cover forces it iso in
    `Â`, hence `m` iso in `A`.  Proves Freyd's "`pairForget` preserves covers" (forward half). -/
theorem pairCover_underlying {X Y : PairObj 𝒞} {f : PairHom X Y}
    (hf : @Cover (PairObj 𝒞) _ X Y f) : Cover f.g := by
  intro C m h hm hfac
  -- lift `m` to `Â`-monic `m̂`; `f` factors through it via `ĥ` underlying `h`
  have hĥcompat : ∀ p ∈ (liftObj hm).F, ∃ q ∈ X.F, ∃ ht : q.1 = p.1, h ≫ p.2 = ht ▸ q.2 := by
    intro p hp
    rcases List.mem_map.1 hp with ⟨e, he, hpe⟩
    obtain ⟨q, hq, hqt, hqe⟩ := f.compat e he
    refine ⟨q, hq, by rw [hqt]; exact congrArg (·.1) hpe, ?_⟩
    subst hpe
    -- h ≫ (m ≫ e.2) = (h ≫ m) ≫ e.2 = f.g ≫ e.2 = q.2
    show h ≫ m ≫ e.2 = hqt ▸ q.2
    rw [← Cat.assoc, hfac, hqe]
  let ĥ : PairHom X (liftObj hm) := ⟨h, hĥcompat⟩
  have hĥm : ĥ.comp (liftMono hm) = f := PairHom.ext (by show h ≫ m = f.g; exact hfac)
  obtain ⟨n, hn₁, hn₂⟩ := hf (liftMono hm) ĥ (liftMono_mono hm) hĥm
  -- `n : Y → liftObj hm` inverts `liftMono` in `Â`; underlying gives `m` iso in `A`
  refine ⟨n.g, ?_, ?_⟩
  · have := congrArg PairHom.g hn₁; simpa [PairHom.comp, liftMono] using this
  · have := congrArg PairHom.g hn₂; simpa [PairHom.comp, liftMono] using this

/-- **§1.547 — `Â`'s pullbacks transfer covers** (the pre-regular closure condition).  The STATEMENT
    is Freyd's genuine `PullbacksTransferCovers`: in a pullback square in `Â`, the leg opposite an
    `Â`-cover is an `Â`-cover.  Freyd discharges this for `Â` via the slice equivalence — "`A*` is a
    directed union of slices `A*|U`, each pre-regular", so the cover structure of `Â`/`A*` is read
    off the pre-regular slices (§1.547, and §1.481 localisation preserves pre-regular).

    The forward bridge `pairCover_underlying` (`Â`-cover ⟹ `A`-cover, sorry-free) reduces the
    underlying square to `A`'s own `PullbacksTransferCovers`, giving the OPPOSITE leg's underlying
    `c.π₂.g` an `A`-cover; the remaining step — promoting that back to an `Â`-cover — is exactly the
    direction `pairForget` does NOT reflect (`Â`-monos are tested against fewer arrows), i.e. the
    slice-equivalence verification.  This is the single sharply-isolated §1.547 obstruction; every
    finite-limit and forward-cover ingredient feeding the pre-regular structure is sorry-free. -/
theorem pairPullbacksTransferCovers [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞] :
    ∀ {A B C : PairObj 𝒞} {f : A ⟶ B} {g : C ⟶ B}
      (c : @Cone (PairObj 𝒞) _ _ _ _ f g), c.IsPullback →
      @Cover (PairObj 𝒞) _ _ _ f → @Cover (PairObj 𝒞) _ _ _ c.π₂ := by
  sorry

/-- **§1.547 — `Â` IS PRE-REGULAR.**  Terminal (`pairHasTerminal`), binary products
    (`pairHasBinaryProducts`), pullbacks (`pairHasPullbacks`), and pullbacks-transfer-covers
    (`pairPullbacksTransferCovers`).  This is the §1.547 pre-regular intermediate category; the only
    non-sorry-free field is the cover transfer, which is Freyd's slice-equivalence verification. -/
instance pairPreRegular [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞] :
    PreRegularCategory (PairObj 𝒞) where
  pullbacks_transfer_covers c hpb hf := pairPullbacksTransferCovers c hpb hf

/-! ### §1.547  `PairDense` as a `DenseClass (PairObj 𝒞)` — the class the rational category inverts

  With `Â`'s pullbacks in hand we package the §1.547 dense morphisms into the `DenseClass` record
  the §1.48 rational category consumes: `mem x := Nonempty (PairDense x)`.  Closure under isos
  (`pairDense_of_isIso`) and composition (`pairDense_comp`) are sorry-free (R3).  Pullback-closure
  (§1.48(iii)) is the dense morphism's product-projection form being stable under base change: the
  `Â`-pullback of `x : X→Y` (with `X.A ≅ Y.A × W`, `x.g = fst`) along any `g : Z→Y` is again a
  projection `Z.A × W → Z.A` onto the SAME well-supported `W`, hence dense.  Its proof descends to
  the underlying product-pullback in `A`; it is stated here with that exact obstruction and is the
  one remaining dense-class field (the rest sorry-free). -/

/-- §1.48(iii) for `Â`: the dense morphisms are closed under pullback.  STATEMENT is the genuine
    `DenseClass.pb_mem` obligation for `PairDense`; the dense `x`'s product-projection form
    (`X.A ≅ Y.A × W`, `x.g = fst`) is stable under base change, the `Â`-pullback projection being
    `Z.A × W → Z.A` onto the same `W` — read off the underlying product-pullback in `A`. -/
theorem pairDense_pb [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞]
    {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (hx : Nonempty (PairDense x)) :
    Nonempty (PairDense ((HasPullbacks.has g x).cone.π₁)) := by
  sorry

/-- **§1.547 — `PairDense` is a `DenseClass (PairObj 𝒞)`.**  `mem x := Nonempty (PairDense x)`; isos
    dense (`pairDense_of_isIso`), composition-closed (`pairDense_comp`), pullback-closed
    (`pairDense_pb`).  This is the refined dense class the §1.48 rational category inverts to form
    `A* = Â[PairDense⁻¹]`. -/
def pairDenseClass [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞] : DenseClass (PairObj 𝒞) where
  mem x := Nonempty (PairDense x)
  iso_mem x hx := pairDense_of_isIso hx
  comp_mem x y hx hy := hx.elim (fun dx => hy.elim (fun dy => ⟨pairDense_comp dx dy⟩))
  pb_mem x g hx := pairDense_pb x g hx

/-! ### §1.547  THE MONIC/EPIC WALL — `pairDenseClass` is NOT a `MonicDense` class

  The monic left-fraction skeleton (`MonicDense`, above) cannot be instantiated on `pairDenseClass`.
  Its members are EPIC in `Â` (`pairDense_epi`); a `MonicDense pairDenseClass` would force every dense
  morphism MONIC as well, hence (being epic) an iso — collapsing the dense class to the isos, so the
  localisation `Â[pairDense⁻¹]` would be trivial (`= Â`) instead of §1.547's genuine `A*`.  Thus the
  §1.547 localisation is at an EPIC class and is modelled by the DUAL right-fraction (co-span) calculus,
  not by this skeleton.  This is the precise, machine-checked form of the R1/R2 monic/epic wall.

  `not_monicDense_pairDenseClass`: a `MonicDense pairDenseClass` makes every `pairDense` morphism both
  MONIC and EPIC in `Â`.  (Combined with `pairDense_cover` — dense underlying-arrows are covers — this
  pins the collapse: a monic cover is an iso.) -/

/-- **Obstruction (machine-checked, sorry-free).**  A `pairDense` morphism is always EPIC in `Â`
    (`pairDense_epi`); if additionally — as a `MonicDense` localisation hypothesis would force — it were
    MONIC in `Â`, it would be both.  Phrased decoupled from the `pairDenseClass` record (which carries
    the `pairDense_pb` sorry): the hypothesis `hmono` is exactly the `MonicDense.mem_iff_mono` content
    on dense morphisms.  Hence the monic left-fraction skeleton is the wrong tool for §1.547's `A*`
    (which inverts these epic projections); the dual right-fraction calculus is required. -/
theorem pairDense_mono_epic_collapse [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞]
    (hmono : ∀ {X Y : PairObj 𝒞} (x : PairHom X Y), Nonempty (PairDense x) → @Mono (PairObj 𝒞) _ _ _ x)
    {X Y : PairObj 𝒞} {x : PairHom X Y} (dx : PairDense x) :
    @Mono (PairObj 𝒞) _ _ _ x ∧
      (∀ {Z : PairObj 𝒞} (a b : PairHom Y Z), x.comp a = x.comp b → a = b) :=
  ⟨hmono x ⟨dx⟩, fun a b h => pairDense_epi dx a b h⟩

end PairEq

end PairsCategory

/-! ## §1.547  The relative-capitalization statement and the points-everything payoff

  The rational category `A[denseMonos⁻¹]` is §1.547's `A*` (up to the equivalence with the
  directed union of product-slices, which §1.547 records as the *verification*, not the
  construction).  The §1.547 payoff is:

      `StepWellPointsStatement` — for every well-supported `A` of `S`, `loc A` is
      `WellPointed` in the rational category.

  The mathematical heart (§1.547, last paragraph): a proper subobject `B' ↪ loc A`
  pulls back to a proper subobject at some finite stage `A/(∏U)` with `A ∈ U`, where the
  slice carries the generic point `1 → loc A` (`sliceFactorPoint`/`listProdSliceAcquires
  EveryFactor`, RelativeCapitalization.lean) that the subobject misses — "AB' ↪ AB does
  not allow the generic point in A/B".  The generic-point ingredients are sorry-free; the
  residual is the descent of an arbitrary rational-category subobject to a finite stage and
  the missed-point extraction, isolated below. -/

section WellPointed
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [PullbacksTransferCovers 𝒞]

/-- **§1.547 — the generic point of factor `A` in the product-slice `A/(∏U)`.**  This is the
    point the §1.547 rational step adds for the well-supported target `A` reached from the
    base `∏U` by the projection `g : ∏U → A`: the over-arrow `1 → sliceEmbedObj (∏U) A` whose
    underlying arrow is `pair g id`.  Read off `sliceFactorPoint`/`listProdSliceAcquiresEvery
    Factor` (RelativeCapitalization.lean), which are sorry-free.  Restated here as the
    rational-category-level "global point of `loc A`": in the directed-union model of
    `A[𝒟⁻¹]`, the slice `A/(∏U)` IS the stage `A*|U`, its terminator `overTerm (∏U)` is the
    `1` of that stage, and this is a genuine point `1 → A` at that stage. -/
theorem slice_factor_point_acquired {P : 𝒞} (A : 𝒞) (g : P ⟶ A) :
    (sliceFactorPoint A g).f ≫ (sliceEmbedObj P A).hom = (overTerm P).hom :=
  sliceAcquiresFactorPoint A g

/-- **§1.547 core — `A/(∏U)` points every factor (the one-step payoff).**  For each factor
    `A = U.get k` of a finite set `U` of well-supported objects, the single product-slice
    `A/(∏U)` carries a global point `1 → sliceEmbedObj (∏U) A` (`sliceFactorPoint` along the
    projection `listProdProj U k`).  Iterated over `U`, one rung points all of `U` at once —
    the structural reason the §1.547 relative capitalization needs only ω iterations (each
    rational step `A ⊆ A*` points every well-supported object simultaneously).  Sorry-free;
    this is `listProdSliceAcquiresEveryFactor` re-exposed as the rational-step payoff. -/
theorem ratStep_points_every_factor (U : List 𝒞) (k : Fin U.length) :
    (sliceFactorPoint (U.get k) (listProdProj U k)).f
        ≫ (sliceEmbedObj (listProd U) (U.get k)).hom = (overTerm (listProd U)).hom :=
  listProdSliceAcquiresEveryFactor U k

/-- **§1.547 — `WellPointed` of the embedded factor (the full payoff, residual isolated).**
    In the product-slice `A/(∏U)` (with `A ∈ U` a well-supported factor), the embedded object
    `sliceEmbedObj (∏U) A` is `WellPointed`: every proper monic into it misses some global
    point.  The book's argument (§1.547 last paragraph): a proper subobject `m` corresponds
    to a proper subobject `B' ↪ A` downstairs (`A` well-supported, slice embedding faithful),
    and the generic point `sliceFactorPoint A (proj)` — which factors through `A` itself, not
    through any proper `B'` — is exactly the point `m` cannot lift ("AB' ↪ AB does not allow
    the generic point in A/B").

    Stated with the slice's genuine `HasTerminal` (`overHasTerminal (∏U)`) — NO `sorry` in
    the type, so the statement is the book's real `WellPointed`.  The residual is the
    descent of `m` to the downstairs proper subobject `B'` and the missed-point extraction;
    the generic-point ingredient is in hand (`ratStep_points_every_factor`). -/
theorem sliceEmbed_factor_wellPointed (U : List 𝒞)
    (hU : ∀ x ∈ U, WellSupported x) (k : Fin U.length) :
    @WellPointed (Over (listProd U)) _ (overHasTerminal (listProd U))
      (sliceEmbedObj (listProd U) (U.get k)) := by
  sorry

end WellPointed

end Freyd
