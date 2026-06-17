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
    * `ratComp`              — composition on equivalence classes; the `Quotient.lift₂`
                                WELL-DEFINEDNESS (independence of names + pullback choice,
                                §1.48) is the one isolated `sorry` here — a multi-pullback
                                roof chase, stated on the TRUE goal.
    * `ratStep_points_every_factor` / `slice_factor_point_acquired` — SORRY-FREE.  The §1.547
                                per-step PAYOFF: the product-slice `A/(∏U)` carries a global
                                point of every factor (re-exposed `listProdSliceAcquiresEvery
                                Factor`).
    * `sliceEmbed_factor_wellPointed` — the §1.547 well-pointedness CORE, stated with the
                                slice's genuine `HasTerminal` (overHasTerminal) — NO sorry in
                                the type, so it is the book's real `WellPointed`.  The descent
                                of an arbitrary subobject to the downstairs proper `B'` and the
                                missed-point extraction is the isolated `sorry`.

  ── INTEGRITY ──────────────────────────────────────────────────────────────────

  No `axiom`, no `: True`, no `sorry` on a false statement, no `sorry` in any STATEMENT/type.
  The two remaining `sorry`s (`ratComp` well-definedness; `sliceEmbed_factor_wellPointed`
  descent) each sit inside a theorem whose STATEMENT is the book's genuine statement, sharply
  documented as a precisely-located obstruction.  The protected types of
  `capData_exists`/`CapData`/`CapStep` are not touched by this file.

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

section RatHom
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- **Transitivity of `FractionEquiv` for the all-monics dense class (`denseMonos`).**  Given
    roofs `R : f₁ ≈ f₂` (legs `r₁,r₂`) and `S : f₂ ≈ f₃` (legs `s₂,s₃`), form the pullback `P`
    of `(r₂, s₂)` over `f₂.apex`.  Its two legs compose with `r₁`/`s₃` to give a roof
    `f₁ ≈ f₃`.  The declared-dense leg `(P.π₁ ≫ r₁) ≫ f₁.denom` is MONIC: `r₁` is monic
    (left-factor of the monic `r₁ ≫ f₁.denom`, `mono_of_comp_mono`); `s₂` is monic likewise;
    `P.π₁` is the pullback of the monic `s₂` along `r₂`, hence monic (`mono_pullback`); and
    `f₁.denom` is monic.  A composite of monics is monic — closing what for a *general* dense
    class would be the Ore roof axiom, but for `denseMonos` is just `mono` closure.  Sorry-free
    over `denseMonos 𝒞`. -/
theorem fractionEquiv_trans {A B : 𝒞} {f₁ f₂ f₃ : Fraction (denseMonos 𝒞) A B}
    (h₁₂ : FractionEquiv f₁ f₂) (h₂₃ : FractionEquiv f₂ f₃) : FractionEquiv f₁ f₃ := by
  obtain ⟨R, r₁, r₂, hRd, hRden, hRnum⟩ := h₁₂
  obtain ⟨S, s₂, s₃, hSd, hSden, hSnum⟩ := h₂₃
  -- pullback of the two middle legs `r₂ : R → f₂.apex` and `s₂ : S → f₂.apex`
  let P := (HasPullbacks.has r₂ s₂).cone
  refine ⟨P.pt, P.π₁ ≫ r₁, P.π₂ ≫ s₃, ?_, ?_, ?_⟩
  · -- composite denominator `(P.π₁ ≫ r₁) ≫ f₁.denom` monic.
    -- `hRd : Mono (r₁ ≫ f₁.denom)` ⟹ `r₁` monic; `hSd : Mono (s₂ ≫ f₂.denom)` ⟹ `s₂` monic;
    -- `P.π₁` = pullback of monic `s₂` along `r₂` ⟹ monic; `f₁.denom` monic.
    have hr₁ : Mono r₁ := mono_of_comp_mono hRd
    have hs₂ : Mono s₂ := mono_of_comp_mono hSd
    have hP₁ : Mono P.π₁ := mono_pullback r₂ s₂ hs₂ (HasPullbacks.has r₂ s₂)
    show Mono ((P.π₁ ≫ r₁) ≫ f₁.denom)
    exact mono_comp' _ _ (mono_comp' _ _ hP₁ hr₁) f₁.denom_dense
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
    fractionEquiv_trans⟩

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

/-- **Composition in `A[𝒟⁻¹]`** (on equivalence classes), by `compFraction`.

    WELL-DEFINEDNESS OBSTRUCTION (documented, real §1.48 content): `Quotient.lift₂`
    requires `compFraction` to respect `FractionEquiv` in BOTH arguments and to be
    independent of the pullback choice.  Replacing `f` by an equivalent `f'` (roof `r`)
    re-bases the pullback `Q` along `r`; the resulting composite spans share the roof
    pulled back over the new apex, but exhibiting that common roof — and that its declared
    denominator stays dense — is precisely Freyd's "the named morphism is independent of
    the choice of names for `A → B` and `B → C`, and of the choice of pullback" (§1.48).
    This is a multi-pullback diagram chase; it is the substantive remaining construction,
    carried here as a `sorry` inside the TRUE statement (the composite is well-defined). -/
def ratComp {A B C : 𝒞} (m : RatHom (𝒞 := 𝒞) A B)
    (n : RatHom (𝒞 := 𝒞) B C) : RatHom (𝒞 := 𝒞) A C :=
  Quotient.lift₂ (fun f g => Quotient.mk _ (compFraction (denseMonos 𝒞) f g))
    (by
      -- the binary congruence: `f ≈ f'`, `g ≈ g'` ⇒ `compFraction f g ≈ compFraction f' g'`
      intro f g f' g' hf hg
      apply Quotient.sound
      sorry)
    m n

end Comp

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
