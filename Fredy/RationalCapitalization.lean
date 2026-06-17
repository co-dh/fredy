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

  Still R4 (not faked here): the full `HasPullbacks (PairObj 𝒞)` + `DenseClass (PairObj 𝒞)` to
  instantiate the R2 generic rational-category skeleton on `(Â, PairDense)` and get the localised
  category object `A*` + functor; and dense pullback-closure (needs `Â`'s own pullbacks).  The
  faithfulness OBLIGATION of that functor is already discharged by
  `pairLocalisation_faithful_criterion`.  No `ratCap` is asserted (its `stepFaithful` field is
  exactly this criterion; the remaining `CapStep` preservation fields are the R4 instantiation).

  ── INTEGRITY ──────────────────────────────────────────────────────────────────

  No `axiom`, no `: True`, no `sorry` on a false statement, no `sorry` in any STATEMENT/type.
  The SINGLE remaining `sorry` is the R2 residual `sliceEmbed_factor_wellPointed` (the §1.547
  subobject-descent); its STATEMENT is the book's genuine `WellPointed`, sharply documented as a
  precisely-located obstruction.  The protected types of `capData_exists`/`CapData`/`CapStep` are
  not touched by this file.  No fake `ratCap` is asserted.

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
      exact fractionEquiv_trans
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
    morphisms out of `A` to well-supported targets.  `targets` is `F°`. -/
structure PairObj (𝒞 : Type u) [Cat.{u} 𝒞] [HasTerminal 𝒞] where
  A : 𝒞
  F : List (Σ T : 𝒞, A ⟶ T)
  wsupp : ∀ p ∈ F, WellSupported p.1

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
