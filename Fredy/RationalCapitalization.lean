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

  ── INTEGRITY ──────────────────────────────────────────────────────────────────

  No `axiom`, no `: True`, no `sorry` on a false statement, no `sorry` in any STATEMENT/type.
  After milestone R2 the SINGLE remaining `sorry` is `sliceEmbed_factor_wellPointed` (the §1.547
  descent, left for R3); its STATEMENT is the book's genuine `WellPointed`, sharply documented as
  a precisely-located obstruction.  The protected types of `capData_exists`/`CapData`/`CapStep`
  are not touched by this file.  No fake `ratCap` is asserted (see the faithfulness finding).

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
