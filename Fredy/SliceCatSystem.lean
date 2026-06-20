import Fredy.Capitalization
import Fredy.RelativeCapitalization

/-! # §1.543 M4 — the index-agnostic slice `CatSystem` successor `nextStepOfOrdChain`

  This file factors Freyd's relative-capitalization successor `S ↦ S*` (§1.546/§1.547) out of the
  `ℕ`-enumeration it is currently pinned to (`nextStepOfEnum`, Capitalization.lean) and re-expresses
  it over an ARBITRARY directed index via `OrdChain D` (Inflation.lean).  The point of the exercise
  (the §1.543 "M4 slice CatSystem" endgame): the §1.547 successor must be cofinal over the
  well-supported objects of an UNCOUNTABLE carrier, so `ℕ` cannot index the chain — the construction
  must run over a well-ordering (a `Colim.Directed` from `Ordinal`/`WellFoundedLT`).  Everything the
  successor needs is ALREADY index-agnostic in the repo:

    * `ordChainSliceSystem O`        — the inner slice system over any directed index (Inflation.lean)
    * `ordChainSliceCoherent O`      — its on-the-nose `Coherent` (Inflation.lean)
    * `ordChainSlicePreRegular O`    — the colimit `S*` is pre-regular, GIVEN `hcanon` (Inflation.lean)
    * `ordChainCanonicalCover O`     — discharges `hcanon` from transition faithfulness/conservativity
    * `ordChainHfaith`/`ordChainHcons` — those, GIVEN every appended suffix product is well-supported
    * `ordChainHmono`/`ordChainHcovpres`/`ordChainStagePTC` — the canonical-cover bridge ingredients

  The ℕ specializations (`chain*` = `P.toOrdChain` instances) are exactly what `nextStepOfEnum` uses;
  here we lift the SAME assembly to the generic `OrdChain`.  Two genuinely new Sorry-free pieces:

    * `ordChainSlicePreRegularWS` — the generic `chainSlicePreRegularWS`: the inner colimit `S*` is
      pre-regular once every appended suffix product `∏(prefixSuffix (chain i) (chain j))` is
      well-supported.  Verbatim DRY generalization of `chainSlicePreRegularWS`.

    * `nextStepOfOrdChain` — the generic `nextStepOfEnum`: a `CapStep S` from any `OrdChain D O`, a
      designated initial index `i₀`, a bottom-stage embedding `E : BaseStageEmbed O i₀` (the §1.546
      faithful/Cartesian/mono-cover-preserving `S ↪ A i₀`, realized by `baseSlice*` when stage `i₀` is
      the base slice `Over []`), and the well-supported-suffix hypothesis.  The faithful pre-regular
      embedding `S → S*` is `E.base` followed by the colimit stage-`i₀` inclusion — index-agnostic,
      since `objIncl`/`stageIncl*` and the `ordChain*` package are all index-free.  The bottom-stage
      embedding is carried as input rather than hard-wiring stage `i₀` to `innerSliceObj []` (a generic
      `OrdChain` only knows `O.chain i₀ = []` propositionally, and transporting `baseSlice*` across that
      would re-type the whole stage).

  What this does NOT yet build (the precise remaining §1.543 blocker, stated honestly, no `Sorry`
  here): a CONCRETE cofinal `OrdChain D O` over a well-ordering of the well-supported objects (the
  transfinite cofinal chain, needing the mathlib `Ordinal`-backed `Colim.Directed` confined to the
  separate transfinite file), AND the `StepWellPoints` obligation — `WellPointed (st.step A)` for every
  well-supported `A`.  `WellPointed` (S1_52.lean) is the JOINTLY-COVERING property (every proper mono
  misses a point), strictly stronger than "the slice acquires a point" (`sliceAcquiresPoint`, which is
  all the current acquisition machinery proves); deriving it is §1.546's structural argument, the real
  M4 content beyond this successor.  Both are recorded as the two open inputs of `CofinalCapStep`. -/

namespace Freyd

open Colim

universe u

variable {𝒞 : Type u} [Cat.{u} 𝒞] [PreRegularCategory 𝒞]

-- The canonical `HasEqualizers 𝒞` of a pre-regular category (products + pullbacks ⟹ equalizers).
-- Used uniformly so the source equalizer instance matches the `CapStep.stepEqs` field on the nose
-- (which is stated against `products_pullbacks_implies_equalizers`), exactly as `nextStepOfEnum` does.
attribute [local instance] products_pullbacks_implies_equalizers

/-! ## The generic well-supported-suffix pre-regularity of the inner colimit

  `ordChainSlicePreRegularWS O hwsuf` is the verbatim DRY generalization of `chainSlicePreRegularWS`
  (Capitalization.lean) from the ℕ `PrefixChain` to an arbitrary `OrdChain D`.  The colimit `S* =
  (ordChainSliceSystem O).Obj` is pre-regular once every appended suffix product is well-supported:
  that single concrete book precondition discharges transition faithfulness (`ordChainHfaith`) and
  conservativity (`ordChainHcons`), which `ordChainCanonicalCover` consumes to produce `hcanon`,
  which `ordChainSlicePreRegular` consumes to produce the `PreRegularCategory`. -/

/-- **The generic well-supported-suffix `hcanon` discharge** — `chainCanonicalCoverWS` over any
    directed index.  `ordChainHfaith`/`ordChainHcons` need the appended suffix product well-supported;
    `hwsuf` supplies exactly that for every transition. -/
theorem ordChainCanonicalCoverWS {ι : Type u} {D : Directed ι} (O : OrdChain D 𝒞) [Nonempty ι]
    (hwsuf : ∀ {i j : ι} (_hij : D.le i j),
        WellSupported (listProd (𝒞 := 𝒞) (prefixSuffix (O.chain i) (O.chain j)))) :
    letI : Cat (ordChainSliceSystem O).Obj := colimitCat _ (ordChainSliceCoherent O)
    letI : HasPullbacks (ordChainSliceSystem O).Obj :=
      colimitHasPullbacks _ (ordChainSliceCoherent O)
        (ordChainHasTerminal O) (ordChainHtpres O) (ordChainHasProducts O)
        (ordChainHppres O) (ordChainHppresPair O)
        (ordChainHasEqualizers O) (ordChainHepres O) (ordChainHepresLift O)
    ∀ {X Y Z : (ordChainSliceSystem O).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
        Cover f → Cover (HasPullbacks.has f g).cone.π₂ :=
  ordChainCanonicalCover O
    (fun {_ _} hij {_ _} p q h => ordChainHfaith O hij (hwsuf hij) p q h)
    (fun {_ _} hij {_ _} φ hiso => ordChainHcons O hij (hwsuf hij) φ hiso)

/-- **The generic inner colimit `S*` is PRE-REGULAR** — `chainSlicePreRegularWS` over any directed
    index.  Reduces to the single book precondition `hwsuf` (every appended suffix well-supported),
    exactly as in the ℕ case.  This is the relative-capitalization successor `S → S*` at the level of
    pre-regular structure, transfinite-ready. -/
noncomputable def ordChainSlicePreRegularWS {ι : Type u} {D : Directed ι} (O : OrdChain D 𝒞)
    [Nonempty ι]
    (hwsuf : ∀ {i j : ι} (_hij : D.le i j),
        WellSupported (listProd (𝒞 := 𝒞) (prefixSuffix (O.chain i) (O.chain j)))) :
    @PreRegularCategory (ordChainSliceSystem O).Obj (colimitCat _ (ordChainSliceCoherent O)) :=
  ordChainSlicePreRegular O (ordChainCanonicalCoverWS O hwsuf)

/-! ## The generic relative-capitalization successor `nextStepOfOrdChain`

  `nextStepOfOrdChain O i₀ E hwsuf : CapStep S` is the verbatim DRY generalization of
  `nextStepOfEnum` (Capitalization.lean) from the ℕ `enumChain` to an arbitrary `OrdChain D O`.  The
  successor is the colimit `S* = (ordChainSliceSystem O).Obj`, pre-regular by `ordChainSlicePreRegularWS`,
  with the faithful embedding `S → S*` the bottom-stage embedding `E.base : S → A i₀` followed by the
  colimit stage-`i₀` inclusion.  The five preservation fields are the index-free composites
  (`E.base*` ∘ `objIncl_preserves*`), exactly as in `nextStepOfEnum`.

  Every ingredient is already index-agnostic in the repo (the `ordChain*` preservation package and the
  `objIncl*`/`stageIncl*`/`baseSlice*` lemmas, which take a `CatSystem ι D` over any `ι`/`D`), so the
  proof is the ℕ one with `chain* → ordChain*` and `i0 = ⟨0⟩` replaced by the supplied `i₀`, the
  bottom-stage embedding carried as the input `BaseStageEmbed O i₀` (see its doc-comment for why it is
  an input rather than the hard-wired `innerSliceObj []`). -/

variable [PullbacksTransferCovers 𝒞]

/-! ### The bottom-stage embedding package

  The §1.546/§1.547 successor needs `S` to embed, faithfully + Cartesian-ly + mono/cover-preservingly,
  into the INITIAL stage `(ordChainSliceSystem O).A i₀` of the chain.  For the concrete relative-
  capitalization chain this stage is the base slice `Over []` (the slice over the inflation terminal)
  and the embedding is `baseSliceObj` (Capitalization.lean), whose every required property is already
  proven (`baseSliceFaithful`/`baseSliceObjCartFunctor`/`baseSlice_preservesPullbacks`/
  `baseSlice_preservesCover`).  We abstract that data as `BaseStageEmbed O i₀` rather than hard-wire
  the stage type to `innerSliceObj []`: a generic `OrdChain` only knows `O.chain i₀ = []`
  *propositionally*, and transporting `baseSlice*` across that propositional equality would re-type the
  whole stage; carrying the embedding as input keeps the §1.546 "stage `i₀` is the base slice" fact
  exactly where it belongs (it is index/stage-specific, the one thing a concrete cofinal chain supplies)
  while the rest of the successor stays index-agnostic. -/

/-- **The bottom-stage embedding data** the generic successor consumes: a faithful, Cartesian,
    mono- and cover-preserving functor `base : S → (ordChainSliceSystem O).A i₀` into the chain's
    initial stage.  For the relative-capitalization chain `base = baseSliceObj` (Capitalization.lean)
    and every field is the corresponding `baseSlice*` fact.  Bundling it isolates the §1.546
    "stage `i₀` is the base slice" content. -/
structure BaseStageEmbed {ι : Type u} {D : Directed ι} (O : OrdChain D 𝒞) (i₀ : ι) where
  base : 𝒞 → (ordChainSliceSystem O).A i₀
  baseFun : @Functor 𝒞 _ ((ordChainSliceSystem O).A i₀) _ base
  baseFaithful : @Faithful 𝒞 _ ((ordChainSliceSystem O).A i₀) _ base baseFun
  /-- `base` preserves the terminal (`pres_terminal` of the §1.546 base CartesianFunctor). -/
  baseTerminal : @PreservesTerminal 𝒞 ((ordChainSliceSystem O).A i₀) _ _ base baseFun
    (PreRegularCategory.toHasTerminal) (ordChainHasTerminal O i₀)
  /-- `base` preserves binary products. -/
  baseProds : @PreservesBinaryProducts 𝒞 ((ordChainSliceSystem O).A i₀) _ _ base baseFun
    (PreRegularCategory.toHasBinaryProducts) (ordChainHasProducts O i₀)
  /-- `base` preserves equalizers (source `HasEqualizers 𝒞` the ambient instance). -/
  baseEqs : @PreservesEqualizers 𝒞 ((ordChainSliceSystem O).A i₀) _ _ base baseFun
    _ (ordChainHasEqualizers O i₀)
  /-- the EXISTENCE half of "`base one` is terminal": a map `X ⟶ base one` from every stage object
      (the `stepTerminalArrow` existence datum at the bottom stage). -/
  baseTerminalArrow : ∀ (X : (ordChainSliceSystem O).A i₀),
    @Cat.Hom _ ((ordChainSliceSystem O).catA i₀) X (base one)
  baseMono : ∀ {x y : 𝒞} (φ : x ⟶ y), Mono φ → Mono (baseFun.map φ)
  baseCover : ∀ {x y : 𝒞} (φ : x ⟶ y), Cover φ → Cover (baseFun.map φ)

set_option maxHeartbeats 1000000 in
/-- **The generic §1.546/§1.547 successor `S → S*` over an arbitrary directed index** —
    `nextStepOfEnum` lifted to any `OrdChain D O` with a bottom-stage embedding `E : BaseStageEmbed O i₀`
    and every appended suffix well-supported.  The successor is the inner colimit
    `S* = (ordChainSliceSystem O).Obj` (pre-regular by `ordChainSlicePreRegularWS`); the faithful
    pre-regular embedding `S → S*` is `E.base` followed by the colimit stage-`i₀` inclusion.  Sorry-free.
    The transfinite cofinal chain (`Ordinal`-indexed, separate file) plugs in by supplying `O`, `i₀`,
    `E` (the §1.546 base embedding at the bottom stage) and `hwsuf`. -/
noncomputable def nextStepOfOrdChain {ι : Type u} {D : Directed ι} (O : OrdChain D 𝒞)
    [Nonempty ι] (i₀ : ι) (E : BaseStageEmbed O i₀)
    (hwsuf : ∀ {i j : ι} (_hij : D.le i j),
        WellSupported (listProd (𝒞 := 𝒞) (prefixSuffix (O.chain i) (O.chain j)))) :
    CapStep 𝒞 := by
  letI : Cat (ordChainSliceSystem O).Obj := colimitCat _ (ordChainSliceCoherent O)
  letI := E.baseFun
  letI : HasTerminal ((ordChainSliceSystem O).A i₀) := ordChainHasTerminal O i₀
  letI : HasBinaryProducts ((ordChainSliceSystem O).A i₀) := ordChainHasProducts O i₀
  letI : HasEqualizers ((ordChainSliceSystem O).A i₀) := ordChainHasEqualizers O i₀
  letI hF0 : @Functor ((ordChainSliceSystem O).A i₀) _ (ordChainSliceSystem O).Obj _
      ((ordChainSliceSystem O).objIncl i₀) :=
    @stageInclFunctor.{u, u} ι D (ordChainSliceSystem O) (ordChainSliceCoherent O) i₀
  have hfaith0 : @Faithful ((ordChainSliceSystem O).A i₀) _ (ordChainSliceSystem O).Obj _
      ((ordChainSliceSystem O).objIncl i₀) hF0 :=
    @stageInclFaithful.{u, u} ι D (ordChainSliceSystem O) (ordChainSliceCoherent O)
      (fun {_ _} hij {_ _} p q h => ordChainHfaith O hij (hwsuf hij) p q h)
      (fun {_ _} hij {_ _} φ hiso => ordChainHcons O hij (hwsuf hij) φ hiso) i₀
  -- the COMPOSITE functor instance `S → S*`, bound so the `step*` field goals pick up THIS `Functor`
  -- (and its `Cat (ordChainSliceSystem O).Obj = instCat`) rather than re-synthesizing a fresh one
  -- with a non-matching `colimitCat` (mirrors `nextStepOfEnum`'s `hGF`).
  letI hGF : @Functor 𝒞 _ (ordChainSliceSystem O).Obj _
      ((ordChainSliceSystem O).objIncl i₀ ∘ E.base) :=
    compFunctor (F := E.base) (G := (ordChainSliceSystem O).objIncl i₀)
  exact
    { T := (ordChainSliceSystem O).Obj
      catT := colimitCat _ (ordChainSliceCoherent O)
      preT := ordChainSlicePreRegularWS (𝒞 := 𝒞) O hwsuf
      step := (ordChainSliceSystem O).objIncl i₀ ∘ E.base
      stepFun := compFunctor (F := E.base) (G := (ordChainSliceSystem O).objIncl i₀)
      stepFaithful := faithful_comp (F := E.base)
        (G := (ordChainSliceSystem O).objIncl i₀) E.baseFaithful hfaith0
      stepTerminal := by
        letI : HasTerminal (ordChainSliceSystem O).Obj :=
          colimitHasTerminal (ordChainSliceSystem O) (ordChainSliceCoherent O)
            (ordChainHasTerminal O) (ordChainHtpres O)
        intro X f g
        exact preservesTerminal_uniq_comp (F := E.base)
          (G := (ordChainSliceSystem O).objIncl i₀)
          E.baseTerminal
          (objIncl_preservesTerminal (ordChainSliceSystem O) (ordChainSliceCoherent O)
            (ordChainHasTerminal O) (ordChainHtpres O) i₀)
          (objIncl_preservesMono (ordChainSliceSystem O) (ordChainSliceCoherent O)
            (fun {i j} hij {x y} φ hφ => ordChainHmono O hij φ hφ) i₀) X f g
      stepTerminalArrow := by
        letI htCol : HasTerminal (ordChainSliceSystem O).Obj :=
          colimitHasTerminal (ordChainSliceSystem O) (ordChainSliceCoherent O)
            (ordChainHasTerminal O) (ordChainHtpres O)
        intro X
        -- stage arrow `g : (terminal i₀).one ⟶ E.base one` in stage `i₀`, supplied as the bottom-stage
        -- existence datum `E.baseTerminalArrow` (the §1.546 "base one receives a map from terminal").
        let g : @Cat.Hom _ ((ordChainSliceSystem O).catA i₀) (ordChainHasTerminal O i₀).one
            (E.base one) := E.baseTerminalArrow (ordChainHasTerminal O i₀).one
        have hEq : htCol.one = (ordChainSliceSystem O).objIncl i₀ (ordChainHasTerminal O i₀).one :=
          objIncl_terminal_eq.{u} (ordChainSliceSystem O) (ordChainSliceCoherent O)
            (ordChainHasTerminal O) (ordChainHtpres O)
            (Classical.choice (inferInstanceAs (Nonempty ι))) i₀
        exact castHom rfl hEq (htCol.trm X) ≫
          (@stageInclFunctor.{u, u} ι D (ordChainSliceSystem O) (ordChainSliceCoherent O) i₀).map g
      stepProds := by
        letI : HasBinaryProducts (ordChainSliceSystem O).Obj :=
          (ordChainSlicePreRegularWS (𝒞 := 𝒞) O hwsuf).toHasBinaryProducts
        apply preservesBinaryProducts_comp (F := E.base)
          (G := (ordChainSliceSystem O).objIncl i₀)
          E.baseProds
        exact objIncl_preservesBinaryProducts (ordChainSliceSystem O) (ordChainSliceCoherent O)
          (ordChainHasProducts O) (ordChainHppres O) (ordChainHppresPair O) i₀
      stepEqs := by
        letI heCol : HasEqualizers (ordChainSliceSystem O).Obj :=
          colimitHasEqualizers (ordChainSliceSystem O) (ordChainSliceCoherent O)
            (ordChainHasEqualizers O) (ordChainHepres O) (ordChainHepresLift O)
        have hcomp : PreservesEqualizers ((ordChainSliceSystem O).objIncl i₀ ∘ E.base) :=
          preservesEqualizers_comp (F := E.base)
            (G := (ordChainSliceSystem O).objIncl i₀)
            E.baseEqs
            (objIncl_preservesEqualizers (ordChainSliceSystem O) (ordChainSliceCoherent O)
              (ordChainHasEqualizers O) (ordChainHepres O) (ordChainHepresLift O) i₀)
        -- the field's target equalizer instance is the one DERIVED from `preT` (products+pullbacks of
        -- the pre-regular colimit), not the ambient one; supply it explicitly so `e₂` matches on the nose.
        letI preT := ordChainSlicePreRegularWS (𝒞 := 𝒞) O hwsuf
        exact @preservesEqualizers_target_irrel 𝒞 (ordChainSliceSystem O).Obj _ _
          ((ordChainSliceSystem O).objIncl i₀ ∘ E.base) hGF
          products_pullbacks_implies_equalizers heCol
          (@products_pullbacks_implies_equalizers (ordChainSliceSystem O).Obj _
            preT.toHasBinaryProducts preT.toHasPullbacks) hcomp
      stepMono := fun {x y} φ hφ =>
        objIncl_preservesMono (ordChainSliceSystem O) (ordChainSliceCoherent O)
          (fun {i j} hij {x y} ψ hψ => ordChainHmono O hij ψ hψ) i₀
          (E.baseMono φ hφ)
      stepCover := fun {x y} φ hφ =>
        objIncl_preservesCover (ordChainSliceSystem O) (ordChainSliceCoherent O)
          (fun {i j} hij {p q} a b h => ordChainHfaith O hij (hwsuf hij) a b h)
          (fun {i j} hij {x y} ψ hψ => ordChainHcovpres O hij ψ hψ) (i := i₀)
          (φ := E.baseFun.map φ) (E.baseCover φ hφ) }

end Freyd
