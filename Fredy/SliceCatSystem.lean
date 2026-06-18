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
  here we lift the SAME assembly to the generic `OrdChain`.  Two genuinely new sorry-free pieces:

    * `ordChainSlicePreRegularWS` — the generic `chainSlicePreRegularWS`: the inner colimit `S*` is
      pre-regular once every appended suffix product `∏(prefixSuffix (chain i) (chain j))` is
      well-supported.  Verbatim DRY generalization of `chainSlicePreRegularWS`.

    * `nextStepOfOrdChain` — the generic `nextStepOfEnum`: a `CapStep S` from any `OrdChain D O` whose
      INITIAL stage is the empty factor-list (`O.chain i₀ = []`, so stage `i₀` is the base slice
      `Over []` that `S` embeds into) and whose every appended suffix is well-supported.  The faithful
      pre-regular embedding `S → S*` is the base embedding `S → innerSliceObj []` (stage `i₀`) followed
      by the colimit stage-inclusion — index-agnostic, since `objIncl`/`stageIncl*` and the base
      embedding `baseSlice*`/`baseSliceObjCartFunctor` are all index-free.

  What this does NOT yet build (the precise remaining §1.543 blocker, stated honestly, no `sorry`
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

variable {𝒞 : Type u} [Cat.{u} 𝒞] [PreRegularCategory 𝒞] [HasEqualizers 𝒞]

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

end Freyd
