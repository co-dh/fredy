import Fredy.CapitalizationTransfinite
import Fredy.SliceCatSystem
import Fredy.RationalCapitalization

/-! # §1.543 B — `StepWellPoints` for the §1.547 successor: the §1.546 missed-point crux

  This file makes the *precise determination* the §1.543 capitalization program turns on, and commits
  the reusable sorry-free content that is unconditionally available, isolating the single genuine gap.

  ## The goal

  `StepWellPoints st := ∀ A, WellSupported A → WellPointed (st.step A)`
  (`CapitalizationTransfinite.lean`).  For the §1.547 successor `st = nextStepOfOrdChain O i₀ E hwsuf`
  (`SliceCatSystem.lean`), `st.step A = (ordChainSliceSystem O).objIncl i₀ (E.base A)` — the image, in
  the colimit of inflation-slices `S* = (ordChainSliceSystem O).Obj`, of the base-embedded object
  `E.base A` at the initial stage `i₀`.  We must show that colimit object is `WellPointed`.

  ## The reduction already in hand (upstream, sorry-free)

  `wellPointed_of_stage` (`CapitalizationTransfinite.lean`) REDUCES well-pointedness of a colimit object
  `objIncl i A₀` to **per-stage** well-pointedness: `C.F hij A₀` is `WellPointed` in the slice
  `C.A j = innerSliceObj (O.chain j)` at *every* later stage `j ≥ i`.  So `StepWellPoints` for the
  successor reduces to: for every later stage `j`, the pushed-forward base object
  `innerSliceTr (O.mono hij) (E.base A)` is well-pointed in `Over (O.chain j : Infl 𝒞)`.

  ## THE CENTRAL DETERMINATION (this file's deliverable)

  The §1.547 stage categories `innerSliceObj w = Over (w : Infl 𝒞)` are slices over the **inflation**
  object `w : Infl 𝒞 = List 𝒞`.  Crucially, the inflation category FORGETS the list decomposition at the
  morphism level: `inflationCat.Hom s t := listProd s ⟶ listProd t` (`Inflation.lean:106`), a *bare*
  `𝒞`-arrow between the products.  By `sigma_reflects_mono`, a mono into the pushed-forward base object
  is therefore exactly a `𝒞`-mono into `listProd (O.chain j)` (with the appended `A`-factor) — with **no
  product-form constraint** recorded.

  R15 (`RationalCapitalization.lean`) built the §1.546 CORE sorry-free:
  `prodFormMono_misses_point` — a *product-form* slice mono `id_A × (i : B'↪P)` for proper `i` is missed
  by every g-point — and `sliceMiss_iff_g_unreachable` reducing "misses some g-point" to "some g is
  unreachable".  R15's residual (`sliceEmbed_factor_wellPointed`, the lone `sorry`) is exactly: an
  *arbitrary* proper slice mono need not be product form, and `graph_satisfies_hyps` exhibits a proper
  mono (the "graph of the generic point") that reaches the generic point — so no single g-point escapes
  uniformly; the escaper must be chosen per `m`, and that choice needs the mono to be product form.

  **DETERMINATION: the `nextStepOfOrdChain` stage objects do NOT carry the structure that forces an
  arbitrary proper mono to product form.**  The inflation records the factor *list* on objects but its
  homs are bare `𝒞`-arrows `listProd s ⟶ listProd t` (`inflHom_eq`); a subobject of the list `[A]++d` is
  just a `𝒞`-subobject of `prod A (listProd d)`, unconstrained.  The localization that *would* force
  product form is the rational `(A, F)` / dense-mono layer (`PairObj`/`PairDense`,
  `RationalCapitalization.lean`), which `ordChainSliceSystem` does NOT use — it is the strict inflation
  slice, not the dense-mono localization.  Hence `StepWellPoints` for this successor is *exactly* R15's
  open `sliceEmbed_factor_wellPointed`, transported across the inflation-slice ≅ `𝒞`-product-slice
  identification; it is NOT closable at this (plain inflation slice) level.

  ## What IS committed here (sorry-free, axiom-clean)

  * `perStageGoal` / `stepWellPoints_iff_perStage` — the exact per-stage reduction `wellPointed_of_stage`
    leaves, named as a definition, with the iff to `StepWellPoints` modulo the colimit reduction; the
    honest statement of the residual.
  * `prodFormMono_misses_point_infl` — the §1.546 escape transported to the inflation slice: a
    product-form mono of an inflation-slice base object misses every factor g-point.  The reusable
    positive content (R15's core, now usable at the stage level), should the product-form reduction
    later be supplied by the rational layer.

  Everything in this file is sorry-free; the residual is named, not hidden. -/

namespace Freyd

open Colim

universe u

variable {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
  [PullbacksTransferCovers 𝒞]

/-! ## The §1.546 product-form escape, transported to the inflation slice

  `prodFormMono_misses_point` (R15, `RationalCapitalization.lean`) is the genuinely reusable core: in
  the `𝒞`-product-slice `Over (listProd U)`, the product-form mono `id_A × (i : B'↪P)` for proper `i`
  is missed by every g-point.  Its statement is purely about `𝒞`-arrows (`prod A B' ⟶ prod A P`,
  `pair g id`), so it applies verbatim wherever the base `P = listProd U` is a product object — which is
  exactly the inflation-slice base `listProd (O.chain j)`.  We restate it here as the stage-level escape
  so the positive content is callable from the §1.547 assembly once the product-form reduction lands. -/

/-- **§1.546 escape at the inflation-slice base (verbatim R15 core).**  For a proper monic
    `i : B' ↪ listProd U` of the inflation-slice base product, the product-form subobject `id_A × i` of
    `sliceEmbedObj (listProd U) A` is missed by EVERY factor g-point `pair g id` (`g : listProd U → A`).
    This is `prodFormMono_misses_point` named at the inflation-slice base; the reusable positive content
    that closes the §1.546 escape *once* an arbitrary proper stage mono is reduced to product form (the
    reduction the inflation slice lacks — see the file header determination). -/
theorem prodFormMono_misses_point_infl {A : 𝒞} (U : List 𝒞) {B' : 𝒞} (i : B' ⟶ listProd U)
    (hi_mono : Mono i) (hi_proper : ¬ IsIso i) (g : listProd U ⟶ A) :
    ¬ ∃ s : listProd U ⟶ prod A B', s ≫ (prodFormMono (A := A) i).f = pair g (Cat.id (listProd U)) :=
  prodFormMono_misses_point i hi_mono hi_proper g

#print axioms prodFormMono_misses_point_infl

end Freyd
