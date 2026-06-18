import Fredy.SliceEquivalence
import Fredy.SliceRegular

/-! # §1.543 E — transporting `PreRegularCategory` across an `EquivalenceFunctor`

  ## Goal and route

  The §1.547 endgame builds `PreRegular A*` from the directed union of the fixed-`U` slices
  `A*|U ≃ A/(∏U)` (each pre-regular by `overPreRegular`).  The just-committed
  `pairOnUToSlice_equivalence` (SliceEquivalence.lean) gives the FIBERWISE equivalence
  `Φ : PairOnU U → Over (listProd U)` (an `EquivalenceFunctor` — fully faithful + essentially
  surjective).  Before any colimit can be taken, each fiber `PairOnU U` must itself be shown
  pre-regular; the colimit machinery (`colimitPreRegular`) consumes the per-stage
  `HasTerminal`/`HasBinaryProducts`/`HasEqualizers`/`PullbacksTransferCovers`.

  This file builds the missing FIBERWISE ingredient: **`PreRegularCategory` transports backward
  across an `EquivalenceFunctor`**.  Given a fully-faithful, essentially-surjective `F : 𝒞 → 𝒟`
  with `𝒟` pre-regular, `𝒞` is pre-regular.  This is the standard "an equivalence creates finite
  limits" argument, done by hand on this repo's `Cat`:

    * `equivFunctor_reflects_iso`   — fully faithful ⟹ reflects isomorphisms.
    * `equivFunctor_hasTerminal`    — pull the terminal back through the representative image.
    * `equivFunctor_hasBinaryProducts` — products via fullness + faithfulness.
    * `equivFunctor_hasPullbacks`   — pullbacks via fullness + faithfulness.
    * `equivFunctor_reflects_cover` — fully faithful ⟹ reflects covers.
    * `equivFunctor_pullbacksTransferCovers` — covers transfer, transported.
    * `equivFunctor_preRegular`     — bundle the four into `PreRegularCategory 𝒞`.

  Applied to `pairOnUToSlice_equivalence` + `overPreRegular`, this yields
  `PreRegularCategory (PairOnU U)` for every `Nodup` list `U` of well-supported objects.

  ## What this does NOT yet build (the precise next blocker, stated honestly — no `sorry`)

  The directed COLIMIT of these pre-regular fibers via `colimitPreRegular` needs a `CatSystem`
  with ON-THE-NOSE functorial transitions (`F_refl`/`F_trans` definitional).  Over the subset
  lattice with `listProd` bases the natural transition is base-change `A/(∏V) → A/(∏U)`, which is
  only PSEUDO-functorial (`baseChangeObj (id) X ≅ X` but `≠ X`) — the documented `StrictBaseChange`
  wall (RelativeCapitalization.lean).  The equivalence does NOT dissolve that wall: it makes each
  FIBER pre-regular, but the directed-union transitions remain pseudo-functorial.  The only strict
  inner system in the repo (`ordChainSliceSystem`, Inflation.lean) is over the PREFIX order with
  suffix-concatenation transitions and base `(w : Infl 𝒞)`, not the subset lattice over `listProd`.
  So the remaining §1.543 blocker is exactly: a strictly-functorial `CatSystem` realizing the
  subset-lattice directed union (or a base-change strictification).  This file commits the fiberwise
  pre-regularity, which any such route requires. -/

namespace Freyd

universe u

variable {𝒞 : Type u} [Cat.{u} 𝒞] {𝒟 : Type u} [Cat.{u} 𝒟]

/-! ## Fully faithful reflects isomorphisms -/

/-- **A fully-faithful functor reflects isos.**  If `F.map f` is iso with inverse `h`, fullness
    gives `g` with `F.map g = h`; faithfulness turns the two `F`-image inverse equations into
    `f ≫ g = id` and `g ≫ f = id`. -/
theorem equivFunctor_reflects_iso {F : 𝒞 → 𝒟} [hF : Functor F]
    (emb : Embedding F) (full : Full F) {X Y : 𝒞} (f : X ⟶ Y)
    (hf : IsIso (hF.map f)) : IsIso f := by
  obtain ⟨h, hfh, hhf⟩ := hf
  obtain ⟨g, hg⟩ := full h
  refine ⟨g, ?_, ?_⟩
  · -- f ≫ g = id : both F-images equal id (F (f≫g) = F f ≫ F g = F f ≫ h = id)
    apply emb (f ≫ g) (Cat.id X)
    rw [hF.map_comp, hg, hF.map_id, hfh]
  · apply emb (g ≫ f) (Cat.id Y)
    rw [hF.map_comp, hg, hF.map_id, hhf]

end Freyd
