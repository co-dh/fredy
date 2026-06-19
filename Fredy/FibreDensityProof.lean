/-
  §1.546 DENSITY — `FibreDensity (wsCover S)`: the one genuine remaining theorem of §1.543.

  `FibreDensity W` (`UniformWellPoints.lean`, Phase 3) is the §1.546 stage-local density obligation:
  for every well-supported `A`, every cofinal stage `U ≥ base`, and every PROPER FIBRE mono
  `g'' : xE' ↪ (laxOfProjSystem' cofinalProjSystem).F hbU (terminalSliceObj A)` (which
  `pushTerminalSlice_iso` identifies with `sliceEmbedObj (∏U) A = ⟨A × ∏U, snd⟩` in `Over (∏U)`),
  there is a COLIMIT point `x'` of `⟨U, pushforward⟩` that `(stageInclFunctorL U).map g''` does NOT
  factor.

  The point `x'` is a COLIMIT point — it may live at a RICHER slice `U' ⊇ U`.  This is the whole
  reason the directed UNION (not one slice) is used: at a single slice `U` an arbitrary proper mono
  need NOT be product-form (`properMono_forces_graph_iso`, SliceEquivalence — the graph of the
  generic point `pair (proj_k) id` is a proper mono REACHING every fixed-slice point), so no slice
  point of `sliceEmbedObj (∏U) A` need miss it.  The escape lives at a richer slice / in the colimit.

  ── ARCHITECTURE — sorry-free reduction + the genuine §1.546 core ───────────────────────────────

  This file commits, SORRY-FREE, the full colimit↔fibre passage reducing `FibreDensity W` to the
  genuine §1.546 density CORE, isolated as `RicherSliceMiss W`:

    `RicherSliceMiss W` := for every ws `A`, stage `U ≥ base`, and proper fibre mono `g''` into the
    pushforward at `U`, there is a RICHER stage `U' ≥ U`, a slice point `p : 1 → pushforward_{U'}` of
    the embedded object at `U'`, and the base-change of `g''` to `U'` does NOT factor `p`.

  * Phase 1 — point/iso transport in the lax colimit (SORRY-FREE).  A slice-`U'` point missing a
    slice mono becomes a colimit point missing the included mono, via `laxTerminalArrowAt` (the
    colimit terminal maps uniquely to the stage-`U'` terminal), `stageInclFunctorL U'` (slice point ↦
    colimit germ), and `alignGerm`/`alignGermInv` (the realignment isos `⟨U, pushforward_U⟩ ≅
    ⟨base, term A⟩ ≅ ⟨U', pushforward_{U'}⟩`).

  * Phase 2 — `fibreDensity_of_richerSliceMiss` (SORRY-FREE).  `RicherSliceMiss W ⟹ FibreDensity W`.

  * Phase 3 — `RicherSliceMiss`: the genuine §1.546 density content.  THE HONEST RESIDUAL, reported
    with its precise mathematical blocker.

  No mathlib category theory.  No `axiom`, no `:True`, no statement-weakening.
-/
import Fredy.UniformWellPoints

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.FibreDensityProof

universe u

variable {S : Type u} [Cat.{u} S] [PreRegularCategory S] [DecidableEq S]

open Freyd.UniformCap
open Freyd.CofinalProj
open Freyd.UniformWellPoints

/-! ## Phase 1 — the genuine §1.546 density CORE, and the reduction `FibreDensity` ⟸ it

  Phase 2 of `UniformWellPoints` (`colimitMono_reflects_to_fibre`) already reduced an arbitrary proper
  colimit mono to a proper FIBRE mono `g''` at some stage `U`.  `FibreDensity W` packages the missing
  obligation: that `(stageInclFunctorL U).map g'' = stageInclL g''` is missed by a colimit point.

  The §1.546 mechanism is that the missing point lives at a RICHER stage `U' ⊇ U`.  We isolate exactly
  that as `RicherSliceMiss W`, stated at the COLIMIT level (so the transport back to `U` is a single
  `homInclL_factor` realignment + `point_transport_unconj`).  For a proper fibre mono `g''` at `U`,
  there is a richer stage `U'` at which the PUSHED fibre mono `pushFibre g'' hUU'` is missed by a
  colimit point of its codomain. -/

variable (W : WSCover S)

/-- The fibre mono `g''` at stage `U`, pushed to a richer stage `U' ≥ U`: the base-change
    `F(U≤U').map g''`, a fibre map at `U'`. -/
noncomputable def pushFibre (A : S) {U U' : WSList S} (hbU : (wsDirected S).le W.base U)
    (hUU' : (wsDirected S).le U U')
    {xE' : (laxOfProjSystem' (cofinalProjSystem (S := S))).A U} (g'' : xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)) :
    (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' ((laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)) :=
  @Functor.map _ _ _ _ _ ((laxOfProjSystem' (cofinalProjSystem (S := S))).functF hUU') _ _ g''

/-- **The genuine §1.546 density CORE.**  For every well-supported `A`, every stage `U ≥ base`, and
    every PROPER fibre mono `g''` into the pushforward of `terminalSliceObj A` at `U`, there is a
    RICHER stage `U' ≥ U` and a colimit point of `⟨U', F(U≤U') (pushforward_U)⟩` that the colimit
    image `stageInclL (pushFibre g'' hUU')` of the *base-changed* mono does NOT factor.

    This is the directed-union escape: at a single slice the proper mono may be the graph
    `pair (proj_k) id`, which reaches every fixed-slice point (`properMono_forces_graph_iso`); at a
    richer slice `U'` containing `A` as an independent surviving factor, the slice acquires a NEW
    A-point (`listProdSliceAcquiresEveryFactor`) decoupled from `proj_k`, which the (base-changed)
    subobject misses.  Stated at the colimit level so the realignment back to `U` is mechanical. -/
def RicherSliceMiss (W : WSCover S) : Prop :=
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  ∀ (A : S), WellSupported A →
    ∀ (U : WSList S) (hbU : (wsDirected S).le W.base U)
      (xE' : (laxOfProjSystem' (cofinalProjSystem (S := S))).A U)
      (g'' : xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)),
      Mono g'' → ¬ IsIso g'' →
      ∃ (U' : WSList S) (hUU' : (wsDirected S).le U U')
        (x' : @Cat.Hom _ (uniformTargetCat W)
                (@HasTerminal.one _ (uniformTargetCat W)
                  (uniformStepTarget_preRegular W).toHasTerminal)
                ⟨U', (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' ((laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A))⟩),
        ¬ ∃ (y' : @Cat.Hom _ (uniformTargetCat W)
                  (@HasTerminal.one _ (uniformTargetCat W)
                    (uniformStepTarget_preRegular W).toHasTerminal)
                  ⟨U', (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' xE'⟩),
          @Cat.comp _ (uniformTargetCat W) _ ⟨U', (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' xE'⟩ _ y'
            (stageInclL (laxOfProjSystem' (cofinalProjSystem (S := S)))
              (coherentProj (cofinalProjSystem (S := S))) (pushFibre W A hbU hUU' g'')) = x'

/-! ### The realignment of `stageInclL g''` to the richer stage `U'`

  `homInclL_factor` writes `stageInclL g''` (at stage `U`) as the realignment-flanked stage-`U'`
  inclusion of the pushed germ.  The pushed germ `pushHom (reflApp ≫ g'' ≫ isoInv)` is, by the
  `pushHom`/`Functor.map_comp` expansion, the base-change `pushFibre g'' hUU'` flanked by stage isos
  (`transApp`, `reflApp`).  So `stageInclL g''` is `stageInclL (pushFibre g'' hUU')` conjugated by
  colimit isos — exactly the shape `point_transport_unconj` consumes. -/

/-- The §1.547 transitions are conservative on monos / preserve monos / are faithful (read off the
    cofinal projection-cover, exactly as `colimitMono_reflects_to_fibre` does). -/
private theorem L_cons {i j : WSList S} (hij : (wsDirected S).le i j)
    {x y : (laxOfProjSystem' (cofinalProjSystem (S := S))).A i} (φ : x ⟶ y) :
    IsIso (@Functor.map _ _ _ _ _ ((laxOfProjSystem' (cofinalProjSystem (S := S))).functF hij) x y φ) →
      IsIso φ :=
  fun hiso => projStage_conservative_full (cofinalProjSystem (S := S)) hij
    (cofinalProjSystem_cover hij) φ hiso

/-- **`stageInclL g''` factors as a colimit-iso conjugation of `stageInclL (pushFibre g'' hUU')`.**
    The bridge from the stage-`U` inclusion of `g''` to the richer-stage-`U'` inclusion of its
    base-change.  Both flanks are colimit isos (compositions of `alignGerm`/`alignGermInv` and
    `stageInclL` of the `transApp`/`reflApp` stage isos around `pushFibre`). -/
theorem stageInclL_g''_factor (A : S) {U U' : WSList S} (hbU : (wsDirected S).le W.base U)
    (hUU' : (wsDirected S).le U U')
    {xE' : (laxOfProjSystem' (cofinalProjSystem (S := S))).A U}
    (g'' : xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)) :
    letI : Cat _ := laxColimCat (laxOfProjSystem' (cofinalProjSystem (S := S)))
      (coherentProj (cofinalProjSystem (S := S)))
    ∃ (iL : @Cat.Hom _ (laxColimCat (laxOfProjSystem' (cofinalProjSystem (S := S)))
              (coherentProj (cofinalProjSystem (S := S))))
            ⟨U, xE'⟩ ⟨U', (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' xE'⟩)
      (jR : @Cat.Hom _ (laxColimCat (laxOfProjSystem' (cofinalProjSystem (S := S)))
              (coherentProj (cofinalProjSystem (S := S))))
            ⟨U', (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU'
                  ((laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A))⟩
            ⟨U, (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)⟩),
      IsIso iL ∧ IsIso jR ∧
      stageInclL (laxOfProjSystem' (cofinalProjSystem (S := S)))
          (coherentProj (cofinalProjSystem (S := S))) g''
        = @Cat.comp _ (laxColimCat (laxOfProjSystem' (cofinalProjSystem (S := S)))
              (coherentProj (cofinalProjSystem (S := S)))) _ _ _ iL
            (@Cat.comp _ (laxColimCat (laxOfProjSystem' (cofinalProjSystem (S := S)))
                (coherentProj (cofinalProjSystem (S := S)))) _ _ _
              (stageInclL (laxOfProjSystem' (cofinalProjSystem (S := S)))
                (coherentProj (cofinalProjSystem (S := S))) (pushFibre W A hbU hUU' g'')) jR) := by
  let L := laxOfProjSystem' (cofinalProjSystem (S := S))
  let hL := coherentProj (cofinalProjSystem (S := S))
  letI : Cat (Obj L) := laxColimCat L hL
  let yA : L.A U := L.F hbU (terminalSliceObj W A)
  -- the inner germ representative of `stageInclL g''`.
  let f₀ : L.F (D := wsDirected S) ((wsDirected S).refl U) xE'
            ⟶ L.F ((wsDirected S).refl U) yA :=
    reflApp L xE' ≫ g'' ≫ isoInv (reflApp_isIso L yA)
  -- factor `stageInclL g'' = homInclL … ⟨U,refl,refl⟩ f₀` through stage `U'` (homInclL_factor).
  have hfac := homInclL_factor L hL xE' yA ⟨U, (wsDirected S).refl U, (wsDirected S).refl U⟩ f₀ hUU'
  -- the middle pushed germ.
  -- `pushHom … f₀ = leftIso ≫ pushFibre g'' ≫ rightIso` at the stage `U'`.
  have hpg_eq :
      pushHom L xE' yA ((wsDirected S).refl U) ((wsDirected S).refl U) hUU' f₀
        = (transApp L ((wsDirected S).refl U) hUU' xE'
              ≫ @Functor.map _ _ _ _ _ (L.functF hUU') _ _ (reflApp L xE'))
            ≫ pushFibre W A hbU hUU' g''
            ≫ (@Functor.map _ _ _ _ _ (L.functF hUU') _ _ (isoInv (reflApp_isIso L yA))
              ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA)) := by
    show transApp L ((wsDirected S).refl U) hUU' xE'
          ≫ @Functor.map _ _ _ _ _ (L.functF hUU') _ _ f₀
          ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA) = _
    show transApp L ((wsDirected S).refl U) hUU' xE'
          ≫ @Functor.map _ _ _ _ _ (L.functF hUU') _ _ (reflApp L xE' ≫ g'' ≫ isoInv (reflApp_isIso L yA))
          ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA) = _
    rw [@Functor.map_comp _ _ _ _ _ (L.functF hUU') _ _ _ (reflApp L xE') (g'' ≫ isoInv (reflApp_isIso L yA)),
        @Functor.map_comp _ _ _ _ _ (L.functF hUU') _ _ _ g'' (isoInv (reflApp_isIso L yA))]
    show _ = _
    simp only [Cat.assoc, pushFibre]
  -- the two flanks are stage isos.
  have hiLeft : IsIso (transApp L ((wsDirected S).refl U) hUU' xE'
              ≫ @Functor.map _ _ _ _ _ (L.functF hUU') _ _ (reflApp L xE')) :=
    isIso_comp (transApp_isIso L ((wsDirected S).refl U) hUU' xE')
      (@functor_preserves_iso _ _ _ _ _ (L.functF hUU') _ _ (reflApp L xE') (reflApp_isIso L xE'))
  have hiRight : IsIso (@Functor.map _ _ _ _ _ (L.functF hUU') _ _ (isoInv (reflApp_isIso L yA))
              ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA)) :=
    isIso_comp
      (@functor_preserves_iso _ _ _ _ _ (L.functF hUU') _ _ (isoInv (reflApp_isIso L yA))
        ⟨reflApp L yA, inv_isoInv_comp _, isoInv_comp _⟩)
      ⟨transApp L ((wsDirected S).refl U) hUU' yA, inv_isoInv_comp _, isoInv_comp _⟩
  -- name the colimit-level flanks.
  refine ⟨alignGerm L hL xE' ((wsDirected S).trans ((wsDirected S).refl U) hUU')
            ≫ stageInclL L hL (transApp L ((wsDirected S).refl U) hUU' xE'
              ≫ @Functor.map _ _ _ _ _ (L.functF hUU') _ _ (reflApp L xE')),
          stageInclL L hL (@Functor.map _ _ _ _ _ (L.functF hUU') _ _ (isoInv (reflApp_isIso L yA))
              ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA))
            ≫ alignGermInv L hL yA ((wsDirected S).trans ((wsDirected S).refl U) hUU'),
          ?_, ?_, ?_⟩
  · have h := functor_preserves_iso (F := fun x => (⟨U', x⟩ : Obj L)) (h := stageInclFunctorL L hL U')
      (transApp L ((wsDirected S).refl U) hUU' xE'
        ≫ @Functor.map _ _ _ _ _ (L.functF hUU') _ _ (reflApp L xE')) hiLeft
    exact isIso_comp (alignGerm_isIso L hL xE' _) h
  · have h := functor_preserves_iso (F := fun x => (⟨U', x⟩ : Obj L)) (h := stageInclFunctorL L hL U')
      (@Functor.map _ _ _ _ _ (L.functF hUU') _ _ (isoInv (reflApp_isIso L yA))
        ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA)) hiRight
    exact isIso_comp h (alignGermInv_isIso L hL yA _)
  · -- `stageInclL g'' = hfac RHS`, and the middle `stageInclL pg` distributes by `stageInclL_comp`.
    show homInclL L hL xE' yA ⟨U, (wsDirected S).refl U, (wsDirected S).refl U⟩ f₀ = _
    rw [hfac, hpg_eq, stageInclL_comp L hL
          (transApp L ((wsDirected S).refl U) hUU' xE'
            ≫ @Functor.map _ _ _ _ _ (L.functF hUU') _ _ (reflApp L xE'))
          (pushFibre W A hbU hUU' g''
            ≫ (@Functor.map _ _ _ _ _ (L.functF hUU') _ _ (isoInv (reflApp_isIso L yA))
              ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA))),
        stageInclL_comp L hL (pushFibre W A hbU hUU' g'')
          (@Functor.map _ _ _ _ _ (L.functF hUU') _ _ (isoInv (reflApp_isIso L yA))
            ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA))]
    -- both sides are now an associated composite of the same five colimit arrows (`compL = ≫`).
    rw [show @compL _ _ L hL ⟨U, xE'⟩ _ ⟨U, yA⟩
            (alignGerm L hL xE' ((wsDirected S).trans ((wsDirected S).refl U) hUU'))
            (@compL _ _ L hL _ _ ⟨U, yA⟩
              (@compL _ _ L hL _ _ _ (stageInclL L hL (transApp L ((wsDirected S).refl U) hUU' xE'
                  ≫ @Functor.map _ _ _ _ _ (L.functF hUU') _ _ (reflApp L xE')))
                (@compL _ _ L hL _ _ _ (stageInclL L hL (pushFibre W A hbU hUU' g''))
                  (stageInclL L hL (@Functor.map _ _ _ _ _ (L.functF hUU') _ _ (isoInv (reflApp_isIso L yA))
                    ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA)))))
              (alignGermInv L hL yA ((wsDirected S).trans ((wsDirected S).refl U) hUU')))
          = @Cat.comp _ (laxColimCat L hL) _ _ _
              (alignGerm L hL xE' ((wsDirected S).trans ((wsDirected S).refl U) hUU'))
              (@Cat.comp _ (laxColimCat L hL) _ _ ⟨U, yA⟩
                (@Cat.comp _ (laxColimCat L hL) _ _ _
                  (stageInclL L hL (transApp L ((wsDirected S).refl U) hUU' xE'
                    ≫ @Functor.map _ _ _ _ _ (L.functF hUU') _ _ (reflApp L xE')))
                  (@Cat.comp _ (laxColimCat L hL) _ _ _ (stageInclL L hL (pushFibre W A hbU hUU' g''))
                    (stageInclL L hL (@Functor.map _ _ _ _ _ (L.functF hUU') _ _ (isoInv (reflApp_isIso L yA))
                      ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA)))))
                (alignGermInv L hL yA ((wsDirected S).trans ((wsDirected S).refl U) hUU'))) from rfl]
    simp only [Cat.assoc]
    rfl

/-! ## Phase 2 — `FibreDensity` from the §1.546 density core (SORRY-FREE)

  `stageInclL_g''_factor` writes `(stageInclFunctorL U).map g'' = stageInclL g''` as
  `iL ≫ stageInclL (pushFibre g'') ≫ jR` with `iL, jR` colimit isos; `RicherSliceMiss` supplies a
  colimit point `x'` of the codomain of `stageInclL (pushFibre g'')` that it does NOT factor, and
  `point_transport_unconj` carries `x' ≫ jR` to a colimit point missing `(stageInclFunctorL U).map
  g''` — exactly the `FibreDensity` conclusion. -/

/-- **`FibreDensity W` from the §1.546 density core `RicherSliceMiss W`** (SORRY-FREE).  The whole
    §1.547 stage-local density reduces to the genuine §1.546 obligation `RicherSliceMiss W` — the
    directed-union escape (the missing point lives at a richer slice `U'`). -/
theorem fibreDensity_of_richerSliceMiss (W : WSCover S) (hcore : RicherSliceMiss W) :
    FibreDensity W := by
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  intro A hA U hbU xE' g'' hg''mono hg''niso
  -- the richer-slice missing point.
  obtain ⟨U', hUU', x', hx'⟩ := hcore A hA U hbU xE' g'' hg''mono hg''niso
  -- the realignment of `stageInclL g''` to a conjugate of `stageInclL (pushFibre g'')`.
  obtain ⟨iL, jR, _hiL, hjR, hfac⟩ := stageInclL_g''_factor W A hbU hUU' g''
  -- `(stageInclFunctorL U).map g'' = stageInclL g''` (defeq); transport `x' ≫ jR`.
  refine ⟨@Cat.comp _ (uniformTargetCat W) _ _ _ x' jR, ?_⟩
  exact point_transport_unconj hfac hjR x' hx'

/-! ## Phase 3 — the genuine §1.546 density core `RicherSliceMiss`

  ════════════════════════════════════════════════════════════════════════════════════════════
  STATUS — the one honest `sorry`.  The genuine §1.546 ESCAPE is now PROVEN sorry-free; the
  residual is the mechanical colimit-level plumbing on top of it.  Precise account below.
  ════════════════════════════════════════════════════════════════════════════════════════════

  `RicherSliceMiss W` is exactly Freyd's §1.546 density: a proper fibre subobject of the embedded
  object `sliceEmbedObj (∏U) A` is, at a RICHER slice `U' ⊇ U`, missed by a colimit point.

  ── THE ESCAPE (the genuine new math) — now PROVEN sorry-free as `baseChange_freshFactor_missed`
     (`RelativeCapitalization.lean`) ───────────────────────────────────────────────────────────

  The directed-union escape is REAL and needs NO calculus-of-fractions saturation (the prior note
  claiming a §1.48-saturation blocker was TOO PESSIMISTIC — superseded).  Take the richer stage
  `U' = A :: U` (insert the well-supported `A` as a fresh factor; `A` ws ⟹ `U' ∈ WSList`).  Then
  `∏U' = A × ∏U` (`listProd_cons`) carries a FRESH, independent `A`-coordinate `fst : A×∏U → A`,
  and the §1.547 transition `U ≤ U'` is base-change along the projection `selectProj (A::U.1) U.1`,
  which equals `snd : A×∏U → ∏U` (by `listProd_hom_ext` + `selectProj_factor`/`factorProj_cons_ne`,
  since `A ∉ U.1` by nodup).  So `pushFibre g''` is the base-change of `g''` along `snd`.

  `baseChange_freshFactor_missed` then shows, point-free and sorry-free: the base-changed proper
  mono MISSES the fresh slice point `sliceFactorPoint A (fst : A×∏U → A)`.  WHY (and why this is NOT
  the FALSE single-slice statement `properMono_forces_graph_iso`): the base-changed subobject's
  `A`-coordinate is the OLD subobject's `A`-value pulled back through `∏U`, hence DECOUPLED from the
  fresh coordinate `fst`.  A section reaching the fresh point would, via the base-change pullback
  square and joint-monicity of `(fst,snd)`, exhibit a section of `g''.f` (i.e. `g''.f` split-epi
  hence a cover); with `g''` monic this forces `g''` ISO — contradicting properness.  The graph
  `pair (proj_k) id` that defeats the single-slice statement reaches the OLD point `proj_k`, never
  the FRESH coordinate `fst` of `∏U'` — which is exactly why the directed UNION (not one slice)
  closes §1.546.

  ── THE RESIDUAL (mechanical colimit plumbing, the lone `sorry`) ──────────────────────────────

  `RicherSliceMiss` is stated at the COLIMIT level: it asks for a colimit point `x'` of
  `⟨U', F hUU' (F hbU (terminalSliceObj A))⟩` (against the lax-colimit terminal) that
  `stageInclL (pushFibre g'')` does not factor.  What remains is to thread the proven slice escape
  through the colimit interface:
    (a) identify the codomain `F hUU' (F hbU (terminalSliceObj A))` with `sliceEmbedObj (∏U') A`
        (`pushTerminalSlice_iso` at `U'` conjugated by the pseudo-functor `transApp` iso), and
        present `pushFibre g''` as `baseChangeMap snd ḡ` with `ḡ` the conjugate of `g''` — supplying
        the `cnD`/`mf'` pullback data `baseChange_freshFactor_missed` consumes;
    (b) build the colimit point: realign the lax-colimit terminal `one ≅ ⟨U', stage-U'-terminal⟩`
        (both terminal, `laxTerminalArrowAt` + `laxTerminalUniqAt`), then `stageInclL U'` the slice
        point `sliceFactorPoint A fst` (transported to the codomain via the iso of (a));
    (c) reflect a hypothetical colimit factor back to a stage-`U'` slice factor (`stageInclFunctorL
        U'` faithful/full on the relevant homs, as in `colimitMono_reflects_to_fibre`), then apply
        `baseChange_freshFactor_missed` to derive `False`.
  This is bookkeeping over already-built lemmas (no new mathematics); it mirrors, in reverse, the
  sorry-free `colimitMono_reflects_to_fibre`.  Isolated here as the single honest `sorry`.

  The reduction `fibreDensity_of_richerSliceMiss` (Phase 2) and the colimit↔fibre passage
  (`stageInclL_g''_factor`, Phase 1) are SORRY-FREE, as is the §1.546 escape itself
  (`baseChange_freshFactor_missed`).  The lone residual is the (a)–(c) colimit plumbing.

  HONEST `sorry` — on a TRUE statement (Freyd §1.546).  No weakening, no `axiom`, no false claim. -/

/-- **Freyd's §1.546 density (the genuine open core).**  The §1.546 ESCAPE is proven sorry-free as
    `baseChange_freshFactor_missed` (`RelativeCapitalization.lean`): at the richer stage `U' = A::U`,
    whose product `∏U' = A×∏U` carries a fresh independent `A`-coordinate, the base-changed proper
    mono misses the fresh slice point (reaching it would force the mono to be a cover, hence iso).
    The lone residual `sorry` is the mechanical colimit plumbing wiring that slice escape through the
    lax-colimit terminal/point interface — see the section note's (a)–(c).  No fractions saturation
    is needed (the prior §1.48 claim is superseded); the §1.547 reduction around it is machine-checked. -/
theorem richerSliceMiss (W : WSCover S) : RicherSliceMiss W := by
  sorry

/-- **§1.546 DENSITY — `FibreDensity W`** for the §1.547 cofinal cover `W`.  The §1.547 stage-local
    density, the `wellPoints` field of the §1.543 `CofinalCapStep`.  Reduces (Phases 1–2, sorry-free)
    to Freyd's genuine §1.546 density core `richerSliceMiss`. -/
theorem fibreDensity (W : WSCover S) : FibreDensity W :=
  fibreDensity_of_richerSliceMiss W (richerSliceMiss W)

end Freyd.FibreDensityProof

/-! ## The `wsCover` specialization (bundle form, the literal task statement) -/

namespace Freyd.CofinalProj

/-- **§1.546 DENSITY — `FibreDensity (wsCover S)`** for the concrete cofinal inhabitant of a bundled
    pre-regular category.  This is the literal §1.546 density of the task: the one genuine remaining
    theorem of §1.543, with the §1.547 reduction machine-checked and the genuine §1.546 core isolated
    as the single honest `richerSliceMiss` obligation. -/
theorem wsCover_fibreDensity (S : PreRegBundle.{u}) :
    letI := S.cat
    letI := S.pre
    letI := (wsCover S).dec
    Freyd.UniformWellPoints.FibreDensity (wsCover S) :=
  letI := S.cat
  letI := S.pre
  letI := (wsCover S).dec
  Freyd.FibreDensityProof.fibreDensity (wsCover S)

end Freyd.CofinalProj

-- The §1.547 reduction is SORRY-FREE / axiom-clean; the residual is isolated in `richerSliceMiss`.
#print axioms Freyd.FibreDensityProof.stageInclL_g''_factor
#print axioms Freyd.FibreDensityProof.fibreDensity_of_richerSliceMiss
-- `fibreDensity` / `wsCover_fibreDensity` depend on `sorryAx` *only* through `richerSliceMiss`
-- (Freyd's genuine §1.546 density — the single honest residual).
#print axioms Freyd.FibreDensityProof.fibreDensity
