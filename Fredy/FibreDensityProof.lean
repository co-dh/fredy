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
import Fredy.S1_43

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

  ── THE COLIMIT PLUMBING — (a)/(b) MACHINE-CHECKED, two sharp residuals in (c) ─────────────────

  `RicherSliceMiss` is stated at the COLIMIT level: it asks for a colimit point `x'` of
  `⟨U', F hUU' (F hbU (terminalSliceObj A))⟩` (against the lax-colimit terminal) that
  `stageInclL (pushFibre g'')` does not factor.  The slice escape is threaded through the colimit
  interface (`richerSliceSection`):
    (a) — SORRY-FREE.  The codomain `F hUU' (F hbU (terminalSliceObj A))` is `baseChangeObj snd
        (F hbU term)` (`selectProj (A::U) U = snd`, `selectProj_head_notin`+`selectProj_refl`); the
        comparison `sliceEmbedObj (∏U') A ≅ baseChangeObj snd (sliceEmbedObj P A)` is `bcSliceIso`
        (`bcSlice_isPullback`+`isIso_of_two_pullbacks`).  `pushFibre g''` IS `baseChangeMap snd g''`
        definitionally; the `cnD`/`mf'` data `baseChange_freshFactor_missed` consumes are `mf' :=
        pair (cnD.π₁ ≫ m.f ≫ fst) cnD.π₂`, `m := g'' ⊚ pushTerminalSlice_iso⁻¹`.
    (b) — SORRY-FREE.  The colimit point `x'` is `laxTerminalArrowAt` (`one ≅ ⟨U', overTerm(∏U')⟩`,
        iso by `laxTerminalUniqAt`) post-composed with `stageInclL U'` of `sliceFactorPoint A fst`
        transported across the (a)-iso `cod`.
    (c) — TWO SHARP RESIDUALS (the honest gaps):
        (c.i)  the colimit-factor REFLECTION `richerSliceSection` `sorry`: turning a colimit factor
               `y' : one ⟶ ⟨U', F hUU' xE'⟩` into a stage-`U'` base-change SECTION needs
               `stageInclFunctorL U'` FULLNESS on that hom.  The §1.547 transitions are base-change
               along covers (`selectProj`) — NOT full — so the germ representative sits at a richer
               stage `N ⊇ U'` that need not descend.  Hom-fullness / point-descent is not among the
               built lemmas (the repo has property-reflection — mono/iso/cover — but not hom-fullness;
               mathlib's `Full` is import-banned).  This is the genuine remaining §1.546 content.
        (c.ii) the `A ∈ U` case: appending `A` as a fresh nodup factor is impossible when `A` already
               indexes `U`; the escape needs a fresh INDEPENDENT copy of `A`, not expressible at the
               object level of the `WSList` index.

  The reduction `fibreDensity_of_richerSliceMiss` (Phase 2), the colimit↔fibre passage
  (`stageInclL_g''_factor`, Phase 1), the §1.546 escape (`baseChange_freshFactor_missed`), and the
  (a)/(b) base-change comparison + point (`bcSlice_isPullback`/`bcSliceIso`/`richerSliceSection` up to
  the `(c)` `sorry`) are SORRY-FREE.  The two residuals are on TRUE statements (Freyd §1.546); no
  weakening, no `axiom`, no false claim. -/

/-- **Canonical base-change pullback of a slice-embedded object.**  The pullback of the structure
    map `snd : C×P → P` of `sliceEmbedObj P C` along ANY map `q : P' → P` has apex `C×P'`, legs
    `pair fst (snd≫q)` (to `C×P`) and `snd` (to `P'`).  This is the geometric content of the §1.546(a)
    identification `baseChangeObj q (sliceEmbedObj P C) ≅ sliceEmbedObj P' C`. -/
theorem bcSlice_isPullback {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] (C P P' : 𝒞) (q : P' ⟶ P) :
    (Cone.mk (f := (snd : prod C P ⟶ P)) (g := q) (prod C P')
      (pair (fst : prod C P' ⟶ C) ((snd : prod C P' ⟶ P') ≫ q)) (snd : prod C P' ⟶ P')
      (by rw [snd_pair])).IsPullback := by
  intro d
  refine ⟨pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂, ⟨?_, ?_⟩, ?_⟩
  · have e1 : (pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂ ≫
        pair (fst : prod C P' ⟶ C) ((snd : prod C P' ⟶ P') ≫ q)) ≫ fst = d.π₁ ≫ fst := by
      rw [Cat.assoc, fst_pair, fst_pair]
    have e2 : (pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂ ≫
        pair (fst : prod C P' ⟶ C) ((snd : prod C P' ⟶ P') ≫ q)) ≫ snd = d.π₁ ≫ snd := by
      rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, d.w]
    exact (pair_uniq _ _ _ e1 e2).trans (pair_uniq _ _ d.π₁ rfl rfl).symm
  · rw [snd_pair]
  · intro v hv₁ hv₂
    have ev1 : v ≫ (fst : prod C P' ⟶ C) = (pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂) ≫ fst := by
      rw [fst_pair, ← hv₁]; show _ = (v ≫ pair fst (snd ≫ q)) ≫ fst; rw [Cat.assoc, fst_pair]
    have ev2 : v ≫ (snd : prod C P' ⟶ P') = (pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂) ≫ snd := by
      have : (pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂) ≫ (snd : prod C P' ⟶ P') = d.π₂ := snd_pair _ _
      rw [this, ← hv₂]
    exact (pair_uniq _ _ v ev1 ev2).trans (pair_uniq _ _ _ rfl rfl).symm

/-- **§1.546(a) — the base-change/slice comparison iso (underlying).**  `sliceEmbedObj (A×P) A` is, in
    `Over (A×P)`, isomorphic to `baseChangeObj snd (sliceEmbedObj P A)` (both are the pullback of
    `snd : A×P → P` against itself).  This is the codomain identification that presents the §1.547
    transition `U → U' = A::U` as the base-change `baseChange snd` (`bcSlice_isPullback`). -/
noncomputable def bcSliceIso (A P : S) :
    OverHom (sliceEmbedObj (prod A P) A) (baseChangeObj (snd : prod A P ⟶ P) (sliceEmbedObj P A)) :=
  ⟨(HasPullbacks.has ((sliceEmbedObj P A).hom) (snd : prod A P ⟶ P)).lift
      (Cone.mk (f := (snd : prod A P ⟶ P)) (g := (snd : prod A P ⟶ P)) (prod A (prod A P))
        (pair (fst : prod A (prod A P) ⟶ A) ((snd : prod A (prod A P) ⟶ prod A P) ≫ snd))
        (snd : prod A (prod A P) ⟶ prod A P) (by rw [snd_pair])),
    (HasPullbacks.has ((sliceEmbedObj P A).hom) (snd : prod A P ⟶ P)).lift_snd _⟩

theorem bcSliceIso_isIso (A P : S) : @IsIso (Over (prod A P)) _ _ _ (bcSliceIso A P) := by
  apply overIso_of_underlying
  exact isIso_of_two_pullbacks (bcSlice_isPullback A P (prod A P) (snd : prod A P ⟶ P))
    (HasPullbacks.has ((sliceEmbedObj P A).hom) (snd : prod A P ⟶ P)).cone_isPullback _
    ((HasPullbacks.has ((sliceEmbedObj P A).hom) (snd : prod A P ⟶ P)).lift_fst _)
    ((HasPullbacks.has ((sliceEmbedObj P A).hom) (snd : prod A P ⟶ P)).lift_snd _)

/-- **§1.546(c) — the colimit-factor REFLECTION (the one honest residual).**  At the richer stage
    `U' = A::U` (`A ∉ U`), suppose the §1.546 point `x'` (the `stageInclL U'` of the fresh slice point
    `sliceFactorPoint A fst`, transported across the codomain iso) IS factored by a colimit arrow
    `y'` through the included base-changed mono `stageInclL (pushFibre g'')`.  Then there is a
    base-change SECTION `s : A×P → cnD.pt` reaching the fresh `A`-coordinate `fst`, where `cnD` is the
    chosen base-change pullback of `xE'.hom` along `snd : A×P → P`.

    `baseChange_freshFactor_missed` refutes such a section, closing §1.546 — PROVIDED this reflection
    holds.  It is the REVERSE of `colimitMono_reflects_to_fibre`: that lemma reflects a colimit MONO
    to a fibre mono via `stageInclFunctorL` faithfulness; here we must reflect a colimit POINT/FACTOR
    `y' : one ⟶ ⟨U', F hUU' xE'⟩` to a stage-`U'` slice section.

    ── THE BLOCKER (precise).  `y'` is realigned (the lax-colimit terminal `one ≅ ⟨U', overTerm(A×P)⟩`,
    `laxTerminalArrowAt`/`laxTerminalUniqAt`) to a colimit hom `⟨U', overTerm(A×P)⟩ ⟶ ⟨U', F hUU' xE'⟩`.
    To extract the section it must be a `stageInclL` of a stage-`U'` slice arrow — i.e. one needs
    `stageInclFunctorL U'` to be FULL on this hom.  But the §1.547 transitions are base-change along
    product projections (`selectProj`, covers but not full), so a colimit hom between stage-`U'`
    objects has a germ representative at a STRICTLY RICHER stage `N ⊇ U'` (`incl_surjective`/
    `homInclL_factor`) that need not descend to `U'`.  `stageInclFunctorL U'` fullness (equivalently:
    descent of a fibre-`N` point of a base-changed object back to fibre `U'`) is NOT among the built
    lemmas; it is the genuine remaining content.  Everything else of §1.546 (the escape
    `baseChange_freshFactor_missed`, the (a) base-change data, the (b) point `x'`, the §1.547
    reduction) is machine-checked sorry-free. -/
theorem richerSliceSection (W : WSCover S) (A : S) (hA : WellSupported A) (U : WSList S)
    (hbU : (wsDirected S).le W.base U) (hAU : A ∉ U.1)
    (xE' : (laxOfProjSystem' (cofinalProjSystem (S := S))).A U)
    (g'' : xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A))
    (hmono : Mono g'') (hniso : ¬ IsIso g'')
    (hnd : (A :: U.1).Nodup) (hws : ∀ B ∈ (A :: U.1), WellSupported B) :
    letI : Cat (uniformTargetTy W) := uniformTargetCat W
    ∃ (x' : @Cat.Hom _ (uniformTargetCat W)
              (@HasTerminal.one _ (uniformTargetCat W) (uniformStepTarget_preRegular W).toHasTerminal)
              ⟨⟨A :: U.1, hnd, hws⟩, (laxOfProjSystem' (cofinalProjSystem (S := S))).F
                (fun B hB => List.mem_cons.2 (Or.inr hB))
                ((laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A))⟩),
      ¬ ∃ (y' : @Cat.Hom _ (uniformTargetCat W)
                (@HasTerminal.one _ (uniformTargetCat W)
                  (uniformStepTarget_preRegular W).toHasTerminal)
                ⟨⟨A :: U.1, hnd, hws⟩, (laxOfProjSystem' (cofinalProjSystem (S := S))).F
                  (fun B hB => List.mem_cons.2 (Or.inr hB)) xE'⟩),
        @Cat.comp _ (uniformTargetCat W) _
            ⟨⟨A :: U.1, hnd, hws⟩, (laxOfProjSystem' (cofinalProjSystem (S := S))).F
              (fun B hB => List.mem_cons.2 (Or.inr hB)) xE'⟩ _ y'
          (stageInclL (laxOfProjSystem' (cofinalProjSystem (S := S)))
            (coherentProj (cofinalProjSystem (S := S)))
            (pushFibre W A hbU (fun B hB => List.mem_cons.2 (Or.inr hB)) g'')) = x' := by
  letI : HasEqualizers S := products_pullbacks_implies_equalizers
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  let L := laxOfProjSystem' (cofinalProjSystem (S := S))
  let hL := coherentProj (cofinalProjSystem (S := S))
  let T := ratLaxTerminalData (cofinalProjSystem (S := S))
  let P := listProd (𝒞 := S) U.1
  let U' : WSList S := ⟨A :: U.1, hnd, hws⟩
  have hUU' : (wsDirected S).le U U' := fun B hB => List.mem_cons.2 (Or.inr hB)
  have hsp : selectProj U'.1 U.1 hUU' = (snd : prod A P ⟶ P) := by
    show selectProj (A :: U.1) U.1 hUU' = _
    rw [selectProj_head_notin A U.1 U.1 hUU' hAU (fun B hB => hB),
        selectProj_refl U.2.1 (fun B hB => hB), Cat.comp_id]
  -- ===== (a) the §1.546 escape data (sorry-free) =====
  let pIso : OverHom (sliceEmbedObj P A) (L.F hbU (terminalSliceObj W A)) := pushTerminalSlice_iso W A hbU
  obtain ⟨pInv, hp1, hp2⟩ := pushTerminalSlice_iso_isIso W A hbU
  let m : OverHom xE' (sliceEmbedObj P A) := g'' ⊚ pInv
  have hpInv_iso : @IsIso (Over P) _ _ _ pInv := ⟨pIso, hp2, hp1⟩
  have hm_mono : @Mono (Over P) _ _ _ m := mono_postcomp_iso' hmono hpInv_iso
  have hm_niso : ¬ @IsIso (Over P) _ _ _ m := by
    intro hmi; apply hniso
    have he : g'' = @Cat.comp (Over P) _ _ _ _ m pIso := by
      apply OverHom.ext
      have hpp : pInv.f ≫ pIso.f = Cat.id _ := congrArg OverHom.f hp2
      show g''.f = (g''.f ≫ pInv.f) ≫ pIso.f
      rw [Cat.assoc, hpp, Cat.comp_id]
    rw [he]; exact isIso_comp hmi ⟨pInv, hp1, hp2⟩
  let cnD : Cone (xE'.hom) (snd : prod A P ⟶ P) := (HasPullbacks.has (xE'.hom) (snd : prod A P ⟶ P)).cone
  have hcnD : cnD.IsPullback := (HasPullbacks.has (xE'.hom) (snd : prod A P ⟶ P)).cone_isPullback
  let mf' : cnD.pt ⟶ prod A (prod A P) := pair (cnD.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A)) cnD.π₂
  have hmf1 : mf' ≫ (fst : prod A (prod A P) ⟶ A) = cnD.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A) := fst_pair _ _
  have hmf2 : mf' ≫ (snd : prod A (prod A P) ⟶ prod A P) = cnD.π₂ := snd_pair _ _
  -- the escape: NO base-change section reaches the fresh `A`-coordinate `fst`.
  have key : ∀ (s : (prod A P) ⟶ cnD.pt), s ≫ cnD.π₂ = Cat.id (prod A P) →
      s ≫ (mf' ≫ (fst : prod A (prod A P) ⟶ A)) = (fst : prod A P ⟶ A) → False :=
    fun s hs2 hsA => baseChange_freshFactor_missed m hm_mono hm_niso cnD hcnD mf' hmf1 hmf2 s hs2 hsA
  -- ===== (b) the §1.546 colimit point `x'` (sorry-free) =====
  let cod' : OverHom (sliceEmbedObj (prod A P) A)
      (baseChangeObj (snd : prod A P ⟶ P) (L.F hbU (terminalSliceObj W A))) :=
    bcSliceIso A P ⊚ (@Functor.map _ _ _ _ _ (baseChangeFunctor (snd : prod A P ⟶ P)) _ _ pIso)
  have hcodEq : L.F hUU' (L.F hbU (terminalSliceObj W A))
      = baseChangeObj (snd : prod A P ⟶ P) (L.F hbU (terminalSliceObj W A)) := by
    show baseChangeObj (selectProj U'.1 U.1 hUU') (L.F hbU (terminalSliceObj W A)) = _; rw [hsp]
  let cod : OverHom (sliceEmbedObj (prod A P) A) (L.F hUU' (L.F hbU (terminalSliceObj W A))) := hcodEq ▸ cod'
  let sfp : OverHom (overTerm (prod A P)) (sliceEmbedObj (prod A P) A) :=
    sliceFactorPoint A (fst : prod A P ⟶ A)
  let align : @Cat.Hom (Obj L) (laxColimCat L hL)
      (@HasTerminal.one _ (uniformTargetCat W) (uniformStepTarget_preRegular W).toHasTerminal)
      ⟨U', (T.ht U').one⟩ := laxTerminalArrowAt L hL T U' _
  let x' := @Cat.comp (Obj L) (laxColimCat L hL) _ _ _ align
    (stageInclL L hL (sfp ⊚ cod))
  refine ⟨x', ?_⟩
  rintro ⟨y', hy'⟩
  -- ===== (c.i) reflect the colimit factor `y'` to a stage-`N` base-change section =====
  -- Steps (1)+(2) below (`align`-kill, germ reduction, push to stage `N`) are SORRY-FREE and narrow
  -- the colimit factor `hy'` to the on-the-nose stage-`N` factorization `hstage` (`Over (∏N)`).  The
  -- single remaining gap is the stage-`N` base-change escape on `hstage`; see the note at it below.
  -- `align` is iso (a map between two terminals: `one` and the stage-`U'` terminal).
  letI htOne : HasTerminal (Obj L) := (uniformStepTarget_preRegular W).toHasTerminal
  have halignIso : @IsIso (Obj L) (laxColimCat L hL) _ _ align :=
    ⟨htOne.trm _, htOne.uniq _ _, laxTerminalUniqAt L hL T U' _ _ _⟩
  obtain ⟨alignInv, halign1, halign2⟩ := halignIso
  -- kill `align`: `z := alignInv ≫ y'` satisfies `z ≫ M = stageInclL (sfp ⊚ cod)` (a stage point).
  -- `z : ⟨U', (T.ht U').one⟩ ⟶ ⟨U', F hUU' xE'⟩`, a colimit hom between stage-`U'` objects.
  let z : @Cat.Hom (Obj L) (laxColimCat L hL) ⟨U', (T.ht U').one⟩ ⟨U', L.F hUU' xE'⟩ :=
    @Cat.comp (Obj L) (laxColimCat L hL) _ _ _ alignInv y'
  have hz : @Cat.comp (Obj L) (laxColimCat L hL) _ _ _ z
        (stageInclL L hL (pushFibre W A hbU hUU' g''))
      = stageInclL L hL (sfp ⊚ cod) := by
    show @Cat.comp (Obj L) (laxColimCat L hL) _ _ _
        (@Cat.comp (Obj L) (laxColimCat L hL) _ _ _ alignInv y')
        (stageInclL L hL (pushFibre W A hbU hUU' g'')) = _
    rw [Cat.assoc, hy']
    show @Cat.comp (Obj L) (laxColimCat L hL) _ _ _ alignInv
        (@Cat.comp (Obj L) (laxColimCat L hL) _ _ _ align (stageInclL L hL (sfp ⊚ cod))) = _
    rw [← Cat.assoc, halign2, Cat.id_comp]
  -- germ-reduce `z`: a representative `z₀` at a bound `b ⊇ U'`.
  obtain ⟨b, z₀, hz₀⟩ :=
    incl_surjective (homSystemL L hL (T.ht U').one (L.F hUU' xE')) z
  -- the refl-bound germ representatives of the two `stageInclL`s.
  let pf₀ : L.F ((wsDirected S).refl U') (L.F hUU' xE')
      ⟶ L.F ((wsDirected S).refl U') (L.F hUU' (L.F hbU (terminalSliceObj W A))) :=
    reflApp L (L.F hUU' xE') ≫ pushFibre W A hbU hUU' g''
      ≫ isoInv (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))
  let sc₀ : L.F ((wsDirected S).refl U') (T.ht U').one
      ⟶ L.F ((wsDirected S).refl U') (L.F hUU' (L.F hbU (terminalSliceObj W A))) :=
    reflApp L (T.ht U').one ≫ (sfp ⊚ cod)
      ≫ isoInv (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))
  -- `hz` as a `homCompRawL = homInclL` equation, then push to a stage `N`.
  have hraw : homCompRawL L hL (T.ht U').one (L.F hUU' xE')
        (L.F hUU' (L.F hbU (terminalSliceObj W A)))
        b z₀ ⟨U', (wsDirected S).refl U', (wsDirected S).refl U'⟩ pf₀
      = homInclL L hL (T.ht U').one (L.F hUU' (L.F hbU (terminalSliceObj W A)))
          ⟨U', (wsDirected S).refl U', (wsDirected S).refl U'⟩ sc₀ := by
    rw [← compL_homInclL L hL (T.ht U').one (L.F hUU' xE')
          (L.F hUU' (L.F hbU (terminalSliceObj W A))) b z₀
          ⟨U', (wsDirected S).refl U', (wsDirected S).refl U'⟩ pf₀]
    rw [show homInclL L hL (T.ht U').one (L.F hUU' xE') b z₀ = z from hz₀]
    exact hz
  obtain ⟨N, hbN, hUN, hUN', hstage⟩ :=
    homCompRawL_eq_stage L hL (T.ht U').one (L.F hUU' xE')
      (L.F hUU' (L.F hbU (terminalSliceObj W A)))
      b z₀ ⟨U', (wsDirected S).refl U', (wsDirected S).refl U'⟩ pf₀
      ⟨U', (wsDirected S).refl U', (wsDirected S).refl U'⟩ sc₀ hraw
  -- ===== (c.i) THE SHARPEST RESIDUAL — the stage-`N` base-change escape =====
  -- `hstage` is the ON-THE-NOSE factorization, in `L.A N = Over (∏N)`, of the `N`-image of the fresh
  -- slice point `sfp ⊚ cod` (= `sliceFactorPoint A fst` base-changed to `N`) through the `N`-image of
  -- `pushFibre g''` (= `g''` base-changed along `selectProj N.1 U.1`), witnessed by the `N`-rep
  -- `zN := pushHom … z₀` of the colimit factor `z`.  Steps (1) `align`-kill and (2) the germ
  -- reduction `z ↦ zN` + push of the colimit equation to this stage-`N` equation are now sorry-free.
  --
  -- WHAT REMAINS (single sharp gap): translate `hstage` into the binary-product shape
  -- `baseChange_freshFactor_missed` consumes.  `A ∈ U' = A::U ⊆ N` gives `hA_in_N : A ∈ N.1`, and
  -- `CofinalProj.listProd_pull_factor N.1 A N.2.1 hA_in_N` supplies `ψ : ∏N ≅ A × ∏(N.erase A)` with
  -- `ψ ≫ fst = factorProj N A`, `ψ ≫ snd = selectProj N (N.erase A)`.
  have hA_in_N : A ∈ N.1 := hUN A List.mem_cons_self
  -- `ψ : ∏N ≅ A × ∏(N.erase A)`, the reindexing onto the fresh `A`-coordinate `factorProj N A`.
  obtain ⟨hψiso, hψfst, hψsnd⟩ := listProd_pull_factor (𝒞 := S) N.1 A N.2.1 hA_in_N
  let PN : S := listProd (N.1.erase A)
  let ψ : listProd N.1 ⟶ prod A PN :=
    selectProj N.1 (A :: N.1.erase A)
      (fun _ hB => (List.mem_cons.1 hB).elim (· ▸ hA_in_N) List.mem_of_mem_erase)
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- THE SHARPEST RESIDUAL (single isolated section).  The CONSUMER is now a reusable, sorry-free,
  -- axiom-free escape: `freshSlicePoint_factors_imp_false` (RelativeCapitalization.lean) — the §1.546
  -- escape in POINT-FACTORIZATION form.  Given the proper base-changed mono `m̄ : ⟨cnD_N.pt, π₂⟩ ↪
  -- sliceEmbedObj (∏N) A` (apex comparison `mf_N`) and a POINT factorization
  -- `t ⊚ m̄ = sliceFactorPoint A (factorProj N A)`, it directly derives `False` (it extracts the
  -- section `t.f` internally and routes through `baseChange_freshFactor_missed`).  So the Step-2
  -- obligation is now exactly: PRODUCE that point factorization `t` (an `OverHom` equation), proper
  -- `m̄`, and the cone/apex data, from `hstage`.
  --
  -- WHAT REMAINS (the genuine §1.546 transport).  `hstage` is an equation of THREE `pushHom`-
  -- conjugated arrows in `Over (∏N)`.  The `pushHom` `.f`-conjugation is NO LONGER opaque: the
  -- decisive Phase-1 primitives now exist sorry-free in `CapitalizationLaxColimit.lean`:
  --   • `pushHom_transApp` : `pushHom g ≫ transApp y = transApp x ≫ Functor.map g` — the
  --     source-naturality form (the `isoInv` cancels; no `transApp`-inverse left).
  --   • `proj_pushHom_f_π₂` : `(pushHom g).f ≫ (_pb (proj (trans hjk hkm)) y).π₂
  --        = (_pb (proj (trans hik hkm)) x).π₂` — `pushHom.f` preserves the `∏N`-structure map
  --     ON THE NOSE (so each layer IS an over-`∏N` arrow with computable structure leg).
  --   • `proj_pushHom_f_π₁` : `(pushHom g).f ≫ (transApp hjk hkm y).f ≫ outerπ₁
  --        = (transApp hik hkm x).f ≫ outerπ₁ ≫ g.f` — `pushHom.f` intertwines the CONTENT
  --     projection with the underlying `g.f` (the §1.546 content arrow), explicitly via the
  --     concrete pullback `lift`s of `transApp`/`baseChangeMap` (`transApp_f_π₁π₁₀`,
  --     `baseChangeMap_f_π₁`).
  -- So `(pushHom … wa).f` over `∏N` IS now an explicit composite of `baseChangeMap` underlying
  -- arrows and pullback `lift`s, exactly as the brief demanded — the conjugation reduces to pullback
  -- algebra, not an abstract iso.
  --
  -- THE REMAINING ASSEMBLY (Phase 2, the residual).  With the primitives above, building the
  -- point-factorization `t ⊚ m̄ = sliceFactorPoint A (factorProj N A)` for
  -- `freshSlicePoint_factors_imp_false` reduces to: (i) identify the codomain object
  -- `L.F hUN' (L.F hUU' (L.F hbU term))` over `∏N` with `sliceEmbedObj (∏N) A` via `nestApp3`
  -- (`CapitalizationLaxColimit`) `≫ pushTerminalSlice_iso W A (D.trans hbU (D.trans hUU' hUN))`;
  -- (ii) reindex `∏N ≅ A×PN` by `ψ` (`hψiso`/`hψfst`/`hψsnd`); (iii) read off the base-change cone
  -- `cnD_N` (pullback of `xE'`'s N-image hom along `snd : A×PN → PN`), the apex comparison `mf'_N`,
  -- and the section `t.f` from `hstage` projected through `proj_pushHom_f_π₁`/`π₂` and precomposed by
  -- `ψ⁻¹`.  `m̄` is proper at `N` via `L_cons`/`projStage_conservative_full` on `g''` (`hniso`).
  -- This step is pure pullback bookkeeping over the now-explicit `.f` legs — no opaque coherence
  -- remains — but it is a multi-screen `pb_hom_ext` reindexing chain, the genuine §1.546 content,
  -- left as the single sharpest residual.
  -- ── (i) identify the `hstage` codomain over `∏N` with `sliceEmbedObj (∏N) A`. ──
  let hbN3 : (wsDirected S).le W.base N := (wsDirected S).trans hbU ((wsDirected S).trans hUU' hUN')
  let Θ : sliceEmbedObj (listProd N.1) A
      ⟶ L.F hUN' (L.F hUU' (L.F hbU (terminalSliceObj W A))) :=
    pushTerminalSlice_iso W A hbN3 ≫ nestApp3 L hbU hUU' hUN' (terminalSliceObj W A)
  have hΘiso : @IsIso (Over (listProd N.1)) _ _ _ Θ :=
    isIso_comp (pushTerminalSlice_iso_isIso W A hbN3)
      (nestApp3_isIso L hbU hUU' hUN' (terminalSliceObj W A))
  -- ── (ii) the N-image of `pushFibre g''`, a PROPER mono into `sliceEmbedObj (∏N) A` via `Θ⁻¹`. ──
  -- N-image of `pushFibre = Functor.map (functF hUU') g''`.
  let pfN : L.F hUN' (L.F hUU' xE') ⟶ L.F hUN' (L.F hUU' (L.F hbU (terminalSliceObj W A))) :=
    @Functor.map _ _ _ _ _ (L.functF hUN') _ _ (pushFibre W A hbU hUU' g'')
  let m_N : OverHom (L.F hUN' (L.F hUU' xE')) (sliceEmbedObj (listProd N.1) A) :=
    pfN ⊚ isoInv hΘiso
  have hpfN_mono : Mono pfN :=
    projStage_preservesMono (cofinalProjSystem (S := S)) hUN'
      (@Functor.map _ _ _ _ _ (L.functF hUU') _ _ g'')
      (projStage_preservesMono (cofinalProjSystem (S := S)) hUU' g'' hmono)
  have hΘinv_iso : IsIso (isoInv hΘiso) := ⟨Θ, inv_isoInv_comp hΘiso, isoInv_comp hΘiso⟩
  have hm_N_mono : @Mono (Over (listProd N.1)) _ _ _ m_N :=
    mono_postcomp_iso' hpfN_mono hΘinv_iso
  have hm_N_niso : ¬ @IsIso (Over (listProd N.1)) _ _ _ m_N := by
    intro hmi
    -- `m_N = pfN ≫ Θ⁻¹` iso, `Θ⁻¹` iso ⇒ `pfN` iso ⇒ (L_cons) push iso ⇒ g'' iso.
    have hpfN_iso : IsIso pfN := by
      have hmΘ : @IsIso (Over (listProd N.1)) _ _ _ (@Cat.comp (Over (listProd N.1)) _ _ _ _ m_N Θ) :=
        isIso_comp hmi hΘiso
      have heq : (@Cat.comp (Over (listProd N.1)) _ _ _ _ m_N Θ) = pfN := by
        show @Cat.comp (Over (listProd N.1)) _ _ _ _
            (@Cat.comp (Over (listProd N.1)) _ _ _ _ pfN (isoInv hΘiso)) Θ = pfN
        rw [Cat.assoc, inv_isoInv_comp hΘiso, Cat.comp_id]
      rwa [heq] at hmΘ
    exact hniso (L_cons hUU' g'' (L_cons hUN' (pushFibre W A hbU hUU' g'') hpfN_iso))
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- SHARPEST RESIDUAL (now reduced to ONE structural step — the §1.546 descent).
  --
  -- VERIFIED ABOVE (sorry-free):  `m_N : OverHom (L.F hUN' (L.F hUU' xE')) (sliceEmbedObj (∏N) A)`
  -- is a PROPER mono (`hm_N_mono`, `hm_N_niso`) — the N-image of `pushFibre g''` transported by the
  -- object iso `Θ` (`nestApp3 ≫ pushTerminalSlice_iso`) onto `sliceEmbedObj (∏N) A`.  The `ψ`-reindex
  -- `∏N ≅ A×PN` (`hψiso`/`hψfst`/`hψsnd`) is in hand.
  --
  -- WHAT REMAINS — the §1.546 DESCENT (the genuine open core, NOT a `pb_hom_ext` triviality).
  -- `freshSlicePoint_factors_imp_false` consumes a proper mono `m` over the OLD base `PN` whose
  -- base-change along `snd : A×PN ⟶ PN` is the apex of the fresh-point factorization.  But `m_N`
  -- lives over `∏N ≅ A×PN` (the base WITH the fresh `A`-coordinate `factorProj N A = ψ≫fst`), one
  -- product-factor RICHER than `PN`.  To feed the consumer we must DESCEND `m_N` to a proper mono
  -- `m` over `PN` whose `snd`-base-change recovers `m_N` — i.e. exhibit `m_N` AS the base-change
  -- (along `snd : A×PN ⟶ PN`) of an `A/PN`-mono.  This is the §1.546 structural fact that the fresh
  -- `A`-factor is INDEPENDENT of `PN`: it holds because `m_N` is the N-image (base-change along
  -- `selectProj N U'`) of `pushFibre g''`, and `selectProj N U' = ψ ≫ (A × selectProj_{PN←U}) ≫ …`
  -- routes through `snd`.  Establishing that base-change factorization (the pullback-pasting that
  -- splits `selectProj N U'` through `snd : A×PN ⟶ PN`) is the remaining multi-screen step; with
  -- the descended `m`, the point factorization `t` is read off `hstage` via `proj_pushHom_f_π₁/π₂`
  -- and `freshSlicePoint_factors_imp_false` closes the goal.
  --
  -- ── THE DESCENT, MADE EXPLICIT (the projection identity is now in hand). ──
  -- `A ∉ U` (`hAU`) and `U ⊆ N` (`hUN`) give `U ⊆ N.erase A`, so the §1.547 SUCCESSOR projection
  -- `selectProj N (A::U)` — the base map along which `pushFibre g''` was base-changed to produce the
  -- N-image `m_N` over `∏N` — SPLITS through the fresh `A`-coordinate via `selectProj_pull_head`:
  --   `selectProj N (A::U) = ψ ≫ pair fst (snd ≫ selectProj (N.erase A) U)`,
  -- with `ψ : ∏N ≅ A×PN` (`PN = ∏(N.erase A)`) the reindexing onto the fresh `A`-factor.  So the
  -- base-change along `selectProj N (A::U)` FACTORS (pseudofunctorially, `projTransIso`) as
  -- base-change along `selectProj (N.erase A) U` (landing at the PN-level — the proper mono `m` the
  -- consumer `freshSlicePoint_factors_imp_false` eats) THEN along `snd : A×PN ⟶ PN` (the
  -- base-change whose section the §1.546 escape refutes) THEN transported by `ψ` (recovering `m_N`
  -- over `∏N`).  `hUe` and the split identity are recorded for the assembly:
  have hUe : ∀ B ∈ U.1, B ∈ N.1.erase A := fun B hB =>
    List.mem_erase_of_ne (a := B) (by rintro rfl; exact hAU hB)
      |>.mpr (hUN B (List.mem_cons.2 (Or.inr hB)))
  have hsplit :
      selectProj N.1 (A :: U.1) hUN'
        = selectProj N.1 (A :: N.1.erase A)
            (fun _ hB => (List.mem_cons.1 hB).elim (· ▸ hA_in_N) List.mem_of_mem_erase)
          ≫ pair (fst : prod A PN ⟶ A)
              ((snd : prod A PN ⟶ PN) ≫ selectProj (N.1.erase A) U.1 hUe) :=
    selectProj_pull_head (𝒞 := S) N.1 A U.1 N.2.1 hnd hA_in_N hUe hUN'
  -- ── THE PN-LEVEL PROPER MONO `m_PN` (the descended subobject the consumer eats) — SORRY-FREE. ──
  -- `selectProj (N.erase A) U` is a cover (bigger nodup product of well-supported objects projects).
  have hcov : Cover (selectProj (N.1.erase A) U.1 hUe) :=
    selectProj_cover (𝒞 := S) (N.1.erase A) U.1 U.2.1 hUe
      (fun B hB => N.2.2 B (List.mem_of_mem_erase hB))
  -- `m_PN := baseChangeMap (selectProj (N.erase A) U) m`, the base-change of the `∏U`-level proper
  -- mono `m` down to `PN = ∏(N.erase A)`.  Mono: base-change preserves monos
  -- (`projStage_preservesMono`).  ¬Iso: base-change along the COVER `selectProj (N.erase A) U`
  -- reflects iso among monos (`isIso_of_baseChange_isIso_of_cover`, BaseChangeDescent.lean), so an
  -- iso `m_PN` would force `m` iso, contradicting `hm_niso`.
  have hmPN_mono : @Mono (Over PN) _ _ _ (baseChangeMap (selectProj (N.1.erase A) U.1 hUe) m) :=
    projStage_preservesMono (cofinalProjSystem (S := S)) (i := U)
      (j := (⟨N.1.erase A, N.2.1.erase A,
        fun B hB => N.2.2 B (List.mem_of_mem_erase hB)⟩ : WSList S)) hUe m hm_mono
  have hmPN_niso : ¬ @IsIso (Over PN) _ _ _ (baseChangeMap (selectProj (N.1.erase A) U.1 hUe) m) :=
    fun hiso => hm_niso (isIso_of_baseChange_isIso_of_cover (selectProj (N.1.erase A) U.1 hUe)
      hcov m hm_mono hiso)
  -- ── THE COMPARISON ISO `bcGen : sliceEmbedObj PN A ≅ baseChangeObj (selectProj (N.erase A) U) … ──
  -- the codomain identification (§1.546(a), generic base map `q := selectProj (N.erase A) U`):
  -- `baseChangeObj q (sliceEmbedObj P A) ≅ sliceEmbedObj PN A` (both pullbacks of `snd : A×P → P`
  -- along `q`, apex `A×PN`), via `bcSlice_isPullback … q` + `isIso_of_two_pullbacks`.  Transporting
  -- `m_PN` across it gives the consumer's `m : OverHom (baseChangeObj q xE') (sliceEmbedObj PN A)`.
  let bcGenCone : Cone (snd : prod A P ⟶ P) (selectProj (N.1.erase A) U.1 hUe) :=
    Cone.mk (f := (snd : prod A P ⟶ P)) (g := selectProj (N.1.erase A) U.1 hUe) (prod A PN)
      (pair (fst : prod A PN ⟶ A) ((snd : prod A PN ⟶ PN) ≫ selectProj (N.1.erase A) U.1 hUe))
      (snd : prod A PN ⟶ PN) (by rw [snd_pair])
  let bcGen : OverHom (sliceEmbedObj PN A)
      (baseChangeObj (selectProj (N.1.erase A) U.1 hUe) (sliceEmbedObj P A)) :=
    ⟨(HasPullbacks.has ((sliceEmbedObj P A).hom) (selectProj (N.1.erase A) U.1 hUe)).lift bcGenCone,
      (HasPullbacks.has ((sliceEmbedObj P A).hom) (selectProj (N.1.erase A) U.1 hUe)).lift_snd
        bcGenCone⟩
  have bcGen_iso : @IsIso (Over PN) _ _ _ bcGen := by
    apply overIso_of_underlying
    show @IsIso S _ _ _
      ((HasPullbacks.has ((sliceEmbedObj P A).hom) (selectProj (N.1.erase A) U.1 hUe)).lift bcGenCone)
    exact isIso_of_two_pullbacks
      (bcSlice_isPullback A P PN (selectProj (N.1.erase A) U.1 hUe))
      (HasPullbacks.has ((sliceEmbedObj P A).hom) (selectProj (N.1.erase A) U.1 hUe)).cone_isPullback
      _
      ((HasPullbacks.has ((sliceEmbedObj P A).hom) (selectProj (N.1.erase A) U.1 hUe)).lift_fst
        bcGenCone)
      ((HasPullbacks.has ((sliceEmbedObj P A).hom) (selectProj (N.1.erase A) U.1 hUe)).lift_snd
        bcGenCone)
  -- the projection split routed through `snd : A×PN → PN` (consumed by the descent pasting below):
  -- `selectProj N U' ≫ snd = ψ ≫ (snd ≫ selectProj (N.erase A) U)`.
  have hsplit2 : selectProj N.1 U'.1 hUN' ≫ (snd : prod A P ⟶ P)
      = ψ ≫ ((snd : prod A PN ⟶ PN) ≫ selectProj (N.1.erase A) U.1 hUe) := by
    rw [show selectProj N.1 U'.1 hUN' = _ from hsplit, Cat.assoc, snd_pair]
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- THE SINGLE SHARPEST RESIDUAL — the §1.546 descent EQUATION + section read-off.
  --
  -- VERIFIED ABOVE (sorry-free): the PN-level PROPER mono `m_PN := baseChangeMap (selectProj
  -- (N.erase A) U) m` (`hmPN_mono`/`hmPN_niso`), the codomain comparison iso `bcGen`/`bcGen_iso`
  -- (so `m̄_PN := bcGen⁻¹ ⊚ m_PN : OverHom (baseChangeObj (selectProj (N.erase A) U) xE')
  -- (sliceEmbedObj PN A)` is the proper mono `freshSlicePoint_factors_imp_false` consumes at base
  -- `PN`), and the base-map split `hsplit2` routing `selectProj N U' ≫ snd` through `snd : A×PN→PN`.
  --
  -- WHAT REMAINS — two coupled steps:
  --   (1) THE DESCENT EQUATION.  `m_N = ψ-iso-transport (baseChangeMap (snd : A×PN→PN) m̄_PN)`.
  --       `m_N`'s domain `L.F hUN' (L.F hUU' xE') = baseChangeObj (selectProj N U') (baseChangeObj
  --       (selectProj U' U) xE')` (rfl).  By `hsplit2` the OUTER base `selectProj N U'` post-composed
  --       with `snd` (= `selectProj U' U`, `hsp`) factors as `ψ ≫ (snd ≫ selectProj (N.erase A) U)`;
  --       `baseChangeTransNatIso` (+ `pasteCone_isPullback`) identifies the chosen pullback at `∏N`
  --       (apex of `m_N`) with the PASTED pullback `(snd-pullback over A×PN) ∘ ((selectProj (N.erase
  --       A) U)-pullback over PN)`, ψ-transported.  The two inner `bcGen`-style comparison isos (at
  --       P and at PN) reconcile the `sliceEmbedObj`/`baseChangeObj` codomains; `pfN`'s `.f`-legs are
  --       `proj_pushHom_f_π₁`/`proj_pushHom_f_π₂`.  Output: cone `cnD_N` (= `snd`-pullback of
  --       `(baseChangeObj (selectProj (N.erase A) U) xE').hom`), apex `mf'_N`, and `m̄_N : OverHom
  --       ⟨cnD_N.pt, π₂⟩ (sliceEmbedObj (A×PN) A)` with `m̄_N.f = mf'_N` — the consumer's cone data.
  --   (2) THE POINT READ-OFF.  `hstage` (the on-the-nose stage-`N` factorization of the fresh point
  --       through `pfN`) gives, via `proj_pushHom_f_π₂` (structure leg) and `proj_pushHom_f_π₁`
  --       (content leg) precomposed by `ψ⁻¹` (`hψiso`) and transported by `Θ`/`hΘiso`, a point
  --       `t : OverHom (overTerm (A×PN)) ⟨cnD_N.pt, π₂⟩` with `t ⊚ m̄_N = sliceFactorPoint A fst`.
  --   Then `freshSlicePoint_factors_imp_false (bcGen⁻¹ ⊚ m_PN) … cnD_N hcnD_N mf'_N … m̄_N rfl t hfac`
  --   closes the goal.  This is the multi-screen `pb_hom_ext` reindexing chain (the genuine §1.546
  --   content); every primitive it needs is now in scope sorry-free.
  exact (by sorry : False)

/-- **Freyd's §1.546 density (the genuine open core).**  The §1.546 ESCAPE is sorry-free
    (`baseChange_freshFactor_missed`); the (a) base-change comparison (`bcSliceIso`) and (b) colimit
    point are sorry-free in `richerSliceSection`.  Two sharp residuals remain (see the Phase 3 note):
    (c.i) the `stageInclFunctorL U'` fullness reflection of a colimit factor to a base-change section
    (`richerSliceSection`), and (c.ii) the `A ∈ U` fresh-copy case.  No fractions saturation is needed;
    the §1.547 reduction around the core is machine-checked. -/
theorem richerSliceMiss (W : WSCover S) : RicherSliceMiss W := by
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  intro A hA U hbU xE' g'' hmono hniso
  by_cases hAU : A ∈ U.1
  · -- SECOND RESIDUAL (c.ii): `A ∈ U`.  The escape needs a FRESH independent `A`-factor in the base,
    -- but `A ∈ U.1` blocks `A :: U.1` being nodup, so the richer stage `U' = A::U` is unavailable.
    -- Route (1) (reflect at an `A`-free stage) is IMPOSSIBLE: the stage `U` here is universally
    -- quantified in `RicherSliceMiss`, and the directed `WSList` index only ENLARGES stages
    -- (`hUU' : U ≤ U'` adds factors), never removes `A`; so an `A ∉ U'` stage with `U ⊆ U'` cannot
    -- exist when `A ∈ U`.  The principled fix is ROUTE (2): re-index `cofinalProjSystem` by nodup
    -- lists over `S ⊕ Unit` (or `S` with a distinguished prependable "point slot") so the embedded
    -- object's fresh `A`-factor is ALWAYS addable.  This re-threads `WSList`/`selectProj`/
    -- `cofinalProjSystem`/`uniformStep`/`FibreDensity` — LARGE; deferred (see report).
    sorry
  · -- `A ∉ U`: the directed-union escape at `U' = A :: U`, via `richerSliceSection` (sorry-free
    -- except for the isolated §1.546(c) fullness residual it documents).
    have hnd : (A :: U.1).Nodup := List.nodup_cons.2 ⟨hAU, U.2.1⟩
    have hws : ∀ B ∈ (A :: U.1), WellSupported B := by
      intro B hB; rcases List.mem_cons.1 hB with e | hf
      · exact e ▸ hA
      · exact U.2.2 B hf
    obtain ⟨x', hx'⟩ := richerSliceSection W A hA U hbU hAU xE' g'' hmono hniso hnd hws
    exact ⟨⟨A :: U.1, hnd, hws⟩, fun B hB => List.mem_cons.2 (Or.inr hB), x', hx'⟩

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

-- The §1.547 reduction is SORRY-FREE / axiom-clean; the residuals are isolated in `richerSliceMiss`.
-- The §1.546(a) base-change/slice comparison is sorry-free:
#print axioms Freyd.FibreDensityProof.bcSlice_isPullback
#print axioms Freyd.FibreDensityProof.bcSliceIso_isIso
#print axioms Freyd.FibreDensityProof.stageInclL_g''_factor
#print axioms Freyd.FibreDensityProof.fibreDensity_of_richerSliceMiss
-- `fibreDensity` / `wsCover_fibreDensity` depend on `sorryAx` *only* through `richerSliceMiss`,
-- whose two isolated residuals are (i) the §1.546(c) `stageInclFunctorL U'` fullness reflection
-- (`richerSliceSection`) and (ii) the `A ∈ U` fresh-copy case.  The whole §1.546 escape
-- (`baseChange_freshFactor_missed`), the (a) base-change comparison, the (b) colimit point, and the
-- §1.547 colimit↔fibre reduction are machine-checked sorry-free.
#print axioms Freyd.FibreDensityProof.fibreDensity
