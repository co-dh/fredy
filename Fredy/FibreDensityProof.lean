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
  -- ===== (c) reflect the colimit factor to a base-change section, then apply the escape =====
  -- THE HONEST RESIDUAL: `stageInclFunctorL U'` fullness on this hom (see the docstring blocker).
  -- The reflection of `y'` yields `s : A×P → cnD.pt` with `s ≫ cnD.π₂ = id` and
  -- `s ≫ mf' ≫ fst = fst`; `key s …` then derives `False`.  `key`, `cnD`, `mf'` (the §1.546 escape
  -- data) are all in hand above; only the fullness reflection of `y'` to `s` is missing.
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
  · -- SECOND RESIDUAL: `A ∈ U` (the fresh `A`-coordinate cannot be appended nodup; needs a fresh
    -- independent copy of `A` — not expressible at the object level of this index).  See the note.
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
