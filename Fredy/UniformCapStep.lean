/-
  §1.547 — THE UNIFORM CAPITALIZATION SUCCESSOR as a `CapStep`.

  This file BEGINS the construction of `uniformStep (S : PreRegBundle) : CapStep S.carrier`, the
  remaining content of `Freyd.capData_exists`.  Its point (vs. the countable `nextStepOfEnum`) is that
  ONE rung adjoins a point to EVERY well-supported object of `S` simultaneously, so it can satisfy
  `StepWellPoints` (`CapitalizationTransfinite.lean`).

  ── ROUTE ──────────────────────────────────────────────────────────────────────────────────────
  The successor target is the LAX colimit `ratCapCat P_S` of the §1.547 base-change slice system
  `laxOfProjSystem' P_S`, where `P_S : ProjSystem (List S.carrier) listDirected S.carrier` is the
  system of finite-product projections over (lists of) well-supported objects of `S`:

    * stage index `U : List S.carrier`  (a finite set of objects, modelled as a list);
    * stage product `pr U = ∏U = listProd U`  (right-folded binary product, `pr [] = 1`);
    * projection `proj : ∏U' ⟶ ∏U` for `U ⊆ U'`  (the bigger product onto the smaller).

  `ratCapPreRegular_of_projCover P_S hpc` (RatCapStagePTC.lean) makes `ratCapCat P_S` pre-regular,
  given `hpc : ∀ {U U'} (h), Cover (P_S.proj h)`.  Each projection `∏U' ↠ ∏U` is a cover because the
  dropped factors are well-supported (`prod_fst_cover`/`cover_comp'`), so `hpc` is genuinely available.

  The successor functor `step : S → ratCapCat P_S` is the base embedding `S → Over (pr []) = Over 1`
  (`baseSliceObj`, Capitalization.lean — already faithful, terminal/product/equalizer/pullback/cover
  preserving) followed by the lax stage-0 inclusion `stageInclFunctorL []` (RatCapHcanon.lean).

  ── (R-A) SOLVED — the STRICT directed projection family is now CONCRETE & sorry-free ────────────
  `proj_refl`/`proj_trans` must be ON-THE-NOSE.  Over `listDirected`'s SUBSET order they cannot be
  built choice-free (the `DecidableEq 𝒞` `ListProjFamily` wall).  We sidestep it exactly as the
  sorry-free `ordChainSliceSystem` (`Inflation.lean`) does: index by the APPEND/PREFIX order and take
  the projection to be the iterated product forget `prefixForget = catForget V (prefixSuffix V U)`,
  which is STRICTLY functorial in the append index (`catForget_nil_heq`/`catForget_append_heq` give
  the refl/trans laws on the nose) and a COVER off well-supported factors (`catForget_cover`).  The
  abstract `WSProjData` structure (and its sorry inhabitant) is ELIMINATED — `projSystemOfWS` now
  takes only the concrete cofinal append index `WSChain` (the chain `hwall_step` supplies), no
  `DecidableEq`, no choice.

  ── REMAINING RESIDUAL ───────────────────────────────────────────────────────────────────────────
  (R-step) the lax stage-0 inclusion's faithfulness / finite-limit-preservation packaged as the
         `CapStep` fields — the per-piece lax lemmas exist (`stageInclFunctorL_preservesProducts`,
         `…_preservesEqualizers`, `…_preservesPullbacks`, `homInclL_cover_*`) but their composition
         with `baseSliceFunctor` into the exact `CapStep` field shapes is the remaining assembly.

  No mathlib category theory (the lax colimit is on this repo's own `Cat`); the ordinal exception is
  not needed here.  No `axiom`, no `: True`, no statement-weakening; every `sorry` is on the book's
  genuine statement and reported.
-/
import Fredy.RatCapStagePTC
import Fredy.RelativeCapitalization
import Fredy.CapitalizationTransfinite

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.UniformCap

universe u

variable {S : Type u} [Cat.{u} S] [PreRegularCategory S]

/-! ## Phase 1 — the STRICT product-projection `prefixForget` over the APPEND order

  `ProjSystem.proj_refl`/`proj_trans` must be ON-THE-NOSE.  Over the SUBSET-ordered index
  (`listDirected`) they are not — building the projection `∏U' ⟶ ∏U` choice-free with strict
  coherence needs positional matching `B ∈ U' ↦ index` (barred without `DecidableEq S`; the
  §1.547 `ListProjFamily` wall).

  We sidestep the wall exactly as the sorry-free `ordChainSliceSystem` (`Inflation.lean`) does:
  index by the APPEND/PREFIX order `V ⊑ U := V <+: U`.  The projection is then the iterated product
  forget `catForget V (prefixSuffix V U) : ∏(V ++ d) ⟶ ∏V` (drop the appended suffix `d`), which is
  STRICTLY functorial in the append index — `catForget_nil_heq` (drop nothing = id) and
  `catForget_append_heq` (drop `d++e` = drop `e` then drop `d`) give the strict refl/trans laws on
  the nose, threaded through the base-equality transport by `comp_heq` (the same machinery the
  strict inner `innerSliceTr_refl`/`_trans` uses).  And `catForget V d` is a COVER whenever `∏d` is
  well-supported (`catForget_cover`), which holds because `d` is a suffix of the chain (whose members
  are all well-supported).  No `DecidableEq`, no abstract `WSProjData` structure, no choice. -/

/-- The strict product projection `∏U ⟶ ∏V` for a prefix `V ⊑ U`: the iterated forget
    `catForget V (prefixSuffix V U)`, transported along `V ++ prefixSuffix V U = U` (`prefixSuffix_eq`)
    so it lands at the *object* `listProd U` (not the propositionally-equal `listProd (V ++ d)`). -/
noncomputable def prefixForget {V U : List S} (h : prefixLe V U) :
    listProd (𝒞 := S) U ⟶ listProd (𝒞 := S) V :=
  (prefixSuffix_eq h) ▸ (catForget (𝒞 := S) V (prefixSuffix V U))

/-- The base-equality transport in `prefixForget` only re-types the domain: `prefixForget h` is
    `HEq` the untransported `catForget V (prefixSuffix V U)`.  (`subst` collapses the `▸`.) -/
theorem transportForget_heq {V U : List S} (d : List S) (e : V ++ d = U) :
    HEq (e ▸ (catForget (𝒞 := S) V d) : listProd (𝒞 := S) U ⟶ listProd (𝒞 := S) V)
        (catForget (𝒞 := S) V d) := by
  subst e; rfl

theorem prefixForget_heq {V U : List S} (h : prefixLe V U) :
    HEq (prefixForget h) (catForget (𝒞 := S) V (prefixSuffix V U)) :=
  transportForget_heq (prefixSuffix V U) (prefixSuffix_eq h)

/-- `catForget` is invariant under a base-list equality (up to `HEq`). -/
theorem catForget_base_heq {V V' : List S} (d : List S) (h : V = V') :
    HEq (catForget (𝒞 := S) V d) (catForget (𝒞 := S) V' d) := by subst h; rfl

/-- **STRICT unit** — `prefixForget (refl) = id`.  The empty appended suffix forgets nothing
    (`catForget_nil_heq`, `prefixSuffix V V = []`). -/
theorem prefixForget_refl {V : List S} :
    prefixForget (List.prefix_refl V) = Cat.id (listProd (𝒞 := S) V) := by
  have hps : prefixSuffix V V = ([] : List S) := by unfold prefixSuffix; rw [List.drop_length]
  apply eq_of_heq
  refine (prefixForget_heq (List.prefix_refl V)).trans ?_
  rw [hps]; exact catForget_nil_heq V

/-- **STRICT composition** (contravariant) — `prefixForget (h₁.trans h₂) = prefixForget h₂ ≫
    prefixForget h₁`.  Forgetting the concatenated suffix `dVU ++ dUW` equals forgetting `dUW` then
    `dVU` (`catForget_append_heq`), threaded through the base transport by `comp_heq`. -/
theorem prefixForget_trans {V U W : List S} (h₁ : prefixLe V U) (h₂ : prefixLe U W) :
    prefixForget (h₁.trans h₂) = prefixForget h₂ ≫ prefixForget h₁ := by
  apply eq_of_heq
  have hVU : V ++ prefixSuffix V U = U := prefixSuffix_eq h₁
  have hUW : U ++ prefixSuffix U W = W := prefixSuffix_eq h₂
  refine (prefixForget_heq (h₁.trans h₂)).trans ?_
  rw [show prefixSuffix V W = prefixSuffix V U ++ prefixSuffix U W from prefixSuffix_trans h₁ h₂]
  refine (catForget_append_heq V (prefixSuffix V U) (prefixSuffix U W)).trans ?_
  refine comp_heq _ _ _ _ (by rw [hVU, hUW]) (by rw [hVU]) rfl ?_ (HEq.symm (prefixForget_heq h₁))
  exact (catForget_base_heq (prefixSuffix U W) hVU).trans (HEq.symm (prefixForget_heq h₂))

/-- **`prefixForget` is a COVER** when the dropped suffix `∏(prefixSuffix V U)` is well-supported
    (`catForget_cover`, transported). -/
theorem transportForget_cover [HasEqualizers S] {V U : List S} (d : List S) (e : V ++ d = U)
    (hc : Cover (catForget (𝒞 := S) V d)) :
    Cover (e ▸ (catForget (𝒞 := S) V d) : listProd (𝒞 := S) U ⟶ listProd (𝒞 := S) V) := by
  subst e; exact hc

theorem prefixForget_cover [HasEqualizers S] {V U : List S} (h : prefixLe V U)
    (hws : WellSupported (listProd (𝒞 := S) (prefixSuffix V U))) :
    Cover (prefixForget h) :=
  transportForget_cover (prefixSuffix V U) (prefixSuffix_eq h) (catForget_cover hws V)

/-! ## Phase 2 — the append-ordered well-supported index and `projSystemOfWS`

  Following the sorry-free `OrdChain`/`ordChainSliceSystem` pattern (`Inflation.lean`): the directed
  index is an ARBITRARY directed `(ι, D)` carrying a `prefixLe`-monotone `chain : ι → List S` whose
  every member is well-supported, plus a distinguished base index `base` with `chain base = []` (the
  fibre `S/1` the successor embeds into).  This is the cofinal chain `hwall_step` supplies (an
  enumeration of the well-supported objects of `S`); `projSystemOfWS` reads its `pr`/`proj` straight
  off `prefixForget`, with refl/trans STRICT by `prefixForget_refl`/`prefixForget_trans`. -/

/-- **The append-ordered well-supported index for the §1.547 successor.**  A `prefixLe`-monotone
    chain of finite well-supported-object lists over an arbitrary directed index, with a base index
    whose stage is the empty list (`∏[] = 1`, the fibre `S/1`).  Replaces the abstract `WSProjData`
    by concrete append data — the strict projection is `prefixForget` off the chain. -/
structure WSChain (S : Type u) [Cat.{u} S] [PreRegularCategory S] where
  /-- the directed index of the chain -/
  ι : Type u
  /-- the directed order on the index -/
  D : Directed ι
  /-- the chain of finite well-supported-object lists -/
  chain : ι → List S
  /-- the chain is `prefixLe`-monotone along the directed order -/
  mono : ∀ {i j : ι}, D.le i j → prefixLe (chain i) (chain j)
  /-- every object listed in any stage is well-supported (so the dropped suffixes are too) -/
  ws : ∀ (i : ι) (B : S), B ∈ chain i → WellSupported B
  /-- the base index whose stage is the empty list (the fibre `S/1`) -/
  base : ι
  /-- the base stage IS the empty list -/
  chain_base : chain base = ([] : List S)

/-- **`projSystemOfWS` — the §1.547 product-projection `ProjSystem` over the APPEND order.**  Index
    = the chain's directed index; stage product `pr i = ∏(chain i)`; projection `proj h =
    prefixForget (mono h)` (drop the appended suffix).  Strict coherence is the STRICT
    `prefixForget_refl`/`prefixForget_trans` — solved ON THE NOSE the same way `ordChainSliceSystem`
    solves it, with NO `WSProjData` and NO `DecidableEq`. -/
noncomputable def projSystemOfWS (C : WSChain S) : ProjSystem C.ι C.D S where
  pr i := listProd (C.chain i)
  proj h := prefixForget (C.mono h)
  proj_refl _ := prefixForget_refl
  proj_trans h₁ h₂ := prefixForget_trans (C.mono h₁) (C.mono h₂)

/-- **`projSystemOfWS_cover`** — every projection of `projSystemOfWS C` is a cover.  The dropped
    suffix is a sublist of a chain stage, hence well-supported (`WSChain.ws` + `wellSupported_listProd`),
    so `prefixForget_cover` applies.  This is the `hpc` premise of `ratCapPreRegular_of_projCover`. -/
theorem projSystemOfWS_cover (C : WSChain S) :
    ∀ {i j : C.ι} (h : C.D.le i j), Cover ((projSystemOfWS C).proj h) := by
  letI : HasEqualizers S := products_pullbacks_implies_equalizers
  intro i j h
  refine prefixForget_cover (C.mono h) ?_
  -- the dropped suffix `prefixSuffix (chain i) (chain j)` is a sublist of `chain j`.
  exact wellSupported_listProd
    (fun B hB => C.ws j B (List.mem_of_mem_drop hB))

/-! ## Phase 3 — pre-regularity of the successor target -/

/-- **`uniformStepTarget_preRegular`** — the lax-colimit target `ratCapCat (projSystemOfWS C)` is
    pre-regular, by `ratCapPreRegular_of_projCover` with `hpc = projSystemOfWS_cover`.  (`[Nonempty
    C.ι]` holds since `C.base : C.ι`; `HasEqualizers S` from products+pullbacks.) -/
noncomputable def uniformStepTarget_preRegular (C : WSChain S) :
    @PreRegularCategory (Obj (laxOfProjSystem' (projSystemOfWS C)))
      (ratCat (projSystemOfWS C)) := by
  letI : HasEqualizers S := products_pullbacks_implies_equalizers
  letI : Nonempty C.ι := ⟨C.base⟩
  exact ratCapPreRegular_of_projCover (projSystemOfWS C) (fun h => projSystemOfWS_cover C h)

/-! ## Phase 4 — the `CapStep`

  The fibre of the lax base-change system at the BASE index `C.base` is `pcObj (projSystemOfWS C)
  C.base = Over (listProd (C.chain C.base)) = Over (listProd []) = Over (1_S)` (a slice in `S` ITSELF
  over the terminal — `C.chain_base : C.chain C.base = []`).  So the §1.547 base embedding into THIS
  route is the canonical `S ≃ S/1`: `X ↦ ⟨X, term X⟩` (transported to the base stage).

  `step : S → ratCapCat (projSystemOfWS C)` is then `terminalSliceObj` followed by the lax base-stage
  inclusion `stageInclFunctorL C.base` (RatCapHcanon.lean), i.e. `X ↦ ⟨C.base, terminalSliceObj X⟩`. -/

variable (C : WSChain S)

/-- The successor target type. -/
abbrev uniformTargetTy (C : WSChain S) : Type u := Obj (laxOfProjSystem' (projSystemOfWS C))

noncomputable instance uniformTargetCat (C : WSChain S) : Cat.{u} (uniformTargetTy C) :=
  ratCat (projSystemOfWS C)

/-- The base stage product is the terminal of `S` (`listProd (C.chain C.base) = listProd [] = 1_S`). -/
theorem pr_base_eq : listProd (𝒞 := S) (C.chain C.base) = (HasTerminal.one : S) := by
  rw [C.chain_base]; rfl

/-- Any two maps into an object equal to the terminal agree. -/
theorem hom_uniq_of_eq_one {W : S} (hW : W = (HasTerminal.one : S)) {X : S}
    (f g : X ⟶ W) : f = g := by subst hW; exact term_uniq f g

/-- Any two maps into the base stage `listProd (C.chain C.base) = 1` agree (it is terminal). -/
theorem base_hom_uniq {X : S} (f g : X ⟶ listProd (𝒞 := S) (C.chain C.base)) : f = g :=
  hom_uniq_of_eq_one (pr_base_eq C) f g

/-- The fibre at the base index is the slice `S/1` over the terminal of `S`. -/
theorem fibre_base_eq :
    (laxOfProjSystem' (projSystemOfWS C)).A C.base = Over (listProd (𝒞 := S) (C.chain C.base)) :=
  rfl

/-- **The §1.547 base embedding `S → S/(∏(chain base)) = S/1`**, `X ↦ ⟨X, term X⟩` (transported along
    `pr_base_eq` so the structure map `X ⟶ listProd (C.chain C.base)` is the canonical terminator). -/
def terminalSliceObj (X : S) : Over (listProd (𝒞 := S) (C.chain C.base)) :=
  ⟨X, ((pr_base_eq C).symm ▸ (term X : X ⟶ (HasTerminal.one : S)))⟩

/-- The morphism part: `f : X ⟶ Y ↦ ⟨f, term_uniq⟩` (commutes with the structure maps since any two
    maps into the base stage `= 1` agree). -/
def terminalSliceMap {X Y : S} (f : X ⟶ Y) :
    OverHom (terminalSliceObj C X) (terminalSliceObj C Y) :=
  ⟨f, base_hom_uniq C _ _⟩

/-- The base embedding `S → S/1` is a functor (laws transport via `OverHom.ext` to the underlying
    `S`-arrow equalities, which hold by the source's `Functor`/`Cat` laws). -/
instance terminalSliceFunctor :
    @Functor S _ (Over (listProd (𝒞 := S) (C.chain C.base)))
      (overCat (listProd (𝒞 := S) (C.chain C.base))) (terminalSliceObj C) where
  map {_ _} f := terminalSliceMap C f
  map_id _ := OverHom.ext rfl
  map_comp {_ _ _} _ _ := OverHom.ext rfl

/-- **`terminalSliceObj` is FAITHFUL.**  The underlying arrow of `terminalSliceMap f` IS `f`, so two
    maps with equal images have equal `f` (`OverHom.f` is literally the original arrow). -/
theorem terminalSliceFaithful :
    @Faithful S _ (Over (listProd (𝒞 := S) (C.chain C.base)))
      (overCat (listProd (𝒞 := S) (C.chain C.base)))
      (terminalSliceObj C) (terminalSliceFunctor C) := by
  refine ⟨?_, ?_⟩
  · -- embedding: the underlying arrow of `terminalSliceMap f` IS `f`.
    intro X Y f g h
    exact congrArg OverHom.f h
  · -- conservative: `(terminalSliceMap f).f = f`, so an iso image forces `f` iso.
    intro X Y f hiso
    exact overIso_underlying hiso

/-- The successor object map `step : S → ratCapCat P`: base-embed into the base fibre, then include
    that fibre into the lax colimit (`⟨C.base, ·⟩`).  It IS the composite `stageInclFunctorL C.base ∘
    terminalSliceObj` (the object map of `stageInclFunctorL C.base` is `fun x => ⟨C.base, x⟩`). -/
def uniformStepObj (X : S) : uniformTargetTy C :=
  ⟨C.base, terminalSliceObj C X⟩

/-- The lax base-stage inclusion functor `Over (listProd (chain base)) → ratCapCat P`, object map
    `⟨C.base, ·⟩`.  (`stageInclFunctorL` of RatCapHcanon.lean, instantiated at the §1.547 system and
    stage `C.base`.) -/
noncomputable def stageInclNil :
    @Functor (Over (listProd (𝒞 := S) (C.chain C.base)))
      (overCat (listProd (𝒞 := S) (C.chain C.base)))
      (uniformTargetTy C) (uniformTargetCat C)
      (fun x => (⟨C.base, x⟩ : uniformTargetTy C)) :=
  stageInclFunctorL (laxOfProjSystem' (projSystemOfWS C)) (coherentProj (projSystemOfWS C))
    C.base

/-- **The successor functor `step : S → ratCapCat P` is a `Functor`** — the composite
    `stageInclNil ∘ terminalSliceObj` (`compFunctor`).  `uniformStepObj = stageInclNil.obj ∘
    terminalSliceObj` definitionally, so this IS its functoriality. -/
noncomputable instance uniformStepFunctor :
    @Functor S _ (uniformTargetTy C) (uniformTargetCat C) (uniformStepObj C) :=
  @compFunctor S _ (Over (listProd (𝒞 := S) (C.chain C.base)))
    (overCat (listProd (𝒞 := S) (C.chain C.base)))
    (uniformTargetTy C) (uniformTargetCat C)
    (terminalSliceObj C) (fun x => (⟨C.base, x⟩ : uniformTargetTy C))
    (terminalSliceFunctor C) (stageInclNil C)

/-- **(R-step) The successor functor is FAITHFUL.**  Composite of the faithful base embedding
    `terminalSliceFaithful` and the faithful lax stage-`[]` inclusion `stageInclNil`.  The latter's
    faithfulness is `homInclL_injective` (embedding half, transitions of the base-change system are
    faithful, `projStage_faithful`) plus iso-reflection (`homInclL_isIso_reflects`); packaging the
    composite into `Faithful` is the residual lax-inclusion assembly. -/
theorem uniformStepFaithful :
    @Faithful S _ (uniformTargetTy C) (uniformTargetCat C)
      (uniformStepObj C) (uniformStepFunctor C) := by
  sorry

/-! ## Phase 5 — the assembled `CapStep`

  `uniformStep C : CapStep S` packages the real target (`T = ratCapCat (projSystemOfWS C)`,
  pre-regular by `uniformStepTarget_preRegular`) and the real successor functor `step = uniformStepObj`
  (faithful via `uniformStepFaithful`).  The single-step PRESERVATION fields (`stepTerminal`,
  `stepTerminalArrow`, `stepProds`, `stepEqs`, `stepMono`, `stepCover`) are the composites of the base
  embedding's preservation (`terminalSliceObj` preserves all finite limits/covers — the slice `S/1`
  is `S`) with the lax stage-inclusion's preservation (`stageInclFunctorL_preservesProducts`,
  `…_preservesEqualizers`, `…_preservesPullbacks`, `homInclL_cover_*` of RatCapHcanon.lean).  Each is a
  genuine lemma; threading the lax lemmas through `compFunctor` into the exact `CapStep` field shape is
  the residual (R-step) assembly, flagged with one `sorry` per field. -/

/-- **The §1.547 uniform capitalization successor as a `CapStep`.**  Real `T`/`catT`/`preT`/`step`/
    `stepFun`; the preservation/faithfulness fields are the (R-step) lax-composition residuals. -/
noncomputable def uniformStep (C : WSChain S) : CapStep S where
  T := uniformTargetTy C
  catT := uniformTargetCat C
  preT := uniformStepTarget_preRegular C
  step := uniformStepObj C
  stepFun := uniformStepFunctor C
  stepFaithful := uniformStepFaithful C
  stepTerminal := by sorry
  stepTerminalArrow := by sorry
  stepProds := by sorry
  stepEqs := by sorry
  stepMono := by sorry
  stepCover := by sorry

end Freyd.UniformCap
