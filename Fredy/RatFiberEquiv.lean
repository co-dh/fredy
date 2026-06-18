import Fredy.RatInclColimit
import Fredy.SliceEquivalence

/-! # §1.543 I — the fraction-fiber slice equivalence `RatBelow U ≃ A/(∏U)`, and `PreRegular A*`

  This file completes **gap 1** of Freyd's §1.543 capitalization: the per-stage pre-regularity that
  `colimitPreRegular` consumes for the inclusion system `ratBelowSystem`.

  ## The route (three links, then the colimit)

  `RatColimit.lean` proved `PairOnU U ≃ A/(∏U)` (the PLAIN-`Â`-fiber, `targets = U`).  We need the
  LOCALISATION fiber `RatBelow U` (the `F° ⊆ U` full subcategory of `A* = pairRatCat`) to be
  pre-regular.  The bridge is built link by link:

  1. **`PairOnU U → RatBelow U` is fully faithful** — the localisation functor `T : Â → A*` restricted
     to the exactly-`U` objects.  Object `X ↦ RatObj.mk X.obj`; hom `m ↦ locMapOf m`.  Faithful by
     `pairLocalisation_faithful_criterion` (the §1.547 dense-roof epi).  Full because a fraction
     `[R,denom,num]` between exactly-`U` objects has its DENOMINATOR dense with
     `X°(=U) ⊆ R°` — and `dense_exactlyU_isIso` inverts it once we know `R° ⊆ U` (which holds: the
     apex `R` of the canonical representative can be taken with `R° = U`), so the fraction collapses
     to the single `Â`-hom `denom⁻¹ ≫ num`.

  This is the first committed link; subsequent links and the colimit assembly are layered on top. -/

namespace Freyd

open Freyd.Colim

universe u

variable {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
  [HasEqualizers 𝒞] [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞]

/-! ## Link 1 — the embedding `J : PairOnU U → RatBelow U`

  `J` is the localisation functor `T : Â → A*` cut down to the exactly-`U` full subcategories.
  On objects it sends a `PairOnU U` object `⟨Xo, Xo° = U⟩` to the `RatBelow U` object
  `⟨RatObj.mk Xo, Xo° = U ⊆ U⟩`; on homs it sends a `PairHom Xo → Yo` to its localisation
  `locMapOf hD`.  Functoriality is inherited from `pairLocFunctor`. -/

/-- The object map `PairOnU U → RatBelow U`: localise the underlying `Â`-object; the targets-`⊆ U`
    proof is the reflexive subset (`Xo° = U`). -/
def fiberJObj {U : List 𝒞} (X : PairOnU U) : RatBelow (𝒞 := 𝒞) U :=
  ⟨RatObj.mk (_hD := pairDense_denseRoof) X.obj, fun T hT => X.htgt ▸ hT⟩

@[simp] theorem fiberJObj_obj {U : List 𝒞} (X : PairOnU U) :
    (fiberJObj X).obj = RatObj.mk (_hD := pairDense_denseRoof) X.obj := rfl

/-- The functor `J : PairOnU U → RatBelow U`.  Hom-action is the localisation `locMapOf` of the
    underlying `PairHom`; `map_id`/`map_comp` are inherited from `pairLocFunctor` (= `locFunctorOf`),
    which is the same `locMapOf` action under the `RatBelow`/`RatObj` identifications. -/
instance fiberJ {U : List 𝒞} : @Functor (PairOnU U) _ (RatBelow (𝒞 := 𝒞) U) _ fiberJObj where
  map {X Y} (m : PairHom X.obj Y.obj) :=
    (pairLocFunctor (𝒞 := 𝒞)).map (F := fun A : PairObj 𝒞 => RatObj.mk (_hD := pairDense_denseRoof) A) m
  map_id X := (pairLocFunctor (𝒞 := 𝒞)).map_id X.obj
  map_comp m n := (pairLocFunctor (𝒞 := 𝒞)).map_comp m n

@[simp] theorem fiberJ_map {U : List 𝒞} {X Y : PairOnU U} (m : PairHom X.obj Y.obj) :
    (fiberJ (U := U)).map m = locMapOf pairDense_denseRoof m := rfl

/-- **Link 1 — `J : PairOnU U → RatBelow U` is an `Embedding`** (faithful).  `locMapOf m₁ = locMapOf m₂`
    gives, by `Quotient.exact`, a `FractionEquiv` of the two localisation spans `[id, mᵢ]`: a common
    roof `R, r₁, r₂ : R → X.obj` with `r₁ = r₂` (denominators are `id`, `Cat.comp_id`), `r₁` DENSE
    (`mem (r₁ ≫ id) = mem r₁`), and `r₁ ≫ m₁ = r₁ ≫ m₂` (numerators).  A dense leg is epic in `Â`
    (`pairLocalisation_faithful_criterion`), so `m₁ = m₂`. -/
theorem fiberJ_embedding (U : List 𝒞) : Embedding (fun X : PairOnU U => fiberJObj X) := by
  intro X Y m₁ m₂ h
  -- `h : locMapOf m₁ = locMapOf m₂` (the two `RatBelow`-homs).  Extract the `FractionEquiv`.
  have heq : FractionEquiv (locFraction pairDenseClass m₁) (locFraction pairDenseClass m₂) :=
    Quotient.exact h
  obtain ⟨R, r₁, r₂, hmem, hden, hnum⟩ := heq
  simp only [locFraction] at hmem hden hnum
  -- denominators of `locFraction` are `id`: `r₁ ≫ id = r₂ ≫ id` ⟹ `r₁ = r₂`.
  have hr : r₁ = r₂ := by rwa [Cat.comp_id, Cat.comp_id] at hden
  -- `r₁` is dense (`mem (r₁ ≫ id) = mem r₁`).
  have hmem' : (pairDenseClass (𝒞 := 𝒞)).mem r₁ := by rwa [Cat.comp_id] at hmem
  -- numerators: `r₁ ≫ m₁ = r₂ ≫ m₂ = r₁ ≫ m₂`.
  have hnum' : r₁.comp m₁ = r₁.comp m₂ := by
    show r₁ ≫ m₁ = r₁ ≫ m₂
    rw [hnum, hr]
  exact hmem'.elim (fun d => pairLocalisation_faithful_criterion d m₁ m₂ hnum')

/-! ## Remaining blocker — `Full (fiberJ)` (the fraction-collapse) — stated precisely

  To finish link 1 (`EquivalenceFunctor (fiberJ : PairOnU U → RatBelow U)`) we still need:

      `Full (fun X : PairOnU U => fiberJObj X)`
        : ∀ {X Y : PairOnU U} (φ : (fiberJObj X) ⟶ (fiberJObj Y)),
            ∃ m : PairHom X.obj Y.obj, locMapOf pairDense_denseRoof m = φ

  Unfolding: `φ = Quotient.mk ⟨R, denom, num⟩` with `denom : R ⟶ X.obj` DENSE in `Â` and
  `num : R ⟶ Y.obj`.  We must produce a `PairHom m : X.obj → Y.obj` with
  `FractionEquiv (locFraction m) ⟨R,denom,num⟩`; taking the roof `(R, denom, id)` this reduces to
  finding `m` with **`denom ≫ m = num`** in `Â`, i.e. INVERTING `denom` in `Â` (set `m = denom⁻¹ ≫ num`).

  `dense_exactlyU_isIso` inverts a dense map only when `dom° ⊆ cod°`.  Here `dom = R`, `cod = X.obj`,
  and the dense `denom`'s SURVIVORS are exactly `R° \ U` (`PairDense.survInX`/`survDistinct`), which is
  NONEMPTY for a general apex `R`.  So `denom` is NOT directly invertible.

  The constructive fix (Freyd's, not yet formalised here) is the **apex-trimming reduction**: every
  fraction `⟨R,denom,num⟩` between exactly-`U` objects is `FractionEquiv` to one whose apex `R'` has
  `R'° ⊆ U` — drop the surviving factors of `R` (the iso `R ≅ R'` on the underlying `R.A` is the
  factor-list trim, dense since identity-on-`.A`; the trimmed `denom' : R' → X.obj` then has
  `R'° ⊆ U`, so `dense_exactlyU_isIso` inverts it).  Building the trimmed `PairObj` (its `wsupp`,
  `distinct`, and the dense iso `R ≅ R'`) is a construction on the scale of `dense_exactlyU_isIso`
  and is the precise next piece.  Once `Full fiberJ` lands:

    * `EquivalenceFunctor fiberJ` (embedding + full + repImage; repImage of `fiberJ` is the SAME
      apex-trimming applied to a `RatBelow U` object, i.e. Freyd's padding/trimming for ⊆U objects);
    * compose with `pairOnUToSlice_equivalence` ⇒ `EquivalenceFunctor (RatBelow U → Over (∏U))`
      (via `embedding_comp`/`full_comp`/`hasRepresentativeImage_comp`, S1_31);
    * `equivFunctor_preRegular` + `overPreRegular (listProd U)` ⇒ `PreRegularCategory (RatBelow U)`;
    * feed `colimitPreRegular ratBelowSystem` (preservation hyps TRIVIAL: identity-on-homs
      transitions) ⇒ `PreRegularCategory (colimitCat ratBelowSystem)`, transport along
      `ratColimToObj` (bijective-on-objects, identity-on-homs) ⇒ `PreRegularCategory A*`. -/

end Freyd

#print axioms Freyd.fiberJObj
#print axioms Freyd.fiberJ
#print axioms Freyd.fiberJ_embedding
