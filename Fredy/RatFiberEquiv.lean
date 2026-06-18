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

end Freyd

#print axioms Freyd.fiberJObj
#print axioms Freyd.fiberJ
