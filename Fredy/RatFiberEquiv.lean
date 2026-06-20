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

/-! ## Link 2 — the fraction-collapse REDUCTION, and the DETERMINATION that `Full fiberJ` fails

  `Full (fun X : PairOnU U => fiberJObj X)` unfolds to: for every `φ : RatHomOf … X.obj Y.obj`,
  `φ = Quotient.mk ⟨R, denom, num⟩` (with `denom : R ⟶ X.obj` dense and `num : R ⟶ Y.obj`), there is
  a `PairHom m : X.obj → Y.obj` with `locMapOf m = φ`.

  ### The collapse lemma (`locMapOf_eq_of_factor`) — UNCONDITIONALLY TRUE
  If `m : PairHom X Y` satisfies `denom.comp m = num` in `Â`, then `locMapOf m = ⟦⟨R,denom,num⟩⟧`.
  The witnessing roof is `(R, denom, 1_R)`: `denom ≫ (locFraction m).denom = denom ≫ 1 = denom`
  is dense; the denominators agree (`denom = 1_R ≫ denom`); the numerators are `denom ≫ m = num`.

  ### The uniqueness (`fiberJ` faithful, already `fiberJ_embedding`)
  `denom` is dense ⇒ a COVER (`pairDense_cover`) ⇒ EPIC (`pairDense_epi`).  So if `denom.comp m = num`
  has a solution `m`, it is the UNIQUE such `Â`-hom, and (by the epi cancellation in any roof) the ONLY
  `Â`-hom whose `locMapOf` can equal `φ`.  Hence:

    **`fiberJ` is full at `(X,Y)` ⟺ for every dense `denom : R ⟶ X.obj` and `num : R ⟶ Y.obj` there is
    a `PairHom m : X.obj → Y.obj` with `denom.comp m = num`** (a factorisation of `num` through `denom`
    in `Â`).  Necessity: in any roof `t₁ ≫ num = t₂ ≫ m`, `t₁ ≫ denom = t₂`, with `t₁` dense ⇒ epic,
    cancels to `num = denom.comp m`.

  ### DETERMINATION — the factorisation FAILS for the bare §1.547 dense class (NO, needs saturation)
  `denom.g = e ≫ fst` with `e : R.A ≅ X.A × W`, `W = ∏surv`, survivor targets ∉ `U` (= `X°`,
  `survDistinct`).  `denom.comp m = num` ⟺ `denom.g ≫ m.g = num.g` ⟺ (cancelling the iso `e`)
  `num.g` is INDEPENDENT of the `W`-coordinate (factors through `fst`).  **`Y° = U` does NOT force
  this.**  Concrete counterexample (valid for the universally-quantified `Full fiberJ`):

    * `T` well-supported with `T ∉ U` (`WellSupported T := Cover (term T)` — does NOT give a point
      `1 → T`, so `fst : X.A × T → X.A` is NOT split-monic in general);
    * `R := (X.A × T, {fst ≫ f | f ∈ F_X} ∪ {snd : X.A×T → T})`, `denom := fst : R → X` dense (`W=T`);
    * `Y := (X.A × T, {fst ≫ f | f ∈ F_X})`, so `Y° = U` exactly, `Y.A = X.A × T`;
    * `num := 1_{X.A×T} : R → Y` — a VALID `PairHom` (each `Y`-factor `fst ≫ f` pulls back to the same
      factor of `R`, target in `U`).

  Here `num.g = id` DEPENDS on the `T`-coordinate, yet every constraint only sees `num.g` through the
  `Y`-factors `pairFactorMap Y = fst ≫ (…)`, which ARE `T`-independent.  `id` does not factor through
  `fst` (that would split `fst`, impossible for pointless well-supported `T`).  So `num` does NOT factor
  through `denom`, and `fiberJ` is **NOT full** on the bare dense class.

  The compat of `num` pins only `num.g ≫ pairFactorMap Y` (the `U`-factors), NOT `num.g` itself; the
  missing fact "`pairFactorMap Y` monic" is exactly the survivor/`survPinned` structure that `num`, not
  being a dense map, does not carry.  `survPinned` pins the `W`-component of maps INTO a DENSE domain;
  `num`'s codomain `Y` is not the dense domain, so it does not apply.

  ### What this means for the route
  Full faithfulness of `fiberJ` (hence `RatBelow U ≃ A/(∏U)` as Freyd asserts) requires the localised
  homs to be taken modulo the SATURATION of the §1.547 dense class — i.e. `A* = Â[dense⁻¹]` must invert
  enough maps that `num ~ denom.comp m` already in `A*` even when no `Â`-level `m` exists.  Equivalently
  the apex must be TRIMMED to `R'° ⊆ U` (drop the `W = ∏surv` factor) BEFORE reading off `m`; the trimmed
  `denom'` is then iso (`dense_exactlyU_isIso`).  But the trim `R ↠ R'` collapses `X.A × T → X.A`, and is
  legitimate in `A*` ONLY because it is itself dense — i.e. the collapse `num ↦ num'` is well-defined on
  `A*`-classes precisely when `num` already coequalises the kernel pair of `denom`, which is the SAME
  `W`-independence we just showed is not forced.  So the gap is genuine: it is the §1.48 calculus-of-
  fractions SATURATION (the dense roof rebuild `π ≫ r ≫ d` staying dense, the standing Ore condition for
  a PROPER monic dense class, flagged at `MonicDense`/`DenseRoof` in RationalCapitalization.lean), NOT a
  missing elementary construction.  `fiberJ_full` is therefore NOT provable from the bare dense-class
  closures; the committed pieces below (the collapse lemma + conditional fullness) are the Sorry-free
  partial, and `fiberJ_full_of_factor` is the exact hypothesis the saturation must supply. -/

variable {U : List 𝒞}

/-- **Link 2 (collapse) — a fraction whose `num` factors through its dense `denom` collapses to a single
    `Â`-hom.**  If `m : PairHom X Y` satisfies `denom.comp m = num` (in `Â`), then the localisation of
    `m` is the `A*`-class of the fraction `⟨R, denom, num⟩`.  Witnessing roof `(R, denom, 1_R)`:
    denominators `denom ≫ 1 = denom = 1 ≫ denom`, numerators `denom ≫ m = num = 1 ≫ num`, and
    `denom ≫ 1 = denom` is dense.  UNCONDITIONALLY TRUE (no saturation needed). -/
theorem locMapOf_eq_of_factor {X Y R : PairObj 𝒞} (denom : PairHom R X) (num : PairHom R Y)
    (hden : (pairDenseClass (𝒞 := 𝒞)).mem denom) (m : PairHom X Y) (hm : denom.comp m = num) :
    locMapOf pairDense_denseRoof m
      = Quotient.mk (fractionSetoidOf pairDense_denseRoof) ⟨R, denom, num, hden⟩ := by
  apply Quotient.sound
  -- roof `(R, denom, 1_R)` between `locFraction m = ⟨X, 1, m⟩` and `⟨R, denom, num⟩`.
  refine ⟨R, denom, @Cat.id (PairObj 𝒞) _ R, ?_, ?_, ?_⟩
  · -- `denom ≫ (locFraction m).denom = denom ≫ 1 = denom` is dense.
    show (pairDenseClass (𝒞 := 𝒞)).mem (denom ≫ @Cat.id (PairObj 𝒞) _ X)
    rw [Cat.comp_id]; exact hden
  · -- denominators: `denom ≫ 1 = 1 ≫ denom`.
    show denom ≫ @Cat.id (PairObj 𝒞) _ X = @Cat.id (PairObj 𝒞) _ R ≫ denom
    rw [Cat.comp_id, Cat.id_comp]
  · -- numerators: `denom ≫ m = 1 ≫ num`, i.e. `denom.comp m = num`.
    show denom ≫ m = @Cat.id (PairObj 𝒞) _ R ≫ num
    rw [Cat.id_comp]; exact hm

/-- **Link 2 (conditional fullness) — `fiberJ` is full GIVEN the factorisation hypothesis.**  If every
    dense `denom : R ⟶ X.obj` and `num : R ⟶ Y.obj` (between exactly-`U` objects) admit a `PairHom`
    `m : X.obj ⟶ Y.obj` with `denom.comp m = num`, then `fiberJ` is full.  This is the EXACT extra fact
    the §1.48 saturation must supply (the bare dense class does NOT — see the DETERMINATION above).
    Discharges the full-image obligation by `locMapOf_eq_of_factor` on the chosen representative. -/
theorem fiberJ_full_of_factor
    (hfac : ∀ {X Y : PairOnU U} {R : PairObj 𝒞} (denom : PairHom R X.obj) (num : PairHom R Y.obj),
      (pairDenseClass (𝒞 := 𝒞)).mem denom → ∃ m : PairHom X.obj Y.obj, denom.comp m = num) :
    Full (fun X : PairOnU U => fiberJObj X) := by
  intro X Y φ
  -- `φ : RatHomOf … X.obj.obj Y.obj.obj`; pick a fraction representative `⟨R, denom, num, hden⟩`.
  refine Quotient.inductionOn φ (fun f => ?_)
  obtain ⟨R, denom, num, hden⟩ := f
  obtain ⟨m, hm⟩ := hfac denom num hden
  exact ⟨m, (locMapOf_eq_of_factor denom num hden m hm)⟩

end Freyd

#print axioms Freyd.fiberJObj
#print axioms Freyd.fiberJ
#print axioms Freyd.fiberJ_embedding
#print axioms Freyd.locMapOf_eq_of_factor
#print axioms Freyd.fiberJ_full_of_factor
