import Fredy.RatColimit
import Fredy.RelativeCapitalization

/-! # §1.543 F — the INCLUSION directed-union `CatSystem` for `A* = ⋃_U A*|U`

  ## Why this file exists (the route, honestly)

  `RatColimit.lean` proved each fixed-`U` slice is pre-regular but got STUCK assembling the directed
  union as a `CatSystem`, because it tried BASE-CHANGE transitions `A/(∏V) → A/(∏U)`, which are only
  PSEUDO-functorial — the documented `StrictBaseChange` wall (`RelativeCapitalization.lean`: base-change
  along `1` is `X ×_D D ≅ X` but `≠ X`, and along a composite re-associates pullbacks).

  **The fix in this file: INCLUSION transitions, not base-change.**  Define Freyd's `A*|U` directly
  as the FULL SUBCATEGORY of the rational category `A* = pairRatCat` on objects whose target list is
  `⊆ U` (`RatBelow U`).  This is *exactly* Freyd's `A*|U` (§1.547, lines 4958-4961: "`A*|U` is the
  full subcategory of `A*` on objects `(A,F)` with `F° ⊆ U`"), with no padding and no base-change.

  For `U ⊆ V` (`listSubset U V`) the transition `RatBelow U → RatBelow V` is the literal INCLUSION
  `⟨X, hX⟩ ↦ ⟨X, hX.trans hUV⟩`: IDENTITY on the underlying `RatObj` *and* IDENTITY on homs (the
  `⊆`-proof is a `Prop`, the underlying object/fraction-hom is unchanged).  Consequences:

    * `F_refl`/`F_trans` hold ON THE NOSE (`Subtype.ext` + proof irrelevance of the `Prop` field).
    * `Coherent` (`refl_map`/`trans_map`, the `HEq` morphism-coherence) is TRIVIAL — the transition
      functor is the identity on homs, so its action on a morphism *is* that morphism (`HEq.rfl`).

  No `StrictBaseChange`, no `ListProjFamily`, no pseudo-functoriality.  The index is the FILTERED
  finite-set lattice `listDirected` (`bound = append`) — no transfinite limit.

  ## What this file delivers (sorry-free, committed)

    * `RatBelow U` — the fiber type + its full-subcategory `Cat` instance (fraction homs).
    * `ratBelowIncl` / `ratBelowInclFunctor` — the inclusion transition + its (identity) functoriality.
    * `ratBelowSystem : CatSystem (List Â) listDirected` — the inclusion directed system.
    * `ratBelowSystem_coherent : ratBelowSystem.Coherent` — morphism-coherence (identity ⟹ `HEq.rfl`).

  ## The remaining blocker (stated precisely, no `sorry`, no fake)

  `colimitPreRegular` consumes per-fiber `HasTerminal`/`HasBinaryProducts`/`HasEqualizers`/PTC of each
  `RatBelow U`.  `RatColimit.lean`'s `pairOnU_preRegular` proves the analogous fact for `PairOnU U` —
  but that is the fiber of `Â` (PLAIN `PairHom` homs), whereas `RatBelow U` is the fiber of the
  LOCALISATION `A*` (FRACTION homs).  These coincide only via the localisation-restricted-to-a-fiber
  equivalence `RatBelow U ≃ PairOnU U`, i.e. that the localisation functor `T : Â → A*` becomes an
  equivalence between the `F° ⊆ U` subcategories — which is NOT yet proven (no `Â ≃ A*` / fiberwise
  localisation-equivalence theorem exists in the repo; see `RatColimit`/`SliceEquivalence` notes).

  So the precise next blocker is: **`PreRegularCategory (RatBelow U)`**, reducible (via the already-built
  `equivFunctor_preRegular` + `overPreRegular`) to **`EquivalenceFunctor (RatBelow U → A/(∏U))`** — the
  fraction-fiber slice equivalence.  This file delivers the strict inclusion `CatSystem` (the part the
  StrictBaseChange wall blocked); the fraction-fiber pre-regularity is the one thing left to feed
  `colimitPreRegular` and then transport `PreRegular (colimitCat …) ≃ PreRegular A*`. -/

namespace Freyd

open Freyd.Colim

universe u

variable {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
  [HasEqualizers 𝒞] [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞]

/-! ## The fiber `A*|U = RatBelow U` — full subcategory of `A*` on `F° ⊆ U` -/

/-- **§1.547 — Freyd's `A*|U` on the nose.**  The full subcategory of the rational category
    `A* = pairRatCat` on objects whose underlying pair's target list is `⊆ U`.  Bundles a `RatObj`
    (= object of `A*`) with a proof that its underlying `PairObj`'s targets are `⊆ U`.  Homs are the
    `A*`-fraction homs of the underlying objects (FULL subcategory). -/
structure RatBelow (U : List 𝒞) where
  obj   : RatObj (pairDense_denseRoof (𝒞 := 𝒞))
  htgt  : listSubset obj.obj.targets U

/-- Homs of `RatBelow U` are the `A*`-fraction homs of the underlying objects (full subcategory).
    The category laws are inherited verbatim from `pairRatCat`. -/
instance ratBelowCat (U : List 𝒞) : Cat.{u} (RatBelow (𝒞 := 𝒞) U) where
  Hom X Y := @Cat.Hom _ pairRatCat X.obj Y.obj
  id X := @Cat.id _ pairRatCat X.obj
  comp f g := @Cat.comp _ pairRatCat _ _ _ f g
  id_comp f := @Cat.id_comp _ pairRatCat _ _ f
  comp_id f := @Cat.comp_id _ pairRatCat _ _ f
  assoc f g h := @Cat.assoc _ pairRatCat _ _ _ _ f g h

/-! ## The inclusion transition `RatBelow U → RatBelow V` for `U ⊆ V`

  IDENTITY on the underlying `RatObj` and on homs.  `F_refl`/`F_trans` are `Subtype`-style equalities
  that hold by `RatBelow.ext` (proof irrelevance of the `Prop` field `htgt`). -/

/-- `RatBelow` objects are determined by their underlying `RatObj` (`htgt` is a `Prop`). -/
@[ext] theorem RatBelow.ext {U : List 𝒞} {X Y : RatBelow (𝒞 := 𝒞) U}
    (h : X.obj = Y.obj) : X = Y := by
  obtain ⟨xo, xh⟩ := X; obtain ⟨yo, yh⟩ := Y; cases h; rfl

/-- The inclusion `RatBelow U → RatBelow V` for `U ⊆ V`: same underlying object, weakened `⊆`-proof. -/
def ratBelowIncl {U V : List 𝒞} (hUV : listSubset U V) (X : RatBelow (𝒞 := 𝒞) U) :
    RatBelow (𝒞 := 𝒞) V :=
  ⟨X.obj, fun x hx => hUV x (X.htgt x hx)⟩

@[simp] theorem ratBelowIncl_obj {U V : List 𝒞} (hUV : listSubset U V) (X : RatBelow (𝒞 := 𝒞) U) :
    (ratBelowIncl hUV X).obj = X.obj := rfl

/-- The inclusion is a functor: IDENTITY on homs (a `RatBelow U`-hom *is* an `A*`-hom of the
    underlying objects, and so is the corresponding `RatBelow V`-hom).  `map_id`/`map_comp` are
    therefore `rfl`. -/
instance ratBelowInclFunctor {U V : List 𝒞} (hUV : listSubset U V) :
    @Functor (RatBelow (𝒞 := 𝒞) U) _ (RatBelow (𝒞 := 𝒞) V) _ (ratBelowIncl hUV) where
  map {X Y} f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## The inclusion directed system `ratBelowSystem` over `listDirected` -/

/-- **§1.547 — the INCLUSION directed system of fibers `A*|U` over the finite-set lattice.**  Index
    `List Â` with `listSubset`/`listDirected` (`bound = append`); fiber `A U := RatBelow U`; transition
    `F hUV := ratBelowIncl` (identity on objects/homs).  `F_refl`/`F_trans` hold ON THE NOSE by
    `RatBelow.ext` (the `htgt` field is a `Prop`).  This is a STRICT `CatSystem` — NO base-change,
    NO `StrictBaseChange` wall. -/
def ratBelowSystem : CatSystem (List 𝒞) (listDirected (𝒞 := 𝒞)) where
  A U := RatBelow (𝒞 := 𝒞) U
  catA U := ratBelowCat U
  F hUV := ratBelowIncl hUV
  functF hUV := ratBelowInclFunctor hUV
  F_refl _ := RatBelow.ext rfl
  F_trans _ _ _ := RatBelow.ext rfl

/-- **`ratBelowSystem` is `Coherent`.**  Both morphism-coherence fields are immediate: the transition
    functor is the IDENTITY on homs, so applying it to a morphism `g` returns `g` definitionally, and
    the object-equality casts are along `RatBelow.ext rfl = rfl`, leaving `HEq.rfl`. -/
theorem ratBelowSystem_coherent : (ratBelowSystem (𝒞 := 𝒞)).Coherent where
  refl_map := fun _ => HEq.rfl
  trans_map := by intros; exact HEq.rfl

/-! ## Step 4 (object half) — `colimitCat ratBelowSystem` and `A*` have the SAME objects

  The colimit's OBJECT type is `Colimit ratBelowSystem.objSystem`: classes of `⟨U, X : RatBelow U⟩`.
  The forgetful map `⟨U, X⟩ ↦ X.obj` lands in `RatObj` (= objects of `A* = pairRatCat`) and is
  compatible with the inclusion transitions (which fix `.obj`), so it descends to the colimit
  (`ratColimToObj`).  It is a BIJECTION on objects:

    * SURJECTIVE — every `Y : RatObj` sits in the stage `RatBelow Y.obj.targets` (its targets are
      `⊆` themselves by `listDirected.refl`), and `ratColimToObj` of that stage-inclusion is `Y`
      (`ratColimToObj_objIncl_self`).
    * INJECTIVE — two stage objects with equal `.obj` already become equal in the colimit at the
      common upper bound (`bound = append`), because the inclusion transitions are IDENTITY on `.obj`
      (`ratColimToObj_inj`).

  This is the OBJECT-level half of the recognition `colimitCat ratBelowSystem ≃ A*`.  The HOM-level
  half (a `Functor` whose hom-action is "the underlying `A*`-fraction is independent of the stage",
  full + faithful) reduces, via the same identity-on-homs transitions, to the `colimHom`/`HomColim`
  quotient being a singleton-per-underlying-`A*`-hom; it is the remaining recognition residual. -/

/-- The forgetful map on stage objects: a `RatBelow U` object forgets to its underlying `A*` object. -/
def ratBelowForget {U : List 𝒞} (X : RatBelow (𝒞 := 𝒞) U) : RatObj (pairDense_denseRoof (𝒞 := 𝒞)) :=
  X.obj

/-- **The object map `colimitCat ratBelowSystem → A*`.**  Descends `⟨U, X⟩ ↦ X.obj` through the
    colimit; well-defined because the inclusion transitions fix the underlying `A*` object. -/
def ratColimToObj (c : (ratBelowSystem (𝒞 := 𝒞)).Obj) : RatObj (pairDense_denseRoof (𝒞 := 𝒞)) :=
  Colim.desc (ratBelowSystem (𝒞 := 𝒞)).objSystem (fun _ X => ratBelowForget X)
    (fun _ _ => rfl) c

@[simp] theorem ratColimToObj_objIncl {U : List 𝒞} (X : RatBelow (𝒞 := 𝒞) U) :
    ratColimToObj ((ratBelowSystem (𝒞 := 𝒞)).objIncl U X) = X.obj := rfl

/-- Every `A*`-object lies in its own targets-stage. -/
def ratBelowSelf (Y : RatObj (pairDense_denseRoof (𝒞 := 𝒞))) :
    RatBelow (𝒞 := 𝒞) Y.obj.targets :=
  ⟨Y, (listDirected (𝒞 := 𝒞)).refl Y.obj.targets⟩

/-- **`ratColimToObj` is SURJECTIVE** — every `A*`-object is the image of its own targets-stage. -/
theorem ratColimToObj_objIncl_self (Y : RatObj (pairDense_denseRoof (𝒞 := 𝒞))) :
    ratColimToObj ((ratBelowSystem (𝒞 := 𝒞)).objIncl Y.obj.targets (ratBelowSelf Y)) = Y := rfl

theorem ratColimToObj_surjective (Y : RatObj (pairDense_denseRoof (𝒞 := 𝒞))) :
    ∃ c : (ratBelowSystem (𝒞 := 𝒞)).Obj, ratColimToObj c = Y :=
  ⟨_, ratColimToObj_objIncl_self Y⟩

/-- **`ratColimToObj` is INJECTIVE.**  Two stage objects with the same underlying `A*` object are
    already identified in the colimit: include both into the common upper bound `U ++ V` (`bound`);
    the inclusion transitions fix `.obj`, so the two upper-bound objects are equal (`RatBelow.ext`),
    hence the two classes coincide (`objIncl_compat`). -/
theorem ratColimToObj_inj {c d : (ratBelowSystem (𝒞 := 𝒞)).Obj}
    (h : ratColimToObj c = ratColimToObj d) : c = d := by
  obtain ⟨U, X, rfl⟩ := Colim.incl_surjective _ c
  obtain ⟨V, Z, rfl⟩ := Colim.incl_surjective _ d
  -- `ratColimToObj (objIncl U X) = X.obj`, similarly for Z; `h : X.obj = Z.obj`.
  have hobj : X.obj = Z.obj := h
  -- common upper bound and its two inclusions
  obtain ⟨W, hUW, hVW⟩ := (listDirected (𝒞 := 𝒞)).bound U V
  have eXZ : ratBelowIncl hUW X = ratBelowIncl hVW Z := RatBelow.ext hobj
  calc (ratBelowSystem (𝒞 := 𝒞)).objIncl U X
      = (ratBelowSystem (𝒞 := 𝒞)).objIncl W (ratBelowIncl hUW X) :=
        ((ratBelowSystem (𝒞 := 𝒞)).objIncl_compat hUW X).symm
    _ = (ratBelowSystem (𝒞 := 𝒞)).objIncl W (ratBelowIncl hVW Z) := by rw [eXZ]
    _ = (ratBelowSystem (𝒞 := 𝒞)).objIncl V Z :=
        (ratBelowSystem (𝒞 := 𝒞)).objIncl_compat hVW Z

end Freyd

#print axioms Freyd.ratBelowSystem
#print axioms Freyd.ratBelowSystem_coherent
#print axioms Freyd.ratColimToObj
#print axioms Freyd.ratColimToObj_surjective
#print axioms Freyd.ratColimToObj_inj
