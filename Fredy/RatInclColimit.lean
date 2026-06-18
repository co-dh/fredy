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

/-! ## §1.543 G — dense maps localise to ISOS in `A[𝒟⁻¹]` (`locMapOf_isIso`)

  The fraction-fiber pre-regularity route needs the calculus-of-fractions fact the repo's concrete
  `ratCatOf` does not yet record: for `f` a MEMBER of the dense class `𝒟` (`hD.mem f`), its
  localisation `locMapOf hD f : RatHomOf hD A B` is an ISO in `A[𝒟⁻¹] = ratCatOf hD`.  The inverse is
  the SWAPPED span `B ←[f]— A —id→ A` (denominator `f`, dense; numerator `id`).  Both round-trips are
  single diagonal roofs into the pullback `Q = pb(f,f)`: `compFraction (loc f) (swap f)` has apex `Q`,
  denom `Q.π₁`, num `Q.π₂`, and the diagonal `Δ = Q.lift⟨A,id,id⟩` is a dense roof to `idFraction`
  (`Δ≫π₁ = Δ≫π₂ = id`).  This is the §1.547/§1.48 "`T_𝒟` inverts every member" fact for the concrete
  `ratCatOf`, sorry-free, and is exactly what lets an A*-fraction between exactly-`U` objects collapse
  to a single `Â`-hom (the denominator there is a member, so its localisation is invertible). -/

section LocIso
variable {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟)

/-- The SWAPPED span of a member `f : A → B`: `B ←[f]— A —id→ A` (denominator `f` dense, num `id`). -/
def swapFraction {A B : 𝒞} {f : A ⟶ B} (hf : 𝒟.mem f) : Fraction 𝒟 B A :=
  ⟨A, f, Cat.id A, hf⟩

/-- **§1.543 G — `compFraction (loc f) (swap f) ≈ idFraction A`.**  The composite apex is the
    pullback `Q = pb(f,f)` (num of `loc f` is `f`, denom of `swap f` is `f`), with denom `Q.π₁`,
    num `Q.π₂`.  The diagonal `Δ = Q.lift⟨A,id,id⟩` is a roof from `idFraction A` to the composite:
    `Δ≫(Q.π₁) = id` (dense) and `Δ≫(Q.π₂) = id`, matching `idFraction`'s `id`/`id`. -/
theorem compFraction_loc_swap {A B : 𝒞} {f : A ⟶ B} (hf : 𝒟.mem f) :
    FractionEquiv (compFraction 𝒟 (locFraction 𝒟 f) (swapFraction (𝒟 := 𝒟) hf)) (idFraction 𝒟 A) := by
  -- the composite span: apex Q = pb(f,f); denom = Q.π₁ ≫ id_A = Q.π₁; num = Q.π₂ ≫ id_A = Q.π₂.
  let Q := (HasPullbacks.has (locFraction 𝒟 f).num (swapFraction (𝒟 := 𝒟) hf).denom).cone
  -- Q.w : Q.π₁ ≫ f = Q.π₂ ≫ f.   (num (loc f) = f; denom (swap) = f.)
  have hQw : Q.π₁ ≫ f = Q.π₂ ≫ f := Q.w
  -- diagonal Δ : A → Q with Δ≫π₁ = id, Δ≫π₂ = id.
  let Δ : A ⟶ Q.pt := (HasPullbacks.has (locFraction 𝒟 f).num (swapFraction (𝒟 := 𝒟) hf).denom).lift
    ⟨A, Cat.id A, Cat.id A, by show Cat.id A ≫ f = Cat.id A ≫ f; rfl⟩
  have hΔ₁ : Δ ≫ Q.π₁ = Cat.id A :=
    (HasPullbacks.has (locFraction 𝒟 f).num (swapFraction (𝒟 := 𝒟) hf).denom).lift_fst _
  have hΔ₂ : Δ ≫ Q.π₂ = Cat.id A :=
    (HasPullbacks.has (locFraction 𝒟 f).num (swapFraction (𝒟 := 𝒟) hf).denom).lift_snd _
  -- roof R = A, r₁ = Δ, r₂ = id_A.
  refine ⟨A, Δ, Cat.id A, ?_, ?_, ?_⟩
  · -- (Δ ≫ composite.denom) member: composite.denom = Q.π₁ ≫ id = Q.π₁, and Δ ≫ Q.π₁ = id (member).
    show 𝒟.mem (Δ ≫ ((Q.π₁ ≫ (locFraction 𝒟 f).denom)))
    have : Δ ≫ (Q.π₁ ≫ (locFraction 𝒟 f).denom) = Cat.id A := by
      show Δ ≫ (Q.π₁ ≫ Cat.id A) = Cat.id A
      rw [← Cat.assoc, hΔ₁, Cat.id_comp]
    rw [this]; exact 𝒟.iso_mem _ ⟨Cat.id A, Cat.id_comp _, Cat.id_comp _⟩
  · -- denominators agree: Δ ≫ (Q.π₁ ≫ id) = id ≫ id.
    show Δ ≫ (Q.π₁ ≫ (locFraction 𝒟 f).denom) = Cat.id A ≫ (idFraction 𝒟 A).denom
    show Δ ≫ (Q.π₁ ≫ Cat.id A) = Cat.id A ≫ Cat.id A
    rw [← Cat.assoc, hΔ₁, Cat.id_comp]
  · -- numerators agree: Δ ≫ (Q.π₂ ≫ id) = id ≫ id.
    show Δ ≫ (Q.π₂ ≫ (swapFraction (𝒟 := 𝒟) hf).num) = Cat.id A ≫ (idFraction 𝒟 A).num
    show Δ ≫ (Q.π₂ ≫ Cat.id A) = Cat.id A ≫ Cat.id A
    rw [← Cat.assoc, hΔ₂, Cat.id_comp]

/-- **§1.543 G — `compFraction (swap f) (loc f) ≈ idFraction B`.**  Symmetric: apex `Q' = pb(id, id)`
    (num of `swap f` is `id`, denom of `loc f` is `id`), so `Q'.π₁ = Q'.π₂` after the trivial square;
    the composite is `B ←[Q'.π₁≫f]— Q' —Q'.π₂≫f→ B`, and the roof `Δ' = Q'.lift⟨B,id,id⟩` gives
    `Δ'≫(Q'.π₁≫f) = f` ... actually denom = Q'.π₁ ≫ (swap).denom = Q'.π₁ ≫ f, num = Q'.π₂ ≫ f.
    The roof `r₁ = Δ'` with `Δ'≫Q'.π₁ = Δ'≫Q'.π₂ = id` matches `idFraction B` (denom/num `id`) after
    noting `idFraction B`'s denom/num are `id`, so we need `Δ'≫(Q'.π₁≫f) = r₂≫id`; take `r₂ = f`. -/
theorem compFraction_swap_loc {A B : 𝒞} {f : A ⟶ B} (hf : 𝒟.mem f) :
    FractionEquiv (compFraction 𝒟 (swapFraction (𝒟 := 𝒟) hf) (locFraction 𝒟 f)) (idFraction 𝒟 B) := by
  -- apex Q' = pb(num(swap)=id_A, denom(loc f)=id_A); both legs land in A.
  let Q := (HasPullbacks.has (swapFraction (𝒟 := 𝒟) hf).num (locFraction 𝒟 f).denom).cone
  -- Q.w : Q.π₁ ≫ id = Q.π₂ ≫ id, i.e. Q.π₁ = Q.π₂.
  have hQw : Q.π₁ = Q.π₂ := by
    have := Q.w; show Q.π₁ = Q.π₂
    simpa [swapFraction, locFraction, Cat.comp_id] using this
  -- diagonal Δ : A → Q with Δ≫π₁ = id, Δ≫π₂ = id.
  let Δ : A ⟶ Q.pt := (HasPullbacks.has (swapFraction (𝒟 := 𝒟) hf).num (locFraction 𝒟 f).denom).lift
    ⟨A, Cat.id A, Cat.id A, by show Cat.id A ≫ Cat.id A = Cat.id A ≫ Cat.id A; rfl⟩
  have hΔ₁ : Δ ≫ Q.π₁ = Cat.id A :=
    (HasPullbacks.has (swapFraction (𝒟 := 𝒟) hf).num (locFraction 𝒟 f).denom).lift_fst _
  have hΔ₂ : Δ ≫ Q.π₂ = Cat.id A :=
    (HasPullbacks.has (swapFraction (𝒟 := 𝒟) hf).num (locFraction 𝒟 f).denom).lift_snd _
  -- composite.denom = Q.π₁ ≫ (swap).denom = Q.π₁ ≫ f;  composite.num = Q.π₂ ≫ (loc f).num = Q.π₂ ≫ f.
  -- roof R = A, r₁ = Δ, r₂ = f.
  refine ⟨A, Δ, f, ?_, ?_, ?_⟩
  · show 𝒟.mem (Δ ≫ (Q.π₁ ≫ (swapFraction (𝒟 := 𝒟) hf).denom))
    have : Δ ≫ (Q.π₁ ≫ (swapFraction (𝒟 := 𝒟) hf).denom) = f := by
      show Δ ≫ (Q.π₁ ≫ f) = f
      rw [← Cat.assoc, hΔ₁, Cat.id_comp]
    rw [this]; exact hf
  · show Δ ≫ (Q.π₁ ≫ (swapFraction (𝒟 := 𝒟) hf).denom) = f ≫ (idFraction 𝒟 B).denom
    show Δ ≫ (Q.π₁ ≫ f) = f ≫ Cat.id B
    rw [Cat.comp_id, ← Cat.assoc, hΔ₁, Cat.id_comp]
  · show Δ ≫ (Q.π₂ ≫ (locFraction 𝒟 f).num) = f ≫ (idFraction 𝒟 B).num
    show Δ ≫ (Q.π₂ ≫ f) = f ≫ Cat.id B
    rw [Cat.comp_id, ← Cat.assoc, hΔ₂, Cat.id_comp]

/-- **§1.543 G — a member of the dense class localises to an ISO.**  For `f : A → B` with `𝒟.mem f`,
    `locMapOf hD f` is an iso in `ratCatOf hD`, inverse `Quotient.mk (swapFraction hf)`.  Both
    round-trips reduce, by `Quotient.sound`, to `compFraction_loc_swap`/`compFraction_swap_loc`. -/
theorem locMapOf_isIso {A B : 𝒞} {f : A ⟶ B} (hf : 𝒟.mem f) :
    @IsIso (RatObj hD) (ratCatOf hD) ⟨A⟩ ⟨B⟩ (locMapOf hD f) := by
  refine ⟨Quotient.mk _ (swapFraction (𝒟 := 𝒟) hf), ?_, ?_⟩
  · -- locMapOf f ≫ swap = id_A
    show ratCompOf hD (locMapOf hD f) (Quotient.mk _ (swapFraction (𝒟 := 𝒟) hf)) = ratIdOf hD A
    exact Quotient.sound (compFraction_loc_swap hf)
  · show ratCompOf hD (Quotient.mk _ (swapFraction (𝒟 := 𝒟) hf)) (locMapOf hD f) = ratIdOf hD B
    exact Quotient.sound (compFraction_swap_loc hf)

end LocIso

end Freyd

#print axioms Freyd.ratBelowSystem
#print axioms Freyd.ratBelowSystem_coherent
#print axioms Freyd.ratColimToObj
#print axioms Freyd.ratColimToObj_surjective
#print axioms Freyd.ratColimToObj_inj
#print axioms Freyd.locMapOf_isIso
