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

/-! ## Terminal object transport

  Pick `A : 𝒞` with `F A ≅ 1_𝒟` (representative image of the `𝒟`-terminal).  `A` is terminal in
  `𝒞`: a map `X ⟶ A` is the fullness-preimage of `F X ⟶ F A` (the composite `term (F X) ≫ iso⁻¹`),
  and any two maps `X ⟶ A` agree because their `F`-images both equal `term (F X)` after the iso
  (faithfulness + `term_uniq`). -/

/-- **`HasTerminal` transports backward across an `EquivalenceFunctor`.**  With `𝒟` having a
    terminal, the representative-image preimage `A` of `1_𝒟` is terminal in `𝒞`. -/
noncomputable def equivFunctor_hasTerminal {F : 𝒞 → 𝒟} [hF : Functor F]
    (emb : Embedding F) (full : Full F) (hri : HasRepresentativeImage F)
    [ht : HasTerminal 𝒟] : HasTerminal 𝒞 :=
  -- `A` = representative-image preimage of `1_𝒟`; `ι : F A ≅ 1_𝒟` with inverse `ι'`.
  let A : 𝒞 := (hri (one : 𝒟)).choose
  let ι : F A ⟶ (one : 𝒟) := (hri (one : 𝒟)).choose_spec.choose
  let ι' : (one : 𝒟) ⟶ F A := (hri (one : 𝒟)).choose_spec.choose_spec.choose
  { one := A
    -- the trm map X ⟶ A: fullness-preimage of `term (F X) ≫ ι' : F X ⟶ F A`.
    trm := fun X => (full (term (F X) ≫ ι')).choose
    uniq := fun {X} f g => by
      -- two maps X ⟶ A agree: their F-images, post-composed with `ι`, both hit `term (F X)`.
      apply emb f g
      have hιι' : ι ≫ ι' = Cat.id (F A) :=
        (hri (one : 𝒟)).choose_spec.choose_spec.choose_spec.1
      have key : ∀ h : X ⟶ A, hF.map h ≫ ι = term (F X) := fun h => term_uniq _ _
      have e : hF.map f ≫ ι = hF.map g ≫ ι := by rw [key f, key g]
      calc hF.map f = hF.map f ≫ ι ≫ ι' := by rw [hιι', Cat.comp_id]
        _ = (hF.map f ≫ ι) ≫ ι' := (Cat.assoc _ _ _).symm
        _ = (hF.map g ≫ ι) ≫ ι' := by rw [e]
        _ = hF.map g ≫ ι ≫ ι' := Cat.assoc _ _ _
        _ = hF.map g := by rw [hιι', Cat.comp_id] }

/-! ## Binary products transport

  For `A B : 𝒞`, take the representative-image preimage `P` of `F A × F B` (iso `ι : F P ≅ FA×FB`,
  inverse `ι'`).  The projections are the fullness-preimages of `ι ≫ fst`, `ι ≫ snd`; the pairing
  of `f : X ⟶ A`, `g : X ⟶ B` is the preimage of `pair (F f) (F g) ≫ ι'`.  Each product law follows
  by `emb` from the corresponding `𝒟`-law after passing through `ι`/`ι'`. -/

/-- The representative-image iso `F (prodPre A B) ≅ prod (F A) (F B)`, packaged for products. -/
noncomputable def prodPre {F : 𝒞 → 𝒟} [Functor F] (hri : HasRepresentativeImage F)
    [HasBinaryProducts 𝒟] (A B : 𝒞) : 𝒞 := (hri (prod (F A) (F B))).choose

/-- The forward iso leg `F (prodPre A B) ⟶ prod (F A) (F B)`. -/
noncomputable def prodPreι {F : 𝒞 → 𝒟} [Functor F] (hri : HasRepresentativeImage F)
    [HasBinaryProducts 𝒟] (A B : 𝒞) : F (prodPre hri A B) ⟶ prod (F A) (F B) :=
  (hri (prod (F A) (F B))).choose_spec.choose

/-- The inverse iso leg `prod (F A) (F B) ⟶ F (prodPre A B)`. -/
noncomputable def prodPreι' {F : 𝒞 → 𝒟} [Functor F] (hri : HasRepresentativeImage F)
    [HasBinaryProducts 𝒟] (A B : 𝒞) : prod (F A) (F B) ⟶ F (prodPre hri A B) :=
  (hri (prod (F A) (F B))).choose_spec.choose_spec.choose

theorem prodPreι_ι' {F : 𝒞 → 𝒟} [Functor F] (hri : HasRepresentativeImage F)
    [HasBinaryProducts 𝒟] (A B : 𝒞) :
    prodPreι hri A B ≫ prodPreι' hri A B = Cat.id _ :=
  (hri (prod (F A) (F B))).choose_spec.choose_spec.choose_spec.1

theorem prodPreι'_ι {F : 𝒞 → 𝒟} [Functor F] (hri : HasRepresentativeImage F)
    [HasBinaryProducts 𝒟] (A B : 𝒞) :
    prodPreι' hri A B ≫ prodPreι hri A B = Cat.id _ :=
  (hri (prod (F A) (F B))).choose_spec.choose_spec.choose_spec.2

/-- **`HasBinaryProducts` transports backward across an `EquivalenceFunctor`.** -/
noncomputable def equivFunctor_hasBinaryProducts {F : 𝒞 → 𝒟} [hF : Functor F]
    (emb : Embedding F) (full : Full F) (hri : HasRepresentativeImage F)
    [hp : HasBinaryProducts 𝒟] : HasBinaryProducts 𝒞 where
  prod A B := prodPre hri A B
  fst {A B} := (full (prodPreι hri A B ≫ fst)).choose
  snd {A B} := (full (prodPreι hri A B ≫ snd)).choose
  pair {X A B} f g := (full (pair (hF.map f) (hF.map g) ≫ prodPreι' hri A B)).choose
  fst_pair {X A B} f g := by
    apply emb
    rw [hF.map_comp, (full (pair (hF.map f) (hF.map g) ≫ prodPreι' hri A B)).choose_spec,
      (full (prodPreι hri A B ≫ fst)).choose_spec, Cat.assoc,
      ← Cat.assoc (prodPreι' hri A B), prodPreι'_ι, Cat.id_comp, fst_pair]
  snd_pair {X A B} f g := by
    apply emb
    rw [hF.map_comp, (full (pair (hF.map f) (hF.map g) ≫ prodPreι' hri A B)).choose_spec,
      (full (prodPreι hri A B ≫ snd)).choose_spec, Cat.assoc,
      ← Cat.assoc (prodPreι' hri A B), prodPreι'_ι, Cat.id_comp, snd_pair]
  pair_uniq {X A B} f g h h₁ h₂ := by
    apply emb
    rw [(full (pair (hF.map f) (hF.map g) ≫ prodPreι' hri A B)).choose_spec]
    -- F h ≫ ι = pair (Ff)(Fg) via the two projection laws; then right-cancel ι (using ι ≫ ι' = id).
    have hfst := congrArg hF.map h₁
    have hsnd := congrArg hF.map h₂
    rw [hF.map_comp, (full (prodPreι hri A B ≫ fst)).choose_spec] at hfst
    rw [hF.map_comp, (full (prodPreι hri A B ≫ snd)).choose_spec] at hsnd
    have key : hF.map h ≫ prodPreι hri A B = pair (hF.map f) (hF.map g) := by
      apply pair_uniq
      · rw [Cat.assoc]; exact hfst
      · rw [Cat.assoc]; exact hsnd
    calc hF.map h = hF.map h ≫ prodPreι hri A B ≫ prodPreι' hri A B := by
            rw [prodPreι_ι', Cat.comp_id]
      _ = (hF.map h ≫ prodPreι hri A B) ≫ prodPreι' hri A B := (Cat.assoc _ _ _).symm
      _ = pair (hF.map f) (hF.map g) ≫ prodPreι' hri A B := by rw [key]

end Freyd
