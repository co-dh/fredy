import Fredy.CatColimitRegular
import Fredy.S1_61
import Fredy.UnionFromCoproduct
import Fredy.Initial

/-!
  # The directed colimit of pre-logoi is a pre-logos

  The directed colimit `colimitCat C hC` of a `CatSystem` whose stages are each a `PreLogos`
  (§1.6) is again a `PreLogos`, once it is known to be a `RegularCategory` with binary coproducts
  (supplied by the §2.218 regular tower: `colimitPreRegular` + `colimitHasImages` +
  `colimitHasBinaryCoproducts`).

  The genuinely new content is the BOTTOM (empty-join) story.  Every stage `PreLogos` has a
  STRICT INITIAL object `0_i` (§1.61: the minimal subobject of `1`, every map into it iso).  We
  prove the single new brick

      `colimitStrictInitial : StrictCoterminator (objIncl i₀ 0_{i₀})`   (in `colimitCat`)

  — the `objIncl`-image of any one stage's strict initial is a strict initial of the colimit.  From
  it the four bottom-related `PreLogos` fields all follow cleanly with a SINGLE global bottom object
  `Z₀ := objIncl i₀ 0_{i₀}` whose domain is the same for every `A`:

    * `bottom A`            — `Z₀ ↣ A` (map out of the strict initial, monic);
    * `bottom_min`          — `Z₀ ⟶ S.dom` factors `Z₀ ⟶ A` (initial uniqueness);
    * `bottom_dom_iso`      — both bottom domains are `Z₀` (reflexivity);
    * `invImage_preserves_bottom` — the pullback of `Z₀ ↣ B` along `f` projects to `Z₀`, hence
      (strictness) is iso to `Z₀`.

  The remaining field `invImage_preserves_union` (Freyd's coherent-stability law) is threaded as a
  hypothesis: at the colimit it requires showing the colimit union / inverse-image agree with the
  germs of the per-stage operations (`objIncl_preserves_images` + `objIncl_preserves_pullbacks` +
  a coproduct-germ lemma) — a separate, heavy assembly, not the bottom content of this file.
-/

open Freyd

namespace Freyd.Colim

universe u v

variable {ι : Type u} {D : Directed ι}

/-- Transfer `IsIso` across a heterogeneous equality of morphisms whose domains and codomains
    are (propositionally) equal objects.  Used to lift `IsIso (homInclObj …)` to `IsIso g` along
    the `colimHom_as_homInclObj` alignment. -/
theorem isIso_of_heq {𝒞 : Type u} [Cat.{v} 𝒞] {P Q X Y : 𝒞} {m : P ⟶ Q} {g : X ⟶ Y}
    (hP : P = X) (hQ : Q = Y) (h : HEq m g) (hm : IsIso m) : IsIso g := by
  subst hP; subst hQ; rw [eq_of_heq h] at hm; exact hm

/-- Casting the codomain object of a stage germ does not change its stage inclusion (up to `HEq`):
    `homInclObj (castHom rfl e g)` is `HEq` to `homInclObj g`. -/
theorem homInclObj_castHom_cod_heq (C : CatSystem ι D) (hC : C.Coherent) {i : ι}
    {x y y' : C.A i} (g : x ⟶ y) (e : y = y') :
    HEq (homInclObj C hC (castHom rfl e g)) (homInclObj C hC g) := by
  subst e; rfl

/-- The chosen strict initial object of stage `i` (the minimal subobject of `1`, §1.61). -/
noncomputable def stageZero (C : CatSystem ι D) (hbot : ∀ i, PreLogos (C.A i)) (i : ι) : C.A i :=
  (minimal_subobject_of_one_is_coterminator (hbot i)).zero

/-- **The new colimit-zero brick.**  The `objIncl`-image of one stage's strict initial `0_{i₀}` is
    a STRICT COTERMINATOR (strict initial) of `colimitCat`: every colimit map into it is an iso.

    PROOF.  A map `g : X ⟶ objIncl i₀ 0_{i₀}` is, up to `HEq`, the stage inclusion `homInclObj fN`
    of a germ `fN : xX ⟶ xZ` at some stage `N` with `objIncl N xZ = objIncl i₀ 0_{i₀}`.  Pushing to
    a common stage `M'` where `xZ` becomes the stage initial `0_{M'}` (the two `objIncl`-images agree
    there, `objIncl_eq_commonStage`, and transitions preserve `0`), the pushed germ is a map INTO
    `0_{M'}`, hence iso by `any_map_to_zero_is_iso`.  `homInclObj_isIso_of_stage` lifts this stage
    iso to the colimit, and the `HEq` chain (`homInclObj_castHom_cod_heq` + `homInclObj_push_heq` +
    the alignment) transports `IsIso` to `g`. -/
theorem colimitStrictInitial (C : CatSystem ι D) (hC : C.Coherent) [Nonempty ι]
    (hbot : ∀ i, PreLogos (C.A i))
    (hinitpres : ∀ {i j : ι} (hij : D.le i j), C.F hij (stageZero C hbot i) = stageZero C hbot j)
    (i₀ : ι) :
    letI : Cat C.Obj := colimitCat C hC
    StrictCoterminator (C.objIncl i₀ (stageZero C hbot i₀)) := by
  letI : Cat C.Obj := colimitCat C hC
  intro X g
  -- align `g` to a stage inclusion `homInclObj fN`
  obtain ⟨N, xX, xZ, fN, eX, eZ, hHEq⟩ :=
    colimHom_as_homInclObj C hC (A := X) (Z := C.objIncl i₀ (stageZero C hbot i₀)) g
  -- find a stage `M'` where `xZ` becomes the stage initial `0_{M'}`
  obtain ⟨M, hNM, hi₀M⟩ := D.bound N i₀
  -- the two `objIncl`-images agree at `M`: `objIncl M (F xZ) = objIncl M 0_M`
  have hAgreeM : C.objIncl M (C.F hNM xZ) = C.objIncl M (stageZero C hbot M) := by
    rw [C.objIncl_compat hNM xZ, eZ, ← hinitpres hi₀M, C.objIncl_compat hi₀M (stageZero C hbot i₀)]
  obtain ⟨M', hMM', hZeqM'⟩ := objIncl_eq_commonStage C (C.F hNM xZ) (stageZero C hbot M) hAgreeM
  -- assemble the transition `N ≤ M'` and the codomain equality `F (N→M') xZ = 0_{M'}`
  let hNM' : D.le N M' := D.trans hNM hMM'
  have e : C.F hNM' xZ = stageZero C hbot M' := by
    calc C.F hNM' xZ = C.F hMM' (C.F hNM xZ) := by rw [C.F_trans hNM hMM']
      _ = C.F hMM' (stageZero C hbot M) := by rw [hZeqM']
      _ = stageZero C hbot M' := hinitpres hMM'
  -- the pushed germ, cast to a map INTO the stage initial `0_{M'}`
  let fN' : C.F hNM' xX ⟶ C.F hNM' xZ := (C.functF hNM').map fN
  let fM' : C.F hNM' xX ⟶ stageZero C hbot M' := castHom rfl e fN'
  -- `fM'` is a map into the stage strict initial, hence iso (§1.61)
  obtain ⟨inv, hfi1, hfi2⟩ := any_map_to_zero_is_iso (hbot M') fM'
  -- lift the stage iso to the colimit
  have hiso_fM' : @IsIso C.Obj (colimitCat C hC) _ _ (homInclObj C hC fM') :=
    homInclObj_isIso_of_stage C hC fM' inv hfi1 hfi2
  -- HEq chain: homInclObj fM' ≅ homInclObj fN' ≅ homInclObj fN ≅ g
  have H1 : HEq (homInclObj C hC fM') (homInclObj C hC fN') :=
    homInclObj_castHom_cod_heq C hC fN' e
  have H2 : HEq (homInclObj C hC fN') (homInclObj C hC fN) :=
    homInclObj_push_heq C hC hNM' fN
  have Hchain : HEq (homInclObj C hC fM') g := H1.trans (H2.trans hHEq)
  -- object equalities for the transfer
  have hP : C.objIncl M' (C.F hNM' xX) = X := (C.objIncl_compat hNM' xX).trans eX
  have hQ : C.objIncl M' (stageZero C hbot M') = C.objIncl i₀ (stageZero C hbot i₀) := by
    rw [← e, C.objIncl_compat hNM' xZ, eZ]
  exact isIso_of_heq hP hQ Hchain hiso_fM'

/-- A map out of a strict initial object is monic.  Given `u v : W ⟶ Z` with `u ≫ m = v ≫ m`:
    `u` is iso (strictness, inverse `ui`), and `ui ≫ v = ui ≫ u` (both maps OUT of the initial
    `Z`), whence `v = u ≫ (ui ≫ v) = u ≫ (ui ≫ u) = u`. -/
theorem mono_of_strict_initial {𝒞 : Type u} [Cat.{v} 𝒞] {Z A : 𝒞}
    (hInit : IsInitial Z) (hStrict : StrictCoterminator Z) (m : Z ⟶ A) : Monic m := by
  intro W u v huv
  obtain ⟨ui, hu1, hu2⟩ := hStrict u
  have key : ui ≫ v = ui ≫ u := hInit.hom_uniq (ui ≫ v) (ui ≫ u)
  refine Eq.symm ?_
  calc v = (u ≫ ui) ≫ v := by rw [hu1, Cat.id_comp]
    _ = u ≫ (ui ≫ v) := Cat.assoc _ _ _
    _ = u ≫ (ui ≫ u) := by rw [key]
    _ = u ≫ Cat.id Z := by rw [hu2]
    _ = u := Cat.comp_id _

/-- **The directed colimit of pre-logoi is a pre-logos.**

  Given the per-stage `PreLogos` data (`hbot`) and that transitions preserve the chosen stage
  initial on the nose (`hinitpres`), plus the colimit's already-established `RegularCategory`
  (`hReg`, from the §2.218 tower) and subobject unions (`hUn`, e.g.
  `hasSubobjectUnions_of_coproducts_images` from `colimitHasBinaryCoproducts` + the colimit images),
  the colimit is a `PreLogos`.

  The four bottom fields rest on the single new brick `colimitStrictInitial`; the substantive
  coherent-stability law `invImage_preserves_union` is threaded as `hinvun`. -/
noncomputable def colimitPreLogos (C : CatSystem ι D) (hC : C.Coherent) [Nonempty ι]
    (hbot : ∀ i, PreLogos (C.A i))
    (hinitpres : ∀ {i j : ι} (hij : D.le i j), C.F hij (stageZero C hbot i) = stageZero C hbot j)
    [hReg : @RegularCategory C.Obj (colimitCat C hC)]
    [hUn : @HasSubobjectUnions C.Obj (colimitCat C hC) hReg.toHasImages]
    (hinvun : letI : Cat C.Obj := colimitCat C hC
              ∀ {A B : C.Obj} (f : A ⟶ B), inverseImage_preserves_unions f) :
    @PreLogos C.Obj (colimitCat C hC) := by
  letI : Cat C.Obj := colimitCat C hC
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  let Z₀ : C.Obj := C.objIncl i₀ (stageZero C hbot i₀)
  have hSI : StrictCoterminator Z₀ := colimitStrictInitial C hC hbot hinitpres i₀
  have hInit : IsInitial Z₀ := hSI.isInitial
  exact
    { toRegularCategory := hReg
      toHasSubobjectUnions := hUn
      bottom := fun A => ⟨Z₀, hInit.out A, mono_of_strict_initial hInit hSI (hInit.out A)⟩
      bottom_min := fun {A} S => ⟨hInit.out S.dom, hInit.hom_uniq _ _⟩
      bottom_dom_iso := fun A B => isomorphic_refl Z₀
      invImage_preserves_union := fun {A B} f => hinvun f
      invImage_preserves_bottom := fun {A B} f =>
        ⟨(HasPullbacks.has f (hInit.out B)).cone.π₂, hSI _⟩ }

end Freyd.Colim
