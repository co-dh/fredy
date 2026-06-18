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

/-! ## Pullbacks transport

  For a cospan `f : A ⟶ C`, `g : B ⟶ C`, take the representative-image preimage `P` of the 𝒟
  pullback of `(F f, F g)` (iso `ι : F P ≅ Pull`, inverse `ι'`).  The cone legs are the
  fullness-preimages of `ι ≫ 𝒟π₁`, `ι ≫ 𝒟π₂`; the square commutes by `emb`.  Any 𝒞-cone `c` maps
  (via `F`) to a 𝒟-cone over `(F f, F g)`; its 𝒟-lift, transported through `ι'` and pulled back by
  fullness, is the 𝒞-lift.  Universality is `emb`/faithfulness from the 𝒟-pullback's. -/

/-- The chosen 𝒟-pullback cone of `(F f, F g)`. -/
noncomputable def pbDCone {F : 𝒞 → 𝒟} [hF : Functor F] [HasPullbacks 𝒟]
    {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) : Cone (hF.map f) (hF.map g) :=
  (HasPullbacks.has (hF.map f) (hF.map g)).cone

/-- The image, under a functor, of a 𝒞-cone over `(f, g)`, as a 𝒟-cone over `(F f, F g)`. -/
def mapCone {F : 𝒞 → 𝒟} [hF : Functor F] {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C}
    (c : Cone f g) : Cone (hF.map f) (hF.map g) :=
  ⟨F c.pt, hF.map c.π₁, hF.map c.π₂, by rw [← hF.map_comp, ← hF.map_comp, c.w]⟩

/-- **`HasPullbacks` transports backward across an `EquivalenceFunctor`.** -/
noncomputable def equivFunctor_hasPullbacks {F : 𝒞 → 𝒟} [hF : Functor F]
    (emb : Embedding F) (full : Full F) (hri : HasRepresentativeImage F)
    [hpull : HasPullbacks 𝒟] : HasPullbacks 𝒞 where
  has {A B C} f g := by
    -- `P` = preimage of the 𝒟-pullback apex; `ι : F P ≅ pbD.pt`.
    let pbD := pbDCone (F := F) f g
    let P : 𝒞 := (hri pbD.pt).choose
    let ι : F P ⟶ pbD.pt := (hri pbD.pt).choose_spec.choose
    let ι' : pbD.pt ⟶ F P := (hri pbD.pt).choose_spec.choose_spec.choose
    have hιι' : ι ≫ ι' = Cat.id _ := (hri pbD.pt).choose_spec.choose_spec.choose_spec.1
    have hι'ι : ι' ≫ ι = Cat.id _ := (hri pbD.pt).choose_spec.choose_spec.choose_spec.2
    -- the cone legs as fullness-preimages of `ι ≫ 𝒟π₁`, `ι ≫ 𝒟π₂`.
    let p₁ : P ⟶ A := (full (ι ≫ pbD.π₁)).choose
    let p₂ : P ⟶ B := (full (ι ≫ pbD.π₂)).choose
    have hp₁ : hF.map p₁ = ι ≫ pbD.π₁ := (full (ι ≫ pbD.π₁)).choose_spec
    have hp₂ : hF.map p₂ = ι ≫ pbD.π₂ := (full (ι ≫ pbD.π₂)).choose_spec
    have hw : p₁ ≫ f = p₂ ≫ g := by
      apply emb
      rw [hF.map_comp, hF.map_comp, hp₁, hp₂, Cat.assoc, Cat.assoc, pbD.w]
    refine
      { cone := ⟨P, p₁, p₂, hw⟩
        lift := fun c => (full ((HasPullbacks.has (hF.map f) (hF.map g)).lift (mapCone c) ≫ ι')).choose
        lift_fst := fun c => ?_
        lift_snd := fun c => ?_
        lift_uniq := fun c v h₁ h₂ => ?_ }
    · -- (lift c) ≫ p₁ = c.π₁ : apply `emb`, push through F.
      apply emb
      rw [hF.map_comp, (full ((HasPullbacks.has (hF.map f) (hF.map g)).lift (mapCone c) ≫ ι')).choose_spec,
        hp₁, Cat.assoc, ← Cat.assoc ι', hι'ι, Cat.id_comp]
      exact (HasPullbacks.has (hF.map f) (hF.map g)).lift_fst (mapCone c)
    · apply emb
      rw [hF.map_comp, (full ((HasPullbacks.has (hF.map f) (hF.map g)).lift (mapCone c) ≫ ι')).choose_spec,
        hp₂, Cat.assoc, ← Cat.assoc ι', hι'ι, Cat.id_comp]
      exact (HasPullbacks.has (hF.map f) (hF.map g)).lift_snd (mapCone c)
    · -- uniqueness: F v ≫ ι is the 𝒟-lift of (mapCone c), so v = the preimage.
      apply emb
      rw [(full ((HasPullbacks.has (hF.map f) (hF.map g)).lift (mapCone c) ≫ ι')).choose_spec]
      -- show F v = 𝒟-lift ≫ ι' by right-cancelling ι: F v ≫ ι = 𝒟-lift.
      have hFv₁ := congrArg hF.map h₁
      have hFv₂ := congrArg hF.map h₂
      rw [hF.map_comp, hp₁] at hFv₁
      rw [hF.map_comp, hp₂] at hFv₂
      have hlift : hF.map v ≫ ι = (HasPullbacks.has (hF.map f) (hF.map g)).lift (mapCone c) := by
        apply (HasPullbacks.has (hF.map f) (hF.map g)).lift_uniq (mapCone c)
        · show (hF.map v ≫ ι) ≫ pbD.π₁ = (mapCone c).π₁
          rw [Cat.assoc]; exact hFv₁
        · show (hF.map v ≫ ι) ≫ pbD.π₂ = (mapCone c).π₂
          rw [Cat.assoc]; exact hFv₂
      calc hF.map v = hF.map v ≫ ι ≫ ι' := by rw [hιι', Cat.comp_id]
        _ = (hF.map v ≫ ι) ≫ ι' := (Cat.assoc _ _ _).symm
        _ = (HasPullbacks.has (hF.map f) (hF.map g)).lift (mapCone c) ≫ ι' := by rw [hlift]

/-! ## Mono / cover preservation and reflection (for `PullbacksTransferCovers`) -/

/-- **An `EquivalenceFunctor` preserves monos.**  `F f` mono: take `u, v : Z ⟶ F X` with
    `u ≫ F f = v ≫ F f`.  The test object `Z` need not be in the image, so use essential
    surjectivity: `Z ≅ F W` (iso `j`, inverse `j'`).  Then `j ≫ u`, `j ≫ v : F W ⟶ F X` are
    `F`-images (fullness) `u'`, `v'`; faithfulness + mono `f` give `u' = v'`, so `j ≫ u = j ≫ v`,
    and left-cancelling the iso `j` gives `u = v`. -/
theorem equivFunctor_preserves_mono {F : 𝒞 → 𝒟} [hF : Functor F]
    (emb : Embedding F) (full : Full F) (hri : HasRepresentativeImage F)
    {X Y : 𝒞} {f : X ⟶ Y} (hf : Mono f) :
    Mono (hF.map f) := by
  intro Z u v huv
  -- Z ≅ F W
  obtain ⟨W, j, j', hjj', hj'j⟩ := hri Z
  obtain ⟨u', hu'⟩ := full (j ≫ u)
  obtain ⟨v', hv'⟩ := full (j ≫ v)
  -- u' = v' from faithfulness + mono f
  have hcomp : hF.map (u' ≫ f) = hF.map (v' ≫ f) := by
    rw [hF.map_comp, hF.map_comp, hu', hv', Cat.assoc, Cat.assoc, huv]
  have huv' : u' = v' := hf _ _ (emb _ _ hcomp)
  -- j ≫ u = j ≫ v, then left-cancel iso j
  have hju : j ≫ u = j ≫ v := by rw [← hu', ← hv', huv']
  calc u = (Cat.id Z) ≫ u := (Cat.id_comp u).symm
    _ = (j' ≫ j) ≫ u := by rw [hj'j]
    _ = j' ≫ (j ≫ u) := Cat.assoc _ _ _
    _ = j' ≫ (j ≫ v) := by rw [hju]
    _ = (j' ≫ j) ≫ v := (Cat.assoc _ _ _).symm
    _ = (Cat.id Z) ≫ v := by rw [hj'j]
    _ = v := Cat.id_comp v

/-- **A fully-faithful functor reflects covers.**  `Cover (F f)` ⟹ `Cover f`.  A monic `m` that
    `f` factors through `g` maps to a monic `F m` (preserve mono) that `F f` factors through, so
    `Cover (F f)` forces `IsIso (F m)`, reflected to `IsIso m`. -/
theorem equivFunctor_reflects_cover {F : 𝒞 → 𝒟} [hF : Functor F]
    (emb : Embedding F) (full : Full F) (hri : HasRepresentativeImage F) {X Y : 𝒞} {f : X ⟶ Y}
    (hf : Cover (hF.map f)) : Cover f := by
  intro C m g hm hgm
  apply equivFunctor_reflects_iso emb full m
  apply hf (hF.map m) (hF.map g) (equivFunctor_preserves_mono emb full hri hm)
  rw [← hF.map_comp, hgm]

/-- **A faithful functor reflects monos.**  If `F m` is mono, so is `m`: two maps `u, v` with
    `u ≫ m = v ≫ m` give `F u ≫ F m = F v ≫ F m`, so `F u = F v` (`F m` mono), so `u = v`
    (faithful). -/
theorem equivFunctor_reflects_mono {F : 𝒞 → 𝒟} [hF : Functor F]
    (emb : Embedding F) {X Y : 𝒞} {m : X ⟶ Y} (hm : Mono (hF.map m)) : Mono m := by
  intro Z u v huv
  apply emb
  apply hm
  rw [← hF.map_comp, ← hF.map_comp, huv]

/-- **An `EquivalenceFunctor` preserves covers.**  `Cover f` ⟹ `Cover (F f)`.  A monic `m : C' ⟶ F Y`
    that `F f` factors through is, after `C' ≅ F C` (ess surj), the `F`-image of a 𝒞-monic `m₀`
    (reflect mono); the factorization transports to `g₀ ≫ m₀ = f` (faithfulness), so `Cover f`
    forces `IsIso m₀`, hence `IsIso (F m₀) = IsIso (j' ≫ m)`, hence `IsIso m` (= `j ≫ (j' ≫ m)`). -/
theorem equivFunctor_preserves_cover {F : 𝒞 → 𝒟} [hF : Functor F]
    (emb : Embedding F) (full : Full F) (hri : HasRepresentativeImage F)
    {X Y : 𝒞} {f : X ⟶ Y} (hf : Cover f) : Cover (hF.map f) := by
  intro C' m g' hm hgm
  -- C' ≅ F C, with `j : F C ⟶ C'`, inverse `j' : C' ⟶ F C`.
  obtain ⟨C, j, j', hjj', hj'j⟩ := hri C'
  -- m₀ : C ⟶ Y with F m₀ = j ≫ m
  obtain ⟨m₀, hm₀⟩ := full (j ≫ m)
  -- g₀ : F X ⟶ F C with F g₀ = g' ≫ j'
  obtain ⟨g₀, hg₀⟩ := full (g' ≫ j')
  -- m₀ is mono (F m₀ = j ≫ m is iso ≫ mono)
  have hFm₀mono : Mono (hF.map m₀) := by
    rw [hm₀]
    -- `j ≫ m` mono: `j` iso (inverse `j'`), `m` mono.  Direct cancellation.
    intro Z u v huv
    have h1 : (u ≫ j) ≫ m = (v ≫ j) ≫ m := by
      rw [Cat.assoc, Cat.assoc]; exact huv
    have h2 : u ≫ j = v ≫ j := hm _ _ h1
    calc u = (u ≫ j) ≫ j' := by rw [Cat.assoc, hjj', Cat.comp_id]
      _ = (v ≫ j) ≫ j' := by rw [h2]
      _ = v := by rw [Cat.assoc, hjj', Cat.comp_id]
  have hm₀mono : Mono m₀ := equivFunctor_reflects_mono emb hFm₀mono
  -- g₀ ≫ m₀ = f (faithfulness): F(g₀ ≫ m₀) = (g' ≫ j') ≫ (j ≫ m) = g' ≫ m = F f.
  have hfac : g₀ ≫ m₀ = f := by
    apply emb
    rw [hF.map_comp, hg₀, hm₀, Cat.assoc, ← Cat.assoc j', hj'j, Cat.id_comp, hgm]
  -- Cover f ⟹ IsIso m₀ ⟹ IsIso (F m₀) = IsIso (j ≫ m)
  have hm₀iso : IsIso m₀ := hf m₀ g₀ hm₀mono hfac
  have hjm_iso : IsIso (j ≫ m) := by rw [← hm₀]; exact functor_preserves_iso m₀ hm₀iso
  -- m = j' ≫ (j ≫ m) is iso ∘ iso
  have : m = j' ≫ (j ≫ m) := by rw [← Cat.assoc, hj'j, Cat.id_comp]
  rw [this]; exact isIso_comp ⟨j, hj'j, hjj'⟩ hjm_iso

/-! ## Pullback-square preservation, and `PullbacksTransferCovers` transport -/

/-- **An `EquivalenceFunctor` preserves the `IsPullback` predicate.**  If `c` is a 𝒞-pullback of
    `(f, g)`, then `mapCone c` is a 𝒟-pullback of `(F f, F g)`.  Any 𝒟-cone `d` over `(F f, F g)`
    has `d.pt ≅ F W` (ess surj); its legs pull back (fullness) to a 𝒞-cone over `(f, g)` whose
    unique 𝒞-lift, transported through `F` and the iso, gives the unique 𝒟-lift. -/
theorem equivFunctor_preserves_isPullback {F : 𝒞 → 𝒟} [hF : Functor F]
    (emb : Embedding F) (full : Full F) (hri : HasRepresentativeImage F)
    {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C} {c : Cone f g} (hc : c.IsPullback) :
    (mapCone (F := F) c).IsPullback := by
  intro d
  -- d.pt ≅ F W (j : F W ⟶ d.pt, inverse j')
  obtain ⟨W, j, j', hjj', hj'j⟩ := hri d.pt
  -- 𝒞-cone over (f,g): legs are fullness-preimages of `j ≫ d.π₁`, `j ≫ d.π₂`.
  obtain ⟨q₁, hq₁⟩ := full (j ≫ d.π₁)
  obtain ⟨q₂, hq₂⟩ := full (j ≫ d.π₂)
  have hqw : q₁ ≫ f = q₂ ≫ g := by
    apply emb
    rw [hF.map_comp, hF.map_comp, hq₁, hq₂, Cat.assoc, Cat.assoc, d.w]
  obtain ⟨t, ⟨ht₁, ht₂⟩, htuniq⟩ := hc ⟨W, q₁, q₂, hqw⟩
  -- the 𝒟-lift: `j' ≫ F t : d.pt ⟶ F c.pt`.
  refine ⟨j' ≫ hF.map t, ⟨?_, ?_⟩, ?_⟩
  · -- (j' ≫ F t) ≫ (mapCone c).π₁ = d.π₁, i.e. = F c.π₁; reduces through F t ≫ F c.π₁ = F q₁ = j ≫ dπ₁.
    show (j' ≫ hF.map t) ≫ hF.map c.π₁ = d.π₁
    rw [Cat.assoc, ← hF.map_comp, ht₁, hq₁, ← Cat.assoc, hj'j, Cat.id_comp]
  · show (j' ≫ hF.map t) ≫ hF.map c.π₂ = d.π₂
    rw [Cat.assoc, ← hF.map_comp, ht₂, hq₂, ← Cat.assoc, hj'j, Cat.id_comp]
  · -- uniqueness: any v with v ≫ (mapCone c).π_i = d.π_i has `j ≫ v = F t₀` for a 𝒞-lift t₀ = t.
    intro v hv₁ hv₂
    obtain ⟨t₀, ht₀⟩ := full (j ≫ v)
    -- t₀ is a 𝒞-lift of the cone ⟨W, q₁, q₂⟩, so t₀ = t.
    have e₀ : t₀ = t := by
      apply htuniq
      · apply emb; rw [hF.map_comp, ht₀, hq₁, Cat.assoc]
        exact congrArg (j ≫ ·) hv₁
      · apply emb; rw [hF.map_comp, ht₀, hq₂, Cat.assoc]
        exact congrArg (j ≫ ·) hv₂
    -- v = j' ≫ (j ≫ v) = j' ≫ F t₀ = j' ≫ F t.
    calc v = j' ≫ (j ≫ v) := by rw [← Cat.assoc, hj'j, Cat.id_comp]
      _ = j' ≫ hF.map t₀ := by rw [ht₀]
      _ = j' ≫ hF.map t := by rw [e₀]

/-- **`PullbacksTransferCovers` transports backward across an `EquivalenceFunctor`** (given `𝒟`
    pre-regular, so the obligation can be discharged in `𝒟`).  A 𝒞-pullback `c` of `(f, g)` with
    `Cover f` maps to the 𝒟-pullback `mapCone c` of `(F f, F g)` with `Cover (F f)`; PTC in `𝒟`
    gives `Cover (F c.π₂)`, reflected to `Cover c.π₂`. -/
theorem equivFunctor_pullbacksTransferCovers {F : 𝒞 → 𝒟} [hF : Functor F]
    (emb : Embedding F) (full : Full F) (hri : HasRepresentativeImage F)
    [HasBinaryProducts 𝒟] [HasPullbacks 𝒟] [PullbacksTransferCovers 𝒟] :
    PullbacksTransferCovers 𝒞 where
  pullbacks_transfer_covers {A B C f g} c hc hf := by
    apply equivFunctor_reflects_cover emb full hri (f := c.π₂)
    have hFpb : (mapCone (F := F) c).IsPullback :=
      equivFunctor_preserves_isPullback emb full hri hc
    show Cover (mapCone (F := F) c).π₂
    exact PullbacksTransferCovers.pullbacks_transfer_covers (mapCone c) hFpb
      (equivFunctor_preserves_cover emb full hri hf)

end Freyd
