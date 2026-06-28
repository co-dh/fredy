import Fredy.CatColimitRegular
import Fredy.S1_62
import Fredy.UnionFromCoproduct
import Fredy.ColimitPreLogos

/-!
  # Disjoint binary coproducts for the directed colimit of categories

  The directed colimit `colimitCat C hC` of a `CatSystem` of regular categories is, when each
  stage is a `DisjointBinaryCoproduct` (§1.621/§1.623, the faithful positivity data), again a
  `DisjointBinaryCoproduct` — this is the positive-pre-logos rung needed by the §2.218 regular
  capitalization tower.

  The assembly splits into two parts:

  * `disjointBinaryCoproduct_of_disjoint` (GENERIC): in any pre-logos with binary coproducts whose
    injections are monic and disjoint (`inl ∩ inr ≤ ⊥`), the remaining §1.621 field
    `inl ∪ inr = ⊤` is AUTOMATIC — it is `image (case inl inr) = image id = ⊤` read through the
    union lattice.  This is the genuinely new, fully-proven content.

  * `colimitDisjointBinaryCoproduct` (COLIMIT): instantiates the generic constructor at
    `colimitCat C hC`.  The regular+union+bottom layer is the `[PreLogos]` hypothesis (supplied by
    `colimitPreRegular` + `colimitHasImages` + the bottom infrastructure); the binary coproducts are
    `colimitHasBinaryCoproducts` sourced from the per-stage disjoint coproducts; the two genuinely
    colimit-specific facts — the colimit injections are monic (`colimit_inl_monic`/`colimit_inr_monic`)
    and disjoint (`colimit_inl_inter_inr`) — are now DISCHARGED INTERNALLY from the per-stage `hdisj`
    by germ-transport, using the keystone `objIncl_preserves_coproducts` /
    `objIncl_preserves_pullbacks` and the colimit strict initial `colimitStrictInitial`.  So
    `colimitDisjointBinaryCoproduct` takes NO disjointness hypotheses, only the per-stage
    finite-limit / mono / initial bundles the §2.218 regular tower already supplies.
-/

open Freyd
namespace Freyd

universe u v

/-- **Generic disjoint-coproduct constructor.**  A `PreLogos` with binary coproducts whose
    injections are monic (`hl`/`hr`) and disjoint (`hinter : inl ∩ inr ≤ ⊥`) is a
    `DisjointBinaryCoproduct`.  The fourth §1.621 field `inl ∪ inr = ⊤` is proven here once and for
    all: `case inl inr = id` (copairing of the injections, `case_uniq`), so `inl, inr` factor
    through the image `image (case inl inr)`, which is therefore an upper bound of `inlSub, inrSub`;
    the union — their LEAST upper bound — lies below it (`union_min`), while `case inl inr = id`
    factors through `union.arr` (the copairing of the two union inclusions), so the image lies below
    the union (`image_min`); and `entire` factors through the image via `image.lift`.  Chaining,
    `entire ≤ union`. -/
def disjointBinaryCoproduct_of_disjoint {𝒞 : Type u} [Cat.{v} 𝒞]
    [hPL : PreLogos 𝒞] [hCop : HasBinaryCoproducts 𝒞]
    (hl : ∀ {A B : 𝒞}, Monic (HasBinaryCoproducts.inl (A := A) (B := B)))
    (hr : ∀ {A B : 𝒞}, Monic (HasBinaryCoproducts.inr (A := A) (B := B)))
    (hinter : ∀ {A B : 𝒞},
      Subobject.le (Subobject.inter (inlSub (𝒞 := 𝒞) (A := A) (B := B) hl)
                                    (inrSub (𝒞 := 𝒞) (A := A) (B := B) hr))
                   (PreLogos.bottom (HasBinaryCoproducts.coprod A B))) :
    DisjointBinaryCoproduct 𝒞 where
  toPositivePreLogos := { toPreLogos := hPL, toHasBinaryCoproducts := hCop }
  inl_monic := hl
  inr_monic := hr
  inl_inter_inr := hinter
  inl_union_inr := by
    intro A B
    -- the injections, their copairing `c = case inl inr = id`, and the union `U`.
    let inl := HasBinaryCoproducts.inl (A := A) (B := B)
    let inr := HasBinaryCoproducts.inr (A := A) (B := B)
    let c : HasBinaryCoproducts.coprod A B ⟶ HasBinaryCoproducts.coprod A B :=
      HasBinaryCoproducts.case inl inr
    have hc_id : c = Cat.id (HasBinaryCoproducts.coprod A B) :=
      (HasBinaryCoproducts.case_uniq inl inr (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)).symm
    let U := HasSubobjectUnions.union (inlSub (𝒞 := 𝒞) (A := A) (B := B) hl)
                                      (inrSub (𝒞 := 𝒞) (A := A) (B := B) hr)
    -- `inl`, `inr` factor through `U.arr` (they are below the union).
    obtain ⟨a, ha⟩ := HasSubobjectUnions.union_left (inlSub (𝒞 := 𝒞) (A := A) (B := B) hl)
                                                     (inrSub (𝒞 := 𝒞) (A := A) (B := B) hr)
    obtain ⟨b, hb⟩ := HasSubobjectUnions.union_right (inlSub (𝒞 := 𝒞) (A := A) (B := B) hl)
                                                     (inrSub (𝒞 := 𝒞) (A := A) (B := B) hr)
    -- `case a b ≫ U.arr = case (a ≫ U.arr) (b ≫ U.arr) = case inl inr = c`, so `U` allows `c`.
    have hAllow : Allows U c := by
      refine ⟨HasBinaryCoproducts.case a b, ?_⟩
      refine HasBinaryCoproducts.case_uniq inl inr (HasBinaryCoproducts.case a b ≫ U.arr)
        ?_ ?_
      · rw [← Cat.assoc, HasBinaryCoproducts.case_inl]; exact ha
      · rw [← Cat.assoc, HasBinaryCoproducts.case_inr]; exact hb
    -- `image c ≤ U` (minimality of the image) and `entire ≤ image c` (via `image.lift c`).
    have him_le : (image c).le U := image_min c U hAllow
    have hentire : (Subobject.entire (HasBinaryCoproducts.coprod A B)).le (image c) :=
      ⟨image.lift c, by
        show image.lift c ≫ (image c).arr = Cat.id (HasBinaryCoproducts.coprod A B)
        rw [image.lift_fac]; exact hc_id⟩
    exact Subobject.le_trans hentire him_le

/-! ## Generic discharge lemmas for the colimit disjointness facts

  These are instance-free §1.4/§1.5/§1.61 facts; none mentions the colimit.  They let the
  colimit proof reduce each of the three disjointness fields (`inl`/`inr` monic, `inl ∩ inr ≤ ⊥`)
  to per-stage data transported by germs. -/

/-- A LEFT FACTOR of a monic is monic: if `f ≫ g` is left-cancellable, so is `f`. -/
theorem monic_of_comp_monic {𝒞 : Type u} [Cat.{v} 𝒞] {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : Monic (f ≫ g)) : Monic f :=
  fun u v huv => h u v (by rw [← Cat.assoc, ← Cat.assoc, huv])

/-- **`inl` is monic whenever there is ANY monic `j₁ : A ⟶ P` and any `j₂ : B ⟶ P`.**  The
    copairing `case j₁ j₂` satisfies `inl ≫ case j₁ j₂ = j₁` (`case_inl`), so `inl` is a left
    factor of the monic `j₁`. -/
theorem monic_inl_of_factor {𝒞 : Type u} [Cat.{v} 𝒞] [HasBinaryCoproducts 𝒞] {A B P : 𝒞}
    (j₁ : A ⟶ P) (j₂ : B ⟶ P) (hj₁ : Monic j₁) :
    Monic (HasBinaryCoproducts.inl (A := A) (B := B)) := by
  refine monic_of_comp_monic (g := HasBinaryCoproducts.case j₁ j₂) ?_
  rw [HasBinaryCoproducts.case_inl]; exact hj₁

/-- Dual of `monic_inl_of_factor`: `inr` is monic whenever there is any `j₁ : A ⟶ P` and a monic
    `j₂ : B ⟶ P`. -/
theorem monic_inr_of_factor {𝒞 : Type u} [Cat.{v} 𝒞] [HasBinaryCoproducts 𝒞] {A B P : 𝒞}
    (j₁ : A ⟶ P) (j₂ : B ⟶ P) (hj₂ : Monic j₂) :
    Monic (HasBinaryCoproducts.inr (A := A) (B := B)) := by
  refine monic_of_comp_monic (g := HasBinaryCoproducts.case j₁ j₂) ?_
  rw [HasBinaryCoproducts.case_inr]; exact hj₂

/-- A subobject with an INITIAL domain lies below every subobject of the same object. -/
theorem subobject_le_of_initial_dom {𝒞 : Type u} [Cat.{v} 𝒞] {B : 𝒞} {S T : Subobject 𝒞 B}
    (h : IsInitial S.dom) : S.le T :=
  ⟨h.out T.dom, h.hom_uniq _ _⟩

/-- Initiality transports backwards along an iso: if `m : X ⟶ Z` is iso and `Z` is initial then
    `X` is initial. -/
theorem isInitial_of_iso {𝒞 : Type u} [Cat.{v} 𝒞] {X Z : 𝒞} (m : X ⟶ Z) (hm : IsIso m)
    (hZ : IsInitial Z) : IsInitial X := by
  obtain ⟨mi, h1, _⟩ := hm
  intro Y
  refine ⟨m ≫ hZ.out Y, fun g => ?_⟩
  calc g = (m ≫ mi) ≫ g := by rw [h1, Cat.id_comp]
    _ = m ≫ (mi ≫ g) := Cat.assoc _ _ _
    _ = m ≫ (mi ≫ (m ≫ hZ.out Y)) := by rw [hZ.hom_uniq (mi ≫ g) (mi ≫ (m ≫ hZ.out Y))]
    _ = (m ≫ mi) ≫ (m ≫ hZ.out Y) := (Cat.assoc _ _ _).symm
    _ = m ≫ hZ.out Y := by rw [h1, Cat.id_comp]

/-- In a `PreLogos`, the bottom subobject's domain is a STRICT coterminator (every map into it is
    an iso): it is iso to the strict zero `0` (`bottom_dom_iso`), and `any_map_to_zero_is_iso`. -/
theorem prelogos_bottom_strict {𝒞 : Type u} [Cat.{v} 𝒞] (h : PreLogos 𝒞) (B : 𝒞) :
    StrictCoterminator (h.bottom B).dom := by
  intro X f
  obtain ⟨e, ei, hei1, hei2⟩ := h.bottom_dom_iso B h.toHasTerminal.one
  have hfe : IsIso (f ≫ e) := any_map_to_zero_is_iso h (f ≫ e)
  have hf_eq : f = (f ≫ e) ≫ ei := by rw [Cat.assoc, hei1, Cat.comp_id]
  rw [hf_eq]; exact isIso_comp hfe ⟨e, hei2, hei1⟩

/-- In a `PreLogos`, the bottom subobject's domain is INITIAL. -/
theorem prelogos_bottom_initial {𝒞 : Type u} [Cat.{v} 𝒞] (h : PreLogos 𝒞) (B : 𝒞) :
    IsInitial (h.bottom B).dom := by
  obtain ⟨e, ei, hei1, hei2⟩ := h.bottom_dom_iso B h.toHasTerminal.one
  letI : HasCoterminator 𝒞 := minimal_subobject_of_one_is_coterminator h
  exact isInitial_of_iso e ⟨ei, hei1, hei2⟩ HasCoterminator.coterm_isInitial

/-- **The §1.432 pullback of `(inl, inr)` is INITIAL in a disjoint binary coproduct.**  Stage
    fact: §1.621 disjointness `inl ∩ inr ≤ ⊥` gives a map from the pullback into the strict-initial
    bottom, so the pullback is iso to it, hence initial.  The pullback used is the
    `products_equalizers_implies_pullbacks` one (the choice `objIncl_preserves_pullbacks` uses); it
    is bridged to the ambient `HasPullbacks` pullback of §1.621 by pullback uniqueness. -/
theorem disjoint_pullback_initial {𝒞 : Type u} [Cat.{v} 𝒞] (hD : DisjointBinaryCoproduct 𝒞)
    (hpp : HasBinaryProducts 𝒞) (hee : HasEqualizers 𝒞) {A B : 𝒞} :
    letI := hpp; letI := hee
    IsInitial (@products_equalizers_implies_pullbacks 𝒞 _ hpp hee _ _ _
        (@HasBinaryCoproducts.inl 𝒞 _ hD.toHasBinaryCoproducts A B)
        (@HasBinaryCoproducts.inr 𝒞 _ hD.toHasBinaryCoproducts A B)).cone.pt := by
  letI : DisjointBinaryCoproduct 𝒞 := hD
  -- pin `HasPullbacks` to `hD.toHasPullbacks` (the path the §1.621 field uses); the diamond would
  -- otherwise pick `exactPullbacks` and break the `le_inter`/`inl_inter_inr` match.
  letI : HasPullbacks 𝒞 := hD.toHasPullbacks
  letI := hpp; letI := hee
  let inl := @HasBinaryCoproducts.inl 𝒞 _ hD.toHasBinaryCoproducts A B
  let inr := @HasBinaryCoproducts.inr 𝒞 _ hD.toHasBinaryCoproducts A B
  -- the §1.432 pullback of the two injections, and its inclusion into the coproduct as a subobject
  let pdq := @products_equalizers_implies_pullbacks 𝒞 _ hpp hee _ _ _ inl inr
  have hπ₁mono : Monic pdq.cone.π₁ := pdq.cone_isPullback.pi1_monic hD.inr_monic
  have harr_mono : Monic (pdq.cone.π₁ ≫ inl) := fun u v huv =>
    hπ₁mono u v (hD.inl_monic (u ≫ pdq.cone.π₁) (v ≫ pdq.cone.π₁) (by rw [Cat.assoc, Cat.assoc]; exact huv))
  let Spdq : Subobject 𝒞 (HasBinaryCoproducts.coprod A B) := ⟨pdq.cone.pt, pdq.cone.π₁ ≫ inl, harr_mono⟩
  -- `Spdq ≤ inl`, `Spdq ≤ inr`, hence `Spdq ≤ inl ∩ inr ≤ ⊥` (§1.621 disjointness)
  have hSpdq_inl : Spdq.le (inlSub (𝒞 := 𝒞) (A := A) (B := B) hD.inl_monic) :=
    ⟨pdq.cone.π₁, rfl⟩
  have hSpdq_inr : Spdq.le (inrSub (𝒞 := 𝒞) (A := A) (B := B) hD.inr_monic) :=
    ⟨pdq.cone.π₂, pdq.cone.w.symm⟩
  have hSpdq_bot : Spdq.le (PreLogos.bottom (HasBinaryCoproducts.coprod A B)) :=
    Subobject.le_trans (Subobject.le_inter hSpdq_inl hSpdq_inr) (hD.inl_inter_inr (A := A) (B := B))
  -- the witnessing map `pdq.pt → ⊥.dom` is iso (`⊥.dom` strict initial), so `pdq.pt` is initial
  obtain ⟨m, _⟩ := hSpdq_bot
  exact isInitial_of_iso m
    (prelogos_bottom_strict hD.toPreLogos _ m)
    (prelogos_bottom_initial hD.toPreLogos _)

end Freyd

namespace Freyd.Colim

variable {ι : Type u} {D : Directed ι}

/-- The colimit's binary coproducts, sourced from the per-stage DISJOINT coproducts.  This is
    `colimitHasBinaryCoproducts` fed `hcop i := (hdisj i).toHasBinaryCoproducts`, so the coproduct
    object/injections of the colimit are built from the per-stage positive coproducts.  `hcoppres`/
    `hcoppres_case` are the (joint-monic + copairing) preservation premises of the brick. -/
noncomputable def colimitCoprodOfDisjoint
    (C : CatSystem ι D) (hC : C.Coherent)
    (hdisj : ∀ i, DisjointBinaryCoproduct (C.A i))
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : C.F hij a ⟶ z) (q : C.F hij b ⟶ z),
        ∃ r : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q) :
    @HasBinaryCoproducts C.Obj (colimitCat C hC) :=
  colimitHasBinaryCoproducts C hC (fun i => (hdisj i).toHasBinaryCoproducts) hcoppres hcoppres_case

/-- **Two colimit objects live at one stage.**  Push the `colimOut` representatives of `A` and `B`
    to a common bound `k`; `objIncl_compat` + `colimOut_spec` make their `objIncl k`-images equal to
    `A`, `B`.  (The fresh `k, xA', xB'` let the caller `subst` `A, B` to `objIncl`-objects.) -/
theorem objIncl_pair_commonStage (C : CatSystem ι D) (A B : C.Obj) :
    ∃ (k : ι) (xA' xB' : C.A k), C.objIncl k xA' = A ∧ C.objIncl k xB' = B := by
  obtain ⟨k, hAk, hBk⟩ := D.bound (colimOut C A).1 (colimOut C B).1
  exact ⟨k, C.F hAk (colimOut C A).2, C.F hBk (colimOut C B).2,
    (C.objIncl_compat hAk (colimOut C A).2).trans (colimOut_spec C A),
    (C.objIncl_compat hBk (colimOut C B).2).trans (colimOut_spec C B)⟩

/-- **The colimit's left injection is monic.**  Reduce arbitrary `A, B` to a common stage `k`; the
    per-stage germ injection `homInclObj inl` is monic (`homInclObj_mono_of_stage`, since transitions
    preserve the stage mono `(hdisj k).inl_monic`), and the colimit `inl` is a left factor of it via
    `case (homInclObj inl) (homInclObj inr)` (`monic_inl_of_factor`). -/
theorem colimit_inl_monic (C : CatSystem ι D) (hC : C.Coherent)
    (hdisj : ∀ i, DisjointBinaryCoproduct (C.A i)) (hmono : TransMono C)
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : C.F hij a ⟶ z) (q : C.F hij b ⟶ z),
        ∃ r : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q) :
    letI : Cat C.Obj := colimitCat C hC
    letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
    ∀ {A B : C.Obj}, Monic (HasBinaryCoproducts.inl (A := A) (B := B)) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
  intro A B
  obtain ⟨k, xA', xB', hA, hB⟩ := objIncl_pair_commonStage C A B
  subst hA; subst hB
  refine monic_inl_of_factor
    (homInclObj C hC ((hdisj k).toHasBinaryCoproducts.inl (A := xA') (B := xB')))
    (homInclObj C hC ((hdisj k).toHasBinaryCoproducts.inr (A := xA') (B := xB'))) ?_
  exact homInclObj_mono_of_stage C hC ((hdisj k).toHasBinaryCoproducts.inl (A := xA') (B := xB'))
    (fun {j} hij z u v huv => hmono hij (hdisj k).inl_monic u v huv)

/-- **The colimit's right injection is monic** (dual of `colimit_inl_monic`). -/
theorem colimit_inr_monic (C : CatSystem ι D) (hC : C.Coherent)
    (hdisj : ∀ i, DisjointBinaryCoproduct (C.A i)) (hmono : TransMono C)
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : C.F hij a ⟶ z) (q : C.F hij b ⟶ z),
        ∃ r : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q) :
    letI : Cat C.Obj := colimitCat C hC
    letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
    ∀ {A B : C.Obj}, Monic (HasBinaryCoproducts.inr (A := A) (B := B)) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
  intro A B
  obtain ⟨k, xA', xB', hA, hB⟩ := objIncl_pair_commonStage C A B
  subst hA; subst hB
  refine monic_inr_of_factor
    (homInclObj C hC ((hdisj k).toHasBinaryCoproducts.inl (A := xA') (B := xB')))
    (homInclObj C hC ((hdisj k).toHasBinaryCoproducts.inr (A := xA') (B := xB'))) ?_
  exact homInclObj_mono_of_stage C hC ((hdisj k).toHasBinaryCoproducts.inr (A := xA') (B := xB'))
    (fun {j} hij z u v huv => hmono hij (hdisj k).inr_monic u v huv)

/-- **The colimit injections are disjoint:** `inl ∩ inr ≤ ⊥`.

    Reduce arbitrary `A, B` to a common stage `k`.  The intersection's domain is the colimit
    pullback of `(inl, inr)`.  Via the keystone comparison `φ = case (homInclObj inl) (homInclObj inr)`
    (`inl ≫ φ = homInclObj inlₖ`, `inr ≫ φ = homInclObj inrₖ`) it is a pullback of the germ
    injections, hence (`objIncl_preserves_pullbacks` mediator) maps to `objIncl k (pdqₖ.pt)`.  The
    §1.432 stage pullback `pdqₖ.pt` is INITIAL in the stage (`disjoint_pullback_initial`, from the
    per-stage §1.621 disjointness), so it maps to the strict-initial `Zₖ = objIncl k 0ₖ`
    (`colimitStrictInitial`).  Therefore the intersection's domain maps to the colimit strict initial,
    is itself initial, and lies below `⊥`. -/
theorem colimit_inl_inter_inr (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (hdisj : ∀ i, DisjointBinaryCoproduct (C.A i)) (hmono : TransMono C)
    (hbot : ∀ i, PreLogos (C.A i))
    (hinitpres : ∀ {i j : ι} (hij : D.le i j), C.F hij (stageZero C hbot i) = stageZero C hbot j)
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k)
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : C.F hij a ⟶ z) (q : C.F hij b ⟶ z),
        ∃ r : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q)
    [hPL : @PreLogos C.Obj (colimitCat C hC)]
    (hl : letI : Cat C.Obj := colimitCat C hC
          letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
          ∀ {A B : C.Obj}, Monic (HasBinaryCoproducts.inl (A := A) (B := B)))
    (hr : letI : Cat C.Obj := colimitCat C hC
          letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
          ∀ {A B : C.Obj}, Monic (HasBinaryCoproducts.inr (A := A) (B := B))) :
    letI : Cat C.Obj := colimitCat C hC
    letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
    ∀ {A B : C.Obj},
      Subobject.le (Subobject.inter (inlSub (𝒞 := C.Obj) (A := A) (B := B) hl)
                                    (inrSub (𝒞 := C.Obj) (A := A) (B := B) hr))
                   (PreLogos.bottom (HasBinaryCoproducts.coprod A B)) := by
  letI iCat : Cat C.Obj := colimitCat C hC
  letI iCop : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
  letI iBP : HasBinaryProducts C.Obj := hPL.toHasBinaryProducts
  intro A B
  refine subobject_le_of_initial_dom ?_
  obtain ⟨k, xA', xB', hA, hB⟩ := objIncl_pair_commonStage C A B
  subst hA; subst hB
  -- the colimit pullback underlying the intersection
  let pbC := HasPullbacks.has (inlSub (𝒞 := C.Obj) (A := C.objIncl k xA') (B := C.objIncl k xB') hl).arr
                              (inrSub (𝒞 := C.Obj) (A := C.objIncl k xA') (B := C.objIncl k xB') hr).arr
  show IsInitial pbC.cone.pt
  -- stage injections and the keystone comparison `φ`
  let inl := HasBinaryCoproducts.inl (A := C.objIncl k xA') (B := C.objIncl k xB')
  let inr := HasBinaryCoproducts.inr (A := C.objIncl k xA') (B := C.objIncl k xB')
  let inlS := (hdisj k).toHasBinaryCoproducts.inl (A := xA') (B := xB')
  let inrS := (hdisj k).toHasBinaryCoproducts.inr (A := xA') (B := xB')
  let φ := @HasBinaryCoproducts.case C.Obj iCat iCop
    (C.objIncl k ((hdisj k).toHasBinaryCoproducts.coprod xA' xB'))
    (C.objIncl k xA') (C.objIncl k xB') (homInclObj C hC inlS) (homInclObj C hC inrS)
  have e_inl : inl ≫ φ = homInclObj C hC inlS :=
    @HasBinaryCoproducts.case_inl C.Obj iCat iCop
      (C.objIncl k ((hdisj k).toHasBinaryCoproducts.coprod xA' xB'))
      (C.objIncl k xA') (C.objIncl k xB') (homInclObj C hC inlS) (homInclObj C hC inrS)
  have e_inr : inr ≫ φ = homInclObj C hC inrS :=
    @HasBinaryCoproducts.case_inr C.Obj iCat iCop
      (C.objIncl k ((hdisj k).toHasBinaryCoproducts.coprod xA' xB'))
      (C.objIncl k xA') (C.objIncl k xB') (homInclObj C hC inlS) (homInclObj C hC inrS)
  -- the intersection's domain is a pullback of the germ injections
  have hgermPB := objIncl_preserves_pullbacks C hC ht htpres hp hpres hpres_pair he hepres hepres_lift
    k inlS inrS
  have hw : pbC.cone.π₁ ≫ inl = pbC.cone.π₂ ≫ inr := pbC.cone.w
  let interCone' : Cone (homInclObj C hC inlS) (homInclObj C hC inrS) :=
    { pt := pbC.cone.pt, π₁ := pbC.cone.π₁, π₂ := pbC.cone.π₂,
      w := by rw [← e_inl, ← e_inr, ← Cat.assoc, ← Cat.assoc, hw] }
  obtain ⟨m1, _, _⟩ := hgermPB interCone'
  -- the stage pullback is initial; map its `objIncl` into the colimit strict initial
  have hpdqInit := disjoint_pullback_initial (hdisj k) (hp k) (he k) (A := xA') (B := xB')
  have hZk : StrictCoterminator (C.objIncl k (stageZero C hbot k)) :=
    colimitStrictInitial C hC hbot hinitpres k
  refine isInitial_of_iso (m1 ≫ homInclObj C hC (hpdqInit.out (stageZero C hbot k)))
    (hZk _) hZk.isInitial

/-- **The directed colimit of disjoint binary coproducts is a `DisjointBinaryCoproduct`.**

    Layers:
    * `[hPL]` — the colimit is a pre-logos (regular + subobject unions + bottom).  Supplied at the
      call site by `colimitPreRegular` + `colimitHasImages` + the bottom infrastructure, exactly as
      the §2.218 regular tower supplies `RegularCategory`.
    * `colimitCoprodOfDisjoint` — binary coproducts, built from the per-stage disjoint coproducts via
      `colimitHasBinaryCoproducts` (premises `hcoppres`/`hcoppres_case`).
    * the §1.621 union field `inl ∪ inr = ⊤` is PROVEN generically (`disjointBinaryCoproduct_of_disjoint`).

    The three genuinely colimit-specific disjointness facts are now discharged INTERNALLY from the
    per-stage `hdisj` by germ-transport (`colimit_inl_monic`, `colimit_inr_monic`,
    `colimit_inl_inter_inr`), using the keystone `objIncl_preserves_coproducts` /
    `objIncl_preserves_pullbacks` and the strict initial `colimitStrictInitial`.  The per-stage
    finite-limit / mono / initial bundles (`hmono`, `ht`/`htpres`, `hp`/`hpres`/`hpres_pair`,
    `he`/`hepres`/`hepres_lift`, `hbot`/`hinitpres`) are exactly the ones the §2.218 regular tower
    already supplies. -/
noncomputable def colimitDisjointBinaryCoproduct
    (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [Nonempty ι]
    (hdisj : ∀ i, DisjointBinaryCoproduct (C.A i)) (hmono : TransMono C)
    (hbot : ∀ i, PreLogos (C.A i))
    (hinitpres : ∀ {i j : ι} (hij : D.le i j), C.F hij (stageZero C hbot i) = stageZero C hbot j)
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k)
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : C.F hij a ⟶ z) (q : C.F hij b ⟶ z),
        ∃ r : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q)
    [hPL : @PreLogos C.Obj (colimitCat C hC)] :
    @DisjointBinaryCoproduct C.Obj (colimitCat C hC) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
  -- ascribe the `∀ {A B}` types so the trailing implicits are not eagerly instantiated by `have`
  have hl : ∀ {A B : C.Obj}, Monic (HasBinaryCoproducts.inl (A := A) (B := B)) :=
    colimit_inl_monic C hC hdisj hmono hcoppres hcoppres_case
  have hr : ∀ {A B : C.Obj}, Monic (HasBinaryCoproducts.inr (A := A) (B := B)) :=
    colimit_inr_monic C hC hdisj hmono hcoppres hcoppres_case
  have hinter : ∀ {A B : C.Obj},
      Subobject.le (Subobject.inter (inlSub (𝒞 := C.Obj) (A := A) (B := B) hl)
                                    (inrSub (𝒞 := C.Obj) (A := A) (B := B) hr))
                   (PreLogos.bottom (HasBinaryCoproducts.coprod A B)) :=
    colimit_inl_inter_inr C hC hdisj hmono hbot hinitpres ht htpres hp hpres hpres_pair
      he hepres hepres_lift hcoppres hcoppres_case hl hr
  exact disjointBinaryCoproduct_of_disjoint (𝒞 := C.Obj) hl hr hinter

/-- **The directed colimit of positive pre-logoi is a positive pre-logos** (Freyd §1.63 "union
    condition", strict level).  Single entry point bundling `colimitPreLogos` (the `PreLogos` layer,
    via `colimit_invImage_union_le`) as the `[hPL]` of `colimitDisjointBinaryCoproduct` (the disjoint
    binary coproduct, via the internal `colimit_inl/inr_monic` + `colimit_inl_inter_inr`).  All
    hypotheses are the per-stage finite-limit / image / coproduct coherence bundles the §2.218
    capitalization tower already supplies; the colimit's `RegularCategory`/`HasSubobjectUnions` come
    from `colimitPreRegular` + `colimitHasImages` + `hasSubobjectUnions_of_coproducts_images`. -/
noncomputable def colimitPositive
    (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [Nonempty ι]
    (hdisj : ∀ i, DisjointBinaryCoproduct (C.A i)) (hmono : TransMono C)
    (hbot : ∀ i, PreLogos (C.A i))
    (hinitpres : ∀ {i j : ι} (hij : D.le i j), C.F hij (stageZero C hbot i) = stageZero C hbot j)
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k)
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : C.F hij a ⟶ z) (q : C.F hij b ⟶ z),
        ∃ r : C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q)
    (hi : ∀ i, HasImages (C.A i))
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    (himgpres : ∀ {i j : ι} (hij : D.le i j) {A B : C.A i} (f : A ⟶ B),
        IsImage ((C.functF hij).map f)
          (@Subobject.map _ _ (C.catA i) (C.catA j) (C.F hij) (C.functF hij) (hmono hij) _
            (@image _ (C.catA i) (hi i) _ _ f)))
    [hReg : @RegularCategory C.Obj (colimitCat C hC)]
    [hUn : @HasSubobjectUnions C.Obj (colimitCat C hC) hReg.toHasImages] :
    @DisjointBinaryCoproduct C.Obj (colimitCat C hC) :=
  letI : Cat C.Obj := colimitCat C hC
  letI hPL : @PreLogos C.Obj (colimitCat C hC) :=
    colimitPreLogos C hC hbot hinitpres hmono ht htpres hp hpres hpres_pair he hepres hepres_lift
      (fun i => (hdisj i).toHasBinaryCoproducts) hcoppres hcoppres_case hi hfaith himgpres
  colimitDisjointBinaryCoproduct C hC hdisj hmono hbot hinitpres ht htpres hp hpres hpres_pair
    he hepres hepres_lift hcoppres hcoppres_case

end Freyd.Colim
