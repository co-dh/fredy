import Fredy.CatColimitRegular
import Fredy.S1_62
import Fredy.UnionFromCoproduct

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
    colimit-specific facts — the colimit injections are monic (`inl_monic`/`inr_monic`) and disjoint
    (`inl_inter_inr`) — are threaded as hypotheses, since `colimitHasBinaryCoproducts` does not expose
    its `inl`/`inr` germs as companion lemmas (see the note on `colimitDisjointBinaryCoproduct`).
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

/-- **The directed colimit of disjoint binary coproducts is a `DisjointBinaryCoproduct`.**

    Layers:
    * `[hPL]` — the colimit is a pre-logos (regular + subobject unions + bottom).  Supplied at the
      call site by `colimitPreRegular` + `colimitHasImages` + the bottom infrastructure, exactly as
      the §2.218 regular tower supplies `RegularCategory`.
    * `colimitCoprodOfDisjoint` — binary coproducts, built from the per-stage disjoint coproducts via
      `colimitHasBinaryCoproducts` (premises `hcoppres`/`hcoppres_case`).
    * the §1.621 union field `inl ∪ inr = ⊤` is PROVEN generically (`disjointBinaryCoproduct_of_disjoint`).

    The two genuinely colimit-specific disjointness facts are threaded as hypotheses:
    * `hl`/`hr` — the colimit injections are monic;
    * `hinter` — they are disjoint, `inl ∩ inr ≤ ⊥`.

    These cannot be discharged from `hdisj` inside this file because `colimitHasBinaryCoproducts`
    does not export its `inl`/`inr` germs (`homIncl` of the per-stage injections) as companion
    lemmas: proving the colimit `inl` monic needs `colimHom_mono_of_rep` against the brick's exact
    internal `let`-chain (`op A B`/`kp A B`/… built by `Classical.choose`), and proving disjointness
    additionally needs "the colimit pullback of the germ injections is the germ of the per-stage
    pullback" plus "the colimit bottom is the germ of the per-stage bottom".  The caller (the
    capitalization tower) discharges them from the per-stage `hdisj` via `objIncl_preservesMono` /
    `objIncl_preserves_pullbacks`. -/
noncomputable def colimitDisjointBinaryCoproduct
    (C : CatSystem ι D) (hC : C.Coherent) [Nonempty ι]
    (hdisj : ∀ i, DisjointBinaryCoproduct (C.A i))
    [hPL : @PreLogos C.Obj (colimitCat C hC)]
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
    (hl : letI : Cat C.Obj := colimitCat C hC
          letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
          ∀ {A B : C.Obj}, Monic (HasBinaryCoproducts.inl (A := A) (B := B)))
    (hr : letI : Cat C.Obj := colimitCat C hC
          letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
          ∀ {A B : C.Obj}, Monic (HasBinaryCoproducts.inr (A := A) (B := B)))
    (hinter : letI : Cat C.Obj := colimitCat C hC
              letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
              ∀ {A B : C.Obj},
                Subobject.le (Subobject.inter (inlSub (𝒞 := C.Obj) (A := A) (B := B) hl)
                                              (inrSub (𝒞 := C.Obj) (A := A) (B := B) hr))
                             (PreLogos.bottom (HasBinaryCoproducts.coprod A B))) :
    @DisjointBinaryCoproduct C.Obj (colimitCat C hC) :=
  letI : Cat C.Obj := colimitCat C hC
  letI : HasBinaryCoproducts C.Obj := colimitCoprodOfDisjoint C hC hdisj hcoppres hcoppres_case
  disjointBinaryCoproduct_of_disjoint (𝒞 := C.Obj) hl hr hinter

end Freyd.Colim

