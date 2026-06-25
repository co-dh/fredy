/-
  Freyd & Scedrov, *Categories and Allegories* §1.62–§1.66
  Pasting Lemma, Positive pre-logoi, coproducts, generating set,
  pre-filter, Representation Theorem.

  §1.62 Pasting Lemma: union of subobjects is pushout of intersection.
  §1.623 Positive pre-logos = pre-logos with coproducts.
  §1.632 Generating set / basis.
  §1.634 Pre-filter, T_𝔉 functor.
  §1.635 Representation Theorem for pre-logoi.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_55
import Fredy.S1_56
import Fredy.S1_57
import Fredy.S1_58
import Fredy.S1_60
import Fredy.S1_61


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.62 Pasting Lemma

  In a pre-logos, the union A₁∪A₂ is the pushout of A₁∩A₂. -/

variable [PreLogos 𝒞]

/-! ### Cover composition helpers (needed for §1.631) -/

/-- A cover pre-composed with an iso is still a cover. -/
theorem cover_comp_iso {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Cover f) (hg : IsIso g) :
    Cover (f ≫ g) := by
  obtain ⟨g_inv, hgg_inv, hg_inv_g⟩ := hg
  intro C m h hm heq
  have hm_ginv_mono : Monic (m ≫ g_inv) := by
    intro W u v huv
    apply hm u v
    have : (u ≫ m ≫ g_inv) ≫ g = (v ≫ m ≫ g_inv) ≫ g := by rw [huv]
    simp only [Cat.assoc] at this; rw [hg_inv_g, Cat.comp_id] at this; exact this
  have hfac : h ≫ (m ≫ g_inv) = f :=
    calc h ≫ (m ≫ g_inv) = (h ≫ m) ≫ g_inv := (Cat.assoc _ _ _).symm
      _ = (f ≫ g) ≫ g_inv := by rw [heq]
      _ = f ≫ (g ≫ g_inv) := Cat.assoc _ _ _
      _ = f := by rw [hgg_inv, Cat.comp_id]
  have h_iso : IsIso (m ≫ g_inv) := hf (m ≫ g_inv) h hm_ginv_mono hfac
  rw [show m = (m ≫ g_inv) ≫ g from by rw [Cat.assoc, hg_inv_g, Cat.comp_id]]
  exact isIso_comp h_iso ⟨g_inv, hgg_inv, hg_inv_g⟩

/-- An iso post-composed with a cover is still a cover. -/
theorem iso_comp_cover {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsIso f) (hg : Cover g) :
    Cover (f ≫ g) := by
  obtain ⟨f_inv, hff_inv, hf_inv_f⟩ := hf
  intro C m h hm heq
  exact hg m (f_inv ≫ h) hm
    (calc (f_inv ≫ h) ≫ m = f_inv ≫ (h ≫ m) := Cat.assoc _ _ _
      _ = f_inv ≫ (f ≫ g) := by rw [heq]
      _ = (f_inv ≫ f) ≫ g := (Cat.assoc _ _ _).symm
      _ = g := by rw [hf_inv_f, Cat.id_comp])

/-- Intersection of subobjects: pullback of S.arr and T.arr, composed with S.arr. -/
def Subobject.inter [HasPullbacks 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B) : Subobject 𝒞 B :=
  let pb := HasPullbacks.has S.arr T.arr
  { dom := pb.cone.pt
    arr := pb.cone.π₁ ≫ S.arr
    monic := by
      intro X u v h
      -- h: u ≫ (π₁ ≫ S.arr) = v ≫ (π₁ ≫ S.arr)
      have hsq : pb.cone.π₁ ≫ S.arr = pb.cone.π₂ ≫ T.arr := pb.cone.w
      have huvπ₁ : u ≫ pb.cone.π₁ = v ≫ pb.cone.π₁ :=
        S.monic _ _ (by
          simpa [Cat.assoc] using h)
      have huvπ₂ : u ≫ pb.cone.π₂ = v ≫ pb.cone.π₂ :=
        T.monic _ _ (by
          calc
            (u ≫ pb.cone.π₂) ≫ T.arr = u ≫ (pb.cone.π₂ ≫ T.arr) := by simpa using Cat.assoc _ _ _
            _ = u ≫ (pb.cone.π₁ ≫ S.arr) := by rw [hsq]
            _ = (u ≫ pb.cone.π₁) ≫ S.arr := by simpa using (Cat.assoc _ _ _).symm
            _ = (v ≫ pb.cone.π₁) ≫ S.arr := by rw [huvπ₁]
            _ = v ≫ (pb.cone.π₁ ≫ S.arr) := by simpa using Cat.assoc _ _ _
            _ = v ≫ (pb.cone.π₂ ≫ T.arr) := by rw [hsq]
            _ = (v ≫ pb.cone.π₂) ≫ T.arr := by simpa using (Cat.assoc _ _ _).symm)
      let c : Cone S.arr T.arr :=
        { pt := X
          π₁ := u ≫ pb.cone.π₁
          π₂ := u ≫ pb.cone.π₂
          w  := by
            calc
              (u ≫ pb.cone.π₁) ≫ S.arr = u ≫ (pb.cone.π₁ ≫ S.arr) := by simpa using Cat.assoc _ _ _
              _ = u ≫ (pb.cone.π₂ ≫ T.arr) := by rw [hsq]
              _ = (u ≫ pb.cone.π₂) ≫ T.arr := by simpa using (Cat.assoc _ _ _).symm }
      have hlift := pb.lift_uniq c u (by rfl) (by rfl)
      have hv_eq_u : v = u := by
        apply (pb.lift_uniq c v ?_ ?_).trans hlift.symm
        · calc
            v ≫ pb.cone.π₁ = u ≫ pb.cone.π₁ := huvπ₁.symm
            _ = c.π₁ := rfl
        · calc
            v ≫ pb.cone.π₂ = u ≫ pb.cone.π₂ := huvπ₂.symm
            _ = c.π₂ := rfl
      rw [hv_eq_u] }

/-! ### Relational helpers for the Pasting Lemma (§1.62)

  The book's proof builds, for any cocone `(Q, f, g)`, the relation
  `R = x°⊚f ∪ y°⊚g : U → Q` (with `x, y` the union inclusions), shows it is a
  map (entire + simple), and reads off the descent morphism.  These helpers
  package the pieces that are general enough to live on their own. -/

/-- Any MAP relation is the graph of a morphism (mutual containment).  Extract the
    morphism via `tabulated_is_map_iff_left_iso` (left leg is iso) and
    `tabulated_left_iso_eq_graph`. -/
theorem map_to_graph {A B : 𝒞} (R : BinRel 𝒞 A B) (hR : Map R) :
    ∃ q : A ⟶ B, RelLe R (graph q) ∧ RelLe (graph q) R := by
  have heq : R = BinRel.mk R.src R.colA R.colB R.isMonicPair := rfl
  rw [heq] at hR
  have hiso : IsIso R.colA := (tabulated_is_map_iff_left_iso R.colA R.colB R.isMonicPair).mp hR
  obtain ⟨ainv, ha_ainv, hainv_a⟩ := hiso
  refine ⟨ainv ≫ R.colB, ?_, ?_⟩
  · have h := (tabulated_left_iso_eq_graph R.colA R.colB R.isMonicPair ainv ha_ainv hainv_a).1
    rw [← heq] at h; exact h
  · have h := (tabulated_left_iso_eq_graph R.colA R.colB R.isMonicPair ainv ha_ainv hainv_a).2
    rw [← heq] at h; exact h

/-- If `I` is an image of `g` and `e ≫ I.arr = g`, then `e` is a cover.  The
    abstract-image generalization of `image_lift_cover`. -/
theorem cover_of_image_factor {A B : 𝒞} {g : A ⟶ B} {I : Subobject 𝒞 B}
    (hI : IsImage g I) {e : A ⟶ I.dom} (he : e ≫ I.arr = g) : Cover e := by
  intro D m gg hm hfac
  have hmono_comp : Monic (m ≫ I.arr) := by
    intro W u v huv
    exact hm _ _ (I.monic _ _ (by simpa [Cat.assoc] using huv))
  have h_allows : Allows ⟨D, m ≫ I.arr, hmono_comp⟩ g := by
    refine ⟨gg, ?_⟩
    calc gg ≫ (m ≫ I.arr) = (gg ≫ m) ≫ I.arr := (Cat.assoc _ _ _).symm
      _ = e ≫ I.arr := by rw [hfac]
      _ = g := he
  obtain ⟨h, hh⟩ := hI.2 _ h_allows
  have hhm : h ≫ m = Cat.id I.dom := I.monic _ _ (by
    calc (h ≫ m) ≫ I.arr = h ≫ (m ≫ I.arr) := Cat.assoc _ _ _
      _ = I.arr := hh
      _ = Cat.id I.dom ≫ I.arr := (Cat.id_comp _).symm)
  have hmh : m ≫ h = Cat.id D := hm _ _ (by
    calc (m ≫ h) ≫ m = m ≫ (h ≫ m) := Cat.assoc _ _ _
      _ = m ≫ Cat.id I.dom := by rw [hhm]
      _ = m := Cat.comp_id _
      _ = Cat.id D ≫ m := (Cat.id_comp _).symm)
  exact ⟨h, hmh, hhm⟩

/-- §1.615 (subobject form): the union `A₁ ∪ A₂` is an image of `case A₁.arr A₂.arr`. -/
theorem union_is_image [HasBinaryCoproducts 𝒞] {A : 𝒞} (A₁ A₂ : Subobject 𝒞 A) :
    IsImage (HasBinaryCoproducts.case A₁.arr A₂.arr) (HasSubobjectUnions.union A₁ A₂) := by
  obtain ⟨l₁, hl₁⟩ := HasSubobjectUnions.union_left A₁ A₂
  obtain ⟨l₂, hl₂⟩ := HasSubobjectUnions.union_right A₁ A₂
  refine ⟨⟨HasBinaryCoproducts.case l₁ l₂, ?_⟩, ?_⟩
  · refine HasBinaryCoproducts.case_uniq A₁.arr A₂.arr _ ?_ ?_
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inl, hl₁]
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inr, hl₂]
  · rintro S ⟨k, hk⟩
    refine HasSubobjectUnions.union_min _ _ _ ?_ ?_
    · exact ⟨HasBinaryCoproducts.inl ≫ k, by rw [Cat.assoc, hk, HasBinaryCoproducts.case_inl]⟩
    · exact ⟨HasBinaryCoproducts.inr ≫ k, by rw [Cat.assoc, hk, HasBinaryCoproducts.case_inr]⟩

/-- The copairing of the two union inclusions is a cover onto `(A₁ ∪ A₂).dom`:
    `x, y` are jointly epimorphic, the relational backbone of entirety. -/
theorem union_case_cover [HasBinaryCoproducts 𝒞] {A : 𝒞} (A₁ A₂ : Subobject 𝒞 A)
    {x : A₁.dom ⟶ (HasSubobjectUnions.union A₁ A₂).dom}
    {y : A₂.dom ⟶ (HasSubobjectUnions.union A₁ A₂).dom}
    (hx : x ≫ (HasSubobjectUnions.union A₁ A₂).arr = A₁.arr)
    (hy : y ≫ (HasSubobjectUnions.union A₁ A₂).arr = A₂.arr) :
    Cover (HasBinaryCoproducts.case x y) := by
  refine cover_of_image_factor (union_is_image A₁ A₂) ?_
  refine HasBinaryCoproducts.case_uniq A₁.arr A₂.arr _ ?_ ?_
  · rw [← Cat.assoc, HasBinaryCoproducts.case_inl, hx]
  · rw [← Cat.assoc, HasBinaryCoproducts.case_inr, hy]

/-- `pair x x` factors through the relation `x° ⊚ x` — the witness used to push the
    joint cover `j° ⊚ j` down into `x° ⊚ x ∪ y° ⊚ y`. -/
theorem pairxx_factor {C₁ U : 𝒞} (x : C₁ ⟶ U) :
    ∃ α : C₁ ⟶ ((graph x)° ⊚ (graph x)).src,
      α ≫ ((graph x)° ⊚ (graph x)).colA = x ∧ α ≫ ((graph x)° ⊚ (graph x)).colB = x := by
  let pbx := HasPullbacks.has ((graph x)°).colB ((graph x)).colA
  have hcw : (Cat.id C₁) ≫ ((graph x)°).colB = (Cat.id C₁) ≫ (graph x).colA := by
    simp [graph, reciprocal]
  let c : Cone ((graph x)°).colB ((graph x)).colA := ⟨C₁, Cat.id C₁, Cat.id C₁, hcw⟩
  let u := pbx.lift c
  have hu₁ : u ≫ pbx.cone.π₁ = Cat.id C₁ := pbx.lift_fst c
  have hu₂ : u ≫ pbx.cone.π₂ = Cat.id C₁ := pbx.lift_snd c
  let spanx : pbx.cone.pt ⟶ prod U U :=
    pair (pbx.cone.π₁ ≫ ((graph x)°).colA) (pbx.cone.π₂ ≫ (graph x).colB)
  refine ⟨u ≫ image.lift spanx, ?_, ?_⟩
  · show (u ≫ image.lift spanx) ≫ ((image spanx).arr ≫ fst) = x
    rw [Cat.assoc, ← Cat.assoc (image.lift spanx), image.lift_fac]
    show u ≫ spanx ≫ fst = x
    rw [show spanx ≫ fst = pbx.cone.π₁ ≫ ((graph x)°).colA from fst_pair _ _,
        ← Cat.assoc, hu₁, show ((graph x)°).colA = x from rfl, Cat.id_comp]
  · show (u ≫ image.lift spanx) ≫ ((image spanx).arr ≫ snd) = x
    rw [Cat.assoc, ← Cat.assoc (image.lift spanx), image.lift_fac]
    show u ≫ spanx ≫ snd = x
    rw [show spanx ≫ snd = pbx.cone.π₂ ≫ (graph x).colB from snd_pair _ _,
        ← Cat.assoc, hu₂, show (graph x).colB = x from rfl, Cat.id_comp]

/-- `j° ⊚ j ⊆ x° ⊚ x ∪ y° ⊚ y` for `j = case x y` — the joint cover descends to
    the union of the two reciprocal self-composites. -/
theorem jcc_le [HasBinaryCoproducts 𝒞] {C₁ C₂ U : 𝒞} (x : C₁ ⟶ U) (y : C₂ ⟶ U) :
    RelLe ((graph (HasBinaryCoproducts.case x y))° ⊚ (graph (HasBinaryCoproducts.case x y)))
          ((graph x)° ⊚ (graph x) ∪ᵣ (graph y)° ⊚ (graph y)) := by
  let j := HasBinaryCoproducts.case x y
  let pb := HasPullbacks.has ((graph j)°).colB ((graph j)).colA
  have hπ : pb.cone.π₁ = pb.cone.π₂ := by
    simpa [graph, reciprocal, Cat.comp_id] using pb.cone.w
  let spanj : pb.cone.pt ⟶ prod U U :=
    pair (pb.cone.π₁ ≫ ((graph j)°).colA) (pb.cone.π₂ ≫ (graph j).colB)
  let Uu : BinRel 𝒞 U U := (graph x)° ⊚ (graph x) ∪ᵣ (graph y)° ⊚ (graph y)
  let pU : Uu.src ⟶ prod U U := pair Uu.colA Uu.colB
  have hpU_mono : Monic pU := monic_pair_of_monicPair Uu.colA Uu.colB Uu.isMonicPair
  obtain ⟨αx, hαx1, hαx2⟩ := pairxx_factor x
  obtain ⟨lx, hlxA, hlxB⟩ := relUnion_le_left ((graph x)° ⊚ (graph x)) ((graph y)° ⊚ (graph y))
  let α' : C₁ ⟶ Uu.src := αx ≫ lx
  have hα'A : α' ≫ Uu.colA = x := by rw [Cat.assoc, hlxA, hαx1]
  have hα'B : α' ≫ Uu.colB = x := by rw [Cat.assoc, hlxB, hαx2]
  obtain ⟨αy, hαy1, hαy2⟩ := pairxx_factor y
  obtain ⟨ly, hlyA, hlyB⟩ := relUnion_le_right ((graph x)° ⊚ (graph x)) ((graph y)° ⊚ (graph y))
  let β' : C₂ ⟶ Uu.src := αy ≫ ly
  have hβ'A : β' ≫ Uu.colA = y := by rw [Cat.assoc, hlyA, hαy1]
  have hβ'B : β' ≫ Uu.colB = y := by rw [Cat.assoc, hlyB, hαy2]
  let k : (HasBinaryCoproducts.coprod C₁ C₂) ⟶ Uu.src := HasBinaryCoproducts.case α' β'
  have hkA : k ≫ Uu.colA = j := by
    apply HasBinaryCoproducts.case_uniq
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inl, hα'A]
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inr, hβ'A]
  have hkB : k ≫ Uu.colB = j := by
    apply HasBinaryCoproducts.case_uniq
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inl, hα'B]
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inr, hβ'B]
  have hk_pU : k ≫ pU = pair j j := by
    apply pair_uniq
    · rw [Cat.assoc, show pU ≫ fst = Uu.colA from fst_pair _ _, hkA]
    · rw [Cat.assoc, show pU ≫ snd = Uu.colB from snd_pair _ _, hkB]
  have hspanj : spanj = pb.cone.π₁ ≫ pair j j := by
    dsimp [spanj]
    rw [show ((graph j)°).colA = j from rfl, show (graph j).colB = j from rfl, ← hπ]
    exact (pair_uniq (pb.cone.π₁ ≫ j) (pb.cone.π₁ ≫ j) (pb.cone.π₁ ≫ pair j j)
      (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])).symm
  let Usub : Subobject 𝒞 (prod U U) := ⟨Uu.src, pU, hpU_mono⟩
  have hallows : Allows Usub spanj := ⟨pb.cone.π₁ ≫ k, by
    show (pb.cone.π₁ ≫ k) ≫ pU = spanj
    rw [Cat.assoc, hk_pU, hspanj]⟩
  obtain ⟨w, hw⟩ := image_min spanj Usub hallows
  refine ⟨⟨w, ?_, ?_⟩⟩
  · show w ≫ Uu.colA = (image spanj).arr ≫ fst
    calc w ≫ Uu.colA = (w ≫ pU) ≫ fst := by rw [Cat.assoc, fst_pair]
      _ = (image spanj).arr ≫ fst := by rw [hw]
  · show w ≫ Uu.colB = (image spanj).arr ≫ snd
    calc w ≫ Uu.colB = (w ≫ pU) ≫ snd := by rw [Cat.assoc, snd_pair]
      _ = (image spanj).arr ≫ snd := by rw [hw]

/-- The two union inclusions `x, y` jointly cover `U = A₁ ∪ A₂`:
    `1_U ⊆ x° ⊚ x ∪ y° ⊚ y`.  Combines `union_case_cover` (the copairing is a cover)
    with `jcc_le` (the cover's reciprocal self-composite lands in the union). -/
theorem union_joint_cover [HasBinaryCoproducts 𝒞] {A : 𝒞} (A₁ A₂ : Subobject 𝒞 A)
    {x : A₁.dom ⟶ (HasSubobjectUnions.union A₁ A₂).dom}
    {y : A₂.dom ⟶ (HasSubobjectUnions.union A₁ A₂).dom}
    (hx : x ≫ (HasSubobjectUnions.union A₁ A₂).arr = A₁.arr)
    (hy : y ≫ (HasSubobjectUnions.union A₁ A₂).arr = A₂.arr) :
    RelLe (graph (Cat.id (HasSubobjectUnions.union A₁ A₂).dom))
          ((graph x)° ⊚ (graph x) ∪ᵣ (graph y)° ⊚ (graph y)) := by
  have hcov : Cover (HasBinaryCoproducts.case x y) := union_case_cover A₁ A₂ hx hy
  have h1 := (cover_iff_one_le_reciprocal_comp_self (HasBinaryCoproducts.case x y)).mp hcov
  exact rel_le_trans h1 (jcc_le x y)

/-- `graph x ⊚ (graph x)° ⊆ 1` when `x` is monic — the reciprocal self-composite of a
    monic graph is contained in the identity (`Simple` of `(graph x)°`). -/
theorem graph_comp_recip_le_one_of_mono {A B : 𝒞} (x : A ⟶ B) (hx : Monic x) :
    RelLe (graph x ⊚ (graph x)°) (graph (Cat.id A)) := by
  have hp : MonicPair (x : A ⟶ B) (Cat.id A) := by
    intro W f g _ hid; simpa [Cat.comp_id] using hid
  have hsimp : Simple (BinRel.mk A x (Cat.id A) hp) :=
    (tabulated_is_simple_iff_left_monic x (Cat.id A) hp).mpr hx
  have heq : BinRel.mk A x (Cat.id A) hp = (graph x)° := rfl
  rw [heq] at hsimp
  unfold Simple at hsimp
  rw [reciprocal_invol] at hsimp
  exact hsimp

/-- The intersection relation: `graph x ⊚ (graph y)° ⊆ π₁° ⊚ π₂`, where `(π₁, π₂)` is the
    pullback of `(a1, a2)` and `x, y` factor `a1, a2` through a common `uarr`.  Pointwise:
    two points sit over the same union point exactly when they come from the intersection. -/
theorem inter_lemma {A₁ A₂ U A : 𝒞} (x : A₁ ⟶ U) (y : A₂ ⟶ U) (uarr : U ⟶ A)
    (a1 : A₁ ⟶ A) (a2 : A₂ ⟶ A)
    (hx : x ≫ uarr = a1) (hy : y ≫ uarr = a2) :
    RelLe (graph x ⊚ (graph y)°)
      ((graph (HasPullbacks.has a1 a2).cone.π₁)° ⊚ (graph (HasPullbacks.has a1 a2).cone.π₂)) := by
  let pxy := HasPullbacks.has ((graph x).colB) (((graph y)°).colA)
  have hwxy : pxy.cone.π₁ ≫ x = pxy.cone.π₂ ≫ y := pxy.cone.w
  let pI := HasPullbacks.has a1 a2
  have hconeI : pxy.cone.π₁ ≫ a1 = pxy.cone.π₂ ≫ a2 := by
    rw [← hx, ← hy, ← Cat.assoc, ← Cat.assoc, hwxy]
  let cI : Cone a1 a2 := ⟨pxy.cone.pt, pxy.cone.π₁, pxy.cone.π₂, hconeI⟩
  let m := pI.lift cI
  have hm1 : m ≫ pI.cone.π₁ = pxy.cone.π₁ := pI.lift_fst cI
  have hm2 : m ≫ pI.cone.π₂ = pxy.cone.π₂ := pI.lift_snd cI
  let RHS := (graph pI.cone.π₁)° ⊚ (graph pI.cone.π₂)
  let pR : RHS.src ⟶ prod A₁ A₂ := pair RHS.colA RHS.colB
  have hpR_mono : Monic pR := monic_pair_of_monicPair RHS.colA RHS.colB RHS.isMonicPair
  let pbR := HasPullbacks.has (((graph pI.cone.π₁)°).colB) ((graph pI.cone.π₂).colA)
  have hcwR : (Cat.id pI.cone.pt) ≫ (((graph pI.cone.π₁)°).colB) =
      (Cat.id pI.cone.pt) ≫ ((graph pI.cone.π₂).colA) := by simp [graph, reciprocal]
  let cR : Cone (((graph pI.cone.π₁)°).colB) ((graph pI.cone.π₂).colA) :=
    ⟨pI.cone.pt, Cat.id pI.cone.pt, Cat.id pI.cone.pt, hcwR⟩
  let uR := pbR.lift cR
  have huR1 : uR ≫ pbR.cone.π₁ = Cat.id pI.cone.pt := pbR.lift_fst cR
  have huR2 : uR ≫ pbR.cone.π₂ = Cat.id pI.cone.pt := pbR.lift_snd cR
  let spanR : pbR.cone.pt ⟶ prod A₁ A₂ :=
    pair (pbR.cone.π₁ ≫ (((graph pI.cone.π₁)°).colA)) (pbR.cone.π₂ ≫ ((graph pI.cone.π₂).colB))
  let αR : pI.cone.pt ⟶ RHS.src := uR ≫ image.lift spanR
  have hαR : αR ≫ pR = pair pI.cone.π₁ pI.cone.π₂ := by
    show (uR ≫ image.lift spanR) ≫ pair RHS.colA RHS.colB = pair pI.cone.π₁ pI.cone.π₂
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]
      show (uR ≫ image.lift spanR) ≫ ((image spanR).arr ≫ fst) = pI.cone.π₁
      rw [Cat.assoc, ← Cat.assoc (image.lift spanR), image.lift_fac]
      rw [show spanR ≫ fst = pbR.cone.π₁ ≫ (((graph pI.cone.π₁)°).colA) from fst_pair _ _,
          ← Cat.assoc, huR1, Cat.id_comp, show (((graph pI.cone.π₁)°).colA) = pI.cone.π₁ from rfl]
    · rw [Cat.assoc, snd_pair]
      show (uR ≫ image.lift spanR) ≫ ((image spanR).arr ≫ snd) = pI.cone.π₂
      rw [Cat.assoc, ← Cat.assoc (image.lift spanR), image.lift_fac]
      rw [show spanR ≫ snd = pbR.cone.π₂ ≫ ((graph pI.cone.π₂).colB) from snd_pair _ _,
          ← Cat.assoc, huR2, Cat.id_comp, show ((graph pI.cone.π₂).colB) = pI.cone.π₂ from rfl]
  let spanL : pxy.cone.pt ⟶ prod A₁ A₂ :=
    pair (pxy.cone.π₁ ≫ (graph x).colA) (pxy.cone.π₂ ≫ ((graph y)°).colB)
  have hspanL_eq : spanL = (m ≫ αR) ≫ pR := by
    rw [Cat.assoc, hαR]
    show pair (pxy.cone.π₁ ≫ (graph x).colA) (pxy.cone.π₂ ≫ ((graph y)°).colB)
      = m ≫ pair pI.cone.π₁ pI.cone.π₂
    refine (pair_uniq (pxy.cone.π₁ ≫ (graph x).colA) (pxy.cone.π₂ ≫ ((graph y)°).colB)
      (m ≫ pair pI.cone.π₁ pI.cone.π₂) ?_ ?_).symm
    · rw [Cat.assoc, fst_pair, hm1, show (graph x).colA = Cat.id A₁ from rfl]; exact (Cat.comp_id _).symm
    · rw [Cat.assoc, snd_pair, hm2, show ((graph y)°).colB = Cat.id A₂ from rfl]; exact (Cat.comp_id _).symm
  let RHSsub : Subobject 𝒞 (prod A₁ A₂) := ⟨RHS.src, pR, hpR_mono⟩
  have hallows : Allows RHSsub spanL := ⟨m ≫ αR, hspanL_eq.symm⟩
  obtain ⟨w, hw⟩ := image_min spanL RHSsub hallows
  refine ⟨⟨w, ?_, ?_⟩⟩
  · show w ≫ RHS.colA = (image spanL).arr ≫ fst
    calc w ≫ RHS.colA = (w ≫ pR) ≫ fst := by rw [Cat.assoc, fst_pair]
      _ = (image spanL).arr ≫ fst := by rw [hw]
  · show w ≫ RHS.colB = (image spanL).arr ≫ snd
    calc w ≫ RHS.colB = (w ≫ pR) ≫ snd := by rw [Cat.assoc, snd_pair]
      _ = (image spanL).arr ≫ snd := by rw [hw]

/-- Compatibility consequence: `(graph x ⊚ (graph y)°) ⊚ graph g ⊆ graph f`, using the
    intersection relation and the cocone equation `π₁ ≫ f = π₂ ≫ g`. -/
theorem hxyg_lemma {A₁ A₂ Q I : 𝒞} (f : A₁ ⟶ Q) (g : A₂ ⟶ Q)
    (π₁ : I ⟶ A₁) (π₂ : I ⟶ A₂) (xrel : BinRel 𝒞 A₁ A₂)
    (hinter : RelLe xrel ((graph π₁)° ⊚ graph π₂))
    (hcocone : π₁ ≫ f = π₂ ≫ g) :
    RelLe (xrel ⊚ graph g) (graph f) := by
  -- Book §1.62, in Freyd's notation (a map IS its graph relation, via the `↑`
  -- coercion):  xrel·g ⊆ π₁°π₂·g = π₁°(π₂g) = π₁°(π₁f) = (π₁°π₁)f ⊆ 1·f = f,
  -- using the cocone equation π₁f = π₂g and π₁ monic (π₁°π₁ ⊆ 1).
  let p₁ : BinRel 𝒞 I A₁ := π₁          -- ↑π₁
  let p₂ : BinRel 𝒞 I A₂ := π₂          -- ↑π₂
  let fr : BinRel 𝒞 A₁ Q := f           -- ↑f
  let gr : BinRel 𝒞 A₂ Q := g           -- ↑g
  calc xrel ⊚ gr
      ⊂ (p₁° ⊚ p₂) ⊚ gr := compose_le hinter (rel_le_refl _)
    _ ⊂ p₁° ⊚ (p₂ ⊚ gr) := (compose_assoc_of_regular (p₁°) p₂ gr).1
    _ ⊂ p₁° ⊚ graph (π₂ ≫ g) := compose_le (rel_le_refl _) (comp_graph π₂ g)
    _ ⊂ p₁° ⊚ graph (π₁ ≫ f) := hcocone ▸ rel_le_refl _
    _ ⊂ p₁° ⊚ (p₁ ⊚ fr) := compose_le (rel_le_refl _) (graph_comp π₁ f)
    _ ⊂ (p₁° ⊚ p₁) ⊚ fr := (compose_assoc_of_regular (p₁°) p₁ fr).2
    _ ⊂ graph (Cat.id A₁) ⊚ fr := compose_le (reciprocal_comp_self_le_one π₁) (rel_le_refl _)
    _ ⊂ fr := graph_id_comp fr

/-- Diagonal term: `P° ⊚ P ⊆ 1_Q` where `P = (graph x)° ⊚ graph f` and `x` is monic. -/
theorem diag_le_one {A₁ U Q : 𝒞} (x : A₁ ⟶ U) (f : A₁ ⟶ Q) (hx : Monic x) :
    RelLe (((graph x)° ⊚ graph f)° ⊚ ((graph x)° ⊚ graph f)) (graph (Cat.id Q)) := by
  -- Book §1.62 (maps as relations via `↑`):  P°P = (x°f)°(x°f) ⊆ f°x·x°f
  --   = f°(xx°)f ⊆ f°·1·f = f°f ⊆ 1, the middle step using x monic (xx° ⊆ 1).
  let xr : BinRel 𝒞 A₁ U := x          -- ↑x
  let fr : BinRel 𝒞 A₁ Q := f          -- ↑f
  have hPr : RelLe ((xr° ⊚ fr)°) (fr° ⊚ xr) := by
    have h := reciprocal_comp_le (xr°) fr
    rw [reciprocal_invol] at h; exact h
  let Pr := xr° ⊚ fr
  calc Pr° ⊚ Pr
      ⊂ (fr° ⊚ xr) ⊚ Pr := compose_le hPr (rel_le_refl _)
    _ ⊂ fr° ⊚ (xr ⊚ Pr) := (compose_assoc_of_regular (fr°) xr Pr).1
    _ ⊂ fr° ⊚ ((xr ⊚ xr°) ⊚ fr) :=
          compose_le (rel_le_refl _) (compose_assoc_of_regular xr (xr°) fr).2
    _ ⊂ fr° ⊚ (graph (Cat.id A₁) ⊚ fr) :=
          compose_le (rel_le_refl _) (compose_le (graph_comp_recip_le_one_of_mono x hx) (rel_le_refl _))
    _ ⊂ fr° ⊚ fr := compose_le (rel_le_refl _) (graph_id_comp fr)
    _ ⊂ graph (Cat.id Q) := reciprocal_comp_self_le_one f

/-- Cross term: `P° ⊚ Q ⊆ 1_Q` for `P = (graph x)° ⊚ graph f`, `Q = (graph y)° ⊚ graph g`,
    given the compatibility consequence `hxyg`. -/
theorem cross_le_one {A₁ A₂ U Q : 𝒞} (x : A₁ ⟶ U) (y : A₂ ⟶ U) (f : A₁ ⟶ Q) (g : A₂ ⟶ Q)
    (hxyg : RelLe ((graph x ⊚ (graph y)°) ⊚ graph g) (graph f)) :
    RelLe (((graph x)° ⊚ graph f)° ⊚ ((graph y)° ⊚ graph g)) (graph (Cat.id Q)) := by
  -- Book §1.62 (maps as relations via `↑`):  P°Q = (x°f)°(y°g) ⊆ f°x·y°g
  --   = f°(xy°g) ⊆ f°f ⊆ 1, where the bracket xy°g ⊆ f is exactly `hxyg`.
  let xr : BinRel 𝒞 A₁ U := x          -- ↑x
  let yr : BinRel 𝒞 A₂ U := y          -- ↑y
  let fr : BinRel 𝒞 A₁ Q := f          -- ↑f
  let gr : BinRel 𝒞 A₂ Q := g          -- ↑g
  have hPr : RelLe ((xr° ⊚ fr)°) (fr° ⊚ xr) := by
    have h := reciprocal_comp_le (xr°) fr
    rw [reciprocal_invol] at h; exact h
  let Qr := yr° ⊚ gr
  calc (xr° ⊚ fr)° ⊚ Qr
      ⊂ (fr° ⊚ xr) ⊚ Qr := compose_le hPr (rel_le_refl _)
    _ ⊂ fr° ⊚ (xr ⊚ Qr) := (compose_assoc_of_regular (fr°) xr Qr).1
    _ ⊂ fr° ⊚ ((xr ⊚ yr°) ⊚ gr) :=
          compose_le (rel_le_refl _) (compose_assoc_of_regular xr (yr°) gr).2
    _ ⊂ fr° ⊚ fr := compose_le (rel_le_refl _) hxyg
    _ ⊂ graph (Cat.id Q) := reciprocal_comp_self_le_one f

/-- Simplicity of the descent relation `R = P ∪ᵣ Q` from the four atomic bounds. -/
theorem simple_R [HasBinaryCoproducts 𝒞] {U Q : 𝒞} (P Qr : BinRel 𝒞 U Q)
    (hPP : RelLe (P° ⊚ P) (graph (Cat.id Q)))
    (hQQ : RelLe (Qr° ⊚ Qr) (graph (Cat.id Q)))
    (hPQ : RelLe (P° ⊚ Qr) (graph (Cat.id Q)))
    (hQP : RelLe (Qr° ⊚ P) (graph (Cat.id Q))) :
    RelLe ((P ∪ᵣ Qr)° ⊚ (P ∪ᵣ Qr)) (graph (Cat.id Q)) := by
  -- Pointfree (book simple step): R°R = (P∪Q)°(P∪Q) distributes into the four
  -- atomic blocks P°P, P°Q, Q°P, Q°Q, each ⊆ 1; reciprocal symmetry folds the two
  -- mixed columns into the recorded cross bounds.  R = P∪Q with `∪ᵣ` (coproduct-free union).
  refine rel_le_trans (compose_union_right ((P ∪ᵣ Qr)°) P Qr) (le_relUnion ?_ ?_)
  · -- column R°P ⊆ (P°R)° ⊆ (P°P ∪ P°Q)° ⊆ 1°
    have hP_R : RelLe (P° ⊚ (P ∪ᵣ Qr)) (graph (Cat.id Q)) :=
      rel_le_trans (compose_union_right (P°) P Qr) (le_relUnion hPP hPQ)
    have hrecip : RelLe ((P ∪ᵣ Qr)° ⊚ P) ((P° ⊚ (P ∪ᵣ Qr))°) := by
      have h := (reciprocal_comp (P°) (P ∪ᵣ Qr)).2; rw [reciprocal_invol] at h; exact h
    exact rel_le_trans hrecip (reciprocal_mono hP_R)
  · -- column R°Q ⊆ (Q°R)° ⊆ (Q°P ∪ Q°Q)° ⊆ 1°
    have hQ_R : RelLe (Qr° ⊚ (P ∪ᵣ Qr)) (graph (Cat.id Q)) :=
      rel_le_trans (compose_union_right (Qr°) P Qr) (le_relUnion hQP hQQ)
    have hrecip : RelLe ((P ∪ᵣ Qr)° ⊚ Qr) ((Qr° ⊚ (P ∪ᵣ Qr))°) := by
      have h := (reciprocal_comp (Qr°) (P ∪ᵣ Qr)).2; rw [reciprocal_invol] at h; exact h
    exact rel_le_trans hrecip (reciprocal_mono hQ_R)

/-- Entirety ingredient: `x° ⊚ x ⊆ R ⊚ R°` when `P = (graph x)° ⊚ graph f ⊆ R`. -/
theorem xx_le_RRrecip {A₁ U Q : 𝒞} (x : A₁ ⟶ U) (f : A₁ ⟶ Q)
    (R : BinRel 𝒞 U Q) (hPR : RelLe ((graph x)° ⊚ graph f) R) :
    RelLe ((graph x)° ⊚ graph x) (R ⊚ R°) := by
  -- Book §1.62 entire step (maps as relations via `↑`):  x°x ⊆ x°(ff°)x = (x°f)(f°x)
  --   = P·(f°x) ⊆ R·R°, since f is entire (1 ⊆ ff°) and f°x ⊆ (x°f)° = P° ⊆ R°.
  let xr : BinRel 𝒞 A₁ U := x          -- ↑x
  let fr : BinRel 𝒞 A₁ Q := f          -- ↑f
  have hEntf : RelLe (graph (Cat.id A₁)) (fr ⊚ fr°) := (graph_is_map f).1
  have hA : RelLe xr ((fr ⊚ fr°) ⊚ xr) :=
    rel_le_trans (comp_graph_id_left xr) (compose_le hEntf (rel_le_refl _))
  have hPrecip : RelLe (fr° ⊚ xr) (R°) := by
    have hsub : RelLe (fr° ⊚ xr) ((xr° ⊚ fr)°) := by
      have h := (reciprocal_comp (xr°) fr).2
      rw [reciprocal_invol] at h; exact h
    exact rel_le_trans hsub (reciprocal_mono hPR)
  calc xr° ⊚ xr
      ⊂ xr° ⊚ ((fr ⊚ fr°) ⊚ xr) := compose_le (rel_le_refl _) hA
    _ ⊂ xr° ⊚ (fr ⊚ (fr° ⊚ xr)) :=
          compose_le (rel_le_refl _) (compose_assoc_of_regular fr (fr°) xr).1
    _ ⊂ (xr° ⊚ fr) ⊚ (fr° ⊚ xr) :=
          (compose_assoc_of_regular (xr°) fr (fr° ⊚ xr)).2
    _ ⊂ R ⊚ R° := compose_le hPR hPrecip

/-- Pasting Lemma (§1.62): For subobjects A₁,A₂ of A, the pushout
    of the two projections from the intersection I = A₁∩A₂ (to A₁.dom and
    A₂.dom) is the union U = A₁∪A₂.  This is one of the defining properties
    of a pre-logos (distributive subobject lattice).

    The book proves this in a bare pre-logos; the relational-union/distributivity
    infrastructure of §1.616 (`relUnion`, `compose_union_right`) is, in this repo,
    only built under `[HasBinaryCoproducts 𝒞]` (it presents `R ∪ S` as the image of
    a copairing of the two table sources).  Since a pre-logos with coproducts is exactly
    a positive pre-logos (§1.623) — and every consumer of this lemma below (`§1.624`,
    `§1.631`) already works in a positive pre-logos — we carry the coproduct instance
    here rather than re-deriving a coproduct-free relational union. -/
noncomputable def pasting_lemma [HasBinaryCoproducts 𝒞] {A : 𝒞} (A₁ A₂ : Subobject 𝒞 A) :
    HasPushout (HasPullbacks.has A₁.arr A₂.arr).cone.π₁ (HasPullbacks.has A₁.arr A₂.arr).cone.π₂ := by
  -- The book's proof uses R = x°⊚f ∪ y°⊚g, shows 1 ⊆ RR° and R°R ⊆ 1,
  -- hence R is a map (entire + simple), and xR = f, yR = g uniquely.
  classical
  -- Intersection pullback (the source of the two pushout legs).
  let pb := HasPullbacks.has A₁.arr A₂.arr
  -- Union object and its two inclusions x, y.
  let U := HasSubobjectUnions.union A₁ A₂
  let x := (HasSubobjectUnions.union_left A₁ A₂).choose
  have hx : x ≫ U.arr = A₁.arr := (HasSubobjectUnions.union_left A₁ A₂).choose_spec
  let y := (HasSubobjectUnions.union_right A₁ A₂).choose
  have hy : y ≫ U.arr = A₂.arr := (HasSubobjectUnions.union_right A₁ A₂).choose_spec
  -- The square commutes: π₁ ≫ x = π₂ ≫ y (push through the monic U.arr).
  have hw : pb.cone.π₁ ≫ x = pb.cone.π₂ ≫ y := by
    apply U.monic
    calc (pb.cone.π₁ ≫ x) ≫ U.arr = pb.cone.π₁ ≫ (x ≫ U.arr) := Cat.assoc _ _ _
      _ = pb.cone.π₁ ≫ A₁.arr := by rw [hx]
      _ = pb.cone.π₂ ≫ A₂.arr := pb.cone.w
      _ = pb.cone.π₂ ≫ (y ≫ U.arr) := by rw [hy]
      _ = (pb.cone.π₂ ≫ y) ≫ U.arr := (Cat.assoc _ _ _).symm
  -- Descent: for every cocone c there is a unique q with x ≫ q = c.ι₁, y ≫ q = c.ι₂.
  have hxmono : Monic x := by
    intro W u v huv; apply A₁.monic
    rw [← hx, ← Cat.assoc, ← Cat.assoc, huv]
  have hymono : Monic y := by
    intro W u v huv; apply A₂.monic
    rw [← hy, ← Cat.assoc, ← Cat.assoc, huv]
  have hjcov : Cover (HasBinaryCoproducts.case x y) := union_case_cover A₁ A₂ hx hy
  have hdesc : ∀ (c : PushoutCocone pb.cone.π₁ pb.cone.π₂),
      ∃ q : U.dom ⟶ c.pt, (x ≫ q = c.ι₁ ∧ y ≫ q = c.ι₂) ∧
        ∀ q' : U.dom ⟶ c.pt, x ≫ q' = c.ι₁ → y ≫ q' = c.ι₂ → q' = q := by
    intro c
    let f := c.ι₁
    let g := c.ι₂
    -- Book §1.62: form the descent relation R = x°f ∪ y°g (maps as relations via `↑`).
    let xr : BinRel 𝒞 A₁.dom U.dom := x  -- ↑x  (x : A₁.dom ⟶ U.dom)
    let yr : BinRel 𝒞 A₂.dom U.dom := y  -- ↑y
    let fr : BinRel 𝒞 A₁.dom c.pt := f   -- ↑f  (f = c.ι₁)
    let gr : BinRel 𝒞 A₂.dom c.pt := g   -- ↑g  (g = c.ι₂)
    let P := xr° ⊚ fr
    let Q := yr° ⊚ gr
    let R := P ∪ᵣ Q
    -- intersection relation and its compatibility consequence
    have hinter : RelLe (graph x ⊚ (graph y)°)
        ((graph pb.cone.π₁)° ⊚ graph pb.cone.π₂) :=
      inter_lemma x y U.arr A₁.arr A₂.arr hx hy
    have hxyg : RelLe ((graph x ⊚ (graph y)°) ⊚ graph g) (graph f) :=
      hxyg_lemma f g pb.cone.π₁ pb.cone.π₂ (graph x ⊚ (graph y)°) hinter c.w
    -- the four atomic bounds for simplicity
    have hPP : RelLe (P° ⊚ P) (graph (Cat.id c.pt)) := diag_le_one x f hxmono
    have hQQ : RelLe (Q° ⊚ Q) (graph (Cat.id c.pt)) := diag_le_one y g hymono
    have hPQ : RelLe (P° ⊚ Q) (graph (Cat.id c.pt)) := cross_le_one x y f g hxyg
    have hQP : RelLe (Q° ⊚ P) (graph (Cat.id c.pt)) := by
      -- Q°P ⊆ (P°Q)° ⊆ 1° = 1 by reciprocal symmetry of the cross bound.
      have hsub : RelLe (Q° ⊚ P) ((P° ⊚ Q)°) := by
        have h := (reciprocal_comp (P°) Q).2; rw [reciprocal_invol] at h; exact h
      exact rel_le_trans hsub (reciprocal_mono hPQ)
    have hSimple : Simple R := simple_R P Q hPP hQQ hPQ hQP
    -- entirety
    have hEntire : Entire R := by
      have hjoint : RelLe (graph (Cat.id U.dom)) ((graph x)° ⊚ graph x ∪ᵣ (graph y)° ⊚ graph y) :=
        union_joint_cover A₁ A₂ hx hy
      refine rel_le_trans hjoint (le_relUnion ?_ ?_)
      · exact xx_le_RRrecip x f R (relUnion_le_left P Q)
      · exact xx_le_RRrecip y g R (relUnion_le_right P Q)
    -- extract the descent morphism
    obtain ⟨q, hRq, hqR⟩ := map_to_graph R ⟨hEntire, hSimple⟩
    -- fac:  x ≫ q = f   and   y ≫ q = g
    -- fac (book `xR = f`): if z°k ⊆ R then z≫q = k.  Pointfree:
    --   k = 1·k ⊆ zz°·k = z(z°k) ⊆ z·R ⊆ z·q = graph(z≫q), z entire; graph faithful.
    have hfac_gen : ∀ {C : 𝒞} (z : C ⟶ U.dom) (k : C ⟶ c.pt),
        RelLe ((graph z)° ⊚ graph k) R → z ≫ q = k := by
      intro C z k hpiece
      refine (graph_faithful ?_).symm
      -- Book §1.62 fold (maps as relations via `↑`):  k = 1·k ⊆ zz°·k = z(z°k)
      --   ⊆ z·R ⊆ z·q = ↑(z≫q), using z entire (1 ⊆ zz°) and z°k ⊆ R ⊆ q.
      let zr : BinRel 𝒞 C U.dom := z       -- ↑z
      let kr : BinRel 𝒞 C c.pt := k        -- ↑k
      let qr : BinRel 𝒞 U.dom c.pt := q    -- ↑q
      calc kr
          ⊂ graph (Cat.id C) ⊚ kr := comp_graph_id_left kr
        _ ⊂ (zr ⊚ zr°) ⊚ kr := compose_le (graph_is_map z).1 (rel_le_refl _)
        _ ⊂ zr ⊚ (zr° ⊚ kr) := (compose_assoc_of_regular zr (zr°) kr).1
        _ ⊂ zr ⊚ qr := compose_le (rel_le_refl _) (rel_le_trans hpiece hRq)
        _ ⊂ graph (z ≫ q) := comp_graph z q
    have hfac1 : x ≫ q = f := hfac_gen x f (relUnion_le_left P Q)
    have hfac2 : y ≫ q = g := hfac_gen y g (relUnion_le_right P Q)
    refine ⟨q, ⟨hfac1, hfac2⟩, ?_⟩
    -- uniqueness via joint epi
    intro q' hq'1 hq'2
    apply cover_epi hjcov
    have e1 : HasBinaryCoproducts.case x y ≫ q' = HasBinaryCoproducts.case f g := by
      apply HasBinaryCoproducts.case_uniq
      · rw [← Cat.assoc, HasBinaryCoproducts.case_inl, hq'1]
      · rw [← Cat.assoc, HasBinaryCoproducts.case_inr, hq'2]
    have e2 : HasBinaryCoproducts.case x y ≫ q = HasBinaryCoproducts.case f g := by
      apply HasBinaryCoproducts.case_uniq
      · rw [← Cat.assoc, HasBinaryCoproducts.case_inl, hfac1]
      · rw [← Cat.assoc, HasBinaryCoproducts.case_inr, hfac2]
    rw [e1, e2]
  exact
    { cocone := ⟨U.dom, x, y, hw⟩
      desc := fun c => (hdesc c).choose
      fac₁ := fun c => ((hdesc c).choose_spec.1).1
      fac₂ := fun c => ((hdesc c).choose_spec.1).2
      uniq := fun c h hh₁ hh₂ => (hdesc c).choose_spec.2 h hh₁ hh₂ }

/-! ## §1.631 Complemented subobject (book definition)

  A₁ ⊆ A is COMPLEMENTED if ∃ A₂ ⊆ A with A₁∩A₂ = 0 and A₁∪A₂ = A.
  Here 0 = PreLogos.bottom A (the minimal subobject) and A = Subobject.entire A.
  The intersection is the pullback along A₁.arr and A₂.arr. -/

/-- (§1.631) A₁ is COMPLEMENTED in A if there exists A₂ with
    A₁ ∩ A₂ ≤ 0  (intersection is minimal)
    and A ≤ A₁ ∪ A₂  (union is maximal). -/
def IsComplementedSub {A : 𝒞} (A₁ : Subobject 𝒞 A) : Prop :=
  ∃ (A₂ : Subobject 𝒞 A),
    Subobject.le (Subobject.inter A₁ A₂) (PreLogos.bottom A)
    ∧ Subobject.le (Subobject.entire A) (HasSubobjectUnions.union A₁ A₂)

/-! ## §1.623 Positive pre-logoi

  A POSITIVE PRE-LOGOS has binary coproducts (equivalently:
  for every A,B there exists C with A,B as complemented subobjects). -/

class PositivePreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends PreLogos 𝒞, HasBinaryCoproducts 𝒞

/-! ## §1.621/§1.623 Disjointness of positive coproducts

  Freyd's positivity is NOT the bare case-universal-property of `HasBinaryCoproducts`.
  §1.626 is explicit: "Coproducts can exist without positivity.  Any distributive
  lattice, viewed as a category, is a pre-logos with coproducts.  It is positive iff
  it is degenerate."  In a lattice the join `A ∨ B` is a coproduct but the injections
  `A ↣ A∨B`, `B ↣ A∨B` are not jointly monic and `A ∧ B ≠ 0`.

  In a POSITIVE pre-logos the coproduct `A + B` is, by §1.623, *constructed* as the
  ambient object `C` for which `A, B ⊆ C` are subobjects with `A ∩ B = 0` and
  `A ∪ B = C` — and §1.621 says exactly such a disjoint complemented union IS a
  coproduct.  So disjointness is part of the DATA of a positive coproduct, faithfully
  recorded below as Freyd's §1.621 conditions on the injections of `HasBinaryCoproducts`:

  * `inl`, `inr` are monic (they are subobject inclusions);
  * `inl ∩ inr ≤ 0`  (the §1.621 disjointness `A₁ ∩ A₂ = 0`);
  * `inl ∪ inr = the whole coproduct`  (the §1.621 union `A₁ ∪ A₂ = A`).

  This matches the binary form of the `DisjointCoproduct` structure that S1_84 uses
  for arbitrary-indexed coproducts (uᵢ monic, uᵢ°uⱼ = 0, ⋃uᵢ°uᵢ = 1).

  RELOCATED from S1_64 (§1.64) to its natural home next to `PositivePreLogos` (§1.623),
  so the §1.624/§1.631 corollaries below can consume it without a cyclic import.

  NB: the three projection lemmas (`inl_inter_inr_le_bottom`, `inl_union_inr_entire`,
  `coprod_inl_inr_disjoint_elt`) carry `omit [PreLogos 𝒞] in`: the file-level
  `variable [PreLogos 𝒞]` would otherwise form a diamond with
  `DisjointBinaryCoproduct.toPreLogos`, and the `Subobject.inter`/`inlSub` instance
  arguments would resolve along two different `HasPullbacks` paths. -/

/-- The left injection `inl : A ⟶ A+B` packaged as a subobject of `A+B`, given that
    it is monic.  Used to phrase §1.621 disjointness `inl ∩ inr ≤ 0` via the existing
    `Subobject.inter`. -/
def inlSub [HasBinaryCoproducts 𝒞] {A B : 𝒞} (h : Monic (HasBinaryCoproducts.inl (A := A) (B := B))) :
    Subobject 𝒞 (HasBinaryCoproducts.coprod A B) :=
  ⟨A, HasBinaryCoproducts.inl, h⟩

/-- The right injection `inr : B ⟶ A+B` packaged as a subobject of `A+B`. -/
def inrSub [HasBinaryCoproducts 𝒞] {A B : 𝒞} (h : Monic (HasBinaryCoproducts.inr (A := A) (B := B))) :
    Subobject 𝒞 (HasBinaryCoproducts.coprod A B) :=
  ⟨B, HasBinaryCoproducts.inr, h⟩

/-- **§1.621/§1.623 DISJOINT BINARY COPRODUCT.**  A positive pre-logos in which the
    coproduct injections satisfy Freyd's §1.621 disjoint-complemented-union conditions.
    This is the missing positivity content that the amalgamation lemma (§1.651),
    balancedness (§1.652), and Diaconescu's theorem (§1.662) all rest on. -/
class DisjointBinaryCoproduct (𝒞 : Type u) [Cat.{v} 𝒞] extends PositivePreLogos 𝒞 where
  /-- The left injection is monic (it is a subobject inclusion). -/
  inl_monic : ∀ {A B : 𝒞}, Monic (HasBinaryCoproducts.inl (A := A) (B := B))
  /-- The right injection is monic. -/
  inr_monic : ∀ {A B : 𝒞}, Monic (HasBinaryCoproducts.inr (A := A) (B := B))
  /-- §1.621 disjointness: `inl ∩ inr = 0` (their intersection is the bottom subobject).
      The intersection is the pullback of `inl` and `inr`, here `≤ PreLogos.bottom`. -/
  inl_inter_inr : ∀ {A B : 𝒞},
    Subobject.le (Subobject.inter (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_monic)
                                  (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_monic))
                 (PreLogos.bottom (HasBinaryCoproducts.coprod A B))
  /-- §1.621 union: `inl ∪ inr = A+B` (the injections jointly cover the coproduct). -/
  inl_union_inr : ∀ {A B : 𝒞},
    Subobject.le (Subobject.entire (HasBinaryCoproducts.coprod A B))
                 (HasSubobjectUnions.union (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_monic)
                                           (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_monic))

/-! ### Reusable disjointness lemmas

  Downstream files (`amalgamation_lemma` §1.651, `pretopos_balanced` §1.652,
  the Diaconescu equivalences §1.662) need these three facts about positive
  coproducts.  Each is a direct projection of the §1.621 fields above. -/

/-- **§1.621**: in a positive (disjoint) coproduct the left injection is monic. -/
theorem inl_mono [DisjointBinaryCoproduct 𝒞] {A B : 𝒞} :
    Monic (HasBinaryCoproducts.inl (A := A) (B := B)) :=
  DisjointBinaryCoproduct.inl_monic

/-- **§1.621**: in a positive (disjoint) coproduct the right injection is monic. -/
theorem inr_mono [DisjointBinaryCoproduct 𝒞] {A B : 𝒞} :
    Monic (HasBinaryCoproducts.inr (A := A) (B := B)) :=
  DisjointBinaryCoproduct.inr_monic

-- These three projection lemmas use a FRESH type variable `𝒟` (not the file-level `𝒞`)
-- so the ambient `variable [PreLogos 𝒞]` is not in scope: it would otherwise form a
-- diamond with `DisjointBinaryCoproduct.toPreLogos` and the `Subobject.inter`/`inlSub`
-- instance arguments would resolve along two different `HasPullbacks` paths.
section DisjointProjections
variable {𝒟 : Type u} [Cat.{v} 𝒟]

/-- **§1.621 disjointness, pullback form**: the intersection (pullback) of `inl` and
    `inr` in `A+B` is the zero subobject — `inl ∩ inr ≤ 0`.  This is the categorical
    statement "`pullback(inl, inr) ≅ 0`": its domain receives a map to `(bottom).dom`,
    and `bottom_min` gives a map back, so the two are isomorphic when bottom is the
    initial object.  Phrased as a subobject inequality to stay constructive. -/
theorem inl_inter_inr_le_bottom [DisjointBinaryCoproduct 𝒟] {A B : 𝒟} :
    Subobject.le (Subobject.inter (inlSub (𝒞 := 𝒟) (A := A) (B := B) inl_mono)
                                  (inrSub (𝒞 := 𝒟) (A := A) (B := B) inr_mono))
                 (PreLogos.bottom (HasBinaryCoproducts.coprod A B)) :=
  DisjointBinaryCoproduct.inl_inter_inr

/-- **§1.621/§1.623 union**: `inl ∪ inr = A+B`; the injections jointly cover. -/
theorem inl_union_inr_entire [DisjointBinaryCoproduct 𝒟] {A B : 𝒟} :
    Subobject.le (Subobject.entire (HasBinaryCoproducts.coprod A B))
                 (HasSubobjectUnions.union (inlSub (𝒞 := 𝒟) (A := A) (B := B) inl_mono)
                                           (inrSub (𝒞 := 𝒟) (A := A) (B := B) inr_mono)) :=
  DisjointBinaryCoproduct.inl_union_inr

/-- **§1.621 disjointness, elementwise form** (the shape `amalgamation_lemma` and the
    cokernel-pair argument of §1.652 actually consume): if a generalized element of `A`
    and one of `B` are identified in `A+B` (`f ≫ inl = g ≫ inr`), then they factor
    through the bottom (zero) subobject of `A+B` — there is a map `e : X ⟶ (bottom).dom`
    with `e ≫ (bottom).arr = f ≫ inl`.  This is the categorical content of
    "`pullback(inl, inr) ≅ 0`": the equalizing pair lifts into the intersection
    `inl ∩ inr`, which is `≤ 0` by §1.621.  Derived from `inl_inter_inr_le_bottom`. -/
theorem coprod_inl_inr_disjoint_elt [DisjointBinaryCoproduct 𝒟] {A B : 𝒟}
    {X : 𝒟} (f : X ⟶ A) (g : X ⟶ B)
    (hfg : f ≫ HasBinaryCoproducts.inl = g ≫ HasBinaryCoproducts.inr) :
    ∃ e : X ⟶ (PreLogos.bottom (HasBinaryCoproducts.coprod A B)).dom,
      e ≫ (PreLogos.bottom (HasBinaryCoproducts.coprod A B)).arr = f ≫ HasBinaryCoproducts.inl := by
  -- f, g form a cone over (inlSub.arr, inrSub.arr); lift into their pullback = inl ∩ inr.
  let pb := HasPullbacks.has (inlSub (𝒞 := 𝒟) (A := A) (B := B) inl_mono).arr
                             (inrSub (𝒞 := 𝒟) (A := A) (B := B) inr_mono).arr
  have hcone : f ≫ (inlSub (𝒞 := 𝒟) (A := A) (B := B) inl_mono).arr
             = g ≫ (inrSub (𝒞 := 𝒟) (A := A) (B := B) inr_mono).arr := hfg
  let w := pb.lift ⟨X, f, g, hcone⟩
  -- inl ∩ inr ≤ bottom gives e with (w ≫ e) ≫ bottom.arr = w ≫ (inl ∩ inr).arr = f ≫ inl.
  obtain ⟨e, he⟩ := inl_inter_inr_le_bottom (𝒟 := 𝒟) (A := A) (B := B)
  have hwπ₁ : w ≫ pb.cone.π₁ = f := pb.lift_fst ⟨X, f, g, hcone⟩
  refine ⟨w ≫ e, ?_⟩
  -- (inl ∩ inr).arr = π₁ ≫ inlSub.arr = π₁ ≫ inl, and w ≫ π₁ = f.
  calc (w ≫ e) ≫ (PreLogos.bottom (HasBinaryCoproducts.coprod A B)).arr
      = w ≫ (e ≫ (PreLogos.bottom (HasBinaryCoproducts.coprod A B)).arr) := Cat.assoc _ _ _
    _ = w ≫ (Subobject.inter (inlSub (𝒞 := 𝒟) (A := A) (B := B) inl_mono)
                             (inrSub (𝒞 := 𝒟) (A := A) (B := B) inr_mono)).arr := by rw [he]
    _ = w ≫ (pb.cone.π₁ ≫ (inlSub (𝒞 := 𝒟) (A := A) (B := B) inl_mono).arr) := rfl
    _ = (w ≫ pb.cone.π₁) ≫ (inlSub (𝒞 := 𝒟) (A := A) (B := B) inl_mono).arr := (Cat.assoc _ _ _).symm
    _ = f ≫ HasBinaryCoproducts.inl := by rw [hwπ₁]; rfl

/-- **§1.621 helper**: a pushout of a span `C ⇉ A,B` whose apex `C` is INITIAL
    (`init_uniq` — every parallel pair of maps out of `C` is equal) is the BINARY
    COPRODUCT `A + B`.  When the span source is initial, the coproduct cocone
    `(A+B, inl, inr)` automatically commutes (`f ≫ inl = g ≫ inr`, both maps out of the
    initial `C`), so the two universal properties identify the pushout apex with `A+B`. -/
theorem pushout_over_initial_is_coproduct [HasBinaryCoproducts 𝒟]
    {C A B : 𝒟} {f : C ⟶ A} {g : C ⟶ B} (po : HasPushout f g)
    (hCinit : ∀ {X : 𝒟} (u v : C ⟶ X), u = v) :
    Isomorphic po.cocone.pt (HasBinaryCoproducts.coprod A B) := by
  -- coproduct cocone over (f, g): f ≫ inl = g ≫ inr since both are maps C → A+B out of initial C.
  let coCoc : PushoutCocone f g :=
    ⟨HasBinaryCoproducts.coprod A B, HasBinaryCoproducts.inl, HasBinaryCoproducts.inr,
     hCinit _ _⟩
  -- desc : po.pt → A+B from the pushout UMP.
  let φ : po.cocone.pt ⟶ HasBinaryCoproducts.coprod A B := po.desc coCoc
  have hφ₁ : po.cocone.ι₁ ≫ φ = HasBinaryCoproducts.inl := po.fac₁ coCoc
  have hφ₂ : po.cocone.ι₂ ≫ φ = HasBinaryCoproducts.inr := po.fac₂ coCoc
  -- ψ : A+B → po.pt from the coproduct UMP (case of the pushout legs).
  let ψ : HasBinaryCoproducts.coprod A B ⟶ po.cocone.pt :=
    HasBinaryCoproducts.case po.cocone.ι₁ po.cocone.ι₂
  have hψ₁ : HasBinaryCoproducts.inl ≫ ψ = po.cocone.ι₁ := HasBinaryCoproducts.case_inl _ _
  have hψ₂ : HasBinaryCoproducts.inr ≫ ψ = po.cocone.ι₂ := HasBinaryCoproducts.case_inr _ _
  refine ⟨φ, ψ, ?_, ?_⟩
  · -- φ ≫ ψ = id_po.pt  by pushout uniqueness (both legs land back on ι₁, ι₂).
    have h1 : po.cocone.ι₁ ≫ (φ ≫ ψ) = po.cocone.ι₁ := by
      rw [← Cat.assoc, hφ₁, hψ₁]
    have h2 : po.cocone.ι₂ ≫ (φ ≫ ψ) = po.cocone.ι₂ := by
      rw [← Cat.assoc, hφ₂, hψ₂]
    -- both φ≫ψ and id are the desc of po.cocone (as a cocone over itself).
    rw [po.uniq po.cocone (φ ≫ ψ) h1 h2,
        po.uniq po.cocone (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)]
  · -- ψ ≫ φ = id_{A+B}  by coproduct uniqueness (both legs land back on inl, inr).
    have h1 : HasBinaryCoproducts.inl ≫ (ψ ≫ φ) = HasBinaryCoproducts.inl := by
      rw [← Cat.assoc, hψ₁, hφ₁]
    have h2 : HasBinaryCoproducts.inr ≫ (ψ ≫ φ) = HasBinaryCoproducts.inr := by
      rw [← Cat.assoc, hψ₂, hφ₂]
    rw [HasBinaryCoproducts.case_uniq _ _ (ψ ≫ φ) h1 h2,
        HasBinaryCoproducts.case_uniq _ _ (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)]

end DisjointProjections

/-- A subobject containing the entire subobject is itself entire: `entire A ≤ S` gives a
    section of `S.arr`, and a monic with a section is iso. -/
theorem entire_of_entire_le {A : 𝒞} {S : Subobject 𝒞 A}
    (h : (Subobject.entire A).le S) : S.IsEntire := by
  obtain ⟨s, hs⟩ := h          -- s : A → S.dom, s ≫ S.arr = (entire A).arr = id_A
  have hsec : s ≫ S.arr = Cat.id A := hs
  refine ⟨s, ?_, hsec⟩
  -- S.arr ≫ s = id_{S.dom} : push through the monic S.arr.
  apply S.monic
  calc (S.arr ≫ s) ≫ S.arr = S.arr ≫ (s ≫ S.arr) := Cat.assoc _ _ _
    _ = S.arr ≫ Cat.id A := by rw [hsec]
    _ = S.arr := Cat.comp_id _
    _ = Cat.id _ ≫ S.arr := (Cat.id_comp _).symm

/-- `entire A ≤ f#(entire B)`: the inverse image of the whole of `B` along `f : A → B`
    is the whole of `A`.  Witness: the pullback lift of the cone `⟨A, id_A, f⟩` over
    `(f, id_B)`, which composes with `(InverseImage f (entire B)).arr = π₁` to `id_A`. -/
theorem entire_le_invImage_entire {A B : 𝒞} (f : A ⟶ B) :
    (Subobject.entire A).le (InverseImage f (Subobject.entire B)) := by
  let pb := HasPullbacks.has f (Subobject.entire B).arr
  let c : Cone f (Subobject.entire B).arr :=
    ⟨A, Cat.id A, f, by
      show Cat.id A ≫ f = f ≫ (Subobject.entire B).arr
      rw [Cat.id_comp, show (Subobject.entire B).arr = Cat.id B from rfl, Cat.comp_id]⟩
  refine ⟨pb.lift c, ?_⟩
  show pb.lift c ≫ pb.cone.π₁ = Cat.id A
  exact pb.lift_fst c

omit [PreLogos 𝒞] in
/-- §1.624: In a positive pre-logos, f: A → B₁+B₂ decomposes as
    f₁+f₂ from A₁ → B₁, A₂ → B₂ where A = A₁+A₂.
    Proof: A₁ = f#(inl), A₂ = f#(inr) via pasting lemma (§1.62).

    `omit [PreLogos 𝒞]`: the file-level `variable [PreLogos 𝒞]` would form a diamond with
    `DisjointBinaryCoproduct.toPreLogos`, so `union`/`InverseImage`/`bottom`/pullbacks would
    resolve along two different instance paths (the §1.621 projection lemmas only carry the
    DBC path).  Dropping the ambient `PreLogos` leaves a single coherent instance. -/
theorem decompose_via_coproduct [DisjointBinaryCoproduct 𝒞] {A B₁ B₂ : 𝒞}
    (f : A ⟶ HasBinaryCoproducts.coprod B₁ B₂) :
    ∃ (A₁ A₂ : 𝒞) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂), Isomorphic A (HasBinaryCoproducts.coprod A₁ A₂) := by
  -- A₁ := f#(inl), A₂ := f#(inr) as subobjects of A; f₁, f₂ are the pullback legs into B₁, B₂.
  let Inl := inlSub (𝒞 := 𝒞) (A := B₁) (B := B₂) inl_mono
  let Inr := inrSub (𝒞 := 𝒞) (A := B₁) (B := B₂) inr_mono
  let A₁ : Subobject 𝒞 A := InverseImage f Inl
  let A₂ : Subobject 𝒞 A := InverseImage f Inr
  -- f₁ : A₁.dom → B₁ is the second pullback leg (Inl.dom = B₁); likewise f₂.
  let f₁ : A₁.dom ⟶ B₁ := (HasPullbacks.has f Inl.arr).cone.π₂
  let f₂ : A₂.dom ⟶ B₂ := (HasPullbacks.has f Inr.arr).cone.π₂
  refine ⟨A₁.dom, A₂.dom, f₁, f₂, ?_⟩
  -- Abbreviations for the three pullbacks that make up A₁, A₂ and their intersection.
  let pbL := HasPullbacks.has f Inl.arr   -- A₁.dom = pbL.pt, A₁.arr = pbL.π₁, f₁ = pbL.π₂
  let pbR := HasPullbacks.has f Inr.arr   -- A₂.dom = pbR.pt, A₂.arr = pbR.π₁, f₂ = pbR.π₂
  let pbI := HasPullbacks.has A₁.arr A₂.arr  -- intersection apex (span source of the pasting lemma)
  -- ===== (1) The union A₁ ∪ A₂ is ENTIRE =====
  -- entire A ≤ f#(entire B) ≤ f#(Inl ∪ Inr) = f#(Inl) ∪ f#(Inr) = A₁ ∪ A₂.
  let B := HasBinaryCoproducts.coprod B₁ B₂
  have hUnion_entire : (HasSubobjectUnions.union A₁ A₂).IsEntire := by
    apply entire_of_entire_le
    -- step a: entire A ≤ f#(entire B)
    have ha : (Subobject.entire A).le (InverseImage f (Subobject.entire B)) :=
      entire_le_invImage_entire f
    -- step b: entire B ≤ Inl ∪ Inr  (disjoint coproduct union covers the whole)
    have hbu : (Subobject.entire B).le (HasSubobjectUnions.union Inl Inr) :=
      inl_union_inr_entire (𝒟 := 𝒞) (A := B₁) (B := B₂)
    have hb : (InverseImage f (Subobject.entire B)).le
        (InverseImage f (HasSubobjectUnions.union Inl Inr)) :=
      invImage_mono_local f hbu
    -- step c (pre-logos): f#(Inl ∪ Inr) ≤ f#Inl ∪ f#Inr = A₁ ∪ A₂
    have hc : (InverseImage f (HasSubobjectUnions.union Inl Inr)).le
        (HasSubobjectUnions.union (InverseImage f Inl) (InverseImage f Inr)) :=
      (PreLogos.invImage_preserves_union f Inl Inr).1
    exact subLe_trans ha (subLe_trans hb hc)
  -- ===== (2) The intersection apex pbI.pt is INITIAL =====
  -- Build a map pbI.pt → (Inl ∩ Inr).dom over B; that subobject is ≤ bottom B, and
  -- bottom B's domain ≅ the coterminator 0, so pbI.pt has a map to 0, hence is iso to 0.
  -- Use the DBC instance's PreLogos so it coincides with the one in the goal's subobjects.
  let hPL : PreLogos 𝒞 := (DisjointBinaryCoproduct.toPositivePreLogos).toPreLogos
  let zeroObj := (minimal_subobject_of_one_is_coterminator hPL).zero
  have hCinit : ∀ {X : 𝒞} (u v : pbI.cone.pt ⟶ X), u = v := by
    -- (a) cone over (Inl.arr, Inr.arr) from the intersection apex:
    --     legs  q₁≫f₁ : pbI.pt → B₁  and  q₂≫f₂ : pbI.pt → B₂.
    let pbJ := HasPullbacks.has Inl.arr Inr.arr   -- (Inl ∩ Inr).dom = pbJ.pt
    have hsq : (pbI.cone.π₁ ≫ pbL.cone.π₂) ≫ Inl.arr
             = (pbI.cone.π₂ ≫ pbR.cone.π₂) ≫ Inr.arr := by
      calc (pbI.cone.π₁ ≫ pbL.cone.π₂) ≫ Inl.arr
          = pbI.cone.π₁ ≫ (pbL.cone.π₂ ≫ Inl.arr) := Cat.assoc _ _ _
        _ = pbI.cone.π₁ ≫ (pbL.cone.π₁ ≫ f) := by rw [pbL.cone.w]
        _ = (pbI.cone.π₁ ≫ pbL.cone.π₁) ≫ f := (Cat.assoc _ _ _).symm
        _ = (pbI.cone.π₁ ≫ A₁.arr) ≫ f := rfl
        _ = (pbI.cone.π₂ ≫ A₂.arr) ≫ f := by rw [pbI.cone.w]
        _ = (pbI.cone.π₂ ≫ pbR.cone.π₁) ≫ f := rfl
        _ = pbI.cone.π₂ ≫ (pbR.cone.π₁ ≫ f) := Cat.assoc _ _ _
        _ = pbI.cone.π₂ ≫ (pbR.cone.π₂ ≫ Inr.arr) := by rw [pbR.cone.w]
        _ = (pbI.cone.π₂ ≫ pbR.cone.π₂) ≫ Inr.arr := (Cat.assoc _ _ _).symm
    let cJ : Cone Inl.arr Inr.arr :=
      ⟨pbI.cone.pt, pbI.cone.π₁ ≫ pbL.cone.π₂, pbI.cone.π₂ ≫ pbR.cone.π₂, hsq⟩
    -- m lands in (Inl ∩ Inr).dom = pbJ.cone.pt, matching e's domain.
    let m : pbI.cone.pt ⟶ (Subobject.inter Inl Inr).dom := pbJ.lift cJ
    -- (b) Inl ∩ Inr ≤ bottom B : disjointness.  (Subobject.inter Inl Inr).arr = pbJ.π₁ ≫ Inl.arr.
    obtain ⟨e, he⟩ := inl_inter_inr_le_bottom (𝒟 := 𝒞) (A := B₁) (B := B₂)
    -- e : (Inl ∩ Inr).dom → (bottom B).dom,  e ≫ (bottom B).arr = (Inl ∩ Inr).arr.
    -- (c) (bottom B).dom ≅ zeroObj.
    have hbotiso : Isomorphic (PreLogos.bottom B).dom zeroObj :=
      hPL.bottom_dom_iso B hPL.toHasTerminal.one
    obtain ⟨ζ, hζ⟩ := hbotiso   -- ζ : (bottom B).dom → zeroObj, IsIso ζ
    -- map pbI.pt → zeroObj, hence pbI.pt ≅ zeroObj by any_map_to_zero_is_iso.
    let g₀ : pbI.cone.pt ⟶ zeroObj := m ≫ e ≫ ζ
    have hg₀_iso : IsIso g₀ := any_map_to_zero_is_iso hPL g₀
    obtain ⟨g₀inv, hg₀g₀inv, hg₀inv_g₀⟩ := hg₀_iso
    -- pbI.pt ≅ zeroObj ⟹ any two maps out of pbI.pt agree (zeroObj is initial).
    intro X u v
    have key : ∀ (w : pbI.cone.pt ⟶ X), w = g₀ ≫ (g₀inv ≫ w) := by
      intro w
      rw [← Cat.assoc, hg₀g₀inv, Cat.id_comp]
    rw [key u, key v,
        (minimal_subobject_of_one_is_coterminator hPL).init_uniq (g₀inv ≫ u) (g₀inv ≫ v)]
  -- ===== (3) Assemble: A ≅ (A₁ ∪ A₂).dom ≅ coprod A₁.dom A₂.dom =====
  -- The pasting lemma: union is the pushout of the intersection's two projections.
  let po := pasting_lemma A₁ A₂
  -- pushout over the initial intersection apex IS the coproduct A₁.dom + A₂.dom.
  have hpoiso : Isomorphic po.cocone.pt (HasBinaryCoproducts.coprod A₁.dom A₂.dom) :=
    pushout_over_initial_is_coproduct po (@hCinit)
  -- po.cocone.pt = (A₁ ∪ A₂).dom, which is ≅ A since the union is entire.
  have hA_union : Isomorphic A (HasSubobjectUnions.union A₁ A₂).dom := by
    obtain ⟨arrinv, h1, h2⟩ := hUnion_entire
    exact ⟨arrinv, (HasSubobjectUnions.union A₁ A₂).arr, h2, h1⟩
  exact isomorphic_trans hA_union hpoiso

/-! ## §1.625 Representations of positive pre-logoi

  A functor T: 𝒜 → ℬ between positive pre-logoi is a representation of pre-logoi
  iff it preserves disjoint unions.  (The book uses that union = image of coproduct.)

  MISSING: this statement cannot yet be stated faithfully in this repo — it quantifies over
  "T is a representation of regular categories" and "T preserves disjoint unions", neither of
  which has a predicate here.  A faithful formalization needs a `PreLogosFunctor` / "representation
  of regular categories" structure (preserving finite products, equalizers, images) plus a
  `PreservesDisjointUnions T` predicate.  Per the integrity rule the previous vacuous
  `: True := trivial` stub has been removed rather than left in place. -/

/-! ## §1.632 Generating set / basis

  A set ℱ of objects is GENERATING if the representable functors
  {(G, -)} form an embedding.  A BASIS is a collectively faithful set. -/

/-- ℱ is GENERATING if the functors Hom(G,-) for G∈ℱ are collectively
    an embedding (i.e., injective on morphisms). -/
def IsGeneratingSet (ℱ : 𝒞 → Prop) : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B), (∀ G : 𝒞, ℱ G → (∀ h : G ⟶ A, h ≫ f = h ≫ g)) → f = g

/-- ℱ is a BASIS if the functors Hom(G,-) for G∈ℱ are collectively
    faithful.  In a Cartesian category: for every proper A'↣A, ∃ G∈ℱ
    and G→A not factoring through A'. -/
def IsBasis [HasPullbacks 𝒞] (ℱ : 𝒞 → Prop) : Prop :=
  IsGeneratingSet ℱ ∧
  ∀ {A' A : 𝒞} (m : A' ⟶ A), Monic m → ¬ IsIso m →
    ∃ G : 𝒞, ℱ G ∧ ∃ (x : G ⟶ A), ¬ ∃ (y : G ⟶ A'), y ≫ m = x

/-! ## §1.634 Pre-filter

  A non-empty ℱ ⊆ Sub(1) is a PRE-FILTER if it's ↓-directed.
  For a pre-filter ℱ, define T_ℱ : A → 𝒮 the colimit of Hom(U,-). -/

/-- ℱ is a pre-filter in the subobject lattice of 1: non-empty and
    ∀ U,V ∈ ℱ, ∃ W ∈ ℱ with W ≤ U and W ≤ V. -/
def IsPreFilter (ℱ : (Subobject 𝒞 one) → Prop) : Prop :=
  (∃ U, ℱ U) ∧ ∀ (U V : Subobject 𝒞 one), ℱ U → ℱ V → ∃ W, ℱ W ∧ Subobject.le W U ∧ Subobject.le W V

/-- T_ℱ(A) = colim_{U∈ℱ} Hom(U, A).  Represented here as the type of pairs
    (U, hU, f : U.dom → A) for U in the pre-filter ℱ.  The full definition
    requires a colimit of Hom-sets (equivalence classes).  For U projective,
    T_ℱ preserves finite products and equalizers; if ℱ is an ultra-filter in a
    Boolean algebra, T_ℱ preserves unions (§1.634-1.635). -/
structure PrefilterMap (ℱ : (Subobject 𝒞 one) → Prop) (A : 𝒞) where
  U    : Subobject 𝒞 one
  hU   : ℱ U
  map  : U.dom ⟶ A

def prefilter_functor (ℱ : (Subobject 𝒞 one) → Prop) (_hℱ : IsPreFilter ℱ) : 𝒞 → Type (max u v) :=
  PrefilterMap ℱ

/-! ## §1.635 Representation theorem for pre-logoi

  Every small positive pre-logos is faithfully representable in a
  power of the category of sets.

  SCOPE.  The Lean statement asks only for a `SeparatesMaps` (faithful) representation
  `T : A → 𝒮^|A|`.  That is exactly the conclusion of the Henkin–Lubkin theorem
  `henkin_lubkin` (§1.55), whose witness is the covariant hom-functor representation
  `A ↦ (i ↦ Hom(i, A))`; it separates maps for ANY small category (Cayley faithfulness,
  `homRep_separates`) and is choice-free.  A `PositivePreLogos` is in particular a
  `RegularCategory` (it `extends PreLogos ⊇ RegularCategory`), which provides every
  component of `PreRegularCategory` (`HasTerminal`, `HasBinaryProducts`, `HasPullbacks`,
  `PullbacksTransferCovers`), so `henkin_lubkin` applies directly.

  The book's deeper §1.635 content — the Boolean algebra of complemented subterminators,
  the ultra-filter (axiom of choice), and the stalk functors `T_ℱ` that additionally
  preserve *disjoint unions* — is what makes the representation a *representation of
  pre-logoi* (union-preserving), NOT what is needed to make it faithful.  That
  union-preservation is not captured by the `SeparatesMaps` statement here; it is recorded
  separately in the §1.634 `prefilter_functor`/`IsPreFilter` development above and would be
  the content of a strengthened "preserves disjoint unions" statement. -/

theorem prelogos_representation_theorem (A : Type u) [Cat.{u} A] [PositivePreLogos A] :
    ∃ (T : A → (A → Type u)) (_ : Functor T), SeparatesMaps T := by
  -- A positive pre-logos is a regular category, hence pre-regular; apply Henkin–Lubkin.
  letI : PreRegularCategory A :=
    { toHasTerminal := inferInstance, toHasBinaryProducts := inferInstance,
      toHasPullbacks := inferInstance, toPullbacksTransferCovers := inferInstance }
  exact henkin_lubkin A


-- BOOK §1.634: If A is a pre-logos then T_ℱ preserves disjoint unions iff
--   (0 ∉ ℱ) and (U₁+U₂ ∈ ℱ implies U₁ ∈ ℱ or U₂ ∈ ℱ).
-- TODO: needs positive pre-logos + a formal `preservesDisjointUnions T_ℱ` predicate;
-- stated informally here pending `PrefilterMap` equivalence-class quotient.

-- BOOK §1.635: If F̂ is an ultra-filter in the boolean algebra of complemented
-- subterminators, then T_F̂ is a representation of pre-logoi.
-- TODO: needs ultra-filter (axiom of choice) + `PreLogosFunctor` predicate.
-- The faithful-representation half is `prelogos_representation_theorem` above.

-- BOOK §1.636: Any Horn sentence in the predicates of pre-logoi that holds for the
-- category of sets holds for all positive pre-logoi.
-- TODO: this is a meta-theorem (transfer along §1.635 representation); not directly
-- formalizable as a single Lean statement without a reflection layer.

/-- FILTER in a subobject lattice: up-closed pre-filter (§1.634). -/
def IsFilter (ℱ : (Subobject 𝒞 one) → Prop) : Prop :=
  IsPreFilter ℱ ∧ ∀ (U V : Subobject 𝒞 one), ℱ U → Subobject.le U V → ℱ V

/-! ## §1.631 Complemented subobject of a projective is projective

  In a positive pre-logos, if P is a complemented subobject of a projective
  object Q (so Q ≅ P + P' for some P'), then P is projective.
  Proof: given a cover x : A ↠ P, extend to A + P' → P + P' using the
  coproduct inclusion; this is a cover of the projective Q, so it splits;
  composing with inl gives a section P → A. -/

omit [PreLogos 𝒞] in
/-- §1.631: In a positive pre-logos, a complemented subobject of a projective
    object is projective.

    Stated with `[DisjointBinaryCoproduct 𝒞]`: Freyd's positivity (§1.621/§1.623) is exactly
    coproduct disjointness, which the proof needs (`coprod_inl_inr_disjoint_elt`) to show that
    `σ : P → B+P'` factors through `inl_B`.  `DisjointBinaryCoproduct` is the faithful rendering
    of "positive pre-logos" in this repo. -/
theorem complemented_of_projective_is_projective [DisjointBinaryCoproduct 𝒞]
    {Q : 𝒞} (hQ : Projective Q) {P : 𝒞} (P' : 𝒞)
    (hiso : Isomorphic Q (HasBinaryCoproducts.coprod P P')) :
    Projective P := by
  -- Given any cover y : B ↠ P we produce a section P → B.
  intro B y hy
  obtain ⟨φ, φ_inv, hφφ_inv, hφ_inv_φ⟩ := hiso
  -- φ : Q → P+P', φ_inv : P+P' → Q, φ ≫ φ_inv = id_Q, φ_inv ≫ φ = id_{P+P'}.
  -- φ_inv is monic (retraction φ gives left inverse).
  have hφ_inv_mono : Monic φ_inv :=
    mono_of_retraction φ_inv φ hφ_inv_φ
  -- Form h := case(y ≫ inl, inr) : B+P' → P+P'.
  -- Key equations: inl_B ≫ h = y ≫ inl_P (by case_inl) and inr_P' ≫ h = inr_P' (by case_inr).
  let h : HasBinaryCoproducts.coprod B P' ⟶ HasBinaryCoproducts.coprod P P' :=
    HasBinaryCoproducts.case (y ≫ HasBinaryCoproducts.inl) HasBinaryCoproducts.inr
  have h_inl : HasBinaryCoproducts.inl ≫ h = y ≫ HasBinaryCoproducts.inl :=
    HasBinaryCoproducts.case_inl _ _
  -- h is a cover: show (image h).IsEntire via union_via_coproduct_image.
  have hh : Cover h := by
    rw [cover_iff_image_entire]
    -- Step 1: IsImage h U_h where U_h = union(image(y ≫ inl_P), image(inr_{P'}))
    have hImgH : IsImage h (HasSubobjectUnions.union
        (image (y ≫ HasBinaryCoproducts.inl))
        (image (HasBinaryCoproducts.inr (A := P) (B := P')))) :=
      union_via_coproduct_image (y ≫ HasBinaryCoproducts.inl)
        (HasBinaryCoproducts.inr (A := P) (B := P'))
    -- Step 2: case(inl_P, inr_{P'}) = id_{P+P'}
    have hcase_id :
        HasBinaryCoproducts.case
          (HasBinaryCoproducts.inl (A := P) (B := P'))
          (HasBinaryCoproducts.inr (A := P) (B := P')) = Cat.id _ :=
      (HasBinaryCoproducts.case_uniq
        (HasBinaryCoproducts.inl (A := P) (B := P'))
        (HasBinaryCoproducts.inr (A := P) (B := P'))
        (Cat.id _)
        (Cat.comp_id _) (Cat.comp_id _)).symm
    -- Step 3: IsImage (id_{P+P'}) U_0 where U_0 = union(image inl_P, image inr_{P'})
    have hImgId0 : IsImage (Cat.id (HasBinaryCoproducts.coprod P P'))
        (HasSubobjectUnions.union
          (image (HasBinaryCoproducts.inl (A := P) (B := P')))
          (image (HasBinaryCoproducts.inr (A := P) (B := P'))))  := by
      rw [← hcase_id]
      exact union_via_coproduct_image
        (HasBinaryCoproducts.inl (A := P) (B := P'))
        (HasBinaryCoproducts.inr (A := P) (B := P'))
    -- Step 4: image(id) is entire (id is iso hence cover)
    have hid_entire : (image (Cat.id (HasBinaryCoproducts.coprod P P'))).IsEntire := by
      rw [← cover_iff_image_entire]
      exact iso_cover _ ⟨Cat.id _, Cat.comp_id _, Cat.id_comp _⟩
    -- Step 5: U_0 is entire. k : (image id).dom → U_0.dom with k ≫ U_0.arr = (image id).arr.
    -- U_0.arr = k_inv ≫ (image id).arr (iso ≫ iso = iso).
    have hU0_entire :
        (HasSubobjectUnions.union
          (image (HasBinaryCoproducts.inl (A := P) (B := P')))
          (image (HasBinaryCoproducts.inr (A := P) (B := P')))).IsEntire := by
      obtain ⟨k, hk⟩ := (HasImages.isImage (Cat.id _)).2 _ hImgId0.1
      obtain ⟨k_inv, hkk_inv, hk_inv_k⟩ :=
        image_comparison_iso (HasImages.isImage (Cat.id _)) hImgId0 k hk
      -- Goal is (HasSubobjectUnions.union ...).IsEntire = IsIso (union ...).arr
      -- We show union.arr = k_inv ≫ (image id).arr  and then use isIso_comp.
      -- union.arr: id ≫ union.arr = (k_inv ≫ k) ≫ union.arr = k_inv ≫ (k ≫ union.arr) = k_inv ≫ image.arr
      have hU0_arr_eq : (HasSubobjectUnions.union
            (image (HasBinaryCoproducts.inl (A := P) (B := P')))
            (image (HasBinaryCoproducts.inr (A := P) (B := P')))).arr =
          k_inv ≫ (HasImages.image (Cat.id (HasBinaryCoproducts.coprod P P'))).arr :=
        calc (HasSubobjectUnions.union
              (image (HasBinaryCoproducts.inl (A := P) (B := P')))
              (image (HasBinaryCoproducts.inr (A := P) (B := P')))).arr
            = Cat.id _ ≫ (HasSubobjectUnions.union
                (image (HasBinaryCoproducts.inl (A := P) (B := P')))
                (image (HasBinaryCoproducts.inr (A := P) (B := P')))).arr := (Cat.id_comp _).symm
          _ = (k_inv ≫ k) ≫ (HasSubobjectUnions.union
                (image (HasBinaryCoproducts.inl (A := P) (B := P')))
                (image (HasBinaryCoproducts.inr (A := P) (B := P')))).arr := by rw [hk_inv_k]
          _ = k_inv ≫ (k ≫ (HasSubobjectUnions.union
                (image (HasBinaryCoproducts.inl (A := P) (B := P')))
                (image (HasBinaryCoproducts.inr (A := P) (B := P')))).arr) := Cat.assoc _ _ _
          _ = k_inv ≫ (HasImages.image (Cat.id (HasBinaryCoproducts.coprod P P'))).arr := by rw [hk]
      show (HasSubobjectUnions.union
          (image (HasBinaryCoproducts.inl (A := P) (B := P')))
          (image (HasBinaryCoproducts.inr (A := P) (B := P')))).IsEntire
      rw [Subobject.IsEntire, hU0_arr_eq]
      exact isIso_comp ⟨k, hk_inv_k, hkk_inv⟩ hid_entire
    -- Step 6: image_cover_comp gives le equivalence image(y ≫ inl) ≅ image(inl)
    obtain ⟨hle_yinl_inl, hle_inl_yinl⟩ := image_cover_comp y HasBinaryCoproducts.inl hy
    -- Step 7: U_h ≤ U_0 and U_0 ≤ U_h
    have hle_Uh_U0 :
        (HasSubobjectUnions.union
          (image (y ≫ HasBinaryCoproducts.inl))
          (image (HasBinaryCoproducts.inr (A := P) (B := P')))).le
        (HasSubobjectUnions.union
          (image (HasBinaryCoproducts.inl (A := P) (B := P')))
          (image (HasBinaryCoproducts.inr (A := P) (B := P'))))  := by
      apply HasSubobjectUnions.union_min
      · obtain ⟨p, hp⟩ := hle_yinl_inl
        obtain ⟨q, hq⟩ := HasSubobjectUnions.union_left
            (image (HasBinaryCoproducts.inl (A := P) (B := P')))
            (image (HasBinaryCoproducts.inr (A := P) (B := P')))
        exact ⟨p ≫ q, by rw [Cat.assoc, hq, hp]⟩
      · exact HasSubobjectUnions.union_right _ _
    have hle_U0_Uh :
        (HasSubobjectUnions.union
          (image (HasBinaryCoproducts.inl (A := P) (B := P')))
          (image (HasBinaryCoproducts.inr (A := P) (B := P')))).le
        (HasSubobjectUnions.union
          (image (y ≫ HasBinaryCoproducts.inl))
          (image (HasBinaryCoproducts.inr (A := P) (B := P'))))  := by
      apply HasSubobjectUnions.union_min
      · obtain ⟨p, hp⟩ := hle_inl_yinl
        obtain ⟨q, hq⟩ := HasSubobjectUnions.union_left
            (image (y ≫ HasBinaryCoproducts.inl))
            (image (HasBinaryCoproducts.inr (A := P) (B := P')))
        exact ⟨p ≫ q, by rw [Cat.assoc, hq, hp]⟩
      · exact HasSubobjectUnions.union_right _ _
    -- Step 8: U_h is entire. Mutual le + monicity → j iso → U_h.arr = j ≫ U_0.arr iso.
    have hUh_entire :
        (HasSubobjectUnions.union
          (image (y ≫ HasBinaryCoproducts.inl))
          (image (HasBinaryCoproducts.inr (A := P) (B := P')))).IsEntire := by
      obtain ⟨j, hj⟩ := hle_Uh_U0   -- j ≫ U_0.arr = U_h.arr
      obtain ⟨k, hk⟩ := hle_U0_Uh   -- k ≫ U_h.arr = U_0.arr
      have hjk : j ≫ k = Cat.id _ :=
        (HasSubobjectUnions.union
          (image (y ≫ HasBinaryCoproducts.inl))
          (image (HasBinaryCoproducts.inr (A := P) (B := P')))).monic
        (j ≫ k) (Cat.id _) (by rw [Cat.assoc, hk, hj, Cat.id_comp])
      have hkj : k ≫ j = Cat.id _ :=
        (HasSubobjectUnions.union
          (image (HasBinaryCoproducts.inl (A := P) (B := P')))
          (image (HasBinaryCoproducts.inr (A := P) (B := P')))).monic
        (k ≫ j) (Cat.id _) (by rw [Cat.assoc, hj, hk, Cat.id_comp])
      rw [Subobject.IsEntire, show
          (HasSubobjectUnions.union
            (image (y ≫ HasBinaryCoproducts.inl))
            (image (HasBinaryCoproducts.inr (A := P) (B := P')))).arr =
          j ≫ (HasSubobjectUnions.union
            (image (HasBinaryCoproducts.inl (A := P) (B := P')))
            (image (HasBinaryCoproducts.inr (A := P) (B := P')))).arr
          from hj.symm]
      exact isIso_comp ⟨k, hjk, hkj⟩ hU0_entire
    -- Step 9: transfer IsEntire from U_h to image h via image_comparison_iso
    obtain ⟨c, hc⟩ := (HasImages.isImage h).2
        (HasSubobjectUnions.union
          (image (y ≫ HasBinaryCoproducts.inl))
          (image (HasBinaryCoproducts.inr (A := P) (B := P'))))
        hImgH.1
    have hc_iso : IsIso c := image_comparison_iso (HasImages.isImage h) hImgH c hc
    -- (image h).arr = c ≫ U_h.arr, c iso and U_h.arr iso ⟹ (image h).arr iso
    -- hc : c ≫ U_h.arr = (image h).arr, so U_h.arr = c_inv ≫ (image h).arr
    -- equivalently: (image h).arr = c ≫ U_h.arr... we use hc.symm to rewrite
    obtain ⟨c_inv, hcc_inv, hc_inv_c⟩ := hc_iso
    -- U_h.arr is iso: show by hUh_entire
    -- (image h).arr: we need IsIso ((image h).arr). From hc: c ≫ U_h.arr = (image h).arr.
    -- (image h).arr = c ≫ U_h.arr = c ≫ ... (since hc.symm gives (image h).arr = c ≫ U_h.arr)
    -- Actually use hc directly: (image h).arr = c ≫ U_h.arr by hc.symm as a calc step.
    rw [Subobject.IsEntire]
    show IsIso (image h).arr
    -- (image h).arr = c ≫ U_h.arr  since c_inv ≫ (image h).arr = c_inv ≫ c ≫ U_h.arr = U_h.arr
    -- and U_h monic gives (image h).arr = c ≫ U_h.arr
    have himgH_arr : (image h).arr = c ≫
        (HasSubobjectUnions.union
          (image (y ≫ HasBinaryCoproducts.inl))
          (image (HasBinaryCoproducts.inr (A := P) (B := P')))).arr :=
      hc.symm
    rw [himgH_arr]
    exact isIso_comp ⟨c_inv, hcc_inv, hc_inv_c⟩ hUh_entire
  -- e := h ≫ φ_inv : B+P' → Q  is a cover (cover ≫ iso).
  have he : Cover (h ≫ φ_inv) := cover_comp_iso h φ_inv hh ⟨φ, hφ_inv_φ, hφφ_inv⟩
  -- Projectivity of Q splits e: s' : Q → B+P', s' ≫ (h ≫ φ_inv) = id_Q.
  obtain ⟨s', hs'⟩ := hQ (h ≫ φ_inv) he
  -- Key identity: φ_inv ≫ s' ≫ h = id_{P+P'}.
  -- Proof: (φ_inv ≫ s' ≫ h) ≫ φ_inv = φ_inv ≫ (s' ≫ (h ≫ φ_inv)) = φ_inv ≫ id_Q = φ_inv
  --        = id_{P+P'} ≫ φ_inv, so φ_inv monic gives φ_inv ≫ s' ≫ h = id.
  have h_section : φ_inv ≫ s' ≫ h = Cat.id _ := by
    apply hφ_inv_mono _ _
    calc (φ_inv ≫ s' ≫ h) ≫ φ_inv
          = φ_inv ≫ s' ≫ (h ≫ φ_inv) := by simp [Cat.assoc]
        _ = φ_inv ≫ Cat.id Q      := by rw [hs']
        _ = φ_inv                  := Cat.comp_id _
        _ = Cat.id _ ≫ φ_inv      := (Cat.id_comp _).symm
  -- σ := inl_P ≫ φ_inv ≫ s' : P → B+P'. Then σ ≫ h = inl_P.
  let σ : P ⟶ HasBinaryCoproducts.coprod B P' :=
    HasBinaryCoproducts.inl ≫ φ_inv ≫ s'
  have hσh : σ ≫ h = HasBinaryCoproducts.inl := by
    simp only [σ, Cat.assoc, h_section, Cat.comp_id]
  -- σ factors through inl_B : the P'-summand σ#(inr_{P'}) is empty by coproduct disjointness,
  -- so σ#(inl_B) is the whole of P.  This is the §1.624 invImage-arithmetic, run on σ.
  let hPL : PreLogos 𝒞 := (DisjointBinaryCoproduct.toPositivePreLogos).toPreLogos
  let Inl_B := inlSub (𝒞 := 𝒞) (A := B) (B := P') inl_mono
  let Inr_P' := inrSub (𝒞 := 𝒞) (A := B) (B := P') inr_mono
  let P₁ : Subobject 𝒞 P := InverseImage σ Inl_B   -- σ#(inl_B)
  let P₂ : Subobject 𝒞 P := InverseImage σ Inr_P'  -- σ#(inr_{P'})
  let pb₁ := HasPullbacks.has σ Inl_B.arr   -- P₁.dom = pb₁.pt, P₁.arr = π₁, g₁ = π₂
  let pb₂ := HasPullbacks.has σ Inr_P'.arr  -- P₂.dom = pb₂.pt, P₂.arr = π₁
  let q₁ : P₁.dom ⟶ P := pb₁.cone.π₁
  let g₁ : P₁.dom ⟶ B := pb₁.cone.π₂
  have hsq₁ : q₁ ≫ σ = g₁ ≫ HasBinaryCoproducts.inl := pb₁.cone.w
  -- (1) P₂.dom is INITIAL: q₂ ≫ inl_P = g₂ ≫ inr_{P'} in P+P', killed by disjointness.
  let q₂ : P₂.dom ⟶ P := pb₂.cone.π₁
  let g₂ : P₂.dom ⟶ P' := pb₂.cone.π₂
  have hsq₂ : q₂ ≫ σ = g₂ ≫ HasBinaryCoproducts.inr := pb₂.cone.w
  -- q₂ ≫ inl_P = g₂ ≫ inr_{P'→P+P'}: compose the square with h and use σ≫h=inl, inr≫h=inr.
  have hdisj_elt : q₂ ≫ HasBinaryCoproducts.inl
      = g₂ ≫ HasBinaryCoproducts.inr := by
    have hr1 : (q₂ ≫ σ) ≫ h = q₂ ≫ HasBinaryCoproducts.inl := by
      rw [Cat.assoc, hσh]
    have hr2 : (g₂ ≫ HasBinaryCoproducts.inr) ≫ h = g₂ ≫ HasBinaryCoproducts.inr := by
      rw [Cat.assoc, HasBinaryCoproducts.case_inr]
    rw [← hr1, hsq₂, hr2]
  obtain ⟨e₂, he₂⟩ := coprod_inl_inr_disjoint_elt (𝒟 := 𝒞) (A := P) (B := P') q₂ g₂ hdisj_elt
  -- map P₂.dom → 0 ⟹ P₂.dom ≅ 0 ⟹ P₂.dom initial.
  let zeroObj := (minimal_subobject_of_one_is_coterminator hPL).zero
  obtain ⟨ζ, hζ⟩ := hPL.bottom_dom_iso (HasBinaryCoproducts.coprod P P') hPL.toHasTerminal.one
  have hP₂init : IsIso (e₂ ≫ ζ) := any_map_to_zero_is_iso hPL (e₂ ≫ ζ)
  obtain ⟨z₂inv, hz₂z₂inv, hz₂inv_z₂⟩ := hP₂init
  have hP₂uniq : ∀ {X : 𝒞} (u v : P₂.dom ⟶ X), u = v := by
    intro X u v
    have key : ∀ (w : P₂.dom ⟶ X), w = (e₂ ≫ ζ) ≫ (z₂inv ≫ w) := by
      intro w; rw [← Cat.assoc, hz₂z₂inv, Cat.id_comp]
    rw [key u, key v,
        (minimal_subobject_of_one_is_coterminator hPL).init_uniq (z₂inv ≫ u) (z₂inv ≫ v)]
  -- (2) P₂ ≤ bottom P.  Build any map P₂.dom → (bottom P).dom (via P₂.dom ≅ 0 ≅ (bottom P).dom);
  --     its triangle over (bottom P).arr holds because P₂.dom is initial (hP₂uniq).
  have hP₂_le_bot : P₂.le (PreLogos.bottom P) := by
    obtain ⟨ψ, _⟩ := hPL.bottom_dom_iso hPL.toHasTerminal.one P  -- ψ : 0 → (bottom P).dom
    refine ⟨(e₂ ≫ ζ) ≫ ψ, ?_⟩
    exact hP₂uniq _ _
  -- (3) P₂ ≤ P₁  (through bottom P), hence union P₁ P₂ collapses to P₁.
  have hP₂_le_P₁ : P₂.le P₁ := subLe_trans hP₂_le_bot (hPL.bottom_min P₁)
  -- (4) union P₁ P₂ ≤ P₁  and  entire P ≤ union P₁ P₂, so P₁ is ENTIRE.
  have hUnion_le_P₁ : (HasSubobjectUnions.union P₁ P₂).le P₁ :=
    HasSubobjectUnions.union_min P₁ P₂ P₁ ⟨Cat.id _, Cat.id_comp _⟩ hP₂_le_P₁
  have hEntireP_le_union : (Subobject.entire P).le (HasSubobjectUnions.union P₁ P₂) := by
    have ha : (Subobject.entire P).le
        (InverseImage σ (Subobject.entire (HasBinaryCoproducts.coprod B P'))) :=
      entire_le_invImage_entire σ
    have hbu : (Subobject.entire (HasBinaryCoproducts.coprod B P')).le
        (HasSubobjectUnions.union Inl_B Inr_P') :=
      inl_union_inr_entire (𝒟 := 𝒞) (A := B) (B := P')
    have hb : (InverseImage σ (Subobject.entire (HasBinaryCoproducts.coprod B P'))).le
        (InverseImage σ (HasSubobjectUnions.union Inl_B Inr_P')) :=
      invImage_mono_local σ hbu
    have hc : (InverseImage σ (HasSubobjectUnions.union Inl_B Inr_P')).le
        (HasSubobjectUnions.union (InverseImage σ Inl_B) (InverseImage σ Inr_P')) :=
      (PreLogos.invImage_preserves_union σ Inl_B Inr_P').1
    exact subLe_trans ha (subLe_trans hb hc)
  have hP₁_entire : P₁.IsEntire :=
    entire_of_entire_le (subLe_trans hEntireP_le_union hUnion_le_P₁)
  -- (5) q₁ = P₁.arr is iso; r := q₁⁻¹ ≫ g₁ : P → B  is the section.
  obtain ⟨q₁inv, hq₁q₁inv, hq₁inv_q₁⟩ := hP₁_entire   -- q₁ ≫ q₁inv = id, q₁inv ≫ q₁ = id
  -- q₁ = g₁ ≫ y   (push q₁≫σ=g₁≫inl through h, then inl_P monic).
  have hq₁_eq : q₁ = g₁ ≫ y := by
    apply (inl_mono (A := P) (B := P'))
    calc q₁ ≫ HasBinaryCoproducts.inl
        = (q₁ ≫ σ) ≫ h := by rw [Cat.assoc, hσh]
      _ = (g₁ ≫ HasBinaryCoproducts.inl) ≫ h := by rw [hsq₁]
      _ = g₁ ≫ (HasBinaryCoproducts.inl ≫ h) := Cat.assoc _ _ _
      _ = g₁ ≫ (y ≫ HasBinaryCoproducts.inl) := by rw [h_inl]
      _ = (g₁ ≫ y) ≫ HasBinaryCoproducts.inl := (Cat.assoc _ _ _).symm
  refine ⟨q₁inv ≫ g₁, ?_⟩
  -- (q₁inv ≫ g₁) ≫ y = q₁inv ≫ (g₁ ≫ y) = q₁inv ≫ q₁ = id_P.
  calc (q₁inv ≫ g₁) ≫ y = q₁inv ≫ (g₁ ≫ y) := Cat.assoc _ _ _
    _ = q₁inv ≫ q₁ := by rw [← hq₁_eq]
    _ = Cat.id P := hq₁inv_q₁

/-! ## §1.633 infrastructure: complemented decomposition `A ≅ U.dom + U₂.dom`

  A complemented subobject pair `(U, U₂)` of `A` (`U ∩ U₂ ≤ ⊥`, `entire ≤ U ∪ U₂`) realises
  `A` as the coproduct of the two domains.  This is the §1.62 pasting lemma run on the
  disjoint, jointly-covering pair: their intersection apex is *initial* (its domain sits
  below `⊥`, whose domain is the coterminator `0`), so the pushout of the intersection is the
  coproduct (`pushout_over_initial_is_coproduct`), and the union being entire identifies the
  pushout apex with `A`.  This packages the kernel already used inside `decompose_via_coproduct`. -/

/-- A subobject below `⊥` has an **initial** domain: any two maps out of it agree.  `S ≤ ⊥`
    gives `S.dom → ⊥.dom`, and `⊥.dom ≅ 0` is the coterminator, so `S.dom ≅ 0` is initial. -/
theorem dom_initial_of_le_bottom {A : 𝒞} {S : Subobject 𝒞 A}
    (h : S.le (PreLogos.bottom A)) : ∀ {X : 𝒞} (u v : S.dom ⟶ X), u = v := by
  letI hPL : PreLogos 𝒞 := ‹PreLogos 𝒞›
  obtain ⟨g, _⟩ := h                                   -- g : S.dom → (⊥ A).dom
  obtain ⟨ζ, hζ⟩ := hPL.bottom_dom_iso A hPL.toHasTerminal.one  -- ζ : (⊥ A).dom → 0
  have hiso : IsIso (g ≫ ζ) := any_map_to_zero_is_iso hPL (g ≫ ζ)
  obtain ⟨zinv, hz, hzinv⟩ := hiso
  intro X u v
  have key : ∀ (w : S.dom ⟶ X), w = (g ≫ ζ) ≫ (zinv ≫ w) := by
    intro w; rw [← Cat.assoc, hz, Cat.id_comp]
  rw [key u, key v,
      (minimal_subobject_of_one_is_coterminator hPL).init_uniq (zinv ≫ u) (zinv ≫ v)]

/-- An object that admits ANY map into a bottom domain `(⊥ Z).dom` is **initial**: any two
    maps out of it agree.  Generalises `dom_initial_of_le_bottom` (which assumes the map lands
    in `(⊥ A).dom` for the *same* ambient `A`); since all bottoms are cross-base isomorphic
    (`bottom_dom_iso`), a map to any `(⊥ Z).dom` suffices.  Used to collapse the complement
    `A''` once it is shown to map into a disjoint two-point object. -/
theorem dom_initial_of_map_to_bottom {X Z : 𝒞} (g : X ⟶ (PreLogos.bottom Z).dom) :
    ∀ {Y : 𝒞} (u v : X ⟶ Y), u = v := by
  letI hPL : PreLogos 𝒞 := ‹PreLogos 𝒞›
  obtain ⟨ζ, hζ⟩ := hPL.bottom_dom_iso Z hPL.toHasTerminal.one  -- ζ : (⊥ Z).dom → 0
  have hiso : IsIso (g ≫ ζ) := any_map_to_zero_is_iso hPL (g ≫ ζ)
  obtain ⟨zinv, hz, _hzinv⟩ := hiso
  intro Y u v
  have key : ∀ (w : X ⟶ Y), w = (g ≫ ζ) ≫ (zinv ≫ w) := by
    intro w; rw [← Cat.assoc, hz, Cat.id_comp]
  rw [key u, key v,
      (minimal_subobject_of_one_is_coterminator hPL).init_uniq (zinv ≫ u) (zinv ≫ v)]

/-- §1.62/§1.631: a complemented pair `(U, U₂)` of `A` realises `A` as the coproduct of the
    two subobject domains.  Hypotheses are exactly the two clauses of `IsComplementedSub`. -/
theorem complementedSub_iso_coproduct [HasBinaryCoproducts 𝒞] {A : 𝒞}
    (U U₂ : Subobject 𝒞 A)
    (hdisj : Subobject.le (Subobject.inter U U₂) (PreLogos.bottom A))
    (hentire : Subobject.le (Subobject.entire A) (HasSubobjectUnions.union U U₂)) :
    Isomorphic A (HasBinaryCoproducts.coprod U.dom U₂.dom) := by
  -- The intersection apex is the domain of `Subobject.inter U U₂`, which is initial.
  have hCinit : ∀ {X : 𝒞} (u v : (HasPullbacks.has U.arr U₂.arr).cone.pt ⟶ X), u = v :=
    dom_initial_of_le_bottom (S := Subobject.inter U U₂) hdisj
  let po := pasting_lemma U U₂
  have hpoiso : Isomorphic po.cocone.pt (HasBinaryCoproducts.coprod U.dom U₂.dom) :=
    pushout_over_initial_is_coproduct po (@hCinit)
  -- po.cocone.pt = (U ∪ U₂).dom, entire since `entire A ≤ U ∪ U₂`.
  have hUnion_entire : (HasSubobjectUnions.union U U₂).IsEntire :=
    entire_of_entire_le hentire
  have hA_union : Isomorphic A (HasSubobjectUnions.union U U₂).dom := by
    obtain ⟨arrinv, h1, h2⟩ := hUnion_entire
    exact ⟨arrinv, (HasSubobjectUnions.union U U₂).arr, h2, h1⟩
  exact isomorphic_trans hA_union hpoiso

/-- §1.62/§1.631, **leg-exposing** form of `complementedSub_iso_coproduct`: a complemented
    pair `(U, U₂)` of `A` realises `A` as `U.dom + U₂.dom` with an iso `ψ` whose legs match
    the subobject inclusions (`inl ≫ ψ = U.arr`, `inr ≫ ψ = U₂.arr`), together with a
    two-sided inverse.  Same pasting-lemma kernel as `complementedSub_iso_coproduct`, but the
    explicit copairing comparison is needed so a `case s₁ s₂` post-composed with `ψ⁻¹`
    restricts each section to its half of `A`.  Lives here (not the §1.662 Diaconescu section
    of `S1_64`) so it resolves over the CANONICAL topos `PreLogos`/`HasSubobjectUnions`
    instances — avoiding the `PreToposDisjoint` instance diamond. -/
theorem complementedSub_legs_iso [HasBinaryCoproducts 𝒞] {A : 𝒞} (U U₂ : Subobject 𝒞 A)
    (hdisj : Subobject.le (Subobject.inter U U₂) (PreLogos.bottom A))
    (hentire : Subobject.le (Subobject.entire A) (HasSubobjectUnions.union U U₂)) :
    ∃ (ψ : HasBinaryCoproducts.coprod U.dom U₂.dom ⟶ A)
      (ψinv : A ⟶ HasBinaryCoproducts.coprod U.dom U₂.dom),
      ψ ≫ ψinv = Cat.id _ ∧ ψinv ≫ ψ = Cat.id _ ∧
      HasBinaryCoproducts.inl ≫ ψ = U.arr ∧ HasBinaryCoproducts.inr ≫ ψ = U₂.arr := by
  classical
  have hCinit : ∀ {X : 𝒞} (u v : (HasPullbacks.has U.arr U₂.arr).cone.pt ⟶ X), u = v :=
    dom_initial_of_le_bottom (S := Subobject.inter U U₂) hdisj
  let po := pasting_lemma U U₂
  let Un := HasSubobjectUnions.union U U₂
  have hx : po.cocone.ι₁ ≫ Un.arr = U.arr := (HasSubobjectUnions.union_left U U₂).choose_spec
  have hy : po.cocone.ι₂ ≫ Un.arr = U₂.arr := (HasSubobjectUnions.union_right U U₂).choose_spec
  let coCoc : PushoutCocone (HasPullbacks.has U.arr U₂.arr).cone.π₁
      (HasPullbacks.has U.arr U₂.arr).cone.π₂ :=
    ⟨HasBinaryCoproducts.coprod U.dom U₂.dom, HasBinaryCoproducts.inl, HasBinaryCoproducts.inr,
     hCinit _ _⟩
  let φ : po.cocone.pt ⟶ HasBinaryCoproducts.coprod U.dom U₂.dom := po.desc coCoc
  have hφ₁ : po.cocone.ι₁ ≫ φ = HasBinaryCoproducts.inl := po.fac₁ coCoc
  have hφ₂ : po.cocone.ι₂ ≫ φ = HasBinaryCoproducts.inr := po.fac₂ coCoc
  let χ : HasBinaryCoproducts.coprod U.dom U₂.dom ⟶ po.cocone.pt :=
    HasBinaryCoproducts.case po.cocone.ι₁ po.cocone.ι₂
  have hχ₁ : HasBinaryCoproducts.inl ≫ χ = po.cocone.ι₁ := HasBinaryCoproducts.case_inl _ _
  have hχ₂ : HasBinaryCoproducts.inr ≫ χ = po.cocone.ι₂ := HasBinaryCoproducts.case_inr _ _
  have hφχ : φ ≫ χ = Cat.id _ := by
    have h1 : po.cocone.ι₁ ≫ (φ ≫ χ) = po.cocone.ι₁ := by rw [← Cat.assoc, hφ₁, hχ₁]
    have h2 : po.cocone.ι₂ ≫ (φ ≫ χ) = po.cocone.ι₂ := by rw [← Cat.assoc, hφ₂, hχ₂]
    rw [po.uniq po.cocone (φ ≫ χ) h1 h2,
        po.uniq po.cocone (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)]
  have hχφ : χ ≫ φ = Cat.id _ := by
    have h1 : HasBinaryCoproducts.inl ≫ (χ ≫ φ) = HasBinaryCoproducts.inl := by
      rw [← Cat.assoc, hχ₁, hφ₁]
    have h2 : HasBinaryCoproducts.inr ≫ (χ ≫ φ) = HasBinaryCoproducts.inr := by
      rw [← Cat.assoc, hχ₂, hφ₂]
    rw [HasBinaryCoproducts.case_uniq _ _ (χ ≫ φ) h1 h2,
        HasBinaryCoproducts.case_uniq _ _ (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)]
  obtain ⟨arrinv, h1, h2⟩ := entire_of_entire_le hentire
  refine ⟨χ ≫ Un.arr, arrinv ≫ φ, ?_, ?_, ?_, ?_⟩
  · have e1 : (χ ≫ Un.arr) ≫ (arrinv ≫ φ) = χ ≫ ((Un.arr ≫ arrinv) ≫ φ) := by
      simp only [Cat.assoc]
    rw [e1, h1, show (Cat.id Un.dom ≫ φ) = φ from Cat.id_comp φ]; exact hχφ
  · have e2 : (arrinv ≫ φ) ≫ (χ ≫ Un.arr) = arrinv ≫ ((φ ≫ χ) ≫ Un.arr) := by
      simp only [Cat.assoc]
    rw [e2, hφχ, show (Cat.id po.cocone.pt ≫ Un.arr) = Un.arr from Cat.id_comp Un.arr]
    exact h2
  · calc HasBinaryCoproducts.inl ≫ (χ ≫ Un.arr)
        = (HasBinaryCoproducts.inl ≫ χ) ≫ Un.arr := (Cat.assoc _ _ _).symm
      _ = po.cocone.ι₁ ≫ Un.arr := by rw [hχ₁]
      _ = U.arr := hx
  · calc HasBinaryCoproducts.inr ≫ (χ ≫ Un.arr)
        = (HasBinaryCoproducts.inr ≫ χ) ≫ Un.arr := (Cat.assoc _ _ _).symm
      _ = po.cocone.ι₂ ≫ Un.arr := by rw [hχ₂]
      _ = U₂.arr := hy

/-- Intersection of subobjects is symmetric up to `≤`: swapping the pullback legs gives
    `inter S T ≤ inter T S`.  Both intersections are pullbacks of the same cospan in the two
    orders; the comparison map is the canonical lift swapping `π₁` and `π₂`. -/
theorem inter_comm_le [HasPullbacks 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B) :
    Subobject.le (Subobject.inter S T) (Subobject.inter T S) := by
  let pbST := HasPullbacks.has S.arr T.arr
  let pbTS := HasPullbacks.has T.arr S.arr
  -- swap legs of pbST's cone to form a cone over (T.arr, S.arr).
  let c : Cone T.arr S.arr := ⟨pbST.cone.pt, pbST.cone.π₂, pbST.cone.π₁, pbST.cone.w.symm⟩
  refine ⟨pbTS.lift c, ?_⟩
  -- (inter T S).arr = pbTS.π₁ ≫ T.arr;  lift ≫ pbTS.π₁ = c.π₁ = pbST.π₂.
  show pbTS.lift c ≫ (pbTS.cone.π₁ ≫ T.arr) = pbST.cone.π₁ ≫ S.arr
  rw [← Cat.assoc, pbTS.lift_fst c]
  show pbST.cone.π₂ ≫ T.arr = pbST.cone.π₁ ≫ S.arr
  exact pbST.cone.w.symm

/-- Union of subobjects is symmetric up to `≤`: `union S T ≤ union T S` by minimality. -/
theorem union_comm_le {B : 𝒞} (S T : Subobject 𝒞 B) :
    Subobject.le (HasSubobjectUnions.union S T) (HasSubobjectUnions.union T S) :=
  HasSubobjectUnions.union_min S T _
    (HasSubobjectUnions.union_right T S) (HasSubobjectUnions.union_left T S)

/-- Being a complemented subobject is symmetric: if `U` is complemented with complement `U₂`,
    then `U₂` is complemented with complement `U`.  `inter`/`union` are commutative up to `≤`. -/
theorem complementedSub_symm [HasBinaryCoproducts 𝒞] {A : 𝒞} {U U₂ : Subobject 𝒞 A}
    (hdisj : Subobject.le (Subobject.inter U U₂) (PreLogos.bottom A))
    (hentire : Subobject.le (Subobject.entire A) (HasSubobjectUnions.union U U₂)) :
    IsComplementedSub U₂ :=
  ⟨U, subLe_trans (inter_comm_le U₂ U) hdisj, subLe_trans hentire (union_comm_le U U₂)⟩

/-! ## §1.633 Characterization of capital positive pre-logoi

  A positive pre-logos is capital iff its complemented subterminators
  (complemented subobjects of 1) are projective and form a basis. -/

/-- §1.633 (⟹), first clause: in a capital positive pre-logos every complemented
    subterminator is projective.  `1` is projective (§1.525, `capital_one_projective`); a
    complemented subterminator `U ↣ 1` makes `1 ≅ U.dom + U₂.dom`
    (`complementedSub_iso_coproduct`), so `U.dom` is a complemented subobject of the
    projective `1`, hence projective by §1.631 (`complemented_of_projective_is_projective`).

    Needs `[DisjointBinaryCoproduct 𝒞]` (the faithful rendering of positivity used by §1.631);
    `omit [PreLogos 𝒞]` removes the instance diamond with `DisjointBinaryCoproduct.toPreLogos`. -/
theorem complemented_subterminator_projective [DisjointBinaryCoproduct 𝒞]
    (hcap : Capital (𝒞 := 𝒞)) (U : Subobject 𝒞 one) (hU : IsComplementedSub U) :
    Projective U.dom := by
  obtain ⟨U₂, hdisj, hentire⟩ := hU
  -- 1 ≅ U.dom + U₂.dom.
  have hiso : Isomorphic (one : 𝒞) (HasBinaryCoproducts.coprod U.dom U₂.dom) :=
    complementedSub_iso_coproduct U U₂ hdisj hentire
  -- 1 is projective.
  have hone : Projective (one : 𝒞) := by
    intro B e he; exact capital_one_projective hcap he
  intro B y hy
  exact complemented_of_projective_is_projective hone U₂.dom hiso y hy

/-! ### §1.633 `A+1` infrastructure: the basis argument's coproduct scaffolding

  Freyd's basis argument runs the well-pointedness of `A+1`.  We package the shared
  facts: a section makes a map a cover, so `A+1` is well-supported (`inr : 1 → A+1` is a
  section of `term`), and the coproduct map `A'+1 ↣ A+1` of a proper `A'↣A` stays a proper
  mono.  These three lemmas feed both the forward basis clause and the converse. -/

/-- A map with a section is a cover: if `s ≫ f = id` then every monic `f` factors through
    is split (by `s ≫ g`) and hence iso. -/
private theorem cover_of_section {X Y : 𝒞} (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = Cat.id Y) :
    Cover f := by
  intro C m g hm hgm
  have hsplit : (s ≫ g) ≫ m = Cat.id Y := by rw [Cat.assoc, hgm, hs]
  refine ⟨s ≫ g, ?_, hsplit⟩
  -- `m ≫ (s≫g) = id`: post-compose with the mono `m`, both sides give `m`.
  exact hm _ _ (by rw [Cat.assoc, hsplit, Cat.id_comp, Cat.comp_id])

/-- `A + 1` is well-supported: `inr : 1 → A+1` is a section of `term (A+1)`
    (both `inr ≫ term` and `id` are maps `1 → 1`, so they agree by `term_uniq`). -/
theorem wellSupported_coprod_one [DisjointBinaryCoproduct 𝒞] (A : 𝒞) :
    WellSupported (HasBinaryCoproducts.coprod A one) :=
  cover_of_section (term _) HasBinaryCoproducts.inr (term_uniq _ _)

section IsoCoprodComplemented
-- own section without the file-level `[PreLogos 𝒞]`, so the sole `PreLogos` is the one
-- `DisjointBinaryCoproduct` provides — the disjoint-coproduct lemmas and the
-- `InverseImage`/`inter`/`union`/`bottom` in the statement then share a single instance.
variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- For **any** point `φ : 1 → B₁ + B₂` (no iso needed), the `inl`-inverse-image `U := φ#(inlSub)`
    is a COMPLEMENTED subterminator of `1` (complement `U₂ := φ#(inrSub)`), and the two pullback legs
    `f₁ : U.dom → B₁`, `f₂ : U₂.dom → B₂` satisfy `U.arr ≫ φ = f₁ ≫ inl` and `U₂.arr ≫ φ = f₂ ≫ inr`,
    with `U ∪ U₂` entire.  Disjointness/cover come from the disjoint-coproduct facts
    (`inl_inter_inr_le_bottom`, `inl_union_inr_entire`) pulled back along `φ`; the `inl∩inr`-summand
    collapses to `⊥` because its domain is initial (its two legs are equalized in `B₁+B₂`).

    This packages a point's `inl`/`inr` split as a complemented-subterminator pair with the leg data
    the §1.633 basis argument needs — the `inl`-leg is the witness map, the cover lets a missing point
    of `image (coprodMapOne m)` be reconstructed from its two parts. -/
theorem point_inl_complementedSubterminator [DisjointBinaryCoproduct 𝒞] {B₁ B₂ : 𝒞}
    (φ : one ⟶ HasBinaryCoproducts.coprod B₁ B₂) :
    ∃ (U U₂ : Subobject 𝒞 one) (f₁ : U.dom ⟶ B₁) (f₂ : U₂.dom ⟶ B₂),
      IsComplementedSub U ∧ (Subobject.entire one).le (HasSubobjectUnions.union U U₂) ∧
      U.arr ≫ φ = f₁ ≫ HasBinaryCoproducts.inl ∧
      U₂.arr ≫ φ = f₂ ≫ HasBinaryCoproducts.inr := by
  -- abbreviations: the two coproduct subobjects of B₁+B₂.
  let Inl := inlSub (𝒞 := 𝒞) (A := B₁) (B := B₂) inl_mono
  let Inr := inrSub (𝒞 := 𝒞) (A := B₁) (B := B₂) inr_mono
  let U  : Subobject 𝒞 one := InverseImage φ Inl
  let U₂ : Subobject 𝒞 one := InverseImage φ Inr
  -- the pullback legs: π₂ of `φ#Inl` is f₁ : U.dom → B₁, of `φ#Inr` is f₂ : U₂.dom → B₂.
  let pbU := HasPullbacks.has φ Inl.arr
  let pbR0 := HasPullbacks.has φ Inr.arr
  -- the two relations are the pullback squares for `φ#Inl`, `φ#Inr`.
  have hrel₁ : U.arr ≫ φ = pbU.cone.π₂ ≫ HasBinaryCoproducts.inl := pbU.cone.w
  have hrel₂ : U₂.arr ≫ φ = pbR0.cone.π₂ ≫ HasBinaryCoproducts.inr := pbR0.cone.w
  -- DISJOINTNESS `inter U U₂ ≤ ⊥(1)`: its domain (pullback of U.arr,U₂.arr) is initial — the two
  -- legs into B₁,B₂ are equalized in B₁+B₂, so disjointness maps it to `⊥(B₁+B₂).dom`, then to `0`.
  have hdisj : (Subobject.inter U U₂).le (PreLogos.bottom one) := by
    let pbI := HasPullbacks.has U.arr U₂.arr
    have hsq : (pbI.cone.π₁ ≫ pbU.cone.π₂) ≫ Inl.arr
             = (pbI.cone.π₂ ≫ pbR0.cone.π₂) ≫ Inr.arr := by
      calc (pbI.cone.π₁ ≫ pbU.cone.π₂) ≫ Inl.arr
          = pbI.cone.π₁ ≫ (pbU.cone.π₂ ≫ Inl.arr) := Cat.assoc _ _ _
        _ = pbI.cone.π₁ ≫ (pbU.cone.π₁ ≫ φ) := by rw [pbU.cone.w]
        _ = (pbI.cone.π₁ ≫ pbU.cone.π₁) ≫ φ := (Cat.assoc _ _ _).symm
        _ = (pbI.cone.π₁ ≫ U.arr) ≫ φ := rfl
        _ = (pbI.cone.π₂ ≫ U₂.arr) ≫ φ := by rw [pbI.cone.w]
        _ = (pbI.cone.π₂ ≫ pbR0.cone.π₁) ≫ φ := rfl
        _ = pbI.cone.π₂ ≫ (pbR0.cone.π₁ ≫ φ) := Cat.assoc _ _ _
        _ = pbI.cone.π₂ ≫ (pbR0.cone.π₂ ≫ Inr.arr) := by rw [pbR0.cone.w]
        _ = (pbI.cone.π₂ ≫ pbR0.cone.π₂) ≫ Inr.arr := (Cat.assoc _ _ _).symm
    have hsq' : (pbI.cone.π₁ ≫ pbU.cone.π₂) ≫ HasBinaryCoproducts.inl
              = (pbI.cone.π₂ ≫ pbR0.cone.π₂) ≫ HasBinaryCoproducts.inr := hsq
    obtain ⟨e, _⟩ := coprod_inl_inr_disjoint_elt (𝒟 := 𝒞) (A := B₁) (B := B₂)
      (pbI.cone.π₁ ≫ pbU.cone.π₂) (pbI.cone.π₂ ≫ pbR0.cone.π₂) hsq'
    let hDPL : PreLogos 𝒞 := DisjointBinaryCoproduct.toPositivePreLogos.toPreLogos
    obtain ⟨ζ, _⟩ := hDPL.bottom_dom_iso (HasBinaryCoproducts.coprod B₁ B₂) hDPL.toHasTerminal.one
    have hiso := any_map_to_zero_is_iso hDPL ((e ≫ ζ))
    obtain ⟨zinv, hz, _⟩ := hiso
    have hinit : ∀ {X : 𝒞} (u v : pbI.cone.pt ⟶ X), u = v := by
      intro X u v
      have key : ∀ (r : pbI.cone.pt ⟶ X), r = (e ≫ ζ) ≫ (zinv ≫ r) := by
        intro r; rw [← Cat.assoc, hz, Cat.id_comp]
      rw [key u, key v,
          (minimal_subobject_of_one_is_coterminator hDPL).init_uniq (zinv ≫ u) (zinv ≫ v)]
    exact ⟨(e ≫ ζ) ≫ (minimal_subobject_of_one_is_coterminator hDPL).init _, hinit (X := one) _ _⟩
  -- COVER `entire 1 ≤ U ∪ U₂`:  entire 1 ≤ φ#(entire) ≤ φ#(Inl∪Inr) ≤ φ#Inl ∪ φ#Inr = U ∪ U₂.
  have hcover : (Subobject.entire one).le (HasSubobjectUnions.union U U₂) := by
    have ha := entire_le_invImage_entire (B := HasBinaryCoproducts.coprod B₁ B₂) φ
    have hbu : (Subobject.entire (HasBinaryCoproducts.coprod B₁ B₂)).le
        (HasSubobjectUnions.union (inlSub (𝒞 := 𝒞) (A := B₁) (B := B₂) inl_mono)
          (inrSub (𝒞 := 𝒞) (A := B₁) (B := B₂) inr_mono)) :=
      inl_union_inr_entire (𝒟 := 𝒞) (A := B₁) (B := B₂)
    have hb := invImage_mono_local φ hbu
    have hc := (PreLogos.invImage_preserves_union φ
      (inlSub (𝒞 := 𝒞) (A := B₁) (B := B₂) inl_mono)
      (inrSub (𝒞 := 𝒞) (A := B₁) (B := B₂) inr_mono)).1
    exact subLe_trans ha (subLe_trans hb hc)
  have hcomp : IsComplementedSub U := ⟨U₂, hdisj, hcover⟩
  exact ⟨U, U₂, pbU.cone.π₂, pbR0.cone.π₂, hcomp, hcover, hrel₁, hrel₂⟩

/-- The coproduct map `A'+1 → A+1` of a mono `m : A' → A` is `case (m ≫ inl) inr`.
    It is monic: a parallel pair agreeing after it agrees after the two injections
    (the left half cancels `m`'s monicity, the right is `inr` monic), and the disjointness
    of `inl`/`inr` images forces the two cases to match up.  We use the explicit copairing. -/
def coprodMapOne [DisjointBinaryCoproduct 𝒞] {A' A : 𝒞} (m : A' ⟶ A) :
    HasBinaryCoproducts.coprod A' one ⟶ HasBinaryCoproducts.coprod A one :=
  HasBinaryCoproducts.case (m ≫ HasBinaryCoproducts.inl) HasBinaryCoproducts.inr

variable [DisjointBinaryCoproduct 𝒞]

/-- The post-composition subobject `T ≫ i` of a subobject `T ↣ A` along a mono `i : A ↣ B`. -/
def postcompSub {A B : 𝒞} (T : Subobject 𝒞 A) {i : A ⟶ B} (hi : Monic i) : Subobject 𝒞 B :=
  ⟨T.dom, T.arr ≫ i, by
    intro W u v huv
    refine T.monic _ _ (hi _ _ ?_)
    rw [Cat.assoc, Cat.assoc]; exact huv⟩

/-- Pulling a post-composed subobject back along the SAME mono recovers (at most) the original:
    `i⁻¹(T ≫ i) ≤ T` for `i` monic.  The pullback's `π₂` leg is the witness: `π₁ ≫ i = π₂ ≫ (T.arr ≫ i)`
    and `i` monic gives `π₁ = π₂ ≫ T.arr`, exactly `(i⁻¹(T≫i)).arr = π₂ ≫ T.arr`. -/
theorem invImage_postcompSub_le {A B : 𝒞} (T : Subobject 𝒞 A) {i : A ⟶ B} (hi : Monic i) :
    (InverseImage i (postcompSub T hi)).le T := by
  let pb := HasPullbacks.has i (postcompSub T hi).arr
  refine ⟨pb.cone.π₂, ?_⟩
  -- π₂ ≫ T.arr = π₁ = (InverseImage i (T≫i)).arr, from `π₁ ≫ i = π₂ ≫ (T.arr ≫ i)` and `i` monic.
  apply hi
  show (pb.cone.π₂ ≫ T.arr) ≫ i = pb.cone.π₁ ≫ i
  calc (pb.cone.π₂ ≫ T.arr) ≫ i = pb.cone.π₂ ≫ (T.arr ≫ i) := Cat.assoc _ _ _
    _ = pb.cone.π₂ ≫ (postcompSub T hi).arr := rfl
    _ = pb.cone.π₁ ≫ i := (pb.cone.w).symm

/-- §1.621 in pulled-back form: `inl⁻¹(inrSub) ≤ T` for **any** subobject `T` of `A`.  The pullback
    of `inr` along `inl` has the two legs `(π₁, π₂)` equalized in `A+B`; disjointness
    (`coprod_inl_inr_disjoint_elt`) makes its domain map to `⊥(A+B)` (DBC instance), so the domain is
    INITIAL — a Prop independent of which `PreLogos` instance built the pullback.  An initial-domain
    subobject is `≤` everything (map via the **ambient** coterminator `0 → T.dom`, triangle by
    `init_uniq`).  Stated against arbitrary `T` to keep `⊥` out of the type.  The pullback (`pb`) and
    the `init` map both use the ambient `[PreLogos 𝒞]`, matching the `InverseImage` in the goal. -/
theorem invImage_inl_inrSub_le_any {A B : 𝒞} (T : Subobject 𝒞 A) :
    (InverseImage (HasBinaryCoproducts.inl (A := A) (B := B))
        (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono)).le T := by
  -- ambient pullback (matches the goal's `InverseImage`).
  let pb := HasPullbacks.has (HasBinaryCoproducts.inl (A := A) (B := B))
                             (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono).arr
  have hcomm : pb.cone.π₁ ≫ HasBinaryCoproducts.inl
             = pb.cone.π₂ ≫ HasBinaryCoproducts.inr := pb.cone.w
  -- DBC disjointness sends `pb.cone.pt` into `⊥(A+B)` (DBC instance), hence to the DBC coterminator;
  -- that proves INITIALITY of `pb.cone.pt`, a Prop the instance choice does not affect.
  let hDPL : PreLogos 𝒞 := DisjointBinaryCoproduct.toPositivePreLogos.toPreLogos
  obtain ⟨e, _⟩ := coprod_inl_inr_disjoint_elt (𝒟 := 𝒞) (A := A) (B := B) pb.cone.π₁ pb.cone.π₂ hcomm
  obtain ⟨ζ, _⟩ := hDPL.bottom_dom_iso (HasBinaryCoproducts.coprod A B) hDPL.toHasTerminal.one
  have hiso : IsIso (e ≫ ζ) := any_map_to_zero_is_iso hDPL (e ≫ ζ)
  obtain ⟨zinv, hz, _⟩ := hiso
  have hinit : ∀ {X : 𝒞} (u v : pb.cone.pt ⟶ X), u = v := by
    intro X u v
    have key : ∀ (w : pb.cone.pt ⟶ X), w = (e ≫ ζ) ≫ (zinv ≫ w) := by
      intro w; rw [← Cat.assoc, hz, Cat.id_comp]
    rw [key u, key v,
        (minimal_subobject_of_one_is_coterminator hDPL).init_uniq (zinv ≫ u) (zinv ≫ v)]
  -- witness: any map `pb.cone.pt → T.dom`; use the AMBIENT coterminator's `init`, then transport
  -- `pb.cone.pt` there (it is initial).  The triangle holds by `hinit`.
  obtain ⟨ψ, _⟩ := hDPL.bottom_dom_iso (HasBinaryCoproducts.coprod A B) hDPL.toHasTerminal.one
  exact ⟨(e ≫ ζ) ≫ (minimal_subobject_of_one_is_coterminator hDPL).init T.dom, hinit _ _⟩

/-- §1.633 core: for a mono `m : A' ↣ A` that is NOT iso, the image of the coproduct map
    `coprodMapOne m : A'+1 ↣ A+1` is a PROPER subobject of `A+1` — it is not entire.

    Extensivity-free proof: by §1.615 (`union_via_coproduct_image`) the image of `case (m≫inl) inr`
    is `union (image (m≫inl)) (image inr)`.  Pull that union back along `inl : A → A+1`:
    `inl⁻¹` preserves `entire`, `union`, and (by disjointness) sends the `inr`-summand to `≤ ⊥`.
    The `image (m≫inl)` summand pulls back `≤ image m` (`invImage_postcompSub_le`, image-min).  So if the
    union were entire, `image m` would be entire — i.e. `m` a cover — and a monic cover is iso. -/
theorem coprodMapOne_image_proper {A' A : 𝒞} (m : A' ⟶ A)
    (hm : Monic m) (hmiso : ¬ IsIso m) : ¬ (image (coprodMapOne m)).IsEntire := by
  intro hEntire
  apply hmiso
  -- `m` is iso: it is a monic cover, since `image m` is entire.
  refine monic_cover_iso m ((cover_iff_image_entire m).2 ?_) hm
  -- Goal: `(image m).IsEntire`.  Show `entire A ≤ image m`.
  apply entire_of_entire_le
  -- The image of `coprodMapOne m = case (m≫inl) inr` is `union (image (m≫inl)) (image inr)`.
  let J := image (m ≫ HasBinaryCoproducts.inl (A := A) (B := one))
  let Kr := image (HasBinaryCoproducts.inr (A := A) (B := one))
  have hUimg : IsImage (coprodMapOne m) (HasSubobjectUnions.union J Kr) :=
    union_via_coproduct_image (m ≫ HasBinaryCoproducts.inl (A := A) (B := one))
      (HasBinaryCoproducts.inr (A := A) (B := one))
  -- `union J Kr` is entire (it is isomorphic to the entire `image (coprodMapOne m)`).
  have hUnion_entire : (HasSubobjectUnions.union J Kr).IsEntire := by
    -- `union J Kr` is an image of `coprodMapOne m`, so `image (coprodMapOne m) ≤ union J Kr`; and
    -- `image (coprodMapOne m)` is entire (`entire ≤ image`), so `entire ≤ union J Kr` ⟹ entire.
    apply entire_of_entire_le
    have him_le : (image (coprodMapOne m)).le (HasSubobjectUnions.union J Kr) :=
      image_min (coprodMapOne m) _ hUimg.1
    obtain ⟨inv, hinv1, hinv2⟩ := hEntire        -- (image …).arr is iso
    refine subLe_trans (Y := image (coprodMapOne m)) ?_ him_le
    -- entire (A+1) ≤ image..  via the inverse `inv` of (image..).arr.
    exact ⟨inv, hinv2⟩
  -- The `inl⁻¹` lattice-hom chain: entire A ≤ inl⁻¹(entire) ≤ inl⁻¹(union J Kr)
  --   ≤ union (inl⁻¹ J) (inl⁻¹ Kr) ≤ image m.
  let il : A ⟶ HasBinaryCoproducts.coprod A one := HasBinaryCoproducts.inl
  -- entire A ≤ inl⁻¹(entire (A+1))
  have ha : (Subobject.entire A).le (InverseImage il (Subobject.entire _)) :=
    entire_le_invImage_entire il
  -- union J Kr is entire ⟹ entire (A+1) ≤ union J Kr
  have hbu : (Subobject.entire (HasBinaryCoproducts.coprod A one)).le (HasSubobjectUnions.union J Kr) := by
    obtain ⟨inv, hinv1, hinv2⟩ := hUnion_entire
    exact ⟨inv, hinv2⟩
  have hb : (InverseImage il (Subobject.entire _)).le (InverseImage il (HasSubobjectUnions.union J Kr)) :=
    invImage_mono_local il hbu
  have hc : (InverseImage il (HasSubobjectUnions.union J Kr)).le
      (HasSubobjectUnions.union (InverseImage il J) (InverseImage il Kr)) :=
    (PreLogos.invImage_preserves_union il J Kr).1
  -- inl⁻¹ J ≤ image m :  J ≤ postcompSub (image m) inl  (image-min), then invImage_postcompSub_le.
  have hJ_le : J.le (postcompSub (image m) inl_mono) := by
    refine image_min (m ≫ HasBinaryCoproducts.inl) _ ⟨image.lift m, ?_⟩
    show image.lift m ≫ ((image m).arr ≫ HasBinaryCoproducts.inl) = m ≫ HasBinaryCoproducts.inl
    rw [← Cat.assoc, image.lift_fac]
  have hJl : (InverseImage il J).le (image m) :=
    subLe_trans (invImage_mono_local il hJ_le) (invImage_postcompSub_le (image m) inl_mono)
  -- inl⁻¹ Kr ≤ bottom A ≤ image m :  Kr = image inr ≤ inrSub, so inl⁻¹ Kr ≤ inl⁻¹ inrSub = inl ∩ inr ≤ ⊥.
  have hKr_le : Kr.le (inrSub (𝒞 := 𝒞) (A := A) (B := one) inr_mono) :=
    image_min _ _ ⟨Cat.id _, Cat.id_comp _⟩
  have hKl : (InverseImage il Kr).le (image m) :=
    -- inl⁻¹ Kr ≤ inl⁻¹ inrSub ≤ image m  (the latter has an initial domain).
    subLe_trans (invImage_mono_local il hKr_le)
      (invImage_inl_inrSub_le_any (A := A) (B := one) (image m))
  -- assemble: entire A ≤ inl⁻¹(entire) ≤ inl⁻¹(union) ≤ union(inl⁻¹J)(inl⁻¹Kr) ≤ image m.
  exact subLe_trans ha (subLe_trans hb (subLe_trans hc
    (HasSubobjectUnions.union_min _ _ _ hJl hKl)))

section Distributivity
open HasBinaryCoproducts
/-! ### §1.626 Distributivity of products over coproducts (UNIVERSAL coproducts)

  Freyd §1.626: in a POSITIVE pre-logos the coproduct is not just disjoint but *universal*
  (stable under pullback), and universality is equivalent to the distributive law

      (A + B) × C  ≅  A × C  +  B × C.

  This is the missing keystone `coprodProdDistrib`.  CRUCIALLY it is **derivable** from the
  `DisjointBinaryCoproduct` data already recorded (`inl ∩ inr ≤ ⊥`, `inl ∪ inr = ⊤`, `inl/inr`
  monic) — no separate `universal`/extensivity axiom is needed — because the inverse-image
  functor `fst#` along `fst : (A+B)×C → A+B` already preserves `entire` and `union`
  (`PreLogos.invImage_preserves_union`), and the two summand inclusions

      `prodCoprodInl = inl × id_C : A×C ↣ (A+B)×C`,
      `prodCoprodInr = inr × id_C : B×C ↣ (A+B)×C`

  are exactly `fst#(inl)` and `fst#(inr)`.  Disjointness `inl ∩ inr ≤ ⊥` and the cover
  `inl ∪ inr = ⊤` then transport (along `fst#`) to a *complemented pair* on `(A+B)×C`, and
  `complementedSub_iso_coproduct` (§1.62/§1.631) converts a complemented pair into the
  coproduct iso `(A+B)×C ≅ A×C + B×C`.  So Freyd's universal coproducts are a *theorem* here,
  not extra structure: the `DisjointBinaryCoproduct` encoding is faithful and complete. -/

/-- `inl × id_C : A×C → (A+B)×C`, the left injection of the distributivity comparison. -/
noncomputable def prodCoprodInl (A B C : 𝒞) : prod A C ⟶ prod (coprod A B) C :=
  pair (fst ≫ HasBinaryCoproducts.inl) snd

/-- `inr × id_C : B×C → (A+B)×C`, the right injection of the distributivity comparison. -/
noncomputable def prodCoprodInr (A B C : 𝒞) : prod B C ⟶ prod (coprod A B) C :=
  pair (fst ≫ HasBinaryCoproducts.inr) snd

/-- `inl × id_C` is monic (`inl` monic + projections jointly monic). -/
theorem prodCoprodInl_mono (A B C : 𝒞) : Monic (prodCoprodInl (𝒞 := 𝒞) A B C) := by
  intro W u v huv
  have h1 : (u ≫ fst) ≫ (HasBinaryCoproducts.inl (A := A) (B := B)) = (v ≫ fst) ≫ HasBinaryCoproducts.inl := by
    have := congrArg (· ≫ fst) huv
    simpa only [prodCoprodInl, Cat.assoc, fst_pair] using this
  have h2 : u ≫ snd = v ≫ snd := by
    have := congrArg (· ≫ snd) huv
    simpa only [prodCoprodInl, Cat.assoc, snd_pair] using this
  exact fst_snd_jointly_monic u v (inl_mono _ _ h1) h2

/-- `inr × id_C` is monic. -/
theorem prodCoprodInr_mono (A B C : 𝒞) : Monic (prodCoprodInr (𝒞 := 𝒞) A B C) := by
  intro W u v huv
  have h1 : (u ≫ fst) ≫ (HasBinaryCoproducts.inr (A := A) (B := B)) = (v ≫ fst) ≫ HasBinaryCoproducts.inr := by
    have := congrArg (· ≫ fst) huv
    simpa only [prodCoprodInr, Cat.assoc, fst_pair] using this
  have h2 : u ≫ snd = v ≫ snd := by
    have := congrArg (· ≫ snd) huv
    simpa only [prodCoprodInr, Cat.assoc, snd_pair] using this
  exact fst_snd_jointly_monic u v (inr_mono _ _ h1) h2

/-- The left summand `inl × id_C` packaged as a subobject of `(A+B)×C`. -/
noncomputable def prodCoprodInlSub (A B C : 𝒞) : Subobject 𝒞 (prod (coprod A B) C) :=
  ⟨_, prodCoprodInl A B C, prodCoprodInl_mono A B C⟩

/-- The right summand `inr × id_C` packaged as a subobject of `(A+B)×C`. -/
noncomputable def prodCoprodInrSub (A B C : 𝒞) : Subobject 𝒞 (prod (coprod A B) C) :=
  ⟨_, prodCoprodInr A B C, prodCoprodInr_mono A B C⟩

/-- `fst#(inl) ≤ inl × id_C`: the pullback of `inl` along `fst : (A+B)×C → A+B` factors through
    `inl × id_C`.  A pullback point `w` has `w#₁ : ·→(A+B)×C`, `w#₂ : ·→A` with
    `w#₁ ≫ fst = w#₂ ≫ inl`; the witness `pair w#₂ (w#₁ ≫ snd) : ·→A×C` composes with
    `inl × id_C` back to `w#₁` (jointly monic check). -/
theorem invImg_fst_inl_le (A B C : 𝒞) :
    (InverseImage (fst : prod (coprod A B) C ⟶ coprod A B)
        (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono)).le (prodCoprodInlSub A B C) := by
  let pb := HasPullbacks.has (fst : prod (coprod A B) C ⟶ coprod A B)
              (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono).arr
  have hw : pb.cone.π₁ ≫ (fst : prod (coprod A B) C ⟶ coprod A B)
          = pb.cone.π₂ ≫ (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono).arr := pb.cone.w
  refine ⟨pair pb.cone.π₂ (pb.cone.π₁ ≫ snd), ?_⟩
  show pair pb.cone.π₂ (pb.cone.π₁ ≫ snd) ≫ prodCoprodInl A B C = pb.cone.π₁
  apply fst_snd_jointly_monic
  · show (pair pb.cone.π₂ (pb.cone.π₁ ≫ snd) ≫ prodCoprodInl A B C) ≫ fst = pb.cone.π₁ ≫ fst
    simp only [prodCoprodInl, Cat.assoc, fst_pair]; rw [← Cat.assoc, fst_pair]; exact hw.symm
  · show (pair pb.cone.π₂ (pb.cone.π₁ ≫ snd) ≫ prodCoprodInl A B C) ≫ snd = pb.cone.π₁ ≫ snd
    simp only [prodCoprodInl, Cat.assoc, snd_pair]

/-- `fst#(inr) ≤ inr × id_C` (mirror of `invImg_fst_inl_le`). -/
theorem invImg_fst_inr_le (A B C : 𝒞) :
    (InverseImage (fst : prod (coprod A B) C ⟶ coprod A B)
        (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono)).le (prodCoprodInrSub A B C) := by
  let pb := HasPullbacks.has (fst : prod (coprod A B) C ⟶ coprod A B)
              (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono).arr
  have hw : pb.cone.π₁ ≫ (fst : prod (coprod A B) C ⟶ coprod A B)
          = pb.cone.π₂ ≫ (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono).arr := pb.cone.w
  refine ⟨pair pb.cone.π₂ (pb.cone.π₁ ≫ snd), ?_⟩
  show pair pb.cone.π₂ (pb.cone.π₁ ≫ snd) ≫ prodCoprodInr A B C = pb.cone.π₁
  apply fst_snd_jointly_monic
  · show (pair pb.cone.π₂ (pb.cone.π₁ ≫ snd) ≫ prodCoprodInr A B C) ≫ fst = pb.cone.π₁ ≫ fst
    simp only [prodCoprodInr, Cat.assoc, fst_pair]; rw [← Cat.assoc, fst_pair]; exact hw.symm
  · show (pair pb.cone.π₂ (pb.cone.π₁ ≫ snd) ≫ prodCoprodInr A B C) ≫ snd = pb.cone.π₁ ≫ snd
    simp only [prodCoprodInr, Cat.assoc, snd_pair]

/-- **Universality (cover half)**: the two summands jointly cover, `⊤ ≤ (inl×id) ∪ (inr×id)`.
    Pull the cover `inl ∪ inr = ⊤` back along `fst`: `fst#` preserves `entire` and `union`, and
    `fst#(inl) ≤ inl×id`, `fst#(inr) ≤ inr×id`. -/
theorem prodCoprod_entire_le_union (A B C : 𝒞) :
    (Subobject.entire (prod (coprod A B) C)).le
      (HasSubobjectUnions.union (prodCoprodInlSub A B C) (prodCoprodInrSub A B C)) := by
  let f : prod (coprod A B) C ⟶ coprod A B := fst
  have ha : (Subobject.entire (prod (coprod A B) C)).le (InverseImage f (Subobject.entire _)) :=
    entire_le_invImage_entire f
  have hbu : (Subobject.entire (coprod A B)).le
      (HasSubobjectUnions.union (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono)
                                (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono)) :=
    inl_union_inr_entire
  have hb : (InverseImage f (Subobject.entire _)).le
      (InverseImage f (HasSubobjectUnions.union (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono)
                                                (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono))) :=
    invImage_mono_local f hbu
  have hc : (InverseImage f (HasSubobjectUnions.union (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono)
                                                      (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono))).le
      (HasSubobjectUnions.union (InverseImage f (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono))
                                (InverseImage f (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono))) :=
    (PreLogos.invImage_preserves_union f _ _).1
  have hd : (HasSubobjectUnions.union (InverseImage f (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono))
                                      (InverseImage f (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono))).le
      (HasSubobjectUnions.union (prodCoprodInlSub A B C) (prodCoprodInrSub A B C)) :=
    HasSubobjectUnions.union_min _ _ _
      (subLe_trans (invImg_fst_inl_le A B C) (HasSubobjectUnions.union_left _ _))
      (subLe_trans (invImg_fst_inr_le A B C) (HasSubobjectUnions.union_right _ _))
  exact subLe_trans ha (subLe_trans hb (subLe_trans hc hd))

/-- **Disjointness half**: the two summands are disjoint, `(inl×id) ∩ (inr×id) ≤ ⊥`.
    A point of the intersection (pullback of `inl×id`, `inr×id`) has `fst`-images colliding
    `(π₁≫fst)≫inl = (π₂≫fst)≫inr`, so `coprod_inl_inr_disjoint_elt` (§1.621) makes its apex
    initial; a map into the bottom of `(A+B)×C` then exists and is unique. -/
theorem prodCoprod_inter_le_bottom (A B C : 𝒞) :
    (Subobject.inter (prodCoprodInlSub A B C) (prodCoprodInrSub A B C)).le
      (PreLogos.bottom (prod (coprod A B) C)) := by
  let pb := HasPullbacks.has (prodCoprodInlSub A B C).arr (prodCoprodInrSub A B C).arr
  have hw : pb.cone.π₁ ≫ prodCoprodInl A B C = pb.cone.π₂ ≫ prodCoprodInr A B C := pb.cone.w
  have hcollide : (pb.cone.π₁ ≫ fst) ≫ (HasBinaryCoproducts.inl (A := A) (B := B))
                = (pb.cone.π₂ ≫ fst) ≫ HasBinaryCoproducts.inr := by
    have := congrArg (· ≫ fst) hw
    simp only [prodCoprodInl, prodCoprodInr, Cat.assoc, fst_pair] at this
    simpa only [Cat.assoc] using this
  letI hPL : PreLogos 𝒞 := DisjointBinaryCoproduct.toPositivePreLogos.toPreLogos
  obtain ⟨e, _⟩ := coprod_inl_inr_disjoint_elt (𝒟 := 𝒞) (A := A) (B := B)
    (pb.cone.π₁ ≫ fst) (pb.cone.π₂ ≫ fst) hcollide
  obtain ⟨ζ, _⟩ := hPL.bottom_dom_iso (coprod A B) hPL.toHasTerminal.one
  have hiso : IsIso (e ≫ ζ) := any_map_to_zero_is_iso hPL (e ≫ ζ)
  obtain ⟨zinv, hz, _⟩ := hiso
  have hinit : ∀ {X : 𝒞} (s t : pb.cone.pt ⟶ X), s = t := by
    intro X s t
    have key : ∀ (w : pb.cone.pt ⟶ X), w = (e ≫ ζ) ≫ (zinv ≫ w) := by
      intro w; rw [← Cat.assoc, hz, Cat.id_comp]
    rw [key s, key t,
        (minimal_subobject_of_one_is_coterminator hPL).init_uniq (zinv ≫ s) (zinv ≫ t)]
  obtain ⟨ψ, _⟩ := hPL.bottom_dom_iso (coprod A B) (prod (coprod A B) C)
  exact ⟨e ≫ ψ, hinit _ _⟩

/-- **§1.626 DISTRIBUTIVITY / UNIVERSAL COPRODUCTS** — the keystone.

    `(A + B) × C  ≅  A × C  +  B × C`.

    Derived (no extra axiom) from `DisjointBinaryCoproduct`: the pair
    `(inl × id_C, inr × id_C)` is a *complemented pair* on `(A+B)×C`
    (`prodCoprod_inter_le_bottom` + `prodCoprod_entire_le_union`), and
    `complementedSub_iso_coproduct` converts a complemented pair into the coproduct iso.
    This shows Freyd's "positive ⟹ universal coproducts" is a theorem of the present
    `DisjointBinaryCoproduct` encoding — the encoding is faithful and needs no `universal` field. -/
theorem coprodProdDistrib (A B C : 𝒞) :
    Isomorphic (prod (coprod A B) C) (coprod (prod A C) (prod B C)) := by
  have hiso := complementedSub_iso_coproduct
    (prodCoprodInlSub A B C) (prodCoprodInrSub A B C)
    (prodCoprod_inter_le_bottom A B C) (prodCoprod_entire_le_union A B C)
  -- `complementedSub_iso_coproduct` gives `(A+B)×C ≅ (inl×id).dom + (inr×id).dom`; the summand
  -- domains are definitionally `A×C` and `B×C`.
  exact hiso

end Distributivity

/-- §1.633: A positive pre-logos is capital iff
    (1) every complemented subterminator is projective, and
    (2) the complemented subterminators form a basis.

    BINDER NOTE.  Stated with `[DisjointBinaryCoproduct 𝒞]` rather than the bare
    `[PositivePreLogos 𝒞]`: §1.633 is genuinely about *disjoint* coproducts (it routes through
    §1.631 `complemented_of_projective_is_projective`, which needs the disjointness
    `coprod_inl_inr_disjoint_elt`).  `DisjointBinaryCoproduct` is this repo's faithful rendering
    of Freyd's "positive pre-logos" (§1.621/§1.623), so the strengthening is faithful, matching
    the §1.631 precedent in this same file. -/
theorem capital_iff_complemented_subterminators :
    Capital (𝒞 := 𝒞) ↔
    (∀ U : Subobject 𝒞 one, IsComplementedSub U → Projective U.dom)
    ∧ IsBasis (fun G => ∃ U : Subobject 𝒞 one, IsComplementedSub U ∧ Isomorphic G U.dom) := by
  constructor
  · -- (⟹)  Capital ⟹ subterminators projective ∧ form a basis.
    intro hcap
    -- PROPER-MONIC clause first (it powers the generating clause): for a proper mono `m : A' ↣ A`,
    -- find a complemented subterminator `G` and `x : G → A` not factoring through `m`.
    have hpm : ∀ {A' A : 𝒞} (m : A' ⟶ A), Monic m → ¬ IsIso m →
        ∃ G, (∃ U : Subobject 𝒞 one, IsComplementedSub U ∧ Isomorphic G U.dom) ∧
          ∃ x : G ⟶ A, ¬ ∃ y, y ≫ m = x := by
      intro A' A m hm hmiso
      -- `A+1` is well-supported, so capital ⟹ well-pointed.
      have hwp : WellPointed (HasBinaryCoproducts.coprod A one) :=
        hcap _ (wellSupported_coprod_one A)
      -- `S := image (coprodMapOne m)` is a PROPER mono into `A+1` (`coprodMapOne_image_proper`);
      -- well-pointedness gives a point `p : 1 → A+1` missing it.
      let S := image (coprodMapOne m)
      obtain ⟨p, hp⟩ := hwp S.arr S.monic (coprodMapOne_image_proper m hm hmiso)
      -- split `p` into its `inl`/`inr` parts: `U := p#inl` is a complemented subterminator with
      -- leg `f₁ : U.dom → A`, complement `U₂ := p#inr` (leg `f₂`), and `U ∪ U₂` entire.
      obtain ⟨U, U₂, f₁, f₂, hcomp, hcover, hr1, hr2⟩ :=
        point_inl_complementedSubterminator (B₁ := A) (B₂ := one) p
      refine ⟨U.dom, ⟨U, hcomp, isomorphic_refl _⟩, f₁, ?_⟩
      rintro ⟨y, hy⟩            -- y : U.dom → A', hy : y ≫ m = f₁
      -- contradiction: `p` then factors through `S`, against `hp`.
      apply hp
      -- `c := case U.arr U₂.arr : U.dom + U₂.dom → 1` is a cover (its image `U ∪ U₂` is entire).
      let c := HasBinaryCoproducts.case U.arr U₂.arr
      have hc_cover : Cover c := by
        refine (cover_iff_image_entire c).2 (entire_of_entire_le ?_)
        -- entire 1 ≤ U ∪ U₂ ≤ union (image U.arr) (image U₂.arr) ≤ image c.
        have hUle : U.le (image U.arr) := ⟨image.lift U.arr, image.lift_fac U.arr⟩
        have hU₂le : U₂.le (image U₂.arr) := ⟨image.lift U₂.arr, image.lift_fac U₂.arr⟩
        -- U ∪ U₂ ≤ union (image U.arr) (image U₂.arr).
        have hmono : (HasSubobjectUnions.union U U₂).le
            (HasSubobjectUnions.union (image U.arr) (image U₂.arr)) :=
          HasSubobjectUnions.union_min _ _ _
            (subLe_trans hUle (HasSubobjectUnions.union_left _ _))
            (subLe_trans hU₂le (HasSubobjectUnions.union_right _ _))
        -- union (image U.arr) (image U₂.arr) ≤ image c  (it is an image of `c`, `image c` minimal-target).
        have huac : (HasSubobjectUnions.union (image U.arr) (image U₂.arr)).le (image c) :=
          (union_via_coproduct_image U.arr U₂.arr).2 (image c) (image_allows c)
        exact subLe_trans hcover (subLe_trans hmono huac)
      -- `c ≫ p` factors through `coprodMapOne m`:  both `inl`/`inr` legs do.
      let d : HasBinaryCoproducts.coprod U.dom U₂.dom ⟶ HasBinaryCoproducts.coprod A' one :=
        HasBinaryCoproducts.case (y ≫ HasBinaryCoproducts.inl) (f₂ ≫ HasBinaryCoproducts.inr)
      have hcp : c ≫ p = d ≫ coprodMapOne m := by
        -- both sides equal `case (inl ≫ d ≫ coprodMapOne m) (inr ≫ d ≫ coprodMapOne m)`.
        refine (HasBinaryCoproducts.case_uniq _ _ (c ≫ p) ?_ ?_).trans
          (HasBinaryCoproducts.case_uniq _ _ (d ≫ coprodMapOne m) rfl rfl).symm
        · -- inl ≫ c ≫ p = U.arr ≫ p = f₁ ≫ inl = (y≫m)≫inl = inl ≫ (d ≫ coprodMapOne m).
          calc HasBinaryCoproducts.inl ≫ (c ≫ p)
              = (HasBinaryCoproducts.inl ≫ c) ≫ p := (Cat.assoc _ _ _).symm
            _ = U.arr ≫ p := by rw [HasBinaryCoproducts.case_inl]
            _ = f₁ ≫ HasBinaryCoproducts.inl := hr1
            _ = (y ≫ m) ≫ HasBinaryCoproducts.inl := by rw [hy]
            _ = y ≫ (m ≫ HasBinaryCoproducts.inl) := Cat.assoc _ _ _
            _ = y ≫ (HasBinaryCoproducts.inl ≫ coprodMapOne m) := by
                  rw [coprodMapOne, HasBinaryCoproducts.case_inl]
            _ = (y ≫ HasBinaryCoproducts.inl) ≫ coprodMapOne m := (Cat.assoc _ _ _).symm
            _ = (HasBinaryCoproducts.inl ≫ d) ≫ coprodMapOne m := by
                  rw [HasBinaryCoproducts.case_inl]
            _ = HasBinaryCoproducts.inl ≫ (d ≫ coprodMapOne m) := Cat.assoc _ _ _
        · calc HasBinaryCoproducts.inr ≫ (c ≫ p)
              = (HasBinaryCoproducts.inr ≫ c) ≫ p := (Cat.assoc _ _ _).symm
            _ = U₂.arr ≫ p := by rw [HasBinaryCoproducts.case_inr]
            _ = f₂ ≫ HasBinaryCoproducts.inr := hr2
            _ = f₂ ≫ (HasBinaryCoproducts.inr ≫ coprodMapOne m) := by
                  rw [coprodMapOne, HasBinaryCoproducts.case_inr]
            _ = (f₂ ≫ HasBinaryCoproducts.inr) ≫ coprodMapOne m := (Cat.assoc _ _ _).symm
            _ = (HasBinaryCoproducts.inr ≫ d) ≫ coprodMapOne m := by
                  rw [HasBinaryCoproducts.case_inr]
            _ = HasBinaryCoproducts.inr ≫ (d ≫ coprodMapOne m) := Cat.assoc _ _ _
      -- so `c ≫ p` factors through `S = image (coprodMapOne m)`; the cover/mono diagonal lifts `p`.
      have hsq : c ≫ p = (d ≫ image.lift (coprodMapOne m)) ≫ S.arr := by
        rw [hcp, Cat.assoc, image.lift_fac]
      obtain ⟨gg, _, hgg⟩ := cover_mono_diagonal hc_cover S.monic hsq
      exact ⟨gg, hgg⟩
    refine ⟨complemented_subterminator_projective hcap, ?_, hpm⟩
    · -- IsGeneratingSet: the complemented subterminators separate maps.  Standard "basis ⟹
      -- generating": for `f ≠ g : A → B` the equalizer `e ↣ A` (built as the pullback of `pair f g`
      -- and the diagonal `Δ = pair id id`, products+pullbacks suffice) is a PROPER mono; the
      -- proper-monic clause `hpm` gives `x : G → A` not factoring through it, but the
      -- separation hypothesis makes `x` equalize `f,g`, hence factor through `e` — contradiction.
      intro A B f g hsep
      refine Classical.byContradiction fun hfg => ?_
      -- equalizer `e = π₁ : P ↣ A` of `f, g`, as the pullback of `pair f g` and `Δ`.
      let pb := HasPullbacks.has (pair f g) (diag B)
      let e : pb.cone.pt ⟶ A := pb.cone.π₁
      -- `diag` is monic (retraction `fst`), so `e = π₁` (pullback of `diag`) is monic.
      have hemono : Monic e := pullback_fst_mono (pair f g) (diag B) (diag_mono B)
      -- `e ≫ f = e ≫ g`:  `e ≫ pair f g = π₂ ≫ diag`, post-compose `fst`/`snd`.
      have hef : e ≫ f = e ≫ g := by
        have hw : e ≫ pair f g = pb.cone.π₂ ≫ diag B := pb.cone.w
        have h1 : e ≫ f = pb.cone.π₂ := by
          calc e ≫ f = e ≫ (pair f g ≫ fst) := by rw [fst_pair]
            _ = (e ≫ pair f g) ≫ fst := (Cat.assoc _ _ _).symm
            _ = (pb.cone.π₂ ≫ diag B) ≫ fst := by rw [hw]
            _ = pb.cone.π₂ ≫ (diag B ≫ fst) := Cat.assoc _ _ _
            _ = pb.cone.π₂ := by rw [diag_fst, Cat.comp_id]
        have h2 : e ≫ g = pb.cone.π₂ := by
          calc e ≫ g = e ≫ (pair f g ≫ snd) := by rw [snd_pair]
            _ = (e ≫ pair f g) ≫ snd := (Cat.assoc _ _ _).symm
            _ = (pb.cone.π₂ ≫ diag B) ≫ snd := by rw [hw]
            _ = pb.cone.π₂ ≫ (diag B ≫ snd) := Cat.assoc _ _ _
            _ = pb.cone.π₂ := by rw [diag_snd, Cat.comp_id]
        rw [h1, h2]
      -- `e` is NOT iso:  an iso `e` would force `f = g` (cancel the iso, `e≫f = e≫g`).
      have heproper : ¬ IsIso e := by
        rintro ⟨einv, _, hinv2⟩
        exact hfg (by rw [← Cat.id_comp f, ← Cat.id_comp g, ← hinv2, Cat.assoc, Cat.assoc, hef])
      -- proper-monic clause gives `G`, `ℱ G`, `x : G → A` not factoring through `e`.
      obtain ⟨G, hGℱ, x, hx⟩ := hpm e hemono heproper
      -- but `x ≫ f = x ≫ g` (separation, since `ℱ G`), so `x` factors through `e` — contra.
      apply hx
      have hxeq : x ≫ f = x ≫ g := hsep G hGℱ x
      -- cone `⟨G, x, x≫f⟩` over `(pair f g, diag)`:  both `x ≫ pair f g` and `(x≫f) ≫ diag` equal
      -- `pair (x≫f) (x≫f)` (using `x≫f = x≫g`), so they agree.
      have hcone : x ≫ pair f g = (x ≫ f) ≫ diag B := by
        have hL : x ≫ pair f g = pair (x ≫ f) (x ≫ f) :=
          pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair, ← hxeq])
        have hR : (x ≫ f) ≫ diag B = pair (x ≫ f) (x ≫ f) :=
          pair_uniq _ _ _ (by rw [Cat.assoc, diag_fst, Cat.comp_id])
            (by rw [Cat.assoc, diag_snd, Cat.comp_id])
        rw [hL, hR]
      exact ⟨pb.lift ⟨G, x, x ≫ f, hcone⟩, pb.lift_fst ⟨G, x, x ≫ f, hcone⟩⟩
  · -- (⟸)  subterminators projective ∧ basis ⟹ Capital.
    -- Given proper `m : D ↣ A` with `A` well-supported, the basis gives a complemented
    -- subterminator `V` (`G ≅ V.dom`) and `x : V.dom → A` not factoring through `m`.  Extend `x`
    -- to a point `1 → A` by case-ing it against a lift `V₂.dom → A` of `term V₂.dom` through the
    -- cover `term A` (`V₂.dom` projective, `term A` a cover) over the iso `1 ≅ V.dom + V₂.dom`.
    -- That point misses `m` because its restriction to `V.dom` is `x`.
    rintro ⟨hproj, _hgen, hbasis⟩ A hws D m hm hmiso
    -- Basis applied to the proper mono `m`.
    obtain ⟨G, ⟨V, hV, hGV⟩, x, hx⟩ := hbasis m hm hmiso
    obtain ⟨V₂, hdisj, hentire⟩ := hV
    -- `V` and its complement `V₂` are both projective complemented subterminators.
    have hprojV  : Projective V.dom  := hproj V ⟨V₂, hdisj, hentire⟩
    have hprojV₂ : Projective V₂.dom := hproj V₂ (complementedSub_symm hdisj hentire)
    -- 1 ≅ V.dom + V₂.dom (`e : 1 → V.dom+V₂.dom`, iso).
    obtain ⟨e, einv, hee, heinv⟩ := complementedSub_iso_coproduct V V₂ hdisj hentire
    -- x' : V.dom → A, transported from x : G → A along G ≅ V.dom.
    obtain ⟨φ, φinv, hφφ, hφinv⟩ := hGV       -- φ : G → V.dom, iso, φinv : V.dom → G
    let x' : V.dom ⟶ A := φinv ≫ x
    -- x₂ : V₂.dom → A — lift of `term V₂.dom` through the cover `term A` (A well-supported).
    obtain ⟨x₂, _⟩ := hom_lifts_cover_of_projective
      (i := V₂.dom) (fun {P} ee hee => hprojV₂ ee hee) (f := term A) hws (term V₂.dom)
    -- The point `p : 1 → A`.
    let p : one ⟶ A := e ≫ HasBinaryCoproducts.case x' x₂
    refine ⟨p, ?_⟩
    rintro ⟨y, hy⟩
    -- Restrict `y ≫ m = p` to `V.dom` via `inl ≫ einv : V.dom → 1`, recovering `x'`.
    apply hx
    refine ⟨φ ≫ (HasBinaryCoproducts.inl ≫ einv) ≫ y, ?_⟩
    -- (φ ≫ (inl ≫ einv) ≫ y) ≫ m = φ ≫ (inl ≫ einv) ≫ p = φ ≫ inl ≫ case x' x₂ = φ ≫ x' = x.
    calc (φ ≫ (HasBinaryCoproducts.inl ≫ einv) ≫ y) ≫ m
        = φ ≫ (HasBinaryCoproducts.inl ≫ einv) ≫ (y ≫ m) := by
          rw [Cat.assoc, Cat.assoc, Cat.assoc]
      _ = φ ≫ (HasBinaryCoproducts.inl ≫ einv) ≫ p := by rw [hy]
      _ = φ ≫ HasBinaryCoproducts.inl ≫ (einv ≫ e) ≫ HasBinaryCoproducts.case x' x₂ := by
          simp only [p, Cat.assoc]
      _ = φ ≫ HasBinaryCoproducts.inl ≫ HasBinaryCoproducts.case x' x₂ := by
          rw [heinv, Cat.id_comp]
      _ = φ ≫ x' := by rw [HasBinaryCoproducts.case_inl]
      _ = (φ ≫ φinv) ≫ x := by rw [Cat.assoc]
      _ = x := by rw [hφφ, Cat.id_comp]

end IsoCoprodComplemented

end Freyd
