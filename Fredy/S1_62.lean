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
  have hm_ginv_mono : Mono (m ≫ g_inv) := by
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
  have hmono_comp : Mono (m ≫ I.arr) := by
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
  have hpU_mono : Mono pU := monic_pair_of_monicPair Uu.colA Uu.colB Uu.isMonicPair
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
theorem graph_comp_recip_le_one_of_mono {A B : 𝒞} (x : A ⟶ B) (hx : Mono x) :
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
  have hpR_mono : Mono pR := monic_pair_of_monicPair RHS.colA RHS.colB RHS.isMonicPair
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
  have h1 : RelLe (xrel ⊚ graph g) (((graph π₁)° ⊚ graph π₂) ⊚ graph g) :=
    compose_le hinter (rel_le_refl _)
  have h2 : RelLe (((graph π₁)° ⊚ graph π₂) ⊚ graph g) ((graph π₁)° ⊚ (graph π₂ ⊚ graph g)) :=
    (compose_assoc_of_regular ((graph π₁)°) (graph π₂) (graph g)).1
  have h3 : RelLe ((graph π₁)° ⊚ (graph π₂ ⊚ graph g)) ((graph π₁)° ⊚ graph (π₂ ≫ g)) :=
    compose_le (rel_le_refl _) (comp_graph π₂ g)
  have h4 : RelLe ((graph π₁)° ⊚ graph (π₂ ≫ g)) ((graph π₁)° ⊚ graph (π₁ ≫ f)) := by
    rw [hcocone]; exact rel_le_refl _
  have h5 : RelLe ((graph π₁)° ⊚ graph (π₁ ≫ f)) ((graph π₁)° ⊚ (graph π₁ ⊚ graph f)) :=
    compose_le (rel_le_refl _) (graph_comp π₁ f)
  have h6 : RelLe ((graph π₁)° ⊚ (graph π₁ ⊚ graph f)) (((graph π₁)° ⊚ graph π₁) ⊚ graph f) :=
    (compose_assoc_of_regular ((graph π₁)°) (graph π₁) (graph f)).2
  have h7 : RelLe (((graph π₁)° ⊚ graph π₁) ⊚ graph f) (graph (Cat.id A₁) ⊚ graph f) :=
    compose_le (reciprocal_comp_self_le_one π₁) (rel_le_refl _)
  have h8 : RelLe (graph (Cat.id A₁) ⊚ graph f) (graph f) := graph_id_comp (graph f)
  exact rel_le_trans h1 (rel_le_trans h2 (rel_le_trans h3 (rel_le_trans h4
    (rel_le_trans h5 (rel_le_trans h6 (rel_le_trans h7 h8))))))

/-- Diagonal term: `P° ⊚ P ⊆ 1_Q` where `P = (graph x)° ⊚ graph f` and `x` is monic. -/
theorem diag_le_one {A₁ U Q : 𝒞} (x : A₁ ⟶ U) (f : A₁ ⟶ Q) (hx : Mono x) :
    RelLe (((graph x)° ⊚ graph f)° ⊚ ((graph x)° ⊚ graph f)) (graph (Cat.id Q)) := by
  have hPr : RelLe (((graph x)° ⊚ graph f)°) ((graph f)° ⊚ graph x) := by
    have h := reciprocal_comp_le ((graph x)°) (graph f)
    rw [reciprocal_invol] at h; exact h
  let Pr := (graph x)° ⊚ graph f
  have h1 : RelLe (Pr° ⊚ Pr) (((graph f)° ⊚ graph x) ⊚ Pr) := compose_le hPr (rel_le_refl _)
  have h2 : RelLe (((graph f)° ⊚ graph x) ⊚ Pr) ((graph f)° ⊚ (graph x ⊚ Pr)) :=
    (compose_assoc_of_regular ((graph f)°) (graph x) Pr).1
  have h3 : RelLe ((graph f)° ⊚ (graph x ⊚ Pr))
                  ((graph f)° ⊚ ((graph x ⊚ (graph x)°) ⊚ graph f)) :=
    compose_le (rel_le_refl _) (compose_assoc_of_regular (graph x) ((graph x)°) (graph f)).2
  have h4 : RelLe ((graph f)° ⊚ ((graph x ⊚ (graph x)°) ⊚ graph f))
                  ((graph f)° ⊚ (graph (Cat.id A₁) ⊚ graph f)) :=
    compose_le (rel_le_refl _) (compose_le (graph_comp_recip_le_one_of_mono x hx) (rel_le_refl _))
  have h5 : RelLe ((graph f)° ⊚ (graph (Cat.id A₁) ⊚ graph f)) ((graph f)° ⊚ graph f) :=
    compose_le (rel_le_refl _) (graph_id_comp (graph f))
  have h6 : RelLe ((graph f)° ⊚ graph f) (graph (Cat.id Q)) := reciprocal_comp_self_le_one f
  exact rel_le_trans h1 (rel_le_trans h2 (rel_le_trans h3 (rel_le_trans h4 (rel_le_trans h5 h6))))

/-- Cross term: `P° ⊚ Q ⊆ 1_Q` for `P = (graph x)° ⊚ graph f`, `Q = (graph y)° ⊚ graph g`,
    given the compatibility consequence `hxyg`. -/
theorem cross_le_one {A₁ A₂ U Q : 𝒞} (x : A₁ ⟶ U) (y : A₂ ⟶ U) (f : A₁ ⟶ Q) (g : A₂ ⟶ Q)
    (hxyg : RelLe ((graph x ⊚ (graph y)°) ⊚ graph g) (graph f)) :
    RelLe (((graph x)° ⊚ graph f)° ⊚ ((graph y)° ⊚ graph g)) (graph (Cat.id Q)) := by
  have hPr : RelLe (((graph x)° ⊚ graph f)°) ((graph f)° ⊚ graph x) := by
    have h := reciprocal_comp_le ((graph x)°) (graph f)
    rw [reciprocal_invol] at h; exact h
  let Qr := (graph y)° ⊚ graph g
  have h1 : RelLe ((((graph x)° ⊚ graph f)°) ⊚ Qr) (((graph f)° ⊚ graph x) ⊚ Qr) :=
    compose_le hPr (rel_le_refl _)
  have h2 : RelLe (((graph f)° ⊚ graph x) ⊚ Qr) ((graph f)° ⊚ (graph x ⊚ Qr)) :=
    (compose_assoc_of_regular ((graph f)°) (graph x) Qr).1
  have h3 : RelLe ((graph f)° ⊚ (graph x ⊚ Qr))
                  ((graph f)° ⊚ ((graph x ⊚ (graph y)°) ⊚ graph g)) :=
    compose_le (rel_le_refl _) (compose_assoc_of_regular (graph x) ((graph y)°) (graph g)).2
  have h4 : RelLe ((graph f)° ⊚ ((graph x ⊚ (graph y)°) ⊚ graph g)) ((graph f)° ⊚ graph f) :=
    compose_le (rel_le_refl _) hxyg
  have h5 : RelLe ((graph f)° ⊚ graph f) (graph (Cat.id Q)) := reciprocal_comp_self_le_one f
  exact rel_le_trans h1 (rel_le_trans h2 (rel_le_trans h3 (rel_le_trans h4 h5)))

/-- Simplicity of the descent relation `R = P ∪ᵣ Q` from the four atomic bounds. -/
theorem simple_R [HasBinaryCoproducts 𝒞] {U Q : 𝒞} (P Qr : BinRel 𝒞 U Q)
    (hPP : RelLe (P° ⊚ P) (graph (Cat.id Q)))
    (hQQ : RelLe (Qr° ⊚ Qr) (graph (Cat.id Q)))
    (hPQ : RelLe (P° ⊚ Qr) (graph (Cat.id Q)))
    (hQP : RelLe (Qr° ⊚ P) (graph (Cat.id Q))) :
    RelLe ((P ∪ᵣ Qr)° ⊚ (P ∪ᵣ Qr)) (graph (Cat.id Q)) := by
  have step1 : RelLe ((P ∪ᵣ Qr)° ⊚ (P ∪ᵣ Qr)) (((P ∪ᵣ Qr)° ⊚ P) ∪ᵣ ((P ∪ᵣ Qr)° ⊚ Qr)) :=
    compose_union_right ((P ∪ᵣ Qr)°) P Qr
  refine rel_le_trans step1 (le_relUnion ?_ ?_)
  · have hP_R : RelLe (P° ⊚ (P ∪ᵣ Qr)) (graph (Cat.id Q)) :=
      rel_le_trans (compose_union_right (P°) P Qr) (le_relUnion hPP hPQ)
    have hrecip : RelLe ((P ∪ᵣ Qr)° ⊚ P) ((P° ⊚ (P ∪ᵣ Qr))°) := by
      have h := (reciprocal_comp (P°) (P ∪ᵣ Qr)).2
      rw [reciprocal_invol] at h; exact h
    refine rel_le_trans hrecip ?_
    have h := reciprocal_mono hP_R
    rwa [show (graph (Cat.id Q))° = graph (Cat.id Q) from rfl] at h
  · have hQ_R : RelLe (Qr° ⊚ (P ∪ᵣ Qr)) (graph (Cat.id Q)) :=
      rel_le_trans (compose_union_right (Qr°) P Qr) (le_relUnion hQP hQQ)
    have hrecip : RelLe ((P ∪ᵣ Qr)° ⊚ Qr) ((Qr° ⊚ (P ∪ᵣ Qr))°) := by
      have h := (reciprocal_comp (Qr°) (P ∪ᵣ Qr)).2
      rw [reciprocal_invol] at h; exact h
    refine rel_le_trans hrecip ?_
    have h := reciprocal_mono hQ_R
    rwa [show (graph (Cat.id Q))° = graph (Cat.id Q) from rfl] at h

/-- Entirety ingredient: `x° ⊚ x ⊆ R ⊚ R°` when `P = (graph x)° ⊚ graph f ⊆ R`. -/
theorem xx_le_RRrecip {A₁ U Q : 𝒞} (x : A₁ ⟶ U) (f : A₁ ⟶ Q)
    (R : BinRel 𝒞 U Q) (hPR : RelLe ((graph x)° ⊚ graph f) R) :
    RelLe ((graph x)° ⊚ graph x) (R ⊚ R°) := by
  have hEntf : RelLe (graph (Cat.id A₁)) (graph f ⊚ (graph f)°) := (graph_is_map f).1
  have hA : RelLe (graph x) ((graph f ⊚ (graph f)°) ⊚ graph x) :=
    rel_le_trans (comp_graph_id_left (graph x)) (compose_le hEntf (rel_le_refl _))
  have h1 : RelLe ((graph x)° ⊚ graph x) ((graph x)° ⊚ ((graph f ⊚ (graph f)°) ⊚ graph x)) :=
    compose_le (rel_le_refl _) hA
  have h2 : RelLe ((graph x)° ⊚ ((graph f ⊚ (graph f)°) ⊚ graph x))
                  ((graph x)° ⊚ (graph f ⊚ ((graph f)° ⊚ graph x))) :=
    compose_le (rel_le_refl _) (compose_assoc_of_regular (graph f) ((graph f)°) (graph x)).1
  have h3 : RelLe ((graph x)° ⊚ (graph f ⊚ ((graph f)° ⊚ graph x)))
                  (((graph x)° ⊚ graph f) ⊚ ((graph f)° ⊚ graph x)) :=
    (compose_assoc_of_regular ((graph x)°) (graph f) ((graph f)° ⊚ graph x)).2
  have hPrecip : RelLe ((graph f)° ⊚ graph x) (R°) := by
    have hPrec : RelLe (((graph x)° ⊚ graph f)°) (R°) := reciprocal_mono hPR
    have hsub : RelLe ((graph f)° ⊚ graph x) (((graph x)° ⊚ graph f)°) := by
      have h := (reciprocal_comp ((graph x)°) (graph f)).2
      rw [reciprocal_invol] at h; exact h
    exact rel_le_trans hsub hPrec
  have h4 : RelLe (((graph x)° ⊚ graph f) ⊚ ((graph f)° ⊚ graph x)) (R ⊚ R°) :=
    compose_le hPR hPrecip
  exact rel_le_trans h1 (rel_le_trans h2 (rel_le_trans h3 h4))

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
  have hxmono : Mono x := by
    intro W u v huv; apply A₁.monic
    rw [← hx, ← Cat.assoc, ← Cat.assoc, huv]
  have hymono : Mono y := by
    intro W u v huv; apply A₂.monic
    rw [← hy, ← Cat.assoc, ← Cat.assoc, huv]
  have hjcov : Cover (HasBinaryCoproducts.case x y) := union_case_cover A₁ A₂ hx hy
  have hdesc : ∀ (c : PushoutCocone pb.cone.π₁ pb.cone.π₂),
      ∃ q : U.dom ⟶ c.pt, (x ≫ q = c.ι₁ ∧ y ≫ q = c.ι₂) ∧
        ∀ q' : U.dom ⟶ c.pt, x ≫ q' = c.ι₁ → y ≫ q' = c.ι₂ → q' = q := by
    intro c
    let f := c.ι₁
    let g := c.ι₂
    let P := (graph x)° ⊚ graph f
    let Q := (graph y)° ⊚ graph g
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
      have hsub : RelLe (Q° ⊚ P) ((P° ⊚ Q)°) := by
        have h := (reciprocal_comp (P°) Q).2
        rw [reciprocal_invol] at h; exact h
      refine rel_le_trans hsub ?_
      have h := reciprocal_mono hPQ
      rwa [show (graph (Cat.id c.pt))° = graph (Cat.id c.pt) from rfl] at h
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
    have hfac_gen : ∀ {C : 𝒞} (z : C ⟶ U.dom) (k : C ⟶ c.pt),
        RelLe ((graph z)° ⊚ graph k) R → z ≫ q = k := by
      intro C z k hpiece
      have step1 : RelLe (graph k) ((graph (Cat.id C)) ⊚ graph k) := comp_graph_id_left (graph k)
      have step2 : RelLe ((graph (Cat.id C)) ⊚ graph k) ((graph z ⊚ (graph z)°) ⊚ graph k) :=
        compose_le (graph_is_map z).1 (rel_le_refl _)
      have step3 : RelLe ((graph z ⊚ (graph z)°) ⊚ graph k) (graph z ⊚ ((graph z)° ⊚ graph k)) :=
        (compose_assoc_of_regular (graph z) ((graph z)°) (graph k)).1
      have step4 : RelLe (graph z ⊚ ((graph z)° ⊚ graph k)) (graph z ⊚ graph q) :=
        compose_le (rel_le_refl _) (rel_le_trans hpiece hRq)
      have step5 : RelLe (graph z ⊚ graph q) (graph (z ≫ q)) := comp_graph z q
      exact (graph_faithful (rel_le_trans step1 (rel_le_trans step2
        (rel_le_trans step3 (rel_le_trans step4 step5))))).symm
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

/-- §1.624: In a positive pre-logos, f: A → B₁+B₂ decomposes as
    f₁+f₂ from A₁ → B₁, A₂ → B₂ where A = A₁+A₂.
    Proof: A₁ = f#(inl), A₂ = f#(inr) via pasting lemma (§1.62). -/
theorem decompose_via_coproduct [PositivePreLogos 𝒞] {A B₁ B₂ : 𝒞} (f : A ⟶ HasBinaryCoproducts.coprod B₁ B₂) :
    ∃ (A₁ A₂ : 𝒞) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂), Isomorphic A (HasBinaryCoproducts.coprod A₁ A₂) := by
  -- A₁ := (InverseImage f (Subobject(inl))).dom, A₂ := (InverseImage f (Subobject(inr))).dom.
  -- A₁+A₂ ≅ A follows from the pasting lemma (sorry pending pasting_lemma proof).
  sorry

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
  ∀ {A' A : 𝒞} (m : A' ⟶ A), Mono m → ¬ IsIso m →
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
  power of the category of sets.  Proof via capital extension,
  complemented subterminators (which form a Boolean algebra),
  ultra-filters, and the T_ℱ construction. -/

theorem prelogos_representation_theorem (A : Type u) [Cat.{u} A] [PositivePreLogos A] :
    ∃ (T : A → (A → Type u)) (_ : Functor T), SeparatesMaps T := by
  -- The deep proof uses: capital extension (§1.63) + Stone representation
  -- of Boolean algebras via ultra-filters → T_ℱ is a faithful representation.
  -- Requires axiom of choice for the ultra-filter theorem.
  sorry


/-- FILTER in a subobject lattice: up-closed pre-filter (§1.634). -/
def IsFilter (ℱ : (Subobject 𝒞 one) → Prop) : Prop :=
  IsPreFilter ℱ ∧ ∀ (U V : Subobject 𝒞 one), ℱ U → Subobject.le U V → ℱ V

/-! ## §1.631 Complemented subobject of a projective is projective

  In a positive pre-logos, if P is a complemented subobject of a projective
  object Q (so Q ≅ P + P' for some P'), then P is projective.
  Proof: given a cover x : A ↠ P, extend to A + P' → P + P' using the
  coproduct inclusion; this is a cover of the projective Q, so it splits;
  composing with inl gives a section P → A. -/

/-- §1.631: In a positive pre-logos, a complemented subobject of a projective
    object is projective. -/
theorem complemented_of_projective_is_projective [PositivePreLogos 𝒞]
    {Q : 𝒞} (hQ : Projective Q) {P : 𝒞} (P' : 𝒞)
    (hiso : Isomorphic Q (HasBinaryCoproducts.coprod P P'))
    {A : 𝒞} (x : A ⟶ P) (hx : Cover x) :
    Projective P := by
  -- Given any cover y : B ↠ P we produce a section P → B.
  intro B y hy
  obtain ⟨φ, φ_inv, hφφ_inv, hφ_inv_φ⟩ := hiso
  -- φ : Q → P+P', φ_inv : P+P' → Q, φ ≫ φ_inv = id_Q, φ_inv ≫ φ = id_{P+P'}.
  -- φ_inv is monic (retraction φ gives left inverse).
  have hφ_inv_mono : Mono φ_inv :=
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
  -- KEY COMPUTATION: σ ≫ case(y, z) = id_P for ANY z : P' → P.
  -- Proof: h ≫ case(id_P, z) = case(y, z)  (unfold h = case(y ≫ inl, inr), use case_inl/case_inr).
  --        σ ≫ case(y, z) = σ ≫ h ≫ case(id_P, z) = inl_P ≫ case(id_P, z) = id_P.
  -- Equivalently: r := σ ≫ case(id_B, w) satisfies r ≫ y = id_P for ANY w : P' → B
  --   (since case(id_B, w) ≫ y = case(y, w ≫ y) and σ ≫ case(y, w ≫ y) = id_P by above).
  -- BLOCKER: no morphism z : P' → P (or w : P' → B) is available in the proof state.
  -- Coproduct disjointness (§1.62 pasting lemma) would yield t := inr_{P'} ≫ φ_inv ≫ s' = inr_{P'},
  -- forcing σ = r ≫ inl_B for some r : P → B, and then r ≫ y = id_P by the key computation.
  -- BLOCKED on pasting_lemma (§1.62) / compose_union_right (§1.616).
  obtain ⟨r, hr⟩ : ∃ r : P ⟶ B, r ≫ y = Cat.id P := by sorry
  exact ⟨r, hr⟩

/-! ## §1.633 Characterization of capital positive pre-logoi

  A positive pre-logos is capital iff its complemented subterminators
  (complemented subobjects of 1) are projective and form a basis. -/

/-- §1.633: A positive pre-logos is capital iff
    (1) every complemented subterminator is projective, and
    (2) the complemented subterminators form a basis. -/
theorem capital_iff_complemented_subterminators [PositivePreLogos 𝒞] :
    Capital (𝒞 := 𝒞) ↔
    (∀ U : Subobject 𝒞 one, IsComplementedSub U → Projective U.dom)
    ∧ IsBasis (fun G => ∃ U : Subobject 𝒞 one, IsComplementedSub U ∧ Isomorphic G U.dom) := by
  sorry

end Freyd
