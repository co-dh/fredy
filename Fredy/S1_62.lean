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
def inlSub [HasBinaryCoproducts 𝒞] {A B : 𝒞} (h : Mono (HasBinaryCoproducts.inl (A := A) (B := B))) :
    Subobject 𝒞 (HasBinaryCoproducts.coprod A B) :=
  ⟨A, HasBinaryCoproducts.inl, h⟩

/-- The right injection `inr : B ⟶ A+B` packaged as a subobject of `A+B`. -/
def inrSub [HasBinaryCoproducts 𝒞] {A B : 𝒞} (h : Mono (HasBinaryCoproducts.inr (A := A) (B := B))) :
    Subobject 𝒞 (HasBinaryCoproducts.coprod A B) :=
  ⟨B, HasBinaryCoproducts.inr, h⟩

/-- **§1.621/§1.623 DISJOINT BINARY COPRODUCT.**  A positive pre-logos in which the
    coproduct injections satisfy Freyd's §1.621 disjoint-complemented-union conditions.
    This is the missing positivity content that the amalgamation lemma (§1.651),
    balancedness (§1.652), and Diaconescu's theorem (§1.662) all rest on. -/
class DisjointBinaryCoproduct (𝒞 : Type u) [Cat.{v} 𝒞] extends PositivePreLogos 𝒞 where
  /-- The left injection is monic (it is a subobject inclusion). -/
  inl_monic : ∀ {A B : 𝒞}, Mono (HasBinaryCoproducts.inl (A := A) (B := B))
  /-- The right injection is monic. -/
  inr_monic : ∀ {A B : 𝒞}, Mono (HasBinaryCoproducts.inr (A := A) (B := B))
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
    Mono (HasBinaryCoproducts.inl (A := A) (B := B)) :=
  DisjointBinaryCoproduct.inl_monic

/-- **§1.621**: in a positive (disjoint) coproduct the right injection is monic. -/
theorem inr_mono [DisjointBinaryCoproduct 𝒞] {A B : 𝒞} :
    Mono (HasBinaryCoproducts.inr (A := A) (B := B)) :=
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

/-- §1.633: A positive pre-logos is capital iff
    (1) every complemented subterminator is projective, and
    (2) the complemented subterminators form a basis.

    BINDER NOTE.  Stated with `[DisjointBinaryCoproduct 𝒞]` rather than the bare
    `[PositivePreLogos 𝒞]`: §1.633 is genuinely about *disjoint* coproducts (it routes through
    §1.631 `complemented_of_projective_is_projective`, which needs the disjointness
    `coprod_inl_inr_disjoint_elt`).  `DisjointBinaryCoproduct` is this repo's faithful rendering
    of Freyd's "positive pre-logos" (§1.621/§1.623), so the strengthening is faithful, matching
    the §1.631 precedent in this same file. -/
theorem capital_iff_complemented_subterminators [DisjointBinaryCoproduct 𝒞] :
    Capital (𝒞 := 𝒞) ↔
    (∀ U : Subobject 𝒞 one, IsComplementedSub U → Projective U.dom)
    ∧ IsBasis (fun G => ∃ U : Subobject 𝒞 one, IsComplementedSub U ∧ Isomorphic G U.dom) := by
  constructor
  · -- (⟹)  Capital ⟹ subterminators projective ∧ form a basis.
    intro hcap
    refine ⟨complemented_subterminator_projective hcap, ?_, ?_⟩
    · -- IsGeneratingSet: points 1 → A separate maps (1 is itself a complemented subterminator).
      -- RESIDUAL (named infra): "in a capital positive pre-logos global points 1→A are jointly
      -- faithful".  Needs the §1.633 points-separation lemma (well-pointedness of the equalizer
      -- of f,g), which is not yet built in the S1_62 import chain.
      sorry
    · -- Proper-monic basis clause.
      -- RESIDUAL (named infra): the book's `A'+1 ↣ A+1` argument — proper coproduct injection,
      -- `A+1` well-supported, `decompose_via_coproduct` of `f : U → A+1`, and the pullback-square
      -- properness transfer giving a complemented subterminator `V₂` with a map `V₂ → A` not
      -- factoring through `A'`.  This `A'+1`/decompose-properness theory is not yet built.
      sorry
  · -- (⟸)  subterminators projective ∧ basis ⟹ Capital.
    -- RESIDUAL (named infra): the book's converse — given proper `A'↣A` with `A` well-supported,
    -- the basis gives `V₁+V₂=1` with `V₂` projective and (since `A→1` is a cover) a lift
    -- `V₂ → A`, yielding `U₁+U₂` proper in `V₁+V₂=1` and a point missing `A'`.  Same missing
    -- `A'+1`/decompose-properness + projective-lifting theory as the forward basis clause.
    sorry

end Freyd
