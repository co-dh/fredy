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
import Fredy.Horn          -- §2.218 BRICK 1: reuse `setCat : Cat (Type v)` for the regular structure of Set
import Fredy.S1_55
import Fredy.S1_56
import Fredy.S1_57
import Fredy.S1_58
import Fredy.S1_60
import Fredy.S1_61
import Fredy.WellOrdering   -- §1.635(a): mathlib-free Zorn for ultra-filter existence


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

/-- `S ∩ T ≤ S` (the intersection is below its left factor). -/
theorem Subobject.inter_le_left [HasPullbacks 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B) :
    (Subobject.inter S T).le S :=
  ⟨(HasPullbacks.has S.arr T.arr).cone.π₁, rfl⟩

/-- `S ∩ T ≤ T`. -/
theorem Subobject.inter_le_right [HasPullbacks 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B) :
    (Subobject.inter S T).le T :=
  ⟨(HasPullbacks.has S.arr T.arr).cone.π₂, ((HasPullbacks.has S.arr T.arr).cone.w).symm⟩

/-- The meet property: any `X` below both `S` and `T` is below `S ∩ T` (the pullback's
    universal property: `X`'s two factorizations form a cone, lifted into the pullback). -/
theorem Subobject.le_inter [HasPullbacks 𝒞] {B : 𝒞} {X S T : Subobject 𝒞 B}
    (hS : X.le S) (hT : X.le T) : X.le (Subobject.inter S T) := by
  obtain ⟨f, hf⟩ := hS; obtain ⟨g, hg⟩ := hT
  let pb := HasPullbacks.has S.arr T.arr
  let c : Cone S.arr T.arr := { pt := X.dom, π₁ := f, π₂ := g, w := by rw [hf, hg] }
  refine ⟨pb.lift c, ?_⟩
  show pb.lift c ≫ (pb.cone.π₁ ≫ S.arr) = X.arr
  rw [← Cat.assoc, pb.lift_fst c]; exact hf

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
    exact Subobject.le_trans ha (Subobject.le_trans hb hc)
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

/-! ### §1.634 The colimit functor `T_ℱ = colim_{U∈ℱ} Hom(U,-)`

  `PrefilterMap ℱ A` is only the disjoint union of the representing hom-sets; the
  actual value `T_ℱ(A)` is the *colimit*: two names `x : U→A`, `y : V→A` give the same
  element iff there is `W ∈ ℱ`, `W ⊆ U`, `W ⊆ V` with the two restrictions of `x, y`
  to `W` equal.  Because every `U.arr : U.dom ↣ 1` is monic, the inclusion `W ⊆ U` has a
  *unique* witness, so the restriction is canonical and the relation below is an honest
  equivalence (transitivity uses the ↓-directedness of the pre-filter `ℱ`). -/

/-- The book's naming relation on `PrefilterMap ℱ A`: `p ~ q` iff there is a common
    refinement `W ∈ ℱ` below both `p.U` and `q.U` on which the two maps agree.  The
    witnessing factorizations `a, b` are unique (monic `arr`), so this is canonical. -/
def PrefRel (ℱ : (Subobject 𝒞 one) → Prop) {A : 𝒞} (p q : PrefilterMap ℱ A) : Prop :=
  ∃ (W : Subobject 𝒞 one), ℱ W ∧ ∃ (a : W.dom ⟶ p.U.dom) (b : W.dom ⟶ q.U.dom),
    a ≫ p.U.arr = W.arr ∧ b ≫ q.U.arr = W.arr ∧ a ≫ p.map = b ≫ q.map

/-- `PrefRel` is reflexive (refine by `p.U` itself, identity factorization). -/
theorem PrefRel.refl (ℱ : (Subobject 𝒞 one) → Prop) {A : 𝒞} (p : PrefilterMap ℱ A) :
    PrefRel ℱ p p :=
  ⟨p.U, p.hU, Cat.id _, Cat.id _, Cat.id_comp _, Cat.id_comp _, rfl⟩

theorem PrefRel.symm (ℱ : (Subobject 𝒞 one) → Prop) {A : 𝒞} {p q : PrefilterMap ℱ A}
    (h : PrefRel ℱ p q) : PrefRel ℱ q p := by
  obtain ⟨W, hW, a, b, ha, hb, hab⟩ := h
  exact ⟨W, hW, b, a, hb, ha, hab.symm⟩

/-- Transitivity uses ↓-directedness of `ℱ`: a common refinement `W ⊆ W₁, W ⊆ W₂` of the
    two refinements, and monic cancellation of `q.U.arr` to splice the two agreements. -/
theorem PrefRel.trans (ℱ : (Subobject 𝒞 one) → Prop) (hℱ : IsPreFilter ℱ)
    {A : 𝒞} {p q r : PrefilterMap ℱ A}
    (h₁ : PrefRel ℱ p q) (h₂ : PrefRel ℱ q r) : PrefRel ℱ p r := by
  obtain ⟨W₁, hW₁, a₁, b₁, ha₁, hb₁, hab₁⟩ := h₁
  obtain ⟨W₂, hW₂, a₂, b₂, ha₂, hb₂, hab₂⟩ := h₂
  obtain ⟨W, hW, ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := hℱ.2 W₁ W₂ hW₁ hW₂
  -- W ⊆ W₁ via c₁ (c₁ ≫ W₁.arr = W.arr), W ⊆ W₂ via c₂.
  -- The two routes  W → q.U.dom  (c₁ ≫ b₁ and c₂ ≫ a₂) agree since q.U.arr is monic.
  have hmid : c₁ ≫ b₁ = c₂ ≫ a₂ := by
    apply q.U.monic
    calc (c₁ ≫ b₁) ≫ q.U.arr = c₁ ≫ (b₁ ≫ q.U.arr) := Cat.assoc _ _ _
      _ = c₁ ≫ W₁.arr := by rw [hb₁]
      _ = W.arr := hc₁
      _ = c₂ ≫ W₂.arr := hc₂.symm
      _ = c₂ ≫ (a₂ ≫ q.U.arr) := by rw [ha₂]
      _ = (c₂ ≫ a₂) ≫ q.U.arr := (Cat.assoc _ _ _).symm
  refine ⟨W, hW, c₁ ≫ a₁, c₂ ≫ b₂, ?_, ?_, ?_⟩
  · rw [Cat.assoc, ha₁]; exact hc₁
  · rw [Cat.assoc, hb₂]; exact hc₂
  · calc (c₁ ≫ a₁) ≫ p.map = c₁ ≫ (a₁ ≫ p.map) := Cat.assoc _ _ _
      _ = c₁ ≫ (b₁ ≫ q.map) := by rw [hab₁]
      _ = (c₁ ≫ b₁) ≫ q.map := (Cat.assoc _ _ _).symm
      _ = (c₂ ≫ a₂) ≫ q.map := by rw [hmid]
      _ = c₂ ≫ (a₂ ≫ q.map) := Cat.assoc _ _ _
      _ = c₂ ≫ (b₂ ≫ r.map) := by rw [hab₂]
      _ = (c₂ ≫ b₂) ≫ r.map := (Cat.assoc _ _ _).symm

/-- `T_ℱ(A)` — the colimit value: equivalence classes of `PrefilterMap ℱ A` under
    `PrefRel`.  Lives in `Type (max u v)`. -/
def TF (ℱ : (Subobject 𝒞 one) → Prop) (A : 𝒞) : Type (max u v) :=
  Quot (PrefRel ℱ (A := A))

/-- The class of a name `x : U → A` (`U ∈ ℱ`) as an element of `T_ℱ(A)`. -/
def TF.mk (ℱ : (Subobject 𝒞 one) → Prop) {A : 𝒞} (p : PrefilterMap ℱ A) : TF ℱ A :=
  Quot.mk _ p

/-- Functorial action: post-compose a name `U → A` with `f : A → B`.  Respects `PrefRel`. -/
def TF.map (ℱ : (Subobject 𝒞 one) → Prop) {A B : 𝒞} (f : A ⟶ B) : TF ℱ A → TF ℱ B :=
  Quot.lift (fun p => TF.mk ℱ ⟨p.U, p.hU, p.map ≫ f⟩) (by
    intro p q h
    obtain ⟨W, hW, a, b, ha, hb, hab⟩ := h
    apply Quot.sound
    exact ⟨W, hW, a, b, ha, hb, by
      show a ≫ (p.map ≫ f) = b ≫ (q.map ≫ f)
      rw [← Cat.assoc, ← Cat.assoc, hab]⟩)

@[simp] theorem TF.map_mk (ℱ : (Subobject 𝒞 one) → Prop) {A B : 𝒞} (f : A ⟶ B)
    (p : PrefilterMap ℱ A) :
    TF.map ℱ f (TF.mk ℱ p) = TF.mk ℱ ⟨p.U, p.hU, p.map ≫ f⟩ := rfl

/-- Functor law (identity): `T_ℱ(id) = id`.  Stated as a plain law rather than via the
    `Functor` typeclass because that class forces the source hom-universe `v` to equal the
    target hom-universe `max u v` (it would need `u ≤ v`); §1.55's representations dodge this
    by working at `Cat.{u}`.  At `v = u`, `TF_functor` below packages these into an instance. -/
theorem TF.map_id (ℱ : (Subobject 𝒞 one) → Prop) {A : 𝒞} (x : TF ℱ A) :
    TF.map ℱ (Cat.id A) x = x := by
  refine Quot.inductionOn x (fun p => ?_)
  show TF.map ℱ (Cat.id A) (TF.mk ℱ p) = TF.mk ℱ p
  simp [TF.map_mk, Cat.comp_id]

/-- Functor law (composition): `T_ℱ(f ≫ g) = T_ℱ(f) ≫ T_ℱ(g)`. -/
theorem TF.map_comp (ℱ : (Subobject 𝒞 one) → Prop) {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C)
    (x : TF ℱ A) :
    TF.map ℱ (f ≫ g) x = TF.map ℱ g (TF.map ℱ f x) := by
  refine Quot.inductionOn x (fun p => ?_)
  show TF.map ℱ (f ≫ g) (TF.mk ℱ p) = TF.map ℱ g (TF.map ℱ f (TF.mk ℱ p))
  simp [TF.map_mk, Cat.assoc]

/-- `T_ℱ : 𝒞 → 𝒮` is a set-valued functor, packaged at `Cat.{u} 𝒞` (so source and target
    hom-universes coincide, exactly as the §1.55 representations require). -/
instance TF_functor {𝒞 : Type u} [Cat.{u} 𝒞] [PreLogos 𝒞] (ℱ : (Subobject 𝒞 one) → Prop) :
    Functor (TF ℱ) where
  map f := TF.map ℱ f
  map_id A := by funext x; exact TF.map_id ℱ x
  map_comp f g := by funext x; exact TF.map_comp ℱ f g x

/-! ### §1.634  Recovering `PrefRel` from a `TF`-quotient equality (OBSTACLE 2 kernel)

  `TF ℱ A = Quot (PrefRel ℱ)` is a BARE `Quot`, not a `Quotient`/`Setoid`, so `Quot.exact`
  is unavailable.  We recover relatedness from `Quot.mk p = Quot.mk q` with the standard
  separating-invariant trick: for a fixed `q`, the predicate `fun p => PrefRel ℱ p q` is
  `PrefRel`-invariant in `p` (by `symm` + `trans`, the latter needing `IsPreFilter ℱ`), so it
  descends through `Quot.lift` to `TF ℱ A → Prop`; evaluating the descent at the two equal
  classes and using reflexivity at `q` yields `PrefRel ℱ p q`. -/

/-- The `PrefRel`-invariant predicate `relatesTo ℱ q` descended to `TF ℱ A`:
    `relatesTo ℱ q (TF.mk p) ↔ PrefRel ℱ p q`. -/
def TF.relatesTo (ℱ : (Subobject 𝒞 one) → Prop) (hℱ : IsPreFilter ℱ) {A : 𝒞}
    (q : PrefilterMap ℱ A) : TF ℱ A → Prop :=
  Quot.lift (fun p => PrefRel ℱ p q) (by
    intro p p' h
    apply propext
    constructor
    · exact fun hp => PrefRel.trans ℱ hℱ (PrefRel.symm ℱ h) hp
    · exact fun hp' => PrefRel.trans ℱ hℱ h hp')

@[simp] theorem TF.relatesTo_mk (ℱ : (Subobject 𝒞 one) → Prop) (hℱ : IsPreFilter ℱ) {A : 𝒞}
    (q p : PrefilterMap ℱ A) : TF.relatesTo ℱ hℱ q (TF.mk ℱ p) = PrefRel ℱ p q := rfl

/-- **OBSTACLE 2 kernel.**  Equal `TF`-classes are `PrefRel`-related. -/
theorem PrefRel_of_TF_eq (ℱ : (Subobject 𝒞 one) → Prop) (hℱ : IsPreFilter ℱ) {A : 𝒞}
    {p q : PrefilterMap ℱ A} (h : TF.mk ℱ p = TF.mk ℱ q) : PrefRel ℱ p q := by
  have hq : TF.relatesTo ℱ hℱ q (TF.mk ℱ q) = PrefRel ℱ q q := rfl
  have := hq ▸ (PrefRel.refl ℱ q)         -- relatesTo ℱ q (TF.mk q)
  rw [← h] at this                         -- relatesTo ℱ q (TF.mk p) = PrefRel p q
  exact this

/-- Post-composition with a MONIC `m` reflects `PrefRel`: a refinement-agreement of
    `p.map ≫ m` and `q.map ≫ m` cancels `m` to one of `p.map` and `q.map`.  (The inl/inl
    and inr/inr injectivity cases of `disjUnionCompare` on the `TF`-quotient.) -/
theorem PrefRel_reflect_monic (ℱ : (Subobject 𝒞 one) → Prop) {A B : 𝒞} {m : A ⟶ B}
    (hm : Monic m) {p q : PrefilterMap ℱ A}
    (h : PrefRel ℱ (⟨p.U, p.hU, p.map ≫ m⟩ : PrefilterMap ℱ B) ⟨q.U, q.hU, q.map ≫ m⟩) :
    PrefRel ℱ p q := by
  obtain ⟨W, hW, a, b, ha, hb, hab⟩ := h
  refine ⟨W, hW, a, b, ha, hb, hm _ _ ?_⟩
  -- a ≫ p.map ≫ m = b ≫ q.map ≫ m  (reassociate the given `a≫(p.map≫m)=b≫(q.map≫m)`).
  calc (a ≫ p.map) ≫ m = a ≫ (p.map ≫ m) := Cat.assoc _ _ _
    _ = b ≫ (q.map ≫ m) := hab
    _ = (b ≫ q.map) ≫ m := (Cat.assoc _ _ _).symm

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


/-! ## §1.634/§1.635(b) STEP A — the Boolean algebra of subterminators `Sub(1)`

  Freyd's §1.635 maximality argument runs in the Boolean algebra `ℬ` of complemented
  subobjects of `1`.  It needs two elementary facts about the underlying lattice `Sub(B)`:

  * DISTRIBUTIVITY  `S ∩ (U₁ ∪ U₂) ≤ (S∩U₁) ∪ (S∩U₂)`  (§1.612/§1.613), and
  * intersection-of-complemented-is-complemented (via De Morgan).

  The bridge is the PUSHFORWARD of a subobject of `S.dom` along the monic `S.arr : S.dom ↣ B`.
  Pushing forward `InverseImage S.arr X` recovers `Subobject.inter S X` *definitionally*
  (both have apex `pullback(S.arr, X.arr)`; the inter-arrow `π₁ ≫ S.arr` is exactly the
  pushforward of the inverse-image arrow `π₁`), so distributivity reduces to
  `PreLogos.invImage_preserves_union` plus monotonicity of pushforward. -/

/-- Pushforward of a subobject `X ⊆ S.dom` along a monic `m : S.dom ↣ B`: the subobject
    `⟨X.dom, X.arr ≫ m⟩ ⊆ B`.  (`X.arr ≫ m` is monic as a composite of monics.) -/
def pushforwardSub {S B : 𝒞} (m : S ⟶ B) (hm : Monic m) (X : Subobject 𝒞 S) :
    Subobject 𝒞 B :=
  ⟨X.dom, X.arr ≫ m, by
    intro W u v huv
    exact X.monic _ _ (hm _ _ (by simpa [Cat.assoc] using huv))⟩

/-- Pushforward is order-preserving: `X ≤ Y ⟹ pushforward m X ≤ pushforward m Y`.
    The witness `h : X.dom → Y.dom` with `h ≫ Y.arr = X.arr` also factors the pushed arrows. -/
theorem pushforwardSub_mono {S B : 𝒞} (m : S ⟶ B) (hm : Monic m) {X Y : Subobject 𝒞 S}
    (hXY : X.le Y) : (pushforwardSub m hm X).le (pushforwardSub m hm Y) := by
  obtain ⟨h, hh⟩ := hXY
  exact ⟨h, by show h ≫ (Y.arr ≫ m) = X.arr ≫ m; rw [← Cat.assoc, hh]⟩

/-- Pushforward distributes over binary unions (one inclusion):
    `pushforward m (P ∪ Q) ≤ pushforward m P ∪ pushforward m Q`.
    The union `P ∪ Q` is the image of `case P.arr Q.arr`; pushing along `m`, the composite
    `case P.arr Q.arr ≫ m = case (P.arr≫m) (Q.arr≫m)` is allowed by
    `pushforward m P ∪ pushforward m Q` (which is its image by `union_is_image`), and image
    minimality gives the inclusion. -/
theorem pushforwardSub_union_le [HasBinaryCoproducts 𝒞] {S B : 𝒞} (m : S ⟶ B) (hm : Monic m)
    (P Q : Subobject 𝒞 S) :
    (pushforwardSub m hm (HasSubobjectUnions.union P Q)).le
      (HasSubobjectUnions.union (pushforwardSub m hm P) (pushforwardSub m hm Q)) := by
  let RHS := HasSubobjectUnions.union (pushforwardSub m hm P) (pushforwardSub m hm Q)
  -- RHS is the image of `case ((pushforward P).arr) ((pushforward Q).arr)
  --                    = case (P.arr≫m) (Q.arr≫m)`.
  have hImg : IsImage (HasBinaryCoproducts.case (P.arr ≫ m) (Q.arr ≫ m)) RHS := union_is_image _ _
  obtain ⟨k, hk⟩ := hImg.1   -- k : coprod P.dom Q.dom → RHS.dom, k ≫ RHS.arr = case (P.arr≫m)(Q.arr≫m)
  -- Union inclusions of `P,Q` into `P∪Q`, whose copairing is a cover.
  obtain ⟨cP, hcP⟩ := HasSubobjectUnions.union_left P Q
  obtain ⟨cQ, hcQ⟩ := HasSubobjectUnions.union_right P Q
  have hcover : Cover (HasBinaryCoproducts.case cP cQ) := union_case_cover P Q hcP hcQ
  -- `case cP cQ ≫ (P∪Q).arr = case P.arr Q.arr`.
  have hcc_fac : HasBinaryCoproducts.case cP cQ ≫ (HasSubobjectUnions.union P Q).arr
      = HasBinaryCoproducts.case P.arr Q.arr := by
    refine HasBinaryCoproducts.case_uniq _ _ _ ?_ ?_
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inl, hcP]
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inr, hcQ]
  -- `case P.arr Q.arr ≫ m = case (P.arr≫m)(Q.arr≫m)`.
  have hcase_m : HasBinaryCoproducts.case P.arr Q.arr ≫ m
      = HasBinaryCoproducts.case (P.arr ≫ m) (Q.arr ≫ m) := by
    refine HasBinaryCoproducts.case_uniq _ _ _ ?_ ?_
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inl]
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inr]
  -- Square for cover ⊥ mono:  (case cP cQ) ≫ ((P∪Q).arr ≫ m) = k ≫ RHS.arr.
  have hsq : HasBinaryCoproducts.case cP cQ ≫ ((HasSubobjectUnions.union P Q).arr ≫ m)
      = k ≫ RHS.arr := by
    rw [← Cat.assoc, hcc_fac, hcase_m, hk]
  -- Diagonal fill-in gives `g : (P∪Q).dom → RHS.dom` with `g ≫ RHS.arr = (P∪Q).arr ≫ m`.
  obtain ⟨g, _, hg⟩ := cover_mono_diagonal hcover RHS.monic hsq
  exact ⟨g, hg⟩

/-- Pushforward and meet (one inclusion): `push m P ∩ push m Q ≤ push m (P ∩ Q)`.
    The two pushed legs are `P.arr ≫ m`, `Q.arr ≫ m`; their pullback's square, after cancelling
    the monic `m`, is a cone over `(P.arr, Q.arr)`, lifting into `P ∩ Q`.  That lift witnesses the
    `≤`. -/
theorem inter_pushforward_le {S B : 𝒞} (m : S ⟶ B) (hm : Monic m) (P Q : Subobject 𝒞 S) :
    (Subobject.inter (pushforwardSub m hm P) (pushforwardSub m hm Q)).le
      (pushforwardSub m hm (Subobject.inter P Q)) := by
  let pbF := HasPullbacks.has (pushforwardSub m hm P).arr (pushforwardSub m hm Q).arr
  -- pbF legs already land in (push P).dom = P.dom and (push Q).dom = Q.dom.
  -- pbF.w : pbF.π₁ ≫ (P.arr ≫ m) = pbF.π₂ ≫ (Q.arr ≫ m); cancel m ⟹ cone over (P.arr, Q.arr).
  have hcone : pbF.cone.π₁ ≫ P.arr = pbF.cone.π₂ ≫ Q.arr := by
    apply hm
    calc (pbF.cone.π₁ ≫ P.arr) ≫ m = pbF.cone.π₁ ≫ (pushforwardSub m hm P).arr := Cat.assoc _ _ _
      _ = pbF.cone.π₂ ≫ (pushforwardSub m hm Q).arr := pbF.cone.w
      _ = (pbF.cone.π₂ ≫ Q.arr) ≫ m := (Cat.assoc _ _ _).symm
  let pbI := HasPullbacks.has P.arr Q.arr
  let cI : Cone P.arr Q.arr := ⟨pbF.cone.pt, pbF.cone.π₁, pbF.cone.π₂, hcone⟩
  refine ⟨pbI.lift cI, ?_⟩
  -- Goal: pbI.lift cI ≫ (P∩Q).arr ≫ m = pbF.π₁ ≫ (push P).arr.
  have hlf : pbI.lift cI ≫ pbI.cone.π₁ = pbF.cone.π₁ := pbI.lift_fst cI
  calc pbI.lift cI ≫ ((Subobject.inter P Q).arr ≫ m)
      = pbI.lift cI ≫ ((pbI.cone.π₁ ≫ P.arr) ≫ m) := rfl
    _ = (pbI.lift cI ≫ pbI.cone.π₁) ≫ (P.arr ≫ m) := by simp only [Cat.assoc]
    _ = pbF.cone.π₁ ≫ (P.arr ≫ m) := by rw [hlf]
    _ = pbF.cone.π₁ ≫ (pushforwardSub m hm P).arr := rfl

/-- BRIDGE: `Subobject.inter S X = pushforward S.arr (InverseImage S.arr X)`.
    Both subobjects have apex `pullback(S.arr, X.arr)`; `inter` uses `π₁ ≫ S.arr` while the
    pushforward of `InverseImage S.arr X` (whose arrow is `π₁`) is again `π₁ ≫ S.arr`.  Equal up
    to `Subobject.le` both ways — here even definitionally, so a single `le` (identity witness)
    suffices in each direction. -/
theorem inter_eq_pushforward_invImage {B : 𝒞} (S X : Subobject 𝒞 B) :
    (Subobject.inter S X).le (pushforwardSub S.arr S.monic (InverseImage S.arr X))
    ∧ (pushforwardSub S.arr S.monic (InverseImage S.arr X)).le (Subobject.inter S X) :=
  ⟨⟨Cat.id _, by rw [Cat.id_comp]; rfl⟩, ⟨Cat.id _, by rw [Cat.id_comp]; rfl⟩⟩

/-- §1.612/§1.613 DISTRIBUTIVITY of `Sub(B)` (forward inequality):
    `S ∩ (U₁ ∪ U₂) ≤ (S ∩ U₁) ∪ (S ∩ U₂)`.
    PROOF: pass to `Sub(S.dom)` via the bridge `S ∩ X = pushforward S.arr (S.arr#X)`, where
    `PreLogos.invImage_preserves_union` gives `S.arr#(U₁∪U₂) ≤ S.arr#U₁ ∪ S.arr#U₂`; push
    that forward (`pushforwardSub_mono`, then `pushforwardSub_union_le`) and re-bridge. -/
theorem inter_union_le [HasBinaryCoproducts 𝒞] {B : 𝒞} (S U₁ U₂ : Subobject 𝒞 B) :
    (Subobject.inter S (HasSubobjectUnions.union U₁ U₂)).le
      (HasSubobjectUnions.union (Subobject.inter S U₁) (Subobject.inter S U₂)) := by
  -- (1) S ∩ (U₁∪U₂) = pushforward S.arr (S.arr#(U₁∪U₂)).
  refine Subobject.le_trans (inter_eq_pushforward_invImage S (HasSubobjectUnions.union U₁ U₂)).1 ?_
  -- (2) S.arr#(U₁∪U₂) ≤ S.arr#U₁ ∪ S.arr#U₂ in Sub(S.dom), pushed forward.
  refine Subobject.le_trans
    (pushforwardSub_mono S.arr S.monic
      (PreLogos.invImage_preserves_union S.arr U₁ U₂).1) ?_
  -- (3) pushforward (P ∪ Q) ≤ pushforward P ∪ pushforward Q.
  refine Subobject.le_trans (pushforwardSub_union_le S.arr S.monic _ _) ?_
  -- (4) re-bridge each summand: pushforward S.arr (S.arr#Uᵢ) ≤ S ∩ Uᵢ.
  exact HasSubobjectUnions.union_min _ _ _
    (Subobject.le_trans (inter_eq_pushforward_invImage S U₁).2
      (HasSubobjectUnions.union_left _ _))
    (Subobject.le_trans (inter_eq_pushforward_invImage S U₂).2
      (HasSubobjectUnions.union_right _ _))

/-! ### STEP A lattice helpers (monotonicity / commutativity of meet) -/

/-- Meet is monotone in both arguments. -/
theorem inter_mono {B : 𝒞} {S S' T T' : Subobject 𝒞 B}
    (hS : S.le S') (hT : T.le T') : (Subobject.inter S T).le (Subobject.inter S' T') :=
  Subobject.le_inter (Subobject.le_trans (Subobject.inter_le_left S T) hS)
                     (Subobject.le_trans (Subobject.inter_le_right S T) hT)

/-- `IsComplementedSub` is invariant under subobject equality (mutual `≤`): same complement
    `T₂` works.  (Mirror of `Complement.IsComplementedSub_congr`, inlined here because
    `Complement.lean` imports `S1_62`.) -/
theorem complementedSub_congr {A : 𝒞} {S T : Subobject 𝒞 A}
    (hST : S.le T) (hTS : T.le S) (hT : IsComplementedSub T) : IsComplementedSub S := by
  obtain ⟨T₂, hdisj, hcover⟩ := hT
  refine ⟨T₂, ?_, ?_⟩
  · exact Subobject.le_trans (inter_mono hST (Subobject.le_refl T₂)) hdisj
  · exact Subobject.le_trans hcover
      (HasSubobjectUnions.union_min _ _ _
        (Subobject.le_trans hTS (HasSubobjectUnions.union_left S T₂))
        (HasSubobjectUnions.union_right S T₂))

/-- Every subobject is below the entire subobject (whose arrow is `id`): witness `S.arr`. -/
theorem sub_le_entire {B : 𝒞} (S : Subobject 𝒞 B) : S.le (Subobject.entire B) := by
  refine ⟨S.arr, ?_⟩
  show S.arr ≫ (Subobject.entire B).arr = S.arr
  rw [show (Subobject.entire B).arr = Cat.id B from rfl, Cat.comp_id]

/-- Intersection of subobjects is symmetric up to `≤`: swapping the pullback legs gives
    `inter S T ≤ inter T S`.  Both intersections are pullbacks of the same cospan in the two
    orders; the comparison map is the canonical lift swapping `π₁` and `π₂`. -/
theorem inter_comm_le {B : 𝒞} (S T : Subobject 𝒞 B) :
    Subobject.le (Subobject.inter S T) (Subobject.inter T S) := by
  let pbST := HasPullbacks.has S.arr T.arr
  let pbTS := HasPullbacks.has T.arr S.arr
  let c : Cone T.arr S.arr := ⟨pbST.cone.pt, pbST.cone.π₂, pbST.cone.π₁, pbST.cone.w.symm⟩
  refine ⟨pbTS.lift c, ?_⟩
  show pbTS.lift c ≫ (pbTS.cone.π₁ ≫ T.arr) = pbST.cone.π₁ ≫ S.arr
  rw [← Cat.assoc, pbTS.lift_fst c]
  show pbST.cone.π₂ ≫ T.arr = pbST.cone.π₁ ≫ S.arr
  exact pbST.cone.w.symm

/-- Union of subobjects is symmetric up to `≤`: `union S T ≤ union T S` by minimality. -/
theorem union_comm_le {B : 𝒞} (S T : Subobject 𝒞 B) :
    Subobject.le (HasSubobjectUnions.union S T) (HasSubobjectUnions.union T S) :=
  HasSubobjectUnions.union_min S T _
    (HasSubobjectUnions.union_right T S) (HasSubobjectUnions.union_left T S)

/-- §1.634/§1.635(b) STEP A(ii): the meet of two COMPLEMENTED subterminators is complemented.
    If `U,V` have complements `Uᶜ,Vᶜ` (`U∩Uᶜ ≤ 0`, `⊤ ≤ U∪Uᶜ`, likewise `V`), then `U∩V` has
    complement `Uᶜ ∪ Vᶜ`:
      * DISJOINTNESS `(U∩V) ∩ (Uᶜ∪Vᶜ) ≤ 0`: distribute (`inter_union_le`) into
        `((U∩V)∩Uᶜ) ∪ ((U∩V)∩Vᶜ)`; the first `≤ U∩Uᶜ ≤ 0`, the second `≤ V∩Vᶜ ≤ 0`.
      * COVER `⊤ ≤ (U∩V) ∪ (Uᶜ∪Vᶜ)`: from `⊤ ≤ (U∪Uᶜ)∩(V∪Vᶜ)`, distribute twice; the only
        meet of two un-complemented pieces is `U∩V`, every other piece lands in `Uᶜ∪Vᶜ`. -/
theorem inter_complemented [HasBinaryCoproducts 𝒞] {B : 𝒞} {U V : Subobject 𝒞 B}
    (hU : IsComplementedSub U) (hV : IsComplementedSub V) :
    IsComplementedSub (Subobject.inter U V) := by
  obtain ⟨Uc, hUdisj, hUcov⟩ := hU
  obtain ⟨Vc, hVdisj, hVcov⟩ := hV
  refine ⟨HasSubobjectUnions.union Uc Vc, ?_, ?_⟩
  · -- DISJOINTNESS
    refine Subobject.le_trans (inter_union_le (Subobject.inter U V) Uc Vc) ?_
    refine HasSubobjectUnions.union_min _ _ _ ?_ ?_
    · -- (U∩V)∩Uc ≤ U∩Uc ≤ 0
      refine Subobject.le_trans ?_ hUdisj
      exact inter_mono (Subobject.inter_le_left U V) (Subobject.le_refl Uc)
    · -- (U∩V)∩Vc ≤ V∩Vc ≤ 0
      refine Subobject.le_trans ?_ hVdisj
      exact inter_mono (Subobject.inter_le_right U V) (Subobject.le_refl Vc)
  · -- COVER:  ⊤ ≤ (U∪Uc) ∩ (V∪Vc) ≤ … ≤ (U∩V) ∪ (Uc∪Vc).
    -- Abbreviate the complement union  W := Uc ∪ Vc.
    let W := HasSubobjectUnions.union Uc Vc
    -- ⊤ ≤ (U∪Uc) ∩ (V∪Vc).
    have htop : (Subobject.entire B).le
        (Subobject.inter (HasSubobjectUnions.union U Uc) (HasSubobjectUnions.union V Vc)) :=
      Subobject.le_inter hUcov hVcov
    refine Subobject.le_trans htop ?_
    -- Distribute over the FIRST union (after commuting):
    --   (U∪Uc)∩(V∪Vc) ≤ (V∪Vc)∩(U∪Uc) ≤ ((V∪Vc)∩U) ∪ ((V∪Vc)∩Uc).
    refine Subobject.le_trans (Subobject.le_trans
        (Subobject.le_inter (Subobject.inter_le_right _ _) (Subobject.inter_le_left _ _))
        (inter_union_le (HasSubobjectUnions.union V Vc) U Uc)) ?_
    -- Now bound each of the two pieces by  (U∩V) ∪ W.
    refine HasSubobjectUnions.union_min _ _ _ ?_ ?_
    · -- (V∪Vc)∩U ≤ U∩(V∪Vc) ≤ (U∩V) ∪ (U∩Vc) ≤ (U∩V) ∪ W.
      refine Subobject.le_trans
        (Subobject.le_inter (Subobject.inter_le_right _ _) (Subobject.inter_le_left _ _)) ?_
      refine Subobject.le_trans (inter_union_le U V Vc) ?_
      refine HasSubobjectUnions.union_min _ _ _ ?_ ?_
      · -- U∩V ≤ (U∩V) ∪ W
        exact HasSubobjectUnions.union_left _ _
      · -- U∩Vc ≤ Vc ≤ W ≤ (U∩V) ∪ W
        refine Subobject.le_trans (Subobject.inter_le_right U Vc) ?_
        exact Subobject.le_trans (HasSubobjectUnions.union_right Uc Vc)
          (HasSubobjectUnions.union_right (Subobject.inter U V) W)
    · -- (V∪Vc)∩Uc ≤ Uc ≤ W ≤ (U∩V) ∪ W.
      refine Subobject.le_trans (Subobject.inter_le_right (HasSubobjectUnions.union V Vc) Uc) ?_
      exact Subobject.le_trans (HasSubobjectUnions.union_left Uc Vc)
        (HasSubobjectUnions.union_right (Subobject.inter U V) W)

-- BOOK §1.634: If A is a pre-logos then T_ℱ preserves disjoint unions iff
--   (0 ∉ ℱ) and (U₁+U₂ ∈ ℱ implies U₁ ∈ ℱ or U₂ ∈ ℱ).
-- LANDED (below, after `IsFilter`):
--   * The COLIMIT functor `TF ℱ A = colim_{U∈ℱ} Hom(U,A)` (quotient of `PrefilterMap` by
--     `PrefRel`), with functoriality (`TF.map_id`, `TF.map_comp`, `TF_functor`).
--   * `PreservesDisjointUnions T` predicate (`disjUnionCompare` bijective) and the
--     §1.625 `SetRepOfPreLogos` packaging "rep-of-regular + preserves disjoint unions".
--   * The §1.634 BECAUSE first sentence `0 ∉ ℱ ⇔ T_ℱ(0) = ∅`
--     (`TF_coterminator_empty` ⇐ / `TF_coterminator_nonempty` ⇒).
--   * The §1.634 membership condition `UnionPrime ℱ`.
-- (⟸) DONE — `preservesDisjointUnions_of_ultrafilter`:  an ULTRA-FILTER `F̂` (proper + all members
--   complemented + maximal) gives a union-preserving `T_F̂`.  Built from the two OBSTACLE kernels,
--   both now CLOSED (section `DisjointUnionPreservation`, at `Cat.{u}`):
--     • OBSTACLE 2 (injectivity, `disjUnionCompare_injective`, needs `IsProperFilter`): the bare
--       `Quot (PrefRel)` has no `Quot.exact`, so `PrefRel_of_TF_eq` recovers relatedness via the
--       SEPARATING-INVARIANT `TF.relatesTo` (`Quot.lift` of `fun p => PrefRel p q`, invariant by
--       symm+trans).  inl/inl, inr/inr cancel the monic injection (`PrefRel_reflect_monic`); the
--       cross inl/inr forces a common refinement `W∈ℱ` factoring through both injections, hence
--       `W ≤ 0` (`coprod_inl_inr_disjoint_elt` + `le_bottom_of_map_to_bottom`), contra properness.
--     • OBSTACLE 1 (surjectivity, `disjUnionCompare_surjective`, needs `UnionPrime` + complemented
--       up-closure): the witness-exposing `decompose_witnesses` splits a name `(U,h:U.dom→A₁+A₂)`
--       into `U₁=h#inl, U₂=h#inr ⊆ U.dom` with cover/disjoint/factorizations; pushed to `Sub(1)`
--       (`pushforwardSub`, `inter_pushforward_le`, `pushforwardSub_bottom_le`) the pair `V₁,V₂`
--       satisfies `V₁∩V₂≤0` and `V₁∪V₂ ≅ U ∈ ℱ` (complemented via `complementedSub_congr`), so up-
--       closure puts `V₁∪V₂∈ℱ` and `UnionPrime` (= `ultrafilter_unionPrime`) puts `V₁∈ℱ ∨ V₂∈ℱ`.
--   (⟹) part 1 DONE — `notMem_zero_of_injective`: injectivity forces `0 ∉ ℱ` (else the two zero-named
--   elements of `T(A₁),T(A₂)` collide under the comparison but carry distinct sum tags).
--   (⟹) part 2 RESIDUAL — `UnionPrime`'s membership clause from surjectivity: given `U₁∩U₂≤0` and
--   `U₁∪U₂∈ℱ`, build the complemented pair `Q₁=K#U₁,Q₂=K#U₂ ⊆ K.dom` (`K=U₁∪U₂`), name the iso
--   `K.dom ≅ Q₁.dom+Q₂.dom`, and read off `W ≤ Uᵢ` from the surjectivity preimage.  Needs a
--   WITNESS-EXPOSING `complementedSub_iso_coproduct` (`inl≫h⁻¹ = Q₁.arr`) — the dual of
--   `decompose_witnesses` — plus complemented up-closure (`complemented_of_disjoint_half`).  Not yet
--   built; this is the only open piece of the §1.634 iff (the ⟸ keystone for §1.635 is DONE).

-- BOOK §1.635: If F̂ is an ultra-filter in the boolean algebra of complemented
-- subterminators, then T_F̂ is a representation of pre-logoi (union-preserving).
-- LANDED (below): `IsProperFilter`/`IsUltraFilter` predicates; the standard ultra-filter
--   algebra `ultrafilter_isFilter` (maximal proper ⟹ up-closed) and `ultrafilter_inter_closed`
--   (closed under meet) — Freyd's "an ultra-filter is easily seen to be a filter, hence closed
--   under intersection".  The §1.625 conclusion shape is `SetRepOfPreLogos`.
--   (a) ULTRA-FILTER EXISTENCE: **DONE** — `exists_ultrafilter_extending` (below).  Every proper
--       complemented pre-filter extends to an `IsUltraFilter`, via the now-generic mathlib-free
--       `Freyd.WO.zorn` (Bourbaki–Witt tower in `Fredy/WellOrdering.lean`, axiom-clean
--       [propext, Classical.choice, Quot.sound]) applied to the poset `ExtFilter ℱ₀` of proper
--       complemented pre-filters extending `ℱ₀`; the chain-upper-bound is the union of the chain.
--   (b) `UnionPrime F̂` for `F̂` ultra: **DONE** — `ultrafilter_unionPrime` (Freyd's maximality
--       argument, STEP C).  Uses the now-landed STEP A Boolean development:
--         (i)  DISTRIBUTIVITY `S ∩ (U₁∪U₂) ≤ (S∩U₁)∪(S∩U₂)`: **DONE** `inter_union_le`, via the
--              pushforward bridge `Subobject.inter S X = pushforwardSub S.arr (InverseImage S.arr X)`
--              (`inter_eq_pushforward_invImage`) + `(PreLogos.invImage_preserves_union S.arr ..).1`
--              + `pushforwardSub_mono`/`pushforwardSub_union_le` (the latter via the §1.56
--              cover⊥mono diagonal `cover_mono_diagonal`).
--         (ii) INTERSECTION OF COMPLEMENTED IS COMPLEMENTED: **DONE** `inter_complemented`
--              (complement `Uᶜ∪Vᶜ`, De Morgan via (i)).  Plus `complemented_of_disjoint_half`.
--   (c) `T_F̂` IS A REPRESENTATION OF PRE-LOGOI: **DONE** — `setRepOfPreLogos_of_ultrafilter`
--       (and the core `preservesDisjointUnions_of_ultrafilter`).  Combines (a)/(b) with the
--       §1.634 (⟸) iff: `ultrafilter_unionPrime F̂` + `ultrafilter_isFilter` up-closure feed the
--       now-closed `disjUnionCompare` bijectivity, giving `PreservesDisjointUnions (TF F̂)`, packaged
--       in the §1.625 `SetRepOfPreLogos` shape ("rep-of-regular + preserves disjoint unions").
-- The faithful-representation half (`SeparatesMaps`) is `prelogos_representation_theorem`.

-- BOOK §1.636: Any Horn sentence in the predicates of pre-logoi that holds for the
-- category of sets holds for all positive pre-logoi.
-- INFRA-BLOCKED. §1.636 is a DIFFERENT Horn metatheorem from §1.444 (Horn.lean):
--   - §1.444 Horn.lean covers Cartesian predicates (terminator / product / equalizer).
--   - §1.636 covers PRE-LOGOS predicates: additionally `image`, `disjoint coproduct`,
--     `zero object`, `union of subobjects` — none of these appear in `Freyd.Horn.Atom`.
-- (The between-pre-logoi `PreLogosFunctor` predicate — item (4) of the assembly — already exists
--  in S1_61 (`Freyd.PreLogosFunctor`): preserves union + bottom on top of Cartesian+mono.)
-- To formalize §1.636 one needs:
--   (1) An extended `PreLogosAtom` inductive adding `image`, `disjointCoprod`, `zero`,
--       `union` constructors with well-typed morphism variables.
--   (2) `HoldsInPreLogos 𝒞 φ` semantics interpreting those atoms via the pre-logos
--       operations (`HasImages`, `DisjointBinaryCoproduct`, `PreLogos.bottom`, etc.).
--   (3) Preservation theorems for each new predicate under `T_F̂` — the functional core
--       of §1.634–1.635 (INFRA-BLOCKED above).
--   (4) Reflection theorems (collective faithfulness for the extended language via
--       `prelogos_representation_theorem`).
-- Transfer route: once (1)–(4) are in place, the proof follows §1.444's pattern:
-- for each `i`, `pushEnv i ρ` preserves all pre-logos predicates by (3); truth-for-Set
-- gives the conclusion; reflection (4) pulls it back.  But (1)–(3) are substantial new
-- infra, not a one-liner extension of `Horn.lean`.

/-- FILTER in a subobject lattice: up-closed pre-filter (§1.634). -/
def IsFilter (ℱ : (Subobject 𝒞 one) → Prop) : Prop :=
  IsPreFilter ℱ ∧ ∀ (U V : Subobject 𝒞 one), ℱ U → Subobject.le U V → ℱ V

/-! ### §1.634/§1.635 The ultra-filter layer

  The subobjects of `1` carry the order `Subobject.le`; the *complemented* ones
  (`IsComplementedSub`) form a distributive lattice with `0 = PreLogos.bottom 1` and meet
  `Subobject.inter`, complements — Freyd's BOOLEAN ALGEBRA `ℬ` of complemented
  subterminators (§1.635).  A pre-filter is PROPER when it omits `0`; an ULTRA-FILTER is a
  maximal proper pre-filter.  All predicates below are on `Subobject 𝒞 one → Prop`. -/

/-- `0` (the bottom subterminator) — `PreLogos.bottom 1`.  `0 ∈ ℱ` means `Zero ∈ ℱ`. -/
abbrev Zero1 : Subobject 𝒞 one := PreLogos.bottom one

/-- A pre-filter is PROPER if no member is below `0` (equivalently `0 ∉ ℱ`, stated in the
    order-robust form `¬ ∃ U ∈ ℱ, U ≤ 0` so it is stable under the iso-ambiguity of raw
    subobjects). -/
def IsProperFilter (ℱ : (Subobject 𝒞 one) → Prop) : Prop :=
  IsPreFilter ℱ ∧ ¬ ∃ U, ℱ U ∧ Subobject.le U Zero1

/-- §1.635 ULTRA-FILTER: a maximal proper pre-filter in the Boolean algebra of complemented
    subterminators.  `ℱ` is a proper pre-filter all of whose members are complemented, and any
    proper pre-filter (of complemented subterminators) extending `ℱ` equals `ℱ`. -/
def IsUltraFilter (ℱ : (Subobject 𝒞 one) → Prop) : Prop :=
  IsProperFilter ℱ ∧ (∀ U, ℱ U → IsComplementedSub U) ∧
    ∀ (𝒢 : (Subobject 𝒞 one) → Prop), IsProperFilter 𝒢 → (∀ U, 𝒢 U → IsComplementedSub U) →
      (∀ U, ℱ U → 𝒢 U) → ∀ U, 𝒢 U → ℱ U

/-- §1.634 filter membership condition that characterises union-preservation of `T_ℱ`:
    `0 ∉ ℱ`, and a disjoint complemented union `U₁ ∪ U₂ ∈ ℱ` forces `U₁ ∈ ℱ` or `U₂ ∈ ℱ`.
    (The union is taken in `Subobject 𝒞 one`; `U₁, U₂` are the two halves of a complemented
    pair, i.e. `U₁ ∩ U₂ = 0`.) -/
def UnionPrime (ℱ : (Subobject 𝒞 one) → Prop) : Prop :=
  ¬ ℱ Zero1 ∧
    ∀ (U₁ U₂ : Subobject 𝒞 one),
      Subobject.le (Subobject.inter U₁ U₂) Zero1 →
      ℱ (HasSubobjectUnions.union U₁ U₂) → ℱ U₁ ∨ ℱ U₂

/-! ### §1.634/§1.625  Union-preservation of a set-valued representation

  A representation `T : 𝒞 → 𝒮` of regular categories preserves DISJOINT UNIONS (§1.625) iff
  for every disjoint complemented pair realising `A ≅ A₁ + A₂` the two injection images in
  `T A` are disjoint and jointly cover `T A` (and each injection is injective).  This is the
  Set-theoretic content of "`T(A₁+A₂) = T(A₁) ⊔ T(A₂)`" — a representation of pre-logoi is
  exactly a representation of regular categories that is additionally union-preserving. -/

/-- The canonical comparison `T A₁ ⊔ T A₂ → T(A₁+A₂)` of a SET-valued functor `T`,
    namely `[T(inl), T(inr)]` on the disjoint sum of the two stalks. -/
def disjUnionCompare (T : 𝒞 → Type v) [hT : Functor T]
    [HasBinaryCoproducts 𝒞] (A₁ A₂ : 𝒞) :
    (T A₁) ⊕ (T A₂) → T (HasBinaryCoproducts.coprod A₁ A₂) :=
  fun s => s.elim (fun x => hT.map (HasBinaryCoproducts.inl) x)
                  (fun y => hT.map (HasBinaryCoproducts.inr) y)

/-- §1.625  `T : 𝒞 → 𝒮` PRESERVES DISJOINT UNIONS: for every binary coproduct the canonical
    comparison `T A₁ ⊔ T A₂ → T(A₁+A₂)` is a bijection (Set-level
    "`T(A₁+A₂) = T A₁ ⊔ T A₂`").  A representation of regular categories that preserves
    disjoint unions is a REPRESENTATION OF PRE-LOGOI. -/
def PreservesDisjointUnions (T : 𝒞 → Type v) [Functor T]
    [HasBinaryCoproducts 𝒞] : Prop :=
  ∀ (A₁ A₂ : 𝒞),
    Function.Injective (disjUnionCompare T A₁ A₂) ∧ Function.Surjective (disjUnionCompare T A₁ A₂)

/-- §1.625/§1.635 SET-VALUED REPRESENTATION OF PRE-LOGOI.  A set-valued functor
    `T : 𝒞 → 𝒮` is a representation of pre-logoi iff it is a representation of regular
    categories that also preserves disjoint unions.  (The §1.61 class `PreLogosFunctor` is the
    between-pre-logoi version; this `SetRepOfPreLogos` is its set-valued analogue, the form the
    representation theorem §1.635 actually produces, since the target `𝒮 = Type v` is not
    instanced as a `PreLogos` object in this repo.)

    The regular-representation half (`repReg`) is supplied as an abstract predicate: it is the
    conjunction of preservation of binary products, equalizers and covers, which for `T_ℱ` is
    the §1.634 fact "`T_ℱ` preserves finite products and equalizers, and preserves covers when
    the elements of `ℱ` are projective".  `SetRepOfPreLogos` adds the missing §1.635 ingredient
    — disjoint-union preservation — on top.  `repReg` is the regular-representation predicate
    (preserves products, equalizers, covers) carried as a parameter. -/
def SetRepOfPreLogos (T : 𝒞 → Type v) [Functor T] [HasBinaryCoproducts 𝒞]
    (repReg : Prop) : Prop :=
  repReg ∧ PreservesDisjointUnions T

/-! ### §1.635  Algebra of ultra-filters

  An ultra-filter in the Boolean algebra of complemented subterminators is automatically a
  filter (up-closed), hence — `ℬ` being a lattice — closed under meet.  These are the
  "standard facts" Freyd invokes ("An ultra-filter is easily seen to be a filter, hence
  closed under intersection").  We prove the up-closure half here from maximality. -/

/-- An ULTRA-FILTER is a FILTER: it is up-closed within the complemented subterminators.
    PROOF (Freyd): the up-closure `𝒢 = {W complemented | ∃ S ∈ ℱ, S ≤ W}` is a proper
    pre-filter extending `ℱ`; by maximality `𝒢 = ℱ`, and `U ≤ V`, `U ∈ ℱ` puts `V ∈ 𝒢 = ℱ`. -/
theorem ultrafilter_isFilter (ℱ : (Subobject 𝒞 one) → Prop) (hU : IsUltraFilter ℱ) :
    ∀ (U V : Subobject 𝒞 one), ℱ U → IsComplementedSub V → Subobject.le U V → ℱ V := by
  obtain ⟨⟨hpre, h0⟩, hcomp, hmax⟩ := hU
  intro U V hUmem hVcomp hUV
  -- 𝒢 = the up-closure of ℱ within complemented subterminators.
  let 𝒢 : (Subobject 𝒞 one) → Prop := fun W => IsComplementedSub W ∧ ∃ S, ℱ S ∧ Subobject.le S W
  -- 𝒢 is a pre-filter: ↓-directed using directedness of ℱ on the witnesses.
  have h𝒢pre : IsPreFilter 𝒢 := by
    obtain ⟨S₀, hS₀⟩ := hpre.1
    refine ⟨⟨S₀, hcomp S₀ hS₀, S₀, hS₀, Subobject.le_refl S₀⟩, ?_⟩
    rintro W₁ W₂ ⟨_, S₁, hS₁, hS₁W₁⟩ ⟨_, S₂, hS₂, hS₂W₂⟩
    obtain ⟨T, hT, hTS₁, hTS₂⟩ := hpre.2 S₁ S₂ hS₁ hS₂
    -- T ∈ ℱ ⊆ 𝒢, and T ≤ S₁ ≤ W₁, T ≤ S₂ ≤ W₂.
    exact ⟨T, ⟨hcomp T hT, T, hT, Subobject.le_refl T⟩,
      Subobject.le_trans hTS₁ hS₁W₁, Subobject.le_trans hTS₂ hS₂W₂⟩
  -- 𝒢 is proper: a member ≤ 0 yields a witness S ∈ ℱ with S ≤ 0, contradicting properness of ℱ.
  have h𝒢prop : ¬ ∃ W, 𝒢 W ∧ Subobject.le W Zero1 := by
    rintro ⟨W, ⟨_, S, hS, hSW⟩, hW0⟩
    exact h0 ⟨S, hS, Subobject.le_trans hSW hW0⟩
  -- ℱ ⊆ 𝒢 (every member is above itself), all 𝒢-members complemented; maximality ⟹ 𝒢 ⊆ ℱ.
  have hℱ𝒢 : ∀ W, ℱ W → 𝒢 W := fun W hW => ⟨hcomp W hW, W, hW, Subobject.le_refl W⟩
  exact hmax 𝒢 ⟨h𝒢pre, h𝒢prop⟩ (fun W hW => hW.1) hℱ𝒢 V ⟨hVcomp, U, hUmem, hUV⟩

/-- An ULTRA-FILTER is closed under MEET (intersection): if `U, V ∈ ℱ` and their meet
    `U ∩ V` is complemented (which it is in the Boolean algebra `ℬ`), then `U ∩ V ∈ ℱ`.
    PROOF: ↓-directedness gives `T ∈ ℱ` with `T ≤ U`, `T ≤ V`, hence `T ≤ U ∩ V`
    (`Subobject.le_inter`); up-closure (`ultrafilter_isFilter`) lifts membership to `U ∩ V`.
    The complementedness of `U ∩ V` is the only non-elementary input (De Morgan in `ℬ`), so it
    is taken as a hypothesis here rather than re-deriving the Boolean-algebra structure. -/
theorem ultrafilter_inter_closed (ℱ : (Subobject 𝒞 one) → Prop) (hU : IsUltraFilter ℱ)
    (U V : Subobject 𝒞 one) (hUmem : ℱ U) (hVmem : ℱ V)
    (hcompInter : IsComplementedSub (Subobject.inter U V)) :
    ℱ (Subobject.inter U V) := by
  have hpre : IsPreFilter ℱ := hU.1.1
  obtain ⟨T, hT, hTU, hTV⟩ := hpre.2 U V hUmem hVmem
  exact ultrafilter_isFilter ℱ hU T (Subobject.inter U V) hT hcompInter
    (Subobject.le_inter hTU hTV)

/-- §1.634 (BECAUSE, first sentence): `0 ∉ ℱ` is equivalent with `T_ℱ(0) = ∅`.

  Here `0` is the coterminator object of the pre-logos.  An element of `T_ℱ(0)` is named by
  some `x : U.dom → 0` with `U ∈ ℱ`; any map into the (strict) coterminator is an iso
  (`any_map_to_zero_is_iso`), so `U.dom ≅ 0 ≅ (PreLogos.bottom 1).dom`, and since `1` is
  terminal that iso *is* a witness `U ≤ 0` in `Sub(1)`.  Properness (`0 ∉ ℱ`, i.e. no member
  `≤ 0`) then excludes `U`, so `T_ℱ(0)` is empty. -/
theorem TF_coterminator_empty (ℱ : (Subobject 𝒞 one) → Prop) (hprop : ¬ ∃ U, ℱ U ∧ Subobject.le U Zero1) :
    TF ℱ (minimal_subobject_of_one_is_coterminator (inferInstance : PreLogos 𝒞)).zero → False := by
  intro t
  refine Quot.inductionOn t (fun p => ?_)
  -- `0 = Zero1.dom` definitionally, so `p.map : p.U.dom → Zero1.dom` IS a witness `p.U ≤ Zero1`
  -- once composed with `Zero1.arr`; the triangle holds since `1` is terminal (`term_uniq`).
  have hle : Subobject.le p.U Zero1 := ⟨p.map, term_uniq _ _⟩
  exact hprop ⟨p.U, p.hU, hle⟩

/-- §1.634 converse: if `0 ∈ ℱ` (the literal bottom subterminator) then `T_ℱ(0) ≠ ∅` — the
    identity name `Zero1 → 0` (recall `0 = Zero1.dom`) is an element.  Together with
    `TF_coterminator_empty` this gives Freyd's equivalence `0 ∉ ℱ ⇔ T_ℱ(0) = ∅`. -/
def TF_coterminator_nonempty (ℱ : (Subobject 𝒞 one) → Prop) (h0 : ℱ Zero1) :
    TF ℱ (minimal_subobject_of_one_is_coterminator (inferInstance : PreLogos 𝒞)).zero :=
  TF.mk ℱ ⟨Zero1, h0, Cat.id _⟩

/-- §1.635 (GAP 3, part a): a PROPER pre-filter omits the literal bottom `0 ∈ Sub(1)`.
    Immediate from properness (`¬ ∃ U ∈ ℱ, U ≤ 0`) since `0 ≤ 0` (`Subobject.le_refl`). -/
theorem properFilter_not_zero (ℱ : (Subobject 𝒞 one) → Prop) (hprop : IsProperFilter ℱ) :
    ¬ ℱ Zero1 := fun h0 => hprop.2 ⟨Zero1, h0, Subobject.le_refl _⟩

/-! ### §1.635(b)  STEP C — `UnionPrime` of every ultra-filter

  If `U₁∩U₂ ≤ 0` and `U₁∪U₂ ∈ F̂` then `U₁ ∈ F̂` or `U₂ ∈ F̂`.  Freyd's maximality argument:
  if `U₁ ∉ F̂`, the up-closure `𝒢 = {W complemented | ∃ S∈F̂, S∩U₁ᶜ ≤ W}` (using the complement
  `U₁ᶜ`) is a proper complemented pre-filter strictly above `F̂` that contains `U₂`; maximality
  collapses `𝒢 = F̂`, forcing `U₂ ∈ F̂`.  Distributivity (`inter_union_le`) and
  intersection-of-complemented (`inter_complemented`) from STEP A power the filter axioms. -/

/-- A disjoint half of a complemented union is itself complemented:
    if `U₁∩U₂ ≤ 0` and `K = U₁∪U₂` is complemented with complement `Kᶜ`, then `U₁` is
    complemented with complement `U₂ ∪ Kᶜ`.
      * `U₁ ∩ (U₂∪Kᶜ) ≤ (U₁∩U₂) ∪ (U₁∩Kᶜ) ≤ 0 ∪ (K∩Kᶜ) ≤ 0` (`U₁ ≤ K`),
      * `⊤ ≤ K ∪ Kᶜ = (U₁∪U₂) ∪ Kᶜ = U₁ ∪ (U₂∪Kᶜ)`. -/
theorem complemented_of_disjoint_half [HasBinaryCoproducts 𝒞] {U₁ U₂ : Subobject 𝒞 one}
    (hdisj : Subobject.le (Subobject.inter U₁ U₂) Zero1)
    (hKcomp : IsComplementedSub (HasSubobjectUnions.union U₁ U₂)) :
    IsComplementedSub U₁ := by
  obtain ⟨Kc, hKdisj, hKcov⟩ := hKcomp
  refine ⟨HasSubobjectUnions.union U₂ Kc, ?_, ?_⟩
  · -- U₁ ∩ (U₂ ∪ Kc) ≤ (U₁∩U₂) ∪ (U₁∩Kc) ≤ 0.
    refine Subobject.le_trans (inter_union_le U₁ U₂ Kc) ?_
    refine HasSubobjectUnions.union_min _ _ _ hdisj ?_
    -- U₁ ∩ Kc ≤ (U₁∪U₂) ∩ Kc = K ∩ Kc ≤ 0.
    refine Subobject.le_trans ?_ hKdisj
    exact inter_mono (HasSubobjectUnions.union_left U₁ U₂) (Subobject.le_refl Kc)
  · -- ⊤ ≤ (U₁∪U₂) ∪ Kc ≤ U₁ ∪ (U₂ ∪ Kc).
    refine Subobject.le_trans hKcov ?_
    refine HasSubobjectUnions.union_min _ _ _ ?_ ?_
    · -- U₁∪U₂ ≤ U₁ ∪ (U₂∪Kc)
      refine HasSubobjectUnions.union_min _ _ _ (HasSubobjectUnions.union_left _ _) ?_
      exact Subobject.le_trans (HasSubobjectUnions.union_left U₂ Kc)
        (HasSubobjectUnions.union_right U₁ (HasSubobjectUnions.union U₂ Kc))
    · -- Kc ≤ U₂∪Kc ≤ U₁ ∪ (U₂∪Kc)
      exact Subobject.le_trans (HasSubobjectUnions.union_right U₂ Kc)
        (HasSubobjectUnions.union_right U₁ (HasSubobjectUnions.union U₂ Kc))

/-- §1.635(b): every ULTRA-FILTER is `UnionPrime`.  (Freyd's maximality argument; STEP C.) -/
theorem ultrafilter_unionPrime [HasBinaryCoproducts 𝒞] (Fhat : (Subobject 𝒞 one) → Prop)
    (hU : IsUltraFilter Fhat) : UnionPrime Fhat := by
  have hUF := hU
  obtain ⟨hprop, hcompAll, hmax⟩ := hU
  refine ⟨properFilter_not_zero Fhat hprop, ?_⟩
  intro U₁ U₂ hdisj hKmem
  by_cases hU1 : Fhat U₁
  · exact Or.inl hU1
  · refine Or.inr ?_
    -- K := U₁∪U₂ ∈ F̂; it is complemented, with complement Kc.
    obtain ⟨Kc, hKdisj, hKcov⟩ := hcompAll _ hKmem
    -- complement of U₁:  U₁ᶜ := U₂ ∪ Kc.  Disjointness/cover proved directly (cf.
    -- `complemented_of_disjoint_half`, inlined here so `U1c` stays the literal `U₂∪Kc`).
    let U1c : Subobject 𝒞 one := HasSubobjectUnions.union U₂ Kc
    have hU1disj : Subobject.le (Subobject.inter U₁ U1c) Zero1 := by
      refine Subobject.le_trans (inter_union_le U₁ U₂ Kc) ?_
      refine HasSubobjectUnions.union_min _ _ _ hdisj ?_
      refine Subobject.le_trans ?_ hKdisj
      exact inter_mono (HasSubobjectUnions.union_left U₁ U₂) (Subobject.le_refl Kc)
    have hU1cov : (Subobject.entire one).le (HasSubobjectUnions.union U₁ U1c) := by
      refine Subobject.le_trans hKcov ?_
      refine HasSubobjectUnions.union_min _ _ _ ?_ ?_
      · refine HasSubobjectUnions.union_min _ _ _ (HasSubobjectUnions.union_left _ _) ?_
        exact Subobject.le_trans (HasSubobjectUnions.union_left U₂ Kc)
          (HasSubobjectUnions.union_right U₁ U1c)
      · exact Subobject.le_trans (HasSubobjectUnions.union_right U₂ Kc)
          (HasSubobjectUnions.union_right U₁ U1c)
    -- Freyd's family 𝒢 = up-closure of F̂ ∩ U1c.
    let 𝒢 : (Subobject 𝒞 one) → Prop :=
      fun W => IsComplementedSub W ∧ ∃ S, Fhat S ∧ Subobject.le (Subobject.inter S U1c) W
    have hpreF : IsPreFilter Fhat := hprop.1
    -- (1) 𝒢 is a pre-filter.
    have h𝒢pre : IsPreFilter 𝒢 := by
      refine ⟨⟨HasSubobjectUnions.union U₁ U₂, hcompAll _ hKmem,
        HasSubobjectUnions.union U₁ U₂, hKmem, Subobject.inter_le_left _ _⟩, ?_⟩
      rintro W₁ W₂ ⟨hW₁c, S₁, hS₁, hS₁W₁⟩ ⟨hW₂c, S₂, hS₂, hS₂W₂⟩
      -- common refinement: T ≤ S₁,S₂ with T ∈ Fhat (directed); the witness is T ∩ U1c.
      obtain ⟨T, hT, hTS₁, hTS₂⟩ := hpreF.2 S₁ S₂ hS₁ hS₂
      have hU1cc : IsComplementedSub U1c := ⟨U₁, Subobject.le_trans (inter_comm_le _ _) hU1disj,
        Subobject.le_trans hU1cov (union_comm_le U₁ U1c)⟩
      refine ⟨Subobject.inter T U1c,
        ⟨inter_complemented (hcompAll _ hT) hU1cc, T, hT, Subobject.le_refl _⟩, ?_, ?_⟩
      · -- T∩U1c ≤ S₁∩U1c ≤ W₁
        exact Subobject.le_trans (inter_mono hTS₁ (Subobject.le_refl U1c)) hS₁W₁
      · -- T∩U1c ≤ S₂∩U1c ≤ W₂
        exact Subobject.le_trans (inter_mono hTS₂ (Subobject.le_refl U1c)) hS₂W₂
    -- (2) all members complemented (by construction).
    have h𝒢comp : ∀ W, 𝒢 W → IsComplementedSub W := fun W hW => hW.1
    -- (3) 𝒢 is proper: a member ≤ 0 forces U₁ ∈ F̂, contradicting hU1.
    have h𝒢prop : IsProperFilter 𝒢 := by
      refine ⟨h𝒢pre, ?_⟩
      rintro ⟨W, ⟨_, S, hS, hSW⟩, hW0⟩
      -- S ∩ U1c ≤ W ≤ 0.  Then S ≤ S∩(U₁∪U1c) ≤ (S∩U₁)∪(S∩U1c) ≤ (S∩U₁)∪0 = S∩U₁ ≤ U₁.
      have hSU1c0 : Subobject.le (Subobject.inter S U1c) Zero1 := Subobject.le_trans hSW hW0
      -- S ≤ (S∩U₁) ∪ (S∩U1c):  S = S∩⊤ ≤ S∩(U₁∪U1c) ≤ (S∩U₁)∪(S∩U1c).
      have hS_le : S.le (HasSubobjectUnions.union (Subobject.inter S U₁) (Subobject.inter S U1c)) := by
        have h1 : S.le (Subobject.inter S (HasSubobjectUnions.union U₁ U1c)) :=
          Subobject.le_inter (Subobject.le_refl S)
            (Subobject.le_trans (sub_le_entire S) hU1cov)
        exact Subobject.le_trans h1 (inter_union_le S U₁ U1c)
      -- (S∩U₁) ∪ (S∩U1c) ≤ (S∩U₁) ∪ 0 ≤ S∩U₁ ≤ U₁.
      have hS_U1 : S.le U₁ := by
        refine Subobject.le_trans hS_le ?_
        refine HasSubobjectUnions.union_min _ _ _ (Subobject.inter_le_right S U₁) ?_
        exact Subobject.le_trans hSU1c0 (PreLogos.bottom_min U₁)
      exact hU1 (ultrafilter_isFilter Fhat hUF S U₁ hS ⟨U1c, hU1disj, hU1cov⟩ hS_U1)
    -- (4) F̂ ⊆ 𝒢.
    have hF𝒢 : ∀ W, Fhat W → 𝒢 W := fun W hW =>
      ⟨hcompAll _ hW, W, hW, Subobject.inter_le_left _ _⟩
    -- (5) U₂ ∈ 𝒢:  S = K = U₁∪U₂ ∈ F̂,  K ∩ U1c ≤ U₂.
    have hU2𝒢 : 𝒢 U₂ := by
      refine ⟨complemented_of_disjoint_half (U₁ := U₂) (U₂ := U₁)
        (Subobject.le_trans (inter_comm_le _ _) hdisj)
        ⟨Kc, Subobject.le_trans (inter_mono (union_comm_le U₂ U₁) (Subobject.le_refl Kc)) hKdisj,
          Subobject.le_trans hKcov
            (HasSubobjectUnions.union_min _ _ _
              (Subobject.le_trans (union_comm_le U₁ U₂)
                (HasSubobjectUnions.union_left (HasSubobjectUnions.union U₂ U₁) Kc))
              (HasSubobjectUnions.union_right (HasSubobjectUnions.union U₂ U₁) Kc))⟩,
        HasSubobjectUnions.union U₁ U₂, hKmem, ?_⟩
      -- (U₁∪U₂) ∩ (U₂∪Kc) ≤ ((U₁∪U₂)∩U₂) ∪ ((U₁∪U₂)∩Kc) ≤ U₂.
      refine Subobject.le_trans (inter_union_le (HasSubobjectUnions.union U₁ U₂) U₂ Kc) ?_
      refine HasSubobjectUnions.union_min _ _ _ (Subobject.inter_le_right _ _) ?_
      -- (U₁∪U₂)∩Kc = K∩Kc ≤ 0 ≤ U₂.
      exact Subobject.le_trans hKdisj (PreLogos.bottom_min U₂)
    -- maximality: 𝒢 proper complemented extending F̂ ⟹ 𝒢 ⊆ F̂; hence U₂ ∈ F̂.
    exact hmax 𝒢 h𝒢prop h𝒢comp hF𝒢 U₂ hU2𝒢

/-! ### §1.635(a)  Ultra-filter EXISTENCE (Zorn)

  Every proper pre-filter `ℱ₀` of complemented subterminators extends to an ULTRA-FILTER.
  This is the one genuine use of the axiom of choice in §1.635.  We drive it with the
  mathlib-free `Freyd.WO.zorn` (Bourbaki–Witt tower, `Fredy/WellOrdering.lean`) applied to the
  poset of proper complemented pre-filters extending `ℱ₀`, ordered by `⊆`.  The chain-upper-bound
  hypothesis is the union of the chain (a proper complemented pre-filter), and the `zorn`-maximal
  element is exactly Freyd's ultra-filter. -/

/-- The poset point: a proper pre-filter of complemented subterminators extending `ℱ₀`. -/
structure ExtFilter (ℱ₀ : (Subobject 𝒞 one) → Prop) : Type (max u v) where
  fam      : (Subobject 𝒞 one) → Prop
  isProper : IsProperFilter fam
  allComp  : ∀ U, fam U → IsComplementedSub U
  extends₀ : ∀ U, ℱ₀ U → fam U

/-- §1.635(a): **EXISTENCE OF ULTRA-FILTERS.**  Every proper pre-filter `ℱ₀` all of whose members
    are complemented extends to an `IsUltraFilter`.  Proof by Zorn on `ExtFilter ℱ₀` ordered by
    `⊆`; the union of a chain is again a proper complemented pre-filter (the bound), and Zorn's
    maximal element is the ultra-filter. -/
theorem exists_ultrafilter_extending (ℱ₀ : (Subobject 𝒞 one) → Prop)
    (hproper : IsProperFilter ℱ₀) (hcomp : ∀ U, ℱ₀ U → IsComplementedSub U) :
    ∃ Fhat, IsUltraFilter Fhat ∧ (∀ U, ℱ₀ U → Fhat U) := by
  -- order on ExtFilter: containment of the underlying families.
  let le : ExtFilter ℱ₀ → ExtFilter ℱ₀ → Prop := fun a b => ∀ U, a.fam U → b.fam U
  have hrefl : ∀ a, le a a := fun a U h => h
  have htrans : ∀ {a b c}, le a b → le b c → le a c :=
    fun {a b c} hab hbc U h => hbc U (hab U h)
  -- the union of a chain of ExtFilters, joined with ℱ₀ to stay nonempty even on the empty chain.
  -- chain-upper-bound: take the family  ℱ₀ ∪ (⋃ of the chain).
  have hub : ∀ s : Freyd.WO.Sub (ExtFilter ℱ₀), Freyd.WO.IsChain le s →
      ∃ b, Freyd.WO.IsUB le s b := by
    intro s hchain
    -- the union family
    let 𝒰 : (Subobject 𝒞 one) → Prop := fun U => ℱ₀ U ∨ ∃ a, s a ∧ a.fam U
    -- every member of 𝒰 is complemented
    have hUcomp : ∀ U, 𝒰 U → IsComplementedSub U := by
      rintro U (h | ⟨a, _, ha⟩)
      · exact hcomp U h
      · exact a.allComp U ha
    -- 𝒰 is a pre-filter
    have hUpre : IsPreFilter 𝒰 := by
      refine ⟨⟨_, Or.inl hproper.1.1.choose_spec⟩, ?_⟩
      -- ↓-directedness
      rintro U V hU hV
      -- reduce both to a single ExtFilter a (or to ℱ₀), then use its directedness.
      -- helper: anything in ℱ₀ is in every chain member's family (extends₀); so if the chain is
      -- inhabited we can absorb ℱ₀-members into a chain member.
      -- Case analysis on where U, V come from.
      rcases hU with hU0 | ⟨a, hsa, haU⟩ <;> rcases hV with hV0 | ⟨b, hsb, hbV⟩
      · -- both from ℱ₀: use ℱ₀'s directedness.
        obtain ⟨W, hW, hWU, hWV⟩ := hproper.1.2 U V hU0 hV0
        exact ⟨W, Or.inl hW, hWU, hWV⟩
      · -- U ∈ ℱ₀, V ∈ b.fam.  ℱ₀ ⊆ b.fam, so U ∈ b.fam; use b's directedness.
        obtain ⟨W, hW, hWU, hWV⟩ := b.isProper.1.2 U V (b.extends₀ U hU0) hbV
        exact ⟨W, Or.inr ⟨b, hsb, hW⟩, hWU, hWV⟩
      · -- symmetric
        obtain ⟨W, hW, hWU, hWV⟩ := a.isProper.1.2 U V haU (a.extends₀ V hV0)
        exact ⟨W, Or.inr ⟨a, hsa, hW⟩, hWU, hWV⟩
      · -- both from chain members a, b: compare via the chain to land both in one family.
        rcases hchain hsa hsb with hab | hba
        · obtain ⟨W, hW, hWU, hWV⟩ := b.isProper.1.2 U V (hab U haU) hbV
          exact ⟨W, Or.inr ⟨b, hsb, hW⟩, hWU, hWV⟩
        · obtain ⟨W, hW, hWU, hWV⟩ := a.isProper.1.2 U V haU (hba V hbV)
          exact ⟨W, Or.inr ⟨a, hsa, hW⟩, hWU, hWV⟩
    -- 𝒰 is proper
    have hUprop : ¬ ∃ U, 𝒰 U ∧ Subobject.le U Zero1 := by
      rintro ⟨U, (hU0 | ⟨a, _, haU⟩), hU0le⟩
      · exact hproper.2 ⟨U, hU0, hU0le⟩
      · exact a.isProper.2 ⟨U, haU, hU0le⟩
    -- assemble the bound ExtFilter
    let bnd : ExtFilter ℱ₀ :=
      { fam := 𝒰, isProper := ⟨hUpre, hUprop⟩, allComp := hUcomp, extends₀ := fun U h => Or.inl h }
    exact ⟨bnd, fun a hsa U haU => Or.inr ⟨a, hsa, haU⟩⟩
  -- ExtFilter ℱ₀ is nonempty: ℱ₀ itself.
  have hne : Nonempty (ExtFilter ℱ₀) :=
    ⟨{ fam := ℱ₀, isProper := hproper, allComp := hcomp, extends₀ := fun _ h => h }⟩
  -- apply Zorn.
  obtain ⟨m, hm⟩ := Freyd.WO.zorn le hrefl htrans hub hne
  -- m.fam is the ultra-filter.
  refine ⟨m.fam, ⟨m.isProper, m.allComp, ?_⟩, m.extends₀⟩
  -- maximality clause: any proper complemented pre-filter 𝒢 ⊇ m.fam is ⊆ m.fam.
  intro 𝒢 h𝒢prop h𝒢comp hm𝒢 U h𝒢U
  -- 𝒢 extends ℱ₀ (via m.fam ⊇ ℱ₀ ⊆ … actually 𝒢 ⊇ m.fam ⊇ ℱ₀).
  let g : ExtFilter ℱ₀ :=
    { fam := 𝒢, isProper := h𝒢prop, allComp := h𝒢comp,
      extends₀ := fun V hV => hm𝒢 V (m.extends₀ V hV) }
  -- m ≤ g, so Zorn-maximality of m gives g ≤ m, i.e. 𝒢 ⊆ m.fam.
  exact hm g hm𝒢 U h𝒢U

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
  have hP₂_le_P₁ : P₂.le P₁ := Subobject.le_trans hP₂_le_bot (hPL.bottom_min P₁)
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
    exact Subobject.le_trans ha (Subobject.le_trans hb hc)
  have hP₁_entire : P₁.IsEntire :=
    entire_of_entire_le (Subobject.le_trans hEntireP_le_union hUnion_le_P₁)
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

/-- A subobject `S` of `A` whose domain admits ANY map into a bottom domain `(⊥ W).dom` is
    `≤ ⊥ A`.  The map makes `S.dom` initial (`dom_initial_of_map_to_bottom`); transporting along
    `bottom_dom_iso W A` yields `S.dom → (⊥ A).dom`, and the factorization triangle is forced
    because both sides are maps out of the initial `S.dom`. -/
theorem le_bottom_of_map_to_bottom {A W : 𝒞} (S : Subobject 𝒞 A)
    (g : S.dom ⟶ (PreLogos.bottom W).dom) : S.le (PreLogos.bottom A) := by
  have hinit : ∀ {Y : 𝒞} (u v : S.dom ⟶ Y), u = v := dom_initial_of_map_to_bottom g
  obtain ⟨ι, _⟩ := PreLogos.bottom_dom_iso W A
  exact ⟨g ≫ ι, hinit ((g ≫ ι) ≫ (PreLogos.bottom A).arr) S.arr⟩

/-- Pushforward of the bottom subobject lands in the bottom: `push m (⊥ S) ≤ ⊥ B`.
    `(push m (⊥ S)).dom = (⊥ S).dom` admits the identity map into a bottom domain, so it is
    INITIAL (`dom_initial_of_map_to_bottom`); the factorization triangle into `⊥ B` is forced
    because both sides are maps out of that initial object. -/
theorem pushforwardSub_bottom_le {S B : 𝒞} (m : S ⟶ B) (hm : Monic m) :
    (pushforwardSub m hm (PreLogos.bottom S)).le (PreLogos.bottom B) := by
  have hinit : ∀ {Y : 𝒞} (u v : (PreLogos.bottom S).dom ⟶ Y), u = v :=
    dom_initial_of_map_to_bottom (Cat.id (PreLogos.bottom S).dom)
  obtain ⟨ι, _⟩ := PreLogos.bottom_dom_iso S B   -- ι : (⊥ S).dom → (⊥ B).dom
  exact ⟨ι, hinit (ι ≫ (PreLogos.bottom B).arr) (pushforwardSub m hm (PreLogos.bottom S)).arr⟩

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

/-- Being a complemented subobject is symmetric: if `U` is complemented with complement `U₂`,
    then `U₂` is complemented with complement `U`.  `inter`/`union` are commutative up to `≤`. -/
theorem complementedSub_symm [HasBinaryCoproducts 𝒞] {A : 𝒞} {U U₂ : Subobject 𝒞 A}
    (hdisj : Subobject.le (Subobject.inter U U₂) (PreLogos.bottom A))
    (hentire : Subobject.le (Subobject.entire A) (HasSubobjectUnions.union U U₂)) :
    IsComplementedSub U₂ :=
  ⟨U, Subobject.le_trans (inter_comm_le U₂ U) hdisj, Subobject.le_trans hentire (union_comm_le U U₂)⟩

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
    exact Subobject.le_trans ha (Subobject.le_trans hb hc)
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
    refine Subobject.le_trans (Y := image (coprodMapOne m)) ?_ him_le
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
    Subobject.le_trans (invImage_mono_local il hJ_le) (invImage_postcompSub_le (image m) inl_mono)
  -- inl⁻¹ Kr ≤ bottom A ≤ image m :  Kr = image inr ≤ inrSub, so inl⁻¹ Kr ≤ inl⁻¹ inrSub = inl ∩ inr ≤ ⊥.
  have hKr_le : Kr.le (inrSub (𝒞 := 𝒞) (A := A) (B := one) inr_mono) :=
    image_min _ _ ⟨Cat.id _, Cat.id_comp _⟩
  have hKl : (InverseImage il Kr).le (image m) :=
    -- inl⁻¹ Kr ≤ inl⁻¹ inrSub ≤ image m  (the latter has an initial domain).
    Subobject.le_trans (invImage_mono_local il hKr_le)
      (invImage_inl_inrSub_le_any (A := A) (B := one) (image m))
  -- assemble: entire A ≤ inl⁻¹(entire) ≤ inl⁻¹(union) ≤ union(inl⁻¹J)(inl⁻¹Kr) ≤ image m.
  exact Subobject.le_trans ha (Subobject.le_trans hb (Subobject.le_trans hc
    (HasSubobjectUnions.union_min _ _ _ hJl hKl)))

/-! ### §1.634 OBSTACLE 1 — witness-exposing coproduct decomposition

  `decompose_via_coproduct` returns only an `Isomorphic A (A₁ + A₂)`, discarding the subobject
  witnesses.  For the surjectivity of `disjUnionCompare` on the `TF`-quotient we need the two
  inverse-image subobjects `A₁ := h#inl`, `A₂ := h#inr ⊆ U.dom` with their COVER
  (`A₁ ∪ A₂ = ⊤`), DISJOINTNESS (`A₁ ∩ A₂ ≤ ⊥`) and the FACTORIZATIONS `A_i.arr ≫ h = f_i ≫ inj_i`.
  All three are extracted from the same pullback data that builds the iso. -/

/-- **OBSTACLE 1.**  For `h : X → A₁+A₂` the two inverse images `A₁ := h#inl`, `A₂ := h#inr`
    of the coproduct injections give a complemented pair of `X` together with the factorizing
    legs `f₁ : A₁.dom → A₁`, `f₂ : A₂.dom → A₂`:
      * cover  `⊤ ≤ A₁ ∪ A₂`  (every element of `X` lands in one injection's image),
      * disjoint `A₁ ∩ A₂ ≤ ⊥`  (no element lands in both),
      * `A₁.arr ≫ h = f₁ ≫ inl`,  `A₂.arr ≫ h = f₂ ≫ inr`. -/
theorem decompose_witnesses {X A₁ A₂ : 𝒞} (h : X ⟶ HasBinaryCoproducts.coprod A₁ A₂) :
    (Subobject.entire X).le (HasSubobjectUnions.union
        (InverseImage h (inlSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inl_mono))
        (InverseImage h (inrSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inr_mono)))
    ∧ (Subobject.inter
        (InverseImage h (inlSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inl_mono))
        (InverseImage h (inrSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inr_mono))).le (PreLogos.bottom X)
    ∧ (∃ f₁ : (InverseImage h (inlSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inl_mono)).dom ⟶ A₁,
        (InverseImage h (inlSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inl_mono)).arr ≫ h
          = f₁ ≫ HasBinaryCoproducts.inl)
    ∧ (∃ f₂ : (InverseImage h (inrSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inr_mono)).dom ⟶ A₂,
        (InverseImage h (inrSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inr_mono)).arr ≫ h
          = f₂ ≫ HasBinaryCoproducts.inr) := by
  let Inl := inlSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inl_mono
  let Inr := inrSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inr_mono
  let U₁ := InverseImage h Inl
  let U₂ := InverseImage h Inr
  show (Subobject.entire X).le (HasSubobjectUnions.union U₁ U₂)
    ∧ (Subobject.inter U₁ U₂).le (PreLogos.bottom X)
    ∧ (∃ f₁ : U₁.dom ⟶ A₁, U₁.arr ≫ h = f₁ ≫ HasBinaryCoproducts.inl)
    ∧ (∃ f₂ : U₂.dom ⟶ A₂, U₂.arr ≫ h = f₂ ≫ HasBinaryCoproducts.inr)
  let pbL := HasPullbacks.has h Inl.arr   -- U₁.dom = pbL.pt, U₁.arr = pbL.π₁, f₁ = pbL.π₂
  let pbR := HasPullbacks.has h Inr.arr
  refine ⟨?_, ?_, ⟨pbL.cone.π₂, ?_⟩, ⟨pbR.cone.π₂, ?_⟩⟩
  · -- COVER:  entire X ≤ h#(entire) ≤ h#(Inl∪Inr) ≤ h#Inl ∪ h#Inr = U₁∪U₂.
    have ha : (Subobject.entire X).le
        (InverseImage h (Subobject.entire (HasBinaryCoproducts.coprod A₁ A₂))) :=
      entire_le_invImage_entire h
    have hbu : (Subobject.entire (HasBinaryCoproducts.coprod A₁ A₂)).le
        (HasSubobjectUnions.union Inl Inr) := inl_union_inr_entire (𝒟 := 𝒞) (A := A₁) (B := A₂)
    have hb : (InverseImage h (Subobject.entire _)).le
        (InverseImage h (HasSubobjectUnions.union Inl Inr)) := invImage_mono_local h hbu
    have hc : (InverseImage h (HasSubobjectUnions.union Inl Inr)).le
        (HasSubobjectUnions.union U₁ U₂) := (PreLogos.invImage_preserves_union h Inl Inr).1
    exact Subobject.le_trans ha (Subobject.le_trans hb hc)
  · -- DISJOINT:  the intersection apex maps into (Inl∩Inr).dom ≤ ⊥(A₁+A₂), hence U₁∩U₂ ≤ ⊥X.
    let pbI := HasPullbacks.has U₁.arr U₂.arr   -- (U₁∩U₂).dom = pbI.pt
    let pbJ := HasPullbacks.has Inl.arr Inr.arr -- (Inl∩Inr).dom
    have hsq : (pbI.cone.π₁ ≫ pbL.cone.π₂) ≫ Inl.arr
             = (pbI.cone.π₂ ≫ pbR.cone.π₂) ≫ Inr.arr := by
      calc (pbI.cone.π₁ ≫ pbL.cone.π₂) ≫ Inl.arr
          = pbI.cone.π₁ ≫ (pbL.cone.π₂ ≫ Inl.arr) := Cat.assoc _ _ _
        _ = pbI.cone.π₁ ≫ (pbL.cone.π₁ ≫ h) := by rw [pbL.cone.w]
        _ = (pbI.cone.π₁ ≫ pbL.cone.π₁) ≫ h := (Cat.assoc _ _ _).symm
        _ = (pbI.cone.π₁ ≫ U₁.arr) ≫ h := rfl
        _ = (pbI.cone.π₂ ≫ U₂.arr) ≫ h := by rw [pbI.cone.w]
        _ = (pbI.cone.π₂ ≫ pbR.cone.π₁) ≫ h := rfl
        _ = pbI.cone.π₂ ≫ (pbR.cone.π₁ ≫ h) := Cat.assoc _ _ _
        _ = pbI.cone.π₂ ≫ (pbR.cone.π₂ ≫ Inr.arr) := by rw [pbR.cone.w]
        _ = (pbI.cone.π₂ ≫ pbR.cone.π₂) ≫ Inr.arr := (Cat.assoc _ _ _).symm
    let cJ : Cone Inl.arr Inr.arr :=
      ⟨pbI.cone.pt, pbI.cone.π₁ ≫ pbL.cone.π₂, pbI.cone.π₂ ≫ pbR.cone.π₂, hsq⟩
    let mJ : pbI.cone.pt ⟶ (Subobject.inter Inl Inr).dom := pbJ.lift cJ
    obtain ⟨e, _⟩ := inl_inter_inr_le_bottom (𝒟 := 𝒞) (A := A₁) (B := A₂)
    -- e : (Inl∩Inr).dom → (⊥(A₁+A₂)).dom.  (U₁∩U₂).dom = pbI.pt maps to a bottom domain.
    exact le_bottom_of_map_to_bottom (Subobject.inter U₁ U₂) (mJ ≫ e)
  · -- FACTORIZATION U₁:  U₁.arr ≫ h = pbL.π₁ ≫ h = pbL.π₂ ≫ Inl.arr = f₁ ≫ inl.
    show pbL.cone.π₁ ≫ h = pbL.cone.π₂ ≫ HasBinaryCoproducts.inl
    exact pbL.cone.w
  · show pbR.cone.π₁ ≫ h = pbR.cone.π₂ ≫ HasBinaryCoproducts.inr
    exact pbR.cone.w

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
      (Subobject.le_trans (invImg_fst_inl_le A B C) (HasSubobjectUnions.union_left _ _))
      (Subobject.le_trans (invImg_fst_inr_le A B C) (HasSubobjectUnions.union_right _ _))
  exact Subobject.le_trans ha (Subobject.le_trans hb (Subobject.le_trans hc hd))

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
            (Subobject.le_trans hUle (HasSubobjectUnions.union_left _ _))
            (Subobject.le_trans hU₂le (HasSubobjectUnions.union_right _ _))
        -- union (image U.arr) (image U₂.arr) ≤ image c  (it is an image of `c`, `image c` minimal-target).
        have huac : (HasSubobjectUnions.union (image U.arr) (image U₂.arr)).le (image c) :=
          (union_via_coproduct_image U.arr U₂.arr).2 (image c) (image_allows c)
        exact Subobject.le_trans hcover (Subobject.le_trans hmono huac)
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

/-! ## §1.634 The disjoint-union iff:  `PreservesDisjointUnions (T_ℱ) ↔ UnionPrime ℱ`

  Working at `Cat.{u}` (source and target hom-universes coincide, so `TF ℱ : 𝒞 → Type u` and the
  `TF_functor` instance applies — exactly the §1.55 setting).  We combine the two OBSTACLE kernels:

    * SURJECTIVITY ⟸ `UnionPrime ℱ` (with `ℱ` up-closed, `IsFilter`): `decompose_witnesses`
      splits a name `(U, h:U.dom→A₁+A₂)` into `U₁=h#inl, U₂=h#inr ⊆ U.dom`; pushing to `Sub(1)`
      (`pushforwardSub`) gives `V₁,V₂` with `V₁∩V₂ ≤ 0` (`inter_pushforward_le` +
      `pushforwardSub_bottom_le`) and `U ≤ V₁∪V₂` (cover + `pushforwardSub_union_le`), so up-closure
      puts `V₁∪V₂ ∈ ℱ` and `UnionPrime` puts `V₁∈ℱ` or `V₂∈ℱ`; the name then comes from `T_ℱ(Aᵢ)`.

    * INJECTIVITY ⟸ `IsProperFilter ℱ`: the inl/inl, inr/inr cases cancel the monic injection
      (`PrefRel_of_TF_eq` + `PrefRel_reflect_monic`); the cross inl/inr case forces a common
      refinement `W∈ℱ` factoring through both injections, hence `W ≤ 0` (`coprod_inl_inr_disjoint_elt`
      + `le_bottom_of_map_to_bottom`), contradicting properness. -/

section DisjointUnionPreservation

variable {𝒞 : Type u} [Cat.{u} 𝒞] [DisjointBinaryCoproduct 𝒞]

/-- SURJECTIVITY of `disjUnionCompare (TF ℱ)` from `UnionPrime ℱ` (and up-closure of `ℱ`). -/
theorem disjUnionCompare_surjective (ℱ : (Subobject 𝒞 one) → Prop)
    (hcompAll : ∀ U, ℱ U → IsComplementedSub U)
    (hup : ∀ U V, ℱ U → U.le V → IsComplementedSub V → ℱ V)
    (hUP : UnionPrime ℱ) (A₁ A₂ : 𝒞) :
    Function.Surjective (disjUnionCompare (TF ℱ) A₁ A₂) := by
  intro t
  refine Quot.inductionOn t (fun p => ?_)
  -- p = ⟨U, hU, h⟩, h : U.dom → A₁+A₂.
  obtain ⟨hcover, hdisj, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩ := decompose_witnesses (X := p.U.dom) p.map
  -- subobjects of U.dom and their pushforwards to Sub(1).
  let Inl := inlSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inl_mono
  let Inr := inrSub (𝒞 := 𝒞) (A := A₁) (B := A₂) inr_mono
  let U₁ := InverseImage p.map Inl
  let U₂ := InverseImage p.map Inr
  let V₁ := pushforwardSub p.U.arr p.U.monic U₁
  let V₂ := pushforwardSub p.U.arr p.U.monic U₂
  -- push(entire U.dom) and U coincide; V₁,V₂ ≤ U.
  have hpushEntire_le_U : (pushforwardSub p.U.arr p.U.monic (Subobject.entire p.U.dom)).le p.U :=
    ⟨Cat.id _, by
      show Cat.id _ ≫ p.U.arr
        = (Subobject.entire p.U.dom).arr ≫ p.U.arr
      rw [Cat.id_comp]
      show p.U.arr = Cat.id p.U.dom ≫ p.U.arr
      rw [Cat.id_comp]⟩
  have hV₁_le_U : V₁.le p.U :=
    Subobject.le_trans (pushforwardSub_mono p.U.arr p.U.monic (sub_le_entire U₁)) hpushEntire_le_U
  have hV₂_le_U : V₂.le p.U :=
    Subobject.le_trans (pushforwardSub_mono p.U.arr p.U.monic (sub_le_entire U₂)) hpushEntire_le_U
  -- (a) V₁ ∩ V₂ ≤ 0.
  have hVdisj : (Subobject.inter V₁ V₂).le Zero1 := by
    refine Subobject.le_trans (inter_pushforward_le p.U.arr p.U.monic U₁ U₂) ?_
    refine Subobject.le_trans (pushforwardSub_mono p.U.arr p.U.monic hdisj) ?_
    exact pushforwardSub_bottom_le p.U.arr p.U.monic
  -- (b) U ≤ V₁ ∪ V₂  and  V₁∪V₂ ≤ U, so V₁∪V₂ ≅ U is complemented; up-closure puts it in ℱ.
  have hUV : p.U.le (HasSubobjectUnions.union V₁ V₂) := by
    -- U ≤ push(entire U.dom) ≤ push(U₁∪U₂) ≤ V₁∪V₂.
    have hUpush : p.U.le (pushforwardSub p.U.arr p.U.monic (Subobject.entire p.U.dom)) :=
      ⟨Cat.id _, by
        show Cat.id _ ≫ (Cat.id p.U.dom ≫ p.U.arr) = p.U.arr
        rw [Cat.id_comp, Cat.id_comp]⟩
    refine Subobject.le_trans hUpush ?_
    refine Subobject.le_trans
      (pushforwardSub_mono p.U.arr p.U.monic hcover) ?_
    exact pushforwardSub_union_le p.U.arr p.U.monic U₁ U₂
  have hVU : (HasSubobjectUnions.union V₁ V₂).le p.U :=
    HasSubobjectUnions.union_min _ _ _ hV₁_le_U hV₂_le_U
  have hVcomp : IsComplementedSub (HasSubobjectUnions.union V₁ V₂) :=
    complementedSub_congr hVU hUV (hcompAll p.U p.hU)
  have hUmem : ℱ (HasSubobjectUnions.union V₁ V₂) := hup p.U _ p.hU hUV hVcomp
  -- (c) UnionPrime ⟹ V₁ ∈ ℱ or V₂ ∈ ℱ.
  rcases hUP.2 V₁ V₂ hVdisj hUmem with hV1 | hV2
  · -- V₁ ∈ ℱ:  the name comes from T_ℱ(A₁) via f₁.
    refine ⟨Sum.inl (TF.mk ℱ ⟨V₁, hV1, f₁⟩), ?_⟩
    show TF.map ℱ HasBinaryCoproducts.inl (TF.mk ℱ ⟨V₁, hV1, f₁⟩) = Quot.mk _ p
    show TF.mk ℱ ⟨V₁, hV1, f₁ ≫ HasBinaryCoproducts.inl⟩ = TF.mk ℱ p
    apply Quot.sound
    -- PrefRel: W=V₁, a=id, b=U₁.arr.
    refine ⟨V₁, hV1, Cat.id _, U₁.arr, Cat.id_comp _, ?_, ?_⟩
    · show U₁.arr ≫ p.U.arr = U₁.arr ≫ p.U.arr; rfl
    · show Cat.id _ ≫ (f₁ ≫ HasBinaryCoproducts.inl) = U₁.arr ≫ p.map
      rw [Cat.id_comp, ← hf₁]
  · refine ⟨Sum.inr (TF.mk ℱ ⟨V₂, hV2, f₂⟩), ?_⟩
    show TF.map ℱ HasBinaryCoproducts.inr (TF.mk ℱ ⟨V₂, hV2, f₂⟩) = Quot.mk _ p
    show TF.mk ℱ ⟨V₂, hV2, f₂ ≫ HasBinaryCoproducts.inr⟩ = TF.mk ℱ p
    apply Quot.sound
    refine ⟨V₂, hV2, Cat.id _, U₂.arr, Cat.id_comp _, ?_, ?_⟩
    · show U₂.arr ≫ p.U.arr = U₂.arr ≫ p.U.arr; rfl
    · show Cat.id _ ≫ (f₂ ≫ HasBinaryCoproducts.inr) = U₂.arr ≫ p.map
      rw [Cat.id_comp, ← hf₂]

/-- INJECTIVITY of `disjUnionCompare (TF ℱ)` from `IsProperFilter ℱ`. -/
theorem disjUnionCompare_injective (ℱ : (Subobject 𝒞 one) → Prop)
    (hprop : IsProperFilter ℱ) (A₁ A₂ : 𝒞) :
    Function.Injective (disjUnionCompare (TF ℱ) A₁ A₂) := by
  have hpre : IsPreFilter ℱ := hprop.1
  -- The cross case: TF.map inl x = TF.map inr y is impossible (properness).
  have hcross : ∀ (p : PrefilterMap ℱ A₁) (q : PrefilterMap ℱ A₂),
      TF.map ℱ (HasBinaryCoproducts.inl (A := A₁) (B := A₂)) (TF.mk ℱ p)
        = TF.map ℱ (HasBinaryCoproducts.inr (A := A₁) (B := A₂)) (TF.mk ℱ q)
      → False := by
    intro p q hpq
    rw [TF.map_mk, TF.map_mk] at hpq
    -- PrefRel ⟨p.U,_,p.map≫inl⟩ ⟨q.U,_,q.map≫inr⟩.
    have hrel : PrefRel ℱ (⟨p.U, p.hU, p.map ≫ HasBinaryCoproducts.inl⟩ : PrefilterMap ℱ _)
        ⟨q.U, q.hU, q.map ≫ HasBinaryCoproducts.inr⟩ := PrefRel_of_TF_eq ℱ hpre hpq
    obtain ⟨W, hW, a, b, ha, hb, hab⟩ := hrel
    -- (a≫p.map)≫inl = (b≫q.map)≫inr.
    have hcross_eq : (a ≫ p.map) ≫ HasBinaryCoproducts.inl
        = (b ≫ q.map) ≫ HasBinaryCoproducts.inr := by
      calc (a ≫ p.map) ≫ HasBinaryCoproducts.inl = a ≫ (p.map ≫ HasBinaryCoproducts.inl) := Cat.assoc _ _ _
        _ = b ≫ (q.map ≫ HasBinaryCoproducts.inr) := hab
        _ = (b ≫ q.map) ≫ HasBinaryCoproducts.inr := (Cat.assoc _ _ _).symm
    obtain ⟨e, _⟩ := coprod_inl_inr_disjoint_elt (𝒟 := 𝒞) (A := A₁) (B := A₂)
      (a ≫ p.map) (b ≫ q.map) hcross_eq
    -- e : W.dom → bottom(A₁+A₂).dom ⟹ W ≤ 0 ⟹ contradicts properness.
    exact hprop.2 ⟨W, hW, le_bottom_of_map_to_bottom W e⟩
  -- inl/inl, inr/inr injectivity at the representative level.
  have hinl : ∀ (p p' : PrefilterMap ℱ A₁),
      TF.map ℱ (HasBinaryCoproducts.inl (A := A₁) (B := A₂)) (TF.mk ℱ p)
        = TF.map ℱ (HasBinaryCoproducts.inl (A := A₁) (B := A₂)) (TF.mk ℱ p')
      → TF.mk ℱ p = TF.mk ℱ p' := by
    intro p p' hpp
    rw [TF.map_mk, TF.map_mk] at hpp
    exact Quot.sound (PrefRel_reflect_monic ℱ (m := HasBinaryCoproducts.inl) inl_mono
      (PrefRel_of_TF_eq ℱ hpre hpp))
  have hinr : ∀ (q q' : PrefilterMap ℱ A₂),
      TF.map ℱ (HasBinaryCoproducts.inr (A := A₁) (B := A₂)) (TF.mk ℱ q)
        = TF.map ℱ (HasBinaryCoproducts.inr (A := A₁) (B := A₂)) (TF.mk ℱ q')
      → TF.mk ℱ q = TF.mk ℱ q' := by
    intro q q' hqq
    rw [TF.map_mk, TF.map_mk] at hqq
    exact Quot.sound (PrefRel_reflect_monic ℱ (m := HasBinaryCoproducts.inr) inr_mono
      (PrefRel_of_TF_eq ℱ hpre hqq))
  intro s s' hss
  revert hss
  cases s with
  | inl x => cases s' with
    | inl x' =>
        refine Quot.inductionOn x (fun p => Quot.inductionOn x' (fun p' hss => ?_))
        exact congrArg Sum.inl (hinl p p' hss)
    | inr y' =>
        refine Quot.inductionOn x (fun p => Quot.inductionOn y' (fun q hss => ?_))
        exact (hcross p q hss).elim
  | inr y => cases s' with
    | inl x' =>
        refine Quot.inductionOn y (fun q => Quot.inductionOn x' (fun p hss => ?_))
        exact (hcross p q hss.symm).elim
    | inr y' =>
        refine Quot.inductionOn y (fun q => Quot.inductionOn y' (fun q' hss => ?_))
        exact congrArg Sum.inr (hinr q q' hss)

/-- **§1.634 (⟸):** an ULTRA-FILTER `F̂` gives a union-preserving `T_F̂`.  Injectivity from
    properness; surjectivity from `UnionPrime F̂` (`ultrafilter_unionPrime`), with up-closure
    within complemented subterminators supplied by `ultrafilter_isFilter`. -/
theorem preservesDisjointUnions_of_ultrafilter (ℱ : (Subobject 𝒞 one) → Prop)
    (hU : IsUltraFilter ℱ) : PreservesDisjointUnions (TF ℱ) :=
  fun A₁ A₂ =>
    ⟨disjUnionCompare_injective ℱ hU.1 A₁ A₂,
     disjUnionCompare_surjective ℱ hU.2.1
       (fun U V hUmem hUV hVcomp => ultrafilter_isFilter ℱ hU U V hUmem hVcomp hUV)
       (ultrafilter_unionPrime ℱ hU) A₁ A₂⟩

/-- **§1.634 (⟹), part 1:** injectivity of `disjUnionCompare` forces `0 ∉ ℱ`.  If `0 ∈ ℱ`, the
    zero-named elements of `T_ℱ(A₁)` and `T_ℱ(A₂)` (named by the unique maps out of the initial
    `0 = Zero1.dom`) have equal images under the comparison (their representatives agree on the
    common refinement `Zero1`, both maps out of the initial `0`), but `inl ≠ inr` as sum tags. -/
theorem notMem_zero_of_injective (ℱ : (Subobject 𝒞 one) → Prop)
    (hinj : Function.Injective
      (disjUnionCompare (TF ℱ) (minimal_subobject_of_one_is_coterminator
        (inferInstance : PreLogos 𝒞)).zero
        (minimal_subobject_of_one_is_coterminator (inferInstance : PreLogos 𝒞)).zero)) :
    ¬ ℱ Zero1 := by
  intro h0
  let Z := (minimal_subobject_of_one_is_coterminator (inferInstance : PreLogos 𝒞)).zero
  -- Zero1.dom = Z definitionally; the coterminator gives ζ : Z → Z (here identity suffices).
  -- zero-named elements of T_ℱ(Z) on the left and right summand.
  let pL : PrefilterMap ℱ Z := ⟨Zero1, h0, Cat.id _⟩
  let pR : PrefilterMap ℱ Z := ⟨Zero1, h0, Cat.id _⟩
  have hsum : (Sum.inl (TF.mk ℱ pL) : (TF ℱ Z) ⊕ (TF ℱ Z)) = Sum.inr (TF.mk ℱ pR) := by
    apply hinj
    -- disjUnionCompare(inl pL)=TF.mk⟨Zero1,_,id≫inl⟩, (inr pR)=TF.mk⟨Zero1,_,id≫inr⟩.
    show TF.map ℱ HasBinaryCoproducts.inl (TF.mk ℱ pL)
       = TF.map ℱ HasBinaryCoproducts.inr (TF.mk ℱ pR)
    rw [TF.map_mk, TF.map_mk]
    apply Quot.sound
    -- common refinement Zero1; both maps out of the initial Z = Zero1.dom agree.
    refine ⟨Zero1, h0, Cat.id _, Cat.id _, Cat.id_comp _, Cat.id_comp _, ?_⟩
    exact (minimal_subobject_of_one_is_coterminator (inferInstance : PreLogos 𝒞)).init_uniq _ _
  exact nomatch hsum

/-- **§1.635 (proper):** for an ultra-filter `F̂` in the Boolean algebra of complemented
    subterminators, `T_F̂` is a REPRESENTATION OF PRE-LOGOI — i.e. a representation of regular
    categories (`repReg`, the §1.634 "preserves finite products, equalizers and covers" half,
    carried as a parameter since `Type u` is not instanced as a `PreLogos` here) that additionally
    PRESERVES DISJOINT UNIONS (`preservesDisjointUnions_of_ultrafilter`).  This packages
    `T_F̂` in the `SetRepOfPreLogos` shape Freyd's representation theorem produces. -/
theorem setRepOfPreLogos_of_ultrafilter (ℱ : (Subobject 𝒞 one) → Prop)
    (hU : IsUltraFilter ℱ) {repReg : Prop} (hreg : repReg) :
    SetRepOfPreLogos (TF ℱ) repReg :=
  ⟨hreg, preservesDisjointUnions_of_ultrafilter ℱ hU⟩

end DisjointUnionPreservation

/-! ## §2.218 BRICK 1 — `RegularCategory (Type v)` and `RegularCategory (I → Type v)`

  The §1.635 Henkin–Lubkin target is `Set^I = (I → Type v)`.  To apply `Rel(–)` (the
  allegory-of-relations construction, §2.111) to it we need it packaged as a
  `RegularCategory`.  We build the regular structure of `Set = Type v` first (finite limits
  pointwise, images = set-images, covers = surjections, pullbacks transfer surjections), then
  lift it pointwise to `I → Type v`.

  `setCat : Cat.{v} (Type v)` is reused from `Horn.lean` (DRY). -/

namespace SetRegular

universe w

/-! ### Finite limits of `Type w` -/

/-- §1.421 (Set): `PUnit` is the terminator. -/
instance setHasTerminal : HasTerminal (Type w) where
  one := PUnit
  trm _ := fun _ => PUnit.unit
  uniq f g := by funext x; rfl

/-- §1.423 (Set): the cartesian product is the categorical product. -/
instance setHasBinaryProducts : HasBinaryProducts (Type w) where
  prod A B := A × B
  fst := Prod.fst
  snd := Prod.snd
  pair f g := fun x => (f x, g x)
  fst_pair _ _ := rfl
  snd_pair _ _ := rfl
  pair_uniq f g h h₁ h₂ := by
    funext x
    have e1 : (h x).1 = f x := congrFun h₁ x
    have e2 : (h x).2 = g x := congrFun h₂ x
    exact Prod.ext e1 e2

/-- §1.454 (Set): the pullback of `f, g` is the fibre-product subtype. -/
instance setHasPullbacks : HasPullbacks (Type w) where
  has {A B C} f g :=
    { cone :=
        { pt := {p : A × B // f p.1 = g p.2}
          π₁ := fun p => p.val.1
          π₂ := fun p => p.val.2
          w  := by funext p; exact p.property }
      lift := fun c => fun x => ⟨(c.π₁ x, c.π₂ x), congrFun c.w x⟩
      lift_fst := fun _ => rfl
      lift_snd := fun _ => rfl
      lift_uniq := fun c u h₁ h₂ => by
        funext x
        apply Subtype.ext
        exact Prod.ext (congrFun h₁ x) (congrFun h₂ x) }

/-! ### Monics, covers and images of `Type w` -/

/-- A `Type w`-morphism is monic iff it is injective. -/
theorem set_monic_iff_injective {A B : Type w} (f : A ⟶ B) :
    Monic f ↔ Function.Injective f := by
  constructor
  · intro hm a a' h
    -- Test the two constant maps `PUnit → A` at `a, a'`.
    have := hm (fun _ : PUnit => a) (fun _ : PUnit => a') (by funext _; exact h)
    exact congrFun this PUnit.unit
  · intro hinj W g h hgh
    funext x; exact hinj (congrFun hgh x)

/-- A `Type w`-morphism is a cover iff it is surjective.  (⇐) uses `Classical.choice`
    to split the surjection through any monic factor; (⇒) takes the image subtype as a
    monic the cover must factor through. -/
theorem set_cover_iff_surjective {A B : Type w} (f : A ⟶ B) :
    Cover f ↔ Function.Surjective f := by
  constructor
  · intro hc b
    -- Factor `f` through the image subtype `{b // ∃ a, f a = b}` (monic); cover ⟹ iso ⟹ onto.
    let I : Type w := {b : B // ∃ a, f a = b}
    let m : I ⟶ B := Subtype.val
    have hm : Monic m := (set_monic_iff_injective m).2 (fun _ _ h => Subtype.ext h)
    let g : A ⟶ I := fun a => ⟨f a, a, rfl⟩
    have hgm : g ≫ m = f := rfl
    obtain ⟨inv, _, hinv2⟩ := hc m g hm hgm
    -- `inv : B → I`, `m ∘ inv = id`, so `b = m (inv b) ∈ image`.
    have hmb : m (inv b) = b := congrFun hinv2 b
    obtain ⟨a, ha⟩ := (inv b).property
    exact ⟨a, by rw [ha]; exact hmb⟩
  · intro hsurj
    -- Surjective ⟹ has a section (Classical.choice) ⟹ cover.
    let s : B ⟶ A := fun b => (hsurj b).choose
    have hs : s ≫ f = Cat.id B := by funext b; exact (hsurj b).choose_spec
    intro C m g hm hgm
    exact cover_of_section (e := f) s hs m g hm hgm

/-- §1.51 (Set): the image of `f : A → B` is the subtype `{b // ∃ a, f a = b}`. -/
def setImage {A B : Type w} (f : A ⟶ B) : Subobject (Type w) B where
  dom := {b : B // ∃ a, f a = b}
  arr := Subtype.val
  monic := (set_monic_iff_injective _).2 (fun _ _ h => Subtype.ext h)

theorem set_isImage {A B : Type w} (f : A ⟶ B) : IsImage f (setImage f) := by
  refine ⟨⟨fun a => ⟨f a, a, rfl⟩, rfl⟩, ?_⟩
  -- Minimality: any subobject `S` allowing `f` receives a map from the image subtype.
  intro S hS
  obtain ⟨g, hg⟩ := hS
  -- For `⟨b, a, ha⟩ : image`, send to `g a`; well-defined since `S.arr` is monic.
  refine ⟨fun p => g p.property.choose, ?_⟩
  funext p
  obtain ⟨b, hb⟩ := p
  -- `S.arr (g a') = f a' = b` for `a' := (∃ a, f a = b).choose`.
  exact (Eq.trans (congrFun hg _) hb.choose_spec)

instance setHasImages : HasImages (Type w) where
  image f := setImage f
  isImage f := set_isImage f

/-! ### Pullbacks transfer covers in `Type w` -/

/-- §1.52 (Set): in a pullback square the map opposite a surjection is a surjection. -/
instance setPullbacksTransferCovers : PullbacksTransferCovers (Type w) where
  pullbacks_transfer_covers {A B C f g} c hpb hf := by
    -- `c` is a pullback of `f, g`; `f` surjective ⟹ `c.π₂` surjective.
    rw [set_cover_iff_surjective] at hf ⊢
    intro b
    -- pick `a` with `f a = g b`; the pair `(a, b)` lifts into the pullback vertex.
    obtain ⟨a, ha⟩ := hf (g b)
    -- Use the comparison `u` from the canonical fibre cone `{(a,b) // f a = g b}` into `c`.
    let d : Cone f g :=
      { pt := PUnit
        π₁ := fun _ => a
        π₂ := fun _ => b
        w  := by funext _; exact ha }
    obtain ⟨u, ⟨_, hu₂⟩, _⟩ := hpb d
    exact ⟨u PUnit.unit, congrFun hu₂ PUnit.unit⟩

/-- §1.52: `Type w` is a regular category. -/
instance setRegular : RegularCategory (Type w) where
  toHasTerminal := setHasTerminal
  toHasBinaryProducts := setHasBinaryProducts
  toHasPullbacks := setHasPullbacks
  toHasImages := setHasImages
  toPullbacksTransferCovers := setPullbacksTransferCovers

/-! ### §1.521 The power `Set^I = (I → Type w)` is regular (pointwise)

  Everything lifts pointwise: terminator/product/pullback/image are computed in each fibre,
  and a morphism is monic / a cover iff it is so in every fibre (injective / surjective at
  each `i`).  `powerCat I : Cat (I → Type w)` is reused from `S1_55`. -/

variable {I : Type w}

/-- A power morphism is monic iff it is fibrewise injective.  The forward probe uses the
    pointed family `W j := PLift (i = j)`, inhabited only at `j = i` (so off-`i` fibres carry
    a unique empty-domain map — no choice, no decidability, handles empty fibres). -/
theorem power_monic_iff {X Y : I → Type w} (f : X ⟶ Y) :
    Monic f ↔ ∀ i, Function.Injective (f i) := by
  constructor
  · intro hm i a a' h
    let W : I → Type w := fun j => ULift.{w} (PLift (i = j))
    have := hm (W := W)
               (fun j p => p.down.down ▸ a) (fun j p => p.down.down ▸ a') ?_
    · have := congrFun (congrFun this i) (ULift.up (PLift.up rfl))
      simpa using this
    · funext j p
      obtain ⟨⟨e⟩⟩ := p; cases e; simpa using h
  · intro hinj W g h hgh
    funext i x
    exact hinj i (congrFun (congrFun hgh i) x)

/-- A power morphism is a cover iff it is fibrewise surjective. -/
theorem power_cover_iff {X Y : I → Type w} (f : X ⟶ Y) :
    Cover f ↔ ∀ i, Function.Surjective (f i) := by
  constructor
  · intro hc i b
    -- Factor through the fibrewise-image family; cover ⟹ iso ⟹ each fibre onto.
    let Im : I → Type w := fun j => {b : Y j // ∃ a, f j a = b}
    let m : Im ⟶ Y := fun j p => p.val
    have hm : Monic m := (power_monic_iff m).2 (fun j _ _ h => Subtype.ext h)
    let g : X ⟶ Im := fun j a => ⟨f j a, a, rfl⟩
    have hgm : g ≫ m = f := rfl
    obtain ⟨inv, _, hinv2⟩ := hc m g hm hgm
    have hmb : m i (inv i b) = b := congrFun (congrFun hinv2 i) b
    obtain ⟨a, ha⟩ := (inv i b).property
    exact ⟨a, by rw [ha]; exact hmb⟩
  · intro hsurj
    let s : Y ⟶ X := fun j b => (hsurj j b).choose
    have hs : s ≫ f = Cat.id Y := by funext j b; exact (hsurj j b).choose_spec
    intro C m g hm hgm
    exact cover_of_section (e := f) s hs m g hm hgm

instance powerHasTerminal : HasTerminal (I → Type w) where
  one := fun _ => PUnit
  trm _ := fun _ _ => PUnit.unit
  uniq f g := by funext i x; rfl

instance powerHasBinaryProducts : HasBinaryProducts (I → Type w) where
  prod X Y := fun i => X i × Y i
  fst := fun _ p => p.1
  snd := fun _ p => p.2
  pair f g := fun i x => (f i x, g i x)
  fst_pair _ _ := rfl
  snd_pair _ _ := rfl
  pair_uniq f g h h₁ h₂ := by
    funext i x
    exact Prod.ext (congrFun (congrFun h₁ i) x) (congrFun (congrFun h₂ i) x)

instance powerHasPullbacks : HasPullbacks (I → Type w) where
  has {A B C} f g :=
    { cone :=
        { pt := fun i => {p : A i × B i // f i p.1 = g i p.2}
          π₁ := fun _ p => p.val.1
          π₂ := fun _ p => p.val.2
          w  := by funext i p; exact p.property }
      lift := fun c => fun i x => ⟨(c.π₁ i x, c.π₂ i x), congrFun (congrFun c.w i) x⟩
      lift_fst := fun _ => rfl
      lift_snd := fun _ => rfl
      lift_uniq := fun c u h₁ h₂ => by
        funext i x
        apply Subtype.ext
        exact Prod.ext (congrFun (congrFun h₁ i) x) (congrFun (congrFun h₂ i) x) }

/-- §1.51 (power): the image of `f` is the fibrewise image family. -/
def powerImage {X Y : I → Type w} (f : X ⟶ Y) : Subobject (I → Type w) Y where
  dom := fun i => {b : Y i // ∃ a, f i a = b}
  arr := fun _ p => p.val
  monic := (power_monic_iff _).2 (fun _ _ _ h => Subtype.ext h)

theorem power_isImage {X Y : I → Type w} (f : X ⟶ Y) : IsImage f (powerImage f) := by
  refine ⟨⟨fun i a => ⟨f i a, a, rfl⟩, rfl⟩, ?_⟩
  intro S hS
  obtain ⟨g, hg⟩ := hS
  refine ⟨fun i p => g i p.property.choose, ?_⟩
  funext i p
  obtain ⟨b, hb⟩ := p
  exact Eq.trans (congrFun (congrFun hg i) _) hb.choose_spec

instance powerHasImages : HasImages (I → Type w) where
  image f := powerImage f
  isImage f := power_isImage f

instance powerPullbacksTransferCovers : PullbacksTransferCovers (I → Type w) where
  pullbacks_transfer_covers {A B C f g} c hpb hf := by
    rw [power_cover_iff] at hf ⊢
    intro i b
    obtain ⟨a, ha⟩ := hf i (g i b)
    -- Pointed cone supported at `i`: `d.pt j = PLift (i = j)` carries `(a, b)` at `i`.
    let d : Cone f g :=
      { pt := fun j => ULift.{w} (PLift (i = j))
        π₁ := fun j p => p.down.down ▸ a
        π₂ := fun j p => p.down.down ▸ b
        w  := by funext j p; obtain ⟨⟨e⟩⟩ := p; cases e; simpa using ha }
    obtain ⟨u, ⟨_, hu₂⟩, _⟩ := hpb d
    refine ⟨u i (ULift.up (PLift.up rfl)), ?_⟩
    have hval := congrFun (congrFun hu₂ i) (ULift.up (PLift.up (rfl : i = i)))
    simpa using hval

/-- §1.521: the power category `Set^I = (I → Type w)` is regular. -/
instance powerRegular : RegularCategory (I → Type w) where
  toHasTerminal := powerHasTerminal
  toHasBinaryProducts := powerHasBinaryProducts
  toHasPullbacks := powerHasPullbacks
  toHasImages := powerHasImages
  toPullbacksTransferCovers := powerPullbacksTransferCovers

end SetRegular

/-! ## §2.218 BRICK 2c — the hom-representation `homRep 𝒞 : 𝒞 → 𝒮^|𝒞|` is a regular functor

  `homRep 𝒞 A i = (i ⟶ A)` is the §1.55 Henkin–Lubkin representation into the power
  `(𝒞 → Type u)` (= `Set^|𝒞|`, regular by BRICK 1).  A representable functor preserves all
  limits essentially definitionally (the universal property of products / pullbacks in `𝒞`
  IS the bijection `Hom(i, lim) ≅ lim Hom(i, –)`), and — when the source is CAPITAL (every
  object projective, the §1.543 case) — it preserves covers (`homRep_preserves_cover_pointwise`)
  and hence images.  We assemble the five `RegularFunctor` fields here; the structure itself
  lives in `RelCat`, so the packaged `RegularFunctor (homRep 𝒞)` is built there from these. -/

namespace HomRepRegular

open SetRegular

variable {𝒞 : Type u} [Cat.{u} 𝒞] [RegularCategory 𝒞]

/-- **`homRep` preserves binary products.**  The comparison `homRep(A×B) → homRep A × homRep B`,
    `h ↦ (h ≫ fst, h ≫ snd)`, has inverse `(p, q) ↦ ⟨p, q⟩` (the `𝒞`-pairing); both round-trips
    are the product universal property (`fst_pair`/`snd_pair`/`pair_uniq`). -/
theorem homRep_preserves_prod : PreservesBinaryProducts (homRep 𝒞) := by
  intro A B
  -- The comparison is `pair (map fst) (map snd)`; its fibrewise value at `h` is `(h ≫ fst, h ≫ snd)`.
  refine ⟨fun i pq => pair (pq.1) (pq.2), ?_, ?_⟩
  · -- comparison ≫ inverse = id on `homRep (prod A B)`
    funext i h
    -- `(pair (map fst)(map snd)) i h = (h ≫ fst, h ≫ snd)`; pairing recovers `h`.
    show pair ((h ≫ fst : i ⟶ A)) ((h ≫ snd : i ⟶ B)) = h
    exact (pair_uniq (h ≫ fst) (h ≫ snd) h rfl rfl).symm
  · -- inverse ≫ comparison = id on `prod (homRep A) (homRep B)`
    funext i pq
    -- `cmp i (pair pq.1 pq.2) = (pair pq.1 pq.2 ≫ fst, pair pq.1 pq.2 ≫ snd) = (pq.1, pq.2) = pq`.
    show ((pair pq.1 pq.2 ≫ fst : i ⟶ A), (pair pq.1 pq.2 ≫ snd : i ⟶ B)) = pq
    rw [fst_pair, snd_pair]
    rfl

/-- **`homRep` preserves pullbacks.**  A pullback square in `𝒞` is sent to a pullback square in
    `Set^|𝒞|`: at each index `i`, a fibrewise compatible pair `(x, y)` of arrows out of `i`
    glues, by the pullback's universal property, to a unique arrow `i → c.pt`. -/
theorem homRep_preserves_pullbacks : PreservesPullbacks (homRep 𝒞) := by
  intro A B C f g c hpb
  -- Goal: the image cone in `Set^|𝒞|` is a pullback, i.e. the canonical lift exists+unique.
  intro d
  -- At index `i` and element `x`, `d.π₁ i x : i ⟶ A`, `d.π₂ i x : i ⟶ B`, compatible after `f`/`g`.
  -- Package the fibre cone over `f, g` in `𝒞` with apex `i`.
  let leg₁ : ∀ i, d.pt i → (i ⟶ A) := fun i x => d.π₁ i x
  let leg₂ : ∀ i, d.pt i → (i ⟶ B) := fun i x => d.π₂ i x
  have hcompat : ∀ i (x : d.pt i), leg₁ i x ≫ f = leg₂ i x ≫ g := by
    intro i x
    have := congrFun (congrFun d.w i) x
    simpa [homRep, familyFunctor, homFunctor] using this
  let fibreCone : ∀ i, d.pt i → Cone f g := fun i x => Cone.mk i (leg₁ i x) (leg₂ i x) (hcompat i x)
  refine ⟨fun i x => (hpb (fibreCone i x)).choose, ?_, ?_⟩
  · constructor
    · funext i x
      show (hpb (fibreCone i x)).choose ≫ c.π₁ = leg₁ i x
      exact (hpb (fibreCone i x)).choose_spec.1.1
    · funext i x
      show (hpb (fibreCone i x)).choose ≫ c.π₂ = leg₂ i x
      exact (hpb (fibreCone i x)).choose_spec.1.2
  · intro u hu1 hu2
    funext i x
    -- uniqueness fibrewise: `u i x : i ⟶ c.pt` is also a lift, so equals the chosen one.
    refine (hpb (fibreCone i x)).choose_spec.2 (u i x) ?_ ?_
    · have := congrFun (congrFun hu1 i) x; simpa [homRep, familyFunctor, homFunctor] using this
    · have := congrFun (congrFun hu2 i) x; simpa [homRep, familyFunctor, homFunctor] using this

/-- **`homRep` preserves covers**, given the source is capital (every object projective, so every
    cover splits — the §1.543 situation).  A power morphism is a cover iff fibrewise surjective
    (`power_cover_iff`); `homRep_preserves_cover_pointwise` gives exactly fibrewise surjectivity. -/
theorem homRep_preserves_covers
    (hproj : ∀ C : 𝒞, ∀ {P : 𝒞} (e : P ⟶ C), Cover e → ∃ s : C ⟶ P, s ≫ e = Cat.id C) :
    PreservesCovers (homRep 𝒞) := by
  intro X Y f hf
  rw [power_cover_iff]
  intro i b
  obtain ⟨h', hh'⟩ := homRep_preserves_cover_pointwise hproj hf i b
  exact ⟨h', hh'⟩

/-- **`homRep` preserves images**, given the source is capital.  In a regular category
    `image f = cover ; mono` (the `image.lift` is a cover, `image.arr` a mono); `homRep` preserves
    both (`homRep_preserves_covers`, `homRep_preserves_mono`), and in `Set^|𝒞|` a cover-then-mono
    factorization IS the image (`image` of a cover∘mono is the mono).  We discharge the
    `PreservesImages` obligation directly: the pushed-forward image subobject allows `homRep f`
    and is minimal, because the cover `homRep (image.lift f)` is onto it. -/
theorem homRep_preserves_images
    (hproj : ∀ C : 𝒞, ∀ {P : 𝒞} (e : P ⟶ C), Cover e → ∃ s : C ⟶ P, s ≫ e = Cat.id C) :
    PreservesImages (homRep 𝒞) (homRep_preserves_mono 𝒞) := by
  intro A B f I hI
  -- `Subobject.map (homRep 𝒞) _ I` has arrow `homRep (I.arr)` (a mono) and allows `homRep f`.
  -- We show it is the image of `homRep f`.  Strategy: `homRep` preserves the cover `image.lift`.
  -- `hI : IsImage f I`.  The canonical image `image f` has `(image f).le I` and `I.le (image f)`
  -- (both images), but to stay general we work from `hI` directly via the cover onto `I`.
  -- The lift `ℓ : A → I.dom` with `ℓ ≫ I.arr = f` is a cover (since `I` is an image: `image f`
  -- minimal and `f` factors, the comparison is a cover).  We obtain it from `cover_iff`...
  -- Simpler: use that in a regular category, the image lift `image.lift f` is a cover and
  -- `(image f)` equals `I` up to iso; transport along the iso.
  -- We instead prove minimality of `Subobject.map _ I` by hand using the onto cover.
  -- Allows: `homRep f` factors through `homRep I.arr` via `homRep ℓ`.
  obtain ⟨ℓ, hℓ⟩ := hI.1
  -- ℓ ≫ I.arr = f, and ℓ is a cover (image lift is a cover; here `I` is an image of `f`).
  have hℓcov : Cover ℓ := by
    -- `ℓ : A → I.dom` with `ℓ ≫ I.arr = f`.  Since `I` is the image, `image.lift f` and `ℓ`
    -- both witness the factorization through a mono; `image.lift` is a cover and the
    -- comparison `image f ≅ I` makes `ℓ` a cover.
    have hImg : IsImage f (image f) := HasImages.isImage f
    -- comparison isos between the two images `image f` and `I`
    obtain ⟨k, hk⟩ := hImg.2 I hI.1
    obtain ⟨k', hk'⟩ := hI.2 (image f) hImg.1
    -- `k : (image f).dom → I.dom`, `k ≫ I.arr = (image f).arr`; `k' : I.dom → (image f).dom`.
    -- `k` is iso (mutually inverse via monic cancellation).
    have hkk' : k ≫ k' = Cat.id (image f).dom := by
      apply (image f).monic
      rw [Cat.assoc, hk', hk, Cat.id_comp]
    have hk'k : k' ≫ k = Cat.id I.dom := by
      apply I.monic
      rw [Cat.assoc, hk, hk', Cat.id_comp]
    -- `image.lift f : A → (image f).dom` is a cover; `ℓ = image.lift f ≫ k` (both monic-cancel
    -- to `f` through `I.arr`), so `ℓ` is a cover.
    have hlift : image.lift f ≫ k = ℓ := by
      apply I.monic
      rw [Cat.assoc, hk, image.lift_fac, hℓ]
    have hkcov : Cover k := iso_cover k ⟨k', hkk', hk'k⟩
    have hliftcov : Cover (image.lift f) := image_lift_cover f
    have : Cover (image.lift f ≫ k) := cover_comp hliftcov hkcov
    rwa [hlift] at this
  -- Now build `IsImage (homRep f) (Subobject.map (homRep 𝒞) _ I)`.
  refine ⟨⟨(homRepFunctor 𝒞).map ℓ, ?_⟩, ?_⟩
  · -- allows: `homRep ℓ ≫ homRep I.arr = homRep f`
    show (homRepFunctor 𝒞).map ℓ ≫ (homRepFunctor 𝒞).map I.arr = (homRepFunctor 𝒞).map f
    rw [← (homRepFunctor 𝒞).map_comp, hℓ]
  · -- minimality: any `S` allowing `homRep f` receives `Subobject.map _ I`.
    intro S hS
    obtain ⟨t, ht⟩ := hS
    -- `t : homRep A → S.dom`, `t ≫ S.arr = homRep f`.  Goal `(Subobject.map _ I).le S`: produce
    -- `r : homRep I.dom → S.dom` with `r ≫ S.arr = (Subobject.map _ I).arr = homRep I.arr`.
    -- `homRep ℓ` is a cover onto `homRep I.dom` (fibrewise surjective).
    have hℓcov' : Cover ((homRepFunctor 𝒞).map ℓ) := homRep_preserves_covers hproj ℓ hℓcov
    rw [power_cover_iff] at hℓcov'
    -- Fibrewise: pick ANY preimage `pre i y` of `y` under `homRep ℓ`; the value `t i (pre i y)`
    -- satisfies the required equation regardless of the choice (so no well-definedness needed):
    --   S.arr (t (pre y)) = homRep I.arr (homRep ℓ (pre y)) = homRep I.arr y.
    let pre : ∀ i, (homRep 𝒞 I.dom) i → (homRep 𝒞 A) i :=
      fun i y => (hℓcov' i y).choose
    have hpre : ∀ i y, (homRepFunctor 𝒞).map ℓ i (pre i y) = y :=
      fun i y => (hℓcov' i y).choose_spec
    -- `ht` fibrewise: `S.arr i (t i z) = (homRep f) i z = (homRep I.arr) i ((homRep ℓ) i z)`.
    have ht' : ∀ i z, S.arr i (t i z)
        = (homRepFunctor 𝒞).map I.arr i ((homRepFunctor 𝒞).map ℓ i z) := by
      intro i z
      have e1 : (homRepFunctor 𝒞).map f = (homRepFunctor 𝒞).map ℓ ≫ (homRepFunctor 𝒞).map I.arr := by
        rw [← (homRepFunctor 𝒞).map_comp, hℓ]
      have e2 : S.arr i (t i z) = (homRepFunctor 𝒞).map f i z := congrFun (congrFun ht i) z
      rw [e2, e1]; rfl
    refine ⟨fun i y => t i (pre i y), ?_⟩
    funext i y
    show S.arr i (t i (pre i y)) = (homRepFunctor 𝒞).map I.arr i y
    rw [ht' i (pre i y), hpre i y]

end HomRepRegular

end Freyd
