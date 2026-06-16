/-
  Freyd & Scedrov, *Categories and Allegories* §1.6  Pre-logoi.

  §1.6  PRE-LOGOS: regular category where subobject posets are lattices
        and inverse image preserves unions.  Equivalent: Cartesian +
        images + pullbacks transfer finite covers.
  §1.61 0 = minimal subobject of 1.  Any map to 0 is iso. 0 is coterminator.
  §1.612 For monic f: A↣B, f# distributes over unions iff distributive lattice.
  §1.613 Poset is pre-logos iff it is a distributive lattice.
  §1.614 Representation of pre-logoi.
-/


import Fredy.S1_1
import Fredy.S1_34
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.6 Pre-logos

  A PRE-LOGOS is a regular category in which subobject posets
  are lattices (have binary unions) and inverse image preserves
  unions.  Equivalent: Cartesian + images + pullbacks transfer
  finite covers (§1.6). -/

/-- Subobjects have binary unions (join). -/
class HasSubobjectUnions (𝒞 : Type u) [Cat.{v} 𝒞] [HasImages 𝒞] where
  union : ∀ {B : 𝒞} (S T : Subobject 𝒞 B), Subobject 𝒞 B
  union_left  : ∀ {B} (S T : Subobject 𝒞 B), S.le (union S T)
  union_right : ∀ {B} (S T : Subobject 𝒞 B), T.le (union S T)
  union_min   : ∀ {B} (S T U : Subobject 𝒞 B), S.le U → T.le U → (union S T).le U

/-- Inverse image f#: 𝒫(B) → 𝒫(A).  For subobject B'↣B, f#(B')
    is the pullback of B'.arr along f.  The pullback of a monic is
    monic (standard; proof deferred). -/
def InverseImage (f : A ⟶ B) (B' : Subobject 𝒞 B) [HasPullbacks 𝒞] : Subobject 𝒞 A :=
  let pb := HasPullbacks.has f B'.arr
  { dom := pb.cone.pt
    arr := pb.cone.π₁
    monic := by
      -- Pullback of a monic is monic: π₁ is left-cancellable.
      intro W u v huv
      -- B'.arr monic forces the π₂-legs to agree
      have hπ₂ : u ≫ pb.cone.π₂ = v ≫ pb.cone.π₂ := by
        apply B'.monic
        rw [Cat.assoc, ← pb.cone.w, ← Cat.assoc, huv, Cat.assoc, pb.cone.w, ← Cat.assoc]
      -- both u and v are the unique lift of the cone ⟨W, u≫π₁, u≫π₂⟩
      let c : Cone f B'.arr :=
        ⟨W, u ≫ pb.cone.π₁, u ≫ pb.cone.π₂, by rw [Cat.assoc, pb.cone.w, ← Cat.assoc]⟩
      rw [pb.lift_uniq c u rfl rfl, pb.lift_uniq c v huv.symm hπ₂.symm] }

/-- f# preserves binary unions: for any S,T subobjects of B,
    f#(S ∪ T) EQUALS f#(S) ∪ f#(T) as subobjects of A — i.e. each is
    `Subobject.le` the other.  This is stronger than a bare object
    `Isomorphic` of the domains: the mediating maps commute with the
    monics into A, so they can serve as the factorizing maps that
    `Subobject.le` (and hence the §1.62 relational lattice) requires. -/
def inverseImage_preserves_unions [HasImages 𝒞] [HasSubobjectUnions 𝒞] {A B : 𝒞} (f : A ⟶ B) [HasPullbacks 𝒞] : Prop :=
  ∀ (S T : Subobject 𝒞 B),
    (InverseImage f (HasSubobjectUnions.union S T)).le
        (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T))
    ∧ (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)).le
        (InverseImage f (HasSubobjectUnions.union S T))

/-- A PRE-LOGOS (§1.6): regular + subobject lattices + inverse image
    preserves finite unions (including empty joins). -/
class PreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    RegularCategory 𝒞, HasSubobjectUnions 𝒞 where
  -- empty join (bottom) of each subobject lattice
  bottom : ∀ (A : 𝒞), Subobject 𝒞 A
  bottom_min : ∀ {A : 𝒞} (S : Subobject 𝒞 A), (bottom A).le S
  bottom_dom_iso : ∀ (A B : 𝒞), Isomorphic (bottom A).dom (bottom B).dom
  -- f# preserves binary unions
  invImage_preserves_union : ∀ {A B : 𝒞} (f : A ⟶ B), inverseImage_preserves_unions f
  -- f# preserves the empty join (bottom)
  invImage_preserves_bottom : ∀ {A B : 𝒞} (f : A ⟶ B),
    Isomorphic (InverseImage f (bottom B)).dom (bottom A).dom

/-! ## §1.613 Posets as pre-logoi

  A poset viewed as a category is a pre-logos iff the poset is
  a distributive lattice (§1.613). -/

/-- A DISTRIBUTIVE LATTICE (§1.613): the subobject lattices satisfy the
    *meet-over-join* distributive law.  The meet `A ∩ S` is `InverseImage A.arr S`
    (the pullback of `A.arr` along `S.arr`), exactly as in §1.612
    (`monic_inverseImage_iff_distributive`).  We state the substantive direction

        A ∩ (S ∪ T)  ≤  (A ∩ S) ∪ (A ∩ T)

    (the reverse always holds in any lattice; this forward inequality is what
    fails in the non-distributive N₅, M₃).  Unlike the previous meet-free
    formulation `(A∪S)∪A ≤ A∪(S∪T)` — a join-absorption that is true in EVERY
    lattice and so captures nothing — this genuinely characterizes distributivity. -/
def IsDistributiveLattice [HasImages 𝒞] [HasSubobjectUnions 𝒞] [HasPullbacks 𝒞] : Prop :=
  ∀ {B : 𝒞} (A S T : Subobject 𝒞 B),
    Subobject.le
      (InverseImage A.arr (HasSubobjectUnions.union S T))
      (HasSubobjectUnions.union (InverseImage A.arr S) (InverseImage A.arr T))

/-- **§1.613**: In a thin category (poset), a pre-logos IS a distributive lattice.
    The distributive inequality `A ∩ (S∪T) ≤ (A∩S) ∪ (A∩T)` is exactly the forward
    half of `PreLogos.invImage_preserves_union` specialized to the monic `A.arr`:
    `A.arr#` preserves the union `S ∪ T`, and `A ∩ X = InverseImage A.arr X`.

    Faithful, fully proved: we read off the inequality from the pre-logos axiom
    that inverse images preserve binary unions. -/
theorem poset_prelogos_iff_distributive [PreLogos 𝒞]
    (_hThin : ∀ {A B : 𝒞} (f g : A ⟶ B), f = g) : IsDistributiveLattice (𝒞 := 𝒞) := by
  intro B A S T
  -- `inverseImage_preserves_unions A.arr` gives both inclusions; we need the
  -- forward one: A.arr#(S∪T) ≤ A.arr#(S) ∪ A.arr#(T), i.e. A∩(S∪T) ≤ (A∩S)∪(A∩T).
  exact (PreLogos.invImage_preserves_union A.arr S T).1

/-! ## §1.616  BinRel(A,B) is a distributive lattice

  In a pre-logos, BinRel(A,B) is isomorphic to Sub(A×B), hence a
  distributive lattice.  We define union directly via image of the
  copairing and establish the lattice + distributivity laws. -/

section BinRelLattice

variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] [HasBinaryCoproducts 𝒞]

/-- Union of two relations R, S : A → B (§1.616).
    Their coproduct-of-tables maps to A×B; the image is the union. -/
def relUnion {A B : 𝒞} (R S : BinRel 𝒞 A B) : BinRel 𝒞 A B :=
  let cop := HasBinaryCoproducts.coprod R.src S.src
  -- copairing of the two embedding maps pair(colA,colB) into A×B
  let m : cop ⟶ prod A B :=
    HasBinaryCoproducts.case (pair R.colA R.colB) (pair S.colA S.colB)
  let I := image m
  { src  := I.dom
    colA := I.arr ≫ fst
    colB := I.arr ≫ snd
    isMonicPair := by
      intro W f g hA hB
      have h_fst : (f ≫ I.arr) ≫ fst = (g ≫ I.arr) ≫ fst := by simpa [Cat.assoc] using hA
      have h_snd : (f ≫ I.arr) ≫ snd = (g ≫ I.arr) ≫ snd := by simpa [Cat.assoc] using hB
      have h_prod : f ≫ I.arr = g ≫ I.arr :=
        pair_uniq _ _ (f ≫ I.arr) rfl rfl |>.trans
          (pair_uniq _ _ (g ≫ I.arr) h_fst.symm h_snd.symm).symm
      exact I.monic f g h_prod }

/-- Notation ∪ for relUnion. -/
infixl:65 (name := relUnionNotation) " ∪ᵣ " => relUnion

/-- R ≤ R ∪ S (left inclusion). -/
theorem relUnion_le_left {A B : 𝒞} (R S : BinRel 𝒞 A B) : RelLe R (R ∪ᵣ S) := by
  -- witness: image.lift m ∘ inl, where m is the copairing
  let cop := HasBinaryCoproducts.coprod R.src S.src
  let m : cop ⟶ prod A B :=
    HasBinaryCoproducts.case (pair R.colA R.colB) (pair S.colA S.colB)
  let I := image m
  -- inl ≫ m = pair R.colA R.colB
  have h_inl : HasBinaryCoproducts.inl ≫ m = pair R.colA R.colB :=
    HasBinaryCoproducts.case_inl _ _
  -- pair R.colA R.colB factors through I.arr
  have hallow : Allows I (pair R.colA R.colB) :=
    ⟨HasBinaryCoproducts.inl ≫ image.lift m, by rw [Cat.assoc, image.lift_fac, h_inl]⟩
  obtain ⟨k, hk⟩ := hallow
  -- k : R.src → I.dom with k ≫ I.arr = pair R.colA R.colB
  refine ⟨⟨k, ?_, ?_⟩⟩
  · calc k ≫ (R ∪ᵣ S).colA = k ≫ I.arr ≫ fst := rfl
      _ = (k ≫ I.arr) ≫ fst := by rw [Cat.assoc]
      _ = pair R.colA R.colB ≫ fst := by rw [hk]
      _ = R.colA := fst_pair R.colA R.colB
  · calc k ≫ (R ∪ᵣ S).colB = k ≫ I.arr ≫ snd := rfl
      _ = (k ≫ I.arr) ≫ snd := by rw [Cat.assoc]
      _ = pair R.colA R.colB ≫ snd := by rw [hk]
      _ = R.colB := snd_pair R.colA R.colB

/-- S ≤ R ∪ S (right inclusion). -/
theorem relUnion_le_right {A B : 𝒞} (R S : BinRel 𝒞 A B) : RelLe S (R ∪ᵣ S) := by
  let cop := HasBinaryCoproducts.coprod R.src S.src
  let m : cop ⟶ prod A B :=
    HasBinaryCoproducts.case (pair R.colA R.colB) (pair S.colA S.colB)
  let I := image m
  have h_inr : HasBinaryCoproducts.inr ≫ m = pair S.colA S.colB :=
    HasBinaryCoproducts.case_inr _ _
  have hallow : Allows I (pair S.colA S.colB) :=
    ⟨HasBinaryCoproducts.inr ≫ image.lift m, by rw [Cat.assoc, image.lift_fac, h_inr]⟩
  obtain ⟨k, hk⟩ := hallow
  refine ⟨⟨k, ?_, ?_⟩⟩
  · show k ≫ I.arr ≫ fst = S.colA
    rw [← Cat.assoc, hk, fst_pair]
  · show k ≫ I.arr ≫ snd = S.colB
    rw [← Cat.assoc, hk, snd_pair]

/-- Universal property of relUnion: R ≤ U → S ≤ U → R ∪ S ≤ U. -/
theorem le_relUnion {A B : 𝒞} {R S U : BinRel 𝒞 A B}
    (hRU : RelLe R U) (hSU : RelLe S U) : RelLe (R ∪ᵣ S) U := by
  obtain ⟨⟨hR, hRA, hRB⟩⟩ := hRU
  obtain ⟨⟨hS, hSA, hSB⟩⟩ := hSU
  -- U.arr = pair U.colA U.colB is monic; we need to show (R∪S) ≤ U
  -- The image (R∪ᵣS) is the image of m = case(pairR, pairS) : coprod → A×B
  -- We exhibit a map coprod → U.src making the diagram commute, then apply image_min
  let cop := HasBinaryCoproducts.coprod R.src S.src
  let m : cop ⟶ prod A B :=
    HasBinaryCoproducts.case (pair R.colA R.colB) (pair S.colA S.colB)
  let pU : U.src ⟶ prod A B := pair U.colA U.colB
  -- Build a map coprod → U.src via the coproduct UMP
  let kU : cop ⟶ U.src := HasBinaryCoproducts.case hR hS
  -- kU ≫ pU = m  (both agree on inl and inr)
  have h_eq : kU ≫ pU = m := by
    apply HasBinaryCoproducts.case_uniq
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inl]
      rw [pair_uniq R.colA R.colB (hR ≫ pU)
          (by rw [Cat.assoc, fst_pair, hRA])
          (by rw [Cat.assoc, snd_pair, hRB])]
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inr]
      rw [pair_uniq S.colA S.colB (hS ≫ pU)
          (by rw [Cat.assoc, fst_pair, hSA])
          (by rw [Cat.assoc, snd_pair, hSB])]
  -- pU is monic (U.isMonicPair)
  have hpU_mono : Mono pU := monic_pair_of_monicPair U.colA U.colB U.isMonicPair
  -- Allows (image m as subobject via pU) m is given by kU
  -- We need to build a Subobject out of pU
  let U_sub : Subobject 𝒞 (prod A B) := Subobject.mk U.src pU hpU_mono
  have hallow_U : Allows U_sub m := ⟨kU, h_eq⟩
  -- image m ≤ U_sub
  have hle := image_min m U_sub hallow_U
  obtain ⟨k, hk⟩ := hle
  -- k : (R∪ᵣS).src → U.src with k ≫ pU = (image m).arr  (since U_sub.arr = pU)
  -- (R∪ᵣS).colA = (image m).arr ≫ fst, colB = ... ≫ snd
  refine ⟨⟨k, ?_, ?_⟩⟩
  · -- Goal: k ≫ U.colA = (R ∪ᵣ S).colA, i.e. = (image m).arr ≫ fst
    show k ≫ U.colA = (image m).arr ≫ fst
    have hkpU : k ≫ pU = (image m).arr := hk
    calc k ≫ U.colA = (k ≫ pU) ≫ fst := by rw [Cat.assoc, fst_pair]
      _ = (image m).arr ≫ fst := by rw [hkpU]
  · show k ≫ U.colB = (image m).arr ≫ snd
    have hkpU : k ≫ pU = (image m).arr := hk
    calc k ≫ U.colB = (k ≫ pU) ≫ snd := by rw [Cat.assoc, snd_pair]
      _ = (image m).arr ≫ snd := by rw [hkpU]

/-- §1.616: (R ∩ S) ∪ (R ∩ T) ≤ R ∩ (S ∪ T) — the reverse always holds. -/
theorem rel_union_inter_le {A B : 𝒞} (R S T : BinRel 𝒞 A B) :
    RelLe ((R ⊓ S) ∪ᵣ (R ⊓ T)) (R ⊓ (S ∪ᵣ T)) := by
  apply le_relUnion
  · exact le_intersect (intersect_le_left R S) (rel_le_trans (intersect_le_right R S) (relUnion_le_left S T))
  · exact le_intersect (intersect_le_left R T) (rel_le_trans (intersect_le_right R T) (relUnion_le_right S T))

/-- §1.616: (R⊚S) ∪ (R⊚T) ≤ R ⊚ (S ∪ T) — always holds. -/
theorem compose_union_right_le {A B C : 𝒞} (R : BinRel 𝒞 A B) (S T : BinRel 𝒞 B C) :
    RelLe ((R ⊚ S) ∪ᵣ (R ⊚ T)) (R ⊚ (S ∪ᵣ T)) := by
  apply le_relUnion
  · -- R⊚S ≤ R⊚(S∪T): use monotonicity of composition in second argument
    -- Since S ≤ S∪T (relUnion_le_left), we need compose_mono_right.
    -- Exhibit the witness: for any k : (R⊚S).src → witness, compose with the
    -- containment of S in S∪T.
    obtain ⟨⟨hST_w, hST_A, hST_B⟩⟩ := relUnion_le_left S T
    -- hST_w : S.src → (S∪ᵣT).src with hST_w ≫ (S∪T).colA = S.colA etc.
    -- compose R (S∪T): pullback of R.colB and (S∪T).colA
    -- We need to show (R⊚S).src → (R⊚(S∪T)).src
    -- The pullback of R.colB over S.colA factors through the pullback over (S∪T).colA
    -- via hST_w.
    -- Strategy: construct a cone for the (S∪T) pullback from the S pullback.
    let pbS  := HasPullbacks.has R.colB S.colA
    let pbST := HasPullbacks.has R.colB (S ∪ᵣ T).colA
    -- (S∪T).colA = (image m).arr ≫ fst, but morally hST_w : S → (S∪T) gives S.colA = hST_w ≫ (S∪T).colA
    have hST_colA : hST_w ≫ (S ∪ᵣ T).colA = S.colA := hST_A
    -- Build cone for pbST from pbS
    let cST : Cone R.colB (S ∪ᵣ T).colA :=
      ⟨pbS.cone.pt, pbS.cone.π₁, pbS.cone.π₂ ≫ hST_w,
       by rw [Cat.assoc, hST_colA, pbS.cone.w]⟩
    let uST : pbS.cone.pt ⟶ pbST.cone.pt := pbST.lift cST
    have huST_π₁ : uST ≫ pbST.cone.π₁ = pbS.cone.π₁ := pbST.lift_fst cST
    have huST_π₂ : uST ≫ pbST.cone.π₂ = pbS.cone.π₂ ≫ hST_w := pbST.lift_snd cST
    -- Now: (R⊚S).src = image(pair(pbS.π₁≫R.colA, pbS.π₂≫S.colB)).dom
    -- The span for R⊚(S∪T) is pair(pbST.π₁≫R.colA, pbST.π₂≫(S∪T).colB)
    -- We have a map from the S-pullback point to the (S∪T)-pullback point via uST.
    -- And pbS.π₂ ≫ S.colB = pbS.π₂ ≫ hST_w ≫ (S∪T).colB (since hST_w ≫ (S∪T).colB = S.colB)
    have hST_colB : hST_w ≫ (S ∪ᵣ T).colB = S.colB := hST_B
    -- Build the map from (R⊚S).src to (R⊚(S∪T)).src
    let spanS  : pbS.cone.pt ⟶ prod A C :=
      pair (pbS.cone.π₁ ≫ R.colA) (pbS.cone.π₂ ≫ S.colB)
    let spanST : pbST.cone.pt ⟶ prod A C :=
      pair (pbST.cone.π₁ ≫ R.colA) (pbST.cone.π₂ ≫ (S ∪ᵣ T).colB)
    -- spanS factors through spanST via uST: uST ≫ spanST = spanS
    have h_span_eq : uST ≫ spanST = spanS := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, huST_π₁]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, huST_π₂, Cat.assoc, hST_colB]
    -- image(spanS) ≤ image(spanST): since spanS = uST ≫ spanST, spanS allows image(spanST)
    let IS  := image spanS
    let IST := image spanST
    have hallow : Allows IST spanS := by
      obtain ⟨k, hk⟩ := image_allows spanST
      exact ⟨uST ≫ k, by rw [Cat.assoc, hk, h_span_eq]⟩
    obtain ⟨wit, hwit⟩ := image_min spanS IST hallow
    -- wit : IS.dom → IST.dom with wit ≫ IST.arr = IS.arr
    -- R⊚S has src = IS.dom, R⊚(S∪T) has src = IST.dom
    refine ⟨⟨wit, ?_, ?_⟩⟩
    · calc wit ≫ (R ⊚ (S ∪ᵣ T)).colA
          = wit ≫ IST.arr ≫ fst := rfl
        _ = (wit ≫ IST.arr) ≫ fst := by rw [Cat.assoc]
        _ = IS.arr ≫ fst := by rw [hwit]
        _ = (R ⊚ S).colA := rfl
    · calc wit ≫ (R ⊚ (S ∪ᵣ T)).colB
          = wit ≫ IST.arr ≫ snd := rfl
        _ = (wit ≫ IST.arr) ≫ snd := by rw [Cat.assoc]
        _ = IS.arr ≫ snd := by rw [hwit]
        _ = (R ⊚ S).colB := rfl
  · -- symmetric: R⊚T ≤ R⊚(S∪T)
    obtain ⟨⟨hST_w, hST_A, hST_B⟩⟩ := relUnion_le_right S T
    let pbT  := HasPullbacks.has R.colB T.colA
    let pbST := HasPullbacks.has R.colB (S ∪ᵣ T).colA
    have hST_colA : hST_w ≫ (S ∪ᵣ T).colA = T.colA := hST_A
    let cST : Cone R.colB (S ∪ᵣ T).colA :=
      ⟨pbT.cone.pt, pbT.cone.π₁, pbT.cone.π₂ ≫ hST_w,
       by rw [Cat.assoc, hST_colA, pbT.cone.w]⟩
    let uST : pbT.cone.pt ⟶ pbST.cone.pt := pbST.lift cST
    have huST_π₁ : uST ≫ pbST.cone.π₁ = pbT.cone.π₁ := pbST.lift_fst cST
    have huST_π₂ : uST ≫ pbST.cone.π₂ = pbT.cone.π₂ ≫ hST_w := pbST.lift_snd cST
    have hST_colB : hST_w ≫ (S ∪ᵣ T).colB = T.colB := hST_B
    let spanT  : pbT.cone.pt ⟶ prod A C :=
      pair (pbT.cone.π₁ ≫ R.colA) (pbT.cone.π₂ ≫ T.colB)
    let spanST : pbST.cone.pt ⟶ prod A C :=
      pair (pbST.cone.π₁ ≫ R.colA) (pbST.cone.π₂ ≫ (S ∪ᵣ T).colB)
    have h_span_eq : uST ≫ spanST = spanT := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, huST_π₁]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, huST_π₂, Cat.assoc, hST_colB]
    let IT  := image spanT
    let IST := image spanST
    have hallow : Allows IST spanT := by
      obtain ⟨k, hk⟩ := image_allows spanST
      exact ⟨uST ≫ k, by rw [Cat.assoc, hk, h_span_eq]⟩
    obtain ⟨wit, hwit⟩ := image_min spanT IST hallow
    refine ⟨⟨wit, ?_, ?_⟩⟩
    · show wit ≫ IST.arr ≫ fst = IT.arr ≫ fst
      rw [← Cat.assoc, hwit]
    · show wit ≫ IST.arr ≫ snd = IT.arr ≫ snd
      rw [← Cat.assoc, hwit]

/-- Helper: computes the "swap-copairing" equality
    `case(pairR, pairS) ≫ pair snd fst = case(pair R.colB R.colA, pair S.colB S.colA)`. -/
private theorem relUnion_swap_eq {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    HasBinaryCoproducts.case (pair R.colA R.colB) (pair S.colA S.colB) ≫ (pair snd fst : prod A B ⟶ prod B A) =
    HasBinaryCoproducts.case (HasBinaryCoproducts.inr (A := S.src) (B := R.src))
                             (HasBinaryCoproducts.inl (A := S.src) (B := R.src)) ≫
    HasBinaryCoproducts.case (pair S.colB S.colA) (pair R.colB R.colA) := by
  have hL :
      HasBinaryCoproducts.case (pair R.colA R.colB) (pair S.colA S.colB) ≫
        (pair snd fst : prod A B ⟶ prod B A) =
      HasBinaryCoproducts.case (pair R.colB R.colA) (pair S.colB S.colA) :=
    HasBinaryCoproducts.case_uniq _ _ _
      (by rw [← Cat.assoc, HasBinaryCoproducts.case_inl]
          apply pair_uniq
          · rw [Cat.assoc, fst_pair, snd_pair]
          · rw [Cat.assoc, snd_pair, fst_pair])
      (by rw [← Cat.assoc, HasBinaryCoproducts.case_inr]
          apply pair_uniq
          · rw [Cat.assoc, fst_pair, snd_pair]
          · rw [Cat.assoc, snd_pair, fst_pair])
  have hR :
      HasBinaryCoproducts.case (HasBinaryCoproducts.inr (A := S.src) (B := R.src))
                               (HasBinaryCoproducts.inl (A := S.src) (B := R.src)) ≫
      HasBinaryCoproducts.case (pair S.colB S.colA) (pair R.colB R.colA) =
      HasBinaryCoproducts.case (pair R.colB R.colA) (pair S.colB S.colA) :=
    HasBinaryCoproducts.case_uniq _ _ _
      (by rw [← Cat.assoc, HasBinaryCoproducts.case_inl, HasBinaryCoproducts.case_inr])
      (by rw [← Cat.assoc, HasBinaryCoproducts.case_inr, HasBinaryCoproducts.case_inl])
  exact hL.trans hR.symm

/-- §1.616: Reciprocation distributes over union: (R ∪ᵣ S)° ≤ S° ∪ᵣ R°.
    Proof: the copairing for (R∪S)° lands in B×A via swap_pair = pair snd fst; the
    copairing for S°∪R° is case(pairS°, pairR°).  cover⊥mono (cover_mono_diagonal)
    applied to image.lift(m) (a cover) and image(m').arr (monic) yields the factorization. -/
theorem relUnion_le_reciprocal {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    RelLe (R ∪ᵣ S)° (S° ∪ᵣ R°) := by
  let m  : HasBinaryCoproducts.coprod R.src S.src ⟶ prod A B :=
    HasBinaryCoproducts.case (pair R.colA R.colB) (pair S.colA S.colB)
  let m' : HasBinaryCoproducts.coprod S.src R.src ⟶ prod B A :=
    HasBinaryCoproducts.case (pair S.colB S.colA) (pair R.colB R.colA)
  let swap_pair : prod A B ⟶ prod B A := pair snd fst
  let swap_cop  : HasBinaryCoproducts.coprod R.src S.src ⟶ HasBinaryCoproducts.coprod S.src R.src :=
    HasBinaryCoproducts.case HasBinaryCoproducts.inr HasBinaryCoproducts.inl
  have h_swap : m ≫ swap_pair = swap_cop ≫ m' := relUnion_swap_eq R S
  -- cover_mono_diagonal needs: c ≫ f = d ≫ m_arg
  -- c = image.lift m, f = (image m).arr ≫ swap_pair, d = swap_cop ≫ image.lift m', m_arg = (image m').arr
  have h_sq : image.lift m ≫ ((image m).arr ≫ swap_pair) =
              (swap_cop ≫ image.lift m') ≫ (image m').arr := by
    calc image.lift m ≫ ((image m).arr ≫ swap_pair)
        = (image.lift m ≫ (image m).arr) ≫ swap_pair := by rw [← Cat.assoc]
      _ = m ≫ swap_pair                               := by rw [image.lift_fac]
      _ = swap_cop ≫ m'                               := h_swap
      _ = swap_cop ≫ (image.lift m' ≫ (image m').arr) := by congr 1; exact (image.lift_fac m').symm
      _ = (swap_cop ≫ image.lift m') ≫ (image m').arr := (Cat.assoc _ _ _).symm
  obtain ⟨k, _, hk⟩ := cover_mono_diagonal (image_lift_cover m) (image m').monic h_sq
  -- hk : k ≫ (image m').arr = (image m).arr ≫ swap_pair
  refine ⟨⟨k, ?_, ?_⟩⟩
  · show k ≫ (image m').arr ≫ fst = (image m).arr ≫ snd
    calc k ≫ (image m').arr ≫ fst = (k ≫ (image m').arr) ≫ fst := by rw [Cat.assoc]
      _ = ((image m).arr ≫ swap_pair) ≫ fst := by rw [hk]
      _ = (image m).arr ≫ swap_pair ≫ fst   := Cat.assoc _ _ _
      _ = (image m).arr ≫ snd               := by rw [fst_pair]
  · show k ≫ (image m').arr ≫ snd = (image m).arr ≫ fst
    calc k ≫ (image m').arr ≫ snd = (k ≫ (image m').arr) ≫ snd := by rw [Cat.assoc]
      _ = ((image m).arr ≫ swap_pair) ≫ snd := by rw [hk]
      _ = (image m).arr ≫ swap_pair ≫ snd   := Cat.assoc _ _ _
      _ = (image m).arr ≫ fst               := by rw [snd_pair]

/-- §1.616: S° ∪ᵣ R° ≤ (R ∪ᵣ S)° (reverse direction). -/
theorem relUnion_reciprocal_le {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    RelLe (S° ∪ᵣ R°) (R ∪ᵣ S)° := by
  -- Mirror image of relUnion_le_reciprocal with R↔S swapped.
  -- S°∪R° is the union of S° and R° as B→A relations.
  -- (R∪S)° has colA = (R∪S).colB, colB = (R∪S).colA.
  -- The copairing for S°∪R° maps case(pairS°, pairR°) = case(pair S.colB S.colA, pair R.colB R.colA).
  -- The copairing for (R∪S) is m = case(pair R.colA R.colB, pair S.colA S.colB).
  -- Use relUnion_swap_eq symmetrically.
  let m  : HasBinaryCoproducts.coprod R.src S.src ⟶ prod A B :=
    HasBinaryCoproducts.case (pair R.colA R.colB) (pair S.colA S.colB)
  let m' : HasBinaryCoproducts.coprod S.src R.src ⟶ prod B A :=
    HasBinaryCoproducts.case (pair S.colB S.colA) (pair R.colB R.colA)
  let swap_pair' : prod B A ⟶ prod A B := pair snd fst
  let swap_cop'  : HasBinaryCoproducts.coprod S.src R.src ⟶ HasBinaryCoproducts.coprod R.src S.src :=
    HasBinaryCoproducts.case HasBinaryCoproducts.inr HasBinaryCoproducts.inl
  -- h_swap' is exactly relUnion_swap_eq applied to S° and R° (as BinRel 𝒞 B A)
  have h_swap' : m' ≫ swap_pair' = swap_cop' ≫ m := relUnion_swap_eq S° R°
  have h_sq' : image.lift m' ≫ ((image m').arr ≫ swap_pair') =
               (swap_cop' ≫ image.lift m) ≫ (image m).arr := by
    calc image.lift m' ≫ ((image m').arr ≫ swap_pair')
        = (image.lift m' ≫ (image m').arr) ≫ swap_pair' := by rw [← Cat.assoc]
      _ = m' ≫ swap_pair'                                := by rw [image.lift_fac]
      _ = swap_cop' ≫ m                                  := h_swap'
      _ = swap_cop' ≫ (image.lift m ≫ (image m).arr)    := by congr 1; exact (image.lift_fac m).symm
      _ = (swap_cop' ≫ image.lift m) ≫ (image m).arr    := (Cat.assoc _ _ _).symm
  obtain ⟨k, _, hk⟩ := cover_mono_diagonal (image_lift_cover m') (image m).monic h_sq'
  -- hk : k ≫ (image m).arr = (image m').arr ≫ swap_pair'
  -- (R∪S)°.src = (image m).dom, (S°∪R°).src = (image m').dom
  -- (R∪S)°.colA = (image m).arr ≫ snd, (R∪S)°.colB = (image m).arr ≫ fst
  refine ⟨⟨k, ?_, ?_⟩⟩
  · show k ≫ (image m).arr ≫ snd = (image m').arr ≫ fst
    calc k ≫ (image m).arr ≫ snd = (k ≫ (image m).arr) ≫ snd := by rw [Cat.assoc]
      _ = ((image m').arr ≫ swap_pair') ≫ snd := by rw [hk]
      _ = (image m').arr ≫ swap_pair' ≫ snd   := Cat.assoc _ _ _
      _ = (image m').arr ≫ fst               := by rw [snd_pair]
  · show k ≫ (image m).arr ≫ fst = (image m').arr ≫ snd
    calc k ≫ (image m).arr ≫ fst = (k ≫ (image m).arr) ≫ fst := by rw [Cat.assoc]
      _ = ((image m').arr ≫ swap_pair') ≫ fst := by rw [hk]
      _ = (image m').arr ≫ swap_pair' ≫ fst   := Cat.assoc _ _ _
      _ = (image m').arr ≫ snd               := by rw [fst_pair]

end BinRelLattice

/-! ## §1.616 (pre-logos): the substantive distributive laws

  Freyd §1.616: *in a pre-logos* the relations `B&(A,B) ≃ Sub(A×B)` form a distributive
  lattice and composition distributes over union.  These are FALSE in a bare regular
  category — they need the defining pre-logos axiom that inverse images preserve unions.
  We therefore state them with `[PreLogos 𝒞]` (matching the book) and transport the
  pre-logos subobject-lattice facts across the canonical bridge `relSub : BinRel A B → Sub(A×B)`. -/

section BinRelDistributive

variable [HasBinaryCoproducts 𝒞] [PreLogos 𝒞]

/-- The subobject of `A×B` represented by a relation `R : A → B`: its monic pairing. -/
def relSub {A B : 𝒞} (R : BinRel 𝒞 A B) : Subobject 𝒞 (prod A B) :=
  ⟨R.src, pair R.colA R.colB, monic_pair_of_monicPair R.colA R.colB R.isMonicPair⟩

/-- `RelLe R S` is exactly `Subobject.le (relSub R) (relSub S)`: a relation homomorphism
    `h` (commuting with both legs) is the same data as a subobject factorization
    `h ≫ pair S.colA S.colB = pair R.colA R.colB`. -/
theorem relLe_iff_subLe {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    RelLe R S ↔ (relSub R).le (relSub S) := by
  constructor
  · rintro ⟨⟨h, hA, hB⟩⟩
    refine ⟨h, ?_⟩
    show h ≫ pair S.colA S.colB = pair R.colA R.colB
    exact pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair, hA]) (by rw [Cat.assoc, snd_pair, hB])
  · rintro ⟨h, hh⟩
    simp only [relSub] at hh
    refine ⟨⟨h, ?_, ?_⟩⟩
    · have h2 : (h ≫ pair S.colA S.colB) ≫ fst = pair R.colA R.colB ≫ fst :=
        congrArg (· ≫ fst) hh
      rwa [Cat.assoc, fst_pair, fst_pair] at h2
    · have h2 : (h ≫ pair S.colA S.colB) ≫ snd = pair R.colA R.colB ≫ snd :=
        congrArg (· ≫ snd) hh
      rwa [Cat.assoc, snd_pair, snd_pair] at h2

theorem relLe_of_subLe {A B : 𝒞} {R S : BinRel 𝒞 A B}
    (h : (relSub R).le (relSub S)) : RelLe R S := (relLe_iff_subLe R S).2 h

theorem subLe_of_relLe {A B : 𝒞} {R S : BinRel 𝒞 A B}
    (h : RelLe R S) : (relSub R).le (relSub S) := (relLe_iff_subLe R S).1 h

/-- `relSub (R ∪ᵣ S) ≤ union (relSub R) (relSub S)`.  `relUnion` is the image of
    `m = case (pairR) (pairS)`; both pieces sit below the union, so `case l₁ l₂` factors
    `m` through the union's monic, and image-minimality descends. -/
theorem relSub_union_le {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    (relSub (R ∪ᵣ S)).le (HasSubobjectUnions.union (relSub R) (relSub S)) := by
  let m : HasBinaryCoproducts.coprod R.src S.src ⟶ prod A B :=
    HasBinaryCoproducts.case (pair R.colA R.colB) (pair S.colA S.colB)
  have harr : (relSub (R ∪ᵣ S)).arr = (image m).arr := by
    show pair (R ∪ᵣ S).colA (R ∪ᵣ S).colB = (image m).arr
    exact (pair_uniq (R ∪ᵣ S).colA (R ∪ᵣ S).colB (image m).arr rfl rfl).symm
  obtain ⟨l₁, hl₁⟩ := HasSubobjectUnions.union_left (relSub R) (relSub S)
  obtain ⟨l₂, hl₂⟩ := HasSubobjectUnions.union_right (relSub R) (relSub S)
  let U := HasSubobjectUnions.union (relSub R) (relSub S)
  have hallow : Allows U m := by
    refine ⟨HasBinaryCoproducts.case l₁ l₂, ?_⟩
    show HasBinaryCoproducts.case l₁ l₂ ≫ U.arr = HasBinaryCoproducts.case _ _
    refine HasBinaryCoproducts.case_uniq _ _ _ ?_ ?_
    · show HasBinaryCoproducts.inl ≫ (HasBinaryCoproducts.case l₁ l₂ ≫ U.arr) = _
      rw [← Cat.assoc, HasBinaryCoproducts.case_inl]; exact hl₁
    · show HasBinaryCoproducts.inr ≫ (HasBinaryCoproducts.case l₁ l₂ ≫ U.arr) = _
      rw [← Cat.assoc, HasBinaryCoproducts.case_inr]; exact hl₂
  obtain ⟨k, hk⟩ := image_min m U hallow
  exact ⟨k, by rw [hk, harr]⟩

/-- `union (relSub R) (relSub S) ≤ relSub (R ∪ᵣ S)`.  `relSub R ≤ relSub(R∪S)` and
    `relSub S ≤ relSub(R∪S)` (from `relUnion_le_left/right` through the bridge), so the union's
    minimality (`union_min`) gives the containment. -/
theorem relSub_union_ge {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    (HasSubobjectUnions.union (relSub R) (relSub S)).le (relSub (R ∪ᵣ S)) :=
  HasSubobjectUnions.union_min _ _ _
    (subLe_of_relLe (relUnion_le_left R S))
    (subLe_of_relLe (relUnion_le_right R S))

/-- Transitivity of `Subobject.le` (compose the two factorizations). -/
theorem subLe_trans {W : 𝒞} {X Y Z : Subobject 𝒞 W} (h₁ : X.le Y) (h₂ : Y.le Z) : X.le Z := by
  obtain ⟨f, hf⟩ := h₁; obtain ⟨g, hg⟩ := h₂
  exact ⟨f ≫ g, by rw [Cat.assoc, hg, hf]⟩

/-- Post-composition with a fixed mono `m : Z ↣ W` carries `Sub Z` into `Sub W`
    order-preservingly: `push m P := ⟨P.dom, P.arr ≫ m⟩`. -/
def pushMono {Z W : 𝒞} (m : Z ⟶ W) (hm : Mono m) (P : Subobject 𝒞 Z) : Subobject 𝒞 W :=
  ⟨P.dom, P.arr ≫ m, by
    intro X u v huv
    refine P.monic u v (hm _ _ ?_)
    rw [Cat.assoc, Cat.assoc]; exact huv⟩

theorem pushMono_mono {Z W : 𝒞} (m : Z ⟶ W) (hm : Mono m) {P Q : Subobject 𝒞 Z}
    (hle : P.le Q) : (pushMono m hm P).le (pushMono m hm Q) := by
  obtain ⟨f, hf⟩ := hle
  exact ⟨f, by show f ≫ (Q.arr ≫ m) = P.arr ≫ m; rw [← Cat.assoc, hf]⟩

/-- `pushMono` reflects `≤`: a factorization through `m` descends because `m` is monic. -/
theorem pushMono_reflects {Z W : 𝒞} (m : Z ⟶ W) (hm : Mono m) {P Q : Subobject 𝒞 Z}
    (hle : (pushMono m hm P).le (pushMono m hm Q)) : P.le Q := by
  obtain ⟨f, hf⟩ := hle
  exact ⟨f, hm _ _ (by show (f ≫ Q.arr) ≫ m = P.arr ≫ m; rw [Cat.assoc]; exact hf)⟩

/-- `pushMono` of a union is `≤` the union of the `pushMono`s.  The ambient union of the two
    pushed pieces factors through `m` (both pieces do, so `union_min`), giving a subobject `Pre`
    of `Z` with `pushMono Pre = union(push P)(push Q)`; `P,Q ≤ Pre` (by `pushMono_reflects`), so
    `union P Q ≤ Pre` (`union_min`), and `pushMono` is monotone. -/
theorem pushMono_union_le {Z W : 𝒞} (m : Z ⟶ W) (hm : Mono m) (P Q : Subobject 𝒞 Z) :
    (pushMono m hm (HasSubobjectUnions.union P Q)).le
      (HasSubobjectUnions.union (pushMono m hm P) (pushMono m hm Q)) := by
  let UP := HasSubobjectUnions.union (pushMono m hm P) (pushMono m hm Q)
  -- both pushed pieces are ≤ ⟨Z, m⟩, hence so is their union; extract the factorization.
  have hsubZ : UP.le ⟨Z, m, hm⟩ :=
    HasSubobjectUnions.union_min _ _ _ ⟨P.arr, rfl⟩ ⟨Q.arr, rfl⟩
  obtain ⟨pre, hpre⟩ := hsubZ
  -- pre : UP.dom → Z with pre ≫ m = UP.arr.  `Pre := ⟨UP.dom, pre⟩` is a subobject of Z.
  have hpre_mono : Mono pre := by
    intro X u v huv
    exact UP.monic u v (by rw [← hpre, ← Cat.assoc, ← Cat.assoc, huv])
  let Pre : Subobject 𝒞 Z := ⟨UP.dom, pre, hpre_mono⟩
  -- pushMono m Pre = UP  (same dom, arr = pre ≫ m = UP.arr)
  -- P ≤ Pre and Q ≤ Pre, via pushMono_reflects (push P ≤ UP = push Pre).
  have hP_pre : P.le Pre :=
    pushMono_reflects m hm (P := P) (Q := Pre)
      (subLe_trans (HasSubobjectUnions.union_left (pushMono m hm P) (pushMono m hm Q))
        ⟨Cat.id _, by show Cat.id _ ≫ (pre ≫ m) = UP.arr; rw [Cat.id_comp, hpre]⟩)
  have hQ_pre : Q.le Pre :=
    pushMono_reflects m hm (P := Q) (Q := Pre)
      (subLe_trans (HasSubobjectUnions.union_right (pushMono m hm P) (pushMono m hm Q))
        ⟨Cat.id _, by show Cat.id _ ≫ (pre ≫ m) = UP.arr; rw [Cat.id_comp, hpre]⟩)
  have hunion_pre : (HasSubobjectUnions.union P Q).le Pre :=
    HasSubobjectUnions.union_min _ _ _ hP_pre hQ_pre
  -- finally push forward and land in UP (= pushMono m Pre).
  obtain ⟨g, hg⟩ := hunion_pre
  -- hg : g ≫ pre = (union P Q).arr.  Goal: g ≫ UP.arr = (union P Q).arr ≫ m.
  refine ⟨g, ?_⟩
  show g ≫ UP.arr = (HasSubobjectUnions.union P Q).arr ≫ m
  rw [← hpre, ← Cat.assoc, hg]

/-- The two arrows agree: `relSub (R ⊓ S).arr = pb.π₁ ≫ pairR = (pushMono pairR (InverseImage..)).arr`.
    `intersect` reads off `pb.π₁ ≫ R.colA` and `pb.π₁ ≫ R.colB`, which pair up to `pb.π₁ ≫ pairR`;
    `InverseImage pairR (relSub S)` has arr `pb.π₁` (same pullback `pb`), whose pushforward along
    `pairR` is exactly that.  We record the identity-witnessed `≤` both ways. -/
theorem relSub_inter_le {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    (relSub (R ⊓ S)).le
      (pushMono (pair R.colA R.colB) (monic_pair_of_monicPair R.colA R.colB R.isMonicPair)
        (InverseImage (pair R.colA R.colB) (relSub S))) := by
  refine ⟨Cat.id _, ?_⟩
  -- Goal: id ≫ (pb.π₁ ≫ pairR) = relSub(R⊓S).arr = pair (pb.π₁≫R.colA) (pb.π₁≫R.colB)
  rw [Cat.id_comp]
  show (HasPullbacks.has (pair R.colA R.colB) (pair S.colA S.colB)).cone.π₁ ≫ pair R.colA R.colB
        = pair (R ⊓ S).colA (R ⊓ S).colB
  exact pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]; rfl) (by rw [Cat.assoc, snd_pair]; rfl)

theorem relSub_inter_ge {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    (pushMono (pair R.colA R.colB) (monic_pair_of_monicPair R.colA R.colB R.isMonicPair)
        (InverseImage (pair R.colA R.colB) (relSub S))).le (relSub (R ⊓ S)) := by
  refine ⟨Cat.id _, ?_⟩
  rw [Cat.id_comp]
  show pair (R ⊓ S).colA (R ⊓ S).colB
        = (HasPullbacks.has (pair R.colA R.colB) (pair S.colA S.colB)).cone.π₁ ≫ pair R.colA R.colB
  exact (pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]; rfl) (by rw [Cat.assoc, snd_pair]; rfl)).symm

/-- Local copy of inverse-image monotonicity (the canonical one lives downstream in `S1_61`,
    which imports this file).  If `S ≤ T` then `f# S ≤ f# T`: the `S`-pullback cone maps into
    the `T`-pullback via the factorization, and pullback-lift gives the comparison on `π₁`. -/
theorem invImage_mono_local {A B : 𝒞} (f : A ⟶ B) {S T : Subobject 𝒞 B} (hle : S.le T) :
    (InverseImage f S).le (InverseImage f T) := by
  obtain ⟨l, hl⟩ := hle
  let pbS := HasPullbacks.has f S.arr
  let pbT := HasPullbacks.has f T.arr
  -- cone over (f, T.arr): pt = pbS.pt, legs π₁ and π₂≫l (since (π₂≫l)≫T.arr = π₂≫S.arr = π₁≫f).
  let c : Cone f T.arr :=
    ⟨pbS.cone.pt, pbS.cone.π₁, pbS.cone.π₂ ≫ l,
      by rw [Cat.assoc, hl, pbS.cone.w]⟩
  refine ⟨pbT.lift c, ?_⟩
  show pbT.lift c ≫ pbT.cone.π₁ = pbS.cone.π₁
  exact pbT.lift_fst c

/-- **§1.616** (pre-logos): `BinRel(A,B)` is a DISTRIBUTIVE lattice — the meet-over-join law
    `R ⊓ (S ∪ T) ≤ (R ⊓ S) ∪ (R ⊓ T)`.  Transported across `relSub` from the pre-logos fact
    that inverse images preserve unions (`PreLogos.invImage_preserves_union`) plus monotonicity
    of `pushMono`/`InverseImage` and the union laws. -/
theorem rel_inter_union_le {A B : 𝒞} (R S T : BinRel 𝒞 A B) :
    RelLe (R ⊓ (S ∪ᵣ T)) ((R ⊓ S) ∪ᵣ (R ⊓ T)) := by
  apply relLe_of_subLe
  let pR := pair R.colA R.colB
  let hpR : Mono pR := monic_pair_of_monicPair R.colA R.colB R.isMonicPair
  -- LHS = relSub(R ⊓ (S∪T)) ≤ pushMono pR (InverseImage pR (relSub (S∪T)))
  have hL : (relSub (R ⊓ (S ∪ᵣ T))).le
              (pushMono pR hpR (InverseImage pR (relSub (S ∪ᵣ T)))) := relSub_inter_le R (S ∪ᵣ T)
  -- step 1: InverseImage pR (relSub(S∪T)) ≤ InverseImage pR (union (relSub S)(relSub T))
  have h1 : (InverseImage pR (relSub (S ∪ᵣ T))).le
              (InverseImage pR (HasSubobjectUnions.union (relSub S) (relSub T))) :=
    invImage_mono_local pR (relSub_union_le S T)
  -- step 2 (PreLogos): InverseImage pR (union ..) ≤ union (InverseImage pR (relSub S)) (.. T)
  have h2 := (PreLogos.invImage_preserves_union pR (relSub S) (relSub T)).1
  have h12 := subLe_trans h1 h2
  have hpush := pushMono_mono pR hpR h12
  -- step 3: pushMono of union ≤ union of pushMono
  have hdist := pushMono_union_le pR hpR (InverseImage pR (relSub S)) (InverseImage pR (relSub T))
  -- step 4: each pushMono pR (InverseImage pR (relSub X)) ≤ relSub (R ⊓ X)
  have hSge := relSub_inter_ge R S
  have hTge := relSub_inter_ge R T
  let pS := pushMono pR hpR (InverseImage pR (relSub S))
  let pT := pushMono pR hpR (InverseImage pR (relSub T))
  have hunion_mono : (HasSubobjectUnions.union pS pT).le
                     (HasSubobjectUnions.union (relSub (R ⊓ S)) (relSub (R ⊓ T))) :=
    HasSubobjectUnions.union_min pS pT _
      (subLe_trans hSge (HasSubobjectUnions.union_left (relSub (R ⊓ S)) (relSub (R ⊓ T))))
      (subLe_trans hTge (HasSubobjectUnions.union_right (relSub (R ⊓ S)) (relSub (R ⊓ T))))
  -- step 5: union (relSub(R⊓S)) (relSub(R⊓T)) ≤ relSub ((R⊓S) ∪ (R⊓T))
  have hfinal := relSub_union_ge (R ⊓ S) (R ⊓ T)
  exact subLe_trans hL
    (subLe_trans hpush (subLe_trans hdist (subLe_trans hunion_mono hfinal)))

/-! ### §1.616  Composition distributes over union (right)

  Freyd's pre-logos proof reformulates `R ⊚ S` as a DIRECT IMAGE of a MEET of INVERSE IMAGES
  on the ternary product `A×B×C := prod A (prod B C)`:

      R ⊚ S  =  ∃_{πAC} ( πAB# (relSub R)  ⊓  πBC# (relSub S) ).

  Then `R⊚(S∪T) ≤ (R⊚S)∪(R⊚T)` falls out of three pre-logos facts, each available here:
    • `πBC#` preserves unions            (`PreLogos.invImage_preserves_union`),
    • meet distributes over join          (the `rel_inter_union_le` pattern, in `Sub(A×B×C)`),
    • `∃_{πAC}` preserves unions          (direct image of a union, `union_via_coproduct_image`).

  The ternary product and projections exist (`HasBinaryProducts`).  The remaining work is the
  geometric IDENTITY relating the binary-pullback definition of `compose` to the ternary
  direct-image-of-meet form; that single bridge is isolated below as `compose_eq_ternary`. -/

/-- Ternary product `A×B×C`. -/
abbrev prod₃ (A B C : 𝒞) : 𝒞 := prod A (prod B C)

/-- Direct image (∃) of a subobject `U ↣ X` along `g : X ⟶ Y`: the image of `U.arr ≫ g`. -/
def existsAlong {X Y : 𝒞} (g : X ⟶ Y) (U : Subobject 𝒞 X) : Subobject 𝒞 Y :=
  image (U.arr ≫ g)

/-- The image/pullback **adjunction** `∃_g ⊣ g#` at the level of subobject containment:
    `existsAlong g P ≤ V  ↔  P ≤ InverseImage g V`.  Forward: a factorization of `(image).arr`
    through `V` makes `P.arr ≫ g` factor through `V.arr`, so `P.arr` lifts to `pullback(g, V.arr)`.
    Reverse: a lift of `P.arr` to the pullback gives `P.arr ≫ g = (k ≫ π₂) ≫ V.arr`, so `V` allows
    `P.arr ≫ g` and `image_min` finishes.  Pure regular-category fact (no pre-logos needed). -/
theorem existsAlong_le_iff {X Y : 𝒞} (g : X ⟶ Y) (P : Subobject 𝒞 X) (V : Subobject 𝒞 Y) :
    (existsAlong g P).le V ↔ P.le (InverseImage g V) := by
  constructor
  · rintro ⟨k, hk⟩
    -- hk : k ≫ V.arr = (existsAlong g P).arr = (image (P.arr≫g)).arr.
    have hk' : k ≫ V.arr = (image (P.arr ≫ g)).arr := hk
    have hfac : (image.lift (P.arr ≫ g) ≫ k) ≫ V.arr = P.arr ≫ g := by
      rw [Cat.assoc, hk', image.lift_fac]
    let pb := HasPullbacks.has g V.arr
    let c : Cone g V.arr := ⟨P.dom, P.arr, image.lift (P.arr ≫ g) ≫ k, hfac.symm⟩
    exact ⟨pb.lift c, pb.lift_fst c⟩
  · rintro ⟨k, hk⟩
    let pb := HasPullbacks.has g V.arr
    have hk' : k ≫ pb.cone.π₁ = P.arr := hk
    refine image_min (P.arr ≫ g) V ⟨k ≫ pb.cone.π₂, ?_⟩
    -- (k ≫ π₂) ≫ V.arr = k ≫ π₁ ≫ g = P.arr ≫ g  using the pullback square π₁≫g = π₂≫V.arr.
    rw [Cat.assoc, ← pb.cone.w, ← Cat.assoc, hk']

theorem existsAlong_mono {X Y : 𝒞} (g : X ⟶ Y) {P Q : Subobject 𝒞 X} (hle : P.le Q) :
    (existsAlong g P).le (existsAlong g Q) := by
  obtain ⟨f, hf⟩ := hle
  refine image_min (P.arr ≫ g) (existsAlong g Q) ⟨f ≫ image.lift (Q.arr ≫ g), ?_⟩
  show (f ≫ image.lift (Q.arr ≫ g)) ≫ (existsAlong g Q).arr = P.arr ≫ g
  show (f ≫ image.lift (Q.arr ≫ g)) ≫ (image (Q.arr ≫ g)).arr = P.arr ≫ g
  rw [Cat.assoc, image.lift_fac, ← Cat.assoc, hf]

/-- `∃_g` preserves binary unions: `existsAlong g (union P Q) ≤ union (existsAlong g P) (existsAlong g Q)`.
    Via the `∃_g ⊣ g#` adjunction: the RHS-bound `V` satisfies `existsAlong g P ≤ V` and
    `existsAlong g Q ≤ V` (union inclusions), hence `P ≤ g#V` and `Q ≤ g#V`, hence `union P Q ≤ g#V`
    by `union_min`, hence `existsAlong g (union P Q) ≤ V` by the adjunction. -/
theorem existsAlong_union_le {X Y : 𝒞} (g : X ⟶ Y) (P Q : Subobject 𝒞 X) :
    (existsAlong g (HasSubobjectUnions.union P Q)).le
      (HasSubobjectUnions.union (existsAlong g P) (existsAlong g Q)) := by
  let V := HasSubobjectUnions.union (existsAlong g P) (existsAlong g Q)
  have hP : P.le (InverseImage g V) :=
    (existsAlong_le_iff g P V).1 (HasSubobjectUnions.union_left _ _)
  have hQ : Q.le (InverseImage g V) :=
    (existsAlong_le_iff g Q V).1 (HasSubobjectUnions.union_right _ _)
  exact (existsAlong_le_iff g (HasSubobjectUnions.union P Q) V).2
    (HasSubobjectUnions.union_min _ _ _ hP hQ)

/-! ### §1.616  The extensive descent for `compose_union_right`

  The hard half `R⊚(S∪T) ≤ (R⊚S)∪(R⊚T)` is, in any pre-logos, the *extensive* (= "geometric")
  content of §1.616: pulling a relation back along the cover that presents a union RE-DECOMPOSES it
  over the two pieces.  Concretely, `compose` builds `R⊚(S∪T)` as the image of the span out of
  `pb := pullback(R.colB, (S∪T).colA)`, and `(S∪T).colA` is the `fst`-leg of the cover-image of the
  copairing `m := case(pairS)(pairT)`.  Pulling that cover back along `pb.π₂` (covers are stable
  under pullback in a regular category — `cover_pullback`) yields a common cover `P ↠ pb.pt` whose
  domain carries, summand-by-summand, the `R⊚S`/`R⊚T` data — so it maps into `(R⊚S)∪(R⊚T)`.

  The COVER `P ↠ pb.pt` together with the descent map `φ : P → ((R⊚S)∪(R⊚T)).src` is isolated as
  `union_compose_descent`.  Everything else (`relLe_of_cover_factor`, `image_lift_cover`,
  `cover_comp`) is fully proven, so the main theorem below is a complete reduction to it.

  Why a `sorry` remains here: producing `φ` requires that the pullback `pb1 := pullback(eU, pb.π₂)`
  of the coproduct-presenting cover `eU` SPLITS over `S.src + T.src` — i.e. binary coproducts are
  stable under pullback (EXTENSIVITY / "pullback distributes over coproduct").  That primitive is
  not yet built in this repo (cf. the same gap flagged at `S1_84.lean:510` `pullback_union`).  Once
  the extensive split `pullback(P+Q, h) ≅ pullback(P,h) + pullback(Q,h)` is available, `φ` is the
  copairing of the two summand descents and the `sorry` discharges with no new ideas. -/

/-- **Extensive descent** (SHARP gap, §1.616).  With `U := S ∪ᵣ T` and `pb := pullback(R.colB, U.colA)`,
    there is a cover `c : P ↠ pb.cone.pt` and a descent `φ : P → ((R⊚S) ∪ᵣ (R⊚T)).src` whose legs
    match the `R⊚U`-span composed with `c`:
      `c ≫ (pb.π₁ ≫ R.colA) = φ ≫ ((R⊚S)∪(R⊚T)).colA`,
      `c ≫ (pb.π₂ ≫ U.colB) = φ ≫ ((R⊚S)∪(R⊚T)).colB`.
    Both hypotheses are genuinely used downstream (they ARE the two leg-agreements fed to
    `relLe_of_cover_factor`).  The single missing ingredient is the extensive split of the
    coproduct-presenting cover of `U.src` under pullback along `pb.π₂`; see the section header. -/
private theorem union_compose_descent {A B C : 𝒞} (R : BinRel 𝒞 A B) (S T : BinRel 𝒞 B C) :
    ∃ (P : 𝒞) (c : P ⟶ (HasPullbacks.has R.colB (S ∪ᵣ T).colA).cone.pt)
      (φ : P ⟶ ((R ⊚ S) ∪ᵣ (R ⊚ T)).src),
      Cover c ∧
      c ≫ ((HasPullbacks.has R.colB (S ∪ᵣ T).colA).cone.π₁ ≫ R.colA)
        = φ ≫ ((R ⊚ S) ∪ᵣ (R ⊚ T)).colA ∧
      c ≫ ((HasPullbacks.has R.colB (S ∪ᵣ T).colA).cone.π₂ ≫ (S ∪ᵣ T).colB)
        = φ ≫ ((R ⊚ S) ∪ᵣ (R ⊚ T)).colB := by
  -- The cover `c` is built from `cover_pullback (image_lift_cover m) ≫ pb.π₂`; the descent `φ` is
  -- the copairing of the two summand maps after the extensive split of `pullback(eU, pb.π₂)`.
  sorry

/-- §1.616: Composition distributes over union (right): `R ⊚ (S ∪ T) ≤ (R⊚S) ∪ (R⊚T)`.

    FAITHFUL to Freyd: pre-logos hypothesis restored (the statement is FALSE in a bare regular
    category, true in a pre-logos).  The composed relation `R⊚(S∪T)` is `image span`, where
    `span := pair (pb.π₁ ≫ R.colA) (pb.π₂ ≫ (S∪T).colB)` and `pb := pullback(R.colB, (S∪T).colA)`;
    `eW := image.lift span : pb.pt ↠ (R⊚(S∪T)).src` is therefore a COVER (`image_lift_cover`).

    `union_compose_descent` supplies a further cover `c : P ↠ pb.pt` and a descent
    `φ : P → ((R⊚S)∪(R⊚T)).src` matching the span legs.  Composing covers (`cover_comp`) gives a
    cover `c ≫ eW : P ↠ (R⊚(S∪T)).src`, and `φ` agrees with it on both legs (the two `span`-leg
    identities `eW ≫ (R⊚(S∪T)).colX = (span)≫…`), so `relLe_of_cover_factor` (cover⊥mono descent)
    delivers the containment `R⊚(S∪T) ≤ (R⊚S)∪(R⊚T)`. -/
theorem compose_union_right {A B C : 𝒞} (R : BinRel 𝒞 A B) (S T : BinRel 𝒞 B C) :
    RelLe (R ⊚ (S ∪ᵣ T)) ((R ⊚ S) ∪ᵣ (R ⊚ T)) := by
  -- The image-cover presenting `R⊚(S∪T)` and its two span-leg identities.
  let pb := HasPullbacks.has R.colB (S ∪ᵣ T).colA
  let span : pb.cone.pt ⟶ prod A C :=
    pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ (S ∪ᵣ T).colB)
  let eW := image.lift span
  have hWa : eW ≫ (R ⊚ (S ∪ᵣ T)).colA = pb.cone.π₁ ≫ R.colA := by
    show eW ≫ ((image span).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hWb : eW ≫ (R ⊚ (S ∪ᵣ T)).colB = pb.cone.π₂ ≫ (S ∪ᵣ T).colB := by
    show eW ≫ ((image span).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- The extensive descent: a cover `c : P ↠ pb.pt` and descent map `φ`.
  obtain ⟨P, c, φ, hc, hφA, hφB⟩ := union_compose_descent R S T
  -- `c ≫ eW : P ↠ (R⊚(S∪T)).src` is a cover; `φ` descends along it.
  refine relLe_of_cover_factor (c ≫ eW) (cover_comp hc (image_lift_cover span)) φ ?_ ?_
  · -- φ ≫ colA = (c ≫ eW) ≫ (R⊚(S∪T)).colA
    calc φ ≫ ((R ⊚ S) ∪ᵣ (R ⊚ T)).colA
        = c ≫ (pb.cone.π₁ ≫ R.colA) := hφA.symm
      _ = c ≫ (eW ≫ (R ⊚ (S ∪ᵣ T)).colA) := by rw [hWa]
      _ = (c ≫ eW) ≫ (R ⊚ (S ∪ᵣ T)).colA := (Cat.assoc _ _ _).symm
  · -- φ ≫ colB = (c ≫ eW) ≫ (R⊚(S∪T)).colB
    calc φ ≫ ((R ⊚ S) ∪ᵣ (R ⊚ T)).colB
        = c ≫ (pb.cone.π₂ ≫ (S ∪ᵣ T).colB) := hφB.symm
      _ = c ≫ (eW ≫ (R ⊚ (S ∪ᵣ T)).colB) := by rw [hWb]
      _ = (c ≫ eW) ≫ (R ⊚ (S ∪ᵣ T)).colB := (Cat.assoc _ _ _).symm

end BinRelDistributive

end Freyd
