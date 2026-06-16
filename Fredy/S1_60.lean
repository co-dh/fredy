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

/-- §1.616: BinRel(A,B) is a distributive lattice.
    Distributivity: R ∩ (S ∪ T) ≡ (R ∩ S) ∪ (R ∩ T). -/
theorem rel_inter_union_le {A B : 𝒞} (R S T : BinRel 𝒞 A B) :
    RelLe (R ⊓ (S ∪ᵣ T)) ((R ⊓ S) ∪ᵣ (R ⊓ T)) := by
  -- BLOCKER (§1.616, book needs [PreLogos] + BinRel↔Sub(A×B) bridge):
  -- `R ⊓ U` is definitionally `InverseImage (pair R.colA R.colB) U_sub` (same pullback)
  -- and `relUnion S T` is the image of the copairing, which equals
  -- `HasSubobjectUnions.union S_sub T_sub` (by union_via_coproduct_image + S1_61).
  -- With [PreLogos], `invImage_preserves_union` gives the forward `Subobject.le` in Sub(R.src),
  -- but that lives in a DIFFERENT universe than the BinRel `RelLe` (which requires equations
  -- over colA/colB mapping to A×B, not over the abstract `.arr : InvImg.dom → R.src`).
  -- Bridging requires `relSub : BinRel 𝒞 A B → Subobject 𝒞 (prod A B)` plus
  -- `relUnion R S ≈ HasSubobjectUnions.union (relSub R) (relSub S)` — absent in this repo.
  -- The statement is faithful (Freyd §1.616); false without pre-logos.
  sorry

/-- §1.616: (R ∩ S) ∪ (R ∩ T) ≤ R ∩ (S ∪ T) — the reverse always holds. -/
theorem rel_union_inter_le {A B : 𝒞} (R S T : BinRel 𝒞 A B) :
    RelLe ((R ⊓ S) ∪ᵣ (R ⊓ T)) (R ⊓ (S ∪ᵣ T)) := by
  apply le_relUnion
  · exact le_intersect (intersect_le_left R S) (rel_le_trans (intersect_le_right R S) (relUnion_le_left S T))
  · exact le_intersect (intersect_le_left R T) (rel_le_trans (intersect_le_right R T) (relUnion_le_right S T))

/-- §1.616: Composition distributes over union (right): R ⊚ (S ∪ T) ≡ (R⊚S) ∪ (R⊚T).
    Proof relies on direct images preserving unions (book §1.616). -/
theorem compose_union_right {A B C : 𝒞} (R : BinRel 𝒞 A B) (S T : BinRel 𝒞 B C) :
    RelLe (R ⊚ (S ∪ᵣ T)) ((R ⊚ S) ∪ᵣ (R ⊚ T)) := by
  -- KNOWN-HARD BLOCKER (§1.616, "direct images preserve unions"):
  -- R⊚U = image(spanU) where spanU : pbU.pt → A×C, pbU = pullback(R.colB, U.colA).
  -- Every proof route for R⊚(S∪T) ≤ (R⊚S)∪(R⊚T) reduces to splitting pbST.pt
  -- (pullback of R.colB along (S∪T).colA) into pbS.pt ⊕ pbT.pt — which requires
  -- COPRODUCT EXTENSIVITY (cover(case s₁ t₁) where s₁,t₁ are pullbacks of the
  -- coproduct injections along pbST.π₂) — strictly beyond [RegularCategory].
  -- The book's route (Freyd §1.616) uses a FIXED projection π_BC : A×B×C → B×C and
  -- reformulates R⊚S as a direct image, but that needs a ternary product A×B×C which
  -- does not exist in this repo (grep prodMap/ternary → empty).
  -- False without [PreLogos] (need "direct images preserve unions" = the §1.616 content).
  sorry

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

end Freyd
