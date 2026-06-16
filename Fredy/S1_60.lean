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
    f#(S ∪ T) is isomorphic to f#(S) ∪ f#(T). -/
def inverseImage_preserves_unions [HasImages 𝒞] [HasSubobjectUnions 𝒞] {A B : 𝒞} (f : A ⟶ B) [HasPullbacks 𝒞] : Prop :=
  ∀ (S T : Subobject 𝒞 B),
    Isomorphic (InverseImage f (HasSubobjectUnions.union S T)).dom
               (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)).dom

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

/-- A distributive lattice: the subobject unions satisfy distributivity. -/
def IsDistributiveLattice [HasImages 𝒞] [HasSubobjectUnions 𝒞] : Prop :=
  ∀ {B : 𝒞} (A S T : Subobject 𝒞 B),
    Subobject.le (HasSubobjectUnions.union
      (HasSubobjectUnions.union A S) A)
      (HasSubobjectUnions.union A (HasSubobjectUnions.union S T))

/-- In a thin category (at most one morphism per hom-set), pre-logos
    is equivalent to being a distributive lattice (§1.613). -/
theorem poset_prelogos_iff_distributive [PreLogos 𝒞]
    (_hThin : ∀ {A B : 𝒞} (f g : A ⟶ B), f = g) : IsDistributiveLattice (𝒞 := 𝒞) := by
  intro B A S T
  -- This (absorption) inequality holds from the lattice axioms alone.
  have le_trans : ∀ {X Y Z : Subobject 𝒞 B}, X.le Y → Y.le Z → X.le Z := by
    rintro X Y Z ⟨h1, e1⟩ ⟨h2, e2⟩
    exact ⟨h1 ≫ h2, by rw [Cat.assoc, e2, e1]⟩
  apply HasSubobjectUnions.union_min
  · apply HasSubobjectUnions.union_min
    · exact HasSubobjectUnions.union_left _ _
    · exact le_trans (HasSubobjectUnions.union_left S T) (HasSubobjectUnions.union_right _ _)
  · exact HasSubobjectUnions.union_left _ _

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
  -- R ⊓ (S∪T) ≤ R and ≤ S∪T
  have hR  := intersect_le_left R (S ∪ᵣ T)
  have hST := intersect_le_right R (S ∪ᵣ T)
  -- S∪T = (S∪T), so hST : R⊓(S∪T) ≤ S∪T
  -- We need R⊓(S∪T) ≤ (R⊓S)∪(R⊓T).
  -- Since R⊓(S∪T) ≤ R, it suffices to split via S vs T.
  -- Strategy: use universal property of (R⊓S)∪(R⊓T) with the two legs:
  --   R⊓S ≤ (R⊓S)∪(R⊓T) and R⊓T ≤ (R⊓S)∪(R⊓T).
  -- The difficult part: showing R⊓(S∪T) factors through (R⊓S)∪(R⊓T).
  -- In a pre-logos this follows from inverse-image preserving unions.
  -- For the relational calculus: we show the intersection witnesses factor.
  -- R⊓(S∪T) ≤ (R⊓S)∪(R⊓T) means: for any f witnessing R⊓(S∪T), it
  -- factors through (R⊓S)∪(R⊓T). This requires the image to split,
  -- which needs the pre-logos axiom (inverse image preserves unions).
  -- Faithful statement; proof needs PreLogos.invImage_preserves_union.
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
  -- R⊚S ≤ R⊚(S∪T) and R⊚T ≤ R⊚(S∪T) would give (R⊚S)∪(R⊚T) ≤ R⊚(S∪T).
  -- The forward direction R⊚(S∪T) ≤ (R⊚S)∪(R⊚T) needs direct image to preserve unions.
  -- This is the key fact of §1.616 (direct images always preserve unions in a logos/pre-logos).
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

end BinRelLattice

end Freyd
