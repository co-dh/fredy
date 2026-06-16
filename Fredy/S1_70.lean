/-
  Freyd & Scedrov, *Categories and Allegories* §1.7  Logoi.

  §1.7  LOGOS: regular + subobject lattices + f# has right adjoint f##.
  §1.71 In boolean pre-logos, f##(A') = ¬f(¬A') (complement of direct image).
  §1.711 Logos ⇒ pre-logos (f# preserves all unions).
  §1.712 Locally complete: subobject lattices are complete.
  §1.72  Heyting algebra: lattice with implication →.
  §1.721 Sub-object lattice of any object in a logos is a Heyting algebra.
  §1.722 Poset is logos iff Heyting algebra.
  §1.723 Locale: complete lattice with distributivity.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_60


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## Subobject order helpers -/

/-- Mutual ≤ between subobjects gives isomorphic domains. -/
theorem subobject_le_antisymm_iso {B : 𝒞} {S T : Subobject 𝒞 B}
    (hST : S.le T) (hTS : T.le S) : Isomorphic S.dom T.dom := by
  obtain ⟨h₁, h₁fac⟩ := hST
  obtain ⟨h₂, h₂fac⟩ := hTS
  refine ⟨h₁, h₂, ?_, ?_⟩
  · exact S.monic (h₁ ≫ h₂) (Cat.id S.dom) (by rw [Cat.assoc, h₂fac, h₁fac, Cat.id_comp])
  · exact T.monic (h₂ ≫ h₁) (Cat.id T.dom) (by rw [Cat.assoc, h₁fac, h₂fac, Cat.id_comp])

/-- Transitivity of Subobject.le. -/
theorem subobject_le_trans {B : 𝒞} {X Y Z : Subobject 𝒞 B}
    (hXY : X.le Y) (hYZ : Y.le Z) : X.le Z :=
  let ⟨h₁, e₁⟩ := hXY; let ⟨h₂, e₂⟩ := hYZ
  ⟨h₁ ≫ h₂, by rw [Cat.assoc, e₂, e₁]⟩

/-- Reflexivity of Subobject.le. -/
theorem subobject_le_refl {B : 𝒞} (S : Subobject 𝒞 B) : S.le S :=
  ⟨Cat.id S.dom, Cat.id_comp S.arr⟩

/-! ## §1.71 Boolean pre-logos: f## = complement of direct image

  In a BOOLEAN PRE-LOGOS, every subobject lattice has a complement operation
  (Boolean algebra). The right adjoint f## can then be built without a general
  adjoint: f##(A') = ¬f(¬A'), i.e. the complement of the direct image of the
  complement.  (Freyd §1.71.) -/

/-- A pre-logos with subobject complements (boolean pre-logos). -/
class HasSubobjectComplements (𝒞 : Type u) [Cat.{v} 𝒞] [HasImages 𝒞] where
  compl : ∀ {A : 𝒞}, Subobject 𝒞 A → Subobject 𝒞 A
  compl_join  : ∀ {A : 𝒞} (S : Subobject 𝒞 A) [HasSubobjectUnions 𝒞],
    (HasSubobjectUnions.union S (compl S)) = HasSubobjectUnions.union (compl S) S
  compl_inv   : ∀ {A : 𝒞} (S : Subobject 𝒞 A), compl (compl S) = S

/-- Direct image f_! : Sub(A) → Sub(B) via the image of the composite. -/
noncomputable def DirectImage [HasImages 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (S : Subobject 𝒞 A) : Subobject 𝒞 B :=
  HasImages.image (S.arr ≫ f)

-- (§1.71 boolean logos theorem follows after class definitions below)

/-! ## §1.7 Logos

  A LOGOS is a regular category where subobject lattices have a right
  adjoint f## to the inverse image f# for every f: A → B (§1.7). -/

-- Class definitions need HasPullbacks etc. in scope.
section LogosClasses

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-- f##(A') is the right adjoint of f#: the maximal B' ⊆ B such that
    f#(B') ⊆ A'.  Satisfies: f#(B') ⊆ A' ⇔ B' ⊆ f##(A'). -/
class HasRightAdjointImage (𝒞 : Type u) [Cat.{v} 𝒞] extends HasImages 𝒞, HasPullbacks 𝒞 where
  rightAdj : ∀ {A B : 𝒞} (f : A ⟶ B), Subobject 𝒞 A → Subobject 𝒞 B
  adjunction : ∀ {A B : 𝒞} (f : A ⟶ B) (B' : Subobject 𝒞 B) (A' : Subobject 𝒞 A),
    Subobject.le (InverseImage f B') A' ↔ Subobject.le B' (rightAdj f A')

/-- A LOGOS (§1.7): regular + subobject lattices + right adjoint to f#.

    The book says "Sub(A) is a *lattice* (not just a semi-lattice)" (§1.6, §1.7),
    so a logos carries the *bottom* (empty join, minimal subobject 0) of each
    Sub(A) in addition to the binary joins of `HasSubobjectUnions`.  These bottom
    fields mirror the pre-logos lattice bottom; §1.711 (`logos_implies_preLogos`)
    *derives* that f# preserves it, because f# is a left adjoint. -/
class Logos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    RegularCategory 𝒞, HasSubobjectUnions 𝒞, HasRightAdjointImage 𝒞 where
  bottom : ∀ (A : 𝒞), Subobject 𝒞 A
  bottom_min : ∀ {A : 𝒞} (S : Subobject 𝒞 A), (bottom A).le S
  bottom_dom_iso : ∀ (A B : 𝒞), Isomorphic (bottom A).dom (bottom B).dom

end LogosClasses

/-! ## §1.71 Boolean pre-logos: f## = ¬f(¬(−))

  In a boolean pre-logos (where each Sub(A) is a Boolean algebra), the right
  adjoint f## can be constructed without local completeness: given A' ⊆ A, let
  f##(A') = ¬ f(¬A'), the complement of the direct image of the complement. -/

section BooleanLogos

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
variable [HasSubobjectUnions 𝒞] [HasSubobjectComplements 𝒞] [HasRightAdjointImage 𝒞]

/-- §1.71: In a boolean logos, f##(A') ≅ ¬f(¬A') (complement of direct image of complement).
    The proof uses: f#(B') ≤ A' ↔ f#(B') ∧ ¬A' = 0 ↔ f(B' ∧ f#(¬A')) = 0
    ↔ B' ∧ f#(¬A') = 0 ↔ B' ≤ ¬f#(¬A') = f##(A').  We state this faithfully;
    the full argument needs boolean identities connecting f# and direct images. -/
theorem boolean_logos_rightAdj_eq_compl_direct_compl
    {A B : 𝒞} (f : A ⟶ B) (A' : Subobject 𝒞 A) :
    Subobject.le (HasRightAdjointImage.rightAdj f A')
                 (HasSubobjectComplements.compl (DirectImage f (HasSubobjectComplements.compl A'))) ∧
    Subobject.le (HasSubobjectComplements.compl (DirectImage f (HasSubobjectComplements.compl A')))
                 (HasRightAdjointImage.rightAdj f A') := by
  sorry

end BooleanLogos

/-! ## §1.711 Logos ⇒ pre-logos

  In a logos, f# preserves all unions that exist.  Hence a logos is a
  pre-logos. -/

-- §1.711 helper: proved in its own section so the outer variable block
-- [HasPullbacks] / [HasImages] is NOT in scope and the Logos instances win.
section LogosPreLogosHelper

variable [L : Logos 𝒞]

-- InverseImage and HasSubobjectUnions now use L's internal instances.

private theorem logos_invImage_pres_union {A B : 𝒞} (f : A ⟶ B)
    (S T : Subobject 𝒞 B) :
    (InverseImage f (HasSubobjectUnions.union S T)).le
        (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T))
    ∧ (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)).le
        (InverseImage f (HasSubobjectUnions.union S T)) := by
  -- §1.711: via the adjunction f# ⊣ f##.
  -- adj: (InverseImage f B').le A' ↔ B'.le (f## A')
  have adj : ∀ (B' : Subobject 𝒞 B) (A' : Subobject 𝒞 A),
      (InverseImage f B').le A' ↔ B'.le (HasRightAdjointImage.rightAdj f A') :=
    fun B' A' => L.adjunction f B' A'
  let ST   := HasSubobjectUnions.union S T
  let fST  := InverseImage f ST
  let fS   := InverseImage f S
  let fT   := InverseImage f T
  let join := HasSubobjectUnions.union fS fT
  -- Step 1: join ≤ fST  (f#S ∪ f#T ≤ f#(S∪T))
  -- S∪T ≤ f##(fST) from f#(S∪T) ≤ f#(S∪T) [refl] and adj.
  have h_ST_le_ra : ST.le (HasRightAdjointImage.rightAdj f fST) :=
    (adj ST fST).mp (subobject_le_refl fST)
  have hS_le : fS.le fST := (adj S fST).mpr
    (subobject_le_trans (HasSubobjectUnions.union_left S T) h_ST_le_ra)
  have hT_le : fT.le fST := (adj T fST).mpr
    (subobject_le_trans (HasSubobjectUnions.union_right S T) h_ST_le_ra)
  have hle : join.le fST := HasSubobjectUnions.union_min _ _ _ hS_le hT_le
  -- Step 2: fST ≤ join  (f#(S∪T) ≤ f#S ∪ f#T)
  -- S ≤ f##(join) from f#S ≤ join [union_left] and adj; idem T.
  have hS_le_ra : S.le (HasRightAdjointImage.rightAdj f join) :=
    (adj S join).mp (HasSubobjectUnions.union_left fS fT)
  have hT_le_ra : T.le (HasRightAdjointImage.rightAdj f join) :=
    (adj T join).mp (HasSubobjectUnions.union_right fS fT)
  have hle2 : fST.le join := (adj ST join).mpr
    (HasSubobjectUnions.union_min S T _ hS_le_ra hT_le_ra)
  -- fST = InverseImage f (S∪T), join = f#S ∪ f#T; expose both le-directions
  -- (the mediating maps commute with the monics into A).
  exact ⟨hle2, hle⟩

/-- §1.711: f# preserves the bottom (empty join).  Since f# is a *left* adjoint
    (f# ⊣ f##), it preserves the bottom: for every A', `f#(⊥_B) ≤ A'` because
    `⊥_B ≤ rightAdj f A'` always (bottom_min), so via the adjunction
    `f#(⊥_B) ≤ A'`.  Taking A' = ⊥_A gives `f#(⊥_B) ≤ ⊥_A`; the reverse is
    `bottom_min` again, and antisymmetry yields the domain iso. -/
private theorem logos_invImage_pres_bottom {A B : 𝒞} (f : A ⟶ B) :
    Isomorphic (InverseImage f (Logos.bottom B)).dom (Logos.bottom A).dom := by
  have adj : ∀ (B' : Subobject 𝒞 B) (A' : Subobject 𝒞 A),
      (InverseImage f B').le A' ↔ B'.le (HasRightAdjointImage.rightAdj f A') :=
    fun B' A' => L.adjunction f B' A'
  -- f#(⊥_B) ≤ ⊥_A : adjunction turns the goal into ⊥_B ≤ rightAdj f ⊥_A, true by bottom_min.
  have hle : (InverseImage f (Logos.bottom B)).le (Logos.bottom A) :=
    (adj (Logos.bottom B) (Logos.bottom A)).mpr (Logos.bottom_min _)
  -- ⊥_A ≤ f#(⊥_B) : bottom is minimal in Sub(A).
  have hge : (Logos.bottom A).le (InverseImage f (Logos.bottom B)) := Logos.bottom_min _
  exact subobject_le_antisymm_iso hle hge

end LogosPreLogosHelper

section LogosFacts

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

def logos_implies_preLogos [L : Logos 𝒞] : PreLogos 𝒞 where
  toRegularCategory    := L.toRegularCategory
  toHasSubobjectUnions := L.toHasSubobjectUnions
  invImage_preserves_union {A B} f S T := logos_invImage_pres_union f S T
  -- §1.61/§1.711: the logos's lattice supplies the bottom (empty join); f# being a
  -- left adjoint preserves it (logos_invImage_pres_bottom).
  bottom                       := L.bottom
  bottom_min                   := L.bottom_min
  bottom_dom_iso               := L.bottom_dom_iso
  invImage_preserves_bottom f  := logos_invImage_pres_bottom f

/-! ## §1.712 Locally complete categories

  A category is LOCALLY COMPLETE if each subobject lattice is
  a complete lattice (all meets/joins exist). -/

/-- Subobjects of A form a complete lattice (all meets and joins exist). -/
class LocallyComplete (𝒞 : Type u) [Cat.{v} 𝒞] extends HasImages 𝒞 where
  sup : ∀ {A : 𝒞}, ((Subobject 𝒞 A) → Prop) → Subobject 𝒞 A
  sup_upper : ∀ {A} (S : (Subobject 𝒞 A) → Prop) (s : Subobject 𝒞 A), S s → Subobject.le s (sup S)
  sup_least : ∀ {A} (S : (Subobject 𝒞 A) → Prop) (U : Subobject 𝒞 A),
    (∀ (s : Subobject 𝒞 A), S s → Subobject.le s U) → Subobject.le (sup S) U

/-- §1.712: InverseImage f is monotone: B₁ ≤ B₂ ⟹ f#(B₁) ≤ f#(B₂).
    Proof: use the pullback mediating map into the cone (π₁, π₂ ≫ k). -/
theorem invImage_mono {A B : 𝒞} (f : A ⟶ B) {B₁ B₂ : Subobject 𝒞 B}
    (hle : B₁.le B₂) : (InverseImage f B₁).le (InverseImage f B₂) := by
  obtain ⟨k, hk⟩ := hle
  let pb₁ := HasPullbacks.has f B₁.arr
  let pb₂ := HasPullbacks.has f B₂.arr
  have hw : pb₁.cone.π₁ ≫ f = (pb₁.cone.π₂ ≫ k) ≫ B₂.arr := by
    rw [Cat.assoc, hk, ← pb₁.cone.w]
  exact ⟨pb₂.lift ⟨pb₁.cone.pt, pb₁.cone.π₁, pb₁.cone.π₂ ≫ k, hw⟩, pb₂.lift_fst _⟩

end LogosFacts

/-! ## §1.712 Locally complete + union-preserving ⟹ logos (main theorem) -/

section LogosFromLC

/-- In a locally complete regular category with f# preserving all unions,
    the right adjoint f## exists (constructible as sup of all B' with f#(B')⊆A').
    §1.712: the adjunction f# ⊣ f## is fully proven. -/
def locallyComplete_with_union_preserving_is_logos
    {𝒞 : Type u} [Cat.{v} 𝒞]
    [LC : LocallyComplete 𝒞] [PL : PreLogos 𝒞]
    (h_preserves : ∀ {A B : 𝒞} (f : A ⟶ B) (S : (Subobject 𝒞 B) → Prop),
      Subobject.le (InverseImage f (LC.sup S))
                   (LC.sup (λ A' => ∃ B', S B' ∧ A' = InverseImage f B'))) : Logos 𝒞 where
  toRegularCategory    := PL.toRegularCategory
  toHasSubobjectUnions := PL.toHasSubobjectUnions
  -- the lattice bottom is inherited from the underlying pre-logos.
  bottom         := PL.bottom
  bottom_min     := PL.bottom_min
  bottom_dom_iso := PL.bottom_dom_iso
  -- f##(A') := sup { B' : Sub(B) | f#(B') ≤ A' }
  rightAdj f A' := LC.sup (fun B' => (InverseImage f B').le A')
  adjunction f B' A' := by
    constructor
    · -- forward: f#(B') ≤ A' → B' ≤ sup { C | f#(C) ≤ A' }
      exact fun h => LC.sup_upper (fun C => (InverseImage f C).le A') B' h
    · -- backward: B' ≤ sup S → f#(B') ≤ A'
      -- mono: f#(B') ≤ f#(sup S); h_preserves: f#(sup S) ≤ sup { f#(C) | C ∈ S };
      -- sup_least: every f#(C) in that image satisfies f#(C) ≤ A'.
      intro hB'
      have hmono := @invImage_mono 𝒞 _
                     PL.toRegularCategory.toHasTerminal
                     PL.toRegularCategory.toHasBinaryProducts
                     PL.toRegularCategory.toHasPullbacks
                     PL.toRegularCategory.toHasImages
                     _ _ f _ _ hB'
      have hpres := h_preserves f (fun C => (InverseImage f C).le A')
      have himg_le : (LC.sup (fun A'' => ∃ C, (InverseImage f C).le A' ∧ A'' = InverseImage f C)).le A' :=
        LC.sup_least _ A' (fun A'' ⟨_, hC, heq⟩ => heq ▸ hC)
      exact subobject_le_trans (subobject_le_trans hmono hpres) himg_le

end LogosFromLC

/-! ## §1.713 Presheaves and sheaves are locally complete

  The presheaf category Set^(𝒞ᵒᵖ) (written -Y^A in the book) and the
  sheaf category Sh(Y,f) are locally complete.  The evaluation functors
  preserve inverse images and arbitrary unions; because they are collectively
  faithful, these categories satisfy the condition of §1.712 and hence are
  logoi.  (Freyd §1.713; the argument is abstract and relies on §1.712.) -/

-- §1.713: Both the presheaf category Set^(𝒞ᵒᵖ) (-Y^A) and the sheaf category
-- Sh(Y,f) are locally complete, and the evaluation / stalk functors preserve
-- inverse images and arbitrary unions. By collective faithfulness, §1.712 applies
-- and these categories are logoi. The formal Lean construction would require a
-- concrete model of the presheaf/sheaf category (ambient set theory); we record
-- this as a design note rather than a sorry-bearing stub.

/-! ## §1.714 Alternate axiom for logos

  A logos may equivalently be defined as a pre-logos in which (some condition
  on f# that the OCR scan truncated — page break after "A logos may be defined
  as a pre-logos in which").  The most natural reconstruction is the locally-
  complete characterisation of §1.712: a pre-logos is a logos iff it is locally
  complete (each Sub(A) is a complete lattice), since §1.712 shows that local
  completeness + union preservation is exactly what gives f##.

  We state the alternate axiom as: logos = pre-logos + locally complete.
  This is proven via `locallyComplete_with_union_preserving_is_logos`. -/

/-- §1.714: A pre-logos that is locally complete is a logos.
    This is the assembled form of §1.712, capturing the alternate logos axiom. -/
def preLogos_locallyComplete_is_logos
    {𝒞 : Type u} [Cat.{v} 𝒞]
    [LC : LocallyComplete 𝒞] [PL : PreLogos 𝒞]
    (h_preserves : ∀ {A B : 𝒞} (f : A ⟶ B) (S : (Subobject 𝒞 B) → Prop),
      Subobject.le (InverseImage f (LC.sup S))
                   (LC.sup (λ A' => ∃ B', S B' ∧ A' = InverseImage f B'))) :
    Logos 𝒞 :=
  locallyComplete_with_union_preserving_is_logos h_preserves

section LogosFacts2

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-! ## §1.721 Subobject lattice of any object in a logos is a Heyting algebra.

  Given A₁, A₂ ⊆ A in a logos, let i : A₁ ↪ A be the inclusion map.
  Then (A₁ → A₂) := i##(A₁ ∩ A₂) = rightAdj i (intersection A₁ A₂).
  The adjunction gives: A₃ ∧ A₁ ≤ A₂ ↔ A₃ ≤ (A₁ → A₂). -/

-- §1.721 (subobject lattice of a logos object is a Heyting algebra) is stated
-- and developed in S1_72 alongside the `HeytingAlgebra` class; not restated here
-- as a vacuous stub.

/-! ## §1.722 A poset viewed as a category is a logos iff it is a Heyting algebra.

  Proof sketch: In a poset, InverseImage f B' = x∧y (meet), and f## gives
  implication.  §1.722 combines §1.721 and §1.613. -/

-- §1.722 (a poset is a logos iff it is a Heyting algebra) belongs with the
-- `HeytingAlgebra` development in S1_72 (which imports this file); not restated
-- here as a vacuous stub.

-- §1.723 LOCALE is defined canonically in S1_72 (with the meet/Heyting structure);
-- not duplicated here.

end LogosFacts2

end Freyd
