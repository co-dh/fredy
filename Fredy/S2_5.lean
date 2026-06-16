/-
  Freyd & Scedrov, *Categories and Allegories* §2.5  Quotient allegories.

  §2.5  CONGRUENCE on an allegory, QUOTIENT ALLEGORY
  §2.521 BOOLEAN QUOTIENT
  §2.522 CLOSED QUOTIENT
  §2.53 AMENABLE CONGRUENCE, AMENABLE QUOTIENT
  §2.536 Amenable quotient of division allegory is division
  §2.542 every topos admits a faithful bicartesian representation
-/

import Fredy.S1_1
import Fredy.S2_1
import Fredy.S2_2
import Fredy.S2_3
import Fredy.S2_4


universe v u

namespace Freyd.Alg

/-! ## §2.5  Congruence and quotient allegory

  A CONGRUENCE on an allegory is an equivalence relation on morphisms
  that respects reciprocation, intersection, and composition.
  Different identity morphisms are never identified. -/

/-- A CONGRUENCE on an allegory (§2.5). -/
structure Congruence (𝒜 : Type u) [Allegory 𝒜] where
  rel {a b : 𝒜} (R S : a ⟶ b) : Prop
  refl {a b : 𝒜} (R : a ⟶ b) : rel R R
  symm {a b : 𝒜} {R S : a ⟶ b} (h : rel R S) : rel S R
  trans {a b : 𝒜} {R S T : a ⟶ b} (hRS : rel R S) (hST : rel S T) : rel R T
  recip_congr {a b : 𝒜} {R S : a ⟶ b} (h : rel R S) : rel (R°) (S°)
  inter_congr {a b : 𝒜} {R S R' S' : a ⟶ b} (hR : rel R R') (hS : rel S S') :
    rel (R ∩ S) (R' ∩ S')
  comp_congr {a b c : 𝒜} {R R' : a ⟶ b} {S S' : b ⟶ c}
    (hR : rel R R') (hS : rel S S') : rel (R ≫ S) (R' ≫ S')

/-! ## §2.521  Boolean quotient

  R ≡ S iff ∀ T, R ∩ T = 0 ↔ S ∩ T = 0 (§2.521). -/

section BooleanQuotient

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- The BOOLEAN QUOTIENT relation (§2.521). -/
def booleanQuotientRel {a b : 𝒜} (R S : a ⟶ b) : Prop :=
  ∀ (T : a ⟶ b), (R ∩ T = (𝟘 : a ⟶ b)) ↔ (S ∩ T = (𝟘 : a ⟶ b))

end BooleanQuotient

/-! ## §2.522  Closed quotient

  R ≡ S iff R ∪ (p_a ≫ U ≫ p_b°) = S ∪ (p_a ≫ U ≫ p_b°) (§2.522). -/

section ClosedQuotient

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- The CLOSED QUOTIENT relation with respect to U : T → T (§2.522). -/
def closedQuotientRel {a b T : 𝒜} (U : T ⟶ T) (p_a : a ⟶ T) (p_b : b ⟶ T) (R S : a ⟶ b) : Prop :=
  R ∪ (p_a ≫ U ≫ p_b°) = S ∪ (p_a ≫ U ≫ p_b°)

end ClosedQuotient

/-! ## §2.53  Amenable congruence

  A congruence is AMENABLE if it respects binary unions and each
  congruence class has a largest element R⁺ (§2.53). -/

section Amenable

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- An AMENABLE CONGRUENCE (§2.53). -/
structure AmenableCongruence (𝒜 : Type u) [DistributiveAllegory 𝒜] where
  cong : Congruence 𝒜
  union_congr {a b : 𝒜} {R S R' S' : a ⟶ b} (hR : cong.rel R R') (hS : cong.rel S S') :
    cong.rel (R ∪ S) (R' ∪ S')
  largest {a b : 𝒜} (R : a ⟶ b) : a ⟶ b
  largest_rel {a b : 𝒜} (R : a ⟶ b) : cong.rel R (largest R)
  largest_max {a b : 𝒜} {R S : a ⟶ b} (h : cong.rel R S) : S ⊑ largest R

/-- §2.531: If R ⊑ S, then R⁺ ⊑ S⁺. -/
theorem amenable_le_largest (amen : AmenableCongruence 𝒜) {a b : 𝒜} {R S : a ⟶ b} (h : R ⊑ S) :
    amen.largest R ⊑ amen.largest S := by
  -- R ⊑ S implies R ∪ S = S
  have h_union : R ∪ S = S := (le_iff_union_eq_left R S).mp h
  -- Congruence relates each morphism to its largest element
  have hR : amen.cong.rel R (amen.largest R) := amen.largest_rel R
  have hS : amen.cong.rel S (amen.largest S) := amen.largest_rel S
  -- Union respects the congruence
  have h_union_congr : amen.cong.rel (R ∪ S) (amen.largest R ∪ amen.largest S) :=
    amen.union_congr hR hS
  -- Using h_union, this gives: cong.rel S (largest R ∪ largest S)
  rw [h_union] at h_union_congr
  -- Now apply largest_max: if S ≡ X, then X ⊑ largest S
  have hX : amen.largest R ∪ amen.largest S ⊑ amen.largest S :=
    amen.largest_max h_union_congr
  -- Since largest R ⊑ largest R ∪ largest S, transitivity gives the result
  have h_le_union : amen.largest R ⊑ amen.largest R ∪ amen.largest S := le_union_left _ _
  exact le_trans h_le_union hX

/-- §2.532: (R ∩ S)⁺ = R⁺ ∩ S⁺. -/
theorem amenable_inter_largest (amen : AmenableCongruence 𝒜) {a b : 𝒜} (R S : a ⟶ b) :
    amen.largest (R ∩ S) = (amen.largest R) ∩ (amen.largest S) := by
  apply le_antisymm
  · -- largest(R∩S) ⊑ largest R ∩ largest S
    -- R∩S ⊑ R and R∩S ⊑ S, so by amen.le_largest, both largest(R∩S) ⊑ largest R and largest(R∩S) ⊑ largest S
    have hR : R ∩ S ⊑ R := inter_lb_left R S
    have hS : R ∩ S ⊑ S := inter_lb_right R S
    have hR' : amen.largest (R ∩ S) ⊑ amen.largest R := amenable_le_largest amen hR
    have hS' : amen.largest (R ∩ S) ⊑ amen.largest S := amenable_le_largest amen hS
    exact le_inter hR' hS'
  · -- largest R ∩ largest S ⊑ largest(R∩S)
    -- R ≡ largest R, S ≡ largest S, so by inter_congr: R∩S ≡ largest R ∩ largest S
    have hR : amen.cong.rel R (amen.largest R) := amen.largest_rel R
    have hS : amen.cong.rel S (amen.largest S) := amen.largest_rel S
    -- Use inter_congr from the underlying Congruence
    have h_inter : amen.cong.rel (R ∩ S) (amen.largest R ∩ amen.largest S) :=
      amen.cong.inter_congr hR hS
    -- Apply largest_max to the symmetric relation
    have h_symm : amen.cong.rel (amen.largest R ∩ amen.largest S) (R ∩ S) := amen.cong.symm h_inter
    -- largest_max h_symm : R∩S ⊑ largest(largest R ∩ largest S)
    -- No, largest_max goes the other way: cong.rel A B implies B ⊑ largest A
    -- So: largest_max h_inter : (largest R ∩ largest S) ⊑ largest (R∩S)
    exact amen.largest_max h_inter

/-- §2.531 (union form, used in the book's proof): R⁺ ∪ S⁺ ⊑ (R ∪ S)⁺.
    Proof: R ≡ R⁺ and S ≡ S⁺, so by union_congr R∪S ≡ R⁺∪S⁺; apply largest_max. -/
theorem amenable_union_largest_le (amen : AmenableCongruence 𝒜) {a b : 𝒜} (R S : a ⟶ b) :
    amen.largest R ∪ amen.largest S ⊑ amen.largest (R ∪ S) := by
  have hcong : amen.cong.rel (R ∪ S) (amen.largest R ∪ amen.largest S) :=
    amen.union_congr (amen.largest_rel R) (amen.largest_rel S)
  exact amen.largest_max hcong

/-- The largest-in-class operator ⁺ depends only on the congruence class:
    if R ≡ S then R⁺ = S⁺.  (Used implicitly throughout §2.533–2.535.) -/
theorem amenable_largest_class_invariant (amen : AmenableCongruence 𝒜) {a b : 𝒜}
    {R S : a ⟶ b} (h : amen.cong.rel R S) : amen.largest R = amen.largest S := by
  apply le_antisymm
  · -- Goal: R⁺ ⊑ S⁺.  S ≡ R and R ≡ R⁺, so S ≡ R⁺; largest_max gives R⁺ ⊑ S⁺.
    have hSR' : amen.cong.rel S (amen.largest R) :=
      amen.cong.trans (amen.cong.symm h) (amen.largest_rel R)
    exact amen.largest_max hSR'
  · -- Goal: S⁺ ⊑ R⁺.  R ≡ S and S ≡ S⁺, so R ≡ S⁺; largest_max gives S⁺ ⊑ R⁺.
    have hRS' : amen.cong.rel R (amen.largest S) := amen.cong.trans h (amen.largest_rel S)
    exact amen.largest_max hRS'

end Amenable

/-! ## §2.5  Quotient allegory construction

  Given a Congruence on an allegory A, the QUOTIENT ALLEGORY has the same
  objects as A and hom-sets = congruence classes.  We define the hom-setoid
  and record that quotient composition/reciprocal/intersection are
  well-defined on congruence classes (§2.5). -/

section QuotientConstruction

variable {𝒜 : Type u} [Allegory 𝒜] (C : Congruence 𝒜)

/-- The setoid on hom-sets induced by a congruence (§2.5). -/
def congSetoid {a b : 𝒜} : Setoid (a ⟶ b) where
  r := C.rel
  iseqv := ⟨C.refl, C.symm, C.trans⟩

/-- Quotient composition is well-defined on congruence classes (§2.5):
    if R ≡ R' and S ≡ S' then RS ≡ R'S'. -/
theorem quotient_comp_wellDefined {a b c : 𝒜} {R R' : a ⟶ b} {S S' : b ⟶ c}
    (hR : C.rel R R') (hS : C.rel S S') : C.rel (R ≫ S) (R' ≫ S') :=
  C.comp_congr hR hS

/-- Quotient reciprocal is well-defined on congruence classes (§2.5):
    if R ≡ R' then R° ≡ R'°. -/
theorem quotient_recip_wellDefined {a b : 𝒜} {R R' : a ⟶ b}
    (hR : C.rel R R') : C.rel (R°) (R'°) :=
  C.recip_congr hR

/-- Quotient intersection is well-defined on congruence classes (§2.5):
    if R ≡ R' and S ≡ S' then R∩S ≡ R'∩S'. -/
theorem quotient_inter_wellDefined {a b : 𝒜} {R R' S S' : a ⟶ b}
    (hR : C.rel R R') (hS : C.rel S S') : C.rel (R ∩ S) (R' ∩ S') :=
  C.inter_congr hR hS

end QuotientConstruction

/-! ## §2.521  booleanQuotientRel is a congruence (§2.521). -/

section BooleanCong

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- booleanQuotientRel is an equivalence relation (§2.521). -/
theorem booleanQuotientRel_equiv {a b : 𝒜} :
    Equivalence (booleanQuotientRel (a := a) (b := b)) :=
  ⟨fun _ _ => Iff.rfl, fun h T => (h T).symm, fun h1 h2 T => (h1 T).trans (h2 T)⟩

/-- booleanQuotientRel is a Congruence on any DistributiveAllegory (§2.521).
    (It is in fact the maximal congruence not identifying nonzeros with zero.) -/
def booleanQuotientRel_is_congruence : Congruence 𝒜 where
  rel := booleanQuotientRel
  refl _ _ := Iff.rfl
  symm h T := (h T).symm
  trans h1 h2 T := (h1 T).trans (h2 T)
  recip_congr := by
    -- R° ∩ T = 0 ↔ S° ∩ T = 0 follows from R ∩ T° = 0 ↔ S ∩ T° = 0 (apply hRS to T°)
    -- and the identity (R° ∩ T)° = R ∩ T° (taking recip of both sides).
    intro a b R S hRS
    simp only [booleanQuotientRel]
    intro T
    -- Key helper: R° ∩ T = 0 ↔ R ∩ T° = 0
    have key : ∀ (X : a ⟶ b) (Y : b ⟶ a), X° ∩ Y = (𝟘 : b ⟶ a) ↔ X ∩ Y° = (𝟘 : a ⟶ b) := by
      intro X Y
      constructor
      · intro h
        have h1 : (X° ∩ Y)° = (𝟘 : b ⟶ a)° := congrArg Allegory.recip h
        simp only [Allegory.recip_inter, Allegory.recip_recip, recip_zero] at h1
        exact h1
      · intro h
        have h1 : (X ∩ Y°)° = (𝟘 : a ⟶ b)° := congrArg Allegory.recip h
        simp only [Allegory.recip_inter, Allegory.recip_recip, recip_zero] at h1
        exact h1
    rw [key R T, key S T]
    exact hRS T°
  inter_congr := by
    -- (R∩S) ≡_bool (R'∩S') when R≡R' and S≡S'.
    -- Chain disjointness: (R∩S)∩T=0 ↔ R∩(S∩T)=0 ↔ R'∩(S∩T)=0 [hR (S∩T)]
    --   = S∩(R'∩T)=0 ↔ S'∩(R'∩T)=0 [hS (R'∩T)] = (R'∩S')∩T=0,
    -- using only associativity/commutativity of ∩.
    intro a b R S R' S' hR hS
    simp only [booleanQuotientRel] at hR hS ⊢
    intro T
    -- LHS: (R∩S)∩T = R∩(S∩T); apply hR at S∩T.
    rw [← Allegory.inter_assoc R S T, hR (S ∩ T)]
    -- Now R'∩(S∩T)=0; rewrite to S∩(R'∩T) and apply hS.
    have e1 : R' ∩ (S ∩ T) = S ∩ (R' ∩ T) := by
      rw [Allegory.inter_assoc R' S T, Allegory.inter_comm R' S, ← Allegory.inter_assoc S R' T]
    rw [e1, hS (R' ∩ T)]
    -- Now S'∩(R'∩T)=0; rewrite to (R'∩S')∩T = (R'∩S')∩T.
    rw [Allegory.inter_assoc S' R' T, Allegory.inter_comm S' R']
  comp_congr := by
    intro a b c R R' S S' hR hS
    simp only [booleanQuotientRel] at hR hS ⊢
    intro T; sorry

end BooleanCong

/-! ## §2.522  closedQuotientRel is amenable (§2.522). -/

/-- closedQuotientRel is a Congruence (§2.522).
    This is the least congruence identifying U with zero that respects unions. -/
def closedQuotientRel_is_congruence {𝒜 : Type u} [DistributiveAllegory 𝒜]
    {T : 𝒜} (U : T ⟶ T) (p_a : ∀ (a : 𝒜), a ⟶ T) (p_b : ∀ (b : 𝒜), b ⟶ T) :
    Congruence 𝒜 where
  rel {a b} R S := closedQuotientRel U (p_a a) (p_b b) R S
  refl _ := rfl
  symm h := h.symm
  trans h1 h2 := h1.trans h2
  recip_congr := by sorry
  inter_congr := by sorry
  comp_congr := by sorry

/-! ## §2.536  Amenable quotient of division allegory is division

  R / S is constructed as R⁺ / S⁺ (§2.536). -/

-- §2.536  MISSING (recorded in Fredy/S2_5.md): "An amenable quotient of a division
-- allegory is a division allegory."  Cannot be STATED faithfully: the QUOTIENT ALLEGORY
-- (equivalence classes of morphisms as a *new* allegory type, with its own Hom / comp /
-- recip / inter / division) is not constructed in this repo.  A signature of the form
-- `AmenableCongruence 𝒜 → DivisionAllegory 𝒜` would be a VACUOUS restatement (𝒜 already
-- carries a DivisionAllegory instance and `amen` would be ignored), so per the integrity
-- rule it is omitted, not stubbed.  Blocker: build the quotient-allegory type first.
--
-- The purely ALGEBRAIC heart of §2.536 — that ⁺ commutes with the division-allegory
-- operations well enough to define R/S := R⁺/S⁺ on classes — is already captured by the
-- ⁺-laws proved above (amenable_le_largest §2.531, largest_comp_le §2.534, and the
-- class-invariance amenable_largest_class_invariant).

/-! ## §2.533–535  Order, composition, reciprocal, and RST in the quotient

  For amenable congruences the largest-in-class operator ⁺ interacts with
  the allegory structure as follows (§2.533–2.535). -/

section AmenableOrder

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- §2.533 (main statement): In the quotient allegory, [R] ⊑ [S] iff R⁺ ⊑ S⁺. -/
theorem quotient_order_iff_largest (amen : AmenableCongruence 𝒜) {a b : 𝒜} (R S : a ⟶ b) :
    (∃ R' S', amen.cong.rel R R' ∧ amen.cong.rel S S' ∧ R' ⊑ S') ↔
    amen.largest R ⊑ amen.largest S := by
  constructor
  · rintro ⟨R', S', hR, hS, hle⟩
    -- ⁺ is class-invariant: largest R = largest R' and largest S = largest S'.
    have hR' : amen.largest R = amen.largest R' := amenable_largest_class_invariant amen hR
    have hS' : amen.largest S = amen.largest S' := amenable_largest_class_invariant amen hS
    rw [hR', hS']
    -- §2.531 applied to R' ⊑ S'.
    exact amenable_le_largest amen hle
  · intro h
    exact ⟨_, _, amen.largest_rel R, amen.largest_rel S, h⟩

/-- §2.534: T⁺S⁺ ⊑ (TS)⁺.
    Proof: T ≡ T⁺ and S ≡ S⁺, so T⁺S⁺ ≡ TS by comp_congr; then largest_max. -/
theorem largest_comp_le (amen : AmenableCongruence 𝒜) {a b c : 𝒜} (T : a ⟶ b) (S : b ⟶ c) :
    amen.largest T ≫ amen.largest S ⊑ amen.largest (T ≫ S) := by
  -- largest_rel T : cong.rel T (largest T), and similarly for S
  -- comp_congr gives: cong.rel (T ≫ S) (largest T ≫ largest S)
  have hcong : amen.cong.rel (T ≫ S) (amen.largest T ≫ amen.largest S) :=
    amen.cong.comp_congr (amen.largest_rel T) (amen.largest_rel S)
  -- largest_max hcong : (largest T ≫ largest S) ⊑ largest (T ≫ S)
  exact amen.largest_max hcong

/-- §2.534: (S⁺)° ⊑ (S°)⁺.
    Proof: S ≡ S⁺ ⟹ S° ≡ (S⁺)°; apply largest_max. -/
theorem largest_recip_le (amen : AmenableCongruence 𝒜) {a b : 𝒜} (S : a ⟶ b) :
    (amen.largest S)° ⊑ amen.largest (S°) := by
  -- largest_rel S : cong.rel S (largest S)
  -- recip_congr gives: cong.rel (S°) ((largest S)°)
  have hcong : amen.cong.rel (S°) ((amen.largest S)°) :=
    amen.cong.recip_congr (amen.largest_rel S)
  -- largest_max hcong : (largest S)° ⊑ largest (S°)
  exact amen.largest_max hcong

/-- §2.535: If R is reflexive, so is R⁺.
    Proof: 1 ⊑ R and R ⊑ R⁺ (largest_max (refl R) : R ⊑ largest R), so 1 ⊑ R⁺. -/
theorem largest_reflexive (amen : AmenableCongruence 𝒜) {a : 𝒜} {R : a ⟶ a}
    (hR : Reflexive R) : Reflexive (amen.largest R) := by
  -- largest_max h where h : cong.rel R S gives S ⊑ largest R.
  -- With S = R and h = cong.refl R: R ⊑ largest R.
  have hR_le : R ⊑ amen.largest R := amen.largest_max (amen.cong.refl R)
  exact le_trans hR hR_le

/-- §2.535: If R is symmetric, so is R⁺.
    Proof: R° ⊑ R ≡ R⁺, and (R⁺)° ≡ R° (by §2.534), so (R⁺)° ⊑ R⁺. -/
theorem largest_symmetric (amen : AmenableCongruence 𝒜) {a : 𝒜} {R : a ⟶ a}
    (hR : Symmetric R) : Symmetric (amen.largest R) := by
  -- Want: (R⁺)° ⊑ R⁺.
  -- (R⁺)° ⊑ (R°)⁺   [§2.534]
  have h1 : (amen.largest R)° ⊑ amen.largest (R°) := largest_recip_le amen R
  -- R° ⊑ R   [hR], so (R°)⁺ ⊑ R⁺   [§2.531]
  have h2 : amen.largest (R°) ⊑ amen.largest R := amenable_le_largest amen hR
  exact le_trans h1 h2

/-- §2.535: If R is transitive, so is R⁺.
    Proof: R⁺R⁺ ⊑ (RR)⁺ ⊑ R⁺ (using §2.534 and §2.531). -/
theorem largest_transitive (amen : AmenableCongruence 𝒜) {a : 𝒜} {R : a ⟶ a}
    (hR : Transitive R) : Transitive (amen.largest R) := by
  -- Want: R⁺ ≫ R⁺ ⊑ R⁺.
  -- R⁺R⁺ ⊑ (RR)⁺   [§2.534]
  have h1 : amen.largest R ≫ amen.largest R ⊑ amen.largest (R ≫ R) := largest_comp_le amen R R
  -- RR ⊑ R  [hR], so (RR)⁺ ⊑ R⁺  [§2.531]
  have h2 : amen.largest (R ≫ R) ⊑ amen.largest R := amenable_le_largest amen hR
  exact le_trans h1 h2

end AmenableOrder

/-! ## §2.56  Separated objects and dense relations

  Working in an amenable quotient of an allegory.
  An object A is SEPARATED if 1_A = 1_A⁺.
  A relation R : A → B is DENSE if R is congruent to the maximal relation
  (i.e., R⁺ is entire) (§2.563). -/

section SeparatedDense

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- An object A is SEPARATED (§2.563) if its identity is its own largest element:
    1_A = 1_A⁺ in the congruence.  Equivalently, every congruent morphism above 1_A is 1_A. -/
def Separated (amen : AmenableCongruence 𝒜) (A : 𝒜) : Prop :=
  amen.largest (Cat.id A) = Cat.id A

/-- A relation R : A → B is DENSE (§2.563) if it is congruent to the maximal
    relation from A to B, i.e., R⁺ is an entire morphism in the original allegory
    (its domain is 1_A). -/
def Dense (amen : AmenableCongruence 𝒜) {A B : 𝒜} (R : A ⟶ B) : Prop :=
  Entire (amen.largest R)

end SeparatedDense

/-! ## §2.542  Every topos admits a faithful bicartesian
    representation to a boolean topos (§2.542).

    MISSING (recorded in Fredy/S2_5.md): this theorem cannot be STATED faithfully
    in this repo yet.  It quantifies over toposes / boolean toposes and asserts the
    existence of a faithful bicartesian *representation* — none of `Topos`,
    `BooleanTopos`, nor the representation-of-allegories morphism is constructed
    here.  Per the integrity rule we do NOT emit a `: True` stub; the prior such
    stub has been removed. -/

end Freyd.Alg
