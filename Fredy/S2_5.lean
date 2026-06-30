import Fredy.S1_1
import Fredy.S2_1
import Fredy.S2_2
import Fredy.S2_3
import Fredy.S2_4
import Fredy.S2_147_MapCat

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* §2.5  Quotient allegories.

  §2.5  CONGRUENCE on an allegory, QUOTIENT ALLEGORY
  §2.521 BOOLEAN QUOTIENT
  §2.522 CLOSED QUOTIENT
  §2.53 AMENABLE CONGRUENCE, AMENABLE QUOTIENT
  §2.536 Amenable quotient of division allegory is division
  §2.542 every topos admits a faithful bicartesian representation
-/




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

/-- `X ⊑ 𝟘` forces `X = 𝟘` (𝟘 is the least element). -/
private theorem le_zero {a b : 𝒜} {X : a ⟶ b} (h : X ⊑ (𝟘 : a ⟶ b)) : X = (𝟘 : a ⟶ b) :=
  le_antisymm h (zero_le X)

/-- `R ∩ 𝟘 = 𝟘`. -/
private theorem inter_zero {a b : 𝒜} (R : a ⟶ b) : R ∩ (𝟘 : a ⟶ b) = (𝟘 : a ⟶ b) := by
  rw [Allegory.inter_comm]; exact zero_le R

/-- SCHRÖDER disjointness (§2.11, modular law): `(R≫S) ∩ T = 𝟘 ↔ (T≫S°) ∩ R = 𝟘`.
    Both directions are the modular law: `(R≫S)∩T ⊑ (R ∩ T≫S°)≫S`, and if the
    other side is `𝟘` the bracket vanishes, so the composite is `𝟘`. -/
private theorem disjoint_schroder {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S) ∩ T = (𝟘 : a ⟶ c) ↔ (T ≫ S°) ∩ R = (𝟘 : a ⟶ b) := by
  constructor
  · intro h
    -- modular_le T S° R : (T≫S°) ∩ R ⊑ (T ∩ R≫S°°)≫S°.  S°° = S.
    have hmod := modular_le T S° R
    rw [Allegory.recip_recip] at hmod
    -- T ∩ R≫S = 𝟘 (from h via commutativity), so the bracket is 𝟘.
    have hbr : T ∩ (R ≫ S) = (𝟘 : a ⟶ c) := by rw [Allegory.inter_comm]; exact h
    rw [hbr, DistributiveAllegory.zero_comp] at hmod
    exact le_zero hmod
  · intro h
    have hmod := modular_le R S T
    -- modular_le R S T : (R≫S) ∩ T ⊑ (R ∩ T≫S°)≫S.  Bracket R ∩ T≫S° = 𝟘 from h.
    have hbr : R ∩ (T ≫ S°) = (𝟘 : a ⟶ b) := by rw [Allegory.inter_comm]; exact h
    rw [hbr, DistributiveAllegory.zero_comp] at hmod
    exact le_zero hmod

/-- Disjointness is invariant under reciprocation: `X ∩ Y = 𝟘 ↔ X° ∩ Y° = 𝟘`. -/
private theorem recip_disjoint {a b : 𝒜} (X Y : a ⟶ b) :
    X ∩ Y = (𝟘 : a ⟶ b) ↔ X° ∩ Y° = (𝟘 : b ⟶ a) := by
  constructor
  · intro h
    have h1 : (X ∩ Y)° = (𝟘 : a ⟶ b)° := congrArg Allegory.recip h
    rwa [Allegory.recip_inter, recip_zero] at h1
  · intro h
    have h1 : (X° ∩ Y°)° = (𝟘 : b ⟶ a)° := congrArg Allegory.recip h
    rwa [Allegory.recip_inter, Allegory.recip_recip, Allegory.recip_recip, recip_zero] at h1

/-- SCHRÖDER disjointness, second form: `(R≫S) ∩ T = 𝟘 ↔ (R°≫T) ∩ S = 𝟘`.
    Reduce to `disjoint_schroder` by reciprocating the disjointness. -/
private theorem disjoint_schroder' {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S) ∩ T = (𝟘 : a ⟶ c) ↔ (R° ≫ T) ∩ S = (𝟘 : b ⟶ c) := by
  rw [recip_disjoint (R ≫ S) T, Allegory.recip_comp]
  -- (S°≫R°) ∩ T° = 𝟘 ↔ (T°≫R°°) ∩ S° = 𝟘  by disjoint_schroder S° R° T°
  rw [disjoint_schroder S° R° T°, Allegory.recip_recip]
  -- (T°≫R) ∩ S° = 𝟘 ↔ (R°≫T) ∩ S = 𝟘  by recip_disjoint
  rw [recip_disjoint (T° ≫ R) S°, Allegory.recip_comp, Allegory.recip_recip,
    Allegory.recip_recip]

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
    intro T
    -- Disjointness chain using the two Schröder forms and hR/hS:
    -- (RS)∩T=0 ↔ (TS°)∩R=0 ↔[hR] (TS°)∩R'=0 ↔ (R'S)∩T=0
    --        ↔ (R'°T)∩S=0 ↔[hS] (R'°T)∩S'=0 ↔ (R'S')∩T=0.
    calc (R ≫ S) ∩ T = (𝟘 : a ⟶ c)
        ↔ (T ≫ S°) ∩ R = (𝟘 : a ⟶ b) := disjoint_schroder R S T
      _ ↔ R ∩ (T ≫ S°) = (𝟘 : a ⟶ b) := by rw [Allegory.inter_comm]
      _ ↔ R' ∩ (T ≫ S°) = (𝟘 : a ⟶ b) := hR (T ≫ S°)
      _ ↔ (T ≫ S°) ∩ R' = (𝟘 : a ⟶ b) := by rw [Allegory.inter_comm]
      _ ↔ (R' ≫ S) ∩ T = (𝟘 : a ⟶ c) := (disjoint_schroder R' S T).symm
      _ ↔ (R'° ≫ T) ∩ S = (𝟘 : b ⟶ c) := disjoint_schroder' R' S T
      _ ↔ S ∩ (R'° ≫ T) = (𝟘 : b ⟶ c) := by rw [Allegory.inter_comm]
      _ ↔ S' ∩ (R'° ≫ T) = (𝟘 : b ⟶ c) := hS (R'° ≫ T)
      _ ↔ (R'° ≫ T) ∩ S' = (𝟘 : b ⟶ c) := by rw [Allegory.inter_comm]
      _ ↔ (R' ≫ S') ∩ T = (𝟘 : a ⟶ c) := (disjoint_schroder' R' S' T).symm

end BooleanCong

/-! ## §2.522  closedQuotientRel is amenable (§2.522). -/

/-- Dual distributivity `(R ∩ S) ∪ K = (R ∪ K) ∩ (S ∪ K)`, derived from
    `inter_union_distrib` and absorption (standard distributive-lattice fact). -/
private theorem union_inter_distrib {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜}
    (R S K : a ⟶ b) : (R ∩ S) ∪ K = (R ∪ K) ∩ (S ∪ K) := by
  -- Work from the RHS: (R∪K)∩(S∪K) = ((R∪K)∩S) ∪ ((R∪K)∩K).
  rw [DistributiveAllegory.inter_union_distrib (R ∪ K) S K]
  -- (R∪K)∩K = K  (absorption: (R∪K)∩K = K by inter_union_absorb K R after union_comm).
  have hk : (R ∪ K) ∩ K = K := by
    rw [DistributiveAllegory.union_comm R K]; exact DistributiveAllegory.inter_union_absorb K R
  rw [hk]
  -- (R∪K)∩S = S∩(R∪K) = (S∩R) ∪ (S∩K).
  rw [Allegory.inter_comm (R ∪ K) S, DistributiveAllegory.inter_union_distrib S R K]
  -- (S∩R) ∪ (S∩K) ∪ K = (S∩R) ∪ ((S∩K) ∪ K) = (S∩R) ∪ K = (R∩S) ∪ K.
  rw [← DistributiveAllegory.union_assoc, DistributiveAllegory.union_comm (S ∩ K) K,
    DistributiveAllegory.union_inter_absorb K S, Allegory.inter_comm S R]

/-- closedQuotientRel is a Congruence (§2.522).
    This is the least congruence identifying `U` with zero that respects unions.

    In the book's setting `T` is the *unit* `A` of a unitary distributive allegory,
    `p` is the canonical family of (entire) maps `p a : a ⟶ A`, and `U : A ⟶ A` is
    symmetric.  The closed-quotient term is `K_{ab} = p a ≫ U ≫ (p b)°`; the relation
    is `R ≡ S ⟺ R ∪ K = S ∪ K`.  Verifying the congruence axioms needs exactly the
    facts that hold in that unitary context and are recorded here as hypotheses:

    * `hU : U° = U` — `U` is symmetric (a coreflexive/closed element on the unit).
      Makes `K_{ab}° = K_{ba}`, so the relation respects reciprocation.
    * `hL R : R ≫ (p b ≫ U ≫ (p c)°) ⊑ p a ≫ U ≫ (p c)°` — `K` absorbs on the left.
    * `hR' S : (p a ≫ U ≫ (p b)°) ≫ S ⊑ p a ≫ U ≫ (p c)°` — `K` absorbs on the right.

    `(hL, hR')` say `K` is a two-sided ideal (so it absorbs cross terms in a product),
    which in the unitary context follows from the maximality of the unit projections
    `R ≫ p b ⊑ p a` together with `U ≫ U ⊑ U`. They are the genuine content of the
    book's `K = R⁺` claim, stated here as the precise proof obligations. -/
def closedQuotientRel_is_congruence {𝒜 : Type u} [DistributiveAllegory 𝒜]
    {T : 𝒜} (U : T ⟶ T) (p : ∀ (a : 𝒜), a ⟶ T) (hU : U° = U)
    (hL : ∀ {a b c : 𝒜} (R : a ⟶ b),
      R ≫ (p b ≫ U ≫ (p c)°) ⊑ p a ≫ U ≫ (p c)°)
    (hR' : ∀ {a b c : 𝒜} (S : b ⟶ c),
      (p a ≫ U ≫ (p b)°) ≫ S ⊑ p a ≫ U ≫ (p c)°) :
    Congruence 𝒜 where
  rel {a b} R S := closedQuotientRel U (p a) (p b) R S
  refl _ := rfl
  symm h := h.symm
  trans h1 h2 := h1.trans h2
  recip_congr := by
    intro a b R R' hR
    -- closedQuotientRel U (p a) (p b) R R' : R ∪ K_ab = R' ∪ K_ab,  K_ab = p a ≫ U ≫ (p b)°.
    -- Goal: closedQuotientRel U (p b) (p a) R° R'° : R° ∪ K_ba = R'° ∪ K_ba.
    simp only [closedQuotientRel] at hR ⊢
    -- K_ba = p b ≫ U ≫ (p a)° = (p a ≫ U ≫ (p b)°)°  using U° = U.
    have hKrecip : p b ≫ U ≫ (p a)° = (p a ≫ U ≫ (p b)°)° := by
      rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, hU, Cat.assoc]
    rw [hKrecip]
    -- Apply ° to hR : (R ∪ K_ab)° = (R' ∪ K_ab)°, i.e. K_ab° ∪ R° = K_ab° ∪ R'°.
    have h1 : (R ∪ (p a ≫ U ≫ (p b)°))° = (R' ∪ (p a ≫ U ≫ (p b)°))° := congrArg Allegory.recip hR
    rw [recip_union, recip_union] at h1
    -- h1 : (p a ≫ U ≫ (p b)°)° ∪ R° = (p a ≫ U ≫ (p b)°)° ∪ R'°.  Commute to match goal.
    rw [DistributiveAllegory.union_comm R° _, DistributiveAllegory.union_comm R'° _]
    exact h1
  inter_congr := by
    intro a b R S R' S' hR hS
    -- closedQuotientRel: R ∪ K = R' ∪ K and S ∪ K = S' ∪ K, K = p a ≫ U ≫ (p b)°.
    simp only [closedQuotientRel] at hR hS ⊢
    -- (R∩S)∪K = (R∪K)∩(S∪K) = (R'∪K)∩(S'∪K) = (R'∩S')∪K.
    rw [union_inter_distrib, hR, hS, ← union_inter_distrib]
  comp_congr := by
    intro a b c R R' S S' hR hS
    -- hR : R ∪ K_ab = R' ∪ K_ab,  hS : S ∪ K_bc = S' ∪ K_bc.
    -- Goal: (R≫S) ∪ K_ac = (R'≫S') ∪ K_ac,  K_xy = p x ≫ U ≫ (p y)°.
    simp only [closedQuotientRel] at hR hS ⊢
    -- Both sides equal (R∪K_ab) ≫ (S∪K_bc) ∪ K_ac: the cross terms R·K_bc, K_ab·S,
    -- K_ab·K_bc are all ⊑ K_ac (ideal absorption hL/hR'), hence absorbed by ∪ K_ac.
    have expand : ∀ (X : a ⟶ b) (Y : b ⟶ c),
        (X ≫ Y) ∪ (p a ≫ U ≫ (p c)°)
          = (X ∪ (p a ≫ U ≫ (p b)°)) ≫ (Y ∪ (p b ≫ U ≫ (p c)°)) ∪ (p a ≫ U ≫ (p c)°) := by
      intro X Y
      -- Set Kab, Kbc, Kac; the product expands into XY plus three cross terms.
      have hprod : (X ∪ (p a ≫ U ≫ (p b)°)) ≫ (Y ∪ (p b ≫ U ≫ (p c)°))
          = (X ≫ Y) ∪ (X ≫ (p b ≫ U ≫ (p c)°))
            ∪ ((p a ≫ U ≫ (p b)°) ≫ Y) ∪ ((p a ≫ U ≫ (p b)°) ≫ (p b ≫ U ≫ (p c)°)) := by
        rw [union_comp_distrib, DistributiveAllegory.comp_union_distrib,
          DistributiveAllegory.comp_union_distrib, DistributiveAllegory.union_assoc]
      -- The three cross terms are all ⊑ Kac (left/right ideal absorption).
      have a1 : X ≫ (p b ≫ U ≫ (p c)°) ⊑ p a ≫ U ≫ (p c)° := hL X
      have a2 : (p a ≫ U ≫ (p b)°) ≫ Y ⊑ p a ≫ U ≫ (p c)° := hR' Y
      have a3 : (p a ≫ U ≫ (p b)°) ≫ (p b ≫ U ≫ (p c)°) ⊑ p a ≫ U ≫ (p c)° := hL _
      apply le_antisymm
      · -- XY ∪ Kac ⊑ product ∪ Kac.
        apply union_lub
        · -- XY ⊑ product ⊑ product ∪ Kac.
          refine le_trans ?_ (le_union_left _ _)
          rw [hprod]
          exact le_trans (le_union_left _ _)
            (le_trans (le_union_left _ _) (le_union_left _ _))
        · exact le_union_right _ _
      · -- product ∪ Kac ⊑ XY ∪ Kac.
        apply union_lub
        · rw [hprod]
          -- each of the four summands ⊑ XY ∪ Kac.
          refine union_lub (union_lub (union_lub ?_ ?_) ?_) ?_
          · exact le_union_left _ _
          · exact le_trans a1 (le_union_right _ _)
          · exact le_trans a2 (le_union_right _ _)
          · exact le_trans a3 (le_union_right _ _)
        · exact le_union_right _ _
    rw [expand R S, expand R' S', hR, hS]

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
  A relation R : A → B is DENSE if it is congruent to the maximal relation from
  A to B (§2.563). -/

section SeparatedDense

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- An object A is SEPARATED (§2.563) if its identity is its own largest element:
    1_A = 1_A⁺ in the congruence.  Equivalently, every congruent morphism above 1_A is 1_A. -/
def Separated (amen : AmenableCongruence 𝒜) (A : 𝒜) : Prop :=
  amen.largest (Cat.id A) = Cat.id A

end SeparatedDense

/-! ### Dense relations need a maximal (top) relation

  Book §2.563 defines `R : A → B` to be DENSE iff it is *congruent to the maximal
  relation* from A to B.  The "maximal relation" `⊤ : A → B` is the top of the
  hom-lattice — but a bare `DistributiveAllegory` has NO top element, so the
  faithful condition is not even *stateable* there (this was an audit defect: the
  old `Dense := Entire (largest R)`, i.e. `dom R⁺ = 1`, is a genuinely *different,
  weaker* condition).  §2.563 itself works in an effective *tabular unitary
  division* allegory, and §2.55 runs amenable quotients of *locally complete*
  allegories — exactly the setting where the maximal relation exists as
  `Sup (fun _ => True)`.  We therefore state `Dense` in a
  `LocallyCompleteDistributiveAllegory`, where the top relation is available. -/

section Dense

open LocallyCompleteDistributiveAllegory

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-- The MAXIMAL relation from `a` to `b`: the supremum of all relations, i.e. the
    top of the hom-lattice `(a, b)`.  Stateable only because the allegory is
    locally complete (§2.22). -/
def topRel (a b : 𝒜) : a ⟶ b := Sup (fun _ : a ⟶ b => True)

/-- `topRel` is the greatest relation: every `R : a ⟶ b` is below it. -/
theorem le_topRel {a b : 𝒜} (R : a ⟶ b) : R ⊑ topRel a b :=
  le_Sup (P := fun _ : a ⟶ b => True) trivial

/-- A relation `R : A → B` is DENSE (§2.563) iff it is CONGRUENT to the maximal
    relation `⊤ : A → B`.  This is the faithful book condition (`R ≡ ⊤`), now
    stateable because the locally complete allegory has a top relation `topRel`. -/
def Dense (amen : AmenableCongruence 𝒜) {A B : 𝒜} (R : A ⟶ B) : Prop :=
  amen.cong.rel R (topRel A B)

/-- §2.533-style characterization: `R` is dense iff `R⁺ = ⊤`.  (Congruence classes
    are detected by their largest element: `R ≡ S ↔ R⁺ = S⁺`, and `⊤⁺ = ⊤` since
    `⊤` is already maximal.)  This connects `Dense` to the largest-element calculus
    used throughout §2.53. -/
theorem dense_iff_largest_eq_top (amen : AmenableCongruence 𝒜) {A B : 𝒜}
    (R : A ⟶ B) : Dense amen R ↔ amen.largest R = topRel A B := by
  constructor
  · -- R ≡ ⊤  ⟹  ⊤ ⊑ R⁺  (by largest_max), and R⁺ ⊑ ⊤  (top), so R⁺ = ⊤.
    intro hR
    exact le_antisymm (le_topRel _) (amen.largest_max hR)
  · -- R⁺ = ⊤  ⟹  R ≡ R⁺ = ⊤.
    intro hRplus
    have hRrel : amen.cong.rel R (amen.largest R) := amen.largest_rel R
    rwa [hRplus] at hRrel

end Dense

/-! ## §2.51  Quotient of tabular/unitary allegory

  BOOK §2.51: A quotient of a tabular (resp. unitary) allegory is such.
  CANNOT BE STATED: the quotient allegory is not constructed as a type in this repo.
  The algebraic content is that the equivalence class of an entire/simple/tabular morphism
  is such in the quotient, and the class of a (partial) unit is a (partial) unit.
  Blocker: build the quotient-allegory type (QuotAllegory). -/

/-! ## §2.537  Amenable quotient of effective power allegory

  BOOK §2.537: An amenable quotient of an effective power allegory is an effective power allegory.
  CANNOT BE STATED: the quotient allegory type is not constructed in this repo.
  Key steps: effectivity is preserved by §2.535 (largest_reflexive/symmetric/transitive);
  the quotient is a pre-power allegory because ∋_R is thick in the quotient [§2.432].
  Blocker: build the quotient-allegory type (QuotAllegory). -/

/-! ## §2.54  Coreflexive naming in amenable quotient -/

section Coreflexive54

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- §2.54: Every coreflexive morphism of an amenable quotient allegory is named by
    a coreflexive morphism of the given allegory.
    More precisely: if S is congruent (in amen) to a sub-identity (i.e., the class
    [S] is coreflexive in the quotient), then there exists a coreflexive R in 𝒜
    with amen.cong.rel S R.
    Proof: Let R = dom(S) = 1 ∩ SS° (the domain coreflexive of S) [§2.122].
    Since S is a symmetric idempotent [§2.12], R = 1 ∩ SS° = S.
    Actually the book takes R = 1 ∩ SS° directly; since S ≡ S⁺ ⊑ 1 the class is S itself.
    The exact statement: if [S] ⊑ [1] (i.e., S⁺ ⊑ 1), then 1 ∩ SS° ⊑ 1 is coreflexive
    and cong.rel S (1 ∩ SS°). -/
theorem quotient_coreflexive_named (amen : AmenableCongruence 𝒜) {a : 𝒜} (S : a ⟶ a)
    (h : amen.largest S ⊑ Cat.id a) :
    Coreflexive (dom S) ∧ amen.cong.rel S (dom S) := by
  constructor
  · -- dom S = 1 ∩ SS° ⊑ 1, so coreflexive by definition
    exact dom_coreflexive S
  · -- S ≡ dom(S).
    -- Route: S ≡ S⁺ (largest_rel), dom(S) ≡ dom(S⁺) (congruence-compat),
    -- and dom(S⁺) = S⁺ because S⁺ is coreflexive (S⁺ ⊑ 1 = h).
    have hS_rel : amen.cong.rel S (amen.largest S) := amen.largest_rel S
    -- dom(S) ≡ dom(S⁺) via comp_congr + recip_congr + inter_congr.
    have hdom_cong : amen.cong.rel (dom S) (dom (amen.largest S)) :=
      amen.cong.inter_congr (amen.cong.refl _)
        (amen.cong.comp_congr hS_rel (amen.cong.recip_congr hS_rel))
    -- dom(S⁺) = S⁺: S⁺ ⊑ 1 implies S⁺ symmetric+idempotent, so
    --   S⁺(S⁺)° = S⁺ S⁺ = S⁺  and  1 ∩ S⁺ = S⁺.
    have hcoref : Coreflexive (amen.largest S) := h
    obtain ⟨hSym, hIdem⟩ := coreflexive_symmetric_idempotent hcoref
    have hSo : (amen.largest S)° = amen.largest S := symmetric_eq hSym
    have hdom_sp : dom (amen.largest S) = amen.largest S := by
      dsimp [dom]
      rw [hSo, hIdem, Allegory.inter_comm]
      exact inter_eq_left h
    -- Combine: S ≡ S⁺ = dom(S⁺) ≡ dom(S), so S ≡ dom(S).
    rw [hdom_sp] at hdom_cong
    exact amen.cong.trans hS_rel (amen.cong.symm hdom_cong)

end Coreflexive54

/-! ## §2.55  Amenable quotient of locally/globally complete allegory

  BOOK §2.55: An amenable quotient of a locally (resp. globally) complete allegory
  is locally (resp. globally) complete.
  CANNOT BE STATED FULLY: the quotient allegory type is not constructed in this repo.
  The algebraic content (already usable): if Sᵢ ≡ Tᵢ for each i, then ⋃ᵢ Sᵢ ≡ ⋃ᵢ Tᵢ,
  so the quotient inherits local completeness.  The key sub-lemma (⋃ᵢ Rᵢ⁺ ≡ (⋃ᵢ Rᵢ)⁺)
  uses `amenable_union_largest_le` and `amenable_le_largest`.
  Blocker: quotient-allegory type construction. -/

/-! ## §2.542  Every topos admits a faithful bicartesian
    representation to a boolean topos (§2.542).

    MISSING: this theorem cannot be STATED faithfully in this repo yet.  It quantifies
    over toposes / boolean toposes and asserts the existence of a faithful bicartesian
    *representation* — none of `Topos`, `BooleanTopos`, nor the representation-of-allegories
    morphism is constructed here.  Per the integrity rule we do NOT emit a `: True` stub. -/

/-! ## §2.563  Dense relations and separated objects: map-naming theorem

  §2.563: If B is separated, then any map A → B in the boolean quotient is named
  by a simple relation whose domain is a dense subobject of A.
  PROVED: `map_in_quotient_named_by_simple` below. -/

section Naming563

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-- §2.563: If B is separated (1_B = 1_B⁺) and R : A → B is entire and simple in
    the amenable quotient (i.e., [R]° ≫ [R] ⊑ [1_B] and [1_A] ⊑ [R] ≫ [R]°),
    then there exists a simple S : A → B in 𝒜 such that [S] = [R] and dom(S) is dense.
    Expressed purely in terms of the largest-element calculus:
    if (R⁺)°(R⁺) ⊑ 1_B (simplicity in the original, using B separated: 1_B⁺=1_B)
    and the domain of R is congruent to 1_A, then (R⁺) is simple and dom(R⁺) ≡ 1_A (dense). -/
theorem map_in_quotient_named_by_simple (amen : AmenableCongruence 𝒜) {A B : 𝒜}
    (R : A ⟶ B)
    (hB_sep : Separated amen B)
    (hR_simple : (amen.largest R)° ≫ (amen.largest R) ⊑ Cat.id B)
    (hR_entire : Dense amen (dom R)) :
    Simple (amen.largest R) ∧ Dense amen (dom (amen.largest R)) := by
  constructor
  · -- (R⁺)°(R⁺) ⊑ 1_B  is exactly hR_simple
    exact hR_simple
  · -- dom(R⁺) ≡ dom(R) ≡ ⊤ (dense in A)
    -- R ≡ R⁺ ⟹ dom(R) ≡ dom(R⁺) by unfolding dom = 1 ∩ R≫R° and using comp_congr + recip_congr.
    have hR_rel : amen.cong.rel R (amen.largest R) := amen.largest_rel R
    have hdom_rel : amen.cong.rel (dom R) (dom (amen.largest R)) :=
      amen.cong.inter_congr (amen.cong.refl _)
        (amen.cong.comp_congr hR_rel (amen.cong.recip_congr hR_rel))
    exact amen.cong.trans (amen.cong.symm hdom_rel) hR_entire

end Naming563

/-! ## §2.56  Independence of the Axiom of Choice: example constructions

  §2.56 constructs a specific 2-valued boolean Grothendieck topos (category of
  functors 𝒮^{A°} quotiented by the boolean congruence of Rel(𝒮^{A°})) to show
  IAC fails.  The constructions involve:
  - A specific category A of non-zero finite ordinals with source-target condition
  - Representable presheaves H_n = (−, n): A° → 𝒮
  - A boolean topos B = Maps(boolean quotient of Rel(𝒮^{A°}))
  These are not abstract allegory-theoretic statements but specific set-theoretic
  examples.  They cannot be stated in the abstract Cat/Allegory framework of this repo
  without building the presheaf/functor-category machinery first.

  BOOK §2.561: Objects of A are non-zero finite ordinals; morphism m → n iff m ≥ n.
  BOOK §2.562: B is two-valued.
  BOOK §2.563 (sep'd/dense property, above): see `map_in_quotient_named_by_simple`.
  BOOK §2.565: Representable functors H_n = (−, n) in 𝒮^{A°} are separated.
  BOOK §2.566: If f ≠ g : m → n in A, then H_f and H_g have disjoint images in 𝒮^{A°}.
  BOOK §2.567: For each n, there exists a jointly monic countable collection H_n → 2 in B.
  BOOK §2.56(10): Given f: m→n and g: m→n+1 in A, ∃ h, h': m+1→m with hf=h'f and hg=h'g.
  BOOK §2.56(12): In B, the product ΠH_n is the empty functor.

  All of §2.561–§2.56(12) are TODO pending presheaf/functor-category infrastructure. -/

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* §2.5  The QUOTIENT ALLEGORY.

  Given a `Congruence C` on an allegory `𝒜` (§2.5), the QUOTIENT ALLEGORY
  `QuotAllegory 𝒜 C` has the SAME objects as `𝒜` and hom-sets the congruence
  classes `Quotient (congSetoid C)`.  Composition, reciprocation and
  intersection descend to classes (`quotient_comp/recip/inter_wellDefined`,
  S2_5), so `QuotAllegory 𝒜 C` is an allegory and the assignment of equivalence
  classes `R ↦ [R]` is a representation of allegories (`quotRep`, an
  `AllegoryFunctor`).  This is the book's

      "the allegory of equivalence classes with the obvious operations
       (which makes the assignment of equivalence classes into a
       representation of allegories)."

  §2.52: if the congruence also respects binary unions, the quotient is a
  DISTRIBUTIVE ALLEGORY and `quotRep` is a representation of distributive
  allegories (`QuotAllegory.instDistributiveAllegory`, `quotRep_map_union`,
  `quotRep_map_zero`).  Zero is the class of `𝟘` — a constant, so it descends
  with NO extra hypothesis: this is the book's "any congruence on a
  distributive allegory respects zero".
-/



namespace Freyd.Alg

/-! ## §2.5  The quotient-allegory type

  A type synonym on `𝒜`'s objects, carrying the congruence `C` in its type so a
  fresh `Cat`/`Allegory` structure (hom = congruence class) can be hung on it
  without colliding with `𝒜`'s own structure. -/

/-- §2.5  The QUOTIENT ALLEGORY `𝒜/C`: same objects as `𝒜`, homs = congruence
    classes.  (Body ignores `_C`; the parameter is carried only to key the
    instances below.) -/
def QuotAllegory (𝒜 : Type u) [Allegory 𝒜] (_C : Congruence 𝒜) : Type u := 𝒜

/-! ## §2.5  Category structure: hom-classes under congruence -/

/-- §2.5  `Cat (𝒜/C)`: `Hom a b = Quotient (congSetoid C)`, identity `[1]`,
    composition the lift of `≫` (well-defined by `quotient_comp_wellDefined`). -/
instance QuotAllegory.instCat {𝒜 : Type u} [Allegory 𝒜] (C : Congruence 𝒜) :
    Cat (QuotAllegory 𝒜 C) where
  Hom a b := Quotient (congSetoid C (a := a) (b := b))
  id a := Quotient.mk (congSetoid C) (@Cat.id 𝒜 _ a)
  comp {a b c} := Quotient.lift₂
    (fun R S => Quotient.mk (congSetoid C) (R ≫ S))
    (fun _ _ _ _ hR hS => Quotient.sound (quotient_comp_wellDefined C hR hS))
  id_comp := by
    intro a b f
    refine Quotient.inductionOn f (fun R => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Cat.id_comp R)
  comp_id := by
    intro a b f
    refine Quotient.inductionOn f (fun R => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Cat.comp_id R)
  assoc := by
    intro a b c d f g h
    refine Quotient.inductionOn₃ f g h (fun R S T => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Cat.assoc R S T)

/-! ## §2.5  Allegory structure: reciprocation and intersection on classes -/

/-- §2.5  `Allegory (𝒜/C)`: `[R]° = [R°]`, `[R] ∩ [S] = [R ∩ S]` (well-defined
    by `quotient_recip/inter_wellDefined`).  Every allegory axiom is the lift of
    `𝒜`'s — proved by inducting on the class representatives down to `𝒜`'s law. -/
instance QuotAllegory.instAllegory {𝒜 : Type u} [Allegory 𝒜] (C : Congruence 𝒜) :
    Allegory (QuotAllegory 𝒜 C) where
  recip {a b} := Quotient.lift
    (fun R => Quotient.mk (congSetoid C) (R°))
    (fun _ _ hR => Quotient.sound (quotient_recip_wellDefined C hR))
  inter {a b} := Quotient.lift₂
    (fun R S => Quotient.mk (congSetoid C) (R ∩ S))
    (fun _ _ _ _ hR hS => Quotient.sound (quotient_inter_wellDefined C hR hS))
  recip_recip := by
    intro a b R
    refine Quotient.inductionOn R (fun r => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.recip_recip r)
  recip_comp := by
    intro a b c R S
    refine Quotient.inductionOn₂ R S (fun r s => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.recip_comp r s)
  recip_inter := by
    intro a b R S
    refine Quotient.inductionOn₂ R S (fun r s => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.recip_inter r s)
  inter_idem := by
    intro a b R
    refine Quotient.inductionOn R (fun r => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.inter_idem r)
  inter_comm := by
    intro a b R S
    refine Quotient.inductionOn₂ R S (fun r s => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.inter_comm r s)
  inter_assoc := by
    intro a b R S T
    refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.inter_assoc r s t)
  semidistrib := by
    intro a b c R S T
    refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.semidistrib r s t)
  modular := by
    intro a b c R S T
    refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.modular r s t)

/-! ## §2.5  The representation `R ↦ [R]` -/

/-- §2.5  The ASSIGNMENT OF EQUIVALENCE CLASSES `R ↦ [R]` as a REPRESENTATION of
    allegories: an `AllegoryFunctor 𝒜 → 𝒜/C`, identity on objects.  All four
    functor laws hold definitionally (`[1] = 1`, `[R≫S] = [R]≫[S]`, etc.). -/
def quotRep {𝒜 : Type u} [Allegory 𝒜] (C : Congruence 𝒜) :
    AllegoryFunctor 𝒜 (QuotAllegory 𝒜 C) where
  obj a := a
  map {a b} R := Quotient.mk (congSetoid C) R
  map_id a := rfl
  map_comp R S := rfl
  map_recip R := rfl
  map_inter R S := rfl

/-- `quotRep` is faithful exactly when `C` is the discrete congruence; in
    general it is the canonical quotient map.  `[R]` of `R` unfolds to the
    class. -/
theorem quotRep_map {𝒜 : Type u} [Allegory 𝒜] (C : Congruence 𝒜) {a b : 𝒜} (R : a ⟶ b) :
    (quotRep C).map R = Quotient.mk (congSetoid C) R := rfl

/-! ## §2.52  Distributive quotient

  If the congruence respects binary unions, the quotient is distributive and
  `quotRep` preserves `∪` and `𝟘`.  The union hypothesis cannot be derived from
  a bare `Congruence` (it is exactly the extra closure the book demands), so it
  is taken as an explicit argument; zero needs none.  Because the union
  hypothesis is not part of `Congruence`, this is delivered as a `def`
  (apply via `letI`/`haveI`), not a global `instance`. -/

/-- §2.52  If `C` respects binary unions, `𝒜/C` is a DISTRIBUTIVE ALLEGORY.
    Zero `= [𝟘]` (a constant: descends with no hypothesis — "any congruence on a
    distributive allegory respects zero"); union `= [R ∪ S]`, well-defined by
    `hunion`.  Every distributive-lattice/zero axiom is the lift of `𝒜`'s. -/
def QuotAllegory.instDistributiveAllegory {𝒜 : Type u} [DistributiveAllegory 𝒜]
    (C : Congruence 𝒜)
    (hunion : ∀ {a b : 𝒜} {R S R' S' : a ⟶ b},
      C.rel R R' → C.rel S S' → C.rel (R ∪ S) (R' ∪ S')) :
    DistributiveAllegory (QuotAllegory 𝒜 C) :=
  { QuotAllegory.instAllegory C with
    zero := fun {a b} => Quotient.mk (congSetoid C) (@DistributiveAllegory.zero 𝒜 _ a b)
    union := fun {a b} => Quotient.lift₂
      (fun R S => Quotient.mk (congSetoid C) (R ∪ S))
      (fun _ _ _ _ hR hS => Quotient.sound (hunion hR hS))
    zero_comp := by
      intro a b c R
      refine Quotient.inductionOn R (fun r => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (@DistributiveAllegory.zero_comp 𝒜 _ a b c r)
    comp_zero := by
      intro a b c R
      refine Quotient.inductionOn R (fun r => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (@DistributiveAllegory.comp_zero 𝒜 _ a b c r)
    union_idem := by
      intro a b R
      refine Quotient.inductionOn R (fun r => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.union_idem r)
    union_comm := by
      intro a b R S
      refine Quotient.inductionOn₂ R S (fun r s => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.union_comm r s)
    union_assoc := by
      intro a b R S T
      refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.union_assoc r s t)
    union_inter_absorb := by
      intro a b R S
      refine Quotient.inductionOn₂ R S (fun r s => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.union_inter_absorb r s)
    inter_union_absorb := by
      intro a b R S
      refine Quotient.inductionOn₂ R S (fun r s => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.inter_union_absorb r s)
    comp_union_distrib := by
      intro a b c R S T
      refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.comp_union_distrib r s t)
    inter_union_distrib := by
      intro a b R S T
      refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.inter_union_distrib r s t)
    zero_union := by
      intro a b R
      refine Quotient.inductionOn R (fun r => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.zero_union r) }

/-- §2.52  `quotRep` preserves binary unions (it is a representation of
    distributive allegories), against the distributive structure of
    `QuotAllegory.instDistributiveAllegory`. -/
theorem quotRep_map_union {𝒜 : Type u} [DistributiveAllegory 𝒜] (C : Congruence 𝒜)
    (hunion : ∀ {a b : 𝒜} {R S R' S' : a ⟶ b},
      C.rel R R' → C.rel S S' → C.rel (R ∪ S) (R' ∪ S'))
    {a b : 𝒜} (R S : a ⟶ b) :
    letI := QuotAllegory.instDistributiveAllegory C hunion
    (quotRep C).map (R ∪ S) = (quotRep C).map R ∪ (quotRep C).map S := rfl

/-- §2.52  `quotRep` preserves zero. -/
theorem quotRep_map_zero {𝒜 : Type u} [DistributiveAllegory 𝒜] (C : Congruence 𝒜)
    (hunion : ∀ {a b : 𝒜} {R S R' S' : a ⟶ b},
      C.rel R R' → C.rel S S' → C.rel (R ∪ S) (R' ∪ S'))
    {a b : 𝒜} :
    letI := QuotAllegory.instDistributiveAllegory C hunion
    (quotRep C).map (𝟘 : a ⟶ b) = (𝟘 : (quotRep C).obj a ⟶ (quotRep C).obj b) := rfl

/-! ## Shared helpers (used across §2.51/§2.536/§2.537/§2.541/§2.55) -/

/-- `quotRep` is monotone: `R ⊑ S → [R] ⊑ [S]`.  (`⊑` is `R = R ∩ S`, and `quotRep`
    preserves `∩`.)  The single canonical version of this fact. -/
theorem quotRep_mono {𝒜 : Type u} [Allegory 𝒜] (C : Congruence 𝒜) {a b : 𝒜}
    {R S : a ⟶ b} (h : R ⊑ S) : (quotRep C).map R ⊑ (quotRep C).map S := by
  show (quotRep C).map R ∩ (quotRep C).map S = (quotRep C).map R
  rw [← (quotRep C).map_inter, inter_eq_left h]

/-- The largest-element operator is idempotent: `R⁺⁺ = R⁺` (the book's "largest
    idempotent").  The single canonical version of this fact. -/
theorem largest_idem {𝒜 : Type u} [DistributiveAllegory 𝒜] (amen : AmenableCongruence 𝒜)
    {a b : 𝒜} (R : a ⟶ b) : amen.largest (amen.largest R) = amen.largest R :=
  (amenable_largest_class_invariant amen (amen.largest_rel R)).symm

end Freyd.Alg
