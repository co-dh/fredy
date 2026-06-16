/-
  Freyd & Scedrov, *Categories and Allegories* §2.3  Division allegories.

  §2.31 DIVISION ALLEGORY — right division R/S
  §2.331 SYMMETRIC DIVISION R/ₛS
  §2.35  STRAIGHT morphism, simple part, domain of simplicity
-/

import Fredy.S1_1
import Fredy.S2_1
import Fredy.S2_2


universe v u

namespace Freyd.Alg

/-! ## §2.31  Division allegory

  A DIVISION ALLEGORY is a distributive allegory with a binary partial
  operation R/S (right division) defined when R□ = S□, characterized by:
  T ⊑ R/S  iff  TS ⊑ R.

  Equivalently: (R/S)S ⊑ R (semi-commutative triangle) and R/S is
  maximal among such morphisms. -/

/-- A DIVISION ALLEGORY (§2.31): distributive allegory with right division R/S,
    the right adjoint to composition (-) ≫ S. -/
class DivisionAllegory (𝒜 : Type u) extends DistributiveAllegory 𝒜 where
  /-- Right division R/S : □R → □S, defined when R□ = S□. -/
  div {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : a ⟶ b

  /-- The semi-commutative triangle: (R/S)S ⊑ R (§2.31). -/
  div_comp_le {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : (div R S ≫ S) ⊑ R

  /-- The adjointness: if TS ⊑ R then T ⊑ R/S (§2.31). -/
  le_div {a b c : 𝒜} (T : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) (h : T ≫ S ⊑ R) : T ⊑ div R S

/-! ### Notation -/

/-- Right division notation R / S -/
infixl:70 " / " => DivisionAllegory.div

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ### Derived properties of division -/

/-- The defining equivalence: T ⊑ R/S iff TS ⊑ R (§2.31). -/
theorem le_div_iff {a b c : 𝒜} (T : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) :
    T ⊑ R / S ↔ T ≫ S ⊑ R := by
  constructor
  · intro h
    -- T ⊑ R/S → TS ⊑ (R/S)S ⊑ R
    apply le_trans ?_ (DivisionAllegory.div_comp_le R S)
    exact comp_mono_right h S
  · exact DivisionAllegory.le_div T R S

/-- (R/S)S ⊑ R (§2.31). -/
theorem div_comp_eq_le {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : (R / S) ≫ S ⊑ R :=
  DivisionAllegory.div_comp_le R S

/-- (R ∩ R')/S ⊑ (R/S) ∩ (R'/S) (§2.31). -/
theorem div_inter_le {a b c : 𝒜} (R R' : a ⟶ c) (S : b ⟶ c) :
    (R ∩ R') / S ⊑ (R / S) ∩ (R' / S) := by
  apply le_inter
  · apply (le_div_iff _ _ _).mpr
    -- ((R ∩ R') / S) ≫ S ⊑ R ∩ R' ⊑ R
    apply le_trans (div_comp_eq_le _ _)
    exact inter_lb_left _ _
  · apply (le_div_iff _ _ _).mpr
    apply le_trans (div_comp_eq_le _ _)
    exact inter_lb_right _ _

/-- R/1 = R (§2.314). -/
theorem div_one {a b : 𝒜} (R : a ⟶ b) : R / Cat.id b = R := by
  apply le_antisymm
  · -- (R/1) ⊑ R: div_comp_eq_le gives (R/1)≫1 ⊑ R, and (R/1)≫1 = R/1
    have h := div_comp_eq_le R (Cat.id b)
    simpa [Cat.comp_id] using h
  · -- R ⊑ R/1: by le_div_iff, this is equivalent to R≫1 ⊑ R
    rw [le_div_iff]
    simpa [Cat.comp_id] using le_refl R

/-- 1 ⊑ R/R (§2.314). -/
theorem one_le_div_self {a b : 𝒜} (R : a ⟶ b) : Cat.id a ⊑ R / R := by
  apply (le_div_iff _ _ _).mpr
  rw [Cat.id_comp]
  exact le_refl _

/-- (R/R)R ⊑ R (§2.314). -/
theorem div_self_comp_le {a b : 𝒜} (R : a ⟶ b) : (R / R) ≫ R ⊑ R :=
  div_comp_eq_le R R

/-- (R/S)(S/T) ⊑ R/T (§2.314). -/
theorem div_comp {a b c d : 𝒜} (R : a ⟶ d) (S : b ⟶ d) (T : c ⟶ d) :
    (R / S) ≫ (S / T) ⊑ R / T := by
  apply (le_div_iff _ _ _).mpr
  apply le_trans ?_ (div_comp_eq_le R S)
  rw [Cat.assoc]
  exact comp_mono_left (R / S) (div_comp_eq_le S T)

/-- R/(S₁∪S₂) = (R/S₁) ∩ (R/S₂) (§2.314). -/
theorem div_union {a b c : 𝒜} (R : a ⟶ c) (S₁ S₂ : b ⟶ c) :
    R / (S₁ ∪ S₂) = (R / S₁) ∩ (R / S₂) := by
  apply le_antisymm
  · -- R/(S₁∪S₂) ⊑ R/S₁: by le_div_iff, (R/(S₁∪S₂))(S₁) ⊑ (R/(S₁∪S₂))(S₁∪S₂) ⊑ R
    apply le_inter
    · apply (le_div_iff _ _ _).mpr
      exact le_trans (comp_mono_left _ (le_union_left S₁ S₂)) (div_comp_eq_le R _)
    · apply (le_div_iff _ _ _).mpr
      exact le_trans (comp_mono_left _ (le_union_right S₁ S₂)) (div_comp_eq_le R _)
  · -- R/S₁ ∩ R/S₂ ⊑ R/(S₁∪S₂): need T(S₁∪S₂) ⊑ R whenever TS₁ ⊑ R and TS₂ ⊑ R
    apply (le_div_iff _ _ _).mpr
    rw [DistributiveAllegory.comp_union_distrib]
    exact union_lub
      (le_trans (comp_mono_right (inter_lb_left _ _) S₁) (div_comp_eq_le R S₁))
      (le_trans (comp_mono_right (inter_lb_right _ _) S₂) (div_comp_eq_le R S₂))

/-- R/(S₁≫S₂) = (R/S₂)/S₁ (§2.314). -/
theorem div_comp_assoc {a b c d : 𝒜} (R : a ⟶ d) (S₁ : b ⟶ c) (S₂ : c ⟶ d) :
    R / (S₁ ≫ S₂) = (R / S₂) / S₁ := by
  apply le_antisymm
  · -- R/(S₁S₂) ⊑ (R/S₂)/S₁: need ((R/(S₁S₂)) ≫ S₁) ≫ S₂ ⊑ R
    apply (le_div_iff _ _ _).mpr
    apply (le_div_iff _ _ _).mpr
    -- goal: ((R / (S₁ ≫ S₂)) ≫ S₁) ≫ S₂ ⊑ R
    -- ((R/(S₁S₂))S₁)S₂ = (R/(S₁S₂))(S₁S₂) ⊑ R
    have : ((R / (S₁ ≫ S₂)) ≫ S₁) ≫ S₂ = (R / (S₁ ≫ S₂)) ≫ (S₁ ≫ S₂) := by
      rw [Cat.assoc]
    rw [this]; exact div_comp_eq_le R (S₁ ≫ S₂)
  · -- (R/S₂)/S₁ ⊑ R/(S₁S₂): need ((R/S₂)/S₁)(S₁S₂) ⊑ R
    apply (le_div_iff _ _ _).mpr
    -- ((R/S₂)/S₁)(S₁S₂) = ((R/S₂)/S₁)S₁ · S₂ ⊑ (R/S₂) · S₂ ⊑ R
    have step1 : ((R / S₂) / S₁) ≫ (S₁ ≫ S₂) = (((R / S₂) / S₁) ≫ S₁) ≫ S₂ := by
      rw [Cat.assoc]
    rw [step1]
    exact le_trans (comp_mono_right (div_comp_eq_le (R / S₂) S₁) S₂) (div_comp_eq_le R S₂)

/-! ## §2.316  Heyting algebra structure on (a,a)

  For an object a in a division allegory, the hom-set (a,a) is a Heyting
  algebra.  Given A, B ∈ (a,a) the Heyting implication is defined as
  A ⊃ B := 1 ∩ B/A  (§2.316). -/

/-- Heyting implication in (a,a): A ⊃ B := 1 ∩ B/A (§2.316). -/
def heytingImpl {a : 𝒜} (A B : a ⟶ a) : a ⟶ a :=
  Cat.id a ∩ (B / A)

-- Note: the book's §2.316 Heyting algebra is on coreflexive morphisms (subidentities).
-- The general adjointness A ∩ C ⊑ B ↔ C ⊑ 1 ∩ B/A does NOT hold for arbitrary morphisms;
-- it requires A, C coreflexive (so A∩C = A≫C in the poset sense).
-- See heyting_adj_coref below for the correct statement.

/-- Heyting adjointness for coreflexive morphisms (§2.316):
    if A, B, C : a → a are coreflexive, then A ≫ C ⊑ B ↔ C ⊑ 1 ∩ B/A. -/
theorem heyting_adj_coref {a : 𝒜} {A B C : a ⟶ a}
    (hA : Coreflexive A) (hC : Coreflexive C) :
    A ≫ C ⊑ B ↔ C ⊑ heytingImpl A B := by
  -- Coreflexive morphisms commute: A≫C = A∩C = C∩A = C≫A
  have hac_comm : A ≫ C = C ≫ A :=
    (coreflexive_comp_eq_inter hA hC).trans
      ((Allegory.inter_comm A C).trans (coreflexive_comp_eq_inter hC hA).symm)
  dsimp [heytingImpl]
  constructor
  · intro h
    apply le_inter
    · exact hC
    · -- C ⊑ B/A: use le_div_iff, need C ≫ A ⊑ B
      apply (le_div_iff _ _ _).mpr
      rwa [← hac_comm]
  · intro h
    -- A ≫ C = C ≫ A ⊑ (B/A) ≫ A ⊑ B
    rw [hac_comm]
    exact le_trans (comp_mono_right (le_trans h (inter_lb_right _ _)) A) (div_comp_eq_le B A)

/-! ## §2.331  Symmetric division

  R/ₛS = (R/S) ∩ (S/R)° (§2.35).  Characterized by:
  T ⊑ R/ₛS  iff  TS ⊑ R and T°R ⊑ S. -/

/-- SYMMETRIC DIVISION: R/ₛS = (R/S) ∩ (S/R)° (§2.35, §2.331). -/
def symmDiv {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : a ⟶ b :=
  (R / S) ∩ ((S / R)°)

infixl:70 " /ₛ " => symmDiv

/-- Characterizing property of symmetric division (§2.35). -/
theorem le_symmDiv_iff {a b c : 𝒜} (T : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) :
    T ⊑ R /ₛ S ↔ T ≫ S ⊑ R ∧ T° ≫ R ⊑ S := by
  dsimp [symmDiv]
  constructor
  · intro h
    have h1 : T ⊑ R / S := le_trans h (inter_lb_left _ _)
    have h2 : T ⊑ (S / R)° := le_trans h (inter_lb_right _ _)
    constructor
    · exact ((le_div_iff _ _ _).mp h1)
    · -- T ⊑ (S/R)° → T° ⊑ S/R → T°R ⊑ S
      have h2' : T° ⊑ S / R := by
        -- T ⊑ (S/R)° → T° ⊑ (S/R)°° = S/R
        calc
          T° ⊑ ((S / R)°)° := recip_mono h2
          _ = S / R := by rw [Allegory.recip_recip]
      exact ((le_div_iff _ _ _).mp h2')
  · intro ⟨hTS, hTR⟩
    apply le_inter
    · exact ((le_div_iff _ _ _).mpr hTS)
    · -- T ⊑ (S/R)° ↔ T° ⊑ S/R
      have hTR_div : T° ⊑ S / R := (le_div_iff _ _ _).mpr hTR
      calc
        T = (T°)° := by rw [Allegory.recip_recip]
        _ ⊑ (S / R)° := recip_mono hTR_div

/-! ### Properties of symmetric division (§2.35) -/

/-- Symmetric division satisfies (R/ₛS)° = S/ₛR (§2.35). -/
theorem symmDiv_recip {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) :
    (R /ₛ S)° = S /ₛ R := by
  apply le_antisymm
  · -- (R/ₛS)° ⊑ S/ₛR.  R:a→c, S:b→c, R/ₛS:a→b, (R/ₛS)°:b→a, S/ₛR:b→a.
    -- le_symmDiv_iff: (R/ₛS)° ⊑ S/ₛR ↔ (R/ₛS)°≫R ⊑ S ∧ ((R/ₛS)°)°≫S ⊑ R.
    rw [le_symmDiv_iff]
    have h := (le_symmDiv_iff (R /ₛ S) R S).mp (le_refl _)
    exact ⟨h.2, by rw [Allegory.recip_recip]; exact h.1⟩
  · -- S/ₛR ⊑ (R/ₛS)°.  Equivalently (S/ₛR)° ⊑ R/ₛS (by recip_le_iff).
    rw [← recip_le_iff]
    apply (le_symmDiv_iff _ R S).mpr
    have h := (le_symmDiv_iff (S /ₛ R) S R).mp (le_refl _)
    -- goal: (S/ₛR)°≫S ⊑ R ∧ (S/ₛR)°°≫R ⊑ S
    -- h.2 : (S/ₛR)°≫S ⊑ R; h.1 : (S/ₛR)≫R ⊑ S, and (S/ₛR)°° = S/ₛR
    exact ⟨h.2, by rw [Allegory.recip_recip]; exact h.1⟩

/-- Symmetric division is transitive: (R/ₛS)(S/ₛT) ⊑ R/ₛT (§2.35). -/
theorem symmDiv_comp {a b c d : 𝒜} (R : a ⟶ d) (S : b ⟶ d) (T : c ⟶ d) :
    (R /ₛ S) ≫ (S /ₛ T) ⊑ R /ₛ T := by
  rw [le_symmDiv_iff]
  have hRS := (le_symmDiv_iff (R /ₛ S) R S).mp (le_refl _)
  have hST := (le_symmDiv_iff (S /ₛ T) S T).mp (le_refl _)
  constructor
  · -- ((R/ₛS)(S/ₛT)) ≫ T ⊑ R
    rw [Cat.assoc]
    exact le_trans (comp_mono_left _ hST.1) hRS.1
  · -- ((R/ₛS)(S/ₛT))° ≫ R ⊑ T
    -- = (S/ₛT)°(R/ₛS)° ≫ R ⊑ T
    rw [Allegory.recip_comp, Cat.assoc]
    -- (R/ₛS)° = S/ₛR, and (S/ₛT)° = T/ₛS
    have h_rs_rec : (R /ₛ S)° ≫ R ⊑ S := hRS.2
    exact le_trans (comp_mono_left _ h_rs_rec) hST.2

-- Note: "R/ₛS ⊑ R" is listed in the book as a containment (§2.35) but only for the
-- case where the objects match (S = 1), i.e. simplePart R ⊑ R. See simplePart_le.
-- For general S the containment R/ₛS ⊑ R does not hold (R and R/ₛS have different types
-- in general: R : a→c, R/ₛS : a→b; the book notation is in the endomorphism case only).

/-! ## §2.35  Straight morphism, simple part

  R is STRAIGHT if R/ₛR ⊑ 1 (§2.351).
  In a division allegory, for any R, R/(R/ₛR) is the simple part. -/

/-- R is STRAIGHT if R/ₛR ⊑ 1 (§2.351). -/
def Straight {a b : 𝒜} (R : a ⟶ b) : Prop := R /ₛ R ⊑ Cat.id a

/-- In a division allegory, (R/R)R = R (§2.314). -/
theorem div_self_comp {a b : 𝒜} (R : a ⟶ b) : (R / R) ≫ R = R := by
  apply le_antisymm (div_comp_eq_le R R)
  -- R ⊑ (R/R)R: since 1 ⊑ R/R, we have R = 1R ⊑ (R/R)R
  have h : R ⊑ (R / R) ≫ R := by
    calc
      R = (Cat.id a) ≫ R := by rw [Cat.id_comp]
      _ ⊑ (R / R) ≫ R := comp_mono_right (one_le_div_self R) R
  exact h

/-! ## §2.312  Left division

  S\R := (R°/S°)°, defined when codomain(S) = source(R).
  S : a ⟶ b, R : a ⟶ c gives S\R : b ⟶ c.
  Characterization: T ⊑ S\R iff ST ⊑ R. -/

/-- LEFT DIVISION: S\R := (R°/S°)° (§2.312).
    S : a ⟶ b, R : a ⟶ c, result S\R : b ⟶ c. -/
def leftDiv {a b c : 𝒜} (S : a ⟶ b) (R : a ⟶ c) : b ⟶ c :=
  (R° / S°)°

/-- The defining equivalence: T ⊑ S\R iff ST ⊑ R (§2.312). -/
theorem le_leftDiv_iff {a b c : 𝒜} (T : b ⟶ c) (S : a ⟶ b) (R : a ⟶ c) :
    T ⊑ leftDiv S R ↔ S ≫ T ⊑ R := by
  dsimp [leftDiv]
  -- T ⊑ (R°/S°)° ↔ T° ⊑ R°/S° ↔ T°S° ⊑ R° ↔ (ST)° ⊑ R° ↔ ST ⊑ R
  rw [← recip_le_iff, le_div_iff, ← Allegory.recip_comp, recip_le_iff,
      Allegory.recip_recip]

/-- The semi-commutative triangle for left division: S(S\R) ⊑ R (§2.312). -/
theorem leftDiv_comp_le {a b c : 𝒜} (S : a ⟶ b) (R : a ⟶ c) : S ≫ leftDiv S R ⊑ R :=
  (le_leftDiv_iff _ S R).mp (le_refl _)

/-! ## §2.314  The equation S\(R/T) = (S\R)/T -/

/-- S\(R/T) = (S\R)/T (§2.314).
    S : a ⟶ b, R : a ⟶ d, T : c ⟶ d.
    LHS: leftDiv S (R/T) where R/T : a ⟶ c, so leftDiv S (R/T) : b ⟶ c.
    RHS: (leftDiv S R) / T where leftDiv S R : b ⟶ d, T : c ⟶ d, so result : b ⟶ c. ✓
    -/
theorem leftDiv_div {a b c d : 𝒜} (S : a ⟶ b) (R : a ⟶ d) (T : c ⟶ d) :
    leftDiv S (R / T) = (leftDiv S R) / T := by
  apply le_antisymm
  · -- S\(R/T) ⊑ (S\R)/T: show S ≫ (leftDiv S (R/T) ≫ T) ⊑ R
    apply (le_div_iff _ _ _).mpr
    apply (le_leftDiv_iff _ S R).mpr
    have h1 : (S ≫ leftDiv S (R / T)) ≫ T ⊑ (R / T) ≫ T :=
      comp_mono_right (leftDiv_comp_le S (R / T)) T
    have h2 : (R / T) ≫ T ⊑ R := div_comp_eq_le R T
    rw [← Cat.assoc]; exact le_trans h1 h2
  · -- (S\R)/T ⊑ S\(R/T): show (S ≫ (S\R)/T) ≫ T ⊑ R
    apply (le_leftDiv_iff _ S _).mpr
    apply (le_div_iff _ _ _).mpr
    -- goal: (S ≫ (leftDiv S R)/T) ≫ T ⊑ R
    have step1 : ((leftDiv S R) / T) ≫ T ⊑ leftDiv S R := div_comp_eq_le (leftDiv S R) T
    have step2 : S ≫ (((leftDiv S R) / T) ≫ T) ⊑ S ≫ leftDiv S R :=
      comp_mono_left S step1
    have step3 : S ≫ leftDiv S R ⊑ R := leftDiv_comp_le S R
    have step4 : S ≫ (((leftDiv S R) / T) ≫ T) ⊑ R := le_trans step2 step3
    rwa [← Cat.assoc] at step4

/-! ## §2.351  R/ₛR is an equivalence relation

  The book's §2.351 states that R/ₛR is an equivalence relation. -/

/-- R/ₛR is symmetric (§2.351).
    (R/ₛR)° = ((R/R) ∩ (R/R)°)° = (R/R)° ∩ (R/R)°° = (R/R)° ∩ (R/R) = R/ₛR. -/
theorem symmDiv_self_symmetric {a b : 𝒜} (R : a ⟶ b) : Symmetric (R /ₛ R) := by
  -- R/ₛR = (R/R) ∩ (R/R)°. Show (R/ₛR)° ⊑ R/ₛR.
  -- (R/ₛR)° ⊑ R/ₛR = (R/R) ∩ (R/R)°. Check each component:
  -- (R/ₛR)° ⊑ R/R: (R/ₛR)° ⊑ ((R/R)°)° = R/R. ✓
  -- (R/ₛR)° ⊑ (R/R)°: (R/ₛR)° ⊑ ((R/R))° = (R/R)°... wait need (R/ₛR)° ⊑ (R/R)°.
  -- (R/ₛR) ⊑ R/R, so (R/ₛR)° ⊑ (R/R)°. ✓
  dsimp [Symmetric, le, symmDiv]
  -- goal: ((R/R) ∩ (R/R)°)° ∩ ((R/R) ∩ (R/R)°) = ((R/R) ∩ (R/R)°)°
  rw [Allegory.recip_inter, Allegory.recip_recip]
  -- goal: ((R/R)° ∩ (R/R)) ∩ ((R/R) ∩ (R/R)°) = (R/R)° ∩ (R/R)
  rw [show Allegory.inter (R / R) (Allegory.recip (R / R)) =
        Allegory.inter (Allegory.recip (R / R)) (R / R) from Allegory.inter_comm _ _]
  apply Allegory.inter_idem

/-- R/ₛR is reflexive: 1 ⊑ R/ₛR (§2.351). -/
theorem symmDiv_self_reflexive {a b : 𝒜} (R : a ⟶ b) : Reflexive (R /ₛ R) := by
  dsimp [Reflexive]
  rw [le_symmDiv_iff (Cat.id a) R R]
  exact ⟨by rw [Cat.id_comp]; exact le_refl R,
         by rw [recip_id, Cat.id_comp]; exact le_refl R⟩

/-- R/ₛR is transitive: (R/ₛR)(R/ₛR) ⊑ R/ₛR (§2.351). -/
theorem symmDiv_self_transitive {a b : 𝒜} (R : a ⟶ b) : Transitive (R /ₛ R) := by
  dsimp [Transitive]
  rw [le_symmDiv_iff ((R /ₛ R) ≫ (R /ₛ R)) R R]
  have h1 : (R /ₛ R) ≫ R ⊑ R := ((le_symmDiv_iff (R /ₛ R) R R).mp (le_refl _)).1
  have h_sym : (R /ₛ R)° ⊑ R /ₛ R := symmDiv_self_symmetric R
  constructor
  · -- ((R/ₛR)(R/ₛR)) ≫ R ⊑ R
    -- ((R/ₛR)(R/ₛR)) ≫ R = (R/ₛR) ≫ ((R/ₛR) ≫ R) by assoc; ⊑ (R/ₛR) ≫ R ⊑ R
    have : ((R /ₛ R) ≫ (R /ₛ R)) ≫ R = (R /ₛ R) ≫ (R /ₛ R) ≫ R := Cat.assoc _ _ _
    rw [this]
    exact le_trans (comp_mono_left (R /ₛ R) h1) h1
  · -- ((R/ₛR)(R/ₛR))° ≫ R ⊑ R: = (R/ₛR)°(R/ₛR)° ≫ R ⊑ ... ⊑ R
    rw [Allegory.recip_comp]
    have step1 : (R /ₛ R)° ≫ (R /ₛ R)° ≫ R ⊑ (R /ₛ R) ≫ (R /ₛ R)° ≫ R :=
      comp_mono_right h_sym ((R /ₛ R)° ≫ R)
    have step2 : (R /ₛ R) ≫ (R /ₛ R)° ≫ R ⊑ (R /ₛ R) ≫ (R /ₛ R) ≫ R :=
      comp_mono_left (R /ₛ R) (comp_mono_right h_sym R)
    have step3 : (R /ₛ R) ≫ (R /ₛ R) ≫ R = ((R /ₛ R) ≫ (R /ₛ R)) ≫ R := (Cat.assoc _ _ _).symm
    have step4 : ((R /ₛ R) ≫ (R /ₛ R)) ≫ R ⊑ R := by
      rw [Cat.assoc]; exact le_trans (comp_mono_left (R /ₛ R) h1) h1
    rw [Cat.assoc]
    exact le_trans step1 (le_trans step2 (step3 ▸ step4))

/-- R/ₛR is an EQUIVALENCE RELATION (§2.351). -/
theorem symmDiv_self_equiv {a b : 𝒜} (R : a ⟶ b) :
    Reflexive (R /ₛ R) ∧ Symmetric (R /ₛ R) ∧ Transitive (R /ₛ R) :=
  ⟨symmDiv_self_reflexive R, symmDiv_self_symmetric R, symmDiv_self_transitive R⟩

/-! ## §2.352  Left cancellation for straight morphisms -/

/-- Reflexive-domain factorization: R ⊑ (dom R) ≫ R (§2.122).
    From the modular law with R=1, S=R, T=R: R = (1≫R)∩R ⊑ (1 ∩ RR°)R = (dom R)R. -/
private theorem le_dom_comp {a b : 𝒜} (R : a ⟶ b) : R ⊑ dom R ≫ R := by
  have hm := modular_le (Cat.id a) R R
  rwa [Cat.id_comp, Allegory.inter_idem] at hm

/-- If S is straight, F and G are simple with same source, and FS = GS, then (dom F)G = (dom G)F (§2.352). -/
theorem straight_cancel_simple {a b c : 𝒜} {S : a ⟶ b} (hS : Straight S)
    {F G : c ⟶ a} (hF : Simple F) (hG : Simple G)
    (h : F ≫ S = G ≫ S) :
    dom F ≫ G = dom G ≫ F := by
  -- G°FS ⊑ G°GS ⊑ S and (G°F)°S = F°GS ⊑ F°FS ⊑ S, so G°F ⊑ S/ₛS ⊑ 1.
  have hGF1 : G° ≫ F ⊑ Cat.id a := by
    refine le_trans ?_ hS
    rw [le_symmDiv_iff (G° ≫ F) S S]
    refine ⟨?_, ?_⟩
    · have eq1 : (G° ≫ F) ≫ S = (G° ≫ G) ≫ S := by rw [Cat.assoc, h, ← Cat.assoc]
      rw [eq1]; exact le_trans (comp_mono_right hG S) (by rw [Cat.id_comp]; exact le_refl S)
    · have heq : (G° ≫ F)° = F° ≫ G := by rw [Allegory.recip_comp, Allegory.recip_recip]
      rw [heq]
      have eq2 : (F° ≫ G) ≫ S = (F° ≫ F) ≫ S := by rw [Cat.assoc, ← h, ← Cat.assoc]
      rw [eq2]; exact le_trans (comp_mono_right hF S) (by rw [Cat.id_comp]; exact le_refl S)
  have hFG1 : F° ≫ G ⊑ Cat.id a := by
    have key : (G° ≫ F)° = F° ≫ G := by rw [Allegory.recip_comp, Allegory.recip_recip]
    calc F° ≫ G = (G° ≫ F)° := key.symm
      _ ⊑ (Cat.id a)° := recip_mono hGF1
      _ = Cat.id a := recip_id
  -- dom F ⊑ F F° and dom G ⊑ G G° (coreflexive part of domain).
  have hdomF : dom F ⊑ F ≫ F° := inter_lb_right _ _
  have hdomG : dom G ⊑ G ≫ G° := inter_lb_right _ _
  -- dom F and dom G are coreflexive, hence commute under composition.
  have hcF := dom_coreflexive F
  have hcG := dom_coreflexive G
  have hcomm : dom F ≫ dom G = dom G ≫ dom F :=
    (coreflexive_comp_eq_inter hcF hcG).trans
      ((Allegory.inter_comm _ _).trans (coreflexive_comp_eq_inter hcG hcF).symm)
  -- Forward chain: (dom F)G ⊑ (dom F)(dom G)G ⊑ (dom G)(dom F)G ⊑ (dom G)F F°G ⊑ (dom G)F.
  apply le_antisymm
  · -- (dom F)G ⊑ (dom F)(dom G)G = (dom G)(dom F)G ⊑ (dom G)F F°G ⊑ (dom G)F.
    have s1 : dom F ≫ G ⊑ dom G ≫ (dom F ≫ G) := by
      have h1 : dom F ≫ G ⊑ dom F ≫ (dom G ≫ G) := comp_mono_left _ (le_dom_comp G)
      have h2 : dom F ≫ (dom G ≫ G) = dom G ≫ (dom F ≫ G) := by
        rw [← Cat.assoc, hcomm, Cat.assoc]
      rwa [h2] at h1
    have s2 : dom G ≫ (dom F ≫ G) ⊑ dom G ≫ F := by
      have h3 : dom F ≫ G ⊑ (F ≫ F°) ≫ G := comp_mono_right hdomF G
      have h4 : (F ≫ F°) ≫ G ⊑ F := by
        rw [Cat.assoc]; have := comp_mono_left F hFG1; rwa [Cat.comp_id] at this
      exact comp_mono_left _ (le_trans h3 h4)
    exact le_trans s1 s2
  · have s1 : dom G ≫ F ⊑ dom F ≫ (dom G ≫ F) := by
      have h1 : dom G ≫ F ⊑ dom G ≫ (dom F ≫ F) := comp_mono_left _ (le_dom_comp F)
      have h2 : dom G ≫ (dom F ≫ F) = dom F ≫ (dom G ≫ F) := by
        rw [← Cat.assoc, ← hcomm, Cat.assoc]
      rwa [h2] at h1
    have s2 : dom F ≫ (dom G ≫ F) ⊑ dom F ≫ G := by
      have h3 : dom G ≫ F ⊑ (G ≫ G°) ≫ F := comp_mono_right hdomG F
      have h4 : (G ≫ G°) ≫ F ⊑ G := by
        rw [Cat.assoc]; have := comp_mono_left G hGF1; rwa [Cat.comp_id] at this
      exact comp_mono_left _ (le_trans h3 h4)
    exact le_trans s1 s2

/-- Helper: from map f, 1 ⊑ f ≫ f° (entireness unfold). -/
private theorem map_entire_le {a b : 𝒜} {f : a ⟶ b} (hf : Map f) : Cat.id a ⊑ f ≫ f° := by
  have := hf.1
  dsimp [Entire, dom] at this
  exact this ▸ inter_lb_right _ _

/-- If S is straight and f, g are maps with fS = gS then f = g (§2.352). -/
theorem straight_cancel {a b c : 𝒜} {S : a ⟶ b} (hS : Straight S)
    {f g : c ⟶ a} (hf : Map f) (hg : Map g) (h : f ≫ S = g ≫ S) : f = g := by
  -- g°f ⊑ S/ₛS ⊑ 1. (g°f)S = g°(fS) = g°(gS) ⊑ (g°g)S ⊑ S; and ((g°f)°)S ⊑ S similarly.
  have hgf_ss : g° ≫ f ⊑ S /ₛ S := by
    rw [le_symmDiv_iff (g° ≫ f) S S]
    constructor
    · -- (g°f)S ⊑ S
      have eq1 : (g° ≫ f) ≫ S = (g° ≫ g) ≫ S := by rw [Cat.assoc, h, ← Cat.assoc]
      rw [eq1]; exact le_trans (comp_mono_right hg.2 S) (by rw [Cat.id_comp]; exact le_refl S)
    · -- (g°f)°S ⊑ S: (g°f)° = f°g°° = f°g
      have heq : (g° ≫ f)° = f° ≫ g := by rw [Allegory.recip_comp, Allegory.recip_recip]
      rw [heq]
      have eq2 : (f° ≫ g) ≫ S = (f° ≫ f) ≫ S := by rw [Cat.assoc, ← h, ← Cat.assoc]
      rw [eq2]; exact le_trans (comp_mono_right hf.2 S) (by rw [Cat.id_comp]; exact le_refl S)
  have hgf1 : g° ≫ f ⊑ Cat.id a := le_trans hgf_ss hS
  have hfg1 : f° ≫ g ⊑ Cat.id a := by
    have key : (g° ≫ f)° = f° ≫ g := by rw [Allegory.recip_comp, Allegory.recip_recip]
    calc f° ≫ g = (g° ≫ f)° := key.symm
        _ ⊑ (Cat.id a)° := recip_mono hgf1
        _ = Cat.id a := recip_id
  apply le_antisymm
  · -- f ⊑ g: 1f ⊑ (gg°)f = g(g°f) ⊑ g1 = g
    have h_id : f ⊑ Cat.id c ≫ f := by dsimp [le]; rw [Cat.id_comp]; exact Allegory.inter_idem f
    have h1 : f ⊑ (g ≫ g°) ≫ f := le_trans h_id (comp_mono_right (map_entire_le hg) f)
    have h2 : g ≫ g° ≫ f ⊑ g ≫ Cat.id a := comp_mono_left g hgf1
    exact Cat.comp_id g ▸ le_trans h1 ((Cat.assoc g g° f).symm ▸ h2)
  · -- g ⊑ f: 1g ⊑ (ff°)g = f(f°g) ⊑ f1 = f
    have h_id : g ⊑ Cat.id c ≫ g := by dsimp [le]; rw [Cat.id_comp]; exact Allegory.inter_idem g
    have h1 : g ⊑ (f ≫ f°) ≫ g := le_trans h_id (comp_mono_right (map_entire_le hf) g)
    have h2 : f ≫ f° ≫ g ⊑ f ≫ Cat.id a := comp_mono_left f hfg1
    exact Cat.comp_id f ▸ le_trans h1 ((Cat.assoc f f° g).symm ▸ h2)

/-! ## §2.353  Converse characterization of straightness -/

/-- Converse of straight_cancel (§2.353): if (FS = GS → (dom F)G = (dom G)F)
    for all simple F, G with the same source, then S is straight.

    FAITHFUL SORRY. The book's §2.353 proves this only for division allegories
    "in which every morphism is the union of the semisimple morphisms it contains"
    (§2.225). That hypothesis is what licenses the *reduction step*: to prove
    `S/ₛS ⊑ 1` it suffices to prove `F°G ⊑ 1` for every simple F, G with
    `F°G ⊑ S/ₛS`, because `S/ₛS` is then the union of such pieces. The reduction
    is not available from the bare `DivisionAllegory` interface here (it needs
    unions / local completeness — §2.225 itself is unformalized). The inner
    argument (set F' = (dom G)F, G' = (dom F)G; then F'S = G'S, so by `h`
    F' = G', whence F°G = F'°G' ⊑ 1) IS pure division-allegory algebra and is
    discharged in spirit by `straight_cancel_simple`; only the §2.225 reduction
    blocks a complete proof. See S2_3.md for the sharpened blocker. -/
theorem straight_of_cancel {a b : 𝒜} {S : a ⟶ b}
    (h : ∀ {c : 𝒜} (F G : c ⟶ a),
        Simple F → Simple G → F ≫ S = G ≫ S → dom F ≫ G = dom G ≫ F) :
    Straight S := by
  sorry

/-! ## §2.355  If SR is straight then S is straight -/

/-- If SR is straight then S is straight (§2.355).
    Proof: S/ₛS ⊑ (SR)/ₛ(SR) ⊑ 1. -/
theorem straight_of_comp_straight {a b c : 𝒜} {S : a ⟶ b} {R : b ⟶ c}
    (h : Straight (S ≫ R)) : Straight S := by
  apply le_trans _ h
  -- Show S/ₛS ⊑ (SR)/ₛ(SR): need (S/ₛS)(SR) ⊑ SR and (S/ₛS)°(SR) ⊑ SR.
  rw [le_symmDiv_iff (S /ₛ S) (S ≫ R) (S ≫ R)]
  have hss_le : (S /ₛ S) ≫ S ⊑ S := ((le_symmDiv_iff (S /ₛ S) S S).mp (le_refl _)).1
  constructor
  · -- (S/ₛS)(SR) = ((S/ₛS)S)R ⊑ SR
    rw [← Cat.assoc]; exact comp_mono_right hss_le R
  · -- (S/ₛS)°(SR) ⊑ SR: (S/ₛS)° ⊑ S/ₛS so (S/ₛS)°S ⊑ (S/ₛS)S ⊑ S
    have h_sym : (S /ₛ S)° ⊑ S /ₛ S := symmDiv_self_symmetric S
    have hss_sym_le : (S /ₛ S)° ≫ S ⊑ S := le_trans (comp_mono_right h_sym S) hss_le
    rw [← Cat.assoc]; exact comp_mono_right hss_sym_le R

/-- Right-invertible morphisms are straight (§2.355). -/
theorem rightInvertible_straight {a b : 𝒜} {S : a ⟶ b} {T : b ⟶ a}
    (h : S ≫ T = Cat.id a) : Straight S := by
  -- S(ST) = (SS)T? No. Use: ST = 1, so straight_of_comp_straight with R=T.
  -- Need Straight (S ≫ T). Since S ≫ T = Cat.id a and Cat.id a is straight, done.
  have h1_straight : Straight (S ≫ T) := by
    rw [h]
    -- Straight (Cat.id a): 1/ₛ1 = (1/1) ∩ (1/1)° = 1 ∩ 1° = 1 ∩ 1 ⊑ 1
    dsimp [Straight, le, symmDiv]
    rw [div_one, recip_id]
    simp [Allegory.inter_idem]
  exact straight_of_comp_straight h1_straight

/-! ## §2.356  If S is straight then R/ₛS is simple -/

/-- If S is straight then R/ₛS is simple (§2.356).
    Proof: (R/ₛS)°(R/ₛS) ⊑ S/ₛS ⊑ 1. -/
theorem straight_symmDiv_simple {a b c : 𝒜} {S : b ⟶ c} (hS : Straight S)
    (R : a ⟶ c) : Simple (R /ₛ S) := by
  dsimp [Simple]
  apply le_trans _ hS
  rw [le_symmDiv_iff]
  -- Let T := (R/ₛS)°(R/ₛS). T° = T (symmetric). TS ⊑ S.
  -- (R/ₛS)S ⊑ R and (R/ₛS)°R ⊑ S, from le_symmDiv for T = R/ₛS.
  have hRS_le : (R /ₛ S) ≫ S ⊑ R := ((le_symmDiv_iff _ _ _).mp (le_refl _)).1
  have hRS_rec : (R /ₛ S)° ≫ R ⊑ S := ((le_symmDiv_iff _ _ _).mp (le_refl _)).2
  constructor
  · -- ((R/ₛS)°(R/ₛS))S ⊑ (R/ₛS)°R ⊑ S
    rw [Cat.assoc]; exact le_trans (comp_mono_left _ hRS_le) hRS_rec
  · -- ((R/ₛS)°(R/ₛS))° ≫ S ⊑ S.
    -- T := (R/ₛS)°(R/ₛS). T° = (R/ₛS)°(R/ₛS)°° = (R/ₛS)°(R/ₛS) = T.
    -- So T° ≫ S = T ≫ S ⊑ S (same as first bullet).
    -- In Lean, ((R/ₛS)° ≫ R/ₛS)° = (R/ₛS)° ≫ (R/ₛS)°° = (R/ₛS)° ≫ R/ₛS.
    -- After rw [recip_comp, recip_recip], goal: (R/ₛS)° ≫ (R/ₛS) ≫ S ⊑ S.
    -- That IS the first bullet (same expression, just associativity).
    rw [Allegory.recip_comp, Allegory.recip_recip]
    -- goal: ((R/ₛS)° ≫ R/ₛS) ≫ S ⊑ S (same as first bullet after assoc)
    exact le_trans (Cat.assoc (R /ₛ S)° (R /ₛ S) S ▸ comp_mono_left _ hRS_le) hRS_rec

/-! ## §2.357  Simple part and domain of simplicity -/

/-- The SIMPLE PART of R: R/ₛ1 (§2.357).
    T ⊑ R/ₛ1 iff T ⊑ R and T°R ⊑ 1 (simplicity of T, contained in R). -/
def simplePart {a b : 𝒜} (R : a ⟶ b) : a ⟶ b := R /ₛ Cat.id b

/-- The DOMAIN OF SIMPLICITY of R: dom(R/ₛ1) (§2.357). -/
def domSimplicity {a b : 𝒜} (R : a ⟶ b) : a ⟶ a := dom (simplePart R)

/-- The simple part is simple (§2.357).
    1_b is straight (right-invertible), so R/ₛ1 is simple by §2.356. -/
theorem simplePart_simple {a b : 𝒜} (R : a ⟶ b) : Simple (simplePart R) := by
  apply straight_symmDiv_simple
  exact rightInvertible_straight (Cat.comp_id (Cat.id b))

/-- The simple part is contained in R: R/ₛ1 ⊑ R (§2.357). -/
theorem simplePart_le {a b : 𝒜} (R : a ⟶ b) : simplePart R ⊑ R := by
  dsimp [simplePart, symmDiv]
  calc (R / Cat.id b) ∩ ((Cat.id b / R)°) ⊑ R / Cat.id b := inter_lb_left _ _
      _ = R := div_one R

/-- R/ₛ1 is the largest simple AR with A coreflexive (§2.357).
    Here the "simple" condition on AR is expressed directly as the
    symmDiv characterization: AR ⊑ R and (AR)°R ⊑ 1.
    (The book's proof of the equivalence with Simple uses A°A = A for coreflexive A.) -/
theorem simplePart_largest {a b : 𝒜} (R : a ⟶ b) (A : a ⟶ a)
    (hA : Coreflexive A) (hAR : (A ≫ R)° ≫ R ⊑ Cat.id b) :
    A ≫ R ⊑ simplePart R := by
  dsimp [simplePart]
  rw [le_symmDiv_iff (A ≫ R) R (Cat.id b)]
  constructor
  · -- (AR) ≫ 1 ⊑ R: AR ⊑ R since A ⊑ 1
    rw [Cat.comp_id]
    exact le_trans (comp_mono_right hA R) (by rw [Cat.id_comp]; exact le_refl R)
  · exact hAR

end Freyd.Alg
