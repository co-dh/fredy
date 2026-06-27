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

/-- (R ∩ R')/S = (R/S) ∩ (R'/S) (§2.31, full equality).

    Book §2.31: "The first containment may be replaced with an equality:
    (R₁/S ∩ R₂/S) ⊑ (R₁∩R₂)/S because (R₁/S ∩ R₂/S)S ⊑ (R₁/S)S ∩ (R₂/S)S ⊑ (R₁∩R₂)." -/
theorem div_inter_eq {a b c : 𝒜} (R R' : a ⟶ c) (S : b ⟶ c) :
    (R ∩ R') / S = (R / S) ∩ (R' / S) := by
  apply le_antisymm
  · -- ⊑ : (R∩R')/S ⊑ R/S and ⊑ R'/S
    apply le_inter
    · apply (le_div_iff _ _ _).mpr
      -- ((R ∩ R') / S) ≫ S ⊑ R ∩ R' ⊑ R
      apply le_trans (DivisionAllegory.div_comp_le _ _)
      exact inter_lb_left _ _
    · apply (le_div_iff _ _ _).mpr
      apply le_trans (DivisionAllegory.div_comp_le _ _)
      exact inter_lb_right _ _
  · -- ⊒ : (R/S ∩ R'/S) ⊑ (R∩R')/S, since (R/S ∩ R'/S)S ⊑ (R/S)S ∩ (R'/S)S ⊑ R∩R'
    apply (le_div_iff _ _ _).mpr
    apply le_inter
    · exact le_trans (comp_mono_right (inter_lb_left _ _) S) (DivisionAllegory.div_comp_le R S)
    · exact le_trans (comp_mono_right (inter_lb_right _ _) S) (DivisionAllegory.div_comp_le R' S)

/-- (R ∩ R')/S ⊑ (R/S) ∩ (R'/S) (§2.31, the ⊑ direction of `div_inter_eq`). -/
theorem div_inter_le {a b c : 𝒜} (R R' : a ⟶ c) (S : b ⟶ c) :
    (R ∩ R') / S ⊑ (R / S) ∩ (R' / S) := by
  rw [div_inter_eq]; exact le_refl _

/-- R/1 = R (§2.314). -/
theorem div_one {a b : 𝒜} (R : a ⟶ b) : R / Cat.id b = R := by
  apply le_antisymm
  · -- (R/1) ⊑ R: DivisionAllegory.div_comp_le gives (R/1)≫1 ⊑ R, and (R/1)≫1 = R/1
    have h := DivisionAllegory.div_comp_le R (Cat.id b)
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
  DivisionAllegory.div_comp_le R R

/-- (R/S)(S/T) ⊑ R/T (§2.314). -/
theorem div_comp {a b c d : 𝒜} (R : a ⟶ d) (S : b ⟶ d) (T : c ⟶ d) :
    (R / S) ≫ (S / T) ⊑ R / T := by
  apply (le_div_iff _ _ _).mpr
  apply le_trans ?_ (DivisionAllegory.div_comp_le R S)
  rw [Cat.assoc]
  exact comp_mono_left (R / S) (DivisionAllegory.div_comp_le S T)

/-- R/(S₁∪S₂) = (R/S₁) ∩ (R/S₂) (§2.314). -/
theorem div_union {a b c : 𝒜} (R : a ⟶ c) (S₁ S₂ : b ⟶ c) :
    R / (S₁ ∪ S₂) = (R / S₁) ∩ (R / S₂) := by
  apply le_antisymm
  · -- R/(S₁∪S₂) ⊑ R/S₁: by le_div_iff, (R/(S₁∪S₂))(S₁) ⊑ (R/(S₁∪S₂))(S₁∪S₂) ⊑ R
    apply le_inter
    · apply (le_div_iff _ _ _).mpr
      exact le_trans (comp_mono_left _ (le_union_left S₁ S₂)) (DivisionAllegory.div_comp_le R _)
    · apply (le_div_iff _ _ _).mpr
      exact le_trans (comp_mono_left _ (le_union_right S₁ S₂)) (DivisionAllegory.div_comp_le R _)
  · -- R/S₁ ∩ R/S₂ ⊑ R/(S₁∪S₂): need T(S₁∪S₂) ⊑ R whenever TS₁ ⊑ R and TS₂ ⊑ R
    apply (le_div_iff _ _ _).mpr
    rw [DistributiveAllegory.comp_union_distrib]
    exact union_lub
      (le_trans (comp_mono_right (inter_lb_left _ _) S₁) (DivisionAllegory.div_comp_le R S₁))
      (le_trans (comp_mono_right (inter_lb_right _ _) S₂) (DivisionAllegory.div_comp_le R S₂))

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
    rw [this]; exact DivisionAllegory.div_comp_le R (S₁ ≫ S₂)
  · -- (R/S₂)/S₁ ⊑ R/(S₁S₂): need ((R/S₂)/S₁)(S₁S₂) ⊑ R
    apply (le_div_iff _ _ _).mpr
    -- ((R/S₂)/S₁)(S₁S₂) = ((R/S₂)/S₁)S₁ · S₂ ⊑ (R/S₂) · S₂ ⊑ R
    have step1 : ((R / S₂) / S₁) ≫ (S₁ ≫ S₂) = (((R / S₂) / S₁) ≫ S₁) ≫ S₂ := by
      rw [Cat.assoc]
    rw [step1]
    exact le_trans (comp_mono_right (DivisionAllegory.div_comp_le (R / S₂) S₁) S₂) (DivisionAllegory.div_comp_le R S₂)

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
    exact le_trans (comp_mono_right (le_trans h (inter_lb_right _ _)) A) (DivisionAllegory.div_comp_le B A)

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
  apply le_antisymm (DivisionAllegory.div_comp_le R R)
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
    have h2 : (R / T) ≫ T ⊑ R := DivisionAllegory.div_comp_le R T
    rw [← Cat.assoc]; exact le_trans h1 h2
  · -- (S\R)/T ⊑ S\(R/T): show (S ≫ (S\R)/T) ≫ T ⊑ R
    apply (le_leftDiv_iff _ S _).mpr
    apply (le_div_iff _ _ _).mpr
    -- goal: (S ≫ (leftDiv S R)/T) ≫ T ⊑ R
    have step1 : ((leftDiv S R) / T) ≫ T ⊑ leftDiv S R := DivisionAllegory.div_comp_le (leftDiv S R) T
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

/-! ### Domain algebra used by §2.353

  The §2.353 construction sets F' = (dom G)F, G' = (dom F)G for simple F, G with
  the same source and target.  The four lemmas below are the pure
  division-allegory facts the book uses silently:
  `dom F' = dom G'`, `F'°G' = F°G`, `Simple F'`, and `dom R ≫ R = R`. -/

/-- `dom R ≫ R = R` (the domain restricts nothing): one half is `dom R ⊑ 1`,
    the other is `le_dom_comp`. -/
theorem dom_comp_self {a b : 𝒜} (R : a ⟶ b) : dom R ≫ R = R :=
  le_antisymm (le_trans (comp_mono_right (dom_coreflexive R) R)
    (by rw [Cat.id_comp]; exact le_refl R)) (le_dom_comp R)

/-- `Simple (E ≫ F)` when `E` is coreflexive and `F` simple
    (E°E ⊑ 1 so (EF)°(EF) = F°(E°E)F ⊑ F°F ⊑ 1). -/
theorem simple_coref_comp {a c : 𝒜} {E : c ⟶ c} {F : c ⟶ a}
    (hE : Coreflexive E) (hF : Simple F) : Simple (E ≫ F) := by
  dsimp [Simple]
  have hErec : E° ⊑ Cat.id c := by have := recip_mono hE; rwa [recip_id] at this
  have hEE : E° ≫ E ⊑ Cat.id c := by
    have h1 := comp_mono_right hErec E
    rw [Cat.id_comp] at h1
    exact le_trans h1 hE
  have hstep : (E ≫ F)° ≫ (E ≫ F) ⊑ F° ≫ F := by
    have e1 : (E ≫ F)° ≫ (E ≫ F) = F° ≫ ((E° ≫ E) ≫ F) := by
      rw [Allegory.recip_comp, Cat.assoc, ← Cat.assoc E° E F]
    rw [e1]
    calc F° ≫ ((E° ≫ E) ≫ F)
        ⊑ F° ≫ (Cat.id c ≫ F) := comp_mono_left F° (comp_mono_right hEE F)
      _ = F° ≫ F := by rw [Cat.id_comp]
  exact le_trans hstep hF

/-- dom is symmetric: (dom R)° = dom R. -/
theorem dom_recip {a b : 𝒜} (R : a ⟶ b) : (dom R)° = dom R :=
  symmetric_eq (coreflexive_symmetric_idempotent (dom_coreflexive R)).1

/-- `R° ≫ dom R = R°` (recip of `dom_comp_self`). -/
theorem recip_comp_dom {a b : 𝒜} (R : a ⟶ b) : R° ≫ dom R = R° := by
  have := congrArg (·°) (dom_comp_self R)
  simpa [Allegory.recip_comp, dom_recip] using this

/-- Domains commute: dom F ≫ dom G = dom G ≫ dom F. -/
theorem dom_comm {a b₁ b₂ : 𝒜} (F : a ⟶ b₁) (G : a ⟶ b₂) :
    dom F ≫ dom G = dom G ≫ dom F :=
  (coreflexive_comp_eq_inter (dom_coreflexive F) (dom_coreflexive G)).trans
    ((Allegory.inter_comm _ _).trans
      (coreflexive_comp_eq_inter (dom_coreflexive G) (dom_coreflexive F)).symm)

/-- Coreflexive sandwich: for coreflexive `E`, `1 ∩ (E ≫ X ≫ E°) = E ∩ X`. -/
theorem coref_sandwich {c : 𝒜} (E : c ⟶ c) (X : c ⟶ c) (hE : Coreflexive E) :
    Cat.id c ∩ (E ≫ X ≫ E°) = E ∩ X := by
  have hEsym : E° = E := symmetric_eq (coreflexive_symmetric_idempotent hE).1
  have hEidem : E ≫ E = E := (coreflexive_symmetric_idempotent hE).2
  apply le_antisymm
  · apply le_inter
    · -- ⊑ E : modular on (E≫X) ≫ E°  ⟹  ((E≫X) ∩ E) ≫ E° ⊑ E≫E° = E
      have hm := modular_le (E ≫ X) E° (Cat.id c)
      have heq : Cat.id c ∩ (E ≫ X ≫ E°) = (E ≫ X) ≫ E° ∩ Cat.id c := by
        rw [Allegory.inter_comm, ← Cat.assoc]
      rw [heq]
      refine le_trans hm ?_
      have hEE' : E ≫ E° = E := by rw [hEsym, hEidem]
      have hfac : (E ≫ X ∩ Cat.id c ≫ E°°) ⊑ E := by
        refine le_trans (inter_lb_right _ _) ?_
        rw [Cat.id_comp, Allegory.recip_recip]; exact le_refl E
      exact le_trans (comp_mono_right hfac E°) (by rw [hEE']; exact le_refl E)
    · -- ⊑ X : E X E° ⊑ 1·X·1 = X
      refine le_trans (inter_lb_right _ _) ?_
      calc E ≫ X ≫ E°
          ⊑ Cat.id c ≫ X ≫ Cat.id c := by
            refine le_trans (comp_mono_right hE _) ?_
            exact comp_mono_left _ (comp_mono_left X (by rw [hEsym]; exact hE))
        _ = X := by rw [Cat.id_comp, Cat.comp_id]
  · apply le_inter
    · exact le_trans (inter_lb_left _ _) hE
    · -- E ∩ X ⊑ E X E°: C := E∩X coreflexive, C = C C C ⊑ E X E°
      have hC : Coreflexive (E ∩ X) := le_trans (inter_lb_left _ _) hE
      have hCidem : (E ∩ X) ≫ (E ∩ X) = E ∩ X := (coreflexive_symmetric_idempotent hC).2
      calc E ∩ X
          = (E ∩ X) ≫ (E ∩ X) ≫ (E ∩ X) := by rw [hCidem, hCidem]
        _ ⊑ E ≫ X ≫ E° := by
            refine le_trans (comp_mono_right (inter_lb_left _ _) _) ?_
            refine comp_mono_left E ?_
            refine le_trans (comp_mono_right (inter_lb_right _ _) _) ?_
            refine comp_mono_left X ?_
            rw [hEsym]; exact inter_lb_left _ _

/-- `dom (E ≫ F) = E ∩ dom F` for coreflexive `E` (instance of `coref_sandwich`). -/
theorem dom_coref_comp {a c : 𝒜} (E : c ⟶ c) (F : c ⟶ a) (hE : Coreflexive E) :
    dom (E ≫ F) = E ∩ dom F := by
  have hEsym : E° = E := symmetric_eq (coreflexive_symmetric_idempotent hE).1
  -- RHS: E ∩ dom F = E ∩ (F ≫ F°), since E ⊑ 1
  have hrhs : E ∩ dom F = E ∩ (F ≫ F°) := by
    have hE1 : E ∩ Cat.id c = E := le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hE)
    dsimp [dom]; rw [Allegory.inter_assoc, hE1]
  rw [hrhs]
  -- LHS: dom(E≫F) = 1 ∩ E≫(F≫F°)≫E°
  dsimp [dom]
  have lhs_eq : (E ≫ F) ≫ (E ≫ F)° = E ≫ (F ≫ F°) ≫ E° := by
    rw [Allegory.recip_comp, Cat.assoc, ← Cat.assoc F F° E°]
  rw [lhs_eq]
  exact coref_sandwich E (F ≫ F°) hE

/-- §2.225 property (faithful to Freyd §2.16(10): "R is SEMI-SIMPLE if there
    exist simple F, G such that R = F°G").  A morphism `R` is the UNION of the
    semisimple morphisms it contains, encoded by its universal property: any `X`
    (parallel to `R`) dominating every book-semisimple piece `F° ≫ G` (F, G
    simple) contained in `R` also dominates `R`.  (`R` is the least upper bound
    of its semisimple parts.)

    Freyd states §2.353 only "for division allegories in which every morphism is
    the union of the semisimple morphisms it contains [2.225]"; this is the
    exact hypothesis, taken as a parameter because arbitrary unions / local
    completeness are not part of the bare `DivisionAllegory` interface.

    NOTE: the §2.16(10) book definition of semisimple is `F°G` (F, G simple),
    which is what the §2.353 reduction quantifies over; we use that form here
    directly. -/
def UnionOfSemiSimple {a : 𝒜} (R : a ⟶ a) : Prop :=
  ∀ X : a ⟶ a,
    (∀ {c : 𝒜} (F G : c ⟶ a), Simple F → Simple G → F° ≫ G ⊑ R → F° ≫ G ⊑ X) →
    R ⊑ X

/-- Converse of `straight_cancel` (§2.353).  Given the §2.225 hypothesis that
    `S /ₛ S` is the union of the (book-)semisimple morphisms it contains, and
    that `FS = GS → (dom F)G = (dom G)F` for all simple F, G of the same source
    and target, then `S` is straight.

    Proof (Freyd §2.353).  By §2.225 it suffices to show `F°G ⊑ 1` for all
    simple F, G with `F°G ⊑ S/ₛS`.  Set `F' = (dom G)F`, `G' = (dom F)G`.  Then
    `dom F' = dom G'` (`dom_coref_comp` + `dom_comm`), `F'°G' = F°G`, and
    `F'S = G'S` (using `F°G ⊑ S/ₛS`).  The hypothesis `h` gives
    `(dom F')G' = (dom G')F'`; with `dom F' = dom G'` this forces `F' = G'`,
    whence `F°G = F'°G' = F'°F' ⊑ 1` by simplicity of `F'`. -/
theorem straight_of_cancel {a b : 𝒜} {S : a ⟶ b}
    (hUnion : UnionOfSemiSimple (S /ₛ S))
    (h : ∀ {c : 𝒜} (F G : c ⟶ a),
        Simple F → Simple G → F ≫ S = G ≫ S → dom F ≫ G = dom G ≫ F) :
    Straight S := by
  -- §2.225 reduction: suffices F°G ⊑ 1 for all simple F, G with F°G ⊑ S/ₛS.
  refine hUnion (Cat.id a) ?_
  intro c F G hF hG hFGle
  -- F' = (dom G) F, G' = (dom F) G.  Both simple.
  -- (no `set`/`let`: this file is mathlib-free; use explicit abbreviations.)
  obtain ⟨F', hF'⟩ : ∃ F', F' = dom G ≫ F := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ G', G' = dom F ≫ G := ⟨_, rfl⟩
  have hF'simple : Simple F' := hF' ▸ simple_coref_comp (dom_coreflexive G) hF
  have hG'simple : Simple G' := hG' ▸ simple_coref_comp (dom_coreflexive F) hG
  -- dom F' = dom G' = dom F ∩ dom G.
  have hdomF' : dom F' = dom G ∩ dom F := by rw [hF', dom_coref_comp _ _ (dom_coreflexive G)]
  have hdomG' : dom G' = dom F ∩ dom G := by rw [hG', dom_coref_comp _ _ (dom_coreflexive F)]
  have hdomEq : dom F' = dom G' := by rw [hdomF', hdomG', Allegory.inter_comm]
  -- F'°G' = F°G.
  have hF'G' : F'° ≫ G' = F° ≫ G := by
    rw [hF', hG', Allegory.recip_comp, dom_recip]
    calc (F° ≫ dom G) ≫ (dom F ≫ G)
        = F° ≫ (dom G ≫ dom F) ≫ G := by
          rw [Cat.assoc, Cat.assoc, ← Cat.assoc (dom G) (dom F) G]
      _ = F° ≫ (dom F ≫ dom G) ≫ G := by rw [dom_comm]
      _ = (F° ≫ dom F) ≫ (dom G ≫ G) := by
          rw [Cat.assoc, Cat.assoc, ← Cat.assoc (dom F) (dom G) G]
      _ = F° ≫ G := by rw [recip_comp_dom, dom_comp_self]
  -- F'S = G'S, using F°G ⊑ S/ₛS.
  -- (S/ₛS)S ⊑ S.
  have hssS : (S /ₛ S) ≫ S ⊑ S := ((le_symmDiv_iff (S /ₛ S) S S).mp (le_refl _)).1
  -- F'°G' ⊑ S/ₛS and G'°F' ⊑ S/ₛS (the latter by symmetry of S/ₛS).
  have hF'G'le : F'° ≫ G' ⊑ S /ₛ S := by rw [hF'G']; exact hFGle
  have hG'F'le : G'° ≫ F' ⊑ S /ₛ S := by
    have hsym : (S /ₛ S)° ⊑ S /ₛ S := symmDiv_self_symmetric (S)
    have : (F'° ≫ G')° ⊑ (S /ₛ S)° := recip_mono hF'G'le
    rw [Allegory.recip_comp, Allegory.recip_recip] at this
    exact le_trans this hsym
  -- domain restriction: G' = dom F' ≫ G' ⊑ (F' ≫ F'°) ≫ G'.
  have hdomle : dom F' ⊑ F' ≫ F'° := inter_lb_right _ _
  have hG'restrict : G' ⊑ (F' ≫ F'°) ≫ G' :=
    calc G' = dom F' ≫ G' := by rw [hdomEq, dom_comp_self]
      _ ⊑ (F' ≫ F'°) ≫ G' := comp_mono_right hdomle G'
  have hF'restrict : F' ⊑ (G' ≫ G'°) ≫ F' :=
    calc F' = dom G' ≫ F' := by rw [← hdomEq, dom_comp_self]
      _ ⊑ (G' ≫ G'°) ≫ F' := comp_mono_right (inter_lb_right _ _) F'
  have hF'S : F' ≫ S = G' ≫ S := by
    apply le_antisymm
    · -- F'S ⊑ G'S : F'S ⊑ (G'G'°)F'S = G'(G'°F')S ⊑ G'(S/ₛS)S ⊑ G'S
      have c1 : F' ≫ S ⊑ ((G' ≫ G'°) ≫ F') ≫ S := comp_mono_right hF'restrict S
      have c2 : ((G' ≫ G'°) ≫ F') ≫ S = G' ≫ ((G'° ≫ F') ≫ S) := by
        rw [Cat.assoc, Cat.assoc, ← Cat.assoc G'° F' S]
      have c3 : G' ≫ ((G'° ≫ F') ≫ S) ⊑ G' ≫ ((S /ₛ S) ≫ S) :=
        comp_mono_left G' (comp_mono_right hG'F'le S)
      have c4 : G' ≫ ((S /ₛ S) ≫ S) ⊑ G' ≫ S := comp_mono_left G' hssS
      exact le_trans c1 (by rw [c2]; exact le_trans c3 c4)
    · -- G'S ⊑ F'S : symmetric
      have c1 : G' ≫ S ⊑ ((F' ≫ F'°) ≫ G') ≫ S := comp_mono_right hG'restrict S
      have c2 : ((F' ≫ F'°) ≫ G') ≫ S = F' ≫ ((F'° ≫ G') ≫ S) := by
        rw [Cat.assoc, Cat.assoc, ← Cat.assoc F'° G' S]
      have c3 : F' ≫ ((F'° ≫ G') ≫ S) ⊑ F' ≫ ((S /ₛ S) ≫ S) :=
        comp_mono_left F' (comp_mono_right hF'G'le S)
      have c4 : F' ≫ ((S /ₛ S) ≫ S) ⊑ F' ≫ S := comp_mono_left F' hssS
      exact le_trans c1 (by rw [c2]; exact le_trans c3 c4)
  -- By h: dom F' ≫ G' = dom G' ≫ F'.  With dom F' = dom G', get F' = G'.
  have hcancel := h F' G' hF'simple hG'simple hF'S
  have hFG'eq : F' = G' := by
    have e1 : F' = dom F' ≫ F' := (dom_comp_self F').symm
    have e2 : G' = dom G' ≫ G' := (dom_comp_self G').symm
    calc F' = dom F' ≫ F' := e1
      _ = dom G' ≫ F' := by rw [hdomEq]
      _ = dom F' ≫ G' := by rw [← hcancel, hdomEq]
      _ = dom G' ≫ G' := by rw [hdomEq]
      _ = G' := e2.symm
  -- F°G = F'°G' = F'°F' ⊑ 1 (F' simple).
  calc F° ≫ G = F'° ≫ G' := hF'G'.symm
    _ = F'° ≫ F' := by rw [hFG'eq]
    _ ⊑ Cat.id a := hF'simple

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

/-! ## §2.315  Division allegory → locally complete distributive allegory

  Any division allegory is faithfully representable in a locally complete
  distributive allegory, and thus in a globally complete allegory.

  (Proof sketch: R/S is constructible as ⊔{T | TS ⊑ R} in the local completion;
  the local-completion embedding A → Â is faithful; and a globally complete
  allegory subsumes locally complete.) -/

-- BOOK §2.315: Any division allegory is faithfully representable in a locally complete
-- distributive allegory, and thus in a globally complete allegory.
-- STATUS: OPEN.
-- AVAILABLE: the faithful embedding A → Â (R ↦ ↓R via `principalDowndeal`) exists in
--   S2_2.lean; `IsDowndeal` and `principalIdeal_isIdeal` (closure under union) are defined.
-- MISSING: a `Cat`+`Allegory`+`DivisionAllegory` instance on the downdeal completion Â.
--   Specifically: (1) Â-composition `(D₁ ≫ D₂) := ↓{T | ∃ R ∈ D₁, S ∈ D₂, T ⊑ R≫S}` and
--   (2) division `D₁/D₂ := ↓{T | T≫D₂ ⊑ D₁}` on downdeals, plus verification of the six
--   `DivisionAllegory` class fields.  None of these structures exist in the repo.

/-! ## §2.32  Tabular unitary division allegory ↔ Mσn(A) is a logos

  The MAP CATEGORY Mσn(A) of a tabular unitary allegory A has:
  - objects = objects of A
  - morphisms = maps (entire + simple morphisms) of A
  The book's §2.32 states: A is a tabular unitary division allegory iff Mσn(A)
  is a logos.

  (One direction was shown in §1.784: Rel(C) is a division allegory when C is a
  logos.  The other direction: construct the right adjoint to f# using f\(-)/f°.) -/

/-- **§2.32 lower-function form.** For a map `f : a → b` and a coreflexive `c` on `b`, the
    book's "domain of `fB`" lower function is `dom (f ≫ c) = 1 ∩ f c f°` (using `c° = c`,
    `c ≫ c = c`).  This is the coreflexive on `a` that `corOf_invImage` (MapCat) computes for the
    inverse image `f#` once the subobject `B` of `b` is read as the coreflexive `c = corOf B`. -/
theorem dom_comp_coref {a b : 𝒜} (f : a ⟶ b) {c : b ⟶ b} (hc : Coreflexive c) :
    dom (f ≫ c) = Cat.id a ∩ (f ≫ c ≫ f°) := by
  have hcsym : c° = c := symmetric_eq (coreflexive_symmetric_idempotent hc).1
  have hcidem : c ≫ c = c := (coreflexive_symmetric_idempotent hc).2
  unfold dom
  rw [Allegory.recip_comp, hcsym, Cat.assoc, ← Cat.assoc c c f°, hcidem]

/-- **§2.32, the coreflexive `dom` of a map-conjugate is its plain `1 ∩`-meet.**  For a map
    `f : a → b` and a coreflexive `c` on `b`, `dom (f ≫ c ≫ f°) = 1 ∩ f c f°`.  (The general
    `dom R = 1 ∩ R R°` collapses because `R := f c f°` is symmetric and `f° f ⊑ 1` makes
    `R R° ⊑ R`, while `R` is itself a meet of symmetric idempotents.)  Together with
    `dom_comp_coref` this says `dom (f ≫ c) = dom (f ≫ c ≫ f°) = 1 ∩ f c f°`. -/
theorem dom_map_coref {a b : 𝒜} (f : a ⟶ b) (hf : Map f) {c : b ⟶ b} (hc : Coreflexive c) :
    dom (f ≫ c ≫ f°) = Cat.id a ∩ (f ≫ c ≫ f°) := by
  have hsym : (f ≫ c ≫ f°)° = f ≫ c ≫ f° := by
    have hCsym : c° = c := symmetric_eq (coreflexive_symmetric_idempotent hc).1
    rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, hCsym, Cat.assoc]
  have hCidem : c ≫ c = c := (coreflexive_symmetric_idempotent hc).2
  have hidem_le : (f ≫ c ≫ f°) ≫ (f ≫ c ≫ f°) ⊑ f ≫ c ≫ f° := by
    have hmid : c ≫ (f° ≫ f) ≫ c ⊑ c := by
      calc c ≫ (f° ≫ f) ≫ c ⊑ c ≫ Cat.id b ≫ c := comp_mono_left c (comp_mono_right hf.2 c)
        _ = c ≫ c := by rw [Cat.id_comp]
        _ = c := hCidem
    calc (f ≫ c ≫ f°) ≫ (f ≫ c ≫ f°)
        = f ≫ (c ≫ (f° ≫ f) ≫ c) ≫ f° := by
          rw [Cat.assoc, Cat.assoc, Cat.assoc, Cat.assoc, Cat.assoc]
      _ ⊑ f ≫ c ≫ f° := comp_mono_left f (comp_mono_right hmid f°)
  unfold dom
  rw [hsym]
  apply le_antisymm
  · exact le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) hidem_le)
  · apply le_inter (inter_lb_left _ _)
    have hKcor : Coreflexive (Cat.id a ∩ (f ≫ c ≫ f°)) := inter_lb_left _ _
    have hKidem : (Cat.id a ∩ (f ≫ c ≫ f°)) ≫ (Cat.id a ∩ (f ≫ c ≫ f°))
        = Cat.id a ∩ (f ≫ c ≫ f°) := (coreflexive_symmetric_idempotent hKcor).2
    rw [← hKidem]
    exact le_trans (comp_mono_right (inter_lb_right _ _) _)
      (comp_mono_left _ (inter_lb_right _ _))

-- BOOK §2.32: A is a tabular unitary division allegory iff Mσn(A) is a logos.
-- STATUS: OPEN (both directions).
-- AVAILABLE:
--   • `mapPreLogos` in MapCat.lean: `PreLogos (MapObj 𝒜)` for `[TabularUnitaryDistributiveAllegory 𝒜]`
--     (terminal, pullbacks, regular covers, subobject unions, bottom, inverse-image preservation).
--   • `leftDiv` (§2.312) is defined above in this file.
-- MISSING (FORWARD, logos → division allegory):
--   • `DivisionAllegory (RelObj 𝒞)` for `[Logos 𝒞]`.  S1_77.lean proves the adjointness
--     `T ⊑ R/(graph f)°` ↔ `T⊚(graph f)° ⊑ R` for maps `f`, but the full right division
--     `R/S` for an arbitrary relation `S` (not just a graph) is not yet assembled as an
--     instance; `DivisionAllegory (RelObj 𝒞)` does not exist in RelCat.lean.
-- MISSING (BACKWARD, division allegory → logos on Map(𝒜)):
--   • EXACT FIELD NEEDED.  `Logos (MapObj 𝒜)` = `mapPreLogos` (DONE) + `HasRightAdjointImage`.
--     `HasRightAdjointImage` (S1_70) needs ONE constructive field beyond pullbacks/images:
--         rightAdj : ∀ {A B} (f : A ⟶ B), Subobject (MapObj 𝒜) A → Subobject (MapObj 𝒜) B
--         adjunction : (InverseImage f B').le A' ↔ B'.le (rightAdj f A')      [B':Sub B, A':Sub A]
--   • THE TRANSLATION IS DONE (bridge already in MapCat, here made usable):
--     under the iso `Sub(MapObj 𝒜) X ≅ Cor(X)` (`corOf`/`splitSub`, `le_iff_corOf_le`,
--     `corOf_splitSub`, `corOf_invImage` in MapCat), with `f : a → b` a map, `A := corOf A'`
--     (coreflexive on a), `c := corOf B'` (coreflexive on b), the adjunction is EXACTLY
--         dom (f.val ≫ c ≫ f.val°) ⊑ A   ↔   c ⊑ corOf (rightAdj f A')              (★)
--     and `corOf_invImage` rewrites the LHS to `dom (f c f°)`, which by `dom_map_coref`
--     (proved just above) equals `1 ∩ f c f°` — Freyd's lower function `1 ∩ f B f°`
--     (= `dom (f≫c)` by `dom_comp_coref`).  So `rightAdj f A' := splitSub <coreflexive D>`
--     reduces the whole problem to ONE poset statement:
--         find a coreflexive `D` on `b` with   (1 ∩ f c f°) ⊑ A  ↔  c ⊑ D   for all coref `c`.
--   • THE ONE GENUINELY MISSING BRICK (mathematical depth, NOT mere infra):
--     `D` is the RIGHT ADJOINT of the monotone map `c ↦ 1 ∩ f c f° : Cor(b) → Cor(a)`.
--     Freyd's closed form is `D = f \ (1 → A) / f°` where `→` is the Heyting arrow ON THE FULL
--     HOM-POSET `(a,a)` (his words: "the Heyting arrow on (α,α), NOT Cor(α)").  The naive read
--     `1 → A = 1 ∩ A/1 = A` (A coref) is WRONG: it yields `D = f\A/f°`, whose adjunction
--     (`le_div_iff` ∘ `le_leftDiv_iff`) is `c ⊑ f\A/f° ↔ f c f° ⊑ A` — STRICTLY STRONGER than
--     `1 ∩ f c f° ⊑ A` (counterexample: `c = 1` forces `f f° ⊑ A`, false unless `f` is a
--     retraction-mono).  Hence the `1 ∩` cannot be dropped, and `D ≠ f\A/f°`.
--   • WHAT IS REALLY REQUIRED:  the FULL hom-poset `(a,a)` (not just `Cor(a)`) must be a HEYTING
--     ALGEBRA — i.e. `∩` must have a relative pseudocomplement `X ⟹ Y` (`Z ∩ X ⊑ Y ↔ Z ⊑ X⟹Y`).
--     A division allegory supplies the `≫`-residual `/`, NOT the `∩`-residual, so `(a,a)` Heyting
--     does NOT follow from `DivisionAllegory` alone.  Freyd gets it from §2.316's LAST paragraph:
--     in a TABULAR UNITARY division allegory tabulate the maximal morphism `⊤ : a → a` by
--     `(ℓ₁,ℓ₂) : γ → a × a`; then `(a,a) ≅ Cor(γ)` (`R ↦ 1 ∩ ℓ₁ R ℓ₂°`), and the `(a,a)` arrow is
--     the Cor(γ) Heyting arrow transported across that iso.  (THIS is why the theorem needs
--     tabular + unitary, not just division.)
--   • REPO STATUS OF THAT BRICK: ABSENT.  There is no `⊤`/maximal-morphism tabulation, no
--     `(a,a) ≅ Cor(γ)` iso, and no `(a,a)`-Heyting-algebra instance in the repo.  `UnitaryAllegory`
--     gives only a unit object (`unit_obj`/`unit_prop`), not the tabulated top or the §2.316 iso.
--     Building these (⊤-tabulation + the poset iso + transported Heyting arrow) is a multi-lemma
--     §2.316-final-paragraph construction — a real piece of mathematics, not a one-line bridge.
--   • DELIVERED HERE: `dom_comp_coref`, `dom_map_coref` (both proved, axiom-clean) reduce the
--     backward direction to exactly statement (★)+the `D`-existence poset fact above; the residual
--     gap is precisely "(a,a) is a Heyting algebra via the ⊤-tabulation `(a,a) ≅ Cor(γ)`".

/-! ## §2.331  Moerdijk representation theorems

  These results about faithful representation in O(X)-valued sets are classical
  topology / locale theory results (Ieke Moerdijk).  They require the locale
  O(X) of open sets of a metrizable space X (without isolated points) and the
  allegory of O(X)-valued sets [§2.227]. -/

-- BOOK §2.331 (i): Let X be a metrizable space without isolated points, O(X) the locale
-- of open subsets thereof.  Any countable tabular unitary division allegory may be
-- faithfully represented in a countable power of the allegory of O(X)-valued sets.

-- BOOK §2.331 (ii): Any countable tabular unitary division allegory may be faithfully
-- represented in a countable power of the allegory of O(X)-valued sets.

-- BOOK §2.331 (iii): Any countable logos may be faithfully represented in a countable
-- power of H(X).

-- BOOK §2.331 (iv): Any countable logos with a coprime terminator may be faithfully
-- represented in H(X).

-- STATUS: OPEN — all four parts out of scope for the current formalization.
-- MISSING: (a) a locale `O(X)` type for metrizable X (Locale.lean has abstract frames but no
--   topology); (b) the allegory of `O(X)`-valued sets (§2.227); (c) Heyting algebra `H(X)`;
--   (d) Moerdijk's embedding `O(2^ω) ↪ O(X)` used to pass from the Cantor space to X.
--   None of (a)–(d) exist in this repo.  Out of scope for the current formalization.

/-! ## §2.34  Split allegory PRel(E) is a division allegory -/

-- BOOK §2.34: Let A be a division allegory, E a class of symmetric idempotents.
-- Then PRel(E) (the E-split completion of A) is a division allegory.
-- If |A| ⊂ E (all objects are in E) then A → PRel(E) is a faithful embedding of
-- division allegories.
-- STATUS: DONE for the full-Spl case (E = all symmetric idempotents); see below.
-- AVAILABLE: `SplObj 𝒜` (S2_21.lean) = the case E = all symmetric idempotents, with
--   `instAllegorySpl`, `instDistributiveSpl`, `instUnitarySpl`, `instPositiveSpl`,
--   `instTabularAllegorySplCor` (Spl.lean), `splObj_tabular_of_semiSimple`.
-- FULL-Spl case (E = all symmetric idempotents) DONE: `DivisionAllegory (SplObj 𝒜)` for
--   `[DivisionAllegory 𝒜]` is PROVED as `instDivisionSpl` (Spl.lean) — pointwise division
--   `splDiv = E.e ≫ (R.R/S.R) ≫ F.e`, both §2.31 laws via SplHom.fixed + base div_comp_le/le_div.
-- MISSING: (2) For restricted PRel(E) with E ⊊ all-sym-idempotents: not yet
--   needed; the full-Spl case subsumes the faithful-embedding claim when |A| ⊂ E.

/-! ## §2.342  Positive reflection of a division allegory

  **PROVED** in `Fredy.MatrixAllegory` (imported below is impossible due to the import cycle
  `MatrixAllegory → S2_3`; the result lives in the downstream file by necessity).

  The POSITIVE REFLECTION A⁺ of a division allegory A is the matrix allegory `MatObj 𝒜`:
  - Objects are finite-index families of A-objects (`Fin n → 𝒜`).
  - Morphisms are `n×m` matrices of A-morphisms.
  - Composition: `(MN)_{ik} = ⨆_j M_{ij} ≫ N_{jk}` (finite join).
  - Division: `(R/S)_{ij} = ⋀_k R_{ik}/S_{jk}` (finite meet over the codomain index).

  The key adjointness check — `T ⊑ R/S ↔ T≫S ⊑ R` — reduces to `le_div_iff` entrywise:
  the join in the composition pairs with the meet in the division via `finJoin_le`/`le_finMeet`.

  The 1×1 embedding `embed1 : 𝒜 → MatObj 𝒜` is faithful and preserves ≫, °, ∩, ∪, 𝟘, /.

  Relevant declarations in `Fredy.MatrixAllegory` (namespace `Freyd.Alg.Mat`):
    `instDivisionAllegoryMat`  : `DivisionAllegory (MatObj 𝒜)` [noncomputable, §2.342]
    `embed1_injective`, `embed1_div` : faithfulness + division preservation -/

/-! ## §2.343  Every logos faithfully and fully embeds in a positive effective logos -/

-- BOOK §2.343: Every logos C embeds faithfully and fully in a positive effective logos via
-- C → Mσn(H̃(Eq(Rel(C))⁺)), using §2.32, §2.216 (A⁺ faithfully embeds A), §2.169 (Spl).
-- STATUS: OPEN.
-- AVAILABLE steps:
--   Rel(C)     — `Allegory (RelObj C)` + `DistributiveAllegory`: proved in RelCat.lean.
--   A⁺ = Mat(A)  — `DivisionAllegory (MatObj 𝒜)`: `instDivisionAllegoryMat` in MatrixAllegory.
--   Eq(A) = SplObj — `instAllegorySpl`, effective: proved in S2_21/S2_22b/Spl.lean.
--   Mσn(A) — `Cat (MapObj 𝒜)`: `mapCat` in MapCat.lean; `PreLogos (MapObj 𝒜)`: `mapPreLogos`.
--   §2.217(1) (not §2.343): `C ↪ Map(Mat(Rel C))` faithful + target positive-pre-logos:
--   `s217_faithful_embed_into_positive` in RelCat.lean.  This covers the PRE-LOGOS version.
-- MISSING for §2.343 specifically:
--   • `Logos (MapObj 𝒜)` (not just `PreLogos`): needs `HasRightAdjointImage` on `MapObj 𝒜`
--     (the §2.32 gap above).
--   • The §2.343 target is `Mσn(Eq(Rel(C))⁺)` = `Map(SplObj(Mat(Rel C)))`.  Its
--     `DivisionAllegory (SplObj 𝒜)` prerequisite (§2.34) is DONE (`instDivisionSpl`);
--     the remaining blocker is §2.32 backward (`HasRightAdjointImage (MapObj 𝒜)`).
--   • Fullness of the composite embedding `C → Map(SplObj(Mat(Rel C)))` has not been assembled.

end Freyd.Alg
