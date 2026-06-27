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

/-! ## §2.315(a)  Every locally complete distributive allegory is a division allegory

  In a `LocallyCompleteDistributiveAllegory` the right adjoint to `(-) ≫ S`
  exists as a supremum: `R / S := ⊔ {T | T ≫ S ⊑ R}`.  The two `DivisionAllegory`
  fields then follow from `Sup_le`/`le_Sup`.  (`div_comp_le` needs that composition
  on the *right* distributes over `Sup`; we get that by reciprocating the left
  distributivity `comp_Sup_distrib`.) -/

section LCDADivision

open LocallyCompleteDistributiveAllegory

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-- Reciprocation commutes with `Sup`: `(Sup P)° = Sup {R° | P R}`.
    Reciprocation is an order-isomorphism, so it carries suprema to suprema. -/
theorem recip_Sup {a b : 𝒜} (P : (a ⟶ b) → Prop) :
    (Sup P)° = Sup (fun T : b ⟶ a => ∃ R, P R ∧ T = R°) := by
  apply le_antisymm
  · -- (Sup P)° ⊑ Sup Pᵒ  ↔  Sup P ⊑ (Sup Pᵒ)°  (recip adjoint); then Sup_le pointwise.
    apply recip_le_iff.mpr
    apply Sup_le; intro R hR
    -- R ⊑ (Sup Pᵒ)°  ↔  R° ⊑ Sup Pᵒ, and R° is a member of Pᵒ.
    exact recip_le_iff.mp (le_Sup ⟨R, hR, rfl⟩)
  · -- Sup Pᵒ ⊑ (Sup P)°: each member R° ⊑ (Sup P)° since R ⊑ Sup P.
    apply Sup_le; intro T ⟨R, hR, hT⟩
    subst hT; exact recip_mono (le_Sup hR)

/-- Composition on the right distributes over `Sup`: `(Sup P) ≫ S = ⊔ {T ≫ S | P T}`.
    Derived from the left law `comp_Sup_distrib` by reciprocation. -/
theorem Sup_comp_distrib {a b c : 𝒜} (P : (a ⟶ b) → Prop) (S : b ⟶ c) :
    Sup P ≫ S = Sup (fun T : a ⟶ c => ∃ R, P R ∧ T = R ≫ S) := by
  apply le_antisymm
  · -- (Sup P)S ⊑ ⊔{RS}.  Reciprocate both sides: ((Sup P)S)° ⊑ (⊔{RS})°, i.e.
    -- S°(Sup P)° ⊑ (⊔{RS})°.
    have key : (Sup P ≫ S)° ⊑ (Sup (fun T : a ⟶ c => ∃ R, P R ∧ T = R ≫ S))° := by
      rw [Allegory.recip_comp, recip_Sup, comp_Sup_distrib]
      apply Sup_le; intro U ⟨T, ⟨R, hR, hT⟩, hU⟩
      subst hT; subst hU
      -- S° ≫ R° = (R ≫ S)° ⊑ (⊔{RS})°  since R ≫ S is a member.
      rw [← Allegory.recip_comp]
      have hmem : (fun T : a ⟶ c => ∃ R', P R' ∧ T = R' ≫ S) (R ≫ S) := ⟨R, hR, rfl⟩
      exact recip_mono (le_Sup hmem)
    have := recip_mono key
    rwa [Allegory.recip_recip, Allegory.recip_recip] at this
  · -- ⊔{RS} ⊑ (Sup P)S: each RS ⊑ (Sup P)S since R ⊑ Sup P.
    apply Sup_le; intro T ⟨R, hR, hT⟩
    subst hT; exact comp_mono_right (le_Sup hR) S

/-- Right division in a locally complete distributive allegory: `R / S := ⊔ {T | T ≫ S ⊑ R}`. -/
def lcdaDiv {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : a ⟶ b :=
  Sup (fun T : a ⟶ b => T ≫ S ⊑ R)

/-- The semi-commutative triangle `(R / S) ≫ S ⊑ R` (§2.31 field). -/
theorem lcdaDiv_comp_le {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : lcdaDiv R S ≫ S ⊑ R := by
  rw [lcdaDiv, Sup_comp_distrib]
  apply Sup_le; intro T ⟨U, hU, hT⟩
  subst hT; exact hU

/-- The adjointness `T ≫ S ⊑ R → T ⊑ R / S` (§2.31 field). -/
theorem le_lcdaDiv {a b c : 𝒜} (T : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) (h : T ≫ S ⊑ R) :
    T ⊑ lcdaDiv R S :=
  le_Sup h

/-- (§2.315a) A locally complete distributive allegory is a division allegory, with
    `R / S = ⊔ {T | T ≫ S ⊑ R}`.  Provided as a `def` (not a global instance) to avoid a
    typeclass-resolution loop: `DivisionAllegory` extends `DistributiveAllegory`, so a global
    instance here would give `DistributiveAllegory X` two derivations (direct, and via this).
    Apply with `letI`/`@`. -/
def divisionAllegoryLCDA : DivisionAllegory 𝒜 :=
  { (inferInstance : LocallyCompleteDistributiveAllegory 𝒜).toDistributiveAllegory with
    div         := fun R S => lcdaDiv R S
    div_comp_le := fun R S => lcdaDiv_comp_le R S
    le_div      := fun T R S h => le_lcdaDiv T R S h }

end LCDADivision

/-! ## §2.315  Division allegory → locally complete distributive allegory

  Any division allegory is faithfully representable in a locally complete
  distributive allegory, and thus in a globally complete allegory.

  (Proof sketch: R/S is constructible as ⊔{T | TS ⊑ R} in the local completion;
  the local-completion embedding A → Â is faithful; and a globally complete
  allegory subsumes locally complete.) -/

-- BOOK §2.315: Any division allegory is faithfully representable in a locally complete
-- distributive allegory, and thus in a globally complete allegory.
-- STATUS: DONE.
-- The local completion `Â = Downdeal 𝒜` (ideals of A-homs, S2_2.lean) is a
-- `LocallyCompleteDistributiveAllegory`; by §2.315(a) every LCDA is a `DivisionAllegory`.
-- The principal-ideal embedding `R ↦ ↓R = DowndealHom.prin R` preserves ≫/°/∩/∪/𝟘 and is
-- injective (`DowndealHom.prin_*`).  The headline `divisionAllegory_faithful_in_lcda`
-- packages this.

section Representation

/-- (§2.315) **Any division allegory is faithfully representable in a locally complete
    distributive allegory** (which is, by §2.315(a), itself a division allegory).

    Concretely: for any `DistributiveAllegory ℬ` — in particular any `DivisionAllegory` —
    the local completion `B̂ = Downdeal ℬ` is a `LocallyCompleteDistributiveAllegory` (hence a
    `DivisionAllegory` via `divisionAllegoryLCDA`), and the principal-ideal embedding
    `R ↦ ↓R` is a faithful homomorphism: injective and preserving `≫`, `°`, `∩`, `∪`, `𝟘`.
    (Fresh type variable `ℬ` avoids the file-level `[DivisionAllegory 𝒜]`, which would make
    the base `DistributiveAllegory` ambiguous.) -/
theorem divisionAllegory_faithful_in_lcda {ℬ : Type u} [hℬ : DistributiveAllegory.{u, u} ℬ] :
    -- B̂ is locally complete distributive (and so a division allegory):
    Nonempty (LocallyCompleteDistributiveAllegory.{u, u} (Downdeal ℬ)) ∧
    Nonempty (DivisionAllegory.{u, u} (Downdeal ℬ)) ∧
    -- the embedding R ↦ ↓R is faithful:
    (∀ {a b : ℬ} {R S : a ⟶ b}, DowndealHom.prin R = DowndealHom.prin S → R = S) ∧
    -- and preserves every operation:
    (∀ {a b c : ℬ} (R : a ⟶ b) (S : b ⟶ c),
      DowndealHom.prin (R ≫ S) = DowndealHom.comp (DowndealHom.prin R) (DowndealHom.prin S)) ∧
    (∀ {a b : ℬ} (R : a ⟶ b), DowndealHom.prin (R°) = DowndealHom.recip (DowndealHom.prin R)) ∧
    (∀ {a b : ℬ} (R S : a ⟶ b),
      DowndealHom.prin (R ∩ S) = DowndealHom.inter (DowndealHom.prin R) (DowndealHom.prin S)) ∧
    (∀ {a b : ℬ} (R S : a ⟶ b),
      DowndealHom.prin (R ∪ S) = DowndealHom.union (DowndealHom.prin R) (DowndealHom.prin S)) :=
  by
  letI inst : LocallyCompleteDistributiveAllegory (Downdeal ℬ) :=
    @instLocallyCompleteDistributiveAllegoryDowndealHom ℬ hℬ
  exact ⟨⟨inst⟩, ⟨@divisionAllegoryLCDA (Downdeal ℬ) inst⟩,
    DowndealHom.prin_injective, DowndealHom.prin_comp, DowndealHom.prin_recip,
    DowndealHom.prin_inter, DowndealHom.prin_union⟩

end Representation

/-! ## §2.316 (final paragraph)  The full hom-poset `(a,a)` is a Heyting algebra

  In a TABULAR UNITARY division allegory, tabulate the maximal morphism `⊤ : a → a`
  by maps `ℓ₁, ℓ₂ : γ → a`.  Then `(a,a) ≅ Cor(γ)` via `R ↦ 1_γ ∩ ℓ₁ R ℓ₂°`, with
  inverse `c ↦ ℓ₁° c ℓ₂`.  Transporting the Cor(γ) Heyting arrow (`heyting_adj_coref`)
  across this order-iso makes `(a,a)` a Heyting algebra.  We need exactly the special
  arrow `1 → A` (largest `H` with `H ∩ 1 ⊑ A`), used in §2.32 to right-adjoin `f#`. -/

/-- A **TABULAR UNITARY DIVISION ALLEGORY** (§2.316/§2.32): combines `TabularAllegory`,
    `UnitaryAllegory` and `DivisionAllegory` in a SINGLE class so their shared `Allegory`
    grandparent is merged into ONE `toAllegory` field (the diamond-safe inheritance pattern;
    `DivisionAllegory` brings `DistributiveAllegory`, hence `∪`/`𝟘`).  This is exactly the
    hypothesis under which `Mσn(𝒜)` is a logos (§2.32). -/
class TabularUnitaryDivisionAllegory (𝒜 : Type u) extends
    TabularAllegory 𝒜, UnitaryAllegory 𝒜, DivisionAllegory 𝒜

section HeytingHom
variable {𝒜 : Type u} [TabularUnitaryDivisionAllegory 𝒜]

open Allegory in
/-- The maximal morphism `⊤ : a → b` of a unitary allegory: `p_a ≫ p_b°` for the
    (map) projections to the unit.  `topMor_max`: every `R ⊑ ⊤`. -/
noncomputable def topMor (a b : 𝒜) : a ⟶ b :=
  (unit_proj_is_map a).choose ≫ (unit_proj_is_map b).choose°

theorem topMor_max {a b : 𝒜} (R : a ⟶ b) : R ⊑ topMor a b :=
  unit_proj_max _ (unit_proj_is_map a).choose_spec _ (unit_proj_is_map b).choose_spec R

/-- A chosen tabulation `(ℓ₁, ℓ₂) : γ → a` of the maximal morphism `⊤ : a → a`. -/
noncomputable def topTab (a : 𝒜) : Σ γ : 𝒜, (γ ⟶ a) × (γ ⟶ a) :=
  ⟨(TabularAllegory.tabular (topMor a a)).choose,
   ((TabularAllegory.tabular (topMor a a)).choose_spec.choose,
    (TabularAllegory.tabular (topMor a a)).choose_spec.choose_spec.choose)⟩

/-- ℓ₁, ℓ₂ are maps; ℓ₁° ℓ₂ = ⊤; ℓ₁ℓ₁° ∩ ℓ₂ℓ₂° = 1_γ. -/
theorem topTab_spec (a : 𝒜) :
    Tabulates (topTab a).2.1 (topTab a).2.2 (topMor a a) :=
  (TabularAllegory.tabular (topMor a a)).choose_spec.choose_spec.choose_spec

theorem topTab_l1_map (a : 𝒜) : Map (topTab a).2.1 := (topTab_spec a).1
theorem topTab_l2_map (a : 𝒜) : Map (topTab a).2.2 := (topTab_spec a).2.1
theorem topTab_eq (a : 𝒜) : topMor a a = (topTab a).2.1° ≫ (topTab a).2.2 :=
  (topTab_spec a).2.2.1
theorem topTab_jointMono (a : 𝒜) :
    (topTab a).2.1 ≫ (topTab a).2.1° ∩ (topTab a).2.2 ≫ (topTab a).2.2° = Cat.id (topTab a).1 :=
  (topTab_spec a).2.2.2

/-- `Φ : (a,a) → Cor(γ)` sends `R` to `1_γ ∩ ℓ₁ R ℓ₂°`. -/
noncomputable def phiCor {a : 𝒜} (R : a ⟶ a) : (topTab a).1 ⟶ (topTab a).1 :=
  Cat.id (topTab a).1 ∩ ((topTab a).2.1 ≫ R ≫ (topTab a).2.2°)

/-- `Ψ : Cor(γ) → (a,a)` sends `c` to `ℓ₁° c ℓ₂`. -/
noncomputable def psiCor {a : 𝒜} (c : (topTab a).1 ⟶ (topTab a).1) : a ⟶ a :=
  (topTab a).2.1° ≫ c ≫ (topTab a).2.2

/-- Dual modular law: `(R≫S) ∩ T ⊑ R ≫ (S ∩ R°≫T)`.  (Reciprocal form of `modular_le`.) -/
theorem modular_le' {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S) ∩ T ⊑ R ≫ (S ∩ R° ≫ T) := by
  have h := modular_le S° R° T° (𝒜 := 𝒜)
  -- h : (S°≫R°) ∩ T° ⊑ (S° ∩ T°≫R)≫R°
  have hr := recip_mono h
  rw [Allegory.recip_inter, ← Allegory.recip_comp, Allegory.recip_recip, Allegory.recip_recip] at hr
  -- hr : ((R≫S) ∩ T) ⊑ ((S° ∩ T°≫R°°)≫R°)°
  simpa [Allegory.recip_comp, Allegory.recip_recip, Allegory.recip_inter] using hr

/-- **Tabulation recovery**: if `(f, g)` are maps from `γ` with `f° ≫ g` maximal
    (so `R ⊑ f° ≫ g` for all `R : a → a`), then `R = f° ≫ (1_γ ∩ f ≫ R ≫ g°) ≫ g`.
    This is the recovery half of the order-iso `(a,a) ≅ Cor(γ)`. -/
theorem tab_recover {a γ : 𝒜} {R : a ⟶ a} {f g : γ ⟶ a} (hfm : Map f) (hgm : Map g)
    (htop : R ⊑ f° ≫ g) :
    f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°) ≫ g = R := by
  have hfs : f° ≫ f ⊑ Cat.id a := hfm.2
  have hgs : g° ≫ g ⊑ Cat.id a := hgm.2
  apply le_antisymm
  · -- upper: f°(1∩fRg°)g ⊑ f°(fRg°)g = (f°f)R(g°g) ⊑ R
    have u1 : f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°) ≫ g ⊑ f° ≫ (f ≫ R ≫ g°) ≫ g :=
      comp_mono_left _ (comp_mono_right (inter_lb_right _ _) g)
    have u2 : f° ≫ (f ≫ R ≫ g°) ≫ g = (f° ≫ f) ≫ R ≫ (g° ≫ g) := by simp [Cat.assoc]
    have u3 : (f° ≫ f) ≫ R ≫ (g° ≫ g) ⊑ R := by
      have := le_trans (comp_mono_right hfs _) (comp_mono_left _ (comp_mono_left R hgs))
      rwa [Cat.id_comp, Cat.comp_id] at this
    exact le_trans u1 (u2 ▸ u3)
  · -- lower: R ⊑ R ∩ f°g ⊑ (f° ∩ Rg°)g ⊑ f°(1∩fRg°)g
    have hReq : R = (f° ≫ g) ∩ R := by
      rw [Allegory.inter_comm]; exact (le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) htop)).symm
    have step2 : (f° ≫ g) ∩ R ⊑ (f° ∩ R ≫ g°) ≫ g := modular_le f° g R
    have step3 : (f° ∩ R ≫ g°) ⊑ f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°) := by
      have h := modular_le' f° (Cat.id γ) (R ≫ g°)
      rw [Cat.comp_id, Allegory.recip_recip] at h
      exact h
    have step4 : (f° ∩ R ≫ g°) ≫ g ⊑ (f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°)) ≫ g :=
      comp_mono_right step3 g
    have step5 : (f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°)) ≫ g = f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°) ≫ g := by
      rw [Cat.assoc]
    calc R = (f° ≫ g) ∩ R := hReq
      _ ⊑ f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°) ≫ g := le_trans step2 (step5 ▸ step4)

/-- **§2.316 crux**: `ψ(φ(R)) = R`. -/
theorem psi_phi {a : 𝒜} (R : a ⟶ a) : psiCor (phiCor R) = R :=
  tab_recover (R := R) (topTab_l1_map a) (topTab_l2_map a)
    ((topTab_eq a) ▸ topMor_max R)

/-- **Tabulation co-recovery**: `φ(ψ(c)) = c` for coreflexive `c` on the apex `γ`, when
    `(f, g)` are maps with `f ≫ f° ∩ g ≫ g° = 1_γ` (jointly monic).  I.e.
    `1_γ ∩ f ≫ (f° ≫ c ≫ g) ≫ g° = c`. -/
theorem tab_corecover {a γ : 𝒜} {c : γ ⟶ γ} {f g : γ ⟶ a} (hfm : Map f) (hgm : Map g)
    (hjm : f ≫ f° ∩ g ≫ g° = Cat.id γ) (hc : Coreflexive c) :
    Cat.id γ ∩ f ≫ (f° ≫ c ≫ g) ≫ g° = c := by
  have hfe : Cat.id γ ⊑ f ≫ f° := by
    have := hfm.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have hge : Cat.id γ ⊑ g ≫ g° := by
    have := hgm.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have htab : Tabulates f g (f° ≫ g) := ⟨hfm, hgm, rfl, hjm⟩
  apply le_antisymm
  · -- 1 ∩ f(f°cg)g° ⊑ c.  Split c = e°e (e map, ee°=1), set x=ef, y=eg.
    obtain ⟨d, e, hem, hee, hee'⟩ := coreflexive_splits hc
    -- ψ(c) = f°cg = (ef)°(eg)
    have hpsi : f° ≫ c ≫ g = (e ≫ f)° ≫ (e ≫ g) := by
      rw [← hee, Allegory.recip_comp]; simp [Cat.assoc]
    -- mediating map H with Hf = ef, Hg = eg; by uniqueness H = e.
    have hxy : (e ≫ f)° ≫ (e ≫ g) ⊑ f° ≫ g := by
      rw [← hpsi]
      -- f°cg ⊑ f°g since c ⊑ 1
      have h1 : f° ≫ c ≫ g ⊑ f° ≫ Cat.id γ ≫ g := comp_mono_left f° (comp_mono_right hc g)
      rwa [Cat.id_comp] at h1
    obtain ⟨hHm, hHf, hHg⟩ :=
      tabulation_UP_forward_witness htab (map_comp hem hfm) (map_comp hem hgm) hxy
    -- explicit mediating map K = (ef)f° ∩ (eg)g°; K = e by uniqueness.
    have hKe : ((e ≫ f) ≫ f° ∩ (e ≫ g) ≫ g°) = e :=
      tabulation_UP_unique htab hHm hem hHf hHg
    -- recip: f(ef)° ∩ g(eg)° = e°.
    have hKrecip : (f ≫ (e ≫ f)° ∩ g ≫ (e ≫ g)°) = e° := by
      have := congrArg (·°) hKe
      simpa [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
        using this
    -- D = 1 ∩ (f(ef)°)≫((eg)g°);  modular ⟹ D ⊑ (f(ef)° ∩ g(eg)°)≫((eg)g°) = e°≫(eg≫g°).
    have hDle : Cat.id γ ∩ f ≫ (f° ≫ c ≫ g) ≫ g° ⊑ c ≫ g ≫ g° := by
      have hgrp : f ≫ (f° ≫ c ≫ g) ≫ g° = (f ≫ (e ≫ f)°) ≫ ((e ≫ g) ≫ g°) := by
        rw [hpsi]; simp [Cat.assoc]
      rw [hgrp, Allegory.inter_comm]
      have hm := modular_le (f ≫ (e ≫ f)°) ((e ≫ g) ≫ g°) (Cat.id γ)
      -- hm : (f(ef)°)((eg)g°) ∩ 1 ⊑ (f(ef)° ∩ 1≫((eg)g°)°)≫((eg)g°)
      have hpr : Cat.id γ ≫ ((e ≫ g) ≫ g°)° = g ≫ (e ≫ g)° := by
        rw [Cat.id_comp, Allegory.recip_comp, Allegory.recip_recip]
      rw [hpr, hKrecip] at hm
      have hKval : e° ≫ ((e ≫ g) ≫ g°) = c ≫ g ≫ g° := by
        rw [← hee]; simp [Cat.assoc]
      rw [hKval] at hm
      exact hm
    -- D ⊑ 1 and D ⊑ c≫g≫g° ⟹ D ⊑ 1 ∩ c≫g≫g° ⊑ c≫(g≫g° ∩ c) = c≫c = c.
    have hfin : (Cat.id γ ∩ f ≫ (f° ≫ c ≫ g) ≫ g°) ⊑ c := by
      have hD1 : (Cat.id γ ∩ f ≫ (f° ≫ c ≫ g) ≫ g°) ⊑ Cat.id γ := inter_lb_left _ _
      have hmeet := modular_le' c (g ≫ g°) (Cat.id γ)
      -- (c≫gg°) ∩ 1 ⊑ c≫(gg° ∩ c°≫1) = c≫(gg° ∩ c)
      have hcc : g ≫ g° ∩ c° ≫ Cat.id γ = c := by
        have hcsym : c° = c := symmetric_eq (coreflexive_symmetric_idempotent hc).1
        rw [Cat.comp_id, hcsym, Allegory.inter_comm]
        exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) (le_trans hc hge))
      rw [hcc] at hmeet
      have hidem : c ≫ c = c := (coreflexive_symmetric_idempotent hc).2
      rw [hidem] at hmeet
      exact le_trans (le_inter hDle hD1) hmeet
    exact hfin
  · -- c ⊑ 1 ∩ f(f°cg)g° : c ⊑ 1 (coref) and c ⊑ f f° c g g° (entirety both sides).
    apply le_inter hc
    have l1 : c ⊑ (f ≫ f°) ≫ c := by
      have := comp_mono_right hfe c; rwa [Cat.id_comp] at this
    have l2 : (f ≫ f°) ≫ c ⊑ (f ≫ f°) ≫ c ≫ (g ≫ g°) := by
      apply comp_mono_left
      have := comp_mono_left c hge; rwa [Cat.comp_id] at this
    have hassoc : (f ≫ f°) ≫ c ≫ (g ≫ g°) = f ≫ (f° ≫ c ≫ g) ≫ g° := by
      simp [Cat.assoc]
    exact hassoc ▸ le_trans l1 l2

/-- `φ(R)` is coreflexive. -/
theorem phiCor_coref {a : 𝒜} (R : a ⟶ a) : Coreflexive (phiCor R) := inter_lb_left _ _

/-- `φ` is monotone. -/
theorem phiCor_mono {a : 𝒜} {R S : a ⟶ a} (h : R ⊑ S) : phiCor R ⊑ phiCor S :=
  le_inter (inter_lb_left _ _)
    (le_trans (inter_lb_right _ _) (comp_mono_left _ (comp_mono_right h _)))

/-- `ψ` is monotone. -/
theorem psiCor_mono {a : 𝒜} {c d : (topTab a).1 ⟶ (topTab a).1} (h : c ⊑ d) :
    psiCor c ⊑ psiCor d :=
  comp_mono_left _ (comp_mono_right h _)

/-- `φ(ψ(c)) = c` for coreflexive `c` (specialization of `tab_corecover` to the chosen
    tabulation of `⊤_a`). -/
theorem phi_psi {a : 𝒜} {c : (topTab a).1 ⟶ (topTab a).1} (hc : Coreflexive c) :
    phiCor (psiCor c) = c :=
  tab_corecover (topTab_l1_map a) (topTab_l2_map a) (topTab_jointMono a) hc

/-- `φ` reflects order: `φ(X) ⊑ φ(Y) ↔ X ⊑ Y` (an order-iso onto `Cor(γ)`). -/
theorem phiCor_le_iff {a : 𝒜} (X Y : a ⟶ a) : phiCor X ⊑ phiCor Y ↔ X ⊑ Y := by
  constructor
  · intro h
    have := psiCor_mono h
    rwa [psi_phi, psi_phi] at this
  · exact phiCor_mono

/-- `ψ`-`φ` Galois iff for coreflexive targets: `Z ⊑ ψ(c) ↔ φ(Z) ⊑ c`. -/
theorem le_psiCor_iff {a : 𝒜} (Z : a ⟶ a) {c : (topTab a).1 ⟶ (topTab a).1}
    (hc : Coreflexive c) : Z ⊑ psiCor c ↔ phiCor Z ⊑ c := by
  constructor
  · intro h
    have := phiCor_mono h
    rwa [phi_psi hc] at this
  · intro h
    have := psiCor_mono h
    rwa [psi_phi] at this

/-- `φ` preserves meets: `φ(X ∩ Y) = φ(X) ∩ φ(Y)`. -/
theorem phiCor_inter {a : 𝒜} (X Y : a ⟶ a) : phiCor (X ∩ Y) = phiCor X ∩ phiCor Y := by
  apply le_antisymm
  · exact le_inter (phiCor_mono (inter_lb_left _ _)) (phiCor_mono (inter_lb_right _ _))
  · -- φX ∩ φY ⊑ φ(X∩Y): both coreflexive; transport back via ψ and the meet-on-Cor.
    have hle : phiCor X ∩ phiCor Y ⊑ phiCor (X ∩ Y) := by
      -- ψ(φX ∩ φY) ⊑ X and ⊑ Y, so ⊑ X∩Y; then φ-monotone + φψ.
      have hcor : Coreflexive (phiCor X ∩ phiCor Y) :=
        le_trans (inter_lb_left _ _) (phiCor_coref X)
      have hX : psiCor (phiCor X ∩ phiCor Y) ⊑ X := by
        have := psiCor_mono (inter_lb_left (phiCor X) (phiCor Y)); rwa [psi_phi] at this
      have hY : psiCor (phiCor X ∩ phiCor Y) ⊑ Y := by
        have := psiCor_mono (inter_lb_right (phiCor X) (phiCor Y)); rwa [psi_phi] at this
      have hXY : psiCor (phiCor X ∩ phiCor Y) ⊑ X ∩ Y := le_inter hX hY
      have := phiCor_mono hXY
      rwa [phi_psi hcor] at this
    exact hle

-- ⊤ → A : the largest H with H ∩ 1 ⊑ A.
/-- The Heyting special arrow `1 → A` on the full poset `(a,a)`: `Ψ(Φ(1) ⟹ Φ(A))`,
    where `⟹` is the Cor(γ) Heyting arrow. -/
noncomputable def oneHeyting {a : 𝒜} (A : a ⟶ a) : a ⟶ a :=
  psiCor (heytingImpl (phiCor (Cat.id a)) (phiCor A))

/-- **§2.316 / §2.32 adjunction**: for coreflexive `A`, `oneHeyting A` is the largest
    `Z : (a,a)` whose coreflexive part lies under `A`:  `Z ∩ 1 ⊑ A ↔ Z ⊑ oneHeyting A`. -/
theorem oneHeyting_adj {a : 𝒜} (A : a ⟶ a) (Z : a ⟶ a) :
    Z ∩ Cat.id a ⊑ A ↔ Z ⊑ oneHeyting A := by
  have hP : Coreflexive (heytingImpl (phiCor (Cat.id a)) (phiCor A)) := inter_lb_left _ _
  rw [oneHeyting, le_psiCor_iff Z hP]
  -- φZ ⊑ (φ1 ⟹ φA)  ↔  φ1 ≫ φZ ⊑ φA   (heyting_adj_coref)
  rw [← heyting_adj_coref (phiCor_coref (Cat.id a)) (phiCor_coref Z)]
  -- φ1 ≫ φZ = φ1 ∩ φZ = φ(1 ∩ Z); and ⊑ φA ↔ 1 ∩ Z ⊑ A.
  rw [coreflexive_comp_eq_inter (phiCor_coref (Cat.id a)) (phiCor_coref Z),
      Allegory.inter_comm (phiCor (Cat.id a)) (phiCor Z), ← phiCor_inter,
      phiCor_le_iff, Allegory.inter_comm Z (Cat.id a)]

end HeytingHom

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
-- STATUS: BOTH directions DONE.
-- BACKWARD direction DONE (`Logos (MapObj A)` in MapCat.lean, `mapLogos`, axiom-clean
--   `[propext, Classical.choice]`).
-- FORWARD (logos → division allegory) — DONE (§1.784):
--   • `DivisionAllegory (RelObj 𝒞)` for `[Logos 𝒞]` = `relDivisionAllegory` (RelCat.lean,
--     axioms `[propext, Classical.choice, Quot.sound]`).  S1_77 proves the two special
--     quotients — by a graph (`relQuotByMap`) and by the reciprocal of a graph
--     (`relQuotByMapRecip`, the `f##` right-adjoint image).  The general `R/S` for an arbitrary
--     relation `S` is `relQuotGen R S = (R/graph(S.colB))/(graph S.colA)°`, using the span
--     factorisation `S ≈ (graph S.colA)° ⊚ graph S.colB` (`reconstitute_le`/`le_reconstitute`) and
--     §1.783 associativity.  `qDiv` descends it to the `RelLe`-quotient; both adjunction laws are
--     `relQuotGen.le`/`.maximal` across the `quotLe ↔ ⊑` bridge.  This unblocks §2.343.
-- BACKWARD (division allegory → logos on Map(𝒜)) — DONE.  The construction (Freyd §2.316 final
--   paragraph + §2.32) is split between THIS file (the §2.316 Heyting machinery) and MapCat.lean
--   (the subobject bridge + the `Logos` instance):
--   • §2.316 HOM-POSET HEYTING ARROW (this file, `section HeytingHom`):
--     - `topMor`/`topMor_max`: the maximal morphism `⊤_{a,b} = p_a ≫ p_b°` of the unit (`R ⊑ ⊤`).
--     - `topTab`: a chosen tabulation `(ℓ₁,ℓ₂) : γ → a` of `⊤_a` (`topTab_spec`).
--     - `phiCor R := 1_γ ∩ ℓ₁ R ℓ₂°`,  `psiCor c := ℓ₁° c ℓ₂`:  the ORDER-ISO `(a,a) ≅ Cor(γ)`.
--       `psi_phi : ψ(φ R) = R` (via `tab_recover`) and `phi_psi : φ(ψ c) = c` for coreflexive `c`
--       (via `tab_corecover`, joint-monicity + `tabulation_UP_*`); `phiCor_le_iff`, `phiCor_inter`,
--       `le_psiCor_iff` are the order/meet/Galois consequences.
--     - `oneHeyting A := ψ(φ1 ⟹ φA)` (the §2.316 arrow `1 → A` on `(a,a)`, NOT on `Cor(a)`), with
--       `oneHeyting_adj : Z ∩ 1 ⊑ A ↔ Z ⊑ oneHeyting A`  (the relative pseudocomplement of `∩`).
--   • §2.32 RIGHT ADJOINT TO `f#` (MapCat.lean, `section MapLogos`):  under the subobject bridge
--     `Sub(Map A) X ≅ Cor(X)`, `corOf_invImage` + `dom_map_coref` give `corOf (f# B') = 1 ∩ f c f°`.
--     `rightAdjCor f A := 1_b ∩ f \ (oneHeyting A) / f°` is its right adjoint
--     (`rightAdjCor_adj`: `1 ∩ f c f° ⊑ A ↔ c ⊑ rightAdjCor f A`, via `le_leftDiv_iff`/`le_div_iff`
--     ∘ `oneHeyting_adj`).  `mapHasRightAdjointImage` = `splitSub ∘ rightAdjCor`; `mapLogos` then
--     bundles it with `mapPreLogos`.  (`D = f\A/f°` would be WRONG: its adjunction `f c f° ⊑ A` is
--     strictly stronger than `1 ∩ f c f° ⊑ A` — hence the genuine §2.316 `oneHeyting` is needed.)

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
-- C → Mσn(H̃(Eq(Rel(C))⁺)) = Map(SplObj(Mat(Rel C))), using §2.32, §2.216, §2.169 (Spl).
-- STATUS: DONE — assembled in `Fredy/RelCat.lean` (this file cannot import RelCat/MapCat without a
-- cycle, so the theorems live there; their statements/names are recorded here).
--
-- The target `D := Map(SplObj(Mat(Rel C)))` and the embedding `embed217_2 : C → D` (already FAITHFUL
-- from §2.217(2)) are reused; over `[Logos C]` they upgrade to the §2.343 headline:
--
--   PART A (structure) — `D` is a POSITIVE EFFECTIVE LOGOS (`Freyd.s343_positive_effective_logos`):
--     • `Freyd.splMatRelTUDiv` : `TabularUnitaryDivisionAllegory (SplObj (Mat (Rel C)))`, assembling
--       `relDivisionAllegory` (§1.784/§2.32 fwd, `RelObj C`) → `instDivisionAllegoryMat` (§2.342) →
--       `instDivisionSpl` (§2.31) for division, with tabular+unitary from `splMatRelTUP`.
--     • `Freyd.s343_logos`            : `Logos D`             (`mapLogos`, §2.32 backward);
--     • positivity                    : `s217_2_target_positivePreLogos.toHasBinaryCoproducts`;
--     • `Freyd.s343_effectiveRegular` : `EffectiveRegular D`  (`mapEffectiveRegular`, §2.217(2) split).
--
--   PART B (fullness) — `Freyd.embed217_2_full`: every `D`-morphism `embed217_2Obj a ⟶ embed217_2Obj b`
--   is `embed217_2 f` for a unique `f`.  The collapse runs down the tower
--     Spl (`embHom_full` + `embHom_reflects_map`) → Mat 1×1 (`Fin 1` + `embed1_reflects_map`) →
--     Rel (`embedRel_full`, every Map is the graph of a unique C-morphism).
--
--   HEADLINE: `Freyd.s343_full_faithful_embed_into_positive_effective_logos` — there is a positive
--   effective logos structure on `D` plus a FULL+FAITHFUL embedding `C ↪ D`.  Bare `[Logos C]`.
--   Axioms: [propext, Classical.choice, Quot.sound], no `sorryAx`.

end Freyd.Alg
