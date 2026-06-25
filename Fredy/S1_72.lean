/-
  Freyd & Scedrov, *Categories and Allegories* §1.72–§1.76
  Heyting algebras, Negation, Focal logoi, Representation theorems.

  §1.72  Heyting algebra: lattice with implication → (right adjoint to ∧).
  §1.723 Locale: complete lattice with finite-meet/arbitrary-join distributivity.
  §1.724 Double-arrow x⟺y = (x→y)∧(y→x), commutative with unit 1.
  §1.725 Equational theory of Heyting algebras.
  §1.726 Derived equations (x→y covariant in y, contravariant in x; distributivity).
  §1.727 Negation: ¬x = x→0, double negation, De Morgan.
  §1.728 Law of excluded middle ⇒ Boolean algebra.
  §1.73  ℱ(T) filter, A/ℱ quotient logos.
  §1.733 Coprime object, connected object, FOCAL LOGOS (1 is coprime projective).
  §1.734 Focal representation, representation theorems.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_57
import Fredy.S1_60
import Fredy.S1_64
import Fredy.S1_70


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.72 Heyting algebra

  A HEYTING ALGEBRA is a lattice with a binary → such that
  z ≤ x → y  ⇔  x ∧ z ≤ y  (→ is right adjoint to ∧, fixing x).
  The underlying poset must be a lattice, so meet satisfies the standard
  lattice axioms (meet_le_left, meet_le_right, le_meet). -/

/-- A HEYTING ALGEBRA: lattice with implication satisfying the adjunction
    z ≤ (x→y) ↔ x∧z ≤ y  (book §1.72). -/
class HeytingAlgebra (𝒞 : Type u) [Cat.{v} 𝒞] [HasImages 𝒞]
    extends HasSubobjectUnions 𝒞 where
  /-- Binary meet (∧) of subobjects. -/
  meet : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject 𝒞 A
  /-- meet is a lower bound: x∧y ≤ x. -/
  meet_le_left  : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject.le (meet x y) x
  /-- meet is a lower bound: x∧y ≤ y. -/
  meet_le_right : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject.le (meet x y) y
  /-- meet is the greatest lower bound: z ≤ x → z ≤ y → z ≤ x∧y. -/
  le_meet : ∀ {A : 𝒞} (x y z : Subobject 𝒞 A),
    Subobject.le z x → Subobject.le z y → Subobject.le z (meet x y)
  /-- Implication x → y. -/
  imp  : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject 𝒞 A
  /-- The adjunction: z ≤ (x→y) ↔ x∧z ≤ y. -/
  adjunction : ∀ {A : 𝒞} (x y z : Subobject 𝒞 A),
    Subobject.le z (imp x y) ↔ Subobject.le (meet x z) y

/-! ## §1.725-§1.726 Derived laws in a Heyting algebra

  Derived laws from the double-Horn characterization (§1.725–§1.726):
  monotonicity of → in each argument, and finite-meet distributivity. -/

section HeytingLaws

variable [HasImages 𝒞] [HeytingAlgebra 𝒞] {A : 𝒞}

/-- z ≤ (x→y) ↔ x∧z ≤ y  (adjunction alias). -/
theorem heyting_adj (x y z : Subobject 𝒞 A) :
    Subobject.le z (HeytingAlgebra.imp x y) ↔
    Subobject.le (HeytingAlgebra.meet x z) y :=
  HeytingAlgebra.adjunction x y z

/-- Modus ponens: x∧(x→y) ≤ y  (from adjunction, taking z := x→y). -/
theorem heyting_mp (x y : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet x (HeytingAlgebra.imp x y)) y :=
  (heyting_adj x y (HeytingAlgebra.imp x y)).mp (subobject_le_refl _)

/-- meet is monotone in the left argument: w ≤ x → w∧z ≤ x∧z. -/
theorem meet_mono_left {w x z : Subobject 𝒞 A} (h : Subobject.le w x) :
    Subobject.le (HeytingAlgebra.meet w z) (HeytingAlgebra.meet x z) :=
  HeytingAlgebra.le_meet _ _ _
    (subobject_le_trans (HeytingAlgebra.meet_le_left _ _) h)
    (HeytingAlgebra.meet_le_right _ _)

/-- meet is symmetric: x∧y ≤ y∧x. -/
theorem meet_comm_le (x y : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet x y) (HeytingAlgebra.meet y x) :=
  HeytingAlgebra.le_meet _ _ _
    (HeytingAlgebra.meet_le_right _ _)
    (HeytingAlgebra.meet_le_left _ _)

/-- (§1.726) x→y is covariant in y: y ≤ z → (x→y) ≤ (x→z). -/
theorem imp_mono_right {x y z : Subobject 𝒞 A} (h : Subobject.le y z) :
    Subobject.le (HeytingAlgebra.imp x y) (HeytingAlgebra.imp x z) := by
  rw [heyting_adj]
  -- x∧(x→y) ≤ y ≤ z
  exact subobject_le_trans (heyting_mp x y) h

/-- (§1.726) x→y is contravariant in x: w ≤ x → (x→y) ≤ (w→y). -/
theorem imp_mono_left_contra {x w y : Subobject 𝒞 A} (h : Subobject.le w x) :
    Subobject.le (HeytingAlgebra.imp x y) (HeytingAlgebra.imp w y) := by
  rw [heyting_adj]
  -- w∧(x→y) ≤ x∧(x→y) ≤ y
  exact subobject_le_trans (meet_mono_left h) (heyting_mp x y)

end HeytingLaws

/-! ## §1.723 Locale

  A LOCALE is a complete lattice in which finite meets distribute over
  arbitrary joins: x ∧ (⨆ S) = ⨆ {x ∧ s | s ∈ S}  (§1.723).
  Every locale is a Heyting algebra. -/

/-- A LOCALE: locally complete lattice with meet distributing over
    arbitrary joins (§1.723). -/
class Locale (𝒞 : Type u) [Cat.{v} 𝒞] [HasImages 𝒞]
    extends LocallyComplete 𝒞 where
  /-- Binary meet (∧). -/
  meet : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject 𝒞 A
  /-- meet_le_left: x∧y ≤ x. -/
  meet_le_left  : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject.le (meet x y) x
  /-- meet_le_right: x∧y ≤ y. -/
  meet_le_right : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject.le (meet x y) y
  /-- le_meet: greatest lower bound. -/
  le_meet : ∀ {A : 𝒞} (x y z : Subobject 𝒞 A),
    Subobject.le z x → Subobject.le z y → Subobject.le z (meet x y)
  /-- meet distributes over arbitrary joins:
      x ∧ sup S = sup { x ∧ s | s ∈ S }. -/
  meet_sup_distrib : ∀ {A : 𝒞} (x : Subobject 𝒞 A) (S : Subobject 𝒞 A → Prop),
    meet x (LocallyComplete.sup S) =
    LocallyComplete.sup (fun s => ∃ t, S t ∧ s = meet x t)

/-- Every locale is a Heyting algebra (§1.723):
    define x → y = sup {z | x∧z ≤ y}. -/
noncomputable def locale_is_heyting [HasImages 𝒞] [Locale 𝒞] :
    HeytingAlgebra 𝒞 where
  toHasSubobjectUnions := {
    union := fun S T => LocallyComplete.sup (fun U => U = S ∨ U = T)
    union_left := fun S T =>
      LocallyComplete.sup_upper _ S (Or.inl rfl)
    union_right := fun S T =>
      LocallyComplete.sup_upper _ T (Or.inr rfl)
    union_min := fun S T U hS hT =>
      LocallyComplete.sup_least _ U
        (fun s hs => hs.elim (fun h => h ▸ hS) (fun h => h ▸ hT))
  }
  meet := Locale.meet
  meet_le_left  := Locale.meet_le_left
  meet_le_right := Locale.meet_le_right
  le_meet       := Locale.le_meet
  imp := fun x y => LocallyComplete.sup (fun z => Subobject.le (Locale.meet x z) y)
  adjunction := fun x y z => by
    constructor
    · -- z ≤ sup{w | x∧w ≤ y} → x∧z ≤ y; use meet_sup_distrib
      intro hz
      have h1 : Subobject.le (Locale.meet x z)
                    (Locale.meet x (LocallyComplete.sup fun w => Subobject.le (Locale.meet x w) y)) :=
        Locale.le_meet _ _ _ (Locale.meet_le_left _ _)
          (subobject_le_trans (Locale.meet_le_right _ _) hz)
      have h2 := Locale.meet_sup_distrib x (fun w => Subobject.le (Locale.meet x w) y)
      have h3 : Subobject.le
          (LocallyComplete.sup (fun s => ∃ t, Subobject.le (Locale.meet x t) y ∧ s = Locale.meet x t)) y :=
        LocallyComplete.sup_least _ y (fun s ⟨t, ht, hs⟩ => hs ▸ ht)
      exact subobject_le_trans (h2 ▸ h1) h3
    · -- x∧z ≤ y → z ≤ sup{w | x∧w ≤ y}  (z witnesses itself)
      intro hxz; exact LocallyComplete.sup_upper _ z hxz

/-! ## §1.724 Double-arrow (biimplication)

  Define x ⟺ y = (x→y) ∧ (y→x).  The book characterizes it by
  the double-Horn sentence: z ≤ x⟺y iff z∧x = z∧y  (§1.724).
  Properties: commutative, unit is 1, every element is its own inverse
  (x⟺x = 1), and x∧(x⟺y) = x∧y. -/

/-- Double-arrow: x ⟺ y = (x→y) ∧ (y→x)  (§1.724). -/
def hiff [HasImages 𝒞] [HeytingAlgebra 𝒞] {A : 𝒞}
    (x y : Subobject 𝒞 A) : Subobject 𝒞 A :=
  HeytingAlgebra.meet (HeytingAlgebra.imp x y) (HeytingAlgebra.imp y x)

section HiffLaws

variable [HasImages 𝒞] [HeytingAlgebra 𝒞] {A : 𝒞}

/-- (§1.724) Double-arrow is commutative: x⟺y ≤ y⟺x. -/
theorem hiff_comm_le (x y : Subobject 𝒞 A) :
    Subobject.le (hiff x y) (hiff y x) := by
  unfold hiff
  exact HeytingAlgebra.le_meet _ _ _
    (HeytingAlgebra.meet_le_right _ _)
    (HeytingAlgebra.meet_le_left _ _)

/-- (§1.724) x∧(x⟺y) ≤ x∧y.
    Key step: x∧(x⟺y) ≤ x∧(x→y) and x∧(x→y) ≤ y by modus ponens. -/
theorem meet_hiff_le (x y : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet x (hiff x y))
                 (HeytingAlgebra.meet x y) := by
  unfold hiff
  -- x∧((x→y)∧(y→x)) ≤ x∧(x→y) by meet_le_left
  have h1 : Subobject.le (HeytingAlgebra.meet x
      (HeytingAlgebra.meet (HeytingAlgebra.imp x y) (HeytingAlgebra.imp y x)))
      (HeytingAlgebra.meet x (HeytingAlgebra.imp x y)) :=
    HeytingAlgebra.le_meet _ _ _
      (HeytingAlgebra.meet_le_left _ _)
      (subobject_le_trans (HeytingAlgebra.meet_le_right _ _)
        (HeytingAlgebra.meet_le_left _ _))
  -- x∧(x→y) ≤ y by modus ponens
  have h2 : Subobject.le (HeytingAlgebra.meet x (HeytingAlgebra.imp x y)) y :=
    heyting_mp x y
  exact HeytingAlgebra.le_meet _ _ _
    (HeytingAlgebra.meet_le_left _ _)
    (subobject_le_trans h1 h2)

end HiffLaws

/-! ## §1.727 Negation

  Define ¬x = x → 0 (§1.727).  ¬x is the largest element disjoint from x.
  Laws: ¬(x∨y) = ¬x∧¬y, ¬1=0, ¬0=1, x ≤ ¬¬x, ¬x = ¬¬¬x,
        x ≤ y → ¬y ≤ ¬x.  Double negation preserves meets. -/

/-- Negation in a Heyting algebra with a bottom element: ¬x = x → ⊥ (§1.727). -/
def hneg [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) : Subobject 𝒞 A :=
  HeytingAlgebra.imp x (PreLogos.bottom A)

/-- Characterization: z ≤ ¬x ↔ x∧z ≤ ⊥  (§1.727). -/
theorem hneg_adj [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x z : Subobject 𝒞 A) :
    Subobject.le z (hneg x) ↔
    Subobject.le (HeytingAlgebra.meet x z) (PreLogos.bottom A) :=
  HeytingAlgebra.adjunction x (PreLogos.bottom A) z

/-- x∧¬x ≤ ⊥  (disjointness of x and its negation). -/
theorem meet_neg_le_bot [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet x (hneg x)) (PreLogos.bottom A) :=
  heyting_mp x (PreLogos.bottom A)

/-- x ≤ ¬¬x  (§1.727).
    Proof: apply hneg_adj for ¬¬x; need (¬x)∧x ≤ ⊥, which is meet_neg_le_bot + comm. -/
theorem le_double_neg [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le x (hneg (hneg x)) := by
  rw [hneg_adj]
  -- Need: (¬x)∧x ≤ ⊥.  We have x∧(¬x) ≤ ⊥; use commutativity of meet.
  exact subobject_le_trans (meet_comm_le (hneg x) x) (meet_neg_le_bot x)

/-- Negation is contravariant: x ≤ y → ¬y ≤ ¬x  (§1.727).
    Proof: ¬y ≤ ¬x iff x∧¬y ≤ ⊥; since x ≤ y, x∧¬y ≤ y∧¬y ≤ ⊥. -/
theorem hneg_antitone [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} {x y : Subobject 𝒞 A} (h : Subobject.le x y) :
    Subobject.le (hneg y) (hneg x) := by
  rw [hneg_adj]
  -- x∧(¬y) ≤ y∧(¬y) ≤ ⊥
  exact subobject_le_trans (meet_mono_left h) (meet_neg_le_bot y)

/-- ¬x ≤ ¬¬¬x  (from le_double_neg applied to ¬x). -/
theorem neg_le_triple_neg [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le (hneg x) (hneg (hneg (hneg x))) :=
  le_double_neg (hneg x)

/-- ¬¬¬x ≤ ¬x  (apply hneg_antitone to x ≤ ¬¬x). -/
theorem triple_neg_le_neg [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le (hneg (hneg (hneg x))) (hneg x) :=
  hneg_antitone (le_double_neg x)

/-- ¬¬¬x and ¬x are mutually ≤ (book's ¬¬¬x = ¬x, §1.727).
    In the subobject setting we get mutual le; propositional eq needs extensionality. -/
theorem triple_neg_equiv [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le (hneg (hneg (hneg x))) (hneg x) ∧
    Subobject.le (hneg x) (hneg (hneg (hneg x))) :=
  ⟨triple_neg_le_neg x, neg_le_triple_neg x⟩

/-- De Morgan: ¬(x∨y) ≤ ¬x∧¬y  (§1.726/§1.727).
    Proof: ¬(x∨y) ≤ ¬x because x ≤ x∨y; similarly for y; use le_meet. -/
theorem hneg_union_le [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x y : Subobject 𝒞 A) :
    Subobject.le (hneg (HasSubobjectUnions.union x y))
                 (HeytingAlgebra.meet (hneg x) (hneg y)) :=
  HeytingAlgebra.le_meet _ _ _
    (hneg_antitone (HasSubobjectUnions.union_left x y))
    (hneg_antitone (HasSubobjectUnions.union_right x y))

/-- Double negation preserves meets: ¬¬(x∧y) ≤ ¬¬x∧¬¬y  (§1.727, ≤ direction).
    Proof: x∧y ≤ x and x∧y ≤ y give ¬¬(x∧y) ≤ ¬¬x and ¬¬(x∧y) ≤ ¬¬y by hneg_antitone.
    The reverse inequality ¬¬x∧¬¬y ≤ ¬¬(x∧y) is `double_neg_meet_ge` (proven below). -/
theorem double_neg_meet_le [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x y : Subobject 𝒞 A) :
    Subobject.le (hneg (hneg (HeytingAlgebra.meet x y)))
                 (HeytingAlgebra.meet (hneg (hneg x)) (hneg (hneg y))) := by
  -- ¬¬(x∧y) ≤ ¬¬x: apply hneg_antitone twice to x∧y ≤ x
  apply HeytingAlgebra.le_meet
  · exact hneg_antitone (hneg_antitone (HeytingAlgebra.meet_le_left x y))
  · exact hneg_antitone (hneg_antitone (HeytingAlgebra.meet_le_right x y))

/-- ¬¬x∧¬¬y ≤ ¬¬(x∧y)  (the harder direction, §1.727).
    Book argument: x∧y∧¬(x∧y)=0 → ¬(x∧y)∧x ≤ ¬y → ¬¬y ≤ ¬(¬(x∧y)∧x)
    → ¬(x∧y)∧¬¬y ≤ ¬x → ¬¬x ≤ ¬(¬(x∧y)∧¬¬y) → ¬(x∧y)∧¬¬x∧¬¬y ≤ 0. -/
theorem double_neg_meet_ge [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x y : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet (hneg (hneg x)) (hneg (hneg y)))
                 (hneg (hneg (HeytingAlgebra.meet x y))) := by
  -- A: y ∧ (¬(x∧y) ∧ x) ≤ ⊥
  have hA : Subobject.le
      (HeytingAlgebra.meet y (HeytingAlgebra.meet (hneg (HeytingAlgebra.meet x y)) x))
      (PreLogos.bottom A) := by
    apply subobject_le_trans _ (meet_neg_le_bot (HeytingAlgebra.meet x y))
    apply HeytingAlgebra.le_meet
    · apply subobject_le_trans _ (meet_comm_le y x)
      exact HeytingAlgebra.le_meet _ _ _ (HeytingAlgebra.meet_le_left _ _)
        (subobject_le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_right _ _))
    · exact subobject_le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_left _ _)
  -- B: ¬(x∧y)∧x ≤ ¬y; D: x∧(¬(x∧y)∧¬¬y) ≤ ⊥; E: ¬(x∧y)∧¬¬y ≤ ¬x; F: ¬¬x ≤ ¬(¬(x∧y)∧¬¬y)
  have hB := (hneg_adj y _).mpr hA
  have hD : Subobject.le
      (HeytingAlgebra.meet x (HeytingAlgebra.meet (hneg (HeytingAlgebra.meet x y)) (hneg (hneg y))))
      (PreLogos.bottom A) := by
    apply subobject_le_trans _ (meet_neg_le_bot (hneg y))
    apply subobject_le_trans (HeytingAlgebra.le_meet _ _ _
      (HeytingAlgebra.le_meet _ _ _
        (subobject_le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_left _ _))
        (HeytingAlgebra.meet_le_left _ _))
      (subobject_le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_right _ _)))
    exact meet_mono_left hB
  have hE := (hneg_adj x _).mpr hD
  have hF := hneg_antitone hE
  -- Conclude: ¬(x∧y) ∧ (¬¬x ∧ ¬¬y) ≤ ⊥, i.e. ¬¬x∧¬¬y ≤ ¬¬(x∧y)
  apply (hneg_adj (hneg (HeytingAlgebra.meet x y)) _).mpr
  apply subobject_le_trans _ (subobject_le_trans
    (meet_comm_le
      (hneg (HeytingAlgebra.meet (hneg (HeytingAlgebra.meet x y)) (hneg (hneg y))))
      (HeytingAlgebra.meet (hneg (HeytingAlgebra.meet x y)) (hneg (hneg y))))
    (meet_neg_le_bot (HeytingAlgebra.meet (hneg (HeytingAlgebra.meet x y)) (hneg (hneg y)))))
  apply HeytingAlgebra.le_meet
  · exact subobject_le_trans
      (subobject_le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_left _ _))
      hF
  · exact HeytingAlgebra.le_meet _ _ _
      (HeytingAlgebra.meet_le_left _ _)
      (subobject_le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_right _ _))

/-- Meet distributes over union: z∧(a∨b) ≤ (z∧a)∨(z∧b)  (§1.726).
    A Heyting algebra is distributive because meet has a right adjoint (imp):
    by the adjunction this reduces to a∨b ≤ z→((z∧a)∨(z∧b)), and each
    disjunct a, b lands there since z∧a, z∧b ≤ (z∧a)∨(z∧b).  The reverse
    inequality is automatic in any lattice, so this is genuine distributivity. -/
theorem meet_union_le_distrib [HasImages 𝒞] [HeytingAlgebra 𝒞]
    {A : 𝒞} (z a b : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet z (HasSubobjectUnions.union a b))
                 (HasSubobjectUnions.union (HeytingAlgebra.meet z a)
                                           (HeytingAlgebra.meet z b)) := by
  -- z∧(a∨b) ≤ W  ↔  a∨b ≤ z→W, with W = (z∧a)∨(z∧b)
  rw [← HeytingAlgebra.adjunction]
  apply HasSubobjectUnions.union_min
  · -- a ≤ z→W  ↔  z∧a ≤ W; and z∧a ≤ (z∧a)∨(z∧b)
    rw [HeytingAlgebra.adjunction]; exact HasSubobjectUnions.union_left _ _
  · rw [HeytingAlgebra.adjunction]; exact HasSubobjectUnions.union_right _ _

/-! ## §1.728 Law of excluded middle

  If we adjoin x ∨ ¬x = 1 (law of excluded middle), every element has a
  complement, and since Heyting algebras are distributive lattices, we get
  a Boolean algebra (§1.728).
  Alternatively: x = ¬¬x suffices: x ∨ ¬x = ¬¬(x ∨ ¬x) = ¬(¬x ∧ ¬¬x) = ¬0 = 1. -/

/-- x∧¬x ≤ ⊥ iff (¬x) disjoint from x.
    Under EM, ¬x is a complement of x (§1.728). -/
theorem em_disjoint [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet x (hneg x)) (PreLogos.bottom A) :=
  meet_neg_le_bot x

/-- Every subobject is ≤ the entire (top) subobject. -/
theorem le_entire {A : 𝒞} (S : Subobject 𝒞 A) : Subobject.le S (Subobject.entire A) :=
  ⟨S.arr, by simp [Subobject.entire, Cat.comp_id]⟩

/-- Under excluded middle, double negation is the identity: ¬¬x ≤ x
    (the converse `x ≤ ¬¬x` is `le_double_neg`, so ¬¬x = x).  (§1.728)
    Proof (Boolean): ¬¬x = ¬¬x ∧ 1 = ¬¬x ∧ (x∨¬x) ≤ (¬¬x∧x) ∨ (¬¬x∧¬x) ≤ x∨⊥ = x,
    using meet-over-union distributivity and ¬¬x∧¬x ≤ ⊥. -/
theorem double_neg_le_of_em [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A)
    (hem : Subobject.le (Subobject.entire A)
            (HasSubobjectUnions.union x (hneg x))) :
    Subobject.le (hneg (hneg x)) x := by
  -- ¬¬x ≤ ¬¬x ∧ (x∨¬x)
  have step1 : Subobject.le (hneg (hneg x))
      (HeytingAlgebra.meet (hneg (hneg x)) (HasSubobjectUnions.union x (hneg x))) :=
    HeytingAlgebra.le_meet _ _ _ (subobject_le_refl _)
      (subobject_le_trans (le_entire _) hem)
  -- ¬¬x ∧ (x∨¬x) ≤ (¬¬x∧x) ∨ (¬¬x∧¬x)
  have step2 := meet_union_le_distrib (hneg (hneg x)) x (hneg x)
  -- (¬¬x∧x) ∨ (¬¬x∧¬x) ≤ x
  have step3 : Subobject.le
      (HasSubobjectUnions.union (HeytingAlgebra.meet (hneg (hneg x)) x)
                                (HeytingAlgebra.meet (hneg (hneg x)) (hneg x))) x :=
    HasSubobjectUnions.union_min _ _ _
      (HeytingAlgebra.meet_le_right _ _)
      -- ¬¬x∧¬x ≤ ¬x∧¬¬x ≤ ⊥ ≤ x
      (subobject_le_trans (meet_comm_le _ _)
        (subobject_le_trans (meet_neg_le_bot (hneg x)) (PreLogos.bottom_min x)))
  exact subobject_le_trans step1 (subobject_le_trans step2 step3)

/-- Excluded middle ⇒ double negation is the identity (§1.728).
    Records both halves: `x ≤ ¬¬x` (always) and `¬¬x ≤ x` (under EM). -/
theorem double_neg_eq_self [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A)
    (hem : Subobject.le (Subobject.entire A)
            (HasSubobjectUnions.union x (hneg x))) :
    Subobject.le (hneg (hneg x)) x ∧ Subobject.le x (hneg (hneg x)) :=
  ⟨double_neg_le_of_em x hem, le_double_neg x⟩

/-- In a Heyting algebra (with bottom), excluded middle x∨¬x = 1 implies
    x has a complement in the sense of §1.631.  (§1.728)
    Here "complement" is (¬x), with x∧¬x = ⊥ and x∨¬x = 1. -/
theorem em_implies_complemented [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A)
    (hem : Subobject.le (Subobject.entire A)
            (HasSubobjectUnions.union x (hneg x))) :
    ∃ (nx : Subobject 𝒞 A),
      (∀ S, Subobject.le S x → Subobject.le S nx →
        Subobject.le S (PreLogos.bottom A)) ∧
      Subobject.le (Subobject.entire A) (HasSubobjectUnions.union x nx) :=
  ⟨hneg x,
    fun S hSx hSnx =>
      subobject_le_trans
        (HeytingAlgebra.le_meet _ _ _ hSx hSnx)
        (meet_neg_le_bot x),
    hem⟩

/-! ## §1.73 Filter ℱ(T) and quotient A/ℱ

  For a representation T: A → B of logoi, ℱ(T) = {U⊆1 | T(U)=1}.
  ℱ(T) is a filter.  For any filter ℱ, there's a quotient logos A/ℱ
  with a representation T_ℱ: A → A/ℱ (§1.731). -/

/-- The filter of a representation: subterminators sent to 1. -/
def repFilter {𝒟 : Type u} [Cat.{v} 𝒟] [Logos 𝒞] [Logos 𝒟]
    (T : 𝒞 → 𝒟) [Functor T] : (Subobject 𝒞 one) → Prop :=
  λ U => @Isomorphic 𝒟 _ (T U.dom) one

/-! ### §1.73 the double-sharp filter bridge `A' = A  ↔  pA##(A') = 1`

  The book's §1.73 argument hinges on a *pure* property of the right-adjoint
  pA## = `rightAdj (term A)`, with no functor `T` involved:

    *"Given A' ⊆ A, consider pA##(A') ⊆ 1.  Note that A' = A iff pA##(A') = 1."*

  We formalize this fact in full.  It is the half of §1.73 that the repo's
  infrastructure (`HasRightAdjointImage.rightAdj`, `InverseImage`, `IsEntire`)
  supports faithfully; the bridge to a functor `T`'s action on subobjects
  (`T(A') ⊊ T(A) ↔ pA##(A') ∉ ℱ(T)`, hence the full `faithful_iff_trivial_filter`)
  still needs a `LogosMap` carrying `T`'s action on `Sub`, recorded MISSING below.

  First a reusable lemma: a subobject is entire iff the top subobject factors
  through it (a split-epi-and-mono is iso). -/

/-- A subobject `S ↣ A` is entire iff the entire subobject is `≤` it, i.e. iff
    its mono `S.arr` is split epic (and, being monic, then iso). -/
theorem isEntire_iff_entire_le {A : 𝒞} (S : Subobject 𝒞 A) :
    Subobject.IsEntire S ↔ Subobject.le (Subobject.entire A) S := by
  constructor
  · -- iso ⇒ its inverse witnesses entire ≤ S
    rintro ⟨g, _h1, h2⟩
    exact ⟨g, by simpa [Subobject.entire] using h2⟩
  · -- entire ≤ S gives a section h of S.arr; mono cancels to make h a 2-sided inverse
    rintro ⟨h, hsec⟩
    have hsec' : h ≫ S.arr = Cat.id A := by simpa [Subobject.entire] using hsec
    refine ⟨h, ?_, hsec'⟩
    -- (S.arr ≫ h) ≫ S.arr = id ≫ S.arr, cancel the mono S.arr on the right
    apply S.monic
    rw [Cat.assoc, hsec', Cat.comp_id, Cat.id_comp]

/-- The inverse image of the top subobject is the top subobject:
    `f#(1_B) = 1_A` (each side `≤` the other).  The `entire B ≤` direction is
    trivial; the other uses that `f` itself lifts through the pullback cone of
    `f` against `id_B`. -/
theorem entire_le_inverseImage_entire [HasPullbacks 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Subobject.le (Subobject.entire A) (InverseImage f (Subobject.entire B)) := by
  -- the pullback of (f, id_B); lift the cone ⟨A, id_A, f⟩ through it
  let pb := HasPullbacks.has f (Subobject.entire B).arr
  let c : Cone f (Subobject.entire B).arr :=
    ⟨A, Cat.id A, f, by simp [Subobject.entire, Cat.id_comp, Cat.comp_id]⟩
  -- the π₁-leg (the InverseImage's arrow) of this lift is id_A
  exact ⟨pb.lift c, by simpa [InverseImage, Subobject.entire] using pb.lift_fst c⟩

/-- **§1.73 double-sharp bridge.** For any object `A` in a logos and any
    subobject `A' ⊆ A`, writing `pA = term A : A → 1` for the unique map to the
    terminator and `pA## = rightAdj (term A)`:

        `A' = A   ↔   pA##(A') = 1`.

    (Book §1.73: *"A' = A iff pA##(A') = 1."*)  Proof: `pA##(A')` is entire iff
    `1 ≤ pA##(A')`, iff (adjunction) `pA#(1) ≤ A'`, and `pA#(1) = 1_A` is the top
    of `Sub A`, so this says `1_A ≤ A'`, iff `A'` is entire. -/
theorem isEntire_rightAdj_term_iff [Logos 𝒞] {A : 𝒞} (A' : Subobject 𝒞 A) :
    Subobject.IsEntire (HasRightAdjointImage.rightAdj (term A) A') ↔
    Subobject.IsEntire A' := by
  rw [isEntire_iff_entire_le, isEntire_iff_entire_le]
  -- entire 1 ≤ pA##(A')  ↔  pA#(entire 1) ≤ A'  ↔  entire A ≤ A'
  rw [← HasRightAdjointImage.adjunction (term A) (Subobject.entire one) A']
  constructor
  · -- entire A ≤ pA#(entire 1) ≤ A'
    intro h
    exact subobject_le_trans (entire_le_inverseImage_entire (term A)) h
  · -- pA#(entire 1) ≤ entire A ≤ A'
    intro h
    exact subobject_le_trans (le_entire _) h

-- §1.73 (MISSING, narrowed): `faithful_iff_trivial_filter`.
-- With the double-sharp bridge above proven, the only remaining gap is the
-- functor side.  The book reads: *"T(A') ⊆ T(A) iff pA##(A') ∈ ℱ(T)"*, hence
--   T faithful  ⟺  T preserves properness of subobjects  (§1.453)
--               ⟺  ℱ(T) = {1}  (via the bridge `isEntire_rightAdj_term_iff`).
-- The repo's `Functor`/`Faithful` (S1_33) carries only T's action on objects and
-- morphisms; it has NO action `T : Sub A → Sub (T A)` on subobjects, so the
-- premise *"T preserves/reflects properness of subobjects"* and the value
-- `T(A') : Sub (T A)` cannot even be written.  `repFilter` above only inspects
-- `T U.dom` (an object), not a subobject of `T one`.  Stating
-- `faithful_iff_trivial_filter` faithfully therefore requires a `LogosMap T`
-- structure (a CartesianFunctor preserving images, giving `T : Sub A → Sub (T A)`
-- compatibly with `pA##`).  That infra is not in the repo, so the full theorem
-- stays MISSING — but its mathematical core (the pA## ↔ entire bridge) is now
-- proven above.  Per the integrity rule we emit no Sorry on the unstatable form.

/-! ## §1.733 Coprime and Connected

  An object A in a pre-logos is COPRIME if the functor (A,-) preserves
  finite unions, i.e. any finite collection of subobjects of A whose union
  is A must already contain A (§1.733).

  A is CONNECTED if it has exactly two complemented subobjects (§1.733). -/

/-- A is COPRIME (§1.733): the functor (A,-) preserves finite unions,
    meaning any two subobjects whose union covers A must include A itself
    (i.e. one of them must be entire). -/
def Coprime [HasImages 𝒞] [HasSubobjectUnions 𝒞] (A : 𝒞) : Prop :=
  ∀ (U V : Subobject 𝒞 A),
    Subobject.le (Subobject.entire A) (HasSubobjectUnions.union U V) →
    Subobject.IsEntire U ∨ Subobject.IsEntire V

/-- A is CONNECTED (§1.733): it has exactly two complemented subobjects,
    i.e. the only complemented subobjects are ⊥ (bottom) and A (entire). -/
def Connected [HasImages 𝒞] [PreLogos 𝒞] (A : 𝒞) : Prop :=
  ∀ (U : Subobject 𝒞 A),
    IsComplemented U → Subobject.IsEntire U ∨ U = PreLogos.bottom A

/-- A FOCAL LOGOS (§1.733): its terminator is a coprime projective.
    Equivalently, r = (1,-) is a representation of pre-logoi. -/
class FocalLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends Logos 𝒞 where
  one_coprime    : Coprime (𝒞 := 𝒞) (one)
  one_projective : Projective (𝒞 := 𝒞) (one)

/-! ## §1.722 Poset is a logos iff Heyting algebra

  "A poset, when viewed as a category, is a logos iff it is a Heyting algebra
  (more precisely, iff it is the poset underlying a [necessarily unique] Heyting algebra)."
  (Freyd §1.722, combining §1.721 and §1.613.)

  The infrastructure for this requires a concrete model of "poset viewed as a category"
  (a thin category) together with the identification of its logos structure with a Heyting
  algebra on the carrier.  That model is not built in this repo (there is no thin-category
  constructor); the statement is recorded below as a book reference. -/

-- BOOK §1.722: A poset, when viewed as a category, is a logos iff it is a Heyting algebra
-- (more precisely, iff it is the poset underlying a [necessarily unique] Heyting algebra).

/-! ## §1.733 Positive pre-logos focal iff connected projective terminator

  "A positive pre-logos is focal iff its terminator is a connected projective."
  (Freyd §1.733; book proof: projective 1 ⟹ 1 is a representation of regular cats,
  so it preserves unions iff it preserves disjoint unions [1.625]; connected = exactly
  two complemented subobjects.) -/

/-- §1.733: A positive pre-logos is FOCAL iff its terminator is a CONNECTED PROJECTIVE.
    (⟹) `FocalLogos` gives `one_coprime` and `one_projective`; coprime + connected follow.
    (⟸) Connectedness gives coprimeness via §1.625 (projective 1 preserves disjoint unions).
    Needs `HasDisjointUnions` / §1.625 (projective 1 preserves disjoint ⟹ binary unions)
    not yet in the repo; stated as a sorry-stub. -/
theorem focal_iff_connected_projective
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PreLogos 𝒞] :
    Nonempty (FocalLogos 𝒞) ↔ (Connected (𝒞 := 𝒞) one ∧ Projective (𝒞 := 𝒞) one) := by
  sorry

-- §1.734 FOCAL REPRESENTATION THEOREM (every small logos has a collectively faithful
-- family of focal representations) and §1.74 GEOMETRIC REPRESENTATION THEOREM (countable
-- logos faithfully represented in a power of sheaves on ℝ) are recorded MISSING in
-- S1_72.md: stating them faithfully needs the focal-representation / sheaf-on-ℝ
-- infrastructure not yet in the repo. Per the integrity rule we do NOT emit vacuous
-- `: True` stubs for them.

-- BOOK §1.734: Any small (positive) logos has a small, collectively faithful family of
-- focal representations.

-- BOOK §1.734: A logos may be faithfully represented in a single focal logos iff its
-- terminator is coprime.

-- BOOK §1.735: Any countable (positive) logos has a countable, collectively faithful
-- family of focal representations.

-- BOOK §1.735: Any countable logos with a coprime terminator may be faithfully
-- represented in a countable focal logos.

-- BOOK §1.72(10): Every Heyting algebra can be covered by a Heyting algebra for which the
-- functor T = (1,_) is a representation of bicartesian categories.
-- (Via the scone construction; §1.72(11): a free Heyting algebra is a retract of its scone.)

end Freyd
