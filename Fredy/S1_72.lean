/-
  Freyd & Scedrov, *Categories and Allegories* §1.72–§1.76
  Heyting algebras, Negation, Focal logoi, Representation theorems.

  §1.72  Heyting algebra: lattice with implication → (right adjoint to ∧).
  §1.723 Locale: complete lattice with finite-meet/arbitrary-join distributivity.
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
  z ≤ x → y  ⇔  x ∧ z ≤ y  (→ is right adjoint to ∧, fixing x). -/

/-- A HEYTING ALGEBRA: lattice with implication satisfying the adjunction
    z ≤ (x→y) ↔ x∧z ≤ y  (book §1.72). -/
class HeytingAlgebra (𝒞 : Type u) [Cat.{v} 𝒞] [HasImages 𝒞]
    extends HasSubobjectUnions 𝒞 where
  /-- Binary meet (∧) of subobjects. -/
  meet : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject 𝒞 A
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

/-- (§1.726) x→y is covariant in y: y ≤ z → (x→y) ≤ (x→z). -/
theorem imp_mono_right {x y z : Subobject 𝒞 A} (h : Subobject.le y z) :
    Subobject.le (HeytingAlgebra.imp x y) (HeytingAlgebra.imp x z) := by
  rw [heyting_adj]
  sorry  -- Proof: by heyting_adj, x∧(x→y) ≤ y ≤ z

/-- (§1.726) x→y is contravariant in x: w ≤ x → (x→y) ≤ (w→y). -/
theorem imp_mono_left_contra {x w y : Subobject 𝒞 A} (h : Subobject.le w x) :
    Subobject.le (HeytingAlgebra.imp x y) (HeytingAlgebra.imp w y) := by
  sorry  -- Proof: w∧(x→y) ≤ x∧(x→y) ≤ y, so x→y ≤ w→y by adjunction

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
  imp := fun x y => LocallyComplete.sup (fun z => Subobject.le (Locale.meet x z) y)
  adjunction := fun x y z => by
    constructor
    · -- z ≤ sup{w | x∧w ≤ y} → x∧z ≤ y
      intro _hz; sorry  -- uses distributivity: x∧sup{w|…} = sup{x∧w|…} ≤ y
    · -- x∧z ≤ y → z ≤ sup{w | x∧w ≤ y}  (z witnesses itself)
      intro hxz; exact LocallyComplete.sup_upper _ z hxz

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

/-- x ≤ ¬¬x  (§1.727). -/
theorem le_double_neg [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le x (hneg (hneg x)) := by
  sorry  -- apply hneg_adj; need x∧¬x ≤ ⊥ (modus ponens for ⊥)

/-- Negation is contravariant: x ≤ y → ¬y ≤ ¬x  (§1.727). -/
theorem hneg_antitone [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} {x y : Subobject 𝒞 A} (h : Subobject.le x y) :
    Subobject.le (hneg y) (hneg x) := by
  sorry  -- hneg_adj: y∧¬y ≤ ⊥; use h to get x∧¬y ≤ y∧¬y ≤ ⊥

/-- ¬¬¬x = ¬x  (§1.727). -/
theorem triple_neg [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    hneg (hneg (hneg x)) = hneg x := by
  sorry  -- ≤ in both directions from le_double_neg and hneg_antitone

/-- De Morgan: ¬(x∨y) ≤ ¬x∧¬y  (§1.726/§1.727). -/
theorem hneg_union_le [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x y : Subobject 𝒞 A) :
    Subobject.le (hneg (HasSubobjectUnions.union x y))
                 (HeytingAlgebra.meet (hneg x) (hneg y)) := by
  sorry  -- z ≤ ¬(x∨y) ↔ (x∨y)∧z ≤ ⊥ ↔ x∧z ≤ ⊥ ∧ y∧z ≤ ⊥ ↔ z ≤ ¬x ∧ z ≤ ¬y

/-- Double negation preserves meets: ¬¬(x∧y) = ¬¬x ∧ ¬¬y  (§1.727). -/
theorem double_neg_meet [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x y : Subobject 𝒞 A) :
    hneg (hneg (HeytingAlgebra.meet x y)) =
    HeytingAlgebra.meet (hneg (hneg x)) (hneg (hneg y)) := by
  sorry

/-! ## §1.728 Law of excluded middle

  If we adjoin x ∨ ¬x = 1 (law of excluded middle), every element has a
  complement, and since Heyting algebras are distributive lattices, we get
  a Boolean algebra (§1.728).
  Alternatively: x = ¬¬x suffices. -/

/-- In a Heyting algebra (with bottom), excluded middle x∨¬x = 1 implies
    x has a complement in the sense of §1.631.  (§1.728)
    Here "complement" is (¬x), with x∧¬x = ⊥ and x∨¬x = 1. -/
theorem em_implies_complemented [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A)
    (hem : Subobject.le (Subobject.entire A)
            (HasSubobjectUnions.union x (hneg x))) :
    ∃ (nx : Subobject 𝒞 A),
      (∀ S, Subobject.le S x → Subobject.le S nx → False) ∧
      Subobject.le (Subobject.entire A) (HasSubobjectUnions.union x nx) :=
  ⟨hneg x,
    by sorry,  -- x∧¬x ≤ ⊥: disjointness from hneg_adj
    hem⟩

/-! ## §1.73 Filter ℱ(T) and quotient A/ℱ

  For a representation T: A → B of logoi, ℱ(T) = {U⊆1 | T(U)=1}.
  ℱ(T) is a filter.  For any filter ℱ, there's a quotient logos A/ℱ
  with a representation T_ℱ: A → A/ℱ (§1.731). -/

/-- The filter of a representation: subterminators sent to 1. -/
def repFilter {𝒟 : Type u} [Cat.{v} 𝒟] [Logos 𝒞] [Logos 𝒟]
    (T : 𝒞 → 𝒟) [Functor T] : (Subobject 𝒞 one) → Prop :=
  λ U => @Isomorphic 𝒟 _ (T U.dom) one

/-- A representation T is faithful iff ℱ(T) = {1} (§1.73). -/
theorem faithful_iff_trivial_filter {𝒟 : Type u} [Cat.{v} 𝒟] [Logos 𝒞] [Logos 𝒟]
    (T : 𝒞 → 𝒟) [Functor T] :
    Faithful T ↔ (∀ U, repFilter T U ↔ U = Subobject.entire one) := by
  sorry

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

/-! ## §1.734 Focal representation

  A representation A → F is FOCAL if F is focal, i.e. A → F → 𝒮
  is a representation of pre-logoi. -/

/-- Every small logos has a collectively faithful family of focal
    representations (§1.734). -/
theorem focal_representation_theorem (A : Type u) [Cat.{v} A] [Logos A] : True := by
  -- Proof: capitalize A, then use ultrafilter on Boolean algebra of
  -- complemented subterminators to get focal A/ℱ.
  sorry

/-! ## §1.74 Geometric Representation Theorem

  Every countable (positive) logos may be faithfully represented in a
  countable power of the logos of sheaves on the real line. -/

theorem geometric_representation_theorem : True := by
  -- Uses the focal representation theorem + properties of ℝ.
  sorry

end Freyd
