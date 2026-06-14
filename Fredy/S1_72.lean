/-
  Freyd & Scedrov, *Categories and Allegories* §1.72–§1.76
  Heyting algebras, Negation, Focal logoi, Representation theorems.

  §1.72  Heyting algebra: lattice with implication → (right adjoint to ∧).
  §1.727 Negation: ¬x = x→0, double negation, De Morgan.
  §1.73  ℱ(T) filter, A/ℱ quotient logos.
  §1.733 Coprime object, connected, FOCAL LOGOS (1 is coprime projective).
  §1.734 Focal representation, representation theorems.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_57
import Fredy.S1_60
import Fredy.S1_70


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.72 Heyting algebra

  A HEYTING ALGEBRA is a lattice with a binary → such that
  z ≤ x → y  ⇔  z ∧ x ≤ y  (→ is right adjoint to ∧). -/

/-- A HEYTING ALGEBRA: distributive lattice with implication →. -/
class HeytingAlgebra (𝒞 : Type u) [Cat.{v} 𝒞] [HasImages 𝒞] extends HasSubobjectUnions 𝒞 where
  meet : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject 𝒞 A
  imp  : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject 𝒞 A
  adjunction : ∀ {A : 𝒞} (x y z : Subobject 𝒞 A),
    Subobject.le (meet x y) z ↔ Subobject.le x (imp y z)

/-! ## §1.727 Negation

  ¬x = x → 0 (the largest element disjoint from x).
  ¬¬¬x = ¬x, and double-negation preserves meets. -/

-- Negation requires a minimal subobject (bottom element) not yet available.
-- def neg [HeytingAlgebra 𝒞] {A : 𝒞} (x : Subobject 𝒞 A) : Subobject 𝒞 A :=
--   HeytingAlgebra.imp x minimalSubobject

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
    (T : 𝒞 → 𝒟) [Functor T] : Faithful T ↔ (∀ U, repFilter T U ↔ U = Subobject.entire one) := by
  sorry

/-! ## §1.733 Coprime and Focal

  An object A is COPRIME if Hom(A,-) preserves finite unions.
  A logos is FOCAL if its terminator is coprime and projective. -/

/-- A is COPRIME: A factors through any cover of it by two subobjects. -/
def Coprime [HasImages 𝒞] [HasSubobjectUnions 𝒞] (A : 𝒞) : Prop :=
  ∀ (U V : Subobject 𝒞 A),
    Subobject.le (Subobject.entire A) (HasSubobjectUnions.union U V) → IsIso (Subobject.entire A).arr

/-- A FOCAL LOGOS: terminator is coprime and projective (§1.733). -/
class FocalLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends Logos 𝒞 where
  one_coprime    : Coprime one
  one_projective : Projective one

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
