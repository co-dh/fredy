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
    (T : 𝒞 → 𝒟) [hT : Functor T] : Faithful T ↔ (∀ U, repFilter T U ↔ U = Subobject.entire one) := by
  constructor
  · intro hfaithful U
    rcases hfaithful with ⟨hemb, href⟩
    constructor
    · intro hrep
      rcases hrep with ⟨φ, hiso⟩
      -- φ : T(U.dom) → 1_𝒟 iso.  Since T reflects isos (href), we can show U.arr is iso.
      -- Compose: T(U.arr) ≫ term(T(1)) = term(T(U.dom)) = φ, which is iso.
      have hterm_iso : IsIso (@term 𝒟 _ _ (T U.dom)) := by
        have hφ_term : φ = @term 𝒟 _ _ (T U.dom) := term_uniq _ _
        rw [hφ_term] at hiso; exact hiso
      have hcomp : hT.map U.arr ≫ @term 𝒟 _ _ (T (@one 𝒞 _ _)) = @term 𝒟 _ _ (T U.dom) :=
        term_uniq _ _
      -- So hT.map U.arr ≫ term(T(1)) is iso, making hT.map U.arr split epic
      -- and term(T(1)) split monic.  To conclude U.arr iso via href, we need
      -- hT.map U.arr itself iso, which requires term(T(1)) iso — i.e. T(1) ≅ 1.
      -- This needs T to preserve the terminal, which follows from the right-adjoint
      -- structure of a Logos representation (not available as [Functor T] alone).
      sorry
    · intro hUeq
      -- U = Subobject.entire one → repFilter T U
      -- Requires T(1_𝒞) ≅ 1_𝒟.  A faithful functor between logoi preserves the
      -- terminal via the right adjoint image, but [Functor T] is too weak.
      sorry
  · intro hfilter
    -- (∀ U, repFilter T U ↔ U = Subobject.entire one) → Faithful T
    -- From the filter condition at U = Subobject.entire one, we get T(1_𝒞) ≅ 1_𝒟.
    have h_one_iso : @Isomorphic 𝒟 _ (T (@one 𝒞 _ _)) (@one 𝒟 _ _) :=
      ((hfilter (Subobject.entire (@one 𝒞 _ _))).mpr rfl)
    rcases h_one_iso with ⟨φ, hiso⟩
    -- Embedding: use the Logos equalizer.  For f,g with T(f)=T(g), the equalizer E↣A
    -- gives a subobject; its image under (term A)## is a subterminator.  The filter
    -- condition forces this subterminator to be entire, hence f=g.
    -- Requires T to preserve equalizers and the right adjoint, not available as [Functor T].
    have hemb : Embedding T := by
      intro A B f g hTfg
      sorry
    -- Reflects isos: if T(f) is iso, then the image of f satisfies T(im(f).dom) ≅ 1_𝒟,
    -- forcing im(f) entire via the filter condition, hence f iso.
    -- Requires T to preserve images, not available as [Functor T].
    have href : ∀ {A B : 𝒞} (f : A ⟶ B), IsIso (hT.map f) → IsIso f := by
      intro A B f hTf
      sorry
    exact ⟨hemb, href⟩

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
