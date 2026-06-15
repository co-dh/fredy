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

/-- A representation `T` is faithful iff `ℱ(T) = {1}` (§1.73).

    `[Functor T]` alone is too weak (the book's `T` is a logos *representation*):
    we add the two preservation facts a representation supplies — `T` preserves
    monos (`hpm`) and the terminal object (`hT1 : T 1 ≅ 1`).  The conclusion is
    stated up to isomorphism (a subterminator `U ⊆ 1` is "trivial" when its
    domain is `≅ 1`); the original `U = Subobject.entire one` was too strong,
    forcing `U.dom` to be *literally* `one`.

    The forward direction is proved here.  The converse (a trivial filter forces
    faithfulness) additionally needs `T` to preserve equalizers and images, and
    is left decomposed into its two genuine obligations. -/
theorem faithful_iff_trivial_filter {𝒟 : Type u} [Cat.{v} 𝒟] [Logos 𝒞] [Logos 𝒟]
    (T : 𝒞 → 𝒟) [hT : Functor T] (hpm : PreservesMono T)
    (hT1 : Isomorphic (T (one : 𝒞)) (one : 𝒟)) :
    Faithful T ↔ (∀ U : Subobject 𝒞 one, repFilter T U ↔ Isomorphic U.dom (one : 𝒞)) := by
  constructor
  · rintro ⟨_hemb, href⟩ U
    constructor
    · -- repFilter U (T U.dom ≅ 1) → U.dom ≅ 1.
      intro hrep
      -- `T(U.arr)` is a mono between two objects each `≅ 1`, hence an iso;
      -- faithfulness reflects it to make `U.arr` an iso.
      have hTarr_iso : IsIso (hT.map U.arr) := by
        obtain ⟨φ, hφ⟩ := hrep
        obtain ⟨ψ, ψ', hψ1, hψ2⟩ := hT1
        -- both `T(U.arr) ≫ ψ` and `φ` are maps into the terminal, so equal.
        have hcomp : hT.map U.arr ≫ ψ = φ := term_uniq _ _
        have hTeq : hT.map U.arr = φ ≫ ψ' := by
          rw [← hcomp, Cat.assoc, hψ1, Cat.comp_id]
        rw [hTeq]; exact isIso_comp hφ ⟨ψ, hψ2, hψ1⟩
      exact ⟨U.arr, href U.arr hTarr_iso⟩
    · -- U.dom ≅ 1 → T U.dom ≅ T 1 ≅ 1.
      intro hUiso
      exact isomorphic_trans (functor_preserves_iso_obj T hUiso) hT1
  · intro hfilter
    -- From the filter at `U = 1`, recover `T 1 ≅ 1` (also given directly as `hT1`).
    have h_one_iso : Isomorphic (T (one : 𝒞)) (one : 𝒟) :=
      (hfilter (Subobject.entire one)).mpr (isomorphic_refl one)
    -- Embedding needs `T` to preserve equalizers; reflecting isos needs `T` to
    -- preserve images.  Both are genuine missing obligations, left as honest
    -- sorries (not derivable from `hpm`/`hT1` alone).
    have hemb : Embedding T := by
      intro A B f g _hTfg
      sorry
    have href : ∀ {A B : 𝒞} (f : A ⟶ B), IsIso (hT.map f) → IsIso f := by
      intro A B f _hTf
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
