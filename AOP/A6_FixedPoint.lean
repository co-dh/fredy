/-
  Port of AoPA `FixedPoint.agda`: lower bounds, least elements, and least (pre)fixed-point
  lemmas.  This is point-level order theory over a carrier type `A` with an equivalence `≈`
  (`eqv`) and an order `≼` (`le`); it is not tied to the allegory, so it is stated generically.

  Mathlib-free; axioms ⊆ {} (pure logic).
-/

universe u

namespace Freyd.Alg
namespace FixedPoint

variable {A : Type u}

/-- `LowerBound P ≼ lb`: `lb` is `≼`-below every element satisfying `P` (AoPA `LowerBound`). -/
def LowerBound (P : A → Prop) (le : A → A → Prop) (lb : A) : Prop := ∀ {x}, P x → le lb x

/-- `Least P ≼ x`: `x` satisfies `P` and is a lower bound of `P` (AoPA `Least`). -/
def Least (P : A → Prop) (le : A → A → Prop) (x : A) : Prop := P x ∧ LowerBound P le x

/-- `PrefixP ≼ f x`: `x` is a prefixed point of `f`, `f x ≼ x` (AoPA `PrefixP`). -/
def PrefixP (le : A → A → Prop) (f : A → A) (x : A) : Prop := le (f x) x

/-- Least prefixed point (AoPA `LeastPrefixedPoint`). -/
def LeastPrefixedPoint (le : A → A → Prop) (f : A → A) (x : A) : Prop :=
  Least (PrefixP le f) le x

/-- `FixP ≈ f x`: `x` is a fixed point of `f`, `f x ≈ x` (AoPA `FixP`). -/
def FixP (eqv : A → A → Prop) (f : A → A) (x : A) : Prop := eqv (f x) x

/-- Least fixed point (AoPA `LeastFixedPoint`). -/
def LeastFixedPoint (eqv le : A → A → Prop) (f : A → A) (x : A) : Prop :=
  Least (FixP eqv f) le x

/-- A partial order at the point level: what AoPA's `IsPartialOrder _≈_ _≼_` supplies. -/
structure IsPartialOrder (eqv le : A → A → Prop) : Prop where
  refl : ∀ x, le x x
  trans : ∀ {x y z}, le x y → le y z → le x z
  reflexive : ∀ {x y}, eqv x y → le x y
  antisym : ∀ {x y}, le x y → le y x → eqv x y

variable {eqv le : A → A → Prop} {f : A → A}

/-- AoPA `lpfp-unique`: least prefixed points are unique up to `≈`. -/
theorem lpfp_unique (po : IsPartialOrder eqv le)
    {μ₁ : A} (h₁ : LeastPrefixedPoint le f μ₁)
    {μ₂ : A} (h₂ : LeastPrefixedPoint le f μ₂) : eqv μ₁ μ₂ :=
  po.antisym (h₁.2 h₂.1) (h₂.2 h₁.1)

/-- AoPA `lfp-unique`: least fixed points are unique up to `≈`. -/
theorem lfp_unique (po : IsPartialOrder eqv le)
    {μ₁ : A} (h₁ : LeastFixedPoint eqv le f μ₁)
    {μ₂ : A} (h₂ : LeastFixedPoint eqv le f μ₂) : eqv μ₁ μ₂ :=
  po.antisym (h₁.2 h₂.1) (h₂.2 h₁.1)

/-- AoPA `lpfp⇒≽`: a least prefixed point of a monotone `f` satisfies `μf ≼ f μf`. -/
theorem lpfp_ge (f_mono : ∀ {x y}, le x y → le (f x) (f y))
    {μf : A} (h : LeastPrefixedPoint le f μf) : le μf (f μf) :=
  -- `f μf ≼ μf` ⇒ (mono) `f (f μf) ≼ f μf` = `PrefixP (f μf)` ⇒ (lower bound) `μf ≼ f μf`.
  h.2 (f_mono h.1)

/-- AoPA `lpfp⇒fixp`: a least prefixed point of a monotone `f` is a fixed point. -/
theorem lpfp_fixp (po : IsPartialOrder eqv le)
    (f_mono : ∀ {x y}, le x y → le (f x) (f y))
    {μf : A} (h : LeastPrefixedPoint le f μf) : FixP eqv f μf :=
  po.antisym h.1 (lpfp_ge f_mono h)

/-- AoPA `lpfp⇒lb`: a least prefixed point is a lower bound for fixed points. -/
theorem lpfp_lb (po : IsPartialOrder eqv le)
    {μf : A} (h : LeastPrefixedPoint le f μf) : LowerBound (FixP eqv f) le μf :=
  fun {_} hfx => h.2 (po.reflexive hfx)

/-- AoPA `lpfp⇒lfp`: a least prefixed point of a monotone `f` is a least fixed point. -/
theorem lpfp_lfp (po : IsPartialOrder eqv le)
    (f_mono : ∀ {x y}, le x y → le (f x) (f y))
    {μf : A} (h : LeastPrefixedPoint le f μf) : LeastFixedPoint eqv le f μf :=
  ⟨lpfp_fixp po f_mono h, lpfp_lb po h⟩

/-- AoPA `lfp⇒lpfp≈`: a least prefixed point equals (up to `≈`) any least fixed point. -/
theorem lfp_lpfp_eqv (po : IsPartialOrder eqv le)
    (f_mono : ∀ {x y}, le x y → le (f x) (f y))
    {μf : A} (lpfp : LeastPrefixedPoint le f μf)
    {φf : A} (lfp : LeastFixedPoint eqv le f φf) : eqv μf φf :=
  lfp_unique po (lpfp_lfp po f_mono lpfp) lfp

end FixedPoint
end Freyd.Alg
