/-
  Freyd & Scedrov, *Categories and Allegories* §1.97–§1.98  Boolean topoi, natural numbers.

  §1.97  BOOLEAN TOPOS: Ω is a Boolean algebra (every subobject is complemented).
  §1.971 SMALL OBJECT in a topos.
  §1.973 INTERNAL AXIOM OF CHOICE (IAC).
  §1.98  NATURAL NUMBERS OBJECT (NNO) in a topos.
  §1.987 PEANO PROPERTY for NNO.
  §1.98(10) Bicartesian characterization of NNO.
  §1.98(12) A-ACTION, FREE A-ACTION.
-/

import Fredy.S1_1
import Fredy.S1_9


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.97  Boolean topos

  A TOPOS IS BOOLEAN if its subobject classifier Ω is an internal
  Boolean algebra, i.e. every subobject has a complement (§1.97).
  Equivalently: the negation map ¬ : Ω → Ω satisfies ¬¬ = id. -/

/-- A BOOLEAN TOPOS has ¬¬ = id on Ω, i.e. every subobject is complemented (§1.97). -/
class BooleanTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞 where
  not : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)
  double_neg : not ≫ not = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞))

/-! ## §1.98  Natural numbers object

  A NATURAL NUMBERS OBJECT in a topos is an object N with maps
  0 : 1 → N and s : N → N satisfying the Peano property:
  for any object X with x : 1 → X and f : X → X, there exists a
  unique h : N → X such that 0 ≫ h = x and s ≫ h = h ≫ f. -/

/-- A NATURAL NUMBERS OBJECT (NNO) (§1.98, §1.987): object N with zero 0:1→N
    and successor s:N→N satisfying the universal property (Peano). -/
class HasNaturalNumbersObject (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞 where
  nno : 𝒞
  zero : one ⟶ nno
  succ : nno ⟶ nno
  /-- The universal property: for X, x:1→X, f:X→X, there exists a unique
      h : N → X such that 0 ≫ h = x and s ≫ h = h ≫ f. -/
  iterate {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X) : nno ⟶ X
  iterate_zero {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X) : zero ≫ iterate x f = x
  iterate_succ {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X) : succ ≫ iterate x f = iterate x f ≫ f
  iterate_unique {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X) (h : nno ⟶ X)
    (h0 : zero ≫ h = x) (hs : succ ≫ h = h ≫ f) : h = iterate x f

end Freyd
