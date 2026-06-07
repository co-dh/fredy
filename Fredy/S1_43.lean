/-
  Freyd & Scedrov, *Categories and Allegories* §1.43–§1.437
  Cartesian categories: equalizers, pullbacks, equivalences.

  §1.43: Cartesian = finite products + equalizers.
  §1.431: Pullback diagram.
  §1.432–§1.435: Equivalence theorems (products+eq→pb, pb+term→products, etc.)
  §1.437: Representation of Cartesian categories.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45

set_option linter.unusedSectionVars false

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## Equalizers

  An EQUALIZER of f, g : A → B is an object E with e : E → A
  such that e ≫ f = e ≫ g, universal among such morphisms. -/

structure EqualizerCone {A B : 𝒞} (f g : A ⟶ B) where
  dom : 𝒞
  map : dom ⟶ A
  eq  : map ≫ f = map ≫ g

class HasEqualizer {A B : 𝒞} (f g : A ⟶ B) where
  cone : EqualizerCone f g
  lift : ∀ (c : EqualizerCone f g), c.dom ⟶ cone.dom
  fac  : ∀ (c : EqualizerCone f g), lift c ≫ cone.map = c.map
  uniq : ∀ (c : EqualizerCone f g) (m : c.dom ⟶ cone.dom), m ≫ cone.map = c.map → m = lift c

class HasEqualizers (𝒞 : Type u) [Cat.{v} 𝒞] where
  eq : ∀ {A B : 𝒞} (f g : A ⟶ B), HasEqualizer f g

variable [HasEqualizers 𝒞]

def eqObj {A B : 𝒞} (f g : A ⟶ B) : 𝒞 := (HasEqualizers.eq f g).cone.dom
def eqMap {A B : 𝒞} (f g : A ⟶ B) : eqObj f g ⟶ A := (HasEqualizers.eq f g).cone.map
theorem eqMap_eq {A B : 𝒞} (f g : A ⟶ B) : eqMap f g ≫ f = eqMap f g ≫ g :=
  (HasEqualizers.eq f g).cone.eq

def eqLift {A B X : 𝒞} (f g : A ⟶ B) (k : X ⟶ A) (h : k ≫ f = k ≫ g) : X ⟶ eqObj f g :=
  (HasEqualizers.eq f g).lift ⟨X, k, h⟩

theorem eqLift_fac {A B X : 𝒞} (f g : A ⟶ B) (k : X ⟶ A) (h : k ≫ f = k ≫ g) :
    eqLift f g k h ≫ eqMap f g = k :=
  (HasEqualizers.eq f g).fac ⟨X, k, h⟩

theorem eqLift_uniq {A B X : 𝒞} (f g : A ⟶ B) (k : X ⟶ A) (h : k ≫ f = k ≫ g)
    (m : X ⟶ eqObj f g) (hm : m ≫ eqMap f g = k) : m = eqLift f g k h :=
  (HasEqualizers.eq f g).uniq ⟨X, k, h⟩ m hm

/-! ## Cartesian category (§1.43) -/

/-- A CARTESIAN CATEGORY: has terminal object, binary products, and equalizers. -/
class CartesianCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasEqualizers 𝒞

/-! ## §1.432–§1.435 Equivalence theorems

  (1) Products + equalizers → pullbacks (§1.432)
  (2) Pullbacks + terminator → binary products (§1.433)
  (3) Binary products + pullbacks → equalizers (§1.434)
  (4) Pullbacks + terminator → Cartesian (§1.435: (2)+(3)+(1))

  Proofs involve constructing pullbacks/equalizers/products in terms of
  each other.  Standard category theory. -/

variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞]

/-- §1.432: Products + equalizers → pullbacks.
    Given f: A→C, g: B→C, construct their pullback as the equalizer
    of p₁≫f and p₂≫g on A×B. -/
def products_equalizers_implies_pullbacks
    {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) : HasPullback f g := by
  -- Equalize fst ≫ f and snd ≫ g on prod A B
  sorry

/-- §1.433: Pullbacks + terminator → binary products.
    Product A×B is the pullback of !A, !B over 1. -/
def pullbacks_terminator_implies_products : HasBinaryProducts 𝒞 := by
  sorry

/-- §1.434: Binary products + pullbacks → equalizers.
    Equalizer of f,g is the pullback of (id, f) and (id, g) on A × B. -/
def products_pullbacks_implies_equalizers : HasEqualizers 𝒞 := by
  sorry

/-- §1.435: Pullbacks + terminator → Cartesian. -/
def pullbacks_terminator_implies_cartesian : CartesianCategory 𝒞 := by
  sorry

end Freyd
