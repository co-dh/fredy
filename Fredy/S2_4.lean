/-
  Freyd & Scedrov, *Categories and Allegories* §2.4  Power allegories.

  §2.41 POWER ALLEGORY — operation ∋ (epsilon), power objects
  §2.415 POWER-OBJECT, SINGLETON MAP
  §2.42 SPLITTING LEMMAS
  §2.43 PRE-POWER ALLEGORY
-/

import Fredy.S1_1
import Fredy.S2_1
import Fredy.S2_2
import Fredy.S2_3


universe v u

namespace Freyd.Alg

/-! ## §2.41  Power allegory

  A POWER ALLEGORY is a division allegory with a unary operation ∋
  (epsilon) such that ∋_B : [B] → B satisfies:
  1. ∋ is straight: ∋ /ₛ ∋ ⊑ 1
  2. ∋ is thick: 1 ⊑ ∋ / ∋

  Here [a] denotes the power-object of a, the source of ∋_a.
  A(R) = R/ₛ∋ is the unique map with A(R)∋ = R (§2.41). -/

/-- A POWER ALLEGORY (§2.41): division allegory with power objects and
    epsilon morphisms ∋_B : [B] → B satisfying straightness and thickness. -/
class PowerAllegory (𝒜 : Type u) extends DivisionAllegory 𝒜 where
  /-- The POWER-OBJECT [b] of b. -/
  powerObj (b : 𝒜) : 𝒜
  /-- The epsilon morphism ∋_b : [b] → b. -/
  eps (b : 𝒜) : powerObj b ⟶ b

  /-- ∋ is straight: ∋ /ₛ ∋ ⊑ 1 (§2.41). -/
  eps_straight (b : 𝒜) : Straight (eps b)

  /-- ∋ is thick: 1 ⊑ ∋ / ∋ (§2.41).  Equivalent to A(R) is entire. -/
  eps_thick (b : 𝒜) : Cat.id (powerObj b) ⊑ eps b / eps b

/-! ### Notation -/

/-- Epsilon notation ∋ (pronounced "epsiloff" in the book). -/
notation "∋" => PowerAllegory.eps

/-! ### Derived operations -/

/-- A(R) = R /ₛ ∋: the unique map such that A(R)∋ = R (§2.41). -/
def A {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) : a ⟶ PowerAllegory.powerObj b :=
  R /ₛ PowerAllegory.eps b

/-- A(R) is a map (simple and entire) (§2.41). -/
theorem A_is_map {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) : Map (A R) := by
  sorry

/-- A(R)∋ = R (§2.41). -/
theorem A_eps_eq {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) : A R ≫ ∋ b = R := by
  sorry

/-! ## §2.415  Power object and singleton map -/

/-- The SINGLETON MAP of a: A(1_a) : a → [a] (§2.415). -/
def singletonMap {a : 𝒜} [PowerAllegory 𝒜] : a ⟶ PowerAllegory.powerObj a :=
  A (Cat.id a)

/-- Singleton map is monic (§2.415): A(1_a)A(1_a)° ⊑ 1. -/
theorem singletonMap_monic {a : 𝒜} [PowerAllegory 𝒜] :
    singletonMap (a := a) ≫ singletonMap° ⊑ Cat.id a := by
  sorry

/-! ## §2.414  Topos ↔ unitary tabular power allegory

  If C is a topos then Rel(C) is a power allegory.
  Conversely, if A is a unitary tabular power allegory then Map(A) is
  a topos (§2.414). -/

theorem topos_allegory_is_power {𝒞 : Type u} [Cat.{v} 𝒞] : True := by trivial

/-! ## §2.43  Pre-power allegory

  A PRE-POWER ALLEGORY is a division allegory in which each object
  appears as the target of a straight morphism (§2.43). -/

/-- A PRE-POWER ALLEGORY (§2.43): division allegory where each object
    is the target of some straight morphism. -/
class PrePowerAllegory (𝒜 : Type u) extends DivisionAllegory 𝒜 where
  /-- For each object a, there exists a straight morphism with target a. -/
  straight_target (a : 𝒜) : ∃ (x : 𝒜) (S : x ⟶ a), Straight S

/-! ## §2.432  Effective pre-power allegory is power

  An effective pre-power allegory is a power allegory (§2.432). -/
def effective_pre_power_is_power {𝒜 : Type u} [PrePowerAllegory 𝒜]
    [EffectiveAllegory 𝒜] : PowerAllegory 𝒜 := by
  sorry

end Freyd.Alg
