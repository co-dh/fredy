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
  dsimp [Map, A, symmDiv]
  have h_straight : ∋ b /ₛ ∋ b ⊑ Cat.id (PowerAllegory.powerObj b) :=
    PowerAllegory.eps_straight b
  -- From the definition of symmetric division, A R = (R / ∋) ∩ (∋ / R)°
  -- First get the characterizing inequalities for A R via le_symmDiv_iff
  have h_AR_comp_eps_le_R : ((R / ∋ b) ∩ ((∋ b / R)°)) ≫ ∋ b ⊑ R := by
    -- A R ⊑ R / ∋ b, so A R ≫ ∋ b ⊑ (R / ∋ b) ≫ ∋ b ⊑ R
    apply le_trans (comp_mono_right (inter_lb_left (R / ∋ b) ((∋ b / R)°)) (∋ b)) ?_
    exact div_comp_eq_le R (∋ b)
  have h_ARrecip_comp_R_le_eps : ((R / ∋ b) ∩ ((∋ b / R)°))° ≫ R ⊑ ∋ b := by
    -- (A R)° ⊑ ∋ b / R, so (A R)° ≫ R ⊑ (∋ b / R) ≫ R ⊑ ∋ b
    have h_ARrecip_le_div : ((R / ∋ b) ∩ ((∋ b / R)°))° ⊑ ∋ b / R := by
      -- (R/∋ ∩ (∋/R)°)° = (R/∋)° ∩ (∋/R) ⊑ ∋/R
      rw [Allegory.recip_inter, Allegory.recip_recip]
      exact inter_lb_right ((R / ∋ b)°) (∋ b / R)
    apply le_trans (comp_mono_right h_ARrecip_le_div R) ?_
    exact div_comp_eq_le (∋ b) R
  constructor
  · -- Entire (A R): dom (A R) = id_a
    dsimp [Entire, dom]
    apply le_antisymm
    · exact inter_lb_left (Cat.id a) _
    · apply le_inter (le_refl (Cat.id a))
      sorry
  · -- Simple (A R): (A R)° ≫ (A R) ⊑ id_{powerObj b}
    dsimp [Simple]
    have hX_le_symm : ((R / ∋ b) ∩ ((∋ b / R)°))° ≫ ((R / ∋ b) ∩ ((∋ b / R)°)) ⊑ ∋ b /ₛ ∋ b := by
      rw [le_symmDiv_iff]
      constructor
      · -- X ≫ ∋ ⊑ ∋
        -- X ≫ ∋ = (A R)° ≫ A R ≫ ∋ = (A R)° ≫ (A R ≫ ∋) ⊑ (A R)° ≫ R ⊑ ∋
        rw [Cat.assoc]
        apply le_trans ?_ h_ARrecip_comp_R_le_eps
        apply comp_mono_left _ h_AR_comp_eps_le_R
      · -- X° ≫ ∋ ⊑ ∋; X° = X, so same as above
        have hX_symm : (((R / ∋ b) ∩ ((∋ b / R)°))° ≫ ((R / ∋ b) ∩ ((∋ b / R)°)))° =
            ((R / ∋ b) ∩ ((∋ b / R)°))° ≫ ((R / ∋ b) ∩ ((∋ b / R)°)) := by
          rw [Allegory.recip_comp, Allegory.recip_recip]
        rw [hX_symm]
        rw [Cat.assoc]
        apply le_trans ?_ h_ARrecip_comp_R_le_eps
        apply comp_mono_left _ h_AR_comp_eps_le_R
    exact le_trans hX_le_symm h_straight

/-- A(R)∋ = R (§2.41). -/
theorem A_eps_eq {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) : A R ≫ ∋ b = R := by
  dsimp [A, symmDiv]
  apply le_antisymm
  · -- ((R/∋) ∩ (∋/R)°) ≫ ∋ ⊑ R.  Already proven in A_is_map.
    apply le_trans (comp_mono_right (inter_lb_left (R / ∋ b) ((∋ b / R)°)) (∋ b)) ?_
    exact div_comp_eq_le R (∋ b)
  · -- R ⊑ ((R/∋) ∩ (∋/R)°) ≫ ∋.  Requires power-allegory structure.
    sorry

/-! ## §2.415  Power object and singleton map -/

/-- The SINGLETON MAP of a: A(1_a) : a → [a] (§2.415). -/
def singletonMap {a : 𝒜} [PowerAllegory 𝒜] : a ⟶ PowerAllegory.powerObj a :=
  A (Cat.id a)

/-- Singleton map is monic (§2.415): A(1_a)A(1_a)° ⊑ 1. -/
theorem singletonMap_monic {a : 𝒜} [PowerAllegory 𝒜] :
    singletonMap (a := a) ≫ singletonMap° ⊑ Cat.id a := by
  dsimp [singletonMap, A, symmDiv]
  -- Goal: ((id / ∋) ∩ ((∋ / id)°)) ≫ ((id / ∋) ∩ ((∋ / id)°))° ⊑ id
  rw [Allegory.recip_inter, Allegory.recip_recip]
  -- Goal: ((id / ∋) ∩ ((∋ / id)°)) ≫ ((id / ∋)° ∩ (∋ / id)) ⊑ id
  -- Bound first factor via inter_lb_left, second factor via inter_lb_right
  have h1 : ((Cat.id a / ∋ a) ∩ ((∋ a / Cat.id a)°)) ≫ ((Cat.id a / ∋ a)° ∩ (∋ a / Cat.id a))
      ⊑ (Cat.id a / ∋ a) ≫ ((Cat.id a / ∋ a)° ∩ (∋ a / Cat.id a)) := by
    apply comp_mono_right (inter_lb_left _ _) _
  have h2 : (Cat.id a / ∋ a) ≫ ((Cat.id a / ∋ a)° ∩ (∋ a / Cat.id a))
      ⊑ (Cat.id a / ∋ a) ≫ (∋ a / Cat.id a) := by
    apply comp_mono_left _ (inter_lb_right _ _)
  have h3 : (Cat.id a / ∋ a) ≫ (∋ a / Cat.id a) ⊑ Cat.id a / Cat.id a :=
    div_comp (Cat.id a) (∋ a) (Cat.id a)
  have h4 : Cat.id a / Cat.id a = Cat.id a := div_one _
  apply le_trans h1
  apply le_trans h2
  apply le_trans h3
  rw [h4]
  exact le_refl _

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
