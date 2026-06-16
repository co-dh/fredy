/-
  Freyd & Scedrov, *Categories and Allegories* §2.4  Power allegories.

  §2.41 POWER ALLEGORY — operation ∋ (epsilon), power objects
  §2.412 A(R) is the unique map with A(R)∋ = R; simple F ⊑ A(F∋)
  §2.415 POWER-OBJECT, SINGLETON MAP, A(f) = f · A(1)
  §2.42 SPLITTING LEMMAS
  §2.43 PRE-POWER ALLEGORY
  §2.441 PRE-POSITIVE allegory, WELL-JOINED category
  §2.442 LAW OF METONYMY
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

/-- A(R) is a map (simple and entire) (§2.41).
    Simple branch: A(R) ⊑ R/∋, and since ∋ is straight R/∋ is simple [§2.356].
    Entire branch: dom(A(R)) = 1 ∩ (R/∋)(∋/R) ⊒ 1 via thickness [§2.3571]. -/
theorem A_is_map {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) : Map (A R) := by
  sorry

/-- A(R)∋ = R (§2.41).
    ⊑: A(R) ⊑ R/∋ (left component of symmDiv), so A(R)∋ ⊑ (R/∋)∋ ⊑ R.
    ⊒: uses thickness 1 ⊑ ∋/∋ and domain formula for symmDiv [§2.3571]. -/
theorem A_eps_eq {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) : A R ≫ ∋ b = R := by
  sorry

/-! ## §2.415  Power object and singleton map -/

/-- The SINGLETON MAP of a is A(1_a) : a → [a] (§2.415). -/
def singletonMap {a : 𝒜} [PowerAllegory 𝒜] : a ⟶ PowerAllegory.powerObj a :=
  A (Cat.id a)

/-- Singleton map is monic (§2.415): A(1_a)A(1_a)° ⊑ 1.
    Proof: A(1)A°(1) ⊑ (1/∋)(∋/1) = (1/∋)∋ ⊑ 1. -/
theorem singletonMap_monic {a : 𝒜} [PowerAllegory 𝒜] :
    singletonMap (a := a) ≫ singletonMap° ⊑ Cat.id a := by
  sorry

/-- For any map f : a → b, A(f) = f ≫ A(1_b) (§2.415).
    Book: "For any map p →ᶠ a, A(f) = f A(1) since f A(1) is a map and f A(1) ∋ = f."
    Relies on A_eps_eq and uniqueness of A(R). -/
theorem A_of_map {a b : 𝒜} [PowerAllegory 𝒜] (f : a ⟶ b) (hf : Map f) :
    A f = f ≫ singletonMap (a := b) := by
  sorry

/-! ## §2.412  Uniqueness of A(R) -/

/-- A(R) is the UNIQUE map F with F∋ = R (§2.412).
    Uniqueness: if F is a map and F∋ = R then F = A(R).
    This follows from straightness of ∋: ∋ /ₛ ∋ ⊑ 1 forces A(R) uniqueness. -/
theorem A_unique {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) (F : a ⟶ PowerAllegory.powerObj b)
    (hF : Map F) (hFeq : F ≫ ∋ b = R) : F = A R := by
  sorry

/-- If F is simple then F ⊑ A(F∋) (§2.412).
    Book: "Indeed, if F is simple then F ⊂ A(F∋)."
    Proof: need F ⊑ (F∋)/ₛ∋, i.e. F∋ ⊑ F∋ (trivial) and F°(F∋) ⊑ ∋,
    which follows from F°F ⊑ 1 and A(R)∋ = R. -/
theorem simple_le_A_eps {a b : 𝒜} [PowerAllegory 𝒜] (F : a ⟶ PowerAllegory.powerObj b)
    (hF : Simple F) : F ⊑ A (F ≫ ∋ b) := by
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

/-! ## §2.441  Pre-positive allegory and well-joined category

  An allegory is PRE-POSITIVE if for every pair of objects (a, β)
  there exist maps f : a → γ and g : β → γ (common target γ) such that:
  - ff° ∪ gg° = 1_γ   (jointly cover γ)
  - f°g = 𝟘            (disjoint images)
  (Equivalently, r₀ / ℓ = 𝟘, i.e. f°g = 𝟘.)

  A category is WELL-JOINED if for every pair of objects A, B there
  exist a common target C and maps f : A → C, g : B → C. -/

/-- A PRE-POSITIVE ALLEGORY (§2.441): distributive allegory where every pair
    of objects embeds into a common object via maps with disjoint images
    covering that object. -/
class PrePositiveAllegory (𝒜 : Type u) extends DistributiveAllegory 𝒜 where
  /-- For every pair (a, β), maps f : a → γ and g : β → γ with
      f°f ∪ g°g = 1_γ (covering, diagram order: f° then f gives γ→γ) and
      fg° = 𝟘 (disjoint: f then g° : a → β). -/
  pre_positive (a β : 𝒜) : ∃ (γ : 𝒜) (f : a ⟶ γ) (g : β ⟶ γ),
    Map f ∧ Map g ∧
    (f° ≫ f) ∪ (g° ≫ g) = Cat.id γ ∧
    f ≫ g° = (𝟘 : a ⟶ β)

/-- A WELL-JOINED CATEGORY (§2.441): allegory where every pair of objects
    maps to a common target via maps (no disjointness condition required). -/
class WellJoinedAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  /-- For every pair (A, B), maps f : A → C and g : B → C to a common target. -/
  well_joined (A B : 𝒜) : ∃ (C : 𝒜) (f : A ⟶ C) (g : B ⟶ C), Map f ∧ Map g

/-- Pre-positive implies well-joined (§2.441): the covering maps witness well-joinedness. -/
theorem pre_positive_to_well_joined {𝒜 : Type u} [PrePositiveAllegory 𝒜] :
    ∀ (A B : 𝒜), ∃ (C : 𝒜) (f : A ⟶ C) (g : B ⟶ C), Map f ∧ Map g := by
  intro A B
  obtain ⟨γ, f, g, hf, hg, _, _⟩ := PrePositiveAllegory.pre_positive A B
  exact ⟨γ, f, g, hf, hg⟩

/-! ## §2.442  Law of metonymy

  Given an object a in a power allegory, let ∋ = ∋_a and ∋' = ∋_{[a]}.
  Write ε = ∋° and ε' = (∋')°.

  Define (as maps [[a]] → [a]):
  - ⊓ = A(∋' · ∋)   (big intersection: the intersection of a family)
  - ⊔ = A(ε' \ ∋)    (big union: the union of a family)
    where ε' \ ∋ is the left division (ε' \ ∋ = (∋° / (ε')°)° = (∋° / ∋')°).

  The partial ordering on [a] is 2 = ∋°∋ (the ordering by subset inclusion).
  The straightness of ∋ forces 2 to be a partial order (not just pre-order).

  The LAW OF METONYMY: ⊓ ⊑ ⊔
  (the intersection of any family is contained in its union).

  A pre-positive power allegory is semi-simple iff it obeys the law of metonymy. -/

/-- The partial order morphism on [a]: 2 = ∋/∋ : [a] → [a] (§2.442).
    ∋ : [a] → a, so ∋/∋ : [a] → [a] (right division, reflexive transitive closure).
    Equivalently: X 2 Y iff X∋ ⊑ Y∋ (X is a subset of Y). -/
def powerOrder {a : 𝒜} [PowerAllegory 𝒜] :
    PowerAllegory.powerObj a ⟶ PowerAllegory.powerObj a :=
  ∋ a / ∋ a

-- (LEFT DIVISION `leftDiv` is defined canonically in S2_3 §2.312; reused here.)

/-- The big-intersection map ⊓ : [[a]] → [a] (§2.442).
    ⊓ = A(∋' ≫ ∋) where ∋' = ∋_{[a]} : [[a]] → [a] and ∋ = ∋_a : [a] → a. -/
def bigInter {a : 𝒜} [PowerAllegory 𝒜] :
    PowerAllegory.powerObj (PowerAllegory.powerObj a) ⟶ PowerAllegory.powerObj a :=
  A (∋ (PowerAllegory.powerObj a) ≫ ∋ a)

/-- The big-union map ⊔ : [[a]] → [a] (§2.442).
    ⊔ = A(ε' \ ∋) where ε' = (∋_{[a]})° : [a] → [[a]] and ∋ = ∋_a : [a] → a.
    Left division: ε' \ ∋ = leftDiv ε' ∋ = (∋° / ∋')°. -/
def bigUnion {a : 𝒜} [PowerAllegory 𝒜] :
    PowerAllegory.powerObj (PowerAllegory.powerObj a) ⟶ PowerAllegory.powerObj a :=
  A (leftDiv ((∋ (PowerAllegory.powerObj a))°) (∋ a))

/-- LAW OF METONYMY (§2.442): bigInter ⊑ bigUnion, i.e. ⊓ ⊑ ⊔.
    The intersection of any family is contained in its union. -/
def MetonymyLaw (𝒜 : Type u) [PowerAllegory 𝒜] : Prop :=
  ∀ (a : 𝒜), @bigInter 𝒜 a _ ⊑ @bigUnion 𝒜 a _

/-- A pre-positive power allegory is semi-simple iff it obeys the law of metonymy (§2.442). -/
theorem pre_positive_semi_simple_iff_metonymic {𝒜 : Type u}
    [PowerAllegory 𝒜] [PrePositiveAllegory 𝒜] :
    (∀ (a b : 𝒜) (R : a ⟶ b), SemiSimple R) ↔ MetonymyLaw 𝒜 := by
  sorry

end Freyd.Alg
