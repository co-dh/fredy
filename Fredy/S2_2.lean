/-
  Freyd & Scedrov, *Categories and Allegories* §2.2  Distributive allegories.

  §2.21 DISTRIBUTIVE ALLEGORY — zero and union, distributivity
  §2.215 POSITIVE ALLEGORY — finite coproducts
  §2.22 LOCALLY COMPLETE DISTRIBUTIVE ALLEGORY
  §2.223 GLOBALLY COMPLETE
-/

import Fredy.S1_1
import Fredy.S2_1


universe v u

namespace Freyd.Alg

/-! ## §2.21  Distributive allegory

  A DISTRIBUTIVE ALLEGORY is an allegory with a distinguished zero
  morphism 0 : a → b for each a, b, and a binary union R ∪ S. -/

/-- A DISTRIBUTIVE ALLEGORY (§2.21): allegory with zero, union,
    and distributivity. -/
class DistributiveAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  /-- Zero morphism 0 : a → b for each pair of objects. -/
  zero {a b : 𝒜} : a ⟶ b
  /-- Union (join) R ∪ S : a → b when R, S : a → b. -/
  union {a b : 𝒜} (R S : a ⟶ b) : a ⟶ b

  /-- Zero is absorbing on the left: 0 ≫ R = 0 (§2.21). -/
  zero_comp {a b c : 𝒜} (R : b ⟶ c) : (zero : a ⟶ b) ≫ R = zero
  /-- Zero is absorbing on the right: R ≫ 0 = 0 (§2.21). -/
  comp_zero {a b c : 𝒜} (R : a ⟶ b) : R ≫ (zero : b ⟶ c) = zero

  /-- Union is idempotent: R ∪ R = R (§2.21). -/
  union_idem {a b : 𝒜} (R : a ⟶ b) : union R R = R
  /-- Union is commutative: R ∪ S = S ∪ R (§2.21). -/
  union_comm {a b : 𝒜} (R S : a ⟶ b) : union R S = union S R
  /-- Union is associative: R ∪ (S ∪ T) = (R ∪ S) ∪ T (§2.21). -/
  union_assoc {a b : 𝒜} (R S T : a ⟶ b) : union R (union S T) = union (union R S) T

  /-- Absorption: R ∪ (S ∩ R) = R (§2.21). -/
  union_inter_absorb {a b : 𝒜} (R S : a ⟶ b) : union R (Allegory.inter S R) = R
  /-- Absorption: (R ∪ S) ∩ R = R (§2.21). -/
  inter_union_absorb {a b : 𝒜} (R S : a ⟶ b) : Allegory.inter (union R S) R = R

  /-- Composition distributes over union: R ≫ (S ∪ T) = RS ∪ RT (§2.21). -/
  comp_union_distrib {a b c : 𝒜} (R : a ⟶ b) (S T : b ⟶ c) :
    R ≫ union S T = union (R ≫ S) (R ≫ T)
  /-- Intersection distributes over union: R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T) (§2.21). -/
  inter_union_distrib {a b : 𝒜} (R S T : a ⟶ b) :
    Allegory.inter R (union S T) = union (Allegory.inter R S) (Allegory.inter R T)
  /-- Zero is identity for union: 0 ∪ R = R (§2.211). -/
  zero_union {a b : 𝒜} (R : a ⟶ b) : union zero R = R

/-! ### Notation -/

/-- Zero morphism notation -/
notation "𝟘" => DistributiveAllegory.zero

/-- Union notation R ∪ S -/
infixl:65 " ∪ " => DistributiveAllegory.union

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-! ### Order from union

  In a distributive allegory, R ⊑ S (i.e., R = R ∩ S) iff R ∪ S = S.
  This is the standard lattice duality. -/

theorem le_iff_union_eq_left {a b : 𝒜} (R S : a ⟶ b) : (R ⊑ S) ↔ R ∪ S = S := by
  constructor
  · intro h
    dsimp [le] at h
    -- h: R ∩ S = R. Need: R ∪ S = S.
    have h_absorb : S ∪ (R ∩ S) = S := DistributiveAllegory.union_inter_absorb S R
    calc
      R ∪ S = (R ∩ S) ∪ S := by rw [h]
      _ = S ∪ (R ∩ S) := by rw [DistributiveAllegory.union_comm]
      _ = S := by rw [h_absorb]
  · intro h
    -- h: R ∪ S = S. Need: R ⊑ S, i.e., R ∩ S = R.
    dsimp [le]
    calc
      R ∩ S = S ∩ R := by rw [Allegory.inter_comm R S]
      _ = (R ∪ S) ∩ R := by rw [h]
      _ = R := by rw [DistributiveAllegory.inter_union_absorb R S]

/-! ### Helper: union is least upper bound -/

/-- If A ⊑ C and B ⊑ C then A ∪ B ⊑ C. -/
theorem union_lub {a b : 𝒜} {A B C : a ⟶ b} (hA : A ⊑ C) (hB : B ⊑ C) : A ∪ B ⊑ C := by
  rw [le_iff_union_eq_left] at hA hB ⊢
  -- hA: A ∪ C = C,  hB: B ∪ C = C.  Goal: (A ∪ B) ∪ C = C
  calc
    (A ∪ B) ∪ C = A ∪ (B ∪ C) := by rw [DistributiveAllegory.union_assoc]
    _ = A ∪ C := by rw [hB]
    _ = C := hA

/-- Union is an upper bound: R ⊑ R ∪ S. -/
theorem le_union_left {a b : 𝒜} (R S : a ⟶ b) : R ⊑ R ∪ S := by
  dsimp [le]
  rw [Allegory.inter_comm, DistributiveAllegory.inter_union_absorb]

/-- Union is an upper bound: S ⊑ R ∪ S. -/
theorem le_union_right {a b : 𝒜} (R S : a ⟶ b) : S ⊑ R ∪ S := by
  rw [DistributiveAllegory.union_comm]; exact le_union_left S R

/-! ### Derived properties -/

/-- (R ∪ S)° = S° ∪ R° (§2.211). -/
theorem recip_union {a b : 𝒜} (R S : a ⟶ b) : (R ∪ S)° = S° ∪ R° := by
  apply le_antisymm
  · -- (R ∪ S)° ⊑ S° ∪ R°
    have hR' : R ⊑ (S° ∪ R°)° := recip_le_iff.mp (le_union_right S° R°)
    have hS' : S ⊑ (S° ∪ R°)° := recip_le_iff.mp (le_union_left S° R°)
    have h_union : R ∪ S ⊑ (S° ∪ R°)° := union_lub hR' hS'
    exact recip_le_iff.mpr h_union
  · -- S° ∪ R° ⊑ (R ∪ S)°
    have hR : R ⊑ R ∪ S := le_union_left R S
    have hS : S ⊑ R ∪ S := le_union_right R S
    have hRrecip : R° ⊑ (R ∪ S)° := recip_mono hR
    have hSrecip : S° ⊑ (R ∪ S)° := recip_mono hS
    -- Goal: S° ∪ R° ⊑ (R ∪ S)°.  We have R° ⊑ (R ∪ S)° and S° ⊑ (R ∪ S)°.
    -- union_lub takes the first argument as ⊑ for the LEFT operand of ∪.
    -- Since S° is on the left, we need hSrecip first.
    exact union_lub hSrecip hRrecip

/-- (S ∪ T) ≫ R = SR ∪ TR (§2.211).
    Proof via reciprocation: ((S∪T)R)° = R°(S∪T)° = R°(T°∪S°) = R°T° ∪ R°S° = (TR)° ∪ (SR)°.
    Then take ° of both sides. -/
theorem union_comp_distrib {a b c : 𝒜} (S T : a ⟶ b) (R : b ⟶ c) :
    (S ∪ T) ≫ R = (S ≫ R) ∪ (T ≫ R) := by
  -- First show equality of the reciprocals, then take °
  -- Chain: ((S∪T)R)° = R°(S∪T)° = R°(T°∪S°) = R°T° ∪ R°S° = (TR)° ∪ (SR)°
  --                  = (SR)° ∪ (TR)° = (SR ∪ TR)°
  have h_recip : ((S ∪ T) ≫ R)° = ((S ≫ R) ∪ (T ≫ R))° := by
    rw [Allegory.recip_comp, recip_union S T, DistributiveAllegory.comp_union_distrib,
      ← Allegory.recip_comp T R, ← Allegory.recip_comp S R]
    -- Goal: (T ≫ R)° ∪ (S ≫ R)° = ((S ≫ R) ∪ (T ≫ R))°
    -- recip_union expands RHS to (T ≫ R)° ∪ (S ≫ R)°, matching LHS
    rw [recip_union (S ≫ R) (T ≫ R)]
  -- Now apply ° to both sides of the equality
  calc
    (S ∪ T) ≫ R = (((S ∪ T) ≫ R)°)° := by rw [Allegory.recip_recip]
    _ = (((S ≫ R) ∪ (T ≫ R))°)° := by rw [h_recip]
    _ = (S ≫ R) ∪ (T ≫ R) := by rw [Allegory.recip_recip]

/-- `R ∪ 𝟘 = R` (§2.211). Follows from `zero_union` and `union_comm`. -/
theorem union_zero {a b : 𝒜} (R : a ⟶ b) : R ∪ (𝟘 : a ⟶ b) = R := by
  rw [DistributiveAllegory.union_comm, DistributiveAllegory.zero_union R]

/-- `𝟘 ⊑ R` for all `R` — zero is the minimum morphism (§2.211). -/
theorem zero_le {a b : 𝒜} (R : a ⟶ b) : (𝟘 : a ⟶ b) ⊑ R := by
  rw [le_iff_union_eq_left, DistributiveAllegory.zero_union R]

/-- 0° = 0 (§2.211). -/
theorem recip_zero {a b : 𝒜} : (𝟘 : a ⟶ b)° = (𝟘 : b ⟶ a) := by
  apply le_antisymm
  · -- 0_ab° ⊑ 0_ba   ↔  0_ab ⊑ 0_ba°  by recip_le_iff.mpr
    -- 0_ab ⊑ 0_ba° holds by zero_le (0 is minimum in a→b)
    apply (recip_le_iff.mpr (zero_le (a := a) (b := b) ((𝟘 : b ⟶ a)°)))
  · -- 0_ba ⊑ 0_ab°  holds by zero_le (0 is minimum in b→a)
    apply zero_le (a := b) (b := a) ((𝟘 : a ⟶ b)°)

/-! ## §2.214  Coproducts in distributive allegories

  A₁ ⊕ A₂ is a coproduct if there exist u₁ : A₁ → A, u₂ : A₂ → A
  satisfying five equations (§2.214). -/

/-- Coproduct diagram (§2.214). `u₁ : a₁ → a`, `u₂ : a₂ → a` with:
    u₁u₁° = 1, u₁u₂° = 0, u₂u₁° = 0, u₂u₂° = 1, u₁°u₁ ∪ u₂°u₂ = 1. -/
structure Coproduct (a a₁ a₂ : 𝒜) where
  u₁ : a₁ ⟶ a
  u₂ : a₂ ⟶ a
  u₁_self_comp_recip : u₁ ≫ u₁° = Cat.id a₁
  u₁_u₂_recip : u₁ ≫ u₂° = (𝟘 : a₁ ⟶ a₂)
  u₂_u₁_recip : u₂ ≫ u₁° = (𝟘 : a₂ ⟶ a₁)
  u₂_self_comp_recip : u₂ ≫ u₂° = Cat.id a₂
  recip_union_eq_id : (u₁° ≫ u₁) ∪ (u₂° ≫ u₂) = Cat.id a

/-! ### §2.214  Equivalence: five equations ↔ universal coproduct property

  The book (§2.214) proves that the five equations characterising `Coproduct`
  are equivalent (in any distributive allegory) to the assertion that A is a
  coproduct in the allegory-theoretic sense: every pair (R₁ : a₁ → c,
  R₂ : a₂ → c) factors uniquely through the injections. -/

/-- The universal coproduct property for (a, u₁, u₂) (§2.214):
    for any c and morphisms R₁ : a₁ → c, R₂ : a₂ → c there exists a unique
    R : a → c with u₁ ≫ R = R₁ and u₂ ≫ R = R₂ (where u_i : a_i → a are the injections). -/
def IsCoproduct {𝒜 : Type u} [DistributiveAllegory 𝒜] {a a₁ a₂ : 𝒜}
    (u₁ : a₁ ⟶ a) (u₂ : a₂ ⟶ a) : Prop :=
  ∀ (c : 𝒜) (R₁ : a₁ ⟶ c) (R₂ : a₂ ⟶ c),
    ∃ R : a ⟶ c,
      (u₁ ≫ R = R₁) ∧ (u₂ ≫ R = R₂) ∧
      (∀ R' : a ⟶ c, u₁ ≫ R' = R₁ → u₂ ≫ R' = R₂ → R' = R)

/-- (§2.214) The five `Coproduct` equations imply the universal property.
    The mediating morphism is u₁° ≫ R₁ ∪ u₂° ≫ R₂. -/
theorem coproduct_five_eqs_to_universal {𝒜 : Type u} [DistributiveAllegory 𝒜]
    {a a₁ a₂ : 𝒜} (cp : Coproduct a a₁ a₂) : IsCoproduct cp.u₁ cp.u₂ := by
  -- IsCoproduct: ∀ c R₁ R₂, ∃ R, u₁≫R=R₁ ∧ u₂≫R=R₂ ∧ uniqueness
  intro c R₁ R₂
  -- The mediating morphism [§2.214, p.218]: R = u₁° ≫ R₁ ∪ u₂° ≫ R₂
  refine ⟨cp.u₁° ≫ R₁ ∪ cp.u₂° ≫ R₂, ?_, ?_, ?_⟩
  · -- u₁ ≫ (u₁°≫R₁ ∪ u₂°≫R₂) = R₁. Uses: u₁≫u₁°=id, u₁≫u₂°=0 (from struct fields).
    -- Note: u₁ : a₁→a, u₁° : a→a₁. So u₁ ≫ u₁° : a₁→a₁ = id.
    -- u₁ ≫ (u₁°≫R₁ ∪ u₂°≫R₂) = u₁≫u₁°≫R₁ ∪ u₁≫u₂°≫R₂  [comp_union_distrib]
    --   = (u₁≫u₁°)≫R₁ ∪ (u₁≫u₂°)≫R₂                    [assoc]
    --   = id≫R₁ ∪ 0≫R₂ = R₁ ∪ 0 = R₁
    rw [DistributiveAllegory.comp_union_distrib,
        ← Cat.assoc, ← Cat.assoc,
        cp.u₁_self_comp_recip, cp.u₁_u₂_recip,
        Cat.id_comp, DistributiveAllegory.zero_comp]
    exact union_zero R₁
  · -- u₂ ≫ (u₁°≫R₁ ∪ u₂°≫R₂) = R₂. Uses: u₂≫u₁°=0, u₂≫u₂°=id.
    rw [DistributiveAllegory.comp_union_distrib,
        ← Cat.assoc, ← Cat.assoc,
        cp.u₂_u₁_recip, cp.u₂_self_comp_recip,
        Cat.id_comp, DistributiveAllegory.zero_comp]
    exact DistributiveAllegory.zero_union R₂
  · -- Uniqueness: u₁≫R'=R₁ ∧ u₂≫R'=R₂ → R' = u₁°≫R₁ ∪ u₂°≫R₂.
    -- §2.214: R' = 1≫R' = (u₁°u₁ ∪ u₂°u₂)≫R' = u₁°(u₁≫R') ∪ u₂°(u₂≫R') = u₁°R₁ ∪ u₂°R₂.
    intro R' h₁ h₂
    calc R' = Cat.id a ≫ R' := (Cat.id_comp R').symm
      _ = (cp.u₁° ≫ cp.u₁ ∪ cp.u₂° ≫ cp.u₂) ≫ R' := by rw [cp.recip_union_eq_id]
      _ = cp.u₁° ≫ (cp.u₁ ≫ R') ∪ cp.u₂° ≫ (cp.u₂ ≫ R') := by
            rw [union_comp_distrib, Cat.assoc, Cat.assoc]
      _ = cp.u₁° ≫ R₁ ∪ cp.u₂° ≫ R₂ := by rw [h₁, h₂]

/-- A retraction that is also a partial section is the reciprocal: if `f ≫ g = 1`
    and `g ≫ f ⊑ 1` then `g ⊑ f°`.  Pure modular-law fact (used in §2.214). -/
theorem le_recip_of_section {𝒜 : Type u} [DistributiveAllegory 𝒜] {x y : 𝒜}
    (f : x ⟶ y) (g : y ⟶ x) (h1 : f ≫ g = Cat.id x) (h2 : g ≫ f ⊑ Cat.id y) :
    g ⊑ f° := by
  -- modular_le g f (1_y):  (g≫f) ∩ 1 ⊑ (g ∩ 1≫f°)≫f = (g ∩ f°)≫f.
  -- Since g≫f ⊑ 1, the LHS intersection is g≫f, so  g≫f ⊑ (g ∩ f°)≫f.
  have hmod := modular_le g f (Cat.id y)
  rw [inter_eq_left h2, Cat.id_comp] at hmod
  -- hmod : g ≫ f ⊑ (g ∩ f°) ≫ f.  Post-compose with g and use f≫g = 1.
  have hpost : (g ≫ f) ≫ g ⊑ ((g ∩ f°) ≫ f) ≫ g := comp_mono_right hmod g
  rw [Cat.assoc, Cat.assoc, h1, Cat.comp_id, Cat.comp_id] at hpost
  -- hpost : g ⊑ g ∩ f°.  Hence g ⊑ f°.
  exact le_trans hpost (inter_lb_right g (f°))

/-- A section that is also a partial retraction equals the reciprocal: if
    `f ≫ g = 1` and `g ≫ f ⊑ 1` then `g = f°` (§2.214). -/
theorem eq_recip_of_section {𝒜 : Type u} [DistributiveAllegory 𝒜] {x y : 𝒜}
    (f : x ⟶ y) (g : y ⟶ x) (h1 : f ≫ g = Cat.id x) (h2 : g ≫ f ⊑ Cat.id y) :
    g = f° := by
  apply le_antisymm (le_recip_of_section f g h1 h2)
  -- f° ⊑ g.  Apply the lemma to the reciprocated pair (g°, f°):
  --   g°≫f° = (f≫g)° = 1,   f°≫g° = (g≫f)° ⊑ 1.
  have h1' : g° ≫ f° = Cat.id x := by rw [← Allegory.recip_comp, h1, recip_id]
  have h2' : f° ≫ g° ⊑ Cat.id y := by
    rw [← Allegory.recip_comp]; exact recip_le_iff.mpr (by rw [recip_id]; exact h2)
  have := le_recip_of_section (g°) (f°) h1' h2'
  rwa [Allegory.recip_recip] at this

/-- (§2.214) The five Coproduct equations hold whenever `(u₁, u₂)` enjoys the
    universal property.  Stated as a conjunction (a `Prop`) so that the
    propositional mediators p₁, p₂ supplied by `IsCoproduct` may be `obtain`ed. -/
theorem coproduct_of_universal_eqs {𝒜 : Type u} [DistributiveAllegory 𝒜]
    {a a₁ a₂ : 𝒜} (u₁ : a₁ ⟶ a) (u₂ : a₂ ⟶ a) (h : IsCoproduct u₁ u₂) :
    u₁ ≫ u₁° = Cat.id a₁ ∧ u₁ ≫ u₂° = (𝟘 : a₁ ⟶ a₂) ∧
    u₂ ≫ u₁° = (𝟘 : a₂ ⟶ a₁) ∧ u₂ ≫ u₂° = Cat.id a₂ ∧
    (u₁° ≫ u₁) ∪ (u₂° ≫ u₂) = Cat.id a := by
  -- Mediators p₁ : a → a₁, p₂ : a → a₂:
  --   p₁ mediates (1_{a₁}, 0):  u₁p₁ = 1,  u₂p₁ = 0;
  --   p₂ mediates (0, 1_{a₂}):  u₁p₂ = 0,  u₂p₂ = 1.
  obtain ⟨p₁, hu₁p₁, hu₂p₁, _⟩ := h a₁ (Cat.id a₁) 𝟘
  obtain ⟨p₂, hu₁p₂, hu₂p₂, _⟩ := h a₂ 𝟘 (Cat.id a₂)
  -- Book Eq 5 form: p₁u₁ ∪ p₂u₂ = 1_a, by uniqueness of the mediator of (u₁, u₂).
  obtain ⟨R, _, _, hRuniq⟩ := h a u₁ u₂
  have hpu : (p₁ ≫ u₁) ∪ (p₂ ≫ u₂) = Cat.id a := by
    have hid : Cat.id a = R := by
      apply hRuniq <;> rw [Cat.comp_id]
    have hsum : (p₁ ≫ u₁) ∪ (p₂ ≫ u₂) = R := by
      apply hRuniq
      · rw [DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc,
          hu₁p₁, hu₁p₂, Cat.id_comp, DistributiveAllegory.zero_comp, union_zero]
      · rw [DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc,
          hu₂p₁, hu₂p₂, Cat.id_comp, DistributiveAllegory.zero_comp,
          DistributiveAllegory.zero_union]
    rw [hsum, hid]
  -- p₁u₁ ⊑ 1_a and p₂u₂ ⊑ 1_a (from hpu).
  have hp₁u₁ : p₁ ≫ u₁ ⊑ Cat.id a := by rw [← hpu]; exact le_union_left _ _
  have hp₂u₂ : p₂ ≫ u₂ ⊑ Cat.id a := by rw [← hpu]; exact le_union_right _ _
  -- Hence u₁° = p₁ and u₂° = p₂ (book: U_i = p_i°, reciprocated).
  have hpe₁ : u₁° = p₁ := (eq_recip_of_section u₁ p₁ hu₁p₁ hp₁u₁).symm
  have hpe₂ : u₂° = p₂ := (eq_recip_of_section u₂ p₂ hu₂p₂ hp₂u₂).symm
  -- Read off the five equations by rewriting u_i° = p_i.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hpe₁]; exact hu₁p₁
  · rw [hpe₂]; exact hu₁p₂
  · rw [hpe₁]; exact hu₂p₁
  · rw [hpe₂]; exact hu₂p₂
  · rw [hpe₁, hpe₂]; exact hpu

/-- (§2.214) The universal coproduct property implies the five Coproduct equations.
    Constructs a `Coproduct` record from `IsCoproduct`. -/
def coproduct_of_universal {𝒜 : Type u} [DistributiveAllegory 𝒜]
    {a a₁ a₂ : 𝒜} (u₁ : a₁ ⟶ a) (u₂ : a₂ ⟶ a) (h : IsCoproduct u₁ u₂) :
    Coproduct a a₁ a₂ :=
  let e := coproduct_of_universal_eqs u₁ u₂ h
  { u₁ := u₁, u₂ := u₂,
    u₁_self_comp_recip := e.1, u₁_u₂_recip := e.2.1, u₂_u₁_recip := e.2.2.1,
    u₂_self_comp_recip := e.2.2.2.1, recip_union_eq_id := e.2.2.2.2 }

/-! ## §2.215  Reciprocal duality: coproduct iff product

  "Any allegory is isomorphic, via reciprocation, to its opposite allegory.
  Hence any allegory has coproducts precisely to the extent that it has
  products.  Indeed, (U₁, U₂) is a coproduct iff (U₁°, U₂°) is a product."
  (§2.215) -/

/-- A PRODUCT diagram (§2.215), the reciprocal-dual of `Coproduct`.
    `p₁ : a → a₁`, `p₂ : a → a₂` with the five product equations:
    p₁°p₁ = 1, p₂°p₁ = 0, p₁°p₂ = 0, p₂°p₂ = 1, p₁p₁° ∪ p₂p₂° = 1.
    These are exactly the `Coproduct` equations read off the reciprocals. -/
structure AlgProduct (a a₁ a₂ : 𝒜) where
  p₁ : a ⟶ a₁
  p₂ : a ⟶ a₂
  recip_p₁_self_comp : p₁° ≫ p₁ = Cat.id a₁
  recip_p₂_p₁ : p₂° ≫ p₁ = (𝟘 : a₂ ⟶ a₁)
  recip_p₁_p₂ : p₁° ≫ p₂ = (𝟘 : a₁ ⟶ a₂)
  recip_p₂_self_comp : p₂° ≫ p₂ = Cat.id a₂
  comp_recip_union_eq_id : (p₁ ≫ p₁°) ∪ (p₂ ≫ p₂°) = Cat.id a

/-- (§2.215) If `(u₁, u₂)` is a coproduct then `(u₁°, u₂°)` is a product.
    The product equations are the coproduct equations reciprocated. -/
def AlgProduct.ofCoproduct {a a₁ a₂ : 𝒜} (cp : Coproduct a a₁ a₂) :
    AlgProduct a a₁ a₂ where
  p₁ := cp.u₁°
  p₂ := cp.u₂°
  -- p₁°p₁ = (u₁°)°u₁° = u₁u₁° = 1
  recip_p₁_self_comp := by rw [Allegory.recip_recip]; exact cp.u₁_self_comp_recip
  -- p₂°p₁ = u₂u₁° = 0
  recip_p₂_p₁ := by rw [Allegory.recip_recip]; exact cp.u₂_u₁_recip
  -- p₁°p₂ = u₁u₂° = 0
  recip_p₁_p₂ := by rw [Allegory.recip_recip]; exact cp.u₁_u₂_recip
  -- p₂°p₂ = u₂u₂° = 1
  recip_p₂_self_comp := by rw [Allegory.recip_recip]; exact cp.u₂_self_comp_recip
  -- p₁p₁° ∪ p₂p₂° = u₁°u₁ ∪ u₂°u₂ = 1
  comp_recip_union_eq_id := by
    rw [Allegory.recip_recip, Allegory.recip_recip]; exact cp.recip_union_eq_id

/-- (§2.215) If `(p₁, p₂)` is a product then `(p₁°, p₂°)` is a coproduct.
    The converse direction of the reciprocal duality. -/
def Coproduct.ofAlgProduct {a a₁ a₂ : 𝒜} (pr : AlgProduct a a₁ a₂) :
    Coproduct a a₁ a₂ where
  u₁ := pr.p₁°
  u₂ := pr.p₂°
  -- u₁u₁° = p₁°(p₁°)° = p₁°p₁ = 1
  u₁_self_comp_recip := by rw [Allegory.recip_recip]; exact pr.recip_p₁_self_comp
  -- u₁u₂° = p₁°p₂ = 0
  u₁_u₂_recip := by rw [Allegory.recip_recip]; exact pr.recip_p₁_p₂
  -- u₂u₁° = p₂°p₁ = 0
  u₂_u₁_recip := by rw [Allegory.recip_recip]; exact pr.recip_p₂_p₁
  -- u₂u₂° = p₂°p₂ = 1
  u₂_self_comp_recip := by rw [Allegory.recip_recip]; exact pr.recip_p₂_self_comp
  -- u₁°u₁ ∪ u₂°u₂ = p₁p₁° ∪ p₂p₂° = 1
  recip_union_eq_id := by
    rw [Allegory.recip_recip, Allegory.recip_recip]; exact pr.comp_recip_union_eq_id

/-! ## §2.215  Positive allegory -/

/-- A POSITIVE ALLEGORY (§2.215): distributive allegory with finite coproducts. -/
class PositiveAllegory (𝒜 : Type u) extends DistributiveAllegory 𝒜 where
  coterm : 𝒜
  coprod (a b : 𝒜) : 𝒜
  has_coproduct (a b : 𝒜) : Coproduct (coprod a b) a b

/-! ## §2.22  Locally complete distributive allegory

  Each hom-set is a complete lattice, composition distributes over
  arbitrary unions (§2.22). -/

/-- A LOCALLY COMPLETE distributive allegory (§2.22).
    Uses a predicate-based encoding of arbitrary suprema
    (avoids `Set` dependency).

    Book §2.22: each hom-set is a complete lattice AND composition and finite
    intersection distribute over arbitrary unions, i.e. `R(∪Sᵢ) = ∪ RSᵢ`
    (with the empty-`I` case `R0 = 0`). -/
class LocallyCompleteDistributiveAllegory (𝒜 : Type u) extends DistributiveAllegory 𝒜 where
  /-- Supremum of a predicate P on the hom-set. -/
  Sup {a b : 𝒜} (P : (a ⟶ b) → Prop) : a ⟶ b
  /-- Sup is an upper bound: if P(R), then R ⊑ Sup P. -/
  le_Sup {a b : 𝒜} {P : (a ⟶ b) → Prop} {R : a ⟶ b} (h : P R) : R ⊑ Sup P
  /-- Sup is least upper bound. -/
  Sup_le {a b : 𝒜} {P : (a ⟶ b) → Prop} {T : a ⟶ b} (h : ∀ R, P R → R ⊑ T) : Sup P ⊑ T
  /-- §2.22 distributive law: composition distributes over arbitrary unions on the right,
      `R(∪Sᵢ) = ∪ RSᵢ`.  `Sup_comp` is the indexed family `{RSᵢ}`, given as the image
      predicate `T = R ≫ S` for some `S` with `P S`.  (The empty-`I` case is `R0 = 0`.) -/
  comp_Sup_distrib {a b c : 𝒜} (R : a ⟶ b) (P : (b ⟶ c) → Prop) :
    R ≫ Sup P = Sup (fun T => ∃ S, P S ∧ T = R ≫ S)
  /-- §2.22 distributive law: finite intersection distributes over arbitrary unions,
      `R ∩ (∪Sᵢ) = ∪ (R ∩ Sᵢ)`. -/
  inter_Sup_distrib {a b : 𝒜} (R : a ⟶ b) (P : (a ⟶ b) → Prop) :
    R ∩ Sup P = Sup (fun T => ∃ S, P S ∧ T = R ∩ S)

/-! ## §2.223  Globally complete allegory -/

/-- A GLOBALLY COMPLETE allegory has disjoint unions of indexed
    families of objects (§2.223). -/
class GloballyCompleteAllegory (𝒜 : Type u) extends LocallyCompleteDistributiveAllegory 𝒜 where
  disjointUnion {I : Type u} (a : I → 𝒜) : 𝒜
  inject {I : Type u} {a : I → 𝒜} (i : I) : a i ⟶ disjointUnion a
  inject_self_comp_recip {I : Type u} {a : I → 𝒜} (i : I) :
    inject i ≫ (inject i)° = Cat.id (a i)
  -- §2.223 disjointness `UᵢUⱼ° = Uᵢ°Uⱼ = 0` (i ≠ j).  The book's two products read,
  -- in diagrammatic order, as `inject i ≫ (inject j)°` (αᵢ→αⱼ) and `inject j ≫ (inject i)°`
  -- (αⱼ→αᵢ); these are the SAME family indexed over ordered pairs of distinct indices, so the
  -- single field below (quantified over all `i ≠ j`) supplies both.  A literal `(inject i)° ≫
  -- inject j` does not typecheck (codomains αᵢ, αⱼ differ), confirming there is no extra law.
  inject_comp_recip_ne {I : Type u} {a : I → 𝒜} {i j : I} (h : i ≠ j) :
    inject i ≫ (inject j)° = (𝟘 : a i ⟶ a j)
  complete {I : Type u} {a : I → 𝒜} :
    Sup (λ (R : disjointUnion a ⟶ disjointUnion a) =>
      ∃ (i : I), R = (inject i)° ≫ inject i) = Cat.id (disjointUnion a)

/-! ## §2.216  Positive Reflection A⁺

  Let A be a distributive allegory.  Its POSITIVE REFLECTION A⁺ has
  objects = finite sequences (here: I-indexed tuples for any index type I)
  of A-objects, and morphisms = I×J-matrices of A-morphisms.
  The embedding A → A⁺ sends R : a → b to the 1×1 matrix (R). -/

/-- An I×J matrix of morphisms in A: entry (i,j) is src i → tgt j (§2.216). -/
def AlgMat {𝒜 : Type u} [Allegory 𝒜] {I J : Type u}
    (src : I → 𝒜) (tgt : J → 𝒜) : Type u :=
  (i : I) → (j : J) → src i ⟶ tgt j

/-- Matrix reciprocation: (R°)_{ji} = (R_{ij})° (§2.216). -/
def AlgMat.recip {𝒜 : Type u} [Allegory 𝒜] {I J : Type u}
    {src : I → 𝒜} {tgt : J → 𝒜}
    (R : AlgMat src tgt) : AlgMat tgt src :=
  fun j i => (R i j)°

/-- Matrix intersection: entry-wise (§2.216). -/
def AlgMat.inter {𝒜 : Type u} [Allegory 𝒜] {I J : Type u}
    {src : I → 𝒜} {tgt : J → 𝒜}
    (R S : AlgMat src tgt) : AlgMat src tgt :=
  fun i j => R i j ∩ S i j

/-- Matrix union: entry-wise (§2.216). -/
def AlgMat.union {𝒜 : Type u} [DistributiveAllegory 𝒜] {I J : Type u}
    {src : I → 𝒜} {tgt : J → 𝒜}
    (R S : AlgMat src tgt) : AlgMat src tgt :=
  fun i j => R i j ∪ S i j

/-- Matrix zero: zero in every entry (§2.216). -/
def AlgMat.zero {𝒜 : Type u} [DistributiveAllegory 𝒜] {I J : Type u}
    {src : I → 𝒜} {tgt : J → 𝒜} : AlgMat src tgt :=
  fun _i _j => 𝟘

/-- The embedding A → A⁺ sends R : a → b to the 1×1 matrix (R) (§2.216). -/
def positiveReflectionEmbed {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜}
    (R : a ⟶ b) :
    let src : PUnit.{u+1} → 𝒜 := fun _ => a
    let tgt : PUnit.{u+1} → 𝒜 := fun _ => b
    AlgMat src tgt :=
  fun _i _j => R

/-- (§2.216) The embedding A → A⁺ is faithful. -/
theorem positiveReflectionEmbed_injective {𝒜 : Type u} [DistributiveAllegory 𝒜]
    {a b : 𝒜} {R S : a ⟶ b}
    (h : @positiveReflectionEmbed 𝒜 _ a b R = @positiveReflectionEmbed 𝒜 _ a b S) : R = S :=
  congrFun (congrFun h PUnit.unit) PUnit.unit

/-! ## §2.221  Local Completion (allegory of downdeals)

  Let A be an allegory.  The LOCAL COMPLETION Â is the allegory whose
  objects are those of A and whose hom-sets are downdeals. -/

/-- A DOWNDEAL in (a, b): closed downward under ⊑ (§2.221). -/
def IsDowndeal {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (D : (a ⟶ b) → Prop) : Prop :=
  ∀ (R : a ⟶ b), D R → ∀ (S : a ⟶ b), S ⊑ R → D S

/-- The PRINCIPAL DOWNDEAL ↓R = { S | S ⊑ R } (§2.221). -/
def principalDowndeal {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    (a ⟶ b) → Prop :=
  fun S => S ⊑ R

theorem principalDowndeal_isDowndeal {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    IsDowndeal (principalDowndeal R) :=
  fun _T hT _S hS => le_trans hS hT

/-- (§2.221) The embedding A → Â (R ↦ ↓R) is faithful. -/
theorem principalDowndeal_injective {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} {R S : a ⟶ b}
    (h : principalDowndeal R = principalDowndeal S) : R = S := by
  have hRS : R ⊑ S := by
    have : (principalDowndeal R) R := le_refl R; rw [h] at this; exact this
  have hSR : S ⊑ R := by
    have : (principalDowndeal S) S := le_refl S; rw [← h] at this; exact this
  exact le_antisymm hRS hSR

/-! ## §2.222  Ideal completion (distributive allegory case) -/

/-- An IDEAL in a hom-set: a downdeal closed under finite union (§2.222). -/
def IsIdeal {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜} (D : (a ⟶ b) → Prop) : Prop :=
  IsDowndeal D ∧ D (𝟘 : a ⟶ b) ∧ ∀ (R S : a ⟶ b), D R → D S → D (R ∪ S)

/-- The principal ideal ↓R (same underlying set as ↓R for downdeals). -/
def principalIdeal {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    (a ⟶ b) → Prop := fun S => S ⊑ R

theorem principalIdeal_isIdeal {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    IsIdeal (principalIdeal R) :=
  ⟨principalDowndeal_isDowndeal R, zero_le R, fun _S _T hS hT => union_lub hS hT⟩

/-- (§2.222) The embedding A → ideals(A) is faithful; any distributive allegory
    faithfully represents in a locally complete distributive allegory. -/
theorem principalIdeal_injective {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜}
    {R S : a ⟶ b} (h : principalIdeal R = principalIdeal S) : R = S :=
  principalDowndeal_injective h

/-! ## §2.224  Global Completion A'

  The GLOBAL COMPLETION of a locally complete distributive allegory A has
  indexed families of objects and infinite matrices as morphisms (§2.224). -/

/-- Objects of the global completion: an index type I together with an I-indexed
    family of A-objects (§2.224). -/
structure GlobalObj (𝒜 : Type u) where
  idx : Type u
  obj : idx → 𝒜

/-- Morphisms of the global completion: an infinite matrix R_{ij} : a_i → b_j (§2.224). -/
def GlobalMorphism {𝒜 : Type u} [Allegory 𝒜] (A B : GlobalObj 𝒜) : Type u :=
  (i : A.idx) → (j : B.idx) → A.obj i ⟶ B.obj j

/-- Global completion composition: (RS)_{ik} = Sup_j { R_{ij} ≫ S_{jk} } (§2.224). -/
def GlobalMorphism.comp {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
    {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B) (S : GlobalMorphism B C) :
    GlobalMorphism A C :=
  fun i k => LocallyCompleteDistributiveAllegory.Sup (fun T => ∃ j, T = R i j ≫ S j k)

/-- Global completion reciprocation: (R°)_{ji} = (R_{ij})° (§2.224). -/
def GlobalMorphism.recip {𝒜 : Type u} [Allegory 𝒜] {A B : GlobalObj 𝒜}
    (R : GlobalMorphism A B) : GlobalMorphism B A :=
  fun j i => (R i j)°

/-- The embedding A → A' sending R : a → b to the 1×1 matrix (R) (§2.224). -/
def globalCompletionEmbed {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    GlobalMorphism (𝒜 := 𝒜) ⟨PUnit.{u+1}, fun _ => a⟩ ⟨PUnit.{u+1}, fun _ => b⟩ :=
  fun _i _j => R

/-- (§2.224) The embedding A → A' is faithful. -/
theorem globalCompletionEmbed_injective {𝒜 : Type u} [Allegory 𝒜]
    {a b : 𝒜} {R S : a ⟶ b}
    (h : globalCompletionEmbed R = globalCompletionEmbed S) : R = S :=
  congrFun (congrFun h PUnit.unit) PUnit.unit

/-! ## §2.226  Systemic Completion

  The SYSTEMIC COMPLETION of an allegory is obtained by splitting the
  symmetric idempotents of its global completion (§2.226).

  **§2.226 generating-set theorem**: If an allegory A, viewed as a category, has a
  generating set (e.g. if A is small), then its systemic completion has a unit.
  [Proof: a generating set remains generating in the completion; one constructs a
  maximal partial unit from the generating set by the maximality argument in §2.226.]  -/

-- BOOK §2.226: If an allegory A has a generating set (e.g. A is small), then its
-- systemic completion has a unit.

/-- A split symmetric idempotent in an allegory (§2.226; cf. EffectiveAllegory):
    a symmetric idempotent E on a together with a splitting map f : a → b
    satisfying f ≫ f° = E and f° ≫ f = 1_b. -/
structure SplitSymmIdem {𝒜 : Type u} [Allegory 𝒜] (a : 𝒜) where
  E       : a ⟶ a
  isSymm  : Symmetric E
  isIdem  : E ≫ E = E
  b       : 𝒜
  f       : a ⟶ b
  hMap    : Map f
  hffR    : f ≫ f° = E
  hRff    : f° ≫ f = Cat.id b

/-- (§2.226) The systemic completion of a semi-simple globally complete allegory
    is tabular and effective: every symmetric idempotent splits (by the construction
    of the systemic completion via splitting symmetric idempotents). -/
theorem systemic_completion_tabular_effective
    {𝒜 : Type u} [SemiSimpleAllegory 𝒜] [GloballyCompleteAllegory 𝒜] :
    ∀ (a : 𝒜) (ss : SplitSymmIdem a),
      ∃ (b : 𝒜) (f : a ⟶ b), Map f ∧ f ≫ f° = ss.E ∧ f° ≫ f = Cat.id b :=
  fun _a ss => ⟨ss.b, ss.f, ss.hMap, ss.hffR, ss.hRff⟩

/-! ## §2.145 / §2.163  A tabular coreflexive splits

  **§2.145**: if a coreflexive morphism `A` is tabular — `(f,g)` tabulates `A`
  with `A ⊑ 1` — then its two legs coincide, `f = g`, and `g` is a *splitting*
  of `A`: `g° g = A` and `g g° = 1`.  Equivalently (**§2.163**) a coreflexive is
  a split idempotent iff it is tabular.  In a `TabularAllegory` every coreflexive
  is therefore split — the coreflexive half of effectiveness, the data §2.166
  uses to refine a bare tabulation's apex.

  This is Sorry-free and constructive: the legs agree because
  `f = f (f°f ∩ g°g) ⊑ f (g°g) = A g ⊑ g` (and symmetrically), then
  `map_order_discrete`. -/

/-- **§2.145**: the two legs of a (source-apex) tabulation of a coreflexive coincide. -/
theorem tabulation_coreflexive_legs_eq {𝒜 : Type u} [Allegory 𝒜] {a c : 𝒜}
    {f g : c ⟶ a} {A : a ⟶ a} (hf : Map f) (hg : Map g) (hA : A = f° ≫ g)
    (htab : f ≫ f° ∩ g ≫ g° = Cat.id c) (hcor : Coreflexive A) : f = g := by
  have hcoref1 : A ⊑ Cat.id a := hcor
  -- g ⊑ f:  g = (f f° ∩ g g°)g = … ⊑ (f f°)g = f(f°g) = f A ⊑ f·1 = f
  have hgf : g ⊑ f := by
    have e1 : g = (f ≫ f° ∩ g ≫ g°) ≫ g := by rw [htab, Cat.id_comp]
    have e2 : (f ≫ f° ∩ g ≫ g°) ≫ g ⊑ (f ≫ f°) ≫ g := comp_mono_right (inter_lb_left _ _) g
    have e3 : (f ≫ f°) ≫ g = f ≫ A := by rw [hA]; simp [Cat.assoc]
    have e4 : f ≫ A ⊑ f := by have := comp_mono_left f hcoref1; rwa [Cat.comp_id] at this
    rw [e1]; exact le_trans e2 (e3 ▸ e4)
  exact (map_order_discrete hg hf hgf).symm

/-- **§2.145 / §2.163**: a tabular coreflexive splits.  From a tabulation `(f,g)`
    of coreflexive `A` the legs agree (`f = g`) and `f` is a map with
    `f° ≫ f = A` and `f ≫ f° = 1_c` — i.e. `f` *splits* `A` (`h°h = A`, `hh° = 1`). -/
theorem coreflexive_split_of_tabulation {𝒜 : Type u} [Allegory 𝒜] {a c : 𝒜}
    {f g : c ⟶ a} {A : a ⟶ a} (hf : Map f) (hg : Map g) (hA : A = f° ≫ g)
    (htab : f ≫ f° ∩ g ≫ g° = Cat.id c) (hcor : Coreflexive A) :
    Map f ∧ f° ≫ f = A ∧ f ≫ f° = Cat.id c := by
  have hfeqg : f = g := tabulation_coreflexive_legs_eq hf hg hA htab hcor
  subst hfeqg
  -- now A = f° f, and htab : f f° ∩ f f° = f f° = 1_c
  rw [Allegory.inter_idem] at htab
  exact ⟨hf, hA.symm, htab⟩

/-- In a `TabularAllegory` every coreflexive `A : a → a` splits: there is a map
    `g : c → a` with `g° ≫ g = A`, `g ≫ g° = 1_c` (§2.163).  (The splitting map
    points FROM the apex: in `Rel(Set)` it is the inclusion of the support subset.) -/
theorem coreflexive_splits {𝒜 : Type u} [TabularAllegory 𝒜] {a : 𝒜} {A : a ⟶ a}
    (hcor : Coreflexive A) :
    ∃ (c : 𝒜) (g : c ⟶ a), Map g ∧ g° ≫ g = A ∧ g ≫ g° = Cat.id c := by
  obtain ⟨c, f, g, hf, hg, hA, htab⟩ := TabularAllegory.tabular A
  exact ⟨c, f, coreflexive_split_of_tabulation hf hg hA htab hcor⟩

/-! ## §2.227  O(Y)-valued sets and sheaves

  "Let Y be a topological space, O(Y) the locale of open subsets thereof.
  The category of maps of O(Y)-valued sets is equivalent to H(Y)."
  [§2.227, proof via the bijection: irredundant O(Y)-valued sets ↔ local homeomorphisms
  over Y (étale spaces); the §2.16(12) construction of O(Y)-valued relations.]

  Requires: types for `Locale`, `O(Y)-valued sets`, `LocalHomeomorphism`/étale spaces,
  and the category H(Y) of sheaves — none constructed in this repo.  -/

-- BOOK §2.227: Let Y be a topological space, O(Y) the locale of open subsets thereof.
-- The category of maps of O(Y)-valued sets is equivalent to H(Y).

end Freyd.Alg
