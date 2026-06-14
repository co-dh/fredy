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
    (avoids `Set` dependency). -/
class LocallyCompleteDistributiveAllegory (𝒜 : Type u) extends DistributiveAllegory 𝒜 where
  /-- Supremum of a predicate P on the hom-set. -/
  Sup {a b : 𝒜} (P : (a ⟶ b) → Prop) : a ⟶ b
  /-- Sup is an upper bound: if P(R), then R ⊑ Sup P. -/
  le_Sup {a b : 𝒜} {P : (a ⟶ b) → Prop} {R : a ⟶ b} (h : P R) : R ⊑ Sup P
  /-- Sup is least upper bound. -/
  Sup_le {a b : 𝒜} {P : (a ⟶ b) → Prop} {T : a ⟶ b} (h : ∀ R, P R → R ⊑ T) : Sup P ⊑ T

/-! ## §2.223  Globally complete allegory -/

/-- A GLOBALLY COMPLETE allegory has disjoint unions of indexed
    families of objects (§2.223). -/
class GloballyCompleteAllegory (𝒜 : Type u) extends LocallyCompleteDistributiveAllegory 𝒜 where
  disjointUnion {I : Type u} (a : I → 𝒜) : 𝒜
  inject {I : Type u} {a : I → 𝒜} (i : I) : a i ⟶ disjointUnion a
  inject_self_comp_recip {I : Type u} {a : I → 𝒜} (i : I) :
    inject i ≫ (inject i)° = Cat.id (a i)
  inject_comp_recip_ne {I : Type u} {a : I → 𝒜} {i j : I} (h : i ≠ j) :
    inject i ≫ (inject j)° = (𝟘 : a i ⟶ a j)
  complete {I : Type u} {a : I → 𝒜} :
    Sup (λ (R : disjointUnion a ⟶ disjointUnion a) =>
      ∃ (i : I), R = (inject i)° ≫ inject i) = Cat.id (disjointUnion a)

end Freyd.Alg
