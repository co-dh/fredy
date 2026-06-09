/-
  Freyd & Scedrov, *Categories and Allegories* §2.1  Basic definitions.

  §2.1  RECIPROCATION, COMPOSITION, INTERSECTION, semidistributivity, law of modularity
  §2.11 ALLEGORY
  §2.111 For any regular category C, Rel(C) is an allegory
  §2.12 REFLEXIVE, SYMMETRIC, TRANSITIVE, COREFLEXIVE
  §2.122 DOMAIN
  §2.13 ENTIRE, SIMPLE, MAP
  §2.14 TABULATES, TABULAR ALLEGORY
  §2.15 PARTIAL UNIT, UNIT, UNITARY ALLEGORY
  §2.16 PRE-TABULAR, EFFECTIVE, SEMI-SIMPLE
-/

import Fredy.S1_1


universe v u

namespace Freyd

/-! ## §2.11  Allegory

  An ALLEGORY is a category with a unary operation R° (reciprocation)
  and a binary partial operation R ∩ S (intersection) defined whenever
  □R = □S and R□ = S□.

  The equational axioms: monoid for composition, semi-lattice for
  intersection, anti-involution for reciprocation, semi-distributivity,
  and the law of modularity. -/

/-- An ALLEGORY (§2.11): category with reciprocation (°), intersection (∩),
    semi-distributivity, and the modular law. -/
class Allegory (𝒜 : Type u) extends Cat.{v} 𝒜 where
  /-- RECIPROCATION: R° : b → a when R : a → b. -/
  recip {a b : 𝒜} (R : a ⟶ b) : b ⟶ a
  /-- INTERSECTION: R ∩ S : a → b when R, S : a → b. -/
  inter {a b : 𝒜} (R S : a ⟶ b) : a ⟶ b

  /-- (R°)° = R (§2.11). -/
  recip_recip {a b : 𝒜} (R : a ⟶ b) : recip (recip R) = R
  /-- (RS)° = S°R° (§2.11). -/
  recip_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) : recip (R ≫ S) = recip S ≫ recip R
  /-- (R ∩ S)° = R° ∩ S° (§2.11). -/
  recip_inter {a b : 𝒜} (R S : a ⟶ b) : recip (inter R S) = inter (recip R) (recip S)

  /-- R ∩ R = R (§2.11). -/
  inter_idem {a b : 𝒜} (R : a ⟶ b) : inter R R = R
  /-- R ∩ S = S ∩ R (§2.11). -/
  inter_comm {a b : 𝒜} (R S : a ⟶ b) : inter R S = inter S R
  /-- R ∩ (S ∩ T) = (R ∩ S) ∩ T (§2.11). -/
  inter_assoc {a b : 𝒜} (R S T : a ⟶ b) : inter R (inter S T) = inter (inter R S) T

  /-- SEMI-DISTRIBUTIVITY: R(S ∩ T) = RS ∩ R(S ∩ T) ∩ RT (§2.11).
      Equivalent to R(S ∩ T) ⊑ RS ∩ RT. -/
  semidistrib {a b c : 𝒜} (R : a ⟶ b) (S T : b ⟶ c) :
    R ≫ inter S T = inter (inter (R ≫ S) (R ≫ inter S T)) (R ≫ T)

  /-- MODULAR LAW: RS ∩ T = (RS ∩ T) ∩ (R ∩ TS°)S (§2.11).
      Equivalent to RS ∩ T ⊑ (R ∩ TS°)S. -/
  modular {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    inter (R ≫ S) T = inter (inter (R ≫ S) T) ((inter R (T ≫ recip S)) ≫ S)

/-! ### Notation for allegory operations -/

/-- Reciprocation notation R° -/
postfix:max "°" => Allegory.recip

/-- Intersection notation R ∩ S -/
infixl:70 " ∩ " => Allegory.inter

/-- The ALLEGORY ORDER: R ⊑ S iff R = R ∩ S (§2.11).
    In the book, this is denoted R ⊂ S. -/
def le {a b : 𝒜} [Allegory 𝒜] (R S : a ⟶ b) : Prop :=
  R ∩ S = R

infix:50 " ⊑ " => le

end Freyd

namespace Freyd

variable {𝒜 : Type u} [Allegory 𝒜]

/-! ### Order properties derived from semi-lattice equations -/

theorem inter_eq_left {a b : 𝒜} {R S : a ⟶ b} (h : R ⊑ S) : R ∩ S = R := h

theorem le_refl {a b : 𝒜} (R : a ⟶ b) : R ⊑ R := by
  dsimp [le]; rw [Allegory.inter_idem]

theorem le_trans {a b : 𝒜} {R S T : a ⟶ b} (hRS : R ⊑ S) (hST : S ⊑ T) : R ⊑ T := by
  dsimp [le] at hRS hST ⊢
  calc
    R ∩ T = (R ∩ S) ∩ T := by rw [hRS]
    _ = R ∩ (S ∩ T) := by rw [Allegory.inter_assoc]
    _ = R ∩ S := by rw [hST]
    _ = R := hRS

theorem le_antisymm {a b : 𝒜} {R S : a ⟶ b} (hRS : R ⊑ S) (hSR : S ⊑ R) : R = S := by
  dsimp [le] at hRS hSR
  calc
    R = R ∩ S := by rw [hRS]
    _ = S ∩ R := by rw [Allegory.inter_comm]
    _ = S := by rw [hSR]

theorem inter_lb_left {a b : 𝒜} (R S : a ⟶ b) : R ∩ S ⊑ R := by
  dsimp [le]
  calc
    (R ∩ S) ∩ R = R ∩ (R ∩ S) := by
      rw [Allegory.inter_comm (R ∩ S) R, Allegory.inter_comm R S]
    _ = (R ∩ R) ∩ S := by rw [Allegory.inter_assoc]
    _ = R ∩ S := by rw [Allegory.inter_idem]

theorem inter_lb_right {a b : 𝒜} (R S : a ⟶ b) : R ∩ S ⊑ S := by
  rw [Allegory.inter_comm R S]; exact inter_lb_left S R

theorem le_inter {a b : 𝒜} {R S T : a ⟶ b} (hRS : R ⊑ S) (hRT : R ⊑ T) : R ⊑ S ∩ T := by
  dsimp [le] at hRS hRT ⊢
  calc
    R ∩ (S ∩ T) = (R ∩ S) ∩ T := by rw [Allegory.inter_assoc]
    _ = R ∩ T := by rw [hRS]
    _ = R := hRT

/-! ### Derived order properties for reciprocation and composition -/

/-- Reciprocation preserves order: R ⊑ S → R° ⊑ S° (§2.11). -/
theorem recip_mono {a b : 𝒜} {R S : a ⟶ b} (h : R ⊑ S) : R° ⊑ S° := by
  dsimp [le] at h ⊢
  calc
    R° ∩ S° = (R ∩ S)° := by rw [← Allegory.recip_inter]
    _ = R° := by rw [h]

/-- Composition preserves order in the second argument (Horn sentence, §2.11). -/
theorem comp_mono_left {a b c : 𝒜} {S T : b ⟶ c} (R : a ⟶ b) (hST : S ⊑ T) : R ≫ S ⊑ R ≫ T := by
  dsimp [le] at hST ⊢
  have h := Allegory.semidistrib R S T
  -- h: R ≫ (S ∩ T) = (R ≫ S ∩ R ≫ (S ∩ T)) ∩ R ≫ T
  -- hST: S ∩ T = S
  calc
    (R ≫ S) ∩ (R ≫ T) = (R ≫ (S ∩ T)) ∩ (R ≫ T) := by rw [hST]
    _ = R ≫ (S ∩ T) := by
      rw [h]
      -- (R ≫ S ∩ R ≫ (S ∩ T)) ∩ R ≫ T ∩ R ≫ T = (R ≫ S ∩ R ≫ (S ∩ T)) ∩ R ≫ T
      -- by idempotence of ∩ on (R ≫ T)
      rw [← Allegory.inter_assoc, Allegory.inter_idem, h]
    _ = R ≫ S := by rw [hST]

/-- Composition preserves order in the first argument. -/
theorem comp_mono_right {a b c : 𝒜} {R₁ R₂ : a ⟶ b} (h : R₁ ⊑ R₂) (S : b ⟶ c) : R₁ ≫ S ⊑ R₂ ≫ S := by
  have h_recip : R₁° ⊑ R₂° := recip_mono h
  have h_comp : S° ≫ R₁° ⊑ S° ≫ R₂° := comp_mono_left S° h_recip
  -- (R₁ ≫ S)°° = R₁ ≫ S, similarly for R₂
  -- (R₁ ≫ S)° = S° ≫ R₁°, similarly for R₂
  -- So: R₁ ≫ S = (S° ≫ R₁°)° ⊑ (S° ≫ R₂°)° = R₂ ≫ S
  have h_eq1 : R₁ ≫ S = (S° ≫ R₁°)° := by
    rw [← Allegory.recip_recip (R₁ ≫ S), Allegory.recip_comp R₁ S]
  have h_eq2 : R₂ ≫ S = (S° ≫ R₂°)° := by
    rw [← Allegory.recip_recip (R₂ ≫ S), Allegory.recip_comp R₂ S]
  rw [h_eq1, h_eq2]
  exact recip_mono h_comp

/-! ### The modular law in its order form -/

/-- The modular law in order form: RS ∩ T ⊑ (R ∩ TS°)S (§2.11). -/
theorem modular_le {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S) ∩ T ⊑ (R ∩ T ≫ S°) ≫ S := by
  dsimp [le]
  rw [Allegory.modular R S T, ← Allegory.inter_assoc, Allegory.inter_idem]

/-! ## §2.12  Reflexive, symmetric, transitive, coreflexive -/

/-- R is REFLEXIVE if 1 ⊑ R (§2.12). -/
def Reflexive {a : 𝒜} (R : a ⟶ a) : Prop := Cat.id a ⊑ R

/-- R is SYMMETRIC if R° ⊑ R (§2.12).  Equivalent to R = R°. -/
def Symmetric {a : 𝒜} (R : a ⟶ a) : Prop := R° ⊑ R

/-- R is TRANSITIVE if RR ⊑ R (§2.12). -/
def Transitive {a : 𝒜} (R : a ⟶ a) : Prop := R ≫ R ⊑ R

/-- R is COREFLEXIVE if R ⊑ 1 (§2.12). -/
def Coreflexive {a : 𝒜} (R : a ⟶ a) : Prop := R ⊑ Cat.id a

/-! ### Symmetric iff R = R° -/

theorem symmetric_eq {a : 𝒜} {R : a ⟶ a} (hSym : Symmetric R) : R° = R :=
  le_antisymm hSym <| by
    calc
      R = (R°)° := by rw [Allegory.recip_recip]
      _ ⊑ R° := recip_mono hSym

theorem symmetric_iff {a : 𝒜} (R : a ⟶ a) : Symmetric R ↔ R° = R := by
  constructor
  · exact symmetric_eq
  · intro h; dsimp [Symmetric, le]; rw [h, Allegory.inter_idem]

/-- Reflexive and transitive imply idempotent (§2.12). -/
theorem reflexive_transitive_idempotent {a : 𝒜} {R : a ⟶ a}
    (hR : Reflexive R) (hT : Transitive R) : R ≫ R = R := by
  apply le_antisymm hT
  dsimp [Reflexive, le] at hR
  calc
    R = (Cat.id a) ≫ R := by rw [Cat.id_comp]
    _ ⊑ R ≫ R := comp_mono_right hR R

/-! ### Coreflexive properties -/

/-- Coreflexive implies symmetric idempotent (§2.12). -/
theorem coreflexive_symmetric_idempotent {a : 𝒜} {R : a ⟶ a} (h : Coreflexive R) :
    Symmetric R ∧ R ≫ R = R := by
  sorry

/-! ## §2.121  Coreflexive composition

  For coreflexive morphisms, AB = A ∩ B (§2.121). -/
theorem coreflexive_comp_eq_inter {a : 𝒜} {A B : a ⟶ a} (hA : Coreflexive A) (hB : Coreflexive B) :
    A ≫ B = A ∩ B := by
  sorry

/-! ## §2.122  Domain -/

/-- The DOMAIN of R, denoted %mR in the book: 1 ∩ RR° (§2.122). -/
def dom {a b : 𝒜} (R : a ⟶ b) : a ⟶ a := Cat.id a ∩ R ≫ R°

/-- Domain is coreflexive (§2.122). -/
theorem dom_coreflexive {a b : 𝒜} (R : a ⟶ b) : Coreflexive (dom R) :=
  inter_lb_left (Cat.id a) (R ≫ R°)

/-! ## §2.124  Domain of intersection -/

/-- dom(R ∩ S) = 1 ∩ SR° (§2.124). -/
theorem dom_inter {a b : 𝒜} (R S : a ⟶ b) : dom (R ∩ S) = Cat.id a ∩ S ≫ R° := by
  sorry

/-! ## §2.13  Entire, simple, map

  R : a → b is entire if dom R = 1_a.
  R is simple if R°R ⊑ 1_b (note: target b, since R°R : b → b).
  R is a map if it is entire and simple.  §2.13. -/

/-- R is ENTIRE if dom R = 1_a; equivalently 1_a ⊑ RR° (§2.13). -/
def Entire {a b : 𝒜} (R : a ⟶ b) : Prop := dom R = Cat.id a

/-- R is SIMPLE if R°R ⊑ 1_b (§2.13).
    Note: R°R : b → b, so we compare to id_b. -/
def Simple {a b : 𝒜} (R : a ⟶ b) : Prop := R° ≫ R ⊑ Cat.id b

/-- R is a MAP if it is entire and simple (§2.13). -/
def Map {a b : 𝒜} (R : a ⟶ b) : Prop := Entire R ∧ Simple R

/-! ## §2.133  Order on maps is discrete -/

theorem map_order_discrete {a b : 𝒜} {f g : a ⟶ b} (hf : Map f) (hg : Map g) (h : f ⊑ g) : f = g := by
  sorry

/-! ## §2.134  Reciprocation on maps -/

theorem map_recip_is_inverse {a b : 𝒜} {f : a ⟶ b} (hf : Map f) (hfo : Map (f°)) :
    f ≫ f° = Cat.id a ∧ f° ≫ f = Cat.id b := by
  sorry

/-! ## §2.14  Tabulation

  A pair of maps f : a → c, g : b → c (common TARGET c) TABULATES
  R : a → b if R = f g° and f°f ∩ g°g = 1_c.  §2.14. -/

/-- A pair of maps f : a → c, g : b → c (common TARGET c) TABULATES
    R : a → b if R = f ≫ g° and f° ≫ f ∩ g° ≫ g = id_c (§2.14). -/
def Tabulates {a b c : 𝒜} (f : a ⟶ c) (g : b ⟶ c) (R : a ⟶ b) : Prop :=
  Map f ∧ Map g ∧ R = f ≫ g° ∧ f° ≫ f ∩ g° ≫ g = Cat.id c

/-- R is TABULAR if it has a tabulation (§2.14). -/
def Tabular {a b : 𝒜} (R : a ⟶ b) : Prop :=
  ∃ (c : 𝒜) (f : a ⟶ c) (g : b ⟶ c), Tabulates f g R

/-- A TABULAR ALLEGORY is one where every morphism is tabular (§2.14). -/
class TabularAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  tabular {a b : 𝒜} (R : a ⟶ b) : Tabular R

/-! ## §2.141  Monic pair in Map(A)

  If f, g : a → c (same source and target) are maps and ff° ∩ gg° = 1,
  then (f, g) is a monic pair in Map(A). -/
theorem tabulates_monic_pair {a c : 𝒜} {f g : a ⟶ c} (hf : Map f) (hg : Map g)
    (h : f ≫ f° ∩ g ≫ g° = Cat.id a) :
    ∀ (h₁ h₂ : a ⟶ a), Map h₁ → Map h₂ → h₁ ≫ f = h₂ ≫ f → h₁ ≫ g = h₂ ≫ g → h₁ = h₂ := by
  sorry

/-! ## §2.15  Unit -/

/-- T is a PARTIAL UNIT if 1_T is the maximum endomorphism on T (§2.15). -/
def PartialUnit (T : 𝒜) : Prop := ∀ (R : T ⟶ T), R ⊑ Cat.id T

/-- T is a UNIT if it is a partial unit and every object is the source of
    an entire morphism to T (§2.15). -/
def IsUnit (T : 𝒜) : Prop :=
  PartialUnit T ∧ ∀ (a : 𝒜), ∃ (R : a ⟶ T), Entire R

/-- A UNITARY ALLEGORY has a unit (§2.15). -/
class UnitaryAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  unit_obj : 𝒜
  unit_prop : IsUnit unit_obj

/-! ## §2.16  Pre-tabular, effective, semi-simple -/

/-- A PRE-TABULAR allegory: every morphism is contained in a tabular one (§2.165). -/
class PreTabularAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  pre_tabular {a b : 𝒜} (R : a ⟶ b) : ∃ (S : a ⟶ b), R ⊑ S ∧ Tabular S

/-- An EFFECTIVE ALLEGORY: tabular + every symmetric idempotent splits (§2.167, §2.169).
    A symmetric idempotent E : a → a splits as E = f ≫ f° where f : a → c is a map
    and f° ≫ f = id_c. -/
class EffectiveAllegory (𝒜 : Type u) extends TabularAllegory 𝒜 where
  split_symmetric_idempotent {a : 𝒜} (E : a ⟶ a) :
    Symmetric E → E ≫ E = E → ∃ (c : 𝒜) (f : a ⟶ c), Map f ∧ f ≫ f° = E ∧ f° ≫ f = Cat.id c

/-- A SEMI-SIMPLE morphism factors as F ≫ G° with F, G simple (§2.16(10)).
    F : a → c, G : b → c have a common target c. -/
def SemiSimple {a b : 𝒜} (R : a ⟶ b) : Prop :=
  ∃ (c : 𝒜) (F : a ⟶ c) (G : b ⟶ c), Simple F ∧ Simple G ∧ R = F ≫ G°

/-- A SEMI-SIMPLE ALLEGORY: every morphism is semi-simple (§2.16(10)). -/
class SemiSimpleAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  semi_simple {a b : 𝒜} (R : a ⟶ b) : SemiSimple R

end Freyd
