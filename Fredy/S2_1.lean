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
import Fredy.S1_41   -- for Freyd.IsIso, Freyd.Monic (§2.135, §2.144, §2.145)


universe v u

namespace Freyd.Alg

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
postfix:max (name := allegoryRecip) "°" => Allegory.recip

/-- Intersection notation R ∩ S -/
infixl:70 " ∩ " => Allegory.inter

/-- The ALLEGORY ORDER: R ⊑ S iff R = R ∩ S (§2.11).
    In the book, this is denoted R ⊂ S. -/
def le {a b : 𝒜} [Allegory 𝒜] (R S : a ⟶ b) : Prop :=
  R ∩ S = R

infix:50 " ⊑ " => le

end Freyd.Alg

namespace Freyd.Alg

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

/-- Reciprocation is its own Galois adjoint: R° ⊑ S ↔ R ⊑ S° (§2.11). -/
theorem recip_le_iff {a b : 𝒜} {R : a ⟶ b} {S : b ⟶ a} : R° ⊑ S ↔ R ⊑ S° :=
  ⟨fun h => by simpa [Allegory.recip_recip] using recip_mono h,
   fun h => by simpa [Allegory.recip_recip] using recip_mono h⟩

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

/-! ### Identity is self-reciprocal -/

/-- 1° = 1: derived from `recip_comp` and `recip_recip` (§2.11). -/
theorem recip_id {a : 𝒜} : (Cat.id a)° = Cat.id a := by
  calc
    (Cat.id a)° = ((Cat.id a)°)°° := by rw [Allegory.recip_recip]
    _ = ((Cat.id a ≫ (Cat.id a)°)°)° := by rw [Cat.id_comp]
    _ = (((Cat.id a)°)° ≫ (Cat.id a)°)° := by rw [Allegory.recip_comp]
    _ = (Cat.id a ≫ (Cat.id a)°)° := by rw [Allegory.recip_recip]
    _ = ((Cat.id a)°)° := by rw [Cat.id_comp]
    _ = Cat.id a := by rw [Allegory.recip_recip]

/-! ### Coreflexive properties -/

/-- Coreflexive implies symmetric idempotent (§2.12).
    Proof chain: R ⊑ RR°R (modular law) ⊑ R° (since R ⊑ 1), so R ⊑ R°.
    Taking ° gives R° ⊑ R, hence symmetric.  Idempotent: R = R° gives
    R ⊑ R²R ⊑ R² (from modular law + R⊑1) and R² ⊑ 1R = R. -/
theorem coreflexive_symmetric_idempotent {a : 𝒜} {R : a ⟶ a} (h : Coreflexive R) :
    Symmetric R ∧ R ≫ R = R := by
  -- h: R ⊑ 1
  have h_le_one : R ⊑ Cat.id a := h
  -- Step 1: R ⊑ RR°R via modular law
  have hR_le_RRrecipR : R ⊑ (R ≫ R°) ≫ R := by
    have h_mod := modular_le (Cat.id a) R R
    -- h_mod: (1≫R)∩R ⊑ (1 ∩ RR°)≫R, simplify using id_comp, inter_idem
    have h1 : R ⊑ (Cat.id a ∩ R ≫ R°) ≫ R := by
      simpa [Cat.id_comp, Allegory.inter_idem] using h_mod
    -- (1∩RR°) ⊑ RR°, so (1∩RR°)R ⊑ RR°R by comp_mono_right
    have h2 : (Cat.id a ∩ R ≫ R°) ≫ R ⊑ (R ≫ R°) ≫ R :=
      comp_mono_right (inter_lb_right (Cat.id a) (R ≫ R°)) R
    exact le_trans h1 h2
  -- Step 2: RR°R ⊑ R° (using R ⊑ 1)
  have hRRrecipR_le_Rrecip : (R ≫ R°) ≫ R ⊑ R° := by
    -- R ⊑ 1 ⇒ RR° ⊑ 1R° (comp_mono_right R°)
    have h_RRrecip_le_1Rrecip : R ≫ R° ⊑ (Cat.id a) ≫ R° := comp_mono_right h_le_one R°
    -- RR°R ⊑ (1R°)R
    have h1 : (R ≫ R°) ≫ R ⊑ ((Cat.id a) ≫ R°) ≫ R :=
      comp_mono_right h_RRrecip_le_1Rrecip R
    -- (1R°)R = 1(R°R) ⊑ 1(R°1) = 1R° = R° (since R ⊑ 1)
    have h2 : ((Cat.id a) ≫ R°) ≫ R ⊑ R° := by
      calc
        ((Cat.id a) ≫ R°) ≫ R = (Cat.id a) ≫ (R° ≫ R) := by rw [Cat.assoc]
        _ ⊑ (Cat.id a) ≫ (R° ≫ Cat.id a) :=
          comp_mono_left (Cat.id a) (comp_mono_left R° h_le_one)
        _ = (Cat.id a) ≫ R° := by rw [Cat.comp_id]
        _ = R° := by rw [Cat.id_comp]
    exact le_trans h1 h2
  -- Step 3: R ⊑ R°, hence symmetric
  have h_symm : Symmetric R := by
    have hR_le_Rrecip : R ⊑ R° := le_trans hR_le_RRrecipR hRRrecipR_le_Rrecip
    -- Apply recip_mono: R° ⊑ R°° = R
    have hRrecip_le_R : R° ⊑ R := recip_le_iff.mpr hR_le_Rrecip
    exact hRrecip_le_R
  -- Step 4: Idempotent R² = R
  have h_idem : R ≫ R = R := by
    -- From symmetry: R° = R
    have h_eq : R° = R := symmetric_eq h_symm
    -- R ⊑ R²R (from step 1, substituting R°=R)
    have hR_le_RR_R : R ⊑ (R ≫ R) ≫ R := by
      simpa [h_eq] using hR_le_RRrecipR
    -- R²R ⊑ R² (since R ⊑ 1)
    have hRRR_le_RR : (R ≫ R) ≫ R ⊑ R ≫ R := by
      calc
        (R ≫ R) ≫ R = R ≫ (R ≫ R) := by rw [Cat.assoc]
        _ ⊑ R ≫ (R ≫ Cat.id a) := comp_mono_left R (comp_mono_left R h_le_one)
        _ = R ≫ R := by rw [Cat.comp_id]
    -- So R ⊑ R²
    have hR_le_RR : R ⊑ R ≫ R := le_trans hR_le_RR_R hRRR_le_RR
    -- R² ⊑ R (since R ⊑ 1)
    have hRR_le_R : R ≫ R ⊑ R := by
      calc
        R ≫ R ⊑ (Cat.id a) ≫ R := comp_mono_right h_le_one R
        _ = R := by rw [Cat.id_comp]
    exact le_antisymm hRR_le_R hR_le_RR
  exact ⟨h_symm, h_idem⟩

/-! ## §2.121  Coreflexive composition

  For coreflexive morphisms, AB = A ∩ B (§2.121). -/
theorem coreflexive_comp_eq_inter {a : 𝒜} {A B : a ⟶ a} (hA : Coreflexive A) (hB : Coreflexive B) :
    A ≫ B = A ∩ B := by
  -- A∩B is also coreflexive (it's below A which is below 1)
  have h_inter_coref : Coreflexive (A ∩ B) := by
    dsimp [Coreflexive]
    -- A∩B ⊑ A ⊑ 1, so A∩B ⊑ 1 by transitivity (but we need the equation: (A∩B)∩1 = A∩B)
    -- Actually A∩B ⊑ 1 because inter_lb_left gives A∩B ⊑ A and hA: A ⊑ 1
    apply le_trans (inter_lb_left A B) hA
  -- A∩B is idempotent by the previous theorem
  have h_inter_idem : (A ∩ B) ≫ (A ∩ B) = A ∩ B :=
    (coreflexive_symmetric_idempotent h_inter_coref).2
  apply le_antisymm
  · -- AB ⊑ A∩B: AB ⊑ A (since B⊑1) and AB ⊑ B (since A⊑1)
    -- AB ⊑ A: B ⊑ 1 ⇒ A≫B ⊑ A≫1 = A
    have h_AB_le_A : A ≫ B ⊑ A :=
      le_trans (comp_mono_left A hB) (by rw [Cat.comp_id]; exact le_refl A)
    have h_AB_le_B : A ≫ B ⊑ B :=
      le_trans (comp_mono_right hA B) (by rw [Cat.id_comp]; exact le_refl B)
    exact le_inter h_AB_le_A h_AB_le_B
  · -- A∩B ⊑ AB: A∩B = (A∩B)(A∩B) ⊑ AB
    have h1 : A ∩ B ⊑ A ≫ (A ∩ B) := by
      simpa [h_inter_idem] using comp_mono_right (inter_lb_left A B) (A ∩ B)
    have h2 : A ≫ (A ∩ B) ⊑ A ≫ B := comp_mono_left A (inter_lb_right A B)
    exact le_trans h1 h2
    -- Note: inter_lb_left A B: A∩B ⊑ A.  inter_lb_right A B: A∩B ⊑ B.

/-! ## §2.122  Domain -/

/-- The DOMAIN of R, denoted %mR in the book: 1 ∩ RR° (§2.122). -/
def dom {a b : 𝒜} (R : a ⟶ b) : a ⟶ a := Cat.id a ∩ R ≫ R°

/-- Domain is coreflexive (§2.122). -/
theorem dom_coreflexive {a b : 𝒜} (R : a ⟶ b) : Coreflexive (dom R) :=
  inter_lb_left (Cat.id a) (R ≫ R°)

/-! ## §2.124  Domain of intersection -/

/-- dom(R ∩ S) = 1 ∩ SR° (§2.124).
    Proof uses modular law: 1 ∩ (R∩S)(R∩S)° ⊑ 1 ∩ RS°, and
    1 ∩ SR° ⊑ 1 ∩ (R∩S)(R∩S)°. -/
theorem dom_inter {a b : 𝒜} (R S : a ⟶ b) : dom (R ∩ S) = Cat.id a ∩ S ≫ R° := by
  apply le_antisymm
  · -- dom(R∩S) ⊑ 1 ∩ S R°
    dsimp [dom]
    rw [Allegory.recip_inter]
    have h : (R ∩ S) ≫ (R° ∩ S°) ⊑ S ≫ R° := by
      refine le_trans (comp_mono_right (inter_lb_right R S) (R° ∩ S°)) ?_
      exact comp_mono_left S (inter_lb_left R° S°)
    apply le_inter
    · exact inter_lb_left _ _
    · exact le_trans (inter_lb_right _ _) h
  · -- 1 ∩ S R° ⊑ dom(R∩S)
    dsimp [dom]
    rw [Allegory.recip_inter]
    -- Goal: 1 ∩ S R° ⊑ 1 ∩ (R∩S)(R°∩S°)
    -- Step 1: 1 ∩ S R° = 1 ∩ (R∩S) R°
    have h_eq1 : Cat.id a ∩ S ≫ R° = Cat.id a ∩ ((R ∩ S) ≫ R°) := by
      apply le_antisymm
      · -- 1 ∩ S R° ⊑ 1 ∩ (R∩S) R° via modular law
        have h_m : Cat.id a ∩ S ≫ R° ⊑ (R ∩ S) ≫ R° := by
          calc
            Cat.id a ∩ S ≫ R° = (S ≫ R°) ∩ Cat.id a := by rw [Allegory.inter_comm]
            _ ⊑ (S ∩ (Cat.id a ≫ R)) ≫ R° := by
              have h := modular_le S R° (Cat.id a)
              rw [Allegory.recip_recip] at h
              exact h
            _ = (S ∩ R) ≫ R° := by rw [Cat.id_comp]
            _ = (R ∩ S) ≫ R° := by rw [Allegory.inter_comm S R]
        apply le_inter (inter_lb_left _ _) h_m
      · -- 1 ∩ (R∩S) R° ⊑ 1 ∩ S R° by monotonicity (R∩S ⊑ S)
        have h : (R ∩ S) ≫ R° ⊑ S ≫ R° := comp_mono_right (inter_lb_right R S) R°
        exact le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) h)
    rw [h_eq1]
    -- Step 2: 1 ∩ (R∩S) R° = 1 ∩ R (R°∩S°)  (via recip symmetry of coreflexives)
    have h_eq2 : Cat.id a ∩ ((R ∩ S) ≫ R°) = Cat.id a ∩ (R ≫ (R° ∩ S°)) := by
      have h_coref : Coreflexive (Cat.id a ∩ (R ≫ (R° ∩ S°))) :=
        inter_lb_left _ _
      have h_symm : Symmetric (Cat.id a ∩ (R ≫ (R° ∩ S°))) :=
        (coreflexive_symmetric_idempotent h_coref).1
      have h_self_recip : (Cat.id a ∩ (R ≫ (R° ∩ S°)))° = Cat.id a ∩ (R ≫ (R° ∩ S°)) :=
        symmetric_eq h_symm
      -- LHS° = RHS (computed via recip_inter, recip_comp, recip_recip)
      -- So LHS = LHS°° = RHS° = RHS (by symmetry of coreflexive RHS)
      have h_recip_eq : (Cat.id a ∩ ((R ∩ S) ≫ R°))° = Cat.id a ∩ (R ≫ (R° ∩ S°)) := by
        simp [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip, recip_id]
      calc
        Cat.id a ∩ ((R ∩ S) ≫ R°) = (Cat.id a ∩ ((R ∩ S) ≫ R°))°° := by
          simp [Allegory.recip_recip]
        _ = (Cat.id a ∩ (R ≫ (R° ∩ S°)))° := by rw [h_recip_eq]
        _ = Cat.id a ∩ (R ≫ (R° ∩ S°)) := h_self_recip
    rw [h_eq2]
    -- Step 3: 1 ∩ R (R°∩S°) ⊑ (R∩S)(R°∩S°) via modular law
    have h_m2 : Cat.id a ∩ (R ≫ (R° ∩ S°)) ⊑ (R ∩ S) ≫ (R° ∩ S°) := by
      calc
        Cat.id a ∩ (R ≫ (R° ∩ S°)) = (R ≫ (R° ∩ S°)) ∩ Cat.id a := by rw [Allegory.inter_comm]
        _ ⊑ (R ∩ (Cat.id a ≫ ((R° ∩ S°)°))) ≫ (R° ∩ S°) :=
          modular_le R (R° ∩ S°) (Cat.id a)
        _ = (R ∩ (R ∩ S)) ≫ (R° ∩ S°) := by
          simp [Allegory.recip_inter, Allegory.recip_recip, Cat.id_comp]
        _ = (R ∩ S) ≫ (R° ∩ S°) := by
          rw [Allegory.inter_assoc, Allegory.inter_idem]
    -- Combine: 1 ∩ S R° = ... ⊑ (R∩S)(R°∩S°), and also ⊑ 1
    apply le_inter (inter_lb_left _ _) h_m2

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
  rcases hf with ⟨hf_entire, hf_simple⟩
  rcases hg with ⟨hg_entire, hg_simple⟩
  -- Entire means dom = 1, so 1 = 1 ∩ f f°
  have h_one_f_eq : Cat.id a ∩ (f ≫ f°) = Cat.id a := by
    dsimp [Entire, dom] at hf_entire; exact hf_entire
  -- From f ⊑ g we have f° ⊑ g°
  have h_recip : f° ⊑ g° := recip_mono h
  -- Show g ⊑ f
  have h_g_le_f : g ⊑ f := by
    -- g = (1 ∩ f f°) g ⊑ (f f°) g = f (f° g) ⊑ f (g° g) ⊑ f 1 = f
    have h1 : g = (Cat.id a ∩ (f ≫ f°)) ≫ g := by rw [h_one_f_eq, Cat.id_comp]
    have h2 : (Cat.id a ∩ (f ≫ f°)) ≫ g ⊑ f := by
      have h2a : (Cat.id a ∩ (f ≫ f°)) ≫ g ⊑ (f ≫ f°) ≫ g :=
        comp_mono_right (inter_lb_right (Cat.id a) (f ≫ f°)) g
      have h2b : (f ≫ f°) ≫ g ⊑ f := by
        rw [Cat.assoc]
        -- f (f° g) ⊑ f (g° g)
        have h_fog : f° ≫ g ⊑ g° ≫ g := comp_mono_right h_recip g
        have h_f_le : f ≫ (f° ≫ g) ⊑ f ≫ (g° ≫ g) := comp_mono_left f h_fog
        -- f (g° g) ⊑ f 1 = f
        simpa [Cat.comp_id] using le_trans h_f_le (comp_mono_left f hg_simple)
      exact le_trans h2a h2b
    rw [h1]; exact h2
  exact le_antisymm h h_g_le_f

/-! ## §2.134  Reciprocation on maps -/

theorem map_recip_is_inverse {a b : 𝒜} {f : a ⟶ b} (hf : Map f) (hfo : Map (f°)) :
    f ≫ f° = Cat.id a ∧ f° ≫ f = Cat.id b := by
  rcases hf with ⟨hf_entire, hf_simple⟩
  rcases hfo with ⟨hfo_entire, hfo_simple⟩
  -- Entire f: 1_a ∩ f f° = 1_a → 1_a ⊑ f f°
  have h_id_le_ff : Cat.id a ⊑ f ≫ f° := by
    dsimp [Entire, dom] at hf_entire
    dsimp [le]; rw [hf_entire]
  -- Simple (f°): (f°)° f° ⊑ 1_a, i.e., f f° ⊑ 1_a
  have h_ff_le_id : f ≫ f° ⊑ Cat.id a := by
    dsimp [Simple] at hfo_simple
    simpa [Allegory.recip_recip] using hfo_simple
  -- Entire (f°): 1_b ∩ f° (f°)° = 1_b → 1_b ⊑ f° f
  have h_id_le_ffr : Cat.id b ⊑ f° ≫ f := by
    dsimp [Entire, dom] at hfo_entire
    dsimp [le]
    simpa [Allegory.recip_recip] using hfo_entire
  -- Simple f: f° f ⊑ 1_b
  have h_ffr_le_id : f° ≫ f ⊑ Cat.id b := by
    dsimp [Simple] at hf_simple; exact hf_simple
  exact ⟨le_antisymm h_ff_le_id h_id_le_ff, le_antisymm h_ffr_le_id h_id_le_ffr⟩

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

/-- **§2.141**: If ff° ∩ gg° = 1 for maps f,g : a → c, then (f,g) is a
    monic pair in Map(A).  That is, for any maps h₁, h₂ : a → a,
    h₁f = h₂f ∧ h₁g = h₂g ⇒ h₁ = h₂. -/
theorem tabulates_monic_pair {a c : 𝒜} {f g : a ⟶ c} (hf : Map f) (hg : Map g)
    (h : f ≫ f° ∩ g ≫ g° = Cat.id a) :
    ∀ (h₁ h₂ : a ⟶ a), Map h₁ → Map h₂ → h₁ ≫ f = h₂ ≫ f → h₁ ≫ g = h₂ ≫ g → h₁ = h₂ := by
  intro h₁ h₂ h₁_map h₂_map hf_eq hg_eq
  rcases h₁_map with ⟨h₁_entire, h₁_simple⟩
  rcases h₂_map with ⟨h₂_entire, h₂_simple⟩
  dsimp [Simple] at h₁_simple h₂_simple
  -- From h₁ f = h₂ f, we get (h₁° h₂) f ⊑ f, hence (h₁° h₂) (f f°) ⊑ f f°
  have h_ff_ineq : (h₁° ≫ h₂) ≫ (f ≫ f°) ⊑ f ≫ f° := by
    have h_eq : (h₁° ≫ h₂) ≫ (f ≫ f°) = ((h₁° ≫ h₁) ≫ f) ≫ f° := by
      calc
        (h₁° ≫ h₂) ≫ (f ≫ f°) = ((h₁° ≫ h₂) ≫ f) ≫ f° := by simp [Cat.assoc]
        _ = (h₁° ≫ (h₂ ≫ f)) ≫ f° := by simp [Cat.assoc]
        _ = (h₁° ≫ (h₁ ≫ f)) ≫ f° := by rw [← hf_eq]
        _ = ((h₁° ≫ h₁) ≫ f) ≫ f° := by simp [Cat.assoc]
    rw [h_eq]
    simpa [Cat.id_comp] using comp_mono_right (comp_mono_right h₁_simple f) f°
  -- Similarly from h₁ g = h₂ g: (h₁° h₂) (g g°) ⊑ g g°
  have h_gg_ineq : (h₁° ≫ h₂) ≫ (g ≫ g°) ⊑ g ≫ g° := by
    have h_eq : (h₁° ≫ h₂) ≫ (g ≫ g°) = ((h₁° ≫ h₁) ≫ g) ≫ g° := by
      calc
        (h₁° ≫ h₂) ≫ (g ≫ g°) = ((h₁° ≫ h₂) ≫ g) ≫ g° := by simp [Cat.assoc]
        _ = (h₁° ≫ (h₂ ≫ g)) ≫ g° := by simp [Cat.assoc]
        _ = (h₁° ≫ (h₁ ≫ g)) ≫ g° := by rw [← hg_eq]
        _ = ((h₁° ≫ h₁) ≫ g) ≫ g° := by simp [Cat.assoc]
    rw [h_eq]
    simpa [Cat.id_comp] using comp_mono_right (comp_mono_right h₁_simple g) g°
  -- Prove h₁° h₂ ⊑ 1
  have h_coref : h₁° ≫ h₂ ⊑ Cat.id a := by
    -- h₁° h₂ = (h₁° h₂) 1 = (h₁° h₂) (f f° ∩ g g°)  [since h: ff°∩gg°=1]
    have h_base : h₁° ≫ h₂ = (h₁° ≫ h₂) ≫ (f ≫ f° ∩ g ≫ g°) := by rw [h, Cat.comp_id]
    rw [h_base]
    -- By semidistrib: R(S∩T) ⊑ RS ∩ RT
    have h_sd_eq := Allegory.semidistrib (h₁° ≫ h₂) (f ≫ f°) (g ≫ g°)
    -- h_sd_eq: R(A∩B) = (RA ∩ R(A∩B)) ∩ RB, so R(A∩B) ⊑ RA and R(A∩B) ⊑ RB
    have h_le_A : (h₁° ≫ h₂) ≫ (f ≫ f° ∩ g ≫ g°) ⊑ (h₁° ≫ h₂) ≫ (f ≫ f°) := by
      rw [h_sd_eq]; exact le_trans (inter_lb_left _ _) (inter_lb_left _ _)
    have h_le_B : (h₁° ≫ h₂) ≫ (f ≫ f° ∩ g ≫ g°) ⊑ (h₁° ≫ h₂) ≫ (g ≫ g°) := by
      rw [h_sd_eq]; exact inter_lb_right _ _
    -- Combine: R(A∩B) ⊑ RA ∩ RB ⊑ A ∩ B = 1
    have h_mid : (h₁° ≫ h₂) ≫ (f ≫ f° ∩ g ≫ g°) ⊑ (f ≫ f°) ∩ (g ≫ g°) := by
      have h_le_inter : (h₁° ≫ h₂) ≫ (f ≫ f° ∩ g ≫ g°) ⊑
          ((h₁° ≫ h₂) ≫ (f ≫ f°)) ∩ ((h₁° ≫ h₂) ≫ (g ≫ g°)) :=
        le_inter h_le_A h_le_B
      have h_inter_le : ((h₁° ≫ h₂) ≫ (f ≫ f°)) ∩ ((h₁° ≫ h₂) ≫ (g ≫ g°)) ⊑
          (f ≫ f°) ∩ (g ≫ g°) := by
        have h1 : ((h₁° ≫ h₂) ≫ (f ≫ f°)) ∩ ((h₁° ≫ h₂) ≫ (g ≫ g°)) ⊑ f ≫ f° :=
          le_trans (inter_lb_left _ _) h_ff_ineq
        have h2 : ((h₁° ≫ h₂) ≫ (f ≫ f°)) ∩ ((h₁° ≫ h₂) ≫ (g ≫ g°)) ⊑ g ≫ g° :=
          le_trans (inter_lb_right _ _) h_gg_ineq
        exact le_inter h1 h2
      exact le_trans h_le_inter h_inter_le
    exact le_trans h_mid (by rw [h]; exact le_refl _)
  -- From h₁° h₂ ⊑ 1, prove h₂ ⊑ h₁
  have h₂_le_h₁ : h₂ ⊑ h₁ := by
    have h_one_eq : Cat.id a ∩ (h₁ ≫ h₁°) = Cat.id a := by
      dsimp [Entire, dom] at h₁_entire; exact h₁_entire
    have h_eq : h₂ = (Cat.id a ∩ (h₁ ≫ h₁°)) ≫ h₂ := by rw [h_one_eq, Cat.id_comp]
    rw [h_eq]
    refine le_trans (comp_mono_right (inter_lb_right _ _) h₂) ?_
    rw [Cat.assoc]
    simpa [Cat.comp_id] using comp_mono_left h₁ h_coref
  -- By symmetry, h₁ ⊑ h₂
  have h₁_le_h₂ : h₁ ⊑ h₂ := by
    -- Using the same proof with swapped h₁ ↔ h₂
    -- We need (h₂° h₁) ⊑ 1, which follows similarly from h₂° h₁ f ⊑ f etc.
    -- From h₁ f = h₂ f, taking recip: f° h₁° = f° h₂°
    -- Then compose with h₁ on the right: f° (h₂° h₁) ⊑ f° ... hmm, let me be more direct
    -- Actually, hf_eq and hg_eq are symmetric: they also give h₂ f = h₁ f and h₂ g = h₁ g
    -- So the EXACT same argument with h₁ ↔ h₂ works
    have h_ff_ineq' : (h₂° ≫ h₁) ≫ (f ≫ f°) ⊑ f ≫ f° := by
      have h_eq : (h₂° ≫ h₁) ≫ (f ≫ f°) = ((h₂° ≫ h₂) ≫ f) ≫ f° := by
        calc
          (h₂° ≫ h₁) ≫ (f ≫ f°) = ((h₂° ≫ h₁) ≫ f) ≫ f° := by simp [Cat.assoc]
          _ = (h₂° ≫ (h₁ ≫ f)) ≫ f° := by simp [Cat.assoc]
          _ = (h₂° ≫ (h₂ ≫ f)) ≫ f° := by rw [hf_eq]
          _ = ((h₂° ≫ h₂) ≫ f) ≫ f° := by simp [Cat.assoc]
      rw [h_eq]
      simpa [Cat.id_comp] using comp_mono_right (comp_mono_right h₂_simple f) f°
    have h_gg_ineq' : (h₂° ≫ h₁) ≫ (g ≫ g°) ⊑ g ≫ g° := by
      have h_eq : (h₂° ≫ h₁) ≫ (g ≫ g°) = ((h₂° ≫ h₂) ≫ g) ≫ g° := by
        calc
          (h₂° ≫ h₁) ≫ (g ≫ g°) = ((h₂° ≫ h₁) ≫ g) ≫ g° := by simp [Cat.assoc]
          _ = (h₂° ≫ (h₁ ≫ g)) ≫ g° := by simp [Cat.assoc]
          _ = (h₂° ≫ (h₂ ≫ g)) ≫ g° := by rw [hg_eq]
          _ = ((h₂° ≫ h₂) ≫ g) ≫ g° := by simp [Cat.assoc]
      rw [h_eq]
      simpa [Cat.id_comp] using comp_mono_right (comp_mono_right h₂_simple g) g°
    have h_coref' : h₂° ≫ h₁ ⊑ Cat.id a := by
      have h_base' : h₂° ≫ h₁ = (h₂° ≫ h₁) ≫ (f ≫ f° ∩ g ≫ g°) := by rw [h, Cat.comp_id]
      rw [h_base']
      have h_sd_eq' := Allegory.semidistrib (h₂° ≫ h₁) (f ≫ f°) (g ≫ g°)
      have h_le_A' : (h₂° ≫ h₁) ≫ (f ≫ f° ∩ g ≫ g°) ⊑ (h₂° ≫ h₁) ≫ (f ≫ f°) := by
        rw [h_sd_eq']; exact le_trans (inter_lb_left _ _) (inter_lb_left _ _)
      have h_le_B' : (h₂° ≫ h₁) ≫ (f ≫ f° ∩ g ≫ g°) ⊑ (h₂° ≫ h₁) ≫ (g ≫ g°) := by
        rw [h_sd_eq']; exact inter_lb_right _ _
      have h_mid' : (h₂° ≫ h₁) ≫ (f ≫ f° ∩ g ≫ g°) ⊑ (f ≫ f°) ∩ (g ≫ g°) := by
        have h_le_inter' : (h₂° ≫ h₁) ≫ (f ≫ f° ∩ g ≫ g°) ⊑
            ((h₂° ≫ h₁) ≫ (f ≫ f°)) ∩ ((h₂° ≫ h₁) ≫ (g ≫ g°)) :=
          le_inter h_le_A' h_le_B'
        have h_inter_le' : ((h₂° ≫ h₁) ≫ (f ≫ f°)) ∩ ((h₂° ≫ h₁) ≫ (g ≫ g°)) ⊑
            (f ≫ f°) ∩ (g ≫ g°) := by
          have h1' : ((h₂° ≫ h₁) ≫ (f ≫ f°)) ∩ ((h₂° ≫ h₁) ≫ (g ≫ g°)) ⊑ f ≫ f° :=
            le_trans (inter_lb_left _ _) h_ff_ineq'
          have h2' : ((h₂° ≫ h₁) ≫ (f ≫ f°)) ∩ ((h₂° ≫ h₁) ≫ (g ≫ g°)) ⊑ g ≫ g° :=
            le_trans (inter_lb_right _ _) h_gg_ineq'
          exact le_inter h1' h2'
        exact le_trans h_le_inter' h_inter_le'
      exact le_trans h_mid' (by rw [h]; exact le_refl _)
    have h_one_eq' : Cat.id a ∩ (h₂ ≫ h₂°) = Cat.id a := by
      dsimp [Entire, dom] at h₂_entire; exact h₂_entire
    have h1_eq : h₁ = (Cat.id a ∩ (h₂ ≫ h₂°)) ≫ h₁ := by
      rw [h_one_eq', Cat.id_comp]
    have h1_le : (Cat.id a ∩ (h₂ ≫ h₂°)) ≫ h₁ ⊑ h₂ := by
      refine le_trans (comp_mono_right (inter_lb_right _ _) h₁) ?_
      calc
        (h₂ ≫ h₂°) ≫ h₁ = h₂ ≫ (h₂° ≫ h₁) := by rw [Cat.assoc]
        _ ⊑ h₂ ≫ Cat.id a := comp_mono_left h₂ h_coref'
        _ = h₂ := by rw [Cat.comp_id]
    rw [h1_eq]; exact h1_le
  exact le_antisymm h₁_le_h₂ h₂_le_h₁

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

/-- A SEMI-SIMPLE morphism factors as F° ≫ G with F, G simple (§2.16(10)).
    F : c → a, G : c → b have a common source (apex) c, so F° ≫ G : a → b — exactly
    the form `R = F°G` of a tabulation (§2.143).  (Note: this is NOT the reciprocal
    `F ≫ G°`; simplicity is not preserved under reciprocation, so the apex must be the
    common *source*.) -/
def SemiSimple {a b : 𝒜} (R : a ⟶ b) : Prop :=
  ∃ (c : 𝒜) (F : c ⟶ a) (G : c ⟶ b), Simple F ∧ Simple G ∧ R = F° ≫ G

/-- A SEMI-SIMPLE ALLEGORY: every morphism is semi-simple (§2.16(10)). -/
class SemiSimpleAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  semi_simple {a b : 𝒜} (R : a ⟶ b) : SemiSimple R

/-! ## Missing propositions from §2.12–§2.16(13) -/

-- §2.12: Symmetric and transitive imply idempotent.
-- Already formalized as `symmetric_transitive_idempotent` in S2_22.lean (UnionAllegory).

-- §2.123: dom(RS) ⊑ dom(R).
-- BOOK §2.123: Consequently, Dom(RS) ⊑ Dom(R).
-- (Proof uses the domain characterization: A ⊑ dom R iff R ⊑ AR, §2.122.)

-- §2.131: R and S entire/simple/maps implies RS is entire/simple/a map;
-- RS entire implies R entire.
-- §2.131: simples compose — already formalized as `simple_comp` in S2_4.lean.

theorem entire_comp {a b c : 𝒜} {R : a ⟶ b} {S : b ⟶ c} (hR : Entire R) (hS : Entire S) :
    Entire (R ≫ S) := by
  -- dom R = 1 ⊑ RR°; dom S = 1 ⊑ SS°.
  -- dom(RS) = 1 ∩ RS(RS)°; need 1 ⊑ RS S° R° ⊑ R(dom S)R° = R 1 R° = RR° ⊑ ... ⊑ 1.
  sorry

-- §2.131: maps compose — already formalized as `map_comp` in S2_22b.lean.
-- (The component lemmas `entire_comp`/`simple_comp` remain here as §2.131 stubs.)

theorem entire_of_comp_entire {a b c : 𝒜} {R : a ⟶ b} {S : b ⟶ c} (h : Entire (R ≫ S)) :
    Entire R := by
  sorry

-- §2.135: If R is an isomorphism (§1.41 IsIso) then R is a map and R⁻¹ = R°.
theorem iso_is_map {a b : 𝒜} {R : a ⟶ b} (hR : Freyd.IsIso R) : Map R := by
  sorry

-- §2.135: The inverse of an iso equals its reciprocal.
-- If Rinv is the inverse of iso R (i.e. R ≫ Rinv = 1 ∧ Rinv ≫ R = 1), then Rinv = R°.
theorem iso_inv_eq_recip {a b : 𝒜} {R : a ⟶ b} (hR : Freyd.IsIso R)
    {Rinv : b ⟶ a} (h1 : R ≫ Rinv = Cat.id a) (h2 : Rinv ≫ R = Cat.id b) :
    Rinv = R° := by
  sorry

-- §2.136: If F is simple then F(R ∩ S) = FR ∩ FS.
theorem simple_dist_inter {a b c : 𝒜} {F : a ⟶ b} (hF : Simple F) (R S : b ⟶ c) :
    F ≫ (R ∩ S) = (F ≫ R) ∩ (F ≫ S) := by
  sorry

-- BOOK §2.143: If f,g tabulates R then s°r ⊑ R iff there is a unique map h with the
-- appropriate factorizations through the tabulation (universal property of tabulation).
-- (Stub deferred: the factorization equations depend on the repo's Tabulates convention
-- R = f ≫ g°, which needs care to state; revisit alongside §2.144.)

-- BOOK §2.144: Tabulations are unique up to unique isomorphism: if f,g and f',g' both
-- tabulate R then there is a unique iso u with f' = u ≫ f and g' = u ≫ g.

-- §2.145: If a coreflexive morphism A is tabular then ∃ monic map h with A = h°h.
theorem coreflexive_tabular_monic {a : 𝒜} {A : a ⟶ a} (hA : Coreflexive A) (hTab : Tabular A) :
    ∃ (c : 𝒜) (h : a ⟶ c), Map h ∧ Freyd.Monic h ∧ A = h ≫ h° := by
  sorry

-- BOOK §2.147: If A is a tabular allegory then Map(A) has pullbacks, equalizers, images
-- and pullbacks transfer images.
-- (Constructive description: pullback of f,g = tabulation of fg°; equalizer of f,g = tabulation
-- of dom(f∩g); image of f = tabulation of dom(f°); g cover iff g° entire.)

-- BOOK §2.148: If A is a tabular allegory then A ≅ Rel(Map(A)).

-- §2.151: If π is a partial unit then Dom : (α,π) → Cor(α) is an iso of (α,π) onto an ideal.
-- BOOK §2.151: If π is a partial unit then Dom : (α,π) → Cor(α) is an isomorphism of
-- the semi-lattice (α,π) onto an ideal of Cor(α).

-- §2.152: The unique entire morphism p_α : α → λ (for unit λ) is a map.
theorem unit_proj_is_map (a : 𝒜) [UnitaryAllegory 𝒜] :
    ∃ (p : a ⟶ UnitaryAllegory.unit_obj (𝒜 := 𝒜)), Map p := by
  sorry

-- BOOK §2.152: If λ is a unit then for any α,β, the morphism p_α(p_β)° is maximum in (α,β).

-- BOOK §2.154: The category of small regular categories is isomorphic to the
-- category of small unitary tabular allegories.

-- BOOK §2.154: A small unitary tabular allegory may be faithfully represented
-- in a power of the allegory of sets.

-- §2.162: If R,S splits a symmetric idempotent T (RS = T, SR = 1) then S = R°.
theorem split_symm_idem_recip {a c : 𝒜} {R : a ⟶ c} {S : c ⟶ a} {T : a ⟶ a}
    (hRS : R ≫ S = T) (hSR : S ≫ R = Cat.id c) (hSymm : Symmetric T) :
    S = R° := by
  sorry

-- §2.163: A coreflexive morphism A is a split idempotent iff A is tabular.
theorem coreflexive_split_iff_tabular {a : 𝒜} {A : a ⟶ a} (hA : Coreflexive A) :
    (∃ (c : 𝒜) (h : a ⟶ c), Map h ∧ h ≫ h° = A ∧ h° ≫ h = Cat.id c) ↔ Tabular A := by
  sorry

-- §2.163: An equivalence relation E is a split idempotent iff it is effective
-- (∃ map f with ff° = E, f°f = 1).
def EquivalenceRel {a : 𝒜} (E : a ⟶ a) : Prop :=
  Reflexive E ∧ Symmetric E ∧ Transitive E

theorem equiv_rel_split_iff_effective {a : 𝒜} {E : a ⟶ a} (hE : EquivalenceRel E) :
    (∃ (c : 𝒜) (f : a ⟶ c), Map f ∧ f ≫ f° = E ∧ f° ≫ f = Cat.id c) ↔
    ∃ (c : 𝒜) (R : a ⟶ c) (S : c ⟶ a), R ≫ S = E ∧ S ≫ R = Cat.id c := by
  sorry

-- BOOK §2.165: If A is pre-tabular then Spl(Cor(A)) remains pre-tabular.

-- BOOK §2.166: An allegory is tabular iff it is pre-tabular and all coreflexive morphisms split.

-- BOOK §2.167: For a pre-tabular allegory A, Spl(Cor(A)) is its tabular reflection.

-- BOOK §2.16(10): Let A be an allegory, SI its class of symmetric idempotents.
-- Spl(SI) is tabular iff A is semi-simple.

-- BOOK §2.16(13): If C is an AC regular category and Ĉ its effective reflection,
-- then C is equivalent to the full subcategory of projective objects in Ĉ;
-- hence if Ĉ is not effective then C is not AC.

end Freyd.Alg
