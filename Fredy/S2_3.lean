/-
  Freyd & Scedrov, *Categories and Allegories* §2.3  Division allegories.

  §2.31 DIVISION ALLEGORY — right division R/S
  §2.331 SYMMETRIC DIVISION R/ₛS
  §2.35  STRAIGHT morphism, simple part, domain of simplicity
-/

import Fredy.S1_1
import Fredy.S2_1
import Fredy.S2_2


universe v u

namespace Freyd.Alg

/-! ## §2.31  Division allegory

  A DIVISION ALLEGORY is a distributive allegory with a binary partial
  operation R/S (right division) defined when R□ = S□, characterized by:
  T ⊑ R/S  iff  TS ⊑ R.

  Equivalently: (R/S)S ⊑ R (semi-commutative triangle) and R/S is
  maximal among such morphisms. -/

/-- A DIVISION ALLEGORY (§2.31): distributive allegory with right division R/S,
    the right adjoint to composition (-) ≫ S. -/
class DivisionAllegory (𝒜 : Type u) extends DistributiveAllegory 𝒜 where
  /-- Right division R/S : □R → □S, defined when R□ = S□. -/
  div {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : a ⟶ b

  /-- The semi-commutative triangle: (R/S)S ⊑ R (§2.31). -/
  div_comp_le {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : (div R S ≫ S) ⊑ R

  /-- The adjointness: if TS ⊑ R then T ⊑ R/S (§2.31). -/
  le_div {a b c : 𝒜} (T : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) (h : T ≫ S ⊑ R) : T ⊑ div R S

/-! ### Notation -/

/-- Right division notation R / S -/
infixl:70 " / " => DivisionAllegory.div

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ### Derived properties of division -/

/-- The defining equivalence: T ⊑ R/S iff TS ⊑ R (§2.31). -/
theorem le_div_iff {a b c : 𝒜} (T : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) :
    T ⊑ R / S ↔ T ≫ S ⊑ R := by
  constructor
  · intro h
    -- T ⊑ R/S → TS ⊑ (R/S)S ⊑ R
    apply le_trans ?_ (DivisionAllegory.div_comp_le R S)
    exact comp_mono_right h S
  · exact DivisionAllegory.le_div T R S

/-- (R/S)S ⊑ R (§2.31). -/
theorem div_comp_eq_le {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : (R / S) ≫ S ⊑ R :=
  DivisionAllegory.div_comp_le R S

/-- (R ∩ R')/S ⊑ (R/S) ∩ (R'/S) (§2.31). -/
theorem div_inter_le {a b c : 𝒜} (R R' : a ⟶ c) (S : b ⟶ c) :
    (R ∩ R') / S ⊑ (R / S) ∩ (R' / S) := by
  apply le_inter
  · apply (le_div_iff _ _ _).mpr
    -- ((R ∩ R') / S) ≫ S ⊑ R ∩ R' ⊑ R
    apply le_trans (div_comp_eq_le _ _)
    exact inter_lb_left _ _
  · apply (le_div_iff _ _ _).mpr
    apply le_trans (div_comp_eq_le _ _)
    exact inter_lb_right _ _

/-- R/1 = R (§2.314). -/
theorem div_one {a b : 𝒜} (R : a ⟶ b) : R / Cat.id b = R := by
  apply le_antisymm
  · -- (R/1) ⊑ R: div_comp_eq_le gives (R/1)≫1 ⊑ R, and (R/1)≫1 = R/1
    have h := div_comp_eq_le R (Cat.id b)
    simpa [Cat.comp_id] using h
  · -- R ⊑ R/1: by le_div_iff, this is equivalent to R≫1 ⊑ R
    rw [le_div_iff]
    simpa [Cat.comp_id] using le_refl R

/-- 1 ⊑ R/R (§2.314). -/
theorem one_le_div_self {a b : 𝒜} (R : a ⟶ b) : Cat.id a ⊑ R / R := by
  apply (le_div_iff _ _ _).mpr
  rw [Cat.id_comp]
  exact le_refl _

/-- (R/R)R ⊑ R (§2.314). -/
theorem div_self_comp_le {a b : 𝒜} (R : a ⟶ b) : (R / R) ≫ R ⊑ R :=
  div_comp_eq_le R R

/-- (R/S)(S/T) ⊑ R/T (§2.314). -/
theorem div_comp {a b c d : 𝒜} (R : a ⟶ d) (S : b ⟶ d) (T : c ⟶ d) :
    (R / S) ≫ (S / T) ⊑ R / T := by
  apply (le_div_iff _ _ _).mpr
  apply le_trans ?_ (div_comp_eq_le R S)
  rw [Cat.assoc]
  exact comp_mono_left (R / S) (div_comp_eq_le S T)

/-! ## §2.331  Symmetric division

  R/ₛS = (R/S) ∩ (S/R)° (§2.35).  Characterized by:
  T ⊑ R/ₛS  iff  TS ⊑ R and T°R ⊑ S. -/

/-- SYMMETRIC DIVISION: R/ₛS = (R/S) ∩ (S/R)° (§2.35, §2.331). -/
def symmDiv {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) : a ⟶ b :=
  (R / S) ∩ ((S / R)°)

infixl:70 " /ₛ " => symmDiv

/-- Characterizing property of symmetric division (§2.35). -/
theorem le_symmDiv_iff {a b c : 𝒜} (T : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) :
    T ⊑ R /ₛ S ↔ T ≫ S ⊑ R ∧ T° ≫ R ⊑ S := by
  dsimp [symmDiv]
  constructor
  · intro h
    have h1 : T ⊑ R / S := le_trans h (inter_lb_left _ _)
    have h2 : T ⊑ (S / R)° := le_trans h (inter_lb_right _ _)
    constructor
    · exact ((le_div_iff _ _ _).mp h1)
    · -- T ⊑ (S/R)° → T° ⊑ S/R → T°R ⊑ S
      have h2' : T° ⊑ S / R := by
        -- T ⊑ (S/R)° → T° ⊑ (S/R)°° = S/R
        calc
          T° ⊑ ((S / R)°)° := recip_mono h2
          _ = S / R := by rw [Allegory.recip_recip]
      exact ((le_div_iff _ _ _).mp h2')
  · intro ⟨hTS, hTR⟩
    apply le_inter
    · exact ((le_div_iff _ _ _).mpr hTS)
    · -- T ⊑ (S/R)° ↔ T° ⊑ S/R
      have hTR_div : T° ⊑ S / R := (le_div_iff _ _ _).mpr hTR
      calc
        T = (T°)° := by rw [Allegory.recip_recip]
        _ ⊑ (S / R)° := recip_mono hTR_div

/-! ## §2.35  Straight morphism, simple part

  R is STRAIGHT if R/ₛR ⊑ 1 (§2.351).
  In a division allegory, for any R, R/(R/ₛR) is the simple part. -/

/-- R is STRAIGHT if R/ₛR ⊑ 1 (§2.351). -/
def Straight {a b : 𝒜} (R : a ⟶ b) : Prop := R /ₛ R ⊑ Cat.id a

/-- In a division allegory, (R/R)R = R (§2.314). -/
theorem div_self_comp {a b : 𝒜} (R : a ⟶ b) : (R / R) ≫ R = R := by
  apply le_antisymm (div_comp_eq_le R R)
  -- R ⊑ (R/R)R: since 1 ⊑ R/R, we have R = 1R ⊑ (R/R)R
  have h : R ⊑ (R / R) ≫ R := by
    calc
      R = (Cat.id a) ≫ R := by rw [Cat.id_comp]
      _ ⊑ (R / R) ≫ R := comp_mono_right (one_le_div_self R) R
  exact h

/-! ## §2.312  Left division

  S\R := (R°/S°)°, defined when codomain(S) = source(R).
  S : a ⟶ b, R : a ⟶ c gives S\R : b ⟶ c.
  Characterization: T ⊑ S\R iff ST ⊑ R. -/

/-- LEFT DIVISION: S\R := (R°/S°)° (§2.312).
    S : a ⟶ b, R : a ⟶ c, result S\R : b ⟶ c. -/
def leftDiv {a b c : 𝒜} (S : a ⟶ b) (R : a ⟶ c) : b ⟶ c :=
  (R° / S°)°

/-- The defining equivalence: T ⊑ S\R iff ST ⊑ R (§2.312). -/
theorem le_leftDiv_iff {a b c : 𝒜} (T : b ⟶ c) (S : a ⟶ b) (R : a ⟶ c) :
    T ⊑ leftDiv S R ↔ S ≫ T ⊑ R := by
  dsimp [leftDiv]
  -- T ⊑ (R°/S°)° ↔ T° ⊑ R°/S° ↔ T°S° ⊑ R° ↔ (ST)° ⊑ R° ↔ ST ⊑ R
  rw [← recip_le_iff, le_div_iff, ← Allegory.recip_comp, recip_le_iff,
      Allegory.recip_recip]

/-- The semi-commutative triangle for left division: S(S\R) ⊑ R (§2.312). -/
theorem leftDiv_comp_le {a b c : 𝒜} (S : a ⟶ b) (R : a ⟶ c) : S ≫ leftDiv S R ⊑ R :=
  (le_leftDiv_iff _ S R).mp (le_refl _)

/-! ## §2.314  The equation S\(R/T) = (S\R)/T -/

/-- S\(R/T) = (S\R)/T (§2.314).
    S : a ⟶ b, R : a ⟶ d, T : c ⟶ d.
    LHS: leftDiv S (R/T) where R/T : a ⟶ c, so leftDiv S (R/T) : b ⟶ c.
    RHS: (leftDiv S R) / T where leftDiv S R : b ⟶ d, T : c ⟶ d, so result : b ⟶ c. ✓
    -/
theorem leftDiv_div {a b c d : 𝒜} (S : a ⟶ b) (R : a ⟶ d) (T : c ⟶ d) :
    leftDiv S (R / T) = (leftDiv S R) / T := by
  apply le_antisymm
  · -- S\(R/T) ⊑ (S\R)/T: show S ≫ (leftDiv S (R/T) ≫ T) ⊑ R
    apply (le_div_iff _ _ _).mpr
    apply (le_leftDiv_iff _ S R).mpr
    have h1 : (S ≫ leftDiv S (R / T)) ≫ T ⊑ (R / T) ≫ T :=
      comp_mono_right (leftDiv_comp_le S (R / T)) T
    have h2 : (R / T) ≫ T ⊑ R := div_comp_eq_le R T
    rw [← Cat.assoc]; exact le_trans h1 h2
  · -- (S\R)/T ⊑ S\(R/T): show (S ≫ (S\R)/T) ≫ T ⊑ R
    apply (le_leftDiv_iff _ S _).mpr
    apply (le_div_iff _ _ _).mpr
    -- goal: (S ≫ (leftDiv S R)/T) ≫ T ⊑ R
    have step1 : ((leftDiv S R) / T) ≫ T ⊑ leftDiv S R := div_comp_eq_le (leftDiv S R) T
    have step2 : S ≫ (((leftDiv S R) / T) ≫ T) ⊑ S ≫ leftDiv S R :=
      comp_mono_left S step1
    have step3 : S ≫ leftDiv S R ⊑ R := leftDiv_comp_le S R
    have step4 : S ≫ (((leftDiv S R) / T) ≫ T) ⊑ R := le_trans step2 step3
    rwa [← Cat.assoc] at step4

/-! ## §2.351  R/ₛR is an equivalence relation

  The book's §2.351 states that R/ₛR is an equivalence relation. -/

/-- R/ₛR is symmetric (§2.351).
    (R/ₛR)° = ((R/R) ∩ (R/R)°)° = (R/R)° ∩ (R/R)°° = (R/R)° ∩ (R/R) = R/ₛR. -/
theorem symmDiv_self_symmetric {a b : 𝒜} (R : a ⟶ b) : Symmetric (R /ₛ R) := by
  -- R/ₛR = (R/R) ∩ (R/R)°. Show (R/ₛR)° ⊑ R/ₛR.
  -- (R/ₛR)° ⊑ R/ₛR = (R/R) ∩ (R/R)°. Check each component:
  -- (R/ₛR)° ⊑ R/R: (R/ₛR)° ⊑ ((R/R)°)° = R/R. ✓
  -- (R/ₛR)° ⊑ (R/R)°: (R/ₛR)° ⊑ ((R/R))° = (R/R)°... wait need (R/ₛR)° ⊑ (R/R)°.
  -- (R/ₛR) ⊑ R/R, so (R/ₛR)° ⊑ (R/R)°. ✓
  dsimp [Symmetric, le, symmDiv]
  -- goal: ((R/R) ∩ (R/R)°)° ∩ ((R/R) ∩ (R/R)°) = ((R/R) ∩ (R/R)°)°
  rw [Allegory.recip_inter, Allegory.recip_recip]
  -- goal: ((R/R)° ∩ (R/R)) ∩ ((R/R) ∩ (R/R)°) = (R/R)° ∩ (R/R)
  rw [show Allegory.inter (R / R) (Allegory.recip (R / R)) =
        Allegory.inter (Allegory.recip (R / R)) (R / R) from Allegory.inter_comm _ _]
  apply Allegory.inter_idem

/-- R/ₛR is reflexive: 1 ⊑ R/ₛR (§2.351). -/
theorem symmDiv_self_reflexive {a b : 𝒜} (R : a ⟶ b) : Reflexive (R /ₛ R) := by
  dsimp [Reflexive]
  rw [le_symmDiv_iff (Cat.id a) R R]
  exact ⟨by rw [Cat.id_comp]; exact le_refl R,
         by rw [recip_id, Cat.id_comp]; exact le_refl R⟩

/-- R/ₛR is transitive: (R/ₛR)(R/ₛR) ⊑ R/ₛR (§2.351). -/
theorem symmDiv_self_transitive {a b : 𝒜} (R : a ⟶ b) : Transitive (R /ₛ R) := by
  dsimp [Transitive]
  rw [le_symmDiv_iff ((R /ₛ R) ≫ (R /ₛ R)) R R]
  have h1 : (R /ₛ R) ≫ R ⊑ R := ((le_symmDiv_iff (R /ₛ R) R R).mp (le_refl _)).1
  have h_sym : (R /ₛ R)° ⊑ R /ₛ R := symmDiv_self_symmetric R
  constructor
  · -- ((R/ₛR)(R/ₛR)) ≫ R ⊑ R
    -- ((R/ₛR)(R/ₛR)) ≫ R = (R/ₛR) ≫ ((R/ₛR) ≫ R) by assoc; ⊑ (R/ₛR) ≫ R ⊑ R
    have : ((R /ₛ R) ≫ (R /ₛ R)) ≫ R = (R /ₛ R) ≫ (R /ₛ R) ≫ R := Cat.assoc _ _ _
    rw [this]
    exact le_trans (comp_mono_left (R /ₛ R) h1) h1
  · -- ((R/ₛR)(R/ₛR))° ≫ R ⊑ R: = (R/ₛR)°(R/ₛR)° ≫ R ⊑ ... ⊑ R
    rw [Allegory.recip_comp]
    have step1 : (R /ₛ R)° ≫ (R /ₛ R)° ≫ R ⊑ (R /ₛ R) ≫ (R /ₛ R)° ≫ R :=
      comp_mono_right h_sym ((R /ₛ R)° ≫ R)
    have step2 : (R /ₛ R) ≫ (R /ₛ R)° ≫ R ⊑ (R /ₛ R) ≫ (R /ₛ R) ≫ R :=
      comp_mono_left (R /ₛ R) (comp_mono_right h_sym R)
    have step3 : (R /ₛ R) ≫ (R /ₛ R) ≫ R = ((R /ₛ R) ≫ (R /ₛ R)) ≫ R := (Cat.assoc _ _ _).symm
    have step4 : ((R /ₛ R) ≫ (R /ₛ R)) ≫ R ⊑ R := by
      rw [Cat.assoc]; exact le_trans (comp_mono_left (R /ₛ R) h1) h1
    rw [Cat.assoc]
    exact le_trans step1 (le_trans step2 (step3 ▸ step4))

/-- R/ₛR is an EQUIVALENCE RELATION (§2.351). -/
theorem symmDiv_self_equiv {a b : 𝒜} (R : a ⟶ b) :
    Reflexive (R /ₛ R) ∧ Symmetric (R /ₛ R) ∧ Transitive (R /ₛ R) :=
  ⟨symmDiv_self_reflexive R, symmDiv_self_symmetric R, symmDiv_self_transitive R⟩

/-! ## §2.352  Left cancellation for straight morphisms -/

/-- If S is straight, F and G are simple with same source, and FS = GS, then (dom F)G = (dom G)F (§2.352). -/
theorem straight_cancel_simple {a b c : 𝒜} {S : a ⟶ b} (hS : Straight S)
    {F G : c ⟶ a} (hF : Simple F) (hG : Simple G)
    (h : F ≫ S = G ≫ S) :
    dom F ≫ G = dom G ≫ F := by
  sorry

/-- Helper: from map f, 1 ⊑ f ≫ f° (entireness unfold). -/
private theorem map_entire_le {a b : 𝒜} {f : a ⟶ b} (hf : Map f) : Cat.id a ⊑ f ≫ f° := by
  have := hf.1
  dsimp [Entire, dom] at this
  exact this ▸ inter_lb_right _ _

/-- If S is straight and f, g are maps with fS = gS then f = g (§2.352). -/
theorem straight_cancel {a b c : 𝒜} {S : a ⟶ b} (hS : Straight S)
    {f g : c ⟶ a} (hf : Map f) (hg : Map g) (h : f ≫ S = g ≫ S) : f = g := by
  -- g°f ⊑ S/ₛS ⊑ 1. (g°f)S = g°(fS) = g°(gS) ⊑ (g°g)S ⊑ S; and ((g°f)°)S ⊑ S similarly.
  have hgf_ss : g° ≫ f ⊑ S /ₛ S := by
    rw [le_symmDiv_iff (g° ≫ f) S S]
    constructor
    · -- (g°f)S ⊑ S
      have eq1 : (g° ≫ f) ≫ S = (g° ≫ g) ≫ S := by rw [Cat.assoc, h, ← Cat.assoc]
      rw [eq1]; exact le_trans (comp_mono_right hg.2 S) (by rw [Cat.id_comp]; exact le_refl S)
    · -- (g°f)°S ⊑ S: (g°f)° = f°g°° = f°g
      have heq : (g° ≫ f)° = f° ≫ g := by rw [Allegory.recip_comp, Allegory.recip_recip]
      rw [heq]
      have eq2 : (f° ≫ g) ≫ S = (f° ≫ f) ≫ S := by rw [Cat.assoc, ← h, ← Cat.assoc]
      rw [eq2]; exact le_trans (comp_mono_right hf.2 S) (by rw [Cat.id_comp]; exact le_refl S)
  have hgf1 : g° ≫ f ⊑ Cat.id a := le_trans hgf_ss hS
  have hfg1 : f° ≫ g ⊑ Cat.id a := by
    have key : (g° ≫ f)° = f° ≫ g := by rw [Allegory.recip_comp, Allegory.recip_recip]
    calc f° ≫ g = (g° ≫ f)° := key.symm
        _ ⊑ (Cat.id a)° := recip_mono hgf1
        _ = Cat.id a := recip_id
  apply le_antisymm
  · -- f ⊑ g: 1f ⊑ (gg°)f = g(g°f) ⊑ g1 = g
    have h_id : f ⊑ Cat.id c ≫ f := by dsimp [le]; rw [Cat.id_comp]; exact Allegory.inter_idem f
    have h1 : f ⊑ (g ≫ g°) ≫ f := le_trans h_id (comp_mono_right (map_entire_le hg) f)
    have h2 : g ≫ g° ≫ f ⊑ g ≫ Cat.id a := comp_mono_left g hgf1
    exact Cat.comp_id g ▸ le_trans h1 ((Cat.assoc g g° f).symm ▸ h2)
  · -- g ⊑ f: 1g ⊑ (ff°)g = f(f°g) ⊑ f1 = f
    have h_id : g ⊑ Cat.id c ≫ g := by dsimp [le]; rw [Cat.id_comp]; exact Allegory.inter_idem g
    have h1 : g ⊑ (f ≫ f°) ≫ g := le_trans h_id (comp_mono_right (map_entire_le hf) g)
    have h2 : f ≫ f° ≫ g ⊑ f ≫ Cat.id a := comp_mono_left f hfg1
    exact Cat.comp_id f ▸ le_trans h1 ((Cat.assoc f f° g).symm ▸ h2)

/-! ## §2.353  Converse characterization of straightness -/

/-- Converse of straight_cancel (§2.353): if (FS = GS → (dom F)G = (dom G)F)
    for all simple F, G with the same source, then S is straight.
    (Proof omitted; requires semisimple hypothesis.) -/
theorem straight_of_cancel {a b : 𝒜} {S : a ⟶ b}
    (h : ∀ {c : 𝒜} (F G : c ⟶ a),
        Simple F → Simple G → F ≫ S = G ≫ S → dom F ≫ G = dom G ≫ F) :
    Straight S := by
  sorry

/-! ## §2.355  If SR is straight then S is straight -/

/-- If SR is straight then S is straight (§2.355).
    Proof: S/ₛS ⊑ (SR)/ₛ(SR) ⊑ 1. -/
theorem straight_of_comp_straight {a b c : 𝒜} {S : a ⟶ b} {R : b ⟶ c}
    (h : Straight (S ≫ R)) : Straight S := by
  apply le_trans _ h
  -- Show S/ₛS ⊑ (SR)/ₛ(SR): need (S/ₛS)(SR) ⊑ SR and (S/ₛS)°(SR) ⊑ SR.
  rw [le_symmDiv_iff (S /ₛ S) (S ≫ R) (S ≫ R)]
  have hss_le : (S /ₛ S) ≫ S ⊑ S := ((le_symmDiv_iff (S /ₛ S) S S).mp (le_refl _)).1
  constructor
  · -- (S/ₛS)(SR) = ((S/ₛS)S)R ⊑ SR
    rw [← Cat.assoc]; exact comp_mono_right hss_le R
  · -- (S/ₛS)°(SR) ⊑ SR: (S/ₛS)° ⊑ S/ₛS so (S/ₛS)°S ⊑ (S/ₛS)S ⊑ S
    have h_sym : (S /ₛ S)° ⊑ S /ₛ S := symmDiv_self_symmetric S
    have hss_sym_le : (S /ₛ S)° ≫ S ⊑ S := le_trans (comp_mono_right h_sym S) hss_le
    rw [← Cat.assoc]; exact comp_mono_right hss_sym_le R

/-- Right-invertible morphisms are straight (§2.355). -/
theorem rightInvertible_straight {a b : 𝒜} {S : a ⟶ b} {T : b ⟶ a}
    (h : S ≫ T = Cat.id a) : Straight S := by
  -- S(ST) = (SS)T? No. Use: ST = 1, so straight_of_comp_straight with R=T.
  -- Need Straight (S ≫ T). Since S ≫ T = Cat.id a and Cat.id a is straight, done.
  have h1_straight : Straight (S ≫ T) := by
    rw [h]
    -- Straight (Cat.id a): 1/ₛ1 = (1/1) ∩ (1/1)° = 1 ∩ 1° = 1 ∩ 1 ⊑ 1
    dsimp [Straight, le, symmDiv]
    rw [div_one, recip_id]
    simp [Allegory.inter_idem]
  exact straight_of_comp_straight h1_straight

/-! ## §2.356  If S is straight then R/ₛS is simple -/

/-- If S is straight then R/ₛS is simple (§2.356).
    Proof: (R/ₛS)°(R/ₛS) ⊑ S/ₛS ⊑ 1. -/
theorem straight_symmDiv_simple {a b c : 𝒜} {S : b ⟶ c} (hS : Straight S)
    (R : a ⟶ c) : Simple (R /ₛ S) := by
  dsimp [Simple]
  apply le_trans _ hS
  rw [le_symmDiv_iff]
  -- Let T := (R/ₛS)°(R/ₛS). T° = T (symmetric). TS ⊑ S.
  -- (R/ₛS)S ⊑ R and (R/ₛS)°R ⊑ S, from le_symmDiv for T = R/ₛS.
  have hRS_le : (R /ₛ S) ≫ S ⊑ R := ((le_symmDiv_iff _ _ _).mp (le_refl _)).1
  have hRS_rec : (R /ₛ S)° ≫ R ⊑ S := ((le_symmDiv_iff _ _ _).mp (le_refl _)).2
  constructor
  · -- ((R/ₛS)°(R/ₛS))S ⊑ (R/ₛS)°R ⊑ S
    rw [Cat.assoc]; exact le_trans (comp_mono_left _ hRS_le) hRS_rec
  · -- ((R/ₛS)°(R/ₛS))° ≫ S ⊑ S.
    -- T := (R/ₛS)°(R/ₛS). T° = (R/ₛS)°(R/ₛS)°° = (R/ₛS)°(R/ₛS) = T.
    -- So T° ≫ S = T ≫ S ⊑ S (same as first bullet).
    -- In Lean, ((R/ₛS)° ≫ R/ₛS)° = (R/ₛS)° ≫ (R/ₛS)°° = (R/ₛS)° ≫ R/ₛS.
    -- After rw [recip_comp, recip_recip], goal: (R/ₛS)° ≫ (R/ₛS) ≫ S ⊑ S.
    -- That IS the first bullet (same expression, just associativity).
    rw [Allegory.recip_comp, Allegory.recip_recip]
    -- goal: ((R/ₛS)° ≫ R/ₛS) ≫ S ⊑ S (same as first bullet after assoc)
    exact le_trans (Cat.assoc (R /ₛ S)° (R /ₛ S) S ▸ comp_mono_left _ hRS_le) hRS_rec

/-! ## §2.357  Simple part and domain of simplicity -/

/-- The SIMPLE PART of R: R/ₛ1 (§2.357).
    T ⊑ R/ₛ1 iff T ⊑ R and T°R ⊑ 1 (simplicity of T, contained in R). -/
def simplePart {a b : 𝒜} (R : a ⟶ b) : a ⟶ b := R /ₛ Cat.id b

/-- The DOMAIN OF SIMPLICITY of R: dom(R/ₛ1) (§2.357). -/
def domSimplicity {a b : 𝒜} (R : a ⟶ b) : a ⟶ a := dom (simplePart R)

/-- The simple part is simple (§2.357).
    1_b is straight (right-invertible), so R/ₛ1 is simple by §2.356. -/
theorem simplePart_simple {a b : 𝒜} (R : a ⟶ b) : Simple (simplePart R) := by
  apply straight_symmDiv_simple
  exact rightInvertible_straight (Cat.comp_id (Cat.id b))

/-- The simple part is contained in R: R/ₛ1 ⊑ R (§2.357). -/
theorem simplePart_le {a b : 𝒜} (R : a ⟶ b) : simplePart R ⊑ R := by
  dsimp [simplePart, symmDiv]
  calc (R / Cat.id b) ∩ ((Cat.id b / R)°) ⊑ R / Cat.id b := inter_lb_left _ _
      _ = R := div_one R

/-- R/ₛ1 is the largest simple AR with A coreflexive (§2.357).
    Here the "simple" condition on AR is expressed directly as the
    symmDiv characterization: AR ⊑ R and (AR)°R ⊑ 1.
    (The book's proof of the equivalence with Simple uses A°A = A for coreflexive A.) -/
theorem simplePart_largest {a b : 𝒜} (R : a ⟶ b) (A : a ⟶ a)
    (hA : Coreflexive A) (hAR : (A ≫ R)° ≫ R ⊑ Cat.id b) :
    A ≫ R ⊑ simplePart R := by
  dsimp [simplePart]
  rw [le_symmDiv_iff (A ≫ R) R (Cat.id b)]
  constructor
  · -- (AR) ≫ 1 ⊑ R: AR ⊑ R since A ⊑ 1
    rw [Cat.comp_id]
    exact le_trans (comp_mono_right hA R) (by rw [Cat.id_comp]; exact le_refl R)
  · exact hAR

end Freyd.Alg
