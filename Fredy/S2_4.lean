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

  /-- ∋ is THICK (§2.41, third containment 1 ⊑ A(R)A°(R), spelled out via §2.413):
      for every R targeted at b there exists a map f with f ≫ ∋ = R.
      The naïve form `1 ⊑ ∋/∋` is vacuous (`one_le_div_self`); Freyd's §2.413 shows
      this existential form IS the thickness condition (it forces A(R) = R/ₛ∋ entire). -/
  eps_thick {b : 𝒜} {c : 𝒜} (R : c ⟶ b) : ∃ (f : c ⟶ powerObj b), Map f ∧ f ≫ eps b = R

/-! ### Notation -/

/-- Epsilon notation ∋ (pronounced "epsiloff" in the book). -/
notation "∋" => PowerAllegory.eps

/-! ### Derived operations -/

/-- A(R) = R /ₛ ∋: the unique map such that A(R)∋ = R (§2.41). -/
def A {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) : a ⟶ PowerAllegory.powerObj b :=
  R /ₛ PowerAllegory.eps b

/-- The thickness witness f for R is contained in A(R) (§2.412/§2.413).
    Used both for entireness of A(R) and the lower bound of A(R)∋ = R.
    f ⊑ A R = R/ₛ∋ via le_symmDiv_iff: f∋ = R (so f∋ ⊑ R) and f°R = (f°f)∋ ⊑ ∋ (Simple f). -/
private theorem thick_witness_le_A {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b)
    {f : a ⟶ PowerAllegory.powerObj b} (hf : Map f) (hfeq : f ≫ ∋ b = R) :
    f ⊑ A R := by
  rw [A, le_symmDiv_iff]
  refine ⟨by rw [hfeq]; exact le_refl _, ?_⟩
  rw [← hfeq, ← Cat.assoc]
  exact le_trans (comp_mono_right hf.2 (∋ b)) (by rw [Cat.id_comp]; exact le_refl _)

/-- A(R) is a map (simple and entire) (§2.41).
    Simple branch: A(R) ⊑ R/∋, and since ∋ is straight R/∋ is simple [§2.356].
    Entire branch: the thickness witness f (a map, f∋ = R) has f ⊑ A R, so
    1 ⊑ ff° ⊑ (A R)(A R)°, whence dom(A R) = 1 [§2.412/§2.413]. -/
theorem A_is_map {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) : Map (A R) := by
  constructor
  · -- Entire (§2.412/§2.413) via the thickness witness f ⊑ A R.
    obtain ⟨f, hf, hfeq⟩ := PowerAllegory.eps_thick (b := b) R
    have hf_le : f ⊑ A R := thick_witness_le_A R hf hfeq
    have h1 : Cat.id a ⊑ f ≫ f° := by
      have := hf.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
    have h2 : f ≫ f° ⊑ A R ≫ (A R)° :=
      le_trans (comp_mono_right hf_le _) (comp_mono_left _ (recip_mono hf_le))
    -- dom(A R) = 1 ∩ (A R)(A R)° = 1, since 1 ⊑ (A R)(A R)°.
    dsimp [Entire, dom]
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) (le_trans h1 h2))
  · -- Simple: A(R) = R/ₛ∋, and ∋ is straight, so R/ₛ∋ is simple [§2.356].
    exact straight_symmDiv_simple (PowerAllegory.eps_straight b) R

/-- A(R)∋ = R (§2.41).
    ⊑: A(R) ⊑ R/∋ (left component of symmDiv), so A(R)∋ ⊑ (R/∋)∋ ⊑ R.
    ⊒: thickness gives a map f ⊑ A(R) with f∋ = R, so R = f∋ ⊑ (A R)∋ [§2.413]. -/
theorem A_eps_eq {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) : A R ≫ ∋ b = R := by
  apply le_antisymm
  · -- A(R) ≫ ∋ ⊑ R: first component of le_symmDiv_iff
    exact ((le_symmDiv_iff _ R _).mp (le_refl _)).1
  · -- R = f∋ ⊑ (A R)∋ via the thickness witness f ⊑ A R.
    obtain ⟨f, hf, hfeq⟩ := PowerAllegory.eps_thick (b := b) R
    calc R = f ≫ ∋ b := hfeq.symm
      _ ⊑ A R ≫ ∋ b := comp_mono_right (thick_witness_le_A R hf hfeq) (∋ b)

/-! ## §2.415  Power object and singleton map -/

/-- The SINGLETON MAP of a is A(1_a) : a → [a] (§2.415). -/
def singletonMap {a : 𝒜} [PowerAllegory 𝒜] : a ⟶ PowerAllegory.powerObj a :=
  A (Cat.id a)

/-- Singleton map is monic (§2.415): A(1_a)A(1_a)° ⊑ 1.
    Proof: A(1)A°(1) ⊑ (1/∋)(∋/1) = (1/∋)∋ ⊑ 1. -/
theorem singletonMap_monic {a : 𝒜} [PowerAllegory 𝒜] :
    singletonMap (a := a) ≫ singletonMap° ⊑ Cat.id a := by
  -- singletonMap = A(1_a) = 1/ₛ∋ ⊑ 1/∋.
  -- singletonMap° ⊑ ∋/1 = ∋ (reciprocal of second component of symmDiv).
  -- So singletonMap ≫ singletonMap° ⊑ (1/∋) ≫ ∋ ⊑ 1.
  dsimp only [singletonMap, A]
  -- singletonMap is Cat.id a /ₛ ∋ a, unfold for the proof
  have h1 : Cat.id a /ₛ ∋ a ⊑ Cat.id a / ∋ a := inter_lb_left _ _
  -- (1/ₛ∋)° ⊑ ∋: (1/ₛ∋)° = ((1/∋) ∩ (∋/1)°)° = (1/∋)° ∩ ∋/1 ⊑ ∋/1 = ∋
  have h2 : (Cat.id a /ₛ ∋ a)° ⊑ ∋ a := by
    dsimp [symmDiv]
    rw [Allegory.recip_inter, div_one]
    exact le_trans (inter_lb_right _ _) (by rw [Allegory.recip_recip]; exact le_refl _)
  exact le_trans (comp_mono_right h1 _)
    (le_trans (comp_mono_left _ h2) (div_comp_eq_le _ _))

/-- Composition of maps is a map (§2.13).
    Simple: (fg)°(fg) = g°(f°f)g ⊑ g°g ⊑ 1.
    Entire: 1 ⊑ ff° = f1f° ⊑ f(gg°)f° = (fg)(fg)°, so dom(fg) = 1. -/
theorem map_comp {𝒜 : Type u} [Allegory 𝒜] {a b c : 𝒜} {f : a ⟶ b} {g : b ⟶ c}
    (hf : Map f) (hg : Map g) : Map (f ≫ g) := by
  refine ⟨?_, ?_⟩
  · -- Entire: 1 ⊑ ff° ⊑ f(gg°)f° = (fg)(fg)°.
    have hfe : Cat.id a ⊑ f ≫ f° := by
      have := hf.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
    have hge : Cat.id b ⊑ g ≫ g° := by
      have := hg.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
    -- ff° = f1f° ⊑ f(gg°)f°
    have hstep : f ≫ f° ⊑ f ≫ (g ≫ g°) ≫ f° := by
      calc f ≫ f° = f ≫ Cat.id b ≫ f° := by rw [Cat.id_comp]
        _ ⊑ f ≫ (g ≫ g°) ≫ f° := comp_mono_left f (comp_mono_right hge f°)
    have heq : f ≫ (g ≫ g°) ≫ f° = (f ≫ g) ≫ (f ≫ g)° := by
      rw [Allegory.recip_comp]; simp [Cat.assoc]
    have hfin : Cat.id a ⊑ (f ≫ g) ≫ (f ≫ g)° := heq ▸ le_trans hfe hstep
    dsimp [Entire, dom]; exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hfin)
  · -- Simple: (fg)°(fg) = g°(f°f)g ⊑ g°1g = g°g ⊑ 1.
    have hrw : (f ≫ g)° ≫ (f ≫ g) = g° ≫ (f° ≫ f) ≫ g := by
      rw [Allegory.recip_comp]; simp [Cat.assoc]
    have h1 : g° ≫ (f° ≫ f) ≫ g ⊑ g° ≫ g := by
      calc g° ≫ (f° ≫ f) ≫ g ⊑ g° ≫ Cat.id b ≫ g := comp_mono_left g° (comp_mono_right hf.2 g)
        _ = g° ≫ g := by rw [Cat.id_comp]
    dsimp [Simple]; rw [hrw]; exact le_trans h1 hg.2

/-! ## §2.412  Uniqueness of A(R) -/

/-- A(R) is the UNIQUE map F with F∋ = R (§2.412).
    Uniqueness: if F is a map and F∋ = R then F = A(R).
    This follows from straightness of ∋: ∋ /ₛ ∋ ⊑ 1 forces A(R) uniqueness. -/
theorem A_unique {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) (F : a ⟶ PowerAllegory.powerObj b)
    (hF : Map F) (hFeq : F ≫ ∋ b = R) : F = A R := by
  -- Step 1: F ⊑ A R = R /ₛ ∋ via le_symmDiv_iff
  have hF_le : F ⊑ A R := by
    rw [A, le_symmDiv_iff]
    refine ⟨?_, ?_⟩
    · rw [hFeq]; exact le_refl R
    · -- F° R ⊑ ∋: F°(F ∋) = (F°F)∋ ⊑ 1∋ = ∋ via Simple F
      rw [← hFeq, ← Cat.assoc]
      exact le_trans (comp_mono_right hF.2 (∋ b)) (by rw [Cat.id_comp]; exact le_refl _)
  -- Helper: (A R) ≫ ∋ b ⊑ R
  have hAR_eps : A R ≫ ∋ b ⊑ R := ((le_symmDiv_iff _ R _).mp (le_refl _)).1
  -- Helper: (A R)° ≫ R ⊑ ∋ b
  have hARo_R : (A R)° ≫ R ⊑ ∋ b := ((le_symmDiv_iff _ R _).mp (le_refl _)).2
  -- Step 2: F° ≫ A R ⊑ ∋ /ₛ ∋ ⊑ 1
  have hFoAR : F° ≫ A R ⊑ Cat.id (PowerAllegory.powerObj b) := by
    apply le_trans _ (PowerAllegory.eps_straight b)
    rw [le_symmDiv_iff]
    refine ⟨?_, ?_⟩
    · -- (F° ≫ A R) ≫ ∋ ⊑ ∋
      have step1 : (F° ≫ A R) ≫ ∋ b ⊑ F° ≫ R := by
        rw [Cat.assoc]; exact comp_mono_left F° hAR_eps
      have step2 : F° ≫ R ⊑ ∋ b := by
        rw [← hFeq, ← Cat.assoc]
        exact le_trans (comp_mono_right hF.2 (∋ b)) (by rw [Cat.id_comp]; exact le_refl _)
      exact le_trans step1 step2
    · -- (F° ≫ A R)° ≫ ∋ = (A R)° ≫ F ≫ ∋ ⊑ ∋
      rw [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc, hFeq]
      exact hARo_R
  -- Step 3: Entire F: 1 ⊑ F ≫ F°, so A R ⊑ F(F°(A R)) ⊑ F·1 = F
  have hent : Cat.id a ⊑ F ≫ F° := by
    have h := hF.1; dsimp [Entire, dom] at h
    rw [← h]; exact inter_lb_right _ _
  have hAR_le_F : A R ⊑ F := by
    -- A R = 1_a ≫ A R ⊑ (F F°) A R = F (F° A R) ⊑ F 1 = F
    have h1 : Cat.id a ≫ A R ⊑ (F ≫ F°) ≫ A R := comp_mono_right hent _
    rw [Cat.id_comp] at h1
    have h2 : (F ≫ F°) ≫ A R = F ≫ F° ≫ A R := Cat.assoc _ _ _
    rw [h2] at h1
    have h3 : F ≫ F° ≫ A R ⊑ F ≫ Cat.id _ := comp_mono_left F hFoAR
    have h4 : F ≫ Cat.id (PowerAllegory.powerObj b) = F := Cat.comp_id _
    rw [h4] at h3
    exact le_trans h1 h3
  exact le_antisymm hF_le hAR_le_F

/-- For any map f : a → b, A(f) = f ≫ A(1_b) (§2.415).
    Book: "For any map p →ᶠ a, A(f) = f A(1) since f A(1) is a map and f A(1) ∋ = f."
    Relies on A_eps_eq and uniqueness of A(R) [A_unique]. -/
theorem A_of_map {a b : 𝒜} [PowerAllegory 𝒜] (f : a ⟶ b) (hf : Map f) :
    A f = f ≫ singletonMap (a := b) := by
  -- F := f ≫ singletonMap is a map (composition of maps) with F∋ = f, so F = A f by uniqueness.
  refine (A_unique f (f ≫ singletonMap) (map_comp hf (A_is_map _)) ?_).symm
  -- (f ≫ A(1_b))∋ = f ≫ (A(1_b)∋) = f ≫ 1_b = f, since A(1_b)∋ = 1_b by A_eps_eq.
  rw [singletonMap, Cat.assoc, A_eps_eq, Cat.comp_id]

/-- If F is simple then F ⊑ A(F∋) (§2.412).
    Book: "Indeed, if F is simple then F ⊂ A(F∋)."
    Proof: need F ⊑ (F∋)/ₛ∋, i.e. F∋ ⊑ F∋ (trivial) and F°(F∋) ⊑ ∋,
    which follows from F°F ⊑ 1 and A(R)∋ = R. -/
theorem simple_le_A_eps {a b : 𝒜} [PowerAllegory 𝒜] (F : a ⟶ PowerAllegory.powerObj b)
    (hF : Simple F) : F ⊑ A (F ≫ ∋ b) := by
  -- A (F ≫ ∋ b) = (F ≫ ∋ b) /ₛ ∋ b. By le_symmDiv_iff, F ⊑ (F∋)/ₛ∋ iff
  -- (1) F ≫ ∋ ⊑ F ≫ ∋ (trivial) and (2) F° ≫ (F ≫ ∋) ⊑ ∋.
  -- (2): F°(F ∋) = (F°F)∋ ⊑ 1∋ = ∋ via Simple F (F°F ⊑ 1).
  rw [A, le_symmDiv_iff]
  refine ⟨le_refl _, ?_⟩
  -- F° ≫ (F ≫ ∋ b) = (F° ≫ F) ≫ ∋ b ⊑ Cat.id _ ≫ ∋ b = ∋ b
  rw [← Cat.assoc]
  exact le_trans (comp_mono_right hF (∋ b)) (by rw [Cat.id_comp]; exact le_refl _)

/-! ## §2.42  Splitting lemmas

  If A is a power allegory then Spl(Cor(A)) is a power allegory (§2.42). -/

/-! ## §2.421  R/S = A(R)A°(S)

  In a power allegory, R /ₛ S = A(R) ≫ (A S)° for any R : a → c, S : b → c. -/

/-- §2.421: in a power allegory, the symmetric division R /ₛ S equals A(R) ≫ (A S)°. -/
theorem symm_div_eq_A_comp {a b c : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ c) (S : b ⟶ c) :
    R /ₛ S = A R ≫ (A S)° := by
  apply le_antisymm
  · -- R/ₛS ⊑ A(R) ≫ (A S)° (§2.421), using A(R) entire and A_eps_eq.
    -- Step A: (R/ₛS)° ≫ A R ⊑ A S, hence (A R)° ≫ (R/ₛS) ⊑ (A S)°.
    -- Step B: R/ₛS ⊑ (A R · A R°) (R/ₛS) = A R ((A R)° (R/ₛS)) ⊑ A R (A S)°.
    have hARS_le : (R /ₛ S) ≫ S ⊑ R := ((le_symmDiv_iff _ _ _).mp (le_refl _)).1
    have hARS_rec : (R /ₛ S)° ≫ R ⊑ S := ((le_symmDiv_iff _ _ _).mp (le_refl _)).2
    have hAR_eps : A R ≫ ∋ c ⊑ R := ((le_symmDiv_iff _ R _).mp (le_refl _)).1
    have hARo_R : (A R)° ≫ R ⊑ ∋ c := ((le_symmDiv_iff _ R _).mp (le_refl _)).2
    -- Step A: (R/ₛS)° ≫ A R ⊑ A S = S /ₛ ∋.
    have hstepA : (R /ₛ S)° ≫ A R ⊑ A S := by
      show (R /ₛ S)° ≫ A R ⊑ S /ₛ ∋ c
      rw [le_symmDiv_iff]
      refine ⟨?_, ?_⟩
      · -- ((R/ₛS)° ≫ A R) ≫ ∋ = (R/ₛS)° ≫ (A R ≫ ∋) ⊑ (R/ₛS)° ≫ R ⊑ S
        rw [Cat.assoc]
        exact le_trans (comp_mono_left _ hAR_eps) hARS_rec
      · -- ((R/ₛS)° ≫ A R)° ≫ S = (A R)° ≫ ((R/ₛS) ≫ S) ⊑ (A R)° ≫ R ⊑ ∋
        rw [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
        exact le_trans (comp_mono_left _ hARS_le) hARo_R
    -- (A R)° ≫ (R/ₛS) ⊑ (A S)° by reciprocating hstepA.
    have hstepA' : (A R)° ≫ (R /ₛ S) ⊑ (A S)° := by
      have := recip_mono hstepA
      rwa [Allegory.recip_comp, Allegory.recip_recip] at this
    -- Step B: 1 ⊑ A R ≫ (A R)° (A R is entire), so R/ₛS ⊑ (A R · A R°)(R/ₛS).
    have hAR_ent : Cat.id a ⊑ A R ≫ (A R)° := by
      have := (A_is_map R).1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
    have hb1 : R /ₛ S ⊑ (A R ≫ (A R)°) ≫ (R /ₛ S) := by
      have := comp_mono_right hAR_ent (R /ₛ S); rwa [Cat.id_comp] at this
    have hb2 : (A R ≫ (A R)°) ≫ (R /ₛ S) ⊑ A R ≫ (A S)° := by
      rw [Cat.assoc]; exact comp_mono_left _ hstepA'
    exact le_trans hb1 hb2
  · -- A(R) ≫ (A S)° ⊑ R/ₛS: by le_symmDiv_iff, need:
    -- (1) (A R ≫ (A S)°) ≫ S ⊑ R
    -- (2) (A R ≫ (A S)°)° ≫ R ⊑ S
    rw [le_symmDiv_iff]
    constructor
    · -- (A R ≫ (A S)°) ≫ S = A R ≫ ((A S)° ≫ S) ⊑ A R ≫ ∋ ⊑ R
      rw [Cat.assoc]
      have h1 : (A S)° ≫ S ⊑ ∋ c :=
        ((le_symmDiv_iff _ S _).mp (le_refl _)).2
      have h2 : A R ≫ ∋ c ⊑ R :=
        ((le_symmDiv_iff _ R _).mp (le_refl _)).1
      exact le_trans (comp_mono_left (A R) h1) h2
    · -- (A R ≫ (A S)°)° ≫ R = A S ≫ (A R)° ≫ R ⊑ A S ≫ ∋ ⊑ S
      rw [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
      have h1 : (A R)° ≫ R ⊑ ∋ c :=
        ((le_symmDiv_iff _ R _).mp (le_refl _)).2
      have h2 : A S ≫ ∋ c ⊑ S :=
        ((le_symmDiv_iff _ S _).mp (le_refl _)).1
      exact le_trans (comp_mono_left (A S) h1) h2

/-! ## §2.422  Equivalence relations in power allegories

  In any division allegory, E²=E for any equivalence relation E.
  In a power allegory every equivalence relation is of the form ff°. -/

-- §2.414 (a topos ↔ a unitary tabular power allegory: C topos ⟹ Rel(C) power
-- allegory, and Map of a unitary tabular power allegory is a topos) is recorded
-- MISSING in S2_4.md — stating it faithfully needs the Rel(C)/Map(A) bridge between
-- the categorical (Topos, S1_9) and allegorical worlds, not yet built. Per the
-- integrity rule we do NOT emit a vacuous `: True` stub.

/-! ## §2.43  Pre-power allegory and diagonal proofs

  Freyd's thickness (§2.412, §2.43): for the membership relation ∋, T is thick
  iff `Δ(R) = R/ₛ∋` is entire for every R.  Generalising to an arbitrary T, a
  morphism T : a → b is THICK iff the *symmetric* division `R/ₛT` is entire for
  every R : c → b that is COMPATIBLE with T, i.e. shares T's codomain box
  `R□ = T□` (where `R□ = 1_b ∩ R°R`).  The box side-condition is exactly the
  domain on which Freyd's partial division `R/T` is defined (§2.33), and it is
  indispensable: without it the predicate becomes strictly stronger than the
  §2.431 right-hand side (verified exhaustively in Rel up to 3×3).

  ⚠ The earlier formulation `∀R, Entire (R/T)` using the PLAIN (asymmetric) right
  division and DROPPING the `R□ = T□` guard is NOT Freyd's thickness: it made the
  §2.431 forward direction FALSE.  Counterexample (Rel): T = {(0,0)} : {0,1}→{0},
  R = {(0,0),(1,0)} have `R□ = T□` and T is thick, yet the *plain* witness `R/T`
  fails `(R/T)°R ⊑ T`.  The honest witness is the SYMMETRIC division `R/ₛT`, which
  IS entire here — captured by the corrected definition below.

  A PRE-POWER ALLEGORY is a division allegory in which each object
  appears as the target of a thick morphism (§2.43). -/

/-- The codomain box `R□ = 1_b ∩ R°R` (§2.122): the coreflexive on the target. -/
abbrev codBox {a b : 𝒜} [Allegory 𝒜] (R : a ⟶ b) : b ⟶ b := dom (R°)

/-- T : a → b is THICK (§2.412, §2.43) iff the symmetric division `R/ₛT` is entire
    for every R : c → b with the same codomain box `R□ = T□` (Freyd's `Δ(R)`
    entireness condition, stated for a general T rather than just ∋).
    The `codBox R = codBox T` guard is the domain on which Freyd's `R/T` is defined
    and is necessary for §2.431 to be a biconditional (see the note above). -/
def Thick {a b : 𝒜} [DivisionAllegory 𝒜] (T : a ⟶ b) : Prop :=
  ∀ (c : 𝒜) (R : c ⟶ b), codBox R = codBox T → Entire (R /ₛ T)

/-- `Entire R ↔ 1 ⊑ RR°` (§2.122): since `dom R = 1 ∩ RR°` and `1 ∩ RR° ⊑ 1` always,
    `dom R = 1` is equivalent to `1 ⊑ RR°`. -/
private theorem entire_iff_one_le {a b : 𝒜} [Allegory 𝒜] (R : a ⟶ b) :
    Entire R ↔ Cat.id a ⊑ R ≫ R° := by
  dsimp [Entire, dom]
  constructor
  · intro h; rw [← h]; exact inter_lb_right _ _
  · intro h; exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) h)

/-- §2.431 (faithful, biconditional): T is thick iff for every R : c → b with the
    same codomain box `R□ = T□` there exists R̃ : c → a satisfying Freyd's three
    containments `1 ⊑ R̃R̃°` (entire), `R̃T ⊑ R`, `R̃°R ⊑ T`.

    The `R□ = T□` hypothesis is Freyd's own side-condition (the domain on which his
    partial division `R/T` is defined); restoring it — together with the SYMMETRIC
    division in the definition of `Thick` — makes the biconditional TRUE.  It is
    not falsified by the Rel counterexample (T = {(0,0)}, R = {(0,0),(1,0)}): there
    `R□ = T□` holds, T is thick, and the honest witness `R̃ = R/ₛT = {(0,0),(1,0)}`
    IS entire and satisfies all three containments.

    Forward: take `R̃ = R/ₛT`, entire by `Thick T` (consuming the box hypothesis);
    the last two containments are the defining property of `/ₛ`.
    Reverse: `R̃ ⊑ R/ₛT` and `R̃` entire force `R/ₛT` entire. -/
theorem thick_iff_existential {a b : 𝒜} [DivisionAllegory 𝒜] (T : a ⟶ b) :
    Thick T ↔ ∀ (c : 𝒜) (R : c ⟶ b), codBox R = codBox T → ∃ (R' : c ⟶ a),
        Entire R' ∧ R' ≫ T ⊑ R ∧ R'° ≫ R ⊑ T := by
  constructor
  · -- Thick T → ∃R̃.  Witness R̃ = R/ₛT: entire by Thick (using R□ = T□), and the
    -- two containments R̃T ⊑ R, R̃°R ⊑ T are the symmetric-division law applied to
    -- R/ₛT ⊑ R/ₛT.
    intro hThick c R hBox
    refine ⟨R /ₛ T, hThick c R hBox, ?_, ?_⟩
    · exact ((le_symmDiv_iff (R /ₛ T) R T).mp (le_refl _)).1
    · exact ((le_symmDiv_iff (R /ₛ T) R T).mp (le_refl _)).2
  · -- ∃R̃ → Thick T: given R̃ entire with R̃T ⊑ R and R̃°R ⊑ T, we have R̃ ⊑ R/ₛT,
    -- so 1 ⊑ R̃R̃° ⊑ (R/ₛT)(R/ₛT)°, i.e. R/ₛT is entire.  Hence Thick T.
    intro hEx c R hBox
    obtain ⟨R', hEnt, hRT, hRoR⟩ := hEx c R hBox
    have hR'_le : R' ⊑ R /ₛ T := (le_symmDiv_iff R' R T).mpr ⟨hRT, hRoR⟩
    rw [entire_iff_one_le]
    refine le_trans ((entire_iff_one_le R').mp hEnt) ?_
    exact le_trans (comp_mono_right hR'_le _) (comp_mono_left _ (recip_mono hR'_le))

/-- A PRE-POWER ALLEGORY (§2.43): division allegory where each object
    is the target of some thick morphism. -/
class PrePowerAllegory (𝒜 : Type u) extends DivisionAllegory 𝒜 where
  /-- For each object a, there exists a thick morphism with target a. -/
  thick_target (a : 𝒜) : ∃ (x : 𝒜) (S : x ⟶ a), Thick S

/-! ## §2.432  Effective pre-power allegory is power

  An effective pre-power allegory is a power allegory (§2.432). -/
/-- §2.432: an effective pre-power allegory is a power allegory.
    FAITHFUL SORRY (infrastructure gap, not a false statement).  Freyd's proof
    factors a given thick T as `T = hS` with `S = h°T` straight (§2.354), shows S
    stays thick, and takes [a]/∋ from that straight-thick S.  The blocker is the
    §2.354 factorization "in an effective division allegory every morphism is `hS`
    with S straight" plus the §2.432 lemma "S = h°T remains thick", neither of
    which is yet available in S2_3.  Building the `PowerAllegory` instance also
    requires assembling `powerObj`/`eps` and proving `eps_thick` from that S. -/
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

/-- A pre-positive power allegory is semi-simple iff it obeys the law of metonymy (§2.442).
    FAITHFUL SORRY (infrastructure gap, not a false statement).  Freyd's §2.442 argument
    relates semi-simplicity to `⊓ ⊑ ⊔` through the pre-positive splitting `ff° ∪ gg° = 1`
    and the membership calculus for `bigInter = A(∋∋)` / `bigUnion = A(ε'\∋)`.  The blocker
    is the missing big-intersection/big-union equational lemmas (how `∋` interacts with the
    `A(·)` adjunction across `[[a]]`) plus the §2.441 disjointness arithmetic; these are not
    yet derived in S2_3/S2_4. -/
theorem pre_positive_semi_simple_iff_metonymic {𝒜 : Type u}
    [PowerAllegory 𝒜] [PrePositiveAllegory 𝒜] :
    (∀ (a b : 𝒜) (R : a ⟶ b), SemiSimple R) ↔ MetonymyLaw 𝒜 := by
  sorry

end Freyd.Alg
