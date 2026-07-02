/-
  Bird & de Moor, *Algebra of Programming* §7.1  Minimum and maximum (book pp. 165-172)
  — CORE (`minRel`, `maxRel`, the universal properties, and (7.5)).

  For `R : a ⟶ a`, B&dM define `min R = ∈ ∩ (R/∋) : A ← PA` — a minimum of `x` under `R`
  is an element of `x` that is also an `R`-lower bound of `x`.

  MIRRORING (diagram order, B&dM `X·Y` = Fredy `Y ≫ X`):
  - B&dM `∈ : A ← PA` is Fredy's `∋ a : powerObj a ⟶ a`; B&dM `∋ = ∈°` is Fredy `(∋ a)°`.
  - B&dM division `R/S` (UP: `X ⊆ R/S ⟺ X·S ⊆ R`) mirrors to Fredy `leftDiv S R`
    (`le_leftDiv_iff : T ⊑ leftDiv S R ↔ S ≫ T ⊑ R`); B&dM `S\R` mirrors to Fredy `R / S`.
  - Hence `min R = ∈ ∩ (R/∋)` mirrors to `minRel R = ∋ a ∩ leftDiv ((∋ a)°) R`.

  Setting: `UnguardedPowerLCDA` (`Fredy.A6_2`) — the chapter-6/7 ambient class giving the
  power operations, division, and complete hom-lattices in one diamond-safe bundle.
-/
import Fredy.A6_2

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {a b : 𝒜}

/-- Division by the identity is trivial: `leftDiv id R = R`. -/
theorem leftDiv_id (R : a ⟶ b) : leftDiv (Cat.id a) R = R := by
  apply le_antisymm
  · have h := leftDiv_comp_le (Cat.id a) R; rwa [Cat.id_comp] at h
  · apply (le_leftDiv_iff _ _ _).mpr; rw [Cat.id_comp]; exact le_refl R

/-! ## `min R` and `max R` (book p.166) -/

/-- **B&dM p.166**: `min R = ∈ ∩ (R/∋)`, mirrored: a minimum of `x` under `R` is a member
    of `x` that is an `R`-lower bound of `x`. -/
def minRel (R : a ⟶ a) : PowerAllegory.powerObj a ⟶ a :=
  ∋ a ∩ leftDiv ((∋ a)°) R

/-- **B&dM p.166**: `max R = min R°`. -/
def maxRel (R : a ⟶ a) : PowerAllegory.powerObj a ⟶ a := minRel R°

theorem minRel_le_eps (R : a ⟶ a) : minRel R ⊑ ∋ a := inter_lb_left _ _

theorem minRel_le_lb (R : a ⟶ a) : minRel R ⊑ leftDiv ((∋ a)°) R := inter_lb_right _ _

/-- The universal property of `min` (book p.166): `X ⊑ min R ⟺ X ⊑ ∈ ∧ X·∋ ⊑ R`,
    mirrored (`X·∋` becomes `(∋ a)° ≫ X`). -/
theorem le_minRel_iff {R : a ⟶ a} {X : PowerAllegory.powerObj a ⟶ a} :
    X ⊑ minRel R ↔ X ⊑ ∋ a ∧ (∋ a)° ≫ X ⊑ R := by
  constructor
  · intro h
    refine ⟨le_trans h (minRel_le_eps R), ?_⟩
    exact le_trans (comp_mono_left _ (le_trans h (minRel_le_lb R))) (leftDiv_comp_le _ _)
  · rintro ⟨h1, h2⟩
    exact le_inter h1 ((le_leftDiv_iff _ _ _).mpr h2)

/-! ## (7.5) and its universal property

  The workhorse: composing `min R` with the power transpose of `S` computes minima over
  the `S`-image.  Key step: `A S` transports lower bounds, `A S ≫ (R/∋) = R/S°` mirrored. -/

/-- `ΛS·(R/∋) = R/S°` mirrored: `A S ≫ leftDiv (∋ a)° R = leftDiv S° R` (B&dM (7.2)). -/
theorem A_comp_lb (S : b ⟶ a) (R : a ⟶ a) :
    A S ≫ leftDiv ((∋ a)°) R = leftDiv S° R := by
  have hS' : (∋ a)° ≫ (A S)° = S° := by rw [← Allegory.recip_comp, A_eps_eq']
  apply le_antisymm
  · apply (le_leftDiv_iff _ _ _).mpr
    have hsimple : (A S)° ≫ A S ⊑ Cat.id _ := (A_is_map' S).2
    have hstep : (A S)° ≫ (A S ≫ leftDiv ((∋ a)°) R) ⊑ leftDiv ((∋ a)°) R := by
      have h := comp_mono_right hsimple (leftDiv ((∋ a)°) R)
      rw [Cat.id_comp] at h
      rwa [Cat.assoc] at h
    have h2 : S° ≫ (A S ≫ leftDiv ((∋ a)°) R) =
        (∋ a)° ≫ ((A S)° ≫ (A S ≫ leftDiv ((∋ a)°) R)) := by
      rw [← hS', Cat.assoc]
    rw [h2]
    exact le_trans (comp_mono_left _ hstep) (leftDiv_comp_le _ _)
  · apply (map_shunt_left (A_is_map' S) _ _).mp
    apply (le_leftDiv_iff _ _ _).mpr
    have h3 : (∋ a)° ≫ ((A S)° ≫ leftDiv S° R) = S° ≫ leftDiv S° R := by
      rw [← Cat.assoc, hS']
    rw [h3]
    exact leftDiv_comp_le _ _

/-- **(7.5)**: `min R·ΛS = S ∩ (R/S°)`, mirrored: `A S ≫ minRel R = S ∩ leftDiv S° R`. -/
theorem A_comp_minRel (S : b ⟶ a) (R : a ⟶ a) :
    A S ≫ minRel R = S ∩ leftDiv S° R := by
  show A S ≫ (∋ a ∩ leftDiv ((∋ a)°) R) = S ∩ leftDiv S° R
  rw [simple_dist_inter (A_is_map' S).2, A_eps_eq', A_comp_lb]

/-- The universal property of (7.5), B&dM's "universal property of min":
    `X ⊑ min R·ΛS ⟺ X ⊑ S ∧ X·S° ⊑ R`, mirrored (`X·S°` becomes `S° ≫ X`). -/
theorem le_A_comp_minRel_iff {S : b ⟶ a} {R : a ⟶ a} {X : b ⟶ a} :
    X ⊑ A S ≫ minRel R ↔ X ⊑ S ∧ S° ≫ X ⊑ R := by
  rw [A_comp_minRel]
  constructor
  · intro h
    refine ⟨le_trans h (inter_lb_left _ _), ?_⟩
    exact le_trans (comp_mono_left _ (le_trans h (inter_lb_right _ _))) (leftDiv_comp_le _ _)
  · rintro ⟨h1, h2⟩
    exact le_inter h1 ((le_leftDiv_iff _ _ _).mpr h2)

/-- **(7.4)**: `min R·τ = id ∩ R`, mirrored: the minimum of a singleton is its sole
    inhabitant precisely on the reflexive part of `R` ((7.5) at `S := id`). -/
theorem singletonMap_comp_minRel (R : a ⟶ a) :
    singletonMap ≫ minRel R = Cat.id a ∩ R := by
  show A (Cat.id a) ≫ minRel R = Cat.id a ∩ R
  rw [A_comp_minRel, recip_id, leftDiv_id]

end Freyd.Alg
