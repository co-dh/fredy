/-
  Bird & de Moor, *Algebra of Programming* §8.1  Thinning (book pp. 193-196) — CORE
  (`thinRel`, its (7.5)-style composition law, and the universal property).

  `thin Q = (∈\∈) ∩ ((∋·Q)/∋) : PA ← PA` takes a set `y` to a subset `x ⊆ y` such that
  every element of `y` has a `Q`-lower bound in `x` — keep a representative collection of
  partial solutions without losing the possibility of a future minimum.

  MIRRORING (diagram order, B&dM `X·Y` = Fredy `Y ≫ X`; B&dM `R/S` = Fredy `leftDiv S R`;
  B&dM `S\R` = Fredy `R / S`):
  - B&dM `∈\∈` is `subsetRel a` (= Freyd's `powerOrder`, `Fredy.A7_1`).
  - B&dM `∋·Q` (`Q` then `∋ = ∈°`) is `Q ≫ (∋ a)°`, and `(∋·Q)/∋` is
    `leftDiv ((∋ a)°) (Q ≫ (∋ a)°)`.
  - The UP `X ⊑ thin Q·ΛS ⟺ ∈·X ⊑ S ∧ X·S° ⊑ ∋·Q` mirrors to
    `X ⊑ A S ≫ thinRel Q ⟺ X ≫ ∋ a ⊑ S ∧ S° ≫ X ⊑ Q ≫ (∋ a)°`.

  Setting: `UnguardedPowerLCDA` (`Fredy.A6_2`), continuing chapter 7's `Fredy.A7_1`.
-/
import Fredy.A7_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {a b : 𝒜}

/-- `ΛW·subset = W/∋` mirrored: `A W ≫ subsetRel a = W / (∋ a)` — the transpose of `W`
    followed by shrinking is exactly "all members come from `W`".  (Ex 7.2's
    `existsImage_comp_subsetRel` is the instance `W := ∋ ≫ R`.) -/
theorem A_comp_subsetRel (W : b ⟶ a) : A W ≫ subsetRel a = W / (∋ a) := by
  apply le_antisymm
  · apply (le_div_iff _ _ _).mpr
    have h1 : subsetRel a ≫ ∋ a ⊑ ∋ a := subsetRel_comp_eps_le
    have h2 : A W ≫ (subsetRel a ≫ ∋ a) ⊑ A W ≫ ∋ a := comp_mono_left _ h1
    rw [A_eps_eq'] at h2
    rwa [Cat.assoc]
  · apply (map_shunt_left (A_is_map' W) _ _).mp
    show (A W)° ≫ (W / ∋ a) ⊑ (∋ a) / (∋ a)
    apply (le_div_iff _ _ _).mpr
    have hcancel : (W / ∋ a) ≫ ∋ a ⊑ W := (le_div_iff _ _ _).mp (le_refl _)
    have h1 : (A W)° ≫ ((W / ∋ a) ≫ ∋ a) ⊑ (A W)° ≫ W := comp_mono_left _ hcancel
    have h2 : (A W)° ≫ W = ((A W)° ≫ A W) ≫ ∋ a := by
      rw [Cat.assoc, A_eps_eq']
    have h3 : ((A W)° ≫ A W) ≫ ∋ a ⊑ Cat.id _ ≫ ∋ a :=
      comp_mono_right (A_is_map' W).2 (∋ a)
    rw [Cat.id_comp] at h3
    rw [h2] at h1
    rw [Cat.assoc]
    exact le_trans h1 h3

/-! ## `thin Q` (B&dM (8.1)) -/

/-- **(8.1)**: `thin Q = (∈\∈) ∩ ((∋·Q)/∋)`, mirrored: shrink a set without losing
    `Q`-lower bounds for any of its members. -/
def thinRel (Q : a ⟶ a) : PowerAllegory.powerObj a ⟶ PowerAllegory.powerObj a :=
  subsetRel a ∩ leftDiv ((∋ a)°) (Q ≫ (∋ a)°)

theorem thinRel_le_subsetRel (Q : a ⟶ a) : thinRel Q ⊑ subsetRel a := inter_lb_left _ _

theorem thinRel_le_lb (Q : a ⟶ a) :
    thinRel Q ⊑ leftDiv ((∋ a)°) (Q ≫ (∋ a)°) := inter_lb_right _ _

/-- Thinning only shrinks: `thin Q ≫ ∋ ⊑ ∋` (members of the output were members of the
    input). -/
theorem thinRel_comp_eps_le (Q : a ⟶ a) : thinRel Q ≫ ∋ a ⊑ ∋ a :=
  le_trans (comp_mono_right (thinRel_le_subsetRel Q) (∋ a)) subsetRel_comp_eps_le

/-- Thinning keeps lower bounds: `∋·thin Q ⊑ Q·∋`-mirrored, `(∋ a)° ≫ thinRel Q ⊑
    Q ≫ (∋ a)°` (every input member has a `Q`-lower bound among the output members). -/
theorem recip_eps_comp_thinRel_le (Q : a ⟶ a) :
    (∋ a)° ≫ thinRel Q ⊑ Q ≫ (∋ a)° :=
  le_trans (comp_mono_left _ (thinRel_le_lb Q)) (leftDiv_comp_le _ _)

/-- The (7.5)-analogue for thinning: `thin Q·ΛS = (S/∋... )`-mirrored,
    `A S ≫ thinRel Q = (S / ∋ a) ∩ leftDiv S° (Q ≫ (∋ a)°)`. -/
theorem A_comp_thinRel (S : b ⟶ a) (Q : a ⟶ a) :
    A S ≫ thinRel Q = (S / ∋ a) ∩ leftDiv S° (Q ≫ (∋ a)°) := by
  show A S ≫ (subsetRel a ∩ leftDiv ((∋ a)°) (Q ≫ (∋ a)°)) = _
  rw [simple_dist_inter (A_is_map' S).2, A_comp_subsetRel, A_comp_lb]

/-- **The universal property of `thin`** (book p.193): `X ⊑ thin Q·ΛS ⟺ ∈·X ⊑ S ∧
    X·S° ⊑ ∋·Q`, mirrored.  Like (7.5)'s UP, this is the workhorse of every calculation
    in the chapter. -/
theorem le_A_comp_thinRel_iff {S : b ⟶ a} {Q : a ⟶ a} {X : b ⟶ PowerAllegory.powerObj a} :
    X ⊑ A S ≫ thinRel Q ↔ X ≫ ∋ a ⊑ S ∧ S° ≫ X ⊑ Q ≫ (∋ a)° := by
  rw [A_comp_thinRel]
  constructor
  · intro h
    constructor
    · exact (le_div_iff _ _ _).mp (le_trans h (inter_lb_left _ _))
    · exact le_trans (comp_mono_left _ (le_trans h (inter_lb_right _ _))) (leftDiv_comp_le _ _)
  · rintro ⟨h1, h2⟩
    exact le_inter ((le_div_iff _ _ _).mpr h1) ((le_leftDiv_iff _ _ _).mpr h2)

end Freyd.Alg
