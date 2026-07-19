/-
  Bird & de Moor, *Algebra of Programming* §4.6  Power allegories.

  B&dM's power allegory (universal property `f = ΛR ≡ ∈·f = R` for functions `f`) is exactly
  Freyd's `UnguardedPowerAllegory` (Freyd/S2_4.lean): power object `powerObj b`, membership
  `∋ b : powerObj b ⟶ b` (from the power object TO `b`), power transpose `A R : a ⟶ powerObj b`
  for `R : a ⟶ b` (`A R := R /ₛ ∋ b`), unconditionally a map with `A R ≫ ∋ b = R`
  (`A_is_map'`, `A_eps_eq'`).  Composition throughout is diagram order (`≫`).

  Two of B&dM's book formulas are ALREADY Freyd's definitions/theorems and are not restated:
  - p.107 `ΛR = (∈\R) ∩ (R\∈)°` is literally Freyd's `A R := R /ₛ ∋ b` (symmetric division
    unfolds to exactly this meet, §2.331/§2.41).
  - Ex 4.48 `(ΛR)°·ΛS = (R\S) ∩ (S\R)°` is `symm_div_eq_A_comp` in `S2_4.lean`.

  `map_comp_div` (A4_4) and `map_shunt_left` (A4_2) are imported; the private wave-time
  copies were deduped at collection.
-/

import Freyd.S2_4
import AOP.A4_4  -- map_comp_div (and, via A4_2, the shunting rules)

universe u

namespace Freyd.Alg

section DivisionHelpers

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ### Ex 4.49(i) (B&dM p.107): `R` is reflexive and transitive iff `R = R/R`. -/

/-- Ex 4.49(i): for `R : a ⟶ a`, `Reflexive R ∧ Transitive R ↔ R = R / R`. -/
theorem reflexive_transitive_iff_div_self {a : 𝒜} (R : a ⟶ a) :
    (Reflexive R ∧ Transitive R) ↔ R = R / R := by
  constructor
  · rintro ⟨href, htrans⟩
    apply le_antisymm
    · exact (le_div_iff R R R).mpr htrans
    · have step1 : (R / R) ≫ Cat.id a ⊑ (R / R) ≫ R := comp_mono_left _ href
      have step2 : (R / R) ≫ R ⊑ R := div_self_comp_le R
      calc R / R = (R / R) ≫ Cat.id a := (Cat.comp_id _).symm
        _ ⊑ R := le_trans step1 step2
  · intro h
    exact ⟨by rw [h]; exact one_le_div_self R, by rw [h]; exact div_self_idem R⟩

end DivisionHelpers

/-! ## Universal property of `A` and the resulting calculus

    From here on we work in an `UnguardedPowerAllegory`, where `A_is_map'`/`A_eps_eq'` hold
    unconditionally (no box hypothesis), matching B&dM's power allegory exactly. -/

section PowerCalculus

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜]

/-- B&dM p.103 universal property of `Λ` (here `A`): for a map `f`,
    `f = A R ↔ f ≫ ∋ b = R`. -/
theorem A_UP {a b : 𝒜} (R : a ⟶ b) {f : a ⟶ PowerAllegory.powerObj b} (hf : Map f) :
    f = A R ↔ f ≫ ∋ b = R := by
  constructor
  · intro h; rw [h]; exact A_eps_eq' R
  · intro h; exact A_unique R f hf h

/-- `A` is injective: `A R = A S → R = S`. -/
theorem A_injective {a b : 𝒜} {R S : a ⟶ b} (h : A R = A S) : R = S := by
  rw [← A_eps_eq' R, ← A_eps_eq' S, h]

/-- B&dM p.104 fusion law: for a map `f : c ⟶ a`, `A (f ≫ R) = f ≫ A R`. -/
theorem A_fusion {c a : 𝒜} {f : c ⟶ a} (hf : Map f) {b : 𝒜} (R : a ⟶ b) :
    A (f ≫ R) = f ≫ A R := by
  have hmap : Map (f ≫ A R) := map_comp hf (A_is_map' R)
  have heq : (f ≫ A R) ≫ ∋ b = f ≫ R := by rw [Cat.assoc, A_eps_eq']
  exact (A_unique _ _ hmap heq).symm

/-- B&dM p.104 reflection law: `A (∋ b) = 1_{[b]}` (`Λ∈ = id`). -/
theorem A_eps_reflection {b : 𝒜} : A (∋ b) = Cat.id (PowerAllegory.powerObj b) := by
  have heq : Cat.id (PowerAllegory.powerObj b) ≫ ∋ b = ∋ b := Cat.id_comp _
  exact (A_unique _ _ (id_is_map_local _) heq).symm

/-! ## Existential image `E` (B&dM p.104-105)

    Restricted to maps `f`, `existsImage f` is B&dM's power functor `P`
    (`Pf x = {f a | a ∈ x}`).  `E` and `P` are written with the same symbol here since Freyd
    embeds `Map(𝒜)` in `𝒜`. -/

/-- The existential-image map `E R : [a] ⟶ [b]` for `R : a ⟶ b` (B&dM p.104-105). -/
def existsImage {a b : 𝒜} (R : a ⟶ b) : PowerAllegory.powerObj a ⟶ PowerAllegory.powerObj b :=
  A (∋ a ≫ R)

/-- `∈` is an (exactly) natural transformation (B&dM p.105): `E R ≫ ∋ b = ∋ a ≫ R`. -/
theorem existsImage_eps {a b : 𝒜} (R : a ⟶ b) : existsImage R ≫ ∋ b = ∋ a ≫ R := A_eps_eq' _

/-- `A S ≫ E R = A (S ≫ R)` (B&dM p.105), the absorption law driving the rest of §4.6. -/
theorem A_absorption {a b c : 𝒜} (S : c ⟶ a) (R : a ⟶ b) :
    A S ≫ existsImage R = A (S ≫ R) := by
  have hEMap : Map (existsImage R) := A_is_map' _
  have hmap : Map (A S ≫ existsImage R) := map_comp (A_is_map' S) hEMap
  have heq : (A S ≫ existsImage R) ≫ ∋ b = S ≫ R := by
    rw [Cat.assoc, existsImage_eps, ← Cat.assoc, A_eps_eq']
  exact A_unique _ _ hmap heq

/-- `E` preserves identities: `E 1_a = 1_{[a]}`. -/
theorem existsImage_id {a : 𝒜} : existsImage (Cat.id a) = Cat.id (PowerAllegory.powerObj a) := by
  show A (∋ a ≫ Cat.id a) = Cat.id (PowerAllegory.powerObj a)
  rw [Cat.comp_id, A_eps_reflection]

/-- `E` is functorial: `E (R ≫ S) = E R ≫ E S`. -/
theorem existsImage_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    existsImage (R ≫ S) = existsImage R ≫ existsImage S := by
  have h := A_absorption (∋ a ≫ R) S
  rw [Cat.assoc] at h
  exact h.symm

/-- Singleton naturality (B&dM p.106): for a map `f`, `f ≫ singletonMap = singletonMap ≫ E f`. -/
theorem singletonMap_natural {a b : 𝒜} {f : a ⟶ b} (hf : Map f) :
    f ≫ singletonMap = singletonMap ≫ existsImage f := by
  have hL : f ≫ singletonMap = A f := by
    have h := A_fusion hf (Cat.id b)
    rw [Cat.comp_id] at h
    exact h.symm
  have hR : singletonMap ≫ existsImage f = A f := by
    rw [singletonMap, A_absorption, Cat.id_comp]
  rw [hL, hR]

/-! ## The powerset monad (B&dM p.106: "union `μ = E∈`")

    `bigUnion` (Freyd's `⋃`) IS the powerset-monad multiplication `μ`; these are exactly the
    monad laws for the nondeterminism monad.  Kleisli arrows `a ⟶ [b]` are B&dM's set-valued
    functions and `A` is the isomorphism between relations and Kleisli arrows. -/

/-- `bigUnion = E ∋` (definitional: both unfold to `A (∋' ≫ ∋)`). -/
theorem bigUnion_eq_existsImage_eps {a : 𝒜} :
    (bigUnion : PowerAllegory.powerObj (PowerAllegory.powerObj a) ⟶ PowerAllegory.powerObj a)
      = existsImage (∋ a) := rfl

/-- Monad law `μ·τ = id`: `singletonMap ≫ bigUnion = 1`. -/
theorem bigUnion_singleton {a : 𝒜} :
    singletonMap ≫ bigUnion (a := a) = Cat.id (PowerAllegory.powerObj a) := by
  rw [bigUnion_eq_existsImage_eps, singletonMap, A_absorption, Cat.id_comp, A_eps_reflection]

/-- Monad law `μ·Pτ = id`: `E singletonMap ≫ bigUnion = 1`. -/
theorem bigUnion_existsImage_singleton {a : 𝒜} :
    existsImage (singletonMap (a := a)) ≫ bigUnion = Cat.id (PowerAllegory.powerObj a) := by
  rw [bigUnion_eq_existsImage_eps, ← existsImage_comp, singletonMap, A_eps_eq', existsImage_id]

/-- Monad law `μ·μ = μ·Pμ`: `bigUnion ≫ bigUnion = E bigUnion ≫ bigUnion`. -/
theorem bigUnion_assoc {a : 𝒜} :
    bigUnion ≫ bigUnion (a := a)
      = existsImage (bigUnion (a := a)) ≫ bigUnion := by
  have hL : bigUnion (a := PowerAllegory.powerObj a) ≫ bigUnion (a := a)
      = existsImage (∋ (PowerAllegory.powerObj a) ≫ ∋ a) := by
    rw [bigUnion_eq_existsImage_eps (a := PowerAllegory.powerObj a),
        bigUnion_eq_existsImage_eps (a := a), ← existsImage_comp]
  have hR : existsImage (bigUnion (a := a)) ≫ bigUnion (a := a)
      = existsImage (∋ (PowerAllegory.powerObj a) ≫ ∋ a) := by
    rw [bigUnion_eq_existsImage_eps (a := a), ← existsImage_comp, existsImage_eps]
  exact hL.trans hR.symm

/-! ## Ex 4.50 (B&dM p.108): `R` is recovered from its weakest-liberal-precondition data. -/

/-- Ex 4.50: `(∋ b / R) \ ∋ b = R`. -/
theorem leftDiv_div_eps {a b : 𝒜} (R : a ⟶ b) :
    ((∋ b / R) \ (∋ b)) = R := by
  apply le_antisymm
  · have hi : (A R)° ⊑ ∋ b / R := by
      apply (le_div_iff _ _ _).mpr
      calc (A R)° ≫ R = (A R)° ≫ (A R ≫ ∋ b) := by rw [A_eps_eq']
        _ = ((A R)° ≫ A R) ≫ ∋ b := by rw [Cat.assoc]
        _ ⊑ Cat.id _ ≫ ∋ b := comp_mono_right (A_simple R) _
        _ = ∋ b := Cat.id_comp _
    have hent : Cat.id a ⊑ A R ≫ (A R)° := by
      have h := (A_is_map' R).1
      dsimp [Entire, dom] at h
      rw [← h]; exact inter_lb_right _ _
    -- Combine the three `⊑` steps by hand (no `Trans le le le` instance in this repo).
    have key : A R ≫ ((A R)° ≫ ((∋ b / R) \ (∋ b))) ⊑ A R ≫ ∋ b := by
      have s1 : A R ≫ ((A R)° ≫ ((∋ b / R) \ (∋ b)))
          ⊑ A R ≫ ((∋ b / R) ≫ ((∋ b / R) \ (∋ b))) :=
        comp_mono_left _ (comp_mono_right hi _)
      have s2 : A R ≫ ((∋ b / R) ≫ ((∋ b / R) \ (∋ b))) ⊑ A R ≫ ∋ b :=
        comp_mono_left _ (leftDiv_comp_le _ _)
      exact le_trans s1 s2
    have step : Cat.id a ≫ ((∋ b / R) \ (∋ b)) ⊑ A R ≫ ∋ b := by
      have s0 : Cat.id a ≫ ((∋ b / R) \ (∋ b)) ⊑ (A R ≫ (A R)°) ≫ ((∋ b / R) \ (∋ b)) :=
        comp_mono_right hent _
      rw [Cat.assoc] at s0
      exact le_trans s0 key
    rw [Cat.id_comp] at step
    calc ((∋ b / R) \ (∋ b)) ⊑ A R ≫ ∋ b := step
      _ = R := A_eps_eq' R
  · apply (le_leftDiv_iff R (∋ b / R) (∋ b)).mpr
    exact DivisionAllegory.div_comp_le (∋ b) R

/-! ## Ex 4.52 (B&dM p.108): weakest liberal precondition -/

/-- `wlp R` maps a postcondition-set `Y ⊆ b` to `{x ∈ a | ∀ y, x R y → y ∈ Y}`
    (B&dM Ex 4.52). -/
def wlp {a b : 𝒜} (R : a ⟶ b) : PowerAllegory.powerObj b ⟶ PowerAllegory.powerObj a :=
  A (∋ b / R)

/-- `wlp` is contravariantly functorial (sequential composition of programs). -/
theorem wlp_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    wlp (R ≫ S) = wlp S ≫ wlp R := by
  have hmap : Map (wlp S ≫ wlp R) := map_comp (A_is_map' _) (A_is_map' _)
  have heps : (wlp S ≫ wlp R) ≫ ∋ a = ∋ c / (R ≫ S) := by
    rw [Cat.assoc, show wlp R ≫ ∋ a = ∋ b / R from A_eps_eq' _,
      map_comp_div (show Map (wlp S) from A_is_map' _) (∋ b) R,
      show wlp S ≫ ∋ b = ∋ c / S from A_eps_eq' _,
      div_comp_assoc]
  exact (A_unique _ _ hmap heps).symm

/-- B&dM 4.52's refinement order: `R ⊑ S` iff `wlp S ≤ wlp R` in the predicate-transformer
    order `f ≤ g ≡ f ≫ ∋ ⊑ g ≫ ∋`. -/
theorem wlp_antitone_iff {a b : 𝒜} (R S : a ⟶ b) :
    R ⊑ S ↔ wlp S ≫ ∋ a ⊑ wlp R ≫ ∋ a := by
  rw [show wlp S ≫ ∋ a = ∋ b / S from A_eps_eq' _, show wlp R ≫ ∋ a = ∋ b / R from A_eps_eq' _]
  constructor
  · intro h
    apply (le_div_iff _ _ _).mpr
    have s1 : (∋ b / S) ≫ R ⊑ (∋ b / S) ≫ S := comp_mono_left _ h
    have s2 : (∋ b / S) ≫ S ⊑ ∋ b := DivisionAllegory.div_comp_le _ _
    exact le_trans s1 s2
  · intro h
    have hle : R ⊑ ((∋ b / S) \ (∋ b)) := by
      apply (le_leftDiv_iff _ _ _).mpr
      -- `h : ∋ b / S ⊑ ∋ b / R` bounds the LEFT factor, so `comp_mono_right` (not `_left`).
      have s1 : (∋ b / S) ≫ R ⊑ (∋ b / R) ≫ R := comp_mono_right h _
      have s2 : (∋ b / R) ≫ R ⊑ ∋ b := DivisionAllegory.div_comp_le _ _
      exact le_trans s1 s2
    rwa [leftDiv_div_eps] at hle

/-! ## Ex 4.47 (B&dM p.106): singleton/existsImage/bigUnion identities -/

/-- `A R = singletonMap ≫ E R`. -/
theorem A_eq_singleton_existsImage {a b : 𝒜} (R : a ⟶ b) :
    A R = singletonMap ≫ existsImage R := by
  have h := A_absorption (Cat.id a) R
  rw [Cat.id_comp] at h
  exact h.symm

/-- `E R = E (A R) ≫ bigUnion`. -/
theorem existsImage_eq_A_bigUnion {a b : 𝒜} (R : a ⟶ b) :
    existsImage R = existsImage (A R) ≫ bigUnion := by
  rw [bigUnion_eq_existsImage_eps, ← existsImage_comp, A_eps_eq']

end PowerCalculus

end Freyd.Alg
