/-
  Bird & de Moor, *Algebra of Programming* §6.2  Least fixed points (book pp. 140-142).

  CORE of chapter 6: the Knaster-Tarski theorem (Theorem 6.1) for monotonic mappings on
  the hom-sets of a locally complete (distributive) allegory, the `μ`/`ν` operators, and
  the re-reading of relational catamorphisms as least (and greatest) fixed points,
  giving the inclusion laws (6.2)/(6.3).

  Composition throughout is diagram order (`≫`): B&dM `X·Y` mirrors to `Y ≫ X`.  The
  recursion body `φX = R·FX·α°` therefore mirrors to `φX = α° ≫ F.map X ≫ R`
  (`≫` is right-associative).

  Lambek's lemma (the initial algebra `α` is invertible, with inverse the catamorphism
  of `F.map α`; B&dM Ex 6.5 connects it to the fixed-point view) is proved here because
  (6.2)/(6.3) need `α° ≫ α = id` and `α ≫ α° = id`.

  The merge class `UnguardedPowerLCDA` (locally complete + unguarded power over ONE
  `Allegory` base, diamond-safe as in `Fredy.A4_5.DivisionLCDA`) is the ambient setting
  for the whole fixed-point calculus of chapter 6: `Sup`/`Inf` for `μ`/`ν`, division for
  the hylomorphism arguments (§6.3), and `A`/`∋` for `relCata` (`Fredy.A5_5`).
-/
import Fredy.A4_4
import Fredy.A4_5
import Fredy.A5_5

universe u

namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

variable {𝒜 : Type u}

/-! ## §6.2  Theorem 6.1 (Knaster-Tarski)

  For a monotonic `φ` on a hom-set of a locally complete allegory, `φX ⊑ X` and `φX = X`
  have a common least solution `μφ` (= `Inf` of the prefixed points, `Fredy.A4_4`), and
  dually `X ⊑ φX` and `φX = X` have a common greatest solution `νφ`. -/

section KnasterTarski

variable [LocallyCompleteDistributiveAllegory 𝒜] {a b : 𝒜}

/-- A MONOTONIC mapping on a hom-set (B&dM Theorem 6.1: "not necessarily a functor"). -/
def Monotonic (φ : (a ⟶ b) → (a ⟶ b)) : Prop :=
  ∀ {X Y : a ⟶ b}, X ⊑ Y → φ X ⊑ φ Y

/-- `(μX : φX)`: the LEAST fixed point of `φ`, as the `Inf` of the prefixed points. -/
def mu (φ : (a ⟶ b) → (a ⟶ b)) : a ⟶ b := Inf (fun X => φ X ⊑ X)

/-- `(νX : φX)`: the GREATEST fixed point of `φ`, as the `Sup` of the postfixed points. -/
def nu (φ : (a ⟶ b) → (a ⟶ b)) : a ⟶ b := Sup (fun X => X ⊑ φ X)

/-- `μφ` is a lower bound on the prefixed points (KT leastness; B&dM Ex 6.4's rule). -/
theorem mu_le_of_prefixed {φ : (a ⟶ b) → (a ⟶ b)} {T : a ⟶ b} (h : φ T ⊑ T) : mu φ ⊑ T :=
  Inf_le h

/-- **Theorem 6.1, first half**: `μφ` is itself a prefixed point. -/
theorem mu_prefixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : φ (mu φ) ⊑ mu φ :=
  le_Inf (fun _T hT => le_trans (hφ (mu_le_of_prefixed hT)) hT)

theorem mu_postfixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : mu φ ⊑ φ (mu φ) :=
  mu_le_of_prefixed (hφ (mu_prefixed hφ))

/-- **Theorem 6.1 (Knaster-Tarski)**: `μφ` is a fixed point — with `mu_le_of_prefixed`
    (hence `mu_le_of_fixed`), the least solution of `φX ⊑ X` and of `φX = X` coincide. -/
theorem mu_fixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : φ (mu φ) = mu φ :=
  le_antisymm (mu_prefixed hφ) (mu_postfixed hφ)

theorem mu_le_of_fixed {φ : (a ⟶ b) → (a ⟶ b)} {T : a ⟶ b} (h : φ T = T) : mu φ ⊑ T :=
  mu_le_of_prefixed (by rw [h]; exact le_refl T)

/-- `νφ` is an upper bound on the postfixed points. -/
theorem le_nu_of_postfixed {φ : (a ⟶ b) → (a ⟶ b)} {T : a ⟶ b} (h : T ⊑ φ T) : T ⊑ nu φ :=
  le_Sup h

theorem nu_postfixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : nu φ ⊑ φ (nu φ) :=
  Sup_le (fun _T hT => le_trans hT (hφ (le_nu_of_postfixed hT)))

theorem nu_prefixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : φ (nu φ) ⊑ nu φ :=
  le_nu_of_postfixed (hφ (nu_postfixed hφ))

/-- **Theorem 6.1, dual half**: `νφ` is a fixed point — the greatest solution of
    `X ⊑ φX` and of `φX = X` coincide. -/
theorem nu_fixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : φ (nu φ) = nu φ :=
  le_antisymm (nu_prefixed hφ) (nu_postfixed hφ)

theorem le_nu_of_fixed {φ : (a ⟶ b) → (a ⟶ b)} {T : a ⟶ b} (h : φ T = T) : T ⊑ nu φ :=
  le_nu_of_postfixed (by rw [h]; exact le_refl T)

/-- `μ` is monotonic in the mapping: a pointwise-smaller body has a smaller `μ`. -/
theorem mu_le_mu {φ ψ : (a ⟶ b) → (a ⟶ b)} (h : ∀ X, φ X ⊑ ψ X) : mu φ ⊑ mu ψ :=
  le_Inf (fun T hT => mu_le_of_prefixed (le_trans (h T) hT))

/-- `μ` depends only on the body's graph. -/
theorem mu_congr {φ ψ : (a ⟶ b) → (a ⟶ b)} (h : ∀ X, φ X = ψ X) : mu φ = mu ψ :=
  le_antisymm (mu_le_mu fun X => by rw [h]; exact le_refl _)
    (mu_le_mu fun X => by rw [h]; exact le_refl _)

end KnasterTarski

/-! ## The chapter-6 ambient setting

  §6.3's hylomorphism theorem (and §6.5's uniqueness results) need the fixed-point
  calculus above TOGETHER with `relCata` (`Fredy.A5_5`, unguarded power) and division.
  `UnguardedPowerAllegory` already extends `DivisionAllegory`, so one diamond-safe merge
  with the locally complete class covers everything. -/

/-- A locally complete distributive allegory that is ALSO given as an unguarded power
    allegory (diamond-safe merge over one `Allegory` base, as `Fredy.A4_5.DivisionLCDA`). -/
class UnguardedPowerLCDA (𝒜 : Type u) extends
    LocallyCompleteDistributiveAllegory 𝒜, UnguardedPowerAllegory 𝒜

/-- The power side carries division, so the merge is in particular a `DivisionLCDA` —
    lets `Fredy.A4_5`'s division/LCDA lemmas fire in the chapter-6 setting. -/
instance (priority := 100) UnguardedPowerLCDA.toDivisionLCDA [inst : UnguardedPowerLCDA 𝒜] :
    DivisionLCDA 𝒜 := { inst with }

/-! ## Lambek's lemma for `InitialAlgebra` (B&dM Ex 6.5's subject)

  The inverse of `α` is the (map) catamorphism of the algebra `F.map α`; the standard
  argument runs entirely inside the map subcategory, then `recip_of_comp_id` (Prop 4.1,
  `Fredy.A4_2`) identifies the inverse with `α°`. -/

section Lambek

variable [UnguardedPowerAllegory 𝒜] {F : Relator 𝒜 𝒜}

/-- Lambek inverse: `cata (F.map α)`. -/
def InitialAlgebra.alphaInv (I : InitialAlgebra F) : I.t ⟶ F.obj I.t :=
  I.cata (F.map I.α) (F.map_is_map I.α_map)

/-- **Lambek**: `alphaInv ≫ α = id` — both sides solve the `α`-algebra recursion. -/
theorem InitialAlgebra.alphaInv_alpha (I : InitialAlgebra F) :
    I.alphaInv ≫ I.α = Cat.id I.t := by
  have hk : I.α ≫ I.alphaInv = F.map I.alphaInv ≫ F.map I.α := I.cata_comm _ _
  have hmap : Map (I.alphaInv ≫ I.α) := map_comp (I.cata_map _ _) I.α_map
  have hcomm : I.α ≫ (I.alphaInv ≫ I.α) = F.map (I.alphaInv ≫ I.α) ≫ I.α := by
    rw [← Cat.assoc, hk, ← F.map_comp]
  have hid : I.α ≫ Cat.id I.t = F.map (Cat.id I.t) ≫ I.α := by
    rw [Cat.comp_id, F.map_id, Cat.id_comp]
  have h1 := I.cata_unique I.α I.α_map _ hmap hcomm
  have h2 := I.cata_unique I.α I.α_map _ (id_is_map_local I.t) hid
  rw [h1, ← h2]

/-- **Lambek**: `α ≫ alphaInv = id`. -/
theorem InitialAlgebra.alpha_alphaInv (I : InitialAlgebra F) :
    I.α ≫ I.alphaInv = Cat.id (F.obj I.t) := by
  have hk : I.α ≫ I.alphaInv = F.map I.alphaInv ≫ F.map I.α := I.cata_comm _ _
  rw [hk, ← F.map_comp, I.alphaInv_alpha, F.map_id]

/-- The Lambek inverse IS the reciprocal: `alphaInv = α°` (Prop 4.1). -/
theorem InitialAlgebra.alphaInv_eq_recip (I : InitialAlgebra F) : I.alphaInv = I.α° :=
  (recip_of_comp_id (by rw [I.alpha_alphaInv]; exact le_refl _)
    (by rw [I.alphaInv_alpha]; exact le_refl _)).1

/-- `α° ≫ α = id`: the initial algebra is a split (in fact two-sided) iso of maps. -/
theorem InitialAlgebra.recip_alpha_alpha (I : InitialAlgebra F) :
    I.α° ≫ I.α = Cat.id I.t := by
  rw [← I.alphaInv_eq_recip]; exact I.alphaInv_alpha

/-- `α ≫ α° = id`. -/
theorem InitialAlgebra.alpha_alpha_recip (I : InitialAlgebra F) :
    I.α ≫ I.α° = Cat.id (F.obj I.t) := by
  rw [← I.alphaInv_eq_recip]; exact I.alpha_alphaInv

end Lambek

/-! ## §6.2  Catamorphisms as least (and greatest) fixed points: (6.2) and (6.3)

  Because `α` is invertible, the catamorphism UP `α ≫ X = F.map X ≫ R ⟺ X = ⦇R⦈` (5.12)
  re-reads as `X = α° ≫ F.map X ≫ R ⟺ X = ⦇R⦈`: `⦇R⦈` is the UNIQUE fixed point of the
  monotonic body `φX = α° ≫ F.map X ≫ R`, hence equals both `μφ` and `νφ`, and
  Knaster-Tarski turns the equational UP into the inclusion laws (6.2)/(6.3). -/

section CataFix

variable [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}

/-- The recursion body `φX = R·FX·α°` (mirrored: `α° ≫ F.map X ≫ R`) is monotonic. -/
theorem cataBody_monotonic (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c) :
    Monotonic (fun X : I.t ⟶ c => I.α° ≫ F.map X ≫ R) :=
  fun h => comp_mono_left _ (comp_mono_right (F.map_mono h) R)

/-- The catamorphism UP (5.12), fixed-point form: `X = α° ≫ F.map X ≫ R ↔ X = ⦇R⦈`. -/
theorem eq_relCata_iff_fixed (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c)
    (X : I.t ⟶ c) : X = I.α° ≫ F.map X ≫ R ↔ X = relCata I R := by
  rw [← relCata_UP]
  constructor
  · intro h
    have h2 : I.α ≫ X = I.α ≫ (I.α° ≫ F.map X ≫ R) := by rw [← h]
    rw [h2, ← Cat.assoc, I.alpha_alpha_recip, Cat.id_comp]
  · intro h
    rw [← h, ← Cat.assoc, I.recip_alpha_alpha, Cat.id_comp]

/-- `⦇R⦈ = (μX : R·FX·α°)`, mirrored. -/
theorem relCata_eq_mu (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c) :
    relCata I R = mu (fun X : I.t ⟶ c => I.α° ≫ F.map X ≫ R) := by
  have hfix := mu_fixed (cataBody_monotonic I R)
  exact ((eq_relCata_iff_fixed I R _).mp hfix.symm).symm

/-- `⦇R⦈ = (νX : R·FX·α°)`, mirrored. -/
theorem relCata_eq_nu (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c) :
    relCata I R = nu (fun X : I.t ⟶ c => I.α° ≫ F.map X ≫ R) := by
  have hfix := nu_fixed (cataBody_monotonic I R)
  exact ((eq_relCata_iff_fixed I R _).mp hfix.symm).symm

/-- **(6.2)**: `⦇R⦈ ⊑ X ⟸ R·FX·α° ⊑ X`, mirrored. -/
theorem relCata_le_of_prefixed (I : InitialAlgebra F) {c : 𝒜} {R : F.obj c ⟶ c}
    {X : I.t ⟶ c} (h : I.α° ≫ F.map X ≫ R ⊑ X) : relCata I R ⊑ X := by
  rw [relCata_eq_mu]; exact mu_le_of_prefixed h

/-- **(6.3)**: `X ⊑ ⦇R⦈ ⟸ X ⊑ R·FX·α°`, mirrored. -/
theorem le_relCata_of_postfixed (I : InitialAlgebra F) {c : 𝒜} {R : F.obj c ⟶ c}
    {X : I.t ⟶ c} (h : X ⊑ I.α° ≫ F.map X ≫ R) : X ⊑ relCata I R := by
  rw [relCata_eq_nu]; exact le_nu_of_postfixed h

end CataFix

end Freyd.Alg
