/-
  Freyd & Scedrov, *Categories and Allegories* §1.8–§1.81
  Adjoint functors, reflective/coreflective subcategories.

  §1.81  ADJOINT PAIR OF FUNCTORS — hom-set bijection, unit, counit, triangle identities
  §1.813 REFLECTIVE SUBCATEGORY, REFLECTION
  §1.816 COREFLECTIVE INCLUSION
  §1.815 CLOSURE OPERATION (poset case: idempotent, inflationary, order-preserving)
-/

import Fredy.S1_1
import Fredy.S1_18


universe v u u₁ u₂

namespace Freyd

variable {𝒞 : Type u₁} [Cat.{v} 𝒞] {𝒟 : Type u₂} [Cat.{v} 𝒟]

/-! ## §1.81  Adjoint pair of functors

  F : 𝒞 → 𝒟 and G : 𝒟 → 𝒞 form an ADJOINT PAIR if there is a
  natural equivalence (F A ⟶ B) ≃ (A ⟶ G B) (§1.81).
  F = LEFT-ADJOINT of G, G = RIGHT-ADJOINT of F. -/

/-- An adjoint pair F ⊣ G: a bijection (F A ⟶ B) ≃ (A ⟶ G B)
    natural in A (contravariant) and B (covariant) (§1.81). -/
structure Adjunction (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞) [Functor F] [Functor G] where
  φ {A B} (f : F A ⟶ B) : (A ⟶ G B)
  ψ {A B} (f : A ⟶ G B) : (F A ⟶ B)
  φψ {A B} (f : A ⟶ G B) : φ (ψ f) = f
  ψφ {A B} (f : F A ⟶ B) : ψ (φ f) = f
  φ_nat_left {A' A B} (a : A' ⟶ A) (h : F A ⟶ B) : φ (Functor.map a ≫ h) = a ≫ φ h
  φ_nat_right {A B B'} (h : F A ⟶ B) (b : B ⟶ B') : φ (h ≫ b) = φ h ≫ Functor.map b

infix:25 " ⊣ " => Adjunction

/-- F is a LEFT-ADJOINT of G. -/
class LeftAdjoint (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞) [Functor F] [Functor G] where
  adj : F ⊣ G

/-- G is a RIGHT-ADJOINT of F. -/
class RightAdjoint (G : 𝒟 → 𝒞) (F : 𝒞 → 𝒟) [Functor G] [Functor F] where
  adj : F ⊣ G

section AdjunctionProperties
variable {F : 𝒞 → 𝒟} {G : 𝒟 → 𝒞} [Functor F] [Functor G] (adj : F ⊣ G)

theorem φ_inj {A B} {f₁ f₂ : F A ⟶ B} (h : adj.φ f₁ = adj.φ f₂) : f₁ = f₂ := by
  calc
    f₁ = adj.ψ (adj.φ f₁) := by rw [adj.ψφ]
    _ = adj.ψ (adj.φ f₂) := by rw [h]
    _ = f₂ := by rw [adj.ψφ]

/-! ### Derived naturality for ψ (= φ⁻¹) -/

theorem ψ_nat_left {A' A B} (a : A' ⟶ A) (g : A ⟶ G B) :
    adj.ψ (a ≫ g) = Functor.map a ≫ adj.ψ g :=
  φ_inj adj <| by
    rw [adj.φ_nat_left, adj.φψ, adj.φψ]

theorem ψ_nat_right {A B B'} (g : A ⟶ G B) (b : B ⟶ B') :
    adj.ψ (g ≫ Functor.map b) = adj.ψ g ≫ b :=
  φ_inj adj <| by
    rw [adj.φ_nat_right, adj.φψ, adj.φψ]

/-! ### Unit and counit -/

/-- The UNIT η_A : A → G(F A) is the adjoint of id_{F A} (§1.81). -/
def unit (A : 𝒞) : A ⟶ G (F A) := adj.φ (Cat.id (F A))

/-- The COUNIT ε_B : F(G B) → B is the adjoint of id_{G B} (§1.81). -/
def counit (B : 𝒟) : F (G B) ⟶ B := adj.ψ (Cat.id (G B))

/-- Unit naturality: f ≫ η_B = η_A ≫ G(F f). -/
theorem unit_naturality {A B : 𝒞} (f : A ⟶ B) :
    f ≫ unit adj B = unit adj A ≫ Functor.map (Functor.map f) := by
  dsimp [unit]
  calc
    f ≫ adj.φ (Cat.id (F B)) = adj.φ (Functor.map f ≫ Cat.id (F B)) := by
      rw [adj.φ_nat_left]
    _ = adj.φ (Functor.map f) := by rw [Cat.comp_id]
    _ = adj.φ (Cat.id (F A) ≫ Functor.map f) := by rw [Cat.id_comp]
    _ = adj.φ (Cat.id (F A)) ≫ Functor.map (Functor.map f) := by rw [adj.φ_nat_right]

/-- Counit naturality: F(G f) ≫ ε_B = ε_A ≫ f. -/
theorem counit_naturality {A B : 𝒟} (f : A ⟶ B) :
    Functor.map (Functor.map f) ≫ counit adj B = counit adj A ≫ f := by
  dsimp [counit]
  calc
    Functor.map (Functor.map f) ≫ adj.ψ (Cat.id (G B)) =
      adj.ψ (Functor.map f ≫ Cat.id (G B)) := by
      rw [← ψ_nat_left adj (Functor.map f) (Cat.id (G B))]
    _ = adj.ψ (Functor.map f) := by rw [Cat.comp_id]
    _ = adj.ψ (Cat.id (G A) ≫ Functor.map f) := by rw [Cat.id_comp]
    _ = adj.ψ (Cat.id (G A)) ≫ f := by rw [ψ_nat_right adj (Cat.id (G A)) f]

/-- Triangle identity I: F(η_A) ≫ ε_{F A} = id_{F A}. -/
theorem triangle_one (A : 𝒞) : Functor.map (unit adj A) ≫ counit adj (F A) = Cat.id (F A) := by
  dsimp [unit, counit]
  calc
    Functor.map (adj.φ (Cat.id (F A))) ≫ adj.ψ (Cat.id (G (F A))) =
      adj.ψ (adj.φ (Cat.id (F A)) ≫ Cat.id (G (F A))) := by
      rw [ψ_nat_left adj (adj.φ (Cat.id (F A))) (Cat.id (G (F A)))]
    _ = adj.ψ (adj.φ (Cat.id (F A))) := by rw [Cat.comp_id]
    _ = Cat.id (F A) := by rw [adj.ψφ]

/-- Triangle identity II: η_{G B} ≫ G(ε_B) = id_{G B}. -/
theorem triangle_two (B : 𝒟) : unit adj (G B) ≫ Functor.map (counit adj B) = Cat.id (G B) := by
  dsimp [unit, counit]
  calc
    adj.φ (Cat.id (F (G B))) ≫ Functor.map (adj.ψ (Cat.id (G B))) =
      adj.φ (Cat.id (F (G B)) ≫ adj.ψ (Cat.id (G B))) := by rw [adj.φ_nat_right]
    _ = adj.φ (adj.ψ (Cat.id (G B))) := by rw [Cat.id_comp]
    _ = Cat.id (G B) := by rw [adj.φψ]

/-- φ(h) = η_A ≫ G(h) — reconstruct φ from the unit. -/
theorem φ_eq (h : F A ⟶ B) : adj.φ h = unit adj A ≫ Functor.map h := by
  dsimp [unit]
  calc
    adj.φ h = adj.φ (Cat.id (F A) ≫ h) := by rw [Cat.id_comp]
    _ = adj.φ (Cat.id (F A)) ≫ Functor.map h := by rw [adj.φ_nat_right]

/-- ψ(g) = F(g) ≫ ε_B — reconstruct ψ from the counit. -/
theorem ψ_eq (g : A ⟶ G B) : adj.ψ g = Functor.map g ≫ counit adj B := by
  dsimp [counit]
  calc
    adj.ψ g = adj.ψ (g ≫ Cat.id (G B)) := by rw [Cat.comp_id]
    _ = Functor.map g ≫ adj.ψ (Cat.id (G B)) := by rw [ψ_nat_left adj g (Cat.id (G B))]

end AdjunctionProperties

/-! ## §1.813 Reflective subcategories -/

/-- A subcategory via inclusion I : 𝒜' → 𝒞 is REFLECTIVE
    if I has a left adjoint (§1.813). The left adjoint is the REFLECTION. -/
class ReflectiveSubcategory {𝒜' : Type u₁} [Cat.{v} 𝒜'] (I : 𝒜' → 𝒞) [Functor I] where
  reflection : 𝒞 → 𝒜'
  [refl_functor : Functor reflection]
  adj : LeftAdjoint reflection I

/-- §1.816: A subcategory is COREFLECTIVE if the inclusion has a right adjoint. -/
class CoreflectiveSubcategory {𝒜' : Type u₁} [Cat.{v} 𝒜'] (I : 𝒜' → 𝒞) [Functor I] where
  coreflection : 𝒞 → 𝒜'
  [corefl_functor : Functor coreflection]
  adj : RightAdjoint coreflection I

/-! ## §1.815  Closure operation

  On a poset, a CLOSURE OPERATION is order-preserving, idempotent,
  inflationary (§1.815). For a general category this is an idempotent monad. -/

/-- A CLOSURE OPERATION on a category (§1.815). T is the closure,
    η is the unit (inflationary), idem says Tη is an isomorphism. -/
structure ClosureOperation (𝒞 : Type u) [Cat.{v} 𝒞] where
  T : 𝒞 → 𝒞
  [functor_T : Functor T]
  η : (A : 𝒞) → A ⟶ T A
  η_natural : ∀ {A B} (f : A ⟶ B), f ≫ η B = η A ≫ (Functor.map (F := T) f)
  idem : ∀ (A : 𝒞), IsIso (Functor.map (F := T) (η A))

end Freyd
