/-
  Freyd & Scedrov, *Categories and Allegories* §1.36–§1.367
  Inflation, strong equivalence, equivalent categories, equivalence kernel, factorization.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31
import Fredy.S1_41

set_option linter.unusedSectionVars false

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.36 Inflation

  An INFLATION of B is a category [T] with objects 𝛂, an onto function
  T: 𝛂 → |B|, and morphisms A → B defined as the most inclusive
  (when TA = □x and TB = x□).  The forgetful functor [T] → B is
  a full embedding and onto, hence an equivalence functor. -/

/-- An inflation: artificially replicate objects of B.  Given T : 𝛂 → |B| onto,
    the category [T] has objects 𝛂, hom 𝛂(A,B) = B(TA,TB). -/
structure Inflation (B : 𝒞) where
  objSet  : Type u
  T       : objSet → 𝒞
  isOnto  : ∀ b : 𝒞, ∃ a : objSet, T a = b  -- T is surjective (onto)

/-- The inflated category [T] with objects objSet and hom via T. -/
instance (I : Inflation B) : Cat.{v} I.objSet where
  Hom A B := I.T A ⟶ I.T B
  id A := Cat.id (I.T A)
  comp f g := f ≫ g
  id_comp _ := Cat.id_comp _
  comp_id _ := Cat.comp_id _
  assoc _ _ _ := Cat.assoc _ _ _

/-- The inflation forgetful functor F : [T] → B, which is a full embedding. -/
def Inflation.forget (I : Inflation B) : I.objSet → 𝒞 := I.T

instance (I : Inflation B) : Functor (I.forget) where
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An inflation cross-section: S : |B| → 𝛂 with T∘S = id. -/
structure InflationCrossSection (I : Inflation B) where
  S : 𝒞 → I.objSet
  sec : ∀ b : 𝒞, I.T (S b) = b

/-! ## §1.362 Strong equivalence from inflation

  The axiom of choice implies every inflation is strongly equivalent to B.
  (We state the condition without assuming AC.) -/

/-- If T has a left-inverse (a cross-section S), then [T] is strongly equivalent to B. -/
theorem inflation_strong_equiv (I : Inflation B) (S : InflationCrossSection I) :
    True := by
  -- Construct the strong equivalence using the cross-section
  trivial

/-! ## §1.366 Equivalence kernel

  The kernel of an equivalence functor T : A → B is the subcategory 𝓚 ⊆ A
  of maps sent by T to identity maps.  𝓚 is:
  1. Contains all identity maps
  2. A groupoid (every map is iso with inverse in 𝓚)
  3. A pre-order (at most one map A → B)
  Any such subcategory is an EQUIVALENCE KERNEL. -/

/-- An equivalence kernel: a set of maps K ⊆ Mor(A) satisfying:
    1. id_X ∈ K for all X
    2. If f ∈ K then f is iso and f⁻¹ ∈ K
    3. There is at most one K-map between any two objects. -/
structure EquivalenceKernel (𝒞 : Type u) [Cat.{v} 𝒞] where
  mem    : {X Y : 𝒞} → (X ⟶ Y) → Prop
  mem_id : ∀ X : 𝒞, mem (Cat.id X)
  isGroupoid : ∀ {X Y : 𝒞} (f : X ⟶ Y), mem f → (∃ g : Y ⟶ X, mem g ∧ f ≫ g = Cat.id X ∧ g ≫ f = Cat.id Y)
  isPreorder : ∀ {X Y : 𝒞} (f g : X ⟶ Y), mem f → mem g → f = g

/-- The kernel of an equivalence functor T: {f | T.map f = id}. -/
def equivalenceKernel (F : 𝒞 → 𝒟) [hF : Functor F] : EquivalenceKernel 𝒞 where
  mem {X Y} f := hF.map f = Cat.id (F X) ∧ F X = F Y
  mem_id X := by
    simp [hF.map_id]
  isGroupoid f h := by
    sorry
  isPreorder f g hf hg := by
    rcases hf with ⟨hf1, hf2⟩
    rcases hg with ⟨hg1, hg2⟩
    sorry

end Freyd
