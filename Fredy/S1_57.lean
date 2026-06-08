/-
  Freyd & Scedrov, *Categories and Allegories* §1.57
  Choice objects, AC regular categories, projective objects.

  §1.57  CHOICE: every entire relation targeted at C contains a map.
  AC REGULAR CATEGORY: all objects are choice (⇔ all are projective).
  Equivalent: every morphism factors as left-invertible ∘ monic.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasImages 𝒞]

/-! ## §1.57 Choice and projectivity -/

/-- C is CHOICE if every entire relation R : A → C contains a map f : A → C. -/
def IsChoice (C : 𝒞) : Prop :=
  ∀ {A : 𝒞} (R : BinRel 𝒞 A C), IsEntire R →
    ∃ (f : A ⟶ C), ∃ (h : A ⟶ R.src), h ≫ R.colA = f ∧ h ≫ R.colB = Cat.id A

/-- C is PROJECTIVE if every cover f : A ↠ C splits (∃ s: C→A with s≫f = id). -/
def IsProjective (C : 𝒞) : Prop :=
  ∀ {A : 𝒞} (f : A ⟶ C), Cover f → ∃ (s : C ⟶ A), s ≫ f = Cat.id C

/-- Every object is choice iff every object is projective (§1.57). -/
theorem choice_iff_projective : (∀ C : 𝒞, IsChoice C) ↔ (∀ C : 𝒞, IsProjective C) := by
  constructor
  · intro h C A f hcov
    -- f is cover ⇒ its graph is entire ⇒ by choice, contains a map ⇒ that map is a section
    sorry
  · intro h C A R hent
    -- R entire ⇒ its image is a cover ⇒ by projectivity, the cover splits ⇒ we get a map
    sorry

/-- AC REGULAR CATEGORY: all objects are choice. -/
class ACRegularCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasImages 𝒞 where
  all_choice : ∀ C : 𝒞, IsChoice C

/-- In an AC regular category, every f factors as p≫m where p is
    left-invertible (= split epi = cover with section) and m is monic. -/
theorem ac_factorization [ACRegularCategory 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    ∃ (C : 𝒞) (p : A ⟶ C) (m : C ⟶ B),
      (∃ (s : C ⟶ A), s ≫ p = Cat.id A) ∧ Mono m ∧ p ≫ m = f := by
  -- The image of f gives the factorization: let I = image(f), then f = e ≫ m
  -- where e = image.lift f (cover), m = image.arr (monic).
  -- By the AC condition (all objects projective), the cover e splits.
  sorry

end Freyd
