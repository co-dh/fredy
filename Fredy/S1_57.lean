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

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-! ## §1.57 Choice and projectivity -/

/-- **§1.57**: C is CHOICE if every entire relation R : A → C contains a map f : A → C.
    (The map condition: 1_A ≤ R°R and there is a section.) -/
def Choice (C : 𝒞) : Prop :=
  ∀ {A : 𝒞} (R : BinRel 𝒞 A C), Entire R →
    ∃ (f : A ⟶ C), ∃ (h : A ⟶ R.src), h ≫ R.colA = Cat.id A ∧ h ≫ R.colB = f

/-- C is PROJECTIVE if every cover f : A ↠ C splits (∃ s: C→A with s≫f = id). -/
def Projective (C : 𝒞) : Prop :=
  ∀ {A : 𝒞} (f : A ⟶ C), Cover f → ∃ (s : C ⟶ A), s ≫ f = Cat.id C

/-- Every object is choice iff every object is projective (§1.57). -/
axiom choice_iff_projective : (∀ C : 𝒞, Choice C) ↔ (∀ C : 𝒞, Projective C)

/-- AC REGULAR CATEGORY: all objects are choice. -/
class ACRegularCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasPullbacks 𝒞, HasImages 𝒞 where
  all_choice : ∀ C : 𝒞, Choice C

/-- In an AC regular category, every f factors as p≫m where p is a
    split epi (cover with section) and m is monic. -/
axiom ac_factorization [ACRegularCategory 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    ∃ (C : 𝒞) (p : A ⟶ C) (m : C ⟶ B),
      (∃ (s : C ⟶ A), s ≫ p = Cat.id C) ∧ Mono m ∧ p ≫ m = f

end Freyd
