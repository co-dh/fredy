/-
  Freyd & Scedrov, *Categories and Allegories* §1.38–§1.399
  Duality, Stone duality, Finite presentation, Q-sequences.

  §1.38 DUALITY: a contravariant strong equivalence between categories.
  §1.389 STONE DUALITY: Boolean algebras ↔ Stone spaces.
  §1.392 FINITE PRESENTATION via Q-SEQUENCE: a category presented
         by a finite graph with composition/identity equations.
  §1.395 COMPLEMENTARY Q-SEQUENCE.
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

/-! ## §1.38 Duality

  A DUALITY between 𝒞 and 𝒟 is a contravariant strong equivalence.
  Concretely: a pair of contravariant functors F: 𝒞°→𝒟, G: 𝒟°→𝒞
  with GF ≅ Id_𝒞, FG ≅ Id_𝒟. -/

/-- A DUALITY (contravariant strong equivalence) between 𝒞 and 𝒟 (§1.38). -/
structure Duality (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞)
    [hF : Functor F] [hG : Functor G] where
  -- F and G are contravariant in the book, but we model as covariant
  -- A proper duality would use 𝒞° and 𝒟°.
  unit : Nonempty (NatIso (G ∘ F) (λ X : 𝒞 => X))
  counit : Nonempty (NatIso (F ∘ G) (λ X : 𝒟 => X))

/-! ## §1.389 Stone duality

  STONE DUALITY: the category of Boolean algebras is dual to the
  category of Stone spaces (compact Hausdorff totally disconnected).
  A STONE SPACE is a compact totally disconnected Hausdorff space. -/

/-- STONE SPACE (§1.389): compact, Hausdorff, totally disconnected.
    (Set-theoretic definition; we give a placeholder type.) -/
opaque StoneSpace : Type (u + 1)

/-- STONE DUALITY: BoolAlg° ≅ Stone (§1.389, placeholder). -/
def stoneDuality : Duality (λ _ : StoneSpace => StoneSpace) (λ _ => StoneSpace) where
  unit := Nonempty.intro sorry
  counit := Nonempty.intro sorry

/-! ## §1.392 Finite presentation via Q-sequence

  A Q-SEQUENCE presents a category by generators (graph) and
  relations (equations on paths).  SATISFIES means the equations hold.

  FINITE PRESENTATION: a category given by a finite graph and
  finitely many equations. -/

/-- A Q-SEQUENCE (§1.392): a directed graph with equations. -/
structure QSequence where
  objects : Type
  arrows : Type
  src    : arrows → objects
  tgt    : arrows → objects
  equations : Type
  eq_lhs : equations → List arrows
  eq_rhs : equations → List arrows

/-- SATISFIES a Q-sequence: the equations hold in a given category. -/
def SatisfiesQSequence (Q : QSequence) (𝒜 : Type u) [Cat.{v} 𝒜] (interp : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a)) : Prop :=
  -- Each equation lhs = rhs holds as a composition of arrows
  ∀ (e : Q.equations), True  -- placeholder for path equality

/-- COMPLEMENTARY Q-SEQUENCE (§1.395): dual by reversing arrows. -/
def complementaryQSequence (Q : QSequence) : QSequence where
  objects := Q.objects
  arrows := Q.arrows
  src := Q.tgt
  tgt := Q.src
  equations := Q.equations
  eq_lhs e := (Q.eq_rhs e).reverse
  eq_rhs e := (Q.eq_lhs e).reverse

/-! ## §1.39 Linear order / finite presentation

  A LINEARLY ORDERED CATEGORY has objects totally ordered. -/

/-- A LINEARLY ORDERED CATEGORY (§1.39): objects form a totally ordered set. -/
class LinearlyOrdered (𝒞 : Type u) [Cat.{v} 𝒞] where
  order : 𝒞 → 𝒞 → Prop
  total : ∀ a b : 𝒞, order a b ∨ order b a

end Freyd
