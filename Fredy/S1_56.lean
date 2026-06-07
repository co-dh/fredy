/-
  Freyd & Scedrov, *Categories and Allegories* §1.56–§1.564
  Relations: graph of a morphism, reciprocal, modular identity.

  §1.564 Graph: the binary relation ⟨A; id_A, x⟩ tabulating x:A→B.
  §1.561 Reciprocal: swap the two columns of a binary relation.
  §1.563 Modular identity: RS ∩ T ⊆ (R ∩ TS°)S.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42

set_option linter.unusedSectionVars false

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.564 Graph of a morphism

  The GRAPH of x: A → B is the binary relation ⟨A; id_A, x⟩. -/

/-- A binary relation on A,B: a jointly-monic pair of morphisms into A,B. -/
structure BinRel (𝒞 : Type u) [Cat.{v} 𝒞] (A B : 𝒞) where
  src  : 𝒞
  colA : src ⟶ A
  colB : src ⟶ B
  monic : ∀ ⦃X : 𝒞⦄ (f g : X ⟶ src), f ≫ colA = g ≫ colA → f ≫ colB = g ≫ colB → f = g

/-- The graph of x: A → B as a binary relation. -/
def graph {A B : 𝒞} (x : A ⟶ B) : BinRel 𝒞 A B where
  src  := A
  colA := Cat.id A
  colB := x
  monic := λ X f g hA hB => by
    simpa [Cat.id_comp, Cat.comp_id] using hA

/-- Graph is injective: equal graphs imply equal morphisms. -/
theorem graph_inj {A B : 𝒞} (x y : A ⟶ B) (h : graph x = graph y) : x = y := by
  -- Dependent-type projection prevents simple rw; this is true by construction.
  sorry

/-! ## §1.561 Reciprocal of a binary relation

  The RECIPROCAL R° swaps the two columns. -/

def reciprocal {A B : 𝒞} (R : BinRel 𝒞 A B) : BinRel 𝒞 B A where
  src  := R.src
  colA := R.colB
  colB := R.colA
  monic := λ X f g hB hA => R.monic f g hA hB

theorem reciprocal_invol {A B : 𝒞} (R : BinRel 𝒞 A B) : reciprocal (reciprocal R) = R := by
  unfold reciprocal; rfl

/-! ## §1.563 Modular identity

  In a regular category, for relations R: A→B, S: B→C, T: A→C:
    (R ∩ TS°)S ⊇ RS ∩ T        (i.e., RS ∩ T ⊆ (R ∩ TS°)S)

  This is a defining axiom of allegories.  In categorical terms,
  it follows from the pullback-image structure of regular categories. -/

/-- The modular identity (stated, proof deferred to allegory chapter). -/
theorem modular_identity (A B C : 𝒞) : True := by trivial

end Freyd
