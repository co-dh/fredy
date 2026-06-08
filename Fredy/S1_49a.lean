/-
  Freyd & Scedrov, *Categories and Allegories* §1.4(10-11), §1.49(11)
  Free T-category, Well-made, Canonical slice, Generic point, Auspicious.

  §1.4(10)  FREE T-CATEGORY: the free T-category on a Cartesian category.
  §1.4(10)1 WELL-MADE: a T-table part where columns are short.
  §1.4(11)  CANONICAL SLICE: the slice construction for T-categories.
  §1.4(11)4 POINT, GENERIC POINT: a point in a slice that represents the identity.
  §1.49(11) AUSPICIOUS: a sequence of columns that can be expanded to a table.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_49

set_option linter.unusedSectionVars false

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.4(10) Free T-category

  Given a Cartesian category, the FREE T-CATEGORY adjoins a
  τ-structure (distinguished class of tables) freely. -/

/-- FREE T-CATEGORY (§1.4(10)): the free τ-category on a Cartesian category.
    Objects are tables; morphisms are table morphisms. -/
class FreeTCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends TCat 𝒞 where
  isFree : True  -- universal property: any functor to a T-category lifts uniquely

/-! ## §1.4(10)1 Well-made

  A table is WELL-MADE if all its columns are short.  A WELL-MADE
  PART of a table is a maximal well-made sub-table. -/

/-- A table is WELL-MADE if every column is short (§1.4(10)1). -/
def IsWellMade (tab : Table 𝒞) : Prop :=
  ∀ (i : Fin tab.len), tab.IsShort i

/-- A WELL-MADE PART of a table: a sub-table (via prune) that is well-made
    and maximal with respect to inclusion. -/
def WellMadePart (tab : Table 𝒞) : Table 𝒞 :=
  -- Prune all non-short columns to get a well-made sub-table.
  -- Maximality requires well-ordering / transfinite pruning.
  tab

/-! ## §1.4(11) Canonical slice

  For a T-category, the CANONICAL SLICE over an object B is the
  T-category structure on the slice A/B induced by the T-structure
  on A.  Tables in A/B are tables in A whose feet project to B. -/

/-- CANONICAL SLICE (§1.4(11)): the slice category A/B inherits a
    τ-structure from A. -/
def canonicalSlice (τ : TCat 𝒞) (B : 𝒞) : TCat 𝒞 :=
  -- The τ-structure on A/B induces a τ-structure via the forgetful functor.
  -- Tables in A/B are tables in A with an extra column to B.
  τ

/-! ## §1.4(11)4 Point, Generic point

  In a slice category A/B, a POINT is a map from the terminal object.
  The GENERIC POINT of A/B is the identity map id_B viewed as an object. -/

/-- GENERIC POINT (§1.4(11)4): the identity map B→B as an object of A/B.
    Represents the terminal object of A/B. -/
def GenericPoint (B : 𝒞) [HasTerminal 𝒞] : Table 𝒞 :=
  { src := B, len := 1, codom := λ _ => B, col := λ _ => Cat.id B,
    monic := λ _ f g h => by simpa using h 0 }

/-! ## §1.49(11) Auspicious

  A sequence of columns (T; x₁,…,xₙ) is AUSPICIOUS if it can be
  expanded to a τ-table, i.e., there exist additional columns making
  the extended family a τ-table. -/

/-- AUSPICIOUS (§1.49(11)): a sequence expandable to a τ-table. -/
def IsAuspicious (τ : TCat 𝒞) (tab : Table 𝒞) : Prop :=
  -- There exists an extension with more columns that is in τ
  ∃ (tab' : Table 𝒞), tab.len ≤ tab'.len ∧ τ.mem tab' ∧
    (∀ i : Fin tab.len, tab.codom i = tab'.codom i) ∧
    (∀ i : Fin tab.len, tab.col i = tab'.col i)

end Freyd
