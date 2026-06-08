/-
  Freyd & Scedrov, *Categories and Allegories* §1.412
  Table terminology: TABLE, TOP, FEET, COLUMN, RELATION,
  SUBOBJECT, VALUE, SUBTERMINATOR (§1.412).
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_49

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-- A TABLE ⟨T; x₁,…,xₙ⟩ with COLUMNS xᵢ: T → Aᵢ.  Uses S1_49's Table. -/
abbrev Table := Table 𝒞

/-- The TOP of a table: the common source object. -/
def Table.top (tab : Table) : 𝒞 := tab.src

/-- A COLUMN of a table: the i-th morphism from top to foot. -/
def Table.column (tab : Table) (i : Fin tab.len) : tab.src ⟶ tab.codom i := tab.col i

/-- The FEET of a table: the sequence of target objects. -/
def Table.feet (tab : Table) : Fin tab.len → 𝒞 := tab.codom

/-- A RELATION on a sequence of feet A₁,…,Aₙ is an isomorphism class
    of tables (§1.412).  For n=2 we use BinRel directly. -/
def Relation (feet : Fin 2 → 𝒞) : Type (max u v) :=
  -- Represented by a table; isomorphism handled by RelHom in S1_56
  Table

/-- A SUBOBJECT of B is a relation with n=1 (single foot B) (§1.412).
    Represented by a monomorphism into B.  (Also in S1_51: Subobject 𝒞 B.) -/

/-- A VALUE is a relation with n=0 (no columns), i.e., an isomorphism
    class of subterminators (§1.412).  Represented by a subterminator. -/
def Value : Type (max u v) := Σ (V : 𝒞), Subterminator V

/-- SUBTERMINATOR: an object V such that V→1 is monic (§1.412). -/
def Subterminator (V : 𝒞) : Prop := Mono (term V)

/-- MONIC FAMILY: a family {xᵢ: T→Aᵢ} jointly left-cancellable (§1.41). -/
def MonicFamily {T : 𝒞} {I : Type} (feet : I → 𝒞) (cols : (i : I) → T ⟶ feet i) : Prop :=
  ∀ {X : 𝒞} (f g : X ⟶ T), (∀ i, f ≫ cols i = g ≫ cols i) → f = g

end Freyd
