/-
  Freyd & Scedrov, *Categories and Allegories* §1.1  Basic definitions.

  Mathlib migration spike: categories, typed homs, identities, composition,
  and their laws now come from `CategoryTheory.Category`.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso

open CategoryTheory

universe v u

/-- Transitional spelling for files not yet migrated.  This is an abbreviation for
Mathlib's category class, not a second category structure. -/
abbrev Cat.{w, z} (C : Type z) := CategoryTheory.Category.{w, z} C

namespace Cat

abbrev Hom {C : Type u} [CategoryTheory.Category.{v} C] := @Quiver.Hom C inferInstance
abbrev id {C : Type u} [CategoryTheory.Category.{v} C] (X : C) : X ⟶ X := 𝟙 X
abbrev comp {C : Type u} [CategoryTheory.Category.{v} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z := f ≫ g

theorem id_comp {C : Type u} [CategoryTheory.Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    id X ≫ f = f := CategoryTheory.Category.id_comp f

theorem comp_id {C : Type u} [CategoryTheory.Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    f ≫ id Y = f := CategoryTheory.Category.comp_id f

theorem assoc {C : Type u} [CategoryTheory.Category.{v} C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : (f ≫ g) ≫ h = f ≫ g ≫ h :=
  CategoryTheory.Category.assoc f g h

end Cat

namespace Freyd

/- Mathlib already provides the book-compatible notation
     `X ⟶ Y`, `𝟙 X`, and diagram-order composition `f ≫ g`.
-/

end Freyd
