/-
  Freyd & Scedrov, *Categories and Allegories* §1.26  The slice category A/B
  and §1.263 the coslice category B\A.

  Mathlib migration spike: `Over`, `Under`, their morphisms, composition,
  category laws, and forgetful functors are supplied by Mathlib.
-/

import Fredy.S1_1
import Fredy.S1_41
import Mathlib.CategoryTheory.Comma.Over.Basic

open CategoryTheory

universe v u

namespace Freyd

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- The book's slice `𝒞/B`. -/
abbrev Over (B : 𝒞) := CategoryTheory.Over B

/-- Transitional explicit category witness for code that passes slice categories
as ordinary arguments. -/
def overCat (B : 𝒞) : Cat.{v} (Over B) := inferInstance

/-- Morphisms in `𝒞/B`; Mathlib stores their underlying arrow in `.left`. -/
abbrev OverHom {B : 𝒞} (X Y : Over B) := X ⟶ Y

/-- Diagram-order composition in the slice. -/
def OverHom.comp {B : 𝒞} {X Y Z : Over B} (f : OverHom X Y) (g : OverHom Y Z) :
    OverHom X Z := f ≫ g

infixr:80 (name := overHomComp) " ⊚ " => OverHom.comp

abbrev OverMono {B : 𝒞} {X Y : Over B} (m : OverHom X Y) : Prop := Monic m
abbrev OverIso {B : 𝒞} {X Y : Over B} (m : OverHom X Y) : Prop := IsIso m

/-- Isomorphism in the slice means existence of an inverse slice morphism. -/
theorem overIso_iff {B : 𝒞} {X Y : Over B} (m : OverHom X Y) :
    OverIso m ↔ ∃ inv : OverHom Y X, m ⊚ inv = 𝟙 X ∧ inv ⊚ m = 𝟙 Y := by
  rfl

/-- A slice isomorphism has an isomorphic underlying arrow. -/
theorem overIso_underlying {B : 𝒞} {X Y : Over B} {m : OverHom X Y} (hm : OverIso m) :
    IsIso m.left := by
  obtain ⟨inv, h₁, h₂⟩ := hm
  exact ⟨inv.left, congrArg CommaMorphism.left h₁, congrArg CommaMorphism.left h₂⟩

/-- An isomorphic underlying arrow gives an isomorphism in the slice. -/
theorem overIso_of_underlying {B : 𝒞} {X Y : Over B} (m : OverHom X Y)
    (hf : IsIso m.left) : OverIso m := by
  obtain ⟨inv_f, h₁, h₂⟩ := hf
  have inv_w : inv_f ≫ X.hom = Y.hom := by
    calc
      inv_f ≫ X.hom = inv_f ≫ (m.left ≫ Y.hom) :=
        congrArg (inv_f ≫ ·) (CategoryTheory.Over.w m).symm
      _ = (inv_f ≫ m.left) ≫ Y.hom := (Category.assoc _ _ _).symm
      _ = Y.hom := by rw [h₂, Category.id_comp]
  let inv : OverHom Y X := CategoryTheory.Over.homMk inv_f inv_w
  exact ⟨inv,
    CategoryTheory.Over.OverMorphism.ext h₁,
    CategoryTheory.Over.OverMorphism.ext h₂⟩

/-! ## §1.263 Counter-slice -/

abbrev Under (B : 𝒞) := CategoryTheory.Under B
abbrev UnderHom {B : 𝒞} (X Y : Under B) := X ⟶ Y

def UnderHom.comp {B : 𝒞} {X Y Z : Under B} (f : UnderHom X Y) (g : UnderHom Y Z) :
    UnderHom X Z := f ≫ g

infixr:80 (name := underHomComp) " ⊛ " => UnderHom.comp

abbrev UnderMono {B : 𝒞} {X Y : Under B} (m : UnderHom X Y) : Prop := Monic m

end Freyd
