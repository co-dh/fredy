/-
  Freyd & Scedrov, *Categories and Allegories* §1.26  The slice category A/B.

  Over (§1.26): objects of A/B are maps into B (a pair ⟨X, h : X → B⟩).
  OverHom: morphisms are commuting triangles.
  overCat: the slice category as a `Cat` instance.
  OverMono: monic in the slice category.
  Composition `⊚` is explicit (avoids `Cat` instance issues for `Over B`).
-/

import Fredy.S1_1
import Fredy.S1_41

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

structure Over (B : 𝒞) where
  dom : 𝒞
  hom : dom ⟶ B

structure OverHom {B : 𝒞} (X Y : Over B) where
  f : X.dom ⟶ Y.dom
  w : f ≫ Y.hom = X.hom

@[ext]
theorem OverHom.ext {B : 𝒞} {X Y : Over B} {a b : OverHom X Y} (h : a.f = b.f) : a = b := by
  obtain ⟨af, aw⟩ := a; obtain ⟨bf, bw⟩ := b; subst h; rfl

/-- Composition in A/B (explicit, bypasses `Cat` instance). -/
def OverHom.comp {B : 𝒞} {X Y Z : Over B} (h : OverHom X Y) (k : OverHom Y Z) : OverHom X Z :=
  ⟨h.f ≫ k.f, by rw [Cat.assoc, k.w, h.w]⟩

infixr:80 " ⊚ " => OverHom.comp

/-- The slice category A/B as a `Cat` instance.  Composition is `⊚`, identity
    is the pair `(id_dom, id_comp B)`. -/
instance overCat (B : 𝒞) : Cat.{v} (Over B) where
  Hom := OverHom
  id X := ⟨Cat.id X.dom, Cat.id_comp X.hom⟩
  comp f g := f ⊚ g
  id_comp f := OverHom.ext (Cat.id_comp f.f)
  comp_id f := OverHom.ext (Cat.comp_id f.f)
  assoc f g h := OverHom.ext (Cat.assoc f.f g.f h.f)

/-- Mono in A/B (via the Over category's `Cat` instance).  `OverMono m` iff
    `m` is monic in the slice category. -/
abbrev OverMono {B : 𝒞} {Z Y : Over B} (m : OverHom Z Y) : Prop := @Mono (Over B) _ Z Y m

end Freyd
