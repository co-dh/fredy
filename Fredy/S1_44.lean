/-
  Freyd & Scedrov, *Categories and Allegories* §1.44  The slice category A/B.

  Over (§1.26): objects of A/B are maps into B.
  OverHom: morphisms are commuting triangles.  OverMono: monic in A/B.
  Composition `⊚` is explicit (avoids `Cat` instance issues for `Over B`).
-/

import Fredy.S1_1

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

structure Over (B : 𝒞) where
  dom : 𝒞
  hom : dom ⟶ B

structure OverHom {B : 𝒞} (X Y : Over B) where
  f : X.dom ⟶ Y.dom
  w : f ≫ Y.hom = X.hom

theorem OverHom.ext {B : 𝒞} {X Y : Over B} {a b : OverHom X Y} (h : a.f = b.f) : a = b := by
  obtain ⟨af, aw⟩ := a; obtain ⟨bf, bw⟩ := b; subst h; rfl

/-- Composition in A/B (explicit, bypasses `Cat` instance). -/
def OverHom.comp {B : 𝒞} {X Y Z : Over B} (h : OverHom X Y) (k : OverHom Y Z) : OverHom X Z :=
  ⟨h.f ≫ k.f, by rw [Cat.assoc, k.w, h.w]⟩

infixr:80 " ⊚ " => OverHom.comp

/-- Mono in A/B (explicit, bypasses `Cat` instance for `Over B`). -/
def OverMono {B : 𝒞} {Z Y : Over B} (m : OverHom Z Y) : Prop :=
  ∀ {W : Over B} (g h : OverHom W Z), g ⊚ m = h ⊚ m → g = h
