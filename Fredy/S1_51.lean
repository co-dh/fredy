/-
  Freyd & Scedrov, *Categories and Allegories* §1.51  Covers, regular categories.

  Cover (§1.512): a morphism whose image is entire (every monic
  it factors through is iso).  monic_cover_iso: monic + cover ⇒ iso.
-/

import Fredy.S1_1
import Fredy.S1_41

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

def Cover {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∀ {C : 𝒞} (m : C ⟶ Y) (g : X ⟶ C), Mono m → g ≫ m = f → IsIso m

theorem monic_cover_iso {X Y : 𝒞} (f : X ⟶ Y) (hc : Cover f) (hm : Mono f) : IsIso f :=
  hc f (Cat.id X) hm (Cat.id_comp f)
