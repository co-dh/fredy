/-
  Freyd & Scedrov, *Categories and Allegories* §1.35
  Forgetful functor, grounding, foundation functor.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.35 Forgetful functor

  If A is founded on B (§1.243), the FORGETFUL FUNCTOR U : A → B
  sends objects A ∈ A to |A| ∈ B and morphisms A → B in A to x in B.
  U is always an embedding. -/

/-- The forgetful functor.  Takes an object mapping `|·| : 𝒜 → ℬ` and a morphism
    mapping that forgets structure.  Always an embedding.  (The book's "forgetful
    functor" is defined by a foundation; we capture the general property.) -/
structure ForgetfulFunctor (𝒜 : Type u) (ℬ : Type u) [Cat.{v} 𝒜] [Cat.{v} ℬ] where
  obj    : 𝒜 → ℬ
  map    : {X Y : 𝒜} → (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id : ∀ X : 𝒜, map (Cat.id X) = Cat.id (obj X)
  map_comp : ∀ {X Y Z : 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g
  isEmbedding : ∀ {X Y : 𝒜} (f g : X ⟶ Y), map f = map g → f = g

/-- The forgetful functor yields a `Functor` (as defined in §1.18). -/
instance (U : ForgetfulFunctor 𝒜 ℬ) : Functor U.obj where
  map := U.map
  map_id := U.map_id
  map_comp := U.map_comp

end Freyd
