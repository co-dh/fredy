/-
  Freyd & Scedrov, *Categories and Allegories* §1.35, §1.243
  Forgetful functor, founded category, concrete category, underlying set functor.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31
import Fredy.S1_55


open Freyd

universe v u u₂ v₂ w

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
instance {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] (U : ForgetfulFunctor 𝒜 ℬ) : Functor U.obj where
  map := U.map
  map_id := U.map_id
  map_comp := U.map_comp

/-! ## §1.243 Founded categories and concrete categories

  §1.243: A category A is FOUNDED on B when it is constructed from B by
  - specifying a class of objects equipped with an underlying-object map `|·| : 𝒜 → ℬ`,
  - taking B's morphisms as proto-morphisms with a source-target predicate, and
  - verifying identities and composition close.
  The functor U : A → B (A ↦ |A|, f ↦ f) is always faithful.

  A CONCRETE CATEGORY is one founded on 𝒴 (the category of Sets §1.241).
  The forgetful functor in the concrete case is called the UNDERLYING SET FUNCTOR. -/

/-- §1.243  A is FOUNDED on B: a faithful functor `𝒜 → ℬ` witnesses the foundation.
    `obj` is the underlying-object map `|·| : 𝒜 → ℬ`; `faithful` is injectivity on homs. -/
structure Founded (𝒜 : Type u) (ℬ : Type u₂) [Cat.{v} 𝒜] [Cat.{v₂} ℬ] where
  obj      : 𝒜 → ℬ
  map      : {X Y : 𝒜} → (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id   : ∀ X : 𝒜, map (Cat.id X) = Cat.id (obj X)
  map_comp : ∀ {X Y Z : 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g
  faithful : ∀ {X Y : 𝒜} (f g : X ⟶ Y), map f = map g → f = g

/-- §1.243  A CONCRETE CATEGORY: a category 𝒜 founded on 𝒴 = Sets.
    `w` is the universe of underlying sets; hom-sets are functions (universe `w`). -/
def ConcreteCat (𝒜 : Type u) [Cat.{v} 𝒜] : Type _ :=
  Founded 𝒜 (Type w)

/-- §1.35 / §1.243  The UNDERLYING SET FUNCTOR of a concrete category.
    Sends A ∈ 𝒜 to its underlying set |A| ∈ Sets and each morphism to itself. -/
def underlyingSetFunctor {𝒜 : Type u} [Cat.{v} 𝒜]
    (C : ConcreteCat 𝒜) : Founded 𝒜 (Type w) := C

end Freyd
