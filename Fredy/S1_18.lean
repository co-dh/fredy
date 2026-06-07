/-
  Freyd & Scedrov, *Categories and Allegories* §1.18  Functors, §1.181.

  §1.18  A functor F : A → B preserves source, target, and composition.
         In object-centric form: object map + morphism map preserving id/comp.
  §1.181 Any functor preserves left- and right-invertibility.
         Moreover, the image of an inverse is an inverse of the image.

  ---
  ## Lean tactics used in this file (for readers unfamiliar with Lean)

  `rw [h]`      — **rewrite**.  Replace the goal (or a hypothesis) using the
                  equality `h`.  `rw` searches for the left side of `h` in the
                  goal and replaces it with the right side.  `← h` rewrites
                  the other direction (right side → left side).

  `refine ⟨x, h₁, h₂⟩` — provide the components of an `∃` or `∧` goal one
                  by one.  `⟨a, b⟩` is syntax for a tuple; `?` marks a subgoal
                  to be proved in a later bullet `·`.

  `obtain ⟨g, hfg, hgf⟩ := hf` — **case split**.  If `hf : IsIso f` (i.e.
                  `∃ g, f ≫ g = id ∧ g ≫ f = id`), this names the witness
                  `g` and the two proofs `hfg`, `hgf`.

  `constructor` — split an `∧` goal into two separate subgoals (left and
                  right conjunct).

  `dsimp`       — **definitional simplify**.  Unfolds definitions that are
                  true by computation, such as `(G ∘ F) X = G (F X)`.

  `·`           — **bullet**.  Starts the proof of the next subgoal (created
                  by `refine ?_` or `constructor`).

  `rfl`         — **reflexivity**.  Proves `x = x` or any goal that is true
                  by definition.

  `by`          — enters **tactic mode** for a proof block.

  `apply`       — match the goal against the conclusion of a lemma, turning
                  the lemma's hypotheses into new subgoals.

  `exact`       — provide a term that exactly matches the goal.
-/

import Fredy.S1_1
import Fredy.S1_41

set_option linter.unusedSectionVars false

open Freyd

universe v u w

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type w} [Cat.{v} 𝒟]

namespace Freyd

/-- §1.18  A functor from `𝒞` to `𝒟`.

    `F : 𝒞 → 𝒟` is the map on objects.  The class provides:
    - `map`   : for each `f : X ⟶ Y`, a morphism `map f : F X ⟶ F Y`.
    - `map_id` / `map_comp` : preservation laws.

    In the book's single-sorted language, a functor is a function `F`
    on morphisms such that `□(Fx) = F(□x)`, `(Fx)□ = F(x□)`, and
    `F(xy) = (Fx)(Fy)`.  Our object-centric definition is equivalent. -/
class Functor (F : 𝒞 → 𝒟) where
  map  : {X Y : 𝒞} → (X ⟶ Y) → (F X ⟶ F Y)
  map_id : ∀ (X : 𝒞), map (Cat.id X) = Cat.id (F X)
  map_comp : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

/-- The identity functor `1_𝒞` : every object and morphism maps to itself. -/
def idFunctor : Functor (λ X : 𝒞 => X) where
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition `G ∘ F` of two functors (explicit, not a global typeclass
    instance to avoid looping).  `hf` and `hg` are named so that we can
    write `hf.map` / `hg.map` instead of the more verbose `Functor.map`. -/
def compFunctor {ℰ : Type _} [Cat.{v} ℰ] {F : 𝒞 → 𝒟} {G : 𝒟 → ℰ}
    [hf : Functor F] [hg : Functor G] : Functor (G ∘ F) where
  map f := hg.map (hf.map f)
  -- `(G ∘ F) X` is `G (F X)`.  `dsimp` makes this reduction visible,
  -- then `rw` applies the two `map_id` laws.
  map_id X := by
    dsimp
    rw [hf.map_id, hg.map_id]
  map_comp f g := by
    rw [hf.map_comp, hg.map_comp]

section FunctorProperties
-- The following lemmas all share the same functor `F`; declaring it (and
-- its instance `h`) once as section variables avoids repeating them
-- on every theorem.
variable {F : 𝒞 → 𝒟} [h : Functor F]

/-- **§1.181 (left-invertible)**.  If `f` has a left inverse `g` (meaning
    `g ≫ f = id_Y` — the book calls this "left-invertible" because `g`
    appears on the left in the composition `gf`), then `F.map f` also
    has a left inverse, namely `F.map g`.

    Proof: `F.map g ≫ F.map f = F.map (g ≫ f) = F.map id_Y = id_{F Y}`. -/
theorem functor_preserves_left_inv {X Y : 𝒞} (f : X ⟶ Y) (g : Y ⟶ X)
    (h_eq : g ≫ f = Cat.id Y) : h.map g ≫ h.map f = Cat.id (F Y) := by
  rw [← h.map_comp, h_eq, h.map_id]

/-- **§1.181 (right-invertible)**.  If `f` has a right inverse `g` (meaning
    `f ≫ g = id_X` — the book calls this "right-invertible" because `g`
    appears on the right in `fg`), then `F.map f` also has a right inverse.

    Proof: `F.map f ≫ F.map g = F.map (f ≫ g) = F.map id_X = id_{F X}`. -/
theorem functor_preserves_right_inv {X Y : 𝒞} (f : X ⟶ Y) (g : Y ⟶ X)
    (h_eq : f ≫ g = Cat.id X) : h.map f ≫ h.map g = Cat.id (F X) := by
  rw [← h.map_comp, h_eq, h.map_id]

/-- **§1.181**: a functor preserves isomorphisms.

    If `f : X → Y` has a two-sided inverse `g : Y → X` in `𝒞`, then
    `F.map f` has a two-sided inverse `F.map g` in `𝒟`.  This follows
    immediately from `functor_preserves_left_inv` and
    `functor_preserves_right_inv`: the right inverse gives the first
    equation, the left inverse gives the second. -/
theorem functor_preserves_iso {X Y : 𝒞} (f : X ⟶ Y) (hf : IsIso f) :
    IsIso (h.map f) := by
  -- `hf : IsIso f` is `∃ g, f ≫ g = id_X ∧ g ≫ f = id_Y`
  obtain ⟨g, hfg, hgf⟩ := hf
  -- `hfg : f ≫ g = id_X` is the right-inverse condition,
  -- `hgf : g ≫ f = id_Y` is the left-inverse condition.
  -- Apply the two lemmas to get the equations we need, then package
  -- them into an `IsIso` proof with witness `h.map g`.
  have h_right : h.map f ≫ h.map g = Cat.id (F X) :=
    functor_preserves_right_inv f g hfg
  have h_left : h.map g ≫ h.map f = Cat.id (F Y) :=
    functor_preserves_left_inv f g hgf
  exact ⟨h.map g, h_right, h_left⟩

/-- **§1.181**: the image of the inverse is an inverse of the image.

    If `g` is a specific two-sided inverse of `f` (so `f ≫ g = id_X`
    and `g ≫ f = id_Y`), then `F.map g` is a two-sided inverse of
    `F.map f`.  Returns both equations as a pair (`∧`). -/
theorem functor_map_inv {X Y : 𝒞} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : f ≫ g = Cat.id X) (hgf : g ≫ f = Cat.id Y) :
    h.map f ≫ h.map g = Cat.id (F X) ∧
    h.map g ≫ h.map f = Cat.id (F Y) := by
  constructor
  · exact functor_preserves_right_inv f g hfg
  · exact functor_preserves_left_inv f g hgf

end FunctorProperties
