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

  `constructor` — split an `∧` goal into two separate subgoals.

  `dsimp`       — **definitional simplify**.  Unfolds definitions.

  `·`           — **bullet**.  Starts the proof of the next subgoal.

  `rfl`         — **reflexivity**.  Proves `x = x`.

  `by`          — enters **tactic mode** for a proof block.
-/

import Fredy.S1_1
import Fredy.S1_41


open Freyd

universe v u u₁ u₂

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-- §1.18  A functor from `𝒞` to `𝒟`.

    `F : 𝒞 → 𝒟` is the map on objects.  The class provides:
    - `map`   : for each `f : X ⟶ Y`, a morphism `map f : F X ⟶ F Y`.
    - `map_id` / `map_comp` : preservation laws.

    In the book's single-sorted language, a functor is a function `F`
    on morphisms such that `□(Fx) = F(□x)`, `(Fx)□ = F(x□)`, and
    `F(xy) = (Fx)(Fy)`.  Our object-centric definition is equivalent. -/
class Functor {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D] (F : C → D) where
  map  : {X Y : C} → (X ⟶ Y) → (F X ⟶ F Y)
  map_id : ∀ (X : C), map (Cat.id X) = Cat.id (F X)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

/-- The identity functor `1_𝒞` : every object and morphism maps to itself. -/
instance idFunctor : Functor (λ X : 𝒞 => X) where
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition `G ∘ F` of two functors as a global instance. -/
instance compFunctor {ℰ : Type _} [Cat.{v} ℰ] {F : 𝒞 → 𝒟} {G : 𝒟 → ℰ}
    [hf : Functor F] [hg : Functor G] : Functor (G ∘ F) where
  map f := hg.map (hf.map f)
  map_id X := by
    dsimp
    rw [hf.map_id, hg.map_id]
  map_comp f g := by
    rw [hf.map_comp, hg.map_comp]

/-! ## §1.181 as a general concept: preservation / reflection of a morphism-property -/

/-- A property of morphisms, uniform across all categories (e.g. `@Mono`, `@IsIso`, `@Cover`). -/
abbrev MorphProp := ∀ {𝒜 : Type u} [Cat.{v} 𝒜] {X Y : 𝒜}, (X ⟶ Y) → Prop

/-- `F` PRESERVES `P` if it carries `P`-arrows to `P`-arrows. -/
def Preserves {ℰ ℱ : Type u} [Cat.{v} ℰ] [Cat.{v} ℱ] (F : ℰ → ℱ) [hF : Functor F] (P : MorphProp.{v,u}) : Prop :=
  ∀ {X Y : ℰ} {f : X ⟶ Y}, P f → P (hF.map f)

/-- `F` REFLECTS `P` if a `P`-image forces a `P`-arrow (the shape of the §1.531 Slice Lemma). -/
def Reflects {ℰ ℱ : Type u} [Cat.{v} ℰ] [Cat.{v} ℱ] (F : ℰ → ℱ) [hF : Functor F] (P : MorphProp.{v,u}) : Prop :=
  ∀ {X Y : ℰ} {f : X ⟶ Y}, P (hF.map f) → P f

/-! ### Cross-universe preservation/reflection of `Mono`

  The generic `Preserves`/`Reflects` above take the property as a `MorphProp`
  *parameter*, which fixes one object universe — so they only apply to functors
  whose source and target live in the same universe (e.g. endofunctors).  The
  slice forgetful functor `Σ : A/B → A` is genuinely cross-universe
  (`Over B : Type (max u v)` vs `A : Type u`), so we give `Mono`-specific
  versions: because `Mono` is applied *directly* (not through a parameter) and is
  itself universe-polymorphic, these work for `Functor`s between categories in
  different universes. -/

/-- `F` PRESERVES monos: it carries monos to monos. -/
def PreservesMono {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D]
    (F : C → D) [hF : Functor F] : Prop :=
  ∀ {X Y : C} {f : X ⟶ Y}, Mono f → Mono (hF.map f)

/-- `F` REFLECTS monos: a mono image forces a mono. -/
def ReflectsMono {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D]
    (F : C → D) [hF : Functor F] : Prop :=
  ∀ {X Y : C} {f : X ⟶ Y}, Mono (hF.map f) → Mono f

/-- A morphism has a right inverse: there exists `g` such that `f ≫ g = id`. -/
def HasRightInv : MorphProp.{v,u} := λ {_} _ {X Y} f => ∃ (g : Y ⟶ X), f ≫ g = Cat.id X

/-- A morphism has a left inverse: there exists `g` such that `g ≫ f = id`. -/
def HasLeftInv : MorphProp.{v,u} := λ {_} _ {X Y} f => ∃ (g : Y ⟶ X), g ≫ f = Cat.id Y

/-- **§1.181 restated**: every functor preserves isomorphisms.  This is the one
    morphism-property preserved by *all* functors; preservation of `@Mono`, `@Cover`, … are
    separate statements that need hypotheses on `F`. -/
theorem preserves_iso (F : 𝒞 → 𝒟) [hF : Functor F] : Preserves F @IsIso := by
  intro X Y f hf
  obtain ⟨g, hfg, hgf⟩ := hf
  exact ⟨hF.map g,
    by rw [← hF.map_comp, hfg, hF.map_id],
    by rw [← hF.map_comp, hgf, hF.map_id]⟩

/-- **§1.181**: every functor preserves right-invertibility. -/
theorem preserves_has_right_inv (F : 𝒞 → 𝒟) [hF : Functor F] : Preserves F HasRightInv := by
  intro X Y f ⟨g, hfg⟩
  exact ⟨hF.map g, by rw [← hF.map_comp, hfg, hF.map_id]⟩

/-- **§1.181**: every functor preserves left-invertibility. -/
theorem preserves_has_left_inv (F : 𝒞 → 𝒟) [hF : Functor F] : Preserves F HasLeftInv := by
  intro X Y f ⟨g, hgf⟩
  exact ⟨hF.map g, by rw [← hF.map_comp, hgf, hF.map_id]⟩

section FunctorProperties
-- The theorems below all share the same functor `F` and its instance `h`;
-- declaring them once as section variables avoids repeating them.
variable {F : 𝒞 → 𝒟} [h : Functor F]

/-- **§1.181**: a functor preserves isomorphisms.

    If `f : X → Y` has a two-sided inverse in `𝒞`, then `F.map f`
    has a two-sided inverse in `𝒟`.  This is an instance of the
    general `Preserves` notion — every functor `Preserves` `@IsIso`. -/
theorem functor_preserves_iso {X Y : 𝒞} (f : X ⟶ Y) (hf : IsIso f) :
    IsIso (h.map f) :=
  preserves_iso F hf

/-- **§1.181**: the image of the inverse is an inverse of the image.

    If `g` is a specific two-sided inverse of `f` (so `f ≫ g = id_X`
    and `g ≫ f = id_Y`), then `F.map g` is a two-sided inverse of
    `F.map f`.  Returns both equations as a pair (`∧`). -/
theorem functor_map_inv {X Y : 𝒞} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : f ≫ g = Cat.id X) (hgf : g ≫ f = Cat.id Y) :
    h.map f ≫ h.map g = Cat.id (F X) ∧
    h.map g ≫ h.map f = Cat.id (F Y) := by
  constructor
  · rw [← h.map_comp, hfg, h.map_id]
  · rw [← h.map_comp, hgf, h.map_id]

end FunctorProperties
