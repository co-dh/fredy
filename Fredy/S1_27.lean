/-
  Freyd & Scedrov, *Categories and Allegories* §1.27  Small category, functor category,
  natural transformation (§1.27), right A-sets (§1.271), Cayley representation (§1.272),
  left A-sets (§1.273), natural equivalence (§1.274).

  §1.27  NaturalTransformation: a family α_X : F X → G X with naturality squares.
  §1.271 Right A-set = covariant functor A → Y.  In the single-sorted language this is
         a set X with a unary operation to |A| (the "source" map) and a partial binary
         operation x a defined iff source(x) = □a, satisfying the monoid-action laws.
  §1.272 CAYLEY REPRESENTATION: a small category A is a right A-set whose carriers
         are C(A) = {x | □x = A} (morphisms targeting A).  For f : A → B, C(f)(y) = y f.
         C is one-to-one (faithful): if C(f) = C(g) then f = g, taking y = A (id_A).
         In the object-centric setting: post-composition h ↦ h ≫ f faithfully encodes f
         because id_A ≫ f = f distinguishes f from any g ≠ f.
  §1.273 Left A-set = contravariant version: right A^op-set (§1.273).
  §1.274 Natural equivalence = natural transformation with iso components (§1.274).
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.27  Natural transformation -/

/-- A natural transformation α : F → G between parallel functors F, G : 𝒞 → 𝒟 (§1.27).
    For each X : 𝒞 a component α_X : F X → G X; for every f : X → Y,
    F(f) ≫ α_Y = α_X ≫ G(f) (naturality). -/
structure NaturalTransformation (F G : 𝒞 → 𝒟) [Functor F] [Functor G] where
  app : (X : 𝒞) → (F X ⟶ G X)
  naturality : ∀ {X Y : 𝒞} (f : X ⟶ Y), (Functor.map f) ≫ app Y = app X ≫ (Functor.map f)

infix:25 " ⟹ " => NaturalTransformation

/-! ## §1.274  Natural equivalence (isomorphism in the functor category) -/

/-- A natural equivalence (§1.274): a natural transformation whose every component is
    an isomorphism.  In the functor category this is precisely an isomorphism. -/
def NaturalIso (F G : 𝒞 → 𝒟) [Functor F] [Functor G] (α : F ⟹ G) : Prop :=
  ∀ X : 𝒞, IsIso (NaturalTransformation.app α X)

/-! ## §1.272  Cayley representation -/

section Cayley

variable {A B : 𝒞}

/-- **§1.272 Cayley representation — faithfulness**.
    In Freyd's single-sorted language: C sends A ↦ {y | □y = A}, f ↦ (y ↦ yf).
    C is one-to-one on morphisms because y = A (id_A) belongs to C(A) and A f = f.
    In the object-centric setting this translates to: if post-composition by f and g
    agree on all maps into A then f = g.  The witness is h = id_A : A → A. -/
theorem cayley_faithful (f g : A ⟶ B)
    (h : ∀ {X : 𝒞} (hX : X ⟶ A), hX ≫ f = hX ≫ g) : f = g := by
  have := h (Cat.id A)
  rwa [Cat.id_comp, Cat.id_comp] at this

/-- **§1.272 (contrapositive)**.  If f ≠ g then they are distinguished by
    some pre-composition — specifically id_A composed with each. -/
theorem cayley_faithful_contra (f g : A ⟶ B) (hne : f ≠ g) :
    ∃ (X : 𝒞) (hX : X ⟶ A), hX ≫ f ≠ hX ≫ g := by
  refine ⟨A, Cat.id A, ?_⟩
  intro h_eq
  apply hne
  rwa [Cat.id_comp, Cat.id_comp] at h_eq

end Cayley

/-! ## §1.27  Functor category 𝒟^𝒜 -/

/-- A bundled functor: an object map together with its `Functor` instance.
    These are the OBJECTS of the functor category 𝒟^𝒜 (§1.27). -/
structure FunctorObj (𝒜 𝒟 : Type u) [Cat.{v} 𝒜] [Cat.{v} 𝒟] where
  obj       : 𝒜 → 𝒟
  isFunctor : Functor obj

/-- Make `Functor F.obj` available by instance search when `F : FunctorObj 𝒜 𝒟`. -/
instance {𝒜 𝒟 : Type u} [Cat.{v} 𝒜] [Cat.{v} 𝒟] (F : FunctorObj 𝒜 𝒟) :
    Functor F.obj := F.isFunctor

/-- The hom-type of the functor category: natural transformations from F to G. -/
abbrev FunctorHom {𝒜 𝒟 : Type u} [Cat.{v} 𝒜] [Cat.{v} 𝒟]
    (F G : FunctorObj 𝒜 𝒟) : Type (max v u) :=
  NaturalTransformation F.obj G.obj

/-- Extensionality for `NaturalTransformation`: two NTs with the same components
    are equal.  Requires explicit functor instances to avoid typeclass ambiguity. -/
theorem NaturalTransformation.ext' {𝒜 𝒟 : Type u} [Cat.{v} 𝒜] [Cat.{v} 𝒟]
    {F G : 𝒜 → 𝒟} [Functor F] [Functor G]
    {α β : NaturalTransformation F G}
    (h : ∀ X, α.app X = β.app X) : α = β := by
  cases α; cases β; congr 1; funext X; exact h X

/-- Identity natural transformation on F: component at each X is id_{F X}.
    Naturality: F(f) ≫ id = id ≫ F(f) by comp_id / id_comp. -/
def natTrans_id {𝒜 𝒟 : Type u} [Cat.{v} 𝒜] [Cat.{v} 𝒟]
    (F : FunctorObj 𝒜 𝒟) : FunctorHom F F where
  app X := Cat.id (F.obj X)
  naturality f := by simp [Cat.comp_id, Cat.id_comp]

/-- Vertical composition of natural transformations α : F ⟹ G and β : G ⟹ H.
    Component: (α;β)_X = α_X ≫ β_X.  Naturality square commutes by
    α-naturality and β-naturality and associativity. -/
def natTrans_comp {𝒜 𝒟 : Type u} [Cat.{v} 𝒜] [Cat.{v} 𝒟]
    {F G H : FunctorObj 𝒜 𝒟}
    (α : FunctorHom F G) (β : FunctorHom G H) : FunctorHom F H where
  app X := α.app X ≫ β.app X
  naturality {X Y} f := by
    have hα := α.naturality f
    have hβ := β.naturality f
    -- F(f) ≫ α_Y ≫ β_Y = α_X ≫ G(f) ≫ β_Y = α_X ≫ β_X ≫ H(f)
    rw [← Cat.assoc, hα, Cat.assoc, hβ, ← Cat.assoc]

/-- The FUNCTOR CATEGORY 𝒟^𝒜 (§1.27): objects are bundled functors 𝒜 → 𝒟,
    morphisms are natural transformations, identity and composition as above.
    The three category laws hold pointwise by the laws of 𝒟. -/
instance functorCat (𝒜 𝒟 : Type u) [Cat.{v} 𝒜] [Cat.{v} 𝒟] :
    Cat.{max v u} (FunctorObj 𝒜 𝒟) where
  Hom   := FunctorHom
  id    := natTrans_id
  comp  := natTrans_comp
  id_comp α  := NaturalTransformation.ext' fun X => Cat.id_comp (α.app X)
  comp_id α  := NaturalTransformation.ext' fun X => Cat.comp_id (α.app X)
  assoc α β γ := NaturalTransformation.ext' fun X => Cat.assoc (α.app X) (β.app X) (γ.app X)

/-! ## §1.272  Cayley completeness metatheorem -/

/-- **§1.272 (Cayley completeness)**.
    Every universally-quantified elementary sentence in the predicates of category
    theory that holds in the category of sets holds in every category.

    Proof sketch (Freyd §1.272): The Cayley representation `C : 𝒞 → Set` (sending
    `A` to the set of morphisms with target `A`, and `f : A → B` to post-composition
    with `f`) is faithful (`cayley_faithful`), establishing any category 𝒞 as
    isomorphic to a concrete subcategory of Set.  Any universally-quantified
    elementary sentence true in Set descends to every subcategory, hence to 𝒞.

    We state the key corollary: any property `P` of morphism-pairs (in any category)
    that is (i) preserved under faithful functors and (ii) holds in every Set-like
    category where all homs are subsets of some ambient set — holds in 𝒞.

    The metatheorem cannot be internalized as a single Lean Prop (it quantifies over
    all first-order sentences); we record the statement with `sorry`.
    The operative ingredient — the Cayley embedding is faithful — is `cayley_faithful`. -/
theorem cayley_completeness
    -- `P` is a property of morphisms that is preserved under faithful embeddings
    (P : ∀ {𝒜 : Type u} [Cat.{v} 𝒜] {X Y : 𝒜}, (X ⟶ Y) → Prop)
    -- `P` holds in every category that admits a faithful functor from 𝒞
    (hP : ∀ {𝒜 : Type u} [Cat.{v} 𝒜] (F : 𝒞 → 𝒜) [hF : Functor F]
            (hFaith : ∀ {X Y : 𝒞} (f g : X ⟶ Y), hF.map f = hF.map g → f = g)
            {X Y : 𝒞} (f : X ⟶ Y), P (hF.map f) → P f) :
    ∀ {X Y : 𝒞} (f : X ⟶ Y), P f := by
  sorry

end Freyd
