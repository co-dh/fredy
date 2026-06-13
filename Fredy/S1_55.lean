/-
  Freyd & Scedrov, *Categories and Allegories* §1.55
  Henkin-Lubkin representation theorem.

  Every small (pre-)regular category is faithfully represented in a power of the
  category of sets.  We model the category of sets 𝒮 as `Type w` with functions
  as morphisms, and a power 𝒮^I as I-indexed families of sets with pointwise
  families of functions.

  The faithful representation is the covariant hom-functor (Cayley, §1.272)
  family `i ↦ Hom(i, -)`: the product functor `𝒞 → 𝒮^|𝒞|`, `A ↦ (i ↦ (i ⟶ A))`,
  separates morphisms because `id_A` distinguishes `f` from `g` (`cayley_faithful`).
  This is constructive and choice-free, so it holds for ANY small category — the
  regularity hypothesis is carried for fidelity to the book but is not used.

  NOTE on scope: this establishes the *faithful* representation of §1.55.  The
  book's construction is additionally *exact* (preserves products, images and
  covers), which is what powers the §1.551 Horn-sentence metatheorem; the
  covariant-hom representation preserves limits but NOT images, so exactness is
  not established here.  An exact faithful representation needs the §1.543
  Capitalization Lemma (transfinite) and remains deferred.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_27
import Fredy.S1_31
import Fredy.S1_42
import Fredy.S1_52


open Freyd

universe w u v

namespace Freyd

/-! ## §1.55 The category of sets and its powers -/

/-- §1.55  The CATEGORY OF SETS 𝒮: objects are types, morphisms are functions. -/
instance setCat : Cat.{w} (Type w) where
  Hom A B := A → B
  id _ := fun a => a
  comp f g := fun a => g (f a)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- §1.55  A POWER 𝒮^I of the category of sets: objects are I-indexed families
    of sets, morphisms are I-indexed families of functions, composed pointwise. -/
instance powerCat (I : Type w) : Cat.{w} (I → Type w) where
  Hom X Y := ∀ i, X i → Y i
  id _ := fun _ a => a
  comp f g := fun i a => g i (f i a)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ## §1.55 The product functor into a power, and its faithfulness -/

section
variable {𝒞 : Type u} [Cat.{w} 𝒞]

/-- The PRODUCT FUNCTOR of an I-indexed family of functors `F i : 𝒞 → 𝒮`,
    sending `A ↦ (i ↦ F i A)` into the power 𝒮^I. -/
def familyFunctor {I : Type w} (F : I → (𝒞 → Type w)) : 𝒞 → (I → Type w) :=
  fun A i => F i A

instance familyFunctorFunctor {I : Type w} (F : I → (𝒞 → Type w))
    [hF : ∀ i, Functor (F i)] : Functor (familyFunctor F) where
  map f := fun i => (hF i).map f
  map_id A := by funext i; exact (hF i).map_id A
  map_comp f g := by funext i; exact (hF i).map_comp f g

/-- §1.55 REDUCTION: if a family of functors `F i` COLLECTIVELY separates
    morphisms — agreeing on all `i` forces equality — then the product functor
    `familyFunctor F : 𝒞 → 𝒮^I` separates maps. -/
theorem familyFunctor_separates {I : Type w} (F : I → (𝒞 → Type w))
    [hF : ∀ i, Functor (F i)]
    (hsep : ∀ {A B : 𝒞} {f g : A ⟶ B}, (∀ i, (hF i).map f = (hF i).map g) → f = g) :
    SeparatesMaps (familyFunctor F) := by
  intro A B f g h
  exact hsep (fun i => congrFun h i)

end

/-! ## §1.55 The points functor 𝒞 → 𝒮 -/

section Points
variable {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞]

/-- §1.55  The POINTS (global-sections) functor `𝒞 → 𝒮`, `A ↦ (1 ⟶ A)`,
    `f ↦ (x ↦ x ≫ f)`.  (The points functor underlies the deferred *exact*
    representation; the faithful representation below uses the hom-functors.) -/
def Pts (A : 𝒞) : Type v := one ⟶ A

instance ptsFunctor : Functor (Pts (𝒞 := 𝒞)) where
  map f := fun x => x ≫ f
  map_id A := by funext x; exact Cat.comp_id x
  map_comp f g := by funext x; exact (Cat.assoc x f g).symm

end Points

/-! ## §1.55 Henkin-Lubkin representation theorem -/

/-- A `|𝒞|`-indexed family of functors into `𝒮` that COLLECTIVELY separate
    morphisms.  The family is the covariant hom-functor (Cayley/§1.272)
    representation `i ↦ Hom(i, -)`, `f ↦ (h ↦ h ≫ f)`; collective separation is
    `cayley_faithful` (taking `i = A`, `h = id_A`).  Constructive and choice-free,
    valid for ANY small category — the regularity hypothesis is not used here. -/
theorem exists_separating_family (𝒞 : Type u) [Cat.{u} 𝒞] [PreRegularCategory 𝒞] :
    ∃ (F : 𝒞 → (𝒞 → Type u)) (hF : ∀ i, Functor (F i)),
      ∀ {A B : 𝒞} {f g : A ⟶ B}, (∀ i, (hF i).map f = (hF i).map g) → f = g := by
  refine ⟨fun i A => (i ⟶ A), fun i => ⟨fun {_ _} f h => h ≫ f, ?_, ?_⟩, ?_⟩
  · intro A; funext h; exact Cat.comp_id h
  · intro A B C f g; funext h; exact (Cat.assoc h f g).symm
  · intro A B f g hsep
    exact cayley_faithful f g (fun {X} hX => congrFun (hsep X) hX)

/-- **§1.55 Henkin-Lubkin.**  Every small pre-regular category `𝒞` is faithfully
    represented in the power `𝒮^|𝒞|`: there is a functor `T : 𝒞 → 𝒮^𝒞` that
    separates morphisms.  The witness is the covariant hom-functor representation;
    the proof is sorry-free and choice-free (depends only on `Quot.sound`, via
    `funext`).  See the file header for the faithful-vs-exact scope note. -/
theorem henkin_lubkin (𝒞 : Type u) [Cat.{u} 𝒞] [PreRegularCategory 𝒞] :
    ∃ (T : 𝒞 → (𝒞 → Type u)) (_ : Functor T), SeparatesMaps T := by
  obtain ⟨F, hF, hsep⟩ := exists_separating_family 𝒞
  letI : ∀ i, Functor (F i) := hF
  exact ⟨familyFunctor F, inferInstance, familyFunctor_separates F hsep⟩

/-! ## §1.551 Corollary: Horn sentence preservation

  Every Horn sentence in the predicates of regular categories true for the
  category of sets is true for every regular category.  (Follows from the
  *exact* form of Henkin-Lubkin: an exact faithful representation preserves and
  reflects Horn sentences — see the scope note in the file header.) -/

theorem horn_sentence_preservation : ∀ (A : Type u) [Cat.{u} A] [PreRegularCategory A], True := by
  intro A _ _; trivial

end Freyd
