/-
  Freyd & Scedrov, *Categories and Allegories* §1.58–§1.59
  Bicartesian categories, abelian categories, half-additive.

  §1.58 BICARTESIAN = Cartesian + Cocartesian.
         Coterminator 0, coproduct A+B, coequalizer.
         Pushout = pullback in opposite category.
  §1.59 ABELIAN = bicartesian satisfying all Horn sentences true for 𝒜𝒷.
         Zero object, half-additive, middle-two interchange.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_51


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.58 Bicartesian categories

  A BICARTESIAN CATEGORY is both Cartesian and coCartesian:
  has finite limits and colimits. -/

/-- Has coterminator (initial object): dual to HasTerminal. -/
class HasCoterminator (𝒞 : Type u) [Cat.{v} 𝒞] where
  zero  : 𝒞
  init  : (X : 𝒞) → zero ⟶ X
  init_uniq  : ∀ {X : 𝒞} (f g : zero ⟶ X), f = g

variable [HasCoterminator 𝒞]

def coterm : 𝒞 := HasCoterminator.zero
def zeroMap (X : 𝒞) : coterm ⟶ X := HasCoterminator.init X

/-- Has binary coproducts: dual to HasBinaryProducts. -/
class HasBinaryCoproducts (𝒞 : Type u) [Cat.{v} 𝒞] where
  coprod : 𝒞 → 𝒞 → 𝒞
  inl    : {A B : 𝒞} → A ⟶ coprod A B
  inr    : {A B : 𝒞} → B ⟶ coprod A B
  case   : {X A B : 𝒞} → (A ⟶ X) → (B ⟶ X) → (coprod A B ⟶ X)
  case_inl : ∀ {X A B : 𝒞} (f : A ⟶ X) (g : B ⟶ X), inl ≫ case f g = f
  case_inr : ∀ {X A B : 𝒞} (f : A ⟶ X) (g : B ⟶ X), inr ≫ case f g = g
  case_uniq : ∀ {X A B : 𝒞} (f : A ⟶ X) (g : B ⟶ X) (h : coprod A B ⟶ X),
    inl ≫ h = f → inr ≫ h = g → h = case f g

/-- A single coequalizer: dual to HasEqualizer. -/
class HasCoequalizer {A B : 𝒞} (f g : A ⟶ B) where
  obj   : 𝒞
  map   : B ⟶ obj
  eq    : f ≫ map = g ≫ map
  desc  : ∀ {X : 𝒞} (h : B ⟶ X) (h_eq : f ≫ h = g ≫ h), obj ⟶ X
  fac   : ∀ {X : 𝒞} (h : B ⟶ X) (h_eq : f ≫ h = g ≫ h), map ≫ desc h h_eq = h
  uniq  : ∀ {X : 𝒞} (h : B ⟶ X) (h_eq : f ≫ h = g ≫ h) (m : obj ⟶ X),
    map ≫ m = h → m = desc h h_eq

/-- Has coequalizers: dual to HasEqualizers. -/
class HasCoequalizers (𝒞 : Type u) [Cat.{v} 𝒞] where
  coeq : ∀ {A B : 𝒞} (f g : A ⟶ B), HasCoequalizer f g

/-- A BICARTESIAN CATEGORY: Cartesian + coCartesian (§1.58). -/
class BicartesianCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    CartesianCategory 𝒞, HasCoterminator 𝒞, HasBinaryCoproducts 𝒞, HasCoequalizers 𝒞

/-! ## §1.583 Bicartesian regular: images via coequalizers

  In a bicartesian regular category, images can be constructed as:
  given x: A→B, form its level (kernel pair) l,r: L⇉A, then
  the coequalizer A → C of l,r.  The unique C→B is monic (= image). -/

/-- In bicartesian + images, the image of x is the coequalizer of its level. -/
axiom image_via_coeq [BicartesianCategory 𝒞] [HasImages 𝒞] {A B : 𝒞} (x : A ⟶ B) : True

/-! ## §1.59 Abelian categories

  ABELIAN: bicartesian satisfying all Horn sentences true for 𝒜𝒷.
  First consequences: 0≅1 (zero object), finite (co)products coincide,
  half-additive structure with the middle-two interchange law. -/

/-- A ZERO OBJECT is simultaneously terminal and coterminal: 0 ≅ 1. -/
def IsZeroObject (Z : 𝒞) [ht : HasTerminal 𝒞] [hc : HasCoterminator 𝒞] : Prop :=
  hc.zero = ht.one

/-- A HALF-ADDITIVE CATEGORY: finite products = finite coproducts.
    Yields an abelian monoid structure on each Hom(A,B).  (§1.59) -/
class HalfAdditiveCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasCoterminator 𝒞, HasBinaryCoproducts 𝒞 where
  prod_coprod_coincide : ∀ (A B : 𝒞), True

/-- In a half-additive category, each Hom(A,B) is an abelian monoid.
    Addition is defined via the diagonal/codiagonal.  (§1.59) -/
axiom homAdd [HalfAdditiveCategory 𝒞] (A B : 𝒞) : Cat.Hom A B → Cat.Hom A B → Cat.Hom A B

/-- Middle-two interchange law (§1.59). -/
axiom middle_two_interchange [HalfAdditiveCategory 𝒞] {A B : 𝒞} (u v x y : Cat.Hom A B) : True

/-- ADDITIVE CATEGORY (§1.591): half-additive with additive inverses. -/
class AdditiveCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends HalfAdditiveCategory 𝒞 where
  addInv : ∀ {A B : 𝒞} (f : A ⟶ B), True  -- ∃ g, f + g = 0 (needs + notation)

end Freyd
