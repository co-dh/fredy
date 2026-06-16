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
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56


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

/-! ## §1.581 Bicartesian representations preserve covers

  If 𝒜 and ℬ are regular and cocartesian, and F : 𝒜 → ℬ is a functor that
  preserves coequalizers (and hence the bicartesian structure), then F
  preserves covers (§1.566: in a regular category a cover = coequalizer
  of its kernel pair). -/

/-- F PRESERVES COEQUALIZERS: the image of any coequalizer in 𝒜 is a
    coequalizer in ℬ.  Concretely: if q : B → C is the coequalizer of f, g
    in 𝒜, then hF.map q : F B → F C is the coequalizer of hF.map f, hF.map g. -/
def PreservesCoequalizers {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (F : 𝒜 → ℬ) [hF : Functor F] : Prop :=
  ∀ {A B : 𝒜} (f g : A ⟶ B) [hcoeq : HasCoequalizer f g],
    hF.map f ≫ hF.map hcoeq.map = hF.map g ≫ hF.map hcoeq.map ∧
    ∀ {X : ℬ} (h : F B ⟶ X),
      hF.map f ≫ h = hF.map g ≫ h →
      ∃ m : F hcoeq.obj ⟶ X, hF.map hcoeq.map ≫ m = h ∧
        ∀ m' : F hcoeq.obj ⟶ X, hF.map hcoeq.map ≫ m' = h → m' = m

/-- **§1.581**: If 𝒜 and ℬ are regular and cocartesian, and F : 𝒜 → ℬ
    is a functor that preserves coequalizers, then F preserves covers.
    Proof sketch: in a bicartesian regular category (§1.582) every cover
    is the coequalizer of its kernel pair; F carries that coequalizer to
    a coequalizer in ℬ; and in ℬ every such coequalizer is again a cover
    (§1.566). -/
theorem bicart_repr_preserves_covers
    {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    [RegularCategory 𝒜] [HasCoequalizers 𝒜]
    [RegularCategory ℬ] [HasCoequalizers ℬ]
    (F : 𝒜 → ℬ) [hF : Functor F]
    (hcoeq : PreservesCoequalizers F)
    {A B : 𝒜} (f : A ⟶ B) (hf : Cover f) :
    Cover (hF.map f) := by
  sorry

/-! ## §1.582 Image via coequalizer

  In a bicartesian regular category, the image of x : A → B is
  constructible as the coequalizer of its kernel pair.  Specifically:
  form the kernel pair (level) l = kp₁, r = kp₂ : kernelPair(x) ⇉ A,
  then take the coequalizer q : A → C of l and r.  The unique morphism
  m : C → B satisfying q ≫ m = x is monic; it is the image of x. -/

/-- **§1.582**: In a bicartesian regular category, the image of x : A → B is
    the coequalizer of its kernel pair.  Let l = kp₁, r = kp₂ be the
    projections of the kernel pair of x, and let q : A → C be their
    coequalizer.  The unique m : C → B with q ≫ m = x is monic. -/
theorem image_via_coeq [BicartesianCategory 𝒞] [RegularCategory 𝒞]
    {A B : 𝒞} (x : A ⟶ B) :
    let hcoeq := (HasCoequalizers.coeq (kp₁ (f := x)) (kp₂ (f := x)))
    Mono (hcoeq.desc x kp_sq) := by
  sorry

/-! ## §1.583 Effectiveness is a Horn sentence

  In a bicartesian regular category, effectiveness of an equivalence relation
  E (tabulated by l, r : E ⇉ A) is a Horn sentence in the bicartesian
  predicates: E is effective iff the coequalizer square
     E ⇉ A → C
  is a pullback (i.e. E ≅ kernelPair(q) where q : A → C is the coequalizer
  of l and r). -/

/-- **§1.583**: In a bicartesian regular category, an equivalence relation
    E on A (tabulated by l, r : E ⇉ A) is effective iff the coequalizer
    square is a pullback.  Precisely: let q : A → C be the coequalizer of
    l and r.  Then the cone ⟨E, l, r⟩ over (q, q) is a pullback
    (i.e. E ≅ kernelPair(q)) iff E is effective (is the kernel pair of
    a cover).  The forward direction is the Horn sentence: E is a pullback
    of (q, q), which is expressible in bicartesian predicates. -/
theorem effectiveness_iff_coeq_pullback [BicartesianCategory 𝒞] [RegularCategory 𝒞]
    {A E : 𝒞} (l r : E ⟶ A) :
    -- The coequalizer of l, r coequalizes them by definition
    let hcoeq := HasCoequalizers.coeq l r
    let q := hcoeq.map
    let hlr : l ≫ q = r ≫ q := hcoeq.eq
    -- E is effective (kernel pair of a cover) iff ⟨E,l,r⟩ is a pullback of (q, q)
    (∃ (Q : 𝒞) (x : A ⟶ Q), Cover x ∧
        IsIso ((HasPullbacks.has x x).lift ⟨E, l, r, by
            -- l ≫ x = r ≫ x follows from l ≫ q = r ≫ q and the coequalizer desc
            sorry⟩)) ↔
    (⟨E, l, r, hcoeq.eq⟩ : Cone q q).IsPullback := by
  sorry

/-! ## §1.59 Abelian categories

  ABELIAN: bicartesian satisfying all Horn sentences true for 𝒜𝒷.
  First consequences: 0≅1 (zero object), finite (co)products coincide,
  half-additive structure with the middle-two interchange law. -/

/-- A ZERO OBJECT is simultaneously terminal and coterminal: 0 ≅ 1. -/
def IsZeroObject (Z : 𝒞) [ht : HasTerminal 𝒞] [hc : HasCoterminator 𝒞] : Prop :=
  hc.zero = ht.one

/-! ### §1.591 Half-additive and additive categories

  In an abelian category the canonical map A+B → A×B is an isomorphism.
  This gives each hom-set an abelian monoid structure (half-additive),
  with the middle-two interchange law.  Requiring inverses gives additive. -/

/-- A HALF-ADDITIVE CATEGORY: finite products = finite coproducts, yielding
    an abelian monoid structure on each Hom(A,B).  (§1.591)

    The `zeroHom A B` is the zero morphism A → 0 → B through the zero object.
    The canonical map `A+B → A×B` (whose (i,j)-entry is δᵢⱼ) is an isomorphism.
    The `add` field gives the induced abelian-monoid addition on each Hom(A,B). -/
class HalfAdditiveCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasCoterminator 𝒞, HasBinaryCoproducts 𝒞 where
  /-- Zero morphism A → 0 → B through the zero object (0 ≅ 1). -/
  zeroHom : ∀ (A B : 𝒞), A ⟶ B
  /-- The canonical map A+B → A×B (δᵢⱼ-matrix) is an isomorphism.
      This is the key horn sentence expressing that products = coproducts. -/
  prod_coprod_coincide : ∀ (A B : 𝒞),
    IsIso (HasBinaryCoproducts.case
        (pair (Cat.id A) (zeroHom A B))
        (pair (zeroHom B A) (Cat.id B)) :
      HasBinaryCoproducts.coprod A B ⟶ prod A B)
  /-- The abelian-monoid addition on Hom(A,B), induced by products = coproducts:
      x + y = A → A⊕A → B   (using codiagonal; or dually via diagonal). -/
  add : ∀ {A B : 𝒞}, (A ⟶ B) → (A ⟶ B) → (A ⟶ B)
  add_zero : ∀ {A B : 𝒞} (f : A ⟶ B), add f (zeroHom A B) = f
  zero_add : ∀ {A B : 𝒞} (f : A ⟶ B), add (zeroHom A B) f = f

/-- In a half-additive category, each Hom(A,B) carries the structure's addition. -/
def homAdd [inst : HalfAdditiveCategory 𝒞] {A B : 𝒞} : (A ⟶ B) → (A ⟶ B) → (A ⟶ B) :=
  inst.add

/-- **Middle-two interchange law** (§1.591): `(u + v) + (x + y) = (u + x) + (v + y)`.
    This is the fundamental identity that, together with unitality, forces
    commutativity and associativity of the addition.  Proved from the
    product/coproduct coincidence by universality of the product and coproduct. -/
theorem middle_two_interchange [inst : HalfAdditiveCategory 𝒞] {A B : 𝒞}
    (u v x y : A ⟶ B) :
    inst.add (inst.add u v) (inst.add x y) =
    inst.add (inst.add u x) (inst.add v y) := by
  sorry

/-- ADDITIVE CATEGORY (§1.591): half-additive with additive inverses.
    Every hom-set (A,B) is an abelian group: each f : A → B has a (unique)
    additive inverse g : A → B satisfying f + g = 0_{A,B}. -/
class AdditiveCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends HalfAdditiveCategory 𝒞 where
  /-- Additive inverses exist: every f : A → B has a g with f + g = zeroHom A B. -/
  addInv : ∀ {A B : 𝒞} (f : A ⟶ B), ∃ g : A ⟶ B, add f g = zeroHom A B

end Freyd
