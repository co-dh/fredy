/-
  Freyd & Scedrov, *Categories and Allegories* §1.97–§1.98  Boolean topoi, natural numbers.

  §1.97  BOOLEAN TOPOS: Ω is a Boolean algebra (every subobject is complemented).
  §1.971 SMALL OBJECT in a topos.
  §1.973 INTERNAL AXIOM OF CHOICE (IAC).
  §1.98  NATURAL NUMBERS OBJECT (NNO) in a topos.
  §1.981 NNO iterate for pairs: (A→B, B→B) → unique A×N→B.
  §1.983 PRIMITIVE RECURSION (parametrised) in a topos.
  §1.985 N ≅ 1+N; N→N→1 is a coequalizer.
  §1.987 PEANO PROPERTY for NNO.
  §1.98(10) Bicartesian characterization of NNO.
  §1.98(12) A-ACTION, FREE A-ACTION.
-/

import Fredy.S1_1
import Fredy.S1_9
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_58
import Fredy.S1_85


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.97  Boolean topos

  A TOPOS IS BOOLEAN if its subobject classifier Ω is an internal
  Boolean algebra, i.e. every subobject has a complement (§1.97).
  Equivalently: the negation map ¬ : Ω → Ω satisfies ¬¬ = id. -/

/-- A BOOLEAN TOPOS has ¬¬ = id on Ω, i.e. every subobject is complemented (§1.97). -/
class BooleanTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞 where
  not : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)
  double_neg : not ≫ not = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞))

/-! ## §1.98  Natural numbers object

  A NATURAL NUMBERS OBJECT in a topos is an object N with maps
  0 : 1 → N and s : N → N satisfying the Peano property:
  for any object X with x : 1 → X and f : X → X, there exists a
  unique h : N → X such that 0 ≫ h = x and s ≫ h = h ≫ f. -/

/-- A NATURAL NUMBERS OBJECT (NNO) (§1.98, §1.987): object N with zero 0:1→N
    and successor s:N→N satisfying the universal property (Peano). -/
class HasNaturalNumbersObject (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞 where
  nno : 𝒞
  zero : one ⟶ nno
  succ : nno ⟶ nno
  /-- The universal property: for X, x:1→X, f:X→X, there exists a unique
      h : N → X such that 0 ≫ h = x and s ≫ h = h ≫ f. -/
  iterate {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X) : nno ⟶ X
  iterate_zero {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X) : zero ≫ iterate x f = x
  iterate_succ {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X) : succ ≫ iterate x f = iterate x f ≫ f
  iterate_unique {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X) (h : nno ⟶ X)
    (h0 : zero ≫ h = x) (hs : succ ≫ h = h ≫ f) : h = iterate x f

/-! ## §1.973  Internal Axiom of Choice (IAC)

  A topos is IAC if the functor (-)^A preserves epics for every A (§1.973).
  In the book: "A topos is IAC if (-)*A [1.853] preserves epics, for any A."
  Here (-)^A : 𝒞 → 𝒞 sends B ↦ B^A and f : B → C to f^A : B^A → C^A. -/

/-- The map f^A : B^A → C^A induced by post-composition (§1.853).
    Given f : B → C, f^A is the curry of (eval_exp ≫ f) : A × B^A → C. -/
def expPostMap {𝒞 : Type u} [Cat.{v} 𝒞] [HasExponentials 𝒞] (A B C : 𝒞) (f : B ⟶ C)
    : exp A B ⟶ exp A C :=
  curry (eval_exp A B ≫ f)

/-- A TOPOS IS IAC (Internal Axiom of Choice) if for every A, the functor (-)^A
    sends covers to covers (§1.973). -/
def IsIAC (𝒞 : Type u) [Cat.{v} 𝒞] [Topos 𝒞] [HasExponentials 𝒞] : Prop :=
  ∀ (A B C : 𝒞) (f : B ⟶ C), Cover f → Cover (expPostMap A B C f)

/-! ## §1.981  NNO iterate for pairs

  §1.981: If 1 →⁰ N →ˢ N is a NNO, then for every A →ᵃ B ←ᵇ B there
  exists a unique A × N → B such that the two triangles commute.
  This is obtained by transposing through the exponential adjunction. -/

/-- §1.981: Given an NNO and exponentials, from a : A → B and b : B → B
    build the unique morphism A × N → B satisfying the recursion equations.
    Construction: transpose a to a_hat : 1 → B^A as curry(fst ≫ a) : 1 → B^A
    (since fst ≫ a : A × 1 → B); take b_hat = expPostMap A B B b : B^A → B^A;
    NNO-iterate gives h : N → B^A; uncurry via prodMap + eval gives A × N → B. -/
def iteratePair {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (a : A ⟶ B) (b : B ⟶ B) : prod A hN.nno ⟶ B :=
  let a_hat : one ⟶ exp A B := curry (fst ≫ a)
  let b_hat : exp A B ⟶ exp A B := expPostMap A B B b
  prodMap A hN.nno (exp A B) (hN.iterate a_hat b_hat) ≫ eval_exp A B

/-- §1.981 zero equation: (1_A, 0) ≫ iteratePair a b = a. -/
theorem iteratePair_zero {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (a : A ⟶ B) (b : B ⟶ B) :
    pair (Cat.id A) (term A ≫ hN.zero) ≫ iteratePair a b = a := by
  sorry

/-- §1.981 successor equation: (1_A, s) ≫ iteratePair a b = iteratePair a b ≫ b. -/
theorem iteratePair_succ {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (a : A ⟶ B) (b : B ⟶ B) :
    prodMap A hN.nno hN.nno (hN.succ) ≫ iteratePair a b = iteratePair a b ≫ b := by
  sorry

/-- §1.981 uniqueness: iteratePair is the unique such morphism. -/
theorem iteratePair_unique {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (a : A ⟶ B) (b : B ⟶ B)
    (h : prod A hN.nno ⟶ B)
    (h0 : pair (Cat.id A) (term A ≫ hN.zero) ≫ h = a)
    (hs : prodMap A hN.nno hN.nno hN.succ ≫ h = h ≫ b) :
    h = iteratePair a b := by
  sorry

/-! ## §1.983  Primitive recursion in a topos

  §1.983: Given a NNO 1→N→N and g : A → B and h : A × N × B → B,
  there exists a unique f : A × N → B such that
    (1_A, 0) ≫ f = g
    (1_A × s) ≫ f = (1_A, p₂, f) ≫ h
  where (1_A, p₂, f) : A × N → A × N × B. -/

/-- §1.983: PRIMITIVE RECURSION. Given NNO 1→N→N, g : A→B, h : A×N×B→B,
    the unique f : A×N→B satisfying the primitive recursion equations. -/
def primRec {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (g : A ⟶ B) (h : prod (prod A hN.nno) B ⟶ B) :
    prod A hN.nno ⟶ B :=
  -- The book constructs k : A × N → A × N × B via the iterate of §1.981,
  -- then f = k ≫ p₃ (projection to B).  We sorry the full construction.
  sorry

/-- §1.983 base equation: (1_A, 0) ≫ primRec g h = g. -/
theorem primRec_zero {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (g : A ⟶ B) (h : prod (prod A hN.nno) B ⟶ B) :
    pair (Cat.id A) (term A ≫ hN.zero) ≫ primRec g h = g := by
  sorry

/-- §1.983 step equation: (1_A × s) ≫ primRec g h = ⟨id, id, primRec g h⟩ ≫ h. -/
theorem primRec_succ {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (g : A ⟶ B) (h : prod (prod A hN.nno) B ⟶ B) :
    prodMap A hN.nno hN.nno hN.succ ≫ primRec g h =
      pair (pair fst snd) (primRec g h) ≫ h := by
  sorry

/-- §1.983 uniqueness. -/
theorem primRec_unique {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (g : A ⟶ B) (h : prod (prod A hN.nno) B ⟶ B)
    (f : prod A hN.nno ⟶ B)
    (hf0 : pair (Cat.id A) (term A ≫ hN.zero) ≫ f = g)
    (hfs : prodMap A hN.nno hN.nno hN.succ ≫ f = pair (pair fst snd) f ≫ h) :
    f = primRec g h := by
  sorry

/-! ## §1.985  N ≅ 1 + N; the coequalizer N → N → 1

  §1.985: If 1 →⁰ N →ˢ N is a NNO, then
  (1) N is a coproduct: (0; s) : 1 + N → N is an isomorphism,
  (2) N → N → 1 is a coequalizer (with s and id_N equalised). -/

/-- §1.985(1): The canonical map [0, s] : 1 + N → N is an isomorphism.
    Equivalently, N is a coproduct 1 + N. -/
theorem nno_is_coproduct {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasBinaryCoproducts 𝒞] :
    IsIso (HasBinaryCoproducts.case hN.zero hN.succ
          (A := one) (B := hN.nno) (X := hN.nno)) := by
  sorry

/-- §1.985(2): The terminal map N → 1 is a coequalizer of (s, id_N) : N ⇉ N.
    That is, for any f : N → X with s ≫ f = f, f factors uniquely through
    the terminal: ∃! g : 1 → X, term N ≫ g = f. -/
theorem nno_terminal_is_coequalizer {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] :
    ∀ (X : 𝒞) (f : hN.nno ⟶ X),
      hN.succ ≫ f = f →
      ∃ g : (one ⟶ X), term hN.nno ≫ g = f ∧
        ∀ g' : (one ⟶ X), term hN.nno ≫ g' = f → g' = g := by
  sorry

/-! ## §1.987  Peano property

  §1.987: An object A with morphisms 1 →ᵃ A and t : A → A has the PEANO PROPERTY
  iff every subobject B ↣ A that allows both a and t|_B : B → B is entire.

  §1.987 also states: given 1 →ᵃ A and A →ᵗ A, there exists a LEAST subobject
  A' ↣ A that allows both a and t|_{A'}, and A' has the Peano property. -/

/-- §1.987: An object A with a : 1 → A and t : A → A has the PEANO PROPERTY if
    every subobject B ↣ A that is stable under a and t is entire. -/
def PeanoProperty {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞] [HasImages 𝒞]
    {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) : Prop :=
  ∀ (B : Subobject 𝒞 A),
    -- B allows a: there exists e : 1 → B.dom with e ≫ B.arr = a
    Allows B a →
    -- B is stable under t: t|_B factors through B
    (∃ (tB : B.dom ⟶ B.dom), tB ≫ B.arr = B.arr ≫ t) →
    B.IsEntire

/-- §1.987: The NNO 1 →⁰ N →ˢ N has the Peano property. -/
theorem nno_peano_property {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasImages 𝒞] :
    @PeanoProperty 𝒞 _ hN.toHasTerminal _ hN.nno hN.zero hN.succ := by
  sorry

/-- §1.987: Existence of least subobject with Peano property.
    Given a : 1 → A and t : A → A, there is a least subobject A' ↣ A
    that allows a and is stable under t, and A' has the Peano property.
    The Peano property for A' is stated with respect to the induced morphisms
    a' = term A'.dom ≫ A'.arr ≫ ... restricted to A'. -/
theorem least_peano_subobject {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞] [HasImages 𝒞]
    {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) :
    ∃ (A' : Subobject 𝒞 A),
      Allows A' a ∧
      (∃ (t' : A'.dom ⟶ A'.dom), t' ≫ A'.arr = A'.arr ≫ t) ∧
      (∀ (B : Subobject 𝒞 A), Allows B a →
        (∃ (tB : B.dom ⟶ B.dom), tB ≫ B.arr = B.arr ≫ t) → A'.le B) := by
  sorry

/-! ## §1.98(12)  A-action and free A-action

  §1.98(12): Given an object A in a topos, an A-ACTION is an object B
  with morphisms e : 1 → B (unit) and s : A × B → B (action).
  A FREE A-ACTION is an A-action (A*, e : 1 → A*, s : A × A* → A*)
  such that for any A-action (B, f : 1 → B, b : A × B → B) there is
  a unique morphism A* → B respecting the action structure. -/

/-- §1.98(12): An A-ACTION is a triple (B, e, s) where e : 1 → B and s : A × B → B. -/
structure AAction {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞] (A : 𝒞) where
  obj  : 𝒞
  unit : one ⟶ obj
  act  : prod A obj ⟶ obj

/-- §1.98(12): A FREE A-ACTION for A is an A-action (A*, e, s) with the
    universal property: for any A-action (B, f, b), there is a unique
    morphism A* → B making the unit and action diagrams commute. -/
structure FreeAAction {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞] (A : 𝒞) extends AAction A where
  /-- The unique map into any A-action. -/
  recA  : (α : AAction A) → obj ⟶ α.obj
  recA_unit : ∀ (α : AAction A), unit ≫ recA α = α.unit
  recA_act  : ∀ (α : AAction A),
    prodMap A obj α.obj (recA α) ≫ α.act = act ≫ recA α
  recA_uniq : ∀ (α : AAction A) (m : obj ⟶ α.obj),
    unit ≫ m = α.unit →
    prodMap A obj α.obj m ≫ α.act = act ≫ m →
    m = recA α

/-- §1.98(12): A NNO is a free 1-action.
    The unit element is 0 : 1 → N, the action is s : 1 × N ≅ N → N.
    The iterate of the NNO provides the universal map. -/
theorem nno_is_free_one_action {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞] :
    Nonempty (FreeAAction (𝒞 := 𝒞) one) := by
  sorry

end Freyd
