/-
  Freyd & Scedrov, *Categories and Allegories* §1.85
  Exponential categories (cartesian closed).

  §1.85  EXPONENTIAL CATEGORY: binary products + for each A,
         the functor A × - has a right adjoint (-)^A.
  §1.852 Poset exponential ↔ binary meets + Heyting arrow
  §1.853 B^A as a bifunctor (covariant in B, contravariant in A)
  §1.857 EXPONENTIAL IDEAL, REPLETE SUBCATEGORY; theorems
  §1.858 KURATOWSKI INTERIOR, LAWVERE-TIERNEY CLOSURE; theorem
  §1.859 BASEABLE objects, inclusion preserves equalizers
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_31
import Fredy.S1_34
import Fredy.S1_43
import Fredy.S1_8


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ### Product functor A × -

  For each object A, the endofunctor A × - sends X ↦ A × X, f ↦ A × f. -/

section ProductFunctor

variable [hp' : HasBinaryProducts 𝒞]

/-- A × f : A × X → A × Y, with (A×f)≫fst = fst, (A×f)≫snd = snd≫f. -/
def prodMap (A X Y : 𝒞) (f : X ⟶ Y) : prod A X ⟶ prod A Y :=
  pair (X := prod A X) (A := A) (B := Y) fst (snd ≫ f)

theorem prodMap_fst (A X Y : 𝒞) (f : X ⟶ Y) : prodMap A X Y f ≫ fst (A := A) (B := Y) = fst := by
  dsimp [prodMap]; rw [fst_pair]

theorem prodMap_snd (A X Y : 𝒞) (f : X ⟶ Y) : prodMap A X Y f ≫ snd = snd ≫ f := by
  dsimp [prodMap]; rw [snd_pair]

theorem pair_fst_snd (A X : 𝒞) :
    pair (X := prod A X) (A := A) (B := X) fst snd = Cat.id (prod A X) :=
  (pair_uniq (X := prod A X) (A := A) (B := X) fst snd (Cat.id _)
    (Cat.id_comp _) (Cat.id_comp _)).symm

theorem prodMap_id (A X : 𝒞) : prodMap A X X (Cat.id X) = Cat.id (prod A X) := by
  dsimp [prodMap]; rw [Cat.comp_id, pair_fst_snd]

theorem prodMap_comp (A X Y Z : 𝒞) (f : X ⟶ Y) (g : Y ⟶ Z) :
    prodMap A X Z (f ≫ g) = prodMap A X Y f ≫ prodMap A Y Z g := by
  dsimp [prodMap]
  let RHS := pair (X := prod A X) (A := A) (B := Y) fst (snd ≫ f) ≫
             pair (X := prod A Y) (A := A) (B := Z) fst (snd ≫ g)
  have h_fst : RHS ≫ fst (A := A) (B := Z) = fst := by
    dsimp [RHS]; rw [Cat.assoc, fst_pair, fst_pair]
  have h_snd : RHS ≫ snd = snd ≫ (f ≫ g) := by
    dsimp [RHS]
    rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc]
  apply (pair_uniq (X := prod A X) (A := A) (B := Z) fst (snd ≫ (f ≫ g)) RHS h_fst h_snd).symm

/-- Functor instance for A × -. -/
instance prodFunctor (A : 𝒞) : Functor (λ X => prod A X) where
  map {X Y} f := prodMap A X Y f
  map_id X := prodMap_id A X
  map_comp f g := prodMap_comp A _ _ _ f g

end ProductFunctor

/-! ## §1.85  Exponential categories

  A category with binary products is EXPONENTIAL if each functor
  A × - has a right adjoint.  The counit is the EVALUATION MAP e,
  the adjoint transpose is CARRYING (curry). -/

class HasExponentials (𝒞 : Type u) [Cat.{v} 𝒞] extends HasBinaryProducts 𝒞 where
  exp_obj : 𝒞 → 𝒞 → 𝒞
  eval_map {A B : 𝒞} : prod A (exp_obj A B) ⟶ B
  curry_map {A B X : 𝒞} (f : prod A X ⟶ B) : X ⟶ exp_obj A B
  curry_eval {A B X : 𝒞} (f : prod A X ⟶ B) :
    prodMap A X (exp_obj A B) (curry_map f) ≫ eval_map = f
  curry_unique {A B X : 𝒞} {f : prod A X ⟶ B} {g : X ⟶ exp_obj A B}
    (h_eq : prodMap A X (exp_obj A B) g ≫ eval_map = f) : g = curry_map f

variable [HasExponentials 𝒞]

/-- The exponential object B^A (§1.85). -/
def exp (A B : 𝒞) : 𝒞 := HasExponentials.exp_obj A B

notation:30 B " ^^ " A:30 => exp A B

/-- The EVALUATION MAP e : A × B^A → B (§1.85). -/
def eval_exp (A B : 𝒞) : prod A (B ^^ A) ⟶ B := HasExponentials.eval_map (A := A) (B := B)

/-- The EXPONENTIAL TRANSPOSE (curry): f : A × X → B gives Λf : X → B^A. -/
def curry {A B X : 𝒞} (f : prod A X ⟶ B) : X ⟶ B ^^ A := HasExponentials.curry_map f

/-- The characteristic equation: (A × curry f) ≫ eval = f. -/
@[simp] theorem curry_eval_eq {A B X : 𝒞} (f : prod A X ⟶ B) :
    prodMap A X (B ^^ A) (curry f) ≫ eval_exp A B = f :=
  HasExponentials.curry_eval f

/-- curry is unique: if (A × g) ≫ eval = f then g = curry f. -/
theorem curry_unique_eq {A B X : 𝒞} {f : prod A X ⟶ B} {g : X ⟶ B ^^ A}
    (h : prodMap A X (B ^^ A) g ≫ eval_exp A B = f) : g = curry f :=
  HasExponentials.curry_unique h

/-- curry is injective. -/
theorem curry_inj {A B X : 𝒞} {f₁ f₂ : prod A X ⟶ B}
    (h : curry f₁ = curry f₂) : f₁ = f₂ := by
  rw [← curry_eval_eq f₁, ← curry_eval_eq f₂, h]

/-! ## §1.852  Poset exponential characterization

  A poset, viewed as a category, is exponential iff it has binary meets
  (∧) and for every a, b there exists b^a satisfying
      x ≤ b^a  ↔  a ∧ x ≤ b.
  The element b^a is precisely the Heyting arrow a → b [§1.72].

  Here we represent a poset-as-category via a type `P` with a preorder
  `le` such that hom-sets are propositions (thin category).  Binary meets
  are represented as a `HasBinaryMeets` predicate; the Heyting arrow is
  the right adjoint to meets. -/

/-- A POSET (or preorder) viewed as a thin category:
    objects are elements, at most one morphism between any two. -/
class ThinCategory (P : Type u) [Cat.{v} P] : Prop where
  thin : ∀ {A B : P} (f g : A ⟶ B), f = g

/-- The HEYTING ARROW a → b in a thin category with binary meets.
    By §1.72: x ≤ (a → b) iff a ∧ x ≤ b (§1.852). -/
class HasHeytingArrow (P : Type u) [Cat.{v} P] [HasBinaryProducts P] where
  imp : P → P → P
  /-- Adjunction: a map x → (a→b) exists iff a∧x → b exists. -/
  imp_adj : ∀ (a b x : P), Nonempty (x ⟶ imp a b) ↔ Nonempty (prod a x ⟶ b)

/-- §1.852: A poset (thin category) is exponential iff it has binary meets
    and a Heyting arrow. -/
theorem poset_exponential_iff_meets_heytingArrow
    (P : Type u) [Cat.{v} P] [ThinCategory P] :
    Nonempty (HasExponentials P) ↔
    ∃ (hm : HasBinaryProducts P), Nonempty (@HasHeytingArrow P _ hm) := by
  sorry

/-! ## §1.857  Exponential ideal and replete subcategory

  If 𝒜 is an exponential category and 𝒜' is a FULL SUBCATEGORY, we call
  𝒜' an EXPONENTIAL IDEAL if for every A ∈ |𝒜| and B ∈ |𝒜'| the
  exponential B^A lies in 𝒜'.

  A REPLETE SUBCATEGORY is a subcategory closed under isomorphism type:
  if B ∈ 𝒜' and A ≅ B in 𝒜 then A ∈ 𝒜'.

  Theorems (§1.857):
  1. A full coreflective subcategory closed under binary products is
     exponential.
  2. A full replete reflective subcategory of an exponential category is
     an exponential ideal iff its reflections preserve products. -/

section ExponentialIdeal

variable {𝒜 : Type u} [Cat.{v} 𝒜] [HasExponentials 𝒜]
variable {𝒜' : Type u} [Cat.{v} 𝒜']

/-- A full subcategory (via inclusion I : 𝒜' → 𝒜) is an EXPONENTIAL IDEAL of 𝒜
    if for all A ∈ |𝒜| and B ∈ |𝒜'|, the exponential B^A lies in 𝒜' (§1.857). -/
def ExponentialIdeal (I : 𝒜' → 𝒜) [Functor I] : Prop :=
  Full I ∧
  ∀ (A : 𝒜) (B : 𝒜'), ∃ (E : 𝒜'), Isomorphic (I E) (exp A (I B))

/-- A subcategory (via inclusion I : 𝒜' → 𝒜) is REPLETE if it is closed under
    isomorphism type: if B ∈ |𝒜'| and I B ≅ X in 𝒜 then X ∈ |𝒜'| (§1.857). -/
def RepleteSubcategory (I : 𝒜' → 𝒜) [Functor I] : Prop :=
  ∀ (B : 𝒜') (X : 𝒜), Isomorphic (I B) X → ∃ (B' : 𝒜'), I B' = X

/-- §1.857, Part 1: A full coreflective subcategory of an exponential category
    that is closed under binary products is itself exponential.
    (The coreflection G : 𝒜 → 𝒜' witnesses exponentials via G(B^A).) -/
theorem coreflective_closed_products_is_exponential
    (I : 𝒜' → 𝒜) [Functor I]
    [HasBinaryProducts 𝒜']
    (hFull : Full I)
    (hCorfl : CoreflectiveSubcategory I)
    (hProd : ∀ (B₁ B₂ : 𝒜'), Isomorphic (I (prod B₁ B₂)) (prod (I B₁) (I B₂))) :
    Nonempty (HasExponentials 𝒜') := by
  sorry

/-- §1.857, Part 2: A full replete reflective subcategory of an exponential
    category is an exponential ideal iff its reflections preserve products.
    "Reflections preserve products" means: for A₁, A₂ ∈ |𝒜|, the image
    I(Ā₁ × Ā₂) ≅ I(Ā₁×A₂) in 𝒜, i.e. I preserves the product of the
    reflections; equivalently, Ā₁×A₂ ≅ Ā₁×Ā₂ in 𝒜. -/
theorem reflective_exponential_ideal_iff_refl_preserve_products
    [HasBinaryProducts 𝒜']
    (I : 𝒜' → 𝒜) [Functor I]
    (hFull : Full I)
    (hRepl : RepleteSubcategory I)
    (hRefl : ReflectiveSubcategory I) :
    ExponentialIdeal I ↔
    ∀ (A₁ A₂ : 𝒜),
      Isomorphic
        (I (hRefl.reflection (prod A₁ A₂)))
        (I (prod (hRefl.reflection A₁) (hRefl.reflection A₂))) := by
  sorry

end ExponentialIdeal

/-! ## §1.858  Kuratowski interior and Lawvere-Tierney closure

  On a lattice L (with meets ∧ and order ≤):

  A KURATOWSKI INTERIOR OPERATION is an operation (-)° satisfying:
    x° ≤ x          (deflationary)
    (x°)° = x°      (idempotent)
    (x ∧ y)° = x° ∧ y°  (preserves meets)
  Its fixed points are the OPEN ELEMENTS.

  A LAWVERE-TIERNEY CLOSURE OPERATION j satisfies:
    x ≤ j x           (inflationary)
    j(j x) = j x       (idempotent)
    j(x ∧ y) = j x ∧ j y  (preserves meets)
  Its fixed points are the CLOSED ELEMENTS.

  Theorem: The closed elements of an L-T closure on a Heyting algebra form
  an exponential ideal: if b is closed then (a → b) is closed. -/

section ClosureOnLattice

/-- A lattice L with meets and order, as a type with operations.
    We use a raw-type presentation to stay independent of the
    subobject-based HeytingAlgebra in §1.72. -/
structure MeetLattice where
  carrier   : Type u
  le        : carrier → carrier → Prop
  le_refl   : ∀ x, le x x
  le_trans  : ∀ {x y z}, le x y → le y z → le x z
  le_antisymm : ∀ {x y}, le x y → le y x → x = y
  meet      : carrier → carrier → carrier
  meet_le_left  : ∀ x y, le (meet x y) x
  meet_le_right : ∀ x y, le (meet x y) y
  le_meet   : ∀ {z x y}, le z x → le z y → le z (meet x y)

/-- A HEYTING LATTICE: a meet-lattice with an implication arrow (§1.72, §1.852). -/
structure HeytingLattice extends MeetLattice where
  imp       : carrier → carrier → carrier
  imp_adj   : ∀ {x a b}, le (meet a x) b ↔ le x (imp a b)

/-- A KURATOWSKI INTERIOR OPERATION on a meet-lattice (§1.858):
    deflationary, idempotent, and meet-preserving. -/
structure KuratowskiInterior (L : MeetLattice) where
  op      : L.carrier → L.carrier
  deflat  : ∀ x, L.le (op x) x
  idem    : ∀ x, op (op x) = op x
  meet_pres : ∀ x y, op (L.meet x y) = L.meet (op x) (op y)

/-- OPEN ELEMENTS of a Kuratowski interior: the fixed points. -/
def KuratowskiInterior.isOpen {L : MeetLattice} (ki : KuratowskiInterior L) (x : L.carrier) : Prop :=
  ki.op x = x

/-- A LAWVERE-TIERNEY CLOSURE OPERATION on a meet-lattice (§1.858):
    inflationary, idempotent, and meet-preserving. -/
structure LawvereTierneyClosure (L : MeetLattice) where
  op      : L.carrier → L.carrier
  inflat  : ∀ x, L.le x (op x)
  idem    : ∀ x, op (op x) = op x
  meet_pres : ∀ x y, op (L.meet x y) = L.meet (op x) (op y)

/-- CLOSED ELEMENTS of an L-T closure: the fixed points. -/
def LawvereTierneyClosure.isClosed {L : MeetLattice} (j : LawvereTierneyClosure L) (x : L.carrier) : Prop :=
  j.op x = x

/-- §1.858: The closed elements of an L-T closure on a Heyting lattice form
    an exponential ideal: if b is closed then (a → b) is closed. -/
theorem lt_closure_closed_elements_exponential_ideal
    (L : HeytingLattice) (j : LawvereTierneyClosure L.toMeetLattice)
    (a b : L.carrier)
    (hb : j.isClosed b) :
    j.isClosed (L.imp a b) := by
  sorry

/-- A PROTOclosure is an inflationary, idempotent operation (not yet assumed meet-preserving). -/
structure ProtoClosure (L : MeetLattice) where
  op      : L.carrier → L.carrier
  inflat  : ∀ x, L.le x (op x)
  idem    : ∀ x, op (op x) = op x

/-- Fixed points of a ProtoClosure. -/
def ProtoClosure.isClosed {L : MeetLattice} (j : ProtoClosure L) (x : L.carrier) : Prop :=
  j.op x = x

/-- Converse of §1.858: If the closed elements of an inflationary idempotent
    operation on a Heyting lattice are an exponential ideal (a → b closed
    whenever b is closed), then the operation preserves meets (is L-T). -/
theorem exponential_ideal_implies_lt_closure
    (L : HeytingLattice)
    (j : ProtoClosure L.toMeetLattice)
    (hIdeal : ∀ (a b : L.carrier), j.isClosed b → j.isClosed (L.imp a b)) :
    ∀ x y, j.op (L.meet x y) = L.meet (j.op x) (j.op y) := by
  sorry

end ClosureOnLattice

/-! ## §1.859  Baseable objects

  Given a category 𝒜 with binary products, an object B is BASEABLE if
  B^A = (A × -, B) is representable for all A.  The full subcategory
  𝔹 of baseable objects is itself exponential, and the inclusion 𝔹 → 𝒜
  preserves equalizers. -/

section Baseable

variable {𝒜 : Type u} [Cat.{v} 𝒜] [HasBinaryProducts 𝒜]

/-- B ∈ |𝒜| is BASEABLE if for every A ∈ |𝒜|, the functor (A × -, B)
    is representable (i.e. B^A exists) (§1.859). -/
def Baseable (B : 𝒜) : Prop :=
  ∀ (A : 𝒜), ∃ (E : 𝒜) (ev : prod A E ⟶ B),
    ∀ (X : 𝒜) (f : prod A X ⟶ B),
      ∃ (g : X ⟶ E), prodMap A X E g ≫ ev = f ∧
        ∀ (g' : X ⟶ E), prodMap A X E g' ≫ ev = f → g' = g

/-- The full subcategory of BASEABLE objects of 𝒜 (§1.859). -/
def BaseableSubcat (𝒜 : Type u) [Cat.{v} 𝒜] [HasBinaryProducts 𝒜] : Type u := { B : 𝒜 // Baseable B }

instance : Cat.{v} (BaseableSubcat 𝒜) where
  Hom B₁ B₂ := B₁.1 ⟶ B₂.1
  id B := Cat.id B.1
  comp f g := f ≫ g
  id_comp f := Cat.id_comp f
  comp_id f := Cat.comp_id f
  assoc f g h := Cat.assoc f g h

/-- The inclusion functor 𝔹 → 𝒜. -/
def baseableIncl : BaseableSubcat 𝒜 → 𝒜 := Subtype.val

instance : Functor (baseableIncl (𝒜 := 𝒜)) where
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- §1.859: The inclusion 𝔹 → 𝒜 preserves equalizers.
    BECAUSE: if e : E → B₂ is the equalizer of f, g : B₂ ⇉ B₃ in 𝔹, then
    E is constructible as the equalizer of f^A and g^A (for each A),
    so E is baseable and the underlying diagram in 𝒜 is an equalizer.
    We state this as: the cone underlying a 𝔹-equalizer is an equalizer in 𝒜. -/
theorem baseable_inclusion_preserves_equalizers
    [HasEqualizers 𝒜]
    {B₂ B₃ : BaseableSubcat 𝒜}
    (f g : B₂ ⟶ B₃)
    (cone : EqualizerCone (𝒞 := BaseableSubcat 𝒜) f g)
    -- hypothesis: cone is a 𝔹-equalizer (unique lift)
    (h_lift : ∀ (c : EqualizerCone (𝒞 := BaseableSubcat 𝒜) f g),
        ∃ (u : c.dom ⟶ cone.dom),
          u ≫ cone.map = c.map ∧
          ∀ (u' : c.dom ⟶ cone.dom), u' ≫ cone.map = c.map → u' = u) :
    Nonempty (HasEqualizer (𝒞 := 𝒜) (f : B₂.1 ⟶ B₃.1) g) := by
  sorry

end Baseable

end Freyd
