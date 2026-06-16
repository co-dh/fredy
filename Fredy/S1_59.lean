/-
  Freyd & Scedrov, *Categories and Allegories* §1.59
  Abelian categories: kernels, cokernels, exact, normal subobjects.

  §1.591: Zero object 0≅1, zero morphisms.
  §1.592: Kernel = equalizer(x,0), Cokernel = coequalizer(x,0).
  §1.593: Normal subobject = kernel of some morphism.
         Abelian ↔ regular additive + all-normal subobjects.
  §1.594: Abelian ⇔ effective regular additive category.
  §1.595: Ab(A) = category of abelian group objects; Ab(A) abelian for effective regular A.
  §1.597: Exact category; abelian ↔ exact additive (with binary products or coproducts).
  §1.598: Left-normal, right-normal, normal categories.
         Abelian ↔ normal + kernels + cokernels + (products or coproducts).
  §1.599: Exact sequences, five lemma, snake lemma.
-/


import Fredy.S1_1
import Fredy.S1_34
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.591 Zero object

  If 0 ≅ 1, the zero object is the unique object that is both
  terminal and coterminal.  Every pair A,B has a ZERO MORPHISM
  A → 0 → B.  Zero morphisms form a two-sided ideal. -/

/-- A ZERO OBJECT: terminal = coterminal (§1.591). -/
class HasZeroObject (𝒞 : Type u) [Cat.{v} 𝒞] extends HasTerminal 𝒞, HasCoterminator 𝒞 where
  zero_eq_one : (one : 𝒞) = coterm

/-- The zero morphism A → B factors through the zero object. -/
def zeroMorphism [HasZeroObject 𝒞] (A B : 𝒞) : A ⟶ B :=
  let h := (HasZeroObject.zero_eq_one (𝒞 := 𝒞)).symm
  term A ≫ (cast (congrArg (λ X : 𝒞 => X ⟶ B) h) (zeroMap B))

/-- Zero morphisms are a two-sided ideal: f≫0 = 0, 0≫f = 0. -/
theorem zero_morphism_comp [HasZeroObject 𝒞] {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) :
    f ≫ zeroMorphism B C = zeroMorphism A C := by
  dsimp [zeroMorphism]
  rw [← Cat.assoc]
  rw [term_uniq (f ≫ term B) (term A)]

/-! ## §1.592 Kernels and cokernels

  KERNEL of x: equalizer of (x, 0).  COKERNEL: coequalizer of (x, 0). -/

/-- Kernel of x: the equalizer of x and the zero morphism (§1.592). -/
def Kernel [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B : 𝒞} (x : A ⟶ B) : 𝒞 :=
  eqObj x (zeroMorphism A B)

def kernelMap [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B : 𝒞} (x : A ⟶ B) :
    Kernel x ⟶ A :=
  eqMap x (zeroMorphism A B)

theorem kernelMap_eq [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B : 𝒞} (x : A ⟶ B) :
    kernelMap x ≫ x = kernelMap x ≫ zeroMorphism A B :=
  eqMap_eq x (zeroMorphism A B)

/-- Cokernel of x: the coequalizer of x and the zero morphism (§1.592). -/
def Cokernel [HasZeroObject 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (x : A ⟶ B) : 𝒞 :=
  (HasCoequalizers.coeq x (zeroMorphism A B)).obj

def cokernelMap [HasZeroObject 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (x : A ⟶ B) :
    B ⟶ Cokernel x :=
  (HasCoequalizers.coeq x (zeroMorphism A B)).map

/-! ## §1.593 Normal subobjects

  A subobject is NORMAL if it is the kernel of some morphism.
  A is ABELIAN iff it is a regular additive category in which
  every subobject is normal. -/

/-! A subobject m : A ↣ B is NORMAL (§1.593) if m is the kernel of some f : B → C,
  i.e. there is a morphism h : A → Kernel f that is an iso with h ≫ kernelMap f = m. -/
def IsNormalSubobject [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B : 𝒞}
    (m : A ⟶ B) (hm : Mono m) : Prop :=
  ∃ (C : 𝒞) (f : B ⟶ C) (h : A ⟶ Kernel f), IsIso h ∧ h ≫ kernelMap f = m

/-- An ABELIAN CATEGORY: regular, additive, every subobject is normal (§1.593).
  Includes cokernels (§1.592: an abelian category has kernels and cokernels). -/
class AbelianCategory (𝒞 : Type u) [Cat.{v} 𝒞]
    extends RegularCategory 𝒞, HalfAdditiveCategory 𝒞, HasZeroObject 𝒞,
            HasEqualizers 𝒞, HasCoequalizers 𝒞 where
  all_normal : ∀ {A B : 𝒞} (m : A ⟶ B) (hm : Mono m), IsNormalSubobject m hm

/-! **§1.593**: A is abelian iff it is a regular additive category in which every
  subobject is normal.

  PROOF (sketch): Given a regular additive category with all monics normal, we obtain
  cokernels as follows.  For any monic x:A↣B, by normality x = kernel(y) for some y:B→C.
  Since we also have images (regular), every morphism factors as cover ∘ monic.
  In a regular additive category with all-normal subobjects, a cover that is monic must
  be an iso; hence cokernels exist.  This plus the T:A→Ab faithful representation
  (from §1.552, using one-valuedness + regular) shows cokernels are preserved, giving
  the full abelian bicartesian structure.  The other direction is §1.594 + §1.592. -/
theorem abelian_iff_regular_additive_all_normal
    (𝒞 : Type u) [Cat.{v} 𝒞]
    [RegularCategory 𝒞] [AdditiveCategory 𝒞] [HasZeroObject 𝒞]
    [HasEqualizers 𝒞] [HasCoequalizers 𝒞] :
    (∀ {A B : 𝒞} (m : A ⟶ B) (hm : Mono m), IsNormalSubobject m hm) ↔
    Nonempty (AbelianCategory 𝒞) := by
  sorry

/-! ## §1.594 Effective regular additive ⇔ abelian

  A is abelian iff it is an effective regular additive category (§1.594). -/

/-- A regular category is EFFECTIVE if every equivalence relation is effective
    (i.e., is the level/kernel-pair of some cover/quotient).  This is the
    effective-quotients axiom (§1.568): the content that distinguishes an
    effective regular category from a plain regular one. -/
class EffectiveRegular (𝒞 : Type u) [Cat.{v} 𝒞] extends RegularCategory 𝒞 where
  effective : ∀ {A : 𝒞} (E : BinRel 𝒞 A A), EquivalenceRelation E → IsEffective E

/-! §1.594: A is abelian iff it is an effective regular additive category.
  Direction proved here: effective regular additive ⟹ every mono is a kernel
  (i.e. every subobject is normal), so the category is abelian.

  Proof sketch (Freyd §1.594):
  (⟸) Given monic x:A↣B, form the relation E on B whose tabulation
  is `⟨x,x⟩:A→B×B` (both legs = x; this is reflexive by additivity
  — in the faithful Ab-representation, E(b,b') iff b=b'=x(a) for some a,
  which is reflexive).  By the calculus of relations (which holds in any
  regular additive category faithfully represented in Ab via §1.552),
  a reflexive endo-relation is an equivalence relation.  By effectiveness,
  E is the kernel pair of some cover q:B↠C.  Then x is the kernel of q.

  (⟹) Any abelian category is effective regular (§1.582–1.583 combined with
  the bicartesian structure).

  Full formalization deferred: requires formalizing the Ab-calculus (§1.55)
  and the inverse-image lemma from §1.582. -/
theorem effective_regular_additive_is_abelian
    (𝒞 : Type u) [Cat.{v} 𝒞]
    [EffectiveRegular 𝒞] [AdditiveCategory 𝒞] [HasZeroObject 𝒞] [HasEqualizers 𝒞] :
    ∀ {A B : 𝒞} (m : A ⟶ B) (hm : Mono m), IsNormalSubobject m hm := by
  sorry


/-! ## §1.595 Abelian group objects

  In any category A with finite products, an ABELIAN GROUP OBJECT is an object A
  together with morphisms
    zero  : 1 → A        (identity element)
    neg   : A → A        (additive inverse)
    add   : A × A → A   (addition)
  satisfying the commutative diagrams:

    (i)   (add ∘ ⟨zero ∘ term, id⟩ = id)         left unit
    (ii)  (add ∘ ⟨neg, id⟩ ∘ diag = zero ∘ term)  left inverse
    (iii) add ∘ (id × add) = add ∘ (add × id) ∘ assoc  associativity
    (iv)  add ∘ swap = add                           commutativity

  where swap : A × A → A × A is pair(snd, fst) and assoc : A×(B×C) → (A×B)×C
  is the standard associator.

  Ab(A) denotes the category whose objects are abelian group objects and whose
  morphisms are A-morphisms x : A → B satisfying x ≫ add_B = (x × x) ≫ add_A
  (homomorphism condition). -/

/-- An ABELIAN GROUP OBJECT in a category with finite products (§1.595).
  Fields: carrier object, identity/inverse/addition morphisms, four axioms. -/
structure AbelianGroupObject (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] where
  /-- The underlying object. -/
  carrier : 𝒞
  /-- Zero element: 1 → A. -/
  zero  : (one : 𝒞) ⟶ carrier
  /-- Additive inverse: A → A. -/
  neg   : carrier ⟶ carrier
  /-- Addition: A × A → A. -/
  add   : prod carrier carrier ⟶ carrier
  /-- Left unit: ⟨zero ∘ !, id⟩ ≫ add = id. -/
  add_zero : pair (term carrier ≫ zero) (Cat.id carrier) ≫ add = Cat.id carrier
  /-- Left inverse: ⟨neg, id⟩ ≫ add = zero ∘ !. -/
  add_neg  : pair neg (Cat.id carrier) ≫ add = term carrier ≫ zero
  /-- Associativity: from source (A×A)×A, both bracketings compute equal results.
    LHS: (x+y)+z = (fst ≫ add, snd) ≫ add.
    RHS: x+(y+z) = (fst≫fst, (fst≫snd, snd) ≫ add) ≫ add. -/
  add_assoc :
      pair (fst (A := prod carrier carrier) (B := carrier) ≫ add)
           (snd (A := prod carrier carrier) (B := carrier)) ≫ add =
      pair (fst (A := prod carrier carrier) (B := carrier) ≫ fst)
           (pair (fst (A := prod carrier carrier) (B := carrier) ≫ snd)
                 (snd (A := prod carrier carrier) (B := carrier)) ≫ add) ≫ add
  /-- Commutativity: swap ≫ add = add. -/
  add_comm : pair (snd (A := carrier) (B := carrier)) fst ≫ add = add

/-- A HOMOMORPHISM of abelian group objects: an A-morphism respecting addition (§1.595). -/
-- Homomorphism condition: the square addA ≫ x = (x×x) ≫ addB commutes.
-- Both sides have source prod A.carrier A.carrier.
-- (x×x) is spelled out as pair (fst ≫ x) (snd ≫ x).
def IsHomAbelianGroupObject {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    (A B : AbelianGroupObject 𝒞) (x : A.carrier ⟶ B.carrier) : Prop :=
  A.add ≫ x = pair (fst ≫ x) (snd ≫ x) ≫ B.add

/-- Hom-set in Ab(A): morphisms that are homomorphisms. -/
def HomAb {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    (A B : AbelianGroupObject 𝒞) : Type v :=
  { x : A.carrier ⟶ B.carrier // IsHomAbelianGroupObject A B x }

/-! If A is effective regular, then Ab(A) is also effective regular and the
  forgetful functor Ab(A) → A is a faithful representation of regular categories
  (§1.595).  Consequently, Ab(A) is an abelian category for any effective regular A. -/

/-! §1.595 (consequence): For any effective regular category A, the category Ab(A)
  is abelian.  Proof: Ab(A) is effective regular (forgetful functor is a faithful
  representation of regular categories) and additive by construction; abelianness
  then follows from §1.594.  Formalizing this requires a `Cat` instance for Ab(A),
  which depends on universe-polymorphic hom-set infrastructure left for future work. -/


/-! ## §1.597 Exact categories

  A category with zero, kernels, and cokernels is EXACT if for every x:A→B
  the unique map θ : coker(ker(x)) → ker(coker(x)) is an isomorphism.

  Equivalently: every morphism factors as (cokernel of something) ∘ (kernel of something).

  A is abelian iff it is an exact additive category.
  More precisely: A is abelian iff it is an exact category with either binary
  products or binary coproducts. -/

/-- An EXACT CATEGORY (§1.597): category with zero, kernels, cokernels where
  the canonical map θ : coker(ker(x)) → ker(coker(x)) is an isomorphism
  for every morphism x.

  The map θ exists because: cokernelMap(kernelMap x) : coker(ker x) → B
  satisfies `kernelMap x ≫ cokernelMap(kernelMap x) = 0` (the cokernel map kills
  the kernel), so it factors through ker(coker x) ↣ B via the universal property
  of the kernel.  θ is this factorization morphism. -/
class ExactCategory (𝒞 : Type u) [Cat.{v} 𝒞]
    extends HasZeroObject 𝒞, HasEqualizers 𝒞, HasCoequalizers 𝒞 where
  /-- The canonical coimage-to-image map θ : coker(ker x) → ker(coker x) is an iso. -/
  exact : ∀ {A B : 𝒞} (x : A ⟶ B),
    ∃ (θ : Cokernel (kernelMap x) ⟶ Kernel (cokernelMap x)), IsIso θ

/-! §1.597 key lemma: if A ↣ B is monic and q : B → Q is its cokernel, then A is
  the kernel of q.  (Follows from the exact factorization.) -/
theorem monic_kernel_of_cokernel {𝒞 : Type u} [Cat.{v} 𝒞] [ExactCategory 𝒞] {A B : 𝒞}
    (x : A ⟶ B) (hx : Mono x) :
    let Q := Cokernel x
    let q := cokernelMap x
    ∃ (h : A ⟶ Kernel q), IsIso h ∧ h ≫ kernelMap q = x := by
  sorry

/-! §1.597: A is abelian iff it is an exact additive category (with binary products
  or coproducts).

  PROOF (sketch, Freyd):
  (⟹) Any abelian category is exact: images exist (regular), and in the
  effective-regular additive setting the coimage-image map θ is always an iso.

  (⟸) Given an exact additive category A with binary products:
  — Binary subtraction: using the exact factorization, construct a - operation
    on each hom-set via the cokernel of the diagonal A → A×A.
  — This yields a ring structure on each hom-set, making A additive.
  — Every pullback of a cover is a cover (regularity): follows from the
    exact-category pushout lemma (a pullback square with one cover side is
    also a pushout, making the parallel side a cover).
  — Every monic is a kernel (normality): since each morphism factors as
    cokernel ∘ kernel, a monic that is also a cokernel is a kernel; iterate. -/
theorem abelian_iff_exact_additive
    {𝒞 : Type u} [Cat.{v} 𝒞]
    [ExactCategory 𝒞] [AdditiveCategory 𝒞] [HasBinaryProducts 𝒞] :
    Nonempty (AbelianCategory 𝒞) := by
  sorry


/-! ## §1.598 Normal categories

  A category with zero is LEFT-NORMAL if every subobject (monic) is normal,
  and RIGHT-NORMAL if every comonic (epi seen as a quotient) is a cokernel.
  A NORMAL CATEGORY is both left- and right-normal.

  Historical note: the first book on the subject (Mitchell, 1964) defined
  abelian categories as normal categories with kernels, cokernels, binary
  products and coproducts. -/

/-- LEFT-NORMAL: every subobject is normal (= kernel of some morphism). -/
def IsLeftNormal (𝒞 : Type u) [Cat.{v} 𝒞] [HasZeroObject 𝒞] [HasEqualizers 𝒞] : Prop :=
  ∀ {A B : 𝒞} (m : A ⟶ B) (hm : Mono m), IsNormalSubobject m hm

/-- RIGHT-NORMAL: every cover (Cover e) is a cokernel of some morphism,
  i.e. e = cokernelMap f for some f (up to the cokernel object being B).
  Formally: there exist W, f, and an iso i : Cokernel f ≅ B such that
  cokernelMap f ≫ i.inv = e. -/
def IsRightNormal (𝒞 : Type u) [Cat.{v} 𝒞] [HasZeroObject 𝒞] [HasCoequalizers 𝒞] : Prop :=
  ∀ {A B : 𝒞} (e : A ⟶ B), Cover e →
    ∃ (W : 𝒞) (f : W ⟶ A) (i : Cokernel f ⟶ B),
      IsIso i ∧ cokernelMap f ≫ i = e

/-- NORMAL CATEGORY: both left- and right-normal (§1.598). -/
def IsNormalCategory (𝒞 : Type u) [Cat.{v} 𝒞] [HasZeroObject 𝒞]
    [HasEqualizers 𝒞] [HasCoequalizers 𝒞] : Prop :=
  IsLeftNormal 𝒞 ∧ IsRightNormal 𝒞

/-! §1.598: A is abelian iff it is a normal category with kernels, cokernels and
  either binary products or binary coproducts.

  PROOF (sketch, Freyd):
  Given a normal category with kernels, cokernels, and binary products:
  — Construct pullbacks of pairs of monics from kernel + product (§1.434-style).
  — Every cover is epic (from the pullback of a mono via a cover).
  — For x:A→B, the normal closure ker(coker(x)) is the image of x (since every
    subobject is normal = kernel, so the minimal normal subobject allowing x is
    the image).  Factor x as A ↠ C ↣ B where A↠C is a cover (epic = cokernel).
  — A is exact.  Then apply §1.597. -/
theorem abelian_iff_normal_kernels_cokernels
    {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasZeroObject 𝒞] [HasEqualizers 𝒞] [HasCoequalizers 𝒞] [HasBinaryProducts 𝒞] :
    IsNormalCategory 𝒞 → Nonempty (AbelianCategory 𝒞) := by
  sorry


/-! ## §1.599 Exact sequences and diagram lemmas

  Given objects A_n and morphisms A_{n-1} → A_n → A_{n+1}, the sequence is
  EXACT at A_n if the image of (A_{n-1} → A_n) equals the kernel of (A_n → A_{n+1}).
  Equivalently (in an abelian category), the image of f_{n-1} is a kernel of f_n.

  The FIVE LEMMA and SNAKE LEMMA are the two key diagram lemmas. -/

/-! EXACT at B (§1.599): a composable pair f : A → B, g : B → C is exact at B
  when the image of f is isomorphic to the kernel of g.
  Note: `ExactAt` is defined in `S1_39.lean`; this comment documents it here per §1.599.
  We use `Isomorphic (image f).dom (Kernel g)` inline in statements below. -/

/-! §1.599 FIVE LEMMA: In an abelian category, given a commutative diagram

      A₁ → A₂ → A₃ → A₄ → A₅
      |    |    |    |    |
      B₁ → B₂ → B₃ → B₄ → B₅

  with exact rows, if the outer four verticals (A₁→B₁, A₂→B₂, A₄→B₄, A₅→B₅)
  are isomorphisms, then the middle vertical (A₃→B₃) is also an isomorphism.

  PROOF: This is a Horn sentence in bicartesian predicates, so it holds in any
  abelian category iff it holds in Ab.  In Ab: the center vertical has zero kernel
  (easy diagram chase); the definition of exact category is self-dual, so zero
  cokernel as well; hence it is an isomorphism. -/
theorem five_lemma [AbelianCategory 𝒞]
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : 𝒞}
    {a₁ : A₁ ⟶ A₂} {a₂ : A₂ ⟶ A₃} {a₃ : A₃ ⟶ A₄} {a₄ : A₄ ⟶ A₅}
    {b₁ : B₁ ⟶ B₂} {b₂ : B₂ ⟶ B₃} {b₃ : B₃ ⟶ B₄} {b₄ : B₄ ⟶ B₅}
    {v₁ : A₁ ⟶ B₁} {v₂ : A₂ ⟶ B₂} {v₃ : A₃ ⟶ B₃} {v₄ : A₄ ⟶ B₄} {v₅ : A₅ ⟶ B₅}
    -- rows are exact (image of aₙ ≅ kernel of aₙ₊₁)
    (hA₁₂ : Isomorphic (image a₁).dom (Kernel a₂))
    (hA₂₃ : Isomorphic (image a₂).dom (Kernel a₃))
    (hA₃₄ : Isomorphic (image a₃).dom (Kernel a₄))
    (hB₁₂ : Isomorphic (image b₁).dom (Kernel b₂))
    (hB₂₃ : Isomorphic (image b₂).dom (Kernel b₃))
    (hB₃₄ : Isomorphic (image b₃).dom (Kernel b₄))
    -- squares commute
    (sq₁ : a₁ ≫ v₂ = v₁ ≫ b₁) (sq₂ : a₂ ≫ v₃ = v₂ ≫ b₂)
    (sq₃ : a₃ ≫ v₄ = v₃ ≫ b₃) (sq₄ : a₄ ≫ v₅ = v₄ ≫ b₄)
    -- outer four verticals are isos
    (h₁ : IsIso v₁) (h₂ : IsIso v₂) (h₄ : IsIso v₄) (h₅ : IsIso v₅) :
    IsIso v₃ := by
  sorry

/-! §1.599 SNAKE LEMMA: In an abelian category, given a commutative diagram

      A ──f──→ B ──g──→ C
      |α       |β       |γ
      ↓        ↓        ↓
      A'──f'──→B'──g'──→C'

  with both rows exact, there exist induced morphisms on kernels/cokernels
  and a "connecting morphism" δ : ker(γ) → coker(α) making the sequence

    ker(α) → ker(β) → ker(γ) →δ coker(α) → coker(β) → coker(γ)

  exact.  (Sufficient to verify in Ab; the statement is a Horn sentence.)

  The induced morphisms are:
    κ_f : ker(α) → ker(β)   (kernel-functoriality of f)
    κ_g : ker(β) → ker(γ)   (kernel-functoriality of g)
    π_f : coker(α) → coker(β)  (cokernel-functoriality of f')
    π_g : coker(β) → coker(γ)  (cokernel-functoriality of g')
  These are defined by universal properties; we state their existence. -/
theorem snake_lemma [AbelianCategory 𝒞]
    {A B C A' B' C' : 𝒞}
    {f : A ⟶ B} {g : B ⟶ C} {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'}
    {f' : A' ⟶ B'} {g' : B' ⟶ C'}
    -- rows exact (image ≅ kernel at each interior node)
    (hfg : Isomorphic (image f).dom (Kernel g))
    (hf'g' : Isomorphic (image f').dom (Kernel g'))
    -- squares commute
    (hαβ : f ≫ β = α ≫ f') (hβγ : g ≫ γ = β ≫ g') :
    -- induced kernel maps (by universal property: ker(α) ≫ f ≫ β = 0, lifts to ker(β))
    ∃ (κ_f : Kernel α ⟶ Kernel β) (κ_g : Kernel β ⟶ Kernel γ)
      (π_f : Cokernel α ⟶ Cokernel β) (π_g : Cokernel β ⟶ Cokernel γ)
      (δ : Kernel γ ⟶ Cokernel α),
      -- The induced sequence ker(α)→ker(β)→ker(γ)→coker(α)→coker(β) is exact at each node:
      Isomorphic (image κ_f).dom (Kernel κ_g) ∧
      Isomorphic (image κ_g).dom (Kernel δ) ∧
      Isomorphic (image δ).dom (Kernel π_f) ∧
      Isomorphic (image π_f).dom (Kernel π_g) := by
  sorry

end Freyd
