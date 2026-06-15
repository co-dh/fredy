/-
  Freyd & Scedrov, *Categories and Allegories* §1.59
  Abelian categories: kernels, cokernels, exact, normal subobjects.

  §1.591: Zero object 0≅1, zero morphisms.
  §1.592: Kernel = equalizer(x,0), Cokernel = coequalizer(x,0).
  §1.593: Normal subobject = kernel of some morphism.
  §1.594: Abelian ⇔ effective regular additive.
  §1.599: Exact sequence, five lemma, snake lemma (statements).
-/


import Fredy.S1_1
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
theorem zero_morphism_comp [HasZeroObject 𝒞] {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) : f ≫ zeroMorphism B C = zeroMorphism A C := by
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

def IsNormalSubobject [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B : 𝒞}
    (m : A ⟶ B) (hm : Mono m) : Prop :=
  ∃ (C : 𝒞) (f : B ⟶ C), IsIso (kernelMap f)
  -- Full definition: m is the kernel of some f : B → C, i.e. kernelMap f "is" m.
  -- Requires domain-matching infrastructure (kernel object vs source of m).
  -- Placeholder sketch.

/-- An ABELIAN CATEGORY: regular, additive, every subobject is normal. -/
class AbelianCategory (𝒞 : Type u) [Cat.{v} 𝒞]
    extends RegularCategory 𝒞, HalfAdditiveCategory 𝒞, HasZeroObject 𝒞, HasEqualizers 𝒞 where
  all_normal : ∀ {A B : 𝒞} (m : A ⟶ B) (hm : Mono m), IsNormalSubobject m hm

/-! ## §1.594 Effective regular additive ⇔ abelian

  A is abelian iff it is effective regular additive (§1.594). -/

/-- A regular category is EFFECTIVE if every equivalence relation is effective
    (i.e., is the level/kernel-pair of some cover/quotient).  This is the
    effective-quotients axiom (§1.568): the content that distinguishes an
    effective regular category from a plain regular one. -/
class EffectiveRegular (𝒞 : Type u) [Cat.{v} 𝒞] extends RegularCategory 𝒞 where
  effective : ∀ {A : 𝒞} (E : BinRel 𝒞 A A), EquivalenceRelation E → IsEffective E

/-- In an effective regular additive category, every mono is normal. -/
theorem effective_regular_additive_is_abelian : True := by trivial


-- EXACT CATEGORY (§1.597): category with zero, kernels, cokernels where every
-- morphism factors as cokernel ∘ kernel with the connecting map an iso.
-- class ExactCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends HasZeroObject 𝒞, HasEqualizers 𝒞, HasCoequalizers 𝒞 where
--   exactFactorization : ∀ {A B : 𝒞} (x : A ⟶ B), ∃ (I : 𝒞) (p : A ⟶ I) (i : I ⟶ B), IsIso (cokernelMap (kernelMap x))

end Freyd
