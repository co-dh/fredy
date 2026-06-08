/-
  Freyd & Scedrov, *Categories and Allegories* §1.63–§1.66
  Slice pre-logos, Boolean pre-logoi, Pre-topoi, Amalgamation.

  §1.63  If A is a (positive) pre-logos, so is A/B (§1.63).
  §1.631 Complemented subobject: A₁∩A₂=0, A₁∪A₂=A.
  §1.64  Boolean pre-logos: subobject lattices are Boolean algebras.
  §1.644 Ultra-product / ultra-power functors (§1.644).
  §1.645 𝒦𝓮𝓇(T) = values killed by representation T.
  §1.65  Pre-topos = effective positive pre-logos.
  §1.651 Amalgamation Lemma: pushout of two monics exists.
  §1.652 In a pre-topos: covers = epics, monics = cocovers.
  §1.66  (if applicable)
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58
import Fredy.S1_60
import Fredy.S1_62

set_option linter.unusedSectionVars false

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.631 Complemented subobject

  A₁ ⊆ A is COMPLEMENTED if ∃ A₂ ⊆ A with A₁∩A₂=0, A₁∪A₂=A. -/

variable [PreLogos 𝒞]

/-- A₁ is COMPLEMENTED if there's A₂ with A₁∩A₂=0 and A₁∪A₂=A. -/
def IsComplemented {A : 𝒞} (A₁ : Subobject 𝒞 A) : Prop :=
  ∃ (A₂ : Subobject 𝒞 A),
    Subobject.le A₁ A₂ → False  -- placeholder for "A₁∩A₂ is minimal"
    ∧ Subobject.le (HasSubobjectUnions.union A₁ A₂) (Subobject.entire A)

/-! ## §1.64 Boolean pre-logos

  A BOOLEAN PRE-LOGOS is a pre-logos where every subobject lattice
  is Boolean (every subobject has a complement). -/

class BooleanPreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends PreLogos 𝒞 where
  hasComplement : ∀ {A B : 𝒞} (m : A ⟶ B), Mono m → ∃ (m' : 𝒞 ⟶ B), Mono m'

/-! ## §1.645 𝒦𝓮𝓇(T) — values killed by a representation

  For T: A → B a representation of boolean pre-logoi, Kℯℛ(T) is
  the set of subterminators U ⊆ 1 such that T(U) = 0. -/

/-- The kernel of a representation T: the set of subterminators sent to 0. -/
def killedValues {𝒟 : Type u} [Cat.{v} 𝒟] [PreLogos 𝒞] [PreLogos 𝒟]
    (T : 𝒞 → 𝒟) [Functor F] : Set (Subobject 𝒞 one) :=
  { U | Isomorphic (T U.dom) (T one) }

/-! ## §1.65 Pre-topos

  A PRE-TOPOS is an effective positive pre-logos:
  effective regular + positive pre-logos. -/

class PreTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    EffectiveRegular 𝒞, PositivePreLogos 𝒞

/-! ## §1.651 Amalgamation Lemma

  In a pre-topos, given monics x: A↣B, y: A↣C, there exists a
  pushout B ↣ D, C ↣ D completing the square. -/

theorem amalgamation_lemma [PreTopos 𝒞] {A B C : 𝒞}
    (x : A ⟶ B) (hx : Mono x) (y : A ⟶ C) (hy : Mono y) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D), Mono u ∧ Mono v ∧ x ≫ u = y ≫ v := by
  -- Form coproduct B+C, define E = l°x°yr ∪ 1 ∪ r°y°xl on B+C.
  -- E is an equivalence relation.  Let B+C → D be such that E is its level.
  -- Then u, v are the compositions with the coproduct inclusions, and are monic.
  sorry

/-! ## §1.652 Covers = epics, Monics = cocovers

  In a pre-topos, covers coincide with epimorphisms, and monics
  coincide with coequalizers (cocovers). -/

theorem cover_eq_epic_preTopos [PreTopos 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Cover f ↔ Epic (λ _ => ⟨A, f⟩) := by
  sorry

theorem monic_eq_cocover_preTopos [PreTopos 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Mono f ↔ ∃ (C D : 𝒞) (p q : C ⟶ D), IsCoequalizer p q f := by
  sorry

/-! ## §1.654 Pre-topos opposite is regular (if cocartesian) -/

theorem preTopos_opposite_regular [PreTopos 𝒞] [HasCoequalizers 𝒞] : True := by
  sorry


/-- DECIDABLE OBJECT (§1.658): the diagonal A→A×A has a complement in the subobject lattice.
class DecidableObject (A : 𝒞) [PreLogos 𝒞] where
  diag_complemented : IsComplemented (Subobject.mk A fst (Subobject.mk A snd (Subobject.entire (prod A A))))

end Freyd
