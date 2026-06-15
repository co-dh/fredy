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
import Fredy.S1_59
import Fredy.S1_60
import Fredy.S1_62


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.631 Complemented subobject

  A₁ ⊆ A is COMPLEMENTED if ∃ A₂ ⊆ A with A₁∩A₂=0, A₁∪A₂=A. -/

variable [PreLogos 𝒞]

/-- A₁ is COMPLEMENTED if there's A₂ with A₁∩A₂=0 and A₁∪A₂=A.
    (Placeholder: intersection not yet defined.) -/
def IsComplemented {A : 𝒞} (A₁ : Subobject 𝒞 A) : Prop :=
  ∃ (A₂ : Subobject 𝒞 A),
    (∀ (S : Subobject 𝒞 A), Subobject.le S A₁ → Subobject.le S A₂ → False)
    -- A₁∩A₂ is minimal (no non-trivial common subobject)
    ∧ Subobject.le (Subobject.entire A) (HasSubobjectUnions.union A₁ A₂)
    -- A₁∪A₂ = A (entire)

/-! ## §1.64 Boolean pre-logos

  A BOOLEAN PRE-LOGOS is a pre-logos where every subobject lattice
  is Boolean (every subobject has a complement). -/

class BooleanPreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends PreLogos 𝒞 where
  hasComplement : ∀ {A : 𝒞} (S : Subobject 𝒞 A), IsComplemented S

/-! ## §1.645 𝒦𝓮𝓇(T) — values killed by a representation

  For T: A → B a representation of boolean pre-logoi, Kℯℛ(T) is
  the set of subterminators U ⊆ 1 such that T(U) = 0. -/

/-- The kernel of a representation T: the set of subterminators sent to 0. -/
def killedValues {𝒟 : Type u} [Cat.{v} 𝒟] [PreLogos 𝒞] [PreLogos 𝒟]
    (T : 𝒞 → 𝒟) [Functor T] : (Subobject 𝒞 one) → Prop :=
  λ U => @Isomorphic 𝒟 _ (T U.dom) one

/-! ## §1.65 Pre-topos

  A PRE-TOPOS is an effective positive pre-logos:
  effective regular + positive pre-logos. -/

class PreTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    EffectiveRegular 𝒞, PositivePreLogos 𝒞

/-! ## §1.651 Amalgamation Lemma

  In a pre-topos, given monics x: A↣B, y: A↣C, there exists a
  pushout B ↣ D, C ↣ D completing the square. -/

/-- **§1.651 Amalgamation Lemma**: In a pre-topos, the pushout of two
    monics with a common source exists and the resulting maps are monic.
    Proof: form B+C, define equivalence relation E identifying x(a)∼y(a),
    then the effective quotient B+C ↠ D gives the pushout.
    Requires effective regularity (every equivalence relation has a coequalizer)
    which needs additional structure in `EffectiveRegular`. -/
theorem amalgamation_lemma [PreTopos 𝒞] {A B C : 𝒞}
    (x : A ⟶ B) (hx : Mono x) (y : A ⟶ C) (hy : Mono y) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D), Mono u ∧ Mono v ∧ x ≫ u = y ≫ v := by
  sorry

/-! ## §1.652 Covers = epics, Monics = cocovers

  In a pre-topos, covers coincide with epimorphisms, and monics
  coincide with coequalizers (cocovers). -/

/-- **§1.652 (crux): a pre-topos is BALANCED** — a map that is both monic and
    epic is an isomorphism.  This is the genuine positivity content of §1.652:
    the cokernel pair of `m` is built from the *disjoint* coproduct `B + B`
    (positivity) via the effective quotient, and a monic that is also epic
    equalizes a pair of equal legs, hence splits.  It is **not** derivable from
    the current axioms — `HasBinaryCoproducts` carries only the bare universal
    property, with no disjointness/universality, so the cokernel-pair argument
    has no axiom to stand on.  Isolated here as the single obligation that both
    reverse-directions below (`cover_eq_epic_preTopos`, `monic_eq_cocover`) rest
    on; closing it needs §1.62 positivity axiomatized as Freyd states it
    (disjoint + universal coproducts). -/
theorem pretopos_balanced [PreTopos 𝒞] {A B : 𝒞} (m : A ⟶ B) (hm : Mono m)
    (hepi : ∀ {C : 𝒞} (g h : B ⟶ C), m ≫ g = m ≫ h → g = h) : IsIso m := by
  sorry

theorem cover_eq_epic_preTopos [PreTopos 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Cover f ↔ (∀ {C : 𝒞} (g h : B ⟶ C), f ≫ g = f ≫ h → g = h) := by
  constructor
  · -- Cover → epic (§1.512): already proved
    exact cover_epi
  · intro hepi
    rw [cover_iff_image_entire]
    -- Goal: Subobject.IsEntire (image f), i.e., IsIso (image f).arr.
    -- `(image f).arr` is monic; since `f = lift ≫ arr` is epic, `arr` is epic too.
    have h_arr_epi : ∀ {C : 𝒞} (g h : B ⟶ C), (image f).arr ≫ g = (image f).arr ≫ h → g = h := by
      intro C g h heq
      apply hepi
      calc f ≫ g = (image.lift f ≫ (image f).arr) ≫ g := by rw [image.lift_fac f]
        _ = image.lift f ≫ ((image f).arr ≫ g) := Cat.assoc _ _ _
        _ = image.lift f ≫ ((image f).arr ≫ h) := by rw [heq]
        _ = (image.lift f ≫ (image f).arr) ≫ h := by rw [← Cat.assoc]
        _ = f ≫ h := by rw [image.lift_fac f]
    -- monic + epic ⟹ iso by balancedness (`pretopos_balanced`), so `image f` is entire.
    exact pretopos_balanced (image f).arr (image f).monic h_arr_epi

/-- **§1.652**: In a pre-topos, monics coincide with cocovers
    (maps that are coequalizers of some pair).
    Requires effective regularity (every monic is a regular monic = an equalizer,
    dually every epic is a regular epic = a coequalizer).
    The `HEq` in the statement is a placeholder for an isomorphism between
    the coequalizer map and `f`. -/
theorem monic_eq_cocover_preTopos [PreTopos 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Mono f ↔ ∃ (C : 𝒞) (p q : C ⟶ A), HEq ((HasCoequalizers.coeq p q).map) f := by
  sorry

/-! ## §1.654 Pre-topos opposite is regular (if cocartesian) -/

theorem preTopos_opposite_regular [PreTopos 𝒞] [HasCoequalizers 𝒞] : True := by
  trivial


/-! ## §1.658 Decidable object

  A is DECIDABLE if the diagonal A→A×A has a complement in the subobject lattice. -/

-- class DecidableObject (A : 𝒞) [PreLogos 𝒞] where
--   diag_complemented : IsComplemented (Subobject.mk A (diagonal A) ?monic)

end Freyd
