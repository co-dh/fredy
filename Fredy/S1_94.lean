/-
  Freyd & Scedrov, *Categories and Allegories* §1.94  Internally defined intersection/union.

  §1.94  SUBOBJECTS NAMED BY F (for F ⊆ [A]); INTERNALLY DEFINED INTERSECTION ∩F.
  §1.942 NAME OF A' (adjoint name 'A' : 1 → Ω^A of χ_{A'}).
  §1.943 ∩F is below every subobject named by F; if F well-pointed, ∩F is the glb.
  §1.944 A topos has a strict coterminator.
  §1.945 A topos is regular.
  §1.946 A topos is a logos.
  §1.949 INTERNALLY DEFINED UNION ∪F.

  NOTE: S1_70 (Logos) has a pre-existing build error in `logos_implies_preLogos`
  (missing PreLogos fields). We duplicate the `HasRightAdjointImage'` and `Logos'`
  class definitions here so this file compiles independently.
-/

import Fredy.S1_1
import Fredy.S1_9
import Fredy.S1_85
import Fredy.S1_92
import Fredy.S1_52
import Fredy.S1_58
import Fredy.S1_60

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.70  Local re-statement of Logos (S1_70 has a build error)

  A LOGOS (§1.7) is a regular category where the inverse-image f# has a
  right adjoint f## for every morphism f : A → B.  We duplicate the class
  here because S1_70.lean currently fails to build. -/

/-- f## is the right adjoint of f# : 𝒫(B) → 𝒫(A). (Local copy from S1_70.) -/
class HasRightAdjointImage' (𝒞 : Type u) [Cat.{v} 𝒞]
    extends HasImages 𝒞, HasPullbacks 𝒞 where
  rightAdj : ∀ {A B : 𝒞} (f : A ⟶ B), Subobject 𝒞 A → Subobject 𝒞 B
  adjunction : ∀ {A B : 𝒞} (f : A ⟶ B) (B' : Subobject 𝒞 B) (A' : Subobject 𝒞 A),
    Subobject.le (InverseImage f B') A' ↔ Subobject.le B' (rightAdj f A')

/-- A LOGOS (§1.7): regular + subobject lattices + right adjoint to f#.
    (Local copy; canonical definition is in S1_70.) -/
class Logos' (𝒞 : Type u) [Cat.{v} 𝒞] extends
    RegularCategory 𝒞, HasSubobjectUnions 𝒞, HasRightAdjointImage' 𝒞

/-! ## §1.94  Power object [A] and families named by F

  In a topos the POWER OBJECT [A] is the exponential Ω^A (§1.92).
  A subobject A' ↣ A is NAMED BY F ⊆ [A] if its name 'A'' ≤ F (§1.942).
  The INTERNALLY DEFINED INTERSECTION ∩F is built by pulling back
  `true : 1 → Ω` along the membership evaluation map (§1.94). -/

/-- The POWER OBJECT [A] = Ω^A (§1.92). -/
abbrev powObj (A : 𝒞) : 𝒞 := omega (𝒞 := 𝒞) ^^ A

/-! ## §1.942  Name of a subobject

  For A' ↣ A with characteristic map χ_{A'} : A → Ω, the NAME OF A',
  written 'A'', is curry(χ_{A'}) : 1 → Ω^A = [A].  The adjunction
  prod A 1 ≅ A → Ω^A gives 'A'' = curry(fst ≫ χ_{A'}) : 1 → [A]. -/

/-- The NAME 'A'' : 1 → [A] of the monic m : A' → A (§1.942).
    curry(fst ≫ χ_m) : one → Ω^A, where fst : prod A one → A. -/
noncomputable def nameOf {A A' : 𝒞} (m : A' ⟶ A) (hm : Mono m) : one ⟶ powObj A :=
  curry (fst ≫ classify m hm)

/-- A' is NAMED BY F ⊆ [A] if 'A'' ∈ F, i.e. 'A'' factors through F (§1.942). -/
def NamedBy {A : 𝒞} (A' : Subobject 𝒞 A) (F : Subobject 𝒞 (powObj A)) : Prop :=
  ∃ h : one ⟶ F.dom, h ≫ F.arr = nameOf A'.arr A'.monic

/-! ## §1.94  Internally defined intersection ∩F

  The construction from the book: pull back `true : 1 → Ω` along the
  membership evaluation map A → Ω induced by F.  When F ⊆ [A] is presented
  as a subobject F ↣ [A], its "adjoint" 1 → [[A]] is its name.  For the
  case where F is given by a global element `F_name : 1 → [A]` (i.e. F
  is the singleton subobject of [A] containing F_name), the membership map is

      A ──pair(id,term≫F_name)──→ A × [A] ──eval──→ Ω.

  and ∩F is the pullback of true along this map. -/

/-- The membership test A → Ω for a global element F_name : 1 → [A].
    Evaluates F_name at each a : A via `eval ∘ ⟨id_A, term_A ≫ F_name⟩`. -/
noncomputable def membershipMap {A : 𝒞} (F_name : one ⟶ powObj A) : A ⟶ omega (𝒞 := 𝒞) :=
  pair (Cat.id A) (term A ≫ F_name) ≫ eval_exp A (omega (𝒞 := 𝒞))

/-- **§1.94**: INTERNALLY DEFINED INTERSECTION ∩F for a global element F_name : 1 → [A].
    Constructed as the pullback of true : 1 → Ω along membershipMap F_name. -/
noncomputable def interIntersection {A : 𝒞} (F_name : one ⟶ powObj A) : Subobject 𝒞 A :=
  InverseImage (membershipMap F_name) ⟨one, true (𝒞 := 𝒞), true_monic⟩

/-! ## §1.949  Internally defined union ∪F

  Given F ⊆ [A], the INTERNALLY DEFINED UNION ∪F is the direct image of
  ε_F : prod F.dom A → Ω, where ε_F sends (f, a) to eval(a, f).
  In terms of subobjects of Ω: ∪F is the image of the evaluation
  restricted to F × A ↣ [A] × A.  Since A is the "base" and the
  target of evaluation is Ω, we record ∪F as the image of ε_F as a
  subobject of Ω.  A' is in ∪F iff some member of F names an A'' ⊆ A'. -/

/-- **§1.949**: INTERNALLY DEFINED UNION ∪F for F ⊆ [A].
    The "membership characteristic" of ∪F: subobject of Ω equal to the
    image of `pair snd (fst ≫ F.arr) ≫ eval_exp A Ω : prod F.dom A → Ω`.
    This says a ∈ ∪F iff ∃ f ∈ F, a ∈ f (i.e. eval(a, f) = true). -/
noncomputable def interUnion [HasImages 𝒞] {A : 𝒞} (F : Subobject 𝒞 (powObj A)) :
    Subobject 𝒞 (omega (𝒞 := 𝒞)) :=
  image (pair (snd (A := F.dom) (B := A)) (fst ≫ F.arr) ≫
    eval_exp A (omega (𝒞 := 𝒞)))

/-! ## §1.943  ∩F is a lower bound; glb when F is well-pointed -/

/-- **§1.943** (part 1): ∩F is below every subobject A' named by F.
    For A' ↣ A with 'A'' ∈ F_name (i.e. nameOf A'.arr A'.monic = F_name),
    we have ∩F ≤ A'.

    Proof (§1.943): 'A'' ∈ F means the membership map for A' factors through
    true : 1 → Ω, so ∩F = pullback(true along membershipMap) ≤ A'. -/
theorem inter_le_named {A : 𝒞} (F_name : one ⟶ powObj A)
    (A' : Subobject 𝒞 A)
    (_hA' : nameOf A'.arr A'.monic = F_name) :
    Subobject.le (interIntersection F_name) A' := by
  sorry

/-- **§1.943** (part 2, well-pointed case): If the points of F (i.e. maps 1 → F.dom)
    are jointly epic, then ∩F is the greatest lower bound of subobjects named by F.
    A map B → A factors through ∩F iff it factors through every A' named by F.

    Proof (§1.943): Well-pointedness makes {1_F} jointly epic; Ω(−) contravariant
    with right adjoint carries epic families to monic families; then §1.942 closes. -/
theorem inter_is_glb {A : 𝒞} (F : Subobject 𝒞 (powObj A))
    (_hF : WellPointed F.dom)
    (L : Subobject 𝒞 A)
    (_hL : ∀ A' : Subobject 𝒞 A, NamedBy A' F → Subobject.le L A') :
    ∀ x : one ⟶ F.dom,
        Subobject.le L (interIntersection (x ≫ F.arr)) := by
  sorry

/-! ## §1.944  A topos has a strict coterminator

  A STRICT COTERMINATOR is an initial object 0 such that every morphism
  into 0 is an isomorphism (§1.58).  In a topos, ∩∅ (the intersection over
  the empty family over 1) is a minimal subobject of 1 and is strict. -/

/-- **§1.944**: A topos has a strict coterminator.
    The minimal subobject of 1 (= ∩∅) is initial and strict: any B with
    a map B → ∩∅ has no proper subobjects, hence B ≅ ∩∅. -/
theorem topos_has_strict_coterminator : Nonempty (HasCoterminator 𝒞) := by
  sorry

/-- **§1.945**: A topos is regular — images exist and pullbacks transfer covers.
    For f : A → B let F = {B' ↣ B | f factors through B'}; then ∩F is the image
    of f (§1.943 + capitalization lemma §1.54). -/
theorem topos_is_regular : Nonempty (RegularCategory 𝒞) := by
  sorry

/-- **§1.946**: A topos is a logos — a regular category in which every inverse-image
    functor f# : 𝒫(B) → 𝒫(A) has a right adjoint f## (§1.946).
    Binary unions: A₁ ∪ A₂ = ∩{B' | A₁ ⊆ B' ∧ A₂ ⊆ B'} via §1.943.
    (Uses local Logos'; canonical Logos is in S1_70 which has a build error.) -/
theorem topos_is_logos : Nonempty (Logos' 𝒞) := by
  sorry

end Freyd
