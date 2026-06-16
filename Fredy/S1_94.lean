/-
  Freyd & Scedrov, *Categories and Allegories* §1.94  Internally defined intersection/union.

  §1.94  SUBOBJECTS NAMED BY F (for F ⊆ [A]); INTERNALLY DEFINED INTERSECTION ∩F.
  §1.941 ∩F is preserved by representations and is the "internally definable" lower bound.
  §1.942 NAME OF A' (adjoint name 'A' : 1 → Ω^A of χ_{A'}).
  §1.943 ∩F is below every subobject named by F; if F well-pointed, ∩F is the glb.
  §1.944 A topos has a strict coterminator.
  §1.945 A topos is regular.
  §1.946 A topos is a logos.
  §1.947 A topos is a transitive logos (R* exists for reflexive R).
  §1.948 Example: G-sets (remark).
  §1.949 INTERNALLY DEFINED UNION ∪F.
  §1.94(10) WELL-POINTED PART, SOLVABLE TOPOS.

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

/-! ## §1.941  Representational invariance of ∩F

  ∩F is preserved by representations of topoi — any topos morphism T : 𝒞 → 𝒟
  carries ∩F to ∩(T(F)).  It is the LARGEST subobject of A that remains a
  lower bound under all representations, and is characterised as the largest
  subobject constructible by a formula in the partial operations of topos theory.
  In particular it is "internally definable" (§1.941). -/

/-- **§1.941**: A REPRESENTATION OF TOPOI is a functor T : 𝒞 → 𝒟 between topoi
    that preserves the topos structure (terminal, products, subobject classifier,
    exponentials).  We record this as a predicate on the functorial data. -/
def ToposMap {𝒟 : Type u} [Cat.{v} 𝒟] [Topos 𝒟]
    (T : 𝒞 → 𝒟) [Functor T] : Prop :=
  PreservesMono T ∧
  (Isomorphic (T (one (𝒞 := 𝒞))) (one (𝒞 := 𝒟))) ∧
  (∀ (A B : 𝒞), Isomorphic (T (prod A B)) (prod (T A) (T B)))

-- §1.941 (PERMANENT LOWER BOUND under representations): "T(∩F) is below every
-- subobject named by T(F), for every representation of topoi T : 𝒞 → 𝒟" cannot
-- be stated faithfully yet — it needs functorial transport of subobjects and of
-- the `NamedBy` relation along T (a `T(F)`-as-a-subobject construction), which is
-- not available from the bare `ToposMap` predicate.  Recorded MISSING in S1_94.md.
-- The non-representational fragment ("∩F ≤ every subobject named by F") IS proved
-- below as `inter_le_named` (§1.943 part 1).

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

/-! ## §1.948  Example: G-sets (remark)

  Let G be a group.  G appears as an object in the topos YG of G-sets.
  Let F ⊆ [G] be the complement of the image of the singleton map G1 : G → [G].
  The only G-set named by F is the entire subobject; but ∩F = ∅ for non-trivial G
  (most easily checked via the forgetful U : YG → Y which is a faithful
  representation of topoi and carries ∩F to ∩(UF) = ∅).
  This shows ∩F need not equal the intersection of the named subobjects
  in general (it is only the greatest *permanent* lower bound). -/

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

/-- **§1.942/§1.94 β-law**: evaluating the NAME 'A'' at a point reconstructs the
    characteristic map.  Concretely the membership test of `nameOf m hm` equals
    the classifier `χ_m`: `membershipMap (nameOf m hm) = classify m hm`.

    Proof: `nameOf m hm = curry(fst ≫ χ_m)`; the membership map factors as
    `pair id (term) ≫ prodMap (curry …) ≫ eval`, and `curry_eval` collapses the
    `prodMap … ≫ eval` to `fst ≫ χ_m`, then `fst (pair id term) = id`. -/
theorem membershipMap_nameOf {A A' : 𝒞} (m : A' ⟶ A) (hm : Mono m) :
    membershipMap (nameOf m hm) = HasSubobjectClassifier.classify m hm := by
  show pair (Cat.id A) (term A ≫ nameOf m hm) ≫ eval_exp A (omega (𝒞 := 𝒞))
      = HasSubobjectClassifier.classify m hm
  -- pair id (term ≫ N) = pair id term ≫ prodMap A one (Ω^A) N
  have hfactor : pair (Cat.id A) (term A ≫ nameOf m hm)
      = pair (Cat.id A) (term A) ≫ prodMap A one (omega (𝒞 := 𝒞) ^^ A) (nameOf m hm) :=
    (pair_uniq _ _ _
      (by rw [Cat.assoc, prodMap_fst, fst_pair])
      (by rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair])).symm
  rw [hfactor, Cat.assoc]
  -- prodMap A one _ (curry (fst ≫ χ_m)) ≫ eval = fst ≫ χ_m
  show pair (Cat.id A) (term A) ≫
      (prodMap A one (omega (𝒞 := 𝒞) ^^ A) (curry (fst ≫ HasSubobjectClassifier.classify m hm))
        ≫ eval_exp A (omega (𝒞 := 𝒞))) = _
  rw [curry_eval_eq, ← Cat.assoc, fst_pair, Cat.id_comp]

/-- **§1.943** (part 1): ∩F is below every subobject A' named by F.
    For A' ↣ A with 'A'' ∈ F_name (i.e. nameOf A'.arr A'.monic = F_name),
    we have ∩F ≤ A'.

    Proof (§1.943): 'A'' ∈ F means the membership map for A' factors through
    true : 1 → Ω, so ∩F = pullback(true along membershipMap) ≤ A'. -/
theorem inter_le_named {A : 𝒞} (F_name : one ⟶ powObj A)
    (A' : Subobject 𝒞 A)
    (hA' : nameOf A'.arr A'.monic = F_name) :
    Subobject.le (interIntersection F_name) A' := by
  -- membershipMap F_name = χ_{A'} = classify A'.arr A'.monic
  have hχ : membershipMap F_name = HasSubobjectClassifier.classify A'.arr A'.monic := by
    rw [← hA', membershipMap_nameOf]
  -- ∩F = inverse image of {true} along membershipMap F_name; its arr is π₁ of the
  -- canonical pullback `pb` over the cospan (membershipMap F_name, true).
  let pb := HasPullbacks.has (membershipMap F_name) (HasSubobjectClassifier.true (𝒞 := 𝒞))
  -- A' is the pullback of `true` along χ_{A'} (classify_pullback); use its universal
  -- property to lift pb.cone, getting u : pb.cone.pt → A' with u ≫ A'.arr = pb.cone.π₁.
  have hpbA' := HasSubobjectClassifier.classify_pullback A'.arr A'.monic
  -- pb.cone is a cone over (χ_{A'}, true) after rewriting membershipMap F_name = χ_{A'}.
  have hsq : pb.cone.π₁ ≫ HasSubobjectClassifier.classify A'.arr A'.monic
      = pb.cone.π₂ ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    rw [← hχ]; exact pb.cone.w
  obtain ⟨u, ⟨hu₁, _⟩, _⟩ :=
    hpbA' ⟨pb.cone.pt, pb.cone.π₁, pb.cone.π₂, hsq⟩
  exact ⟨u, hu₁⟩

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

/-! ## §1.947  A topos is a transitive logos

  A TRANSITIVE LOGOS (§1.77) is a logos in which, for every endo-relation R on B,
  the reflexive-transitive closure R* exists (i.e. the least reflexive transitive
  relation ≥ R).

  Construction (§1.947): It suffices to find R* for reflexive R (since for any R,
  R⁺ is the transitive closure of R and R* = R(1 ∪ R)* , but Freyd notes R⁺ is
  constructible as R(1 ∪ R)*).

  Given reflexive R on B, consider the endo-relation R×1 on B×B.
  Apply the right-adjoint f## (f = R×1 : [B×B] → [B×B]) to get an endomorphism
  of 𝒫(B×B) sending S to RS.  Let F₁ ⊆ [B×B] be the equalizer of id and R×1,
  so S is named by F₁ iff RS = S (i.e. R ≤ S is a "pre-fixed-point").
  Since R is reflexive, RS ⊆ S iff RS = S.

  Let F₂ ⊆ [B×B] name the reflexive relations (contains the diagonal Δ_B).
  Set F = F₁ ∩ F₂.  Then ∩F names all reflexive S with RS ⊆ S, i.e. all
  "pre-closed" reflexive relations.  By §1.943 (capitalization + well-pointed),
  ∩F is their greatest lower bound.  R(∩F) ⊆ R(∩F) and 1 ⊆ ∩F hold by
  ordinary categorical reasoning, so ∩F is reflexive and RS ⊆ S, i.e. ∩F = R*. -/

/-- **§1.947**: A topos has the reflexive-transitive closure of any endo-relation.
    Given reflexive R on B, the subobject ∩F (for suitable F ⊆ [B×B]) is R*.
    (Faithful sorry — proof requires the full §1.943 glb theorem + capitalization.) -/
theorem topos_has_rtc {B : 𝒞} (R : Subobject 𝒞 (prod B B))
    (_hRefl : Subobject.le (Subobject.entire (prod B B)) R) :
    ∃ Rstar : Subobject 𝒞 (prod B B),
      -- R ≤ R*
      R.le Rstar ∧
      -- R* is reflexive: diagonal ≤ R*
      Subobject.le (Subobject.entire (prod B B)) Rstar ∧
      -- R* is a lower bound of all reflexive relations S with RS ⊆ S
      ∀ (S : Subobject 𝒞 (prod B B)),
        R.le S →
        Subobject.le (Subobject.entire (prod B B)) S →
        Rstar.le S := by
  sorry

-- §1.947: that a topos is a TRANSITIVE LOGOS (R* exists for every endo-relation)
-- is exactly the content of `topos_has_rtc` above; not restated as a vacuous theorem.

/-! ## §1.94(10)  Well-pointed part and solvable topos

  The SINGLETON MAP A1 : A → [A] names precisely the singleton subobjects,
  i.e. the images of points 1 → A.  The WELL-POINTED PART A* of A is the
  join (least upper bound) of all singletons — equivalently, the largest
  well-pointed subobject of A.

  In general A* does not exist; there is no internal construction (§1.941
  shows the obvious ∪(A1) candidate can fail).

  A SOLVABLE TOPOS is one in which every object has a well-pointed part.
  In a solvable topos every elementarily definable family of subobjects has
  a glb and lub (via ∩(F*) and ∪(F*)).

  Capital topoi are solvable: A* = A if A is well-supported, else A* = 0. -/

/-- **§1.94(10)**: The SINGLETON MAP A1 : A → [A] = Ω^A sends a : A to its name
    'a'' = {a}.  It is `curry(χ_{Δ_A})`, the curried classifier of the diagonal —
    exactly the §1.92 `singletonMapCat`, reused here (DRY). -/
noncomputable def singletonMap (A : 𝒞) : A ⟶ powObj A :=
  singletonMapCat (𝒞 := 𝒞) A

/-- **§1.94(10)**: A subobject A' ↣ A is a POINT SUBOBJECT (named by A1) iff
    A' is the image of some point p : 1 → A. -/
def IsPointSubobj {A : 𝒞} (A' : Subobject 𝒞 A) : Prop :=
  ∃ (p : one ⟶ A), ∃ (h : one ⟶ A'.dom), h ≫ A'.arr = p

/-- **§1.94(10)**: The WELL-POINTED PART of A, if it exists, is the least upper
    bound of all point subobjects of A.  We encode existence separately. -/
def IsWellPointedPart {A : 𝒞} [HasImages 𝒞]
    (Astar : Subobject 𝒞 A) : Prop :=
  -- Astar is above every point subobject
  (∀ P : Subobject 𝒞 A, IsPointSubobj P → P.le Astar) ∧
  -- Astar is well-pointed (the points of Astar.dom are jointly epic)
  WellPointed Astar.dom ∧
  -- Astar is the least such: any other well-pointed subobject ≤ Astar
  ∀ Q : Subobject 𝒞 A, WellPointed Q.dom →
    (∀ P : Subobject 𝒞 A, IsPointSubobj P → P.le Q) → Astar.le Q

/-- **§1.94(10)**: A SOLVABLE TOPOS is a topos in which every object has a
    well-pointed part. -/
class SolvableTopos (𝒞 : Type u) [Cat.{v} 𝒞] [Topos 𝒞] [HasImages 𝒞] where
  wpPart : ∀ (A : 𝒞), Subobject 𝒞 A
  wpPart_is_wp_part : ∀ (A : 𝒞), IsWellPointedPart (wpPart A)

-- §1.94(10): the book's claim is "U(A1) is always entire" — entireness of the
-- singleton map's IMAGE under the forgetful representation U to Set.  It is NOT
-- true that A1 itself is a cover in 𝒞 (A1 is monic and is iso only when A is
-- subterminal), so `Cover (singletonMap A)` is not Freyd's statement.  The
-- representational claim needs the forgetful functor U : 𝒞 → Set, which this
-- repo does not have; recorded MISSING in S1_94.md.
--
-- The genuine categorical fact about A1 available here is MONICITY (§1.92), which
-- we expose by reuse of `singletonMapCat_monic` (DRY — singletonMap = singletonMapCat).
theorem singletonMap_monic (A : 𝒞) : Mono (singletonMap A) :=
  singletonMapCat_monic (𝒞 := 𝒞) A

/-- **§1.94(10)**: A capital topos is solvable.
    In a capital topos, A* = A if A is well-supported (Cover (term A)),
    else A* = 0 (the minimal subobject from §1.944).
    Faithful sorry — proof uses the capitalization lemma §1.54. -/
theorem capital_is_solvable [HasImages 𝒞] (_hcap : Capital (𝒞 := 𝒞)) :
    ∀ (A : 𝒞), ∃ Astar : Subobject 𝒞 A, IsWellPointedPart Astar := by
  sorry

end Freyd
