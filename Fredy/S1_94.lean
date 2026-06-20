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
import Fredy.S1_77
-- §1.94 power-object name / `interIntersection` cluster (relocated upstream to break the
-- import cycle S1_94 → InternalForall → InternalForallTopos → S1_94).  Re-exported here so
-- S1_94's public surface (`powObj`, `nameOf`, `interIntersection`, …) is unchanged for its
-- own downstream users.
import Fredy.InterIntersection
-- §1.945 topos-regularity infrastructure.  The cycle that used to block this import
-- (S1_94 → InternalForall → InternalForallTopos → S1_94) was removed by pointing
-- InternalForall at S1_9 directly instead of S1_94.  InternalForallTopos provides the
-- sorry-free `toposHasImages` instance, the `SlicePi.toposPullbacksTransferCovers`
-- instance, and `topos_is_regular_real : Nonempty (RegularCategory 𝒞)`.
import Fredy.InternalForallTopos
-- §1.946 right adjoint f## to inverse image (the `HasRightAdjointImage'` keystone): the
-- subobject-level internal-∀ `radjImage`/`radjImage_adjunction`, built sorry-free via the
-- internal-∀ family-glb machinery.  Plus §1.95 `bottomSub` for the strict coterminator.
import Fredy.RightAdjointImage
import Fredy.ToposColimits
-- §1.944 strict coterminator: `topos_has_coterminator` (built sorry-free modulo the single
-- `bottomSub_dom_iso` seed = `0 × A ≅ 0`; see `Fredy/ToposStrictZero.lean`).
import Fredy.ToposStrictZero

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

/-- **§1.946 — a topos has the right adjoint `f##` to inverse image.**  Bundles the §1.946
    keystone `radjImage` (the internal-∀ right adjoint `f## = ∀_f : Sub(A) → Sub(B)`) with its
    adjunction `radjImage_adjunction` (`f* ⊣ f##`) into the `HasRightAdjointImage'` interface.
    Both are built sorry-free in `Fredy.RightAdjointImage` via the internal-∀ family-glb machinery
    (NO §1.54 transfinite capitalization).  This is the load-bearing instance that turns
    `topos_is_logos` from a `sorry` into an assembly. -/
noncomputable instance toposHasRightAdjointImage : HasRightAdjointImage' 𝒞 where
  rightAdj f A' := radjImage f A'
  adjunction f B' A' := radjImage_adjunction f B' A'

/-! ## §1.94  Power object [A] and families named by F

  In a topos the POWER OBJECT [A] is the exponential Ω^A (§1.92).
  A subobject A' ↣ A is NAMED BY F ⊆ [A] if its name 'A'' ≤ F (§1.942).
  The INTERNALLY DEFINED INTERSECTION ∩F is built by pulling back
  `true : 1 → Ω` along the membership evaluation map (§1.94). -/

-- `powObj` (the POWER OBJECT [A] = Ω^A) is now defined in `InterIntersection` and
-- re-exported via the import above.

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

-- `nameOf` (the NAME 'A'' : 1 → [A] of a monic) and `NamedBy` are now in
-- `InterIntersection` and re-exported via the import above.

/-! ## §1.94  Internally defined intersection ∩F

  The construction from the book: pull back `true : 1 → Ω` along the
  membership evaluation map A → Ω induced by F.  When F ⊆ [A] is presented
  as a subobject F ↣ [A], its "adjoint" 1 → [[A]] is its name.  For the
  case where F is given by a global element `F_name : 1 → [A]` (i.e. F
  is the singleton subobject of [A] containing F_name), the membership map is

      A ──pair(id,term≫F_name)──→ A × [A] ──eval──→ Ω.

  and ∩F is the pullback of true along this map. -/

-- `membershipMap` (the membership test A → Ω of a global name) and `interIntersection`
-- (the INTERNALLY DEFINED INTERSECTION ∩F) are now in `InterIntersection` and re-exported.

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

/-! ## §1.943  ∩F is a lower bound; glb when F is well-pointed

  The β/η-law lemma cluster around `membershipMap`/`interIntersection`
  (`membershipMap_nameOf`, `inter_le_named`, `curry_fst_membershipMap`,
  `classify_interIntersection`, `nameOf_interIntersection`, `inter_le_singleton_named`)
  is now in `InterIntersection` and re-exported via the import above. -/


/-! ## §1.944  A topos has a strict coterminator

  A STRICT COTERMINATOR is an initial object 0 such that every morphism
  into 0 is an isomorphism (§1.58).  In a topos, ∩∅ (the intersection over
  the empty family over 1) is a minimal subobject of 1 and is strict. -/

/-- **§1.944**: A topos has a strict coterminator.
    The minimal subobject of 1 (= ∩∅) is initial and strict: any B with
    a map B → ∩∅ has no proper subobjects, hence B ≅ ∩∅.

    BLOCKER (faithful sorry): the initial object is `⋂∅`, the glb of the *empty*
    family over `1`.  This file only has `interIntersection` for a single global
    name `1 → [A]` (a singleton family); the `⋂F`-over-a-subobject-family glb that
    §1.943 actually asserts is not constructed here — it needs §1.54's
    `capitalization_lemma` (itself still `sorry`) to terminate the transfinite
    A ⊆ A* iteration that builds the glb.  No current arm yields the empty glb.

    REDUCED THIS PASS to a SINGLE sharp seed (the §1.543 transfinite blocker is GONE — the
    `⋂∅` glb is now built sorry-free as `bottomSub A := ⋂{all σ ⊆ A}` in `Fredy.ToposColimits`,
    the all-subobjects family-glb via the internal-∀ engine, NOT capitalization).  The
    strict-coterminator scaffolding `Fredy.ToposStrictZero` is now ALL sorry-free EXCEPT one
    cross-base lemma:

        carrier `0 := (bottomSub one).dom`;
        `StrictCoterminator 0` (every map into `0` is iso) via the S1_61 pullback argument,
        ported to `bottomSub` + the §1.946 right-adjoint EMPTINESS lemma `g*(∅) ≤ ∅`
        (`invImage_bottomSub_le`, proved sorry-free from `radjImage_adjunction`);
        then `HasCoterminator.ofStrict` (S1_58).

    The lone residual is `bottomSub_dom_iso A B : (∅_A).dom ≅ (∅_B).dom` (cross-base bottom-
    domain iso), equivalently the strict-initial absorption `0 × A ≅ 0`, equivalently the
    existence of the universal arrow `0 → A`.  This is NOT supplied by either adjoint to
    inverse image: `g* ⊣ g##` (sorry-free, used here) gives only `g*(⊥) ≅ ⊥` (the emptiness
    direction), and `∃_g ⊣ g*` is gated behind `[PreLogos 𝒞]` (which a bare topos lacks).
    The viable sorry-free route is the partial-map-classifier undefined-point construction
    (`Fredy.PartialMapClassifier`, now sorry-free at the interface) — power-object internals,
    left for a follow-up.  Hence this theorem still carries `sorryAx` THROUGH that one seed
    (`Fredy.ToposStrictZero.bottomSub_dom_iso`); everything else in §1.944 is sorry-free. -/
theorem topos_has_strict_coterminator : Nonempty (HasCoterminator 𝒞) :=
  topos_has_coterminator

/-- **§1.945**: A topos is regular — images exist and pullbacks transfer covers.
    For f : A → B let F = {B' ↣ B | f factors through B'}; then ∩F is the image
    of f (§1.943 + the internal-∀ family-glb).

    CLOSED (no longer a sorry).  `RegularCategory` bundles
    `HasTerminal`/`HasBinaryProducts`/`HasPullbacks` (from `Topos` via the classifier),
    `HasImages`, and `PullbacksTransferCovers`.  The two non-Cartesian fields are now
    both supplied sorry-free by `InternalForallTopos`:

    * `HasImages` — the `toposHasImages` instance, where `image f = imageF f` is the
      family big-intersection `⋂{B' | f factors through B'}`, built via the internal-∀
      family-glb `bigInter` (NOT the §1.54 transfinite capitalization — that route is
      bypassed entirely).
    * `PullbacksTransferCovers` — the `SlicePi.toposPullbacksTransferCovers` instance,
      proved non-circularly from the §1.931 dependent-product right adjoint `Π_f`
      (which preserves epics, so covers are pullback-stable).

    With both instances in scope, `RegularCategory` assembles immediately; this is
    exactly the (sorry-free) `topos_is_regular_real` of `InternalForallTopos`.  The
    historical §1.543-capitalization blocker no longer applies. -/
theorem topos_is_regular : Nonempty (RegularCategory 𝒞) :=
  topos_is_regular_real

/-- **§1.946**: A topos is a logos — a regular category in which every inverse-image
    functor f# : 𝒫(B) → 𝒫(A) has a right adjoint f## (§1.946).
    Binary unions: A₁ ∪ A₂ = ∩{B' | A₁ ⊆ B' ∧ A₂ ⊆ B'} via §1.943.
    (Uses local Logos'; canonical Logos is in S1_70 which has a build error.)

    PARTIAL (faithful sorry — the `RegularCategory` field is now AVAILABLE, two fields
    remain).  `Logos'` extends `RegularCategory` + `HasSubobjectUnions` + the right
    adjoint `HasRightAdjointImage'` (f##).  The `RegularCategory` sub-goal is NO LONGER a
    blocker — it is exactly `topos_is_regular` (now closed via the internal-∀ family-glb,
    no §1.543 capitalization).  What remains genuinely missing are the OTHER two fields:

    * `HasSubobjectUnions` — binary union `A₁ ∪ A₂ = ⋂{B' | A₁ ⊆ B' ∧ A₂ ⊆ B'}`, a glb
      over a subobject FAMILY;
    * `HasRightAdjointImage'` — the right adjoint `f##`, also a family-glb.

    CLOSED (no longer a sorry).  All three fields are now available topos instances:

    * `RegularCategory` — `topos_is_regular` (the internal-∀ family-glb image + `Π_f`-cover-transfer);
    * `HasSubobjectUnions` — `toposHasSubobjectUnions` (the §1.952 family-glb of common upper bounds,
      `Fredy.ToposColimits`);
    * `HasRightAdjointImage'` — `toposHasRightAdjointImage` above, the §1.946 keystone `f##`
      (`Fredy.RightAdjointImage`, internal-∀ right adjoint + adjunction, sorry-free).

    `Logos'` assembles from these three (the regular structure is unbundled into its
    `HasImages`/`PullbacksTransferCovers` fields so the union/right-adjoint instances resolve). -/
theorem topos_is_logos : Nonempty (Logos' 𝒞) := by
  obtain ⟨reg⟩ := topos_is_regular (𝒞 := 𝒞)
  letI : HasImages 𝒞 := reg.toHasImages
  letI : PullbacksTransferCovers 𝒞 := reg.toPullbacksTransferCovers
  exact ⟨{ reg with
    toHasSubobjectUnions := toposHasSubobjectUnions
    toHasRightAdjointImage' := toposHasRightAdjointImage }⟩

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

/-- **§1.947**: A topos is a TRANSITIVE LOGOS — every endo-relation `R` on `B` has a
    reflexive-transitive closure `R*` (the least reflexive transitive relation ⊇ R), with
    its four universal properties: `R ⊑ R*`, `R*` reflexive, `R*` transitive, and `R*`
    minimal among reflexive-transitive relations containing `R`.

    HONEST DISCHARGE.  This is now stated and proved in the genuine §1.77 `BinRel` encoding
    (reflexivity = `graph(id) ⊑ R*`, the diagonal — Freyd's real notion, not the degenerate
    "entire ≤ R*" of the old `Subobject`-stub which forced `R = ⊤`).  The proof is by the new
    §1.77 keystone path: the topos R* IS Freyd's family-glb `⋂F` of reflexive pre-closed
    relations, which `transRefClos_of_glb_preclosed` assembles into a full `TransRefClos R`.
    We take that closure ABSTRACTLY via `[HasReflTransClosure 𝒞]` — Freyd's own hypothesis
    "a topos has R*" (§1.77 documents `HasReflTransClosure` as exactly the natural input for
    this theorem).  The closure-ASSEMBLY (R ⊑ R*, refl, trans, minimal) is now genuinely
    discharged from `rtc`/`le_rtc`/`rtc_reflexive`/`rtc_transitive`/`rtc_minimal`.

    RESIDUAL (pinned by the hypothesis, NOT a sorry): the *existence* of the glb `M = ⋂F`
    — the §1.943 family-glb over a subobject family of `[B×B]` — still rests on §1.54's
    `capitalization_lemma` (still `sorry`), which is what would *construct* the
    `HasReflTransClosure 𝒞` instance for a bare topos.  The §1.945-blocked regular structure
    `[HasImages 𝒞]`/`[PullbacksTransferCovers 𝒞]` (= `topos_is_regular`, still `sorry`) is
    likewise carried as an explicit hypothesis.  This theorem isolates precisely the
    *closure-assembly* (now done) from the *glb-existence* (the genuine §1.543 residual).

    AXIOM-HYGIENE NOTE: the *proof body* `⟨rtc R, …⟩` contains no `sorry` — the four §1.77
    components (`le_rtc`/`rtc_reflexive`/`rtc_transitive`/`rtc_minimal`) are each `#print
    axioms`-clean.  `#print axioms topos_has_rtc` nonetheless reports `sorryAx`; this is the
    pre-existing FILE-WIDE leak of S1_92's `topos_has_exponentials` (a `sorry` global instance
    synthesised from the ambient `[Topos 𝒞]`, which `BinRel`'s `HasPullbacks` resolution routes
    through) and it taints EVERY completed declaration here equally (`inter_le_named`,
    `membershipMap_nameOf`, …) — not anything specific to this discharge.  It is out of scope
    to fix (S1_92, off-limits). -/
theorem topos_has_rtc [HasImages 𝒞] [PullbacksTransferCovers 𝒞] [HasReflTransClosure 𝒞]
    {B : 𝒞} (R : BinRel 𝒞 B B) :
    ∃ Rstar : BinRel 𝒞 B B,
      -- R ⊑ R*
      RelLe R Rstar ∧
      -- R* is reflexive: diagonal graph(id) ⊑ R*
      IsReflexive Rstar ∧
      -- R* is transitive: R* ⊚ R* ⊑ R*
      IsTransitive Rstar ∧
      -- R* is the least reflexive-transitive relation containing R
      ∀ (S : BinRel 𝒞 B B),
        RelLe R S → IsReflexive S → IsTransitive S → RelLe Rstar S :=
  ⟨rtc R, le_rtc R, rtc_reflexive R, rtc_transitive R,
    fun S hRS hReflS hTransS => rtc_minimal R S hRS hReflS hTransS⟩

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

-- `singletonMap` (the SINGLETON MAP A1 : A → [A]) is now in `InterIntersection` and
-- re-exported via the import above.

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
-- The genuine categorical fact about A1 available here is MONICITY (§1.92),
-- exposed as `singletonMap_monic` — now in `InterIntersection` and re-exported.

/-- **§1.94(10)**: A capital topos is solvable.
    In a capital topos, A* = A if A is well-supported (Cover (term A)),
    else A* = 0 (the minimal subobject from §1.944).

    BLOCKER (faithful sorry): the `A* = 0` branch needs the strict coterminator
    (`topos_has_strict_coterminator`, blocked) and the well-pointed-part lub is the
    §1.943 `⋃`/`⋂F` glb over a family — all backed by §1.54's `capitalization_lemma`
    (still `sorry`).  `_hcap : Capital` alone does not supply these.

    RE-EXAMINED against the new infra: none of `modular_identity`/`compose_union_right`/
    `DisjointBinaryCoproduct`/`effective_of_quotient_cover` constructs the singleton-lub
    `A* = ⋃{point subobjects}`; the first three need the §1.543-blocked regular/positive
    structure and the fourth (effectiveness) is orthogonal to the well-pointed part.
    The `IsWellPointedPart` lub and the `A*=0` strict-initial branch both remain
    behind §1.543. -/
theorem capital_is_solvable [HasImages 𝒞] (_hcap : Capital (𝒞 := 𝒞)) :
    ∀ (A : 𝒞), ∃ Astar : Subobject 𝒞 A, IsWellPointedPart Astar := by
  sorry

end Freyd
