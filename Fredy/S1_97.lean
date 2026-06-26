/-
  Freyd & Scedrov, *Categories and Allegories* §1.97–§1.98  Boolean topoi, natural numbers.

  §1.97  BOOLEAN TOPOS: Ω is a Boolean algebra (every subobject is complemented).
  §1.971 SMALL OBJECT in a topos.
  §1.973 INTERNAL AXIOM OF CHOICE (IAC).
  §1.974 AC ↔ IAC + projective terminal.
  §1.98  NATURAL NUMBERS OBJECT (NNO) in a topos.
  §1.981 NNO iterate for pairs: (A→B, B→B) → unique A×N→B.
  §1.983 PRIMITIVE RECURSION (parametrised) in a topos.
  §1.985 N ≅ 1+N; N→N→1 is a coequalizer.
  §1.987 PEANO PROPERTY for NNO.
  §1.98(10) Bicartesian characterization of NNO.
  §1.98(11) Bicartesian functors preserve NNO.
  §1.98(12) A-ACTION, FREE A-ACTION.
  §1.98(13) Bicartesian characterization of free A-action.
  §1.98(14) Existence of free A-action from NNO.
-/

import Fredy.S1_1
import Fredy.S1_9
import Fredy.S1_42
import Fredy.S1_47
import Fredy.S1_51
import Fredy.S1_57
import Fredy.S1_58
import Fredy.S1_64
import Fredy.S1_85
import Fredy.S1_92
import Fredy.S1_94
import Fredy.InternalForall
import Fredy.PartialMapClassifier
import Fredy.LeastClosedTopos
import Fredy.Complement
import Fredy.ToposExists
import Fredy.ToposDistributive


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-- A topos is a cartesian category: `HasTerminal`+`HasBinaryProducts` come from `Topos`,
    `HasEqualizers` from `topos_has_equalizers` (§1.92).  Built *from the ambient instances*
    (no new product/terminal structure), so `term`/`prod`/`eq` agree definitionally with the
    Topos ones.  Low priority so it never pre-empts a locally-supplied cartesian structure.
    Needed to state `TwoValued (𝒞 := 𝒞)` (§1.989 single-valuedness, S1_47). -/
noncomputable instance (priority := 100) Topos.toCartesianCategory : CartesianCategory 𝒞 :=
  { toHasTerminal := inferInstance
    toHasBinaryProducts := inferInstance
    toHasEqualizers := inferInstance }

/-! ## §1.97  Boolean topos

  A TOPOS IS BOOLEAN if its subobject classifier Ω is an internal
  Boolean algebra, i.e. every subobject has a complement (§1.97).
  Equivalently: the negation map ¬ : Ω → Ω satisfies ¬¬ = id. -/

/-- A BOOLEAN TOPOS has ¬¬ = id on Ω, i.e. every subobject is complemented (§1.97). -/
class BooleanTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞 where
  not : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)
  double_neg : not ≫ not = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞))

/-! ## §1.971  Small objects in a Grothendieck topos

  §1.971: Given a generating set G in a Grothendieck topos, an object A is SMALL
  if it appears as a subquotient of a G-object: there exist A ↠ G' ↣ G with G ∈ G. -/

/-- §1.971: An object A is SMALL (relative to generating set G) if it is a subquotient
    of a G-object: there exist maps A → G' ↣ G ∈ G. -/
def IsSmall (G : 𝒞 → Prop) (A : 𝒞) : Prop :=
  ∃ (B C : 𝒞) (q : A ⟶ B) (m : B ⟶ C), Cover q ∧ Monic m ∧ G C

-- §1.971: In a boolean Grothendieck topos every object is a coproduct of small objects.
-- BOOK §1.971: In a boolean Grothendieck topos every object is a coproduct of small objects.
-- (Proof: any object is covered by its small subobjects; in a complete boolean algebra every
--  cover refines to a partition.  Subobjects of small objects are small.)

-- §1.972: In a boolean logos, if 1 is projective, then it is a progenitor.
-- BOOK §1.972: In a boolean logos, if 1 is projective, then it is a progenitor.
-- (Proof: if x ≠ y : A → B, the complement E' of the equalizer is nonzero, so its support U
--  is nonzero; 1 projective gives z : U → E' with the equalizer of zx and zy being zero.)

/-! ## §1.975–§1.979  IAC, boolean, etendue -/

-- §1.975: Slicing by a well-supported C creates a local left inverse for f in E/C.
-- BOOK §1.975: A left inverse for f exists 'locally' (in E/C for any well-supported C).

-- §1.976: A small topos may be faithfully represented in an AC topos iff it is IAC.
-- BOOK §1.976: A small topos may be faithfully represented in an AC topos iff it is IAC.

-- §1.977: Any universal sentence in the predicates of topoi that follows from AC also
--         follows from IAC.  In particular, an IAC topos is boolean.
-- BOOK §1.977: Any universal sentence in the predicates of topoi which follows from AC
--              also follows from IAC.

-- §1.977 (corollary): An IAC topos is boolean.
-- BOOK §1.977: An IAC topos is boolean.

-- §1.978: A Grothendieck topos A is an ETENDUE if there exists a well-supported B
--         such that A/B is value-based (its terminator is a progenitor).
-- BOOK §1.978: A Grothendieck topos is a boolean etendue iff it is IAC.
-- (IsEtendue def deferred: needs WellSupported (S1_52) and IsValueBased (S1_95) in scope.)

-- §1.979: For any topos A there exists a boolean topos B and a faithful bicartesian
--         representation A → B.  (Proof deferred to §2.542 in Chapter 2.)
-- BOOK §1.979: For any topos A there exists a boolean topos B and a faithful bicartesian
--              representation A → B.

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

/-- Absorbing a `pair` into the product functor: `⟨f,g⟩ ≫ (A × h) = ⟨f, g≫h⟩`. -/
theorem pair_prodMap {𝒞 : Type u} [Cat.{v} 𝒞] [HasBinaryProducts 𝒞]
    {A X Y W : 𝒞} (f : W ⟶ A) (g : W ⟶ X) (h : X ⟶ Y) :
    pair f g ≫ prodMap A X Y h = pair f (g ≫ h) := by
  apply pair_uniq
  · rw [Cat.assoc, prodMap_fst, fst_pair]
  · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair]

/-! ## §1.974  AC ↔ IAC + projective terminal

  §1.974: A topos is AC (all objects are projective / choice) iff it is IAC
  and 1 is projective.

  Backward (IAC ∧ 1 projective ⇒ every object projective): given a cover
  f : A → C, the post-composition cover q := f^C : A^C → C^C is a cover (IAC).
  Pull q back along the name `⌜id_C⌝ : 1 → C^C` of the identity; the projection
  P → 1 is a cover (pullbacks transfer covers, the topos-exactness fact Freyd
  treats as ambient — `PullbacksTransferCovers`), and 1 projective splits it.
  The splitting names a point p : 1 → A^C lifting ⌜id_C⌝; uncurrying p gives the
  section s : C → A with s ≫ f = id_C.

  Forward (every object projective ⇒ IAC ∧ 1 projective): 1 projective is the
  C := 1 instance.  IAC: a cover f is split (cover = split epi when its codomain
  is projective), s ≫ f = id; exponential functoriality `f^C` then has the
  section `s^C` (since `(s≫f)^C = s^C ≫ f^C = id`), so `f^C` is a split epi,
  hence a cover.

  The book's argument explicitly invokes "pullbacks preserve epics", i.e.
  `PullbacksTransferCovers` — a topos-exactness fact that this repo does NOT
  derive from `Topos` (see the faithful Sorries in §1.94 `topos_is_regular`).
  We therefore carry it as an explicit hypothesis, matching the book's ambient
  use of topos regularity. -/

/-- A split epi (map with a right inverse `s ≫ f = id`) is a cover. -/
theorem cover_of_split_epi {X Y : 𝒞} [HasImages 𝒞] {f : X ⟶ Y} {s : Y ⟶ X}
    (hsf : s ≫ f = Cat.id Y) : Cover f := by
  intro D m g hm hgm
  -- (s ≫ g) ≫ m = s ≫ f = id_Y, so m has a section; m mono ⇒ m iso.
  have hsec : (s ≫ g) ≫ m = Cat.id Y := by rw [Cat.assoc, hgm, hsf]
  have hms : m ≫ (s ≫ g) = Cat.id D :=
    hm _ _ (by rw [Cat.assoc, hsec, Cat.comp_id, Cat.id_comp])
  exact ⟨s ≫ g, hms, hsec⟩

/-- The NAME of a map `g : C → A` as a point `1 → A^C`: `⌜g⌝ = curry (fst ≫ g)`
    where `fst : C × 1 → C`.  Its uncurry `apply ⌜g⌝ = g`. -/
def expName {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞] [HasExponentials 𝒞] {A C : 𝒞}
    (g : C ⟶ A) : one ⟶ A ^^ C :=
  curry (fst ≫ g)

/-- Uncurry a point `p : 1 → A^C` back to a map `C → A`: `⟨id_C, term≫p⟩ ≫ eval`. -/
def expApply {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞] [HasExponentials 𝒞] {A C : 𝒞}
    (p : one ⟶ A ^^ C) : C ⟶ A :=
  pair (Cat.id C) (term C ≫ p) ≫ eval_exp C A

/-- `apply ⌜g⌝ = g`. -/
theorem expApply_expName {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞] [HasExponentials 𝒞]
    {A C : 𝒞} (g : C ⟶ A) : expApply (expName g) = g := by
  show pair (Cat.id C) (term C ≫ curry (fst ≫ g)) ≫ eval_exp C A = g
  have key : pair (Cat.id C) (term C ≫ curry (fst ≫ g)) ≫ eval_exp C A
      = pair (Cat.id C) (term C) ≫ prodMap C one (A ^^ C) (curry (fst ≫ g)) ≫ eval_exp C A := by
    rw [← Cat.assoc, pair_prodMap]
  rw [key, curry_eval_eq, ← Cat.assoc, fst_pair, Cat.id_comp]

/-- Uncurry commutes with post-composition: `apply (p ≫ f^C) = apply p ≫ f`. -/
theorem expApply_postMap {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞] [HasExponentials 𝒞]
    {A B C : 𝒞} (p : one ⟶ A ^^ C) (f : A ⟶ B) :
    expApply (p ≫ expPostMap C A B f) = expApply p ≫ f := by
  show pair (Cat.id C) (term C ≫ p ≫ expPostMap C A B f) ≫ eval_exp C B
      = (pair (Cat.id C) (term C ≫ p) ≫ eval_exp C A) ≫ f
  calc pair (Cat.id C) (term C ≫ p ≫ expPostMap C A B f) ≫ eval_exp C B
      = pair (Cat.id C) ((term C ≫ p) ≫ expPostMap C A B f) ≫ eval_exp C B := by
        rw [Cat.assoc]
    _ = (pair (Cat.id C) (term C ≫ p) ≫ prodMap C (A ^^ C) (B ^^ C) (curry (eval_exp C A ≫ f)))
          ≫ eval_exp C B := by rw [expPostMap, ← pair_prodMap]
    _ = pair (Cat.id C) (term C ≫ p) ≫ eval_exp C A ≫ f := by rw [Cat.assoc, curry_eval_eq]
    _ = (pair (Cat.id C) (term C ≫ p) ≫ eval_exp C A) ≫ f := (Cat.assoc _ _ _).symm

/-- Naming commutes with post-composition: `⌜g⌝ ≫ f^C = ⌜g ≫ f⌝`. -/
theorem expName_postMap {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞] [HasExponentials 𝒞]
    {A B C : 𝒞} (g : C ⟶ A) (f : A ⟶ B) :
    expName g ≫ expPostMap C A B f = expName (g ≫ f) := by
  -- both name `g ≫ f`; check by uncurrying (prodMap_eval_inj on points via curry_unique).
  show expName g ≫ curry (eval_exp C A ≫ f) = curry (fst ≫ g ≫ f)
  apply curry_unique_eq
  -- (C × (⌜g⌝ ≫ curry(eval≫f))) ≫ eval = fst ≫ g ≫ f
  rw [prodMap_comp, Cat.assoc, curry_eval_eq, ← Cat.assoc]
  -- ((C × ⌜g⌝) ≫ eval) ≫ f = fst ≫ g ≫ f
  show (prodMap C one (A ^^ C) (expName g) ≫ eval_exp C A) ≫ f = fst ≫ g ≫ f
  -- (C × ⌜g⌝) ≫ eval = fst ≫ g, with ⌜g⌝ = curry (fst ≫ g)
  show (prodMap C one (A ^^ C) (curry (fst ≫ g)) ≫ eval_exp C A) ≫ f = fst ≫ g ≫ f
  rw [curry_eval_eq, Cat.assoc]

/-- §1.974: A topos is AC iff it is IAC and the terminal object 1 is projective.
    (`PullbacksTransferCovers` = the ambient topos-exactness the book uses.) -/
theorem ac_iff_iac_and_projective_one [HasExponentials 𝒞] [HasImages 𝒞]
    [HasPullbacks 𝒞] [PullbacksTransferCovers 𝒞] :
    (∀ (C : 𝒞), Projective C) ↔
    (IsIAC 𝒞 ∧ Projective (one (𝒞 := 𝒞))) := by
  constructor
  · -- Forward: all projective ⇒ IAC ∧ 1 projective.
    intro hall
    refine ⟨?_, hall one⟩
    -- IAC: cover f ⇒ f^A := expPostMap A B C f is a cover.
    intro A B C f hf
    -- f is a cover with codomain C, and C is projective, so f splits.
    obtain ⟨s, hs⟩ := hall C f hf
    -- s ≫ f = id_C.  expPostMap is functorial: s^A ≫ f^A = (s≫f)^A = id^A = id.
    have hfun : expPostMap A C B s ≫ expPostMap A B C f = Cat.id (C ^^ A) := by
      show expCovMap A s ≫ expCovMap A f = Cat.id (C ^^ A)
      rw [← expCovMap_comp, hs, expCovMap_id]
    intro D m g hm hgm
    exact (cover_of_split_epi (f := expPostMap A B C f) (s := expPostMap A C B s) hfun)
      m g hm hgm
  · -- Backward: IAC ∧ 1 projective ⇒ every object projective.
    rintro ⟨hiac, h1⟩ C A f hf
    -- q := f^C : A^C → C^C is a cover (IAC).
    let q : (A ^^ C) ⟶ (C ^^ C) := expPostMap C A C f
    have hq : Cover q := hiac C A C f hf
    -- name of id_C : 1 → C^C
    let nm : one ⟶ (C ^^ C) := expName (Cat.id C)
    -- pull q back along nm; projection π₂ : P → 1 is a cover.
    let pb := HasPullbacks.has q nm
    have hπ₂ : Cover pb.cone.π₂ := cover_pullback nm hq
    -- 1 projective splits π₂.
    obtain ⟨r, hr⟩ := h1 pb.cone.π₂ hπ₂
    -- p := r ≫ π₁ : 1 → A^C lifts nm:  p ≫ q = nm.
    let p : one ⟶ (A ^^ C) := r ≫ pb.cone.π₁
    have hp : p ≫ q = nm := by
      show (r ≫ pb.cone.π₁) ≫ q = nm
      rw [Cat.assoc, pb.cone.w, ← Cat.assoc, hr, Cat.id_comp]
    -- s := uncurry p : C → A.  Then s ≫ f = apply (p ≫ q) = apply nm = id_C.
    refine ⟨expApply p, ?_⟩
    -- s ≫ f = apply p ≫ f = apply (p ≫ f^C) = apply (p ≫ q) = apply nm = id_C.
    rw [← expApply_postMap p f]
    show expApply (p ≫ expPostMap C A C f) = Cat.id C
    rw [show expPostMap C A C f = q from rfl, hp]
    exact expApply_expName (Cat.id C)

/-! ## §1.981  NNO iterate for pairs

  §1.981: If 1 →⁰ N →ˢ N is a NNO, then for every A →ᵃ B ←ᵇ B there
  exists a unique A × N → B such that the two triangles commute.
  This is obtained by transposing through the exponential adjunction. -/

/-- `g ↦ (A × g) ≫ eval` is injective: it is split by `curry`. -/
theorem prodMap_eval_inj {𝒞 : Type u} [Cat.{v} 𝒞] [HasExponentials 𝒞]
    {A B X : 𝒞} {g₁ g₂ : X ⟶ B ^^ A}
    (h : prodMap A X (B ^^ A) g₁ ≫ eval_exp A B = prodMap A X (B ^^ A) g₂ ≫ eval_exp A B) :
    g₁ = g₂ := by
  rw [curry_unique_eq (f := prodMap A X (B ^^ A) g₁ ≫ eval_exp A B) rfl,
      curry_unique_eq (f := prodMap A X (B ^^ A) g₂ ≫ eval_exp A B) rfl, h]

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
  -- iteratePair a b = (A × iter) ≫ eval, with iter = iterate a_hat b_hat.
  -- Absorb the pair, use zero ≫ iter = a_hat, then curry_eval to drop a_hat.
  show pair (Cat.id A) (term A ≫ hN.zero) ≫
      prodMap A hN.nno (exp A B) (hN.iterate (curry (fst ≫ a)) (expPostMap A B B b)) ≫ eval_exp A B = a
  rw [← Cat.assoc, pair_prodMap, Cat.assoc, hN.iterate_zero]
  -- goal: ⟨id, term ≫ a_hat⟩ ≫ eval = a, with a_hat = curry (fst ≫ a)
  have key : pair (Cat.id A) (term A ≫ curry (fst ≫ a)) ≫ eval_exp A B
      = pair (Cat.id A) (term A) ≫ prodMap A one (exp A B) (curry (fst ≫ a)) ≫ eval_exp A B := by
    rw [← Cat.assoc, pair_prodMap]
  rw [key, curry_eval_eq, ← Cat.assoc, fst_pair, Cat.id_comp]

/-- §1.981 successor equation: (1_A, s) ≫ iteratePair a b = iteratePair a b ≫ b. -/
theorem iteratePair_succ {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (a : A ⟶ B) (b : B ⟶ B) :
    prodMap A hN.nno hN.nno (hN.succ) ≫ iteratePair a b = iteratePair a b ≫ b := by
  show prodMap A hN.nno hN.nno hN.succ ≫
      prodMap A hN.nno (exp A B) (hN.iterate (curry (fst ≫ a)) (expPostMap A B B b)) ≫ eval_exp A B
    = (prodMap A hN.nno (exp A B) (hN.iterate (curry (fst ≫ a)) (expPostMap A B B b)) ≫ eval_exp A B) ≫ b
  -- collapse the two prodMaps on N, then use succ ≫ iter = iter ≫ b_hat
  rw [← Cat.assoc, ← prodMap_comp, hN.iterate_succ, prodMap_comp]
  -- goal: (A × iter) ≫ (A × b_hat) ≫ eval = ((A × iter) ≫ eval) ≫ b
  rw [Cat.assoc, Cat.assoc]
  congr 1
  -- (A × b_hat) ≫ eval = eval ≫ b, since b_hat = expPostMap = curry (eval ≫ b)
  show prodMap A (exp A B) (exp A B) (curry (eval_exp A B ≫ b)) ≫ eval_exp A B = eval_exp A B ≫ b
  rw [curry_eval_eq]

/-- §1.981 uniqueness: iteratePair is the unique such morphism. -/
theorem iteratePair_unique {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (a : A ⟶ B) (b : B ⟶ B)
    (h : prod A hN.nno ⟶ B)
    (h0 : pair (Cat.id A) (term A ≫ hN.zero) ≫ h = a)
    (hs : prodMap A hN.nno hN.nno hN.succ ≫ h = h ≫ b) :
    h = iteratePair a b := by
  -- Transpose h to curry h : N → B^A. Show curry h = iterate a_hat b_hat by NNO uniqueness,
  -- then uncurry both sides.
  have hbhat : prodMap A (exp A B) (exp A B) (expPostMap A B B b) ≫ eval_exp A B
      = eval_exp A B ≫ b := by
    show prodMap A (exp A B) (exp A B) (curry (eval_exp A B ≫ b)) ≫ eval_exp A B = eval_exp A B ≫ b
    rw [curry_eval_eq]
  -- curry h iterates the NNO data:
  have hcurry : curry h = hN.iterate (curry (fst ≫ a)) (expPostMap A B B b) := by
    apply hN.iterate_unique
    · -- zero ≫ curry h = curry (fst ≫ a)
      apply prodMap_eval_inj
      rw [prodMap_comp, Cat.assoc, curry_eval_eq, curry_eval_eq]
      -- goal: (A × zero) ≫ h = fst ≫ a
      have hpm : prodMap A one hN.nno hN.zero = fst ≫ pair (Cat.id A) (term A ≫ hN.zero) := by
        symm
        apply pair_uniq
        · rw [Cat.assoc, fst_pair, Cat.comp_id]
        · rw [Cat.assoc, snd_pair, ← Cat.assoc]; congr 1; exact term_uniq _ _
      rw [show prodMap A HasTerminal.one hN.nno hN.zero
            = fst ≫ pair (Cat.id A) (term A ≫ hN.zero) from hpm, Cat.assoc, h0]
    · -- succ ≫ curry h = curry h ≫ b_hat
      apply prodMap_eval_inj
      rw [prodMap_comp, Cat.assoc, curry_eval_eq, prodMap_comp, Cat.assoc, hbhat,
          ← Cat.assoc, curry_eval_eq, hs]
  -- now uncurry: h = (A × curry h) ≫ eval = (A × iter) ≫ eval = iteratePair a b
  show h = prodMap A hN.nno (exp A B) (hN.iterate (curry (fst ≫ a)) (expPostMap A B B b)) ≫ eval_exp A B
  rw [← hcurry, curry_eval_eq]

/-! ## §1.983  Primitive recursion in a topos

  §1.983: Given a NNO 1→N→N and g : A → B and h : A × N × B → B,
  there exists a unique f : A × N → B such that
    (1_A, 0) ≫ f = g
    (1_A × s) ≫ f = (1_A, p₂, f) ≫ h
  where (1_A, p₂, f) : A × N → A × N × B. -/

/-- §1.983 base value a' : A → (A×N)×B for the §1.981 iterate: `⟨⟨1_A, 0⟩, g⟩`. -/
def primRecBase {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (g : A ⟶ B) : A ⟶ prod (prod A hN.nno) B :=
  pair (pair (Cat.id A) (term A ≫ hN.zero)) g

/-- §1.983 step b' : (A×N)×B → (A×N)×B for the §1.981 iterate:
    `⟨⟨p₁, p₂·s⟩, h⟩` — advance the counter and apply h. -/
def primRecStep {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (h : prod (prod A hN.nno) B ⟶ B) :
    prod (prod A hN.nno) B ⟶ prod (prod A hN.nno) B :=
  pair (pair (fst ≫ fst) (fst ≫ snd ≫ hN.succ)) h

/-- §1.983: PRIMITIVE RECURSION. Given NNO 1→N→N, g : A→B, h : A×N×B→B,
    the unique f : A×N→B satisfying the primitive recursion equations.
    Construction (book): k := iteratePair ⟨⟨1,0⟩,g⟩ ⟨⟨p₁,p₂s⟩,h⟩ : A×N → (A×N)×B,
    then f = k ≫ p₃ (projection to B). -/
def primRec {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (g : A ⟶ B) (h : prod (prod A hN.nno) B ⟶ B) :
    prod A hN.nno ⟶ B :=
  iteratePair (primRecBase g) (primRecStep h) ≫ snd

/-- §1.983 carrier identity: the A×N-component of k is the identity, i.e. k ≫ p₁ = 1.
    This is what makes k = ⟨p₁, p₂, f⟩.  Proved by §1.981-uniqueness: both k≫p₁ and 1
    iterate ⟨1_A,0⟩ along (A × s). -/
theorem primRec_fst {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (g : A ⟶ B) (h : prod (prod A hN.nno) B ⟶ B) :
    iteratePair (primRecBase g) (primRecStep h) ≫ fst = Cat.id (prod A hN.nno) := by
  -- k ≫ fst and id both equal iteratePair ⟨1,0⟩ (A × s); conclude by uniqueness.
  have e0 : pair (Cat.id A) (term A ≫ hN.zero)
        ≫ (iteratePair (primRecBase g) (primRecStep h) ≫ fst)
      = pair (Cat.id A) (term A ≫ hN.zero) := by
    rw [← Cat.assoc, iteratePair_zero]
    show primRecBase g ≫ fst = _
    rw [primRecBase, fst_pair]
  have es : prodMap A hN.nno hN.nno hN.succ
        ≫ (iteratePair (primRecBase g) (primRecStep h) ≫ fst)
      = (iteratePair (primRecBase g) (primRecStep h) ≫ fst)
        ≫ prodMap A hN.nno hN.nno hN.succ := by
    rw [← Cat.assoc, iteratePair_succ, Cat.assoc, Cat.assoc]
    congr 1
    -- primRecStep h ≫ fst = ⟨p₁p₁, p₁p₂s⟩ = fst ≫ (A × s)
    rw [primRecStep, fst_pair]
    symm
    apply pair_uniq
    · rw [Cat.assoc, prodMap_fst]
    · rw [Cat.assoc, prodMap_snd, ← Cat.assoc]
  -- both k≫fst and id satisfy the same iterate equations for (⟨1,0⟩, A×s)
  have huniq1 : iteratePair (primRecBase g) (primRecStep h) ≫ fst
      = iteratePair (pair (Cat.id A) (term A ≫ hN.zero)) (prodMap A hN.nno hN.nno hN.succ) :=
    iteratePair_unique _ _ _ e0 es
  have huniq2 : Cat.id (prod A hN.nno)
      = iteratePair (pair (Cat.id A) (term A ≫ hN.zero)) (prodMap A hN.nno hN.nno hN.succ) := by
    apply iteratePair_unique
    · rw [Cat.comp_id]
    · rw [Cat.comp_id, Cat.id_comp]
  rw [huniq1, ← huniq2]

/-- §1.983 base equation: (1_A, 0) ≫ primRec g h = g. -/
theorem primRec_zero {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (g : A ⟶ B) (h : prod (prod A hN.nno) B ⟶ B) :
    pair (Cat.id A) (term A ≫ hN.zero) ≫ primRec g h = g := by
  show pair (Cat.id A) (term A ≫ hN.zero)
      ≫ iteratePair (primRecBase g) (primRecStep h) ≫ snd = g
  rw [← Cat.assoc, iteratePair_zero, primRecBase, snd_pair]

/-- §1.983 step equation: (1_A × s) ≫ primRec g h = ⟨id, id, primRec g h⟩ ≫ h. -/
theorem primRec_succ {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (g : A ⟶ B) (h : prod (prod A hN.nno) B ⟶ B) :
    prodMap A hN.nno hN.nno hN.succ ≫ primRec g h =
      pair (pair fst snd) (primRec g h) ≫ h := by
  -- k = ⟨p₁, f⟩ since k≫p₁ = 1; LHS = k≫h, and ⟨⟨p₁,p₂⟩,f⟩ = k.
  have hkeq : iteratePair (primRecBase g) (primRecStep h)
      = pair (pair fst snd) (iteratePair (primRecBase g) (primRecStep h) ≫ snd) := by
    apply pair_uniq
    · rw [primRec_fst, pair_fst_snd]
    · rfl
  have hstep_snd : primRecStep h ≫ snd = h := by rw [primRecStep, snd_pair]
  show prodMap A hN.nno hN.nno hN.succ ≫ iteratePair (primRecBase g) (primRecStep h) ≫ snd
      = pair (pair fst snd) (iteratePair (primRecBase g) (primRecStep h) ≫ snd) ≫ h
  rw [← Cat.assoc, iteratePair_succ, Cat.assoc, hstep_snd, ← hkeq]

/-- §1.983 uniqueness. -/
theorem primRec_unique {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    {A B : 𝒞} (g : A ⟶ B) (h : prod (prod A hN.nno) B ⟶ B)
    (f : prod A hN.nno ⟶ B)
    (hf0 : pair (Cat.id A) (term A ≫ hN.zero) ≫ f = g)
    (hfs : prodMap A hN.nno hN.nno hN.succ ≫ f = pair (pair fst snd) f ≫ h) :
    f = primRec g h := by
  -- kf := ⟨p₁, p₂, f⟩ satisfies the §1.981 iterate equations for (a', b'); by §1.981
  -- uniqueness kf = k = iteratePair a' b', so f = kf ≫ snd = k ≫ snd = primRec g h.
  have kf_fst : pair (pair fst snd) f ≫ fst = pair fst snd := fst_pair _ _
  have hkf : pair (pair fst snd) f = iteratePair (primRecBase g) (primRecStep h) := by
    apply iteratePair_unique
    · -- ⟨1,0⟩ ≫ kf = a' = ⟨⟨1,0⟩, g⟩
      rw [primRecBase]
      apply pair_uniq
      · apply pair_uniq <;>
          simp only [Cat.assoc, fst_pair, snd_pair, Cat.comp_id]
      · simp only [Cat.assoc, fst_pair, snd_pair]; exact hf0
    · -- (A×s) ≫ kf = kf ≫ b'; both equal ⟨⟨p₁, p₂s⟩, kf≫h⟩.
      have lhs : prodMap A hN.nno hN.nno hN.succ ≫ pair (pair fst snd) f
          = pair (pair fst (snd ≫ hN.succ)) (pair (pair fst snd) f ≫ h) := by
        apply pair_uniq
        · apply pair_uniq <;>
            simp only [Cat.assoc, fst_pair, snd_pair, prodMap_fst, prodMap_snd]
        · simp only [Cat.assoc, fst_pair, snd_pair]; exact hfs
      have rhs : pair (pair fst snd) f ≫ pair (pair (fst ≫ fst) (fst ≫ snd ≫ hN.succ)) h
          = pair (pair fst (snd ≫ hN.succ)) (pair (pair fst snd) f ≫ h) := by
        apply pair_uniq
        · rw [Cat.assoc, fst_pair]
          apply pair_uniq
          · rw [Cat.assoc, fst_pair, ← Cat.assoc, kf_fst, fst_pair]
          · rw [Cat.assoc, snd_pair, ← Cat.assoc, kf_fst, ← Cat.assoc, snd_pair]
        · rw [Cat.assoc, snd_pair]
      rw [primRecStep, lhs, rhs]
  show f = iteratePair (primRecBase g) (primRecStep h) ≫ snd
  rw [← hkf, snd_pair]

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
  -- c = [0,s] : 1+N → N.  Build the inverse d : N → 1+N by NNO-iterate:
  --   d := iterate inl f,  where  f := [0≫inr, s≫inr] : 1+N → 1+N.
  -- Key: f ≫ c = c ≫ s (case-uniqueness), inl ≫ c = 0, inr ≫ c = s.
  open HasBinaryCoproducts in
  let c : coprod one hN.nno ⟶ hN.nno := case hN.zero hN.succ
  let f : coprod one hN.nno ⟶ coprod one hN.nno :=
    case (hN.zero ≫ inr) (hN.succ ≫ inr)
  let d : hN.nno ⟶ coprod one hN.nno := hN.iterate inl f
  have hil : inl ≫ c = hN.zero := case_inl _ _
  have hir : inr ≫ c = hN.succ := case_inr _ _
  -- f ≫ c = c ≫ s :  both equal case (0≫s) (s≫s)
  have hfc : f ≫ c = c ≫ hN.succ := by
    rw [case_uniq (hN.zero ≫ hN.succ) (hN.succ ≫ hN.succ) (f ≫ c)
          (by rw [← Cat.assoc]; show (inl ≫ f) ≫ c = _;
              rw [case_inl, Cat.assoc, hir])
          (by rw [← Cat.assoc]; show (inr ≫ f) ≫ c = _;
              rw [case_inr, Cat.assoc, hir]),
        case_uniq (hN.zero ≫ hN.succ) (hN.succ ≫ hN.succ) (c ≫ hN.succ)
          (by rw [← Cat.assoc, hil]) (by rw [← Cat.assoc, hir])]
  refine ⟨d, ?_, ?_⟩
  · -- c ≫ d = id_{1+N}, via case_uniq: inl-leg = inl, inr-leg = inr.
    rw [show Cat.id (coprod one hN.nno) = case inl inr from
        case_uniq inl inr _ (by rw [Cat.comp_id]) (by rw [Cat.comp_id])]
    apply case_uniq
    · -- inl ≫ c ≫ d = inl :  inl≫c = 0, 0≫d = inl
      rw [← Cat.assoc, hil, hN.iterate_zero]
    · -- inr ≫ c ≫ d = inr :  inr≫c = s, s≫d = d≫f, and d≫f = inr by NNO-uniqueness
      rw [← Cat.assoc, hir, hN.iterate_succ]
      -- d ≫ f = inr = iterate (0≫inr) f
      have hinr : inr (A := one) (B := hN.nno) = hN.iterate (hN.zero ≫ inr) f :=
        hN.iterate_unique _ _ _ rfl (case_inr _ _).symm
      have hdf : d ≫ f = hN.iterate (hN.zero ≫ inr) f := by
        apply hN.iterate_unique
        · show hN.zero ≫ d ≫ f = hN.zero ≫ inr
          rw [← Cat.assoc, hN.iterate_zero]; show inl ≫ f = _; rw [case_inl]
        · show hN.succ ≫ d ≫ f = (d ≫ f) ≫ f
          rw [← Cat.assoc, hN.iterate_succ, Cat.assoc]
      rw [hdf, ← hinr]
  · -- d ≫ c = id_N = iterate 0 s, via NNO-uniqueness
    rw [show Cat.id hN.nno = hN.iterate hN.zero hN.succ from
        hN.iterate_unique _ _ _ (by rw [Cat.comp_id]) (by rw [Cat.comp_id, Cat.id_comp])]
    apply hN.iterate_unique
    · -- 0 ≫ d ≫ c = 0 :  0≫d = inl, inl≫c = 0
      rw [← Cat.assoc, hN.iterate_zero, hil]
    · -- s ≫ d ≫ c = (d≫c) ≫ s :  s≫d = d≫f, f≫c = c≫s
      rw [← Cat.assoc, hN.iterate_succ, Cat.assoc, hfc, ← Cat.assoc]

/-- §1.985(2): The terminal map N → 1 is a coequalizer of (s, id_N) : N ⇉ N.
    That is, for any f : N → X with s ≫ f = f, f factors uniquely through
    the terminal: ∃! g : 1 → X, term N ≫ g = f. -/
theorem nno_terminal_is_coequalizer {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] :
    ∀ (X : 𝒞) (f : hN.nno ⟶ X),
      hN.succ ≫ f = f →
      ∃ g : (one ⟶ X), term hN.nno ≫ g = f ∧
        ∀ g' : (one ⟶ X), term hN.nno ≫ g' = f → g' = g := by
  intro X f hf
  -- g = zero ≫ f : 1 → X
  refine ⟨hN.zero ≫ f, ?_, ?_⟩
  · -- Show term N ≫ (zero ≫ f) = f via NNO uniqueness.
    -- Both f and (term N ≫ zero ≫ f) satisfy the NNO equations for (zero ≫ f, id_X).
    -- For f: zero ≫ f = zero ≫ f ✓; succ ≫ f = f = f ≫ id ✓.
    -- For (term N ≫ zero ≫ f): zero ≫ (term N ≫ zero ≫ f) = (zero ≫ term N) ≫ zero ≫ f
    --   = id ≫ zero ≫ f = zero ≫ f ✓;
    --   succ ≫ (term N ≫ zero ≫ f) = (succ ≫ term N) ≫ zero ≫ f
    --   = term N ≫ zero ≫ f (since succ ≫ term N = term N by uniqueness) ✓.
    -- By NNO uniqueness both equal hN.iterate (zero ≫ f) (Cat.id X), so f = term N ≫ zero ≫ f.
    have heq_f : f = hN.iterate (hN.zero ≫ f) (Cat.id X) :=
      hN.iterate_unique (hN.zero ≫ f) (Cat.id X) f rfl (by rw [hf, Cat.comp_id])
    have heq_g : term hN.nno ≫ hN.zero ≫ f = hN.iterate (hN.zero ≫ f) (Cat.id X) := by
      apply hN.iterate_unique
      · -- zero ≫ (term N ≫ zero ≫ f) = zero ≫ f
        -- Pull out: (zero ≫ term N) ≫ (zero ≫ f), then zero ≫ term N = id_1
        have h1 : hN.zero ≫ term hN.nno = Cat.id one := term_uniq _ _
        rw [← Cat.assoc, h1]
        exact Cat.id_comp _
      · -- succ ≫ (term N ≫ zero ≫ f) = (term N ≫ zero ≫ f) ≫ id
        rw [Cat.comp_id, ← Cat.assoc]
        congr 1
        exact term_uniq _ _
    rw [heq_g, ← heq_f]
  · -- Uniqueness: if term N ≫ g' = f then g' = zero ≫ f.
    intro g' hg'
    -- zero ≫ term N = id, so g' = zero ≫ term N ≫ g' = zero ≫ f.
    have : hN.zero ≫ term hN.nno = Cat.id one := term_uniq _ _
    calc g' = Cat.id one ≫ g'            := (Cat.id_comp _).symm
      _     = (hN.zero ≫ term hN.nno) ≫ g' := by rw [this]
      _     = hN.zero ≫ term hN.nno ≫ g'   := Cat.assoc _ _ _
      _     = hN.zero ≫ f                   := by rw [hg']

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
  -- B ↣ N allows 0 (point e:1→B.dom, e≫arr=0) and is t=succ-stable (tB:B.dom→B.dom,
  -- tB≫arr = arr≫s).  Then (B.dom, e, tB) is an N-algebra; iterate e tB : N → B.dom
  -- is a SECTION of arr (iterate e tB ≫ arr = iterate 0 s = id_N by NNO-uniqueness).
  -- A mono with a section is an iso, so B is entire.
  intro B ⟨e, he⟩ ⟨tB, htB⟩
  -- sec : N → B.dom, the iterate of the algebra (B.dom, e, tB)
  let sec : hN.nno ⟶ B.dom := hN.iterate e tB
  -- sec ≫ arr = id_N  (both iterate the NNO data (0, s))
  have hsec_arr : sec ≫ B.arr = Cat.id hN.nno := by
    rw [show Cat.id hN.nno = hN.iterate hN.zero hN.succ from
        hN.iterate_unique _ _ _ (by rw [Cat.comp_id]) (by rw [Cat.comp_id, Cat.id_comp])]
    apply hN.iterate_unique
    · -- 0 ≫ sec ≫ arr = 0 :  0≫sec = e (iterate_zero), e≫arr = 0
      rw [← Cat.assoc]; show (hN.zero ≫ sec) ≫ B.arr = _
      rw [show hN.zero ≫ sec = e from hN.iterate_zero _ _, he]
    · -- s ≫ sec ≫ arr = (sec≫arr) ≫ s :  s≫sec = sec≫tB, tB≫arr = arr≫s
      rw [← Cat.assoc]; show (hN.succ ≫ sec) ≫ B.arr = _
      rw [show hN.succ ≫ sec = sec ≫ tB from hN.iterate_succ _ _,
          Cat.assoc, htB, ← Cat.assoc]
  -- arr ≫ sec = id_{B.dom}, by mono-cancelling arr
  have harr_sec : B.arr ≫ sec = Cat.id B.dom := by
    apply B.monic
    rw [Cat.assoc, hsec_arr, Cat.comp_id, Cat.id_comp]
  exact ⟨sec, harr_sec, hsec_arr⟩

/-- §1.987: Existence of least subobject with Peano property.
    Given a : 1 → A and t : A → A, there is a least subobject A' ↣ A
    that allows a and is stable under t, and A' has the Peano property.
    The Peano property for A' is stated with respect to the induced morphisms
    a' = term A'.dom ≫ A'.arr ≫ ... restricted to A'.

    CONSTRUCTION (Freyd §1.987 / §1.94).  `A'` is the internal intersection
    `⋂{ S ↣ A | a ∈ S ∧ t(S) ⊆ S }` of the family of `(a,t)`-CLOSED subobjects of `A`.
    This family-glb is the genuine internal universal quantifier / big-intersection
    `Ω^(Ω^A) → Ω^A` applied to the closedness comprehension `{ G : Ω^A | closed G }`.
    `S1_94.interIntersection` builds only the *singleton*-family glb (one name
    `F_name : 1 → Ω^A`), NOT this glb over a subobject family — see
    `S1_94.inter_le_singleton_named`'s integrity note.  The missing operation is the
    internal-∀ (right adjoint to weakening), whose β/η computation rests on the concrete
    power-object exponential adjunction (`S1_92.topos_has_exponentials`, off-limits and
    itself `Sorry`), so it cannot be built here from the currently-proven primitives.

    We therefore consume the genuine §1.987 conclusion as the explicit hypothesis
    `[HasLeastClosedSubobject 𝒞]` (`Fredy/InternalForall.lean`): in every topos the least
    `(a,t)`-closed subobject exists.  Given that primitive every step below is immediate,
    and crucially the LEASTNESS clause is the CORRECT one (`A'.le B` for every closed `B`,
    exactly §1.987) — NOT the earlier broken reduction, which demanded all closed `B` share
    one name `nameOf B.arr = F_name` (forcing them all equal, a false statement).  STATUS:
    this is NOT the §1.543 capitalization lemma (PROVEN Sorry-free); it is the separate
    internal-∀ / family-glb gap that `S1_94` flags but never builds. -/
theorem least_peano_subobject {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞] [HasImages 𝒞]
    [HasExponentials 𝒞] [HasLeastClosedSubobject 𝒞]
    {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) :
    ∃ (A' : Subobject 𝒞 A),
      Allows A' a ∧
      (∃ (t' : A'.dom ⟶ A'.dom), t' ≫ A'.arr = A'.arr ≫ t) ∧
      (∀ (B : Subobject 𝒞 A), Allows B a →
        (∃ (tB : B.dom ⟶ B.dom), tB ≫ B.arr = B.arr ≫ t) → A'.le B) := by
  -- A' := the least `(a,t)`-closed subobject `⋂{B | IsClosedSub B a t}` (InternalForall).
  refine ⟨HasLeastClosedSubobject.least a t, ?_, ?_, ?_⟩
  · -- A' allows a — first half of `least_isClosed`.
    exact (HasLeastClosedSubobject.least_isClosed a t).1
  · -- A' is t-stable — second half of `least_isClosed`.
    exact (HasLeastClosedSubobject.least_isClosed a t).2
  · -- Leastness: every `(a,t)`-closed B is above A', directly by `least_le`.
    intro B hBa hBt
    exact HasLeastClosedSubobject.least_le a t B ⟨hBa, hBt⟩


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
    [hN : HasNaturalNumbersObject 𝒞] :
    Nonempty (FreeAAction (𝒞 := 𝒞) one) := by
  -- The free 1-action: obj = N, unit = zero, act = snd ≫ succ.
  -- recA α = iterate α.unit (f_rec α) where f_rec α = pair(term,id) ≫ α.act.
  -- Key identity: prodMap one N B h = pair fst (snd ≫ h)
  --   = (snd ≫ h) ≫ pair (term B) (Cat.id B)  [fst eq by term_uniq, snd eq trivial]
  -- recA_act: prodMap one N B (iter) ≫ α.act = (snd ≫ iter) ≫ f_rec α
  --   and act ≫ iter = snd ≫ succ ≫ iter = snd ≫ iter ≫ f_rec α [iterate_succ].
  -- recA_uniq: deduce succ ≫ m = m ≫ f_rec α by snd-monicity, then iterate_unique.
  -- f_rec α : α.obj → α.obj sends x ↦ α.act(*, x) via pair(term,id) ≫ α.act
  -- Key: prodMap one N B h = (snd ≫ h) ≫ pair (term B) (Cat.id B)
  -- recA_act: prodMap one N B iter ≫ α.act = (snd ≫ iter) ≫ f_rec = snd ≫ iter ≫ f_rec
  --   = snd ≫ succ ≫ iter [iterate_succ] = (snd ≫ succ) ≫ iter.
  -- recA_uniq: from hms: snd ≫ m ≫ f_rec = snd ≫ succ ≫ m; cancel snd via its section.
  -- Helper: prodMap one N B h = (snd ≫ h) ≫ pair(term B)(id B) [equal fst and snd by pair_uniq]
  have prodMap_factorN : ∀ {B : 𝒞} (h : hN.nno ⟶ B),
      prodMap one hN.nno B h = (snd ≫ h) ≫ pair (term B) (Cat.id B) := fun h => by
    symm; apply pair_uniq
    · rw [Cat.assoc, fst_pair]; exact term_uniq _ _
    · rw [Cat.assoc, snd_pair, Cat.comp_id]
  exact ⟨{
    obj  := hN.nno
    unit := hN.zero
    act  := snd ≫ hN.succ
    recA := fun α => hN.iterate α.unit (pair (term α.obj) (Cat.id α.obj) ≫ α.act)
    recA_unit := fun α => hN.iterate_zero α.unit _
    recA_act := fun α => by
      -- LHS: prodMap one N α.obj iter ≫ α.act = ((snd ≫ iter) ≫ pair(term,id)) ≫ α.act
      --    = (snd ≫ iter) ≫ pair(term,id) ≫ α.act = snd ≫ iter ≫ (pair(term,id) ≫ α.act)
      -- RHS: (snd ≫ succ) ≫ iter = snd ≫ succ ≫ iter = snd ≫ iter ≫ (pair(term,id) ≫ α.act)
      --    [by iterate_succ]
      rw [prodMap_factorN, Cat.assoc, Cat.assoc, Cat.assoc]
      congr 1
      exact (hN.iterate_succ α.unit (pair (term α.obj) (Cat.id α.obj) ≫ α.act)).symm
    recA_uniq := fun α m hm0 hms => by
      apply hN.iterate_unique α.unit (pair (term α.obj) (Cat.id α.obj) ≫ α.act) m hm0
      -- hms: prodMap one N α.obj m ≫ α.act = (snd ≫ succ) ≫ m
      -- prodMap_factorN: prodMap one N B m = (snd ≫ m) ≫ pair(term,id)
      -- So: ((snd ≫ m) ≫ pair(term,id)) ≫ α.act = (snd ≫ succ) ≫ m
      --     (snd ≫ m) ≫ (pair(term,id) ≫ α.act) = snd ≫ succ ≫ m
      --     snd ≫ m ≫ (pair(term,id) ≫ α.act) = snd ≫ succ ≫ m
      -- Cancel snd via section: prodOneLeftInv ≫ snd = id
      -- Derive: snd ≫ succ ≫ m = snd ≫ m ≫ (pair(term,id) ≫ α.act)
      -- From hms with prodMap_factorN: ((snd ≫ m) ≫ pair...) ≫ α.act = (snd ≫ succ) ≫ m.
      -- Rearranging gives snd ≫ m ≫ f_rec = snd ≫ succ ≫ m.
      -- Cancel snd from left via its section prodOneLeftInv ≫ snd = id.
      have heq : (snd : prod one hN.nno ⟶ hN.nno) ≫ m ≫
            (pair (term α.obj) (Cat.id α.obj) ≫ α.act) = snd ≫ hN.succ ≫ m := by
        have h := hms
        rw [prodMap_factorN] at h
        -- h : ((snd ≫ m) ≫ pair...) ≫ α.act = (snd ≫ succ) ≫ m
        calc (snd : prod one hN.nno ⟶ hN.nno) ≫ m ≫ (pair _ _ ≫ α.act)
            = ((snd ≫ m) ≫ pair _ _) ≫ α.act := by rw [Cat.assoc, Cat.assoc]
          _ = (snd ≫ hN.succ) ≫ m := h
          _ = snd ≫ hN.succ ≫ m := Cat.assoc _ _ _
      have key := congrArg (prodOneLeftInv hN.nno ≫ ·) heq
      simp only [← Cat.assoc, prodOneLeftInv_snd, Cat.id_comp] at key
      -- key: (m ≫ pair...) ≫ α.act = succ ≫ m; need m ≫ (pair... ≫ α.act) = succ ≫ m
      rw [Cat.assoc] at key
      exact key.symm
  }⟩

/-! ## §1.98(10)  Bicartesian characterization of NNO

  §1.98(10): In any topos, if 1 →ᵃ A ←ᵗ A is such that [a, t] : 1 + A → A is
  an isomorphism and A → A → 1 is a coequalizer of (t, id_A), then 1 →ᵃ A →ᵗ A
  is a NNO.

  The Peano property follows from §1.988 (or its generalization, cited as [2.542]
  in the book) and the NNO uniqueness and existence conditions are verified from
  the bicartesian data.  We record the statement here with a Sorry pending the
  §1.988 partial-map-classifier recursor + §1.987 internal-∀ Peano induction
  (W-type infrastructure absent in this repo — NOT the now-proven §1.543 lemma). -/

/-! ### §1.988 BOOLEAN hypothesis (statement-fidelity fix)

  Freyd's §1.988 Peano theorem is stated **for a BOOLEAN topos**, and its proof uses
  booleanness essentially: it takes the COMPLEMENT `A''` of the least `(a,t)`-closed
  subobject `A'` and shows `A'' = 0`.  A general topos is not boolean, so the
  complement need not exist; the general-topos statement is an OVER-REACH that, in
  Freyd's development, silently requires the Chapter-2 boolean embedding §2.542.  The
  faithful **Chapter-1** statement carries the boolean hypothesis, which §1.919/§1.988
  forward-reference to §2.542 as later removable ("Therefore the word 'boolean' will
  be removable from …").  We thread it as `BooleanSub` below — exactly Freyd's §1.97
  definition of a boolean topos: *every subobject is complemented*.

  `BooleanSub` is stated over the CANONICAL `PreLogos 𝒞` instance a topos carries
  (`Fredy.ToposExists`), so `IsComplementedSub` (`Fredy/Complement.lean`, `S1_62`) is
  available with the topos's own products/pullbacks and there is no instance diamond
  (the diamond that a bare `[BooleanPreLogos 𝒞]` super-class would create). -/

/-- §1.97 BOOLEAN topos as a hypothesis: every subobject of every object is
    complemented (`IsComplementedSub`).  This is Freyd's exact definition of "boolean"
    and the hypothesis his §1.988 Peano proof actually uses. -/
def BooleanSub (𝒞 : Type u) [Cat.{v} 𝒞] [Topos 𝒞] : Prop :=
  ∀ {Z : 𝒞} (S : Subobject 𝒞 Z), IsComplementedSub S

/-! ### §1.635/§1.641 regular-image calculus for the `t_stable_complement` claim

  These Chapter-1 facts (direct-image monotonicity, image of a `case` over a union, and
  the complement-meet lemma) assemble Freyd's "claim" that the complement of the least
  closed subobject is `t`-stable.  They sit at the `S1_62` subobject level (images, unions,
  intersections, complements) and use NO Chapter-2 machinery. -/

section RegularImageCalculus
variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-- **Direct-image monotonicity.**  If `S ≤ T` then `t(S) := image (S.arr ≫ t) ≤ t(T)`:
    `S.arr ≫ t` factors through `image (T.arr ≫ t)` (via the `≤`-witness and the image
    lift), so image-minimality gives the containment. -/
theorem image_post_mono {A : 𝒞} (t : A ⟶ A) {S T : Subobject 𝒞 A} (hST : S.le T) :
    (image (S.arr ≫ t)).le (image (T.arr ≫ t)) := by
  obtain ⟨h, hh⟩ := hST
  refine image_min _ _ ⟨h ≫ image.lift (T.arr ≫ t), ?_⟩
  rw [Cat.assoc, image.lift_fac, ← Cat.assoc, hh]

/-- A map out of the terminal object is monic (`f ≫ a = g ≫ a ⟹ f = g`, since `f, g : X → 1`
    are forced equal by `term_uniq`). -/
theorem mono_from_one {A : 𝒞} (a : one ⟶ A) : Monic a := by
  intro X f g _; exact term_uniq f g

/-- Composite of monics is monic. -/
theorem mono_comp'' {X Y Z : 𝒞} {m : X ⟶ Y} {n : Y ⟶ Z} (hm : Monic m) (hn : Monic n) :
    Monic (m ≫ n) := by
  intro W f g h
  apply hm; apply hn
  rw [← Cat.assoc, ← Cat.assoc] at h; exact h

/-- The monic subobject `⟨X, m⟩` is its own image: `image m ≤ ⟨X,m⟩` (minimality, `m` allows
    itself) and `⟨X,m⟩ ≤ image m` (image allows `m`, and `m` monic descends). -/
theorem image_mono_eq {A X : 𝒞} (m : X ⟶ A) (hm : Monic m) :
    (image m).le (Subobject.mk X m hm) ∧ (Subobject.mk X m hm).le (image m) :=
  ⟨image_min m (Subobject.mk X m hm) ⟨Cat.id X, Cat.id_comp m⟩, image_allows m⟩

/-- Post-composition distributes over a copairing: `case f g ≫ h = case (f≫h) (g≫h)`. -/
theorem case_comp [HasBinaryCoproducts 𝒞] {X Y A B : 𝒞}
    (f : A ⟶ X) (g : B ⟶ X) (h : X ⟶ Y) :
    HasBinaryCoproducts.case f g ≫ h
      = HasBinaryCoproducts.case (f ≫ h) (g ≫ h) := by
  refine HasBinaryCoproducts.case_uniq (f ≫ h) (g ≫ h) _ ?_ ?_
  · rw [← Cat.assoc, HasBinaryCoproducts.case_inl]
  · rw [← Cat.assoc, HasBinaryCoproducts.case_inr]

/-- **Disjointness ⟹ `≤ ⊥`** (§1.621 / §1.944).  If a subobject `Z ↣ A` carries two
    generalized elements identified across the CANONICAL disjoint injections
    (`u ≫ coprodInl P Q = v ≫ coprodInr P Q`), then `Z ≤ ⊥`.  Lift `(u,v)` into the
    pullback of `(coprodInl, coprodInr)` — which `coprodInjections_disjoint` shows is `≅ 0` —
    so `Z.dom` maps to the strict-initial `0`, hence is `≅ 0 ≅ (⊥A).dom`. -/
theorem le_bottom_of_canonical_common {A : 𝒞} (Z : Subobject 𝒞 A) {P Q : 𝒞}
    (u : Z.dom ⟶ P) (v : Z.dom ⟶ Q)
    (huv : u ≫ coprodInl P Q = v ≫ coprodInr P Q) :
    Z.le (PreLogos.bottom A) := by
  -- lift `(u,v)` into the canonical pullback of `(coprodInl, coprodInr)`.
  let pb := HasPullbacks.has (coprodInl P Q) (coprodInr P Q)
  let w : Z.dom ⟶ pb.cone.pt := pb.lift ⟨Z.dom, u, v, huv⟩
  -- the pullback apex is `≅ 0`; postcompose `w` to map `Z.dom → 0`, iso by strictness.
  obtain ⟨f0, _⟩ := coprodInjections_disjoint P Q
  let z : Z.dom ⟶ (bottomSub (one : 𝒞)).dom :=
    (w ≫ f0) ≫ (bottomSub_dom_iso (coprodObj P Q) (one : 𝒞)).choose
  have hz_iso : IsIso z := any_map_to_zero_is_iso (inferInstance : PreLogos 𝒞) z
  have hZ0 : Isomorphic Z.dom (PreLogos.bottom A).dom :=
    isomorphic_trans ⟨z, hz_iso⟩ (bottomSub_dom_iso (one : 𝒞) A)
  exact le_bottom_of_dom_iso Z hZ0

/-- **A map into a `⊥`-domain forces `≤ ⊥`** (strict initiality).  `⊥.dom ≅ 0` is strict-initial,
    so any `m : Z.dom → (⊥W).dom` makes `Z.dom ≅ 0 ≅ (⊥A).dom`. -/
theorem peano_le_bottom_of_map {A W : 𝒞} (Z : Subobject 𝒞 A)
    (m : Z.dom ⟶ (PreLogos.bottom W).dom) : Z.le (PreLogos.bottom A) := by
  let z : Z.dom ⟶ (bottomSub (one : 𝒞)).dom :=
    m ≫ (bottomSub_dom_iso W (one : 𝒞)).choose
  have hz_iso : IsIso z := any_map_to_zero_is_iso (inferInstance : PreLogos 𝒞) z
  exact le_bottom_of_dom_iso Z (isomorphic_trans ⟨z, hz_iso⟩ (bottomSub_dom_iso (one : 𝒞) A))

/-- **The complement is `≤` the other half of any cover** (boolean meet–join lemma,
    §1.658 / [1.635]).  A verbatim public copy of the `S1_64` private `complement_le_other`,
    relocated here so it is reachable without importing `S1_64`: if `D₁ ∩ Dc ≤ ⊥` and
    `⊤ ≤ D₁ ∪ D₂` then `Dc ≤ D₂`.  Proof = meet-over-join distributivity. -/
theorem complement_le_other' [HasBinaryCoproducts 𝒞] {A : 𝒞}
    (D₁ D₂ Dc : Subobject 𝒞 A)
    (hdisj : Subobject.le (Subobject.inter D₁ Dc) (PreLogos.bottom A))
    (hcov  : Subobject.le (Subobject.entire A) (HasSubobjectUnions.union D₁ D₂)) :
    Dc.le D₂ := by
  have hA : Dc.le (Subobject.inter Dc (HasSubobjectUnions.union D₁ D₂)) :=
    Subobject.le_inter ⟨Cat.id _, Cat.id_comp _⟩
      (subLe_trans' (Y := Subobject.entire A) ⟨Dc.arr, Cat.comp_id _⟩ hcov)
  have hdist : (Subobject.inter Dc (HasSubobjectUnions.union D₁ D₂)).le
      (HasSubobjectUnions.union (Subobject.inter Dc D₁) (Subobject.inter Dc D₂)) := by
    have e1 : Subobject.inter Dc (HasSubobjectUnions.union D₁ D₂)
        = pushMono Dc.arr Dc.monic (InverseImage Dc.arr (HasSubobjectUnions.union D₁ D₂)) := rfl
    have e2 : Subobject.inter Dc D₁ = pushMono Dc.arr Dc.monic (InverseImage Dc.arr D₁) := rfl
    have e3 : Subobject.inter Dc D₂ = pushMono Dc.arr Dc.monic (InverseImage Dc.arr D₂) := rfl
    rw [e1, e2, e3]
    have hpre : (InverseImage Dc.arr (HasSubobjectUnions.union D₁ D₂)).le
        (HasSubobjectUnions.union (InverseImage Dc.arr D₁) (InverseImage Dc.arr D₂)) :=
      (PreLogos.invImage_preserves_union Dc.arr D₁ D₂).1
    exact subLe_trans' (pushMono_mono Dc.arr Dc.monic hpre)
      (pushMono_union_le Dc.arr Dc.monic _ _)
  have hbot : (Subobject.inter Dc D₁).le (PreLogos.bottom A) :=
    subLe_trans' (inter_comm_le Dc D₁) hdisj
  have hfin : (HasSubobjectUnions.union (Subobject.inter Dc D₁) (Subobject.inter Dc D₂)).le D₂ :=
    HasSubobjectUnions.union_min _ _ _
      (subLe_trans' hbot (PreLogos.bottom_min D₂)) (Subobject.inter_le_right _ _)
  exact subLe_trans' hA (subLe_trans' hdist hfin)

end RegularImageCalculus

/-- **§1.988 PEANO PROPERTY in a BOOLEAN topos.**  If `[a,t] : 1+A ≅ A` is iso and
    `A →ᵗ A → 1` is a coequalizer of `(t, id_A)`, then in a BOOLEAN topos every
    `(a,t)`-closed subobject `B ↣ A` is entire.

    PROOF (Freyd §1.988).  Take `A'` = the least `(a,t)`-closed subobject
    (`least_peano_subobject`); it suffices to show `A'` is entire (any closed `B ⊇ A'`
    is then entire too).  Booleanness gives the complement `A''` of `A'`, so
    `A ≅ A' + A''` (`complementedSub_legs_iso`).  Because `[a,t]` is iso, `A = a(1) ⊔ t(A)`
    disjointly and `t` is monic; since `A' = a(1) ⊔ t(A')` (least closed), the complement
    is `t`-stable (`t` restricts to `A''`, Freyd's §1.635/§1.641 claim), so `t = t' + t''`
    is block-diagonal.  The coequalizer `A →ᵗ A → 1` then splits as `C' + C'' = 1` with
    `C'`, `C''` the terminal coequalizers of `(t',id)`, `(t'',id)`; `A'` allows `a` gives
    a point `1 → C'`, forcing `C' = 1`, `C'' = 0`, hence `A'' = 0` (§1.944).  So `A'` is
    entire and `(a,t)` has the Peano property. -/
theorem peano_property_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasLeastClosedSubobject 𝒞]
    (hbool : BooleanSub 𝒞)
    {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A)
    (hiso : IsIso (HasBinaryCoproducts.case a t (A := one) (B := A) (X := A)))
    (hcoeq : ∀ (X : 𝒞) (f : A ⟶ X), t ≫ f = f →
               ∃ g : (one ⟶ X), term A ≫ g = f ∧
                 ∀ g' : one ⟶ X, term A ≫ g' = f → g' = g)
    (B : Subobject 𝒞 A) (hBa : Allows B a)
    (hBt : ∃ tB : B.dom ⟶ B.dom, tB ≫ B.arr = B.arr ≫ t) :
    B.IsEntire := by
  classical
  -- A' := the least `(a,t)`-closed subobject.
  let A' : Subobject 𝒞 A := HasLeastClosedSubobject.least a t
  have hA'closed : IsClosedSub A' a t := HasLeastClosedSubobject.least_isClosed a t
  -- REDUCTION (no booleanness):  `A'` entire  ⟹  `B` entire.
  -- Leastness: `A' ≤ B`, so `B.arr` is split epi (via `A'.arr`'s inverse); `B.monic` ⟹ iso.
  suffices hA'entire : A'.IsEntire by
    obtain ⟨ai, _hai1, hai2⟩ := hA'entire
    -- `hai2 : ai ≫ A'.arr = id A`
    obtain ⟨k, hk⟩ := HasLeastClosedSubobject.least_le a t B ⟨hBa, hBt⟩
    -- `hk : k ≫ B.arr = A'.arr`
    refine ⟨ai ≫ k, ?_, ?_⟩
    · -- B.arr ≫ (ai ≫ k) = id : use mono of B.arr.
      apply B.monic
      rw [Cat.assoc, Cat.assoc, hk, hai2, Cat.id_comp, Cat.comp_id]
    · -- (ai ≫ k) ≫ B.arr = id_A
      rw [Cat.assoc, hk, hai2]
  -- Now prove `A'.IsEntire`.
  -- Booleanness: complement `A''` of `A'`, with `A' ∩ A'' ≤ 0` and `A ≤ A' ∪ A''`.
  obtain ⟨A'', hdisj, hentire⟩ := hbool A'
  -- `complementedSub_legs_iso` realises `A ≅ A'.dom + A''.dom` matching the inclusions.
  obtain ⟨ψ, ψinv, hψ1, hψ2, hψinl, hψinr⟩ := complementedSub_legs_iso A' A'' hdisj hentire
  -- `t'` : `A'` is t-stable (it is `(a,t)`-closed).
  obtain ⟨t', ht'⟩ := hA'closed.2
  -- A' allows `a` : `a = a₀ ≫ A'.arr`.
  obtain ⟨a₀, ha₀⟩ := hA'closed.1
  -- ── THE CLAIM (Freyd §1.988 / §1.635, §1.641): `t` restricts to the complement `A''`.
  -- Since `[a,t]` iso ⟹ `t` monic and `A = a(1) ⊔ t(A)` disjointly, and `A' = a(1) ⊔ t(A')`
  -- (least closed), a point of `A''` (∉ A', hence ∉ a(1) ⊆ A', hence ∈ t(A)) whose `t`-image
  -- lay in `A'` would lie in `t(A')` (disjoint from a(1)), so (t monic) be in `A'` — absurd.
  -- Thus `t(A'') ⊆ A''`: there is `t'' : A''.dom → A''.dom` with `t'' ≫ A''.arr = A''.arr ≫ t`.
  -- ── Foundational facts for the CLAIM (block-diagonality of `t`).
  -- β-laws and inverse of the iso `case a t`.
  have hcl : HasBinaryCoproducts.inl ≫ HasBinaryCoproducts.case a t = a :=
    HasBinaryCoproducts.case_inl a t
  have hcr : HasBinaryCoproducts.inr ≫ HasBinaryCoproducts.case a t = t :=
    HasBinaryCoproducts.case_inr a t
  obtain ⟨ci, hci1, hci2⟩ := hiso  -- case≫ci = id, ci≫case = id
  -- `inr` (hypothesis coproduct) is split mono (retraction `case a (id A)`), hence monic.
  have hinr_mono : Monic (HasBinaryCoproducts.inr (A := one) (B := A)) :=
    mono_of_retraction _ (HasBinaryCoproducts.case a (Cat.id A))
      (HasBinaryCoproducts.case_inr a (Cat.id A))
  -- `t` monic: `t = inr ≫ case`, `inr` monic, `case` iso.
  have htmono : Monic t := by
    intro W g h hgh
    apply hinr_mono
    -- g ≫ inr = h ≫ inr from g ≫ t = h ≫ t by post-composing `ci`.
    have e : (g ≫ HasBinaryCoproducts.inr) ≫ HasBinaryCoproducts.case a t
        = (h ≫ HasBinaryCoproducts.inr) ≫ HasBinaryCoproducts.case a t := by
      rw [Cat.assoc, Cat.assoc, hcr, hgh]
    have := congrArg (· ≫ ci) e
    simpa only [Cat.assoc, hci1, Cat.comp_id] using this
  -- Disjointness of the HYPOTHESIS coproduct `1+A` via the comparison map to the canonical one.
  have hdisj_hyp : ∀ {Z : 𝒞} (u : Z ⟶ one) (v : Z ⟶ A),
      u ≫ HasBinaryCoproducts.inl = v ≫ HasBinaryCoproducts.inr →
      ∀ {Y : 𝒞} (p q : Z ⟶ Y), p = q := by
    intro Z u v huv Y p q
    let φ : HasBinaryCoproducts.coprod (one : 𝒞) A ⟶ coprodObj (one : 𝒞) A :=
      HasBinaryCoproducts.case (coprodInl (one : 𝒞) A) (coprodInr (one : 𝒞) A)
    have hcommon : u ≫ coprodInl (one : 𝒞) A = v ≫ coprodInr (one : 𝒞) A := by
      have hl : HasBinaryCoproducts.inl ≫ φ = coprodInl (one : 𝒞) A :=
        HasBinaryCoproducts.case_inl _ _
      have hr : HasBinaryCoproducts.inr ≫ φ = coprodInr (one : 𝒞) A :=
        HasBinaryCoproducts.case_inr _ _
      calc u ≫ coprodInl (one : 𝒞) A = u ≫ HasBinaryCoproducts.inl ≫ φ := by rw [hl]
        _ = (u ≫ HasBinaryCoproducts.inl) ≫ φ := (Cat.assoc _ _ _).symm
        _ = (v ≫ HasBinaryCoproducts.inr) ≫ φ := by rw [huv]
        _ = v ≫ HasBinaryCoproducts.inr ≫ φ := Cat.assoc _ _ _
        _ = v ≫ coprodInr (one : 𝒞) A := by rw [hr]
    exact coprodInjections_disjoint_elt u v hcommon p q
  -- `≤ ⊥` from a HYPOTHESIS-coproduct common point: convert `u≫inl = v≫inr` to the canonical
  -- injections (comparison map `φ`), then `le_bottom_of_canonical_common`.
  have hbot_hyp : ∀ (Z : Subobject 𝒞 A) (u : Z.dom ⟶ one) (v : Z.dom ⟶ A),
      u ≫ HasBinaryCoproducts.inl = v ≫ HasBinaryCoproducts.inr →
      Z.le (PreLogos.bottom A) := by
    intro Z u v huv
    let φ : HasBinaryCoproducts.coprod (one : 𝒞) A ⟶ coprodObj (one : 𝒞) A :=
      HasBinaryCoproducts.case (coprodInl (one : 𝒞) A) (coprodInr (one : 𝒞) A)
    have hcommon : u ≫ coprodInl (one : 𝒞) A = v ≫ coprodInr (one : 𝒞) A := by
      have hl : HasBinaryCoproducts.inl ≫ φ = coprodInl (one : 𝒞) A :=
        HasBinaryCoproducts.case_inl _ _
      have hr : HasBinaryCoproducts.inr ≫ φ = coprodInr (one : 𝒞) A :=
        HasBinaryCoproducts.case_inr _ _
      calc u ≫ coprodInl (one : 𝒞) A = u ≫ HasBinaryCoproducts.inl ≫ φ := by rw [hl]
        _ = (u ≫ HasBinaryCoproducts.inl) ≫ φ := (Cat.assoc _ _ _).symm
        _ = (v ≫ HasBinaryCoproducts.inr) ≫ φ := by rw [huv]
        _ = v ≫ HasBinaryCoproducts.inr ≫ φ := Cat.assoc _ _ _
        _ = v ≫ coprodInr (one : 𝒞) A := by rw [hr]
    exact le_bottom_of_canonical_common Z u v hcommon
  have hclaim : ∃ t'' : A''.dom ⟶ A''.dom, t'' ≫ A''.arr = A''.arr ≫ t := by
    -- `t_stable_complement` (Freyd's §1.988 "claim", p.185, [1.635]/[1.641]) — NOW PROVEN.
    -- In the BOOLEAN topos the complement `A''` of the least `(a,t)`-closed `A'` is itself
    -- `t`-stable, so `t = t'+t''` is block-diagonal w.r.t. `A ≅ A'.dom + A''.dom`.  Everything
    -- else of §1.988 is assembled BELOW from this fact (`t`-invariance of `e : A → 1+1`, the
    -- coequalizer point `g = inl`, `A'' = 0`, `A'` entire ⟹ `B` entire).
    --
    -- THE `t_stable_complement` PROOF (Chapter-1 regular-image calculus, [1.635]/[1.641]):
    --   `A' = a(1) ∪ t(A')` (closedness of `a(1)∪t(A')` + leastness), where — crucially — `a`
    --   and `t` are MONIC (`mono_from_one`, `htmono`), so `a(1)`, `t(A')`, `t(A'')` are honest
    --   monic subobjects (`image_mono_eq`), NOT proper images.  Hence `t(A'') ∩ A' ≤ 0` splits
    --   into `a(1)∩t(A'') ≤ 0` and `t(A')∩t(A'') ≤ 0`, both pure disjointness facts:
    --   the first uses the hypothesis coproduct disjointness `[a,t]` (a common point gives
    --   `·≫inl = ·≫inr`), the second uses `t` monic + `A'∩A'' ≤ 0`.  Then
    --   `complement_le_other' A' A'' (t(A''))` gives `t(A'') ≤ A''`, the wanted restriction.
    -- ── the three monic subobjects.  a, t monic ⟹ a, A'.arr≫t, A''.arr≫t monic.
    have ha_mono : Monic a := mono_from_one a
    let aSub : Subobject 𝒞 A := Subobject.mk one a ha_mono
    let tA' : Subobject 𝒞 A := Subobject.mk A'.dom (A'.arr ≫ t) (mono_comp'' A'.monic htmono)
    let tA'' : Subobject 𝒞 A := Subobject.mk A''.dom (A''.arr ≫ t) (mono_comp'' A''.monic htmono)
    -- ── basic `≤`-facts.
    have haSub_le : aSub.le A' := ⟨a₀, ha₀⟩
    have htA'_le : tA'.le A' := ⟨t', ht'⟩
    -- the union `U := a(1) ∪ t(A')`.
    let U : Subobject 𝒞 A := HasSubobjectUnions.union aSub tA'
    -- ── `U ≤ A'` (both summands ≤ A').
    have hUA' : U.le A' := HasSubobjectUnions.union_min _ _ _ haSub_le htA'_le
    -- ── `A' ≤ U`: `U` is `(a,t)`-closed, leastness gives it.
    have hA'U : A'.le U := by
      refine HasLeastClosedSubobject.least_le a t U ⟨?_, ?_⟩
      · -- `U` allows `a`: `a = aSub.arr` factors through `aSub ≤ U`.
        obtain ⟨l, hl⟩ := HasSubobjectUnions.union_left aSub tA'
        exact ⟨l, by show l ≫ U.arr = a; rw [hl]⟩
      · -- `U` is t-stable: `image (U.arr ≫ t) ≤ U`, then descend to a restriction.
        -- cover `c : coprod aSub.dom tA'.dom → U.dom`, `c ≫ U.arr = case aSub.arr tA'.arr`.
        obtain ⟨l₁, hl₁⟩ := HasSubobjectUnions.union_left aSub tA'
        obtain ⟨l₂, hl₂⟩ := HasSubobjectUnions.union_right aSub tA'
        have hUimg : IsImage (HasBinaryCoproducts.case aSub.arr tA'.arr) U := union_is_image aSub tA'
        obtain ⟨c, hc⟩ := hUimg.1
        have hcov : Cover (HasBinaryCoproducts.case l₁ l₂) := union_case_cover aSub tA' hl₁ hl₂
        -- `case l₁ l₂ ≫ U.arr = case aSub.arr tA'.arr` (both legs match), so `c = case l₁ l₂`-cover.
        have hcU : HasBinaryCoproducts.case l₁ l₂ ≫ U.arr
            = HasBinaryCoproducts.case aSub.arr tA'.arr := by
          rw [case_comp, hl₁, hl₂]
        -- `image (U.arr ≫ t) ≤ image (case aSub.arr tA'.arr ≫ t)` via the cover `case l₁ l₂`.
        -- `(case l₁ l₂) ≫ (U.arr ≫ t) = (case aSub.arr tA'.arr) ≫ t = case (aSub.arr≫t)(tA'.arr≫t)`.
        have hcomp : HasBinaryCoproducts.case l₁ l₂ ≫ (U.arr ≫ t)
            = HasBinaryCoproducts.case (aSub.arr ≫ t) (tA'.arr ≫ t) := by
          rw [← Cat.assoc, hcU, case_comp]
        have himg_le : (image (U.arr ≫ t)).le U := by
          -- `image(U.arr≫t) = image(case l₁ l₂ ≫ (U.arr≫t))` (cover-precompose) ≤ union of legs ≤ U.
          have h1 : (image (U.arr ≫ t)).le
              (image (HasBinaryCoproducts.case l₁ l₂ ≫ (U.arr ≫ t))) :=
            (image_cover_comp (HasBinaryCoproducts.case l₁ l₂) (U.arr ≫ t) hcov).2
          rw [hcomp] at h1
          -- `image (case (aSub.arr≫t)(tA'.arr≫t)) ≤ (image (aSub.arr≫t)) ∪ (image (tA'.arr≫t))`:
          -- each leg factors through its own image ≤ the union, copair to factor `case`.
          have h2 : (image (HasBinaryCoproducts.case (aSub.arr ≫ t) (tA'.arr ≫ t))).le
              (HasSubobjectUnions.union (image (aSub.arr ≫ t)) (image (tA'.arr ≫ t))) := by
            obtain ⟨jL, hjL⟩ := HasSubobjectUnions.union_left
              (image (aSub.arr ≫ t)) (image (tA'.arr ≫ t))
            obtain ⟨jR, hjR⟩ := HasSubobjectUnions.union_right
              (image (aSub.arr ≫ t)) (image (tA'.arr ≫ t))
            refine image_min _ _ ⟨HasBinaryCoproducts.case
              (image.lift (aSub.arr ≫ t) ≫ jL) (image.lift (tA'.arr ≫ t) ≫ jR), ?_⟩
            have egL : (image.lift (aSub.arr ≫ t) ≫ jL)
                ≫ (HasSubobjectUnions.union (image (aSub.arr ≫ t)) (image (tA'.arr ≫ t))).arr
                = aSub.arr ≫ t := by rw [Cat.assoc, hjL, image.lift_fac]
            have egR : (image.lift (tA'.arr ≫ t) ≫ jR)
                ≫ (HasSubobjectUnions.union (image (aSub.arr ≫ t)) (image (tA'.arr ≫ t))).arr
                = tA'.arr ≫ t := by rw [Cat.assoc, hjR, image.lift_fac]
            rw [case_comp, egL, egR]
          -- each leg-image ≤ U.  `tA' ≤ U` is `union_right` (NOT via `A' ≤ U`, which is circular).
          have htA'_U : tA'.le U := HasSubobjectUnions.union_right aSub tA'
          have h3 : (image (aSub.arr ≫ t)).le U := by
            -- a(1)≫t = a₀ ≫ (A'.arr≫t) = a₀ ≫ tA'.arr, so image ≤ tA' ≤ U.
            refine subLe_trans' (image_min (aSub.arr ≫ t) tA' ⟨a₀, ?_⟩) htA'_U
            show a₀ ≫ (A'.arr ≫ t) = a ≫ t
            rw [← Cat.assoc, ha₀]
          have h4 : (image (tA'.arr ≫ t)).le U := by
            -- t(A')≫t ⊆ t(A') since tA' ≤ A' (image_post_mono) and image(A'.arr≫t)=tA'.
            refine subLe_trans' (image_post_mono t htA'_le) ?_
            exact subLe_trans' (image_mono_eq (A'.arr ≫ t) (mono_comp'' A'.monic htmono)).1
              htA'_U
          exact subLe_trans' h1 (subLe_trans' h2
            (HasSubobjectUnions.union_min _ _ _ h3 h4))
        -- descend `image(U.arr≫t) ≤ U` to a restriction `tU : U.dom → U.dom`.
        obtain ⟨k, hk⟩ := himg_le
        exact ⟨image.lift (U.arr ≫ t) ≫ k, by
          rw [Cat.assoc, hk, image.lift_fac]⟩
    -- ── `t(A'') ∩ A' ≤ 0`, via `A' ≤ U = a(1) ∪ t(A')` and distributivity.
    have hdisj' : (Subobject.inter A' (image (A''.arr ≫ t))).le (PreLogos.bottom A) := by
      -- `image(A''.arr≫t) = tA''` (image of monic), so it suffices on `tA''`.
      have heq : (image (A''.arr ≫ t)).le tA'' :=
        (image_mono_eq (A''.arr ≫ t) (mono_comp'' A''.monic htmono)).1
      -- `inter A' (image ..) ≤ inter U tA'' ≤ inter tA'' U` (monotone + commute).
      have hmono_inter : (Subobject.inter A' (image (A''.arr ≫ t))).le
          (Subobject.inter tA'' U) :=
        subLe_trans' (Subobject.inter_mono hA'U heq) (inter_comm_le U tA'')
      -- distribute `inter tA'' U = inter tA'' (aSub ∪ tA') ≤ (tA'' ∩ aSub) ∪ (tA'' ∩ tA')`.
      have hdist : (Subobject.inter tA'' U).le
          (HasSubobjectUnions.union (Subobject.inter tA'' aSub) (Subobject.inter tA'' tA')) := by
        have e1 : Subobject.inter tA'' U
            = pushMono tA''.arr tA''.monic (InverseImage tA''.arr U) := rfl
        have e2 : Subobject.inter tA'' aSub
            = pushMono tA''.arr tA''.monic (InverseImage tA''.arr aSub) := rfl
        have e3 : Subobject.inter tA'' tA'
            = pushMono tA''.arr tA''.monic (InverseImage tA''.arr tA') := rfl
        rw [e1, e2, e3]
        have hpre : (InverseImage tA''.arr U).le
            (HasSubobjectUnions.union (InverseImage tA''.arr aSub) (InverseImage tA''.arr tA')) :=
          (PreLogos.invImage_preserves_union tA''.arr aSub tA').1
        exact subLe_trans' (pushMono_mono tA''.arr tA''.monic hpre)
          (pushMono_union_le tA''.arr tA''.monic _ _)
      -- `tA'' ∩ aSub ≤ 0`  (t(A'') ∩ a(1): hypothesis-coproduct disjointness).
      have hbot1 : (Subobject.inter tA'' aSub).le (PreLogos.bottom A) := by
        -- projections π₁ : pt → A''.dom, π₂ : pt → one with π₁≫(A''.arr≫t) = π₂≫a.
        let pb := HasPullbacks.has tA''.arr aSub.arr
        have hsq : pb.cone.π₁ ≫ tA''.arr = pb.cone.π₂ ≫ aSub.arr := pb.cone.w
        -- t = inr≫case, a = inl≫case ⟹ (π₁≫A''.arr)≫inr = π₂≫inl, cancel case (iso).
        have hcancel : pb.cone.π₂ ≫ HasBinaryCoproducts.inl
            = (pb.cone.π₁ ≫ A''.arr) ≫ HasBinaryCoproducts.inr := by
          -- π₂≫a = π₁≫(A''.arr≫t)  (the pullback square, `aSub.arr=a`, `tA''.arr=A''.arr≫t`).
          have hsq' : pb.cone.π₂ ≫ a = (pb.cone.π₁ ≫ A''.arr) ≫ t := by
            rw [Cat.assoc]; exact hsq.symm
          -- post-compose both `·≫case a t` agree, then cancel `case` (iso) by `·≫ci`.
          have hc : (pb.cone.π₂ ≫ HasBinaryCoproducts.inl) ≫ HasBinaryCoproducts.case a t
              = ((pb.cone.π₁ ≫ A''.arr) ≫ HasBinaryCoproducts.inr) ≫ HasBinaryCoproducts.case a t
              := by rw [Cat.assoc, Cat.assoc, hcl, hcr]; exact hsq'
          -- cancel the iso `case a t` on the right via `· ≫ ci`.
          calc pb.cone.π₂ ≫ HasBinaryCoproducts.inl
              = ((pb.cone.π₂ ≫ HasBinaryCoproducts.inl) ≫ HasBinaryCoproducts.case a t) ≫ ci := by
                rw [Cat.assoc, hci1, Cat.comp_id]
            _ = (((pb.cone.π₁ ≫ A''.arr) ≫ HasBinaryCoproducts.inr)
                  ≫ HasBinaryCoproducts.case a t) ≫ ci := by rw [hc]
            _ = (pb.cone.π₁ ≫ A''.arr) ≫ HasBinaryCoproducts.inr := by
                rw [Cat.assoc, hci1, Cat.comp_id]
        exact hbot_hyp (Subobject.inter tA'' aSub) pb.cone.π₂ (pb.cone.π₁ ≫ A''.arr) hcancel
      -- `tA'' ∩ tA' ≤ 0`  (t(A'') ∩ t(A'): `t` monic descends to `A' ∩ A'' ≤ 0`).
      have hbot2 : (Subobject.inter tA'' tA').le (PreLogos.bottom A) := by
        let pb := HasPullbacks.has tA''.arr tA'.arr
        have hsq : pb.cone.π₁ ≫ tA''.arr = pb.cone.π₂ ≫ tA'.arr := pb.cone.w
        -- (π₁≫A''.arr)≫t = (π₂≫A'.arr)≫t ⟹ (t monic) π₁≫A''.arr = π₂≫A'.arr : common pt of A'',A'.
        have hcommon : pb.cone.π₂ ≫ A'.arr = pb.cone.π₁ ≫ A''.arr := by
          apply htmono
          show (pb.cone.π₂ ≫ A'.arr) ≫ t = (pb.cone.π₁ ≫ A''.arr) ≫ t
          rw [Cat.assoc, Cat.assoc]; exact hsq.symm
        -- lift into `inter A' A''`; `hdisj` maps it to ⊥; `peano_le_bottom_of_map`.
        let pbAA := HasPullbacks.has A'.arr A''.arr
        let w : (Subobject.inter tA'' tA').dom ⟶ (Subobject.inter A' A'').dom :=
          pbAA.lift ⟨_, pb.cone.π₂, pb.cone.π₁, hcommon⟩
        obtain ⟨m, _⟩ := hdisj
        exact peano_le_bottom_of_map (Subobject.inter tA'' tA') (w ≫ m)
      -- assemble: `inter A' (image..) ≤ inter tA'' U ≤ union(...) ≤ ⊥`.
      exact subLe_trans' hmono_inter (subLe_trans' hdist
        (HasSubobjectUnions.union_min _ _ _ hbot1 hbot2))
    -- `complement_le_other'` gives `t(A'') ≤ A''`; descend to the restriction `t''`.
    have htle : (image (A''.arr ≫ t)).le A'' :=
      complement_le_other' A' A'' (image (A''.arr ≫ t)) hdisj' hentire
    obtain ⟨k, hk⟩ := htle
    exact ⟨image.lift (A''.arr ≫ t) ≫ k, by rw [Cat.assoc, hk, image.lift_fac]⟩
  obtain ⟨t'', ht''⟩ := hclaim
  -- ── Characteristic map `e : A → Two` (Two = 1+1, canonical disjoint topos coproduct):
  -- `A'` ↦ inl, `A''` ↦ inr.  Built through `ψ⁻¹` and the hypothesis-coproduct copairing.
  let Two : 𝒞 := coprodObj one one
  let inlT : (one : 𝒞) ⟶ Two := coprodInl one one
  let inrT : (one : 𝒞) ⟶ Two := coprodInr one one
  let e : A ⟶ Two :=
    ψinv ≫ HasBinaryCoproducts.case (term A'.dom ≫ inlT) (term A''.dom ≫ inrT)
  -- `A'.arr ≫ e = term ≫ inlT`,  `A''.arr ≫ e = term ≫ inrT`.
  have heA' : A'.arr ≫ e = term A'.dom ≫ inlT := by
    show A'.arr ≫ ψinv ≫ _ = _
    rw [← hψinl, Cat.assoc, ← Cat.assoc ψ ψinv, hψ1, Cat.id_comp,
        HasBinaryCoproducts.case_inl]
  have heA'' : A''.arr ≫ e = term A''.dom ≫ inrT := by
    show A''.arr ≫ ψinv ≫ _ = _
    rw [← hψinr, Cat.assoc, ← Cat.assoc ψ ψinv, hψ1, Cat.id_comp,
        HasBinaryCoproducts.case_inr]
  -- ── `t`-invariance of `e`:  `t ≫ e = e`.  Check on the two summands via `ψ` (epi).
  have hte : t ≫ e = e := by
    -- It suffices to show `ψ ≫ (t ≫ e) = ψ ≫ e`, since `ψ` is (split) epi via `ψinv ≫ ψ = id`.
    have hcancel : ψ ≫ (t ≫ e) = ψ ≫ e → t ≫ e = e := by
      intro h
      have := congrArg (ψinv ≫ ·) h
      simpa only [← Cat.assoc, hψ2, Cat.id_comp] using this
    apply hcancel
    -- `ψ ≫ _` is determined by its `inl`/`inr` legs (joint epi of the coproduct injections).
    have hext : ∀ (X Y : HasBinaryCoproducts.coprod A'.dom A''.dom ⟶ Two),
        HasBinaryCoproducts.inl ≫ X = HasBinaryCoproducts.inl ≫ Y →
        HasBinaryCoproducts.inr ≫ X = HasBinaryCoproducts.inr ≫ Y → X = Y := by
      intro X Y hl hr
      rw [HasBinaryCoproducts.case_uniq (HasBinaryCoproducts.inl ≫ X)
            (HasBinaryCoproducts.inr ≫ X) X rfl rfl,
          HasBinaryCoproducts.case_uniq (HasBinaryCoproducts.inl ≫ X)
            (HasBinaryCoproducts.inr ≫ X) Y hl.symm hr.symm]
    apply hext
    · -- inl: (inl≫ψ)≫t≫e = A'.arr≫t≫e = (t'≫A'.arr)≫e = term≫inlT = A'.arr≫e = (inl≫ψ)≫e.
      calc HasBinaryCoproducts.inl ≫ ψ ≫ (t ≫ e)
          = (HasBinaryCoproducts.inl ≫ ψ) ≫ (t ≫ e) := (Cat.assoc _ _ _).symm
        _ = A'.arr ≫ t ≫ e := by rw [hψinl]
        _ = (A'.arr ≫ t) ≫ e := (Cat.assoc _ _ _).symm
        _ = (t' ≫ A'.arr) ≫ e := by rw [ht']
        _ = t' ≫ (A'.arr ≫ e) := Cat.assoc _ _ _
        _ = t' ≫ (term A'.dom ≫ inlT) := by rw [heA']
        _ = (t' ≫ term A'.dom) ≫ inlT := (Cat.assoc _ _ _).symm
        _ = term A'.dom ≫ inlT := by rw [term_uniq (t' ≫ term A'.dom) (term A'.dom)]
        _ = A'.arr ≫ e := heA'.symm
        _ = (HasBinaryCoproducts.inl ≫ ψ) ≫ e := by rw [hψinl]
        _ = HasBinaryCoproducts.inl ≫ ψ ≫ e := Cat.assoc _ _ _
    · -- inr: (inr≫ψ)≫t≫e = A''.arr≫t≫e = (t''≫A''.arr)≫e = term≫inrT = A''.arr≫e = (inr≫ψ)≫e.
      calc HasBinaryCoproducts.inr ≫ ψ ≫ (t ≫ e)
          = (HasBinaryCoproducts.inr ≫ ψ) ≫ (t ≫ e) := (Cat.assoc _ _ _).symm
        _ = A''.arr ≫ t ≫ e := by rw [hψinr]
        _ = (A''.arr ≫ t) ≫ e := (Cat.assoc _ _ _).symm
        _ = (t'' ≫ A''.arr) ≫ e := by rw [ht'']
        _ = t'' ≫ (A''.arr ≫ e) := Cat.assoc _ _ _
        _ = t'' ≫ (term A''.dom ≫ inrT) := by rw [heA'']
        _ = (t'' ≫ term A''.dom) ≫ inrT := (Cat.assoc _ _ _).symm
        _ = term A''.dom ≫ inrT := by rw [term_uniq (t'' ≫ term A''.dom) (term A''.dom)]
        _ = A''.arr ≫ e := heA''.symm
        _ = (HasBinaryCoproducts.inr ≫ ψ) ≫ e := by rw [hψinr]
        _ = HasBinaryCoproducts.inr ≫ ψ ≫ e := Cat.assoc _ _ _
  -- ── Coequalizer: `e` is `t`-invariant, so factors `e = term A ≫ g` for a unique `g : 1 → Two`.
  obtain ⟨g, hg, _hguniq⟩ := hcoeq Two e hte
  -- `g = inlT` (the `A'`-value), because `A'` allows `a`.
  have hg_inl : g = inlT := by
    -- a ≫ e = a₀ ≫ A'.arr ≫ e = a₀ ≫ term A'.dom ≫ inlT = term one ≫ inlT = inlT
    -- a ≫ e = a ≫ term A ≫ g = term one ≫ g = g.  (term one = id one.)
    have htid : term (one : 𝒞) = Cat.id one := term_uniq _ _
    have h1 : a ≫ e = inlT := by
      rw [← ha₀, Cat.assoc, heA', ← Cat.assoc,
          term_uniq (a₀ ≫ term A'.dom) (term one), htid, Cat.id_comp]
    have h2 : a ≫ e = g := by
      rw [← hg, ← Cat.assoc, term_uniq (a ≫ term A) (term one), htid, Cat.id_comp]
    rw [← h2, h1]
  -- ── `A''.arr ≫ e = term A''.dom ≫ inrT`, but also `= term A''.dom ≫ g = term A''.dom ≫ inlT`.
  -- So `term A''.dom ≫ inlT = term A''.dom ≫ inrT` : a common point of inlT, inrT — `A''.dom` initial.
  have hcommon : term A''.dom ≫ inlT = term A''.dom ≫ inrT := by
    have hgInr : A''.arr ≫ e = term A''.dom ≫ g := by
      rw [← hg, ← Cat.assoc, term_uniq (A''.arr ≫ term A) (term A''.dom)]
    rw [hg_inl] at hgInr
    rw [← hgInr, heA'']
  -- `inlT`, `inrT` are the disjoint canonical injections: a common point makes `A''.dom → 0`.
  -- A common point of the disjoint canonical injections `inlT, inrT` makes `A''.dom` initial.
  have hcommon' : term A''.dom ≫ coprodInl (one : 𝒞) one
      = term A''.dom ≫ coprodInr (one : 𝒞) one := hcommon
  have hAinit : ∀ {Y : 𝒞} (u v : A''.dom ⟶ Y), u = v :=
    coprodInjections_disjoint_elt (term A''.dom) (term A''.dom) hcommon'
  -- ── `A''.dom` initial ⟹ `inl : A'.dom → A'.dom+A''.dom` is iso ⟹ `A'.arr = inl ≫ ψ` is iso.
  -- Inverse of `inl` is `case (id A'.dom) k` for ANY `k : A''.dom → A'.dom` (here `term ≫ a₀`):
  -- `inl ≫ case id k = id`; and `case id k ≫ inl = id` checking legs (the `inr`-leg uses that
  -- `A''.dom` is initial, so `k ≫ inl = inr`).
  show IsIso A'.arr
  have hinl_iso : IsIso (HasBinaryCoproducts.inl (A := A'.dom) (B := A''.dom)) := by
    refine ⟨HasBinaryCoproducts.case (Cat.id A'.dom) (term A''.dom ≫ a₀), ?_, ?_⟩
    · exact HasBinaryCoproducts.case_inl _ _
    · -- `case id k ≫ inl = id`: both sides equal `case inl inr` (the coproduct identity).
      have hid : Cat.id (HasBinaryCoproducts.coprod A'.dom A''.dom)
          = HasBinaryCoproducts.case HasBinaryCoproducts.inl HasBinaryCoproducts.inr :=
        HasBinaryCoproducts.case_uniq _ _ _ (Cat.comp_id _) (Cat.comp_id _)
      rw [hid]
      apply HasBinaryCoproducts.case_uniq
      · rw [← Cat.assoc, HasBinaryCoproducts.case_inl, Cat.id_comp]
      · rw [← Cat.assoc]; exact hAinit _ _
  -- `A'.arr = inl ≫ ψ`; both iso, so `A'.arr` iso.
  rw [← hψinl]; exact isIso_comp hinl_iso ⟨ψinv, hψ1, hψ2⟩

/-- **§1.989 helper — a subobject with no global point is `⊥`** (needs CAPITAL + TWO-VALUED).
    If `S ↣ A` admits no point `1 → A` factoring through it, then `S ≤ ⊥ A`.

    Proof by two-valuedness of `Sub(1)`: case on whether `Support S.dom = image(S.dom → 1) ⊆ 1`
    is entire (`wellSupported_iff_support_entire`).
    * ENTIRE ⟹ `WellSupported S.dom`, i.e. `term S.dom : S.dom ↠ 1` is a cover.  In a CAPITAL
      category 1 is projective (`capital_one_projective`), so that cover splits: a point
      `s : 1 → S.dom`.  Then `s ≫ S.arr : 1 → A` is a global point through `S` — contradicting
      the no-point hypothesis.  (Vacuously closes the goal.)
    * NOT entire ⟹ `Support S.dom ↣ 1` is a PROPER mono.  TWO-VALUEDNESS (`htv.zero_uniq`)
      forces `Support S.dom ≅ htv.zeroObj`.  The image cover `S.dom ↠ Support S.dom` composed
      into `htv.zeroObj` is a map *into* the strict coterminator `htv.zeroObj` (`htv.zero_strict`),
      hence iso ⟹ `S.dom ≅ htv.zeroObj ≅ (⊥ A).dom` ⟹ `S ≤ ⊥ A` (`le_bottom_of_dom_iso`). -/
theorem noPoint_le_bottom {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞] [HasImages 𝒞]
    (hcap : Capital (𝒞 := 𝒞)) (htv : TwoValued (𝒞 := 𝒞))
    {A : 𝒞} (S : Subobject 𝒞 A)
    (hnp : ∀ x : one ⟶ A, ¬ ∃ y : one ⟶ S.dom, y ≫ S.arr = x) :
    S.le (PreLogos.bottom A) := by
  classical
  by_cases hent : Subobject.IsEntire (Support S.dom)
  · -- ENTIRE: `S.dom` is well-supported, so `term S.dom` is a cover; capital splits it.
    have hws : WellSupported S.dom := (wellSupported_iff_support_entire S.dom).2 hent
    obtain ⟨s, _⟩ := capital_one_projective hcap hws
    -- `s : 1 → S.dom`; `s ≫ S.arr` is a global point through `S` — contradiction.
    exact absurd ⟨s, rfl⟩ (hnp (s ≫ S.arr))
  · -- NOT entire: `Support S.dom ↣ 1` is a PROPER mono ⟹ (two-valued) `≅ htv.zeroObj`.
    -- `(Support S.dom).arr` and `term (Support S.dom).dom` are the same map (both `→ 1`).
    have hproper : ProperMono (term (Support S.dom).dom) := by
      have harr : (Support S.dom).arr = term (Support S.dom).dom := term_uniq _ _
      rw [← harr]; exact ⟨(Support S.dom).monic, hent⟩
    obtain ⟨e, _⟩ := htv.zero_uniq (Support S.dom).dom hproper
    -- `S.dom ↠ Support S.dom → htv.zeroObj`: a map INTO the strict coterminator, hence iso.
    have hSiso : IsIso (image.lift (term S.dom) ≫ e) := htv.zero_strict _
    -- `htv.zeroObj` is a strict coterminator (`htv.zero_strict`), hence initial: a map
    -- `htv.zeroObj → (⊥ one).dom`.  Compose `S.dom ≅ htv.zeroObj → (⊥ one).dom`, then `≤ ⊥`.
    letI hCot0 : HasCoterminator 𝒞 := HasCoterminator.ofStrict (fun {X} f => htv.zero_strict f)
    exact peano_le_bottom_of_map (W := one) S
      ((image.lift (term S.dom) ≫ e) ≫ hCot0.init (PreLogos.bottom one).dom)

/-- **A `⊥`-domain has NO global point** (NON-degeneracy from TWO-VALUEDNESS).  A point
    `1 → (⊥ B).dom` would make `(⊥ B).dom ≅ 0 ≅ 1` (the bottom dom is strict-initial), i.e.
    the category degenerate — contradicting `htv.zero_proper` (`0 ↣ 1` is a PROPER mono, so
    `0 ≇ 1`).  This is the "no point ⟹ ⊥" half's dual: a point of `⊥` is absurd. -/
theorem point_bottom_absurd {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞] [HasImages 𝒞]
    (htv : TwoValued (𝒞 := 𝒞)) {B : 𝒞} (z : (one : 𝒞) ⟶ (PreLogos.bottom B).dom) : False := by
  -- `(⊥ B).dom` is initial; map it into the strict coterminator `htv.zeroObj`.
  letI hCotB := minimal_subobject_of_one_is_coterminator (inferInstance : PreLogos 𝒞)
  -- `(⊥ B).dom ≅ (⊥ one).dom = hCotB.zero`; postcompose the initial map to `htv.zeroObj`.
  have hbot0 : Isomorphic (PreLogos.bottom B).dom hCotB.zero :=
    PreLogos.bottom_dom_iso B (HasTerminal.one)
  obtain ⟨φ, _⟩ := hbot0
  -- point of `htv.zeroObj`: `1 → (⊥B).dom → hCotB.zero → htv.zeroObj`.
  let p0 : (one : 𝒞) ⟶ htv.zeroObj := z ≫ φ ≫ hCotB.init htv.zeroObj
  -- `p0 : 1 → htv.zeroObj` is a SECTION of `term htv.zeroObj`, and `term ≫ p0 = id` since
  -- `htv.zeroObj` is initial (`strictCoterminator_hom_unique`).  So `term htv.zeroObj` is iso.
  have hstrict : StrictCoterminator htv.zeroObj := fun {X} f => htv.zero_strict f
  exact htv.zero_proper.2
    ⟨p0, strictCoterminator_hom_unique hstrict _ _, term_uniq _ _⟩

/-- **A subobject of `1` either HAS a global point or is `≤ ⊥`** (the `Sub(1)` two-valued
    dichotomy, from CAPITAL + TWO-VALUED).  Over `1` a point `s : 1 → U.dom` automatically
    splits `U.arr` (`s ≫ U.arr = id` by `term_uniq`), so "has a point" is the positive case;
    `noPoint_le_bottom` supplies the negative `≤ ⊥` case. -/
theorem sub_one_point_or_bot {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    (hcap : Capital (𝒞 := 𝒞)) (htv : TwoValued (𝒞 := 𝒞)) (U : Subobject 𝒞 (one : 𝒞)) :
    Nonempty ((one : 𝒞) ⟶ U.dom) ∨ U.le (PreLogos.bottom one) := by
  classical
  by_cases h : Nonempty ((one : 𝒞) ⟶ U.dom)
  · exact Or.inl h
  · refine Or.inr (noPoint_le_bottom hcap htv U ?_)
    intro x ⟨y, _⟩; exact h ⟨y⟩

/-- **COPRODUCT POINT-DECOMPOSITION (canonical coproduct).**  In a CAPITAL + TWO-VALUED topos,
    any global point `x : 1 → A+B` of the canonical coproduct factors through `coprodInl` or
    through `coprodInr`.  Proof: the inverse images `U := x#(image inl)` and `V := x#(image inr)`
    are subobjects of `1` whose union is ENTIRE (`coprodInjections_union_entire` pulled back, via
    `entire_le_invImage_entire` + `invImage_preserves_union`).  By `sub_one_point_or_bot` each is
    point-or-`⊥`; if both were `≤ ⊥` their union would be `≤ ⊥`, forcing a point of `(⊥ 1).dom`
    (`point_bottom_absurd`).  So one has a point, and a point of an inverse image lifts `x`
    through that injection. -/
theorem coprod_point_split_canonical {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    (hcap : Capital (𝒞 := 𝒞)) (htv : TwoValued (𝒞 := 𝒞)) {A B : 𝒞}
    (x : (one : 𝒞) ⟶ coprodObj A B) :
    (∃ u : (one : 𝒞) ⟶ A, x = u ≫ coprodInl A B) ∨
      (∃ v : (one : 𝒞) ⟶ B, x = v ≫ coprodInr A B) := by
  classical
  let U : Subobject 𝒞 (one : 𝒞) := InverseImage x (inlSubobj A B)
  let V : Subobject 𝒞 (one : 𝒞) := InverseImage x (inrSubobj A B)
  -- `entire 1 ≤ U ∪ V` (pull the entire union `inlSub ∪ inrSub = ⊤` back along `x`).
  have hUVtop : (Subobject.entire (one : 𝒞)).le (HasSubobjectUnions.union U V) := by
    have hunion_top : (Subobject.entire (coprodObj A B)).le
        (HasSubobjectUnions.union (inlSubobj A B) (inrSubobj A B)) := by
      obtain ⟨ι, _, hι⟩ := coprodInjections_union_entire A B
      exact ⟨ι, by simpa using hι⟩
    have h1 : (Subobject.entire (one : 𝒞)).le
        (InverseImage x (Subobject.entire (coprodObj A B))) := entire_le_invImage_entire x
    have h2 : (InverseImage x (Subobject.entire (coprodObj A B))).le
        (InverseImage x (HasSubobjectUnions.union (inlSubobj A B) (inrSubobj A B))) :=
      inverseImage_mono x hunion_top
    have h3 : (InverseImage x (HasSubobjectUnions.union (inlSubobj A B) (inrSubobj A B))).le
        (HasSubobjectUnions.union U V) :=
      (PreLogos.invImage_preserves_union x (inlSubobj A B) (inrSubobj A B)).1
    exact subLe_trans' h1 (subLe_trans' h2 h3)
  -- a point of `U` lifts `x` through `coprodInl` (the pullback square `π₁ ≫ x = π₂ ≫ inl`).
  rcases sub_one_point_or_bot hcap htv U with hUpt | hUbot
  · obtain ⟨s⟩ := hUpt
    refine Or.inl ⟨s ≫ (HasPullbacks.has x (inlSubobj A B).arr).cone.π₂, ?_⟩
    have hsq := (HasPullbacks.has x (inlSubobj A B).arr).cone.w
    have hsU : s ≫ (HasPullbacks.has x (inlSubobj A B).arr).cone.π₁ = Cat.id one :=
      term_uniq _ _
    calc x = Cat.id one ≫ x := (Cat.id_comp _).symm
      _ = (s ≫ (HasPullbacks.has x (inlSubobj A B).arr).cone.π₁) ≫ x := by rw [hsU]
      _ = s ≫ ((HasPullbacks.has x (inlSubobj A B).arr).cone.π₁ ≫ x) := Cat.assoc _ _ _
      _ = s ≫ ((HasPullbacks.has x (inlSubobj A B).arr).cone.π₂ ≫ (inlSubobj A B).arr) := by
            rw [hsq]
      _ = (s ≫ (HasPullbacks.has x (inlSubobj A B).arr).cone.π₂) ≫ coprodInl A B :=
            (Cat.assoc _ _ _).symm
  rcases sub_one_point_or_bot hcap htv V with hVpt | hVbot
  · obtain ⟨s⟩ := hVpt
    refine Or.inr ⟨s ≫ (HasPullbacks.has x (inrSubobj A B).arr).cone.π₂, ?_⟩
    have hsq := (HasPullbacks.has x (inrSubobj A B).arr).cone.w
    have hsV : s ≫ (HasPullbacks.has x (inrSubobj A B).arr).cone.π₁ = Cat.id one :=
      term_uniq _ _
    calc x = Cat.id one ≫ x := (Cat.id_comp _).symm
      _ = (s ≫ (HasPullbacks.has x (inrSubobj A B).arr).cone.π₁) ≫ x := by rw [hsV]
      _ = s ≫ ((HasPullbacks.has x (inrSubobj A B).arr).cone.π₁ ≫ x) := Cat.assoc _ _ _
      _ = s ≫ ((HasPullbacks.has x (inrSubobj A B).arr).cone.π₂ ≫ (inrSubobj A B).arr) := by
            rw [hsq]
      _ = (s ≫ (HasPullbacks.has x (inrSubobj A B).arr).cone.π₂) ≫ coprodInr A B :=
            (Cat.assoc _ _ _).symm
  -- both `≤ ⊥`: their union is `≤ ⊥`, so `entire 1 ≤ ⊥`, giving a point of `(⊥ 1).dom` — absurd.
  exfalso
  have hunion_bot : (HasSubobjectUnions.union U V).le (PreLogos.bottom one) :=
    HasSubobjectUnions.union_min _ _ _ hUbot hVbot
  obtain ⟨z, _⟩ := subLe_trans' hUVtop hunion_bot
  exact point_bottom_absurd htv (Cat.id one ≫ z)

/-- **COPRODUCT POINT-DECOMPOSITION (abstract `HasBinaryCoproducts`).**  Transport of
    `coprod_point_split_canonical` to ANY `[HasBinaryCoproducts 𝒞]` instance via the coproduct
    UNIQUENESS iso `φ := case coprodInl coprodInr : abstract.coprod A B → A+B(canonical)` (with
    inverse the canonical copairing of the abstract injections, `case_morphism_exists`).  Since
    `φ` commutes with the injections (`inl ≫ φ = coprodInl`, etc.), a point `w` of the abstract
    coproduct maps to the canonical point `w ≫ φ`, which splits; pulling the factorization back
    through `φ⁻¹` (which sends `coprodInl ↦ inl`) splits `w`. -/
theorem coprod_point_split {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞] [HasBinaryCoproducts 𝒞]
    (hcap : Capital (𝒞 := 𝒞)) (htv : TwoValued (𝒞 := 𝒞)) {A B : 𝒞}
    (w : (one : 𝒞) ⟶ HasBinaryCoproducts.coprod A B) :
    (∃ u : (one : 𝒞) ⟶ A, w = u ≫ HasBinaryCoproducts.inl) ∨
      (∃ v : (one : 𝒞) ⟶ B, w = v ≫ HasBinaryCoproducts.inr) := by
  classical
  -- `φ : abstract.coprod A B → A+B(canonical)`; `ψ : A+B(canonical) → abstract.coprod A B`.
  let φ : HasBinaryCoproducts.coprod A B ⟶ coprodObj A B :=
    HasBinaryCoproducts.case (coprodInl A B) (coprodInr A B)
  obtain ⟨ψ, hψl, hψr⟩ := case_morphism_exists
    (HasBinaryCoproducts.inl (A := A) (B := B)) (HasBinaryCoproducts.inr (A := A) (B := B))
  -- `φ` commutes with injections.
  have hφl : HasBinaryCoproducts.inl (A := A) (B := B) ≫ φ = coprodInl A B :=
    HasBinaryCoproducts.case_inl _ _
  have hφr : HasBinaryCoproducts.inr (A := A) (B := B) ≫ φ = coprodInr A B :=
    HasBinaryCoproducts.case_inr _ _
  -- `coprodInl ≫ ψ = inl` (and `inr` analogue), the inverse legs.
  -- `φ⁻¹` carries each canonical injection back: `coprodInl ≫ ψ = inl`.
  -- `w` maps to the canonical point `w ≫ φ`; split it.
  rcases coprod_point_split_canonical hcap htv (w ≫ φ) with ⟨u, hu⟩ | ⟨v, hv⟩
  · -- `w = w ≫ φ ≫ ψ = u ≫ coprodInl ≫ ψ = u ≫ inl`.  Need `w ≫ φ ≫ ψ = w`.
    refine Or.inl ⟨u, ?_⟩
    have hround : φ ≫ ψ = Cat.id (HasBinaryCoproducts.coprod A B) := by
      rw [HasBinaryCoproducts.case_uniq (HasBinaryCoproducts.inl (A := A) (B := B))
            (HasBinaryCoproducts.inr (A := A) (B := B)) (φ ≫ ψ)
            (by rw [← Cat.assoc, hφl, hψl]) (by rw [← Cat.assoc, hφr, hψr]),
          ← HasBinaryCoproducts.case_uniq (HasBinaryCoproducts.inl (A := A) (B := B))
            (HasBinaryCoproducts.inr (A := A) (B := B)) (Cat.id _)
            (Cat.comp_id _) (Cat.comp_id _)]
    calc w = w ≫ Cat.id _ := (Cat.comp_id _).symm
      _ = w ≫ (φ ≫ ψ) := by rw [hround]
      _ = (w ≫ φ) ≫ ψ := (Cat.assoc _ _ _).symm
      _ = (u ≫ coprodInl A B) ≫ ψ := by rw [hu]
      _ = u ≫ (coprodInl A B ≫ ψ) := Cat.assoc _ _ _
      _ = u ≫ HasBinaryCoproducts.inl := by rw [hψl]
  · refine Or.inr ⟨v, ?_⟩
    have hround : φ ≫ ψ = Cat.id (HasBinaryCoproducts.coprod A B) := by
      rw [HasBinaryCoproducts.case_uniq (HasBinaryCoproducts.inl (A := A) (B := B))
            (HasBinaryCoproducts.inr (A := A) (B := B)) (φ ≫ ψ)
            (by rw [← Cat.assoc, hφl, hψl]) (by rw [← Cat.assoc, hφr, hψr]),
          ← HasBinaryCoproducts.case_uniq (HasBinaryCoproducts.inl (A := A) (B := B))
            (HasBinaryCoproducts.inr (A := A) (B := B)) (Cat.id _)
            (Cat.comp_id _) (Cat.comp_id _)]
    calc w = w ≫ Cat.id _ := (Cat.comp_id _).symm
      _ = w ≫ (φ ≫ ψ) := by rw [hround]
      _ = (w ≫ φ) ≫ ψ := (Cat.assoc _ _ _).symm
      _ = (v ≫ coprodInr A B) ≫ ψ := by rw [hv]
      _ = v ≫ (coprodInr A B ≫ ψ) := Cat.assoc _ _ _
      _ = v ≫ HasBinaryCoproducts.inr := by rw [hψr]

/-- **UNION POINT-DECOMPOSITION.**  In a CAPITAL + TWO-VALUED topos, a global point `y` of a
    binary union `S ∪ T ↣ A` factors (after `(S∪T).arr`) through `S` or through `T`.  Same Sub(1)
    two-valued split as `coprod_point_split_canonical`: with `x := y ≫ (S∪T).arr`, the inverse
    images `x#S`, `x#T ⊆ 1` have entire union (`x` factors through `S∪T`, and `x#(S∪T) ≤ x#S ∪
    x#T`); `sub_one_point_or_bot` picks the non-`⊥` side, whose point lifts `x` into `S` or `T`. -/
theorem union_point_split {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    (hcap : Capital (𝒞 := 𝒞)) (htv : TwoValued (𝒞 := 𝒞)) {A : 𝒞} (S T : Subobject 𝒞 A)
    (y : (one : 𝒞) ⟶ (HasSubobjectUnions.union S T).dom) :
    (∃ d : (one : 𝒞) ⟶ S.dom, d ≫ S.arr = y ≫ (HasSubobjectUnions.union S T).arr) ∨
      (∃ k : (one : 𝒞) ⟶ T.dom, k ≫ T.arr = y ≫ (HasSubobjectUnions.union S T).arr) := by
  classical
  let x : (one : 𝒞) ⟶ A := y ≫ (HasSubobjectUnions.union S T).arr
  let U : Subobject 𝒞 (one : 𝒞) := InverseImage x S
  let V : Subobject 𝒞 (one : 𝒞) := InverseImage x T
  -- `entire 1 ≤ x#(S∪T) ≤ U ∪ V` (`x` factors through `S∪T` via `y`).
  have hUVtop : (Subobject.entire (one : 𝒞)).le (HasSubobjectUnions.union U V) := by
    have hxfac : (Subobject.entire (one : 𝒞)).le
        (InverseImage x (HasSubobjectUnions.union S T)) := by
      refine ⟨(HasPullbacks.has x (HasSubobjectUnions.union S T).arr).lift
        ⟨one, Cat.id one, y, by rw [Cat.id_comp]⟩, ?_⟩
      show _ ≫ (InverseImage x (HasSubobjectUnions.union S T)).arr = (Subobject.entire one).arr
      rw [show (Subobject.entire (one : 𝒞)).arr = Cat.id one from rfl]
      exact (HasPullbacks.has x (HasSubobjectUnions.union S T).arr).lift_fst _
    have h3 : (InverseImage x (HasSubobjectUnions.union S T)).le
        (HasSubobjectUnions.union U V) :=
      (PreLogos.invImage_preserves_union x S T).1
    exact subLe_trans' hxfac h3
  rcases sub_one_point_or_bot hcap htv U with hUpt | hUbot
  · obtain ⟨s⟩ := hUpt
    refine Or.inl ⟨s ≫ (HasPullbacks.has x S.arr).cone.π₂, ?_⟩
    have hsq := (HasPullbacks.has x S.arr).cone.w
    have hsU : s ≫ (HasPullbacks.has x S.arr).cone.π₁ = Cat.id one := term_uniq _ _
    calc (s ≫ (HasPullbacks.has x S.arr).cone.π₂) ≫ S.arr
        = s ≫ ((HasPullbacks.has x S.arr).cone.π₂ ≫ S.arr) := Cat.assoc _ _ _
      _ = s ≫ ((HasPullbacks.has x S.arr).cone.π₁ ≫ x) := by rw [hsq]
      _ = (s ≫ (HasPullbacks.has x S.arr).cone.π₁) ≫ x := (Cat.assoc _ _ _).symm
      _ = Cat.id one ≫ x := by rw [hsU]
      _ = x := Cat.id_comp _
  rcases sub_one_point_or_bot hcap htv V with hVpt | hVbot
  · obtain ⟨s⟩ := hVpt
    refine Or.inr ⟨s ≫ (HasPullbacks.has x T.arr).cone.π₂, ?_⟩
    have hsq := (HasPullbacks.has x T.arr).cone.w
    have hsV : s ≫ (HasPullbacks.has x T.arr).cone.π₁ = Cat.id one := term_uniq _ _
    calc (s ≫ (HasPullbacks.has x T.arr).cone.π₂) ≫ T.arr
        = s ≫ ((HasPullbacks.has x T.arr).cone.π₂ ≫ T.arr) := Cat.assoc _ _ _
      _ = s ≫ ((HasPullbacks.has x T.arr).cone.π₁ ≫ x) := by rw [hsq]
      _ = (s ≫ (HasPullbacks.has x T.arr).cone.π₁) ≫ x := (Cat.assoc _ _ _).symm
      _ = Cat.id one ≫ x := by rw [hsV]
      _ = x := Cat.id_comp _
  exfalso
  have hunion_bot : (HasSubobjectUnions.union U V).le (PreLogos.bottom one) :=
    HasSubobjectUnions.union_min _ _ _ hUbot hVbot
  obtain ⟨z, _⟩ := subLe_trans' hUVtop hunion_bot
  exact point_bottom_absurd htv (Cat.id one ≫ z)

/-- **§1.621 injection-disjointness at points (canonical coproduct), TWO-VALUED form.**
    Two global points identified across the injections (`u ≫ coprodInl = v ≫ coprodInr`) are
    absurd: lifting `(u,v)` into the pullback of `(coprodInl, coprodInr)` — which
    `coprodInjections_disjoint` shows is `≅ (bottomSub …).dom = (⊥ …).dom` — gives a global point
    of `(⊥ (A+B)).dom`, impossible by `point_bottom_absurd`. -/
theorem coprod_inj_disjoint_canonical_pt {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    (htv : TwoValued (𝒞 := 𝒞)) {A B : 𝒞} (u : (one : 𝒞) ⟶ A) (v : (one : 𝒞) ⟶ B)
    (huv : u ≫ coprodInl A B = v ≫ coprodInr A B) : False := by
  let pb := HasPullbacks.has (coprodInl A B) (coprodInr A B)
  let w : (one : 𝒞) ⟶ pb.cone.pt := pb.lift ⟨one, u, v, huv⟩
  obtain ⟨f0, _⟩ := coprodInjections_disjoint A B
  -- `w ≫ f0 : 1 → (bottomSub (A+B)).dom = (⊥ (A+B)).dom`.
  exact point_bottom_absurd htv (B := coprodObj A B) (w ≫ f0)

/-- **§1.621 injection-disjointness at points (abstract `HasBinaryCoproducts`).**  Transport of
    `coprod_inj_disjoint_canonical_pt` along `φ := case coprodInl coprodInr`: postcomposing
    `u ≫ inl = v ≫ inr` with `φ` (which sends `inl ↦ coprodInl`, `inr ↦ coprodInr`) yields the
    canonical identification, hence `False`. -/
theorem coprod_inj_disjoint_pt {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞] [HasBinaryCoproducts 𝒞]
    (htv : TwoValued (𝒞 := 𝒞)) {A B : 𝒞} (u : (one : 𝒞) ⟶ A) (v : (one : 𝒞) ⟶ B)
    (huv : u ≫ HasBinaryCoproducts.inl (A := A) (B := B)
         = v ≫ HasBinaryCoproducts.inr (A := A) (B := B)) : False := by
  let φ : HasBinaryCoproducts.coprod A B ⟶ coprodObj A B :=
    HasBinaryCoproducts.case (coprodInl A B) (coprodInr A B)
  have hφl : HasBinaryCoproducts.inl (A := A) (B := B) ≫ φ = coprodInl A B :=
    HasBinaryCoproducts.case_inl _ _
  have hφr : HasBinaryCoproducts.inr (A := A) (B := B) ≫ φ = coprodInr A B :=
    HasBinaryCoproducts.case_inr _ _
  refine coprod_inj_disjoint_canonical_pt htv u v ?_
  calc u ≫ coprodInl A B = u ≫ (HasBinaryCoproducts.inl ≫ φ) := by rw [hφl]
    _ = (u ≫ HasBinaryCoproducts.inl) ≫ φ := (Cat.assoc _ _ _).symm
    _ = (v ≫ HasBinaryCoproducts.inr) ≫ φ := by rw [huv]
    _ = v ≫ (HasBinaryCoproducts.inr ≫ φ) := Cat.assoc _ _ _
    _ = v ≫ coprodInr A B := by rw [hφr]

/-- **§1.988 RECURSOR EXISTENCE — in a BOOLEAN + CAPITAL topos (Freyd's actual hypotheses).**

    From bicartesian data `[a,t] : 1+A ≅ A` on `A` (and the terminal coequalizer `hcoeq`),
    §1.988 produces, for every `(X, x : 1→X, f : X→X)`, a map `h : A → X` with `a ≫ h = x` and
    `t ≫ h = h ≫ f` — Freyd's recursion theorem.

    IN-CHAPTER FORM (statement fidelity).  Freyd's §1.988/§1.989 are stated for a BOOLEAN topos
    (`hbool`), and the existence step opens "We may assume the topos is capital [1.935]" — i.e.
    CAPITAL (`hcap : Capital 𝒞`).  We carry both as explicit hypotheses, exactly matching the
    book.  Freyd's capital topos is moreover WELL-POINTED AS A TOPOS, i.e. TWO-VALUED (`Sub(1)`
    has exactly the two elements `0 ↣ 1` and `1 = 1`): §1.989's "no global point ⟹ the subobject
    is `⊥`" step uses precisely this.  Capital alone (well-supported ⟹ well-pointed) yields only
    "a proper subobject of 1 has a missing point", not "= ⊥"; so we add `htv : TwoValued 𝒞`,
    which is part of Freyd's capital/well-pointed-topos package (faithful, not an extra weakening).  The unconditional "any topos" form (§1.98(10) verbatim) follows from the §1.935
    reduction + the §2.542 boolean-and-capital embedding, both in Chapter 2; per the project rule
    "Chapter 1 must not depend on Chapter 2" the faithful in-chapter theorem is the BOOLEAN +
    CAPITAL one stated here.

    PROOF.  EXISTENCE is the functional graph `G ↣ A×X := least (⟨a,x⟩, pair (fst≫t) (snd≫f))`
    (the least closed subobject of `A×X`).  Its projection `p := G.arr ≫ fst` has `image p`
    `(a,t)`-closed, hence ENTIRE by the now Sorry-free `peano_property_of_bicartesian`, so `p` is
    TOTAL (a cover) — this half is proved Sorry-free below, and the recursor `h := p⁻¹ ≫ G.arr ≫
    snd` with its two laws `a≫h=x`, `t≫h=h≫f` is then assembled Sorry-free.  SINGLE-VALUEDNESS
    (`p` monic) is Freyd's §1.989: the diagonal `Δ = image kp_diag ⊆ kernelPair p`, its boolean
    complement `K'` (off-diagonal kernel pair), `A₁ = image(K'.arr ≫ kp₁ ≫ p)`, and `A₂ = complement
    A₁` are all assembled Sorry-free, AS IS the whole collapse `A₂ entire (Peano) ⟹ A₁ ≤ ⊥ ⟹ K' ≤ ⊥
    ⟹ Δ entire ⟹ kp_diag cover (split mono via kp_diag_p₁) ⟹ iso ⟹ Monic p`.  The KEYSTONE
    `cg = [a₀,tG] : 1+G.dom → G.dom` is a cover (graph reachability) is also Sorry-free.  The whole
    SUBOBJECT-LEVEL collapse is now closed: `noPoint_le_bottom` (a no-global-point subobject is `⊥`,
    from CAPITAL + TWO-VALUED `htv`), `point_bottom_absurd` (a `⊥`-domain has no point), and
    `kpPointAbsurd` (an off-diagonal `K'`-point with equal legs lands in `Δ∩K'≤⊥`) reduce both
    `A₁ ∩ {a} ≤ ⊥` and `A₁ ∩ t(A₂) ≤ ⊥` to two PURE POINT facts: the `p`-fiber over `a` is `{a₀}`
    (`hfibSingle`) and over a `t`-image of `A₂` is a singleton (`hfibSingleT`).  TWO residual holes
    remain, both the SAME §1.989 graph-reachability content: those two fiber-singleton facts.  Each
    needs COPRODUCT POINT-DECOMPOSITION for the abstract `1+G.dom` (a point lifts along the keystone
    cover `cg` and splits as `inl`=`a₀` or `inr`=`tG`-successor, the latter forcing the value into
    `image t`, disjoint from `a` via `[a,t]` iso) — the one primitive not yet available as a lemma.

    We bundle the `(a,t) → A`-instance UNIQUENESS clause here (proved Sorry-free from the Peano
    property via the equalizer); it breaks the old `peano ⟺ recursor-uniqueness` circularity,
    after which GENERAL recursor uniqueness is `recursor_unique_of_bicartesian`. -/
theorem recursor_exists_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
    (hbool : BooleanSub 𝒞) (hcap : Capital (𝒞 := 𝒞)) (htv : TwoValued (𝒞 := 𝒞))
    {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A)
    (hiso : IsIso (HasBinaryCoproducts.case a t (A := one) (B := A) (X := A)))
    (hcoeq : ∀ (X : 𝒞) (f : A ⟶ X), t ≫ f = f →
               ∃ g : (one ⟶ X), term A ≫ g = f ∧
                 ∀ g' : one ⟶ X, term A ≫ g' = f → g' = g) :
    -- existence for every codomain, plus uniqueness for the `(a,t) → A` instance.
    (∀ {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X),
        ∃ h : A ⟶ X, a ≫ h = x ∧ t ≫ h = h ≫ f) ∧
      (∀ e : A ⟶ A, a ≫ e = a → t ≫ e = e ≫ t → e = Cat.id A) := by
  -- §1.98(10) recursor, FAITHFULLY in a BOOLEAN topos (`hbool`), as Freyd's §1.988 requires.
  -- The §1.988 PEANO PROPERTY is now an available lemma `peano_property_of_bicartesian`
  -- (every `(a,t)`-closed subobject of `A` is entire), proved from `hbool` by Freyd's
  -- complement argument.  From it both conjuncts follow:
  --   UNIQUENESS — the equalizer `E = eq(e,id_A) ↣ A` of an endo-recursor `e` is `(a,t)`-closed
  --     (allows `a`: `a≫e=a=a≫id`; `t`-stable: `m≫t` still equalizes `e,id`), hence ENTIRE by the
  --     Peano property, so `e = id_A`.  (Same equalizer chase as `recursor_unique_of_bicartesian`.)
  --   EXISTENCE — the graph `G ↣ A×X` (least `(pair a x, prodMap t f)`-closed subobject of `A×X`)
  --     projects to a `(a,t)`-closed subobject of `A`, entire by Peano, giving the functional
  --     `h := proj⁻¹ ≫ G.arr ≫ snd`.
  classical
  refine ⟨?_, ?_⟩
  · -- EXISTENCE residual, FAITHFULLY in a BOOLEAN + CAPITAL topos (Freyd's §1.988/§1.989 actual
    -- hypotheses, now threaded as `hbool`/`hcap`).  The §1.988 recursion theorem via the functional
    -- graph `G ↣ A×X := HasLeastClosedSubobject.least (pair a x) (pair (fst≫t) (snd≫f))` — the least
    -- `(⟨a,x⟩, t×f)`-closed subobject (the `[HasLeastClosedSubobject 𝒞]` instance is the GLOBAL
    -- `Freyd.toposHasLeastClosedSubobject`).  Its `A`-projection `p := G.arr ≫ fst` has `image p`
    -- `(a,t)`-closed in `A` (allows `a`: `⟨a,x⟩≫fst = a`; `t`-stable: `(t×f)≫fst = fst≫t`), hence
    -- ENTIRE by the now SORRY-FREE `peano_property_of_bicartesian` — so `p` is TOTAL (a cover).
    --
    -- The remaining step is SINGLE-VALUEDNESS: `p` MONIC, so `p` iso [1.512] and `h := p⁻¹≫G.arr≫snd`.
    -- This is Freyd's §1.989, whose two hypotheses are EXACTLY the ones now in scope:
    --   (1) 1 is PROJECTIVE — available as `pts_covers_of_capital hcap` (lift the point `p:1→A` back
    --       along the cover, `x = y≫u`);
    --   (2) the topos is CAPITAL / 1 generates (well-pointedness) — `hcap` itself, used to conclude
    --       `image(t↾A₂)` is well-pointed and so honestly `t`-stable.
    --   §1.989 (book p.186): "We may assume the topos is capital [1.935].  Let K ⊂ C×C be the level
    --   of f, K' the complement of the diagonal in K, and A₁ ⊂ A the image of K' ⊂ K → C → A.  Let
    --   A₂ = complement of A₁.  It is enough to show A₂ = A … entire by the Peano property [1.988].
    --   Because 1 is projective [1.525], A₂ allows p:1→A iff there is a unique x:1→C with x≫f=p …
    --   the image of t↾A₂ is well-pointed because it allows 1→A and the topos is capital."
    --
    -- RESIDUAL (the SINGLE remaining hole): the level-of-`p` / complement-of-diagonal "agreement
    -- subobject" assembly that turns the total relation `G` into a single-valued map.  It is now a
    -- pure Chapter-1 construction (no Ch.2, no §1.543), bottoming out on building `A₁ = image(K'→A)`
    -- for the level `K ⊂ A×A` of `p` and showing its complement `A₂` is `(a,t)`-closed using
    -- `hcap`/`pts_covers_of_capital hcap` pointwise.  No `relToMap`/single-valued-graph primitive
    -- exists yet in S1_9/S1_56/S1_59 to package this; it is the absent §1.989 functional-graph lemma.
    intro X x f
    -- Graph `G ↣ A×X` := least `(⟨a,x⟩, S)`-closed subobject, `S := pair (fst≫t) (snd≫f)`.
    let S : prod A X ⟶ prod A X := pair (fst ≫ t) (snd ≫ f)
    let pax : one ⟶ prod A X := pair a x
    let G : Subobject 𝒞 (prod A X) := HasLeastClosedSubobject.least pax S
    have hGclosed : IsClosedSub G pax S := HasLeastClosedSubobject.least_isClosed pax S
    obtain ⟨a₀, ha₀⟩ := hGclosed.1            -- a₀ ≫ G.arr = pax
    obtain ⟨tG, htG⟩ := hGclosed.2            -- tG ≫ G.arr = G.arr ≫ S
    let p : G.dom ⟶ A := G.arr ≫ fst
    -- `S ≫ fst = fst ≫ t`, hence `p ≫ t = tG ≫ p`.
    have hSfst : S ≫ fst = fst ≫ t := fst_pair _ _
    have hpt : p ≫ t = tG ≫ p := by
      show (G.arr ≫ fst) ≫ t = tG ≫ G.arr ≫ fst
      rw [Cat.assoc, ← hSfst, ← Cat.assoc, ← htG, Cat.assoc]
    -- TOTALITY: `image p` is `(a,t)`-closed, hence entire by the Peano property, so `p` is a cover.
    have hpcover : Cover p := by
      have hImgClosed : IsClosedSub (image p) a t := by
        refine ⟨⟨a₀ ≫ image.lift p, ?_⟩, ?_⟩
        · -- `a` factors through `image p`: `(a₀ ≫ image.lift p) ≫ (image p).arr = a₀ ≫ p = a`.
          rw [Cat.assoc, image.lift_fac]
          show a₀ ≫ G.arr ≫ fst = a
          rw [← Cat.assoc, ha₀]; exact fst_pair _ _
        · -- `t`-stability: `image((image p).arr ≫ t) ≤ image(p ≫ t) ≤ image p`, then descend.
          have hcov : Cover (image.lift p) := image_lift_cover p
          have hle1 : (image ((image p).arr ≫ t)).le (image (p ≫ t)) := by
            have hrw : image.lift p ≫ ((image p).arr ≫ t) = p ≫ t := by
              rw [← Cat.assoc, image.lift_fac]
            have := (image_cover_comp (image.lift p) ((image p).arr ≫ t) hcov).2
            rwa [hrw] at this
          have hle2 : (image (p ≫ t)).le (image p) :=
            image_min (p ≫ t) (image p) ⟨tG ≫ image.lift p, by
              rw [Cat.assoc, image.lift_fac, hpt]⟩
          obtain ⟨k, hk⟩ := subLe_trans' hle1 hle2
          exact ⟨image.lift ((image p).arr ≫ t) ≫ k, by rw [Cat.assoc, hk, image.lift_fac]⟩
      have hEnt : (image p).IsEntire :=
        peano_property_of_bicartesian hbool a t hiso hcoeq (image p) hImgClosed.1 hImgClosed.2
      -- `p = image.lift p ≫ (image p).arr` is `cover ≫ iso`, hence a cover.
      have hc : Cover (image.lift p ≫ (image p).arr) :=
        cover_comp (image_lift_cover p) (iso_cover (image p).arr hEnt)
      rwa [image.lift_fac] at hc
    -- SINGLE-VALUEDNESS (§1.989): `p` MONIC.  The one step using CAPITAL — `hcap` supplies both
    -- well-pointedness and (via `pts_covers_of_capital hcap`) "1 is projective".  RESIDUAL: the
    -- level-of-`p` / complement-of-diagonal agreement-subobject assembly (Freyd §1.989, book p.186)
    -- turning the total relation `G` into a single-valued map.  No `relToMap` primitive packages it
    -- yet in S1_9/S1_56/S1_59; this is the SINGLE remaining §1.989 functional-graph hole.
    -- `hcap` (capital / well-pointed) and `pts_covers_of_capital hcap` (1 projective, lifting points
    -- along the cover `p`) are the §1.989 inputs; the agreement-subobject assembly remains the hole.
    -- KEYSTONE (§1.989 graph reachability): the structure map `cg := [a₀, tG] : 1 + G.dom → G.dom`
    -- of the algebra `G` is a COVER.  Proof: `R' := image (cg ≫ G.arr) ⊆ A×X` is `(pax, S)`-closed
    -- (allows `pax` via the `inl` leg of `cg`; `S`-stable via `cg ≫ tG = case (a₀≫inr)(tG≫inr) ≫ cg`),
    -- so `G ≤ R'` (leastness) and `R' ≤ G` (`image_min`), forcing `image cg` entire.
    let cg : HasBinaryCoproducts.coprod (one : 𝒞) G.dom ⟶ G.dom := HasBinaryCoproducts.case a₀ tG
    have hcg : Cover cg := by
      let R' : Subobject 𝒞 (prod A X) := image (cg ≫ G.arr)
      -- `R'` is `(pax, S)`-closed.
      have hR'closed : IsClosedSub R' pax S := by
        refine ⟨⟨HasBinaryCoproducts.inl ≫ image.lift (cg ≫ G.arr), ?_⟩, ?_⟩
        · -- allows `pax`: `(inl ≫ lift) ≫ R'.arr = (inl ≫ cg) ≫ G.arr = a₀ ≫ G.arr = pax`.
          show (HasBinaryCoproducts.inl ≫ image.lift (cg ≫ G.arr)) ≫ (image (cg ≫ G.arr)).arr = pax
          rw [Cat.assoc, image.lift_fac, ← Cat.assoc, HasBinaryCoproducts.case_inl, ha₀]
        · -- `S`-stable: `image (R'.arr ≫ S) ≤ image ((cg≫G.arr) ≫ S) ≤ image (cg≫G.arr) = R'`, descend.
          have hcov : Cover (image.lift (cg ≫ G.arr)) := image_lift_cover (cg ≫ G.arr)
          -- `(cg ≫ G.arr) ≫ S = case (a₀ ≫ inr) (tG ≫ inr) ≫ (cg ≫ G.arr)` (graph law via `htG`).
          have hfact : (cg ≫ G.arr) ≫ S
              = HasBinaryCoproducts.case (a₀ ≫ HasBinaryCoproducts.inr)
                  (tG ≫ HasBinaryCoproducts.inr) ≫ (cg ≫ G.arr) := by
            have hcgtG : cg ≫ tG
                = HasBinaryCoproducts.case (a₀ ≫ HasBinaryCoproducts.inr)
                    (tG ≫ HasBinaryCoproducts.inr) ≫ cg := by
              rw [case_comp, case_comp, Cat.assoc, Cat.assoc,
                  HasBinaryCoproducts.case_inr]
            calc (cg ≫ G.arr) ≫ S = cg ≫ (G.arr ≫ S) := Cat.assoc _ _ _
              _ = cg ≫ (tG ≫ G.arr) := by rw [htG]
              _ = (cg ≫ tG) ≫ G.arr := (Cat.assoc _ _ _).symm
              _ = (HasBinaryCoproducts.case (a₀ ≫ HasBinaryCoproducts.inr)
                    (tG ≫ HasBinaryCoproducts.inr) ≫ cg) ≫ G.arr := by rw [hcgtG]
              _ = _ := Cat.assoc _ _ _
          have hle1 : (image (R'.arr ≫ S)).le (image ((cg ≫ G.arr) ≫ S)) := by
            have hrw : image.lift (cg ≫ G.arr) ≫ (R'.arr ≫ S) = (cg ≫ G.arr) ≫ S := by
              rw [← Cat.assoc, image.lift_fac]
            have := (image_cover_comp (image.lift (cg ≫ G.arr)) (R'.arr ≫ S) hcov).2
            rwa [hrw] at this
          have hle2 : (image ((cg ≫ G.arr) ≫ S)).le R' :=
            image_min ((cg ≫ G.arr) ≫ S) R'
              ⟨HasBinaryCoproducts.case (a₀ ≫ HasBinaryCoproducts.inr)
                  (tG ≫ HasBinaryCoproducts.inr) ≫ image.lift (cg ≫ G.arr), by
                rw [Cat.assoc, image.lift_fac, hfact]⟩
          obtain ⟨k, hk⟩ := subLe_trans' hle1 hle2
          exact ⟨image.lift (R'.arr ≫ S) ≫ k, by rw [Cat.assoc, hk, image.lift_fac]⟩
      -- `G = least pax S ≤ R'` (leastness) and `R' ≤ G` (`image_min`): mutual `≤` ⟹ iso over `A×X`.
      have hGR' : G.le R' := HasLeastClosedSubobject.least_le pax S R' hR'closed
      have hR'G : R'.le G := image_min (cg ≫ G.arr) G ⟨cg, rfl⟩
      obtain ⟨c, hc⟩ := hR'G
      -- `c : R'.dom → G.dom`, `c ≫ G.arr = R'.arr`, iso (mutual `≤`).
      have hciso : IsIso c := by
        obtain ⟨d, hd⟩ := hGR'
        refine ⟨d, ?_, ?_⟩
        · exact R'.monic (c ≫ d) (Cat.id _) (by rw [Cat.assoc, hd, hc, Cat.id_comp])
        · exact G.monic (d ≫ c) (Cat.id _) (by rw [Cat.assoc, hc, hd, Cat.id_comp])
      -- `cg = image.lift (cg ≫ G.arr) ≫ c` (cover ∘ iso): `(lift ≫ c) ≫ G.arr = lift ≫ R'.arr = cg ≫ G.arr`.
      have hcgeq : image.lift (cg ≫ G.arr) ≫ c = cg :=
        G.monic _ _ (by rw [Cat.assoc, hc, image.lift_fac])
      have hcc : Cover (image.lift (cg ≫ G.arr) ≫ c) :=
        cover_comp (image_lift_cover (cg ≫ G.arr)) (iso_cover c hciso)
      rwa [hcgeq] at hcc
    have hpmono : Monic p := by
      -- §1.989 single-valuedness (Freyd p.186).  `K := kernelPair p`, diagonal `Δ := image kp_diag`.
      -- Boolean complement `K'` of `Δ` (off-diagonal kernel pair); `A₁ := image(K'.arr ≫ kp₁ ≫ p)`
      -- its `A`-image; `A₂ := boolean complement`.  `A₂` is `(a,t)`-closed, so ENTIRE by Peano, hence
      -- `A₁ ≤ ⊥` ⟹ `K' ≤ ⊥` ⟹ `Δ` entire ⟹ `kp_diag` cover.  `kp_diag` is split mono (`kp_diag_p₁`),
      -- so a cover-split-mono is iso; `monic_iff_kp_diag_iso` then gives `Monic p`.
      rw [monic_iff_kp_diag_iso]
      -- Δ = image of the diagonal `kp_diag : G.dom → K`.
      let Δ : Subobject 𝒞 (kernelPair p) := image (kp_diag (f := p))
      -- Boolean complement `K'` of `Δ` in `K`.
      obtain ⟨K', hΔdisj, hΔunion⟩ := hbool Δ
      -- `A₁ := image of the off-diagonal kernel-pair leg pushed to `A`.
      let q : K'.dom ⟶ A := K'.arr ≫ kp₁ (f := p) ≫ p
      let A₁ : Subobject 𝒞 A := image q
      -- Boolean complement `A₂` of `A₁` in `A`.
      obtain ⟨A₂, hA₁disj, hA₁union⟩ := hbool A₁
      -- the singleton point subobject `aSub := {a₀} ↣ A` (`a` monic from `1`).
      have ha_mono : Monic a := mono_from_one a
      let aSub : Subobject 𝒞 A := Subobject.mk one a ha_mono
      -- ── A point of `K'` (the OFF-diagonal complement) whose two legs AGREE lies on the
      -- diagonal `Δ`, hence in `Δ ∩ K' ≤ ⊥` — absurd (`point_bottom_absurd`).
      have kpPointAbsurd : ∀ k : (one : 𝒞) ⟶ K'.dom,
          k ≫ K'.arr ≫ kp₁ (f := p) = k ≫ K'.arr ≫ kp₂ (f := p) → False := by
        intro k hlegs
        -- `v := k ≫ K'.arr ≫ kp₁`; `k ≫ K'.arr = v ≫ kp_diag` (lift uniqueness, equal legs).
        let v : (one : 𝒞) ⟶ G.dom := k ≫ K'.arr ≫ kp₁ (f := p)
        have hkdiag : k ≫ K'.arr = v ≫ kp_diag (f := p) := by
          -- both `k ≫ K'.arr` and `v ≫ kp_diag` are the kernel-pair lift of legs `(v, v)`.
          have e₁ := kp_lift_uniq (f := p) v v rfl (k ≫ K'.arr)
            (by rw [Cat.assoc])
            (by rw [Cat.assoc]; exact hlegs.symm)
          have e₂ := kp_lift_uniq (f := p) v v rfl (v ≫ kp_diag (f := p))
            (by rw [Cat.assoc, kp_diag_p₁, Cat.comp_id])
            (by rw [Cat.assoc, kp_diag_p₂, Cat.comp_id])
          rw [e₁, e₂]
        -- `k ≫ K'.arr` factors through `Δ.arr` (`Δ = image kp_diag`).
        let dΔ : (one : 𝒞) ⟶ Δ.dom := v ≫ image.lift (kp_diag (f := p))
        have hdΔ : dΔ ≫ Δ.arr = k ≫ K'.arr := by
          show (v ≫ image.lift (kp_diag (f := p))) ≫ (image (kp_diag (f := p))).arr = k ≫ K'.arr
          rw [Cat.assoc, image.lift_fac, hkdiag]
        -- the point subobject `{k ≫ K'.arr} ≤ Δ ∩ K' ≤ ⊥`, yielding a point of `(⊥ K).dom`.
        let pt : Subobject 𝒞 (kernelPair p) :=
          Subobject.mk one (k ≫ K'.arr) (mono_from_one _)
        have hptΔ : pt.le Δ := ⟨dΔ, hdΔ⟩
        have hptK' : pt.le K' := ⟨k, rfl⟩
        have hptbot : pt.le (PreLogos.bottom (kernelPair p)) :=
          subLe_trans' (Subobject.le_inter hptΔ hptK') hΔdisj
        obtain ⟨m, _⟩ := hptbot
        exact point_bottom_absurd htv m
      -- ── THE FIBER-SINGLETON FACT (§1.989 graph reachability) — the SOLE remaining hole.
      -- The whole subobject-level `A₁ ∩ {a} ≤ ⊥` is now CLOSED (`noPoint_le_bottom` + the
      -- `kpPointAbsurd` off-diagonal contradiction below); it is reduced to this pure POINT fact:
      -- the `p`-fiber over `a` is the singleton `{a₀}`.  Proof (Freyd p.186): `1` is projective
      -- (`pts_covers_of_capital hcap`), so a point `z` lifts along the keystone cover
      -- `cg = [a₀,tG] : 1+G.dom ↠ G.dom` (`hcg`) to `w : 1 → 1+G.dom`; coproduct point-decomposition
      -- (extensivity of the abstract `HasBinaryCoproducts` coproduct `1+G.dom`, the one piece NOT
      -- yet available as a lemma) makes `w` an `inl`-point (⟹ `z = a₀`) or an `inr`-point
      -- (⟹ `z = w'≫tG`, so `z≫p = w'≫p≫t ∈ image t`, contradicting `a`'s disjointness from `image t`
      -- via the iso `[a,t]`).  RESIDUAL: that coproduct point-decomposition for `1+G.dom`.
      have hfibSingle : ∀ z : (one : 𝒞) ⟶ G.dom, z ≫ p = a → z = a₀ := by
        intro z hz
        -- 1 projective: lift `z` along the keystone cover `cg = [a₀, tG]`.
        obtain ⟨w, hw⟩ := pts_covers_of_capital hcap hcg z
        -- `w : 1 → 1+G.dom` splits as an `inl`-point or `inr`-point.
        rcases coprod_point_split hcap htv w with ⟨u, hu⟩ | ⟨w', hw'⟩
        · -- `inl`: `z = w ≫ cg = u ≫ inl ≫ cg = u ≫ a₀ = a₀` (`u : 1→1`, so `u ≫ a₀ = a₀`).
          have hinlcg : HasBinaryCoproducts.inl (A := (one : 𝒞)) (B := G.dom) ≫ cg = a₀ :=
            HasBinaryCoproducts.case_inl _ _
          calc z = w ≫ cg := hw.symm
            _ = (u ≫ HasBinaryCoproducts.inl) ≫ cg := by rw [hu]
            _ = u ≫ (HasBinaryCoproducts.inl ≫ cg) := Cat.assoc _ _ _
            _ = u ≫ a₀ := by rw [hinlcg]
            _ = a₀ := by rw [term_uniq u (Cat.id one), Cat.id_comp]
        · -- `inr`: `z = w' ≫ tG`, so `a = z≫p = w'≫tG≫p = (w'≫p)≫t ∈ image t`, disjoint from `a`.
          exfalso
          have hinrcg : HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := G.dom) ≫ cg = tG :=
            HasBinaryCoproducts.case_inr _ _
          have hztG : z = w' ≫ tG := by
            calc z = w ≫ cg := hw.symm
              _ = (w' ≫ HasBinaryCoproducts.inr) ≫ cg := by rw [hw']
              _ = w' ≫ (HasBinaryCoproducts.inr ≫ cg) := Cat.assoc _ _ _
              _ = w' ≫ tG := by rw [hinrcg]
          -- `a = (w' ≫ p) ≫ t` (using `tG ≫ p = p ≫ t`).
          have hat : a = (w' ≫ p) ≫ t := by
            calc a = z ≫ p := hz.symm
              _ = (w' ≫ tG) ≫ p := by rw [hztG]
              _ = w' ≫ (tG ≫ p) := Cat.assoc _ _ _
              _ = w' ≫ (p ≫ t) := by rw [hpt]
              _ = (w' ≫ p) ≫ t := (Cat.assoc _ _ _).symm
          -- `[a,t]` is iso (mono): `inl`-point `a` = `inr`-point `(w'≫p)≫t` collapses injections.
          obtain ⟨caseInv, hcaseInv, _⟩ := hiso
          have hcase_mono : Monic (HasBinaryCoproducts.case a t (A := (one : 𝒞)) (B := A) (X := A)) :=
            mono_of_retraction _ caseInv hcaseInv
          refine coprod_inj_disjoint_pt htv (Cat.id one) (w' ≫ p) ?_
          apply hcase_mono
          rw [Cat.assoc, Cat.assoc, HasBinaryCoproducts.case_inl,
              HasBinaryCoproducts.case_inr, Cat.id_comp, ← hat]
      -- ── THE FIBER FACT: the `a`-fiber of `p` is the singleton `{a₀}`, i.e. `A₁ ∩ {a} ≤ ⊥`.
      -- `A₁ ∩ {a}` has NO point: a point gives an off-diagonal kernel-pair point over `a`, whose two
      -- legs are both `a₀` (`hfibSingle`), hence equal — `kpPointAbsurd`.  Then `noPoint_le_bottom`.
      have hfiber : (Subobject.inter A₁ aSub).le (PreLogos.bottom A) := by
        refine noPoint_le_bottom hcap htv _ ?_
        rintro _ ⟨y, _⟩
        -- the point factors through both `A₁` (left leg) and `aSub` (right leg, forcing value `a`).
        obtain ⟨kL, hkL⟩ := Subobject.inter_le_left A₁ aSub
        obtain ⟨kR, hkR⟩ := Subobject.inter_le_right A₁ aSub
        -- value over `a`: `(y ≫ kL) ≫ A₁.arr = (y ≫ kR) ≫ aSub.arr = a` (`y ≫ kR : 1 → 1 = id`).
        have hval : (y ≫ kL) ≫ A₁.arr = a := by
          have heq : (y ≫ kR) ≫ aSub.arr = (y ≫ kL) ≫ A₁.arr := by
            rw [Cat.assoc, Cat.assoc, hkR, hkL]
          rw [← heq, term_uniq (y ≫ kR) (Cat.id one), Cat.id_comp]
        -- 1 projective: lift the point of `A₁ = image q` along the cover to a point of `K'`.
        obtain ⟨k₀, hk₀⟩ := pts_covers_of_capital hcap (image_lift_cover q) (y ≫ kL)
        have hk₀q : k₀ ≫ q = a := by
          have : k₀ ≫ q = (y ≫ kL) ≫ A₁.arr := by
            show k₀ ≫ K'.arr ≫ kp₁ (f := p) ≫ p = (y ≫ kL) ≫ (image q).arr
            rw [← hk₀, Cat.assoc, image.lift_fac]
          rw [this, hval]
        -- legs `g₁ = k₀≫K'.arr≫kp₁`, `g₂ = k₀≫K'.arr≫kp₂` both land on `a`, so both `= a₀`.
        apply kpPointAbsurd k₀
        have hg₁ : (k₀ ≫ K'.arr ≫ kp₁ (f := p)) ≫ p = a := by
          rw [Cat.assoc, Cat.assoc]; exact hk₀q
        have hg₂ : (k₀ ≫ K'.arr ≫ kp₂ (f := p)) ≫ p = a := by
          calc (k₀ ≫ K'.arr ≫ kp₂ (f := p)) ≫ p
              = k₀ ≫ K'.arr ≫ (kp₂ (f := p) ≫ p) := by rw [Cat.assoc, Cat.assoc]
            _ = k₀ ≫ K'.arr ≫ (kp₁ (f := p) ≫ p) := by rw [← kp_sq]
            _ = (k₀ ≫ K'.arr ≫ kp₁ (f := p)) ≫ p := by rw [Cat.assoc, Cat.assoc]
            _ = a := hg₁
        rw [hfibSingle _ hg₁, hfibSingle _ hg₂]
      -- ── `A₂` is `(a,t)`-closed.
      -- ALLOWS `a`: `{a} ≤ A₂` by `complement_le_other'` from `A₁ ∩ {a} ≤ ⊥` and `⊤ ≤ A₁ ∪ A₂`.
      have hA₂a : Allows A₂ a := by
        obtain ⟨g, hg⟩ := complement_le_other' A₁ A₂ aSub hfiber hA₁union
        exact ⟨g, by simpa using hg⟩
      -- `t`-STABLE: `image(A₂.arr ≫ t) ≤ A₂` (`complement_le_other'` from `A₁ ∩ t(A₂) ≤ ⊥`), descend.
      -- `A₁ ∩ t(A₂) ≤ ⊥`: a point of `t(A₂)` is `t(a')` with `a'` single-valued (`a' ∈ A₂`); by the
      -- keystone reachability (`hcg`) every preimage of `t(a')` is a `tG`-image of a preimage of `a'`,
      -- so single-valuedness propagates and `t(a') ∉ A₁`.  Same capital "no point ⟹ ⊥" gap as
      -- `hfiber` (PLUS the keystone reachability step); left as the second residual.
      have hA₂t : ∃ tA₂ : A₂.dom ⟶ A₂.dom, tA₂ ≫ A₂.arr = A₂.arr ≫ t := by
        -- `t`-shifted fiber-singleton: the fiber of `p` over a `t`-image `b≫A₂.arr≫t` of a
        -- single-valued point `b ∈ A₂` is again a singleton.  Same keystone reachability as
        -- `hfibSingle`, propagated through `tG` (`hpt : p ≫ t = tG ≫ p`).
        have hfibSingleT : ∀ (b : (one : 𝒞) ⟶ A₂.dom) (g₁ g₂ : (one : 𝒞) ⟶ G.dom),
            g₁ ≫ p = (b ≫ A₂.arr) ≫ t → g₂ ≫ p = (b ≫ A₂.arr) ≫ t → g₁ = g₂ := by
          intro b g₁ g₂ hg₁ hg₂
          -- `t` is MONIC: `inr ≫ case a (id) = id` splits `inr`, so `t = inr ≫ [a,t]` is monic.
          have ht_mono : Monic t := by
            obtain ⟨caseInv, hcaseInv, _⟩ := hiso
            have hcase_mono : Monic (HasBinaryCoproducts.case a t (A := (one : 𝒞)) (B := A) (X := A)) :=
              mono_of_retraction _ caseInv hcaseInv
            have hinr_split : HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := A)
                ≫ HasBinaryCoproducts.case a (Cat.id A) = Cat.id A :=
              HasBinaryCoproducts.case_inr _ _
            have hinr_mono : Monic (HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := A)) :=
              mono_of_retraction _ _ hinr_split
            have ht_eq : HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := A)
                ≫ HasBinaryCoproducts.case a t = t := HasBinaryCoproducts.case_inr _ _
            intro W u v huv
            apply hinr_mono
            apply hcase_mono
            rw [Cat.assoc, Cat.assoc, ht_eq, huv]
          -- reduce a preimage `g` of `c := (b≫A₂.arr)≫t` to a `tG`-image of a preimage of `b≫A₂.arr`.
          have reduce : ∀ g : (one : 𝒞) ⟶ G.dom, g ≫ p = (b ≫ A₂.arr) ≫ t →
              ∃ w' : (one : 𝒞) ⟶ G.dom, g = w' ≫ tG ∧ w' ≫ p = b ≫ A₂.arr := by
            intro g hg
            obtain ⟨wn, hwn⟩ := pts_covers_of_capital hcap hcg g
            rcases coprod_point_split hcap htv wn with ⟨u, hu⟩ | ⟨w', hw'⟩
            · -- `inl`: `g = a₀`, so `c = g≫p = a` is a `t`-image — absurd by `[a,t]`-disjointness.
              exfalso
              have hinlcg : HasBinaryCoproducts.inl (A := (one : 𝒞)) (B := G.dom) ≫ cg = a₀ :=
                HasBinaryCoproducts.case_inl _ _
              have hga₀ : g = a₀ := by
                calc g = wn ≫ cg := hwn.symm
                  _ = (u ≫ HasBinaryCoproducts.inl) ≫ cg := by rw [hu]
                  _ = u ≫ (HasBinaryCoproducts.inl ≫ cg) := Cat.assoc _ _ _
                  _ = u ≫ a₀ := by rw [hinlcg]
                  _ = a₀ := by rw [term_uniq u (Cat.id one), Cat.id_comp]
              -- `a₀ ≫ p = a` (`a₀ ≫ G.arr = pair a x`, `p = G.arr ≫ fst`).
              have ha₀p : a₀ ≫ p = a := by
                show a₀ ≫ G.arr ≫ fst = a
                rw [← Cat.assoc, ha₀]; exact fst_pair _ _
              have hac : a = (b ≫ A₂.arr) ≫ t := by rw [← ha₀p, ← hga₀]; exact hg
              obtain ⟨caseInv, hcaseInv, _⟩ := hiso
              have hcase_mono : Monic (HasBinaryCoproducts.case a t
                  (A := (one : 𝒞)) (B := A) (X := A)) := mono_of_retraction _ caseInv hcaseInv
              refine coprod_inj_disjoint_pt htv (Cat.id one) (b ≫ A₂.arr) ?_
              apply hcase_mono
              rw [Cat.assoc, Cat.assoc, HasBinaryCoproducts.case_inl,
                  HasBinaryCoproducts.case_inr, Cat.id_comp, ← hac]
            · -- `inr`: `g = w' ≫ tG`; `(w'≫p)≫t = g≫p = c`, descend by `t` monic.
              refine ⟨w', ?_, ?_⟩
              · have hinrcg : HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := G.dom) ≫ cg = tG :=
                  HasBinaryCoproducts.case_inr _ _
                calc g = wn ≫ cg := hwn.symm
                  _ = (w' ≫ HasBinaryCoproducts.inr) ≫ cg := by rw [hw']
                  _ = w' ≫ (HasBinaryCoproducts.inr ≫ cg) := Cat.assoc _ _ _
                  _ = w' ≫ tG := by rw [hinrcg]
              · apply ht_mono
                have hinrcg : HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := G.dom) ≫ cg = tG :=
                  HasBinaryCoproducts.case_inr _ _
                have hgtG : g = w' ≫ tG := by
                  calc g = wn ≫ cg := hwn.symm
                    _ = (w' ≫ HasBinaryCoproducts.inr) ≫ cg := by rw [hw']
                    _ = w' ≫ (HasBinaryCoproducts.inr ≫ cg) := Cat.assoc _ _ _
                    _ = w' ≫ tG := by rw [hinrcg]
                calc (w' ≫ p) ≫ t = w' ≫ (p ≫ t) := Cat.assoc _ _ _
                  _ = w' ≫ (tG ≫ p) := by rw [hpt]
                  _ = (w' ≫ tG) ≫ p := (Cat.assoc _ _ _).symm
                  _ = g ≫ p := by rw [← hgtG]
                  _ = (b ≫ A₂.arr) ≫ t := hg
          obtain ⟨w₁, hw₁eq, hw₁p⟩ := reduce g₁ hg₁
          obtain ⟨w₂, hw₂eq, hw₂p⟩ := reduce g₂ hg₂
          -- `w₁ ≫ p = w₂ ≫ p = b≫A₂.arr`; single-valuedness over the `A₂`-point `b` forces `w₁=w₂`.
          have hw₁w₂ : w₁ = w₂ := by
            classical
            by_cases hne : w₁ = w₂
            · exact hne
            exfalso
            -- off-diagonal kernel-pair point over `b≫A₂.arr`; lands in `K'`, projecting to `A₁`.
            have hlegs : w₁ ≫ p = w₂ ≫ p := by rw [hw₁p, hw₂p]
            let κ : (one : 𝒞) ⟶ kernelPair p :=
      (HasPullbacks.has p p).lift ⟨one, w₁, w₂, hlegs⟩
            have hκ₁ : κ ≫ kp₁ (f := p) = w₁ := kp_lift_p₁ w₁ w₂ hlegs
            have hκ₂ : κ ≫ kp₂ (f := p) = w₂ := kp_lift_p₂ w₁ w₂ hlegs
            -- `κ` lifts to `Δ` or `K'` (boolean: `⊤ ≤ Δ ∪ K'`).
            have hκent : (Subobject.mk one κ (mono_from_one _)).le
                (Subobject.entire (kernelPair p)) := ⟨κ, Cat.comp_id _⟩
            have hκtop := subLe_trans' hκent hΔunion
            obtain ⟨e, he⟩ := hκtop
            -- split the point of `Δ ∪ K'` along the cover into `Δ` or `K'`.
            rcases union_point_split hcap htv Δ K' e with ⟨d, hd⟩ | ⟨k, hk⟩
            · -- `κ ∈ Δ`: diagonal, so its two legs agree (every point of `image kp_diag` is on the
              -- diagonal), forcing `w₁ = w₂` — contradicts `hne`.
              apply hne
              have hdΔ : d ≫ Δ.arr = κ := by rw [hd]; exact he
              -- `Δ.arr ≫ kp₁ = Δ.arr ≫ kp₂` (cancel the cover `image.lift kp_diag`).
              have hΔlegs : Δ.arr ≫ kp₁ (f := p) = Δ.arr ≫ kp₂ (f := p) := by
                refine cover_epi (image_lift_cover (kp_diag (f := p))) ?_
                calc image.lift (kp_diag (f := p)) ≫ (Δ.arr ≫ kp₁ (f := p))
                    = (image.lift (kp_diag (f := p)) ≫ Δ.arr) ≫ kp₁ (f := p) := (Cat.assoc _ _ _).symm
                  _ = kp_diag (f := p) ≫ kp₁ (f := p) := by rw [image.lift_fac]
                  _ = kp_diag (f := p) ≫ kp₂ (f := p) := by rw [kp_diag_p₁, kp_diag_p₂]
                  _ = (image.lift (kp_diag (f := p)) ≫ Δ.arr) ≫ kp₂ (f := p) := by rw [image.lift_fac]
                  _ = image.lift (kp_diag (f := p)) ≫ (Δ.arr ≫ kp₂ (f := p)) := Cat.assoc _ _ _
              calc w₁ = κ ≫ kp₁ (f := p) := hκ₁.symm
                _ = (d ≫ Δ.arr) ≫ kp₁ (f := p) := by rw [hdΔ]
                _ = d ≫ (Δ.arr ≫ kp₁ (f := p)) := Cat.assoc _ _ _
                _ = d ≫ (Δ.arr ≫ kp₂ (f := p)) := by rw [hΔlegs]
                _ = (d ≫ Δ.arr) ≫ kp₂ (f := p) := (Cat.assoc _ _ _).symm
                _ = κ ≫ kp₂ (f := p) := by rw [hdΔ]
                _ = w₂ := hκ₂
            · -- `κ ∈ K'`: `b≫A₂.arr = w₁≫p` factors through `A₁ = image q`, so `∈ A₁ ∩ A₂ ≤ ⊥` — absurd.
              exfalso
              have hκK' : k ≫ K'.arr = κ := by rw [hk]; exact he
              -- `b≫A₂.arr = w₁≫p = κ≫kp₁≫p = (k ≫ K'.arr ≫ kp₁) ≫ p = k ≫ q`.
              have hvalA₁ : (k ≫ image.lift q) ≫ A₁.arr = b ≫ A₂.arr := by
                show (k ≫ image.lift q) ≫ (image q).arr = b ≫ A₂.arr
                rw [Cat.assoc, image.lift_fac]
                show k ≫ K'.arr ≫ kp₁ (f := p) ≫ p = b ≫ A₂.arr
                calc k ≫ K'.arr ≫ kp₁ (f := p) ≫ p
                    = (k ≫ K'.arr) ≫ kp₁ (f := p) ≫ p := (Cat.assoc _ _ _).symm
                  _ = κ ≫ kp₁ (f := p) ≫ p := by rw [hκK']
                  _ = (κ ≫ kp₁ (f := p)) ≫ p := (Cat.assoc _ _ _).symm
                  _ = w₁ ≫ p := by rw [hκ₁]
                  _ = b ≫ A₂.arr := hw₁p
              -- point of `A₁ ∩ A₂` (left = `k ≫ image.lift q`, right = `b`) — `≤ ⊥`, absurd.
              have hptbot : (Subobject.mk one (b ≫ A₂.arr) (mono_from_one _)).le
                  (PreLogos.bottom A) :=
                subLe_trans'
                  (Subobject.le_inter (S := A₁) (T := A₂)
                    ⟨k ≫ image.lift q, hvalA₁⟩ ⟨b, rfl⟩)
                  hA₁disj
              obtain ⟨m, _⟩ := hptbot
              exact point_bottom_absurd htv (Cat.id one ≫ m)
          rw [hw₁eq, hw₂eq, hw₁w₂]
        have hdisj_t : (Subobject.inter A₁ (image (A₂.arr ≫ t))).le (PreLogos.bottom A) := by
          refine noPoint_le_bottom hcap htv _ ?_
          rintro _ ⟨y, _⟩
          obtain ⟨kL, hkL⟩ := Subobject.inter_le_left A₁ (image (A₂.arr ≫ t))
          obtain ⟨kR, hkR⟩ := Subobject.inter_le_right A₁ (image (A₂.arr ≫ t))
          -- value over `b ≫ A₂.arr ≫ t`: lift the right point along `image.lift (A₂.arr ≫ t)`.
          obtain ⟨b, hb⟩ := pts_covers_of_capital hcap (image_lift_cover (A₂.arr ≫ t)) (y ≫ kR)
          have hbval : (y ≫ kR) ≫ (image (A₂.arr ≫ t)).arr = (b ≫ A₂.arr) ≫ t := by
            rw [← hb, Cat.assoc, image.lift_fac, ← Cat.assoc]
          -- value over `A₁`: lift the left point along `image.lift q`.
          obtain ⟨k₀, hk₀⟩ := pts_covers_of_capital hcap (image_lift_cover q) (y ≫ kL)
          -- the common value `v := (y ≫ kL) ≫ A₁.arr = (y ≫ kR) ≫ (t(A₂)).arr = (b≫A₂.arr)≫t`.
          have hcommon : (y ≫ kL) ≫ A₁.arr = (b ≫ A₂.arr) ≫ t := by
            have : (y ≫ kL) ≫ A₁.arr = (y ≫ kR) ≫ (image (A₂.arr ≫ t)).arr := by
              rw [Cat.assoc, Cat.assoc, hkL, hkR]
            rw [this, hbval]
          have hk₀q : k₀ ≫ q = (b ≫ A₂.arr) ≫ t := by
            have : k₀ ≫ q = (y ≫ kL) ≫ A₁.arr := by
              show k₀ ≫ K'.arr ≫ kp₁ (f := p) ≫ p = (y ≫ kL) ≫ (image q).arr
              rw [← hk₀, Cat.assoc, image.lift_fac]
            rw [this, hcommon]
          apply kpPointAbsurd k₀
          have hg₁ : (k₀ ≫ K'.arr ≫ kp₁ (f := p)) ≫ p = (b ≫ A₂.arr) ≫ t := by
            rw [Cat.assoc, Cat.assoc]; exact hk₀q
          have hg₂ : (k₀ ≫ K'.arr ≫ kp₂ (f := p)) ≫ p = (b ≫ A₂.arr) ≫ t := by
            calc (k₀ ≫ K'.arr ≫ kp₂ (f := p)) ≫ p
                = k₀ ≫ K'.arr ≫ (kp₂ (f := p) ≫ p) := by rw [Cat.assoc, Cat.assoc]
              _ = k₀ ≫ K'.arr ≫ (kp₁ (f := p) ≫ p) := by rw [← kp_sq]
              _ = (k₀ ≫ K'.arr ≫ kp₁ (f := p)) ≫ p := by rw [Cat.assoc, Cat.assoc]
              _ = (b ≫ A₂.arr) ≫ t := hg₁
          rw [hfibSingleT b _ _ hg₁ hg₂]
        have hle : (image (A₂.arr ≫ t)).le A₂ :=
          complement_le_other' A₁ A₂ (image (A₂.arr ≫ t)) hdisj_t hA₁union
        obtain ⟨k, hk⟩ := hle
        exact ⟨image.lift (A₂.arr ≫ t) ≫ k, by rw [Cat.assoc, hk, image.lift_fac]⟩
      -- ── A₂ ENTIRE by the Peano property.
      have hA₂entire : A₂.IsEntire :=
        peano_property_of_bicartesian hbool a t hiso hcoeq A₂ hA₂a hA₂t
      -- ── A₂ entire ⟹ A₁ ≤ ⊥ (complement of an entire subobject).
      have hA₁bot : A₁.le (PreLogos.bottom A) := by
        -- `A₁ ∩ A₂ ≤ ⊥` and `A₂` entire (so `A₁ ≤ A₁ ∩ A₂`): `A₁ = A₁ ∩ entire ≤ A₁ ∩ A₂ ≤ ⊥`.
        refine subLe_trans' ?_ hA₁disj
        refine Subobject.le_inter ⟨Cat.id _, Cat.id_comp _⟩ ?_
        obtain ⟨inv, _, hinv2⟩ := hA₂entire
        exact ⟨A₁.arr ≫ inv, by rw [Cat.assoc, hinv2, Cat.comp_id]⟩
      -- ── A₁ ≤ ⊥ ⟹ K' ≤ ⊥: `q = K'.arr ≫ kp₁ ≫ p` factors through `image q = A₁`, whose dom is
      -- initial, so `K'.dom → A₁.dom → 0`.
      have hK'bot : K'.le (PreLogos.bottom (kernelPair p)) := by
        -- `image.lift q : K'.dom → A₁.dom`; `A₁ ≤ ⊥` gives `A₁.dom → (⊥A).dom`.
        obtain ⟨m, _hm⟩ := hA₁bot
        exact peano_le_bottom_of_map K' (image.lift q ≫ m)
      -- ── K' ≤ ⊥ ⟹ Δ entire: `entire K ≤ Δ ∪ K' ≤ Δ ∪ ⊥ = Δ`.
      have hΔentire : Δ.IsEntire :=
        entire_of_entire_le (subLe_trans' hΔunion
          (HasSubobjectUnions.union_min Δ K' Δ ⟨Cat.id _, Cat.id_comp _⟩
            (subLe_trans' hK'bot (PreLogos.bottom_min Δ))))
      -- ── Δ entire ⟹ `kp_diag` cover ⟹ (split mono via `kp_diag_p₁`) iso.
      have hdiagcover : Cover (kp_diag (f := p)) :=
        (cover_iff_image_entire (kp_diag (f := p))).2 hΔentire
      exact monic_cover_iso (kp_diag (f := p)) hdiagcover
        (mono_of_retraction _ (kp₁ (f := p)) kp_diag_p₁)
    have hpiso : IsIso p := monic_cover_iso p hpcover hpmono
    obtain ⟨pinv, hpinv1, hpinv2⟩ := hpiso
    -- `h := p⁻¹ ≫ G.arr ≫ snd`.  `a ≫ h = x` and `t ≫ h = h ≫ f` follow from the graph laws.
    refine ⟨pinv ≫ G.arr ≫ snd, ?_, ?_⟩
    · -- `a ≫ (pinv ≫ G.arr ≫ snd) = x`.  `a = a₀ ≫ p` and `a₀ ≫ p ≫ pinv = a₀`, so reduces to
      -- `a₀ ≫ G.arr ≫ snd = pax ≫ snd = x`.
      have hap : a = a₀ ≫ p := by rw [← Cat.assoc, ha₀]; exact (fst_pair _ _).symm
      have hcollapse : a ≫ pinv = a₀ := by
        rw [hap, Cat.assoc, hpinv1, Cat.comp_id]
      calc a ≫ pinv ≫ G.arr ≫ snd = (a ≫ pinv) ≫ G.arr ≫ snd := (Cat.assoc _ _ _).symm
        _ = a₀ ≫ G.arr ≫ snd := by rw [hcollapse]
        _ = (a₀ ≫ G.arr) ≫ snd := (Cat.assoc _ _ _).symm
        _ = pax ≫ snd := by rw [ha₀]
        _ = x := snd_pair _ _
    · -- `t ≫ h = h ≫ f`.  Both sides chase through the graph: `t` lifts via `tG` on `G.dom`,
      -- `S ≫ snd = snd ≫ f`, and `t ≫ pinv = pinv ≫ tG` from `p ≫ t = tG ≫ p`.
      have hSsnd : S ≫ snd = snd ≫ f := snd_pair _ _
      have htpinv : t ≫ pinv = pinv ≫ tG := by
        have h1 : pinv ≫ (tG ≫ p) = t := by
          rw [← hpt, ← Cat.assoc, hpinv2, Cat.id_comp]
        calc t ≫ pinv = (pinv ≫ (tG ≫ p)) ≫ pinv := by rw [h1]
          _ = pinv ≫ tG ≫ (p ≫ pinv) := by rw [Cat.assoc, Cat.assoc]
          _ = pinv ≫ tG := by rw [hpinv1, Cat.comp_id]
      -- `t ≫ h = (t ≫ pinv) ≫ G.arr ≫ snd = (pinv ≫ tG) ≫ G.arr ≫ snd
      --        = pinv ≫ (G.arr ≫ S) ≫ snd = pinv ≫ G.arr ≫ (snd ≫ f) = h ≫ f`.
      have step : (t ≫ pinv) ≫ G.arr ≫ snd = pinv ≫ G.arr ≫ S ≫ snd := by
        rw [htpinv, Cat.assoc, ← Cat.assoc tG G.arr snd, htG, Cat.assoc]
      calc t ≫ pinv ≫ G.arr ≫ snd
          = (t ≫ pinv) ≫ G.arr ≫ snd := by rw [Cat.assoc]
        _ = pinv ≫ G.arr ≫ S ≫ snd := step
        _ = pinv ≫ G.arr ≫ snd ≫ f := by rw [hSsnd]
        _ = (pinv ≫ G.arr ≫ snd) ≫ f := by rw [Cat.assoc, Cat.assoc]
  · -- UNIQUENESS via the equalizer + the §1.988 Peano property (`peano_property_of_bicartesian`).
    intro e he0 hes
    -- Equalizer subobject `E = eq(e, id_A) ↣ A`; its map `m` is monic.
    let m : eqObj e (Cat.id A) ⟶ A := eqMap e (Cat.id A)
    have hm_eq : m ≫ e = m ≫ Cat.id A := eqMap_eq e (Cat.id A)
    have hm_mono : Monic m := by
      intro W u v huv
      have hu : u = eqLift e (Cat.id A) (u ≫ m) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) :=
        eqLift_uniq e (Cat.id A) (u ≫ m) _ u rfl
      have hv : v = eqLift e (Cat.id A) (u ≫ m) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) :=
        eqLift_uniq e (Cat.id A) (u ≫ m) _ v huv.symm
      rw [hu, hv]
    let E : Subobject 𝒞 A := ⟨eqObj e (Cat.id A), m, hm_mono⟩
    -- `E` allows `a`: `a ≫ e = a = a ≫ id_A`, so `a` lifts to `E`.
    have hEa : Allows E a :=
      ⟨eqLift e (Cat.id A) a (by rw [he0, Cat.comp_id]),
       eqLift_fac e (Cat.id A) a (by rw [he0, Cat.comp_id])⟩
    -- `E` is `t`-stable: `m ≫ t` still equalizes `e, id_A`
    --   (`m≫t≫e = m≫e≫t = m≫id≫t = m≫t≫id`, using `t≫e=e≫t` and `m≫e=m≫id`).
    have hmt_eq : (m ≫ t) ≫ e = (m ≫ t) ≫ Cat.id A := by
      calc (m ≫ t) ≫ e = m ≫ t ≫ e := Cat.assoc _ _ _
        _ = m ≫ e ≫ t := by rw [hes]
        _ = (m ≫ e) ≫ t := (Cat.assoc _ _ _).symm
        _ = (m ≫ Cat.id A) ≫ t := by rw [hm_eq]
        _ = m ≫ t := by rw [Cat.comp_id]
        _ = (m ≫ t) ≫ Cat.id A := (Cat.comp_id _).symm
    have hEt : ∃ tE : E.dom ⟶ E.dom, tE ≫ E.arr = E.arr ≫ t :=
      ⟨eqLift e (Cat.id A) (m ≫ t) hmt_eq, eqLift_fac e (Cat.id A) (m ≫ t) hmt_eq⟩
    -- `E` entire by the §1.988 Peano property; its map `m` is iso, left-cancelling `e = id_A`.
    have hEent : E.IsEntire := peano_property_of_bicartesian hbool a t hiso hcoeq E hEa hEt
    obtain ⟨m', _, hm'm⟩ := hEent
    calc e = Cat.id A ≫ e := (Cat.id_comp _).symm
      _ = (m' ≫ m) ≫ e := by rw [hm'm]
      _ = m' ≫ m ≫ e := Cat.assoc _ _ _
      _ = m' ≫ m ≫ Cat.id A := by rw [hm_eq]
      _ = (m' ≫ m) ≫ Cat.id A := (Cat.assoc _ _ _).symm
      _ = Cat.id A ≫ Cat.id A := by rw [hm'm]
      _ = Cat.id A := Cat.id_comp _

/-- **§1.987 PEANO PROPERTY from bicartesian data (BOOLEAN).**  In a BOOLEAN topos
    (`hbool`), every `(a,t)`-closed subobject `B ↣ A` of bicartesian data
    `[a,t] : 1+A ≅ A` is entire.

    This is just `PeanoProperty a t` packaged, delivered directly by Freyd's §1.988
    complement argument (`peano_property_of_bicartesian`) — no longer routed through the
    recursor (which removes the old `peano ⟺ recursor` circularity). -/
theorem peano_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
    (hbool : BooleanSub 𝒞)
    {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A)
    (hiso : IsIso (HasBinaryCoproducts.case a t (A := one) (B := A) (X := A)))
    (hcoeq : ∀ (X : 𝒞) (f : A ⟶ X), t ≫ f = f →
               ∃ g : (one ⟶ X), term A ≫ g = f ∧
                 ∀ g' : one ⟶ X, term A ≫ g' = f → g' = g) :
    @PeanoProperty 𝒞 _ (Topos.toHasSubobjectClassifier.toHasTerminal) _ A a t :=
  fun B hBa hBt => peano_property_of_bicartesian hbool a t hiso hcoeq B hBa hBt

/-- **Recursor UNIQUENESS from bicartesian data** (§1.987 via the equalizer).
    Any two `(a,t)`-recursors `h, h' : A → X` (each with `a ≫ · = x` and
    `t ≫ · = · ≫ f`) are equal.  Their equalizer `E = eq(h,h') ↣ A` is `(a,t)`-closed
    (allows `a` since `a ≫ h = x = a ≫ h'`; `t`-stable since `m ≫ t` still equalizes
    `h, h'`), hence entire by `peano_of_bicartesian`; the equalizer map is then iso and
    left-cancels `h = h'`. -/
theorem recursor_unique_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
    (hbool : BooleanSub 𝒞)
    {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A)
    (hiso : IsIso (HasBinaryCoproducts.case a t (A := one) (B := A) (X := A)))
    (hcoeq : ∀ (X : 𝒞) (f : A ⟶ X), t ≫ f = f →
               ∃ g : (one ⟶ X), term A ≫ g = f ∧
                 ∀ g' : one ⟶ X, term A ≫ g' = f → g' = g)
    {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X) (h h' : A ⟶ X)
    (h0 : a ≫ h = x) (hs : t ≫ h = h ≫ f)
    (h0' : a ≫ h' = x) (hs' : t ≫ h' = h' ≫ f) :
    h = h' := by
  -- Equalizer subobject E = eq(h, h') ↣ A.  Equalizer maps are monic (proved inline by the
  -- equalizer universal property's uniqueness, to keep the `topos_has_equalizers` instance).
  let m : eqObj h h' ⟶ A := eqMap h h'
  have hm_eq : m ≫ h = m ≫ h' := eqMap_eq h h'
  have hm_mono : Monic m := by
    intro W u v huv
    have hu : u = eqLift h h' (u ≫ m) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) :=
      eqLift_uniq h h' (u ≫ m) _ u rfl
    have hv : v = eqLift h h' (u ≫ m) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) :=
      eqLift_uniq h h' (u ≫ m) _ v huv.symm
    rw [hu, hv]
  let E : Subobject 𝒞 A := ⟨eqObj h h', m, hm_mono⟩
  -- E allows a: `a ≫ h = x = a ≫ h'`, so `a` lifts to E.
  have hEa : Allows E a := by
    refine ⟨eqLift h h' a (by rw [h0, h0']), ?_⟩
    exact eqLift_fac h h' a (by rw [h0, h0'])
  -- E is t-stable: `m ≫ t` equalizes h, h' (since `m ≫ t ≫ h = m ≫ h ≫ f = m ≫ h' ≫ f
  --   = m ≫ t ≫ h'`), so lift to `tE : E → E` with `tE ≫ m = m ≫ t`.
  have hmt_eq : (m ≫ t) ≫ h = (m ≫ t) ≫ h' := by
    rw [Cat.assoc, hs, ← Cat.assoc, hm_eq, Cat.assoc, ← hs', ← Cat.assoc]
  have hEt : ∃ tE : E.dom ⟶ E.dom, tE ≫ E.arr = E.arr ≫ t := by
    exact ⟨eqLift h h' (m ≫ t) hmt_eq, eqLift_fac h h' (m ≫ t) hmt_eq⟩
  -- E entire by Peano: its arrow `m` is iso.
  have hEent : E.IsEntire := peano_of_bicartesian hbool a t hiso hcoeq E hEa hEt
  obtain ⟨m', _, hm'm⟩ := hEent
  -- `m' ≫ m = id_A` (the `cod`-side of `IsIso m`); left-cancel: h = m'≫(m≫h) = m'≫(m≫h') = h'.
  calc h = Cat.id A ≫ h := (Cat.id_comp _).symm
    _ = (m' ≫ m) ≫ h := by rw [hm'm]
    _ = m' ≫ m ≫ h := Cat.assoc _ _ _
    _ = m' ≫ m ≫ h' := by rw [hm_eq]
    _ = (m' ≫ m) ≫ h' := (Cat.assoc _ _ _).symm
    _ = Cat.id A ≫ h' := by rw [hm'm]
    _ = h' := Cat.id_comp _

/-- §1.98(10): If [a, t] : 1 + A → A is iso and A → 1 is a coequalizer of (t, id_A),
    then 1 →ᵃ A →ᵗ A is a NNO — in a BOOLEAN + CAPITAL topos (`hbool`/`hcap`).

    IN-CHAPTER FORM.  §1.98(10)'s existence step routes through §1.988/§1.989, which Freyd proves
    for a BOOLEAN (`hbool`) topos, "assuming the topos is capital [1.935]" (`hcap`).  We carry
    both hypotheses, matching the book.  The unconditional "any topos" §1.98(10) follows from the
    §1.935 reduction + the §2.542 boolean-and-capital embedding (Chapter 2); the project rule
    forbids importing Chapter 2 into Chapter 1, so the faithful in-chapter NNO is this one.

    UNIQUENESS of the recursor is fully proved here from the Peano property `peano_of_bicartesian`
    (the equalizer of two recursors is `(a,t)`-closed, hence entire); EXISTENCE is the §1.988
    `recursor_exists_of_bicartesian`, whose own residual is the §1.989 single-valuedness step. -/
theorem nno_of_bicartesian_data {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
    (hbool : BooleanSub 𝒞) (hcap : Capital (𝒞 := 𝒞)) (htv : TwoValued (𝒞 := 𝒞))
    {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A)
    -- [a, t] : 1 + A → A is an isomorphism
    (hiso : IsIso (HasBinaryCoproducts.case a t (A := one) (B := A) (X := A)))
    -- A → 1 is a coequalizer of (t, id_A)
    (hcoeq : ∀ (X : 𝒞) (f : A ⟶ X), t ≫ f = f →
               ∃ g : (one ⟶ X), term A ≫ g = f ∧
                 ∀ g' : one ⟶ X, term A ≫ g' = f → g' = g) :
    -- Then there is a NNO with underlying object A, zero a, and successor t.
    Nonempty (HasNaturalNumbersObject 𝒞) := by
  -- This is the CONVERSE of §1.985 (`nno_is_coproduct` + `nno_terminal_is_coequalizer`).
  -- We reduce the whole NNO to ONE sharp obligation `hrec`: existence of the recursor with its
  -- universal property.  Everything ELSE — packaging `hrec` into a `HasNaturalNumbersObject`
  -- whose `iterate`/`iterate_zero`/`iterate_succ`/`iterate_unique` are read off `hrec` via
  -- `Classical.choice` — is verified here.
  --
  -- `hrec` splits into EXISTENCE + UNIQUENESS.  UNIQUENESS is proven Sorry-free here:
  -- `peano_of_bicartesian` (§1.987 — every `(a,t)`-closed subobject of `A` is entire) plus the
  -- equalizer argument (`recursor_unique_of_bicartesian`) give it.  EXISTENCE is the one residual
  -- `recursor_exists_of_bicartesian`: Freyd's §1.988 recursor `h = pred ≫ case x (h ≫ f)`
  -- (`pred := [a,t]⁻¹ : A → 1+A`), the fixpoint built through the lawful per-codomain partial-map
  -- classifier (`Fredy.partialMapClassifier_exists`).  STATUS: NOT §1.543-capitalization (proven
  -- Sorry-free here); the residual is the absent §1.988 W-type / PMC recursor-fixpoint.
  have hrec : ∀ {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X),
      ∃ h : A ⟶ X, (a ≫ h = x ∧ t ≫ h = h ≫ f) ∧
        ∀ h' : A ⟶ X, a ≫ h' = x → t ≫ h' = h' ≫ f → h' = h := by
    -- EXISTENCE from the §1.988 recursor `recursor_exists_of_bicartesian` (the single residual);
    -- UNIQUENESS proved here Sorry-free from the Peano property via the equalizer
    -- (`recursor_unique_of_bicartesian`).
    intro X x f
    obtain ⟨hex, _⟩ := recursor_exists_of_bicartesian hbool hcap htv a t hiso hcoeq
    obtain ⟨h, hh0, hhs⟩ := hex x f
    exact ⟨h, ⟨hh0, hhs⟩, fun h' h0' hs' =>
      recursor_unique_of_bicartesian hbool a t hiso hcoeq x f h' h h0' hs' hh0 hhs⟩
  -- Package `hrec` into a NNO.  `iterate x f` is the chosen recursor; the three laws and
  -- uniqueness are the components of `hrec`'s ∃.
  refine ⟨{
    nno := A
    zero := a
    succ := t
    iterate := fun {X} x f => (hrec x f).choose
    iterate_zero := fun {X} x f => (hrec x f).choose_spec.1.1
    iterate_succ := fun {X} x f => (hrec x f).choose_spec.1.2
    iterate_unique := fun {X} x f h h0 hs => (hrec x f).choose_spec.2 h h0 hs }⟩

/-! ## §1.98(11)  Bicartesian functors preserve NNO

  §1.98(11): If T : 𝒜 → 𝒜' is a bicartesian functor (preserves finite limits
  and colimits) and 1 →⁰ N →ˢ N is a NNO in 𝒜, then 1 → T N → T N is a NNO
  in 𝒜'.

  This follows from the bicartesian characterization [1.985, 1.98(10)]:
  the coproduct 1 + N ≅ N and coequalizer properties are preserved by T.

  STATEMENT FIDELITY.  The earlier form of this lemma asked for
  `IsIso (T (case 0 s))`, an iso on `T(1+N)`.  But §1.98(10) at `A := T N` wants
  `IsIso (case (1≅T1 ⋙ T 0) (T s))`, an iso on `1 + T N`.  These agree only after
  the comparison `T(1+N) ≅ T1 + T N ≅ 1 + T N`.  To stay faithful we therefore
  take as hypotheses exactly the bicartesian-preservation data §1.98(11) assumes:
  a terminal-preservation point `tOne : 1 → T 1` that is iso, and the coproduct
  comparison stated directly as `IsIso (case (tOne ⋙ T 0) (T s) : 1 + T N → T N)`.
  These are precisely "T preserves 1 and the coproduct 1+N", i.e. T bicartesian. -/

/-- §1.98(11): A bicartesian functor preserves the NNO.
    The bicartesian characterization [1.985, 1.98(10)] is preserved by any
    functor that preserves finite products, coproducts, and coequalizers.

    Faithful form: `tOne : 1 → T 1` witnesses `T 1 ≅ 1` (terminal preservation),
    and `hT_iso` / `hT_coeq` are the §1.98(10) bicartesian data for
    `A := T N, a := tOne ≫ T 0, t := T s`. -/
theorem bicartesian_functor_preserves_nno
    {𝒜 : Type u} [Cat.{v} 𝒜] [hN : HasNaturalNumbersObject 𝒜]
    [HasBinaryCoproducts 𝒜] [HasImages 𝒜]
    {𝒜' : Type u} [Cat.{v} 𝒜'] [Topos 𝒜'] [HasBinaryCoproducts 𝒜'] [HasImages 𝒜']
    (hbool : BooleanSub 𝒜') (hcap : Capital (𝒞 := 𝒜')) (htv : TwoValued (𝒞 := 𝒜'))
    (T : 𝒜 → 𝒜') [hT : Functor T]
    -- T preserves the terminal up to a chosen point `tOne : 1 → T 1`; the zero of the
    -- image NNO is `tOne ≫ T 0`.  (No separate `IsIso tOne` field is needed: `hT_iso`
    -- below already forces `tOne ≫ T 0` to be the correct coproduct injection, so an
    -- extra `IsIso tOne` would be a redundant — hence non-faithful — hypothesis.)
    (tOne : (one : 𝒜') ⟶ T one)
    -- T preserves the NNO coproduct, in the form §1.98(10) consumes directly:
    -- [tOne ≫ T 0, T s] : 1 + T N → T N is an iso.
    (hT_iso : IsIso (HasBinaryCoproducts.case (tOne ≫ hT.map hN.zero) (hT.map hN.succ)
        (A := one) (B := T hN.nno) (X := T hN.nno)))
    -- T preserves the terminal coequalizer (bicartesian functors preserve colimits)
    (hT_coeq : ∀ (X : 𝒜') (f : T hN.nno ⟶ X),
      hT.map hN.succ ≫ f = f →
      ∃ g : one ⟶ X, term (T hN.nno) ≫ g = f ∧
        ∀ g' : one ⟶ X, term (T hN.nno) ≫ g' = f → g' = g) :
    Nonempty (HasNaturalNumbersObject 𝒜') := by
  -- With the faithful hypotheses the conclusion is a LITERAL instance of §1.98(10):
  --   nno_of_bicartesian_data (a := tOne ≫ T 0) (t := T s) hT_iso hT_coeq.
  -- `tOne` forms the zero map `tOne ≫ T 0` fed to `case` in `hT_iso`.  The §1.98(10) recursor is
  -- now derived internally (the old `pmc'` parameter is gone), so this reduction is purely the
  -- transport of the bicartesian data; it carries the SAME single §1.988 residual pinned there.
  exact nno_of_bicartesian_data hbool hcap htv (tOne ≫ hT.map hN.zero) (hT.map hN.succ) hT_iso hT_coeq

/-! ## §1.98(13)  Bicartesian characterization of free A-action

  §1.98(13): The analogue of the bicartesian characterization [1.985, 1.98(10)]
  holds for a free A-action A*: namely A × 1 →(1,e)→ A × A* →s→ A* is a free
  A-action iff [1 + A × A*, A*] ≅ A* (iso) and A × A* → A* → 1 is a coequalizer.
  The reasoning is analogous to [1.985] and [1.98(10)]. -/

/-- **Bridge: action-restriction ⟺ `InverseImage`-`≤` stability.**  For maps `r, proj : P → M`
    and `B ↣ M`, the `InverseImage`-form stability `(proj#B) ≤ (r#B)` used by `actLeast` is
    EQUIVALENT to the existence of a restriction `rB` of `r` along the `proj`-fibre of `B`
    (`rB ≫ B.arr = (proj#B).arr ≫ r`).  Both say "`proj(p)∈B ⟹ r(p)∈B`".  No products needed. -/
theorem invImage_le_iff_restrict {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    {M P : 𝒞} (r proj : P ⟶ M) (B : Subobject 𝒞 M) :
    (InverseImage proj B).le (InverseImage r B)
      ↔ ∃ rB : (InverseImage proj B).dom ⟶ B.dom,
          rB ≫ B.arr = (InverseImage proj B).arr ≫ r := by
  constructor
  · rintro ⟨k, hk⟩
    -- `k ≫ (r#B).arr = (proj#B).arr`; `(r#B).arr ≫ r = (r#B).π₂ ≫ B.arr`.
    refine ⟨k ≫ (HasPullbacks.has r B.arr).cone.π₂, ?_⟩
    have hw := (HasPullbacks.has r B.arr).cone.w
    show (k ≫ (HasPullbacks.has r B.arr).cone.π₂) ≫ B.arr = _
    rw [Cat.assoc, ← hw, ← Cat.assoc]
    show (k ≫ (InverseImage r B).arr) ≫ r = _
    rw [hk]
  · rintro ⟨rB, hrB⟩
    -- factor `(proj#B).arr` through `(r#B)`: lift the cone `⟨(proj#B).arr, rB⟩`.
    have hcone : (InverseImage proj B).arr ≫ r = rB ≫ B.arr := hrB.symm
    refine ⟨(HasPullbacks.has r B.arr).lift ⟨_, (InverseImage proj B).arr, rB, hcone⟩, ?_⟩
    exact (HasPullbacks.has r B.arr).lift_fst _

/-! ### §1.98(13) `prod A (−)` image calculus for the free complement chase

  The free Peano chase replaces the endo direct image `t(S) = image(S.arr ≫ t)` with the
  **act-image** `act(S) = image(prodMap A S.dom α.obj S.arr ≫ act)`.  These three lemmas
  re-establish, for that operator, the exact facts the endo proof draws from `image_post_mono`
  and `actLeast_stable`/`actLeast_le`.  `act` here is an arbitrary `prod A M → M`; in the chase
  it is `α.act` (monic, since `[unit,act]` is iso). -/

section ActImageCalculus
variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

-- Make the genuine `Topos` products win all `HasBinaryProducts` goals (the
-- `topos_has_exponentials.toHasBinaryProducts` route is a `sorry`-derived diamond branch);
-- this keeps `prodMap`/`distCase` products coherent across this section.  Same guard as
-- `Fredy/ToposCopowers.lean`.
attribute [local instance 10000] Topos.toHasBinaryProducts

/-- `prod A (−)` carries covers to covers (right-factor product map).  `prod A X` with
    `(prodMap A X Y c, snd)` is the pullback of `c : X → Y` along `snd : prod A Y → Y`
    (`prodMap_snd` is the square), and pullbacks transfer the cover `c` to the opposite
    leg `prodMap A X Y c`. -/
theorem prodMap_cover (A : 𝒞) {X Y : 𝒞} {c : X ⟶ Y} (hc : Cover c) :
    Cover (prodMap A X Y c) := by
  -- Cone over cospan `(c : X → Y, snd : prod A Y → Y)`: `π₁ = snd`, `π₂ = prodMap A X Y c`.
  have hpb : (⟨prod A X, snd, prodMap A X Y c, (prodMap_snd A X Y c).symm⟩ :
      Cone c (snd (A := A) (B := Y))).IsPullback := by
    intro d
    -- `d.π₁ : d.pt → X`, `d.π₂ : d.pt → prod A Y`, `d.w : d.π₁ ≫ c = d.π₂ ≫ snd`.
    refine ⟨pair (d.π₂ ≫ fst) d.π₁, ⟨snd_pair _ _, ?_⟩, ?_⟩
    · -- `u ≫ prodMap.. = d.π₂` by joint monicity (`snd` uses `d.w`).
      show pair (d.π₂ ≫ fst) d.π₁ ≫ prodMap A X Y c = d.π₂
      apply fst_snd_jointly_monic
      · rw [Cat.assoc, prodMap_fst, fst_pair]
      · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair]; exact d.w
    · intro v hv₁ hv₂
      -- `hv₁ : v ≫ snd = d.π₁`, `hv₂ : v ≫ prodMap.. = d.π₂`.
      apply pair_uniq
      · show v ≫ fst = d.π₂ ≫ fst
        rw [← prodMap_fst A X Y c, ← Cat.assoc]
        show (v ≫ prodMap A X Y c) ≫ fst = _; rw [hv₂]
      · exact hv₁
  intro D m g hm hgm
  exact PullbacksTransferCovers.pullbacks_transfer_covers _ hpb hc m g hm hgm

/-- `prod A (−)` carries monics to monics (right-factor product map). -/
theorem prodMap_mono' (A : 𝒞) {X Y : 𝒞} {f : X ⟶ Y} (hf : Monic f) :
    Monic (prodMap A X Y f) := by
  intro W u v huv
  have hfst : u ≫ fst = v ≫ fst := by
    have := congrArg (· ≫ fst (A := A) (B := Y)) huv
    simpa only [Cat.assoc, prodMap_fst] using this
  have hsnd : u ≫ snd = v ≫ snd := by
    apply hf
    have := congrArg (· ≫ snd (A := A) (B := Y)) huv
    simpa only [Cat.assoc, prodMap_snd] using this
  calc u = pair (u ≫ fst) (u ≫ snd) := pair_uniq _ _ u rfl rfl
    _ = pair (v ≫ fst) (v ≫ snd) := by rw [hfst, hsnd]
    _ = v := (pair_uniq _ _ v rfl rfl).symm

/-- **act-image monotonicity** (free `image_post_mono`).  If `S ≤ T` then
    `act(S) := image(prodMap A S.dom α.obj S.arr ≫ act) ≤ act(T)`.  The witness `h : h ≫ T.arr =
    S.arr` lifts to `prodMap A S.dom T.dom h` via `prodMap`-functoriality:
    `prodMap A S.dom α.obj S.arr = prodMap A S.dom T.dom h ≫ prodMap A T.dom α.obj T.arr`. -/
theorem image_act_mono {A M : 𝒞} (act : prod A M ⟶ M) {S T : Subobject 𝒞 M} (hST : S.le T) :
    (image (prodMap A S.dom M S.arr ≫ act)).le (image (prodMap A T.dom M T.arr ≫ act)) := by
  obtain ⟨h, hh⟩ := hST
  refine image_min _ _ ⟨prodMap A S.dom T.dom h ≫ image.lift (prodMap A T.dom M T.arr ≫ act), ?_⟩
  rw [Cat.assoc, image.lift_fac, ← Cat.assoc, ← prodMap_comp, hh]

/-- **act-stability in image form** (free `actLeast`-consumer).  `S ↣ M` is `(act,snd)`-stable
    (`(snd#S) ≤ (act#S)`) iff its act-image lands in it: `act(S) ≤ S`.  The `prod A S.dom`
    cone `(prodMap.., snd)` over `(snd, S.arr)` lifts into the `snd#S` pullback, transporting
    the restriction back to the act-image factorisation. -/
theorem actImg_le_of_actStable {A M : 𝒞} (act : prod A M ⟶ M) (S : Subobject 𝒞 M)
    (hstab : (InverseImage (snd (A := A) (B := M)) S).le (InverseImage act S)) :
    (image (prodMap A S.dom M S.arr ≫ act)).le S := by
  obtain ⟨actS, hactS⟩ := (invImage_le_iff_restrict act (snd (A := A) (B := M)) S).1 hstab
  -- lift `prod A S.dom → (snd#S).dom` via the pullback of `(snd, S.arr)`.
  let pb := HasPullbacks.has (snd (A := A) (B := M)) S.arr
  have hsq : prodMap A S.dom M S.arr ≫ snd = snd ≫ S.arr := prodMap_snd A S.dom M S.arr
  let j : prod A S.dom ⟶ (InverseImage (snd (A := A) (B := M)) S).dom :=
    pb.lift ⟨prod A S.dom, prodMap A S.dom M S.arr, snd, hsq⟩
  have hj : j ≫ (InverseImage (snd (A := A) (B := M)) S).arr = prodMap A S.dom M S.arr :=
    pb.lift_fst _
  -- `prodMap.. ≫ act = j ≫ (snd#S).arr ≫ act = j ≫ actS ≫ S.arr = (j ≫ actS) ≫ S.arr`.
  refine image_min _ _ ⟨j ≫ actS, ?_⟩
  rw [Cat.assoc, hactS, ← Cat.assoc, hj]

/-- **act-stability from a restriction** (reverse of `actImg_le_of_actStable`).  Given a
    restriction `actS : prod A S.dom → S.dom` of `act` along `S` (`actS ≫ S.arr = prodMap.. ≫
    act`), `S` is `(act,snd)`-stable: `(snd#S) ≤ (act#S)`.  Re-pairs `(snd#S).arr` into
    `prod A S.dom` (legs `fst`, `π₂`) to feed `actS`.  Factored out of the `hBstab` step. -/
theorem actStable_of_restrict {A M : 𝒞} (act : prod A M ⟶ M) (S : Subobject 𝒞 M)
    (actS : prod A S.dom ⟶ S.dom)
    (hactS : actS ≫ S.arr = prodMap A S.dom M S.arr ≫ act) :
    (InverseImage (snd (A := A) (B := M)) S).le (InverseImage act S) := by
  rw [invImage_le_iff_restrict]
  let pb := HasPullbacks.has (snd (A := A) (B := M)) S.arr
  let w : (InverseImage (snd (A := A) (B := M)) S).dom ⟶ prod A S.dom :=
    pair ((InverseImage (snd (A := A) (B := M)) S).arr ≫ fst) pb.cone.π₂
  have hw : w ≫ prodMap A S.dom M S.arr = (InverseImage (snd (A := A) (B := M)) S).arr := by
    have hfstleg : (w ≫ prodMap A S.dom M S.arr) ≫ fst
        = (InverseImage (snd (A := A) (B := M)) S).arr ≫ fst := by
      rw [Cat.assoc, prodMap_fst]; show (pair _ pb.cone.π₂ ≫ fst) = _; rw [fst_pair]
    have hsndleg : (w ≫ prodMap A S.dom M S.arr) ≫ snd
        = (InverseImage (snd (A := A) (B := M)) S).arr ≫ snd := by
      rw [Cat.assoc, prodMap_snd, ← Cat.assoc]
      show (pair _ pb.cone.π₂ ≫ snd) ≫ S.arr = _
      rw [snd_pair]; exact pb.cone.w.symm
    rw [pair_uniq _ _ (w ≫ prodMap A S.dom M S.arr) hfstleg hsndleg,
        ← pair_uniq _ _ ((InverseImage (snd (A := A) (B := M)) S).arr) rfl rfl]
  exact ⟨w ≫ actS, by rw [Cat.assoc, hactS, ← Cat.assoc, hw]⟩

/-- **act-image of a union** (free analogue of the endo `himg_le` decomposition).
    `act(S ∪ T) ≤ act(S) ∪ act(T)`.  The union cover `case l₁ l₂ : S.dom + T.dom ↠ (S∪T).dom`
    is carried to a cover of `prod A (S∪T).dom` by `prodMap_cover`; the composite act-map
    rewrites (via `prodMap` functoriality + `distCase_uniq`) to `distCase` of the two legs,
    whose image copairs through `act(S) ∪ act(T)`. -/
theorem image_act_union_le [HasBinaryCoproducts 𝒞]
    {A M : 𝒞} (act : prod A M ⟶ M) (S T : Subobject 𝒞 M) :
    (image (prodMap A (HasSubobjectUnions.union S T).dom M
              (HasSubobjectUnions.union S T).arr ≫ act)).le
      (HasSubobjectUnions.union (image (prodMap A S.dom M S.arr ≫ act))
                                (image (prodMap A T.dom M T.arr ≫ act))) := by
  obtain ⟨l₁, hl₁⟩ := HasSubobjectUnions.union_left S T
  obtain ⟨l₂, hl₂⟩ := HasSubobjectUnions.union_right S T
  let U : Subobject 𝒞 M := HasSubobjectUnions.union S T
  let cov : HasBinaryCoproducts.coprod S.dom T.dom ⟶ U.dom :=
    HasBinaryCoproducts.case l₁ l₂
  have hcov : Cover cov := union_case_cover S T hl₁ hl₂
  -- the cover on `prod A U.dom`.
  have hPcov : Cover (prodMap A (HasBinaryCoproducts.coprod S.dom T.dom) U.dom cov) :=
    prodMap_cover A hcov
  -- `image(prodMap U.arr ≫ act) = image(prodMap cov ≫ (prodMap U.arr ≫ act))`.
  have h1 : (image (prodMap A U.dom M U.arr ≫ act)).le
      (image (prodMap A (HasBinaryCoproducts.coprod S.dom T.dom) U.dom cov
                ≫ (prodMap A U.dom M U.arr ≫ act))) :=
    (image_cover_comp (prodMap A (HasBinaryCoproducts.coprod S.dom T.dom) U.dom cov)
      (prodMap A U.dom M U.arr ≫ act) hPcov).2
  -- the composite = `distCase (prodMap.. S.arr ≫ act) (prodMap.. T.arr ≫ act)`.
  let F : prod A S.dom ⟶ M := prodMap A S.dom M S.arr ≫ act
  let G : prod A T.dom ⟶ M := prodMap A T.dom M T.arr ≫ act
  have hcomp : prodMap A (HasBinaryCoproducts.coprod S.dom T.dom) U.dom cov
      ≫ (prodMap A U.dom M U.arr ≫ act) = distCase F G := by
    rw [← Cat.assoc, ← prodMap_comp]
    -- `cov ≫ U.arr = case S.arr T.arr` (legs `l₁≫U.arr=S.arr`, `l₂≫U.arr=T.arr`).
    have hcovU : cov ≫ U.arr = HasBinaryCoproducts.case S.arr T.arr := by
      show HasBinaryCoproducts.case l₁ l₂ ≫ U.arr = _
      rw [case_comp, hl₁, hl₂]
    rw [hcovU]
    -- `prodMap (case S.arr T.arr) ≫ act = distCase F G` by `distCase_uniq` on the two inj.
    refine distCase_uniq F G _ ?_ ?_
    · show distInl A S.dom T.dom ≫ (prodMap A _ M (HasBinaryCoproducts.case S.arr T.arr) ≫ act) = F
      show prodMap A S.dom _ HasBinaryCoproducts.inl
            ≫ (prodMap A _ M (HasBinaryCoproducts.case S.arr T.arr) ≫ act) = F
      rw [← Cat.assoc, ← prodMap_comp, HasBinaryCoproducts.case_inl]
    · show distInr A S.dom T.dom ≫ (prodMap A _ M (HasBinaryCoproducts.case S.arr T.arr) ≫ act) = G
      show prodMap A T.dom _ HasBinaryCoproducts.inr
            ≫ (prodMap A _ M (HasBinaryCoproducts.case S.arr T.arr) ≫ act) = G
      rw [← Cat.assoc, ← prodMap_comp, HasBinaryCoproducts.case_inr]
  rw [hcomp] at h1
  -- `image(distCase F G) ≤ act(S) ∪ act(T)` via `image_min` + `distCase`-copairing of lifts.
  refine subLe_trans' h1 ?_
  obtain ⟨jL, hjL⟩ := HasSubobjectUnions.union_left (image F) (image G)
  obtain ⟨jR, hjR⟩ := HasSubobjectUnions.union_right (image F) (image G)
  refine image_min _ _ ⟨distCase (image.lift F ≫ jL) (image.lift G ≫ jR), ?_⟩
  -- the factoring `distCase(...) ≫ union.arr = distCase F G` by `distCase_uniq`.
  refine distCase_uniq F G _ ?_ ?_
  · rw [← Cat.assoc, distCase_inl, Cat.assoc, hjL, image.lift_fac]
  · rw [← Cat.assoc, distCase_inr, Cat.assoc, hjR, image.lift_fac]

end ActImageCalculus

-- The free §1.98(13) chases use `prodMap`/`distCase`; make the genuine `Topos` products win
-- all `HasBinaryProducts` goals (avoids the `topos_has_exponentials.toHasBinaryProducts`
-- `sorry`-derived diamond branch), keeping every `prod`/`image` term coherent (cf. `ToposCopowers`).
attribute [local instance 10000] Topos.toHasBinaryProducts

/-- **§1.98(13) action PEANO PROPERTY in a BOOLEAN topos (the §1.988 free content).**
    Every `(unit,act)`-closed subobject `B ↣ α.obj` is entire.  `B` closed = it allows
    `unit` (point `uB : 1 → B.dom`, `uB ≫ B.arr = α.unit`) and is `act`-stable
    (`actB : A×B.dom → B.dom`, `actB ≫ B.arr = prodMap A B.dom α.obj B.arr ≫ α.act`).

    PROOF.  The A-parametrised analogue of `peano_property_of_bicartesian`: take the least
    `(unit,act)`-closed subobject `α'`, complement it (`hbool`) to `α' + α''`, and use the
    coequalizer `α.act = snd ≫ f` collapse to force `α'' = 0`.  Same complement structure as
    the NNO case for the functor `1 + A×(−)`. -/
theorem free_peano_property_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞]
    (hbool : BooleanSub 𝒞)
    (A : 𝒞) (α : AAction (𝒞 := 𝒞) A)
    (hiso : IsIso (HasBinaryCoproducts.case α.unit α.act
                   (A := one) (B := prod A α.obj) (X := α.obj)))
    (hcoeq : ∀ (X : 𝒞) (f : α.obj ⟶ X),
               α.act ≫ f = snd (A := A) (B := α.obj) ≫ f →
               ∃ g : one ⟶ X, term α.obj ≫ g = f ∧
                 ∀ g' : one ⟶ X, term α.obj ≫ g' = f → g' = g)
    (B : Subobject 𝒞 α.obj)
    (huB : ∃ uB : one ⟶ B.dom, uB ≫ B.arr = α.unit)
    (hactB : ∃ actB : prod A B.dom ⟶ B.dom,
        actB ≫ B.arr = prodMap A B.dom α.obj B.arr ≫ α.act) :
    B.IsEntire := by
  classical
  -- §1.988 free Peano property.  The PARAMETRISED least `(unit, act, snd)`-closed subobject
  -- `A' := actLeast unit act snd` (built Sorry-free in `LeastClosedTopos.lean`) is the A-action
  -- analogue of `HasLeastClosedSubobject.least`.  `actLeast_allows`/`actLeast_stable` make it
  -- `(unit,act)`-closed; `actLeast_le` makes it ≤ every closed `B`.  With these in hand the proof
  -- splits exactly like `peano_property_of_bicartesian`:
  --   REDUCTION (no booleanness):  `A' ≤ B` (leastness) + `A'` entire ⟹ `B.arr` split epi + monic
  --     ⟹ iso ⟹ `B` entire.  [CLOSED below.]
  --   `A'` ENTIRE:  Freyd's §1.988 BOOLEAN complement chase — complement `A''` of `A'`, show `A''`
  --     is `act`-stable (so `[unit,act]` is block-diagonal), build `e : α.obj → 1+1` with
  --     `act ≫ e = snd ≫ e`, apply `hcoeq` to collapse `e` to constant `inl`, forcing `A'' = 0`.
  --     [the one residual `sorry` — the product-indexed port of the endo chase.]
  let A' : Subobject 𝒞 α.obj := actLeast α.unit α.act (snd (A := A) (B := α.obj))
  -- B is `(unit,act,snd)`-closed: allows `unit` (`huB`), and `(snd#B) ≤ (act#B)` via the bridge.
  obtain ⟨uB, huB'⟩ := huB
  have hBallows : Allows B α.unit := ⟨uB, huB'⟩
  have hBstab : (InverseImage (snd (A := A) (B := α.obj)) B).le (InverseImage α.act B) := by
    obtain ⟨actB, hactB'⟩ := hactB
    exact actStable_of_restrict α.act B actB hactB'
  -- REDUCTION:  `A'` entire ⟹ `B` entire.
  suffices hA'entire : A'.IsEntire by
    obtain ⟨ai, _hai1, hai2⟩ := hA'entire
    obtain ⟨k, hk⟩ := actLeast_le α.unit α.act snd B hBallows hBstab
    refine ⟨ai ≫ k, ?_, ?_⟩
    · apply B.monic
      rw [Cat.assoc, Cat.assoc, hk, hai2, Cat.id_comp, Cat.comp_id]
    · rw [Cat.assoc, hk, hai2]
  -- `A'` ENTIRE — the §1.988 BOOLEAN complement chase, A-parametrised over `prod A (−)`.
  -- A-action analogue of `peano_property_of_bicartesian`: `act : prod A α.obj → α.obj` (monic,
  -- since `[unit,act]` iso) replaces the endo `t`; `act(S) := image(prodMap A S.dom α.obj S.arr
  -- ≫ act)` replaces `t(S)`.  The `ActImageCalculus` lemmas re-establish every image fact.
  obtain ⟨A'', hdisj, hentire⟩ := hbool A'
  obtain ⟨ψ, ψinv, hψ1, hψ2, hψinl, hψinr⟩ := complementedSub_legs_iso A' A'' hdisj hentire
  -- `A'` is `(unit,act,snd)`-closed:  allows `unit` (`actLeast_allows`) and act-stable
  -- (`actLeast_stable` → image form via `actImg_le_of_actStable`).
  obtain ⟨a₀, ha₀⟩ := actLeast_allows α.unit α.act (snd (A := A) (B := α.obj))
  -- `act` restricts to `A'` in image form: `act(A') ≤ A'`.
  have hA'act : (image (prodMap A A'.dom α.obj A'.arr ≫ α.act)).le A' :=
    actImg_le_of_actStable α.act A' (actLeast_stable α.unit α.act (snd (A := A) (B := α.obj)))
  -- β-laws and inverse of the iso `case unit act`.
  have hcl : HasBinaryCoproducts.inl ≫ HasBinaryCoproducts.case α.unit α.act = α.unit :=
    HasBinaryCoproducts.case_inl α.unit α.act
  have hcr : HasBinaryCoproducts.inr ≫ HasBinaryCoproducts.case α.unit α.act = α.act :=
    HasBinaryCoproducts.case_inr α.unit α.act
  obtain ⟨ci, hci1, hci2⟩ := hiso
  -- `inr` (hypothesis coproduct) is monic.  No point of `prod A α.obj` to retract with (the endo
  -- trick), so transport through the comparison `φ` to the CANONICAL coproduct, whose `coprodInr`
  -- is monic (`coprodInr_monic`):  `inr ≫ φ = coprodInr`.
  have hinr_mono : Monic (HasBinaryCoproducts.inr (A := one) (B := prod A α.obj)) := by
    intro W g h hgh
    let φ : HasBinaryCoproducts.coprod (one : 𝒞) (prod A α.obj)
        ⟶ coprodObj (one : 𝒞) (prod A α.obj) :=
      HasBinaryCoproducts.case (coprodInl (one : 𝒞) (prod A α.obj))
        (coprodInr (one : 𝒞) (prod A α.obj))
    have hr : HasBinaryCoproducts.inr ≫ φ = coprodInr (one : 𝒞) (prod A α.obj) :=
      HasBinaryCoproducts.case_inr _ _
    apply coprodInr_monic (one : 𝒞) (prod A α.obj)
    rw [← hr, ← Cat.assoc, ← Cat.assoc, hgh]
  -- `act` monic: `act = inr ≫ case`, `inr` monic, `case` iso.
  have hactmono : Monic α.act := by
    intro W g h hgh
    apply hinr_mono
    have e : (g ≫ HasBinaryCoproducts.inr) ≫ HasBinaryCoproducts.case α.unit α.act
        = (h ≫ HasBinaryCoproducts.inr) ≫ HasBinaryCoproducts.case α.unit α.act := by
      rw [Cat.assoc, Cat.assoc, hcr, hgh]
    have := congrArg (· ≫ ci) e
    simpa only [Cat.assoc, hci1, Cat.comp_id] using this
  -- `≤ ⊥` from a HYPOTHESIS-coproduct common point (`u ≫ inl = v ≫ inr`), via canonical injections.
  have hbot_hyp : ∀ (Z : Subobject 𝒞 α.obj) (u : Z.dom ⟶ one) (v : Z.dom ⟶ prod A α.obj),
      u ≫ HasBinaryCoproducts.inl = v ≫ HasBinaryCoproducts.inr →
      Z.le (PreLogos.bottom α.obj) := by
    intro Z u v huv
    let φ : HasBinaryCoproducts.coprod (one : 𝒞) (prod A α.obj)
        ⟶ coprodObj (one : 𝒞) (prod A α.obj) :=
      HasBinaryCoproducts.case (coprodInl (one : 𝒞) (prod A α.obj))
        (coprodInr (one : 𝒞) (prod A α.obj))
    have hcommon : u ≫ coprodInl (one : 𝒞) (prod A α.obj)
        = v ≫ coprodInr (one : 𝒞) (prod A α.obj) := by
      have hl : HasBinaryCoproducts.inl ≫ φ = coprodInl (one : 𝒞) (prod A α.obj) :=
        HasBinaryCoproducts.case_inl _ _
      have hr : HasBinaryCoproducts.inr ≫ φ = coprodInr (one : 𝒞) (prod A α.obj) :=
        HasBinaryCoproducts.case_inr _ _
      calc u ≫ coprodInl (one : 𝒞) (prod A α.obj)
          = u ≫ HasBinaryCoproducts.inl ≫ φ := by rw [hl]
        _ = (u ≫ HasBinaryCoproducts.inl) ≫ φ := (Cat.assoc _ _ _).symm
        _ = (v ≫ HasBinaryCoproducts.inr) ≫ φ := by rw [huv]
        _ = v ≫ HasBinaryCoproducts.inr ≫ φ := Cat.assoc _ _ _
        _ = v ≫ coprodInr (one : 𝒞) (prod A α.obj) := by rw [hr]
    exact le_bottom_of_canonical_common Z u v hcommon
  -- ── THE CLAIM (Freyd §1.988 / §1.635, §1.641): `act` restricts to the complement `A''`.
  have hclaim : ∃ act'' : prod A A''.dom ⟶ A''.dom,
      act'' ≫ A''.arr = prodMap A A''.dom α.obj A''.arr ≫ α.act := by
    -- the three monic subobjects.  `unit`, `prodMap A'.arr ≫ act`, `prodMap A''.arr ≫ act` monic.
    have hu_mono : Monic α.unit := mono_from_one α.unit
    let aSub : Subobject 𝒞 α.obj := Subobject.mk one α.unit hu_mono
    let actA' : Subobject 𝒞 α.obj := Subobject.mk (prod A A'.dom)
      (prodMap A A'.dom α.obj A'.arr ≫ α.act) (mono_comp'' (prodMap_mono' A A'.monic) hactmono)
    let actA'' : Subobject 𝒞 α.obj := Subobject.mk (prod A A''.dom)
      (prodMap A A''.dom α.obj A''.arr ≫ α.act) (mono_comp'' (prodMap_mono' A A''.monic) hactmono)
    -- ── basic `≤`-facts.
    have haSub_le : aSub.le A' := ⟨a₀, ha₀⟩
    -- `actA' = act(A')` as a monic subobject; `actA' ≤ image(..) ≤ A'`.
    have hactA'_eq : (image (prodMap A A'.dom α.obj A'.arr ≫ α.act)).le actA' ∧
        actA'.le (image (prodMap A A'.dom α.obj A'.arr ≫ α.act)) :=
      image_mono_eq (prodMap A A'.dom α.obj A'.arr ≫ α.act)
        (mono_comp'' (prodMap_mono' A A'.monic) hactmono)
    have hactA'_le : actA'.le A' := subLe_trans' hactA'_eq.2 hA'act
    -- the union `U := unit(1) ∪ act(A×A')`.
    let U : Subobject 𝒞 α.obj := HasSubobjectUnions.union aSub actA'
    have hactA'_U : actA'.le U := HasSubobjectUnions.union_right aSub actA'
    have haSub_U : aSub.le U := HasSubobjectUnions.union_left aSub actA'
    -- ── `A' ≤ U`: `U` is `(unit,act,snd)`-closed, leastness gives it.
    have hA'U : A'.le U := by
      refine actLeast_le α.unit α.act (snd (A := A) (B := α.obj)) U ?_ ?_
      · -- `U` allows `unit`: `unit = aSub.arr` factors through `aSub ≤ U`.
        obtain ⟨l, hl⟩ := haSub_U
        exact ⟨l, by show l ≫ U.arr = α.unit; rw [hl]⟩
      · -- `U` is act-stable: `act(U) ≤ U` (image form) then `actStable_of_restrict`.
        have himg_le : (image (prodMap A U.dom α.obj U.arr ≫ α.act)).le U := by
          -- `act(U) ≤ act(aSub) ∪ act(actA')` (`image_act_union_le`), each leg ≤ U DIRECTLY
          -- (NOT via `A' ≤ U`, which is what we are proving — that would be circular).
          refine subLe_trans' (image_act_union_le α.act aSub actA') ?_
          refine HasSubobjectUnions.union_min _ _ _ ?_ ?_
          · -- `act(aSub) ≤ actA' ≤ U`: `unit≫act = a₀≫(A'.arr)≫act = prodMap a₀ ≫ actA'.arr`.
            refine subLe_trans' (image_min _ actA' ⟨prodMap A one A'.dom a₀, ?_⟩) hactA'_U
            show prodMap A one A'.dom a₀ ≫ (prodMap A A'.dom α.obj A'.arr ≫ α.act)
                = prodMap A one α.obj α.unit ≫ α.act
            rw [← Cat.assoc, ← prodMap_comp, ha₀]
          · -- `act(actA') ≤ act(A') ≤ actA' ≤ U`  (`image_act_mono` with actA' ≤ A').
            refine subLe_trans' (image_act_mono α.act hactA'_le) ?_
            exact subLe_trans' hactA'_eq.1 hactA'_U
        obtain ⟨k, hk⟩ := himg_le
        exact actStable_of_restrict α.act U (image.lift (prodMap A U.dom α.obj U.arr ≫ α.act) ≫ k)
          (by rw [Cat.assoc, hk, image.lift_fac])
    have hUA' : U.le A' := HasSubobjectUnions.union_min _ _ _ haSub_le hactA'_le
    -- ── `act(A'') ∩ A' ≤ 0`, via `A' ≤ U = unit(1) ∪ act(A×A')` and distributivity.
    have hdisj' : (Subobject.inter A'
        (image (prodMap A A''.dom α.obj A''.arr ≫ α.act))).le (PreLogos.bottom α.obj) := by
      -- `image(prodMap A''.. ≫ act) = actA''` (image of monic).
      have heq : (image (prodMap A A''.dom α.obj A''.arr ≫ α.act)).le actA'' :=
        (image_mono_eq (prodMap A A''.dom α.obj A''.arr ≫ α.act)
          (mono_comp'' (prodMap_mono' A A''.monic) hactmono)).1
      have hmono_inter : (Subobject.inter A'
          (image (prodMap A A''.dom α.obj A''.arr ≫ α.act))).le (Subobject.inter actA'' U) :=
        subLe_trans' (Subobject.inter_mono hA'U heq) (inter_comm_le U actA'')
      -- distribute `inter actA'' U = inter actA'' (aSub ∪ actA') ≤ (actA''∩aSub) ∪ (actA''∩actA')`.
      have hdist : (Subobject.inter actA'' U).le
          (HasSubobjectUnions.union (Subobject.inter actA'' aSub)
            (Subobject.inter actA'' actA')) := by
        have e1 : Subobject.inter actA'' U
            = pushMono actA''.arr actA''.monic (InverseImage actA''.arr U) := rfl
        have e2 : Subobject.inter actA'' aSub
            = pushMono actA''.arr actA''.monic (InverseImage actA''.arr aSub) := rfl
        have e3 : Subobject.inter actA'' actA'
            = pushMono actA''.arr actA''.monic (InverseImage actA''.arr actA') := rfl
        rw [e1, e2, e3]
        have hpre : (InverseImage actA''.arr U).le
            (HasSubobjectUnions.union (InverseImage actA''.arr aSub)
              (InverseImage actA''.arr actA')) :=
          (PreLogos.invImage_preserves_union actA''.arr aSub actA').1
        exact subLe_trans' (pushMono_mono actA''.arr actA''.monic hpre)
          (pushMono_union_le actA''.arr actA''.monic _ _)
      -- `actA'' ∩ aSub ≤ 0`  (act(A'') ∩ unit(1): hypothesis-coproduct disjointness).
      have hbot1 : (Subobject.inter actA'' aSub).le (PreLogos.bottom α.obj) := by
        let pb := HasPullbacks.has actA''.arr aSub.arr
        have hsq : pb.cone.π₁ ≫ actA''.arr = pb.cone.π₂ ≫ aSub.arr := pb.cone.w
        -- `act = inr≫case`, `unit = inl≫case` ⟹ `π₂≫inl = (π₁≫prodMap A''.arr)≫inr`.
        have hcancel : pb.cone.π₂ ≫ HasBinaryCoproducts.inl
            = (pb.cone.π₁ ≫ prodMap A A''.dom α.obj A''.arr) ≫ HasBinaryCoproducts.inr := by
          have hsq' : pb.cone.π₂ ≫ α.unit
              = (pb.cone.π₁ ≫ prodMap A A''.dom α.obj A''.arr) ≫ α.act := by
            rw [Cat.assoc]; exact hsq.symm
          have hc : (pb.cone.π₂ ≫ HasBinaryCoproducts.inl)
                ≫ HasBinaryCoproducts.case α.unit α.act
              = ((pb.cone.π₁ ≫ prodMap A A''.dom α.obj A''.arr) ≫ HasBinaryCoproducts.inr)
                ≫ HasBinaryCoproducts.case α.unit α.act := by
            rw [Cat.assoc, Cat.assoc, hcl, hcr]; exact hsq'
          calc pb.cone.π₂ ≫ HasBinaryCoproducts.inl
              = ((pb.cone.π₂ ≫ HasBinaryCoproducts.inl)
                  ≫ HasBinaryCoproducts.case α.unit α.act) ≫ ci := by
                rw [Cat.assoc, hci1, Cat.comp_id]
            _ = (((pb.cone.π₁ ≫ prodMap A A''.dom α.obj A''.arr) ≫ HasBinaryCoproducts.inr)
                  ≫ HasBinaryCoproducts.case α.unit α.act) ≫ ci := by rw [hc]
            _ = (pb.cone.π₁ ≫ prodMap A A''.dom α.obj A''.arr) ≫ HasBinaryCoproducts.inr := by
                rw [Cat.assoc, hci1, Cat.comp_id]
        exact hbot_hyp (Subobject.inter actA'' aSub) pb.cone.π₂
          (pb.cone.π₁ ≫ prodMap A A''.dom α.obj A''.arr) hcancel
      -- `actA'' ∩ actA' ≤ 0`  (act(A'') ∩ act(A'): `act` monic + `snd` descends to A'∩A'' ≤ 0).
      have hbot2 : (Subobject.inter actA'' actA').le (PreLogos.bottom α.obj) := by
        let pb := HasPullbacks.has actA''.arr actA'.arr
        have hsq : pb.cone.π₁ ≫ actA''.arr = pb.cone.π₂ ≫ actA'.arr := pb.cone.w
        -- `(π₁≫prodMap A''..)≫act = (π₂≫prodMap A'..)≫act ⟹ (act monic) the prodMaps agree`.
        have hprod : pb.cone.π₁ ≫ prodMap A A''.dom α.obj A''.arr
            = pb.cone.π₂ ≫ prodMap A A'.dom α.obj A'.arr := by
          apply hactmono
          rw [Cat.assoc, Cat.assoc]; exact hsq
        -- post-compose `snd`: gives a common point of A', A'' in `α.obj`.
        have hcommon : (pb.cone.π₂ ≫ snd) ≫ A'.arr = (pb.cone.π₁ ≫ snd) ≫ A''.arr := by
          have hL : pb.cone.π₁ ≫ snd ≫ A''.arr = pb.cone.π₂ ≫ snd ≫ A'.arr := by
            calc pb.cone.π₁ ≫ snd ≫ A''.arr
                = pb.cone.π₁ ≫ (prodMap A A''.dom α.obj A''.arr ≫ snd) := by rw [prodMap_snd]
              _ = (pb.cone.π₁ ≫ prodMap A A''.dom α.obj A''.arr) ≫ snd := (Cat.assoc _ _ _).symm
              _ = (pb.cone.π₂ ≫ prodMap A A'.dom α.obj A'.arr) ≫ snd := by rw [hprod]
              _ = pb.cone.π₂ ≫ (prodMap A A'.dom α.obj A'.arr ≫ snd) := Cat.assoc _ _ _
              _ = pb.cone.π₂ ≫ snd ≫ A'.arr := by rw [prodMap_snd]
          rw [Cat.assoc, Cat.assoc]; exact hL.symm
        -- lift into `inter A' A''`; `hdisj` maps it to ⊥.
        let pbAA := HasPullbacks.has A'.arr A''.arr
        let w : (Subobject.inter actA'' actA').dom ⟶ (Subobject.inter A' A'').dom :=
          pbAA.lift ⟨_, pb.cone.π₂ ≫ snd, pb.cone.π₁ ≫ snd, hcommon⟩
        obtain ⟨m, _⟩ := hdisj
        exact peano_le_bottom_of_map (Subobject.inter actA'' actA') (w ≫ m)
      exact subLe_trans' hmono_inter (subLe_trans' hdist
        (HasSubobjectUnions.union_min _ _ _ hbot1 hbot2))
    -- `complement_le_other'` gives `act(A'') ≤ A''`; descend to the restriction `act''`.
    have htle : (image (prodMap A A''.dom α.obj A''.arr ≫ α.act)).le A'' :=
      complement_le_other' A' A'' (image (prodMap A A''.dom α.obj A''.arr ≫ α.act))
        hdisj' hentire
    obtain ⟨k, hk⟩ := htle
    exact ⟨image.lift (prodMap A A''.dom α.obj A''.arr ≫ α.act) ≫ k, by
      rw [Cat.assoc, hk, image.lift_fac]⟩
  obtain ⟨act'', hact''⟩ := hclaim
  -- ── Characteristic map `e : α.obj → Two`:  `A'` ↦ inl, `A''` ↦ inr.
  let Two : 𝒞 := coprodObj one one
  let inlT : (one : 𝒞) ⟶ Two := coprodInl one one
  let inrT : (one : 𝒞) ⟶ Two := coprodInr one one
  let e : α.obj ⟶ Two :=
    ψinv ≫ HasBinaryCoproducts.case (term A'.dom ≫ inlT) (term A''.dom ≫ inrT)
  have heA' : A'.arr ≫ e = term A'.dom ≫ inlT := by
    show A'.arr ≫ ψinv ≫ _ = _
    rw [← hψinl, Cat.assoc, ← Cat.assoc ψ ψinv, hψ1, Cat.id_comp,
        HasBinaryCoproducts.case_inl]
  have heA'' : A''.arr ≫ e = term A''.dom ≫ inrT := by
    show A''.arr ≫ ψinv ≫ _ = _
    rw [← hψinr, Cat.assoc, ← Cat.assoc ψ ψinv, hψ1, Cat.id_comp,
        HasBinaryCoproducts.case_inr]
  -- ── `act ≫ e = snd ≫ e` (act-invariance of `e`).  Both maps `prod A α.obj → Two`; precompose
  -- the iso `prodMap A (A'+A'') α.obj ψ` (epi) and check on the two distributed summands.
  have hte : α.act ≫ e = snd (A := A) (B := α.obj) ≫ e := by
    -- restriction of `act` to `prod A A'.dom` lands in `A'` (act-stable): `wA' ≫ A'.arr = prodMap..≫act`.
    obtain ⟨rA', hrA'⟩ := hA'act
    let wA' : prod A A'.dom ⟶ A'.dom :=
      image.lift (prodMap A A'.dom α.obj A'.arr ≫ α.act) ≫ rA'
    have hwA' : wA' ≫ A'.arr = prodMap A A'.dom α.obj A'.arr ≫ α.act := by
      show (image.lift _ ≫ rA') ≫ A'.arr = _
      rw [Cat.assoc, hrA', image.lift_fac]
    -- the iso `Ψ := prodMap A (A'.dom+A''.dom) α.obj ψ` is split epi (retraction `prodMap.. ψinv`).
    let Ψ : prod A (HasBinaryCoproducts.coprod A'.dom A''.dom) ⟶ prod A α.obj :=
      prodMap A (HasBinaryCoproducts.coprod A'.dom A''.dom) α.obj ψ
    have hΨepi : ∀ {Z : 𝒞} (p q : prod A α.obj ⟶ Z), Ψ ≫ p = Ψ ≫ q → p = q := by
      intro Z p q h
      have hsec : prodMap A α.obj (HasBinaryCoproducts.coprod A'.dom A''.dom) ψinv ≫ Ψ
          = Cat.id (prod A α.obj) := by
        show _ ≫ prodMap A _ α.obj ψ = _
        rw [← prodMap_comp, hψ2, prodMap_id]
      have := congrArg (prodMap A α.obj (HasBinaryCoproducts.coprod A'.dom A''.dom) ψinv ≫ ·) h
      simpa only [← Cat.assoc, hsec, Cat.id_comp] using this
    apply hΨepi
    -- `distInl`/`distInr` are jointly epi (`distCase_uniq`): suffices both legs agree.
    have hjoint : ∀ {Z : 𝒞} (X Y : prod A (HasBinaryCoproducts.coprod A'.dom A''.dom) ⟶ Z),
        distInl A A'.dom A''.dom ≫ X = distInl A A'.dom A''.dom ≫ Y →
        distInr A A'.dom A''.dom ≫ X = distInr A A'.dom A''.dom ≫ Y → X = Y := by
      intro Z X Y hl hr
      rw [distCase_uniq (distInl A A'.dom A''.dom ≫ X) (distInr A A'.dom A''.dom ≫ X) X rfl rfl,
          distCase_uniq (distInl A A'.dom A''.dom ≫ X) (distInr A A'.dom A''.dom ≫ X) Y
            hl.symm hr.symm]
    apply hjoint
    · -- inl-leg.  `distInl ≫ Ψ = prodMap A A'.dom α.obj A'.arr` (since `inl ≫ ψ = A'.arr`).
      have hΨl : distInl A A'.dom A''.dom ≫ Ψ = prodMap A A'.dom α.obj A'.arr := by
        show prodMap A A'.dom _ HasBinaryCoproducts.inl ≫ prodMap A _ α.obj ψ = _
        rw [← prodMap_comp, hψinl]
      calc distInl A A'.dom A''.dom ≫ (Ψ ≫ (α.act ≫ e))
          = (distInl A A'.dom A''.dom ≫ Ψ) ≫ α.act ≫ e := (Cat.assoc _ _ _).symm
        _ = prodMap A A'.dom α.obj A'.arr ≫ α.act ≫ e := by rw [hΨl]
        _ = (prodMap A A'.dom α.obj A'.arr ≫ α.act) ≫ e := (Cat.assoc _ _ _).symm
        _ = (wA' ≫ A'.arr) ≫ e := by rw [hwA']
        _ = wA' ≫ (A'.arr ≫ e) := Cat.assoc _ _ _
        _ = wA' ≫ (term A'.dom ≫ inlT) := by rw [heA']
        _ = (wA' ≫ term A'.dom) ≫ inlT := (Cat.assoc _ _ _).symm
        _ = term (prod A A'.dom) ≫ inlT := by rw [term_uniq (wA' ≫ term A'.dom) (term _)]
        _ = (snd ≫ term A'.dom) ≫ inlT := by rw [term_uniq (snd ≫ term A'.dom) (term _)]
        _ = snd ≫ (A'.arr ≫ e) := by rw [Cat.assoc, ← heA']
        _ = (snd ≫ A'.arr) ≫ e := (Cat.assoc _ _ _).symm
        _ = (prodMap A A'.dom α.obj A'.arr ≫ snd) ≫ e := by rw [prodMap_snd]
        _ = (distInl A A'.dom A''.dom ≫ Ψ) ≫ snd ≫ e := by rw [hΨl, Cat.assoc]
        _ = distInl A A'.dom A''.dom ≫ (Ψ ≫ (snd ≫ e)) := Cat.assoc _ _ _
    · -- inr-leg.  `distInr ≫ Ψ = prodMap A A''.dom α.obj A''.arr` (since `inr ≫ ψ = A''.arr`).
      have hΨr : distInr A A'.dom A''.dom ≫ Ψ = prodMap A A''.dom α.obj A''.arr := by
        show prodMap A A''.dom _ HasBinaryCoproducts.inr ≫ prodMap A _ α.obj ψ = _
        rw [← prodMap_comp, hψinr]
      calc distInr A A'.dom A''.dom ≫ (Ψ ≫ (α.act ≫ e))
          = (distInr A A'.dom A''.dom ≫ Ψ) ≫ α.act ≫ e := (Cat.assoc _ _ _).symm
        _ = prodMap A A''.dom α.obj A''.arr ≫ α.act ≫ e := by rw [hΨr]
        _ = (prodMap A A''.dom α.obj A''.arr ≫ α.act) ≫ e := (Cat.assoc _ _ _).symm
        _ = (act'' ≫ A''.arr) ≫ e := by rw [hact'']
        _ = act'' ≫ (A''.arr ≫ e) := Cat.assoc _ _ _
        _ = act'' ≫ (term A''.dom ≫ inrT) := by rw [heA'']
        _ = (act'' ≫ term A''.dom) ≫ inrT := (Cat.assoc _ _ _).symm
        _ = term (prod A A''.dom) ≫ inrT := by rw [term_uniq (act'' ≫ term A''.dom) (term _)]
        _ = (snd ≫ term A''.dom) ≫ inrT := by rw [term_uniq (snd ≫ term A''.dom) (term _)]
        _ = snd ≫ (A''.arr ≫ e) := by rw [Cat.assoc, ← heA'']
        _ = (snd ≫ A''.arr) ≫ e := (Cat.assoc _ _ _).symm
        _ = (prodMap A A''.dom α.obj A''.arr ≫ snd) ≫ e := by rw [prodMap_snd]
        _ = (distInr A A'.dom A''.dom ≫ Ψ) ≫ snd ≫ e := by rw [hΨr, Cat.assoc]
        _ = distInr A A'.dom A''.dom ≫ (Ψ ≫ (snd ≫ e)) := Cat.assoc _ _ _
  -- ── Coequalizer: `e` factors `e = term α.obj ≫ g` for a unique `g : 1 → Two`.
  obtain ⟨g, hg, _hguniq⟩ := hcoeq Two e hte
  -- `g = inlT` (the `A'`-value), because `A'` allows `unit`.
  have hg_inl : g = inlT := by
    have htid : term (one : 𝒞) = Cat.id one := term_uniq _ _
    have h1 : α.unit ≫ e = inlT := by
      rw [← ha₀, Cat.assoc, heA', ← Cat.assoc,
          term_uniq (a₀ ≫ term A'.dom) (term one), htid, Cat.id_comp]
    have h2 : α.unit ≫ e = g := by
      rw [← hg, ← Cat.assoc, term_uniq (α.unit ≫ term α.obj) (term one), htid, Cat.id_comp]
    rw [← h2, h1]
  -- ── `A''.dom` initial:  `A''.arr ≫ e = term ≫ inrT = term ≫ g = term ≫ inlT`.
  have hcommon : term A''.dom ≫ inlT = term A''.dom ≫ inrT := by
    have hgInr : A''.arr ≫ e = term A''.dom ≫ g := by
      rw [← hg, ← Cat.assoc, term_uniq (A''.arr ≫ term α.obj) (term A''.dom)]
    rw [hg_inl] at hgInr
    rw [← hgInr, heA'']
  have hcommon' : term A''.dom ≫ coprodInl (one : 𝒞) one
      = term A''.dom ≫ coprodInr (one : 𝒞) one := hcommon
  have hAinit : ∀ {Y : 𝒞} (u v : A''.dom ⟶ Y), u = v :=
    coprodInjections_disjoint_elt (term A''.dom) (term A''.dom) hcommon'
  -- ── `A''.dom` initial ⟹ `inl : A'.dom → A'.dom+A''.dom` iso ⟹ `A'.arr = inl ≫ ψ` iso.
  show IsIso A'.arr
  have hinl_iso : IsIso (HasBinaryCoproducts.inl (A := A'.dom) (B := A''.dom)) := by
    refine ⟨HasBinaryCoproducts.case (Cat.id A'.dom) (term A''.dom ≫ a₀), ?_, ?_⟩
    · exact HasBinaryCoproducts.case_inl _ _
    · -- `case id k ≫ inl = id`: both sides `case inl inr` (the coproduct identity).
      have hid : Cat.id (HasBinaryCoproducts.coprod A'.dom A''.dom)
          = HasBinaryCoproducts.case HasBinaryCoproducts.inl HasBinaryCoproducts.inr :=
        HasBinaryCoproducts.case_uniq _ _ _ (Cat.comp_id _) (Cat.comp_id _)
      rw [hid]
      apply HasBinaryCoproducts.case_uniq
      · rw [← Cat.assoc, HasBinaryCoproducts.case_inl, Cat.id_comp]
      · rw [← Cat.assoc]; exact hAinit _ _
  rw [← hψinl]; exact isIso_comp hinl_iso ⟨ψinv, hψ1, hψ2⟩

/-- **§1.98(13) action PEANO PROPERTY** (boolean) — `free_peano_property_of_bicartesian`
    packaged with the same argument bundle the equalizer chases use. -/
theorem free_peano_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
    (hbool : BooleanSub 𝒞)
    (A : 𝒞) (α : AAction (𝒞 := 𝒞) A)
    (hiso : IsIso (HasBinaryCoproducts.case α.unit α.act
                   (A := one) (B := prod A α.obj) (X := α.obj)))
    (hcoeq : ∀ (X : 𝒞) (f : α.obj ⟶ X),
               α.act ≫ f = snd (A := A) (B := α.obj) ≫ f →
               ∃ g : one ⟶ X, term α.obj ≫ g = f ∧
                 ∀ g' : one ⟶ X, term α.obj ≫ g' = f → g' = g)
    (B : Subobject 𝒞 α.obj)
    (huB : ∃ uB : one ⟶ B.dom, uB ≫ B.arr = α.unit)
    (hactB : ∃ actB : prod A B.dom ⟶ B.dom,
        actB ≫ B.arr = prodMap A B.dom α.obj B.arr ≫ α.act) :
    B.IsEntire :=
  free_peano_property_of_bicartesian hbool A α hiso hcoeq B huB hactB

/-- **§1.98(13) free-recursor UNIQUENESS** (via the equalizer + action Peano).
    Any two free homomorphisms `h, h' : α.obj → β.obj` are equal: their equalizer
    `E ↣ α.obj` is `(unit,act)`-closed, hence entire by `free_peano_of_bicartesian`,
    so the equalizer map is iso and left-cancels `h = h'`. -/
theorem free_recursor_unique_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
    (hbool : BooleanSub 𝒞)
    (A : 𝒞) (α : AAction (𝒞 := 𝒞) A)
    (hiso : IsIso (HasBinaryCoproducts.case α.unit α.act
                   (A := one) (B := prod A α.obj) (X := α.obj)))
    (hcoeq : ∀ (X : 𝒞) (f : α.obj ⟶ X),
               α.act ≫ f = snd (A := A) (B := α.obj) ≫ f →
               ∃ g : one ⟶ X, term α.obj ≫ g = f ∧
                 ∀ g' : one ⟶ X, term α.obj ≫ g' = f → g' = g)
    (β : AAction (𝒞 := 𝒞) A) (h h' : α.obj ⟶ β.obj)
    (h0 : α.unit ≫ h = β.unit) (hs : prodMap A α.obj β.obj h ≫ β.act = α.act ≫ h)
    (h0' : α.unit ≫ h' = β.unit) (hs' : prodMap A α.obj β.obj h' ≫ β.act = α.act ≫ h') :
    h = h' := by
  -- Equalizer subobject E = eq(h, h') ↣ α.obj.
  let m : eqObj h h' ⟶ α.obj := eqMap h h'
  have hm_eq : m ≫ h = m ≫ h' := eqMap_eq h h'
  have hm_mono : Monic m := by
    intro W u v huv
    have hu : u = eqLift h h' (u ≫ m) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) :=
      eqLift_uniq h h' (u ≫ m) _ u rfl
    have hv : v = eqLift h h' (u ≫ m) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) :=
      eqLift_uniq h h' (u ≫ m) _ v huv.symm
    rw [hu, hv]
  let E : Subobject 𝒞 α.obj := ⟨eqObj h h', m, hm_mono⟩
  -- E allows unit: `unit ≫ h = β.unit = unit ≫ h'`, so `unit` lifts to E.
  have hEu : ∃ uB : one ⟶ E.dom, uB ≫ E.arr = α.unit :=
    ⟨eqLift h h' α.unit (by rw [h0, h0']), eqLift_fac h h' α.unit (by rw [h0, h0'])⟩
  -- E is act-stable: `prodMap A E.dom α.obj m ≫ act` equalizes h, h'.
  --   (prodMap A E.dom α.obj m ≫ act) ≫ h = prodMap A E.dom α.obj m ≫ (act ≫ h)
  --     = prodMap A E.dom α.obj m ≫ (prodMap A α.obj β.obj h ≫ β.act)
  --     = prodMap A E.dom β.obj (m ≫ h) ≫ β.act   [prodMap functorial]
  --     = prodMap A E.dom β.obj (m ≫ h') ≫ β.act  [hm_eq]  = … = (…) ≫ h'.
  have hmact_eq : (prodMap A E.dom α.obj m ≫ α.act) ≫ h
                = (prodMap A E.dom α.obj m ≫ α.act) ≫ h' := by
    calc (prodMap A E.dom α.obj m ≫ α.act) ≫ h
        = prodMap A E.dom α.obj m ≫ (prodMap A α.obj β.obj h ≫ β.act) := by
            rw [Cat.assoc, hs]
      _ = prodMap A E.dom β.obj (m ≫ h) ≫ β.act := by rw [← Cat.assoc, ← prodMap_comp]
      _ = prodMap A E.dom β.obj (m ≫ h') ≫ β.act := by rw [hm_eq]
      _ = prodMap A E.dom α.obj m ≫ (prodMap A α.obj β.obj h' ≫ β.act) := by
            rw [prodMap_comp, Cat.assoc]
      _ = (prodMap A E.dom α.obj m ≫ α.act) ≫ h' := by rw [hs', Cat.assoc]
  have hEact : ∃ actB : prod A E.dom ⟶ E.dom,
      actB ≫ E.arr = prodMap A E.dom α.obj E.arr ≫ α.act :=
    ⟨eqLift h h' (prodMap A E.dom α.obj m ≫ α.act) hmact_eq,
     eqLift_fac h h' (prodMap A E.dom α.obj m ≫ α.act) hmact_eq⟩
  -- E entire by the action Peano property; the equalizer map is iso ⇒ h = h'.
  have hEent : E.IsEntire := free_peano_of_bicartesian hbool A α hiso hcoeq E hEu hEact
  obtain ⟨m', _, hm'm⟩ := hEent
  calc h = Cat.id α.obj ≫ h := (Cat.id_comp _).symm
    _ = (m' ≫ m) ≫ h := by rw [hm'm]
    _ = m' ≫ m ≫ h := Cat.assoc _ _ _
    _ = m' ≫ m ≫ h' := by rw [hm_eq]
    _ = (m' ≫ m) ≫ h' := (Cat.assoc _ _ _).symm
    _ = Cat.id α.obj ≫ h' := by rw [hm'm]
    _ = h' := Cat.id_comp _

/-- **§1.98(13) FREE RECURSOR EXISTENCE — the single residual of §1.98(13).**

    The A-action analogue of `recursor_exists_of_bicartesian`, FAITHFULLY in a BOOLEAN
    topos (`hbool`).  From bicartesian data `[unit,act] : 1 + A×α.obj ≅ α.obj` (and the
    terminal coequalizer `hcoeq`), §1.988 produces, for every A-action `β`, a free
    homomorphism `h : α.obj → β.obj` with `α.unit ≫ h = β.unit` and
    `prodMap A α.obj β.obj h ≫ β.act = α.act ≫ h`.  We bundle the `α.obj → α.obj`-instance
    UNIQUENESS (proved here from the free Peano property via the free equalizer at `β := α`);
    EXISTENCE is the SAME mechanical functional-graph residual as the NNO recursor. -/
theorem free_recursor_exists_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞]
    (hbool : BooleanSub 𝒞) (hcap : Capital (𝒞 := 𝒞)) (htv : TwoValued (𝒞 := 𝒞))
    (A : 𝒞) (α : AAction (𝒞 := 𝒞) A)
    (hiso : IsIso (HasBinaryCoproducts.case α.unit α.act
                   (A := one) (B := prod A α.obj) (X := α.obj)))
    (hcoeq : ∀ (X : 𝒞) (f : α.obj ⟶ X),
               α.act ≫ f = snd (A := A) (B := α.obj) ≫ f →
               ∃ g : one ⟶ X, term α.obj ≫ g = f ∧
                 ∀ g' : one ⟶ X, term α.obj ≫ g' = f → g' = g) :
    (∀ (β : AAction (𝒞 := 𝒞) A),
        ∃ h : α.obj ⟶ β.obj,
          α.unit ≫ h = β.unit ∧ prodMap A α.obj β.obj h ≫ β.act = α.act ≫ h) ∧
      (∀ e : α.obj ⟶ α.obj, α.unit ≫ e = α.unit →
          prodMap A α.obj α.obj e ≫ α.act = α.act ≫ e → e = Cat.id α.obj) := by
  -- §1.98(13) free recursor in a BOOLEAN + CAPITAL topos.  The free action PEANO PROPERTY
  -- (`free_peano_property_of_bicartesian`) is Freyd's §1.988 complement argument for the
  -- A-parametrised functor `1 + A×(−)`; from it:
  --   UNIQUENESS — the free equalizer of an endo-free-homomorphism `e` is `(unit,act)`-closed,
  --     hence entire by the free Peano property, forcing `e = id` (free-equalizer chase at `β:=α`).
  --   EXISTENCE — functional-graph extraction from the free Peano property (the SAME mechanical
  --     residual as the NNO `recursor_exists_of_bicartesian` existence conjunct).
  refine ⟨?_, ?_⟩
  · -- EXISTENCE residual: the A-parametrised §1.988 recursion theorem (graph trick), FAITHFULLY in
    -- a BOOLEAN + CAPITAL topos (Freyd's §1.98(13) is "analogous to §1.98(10)").  Mirror of
    -- `recursor_exists_of_bicartesian`'s existence half: for an A-action `β`, build the functional
    -- graph `G ↣ prod α.obj β.obj` as the least `(pair unit β.unit, S, snd)`-closed subobject for
    -- the parametrised "successor" `S` acting by `act` on the α-leg and `β.act` on the β-leg; its
    -- α-projection is TOTAL by the free Peano property (`free_peano_of_bicartesian`) and
    -- SINGLE-VALUED by §1.989 (`pts_covers_of_capital hcap` + `coprod_point_split` + disjointness),
    -- giving `h := proj⁻¹ ≫ G.arr ≫ snd`.
    --
    -- STATUS: the PARAMETRISED least-closed primitive is BUILT Sorry-free (`Freyd.actLeast` +
    -- `actLeast_allows`/`actLeast_stable`/`actLeast_le`), the free-Peano property is now CLOSED
    -- (`free_peano_of_bicartesian`), and the act-image calculus (`image_act_mono`/`actStable_of_restrict`)
    -- is in scope.  We build the functional graph and prove TOTALITY here Sorry-free; the SINGLE
    -- residual is the §1.989 single-valuedness (`Monic p`), re-indexed over the keystone cover
    -- `1 + prod A G.dom ↠ G.dom` (the A-parametrised analogue of the NNO `hpmono`).
    classical
    intro β
    -- The graph `G ↣ prod α.obj β.obj` := least `(⟨unit, β.unit⟩, Sgraph, snd)`-closed subobject.
    -- `Sgraph (a, (x,y)) = (act(a,x), β.act(a,y))` — the action on both legs simultaneously.
    let actOnFst : prod A (prod α.obj β.obj) ⟶ α.obj :=
      pair fst (snd ≫ fst) ≫ α.act
    let actOnSnd : prod A (prod α.obj β.obj) ⟶ β.obj :=
      pair fst (snd ≫ snd) ≫ β.act
    let Sgraph : prod A (prod α.obj β.obj) ⟶ prod α.obj β.obj := pair actOnFst actOnSnd
    let unitPt : one ⟶ prod α.obj β.obj := pair α.unit β.unit
    let G : Subobject 𝒞 (prod α.obj β.obj) :=
      actLeast unitPt Sgraph (snd (A := A) (B := prod α.obj β.obj))
    -- closure of `G`: allows `unitPt`, and act-stable.
    obtain ⟨g₀, hg₀⟩ := actLeast_allows unitPt Sgraph (snd (A := A) (B := prod α.obj β.obj))
    -- the act-restriction `actG : prod A G.dom → G.dom` from `actLeast_stable` (image form).
    have hGact : (image (prodMap A G.dom (prod α.obj β.obj) G.arr ≫ Sgraph)).le G :=
      actImg_le_of_actStable Sgraph G
        (actLeast_stable unitPt Sgraph (snd (A := A) (B := prod α.obj β.obj)))
    obtain ⟨rG, hrG⟩ := hGact
    let actG : prod A G.dom ⟶ G.dom :=
      image.lift (prodMap A G.dom (prod α.obj β.obj) G.arr ≫ Sgraph) ≫ rG
    have hactG : actG ≫ G.arr = prodMap A G.dom (prod α.obj β.obj) G.arr ≫ Sgraph := by
      show (image.lift _ ≫ rG) ≫ G.arr = _
      rw [Cat.assoc, hrG, image.lift_fac]
    let p : G.dom ⟶ α.obj := G.arr ≫ fst
    -- the α-leg law: `prodMap A G.dom α.obj p ≫ α.act = actG ≫ p`.
    have hSgFst : Sgraph ≫ fst = pair fst (snd ≫ fst) ≫ α.act := fst_pair _ _
    have hpt : prodMap A G.dom α.obj p ≫ α.act = actG ≫ p := by
      -- RHS: `actG ≫ p = prodMap.. G.arr ≫ (Sgraph ≫ fst) = prodMap.. G.arr ≫ pair fst (snd≫fst) ≫ act`.
      have hR : actG ≫ p
          = prodMap A G.dom (prod α.obj β.obj) G.arr ≫ (pair fst (snd ≫ fst) ≫ α.act) := by
        show actG ≫ G.arr ≫ fst = _
        rw [← Cat.assoc, hactG, Cat.assoc, hSgFst]
      -- LHS: `prodMap A G.dom α.obj (G.arr≫fst) = prodMap.. G.arr ≫ prodMap (prod α β) α fst`,
      -- and `prodMap A (prod α β) α fst = pair fst (snd≫fst)`.
      have hpm : prodMap A (prod α.obj β.obj) α.obj fst = pair fst (snd ≫ fst) := rfl
      rw [hR]
      show prodMap A G.dom α.obj (G.arr ≫ fst) ≫ α.act = _
      rw [prodMap_comp, hpm, Cat.assoc]
    -- TOTALITY: `image p` is `(unit,act)`-closed (`p`-fiber of `unit` via `g₀`; act-stable via `hpt`),
    -- hence entire by the free Peano property, so `p` is a cover.
    have hpcover : Cover p := by
      have hImgU : ∃ uB : one ⟶ (image p).dom, uB ≫ (image p).arr = α.unit := by
        refine ⟨g₀ ≫ image.lift p, ?_⟩
        rw [Cat.assoc, image.lift_fac]
        show g₀ ≫ G.arr ≫ fst = α.unit
        rw [← Cat.assoc, hg₀]; exact fst_pair _ _
      have hImgAct : ∃ actB : prod A (image p).dom ⟶ (image p).dom,
          actB ≫ (image p).arr
            = prodMap A (image p).dom α.obj (image p).arr ≫ α.act := by
        -- `act(image p) ≤ act(p) ≤ image p` (`image_act_mono` + `hpt` + descend via the graph).
        have hcov : Cover (image.lift p) := image_lift_cover p
        -- `image(prodMap A (image p).dom α.obj (image p).arr ≫ act) ≤ image(prodMap A G.dom α.obj p ≫ act)`.
        have hle1 : (image (prodMap A (image p).dom α.obj (image p).arr ≫ α.act)).le
            (image (prodMap A G.dom α.obj p ≫ α.act)) := by
          -- `prodMap A G.dom (image p).dom (image.lift p)` is a cover (`prodMap_cover`); precomposing
          -- it onto `prodMap A (image p).dom α.obj (image p).arr ≫ act` gives `prodMap.. p ≫ act`.
          have hcov' : Cover (prodMap A G.dom (image p).dom (image.lift p)) :=
            prodMap_cover A (image_lift_cover p)
          have hcomp : prodMap A G.dom (image p).dom (image.lift p)
              ≫ (prodMap A (image p).dom α.obj (image p).arr ≫ α.act)
              = prodMap A G.dom α.obj p ≫ α.act := by
            rw [← Cat.assoc, ← prodMap_comp, image.lift_fac]
          have := (image_cover_comp (prodMap A G.dom (image p).dom (image.lift p))
            (prodMap A (image p).dom α.obj (image p).arr ≫ α.act) hcov').2
          rwa [hcomp] at this
        -- `image(prodMap A G.dom α.obj p ≫ act) = image(actG ≫ p) ≤ image p` (`hpt`, then `actG` factor).
        have hle2 : (image (prodMap A G.dom α.obj p ≫ α.act)).le (image p) := by
          rw [hpt]
          exact image_min (actG ≫ p) (image p)
            ⟨actG ≫ image.lift p, by rw [Cat.assoc, image.lift_fac]⟩
        obtain ⟨k, hk⟩ := subLe_trans' hle1 hle2
        exact ⟨image.lift (prodMap A (image p).dom α.obj (image p).arr ≫ α.act) ≫ k, by
          rw [Cat.assoc, hk, image.lift_fac]⟩
      have hEnt : (image p).IsEntire :=
        free_peano_of_bicartesian hbool A α hiso hcoeq (image p) hImgU hImgAct
      have hc : Cover (image.lift p ≫ (image p).arr) :=
        cover_comp (image_lift_cover p) (iso_cover (image p).arr hEnt)
      rwa [image.lift_fac] at hc
    -- SINGLE-VALUEDNESS (§1.989): `p` MONIC.  Re-indexed over the keystone cover
    -- `cg = [g₀, actG] : 1 + prod A G.dom ↠ G.dom` (the A-parametrised graph algebra structure
    -- map).  The kernel-pair / off-diagonal-complement assembly is verbatim the NNO `hpmono`
    -- EXCEPT the keystone reachability now tracks the A-parameter: a preimage of `S(a,−)` is an
    -- `actG`-image of a preimage, where the `inr`-point of `1 + prod A G.dom` carries the A-leg.
    -- KEYSTONE (§1.989 graph reachability, A-parametrised): the structure map
    -- `cg := [g₀, actG] : 1 + prod A G.dom → G.dom` of the graph algebra `G` is a COVER.
    -- `R' := image (cg ≫ G.arr) ⊆ prod α.obj β.obj` is `(unitPt, Sgraph, snd)`-act-closed
    -- (allows `unitPt` via `inl`; act-stable via `prodMap.. cg ≫ actG = (prodMap.. cg ≫ inr) ≫ cg`,
    -- landing back in `image (cg ≫ G.arr)`), so `G ≤ R'` (`actLeast_le`) and `R' ≤ G` (`image_min`),
    -- forcing `image cg` entire.
    let cg : HasBinaryCoproducts.coprod (one : 𝒞) (prod A G.dom) ⟶ G.dom :=
      HasBinaryCoproducts.case g₀ actG
    have hcg : Cover cg := by
      let cgG : HasBinaryCoproducts.coprod (one : 𝒞) (prod A G.dom) ⟶ prod α.obj β.obj :=
        cg ≫ G.arr
      let R' : Subobject 𝒞 (prod α.obj β.obj) := image cgG
      -- `R'` is `(unitPt, Sgraph, snd)`-act-closed.
      have hR'G : R'.le G := image_min cgG G ⟨cg, rfl⟩
      have hGR' : G.le R' := by
        refine actLeast_le unitPt Sgraph (snd (A := A) (B := prod α.obj β.obj)) R' ?_ ?_
        · -- allows `unitPt`: `(inl ≫ image.lift cgG) ≫ R'.arr = inl ≫ cg ≫ G.arr = g₀ ≫ G.arr = unitPt`.
          refine ⟨HasBinaryCoproducts.inl ≫ image.lift cgG, ?_⟩
          show (HasBinaryCoproducts.inl ≫ image.lift cgG) ≫ (image cgG).arr = unitPt
          rw [Cat.assoc, image.lift_fac]
          show HasBinaryCoproducts.inl ≫ cg ≫ G.arr = unitPt
          rw [← Cat.assoc, HasBinaryCoproducts.case_inl, hg₀]
        · -- act-stable: `(snd # R') ≤ (Sgraph # R')` via a restriction `actR' : prod A R'.dom → R'.dom`.
          -- `act(R') ≤ act-image ≤ R'`: build `actR'` from the descent below, then `actStable_of_restrict`.
          have himg_le : (image (prodMap A R'.dom (prod α.obj β.obj) R'.arr ≫ Sgraph)).le R' := by
            -- cover `prodMap.. (image.lift cgG)`; precompose to get `prodMap.. cgG ≫ Sgraph`.
            have hcov' : Cover (prodMap A (HasBinaryCoproducts.coprod (one : 𝒞) (prod A G.dom))
                R'.dom (image.lift cgG)) := prodMap_cover A (image_lift_cover cgG)
            have hcomp : prodMap A (HasBinaryCoproducts.coprod (one : 𝒞) (prod A G.dom)) R'.dom
                  (image.lift cgG) ≫ (prodMap A R'.dom (prod α.obj β.obj) R'.arr ≫ Sgraph)
                = prodMap A (HasBinaryCoproducts.coprod (one : 𝒞) (prod A G.dom))
                    (prod α.obj β.obj) cgG ≫ Sgraph := by
              rw [← Cat.assoc, ← prodMap_comp, image.lift_fac]
            have hle1 : (image (prodMap A R'.dom (prod α.obj β.obj) R'.arr ≫ Sgraph)).le
                (image (prodMap A (HasBinaryCoproducts.coprod (one : 𝒞) (prod A G.dom))
                    (prod α.obj β.obj) cgG ≫ Sgraph)) := by
              have := (image_cover_comp (prodMap A (HasBinaryCoproducts.coprod (one : 𝒞)
                (prod A G.dom)) R'.dom (image.lift cgG))
                (prodMap A R'.dom (prod α.obj β.obj) R'.arr ≫ Sgraph) hcov').2
              rwa [hcomp] at this
            -- `prodMap.. cgG ≫ Sgraph = (prodMap.. cg ≫ inr) ≫ (cg ≫ G.arr)`, so ≤ R'.
            have hfact : prodMap A (HasBinaryCoproducts.coprod (one : 𝒞) (prod A G.dom))
                  (prod α.obj β.obj) cgG ≫ Sgraph
                = (prodMap A (HasBinaryCoproducts.coprod (one : 𝒞) (prod A G.dom)) G.dom cg
                    ≫ HasBinaryCoproducts.inr) ≫ cgG := by
              show prodMap A _ (prod α.obj β.obj) (cg ≫ G.arr) ≫ Sgraph
                = (prodMap A _ G.dom cg ≫ HasBinaryCoproducts.inr) ≫ (cg ≫ G.arr)
              calc prodMap A _ (prod α.obj β.obj) (cg ≫ G.arr) ≫ Sgraph
                  = (prodMap A _ G.dom cg ≫ prodMap A G.dom (prod α.obj β.obj) G.arr) ≫ Sgraph := by
                    rw [prodMap_comp]
                _ = prodMap A _ G.dom cg
                      ≫ (prodMap A G.dom (prod α.obj β.obj) G.arr ≫ Sgraph) := Cat.assoc _ _ _
                _ = prodMap A _ G.dom cg ≫ (actG ≫ G.arr) := by rw [hactG]
                _ = prodMap A _ G.dom cg ≫ ((HasBinaryCoproducts.inr ≫ cg) ≫ G.arr) := by
                    rw [HasBinaryCoproducts.case_inr]
                _ = (prodMap A _ G.dom cg ≫ HasBinaryCoproducts.inr) ≫ (cg ≫ G.arr) := by
                    rw [Cat.assoc, Cat.assoc]
            have hle2 : (image (prodMap A (HasBinaryCoproducts.coprod (one : 𝒞) (prod A G.dom))
                (prod α.obj β.obj) cgG ≫ Sgraph)).le R' :=
              image_min _ R' ⟨(prodMap A (HasBinaryCoproducts.coprod (one : 𝒞) (prod A G.dom)) G.dom cg
                  ≫ HasBinaryCoproducts.inr) ≫ image.lift cgG, by
                rw [Cat.assoc, image.lift_fac, hfact]⟩
            exact subLe_trans' hle1 hle2
          obtain ⟨k, hk⟩ := himg_le
          exact actStable_of_restrict Sgraph R'
            (image.lift (prodMap A R'.dom (prod α.obj β.obj) R'.arr ≫ Sgraph) ≫ k)
            (by rw [Cat.assoc, hk, image.lift_fac])
      -- mutual `≤` ⟹ `cg` cover (cover ∘ iso through the image factor).
      obtain ⟨c, hc⟩ := hR'G
      have hciso : IsIso c := by
        obtain ⟨d, hd⟩ := hGR'
        refine ⟨d, ?_, ?_⟩
        · exact R'.monic (c ≫ d) (Cat.id _) (by rw [Cat.assoc, hd, hc, Cat.id_comp])
        · exact G.monic (d ≫ c) (Cat.id _) (by rw [Cat.assoc, hc, hd, Cat.id_comp])
      have hcgeq : image.lift cgG ≫ c = cg :=
        G.monic _ _ (by rw [Cat.assoc, hc, image.lift_fac])
      have hcc : Cover (image.lift cgG ≫ c) :=
        cover_comp (image_lift_cover cgG) (iso_cover c hciso)
      rwa [hcgeq] at hcc
    -- RESIDUAL (the SINGLE remaining hole of §1.98(13)): this `prod A G.dom`-keystone single-valuedness.
    have hpmono : Monic p := by
      -- §1.989 single-valuedness (Freyd p.186), A-parametrised.  `K := kernelPair p`, diagonal
      -- `Δ := image kp_diag`; boolean complement `K'` of `Δ`; `A₁ := image(K'.arr ≫ kp₁ ≫ p)` its
      -- α.obj-image; `A₂ := complement`.  `A₂` is `(unit,act)`-closed (free fiber-singleton via the
      -- keystone cover `cg`), so ENTIRE by `free_peano_of_bicartesian` — forcing `A₁ ≤ ⊥`, `K' ≤ ⊥`,
      -- `Δ` entire, `kp_diag` cover; split mono ⟹ iso; `monic_iff_kp_diag_iso` gives `Monic p`.
      rw [monic_iff_kp_diag_iso]
      let Δ : Subobject 𝒞 (kernelPair p) := image (kp_diag (f := p))
      obtain ⟨K', hΔdisj, hΔunion⟩ := hbool Δ
      let q : K'.dom ⟶ α.obj := K'.arr ≫ kp₁ (f := p) ≫ p
      let A₁ : Subobject 𝒞 α.obj := image q
      obtain ⟨A₂, hA₁disj, hA₁union⟩ := hbool A₁
      have ha_mono : Monic α.unit := mono_from_one α.unit
      let aSub : Subobject 𝒞 α.obj := Subobject.mk one α.unit ha_mono
      -- `[unit, act] : 1 + prod A α.obj → α.obj` is iso, hence monic (non-destructive copy of `hiso`).
      have hcase_mono : Monic (HasBinaryCoproducts.case α.unit α.act
          (A := (one : 𝒞)) (B := prod A α.obj) (X := α.obj)) := by
        obtain ⟨caseInv, hcaseInv, _⟩ := id hiso
        exact mono_of_retraction _ caseInv hcaseInv
      -- A point of `K'` (the OFF-diagonal complement) whose two legs AGREE lies on `Δ`, absurd.
      have kpPointAbsurd : ∀ k : (one : 𝒞) ⟶ K'.dom,
          k ≫ K'.arr ≫ kp₁ (f := p) = k ≫ K'.arr ≫ kp₂ (f := p) → False := by
        intro k hlegs
        let v : (one : 𝒞) ⟶ G.dom := k ≫ K'.arr ≫ kp₁ (f := p)
        have hkdiag : k ≫ K'.arr = v ≫ kp_diag (f := p) := by
          have e₁ := kp_lift_uniq (f := p) v v rfl (k ≫ K'.arr)
            (by rw [Cat.assoc])
            (by rw [Cat.assoc]; exact hlegs.symm)
          have e₂ := kp_lift_uniq (f := p) v v rfl (v ≫ kp_diag (f := p))
            (by rw [Cat.assoc, kp_diag_p₁, Cat.comp_id])
            (by rw [Cat.assoc, kp_diag_p₂, Cat.comp_id])
          rw [e₁, e₂]
        let dΔ : (one : 𝒞) ⟶ Δ.dom := v ≫ image.lift (kp_diag (f := p))
        have hdΔ : dΔ ≫ Δ.arr = k ≫ K'.arr := by
          show (v ≫ image.lift (kp_diag (f := p))) ≫ (image (kp_diag (f := p))).arr = k ≫ K'.arr
          rw [Cat.assoc, image.lift_fac, hkdiag]
        let pt : Subobject 𝒞 (kernelPair p) :=
          Subobject.mk one (k ≫ K'.arr) (mono_from_one _)
        have hptΔ : pt.le Δ := ⟨dΔ, hdΔ⟩
        have hptK' : pt.le K' := ⟨k, rfl⟩
        have hptbot : pt.le (PreLogos.bottom (kernelPair p)) :=
          subLe_trans' (Subobject.le_inter hptΔ hptK') hΔdisj
        obtain ⟨m, _⟩ := hptbot
        exact point_bottom_absurd htv m
      -- FREE FIBER-SINGLETON: the `p`-fiber over `unit` is the singleton `{g₀}`.  `1` projective,
      -- so a point `z` lifts along the keystone cover `cg` to `w`; `coprod_point_split` makes `w`
      -- an `inl`-point (⟹ `z = g₀`) or an `inr`-point `w' : 1 → prod A G.dom` (⟹ `z = w' ≫ actG`,
      -- so `z ≫ p = (prodMap.. w' ≫ act-leg) ∈ image act`, contradicting `unit`-disjointness).
      have hfibSingle : ∀ z : (one : 𝒞) ⟶ G.dom, z ≫ p = α.unit → z = g₀ := by
        intro z hz
        obtain ⟨w, hw⟩ := pts_covers_of_capital hcap hcg z
        rcases coprod_point_split hcap htv w with ⟨u, hu⟩ | ⟨w', hw'⟩
        · -- `inl`: `z = u ≫ inl ≫ cg = u ≫ g₀ = g₀`.
          have hinlcg : HasBinaryCoproducts.inl (A := (one : 𝒞)) (B := prod A G.dom) ≫ cg = g₀ :=
            HasBinaryCoproducts.case_inl _ _
          calc z = w ≫ cg := hw.symm
            _ = (u ≫ HasBinaryCoproducts.inl) ≫ cg := by rw [hu]
            _ = u ≫ (HasBinaryCoproducts.inl ≫ cg) := Cat.assoc _ _ _
            _ = u ≫ g₀ := by rw [hinlcg]
            _ = g₀ := by rw [term_uniq u (Cat.id one), Cat.id_comp]
        · -- `inr`: `z = w' ≫ actG`; `unit = z≫p = (prodMap A 1 G.dom w' ≫ (prodMap.. p ≫ act))≫fst`
          -- collapses to `unit = (w'≫p-leg) ≫ act`, an `inr`-point of `[unit,act]` = `inl`-point — absurd.
          exfalso
          have hinrcg : HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := prod A G.dom) ≫ cg = actG :=
            HasBinaryCoproducts.case_inr _ _
          have hzact : z = w' ≫ actG := by
            calc z = w ≫ cg := hw.symm
              _ = (w' ≫ HasBinaryCoproducts.inr) ≫ cg := by rw [hw']
              _ = w' ≫ (HasBinaryCoproducts.inr ≫ cg) := Cat.assoc _ _ _
              _ = w' ≫ actG := by rw [hinrcg]
          -- `unit = z≫p = w'≫actG≫p = w'≫(prodMap.. p ≫ act)` (using `hpt`), a `t`-image of `prod A G.dom`.
          -- write the source point `s := prodMap A one G.dom w' ≫ pair fst snd`-form; pin its `act`-value.
          have hat : α.unit = (w' ≫ prodMap A G.dom α.obj p) ≫ α.act := by
            calc α.unit = z ≫ p := hz.symm
              _ = (w' ≫ actG) ≫ p := by rw [hzact]
              _ = w' ≫ (actG ≫ p) := Cat.assoc _ _ _
              _ = w' ≫ (prodMap A G.dom α.obj p ≫ α.act) := by rw [← hpt]
              _ = (w' ≫ prodMap A G.dom α.obj p) ≫ α.act := (Cat.assoc _ _ _).symm
          -- `unit` (`inl`-point) = `act`-value (`inr`-point): collapse injections of the iso `[unit,act]`.
          refine coprod_inj_disjoint_pt htv (Cat.id one) (w' ≫ prodMap A G.dom α.obj p) ?_
          apply hcase_mono
          rw [Cat.assoc, Cat.assoc, HasBinaryCoproducts.case_inl,
              HasBinaryCoproducts.case_inr, Cat.id_comp, ← hat]
      -- THE FIBER FACT: `A₁ ∩ {unit} ≤ ⊥`.  A point gives an off-diagonal kernel-pair point over
      -- `unit`, whose two legs are both `g₀` (`hfibSingle`), hence equal — `kpPointAbsurd`.
      have hfiber : (Subobject.inter A₁ aSub).le (PreLogos.bottom α.obj) := by
        refine noPoint_le_bottom hcap htv _ ?_
        rintro _ ⟨y, _⟩
        obtain ⟨kL, hkL⟩ := Subobject.inter_le_left A₁ aSub
        obtain ⟨kR, hkR⟩ := Subobject.inter_le_right A₁ aSub
        have hval : (y ≫ kL) ≫ A₁.arr = α.unit := by
          have heq : (y ≫ kR) ≫ aSub.arr = (y ≫ kL) ≫ A₁.arr := by
            rw [Cat.assoc, Cat.assoc, hkR, hkL]
          rw [← heq, term_uniq (y ≫ kR) (Cat.id one), Cat.id_comp]
        obtain ⟨k₀, hk₀⟩ := pts_covers_of_capital hcap (image_lift_cover q) (y ≫ kL)
        have hk₀q : k₀ ≫ q = α.unit := by
          have : k₀ ≫ q = (y ≫ kL) ≫ A₁.arr := by
            show k₀ ≫ K'.arr ≫ kp₁ (f := p) ≫ p = (y ≫ kL) ≫ (image q).arr
            rw [← hk₀, Cat.assoc, image.lift_fac]
          rw [this, hval]
        apply kpPointAbsurd k₀
        have hg₁ : (k₀ ≫ K'.arr ≫ kp₁ (f := p)) ≫ p = α.unit := by
          rw [Cat.assoc, Cat.assoc]; exact hk₀q
        have hg₂ : (k₀ ≫ K'.arr ≫ kp₂ (f := p)) ≫ p = α.unit := by
          calc (k₀ ≫ K'.arr ≫ kp₂ (f := p)) ≫ p
              = k₀ ≫ K'.arr ≫ (kp₂ (f := p) ≫ p) := by rw [Cat.assoc, Cat.assoc]
            _ = k₀ ≫ K'.arr ≫ (kp₁ (f := p) ≫ p) := by rw [← kp_sq]
            _ = (k₀ ≫ K'.arr ≫ kp₁ (f := p)) ≫ p := by rw [Cat.assoc, Cat.assoc]
            _ = α.unit := hg₁
        rw [hfibSingle _ hg₁, hfibSingle _ hg₂]
      -- `A₂` is `(unit,act)`-closed.  ALLOWS `unit` from `complement_le_other'`.
      have hA₂a : Allows A₂ α.unit := by
        obtain ⟨g, hg⟩ := complement_le_other' A₁ A₂ aSub hfiber hA₁union
        exact ⟨g, by simpa using hg⟩
      -- `act`-STABLE: `act(A₂) ≤ A₂` via `complement_le_other'` from `A₁ ∩ act(A₂) ≤ ⊥`.
      have hA₂t : ∃ tA₂ : prod A A₂.dom ⟶ A₂.dom,
          tA₂ ≫ A₂.arr = prodMap A A₂.dom α.obj A₂.arr ≫ α.act := by
        -- `act`-shifted free fiber-singleton: fiber over `act(a, b≫A₂.arr)` of a single-valued
        -- `b ∈ A₂` is again a singleton (keystone reachability propagated through `actG`).
        -- `act` is MONIC (`[unit,act]` iso) — used to descend the `inr` case.
        have ht_mono : Monic α.act := by
          -- `inr` (hypothesis coproduct) is monic via the canonical-coproduct comparison `φ`
          -- (`coprodInr_monic`); then `act = inr ≫ case`, `case` iso.
          have hinr_mono : Monic (HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := prod A α.obj)) := by
            intro W g h hgh
            let φ : HasBinaryCoproducts.coprod (one : 𝒞) (prod A α.obj)
                ⟶ coprodObj (one : 𝒞) (prod A α.obj) :=
              HasBinaryCoproducts.case (coprodInl (one : 𝒞) (prod A α.obj))
                (coprodInr (one : 𝒞) (prod A α.obj))
            have hr : HasBinaryCoproducts.inr ≫ φ = coprodInr (one : 𝒞) (prod A α.obj) :=
              HasBinaryCoproducts.case_inr _ _
            apply coprodInr_monic (one : 𝒞) (prod A α.obj)
            rw [← hr, ← Cat.assoc, ← Cat.assoc, hgh]
          have hcr : HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := prod A α.obj)
              ≫ HasBinaryCoproducts.case α.unit α.act = α.act := HasBinaryCoproducts.case_inr _ _
          obtain ⟨ci, hci1, _⟩ := id hiso
          intro W g h hgh
          apply hinr_mono
          have e : (g ≫ HasBinaryCoproducts.inr) ≫ HasBinaryCoproducts.case α.unit α.act
              = (h ≫ HasBinaryCoproducts.inr) ≫ HasBinaryCoproducts.case α.unit α.act := by
            rw [Cat.assoc, Cat.assoc, hcr, hgh]
          have := congrArg (· ≫ ci) e
          simpa only [Cat.assoc, hci1, Cat.comp_id] using this
        -- the `act`-shifted source point `c b := prodMap A α.obj... b ≫ act` for `b : 1 → prod A A₂.dom`.
        -- single-valuedness of `p` over any value `cv : 1 → α.obj` that is a `t`-image of a `A₂`-value.
        have hfibSingleT : ∀ (b : (one : 𝒞) ⟶ prod A A₂.dom)
            (g₁ g₂ : (one : 𝒞) ⟶ G.dom),
            g₁ ≫ p = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act) →
            g₂ ≫ p = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act) → g₁ = g₂ := by
          intro b g₁ g₂ hg₁ hg₂
          -- the common value `cv := b ≫ (prodMap.. A₂.arr ≫ act)`.
          let cv : (one : 𝒞) ⟶ α.obj := b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act)
          -- reduce each preimage `g` of `cv` to an `actG`-image of a preimage of the SOURCE `prod A G`-pt.
          have reduce : ∀ g : (one : 𝒞) ⟶ G.dom, g ≫ p = cv →
              ∃ w' : (one : 𝒞) ⟶ prod A G.dom, g = w' ≫ actG ∧
                (w' ≫ prodMap A G.dom α.obj p) ≫ α.act = cv := by
            intro g hg
            obtain ⟨wn, hwn⟩ := pts_covers_of_capital hcap hcg g
            rcases coprod_point_split hcap htv wn with ⟨u, hu⟩ | ⟨w', hw'⟩
            · -- `inl`: `g = g₀`, `cv = g≫p = unit` — `unit` a `t`-image, absurd by `[unit,act]`-disjointness.
              exfalso
              have hinlcg : HasBinaryCoproducts.inl (A := (one : 𝒞)) (B := prod A G.dom) ≫ cg = g₀ :=
                HasBinaryCoproducts.case_inl _ _
              have hgg₀ : g = g₀ := by
                calc g = wn ≫ cg := hwn.symm
                  _ = (u ≫ HasBinaryCoproducts.inl) ≫ cg := by rw [hu]
                  _ = u ≫ (HasBinaryCoproducts.inl ≫ cg) := Cat.assoc _ _ _
                  _ = u ≫ g₀ := by rw [hinlcg]
                  _ = g₀ := by rw [term_uniq u (Cat.id one), Cat.id_comp]
              have hg₀p : g₀ ≫ p = α.unit := by
                show g₀ ≫ G.arr ≫ fst = α.unit
                rw [← Cat.assoc, hg₀]; exact fst_pair _ _
              have hac : α.unit = (b ≫ prodMap A A₂.dom α.obj A₂.arr) ≫ α.act := by
                rw [Cat.assoc]
                show α.unit = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act)
                rw [← hg₀p, ← hgg₀]; exact hg
              refine coprod_inj_disjoint_pt htv (Cat.id one) (b ≫ prodMap A A₂.dom α.obj A₂.arr) ?_
              apply hcase_mono
              rw [Cat.assoc, Cat.assoc, HasBinaryCoproducts.case_inl,
                  HasBinaryCoproducts.case_inr, Cat.id_comp, ← hac]
            · -- `inr`: `g = w' ≫ actG`; `(w'≫prodMap.. p)≫act = g≫p = cv`, descend.
              have hinrcg : HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := prod A G.dom) ≫ cg = actG :=
                HasBinaryCoproducts.case_inr _ _
              have hgtG : g = w' ≫ actG := by
                calc g = wn ≫ cg := hwn.symm
                  _ = (w' ≫ HasBinaryCoproducts.inr) ≫ cg := by rw [hw']
                  _ = w' ≫ (HasBinaryCoproducts.inr ≫ cg) := Cat.assoc _ _ _
                  _ = w' ≫ actG := by rw [hinrcg]
              refine ⟨w', hgtG, ?_⟩
              calc (w' ≫ prodMap A G.dom α.obj p) ≫ α.act
                  = w' ≫ (prodMap A G.dom α.obj p ≫ α.act) := Cat.assoc _ _ _
                _ = w' ≫ (actG ≫ p) := by rw [hpt]
                _ = (w' ≫ actG) ≫ p := (Cat.assoc _ _ _).symm
                _ = g ≫ p := by rw [← hgtG]
                _ = cv := hg
          have hg₁cv : g₁ ≫ p = cv := hg₁
          have hg₂cv : g₂ ≫ p = cv := hg₂
          obtain ⟨w₁, hw₁eq, hw₁p⟩ := reduce g₁ hg₁cv
          obtain ⟨w₂, hw₂eq, hw₂p⟩ := reduce g₂ hg₂cv
          -- `(w₁≫prodMap.. p)≫act = (w₂≫prodMap.. p)≫act = cv`; `act` monic gives the two
          -- `prod A G.dom`-source points equal AFTER the `p`-leg, hence `w₁≫prodMap.. p = w₂≫prodMap.. p`.
          have hsrc : w₁ ≫ prodMap A G.dom α.obj p = w₂ ≫ prodMap A G.dom α.obj p :=
            ht_mono _ _ (by rw [hw₁p, hw₂p])
          -- `w₁ ≫ p = w₂ ≫ p` (the second `prodMap` leg is `p`): off-diagonal kernel-pair point ⟹ K'.
          have hw₁₂p : w₁ ≫ (prodMap A G.dom α.obj p ≫ snd) = w₂ ≫ (prodMap A G.dom α.obj p ≫ snd) := by
            rw [← Cat.assoc, ← Cat.assoc, hsrc]
          have hlegs : (w₁ ≫ snd (A := A) (B := G.dom)) ≫ p
              = (w₂ ≫ snd (A := A) (B := G.dom)) ≫ p := by
            have hpm : prodMap A G.dom α.obj p ≫ snd = snd ≫ p := prodMap_snd A G.dom α.obj p
            rw [hpm] at hw₁₂p
            rw [Cat.assoc, Cat.assoc]; exact hw₁₂p
          -- single-valuedness over the `A₂`-value forces `w₁≫snd = w₂≫snd`.
          have hsnd_eq : w₁ ≫ snd (A := A) (B := G.dom) = w₂ ≫ snd (A := A) (B := G.dom) := by
            classical
            by_cases hne : w₁ ≫ snd (A := A) (B := G.dom) = w₂ ≫ snd (A := A) (B := G.dom)
            · exact hne
            exfalso
            let z₁ : (one : 𝒞) ⟶ G.dom := w₁ ≫ snd (A := A) (B := G.dom)
            let z₂ : (one : 𝒞) ⟶ G.dom := w₂ ≫ snd (A := A) (B := G.dom)
            let κ : (one : 𝒞) ⟶ kernelPair p :=
              (HasPullbacks.has p p).lift ⟨one, z₁, z₂, hlegs⟩
            have hκ₁ : κ ≫ kp₁ (f := p) = z₁ := kp_lift_p₁ z₁ z₂ hlegs
            have hκ₂ : κ ≫ kp₂ (f := p) = z₂ := kp_lift_p₂ z₁ z₂ hlegs
            have hκent : (Subobject.mk one κ (mono_from_one _)).le
                (Subobject.entire (kernelPair p)) := ⟨κ, Cat.comp_id _⟩
            have hκtop := subLe_trans' hκent hΔunion
            obtain ⟨e, he⟩ := hκtop
            rcases union_point_split hcap htv Δ K' e with ⟨d, hd⟩ | ⟨k, hk⟩
            · -- `κ ∈ Δ`: legs agree, so `z₁ = z₂` — contradicts `hne`.
              apply hne
              have hdΔ : d ≫ Δ.arr = κ := by rw [hd]; exact he
              have hΔlegs : Δ.arr ≫ kp₁ (f := p) = Δ.arr ≫ kp₂ (f := p) := by
                refine cover_epi (image_lift_cover (kp_diag (f := p))) ?_
                calc image.lift (kp_diag (f := p)) ≫ (Δ.arr ≫ kp₁ (f := p))
                    = (image.lift (kp_diag (f := p)) ≫ Δ.arr) ≫ kp₁ (f := p) := (Cat.assoc _ _ _).symm
                  _ = kp_diag (f := p) ≫ kp₁ (f := p) := by rw [image.lift_fac]
                  _ = kp_diag (f := p) ≫ kp₂ (f := p) := by rw [kp_diag_p₁, kp_diag_p₂]
                  _ = (image.lift (kp_diag (f := p)) ≫ Δ.arr) ≫ kp₂ (f := p) := by rw [image.lift_fac]
                  _ = image.lift (kp_diag (f := p)) ≫ (Δ.arr ≫ kp₂ (f := p)) := Cat.assoc _ _ _
              show z₁ = z₂
              calc z₁ = κ ≫ kp₁ (f := p) := hκ₁.symm
                _ = (d ≫ Δ.arr) ≫ kp₁ (f := p) := by rw [hdΔ]
                _ = d ≫ (Δ.arr ≫ kp₁ (f := p)) := Cat.assoc _ _ _
                _ = d ≫ (Δ.arr ≫ kp₂ (f := p)) := by rw [hΔlegs]
                _ = (d ≫ Δ.arr) ≫ kp₂ (f := p) := (Cat.assoc _ _ _).symm
                _ = κ ≫ kp₂ (f := p) := by rw [hdΔ]
                _ = z₂ := hκ₂
            · -- `κ ∈ K'`: the common `p`-value `z₁≫p` factors through `A₁`; but it also `= cv`'s source
              -- value `(b's A₂)`, so `∈ A₁ ∩ A₂ ≤ ⊥` — absurd.  `z₁ ≫ p = (w₁≫snd)≫p = w₁≫(snd≫p)`.
              exfalso
              have hκK' : k ≫ K'.arr = κ := by rw [hk]; exact he
              -- the A₂-value `bv := b ≫ (prodMap A A₂.dom α.obj A₂.arr)` (the `act`-source's α.obj-leg).
              let bv : (one : 𝒞) ⟶ α.obj := b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ snd)
              have hbv_A₂ : bv = (b ≫ snd (A := A) (B := A₂.dom)) ≫ A₂.arr := by
                show b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ snd) = (b ≫ snd) ≫ A₂.arr
                rw [prodMap_snd, ← Cat.assoc]
              -- `z₁ ≫ p = bv`: `z₁≫p = (w₁≫snd)≫p = w₁≫(snd≫p) = w₁≫(prodMap.. p ≫ snd)` and the
              -- α.obj-leg of `w₁≫prodMap.. p` equals `bv` (single-valued act-source).
              have hz₁p : z₁ ≫ p = bv := by
                have hpm : prodMap A G.dom α.obj p ≫ snd = snd ≫ p := prodMap_snd A G.dom α.obj p
                -- `bv = (w₁ ≫ prodMap.. p) ≫ snd` because `act` is injective on the source legs?
                -- Direct: `w₁ ≫ prodMap.. p` and `b ≫ prodMap.. A₂.arr` have equal `act`-value (`hw₁p`),
                -- and equal A-leg... we only need the α.obj-leg (snd) equality, obtained from `act` monic.
                -- `hsrc'`: the `act`-source `w₁≫prodMap.. p = b ≫ prodMap.. A₂.arr` (both → prod A α.obj).
                have hsrc' : w₁ ≫ prodMap A G.dom α.obj p = b ≫ prodMap A A₂.dom α.obj A₂.arr :=
                  ht_mono _ _ (by
                    calc (w₁ ≫ prodMap A G.dom α.obj p) ≫ α.act = cv := hw₁p
                      _ = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act) := rfl
                      _ = (b ≫ prodMap A A₂.dom α.obj A₂.arr) ≫ α.act := (Cat.assoc _ _ _).symm)
                calc z₁ ≫ p = (w₁ ≫ snd (A := A) (B := G.dom)) ≫ p := rfl
                  _ = w₁ ≫ (snd (A := A) (B := G.dom) ≫ p) := Cat.assoc _ _ _
                  _ = w₁ ≫ (prodMap A G.dom α.obj p ≫ snd) := by rw [hpm]
                  _ = (w₁ ≫ prodMap A G.dom α.obj p) ≫ snd := (Cat.assoc _ _ _).symm
                  _ = (b ≫ prodMap A A₂.dom α.obj A₂.arr) ≫ snd := by rw [hsrc']
                  _ = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ snd) := Cat.assoc _ _ _
                  _ = bv := rfl
              -- `bv` factors through `A₁ = image q` (off-diagonal leg) and through `A₂` (definition).
              have hvalA₁ : (k ≫ image.lift q) ≫ A₁.arr = bv := by
                show (k ≫ image.lift q) ≫ (image q).arr = bv
                rw [Cat.assoc, image.lift_fac]
                show k ≫ K'.arr ≫ kp₁ (f := p) ≫ p = bv
                calc k ≫ K'.arr ≫ kp₁ (f := p) ≫ p
                    = (k ≫ K'.arr) ≫ kp₁ (f := p) ≫ p := (Cat.assoc _ _ _).symm
                  _ = κ ≫ kp₁ (f := p) ≫ p := by rw [hκK']
                  _ = (κ ≫ kp₁ (f := p)) ≫ p := (Cat.assoc _ _ _).symm
                  _ = z₁ ≫ p := by rw [hκ₁]
                  _ = bv := hz₁p
              have hptbot : (Subobject.mk one bv (mono_from_one _)).le
                  (PreLogos.bottom α.obj) :=
                subLe_trans'
                  (Subobject.le_inter (S := A₁) (T := A₂)
                    ⟨k ≫ image.lift q, hvalA₁⟩
                    ⟨b ≫ snd (A := A) (B := A₂.dom), hbv_A₂.symm⟩)
                  hA₁disj
              obtain ⟨m, _⟩ := hptbot
              exact point_bottom_absurd htv (Cat.id one ≫ m)
          -- `w₁ ≫ snd = w₂ ≫ snd` AND `w₁ ≫ prodMap.. p = w₂ ≫ prodMap.. p` (i.e. the A-legs and
          -- α.obj-legs agree)... but we only need `g₁ = g₂`, and `gᵢ = wᵢ ≫ actG`; here `actG` only
          -- sees the source point `wᵢ` through `prodMap.. G.arr ≫ Sgraph`.  Use that `actG` factors
          -- the source: `gᵢ = wᵢ ≫ actG`, and the two sources `wᵢ` agree on BOTH legs
          -- (`A`-leg: hsrc's `fst`; `snd`-leg: `hsnd_eq`), so `w₁ = w₂` by product extensionality.
          have hfst_eq : w₁ ≫ fst (A := A) (B := G.dom) = w₂ ≫ fst (A := A) (B := G.dom) := by
            have hpmf : prodMap A G.dom α.obj p ≫ fst = fst := prodMap_fst A G.dom α.obj p
            have := hsrc
            calc w₁ ≫ fst (A := A) (B := G.dom)
                = w₁ ≫ (prodMap A G.dom α.obj p ≫ fst) := by rw [hpmf]
              _ = (w₁ ≫ prodMap A G.dom α.obj p) ≫ fst := (Cat.assoc _ _ _).symm
              _ = (w₂ ≫ prodMap A G.dom α.obj p) ≫ fst := by rw [hsrc]
              _ = w₂ ≫ (prodMap A G.dom α.obj p ≫ fst) := Cat.assoc _ _ _
              _ = w₂ ≫ fst (A := A) (B := G.dom) := by rw [hpmf]
          have hw₁w₂ : w₁ = w₂ := by
            rw [pair_eta w₁, pair_eta w₂, hfst_eq, hsnd_eq]
          rw [hw₁eq, hw₂eq, hw₁w₂]
        -- `A₁ ∩ act(A₂) ≤ ⊥`: a point of `act(A₂)` is `act(b)` with `b` an `A₂`-source point;
        -- `hfibSingleT` makes both off-diagonal legs over it equal, contradiction via `kpPointAbsurd`.
        have hdisj_t : (Subobject.inter A₁ (image (prodMap A A₂.dom α.obj A₂.arr ≫ α.act))).le
            (PreLogos.bottom α.obj) := by
          refine noPoint_le_bottom hcap htv _ ?_
          rintro _ ⟨y, _⟩
          obtain ⟨kL, hkL⟩ := Subobject.inter_le_left A₁
            (image (prodMap A A₂.dom α.obj A₂.arr ≫ α.act))
          obtain ⟨kR, hkR⟩ := Subobject.inter_le_right A₁
            (image (prodMap A A₂.dom α.obj A₂.arr ≫ α.act))
          obtain ⟨b, hb⟩ := pts_covers_of_capital hcap
            (image_lift_cover (prodMap A A₂.dom α.obj A₂.arr ≫ α.act)) (y ≫ kR)
          have hbval : (y ≫ kR) ≫ (image (prodMap A A₂.dom α.obj A₂.arr ≫ α.act)).arr
              = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act) := by
            show (y ≫ kR) ≫ (image (prodMap A A₂.dom α.obj A₂.arr ≫ α.act)).arr
                = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act)
            rw [← hb, Cat.assoc, image.lift_fac]
          obtain ⟨k₀, hk₀⟩ := pts_covers_of_capital hcap (image_lift_cover q) (y ≫ kL)
          have hcommon : (y ≫ kL) ≫ A₁.arr = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act) := by
            have : (y ≫ kL) ≫ A₁.arr
                = (y ≫ kR) ≫ (image (prodMap A A₂.dom α.obj A₂.arr ≫ α.act)).arr := by
              rw [Cat.assoc, Cat.assoc, hkL, hkR]
            rw [this, hbval]
          have hk₀q : k₀ ≫ q = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act) := by
            have : k₀ ≫ q = (y ≫ kL) ≫ A₁.arr := by
              show k₀ ≫ K'.arr ≫ kp₁ (f := p) ≫ p = (y ≫ kL) ≫ (image q).arr
              rw [← hk₀, Cat.assoc, image.lift_fac]
            rw [this, hcommon]
          apply kpPointAbsurd k₀
          have hg₁ : (k₀ ≫ K'.arr ≫ kp₁ (f := p)) ≫ p
              = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act) := by
            rw [Cat.assoc, Cat.assoc]; exact hk₀q
          have hg₂ : (k₀ ≫ K'.arr ≫ kp₂ (f := p)) ≫ p
              = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act) := by
            calc (k₀ ≫ K'.arr ≫ kp₂ (f := p)) ≫ p
                = k₀ ≫ K'.arr ≫ (kp₂ (f := p) ≫ p) := by rw [Cat.assoc, Cat.assoc]
              _ = k₀ ≫ K'.arr ≫ (kp₁ (f := p) ≫ p) := by rw [← kp_sq]
              _ = (k₀ ≫ K'.arr ≫ kp₁ (f := p)) ≫ p := by rw [Cat.assoc, Cat.assoc]
              _ = b ≫ (prodMap A A₂.dom α.obj A₂.arr ≫ α.act) := hg₁
          rw [hfibSingleT b _ _ hg₁ hg₂]
        have hle : (image (prodMap A A₂.dom α.obj A₂.arr ≫ α.act)).le A₂ :=
          complement_le_other' A₁ A₂ (image (prodMap A A₂.dom α.obj A₂.arr ≫ α.act))
            hdisj_t hA₁union
        obtain ⟨k, hk⟩ := hle
        exact ⟨image.lift (prodMap A A₂.dom α.obj A₂.arr ≫ α.act) ≫ k, by
          rw [Cat.assoc, hk, image.lift_fac]⟩
      -- `A₂` ENTIRE by the free Peano property.
      have hA₂entire : A₂.IsEntire :=
        free_peano_of_bicartesian hbool A α hiso hcoeq A₂ hA₂a hA₂t
      -- `A₂` entire ⟹ `A₁ ≤ ⊥`.
      have hA₁bot : A₁.le (PreLogos.bottom α.obj) := by
        refine subLe_trans' ?_ hA₁disj
        refine Subobject.le_inter ⟨Cat.id _, Cat.id_comp _⟩ ?_
        obtain ⟨inv, _, hinv2⟩ := hA₂entire
        exact ⟨A₁.arr ≫ inv, by rw [Cat.assoc, hinv2, Cat.comp_id]⟩
      -- `A₁ ≤ ⊥ ⟹ K' ≤ ⊥`.
      have hK'bot : K'.le (PreLogos.bottom (kernelPair p)) := by
        obtain ⟨m, _hm⟩ := hA₁bot
        exact peano_le_bottom_of_map K' (image.lift q ≫ m)
      -- `K' ≤ ⊥ ⟹ Δ entire`.
      have hΔentire : Δ.IsEntire :=
        entire_of_entire_le (subLe_trans' hΔunion
          (HasSubobjectUnions.union_min Δ K' Δ ⟨Cat.id _, Cat.id_comp _⟩
            (subLe_trans' hK'bot (PreLogos.bottom_min Δ))))
      -- `Δ` entire ⟹ `kp_diag` cover ⟹ iso.
      have hdiagcover : Cover (kp_diag (f := p)) :=
        (cover_iff_image_entire (kp_diag (f := p))).2 hΔentire
      exact monic_cover_iso (kp_diag (f := p)) hdiagcover
        (mono_of_retraction _ (kp₁ (f := p)) kp_diag_p₁)
    have hpiso : IsIso p := monic_cover_iso p hpcover hpmono
    obtain ⟨pinv, hpinv1, hpinv2⟩ := hpiso
    -- `h := p⁻¹ ≫ G.arr ≫ snd`.  `unit ≫ h = β.unit` and the action square follow from the graph laws.
    refine ⟨pinv ≫ G.arr ≫ snd, ?_, ?_⟩
    · -- `unit ≫ h = β.unit`.  `unit = g₀ ≫ p`, `g₀ ≫ p ≫ pinv = g₀`, reduce to `g₀≫G.arr≫snd = β.unit`.
      have hap : α.unit = g₀ ≫ p := by
        show α.unit = g₀ ≫ G.arr ≫ fst
        rw [← Cat.assoc, hg₀]; exact (fst_pair _ _).symm
      have hcollapse : α.unit ≫ pinv = g₀ := by rw [hap, Cat.assoc, hpinv1, Cat.comp_id]
      calc α.unit ≫ pinv ≫ G.arr ≫ snd = (α.unit ≫ pinv) ≫ G.arr ≫ snd := (Cat.assoc _ _ _).symm
        _ = g₀ ≫ G.arr ≫ snd := by rw [hcollapse]
        _ = (g₀ ≫ G.arr) ≫ snd := (Cat.assoc _ _ _).symm
        _ = unitPt ≫ snd := by rw [hg₀]
        _ = β.unit := snd_pair _ _
    · -- `prodMap A α.obj β.obj h ≫ β.act = α.act ≫ h`.  Both chase through the graph's β-leg law
      -- `Sgraph ≫ snd = actOnSnd` and the α-leg iso (`prodMap.. pinv ≫ actG = act ≫ pinv`).
      have hSgSnd : Sgraph ≫ snd = pair fst (snd ≫ snd) ≫ β.act := snd_pair _ _
      -- `prodMap A α.obj G.dom pinv ≫ actG = α.act ≫ pinv` (both `≫ p` give `α.act`, `p` monic).
      have htpinv : prodMap A α.obj G.dom pinv ≫ actG = α.act ≫ pinv := by
        apply hpmono
        calc (prodMap A α.obj G.dom pinv ≫ actG) ≫ p
            = prodMap A α.obj G.dom pinv ≫ (actG ≫ p) := Cat.assoc _ _ _
          _ = prodMap A α.obj G.dom pinv ≫ (prodMap A G.dom α.obj p ≫ α.act) := by rw [hpt]
          _ = (prodMap A α.obj G.dom pinv ≫ prodMap A G.dom α.obj p) ≫ α.act := (Cat.assoc _ _ _).symm
          _ = prodMap A α.obj α.obj (pinv ≫ p) ≫ α.act := by rw [← prodMap_comp]
          _ = prodMap A α.obj α.obj (Cat.id α.obj) ≫ α.act := by rw [hpinv2]
          _ = α.act := by rw [prodMap_id, Cat.id_comp]
          _ = (α.act ≫ pinv) ≫ p := by rw [Cat.assoc, hpinv2, Cat.comp_id]
      -- `h = pinv ≫ G.arr ≫ snd`;  `prodMap A α.obj β.obj h = pair fst (snd ≫ h)`.
      have hprodh : prodMap A α.obj (prod α.obj β.obj) (pinv ≫ G.arr)
          ≫ pair (fst (A := A) (B := prod α.obj β.obj)) (snd ≫ snd)
          = prodMap A α.obj β.obj (pinv ≫ G.arr ≫ snd) := by
        apply pair_uniq
        · -- `≫ fst`: both `= fst`.
          simp only [Cat.assoc, fst_pair, prodMap_fst]
        · -- `≫ snd`:  `(snd ≫ (pinv≫G.arr)) ≫ snd = snd ≫ pinv ≫ G.arr ≫ snd`.
          rw [Cat.assoc, snd_pair, ← Cat.assoc, prodMap_snd, Cat.assoc, Cat.assoc]
      calc prodMap A α.obj β.obj (pinv ≫ G.arr ≫ snd) ≫ β.act
          = (prodMap A α.obj (prod α.obj β.obj) (pinv ≫ G.arr)
              ≫ pair fst (snd ≫ snd)) ≫ β.act := by rw [hprodh]
        _ = prodMap A α.obj (prod α.obj β.obj) (pinv ≫ G.arr) ≫ (pair fst (snd ≫ snd) ≫ β.act) :=
            Cat.assoc _ _ _
        _ = prodMap A α.obj (prod α.obj β.obj) (pinv ≫ G.arr) ≫ (Sgraph ≫ snd) := by rw [hSgSnd]
        _ = (prodMap A α.obj G.dom pinv ≫ prodMap A G.dom (prod α.obj β.obj) G.arr)
              ≫ (Sgraph ≫ snd) := by rw [prodMap_comp]
        _ = prodMap A α.obj G.dom pinv
              ≫ (prodMap A G.dom (prod α.obj β.obj) G.arr ≫ Sgraph) ≫ snd := by
            rw [Cat.assoc, Cat.assoc]
        _ = prodMap A α.obj G.dom pinv ≫ (actG ≫ G.arr) ≫ snd := by rw [hactG]
        _ = (prodMap A α.obj G.dom pinv ≫ actG) ≫ G.arr ≫ snd := by
            rw [Cat.assoc (prodMap A α.obj G.dom pinv) actG (G.arr ≫ snd),
                ← Cat.assoc actG G.arr snd]
        _ = (α.act ≫ pinv) ≫ G.arr ≫ snd := by rw [htpinv]
        _ = α.act ≫ pinv ≫ G.arr ≫ snd := Cat.assoc _ _ _
  · -- UNIQUENESS via the free equalizer + the action Peano property.
    intro e he0 hes
    exact free_recursor_unique_of_bicartesian hbool A α hiso hcoeq α e (Cat.id α.obj)
      he0 hes (by rw [Cat.comp_id]) (by
        rw [Cat.comp_id, prodMap_id, Cat.id_comp])

/-- §1.98(13): Bicartesian characterization of a free A-action.
    An A-action (A*, e : 1 → A*, s : A × A* → A*) is FREE iff
    [(e, s)] : 1 + A × A* → A* is iso and p₂ : A × A* → A* → 1 is a coequalizer.
    (Analogue of §1.98(10); EXISTENCE of the free recursor is the §1.988 residual
    `free_recursor_exists_of_bicartesian`; UNIQUENESS is proved Sorry-free here.) -/
theorem free_action_iff_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
    (hbool : BooleanSub 𝒞) (hcap : Capital (𝒞 := 𝒞)) (htv : TwoValued (𝒞 := 𝒞))
    (A : 𝒞) (α : AAction (𝒞 := 𝒞) A)
    -- [unit, act] : 1 + A × α.obj → α.obj is iso
    (hiso : IsIso (HasBinaryCoproducts.case α.unit α.act
                   (A := one) (B := prod A α.obj) (X := α.obj)))
    -- p₂ : A × A* → 1 is a coequalizer of (act, p₂)
    (hcoeq : ∀ (X : 𝒞) (f : α.obj ⟶ X),
               α.act ≫ f = snd (A := A) (B := α.obj) ≫ f →
               ∃ g : one ⟶ X, term α.obj ≫ g = f ∧
                 ∀ g' : one ⟶ X, term α.obj ≫ g' = f → g' = g) :
    Nonempty (FreeAAction (𝒞 := 𝒞) A) := by
  -- The A-action analogue of `nno_of_bicartesian_data` (§1.98(13), "analogously to [1.985] and
  -- [1.98(10)]").  We reduce the whole free A-action to ONE sharp obligation `hrec`: existence of
  -- the free recursor `recA β : α.obj → β.obj` for every A-action `β`, with its two compatibility
  -- squares and uniqueness.  Packaging `hrec` into a `FreeAAction` (whose underlying `AAction` is
  -- `α` itself) via `Classical.choice` is verified below.
  --
  -- `hrec` IS the §1.98(13) free recursor: from `pred := [unit,act]⁻¹ : α.obj → 1 + A×α.obj` a map
  -- `h : α.obj → β.obj` is a free homomorphism iff `h = pred ≫ case β.unit (prodMap A α.obj β.obj h
  -- ≫ β.act)` (a fixpoint), built by §1.988 through the lawful per-codomain partial-map classifier
  -- (`Fredy.partialMapClassifier_exists`, now Sorry-free) whose partial-recursor domain `R ↣ α.obj`
  -- is `(unit,act)`-stable and forced entire by the §1.987 Peano INDUCTION that `hcoeq` powers.
  -- The single missing primitive is that Peano-induction recursor (the SAME residual as
  -- `nno_of_bicartesian_data`): `least_peano_subobject` gives the least closed subobject's
  -- existence, not that the bicartesian data makes it entire.  STATUS: NOT §1.543-capitalization
  -- (proven Sorry-free here); the residual is the absent §1.988 W-type / internal-∀ Peano-induction.
  have hrec : ∀ (β : AAction (𝒞 := 𝒞) A),
      ∃ h : α.obj ⟶ β.obj,
        (α.unit ≫ h = β.unit ∧ prodMap A α.obj β.obj h ≫ β.act = α.act ≫ h) ∧
        ∀ h' : α.obj ⟶ β.obj, α.unit ≫ h' = β.unit →
          prodMap A α.obj β.obj h' ≫ β.act = α.act ≫ h' → h' = h := by
    -- EXISTENCE from `free_recursor_exists_of_bicartesian` (the single residual); UNIQUENESS
    -- proved here Sorry-free from the action Peano property via the equalizer.
    intro β
    obtain ⟨hex, _⟩ := free_recursor_exists_of_bicartesian hbool hcap htv A α hiso hcoeq
    obtain ⟨h, hh0, hhs⟩ := hex β
    exact ⟨h, ⟨hh0, hhs⟩, fun h' h0' hs' =>
      free_recursor_unique_of_bicartesian hbool A α hiso hcoeq β h' h h0' hs' hh0 hhs⟩
  exact ⟨{
    obj := α.obj
    unit := α.unit
    act := α.act
    recA := fun β => (hrec β).choose
    recA_unit := fun β => (hrec β).choose_spec.1.1
    recA_act := fun β => (hrec β).choose_spec.1.2
    recA_uniq := fun β m hm0 hms => (hrec β).choose_spec.2 m hm0 hms }⟩

/-! ## §1.98(14)  Existence of free A-action from NNO

  §1.98(14): In a topos with a NNO, for any object A there exists a free A-action.
  The construction uses primRec (or iteratePair) applied to A: the free A-action
  A* is the A-fold "list" object built from the NNO universal property. -/

/-! ### §1.98(14) construction — the exponential carrier `W = (1+A)^N`

  A word in `A` is a map `N → 1+A` that is `inr a` on a prefix `{0,…,len-1}` and `inl ⋆`
  afterwards (a "stream eventually constant `⋆`").  The ambient object is the exponential
  `W := (1+A)^N`; the element-reader is exponential evaluation; `cons` prepends a letter by
  the NNO case-split `1+N ≅ N` on the index.  The list object `A*` is then the least
  `(nil, cons)`-closed subobject of `W` (`actLeast`). -/

section ListObjectConstruction
variable {𝒞 : Type u} [Cat.{v} 𝒞] [hN : HasNaturalNumbersObject 𝒞]
variable (A : 𝒞)

open HasBinaryCoproducts

-- Use the canonical `topos_has_exponentials` (whose `.toHasBinaryProducts` IS the Topos
-- products, definitionally — see `exponentials_of_all_baseable`).  This keeps the exponential
-- maps (`curry`/`eval_exp`) and the product/`actLeast` machinery on a SINGLE products instance,
-- avoiding the diamond that makes `isDefEq` diverge.

/-- The letter object `E = 1 + A` (a letter is either the "blank" `⋆ : 1` or `a : A`). -/
noncomputable abbrev letterObj : 𝒞 := coprod one A

/-- The word carrier `W = (1+A)^N` (a word is a stream of letters, eventually blank). -/
noncomputable abbrev wordObj : 𝒞 := exp hN.nno (letterObj A)

/-- The empty word `[] : 1 → W` — the constant stream `inl ⋆` (blank everywhere). -/
noncomputable def nilMor : one ⟶ wordObj A :=
  curry (A := hN.nno) (B := letterObj A) (X := one) (term _ ≫ inl)

/-- The body of `cons`: `prod N (prod A W) ⟶ 1+A`.  Reads index `n`; via `1+N≅N` it is
    either the new head `inr a` (when `n = 0`) or the shifted lookup `eval(w, m)` (when
    `n = succ m`).  Reindex `n` through `(1+N≅N)⁻¹`, braid the letter-pair to the front,
    then `distCase`. -/
noncomputable def consBody : prod hN.nno (prod A (wordObj A)) ⟶ letterObj A :=
  let cInv : hN.nno ⟶ coprod one hN.nno := (nno_is_coproduct (𝒞 := 𝒞)).choose
  -- shift leg: from `prod (prod A W) N`, output `eval (w, m)`.
  let legShift : prod (prod A (wordObj A)) hN.nno ⟶ letterObj A :=
    pair snd (fst ≫ snd) ≫ eval_exp hN.nno (letterObj A)
  -- new-head leg: from `prod (prod A W) 1`, output `inr (the letter a)`.
  let legNil : prod (prod A (wordObj A)) one ⟶ letterObj A := fst ≫ fst ≫ inr
  pair snd (fst ≫ cInv) ≫ distCase legNil legShift

/-- Prepend `cons : A × W ⟶ W`, the transpose of `consBody`. -/
noncomputable def consMor : prod A (wordObj A) ⟶ wordObj A :=
  curry (consBody A)

/-! #### β-laws for reading words (`eval`) at an index.
  `readAt n w := pair n w ≫ eval` reads the word `w : X → W` at index `n : X → N`. -/

/-- Reading the empty word `nilMor` at any index gives the blank letter `inl ⋆`. -/
theorem nilMor_read {X : 𝒞} (n : X ⟶ hN.nno) (t : X ⟶ one) :
    pair n (t ≫ nilMor A) ≫ eval_exp hN.nno (letterObj A)
      = term X ≫ (inl : one ⟶ letterObj A) := by
  rw [show pair n (t ≫ nilMor A) = pair n t ≫ prodMap hN.nno one (wordObj A) (nilMor A) from
        (pair_prodMap n t (nilMor A)).symm, Cat.assoc]
  show pair n t ≫ prodMap hN.nno one (wordObj A) (curry _) ≫ eval_exp hN.nno (letterObj A) = _
  rw [curry_eval_eq, ← Cat.assoc, term_uniq (pair n t ≫ term _) (term X)]

/-- Reading `consMor (a, w)` at index `n` equals `consBody` applied to `⟨n, a, w⟩`. -/
theorem consMor_read {X : 𝒞} (n : X ⟶ hN.nno) (p : X ⟶ prod A (wordObj A)) :
    pair n (p ≫ consMor A) ≫ eval_exp hN.nno (letterObj A)
      = pair n p ≫ consBody A := by
  rw [show pair n (p ≫ consMor A) = pair n p ≫ prodMap hN.nno (prod A (wordObj A)) (wordObj A)
        (consMor A) from (pair_prodMap n p (consMor A)).symm, Cat.assoc]
  show pair n p ≫ prodMap hN.nno _ (wordObj A) (curry (consBody A)) ≫ eval_exp hN.nno (letterObj A)
      = _
  rw [curry_eval_eq]

/-- `cInv := (1+N≅N)⁻¹`, the inverse of `[0,s] : 1+N → N`. -/
noncomputable def nnoCoUninv : hN.nno ⟶ coprod one hN.nno :=
  (nno_is_coproduct (𝒞 := 𝒞)).choose

theorem nnoCoUninv_spec : case hN.zero hN.succ ≫ nnoCoUninv (𝒞 := 𝒞) = Cat.id _ :=
  (nno_is_coproduct (𝒞 := 𝒞)).choose_spec.1

/-- `0 ≫ cInv = inl`. -/
theorem zero_nnoCoUninv : hN.zero ≫ nnoCoUninv (𝒞 := 𝒞) = inl := by
  have h : (inl : one ⟶ coprod one hN.nno) ≫ case hN.zero hN.succ = hN.zero := case_inl _ _
  rw [← h, Cat.assoc, nnoCoUninv_spec]; exact Cat.comp_id _

/-- `s ≫ cInv = inr`. -/
theorem succ_nnoCoUninv : hN.succ ≫ nnoCoUninv (𝒞 := 𝒞) = inr := by
  have h : (inr : hN.nno ⟶ coprod one hN.nno) ≫ case hN.zero hN.succ = hN.succ := case_inr _ _
  rw [← h, Cat.assoc, nnoCoUninv_spec]; exact Cat.comp_id _

/-- The `consBody` definition restated with the named inverse `nnoCoUninv`. -/
theorem consBody_eq :
    consBody A = pair snd (fst ≫ nnoCoUninv) ≫
      distCase (fst ≫ fst ≫ inr)
        (pair snd (fst ≫ snd) ≫ eval_exp hN.nno (letterObj A)) := rfl

/-- Index-0 β-law: reading `cons(a,w)` at `0` gives the new head `inr a`. -/
theorem consBody_zero {X : 𝒞} (t : X ⟶ one) (p : X ⟶ prod A (wordObj A)) :
    pair (t ≫ hN.zero) p ≫ consBody A = p ≫ fst ≫ (inr : A ⟶ letterObj A) := by
  rw [consBody_eq, ← Cat.assoc]
  -- `pair (t≫0) p ≫ pair snd (fst≫cInv) = pair p (t ≫ inl)`
  have hre : pair (t ≫ hN.zero) p ≫ pair snd (fst ≫ nnoCoUninv)
      = pair p (t ≫ (inl : one ⟶ coprod one hN.nno)) := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, snd_pair]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, fst_pair, Cat.assoc, zero_nnoCoUninv]
  rw [hre, show pair p (t ≫ (inl : one ⟶ coprod one hN.nno))
        = pair p t ≫ distInl (prod A (wordObj A)) one hN.nno by
      unfold distInl; rw [pair_prodMap], Cat.assoc, distCase_inl, ← Cat.assoc, fst_pair]

/-- Index-succ β-law: reading `cons(a,w)` at `succ m` equals reading `w` at `m`. -/
theorem consBody_succ {X : 𝒞} (m : X ⟶ hN.nno) (p : X ⟶ prod A (wordObj A)) :
    pair (m ≫ hN.succ) p ≫ consBody A
      = pair m (p ≫ snd) ≫ eval_exp hN.nno (letterObj A) := by
  rw [consBody_eq, ← Cat.assoc]
  have hre : pair (m ≫ hN.succ) p ≫ pair snd (fst ≫ nnoCoUninv)
      = pair p (m ≫ (inr : hN.nno ⟶ coprod one hN.nno)) := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, snd_pair]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, fst_pair, Cat.assoc, succ_nnoCoUninv]
  rw [hre, show pair p (m ≫ (inr : hN.nno ⟶ coprod one hN.nno))
        = pair p m ≫ distInr (prod A (wordObj A)) one hN.nno by
      unfold distInr; rw [pair_prodMap], Cat.assoc, distCase_inr, ← Cat.assoc]
  -- `pair p m ≫ (pair snd (fst≫snd) ≫ eval) = pair m (p≫snd) ≫ eval`
  congr 1
  apply pair_uniq
  · rw [Cat.assoc, fst_pair, snd_pair]
  · rw [Cat.assoc, snd_pair, ← Cat.assoc, fst_pair]

end ListObjectConstruction

/-- §1.98(14): The LIST OBJECT `A*` of `A` — the initial algebra of the polynomial
    functor `F X = 1 + A × X`, packaged as `nil`/`cons` plus a `fold` recursor.

    This is exactly the free-A-action data in algebra form: `nil = []` is the empty
    word, `cons : A × A* → A*` prepends a letter, and `fold e c : A* → B` is the unique
    `F`-algebra homomorphism into `(B, e, c)`.  `fold_nil`/`fold_cons` are the algebra
    square and `fold_uniq` is initiality (the Peano/induction principle for `A*`). -/
structure ListObjectData {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞] (A : 𝒞) where
  /-- The list object `A* = Σₙ Aⁿ`. -/
  L    : 𝒞
  /-- The empty word `[] : 1 → A*`. -/
  nil  : one ⟶ L
  /-- Prepend `cons : A × A* → A*`. -/
  cons : prod A L ⟶ L
  /-- The fold/recursor into any `F`-algebra `(B, e : 1 → B, c : A × B → B)`. -/
  fold : {B : 𝒞} → (one ⟶ B) → (prod A B ⟶ B) → (L ⟶ B)
  /-- `fold` sends the empty word to the algebra's unit. -/
  fold_nil  : ∀ {B : 𝒞} (e : one ⟶ B) (c : prod A B ⟶ B), nil ≫ fold e c = e
  /-- `fold` is an `F`-algebra homomorphism: it commutes with `cons` / `c`. -/
  fold_cons : ∀ {B : 𝒞} (e : one ⟶ B) (c : prod A B ⟶ B),
    prodMap A L B (fold e c) ≫ c = cons ≫ fold e c
  /-- Initiality: any algebra homomorphism `A* → B` equals `fold`. -/
  fold_uniq : ∀ {B : 𝒞} (e : one ⟶ B) (c : prod A B ⟶ B) (m : L ⟶ B),
    nil ≫ m = e → prodMap A L B m ≫ c = cons ≫ m → m = fold e c

/-- §1.98(14): A list object for `A` IS a free A-action.

    This reduction is Sorry-free: the free-A-action universal property is precisely the
    initiality of the list object `A*` as an `F`-algebra (`F X = 1 + A × X`).  The unit
    is `nil`, the action is `cons`, and the unique map into any A-action `(B, f, b)` is
    `fold f b`; the three commutation laws are `fold_nil`, `fold_cons`, `fold_uniq`. -/
def freeAAction_of_listObject {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞] {A : 𝒞}
    (LD : ListObjectData (𝒞 := 𝒞) A) : FreeAAction (𝒞 := 𝒞) A where
  obj       := LD.L
  unit      := LD.nil
  act       := LD.cons
  recA      := fun α => LD.fold α.unit α.act
  recA_unit := fun α => LD.fold_nil α.unit α.act
  recA_act  := fun α => LD.fold_cons α.unit α.act
  recA_uniq := fun α m hm0 hms => LD.fold_uniq α.unit α.act m hm0 hms

/-! ### §1.98(14) — the list object as the least `(nil, cons)`-closed subobject of `W`

  `A* := actLeast nilMor consMor snd ⊆ W` (least subobject of `W = (1+A)^N` that contains the
  empty word `nilMor` and is closed under `consMor`).  `nil`/`cons` come from
  `actLeast_allows`/`actLeast_stable`; `fold_uniq` is `actLeast`'s leastness (induction). -/

section ListObjectAssembly
variable {𝒞 : Type u} [Cat.{v} 𝒞] [hN : HasNaturalNumbersObject 𝒞]
variable (A : 𝒞)

open HasBinaryCoproducts

-- NOTE: this assembly section uses the ambient Topos products (NOT the exponential ones),
-- because `actLeast`/`InverseImage`/`actImg_le_of_actStable` were all built with the Topos
-- products; forcing the exponential products here makes `isDefEq` diverge reconciling the two.
-- `nilMor`/`consMor` already have fixed (Topos-products) types from their section.

/-- **NON-BOOLEAN injection-disjointness elimination** for `HasBinaryCoproducts.coprod`.  If two
    maps `u, v : X ⟶ −` collide across the two injections (`u ≫ inl = v ≫ inr`), then `X` is
    "empty": ANY two maps out of `X` are equal.  Proof: transport along `φ = case coprodInl
    coprodInr : coprod A B → A+B` to the ambient-topos coproduct, where `coprodInjections_disjoint_elt`
    (strict-initial pullback of `coprodInl, coprodInr`) is non-boolean.  Unlike `coprod_inj_disjoint_pt`
    this needs NO `TwoValued`/boolean hypothesis. -/
theorem coprod_inj_disjoint_elt {P Q X : 𝒞} (u : X ⟶ P) (v : X ⟶ Q)
    (huv : u ≫ HasBinaryCoproducts.inl (A := P) (B := Q)
         = v ≫ HasBinaryCoproducts.inr (A := P) (B := Q)) :
    ∀ {Y : 𝒞} (a b : X ⟶ Y), a = b := by
  let φ : HasBinaryCoproducts.coprod P Q ⟶ coprodObj P Q :=
    HasBinaryCoproducts.case (coprodInl P Q) (coprodInr P Q)
  have hφl : HasBinaryCoproducts.inl (A := P) (B := Q) ≫ φ = coprodInl P Q :=
    HasBinaryCoproducts.case_inl _ _
  have hφr : HasBinaryCoproducts.inr (A := P) (B := Q) ≫ φ = coprodInr P Q :=
    HasBinaryCoproducts.case_inr _ _
  have hraw : u ≫ coprodInl P Q = v ≫ coprodInr P Q :=
    calc u ≫ coprodInl P Q = u ≫ (HasBinaryCoproducts.inl ≫ φ) := by rw [hφl]
      _ = (u ≫ HasBinaryCoproducts.inl) ≫ φ := (Cat.assoc _ _ _).symm
      _ = (v ≫ HasBinaryCoproducts.inr) ≫ φ := by rw [huv]
      _ = v ≫ (HasBinaryCoproducts.inr ≫ φ) := Cat.assoc _ _ _
      _ = v ≫ coprodInr P Q := by rw [hφr]
  intro Y a b
  exact coprodInjections_disjoint_elt u v hraw a b

/-- The list object `A* ⊆ W` — least `(nilMor, consMor, snd)`-closed subobject of `W`. -/
noncomputable def listCarrier : Subobject 𝒞 (wordObj A) :=
  actLeast (nilMor A) (consMor A) snd

/-- The empty word as a point of `A*` (from `actLeast_allows`). -/
noncomputable def listNil : one ⟶ (listCarrier A).dom :=
  (actLeast_allows (nilMor A) (consMor A) snd).choose

theorem listNil_arr : listNil A ≫ (listCarrier A).arr = nilMor A :=
  (actLeast_allows (nilMor A) (consMor A) snd).choose_spec

/-- `actLeast_stable` in image form: `image(prodMap.. ≫ consMor) ≤ A*`. -/
theorem listConsLe :
    (image (prodMap A (listCarrier A).dom (wordObj A) (listCarrier A).arr ≫ consMor A)).le
      (listCarrier A) :=
  actImg_le_of_actStable (consMor A) (listCarrier A) (actLeast_stable (nilMor A) (consMor A) snd)

/-- `cons` restricted to `A*`: `A × A* ⟶ A*` (from `actLeast_stable`, image form). -/
noncomputable def listCons : prod A (listCarrier A).dom ⟶ (listCarrier A).dom :=
  image.lift (prodMap A (listCarrier A).dom (wordObj A) (listCarrier A).arr ≫ consMor A)
    ≫ (listConsLe A).choose

theorem listCons_arr :
    listCons A ≫ (listCarrier A).arr
      = prodMap A (listCarrier A).dom (wordObj A) (listCarrier A).arr ≫ consMor A := by
  rw [listCons, Cat.assoc, (listConsLe A).choose_spec, image.lift_fac]

/-- **List induction / extensionality.**  Any two `F`-algebra homomorphisms out of the list
    object `A* = (listCarrier A)` into the same algebra `(B, e, c)` are equal.  Proof: the
    equalizer `E ↪ A*` of `m, m'`, pushed into `W`, contains `nilMor` and is `(consMor,snd)`-
    stable (using the two algebra squares + the equalizer agreement), so `actLeast_le` forces
    `A* ≤ E`, i.e. `eqMap` is split epi (hence iso), i.e. `m = m'`. -/
theorem listObject_ext {B : 𝒞} (e : one ⟶ B) (c : prod A B ⟶ B)
    (m m' : (listCarrier A).dom ⟶ B)
    (hm0 : listNil A ≫ m = e) (hm0' : listNil A ≫ m' = e)
    (hmc : prodMap A (listCarrier A).dom B m ≫ c = listCons A ≫ m)
    (hmc' : prodMap A (listCarrier A).dom B m' ≫ c = listCons A ≫ m') :
    m = m' := by
  have hEm : eqMap m m' ≫ m = eqMap m m' ≫ m' := eqMap_eq m m'
  -- The subobject `S = (E ↪ L.dom ↪ W)`, `E := eqObj m m'`.
  have hSmono : Monic (eqMap m m' ≫ (listCarrier A).arr) :=
    mono_comp'' (eqMap_mono m m') (listCarrier A).monic
  let S : Subobject 𝒞 (wordObj A) := ⟨eqObj m m', eqMap m m' ≫ (listCarrier A).arr, hSmono⟩
  -- (1) `S` allows `nilMor`: `listNil` factors through `E` (both legs equal `e`).
  have hnilE : listNil A ≫ m = listNil A ≫ m' := by rw [hm0, hm0']
  have hSallows : Allows S (nilMor A) := by
    refine ⟨eqLift m m' (listNil A) hnilE, ?_⟩
    show eqLift m m' (listNil A) hnilE ≫ (eqMap m m' ≫ (listCarrier A).arr) = nilMor A
    rw [← Cat.assoc, eqLift_fac, listNil_arr]
  -- (2) `S` is `(consMor, snd)`-stable.  Build the restriction `consS : A × E → E`.
  -- `cons` on `E`: take the pair into `L.dom`, then `listCons`; it stays in `E` by the squares.
  have hagree : (prodMap A (eqObj m m') (listCarrier A).dom (eqMap m m') ≫ listCons A) ≫ m
      = (prodMap A (eqObj m m') (listCarrier A).dom (eqMap m m') ≫ listCons A) ≫ m' := by
    rw [Cat.assoc, Cat.assoc, ← hmc, ← hmc', ← Cat.assoc, ← Cat.assoc,
        ← prodMap_comp, ← prodMap_comp, hEm]
  let consS : prod A (eqObj m m') ⟶ eqObj m m' :=
    eqLift m m' (prodMap A (eqObj m m') (listCarrier A).dom (eqMap m m') ≫ listCons A) hagree
  have hconsS : consS ≫ eqMap m m'
      = prodMap A (eqObj m m') (listCarrier A).dom (eqMap m m') ≫ listCons A := eqLift_fac _ _ _ _
  have hSstab : (InverseImage (snd (A := A) (B := wordObj A)) S).le (InverseImage (consMor A) S) := by
    refine actStable_of_restrict (consMor A) S consS ?_
    show consS ≫ (eqMap m m' ≫ (listCarrier A).arr)
        = prodMap A (eqObj m m') (wordObj A) (eqMap m m' ≫ (listCarrier A).arr) ≫ consMor A
    rw [← Cat.assoc, hconsS, Cat.assoc, listCons_arr, ← Cat.assoc, ← prodMap_comp, prodMap_comp,
        Cat.assoc]
  -- (3) leastness: `L ≤ S`, so `L.arr` factors through `S.arr = eqMap ≫ L.arr`.
  obtain ⟨k, hk⟩ := actLeast_le (nilMor A) (consMor A) snd S hSallows hSstab
  -- `k : L.dom → E` with `k ≫ (eqMap ≫ L.arr) = L.arr`.  Since `L.arr` mono, `k ≫ eqMap = id`.
  have hkeq : k ≫ eqMap m m' = Cat.id (listCarrier A).dom := by
    apply (listCarrier A).monic
    rw [Cat.assoc]
    rw [show k ≫ eqMap m m' ≫ (listCarrier A).arr = (listCarrier A).arr from hk]
    exact (Cat.id_comp _).symm
  -- `m = (k ≫ eqMap) ≫ m = k ≫ (eqMap ≫ m) = k ≫ (eqMap ≫ m') = (k ≫ eqMap) ≫ m' = m'`.
  calc m = (k ≫ eqMap m m') ≫ m := by rw [hkeq]; exact (Cat.id_comp _).symm
    _ = k ≫ (eqMap m m' ≫ m) := by rw [Cat.assoc]
    _ = k ≫ (eqMap m m' ≫ m') := by rw [hEm]
    _ = (k ≫ eqMap m m') ≫ m' := by rw [Cat.assoc]
    _ = m' := by rw [hkeq]; exact Cat.id_comp _

/-- **NON-BOOLEAN nil/cons disjointness.**  If a word `x : X ⟶ W` is SIMULTANEOUSLY empty
    (`x = t ≫ nilMor`) and a cons (`x = q ≫ consMor`), then `X` is "empty" (any two maps out of
    `X` agree).  Proof: read both at index `0`.  `nilMor` reads `inl ⋆` (the blank) and
    `cons(a,w)` reads `inr a` (the new head), so the two injections collide over `X`; apply the
    non-boolean `coprod_inj_disjoint_elt`.  This is the `nil ∈ S` base case of single-valuedness. -/
theorem nil_cons_disjoint {X : 𝒞} (t : X ⟶ one) (q : X ⟶ prod A (wordObj A))
    (hx : t ≫ nilMor A = q ≫ consMor A) :
    ∀ {Y : 𝒞} (a b : X ⟶ Y), a = b := by
  -- read both sides at index `0`
  have hnil : pair (term X ≫ hN.zero) (t ≫ nilMor A) ≫ eval_exp hN.nno (letterObj A)
      = term X ≫ (inl : one ⟶ letterObj A) := nilMor_read A (term X ≫ hN.zero) t
  have hcons : pair (term X ≫ hN.zero) (q ≫ consMor A) ≫ eval_exp hN.nno (letterObj A)
      = q ≫ fst ≫ (inr : A ⟶ letterObj A) := by
    rw [consMor_read A (term X ≫ hN.zero) q, consBody_zero A (term X) q]
  have hcollide : term X ≫ (inl : one ⟶ letterObj A) = (q ≫ fst) ≫ (inr : A ⟶ letterObj A) := by
    rw [← hnil, hx, hcons, Cat.assoc]
  intro Y a b
  exact coprod_inj_disjoint_elt (term X) (q ≫ fst) hcollide a b

/-- **CONS INJECTIVITY.**  `consMor : A × W ⟶ W` is monic: `cons(a,w) = cons(a',w')` forces
    `(a,w) = (a',w')`.  Proof: read at index `0` recovers the head `a` (`consBody_zero`, `inr`
    monic); read at every `succ m` recovers the tail word `w` (`consBody_succ` exposes `w` at `m`,
    so the uncurried generic-index reads of `w, w'` agree and `prodMap_eval_inj` gives `w = w'`).
    This is the `cons`-step injectivity used to recover the predecessor in single-valuedness. -/
theorem consMor_mono : Monic (consMor A) := by
  intro Z g h hgh
  -- head leg: `g ≫ fst = h ≫ fst` from index-0 read.  Transport the `inr`-collision to the
  -- canonical `coprodInr` (monic) via `φ = case coprodInl coprodInr`.
  have hhead : g ≫ fst = h ≫ fst := by
    let φ : letterObj A ⟶ coprodObj one A :=
      HasBinaryCoproducts.case (coprodInl one A) (coprodInr one A)
    have hφr : (inr : A ⟶ letterObj A) ≫ φ = coprodInr one A := HasBinaryCoproducts.case_inr _ _
    have hr : ∀ k : Z ⟶ prod A (wordObj A),
        pair (term Z ≫ hN.zero) (k ≫ consMor A) ≫ eval_exp hN.nno (letterObj A)
          = k ≫ fst ≫ (inr : A ⟶ letterObj A) := fun k => by
      rw [consMor_read A (term Z ≫ hN.zero) k, consBody_zero A (term Z) k]
    have hinr : (g ≫ fst) ≫ (inr : A ⟶ letterObj A) = (h ≫ fst) ≫ (inr : A ⟶ letterObj A) := by
      rw [Cat.assoc, Cat.assoc, ← hr g, ← hr h, hgh]
    apply (coprodInr_monic one A)
    rw [← hφr, ← Cat.assoc, ← Cat.assoc, hinr, Cat.assoc, Cat.assoc]
  -- tail leg: `g ≫ snd = h ≫ snd` from succ-index reads (`prodMap_eval_inj`).
  have htail : g ≫ snd = h ≫ snd := by
    apply prodMap_eval_inj (A := hN.nno) (B := letterObj A)
    -- generic-index β-law: read of `k≫snd` at `fst` = read of `k≫consMor` at `succ∘fst`.
    have hgen : ∀ k : Z ⟶ prod A (wordObj A),
        prodMap hN.nno Z (wordObj A) (k ≫ snd) ≫ eval_exp hN.nno (letterObj A)
          = pair (fst (A := hN.nno) (B := Z) ≫ hN.succ) (snd ≫ k ≫ consMor A)
              ≫ eval_exp hN.nno (letterObj A) := by
      intro k
      have hpm : prodMap hN.nno Z (wordObj A) (k ≫ snd)
          = pair (fst (A := hN.nno) (B := Z)) (snd ≫ k ≫ snd) := by
        show pair fst (snd ≫ k ≫ snd) = _; rfl
      rw [hpm]
      have h1 := consMor_read A (fst (A := hN.nno) (B := Z) ≫ hN.succ) (snd ≫ k)
      have h2 := consBody_succ A (fst (A := hN.nno) (B := Z)) (snd ≫ k)
      -- h1 : pair (fst≫succ) ((snd≫k)≫consMor) ≫ eval = pair (fst≫succ) (snd≫k) ≫ consBody
      -- h2 : pair (fst≫succ) (snd≫k) ≫ consBody = pair fst ((snd≫k)≫snd) ≫ eval
      rw [Cat.assoc] at h1
      rw [h1, h2, ← Cat.assoc]
    rw [hgen g, hgen h, hgh]
  -- combine into `g = h` via `pair_uniq`.
  rw [show g = pair (g ≫ fst) (g ≫ snd) from (pair_uniq _ _ _ rfl rfl),
      show h = pair (h ≫ fst) (h ≫ snd) from (pair_uniq _ _ _ rfl rfl), hhead, htail]

/-! #### `fold` existence — the functional graph over `prod W B`.

  For an algebra `(B, e, c)`, the graph `G ⊆ prod W B` is the least subobject closed under the
  combined step `foldStep (a,(w,b)) = (consMor(a,w), c(a,b))` and containing `(nilMor, e)`.  Its
  `W`-projection `p := foldProj = G.arr ≫ fst` is TOTAL over `A* = listCarrier A`
  (`foldProj_total`, sorry-free) and SINGLE-VALUED; the functional graph then yields
  `fold := s ≫ G.arr ≫ snd` with its two algebra-square laws (`foldExists`). -/

open HasBinaryCoproducts in
/-- The graph step on `prod W B`: `cons` on the word leg, `c` on the value leg. -/
noncomputable def foldStep {B : 𝒞} (c : prod A B ⟶ B) :
    prod A (prod (wordObj A) B) ⟶ prod (wordObj A) B :=
  pair (pair fst (snd ≫ fst) ≫ consMor A) (pair fst (snd ≫ snd) ≫ c)

/-- The graph unit on `prod W B`: `(nilMor, e)`. -/
noncomputable def foldUnit {B : 𝒞} (e : one ⟶ B) : one ⟶ prod (wordObj A) B :=
  pair (nilMor A) e

/-- The functional graph `G ⊆ prod W B` for the fold into `(B,e,c)`. -/
noncomputable def foldGraph {B : 𝒞} (e : one ⟶ B) (c : prod A B ⟶ B) :
    Subobject 𝒞 (prod (wordObj A) B) :=
  actLeast (foldUnit A e) (foldStep A c) (snd (A := A) (B := prod (wordObj A) B))

/-- The graph's W-projection `p = G.arr ≫ fst : G.dom ⟶ W`. -/
noncomputable def foldProj {B : 𝒞} (e : one ⟶ B) (c : prod A B ⟶ B) :
    (foldGraph A e c).dom ⟶ wordObj A :=
  (foldGraph A e c).arr ≫ fst

/-- **TOTALITY of the graph projection**: `image p` allows `nilMor` and is `(consMor,snd)`-stable,
    so `A* ≤ image p` by `actLeast_le`.  Hence a value `b` exists for every word in `A*`.
    Sorry-free; mirrors the boolean recursor's totality half. -/
theorem foldProj_total {B : 𝒞} (e : one ⟶ B) (c : prod A B ⟶ B) :
    (listCarrier A).le (image (foldProj A e c)) := by
  classical
  obtain ⟨g₀, hg₀⟩ := actLeast_allows (foldUnit A e) (foldStep A c)
    (snd (A := A) (B := prod (wordObj A) B))
  have hGact : (image (prodMap A (foldGraph A e c).dom (prod (wordObj A) B)
      (foldGraph A e c).arr ≫ foldStep A c)).le (foldGraph A e c) :=
    actImg_le_of_actStable (foldStep A c) (foldGraph A e c)
      (actLeast_stable (foldUnit A e) (foldStep A c) (snd (A := A) (B := prod (wordObj A) B)))
  obtain ⟨rG, hrG⟩ := hGact
  let actG : prod A (foldGraph A e c).dom ⟶ (foldGraph A e c).dom :=
    image.lift (prodMap A (foldGraph A e c).dom (prod (wordObj A) B)
      (foldGraph A e c).arr ≫ foldStep A c) ≫ rG
  have hactG : actG ≫ (foldGraph A e c).arr
      = prodMap A (foldGraph A e c).dom (prod (wordObj A) B) (foldGraph A e c).arr
          ≫ foldStep A c := by
    show (image.lift _ ≫ rG) ≫ (foldGraph A e c).arr = _
    rw [Cat.assoc, hrG, image.lift_fac]
  have hSgFst : foldStep A c ≫ fst = pair fst (snd ≫ fst) ≫ consMor A := fst_pair _ _
  have hpt : prodMap A (foldGraph A e c).dom (wordObj A) (foldProj A e c) ≫ consMor A
      = actG ≫ foldProj A e c := by
    have hR : actG ≫ foldProj A e c
        = prodMap A (foldGraph A e c).dom (prod (wordObj A) B) (foldGraph A e c).arr
            ≫ (pair fst (snd ≫ fst) ≫ consMor A) := by
      show actG ≫ (foldGraph A e c).arr ≫ fst = _
      rw [← Cat.assoc, hactG, Cat.assoc, hSgFst]
    have hpm : prodMap A (prod (wordObj A) B) (wordObj A) fst = pair fst (snd ≫ fst) := rfl
    rw [hR]
    show prodMap A (foldGraph A e c).dom (wordObj A) ((foldGraph A e c).arr ≫ fst) ≫ consMor A = _
    rw [prodMap_comp, hpm, Cat.assoc]
  have hg₀' : g₀ ≫ (foldGraph A e c).arr = foldUnit A e := hg₀
  have hImgNil : ∃ uB : one ⟶ (image (foldProj A e c)).dom,
      uB ≫ (image (foldProj A e c)).arr = nilMor A := by
    refine ⟨g₀ ≫ image.lift (foldProj A e c), ?_⟩
    rw [Cat.assoc, image.lift_fac]
    show g₀ ≫ (foldGraph A e c).arr ≫ fst = nilMor A
    rw [← Cat.assoc, hg₀']; show pair (nilMor A) e ≫ fst = nilMor A; exact fst_pair _ _
  have hImgStab : (InverseImage (snd (A := A) (B := wordObj A)) (image (foldProj A e c))).le
      (InverseImage (consMor A) (image (foldProj A e c))) := by
    have hcov' : Cover (prodMap A (foldGraph A e c).dom (image (foldProj A e c)).dom
        (image.lift (foldProj A e c))) := prodMap_cover A (image_lift_cover (foldProj A e c))
    have hcomp : prodMap A (foldGraph A e c).dom (image (foldProj A e c)).dom
          (image.lift (foldProj A e c))
        ≫ (prodMap A (image (foldProj A e c)).dom (wordObj A) (image (foldProj A e c)).arr
            ≫ consMor A)
        = prodMap A (foldGraph A e c).dom (wordObj A) (foldProj A e c) ≫ consMor A := by
      rw [← Cat.assoc, ← prodMap_comp, image.lift_fac]
    have hle1 : (image (prodMap A (image (foldProj A e c)).dom (wordObj A)
          (image (foldProj A e c)).arr ≫ consMor A)).le
        (image (prodMap A (foldGraph A e c).dom (wordObj A) (foldProj A e c) ≫ consMor A)) := by
      have := (image_cover_comp (prodMap A (foldGraph A e c).dom (image (foldProj A e c)).dom
        (image.lift (foldProj A e c)))
        (prodMap A (image (foldProj A e c)).dom (wordObj A) (image (foldProj A e c)).arr
          ≫ consMor A) hcov').2
      rwa [hcomp] at this
    have hle2 : (image (prodMap A (foldGraph A e c).dom (wordObj A) (foldProj A e c)
        ≫ consMor A)).le (image (foldProj A e c)) := by
      rw [hpt]
      exact image_min (actG ≫ foldProj A e c) (image (foldProj A e c))
        ⟨actG ≫ image.lift (foldProj A e c), by rw [Cat.assoc, image.lift_fac]⟩
    obtain ⟨k, hk⟩ := subLe_trans' hle1 hle2
    exact actStable_of_restrict (consMor A) (image (foldProj A e c))
      (image.lift (prodMap A (image (foldProj A e c)).dom (wordObj A) (image (foldProj A e c)).arr
        ≫ consMor A) ≫ k)
      (by rw [Cat.assoc, hk, image.lift_fac])
  exact actLeast_le (nilMor A) (consMor A) snd (image (foldProj A e c)) hImgNil hImgStab

/-- Existence of the fold/recursor `A* → B` into any `1+A×(−)`-algebra `(B,e,c)`, with its two
    algebra-square laws.  The full assembly is sorry-free EXCEPT one isolated §1.989 hole:
    the cover `pCov : G.dom ↠ A*` (`image (foldProj) = A*`, both inclusions sorry-free) is
    corestricted to an iso `A* ≅ G.dom` ONCE `Monic (foldProj A e c)` holds, whence
    `fold := iso⁻¹ ≫ G.arr ≫ snd` and the two laws follow from the graph's `(foldUnit, foldStep)`-
    closure (`hpt`/`hpsnd`).  The SINGLE residual `hcore` is non-boolean single-valuedness — the
    graph is FUNCTIONAL over `A*` — which needs the absent functional-graph relation-induction
    primitive (see the comment at `hpmono`); the boolean recursors discharge it via
    `hbool`/`hcap`/`htv`, deliberately absent here. -/
theorem foldExists {B : 𝒞} (e : one ⟶ B) (c : prod A B ⟶ B) :
    ∃ f : (listCarrier A).dom ⟶ B,
      listNil A ≫ f = e ∧
      prodMap A (listCarrier A).dom B f ≫ c = listCons A ≫ f := by
  classical
  -- Abbreviations matching `foldProj_total`'s local context.
  let G : Subobject 𝒞 (prod (wordObj A) B) := foldGraph A e c
  let p : G.dom ⟶ wordObj A := foldProj A e c
  -- The graph algebra structure: unit `g₀` and act `actG`, with `g₀ ≫ G.arr = foldUnit` and
  -- `actG ≫ G.arr = prodMap.. G.arr ≫ foldStep`.  Same as in `foldProj_total`.
  obtain ⟨g₀, hg₀⟩ := actLeast_allows (foldUnit A e) (foldStep A c)
    (snd (A := A) (B := prod (wordObj A) B))
  have hGact : (image (prodMap A G.dom (prod (wordObj A) B) G.arr ≫ foldStep A c)).le G :=
    actImg_le_of_actStable (foldStep A c) G
      (actLeast_stable (foldUnit A e) (foldStep A c) (snd (A := A) (B := prod (wordObj A) B)))
  obtain ⟨rG, hrG⟩ := hGact
  let actG : prod A G.dom ⟶ G.dom :=
    image.lift (prodMap A G.dom (prod (wordObj A) B) G.arr ≫ foldStep A c) ≫ rG
  have hactG : actG ≫ G.arr = prodMap A G.dom (prod (wordObj A) B) G.arr ≫ foldStep A c := by
    show (image.lift _ ≫ rG) ≫ G.arr = _
    rw [Cat.assoc, hrG, image.lift_fac]
  -- The `(foldUnit, foldStep)` β-facts on the two legs.
  have hSgFst : foldStep A c ≫ fst = pair fst (snd ≫ fst) ≫ consMor A := fst_pair _ _
  have hSgSnd : foldStep A c ≫ snd = pair fst (snd ≫ snd) ≫ c := snd_pair _ _
  have hg₀arr : g₀ ≫ G.arr = pair (nilMor A) e := hg₀
  -- α-leg law `prodMap.. p ≫ consMor = actG ≫ p` (identical to `foldProj_total`'s `hpt`).
  have hpt : prodMap A G.dom (wordObj A) p ≫ consMor A = actG ≫ p := by
    have hR : actG ≫ p
        = prodMap A G.dom (prod (wordObj A) B) G.arr ≫ (pair fst (snd ≫ fst) ≫ consMor A) := by
      show actG ≫ G.arr ≫ fst = _
      rw [← Cat.assoc, hactG, Cat.assoc, hSgFst]
    have hpm : prodMap A (prod (wordObj A) B) (wordObj A) fst = pair fst (snd ≫ fst) := rfl
    rw [hR]
    show prodMap A G.dom (wordObj A) (G.arr ≫ fst) ≫ consMor A = _
    rw [prodMap_comp, hpm, Cat.assoc]
  -- B-leg law `prodMap.. (G.arr ≫ snd) ≫ c = actG ≫ (G.arr ≫ snd)`.
  have hpsnd : prodMap A G.dom B (G.arr ≫ snd) ≫ c = actG ≫ (G.arr ≫ snd) := by
    have hR : actG ≫ (G.arr ≫ snd)
        = prodMap A G.dom (prod (wordObj A) B) G.arr ≫ (pair fst (snd ≫ snd) ≫ c) := by
      rw [← Cat.assoc, hactG, Cat.assoc, hSgSnd]
    have hpm : prodMap A (prod (wordObj A) B) B snd = pair fst (snd ≫ snd) := rfl
    rw [hR, prodMap_comp, hpm, Cat.assoc]
  -- ─────────────────────────────────────────────────────────────────────────────
  -- (0) **G-POINT INDUCTION** ("no junk" for `actLeast`).  Any subobject `Good ⊆ G.dom` that
  --   contains the unit point `g₀` and is `actG`-closed (its `snd`-preimage ≤ its `actG`-preimage)
  --   is ENTIRE.  Proof: push `Good` to `prod W B` as the composite mono `GoodInW = Good.arr ≫ G.arr`;
  --   it allows `foldUnit` (via `g₀`) and is `(foldStep,snd)`-stable (via `actG`-closure + `hactG`),
  --   so `G ≤ GoodInW` by `actLeast_le`; with `GoodInW ≤ G` trivially, the comparison `G.dom → Good.dom`
  --   inverts `Good.arr`.  This is the elementwise route around the boolean point-split: it forces
  --   every `G`-point to factor through `Good`.  (Avoids `coprod_point_split`/`hcap`/`htv`.)
  have hGind : ∀ (Good : Subobject 𝒞 G.dom), Allows Good g₀ →
      (InverseImage (snd (A := A) (B := G.dom)) Good).le (InverseImage actG Good) →
      ∀ {Y : 𝒞} (g : Y ⟶ G.dom), Allows Good g := by
    intro Good hUnit hClosed Y g
    -- `GoodInW = Good.arr ≫ G.arr : Good.dom ↣ prod W B` (composite of two monics).
    have hGIWmono : Monic (Good.arr ≫ G.arr) := by
      intro Z u v huv
      exact Good.monic u v (G.monic _ _ (by rw [Cat.assoc, Cat.assoc, huv]))
    let GoodInW : Subobject 𝒞 (prod (wordObj A) B) := ⟨Good.dom, Good.arr ≫ G.arr, hGIWmono⟩
    -- the `actG`-restriction of `Good`: `actGood : prod A Good.dom → Good.dom`.
    have hImgGood : (image (prodMap A Good.dom G.dom Good.arr ≫ actG)).le Good :=
      actImg_le_of_actStable actG Good hClosed
    obtain ⟨rGood, hrGood⟩ := hImgGood
    let actGood : prod A Good.dom ⟶ Good.dom :=
      image.lift (prodMap A Good.dom G.dom Good.arr ≫ actG) ≫ rGood
    have hactGood : actGood ≫ Good.arr = prodMap A Good.dom G.dom Good.arr ≫ actG := by
      show (image.lift _ ≫ rGood) ≫ Good.arr = _
      rw [Cat.assoc, hrGood, image.lift_fac]
    -- `G ≤ GoodInW`: leastness, since `GoodInW` allows `foldUnit` and is `(foldStep,snd)`-stable.
    have hGleGIW : G.le GoodInW := by
      refine actLeast_le (foldUnit A e) (foldStep A c)
        (snd (A := A) (B := prod (wordObj A) B)) GoodInW ?_ ?_
      · -- `foldUnit = g₀ ≫ G.arr = (u ≫ Good.arr) ≫ G.arr` factors through `GoodInW`.
        obtain ⟨u, hu⟩ := hUnit
        refine ⟨u, ?_⟩
        show u ≫ (Good.arr ≫ G.arr) = foldUnit A e
        rw [← Cat.assoc, hu, hg₀arr]; rfl
      · -- `(foldStep,snd)`-stable via the restriction `actGood`.
        refine actStable_of_restrict (foldStep A c) GoodInW actGood ?_
        show actGood ≫ (Good.arr ≫ G.arr)
            = prodMap A Good.dom (prod (wordObj A) B) (Good.arr ≫ G.arr) ≫ foldStep A c
        rw [← Cat.assoc, hactGood, Cat.assoc, hactG, ← Cat.assoc, ← prodMap_comp]
    -- `GoodInW ≤ G` (it factors through `G.arr` by construction): comparison inverts `Good.arr`.
    obtain ⟨k, hk⟩ := hGleGIW
    -- `k : G.dom → Good.dom` with `k ≫ (Good.arr ≫ G.arr) = G.arr`, so `(k ≫ Good.arr) ≫ G.arr = G.arr`.
    have hkGood : k ≫ Good.arr = Cat.id G.dom := by
      refine G.monic (k ≫ Good.arr) (Cat.id G.dom) ?_
      rw [Cat.assoc]; show k ≫ (Good.arr ≫ G.arr) = Cat.id G.dom ≫ G.arr
      rw [hk, Cat.id_comp]
    -- every `G`-point `g` factors through `Good` via `g ≫ k`.
    exact ⟨g ≫ k, by rw [Cat.assoc, hkGood, Cat.comp_id]⟩
  -- ─────────────────────────────────────────────────────────────────────────────
  -- (I) `image p = A*`.  `A* ≤ image p` is `foldProj_total`; the reverse `image p ≤ A*` comes
  --     from `G ≤ fst#A*` (the graph lives over `A*` since `foldUnit`/`foldStep` keep the word in
  --     `A*`), via `actLeast_le`.  Together they give the cover `pCov : G.dom ↠ A*.dom`.
  have hListLeImg : (listCarrier A).le (image p) := foldProj_total A e c
  -- `B₀ := fst # A*`, the words-with-any-value subobject of `W × B`.
  let B₀ : Subobject 𝒞 (prod (wordObj A) B) := InverseImage (fst (A := wordObj A) (B := B)) (listCarrier A)
  have hGleB₀ : G.le B₀ := by
    refine actLeast_le (foldUnit A e) (foldStep A c) (snd (A := A) (B := prod (wordObj A) B)) B₀ ?_ ?_
    · -- allows `foldUnit`: `foldUnit ≫ fst = nilMor` factors through `A*.arr` (= listNil).
      let pb := HasPullbacks.has (fst (A := wordObj A) (B := B)) (listCarrier A).arr
      have hsq : foldUnit A e ≫ fst (A := wordObj A) (B := B) = listNil A ≫ (listCarrier A).arr := by
        show pair (nilMor A) e ≫ fst = _; rw [fst_pair, listNil_arr]
      refine ⟨pb.lift ⟨one, foldUnit A e, listNil A, hsq⟩, ?_⟩
      show pb.lift ⟨one, foldUnit A e, listNil A, hsq⟩ ≫ pb.cone.π₁ = foldUnit A e
      exact pb.lift_fst _
    · -- `(foldStep, snd)`-stable: restriction `B₀ → B₀` via `consMor` on the word-leg.
      let pb := HasPullbacks.has (fst (A := wordObj A) (B := B)) (listCarrier A).arr
      -- `consMor`-restriction on the underlying `A*`: `listCons : A × A* → A*`.
      -- Build `actB₀ : prod A B₀.dom → B₀.dom` landing back in `fst#A*`.
      -- Its word-leg value is `pair fst (snd≫fst) ≫ consMor` applied through `B₀.arr`, which lies
      -- in `A*` because `(snd≫fst)` of the `B₀`-points lands in `A*` (= `pb.π₂`).
      let wleg : prod A B₀.dom ⟶ wordObj A :=
        prodMap A B₀.dom (wordObj A) (B₀.arr ≫ fst) ≫ consMor A
      let aleg : prod A B₀.dom ⟶ (listCarrier A).dom :=
        prodMap A B₀.dom (listCarrier A).dom pb.cone.π₂ ≫ listCons A
      have hπ : pb.cone.π₂ ≫ (listCarrier A).arr = B₀.arr ≫ fst := pb.cone.w.symm
      have haleg_arr : aleg ≫ (listCarrier A).arr = wleg := by
        show (prodMap A B₀.dom (listCarrier A).dom pb.cone.π₂ ≫ listCons A)
            ≫ (listCarrier A).arr = wleg
        rw [Cat.assoc, listCons_arr, ← Cat.assoc, ← prodMap_comp, hπ]
      -- the value-leg: `c` on `(fst, snd≫B₀.arr≫snd)`.
      let bleg : prod A B₀.dom ⟶ B := prodMap A B₀.dom B (B₀.arr ≫ snd) ≫ c
      -- `pair wleg bleg = prodMap.. B₀.arr ≫ foldStep`.
      have hpairStep : pair wleg bleg
          = prodMap A B₀.dom (prod (wordObj A) B) B₀.arr ≫ foldStep A c := by
        refine (pair_uniq wleg bleg _ ?_ ?_).symm
        · -- `(prodMap.. ≫ foldStep) ≫ fst = prodMap.. B₀.arr ≫ (foldStep ≫ fst) = wleg`.
          rw [Cat.assoc, hSgFst]
          show prodMap A B₀.dom (prod (wordObj A) B) B₀.arr
              ≫ (pair fst (snd ≫ fst) ≫ consMor A) = wleg
          rw [← Cat.assoc]
          show (prodMap A B₀.dom (prod (wordObj A) B) B₀.arr
              ≫ prodMap A (prod (wordObj A) B) (wordObj A) fst) ≫ consMor A = wleg
          rw [← prodMap_comp]
        · rw [Cat.assoc, hSgSnd]
          show prodMap A B₀.dom (prod (wordObj A) B) B₀.arr
              ≫ (pair fst (snd ≫ snd) ≫ c) = bleg
          rw [← Cat.assoc]
          show (prodMap A B₀.dom (prod (wordObj A) B) B₀.arr
              ≫ prodMap A (prod (wordObj A) B) B snd) ≫ c = bleg
          rw [← prodMap_comp]
      have hcone : (pair wleg bleg) ≫ fst (A := wordObj A) (B := B)
          = aleg ≫ (listCarrier A).arr := by rw [fst_pair, haleg_arr]
      let actB₀ : prod A B₀.dom ⟶ B₀.dom :=
        pb.lift ⟨prod A B₀.dom, pair wleg bleg, aleg, hcone⟩
      have hactB₀ : actB₀ ≫ B₀.arr = prodMap A B₀.dom (prod (wordObj A) B) B₀.arr ≫ foldStep A c := by
        show actB₀ ≫ pb.cone.π₁ = _
        rw [pb.lift_fst]; exact hpairStep
      exact actStable_of_restrict (foldStep A c) B₀ actB₀ hactB₀
  -- `G ≤ B₀` gives `p = G.arr ≫ fst` factoring through `A*.arr`, so `image p ≤ A*`.
  have hImgLeList : (image p).le (listCarrier A) := by
    obtain ⟨k, hk⟩ := hGleB₀
    let pb := HasPullbacks.has (fst (A := wordObj A) (B := B)) (listCarrier A).arr
    refine image_min p (listCarrier A) ⟨k ≫ pb.cone.π₂, ?_⟩
    have hw : pb.cone.π₂ ≫ (listCarrier A).arr = B₀.arr ≫ fst := pb.cone.w.symm
    calc (k ≫ pb.cone.π₂) ≫ (listCarrier A).arr
        = k ≫ (pb.cone.π₂ ≫ (listCarrier A).arr) := Cat.assoc _ _ _
      _ = k ≫ (B₀.arr ≫ fst) := by rw [hw]
      _ = (k ≫ B₀.arr) ≫ fst := (Cat.assoc _ _ _).symm
      _ = G.arr ≫ fst := by rw [hk]
      _ = p := rfl
  -- Equal subobjects ⟹ the comparison `j : (image p).dom → A*.dom` is iso.
  obtain ⟨j, hj⟩ := hImgLeList
  obtain ⟨j', hj'⟩ := hListLeImg
  have hjiso : IsIso j := by
    refine ⟨j', ?_, ?_⟩
    · exact (image p).monic (j ≫ j') (Cat.id _) (by rw [Cat.assoc, hj', hj, Cat.id_comp])
    · exact (listCarrier A).monic (j' ≫ j) (Cat.id _) (by rw [Cat.assoc, hj, hj', Cat.id_comp])
  -- The corestricted projection `pCov : G.dom ↠ A*.dom`, a cover with `pCov ≫ A*.arr = p`.
  let pCov : G.dom ⟶ (listCarrier A).dom := image.lift p ≫ j
  have hpCov : pCov ≫ (listCarrier A).arr = p := by
    show (image.lift p ≫ j) ≫ (listCarrier A).arr = p
    rw [Cat.assoc, hj, image.lift_fac]
  have hpCovCover : Cover pCov := cover_comp (image_lift_cover p) (iso_cover j hjiso)
  -- ─────────────────────────────────────────────────────────────────────────────
  -- (II) SINGLE-VALUEDNESS: `p` is MONIC (§1.98(14), non-boolean).
  have hpmono : Monic p := by
    -- `q := G.arr ≫ snd : G.dom → B`, the value-leg of the graph.  `Monic p` is reduced (below,
    -- sorry-free) to this CORE §1.989 single-valuedness equation: the two kernel-pair legs of `p`
    -- agree after `q`, i.e. the graph `G` is FUNCTIONAL over `A*` (same word ⟹ same value).
    --
    -- POWER-OBJECT SINGLETON INDUCTION — NOW WIRED (non-boolean, §1.989).  The whole `Monic p`
    -- reduction below is sorry-free EXCEPT three precisely-scoped graph "no-junk" holes (see them
    -- inside `hNilSing`/`hConsSing`).  Built here SORRY-FREE:
    --   • `valG : W → Ω^B` (= `curry (swap ≫ χ_G)`), the FIBER map `w ↦ {b | (w,b)∈G}`, with the
    --     β-laws `hvalGβ` (eval of `valG`), `hGmem` (a `G`-point is in `G`), `hSingEval` (eval of a
    --     singleton name);  `hExpExt` (exponential extensionality of `W → Ω^B`).
    --   • `hFiberSingleton`: if `(w,b₀)∈G` and the `w`-fiber is single-valued, then `valG w = {b₀}`
    --     (proved by `classify_unique`: both `M₁,M₂ : B×X → Ω` classify the graph `⟨b₀,id⟩` of `b₀`).
    --   • `Sing := InverseImage valG {singletons}` with the pullback factor lemmas `hSingWit`/`hSingFac`.
    --   • `hNilSing`/`hConsSing` reduce `nil∈Sing` / `cons`-closure to `hFiberSingleton` (the cons
    --     restriction map is assembled via `actStable_of_restrict` + the pullback lift);  `(nil,e)∈G`
    --     is discharged via `g₀`.  `actLeast_le` then gives `A* ≤ Sing` (`hListLeSing`).
    --   • the `hcore` extraction:  `δ := kp₁≫p` factors through `A*` (via `pCov`), hence `Sing`, so
    --     `valG δ = {b'}`;  both kernel-pair value-legs `q_i` satisfy `eval(q_i, valG δ) = ⊤` so equal
    --     `b'` by `diag_classify_iff` — single-valuedness, i.e. `Monic p`.
    --
    -- THE THREE RESIDUAL HOLES (all the SAME missing primitive: case-split a `G`-point into a
    -- `foldUnit` point or a `foldStep` point — `actLeast`'s "no junk").  Each is a single-valuedness
    -- of one fiber:  (nil) every `G`-point over a nil word has value `e` (rule out `foldStep` via
    -- `nil_cons_disjoint`);  (cons-sv) every `G`-point over `cons(a,w)` has value `c(a, b)` where `b`
    -- is the IH fiber-value of `w` (recover the predecessor via `consMor_mono`);  (cons-mem) the
    -- cons-fiber is inhabited (`foldStep` of a `G`-point over `(w,b)`).  Closing them needs an
    -- `actLeast_le`-on-`G` induction targeting a COPRODUCT subobject of `W×B` ("blank-head ⟹ value e",
    -- glued by `distCase`), whose monicity (coproduct of disjoint monos) is the one piece of topos
    -- infrastructure absent from S1_9/S1_60/ToposDistributive.  The two NON-BOOLEAN sub-lemmas this
    -- route consumes (`nil_cons_disjoint`, `consMor_mono`, plus `coprod_inj_disjoint_elt`) are DONE.
    -- POWER-OBJECT SINGLETON INDUCTION (non-boolean, §1.989).  Classify `G ⊆ W×B`, curry over `B`
    -- to `valG : W → [B]` (the FIBER map `w ↦ {b | (w,b)∈G}`), and show the subobject `Sing ⊆ W` of
    -- words with SINGLETON fiber contains `nilMor` and is `(consMor,snd)`-closed; `actLeast_le` then
    -- gives `A* ≤ Sing`, so the fiber over any word of `A*` is a singleton, forcing single-valuedness.
    let Ω : 𝒞 := HasSubobjectClassifier.omega (𝒞 := 𝒞)
    let χG : prod (wordObj A) B ⟶ Ω := HasSubobjectClassifier.classify G.arr G.monic
    -- `valG := curry (swap ≫ χG) : W → Ω^B`, currying `χG` over the `B`-slot.
    let valG : wordObj A ⟶ Ω ^^ B := curry (prodSwap B (wordObj A) ≫ χG)
    -- β-law: evaluating `valG` at a generalized point.  `pair b (w ≫ valG) ≫ eval = pair w b ≫ χG`.
    have hvalGβ : ∀ {X : 𝒞} (w : X ⟶ wordObj A) (b : X ⟶ B),
        pair b (w ≫ valG) ≫ eval_exp B Ω = pair w b ≫ χG := by
      intro X w b
      have hfac : pair b (w ≫ valG) = pair b w ≫ prodMap B (wordObj A) (Ω ^^ B) valG := by
        refine (pair_uniq _ _ _ ?_ ?_).symm
        · rw [Cat.assoc, prodMap_fst, fst_pair]
        · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair]
      rw [hfac, Cat.assoc, curry_eval_eq, ← Cat.assoc]
      have hswap : pair b w ≫ prodSwap B (wordObj A) = pair w b := by
        refine pair_uniq w b (pair b w ≫ prodSwap B (wordObj A)) ?_ ?_
        · rw [Cat.assoc, prodSwap_fst, snd_pair]
        · rw [Cat.assoc, prodSwap_snd, fst_pair]
      rw [hswap]
    -- For a `G`-point `g`, its (word,value) lies in `G`, so the membership test is `⊤∘!`.
    have hGmem : ∀ {X : 𝒞} (g : X ⟶ G.dom),
        pair (g ≫ p) (g ≫ (G.arr ≫ snd)) ≫ χG = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      intro X g
      have hpair : pair (g ≫ p) (g ≫ (G.arr ≫ snd)) = g ≫ G.arr := by
        refine (pair_uniq _ _ _ ?_ ?_).symm
        · show (g ≫ G.arr) ≫ fst = g ≫ p; rw [Cat.assoc]; rfl
        · rw [Cat.assoc]
      rw [hpair, Cat.assoc, HasSubobjectClassifier.classify_sq, ← Cat.assoc]
      congr 1; exact term_uniq _ _
    -- Singleton eval β-law: if `σ = b' ≫ singletonMapCat B`, then `eval(b, σ) = ⊤∘!` iff `b = b'`.
    have hSingEval : ∀ {X : 𝒞} (b b' : X ⟶ B),
        pair b (b' ≫ singletonMapCat B) ≫ eval_exp B Ω
          = pair b b' ≫ HasSubobjectClassifier.classify (diag B) (diag_mono B) := by
      intro X b b'
      have hfac : pair b (b' ≫ singletonMapCat B)
          = pair b b' ≫ prodMap B B (Ω ^^ B) (singletonMapCat B) := by
        refine (pair_uniq _ _ _ ?_ ?_).symm
        · rw [Cat.assoc, prodMap_fst, fst_pair]
        · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair]
      rw [hfac, Cat.assoc]
      show pair b b' ≫ (prodMap B B (Ω ^^ B) (curry _) ≫ eval_exp B Ω) = _
      rw [curry_eval_eq]
    -- `Sg = {singletons} ⊆ Ω^B`, the image of the (monic) singleton map.
    let Sg : Subobject 𝒞 (Ω ^^ B) := ⟨B, singletonMapCat B, singletonMapCat_monic B⟩
    -- `Sing ⊆ W` = words whose fiber `valG w` is a singleton (pullback of `Sg` along `valG`).
    let Sing : Subobject 𝒞 (wordObj A) := InverseImage valG Sg
    let pbS := HasPullbacks.has valG Sg.arr
    -- factor → witness: if `f : X → W` factors through `Sing`, its fiber is `b' ≫ singletonMapCat B`.
    have hSingWit : ∀ {X : 𝒞} (f : X ⟶ wordObj A), Allows Sing f →
        ∃ b' : X ⟶ B, f ≫ valG = b' ≫ singletonMapCat B := by
      rintro X f ⟨g, hg⟩
      refine ⟨g ≫ pbS.cone.π₂, ?_⟩
      have hsq : Sing.arr ≫ valG = pbS.cone.π₂ ≫ singletonMapCat B := pbS.cone.w
      rw [← hg, Cat.assoc, hsq, ← Cat.assoc]
    -- witness → factor: a fiber of singleton form gives a lift into `Sing`.
    have hSingFac : ∀ {X : 𝒞} (f : X ⟶ wordObj A) (b' : X ⟶ B),
        f ≫ valG = b' ≫ singletonMapCat B → Allows Sing f := by
      intro X f b' hb'
      refine ⟨pbS.lift ⟨X, f, b', hb'⟩, ?_⟩
      show pbS.lift ⟨X, f, b', hb'⟩ ≫ pbS.cone.π₁ = f
      exact pbS.lift_fst _
    -- Exponential extensionality: two `X → Ω^B` agree iff they agree after `prodMap.. ≫ eval`.
    have hExpExt : ∀ {X : 𝒞} (σ₁ σ₂ : X ⟶ Ω ^^ B),
        prodMap B X (Ω ^^ B) σ₁ ≫ eval_exp B Ω = prodMap B X (Ω ^^ B) σ₂ ≫ eval_exp B Ω →
        σ₁ = σ₂ := by
      intro X σ₁ σ₂ h
      rw [curry_unique_eq h, ← curry_unique_eq (f := prodMap B X (Ω ^^ B) σ₂ ≫ eval_exp B Ω) rfl]
    -- **Singleton ⟹ membership.**  If `valG w = {b₀}` then `(w,b₀) ∈ G` (the singleton's element
    -- is in the fiber): `pair w b₀ ≫ χG = pair b₀ (w≫valG) ≫ eval = pair b₀ b₀ ≫ χ_Δ = ⊤` (refl).
    have hMemOfSing : ∀ {X : 𝒞} (w : X ⟶ wordObj A) (b₀ : X ⟶ B),
        w ≫ valG = b₀ ≫ singletonMapCat B →
        pair w b₀ ≫ χG = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      intro X w b₀ hsing
      rw [← hvalGβ w b₀, hsing, hSingEval b₀ b₀, (diag_classify_iff b₀ b₀).2 rfl]
    -- **Membership ⟹ G-point.**  `(w,b₀) ∈ G` lifts to an actual `G`-point `gp : X → G.dom`
    -- with `gp ≫ p = w` and `gp ≫ (G.arr ≫ snd) = b₀` (classifier pullback of `G.arr`).
    have hGpointOfMem : ∀ {X : 𝒞} (w : X ⟶ wordObj A) (b₀ : X ⟶ B),
        pair w b₀ ≫ χG = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) →
        ∃ gp : X ⟶ G.dom, gp ≫ p = w ∧ gp ≫ (G.arr ≫ snd) = b₀ := by
      intro X w b₀ hmem
      obtain ⟨gp, ⟨hgp₁, _⟩, _⟩ :=
        HasSubobjectClassifier.classify_pullback G.arr G.monic ⟨X, pair w b₀, term X, hmem⟩
      refine ⟨gp, ?_, ?_⟩
      · show gp ≫ G.arr ≫ fst = w; rw [← Cat.assoc, hgp₁, fst_pair]
      · rw [← Cat.assoc, hgp₁, snd_pair]
    -- **Antecedent ⟹ consequent (via G-point induction + Heyting ⇒-adjunction).**  For subobjects
    -- `Anil, Ce ⊆ G.dom`, if the unit point `g₀ ∈ Ce` and the act-image overlap `Anil ⊓ image(actG)`
    -- already lies in `Ce`, then `Anil ≤ Ce`.  Proof: `Det := (Anil ⇒ Ce)` contains `g₀` (since
    -- `Ce ≤ Det`) and is `actG`-closed (since `image(actG) ≤ Det` by `imp_adjunction` on the overlap
    -- hypothesis), so `hGind` makes `Det` swallow every `G`-point — in particular `Anil ≤ Det`,
    -- whence `Anil ≤ Ce` by `imp_adjunction` (X = Anil).  This is the no-junk single-valuedness engine.
    have hAntToVal : ∀ (Anil Ce : Subobject 𝒞 G.dom)
        (hp : HasPullback Anil.arr (image actG).arr),
        Allows Ce g₀ → (Sub.inter Anil (image actG) hp).le Ce → Anil.le Ce := by
      intro Anil Ce hp hUnitCe hOverlap
      let Det : Subobject 𝒞 G.dom := Sub.imp Anil Ce
      -- `Ce ≤ Det`  (`T ≤ (S ⇒ T)`, via `imp_adjunction`: `S ⊓ Ce ≤ Ce`).
      have hCeDet : Ce.le Det :=
        (imp_adjunction Anil Ce Ce (HasPullbacks.has Anil.arr Ce.arr)).2
          (Sub.inter_le_right Anil Ce _)
      -- `image(actG) ≤ Det`  (`imp_adjunction`: `Anil ⊓ image(actG) ≤ Ce`).
      have hImgActDet : (image actG).le Det :=
        (imp_adjunction Anil Ce (image actG) hp).2 hOverlap
      -- `g₀ ∈ Det`  (via `Ce ≤ Det`).
      have hUnitDet : Allows Det g₀ := allows_mono hCeDet hUnitCe
      -- `actG` factors through `Det`  (`image(actG)` allows `actG`, composed with `image(actG) ≤ Det`).
      have hActDet : Allows Det actG :=
        allows_mono hImgActDet ⟨image.lift actG, image.lift_fac actG⟩
      -- `actG`-closure of `Det`:  `(snd # Det) ≤ (actG # Det)` via the restriction `(snd#Det).arr ≫ s`.
      have hClosedDet : (InverseImage (snd (A := A) (B := G.dom)) Det).le (InverseImage actG Det) := by
        rw [invImage_le_iff_restrict]
        obtain ⟨s, hs⟩ := hActDet
        exact ⟨(InverseImage (snd (A := A) (B := G.dom)) Det).arr ≫ s, by rw [Cat.assoc, hs]⟩
      -- `Det` swallows the `Anil`-inclusion ⟹ `Anil ≤ Det`.
      have hAnilDet : Anil.le Det := hGind Det hUnitDet hClosedDet Anil.arr
      -- `Anil ≤ Det = (Anil ⇒ Ce)` ⟹ `Anil ⊓ Anil ≤ Ce` (imp_adjunction) ⟹ `Anil ≤ Ce`.
      have hInterCe : (Sub.inter Anil Anil (HasPullbacks.has Anil.arr Anil.arr)).le Ce :=
        (imp_adjunction Anil Ce Anil (HasPullbacks.has Anil.arr Anil.arr)).1 hAnilDet
      have hrefl : Anil.le Anil := ⟨Cat.id Anil.dom, Cat.id_comp _⟩
      exact subLe_trans
        (Sub.inter_glb Anil Anil Anil (HasPullbacks.has Anil.arr Anil.arr) hrefl hrefl)
        hInterCe
    -- **act-preimage variant of the single-valuedness engine.**  Same conclusion `Anil ≤ Ce`, but
    -- the closure obligation is phrased over `prod A G.dom` as `(actG # Anil) ≤ (actG # Ce)` — i.e.
    -- act-points (foldStep) over the antecedent already satisfy the consequent.  This admits the
    -- predecessor recovery (`consMor_mono` + IH) that the cons step needs, which the `image actG`
    -- overlap cannot express.  `Allows Det actG` is obtained via the classifier bridge: `actG ≫ χ_{S⇒T}`
    -- reduces (`mem_imp_iff`) to `χ_{actG#Anil} = χ_{actG#Anil ⊓ actG#Ce}`, which holds since
    -- `actG#Anil ≤ actG#Ce` (`classify_eq_of_le_le` + `omegaMeet_classifies_inter`).
    have hAntToVal2 : ∀ (Anil Ce : Subobject 𝒞 G.dom),
        Allows Ce g₀ →
        (InverseImage actG Anil).le (InverseImage actG Ce) → Anil.le Ce := by
      intro Anil Ce hUnitCe hClosurePre
      let Det : Subobject 𝒞 G.dom := Sub.imp Anil Ce
      have hCeDet : Ce.le Det :=
        (imp_adjunction Anil Ce Ce (HasPullbacks.has Anil.arr Ce.arr)).2
          (Sub.inter_le_right Anil Ce _)
      have hUnitDet : Allows Det g₀ := allows_mono hCeDet hUnitCe
      -- `Allows Det actG` via the classifier bridge.
      have hActDet : Allows Det actG := by
        rw [allows_iff_classify]
        -- `subChar(Sub.imp Anil Ce) = classify (Sub.imp..).arr (..).monic` (defeq of `subChar`).
        rw [show HasSubobjectClassifier.classify Det.arr Det.monic = subChar (Sub.imp Anil Ce) from rfl,
            mem_imp_iff Anil Ce actG]
        -- goal: `actG ≫ χ_Anil = actG ≫ (⟨χ_Anil,χ_Ce⟩ ≫ omegaMeet)`.
        let SA := InverseImage actG Anil
        let SC := InverseImage actG Ce
        let hpAC : HasPullback SA.arr SC.arr := HasPullbacks.has SA.arr SC.arr
        -- `actG ≫ χ_Anil = χ_{SA}`, `actG ≫ χ_Ce = χ_{SC}` (classify_InverseImage).
        have hA : actG ≫ subChar Anil = subChar SA := (classify_InverseImage actG Anil).symm
        have hC : actG ≫ subChar Ce = subChar SC := (classify_InverseImage actG Ce).symm
        -- `actG ≫ (⟨χ_Anil,χ_Ce⟩∧) = ⟨χ_{SA},χ_{SC}⟩∧ = χ_{SA ⊓ SC}`.
        have hMeet : actG ≫ (pair (subChar Anil) (subChar Ce) ≫ omegaMeet)
            = subChar (Sub.inter SA SC hpAC) := by
          rw [← Cat.assoc]
          have hp2 : actG ≫ pair (subChar Anil) (subChar Ce)
              = pair (subChar SA) (subChar SC) := by
            refine pair_uniq _ _ _ ?_ ?_
            · rw [Cat.assoc, fst_pair, hA]
            · rw [Cat.assoc, snd_pair, hC]
          rw [hp2]; exact omegaMeet_classifies_inter SA SC hpAC
        -- `SA ≤ SC` ⟹ `SA = SA ⊓ SC` ⟹ classifiers agree.
        have hSAeq : subChar SA = subChar (Sub.inter SA SC hpAC) := by
          refine classify_eq_of_le_le ?_ (Sub.inter_le_left SA SC hpAC)
          have hreflA : SA.le SA := ⟨Cat.id SA.dom, Cat.id_comp _⟩
          exact Sub.inter_glb SA SC SA hpAC hreflA hClosurePre
        rw [hA, hMeet, hSAeq]
      have hClosedDet : (InverseImage (snd (A := A) (B := G.dom)) Det).le (InverseImage actG Det) := by
        rw [invImage_le_iff_restrict]
        obtain ⟨s, hs⟩ := hActDet
        exact ⟨(InverseImage (snd (A := A) (B := G.dom)) Det).arr ≫ s, by rw [Cat.assoc, hs]⟩
      have hAnilDet : Anil.le Det := hGind Det hUnitDet hClosedDet Anil.arr
      have hInterCe : (Sub.inter Anil Anil (HasPullbacks.has Anil.arr Anil.arr)).le Ce :=
        (imp_adjunction Anil Ce Anil (HasPullbacks.has Anil.arr Anil.arr)).1 hAnilDet
      have hrefl : Anil.le Anil := ⟨Cat.id Anil.dom, Cat.id_comp _⟩
      exact subLe_trans
        (Sub.inter_glb Anil Anil Anil (HasPullbacks.has Anil.arr Anil.arr) hrefl hrefl)
        hInterCe
    -- **Fiber-singleton criterion.**  If `(w,b₀)∈G` and the `w`-fiber of `G` is single-valued
    -- (every `G`-point over `w` has value `b₀`), then `valG w = {b₀}`, i.e. `w ≫ valG` factors
    -- through the singleton map at `b₀`.  Proof: `hExpExt` reduces to a classifier equation on
    -- `prod B X → Ω`; both sides classify the GRAPH `γ = ⟨b₀,id⟩` of `b₀`, via `classify_unique`.
    have hFiberSingleton : ∀ {X : 𝒞} (w : X ⟶ wordObj A) (b₀ : X ⟶ B),
        (∀ {Y : 𝒞} (g : Y ⟶ G.dom) (y : Y ⟶ X), g ≫ p = y ≫ w → g ≫ (G.arr ≫ snd) = y ≫ b₀) →
        pair w b₀ ≫ χG = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) →
        w ≫ valG = b₀ ≫ singletonMapCat B := by
      intro X w b₀ hSV hmem
      -- graph mono `γ = ⟨b₀, id⟩ : X → B × X` (monic; `γ ≫ snd = id`).
      let γ : X ⟶ prod B X := pair b₀ (Cat.id X)
      have hγsnd : γ ≫ snd = Cat.id X := snd_pair _ _
      have hγfst : γ ≫ fst = b₀ := fst_pair _ _
      have hγmono : Monic γ := mono_of_retraction γ snd hγsnd
      -- `M₁ := ⟨snd≫w, fst⟩ ≫ χG`  and  `M₂ := prodMap B X B b₀ ≫ χ_Δ`, both `prod B X → Ω`.
      let M₁ : prod B X ⟶ Ω := pair (snd ≫ w) fst ≫ χG
      let M₂ : prod B X ⟶ Ω :=
        prodMap B X B b₀ ≫ HasSubobjectClassifier.classify (diag B) (diag_mono B)
      -- `γ ≫ M₁ = term ≫ true` (the point `(b₀ x, x)` maps to `(w x, b₀ x) ∈ G`).
      have hγpair : γ ≫ pair (snd ≫ w) (fst (A := B) (B := X)) = pair w b₀ := by
        refine pair_uniq w b₀ (γ ≫ pair (snd ≫ w) (fst (A := B) (B := X))) ?_ ?_
        · rw [Cat.assoc, fst_pair, ← Cat.assoc, hγsnd, Cat.id_comp]
        · rw [Cat.assoc, snd_pair, hγfst]
      have hsq₁ : γ ≫ M₁ = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
        show γ ≫ pair (snd ≫ w) fst ≫ χG = _
        rw [← Cat.assoc, hγpair, hmem]
      -- `γ ≫ M₂ = term ≫ true` (diagonal: `b₀ = b₀`).
      have hsq₂ : γ ≫ M₂ = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
        show γ ≫ prodMap B X B b₀ ≫ HasSubobjectClassifier.classify (diag B) (diag_mono B) = _
        have hγpm : γ ≫ prodMap B X B b₀ = b₀ ≫ diag B := by
          have hlhs : γ ≫ prodMap B X B b₀ = pair b₀ b₀ := by
            refine pair_uniq b₀ b₀ (γ ≫ prodMap B X B b₀) ?_ ?_
            · rw [Cat.assoc, prodMap_fst, hγfst]
            · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, hγsnd, Cat.id_comp]
          have hrhs : b₀ ≫ diag B = pair b₀ b₀ := by
            refine pair_uniq b₀ b₀ (b₀ ≫ diag B) ?_ ?_
            · rw [Cat.assoc, diag_fst, Cat.comp_id]
            · rw [Cat.assoc, diag_snd, Cat.comp_id]
          rw [hlhs, hrhs]
        rw [← Cat.assoc, hγpm, Cat.assoc, HasSubobjectClassifier.classify_sq, ← Cat.assoc]
        congr 1; exact term_uniq _ _
      -- `M₁` makes `γ` the pullback of `true`: universality uses single-valuedness `hSV`.
      have hPB₁ : (Cone.mk (f := M₁) (g := HasSubobjectClassifier.true (𝒞 := 𝒞))
          (pt := X) (π₁ := γ) (π₂ := term X) (w := hsq₁)).IsPullback := by
        intro d
        let db : d.pt ⟶ B := d.π₁ ≫ fst
        let dx : d.pt ⟶ X := d.π₁ ≫ snd
        -- the test cone says `(dx ≫ w, db) ∈ G`.
        have hdmem : pair (dx ≫ w) db ≫ χG = term d.pt ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
          have hd : d.π₁ ≫ pair (snd ≫ w) (fst (A := B) (B := X)) = pair (dx ≫ w) db := by
            refine pair_uniq (dx ≫ w) db (d.π₁ ≫ pair (snd ≫ w) (fst (A := B) (B := X))) ?_ ?_
            · rw [Cat.assoc, fst_pair, Cat.assoc]
            · rw [Cat.assoc, snd_pair]
          have hdw : d.π₁ ≫ M₁ = term d.pt ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
            rw [d.w]; congr 1; exact term_uniq _ _
          calc pair (dx ≫ w) db ≫ χG
              = (d.π₁ ≫ pair (snd ≫ w) fst) ≫ χG := by rw [hd]
            _ = d.π₁ ≫ M₁ := by rw [Cat.assoc]
            _ = term d.pt ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := hdw
        -- lift `(dx ≫ w, db)` through `G.arr` (pullback of `true` along `χG = classify G.arr`).
        obtain ⟨gp, ⟨hgp₁, _⟩, _⟩ :=
          HasSubobjectClassifier.classify_pullback G.arr G.monic
            ⟨d.pt, pair (dx ≫ w) db, term d.pt, hdmem⟩
        -- single-valuedness: `gp`'s value is `dx ≫ b₀`, hence `db = dx ≫ b₀`.
        have hgpp : gp ≫ p = dx ≫ w := by
          show gp ≫ G.arr ≫ fst = dx ≫ w
          rw [← Cat.assoc, hgp₁, fst_pair]
        have hgpv : gp ≫ (G.arr ≫ snd) = db := by
          rw [← Cat.assoc, hgp₁, snd_pair]
        have hdb : db = dx ≫ b₀ := by rw [← hgpv]; exact hSV gp dx hgpp
        -- the lift into `X` is `dx`; `dx ≫ γ = d.π₁` since `db = dx ≫ b₀`.
        refine ⟨dx, ⟨?_, term_uniq _ _⟩, ?_⟩
        · show dx ≫ γ = d.π₁
          refine (pair_uniq (d.π₁ ≫ fst) (d.π₁ ≫ snd) _ ?_ ?_).trans
            (pair_uniq (d.π₁ ≫ fst) (d.π₁ ≫ snd) d.π₁ rfl rfl).symm
          · rw [Cat.assoc, hγfst]; exact hdb.symm
          · rw [Cat.assoc, hγsnd, Cat.comp_id]
        · intro v hv₁ _
          have : v ≫ γ ≫ snd = d.π₁ ≫ snd := by rw [← Cat.assoc, hv₁]
          rw [hγsnd, Cat.comp_id] at this; exact this
      -- `M₂` makes `γ` the pullback of `true`: paste `prodMap`-square with the diagonal classifier.
      have hPB₂ : (Cone.mk (f := M₂) (g := HasSubobjectClassifier.true (𝒞 := 𝒞))
          (pt := X) (π₁ := γ) (π₂ := term X) (w := hsq₂)).IsPullback := by
        intro d
        have hsqd : (d.π₁ ≫ prodMap B X B b₀)
            ≫ HasSubobjectClassifier.classify (diag B) (diag_mono B) = d.π₂ ≫ HasSubobjectClassifier.true := by
          rw [Cat.assoc]; exact d.w
        obtain ⟨ℓ, ⟨hℓ₁, _⟩, _⟩ :=
          HasSubobjectClassifier.classify_pullback (diag B) (diag_mono B)
            ⟨d.pt, d.π₁ ≫ prodMap B X B b₀, d.π₂, hsqd⟩
        have hfst : d.π₁ ≫ fst = ℓ := by
          have := congrArg (· ≫ fst) hℓ₁
          simp only [Cat.assoc, diag_fst, Cat.comp_id, prodMap_fst] at this; exact this.symm
        have hsnd : d.π₁ ≫ snd ≫ b₀ = ℓ := by
          have := congrArg (· ≫ snd) hℓ₁
          simp only [Cat.assoc, diag_snd, Cat.comp_id, prodMap_snd] at this; exact this.symm
        have hkey : d.π₁ ≫ snd ≫ b₀ = d.π₁ ≫ fst := by rw [hsnd, hfst]
        refine ⟨d.π₁ ≫ snd, ⟨?_, term_uniq _ _⟩, ?_⟩
        · have hA : ((d.π₁ ≫ snd) ≫ γ) ≫ fst = d.π₁ ≫ fst := by
            rw [Cat.assoc, hγfst, Cat.assoc, hkey]
          have hB : ((d.π₁ ≫ snd) ≫ γ) ≫ snd = d.π₁ ≫ snd := by
            rw [Cat.assoc, hγsnd, Cat.comp_id]
          exact (pair_uniq (d.π₁ ≫ fst) (d.π₁ ≫ snd) _ hA hB).trans
            (pair_uniq (d.π₁ ≫ fst) (d.π₁ ≫ snd) d.π₁ rfl rfl).symm
        · intro v hv₁ _
          have hvs : v ≫ γ ≫ snd = v := by rw [hγsnd]; exact Cat.comp_id v
          have hproj : (v ≫ γ) ≫ snd = d.π₁ ≫ snd := congrArg (· ≫ snd) hv₁
          exact hvs.symm.trans ((Cat.assoc v γ snd).symm.trans hproj)
      -- both classify `γ`, hence `M₁ = M₂`; `hExpExt` lifts to `w ≫ valG = b₀ ≫ singletonMapCat`.
      have hM : M₁ = M₂ := by
        rw [HasSubobjectClassifier.classify_unique γ hγmono M₁ hsq₁ hPB₁,
            HasSubobjectClassifier.classify_unique γ hγmono M₂ hsq₂ hPB₂]
      apply hExpExt
      -- `prodMap B X (Ω^B) (w ≫ valG) ≫ eval = M₁ = M₂ = prodMap B X (Ω^B) (b₀ ≫ sing) ≫ eval`.
      have hL : prodMap B X (Ω ^^ B) (w ≫ valG) ≫ eval_exp B Ω = M₁ := by
        show pair fst (snd ≫ w ≫ valG) ≫ eval_exp B Ω = M₁
        have := hvalGβ (snd ≫ w) (fst (A := B) (B := X))
        rw [Cat.assoc] at this
        rw [this]
      have hR : prodMap B X (Ω ^^ B) (b₀ ≫ singletonMapCat B) ≫ eval_exp B Ω = M₂ := by
        show pair fst (snd ≫ b₀ ≫ singletonMapCat B) ≫ eval_exp B Ω = M₂
        have := hSingEval (fst (A := B) (B := X)) (snd ≫ b₀)
        rw [Cat.assoc] at this
        rw [this]; rfl
      rw [hL, hR, hM]
    -- (A) `nilMor ∈ Sing`: the fiber over `nil` is `{e}` (any `(nil,b)∈G` forces `b=e`).
    have hNilSing : Allows Sing (nilMor A) := by
      -- the nil-fiber is `{e}`: `(nil,e)∈G` via `g₀`, single-valued via `nil_cons_disjoint`.
      refine hSingFac (nilMor A) e (hFiberSingleton (nilMor A) e ?_ ?_)
      · -- nil-fiber single-valuedness: any `G`-point over a nil word has value `e`.
        intro Y g y hgw
        -- `Anil ⊆ G.dom` = points whose word is a nil word (`p` ∈ `image nilMor`);
        -- `Ce ⊆ G.dom` = points whose value is `e` (equalizer of `q` and `term ≫ e`).
        let q : G.dom ⟶ B := G.arr ≫ snd
        -- `nilMor` is monic (any two maps to terminal `one` agree), so `NilW := ⟨one, nilMor⟩`
        -- has LITERAL `t ≫ nilMor` points (no image-cover lift needed).
        have hNilMono : Monic (nilMor A) := by
          intro Z u v _; exact term_uniq u v
        let NilW : Subobject 𝒞 (wordObj A) := ⟨one, nilMor A, hNilMono⟩
        let Anil : Subobject 𝒞 G.dom := InverseImage p NilW
        -- the `Anil` pullback square: `Anil.arr ≫ p = pNil ≫ nilMor` (`pNil : Anil.dom → one`).
        let pNil : Anil.dom ⟶ one := (HasPullbacks.has p NilW.arr).cone.π₂
        have hpNil : Anil.arr ≫ p = pNil ≫ nilMor A := (HasPullbacks.has p NilW.arr).cone.w
        have hCe_mono : Monic (eqMap q (term G.dom ≫ e)) := eqMap_mono q (term G.dom ≫ e)
        let Ce : Subobject 𝒞 G.dom := ⟨eqObj q (term G.dom ≫ e), eqMap q (term G.dom ≫ e), hCe_mono⟩
        -- membership-in-`Ce` criterion:  `f` allows `Ce` iff `f ≫ q = f ≫ term ≫ e`.
        have hCeFac : ∀ {Z : 𝒞} (f : Z ⟶ G.dom), f ≫ q = (f ≫ term G.dom) ≫ e → Allows Ce f := by
          intro Z f hf
          have hf' : f ≫ q = f ≫ (term G.dom ≫ e) := by rw [hf, Cat.assoc]
          exact ⟨eqLift q (term G.dom ≫ e) f hf', eqLift_fac q (term G.dom ≫ e) f hf'⟩
        -- `(nil, e) ∈ Ce`: the unit point `g₀` has value `e`.
        have hUnitCe : Allows Ce g₀ := by
          refine hCeFac g₀ ?_
          show g₀ ≫ (G.arr ≫ snd) = (g₀ ≫ term G.dom) ≫ e
          rw [← Cat.assoc, hg₀arr, snd_pair,
              term_uniq (g₀ ≫ term G.dom) (Cat.id one), Cat.id_comp]
        -- overlap `Anil ⊓ image(actG) ≤ Ce`:  an act-point over a nil word is impossible
        -- (`nil_cons_disjoint`), so the apex collapses and the `Ce`-equation holds vacuously.
        -- `Acons ⊆ G.dom` = points whose word is a cons word (`consMor` monic; `actG ≫ p` is a cons).
        let ConsW : Subobject 𝒞 (wordObj A) := ⟨prod A (wordObj A), consMor A, consMor_mono A⟩
        let Acons : Subobject 𝒞 G.dom := InverseImage p ConsW
        let pCons : Acons.dom ⟶ prod A (wordObj A) := (HasPullbacks.has p ConsW.arr).cone.π₂
        have hpCons : Acons.arr ≫ p = pCons ≫ consMor A := (HasPullbacks.has p ConsW.arr).cone.w
        have hActCons : Allows Acons actG := by
          let pbC := HasPullbacks.has p ConsW.arr
          have hsq : actG ≫ p = (prodMap A G.dom (wordObj A) p) ≫ ConsW.arr := by
            rw [← hpt]
          exact ⟨pbC.lift ⟨_, actG, prodMap A G.dom (wordObj A) p, hsq⟩, pbC.lift_fst _⟩
        have hImgActCons : (image actG).le Acons := image_min actG Acons hActCons
        have hOverlap : (Sub.inter Anil (image actG)
            (HasPullbacks.has Anil.arr (image actG).arr)).le Ce := by
          let I := Sub.inter Anil (image actG) (HasPullbacks.has Anil.arr (image actG).arr)
          refine hCeFac I.arr ?_
          -- `I.arr` factors through `Anil` (nil word) and through `Acons` (cons word, via `image actG`).
          obtain ⟨kA, hkA⟩ := Sub.inter_le_left Anil (image actG) _
          obtain ⟨kC, hkC⟩ := subLe_trans (Sub.inter_le_right Anil (image actG) _) hImgActCons
          -- nil word `tN : I.dom → one`, cons predecessor `qC : I.dom → prod A W`.
          let tN : I.dom ⟶ one := kA ≫ pNil
          let qC : I.dom ⟶ prod A (wordObj A) := kC ≫ pCons
          have hnil : I.arr ≫ p = tN ≫ nilMor A := by
            show I.arr ≫ p = (kA ≫ pNil) ≫ nilMor A
            rw [← hkA, Cat.assoc, Cat.assoc, hpNil]
          have hcons : I.arr ≫ p = qC ≫ consMor A := by
            show I.arr ≫ p = (kC ≫ pCons) ≫ consMor A
            rw [← hkC, Cat.assoc, Cat.assoc, hpCons]
          exact nil_cons_disjoint A tN qC (by rw [← hnil, hcons])
            (I.arr ≫ q) ((I.arr ≫ term G.dom) ≫ e)
        -- `Anil ≤ Ce`, then specialize to `g` (its word `= y ≫ nilMor` is a nil word).
        have hAnilCe : Anil.le Ce := hAntToVal Anil Ce _ hUnitCe hOverlap
        -- `g ∈ Anil`:  `g ≫ p = y ≫ nilMor = y ≫ NilW.arr`.
        have hgAnil : Allows Anil g := by
          let pbN := HasPullbacks.has p NilW.arr
          have hsq : g ≫ p = y ≫ NilW.arr := hgw
          exact ⟨pbN.lift ⟨Y, g, y, hsq⟩, pbN.lift_fst _⟩
        -- `g ∈ Ce`:  value `= (g ≫ term) ≫ e = y ≫ e`.
        obtain ⟨gc, hgc⟩ := allows_mono hAnilCe hgAnil
        -- `hgc : gc ≫ eqMap q (term≫e) = g`.  `eqMap_eq` gives `g ≫ q = g ≫ (term≫e)`.
        have hval : g ≫ q = g ≫ (term G.dom ≫ e) := by
          calc g ≫ q = (gc ≫ eqMap q (term G.dom ≫ e)) ≫ q := by rw [hgc]
            _ = gc ≫ (eqMap q (term G.dom ≫ e) ≫ q) := Cat.assoc _ _ _
            _ = gc ≫ (eqMap q (term G.dom ≫ e) ≫ (term G.dom ≫ e)) := by
                  rw [eqMap_eq q (term G.dom ≫ e)]
            _ = (gc ≫ eqMap q (term G.dom ≫ e)) ≫ (term G.dom ≫ e) := (Cat.assoc _ _ _).symm
            _ = g ≫ (term G.dom ≫ e) := by rw [hgc]
        show g ≫ (G.arr ≫ snd) = y ≫ e
        calc g ≫ (G.arr ≫ snd) = g ≫ q := rfl
          _ = g ≫ (term G.dom ≫ e) := hval
          _ = (g ≫ term G.dom) ≫ e := (Cat.assoc _ _ _).symm
          _ = y ≫ e := by rw [term_uniq (g ≫ term G.dom) y]
      · -- `(nil, e) ∈ G`: witnessed by the unit point `g₀` (`g₀ ≫ G.arr = pair nilMor e`).
        have hg₀p : g₀ ≫ p = nilMor A := by
          show g₀ ≫ G.arr ≫ fst = nilMor A; rw [← Cat.assoc, hg₀arr, fst_pair]
        have hg₀v : g₀ ≫ (G.arr ≫ snd) = e := by rw [← Cat.assoc, hg₀arr, snd_pair]
        have hm := hGmem g₀
        rw [hg₀p, hg₀v] at hm
        exact hm
    -- (B) `Sing` is `(consMor,snd)`-closed: the fiber over `cons(a,w)` is `{c(a,b)}`.
    have hConsSing : (InverseImage (snd (A := A) (B := wordObj A)) Sing).le
        (InverseImage (consMor A) Sing) := by
      -- the fiber value over `Sing` is `bSing := pbS.cone.π₂ : Sing.dom → B` (`Sing.arr ≫ valG =
      -- bSing ≫ singletonMapCat`).  The cons-word `consMor(a, Sing.arr s)` has fiber `{c(a, bSing s)}`.
      let bSing : Sing.dom ⟶ B := pbS.cone.π₂
      have hbSing : Sing.arr ≫ valG = bSing ≫ singletonMapCat B := pbS.cone.w
      -- cons-word and its candidate value as maps out of `prod A Sing.dom`.
      let wc : prod A Sing.dom ⟶ wordObj A :=
        prodMap A Sing.dom (wordObj A) Sing.arr ≫ consMor A
      let bc : prod A Sing.dom ⟶ B := prodMap A Sing.dom B bSing ≫ c
      -- `cons(a,w) ≫ valG = c(a,b) ≫ singletonMapCat B`: the cons-fiber is the singleton `{c(a,b)}`.
      have hwcSing : wc ≫ valG = bc ≫ singletonMapCat B := by
        refine hFiberSingleton wc bc ?_ ?_
        · -- cons-fiber single-valuedness via NO-JUNK ACT DECOMPOSITION (no `vw`/equalizer needed).
          -- The arbitrary `G`-point `g` over a cons word `yy ≫ wc = cons(a, Sing.arr s)` factors
          -- through `image actG` (every point over a cons word is an act — `hConsImg` below, the
          -- `imp`-engine with VACUOUS nil-overlap).  Pull back the cover `image.lift actG` to recover a
          -- genuine source point `s : P → prod A G.dom` (over a cover `π₂ : P ↠ Y`) with `s ≫ actG =
          -- π₂ ≫ g`.  Then `g`'s value `= c(a, predecessor.value)` (`hpsnd`), the predecessor lies over
          -- the `Sing` tail (`consMor_mono`), so its value is pinned to `bSing` (singleton fiber), giving
          -- `c(a, bSing s) = yy ≫ bc`; cancel the cover `π₂` (`cover_epi`).
          intro Y g yy hgw
          let q : G.dom ⟶ B := G.arr ≫ snd
          -- `ConsW ⊆ W` = cons words; `Acons ⊆ G.dom` = points over a cons word.
          let ConsW : Subobject 𝒞 (wordObj A) := ⟨prod A (wordObj A), consMor A, consMor_mono A⟩
          let Acons : Subobject 𝒞 G.dom := InverseImage p ConsW
          -- **NO-JUNK**: `Acons ≤ image actG` — every `G`-point over a cons word is an act.  Proof: the
          -- `imp`-engine `Good := (Acons ⇒ image actG)` (`hGind`): `g₀ ∈ Good` is VACUOUS (`g₀` over a
          -- NIL word, `nil_cons_disjoint`); `Good` is `actG`-closed (`image actG ≤ Good`, `actG` an act);
          -- so `Acons ≤ Good`, whence `Acons ⊓ Acons ≤ image actG` (`imp_adjunction`).
          have hConsImg : Acons.le (image actG) := by
            let Good : Subobject 𝒞 G.dom := Sub.imp Acons (image actG)
            -- `g₀ ∈ Good`: `Acons ⊓ ⟨g₀⟩ ≤ image actG` vacuously (g₀ over nil, `nil_cons_disjoint`).
            have hUnitGood : Allows Good g₀ := by
              -- the singleton subobject of `g₀` (monic via `term_uniq`).
              have hg₀mono : Monic g₀ := by intro Z u v _; exact term_uniq u v
              let G0 : Subobject 𝒞 G.dom := ⟨one, g₀, hg₀mono⟩
              -- `g₀ ∈ G0` and `G0 ≤ Good` ⟹ `g₀ ∈ Good`.
              refine allows_mono ?_ (⟨Cat.id one, Cat.id_comp _⟩ : Allows G0 g₀)
              -- `G0 ≤ Good` via `imp_adjunction`: `Acons ⊓ G0 ≤ image actG`, vacuous.
              refine (imp_adjunction Acons (image actG) G0
                (HasPullbacks.has Acons.arr G0.arr)).2 ?_
              let I := Sub.inter Acons G0 (HasPullbacks.has Acons.arr G0.arr)
              -- `I.arr` factors through `Acons` (cons word via `pCons`) and through `G0` (= `g₀`, nil).
              let pCons : Acons.dom ⟶ prod A (wordObj A) := (HasPullbacks.has p ConsW.arr).cone.π₂
              have hpCons : Acons.arr ≫ p = pCons ≫ consMor A := (HasPullbacks.has p ConsW.arr).cone.w
              obtain ⟨kC, hkC⟩ := Sub.inter_le_left Acons G0 _
              obtain ⟨kU, hkU⟩ := Sub.inter_le_right Acons G0 _
              -- `I.arr ≫ p = (kC ≫ pCons) ≫ consMor` (cons) and `= kU ≫ nilMor` (nil, `kU : I.dom → one`).
              have hcons : I.arr ≫ p = (kC ≫ pCons) ≫ consMor A := by
                rw [← hkC, Cat.assoc, Cat.assoc, hpCons]
              have hnil : I.arr ≫ p = kU ≫ nilMor A := by
                have hg₀p : g₀ ≫ p = nilMor A := by
                  show g₀ ≫ G.arr ≫ fst = nilMor A; rw [← Cat.assoc, hg₀arr, fst_pair]
                show I.arr ≫ p = kU ≫ nilMor A
                rw [← hkU]
                show (kU ≫ g₀) ≫ p = kU ≫ nilMor A
                rw [Cat.assoc, hg₀p]
              -- vacuous: build SOME map `I.dom → (image actG).dom`, then `nil_cons_disjoint` collapses.
              let mapToImg : I.dom ⟶ (image actG).dom :=
                pair ((kC ≫ pCons) ≫ fst) I.arr ≫ image.lift actG
              exact ⟨mapToImg,
                nil_cons_disjoint A kU (kC ≫ pCons)
                  (by rw [← hnil, hcons]) (mapToImg ≫ (image actG).arr) I.arr⟩
            -- `Good` is `actG`-closed: `Allows Good actG` (`actG ∈ image actG ≤ Good`), then restrict.
            have hActGood : Allows Good actG :=
              allows_mono
                ((imp_adjunction Acons (image actG) (image actG)
                  (HasPullbacks.has Acons.arr (image actG).arr)).2
                  (Sub.inter_le_right Acons (image actG) _))
                ⟨image.lift actG, image.lift_fac actG⟩
            have hClosedGood : (InverseImage (snd (A := A) (B := G.dom)) Good).le
                (InverseImage actG Good) := by
              rw [invImage_le_iff_restrict]
              obtain ⟨s, hs⟩ := hActGood
              exact ⟨(InverseImage (snd (A := A) (B := G.dom)) Good).arr ≫ s,
                by rw [Cat.assoc, hs]⟩
            have hAconsGood : Acons.le Good := hGind Good hUnitGood hClosedGood Acons.arr
            -- `Acons ≤ Good = (Acons ⇒ image actG)` ⟹ `Acons ⊓ Acons ≤ image actG` ⟹ `Acons ≤ image actG`.
            have hInter : (Sub.inter Acons Acons (HasPullbacks.has Acons.arr Acons.arr)).le
                (image actG) :=
              (imp_adjunction Acons (image actG) Acons
                (HasPullbacks.has Acons.arr Acons.arr)).1 hAconsGood
            have hrefl : Acons.le Acons := ⟨Cat.id Acons.dom, Cat.id_comp _⟩
            exact subLe_trans
              (Sub.inter_glb Acons Acons Acons (HasPullbacks.has Acons.arr Acons.arr) hrefl hrefl)
              hInter
          -- `g ∈ Acons`: `g ≫ p = yy ≫ wc = (yy ≫ prodMap.. Sing.arr) ≫ consMor` is a cons word.
          have hgAcons : Allows Acons g := by
            let pbC := HasPullbacks.has p ConsW.arr
            have hsq : g ≫ p = (yy ≫ prodMap A Sing.dom (wordObj A) Sing.arr) ≫ ConsW.arr := by
              show g ≫ p = (yy ≫ prodMap A Sing.dom (wordObj A) Sing.arr) ≫ consMor A
              rw [hgw, Cat.assoc]
            exact ⟨pbC.lift ⟨Y, g, _, hsq⟩, pbC.lift_fst _⟩
          -- `g ∈ image actG`: factor `g` through `(image actG).arr`.
          obtain ⟨k, hk⟩ := allows_mono hConsImg hgAcons
          -- COVER PULLBACK: pull `image.lift actG : prod A G.dom ↠ (image actG).dom` back along `k`.
          let pbI := HasPullbacks.has (image.lift actG) k
          let s : pbI.cone.pt ⟶ prod A G.dom := pbI.cone.π₁
          let π : pbI.cone.pt ⟶ Y := pbI.cone.π₂
          have hπcover : Cover π := cover_pullback k (image_lift_cover actG)
          -- `s ≫ actG = π ≫ g`.
          have hsg : s ≫ actG = π ≫ g := by
            show pbI.cone.π₁ ≫ actG = pbI.cone.π₂ ≫ g
            calc pbI.cone.π₁ ≫ actG
                = pbI.cone.π₁ ≫ (image.lift actG ≫ (image actG).arr) := by rw [image.lift_fac]
              _ = (pbI.cone.π₁ ≫ image.lift actG) ≫ (image actG).arr := (Cat.assoc _ _ _).symm
              _ = (pbI.cone.π₂ ≫ k) ≫ (image actG).arr := by rw [pbI.cone.w]
              _ = pbI.cone.π₂ ≫ (k ≫ (image actG).arr) := Cat.assoc _ _ _
              _ = pbI.cone.π₂ ≫ g := by rw [hk]
          -- The source's head `a := s ≫ fst` and predecessor `gp := s ≫ snd : P → G.dom`.
          let a : pbI.cone.pt ⟶ A := s ≫ fst
          let gp : pbI.cone.pt ⟶ G.dom := s ≫ snd
          -- predecessor word `wgp := gp ≫ p`; `s ≫ actG ≫ p = cons(a, wgp)` (`hpt`).
          have hword : s ≫ actG ≫ p = pair a (gp ≫ p) ≫ consMor A := by
            calc s ≫ actG ≫ p
                = s ≫ (prodMap A G.dom (wordObj A) p ≫ consMor A) := by rw [← hpt]
              _ = (s ≫ prodMap A G.dom (wordObj A) p) ≫ consMor A := (Cat.assoc _ _ _).symm
              _ = pair a (gp ≫ p) ≫ consMor A := by
                  congr 1
                  refine pair_uniq a (gp ≫ p) _ ?_ ?_
                  · show (s ≫ prodMap A G.dom (wordObj A) p) ≫ fst = s ≫ fst
                    rw [Cat.assoc, prodMap_fst]
                  · show (s ≫ prodMap A G.dom (wordObj A) p) ≫ snd = gp ≫ p
                    rw [Cat.assoc, prodMap_snd]; exact (Cat.assoc _ _ _).symm
          -- `g`'s word along `π` is `cons(π≫yy≫fst, (π≫yy≫snd)≫Sing.arr)`; match via `consMor_mono`.
          have hgword : π ≫ g ≫ p
              = pair ((π ≫ yy) ≫ fst) (((π ≫ yy) ≫ snd) ≫ Sing.arr) ≫ consMor A := by
            calc π ≫ g ≫ p
                = (π ≫ yy ≫ prodMap A Sing.dom (wordObj A) Sing.arr) ≫ consMor A := by
                  rw [hgw]; show π ≫ yy ≫ (prodMap A Sing.dom (wordObj A) Sing.arr ≫ consMor A) = _
                  rw [Cat.assoc, Cat.assoc]
              _ = pair ((π ≫ yy) ≫ fst) (((π ≫ yy) ≫ snd) ≫ Sing.arr) ≫ consMor A := by
                  congr 1
                  refine pair_uniq _ _ _ ?_ ?_
                  · simp only [Cat.assoc, prodMap_fst]
                  · simp only [Cat.assoc, prodMap_snd]
          -- consMor monic: `a` and predecessor word match the cons data of `g`'s word along `π`.
          have hmatch : pair a (gp ≫ p)
              = pair ((π ≫ yy) ≫ fst) (((π ≫ yy) ≫ snd) ≫ Sing.arr) := by
            refine consMor_mono A _ _ ?_
            calc pair a (gp ≫ p) ≫ consMor A
                = s ≫ actG ≫ p := hword.symm
              _ = (s ≫ actG) ≫ p := (Cat.assoc _ _ _).symm
              _ = (π ≫ g) ≫ p := by rw [hsg]
              _ = π ≫ g ≫ p := Cat.assoc _ _ _
              _ = pair ((π ≫ yy) ≫ fst) (((π ≫ yy) ≫ snd) ≫ Sing.arr) ≫ consMor A := hgword
          have hgpw : gp ≫ p = ((π ≫ yy) ≫ snd) ≫ Sing.arr := by
            have := congrArg (· ≫ snd) hmatch
            simpa only [snd_pair] using this
          have ha : a = (π ≫ yy) ≫ fst := by
            have := congrArg (· ≫ fst) hmatch
            simpa only [fst_pair] using this
          -- predecessor over a `Sing` word ⟹ its value is `bSing` (singleton fiber, `diag_classify_iff`).
          have hgpv : gp ≫ q = ((π ≫ yy) ≫ snd) ≫ bSing := by
            -- `(π≫yy≫snd) ≫ (Sing.arr ≫ valG) = (π≫yy≫snd) ≫ bSing ≫ singletonMapCat` (IH `hbSing`).
            have hfib : (gp ≫ p) ≫ valG = (((π ≫ yy) ≫ snd) ≫ bSing) ≫ singletonMapCat B := by
              rw [hgpw, Cat.assoc, hbSing, ← Cat.assoc]
            -- `(wgp, gp≫q) ∈ G` (`hGmem`) and fiber is `{bSing}` ⟹ `gp≫q = bSing` (`diag_classify_iff`).
            have h1 : pair (gp ≫ q) ((gp ≫ p) ≫ valG) ≫ eval_exp B Ω
                = term pbI.cone.pt ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
              rw [hvalGβ (gp ≫ p) (gp ≫ q)]
              show pair (gp ≫ p) (gp ≫ G.arr ≫ snd) ≫ χG = _
              exact hGmem gp
            rw [hfib, hSingEval (gp ≫ q) (((π ≫ yy) ≫ snd) ≫ bSing)] at h1
            exact (diag_classify_iff (gp ≫ q) (((π ≫ yy) ≫ snd) ≫ bSing)).1 h1
          -- VALUE OF `g` ALONG `π`: `c(a, gp≫q)` (`hpsnd`) `= c(π≫yy≫fst, (π≫yy≫snd)≫bSing) = π≫yy≫bc`.
          have hπval : π ≫ g ≫ q = π ≫ yy ≫ bc := by
            have hstep : π ≫ g ≫ q = pair a (gp ≫ q) ≫ c := by
              calc π ≫ g ≫ q
                  = (π ≫ g) ≫ (G.arr ≫ snd) := (Cat.assoc _ _ _).symm
                _ = (s ≫ actG) ≫ (G.arr ≫ snd) := by rw [hsg]
                _ = s ≫ (prodMap A G.dom B (G.arr ≫ snd) ≫ c) := by
                    rw [Cat.assoc, ← hpsnd]
                _ = (s ≫ prodMap A G.dom B (G.arr ≫ snd)) ≫ c := (Cat.assoc _ _ _).symm
                _ = pair a (gp ≫ q) ≫ c := by
                    congr 1
                    refine pair_uniq a (gp ≫ q) _ ?_ ?_
                    · show (s ≫ prodMap A G.dom B (G.arr ≫ snd)) ≫ fst = s ≫ fst
                      rw [Cat.assoc, prodMap_fst]
                    · show (s ≫ prodMap A G.dom B (G.arr ≫ snd)) ≫ snd = gp ≫ q
                      rw [Cat.assoc, prodMap_snd]; exact (Cat.assoc _ _ _).symm
            rw [hstep, ha, hgpv]
            show pair ((π ≫ yy) ≫ fst) (((π ≫ yy) ≫ snd) ≫ bSing) ≫ c
                = π ≫ yy ≫ (prodMap A Sing.dom B bSing ≫ c)
            rw [← Cat.assoc, ← Cat.assoc]
            congr 1
            refine (pair_uniq _ _ _ ?_ ?_).symm
            · simp only [Cat.assoc, prodMap_fst]
            · simp only [Cat.assoc, prodMap_snd]
          -- cancel the cover `π` (`cover_epi`): `g ≫ q = yy ≫ bc`.
          show g ≫ G.arr ≫ snd = yy ≫ bc
          exact cover_epi hπcover (by
            show π ≫ g ≫ G.arr ≫ snd = π ≫ yy ≫ bc
            exact hπval)
        · -- `(cons(a,w), c(a,b)) ∈ G`: `foldStep` applied to a `G`-point over `(w, bSing)`.
          -- `(Sing.arr, bSing) ∈ G` (singleton fiber inhabited), lift to a `G`-point `gp`, then
          -- `actG` it: `gstep := (id_A × gp) ≫ actG` has word `wc`, value `bc` (via `hpt`/`hpsnd`).
          obtain ⟨gp, hgpw, hgpv⟩ := hGpointOfMem Sing.arr bSing (hMemOfSing Sing.arr bSing hbSing)
          let gstep : prod A Sing.dom ⟶ G.dom := prodMap A Sing.dom G.dom gp ≫ actG
          have hgstepw : gstep ≫ p = wc := by
            show (prodMap A Sing.dom G.dom gp ≫ actG) ≫ p = wc
            rw [Cat.assoc, ← hpt, ← Cat.assoc, ← prodMap_comp, hgpw]
          have hgstepv : gstep ≫ (G.arr ≫ snd) = bc := by
            show (prodMap A Sing.dom G.dom gp ≫ actG) ≫ (G.arr ≫ snd) = bc
            rw [Cat.assoc, ← hpsnd, ← Cat.assoc, ← prodMap_comp, hgpv]
          have := hGmem gstep
          rw [hgstepw, hgstepv] at this
          exact this
      -- assemble the restriction map `consSing : prod A Sing.dom → Sing.dom` via the pullback lift.
      refine actStable_of_restrict (consMor A) Sing
        (pbS.lift ⟨prod A Sing.dom, wc, bc, hwcSing⟩) ?_
      show pbS.lift ⟨prod A Sing.dom, wc, bc, hwcSing⟩ ≫ pbS.cone.π₁
          = prodMap A Sing.dom (wordObj A) Sing.arr ≫ consMor A
      exact pbS.lift_fst _
    -- (C) Leastness: `A* ≤ Sing` — every word of `A*` has a singleton fiber.
    have hListLeSing : (listCarrier A).le Sing :=
      actLeast_le (nilMor A) (consMor A) snd Sing hNilSing hConsSing
    have hcore : kp₁ (f := p) ≫ (G.arr ≫ snd) = kp₂ (f := p) ≫ (G.arr ≫ snd) := by
      -- `δ := kp₁ ≫ p = kp₂ ≫ p`, a word that factors through `A*` (via `pCov`), hence `Sing`.
      obtain ⟨s, hs⟩ := hListLeSing
      have hδSing : Allows Sing (kp₁ (f := p) ≫ p) :=
        ⟨kp₁ (f := p) ≫ pCov ≫ s, by
          calc (kp₁ (f := p) ≫ pCov ≫ s) ≫ Sing.arr
              = kp₁ (f := p) ≫ pCov ≫ (s ≫ Sing.arr) := by
                rw [Cat.assoc, Cat.assoc]
            _ = kp₁ (f := p) ≫ pCov ≫ (listCarrier A).arr := by rw [hs]
            _ = kp₁ (f := p) ≫ p := by rw [hpCov]⟩
      obtain ⟨b', hb'⟩ := hSingWit (kp₁ (f := p) ≫ p) hδSing
      -- Both kernel-pair value-legs equal `b'` (singleton fiber over the common word `δ`).
      have hval : ∀ (g : kernelPair p ⟶ G.dom), g ≫ p = kp₁ (f := p) ≫ p →
          g ≫ (G.arr ≫ snd) = b' := by
        intro g hgw
        have h1 : pair (g ≫ (G.arr ≫ snd)) ((kp₁ (f := p) ≫ p) ≫ valG) ≫ eval_exp B Ω
            = term (kernelPair p) ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
          rw [← hgw, hvalGβ (g ≫ p) (g ≫ (G.arr ≫ snd)), hGmem g]
        rw [hb', hSingEval (g ≫ (G.arr ≫ snd)) b'] at h1
        exact (diag_classify_iff (g ≫ (G.arr ≫ snd)) b').1 h1
      rw [hval (kp₁ (f := p)) rfl, hval (kp₂ (f := p)) kp_sq.symm]
    -- The fst-legs of `kp₁≫G.arr`, `kp₂≫G.arr` agree (kp_sq, `p = G.arr≫fst`); the snd-legs
    -- agree by `hcore`.  `pair_uniq` then forces `kp₁≫G.arr = kp₂≫G.arr`; `G.arr` mono ⟹ equal legs.
    have hkparr : kp₁ (f := p) ≫ G.arr = kp₂ (f := p) ≫ G.arr := by
      have h1 : kp₁ (f := p) ≫ G.arr = pair (kp₁ (f := p) ≫ p) (kp₁ (f := p) ≫ (G.arr ≫ snd)) := by
        refine pair_uniq _ _ _ ?_ (Cat.assoc _ _ _)
        show (kp₁ (f := p) ≫ G.arr) ≫ fst = kp₁ (f := p) ≫ p
        rw [Cat.assoc]; rfl
      have h2 : kp₂ (f := p) ≫ G.arr = pair (kp₂ (f := p) ≫ p) (kp₂ (f := p) ≫ (G.arr ≫ snd)) := by
        refine pair_uniq _ _ _ ?_ (Cat.assoc _ _ _)
        show (kp₂ (f := p) ≫ G.arr) ≫ fst = kp₂ (f := p) ≫ p
        rw [Cat.assoc]; rfl
      rw [h1, h2, kp_sq, hcore]
    have hkpeq : kp₁ (f := p) = kp₂ (f := p) := G.monic _ _ hkparr
    -- `Monic p` from `kp₁ = kp₂`.
    intro Z u v huv
    let w : Z ⟶ kernelPair p := (HasPullbacks.has p p).lift ⟨Z, u, v, huv⟩
    calc u = w ≫ kp₁ (f := p) := (kp_lift_p₁ u v huv).symm
      _ = w ≫ kp₂ (f := p) := by rw [hkpeq]
      _ = v := kp_lift_p₂ u v huv
  have hpCovMono : Monic pCov := by
    intro Z u v huv
    apply hpmono
    calc u ≫ p = u ≫ pCov ≫ (listCarrier A).arr := by rw [hpCov]
      _ = (u ≫ pCov) ≫ (listCarrier A).arr := (Cat.assoc _ _ _).symm
      _ = (v ≫ pCov) ≫ (listCarrier A).arr := by rw [huv]
      _ = v ≫ pCov ≫ (listCarrier A).arr := Cat.assoc _ _ _
      _ = v ≫ p := by rw [hpCov]
  -- `pCov` monic + cover ⟹ iso; `f := pCov⁻¹ ≫ G.arr ≫ snd`.
  obtain ⟨pinv, hpinv1, hpinv2⟩ := monic_cover_iso pCov hpCovCover hpCovMono
  refine ⟨pinv ≫ G.arr ≫ snd, ?_, ?_⟩
  · -- `listNil ≫ f = e`.  `listNil ≫ pCov⁻¹ = g₀` since both project to `nilMor` and `pCov` mono.
    -- `g₀ ≫ p = nilMor = listNil ≫ A*.arr = listNil ≫ pCov ≫ A*.arr ≫ ... ` — use `pCov` iso.
    have hg₀p : g₀ ≫ p = nilMor A := by
      show g₀ ≫ G.arr ≫ fst = nilMor A
      rw [← Cat.assoc, hg₀arr, fst_pair]
    -- `listNil = g₀ ≫ pCov`: both compose with `A*.arr` to `nilMor`, and `A*.arr` mono.
    have hnilpCov : listNil A = g₀ ≫ pCov := by
      apply (listCarrier A).monic
      rw [listNil_arr, Cat.assoc, hpCov, hg₀p]
    have hcollapse : listNil A ≫ pinv = g₀ := by
      rw [hnilpCov, Cat.assoc, hpinv1]; exact Cat.comp_id _
    calc listNil A ≫ pinv ≫ G.arr ≫ snd
        = (listNil A ≫ pinv) ≫ G.arr ≫ snd := (Cat.assoc _ _ _).symm
      _ = g₀ ≫ G.arr ≫ snd := by rw [hcollapse]
      _ = (g₀ ≫ G.arr) ≫ snd := (Cat.assoc _ _ _).symm
      _ = pair (nilMor A) e ≫ snd := by rw [hg₀arr]
      _ = e := snd_pair _ _
  · -- `prodMap.. f ≫ c = listCons ≫ f`.  Chase through the graph: `listCons ≫ pCov⁻¹ = actG ↾`.
    let f : (listCarrier A).dom ⟶ B := pinv ≫ G.arr ≫ snd
    show prodMap A (listCarrier A).dom B f ≫ c = listCons A ≫ f
    -- `listCons ≫ pinv = prodMap A A*.dom G.dom pinv ≫ actG`:  both compose with `pCov` to agree,
    -- using `pCov ≫ A*.arr = p`, `hpt`, and `listCons_arr`.
    have htpinv : listCons A ≫ pinv
        = prodMap A (listCarrier A).dom G.dom pinv ≫ actG := by
      apply hpCovMono
      -- LHS ≫ pCov = listCons ≫ (pinv ≫ pCov) = listCons.
      have hL : (listCons A ≫ pinv) ≫ pCov = listCons A := by
        rw [Cat.assoc, hpinv2, Cat.comp_id]
      -- RHS ≫ pCov, then ≫ A*.arr, equals listCons ≫ A*.arr; cancel mono A*.arr.
      apply (listCarrier A).monic
      rw [hL, listCons_arr, Cat.assoc, hpCov]
      -- `prodMap.. A*.arr ≫ consMor = (prodMap.. pinv ≫ actG) ≫ p`.
      have hpinvp : pinv ≫ p = (listCarrier A).arr := by
        rw [← hpCov, ← Cat.assoc, hpinv2, Cat.id_comp]
      rw [Cat.assoc, ← hpt, ← Cat.assoc, ← prodMap_comp, hpinvp]
    -- Now: `prodMap.. f ≫ c = prodMap.. (pinv ≫ G.arr ≫ snd) ≫ c`.
    calc prodMap A (listCarrier A).dom B f ≫ c
        = prodMap A (listCarrier A).dom G.dom pinv
            ≫ (prodMap A G.dom B (G.arr ≫ snd) ≫ c) := by
          show prodMap A (listCarrier A).dom B (pinv ≫ G.arr ≫ snd) ≫ c = _
          rw [prodMap_comp, prodMap_comp, Cat.assoc]
      _ = prodMap A (listCarrier A).dom G.dom pinv ≫ (actG ≫ (G.arr ≫ snd)) := by rw [hpsnd]
      _ = (prodMap A (listCarrier A).dom G.dom pinv ≫ actG) ≫ (G.arr ≫ snd) := (Cat.assoc _ _ _).symm
      _ = (listCons A ≫ pinv) ≫ (G.arr ≫ snd) := by rw [htpinv]
      _ = listCons A ≫ f := by rw [Cat.assoc]

end ListObjectAssembly

/-- §1.98(14): In a topos with a NNO, every object A has a free A-action.

    STATEMENT FIDELITY (no boolean hypothesis here, deliberately).  Unlike §1.988 / §1.98(10)
    / §1.98(13) — whose Peano property Freyd proves only in a BOOLEAN topos (hence
    `recursor_exists_of_bicartesian` / `free_recursor_exists_of_bicartesian` carry `BooleanSub`) —
    Freyd's §1.98(14) is stated and proved in ANY topos with a NNO: the free A-action is the LIST
    OBJECT `A* = Σₙ Aⁿ`, built from the NNO by primitive recursion, with NO booleanness used.  So
    adding `BooleanSub` here would be UNfaithful (an unused hypothesis).  Its residual is the
    genuinely Chapter-1 list-object / N-indexed-coproduct infrastructure gap below, NOT a §1.988
    Peano (boolean) gap. -/
theorem free_action_exists {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    (A : 𝒞) : Nonempty (FreeAAction (𝒞 := 𝒞) A) := by
  -- The free A-action IS a list object `A*` (`freeAAction_of_listObject` above discharges the
  -- whole universal property Sorry-free once `A*` is in hand).  So the entire content of
  -- §1.98(14) is isolated in the SINGLE primitive `ListObjectData A` — the initial algebra of
  -- `F X = 1 + A × X`, i.e. `A* = Σₙ Aⁿ` ("finite words in A").
  --
  -- REALIZED CONSTRUCTION (this session) — the AMBIENT ALGEBRA is the EXPONENTIAL carrier, NOT the
  -- old `powObj(N×A)` graph (which hit a hard relational `consM`).  Concretely:
  --   * `W := (1+A)^N = wordObj A` (a word = a stream of letters, eventually the blank `inl ⋆`).
  --   * `nilMor : 1 → W` = constant blank; `consMor : A×W → W` = prepend, via the NNO `1+N ≅ N`
  --     index case-split (`nnoCoUninv`) + exponential `eval`.  Element-reader is FREE (eval).
  --   * `A* := listCarrier A = (actLeast nilMor consMor snd) ⊆ W`; `listNil`/`listCons` from
  --     `actLeast_allows`/`actLeast_stable` (`listNil_arr`/`listCons_arr`).
  -- ALL of the above is sorry-free `[propext, Classical.choice]`.  The β-laws `nilMor_read`/
  -- `consMor_read`/`consBody_zero`/`consBody_succ`, the list-induction `listObject_ext`
  -- (`fold_uniq`, via the equalizer-on-W + `actLeast_le`), and the fold-graph TOTALITY
  -- `foldProj_total` are ALL sorry-free.
  --
  -- THE SINGLE RESIDUAL is `foldExists` (used below for `fold`/`fold_nil`/`fold_cons`): the
  -- functional-graph EXTRACTION of `fold : A* → B` from the totality-proved graph `foldGraph`.
  -- The corestriction `pCov : G.dom ↠ A*` (via `image (foldProj) = A*`) and the iso assembly are
  -- now sorry-free; the only open content is single-valuedness `Monic (foldProj A e c)` (`hcore`,
  -- non-boolean §1.989).  See `foldExists`'s docstring.
  -- ASSEMBLY (this session): the list object `A* = (listCarrier A).dom ⊆ W = (1+A)^N` is built
  -- sorry-free (`listCarrier`/`listNil`/`listCons` from `actLeast`); `nil`/`cons` and their arr-laws
  -- are proved; `fold` comes from the functional graph `foldExists`; `fold_uniq` is `listObject_ext`
  -- (the `actLeast_le` induction), sorry-free.  The SINGLE residual is `foldExists` (graph
  -- extraction + single-valuedness) — see its docstring.
  obtain ⟨LD⟩ : Nonempty (ListObjectData (𝒞 := 𝒞) A) :=
    ⟨{ L         := (listCarrier A).dom
       nil       := listNil A
       cons      := listCons A
       fold      := fun {B} e c => (foldExists A e c).choose
       fold_nil  := fun {B} e c => (foldExists A e c).choose_spec.1
       fold_cons := fun {B} e c => (foldExists A e c).choose_spec.2
       fold_uniq := fun {B} e c m hm0 hmc =>
         listObject_ext A e c m ((foldExists A e c).choose)
           hm0 (foldExists A e c).choose_spec.1
           hmc (foldExists A e c).choose_spec.2 }⟩
  exact ⟨freeAAction_of_listObject LD⟩

end Freyd
