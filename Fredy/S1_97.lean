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
theorem mono_from_one {A : 𝒞} (a : one ⟶ A) : Mono a := by
  intro X f g _; exact term_uniq f g

/-- Composite of monics is monic. -/
theorem mono_comp'' {X Y Z : 𝒞} {m : X ⟶ Y} {n : Y ⟶ Z} (hm : Mono m) (hn : Mono n) :
    Mono (m ≫ n) := by
  intro W f g h
  apply hm; apply hn
  rw [← Cat.assoc, ← Cat.assoc] at h; exact h

/-- The monic subobject `⟨X, m⟩` is its own image: `image m ≤ ⟨X,m⟩` (minimality, `m` allows
    itself) and `⟨X,m⟩ ≤ image m` (image allows `m`, and `m` monic descends). -/
theorem image_mono_eq {A X : 𝒞} (m : X ⟶ A) (hm : Mono m) :
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
    Isomorphic.trans' ⟨z, hz_iso⟩ (bottomSub_dom_iso (one : 𝒞) A)
  exact le_bottom_of_dom_iso Z hZ0

/-- **A map into a `⊥`-domain forces `≤ ⊥`** (strict initiality).  `⊥.dom ≅ 0` is strict-initial,
    so any `m : Z.dom → (⊥W).dom` makes `Z.dom ≅ 0 ≅ (⊥A).dom`. -/
theorem peano_le_bottom_of_map {A W : 𝒞} (Z : Subobject 𝒞 A)
    (m : Z.dom ⟶ (PreLogos.bottom W).dom) : Z.le (PreLogos.bottom A) := by
  let z : Z.dom ⟶ (bottomSub (one : 𝒞)).dom :=
    m ≫ (bottomSub_dom_iso W (one : 𝒞)).choose
  have hz_iso : IsIso z := any_map_to_zero_is_iso (inferInstance : PreLogos 𝒞) z
  exact le_bottom_of_dom_iso Z (Isomorphic.trans' ⟨z, hz_iso⟩ (bottomSub_dom_iso (one : 𝒞) A))

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

section PeanoRecursor
-- The `sorry`-stub instance `topos_has_exponentials` (S1_92, priority 50) extends
-- `HasBinaryProducts`; instance search can route a `HasBinaryProducts 𝒞` goal through it and
-- inject `sorryAx` into otherwise axiom-clean theorems.  The §1.988/§1.989 Peano/recursor
-- theorems below use NO exponentials, so we make the genuine `Topos.toHasBinaryProducts` win
-- outright for this section (same workaround S1_92 applies to its §1.92 section); without it
-- `recursor_exists_of_bicartesian` etc. spuriously pick up `sorryAx`.
attribute [local instance 10000] Topos.toHasBinaryProducts

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
  have hinr_mono : Mono (HasBinaryCoproducts.inr (A := one) (B := A)) :=
    mono_of_retraction _ (HasBinaryCoproducts.case a (Cat.id A))
      (HasBinaryCoproducts.case_inr a (Cat.id A))
  -- `t` monic: `t = inr ≫ case`, `inr` monic, `case` iso.
  have htmono : Mono t := by
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
    have ha_mono : Mono a := mono_from_one a
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
    ⟹ Δ entire ⟹ kp_diag cover (split mono via kp_diag_p₁) ⟹ iso ⟹ Mono p`.  The KEYSTONE
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
    have hpmono : Mono p := by
      -- §1.989 single-valuedness (Freyd p.186).  `K := kernelPair p`, diagonal `Δ := image kp_diag`.
      -- Boolean complement `K'` of `Δ` (off-diagonal kernel pair); `A₁ := image(K'.arr ≫ kp₁ ≫ p)`
      -- its `A`-image; `A₂ := boolean complement`.  `A₂` is `(a,t)`-closed, so ENTIRE by Peano, hence
      -- `A₁ ≤ ⊥` ⟹ `K' ≤ ⊥` ⟹ `Δ` entire ⟹ `kp_diag` cover.  `kp_diag` is split mono (`kp_diag_p₁`),
      -- so a cover-split-mono is iso; `monic_iff_kp_diag_iso` then gives `Mono p`.
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
      have ha_mono : Mono a := mono_from_one a
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
          have hcase_mono : Mono (HasBinaryCoproducts.case a t (A := (one : 𝒞)) (B := A) (X := A)) :=
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
          have ht_mono : Mono t := by
            obtain ⟨caseInv, hcaseInv, _⟩ := hiso
            have hcase_mono : Mono (HasBinaryCoproducts.case a t (A := (one : 𝒞)) (B := A) (X := A)) :=
              mono_of_retraction _ caseInv hcaseInv
            have hinr_split : HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := A)
                ≫ HasBinaryCoproducts.case a (Cat.id A) = Cat.id A :=
              HasBinaryCoproducts.case_inr _ _
            have hinr_mono : Mono (HasBinaryCoproducts.inr (A := (one : 𝒞)) (B := A)) :=
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
              have hcase_mono : Mono (HasBinaryCoproducts.case a t
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
    have hm_mono : Mono m := by
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
    @PeanoProperty 𝒞 _ (Topos.toHasTerminal) _ A a t :=
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
  have hm_mono : Mono m := by
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

end PeanoRecursor

/-! ## §1.98(13)  Bicartesian characterization of free A-action

  §1.98(13): The analogue of the bicartesian characterization [1.985, 1.98(10)]
  holds for a free A-action A*: namely A × 1 →(1,e)→ A × A* →s→ A* is a free
  A-action iff [1 + A × A*, A*] ≅ A* (iso) and A × A* → A* → 1 is a coequalizer.
  The reasoning is analogous to [1.985] and [1.98(10)]. -/

/-- **§1.98(13) action PEANO PROPERTY in a BOOLEAN topos (the §1.988 free content).**
    Every `(unit,act)`-closed subobject `B ↣ α.obj` is entire.  `B` closed = it allows
    `unit` (point `uB : 1 → B.dom`, `uB ≫ B.arr = α.unit`) and is `act`-stable
    (`actB : A×B.dom → B.dom`, `actB ≫ B.arr = prodMap A B.dom α.obj B.arr ≫ α.act`).

    PROOF.  The A-parametrised analogue of `peano_property_of_bicartesian`: take the least
    `(unit,act)`-closed subobject `α'`, complement it (`hbool`) to `α' + α''`, and use the
    coequalizer `α.act = snd ≫ f` collapse to force `α'' = 0`.  Same complement structure as
    the NNO case for the functor `1 + A×(−)`. -/
theorem free_peano_property_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
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
    B.IsEntire := by
  -- Freyd's §1.988 complement argument for the A-parametrised functor `1 + A×(−)` (boolean).
  -- DIRECT ANALOGUE of the now-CLOSED `peano_property_of_bicartesian`: replay `t_stable_complement`
  -- with `act : A×α.obj → α.obj` as the "successor".  MISSING PRIMITIVE: a least `(unit,act)`-closed
  -- subobject of `α.obj` for the parametrised functor `1+A×(−)`.  The endo-only API in this layer —
  -- `Freyd.IsClosedSub`/`HasLeastClosedSubobject` (`InternalForall.lean`) and its discharge
  -- `Freyd.toposHasLeastClosedSubobject` (`LeastClosedTopos.lean`, whose `tStableBody`/`tStable`/
  -- `closedFamily` are built for an ENDO `t : A→A` via `prod A (powObj A)`) — does NOT apply: closure
  -- here is `image(prodMap A B.dom α.obj B.arr ≫ act) ≤ B`, where `act` consumes the `A`-factor, so
  -- the family-glb `bigInter (closedFamily …)` must be REBUILT with the parametrised closedness
  -- predicate `{σ : [α.obj] | unit∈σ ∧ ∀(a,x). x∈σ ⇒ act(a,x)∈σ}` on `[α.obj]`.  Once that
  -- parametrised `least (unit,act)` is in hand, the complement chase (`hbool` ⟹ `α'+α''`, monic
  -- decomposition `unit(1)∪act(A×α')`, `complement_le_other'`, coequalizer collapse `α''=0`) ports
  -- verbatim.  STATUS: blocked on the parametrised least-closed-subobject primitive, NOT on §1.988
  -- complement (closed for the endo case) and NOT on §1.543-capitalization.
  sorry

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
  have hm_mono : Mono m := by
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
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
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
  · -- EXISTENCE residual: the A-parametrised §1.988 recursion theorem, FAITHFULLY in a BOOLEAN +
    -- CAPITAL topos (Freyd's §1.98(13) is proved "analogously to §1.98(10)", i.e. with the same
    -- BOOLEAN+CAPITAL hypotheses).  With `hcap` now in scope the §1.989 SINGLE-VALUEDNESS half is
    -- in principle available (`pts_covers_of_capital hcap` = 1 projective; `hcap` = well-pointed).
    -- The remaining hole is gap (i): TOTALITY needs `free_peano_property_of_bicartesian` (below),
    -- itself blocked on the PARAMETRISED least `(unit,act)`-closed subobject primitive for the
    -- A-parametrised functor `1+A×(−)` — which the endo-only `HasLeastClosedSubobject` does NOT
    -- supply (its `closedFamily` is built for an ENDO `t:A→A`, not a `act:A×(−)→(−)`).  That
    -- parametrised-least-closed primitive is the genuine residual here; it is NOT supplied by
    -- `hcap` and is NOT a §1.543-capitalization gap (the §1.989 single-valued half is).
    sorry
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
  -- §1.98(14) is now isolated in the SINGLE primitive `ListObjectData A` — the initial algebra
  -- of `F X = 1 + A × X`, i.e. `A* = Σₙ Aⁿ` ("finite words in A").
  --
  -- WHY THE NNO ALONE CANNOT BUILD `A*` IN THIS LAYER.  The NNO is the initial algebra of the
  -- 1-parameter functor `X ↦ 1 + X` (`iterate`, §1.98).  The list object is the initial algebra
  -- of the A-PARAMETRISED functor `X ↦ 1 + A × X`; classically `A* ≅ ∐ₙ Aⁿ`.  Passing from the
  -- former to the latter needs ONE of:
  --   (a) the N-INDEXED COPRODUCT `∐ₙ Aⁿ` — but the repo has only BINARY `HasBinaryCoproducts`
  --       (S1_58); no countable/NNO-indexed coproduct exists, and binary ⊔ + NNO do not yield it;
  --   (b) the LIST OBJECT as a definable subobject of `(1+A)^N` cut out by a "bounded-length"
  --       predicate — but that comprehension is the internal-∀ / family-glb on `Ω^…` that
  --       `least_peano_subobject` (above) and `S1_94` both bottom out on (the internal-∀ /
  --       family-glb that `S1_94` never constructs — NOT the now-proven §1.543 lemma);
  --   (c) the PARTIAL-MAP CLASSIFIER recursor `B̃` of §1.988/§1.934 — Freyd builds `B̃ = Π_t(B/0)`
  --       in a CAPITAL topos (§1.935); §1.543 capitalization is now PROVEN Sorry-free here, so the
  --       residual is the absent LAWFUL per-codomain PMC interface (`S1_92` has only a bare
  --       single-object `pmc_obj`, no restrict/uniqueness law), the same gap hit by
  --       `nno_of_bicartesian_data`.  The available `iteratePair`/`primRec` (§1.981/§1.983)
  --       iterate a FIXED fibre `B`, not the growing power `Aⁿ`, so they cannot define `fold`.
  --
  -- Residual = the SINGLE, sharply named gap `ListObjectData A` (= §1.98(14) list object
  -- existence), with its lawful consumer `freeAAction_of_listObject` already proved Sorry-free.
  obtain ⟨LD⟩ : Nonempty (ListObjectData (𝒞 := 𝒞) A) := by
    -- MISSING PRIMITIVE: existence of the list object `A* = Σₙ Aⁿ` (initial `1 + A×(−)`-algebra).
    -- Not constructible from `HasNaturalNumbersObject` + `HasExponentials` + binary coproducts
    -- alone; requires (a)/(b)/(c) above.  STATUS: NOT §1.543-capitalization (now proven Sorry-free,
    -- `Fredy.CapDataWiring.capData_exists`); the residual is the absent N-indexed coproduct /
    -- internal-∀ comprehension / lawful per-codomain partial-map-classifier infrastructure.
    sorry
  exact ⟨freeAAction_of_listObject LD⟩

end Freyd
