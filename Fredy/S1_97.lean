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
import Fredy.S1_51
import Fredy.S1_57
import Fredy.S1_58
import Fredy.S1_85
import Fredy.S1_92
import Fredy.S1_94
import Fredy.InternalForall
import Fredy.PartialMapClassifier
import Fredy.LeastClosedTopos


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

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

/-- **§1.988 RECURSOR EXISTENCE — the single residual of §1.98(10).**

    From bicartesian data `[a,t] : 1+A ≅ A` on `A` (and the terminal coequalizer
    `hcoeq`), §1.988 produces, for every `(X, x : 1→X, f : X→X)`, a map `h : A → X`
    with `a ≫ h = x` and `t ≫ h = h ≫ f` — Freyd's recursion theorem.  Concretely
    `h` is the fixpoint `h = pred ≫ case x (h ≫ f)` of the iso `pred := [a,t]⁻¹`,
    built through the lawful per-codomain partial-map classifier
    (`Fredy.partialMapClassifier_exists`) for the *partial* recursor, whose domain
    `R ↣ A` is `(a,t)`-stable and forced entire by the §1.987 Peano INDUCTION the
    coequalizer powers.

    This EXISTENCE is the one genuinely missing §1.988 primitive (the W-type / PMC
    fixpoint): `least_peano_subobject` gives the least `(a,t)`-closed subobject's
    *existence*, but constructing the total recursor is the absent recursion theorem.
    Once it is in hand, `peano_of_bicartesian` (the §1.987 Peano property), recursor
    UNIQUENESS, and the full §1.98(10) NNO are derived here Sorry-free.  We bundle the
    `(a,t) → A`-instance UNIQUENESS into this primitive because §1.988 delivers the
    recursor as a unique fixpoint (existence and uniqueness are produced together by
    the partial-map-classifier construction); this single uniqueness clause breaks the
    `peano ⟺ recursor-uniqueness` circularity, after which the GENERAL recursor
    uniqueness (into any `X`) is re-derived from the Peano property via the equalizer
    (`recursor_unique_of_bicartesian`).

    This is the one genuinely missing §1.988 primitive (the W-type / PMC fixpoint):
    `least_peano_subobject` gives the least `(a,t)`-closed subobject's *existence*, but
    constructing the total recursor is the absent recursion theorem.  STATUS: NOT
    §1.543-capitalization (proven Sorry-free); the residual is the absent §1.988
    partial-map-classifier recursor. -/
theorem recursor_exists_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
    {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A)
    (hiso : IsIso (HasBinaryCoproducts.case a t (A := one) (B := A) (X := A)))
    (hcoeq : ∀ (X : 𝒞) (f : A ⟶ X), t ≫ f = f →
               ∃ g : (one ⟶ X), term A ≫ g = f ∧
                 ∀ g' : one ⟶ X, term A ≫ g' = f → g' = g) :
    -- existence for every codomain, plus uniqueness for the `(a,t) → A` instance.
    (∀ {X : 𝒞} (x : one ⟶ X) (f : X ⟶ X),
        ∃ h : A ⟶ X, a ≫ h = x ∧ t ≫ h = h ≫ f) ∧
      (∀ e : A ⟶ A, a ≫ e = a → t ≫ e = e ≫ t → e = Cat.id A) := by
  -- THE ONE RESIDUAL of §1.98(10): the §1.988 recursion theorem (existence of the
  -- recursor for every codomain, and uniqueness of the `(a,t)→A` recursor `= id_A`).
  -- Everything else in §1.98(10) — `peano_of_bicartesian`, GENERAL recursor
  -- uniqueness, and the NNO assembly — is derived from this Sorry-free below.
  --
  -- SHARPENED RESIDUAL (feasibility analysis 2026-06-21, work/recursor2).
  -- Both conjuncts reduce to ONE missing primitive, the §1.988 PEANO PROPERTY:
  --   (P) every `(a,t)`-CLOSED subobject `S ↣ A` of bicartesian `[a,t]:1+A≅A` is ENTIRE.
  -- Given (P): EXISTENCE — build the graph `G ↣ A×X` as `least_peano_subobject (A×X)
  --   (pair a x) (prodMap t f)`; its projection `G ↣ A×X → A` is `(a,t)`-closed in `A`,
  --   so by (P) entire ⇒ single-valued+total ⇒ `h := proj⁻¹ ≫ G.arr ≫ snd`.  UNIQUENESS —
  --   the equalizer `eq(e,id_A) ↣ A` is `(a,t)`-closed, so (P) makes it entire ⇒ `e=id`.
  -- The block is (P) ITSELF, and it is a GENUINE wall here, not a missing tactic:
  --   • Freyd's ACTUAL §1.988 proof proves (P) ONLY in a BOOLEAN topos: take `A''` =
  --     COMPLEMENT of the least closed `A'`, split `A = A' + A''`, and use `hcoeq` to get
  --     `C' + C'' = 1`, forcing `C''=0`, `A''=0` (§1.658 complement + §1.635/§1.641/§1.944).
  --     A general `Topos 𝒞` is NOT boolean — the subobject `A'` need not be COMPLEMENTED
  --     (`IsComplementedSub`, Fredy/Complement.lean), so this route is unavailable.
  --   • The "remove boolean" device (§2.542: faithful bicartesian embedding into a boolean
  --     topos) is ABSENT from the repo — it cannot even be STATED yet (Fredy/S2_5.lean:592).
  --   • The prompt's PMC-W-type alternative (partial recursor `R ↣ A×X` classified via
  --     `partialMapClassifier_exists`, domain forced entire) is CIRCULAR: forcing `dom R`
  --     entire — equivalently single-valuedness/totality of `R` — IS exactly (P) again.
  --   • `least_peano_subobject` (sorry-free, available here) supplies the EXISTENCE of the
  --     least closed subobject, never its ENTIRETY; `hcoeq` alone (maps killing `t` are
  --     constant) cannot split `A` along a non-complemented closed `S`.
  -- MISSING LEMMA, named precisely:  `peano_property_of_bicartesian`:
  --     `IsIso (case a t) → (terminal coeq of (t,id)) → ∀ S closed, S.IsEntire`
  --   provable EITHER from a `[BooleanTopos 𝒞]`/`IsComplementedSub (least closed)` hypothesis
  --   (Freyd's §1.988, complement route) OR from the §2.542 boolean-embedding theorem — both
  --   absent.  This is the absent §1.988 Peano primitive, NOT §1.543-capitalization (proven).
  sorry

/-- **§1.987 PEANO PROPERTY from bicartesian data.**  Every `(a,t)`-closed subobject
    `B ↣ A` of bicartesian data `[a,t] : 1+A ≅ A` is entire.

    PROOF.  `B` closed gives a point `aB : 1 → B.dom` (`aB ≫ B.arr = a`) and a
    `t`-restriction `tB : B.dom → B.dom` (`tB ≫ B.arr = B.arr ≫ t`).  By the §1.988
    recursor (`recursor_exists_of_bicartesian` into `B.dom`) there is a SECTION
    `sec : A → B.dom` with `a ≫ sec = aB` and `t ≫ sec = sec ≫ tB`.  Then
    `sec ≫ B.arr : A → A` is a recursor for `(a,t)` into `A` itself, as is `id_A`;
    the §1.988 recursor's `(a,t)→A` instance is UNIQUE (two recursors into `A` agree
    — their equalizer is `(a,t)`-closed, but here we use the recursor directly), so
    `sec ≫ B.arr = id_A`.  Hence `B.arr` is a split epi; being also monic it is an
    iso, i.e. `B` is entire.  This is the section-building argument of
    `nno_peano_property`, with the §1.988 recursor in place of NNO `iterate`. -/
theorem peano_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
    {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A)
    (hiso : IsIso (HasBinaryCoproducts.case a t (A := one) (B := A) (X := A)))
    (hcoeq : ∀ (X : 𝒞) (f : A ⟶ X), t ≫ f = f →
               ∃ g : (one ⟶ X), term A ≫ g = f ∧
                 ∀ g' : one ⟶ X, term A ≫ g' = f → g' = g) :
    @PeanoProperty 𝒞 _ (Topos.toHasTerminal) _ A a t := by
  intro B ⟨aB, haB⟩ ⟨tB, htB⟩
  obtain ⟨hex, huniqA⟩ := recursor_exists_of_bicartesian a t hiso hcoeq
  -- Section `sec : A → B.dom` via the §1.988 recursor for the B-algebra `(aB, tB)`.
  obtain ⟨sec, hsec0, hsecs⟩ := hex aB tB
  -- `sec ≫ B.arr` and `id_A` are both `(a,t)`-recursors into `A`; the bundled
  -- `(a,t)→A` uniqueness (`huniqA`) forces `sec ≫ B.arr = id_A`.
  -- `sec ≫ B.arr`: `a ≫ (sec ≫ B.arr) = aB ≫ B.arr = a`;
  --   `t ≫ (sec ≫ B.arr) = (sec ≫ tB) ≫ B.arr = sec ≫ (B.arr ≫ t) = (sec ≫ B.arr) ≫ t`.
  have hsecB : sec ≫ B.arr = Cat.id A := by
    apply huniqA
    · rw [← Cat.assoc, hsec0, haB]
    · rw [← Cat.assoc, hsecs, Cat.assoc, htB, ← Cat.assoc]
  -- `B.arr` split epi (retraction `sec`) + monic ⇒ iso.
  refine ⟨sec, ?_, hsecB⟩
  apply B.monic
  rw [Cat.assoc, hsecB, Cat.comp_id, Cat.id_comp]

/-- **Recursor UNIQUENESS from bicartesian data** (§1.987 via the equalizer).
    Any two `(a,t)`-recursors `h, h' : A → X` (each with `a ≫ · = x` and
    `t ≫ · = · ≫ f`) are equal.  Their equalizer `E = eq(h,h') ↣ A` is `(a,t)`-closed
    (allows `a` since `a ≫ h = x = a ≫ h'`; `t`-stable since `m ≫ t` still equalizes
    `h, h'`), hence entire by `peano_of_bicartesian`; the equalizer map is then iso and
    left-cancels `h = h'`. -/
theorem recursor_unique_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
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
  have hEent : E.IsEntire := peano_of_bicartesian a t hiso hcoeq E hEa hEt
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
    then 1 →ᵃ A →ᵗ A is a NNO.

    The `pmc` partial-map-classifier hypothesis is GONE: the lawful per-codomain PMC
    is now derived internally where needed (`Fredy.partialMapClassifier_exists`), so the
    statement is strictly STRONGER than the earlier `(pmc : HasPartialMapClassifier 𝒞)`
    form.  UNIQUENESS of the recursor is fully proved here from the Peano property
    `peano_of_bicartesian` (the equalizer of two recursors is an `(a,t)`-closed
    subobject, hence entire); EXISTENCE of the recursor is the one §1.988 residual
    `recursor_exists_of_bicartesian`. -/
theorem nno_of_bicartesian_data {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
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
    obtain ⟨hex, _⟩ := recursor_exists_of_bicartesian a t hiso hcoeq
    obtain ⟨h, hh0, hhs⟩ := hex x f
    exact ⟨h, ⟨hh0, hhs⟩, fun h' h0' hs' =>
      recursor_unique_of_bicartesian a t hiso hcoeq x f h' h h0' hs' hh0 hhs⟩
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
  exact nno_of_bicartesian_data (tOne ≫ hT.map hN.zero) (hT.map hN.succ) hT_iso hT_coeq

/-! ## §1.98(13)  Bicartesian characterization of free A-action

  §1.98(13): The analogue of the bicartesian characterization [1.985, 1.98(10)]
  holds for a free A-action A*: namely A × 1 →(1,e)→ A × A* →s→ A* is a free
  A-action iff [1 + A × A*, A*] ≅ A* (iso) and A × A* → A* → 1 is a coequalizer.
  The reasoning is analogous to [1.985] and [1.98(10)]. -/

/-- **§1.98(13) FREE RECURSOR EXISTENCE — the single residual of §1.98(13).**

    The A-action analogue of `recursor_exists_of_bicartesian`.  From bicartesian data
    `[unit,act] : 1 + A×α.obj ≅ α.obj` (and the terminal coequalizer `hcoeq`), §1.988
    produces, for every A-action `β`, a free homomorphism `h : α.obj → β.obj` with
    `α.unit ≫ h = β.unit` and `prodMap A α.obj β.obj h ≫ β.act = α.act ≫ h`.  As in the
    NNO case we bundle the `α.obj → α.obj`-instance UNIQUENESS (the free recursor into
    `α.obj` is `id`) to break the `peano ⟺ uniqueness` circularity; the GENERAL free
    recursor uniqueness is then re-derived from the action Peano property via the
    equalizer (`free_recursor_unique_of_bicartesian`).

    This EXISTENCE is the one missing §1.988 primitive — the SAME residual as
    `recursor_exists_of_bicartesian`, now for the A-parametrised functor `1 + A×(−)`.
    STATUS: NOT §1.543-capitalization (proven Sorry-free); the residual is the absent
    §1.988 partial-map-classifier free recursor. -/
theorem free_recursor_exists_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
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
  -- THE ONE RESIDUAL of §1.98(13): the §1.988 free recursion theorem (existence for
  -- every A-action β, and uniqueness of the `α.obj → α.obj` free recursor `= id`).
  -- The action Peano property, general free-recursor uniqueness, and the FreeAAction
  -- assembly are all derived from this Sorry-free below.
  sorry

/-- **§1.98(13) action PEANO PROPERTY.**  Every `(unit,act)`-closed subobject
    `B ↣ α.obj` is entire.  `B` closed = it allows `unit` (point `uB : 1 → B.dom`,
    `uB ≫ B.arr = α.unit`) and is `act`-stable (`actB : A×B.dom → B.dom`,
    `actB ≫ B.arr = prodMap A B.dom α.obj B.arr ≫ α.act`).

    PROOF (analogue of `peano_of_bicartesian`).  The free recursor
    (`free_recursor_exists_of_bicartesian` into `(B.dom, uB, actB)`) gives a SECTION
    `sec : α.obj → B.dom`; then `sec ≫ B.arr` and `id` are both free homomorphisms into
    `α.obj`, so the bundled `α.obj`-uniqueness forces `sec ≫ B.arr = id`, making `B.arr`
    a split epi; monic + split epi ⇒ iso. -/
theorem free_peano_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
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
  obtain ⟨uB, huB⟩ := huB
  obtain ⟨actB, hactB⟩ := hactB
  obtain ⟨hex, huniqα⟩ := free_recursor_exists_of_bicartesian A α hiso hcoeq
  -- Section `sec : α.obj → B.dom` via the free recursor into `(B.dom, uB, actB)`.
  obtain ⟨sec, hsec0, hsecs⟩ := hex { obj := B.dom, unit := uB, act := actB }
  -- `sec ≫ B.arr = id_{α.obj}` by the bundled `α.obj`-free-recursor uniqueness.
  have hsecB : sec ≫ B.arr = Cat.id α.obj := by
    apply huniqα
    · rw [← Cat.assoc, hsec0, huB]
    · -- prodMap A α.obj α.obj (sec≫B.arr) ≫ act
      --   = prodMap A α.obj B.dom sec ≫ (prodMap A B.dom α.obj B.arr ≫ act)
      --   = prodMap A α.obj B.dom sec ≫ actB ≫ B.arr
      --   = (act ≫ sec) ≫ B.arr = act ≫ (sec≫B.arr)
      rw [prodMap_comp, Cat.assoc, ← hactB, ← Cat.assoc, hsecs, Cat.assoc]
  -- `B.arr` split epi (retraction `sec`) + monic ⇒ iso.
  refine ⟨sec, ?_, hsecB⟩
  apply B.monic
  rw [Cat.assoc, hsecB, Cat.comp_id, Cat.id_comp]

/-- **§1.98(13) free-recursor UNIQUENESS** (via the equalizer + action Peano).
    Any two free homomorphisms `h, h' : α.obj → β.obj` are equal: their equalizer
    `E ↣ α.obj` is `(unit,act)`-closed, hence entire by `free_peano_of_bicartesian`,
    so the equalizer map is iso and left-cancels `h = h'`. -/
theorem free_recursor_unique_of_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
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
  have hEent : E.IsEntire := free_peano_of_bicartesian A α hiso hcoeq E hEu hEact
  obtain ⟨m', _, hm'm⟩ := hEent
  calc h = Cat.id α.obj ≫ h := (Cat.id_comp _).symm
    _ = (m' ≫ m) ≫ h := by rw [hm'm]
    _ = m' ≫ m ≫ h := Cat.assoc _ _ _
    _ = m' ≫ m ≫ h' := by rw [hm_eq]
    _ = (m' ≫ m) ≫ h' := (Cat.assoc _ _ _).symm
    _ = Cat.id α.obj ≫ h' := by rw [hm'm]
    _ = h' := Cat.id_comp _

/-- §1.98(13): Bicartesian characterization of a free A-action.
    An A-action (A*, e : 1 → A*, s : A × A* → A*) is FREE iff
    [(e, s)] : 1 + A × A* → A* is iso and p₂ : A × A* → A* → 1 is a coequalizer.
    (Analogue of §1.98(10); EXISTENCE of the free recursor is the §1.988 residual
    `free_recursor_exists_of_bicartesian`; UNIQUENESS is proved Sorry-free here.) -/
theorem free_action_iff_bicartesian {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]
    [HasBinaryCoproducts 𝒞] [HasImages 𝒞]
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
    obtain ⟨hex, _⟩ := free_recursor_exists_of_bicartesian A α hiso hcoeq
    obtain ⟨h, hh0, hhs⟩ := hex β
    exact ⟨h, ⟨hh0, hhs⟩, fun h' h0' hs' =>
      free_recursor_unique_of_bicartesian A α hiso hcoeq β h' h h0' hs' hh0 hhs⟩
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

/-- §1.98(14): In a topos with a NNO, every object A has a free A-action. -/
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
