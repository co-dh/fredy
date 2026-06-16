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

/-! ## §1.974  AC ↔ IAC + projective terminal

  §1.974: A topos is AC (all objects are projective / choice) iff it is IAC
  and 1 is projective.

  One direction: given an epic f : A → B in an IAC topos with projective 1,
  pull f back along itself to get f×f : A×_B A → B×_B B ≅ B; the pullback
  projection A×_B A → A is epic (pullbacks preserve epics in IAC), so
  B→ is well-supported, and since 1 is projective there is a point, giving a
  right-inverse to f.

  The other direction: AC implies every object is projective (cover = split
  epi by definition), so 1 is projective; and AC implies IAC (exponentials
  preserve left-invertible maps and every epic is left-invertible in AC). -/

/-- §1.974: A topos is AC iff it is IAC and the terminal object 1 is projective. -/
theorem ac_iff_iac_and_projective_one [HasExponentials 𝒞] [HasImages 𝒞] :
    (∀ (C : 𝒞), Projective C) ↔
    (IsIAC 𝒞 ∧ Projective (one (𝒞 := 𝒞))) := by
  sorry

/-! ## §1.981  NNO iterate for pairs

  §1.981: If 1 →⁰ N →ˢ N is a NNO, then for every A →ᵃ B ←ᵇ B there
  exists a unique A × N → B such that the two triangles commute.
  This is obtained by transposing through the exponential adjunction. -/

/-- Absorbing a `pair` into the product functor: `⟨f,g⟩ ≫ (A × h) = ⟨f, g≫h⟩`. -/
theorem pair_prodMap {𝒞 : Type u} [Cat.{v} 𝒞] [HasBinaryProducts 𝒞]
    {A X Y W : 𝒞} (f : W ⟶ A) (g : W ⟶ X) (h : X ⟶ Y) :
    pair f g ≫ prodMap A X Y h = pair f (g ≫ h) := by
  apply pair_uniq
  · rw [Cat.assoc, prodMap_fst, fst_pair]
  · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair]

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
  sorry

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
  sorry

/-- §1.987: Existence of least subobject with Peano property.
    Given a : 1 → A and t : A → A, there is a least subobject A' ↣ A
    that allows a and is stable under t, and A' has the Peano property.
    The Peano property for A' is stated with respect to the induced morphisms
    a' = term A'.dom ≫ A'.arr ≫ ... restricted to A'. -/
theorem least_peano_subobject {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞] [HasImages 𝒞]
    {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) :
    ∃ (A' : Subobject 𝒞 A),
      Allows A' a ∧
      (∃ (t' : A'.dom ⟶ A'.dom), t' ≫ A'.arr = A'.arr ≫ t) ∧
      (∀ (B : Subobject 𝒞 A), Allows B a →
        (∃ (tB : B.dom ⟶ B.dom), tB ≫ B.arr = B.arr ≫ t) → A'.le B) := by
  sorry

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
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞] :
    Nonempty (FreeAAction (𝒞 := 𝒞) one) := by
  sorry

/-! ## §1.98(10)  Bicartesian characterization of NNO

  §1.98(10): In any topos, if 1 →ᵃ A ←ᵗ A is such that [a, t] : 1 + A → A is
  an isomorphism and A → A → 1 is a coequalizer of (t, id_A), then 1 →ᵃ A →ᵗ A
  is a NNO.

  The Peano property follows from §1.988 (or its generalization, cited as [2.542]
  in the book) and the NNO uniqueness and existence conditions are verified from
  the bicartesian data.  We record the statement here with a sorry pending the
  Peano property infrastructure from §1.988. -/

/-- §1.98(10): If [a, t] : 1 + A → A is iso and A → 1 is a coequalizer of (t, id_A),
    then 1 →ᵃ A →ᵗ A is a NNO. -/
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
  sorry

/-! ## §1.98(11)  Bicartesian functors preserve NNO

  §1.98(11): If T : 𝒜 → 𝒜' is a bicartesian functor (preserves finite limits
  and colimits) and 1 →⁰ N →ˢ N is a NNO in 𝒜, then 1 → T N → T N is a NNO
  in 𝒜'.

  This follows from the bicartesian characterization [1.985, 1.98(10)]:
  the coproduct 1 + N ≅ N and coequalizer properties are preserved by T. -/

/-- §1.98(11): A bicartesian functor preserves the NNO.
    The bicartesian characterization [1.985, 1.98(10)] is preserved by any
    functor that preserves finite products, coproducts, and coequalizers. -/
theorem bicartesian_functor_preserves_nno
    {𝒜 : Type u} [Cat.{v} 𝒜] [hN : HasNaturalNumbersObject 𝒜]
    [HasBinaryCoproducts 𝒜] [HasImages 𝒜]
    {𝒜' : Type u} [Cat.{v} 𝒜'] [Topos 𝒜'] [HasBinaryCoproducts 𝒜'] [HasImages 𝒜']
    (T : 𝒜 → 𝒜') [hT : Functor T]
    -- T preserves the NNO iso [0, s] : 1 + N → N (bicartesian functors do this)
    (hT_iso : IsIso (hT.map (HasBinaryCoproducts.case hN.zero hN.succ
        (A := one) (B := hN.nno) (X := hN.nno))))
    -- T preserves the terminal coequalizer (bicartesian functors preserve colimits)
    (hT_coeq : ∀ (X : 𝒜') (f : T hN.nno ⟶ X),
      hT.map hN.succ ≫ f = f →
      ∃ g : one ⟶ X, term (T hN.nno) ≫ g = f ∧
        ∀ g' : one ⟶ X, term (T hN.nno) ≫ g' = f → g' = g) :
    Nonempty (HasNaturalNumbersObject 𝒜') := by
  sorry

/-! ## §1.98(13)  Bicartesian characterization of free A-action

  §1.98(13): The analogue of the bicartesian characterization [1.985, 1.98(10)]
  holds for a free A-action A*: namely A × 1 →(1,e)→ A × A* →s→ A* is a free
  A-action iff [1 + A × A*, A*] ≅ A* (iso) and A × A* → A* → 1 is a coequalizer.
  The reasoning is analogous to [1.985] and [1.98(10)]. -/

/-- §1.98(13): Bicartesian characterization of a free A-action.
    An A-action (A*, e : 1 → A*, s : A × A* → A*) is FREE iff
    [(e, s)] : 1 + A × A* → A* is iso and p₂ : A × A* → A* → 1 is a coequalizer.
    (Analogue of §1.98(10); proof omitted pending §1.988 infrastructure.) -/
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
  sorry

/-! ## §1.98(14)  Existence of free A-action from NNO

  §1.98(14): In a topos with a NNO, for any object A there exists a free A-action.
  The construction uses primRec (or iteratePair) applied to A: the free A-action
  A* is the A-fold "list" object built from the NNO universal property. -/

/-- §1.98(14): In a topos with a NNO, every object A has a free A-action. -/
theorem free_action_exists {𝒞 : Type u} [Cat.{v} 𝒞]
    [hN : HasNaturalNumbersObject 𝒞] [HasExponentials 𝒞]
    (A : 𝒞) : Nonempty (FreeAAction (𝒞 := 𝒞) A) := by
  sorry

end Freyd
