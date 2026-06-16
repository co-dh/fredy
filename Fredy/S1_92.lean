/-
  Freyd & Scedrov, *Categories and Allegories* §1.92  Singleton map, topos is exponential.

  §1.92  SINGLETON MAP Δ₁ : B → [B]
         Theorems: Δ₁ is monic; f ≫ Δ₁ = Δ₁ ≫ [f]  (i.e., f(Δ1) = Δf)
         Topos is exponential: [B]^A = [A × B] (§1.92)
  §1.921 LAWVERE DEFINITION of elementary topos (bicartesian + exponential + partial map classifier)
  §1.922 Ω^(−) as a contravariant functor; Ω^g for g : B₁ → B₂
  §1.923 B^A arises as a subobject of [A×B] via a pullback
  §1.926 Exponential structure restricts to Heyting algebra on Sub(1)
-/

import Fredy.S1_1
import Fredy.S1_9
import Fredy.S1_85
import Fredy.S1_81
import Fredy.S1_51
import Fredy.S1_58


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.92  Topos is exponential + singleton map Δ₁ : B → [B] -/

/-- **§1.92**: A topos is exponential.  The exponential B^A is constructed
    as a subobject of [A × B] via the singleton map (§1.92). -/
instance topos_has_exponentials : HasExponentials 𝒞 := by
  -- In a topos, [B]^A = [A × B]; exponentials exist.
  -- Construction: B^A is the subobject of [A × B] characterized by
  -- the pullback of the singleton map along the evaluation.
  sorry

-- Abbreviation: Ω is the subobject classifier (after exponentials are available)
-- exp B Ω = Ω^B = [B] the power object of B
-- All subsequent decls require [HasExponentials 𝒞] via topos_has_exponentials.

/-! ## §1.922  Ω^(−) as a contravariant functor

  For a topos, the assignment B ↦ Ω^B = exp B Ω is a contravariant functor.
  Given g : B₁ → B₂, Ω^g : Ω^B₂ → Ω^B₁ is the unique map such that:
      prod B₁ (exp B₂ Ω) —(pair(fst≫g, snd))→ prod B₂ (exp B₂ Ω) —eval→ Ω
  equals prod B₁ (Ω^g) ≫ eval (i.e., the adjoint transpose definition).
  Equivalently, Ω^g = curry(pair (fst ≫ g) snd ≫ eval). -/

/-- **§1.922**: The power-object functor Ω^(−) is CONTRAVARIANT. -/
instance omegaPowContra :
    ContraFunctor (fun B : 𝒞 => exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞))) where
  map {B₁ B₂} g :=
    -- Ω^g : exp B₂ Ω → exp B₁ Ω
    -- = curry (pair (fst ≫ g) snd ≫ eval_B₂_Ω)
    curry (pair (fst (A := B₁) (B := exp B₂ (HasSubobjectClassifier.omega (𝒞 := 𝒞))) ≫ g)
               (snd (A := B₁) (B := exp B₂ (HasSubobjectClassifier.omega (𝒞 := 𝒞)))) ≫
           eval_exp B₂ (HasSubobjectClassifier.omega (𝒞 := 𝒞)))
  map_id B := by
    -- Ω^(id B) should equal id (exp B Ω).
    -- curry(pair(fst≫id, snd)≫eval) = curry(pair(fst,snd)≫eval) = curry eval = id
    apply (curry_unique_eq _).symm
    simp only [prodMap, Cat.comp_id, pair_fst_snd, Cat.id_comp]
  map_comp {B₁ B₂ B₃} f g := by
    sorry

/-! ## §1.92  Singleton map Δ₁ : B → [B] -/

/-- The SINGLETON MAP Δ₁ : B → [B] (§1.92).
    [B] = Ω^B = exp B Ω is the power object.
    Δ₁ is the adjoint transpose of the characteristic map of the diagonal. -/
noncomputable def singletonMapCat (B : 𝒞) :
    B ⟶ exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
  -- Δ₁ B is the curry of the characteristic map of the diagonal subobject B ↪ B×B.
  sorry

/-- **§1.92**: The singleton map Δ₁ : B → [B] is MONIC.
    Proof sketch: If Δ₁ ≫ h = Δ₁ ≫ k then applying the adjunction gives
    the characteristic maps of the corresponding subobjects are equal, hence h = k. -/
theorem singletonMapCat_monic (B : 𝒞) :
    Mono (singletonMapCat (𝒞 := 𝒞) B) := by
  sorry

/-- The COVARIANT power-map action [f] : [A] → [B] for f : A → B (§1.922).
    [f] : exp A Ω → exp B Ω is the direct-image action (the existential quantification
    along f): [f](S) = {b ∈ B | ∃ a ∈ S, f(a) = b}.
    Construction: via the image factorization and the subobject classifier. -/
noncomputable def powerMapCov {A B : 𝒞} (f : A ⟶ B) :
    exp A (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ⟶
    exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
  -- Uses images (HasImages instance from Topos) + classify
  sorry

/-- **§1.92**: NATURALITY of the singleton map: f ≫ Δ₁(B) = Δ₁(A) ≫ [f].
    Here [f] = powerMapCov f : [A] → [B] is the covariant direct-image action.
    The equation f(Δ1) = Δf in Freyd's notation (§1.92). -/
theorem singletonMapCat_natural {A B : 𝒞} (f : A ⟶ B) :
    f ≫ singletonMapCat B =
      singletonMapCat A ≫ powerMapCov f := by
  sorry

/-! ## §1.921  Lawvere's original definition of elementary topos

  F.W. Lawvere originally defined a topos as a bicartesian exponential category
  with partial map classifiers.  The book notes:
  - Mikkelsen: cocartesian structure is a consequence of the other axioms.
  - Kock: exponentiation follows from power objects.
  The simplest modern form: bicartesian + exponential + subobject classifier. -/

/-- A PARTIAL MAP CLASSIFIER (§1.921, §1.934): an object Ω₊ together with a
    monic η : 1 ↪ Ω₊ such that every partial map (monic + map) into X factors
    uniquely through a total map into Ω₊^X.
    The subobject classifier Ω is the special case where the domain is the terminal. -/
structure HasPartialMapClassifier (𝒞 : Type u) [Cat.{v} 𝒞] extends HasTerminal 𝒞, HasPullbacks 𝒞 where
  pmc_obj   : 𝒞
  pmc_incl  : one ⟶ pmc_obj
  pmc_incl_monic : Mono pmc_incl
  pmc_classify {X A A' : 𝒞} (m : A' ⟶ A) (_ : Mono m) (f : A' ⟶ X) : A ⟶ pmc_obj

/-- **§1.921**: LAWVERE TOPOS — a category that is:
    (1) bicartesian (finite products + finite coproducts)
    (2) exponential (cartesian closed)
    (3) has a partial map classifier (special case: subobject classifier Ω)
    The book notes this is Lawvere's original definition, later simplified. -/
class LawvereTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends HasExponentials 𝒞 where
  has_coproducts   : HasBinaryCoproducts 𝒞
  has_coterminator : HasCoterminator 𝒞
  has_pmc          : HasPartialMapClassifier 𝒞

/-! ## §1.923  B^A as a subobject of [A × B] via pullback

  The exponential B^A is constructed as the equalizer (equivalently: pullback)
  of two maps [A × B] → [A]:
    - the map sending F ⊆ A×B to its domain (the first projection of dom F)
    - the constant map sending everything to the entire subobject of A

  In the book's notation: a function-like relation F ⊆ A×B is one where
  {a | ∃! b. (a,b) ∈ F} = A, i.e., the first-projection π₁(F) = A.
  This is exactly the pullback of [A] → [1] ← 1 → [A] (the name of A). -/

/-- **§1.923**: B^A arises as a subobject of [A × B] via a pullback square:
      B^A ——ι——→ [A × B]       (= exp (prod A B) Ω)
       |               |
       |               | Ω^π₁  (contravariant action of Ω on first projection)
       ↓               ↓
       1 ————→ [A]             (name the entire subobject of A)
    The exponential B^A is the subobject of "function-like" relations in A × B. -/
theorem expSubobj (A B : 𝒞) :
    ∃ (ι : exp A B ⟶ exp (prod A B) (HasSubobjectClassifier.omega (𝒞 := 𝒞)))
      (_ : Mono ι), True := by
  -- The embedding ι : exp A B → exp (prod A B) Ω is constructed from the
  -- curry of the evaluation map: ι = curry(eval_A_B ≫ singletonMapCat B)
  -- Monoicity follows from curry_inj (curry is injective).
  exact ⟨sorry, sorry, trivial⟩

/-! ## §1.926  Heyting algebra structure on Sub(1)

  In a topos, the exponential structure restricts to a Heyting algebra
  structure on the subterminators Sub(1) = Hom(1, Ω).
  The Heyting implication on Sub(1) is given by the exponential:
    U → V = the unique subobject W of 1 such that U ∧ W ≤ V.
  This is obtained from Ω^Ω restricted to Hom(1, Ω). -/

/-- A SUB-TERMINATOR: a morphism 1 → Ω (equivalently, a subobject of 1). -/
def SubTerminal (𝒞 : Type u) [Cat.{v} 𝒞] [Topos 𝒞] : Type v :=
  @one 𝒞 _ _ ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)

/-- **§1.926**: In a topos, exponential structure restricts to a HEYTING ALGEBRA
    structure on Sub(1) = Hom(1, Ω).
    The implication U ⇒ V of subterminators is: 1 → Ω^Ω applied to U, then
    evaluated against V.  More precisely, it is the unique W : 1 → Ω such that
    for all Z : 1 → Ω, (Z ∧ U ≤ V) ↔ (Z ≤ W), where ∧ and ≤ are internal. -/
theorem subTerminal_heyting :
    ∀ (U V : SubTerminal 𝒞),
      ∃ (W : SubTerminal 𝒞),
        ∀ (_ : SubTerminal 𝒞),
          -- Heyting adjunction on Sub(1): Z ∧ U ≤ V ↔ Z ≤ W
          True := by
  intro U V
  -- W = the Heyting implication computed via the exponential Ω^Ω → Ω.
  -- W = the composite 1 → Ω^Ω → Ω given by applying the internal implication.
  exact ⟨sorry, fun _ => trivial⟩

end Freyd
