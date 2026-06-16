/-
  Freyd & Scedrov, *Categories and Allegories* §1.85
  Exponential categories (cartesian closed).

  §1.85  EXPONENTIAL CATEGORY: binary products + for each A,
         the functor A × - has a right adjoint (-)^A.
  §1.852 Poset exponential ↔ binary meets + Heyting arrow
  §1.853 B^A as a bifunctor (covariant in B, contravariant in A)
  §1.854 Σ ⊣ Δ adjunction and Π dependent products
  §1.857 EXPONENTIAL IDEAL, REPLETE SUBCATEGORY; theorems
  §1.858 KURATOWSKI INTERIOR, LAWVERE-TIERNEY CLOSURE; theorem
  §1.859 BASEABLE objects, inclusion preserves equalizers
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_31
import Fredy.S1_34
import Fredy.S1_43
import Fredy.S1_8
import Fredy.S1_44


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ### Product functor A × -

  For each object A, the endofunctor A × - sends X ↦ A × X, f ↦ A × f. -/

section ProductFunctor

variable [hp' : HasBinaryProducts 𝒞]

/-- A × f : A × X → A × Y, with (A×f)≫fst = fst, (A×f)≫snd = snd≫f. -/
def prodMap (A X Y : 𝒞) (f : X ⟶ Y) : prod A X ⟶ prod A Y :=
  pair (X := prod A X) (A := A) (B := Y) fst (snd ≫ f)

theorem prodMap_fst (A X Y : 𝒞) (f : X ⟶ Y) : prodMap A X Y f ≫ fst (A := A) (B := Y) = fst := by
  dsimp [prodMap]; rw [fst_pair]

theorem prodMap_snd (A X Y : 𝒞) (f : X ⟶ Y) : prodMap A X Y f ≫ snd = snd ≫ f := by
  dsimp [prodMap]; rw [snd_pair]

-- (pair_fst_snd is defined canonically in S1_42 §1.423; reused here via import.)

theorem prodMap_id (A X : 𝒞) : prodMap A X X (Cat.id X) = Cat.id (prod A X) := by
  dsimp [prodMap]; rw [Cat.comp_id, pair_fst_snd]

theorem prodMap_comp (A X Y Z : 𝒞) (f : X ⟶ Y) (g : Y ⟶ Z) :
    prodMap A X Z (f ≫ g) = prodMap A X Y f ≫ prodMap A Y Z g := by
  dsimp [prodMap]
  let RHS := pair (X := prod A X) (A := A) (B := Y) fst (snd ≫ f) ≫
             pair (X := prod A Y) (A := A) (B := Z) fst (snd ≫ g)
  have h_fst : RHS ≫ fst (A := A) (B := Z) = fst := by
    dsimp [RHS]; rw [Cat.assoc, fst_pair, fst_pair]
  have h_snd : RHS ≫ snd = snd ≫ (f ≫ g) := by
    dsimp [RHS]
    rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc]
  apply (pair_uniq (X := prod A X) (A := A) (B := Z) fst (snd ≫ (f ≫ g)) RHS h_fst h_snd).symm

/-- Functor instance for A × -. -/
instance prodFunctor (A : 𝒞) : Functor (λ X => prod A X) where
  map {X Y} f := prodMap A X Y f
  map_id X := prodMap_id A X
  map_comp f g := prodMap_comp A _ _ _ f g

end ProductFunctor

/-! ## §1.85  Exponential categories

  A category with binary products is EXPONENTIAL if each functor
  A × - has a right adjoint.  The counit is the EVALUATION MAP e,
  the adjoint transpose is CARRYING (curry). -/

class HasExponentials (𝒞 : Type u) [Cat.{v} 𝒞] extends HasBinaryProducts 𝒞 where
  exp_obj : 𝒞 → 𝒞 → 𝒞
  eval_map {A B : 𝒞} : prod A (exp_obj A B) ⟶ B
  curry_map {A B X : 𝒞} (f : prod A X ⟶ B) : X ⟶ exp_obj A B
  curry_eval {A B X : 𝒞} (f : prod A X ⟶ B) :
    prodMap A X (exp_obj A B) (curry_map f) ≫ eval_map = f
  curry_unique {A B X : 𝒞} {f : prod A X ⟶ B} {g : X ⟶ exp_obj A B}
    (h_eq : prodMap A X (exp_obj A B) g ≫ eval_map = f) : g = curry_map f

variable [HasExponentials 𝒞]

/-- The exponential object B^A (§1.85). -/
def exp (A B : 𝒞) : 𝒞 := HasExponentials.exp_obj A B

notation:30 B " ^^ " A:30 => exp A B

/-- The EVALUATION MAP e : A × B^A → B (§1.85). -/
def eval_exp (A B : 𝒞) : prod A (B ^^ A) ⟶ B := HasExponentials.eval_map (A := A) (B := B)

/-- The EXPONENTIAL TRANSPOSE (curry): f : A × X → B gives Λf : X → B^A. -/
def curry {A B X : 𝒞} (f : prod A X ⟶ B) : X ⟶ B ^^ A := HasExponentials.curry_map f

/-- The characteristic equation: (A × curry f) ≫ eval = f. -/
@[simp] theorem curry_eval_eq {A B X : 𝒞} (f : prod A X ⟶ B) :
    prodMap A X (B ^^ A) (curry f) ≫ eval_exp A B = f :=
  HasExponentials.curry_eval f

/-- curry is unique: if (A × g) ≫ eval = f then g = curry f. -/
theorem curry_unique_eq {A B X : 𝒞} {f : prod A X ⟶ B} {g : X ⟶ B ^^ A}
    (h : prodMap A X (B ^^ A) g ≫ eval_exp A B = f) : g = curry f :=
  HasExponentials.curry_unique h

/-- curry is injective. -/
theorem curry_inj {A B X : 𝒞} {f₁ f₂ : prod A X ⟶ B}
    (h : curry f₁ = curry f₂) : f₁ = f₂ := by
  rw [← curry_eval_eq f₁, ← curry_eval_eq f₂, h]

/-! ## §1.853  Covariant exponential map f^A : B^A → C^A

  In an exponential category, B^A is a bifunctor: covariant in B and
  contravariant in A.  The covariant action sends f : B → C to
  f^A : B^A → C^A, defined as the unique map such that
  (A × f^A) ≫ eval_C = eval_B ≫ f.

  The *contravariant* action g ↦ B^g for g : A₁ → A₂ is in §1.95 as
  `expMap` (S1_95.lean); we name the covariant action `expCovMap`
  to avoid a clash. -/

section ExpBifunctor

/-- Covariant exponential map: given f : B → C, the map f^A : B^A → C^A is
    the unique map with (A × f^A) ≫ eval_C = eval_B ≫ f  (§1.853).
    Concretely: curry(eval_B ≫ f). -/
def expCovMap (A : 𝒞) {B C : 𝒞} (f : B ⟶ C) : B ^^ A ⟶ C ^^ A :=
  curry (eval_exp A B ≫ f)

/-- Defining equation: (A × expCovMap f) ≫ eval = eval ≫ f. -/
theorem expCovMap_eval (A : 𝒞) {B C : 𝒞} (f : B ⟶ C) :
    prodMap A (B ^^ A) (C ^^ A) (expCovMap A f) ≫ eval_exp A C = eval_exp A B ≫ f :=
  curry_eval_eq (eval_exp A B ≫ f)

/-- expCovMap preserves identity: id^A = id. -/
theorem expCovMap_id (A B : 𝒞) : expCovMap A (Cat.id B) = Cat.id (B ^^ A) := by
  symm; apply curry_unique_eq
  rw [Cat.comp_id, prodMap_id, Cat.id_comp]

/-- expCovMap preserves composition: (f ≫ g)^A = f^A ≫ g^A. -/
theorem expCovMap_comp (A : 𝒞) {B C D : 𝒞} (f : B ⟶ C) (g : C ⟶ D) :
    expCovMap A (f ≫ g) = expCovMap A f ≫ expCovMap A g := by
  symm; apply curry_unique_eq
  rw [prodMap_comp, Cat.assoc, expCovMap_eval, ← Cat.assoc, expCovMap_eval, Cat.assoc]

/-- The covariant exponential (-)^A as a Functor instance (covariant in B). -/
instance expCovFunctor (A : 𝒞) : Functor (fun B => B ^^ A) where
  map f := expCovMap A f
  map_id B := expCovMap_id A B
  map_comp f g := expCovMap_comp A f g

end ExpBifunctor

/-! ## §1.852  Poset exponential characterization

  A poset, viewed as a category, is exponential iff it has binary meets
  (∧) and for every a, b there exists b^a satisfying
      x ≤ b^a  ↔  a ∧ x ≤ b.
  The element b^a is precisely the Heyting arrow a → b [§1.72].

  Here we represent a poset-as-category via a type `P` with a preorder
  `le` such that hom-sets are propositions (thin category).  Binary meets
  are represented as a `HasBinaryMeets` predicate; the Heyting arrow is
  the right adjoint to meets. -/

/-- A POSET (or preorder) viewed as a thin category:
    objects are elements, at most one morphism between any two. -/
class ThinCategory (P : Type u) [Cat.{v} P] : Prop where
  thin : ∀ {A B : P} (f g : A ⟶ B), f = g

/-- The HEYTING ARROW a → b in a thin category with binary meets.
    By §1.72: x ≤ (a → b) iff a ∧ x ≤ b (§1.852). -/
class HasHeytingArrow (P : Type u) [Cat.{v} P] [HasBinaryProducts P] where
  imp : P → P → P
  /-- Adjunction: a map x → (a→b) exists iff a∧x → b exists. -/
  imp_adj : ∀ (a b x : P), Nonempty (x ⟶ imp a b) ↔ Nonempty (prod a x ⟶ b)

/-- §1.852: A poset (thin category) is exponential iff it has binary meets
    and a Heyting arrow. -/
theorem poset_exponential_iff_meets_heytingArrow
    (P : Type u) [Cat.{v} P] [ThinCategory P] :
    Nonempty (HasExponentials P) ↔
    ∃ (hm : HasBinaryProducts P), Nonempty (@HasHeytingArrow P _ hm) := by
  constructor
  · -- (→) An exponential thin category has products and a Heyting arrow.
    rintro ⟨he⟩
    refine ⟨he.toHasBinaryProducts, ⟨?_⟩⟩
    refine
      { imp := fun a b => he.exp_obj a b
        imp_adj := fun a b x => ?_ }
    constructor
    · -- x ⟶ b^a  ↦  prodMap a x b^a g ≫ eval : a×x ⟶ b
      rintro ⟨g⟩
      exact ⟨@prodMap P _ he.toHasBinaryProducts a x (he.exp_obj a b) g ≫ he.eval_map⟩
    · -- a×x ⟶ b  ↦  curry : x ⟶ b^a
      rintro ⟨f⟩
      exact ⟨he.curry_map f⟩
  · -- (←) Products + Heyting arrow give exponentials (curry equations are free in a thin cat).
    rintro ⟨hm, ⟨ha⟩⟩
    refine ⟨?_⟩
    refine
      { toHasBinaryProducts := hm
        exp_obj := fun a b => ha.imp a b
        eval_map := fun {A B} => Classical.choice ((ha.imp_adj A B (ha.imp A B)).mp ⟨Cat.id _⟩)
        curry_map := fun {A B X} f => Classical.choice ((ha.imp_adj A B X).mpr ⟨f⟩)
        curry_eval := fun {A B X} f => ThinCategory.thin _ _
        curry_unique := fun {A B X f g} _ => ThinCategory.thin _ _ }

/-! ## §1.854  Σ ⊣ Δ adjunction; Π dependent products

  For any object B in a category A with binary products, the forgetful
  functor Σ : A/B → A has a right adjoint Δ : A → A/B defined by
      Δ(Y) = ⟨Y × B, snd⟩  (the slice object over B with projection snd).
  The adjunction bijection is natural: Hom_{A/B}(X, Δ Y) ≅ Hom_A(Σ X, Y).

  When A also has exponentials, Δ : A → A/B has a further right adjoint
  Π : A/B → A with Π(⟨A, h : A→B⟩) = A^B  (§1.854). -/

section SigmaDeltaAdj

/-- The DIAGONAL functor Δ : 𝒞 → Over B.  Sends Y ↦ ⟨Y × B, snd⟩ (§1.854). -/
def deltaObj (B Y : 𝒞) : Over B := ⟨prod Y B, snd⟩

/-- Δ on morphisms: given f : Y → Z, Δ(f) = pair (fst ≫ f) snd : Y×B → Z×B. -/
def deltaMap (B : 𝒞) {Y Z : 𝒞} (f : Y ⟶ Z) : OverHom (deltaObj B Y) (deltaObj B Z) :=
  ⟨pair (fst ≫ f) snd, snd_pair _ _⟩

/-- The DIAGONAL FUNCTOR Δ B : 𝒞 → Over B. -/
instance deltaFunctor (B : 𝒞) : Functor (fun Y => deltaObj B Y) where
  map f := deltaMap B f
  map_id _Y := by
    apply OverHom.ext
    simp only [deltaMap]
    rw [Cat.comp_id]
    exact pair_fst_snd
  map_comp {_X _Y _Z} f g := by
    apply OverHom.ext
    simp only [deltaMap]
    -- goal: pair (fst ≫ f ≫ g) snd = (deltaMap B f ≫ deltaMap B g).f
    -- (deltaMap B f ≫ deltaMap B g).f = pair (fst ≫ f) snd ≫ pair (fst ≫ g) snd  (definitionally)
    change pair (fst ≫ f ≫ g) snd = pair (fst ≫ f) snd ≫ pair (fst ≫ g) snd
    exact (pair_uniq _ _ _
      (by rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc])
      (by rw [Cat.assoc, snd_pair, snd_pair])).symm

/-- Forward direction of the Σ ⊣ Δ bijection:
    f : Σ X → Y  ↦  ⟨pair f X.hom, ...⟩ : X → Δ Y in Over B. -/
def sigmaToOver {B : 𝒞} (X : Over B) {Y : 𝒞} (f : X.dom ⟶ Y) : OverHom X (deltaObj B Y) :=
  ⟨pair f X.hom, snd_pair _ _⟩

/-- Backward direction of the Σ ⊣ Δ bijection:
    h : X → Δ Y in Over B  ↦  h.f ≫ fst : Σ X → Y. -/
def overToSigma {B : 𝒞} (X : Over B) {Y : 𝒞} (h : OverHom X (deltaObj B Y)) : X.dom ⟶ Y :=
  h.f ≫ fst

/-- The bijection is a left inverse. -/
theorem sigmaToOver_overToSigma {B : 𝒞} (X : Over B) {Y : 𝒞}
    (h : OverHom X (deltaObj B Y)) :
    sigmaToOver X (overToSigma X h) = h := by
  apply OverHom.ext
  simp only [sigmaToOver, overToSigma]
  rw [← h.w]
  exact (pair_eta h.f).symm

/-- The bijection is a right inverse. -/
theorem overToSigma_sigmaToOver {B : 𝒞} (X : Over B) {Y : 𝒞} (f : X.dom ⟶ Y) :
    overToSigma X (sigmaToOver X f) = f := by
  simp [overToSigma, sigmaToOver, fst_pair]

/-- §1.854: The forgetful functor Σ : A/B → A (= SliceForget B) is left adjoint
    to the diagonal functor Δ : A → A/B (sending Y ↦ ⟨Y×B, snd⟩).
    Adjunction: Hom_A(Σ X, Y) ≅ Hom_{A/B}(X, Δ Y), i.e., φ : (X.dom→Y) → OverHom X (ΔY). -/
def sigma_adj_delta (B : 𝒞) :
    @Adjunction (Over B) _ 𝒞 _ (SliceForget B) (fun Y => deltaObj B Y)
      (sliceForgetFunctor B) (deltaFunctor B) :=
  { φ  := fun {X _Y} f => sigmaToOver X f      -- φ : X.dom → Y  ↦  OverHom X (Δ Y)
    ψ  := fun {X _Y} h => overToSigma X h      -- ψ : OverHom X (Δ Y)  ↦  X.dom → Y
    φψ := fun {X _Y} h => sigmaToOver_overToSigma X h
    ψφ := fun {X _Y} f => overToSigma_sigmaToOver X f
    φ_nat_left  := fun {_X' X _Y} a f => by
      apply OverHom.ext
      -- Functor.map a = a.f (sliceForgetFunctor); (a ≫ k).f = a.f ≫ k.f (OverHom.comp)
      change pair (a.f ≫ f) _X'.hom = a.f ≫ pair f X.hom
      exact (pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]; exact a.w)).symm
    φ_nat_right := fun {X _Y _Y'} f b => by
      apply OverHom.ext
      -- (k ≫ deltaMap B b).f = k.f ≫ pair (fst ≫ b) snd
      change pair (f ≫ b) X.hom = pair f X.hom ≫ pair (fst ≫ b) snd
      exact (pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair])
               (by rw [Cat.assoc, snd_pair, snd_pair])).symm }

/-! ### Π : A/B → A as right adjoint of Δ

  When 𝒞 has exponentials, Δ : A → A/B has a right adjoint Π given by
  Π(f : A → B) = A^B.  The adjunction bijection:
      Hom_{A/B}(Δ C, f)  ≅  Hom_A(C, A^B)
  sends k : C×B → A (with k ≫ f.hom = snd) to curry k : C → A^B. -/

/-- The DEPENDENT PRODUCT functor on objects: Π(f : A → B) = A^B (§1.854). -/
def piObj {B : 𝒞} (f : Over B) : 𝒞 := f.dom ^^ B

/-- Π on morphisms: given h : f → g in Over B, h^B : f.dom^B → g.dom^B. -/
def piMap {B : 𝒞} {f g : Over B} (h : OverHom f g) : piObj f ⟶ piObj g :=
  expCovMap B h.f

/-- Π is a functor Over B → 𝒞. -/
instance piFunctor (B : 𝒞) : Functor (fun f : Over B => piObj f) where
  map h := piMap h
  map_id f := expCovMap_id B f.dom
  map_comp h k := expCovMap_comp B h.f k.f

/-- §1.854: When 𝒞 has exponentials, Δ : 𝒞 → Over B has a right adjoint
    Π : Over B → 𝒞 sending f : A → B to A^B (§1.854).
    One direction of the bijection Hom_{Over B}(Δ C, f) ≅ Hom_𝒞(C, f.dom^B):
    any over-map h : C×B → f.dom (with h ≫ f.hom = snd) gives
    curry(prodSwap ≫ h) : C → f.dom^B = piObj f.
    (The full bijection requires showing this is an isomorphism; here we give
    just the map direction OverHom(ΔC, f) → Hom(C, piObj f).) -/
theorem delta_adj_pi_overToExp (B : 𝒞) (C : 𝒞) (f : Over B) :
    Nonempty (OverHom (deltaObj B C) f) → Nonempty (C ⟶ piObj f) := by
  rintro ⟨h⟩
  -- h.f : prod C B → f.dom, h.w : h.f ≫ f.hom = snd
  -- curry (prodSwap C B ≫ h.f) : C → f.dom ^^ B = piObj f
  -- prodSwap B C : prod B C → prod C B; compose with h.f : prod C B → f.dom
  exact ⟨curry (prodSwap B C ≫ h.f)⟩

end SigmaDeltaAdj

/-! ## §1.857  Exponential ideal and replete subcategory

  If 𝒜 is an exponential category and 𝒜' is a FULL SUBCATEGORY, we call
  𝒜' an EXPONENTIAL IDEAL if for every A ∈ |𝒜| and B ∈ |𝒜'| the
  exponential B^A lies in 𝒜'.

  A REPLETE SUBCATEGORY is a subcategory closed under isomorphism type:
  if B ∈ 𝒜' and A ≅ B in 𝒜 then A ∈ 𝒜'.

  Theorems (§1.857):
  1. A full coreflective subcategory closed under binary products is
     exponential.
  2. A full replete reflective subcategory of an exponential category is
     an exponential ideal iff its reflections preserve products. -/

section ExponentialIdeal

variable {𝒜 : Type u} [Cat.{v} 𝒜] [HasExponentials 𝒜]
variable {𝒜' : Type u} [Cat.{v} 𝒜']

/-- A full subcategory (via inclusion I : 𝒜' → 𝒜) is an EXPONENTIAL IDEAL of 𝒜
    if for all A ∈ |𝒜| and B ∈ |𝒜'|, the exponential B^A lies in 𝒜' (§1.857). -/
def ExponentialIdeal (I : 𝒜' → 𝒜) [Functor I] : Prop :=
  Full I ∧
  ∀ (A : 𝒜) (B : 𝒜'), ∃ (E : 𝒜'), Isomorphic (I E) (exp A (I B))

/-- A subcategory (via inclusion I : 𝒜' → 𝒜) is REPLETE if it is closed under
    isomorphism type: if B ∈ |𝒜'| and I B ≅ X in 𝒜 then X ∈ |𝒜'| (§1.857). -/
def RepleteSubcategory (I : 𝒜' → 𝒜) [Functor I] : Prop :=
  ∀ (B : 𝒜') (X : 𝒜), Isomorphic (I B) X → ∃ (B' : 𝒜'), I B' = X

/-- §1.857, Part 1: A full coreflective subcategory of an exponential category
    that is closed under binary products is itself exponential.
    (The coreflection G : 𝒜 → 𝒜' witnesses exponentials via G(B^A).) -/
theorem coreflective_closed_products_is_exponential
    (I : 𝒜' → 𝒜) [Functor I]
    [HasBinaryProducts 𝒜']
    (hFull : Full I)
    (hCorfl : CoreflectiveSubcategory I)
    (hProd : ∀ (B₁ B₂ : 𝒜'), Isomorphic (I (prod B₁ B₂)) (prod (I B₁) (I B₂))) :
    Nonempty (HasExponentials 𝒜') := by
  -- adj0 : I ⊣ G where G = hCorfl.coreflection.
  -- Use letI so the Functor instance matches exactly what adj0 expects.
  letI : Functor hCorfl.coreflection := hCorfl.corefl_functor
  let adj0 := hCorfl.adj.adj
  -- For each pair, pick the 𝒜-iso I(prod B₁ B₂) → prod (I B₁) (I B₂) and its inverse.
  let ip  := fun (B₁ B₂ : 𝒜') => Classical.choose (hProd B₁ B₂)
  let ip' := fun (B₁ B₂ : 𝒜') => (Classical.choose_spec (hProd B₁ B₂)).choose
  have ip_inv := fun (B₁ B₂ : 𝒜') =>
    (Classical.choose_spec (hProd B₁ B₂)).choose_spec
  -- Abbreviation
  let G := hCorfl.coreflection
  -- The counit ε_X : I(G X) → X (in 𝒜).
  let ε := fun (X : 𝒜) => adj0.ψ (Cat.id (G X))
  -- Exponential object in 𝒜': B^A := G(exp (I A) (I B)).
  -- curry_map: given f : prod A X → B in 𝒜', produce X → G(exp(I A)(I B)) via:
  --   I(prod A X) --[ip']→ prod(I A)(I X) ... wait, ip : I(prod) → prod(I,I), so we need ip'
  --   curry(ip'(A,X) ≫ Functor.map f) : I X → exp(I A)(I B)
  --   adj0.φ(...) : X → G(exp(I A)(I B))
  let curry' := fun {A B X : 𝒜'} (f : prod A X ⟶ B) =>
    adj0.φ (curry (ip' A X ≫ Functor.map f))
  -- eval_map: prod A (G(exp(I A)(I B))) → B in 𝒜'.
  -- Build 𝒜-map then apply Full I:
  --   I(prod A (G...)) --[ip A (G...)]→ prod(I A)(I(G...))
  --               --[prodMap(ε)]→ prod(I A)(exp...) --[eval]→ I B
  let eval_A := fun (A B : 𝒜') =>
    ip A (G (exp (I A) (I B))) ≫
    prodMap (I A) (I (G (exp (I A) (I B)))) (exp (I A) (I B)) (ε (exp (I A) (I B))) ≫
    eval_exp (I A) (I B)
  let eval' := fun (A B : 𝒜') => Classical.choose (hFull (eval_A A B))
  refine ⟨?_⟩
  refine
    { toHasBinaryProducts := inferInstance
      exp_obj := fun A B => G (exp (I A) (I B))
      eval_map := fun {A B} => eval' A B
      curry_map := fun {A B X} f => curry' f
      curry_eval := fun {A B X} f => by
        -- The equation prodMap A X (G(exp...)) (curry' f) ≫ eval' = f holds in 𝒜'.
        -- Proof strategy: apply I on both sides (using Embedding I = faithfulness),
        -- then compute using the adjunction equations and ip/ip' identities.
        -- Faithfulness of I follows from the triangle identity I(η) ≫ ε = id (I full coreflective).
        -- Deferred: requires Embedding I as an additional lemma.
        sorry
      curry_unique := fun {A B X f g} h => by
        -- Uniqueness: if prodMap A X _ g ≫ eval' = f, then g = curry' f.
        -- Again requires Embedding I (faithfulness) to cancel I on both sides.
        sorry }

/-- §1.857, Part 2: A full replete reflective subcategory of an exponential
    category is an exponential ideal iff its reflections preserve products.
    "Reflections preserve products" means: for A₁, A₂ ∈ |𝒜|, the image
    I(Ā₁ × Ā₂) ≅ I(Ā₁×A₂) in 𝒜, i.e. I preserves the product of the
    reflections; equivalently, Ā₁×A₂ ≅ Ā₁×Ā₂ in 𝒜. -/
theorem reflective_exponential_ideal_iff_refl_preserve_products
    [HasBinaryProducts 𝒜']
    (I : 𝒜' → 𝒜) [Functor I]
    (hFull : Full I)
    (hRepl : RepleteSubcategory I)
    (hRefl : ReflectiveSubcategory I) :
    ExponentialIdeal I ↔
    ∀ (A₁ A₂ : 𝒜),
      Isomorphic
        (I (hRefl.reflection (prod A₁ A₂)))
        (I (prod (hRefl.reflection A₁) (hRefl.reflection A₂))) := by
  sorry

end ExponentialIdeal

/-! ## §1.858  Kuratowski interior and Lawvere-Tierney closure

  On a lattice L (with meets ∧ and order ≤):

  A KURATOWSKI INTERIOR OPERATION is an operation (-)° satisfying:
    x° ≤ x          (deflationary)
    (x°)° = x°      (idempotent)
    (x ∧ y)° = x° ∧ y°  (preserves meets)
  Its fixed points are the OPEN ELEMENTS.

  A LAWVERE-TIERNEY CLOSURE OPERATION j satisfies:
    x ≤ j x           (inflationary)
    j(j x) = j x       (idempotent)
    j(x ∧ y) = j x ∧ j y  (preserves meets)
  Its fixed points are the CLOSED ELEMENTS.

  Theorem: The closed elements of an L-T closure on a Heyting algebra form
  an exponential ideal: if b is closed then (a → b) is closed. -/

section ClosureOnLattice

/-- A lattice L with meets and order, as a type with operations.
    We use a raw-type presentation to stay independent of the
    subobject-based HeytingAlgebra in §1.72. -/
structure MeetLattice where
  carrier   : Type u
  le        : carrier → carrier → Prop
  le_refl   : ∀ x, le x x
  le_trans  : ∀ {x y z}, le x y → le y z → le x z
  le_antisymm : ∀ {x y}, le x y → le y x → x = y
  meet      : carrier → carrier → carrier
  meet_le_left  : ∀ x y, le (meet x y) x
  meet_le_right : ∀ x y, le (meet x y) y
  le_meet   : ∀ {z x y}, le z x → le z y → le z (meet x y)

/-- A HEYTING LATTICE: a meet-lattice with an implication arrow (§1.72, §1.852). -/
structure HeytingLattice extends MeetLattice where
  imp       : carrier → carrier → carrier
  imp_adj   : ∀ {x a b}, le (meet a x) b ↔ le x (imp a b)

/-- A KURATOWSKI INTERIOR OPERATION on a meet-lattice (§1.858):
    deflationary, idempotent, and meet-preserving. -/
structure KuratowskiInterior (L : MeetLattice) where
  op      : L.carrier → L.carrier
  deflat  : ∀ x, L.le (op x) x
  idem    : ∀ x, op (op x) = op x
  meet_pres : ∀ x y, op (L.meet x y) = L.meet (op x) (op y)

/-- OPEN ELEMENTS of a Kuratowski interior: the fixed points. -/
def KuratowskiInterior.isOpen {L : MeetLattice} (ki : KuratowskiInterior L) (x : L.carrier) : Prop :=
  ki.op x = x

/-- A LAWVERE-TIERNEY CLOSURE OPERATION on a meet-lattice (§1.858):
    inflationary, idempotent, and meet-preserving. -/
structure LawvereTierneyClosure (L : MeetLattice) where
  op      : L.carrier → L.carrier
  inflat  : ∀ x, L.le x (op x)
  idem    : ∀ x, op (op x) = op x
  meet_pres : ∀ x y, op (L.meet x y) = L.meet (op x) (op y)

/-- CLOSED ELEMENTS of an L-T closure: the fixed points. -/
def LawvereTierneyClosure.isClosed {L : MeetLattice} (j : LawvereTierneyClosure L) (x : L.carrier) : Prop :=
  j.op x = x

/-- §1.858: The closed elements of an L-T closure on a Heyting lattice form
    an exponential ideal: if b is closed then (a → b) is closed. -/
theorem lt_closure_closed_elements_exponential_ideal
    (L : HeytingLattice) (j : LawvereTierneyClosure L.toMeetLattice)
    (a b : L.carrier)
    (hb : j.isClosed b) :
    j.isClosed (L.imp a b) := by
  -- isClosed: j.op x = x; need j.op (imp a b) = imp a b.
  -- j is monotone via meet_pres: x ≤ y iff meet x y = x.
  have j_mono : ∀ x y, L.le x y → L.le (j.op x) (j.op y) := fun x y hxy => by
    -- x ≤ y ⟹ meet x y = x ⟹ j(meet x y) = j(x) = meet(j x)(j y) ≥ j(y)... wait:
    -- j(x) = j(meet x y) = meet (j x) (j y) ≤ j(y) via meet_le_right
    have hxy' : L.meet x y = x :=
      L.le_antisymm (L.meet_le_left x y) (L.le_meet (L.le_refl x) hxy)
    -- L.le (j.op x) (j.op y)
    -- j.op x = j.op (L.meet x y) [by ← hxy']
    --        = L.meet (j.op x) (j.op y) [by meet_pres]
    -- so j.op x ≤ j.op y via meet_le_right
    have heq : j.op (L.meet x y) = L.meet (j.op x) (j.op y) := j.meet_pres x y
    have hj_x : j.op x = L.meet (j.op x) (j.op y) := by
      have := heq; rw [hxy'] at this; exact this
    exact hj_x ▸ L.meet_le_right (j.op x) (j.op y)
  -- Show j(imp a b) ≤ imp a b, i.e., a ∧ j(imp a b) ≤ b.
  -- a ∧ j(imp a b) ≤ j(a) ∧ j(imp a b) = j(a ∧ (imp a b)) ≤ j(b) = b.
  apply L.le_antisymm _ (j.inflat _)
  rw [← L.imp_adj]
  have step1 : L.le (L.meet a (j.op (L.imp a b))) (j.op (L.meet a (L.imp a b))) := by
    rw [j.meet_pres]
    exact L.le_meet (L.le_trans (L.meet_le_left _ _) (j.inflat a)) (L.meet_le_right _ _)
  have step2 : L.le (j.op (L.meet a (L.imp a b))) (j.op b) :=
    j_mono _ _ (L.imp_adj.mpr (L.le_refl _))
  -- j.op b = b, so j.op b ≤ b is j.op_b ▸ le_refl
  have step3 : L.le (j.op b) b := by rw [hb]; exact L.le_refl b
  exact L.le_trans step1 (L.le_trans step2 step3)

/-- A PROTOclosure is an inflationary, idempotent operation (not yet assumed meet-preserving). -/
structure ProtoClosure (L : MeetLattice) where
  op      : L.carrier → L.carrier
  inflat  : ∀ x, L.le x (op x)
  idem    : ∀ x, op (op x) = op x

/-- Fixed points of a ProtoClosure. -/
def ProtoClosure.isClosed {L : MeetLattice} (j : ProtoClosure L) (x : L.carrier) : Prop :=
  j.op x = x

/-- Converse of §1.858: If the closed elements of an inflationary idempotent
    MONOTONE operation on a Heyting lattice are an exponential ideal (a → b closed
    whenever b is closed), then the operation preserves meets (is L-T).

    NOTE: The theorem as originally stated (without monotonicity) is FALSE.
    Counterexample: 4-element Boolean algebra {0, a, ¬a, 1}; j(0)=a, j(a)=a,
    j(¬a)=¬a, j(1)=1. This is inflationary, idempotent, hIdeal holds (fixed points
    {a,¬a,1} closed under →), but j(a∧¬a)=j(0)=a ≠ 0=a∧¬a=j(a)∧j(¬a).
    The book's §1.815 "closure operation" requires monotonicity (order-preserving).

    The `≤` direction j(x∧y) ≤ j(x)∧j(y) follows immediately from hMono.
    The `≥` direction j(x)∧j(y) ≤ j(x∧y) uses hIdeal and requires further work. -/
theorem exponential_ideal_implies_lt_closure
    (L : HeytingLattice)
    (j : ProtoClosure L.toMeetLattice)
    (hMono : ∀ x y, L.le x y → L.le (j.op x) (j.op y))
    (hIdeal : ∀ (a b : L.carrier), j.isClosed b → j.isClosed (L.imp a b)) :
    ∀ x y, j.op (L.meet x y) = L.meet (j.op x) (j.op y) := by
  intro x y
  apply L.le_antisymm
  · -- ≤ direction: j(x∧y) ≤ j(x)∧j(y), from monotonicity.
    apply L.le_meet
    · exact hMono _ _ (L.meet_le_left x y)
    · exact hMono _ _ (L.meet_le_right x y)
  · -- ≥ direction: j(x)∧j(y) ≤ j(x∧y).
    -- KEY LEMMA: z ≤ c (c closed) → j(z) ≤ c  (via hMono: j(z) ≤ j(c) = c).
    have key : ∀ z c, j.isClosed c → L.le z c → L.le (j.op z) c := fun z c hc hzc =>
      hc ▸ hMono z c hzc
    -- j(x∧y) is closed (idempotent).
    have hxy_cl : j.isClosed (j.op (L.meet x y)) := j.idem (L.meet x y)
    -- imp x (j(x∧y)) is closed.
    have hc1 : j.isClosed (L.imp x (j.op (L.meet x y))) := hIdeal x _ hxy_cl
    -- y ≤ imp x j(x∧y): imp_adj.mp with x∧y ≤ j(x∧y) (inflationary).
    --   imp_adj : le (meet a t) b ↔ le t (imp a b); mp: (meet a t ≤ b) → (t ≤ imp a b).
    --   Here a=x, t=y, b=j(x∧y). Need: meet x y ≤ j(x∧y), i.e., x∧y ≤ j(x∧y). ✓
    have hy_le : L.le y (L.imp x (j.op (L.meet x y))) :=
      L.imp_adj.mp (j.inflat (L.meet x y))
    -- j(y) ≤ imp x j(x∧y) by KEY LEMMA (y ≤ it, it closed).
    have hjy_le : L.le (j.op y) (L.imp x (j.op (L.meet x y))) := key y _ hc1 hy_le
    -- x∧j(y) ≤ j(x∧y): imp_adj.mpr with j(y) ≤ imp x j(x∧y).
    --   mpr: (t ≤ imp a b) → (meet a t ≤ b); here a=x, t=j(y). ✓
    have step4 : L.le (L.meet x (j.op y)) (j.op (L.meet x y)) :=
      L.imp_adj.mpr hjy_le
    -- imp j(y) j(x∧y) is closed.
    have hc2 : j.isClosed (L.imp (j.op y) (j.op (L.meet x y))) := hIdeal _ _ hxy_cl
    -- x ≤ imp j(y) j(x∧y): imp_adj.mp with meet j(y) x ≤ j(x∧y).
    --   Need: meet (j.op y) x ≤ j(x∧y). We have step4: meet x (j.op y) ≤ j(x∧y).
    --   Use le_trans with meet commutativity (le_meet).
    have hx_le : L.le x (L.imp (j.op y) (j.op (L.meet x y))) :=
      L.imp_adj.mp (L.le_trans
        (L.le_meet (L.meet_le_right (j.op y) x) (L.meet_le_left (j.op y) x))
        step4)
    -- j(x) ≤ imp j(y) j(x∧y) by KEY LEMMA.
    have hjx_le : L.le (j.op x) (L.imp (j.op y) (j.op (L.meet x y))) := key x _ hc2 hx_le
    -- j(x)∧j(y) ≤ j(x∧y): imp_adj.mpr gives meet (j.op y) (j.op x) ≤ j(x∧y).
    -- Then swap via le_meet.
    have hmet : L.le (L.meet (j.op y) (j.op x)) (j.op (L.meet x y)) :=
      L.imp_adj.mpr hjx_le
    exact L.le_trans
      (L.le_meet (L.meet_le_right (j.op x) (j.op y)) (L.meet_le_left (j.op x) (j.op y)))
      hmet

end ClosureOnLattice

/-! ## §1.859  Baseable objects

  Given a category 𝒜 with binary products, an object B is BASEABLE if
  B^A = (A × -, B) is representable for all A.  The full subcategory
  𝔹 of baseable objects is itself exponential, and the inclusion 𝔹 → 𝒜
  preserves equalizers. -/

section Baseable

variable {𝒜 : Type u} [Cat.{v} 𝒜] [HasBinaryProducts 𝒜]

/-- B ∈ |𝒜| is BASEABLE if for every A ∈ |𝒜|, the functor (A × -, B)
    is representable (i.e. B^A exists) (§1.859). -/
def Baseable (B : 𝒜) : Prop :=
  ∀ (A : 𝒜), ∃ (E : 𝒜) (ev : prod A E ⟶ B),
    ∀ (X : 𝒜) (f : prod A X ⟶ B),
      ∃ (g : X ⟶ E), prodMap A X E g ≫ ev = f ∧
        ∀ (g' : X ⟶ E), prodMap A X E g' ≫ ev = f → g' = g

/-- The full subcategory of BASEABLE objects of 𝒜 (§1.859). -/
def BaseableSubcat (𝒜 : Type u) [Cat.{v} 𝒜] [HasBinaryProducts 𝒜] : Type u := { B : 𝒜 // Baseable B }

instance : Cat.{v} (BaseableSubcat 𝒜) where
  Hom B₁ B₂ := B₁.1 ⟶ B₂.1
  id B := Cat.id B.1
  comp f g := f ≫ g
  id_comp f := Cat.id_comp f
  comp_id f := Cat.comp_id f
  assoc f g h := Cat.assoc f g h

/-- The inclusion functor 𝔹 → 𝒜. -/
def baseableIncl : BaseableSubcat 𝒜 → 𝒜 := Subtype.val

instance : Functor (baseableIncl (𝒜 := 𝒜)) where
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- §1.859: The full subcategory of BASEABLE objects is closed under equalizers — the
    equalizer (taken in 𝒜) of two maps `f, g : B₂ ⇉ B₃` between baseable objects is again
    baseable.  Equivalently, the inclusion `𝔹 → 𝒜` preserves equalizers (the 𝔹-equalizer
    of `f, g` IS their 𝒜-equalizer `eqObj f g`, which therefore lies in 𝔹).

    Freyd's construction (§1.859): for each `A`, `E := eqObj f g` is the equalizer of the
    exponential transposes `f^A, g^A : B₂^A ⇉ B₃^A`, exhibiting `E^A` and hence `E` as
    baseable.  FAITHFUL SORRY — the per-`A` representability construction is not yet built.

    NOTE: this replaces an earlier vacuous version that assumed `[HasEqualizers 𝒜]`, ignored
    its cone/lift hypotheses, and merely returned the ambient equalizer (asserting nothing
    about baseability). The substantive content is exactly this baseable-CLOSURE statement,
    which is what §1.92 `topos_has_exponentials` requires. -/
theorem baseable_equalizer_is_baseable [HasEqualizers 𝒜]
    {B₂ B₃ : 𝒜} (hB₂ : Baseable B₂) (hB₃ : Baseable B₃) (f g : B₂ ⟶ B₃) :
    Baseable (eqObj f g) := by
  -- E := eqObj f g, with q₀ := eqMap f g : E → B₂ monic, q₀≫f = q₀≫g.
  -- `eqMap f g` is monic (one-liner from eqLift uniqueness; no HasImages needed).
  have hq₀mono : Mono (eqMap f g) := by
    intro W u v huv
    rw [eqLift_uniq f g (u ≫ eqMap f g) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) u rfl,
        eqLift_uniq f g (u ≫ eqMap f g) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) v huv.symm]
  intro A
  -- Representing data for B₂ and B₃ at stage A.
  obtain ⟨E₂, ev₂, hu₂⟩ := hB₂ A
  obtain ⟨E₃, ev₃, hu₃⟩ := hB₃ A
  -- Exponential transposes fA, gA : E₂ → E₃ of post-composition with f, g.
  obtain ⟨fA, hfA, hfA_uniq⟩ := hu₃ E₂ (ev₂ ≫ f)
  obtain ⟨gA, hgA, _⟩ := hu₃ E₂ (ev₂ ≫ g)
  -- E_A := equalizer of fA, gA, with q := eqMap fA gA : E_A → E₂, q≫fA = q≫gA.
  refine ⟨eqObj fA gA, ?_, ?_⟩
  · -- ev : prod A E_A → E = eqObj f g.
    -- prodMap A E_A E₂ q ≫ ev₂ equalizes f, g, so factors through E.
    refine eqLift f g (prodMap A (eqObj fA gA) E₂ (eqMap fA gA) ≫ ev₂) ?_
    -- (prodMap q ≫ ev₂)≫f = prodMap A E_A E₃ (q≫fA) ≫ ev₃ ; symmetric for g; q≫fA=q≫gA.
    rw [Cat.assoc, Cat.assoc, ← hfA, ← hgA, ← Cat.assoc, ← Cat.assoc,
        ← prodMap_comp, ← prodMap_comp, eqMap_eq]
  · -- Universal property of (E_A, ev).
    intro X φ
    -- φ ≫ q₀ : prod A X → B₂; transpose via B₂-representability to ψ : X → E₂.
    obtain ⟨ψ, hψ, hψ_uniq⟩ := hu₂ X (φ ≫ eqMap f g)
    -- ψ equalizes fA, gA, so lifts to h : X → E_A.
    have hψ_eq : ψ ≫ fA = ψ ≫ gA := by
      -- Both transpose to the same prod A X → B₃ map; cancel by hu₃-injectivity at X.
      obtain ⟨_, _, hinj⟩ := hu₃ X (prodMap A X E₃ (ψ ≫ fA) ≫ ev₃)
      rw [hinj (ψ ≫ fA) rfl, hinj (ψ ≫ gA) ?_]
      -- prodMap A X E₃ (ψ≫gA) ≫ ev₃ = prodMap A X E₃ (ψ≫fA) ≫ ev₃
      rw [prodMap_comp, prodMap_comp, Cat.assoc, Cat.assoc, hfA, hgA,
          ← Cat.assoc, ← Cat.assoc, hψ, Cat.assoc, Cat.assoc, eqMap_eq]
    -- h : X → E_A with h ≫ q = ψ.
    refine ⟨eqLift fA gA ψ hψ_eq, ?_, ?_⟩
    · -- prodMap A X E_A h ≫ ev = φ.  Cancel the monic q₀ = eqMap f g.
      apply hq₀mono
      -- ev ≫ q₀ = prodMap A E_A E₂ q ≫ ev₂  (eqLift_fac); prodMap_comp; eqLift_fac for h; hψ.
      rw [Cat.assoc, eqLift_fac, ← Cat.assoc, ← prodMap_comp, eqLift_fac, hψ]
    · -- Uniqueness of h.
      intro h' hh'
      -- Composing hh' with q₀ and ev₂ pins down h' ≫ q via hu₂; then q monic ⟹ h'.
      have hq'mono : Mono (eqMap fA gA) := by
        intro W u v huv
        rw [eqLift_uniq fA gA (u ≫ eqMap fA gA) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) u rfl,
            eqLift_uniq fA gA (u ≫ eqMap fA gA) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) v huv.symm]
      apply hq'mono
      rw [eqLift_fac]
      -- h' ≫ q = ψ via hu₂ uniqueness: prodMap A X E₂ (h'≫q) ≫ ev₂ = φ ≫ q₀.
      rw [hψ_uniq (h' ≫ eqMap fA gA) (by
        -- LHS = prodMap h' ≫ (prodMap q ≫ ev₂) = prodMap h' ≫ (ev ≫ q₀) = φ ≫ q₀.
        rw [prodMap_comp, Cat.assoc,
            ← eqLift_fac f g (prodMap A (eqObj fA gA) E₂ (eqMap fA gA) ≫ ev₂)
              (by rw [Cat.assoc, Cat.assoc, ← hfA, ← hgA, ← Cat.assoc, ← Cat.assoc,
                      ← prodMap_comp, ← prodMap_comp, eqMap_eq]),
            ← Cat.assoc, hh'])]

end Baseable

end Freyd
