/-
  Freyd & Scedrov, *Categories and Allegories* §1.36–§1.367
  Inflation, strong equivalence, equivalent categories, equivalence kernel, factorization.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31
import Fredy.S1_41


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.36 Inflation

  An INFLATION of B is a category [T] with objects 𝛂, an onto function
  T: 𝛂 → |B|, and morphisms A → B defined as the most inclusive
  (when TA = □x and TB = x□).  The forgetful functor [T] → B is
  a full embedding and onto, hence an equivalence functor. -/

/-- An inflation: artificially replicate objects of B.  Given T : 𝛂 → |B| onto,
    the category [T] has objects 𝛂, hom 𝛂(A,B) = B(TA,TB). -/
structure Inflation (B : 𝒞) where
  objSet  : Type u
  T       : objSet → 𝒞
  isOnto  : ∀ b : 𝒞, ∃ a : objSet, T a = b  -- T is surjective (onto)

/-- The inflated category [T] with objects objSet and hom via T. -/
instance (B : 𝒞) (I : Inflation B) : Cat.{v} I.objSet where
  Hom A B := I.T A ⟶ I.T B
  id A := Cat.id (I.T A)
  comp f g := f ≫ g
  id_comp _ := Cat.id_comp _
  comp_id _ := Cat.comp_id _
  assoc _ _ _ := Cat.assoc _ _ _

/-- The inflation forgetful functor F : [T] → B, which is a full embedding. -/
def Inflation.forget (B : 𝒞) (I : Inflation B) : I.objSet → 𝒞 := I.T

instance (B : 𝒞) (I : Inflation B) : Functor (I.forget B) where
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An inflation cross-section: S : |B| → 𝛂 with T∘S = id. -/
structure InflationCrossSection (B : 𝒞) (I : Inflation B) where
  S : 𝒞 → I.objSet
  sec : ∀ b : 𝒞, I.T (S b) = b

/-! ## §1.362 Strong equivalence from inflation

  The axiom of choice implies every inflation is strongly equivalent to B.
  (We state the condition without assuming AC.) -/

/-- Transport of an identity morphism along an object equality `e : X = Y`.
    This is the canonical iso `X ⟶ Y` witnessing `X = Y` in any category. -/
def eqToHom {X Y : 𝒞} (e : X = Y) : X ⟶ Y := e ▸ Cat.id X

@[simp] theorem eqToHom_refl (X : 𝒞) : eqToHom (rfl : X = X) = Cat.id X := rfl

theorem eqToHom_trans {X Y Z : 𝒞} (e : X = Y) (e' : Y = Z) :
    eqToHom e ≫ eqToHom e' = eqToHom (e.trans e') := by
  cases e; cases e'; exact Cat.id_comp _

theorem eqToHom_comp_eqToHom_symm {X Y : 𝒞} (e : X = Y) :
    eqToHom e ≫ eqToHom e.symm = Cat.id X := by cases e; exact Cat.id_comp _

theorem eqToHom_symm_comp_eqToHom {X Y : 𝒞} (e : X = Y) :
    eqToHom e.symm ≫ eqToHom e = Cat.id Y := by cases e; exact Cat.id_comp _

/-- The cross-section functor `𝒞 → [T]`, sending `b ↦ S b`.  On a map `h : X ⟶ Y`
    it returns `h` transported along `S.sec : I.T (S X) = X` at each endpoint, since
    `Hom` in `[T]` between `S X` and `S Y` is `I.T (S X) ⟶ I.T (S Y)`. -/
instance csFunctor (B : 𝒞) (I : Inflation B) (S : InflationCrossSection B I) :
    Functor (fun b : 𝒞 => S.S b) where
  map {X Y} h := (eqToHom (S.sec X) ≫ h ≫ eqToHom (S.sec Y).symm :
    I.T (S.S X) ⟶ I.T (S.S Y))
  map_id X := by
    show eqToHom (S.sec X) ≫ Cat.id X ≫ eqToHom (S.sec X).symm = Cat.id (I.T (S.S X))
    rw [Cat.id_comp, eqToHom_comp_eqToHom_symm]
  map_comp {X Y Z} f g := by
    show eqToHom (S.sec X) ≫ (f ≫ g) ≫ eqToHom (S.sec Z).symm
      = (eqToHom (S.sec X) ≫ f ≫ eqToHom (S.sec Y).symm)
        ≫ (eqToHom (S.sec Y) ≫ g ≫ eqToHom (S.sec Z).symm)
    simp only [Cat.assoc]
    rw [← Cat.assoc (eqToHom (S.sec Y).symm) (eqToHom (S.sec Y)),
        eqToHom_symm_comp_eqToHom, Cat.id_comp]

/-- If T has a left-inverse (a cross-section S), then the forgetful functor `[T] → B`
    and the cross-section functor `b ↦ S b` constitute a strong equivalence (§1.362). -/
theorem inflation_strong_equiv (B : 𝒞) (I : Inflation B) (S : InflationCrossSection B I) :
    StrongEquivalence (I.forget B) (fun b : 𝒞 => S.S b) where
  -- unit : NatIso ((csFunctor) ∘ forget) id  on  [T].
  -- component at `a : I.objSet` lives in [T], i.e. is a map I.T (S (I.T a)) ⟶ I.T a in 𝒞.
  unit := ⟨{
    nat := {
      app a := (eqToHom (S.sec (I.T a)) : I.T (S.S (I.T a)) ⟶ I.T a)
      naturality {a a'} f := by
        show (eqToHom (S.sec (I.T a)) ≫ f ≫ eqToHom (S.sec (I.T a')).symm)
            ≫ eqToHom (S.sec (I.T a')) = eqToHom (S.sec (I.T a)) ≫ f
        rw [Cat.assoc, Cat.assoc, eqToHom_symm_comp_eqToHom, Cat.comp_id]
    }
    isIso a := ⟨(eqToHom (S.sec (I.T a)).symm : I.T a ⟶ I.T (S.S (I.T a))),
      eqToHom_comp_eqToHom_symm _, eqToHom_symm_comp_eqToHom _⟩
  }⟩
  -- counit : NatIso (forget ∘ csFunctor) id  on  𝒞.
  -- forget (csFunctor b) = I.T (S b); component at `b` is I.T (S b) ⟶ b via S.sec.
  counit := ⟨{
    nat := {
      app b := (eqToHom (S.sec b) : I.T (S.S b) ⟶ b)
      naturality {b b'} f := by
        show (eqToHom (S.sec b) ≫ f ≫ eqToHom (S.sec b').symm)
            ≫ eqToHom (S.sec b') = eqToHom (S.sec b) ≫ f
        rw [Cat.assoc, Cat.assoc, eqToHom_symm_comp_eqToHom, Cat.comp_id]
    }
    isIso b := ⟨eqToHom (S.sec b).symm,
      eqToHom_comp_eqToHom_symm _, eqToHom_symm_comp_eqToHom _⟩
  }⟩

/-! ## §1.366 Equivalence kernel

  The kernel of an equivalence functor T : A → B is the subcategory 𝓚 ⊆ A
  of maps sent by T to identity maps.  𝓚 is:
  1. Contains all identity maps
  2. A groupoid (every map is iso with inverse in 𝓚)
  3. A pre-order (at most one map A → B)
  Any such subcategory is an EQUIVALENCE KERNEL. -/

/-- An equivalence kernel: a set of maps K ⊆ Mor(A) satisfying:
    1. id_X ∈ K for all X
    2. If f ∈ K then f is iso and f⁻¹ ∈ K
    3. There is at most one K-map between any two objects. -/
structure EquivalenceKernel (𝒞 : Type u) [Cat.{v} 𝒞] where
  mem    : {X Y : 𝒞} → (X ⟶ Y) → Prop
  mem_id : ∀ X : 𝒞, mem (Cat.id X)
  isGroupoid : ∀ {X Y : 𝒞} (f : X ⟶ Y), mem f → (∃ g : Y ⟶ X, mem g ∧ f ≫ g = Cat.id X ∧ g ≫ f = Cat.id Y)
  isPreorder : ∀ {X Y : 𝒞} (f g : X ⟶ Y), mem f → mem g → f = g

/-- The kernel of an equivalence functor `T`: the maps `T` sends to identities.

    A map sent to an identity necessarily has equal `T`-images of its endpoints,
    so membership bundles that object equality `e : F X = F Y` alongside the
    `HEq` witnessing `T f = 1`.  Proving the kernel is a *groupoid* genuinely
    needs `T` to be a full embedding (the book's equivalence functor): fullness
    lifts the inverse identity to a map `g : Y → X`, and the embedding (faithful)
    transports `T(fg) = 1 = T(1)` back to `fg = 1`. -/
def equivalenceKernel (F : 𝒞 → 𝒟) [hF : Functor F] (emb : Embedding F) (full : Full F) :
    EquivalenceKernel 𝒞 where
  mem {X Y} f := ∃ _ : F X = F Y, HEq (hF.map f) (Cat.id (F X))
  mem_id X := ⟨rfl, heq_of_eq (hF.map_id X)⟩
  isGroupoid {X Y} f h := by
    obtain ⟨e, hf⟩ := h
    -- `cases` on an object-equality only fires when one side is a free variable,
    -- so we package the needed transports as little lemmas over a fresh endpoint.
    have key : ∀ {P Q : 𝒟} (mf : P ⟶ Q) (mg : Q ⟶ P), P = Q →
        HEq mf (Cat.id P) → HEq mg (Cat.id P) → mf ≫ mg = Cat.id P := by
      intro P Q mf mg e' hmf hmg; cases e'
      rw [eq_of_heq hmf, eq_of_heq hmg]; exact Cat.id_comp _
    have idHEq : HEq (Cat.id (F X)) (Cat.id (F Y)) := by
      have h' : ∀ {Q : 𝒟}, F X = Q → HEq (Cat.id (F X)) (Cat.id Q) := by
        intro Q e'; cases e'; exact HEq.rfl
      exact h' e
    -- Lift the inverse identity `F Y → F X` to a kernel map `g : Y → X`.
    obtain ⟨g, hg⟩ := full (cast (congrArg (· ⟶ F X) e) (Cat.id (F X)))
    have hgid : HEq (hF.map g) (Cat.id (F X)) := by rw [hg]; exact cast_heq _ _
    refine ⟨g, ⟨e.symm, hgid.trans idHEq⟩, ?_, ?_⟩
    · -- f ≫ g = 1_X, via faithfulness from `T(f)T(g) = 1 = T(1_X)`.
      apply emb (f ≫ g) (Cat.id X)
      rw [hF.map_comp, hF.map_id]
      exact key (hF.map f) (hF.map g) e hf hgid
    · -- g ≫ f = 1_Y, symmetrically at the endpoint `F Y`.
      apply emb (g ≫ f) (Cat.id Y)
      rw [hF.map_comp, hF.map_id]
      exact key (hF.map g) (hF.map f) e.symm (hgid.trans idHEq) (hf.trans idHEq)
  isPreorder {X Y} f g hf hg := by
    obtain ⟨_, hf'⟩ := hf
    obtain ⟨_, hg'⟩ := hg
    exact emb f g (eq_of_heq (hf'.trans hg'.symm))

/-! ## §1.363 Equivalent categories

  Two categories are EQUIVALENT iff they have isomorphic inflations.  An
  isomorphism of categories is a functor that is a full embedding (faithful +
  full) and a bijection on objects.  Equivalently (the book's Prop.), `𝒞` and
  `𝒟` are equivalent iff there is an equivalence functor between them. -/

/-- A functor is an ISOMORPHISM of categories if it is a full embedding and a
    bijection on objects (§1.363). -/
def IsCatIso (F : 𝒞 → 𝒟) [Functor F] : Prop :=
  Embedding F ∧ Full F ∧ Function.Injective F ∧ Function.Surjective F

/-- Two categories are EQUIVALENT (§1.363) if they have isomorphic inflations:
    there are inflations `I₁` of `𝒞` and `I₂` of `𝒟` whose inflated categories
    `[T₁]` and `[T₂]` are isomorphic via some functor `Φ`. -/
def AreEquivalent (𝒞 : Type u) [Cat.{v} 𝒞] (𝒟 : Type u) [Cat.{v} 𝒟] : Prop :=
  ∃ (B₁ : 𝒞) (I₁ : Inflation B₁) (B₂ : 𝒟) (I₂ : Inflation B₂)
    (Φ : I₁.objSet → I₂.objSet) (_ : Functor Φ), IsCatIso Φ

/-! ## §1.364 Skeletal category and skeleton

  `IsSkeletal` and `Skeleton` / `CoSkeleton` are defined in `S1_39.lean`
  (they depend on `EquivalentCategories` which in turn uses §1.36 machinery).
  See §1.364 note in S1_36.md. -/

/-! ## §1.361 Factorization of equivalence functors

  Every equivalence functor factors as a cross-section of an inflation, followed
  by an isomorphism of categories, followed by an inflation forgetful functor.
  We state the existence of such a factorization. -/

/-- §1.361: any equivalence functor `F : 𝒞 → 𝒟` factors through an inflation.
    There is an inflation `I` of `𝒟`, an isomorphism-of-categories `Φ : 𝒞 → [T]`,
    such that `F = Φ` followed by the forgetful functor `[T] → 𝒟`. -/
theorem equivalenceFunctor_factorization
    (F : 𝒞 → 𝒟) [hF : Functor F] (hEq : EquivalenceFunctor F) :
    ∃ (B : 𝒟) (I : Inflation B) (Φ : 𝒞 → I.objSet) (_ : Functor Φ),
      IsCatIso Φ ∧ ∀ X : 𝒞, I.T (Φ X) = F X := by
  sorry

/-! ## §1.366 Quotient by an equivalence kernel

  For any equivalence kernel `K ⊆ A`, there is an onto equivalence functor
  `A → A/K` whose kernel is exactly `K`.  `A/K` has the objects of `A` glued
  along `K` and the double cosets `KxK` as morphisms. -/

/-- §1.366: every equivalence kernel `K` of `𝒞` arises as the kernel of an onto
    equivalence functor `Q : 𝒞 → 𝒟`.  "Kernel = K" means a map `f` lies in `K`
    iff `Q` collapses it to an identity (equal endpoints, `Q f` heq `1`). -/
theorem quotientByKernel_exists (K : EquivalenceKernel 𝒞) :
    ∃ (𝒟 : Type u) (_ : Cat.{v} 𝒟) (Q : 𝒞 → 𝒟) (hQ : Functor Q),
      EquivalenceFunctor Q ∧ Function.Surjective Q ∧
      (∀ {X Y : 𝒞} (f : X ⟶ Y),
        K.mem f ↔ ∃ _ : Q X = Q Y, HEq (hQ.map f) (Cat.id (Q X))) := by
  sorry

/-! ## §1.367 Equivalence kernels classify equivalence functors

  Combining §1.366 and `equivalenceKernel`: the equivalence kernels of `𝒞` are
  exactly the kernels of onto equivalence functors out of `𝒞`. -/

/-- §1.367: a subset of maps `K` is an equivalence kernel of `𝒞` iff it is the
    kernel of some onto equivalence functor out of `𝒞`. -/
theorem equivalenceKernel_iff_kernel_of_functor
    (mem : {X Y : 𝒞} → (X ⟶ Y) → Prop) :
    (∃ K : EquivalenceKernel 𝒞, ∀ {X Y : 𝒞} (f : X ⟶ Y), K.mem f ↔ mem f) ↔
    (∃ (𝒟 : Type u) (_ : Cat.{v} 𝒟) (Q : 𝒞 → 𝒟) (hQ : Functor Q),
      EquivalenceFunctor Q ∧ Function.Surjective Q ∧
      ∀ {X Y : 𝒞} (f : X ⟶ Y),
        mem f ↔ ∃ _ : Q X = Q Y, HEq (hQ.map f) (Cat.id (Q X))) := by
  sorry

end Freyd
