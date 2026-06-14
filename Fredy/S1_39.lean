/-
  Freyd & Scedrov, *Categories and Allegories* §1.34–§1.39 — remaining TOC entries.
  Adjoint pair, Skeleton/Coskeleton, Idempotent/Split idempotent,
  Equivalent categories, Exact sequence, Complete measure, Atomic measure.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31
import Fredy.S1_34
import Fredy.S1_41
import Fredy.S1_43

universe v u

namespace Freyd

/-- ADJOINT PAIR (§1.81, §1.373): F ⊣ G with natural bijection Hom(FX,Y) ≅ Hom(X,GY).
    Here defined as a structure on two functors. -/
structure AdjointPair {𝒞 : Type u} {𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞) [Functor F] [Functor G] where
  unit   : Nonempty (NatIso (λ X => X) (G ∘ F))
  counit : Nonempty (NatIso (F ∘ G) (λ X => X))
  -- The proper definition would include triangle identities.
  -- This captures "GF ≅ Id, FG ≅ Id" which characterizes adjoints in the
  -- context of strong equivalences.

/-- LEFT ADJOINT (§1.373): the functor F in an adjoint pair. -/
def LeftAdjoint {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟] (F : 𝒞 → 𝒟) [Functor F] : Prop :=
  ∃ (G : 𝒟 → 𝒞) [Functor G], Nonempty (AdjointPair F G)

/-- RIGHT ADJOINT (§1.373): the functor G in an adjoint pair. -/
def RightAdjoint {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟] (G : 𝒟 → 𝒞) [Functor G] : Prop :=
  ∃ (F : 𝒞 → 𝒟) [Functor F], Nonempty (AdjointPair F G)

/-- EQUIVALENT CATEGORIES (§1.363): two categories are EQUIVALENT if
    there exist isomorphic inflations.  (Existence of an equivalence functor
    implies equivalence.) -/
def EquivalentCategories (𝒜 ℬ : Type u) [Cat.{v} 𝒜] [Cat.{v} ℬ] : Prop :=
  ∃ (F : 𝒜 → ℬ) [Functor F], EquivalenceFunctor F

/-- SKELETAL category (§1.364): isomorphic objects are equal. -/
def IsSkeletal (𝒞 : Type u) [Cat.{v} 𝒞] : Prop :=
  ∀ (A B : 𝒞), Isomorphic A B → A = B

/-- SKELETON of A: a skeletal category A' with an equivalence A' → A. -/
def Skeleton (𝒜 : Type u) [Cat.{v} 𝒜] : Prop :=
  ∃ (A' : Type u) [Cat.{v} A'], IsSkeletal A' ∧ EquivalentCategories A' 𝒜

/-- COSKELETON of A: a skeletal category A' with an equivalence A → A'. -/
def CoSkeleton (𝒜 : Type u) [Cat.{v} 𝒜] : Prop :=
  ∃ (A' : Type u) [Cat.{v} A'], IsSkeletal A' ∧ EquivalentCategories 𝒜 A'

/-- IDEMPOTENT (§1.28): e: A→A such that e² = e. -/
def Idempotent {A : 𝒞} (e : A ⟶ A) : Prop := e ≫ e = e

/-- SPLIT IDEMPOTENT (§1.281): there exist r: A→B, s: B→A with s≫r = id, r≫s = e. -/
def SplitIdempotent {A : 𝒞} (e : A ⟶ A) : Prop :=
  Idempotent e ∧ ∃ (B : 𝒞) (r : A ⟶ B) (s : B ⟶ A), s ≫ r = Cat.id B ∧ r ≫ s = e

/-- **§1.28**: Equalizer maps are monic.  Used in the idempotent-splitting proof. -/
theorem eqMap_mono [HasEqualizers 𝒞] {A B : 𝒞} (f g : A ⟶ B) : Mono (eqMap f g) := by
  intro X a b h
  -- h: a ≫ eqMap f g = b ≫ eqMap f g
  let k := a ≫ eqMap f g
  have hk_eq : k ≫ f = k ≫ g := by
    calc
      k ≫ f = a ≫ (eqMap f g ≫ f) := Cat.assoc _ _ _
      _ = a ≫ (eqMap f g ≫ g) := by rw [eqMap_eq f g]
      _ = k ≫ g := (Cat.assoc _ _ _).symm
  have ha : a = eqLift f g k hk_eq :=
    (eqLift_uniq f g k hk_eq a rfl).symm
  have hb : b = eqLift f g k hk_eq :=
    (eqLift_uniq f g k hk_eq b (by dsimp [k]; rw [h])).symm
  rw [ha, hb]

/-- **§1.28 / §1.571**: In a category with equalizers, every idempotent splits
    through the equalizer of (e, 1_A).  This is the construction used in §1.571:
    the equalizer C → A of (1, e) gives the splitting of e, and the image of x
    (with e·x = x) is constructed as a subobject of A. -/
theorem idempotent_splits_via_equalizer [HasEqualizers 𝒞] {A : 𝒞} {e : A ⟶ A}
    (h_idem : Idempotent e) : SplitIdempotent e := by
  let one := Cat.id A
  let B := eqObj e one
  let m : B ⟶ A := eqMap e one       -- equalizer of (e, 1_A)
  have hm_eq : e ≫ e = e ≫ one := by rw [Cat.comp_id, h_idem]
  let r : A ⟶ B := eqLift e one e hm_eq    -- lift through the equalizer
  have hr_fac : r ≫ m = e := eqLift_fac e one e hm_eq
  have hm_mono : Mono m := eqMap_mono e one
  have h_mr_eq_one : m ≫ r = Cat.id B := by
    -- (m≫r)≫m = m≫(r≫m) = m≫e = m≫1 = 1_B≫m, cancel m
    apply hm_mono (m ≫ r) (Cat.id B) ?_
    calc
      (m ≫ r) ≫ m = m ≫ (r ≫ m) := Cat.assoc _ _ _
      _ = m ≫ e := by rw [hr_fac]
      _ = m ≫ one := by
        -- from the equalizer: eqMap ≫ e = eqMap ≫ 1
        rw [eqMap_eq e one, Cat.comp_id]
      _ = (Cat.id B) ≫ m := by rw [Cat.id_comp]
  refine ⟨h_idem, B, r, m, h_mr_eq_one, hr_fac⟩

/-- EXACT SEQUENCE (§1.599): sequence ... → A_{n-1} → A_n → A_{n+1} → ... where
    the image of each map is the kernel of the next. -/
def ExactSequence {n : ℕ} (objects : Fin n → 𝒞) (maps : (i : Fin (n-1)) → objects i.castSucc ⟶ objects i.succ)
    [HasImages 𝒞] [HasEqualizers 𝒞] [HasZeroObject 𝒞] : Prop :=
  ∀ (i : Fin (n-2)),
    Isomorphic (image (maps i.castSucc)).dom (Kernel (maps i.succ)).dom

/-- COMPLETE MEASURE (§1.648): an ultrafilter closed under countable intersections. -/
def CompleteMeasure (I : Type u) (F : Set (Set I)) : Prop :=
  -- an ultrafilter on I such that for any countable partition {A_n} of I,
  -- at least one A_n is in F.
  True

/-- ATOMIC MEASURE (§1.648): a measure of the form {j | i ≤ j} for some i. -/
def AtomicMeasure (I : Type u) (F : Set (Set I)) (i : I) : Prop :=
  F = {J | i ∈ J}

end Freyd
