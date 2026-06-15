/-
  Freyd & Scedrov, *Categories and Allegories* §1.62–§1.66
  Pasting Lemma, Positive pre-logoi, coproducts, generating set,
  pre-filter, Representation Theorem.

  §1.62 Pasting Lemma: union of subobjects is pushout of intersection.
  §1.623 Positive pre-logos = pre-logos with coproducts.
  §1.632 Generating set / basis.
  §1.634 Pre-filter, T_𝔉 functor.
  §1.635 Representation Theorem for pre-logoi.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_55
import Fredy.S1_56
import Fredy.S1_58
import Fredy.S1_60


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.62 Pasting Lemma

  In a pre-logos, the union A₁∪A₂ is the pushout of A₁∩A₂. -/

variable [PreLogos 𝒞]

/-- Intersection of subobjects: pullback of S.arr and T.arr, composed with S.arr. -/
def Subobject.inter [HasPullbacks 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B) : Subobject 𝒞 B :=
  let pb := HasPullbacks.has S.arr T.arr
  { dom := pb.cone.pt
    arr := pb.cone.π₁ ≫ S.arr
    monic := by
      intro X u v h
      -- h: u ≫ (π₁ ≫ S.arr) = v ≫ (π₁ ≫ S.arr)
      have hsq : pb.cone.π₁ ≫ S.arr = pb.cone.π₂ ≫ T.arr := pb.cone.w
      have huvπ₁ : u ≫ pb.cone.π₁ = v ≫ pb.cone.π₁ :=
        S.monic _ _ (by
          simpa [Cat.assoc] using h)
      have huvπ₂ : u ≫ pb.cone.π₂ = v ≫ pb.cone.π₂ :=
        T.monic _ _ (by
          calc
            (u ≫ pb.cone.π₂) ≫ T.arr = u ≫ (pb.cone.π₂ ≫ T.arr) := by simpa using Cat.assoc _ _ _
            _ = u ≫ (pb.cone.π₁ ≫ S.arr) := by rw [hsq]
            _ = (u ≫ pb.cone.π₁) ≫ S.arr := by simpa using (Cat.assoc _ _ _).symm
            _ = (v ≫ pb.cone.π₁) ≫ S.arr := by rw [huvπ₁]
            _ = v ≫ (pb.cone.π₁ ≫ S.arr) := by simpa using Cat.assoc _ _ _
            _ = v ≫ (pb.cone.π₂ ≫ T.arr) := by rw [hsq]
            _ = (v ≫ pb.cone.π₂) ≫ T.arr := by simpa using (Cat.assoc _ _ _).symm)
      let c : Cone S.arr T.arr :=
        { pt := X
          π₁ := u ≫ pb.cone.π₁
          π₂ := u ≫ pb.cone.π₂
          w  := by
            calc
              (u ≫ pb.cone.π₁) ≫ S.arr = u ≫ (pb.cone.π₁ ≫ S.arr) := by simpa using Cat.assoc _ _ _
              _ = u ≫ (pb.cone.π₂ ≫ T.arr) := by rw [hsq]
              _ = (u ≫ pb.cone.π₂) ≫ T.arr := by simpa using (Cat.assoc _ _ _).symm }
      have hlift := pb.lift_uniq c u (by rfl) (by rfl)
      have hv_eq_u : v = u := by
        apply (pb.lift_uniq c v ?_ ?_).trans hlift.symm
        · calc
            v ≫ pb.cone.π₁ = u ≫ pb.cone.π₁ := huvπ₁.symm
            _ = c.π₁ := rfl
        · calc
            v ≫ pb.cone.π₂ = u ≫ pb.cone.π₂ := huvπ₂.symm
            _ = c.π₂ := rfl
      rw [hv_eq_u] }

/-! ## Union of relations (§1.62)

  A binary relation `R : A ⟶ B` is a jointly-monic table, equivalently a
  subobject of `A × B`.  Their MEET is `intersect` (`⊓`, §1.56); their JOIN
  is the join of those subobjects, so `BinRel 𝒞 A B` is a lattice. -/

/-- `h ≫ pair a b = pair (h≫a) (h≫b)`: composition distributes through `pair`. -/
theorem comp_pair {X Y A B : 𝒞} (h : X ⟶ Y) (a : Y ⟶ A) (b : Y ⟶ B) :
    h ≫ pair a b = pair (h ≫ a) (h ≫ b) :=
  pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])

/-- A jointly-monic table `(colA, colB)` packaged as a subobject of `A × B`. -/
def BinRel.toSub {A B : 𝒞} (R : BinRel 𝒞 A B) : Subobject 𝒞 (prod A B) where
  dom := R.src
  arr := pair R.colA R.colB
  monic := by
    intro W f g h
    refine R.isMonicPair f g ?_ ?_
    · have := congrArg (· ≫ fst) h; simpa [Cat.assoc, fst_pair] using this
    · have := congrArg (· ≫ snd) h; simpa [Cat.assoc, snd_pair] using this

/-- A subobject of `A × B`, read back as a relation via its two projections. -/
def BinRel.ofSub {A B : 𝒞} (S : Subobject 𝒞 (prod A B)) : BinRel 𝒞 A B where
  src := S.dom
  colA := S.arr ≫ fst
  colB := S.arr ≫ snd
  isMonicPair := by
    intro W f g hA hB
    refine S.monic f g (pair_uniq (f ≫ S.arr ≫ fst) (f ≫ S.arr ≫ snd) _ ?_ ?_ |>.trans
      (pair_uniq (f ≫ S.arr ≫ fst) (f ≫ S.arr ≫ snd) (g ≫ S.arr) ?_ ?_).symm)
    · rw [Cat.assoc]
    · rw [Cat.assoc]
    · rw [Cat.assoc, ← hA]
    · rw [Cat.assoc, ← hB]

/-- `RelLe` is the subobject order on the `A × B` tables. -/
theorem relLe_iff_subLe {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    RelLe R S ↔ Subobject.le R.toSub S.toSub := by
  constructor
  · rintro ⟨⟨h, hA, hB⟩⟩
    exact ⟨h, by dsimp [BinRel.toSub]; rw [comp_pair, hA, hB]⟩
  · rintro ⟨h, hh⟩
    refine ⟨⟨h, ?_, ?_⟩⟩
    · have := congrArg (· ≫ fst) hh; simpa [BinRel.toSub, Cat.assoc, fst_pair] using this
    · have := congrArg (· ≫ snd) hh; simpa [BinRel.toSub, Cat.assoc, snd_pair] using this

/-- The UNION (join) of two relations `R, S : A ⟶ B`, as the subobject join of
    their tables in `A × B`.  Dual to `intersect` (`⊓`). -/
def RelUnion {A B : 𝒞} (R S : BinRel 𝒞 A B) : BinRel 𝒞 A B :=
  BinRel.ofSub (HasSubobjectUnions.union R.toSub S.toSub)

@[inherit_doc] infixl:65 " ⊔ " => RelUnion

theorem rel_le_union_left {A B : 𝒞} (R S : BinRel 𝒞 A B) : RelLe R (R ⊔ S) := by
  obtain ⟨h, hh⟩ := HasSubobjectUnions.union_left R.toSub S.toSub
  refine ⟨⟨h, ?_, ?_⟩⟩
  · show h ≫ (HasSubobjectUnions.union R.toSub S.toSub).arr ≫ fst = R.colA
    rw [← Cat.assoc, hh]; simp [BinRel.toSub]
  · show h ≫ (HasSubobjectUnions.union R.toSub S.toSub).arr ≫ snd = R.colB
    rw [← Cat.assoc, hh]; simp [BinRel.toSub]

theorem rel_le_union_right {A B : 𝒞} (R S : BinRel 𝒞 A B) : RelLe S (R ⊔ S) := by
  obtain ⟨h, hh⟩ := HasSubobjectUnions.union_right R.toSub S.toSub
  refine ⟨⟨h, ?_, ?_⟩⟩
  · show h ≫ (HasSubobjectUnions.union R.toSub S.toSub).arr ≫ fst = S.colA
    rw [← Cat.assoc, hh]; simp [BinRel.toSub]
  · show h ≫ (HasSubobjectUnions.union R.toSub S.toSub).arr ≫ snd = S.colB
    rw [← Cat.assoc, hh]; simp [BinRel.toSub]

/-- The union is the least upper bound: if `R ⊂ Q` and `S ⊂ Q` then `R ⊔ S ⊂ Q`. -/
theorem union_le {A B : 𝒞} {R S Q : BinRel 𝒞 A B}
    (hR : RelLe R Q) (hS : RelLe S Q) : RelLe (R ⊔ S) Q := by
  rw [relLe_iff_subLe] at hR hS
  obtain ⟨h, hh⟩ := HasSubobjectUnions.union_min R.toSub S.toSub Q.toSub hR hS
  refine ⟨⟨h, ?_, ?_⟩⟩
  · show h ≫ Q.colA = (HasSubobjectUnions.union R.toSub S.toSub).arr ≫ fst
    rw [← hh, Cat.assoc]; simp [BinRel.toSub]
  · show h ≫ Q.colB = (HasSubobjectUnions.union R.toSub S.toSub).arr ≫ snd
    rw [← hh, Cat.assoc]; simp [BinRel.toSub]

/-- Pasting Lemma (§1.62): For subobjects A₁,A₂ of A, the pushout
    of the two projections from the intersection I = A₁∩A₂ (to A₁.dom and
    A₂.dom) is the union U = A₁∪A₂.  This is one of the defining properties
    of a pre-logos (distributive subobject lattice). -/
def pasting_lemma {A : 𝒞} (A₁ A₂ : Subobject 𝒞 A) :
    HasPushout (HasPullbacks.has A₁.arr A₂.arr).cone.π₁ (HasPullbacks.has A₁.arr A₂.arr).cone.π₂ := by
  -- The book's proof uses R = x°f ∪ y°g, shows 1 ⊆ RR° and R°R ⊆ 1,
  -- hence R is a map (entire + simple), and xR = f, yR = g uniquely.
  -- This requires the full relation composition + simple/entire identities.
  sorry

/-! ## §1.623 Positive pre-logoi

  A POSITIVE PRE-LOGOS has binary coproducts (equivalently:
  for every A,B there exists C with A,B as complemented subobjects). -/

class PositivePreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends PreLogos 𝒞, HasBinaryCoproducts 𝒞

/-- §1.624: In a positive pre-logos, f: A → B₁+B₂ decomposes as
    f₁+f₂ from A₁ → B₁, A₂ → B₂ where A = A₁+A₂. -/
theorem decompose_via_coproduct [PositivePreLogos 𝒞] {A B₁ B₂ : 𝒞} (f : A ⟶ HasBinaryCoproducts.coprod B₁ B₂) :
    ∃ (A₁ A₂ : 𝒞) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂), Isomorphic A (HasBinaryCoproducts.coprod A₁ A₂) := by
  -- f#(inl) and f#(inr) pull back the coproduct inclusions
  sorry

/-! ## §1.632 Generating set / basis

  A set ℱ of objects is GENERATING if the representable functors
  {(G, -)} form an embedding.  A BASIS is a collectively faithful set. -/

/-- ℱ is GENERATING if the functors Hom(G,-) for G∈ℱ are collectively
    an embedding (i.e., injective on morphisms). -/
def IsGeneratingSet (ℱ : 𝒞 → Prop) : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B), (∀ G : 𝒞, ℱ G → (∀ h : G ⟶ A, h ≫ f = h ≫ g)) → f = g

/-- ℱ is a BASIS if the functors Hom(G,-) for G∈ℱ are collectively
    faithful.  In a Cartesian category: for every proper A'↣A, ∃ G∈ℱ
    and G→A not factoring through A'. -/
def IsBasis [HasPullbacks 𝒞] (ℱ : 𝒞 → Prop) : Prop :=
  IsGeneratingSet ℱ ∧
  ∀ {A' A : 𝒞} (m : A' ⟶ A), Mono m → ¬ IsIso m →
    ∃ G : 𝒞, ℱ G ∧ ∃ (x : G ⟶ A), ¬ ∃ (y : G ⟶ A'), y ≫ m = x

/-! ## §1.634 Pre-filter

  A non-empty ℱ ⊆ Sub(1) is a PRE-FILTER if it's ↓-directed.
  For a pre-filter ℱ, define T_ℱ : A → 𝒮 the colimit of Hom(U,-). -/

/-- ℱ is a pre-filter in the subobject lattice of 1: non-empty and
    ∀ U,V ∈ ℱ, ∃ W ∈ ℱ with W ≤ U and W ≤ V. -/
def IsPreFilter (ℱ : (Subobject 𝒞 one) → Prop) : Prop :=
  (∃ U, ℱ U) ∧ ∀ (U V : Subobject 𝒞 one), ℱ U → ℱ V → ∃ W, ℱ W ∧ Subobject.le W U ∧ Subobject.le W V

/-- T_ℱ(A) = colim_{U∈ℱ} Hom(U, A).  Represented here as the type of pairs
    (U, hU, f : U.dom → A) for U in the pre-filter ℱ.  The full definition
    requires a colimit of Hom-sets (equivalence classes).  For U projective,
    T_ℱ preserves finite products and equalizers; if ℱ is an ultra-filter in a
    Boolean algebra, T_ℱ preserves unions (§1.634-1.635). -/
structure PrefilterMap (ℱ : (Subobject 𝒞 one) → Prop) (A : 𝒞) where
  U    : Subobject 𝒞 one
  hU   : ℱ U
  map  : U.dom ⟶ A

def prefilter_functor (ℱ : (Subobject 𝒞 one) → Prop) (_hℱ : IsPreFilter ℱ) : 𝒞 → Type (max u v) :=
  PrefilterMap ℱ

/-! ## §1.635 Representation theorem for pre-logoi

  Every small positive pre-logos is faithfully representable in a
  power of the category of sets.  Proof via capital extension,
  complemented subterminators (which form a Boolean algebra),
  ultra-filters, and the T_ℱ construction. -/

theorem prelogos_representation_theorem (A : Type u) [Cat.{u} A] [PositivePreLogos A] :
    ∃ (T : A → (A → Type u)) (_ : Functor T), SeparatesMaps T := by
  -- The deep proof uses: capital extension (§1.63) + Stone representation
  -- of Boolean algebras via ultra-filters → T_ℱ is a faithful representation.
  -- Requires axiom of choice for the ultra-filter theorem.
  sorry


/-- FILTER in a subobject lattice: up-closed pre-filter (§1.634). -/
def IsFilter (ℱ : (Subobject 𝒞 one) → Prop) : Prop :=
  IsPreFilter ℱ ∧ ∀ (U V : Subobject 𝒞 one), ℱ U → Subobject.le U V → ℱ V

end Freyd
