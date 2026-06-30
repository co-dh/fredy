/-
  Freyd & Scedrov, *Categories and Allegories* §2.224  The GLOBAL COMPLETION.

  The global completion `A'` of a locally complete distributive allegory `A`
  has indexed families of objects (`GlobalObj`) as objects and infinite
  matrices (`GlobalMorphism`) as morphisms, with matrix multiplication via the
  locally-complete `Sup`.  The development here equips `GlobalObj A` with the
  full tower of allegory structure:

  * `globalCat`                   : §2.224 the matrices form a category;
  * `globalAllegory`              : reciprocation/intersection make it an allegory;
  * `globalDistributiveAllegory`  : entry-wise union/zero;
  * `globalLCDA`                  : entry-wise/pointwise `Sup`.

  Hence the faithful 1×1 embedding `A → A'` becomes a structure-preserving
  faithful representation into a locally complete distributive allegory.

  The remaining `GloballyCompleteAllegory` instance (disjoint unions of
  `Type u`-of-object-universe-indexed families) is UNIVERSE-BLOCKED by the
  current encoding; see the note at the end of the file.
-/

import Fredy.S2_2
import Fredy.S2_3

universe v u

namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-! ## Generic `Sup` helpers (in the base allegory `𝒜`) -/

/-- `Sup` of two propositionally-equal predicates agree. -/
theorem gcSup_congr {a b : 𝒜} {P Q : (a ⟶ b) → Prop} (h : ∀ T, P T ↔ Q T) :
    Sup P = Sup Q := by
  have hPQ : P = Q := funext fun T => propext (h T)
  rw [hPQ]

/-- If every member of `P` is below `𝟘`, the supremum is `𝟘`. -/
theorem gcSup_eq_zero {a b : 𝒜} {P : (a ⟶ b) → Prop}
    (h : ∀ T, P T → T ⊑ (𝟘 : a ⟶ b)) : Sup P = (𝟘 : a ⟶ b) :=
  le_antisymm (Sup_le h) (zero_le _)

/-- `Sup P = c` when `c` is a member and an upper bound. -/
theorem gcSup_eq {a b : 𝒜} {P : (a ⟶ b) → Prop} {c : a ⟶ b}
    (hc : P c) (hmax : ∀ T, P T → T ⊑ c) : Sup P = c :=
  le_antisymm (Sup_le hmax) (le_Sup hc)

/-! ## §2.224  The identity matrix and the category structure -/

/-- The IDENTITY MATRIX on an indexed family `A`: the diagonal, using a
    propositional `i = j` (no `DecidableEq`) and `HEq` to express that the
    on-diagonal entry is the identity. -/
def globalId (A : GlobalObj 𝒜) : GlobalMorphism A A :=
  fun i j => Sup (fun U : A.obj i ⟶ A.obj j => ∃ (_ : i = j), HEq U (Cat.id (A.obj i)))

theorem globalId_apply (A : GlobalObj 𝒜) (i j : A.idx) :
    globalId A i j
      = Sup (fun U : A.obj i ⟶ A.obj j => ∃ (_ : i = j), HEq U (Cat.id (A.obj i))) := rfl

/-- The diagonal entry of the identity matrix is the object identity. -/
theorem globalId_diag (A : GlobalObj 𝒜) (i : A.idx) :
    globalId A i i = Cat.id (A.obj i) := by
  rw [globalId_apply]
  apply le_antisymm
  · apply Sup_le
    rintro U ⟨_, hU⟩
    rw [eq_of_heq hU]; exact le_refl _
  · exact le_Sup ⟨rfl, HEq.refl _⟩

theorem globalComp_apply {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B)
    (S : GlobalMorphism B C) (i : A.idx) (k : C.idx) :
    GlobalMorphism.comp R S i k = Sup (fun T => ∃ j, T = R i j ≫ S j k) := rfl

/-- `1 ≫ R = R` (left identity). -/
theorem globalComp_id_left {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    GlobalMorphism.comp (globalId A) R = R := by
  funext i k
  rw [globalComp_apply]
  apply le_antisymm
  · apply Sup_le
    rintro T ⟨j, rfl⟩
    rw [globalId_apply, Sup_comp_distrib]
    apply Sup_le
    rintro Y ⟨U, ⟨h, hU⟩, rfl⟩
    subst h
    rw [eq_of_heq hU, Cat.id_comp]; exact le_refl _
  · exact le_Sup ⟨i, by rw [globalId_diag, Cat.id_comp]⟩

/-- `R ≫ 1 = R` (right identity). -/
theorem globalComp_id_right {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    GlobalMorphism.comp R (globalId B) = R := by
  funext i k
  rw [globalComp_apply]
  apply le_antisymm
  · apply Sup_le
    rintro T ⟨j, rfl⟩
    rw [globalId_apply, comp_Sup_distrib]
    apply Sup_le
    rintro Y ⟨U, ⟨h, hU⟩, rfl⟩
    subst h
    rw [eq_of_heq hU, Cat.comp_id]; exact le_refl _
  · exact le_Sup ⟨k, by rw [globalId_diag, Cat.comp_id]⟩

/-- Associativity = the `Sup`-interchange (Fubini) for matrix multiplication. -/
theorem globalComp_assoc {A B C D : GlobalObj 𝒜}
    (R : GlobalMorphism A B) (S : GlobalMorphism B C) (T : GlobalMorphism C D) :
    GlobalMorphism.comp (GlobalMorphism.comp R S) T
      = GlobalMorphism.comp R (GlobalMorphism.comp S T) := by
  funext i l
  rw [globalComp_apply, globalComp_apply]
  apply le_antisymm
  · apply Sup_le
    rintro X ⟨k, rfl⟩
    rw [globalComp_apply, Sup_comp_distrib]
    apply Sup_le
    rintro Y ⟨W, ⟨j, rfl⟩, rfl⟩
    rw [Cat.assoc]
    refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
    apply comp_mono_left
    rw [globalComp_apply]
    exact le_Sup ⟨k, rfl⟩
  · apply Sup_le
    rintro X ⟨j, rfl⟩
    rw [globalComp_apply, comp_Sup_distrib]
    apply Sup_le
    rintro Y ⟨W, ⟨k, rfl⟩, rfl⟩
    rw [← Cat.assoc]
    refine le_trans ?_ (le_Sup ⟨k, rfl⟩)
    apply comp_mono_right
    rw [globalComp_apply]
    exact le_Sup ⟨j, rfl⟩

/-- §2.224 (1) The global completion is a category. -/
instance globalCat : Cat (GlobalObj 𝒜) where
  Hom := GlobalMorphism
  id := globalId
  comp := GlobalMorphism.comp
  id_comp := globalComp_id_left
  comp_id := globalComp_id_right
  assoc := globalComp_assoc

/-! ## §2.224  Reciprocation and intersection -/

/-- Pointwise intersection of two matrices. -/
def globalInter {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) : GlobalMorphism A B :=
  fun i j => R i j ∩ S i j

theorem globalInter_apply {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) (i : A.idx) (j : B.idx) :
    globalInter R S i j = R i j ∩ S i j := rfl

theorem globalRecip_apply {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) (j : B.idx) (i : A.idx) :
    GlobalMorphism.recip R j i = (R i j)° := rfl

theorem globalRecip_recip {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    GlobalMorphism.recip (GlobalMorphism.recip R) = R := by
  funext i j
  rw [globalRecip_apply, globalRecip_apply, Allegory.recip_recip]

/-- `(R ≫ S)° = S° ≫ R°` : reciprocal flips and transposes, using `recip_Sup`. -/
theorem globalRecip_comp {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B) (S : GlobalMorphism B C) :
    GlobalMorphism.recip (GlobalMorphism.comp R S)
      = GlobalMorphism.comp (GlobalMorphism.recip S) (GlobalMorphism.recip R) := by
  funext k i
  change (Sup (fun T => ∃ j, T = R i j ≫ S j k))°
       = Sup (fun T' => ∃ j, T' = (S j k)° ≫ (R i j)°)
  rw [recip_Sup]
  apply gcSup_congr
  intro T'
  constructor
  · rintro ⟨W, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, by rw [Allegory.recip_comp]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨R i j ≫ S j k, ⟨j, rfl⟩, by rw [Allegory.recip_comp]⟩

theorem globalRecip_inter {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) :
    GlobalMorphism.recip (globalInter R S)
      = globalInter (GlobalMorphism.recip R) (GlobalMorphism.recip S) := by
  funext j i
  simp only [globalRecip_apply, globalInter_apply]
  rw [Allegory.recip_inter]

theorem globalInter_idem {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    globalInter R R = R := by
  funext i j; rw [globalInter_apply, Allegory.inter_idem]

theorem globalInter_comm {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) :
    globalInter R S = globalInter S R := by
  funext i j; rw [globalInter_apply, globalInter_apply, Allegory.inter_comm]

theorem globalInter_assoc {A B : GlobalObj 𝒜} (R S T : GlobalMorphism A B) :
    globalInter R (globalInter S T) = globalInter (globalInter R S) T := by
  funext i j; simp only [globalInter_apply]; rw [Allegory.inter_assoc]

/-- Semi-distributivity reduces, at each entry, to base semi-distributivity via
    `R(S∩T) ⊑ RS` and `R(S∩T) ⊑ RT` (the base `comp_mono_left`/`inter_lb`). -/
theorem globalSemidistrib {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B) (S T : GlobalMorphism B C) :
    GlobalMorphism.comp R (globalInter S T)
      = globalInter (globalInter (GlobalMorphism.comp R S)
            (GlobalMorphism.comp R (globalInter S T))) (GlobalMorphism.comp R T) := by
  funext i k
  rw [globalInter_apply, globalInter_apply]
  have hMP : GlobalMorphism.comp R (globalInter S T) i k ⊑ GlobalMorphism.comp R S i k := by
    rw [globalComp_apply, globalComp_apply]
    apply Sup_le
    rintro X ⟨j, rfl⟩
    refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
    apply comp_mono_left
    rw [globalInter_apply]
    exact inter_lb_left _ _
  have hMQ : GlobalMorphism.comp R (globalInter S T) i k ⊑ GlobalMorphism.comp R T i k := by
    rw [globalComp_apply, globalComp_apply]
    apply Sup_le
    rintro X ⟨j, rfl⟩
    refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
    apply comp_mono_left
    rw [globalInter_apply]
    exact inter_lb_right _ _
  rw [Allegory.inter_comm (GlobalMorphism.comp R S i k), inter_eq_left hMP, inter_eq_left hMQ]

/-- The modular law reduces, at each entry, to base `modular_le` plus reindexing
    the inner `Sup` defining `(T ≫ S°)`. -/
theorem globalModular {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B) (S : GlobalMorphism B C)
    (T : GlobalMorphism A C) :
    globalInter (GlobalMorphism.comp R S) T
      = globalInter (globalInter (GlobalMorphism.comp R S) T)
          (GlobalMorphism.comp
            (globalInter R (GlobalMorphism.comp T (GlobalMorphism.recip S))) S) := by
  funext i k
  rw [globalInter_apply, globalInter_apply, globalInter_apply]
  refine (inter_eq_left ?_).symm
  rw [globalComp_apply, Allegory.inter_comm, inter_Sup_distrib]
  apply Sup_le
  rintro V ⟨X, ⟨j, rfl⟩, rfl⟩
  rw [Allegory.inter_comm (T i k) (R i j ≫ S j k)]
  refine le_trans (modular_le (R i j) (S j k) (T i k)) ?_
  rw [globalComp_apply]
  refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
  apply comp_mono_right
  rw [globalInter_apply]
  apply le_inter (inter_lb_left _ _)
  refine le_trans (inter_lb_right _ _) ?_
  rw [globalComp_apply]
  refine le_Sup ⟨k, ?_⟩
  rw [globalRecip_apply]

/-- §2.224 (2) The global completion is an allegory. -/
instance globalAllegory : Allegory (GlobalObj 𝒜) where
  toCat := globalCat
  recip := GlobalMorphism.recip
  inter := globalInter
  recip_recip := globalRecip_recip
  recip_comp := globalRecip_comp
  recip_inter := globalRecip_inter
  inter_idem := globalInter_idem
  inter_comm := globalInter_comm
  inter_assoc := globalInter_assoc
  semidistrib := globalSemidistrib
  modular := globalModular

/-! ### Global order ↔ entry-wise base order -/

theorem global_le_entry {A B : GlobalObj 𝒜} {R T : A ⟶ B}
    (h : R ⊑ T) (i : A.idx) (j : B.idx) : R i j ⊑ T i j := by
  have h2 : globalInter R T = R := h
  exact congrFun (congrFun h2 i) j

theorem global_le_of_entry {A B : GlobalObj 𝒜} {R T : A ⟶ B}
    (h : ∀ i j, R i j ⊑ T i j) : R ⊑ T := by
  show globalInter R T = R
  funext i j
  exact h i j

/-! ## §2.224  Distributive structure (union and zero) -/

def globalUnion {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) : GlobalMorphism A B :=
  fun i j => R i j ∪ S i j

def globalZero {A B : GlobalObj 𝒜} : GlobalMorphism A B := fun _ _ => 𝟘

theorem globalUnion_apply {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) (i : A.idx) (j : B.idx) :
    globalUnion R S i j = R i j ∪ S i j := rfl

theorem globalZero_apply {A B : GlobalObj 𝒜} (i : A.idx) (j : B.idx) :
    (globalZero : GlobalMorphism A B) i j = (𝟘 : A.obj i ⟶ B.obj j) := rfl

theorem globalZero_comp {A B C : GlobalObj 𝒜} (R : GlobalMorphism B C) :
    GlobalMorphism.comp (globalZero : GlobalMorphism A B) R = globalZero := by
  funext i k
  rw [globalComp_apply, globalZero_apply]
  apply gcSup_eq_zero
  rintro X ⟨j, rfl⟩
  rw [globalZero_apply, DistributiveAllegory.zero_comp]; exact le_refl _

theorem globalComp_zero {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    GlobalMorphism.comp R (globalZero : GlobalMorphism B C) = globalZero := by
  funext i k
  rw [globalComp_apply, globalZero_apply]
  apply gcSup_eq_zero
  rintro X ⟨j, rfl⟩
  rw [globalZero_apply, DistributiveAllegory.comp_zero]; exact le_refl _

theorem globalUnion_idem {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    globalUnion R R = R := by
  funext i j; rw [globalUnion_apply, DistributiveAllegory.union_idem]

theorem globalUnion_comm {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) :
    globalUnion R S = globalUnion S R := by
  funext i j; rw [globalUnion_apply, globalUnion_apply, DistributiveAllegory.union_comm]

theorem globalUnion_assoc {A B : GlobalObj 𝒜} (R S T : GlobalMorphism A B) :
    globalUnion R (globalUnion S T) = globalUnion (globalUnion R S) T := by
  funext i j; simp only [globalUnion_apply]; rw [DistributiveAllegory.union_assoc]

theorem globalUnion_inter_absorb {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) :
    globalUnion R (globalInter S R) = R := by
  funext i j; rw [globalUnion_apply, globalInter_apply, DistributiveAllegory.union_inter_absorb]

theorem globalInter_union_absorb {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) :
    globalInter (globalUnion R S) R = R := by
  funext i j; rw [globalInter_apply, globalUnion_apply, DistributiveAllegory.inter_union_absorb]

theorem globalZero_union {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    globalUnion globalZero R = R := by
  funext i j; rw [globalUnion_apply, globalZero_apply, DistributiveAllegory.zero_union]

theorem globalInter_union_distrib {A B : GlobalObj 𝒜} (R S T : GlobalMorphism A B) :
    globalInter R (globalUnion S T)
      = globalUnion (globalInter R S) (globalInter R T) := by
  funext i j
  simp only [globalInter_apply, globalUnion_apply]
  rw [DistributiveAllegory.inter_union_distrib]

/-- Composition distributes over union: the matrix `Sup` of an entry-wise union
    is the union of the two `Sup`s. -/
theorem globalComp_union_distrib {A B C : GlobalObj 𝒜}
    (R : GlobalMorphism A B) (S T : GlobalMorphism B C) :
    GlobalMorphism.comp R (globalUnion S T)
      = globalUnion (GlobalMorphism.comp R S) (GlobalMorphism.comp R T) := by
  funext i k
  rw [globalUnion_apply, globalComp_apply, globalComp_apply, globalComp_apply]
  apply le_antisymm
  · apply Sup_le
    rintro X ⟨j, rfl⟩
    rw [globalUnion_apply, DistributiveAllegory.comp_union_distrib]
    apply union_lub
    · exact le_trans (le_Sup ⟨j, rfl⟩) (le_union_left _ _)
    · exact le_trans (le_Sup ⟨j, rfl⟩) (le_union_right _ _)
  · apply union_lub
    · apply Sup_le
      rintro X ⟨j, rfl⟩
      refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
      rw [globalUnion_apply, DistributiveAllegory.comp_union_distrib]
      exact le_union_left _ _
    · apply Sup_le
      rintro X ⟨j, rfl⟩
      refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
      rw [globalUnion_apply, DistributiveAllegory.comp_union_distrib]
      exact le_union_right _ _

/-- §2.224 (3) The global completion is a distributive allegory. -/
instance globalDistributiveAllegory : DistributiveAllegory (GlobalObj 𝒜) where
  toAllegory := globalAllegory
  zero := globalZero
  union := globalUnion
  zero_comp := globalZero_comp
  comp_zero := globalComp_zero
  union_idem := globalUnion_idem
  union_comm := globalUnion_comm
  union_assoc := globalUnion_assoc
  union_inter_absorb := globalUnion_inter_absorb
  inter_union_absorb := globalInter_union_absorb
  comp_union_distrib := globalComp_union_distrib
  inter_union_distrib := globalInter_union_distrib
  zero_union := globalZero_union

/-! ## §2.224  Local completeness (pointwise `Sup`) -/

/-- The supremum of a family of matrices is taken pointwise. -/
def globalSup {A B : GlobalObj 𝒜} (P : GlobalMorphism A B → Prop) : GlobalMorphism A B :=
  fun i j => Sup (fun T => ∃ R, P R ∧ T = R i j)

theorem globalSup_apply {A B : GlobalObj 𝒜} (P : GlobalMorphism A B → Prop) (i : A.idx) (j : B.idx) :
    globalSup P i j = Sup (fun T => ∃ R, P R ∧ T = R i j) := rfl

/-- Composition distributes over the pointwise `Sup` (a `Sup`-interchange). -/
theorem globalComp_Sup_distrib {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B)
    (P : GlobalMorphism B C → Prop) :
    GlobalMorphism.comp R (globalSup P)
      = globalSup (fun T => ∃ S, P S ∧ T = GlobalMorphism.comp R S) := by
  funext i k
  rw [globalComp_apply, globalSup_apply]
  apply le_antisymm
  · apply Sup_le
    rintro X ⟨j, rfl⟩
    rw [globalSup_apply, comp_Sup_distrib]
    apply Sup_le
    rintro Y ⟨U, ⟨S, hS, rfl⟩, rfl⟩
    refine le_trans ?_ (le_Sup ⟨GlobalMorphism.comp R S, ⟨S, hS, rfl⟩, rfl⟩)
    rw [globalComp_apply]
    exact le_Sup ⟨j, rfl⟩
  · apply Sup_le
    rintro W ⟨Tm, ⟨S, hS, rfl⟩, rfl⟩
    rw [globalComp_apply]
    apply Sup_le
    rintro X ⟨j, rfl⟩
    refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
    apply comp_mono_left
    rw [globalSup_apply]
    exact le_Sup ⟨S, hS, rfl⟩

/-- Intersection distributes over the pointwise `Sup` (no interchange needed). -/
theorem globalInter_Sup_distrib {A B : GlobalObj 𝒜} (R : GlobalMorphism A B)
    (P : GlobalMorphism A B → Prop) :
    globalInter R (globalSup P)
      = globalSup (fun T => ∃ S, P S ∧ T = globalInter R S) := by
  funext i j
  rw [globalInter_apply, globalSup_apply, globalSup_apply, inter_Sup_distrib]
  apply gcSup_congr
  intro V
  constructor
  · rintro ⟨U, ⟨S, hS, rfl⟩, rfl⟩
    exact ⟨globalInter R S, ⟨S, hS, rfl⟩, rfl⟩
  · rintro ⟨Tm, ⟨S, hS, rfl⟩, rfl⟩
    exact ⟨S i j, ⟨S, hS, rfl⟩, rfl⟩

/-- §2.224 (4) The global completion is a locally complete distributive allegory. -/
instance globalLCDA : LocallyCompleteDistributiveAllegory (GlobalObj 𝒜) where
  toDistributiveAllegory := globalDistributiveAllegory
  Sup := globalSup
  le_Sup := by
    intro A B P R h
    exact global_le_of_entry (fun i j => le_Sup ⟨R, h, rfl⟩)
  Sup_le := by
    intro A B P T h
    refine global_le_of_entry (fun i j => Sup_le ?_)
    rintro U ⟨R', hR', rfl⟩
    exact global_le_entry (h R' hR') i j
  comp_Sup_distrib := globalComp_Sup_distrib
  inter_Sup_distrib := globalInter_Sup_distrib

/-! ## §2.224  The embedding is a faithful structure-preserving representation -/

/-- §2.224 the 1×1 embedding `A → A'` is faithful. -/
theorem globalCompletion_faithful {a b : 𝒜} {R S : a ⟶ b}
    (h : globalCompletionEmbed R = globalCompletionEmbed S) : R = S :=
  globalCompletionEmbed_injective h

/-- The embedding preserves reciprocation. -/
theorem globalCompletionEmbed_recip {a b : 𝒜} (R : a ⟶ b) :
    GlobalMorphism.recip (globalCompletionEmbed R) = globalCompletionEmbed (R°) := by
  funext j i; rfl

/-- The embedding preserves composition (the middle `Sup` over `PUnit` collapses). -/
theorem globalCompletionEmbed_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    GlobalMorphism.comp (globalCompletionEmbed R) (globalCompletionEmbed S)
      = globalCompletionEmbed (R ≫ S) := by
  funext i j
  rw [globalComp_apply]
  refine gcSup_eq ⟨PUnit.unit, rfl⟩ ?_
  rintro T ⟨_, rfl⟩
  exact le_refl _

/-! ## §2.224  GloballyCompleteAllegory — universe obstruction

  The `GloballyCompleteAllegory` class demands, for `𝒜' = GlobalObj 𝒜 : Type (u+1)`,
  a disjoint union of *every* family `a : I → 𝒜'` with `I : Type (u+1)` (the index
  type lives in `𝒜'`'s OBJECT universe).  The disjoint union of indexed families is
  the concatenation `idx := Σ i, (a i).idx`; with `I : Type (u+1)` and
  `(a i).idx : Type u`, this `Σ` lands in `Type (u+1)`, but `GlobalObj 𝒜` requires
  `idx : Type u`.  So `disjointUnion a` is NOT a `GlobalObj 𝒜` and the instance
  cannot even be stated, let alone proved — this is a genuine size/universe gap of
  the encoding (the global completion is globally complete only relative to the
  original universe `u`, not the bumped universe `u+1`).  Closing it would require
  a universe-polymorphic `GlobalObj` (`idx : Type w` with `w` independent of the
  object universe), which is fixed in `Fredy/S2_2.lean` and out of scope here.  -/

end Freyd.Alg
