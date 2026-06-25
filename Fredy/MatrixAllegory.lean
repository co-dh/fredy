/-
  Freyd & Scedrov, *Categories and Allegories* §2.216 / §2.342
  MATRIX ALLEGORY  Mat 𝒜  over a distributive allegory 𝒜.

  Objects  = Fin-n-indexed families of 𝒜-objects  (MatObj 𝒜).
  Morphisms = n×m matrices of base morphisms       (MatHom X Y).

  No Finset/Fintype/LinearOrder from Std — uses only List, Fin n, List.ofFn.
-/

import Fredy.S1_1
import Fredy.S2_1
import Fredy.S2_2
import Fredy.S2_3

universe v u

open Freyd Freyd.Alg

namespace Freyd.Alg.Mat

/-! ## §A  List-based finite join  in a distributive allegory

  `listJoin' l` = fold of `∪` right-to-left with unit `𝟘`. -/

section ListJoin

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

def listJoin' {a b : 𝒜} : List (a ⟶ b) → a ⟶ b
  | []      => 𝟘
  | x :: xs => x ∪ listJoin' xs

@[simp] theorem listJoin'_nil  {a b : 𝒜} : listJoin' ([] : List (a ⟶ b)) = 𝟘 := rfl
@[simp] theorem listJoin'_cons {a b : 𝒜} (x : a ⟶ b) (xs : List (a ⟶ b)) :
    listJoin' (x :: xs) = x ∪ listJoin' xs := rfl

theorem le_listJoin' {a b : 𝒜} {x : a ⟶ b} {l : List (a ⟶ b)} (hx : x ∈ l) :
    x ⊑ listJoin' l := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    simp only [listJoin'_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_union_left x _
    · exact le_trans (ih hmem) (le_union_right _ _)

theorem listJoin'_le {a b : 𝒜} {l : List (a ⟶ b)} {T : a ⟶ b}
    (h : ∀ x ∈ l, x ⊑ T) : listJoin' l ⊑ T := by
  induction l with
  | nil => exact zero_le T
  | cons y ys ih =>
    simp only [listJoin'_cons]
    exact union_lub (h y List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem y hx)))

/-- `finJoin f = ⨆_{i : Fin n} f i`. -/
def finJoin {a b : 𝒜} {n : Nat} (f : Fin n → (a ⟶ b)) : a ⟶ b :=
  listJoin' (List.ofFn f)

theorem le_finJoin {a b : 𝒜} {n : Nat} (f : Fin n → (a ⟶ b)) (i : Fin n) :
    f i ⊑ finJoin f :=
  le_listJoin' (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem finJoin_le {a b : 𝒜} {n : Nat} {f : Fin n → (a ⟶ b)} {T : a ⟶ b}
    (h : ∀ i, f i ⊑ T) : finJoin f ⊑ T :=
  listJoin'_le (fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact h i)

theorem finJoin_mono {a b : 𝒜} {n : Nat} {f g : Fin n → (a ⟶ b)}
    (h : ∀ i, f i ⊑ g i) : finJoin f ⊑ finJoin g :=
  finJoin_le (fun i => le_trans (h i) (le_finJoin g i))

theorem comp_finJoin {a b c : 𝒜} {n : Nat} (R : a ⟶ b) (f : Fin n → (b ⟶ c)) :
    R ≫ finJoin f = finJoin (fun j => R ≫ f j) := by
  simp only [finJoin]
  induction n with
  | zero => simp [List.ofFn_zero, DistributiveAllegory.comp_zero]
  | succ n ih =>
    simp only [List.ofFn_succ, listJoin'_cons, DistributiveAllegory.comp_union_distrib]
    congr 1; exact ih (fun i => f i.succ)

theorem finJoin_comp {a b c : 𝒜} {n : Nat} (f : Fin n → (a ⟶ b)) (R : b ⟶ c) :
    finJoin f ≫ R = finJoin (fun j => f j ≫ R) := by
  simp only [finJoin]
  induction n with
  | zero => simp [List.ofFn_zero, DistributiveAllegory.zero_comp]
  | succ n ih =>
    simp only [List.ofFn_succ, listJoin'_cons, union_comp_distrib]
    congr 1; exact ih (fun i => f i.succ)

theorem recip_finJoin {a b : 𝒜} {n : Nat} (f : Fin n → (a ⟶ b)) :
    (finJoin f)° = finJoin (fun j => (f j)°) := by
  apply le_antisymm
  · rw [recip_le_iff]
    apply finJoin_le; intro j
    rw [← recip_le_iff]
    exact le_finJoin (fun j => (f j)°) j
  · apply finJoin_le; intro j; exact recip_mono (le_finJoin f j)

theorem inter_finJoin {a b : 𝒜} {n : Nat} (T : a ⟶ b) (f : Fin n → (a ⟶ b)) :
    T ∩ finJoin f = finJoin (fun j => T ∩ f j) := by
  simp only [finJoin]
  induction n with
  | zero =>
    simp [List.ofFn_zero]
    exact le_antisymm (inter_lb_right T 𝟘) (le_inter (zero_le T) (le_refl 𝟘))
  | succ n ih =>
    simp only [List.ofFn_succ, listJoin'_cons]
    rw [DistributiveAllegory.inter_union_distrib]
    congr 1; exact ih (fun i => f i.succ)

end ListJoin

/-! ## §B  List-based finite meet  in an allegory

  `listMeet' (x :: xs)` = fold of `∩` over a nonempty list.
  We instantiate at `l = List.ofFn f` when n ≥ 1. -/

section ListMeet

variable {𝒜 : Type u} [Allegory 𝒜]

def listMeet' {a b : 𝒜} : (l : List (a ⟶ b)) → l ≠ [] → a ⟶ b
  | [x],            _  => x
  | x :: y :: rest, _  => x ∩ listMeet' (y :: rest) (List.cons_ne_nil y rest)

theorem listMeet'_singleton {a b : 𝒜} {x : a ⟶ b} (h : [x] ≠ []) :
    listMeet' [x] h = x := rfl

theorem listMeet'_cons_cons {a b : 𝒜} {x y : a ⟶ b} {rest : List (a ⟶ b)}
    (h : x :: y :: rest ≠ []) :
    listMeet' (x :: y :: rest) h = x ∩ listMeet' (y :: rest) (List.cons_ne_nil y rest) := rfl

theorem listMeet'_le {a b : 𝒜} (l : List (a ⟶ b)) (hne : l ≠ []) {x : a ⟶ b}
    (hx : x ∈ l) : listMeet' l hne ⊑ x := by
  induction l with
  | nil => exact absurd rfl hne
  | cons y ys ih =>
    rcases ys with _ | ⟨z, zs⟩
    · rcases List.mem_cons.mp hx with rfl | h
      · exact le_refl _
      · exact absurd h List.not_mem_nil
    · rw [listMeet'_cons_cons]
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact inter_lb_left _ _
      · exact le_trans (inter_lb_right _ _) (ih (List.cons_ne_nil z zs) hmem)

theorem le_listMeet' {a b : 𝒜} (l : List (a ⟶ b)) (hne : l ≠ []) {T : a ⟶ b}
    (h : ∀ x ∈ l, T ⊑ x) : T ⊑ listMeet' l hne := by
  induction l with
  | nil => exact absurd rfl hne
  | cons y ys ih =>
    rcases ys with _ | ⟨z, zs⟩
    · exact h y List.mem_cons_self
    · rw [listMeet'_cons_cons]
      exact le_inter (h y List.mem_cons_self)
        (ih (List.cons_ne_nil z zs) (fun x hx => h x (List.mem_cons_of_mem y hx)))

/-- `finMeet f = ⋀_{i : Fin (n+1)} f i`. -/
def finMeet {a b : 𝒜} {n : Nat} (f : Fin (n + 1) → (a ⟶ b)) : a ⟶ b :=
  listMeet' (List.ofFn f) (by rw [List.ofFn_succ]; exact List.cons_ne_nil _ _)

theorem finMeet_le {a b : 𝒜} {n : Nat} (f : Fin (n + 1) → (a ⟶ b)) (i : Fin (n + 1)) :
    finMeet f ⊑ f i :=
  listMeet'_le _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem le_finMeet {a b : 𝒜} {n : Nat} {f : Fin (n + 1) → (a ⟶ b)} {T : a ⟶ b}
    (h : ∀ i, T ⊑ f i) : T ⊑ finMeet f :=
  le_listMeet' _ _ (fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact h i)

end ListMeet

/-! ## §C  MatObj and MatHom -/

/-- An object of `Mat 𝒜`: a `Fin n`-indexed family of 𝒜-objects. -/
structure MatObj (𝒜 : Type u) where
  n    : Nat
  objs : Fin n → 𝒜

/-- Morphisms in `Mat 𝒜`: n×m matrices of 𝒜 morphisms. -/
abbrev MatHom [Cat.{v} 𝒜] (X Y : MatObj 𝒜) : Type v :=
  (i : Fin X.n) → (j : Fin Y.n) → X.objs i ⟶ Y.objs j

/-! ## §D  Category structure on MatObj 𝒜 -/

section MatCat

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

def matId (X : MatObj 𝒜) : MatHom X X :=
  fun i j => if h : i = j then (by subst h; exact Cat.id (X.objs i)) else 𝟘

def matComp {X Y Z : MatObj 𝒜} (M : MatHom X Y) (N : MatHom Y Z) : MatHom X Z :=
  fun i k => finJoin (fun j => M i j ≫ N j k)

theorem matId_comp {X Y : MatObj 𝒜} (M : MatHom X Y) : matComp (matId X) M = M := by
  funext i k; simp only [matComp, matId]
  apply le_antisymm
  · apply finJoin_le; intro j
    by_cases h : i = j
    · subst h; simp only [↓reduceDIte, Cat.id_comp, le_refl]
    · simp only [h, ↓reduceDIte, DistributiveAllegory.zero_comp]; exact zero_le _
  · have key := le_finJoin (fun j => (if h : i = j then (by subst h; exact Cat.id (X.objs i) : X.objs i ⟶ X.objs j) else 𝟘) ≫ M j k) i
    simp only [↓reduceDIte, Cat.id_comp] at key; exact key

theorem matComp_id {X Y : MatObj 𝒜} (M : MatHom X Y) : matComp M (matId Y) = M := by
  funext i k; simp only [matComp, matId]
  apply le_antisymm
  · apply finJoin_le; intro j
    by_cases h : j = k
    · subst h; simp only [↓reduceDIte, Cat.comp_id, le_refl]
    · simp only [h, ↓reduceDIte, DistributiveAllegory.comp_zero]; exact zero_le _
  · have key := le_finJoin (fun j => M i j ≫ (if h : j = k then (by subst h; exact Cat.id (Y.objs j) : Y.objs j ⟶ Y.objs k) else 𝟘)) k
    simp only [↓reduceDIte, Cat.comp_id] at key; exact key

theorem matComp_assoc {W X Y Z : MatObj 𝒜}
    (M : MatHom W X) (N : MatHom X Y) (P : MatHom Y Z) :
    matComp (matComp M N) P = matComp M (matComp N P) := by
  funext i l; simp only [matComp]
  apply le_antisymm
  · apply finJoin_le; intro k
    rw [finJoin_comp]; apply finJoin_le; intro j
    rw [Cat.assoc]
    exact le_trans (comp_mono_left (M i j) (le_finJoin (fun k => N j k ≫ P k l) k))
                   (le_finJoin (fun j => M i j ≫ finJoin (fun k => N j k ≫ P k l)) j)
  · apply finJoin_le; intro j
    rw [comp_finJoin]; apply finJoin_le; intro k
    rw [← Cat.assoc]
    exact le_trans (comp_mono_right (le_finJoin (fun j => M i j ≫ N j k) j) (P k l))
                   (le_finJoin (fun k => finJoin (fun j => M i j ≫ N j k) ≫ P k l) k)

instance instCatMatObj : Cat.{v} (MatObj 𝒜) where
  Hom     := MatHom
  id      := matId
  comp    := matComp
  id_comp := matId_comp
  comp_id := matComp_id
  assoc   := matComp_assoc

end MatCat

/-! ## §E  Allegory instance -/

section MatAllegory

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

def matRecip {X Y : MatObj 𝒜} (M : MatHom X Y) : MatHom Y X :=
  fun j i => (M i j)°

def matInter {X Y : MatObj 𝒜} (M N : MatHom X Y) : MatHom X Y :=
  fun i j => M i j ∩ N i j

theorem matRecip_comp {X Y Z : MatObj 𝒜} (M : MatHom X Y) (N : MatHom Y Z) :
    matRecip (matComp M N) = matComp (matRecip N) (matRecip M) := by
  funext k i; simp only [matRecip, matComp, recip_finJoin]
  congr 1; funext j; rw [Allegory.recip_comp]

theorem matSemidistrib {X Y Z : MatObj 𝒜} (R : MatHom X Y) (S T : MatHom Y Z) :
    matComp R (matInter S T) =
      matInter (matInter (matComp R S) (matComp R (matInter S T))) (matComp R T) := by
  funext i k; simp only [matComp, matInter]
  apply le_antisymm
  · apply le_inter
    · apply le_inter _ (le_refl _)
      exact finJoin_mono (fun j => comp_mono_left _ (inter_lb_left _ _))
    · exact finJoin_mono (fun j => comp_mono_left _ (inter_lb_right _ _))
  · exact le_trans (inter_lb_left _ _) (inter_lb_right _ _)

/-- Modular law: push `∩` inside the finite join via `inter_finJoin`, apply base `modular_le`. -/
theorem matModular {X Y Z : MatObj 𝒜} (R : MatHom X Y) (S : MatHom Y Z) (T : MatHom X Z) :
    matInter (matComp R S) T =
      matInter (matInter (matComp R S) T)
               (matComp (matInter R (matComp T (matRecip S))) S) := by
  funext i k; simp only [matInter, matComp, matRecip]
  apply le_antisymm
  · apply le_inter (le_refl _)
    rw [Allegory.inter_comm, inter_finJoin]
    apply finJoin_mono; intro j
    rw [Allegory.inter_comm]
    exact le_trans (modular_le (R i j) (S j k) (T i k))
      (comp_mono_right (le_inter (inter_lb_left _ _)
        (le_trans (inter_lb_right _ _) (le_finJoin (fun l => T i l ≫ (S j l)°) k))) _)
  · exact le_trans (inter_lb_left _ _) (le_refl _)

/-- §2.216: `Mat 𝒜` is an allegory. -/
instance instAllegoryMat : Allegory (MatObj 𝒜) where
  recip       := @matRecip 𝒜 _
  inter       := @matInter 𝒜 _
  recip_recip := fun M => by funext i j; simp [matRecip, Allegory.recip_recip]
  recip_comp  := matRecip_comp
  recip_inter := fun M N => by funext j i; simp [matRecip, matInter, Allegory.recip_inter]
  inter_idem  := fun M => by funext i j; simp [matInter, Allegory.inter_idem]
  inter_comm  := fun M N => by funext i j; simp [matInter, Allegory.inter_comm]
  inter_assoc := fun M N P => by funext i j; simp [matInter, Allegory.inter_assoc]
  semidistrib := matSemidistrib
  modular     := matModular

end MatAllegory

/-! ## §F  Distributive allegory instance -/

section MatDistributive

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

def matZero {X Y : MatObj 𝒜} : MatHom X Y := fun _i _j => 𝟘
def matUnion {X Y : MatObj 𝒜} (M N : MatHom X Y) : MatHom X Y := fun i j => M i j ∪ N i j

theorem matZero_comp {X Y Z : MatObj 𝒜} (N : MatHom Y Z) :
    matComp (matZero (X := X)) N = matZero := by
  funext i k; simp only [matComp, matZero, finJoin]
  apply le_antisymm
  · apply listJoin'_le; intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    rw [DistributiveAllegory.zero_comp]; exact le_refl _
  · exact zero_le _

theorem matComp_zero {X Y Z : MatObj 𝒜} (M : MatHom X Y) :
    matComp M (matZero (Y := Z)) = matZero := by
  funext i k; simp only [matComp, matZero, finJoin]
  apply le_antisymm
  · apply listJoin'_le; intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    rw [DistributiveAllegory.comp_zero]; exact le_refl _
  · exact zero_le _

theorem matComp_union_distrib {X Y Z : MatObj 𝒜} (M : MatHom X Y) (N P : MatHom Y Z) :
    matComp M (matUnion N P) = matUnion (matComp M N) (matComp M P) := by
  funext i k; simp only [matComp, matUnion]
  apply le_antisymm
  · apply finJoin_le; intro j
    rw [DistributiveAllegory.comp_union_distrib]
    exact union_lub
      (le_trans (le_finJoin (fun j => M i j ≫ N j k) j) (le_union_left _ _))
      (le_trans (le_finJoin (fun j => M i j ≫ P j k) j) (le_union_right _ _))
  · exact union_lub (finJoin_mono (fun j => comp_mono_left (M i j) (le_union_left _ _)))
                    (finJoin_mono (fun j => comp_mono_left (M i j) (le_union_right _ _)))

/-- §2.216: `Mat 𝒜` is a distributive allegory. -/
instance instDistributiveAllegoryMat : DistributiveAllegory (MatObj 𝒜) :=
  { instAllegoryMat with
    zero  := matZero
    union := matUnion
    zero_comp  := matZero_comp
    comp_zero  := matComp_zero
    union_idem := fun M   => by funext i j; simp [matUnion, DistributiveAllegory.union_idem]
    union_comm := fun M N => by funext i j; simp [matUnion, DistributiveAllegory.union_comm]
    union_assoc := fun M N P => by
      funext i j; simp [matUnion, DistributiveAllegory.union_assoc]
    union_inter_absorb := fun M N => by
      funext i j; simp only [matUnion, matInter]; exact DistributiveAllegory.union_inter_absorb _ _
    inter_union_absorb := fun M N => by
      funext i j; show matInter (matUnion M N) M i j = M i j
      simp only [matUnion, matInter]; exact DistributiveAllegory.inter_union_absorb _ _
    comp_union_distrib := matComp_union_distrib
    inter_union_distrib := fun M N P => by
      funext i j; simp only [matUnion, matInter]; exact DistributiveAllegory.inter_union_distrib _ _ _
    zero_union := fun M => by
      funext i j; simp only [matUnion, matZero]; exact DistributiveAllegory.zero_union _ }

end MatDistributive

/-! ## §G  Division allegory instance (§2.342)

  (R/S)_{ij} = ⋀_{k : Fin Z.n} (R_{ik}/S_{jk}).

  When Z.n = 0 the composition T ≫ S : MatHom X Z has no entries (Fin 0 columns),
  so T ≫ S ⊑ R is vacuously true for any T, and we use
    matDiv R S i j = Cat.id (X.objs i) / (𝟘 : Y.objs j ⟶ X.objs i)
  as a "top" for the hom-set X.objs i ⟶ Y.objs j:
    T ⊑ id / 𝟘  iff  T ≫ 𝟘 ⊑ id  iff  𝟘 ⊑ id  (always true by zero_le). -/

section MatDivision

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- Matrix division: `(R/S)_{ij} = ⋀_{k:Fin Z.n} (R_{ik}/S_{jk})`.
    When Z.n = 0, use the top morphism `id / 𝟘` (satisfied vacuously). -/
noncomputable def matDiv {X Y Z : MatObj 𝒜} (R : MatHom X Z) (S : MatHom Y Z) : MatHom X Y :=
  fun i j =>
    match h : Z.n with
    | 0     => Cat.id (X.objs i) / (𝟘 : Y.objs j ⟶ X.objs i)
    | n + 1 => finMeet (fun k => R i (h ▸ k) / S j (h ▸ k))

-- Pointwise characterization of the matrix order.
private theorem matLe_iff {X Y : MatObj 𝒜} {M N : X ⟶ Y} :
    (M ⊑ N) ↔ ∀ i j, M i j ⊑ N i j := by
  simp only [le]; constructor
  · intro h i j; exact congrFun (congrFun (show M ∩ N = M from h) i) j
  · intro h; show M ∩ N = M; funext i j; exact h i j

theorem matDiv_le_div {X Y Z : MatObj 𝒜} (T : X ⟶ Y) (R : X ⟶ Z) (S : Y ⟶ Z)
    (h : T ≫ S ⊑ R) : T ⊑ matDiv R S := by
  cases Z with | mk zn zobjs =>
  rw [matLe_iff] at h ⊢; intro i j
  simp only [Cat.comp, instCatMatObj, matComp] at h
  simp only [matDiv]
  cases zn with
  | zero => rw [le_div_iff, DistributiveAllegory.comp_zero]; exact zero_le _
  | succ m =>
    apply le_finMeet; intro k
    rw [le_div_iff]
    -- The cast in S j (· ▸ k) is rfl after cases Z, so it's identity
    simp only [eq_mpr_eq_cast, cast_eq]
    exact le_trans (le_finJoin (fun j => T i j ≫ S j k) j) (h i k)

theorem le_matDiv_comp {X Y Z : MatObj 𝒜} (R : X ⟶ Z) (S : Y ⟶ Z) :
    (matDiv R S : X ⟶ Y) ≫ S ⊑ R := by
  cases Z with | mk zn zobjs =>
  rw [matLe_iff]; intro i k
  simp only [Cat.comp, instCatMatObj, matComp, matDiv]
  cases zn with
  | zero => exact Fin.elim0 k
  | succ m =>
    simp only
    apply finJoin_le; intro j
    exact le_trans (comp_mono_right (finMeet_le _ k) _) (div_comp_eq_le _ _)

/-- §2.342: `Mat 𝒜` is a division allegory when `𝒜` is. -/
noncomputable instance instDivisionAllegoryMat : DivisionAllegory (MatObj 𝒜) :=
  { instDistributiveAllegoryMat with
    div         := fun R S => matDiv R S
    div_comp_le := fun R S => le_matDiv_comp R S
    le_div      := fun T R S h => matDiv_le_div T R S h }

end MatDivision

/-! ## §H  The 1×1 faithful embedding  A → Mat A  (§2.216 / §2.342) -/

section Embed1

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- The single-object 1×1 matrix object. -/
def unitObj (a : 𝒜) : MatObj 𝒜 := { n := 1, objs := fun _ => a }

/-- The 1×1 embedding: wraps a morphism as a 1×1 matrix. -/
def embed1 {a b : 𝒜} (R : a ⟶ b) : MatHom (unitObj a) (unitObj b) :=
  fun _i _j => R

/-- `embed1` is injective (faithful). -/
theorem embed1_injective {a b : 𝒜} {R S : a ⟶ b} (h : embed1 R = embed1 S) : R = S :=
  congrFun (congrFun h ⟨0, Nat.zero_lt_one⟩) ⟨0, Nat.zero_lt_one⟩

/-- `embed1` preserves composition. -/
theorem embed1_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    embed1 (R ≫ S) = matComp (embed1 R) (embed1 S) := by
  funext i k; simp only [embed1, matComp, finJoin, List.ofFn_succ, List.ofFn_zero,
    listJoin'_cons, listJoin'_nil, Fin.fin_one_eq_zero, union_zero]

/-- `embed1` preserves reciprocation. -/
theorem embed1_recip {a b : 𝒜} (R : a ⟶ b) :
    embed1 (R°) = matRecip (embed1 R) := rfl

/-- `embed1` preserves intersection. -/
theorem embed1_inter {a b : 𝒜} (R S : a ⟶ b) :
    embed1 (R ∩ S) = matInter (embed1 R) (embed1 S) := rfl

/-- `embed1` preserves union. -/
theorem embed1_union {a b : 𝒜} (R S : a ⟶ b) :
    embed1 (R ∪ S) = matUnion (embed1 R) (embed1 S) := rfl

theorem embed1_zero {a b : 𝒜} :
    embed1 (𝟘 : a ⟶ b) = matZero := rfl

end Embed1

section Embed1Div

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- `embed1` preserves division. -/
theorem embed1_div {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) :
    embed1 (R / S) = matDiv (embed1 R) (embed1 S) := by
  funext i j
  simp only [embed1, matDiv, unitObj]
  -- Z.n = 1 = 0.succ, so the match hits | succ m with m = 0
  -- finMeet (fun k : Fin 1 => R (rfl ▸ k) / S (rfl ▸ k)) = R ⟨0,..⟩ / S ⟨0,..⟩ = R / S
  simp only [finMeet, List.ofFn_succ, List.ofFn_zero, listMeet', Fin.fin_one_eq_zero]

end Embed1Div

/-! ## §I  Summary
  §2.216  Allegory (MatObj 𝒜)               : instAllegoryMat             [PROVED]
  §2.216  DistributiveAllegory (MatObj 𝒜)   : instDistributiveAllegoryMat [PROVED]
  §2.342  DivisionAllegory (MatObj 𝒜)       : instDivisionAllegoryMat     [PROVED]
  embed1 : 𝒜 → MatObj 𝒜 : faithful, preserves ≫, °, ∩, ∪, 𝟘, /  [PROVED]
-/

end Freyd.Alg.Mat
