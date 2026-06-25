/-
  Freyd & Scedrov, *Categories and Allegories* §1.49  τ-categories.
  §1.491–§1.49(11).
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42


open Freyd

universe v u

namespace Freyd

/-! ## §1.491 Tables -/

/-- A TABLE ⟨T; x₁, …, xₙ⟩.  source T, columns xᵢ : T ⟶ Aᵢ, jointly monic.
    Takes 𝒞 explicitly (like HasBinaryProducts in S1_42) for clean typeclass resolution. -/
structure Table (𝒞 : Type u) [Cat.{v} 𝒞] where
  src   : 𝒞
  len   : Nat
  codom : Fin len → 𝒞
  col   : (i : Fin len) → src ⟶ codom i
  monic : ∀ ⦃X : 𝒞⦄ (f g : X ⟶ src), (∀ i : Fin len, f ≫ col i = g ≫ col i) → f = g

namespace Table

variable {𝒞} [Cat.{v} 𝒞] (tab : Table 𝒞)

/-- Column j is SHORT: agreement on earlier columns forces agreement on j (§1.491). -/
def IsShort (j : Fin tab.len) : Prop :=
  ∀ (X : 𝒞) (f g : X ⟶ tab.src),
    (∀ i : Fin tab.len, i.val < j.val → f ≫ tab.col i = g ≫ tab.col i) →
    f ≫ tab.col j = g ≫ tab.col j

end Table

/-! ### Table isomorphism -/

/-- Isomorphism of tables: source iso carrying columns to columns.
    `codom_match` gives the codomain equality (needed for resurfacing arguments);
    `col_match` gives the column equation up to HEq. -/
structure TableIso {𝒞 : Type u} [Cat.{v} 𝒞] (S T : Table 𝒞) where
  hLen        : S.len = T.len
  f           : S.src ⟶ T.src
  g           : T.src ⟶ S.src
  f_g         : f ≫ g = Cat.id S.src
  g_f         : g ≫ f = Cat.id T.src
  codom_match : ∀ i : Fin S.len, T.codom (hLen ▸ i) = S.codom i
  col_match   : ∀ i : Fin S.len, HEq (f ≫ T.col (hLen ▸ i)) (S.col i)

variable {𝒞} [Cat.{v} 𝒞]

def TableIso.refl (S : Table 𝒞) : TableIso S S where
  hLen        := rfl
  f           := Cat.id S.src
  g           := Cat.id S.src
  f_g         := Cat.id_comp _
  g_f         := Cat.id_comp _
  codom_match := fun _ => rfl
  col_match   := λ i => heq_of_eq (Cat.id_comp (S.col i))

/-- The reverse-column relation: `g ≫ S.col i ≍ T.col (hLen ▸ i)`.
    (Compose `col_match` with `g` on the left and use `g ≫ f = id`.) -/
theorem TableIso.col_match_g {S T : Table 𝒞} (iso : TableIso S T) (i : Fin S.len) :
    HEq (iso.g ≫ S.col i) (T.col (iso.hLen ▸ i)) := by
  have e1 : HEq (iso.g ≫ S.col i) (iso.g ≫ (iso.f ≫ T.col (iso.hLen ▸ i))) := by
    congr 1
    · exact (iso.codom_match i).symm
    · exact (iso.col_match i).symm
  refine e1.trans ?_
  rw [← Cat.assoc, iso.g_f, Cat.id_comp]

/-! ## §1.491 Prune – remove a short column -/

/-- Casting a `Fin` along a `Nat` equality preserves its value. -/
theorem fin_cast_val {a b : Nat} (h : a = b) (k : Fin a) : (h ▸ k : Fin b).val = k.val := by
  subst h; rfl

/-- Left-whisker a heterogeneous equality of morphisms (codomains may differ). -/
theorem comp_heq_left {𝒞 : Type u} [Cat.{v} 𝒞] {X A B B' : 𝒞} (h : X ⟶ A) (s : A ⟶ B)
    (t : A ⟶ B') (hB : B = B') (hst : HEq s t) : HEq (h ≫ s) (h ≫ t) := by
  cases hB; cases hst; rfl

/-- Transport a morphism along an equality of its codomain. -/
def castCod {𝒞 : Type u} [Cat.{v} 𝒞] {A B B' : 𝒞} (h : B = B') (f : A ⟶ B) : A ⟶ B' := h ▸ f

/-- `castCod` is heterogeneously equal to the original morphism. -/
theorem castCod_heq {𝒞 : Type u} [Cat.{v} 𝒞] {A B B' : 𝒞} (h : B = B') (f : A ⟶ B) :
    HEq (castCod h f) f := by subst h; rfl

/-- Transport the domain of a morphism along an object equality. -/
def castDom {𝒞 : Type u} [Cat.{v} 𝒞] {A A' B : 𝒞} (h : A = A') (f : A ⟶ B) : A' ⟶ B := h ▸ f

/-- `castDom` is heterogeneously equal to the original morphism. -/
theorem castDom_heq {𝒞 : Type u} [Cat.{v} 𝒞] {A A' B : 𝒞} (h : A = A') (f : A ⟶ B) :
    HEq (castDom h f) f := by subst h; rfl

/-- Apply a heterogeneous equality of dependent functions (same index type) at a point. -/
theorem hcongr_fun {α : Sort u} {P Q : α → Sort v} (f : (a : α) → P a) (g : (a : α) → Q a)
    (hPQ : P = Q) (hfg : HEq f g) (a : α) : HEq (f a) (g a) := by
  subst hPQ; cases hfg; rfl

/-- Heterogeneous function extensionality over a `Fin`-length equality. -/
theorem heq_funext_fin {a b : Nat} {β : Sort v} (hab : a = b) (f : Fin a → β) (g : Fin b → β)
    (hpt : ∀ i : Fin a, f i = g (hab ▸ i)) : HEq f g := by
  subst hab; exact heq_of_eq (funext fun i => hpt i)

/-- Heterogeneous dependent function extensionality over a `Fin`-length equality
    (the value types are determined by `β` applied to the index). -/
theorem heq_dfunext_fin {a b : Nat} {β : Sort w} (hab : a = b) {P : Fin a → β} {Q : Fin b → β}
    (hPQ : ∀ i : Fin a, P i = Q (hab ▸ i)) {𝒞 : β → Sort v}
    (f : (i : Fin a) → 𝒞 (P i)) (g : (i : Fin b) → 𝒞 (Q i))
    (hpt : ∀ i : Fin a, HEq (f i) (g (hab ▸ i))) : HEq f g := by
  subst hab
  have hPQ' : P = Q := funext hPQ; subst hPQ'
  exact heq_of_eq (funext fun i => eq_of_heq (hpt i))

/-- Full heterogeneous congruence for composition (all three objects may differ). -/
theorem comp_heq {𝒞 : Type u} [Cat.{v} 𝒞] {X X' A A' B B' : 𝒞} (f : X ⟶ A) (f' : X' ⟶ A')
    (s : A ⟶ B) (s' : A' ⟶ B') (hX : X = X') (hA : A = A') (hB : B = B')
    (hf : HEq f f') (hs : HEq s s') : HEq (f ≫ s) (f' ≫ s') := by
  cases hX; cases hA; cases hB; cases hf; cases hs; rfl

/-- Embed Fin (n-1) into Fin n skipping index j. -/
def Fin.skip {n : Nat} (j : Fin n) (i : Fin (n - 1)) : Fin n :=
  if h : i.val < j.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- Every k ≠ j is in the image of Fin.skip j.  (Proof: case analysis on k < j or k > j.)
    The k > j branch needs the observation that k.val ≥ 1 when j.val ≤ k.val and k ≠ j. -/
theorem Fin.skip_surj {n : Nat} {j k : Fin n} (hk : k ≠ j) : ∃ i : Fin (n - 1), Fin.skip j i = k := by
  by_cases hlt : k.val < j.val
  · -- k.val < j.val: embed k directly, need k.val < n - 1
    have hk_lt_n_sub_one : k.val < n - 1 := by
      have h_succ_le_j : k.val + 1 ≤ j.val := Nat.succ_le_of_lt hlt
      have hj_lt_n : j.val < n := j.2
      omega
    exact ⟨⟨k.val, hk_lt_n_sub_one⟩, by unfold Fin.skip; simp [hlt]⟩
  · -- k.val ≥ j.val, and k ≠ j, so j.val < k.val, hence 1 ≤ k.val.
    have hj_lt_k : j.val < k.val := by
      have hle : j.val ≤ k.val := Nat.le_of_not_lt hlt
      have hne : j.val ≠ k.val := fun h => hk (Fin.ext h.symm)
      omega
    have h_one_le_k : 1 ≤ k.val := by omega
    -- i = ⟨k.val - 1, ...⟩; need k.val - 1 < n - 1
    have hk_val_sub_one_lt : k.val - 1 < n - 1 := by
      have hk_lt_n : k.val < n := k.2
      omega
    let i : Fin (n - 1) := ⟨k.val - 1, hk_val_sub_one_lt⟩
    have hi_val : i.val = k.val - 1 := rfl
    have hi_not_lt_j : ¬ (i.val < j.val) := by
      dsimp [i]; omega
    have h_eq : Fin.skip j i = k := by
      have hval : (Fin.skip j i).val = k.val := by
        unfold Fin.skip
        split
        · -- case h : i.val < j.val
          exfalso; exact hi_not_lt_j ‹_›
        · -- case h : ¬ i.val < j.val
          simp [hi_val, Nat.sub_add_cancel h_one_le_k]
      exact Fin.ext hval
    exact ⟨i, h_eq⟩

/-- `Fin.skip` depends only on the underlying values of `j` and `i`. -/
theorem Fin.skip_val_eq {n m : Nat} (j : Fin n) (j' : Fin m) (hjv : j'.val = j.val)
    (k : Fin (n - 1)) (k' : Fin (m - 1)) (hkv : k'.val = k.val) :
    (Fin.skip j' k').val = (Fin.skip j k).val := by
  unfold Fin.skip; simp only [hjv, hkv]; split <;> rfl

/-- Pruned table: remove short column at j. (Monicity: pending Fin.skip_surj) -/
def Table.prune (tab : Table 𝒞) (j : Fin tab.len) (hShort : tab.IsShort j) : Table 𝒞 where
  src   := tab.src
  len   := tab.len - 1
  codom := λ i => tab.codom (Fin.skip j i)
  col   := λ i => tab.col (Fin.skip j i)
  monic := by
    intro X f g hAgree
    apply tab.monic
    intro k
    by_cases hkj : k = j
    · rw [hkj]
      refine hShort X f g ?_
      intro i hi
      -- i.val < j.val < tab.len, so i.val < tab.len - 1
      have hi_lt_len_sub_one : i.val < tab.len - 1 := by
        have hj_lt_len : j.val < tab.len := j.2
        omega
      let i' : Fin (tab.len - 1) := ⟨i.val, hi_lt_len_sub_one⟩
      have h_skip_eq : Fin.skip j i' = i := by
        apply Fin.ext
        unfold Fin.skip
        -- i'.val = i.val < j.val, so the if-then branch is taken
        dsimp [i']
        simp [hi]
      -- hAgree i' gives equality on column (Fin.skip j i')
      have h_eq := hAgree i'
      rw [h_skip_eq] at h_eq
      exact h_eq
    · rcases Fin.skip_surj hkj with ⟨i', hi'⟩
      have h := hAgree i'
      rw [hi'] at h; exact h

/-! ## §1.49 intro Table composition -/

/-- Map a compound index into `S.comp T j` back to a column of S or T.
    Result len = S.len - 1 + T.len.
    Indices 0..j-1  → S column i
    Indices j..j+T.len-1 → T column (i-j), composed with S.col j
    Indices j+T.len..end → S column (i - T.len + 1) -/
private def compIdx (slen tlen : Nat) (j : Fin slen) (i : Fin (slen - 1 + tlen)) :
    Sum (Fin slen) (Fin tlen) :=
  if h1 : i.val < j.val then Sum.inl ⟨i.val, by omega⟩
  else if h2 : i.val < j.val + tlen then Sum.inr ⟨i.val - j.val, by omega⟩
  else Sum.inl ⟨i.val - tlen + 1, by omega⟩

/-- Table composition at column j: (S; x₁,…,xₘ) ; (T; y₁,…,yₙ) at j =
    (S; x₁,…,xⱼ₋₁, xⱼy₁,…,xⱼyₙ, xⱼ₊₁,…,xₘ).
    Result has length S.len - 1 + T.len. -/
-- Auxiliary: composition of table S with T replacing column j.
-- codom and col use dependent dite to pick the right type.
@[reducible] private def Table.compCodom (S T : Table 𝒞) (j : Fin S.len)
    (i : Fin (S.len - 1 + T.len)) : 𝒞 :=
  if h1 : i.val < j.val then S.codom ⟨i.val, by omega⟩
  else if h2 : i.val < j.val + T.len then T.codom ⟨i.val - j.val, by omega⟩
  else S.codom ⟨i.val - T.len + 1, by omega⟩

private def Table.compColMor (S T : Table 𝒞) (j : Fin S.len) (h_eq : T.src = S.codom j)
    (i : Fin (S.len - 1 + T.len)) : S.src ⟶ S.compCodom T j i :=
  if h1 : i.val < j.val then
    -- compCodom = S.codom ⟨i.val, _⟩ here; cast S.col ⟨i.val, _⟩ by symm
    (show S.codom ⟨i.val, by omega⟩ = S.compCodom T j i by
      simp [Table.compCodom, h1]) ▸ S.col ⟨i.val, by omega⟩
  else if h2 : i.val < j.val + T.len then
    -- compCodom = T.codom ⟨i.val - j.val, _⟩ here; cast via symm
    (show T.codom ⟨i.val - j.val, by omega⟩ = S.compCodom T j i by
      simp [Table.compCodom, h1, h2]) ▸
      (S.col j ≫ (h_eq ▸ T.col ⟨i.val - j.val, by omega⟩ :
        S.codom j ⟶ T.codom ⟨i.val - j.val, by omega⟩))
  else
    -- compCodom = S.codom ⟨i.val - T.len + 1, _⟩ here; cast via symm
    (show S.codom ⟨i.val - T.len + 1, by omega⟩ = S.compCodom T j i by
      simp [Table.compCodom, h1, h2]) ▸ S.col ⟨i.val - T.len + 1, by omega⟩

/-- Generic cast/associativity helper for the T-branch of `compColMor`.
    Abstracts the codomain cast `eC`, the bridge cast `eB : A = B`, the column
    index cast `eD`, so the whole thing reduces by `cases` on the three equalities. -/
private theorem heq_assoc_cast {X A B Tsrc C C' D : 𝒞} (f : X ⟶ A) (s : A ⟶ B)
    (t : Tsrc ⟶ C) (eB : Tsrc = B) (eC : C = C') (eD : C = D) :
    HEq (f ≫ ((eC ▸ (s ≫ (eB ▸ t : B ⟶ C)) : A ⟶ C') : A ⟶ C'))
        ((eB.symm ▸ (f ≫ s) : X ⟶ Tsrc) ≫ (eD ▸ t : Tsrc ⟶ D)) := by
  cases eB; cases eC; cases eD; dsimp only
  exact heq_of_eq (Cat.assoc f s t).symm

def Table.comp (S T : Table 𝒞) (j : Fin S.len) (h_eq : T.src = S.codom j) : Table 𝒞 where
  src   := S.src
  len   := S.len - 1 + T.len
  codom := S.compCodom T j
  col   := S.compColMor T j h_eq
  monic := by
    -- S.comp T j has columns = S columns (minus j) interleaved with xⱼyᵢ terms.
    -- We recover each S column via HEq using congr 1 for cast morphisms.
    intro X f g hAgree
    apply S.monic; intro k
    by_cases hkj : k.val < j.val
    · -- Index k < j: column k of comp = S.col k (cast)
      have hi_lt : k.val < S.len - 1 + T.len := by omega
      have h := hAgree ⟨k.val, hi_lt⟩
      have lhs : HEq (f ≫ S.compColMor T j h_eq ⟨k.val, hi_lt⟩) (f ≫ S.col k) := by
        unfold Table.compColMor; simp only [hkj, dite_true]
        congr 1; simp [Table.compCodom, hkj]; exact eqRec_heq _ _
      have rhs : HEq (g ≫ S.compColMor T j h_eq ⟨k.val, hi_lt⟩) (g ≫ S.col k) := by
        unfold Table.compColMor; simp only [hkj, dite_true]
        congr 1; simp [Table.compCodom, hkj]; exact eqRec_heq _ _
      exact eq_of_heq (lhs.symm.trans (heq_of_eq h) |>.trans rhs)
    · by_cases hkj2 : k.val = j.val
      · -- Index k = j: after subst hkj_eq, outer j → k; use T.monic on h_eq.symm ▸ casts.
        have hkj_eq : k = j := Fin.ext hkj2; subst hkj_eq
        -- goal: f ≫ S.col k = g ≫ S.col k (h_eq : T.src = S.codom k, j gone)
        have key : (h_eq.symm ▸ f ≫ S.col k) = (h_eq.symm ▸ g ≫ S.col k) :=
          T.monic _ _ (fun r => by
            have hr_lt : k.val + r.val < S.len - 1 + T.len := by omega
            have h1 : ¬ (k.val + r.val < k.val) := by omega
            have h2 : k.val + r.val < k.val + T.len := by omega
            have harg := hAgree ⟨k.val + r.val, hr_lt⟩
            -- Reduce compColMor at T-branch to get homogeneous equality
            -- After unfolding: compColMor = castP ▸ (S.col k ≫ h_eq ▸ T.col r')
            -- where r' = ⟨k+r-k, _⟩ and castP : T.codom r' = compCodom ...
            -- So f ≫ compColMor ≍ (h_eq.symm ▸ f ≫ S.col k) ≫ T.col r
            apply eq_of_heq
            have hrb : k.val + r.val - k.val < T.len := by have := r.isLt; omega
            -- the T-branch column index k+r-k is exactly r
            have hidx : (⟨k.val + r.val - k.val, hrb⟩ : Fin T.len) = r := by
              apply Fin.ext; simp
            -- compCodom cast (proof-irrelevant; any witness works)
            have eC : T.codom ⟨k.val + r.val - k.val, hrb⟩
                = S.compCodom T k ⟨k.val + r.val, hr_lt⟩ := by
              simp [Table.compCodom, h1, h2]
            have lhs2 : HEq (f ≫ S.compColMor T k h_eq ⟨k.val + r.val, hr_lt⟩)
                             ((h_eq.symm ▸ f ≫ S.col k) ≫ T.col r) := by
              unfold Table.compColMor; simp only [h1, dite_false, h2, dite_true]
              refine (heq_assoc_cast f (S.col k) (T.col _) h_eq eC rfl).trans ?_
              rw [hidx]
            have rhs2 : HEq (g ≫ S.compColMor T k h_eq ⟨k.val + r.val, hr_lt⟩)
                             ((h_eq.symm ▸ g ≫ S.col k) ≫ T.col r) := by
              unfold Table.compColMor; simp only [h1, dite_false, h2, dite_true]
              refine (heq_assoc_cast g (S.col k) (T.col _) h_eq eC rfl).trans ?_
              rw [hidx]
            exact lhs2.symm.trans ((heq_of_eq harg).trans rhs2))
        exact eq_of_heq ((eqRec_heq _ _).symm.trans (heq_of_eq key) |>.trans (eqRec_heq _ _))
      · -- Index k > j: column k of comp = S.col k (cast via index shift k+T.len-1)
        have hi_val : k.val + T.len - 1 < S.len - 1 + T.len := by omega
        have h1 : ¬ (k.val + T.len - 1 < j.val) := by omega
        have h2 : ¬ (k.val + T.len - 1 < j.val + T.len) := by omega
        have h := hAgree ⟨k.val + T.len - 1, hi_val⟩
        -- k > j ≥ 0, so k ≥ 1; the trailing-S branch index k+T.len-1-T.len+1 is exactly k
        have hk1 : 1 ≤ k.val := by omega
        have hsk : (⟨k.val + T.len - 1 - T.len + 1, by have := k.isLt; omega⟩ : Fin S.len) = k := by
          apply Fin.ext; show k.val + T.len - 1 - T.len + 1 = k.val; omega
        have lhs : HEq (f ≫ S.compColMor T j h_eq ⟨k.val + T.len - 1, hi_val⟩) (f ≫ S.col k) := by
          unfold Table.compColMor; simp only [h1, dite_false, h2]
          congr 1
          case e_5.h => simp only [Table.compCodom, h1, dite_false, h2]; exact congrArg S.codom hsk
          case e_7 => refine (eqRec_heq _ _).trans ?_; rw [hsk]
        have rhs : HEq (g ≫ S.compColMor T j h_eq ⟨k.val + T.len - 1, hi_val⟩) (g ≫ S.col k) := by
          unfold Table.compColMor; simp only [h1, dite_false, h2]
          congr 1
          case e_5.h => simp only [Table.compCodom, h1, dite_false, h2]; exact congrArg S.codom hsk
          case e_7 => refine (eqRec_heq _ _).trans ?_; rw [hsk]
        exact eq_of_heq (lhs.symm.trans (heq_of_eq h) |>.trans rhs)

/-! ## §1.491 τ-category -/

/-- The 1-column identity table on A: source = A, single column = id_A. -/
def idTable (A : 𝒞) : Table 𝒞 :=
  Table.mk A 1 (λ _ => A) (λ _ => Cat.id A)
    (λ _ f g h => by simpa [Cat.comp_id] using h 0)

/-- A τ-category: Cartesian category with distinguished class τ of tables (§1.491). -/
class TCat (𝒞 : Type u) [Cat.{v} 𝒞] where
  mem   : Table 𝒞 → Prop
  tau1  : ∀ tab : Table 𝒞, ∃ T : Table 𝒞, mem T ∧ Nonempty (TableIso tab T)
  tau1_unique : ∀ (tab T₁ T₂ : Table 𝒞), mem T₁ → mem T₂ →
    Nonempty (TableIso tab T₁) → Nonempty (TableIso tab T₂) → T₁ = T₂
  tau2_id : ∀ (A : 𝒞), mem (idTable A)
  tau2_comp : ∀ (S T : Table 𝒞) (j : Fin S.len) (h_eq : T.src = S.codom j),
    mem S → mem T → mem (S.comp T j h_eq)
  tau3 : ∀ (tab : Table 𝒞) (j : Fin tab.len) (h : tab.IsShort j),
    mem tab → mem (tab.prune j h)

namespace TCat

/-! ## §1.494 Resurfacing -/

structure Resurfacing (τ : TCat 𝒞) (tab : Table 𝒞) where
  rep : Table 𝒞
  mem : τ.mem rep
  iso : TableIso tab rep

theorem resurfacing_unique (τ : TCat 𝒞) {tab : Table 𝒞} (r₁ r₂ : τ.Resurfacing tab) :
    r₁.rep = r₂.rep :=
  τ.tau1_unique tab r₁.rep r₂.rep r₁.mem r₂.mem ⟨r₁.iso⟩ ⟨r₂.iso⟩

noncomputable def resurfacing (τ : TCat 𝒞) (tab : Table 𝒞) : τ.Resurfacing tab :=
  let h := τ.tau1 tab
  { rep := Classical.choose h
    mem := (Classical.choose_spec h).1
    iso := Classical.choice (Classical.choose_spec h).2 }

theorem mem_iff_resurfacing_eq (τ : TCat 𝒞) (tab : Table 𝒞) :
    τ.mem tab ↔ (τ.resurfacing tab).rep = tab := by
  constructor
  · intro hmem
    exact τ.tau1_unique tab _ _ (τ.resurfacing tab).mem hmem
      ⟨(τ.resurfacing tab).iso⟩ ⟨TableIso.refl tab⟩
  · intro h; exact h ▸ (τ.resurfacing tab).mem

end TCat


/-! ## §1.412 Table terminology -/

/-- The TOP of a table: the common source object. -/
def Table.top (tab : Table 𝒞) : 𝒞 := tab.src

/-- A COLUMN of a table: the i-th morphism from top to foot. -/
def Table.column (tab : Table 𝒞) (i : Fin tab.len) : tab.src ⟶ tab.codom i := tab.col i

/-- The FEET of a table: the sequence of target objects. -/
def Table.feet (tab : Table 𝒞) : Fin tab.len → 𝒞 := tab.codom

/-- A RELATION on a sequence of feet A₁,…,Aₙ is an isomorphism class of tables (§1.412).
    For n=2, BinRel represents this directly. -/
def Relation (feet : Fin 2 → 𝒞) : Type _ := Table 𝒞

/-! ## §1.4(10) Free T-category -/

/-- FREE T-CATEGORY (§1.4(10)): the free τ-category on a Cartesian category.

    MISSING: the freeness universal property is not yet formalized — the book's
    construction (via well-made tables, §1.4(10)1) and its universal mapping
    property still need to be stated and proved.  We therefore do NOT carry a
    vacuous `isFree : True` field (that would be a fake stub); `FreeTCategory`
    is, for now, just a τ-category designated as free, with the characterizing
    universal property recorded as MISSING in S1_49.md. -/
class FreeTCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends TCat 𝒞

/-! ## §1.4(10)1 Well-made -/

/-- A table is WELL-MADE if every column is short (§1.4(10)1). -/
def WellMade (tab : Table 𝒞) : Prop :=
  ∀ (i : Fin tab.len), tab.IsShort i

/-- A WELL-MADE PART of a table: a sub-table (via prune) that is well-made. -/
def WellMadePart (tab : Table 𝒞) : Table 𝒞 := tab

/-! ## §1.4(11) Canonical slice -/

/-- CANONICAL SLICE (§1.4(11)): the slice A/B inherits τ-structure from A. -/
def canonicalSlice (τ : TCat 𝒞) (B : 𝒞) : TCat 𝒞 := τ

/-! ## §1.4(11)4 Generic point -/

/-- GENERIC POINT (§1.4(11)4): the identity map B→B as an object of A/B. -/
def GenericPoint (B : 𝒞) : Table 𝒞 := idTable B

/-! ## §1.49(11) Auspicious -/

/-- AUSPICIOUS (§1.49(11)): a sequence expandable to a τ-table.
    The columns of `tab` agree with the first `tab.len` columns of `tab'`. -/
def Auspicious (τ : TCat 𝒞) (tab : Table 𝒞) : Prop :=
  ∃ (tab' : Table 𝒞) (h_len : tab.len ≤ tab'.len), τ.mem tab' ∧ tab.src = tab'.src ∧
    (∀ i : Fin tab.len, HEq (tab.col i) (tab'.col (Fin.castLE h_len i)))

/-! ## §1.492 Supporting subsequences and general PRUNE -/

/-- A SUPPORTING subsequence: a strictly increasing selection `sel : Fin k → Fin tab.len`
    such that the selected columns are still jointly monic (§1.492).
    The book says "a subsequence i₁,…,iₖ is SUPPORTING if (T; xᵢ₁,…,xᵢₖ) satisfies
    the monic condition." -/
def Table.IsSupporting (tab : Table 𝒞) {k : Nat} (sel : Fin k → Fin tab.len) : Prop :=
  ∀ ⦃X : 𝒞⦄ (f g : X ⟶ tab.src), (∀ r : Fin k, f ≫ tab.col (sel r) = g ≫ tab.col (sel r)) → f = g

/-- A PRUNE along a supporting subsequence: the sub-table with selected columns (§1.492).
    Unlike `Table.prune` (which removes a single short column), this is the general PRUNE:
    any supporting subsequence yields a valid (jointly-monic) table. -/
def Table.pruneAlong (tab : Table 𝒞) {k : Nat} (sel : Fin k → Fin tab.len)
    (hSup : tab.IsSupporting sel) : Table 𝒞 where
  src   := tab.src
  len   := k
  codom := λ r => tab.codom (sel r)
  col   := λ r => tab.col (sel r)
  monic := hSup

/-- Every supporting subsequence of a supporting subsequence is supporting. -/
theorem Table.IsSupporting.trans (tab : Table 𝒞) {k₁ k₂ : Nat}
    (sel₁ : Fin k₁ → Fin tab.len) (sel₂ : Fin k₂ → Fin k₁)
    (h₁ : tab.IsSupporting sel₁) (h₂ : (tab.pruneAlong sel₁ h₁).IsSupporting sel₂) :
    tab.IsSupporting (fun r => sel₁ (sel₂ r)) :=
  fun X f g hAgree => h₂ f g (fun r => hAgree r)

/-- The full index list `id : Fin n → Fin n` is supporting (trivially, by original monicity). -/
theorem Table.isSupporting_id (tab : Table 𝒞) : tab.IsSupporting id :=
  fun X f g hAgree => tab.monic f g (fun i => hAgree i)

/-! ## §1.494 Expansion lemma (converse of axiom 3) -/

/-- Two tables are equal if their fields match (codom/col up to HEq). -/
private theorem Table_eq_of_fields {𝒞 : Type u} [Cat.{v} 𝒞] (S T : Table 𝒞)
    (hSrc : S.src = T.src) (hLen : S.len = T.len)
    (hCodom : HEq S.codom T.codom) (hCol : HEq S.col T.col) : S = T := by
  obtain ⟨Ss, Sn, SC, Sc, Sm⟩ := S
  obtain ⟨Ts, Tn, TC, Tc, Tm⟩ := T
  simp only at hSrc hLen hCodom hCol ⊢
  subst hSrc; subst hLen
  cases hCodom; cases hCol
  rfl

/-- Two `Fin`s over (propositionally) equal lengths with equal values are heterogeneously equal. -/
private theorem fin_heq {m n : Nat} (h : m = n) (a : Fin m) (b : Fin n) (hv : a.val = b.val) :
    HEq a b := by cases h; cases a; cases b; cases hv; rfl

/-- Columns of equal tables agree (heterogeneously, at heterogeneously-equal indices). -/
private theorem Table.col_heq_of_eq {𝒞 : Type u} [Cat.{v} 𝒞] {A B : Table 𝒞} (hAB : A = B)
    {i : Fin A.len} {i' : Fin B.len} (hii : HEq i i') : HEq (A.col i) (B.col i') := by
  subst hAB; cases hii; rfl

/-- Heterogeneous extensionality for the `col` field of a table, over a length equality,
    with the source object also allowed to differ. -/
private theorem Table.col_heq_funext {𝒞 : Type u} [Cat.{v} 𝒞] {A B : Table 𝒞}
    (hSrc : A.src = B.src) (hLen : A.len = B.len)
    (hCod : ∀ i : Fin A.len, A.codom i = B.codom (hLen ▸ i))
    (hpt : ∀ i : Fin A.len, HEq (A.col i) (B.col (hLen ▸ i))) : HEq A.col B.col := by
  obtain ⟨As, An, AC, Ac, _⟩ := A
  obtain ⟨Bs, Bn, BC, Bc, _⟩ := B
  simp only at hSrc hLen hCod hpt ⊢
  subst hSrc; subst hLen
  have hCC : AC = BC := funext hCod
  subst hCC
  exact heq_of_eq (funext fun i => eq_of_heq (hpt i))

namespace TCat

/-- §1.494 forward: τ-closure under pruning (= axiom 3 restated).
    If a table is in τ and column j is short, the pruned table is in τ. -/
theorem mem_prune {τ : TCat 𝒞} {tab : Table 𝒞} {j : Fin tab.len}
    (hShort : tab.IsShort j) (hmem : τ.mem tab) : τ.mem (tab.prune j hShort) :=
  τ.tau3 tab j hShort hmem

/-- §1.494 converse: if the pruned table is in τ then the original table is in τ.
    Proof: let `r` be the resurfacing of `tab` (so `r.rep ∈ τ` with `r.iso : tab ≅ r.rep`).
    Column `j` is short in `r.rep` (transport of shortness along `r.iso`), so by τ3 the pruned
    resurfacing `r.rep.prune j'` is in τ.  It is iso to `tab.prune j`, which is in τ by
    hypothesis, so τ1-uniqueness gives `r.rep.prune j' = tab.prune j`.  This forces
    `r.rep.src = tab.src` and pins every non-`j` column; with the short column `j` and joint
    monicity, the iso component `r.iso.f` is the identity, hence `r.rep = tab` and `tab ∈ τ`. -/
theorem mem_of_prune_mem {τ : TCat 𝒞} (tab : Table 𝒞) (j : Fin tab.len)
    (hShort : tab.IsShort j) (h : τ.mem (tab.prune j hShort)) : τ.mem tab := by
  -- Book §1.494: let g : T'' → tab.src be the resurfacing of tab.
  -- T'' = r.rep.src, and (T''; gx₁,…,gxₙ) ∈ τ.
  -- By τ3, (T''; gx₁,…,ĝxⱼ,…,gxₙ) ∈ τ.
  -- This is iso to tab.prune j hShort (via g extended to the pruned table).
  -- By τ1-uniqueness, that rep = tab.prune j hShort (since h says tab.prune ∈ τ).
  -- In particular, r.rep.src = tab.src and all columns match (except j).
  -- Using tab.monic, r.iso.f = id, so r.rep = tab, hence τ.mem tab.
  let r := τ.resurfacing tab
  -- j' is j cast to r.rep
  let j' : Fin r.rep.len := r.iso.hLen ▸ j
  -- hj'val : j'.val = j.val
  have hj'val : j'.val = j.val := fin_cast_val r.iso.hLen j
  -- Step 1: transfer IsShort via the iso
  -- r.rep.IsShort j' because tab.IsShort j and the iso is an equivalence.
  have hShort' : r.rep.IsShort j' := by
    intro X f g hAgree
    -- Transfer to tab via r.iso.g.  For each column index kk:
    --   HEq (h ≫ r.rep.col (hLen ▸ kk)) ((h ≫ r.iso.g) ≫ tab.col kk)
    -- using col_match_g kk : HEq (r.iso.g ≫ tab.col kk) (r.rep.col (hLen ▸ kk)).
    have hbridge : ∀ (h : X ⟶ r.rep.src) (kk : Fin tab.len),
        HEq (h ≫ r.rep.col (r.iso.hLen ▸ kk)) ((h ≫ r.iso.g) ≫ tab.col kk) := by
      intro h kk
      have hcg := (r.iso.col_match_g kk).symm
      -- hcg : HEq (r.rep.col (hLen ▸ kk)) (r.iso.g ≫ tab.col kk)
      have e1 : HEq (h ≫ r.rep.col (r.iso.hLen ▸ kk)) (h ≫ (r.iso.g ≫ tab.col kk)) :=
        comp_heq_left h _ _ (r.iso.codom_match kk) hcg
      exact e1.trans (heq_of_eq (Cat.assoc h r.iso.g (tab.col kk)).symm)
    -- Agreement of f≫g₀ and g≫g₀ on early tab columns
    have hAgree_tab : ∀ k : Fin tab.len, k.val < j.val →
        (f ≫ r.iso.g) ≫ tab.col k = (g ≫ r.iso.g) ≫ tab.col k := by
      intro k hk
      have hk' : (r.iso.hLen ▸ k : Fin r.rep.len).val < j'.val := by
        rw [fin_cast_val r.iso.hLen k, hj'val]; exact hk
      have hAk := hAgree (r.iso.hLen ▸ k) hk'
      -- hAk : f ≫ r.rep.col (hLen ▸ k) = g ≫ r.rep.col (hLen ▸ k)
      exact eq_of_heq ((hbridge f k).symm.trans (heq_of_eq hAk |>.trans (hbridge g k)))
    have hJ := hShort X (f ≫ r.iso.g) (g ≫ r.iso.g) (fun k hk => by
      simp only [Cat.assoc] at hAgree_tab ⊢
      exact hAgree_tab k hk)
    -- hJ : (f ≫ r.iso.g) ≫ tab.col j = (g ≫ r.iso.g) ≫ tab.col j
    -- Transfer back to r.rep.col j' via hbridge at kk = j.
    exact eq_of_heq ((hbridge f j).trans (heq_of_eq hJ |>.trans (hbridge g j).symm))
  -- Step 2: By τ3, τ.mem (r.rep.prune j' hShort')
  have hPruneRep : τ.mem (r.rep.prune j' hShort') := τ.tau3 r.rep j' hShort' r.mem
  -- Step 3: Construct TableIso (tab.prune j hShort) (r.rep.prune j' hShort')
  have hPruneIso : Nonempty (TableIso (tab.prune j hShort) (r.rep.prune j' hShort')) := by
    have hLenP : tab.len - 1 = r.rep.len - 1 := by rw [r.iso.hLen]
    refine ⟨{
      hLen        := by simp [Table.prune]; exact hLenP
      f           := r.iso.f
      g           := r.iso.g
      f_g         := r.iso.f_g
      g_f         := r.iso.g_f
      codom_match := fun k => ?_
      col_match   := fun k => ?_
    }⟩
    · -- rep.prune.codom (hLenP ▸ k) = tab.prune.codom k
      -- i.e., r.rep.codom (Fin.skip j' (hLenP ▸ k)) = tab.codom (Fin.skip j k)
      simp only [Table.prune]
      have hskip : Fin.skip j' (hLenP ▸ k) = r.iso.hLen ▸ Fin.skip j k := by
        apply Fin.ext
        rw [Fin.skip_val_eq j j' hj'val k (hLenP ▸ k) (fin_cast_val hLenP k),
          fin_cast_val r.iso.hLen (Fin.skip j k)]
      rw [hskip]; exact r.iso.codom_match (Fin.skip j k)
    · -- HEq (r.iso.f ≫ r.rep.prune.col (hLenP ▸ k)) (tab.prune.col k)
      -- i.e., HEq (r.iso.f ≫ r.rep.col (Fin.skip j' (hLenP ▸ k))) (tab.col (Fin.skip j k))
      simp only [Table.prune]
      have hskip : Fin.skip j' (hLenP ▸ k) = r.iso.hLen ▸ Fin.skip j k := by
        apply Fin.ext
        rw [Fin.skip_val_eq j j' hj'val k (hLenP ▸ k) (fin_cast_val hLenP k),
          fin_cast_val r.iso.hLen (Fin.skip j k)]
      rw [hskip]; exact r.iso.col_match (Fin.skip j k)
  -- Step 4: tau1_unique gives r.rep.prune = tab.prune
  have hPruneEq : r.rep.prune j' hShort' = tab.prune j hShort :=
    τ.tau1_unique (tab.prune j hShort) _ _ hPruneRep h hPruneIso ⟨TableIso.refl _⟩
  -- Step 5: extract r.rep.src = tab.src from the prune equality
  have hSrc : r.rep.src = tab.src := congrArg (·.src) hPruneEq
  -- Step 6: column-of-prune HEq, transported to homogeneous skip-column equality.
  -- Both prune tables have src = tab.src and r.rep.src; the prune equality forces all
  -- skip-columns to agree.  We extract this as a heterogeneous column-function equality.
  have hColHEq : HEq (r.rep.prune j' hShort').col (tab.prune j hShort).col := by
    rw [hPruneEq]
  -- The prune-tables' codom families also match (same data after the equality).
  have hCodHEq : HEq (r.rep.prune j' hShort').codom (tab.prune j hShort).codom := by
    rw [hPruneEq]
  -- Homogeneous skip-column equality: r.rep.col (skip j' (hLenP ▸ i)) ≍ tab.col (skip j i).
  have hLenP : tab.len - 1 = r.rep.len - 1 := by rw [r.iso.hLen]
  have hSkipCol : ∀ i : Fin (tab.len - 1),
      HEq (r.rep.col (Fin.skip j' (hLenP ▸ i))) (tab.col (Fin.skip j i)) := by
    intro i
    -- (r.rep.prune).col (hLenP ▸ i) ≡ r.rep.col (skip j' (hLenP ▸ i)) and
    -- (tab.prune).col i ≡ tab.col (skip j i), both definitional.
    have hii : HEq (hLenP ▸ i : Fin (r.rep.len - 1)) i := eqRec_heq hLenP i
    have := Table.col_heq_of_eq hPruneEq
      (i := (hLenP ▸ i : Fin (r.rep.len - 1))) (i' := i) hii
    exact this
  -- Step 7: r.iso.f is (heterogeneously) the identity on tab.src.
  have hFf : HEq r.iso.f (Cat.id tab.src) := by
    have hHEq : HEq (castCod hSrc r.iso.f) r.iso.f := castCod_heq hSrc r.iso.f
    -- agreement of f₀ with id on every skip-column
    have hAgreeSkip : ∀ i : Fin (tab.len - 1),
        castCod hSrc r.iso.f ≫ tab.col (Fin.skip j i) = tab.col (Fin.skip j i) := by
      intro i
      apply eq_of_heq
      -- f₀ ≫ tab.col (skip j i) ≍ f ≫ r.rep.col (skip j' (hLenP ▸ i)) ≍ tab.col (skip j i)
      have hcm := r.iso.col_match (Fin.skip j i)
      have hidx : r.iso.hLen ▸ Fin.skip j i = Fin.skip j' (hLenP ▸ i) := by
        apply Fin.ext
        rw [fin_cast_val, Fin.skip_val_eq j j' hj'val i (hLenP ▸ i) (fin_cast_val hLenP i)]
      have hcodi : tab.codom (Fin.skip j i) = r.rep.codom (Fin.skip j' (hLenP ▸ i)) := by
        rw [← hidx]; exact (r.iso.codom_match (Fin.skip j i)).symm
      rw [hidx] at hcm
      -- hcm : HEq (r.iso.f ≫ r.rep.col (skip j' (hLenP ▸ i))) (tab.col (skip j i))
      refine HEq.trans ?_ hcm
      exact comp_heq (castCod hSrc r.iso.f) r.iso.f (tab.col (Fin.skip j i))
        (r.rep.col (Fin.skip j' (hLenP ▸ i))) rfl hSrc.symm
        hcodi hHEq (hSkipCol i).symm
    have hf0id : castCod hSrc r.iso.f = Cat.id tab.src := by
      apply tab.monic; intro k; rw [Cat.id_comp]
      by_cases hkj : k = j
      · -- k = j: short column; agreement on all earlier (skip) columns forces it.
        rw [hkj]
        have hsj : castCod hSrc r.iso.f ≫ tab.col j = Cat.id tab.src ≫ tab.col j :=
          hShort tab.src (castCod hSrc r.iso.f) (Cat.id tab.src) (fun i hi => by
            -- i < j; i = skip j i₀ for some i₀ (Fin.skip is surjective off j)
            have hij : i ≠ j := fun he => by rw [he] at hi; exact Nat.lt_irrefl _ hi
            rcases Fin.skip_surj hij with ⟨i₀, hi₀⟩
            rw [← hi₀, hAgreeSkip i₀, Cat.id_comp])
        rw [hsj, Cat.id_comp]
      · -- k ≠ j: k = skip j i₀
        rcases Fin.skip_surj hkj with ⟨i₀, hi₀⟩
        rw [← hi₀]; exact hAgreeSkip i₀
    exact hf0id ▸ hHEq.symm
  -- Step 8: conclude r.rep = tab
  -- index round-trip: hLen ▸ (hLen.symm ▸ k) = k
  have hidx_rt : ∀ k : Fin r.rep.len,
      (r.iso.hLen ▸ (r.iso.hLen.symm ▸ k : Fin tab.len) : Fin r.rep.len) = k := fun k => by
    apply Fin.ext; rw [fin_cast_val, fin_cast_val]
  -- pointwise codom equality (oriented for the funext helpers)
  have hCodPt : ∀ k : Fin r.rep.len, r.rep.codom k = tab.codom (r.iso.hLen.symm ▸ k) := by
    intro k; have hc := r.iso.codom_match (r.iso.hLen.symm ▸ k); rw [hidx_rt k] at hc; exact hc
  have hrep_eq : r.rep = tab := by
    apply Table_eq_of_fields r.rep tab hSrc r.iso.hLen.symm
    · -- HEq r.rep.codom tab.codom
      exact heq_funext_fin r.iso.hLen.symm r.rep.codom tab.codom hCodPt
    · -- HEq r.rep.col tab.col
      refine Table.col_heq_funext hSrc r.iso.hLen.symm hCodPt (fun k => ?_)
      -- HEq (r.rep.col k) (tab.col (hLen.symm ▸ k)); from col_match with hFf (f ≍ id).
      have hcm := r.iso.col_match (r.iso.hLen.symm ▸ k)
      rw [hidx_rt k] at hcm
      -- hcm : HEq (r.iso.f ≫ r.rep.col k) (tab.col (hLen.symm ▸ k))
      refine HEq.trans ?_ hcm
      -- r.rep.col k ≍ r.iso.f ≫ r.rep.col k, using f ≍ id.
      have hidHEq : HEq (Cat.id r.rep.src) r.iso.f := by
        refine HEq.trans ?_ hFf.symm
        -- HEq (Cat.id r.rep.src) (Cat.id tab.src)
        rw [hSrc]
      have hcomp : HEq (Cat.id r.rep.src ≫ r.rep.col k) (r.iso.f ≫ r.rep.col k) :=
        comp_heq (Cat.id r.rep.src) r.iso.f (r.rep.col k) (r.rep.col k)
          hSrc rfl rfl hidHEq HEq.rfl
      exact (heq_of_eq (Cat.id_comp (r.rep.col k))).symm.trans hcomp
  exact hrep_eq ▸ r.mem

/-- §1.494 EXPANSION LEMMA: a table is in τ iff its pruned table is in τ (§1.494).
    Removing (or keeping) a short column does not change τ-membership. -/
theorem expansionLemma {τ : TCat 𝒞} {tab : Table 𝒞} {j : Fin tab.len}
    (hShort : tab.IsShort j) : τ.mem tab ↔ τ.mem (tab.prune j hShort) :=
  ⟨mem_prune hShort, mem_of_prune_mem tab j hShort⟩

/-- §1.494 corollary: any expansion of a τ-table is a τ-table.
    If `(T; x₁,…,xₙ) ∈ τ` and `xₙ₊₁ : T → B`, then `(T; x₁,…,xₙ,xₙ₊₁) ∈ τ`.
    The extra column is short since the original columns already separate all points.
    We state this over an explicit expanded Table; codomain equalities carried explicitly
    so that `tab'.prune last = tab` can be established via `Table_eq_of_fields`. -/
theorem mem_expansion (τ : TCat 𝒞) (tab : Table 𝒞) (hmem : τ.mem tab)
    (B : 𝒞) (extra : tab.src ⟶ B)
    (tab' : Table 𝒞)
    (hSrc : tab'.src = tab.src)
    (hLen : tab'.len = tab.len + 1)
    -- codomain equalities (needed for Table_eq_of_fields; not derivable from HEq alone)
    (hCodEq : ∀ i : Fin tab.len, tab'.codom (hLen ▸ Fin.castSucc i) = tab.codom i)
    (hCodLast : tab'.codom (hLen ▸ Fin.last tab.len) = B)
    -- column equalities (HEq since source objects differ by hSrc)
    (hCols : ∀ i : Fin tab.len,
      HEq (tab'.col (hLen ▸ Fin.castSucc i)) (hSrc ▸ tab.col i))
    (hLast : HEq (tab'.col (hLen ▸ Fin.last tab.len)) (hSrc ▸ extra)) :
    τ.mem tab' := by
  let j : Fin tab'.len := hLen ▸ Fin.last tab.len
  have hj_val : j.val = tab.len := by simp [j, fin_cast_val]
  -- Last column j is short: f,g agreeing on earlier cols agree by tab.monic.
  have hShort : tab'.IsShort j := by
    intro X f g hAgree
    -- hSrc ▸ tab.col i is domain cast: tab.src → tab'.src (= hSrc.symm ▸ tab.col i).
    -- We denote it by notation in hCols but use eqRec_heq hSrc.symm for HEq proofs.
    have key : ∀ i : Fin tab.len,
        (hSrc ▸ f : X ⟶ tab.src) ≫ tab.col i = (hSrc ▸ g) ≫ tab.col i := by
      intro i
      have hi_lt : (hLen ▸ Fin.castSucc i : Fin tab'.len).val < j.val := by
        simp [fin_cast_val, hj_val]
      have hAg := hAgree (hLen ▸ Fin.castSucc i) hi_lt
      -- (hSrc▸f) ≫ col i ≍ f ≫ (hSrc.symm▸col i) [comp_heq; castCod_heq; eqRec_heq]
      -- f ≫ (hSrc.symm▸col i) ≍ f ≫ tab'.col (castSucc i) [comp_heq_left; (hCols i).symm]
      -- f ≫ tab'.col ... = g ≫ tab'.col ...  [hAg]
      -- g ≫ tab'.col ... ≍ g ≫ (hSrc.symm▸col i) ≍ (hSrc▸g) ≫ col i
      apply eq_of_heq
      -- Step 1: (hSrc▸f) ≫ col i ≍ f ≫ (hSrc.symm▸col i)
      have heq_col_cast : HEq (tab.col i) (hSrc.symm ▸ tab.col i) :=
        (@eqRec_heq 𝒞 (fun x => x ⟶ tab.codom i) tab.src tab'.src hSrc.symm (tab.col i)).symm
      have step1f : HEq ((hSrc ▸ f) ≫ tab.col i) (f ≫ (hSrc.symm ▸ tab.col i)) :=
        comp_heq (hSrc ▸ f) f (tab.col i) (hSrc.symm ▸ tab.col i)
          rfl hSrc.symm rfl (castCod_heq hSrc f) heq_col_cast
      -- Step 2: f ≫ (hSrc.symm▸col i) ≍ f ≫ tab'.col (castSucc i)  [via (hCols i).symm]
      have step2f : HEq (f ≫ (hSrc.symm ▸ tab.col i)) (f ≫ tab'.col (hLen ▸ Fin.castSucc i)) :=
        comp_heq_left f (hSrc.symm ▸ tab.col i) (tab'.col (hLen ▸ Fin.castSucc i))
          (hCodEq i).symm (hCols i).symm
      -- Step 3: g ≫ tab'.col ... ≍ g ≫ (hSrc.symm▸col i) ≍ (hSrc▸g) ≫ col i
      have step3g : HEq (g ≫ tab'.col (hLen ▸ Fin.castSucc i)) (g ≫ (hSrc.symm ▸ tab.col i)) :=
        comp_heq_left g (tab'.col (hLen ▸ Fin.castSucc i)) (hSrc.symm ▸ tab.col i)
          (hCodEq i) (hCols i)
      have step4g : HEq (g ≫ (hSrc.symm ▸ tab.col i)) ((hSrc ▸ g) ≫ tab.col i) :=
        (comp_heq (hSrc ▸ g) g (tab.col i) (hSrc.symm ▸ tab.col i)
          rfl hSrc.symm rfl (castCod_heq hSrc g) heq_col_cast).symm
      exact step1f.trans (step2f.trans (heq_of_eq hAg |>.trans (step3g.trans step4g)))
    have hfg : (hSrc ▸ f : X ⟶ tab.src) = hSrc ▸ g := tab.monic _ _ key
    -- recover f = g: castCod_heq hSrc f : HEq (hSrc▸f) f, so f ≍ hSrc▸f = hSrc▸g ≍ g
    have hfg' : f = g :=
      eq_of_heq ((castCod_heq hSrc f).symm.trans (heq_of_eq hfg |>.trans (castCod_heq hSrc g)))
    rw [hfg']
  apply mem_of_prune_mem tab' j hShort
  have hLenPrune : tab'.len - 1 = tab.len := by omega
  have hskip_val : ∀ i : Fin (tab'.len - 1), (Fin.skip j i).val = i.val := by
    intro i; have hi_lt : i.val < j.val := by have := i.isLt; simp [hj_val]; omega
    simp [Fin.skip, hi_lt]
  have hskip_eq : ∀ i : Fin (tab'.len - 1),
      Fin.skip j i = hLen ▸ Fin.castSucc (hLenPrune ▸ i) := by
    intro i; apply Fin.ext; simp [hskip_val i, fin_cast_val, Fin.val_castSucc]
  have hCodPt : ∀ i : Fin (tab'.len - 1),
      (tab'.prune j hShort).codom i = tab.codom (hLenPrune ▸ i) := by
    intro i; simp only [Table.prune, hskip_eq i]; exact hCodEq (hLenPrune ▸ i)
  have hPruneEq : tab'.prune j hShort = tab := by
    apply Table_eq_of_fields (tab'.prune j hShort) tab hSrc hLenPrune
    · apply heq_funext_fin hLenPrune
      intro i; simp only [Table.prune]; exact hCodPt i
    · apply @Table.col_heq_funext 𝒞 _ (tab'.prune j hShort) tab hSrc hLenPrune hCodPt
      intro i
      -- i : Fin (tab'.prune j hShort).len = Fin (tab'.len - 1)
      -- Coerce i to the right Fin type for hskip_eq
      have hilen : i.val < tab.len := by
        have h1 := i.isLt; simp only [Table.prune] at h1; omega
      let k : Fin tab.len := ⟨i.val, hilen⟩
      have hi_prune_lt : i.val < tab'.len - 1 := by
        have h1 := i.isLt; simp only [Table.prune] at h1; omega
      let i' : Fin (tab'.len - 1) := ⟨i.val, hi_prune_lt⟩
      have hi'_eq_i : i = i'.castLE (by simp [Table.prune]) := by simp [i', Fin.ext_iff]
      simp only [Table.prune] at *
      rw [show (i : Fin (tab'.len - 1)) = i' from rfl, hskip_eq i']
      -- goal: HEq (tab'.col (hLen ▸ (hLenPrune ▸ i').castSucc)) (tab.col (hLenPrune ▸ i'))
      -- note: hLenPrune ▸ i' = k (same val)
      have hki' : hLenPrune ▸ i' = k := Fin.ext (by simp [i', k, fin_cast_val])
      rw [hki']
      exact (hCols k).trans
        (@eqRec_heq 𝒞 (fun x => x ⟶ tab.codom k) tab.src tab'.src hSrc.symm (tab.col k))
  rw [hPruneEq]; exact hmem

end TCat

/-! ## §1.496 Subterminators in a τ-category -/

namespace TCat

variable [HasTerminal 𝒞]

/-- §1.496: If T is a subterminator in a τ-category then `(T; f) ∈ τ` for any `f : T → T'`.
    Reason: `f` is short (T is a subterminator, so T→1 is monic; any two maps into T
    that agree on `f` agree on `T→1` trivially, hence are equal). -/
theorem subterminator_one_col_mem (τ : TCat 𝒞) {T T' : 𝒞} (hSub : Subterminator T)
    (f : T ⟶ T') : τ.mem
      { src   := T
        len   := 1
        codom := fun _ => T'
        col   := fun _ => f
        monic := by
          intro X g h _hAg; apply hSub; apply term_uniq } := by
  -- Build tab2 = (T; id_T, f): expansion of idTable T by column f.
  -- codom: Fin 2 → 𝒞 with [T, T']; col: Fin 2 → hom with [id_T, f]
  let codom2 : Fin 2 → 𝒞 := fun i => if i.val = 0 then T else T'
  let col2 : (i : Fin 2) → T ⟶ codom2 i := fun i => by
    simp only [codom2]; split
    · exact Cat.id T
    · exact f
  let tab2 : Table 𝒞 :=
    { src   := T
      len   := 2
      codom := codom2
      col   := col2
      monic := by
        intro X g h _hAg; apply hSub; apply term_uniq }
  have hmem_id : τ.mem (idTable T) := τ.tau2_id T
  -- tab2 ∈ τ via mem_expansion: idTable T + extra col f
  -- Prove membership of tab2 via mem_expansion.
  -- idTable T has len=1; all ∀ i : Fin 1 goals are trivial.
  have hilen_id : (idTable T).len = 1 := rfl
  have hmem2 : τ.mem tab2 := by
    apply mem_expansion τ (idTable T) hmem_id T' f tab2 rfl rfl
    · -- hCodEq: ∀ i : Fin 1, tab2.codom (castSucc i) = (idTable T).codom i  (i.val=0)
      intro i
      -- i.val = 0 since i : Fin (idTable T).len = Fin 1
      have hiv : i.val = 0 := by have h : i.val < 1 := i.isLt; omega
      -- (idTable T).len = 1, so Fin.castAdd 1 i has val = 0; tab2.codom ⟨0,_⟩ = T
      change tab2.codom _ = T
      have hcs : (Fin.castSucc i : Fin 2) = ⟨0, by omega⟩ := by ext; simp [Fin.castSucc]
      simp [codom2, hcs, tab2]
    · -- hCodLast: tab2.codom (Fin.last 1) = T'  (Fin.last 1 has val=1 ≠ 0)
      change tab2.codom _ = T'
      simp [codom2, Fin.last, tab2, hilen_id]
    · -- hCols: ∀ i : Fin 1, HEq (tab2.col (castSucc i)) ((idTable T).col i)
      intro i
      have hiv : i.val = 0 := by have h : i.val < 1 := i.isLt; omega
      -- both sides = Cat.id T
      change HEq (tab2.col _) ((idTable T).col i)
      have hcs : (Fin.castSucc i : Fin 2) = ⟨0, by omega⟩ := by ext; simp [Fin.castSucc]
      rw [hcs]
      have hdec : instDecidableEqNat 0 0 = isTrue rfl := Subsingleton.elim _ _
      simp [col2, codom2, hdec, tab2, idTable]
    · -- hLast: HEq (tab2.col (Fin.last 1)) f
      change HEq (tab2.col _) f
      have hdec : instDecidableEqNat 1 0 = isFalse (by decide) := Subsingleton.elim _ _
      simp [col2, codom2, Fin.last, hdec, tab2, idTable]
  -- Column 0 of tab2 (= id_T) is short: subterminator T forces any f=g
  have hShort0 : tab2.IsShort ⟨0, Nat.succ_pos 1⟩ := by
    intro X g h _hAgree
    apply hSub; apply term_uniq
  -- mem_prune: tab2 ∈ τ → tab2.prune ⟨0,_⟩ ∈ τ
  have hPrune := mem_prune hShort0 hmem2
  -- tab2.prune ⟨0,_⟩ hShort0 equals {len=1, codom=T', col=f}
  suffices heq : tab2.prune ⟨0, Nat.succ_pos 1⟩ hShort0 =
      { src := T, len := 1, codom := fun _ => T', col := fun _ => f,
        monic := by intro X g h _hAg; apply hSub; apply term_uniq } by
    rw [← heq]; exact hPrune
  have hplen_def : (tab2.prune ⟨0, Nat.succ_pos 1⟩ hShort0).len = 1 := by simp [Table.prune, tab2]
  apply Table_eq_of_fields _ _ rfl rfl
  · -- HEq codom: prune.codom i = T' for the single i (val=0, skip gives val=1)
    apply heq_funext_fin rfl
    intro i
    have hiv : i.val = 0 := by have h : i.val < 1 := i.isLt; omega
    simp [Table.prune, Fin.skip, hiv, codom2]
  · -- HEq col
    apply Table.col_heq_funext rfl rfl
    · intro i
      have hiv : i.val = 0 := by have h : i.val < 1 := i.isLt; omega
      simp [Table.prune, Fin.skip, hiv, codom2]
    · intro i
      have hiv : i.val = 0 := by have h : i.val < 1 := i.isLt; omega
      simp [Table.prune, Fin.skip, hiv, col2, codom2]

/-- For a subterminator `T`, any two maps into `T` are equal (the defining property:
    `term T` is monic, and any two maps into `one` agree by `term_uniq`). -/
theorem subterminator_maps_eq {T : 𝒞} (hSub : Subterminator T) {X : 𝒞} (g h : X ⟶ T) :
    g = h := hSub g h (term_uniq _ _)

/-- The canonical 2-column table `(T; a, b)` over feet `[A, B]`. -/
def pairTable {T A B : 𝒞} (hSub : Subterminator T) (a : T ⟶ A) (b : T ⟶ B) : Table 𝒞 :=
  { src   := T
    len   := 2
    codom := fun i => if i.val = 0 then A else B
    col   := fun i => if h : i.val = 0 then ((if_pos h).symm ▸ a)
                      else ((if_neg h).symm ▸ b)
    monic := by intro X g h _hAg; exact subterminator_maps_eq hSub g h }

@[simp] theorem pairTable_codom_zero {T A B : 𝒞} (hSub : Subterminator T)
    (a : T ⟶ A) (b : T ⟶ B) (i : Fin 2) (hi : i.val = 0) :
    (pairTable hSub a b).codom i = A := by simp [pairTable, hi]

@[simp] theorem pairTable_codom_one {T A B : 𝒞} (hSub : Subterminator T)
    (a : T ⟶ A) (b : T ⟶ B) (i : Fin 2) (hi : i.val = 1) :
    (pairTable hSub a b).codom i = B := by simp [pairTable, hi]

theorem pairTable_col_zero {T A B : 𝒞} (hSub : Subterminator T)
    (a : T ⟶ A) (b : T ⟶ B) (i : Fin 2) (hi : i.val = 0) :
    HEq ((pairTable hSub a b).col i) a := by
  simp only [pairTable]; rw [dif_pos hi]; exact eqRec_heq _ a

theorem pairTable_col_one {T A B : 𝒞} (hSub : Subterminator T)
    (a : T ⟶ A) (b : T ⟶ B) (i : Fin 2) (hi : i.val = 1) :
    HEq ((pairTable hSub a b).col i) b := by
  simp only [pairTable]; rw [dif_neg (by rw [hi]; decide)]; exact eqRec_heq _ b

/-- §1.496: For a subterminator `T`, ANY two-column table `(T; a, b)` over feet `[A, B]`
    is in τ.  Reason: `(T; a) ∈ τ` (subterminator_one_col_mem); expand by `b`. -/
theorem subterminator_pair_mem (τ : TCat 𝒞) {T A B : 𝒞} (hSub : Subterminator T)
    (a : T ⟶ A) (b : T ⟶ B) : τ.mem (pairTable hSub a b) := by
  -- single-column table (T; a) ∈ τ
  have hOne := subterminator_one_col_mem τ hSub a
  let one1 : Table 𝒞 :=
    { src := T, len := 1, codom := fun _ => A, col := fun _ => a,
      monic := by intro X g h _hAg; exact subterminator_maps_eq hSub g h }
  -- expand by column b
  refine mem_expansion τ one1 hOne B b (pairTable hSub a b) rfl rfl ?_ ?_ ?_ ?_
  · -- hCodEq: pairTable.codom (cast ▸ castSucc i) = A  (the index has val 0)
    intro i
    have hiv : i.val = 0 := by have h : i.val < 1 := i.isLt; omega
    change (pairTable hSub a b).codom _ = A
    simp only [pairTable, fin_cast_val, Fin.val_castSucc, hiv, if_pos]
  · -- hCodLast: pairTable.codom (cast ▸ last 1) = B  (val 1)
    change (pairTable hSub a b).codom _ = B
    have hval : (Fin.last one1.len).val = 1 := rfl
    simp only [pairTable, fin_cast_val, hval, if_neg (by omega : ¬ (1:Nat) = 0)]
  · -- hCols: HEq (pairTable.col (cast ▸ castSucc i)) (cast ▸ one1.col i)
    intro i
    have hiv : i.val = 0 := by have h : i.val < 1 := i.isLt; omega
    -- the index has value 0 ⇒ dif_pos branch ⇒ a; one1.col i = a; RHS cast over src=src.
    simp only [pairTable]
    have hval : ((rfl : (2:Nat) = 2) ▸ Fin.castSucc i : Fin 2).val = 0 := by
      simp [Fin.val_castSucc, hiv]
    rw [dif_pos hval]
    exact (eqRec_heq _ a).trans (heq_of_eq rfl).symm
  · -- hLast: HEq (pairTable.col (cast ▸ last 1)) b
    simp only [pairTable]
    have hval : ¬ ((rfl : (2:Nat) = 2) ▸ Fin.last one1.len : Fin 2).val = 0 := by
      show ¬ (1:Nat) = 0; omega
    rw [dif_neg hval]

/-- A subterminator transported along an iso is a subterminator. -/
theorem subterminator_of_iso {T T' : 𝒞} (hSub : Subterminator T)
    {f : T ⟶ T'} (hIso : IsIso f) : Subterminator T' := by
  obtain ⟨finv, _hfg, hgf⟩ := hIso
  intro X g h _hAg
  -- g ≫ finv and h ≫ finv are maps into T, hence equal; compose with f back.
  have h0 : g ≫ finv = h ≫ finv := subterminator_maps_eq hSub _ _
  calc g = g ≫ (finv ≫ f) := by rw [hgf, Cat.comp_id]
    _ = (g ≫ finv) ≫ f := (Cat.assoc _ _ _).symm
    _ = (h ≫ finv) ≫ f := by rw [h0]
    _ = h ≫ (finv ≫ f) := Cat.assoc _ _ _
    _ = h := by rw [hgf, Cat.comp_id]

/-- §1.496: If T is a subterminator and f : T → T' is an isomorphism, then f = id_T
    (hence T' = T and f is the identity).

    Proof: let `g = f⁻¹`.  Build the 2-column τ-tables  P = (T; id_T, f)  and
    Q = (T'; g, id_T'),  both over feet `[T, T']` and both in τ (subterminator_pair_mem;
    T' is a subterminator by `subterminator_of_iso`).  The iso `f : T → T'` is a `TableIso
    P ≅ Q` (its column equations are exactly `f ≫ g = id_T` and `f ≫ id_T' = f`).
    τ1-uniqueness forces `P = Q`, hence `T = P.src = Q.src = T'`.  Finally with `T' = T`,
    both `h ▸ f` and `id_T` are maps `T → T`, equal because `T` is a subterminator. -/
theorem subterminator_iso_is_id (τ : TCat 𝒞) {T T' : 𝒞} (hSub : Subterminator T)
    (f : T ⟶ T') (hIso : IsIso f) : T' = T ∧ ∃ h : T' = T, h ▸ f = Cat.id T := by
  obtain ⟨g, hfg, hgf⟩ := hIso
  -- T' is also a subterminator.
  have hSub' : Subterminator T' := subterminator_of_iso hSub ⟨g, hfg, hgf⟩
  -- The two τ-tables over feet [T, T'].
  let P := pairTable hSub (Cat.id T) f
  let Q := pairTable hSub' g (Cat.id T')
  have hmemP : τ.mem P := subterminator_pair_mem τ hSub (Cat.id T) f
  have hmemQ : τ.mem Q := subterminator_pair_mem τ hSub' g (Cat.id T')
  -- f is a TableIso P ≅ Q.
  have hIsoPQ : Nonempty (TableIso P Q) := by
    refine ⟨{
      hLen        := rfl
      f           := f
      g           := g
      f_g         := hfg
      g_f         := hgf
      codom_match := fun i => ?_
      col_match   := fun i => ?_
    }⟩
    · -- Q.codom (rfl ▸ i) = P.codom i  (both [T, T'])
      show Q.codom i = P.codom i
      by_cases hi : i.val = 0
      · rw [pairTable_codom_zero hSub' g (Cat.id T') i hi,
          pairTable_codom_zero hSub (Cat.id T) f i hi]
      · have hi1 : i.val = 1 := by have h2 : i.val < 2 := i.isLt; omega
        rw [pairTable_codom_one hSub' g (Cat.id T') i hi1,
          pairTable_codom_one hSub (Cat.id T) f i hi1]
    · -- HEq (f ≫ Q.col (rfl ▸ i)) (P.col i)
      show HEq (f ≫ Q.col i) (P.col i)
      by_cases hi : i.val = 0
      · -- col 0:  f ≫ g = id_T = P.col 0
        have hQcol : HEq (Q.col i) g := pairTable_col_zero hSub' g (Cat.id T') i hi
        have hPcol : HEq (P.col i) (Cat.id T) := pairTable_col_zero hSub (Cat.id T) f i hi
        refine HEq.trans (comp_heq_left f _ g
          (pairTable_codom_zero hSub' g (Cat.id T') i hi) hQcol) ?_
        rw [hfg]; exact hPcol.symm
      · -- col 1:  f ≫ id_T' = f = P.col 1
        have hi1 : i.val = 1 := by
          have h2 : i.val < 2 := by have := i.isLt; simpa [P, pairTable] using this
          omega
        have hQcol : HEq (Q.col i) (Cat.id T') := pairTable_col_one hSub' g (Cat.id T') i hi1
        have hPcol : HEq (P.col i) f := pairTable_col_one hSub (Cat.id T) f i hi1
        refine HEq.trans (comp_heq_left f _ (Cat.id T')
          (pairTable_codom_one hSub' g (Cat.id T') i hi1) hQcol) ?_
        rw [Cat.comp_id]; exact hPcol.symm
  -- τ1-uniqueness: P = Q.
  have hPQ : P = Q := τ.tau1_unique P P Q hmemP hmemQ ⟨TableIso.refl P⟩ hIsoPQ
  -- T = T' from the sources.
  have hTT' : T = T' := by
    have := congrArg Table.src hPQ
    simpa [P, Q, pairTable] using this
  refine ⟨hTT'.symm, hTT'.symm, ?_⟩
  -- hTT'.symm ▸ f : T → T;  equal to id_T since T is a subterminator.
  subst hTT'
  exact subterminator_maps_eq hSub _ _

/-- §1.496: Isomorphic subterminators are equal. -/
theorem subterminator_iso_unique (τ : TCat 𝒞) {T T' : 𝒞}
    (hT : Subterminator T) (_hT' : Subterminator T')
    (f : T ⟶ T') (hIso : IsIso f) : T = T' :=
  ((subterminator_iso_is_id τ hT f hIso).1).symm

/-- `one` is a subterminator: `term one` is an identity (by `term_uniq`), hence monic. -/
theorem subterminator_one : Subterminator (@one 𝒞 _ _) := by
  intro X g h _hAg; exact term_uniq g h

/-- §1.496 ("there is a unique terminator"): a TERMINATOR — a subterminator `T` whose map
    `term T : T → one` is an isomorphism (equivalently, an object that is itself terminal) —
    is `one`.

    NOTE.  This is the book's actual claim.  It is NOT true that *every* subterminator is
    terminal (e.g. the empty set is a subterminator in `Set`, a τ-category, but is not the
    terminator): so the hypothesis `IsIso (term T)` — i.e. `T` is genuinely a terminator —
    is essential.  The proof is `subterminator_iso_unique` applied to the iso `term T`. -/
theorem terminator_eq_one (τ : TCat 𝒞) {T : 𝒞} (hSub : Subterminator T)
    (hIso : IsIso (term T)) : T = @one 𝒞 _ _ :=
  subterminator_iso_unique τ hSub subterminator_one (term T) hIso

end TCat

/-! ## §1.497 The Cancellation Lemma -/

namespace TCat

/-- §1.497 CANCELLATION LEMMA: If `S ; T ∈ τ` and `T ∈ τ` then `S ∈ τ`.
    Here `S ; T` is `S.comp T j h_eq` (table composition replacing column j of S with T).

    Book proof: Let g : T'' → top(S) be the resurfacing of S. By τ2.2,
    the composition (T''; gx₁,…,gxₙ) ; (T'; y₁,…,yₘ) ∈ τ, so g is also the resurfacing
    of `S ; T`. Since `S ; T ∈ τ` by assumption, its resurfacing is the identity,
    hence g = id, so S ∈ τ.

    Mechanically: the iso between S.comp and r.rep.comp (built from r.iso) gives
    tau1_unique → comp equality → r.rep.src = S.src → r.iso.f = id (by S.monic)
    → r.rep = S → τ.mem S.
    The index/HEq bookkeeping for compColMor makes this proof mechanically heavy. -/
theorem cancellationLemma (τ : TCat 𝒞) (S T : Table 𝒞) (j : Fin S.len)
    (h_eq : T.src = S.codom j)
    (hST : τ.mem (S.comp T j h_eq)) (hT : τ.mem T) : τ.mem S := by
  let r := τ.resurfacing S
  let j' : Fin r.rep.len := r.iso.hLen ▸ j
  have hj'val : j'.val = j.val := fin_cast_val r.iso.hLen j
  -- h'_eq: T.src = r.rep.codom j'
  have h'_eq : T.src = r.rep.codom j' := h_eq.trans (r.iso.codom_match j).symm
  -- Step 4: r.rep.comp T j' h'_eq ∈ τ
  have hRepComp : τ.mem (r.rep.comp T j' h'_eq) := τ.tau2_comp r.rep T j' h'_eq r.mem hT
  -- Step 5: Build TableIso (S.comp T j h_eq) (r.rep.comp T j' h'_eq)
  -- Use hSlen : S.len = r.rep.len so comp lengths equal
  have hSlen : S.len = r.rep.len := r.iso.hLen
  have hCompIso : Nonempty (TableIso (S.comp T j h_eq) (r.rep.comp T j' h'_eq)) := by
    -- S.comp and r.rep.comp have the same .len (both S.len - 1 + T.len = r.rep.len - 1 + T.len)
    have hLen_field : (S.comp T j h_eq).len = (r.rep.comp T j' h'_eq).len := by
      simp only [Table.comp]; omega
    -- Helper: cast a Fin (S.len-1+T.len) to Fin (r.rep.len-1+T.len) and back preserves value
    have hCompLen : S.len - 1 + T.len = r.rep.len - 1 + T.len := by omega
    -- Work with k₀ : Fin (S.len - 1 + T.len) exposed definitionally
    refine ⟨{
      hLen        := hLen_field
      f           := r.iso.f
      g           := r.iso.g
      f_g         := r.iso.f_g
      g_f         := r.iso.g_f
      codom_match := fun (k : Fin (S.comp T j h_eq).len) => ?_
      col_match   := fun (k : Fin (S.comp T j h_eq).len) => ?_
    }⟩
    · -- Goal: (r.rep.comp T j' h'_eq).codom (hLen_field ▸ k) = (S.comp T j h_eq).codom k
      simp only [Table.comp, Table.compCodom]
      -- hkv: the cast preserves value (hLen_field : .len = .len)
      have hkv : (hLen_field ▸ k : Fin (r.rep.comp T j' h'_eq).len).val = k.val :=
        fin_cast_val hLen_field k
      by_cases h1 : k.val < j.val
      · have h1' : (hLen_field ▸ k).val < j'.val := by rw [hkv, hj'val]; exact h1
        simp only [h1, dite_true, h1', dite_true]
        refine Eq.trans ?_ (r.iso.codom_match ⟨k.val, by omega⟩)
        congr 1; exact Fin.ext (by simp only [fin_cast_val])
      · by_cases h2 : k.val < j.val + T.len
        · have h1' : ¬ (hLen_field ▸ k).val < j'.val := by rw [hkv, hj'val]; exact h1
          have h2' : (hLen_field ▸ k).val < j'.val + T.len := by rw [hkv, hj'val]; exact h2
          simp only [h1, dite_false, h2, dite_true, h1', dite_false, h2', dite_true]
          congr 1; apply Fin.ext; simp [hkv, hj'val]
        · have h1' : ¬ (hLen_field ▸ k).val < j'.val := by rw [hkv, hj'val]; exact h1
          have h2' : ¬ (hLen_field ▸ k).val < j'.val + T.len := by rw [hkv, hj'val]; exact h2
          simp only [h1, dite_false, h2, dite_false, h1', dite_false, h2', dite_false]
          have hkLt : k.val < S.len - 1 + T.len := by have := k.isLt; simpa [Table.comp] using this
          refine Eq.trans ?_ (r.iso.codom_match ⟨k.val - T.len + 1, by omega⟩)
          congr 1; exact Fin.ext (by simp only [fin_cast_val, hkv])
    · -- Goal: HEq (r.iso.f ≫ (r.rep.comp T j' h'_eq).col (hLen_field ▸ k)) ((S.comp T j h_eq).col k)
      simp only [Table.comp]
      have hkv : (hLen_field ▸ k : Fin (r.rep.comp T j' h'_eq).len).val = k.val :=
        fin_cast_val hLen_field k
      have hkLt : k.val < S.len - 1 + T.len := by have := k.isLt; simpa [Table.comp] using this
      have hkLtR : (hLen_field ▸ k : Fin (r.rep.comp T j' h'_eq).len).val < r.rep.len - 1 + T.len := by
        rw [hkv]; rw [← hSlen]; exact hkLt
      -- After simp [Table.comp], goals are about compColMor directly
      show HEq (r.iso.f ≫ Table.compColMor r.rep T j' h'_eq
                 (hLen_field ▸ k : Fin (r.rep.comp T j' h'_eq).len))
               (Table.compColMor S T j h_eq k)
      unfold Table.compColMor
      by_cases h1 : k.val < j.val
      · -- S-left branch: after simp, both sides are eC ▸ S/r.rep.col ⟨k,_⟩
        have h1' : (hLen_field ▸ k).val < j'.val := by rw [hkv, hj'val]; exact h1
        simp only [h1, dite_true, h1', dite_true]
        have hcm := r.iso.col_match (⟨k.val, by omega⟩ : Fin S.len)
        -- hcm : HEq (r.iso.f ≫ r.rep.col (hSlen ▸ ⟨k.val,_⟩)) (S.col ⟨k.val,_⟩)
        -- Strip the eR cast on the LHS r.rep column (via comp_heq_left + eqRec_heq),
        -- bridge the index to (hSlen ▸ ⟨k,_⟩) and use hcm; strip the eS cast on the RHS.
        refine (comp_heq_left r.iso.f _ _ ?_ (eqRec_heq _ _)).trans (HEq.trans ?_
          (hcm.trans (eqRec_heq _ _).symm))
        · -- codom equality eR.symm : r.rep.compCodom T j' (hLen▸k) = r.rep.codom ⟨↑(hLen▸k),_⟩
          simp only [Table.compCodom, h1', dite_true]
        · -- index bridge: r.iso.f ≫ r.rep.col ⟨↑(hLen▸k),_⟩ ≍ r.iso.f ≫ r.rep.col (hSlen ▸ ⟨k,_⟩)
          exact comp_heq_left r.iso.f _ _
            (congrArg r.rep.codom (Fin.ext (by simp only [fin_cast_val])))
            (Table.col_heq_of_eq rfl (fin_heq rfl _ _ (by simp only [fin_cast_val])))
      · by_cases h2 : k.val < j.val + T.len
        · -- T-middle branch
          have h1' : ¬ (hLen_field ▸ k).val < j'.val := by rw [hkv, hj'val]; exact h1
          have h2' : (hLen_field ▸ k).val < j'.val + T.len := by rw [hkv, hj'val]; exact h2
          simp only [h1, dite_false, h2, dite_true, h1', dite_false, h2', dite_true]
          have hcm_j := r.iso.col_match j
          have hidx_eq : (hLen_field ▸ k).val - j'.val = k.val - j.val := by omega
          have hidx_r : (⟨(hLen_field ▸ k).val - j'.val, by
              have := (hLen_field ▸ k).isLt; omega⟩ : Fin T.len)
              = ⟨k.val - j.val, by omega⟩ := Fin.ext hidx_eq
          have eC_S : T.codom ⟨k.val - j.val, by omega⟩ = S.compCodom T j k := by
            simp [Table.compCodom, h1, h2]
          have eC_R : T.codom ⟨(hLen_field ▸ k).val - j'.val, by have := (hLen_field ▸ k).isLt; omega⟩
              = r.rep.compCodom T j' (hLen_field ▸ k : Fin (r.rep.comp T j' h'_eq).len) := by
            simp [Table.compCodom, h1', h2']
          -- Strip the outer compCodom casts eC_R / eC_S, then cases on h_eq/h'_eq.
          refine (comp_heq_left r.iso.f _ _ eC_R.symm (eqRec_heq _ _)).trans
            (HEq.trans ?_ (eqRec_heq eC_S
              (S.col j ≫ (h_eq ▸ T.col ⟨k.val - j.val, by omega⟩ : S.codom j ⟶ _))).symm)
          -- Core: r.iso.f ≫ (r.rep.col j' ≫ (h'_eq ▸ T.col iR)) ≍ S.col j ≫ (h_eq ▸ T.col iS)
          refine HEq.trans (heq_of_eq (Cat.assoc r.iso.f (r.rep.col j') _).symm) ?_
          -- (r.iso.f ≫ r.rep.col j') ≫ (h'_eq ▸ T.col iR) ≍ S.col j ≫ (h_eq ▸ T.col iS)
          -- hg: h'_eq ▸ T.col iR ≍ h_eq ▸ T.col iS, via stripping ▸ and the index equality.
          have hg : HEq (castDom h'_eq (T.col ⟨(hLen_field ▸ k).val - j'.val, by
                have := (hLen_field ▸ k).isLt; omega⟩) : r.rep.codom j' ⟶ _)
              (castDom h_eq (T.col ⟨k.val - j.val, by omega⟩) : S.codom j ⟶ _) :=
            (castDom_heq h'_eq _).trans
              ((Table.col_heq_of_eq (rfl : T = T)
                  (fin_heq rfl
                    (⟨(hLen_field ▸ k).val - j'.val, by have := (hLen_field ▸ k).isLt; omega⟩ : Fin T.len)
                    ⟨k.val - j.val, by omega⟩ hidx_eq)).trans
                (castDom_heq h_eq _).symm)
          exact comp_heq (r.iso.f ≫ r.rep.col j') (S.col j) _ _
            rfl (r.iso.codom_match j) (congrArg T.codom (Fin.ext hidx_eq)) hcm_j hg
        · -- S-right branch
          have h1' : ¬ (hLen_field ▸ k).val < j'.val := by rw [hkv, hj'val]; exact h1
          have h2' : ¬ (hLen_field ▸ k).val < j'.val + T.len := by rw [hkv, hj'val]; exact h2
          simp only [h1, dite_false, h2, dite_false, h1', dite_false, h2', dite_false]
          have hcm := r.iso.col_match (⟨k.val - T.len + 1, by omega⟩ : Fin S.len)
          refine (comp_heq_left r.iso.f _ _ ?_ (eqRec_heq _ _)).trans (HEq.trans ?_
            (hcm.trans (eqRec_heq _ _).symm))
          · -- codom equality eR.symm
            simp only [Table.compCodom, h1', h2', dite_false]
          · -- index bridge: r.rep.col ⟨↑(hLen▸k)-T+1,_⟩ ≍ r.rep.col (hSlen ▸ ⟨k-T+1,_⟩)
            exact comp_heq_left r.iso.f _ _
              (congrArg r.rep.codom (Fin.ext (by simp only [fin_cast_val, hkv])))
              (Table.col_heq_of_eq rfl (fin_heq rfl _ _ (by simp only [fin_cast_val, hkv])))
  -- Step 6: tau1_unique gives hCompEq
  have hCompEq : r.rep.comp T j' h'_eq = S.comp T j h_eq :=
    τ.tau1_unique (S.comp T j h_eq) _ _ hRepComp hST hCompIso ⟨TableIso.refl _⟩
  -- Step 7: r.rep.src = S.src
  have hSrc : r.rep.src = S.src := congrArg (·.src) hCompEq
  -- Step 8: HEq r.iso.f (Cat.id S.src)
  -- Extract direct column equalities from hCompEq, then use S.monic.
  have hFf : HEq r.iso.f (Cat.id S.src) := by
    have hHEq : HEq (castCod hSrc r.iso.f) r.iso.f := castCod_heq hSrc r.iso.f
    -- hRepCol k: HEq (r.rep.col (hLen ▸ k)) (S.col k), derived from hCompEq column equalities.
    -- For k ≠ j: use S-branch of compColMor at the appropriate index.
    -- For k = j: use T.monic on T-branch columns.
    have hRepCol : ∀ k : Fin S.len, HEq (r.rep.col (r.iso.hLen ▸ k)) (S.col k) := fun k => by
      by_cases hkj : k.val < j.val
      · -- k < j: comp index ⟨k.val, _⟩, S-left branch
        have hci_lt : k.val < S.len - 1 + T.len := by omega
        have hci_ltR : k.val < r.rep.len - 1 + T.len := by rw [← hSlen]; exact hci_lt
        have hcol := Table.col_heq_of_eq hCompEq
          (i := ⟨k.val, by simp only [Table.comp]; exact hci_ltR⟩)
          (i' := ⟨k.val, by simp only [Table.comp]; exact hci_lt⟩)
          (fin_heq (by simp only [Table.comp]; rw [hSlen]) _ _ rfl)
        -- hcol : HEq ((r.rep.comp T j' h'_eq).col ⟨k,_⟩) ((S.comp T j h_eq).col ⟨k,_⟩)
        simp only [Table.comp, Table.compColMor, hkj, dite_true,
          show k.val < j'.val from by rw [hj'val]; exact hkj] at hcol
        -- hcol now: HEq (eR ▸ r.rep.col ⟨k,_⟩) (eS ▸ S.col ⟨k,_⟩)
        -- Align the column indices ⟨k.val,_⟩ with (hLen ▸ k) and k.
        have hIdxR : (r.iso.hLen ▸ k : Fin r.rep.len)
            = ⟨k.val, by have := k.isLt; omega⟩ := Fin.ext (by rw [fin_cast_val])
        have hIdxS : k = (⟨k.val, by have := k.isLt; omega⟩ : Fin S.len) := Fin.ext rfl
        rw [hIdxR, hIdxS]
        -- Strip both casts
        exact (eqRec_heq _ _).symm.trans (hcol.trans (eqRec_heq _ _))
      · by_cases hkj2 : j.val < k.val
        · -- k > j: comp index ⟨k.val + T.len - 1, _⟩, S-right branch
          have hone : 1 ≤ k.val := by omega
          have hci_lt : k.val + T.len - 1 < S.len - 1 + T.len := by omega
          have h1' : ¬ (k.val + T.len - 1 < j.val) := by omega
          have h2' : ¬ (k.val + T.len - 1 < j.val + T.len) := by omega
          have h1r : ¬ (k.val + T.len - 1 < j'.val) := by rw [hj'val]; exact h1'
          have h2r : ¬ (k.val + T.len - 1 < j'.val + T.len) := by rw [hj'val]; exact h2'
          have hci_ltR : k.val + T.len - 1 < r.rep.len - 1 + T.len := by rw [← hSlen]; exact hci_lt
          have hcol := Table.col_heq_of_eq hCompEq
            (i := ⟨k.val + T.len - 1, by simp only [Table.comp]; exact hci_ltR⟩)
            (i' := ⟨k.val + T.len - 1, by simp only [Table.comp]; exact hci_lt⟩)
            (fin_heq (by simp only [Table.comp]; rw [hSlen]) _ _ rfl)
          simp only [Table.comp, Table.compColMor, h1', dite_false, h2', dite_false,
            h1r, h2r] at hcol
          -- hcol: HEq (eR ▸ r.rep.col ⟨k+T-1-T+1,_⟩) (eS ▸ S.col ⟨k+T-1-T+1,_⟩)
          -- note: k+T-1-T+1 = k since 1 ≤ k
          have hIdx : k.val + T.len - 1 - T.len + 1 = k.val := by omega
          -- Strip the outer casts, giving bare columns at index ⟨k+T-1-T+1,_⟩.
          have hcol2 : HEq (r.rep.col ⟨k.val + T.len - 1 - T.len + 1, by have := k.isLt; omega⟩)
              (S.col ⟨k.val + T.len - 1 - T.len + 1, by have := k.isLt; omega⟩) :=
            (eqRec_heq _ _).symm.trans (hcol.trans (eqRec_heq _ _))
          -- Bridge the indices to (hLen ▸ k) and k via fin_heq + col_heq_of_eq.
          have hbR : HEq (r.iso.hLen ▸ k : Fin r.rep.len)
              (⟨k.val + T.len - 1 - T.len + 1, by have := k.isLt; omega⟩ : Fin r.rep.len) :=
            fin_heq rfl _ _ (by rw [fin_cast_val]; exact hIdx.symm)
          have hbS : HEq (⟨k.val + T.len - 1 - T.len + 1, by have := k.isLt; omega⟩ : Fin S.len) k :=
            fin_heq rfl _ _ hIdx
          exact (Table.col_heq_of_eq (rfl : r.rep = r.rep) hbR).trans
            (hcol2.trans (Table.col_heq_of_eq (rfl : S = S) hbS))
        · -- k = j: use T.monic on the T-branch columns of hCompEq.
          have hkj_eq : k = j := Fin.ext (Nat.le_antisymm (Nat.le_of_not_lt hkj2) (Nat.le_of_not_lt hkj))
          subst hkj_eq
          -- Now the outer parameter is `k` (j eliminated); j' = r.iso.hLen ▸ k.
          -- Goal: HEq (r.rep.col j') (S.col k).
          -- Build homogeneous maps into T.src and use T.monic.
          let fL : r.rep.src ⟶ T.src := castCod h'_eq.symm (r.rep.col j')
          let fR : r.rep.src ⟶ T.src := castDom hSrc.symm (castCod h_eq.symm (S.col k))
          have hfL : fL = castCod h'_eq.symm (r.rep.col j') := rfl
          have hfR : fR = castDom hSrc.symm (castCod h_eq.symm (S.col k)) := rfl
          have hmonic : fL = fR := by
            apply T.monic
            intro t
            -- Extract the T-middle branch of hCompEq at index j+t.
            have h1_mid : ¬ (k.val + t.val < k.val) := by omega
            have h2_mid : k.val + t.val < k.val + T.len := by have := t.isLt; omega
            have h1r_mid : ¬ (k.val + t.val < j'.val) := by rw [hj'val]; exact h1_mid
            have h2r_mid : k.val + t.val < j'.val + T.len := by rw [hj'val]; exact h2_mid
            have hci_lt : k.val + t.val < S.len - 1 + T.len := by
              have := t.isLt; have := k.isLt; omega
            have hci_ltR : k.val + t.val < r.rep.len - 1 + T.len := by
              have := t.isLt; have := k.isLt; rw [← hSlen]; omega
            have hLenEq : (r.rep.comp T j' h'_eq).len = (S.comp T k h_eq).len := by
              simp only [Table.comp]; rw [hSlen]
            have hiiHEq : HEq (⟨k.val + t.val, by simp [Table.comp, hci_ltR]⟩ :
                Fin (r.rep.comp T j' h'_eq).len)
                (⟨k.val + t.val, by simp [Table.comp, hci_lt]⟩ :
                Fin (S.comp T k h_eq).len) :=
              fin_heq hLenEq _ _ rfl
            have hcol := Table.col_heq_of_eq hCompEq
              (i := ⟨k.val + t.val, by simp [Table.comp, hci_ltR]⟩)
              (i' := ⟨k.val + t.val, by simp [Table.comp, hci_lt]⟩) hiiHEq
            simp only [Table.comp, Table.compColMor, h1_mid, dite_false, h2_mid, dite_true,
              h1r_mid, dite_false, h2r_mid, dite_true] at hcol
            -- hcol : HEq (eR ▸ (r.rep.col j' ≫ h'_eq ▸ T.col ⟨k+t-j',_⟩))
            --             (eS ▸ (S.col k   ≫ h_eq  ▸ T.col ⟨k+t-k,_⟩))
            -- Strip the outer compCodom casts.  Keep the native shifted indices.
            have hcol2 : HEq (r.rep.col j' ≫ (h'_eq ▸ T.col ⟨k.val + t.val - j'.val, by
                  have := t.isLt; have := hj'val; omega⟩ :
                  r.rep.codom j' ⟶ _))
                (S.col k ≫ (h_eq ▸ T.col ⟨k.val + t.val - k.val, by have := t.isLt; omega⟩ :
                  S.codom k ⟶ _)) :=
              (eqRec_heq _ _).symm.trans (hcol.trans (eqRec_heq _ _))
            -- The two shifted column indices both equal t.
            let iR : Fin T.len := ⟨k.val + t.val - j'.val, by have := t.isLt; have := hj'val; omega⟩
            let iS : Fin T.len := ⟨k.val + t.val - k.val, by have := t.isLt; omega⟩
            have hidxR : iR = t :=
              Fin.ext (show k.val + t.val - j'.val = t.val by rw [hj'val]; have := t.isLt; omega)
            have hidxS : iS = t :=
              Fin.ext (show k.val + t.val - k.val = t.val by have := t.isLt; omega)
            -- g-side HEqs: T.col t ≍ h_eq ▸ T.col (shifted index), by stripping ▸ and congrArg.
            have hgL : HEq (T.col t) (castDom h'_eq (T.col iR) : r.rep.codom j' ⟶ _) :=
              (Table.col_heq_of_eq (rfl : T = T)
                (fin_heq rfl t iR (by rw [hidxR]))).trans (castDom_heq h'_eq (T.col iR)).symm
            have hL : HEq (fL ≫ T.col t)
                (r.rep.col j' ≫ (h'_eq ▸ T.col iR : r.rep.codom j' ⟶ _)) :=
              comp_heq fL (r.rep.col j') (T.col t) _ rfl h'_eq
                (congrArg T.codom hidxR.symm)
                (hfL ▸ castCod_heq h'_eq.symm (r.rep.col j')) hgL
            have hgR : HEq (T.col t) (castDom h_eq (T.col iS) : S.codom k ⟶ _) :=
              (Table.col_heq_of_eq (rfl : T = T)
                (fin_heq rfl t iS (by rw [hidxS]))).trans (castDom_heq h_eq (T.col iS)).symm
            have hR : HEq (fR ≫ T.col t)
                (S.col k ≫ (h_eq ▸ T.col iS : S.codom k ⟶ _)) :=
              comp_heq fR (S.col k) (T.col t) _ hSrc h_eq
                (congrArg T.codom hidxS.symm)
                (hfR ▸ (castDom_heq hSrc.symm (castCod h_eq.symm (S.col k))).trans
                  (castCod_heq h_eq.symm (S.col k))) hgR
            -- hcol2 with native indices iR, iS.
            have hcol2' : HEq (r.rep.col j' ≫ (h'_eq ▸ T.col iR : r.rep.codom j' ⟶ _))
                (S.col k ≫ (h_eq ▸ T.col iS : S.codom k ⟶ _)) := hcol2
            exact eq_of_heq (hL.trans (hcol2'.trans hR.symm))
          -- From fL = fR strip casts back to the heterogeneous column equality.
          have hLR : HEq (r.rep.col j') (S.col k) := by
            have e1 : HEq fL (r.rep.col j') := hfL ▸ castCod_heq h'_eq.symm (r.rep.col j')
            have e2 : HEq fR (S.col k) :=
              hfR ▸ (castDom_heq hSrc.symm (castCod h_eq.symm (S.col k))).trans
                (castCod_heq h_eq.symm (S.col k))
            exact e1.symm.trans ((heq_of_eq hmonic).trans e2)
          exact hLR
    -- Now prove hAgreeCol from hRepCol
    have hAgreeCol : ∀ k : Fin S.len,
        castCod hSrc r.iso.f ≫ S.col k = S.col k := fun k => by
      apply eq_of_heq
      have hcm := r.iso.col_match k
      have hcodi : S.codom k = r.rep.codom (r.iso.hLen ▸ k) := (r.iso.codom_match k).symm
      refine HEq.trans ?_ hcm
      exact comp_heq (castCod hSrc r.iso.f) r.iso.f (S.col k)
        (r.rep.col (r.iso.hLen ▸ k)) rfl hSrc.symm hcodi hHEq (hRepCol k).symm
    exact (castCod_heq hSrc r.iso.f).symm.trans
      (heq_of_eq (S.monic _ _ (fun k => by rw [Cat.id_comp]; exact hAgreeCol k)))
  -- Step 9: r.rep = S
  have hidx_rt : ∀ k : Fin r.rep.len,
      (r.iso.hLen ▸ (r.iso.hLen.symm ▸ k : Fin S.len) : Fin r.rep.len) = k := fun k => by
    apply Fin.ext; rw [fin_cast_val, fin_cast_val]
  have hCodPt : ∀ k : Fin r.rep.len, r.rep.codom k = S.codom (r.iso.hLen.symm ▸ k) := by
    intro k; have hc := r.iso.codom_match (r.iso.hLen.symm ▸ k); rw [hidx_rt k] at hc; exact hc
  have hrep_eq : r.rep = S := by
    apply Table_eq_of_fields r.rep S hSrc r.iso.hLen.symm
    · exact heq_funext_fin r.iso.hLen.symm r.rep.codom S.codom hCodPt
    · refine Table.col_heq_funext hSrc r.iso.hLen.symm hCodPt (fun k => ?_)
      have hcm := r.iso.col_match (r.iso.hLen.symm ▸ k)
      rw [hidx_rt k] at hcm
      refine HEq.trans ?_ hcm
      have hidHEq : HEq (Cat.id r.rep.src) r.iso.f :=
        HEq.trans (by rw [hSrc]) hFf.symm
      exact (heq_of_eq (Cat.id_comp (r.rep.col k))).symm.trans
        (comp_heq (Cat.id r.rep.src) r.iso.f (r.rep.col k) (r.rep.col k)
          hSrc rfl rfl hidHEq HEq.rfl)
  exact hrep_eq ▸ r.mem

end TCat

/-! ## §1.498  Canonical Cartesian structure in a τ-category -/

-- BOOK §1.498: A τ-category has a CANONICAL CARTESIAN STRUCTURE.
-- The canonical product ⟨A × B; p₁, p₂⟩ is defined as the unique τ-table
-- on the pair (A, B).  The canonical pullback is likewise the unique τ-table
-- on the pair of projections.

/-! ## §1.49(10)  Lemmas for τ-categories -/

-- BOOK §1.49(10): Canonical products are strictly associative:
--   (A × B) × C = A × (B × C) with the canonical projections.
-- The terminator is strictly a two-sided unit: 1 × A = A = A × 1
-- (not just up to isomorphism: the canonical projections ARE identities).
-- If each square in a stacked pullback diagram is a canonical pullback,
-- then so is the rectangle.

/-! ## §1.4(10)1  Free τ-category -/

-- BOOK §1.4(10)1: For every small Cartesian category A there exists a free
-- τ-category A → A^τ where A → A^τ is an equivalence functor.
-- (The equivalence-kernel of the functor consists of identity maps and
-- isomorphisms between subterminators.)

/-! ## §1.4(11)5  Generic point generates A/B -/

-- BOOK §1.4(11)5: Every object and morphism in A/B is obtainable by taking
-- canonical pullbacks of the generic point ε : 1 → ΔB and morphisms of the
-- form Δx (for morphisms x in A).

/-! ## §1.4(11)6  Unique τ-functor from a point -/

-- BOOK §1.4(11)6: For any τ-functor F : A → B and point x : 1 → F(B),
-- there exists a unique τ-functor F_x : A/B → B such that Δ ; F_x = F and
-- F_x(ε) = x (where ε is the generic point of A/B).

/-! ## §1.4(11)9  Universal property rephrased via Γ -/

-- BOOK §1.4(11)9: Given any τ-functor F : A → B and transformation
-- η : T(Δ(-)) → T(F(-)) (where T = (1, -) is the global-sections functor),
-- there exists a unique τ-functor G : A/B → B such that γ_G = η.

/-! ## §1.4(12)1  Metatheorem for τ-categories -/

-- BOOK §1.4(12)1 METATHEOREM: An equation between terms (built from canonical
-- products, equalizers, pullbacks, resurfacing, and the terminator) is true
-- for all τ-categories if and only if it is true for P (the τ-category of
-- von Neumann ordinals less than ω^ω).

/-! ## §1.4(12)2  Key lemma for the metatheorem -/

-- BOOK §1.4(12)2: If A is countable, then for any morphism f ∉ |A^τ| there
-- exists an ω-ordering of A and an object B ∈ A such that (B, f) ∉ |P|.
-- (This is the inductive step used to embed the free τ-category of a
-- countable Cartesian category into P.)

end Freyd
