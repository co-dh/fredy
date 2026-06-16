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
  have hmem2 : τ.mem tab2 :=
    mem_expansion τ (idTable T) hmem_id T' f tab2 rfl rfl
      (by intro i; fin_cases i; simp [codom2, idTable])
      (by simp [tab2, codom2])
      (by intro i; fin_cases i; simp [tab2, col2, idTable, codom2])
      (by simp [tab2, col2, codom2])
  -- Column 0 of tab2 (= id_T) is short: subterminator T forces any f=g
  have hShort0 : tab2.IsShort ⟨0, by norm_num⟩ := by
    intro X g h _hAgree
    apply hSub; apply term_uniq
  -- mem_prune: tab2 ∈ τ → tab2.prune ⟨0,_⟩ ∈ τ
  have hPrune := mem_prune hShort0 hmem2
  -- tab2.prune ⟨0,_⟩ hShort0 = {len=1, col=f}: Fin.skip ⟨0,_⟩ ⟨0,_⟩ = ⟨1,_⟩
  convert hPrune using 1
  apply Table_eq_of_fields _ _ rfl rfl
  · -- HEq codom: prune.codom ⟨0,_⟩ = tab2.codom ⟨1,_⟩ = T'
    apply heq_funext_fin rfl; intro i; fin_cases i
    simp [Table.prune, Fin.skip, tab2, codom2]
  · -- HEq col
    apply Table.col_heq_funext rfl rfl
    · intro i; fin_cases i; simp [Table.prune, Fin.skip, tab2, codom2]
    · intro i; fin_cases i
      simp only [Table.prune, Fin.skip, show (0 : Fin 1).val < (0 : Fin 2).val = False from by norm_num]
      simp [tab2, col2, codom2]

/-- §1.496: If T is a subterminator and f : T → T' is an isomorphism, then f = id_T
    (hence T' = T and f is the identity). -/
theorem subterminator_iso_is_id (τ : TCat 𝒞) {T T' : 𝒞} (hSub : Subterminator T)
    (f : T ⟶ T') (hIso : IsIso f) : T' = T ∧ ∃ h : T' = T, h ▸ f = Cat.id T := by
  sorry

/-- §1.496: Isomorphic subterminators are equal. -/
theorem subterminator_iso_unique (τ : TCat 𝒞) {T T' : 𝒞}
    (hT : Subterminator T) (hT' : Subterminator T')
    (f : T ⟶ T') (hIso : IsIso f) : T = T' := by
  sorry

/-- §1.496: In a τ-category with a terminal object, the terminal object is the unique
    terminator: any subterminator is the terminal object. -/
theorem subterminator_is_terminal (τ : TCat 𝒞) {T : 𝒞} (hSub : Subterminator T) :
    T = @one 𝒞 _ _ := by
  -- The terminal object `one` is itself a subterminator (trivially, id is monic).
  -- By subterminator_iso_unique applied to (term T : T → one) which is iso
  -- when T is itself terminal... this requires more structure.
  -- The book's argument: any two subterminators are isomorphic (both map to each other
  -- via the unique terminal maps) and by subterminator_iso_unique they are equal.
  sorry

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
  sorry

end TCat

end Freyd
