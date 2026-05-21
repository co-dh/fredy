/-
  Freyd & Scedrov, *Categories and Allegories* §1.49, §1.494.

  From the book (§1.49):

    A TABLE is an object T together with a finite jointly-monic family of
    morphisms x₁, …, xₙ : T → Aᵢ. Notation: ⟨T; x₁, …, xₙ⟩.

    xⱼ is a SHORT COLUMN if for every f, g : X → T with f xⱼ ≠ g xⱼ
    there exists i < j with f xᵢ ≠ g xᵢ. Equivalently (contrapositive):
    if f, g agree on x₁, …, xⱼ₋₁ then they agree on xⱼ.

    A τ-CATEGORY is a cartesian category with a class τ of tables such that:
      τ1. Every table is isomorphic to a unique table in τ.
      τ2.1. ⟨T; 1_T⟩ ∈ τ for all T.
      τ2.2. τ is closed under table composition.
      τ3. If ⟨T; x₁, …, xₙ⟩ ∈ τ and xⱼ is short, then ⟨T; x̂ⱼ⟩ ∈ τ.

    The RESURFACING of ⟨T; x₁, …, xₙ⟩ is the unique g : T' → T such that
    ⟨T'; gx₁, …, gxₙ⟩ ∈ τ. A table is in τ iff its resurfacing is the
    identity.

    Converse of τ3 (§1.494): If ⟨T; x₁, …, xₙ⟩ has short column xⱼ, then
      ⟨T; x₁, …, xₙ⟩ ∈ τ  ↔  ⟨T; x₁, …, x̂ⱼ, …, xₙ⟩ ∈ τ.

  Corrections vs freyd_tau.md (see PLAN.md for details):
    • Tables must be jointly monic (the transcription omitted this).
    • `prune` only produces a valid Table when the column is short.
    • `mem_iff_resurfacing_id` was ill-typed; we use `= self` instead.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.EqToHom

open CategoryTheory

universe v u

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-! ## Minimal Cat typeclass (replaces Mathlib.CategoryTheory in step 2) -/

/-- A category: objects, hom-sets, identity, composition, and the three axioms. -/
class Cat.{w, z} (𝒞 : Type z) : Type (max z (w + 1)) where
  Hom     : 𝒞 → 𝒞 → Type w
  id      : (X : 𝒞) → Hom X X
  comp    : {X Y Z : 𝒞} → Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y : 𝒞} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : 𝒞} (f : Hom X Y), comp f (id Y) = f
  assoc   : ∀ {W X Y Z : 𝒞} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
              comp (comp f g) h = comp f (comp g h)

namespace Cat

/-- An isomorphism in a Cat-category. -/
structure Iso [Cat.{w} 𝒞] (A B : 𝒞) : Type w where
  hom        : Hom A B
  inv        : Hom B A
  hom_inv_id : comp hom inv = id A
  inv_hom_id : comp inv hom = id B

def Iso.refl [Cat.{w} 𝒞] (A : 𝒞) : Iso A A where
  hom        := id A
  inv        := id A
  hom_inv_id := id_comp (id A)
  inv_hom_id := id_comp (id A)

end Cat

namespace Freyd

/-! ## Tables -/

/-- A table ⟨T; x₁, …, xₙ⟩: source object T, jointly-monic column family xᵢ : T → Aᵢ. -/
structure Table (𝒞 : Type u) [Category.{v} 𝒞] where
  T : 𝒞
  n : Nat
  codom : Fin n → 𝒞
  x : (i : Fin n) → T ⟶ codom i
  monic : ∀ ⦃X : 𝒞⦄ (f g : X ⟶ T), (∀ i, f ≫ x i = g ≫ x i) → f = g

namespace Table

variable (tab : Table 𝒞)

/-- xⱼ is SHORT: agreement on x₁,…,xⱼ₋₁ implies agreement on xⱼ. -/
def IsShort (j : Fin tab.n) : Prop :=
  ∀ ⦃X : 𝒞⦄ (f g : X ⟶ tab.T),
    (∀ i : Fin tab.n, i.val < j.val → f ≫ tab.x i = g ≫ tab.x i) →
    f ≫ tab.x j = g ≫ tab.x j

/-- Skip position j: embed Fin (n-1) into Fin n by stepping over j. -/
def skip (j : Fin tab.n) (i : Fin (tab.n - 1)) : Fin tab.n :=
  if h : i.val < j.val then ⟨i.val, by omega⟩
  else ⟨i.val + 1, by have := j.isLt; have := i.isLt; omega⟩

/-- Every m ≠ j is hit by `skip j`. -/
lemma skip_surj (j : Fin tab.n) (m : Fin tab.n) (hm : m ≠ j) :
    ∃ l : Fin (tab.n - 1), tab.skip j l = m := by
  rcases Nat.lt_or_gt_of_ne (fun h => hm (Fin.ext h)) with hlt | hgt
  · exact ⟨⟨m.val, by have := j.isLt; omega⟩, Fin.ext (by simp [skip, hlt])⟩
  · exact ⟨⟨m.val - 1, by have := m.isLt; omega⟩,
      Fin.ext (by simp [skip, show ¬ (m.val - 1 < j.val) from by omega]; omega)⟩

/-- Delete column xⱼ. Short-ness ensures the remaining family is monic. -/
def prune (j : Fin tab.n) (hj : tab.IsShort j) : Table 𝒞 where
  T     := tab.T
  n     := tab.n - 1
  codom := fun i => tab.codom (tab.skip j i)
  x     := fun i => tab.x (tab.skip j i)
  monic := by
    intro X f g hAgree
    apply tab.monic
    intro k
    by_cases hkj : k = j
    · subst hkj; apply hj; intro i hi
      obtain ⟨l, hl⟩ := tab.skip_surj j i (Fin.ne_of_lt hi)
      have h := hAgree l; rwa [hl] at h
    · obtain ⟨l, hl⟩ := tab.skip_surj j k hkj
      have h := hAgree l; rwa [hl] at h

/-- Table isomorphism: a source iso intertwining all columns.
    `hCol` uses `eqToHom` for the codom cast so simp/rw can manipulate it. -/
structure Iso (S T : Table 𝒞) : Type (max u v) where
  hLen   : S.n = T.n
  hCodom : ∀ i : Fin S.n, S.codom i = T.codom (hLen ▸ i)
  iso    : S.T ≅ T.T
  hCol   : ∀ i : Fin S.n,
    S.x i = iso.hom ≫ T.x (hLen ▸ i) ≫ eqToHom (hCodom i).symm

lemma x_at_eq {tab : Table 𝒞} {a b : Fin tab.n} (h : a = b) :
    tab.x a ≫ eqToHom (congrArg tab.codom h) = tab.x b := by subst h; simp

lemma x_cast {S T : Table 𝒞} (hST : S = T) (i : Fin S.n) :
    hST ▸ S.x i = T.x (hST ▸ i) := by subst hST; simp

lemma codom_cast {S T : Table 𝒞} (hST : S = T) (i : Fin S.n) :
    hST ▸ S.codom i = T.codom (hST ▸ i) := by subst hST; simp

def Iso.refl (S : Table 𝒞) : Iso S S where
  hLen   := rfl
  hCodom := fun _ => rfl
  iso    := CategoryTheory.Iso.refl S.T
  hCol   := fun _ => by simp

end Table

/-! ## τ-categories -/

/-- A τ-category (Freyd §1.491). -/
structure TCat (𝒞 : Type u) [Category.{v} 𝒞] where
  mem : Table 𝒞 → Prop
  tau1_exists : ∀ tab : Table 𝒞, ∃ T : Table 𝒞, mem T ∧ Nonempty (Table.Iso tab T)
  tau1_unique : ∀ (tab T₁ T₂ : Table 𝒞),
    mem T₁ → mem T₂ →
    Nonempty (Table.Iso tab T₁) → Nonempty (Table.Iso tab T₂) → T₁ = T₂
  tau2_id : ∀ T : 𝒞,
    mem ⟨T, 1, fun _ => T, fun _ => 𝟙 T, fun _ f g h => by simpa using h 0⟩
  tau2_comp : True
  tau3 : ∀ (tab : Table 𝒞) (j : Fin tab.n) (h : tab.IsShort j),
    mem tab → mem (tab.prune j h)

namespace TCat

variable (τ : TCat 𝒞)

structure Resurfacing (tab : Table 𝒞) : Type (max u v) where
  rep : Table 𝒞
  mem : τ.mem rep
  iso : Table.Iso tab rep

noncomputable def resurfacing (tab : Table 𝒞) : τ.Resurfacing tab :=
  let h := τ.tau1_exists tab
  { rep := Classical.choose h
    mem := (Classical.choose_spec h).1
    iso := Classical.choice (Classical.choose_spec h).2 }

theorem mem_iff_resurfacing_eq (tab : Table 𝒞) :
    τ.mem tab ↔ (τ.resurfacing tab).rep = tab := by
  constructor
  · intro hS
    exact τ.tau1_unique tab _ tab (τ.resurfacing tab).mem hS
      ⟨(τ.resurfacing tab).iso⟩ ⟨Table.Iso.refl tab⟩
  · intro h; exact h ▸ (τ.resurfacing tab).mem

/-! ## Converse of τ3 (§1.494) -/

-- Fin cast preserves .val.
private lemma cast_val {m n : Nat} (h : m = n) (i : Fin m) : (h ▸ i).val = i.val := by
  subst h; rfl

/-- IsShort transports along a table iso.
    Proof: translate f, g via e.iso.inv to S, apply hj, then translate back via eqToHom. -/
private theorem isShort_of_iso {S T : Table 𝒞} (e : Table.Iso S T)
    (j : Fin S.n) (hj : S.IsShort j) : T.IsShort (e.hLen ▸ j) := by
  intro X f g hAgree
  have cast_lt : ∀ i : Fin S.n, i.val < j.val → (e.hLen ▸ i).val < (e.hLen ▸ j).val :=
    fun i hi => by have := cast_val e.hLen i; have := cast_val e.hLen j; omega
  have inv_col : ∀ i : Fin S.n,
      e.iso.inv ≫ S.x i = T.x (e.hLen ▸ i) ≫ eqToHom (e.hCodom i).symm := fun i => by
    rw [e.hCol i, ← Category.assoc, e.iso.inv_hom_id, Category.id_comp]
  have key : (f ≫ e.iso.inv) ≫ S.x j = (g ≫ e.iso.inv) ≫ S.x j := by
    apply hj; intro i hi
    -- right-associate, substitute via inv_col, then left-associate (separate calls)
    simp only [Category.assoc]
    simp only [inv_col]
    simp only [← Category.assoc]
    exact congrArg (· ≫ eqToHom (e.hCodom i).symm) (hAgree (e.hLen ▸ i) (cast_lt i hi))
  -- Same sequence on the hypothesis.
  simp only [Category.assoc] at key
  simp only [inv_col] at key
  simp only [← Category.assoc] at key
  -- key: (f ≫ T.x (e.hLen ▸ j)) ≫ eqToHom (e.hCodom j).symm = (g ≫ ...) ≫ ...
  -- Cancel eqToHom by post-composing and using eqToHom_trans + proof_irrel.
  have hcancel := congrArg (· ≫ eqToHom (e.hCodom j)) key
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hcancel
  exact hcancel

private noncomputable def iso_prune {S T : Table 𝒞} (e : Table.Iso S T)
    (j : Fin S.n) (hjS : S.IsShort j) (hjT : T.IsShort (e.hLen ▸ j)) :
    Table.Iso (S.prune j hjS) (T.prune (e.hLen ▸ j) hjT) :=
  let hLenP : S.n - 1 = T.n - 1 := congrArg (· - 1) e.hLen
  have skip_eq : ∀ i : Fin (S.n - 1),
      T.skip (e.hLen ▸ j) (hLenP ▸ i) = e.hLen ▸ S.skip j i := fun i => by
    apply Fin.ext; simp only [Table.skip, cast_val]; split_ifs <;> omega
  { hLen   := hLenP
    hCodom := fun i => (e.hCodom (S.skip j i)).trans (congrArg T.codom (skip_eq i).symm)
    iso    := e.iso
    hCol   := fun i => by
      simp only [Table.prune]
      rw [e.hCol (S.skip j i)]
      congr 1
      rw [← Table.x_at_eq (skip_eq i), Category.assoc, eqToHom_trans] }

/-- The converse of τ3: if xⱼ is short, then ⟨T;x⟩ ∈ τ ↔ ⟨T;x̂ⱼ⟩ ∈ τ. -/
theorem tau3_converse (tab : Table 𝒞) (j : Fin tab.n) (hShort : tab.IsShort j) :
    τ.mem tab ↔ τ.mem (tab.prune j hShort) := by
  refine ⟨fun h => τ.tau3 tab j hShort h, fun hPrune => ?_⟩
  -- r.rep ∈ τ, e : Iso tab r.rep.
  let r := τ.resurfacing tab
  let j' : Fin r.rep.n := r.iso.hLen ▸ j
  -- Step 1: j'-th column of r.rep is short.
  have hShortT : r.rep.IsShort j' := isShort_of_iso r.iso j hShort
  -- Step 2: r.rep.prune j' ∈ τ.
  have hTprune := τ.tau3 r.rep j' hShortT r.mem
  -- Step 3: Iso (tab.prune j) (r.rep.prune j').
  have ePrune := iso_prune r.iso j hShort hShortT
  -- Step 4: τ1-uniqueness: tab.prune j = r.rep.prune j'.
  have hEq : tab.prune j hShort = r.rep.prune j' hShortT :=
    τ.tau1_unique (tab.prune j hShort) _ _ hPrune hTprune ⟨Table.Iso.refl _⟩ ⟨ePrune⟩
  -- Step 5: tab.T = r.rep.T (sources equal, since prune preserves .T).
  have hSrc : tab.T = r.rep.T := congrArg (·.T) hEq
  -- Step 6: The source iso r.iso.iso.hom equals eqToHom hSrc.
  --   (r.iso.iso.hom acts as identity on every column of tab by hEq + hShort;
  --    joint monicity then gives r.iso.iso.hom = hSrc ▸ 𝟙 = eqToHom hSrc.)
  have hId : r.iso.iso.hom = eqToHom hSrc := by sorry
  -- Step 7: Conclude tab = r.rep from hId and the iso fields.
  have hTabEq : tab = r.rep := by sorry
  rw [hTabEq]; exact r.mem

end TCat

end Freyd
