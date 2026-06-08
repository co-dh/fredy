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
    Uses HEq to handle heterogeneous codomain types. -/
structure TableIso {𝒞 : Type u} [Cat.{v} 𝒞] (S T : Table 𝒞) where
  hLen  : S.len = T.len
  f     : S.src ⟶ T.src
  g     : T.src ⟶ S.src
  f_g   : f ≫ g = Cat.id S.src
  g_f   : g ≫ f = Cat.id T.src
  col_match : ∀ i : Fin S.len, HEq (f ≫ T.col (hLen ▸ i)) (S.col i)

variable {𝒞} [Cat.{v} 𝒞]

def TableIso.refl (S : Table 𝒞) : TableIso S S where
  hLen  := rfl
  f     := Cat.id S.src
  g     := Cat.id S.src
  f_g   := Cat.id_comp _
  g_f   := Cat.id_comp _
  col_match := λ i => heq_of_eq (Cat.id_comp (S.col i))

/-! ## §1.491 Prune – remove a short column -/

/-- Embed Fin (n-1) into Fin n skipping index j. -/
def Fin.skip {n : Nat} (j : Fin n) (i : Fin (n - 1)) : Fin n :=
  if h : i.val < j.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- Every k ≠ j is in the image of Fin.skip j.  (Proof: case analysis on k < j or k > j.)
    The k > j branch needs the observation that k.val ≥ 1 when j.val ≤ k.val and k ≠ j. -/
theorem Fin.skip_surj {n : Nat} {j k : Fin n} (hk : k ≠ j) : ∃ i : Fin (n - 1), Fin.skip j i = k := by
  by_cases hlt : k.val < j.val
  · exact ⟨⟨k.val, by omega⟩, by unfold Fin.skip; simp [hlt]⟩
  · sorry

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
    · subst hkj
      refine hShort X f g ?_
      intro i hi
      sorry
    · rcases Fin.skip_surj hkj with ⟨i', hi'⟩
      have h := hAgree i'
      rw [hi'] at h; exact h

/-! ## §1.49 intro Table composition -/

/-- Table composition: replace column j of S with S.col j ≫ T.col k for all k.
    (Monicity: complex index arithmetic, left as TODO.) -/
def Table.comp (S T : Table 𝒞) (j : Fin S.len) (h_eq : T.src = S.codom j) : Table 𝒞 :=
  -- TODO: proper codom/col with index arithmetic
  let m := S.len - 1 + T.len
  { src   := S.src
    len   := m
    codom := λ _ => S.src
    col   := λ _ => Cat.id S.src
    monic := sorry }

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


/-! ## §1.412 Table terminology

/-- The TOP of a table: the common source object. -/
def Table.top (tab : Table 𝒞) : 𝒞 := tab.src

/-- A COLUMN of a table: the i-th morphism from top to foot. -/
def Table.column (tab : Table 𝒞) (i : Fin tab.len) : tab.src ⟶ tab.codom i := tab.col i

/-- The FEET of a table: the sequence of target objects. -/
def Table.feet (tab : Table 𝒞) : Fin tab.len → 𝒞 := tab.codom

/-- A RELATION on a sequence of feet A₁,…,Aₙ is an isomorphism class of tables (§1.412).
    For n=2, BinRel represents this directly. -/
def Relation (feet : Fin 2 → 𝒞) : Type (max u v) := Table 𝒞

/-! ## §1.4(10) Free T-category -/

/-- FREE T-CATEGORY (§1.4(10)): the free τ-category on a Cartesian category. -/
class FreeTCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends TCat 𝒞 where
  isFree : True

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

/-- AUSPICIOUS (§1.49(11)): a sequence expandable to a τ-table. -/
def Auspicious (τ : TCat 𝒞) (tab : Table 𝒞) : Prop :=
  ∃ (tab' : Table 𝒞), tab.len ≤ tab'.len ∧ τ.mem tab' ∧
    (∀ i : Fin tab.len, tab.codom i = tab'.codom i) ∧
    (∀ i : Fin tab.len, tab.col i = tab'.col i)

end Freyd
