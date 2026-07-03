/-
  LeetCode 121 — Best Time to Buy and Sell Stock — as an ALLEGORY PROGRAM.

  Problem: given prices `x₀,…,x_{n-1}` (one per day), pick a buy day `i` and a later sell day `j > i`
  maximising the profit `x_j − x_i`; if no trade is profitable, the answer is `0`.

  The point of this file is to *program in the allegory* `Rel(Set)` (Freyd's category of sets and
  relations, `Fredy.A6_1_RelSet`), reusing the Bird & de Moor toolkit:

  1. **Data** — a non-empty list of prices is the initial algebra `SnocList ℤ ℤ` of the functor
     `F X = ℤ + X × ℤ` (the reusable engine `Fredy.A6_SnocList`).  `wrap x` is a single price,
     `snoc xs p` appends a price — so a left-to-right scan is a CATAMORPHISM over this datatype.

  2. **Program** — the O(n) sweep is the fold with state `(minSoFar, bestProfit)` and algebra
     `[ x ↦ (x,0),  ((m,b),p) ↦ (min m p, max b (p−m)) ]`.  We package it as a genuine morphism
     `solve : Prices ⟶ ℤ` in `Rel(Set)` (a `Map`, i.e. the graph of a function) and prove it *is*
     the catamorphism of that algebra followed by the second projection (`solve_eq_cata`).

  3. **Specification** — `spec : Prices ⟶ ℤ` is the relation of *achievable* profits: `0`, or `s−b`
     for a buy price `b` occurring strictly before a sell price `s`.  LeetCode asks for its
     `≤`-maximum, i.e. `max (≤) · Λ spec` in `Rel(Set)`.

  4. **Correctness** — `solve` computes exactly that maximum: it returns an achievable profit
     (`solve_profit`, giving `solve ⊑ spec`) and dominates every achievable profit
     (`profit_le_solve`).  Together (`solve_correct`) this is `solve = max (≤) · Λ spec`, evaluated
     pointwise in the Set model.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC121

open Freyd Freyd.Alg.RelSet.SL

/-! ## Integer `min`/`max` (mathlib-free, so we control the rewrite lemmas) -/

def imin (a b : Int) : Int := if a ≤ b then a else b
def imax (a b : Int) : Int := if a ≤ b then b else a

theorem imin_le_left  (a b : Int) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Int) : imin a b ≤ b := by unfold imin; split <;> omega
theorem imin_eq_or (a b : Int) : imin a b = a ∨ imin a b = b := by
  unfold imin; split; exacts [Or.inl rfl, Or.inr rfl]
theorem imax_ge_left  (a b : Int) : a ≤ imax a b := by unfold imax; split <;> omega
theorem imax_ge_right (a b : Int) : b ≤ imax a b := by unfold imax; split <;> omega
theorem imax_eq_or (a b : Int) : imax a b = a ∨ imax a b = b := by
  unfold imax; split; exacts [Or.inr rfl, Or.inl rfl]

/-! ## Data: prices as a non-empty snoc-list of integers -/

/-- The object of price lists in `Rel(Set)` — `SnocList ℤ ℤ` (`wrap x` = single price, `snoc xs p`
    = `xs` with a new final price `p`). -/
abbrev Prices : RelSet.{0} := dSL Int Int
/-- The object of integers (profits) in `Rel(Set)`. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-! ## The program: the left-scan catamorphism `[base, step]`, state `(minSoFar, bestProfit)` -/

/-- The fold algebra `[ x ↦ (x,0),  ((m,b),p) ↦ (min m p, max b (p−m)) ] : F(ℤ×ℤ) → ℤ×ℤ`. -/
def algFn : (Fobj Int Int (⟨Int × Int⟩ : RelSet.{0})).carrier → (Int × Int)
  | Sum.inl x => (x, 0)
  | Sum.inr (st, p) => (imin st.1 p, imax st.2 (p - st.1))

/-- The algebra as a morphism (a `Map`) `F(ℤ×ℤ) ⟶ ℤ×ℤ` in `Rel(Set)`. -/
def alg : Fobj Int Int (⟨Int × Int⟩ : RelSet.{0}) ⟶ (⟨Int × Int⟩ : RelSet.{0}) := graph algFn

/-- The concrete fold (structural recursion), returning `(minSoFar, bestProfit)`. -/
def foldFn : SnocList Int Int → Int × Int
  | SnocList.wrap x => (x, 0)
  | SnocList.snoc xs p => (imin (foldFn xs).1 p, imax (foldFn xs).2 (p - (foldFn xs).1))

/-- The answer: the second component (best profit) of the fold. -/
def solveFn (xs : SnocList Int Int) : Int := (foldFn xs).2

/-- **The allegory program**: LeetCode 121's solution as a morphism `Prices ⟶ ℤ` in `Rel(Set)`. -/
def solve : Prices ⟶ dZ := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree. -/
theorem cataFold_alg : ∀ (xs : SnocList Int Int) (r : Int × Int),
    cataFold alg xs r ↔ r = foldFn xs := by
  intro xs; induction xs with
  | wrap x => intro r; exact Iff.rfl
  | snoc xs p ih =>
    intro r
    simp only [cataFold_snoc]
    constructor
    · rintro ⟨r', hr', hfr⟩
      rw [ih r'] at hr'; subst hr'; exact hfr
    · intro h; exact ⟨foldFn xs, (ih (foldFn xs)).mpr rfl, h⟩

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈ · snd`, a fold followed by the
    projection onto `bestProfit`. -/
theorem solve_eq_cata : solve = cataR alg ≫ graph (Prod.snd : Int × Int → Int) := by
  apply hom_ext; intro xs v
  simp only [solve, graph, comp_apply, cataR]
  constructor
  · intro hv; exact ⟨foldFn xs, (cataFold_alg xs (foldFn xs)).mpr rfl, hv⟩
  · rintro ⟨st, hst, hv⟩; rw [(cataFold_alg xs st).mp hst] at hv; exact hv

/-! ## Specification: the maximum achievable profit -/

/-- `mem xs b` — the price `b` occurs in `xs`. -/
def mem : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun b => b = x
  | SnocList.snoc xs p => fun b => mem xs b ∨ b = p

/-- `Before xs b s` — a price `b` occurs strictly before a price `s` (a valid buy day `<` sell day). -/
def Before : SnocList Int Int → Int → Int → Prop
  | SnocList.wrap x => fun b s => False
  | SnocList.snoc xs p => fun b s => Before xs b s ∨ (mem xs b ∧ s = p)

/-- `profit xs v` — `v` is an achievable profit: either `0` (no trade) or `s − b` for a buy price
    `b` strictly before a sell price `s`.  This is the transpose `Λ⁻¹ spec` of the spec relation. -/
def profit (xs : SnocList Int Int) (v : Int) : Prop :=
  v = 0 ∨ ∃ b s, Before xs b s ∧ v = s - b

/-- The **specification** as a morphism `Prices ⟶ ℤ` in `Rel(Set)`: the relation of achievable
    profits.  LeetCode 121 asks for its `≤`-maximum, `max (≤) · Λ spec`. -/
def spec : Prices ⟶ dZ := fun xs v => profit xs v

/-! ## Invariants of the fold -/

/-- The running minimum price. -/
def minPrice : SnocList Int Int → Int
  | SnocList.wrap x => x
  | SnocList.snoc xs p => imin (minPrice xs) p

/-- The first fold component is the minimum price. -/
theorem foldFn_fst : ∀ xs, (foldFn xs).1 = minPrice xs := by
  intro xs; induction xs with
  | wrap x => rfl
  | snoc xs p ih => show imin (foldFn xs).1 p = imin (minPrice xs) p; rw [ih]

/-- The minimum price is a lower bound of every price in the list. -/
theorem minPrice_le_of_mem : ∀ (xs : SnocList Int Int) (b : Int), mem xs b → minPrice xs ≤ b := by
  intro xs; induction xs with
  | wrap x => intro b h; simp only [mem] at h; show x ≤ b; omega
  | snoc xs p ih =>
    intro b h; simp only [mem] at h; show imin (minPrice xs) p ≤ b
    cases h with
    | inl hm => have := ih b hm; have := imin_le_left (minPrice xs) p; omega
    | inr hm => have := imin_le_right (minPrice xs) p; omega

/-- The minimum price is itself a member of the list (the list is non-empty). -/
theorem mem_minPrice : ∀ xs, mem xs (minPrice xs) := by
  intro xs; induction xs with
  | wrap x => rfl
  | snoc xs p ih =>
    show mem (SnocList.snoc xs p) (imin (minPrice xs) p); simp only [mem]
    cases imin_eq_or (minPrice xs) p with
    | inl he => rw [he]; exact Or.inl ih
    | inr he => exact Or.inr he

/-- The best profit is never negative (buy = sell is always an option, giving `0`). -/
theorem solveFn_nonneg : ∀ xs, 0 ≤ solveFn xs := by
  intro xs; induction xs with
  | wrap x => show (0 : Int) ≤ 0; exact Int.le_refl 0
  | snoc xs p ih =>
    have h : 0 ≤ (foldFn xs).2 := ih
    have hge := imax_ge_left (foldFn xs).2 (p - (foldFn xs).1)
    show 0 ≤ imax (foldFn xs).2 (p - (foldFn xs).1); omega

/-! ## Correctness: `solve` computes the maximum achievable profit -/

/-- `solve` dominates every achievable profit. -/
theorem profit_le_solve : ∀ (xs : SnocList Int Int) (v : Int), profit xs v → v ≤ solveFn xs := by
  intro xs; induction xs with
  | wrap x =>
    intro v hv
    cases hv with
    | inl h0 => rw [h0]; exact solveFn_nonneg (SnocList.wrap x)
    | inr h => obtain ⟨b, s, hbef, _⟩ := h; exact hbef.elim
  | snoc xs p ih =>
    intro v hv
    cases hv with
    | inl h0 => rw [h0]; exact solveFn_nonneg (SnocList.snoc xs p)
    | inr h =>
      obtain ⟨b, s, hbef, hv⟩ := h; subst hv
      simp only [Before] at hbef
      have hmax1 := imax_ge_left  (foldFn xs).2 (p - (foldFn xs).1)
      have hmax2 := imax_ge_right (foldFn xs).2 (p - (foldFn xs).1)
      show s - b ≤ imax (foldFn xs).2 (p - (foldFn xs).1)
      cases hbef with
      | inl hb =>
        have hsx : s - b ≤ (foldFn xs).2 := ih (s - b) (Or.inr ⟨b, s, hb, rfl⟩)
        omega
      | inr hb =>
        obtain ⟨hmem, hsp⟩ := hb; subst hsp
        have hle  : minPrice xs ≤ b := minPrice_le_of_mem xs b hmem
        have hfst : (foldFn xs).1 = minPrice xs := foldFn_fst xs
        omega

/-- `solve`'s output is an achievable profit — hence `solve ⊑ spec`. -/
theorem solve_profit : ∀ xs, profit xs (solveFn xs) := by
  intro xs; induction xs with
  | wrap x => exact Or.inl rfl
  | snoc xs p ih =>
    cases imax_eq_or (foldFn xs).2 (p - (foldFn xs).1) with
    | inl he =>
      have hlift : profit xs (solveFn xs) → profit (SnocList.snoc xs p) (solveFn xs) := by
        intro hp
        cases hp with
        | inl h0 => exact Or.inl h0
        | inr h => obtain ⟨b, s, hbef, hv⟩ := h; exact Or.inr ⟨b, s, Or.inl hbef, hv⟩
      have heq : solveFn (SnocList.snoc xs p) = solveFn xs := he
      rw [heq]; exact hlift ih
    | inr he =>
      have hbef : Before (SnocList.snoc xs p) (minPrice xs) p := by
        show Before xs (minPrice xs) p ∨ (mem xs (minPrice xs) ∧ p = p)
        exact Or.inr ⟨mem_minPrice xs, rfl⟩
      have hfst : (foldFn xs).1 = minPrice xs := foldFn_fst xs
      refine Or.inr ⟨minPrice xs, p, hbef, ?_⟩
      show imax (foldFn xs).2 (p - (foldFn xs).1) = p - minPrice xs
      rw [he, hfst]

/-- **The program refines the specification**: every value `solve` returns is an achievable profit. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs v h => ?_)
  have hv : v = solveFn xs := h
  rw [hv]; exact solve_profit xs

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ spec`, pointwise in `Rel(Set)`):
    `solve xs` is an achievable profit and is `≤`-greatest among all achievable profits. -/
theorem solve_correct (xs : SnocList Int Int) :
    profit xs (solveFn xs) ∧ ∀ v, profit xs v → v ≤ solveFn xs :=
  ⟨solve_profit xs, profit_le_solve xs⟩

/-! ## Running the program -/

/-- Build a price list from a first price and the rest, in day order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 7 [1, 5, 3, 6, 4]) = 5 := by decide
example : solveFn (ofList 7 [6, 4, 3, 1]) = 0 := by decide
example : solveFn (ofList 2 [4, 1]) = 2 := by decide

end Freyd.Alg.RelSet.LC121
