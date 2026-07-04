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
     (`solve_profit`, giving `solve ⊑ spec`) and dominates every achievable profit. Together
     (`solve_correct`) this is `solve = max (≤) · Λ spec`, evaluated pointwise in the Set model.

  Mathlib-free.  Correctness now flows from the GREEDY THEOREM (`A7_4_Horner.horner_correct`), so
  the headline axioms are {propext, Classical.choice, Quot.sound} — the `Classical.choice` is the
  honest cost of the relational-catamorphism universal property, inherited via `cataR_eq_relCata`.
-/
import Fredy.A6_SnocList
import Fredy.A7_4_Horner
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

/-! ## The greedy route: the profit sweep as the projection of a Pareto optimum

  Like Kadane (`Fredy.L53`), best-single-trade is a two-component running-best scan: `bestProfit`
  needs `minSoFar`, so the scalar answer is not a catamorphism.  The genuine route (built once in
  `Fredy.A7_4_Horner`): the PAIR algebra is monotone on the PRODUCT (Pareto) order — here the first
  coordinate (running minimum) is ordered by `≥` (a smaller running min is BETTER) and the second by
  `≤` — so `A7_2.greedy_max` (through `greedy_max_of_refinement`) puts the fold inside the Pareto
  frontier of a non-deterministic GENERATOR `gen`, whose second component is read off as the answer. -/

/-- `imin`/`imax` are monotone in both arguments. -/
theorem imin_mono {a a' b b' : Int} (ha : a ≤ a') (hb : b ≤ b') : imin a b ≤ imin a' b' := by
  unfold imin; split <;> split <;> omega
theorem imax_mono {a a' b b' : Int} (ha : a ≤ a') (hb : b ≤ b') : imax a b ≤ imax a' b' := by
  unfold imax; split <;> split <;> omega

/-- The non-deterministic GENERATOR `S` whose Pareto frontier the deterministic fold computes: at a
    leaf, the sole pair `(x,0)`; at a `snoc`, the running min `m` becomes `m` or `p`, and the best
    profit `b` is kept or reset to `p - m` (sell at `p`, buy at the running min).  `alg` is one
    deterministic choice inside it. -/
def genFn : (Fobj Int Int (⟨Int × Int⟩ : RelSet.{0})).carrier → (Int × Int) → Prop
  | Sum.inl x, w => w = (x, 0)
  | Sum.inr (st, p), w => (w.1 = st.1 ∨ w.1 = p) ∧ (w.2 = st.2 ∨ w.2 = p - st.1)

/-- The generator as a (non-deterministic) morphism `F(ℤ×ℤ) ⟶ ℤ×ℤ`. -/
def gen : Fobj Int Int (⟨Int × Int⟩ : RelSet.{0}) ⟶ (⟨Int × Int⟩ : RelSet.{0}) := genFn

/-- The PRODUCT (Pareto) order used by the greedy theorem: `w` dominates `w'` iff its running min
    is `≤` (SMALLER is better) and its profit is `≥`.  `maxRel prodDom` then picks the pair with the
    smallest running min and the largest profit — the deterministic step. -/
def prodDom : (⟨Int × Int⟩ : RelSet.{0}) ⟶ ⟨Int × Int⟩ :=
  fun w w' => w.1 ≤ w'.1 ∧ w'.2 ≤ w.2

/-- `prodDom` is transitive (`R·R ⊑ R`). -/
theorem prodDom_trans : prodDom ≫ prodDom ⊑ prodDom := by
  rw [le_iff]; rintro w w' ⟨w'', ⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩; exact ⟨by omega, by omega⟩

/-- The deterministic step `alg` is MONOTONIC on the product order `prodDom`. -/
theorem alg_mono : MonotonicAlg (F := F Int Int) alg prodDom := by
  show (F Int Int).map prodDom ≫ alg ⊑ alg ≫ prodDom
  rw [le_iff]; rintro u w ⟨u', hFR, rfl⟩
  refine ⟨algFn u, rfl, ?_⟩
  cases u with
  | inl x => cases u' with
    | inl x' => have hx : x = x' := hFR; subst hx; exact ⟨Int.le_refl _, Int.le_refl _⟩
    | inr q => exact hFR.elim
  | inr pr => cases u' with
    | inl x' => exact hFR.elim
    | inr q' =>
      obtain ⟨st, p⟩ := pr; obtain ⟨st', p'⟩ := q'
      obtain ⟨hd, hpp⟩ := hFR
      have hd1 : st.1 ≤ st'.1 := hd.1
      have hd2 : st'.2 ≤ st.2 := hd.2
      have hpp' : p = p' := hpp
      refine ⟨?_, ?_⟩
      · show imin st.1 p ≤ imin st'.1 p'
        exact imin_mono (by omega) (by omega)
      · show imax st'.2 (p' - st'.1) ≤ imax st.2 (p - st.1)
        exact imax_mono hd2 (by omega)

/-- Greedy-step refinement, part 1: the deterministic choice is one of the generated candidates. -/
theorem alg_le_gen : alg ⊑ gen := by
  rw [le_iff]; intro u w hw
  have hwe : w = algFn u := hw; subst hwe
  cases u with
  | inl x => exact rfl
  | inr pr =>
    obtain ⟨st, p⟩ := pr
    exact ⟨imin_eq_or st.1 p, imax_eq_or st.2 (p - st.1)⟩

/-- Greedy-step refinement, part 2: the deterministic choice `prodDom`-dominates every candidate. -/
theorem gen_recip_alg_le : gen° ≫ alg ⊑ prodDom° := by
  rw [le_iff]; rintro w1 w2 ⟨u, hgu, rfl⟩
  cases u with
  | inl x => have hw1 : w1 = (x, 0) := hgu; subst hw1; exact ⟨Int.le_refl _, Int.le_refl _⟩
  | inr pr =>
    obtain ⟨st, p⟩ := pr
    obtain ⟨he, hb⟩ := hgu
    refine ⟨?_, ?_⟩
    · show imin st.1 p ≤ w1.1
      rcases he with h | h <;> rw [h]
      · exact imin_le_left _ _
      · exact imin_le_right _ _
    · show w1.2 ≤ imax st.2 (p - st.1)
      rcases hb with h | h <;> rw [h]
      · exact imax_ge_left _ _
      · exact imax_ge_right _ _

/-- The greedy-step refinement `alg ⊑ ΛS·max prodDom` (the hypothesis `greedy_max` consumes). -/
theorem alg_ref : alg ⊑ A gen ≫ maxRel prodDom :=
  le_A_comp_maxRel_iff.mpr ⟨alg_le_gen, gen_recip_alg_le⟩

/-! ### The generator computes exactly the spec (soundness + completeness), independent of greedy -/

/-- Lift a profit of `xs` to a profit of `snoc xs p` (the buy-before-sell window only grows). -/
theorem profit_snoc (xs : SnocList Int Int) (p v : Int) (h : profit xs v) :
    profit (SnocList.snoc xs p) v := by
  rcases h with h0 | ⟨b, s, hbef, hv⟩
  · exact Or.inl h0
  · exact Or.inr ⟨b, s, Or.inl hbef, hv⟩

/-- **Soundness**: every generatable pair has a member first component (a price) and an achievable
    profit second component.  (The member invariant is needed to close the `b := p - m` case.) -/
theorem gen_sound : ∀ (xs : SnocList Int Int) (w : Int × Int),
    cataFold gen xs w → mem xs w.1 ∧ profit xs w.2 := by
  intro xs; induction xs with
  | wrap x => intro w h; have hw : w = (x, 0) := h; subst hw; exact ⟨rfl, Or.inl rfl⟩
  | snoc xs p ih =>
    intro w h
    obtain ⟨w', hw', he, hb⟩ := h
    obtain ⟨ihmem, ihprof⟩ := ih w' hw'
    have hmem1 : mem (SnocList.snoc xs p) w.1 := by
      simp only [mem]
      rcases he with h1 | h1
      · exact Or.inl (by rw [h1]; exact ihmem)
      · exact Or.inr h1
    refine ⟨hmem1, ?_⟩
    rcases hb with h2 | h2
    · exact (by rw [h2]; exact profit_snoc xs p w'.2 ihprof)
    · refine Or.inr ⟨w'.1, p, Or.inr ⟨ihmem, rfl⟩, ?_⟩
      rw [h2]

/-- Totality of the generator (it is entire): every list has some generatable pair. -/
theorem gen_total : ∀ (xs : SnocList Int Int), ∃ w, cataFold gen xs w := by
  intro xs; induction xs with
  | wrap x => exact ⟨(x, 0), rfl⟩
  | snoc xs p ih =>
    obtain ⟨w', hw'⟩ := ih
    exact ⟨w', w', hw', Or.inl rfl, Or.inl rfl⟩

/-- **Completeness (first component)**: a price `b` occurring in `xs` is generatable as the first
    component of some pair.  Closes the buy-at-`b` case of `spec_gen`. -/
theorem mem_gen : ∀ (xs : SnocList Int Int) (b : Int),
    mem xs b → ∃ b2, cataFold gen xs (b, b2) := by
  intro xs; induction xs with
  | wrap x => intro b hb; have hbx : b = x := hb; exact ⟨0, show (b, 0) = (x, 0) by rw [hbx]⟩
  | snoc xs p ih =>
    intro b hb
    simp only [mem] at hb
    rcases hb with hm | hm
    · obtain ⟨b2', hb2'⟩ := ih b hm
      exact ⟨b2', (b, b2'), hb2', Or.inl rfl, Or.inl rfl⟩
    · obtain ⟨w', hw'⟩ := gen_total xs
      exact ⟨w'.2, w', hw', Or.inr hm, Or.inl rfl⟩

/-- **Completeness**: every achievable profit `v` is the second component of some generatable pair.
    (Uses `mem_gen` for the "reset to `p - buy`" case and the IH for the "kept" case.) -/
theorem spec_gen : ∀ (xs : SnocList Int Int) (v : Int),
    profit xs v → ∃ e, cataFold gen xs (e, v) := by
  intro xs; induction xs with
  | wrap x =>
    intro v hv
    rcases hv with h0 | ⟨b, s, hbef, _⟩
    · exact ⟨x, show (x, v) = (x, 0) by rw [h0]⟩
    · exact hbef.elim
  | snoc xs p ih =>
    intro v hv
    rcases hv with h0 | ⟨b, s, hbef, hvs⟩
    · obtain ⟨e', he'⟩ := ih 0 (Or.inl rfl)
      exact ⟨e', (e', 0), he', Or.inl rfl, Or.inl h0⟩
    · simp only [Before] at hbef
      rcases hbef with hb | ⟨hmem, hsp⟩
      · obtain ⟨e', he'⟩ := ih v (Or.inr ⟨b, s, hb, hvs⟩)
        exact ⟨e', (e', v), he', Or.inl rfl, Or.inl rfl⟩
      · obtain ⟨b2, hb2⟩ := mem_gen xs b hmem
        exact ⟨b, (b, b2), hb2, Or.inl rfl, Or.inr (show v = p - b by omega)⟩

/-! ## Correctness: `solve` computes the maximum achievable profit — VIA the greedy theorem -/

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ spec`, pointwise in `Rel(Set)`):
    `solve xs` is an achievable profit and is `≤`-greatest among all achievable profits.  Both
    halves flow from `A7_4_Horner.horner_correct` — i.e. from `A7_2.greedy_max` applied to the pair
    carrier — with the generator characterisation supplying only "program = spec". -/
theorem solve_correct (xs : SnocList Int Int) :
    profit xs (solveFn xs) ∧ ∀ v, profit xs v → v ≤ solveFn xs :=
  horner_correct gen alg prodDom foldFn (graph_map algFn) cataFold_alg
    prodDom_trans alg_mono alg_ref (fun x y h => h.2) spec
    (fun xs w h => (gen_sound xs w h).2) spec_gen xs

/-- `solve`'s output is an achievable profit (achievability half of `solve_correct`). -/
theorem solve_profit (xs : SnocList Int Int) : profit xs (solveFn xs) := (solve_correct xs).1

/-- **The program refines the specification**: every value `solve` returns is an achievable profit. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs v h => ?_)
  have hv : v = solveFn xs := h
  rw [hv]; exact solve_profit xs

/-! ## Running the program -/

/-- Build a price list from a first price and the rest, in day order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 7 [1, 5, 3, 6, 4]) = 5 := by decide
example : solveFn (ofList 7 [6, 4, 3, 1]) = 0 := by decide
example : solveFn (ofList 2 [4, 1]) = 2 := by decide

end Freyd.Alg.RelSet.LC121
