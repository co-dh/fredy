/-
  LeetCode 53 — Maximum Subarray (Kadane's algorithm) — as an ALLEGORY PROGRAM.

  Problem: given a non-empty array of integers `x₀,…,x_{n-1}` (possibly negative), find the maximum
  sum over all NON-EMPTY contiguous subarrays.  (The empty subarray is not allowed, so an
  all-negative array's answer is its largest single element.)

  Same recipe as `Fredy/L121.lean` (see `Fredy/leetcode.md`, skill S0):

  1. **Data** — the array is the initial algebra `SnocList ℤ ℤ` of `F X = ℤ + X × ℤ`
     (`Fredy.A6_SnocList`); `wrap x` is a single-element array, `snoc xs p` appends `p`.

  2. **Program** — Kadane's sweep is the fold with state `(bestEndingHere, bestSoFar)` and algebra
     `[ x ↦ (x,x),  ((e,b),p) ↦ (max p (e+p), max b (max p (e+p))) ]`.  We package it as a `Map`
     `solve : Arr ⟶ ℤ` in `Rel(Set)` and prove it *is* the catamorphism of that algebra followed by
     the second projection (`solve_eq_cata`).

  3. **Specification** — two mutually-referencing relations: `suffixSum xs v` says `v` is the sum of
     some non-empty SUFFIX of `xs` (a subarray ending at the last element); `subSum xs v` says `v` is
     the sum of ANY non-empty contiguous subarray of `xs` — either a subarray of the prefix, or a
     suffix.  `spec = subSum` is the transpose `Λ⁻¹ spec`, and LeetCode 53 asks for its `≤`-maximum,
     `max (≤) · Λ spec`.

  4. **Correctness** — `solve` computes exactly that maximum: it returns an achievable subarray sum
     (`solve_sub`, giving `solve ⊑ spec`) and dominates every achievable subarray sum
     (`subSum_le_solve`).  Together (`solve_correct`) this is `solve = max (≤) · Λ spec`.

  Mathlib-free.  Correctness now flows from the GREEDY THEOREM (`A7_4_Horner.horner_correct`), so
  the headline axioms are {propext, Classical.choice, Quot.sound} — the `Classical.choice` is the
  honest cost of the relational-catamorphism universal property, inherited via `cataR_eq_relCata`.
-/
import Fredy.A6_SnocList
import Fredy.A7_4_Horner
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC53

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

/-! ## Data: arrays as a non-empty snoc-list of integers -/

/-- The object of arrays in `Rel(Set)` — `SnocList ℤ ℤ` (`wrap x` = single element, `snoc xs p` =
    `xs` with a new final element `p`). -/
abbrev Arr : RelSet.{0} := dSL Int Int
/-- The object of integers (subarray sums) in `Rel(Set)`. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-! ## The program: Kadane's fold, state `(bestEndingHere, bestSoFar)` -/

/-- The fold algebra `[ x ↦ (x,x),  ((e,b),p) ↦ (max p (e+p), max b (max p (e+p))) ] : F(ℤ×ℤ) → ℤ×ℤ`. -/
def algFn : (Fobj Int Int (⟨Int × Int⟩ : RelSet.{0})).carrier → (Int × Int)
  | Sum.inl x => (x, x)
  | Sum.inr (st, p) => let e := imax p (st.1 + p); (e, imax st.2 e)

/-- The algebra as a morphism (a `Map`) `F(ℤ×ℤ) ⟶ ℤ×ℤ` in `Rel(Set)`. -/
def alg : Fobj Int Int (⟨Int × Int⟩ : RelSet.{0}) ⟶ (⟨Int × Int⟩ : RelSet.{0}) := graph algFn

/-- The concrete fold (structural recursion), returning `(bestEndingHere, bestSoFar)`. -/
def foldFn : SnocList Int Int → Int × Int
  | SnocList.wrap x => (x, x)
  | SnocList.snoc xs p => let e := imax p ((foldFn xs).1 + p); (e, imax (foldFn xs).2 e)

/-- The answer: the second component (best subarray sum) of the fold. -/
def solveFn (xs : SnocList Int Int) : Int := (foldFn xs).2

/-- **The allegory program**: LeetCode 53's solution as a morphism `Arr ⟶ ℤ` in `Rel(Set)`. -/
def solve : Arr ⟶ dZ := graph solveFn

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
    projection onto `bestSoFar`. -/
theorem solve_eq_cata : solve = cataR alg ≫ graph (Prod.snd : Int × Int → Int) := by
  apply hom_ext; intro xs v
  simp only [solve, graph, comp_apply, cataR]
  constructor
  · intro hv; exact ⟨foldFn xs, (cataFold_alg xs (foldFn xs)).mpr rfl, hv⟩
  · rintro ⟨st, hst, hv⟩; rw [(cataFold_alg xs st).mp hst] at hv; exact hv

/-! ## Specification: the maximum achievable subarray sum -/

/-- `suffixSum xs v` — `v` is the sum of some non-empty SUFFIX of `xs` (a subarray ending at the
    last element). -/
def suffixSum : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = x
  | SnocList.snoc xs p => fun v => v = p ∨ ∃ v', suffixSum xs v' ∧ v = v' + p

/-- `subSum xs v` — `v` is the sum of SOME non-empty contiguous subarray of `xs`: either a subarray
    entirely within the prefix, or a suffix (ending at the last element). -/
def subSum : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = x
  | SnocList.snoc xs p => fun v => subSum xs v ∨ suffixSum (SnocList.snoc xs p) v

/-- The **specification** as a morphism `Arr ⟶ ℤ` in `Rel(Set)`: the relation of achievable subarray
    sums.  LeetCode 53 asks for its `≤`-maximum, `max (≤) · Λ spec`. -/
def spec : Arr ⟶ dZ := fun xs v => subSum xs v

/-! ## The greedy route: Kadane's fold as the projection of a Pareto optimum

  Kadane's answer is NOT a scalar catamorphism (`bestSoFar` needs `bestEndingHere`), and its
  scalar step is not `≤`-monotone — so the plain greedy theorem does not apply to the headline
  scalar directly.  The genuine route (built once in `Fredy.A7_4_Horner`): the PAIR algebra is
  monotone on the PRODUCT (Pareto) order, so the greedy theorem `A7_2.greedy_max` (through
  `greedy_max_of_refinement`) puts the fold inside the Pareto frontier of a non-deterministic
  GENERATOR `gen`, and the scalar answer is the frontier's second component.  Below: the generator,
  the three greedy hypotheses (product monotonicity, transitivity, greedy-step refinement), and the
  "generator = spec" characterisation; `horner_correct` assembles them. -/

/-- `imax` is monotone in both arguments. -/
theorem imax_mono {a a' b b' : Int} (ha : a ≤ a') (hb : b ≤ b') : imax a b ≤ imax a' b' := by
  unfold imax; split <;> split <;> omega

/-- The non-deterministic GENERATOR `S` whose Pareto frontier the deterministic fold computes: at a
    leaf, the sole pair `(x,x)`; at a `snoc`, the running suffix `e` becomes `p` or `e+p`, and the
    best `b` is kept or reset to the new suffix `e`.  `alg` is one deterministic choice inside it. -/
def genFn : (Fobj Int Int (⟨Int × Int⟩ : RelSet.{0})).carrier → (Int × Int) → Prop
  | Sum.inl x, w => w = (x, x)
  | Sum.inr (st, p), w => (w.1 = p ∨ w.1 = st.1 + p) ∧ (w.2 = st.2 ∨ w.2 = w.1)

/-- The generator as a (non-deterministic) morphism `F(ℤ×ℤ) ⟶ ℤ×ℤ`. -/
def gen : Fobj Int Int (⟨Int × Int⟩ : RelSet.{0}) ⟶ (⟨Int × Int⟩ : RelSet.{0}) := genFn

/-- The PRODUCT (Pareto) order used by the greedy theorem: `w` dominates `w'` iff it is `≥` in both
    coordinates.  `maxRel prodDom` then picks the coordinatewise-greatest pair — Kadane's step. -/
def prodDom : (⟨Int × Int⟩ : RelSet.{0}) ⟶ ⟨Int × Int⟩ :=
  fun w w' => w'.1 ≤ w.1 ∧ w'.2 ≤ w.2

/-- `prodDom` is transitive (`R·R ⊑ R`). -/
theorem prodDom_trans : prodDom ≫ prodDom ⊑ prodDom := by
  rw [le_iff]; rintro w w' ⟨w'', ⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩; exact ⟨by omega, by omega⟩

/-- The deterministic Kadane step `alg` is MONOTONIC on the product order `prodDom`. -/
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
      have hd1 : st'.1 ≤ st.1 := hd.1
      have hd2 : st'.2 ≤ st.2 := hd.2
      have hpp' : p = p' := hpp
      refine ⟨?_, ?_⟩
      · show imax p' (st'.1 + p') ≤ imax p (st.1 + p)
        exact imax_mono (by omega) (by omega)
      · show imax st'.2 (imax p' (st'.1 + p')) ≤ imax st.2 (imax p (st.1 + p))
        exact imax_mono hd2 (imax_mono (by omega) (by omega))

/-- Greedy-step refinement, part 1: the deterministic choice is one of the generated candidates. -/
theorem alg_le_gen : alg ⊑ gen := by
  rw [le_iff]; intro u w hw
  have hwe : w = algFn u := hw; subst hwe
  cases u with
  | inl x => exact rfl
  | inr pr =>
    obtain ⟨st, p⟩ := pr
    exact ⟨imax_eq_or p (st.1 + p), imax_eq_or st.2 (imax p (st.1 + p))⟩

/-- Greedy-step refinement, part 2: the deterministic choice `prodDom`-dominates every candidate. -/
theorem gen_recip_alg_le : gen° ≫ alg ⊑ prodDom° := by
  rw [le_iff]; rintro w1 w2 ⟨u, hgu, rfl⟩
  cases u with
  | inl x => have hw1 : w1 = (x, x) := hgu; subst hw1; exact ⟨Int.le_refl _, Int.le_refl _⟩
  | inr pr =>
    obtain ⟨st, p⟩ := pr
    obtain ⟨he, hb⟩ := hgu
    refine ⟨?_, ?_⟩
    · show w1.1 ≤ imax p (st.1 + p)
      rcases he with h | h <;> rw [h]
      · exact imax_ge_left _ _
      · exact imax_ge_right _ _
    · show w1.2 ≤ imax st.2 (imax p (st.1 + p))
      rcases hb with h | h <;> rw [h]
      · exact imax_ge_left _ _
      · rcases he with h2 | h2 <;> rw [h2]
        · exact Int.le_trans (imax_ge_left _ _) (imax_ge_right _ _)
        · exact Int.le_trans (imax_ge_right _ _) (imax_ge_right _ _)

/-- The greedy-step refinement `alg ⊑ ΛS·max prodDom` (the hypothesis `greedy_max` consumes). -/
theorem alg_ref : alg ⊑ A gen ≫ maxRel prodDom :=
  le_A_comp_maxRel_iff.mpr ⟨alg_le_gen, gen_recip_alg_le⟩

/-! ### The generator computes exactly the spec (soundness + completeness), independent of greedy -/

/-- **Soundness**: every generatable pair has a suffix-sum first component and a subarray-sum
    second component.  (The suffix invariant is needed to close the `b := e` reset case.) -/
theorem gen_sound : ∀ (xs : SnocList Int Int) (w : Int × Int),
    cataFold gen xs w → suffixSum xs w.1 ∧ subSum xs w.2 := by
  intro xs; induction xs with
  | wrap x => intro w h; have hw : w = (x, x) := h; subst hw; exact ⟨rfl, rfl⟩
  | snoc xs p ih =>
    intro w h
    obtain ⟨w', hw', he, hb⟩ := h
    obtain ⟨ihsuf, ihsub⟩ := ih w' hw'
    have hsuf1 : suffixSum (SnocList.snoc xs p) w.1 := by
      simp only [suffixSum]
      rcases he with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨w'.1, ihsuf, h1⟩
    refine ⟨hsuf1, ?_⟩
    simp only [subSum]
    rcases hb with h2 | h2
    · exact Or.inl (by rw [h2]; exact ihsub)
    · exact Or.inr (by rw [h2]; exact hsuf1)

/-- Totality of the generator (it is entire): every list has some generatable pair. -/
theorem gen_total : ∀ (xs : SnocList Int Int), ∃ w, cataFold gen xs w := by
  intro xs; induction xs with
  | wrap x => exact ⟨(x, x), rfl⟩
  | snoc xs p ih =>
    obtain ⟨w', hw'⟩ := ih
    exact ⟨(p, w'.2), w', hw', Or.inl rfl, Or.inl rfl⟩

/-- **Completeness (diagonal)**: a suffix sum `v` is generatable as the "both components equal `v`"
    pair `(v, v)`.  This closes the suffix cases of `spec_gen` below. -/
theorem diag_gen : ∀ (xs : SnocList Int Int) (v : Int),
    suffixSum xs v → cataFold gen xs (v, v) := by
  intro xs; induction xs with
  | wrap x => intro v hv; have hvx : v = x := hv; show (v, v) = (x, x); rw [hvx]
  | snoc xs p ih =>
    intro v hv
    simp only [suffixSum] at hv
    rcases hv with h1 | ⟨v', hv', hveq⟩
    · obtain ⟨w', hw'⟩ := gen_total xs
      exact ⟨w', hw', Or.inl h1, Or.inr rfl⟩
    · exact ⟨(v', v'), ih v' hv', Or.inr (by rw [hveq]), Or.inr rfl⟩

/-- **Completeness**: every achievable subarray sum `v` is the second component of some generatable
    pair.  (Uses `diag_gen` for suffix subarrays and the IH for prefix subarrays.) -/
theorem spec_gen : ∀ (xs : SnocList Int Int) (v : Int),
    subSum xs v → ∃ e, cataFold gen xs (e, v) := by
  intro xs; induction xs with
  | wrap x => intro v hv; have hvx : v = x := hv; exact ⟨x, show (x, v) = (x, x) by rw [hvx]⟩
  | snoc xs p ih =>
    intro v hv
    simp only [subSum] at hv
    rcases hv with h1 | h2
    · obtain ⟨e', he'⟩ := ih v h1
      exact ⟨p, (e', v), he', Or.inl rfl, Or.inl rfl⟩
    · exact ⟨v, diag_gen (SnocList.snoc xs p) v h2⟩

/-! ## Correctness: `solve` computes the maximum achievable subarray sum — VIA the greedy theorem -/

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ spec`, pointwise in `Rel(Set)`):
    `solve xs` is an achievable subarray sum and is `≤`-greatest among all achievable subarray
    sums.  Both halves flow from `A7_4_Horner.horner_correct` — i.e. from `A7_2.greedy_max` applied
    to the pair carrier — with the generator characterisation supplying only "program = spec". -/
theorem solve_correct (xs : SnocList Int Int) :
    subSum xs (solveFn xs) ∧ ∀ v, subSum xs v → v ≤ solveFn xs :=
  horner_correct gen alg prodDom foldFn (graph_map algFn) cataFold_alg
    prodDom_trans alg_mono alg_ref (fun x y h => h.2) spec
    (fun xs w h => (gen_sound xs w h).2) spec_gen xs

/-- `solve` dominates every achievable subarray sum (domination half of `solve_correct`). -/
theorem subSum_le_solve (xs : SnocList Int Int) (v : Int) (h : subSum xs v) : v ≤ solveFn xs :=
  (solve_correct xs).2 v h

/-- `solve`'s output is an achievable subarray sum (achievability half of `solve_correct`). -/
theorem solve_sub (xs : SnocList Int Int) : subSum xs (solveFn xs) := (solve_correct xs).1

/-- **The program refines the specification**: every value `solve` returns is an achievable
    subarray sum. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs v h => ?_)
  have hv : v = solveFn xs := h
  rw [hv]; exact solve_sub xs

/-! ## Running the program -/

/-- Build an array from a first element and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList (-2) [1, -3, 4, -1, 2, 1, -5, 4]) = 6 := by decide
example : solveFn (ofList (-1) []) = -1 := by decide
example : solveFn (ofList 1 [2, 3]) = 6 := by decide
example : solveFn (ofList (-3) [-1, -2]) = -1 := by decide

end Freyd.Alg.RelSet.LC53
