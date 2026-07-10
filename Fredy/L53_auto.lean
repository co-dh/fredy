/-
  LeetCode 53 — Maximum Subarray (Kadane) — RE-DERIVED through `Fredy.AutoDerive`.

  Same problem, same program, same correctness statement as `Fredy/L53.lean`, but every
  relational side condition (`prodDom_trans`, `alg_mono`, `alg_le_gen`, `gen_recip_alg_le`,
  `alg_ref`, `cataFold_alg`, `gen_total`, `solve_eq_cata` — ~104 lines there) is discharged by
  `RunningBest`.  This file supplies only the CREATIVE content of the derivation:

  1. `kadane : RunningBest Int Int Int` — the algorithm (`base`/`step1`/`step2`), the
     generator's candidate sets (`cand1`/`cand2`), the Pareto dominance (`ord`), and eight
     one-line arithmetic facts about them;
  2. the specification (`suffixSum`/`subSum`) and its generator characterisation
     (`gen_sound`/`spec_gen`) — the genuinely problem-specific inductions saying the search
     space is exactly the set of subarray sums.

  `solve_correct` and the §7.5 headline `solve_eq_maxRel` then fall out of the drivers.
  Axioms: {propext, Classical.choice, Quot.sound}, as in `L53.lean`.
-/
import Fredy.AutoDerive

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC53A

open Freyd Freyd.Alg.RelSet.SL

/-! ## 1. The creative bundle — the whole algorithmic content of Kadane -/

/-- Kadane's derivation bundle.  State `(bestEndingHere, bestSoFar)`: the new suffix is `p` or
    `e + p` (candidates), deterministically their max; the new best is kept or reset to the
    chosen new suffix, deterministically the max; Pareto dominance is `≥` in both coordinates. -/
def kadane : RunningBest Int Int Int where
  base x := (x, x)
  step1 e p := imax p (e + p)
  step2 e b p := imax b (imax p (e + p))
  cand1 e p w1 := w1 = p ∨ w1 = e + p
  cand2 _ b _ w1 w2 := w2 = b ∨ w2 = w1
  ord e e' := e' ≤ e
  ord_refl e := Int.le_refl e
  ord_trans h1 h2 := Int.le_trans h2 h1
  step1_mono p h := imax_mono (Int.le_refl p) (by omega)
  step2_mono p h1 h2 := imax_mono h2 (imax_mono (Int.le_refl p) (by omega))
  step1_cand e p := imax_eq_or p (e + p)
  step2_cand e b p := imax_eq_or b (imax p (e + p))
  cand1_le h := by
    rcases h with h | h <;> rw [h]
    · exact imax_ge_left _ _
    · exact imax_ge_right _ _
  cand2_le h1 h2 := by
    rcases h2 with h | h <;> rw [h]
    · exact imax_ge_left _ _
    · rcases h1 with h1 | h1 <;> rw [h1]
      · exact Int.le_trans (imax_ge_left _ _) (imax_ge_right _ _)
      · exact Int.le_trans (imax_ge_right _ _) (imax_ge_right _ _)

/-! ## 2. The specification and its generator characterisation (problem-specific inductions) -/

/-- `suffixSum xs v` — `v` is the sum of some non-empty SUFFIX of `xs`. -/
def suffixSum : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = x
  | SnocList.snoc xs p => fun v => v = p ∨ ∃ v', suffixSum xs v' ∧ v = v' + p

/-- `subSum xs v` — `v` is the sum of SOME non-empty contiguous subarray of `xs`. -/
def subSum : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = x
  | SnocList.snoc xs p => fun v => subSum xs v ∨ suffixSum (SnocList.snoc xs p) v

/-- The specification as a morphism in `Rel(Set)`; LeetCode 53 asks for its `≤`-maximum. -/
def spec : dSL Int Int ⟶ (⟨Int⟩ : RelSet.{0}) := fun xs v => subSum xs v

/-- **Soundness**: every generatable pair is a (suffix sum, subarray sum) pair. -/
theorem gen_sound : ∀ (xs : SnocList Int Int) (w : Int × Int),
    cataFold kadane.gen xs w → suffixSum xs w.1 ∧ subSum xs w.2 := by
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

/-- **Completeness (diagonal)**: a suffix sum `v` is generatable as the pair `(v, v)`. -/
theorem diag_gen : ∀ (xs : SnocList Int Int) (v : Int),
    suffixSum xs v → cataFold kadane.gen xs (v, v) := by
  intro xs; induction xs with
  | wrap x => intro v hv; have hvx : v = x := hv; show (v, v) = (x, x); rw [hvx]
  | snoc xs p ih =>
    intro v hv
    simp only [suffixSum] at hv
    rcases hv with h1 | ⟨v', hv', hveq⟩
    · obtain ⟨w', hw'⟩ := kadane.gen_total xs
      exact ⟨w', hw', Or.inl h1, Or.inr rfl⟩
    · exact ⟨(v', v'), ih v' hv', Or.inr (by rw [hveq]), Or.inr rfl⟩

/-- **Completeness**: every subarray sum is the best-component of some generatable pair. -/
theorem spec_gen : ∀ (xs : SnocList Int Int) (v : Int),
    subSum xs v → ∃ e, cataFold kadane.gen xs (e, v) := by
  intro xs; induction xs with
  | wrap x => intro v hv; have hvx : v = x := hv; exact ⟨x, show (x, v) = (x, x) by rw [hvx]⟩
  | snoc xs p ih =>
    intro v hv
    simp only [subSum] at hv
    rcases hv with h1 | h2
    · obtain ⟨e', he'⟩ := ih v h1
      exact ⟨p, (e', v), he', Or.inl rfl, Or.inl rfl⟩
    · exact ⟨v, diag_gen (SnocList.snoc xs p) v h2⟩

/-! ## 3. The auto-derived correctness -/

/-- **The allegory program**: Kadane as a morphism `Arr ⟶ ℤ` in `Rel(Set)` — the second
    component of the `RunningBest` fold. -/
def solve : dSL Int Int ⟶ (⟨Int⟩ : RelSet.{0}) := graph (fun xs => (kadane.foldFn xs).2)

/-- **Correctness, auto-derived**: `solve xs` is an achievable subarray sum and dominates every
    achievable subarray sum — `RunningBest.correct` with only the spec characterisation
    supplied. -/
theorem solve_correct (xs : SnocList Int Int) :
    subSum xs (kadane.foldFn xs).2 ∧ ∀ v, subSum xs v → v ≤ (kadane.foldFn xs).2 :=
  kadane.correct spec (fun xs w h => (gen_sound xs w h).2) spec_gen xs

/-- **The §7.5 headline, auto-derived**: `solve = max (≤) · Λ spec` as a morphism equation. -/
theorem solve_eq_maxRel : solve = A spec ≫ maxRel (fun w z : Int => z ≤ w) :=
  kadane.eq_maxRel spec (fun xs w h => (gen_sound xs w h).2) spec_gen

/-- The program is a catamorphism followed by the best-projection (presentation lemma). -/
theorem solve_eq_cata : solve = cataR kadane.alg ≫ graph (Prod.snd : Int × Int → Int) :=
  kadane.solve_eq_cata

/-! ## Running the program -/

/-- Build an array from a first element and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : (kadane.foldFn (ofList (-2) [1, -3, 4, -1, 2, 1, -5, 4])).2 = 6 := by decide
example : (kadane.foldFn (ofList (-1) [])).2 = -1 := by decide
example : (kadane.foldFn (ofList 1 [2, 3])).2 = 6 := by decide
example : (kadane.foldFn (ofList (-3) [-1, -2])).2 = -1 := by decide

end Freyd.Alg.RelSet.LC53A
