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

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_SnocList
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

/-! ## Invariants of the fold -/

/-- The first fold component (`bestEndingHere`) dominates every suffix sum. -/
theorem foldFn_fst_dominates :
    ∀ (xs : SnocList Int Int) (v : Int), suffixSum xs v → v ≤ (foldFn xs).1 := by
  intro xs; induction xs with
  | wrap x => intro v h; simp only [suffixSum] at h; show v ≤ x; omega
  | snoc xs p ih =>
    intro v h; simp only [suffixSum] at h
    show v ≤ imax p ((foldFn xs).1 + p)
    have hge1 := imax_ge_left  p ((foldFn xs).1 + p)
    have hge2 := imax_ge_right p ((foldFn xs).1 + p)
    cases h with
    | inl hp => omega
    | inr h => obtain ⟨v', hv', hv⟩ := h; have := ih v' hv'; omega

/-- The first fold component (`bestEndingHere`) is itself a suffix sum. -/
theorem foldFn_fst_is_suffix : ∀ xs, suffixSum xs (foldFn xs).1 := by
  intro xs; induction xs with
  | wrap x => rfl
  | snoc xs p ih =>
    show suffixSum (SnocList.snoc xs p) (imax p ((foldFn xs).1 + p))
    simp only [suffixSum]
    cases imax_eq_or p ((foldFn xs).1 + p) with
    | inl he => exact Or.inl he
    | inr he => exact Or.inr ⟨(foldFn xs).1, ih, he⟩

/-! ## Correctness: `solve` computes the maximum achievable subarray sum -/

/-- `solve` dominates every achievable subarray sum. -/
theorem subSum_le_solve : ∀ (xs : SnocList Int Int) (v : Int), subSum xs v → v ≤ solveFn xs := by
  intro xs; induction xs with
  | wrap x =>
    intro v h; simp only [subSum] at h
    show v ≤ x; omega
  | snoc xs p ih =>
    intro v h; simp only [subSum] at h
    show v ≤ imax (foldFn xs).2 (imax p ((foldFn xs).1 + p))
    have hge1 := imax_ge_left (foldFn xs).2 (imax p ((foldFn xs).1 + p))
    cases h with
    | inl hp =>
      have hle : v ≤ (foldFn xs).2 := ih v hp
      omega
    | inr hp =>
      have hb : v ≤ imax p ((foldFn xs).1 + p) := foldFn_fst_dominates (SnocList.snoc xs p) v hp
      have hge2 := imax_ge_right (foldFn xs).2 (imax p ((foldFn xs).1 + p))
      omega

/-- `solve`'s output is an achievable subarray sum — hence `solve ⊑ spec`. -/
theorem solve_sub : ∀ xs, subSum xs (solveFn xs) := by
  intro xs; induction xs with
  | wrap x => rfl
  | snoc xs p ih =>
    show subSum (SnocList.snoc xs p) (imax (foldFn xs).2 (imax p ((foldFn xs).1 + p)))
    simp only [subSum]
    have ihs : subSum xs (foldFn xs).2 := ih
    cases imax_eq_or (foldFn xs).2 (imax p ((foldFn xs).1 + p)) with
    | inl he => rw [he]; exact Or.inl ihs
    | inr he =>
      rw [he]
      refine Or.inr ?_
      simp only [suffixSum]
      cases imax_eq_or p ((foldFn xs).1 + p) with
      | inl he2 => exact Or.inl he2
      | inr he2 => exact Or.inr ⟨(foldFn xs).1, foldFn_fst_is_suffix xs, he2⟩

/-- **The program refines the specification**: every value `solve` returns is an achievable
    subarray sum. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs v h => ?_)
  have hv : v = solveFn xs := h
  rw [hv]; exact solve_sub xs

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ spec`, pointwise in `Rel(Set)`):
    `solve xs` is an achievable subarray sum and is `≤`-greatest among all achievable subarray
    sums. -/
theorem solve_correct (xs : SnocList Int Int) :
    subSum xs (solveFn xs) ∧ ∀ v, subSum xs v → v ≤ solveFn xs :=
  ⟨solve_sub xs, subSum_le_solve xs⟩

/-! ## Running the program -/

/-- Build an array from a first element and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList (-2) [1, -3, 4, -1, 2, 1, -5, 4]) = 6 := by decide
example : solveFn (ofList (-1) []) = -1 := by decide
example : solveFn (ofList 1 [2, 3]) = 6 := by decide
example : solveFn (ofList (-3) [-1, -2]) = -1 := by decide

end Freyd.Alg.RelSet.LC53
