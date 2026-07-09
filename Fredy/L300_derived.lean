/-
  LeetCode 300 — Longest Increasing Subsequence — DERIVED as an O(n log n) PATIENCE-SORTING fold.

  `Fredy/L300.lean` writes an O(n²) tabulating DP by hand (state `(records, best)` where `records`
  is the UNBOUNDED history of `(value, LIS-length-ending-here)` pairs, and every step SCANS the whole
  history via `bestBelow`).  This file replaces it with the classic **patience sorting** algorithm,
  which runs in O(n log n): carry a single strictly-increasing array `tails : Array Int` where
  `tails[k]` is the SMALLEST possible last element of a strictly-increasing subsequence of length
  `k+1`.  Processing a new element `x` is ONE binary search (`lowerBound`, the first `tails[i] ≥ x`)
  followed by ONE point write (`insertOrReplace`: overwrite `tails[i]` with `x`, or append `x` when
  it exceeds every tail).  The answer is `tails.size`.  Each step is O(log n) (binary search) + O(1)
  (point write) ⇒ O(n log n) total.

  Two ingredients:

  1. **The program EMERGES from the fold law.**  The `tails` fold is a catamorphism with carrier
     `Array Int`: base `g x = #[x]`, step `st tails x = insertOrReplace tails x`.  Feeding these to
     the general-carrier law `Freyd.Alg.RelSet.SL.snocFold_unique` (`Fredy/A6_GenFold.lean`) produces
     the fold as `cataR (scalarAlg g st)` — we never write the recursion; `tails_emerges` is the law's
     catamorphism.  `insertOrReplace_strictSorted` keeps `StrictSorted` along the fold.

  2. **Correctness is a GENUINE new proof** (patience sorting is NOT the O(n²) DP, so nothing is
     reused verbatim from the fold).  The patience invariant `PatInv`, proved by induction:
        * `StrictSorted tails`;
        * `(I1)` every `tails[k]` is the end of a strictly-increasing subsequence of length `k+1`
          (`anyEnd`); and
        * `(I2)` any strictly-increasing subsequence of length `k` ending at `v` has `k ≤ tails.size`
          AND `tails[k-1] ≤ v` (the min-last-element-per-length property — the new content).
     From the invariant: `tails.size` is achievable (`patience_achievable`) and dominates every
     achievable length (`patience_dominates`), so it is the LIS length.  We ALSO bridge to the
     O(n²) solver: `size_eq_solveFn : (tailsFold xs).size = LC300.solveFn xs` (the two programs agree,
     via `LC300.solve_correct`).  The `anyEnd`/`isSubseqInc` SPEC is reused from `L300.lean`; the
     patience min-per-length argument is proved here.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.A6_BinSearch
import Fredy.L300

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC300D

open Freyd Freyd.Alg.RelSet.SL Freyd.BinSearch

/-! ## The patience-sorting fold: carrier `Array Int`, base `#[x]`, step `insertOrReplace` -/

/-- Base of the emergent algebra: a length-one tails array. -/
def g : Int → Array Int := fun x => #[x]

/-- Step of the emergent algebra: one binary search + one point write. -/
def st : Array Int → Int → Array Int := fun t x => insertOrReplace t x

/-- The patience-sorting fold (structural recursion), carrier `Array Int`.  `tailsFold xs` is the
    tails array after processing the whole array `xs` left to right. -/
def tailsFold : SnocList Int Int → Array Int
  | SnocList.wrap x => #[x]
  | SnocList.snoc xs x => insertOrReplace (tailsFold xs) x

/-- Base condition (`rfl`): `tailsFold (wrap x) = g x`. -/
theorem tailsFold_wrap (x : Int) : tailsFold (SnocList.wrap x) = g x := rfl

/-- Step condition (`rfl`): `tailsFold (snoc xs x) = st (tailsFold xs) x`. -/
theorem tailsFold_snoc (xs : SnocList Int Int) (x : Int) :
    tailsFold (SnocList.snoc xs x) = st (tailsFold xs) x := rfl

/-- The tails array is always non-empty (`wrap` gives size 1, `insertOrReplace` never shrinks). -/
theorem tailsFold_size_pos : ∀ xs : SnocList Int Int, 1 ≤ (tailsFold xs).size := by
  intro xs
  induction xs with
  | wrap x => exact Nat.le_refl 1
  | snoc xs p ih => exact Nat.le_trans ih (le_insertOrReplace_size (tailsFold xs) p)

/-! ## Two small facts about the spec `anyEnd` and about `lowerBound` -/

/-- Every achievable increasing-subsequence length is `≥ 1` (subsequences here are non-empty). -/
theorem anyEnd_ge_one : ∀ (xs : SnocList Int Int) (v : Int) (k : Nat),
    LC300.anyEnd xs v k → 1 ≤ k := by
  intro xs
  induction xs with
  | wrap x => intro v k h; obtain ⟨_, hk⟩ := h; omega
  | snoc xs p ih =>
    intro v k h
    rcases h with h | ⟨_, hcase⟩
    · exact ih v k h
    · rcases hcase with hk1 | ⟨_, k', _, _, hkeq⟩
      · omega
      · omega

/-- On a strictly-sorted array, an element strictly below `x` sits strictly left of `lowerBound x`.
    (The converse of the `lowerBound` spec, used to bound recorded lengths by the search position.) -/
theorem lt_lowerBound_of_lt {t : Array Int} {x : Int} (hs : StrictSorted t)
    {j : Nat} (hj : j < t.size) (hjx : t[j]'hj < x) : j < lowerBound t x := by
  rcases Nat.lt_or_ge j (lowerBound t x) with h | h
  · exact h
  · exfalso
    have hlb : lowerBound t x < t.size := Nat.lt_of_le_of_lt h hj
    have h1 := le_of_lowerBound_le hs.sorted hlb
    have h2 := hs.sorted.le_of_le h hj
    omega

/-- Two accesses of the same array at equal indices give the same element (proof-irrelevant). -/
theorem getElem_idx {t : Array Int} {i j : Nat} (hi : i < t.size) (hj : j < t.size)
    (h : i = j) : t[i]'hi = t[j]'hj := by subst h; rfl

/-! ## The patience invariant

  `PatInv xs t` bundles the three facts that make `t = tails after processing xs` correct:
  `t` is strictly increasing; every `t[k]` ends an increasing subsequence of length `k+1` (I1);
  and every increasing subsequence of length `k` ending at `v` has `k ≤ t.size` and `t[k-1] ≤ v`
  (I2 — domination plus the min-last-element-per-length property). -/
def PatInv (xs : SnocList Int Int) (t : Array Int) : Prop :=
  StrictSorted t ∧
  (∀ k (hk : k < t.size), LC300.anyEnd xs (t[k]'hk) (k + 1)) ∧
  (∀ v k, LC300.anyEnd xs v k →
      k ≤ t.size ∧ ∀ (hk : k - 1 < t.size), t[k - 1]'hk ≤ v)

/-- **The inductive step.**  If `t` is the patience invariant for `xs`, then `insertOrReplace t p`
    is the patience invariant for `snoc xs p`.  This is the heart of patience-sorting correctness:
    the binary-search position `lowerBound t p` is exactly the length-index whose minimum last
    element `p` can lower, and it is one past the longest subsequence `p` can extend. -/
theorem patInv_step (xs : SnocList Int Int) (p : Int) (t : Array Int)
    (hpos : 1 ≤ t.size) (hinv : PatInv xs t) :
    PatInv (SnocList.snoc xs p) (insertOrReplace t p) := by
  obtain ⟨hss, hI1, hI2⟩ := hinv
  rcases Nat.lt_or_ge (lowerBound t p) t.size with hlt | hge
  · -- REPLACE branch: overwrite `t[lowerBound t p]` with `p`
    have he : insertOrReplace t p = t.set (lowerBound t p) p hlt := by
      unfold insertOrReplace; rw [dif_pos hlt]
    rw [he]
    refine ⟨he ▸ insertOrReplace_strictSorted hss, ?_, ?_⟩
    · -- I1
      intro k hk
      rw [Array.size_set] at hk
      rw [Array.getElem_set hlt]
      by_cases hik : lowerBound t p = k
      · rw [if_pos hik]
        refine (LC300.anyEnd_snoc xs p p (k + 1)).mpr (Or.inr ⟨rfl, ?_⟩)
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · exact Or.inl (by omega)
        · right
          have hprev : k - 1 < t.size := by omega
          refine ⟨t[k - 1]'hprev, k, ?_, ?_, rfl⟩
          · have h := hI1 (k - 1) hprev
            have he2 : k - 1 + 1 = k := by omega
            rw [he2] at h; exact h
          · have hjlt : k - 1 < lowerBound t p := by omega
            exact lt_of_lt_lowerBound hss.sorted (k - 1) hjlt hprev
      · rw [if_neg hik]
        exact (LC300.anyEnd_snoc xs p _ _).mpr (Or.inl (hI1 k hk))
    · -- I2
      intro v k hany
      rcases hany with hprefix | ⟨hv, hcase⟩
      · obtain ⟨hdom, hmin⟩ := hI2 v k hprefix
        refine ⟨by rw [Array.size_set]; exact hdom, ?_⟩
        intro hk
        rw [Array.size_set] at hk
        rw [Array.getElem_set hlt]
        by_cases hik : lowerBound t p = k - 1
        · rw [if_pos hik]
          have hval : t[lowerBound t p]'hlt = t[k - 1]'hk := getElem_idx hlt hk hik
          have h1 := le_of_lowerBound_le hss.sorted hlt
          have h2 := hmin hk
          omega
        · rw [if_neg hik]; exact hmin hk
      · subst v
        rcases hcase with hk1 | ⟨v', k', hany', hv'p, hkeq⟩
        · -- new subsequence has length 1
          refine ⟨by rw [Array.size_set]; omega, ?_⟩
          intro hk
          rw [Array.size_set] at hk
          rw [Array.getElem_set hlt]
          by_cases hi00 : lowerBound t p = k - 1
          · rw [if_pos hi00]; exact Int.le_refl p
          · rw [if_neg hi00]
            have hjlt : k - 1 < lowerBound t p := by omega
            have := lt_of_lt_lowerBound hss.sorted (k - 1) hjlt hk
            omega
        · -- new subsequence extends one ending below `p`
          obtain ⟨hdom', hmin'⟩ := hI2 v' k' hany'
          have hk'pos : 1 ≤ k' := anyEnd_ge_one xs v' k' hany'
          have hprev' : k' - 1 < t.size := by omega
          have hmv := hmin' hprev'
          have hlt_p : t[k' - 1]'hprev' < p := by omega
          have hk'lt : k' - 1 < lowerBound t p := lt_lowerBound_of_lt hss hprev' hlt_p
          refine ⟨by rw [Array.size_set]; omega, ?_⟩
          intro hk
          rw [Array.size_set] at hk
          rw [Array.getElem_set hlt]
          by_cases hik : lowerBound t p = k - 1
          · rw [if_pos hik]; exact Int.le_refl p
          · rw [if_neg hik]
            have hklb : k - 1 < lowerBound t p := by omega
            have := lt_of_lt_lowerBound hss.sorted (k - 1) hklb hk
            omega
  · -- APPEND branch: `p` exceeds every tail, push it
    have heq : lowerBound t p = t.size := Nat.le_antisymm (lowerBound_le_size t p) hge
    have he : insertOrReplace t p = t.push p := by
      unfold insertOrReplace; rw [dif_neg (Nat.not_lt.mpr hge)]
    have hall : ∀ j (hj : j < t.size), t[j]'hj < p :=
      (lowerBound_eq_size_iff hss.sorted).1 heq
    rw [he]
    refine ⟨he ▸ insertOrReplace_strictSorted hss, ?_, ?_⟩
    · -- I1
      intro k hk
      rw [Array.size_push] at hk
      rw [Array.getElem_push]
      by_cases hks : k < t.size
      · rw [dif_pos hks]
        exact (LC300.anyEnd_snoc xs p _ _).mpr (Or.inl (hI1 k hks))
      · rw [dif_neg hks]
        have hprev : k - 1 < t.size := by omega
        refine (LC300.anyEnd_snoc xs p p (k + 1)).mpr (Or.inr ⟨rfl, ?_⟩)
        right
        refine ⟨t[k - 1]'hprev, k, ?_, ?_, rfl⟩
        · have h := hI1 (k - 1) hprev
          have he2 : k - 1 + 1 = k := by omega
          rw [he2] at h; exact h
        · exact hall (k - 1) hprev
    · -- I2
      intro v k hany
      rcases hany with hprefix | ⟨hv, hcase⟩
      · obtain ⟨hdom, hmin⟩ := hI2 v k hprefix
        refine ⟨by rw [Array.size_push]; omega, ?_⟩
        intro hk
        rw [Array.size_push] at hk
        rw [Array.getElem_push]
        by_cases hks : k - 1 < t.size
        · rw [dif_pos hks]; exact hmin hks
        · rw [dif_neg hks]; exfalso; omega
      · subst v
        rcases hcase with hk1 | ⟨v', k', hany', hv'p, hkeq⟩
        · refine ⟨by rw [Array.size_push]; omega, ?_⟩
          intro hk
          rw [Array.size_push] at hk
          rw [Array.getElem_push]
          by_cases hks : k - 1 < t.size
          · rw [dif_pos hks]
            have := hall (k - 1) hks
            omega
          · rw [dif_neg hks]; exfalso; omega
        · obtain ⟨hdom', hmin'⟩ := hI2 v' k' hany'
          refine ⟨by rw [Array.size_push]; omega, ?_⟩
          intro hk
          rw [Array.size_push] at hk
          rw [Array.getElem_push]
          by_cases hks : k - 1 < t.size
          · rw [dif_pos hks]
            have := hall (k - 1) hks
            omega
          · rw [dif_neg hks]; exact Int.le_refl p

/-- The patience invariant holds after processing any array (base: singleton; step: `patInv_step`). -/
theorem patInv : ∀ xs : SnocList Int Int, PatInv xs (tailsFold xs) := by
  intro xs
  induction xs with
  | wrap x =>
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij hj
      exfalso
      have hj1 : j < 1 := hj
      omega
    · intro k hk
      have hk1 : k < 1 := hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨rfl, rfl⟩
    · intro v k hany
      obtain ⟨hvx, hkk⟩ := hany
      subst hkk
      refine ⟨Nat.le_refl 1, ?_⟩
      intro hk
      rw [hvx]
      exact Int.le_refl x
  | snoc xs p ih =>
    exact patInv_step xs p (tailsFold xs) (tailsFold_size_pos xs) ih

/-! ## Correctness of the patience answer `tails.size` -/

/-- `tails.size` is itself an achievable increasing-subsequence length (I1 at the top index). -/
theorem patience_achievable (xs : SnocList Int Int) :
    LC300.isSubseqInc xs (tailsFold xs).size := by
  obtain ⟨hss, hI1, hI2⟩ := patInv xs
  have hpos := tailsFold_size_pos xs
  have hlt : (tailsFold xs).size - 1 < (tailsFold xs).size := by omega
  have h := hI1 ((tailsFold xs).size - 1) hlt
  have he : (tailsFold xs).size - 1 + 1 = (tailsFold xs).size := by omega
  rw [he] at h
  exact ⟨(tailsFold xs)[(tailsFold xs).size - 1]'hlt, h⟩

/-- `tails.size` dominates every achievable increasing-subsequence length (I2 domination). -/
theorem patience_dominates (xs : SnocList Int Int) (k : Nat) (h : LC300.isSubseqInc xs k) :
    k ≤ (tailsFold xs).size := by
  obtain ⟨hss, hI1, hI2⟩ := patInv xs
  obtain ⟨v, hv⟩ := h
  exact (hI2 v k hv).1

/-- **The two programs agree.**  The O(n log n) patience answer equals the O(n²) DP answer of
    `L300.lean` — both are the LIS length.  (`tails.size` is achievable and dominates, so it is the
    `≤`-maximum, which `LC300.solve_correct` says is `solveFn`.) -/
theorem size_eq_solveFn (xs : SnocList Int Int) : (tailsFold xs).size = LC300.solveFn xs := by
  have h1 : (tailsFold xs).size ≤ LC300.solveFn xs :=
    (LC300.solve_correct xs).2 _ (patience_achievable xs)
  have h2 : LC300.solveFn xs ≤ (tailsFold xs).size :=
    patience_dominates xs _ (LC300.solve_correct xs).1
  omega

/-! ## The program EMERGES from the general-carrier fold law -/

/-- **The derivation.**  The patience fold is PRODUCED by `snocFold_unique` from the base `g` and
    step `st`; `graph tailsFold` equals the catamorphism of the emergent scalar algebra.  The step
    `st = insertOrReplace` is one binary search plus one point write. -/
theorem tails_emerges :
    (graph tailsFold : dSL Int Int ⟶ ⟨Array Int⟩) = cataR (scalarAlg g st) :=
  SL.snocFold_unique g st tailsFold tailsFold_wrap tailsFold_snoc

/-- The derived allegory program: the emergent patience fold followed by `.size`. -/
def derivedSolve : LC300.Arr ⟶ LC300.dNat :=
  cataR (scalarAlg g st) ≫ graph (fun t : Array Int => t.size)

/-- `derivedSolve` relates `xs` to exactly `(tailsFold xs).size`. -/
theorem derivedSolve_iff (xs : SnocList Int Int) (m : Nat) :
    derivedSolve xs m ↔ m = (tailsFold xs).size := by
  show (cataR (scalarAlg g st) ≫ graph (fun t : Array Int => t.size)) xs m ↔ _
  rw [← tails_emerges]
  show (∃ t, t = tailsFold xs ∧ m = t.size) ↔ m = (tailsFold xs).size
  constructor
  · rintro ⟨t, ht, hm⟩; rw [ht] at hm; exact hm
  · intro hm; exact ⟨tailsFold xs, rfl, hm⟩

/-! ## Headline correctness -/

/-- **Headline.**  The O(n log n) patience-sorting fold `derivedSolve` computes the LIS optimum:
    it relates each array `xs` to a value `m` that is an achievable increasing-subsequence length
    (`isSubseqInc`) and dominates every achievable increasing-subsequence length — the `≤`-maximum
    `max (≤) · Λ isSubseqInc`.  Here `m = (tailsFold xs).size` is produced by one binary search
    (`lowerBound`) and one point write (`insertOrReplace`) per element. -/
theorem lis_derived_correct (xs : SnocList Int Int) :
    ∃ m, derivedSolve xs m ∧ LC300.isSubseqInc xs m ∧ ∀ k, LC300.isSubseqInc xs k → k ≤ m :=
  ⟨(tailsFold xs).size, (derivedSolve_iff xs _).mpr rfl,
   patience_achievable xs, patience_dominates xs⟩

/-! ## Running / cross-checking the patience fold

  `#guard` evaluates the compiled `tailsFold` (its `insertOrReplace`/`lowerBound` use well-founded
  recursion, so they run but do not `decide`-reduce in the kernel), cross-checking the patience
  `tails.size` against the LIS length.  The scalar answers also `decide` on the kernel-reducible
  `LC300.solveFn` (equal to `tails.size` by `size_eq_solveFn`). -/

#guard (tailsFold (LC300.ofList 10 [9, 2, 5, 3, 7, 101, 18])).size = 4
#guard (tailsFold (LC300.ofList 0 [1, 0, 3, 2, 3])).size = 4
#guard (tailsFold (LC300.ofList 7 [7, 7, 7, 7, 7, 7])).size = 1

example : LC300.solveFn (LC300.ofList 10 [9, 2, 5, 3, 7, 101, 18]) = 4 := by decide
example : LC300.solveFn (LC300.ofList 0 [1, 0, 3, 2, 3]) = 4 := by decide
example : LC300.solveFn (LC300.ofList 7 [7, 7, 7, 7, 7, 7]) = 1 := by decide

end Freyd.Alg.RelSet.LC300D
