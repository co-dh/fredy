/-
  LeetCode 303 — Range Sum Query - Immutable — as an ALLEGORY PROGRAM.

  Problem: given a fixed `nums : List Int`, answer many `sumRange i j = nums[i] + … + nums[j]`
  queries. Precompute prefix sums once (`O(n)`), answer each query in `O(1)` via a subtraction.

  1. **Data** — a plain `List Int` paired with the two query indices `(nums, i, j)`. No `SnocList`
     machinery needed (as in `L238`); the answer object is `Int`.

  2. **Program** — `prefixSums nums` is the SCAN `[0, nums[0], nums[0]+nums[1], …]` (length
     `nums.length + 1`, `P 0 = 0`, `P k = nums[0]+…+nums[k-1]`), built by `scanlAdd` — plain
     single-argument structural recursion on `nums` (no fuel, cf. `L238`'s `preScan`).
     `sumRangeFn nums i j := P(j+1) − P(i)`, read off the precomputed list via `List.getElem?`.

  3. **Specification** — the HONEST slice sum, via a `take`/`drop` split (no reference to the
     program's own prefix-sum machinery): `rangeSum nums i j := ((nums.drop i).take (j+1-i)).sum`.

  4. **Correctness** — the crux is TWO structural-induction lemmas, both index-explicit (the `L238`
     `preScan_get?`/S10 move): `scanlAdd_get?` (`P` read off at any in-range index equals the
     `take`-sum, carrying the running accumulator through the induction) and
     `take_eq_take_append_drop_take` (the telescoping list identity `nums.take k = nums.take i ++
     (nums.drop i).take (k−i)` for `i ≤ k`, which Lean core does NOT provide — only the `i=1` step
     `take_add_one` and the Nat-specialised `sum_append_nat` exist). Combining them: `P(j+1) − P(i)
     = (nums.take (j+1)).sum − (nums.take i).sum = ((nums.take i).sum + (slice).sum) −
     (nums.take i).sum = (slice).sum = rangeSum nums i j`.

  Mathlib-free; `sum_append_int` (Lean core only proves `sum_append` for `List Nat`) and the
  telescoping split are both hand-rolled here. Axioms `⊆ {propext, Quot.sound}` — fully
  constructive, no `Classical.choice` (a straight `graph`/`Map` packaging, like `L238`).
-/
import AOP.A6_1_RelSet

namespace Freyd.Alg.RelSet.LC303

open Freyd

/-! ## Mathlib-free `Int` list-sum lemma (core only proves `sum_append` for `List Nat`) -/

theorem sum_append_int (l1 l2 : List Int) : (l1 ++ l2).sum = l1.sum + l2.sum := by
  induction l1 with
  | nil => simp
  | cons x xs ih => rw [List.cons_append, List.sum_cons, List.sum_cons, ih, Int.add_assoc]

/-! ## The telescoping take/drop split (core has no `i ≤ k` generalisation of `take_add_one`) -/

/-- `nums.take k` splits at any `i ≤ k` into its own prefix and the corresponding slice of the
    remainder — the list-level fact underlying prefix-sum telescoping. -/
theorem take_eq_take_append_drop_take (nums : List Int) (i k : Nat) (h : i ≤ k) :
    nums.take k = nums.take i ++ (nums.drop i).take (k - i) := by
  induction nums generalizing i k with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i' =>
      cases k with
      | zero => omega
      | succ k' =>
        have hik' : i' ≤ k' := by omega
        have hsub : (k' + 1) - (i' + 1) = k' - i' := by omega
        rw [List.take_succ_cons, List.take_succ_cons, List.drop_succ_cons, hsub,
          List.cons_append, ih i' k' hik']

/-! ## Data & answer object -/

/-- The object of `(nums, i, j)` queries in `Rel(Set)`. -/
abbrev Query : RelSet.{0} := ⟨List Int × Nat × Nat⟩
/-- The object of integer answers in `Rel(Set)`. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-! ## The program: precompute prefix sums, answer by subtraction -/

/-- `scanlAdd a (x :: xs) = a :: scanlAdd (a + x) xs`: emit the running total `a`, then fold `x`
    into it before recursing — the same accumulator-threaded-DOWN shape as `L238`'s `preScan`. -/
def scanlAdd (a : Int) : List Int → List Int
  | [] => [a]
  | x :: xs => a :: scanlAdd (a + x) xs

@[simp] theorem scanlAdd_nil (a : Int) : scanlAdd a ([] : List Int) = [a] := rfl
@[simp] theorem scanlAdd_cons (a x : Int) (xs : List Int) :
    scanlAdd a (x :: xs) = a :: scanlAdd (a + x) xs := rfl

/-- The prefix-sum list: `P = prefixSums nums` has `P.length = nums.length + 1`, `P 0 = 0`,
    `P k = nums[0] + … + nums[k-1]`. -/
def prefixSums (nums : List Int) : List Int := scanlAdd 0 nums

/-- **The program's underlying function**: `O(1)` query via two lookups into the precomputed
    prefix sums, `.getD 0` guarding out-of-range indices (never hit at a valid query). -/
def sumRangeFn (nums : List Int) (i j : Nat) : Int :=
  ((prefixSums nums)[j + 1]?.getD 0) - ((prefixSums nums)[i]?.getD 0)

/-! ## The specification: the honest slice sum -/

/-- **The spec**: the actual sum of `nums[i..j]`, via a `drop`/`take` slice — no reference to the
    program's own prefix-sum machinery. -/
def rangeSum (nums : List Int) (i j : Nat) : Int := ((nums.drop i).take (j + 1 - i)).sum

/-! ## Correctness — the crux: strengthen the scan to an EXPLICIT per-index formula (S10) -/

/-- `scanlAdd a nums` at any in-range index `k ≤ nums.length` equals `a` plus the sum of `nums`'s
    first `k` elements — carrying the accumulator `a` through the induction. -/
theorem scanlAdd_get? (a : Int) (nums : List Int) (k : Nat) (hk : k ≤ nums.length) :
    (scanlAdd a nums)[k]? = some (a + (nums.take k).sum) := by
  induction nums generalizing a k with
  | nil =>
    have hk0 : k = 0 := by simpa using hk
    subst hk0; simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k' =>
      have hk' : k' ≤ xs.length := by rw [List.length_cons] at hk; omega
      rw [scanlAdd_cons, List.getElem?_cons_succ, ih (a + x) k' hk', List.take_succ_cons,
        List.sum_cons]
      congr 1; omega

/-- `prefixSums nums` at any in-range index `k ≤ nums.length` equals `nums`'s first `k` elements'
    sum — `scanlAdd_get?` specialised to `a = 0`. -/
theorem prefixSums_get? (nums : List Int) (k : Nat) (hk : k ≤ nums.length) :
    (prefixSums nums)[k]? = some ((nums.take k).sum) := by
  have h := scanlAdd_get? 0 nums k hk
  rwa [Int.zero_add] at h

/-- **Correctness (headline)**: `sumRangeFn` computes the honest slice sum `nums[i..j]`, for any
    query with `i ≤ j + 1` (a well-formed range, possibly empty) and `j` in range. -/
theorem sumRange_correct (nums : List Int) (i j : Nat) (hij : i ≤ j + 1) (hj : j < nums.length) :
    sumRangeFn nums i j = rangeSum nums i j := by
  have hj1 : j + 1 ≤ nums.length := by omega
  have hi : i ≤ nums.length := by omega
  have e1 := prefixSums_get? nums (j + 1) hj1
  have e2 := prefixSums_get? nums i hi
  unfold sumRangeFn rangeSum
  rw [e1, e2, Option.getD_some, Option.getD_some,
    take_eq_take_append_drop_take nums i (j + 1) hij, sum_append_int]
  omega

/-! ## Packaging as a genuine `Rel(Set)` morphism -/

/-- **The allegory program**: LeetCode 303's solution as a morphism `Query ⟶ ℤ` in `Rel(Set)`. -/
def solve : Query ⟶ dZ := graph (fun t : List Int × Nat × Nat => sumRangeFn t.1 t.2.1 t.2.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map (fun t : List Int × Nat × Nat => sumRangeFn t.1 t.2.1 t.2.2)

/-- **The program computes the specification** (pointwise in `Rel(Set)`): whatever `solve` relates
    a well-formed query to is the honest slice sum. -/
theorem solve_correct (nums : List Int) (i j : Nat) (hij : i ≤ j + 1) (hj : j < nums.length)
    (v : Int) (h : solve (nums, i, j) v) : v = rangeSum nums i j := by
  have hv : v = sumRangeFn nums i j := h
  rw [hv]; exact sumRange_correct nums i j hij hj

/-! ## Headline: on a well-formed range, `solve` IS `spec` (a genuine morphism equation) -/

/-- The **specification** as a morphism `Query ⟶ ℤ` in `Rel(Set)`: the answer is the honest slice
    sum `rangeSum` (a `drop`/`take` over the list), stated independently of the prefix-sum program. -/
def spec : Query ⟶ dZ := fun q v => v = rangeSum q.1 q.2.1 q.2.2

/-- The precondition coreflexive: the sub-identity on WELL-FORMED queries (`i ≤ j+1`, `j` in range). -/
def pre : Query ⟶ Query := fun q q' => q = q' ∧ q.2.1 ≤ q.2.2 + 1 ∧ q.2.2 < q.1.length

/-- **Preconditioned headline**: restricted to well-formed queries (`pre`), the program equals the
    specification — `pre ≫ solve = pre ≫ spec`.  The exact-value answer is pinned uniquely by the
    equation `v = rangeSum …`; `sumRange_correct` bridges the prefix-sum program to that honest sum. -/
theorem pre_solve_eq_spec : pre ≫ solve = pre ≫ spec := by
  apply hom_ext; intro q v
  rw [comp_apply, comp_apply]
  constructor
  · rintro ⟨q', ⟨rfl, hij, hj⟩, hsolve⟩
    refine ⟨q, ⟨rfl, hij, hj⟩, ?_⟩
    show v = rangeSum q.1 q.2.1 q.2.2
    rw [(hsolve : v = sumRangeFn q.1 q.2.1 q.2.2)]; exact sumRange_correct q.1 q.2.1 q.2.2 hij hj
  · rintro ⟨q', ⟨rfl, hij, hj⟩, hspec⟩
    refine ⟨q, ⟨rfl, hij, hj⟩, ?_⟩
    show v = sumRangeFn q.1 q.2.1 q.2.2
    rw [(hspec : v = rangeSum q.1 q.2.1 q.2.2)]; exact (sumRange_correct q.1 q.2.1 q.2.2 hij hj).symm

/-! ## Running the program -/

-- LeetCode 303's own example: `nums = [-2, 0, 3, -5, 2, -1]`, `sumRange(0,2) = 1`,
-- `sumRange(2,5) = -1`.
example : sumRangeFn [-2, 0, 3, -5, 2, -1] 0 2 = 1 := by decide
example : sumRangeFn [-2, 0, 3, -5, 2, -1] 2 5 = -1 := by decide

end Freyd.Alg.RelSet.LC303
