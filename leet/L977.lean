/-
  LeetCode 977 — Squares of a Sorted Array — as an ALLEGORY PROGRAM.

  Problem: given a `.`-sorted `xs : List Int` (may contain negatives), return the sorted list of
  the squares.

  Same recipe as `leet/L56.lean`/`leet/L242.lean` (`Freyd/leetcode.md` S0/S22/S24/S28): the data
  object is a plain `List Int` (no `SnocList` engine needed — a one-shot map+sort, not a scan).
  The clean allegory route is NOT the O(n) two-pointer merge; it is "square then sort", reusing
  `leet.L242`'s hand-rolled insertion sort verbatim (as `L128`'s `longestConsecFn` already reuses
  it) — the campaign proves CORRECTNESS, not complexity (cf. `L57`/S26).

  1. **Program** — `sortedSquaresFn xs := LC242.isort (xs.map (fun a => a * a))`.

  2. **Specification** — honesty here has TWO independent clauses, neither implying the other:
     - **sorted**: `LC242.Sorted (sortedSquaresFn xs)` — directly `LC242.isort_sorted _`.
     - **exactly the squares (as a multiset)**: `∀ v, LC242.countL (sortedSquaresFn xs) v =
       LC242.countL (xs.map (fun a => a * a)) v` — nothing added, nothing dropped, via
       `LC242.countL_isort`. This is the honest content: `isort`'s SORTEDNESS alone says nothing
       about which elements are present; the count-preservation clause is what pins the output
       down to "a permutation of the squared inputs".

  3. **Correctness** — `squares_correct` bundles both clauses. No `Sorted xs` hypothesis: the
     square-then-sort program is correct for ANY input list, sorted or not; the LeetCode
     precondition (input sorted) is irrelevant to this route (`L977`'s `.`-sortedness is only used
     by the O(n) two-pointer algorithm, which this file does not take).

  Mathlib-free; axioms ⊆ {propext, Quot.sound} (inherited from `L242`'s `isort_sorted`/
  `countL_isort`, both already at that budget).
-/
import leet.L242

namespace Freyd.Alg.RelSet.LC977

open Freyd
open Freyd.Alg.RelSet.LC242 (isort Sorted countL isort_sorted countL_isort)

/-! ## Data: plain integer lists (input and output) -/

/-- The object of integer lists in `Rel(Set)` (both the input and the output object). -/
abbrev Lst : RelSet.{0} := ⟨List Int⟩

/-! ## The program: square every element, then sort (reusing `L242.isort` verbatim) -/

/-- The answer function: square every element, then sort — reusing `LC242.isort` (S22/S24/S28's
    "reuse `L242`'s concrete sort" template, extended from `L56`/`L128`). -/
def sortedSquaresFn (xs : List Int) : List Int := isort (xs.map (fun a => a * a))

/-- **The allegory program**: LeetCode 977's solution as a morphism `Lst ⟶ Lst` in `Rel(Set)`. -/
def solve : Lst ⟶ Lst := graph sortedSquaresFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map sortedSquaresFn

/-! ## Correctness: the output is sorted AND is exactly the multiset of squared inputs -/

/-- **`sortedSquaresFn` is honest**: its output is sorted, and its count function agrees with the
    count function of the squared inputs at every value — i.e. it is exactly the sorted list of
    squares, nothing added or dropped. Holds for ANY input list (no `Sorted xs` hypothesis; the
    LeetCode input-sortedness precondition is irrelevant to this square-then-sort route). -/
theorem squares_correct (xs : List Int) :
    Sorted (sortedSquaresFn xs) ∧
      ∀ v, countL (sortedSquaresFn xs) v = countL (xs.map (fun a => a * a)) v :=
  ⟨isort_sorted _, fun v => countL_isort _ v⟩

/-- **The program refines the specification** (pointwise in `Rel(Set)`): whatever `solve` relates
    an input list to is sorted and is exactly its squares. -/
theorem solve_correct (xs out : List Int) (h : solve xs out) :
    Sorted out ∧ ∀ v, countL out v = countL (xs.map (fun a => a * a)) v := by
  have hout : out = sortedSquaresFn xs := h
  rw [hout]; exact squares_correct xs

/-! ## Specification and the structural-output headline -/

/-- The **specification** as a morphism `Lst ⟶ Lst` in `Rel(Set)`: the output is sorted and its
    multiset is exactly the squared inputs.  Stated via `Sorted`/`countL` (program-independent), NOT
    via `sortedSquaresFn`.  No precondition: the square-then-sort route is correct for ANY input, so
    the LeetCode input-sortedness assumption is not needed. -/
def spec : Lst ⟶ Lst := fun xs out =>
  Sorted out ∧ ∀ v, countL out v = countL (xs.map (fun a => a * a)) v

/-- **`solve` equals `spec` as relations** — the STRUCTURAL-OUTPUT headline: existence
    (`squares_correct`) plus uniqueness (`LC242.sorted_eq_of_countL_eq`: a sorted list is pinned by
    its multiset) make the program exactly the sorted-squares relation. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro xs out
  show (out = sortedSquaresFn xs) ↔
      (Sorted out ∧ ∀ v, countL out v = countL (xs.map (fun a => a * a)) v)
  constructor
  · intro h; subst h; exact squares_correct xs
  · intro h
    obtain ⟨hS, hC⟩ := h
    obtain ⟨hSm, hCm⟩ := squares_correct xs
    exact LC242.sorted_eq_of_countL_eq out (sortedSquaresFn xs) hS hSm (fun x => by rw [hC x, hCm x])

/-! ## Running the program -/

example : sortedSquaresFn [-4, -1, 0, 3, 10] = [0, 1, 9, 16, 100] := by decide
example : sortedSquaresFn [-7, -3, 2, 3, 11] = [4, 9, 9, 49, 121] := by decide

end Freyd.Alg.RelSet.LC977
