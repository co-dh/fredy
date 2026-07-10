/-
  LeetCode 21 — Merge Two Sorted Lists — DERIVED as a relational HYLOMORPHISM (O(m+n)).

  `leet/L21.lean` writes `mergeFn` as the textbook two-input merge: compare the two heads, take the
  smaller, recurse on the rest — a genuine recursion on BOTH lists at once, running in O(m+n).  A merge
  is NOT a single-list catamorphism: the old `_derived` route folded the FIRST list into a residual
  function `List Int → List Int` awaiting the second, which re-scans on every element and costs O(n·m).

  The right scheme for a divide-and-conquer / two-input recursion is the DUAL of the fold: a
  RECURSIVE COALGEBRA `c : S → L + E×S` whose unfolding is well-founded (here witnessed by the `Nat`
  measure `μ` = total remaining length, strictly dropping on every recursive step), re-folded with the
  algebra `[g, st]`.  `Hylo.hyloFold_unique` (`AOP/A6_GenHylo.lean`) is the uniqueness law: any
  function `h` obeying `h s = match c s with | inl l => g l | inr (e,s') => st e (h s')` IS the
  hylomorphism `hyloR c μ hdec g st`.

  Instantiation for merge:  `S := List Int × List Int`, `L := List Int`, `E := Int`, `C := List Int`.
    * coalgebra  `c (xs,ys)` — leaf `.inl ys` / `.inl xs` when either list is exhausted (the answer is
      the other list verbatim), else pop the smaller head as a `.inr` node (branch order matching
      `mergeFn` exactly);
    * measure    `μ (xs,ys) := xs.length + ys.length`, dropping by one on each `.inr` step (`hdec`);
    * algebra    base `g := id` (a leaf returns the surviving list unchanged), step `st := (· :: ·)`
      (cons the popped head onto the merged tail).

  `merge_emerges` runs `hyloFold_unique` on the hand-written `LC21.mergeFn`: it certifies that the
  O(m+n) program IS the relational hylomorphism of `c` — the program was never re-written, only shown
  to satisfy the hylomorphism recurrence (one case split, discharged in place — see `mergeFn_cons_eq`).
  Correctness (`LC21.solve_le_spec`: sortedness + exact multiset preservation) is REUSED from `L21.lean`,
  not re-proved.  The certified program is `LC21.solve = graph mergeFn` itself, so there is no reshaping
  gap this time.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenHylo
import leet.L21

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC21D

open Freyd

/-! ## The merge as a measured recursive coalgebra -/

/-- The merge coalgebra: emit a leaf (`.inl`) when either list is exhausted — the answer is the other
    list verbatim — otherwise pop the smaller head as a node (`.inr`).  Branch order matches
    `LC21.mergeFn`'s recurrence EXACTLY (nil-left, then nil-right, then compare-heads). -/
def c : List Int × List Int → Sum (List Int) (Int × (List Int × List Int))
  | ([], ys) => Sum.inl ys
  | (xs, []) => Sum.inl xs
  | (x :: xs, y :: ys) =>
      if x ≤ y then Sum.inr (x, (xs, y :: ys)) else Sum.inr (y, (x :: xs, ys))

/-- The measure: total remaining length.  The coalgebra's unfolding is well-founded because every
    `.inr` step drops exactly one element (`hdec`). -/
def μ : List Int × List Int → Nat := fun p => p.1.length + p.2.length

/-- Every `.inr` step drops exactly one element, so `μ` strictly decreases — the well-foundedness
    witness the hylomorphism law demands. -/
theorem hdec : ∀ s e s', c s = Sum.inr (e, s') → μ s' < μ s := by
  intro s e s' h
  obtain ⟨xs, ys⟩ := s
  cases xs with
  | nil => simp only [c] at h; nomatch h
  | cons x xs =>
      cases ys with
      | nil => simp only [c] at h; nomatch h
      | cons y ys =>
          simp only [c] at h
          split at h
          · injection h with h1; injection h1 with h2 h3; subst h3
            simp only [μ, List.length_cons]; omega
          · injection h with h1; injection h1 with h2 h3; subst h3
            simp only [μ, List.length_cons]; omega

/-! ## `LC21.mergeFn` EMERGES as the relational hylomorphism -/

/-- **The derivation.**  The hand-written O(m+n) merge `LC21.mergeFn` (= `LC21.solve`) IS the
    relational hylomorphism of the measured coalgebra `c` with algebra `[id, (· :: ·)]` — it was never
    re-written as a hylomorphism; `hyloFold_unique` certifies that it satisfies the hylomorphism
    recurrence.  The remaining goal is exactly "`mergeFn` obeys `h s = match c s with | inl l => l |
    inr (e,s') => e :: h s'`", discharged by case analysis on the two lists using `LC21.mergeFn`'s own
    recurrence lemmas (`mergeFn_nil_left` / `mergeFn_nil_right` / `mergeFn_cons_eq`). -/
theorem merge_emerges :
    (LC21.solve : LC21.dInput ⟶ LC21.dAns) = Hylo.hyloR c μ hdec id (· :: ·) :=
  Hylo.hyloFold_unique c μ hdec id (· :: ·) (fun p => LC21.mergeFn p.1 p.2) (by
    intro s
    obtain ⟨xs, ys⟩ := s
    cases xs with
    | nil => simp only [c, LC21.mergeFn_nil_left, id_eq]
    | cons x xs =>
        cases ys with
        | nil => simp only [c, LC21.mergeFn_nil_right, id_eq]
        | cons y ys =>
            simp only [LC21.mergeFn_cons_eq]
            split
            · rename_i h; simp only [c, if_pos h]
            · rename_i h; simp only [c, if_neg h])

/-! ## Correctness carries over from `L21.lean` (no re-proof of the merge argument) -/

/-- **Headline.**  The honest bundle: (1) the hand-written O(m+n) merge `LC21.solve` IS the relational
    hylomorphism of the measured coalgebra `c` with algebra `[id, (· :: ·)]` (`merge_emerges`); and
    (2) it therefore refines the spec — `LC21.solve_le_spec` (sortedness + exact multiset preservation)
    carried across.  The merge argument is REUSED, not re-proved.  The certified program is `mergeFn`
    itself (O(m+n)), not the earlier O(n·m) function-carrier fold. -/
theorem merge_derived_correct :
    ((LC21.solve : LC21.dInput ⟶ LC21.dAns) = Hylo.hyloR c μ hdec id (· :: ·))
      ∧ (LC21.solve ⊑ LC21.spec) :=
  ⟨merge_emerges, LC21.solve_le_spec⟩

/-! ## Running the certified program

  The certified program is `LC21.mergeFn` verbatim (fuel-indexed, kernel-reducible), so `decide`
  runs it directly on the LeetCode 21 examples. -/

example : LC21.mergeFn ([1, 2, 4] : List Int) [1, 3, 4] = [1, 1, 2, 3, 4, 4] := by decide
example : LC21.mergeFn ([] : List Int) [0] = [0] := by decide
example : LC21.mergeFn ([2, 5, 8] : List Int) [1, 3, 3, 9] = [1, 2, 3, 3, 5, 8, 9] := by decide

end Freyd.Alg.RelSet.LC21D
