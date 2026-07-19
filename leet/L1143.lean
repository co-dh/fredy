/-
  LeetCode 1143 — Longest Common Subsequence — as an ALLEGORY PROGRAM.

  Problem: given two sequences `xs ys : List Int`, find the length of their longest common
  subsequence (a subsequence obtained by deleting zero or more elements from each, preserving
  order, such that the results are equal).

  This is the `L62`/`L322` 2-D DP family generalised to TWO independently-shrinking sequences (not
  one sequence against an amount-axis): the naive recurrence branches on whether the two FRONT
  elements match (consume both, `+1`) or not (drop one or the other, take the `≤`-max of both
  sub-answers) — the classic "match / mismatch" 2-D table shape.

  1. **Spec `lcs`** — the naive recurrence *is* the definition, exactly as stated by the problem.
     Each recursive call decreases a DIFFERENT one of the two arguments (never both together), so —
     like `L62`'s `paths` — a direct pattern-matching definition compiles via WELL-FOUNDED
     recursion, not structural recursion, and is not `decide`-friendly (kernel reduction on
     `WellFounded.fix` stalls). Following the `L322`/S13 fuel trick, `lcs` is instead a thin
     wrapper `lcsFuel (xs.length + ys.length) xs ys` over a FUEL-indexed helper `lcsFuel` that
     recurses structurally on the fuel — kernel-reducible, so `decide` works directly on `lcs`.
     `lcsFuel_stable` (any sufficient fuel agrees with the minimal fuel) then recovers the book
     recurrence as an ordinary theorem, `lcs_cons_eq`.
  2. **Program** — a genuine O(|xs|·|ys|) 2-D DP, in the `L62` row-fold style but one dimension
     richer: `col ys xs` folds a DP ROW (a plain `List Nat`, one entry per SUFFIX of `ys`) down
     `xs`; `rowStep` recomputes the whole row from the previous one AND the fixed `ys` in one
     structural pass (entry `j` needs entry `j+1` of the SAME new row, built back-to-front, plus
     two entries of the previous row — the two-argument analogue of `L62`'s prefix-sum
     `scanStep`).
  3. **Correctness (equality)** — `solveFn xs ys = lcs xs ys`, by the same "strengthen a scalar
     equality to a whole-row equality, nested induction" recipe as `L62`: outer induction on `xs`
     (`col_eq_targetRow`), crux lemma `rowStep_targetRow` by inner induction on `ys`, reducing at
     each step to exactly `lcs_cons_eq` (the role `L62`'s own 2-D recurrence played there).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC1143

open Freyd Freyd.Alg.RelSet.SL

/-! ## Nat `max` (mathlib-free, so we control the rewrite lemmas — copy of `L121`'s `imax`,
    specialised to `Nat` since LCS lengths are never negative). -/

def imax (a b : Nat) : Nat := if a ≤ b then b else a

theorem imax_ge_left  (a b : Nat) : a ≤ imax a b := by unfold imax; split <;> omega
theorem imax_ge_right (a b : Nat) : b ≤ imax a b := by unfold imax; split <;> omega
theorem imax_eq_or (a b : Nat) : imax a b = a ∨ imax a b = b := by
  unfold imax; split; exacts [Or.inr rfl, Or.inl rfl]

/-! ## Data -/

/-- The input object: the two sequences. -/
abbrev dInput : RelSet.{0} := ⟨List Int × List Int⟩
/-- The answer object: the LCS length. -/
abbrev dAns : RelSet.{0} := ⟨Nat⟩

/-! ## Spec: the naive match/mismatch recurrence, via a fuel-indexed helper -/

/-- `lcsFuel fuel xs ys` — the naive LCS recurrence, with an explicit FUEL bound so the recursion
    is ordinary structural recursion on `fuel` (not well-founded recursion on the shrinking-pair
    of lists), keeping it kernel-reducible for `decide`. Any `fuel ≥ xs.length + ys.length`
    computes the true answer (`lcsFuel_stable`); `fuel = 0` with both lists non-empty is a junk
    fallback, never hit once `fuel` is chosen sufficiently. -/
def lcsFuel : Nat → List Int → List Int → Nat
  | 0, _, _ => 0
  | _ + 1, [], _ => 0
  | _ + 1, _ :: _, [] => 0
  | fuel + 1, x :: xs, y :: ys =>
      if x = y then lcsFuel fuel xs ys + 1
      else imax (lcsFuel fuel (x :: xs) ys) (lcsFuel fuel xs (y :: ys))

/-- **The specification**: the length of the longest common subsequence of `xs` and `ys` — the
    book's naive recurrence, run with exactly enough fuel. -/
def lcs (xs ys : List Int) : Nat := lcsFuel (xs.length + ys.length) xs ys

@[simp] theorem lcsFuel_nil_left (fuel : Nat) (ys : List Int) : lcsFuel fuel [] ys = 0 := by
  cases fuel <;> rfl

@[simp] theorem lcsFuel_nil_right (fuel : Nat) (xs : List Int) : lcsFuel fuel xs [] = 0 := by
  cases fuel with
  | zero => rfl
  | succ f => cases xs <;> rfl

theorem lcs_nil_left (ys : List Int) : lcs [] ys = 0 := lcsFuel_nil_left _ ys
theorem lcs_nil_right (xs : List Int) : lcs xs [] = 0 := lcsFuel_nil_right _ xs

/-- **Fuel invariance**: any fuel at least covering the input sizes agrees with `lcs`'s own
    (minimal) fuel — proved by NESTED STRUCTURAL induction (outer on `xs`, inner on `ys`, exactly
    `L62`'s `scanStep_pathsRow` shape) rather than strong induction on a size measure: the outer
    IH (quantified over ALL `ys`) supplies the "same `xs`, any `ys`" sub-case, the inner IH
    supplies the "same `xs`, shorter `ys`" sub-case, and together they cover all three of the
    2-D recurrence's sub-calls. -/
theorem lcsFuel_stable :
    ∀ xs ys fuel, xs.length + ys.length ≤ fuel → lcsFuel fuel xs ys = lcs xs ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys fuel _
    rw [lcsFuel_nil_left, lcs_nil_left]
  | cons x xs ih_outer =>
    intro ys
    induction ys with
    | nil =>
      intro fuel _
      rw [lcsFuel_nil_right, lcs_nil_right]
    | cons y ys ih_inner =>
      intro fuel hfuel
      cases fuel with
      | zero => exfalso; simp only [List.length_cons] at hfuel; omega
      | succ f =>
        have hbase : xs.length + ys.length + 1 ≤ f := by
          simp only [List.length_cons] at hfuel; omega
        have hLHS : lcsFuel (f + 1) (x :: xs) (y :: ys) =
            if x = y then lcsFuel f xs ys + 1
            else imax (lcsFuel f (x :: xs) ys) (lcsFuel f xs (y :: ys)) := by
          simp only [lcsFuel]
        have hmin : (x :: xs).length + (y :: ys).length = (xs.length + ys.length + 1) + 1 := by
          simp only [List.length_cons]; omega
        have hRHS : lcs (x :: xs) (y :: ys) =
            if x = y then lcsFuel (xs.length + ys.length + 1) xs ys + 1
            else imax (lcsFuel (xs.length + ys.length + 1) (x :: xs) ys)
                      (lcsFuel (xs.length + ys.length + 1) xs (y :: ys)) := by
          show lcsFuel ((x :: xs).length + (y :: ys).length) (x :: xs) (y :: ys) = _
          rw [hmin]; simp only [lcsFuel]
        rw [hLHS, hRHS]
        have e1 : lcsFuel f xs ys = lcsFuel (xs.length + ys.length + 1) xs ys := by
          rw [ih_outer ys f (by omega), ih_outer ys (xs.length + ys.length + 1) (by omega)]
        have e2 : lcsFuel f (x :: xs) ys = lcsFuel (xs.length + ys.length + 1) (x :: xs) ys := by
          rw [ih_inner f (by simp only [List.length_cons]; omega),
              ih_inner (xs.length + ys.length + 1) (by simp only [List.length_cons]; omega)]
        have e3 : lcsFuel f xs (y :: ys) = lcsFuel (xs.length + ys.length + 1) xs (y :: ys) := by
          rw [ih_outer (y :: ys) f (by simp only [List.length_cons]; omega),
              ih_outer (y :: ys) (xs.length + ys.length + 1) (by simp only [List.length_cons]; omega)]
        rw [e1, e2, e3]

/-- **The book recurrence, recovered as a theorem**: `lcs`'s match/mismatch equation, at
    exactly-sufficient (but not necessarily minimal) fuel via `lcsFuel_stable`. -/
theorem lcs_cons_eq (x : Int) (xs : List Int) (y : Int) (ys : List Int) :
    lcs (x :: xs) (y :: ys) =
      if x = y then lcs xs ys + 1 else imax (lcs (x :: xs) ys) (lcs xs (y :: ys)) := by
  have hmin : (x :: xs).length + (y :: ys).length = (xs.length + ys.length + 1) + 1 := by
    simp only [List.length_cons]; omega
  have hunfold : lcs (x :: xs) (y :: ys) =
      if x = y then lcsFuel (xs.length + ys.length + 1) xs ys + 1
      else imax (lcsFuel (xs.length + ys.length + 1) (x :: xs) ys)
                (lcsFuel (xs.length + ys.length + 1) xs (y :: ys)) := by
    show lcsFuel ((x :: xs).length + (y :: ys).length) (x :: xs) (y :: ys) = _
    rw [hmin]; simp only [lcsFuel]
  rw [hunfold,
    lcsFuel_stable xs ys (xs.length + ys.length + 1) (by omega),
    lcsFuel_stable (x :: xs) ys (xs.length + ys.length + 1) (by simp only [List.length_cons]; omega),
    lcsFuel_stable xs (y :: ys) (xs.length + ys.length + 1) (by simp only [List.length_cons]; omega)]

/-! ## Program: an O(|xs|·|ys|) 2-D DP — one row of `List Nat`, indexed by suffixes of `ys` -/

/-- One row-transition: given the previous row `prevRow` (indexed by suffixes of `ys`,
    `prevRow`'s `j`-th entry `= lcs xs (ys.drop j)`) and the next front character `x`, compute the
    new row (`j`-th entry `= lcs (x :: xs) (ys.drop j)`) — built back-to-front (`ys`-structural,
    combining its OWN just-computed shorter-suffix entry with two entries of `prevRow`), the
    two-argument analogue of `L62`'s prefix-sum `scanStep`. -/
def rowStep (x : Int) : List Int → List Nat → List Nat
  | [], _ => [0]
  | y :: ys, p :: ps =>
      let newRow := rowStep x ys ps
      (if x = y then ps.headD 0 + 1 else imax (newRow.headD 0) p) :: newRow
  | _ :: _, [] => [0]   -- unreachable (length mismatch); junk fallback

/-- The DP column for a fixed `ys`: `col ys xs` folds `rowStep` down `xs` (`ys.length + 1`
    entries; entry `j = lcs xs (ys.drop j)`), starting from the all-`0` row (`lcs [] _ = 0`
    everywhere). -/
def col (ys : List Int) : List Int → List Nat
  | [] => List.replicate (ys.length + 1) 0
  | x :: xs => rowStep x ys (col ys xs)

/-- **The program**: the DP-table entry for the FULL `ys` (position `0` of the final column). -/
def solveFn (xs ys : List Int) : Nat := (col ys xs).headD 0

/-- **The allegory program**: LeetCode 1143's DP solution as a morphism `dInput ⟶ dAns`. -/
def solve : dInput ⟶ dAns := graph (fun p => solveFn p.1 p.2)

/-- **The specification** as a morphism `dInput ⟶ dAns` in `Rel(Set)`: `(xs, ys)` relates to
    `lcs xs ys`. -/
def spec : dInput ⟶ dAns := fun p k => k = lcs p.1 p.2

/-! ## Correctness: the folded column IS the column of `lcs` values -/

/-- The explicit target row for a fixed `xs`: entry `lcs xs (y :: ys), ..., lcs xs []`,
    snoc-... — er, CONS-built from the front, in DECREASING-suffix order (matches `rowStep`'s own
    back-to-front build direction). -/
def targetRow (xs : List Int) : List Int → List Nat
  | [] => [lcs xs []]
  | y :: ys => lcs xs (y :: ys) :: targetRow xs ys

/-- The head of the target row is exactly the top-level `lcs` value. -/
theorem targetRow_head (xs ys : List Int) : (targetRow xs ys).headD 0 = lcs xs ys := by
  cases ys <;> rfl

/-- The base column (`xs = []`) is the target row `targetRow []` (all `lcs [] _ = 0`). -/
theorem replicate_eq_targetRow_nil (ys : List Int) :
    List.replicate (ys.length + 1) 0 = targetRow [] ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    show (0 : Nat) :: List.replicate (ys.length + 1) 0 = lcs [] (y :: ys) :: targetRow [] ys
    rw [lcs_nil_left, ih]

/-- **Crux lemma**: `rowStep` on the target row for `xs` produces exactly the target row for
    `x :: xs` — the book recurrence `lcs_cons_eq`, read off entry-by-entry via induction on `ys`. -/
theorem rowStep_targetRow (x : Int) (xs ys : List Int) :
    rowStep x ys (targetRow xs ys) = targetRow (x :: xs) ys := by
  induction ys with
  | nil =>
    show ([0] : List Nat) = [lcs (x :: xs) []]
    rw [lcs_nil_right]
  | cons y ys ih =>
    show (if x = y then (targetRow xs ys).headD 0 + 1
          else imax ((rowStep x ys (targetRow xs ys)).headD 0) (lcs xs (y :: ys)))
        :: rowStep x ys (targetRow xs ys)
      = lcs (x :: xs) (y :: ys) :: targetRow (x :: xs) ys
    rw [ih]
    simp only [targetRow_head]
    rw [← lcs_cons_eq]

/-- **The column-fold IS the target column**: `col ys xs` equals `targetRow xs ys`, for every
    `xs` and fixed `ys`. -/
theorem col_eq_targetRow (ys xs : List Int) : col ys xs = targetRow xs ys := by
  induction xs with
  | nil => exact replicate_eq_targetRow_nil ys
  | cons x xs ih =>
    show rowStep x ys (col ys xs) = targetRow (x :: xs) ys
    rw [ih]
    exact rowStep_targetRow x xs ys

/-- **Correctness of the program**: `solveFn` computes exactly `lcs`. -/
theorem solve_correct (xs ys : List Int) : solveFn xs ys = lcs xs ys := by
  show (col ys xs).headD 0 = lcs xs ys
  rw [col_eq_targetRow ys xs, targetRow_head]

/-- **Correctness of the allegory program**: `solve = spec` as morphisms in `Rel(Set)`. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro p k
  show k = solveFn p.1 p.2 ↔ k = lcs p.1 p.2
  rw [solve_correct]

/-! ## Running the program -/

example : lcs [1, 2, 3, 4, 5] [1, 3, 5] = 3 := by decide
example : lcs [1, 2] [3, 4] = 0 := by decide
example : lcs [1, 2, 3] [1, 2, 3] = 3 := by decide
example : lcs ([] : List Int) [1] = 0 := by decide

example : solveFn [1, 2, 3, 4, 5] [1, 3, 5] = 3 := by decide
example : solveFn [1, 2] [3, 4] = 0 := by decide
example : solveFn [1, 2, 3] [1, 2, 3] = 3 := by decide
example : solveFn ([] : List Int) [1] = 0 := by decide

end Freyd.Alg.RelSet.LC1143
