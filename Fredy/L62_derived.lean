/-
  LeetCode 62 — Unique Paths — DERIVED from the general-carrier fold law, as a TABULATING fold.

  `Fredy/L62.lean` WRITES the DP by hand: `rowAt m n` folds `m` copies of `stepRow` (a prefix-sum
  pass) over `initRow n`, one whole DP ROW (`SnocList Nat Nat`) per grid-row, and reads off the
  corner.  This file makes that row-fold EMERGE from the reusable general-carrier law
  `Freyd.Alg.RelSet.SL.snocFold_unique` (`Fredy/A6_GenFold.lean`), exactly as `L300_derived` /
  `L322_derived` do for the other tabulating (growing-carrier) DPs.

  The two axes of the grid play different roles here.  The COLUMN axis lives INSIDE the carrier: the
  carrier is the whole DP row `C := SnocList Nat Nat`, and the width `n` is a fixed closure
  parameter.  The ROW axis is the FOLD's input: it is `SnocList Unit Unit`, the initial algebra of
  `1 + X`, i.e. `ℕ` (`SL.natOf`/`SL.snocs`, `SL.natOf_snocs`).  So folding down `m` rows is a
  snoc-list catamorphism over `SnocList Unit Unit`, whose step reads the WHOLE previous row —
  the tabulating shape.  Feeding the base/step to `snocFold_unique` PRODUCES that fold; we never
  write a recursive row-fold, it is the law's catamorphism.  The base and step are FORCED — they
  are `rowFold`'s own defining equations (both hold by `rfl`):

    * base   `g n () = LC62.initRow n`                     = `rowFold n (wrap _)`
    * step   `st n row () = LC62.stepRow row`              = `rowFold n (snoc ms _)` with
             `row = rowFold n ms`.

  Bridging `rowFold n (SL.snocs m) = LC62.rowAt m n` (induction on `m`) reconnects the emergent
  fold to `L62`'s hand-written answer, so `L62`'s existing correctness (`LC62.solve_correct`:
  `solveFn = paths`) carries over UNCHANGED — no re-proof of the path-count recurrence.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.L62

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC62D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The tabulating ANSATZ and its FORCED base/step

  The carrier of `snocFold_unique` is a bare type `C`; here `C = SnocList Nat Nat` — the whole DP
  row.  The fold's input is the ROW axis `SnocList Unit Unit ≅ ℕ`.  The base `g n` and step `st n`
  below are not guesses: they are `rowFold n`'s defining equations, so both conditions hold by
  `rfl`. -/

/-- The row after folding down the grid's rows, for a fixed width `n`: `stepRow` folded over
    `initRow n`, but written as a catamorphism over the ROW axis `SnocList Unit Unit`.  This mirrors
    `LC62.rowAt`'s recursion in `m`, over the initial-algebra `ℕ`. -/
def rowFold (n : Nat) : SnocList Unit Unit → SnocList Nat Nat
  | SnocList.wrap _    => LC62.initRow n
  | SnocList.snoc ms _ => LC62.stepRow (rowFold n ms)

/-- The base of the emergent algebra: the width-`n` starting row `initRow n` (all `1`s). -/
def g (n : Nat) : Unit → SnocList Nat Nat := fun _ => LC62.initRow n

/-- The step of the emergent algebra: one DP row-transition `stepRow` (a prefix-sum reading the
    WHOLE previous row) — the tabulating shape a fixed-width tupling carrier cannot express. -/
def st (n : Nat) : SnocList Nat Nat → Unit → SnocList Nat Nat := fun row _ => LC62.stepRow row

/-- The base condition is a COMPUTATION, not a guess: `rowFold n (wrap _) = g n _`. -/
theorem rowFold_wrap (n : Nat) : ∀ l : Unit, rowFold n (SnocList.wrap l) = g n l := fun _ => rfl

/-- The step condition IS `rowFold`'s snoc equation: `rowFold n (snoc ms _) = st n (rowFold n ms) _`. -/
theorem rowFold_snoc (n : Nat) : ∀ (ms : SnocList Unit Unit) (e : Unit),
    rowFold n (SnocList.snoc ms e) = st n (rowFold n ms) e := fun _ _ => rfl

/-! ## The row-fold EMERGES via the general-carrier law -/

/-- **The derivation.**  The tabulating row-fold is PRODUCED by `snocFold_unique` from the base `g n`
    and step `st n` — it was never written as a recursive fold: `graph (rowFold n)` equals the
    catamorphism of the emergent scalar algebra `scalarAlg (g n) (st n)`.  The carrier `SnocList Nat
    Nat` (the whole DP row, read in full by every step) is what makes this tabulating. -/
theorem rows_emerge (n : Nat) :
    (graph (rowFold n) : dSL Unit Unit ⟶ ⟨SnocList Nat Nat⟩) = cataR (scalarAlg (g n) (st n)) :=
  SL.snocFold_unique (g n) (st n) (rowFold n) (rowFold_wrap n) (rowFold_snoc n)

/-! ## Bridge to `L62`'s hand-written answer -/

/-- The emergent fold, fed the ROW-axis encoding `SL.snocs m` of `m : ℕ`, reproduces `L62`'s
    hand-written `rowAt m n`.  Induction on `m` (base `wrap`, step `stepRow`) mirrors `rowAt`'s own
    recursion in `m`. -/
theorem rowFold_snocs (n : Nat) : ∀ m, rowFold n (SL.snocs m) = LC62.rowAt m n
  | 0     => rfl
  | m + 1 => by
      show LC62.stepRow (rowFold n (SL.snocs m)) = LC62.stepRow (LC62.rowAt m n)
      rw [rowFold_snocs n m]

/-! ## Correctness carries over from `L62.lean` (no re-proof of the recurrence) -/

/-- **Headline.**  The row-fold EMERGES as the catamorphism of the emergent algebra
    (`rows_emerge`), AND reading its last cell after `m` folded rows is exactly the number of unique
    monotone lattice paths across an `(m+1) × (n+1)` grid — `LC62.paths (m+1) (n+1)`.  The
    path-count argument is REUSED from `LC62.solve_correct` (through the bridge `rowFold_snocs`), not
    re-proved. -/
theorem uniquepaths_derived_correct (m n : Nat) :
    (graph (rowFold n) : dSL Unit Unit ⟶ ⟨SnocList Nat Nat⟩) = cataR (scalarAlg (g n) (st n))
    ∧ LC62.lastOf (rowFold n (SL.snocs m)) = LC62.paths (m + 1) (n + 1) := by
  refine ⟨rows_emerge n, ?_⟩
  rw [rowFold_snocs n m]
  -- `LC62.solveFn (m+1) (n+1)` is definitionally `lastOf (rowAt m n)`; reuse `solve_correct`.
  exact LC62.solve_correct (m + 1) (n + 1)

/-! ## Running / cross-checking the emergent fold against `Fredy/L62.lean`

  The relational catamorphism `cataFold (scalarAlg …)` is not `decide`-computable (its `snoc` case
  is an existential over the carrier), so we `decide` the extensionally-equal computable witness
  `LC62.lastOf ∘ rowFold n ∘ SL.snocs` (equal to the fold by `rows_emerge`), and separately PROVE
  that the emergent fold relates a concrete row-count to `rowFold` of it. -/

-- The derived answer cell `decide`s on the computable witness (LeetCode 62 examples, `(m+1)×(n+1)`):
example : LC62.lastOf (rowFold 6 (SL.snocs 2)) = 28 := by decide   -- 3 × 7 grid
example : LC62.lastOf (rowFold 1 (SL.snocs 2)) = 3  := by decide   -- 3 × 2 grid
example : LC62.lastOf (rowFold 2 (SL.snocs 2)) = 6  := by decide   -- 3 × 3 grid

-- The spec `paths` (compiled by well-founded recursion) matches, via the reused `solve_correct`:
example : LC62.paths 3 7 = 28 := by rw [← LC62.solve_correct]; decide
example : LC62.paths 3 2 = 3  := by rw [← LC62.solve_correct]; decide

/-- The emergent fold genuinely relates the row-count `2` (i.e. `snocs 2`) to `rowFold 6` of it
    (whose last cell is 28, the `3 × 7` path count). -/
example :
    cataFold (scalarAlg (g 6) (st 6)) (SL.snocs 2) (rowFold 6 (SL.snocs 2)) := by
  have h : (graph (rowFold 6) : dSL Unit Unit ⟶ ⟨SnocList Nat Nat⟩)
      (SL.snocs 2) (rowFold 6 (SL.snocs 2)) := rfl
  rw [rows_emerge] at h
  exact h

end Freyd.Alg.RelSet.LC62D
