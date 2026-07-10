/-
  LeetCode 118 — Pascal's Triangle — DERIVED from the general-carrier fold law, as a TABULATING
  (growing-list) fold over the ROW axis.

  `leet/L118.lean` WRITES the iteration by hand: `buildRows n r = r :: buildRows (n-1) (nextRow r)`
  recurses on the row count `n`, prepending each row and advancing the current row by one `nextRow`
  pass.  This file makes that fold EMERGE from the reusable general-carrier law
  `Freyd.Alg.RelSet.SL.snocFold_unique` (`AOP/A6_GenFold.lean`), exactly as `L62_derived` /
  `L300_derived` / `L322_derived` do for the other tabulating DPs.

  Two things play different roles.  The ROW axis is the FOLD's input: `SnocList Unit Unit`, the
  initial algebra of `1 + X`, i.e. `ℕ` (`SL.natOf`/`SL.snocs`).  The whole DP state lives INSIDE
  the carrier `C := List (List Nat) × List Nat` — the TABLE of rows produced so far (this is the
  growing list) paired with the CURRENT row.  Every fold step reads the current row, appends it to
  the table, and advances it by `LC118.nextRow` — the tabulating shape a fixed-width scalar tuple
  cannot express.  The base and step are FORCED — they are `foldSL`'s own defining equations (both
  hold by `rfl`):

    * base   `g () = ([], [1])`                                  = `foldSL (wrap _)`
    * step   `st (rows, cur) () = (rows ++ [cur], nextRow cur)`  = `foldSL (snoc xs _)` with
             `(rows, cur) = foldSL xs`.

  `buildRows` conses at the FRONT with a changing seed while the fold accumulates by appending at
  the BACK, so bridging the two is not `rfl`: the one structural fact needed is
  `buildRows n r ++ [nextRowⁿ r] = buildRows (n+1) r` (`buildRows_snoc`).  Chaining it down the fold
  gives `foldSL_snocs : foldSL (snocs n) = (buildRows n [1], nextRowⁿ [1])`, hence
  `(foldSL (snocs n)).1 = LC118.pascalFn n`.  Through that bridge `L118`'s existing correctness
  (`LC118.pascal_correct`: entry `(i,k)` is the binomial coefficient `binom i k`) carries over
  UNCHANGED — no re-proof of the Pascal recurrence.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L118

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC118D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The tabulating fold and its FORCED base/step

  The carrier of `snocFold_unique` is a bare type `C`; here `C = List (List Nat) × List Nat` — the
  table of rows produced so far (the growing list) paired with the current row.  The base `g` and
  step `st` below are not guesses: they are `foldSL`'s defining equations, so both fold conditions
  hold by `rfl`. -/

/-- The Pascal fold as a catamorphism over the ROW axis `SnocList Unit Unit ≅ ℕ`: fold `n` rows,
    carrying `(table so far, current row)`.  Each step appends the current row to the table and
    advances it by one `LC118.nextRow` pass — the tabulating shape.  Mirrors `LC118.buildRows`'s
    iteration over the initial-algebra `ℕ`, but as an accumulating (append) fold. -/
def foldSL : SnocList Unit Unit → List (List Nat) × List Nat
  | SnocList.wrap _    => ([], [1])
  | SnocList.snoc xs _ => ((foldSL xs).1 ++ [(foldSL xs).2], LC118.nextRow (foldSL xs).2)

/-- The base of the emergent algebra: the empty table and the seed row `[1]` (row `0`). -/
def g : Unit → List (List Nat) × List Nat := fun _ => ([], [1])

/-- The step of the emergent algebra: append the current row to the table and advance it by one
    `LC118.nextRow` pass (a single `zipWith` shift-and-add) — reads the WHOLE current row. -/
def st : List (List Nat) × List Nat → Unit → List (List Nat) × List Nat :=
  fun p _ => (p.1 ++ [p.2], LC118.nextRow p.2)

/-- The base condition is a COMPUTATION, not a guess: `foldSL (wrap _) = g _`. -/
theorem foldSL_wrap : ∀ l : Unit, foldSL (SnocList.wrap l) = g l := fun _ => rfl

/-- The step condition IS `foldSL`'s snoc equation: `foldSL (snoc xs _) = st (foldSL xs) _`. -/
theorem foldSL_snoc : ∀ (xs : SnocList Unit Unit) (e : Unit),
    foldSL (SnocList.snoc xs e) = st (foldSL xs) e := fun _ _ => rfl

/-! ## The fold EMERGES via the general-carrier law -/

/-- **The derivation.**  The tabulating fold is PRODUCED by `snocFold_unique` from the base `g` and
    step `st` — it was never written as a recursive fold: `graph foldSL` equals the catamorphism of
    the emergent scalar algebra `scalarAlg g st`.  The carrier `List (List Nat) × List Nat` — a
    growing table read/extended by every step — is what makes this tabulating. -/
theorem pascal_emerges :
    (graph foldSL : dSL Unit Unit ⟶ ⟨List (List Nat) × List Nat⟩) = cataR (scalarAlg g st) :=
  SL.snocFold_unique g st foldSL foldSL_wrap foldSL_snoc

/-! ## Bridge to `L118`'s hand-written iteration

  `LC118.buildRows` conses at the FRONT with a changing seed; `foldSL` appends at the BACK.  The one
  structural fact reconciling them is `buildRows_snoc`.  `iterNext n r = nextRowⁿ r` names the row
  reached after `n` passes. -/

/-- `nextRow` applied `n` times, folded in at the SEED (needed to name the current row `(foldSL …).2`
    and the row appended at step `n`). -/
def iterNext : Nat → List Nat → List Nat
  | 0,     r => r
  | n + 1, r => iterNext n (LC118.nextRow r)

/-- One extra `nextRow` on the OUTSIDE equals one more fold-in at the seed. -/
theorem iterNext_nextRow : ∀ (n : Nat) (r : List Nat),
    LC118.nextRow (iterNext n r) = iterNext n (LC118.nextRow r)
  | 0,     r => rfl
  | n + 1, r => by
      show LC118.nextRow (iterNext n (LC118.nextRow r))
          = iterNext n (LC118.nextRow (LC118.nextRow r))
      rw [iterNext_nextRow n (LC118.nextRow r)]

/-- **The append-vs-prepend reconciliation.**  Appending the `n`-th row `nextRowⁿ r` at the BACK of
    `buildRows n r` yields exactly `buildRows (n+1) r`.  Induction on `n` (generalizing the seed `r`),
    the sole fact linking the fold's accumulate-by-append to `buildRows`'s cons-with-changing-seed. -/
theorem buildRows_snoc : ∀ (n : Nat) (r : List Nat),
    LC118.buildRows n r ++ [iterNext n r] = LC118.buildRows (n + 1) r
  | 0,     r => rfl
  | n + 1, r => by
      show r :: (LC118.buildRows n (LC118.nextRow r) ++ [iterNext n (LC118.nextRow r)])
          = r :: LC118.buildRows (n + 1) (LC118.nextRow r)
      rw [buildRows_snoc n (LC118.nextRow r)]

/-- **The fold reproduces `L118`'s iteration.**  Fed the ROW-axis encoding `SL.snocs n` of `n : ℕ`,
    the emergent fold's state is `(buildRows n [1], nextRowⁿ [1])`: the first component is exactly
    `L118`'s table of `n` rows, the second the next row to be produced.  Induction on `n`, using
    `buildRows_snoc`/`iterNext_nextRow` at each step. -/
theorem foldSL_snocs : ∀ n, foldSL (SL.snocs n) = (LC118.buildRows n [1], iterNext n [1])
  | 0     => rfl
  | n + 1 => by
      have ih := foldSL_snocs n
      show ((foldSL (SL.snocs n)).1 ++ [(foldSL (SL.snocs n)).2],
             LC118.nextRow (foldSL (SL.snocs n)).2)
          = (LC118.buildRows (n + 1) [1], iterNext (n + 1) [1])
      rw [ih]
      show (LC118.buildRows n [1] ++ [iterNext n [1]], LC118.nextRow (iterNext n [1]))
          = (LC118.buildRows (n + 1) [1], iterNext n (LC118.nextRow [1]))
      rw [buildRows_snoc n [1], iterNext_nextRow n [1]]

/-- The fold's first component (the accumulated table) at `snocs n` is exactly `LC118.pascalFn n`. -/
theorem foldSL_fst_snocs (n : Nat) : (foldSL (SL.snocs n)).1 = LC118.pascalFn n := by
  rw [foldSL_snocs n]; rfl

/-! ## `solve` as the fold -/

/-- **`L118`'s allegory program is the fold.**  `LC118.solve = graph pascalFn` equals the graph of
    the emergent fold's answer projection `n ↦ (foldSL (snocs n)).1`. -/
theorem solve_via_fold :
    LC118.solve = (graph (fun n => (foldSL (SL.snocs n)).1) : LC118.dNat ⟶ LC118.dRows) := by
  funext n rows
  show (rows = LC118.pascalFn n) = (rows = (foldSL (SL.snocs n)).1)
  rw [foldSL_fst_snocs n]

/-! ## Correctness carries over from `L118.lean` (no re-proof of the Pascal recurrence) -/

/-- **Headline.**  The tabulating fold EMERGES as the catamorphism of the emergent algebra
    (`pascal_emerges`), AND its accumulated table at `snocs n` is, entry-by-entry, exactly Pascal's
    triangle: for every row `i < n` and column `k`, entry `(i,k)` is the binomial coefficient
    `binom i k` when `k ≤ i`, and absent otherwise.  The binomial content is REUSED from
    `LC118.pascal_correct` (through the bridge `foldSL_fst_snocs`), not re-proved. -/
theorem pascal_derived_correct (n : Nat) :
    (graph foldSL : dSL Unit Unit ⟶ ⟨List (List Nat) × List Nat⟩) = cataR (scalarAlg g st)
    ∧ ∀ i, i < n → ∀ k, ((foldSL (SL.snocs n)).1)[i]?.bind (·[k]?)
        = (if k ≤ i then some (LC118.binom i k) else none) := by
  refine ⟨pascal_emerges, ?_⟩
  intro i hi k
  rw [foldSL_fst_snocs n]
  exact LC118.pascal_correct n i hi k

/-! ## Running / cross-checking the emergent fold against `leet/L118.lean`

  The relational catamorphism `cataFold (scalarAlg …)` is not `decide`-computable (its `snoc` case
  is an existential over the carrier), so we `decide` the extensionally-equal computable witness
  `(foldSL ∘ SL.snocs).1` (equal to the fold by `pascal_emerges`), and separately PROVE that the
  emergent fold relates a concrete row-count to `foldSL` of it. -/

-- The derived table `decide`s on the computable witness (LeetCode 118's own examples):
example : (foldSL (SL.snocs 5)).1 = [[1], [1, 1], [1, 2, 1], [1, 3, 3, 1], [1, 4, 6, 4, 1]] := by decide
example : (foldSL (SL.snocs 1)).1 = [[1]] := by decide
example : (foldSL (SL.snocs 5)).1 = LC118.pascalFn 5 := by decide

/-- The emergent fold genuinely relates the row-count `3` (i.e. `snocs 3`) to `foldSL (snocs 3)`
    (whose first component is the first three rows `[[1], [1,1], [1,2,1]]`). -/
example : cataFold (scalarAlg g st) (SL.snocs 3) (foldSL (SL.snocs 3)) := by
  have h : (graph foldSL : dSL Unit Unit ⟶ ⟨List (List Nat) × List Nat⟩)
      (SL.snocs 3) (foldSL (SL.snocs 3)) := rfl
  rw [pascal_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC118D
