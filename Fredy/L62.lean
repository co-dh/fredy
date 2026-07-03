/-
  LeetCode 62 — Unique Paths — as an ALLEGORY PROGRAM.

  Problem: on an `m × n` grid a robot moves only right or down, starting top-left; count the
  monotone lattice paths to the bottom-right corner.

  This is the 2-D cousin of `L70`'s tupling skill: the naive recurrence is already the exact
  answer (a correctness EQUALITY, not the refinement+domination `⊑` of the optimisation
  problems), the only issue is exponential blow-up from re-expanding both recursive calls.
  Where `L70` linearised by carrying a PAIR `(f n, f (n+1))`, here we carry an entire DP ROW (a
  `SnocList Nat Nat`, the engine from `Fredy.A6_SnocList`, all `1`s initially) down the grid's
  rows: each new row is the INCLUSIVE PREFIX SUM of the previous row (`newrow[j] = newrow[j-1] +
  oldrow[j]`), and the answer is the row's last entry.

  1. **Spec** — `paths : Nat → Nat → Nat`, the naive 2-D recurrence (the book recurrence
     `paths (M+1) (N+1) = paths M (N+1) + paths (M+1) N`: the last step of a path into an
     `(M+1)×(N+1)` grid came either from above (an `M×(N+1)` grid) or from the left (an
     `(M+1)×N` grid)). `spec : (m,n) ↦ paths m n`.
  2. **Program** — `rowAt m n : SnocList Nat Nat` folds `m` row-transitions (`stepRow`, a
     prefix-sum pass) over `initRow n` (`n+1` columns, all `1`s); `solveFn m n` reads off the
     last entry, for an `(m+1)×(n+1)`-shaped input (with `0` on a degenerate `0`-sized side).
  3. **Refinement (equality)** — `rowAt m n = pathsRow m n`, an explicit snoc-built target row
     of `paths (m+1) 1, …, paths (m+1) (n+1)`, by induction on `m`. The successor step reduces —
     after strengthening to the whole row via a nested induction on the column count `n` — to
     the book recurrence, the crux lemma `scanStep_pathsRow`.

  Route taken: the GENUINE efficient row-fold DP (not the "clean double-recursion" fallback).
  The one wrinkle: `paths`'s two-argument recurrence (each recursive call decreases a DIFFERENT
  argument, so it is not structural in either alone) makes Lean compile it via well-founded
  recursion, so its defining equations are only propositionally true (`simp [paths]`), never
  `rfl` — every `paths`-unfolding step below goes through `simp`/`rw`, not `show … ; rfl`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC62

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data -/

abbrev dNat  : RelSet.{0} := ⟨Nat⟩
abbrev dGrid : RelSet.{0} := ⟨Nat × Nat⟩

/-! ## Spec: the naive 2-D recurrence — "the definition of the answer" -/

/-- Number of monotone (right/down) lattice paths across an `m × n` grid — the naive,
    exponentially-recomputing recurrence. A `1`-row grid (or, symmetrically, the `(m+1),(n+1)`
    clause never fires below `m ≥ 1`) has exactly one path: straight across. -/
def paths : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 0
  | 1, _ => 1
  | (m+1), (n+1) => paths m (n+1) + paths (m+1) n

/-- **The specification** as a morphism `dGrid ⟶ dNat` in `Rel(Set)`: `(m,n)` relates to
    `paths m n`. -/
def spec : dGrid ⟶ dNat := fun mn k => k = paths mn.1 mn.2

/-! ## Program: fold ONE DP ROW down the grid's rows — a `SnocList Nat Nat`, prefix-summed -/

/-- `scanStep xs = (total, ys)`: `ys` is the inclusive prefix-sum of `xs` (`ys`'s `j`-th entry
    (from the left) is the sum of `xs`'s first `j+1` entries), and `total` is `ys`'s last entry
    (= the sum of ALL of `xs`) — a single snoc-recursive left-to-right pass. -/
def scanStep : SnocList Nat Nat → Nat × SnocList Nat Nat
  | SnocList.wrap x => (x, SnocList.wrap x)
  | SnocList.snoc xs p =>
      let (acc, out) := scanStep xs
      (acc + p, SnocList.snoc out (acc + p))

/-- One DP row-transition: `newrow[j] = newrow[j-1] + oldrow[j]`, `newrow[0] = oldrow[0]`. -/
def stepRow (xs : SnocList Nat Nat) : SnocList Nat Nat := (scanStep xs).2

/-- The all-`1`s row of `n+1` columns — grid-row `1`: only rightward moves, one path each. -/
def initRow : Nat → SnocList Nat Nat
  | 0 => SnocList.wrap 1
  | (n+1) => SnocList.snoc (initRow n) 1

/-- The DP row after `m+1` grid-rows, for a grid of `n+1` columns: `stepRow`, folded `m` times
    over `initRow n`. -/
def rowAt : Nat → Nat → SnocList Nat Nat
  | 0, n => initRow n
  | (m+1), n => stepRow (rowAt m n)

/-- The last (rightmost) entry of a `SnocList`. -/
def lastOf : SnocList Nat Nat → Nat
  | SnocList.wrap x => x
  | SnocList.snoc _ p => p

/-- The answer: the bottom-right corner of the DP row, for an `(m+1) × (n+1)` grid (`0` on a
    degenerate `0`-sized side, matching `paths`). -/
def solveFn : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 0
  | (m+1), (n+1) => lastOf (rowAt m n)

/-- **The allegory program**: LeetCode 62's DP solution as a morphism `dGrid ⟶ dNat`. -/
def solve : dGrid ⟶ dNat := graph (fun mn => solveFn mn.1 mn.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map _

/-! ## The refinement: the folded row IS the row of `paths` values -/

/-- Column `1` of every grid-row is `1` (reachable only by going straight down from row `1`).
    `paths` is compiled by well-founded recursion (a genuine 2-argument recurrence, not
    structural in either argument alone), so its defining equations hold propositionally via
    `simp [paths]`, not by `rfl`. -/
theorem paths_col1 (M : Nat) : paths (M+1) 1 = 1 := by
  induction M with
  | zero => simp [paths]
  | succ M ih => simp [paths, ih]

/-- The explicit target row: `pathsRow m n` is the `SnocList` of `paths (m+1) 1, …, paths (m+1)
    (n+1)` (grid-row `m+1`, columns `1..n+1`), snoc-built in increasing column order. -/
def pathsRow (m : Nat) : Nat → SnocList Nat Nat
  | 0 => SnocList.wrap (paths (m+1) 1)
  | (n+1) => SnocList.snoc (pathsRow m n) (paths (m+1) (n+2))

/-- The base row (`m = 0`, i.e. grid-row `1`) is the target row `pathsRow 0`. -/
theorem initRow_eq : ∀ n, initRow n = pathsRow 0 n
  | 0 => by simp [initRow, pathsRow, paths]
  | (n+1) => by
    have h1 : paths 1 (n+2) = 1 := by simp [paths]
    rw [initRow, pathsRow, initRow_eq n, h1]

/-- **Crux lemma**: scanning the target row of grid-row `m+1` produces exactly the target row of
    grid-row `m+2`, the running total landing on its corner value — the book recurrence
    `paths (M+1)(N+1) = paths M (N+1) + paths (M+1) N` (with `M := m+1`, `N := n+1`), read off via
    `simp [paths]` and reoriented to match `scanStep`'s accumulation order (`acc + p`, not
    `p + acc`) by `Nat.add_comm`. -/
theorem scanStep_pathsRow : ∀ m n,
    scanStep (pathsRow m n) = (paths (m+2) (n+1), pathsRow (m+1) n)
  | m, 0 => by
    have h1 : paths (m+2) 1 = 1 := paths_col1 (m+1)
    have h2 : paths (m+1) 1 = 1 := paths_col1 m
    simp [scanStep, pathsRow, h1, h2]
  | m, (n+1) => by
    have hbase : paths (m+2) (n+2) = paths (m+1) (n+2) + paths (m+2) (n+1) := by simp [paths]
    have hrec : paths (m+2) (n+1) + paths (m+1) (n+2) = paths (m+2) (n+2) := by
      rw [hbase, Nat.add_comm]
    simp only [pathsRow, scanStep, scanStep_pathsRow m n, hrec]

/-- `stepRow` on the target row of grid-row `m+1` gives the target row of grid-row `m+2`. -/
theorem stepRow_pathsRow (m n : Nat) : stepRow (pathsRow m n) = pathsRow (m+1) n := by
  show (scanStep (pathsRow m n)).2 = pathsRow (m+1) n
  rw [scanStep_pathsRow]

/-- **The row-fold IS the target row**: `rowAt m n` (the folded DP row) equals `pathsRow m n`
    (the row of `paths` values), for every row index `m` and column count `n`. -/
theorem rowAt_eq : ∀ m n, rowAt m n = pathsRow m n
  | 0, n => initRow_eq n
  | (m+1), n => by
    show stepRow (rowAt m n) = pathsRow (m+1) n
    rw [rowAt_eq m n, stepRow_pathsRow]

/-- **Correctness of the program**: `solveFn` computes exactly `paths`. -/
theorem solve_correct : ∀ m n, solveFn m n = paths m n
  | 0, _ => by simp [solveFn, paths]
  | (_+1), 0 => by simp [solveFn, paths]
  | (m+1), (n+1) => by
    show lastOf (rowAt m n) = paths (m+1) (n+1)
    rw [rowAt_eq m n]
    cases n with
    | zero => rfl
    | succ n => rfl

/-- **Correctness of the allegory program**: `solve = spec` as morphisms in `Rel(Set)`. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro mn k
  show k = solveFn mn.1 mn.2 ↔ k = paths mn.1 mn.2
  rw [solve_correct]

/-! ## Running the program -/

example : solveFn 3 7 = 28 := by decide
example : solveFn 3 3 = 6 := by decide
example : solveFn 1 5 = 1 := by decide
example : solveFn 5 1 = 1 := by decide

end Freyd.Alg.RelSet.LC62
