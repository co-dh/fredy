/-
  LeetCode 45 — Jump Game II — as an ALLEGORY PROGRAM.

  Problem: given `nums = x₀,…,x_{n-1}` (non-negative max-jump lengths, one per index; `nums[i]`
  is the farthest offset one may jump FROM index `i`), starting at index `0`, find the MINIMUM
  number of jumps to reach the last index `n-1`.  LC guarantees the last index is always
  reachable, so we do not need an "unreachable" case.

  Same recipe as `leet/L121.lean`/`leet/L53.lean` (see `Freyd/leetcode.md`), but a MIN-extremum
  (like the greedy theorem 7.2, `AOP/A7_2.lean`) rather than a max-extremum:

  1. **Data** — `nums` is the initial algebra `SnocList ℕ ℕ` of `F X = ℕ + X × ℕ`
     (`AOP.A6_SnocList`); `wrap x` is a single-element array, `snoc xs p` appends `p`.

  2. **Program** — the classic O(n) LAYERED-GREEDY sweep: scan positions left to right, extending
     `farthest := max farthest (idx + nums[idx])`; every time the scan reaches `curEnd` (the
     frontier reachable within the jumps committed so far) it commits one more jump and advances
     the frontier to `farthest`.  The scan runs only over the PREFIX excluding the true last
     index (matching the textbook `for i in 0 to n-2`) — `nums[n-1]`'s own value never matters,
     since no jump is ever taken FROM the destination.

  3. **Specification** — `Reach xs i j`: index `i` is reachable from index `0` using AT MOST `j`
     jumps (upward-closed in `j` by construction — "at most", not "exactly", so it composes
     cleanly with the `min(≤)` extremum).  `jumpsTo xs k := Reach xs (size xs - 1) k`.  LeetCode
     45 asks for the LEAST such `k`, i.e. `min (≤) · Λ jumpsTo` in `Rel(Set)`.

  4. **Correctness** — `solve` computes exactly that minimum: it returns an achievable jump count
     (`solve_reach`, giving `solve ⊑ jumpsTo`, ACHIEVABILITY) and no smaller count is achievable
     (`jumpsTo_ge_solve`, DOMINATION/optimality).  Together (`solve_correct`) this is
     `solve = min (≤) · Λ jumpsTo`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC45

open Freyd Freyd.Alg.RelSet.SL

/-! ## Natural-number `max` (mathlib-free, so we control the rewrite lemmas; cf. L121/L53's
    `imax` on `ℤ` — copied here specialised to `ℕ`, which is what `nums`/indices live in). -/

def nmax (a b : Nat) : Nat := if a ≤ b then b else a

theorem nmax_ge_left  (a b : Nat) : a ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_ge_right (a b : Nat) : b ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_eq_or (a b : Nat) : nmax a b = a ∨ nmax a b = b := by
  unfold nmax; split; exacts [Or.inr rfl, Or.inl rfl]

/-! ## Data: `nums` as a non-empty snoc-list of naturals -/

/-- The object of jump-length arrays in `Rel(Set)` — `SnocList ℕ ℕ` (`wrap x` = single entry,
    `snoc xs p` = `xs` with a new final entry `p`). -/
abbrev Arr : RelSet.{0} := dSL Nat Nat
/-- The object of naturals (jump counts) in `Rel(Set)`. -/
abbrev dN : RelSet.{0} := ⟨Nat⟩

/-! ## Indexing infrastructure: `size`/`nth`, the bridge between the SnocList and the textbook
    index-based statement of the problem. -/

/-- The number of entries of `xs` (always `≥ 1`). -/
def size : SnocList Nat Nat → Nat
  | .wrap _ => 1
  | .snoc xs _ => size xs + 1

theorem size_pos : ∀ xs, 1 ≤ size xs
  | .wrap _ => Nat.le_refl 1
  | .snoc xs _ => by have := size_pos xs; show 1 ≤ size xs + 1; omega

/-- The `i`-th entry of `xs` (0-indexed).  Only meaningful for `i < size xs`; out-of-range
    queries return an arbitrary value and are never consulted by the theorems below. -/
def nth : SnocList Nat Nat → Nat → Nat
  | .wrap x, _ => x
  | .snoc xs d, i => if i = size xs then d else nth xs i

@[simp] theorem nth_last (xs : SnocList Nat Nat) (d : Nat) : nth (.snoc xs d) (size xs) = d := by
  unfold nth; simp

theorem nth_lt (xs : SnocList Nat Nat) (d : Nat) (i : Nat) (h : i < size xs) :
    nth (.snoc xs d) i = nth xs i := by
  show (if i = size xs then d else nth xs i) = nth xs i
  rw [if_neg (by omega)]

/-! ## The program: layered greedy, state `(idx, curEnd, farthest, jumps)` -/

/-- The fold's running state after processing all entries of a (proper prefix) list:
    `idx` = the last processed index, `curEnd` = the frontier reachable within `jumps` jumps,
    `farthest` = the best frontier seen so far for the NEXT jump, `jumps` = jumps committed. -/
def foldFn : SnocList Nat Nat → Nat × Nat × Nat × Nat
  | .wrap x => (0, x, x, 1)
  | .snoc dec dig =>
    let (idx, curEnd, farthest, jumps) := foldFn dec
    let idx' := idx + 1
    let farthest' := nmax farthest (idx' + dig)
    if idx' = curEnd then (idx', farthest', farthest', jumps + 1) else (idx', curEnd, farthest', jumps)

/-- **The allegory program's underlying function**: the minimum number of jumps from index `0`
    to the last index.  A single-entry array needs `0` jumps (already there); a longer array's
    answer is the jump count committed while scanning its PREFIX (everything but the true last
    entry — matching the textbook `for i in 0 to n-2`, since no jump is ever taken FROM the
    destination, so the last entry's own value is irrelevant). -/
def solveFn : SnocList Nat Nat → Nat
  | .wrap _ => 0
  | .snoc dec _ => (foldFn dec).2.2.2

/-- **The allegory program**: LeetCode 45's solution as a morphism `Arr ⟶ ℕ` in `Rel(Set)`. -/
def solve : Arr ⟶ dN := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## Specification: `k` jumps suffice to reach the last index -/

/-- `Reach xs i j` — index `i` is reachable from index `0` using AT MOST `j` jumps: either it
    was already reachable within `j - 1` jumps (padding, keeping the predicate upward-closed in
    `j`), or one more jump lands on it from some `i'` reachable within `j - 1` jumps. -/
def Reach (xs : SnocList Nat Nat) : Nat → Nat → Prop
  | i, 0 => i = 0
  | i, j + 1 => Reach xs i j ∨ ∃ i', Reach xs i' j ∧ i' < i ∧ i ≤ i' + nth xs i'

/-- `Reach` is upward-closed in the jump budget. -/
theorem reach_mono (xs : SnocList Nat Nat) (i j : Nat) (h : Reach xs i j) : Reach xs i (j + 1) :=
  Or.inl h

theorem reach_mono_le (xs : SnocList Nat Nat) (i j j' : Nat) (hle : j ≤ j') (h : Reach xs i j) :
    Reach xs i j' := by
  induction j' with
  | zero =>
    have hj : j = 0 := by omega
    rwa [hj] at h
  | succ n ih =>
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · exact reach_mono xs i n (ih (by omega))
    · have hj : j = n + 1 := by omega
      rwa [hj] at h

/-- The **specification** as a morphism `Arr ⟶ ℕ` in `Rel(Set)`: `k` is a valid jump budget
    reaching the last index of `xs`.  LeetCode 45 asks for its `≤`-minimum, `min (≤) · Λ jumpsTo`. -/
def jumpsTo (xs : SnocList Nat Nat) (k : Nat) : Prop := Reach xs (size xs - 1) k

def spec : Arr ⟶ dN := fun xs k => jumpsTo xs k

/-! ## Running the program -/

/-- Build an array from a first entry and the rest, in index order. -/
def ofList (first : Nat) (rest : List Nat) : SnocList Nat Nat :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 2 [3, 1, 1, 4]) = 2 := by decide
example : solveFn (ofList 2 [3, 0, 1, 4]) = 2 := by decide
example : solveFn (ofList 0 []) = 0 := by decide
example : solveFn (ofList 1 [1]) = 1 := by decide

end Freyd.Alg.RelSet.LC45
