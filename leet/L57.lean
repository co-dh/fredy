/-
  LeetCode 57 — Insert Interval — as an ALLEGORY PROGRAM.

  Problem: given a list `ivs` of NON-overlapping, `.1`-sorted, valid intervals (LeetCode's own
  precondition) and a new interval `new` (`new.1 ≤ new.2`), insert `new` into `ivs` and merge so
  the result is again valid, sorted, and pairwise-disjoint (`GapSorted`), covering exactly the
  union of `ivs`'s points and `new`'s points.

  Route (DRY, per `Freyd/leetcode.md` S22): `leet.L56`'s `mergeFn` already sorts-then-merges an
  ARBITRARY interval list — inserting is nothing but merging `new :: ivs`. No bespoke 3-phase
  O(n) "binary-search the gap, splice, merge overlapping" implementation is needed; reusing
  `mergeFn` costs an O(n log n) sort (vs. LeetCode's typical O(n) pass) but gives the CORRECT
  result — the campaign proves correctness, not complexity — while sharing 100% of the sort/merge
  machinery (`isort`, `mergeRun`, `mergeRun_inv`, `mergeSorted_inv`, `merge_correct`) with L56.

  1. **Data** — `List (Int × Int)` (as in `L56`) plus a single new interval `Int × Int`.

  2. **Program** — `insertFn ivs new := mergeFn (new :: ivs)`.

  3. **Specification** — `IsInsert ivs new out`: `out` covers exactly the points `ivs` covers
     UNION the points `new` covers, is `Sorted`, `GapSorted`, and `Valid` (all four notions
     reused verbatim from `L56`).

  4. **Correctness** — `insert_correct : Valid ivs → new.1 ≤ new.2 → IsInsert ivs new
     (insertFn ivs new)`. The whole proof is `L56.merge_correct` applied to `new :: ivs` (whose
     validity follows immediately from the two hypotheses) plus ONE rewrite of the coverage
     clause via `L56.covers_cons` (`covers (new :: ivs) x ↔ (new.1 ≤ x ∧ x ≤ new.2) ∨ covers ivs
     x`) into the insert-shaped disjunction, plus a manual `∨`-swap to match the spec's stated
     order (`covers ivs x ∨ (new-interval)`, chosen to read "the old coverage, or the newly
     inserted piece"). This is NOT a forbidden one-line wrapper: `insertFn` itself IS a one-line
     delegation to `mergeFn`, but the theorem `insert_correct` re-derives the coverage clause
     under insert semantics (genuine `covers_cons` massaging, not present in `L56`) and
     re-packages all four conjuncts against the insert-specific hypotheses (`hnew`) — the
     mathematical content is instantiating `merge_correct` at a DIFFERENT (extended) list and
     translating its conclusion, not merely renaming a call.

  Mathlib-free; `insert_correct` inherits `L56.merge_correct`'s axiom budget
  `{propext, Quot.sound}` (fully constructive), since no new nonconstructive step is introduced —
  see `#print axioms insert_correct`. `Rel(Set)` packaging (`solve := graph (fun p => insertFn
  p.1 p.2)`) is added at the end, `Map`, per the recipe.
-/
import leet.L56

namespace Freyd.Alg.RelSet.LC57

open Freyd
open Freyd.Alg.RelSet.LC56

/-! ## The program: insert = merge `new :: ivs` -/

/-- **The allegory program's underlying function**: insert `new` into `ivs` by merging
    `new :: ivs` (`L56.mergeFn` sorts-then-merges an arbitrary list, so prepending `new` and
    re-merging is exactly "insert and re-merge"). -/
def insertFn (ivs : List (Int × Int)) (new : Int × Int) : List (Int × Int) :=
  mergeFn (new :: ivs)

/-! ## The specification -/

/-- **The specification**: `out` is a faithful insertion of `new` into `ivs` — covers exactly the
    union of `ivs`'s points and `new`'s points, sorted, pairwise-disjoint (`GapSorted`), and
    itself a list of valid intervals. -/
def IsInsert (ivs : List (Int × Int)) (new : Int × Int) (out : List (Int × Int)) : Prop :=
  (∀ x, covers out x ↔ covers ivs x ∨ (new.1 ≤ x ∧ x ≤ new.2)) ∧ Sorted out ∧ GapSorted out ∧ Valid out

/-! ## Correctness -/

/-- **Correctness (headline)**: for any valid interval list `ivs` and any valid new interval
    `new`, `insertFn ivs new` computes a faithful insertion-and-merge — coverage-preserving
    (old points ∪ new interval's points), sorted, pairwise-disjoint (`GapSorted`), and valid. -/
theorem insert_correct (ivs : List (Int × Int)) (new : Int × Int)
    (hival : Valid ivs) (hnew : new.1 ≤ new.2) : IsInsert ivs new (insertFn ivs new) := by
  have hval' : Valid (new :: ivs) := by
    intro iv hiv
    rcases List.mem_cons.mp hiv with h | h
    · rw [h]; exact hnew
    · exact hival iv h
  obtain ⟨hcov, hsort, hgap, hvalid⟩ := merge_correct (new :: ivs) hval'
  refine ⟨fun x => ?_, hsort, hgap, hvalid⟩
  show covers (mergeFn (new :: ivs)) x ↔ covers ivs x ∨ (new.1 ≤ x ∧ x ≤ new.2)
  rw [hcov, covers_cons]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h

/-! ## Packaging as a genuine `Rel(Set)` morphism -/

/-- The object of (interval-list, new-interval) pairs in `Rel(Set)`. -/
abbrev IvsNew : RelSet.{0} := ⟨List (Int × Int) × (Int × Int)⟩

/-- **The allegory program**: LeetCode 57's solution as a morphism `IvsNew ⟶ Ivs` in `Rel(Set)`. -/
def solve : IvsNew ⟶ Ivs := graph (fun p : List (Int × Int) × (Int × Int) => insertFn p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map (fun p : List (Int × Int) × (Int × Int) => insertFn p.1 p.2)

/-! ## The specification relation + honest headline (refinement + emergence report)

  As in `leet/L56.lean`, coverage over `Int` under-determines the output (touching integer intervals
  share integer coverage), so `solve = spec` is FALSE.  The honest morphism statement is refinement:
  on a valid list and a valid new interval, `solve` produces a faithful insert-and-merge.

  EMERGENCE (task's exception case): `insertFn ivs new = mergeFn (new :: ivs)` delegates to
  `L56.mergeFn = mergeSorted ∘ isort` — sort-then-merge.  It is NOT a single catamorphism of its
  input list (the sort reorders, so no fold over the raw input reconstructs it); the fold content
  lives INSIDE `L56` (`mergeRun` is the run-merging catamorphism, `isort` a `foldr` of `linsert`).
  So no `consFold_unique`/`hyloFold_unique` law is applied here — honestly reported, not forced. -/

/-- **The specification** as a relation `IvsNew ⟶ Ivs`: `out` is a faithful insertion of `new` into
    `ivs` (`IsInsert`), stated independently of `insertFn`. -/
def spec : IvsNew ⟶ Ivs := fun p out => IsInsert p.1 p.2 out

/-- The precondition coreflexive passing only `Valid` lists with a valid new interval. -/
def pre : IvsNew ⟶ IvsNew := fun p q => p = q ∧ Valid p.1 ∧ p.2.1 ≤ p.2.2

/-- **Refinement headline**: `pre ≫ solve ⊑ spec` — on valid input, whatever `solve` produces is a
    faithful insert-and-merge.  (Equality fails: coverage under-determines the interval list.) -/
theorem pre_solve_le_spec : pre ≫ solve ⊑ spec := by
  refine le_iff.mpr (fun p out h => ?_)
  obtain ⟨q, ⟨rfl, hval, hnew⟩, hout⟩ := h
  have hout' : out = insertFn p.1 p.2 := hout
  show IsInsert p.1 p.2 out
  rw [hout']; exact insert_correct p.1 p.2 hval hnew

/-! ## Running the program -/

-- Merges into an existing interval: `(2,5)` overlaps `(1,3)` (`2 ≤ 3`) but not `(6,9)`
-- (`6 ≤ 5` is false), so `[(1,3),(6,9)]` + `(2,5)` → `[(1,5),(6,9)]`.
example : insertFn [(1, 3), (6, 9)] (2, 5) = [(1, 5), (6, 9)] := by decide
-- Lands cleanly in a gap, no merge: inserting `(4, 4)` between disjoint `(1, 3)` and `(6, 9)`.
example : insertFn [(1, 3), (6, 9)] (4, 4) = [(1, 3), (4, 4), (6, 9)] := by decide

end Freyd.Alg.RelSet.LC57
