/-
  LeetCode 23 — Merge k Sorted Lists — as an ALLEGORY PROGRAM.

  Problem: given `lists : List (List Int)`, each individually sorted (non-decreasing), merge them
  all into one sorted list containing exactly all their elements, WITH MULTIPLICITY.

  This is a straight FOLD of `L21`'s binary merge (`LC21.mergeFn`) over the list of lists — no new
  recursion scheme, no new fuel trick, DRY reuse of the whole `L21` correctness proof:

  1. **Program** — `mergeKFn lists := lists.foldr LC21.mergeFn []`, so
     `mergeKFn [l1,l2,l3] = LC21.mergeFn l1 (LC21.mergeFn l2 (LC21.mergeFn l3 []))`.
  2. **Specification** — the honest LeetCode spec: precondition `∀ l ∈ lists, LC21.Sorted l`;
     conclusion **sortedness** of the merged output AND **exact SUMMED multiplicity**
     (`totalCount v lists`, the sum of `LC21.count v` over every input list, itself a plain fold).
  3. **Correctness = `merge_k_correct`** — induction on `lists`, one call to `LC21.merge_correct`
     per cons step (the fold's recursive structure IS the induction structure, so no separate
     "fold commutes with recursion" lemma is needed): base case `[]` is `rfl` on both conjuncts
     (`mergeKFn [] = []`, `totalCount v [] = 0`); the `l :: rest` step applies the IH to `rest`,
     then `LC21.merge_correct l (mergeKFn rest)` to combine sortedness and multiplicity, closing
     the multiplicity equation by `rfl` after two rewrites (`List.foldr`/`List.map` on `l :: rest`
     unfold definitionally to the same `count v l + totalCount v rest` shape the fold produces).

  Mathlib-free; `merge_k_correct` itself needs neither `Classical.choice` nor `Quot.sound` (pure
  `List`/`Nat`/`Int` reasoning delegating to `L21`'s already-axiom-clean `merge_correct`) — only
  the `Rel(Set)` packaging below pulls in `propext`/`Quot.sound`.
-/
import leet.L21

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC23

open Freyd

/-! ## Program: fold `L21`'s binary merge over the list of lists -/

/-- **The program**: merge `k` sorted lists by right-folding `L21`'s binary merge, base `[]`. -/
def mergeKFn (lists : List (List Int)) : List Int := lists.foldr LC21.mergeFn []

/-! ## Specification: sortedness and summed multiplicity across all input lists -/

/-- The total multiset count of `v` across every list in `lists`, as a plain fold of `L21.count`. -/
def totalCount (v : Int) (lists : List (List Int)) : Nat :=
  (lists.map (LC21.count v)).foldr (· + ·) 0

/-- **Correctness of the allegory program** (the headline theorem): given a list of SORTED input
    lists, `mergeKFn` returns a SORTED list whose multiset is exactly the SUM (with multiplicity)
    of every input list's multiset. -/
theorem merge_k_correct : ∀ lists : List (List Int), (∀ l ∈ lists, LC21.Sorted l) →
    LC21.Sorted (mergeKFn lists) ∧ ∀ v, LC21.count v (mergeKFn lists) = totalCount v lists := by
  intro lists
  induction lists with
  | nil =>
    intro _
    exact ⟨trivial, fun _ => rfl⟩
  | cons l rest ih =>
    intro hall
    have hl : LC21.Sorted l := hall l List.mem_cons_self
    have hrest : ∀ l' ∈ rest, LC21.Sorted l' := fun l' hl' => hall l' (List.mem_cons_of_mem l hl')
    obtain ⟨hSrest, hCrest⟩ := ih hrest
    obtain ⟨hSmerge, hCmerge⟩ := LC21.merge_correct l (mergeKFn rest) hl hSrest
    refine ⟨hSmerge, fun v => ?_⟩
    show LC21.count v (LC21.mergeFn l (mergeKFn rest)) = totalCount v (l :: rest)
    rw [hCmerge v, hCrest v]
    rfl

/-! ## `Rel(Set)` packaging -/

/-- The input object: the list of sorted lists to merge. -/
abbrev dInput : RelSet.{0} := ⟨List (List Int)⟩
/-- The answer object: the merged list. -/
abbrev dAns : RelSet.{0} := ⟨List Int⟩

/-- **The allegory program**: LeetCode 23's k-way merge as a morphism `dInput ⟶ dAns`. -/
def solve : dInput ⟶ dAns := graph mergeKFn

/-- `solve` is a `Map` — a genuine function, via the `graph`/`Map` route. -/
theorem solve_map : Map solve := graph_map mergeKFn

/-- **The specification** as a morphism `dInput ⟶ dAns` in `Rel(Set)`: given a list of sorted
    inputs, the output is sorted and its multiset is the sum of theirs. -/
def spec : dInput ⟶ dAns := fun lists l =>
  (∀ l' ∈ lists, LC21.Sorted l') → LC21.Sorted l ∧ ∀ v, LC21.count v l = totalCount v lists

/-- **The program refines the specification** (in fact computes it exactly): every answer `solve`
    returns satisfies `spec`. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun lists l h => ?_)
  have hl : l = mergeKFn lists := h
  intro hall
  rw [hl]
  exact merge_k_correct lists hall

/-! ## Headline: on inputs whose members are all sorted, `solve` IS `spec` -/

/-- The precondition coreflexive: the sub-identity on WELL-FORMED inputs (every member sorted). -/
def pre : dInput ⟶ dInput := fun x y => x = y ∧ ∀ l' ∈ x, LC21.Sorted l'

/-- **Preconditioned headline**: restricted to inputs whose members are all sorted (`pre`), the
    program equals the specification — `pre ≫ solve = pre ≫ spec`.  Existence is `merge_k_correct`;
    uniqueness is `LC21.sorted_count_ext` (a sorted list is pinned by its multiset).  The
    precondition is required because the multiset-sum spec pins a UNIQUE list only under sortedness. -/
theorem pre_solve_eq_spec : pre ≫ solve = pre ≫ spec := by
  apply hom_ext; intro lists l
  rw [comp_apply, comp_apply]
  constructor
  · rintro ⟨y, ⟨rfl, hall⟩, hsolve⟩
    refine ⟨lists, ⟨rfl, hall⟩, ?_⟩
    intro _
    rw [(hsolve : l = mergeKFn lists)]; exact merge_k_correct lists hall
  · rintro ⟨y, ⟨rfl, hall⟩, hspec⟩
    refine ⟨lists, ⟨rfl, hall⟩, ?_⟩
    obtain ⟨hSl, hCl⟩ := hspec hall
    obtain ⟨hSm, hCm⟩ := merge_k_correct lists hall
    show l = mergeKFn lists
    exact LC21.sorted_count_ext l (mergeKFn lists) hSl hSm (fun v => by rw [hCl v, hCm v])

/-! ## Running the program -/

example : mergeKFn [[1, 4, 5], [1, 3, 4], [2, 6]] = [1, 1, 2, 3, 4, 4, 5, 6] := by decide
example : mergeKFn ([] : List (List Int)) = [] := by decide
example : mergeKFn ([[]] : List (List Int)) = [] := by decide
example : mergeKFn [[1], [], [-1, 3]] = [-1, 1, 3] := by decide

end Freyd.Alg.RelSet.LC23
