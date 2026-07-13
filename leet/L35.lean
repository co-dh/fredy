/-
  LeetCode 35 — Search Insert Position — as an ALLEGORY PROGRAM.

  Problem: given a SORTED `xs : List Int` and a `target`, return the index where `target` is (or
  would be inserted to keep `xs` sorted).

  1. **Data** — a plain `List Int` (no `SnocList` engine needed: the scan is a single
     left-to-right pass, as in `L1`/`L11`).
  2. **Program** — `insertPosFn xs target` is a LINEAR scan for the first index whose element is
     `≥ target`: base case `0`; step `if target ≤ x then 0 else 1 + insertPosFn xs target`.
  3. **Specification** — the returned index `i` SPLITS `xs`: `i ≤ xs.length`, every element
     strictly before `i` is `< target`, and the element AT `i` (if any) is `≥ target`.
  4. **Correctness** — `insertPos_correct`, one structural induction on `xs`.

  Reuses `leet.L242`'s `Sorted : List Int → Prop` (`leetcode.md` S22/S24: the "all-later-elements"
  phrasing).  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import leet.L242

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC35

open Freyd
open Freyd.Alg.RelSet.LC242 (Sorted)

/-! ## The program: a left-to-right scan for the first index `≥ target` -/

/-- `insertPosFn xs target` — the first index in `xs` whose element is `≥ target` (i.e. where
    `target` should be inserted to keep a sorted list sorted). -/
def insertPosFn : List Int → Int → Nat
  | [], _ => 0
  | x :: xs, t => if t ≤ x then 0 else 1 + insertPosFn xs t

@[simp] theorem insertPosFn_nil (t : Int) : insertPosFn [] t = 0 := rfl
@[simp] theorem insertPosFn_cons (x t : Int) (xs : List Int) :
    insertPosFn (x :: xs) t = if t ≤ x then 0 else 1 + insertPosFn xs t := rfl

/-! ## `Rel(Set)` packaging -/

/-- The input object: a list of integers paired with a target. -/
abbrev Input : RelSet.{0} := ⟨List Int × Int⟩
/-- The answer object: an index. -/
abbrev Ans : RelSet.{0} := ⟨Nat⟩

/-- **The allegory program**: LeetCode 35's solution as a morphism `Input ⟶ Ans` in `Rel(Set)`. -/
def solve : Input ⟶ Ans := graph (fun p : List Int × Int => insertPosFn p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map (fun p : List Int × Int => insertPosFn p.1 p.2)

/-! ## Correctness: the returned index splits `xs` at `target` -/

/-- **`insertPosFn` splits `xs` at `target`**: the index is in range; every element strictly
    before it is `< target`; the element at it (if any) is `≥ target`.  This is the "first index
    `≥ target`" property BY CONSTRUCTION of the scan, true of any list — the head-bound half of
    `Sorted xs` (`∀ y ∈ xs.tail, xs.head ≤ y`) is never consulted directly below, only `Sorted`'s
    recursive tail is needed to invoke the IH.  `Sorted` genuinely bites at the CLOSED FORM
    (`insertPosFn_eq_filter_length` below), which needs it via transitivity. -/
theorem insertPos_correct : ∀ (xs : List Int) (target : Int), Sorted xs →
    (insertPosFn xs target ≤ xs.length) ∧
    (∀ k v, k < insertPosFn xs target → xs[k]? = some v → v < target) ∧
    (∀ v, xs[insertPosFn xs target]? = some v → target ≤ v) := by
  intro xs
  induction xs with
  | nil =>
    intro target _
    refine ⟨by simp, fun k v hk _ => ?_, fun v hv => ?_⟩
    · simp at hk
    · simp at hv
  | cons x xs ih =>
    intro target hs
    obtain ⟨_hhead, hs'⟩ := hs
    obtain ⟨ih1, ih2, ih3⟩ := ih target hs'
    rw [insertPosFn_cons]
    split
    · rename_i h
      refine ⟨Nat.zero_le _, fun k v hk _ => absurd hk (by omega), fun v hv => ?_⟩
      rw [List.getElem?_cons_zero] at hv
      have hvx : x = v := by injection hv
      omega
    · rename_i h
      have hx : x < target := by omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · intro k v hk hget
        cases k with
        | zero =>
          rw [List.getElem?_cons_zero] at hget
          have hvx : x = v := by injection hget
          omega
        | succ k' =>
          rw [List.getElem?_cons_succ] at hget
          exact ih2 k' v (by omega) hget
      · intro v hv
        rw [show 1 + insertPosFn xs target = insertPosFn xs target + 1 from by omega,
            List.getElem?_cons_succ] at hv
        exact ih3 v hv

/-! ## Closed form: `insertPosFn` counts the elements strictly below `target` — where `Sorted`
    genuinely bites, via transitivity of `≤` through the head. -/

/-- If every element of `xs` is `≥ target`, `filter (· < target)` empties it out.  `p`/`a`/`l` are
    passed EXPLICITLY to `List.filter_cons_of_neg` (`L230`'s trap: implicit args let `rw` mis-unify
    against `decide`'s own internal application). -/
theorem filter_lt_eq_nil_of_forall_ge : ∀ (xs : List Int) (target : Int),
    (∀ a ∈ xs, target ≤ a) → xs.filter (fun a => decide (a < target)) = []
  | [], _, _ => rfl
  | b :: s, target, hv => by
      have hvb : target ≤ b := hv b List.mem_cons_self
      have hcond : ¬ (fun a : Int => decide (a < target)) b := by
        simp only [decide_eq_true_eq]; omega
      rw [List.filter_cons_of_neg (p := fun a : Int => decide (a < target)) (a := b) (l := s) hcond]
      exact filter_lt_eq_nil_of_forall_ge s target
        (fun a ha => hv a (List.mem_cons.mpr (Or.inr ha)))

/-- **Closed form**: `insertPosFn` is exactly the count of elements of `xs` strictly below
    `target` — the "insert index = number of smaller elements" reading of the problem.  Unlike
    `insertPos_correct`, this genuinely needs `Sorted`: the `target ≤ x` branch must rule out any
    LATER element of `xs` being `< target`, which needs `target ≤ x ≤ y` (transitivity through the
    head bound), not just the IH. -/
theorem insertPosFn_eq_filter_length : ∀ (xs : List Int) (target : Int), Sorted xs →
    insertPosFn xs target = (xs.filter (fun a => decide (a < target))).length := by
  intro xs
  induction xs with
  | nil => intro target _; simp
  | cons x xs ih =>
    intro target hs
    obtain ⟨hhead, hs'⟩ := hs
    rw [insertPosFn_cons]
    split
    · rename_i h
      have hge : ∀ a ∈ xs, target ≤ a := fun a ha => by have := hhead a ha; omega
      have hcond : ¬ (fun a : Int => decide (a < target)) x := by
        simp only [decide_eq_true_eq]; omega
      rw [List.filter_cons_of_neg (p := fun a : Int => decide (a < target)) (a := x) (l := xs)
        hcond, filter_lt_eq_nil_of_forall_ge xs target hge]
      rfl
    · rename_i h
      have hcond : (fun a : Int => decide (a < target)) x := by
        simp only [decide_eq_true_eq]; omega
      rw [List.filter_cons_of_pos (p := fun a : Int => decide (a < target)) (a := x) (l := xs)
        hcond, List.length_cons]
      have ihe := ih target hs'
      omega

/-! ## The morphism-equation headline (preconditioned on `Sorted`) -/

/-- The precondition coreflexive: the sub-identity on `Input` that passes only the `Sorted` inputs
    (LeetCode 35's stated precondition). -/
def pre : Input ⟶ Input := fun p q => p = q ∧ Sorted p.1

/-- **The specification** as a morphism `Input ⟶ Ans`: on a `Sorted` list, the answer is THE count
    of elements strictly below `target` (the "insert index = number of smaller elements" reading) —
    a program-independent closed form. -/
def spec : Input ⟶ Ans :=
  fun p v => Sorted p.1 ∧ v = (p.1.filter (fun a => decide (a < p.2))).length

/-- **The allegory-program headline**: `pre ≫ solve = spec` — restricted to sorted inputs, the
    scan `solve` is exactly the closed-form insert index. (Off the `Sorted` domain the composite is
    empty, matching that `insertPosFn`'s "first `≥ target`" scan is only the answer when sorted.) -/
theorem pre_solve_eq_spec : pre ≫ solve = spec := by
  apply hom_ext; intro p v
  constructor
  · rintro ⟨q, ⟨rfl, hsort⟩, hv⟩
    refine ⟨hsort, ?_⟩
    have hv' : v = insertPosFn p.1 p.2 := hv
    rw [hv', insertPosFn_eq_filter_length p.1 p.2 hsort]
  · rintro ⟨hsort, hv⟩
    refine ⟨p, ⟨rfl, hsort⟩, ?_⟩
    show v = insertPosFn p.1 p.2
    rw [hv, insertPosFn_eq_filter_length p.1 p.2 hsort]

/-! ## Running the program -/

example : insertPosFn [1, 3, 5, 6] 5 = 2 := by decide
example : insertPosFn [1, 3, 5, 6] 2 = 1 := by decide
example : insertPosFn [1, 3, 5, 6] 7 = 4 := by decide

end Freyd.Alg.RelSet.LC35
