/-
  LeetCode 234 — Palindrome Linked List — as an ALLEGORY PROGRAM.

  Problem: given a (singly) linked list, decide whether it reads the same forwards and backwards.

  Model the list as `List Int` — `L206`'s object `dList` (`leet/L206.lean`) — and REUSE `L206`'s
  reversal `revFn` as the reverse-and-compare test, instead of reimplementing reversal.

  1. **Program** — `isPalinFn xs := decide (xs = LC206.revFn xs)`, packaged as `solve := graph
     isPalinFn : dList ⟶ Bool` in `Rel(Set)` (a `Map`).

  2. **Honest specification** — `palin_correct : isPalinFn xs = true ↔ xs = xs.reverse` (Bool↔Prop
     reflection, `leetcode.md` skill S5). Since `LC206.revFn xs` is DEFINITIONALLY `xs.reverse`
     (`LC206.solve_correct`), this bridges to `L5`'s own `isPalin` property — the honest palindrome
     predicate, not a tautological restatement of `isPalinFn`.

  3. **Extra content beyond the bare reflection** — a palindrome test must itself be invariant under
     reversing the input: `isPalinFn xs = isPalinFn xs.reverse`, via `List.reverse_reverse`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import leet.L206
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC234

open Freyd Freyd.Alg.RelSet.LC206

/-! ## Data: reuse `L206`'s list object `dList`; answer = `Bool` -/

/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## The program: reverse-and-compare, reusing `L206`'s `revFn` -/

/-- The concrete program: is `xs` equal to its own reversal? Reuses `L206`'s `revFn` rather than
    reimplementing list reversal. -/
def isPalinFn (xs : List Int) : Bool := decide (xs = revFn xs)

/-- **The allegory program**: LeetCode 234's solution as a morphism `dList ⟶ Bool` in `Rel(Set)`. -/
def solve : dList ⟶ dBool := graph isPalinFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map isPalinFn

/-! ## Correctness: the honest palindrome property -/

/-- **Correctness of the allegory program** (Bool↔Prop reflection, `leetcode.md` skill S5):
    `isPalinFn xs` is `true` exactly when `xs` equals its own reversal — `L5`'s `isPalin` property. -/
theorem palin_correct (xs : List Int) : isPalinFn xs = true ↔ xs = xs.reverse := by
  show decide (xs = revFn xs) = true ↔ xs = xs.reverse
  rw [decide_eq_true_eq, solve_correct xs]

/-! ## Extra content: a palindrome test is reversal-invariant -/

/-- Two booleans that agree on being `true` are equal (Bool extensionality). -/
theorem bool_eq_of_iff_true {b c : Bool} (h : (b = true) ↔ (c = true)) : b = c := by
  cases b with
  | true => cases c with
    | true => rfl
    | false => exact (h.mp rfl).symm
  | false => cases c with
    | true => exact h.mpr rfl
    | false => rfl

/-- **Reversal invariance**: a palindrome test gives the same verdict on `xs` and on `xs` reversed —
    genuine content beyond `palin_correct` alone (`palin_correct` only characterizes ONE call; this
    relates two calls), via `List.reverse_reverse`. -/
theorem palin_reversal_invariant (xs : List Int) : isPalinFn xs = isPalinFn xs.reverse := by
  have h1 := palin_correct xs
  have h2 := palin_correct xs.reverse
  rw [List.reverse_reverse] at h2
  exact bool_eq_of_iff_true ((h1.trans (Iff.intro Eq.symm Eq.symm)).trans h2.symm)

/-! ## Specification: the correct boolean answer -/

/-- The **specification** as a morphism `dList ⟶ Bool` in `Rel(Set)`: `b` is THE correct boolean
    answer to "is `xs` a palindrome?" -/
def spec : dList ⟶ dBool := fun xs b => (b = true ↔ xs = xs.reverse)

/-- **`solve` equals `spec` as relations** (the allegory-program correctness statement). -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro xs b
  show (b = isPalinFn xs) ↔ (b = true ↔ xs = xs.reverse)
  constructor
  · intro h; rw [h]; exact palin_correct xs
  · intro h
    have h' : (b = true) ↔ (isPalinFn xs = true) := h.trans (palin_correct xs).symm
    exact bool_eq_of_iff_true h'

/-! ## Running the program -/

example : isPalinFn ([1, 2, 2, 1] : List Int) = true := by decide
example : isPalinFn ([1, 2] : List Int) = false := by decide
example : isPalinFn ([1] : List Int) = true := by decide

end Freyd.Alg.RelSet.LC234
