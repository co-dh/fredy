/-
  LeetCode 217 — Contains Duplicate — as an ALLEGORY PROGRAM.

  Problem: given a non-empty array of integers, return `true` iff some value occurs at least twice.

  Unlike `leet/L121.lean`/`leet/L53.lean` (an OPTIMUM `max(≤)·Λ spec`), this is a DECISION problem:
  the answer object is `Bool`, and correctness is a plain `iff`, `solveFn xs = true ↔ dupP xs`, not an
  extremum.  Same data/program recipe otherwise (`AOP.A6_SnocList`, `Fredy/leetcode.md` skill S0):

  1. **Data** — the array is the initial algebra `SnocList ℤ ℤ` of `F X = ℤ + X × ℤ`; `wrap x` is a
     single-element array, `snoc xs p` appends `p`.

  2. **Program** — a *nested* fold: `memB xs p` (Bool "does `p` occur in `xs`?", itself a fold over
     `xs`) and `hasDup xs` (Bool "does `xs` have an internal duplicate?"; the `snoc` step checks
     `hasDup xs || memB xs q` — either the prefix already had a dup, or the new element `q` matches
     something in the prefix).  `solve := graph hasDup : Arr ⟶ Bool` is the allegory program.

  3. **Specification** — the mirrored Prop relations `memP`/`dupP`.  `spec : Arr ⟶ Bool` relates `xs`
     to the (unique) correct boolean answer via `b = true ↔ dupP xs`.

  4. **Correctness** — a reflection bridge `memB_iff_memP : memB xs p = true ↔ memP xs p` (induction
     on `xs`), lifted to `hasDup_correct`/`solve_correct : solveFn xs = true ↔ dupP xs`.  `solve = spec`
     then follows pointwise (`solve_eq_spec`) via a Bool-extensionality lemma (`bool_eq_of_iff_true`:
     two booleans agreeing on `= true` are equal).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC217

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: array as a non-empty snoc-list of integers; answer = `Bool` -/

/-- The object of arrays in `Rel(Set)` — `SnocList ℤ ℤ`. -/
abbrev Arr : RelSet.{0} := dSL Int Int
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## The program: a boolean membership fold, then a boolean "any duplicate" fold -/

/-- Boolean equality test on `ℤ`. -/
def eqi (a b : Int) : Bool := decide (a = b)

/-- `eqi` reflects `Int` equality. -/
theorem eqi_eq_true {a b : Int} : eqi a b = true ↔ a = b := by
  show decide (a = b) = true ↔ a = b
  rw [decide_eq_true_eq]

/-- `memB xs p` — does `p` occur somewhere in `xs`? (a fold over `xs`). -/
def memB : SnocList Int Int → Int → Bool
  | SnocList.wrap x => fun p => eqi p x
  | SnocList.snoc xs q => fun p => memB xs p || eqi p q

/-- `hasDup xs` — does `xs` contain some value at least twice? -/
def hasDup : SnocList Int Int → Bool
  | SnocList.wrap _ => false
  | SnocList.snoc xs q => hasDup xs || memB xs q

/-- The answer function. -/
def solveFn : SnocList Int Int → Bool := hasDup

/-- **The allegory program**: LeetCode 217's solution as a morphism `Arr ⟶ Bool` in `Rel(Set)`. -/
def solve : Arr ⟶ dBool := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## Specification: does a value repeat? -/

/-- `memP xs p` — the Prop mirror of `memB`: `p` occurs somewhere in `xs`. -/
def memP : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun p => p = x
  | SnocList.snoc xs q => fun p => memP xs p ∨ p = q

/-- `dupP xs` — the Prop mirror of `hasDup`: `xs` contains some value at least twice. -/
def dupP : SnocList Int Int → Prop
  | SnocList.wrap _ => False
  | SnocList.snoc xs q => dupP xs ∨ memP xs q

/-- The **specification** as a morphism `Arr ⟶ Bool` in `Rel(Set)`: `b` is THE correct boolean
    answer to "does `xs` contain a duplicate?" -/
def spec : Arr ⟶ dBool := fun xs b => (b = true ↔ dupP xs)

/-! ## Bridge: the boolean fold reflects the Prop relation -/

/-- **The bridge lemma**: `memB` computes `memP`. -/
theorem memB_iff_memP : ∀ (xs : SnocList Int Int) (p : Int), memB xs p = true ↔ memP xs p := by
  intro xs; induction xs with
  | wrap x =>
    intro p
    show eqi p x = true ↔ p = x
    exact eqi_eq_true
  | snoc xs q ih =>
    intro p
    show (memB xs p || eqi p q) = true ↔ (memP xs p ∨ p = q)
    rw [Bool.or_eq_true, ih p, eqi_eq_true]

/-! ## Correctness: `solve` decides `dupP` -/

/-- **`hasDup` computes `dupP`**: the DECISION-problem correctness shape — an `iff`, not an
    extremum. -/
theorem hasDup_correct : ∀ xs : SnocList Int Int, hasDup xs = true ↔ dupP xs := by
  intro xs; induction xs with
  | wrap x =>
    show (false : Bool) = true ↔ False
    exact ⟨fun h => (nomatch h), False.elim⟩
  | snoc xs q ih =>
    show (hasDup xs || memB xs q) = true ↔ (dupP xs ∨ memP xs q)
    rw [Bool.or_eq_true, ih, memB_iff_memP xs q]

/-- **Correctness of the allegory program**: `solveFn xs = true ↔ dupP xs`. -/
theorem solve_correct (xs : SnocList Int Int) : solveFn xs = true ↔ dupP xs := hasDup_correct xs

/-- Two booleans that agree on being `true` are equal (Bool extensionality). -/
theorem bool_eq_of_iff_true {b c : Bool} (h : (b = true) ↔ (c = true)) : b = c := by
  cases b with
  | true => cases c with
    | true => rfl
    | false => exact (h.mp rfl).symm
  | false => cases c with
    | true => exact h.mpr rfl
    | false => rfl

/-- **`solve` equals `spec` as relations** (the allegory-program correctness statement). -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro xs b
  show (b = solveFn xs) ↔ (b = true ↔ dupP xs)
  constructor
  · intro h; rw [h]; exact solve_correct xs
  · intro h
    have h' : (b = true) ↔ (solveFn xs = true) := h.trans (solve_correct xs).symm
    exact bool_eq_of_iff_true h'

/-! ## Running the program -/

/-- Build an array from a first element and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : hasDup (ofList 1 [2, 3, 1]) = true := by decide
example : hasDup (ofList 1 [2, 3, 4]) = false := by decide
example : hasDup (ofList 1 []) = false := by decide
example : hasDup (ofList 1 [1]) = true := by decide

end Freyd.Alg.RelSet.LC217
