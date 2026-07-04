/-
  LeetCode 125 — Valid Palindrome — as an ALLEGORY PROGRAM.

  Problem: given a sequence of characters, decide whether it reads the same forwards and
  backwards.  (The real LeetCode problem also filters to alphanumeric characters and case-folds
  before comparing; that is a routine pre-pass on the input list and is SKIPPED here — we solve
  the core decision "is this sequence a palindrome?", chars as `Int`.)

  Same data/program recipe as `Fredy/L217.lean` (`Fredy.A6_SnocList`, `Fredy/leetcode.md` S0/S5):
  this is a DECISION problem, so correctness is a plain `iff`, not a refinement+domination
  extremum.

  1. **Data** — the sequence is the initial algebra `SnocList Int Int` (§A6_SnocList).

  2. **Program** — `toList : SnocList Int Int → List Int` unpacks the (right-append) `SnocList`
     into a plain `List Int`, giving symmetric front/back access; `palinFn xs` then decides
     `toList xs = (toList xs).reverse` via `List Int`'s `DecidableEq`.

  3. **Specification** — `IsPalin xs : Prop := toList xs = (toList xs).reverse` ("the sequence
     reads the same both ways"), stated directly in terms of `List.reverse` (not re-derived
     structurally), so the bridge to `palinFn` is honest.

  4. **Correctness** — `solve_correct : palinFn xs = true ↔ IsPalin xs` is immediate from
     `decide_eq_true_eq`; the real content is `toList`'s two equation lemmas.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC125

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: a sequence of characters, chars = `Int`; answer = `Bool` -/

/-- The object of character sequences in `Rel(Set)` — `SnocList Int Int`. -/
abbrev Arr : RelSet.{0} := dSL Int Int
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## `toList` — unpack the (right-append) `SnocList` into a plain `List`, for symmetric
    front/back access (`List.reverse`) -/

/-- `toList xs` — the elements of `xs` in index order, as a plain `List Int`. -/
def toList : SnocList Int Int → List Int
  | SnocList.wrap x => [x]
  | SnocList.snoc xs q => toList xs ++ [q]

@[simp] theorem toList_wrap (x : Int) : toList (SnocList.wrap x) = [x] := rfl
@[simp] theorem toList_snoc (xs : SnocList Int Int) (q : Int) :
    toList (SnocList.snoc xs q) = toList xs ++ [q] := rfl

/-! ## The program: decide reverse-equality on the unpacked list -/

/-- The answer function: does `xs` read the same forwards and backwards? -/
def palinFn (xs : SnocList Int Int) : Bool := decide (toList xs = (toList xs).reverse)

/-- **The allegory program**: LeetCode 125's solution as a morphism `Arr ⟶ Bool` in `Rel(Set)`. -/
def solve : Arr ⟶ dBool := graph palinFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map palinFn

/-! ## Specification: a sequence reads the same both ways -/

/-- **The specification**: `xs` is a palindrome iff its unpacked list equals its own reverse. -/
def IsPalin (xs : SnocList Int Int) : Prop := toList xs = (toList xs).reverse

/-! ## Correctness: `solve` decides `IsPalin` -/

/-- **`palinFn` decides `IsPalin`**: the DECISION-problem correctness shape — an `iff`, not an
    extremum. -/
theorem solve_correct (xs : SnocList Int Int) : palinFn xs = true ↔ IsPalin xs := by
  show decide (toList xs = (toList xs).reverse) = true ↔ (toList xs = (toList xs).reverse)
  rw [decide_eq_true_eq]

/-! ## Running the program -/

/-- Build a sequence from a first element and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : palinFn (ofList 97 [98, 97]) = true := by decide         -- "aba"
example : palinFn (ofList 97 [98]) = false := by decide            -- "ab"
example : palinFn (ofList 97 [98, 98, 97]) = true := by decide     -- "abba"
example : palinFn (ofList 1 []) = true := by decide                -- single char

end Freyd.Alg.RelSet.LC125
