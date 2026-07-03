/-
  LeetCode 20 — Valid Parentheses — as an ALLEGORY PROGRAM.

  Problem: a non-empty bracket sequence (`Bool`: `true` = open, `false` = close) is VALID iff it
  is balanced — scanning left to right, the running depth `#open − #close` never goes negative,
  and ends at `0`.  This is a DECISION problem (the answer is `Bool`), not an optimization one, so
  the "spec" is a two-sided `Prop` (`solve xs = true ↔ xs is balanced`), not a relation to be
  extremized.

  Only ONE bracket type is modelled (`Bool`); the three-type LeetCode original (`()[]{}`) is a
  routine extension — replace the leaf/element type `Bool` by an enum tagging open/close WITH a
  bracket kind, and add "the popped kind matches" to the close step. The depth-scan core (this
  file) is unchanged by that extension.

  Same recipe as `Fredy/L121.lean` (`Fredy/leetcode.md`, skill S0), but for a decision, not an
  optimum:

  1. **Data** — the sequence is the initial algebra `SnocList Bool Bool` (`Fredy.A6_SnocList`);
     `wrap b` is a single bracket, `snoc xs b` appends one.

  2. **Program** — the left-to-right depth scan is the fold with state `(depth : Int, ok : Bool)`,
     `ok` meaning "depth never went negative so far": open increments depth; close decrements it
     and requires the PRIOR depth `≥ 1` (else `ok` turns `false`, and stays `false` forever after).
     Packaged as a `Map solve : Toks ⟶ Bool := graph validFn`.

  3. **Specification** — `balancedP xs := neverNegP xs ∧ depthP xs = 0`, the textbook two-clause
     characterization of a balanced (one-type Dyck) word: every non-empty prefix has non-negative
     net depth (`neverNegP`), and the whole word's net depth is `0` (`depthP xs = 0`).

  4. **Correctness** — `solve_correct : validFn xs = true ↔ balancedP xs`, a genuine `Iff` (not a
     refinement/domination pair — there is no extremum here, just a decision). It follows from two
     INVARIANT lemmas relating the fold's state to the spec's structural definitions:
     `foldFn_fst_of_ok` (once `ok`, the fold's depth component IS `depthP`) and
     `foldFn_snd_iff_neverNeg` (`ok ↔ neverNegP`).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC20

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: bracket sequences as a snoc-list of `Bool` -/

/-- The object of bracket sequences in `Rel(Set)` — `SnocList Bool Bool` (`wrap b` = a single
    bracket, `snoc xs b` = `xs` with one more bracket appended; `true` = open, `false` = close). -/
abbrev Toks : RelSet.{0} := dSL Bool Bool
/-- The object of Booleans (the decision) in `Rel(Set)`. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## The program: a left-to-right depth scan, state `(depth, ok)` -/

/-- The concrete fold (structural recursion): running `(depth, ok)`, where `depth` counts
    `#open − #close` and `ok` records "depth never dipped below zero so far". A lone open starts
    at depth `1` (valid so far); a lone close is immediately invalid (`ok = false`) — its `depth`
    component is then a don't-care dummy value, never consulted again (see `foldFn_fst_of_ok`). -/
def foldFn : SnocList Bool Bool → Int × Bool
  | SnocList.wrap b => if b then (1, true) else (0, false)
  | SnocList.snoc xs b =>
      if b then ((foldFn xs).1 + 1, (foldFn xs).2)
      else ((foldFn xs).1 - 1, (foldFn xs).2 && decide (1 ≤ (foldFn xs).1))

@[simp] theorem foldFn_wrap (b : Bool) :
    foldFn (SnocList.wrap b) = if b then (1, true) else (0, false) := rfl
@[simp] theorem foldFn_snoc_true (xs : SnocList Bool Bool) :
    foldFn (SnocList.snoc xs true) = ((foldFn xs).1 + 1, (foldFn xs).2) := rfl
@[simp] theorem foldFn_snoc_false (xs : SnocList Bool Bool) :
    foldFn (SnocList.snoc xs false) =
      ((foldFn xs).1 - 1, (foldFn xs).2 && decide (1 ≤ (foldFn xs).1)) := rfl

/-- The answer: `xs` is valid iff the scan stayed non-negative throughout AND ends at depth `0`. -/
def validFn (xs : SnocList Bool Bool) : Bool := (foldFn xs).2 && decide ((foldFn xs).1 = 0)

/-- **The allegory program**: LeetCode 20's decision as a morphism `Toks ⟶ Bool` in `Rel(Set)`. -/
def solve : Toks ⟶ dBool := graph validFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map validFn

/-! ## Specification: the balanced (one-type Dyck) language -/

/-- `depthP xs` — the net bracket depth `#open − #close`, structural (not clamped, unlike the
    fold's `depth` component once `ok` fails). -/
def depthP : SnocList Bool Bool → Int
  | SnocList.wrap b => if b then 1 else -1
  | SnocList.snoc xs b => depthP xs + (if b then 1 else -1)

/-- `neverNegP xs` — every non-empty PREFIX of `xs` (including `xs` itself) has net depth `≥ 0`. -/
def neverNegP : SnocList Bool Bool → Prop
  | SnocList.wrap b => (if b then True else False)
  | SnocList.snoc xs b => neverNegP xs ∧ 0 ≤ depthP (SnocList.snoc xs b)

/-- `balancedP xs` — `xs` is a balanced bracket sequence: every prefix stays non-negative and the
    whole sequence's net depth is `0`. -/
def balancedP (xs : SnocList Bool Bool) : Prop := neverNegP xs ∧ depthP xs = 0

/-- The **specification** as a morphism `Toks ⟶ Bool` in `Rel(Set)`: `r = true` iff `xs` is
    balanced — a genuine `Iff`, since this is a DECISION problem, not an optimum to extremize. -/
def spec : Toks ⟶ dBool := fun xs r => (r = true ↔ balancedP xs)

/-! ## Invariants of the fold -/

/-- If every prefix so far is non-negative, `depthP` itself is non-negative. (Needed to bridge the
    fold's dummy base-case depth to the true `depthP` in the invariant below.) -/
theorem depthP_nonneg_of_neverNeg (xs : SnocList Bool Bool) (h : neverNegP xs) : 0 ≤ depthP xs := by
  cases xs with
  | wrap b =>
    cases b with
    | false => simp [neverNegP] at h
    | true => show (0 : Int) ≤ 1; omega
  | snoc xs b => exact h.2

/-- **Once `ok`, the fold's depth component IS `depthP`.** This is a CONDITIONAL invariant, not an
    unconditional one: `foldFn`'s `wrap false` case sets `depth = 0` (a dummy — the sequence is
    already invalid there, while `depthP (wrap false) = -1`), so the raw equality
    `(foldFn xs).1 = depthP xs` is FALSE in general. It becomes true exactly when `ok` holds, which
    is the only regime `solve_correct` ever needs it in (once `ok = false`, `validFn` is already
    `false` regardless of the depth component). -/
theorem foldFn_fst_of_ok : ∀ xs, (foldFn xs).2 = true → (foldFn xs).1 = depthP xs := by
  intro xs; induction xs with
  | wrap b =>
    intro h
    cases b with
    | false => exact absurd h (by decide)
    | true => rfl
  | snoc xs b ih =>
    intro h
    cases b with
    | true =>
      have hok : (foldFn xs).2 = true := by simpa only [foldFn_snoc_true] using h
      have hd := ih hok
      show (foldFn xs).1 + 1 = depthP xs + 1
      omega
    | false =>
      have h' : (foldFn xs).2 = true ∧ 1 ≤ (foldFn xs).1 := by
        rw [foldFn_snoc_false, Bool.and_eq_true_iff, decide_eq_true_eq] at h
        exact h
      have hd := ih h'.1
      show (foldFn xs).1 - 1 = depthP xs + (-1)
      omega

/-- **`ok` tracks exactly `neverNegP`.** -/
theorem foldFn_snd_iff_neverNeg : ∀ xs, (foldFn xs).2 = true ↔ neverNegP xs := by
  intro xs; induction xs with
  | wrap b => cases b <;> simp [foldFn_wrap, neverNegP]
  | snoc xs b ih =>
    cases b with
    | true =>
      have step : (foldFn (SnocList.snoc xs true)).2 = true ↔ (foldFn xs).2 = true := by
        rw [foldFn_snoc_true]
      rw [step, ih]
      show neverNegP xs ↔ neverNegP xs ∧ 0 ≤ depthP xs + 1
      constructor
      · intro hnn
        exact ⟨hnn, by have := depthP_nonneg_of_neverNeg xs hnn; omega⟩
      · rintro ⟨hnn, _⟩; exact hnn
    | false =>
      have step : (foldFn (SnocList.snoc xs false)).2 = true ↔
          (foldFn xs).2 = true ∧ 1 ≤ (foldFn xs).1 := by
        rw [foldFn_snoc_false, Bool.and_eq_true_iff, decide_eq_true_eq]
      rw [step]
      show (foldFn xs).2 = true ∧ 1 ≤ (foldFn xs).1 ↔ neverNegP xs ∧ 0 ≤ depthP xs + (-1)
      constructor
      · rintro ⟨hok, hge⟩
        have hnn := ih.mp hok
        have heq := foldFn_fst_of_ok xs hok
        exact ⟨hnn, by omega⟩
      · rintro ⟨hnn, hge⟩
        have hok := ih.mpr hnn
        have heq := foldFn_fst_of_ok xs hok
        exact ⟨hok, by omega⟩

/-! ## Correctness: `solve` decides the balanced language -/

/-- **Correctness of the allegory program** (`solve` DECIDES `balancedP`): `xs` is valid iff it is
    balanced. Follows from the two invariants above, via `Bool.and_eq_true_iff`/`decide_eq_true_eq`
    to unpack `validFn`'s `&&`/`decide`. -/
theorem solve_correct (xs : SnocList Bool Bool) : validFn xs = true ↔ balancedP xs := by
  show ((foldFn xs).2 && decide ((foldFn xs).1 = 0)) = true ↔ neverNegP xs ∧ depthP xs = 0
  rw [Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨hok, hd0⟩
    have hnn := (foldFn_snd_iff_neverNeg xs).mp hok
    have heq := foldFn_fst_of_ok xs hok
    exact ⟨hnn, by omega⟩
  · rintro ⟨hnn, hd0⟩
    have hok := (foldFn_snd_iff_neverNeg xs).mpr hnn
    have heq := foldFn_fst_of_ok xs hok
    exact ⟨hok, by omega⟩

/-! ## Running the program -/

/-- Build a bracket sequence from a first bracket and the rest, in order (`true` = open). -/
def ofOpens (first : Bool) (rest : List Bool) : SnocList Bool Bool :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : validFn (ofOpens true [false]) = true := by decide                 -- "()"
example : validFn (ofOpens true [true, false, false]) = true := by decide    -- "(())"
example : validFn (ofOpens false [true]) = false := by decide                -- ")("
example : validFn (ofOpens true [true]) = false := by decide                 -- "(("
example : validFn (ofOpens true [false, false]) = false := by decide         -- "())"

end Freyd.Alg.RelSet.LC20
