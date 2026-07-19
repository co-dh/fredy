/-
  LeetCode 383 — Ransom Note — as an ALLEGORY PROGRAM.

  Problem: `ransom` can be built from `magazine`'s letters (each magazine letter usable at most
  once) iff every letter's count in `ransom` is `≤` its count in `magazine` — MULTISET
  containment.  Letters are modelled as `List Int` (character codes), reusing `leet/L242.lean`'s
  `countL : List Int → Int → Nat` (the "Valid Anagram" count fold) rather than re-deriving it.

  Same DECISION shape as `L217`/`L242`/`L125` (`Freyd/leetcode.md` S5): correctness is a plain
  `iff`, not a refinement+domination extremum.

  1. **Data** — the input is a *pair* of letter lists `⟨(List Int) × (List Int)⟩ ⟶ ⟨Bool⟩`.

  2. **Program (Bool)** — `∀ c, countL ransom c ≤ countL magazine c` quantifies over all of `Int`,
     which is not directly decidable.  But a letter `c` that does not occur in `ransom` has
     `countL ransom c = 0 ≤` anything, so checking only the letters that DO appear in `ransom`
     suffices: `canBuildFn ransom magazine := ransom.all (fun c => decide (countL ransom c ≤
     countL magazine c))`.  This avoids quantifying over the infinite `Int` domain in the
     executable program.

  3. **The bridge (the real work)** — `canBuild_correct` uses `List.all_eq_true` (Lean core) to
     unfold the Bool program to "the bound holds for every `c ∈ ransom`", then extends it to EVERY
     `c : Int` via `L242.mem_iff_countL_pos` (`c ∈ ransom ↔ 0 < countL ransom c`): a letter absent
     from `ransom` has `countL ransom c = 0`, so the bound is trivial there.

  4. **Correctness** — `canBuild_correct : canBuildFn ransom magazine = true ↔
     ∀ c, countL ransom c ≤ countL magazine c` — the honest multiset-containment spec, reflected
     against the Bool program (no `Decidable` instance manufactured, exactly `L217`/`L242`'s
     `bool_eq_of_iff_true` route).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import leet.L242
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC383

open Freyd Freyd.Alg.RelSet

/-! ## Data: a pair of letter lists (ransom note, magazine); answer = `Bool` -/

/-- The object of a PAIR of letter lists — the input to the "can build" decision. -/
abbrev Pair : RelSet.{0} := ⟨(List Int) × (List Int)⟩
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## The program: check the bound only for letters that actually appear in `ransom` -/

/-- `canBuildFn ransom magazine` — can `ransom` be built from `magazine`'s letters?  Checks
    `countL ransom c ≤ countL magazine c` for every letter `c ∈ ransom` (a letter absent from
    `ransom` needs no check: its count there is `0`). -/
def canBuildFn (ransom magazine : List Int) : Bool :=
  ransom.all (fun c => decide (LC242.countL ransom c ≤ LC242.countL magazine c))

/-- `canBuildFn`, uncurried to a function on `Pair`'s carrier (what `graph` needs). -/
def solveFn (p : (List Int) × (List Int)) : Bool := canBuildFn p.1 p.2

/-- **The allegory program**: LeetCode 383's solution as a morphism `Pair ⟶ Bool` in `Rel(Set)`. -/
def solve : Pair ⟶ dBool := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## The specification: multiset containment -/

/-- **The specification**: `ransom` can be built from `magazine` iff every letter occurs no more
    often in `ransom` than in `magazine` — the honest "multiset containment" definition. -/
def CanBuild (ransom magazine : List Int) : Prop :=
  ∀ c, LC242.countL ransom c ≤ LC242.countL magazine c

/-- **`canBuildFn` decides `CanBuild`** — the DECISION-problem correctness shape: an `iff`. -/
theorem canBuild_correct (ransom magazine : List Int) :
    canBuildFn ransom magazine = true ↔ CanBuild ransom magazine := by
  unfold canBuildFn CanBuild
  rw [List.all_eq_true]
  constructor
  · intro h c
    by_cases hc : c ∈ ransom
    · exact decide_eq_true_eq.mp (h c hc)
    · have hmem := LC242.mem_iff_countL_pos ransom c
      have h0 : ¬ (0 < LC242.countL ransom c) := fun hpos => hc (hmem.mpr hpos)
      omega
  · intro h c _hc
    exact decide_eq_true_eq.mpr (h c)

/-- **The specification** as a morphism `Pair ⟶ Bool`: `b` is THE correct boolean answer to "can
    `ransom` be built from `magazine`?" -/
def spec : Pair ⟶ dBool := fun p b => (b = true ↔ CanBuild p.1 p.2)

/-- Two booleans that agree on being `true` are equal (Bool extensionality; cf. `L217`/`L242`). -/
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
  apply hom_ext; intro p b
  show (b = solveFn p) ↔ (b = true ↔ CanBuild p.1 p.2)
  constructor
  · intro h; rw [h]; exact canBuild_correct p.1 p.2
  · intro h
    have h' : (b = true) ↔ (solveFn p = true) := h.trans (canBuild_correct p.1 p.2).symm
    exact bool_eq_of_iff_true h'

/-! ## Running the program -/

-- letters encoded as distinct `Int`s: a=97 b=98
example : canBuildFn [97] [98] = false := by decide  -- "a" cannot be built from "b"
example : canBuildFn [97, 98] [97, 98, 98] = true := by decide  -- "ab" from "abb"

end Freyd.Alg.RelSet.LC383
