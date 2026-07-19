/-
  LeetCode 91 — Decode Ways — as an ALLEGORY PROGRAM.

  Problem: a non-empty digit string `d₀,…,d_{n-1}` (digits `0`–`9`). Count the number of ways to
  decode it into letters, where a decoded GROUP is either
    - one digit `1..9` (never `0` alone), or
    - two consecutive digits forming `10..26`.
  Every digit must belong to exactly one group.

  Same recipe as `leet/L70.lean` (see `Freyd/leetcode.md`, skill S6) rather than the
  refinement-of-an-order recipe of `L121`/`L198`/`L53`: Decode Ways is a COUNTING problem, not an
  optimisation one, so there is no `≤`-extremum to refine into — the specification IS the exact
  answer, and the only job is to show an O(n) fold computes it.

  1. **Data** — the digit string is the initial algebra `SnocList ℕ ℕ` of `F X = ℕ + X × ℕ`
     (`AOP.A6_SnocList`); `wrap d` is a single digit, `snoc xs d` appends a digit.

  2. **Specification** — `decode`/`decodePrev` (mutual): the TEXTBOOK decode-ways recurrence, "the
     last group is a single digit (drop it, recurse) OR the last group is a valid pair (drop both,
     recurse)". This is *the* definition of "the number of valid segmentations", exactly as `L70`'s
     naive `climb` is *the* definition of "the number of ways to climb `n` stairs" — but, because
     each step calls itself on TWO different smaller lists (`xs`, and `xs` with its own last digit
     removed too), it is exponential, just like `climb`.

  3. **Program** — `foldFn`: the O(n) fold carrying `(ways, prevWays, lastDigit)`, TUPLING
     `decode`/`decodePrev`/`lastDigit` into one state so nothing is recomputed — the same
     linearisation trick as `L70`'s `fibPair`.

  4. **Correctness** — one simultaneous induction, `foldFn_eq`, shows the tupled fold's first two
     components equal `decode`/`decodePrev` at every step; the answer follows (`solve_eq_spec`).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC91

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: a non-empty digit string -/

/-- The object of digit strings in `Rel(Set)` — `SnocList ℕ ℕ` (`wrap d` = single digit, `snoc xs
    d` = `xs` with a new final digit `d`). -/
abbrev Digits : RelSet.{0} := dSL Nat Nat
/-- The object of naturals (decode counts) in `Rel(Set)`. -/
abbrev dN : RelSet.{0} := ⟨Nat⟩

/-! ## Specification: the naive (exponential) decode-ways recurrence -/

/-- The last digit of a (non-empty) digit string. -/
def lastDigit : SnocList Nat Nat → Nat
  | SnocList.wrap d => d
  | SnocList.snoc _ d => d

/- `decode xs` — the number of ways to decode `xs` into 1- or 2-digit codes. `decodePrev xs` — the
   same count for `xs` with its OWN last digit removed (so `1` when that leaves nothing: the empty
   string decodes exactly one way — the base case of every DP over a non-empty structure needs a
   "before the first element" value, here `1`). Mutual because the "last group is a pair" case of
   `decode` needs the count TWO digits back, reached via `decodePrev`'s own `snoc` case peeling one
   further digit than `decode`'s. -/
mutual
def decode : SnocList Nat Nat → Nat
  | SnocList.wrap d => if 1 ≤ d ∧ d ≤ 9 then 1 else 0
  | SnocList.snoc xs d =>
      let single := if 1 ≤ d ∧ d ≤ 9 then decode xs else 0
      let two := lastDigit xs * 10 + d
      let double := if 10 ≤ two ∧ two ≤ 26 then decodePrev xs else 0
      single + double

def decodePrev : SnocList Nat Nat → Nat
  | SnocList.wrap _ => 1
  | SnocList.snoc xs _ => decode xs
end

/-- The **specification** as a morphism `Digits ⟶ ℕ` in `Rel(Set)`: `xs` relates to `decode xs`,
    the exact number of valid decodings. -/
def spec : Digits ⟶ dN := fun xs k => k = decode xs

/-! ## Program: the O(n) TUPLED fold — carry `(ways, prevWays, lastDigit)` -/

/-- The fold algebra `[ d ↦ (single d, 1, d), ((w,wp,ld),d) ↦ (single+double, w, d) ] :
    F(ℕ×ℕ×ℕ) → ℕ×ℕ×ℕ`. -/
def algFn : (Fobj Nat Nat (⟨Nat × Nat × Nat⟩ : RelSet.{0})).carrier → (Nat × Nat × Nat)
  | Sum.inl d => ((if 1 ≤ d ∧ d ≤ 9 then 1 else 0), 1, d)
  | Sum.inr (st, d) =>
      let (w, wp, ld) := st
      let single := if 1 ≤ d ∧ d ≤ 9 then w else 0
      let two := ld * 10 + d
      let double := if 10 ≤ two ∧ two ≤ 26 then wp else 0
      (single + double, w, d)

/-- The algebra as a morphism (a `Map`) `F(ℕ×ℕ×ℕ) ⟶ ℕ×ℕ×ℕ` in `Rel(Set)`. -/
def alg : Fobj Nat Nat (⟨Nat × Nat × Nat⟩ : RelSet.{0}) ⟶ (⟨Nat × Nat × Nat⟩ : RelSet.{0}) :=
  graph algFn

/-- The concrete fold (structural recursion), returning `(ways, prevWays, lastDigit)`. -/
def foldFn : SnocList Nat Nat → Nat × Nat × Nat
  | SnocList.wrap d => ((if 1 ≤ d ∧ d ≤ 9 then 1 else 0), 1, d)
  | SnocList.snoc xs d =>
      let (w, wp, ld) := foldFn xs
      let single := if 1 ≤ d ∧ d ≤ 9 then w else 0
      let two := ld * 10 + d
      let double := if 10 ≤ two ∧ two ≤ 26 then wp else 0
      (single + double, w, d)

/-- The answer: the first fold component (the total decode count). -/
def solveFn (xs : SnocList Nat Nat) : Nat := (foldFn xs).1

/-- **The allegory program**: LeetCode 91's O(n) solution as a morphism `Digits ⟶ ℕ` in
    `Rel(Set)`. -/
def solve : Digits ⟶ dN := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree. -/
theorem cataFold_alg : ∀ (xs : SnocList Nat Nat) (r : Nat × Nat × Nat),
    cataFold alg xs r ↔ r = foldFn xs := by
  intro xs; induction xs with
  | wrap d => intro r; exact Iff.rfl
  | snoc xs d ih =>
    intro r
    simp only [cataFold_snoc]
    constructor
    · rintro ⟨r', hr', hfr⟩
      rw [ih r'] at hr'; subst hr'; exact hfr
    · intro h; exact ⟨foldFn xs, (ih (foldFn xs)).mpr rfl, h⟩

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈ · fst`, a fold followed by the
    projection onto `ways`. -/
theorem solve_eq_cata : solve = cataR alg ≫ graph (Prod.fst : Nat × Nat × Nat → Nat) := by
  apply hom_ext; intro xs v
  simp only [solve, graph, comp_apply, cataR]
  constructor
  · intro hv; exact ⟨foldFn xs, (cataFold_alg xs (foldFn xs)).mpr rfl, hv⟩
  · rintro ⟨st, hst, hv⟩; rw [(cataFold_alg xs st).mp hst] at hv; exact hv

/-! ## Correctness: the fold's `(ways, prevWays)` equal `(decode, decodePrev)` -/

/-- The tupled fold's third component is always the last digit — immediate from the equations
    (both `foldFn` and `lastDigit` return the digit just consumed), no induction needed. -/
theorem foldFn_lastDigit : ∀ xs, (foldFn xs).2.2 = lastDigit xs
  | SnocList.wrap _ => rfl
  | SnocList.snoc _ _ => rfl

/-- **The linearisation lemma** (the point of the file, `L70`-style): the tupled fold's first two
    components are exactly the naive recurrence's two counts, `decode`/`decodePrev`, at every
    step — tupling avoids ever recomputing either count. -/
theorem foldFn_eq : ∀ xs, (foldFn xs).1 = decode xs ∧ (foldFn xs).2.1 = decodePrev xs := by
  intro xs; induction xs with
  | wrap d => exact ⟨rfl, rfl⟩
  | snoc xs d ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hld : (foldFn xs).2.2 = lastDigit xs := foldFn_lastDigit xs
    refine ⟨?_, ?_⟩
    · show (if 1 ≤ d ∧ d ≤ 9 then (foldFn xs).1 else 0)
          + (if 10 ≤ (foldFn xs).2.2 * 10 + d ∧ (foldFn xs).2.2 * 10 + d ≤ 26
             then (foldFn xs).2.1 else 0)
        = decode (SnocList.snoc xs d)
      rw [ih1, ih2, hld]; rfl
    · show (foldFn xs).1 = decodePrev (SnocList.snoc xs d)
      rw [ih1]; rfl

/-- **Correctness of the allegory program**: `solve = spec` as morphisms in `Rel(Set)`. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro xs k
  show k = (foldFn xs).1 ↔ k = decode xs
  rw [(foldFn_eq xs).1]

/-! ## Running the program -/

/-- Build a digit string from a first digit and the rest, in order. -/
def ofList (first : Nat) (rest : List Nat) : SnocList Nat Nat :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 1 [2]) = 2 := by decide
example : solveFn (ofList 1 [0]) = 1 := by decide
example : solveFn (ofList 0 []) = 0 := by decide
example : solveFn (ofList 2 [2, 6]) = 3 := by decide

end Freyd.Alg.RelSet.LC91
