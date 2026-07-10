/-
  LeetCode 55 — Jump Game — as an ALLEGORY PROGRAM (a greedy reachability DECISION).

  Problem: given a non-empty array of max-jump-lengths `nums[0],…,nums[n-1]` (one per index,
  `Nat`-valued), return `true` iff the last index is reachable from index `0`, where from index
  `i` you may jump to any index `j` with `i < j ≤ i + nums[i]`.

  Same recipe as `leet/L20.lean`/`leet/L217.lean` (`Fredy/leetcode.md`, skill S0), for a
  DECISION problem (answer = `Bool`, correctness = a plain `Iff`, no extremum):

  1. **Data** — the array is the initial algebra `SnocList ℕ ℕ` (`AOP.A6_SnocList`); `wrap x` is
     a single-element array, `snoc xs p` appends `p`.

  2. **Program** — the left-to-right GREEDY scan of B&dM §7.2 / `AOP.A7_2`: fold state
     `(maxReach, ok)`. For the element `p` at position `idx = len xs` (the length of the prefix
     already processed): if `idx > maxReach` the position is unreachable and `ok` turns `false`
     (and freezes `maxReach`, self-perpetuating — `idx` only grows from here, `maxReach` never
     does, so `ok` stays `false` forever after); else `maxReach := max maxReach (idx + p)` and
     `ok` is carried through unchanged. `solveFn xs := (foldFn xs).2`.

  3. **Specification** — `Reaches xs`, via the inductive relation `ReachIdx xs n` ("index `n` is
     reachable in `xs`"): `0` is always reachable (`start`); if `a` is reachable and
     `a < b ≤ a + nums[a]`, then `b` is reachable (`step`). This is exactly the book's "there is a
     sequence of positions `0 = p₀ < p₁ < … < p_k = lastIndex` with each `p_{j+1} ≤ p_j +
     nums[p_j]`" unrolled at the endpoint: `Reaches xs := ReachIdx xs (len xs - 1)`.

  4. **Correctness** (`solve_correct : solveFn xs = true ↔ Reaches xs`) splits into greedy
     SOUNDNESS and COMPLETENESS, both packaged as ONE invariant (`ok_iff_allReach`):
     `(foldFn xs).2 = true ↔ ∀ j, j < len xs → ReachIdx xs j` — `ok` tracks reachability of EVERY
     position, not just the last. The two directions:
     - **Soundness** (`ok = true ⟹ a jump plan exists`): if `ok` held through the whole prefix,
       the position achieving `maxReach` (`maxReach_achieved`, the `mem_minPrice`-style witness
       lemma) is itself reachable by the outer induction hypothesis, so any position within
       `maxReach` — in particular the newly-processed one — extends the reachable set.
     - **Completeness** (`a jump plan exists ⟹ ok`): the contrapositive is cleaner — if `ok`
       fails at some position, then (by `reachIdx_le_maxReach`, itself powered by `contributes_le`
       — the fold's `maxReach` dominates `a + nums[a]` for every REACHABLE `a`) nothing beyond the
       frozen `maxReach` bound is ever reachable, in particular not the failing position itself.
     `ReachIdx_mono_le` (downward closure — reaching `n` lets you stop at any earlier `k ≤ n` by
     choosing shorter jumps, pure combinatorics, no fold needed) then upgrades "every position
     reachable" to and from "the last position reachable" for the final `Iff`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC55

open Freyd Freyd.Alg.RelSet.SL

/-! ## Mathlib-free `Nat` `max` (copied from `L104`, control the rewrite set) -/

def imax (a b : Nat) : Nat := if a ≤ b then b else a

theorem imax_ge_left  (a b : Nat) : a ≤ imax a b := by unfold imax; split <;> omega
theorem imax_ge_right (a b : Nat) : b ≤ imax a b := by unfold imax; split <;> omega
theorem imax_eq_or (a b : Nat) : imax a b = a ∨ imax a b = b := by
  unfold imax; split; exacts [Or.inr rfl, Or.inl rfl]

/-! ## Data: the jump-length array as a non-empty snoc-list of naturals -/

/-- The object of jump-length arrays in `Rel(Set)` — `SnocList ℕ ℕ` (`wrap x` = a single-element
    array, `snoc xs p` = `xs` with one more jump length appended). -/
abbrev Jumps : RelSet.{0} := dSL Nat Nat
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## Index bookkeeping: length and lookup into a `SnocList ℕ ℕ`, read left to right -/

/-- The number of elements in `xs` (`≥ 1`, always). -/
def len : SnocList Nat Nat → Nat
  | SnocList.wrap _ => 1
  | SnocList.snoc xs _ => len xs + 1

@[simp] theorem len_wrap (x : Nat) : len (SnocList.wrap x) = 1 := rfl
@[simp] theorem len_snoc (xs : SnocList Nat Nat) (p : Nat) :
    len (SnocList.snoc xs p) = len xs + 1 := rfl

theorem len_pos : ∀ xs : SnocList Nat Nat, 0 < len xs
  | SnocList.wrap _ => by show 0 < 1; omega
  | SnocList.snoc xs _ => by simp only [len_snoc]; omega

/-- `nth xs i` — the jump length recorded at index `i` in `xs` (`0`-indexed from the left).
    Meaningless for `i ≥ len xs`; never queried there. -/
def nth : SnocList Nat Nat → Nat → Nat
  | SnocList.wrap x, _ => x
  | SnocList.snoc xs p, i => if i = len xs then p else nth xs i

@[simp] theorem nth_wrap (x i : Nat) : nth (SnocList.wrap x) i = x := rfl

theorem nth_snoc_self (xs : SnocList Nat Nat) (p : Nat) :
    nth (SnocList.snoc xs p) (len xs) = p := by
  show (if len xs = len xs then p else nth xs (len xs)) = p
  rw [if_pos rfl]

theorem nth_snoc_of_lt {xs : SnocList Nat Nat} {p i : Nat} (h : i < len xs) :
    nth (SnocList.snoc xs p) i = nth xs i := by
  show (if i = len xs then p else nth xs i) = nth xs i
  rw [if_neg (by omega)]

/-! ## The program: the left-to-right greedy scan, state `(maxReach, ok)` -/

/-- The concrete fold (structural recursion): `maxReach` is the farthest index reachable using
    only the elements processed so far (assuming `ok`); `ok` records "no position seen so far was
    stuck". A lone element always starts `ok`, `maxReach := x` (from index `0`, reach `0 + x`). At
    each new element `p` (position `idx = len xs`): if `idx > maxReach`, that position — and
    (since `maxReach` freezes and `idx` only grows) every later one — is unreachable, so `ok`
    turns `false` for good; else `maxReach` grows to `max maxReach (idx + p)` and `ok` carries. -/
def foldFn : SnocList Nat Nat → Nat × Bool
  | SnocList.wrap x => (x, true)
  | SnocList.snoc xs p =>
      if len xs > (foldFn xs).1 then ((foldFn xs).1, false)
      else (imax (foldFn xs).1 (len xs + p), (foldFn xs).2)

theorem foldFn_snoc_fail {xs : SnocList Nat Nat} {p : Nat} (h : len xs > (foldFn xs).1) :
    foldFn (SnocList.snoc xs p) = ((foldFn xs).1, false) := by
  show (if len xs > (foldFn xs).1 then ((foldFn xs).1, false)
      else (imax (foldFn xs).1 (len xs + p), (foldFn xs).2)) = ((foldFn xs).1, false)
  rw [if_pos h]

theorem foldFn_snoc_ok {xs : SnocList Nat Nat} {p : Nat} (h : len xs ≤ (foldFn xs).1) :
    foldFn (SnocList.snoc xs p) = (imax (foldFn xs).1 (len xs + p), (foldFn xs).2) := by
  show (if len xs > (foldFn xs).1 then ((foldFn xs).1, false)
      else (imax (foldFn xs).1 (len xs + p), (foldFn xs).2)) =
        (imax (foldFn xs).1 (len xs + p), (foldFn xs).2)
  rw [if_neg (by omega)]

/-- The answer: can the last index be reached? -/
def solveFn (xs : SnocList Nat Nat) : Bool := (foldFn xs).2

/-- **The allegory program**: LeetCode 55's decision as a morphism `Jumps ⟶ Bool` in `Rel(Set)`. -/
def solve : Jumps ⟶ dBool := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## Specification: reachability of the last index by a chain of valid jumps -/

/-- `ReachIdx xs n` — index `n` is reachable in `xs` from index `0` by a chain of valid jumps:
    `0` is always reachable, and from a reachable `a < len xs` you may reach any `b` with
    `a < b ≤ a + nums[a]`. Unrolling the `step` constructors recovers the book's "there is a
    sequence of positions `0 = p₀ < p₁ < … < p_k = n` with each `p_{j+1} ≤ p_j + nums[p_j]`". -/
inductive ReachIdx (xs : SnocList Nat Nat) : Nat → Prop
  | start : ReachIdx xs 0
  | step {a b : Nat} : ReachIdx xs a → a < len xs → a < b → b ≤ a + nth xs a → ReachIdx xs b

/-- The **specification**: the last index of `xs` is reachable from index `0`. -/
def Reaches (xs : SnocList Nat Nat) : Prop := ReachIdx xs (len xs - 1)

/-- The **specification** as a morphism `Jumps ⟶ Bool` in `Rel(Set)`: `b = true` iff the last
    index is reachable — a genuine `Iff`, since this is a DECISION problem, not an optimum. -/
def spec : Jumps ⟶ dBool := fun xs b => (b = true ↔ Reaches xs)

/-! ## Pure combinatorics of `ReachIdx` (no fold involved) -/

/-- **Downward closure**: if `n` is reachable, so is any earlier `k ≤ n` — jump the same chain but
    stop short (or don't move at all). -/
theorem ReachIdx_mono_le {xs : SnocList Nat Nat} {n : Nat} (h : ReachIdx xs n) :
    ∀ {k}, k ≤ n → ReachIdx xs k := by
  induction h with
  | start =>
    intro k hk
    have hk0 : k = 0 := by omega
    rw [hk0]; exact ReachIdx.start
  | @step a b hprev hlt hab hbr ih =>
    intro k hk
    by_cases hc : k ≤ a
    · exact ih hc
    · exact ReachIdx.step hprev hlt (by omega) (by omega)

/-- Extending `xs` by one more element on the right never removes a reachable position (the
    lookup at any position `< len xs` is unaffected by the new tail element). -/
theorem ReachIdx_weaken (p : Nat) {xs : SnocList Nat Nat} {n : Nat} (h : ReachIdx xs n) :
    ReachIdx (SnocList.snoc xs p) n := by
  induction h with
  | start => exact ReachIdx.start
  | @step a b hprev hlt hab hbr ih =>
    have hlt' : a < len (SnocList.snoc xs p) := by simp only [len_snoc]; omega
    exact ReachIdx.step ih hlt' hab (by rw [nth_snoc_of_lt hlt]; exact hbr)

/-- The converse of `ReachIdx_weaken`: a chain living entirely below `len xs` never actually
    needed the appended element `p`, so it restricts back down to `xs`. -/
theorem ReachIdx_restrict (p : Nat) {xs : SnocList Nat Nat} {n : Nat}
    (h : ReachIdx (SnocList.snoc xs p) n) : n < len xs → ReachIdx xs n := by
  induction h with
  | start => intro _; exact ReachIdx.start
  | @step a b hprev hlt hab hbr ih =>
    intro hb
    have hamlt : a < len xs := by omega
    have hstep := ih hamlt
    refine ReachIdx.step hstep hamlt hab ?_
    rw [nth_snoc_of_lt hamlt] at hbr
    exact hbr

/-! ## The fold's `maxReach` dominates every reachable position's own jump -/

/-- `maxReach` is always ACHIEVED by some position — the `mem_minPrice`/`pathLen_depth`-style
    witness lemma. -/
theorem maxReach_achieved :
    ∀ xs : SnocList Nat Nat, ∃ k, k < len xs ∧ (foldFn xs).1 = k + nth xs k := by
  intro xs
  induction xs with
  | wrap x =>
    refine ⟨0, ?_, ?_⟩
    · show 0 < 1; omega
    · have hf : (foldFn (SnocList.wrap x)).1 = x := rfl
      have hn : nth (SnocList.wrap x) 0 = x := rfl
      rw [hf, hn, Nat.zero_add]
  | snoc xs p ih =>
    by_cases hfail : len xs > (foldFn xs).1
    · simp only [foldFn_snoc_fail hfail]
      obtain ⟨k, hk, hkeq⟩ := ih
      refine ⟨k, ?_, ?_⟩
      · exact Nat.lt_succ_of_lt hk
      · rw [nth_snoc_of_lt hk]; exact hkeq
    · replace hfail : len xs ≤ (foldFn xs).1 := Nat.not_lt.mp hfail
      simp only [foldFn_snoc_ok hfail]
      rcases imax_eq_or (foldFn xs).1 (len xs + p) with he | he
      · obtain ⟨k, hk, hkeq⟩ := ih
        refine ⟨k, ?_, ?_⟩
        · exact Nat.lt_succ_of_lt hk
        · rw [he, nth_snoc_of_lt hk]; exact hkeq
      · refine ⟨len xs, ?_, ?_⟩
        · exact Nat.lt_succ_self (len xs)
        · rw [he, nth_snoc_self]

/-- **Key invariant**: `maxReach` dominates `m + nums[m]` for every `m` it "knows about" — every
    `m < len xs` with `m ≤ maxReach`. (Positions past a freeze point are excluded automatically:
    once frozen at some bound `B`, every `m > B` fails `m ≤ maxReach = B`.) -/
theorem contributes_le (xs : SnocList Nat Nat) :
    ∀ m, m < len xs → m ≤ (foldFn xs).1 → m + nth xs m ≤ (foldFn xs).1 := by
  induction xs with
  | wrap x =>
    intro m hm _
    have hlen : len (SnocList.wrap x) = 1 := rfl
    have hf : (foldFn (SnocList.wrap x)).1 = x := rfl
    have hn : nth (SnocList.wrap x) m = x := rfl
    omega
  | snoc xs p ih =>
    intro m hm hle
    by_cases hfail : len xs > (foldFn xs).1
    · simp only [foldFn_snoc_fail hfail] at hle ⊢
      have hmlt : m < len xs := by omega
      rw [nth_snoc_of_lt hmlt]
      exact ih m hmlt hle
    · replace hfail : len xs ≤ (foldFn xs).1 := Nat.not_lt.mp hfail
      simp only [foldFn_snoc_ok hfail] at hle ⊢
      rcases Nat.lt_or_ge m (len xs) with hmlt | hmge
      · rw [nth_snoc_of_lt hmlt]
        have hge := imax_ge_left (foldFn xs).1 (len xs + p)
        have hb := ih m hmlt (by omega)
        omega
      · have hmeq : m = len xs := by simp only [len_snoc] at hm; omega
        rw [hmeq, nth_snoc_self]
        exact imax_ge_right (foldFn xs).1 (len xs + p)

/-- **Bound**: every reachable position lies within `maxReach`. -/
theorem reachIdx_le_maxReach {xs : SnocList Nat Nat} {n : Nat} (h : ReachIdx xs n) :
    n ≤ (foldFn xs).1 := by
  induction h with
  | start => exact Nat.zero_le _
  | @step a b hprev hlt hab hbr ih =>
    have hc := contributes_le xs a hlt ih
    omega

/-! ## Correctness: `ok` tracks reachability of EVERY position -/

/-- **The master invariant**: `ok` holds after processing `xs` iff EVERY position in `xs` is
    reachable — the SOUNDNESS and COMPLETENESS of the greedy scan, in one `Iff`. -/
theorem ok_iff_allReach : ∀ xs : SnocList Nat Nat,
    (foldFn xs).2 = true ↔ ∀ j, j < len xs → ReachIdx xs j := by
  intro xs
  induction xs with
  | wrap x =>
    constructor
    · intro _ j hj
      have hj0 : j = 0 := by simp only [len_wrap] at hj; omega
      rw [hj0]; exact ReachIdx.start
    · intro _; rfl
  | snoc xs p ih =>
    by_cases hfail : len xs > (foldFn xs).1
    · simp only [foldFn_snoc_fail hfail]
      constructor
      · intro hc; simp at hc
      · intro hall
        exfalso
        have hreach : ReachIdx (SnocList.snoc xs p) (len xs) :=
          hall (len xs) (by simp only [len_snoc]; omega)
        generalize hgen : len xs = N at hreach
        cases hreach with
        | start =>
          have hp := len_pos xs
          omega
        | @step a b hprev hlt hab hbr =>
          have hamlt : a < len xs := by omega
          have hrestrict := ReachIdx_restrict p hprev hamlt
          have hbound := reachIdx_le_maxReach hrestrict
          have hc2 := contributes_le xs a hamlt hbound
          rw [nth_snoc_of_lt hamlt] at hbr
          omega
    · replace hfail : len xs ≤ (foldFn xs).1 := Nat.not_lt.mp hfail
      simp only [foldFn_snoc_ok hfail, ih]
      constructor
      · intro hall j hj
        rcases Nat.lt_or_ge j (len xs) with hjlt | hjge
        · exact ReachIdx_weaken p (hall j hjlt)
        · have hjeq : j = len xs := by simp only [len_snoc] at hj; omega
          rw [hjeq]
          obtain ⟨k, hk, hkeq⟩ := maxReach_achieved xs
          have hkreach := ReachIdx_weaken p (hall k hk)
          refine ReachIdx.step hkreach (by simp only [len_snoc]; omega) hk ?_
          rw [nth_snoc_of_lt hk, ← hkeq]
          exact hfail
      · intro hall j hj
        exact ReachIdx_restrict p (hall j (by simp only [len_snoc]; omega)) hj

/-- **Correctness of the allegory program**: `solveFn xs = true ↔ Reaches xs`. -/
theorem solve_correct (xs : SnocList Nat Nat) : solveFn xs = true ↔ Reaches xs := by
  show (foldFn xs).2 = true ↔ ReachIdx xs (len xs - 1)
  rw [ok_iff_allReach]
  constructor
  · intro hall
    exact hall (len xs - 1) (by have := len_pos xs; omega)
  · intro hreach j hj
    exact ReachIdx_mono_le hreach (by omega)

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
  show (b = solveFn xs) ↔ (b = true ↔ Reaches xs)
  constructor
  · intro h; rw [h]; exact solve_correct xs
  · intro h
    have h' : (b = true) ↔ (solveFn xs = true) := h.trans (solve_correct xs).symm
    exact bool_eq_of_iff_true h'

/-! ## Running the program -/

/-- Build a jump-length array from a first element and the rest, in index order. -/
def ofList (first : Nat) (rest : List Nat) : SnocList Nat Nat :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 2 [3, 1, 1, 4]) = true := by decide
example : solveFn (ofList 3 [2, 1, 0, 4]) = false := by decide
example : solveFn (ofList 0 []) = true := by decide
example : solveFn (ofList 1 [0]) = true := by decide

end Freyd.Alg.RelSet.LC55
