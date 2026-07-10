/-
  LeetCode 268 — Missing Number — as an ALLEGORY PROGRAM.

  Problem: given a `SnocList Nat Nat` of `n` DISTINCT numbers drawn from `{0,…,n}` (one is
  missing), return the missing one.

  Same recipe as `leet/L121.lean`/`leet/L191.lean` (see `Fredy/leetcode.md`, skill S0/S8):

  1. **Data** — the numbers form the initial algebra `SnocList ℕ ℕ` of `F X = ℕ + X×ℕ`
     (`AOP.A6_SnocList`); `wrap x` is a single number, `snoc xs p` appends one.

  2. **Program** — the O(n) Gauss-sum sweep: fold `(size, sum)`, then compute
     `triangle size − sum` where `triangle n := n*(n+1)/2`. Packaged as `solve := graph solveFn`,
     proved equal to the relational catamorphism of that pair-algebra followed by the extraction
     `(n,s) ↦ triangle n − s` (`solve_eq_cata`).

  3. **Specification** — `IsValidInput xs` is the LeetCode precondition (pairwise distinct, all
     values `≤ size xs`, i.e. drawn from the `size xs + 1`-element range `{0,…,size xs}`);
     `spec xs m := m ≤ size xs ∧ m ∉ xs` says `m` is exactly the missing value.

  4. **Correctness** — **NB, fallback taken** (per this file's task spec, explicitly sanctioned):
     the FULL statement `IsValidInput xs → spec xs (solveFn xs)` needs a genuine pigeonhole /
     cardinality argument (distinctness + a tight bound forces exactly one value absent). Doing
     that constructively over `SnocList` hits a real obstacle: the natural inductive proof peels
     off one value at a time and needs to shrink the list past size `0`, but `SnocList` is
     non-empty *by construction* (no `nil`), so a "remove one occurrence" helper can't be typed to
     return a smaller `SnocList` in general (only `List` naturally supports that, via `[]`/
     `List.erase`) — bridging to `List` and re-doing the induction there is real extra
     infrastructure, disproportionate to one LeetCode problem. Instead we prove the arithmetic
     mechanism in full rigor:
     - `even_mul_succ`/`triangle_even`: `n*(n+1)` is always even, so `triangle n := n*(n+1)/2` is
       an EXACT (non-truncating) division — the Gauss-sum identity `2 * triangle n = n*(n+1)`.
     - `solve_correct_witnessed`: GIVEN the missing value `m` together with its defining sum
       equation `sumFn xs + m = triangle (size xs)`, `solveFn` recovers exactly `m` and `spec`
       holds. This is the honest arithmetic content of the Gauss-sum trick (subtracting the
       actual sum from the full range's sum recovers exactly what's missing), stated with the
       existence of the witness as a hypothesis instead of derived from `IsValidInput` alone.
     We then discharge the three `decide` examples via `solve_correct_witnessed`, supplying an
     explicit witness for each (checked by `decide`), on top of the raw `decide` on `solveFn`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC268

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: a snoc-list of numbers -/

/-- The object of number lists in `Rel(Set)` — `SnocList Nat Nat`. -/
abbrev Nums : RelSet.{0} := dSL Nat Nat
/-- The object of natural numbers (the missing value) in `Rel(Set)`. -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## Plain recursive descriptions: size, sum, membership, distinctness -/

/-- `size xs` — the number of elements in `xs`. -/
def size : SnocList Nat Nat → Nat
  | SnocList.wrap _ => 1
  | SnocList.snoc xs _ => size xs + 1

/-- `sumFn xs` — the sum of every element of `xs`. -/
def sumFn : SnocList Nat Nat → Nat
  | SnocList.wrap x => x
  | SnocList.snoc xs p => sumFn xs + p

/-- `mem xs b` — the value `b` occurs in `xs`. -/
def mem : SnocList Nat Nat → Nat → Prop
  | SnocList.wrap x => fun b => b = x
  | SnocList.snoc xs p => fun b => mem xs b ∨ b = p

/-- `NoDup xs` — every value in `xs` occurs at most once. -/
def NoDup : SnocList Nat Nat → Prop
  | SnocList.wrap _ => True
  | SnocList.snoc xs p => NoDup xs ∧ ¬ mem xs p

/-- **`IsValidInput`** — the LeetCode precondition: pairwise distinct AND drawn from
    `{0,…,size xs}` (`size xs` numbers out of `size xs + 1` possible values, so exactly one is
    missing). -/
def IsValidInput (xs : SnocList Nat Nat) : Prop := NoDup xs ∧ ∀ e, mem xs e → e ≤ size xs

/-- `mem` is decidable (needed so `decide` can discharge concrete membership facts below). -/
instance memDecidable : (xs : SnocList Nat Nat) → (b : Nat) → Decidable (mem xs b)
  | SnocList.wrap x, b => inferInstanceAs (Decidable (b = x))
  | SnocList.snoc xs p, b =>
      match memDecidable xs b, inferInstanceAs (Decidable (b = p)) with
      | isTrue h, _ => isTrue (Or.inl h)
      | isFalse h, isTrue h2 => isTrue (Or.inr h2)
      | isFalse h, isFalse h2 => isFalse (fun hc => hc.elim h h2)

/-! ## The Gauss-sum triangular number, exactly halved -/

/-- The `n`-th triangular number `0+1+⋯+n = n*(n+1)/2`. -/
def triangle (n : Nat) : Nat := n * (n + 1) / 2

/-- `n*(n+1)` is always even — of two consecutive numbers, one is even. -/
theorem even_mul_succ (n : Nat) : ∃ k, n * (n + 1) = 2 * k := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + m + 1, ?_⟩
    have step : (m + 1) * (m + 1 + 1) = m * (m + 1) + m + (m + 1 + 1) := by
      rw [Nat.succ_mul, Nat.mul_succ]
    rw [step, hk]; omega

/-- **The Gauss-sum identity**: `triangle n`'s division by `2` is EXACT — `2 * triangle n =
    n*(n+1)`, not merely `≤`. This is the "new skill" this file exercises: an even-product `/2`
    exactness lemma, needed anywhere a Nat program divides by a constant and expects no
    truncation. -/
theorem triangle_even (n : Nat) : 2 * triangle n = n * (n + 1) := by
  obtain ⟨k, hk⟩ := even_mul_succ n
  show 2 * (n * (n + 1) / 2) = n * (n + 1)
  rw [hk]; omega

/-- The successor step of the triangular numbers: `triangle (n+1) = triangle n + (n+1)`. -/
theorem triangle_succ (n : Nat) : triangle (n + 1) = triangle n + (n + 1) := by
  have h1 := triangle_even n
  have h2 := triangle_even (n + 1)
  have expand : (n + 1) * (n + 1 + 1) = n * (n + 1) + n + (n + 1 + 1) := by
    rw [Nat.succ_mul, Nat.mul_succ]
  rw [expand] at h2
  omega

/-! ## The program: the Gauss-sum sweep, packaged as a catamorphism followed by an extraction -/

/-- The fold algebra `[ x ↦ (1,x),  ((n,s),p) ↦ (n+1, s+p) ] : F(ℕ×ℕ) → ℕ×ℕ`, accumulating
    `(size, sum)`. -/
def algFn : (Fobj Nat Nat (⟨Nat × Nat⟩ : RelSet.{0})).carrier → (Nat × Nat)
  | Sum.inl x => (1, x)
  | Sum.inr (st, p) => (st.1 + 1, st.2 + p)

/-- The algebra as a morphism (a `Map`) `F(ℕ×ℕ) ⟶ ℕ×ℕ` in `Rel(Set)`. -/
def alg : Fobj Nat Nat (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ (⟨Nat × Nat⟩ : RelSet.{0}) := graph algFn

/-- The concrete fold (structural recursion), returning `(size, sum)`. -/
def foldFn : SnocList Nat Nat → Nat × Nat
  | SnocList.wrap x => (1, x)
  | SnocList.snoc xs p => ((foldFn xs).1 + 1, (foldFn xs).2 + p)

theorem foldFn_fst : ∀ xs, (foldFn xs).1 = size xs := by
  intro xs; induction xs with
  | wrap x => rfl
  | snoc xs p ih => show (foldFn xs).1 + 1 = size xs + 1; rw [ih]

theorem foldFn_snd : ∀ xs, (foldFn xs).2 = sumFn xs := by
  intro xs; induction xs with
  | wrap x => rfl
  | snoc xs p ih => show (foldFn xs).2 + p = sumFn xs + p; rw [ih]

/-- **The Gauss-sum program**: `triangle size − sum`. -/
def solveFn (xs : SnocList Nat Nat) : Nat := triangle (size xs) - sumFn xs

/-- **The allegory program**: LeetCode 268's solution as a morphism `Nums ⟶ ℕ` in `Rel(Set)`. -/
def solve : Nums ⟶ dNat := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree. -/
theorem cataFold_alg : ∀ (xs : SnocList Nat Nat) (r : Nat × Nat),
    cataFold alg xs r ↔ r = foldFn xs := by
  intro xs; induction xs with
  | wrap x => intro r; exact Iff.rfl
  | snoc xs p ih =>
    intro r
    simp only [cataFold_snoc]
    constructor
    · rintro ⟨r', hr', hfr⟩
      rw [ih r'] at hr'; subst hr'; exact hfr
    · intro h; exact ⟨foldFn xs, (ih (foldFn xs)).mpr rfl, h⟩

/-- `solveFn` matches the extraction applied to the pair-catamorphism's fold state. -/
theorem solveFn_eq_fold (xs : SnocList Nat Nat) :
    solveFn xs = triangle (foldFn xs).1 - (foldFn xs).2 := by
  show triangle (size xs) - sumFn xs = triangle (foldFn xs).1 - (foldFn xs).2
  rw [foldFn_fst, foldFn_snd]

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈ ≫ extract`, a fold followed by the
    extraction `(size,sum) ↦ triangle size − sum`. -/
theorem solve_eq_cata :
    solve = cataR alg ≫ graph (fun p : Nat × Nat => triangle p.1 - p.2) := by
  apply hom_ext; intro xs v
  simp only [solve, graph, comp_apply, cataR]
  rw [solveFn_eq_fold]
  constructor
  · intro hv; exact ⟨foldFn xs, (cataFold_alg xs (foldFn xs)).mpr rfl, hv⟩
  · rintro ⟨st, hst, hv⟩; rw [(cataFold_alg xs st).mp hst] at hv; exact hv

/-! ## Specification: the missing value -/

/-- The **specification** as a morphism `Nums ⟶ ℕ` in `Rel(Set)`: `m` is the missing value —
    in range and absent. -/
def spec (xs : SnocList Nat Nat) (m : Nat) : Prop := m ≤ size xs ∧ ¬ mem xs m

/-! ## Correctness: the WITNESSED Gauss-sum arithmetic (see file docstring for the fallback taken)

    Given the missing value `m` together with its defining sum equation, `solveFn` recovers `m`
    exactly and `spec` holds. Deriving the EXISTENCE of such `m` from `IsValidInput` alone (the
    full distinctness→sum pigeonhole argument) is the heavy part this file does not attempt — see
    the docstring for why. -/
theorem solve_correct_witnessed (xs : SnocList Nat Nat) (m : Nat)
    (hm : m ≤ size xs) (hnm : ¬ mem xs m) (hsum : sumFn xs + m = triangle (size xs)) :
    solveFn xs = m ∧ spec xs (solveFn xs) := by
  have heq : solveFn xs = m := by show triangle (size xs) - sumFn xs = m; omega
  exact ⟨heq, heq ▸ ⟨hm, hnm⟩⟩

/-! ## Running the program -/

/-- Build a number list from a first number and the rest, in order. -/
def ofList (first : Nat) (rest : List Nat) : SnocList Nat Nat :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 3 [0, 1]) = 2 := by decide
example : solveFn (ofList 0 []) = 1 := by decide
example : solveFn (ofList 9 [6, 4, 2, 3, 5, 7, 0, 1]) = 8 := by decide

/-- `solve_correct_witnessed` applied to the first `decide` example, with the missing value `2`
    supplied as an explicit witness (its defining sum equation checked by `decide`). -/
example : spec (ofList 3 [0, 1]) 2 :=
  (solve_correct_witnessed (ofList 3 [0, 1]) 2 (by decide) (by decide) (by decide)).2

example : spec (ofList 0 []) 1 :=
  (solve_correct_witnessed (ofList 0 []) 1 (by decide) (by decide) (by decide)).2

example : spec (ofList 9 [6, 4, 2, 3, 5, 7, 0, 1]) 8 :=
  (solve_correct_witnessed (ofList 9 [6, 4, 2, 3, 5, 7, 0, 1]) 8 (by decide) (by decide)
    (by decide)).2

end Freyd.Alg.RelSet.LC268
