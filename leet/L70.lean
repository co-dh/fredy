/-
  LeetCode 70 — Climbing Stairs — as an ALLEGORY PROGRAM.

  Problem: `climb n` = the number of ways to climb `n` stairs taking 1 or 2 steps at a time.
  `climb 0 = 1`, `climb 1 = 1`, `climb (n+2) = climb (n+1) + climb n` (a Fibonacci-shifted
  recurrence).

  The point of this file is a DIFFERENT skill from `L121`/`L53`/`L152`: those refine a spec into
  a fold that carries auxiliary state; here the naive `spec` recurrence is already the exact
  answer — the only inefficiency is that computing it directly costs exponential time (each
  `climb (n+2)` call re-expands into two recursive calls). The fix is **tupling /
  linearization**: instead of computing `climb n` alone, compute the PAIR `(climb n, climb
  (n+1))` by a single linear recursion, so each step reuses both previous values instead of
  recomputing them. This is the classic Bird–de Moor trick behind e.g. fast Fibonacci.

  Also unlike `L121`/`L53`/`L152`, the data object is not a `SnocList` — it is `ℕ` itself, the
  initial algebra of `G X = 1 + X` (`zero`/`succ`), imported wholesale from `AOP.A6_SnocList`'s
  companion `Fredy.Exacts` for the `RelSet`/`graph`/`Map`/`hom_ext` machinery.

  1. **Spec** — `spec : ℕ ⟶ ℕ` relates `n` to `climb n`, the naive recurrence (`Λ⁻¹ spec`).
  2. **Program** — `solve : ℕ ⟶ ℕ` is the `Map` (graph of a function) `graph solveFn`, where
     `solveFn n = (fibPair n).1` and `fibPair n = (climb n, climb (n+1))` computed by a single
     O(n) structural recursion carrying the pair.
  3. **Refinement** — `fibPair n = (climb n, climb (n+1))` by one induction on `n` (the successor
     step is exactly the book recurrence `climb (n+2) = climb (n+1) + climb n`, used
     definitionally). Hence `solveFn n = climb n` and `solve = spec` as relations.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC70

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: `ℕ`, the initial algebra of `G X = 1 + X` -/

/-- The answer/data object: natural numbers, in `Rel(Set)`. -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## Spec: the naive exponential recurrence — "the definition of the answer" -/

/-- The number of ways to climb `n` stairs, 1 or 2 steps at a time — the Fibonacci-shifted
    recurrence, computed the naive (exponential-time) way. -/
def climb : Nat → Nat
  | 0 => 1
  | 1 => 1
  | (n+2) => climb (n+1) + climb n

/-- The **specification** as a morphism `dNat ⟶ dNat` in `Rel(Set)`: `n` relates to `climb n`. -/
def spec : dNat ⟶ dNat := fun n k => k = climb n

/-! ## Program: the O(n) TUPLED fold — carry `(climb i, climb (i+1))` -/

/-- The linear-recursion pair `(climb n, climb (n+1))`, computed in one O(n) pass: each step
    only adds the two carried values, never re-expanding `climb`. -/
def fibPair : Nat → Nat × Nat
  | 0 => (1, 1)
  | (n+1) => let (a, b) := fibPair n; (b, a + b)

/-- The answer: the first component of the tupled fold. -/
def solveFn (n : Nat) : Nat := (fibPair n).1

/-- **The allegory program**: LeetCode 70's O(n) solution as a morphism `dNat ⟶ dNat`. -/
def solve : dNat ⟶ dNat := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## The refinement lemma: tupling linearizes the naive recurrence -/

/-- **The point of the file**: the tupled fold computes exactly the pair of consecutive `climb`
    values. The successor step uses the book recurrence `climb (n+2) = climb (n+1) + climb n`
    definitionally (`Nat.add_comm` reorders it to the `fibPair` sum). -/
theorem fibPair_eq : ∀ n, fibPair n = (climb n, climb (n+1))
  | 0 => rfl
  | (n+1) => by
    show (let (a, b) := fibPair n; (b, a + b)) = (climb (n+1), climb (n+1+1))
    rw [fibPair_eq n]
    show (climb (n+1), climb n + climb (n+1)) = (climb (n+1), climb (n+1+1))
    rw [Nat.add_comm (climb n) (climb (n+1))]
    rfl

/-! ## Correctness: `solve` computes exactly `spec` -/

/-- `solveFn` agrees with the naive spec at every `n` — the refinement is exact, not just an
    inequality (unlike the optimization problems `L121`/`L53`/`L152`, there is nothing to choose
    among: `climb` already names the unique right answer). -/
theorem solve_correct (n : Nat) : solveFn n = climb n := by
  show (fibPair n).1 = climb n
  rw [fibPair_eq n]

/-- **Correctness of the allegory program**: `solve = spec` as morphisms in `Rel(Set)`. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro n k
  show k = solveFn n ↔ k = climb n
  rw [solve_correct]

/-! ## Running the program -/

example : solveFn 0 = 1 := by decide
example : solveFn 1 = 1 := by decide
example : solveFn 2 = 2 := by decide
example : solveFn 3 = 3 := by decide
example : solveFn 5 = 8 := by decide

end Freyd.Alg.RelSet.LC70
