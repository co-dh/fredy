/-
  LeetCode 1137 — N-th Tribonacci Number — as an ALLEGORY PROGRAM.

  Problem: `T 0 = 0`, `T 1 = 1`, `T 2 = 1`, `T (n+3) = T(n+2) + T(n+1) + T n`. Return `T n`.

  Same recipe as `Fredy/L70.lean` (`Fredy/leetcode.md`, skill S6): the naive textbook recurrence
  is already the exact answer, exponential-time only because it re-expands into THREE recursive
  calls at every step. The fix is again tupling/linearization — but here the carried state is a
  TRIPLE `(T n, T(n+1), T(n+2))` instead of `L70`'s pair, one dimension up (the `L91`/S9
  generalization of the same move).

  1. **Spec** — `spec : ℕ ⟶ ℕ` relates `n` to `trib n`, the naive recurrence.
  2. **Program** — `solve : ℕ ⟶ ℕ` is the `Map` `graph solveFn`, where `solveFn n = (tribTriple
     n).1` and `tribTriple n = (T n, T(n+1), T(n+2))` computed by a single O(n) structural
     recursion carrying the triple.
  3. **Refinement** — `tribTriple n = (trib n, trib (n+1), trib (n+2))` by one induction on `n`
     (the successor step is exactly the book recurrence `trib (n+3) = trib (n+2) + trib (n+1) +
     trib n`, used definitionally up to a commutative reordering of the sum). Hence `solveFn n =
     trib n` and `solve = spec` as relations.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC1137

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: `ℕ`, the initial algebra of `G X = 1 + X` -/

/-- The answer/data object: natural numbers, in `Rel(Set)`. -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## Spec: the naive exponential recurrence — "the definition of the answer" -/

/-- The `n`-th Tribonacci number, computed the naive (exponential-time) way — accepted AS the
    definition, exactly as `L70`'s `climb`. -/
def trib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | (n+3) => trib (n+2) + trib (n+1) + trib n

/-- The **specification** as a morphism `dNat ⟶ dNat` in `Rel(Set)`: `n` relates to `trib n`. -/
def spec : dNat ⟶ dNat := fun n k => k = trib n

/-! ## Program: the O(n) TUPLED fold — carry `(trib i, trib (i+1), trib (i+2))` -/

/-- The linear-recursion triple `(trib n, trib (n+1), trib (n+2))`, computed in one O(n) pass:
    each step only adds the three carried values, never re-expanding `trib`. -/
def tribTriple : Nat → Nat × Nat × Nat
  | 0 => (0, 1, 1)
  | (n+1) => let (a, b, c) := tribTriple n; (b, c, a + b + c)

/-- The answer: the first component of the tupled fold. -/
def solveFn (n : Nat) : Nat := (tribTriple n).1

/-- **The allegory program**: LeetCode 1137's O(n) solution as a morphism `dNat ⟶ dNat`. -/
def solve : dNat ⟶ dNat := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## The refinement lemma: tupling linearizes the naive recurrence -/

/-- **The point of the file**: the tupled fold computes exactly the triple of consecutive `trib`
    values. The successor step uses the book recurrence `trib (n+3) = trib (n+2) + trib (n+1) +
    trib n` up to reordering the sum (`Nat.add_assoc`/`Nat.add_comm`). -/
theorem tribTriple_eq : ∀ n, tribTriple n = (trib n, trib (n+1), trib (n+2))
  | 0 => rfl
  | (n+1) => by
    show (let (a, b, c) := tribTriple n; (b, c, a + b + c))
        = (trib (n+1), trib (n+1+1), trib (n+1+1+1))
    rw [tribTriple_eq n]
    show (trib (n+1), trib (n+2), trib n + trib (n+1) + trib (n+2))
        = (trib (n+1), trib (n+2), trib (n+1+1+1))
    rw [Nat.add_assoc, Nat.add_comm (trib n) (trib (n+1) + trib (n+2)),
        Nat.add_comm (trib (n+1)) (trib (n+2))]
    rfl

/-! ## Correctness: `solve` computes exactly `spec` -/

/-- `solveFn` agrees with the naive spec at every `n` — the refinement is exact, not just an
    inequality (unlike the optimization problems `L121`/`L53`/`L152`, there is nothing to choose
    among: `trib` already names the unique right answer). -/
theorem solve_correct (n : Nat) : solveFn n = trib n := by
  show (tribTriple n).1 = trib n
  rw [tribTriple_eq n]

/-- **Correctness of the allegory program**: `solve = spec` as morphisms in `Rel(Set)`. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro n k
  show k = solveFn n ↔ k = trib n
  rw [solve_correct]

/-! ## Running the program -/

example : solveFn 4 = 4 := by decide
example : solveFn 25 = 1389537 := by decide

end Freyd.Alg.RelSet.LC1137
