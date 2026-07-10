/-
  LeetCode 338 — Counting Bits — as an ALLEGORY PROGRAM.

  Problem: given `n`, return the list `[popcount 0, popcount 1, …, popcount n]`, where `popcount
  m` is the Hamming weight (number of `1`-bits) of `m`.

  NEW skill (contrast `L70`/`L91`/`L62`): those DP folds carry a fixed-lag window (a PAIR, a
  TRIPLE, a whole row scanned in lockstep) and read back only the IMMEDIATELY preceding state(s).
  Here the answer itself is a whole growing `List Nat`, and the DP step for entry `i` reads back
  an EARLIER, non-adjacent entry `bits[i/2]` (valid since `i/2 < i` for `i ≥ 1`) — indexing into
  the already-built prefix, not just carrying its last cell(s) forward.

  1. **Spec** — `popcount : Nat → Nat`, the honest halving recurrence `popcount 0 = 0, popcount m
     = popcount (m/2) + m%2`; well-founded on `m` (`m/2 < m` for `m ≠ 0`), so — like `L62`'s
     `paths` — its defining equation holds only propositionally, via the auto-generated
     `popcount.eq_1`/`popcount.eq_2`, not `rfl` (a bare `simp [popcount]` here LOOPS — "Possibly
     looping simp theorem `popcount.eq_1`" — so the equation lemmas are applied directly instead).
     The explicit target list `target n = [popcount 0, …, popcount n]` is built by `++`,
     structurally recursive in `n`.
  2. **Program** — `solveFn : Nat → List Nat` builds the SAME list left to right: `solveFn (n+1)
     = solveFn n ++ [solveFn n `.getD` ((n+1)/2) 0 + (n+1)%2]`, reusing the already-computed
     prefix instead of recomputing `popcount (n+1)` from scratch by repeated halving.
  3. **Refinement (equality)** — `solveFn n = target n`, by induction on `n`; the successor step
     needs `target n`'s entry at index `(n+1)/2` to BE `popcount ((n+1)/2)` (`target_getD`, a
     dedicated indexing lemma proved by induction on `target`, since core Lean has no
     `List.getD_append_left/right` lemmas to reuse — added here as local helpers).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC338

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data -/

/-- The input/index object: natural numbers, in `Rel(Set)`. -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩
/-- The answer object: lists of bit-counts, in `Rel(Set)`. -/
abbrev dList : RelSet.{0} := ⟨List Nat⟩

/-! ## Spec: the honest bit-count, and the target list it names -/

/-- Hamming weight of `m` — the honest halving recurrence, well-founded on `m` (`m/2 < m` for
    `m ≠ 0`). -/
def popcount : Nat → Nat
  | 0 => 0
  | (m + 1) => popcount ((m + 1) / 2) + (m + 1) % 2
  termination_by m => m
  decreasing_by exact Nat.div_lt_self (by omega) (by omega)

@[simp] theorem popcount_zero : popcount 0 = 0 := popcount.eq_1

/-- The defining equation at a successor — propositional only (well-founded recursion), needs
    the auto-generated equation lemma rather than `rfl` (cf. `L62`'s `paths`, `S10`). -/
theorem popcount_succ (m : Nat) : popcount (m + 1) = popcount ((m + 1) / 2) + (m + 1) % 2 :=
  popcount.eq_2 m

/-- The explicit target: `[popcount 0, …, popcount n]`, built by `++` (structural recursion in
    `n`) — "the definition of the answer" `L62`-style. -/
def target : Nat → List Nat
  | 0 => [popcount 0]
  | (n + 1) => target n ++ [popcount (n + 1)]

@[simp] theorem target_length : ∀ n, (target n).length = n + 1
  | 0 => rfl
  | (n + 1) => by simp [target, target_length n]

/-- The **specification** as a morphism `dNat ⟶ dList` in `Rel(Set)`: `n` relates to `target n`. -/
def spec : dNat ⟶ dList := fun n xs => xs = target n

/-! ## Two local `List.getD`/`++` lemmas (core Lean has no `getD_append_left/right`) -/

theorem getD_append_left {l₁ l₂ : List Nat} {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {l₁ l₂ : List Nat} {i : Nat} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- **Indexing lemma**: `target n`'s entry at any index `i ≤ n` IS `popcount i` — the content that
    makes reading `target n `.getD` ((n+1)/2) 0` back out legitimate. -/
theorem target_getD : ∀ n i, i ≤ n → (target n).getD i 0 = popcount i
  | 0, i, hi => by
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0; rfl
  | (n + 1), i, hi => by
    rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · have hile : i ≤ n := Nat.lt_succ_iff.mp hlt
      show (target n ++ [popcount (n + 1)]).getD i 0 = popcount i
      have hlen : i < (target n).length := by rw [target_length]; exact hlt
      rw [getD_append_left hlen]
      exact target_getD n i hile
    · have hieq : i = n + 1 := Nat.le_antisymm hi hge
      subst hieq
      show (target n ++ [popcount (n + 1)]).getD (n + 1) 0 = popcount (n + 1)
      have hlen : (target n).length ≤ n + 1 := Nat.le_of_eq (target_length n)
      rw [getD_append_right hlen]
      simp [target_length]

/-! ## Program: the O(n) DP — read `bits[i/2]` back from the growing prefix -/

/-- The DP: `bits[i] = bits[i/2] + i%2`, reading `bits[i/2]` back from the ALREADY-COMPUTED
    prefix (`(n+1)/2 ≤ n`, so it always lands inside `solveFn n`). -/
def solveFn : Nat → List Nat
  | 0 => [0]
  | (n + 1) =>
    let prev := solveFn n
    prev ++ [prev.getD ((n + 1) / 2) 0 + (n + 1) % 2]

/-- **The allegory program**: LeetCode 338's O(n) DP solution as a morphism `dNat ⟶ dList`. -/
def solve : dNat ⟶ dList := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## Correctness: `solveFn` builds exactly the target list -/

/-- **The DP list IS the target list**: `solveFn n = target n`, for every `n` — an equality
    refinement (like `L70`/`L62`), not the `⊑`-refinement of the optimisation scans. -/
theorem solveFn_eq_target : ∀ n, solveFn n = target n
  | 0 => by simp [solveFn, target]
  | (n + 1) => by
    show solveFn n ++ [(solveFn n).getD ((n + 1) / 2) 0 + (n + 1) % 2] = target (n + 1)
    rw [solveFn_eq_target n]
    have hhalf : (n + 1) / 2 ≤ n := by omega
    rw [target_getD n ((n + 1) / 2) hhalf, ← popcount_succ n]
    rfl

/-- **Correctness of the allegory program**: `solve = spec` as morphisms in `Rel(Set)`. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro n xs
  show xs = solveFn n ↔ xs = target n
  rw [solveFn_eq_target]

/-- **Correctness, unpacked**: `solveFn` builds `target n`, and `target n`'s `i`-th entry (`i ≤
    n`) really is `popcount i` — the content behind the bare equality. -/
theorem solve_correct (n : Nat) :
    solveFn n = target n ∧ ∀ i, i ≤ n → (target n).getD i 0 = popcount i :=
  ⟨solveFn_eq_target n, fun i hi => target_getD n i hi⟩

/-! ## Running the program -/

example : solveFn 2 = [0, 1, 1] := by decide
example : solveFn 5 = [0, 1, 1, 2, 1, 2] := by decide
example : solveFn 0 = [0] := by decide

end Freyd.Alg.RelSet.LC338
