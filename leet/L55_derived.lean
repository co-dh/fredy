/-
  LeetCode 55 — Jump Game — the greedy reachability DECISION fold DERIVED as a snoc-list
  catamorphism (general-carrier law).

  `leet/L55.lean` writes the greedy scan `foldFn : SnocList Nat Nat → Nat × Bool` (state
  `(maxReach, ok)`) directly and verifies it by induction.  This file makes that fold EMERGE
  from the reusable general-carrier snoc-fold-uniqueness law `SL.snocFold_unique`
  (`AOP/A6_GenFold.lean`) — the "any carrier `C`" generalisation of `tupling`.

  A wrinkle vs. `L198_derived`'s pair-DP: `foldFn`'s `snoc` clause does not depend on
  `(foldFn xs).1, (foldFn xs).2` ALONE — it also reads `len xs`, the running INDEX, to decide
  whether the newly-processed position is itself reachable (`len xs > (foldFn xs).1`).  `len xs`
  is NOT recoverable from `(maxReach, ok)` alone: once `ok` turns `false`, `maxReach` freezes
  while `len` keeps growing, so the pair loses the index.  The carrier is therefore widened to
  the TRIPLE `C := Nat × Nat × Bool` — `(idx, maxReach, ok)` — tracking whatever auxiliary
  quantity the step genuinely reads (the same "amount/row axis" bookkeeping the course-of-values
  DP carriers already use).  Base and step are then FORCED — they are `foldFn`'s (and `len`'s)
  own defining equations:

    * base `g x = (1, x, true)`                     = `(len (wrap x), foldFn (wrap x))`
    * step `step (idx,mx,ok) p =`
        `if idx > mx then (idx+1, mx, false) else (idx+1, imax mx (idx+p), ok)`
                                                      = `(len (snoc xs p), foldFn (snoc xs p))`
      with `(idx,mx,ok) = (len xs, foldFn xs)`.

  Feeding `g`/`step`/`h` (`h xs := (len xs, foldFn xs)`) to `snocFold_unique` PRODUCES the
  index-aware greedy scan as `cataR (scalarAlg g step)` — never hand-written as a fold.  Reading
  off the third (`ok`) component of `h` recovers `LC55.solveFn` exactly (`rfl`), so the derived
  program `derivedSolve` equals `LC55.solve`, and correctness (`LC55.solve_eq_spec`, itself a
  decision-problem morphism EQUALITY, not just a pointwise `Iff`) transports unchanged: no
  reachability argument is re-proved here.

  Complexity: `h` (equivalently `foldFn`) is one structural pass over the `n`-element `SnocList`,
  O(1) work per `snoc` (one comparison, one `imax`) — O(n) overall, matching `LC55.foldFn`.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L55

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC55D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The ANSATZ carrier and its FORCED base/step

  Carrier `C := Nat × Nat × Bool = (idx, maxReach, ok)`.  `idx` must ride along because the
  greedy step reads the CURRENT prefix length (`len xs`), which the pair `(maxReach, ok)` alone
  cannot reconstruct once a failure has frozen `maxReach`. -/

/-- The base of the emergent algebra: `(len (wrap x), foldFn (wrap x)) = (1, x, true)`. -/
def g : Nat → Nat × Nat × Bool := fun x => (1, x, true)

/-- The step of the emergent algebra: given `(idx, mx, ok) = (len xs, foldFn xs)` and a new
    jump-length `p`, either the new position `idx` is unreachable (`idx > mx`, `ok` turns `false`
    for good) or it grows `mx` to `imax mx (idx + p)` and carries `ok`; `idx` always advances by 1,
    mirroring `len (snoc xs p) = len xs + 1`. -/
def step : Nat × Nat × Bool → Nat → Nat × Nat × Bool :=
  fun st p => if st.1 > st.2.1 then (st.1 + 1, st.2.1, false)
              else (st.1 + 1, LC55.imax st.2.1 (st.1 + p), st.2.2)

/-- The witness function: pairs `len` with `foldFn`, so its own recursion equations ARE `g`/`step`
    applied to `len`'s and `foldFn`'s. -/
def h : SnocList Nat Nat → Nat × Nat × Bool :=
  fun xs => (LC55.len xs, (LC55.foldFn xs).1, (LC55.foldFn xs).2)

/-- The base condition is a COMPUTATION: `h (wrap x) = g x` (both sides reduce to `(1, x, true)`). -/
theorem h_wrap : ∀ x : Nat, h (SnocList.wrap x) = g x := fun x => rfl

/-- The step condition IS `foldFn`'s (and `len`'s) `snoc` equation, case-split exactly as
    `foldFn` itself is (`foldFn_snoc_fail`/`foldFn_snoc_ok`). -/
theorem h_snoc : ∀ (xs : SnocList Nat Nat) (p : Nat), h (SnocList.snoc xs p) = step (h xs) p := by
  intro xs p
  by_cases hfail : LC55.len xs > (LC55.foldFn xs).1
  · show (LC55.len xs + 1, (LC55.foldFn (SnocList.snoc xs p)).1, (LC55.foldFn (SnocList.snoc xs p)).2)
      = step (LC55.len xs, (LC55.foldFn xs).1, (LC55.foldFn xs).2) p
    rw [LC55.foldFn_snoc_fail hfail]
    show (LC55.len xs + 1, (LC55.foldFn xs).1, false)
      = step (LC55.len xs, (LC55.foldFn xs).1, (LC55.foldFn xs).2) p
    unfold step
    rw [if_pos hfail]
  · replace hfail : LC55.len xs ≤ (LC55.foldFn xs).1 := Nat.not_lt.mp hfail
    show (LC55.len xs + 1, (LC55.foldFn (SnocList.snoc xs p)).1, (LC55.foldFn (SnocList.snoc xs p)).2)
      = step (LC55.len xs, (LC55.foldFn xs).1, (LC55.foldFn xs).2) p
    rw [LC55.foldFn_snoc_ok hfail]
    show (LC55.len xs + 1, LC55.imax (LC55.foldFn xs).1 (LC55.len xs + p), (LC55.foldFn xs).2)
      = step (LC55.len xs, (LC55.foldFn xs).1, (LC55.foldFn xs).2) p
    unfold step
    rw [if_neg (show ¬ (LC55.len xs > (LC55.foldFn xs).1) by omega)]

/-! ## The greedy scan EMERGES via the general-carrier snoc-fold law -/

/-- **The derivation.**  `graph h` — pairing the array length with the greedy state — equals the
    catamorphism of the emergent algebra `scalarAlg g step`: the index-aware greedy scan was
    never written as a fold, it is PRODUCED by `snocFold_unique`. -/
theorem fold_derived :
    (graph h : dSL Nat Nat ⟶ ⟨Nat × Nat × Bool⟩) = cataR (scalarAlg g step) :=
  snocFold_unique g step h h_wrap h_snoc

/-! ## The derived program equals `LC55.solve` -/

/-- The derived allegory program: the third (`ok`) component of the emergent triple. -/
def derivedSolve : LC55.Jumps ⟶ LC55.dBool := graph (fun xs => (h xs).2.2)

/-- The derived program IS `LC55.solve`: `(h xs).2.2` unfolds to `(foldFn xs).2 = solveFn xs`,
    definitionally. -/
theorem derivedSolve_eq_solve : derivedSolve = LC55.solve := by
  show graph (fun xs => (h xs).2.2) = graph LC55.solveFn
  rfl

/-! ## Correctness of the derived program, reused from `L55.lean` -/

/-- **Headline.**  The Jump-Game decision program IS the general-carrier snoc catamorphism
    (`fold_derived`), and the derived solver equals the specification relation `LC55.spec`
    (`b = true ↔ Reaches xs`) — a genuine morphism EQUALITY, obtained by chaining
    `derivedSolve = LC55.solve` with the REUSED `LC55.solve_eq_spec`; the greedy
    soundness/completeness argument (`LC55.ok_iff_allReach`) is not re-proved here. -/
theorem jump_game_derived_correct :
    ((graph h : dSL Nat Nat ⟶ ⟨Nat × Nat × Bool⟩) = cataR (scalarAlg g step)) ∧
    (derivedSolve = LC55.spec) :=
  ⟨fold_derived, derivedSolve_eq_solve.trans LC55.solve_eq_spec⟩

/-! ## Running / cross-checking the emergent fold against `leet/L55.lean`

  The relational catamorphism `cataFold (scalarAlg …)` is not `decide`-computable (its `snoc`
  case is an existential over the carrier), so we `decide` the extensionally-equal computable
  witnesses `LC55.solveFn`/`h`, and separately PROVE that the emergent fold relates a concrete
  array to `h` of it. -/

example : LC55.solveFn (LC55.ofList 2 [3, 1, 1, 4]) = true := by decide
example : LC55.solveFn (LC55.ofList 3 [2, 1, 0, 4]) = false := by decide
example : (h (LC55.ofList 2 [3, 1, 1, 4])).2.2 = true := by decide

/-- The emergent fold genuinely relates a concrete array to `h` of it. -/
example :
    cataFold (scalarAlg g step) (LC55.ofList 2 [3, 1, 1, 4]) (h (LC55.ofList 2 [3, 1, 1, 4])) := by
  have hh : (graph h : dSL Nat Nat ⟶ ⟨Nat × Nat × Bool⟩)
      (LC55.ofList 2 [3, 1, 1, 4]) (h (LC55.ofList 2 [3, 1, 1, 4])) := rfl
  rw [fold_derived] at hh
  exact hh

end Freyd.Alg.RelSet.LC55D
