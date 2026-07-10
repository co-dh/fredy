/-
  LeetCode 338 — Counting Bits — DERIVED as an O(n) TABULATING DP over the AMOUNT axis, with an
  `Array Nat` carrier.

  `Fredy/L338.lean` builds `[popcount 0, …, popcount n]` by hand with a `List Nat` accumulator whose
  step is `prev ++ [prev.getD ((n+1)/2) 0 + (n+1)%2]`.  That is CORRECT but O(n²): `acc ++ [x]` copies
  the whole prefix on every step (O(n)), and the `List.getD ((n+1)/2)` read walks the list (O(n)).
  This file re-derives the SAME table as an emergent catamorphism whose carrier is `Array Nat`, so
  BOTH the write (`Array.push`, amortised O(1)) and the recurrence read (`Array.getD (i/2)`, O(1)) are
  O(1) — total O(n).

  The amount axis `0, 1, …, n` is `SnocList Unit Unit ≅ ℕ` (`SL.snocs`/`SL.natOf`,
  `Fredy/A6_8_Tupling.lean`), so tabulating over amounts is a snoc-fold with `L = E = Unit`.  The
  carried value is the DP table `T = #[dp[0], …, dp[i-1]]`; its size `i = T.size` is the next amount to
  fill, and the step pushes `dp[i] = dp[i/2] + i%2`, reading the already-built cell `T[i/2]` (`i/2 < i`
  for `i ≥ 1`, so it lands inside `T`):

    * base  `g ()   = #[0]`                                     (dp[0] = 0)
    * step  `st T () = T.push (T.getD (T.size/2) 0 + T.size%2)` (append dp[T.size])

  Feeding `g`/`st`/`dpFold` to the general-carrier fold-uniqueness law
  `Freyd.Alg.RelSet.SL.snocFold_unique` (`Fredy/A6_GenFold.lean`) PRODUCES the fold as
  `cataR (scalarAlg g st)` — the recursion is never written by hand; `dp_emerges` is the law's
  catamorphism.  Correctness is REUSED from `L338.lean`: the Array table, read out as a list, is
  `L338.solveFn n` (bridge `dpFold_toList`, by `Array.toList_push`/`size_eq_length_toList`), which
  `L338.solveFn_eq_target` already proves equals `[popcount 0, …, popcount n]`.  Since the answer is a
  function (an exact count), the headline is an EQUALITY refinement `derivedSolve = spec` (shape 1),
  not the `⊑`-refinement of the optimisation scans.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.L338

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC338D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The emergent algebra: carrier `Array Nat`, base `#[0]`, step `push (dp[i/2] + i%2)` -/

/-- Base of the emergent algebra: the amount-0 table `#[dp[0]] = #[0]`. -/
def g : Unit → Array Nat := fun _ => #[0]

/-- Step of the emergent algebra: at a table `T` of size `i = T.size`, append the next cell
    `dp[i] = dp[i/2] + i%2`, reading the already-built entry `T[i/2]` back from `T` (`i/2 < i` for
    `i ≥ 1`, so it always lands inside `T`).  Both `push` and `getD` are O(1). -/
def st : Array Nat → Unit → Array Nat :=
  fun T _ => T.push (T.getD (T.size / 2) 0 + T.size % 2)

/-- The DP-table fold (structural recursion over the amount axis), carrier `Array Nat`.
    `dpFold (snocs n)` is the table `#[popcount 0, …, popcount n]`. -/
def dpFold : SnocList Unit Unit → Array Nat
  | SnocList.wrap l    => g l
  | SnocList.snoc xs e => st (dpFold xs) e

/-- Base condition (`rfl`): `dpFold (wrap l) = g l`. -/
theorem dpFold_wrap (l : Unit) : dpFold (SnocList.wrap l) = g l := rfl

/-- Step condition (`rfl`): `dpFold (snoc xs e) = st (dpFold xs) e`. -/
theorem dpFold_snoc (xs : SnocList Unit Unit) (e : Unit) :
    dpFold (SnocList.snoc xs e) = st (dpFold xs) e := rfl

/-- **The derivation.**  The DP-table fold is PRODUCED by the general-carrier fold-uniqueness law —
    never written by hand: `graph dpFold` equals the catamorphism of the scalar algebra
    `scalarAlg g st`, carrier `Array Nat`.  The step is one O(1) `push` plus one O(1) `getD`. -/
theorem dp_emerges :
    (graph dpFold : dSL Unit Unit ⟶ ⟨Array Nat⟩) = cataR (scalarAlg g st) :=
  SL.snocFold_unique g st dpFold dpFold_wrap dpFold_snoc

/-! ## Bridge to the solved file: the Array table read out as a list is `L338.solveFn` -/

/-- Reading an `Array Nat` with `getD` agrees with reading its `toList` with `List.getD`. -/
theorem array_getD_toList (a : Array Nat) (i d : Nat) : a.getD i d = a.toList.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **The Array DP builds exactly `L338.solveFn`.**  Reading the emergent `Array Nat` table out as a
    list yields the same list the solved file's O(n²) `List` accumulator builds — so the O(n) fold and
    the verified O(n²) program agree, entry for entry.  Proved by induction: `push` becomes `++ [·]`
    (`Array.toList_push`), `Array.size` becomes `List.length` (`Array.size_eq_length_toList`), and the
    length `(solveFn n).length = n+1` matches the amount being filled. -/
theorem dpFold_toList : ∀ n, (dpFold (snocs n)).toList = LC338.solveFn n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show ((dpFold (snocs n)).push
        ((dpFold (snocs n)).getD ((dpFold (snocs n)).size / 2) 0
          + (dpFold (snocs n)).size % 2)).toList = LC338.solveFn (n + 1)
    rw [Array.toList_push, array_getD_toList, Array.size_eq_length_toList, ih]
    have hlen : (LC338.solveFn n).length = n + 1 := by
      rw [LC338.solveFn_eq_target, LC338.target_length]
    rw [hlen]; rfl

/-- The Array table read out as a list IS the target `[popcount 0, …, popcount n]`
    (`dpFold_toList` composed with `L338.solveFn_eq_target`). -/
theorem dpFold_toList_eq_target (n : Nat) : (dpFold (snocs n)).toList = LC338.target n := by
  rw [dpFold_toList n, LC338.solveFn_eq_target]

/-! ## The derived allegory program and its equality-refinement headline

  The answer is a FUNCTION (an exact bit-count list), so — like `L70`/`L91`/`L62` — the correctness
  headline is an EQUALITY of morphisms `derivedSolve = spec`, not the `⊑`-refinement of the
  optimisation scans.  `derivedSolve` on `ℕ` encodes `n` as `snocs n`, runs the emergent Array-DP
  fold, and reads the table out as a list. -/

/-- The derived allegory program `dNat ⟶ dList`: encode `n` as `snocs n`, run the emergent Array-DP
    fold `cataR (scalarAlg g st)`, read the table out with `Array.toList`. -/
def derivedSolve : LC338.dNat ⟶ LC338.dList :=
  graph snocs ≫ (cataR (scalarAlg g st) ≫ graph (fun t : Array Nat => t.toList))

/-- **Headline (equality refinement).**  The O(n) Array-DP program equals the specification
    `L338.spec` as morphisms in `Rel(Set)`: for every `n` it relates `n` to exactly the target list
    `[popcount 0, …, popcount n]`.  The table itself is the emergent catamorphism (`dp_emerges`); its
    correctness is reused from `L338.solveFn_eq_target`. -/
theorem derivedSolve_eq_spec : derivedSolve = LC338.spec := by
  apply RelSet.hom_ext; intro n xs
  show (graph snocs ≫ (cataR (scalarAlg g st) ≫ graph (fun t : Array Nat => t.toList))) n xs
      ↔ LC338.spec n xs
  rw [← dp_emerges]
  simp only [RelSet.comp_apply, RelSet.graph, LC338.spec]
  constructor
  · rintro ⟨s, hs, t, ht, hxs⟩
    subst hs; subst ht
    rw [hxs]; exact dpFold_toList_eq_target n
  · intro hxs
    exact ⟨snocs n, rfl, dpFold (snocs n), rfl, by rw [hxs]; exact (dpFold_toList_eq_target n).symm⟩

/-- `derivedSolve` is a `Map` (a composite of graphs). -/
theorem derivedSolve_map : Map derivedSolve := by
  rw [derivedSolve_eq_spec, ← LC338.solve_eq_spec]
  exact LC338.solve_map

/-- **Correctness, unpacked.**  The derived fold, read out, builds `target n`, and `target n`'s
    `i`-th entry (`i ≤ n`) really is `popcount i` — the content behind the equality
    (`L338.target_getD`, reused). -/
theorem derived_correct (n : Nat) :
    (dpFold (snocs n)).toList = LC338.target n
      ∧ ∀ i, i ≤ n → (LC338.target n).getD i 0 = LC338.popcount i :=
  ⟨dpFold_toList_eq_target n, fun i hi => LC338.target_getD n i hi⟩

/-! ## Running the O(n) program

  `#guard` evaluates the compiled `dpFold` (structural recursion + O(1) `Array.push`/`getD`),
  cross-checking the emergent table's list against the hand-written answers and against
  `L338.solveFn`. -/

#guard (dpFold (snocs 2)).toList = [0, 1, 1]
#guard (dpFold (snocs 5)).toList = [0, 1, 1, 2, 1, 2]
#guard (dpFold (snocs 5)).toList = LC338.solveFn 5
#guard (dpFold (snocs 0)).toList = [0]

end Freyd.Alg.RelSet.LC338D
