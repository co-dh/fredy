/-
  LeetCode 125 — Valid Palindrome — DERIVED as a catamorphism via the general-carrier
  fold-uniqueness law `Freyd.Alg.RelSet.SL.snocFold_unique`.

  `Fredy.L125` writes the list-reconstruction fold `toList` by hand and then decides reverse-equality
  on the result (`palinFn xs = decide (toList xs = (toList xs).reverse)`).  HERE we do the opposite:
  the fold is PRODUCED by the law.

  The carrier is `C := List Int` — a palindrome cannot be decided by a single scalar fold over the
  back-to-front `SnocList` (that gives only one end at a time), so the honest structural fold is the
  reconstruction `toList : SnocList Int Int → List Int`; the palindrome logic is a decision on the
  whole reconstructed list.  Feeding

    * `g x  := [x]`           (base: a one-element sequence), and
    * `st l q := l ++ [q]`    (step: append the new element at the back)

  to `snocFold_unique` PRODUCES `toList` as the catamorphism `cataR (scalarAlg g st)` — the recursion
  is never re-written (`toList_emerges`; its two hypotheses are `L125.toList`'s own defining equations,
  `rfl`).  The DERIVED program is `derivedSolve := cataR (scalarAlg g st) ≫ graph decideRev` (fold,
  then decide reverse-equality); `derivedSolve_eq_solve` identifies it with `L125.solve`.  Correctness
  is the DECISION shape `b = true ↔ P`, REUSED from `L125.solve_correct` — not re-proved.

  Mathlib-free.  Sorry-free.  Axioms of the headline `palin_derived_correct` ⊆ {propext, Quot.sound}
  (the constructive `snocFold_unique` route; no `cataR_eq_relCata`, hence no `Classical.choice`).
-/
import Fredy.A6_GenFold
import Fredy.L125

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC125D

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.SL Freyd.Alg.RelSet.LC125

/-! ## Base and step of the reconstruction fold

`g`/`st` are the base/step of the scalar algebra fed to `snocFold_unique`; `L125.toList` folds by
exactly these two equations, so the law's two hypotheses hold by `rfl`. -/

/-- Base: a one-element sequence. -/
def g (x : Int) : List Int := [x]

/-- Step: append the new element at the back (the `SnocList.snoc` order). -/
def st (l : List Int) (q : Int) : List Int := l ++ [q]

/-! ## The reconstruction fold EMERGES as the catamorphism -/

/-- **The fold is produced by the law.**  `L125.toList` — the sequence rebuilt as a plain `List Int`
    — IS the catamorphism of the scalar algebra `[g, st]`; the two hypotheses are `toList`'s own
    defining equations (`toList_wrap`/`toList_snoc`), so both are `rfl`.  The recursion is never
    written by hand here. -/
theorem toList_emerges :
    (graph toList : Arr ⟶ (⟨List Int⟩ : RelSet.{0})) = cataR (scalarAlg g st) :=
  SL.snocFold_unique g st toList (fun _ => rfl) (fun _ _ => rfl)

/-! ## The derived program: fold, then decide reverse-equality -/

/-- The palindrome decision on the reconstructed list: does it read the same reversed? -/
def decideRev (l : List Int) : Bool := decide (l = l.reverse)

/-- **The derived allegory program.**  Run the emergent reconstruction fold, then decide
    reverse-equality — a composite `Arr ⟶ dBool` in `Rel(Set)`, with the fold half PRODUCED by
    `snocFold_unique`, not hand-written. -/
def derivedSolve : Arr ⟶ dBool := cataR (scalarAlg g st) ≫ graph decideRev

/-- **The derived program is `L125.solve`.**  Rewriting the fold back to `toList` (`toList_emerges`)
    and composing the two graphs, `derivedSolve` is exactly `graph palinFn = L125.solve` — since
    `decideRev (toList xs)` is `palinFn xs` definitionally. -/
theorem derivedSolve_eq_solve : derivedSolve = LC125.solve := by
  show cataR (scalarAlg g st) ≫ graph decideRev = graph palinFn
  rw [← toList_emerges]
  apply hom_ext
  intro x z
  constructor
  · rintro ⟨y, hy, hz⟩
    subst hy
    exact hz
  · intro hz
    exact ⟨toList x, rfl, hz⟩

/-! ## Correctness — REUSED from `L125`, not re-proved -/

/-- **LeetCode 125, derived.**  The palindrome-decision program `derivedSolve` — whose fold half is
    PRODUCED by the fold law (`toList_emerges`) and whose answer is the reverse-equality decision —
    relates a sequence `xs` to `true` exactly when `xs` is a palindrome (`L125.IsPalin`).  The
    DECISION correctness shape `b = true ↔ P`, obtained by transporting `derivedSolve` to `L125.solve`
    (`derivedSolve_eq_solve`) and REUSING `L125.solve_correct` — the `iff` is not re-proved. -/
theorem palin_derived_correct (xs : SnocList Int Int) :
    derivedSolve xs true ↔ IsPalin xs := by
  rw [derivedSolve_eq_solve]
  show (true = palinFn xs) ↔ IsPalin xs
  constructor
  · intro h; exact (solve_correct xs).mp h.symm
  · intro h; exact ((solve_correct xs).mpr h).symm

/-! ## Running the derived program (same computations as `L125`)

  `cataR (scalarAlg g st)` is a relational catamorphism (its `snoc` case is an existential over the
  carrier), so it is not itself `decide`-computable; we `decide` the computable witness
  `decideRev (toList _)` — extensionally `derivedSolve`'s value on a graph point (`toList_emerges`),
  and `palinFn _` definitionally. -/

example : decideRev (toList (ofList 97 [98, 97])) = true := by decide      -- "aba"
example : decideRev (toList (ofList 97 [98])) = false := by decide         -- "ab"
example : decideRev (toList (ofList 97 [98, 98, 97])) = true := by decide  -- "abba"
example : decideRev (toList (ofList 1 [])) = true := by decide             -- single char

end Freyd.Alg.RelSet.LC125D
