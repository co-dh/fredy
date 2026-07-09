/-
  LeetCode 128 — Longest Consecutive Sequence — DERIVED as a snoc-list catamorphism.

  `Fredy/L128.lean` computes the answer as `longestConsecFn nums = scanFn (isort nums)`: sort with
  `L242`'s insertion sort, then a LEFT-TO-RIGHT run-tracking scan (`scanAux`, a `foldl` over the
  sorted list threading the state `(prev, runLen, best)`).  That scan is written by hand over a RAW
  `List Int`, so as written it is not a catamorphism (raw `List` has no `Rel(Set)` initial-algebra
  machinery here).  This file RESHAPES it onto the snoc-list initial algebra and makes the fold
  EMERGE from the general-carrier law `Freyd.Alg.RelSet.SL.snocFold_unique` (`Fredy/A6_GenFold.lean`).

  Reshaping (the recipe of the `aop` skill):
  * A left-to-right `foldl` is a BACK-TO-FRONT snoc-fold: `snoc` adds the rightmost element, and
    `foldSL (snoc xs e) = stepOpt (foldSL xs) e` combines the accumulated state with the new element
    — exactly `foldl`.  So the axis is `SnocList Unit Int` and the carrier is a DIRECT value carrier
    `Option (Int × Nat × Nat)` (no function-carrier trick needed).
  * The `Option` carries the "no element seen yet" state, folding `scanFn`'s first-element SEED
    (`scanFn (c :: t) = (scanAux t (c,1,1)).2.2`) INTO the fold: `stepOpt none c = some (c,1,1)`.
  * base `g () = none`;  step `stepOpt` = `scanAux`'s inner step lifted through `Option`.

  Feeding `g`/`stepOpt`/`foldSL` to `snocFold_unique` PRODUCES the scan as `cataR (scalarAlg g stepOpt)`
  — the recursion is never re-written.  A bridge (`extract_foldSL_eq_scanFn`) shows the emergent fold,
  read out and pre-composed with `isort`, equals `L128`'s `scanFn`/`longestConsecFn`, so the derived
  program `derivedSolve` equals `LC128.solve`.  Correctness — the refinement + domination pair (an
  achievable value-run of the answer's length, dominating every value-run present in `nums`) — is
  REUSED verbatim from `LC128.longestConsec_correct`, not re-proved (this is an optimization problem:
  `solve` is the extremum selector, not the full achievability relation).

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.Deriv1
import Fredy.L128

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC128D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The emergent algebra: base `g`, step `stepOpt`, and the fold `foldSL` defined FROM them

  The carrier of `snocFold_unique` is a bare type `C`; here `C = Option (Int × Nat × Nat)` — the
  running scan state `(prev, runLen, best)`, or `none` before any element is seen.  `g`/`stepOpt`
  are the base/step of the scalar algebra; `foldSL` is defined FROM them so `snocFold_unique`'s two
  hypotheses hold by `rfl`. -/

/-- Base: the empty snoc-list folds to the "no element seen" state. -/
def g : Unit → Option (Int × Nat × Nat) := fun _ => none

/-- Step: on the next (rightmost) element `c`, seed the state if none yet; otherwise run `scanAux`'s
    inner step — dedup (`c = prev`), extend (`c = prev + 1`), or reset a fresh run of length 1. -/
def stepOpt : Option (Int × Nat × Nat) → Int → Option (Int × Nat × Nat)
  | none, c => some (c, 1, 1)
  | some (prev, runLen, best), c =>
      if c = prev then some (prev, runLen, best)
      else if c = prev + 1 then some (c, runLen + 1, LC128.nmax best (runLen + 1))
      else some (c, 1, LC128.nmax best 1)

/-- The scan as a snoc-list fold, defined FROM `g`/`stepOpt` so `snocFold_unique` applies. -/
def foldSL : SnocList Unit Int → Option (Int × Nat × Nat)
  | SnocList.wrap l => g l
  | SnocList.snoc xs e => stepOpt (foldSL xs) e

/-- **The derivation.**  The run-tracking scan is PRODUCED by the general-carrier fold-uniqueness
    law — never re-written: `graph foldSL` equals the catamorphism of the scalar algebra
    `scalarAlg g stepOpt`, carrier `Option (Int × Nat × Nat)`. -/
theorem emerges :
    (graph foldSL : dSL Unit Int ⟶ ⟨Option (Int × Nat × Nat)⟩) = cataR (scalarAlg g stepOpt) :=
  SL.snocFold_unique g stepOpt foldSL (fun _ => rfl) (fun _ _ => rfl)

/-! ## Reading out the answer, and the raw-`List` → snoc-list bridge -/

/-- Read the running best off the final state (`0` if the list was empty). -/
def extract : Option (Int × Nat × Nat) → Nat
  | none => 0
  | some s => s.2.2

/-- Build the snoc-list of a raw list, first element innermost (matching `foldl` order). -/
def ofSnocList (l : List Int) : SnocList Unit Int :=
  l.foldl SnocList.snoc (SnocList.wrap () : SnocList Unit Int)

/-- Folding `foldSL` over `ofSnocList` is a `foldl` of the step `stepOpt` — `foldSL` commutes with
    building the snoc-list from the left. -/
theorem foldl_snoc_foldSL (l : List Int) : ∀ acc : SnocList Unit Int,
    foldSL (l.foldl SnocList.snoc acc) = l.foldl stepOpt (foldSL acc) := by
  induction l with
  | nil => intro acc; rfl
  | cons c t ih =>
    intro acc
    calc foldSL (t.foldl SnocList.snoc (SnocList.snoc acc c))
        = t.foldl stepOpt (foldSL (SnocList.snoc acc c)) := ih (SnocList.snoc acc c)
      _ = t.foldl stepOpt (stepOpt (foldSL acc) c) := rfl

/-- The `Option`-lifted `foldl` of `stepOpt` from a `some` seed reproduces `L128`'s `scanAux`. -/
theorem foldl_stepOpt_some : ∀ (t : List Int) (st : Int × Nat × Nat),
    t.foldl stepOpt (some st) = some (LC128.scanAux t st) := by
  intro t
  induction t with
  | nil => intro st; rfl
  | cons d t' ih =>
    intro st
    obtain ⟨prev, runLen, best⟩ := st
    show t'.foldl stepOpt (stepOpt (some (prev, runLen, best)) d)
        = some (LC128.scanAux (d :: t') (prev, runLen, best))
    by_cases h1 : d = prev
    · simp only [stepOpt, LC128.scanAux, if_pos h1]
      exact ih (prev, runLen, best)
    · by_cases h2 : d = prev + 1
      · simp only [stepOpt, LC128.scanAux, if_neg h1, if_pos h2]
        exact ih (d, runLen + 1, LC128.nmax best (runLen + 1))
      · simp only [stepOpt, LC128.scanAux, if_neg h1, if_neg h2]
        exact ih (d, 1, LC128.nmax best 1)

/-- **The bridge.**  Reading out the emergent snoc-fold over the reshaped list equals `L128`'s
    hand-written scan `scanFn`. -/
theorem extract_foldSL_eq_scanFn (l : List Int) :
    extract (foldSL (ofSnocList l)) = LC128.scanFn l := by
  have h1 : foldSL (ofSnocList l) = l.foldl stepOpt none :=
    foldl_snoc_foldSL l (SnocList.wrap () : SnocList Unit Int)
  rw [h1]
  cases l with
  | nil => rfl
  | cons c t =>
    show extract (t.foldl stepOpt (some (c, 1, 1))) = (LC128.scanAux t (c, 1, 1)).2.2
    rw [foldl_stepOpt_some]; rfl

/-! ## The derived allegory program -/

/-- The preprocessing map `nums ↦ ofSnocList (isort nums)` — sort (reused from `L242`), then reshape
    onto the snoc-list initial algebra. -/
def pre (nums : List Int) : SnocList Unit Int := ofSnocList (LC242.isort nums)

/-- **The derived program**: reshape, run the emergent catamorphism, read out the answer. -/
def derivedSolve : LC128.NumList ⟶ LC128.dNat :=
  graph pre ≫ cataR (scalarAlg g stepOpt) ≫ graph extract

/-- Reading out the derived program pointwise equals `L128`'s `longestConsecFn`. -/
theorem derived_eq_longestConsec (nums : List Int) :
    extract (foldSL (pre nums)) = LC128.longestConsecFn nums := by
  show extract (foldSL (ofSnocList (LC242.isort nums))) = LC128.longestConsecFn nums
  rw [extract_foldSL_eq_scanFn]; rfl

/-- **The derived program equals the hand-written `LC128.solve`.**  Rewriting the emergent
    catamorphism back to `graph foldSL` (via `emerges`) and unfolding the graph composition, the
    derived program relates `nums` to exactly `longestConsecFn nums`. -/
theorem derivedSolve_eq_solve : derivedSolve = LC128.solve := by
  show (graph pre ≫ cataR (scalarAlg g stepOpt) ≫ graph extract) = LC128.solve
  rw [← emerges, Deriv.graph_comp, Deriv.graph_comp]
  show graph (fun nums => extract (foldSL (pre nums))) = LC128.solve
  apply hom_ext; intro nums L
  show (L = extract (foldSL (pre nums))) ↔ (L = LC128.longestConsecFn nums)
  rw [derived_eq_longestConsec]

/-! ## Correctness carries over from `L128.lean` (no re-proof of the optimization argument) -/

/-- **Headline.**  The law-derived program computes the Longest-Consecutive-Sequence optimum:
    `derivedSolve` relates each `nums` to a value `m` that is an achievable value-run length
    (some `s` with `s, s+1, …, s+m-1` all in `nums`) and dominates every value-run present in `nums`.
    The optimization argument is REUSED from `LC128.longestConsec_correct` (via `derivedSolve_eq_solve`),
    not re-proved. -/
theorem longestConsec_derived_correct (nums : List Int) :
    ∃ m, derivedSolve nums m ∧
      (∃ s : Int, ∀ i : Nat, i < m → s + (i : Int) ∈ nums) ∧
      (∀ (s : Int) (Lrun : Nat), (∀ i : Nat, i < Lrun → s + (i : Int) ∈ nums) → Lrun ≤ m) := by
  refine ⟨LC128.longestConsecFn nums, ?_,
    (LC128.longestConsec_correct nums).1, (LC128.longestConsec_correct nums).2⟩
  rw [derivedSolve_eq_solve]
  exact rfl

/-! ## Running / cross-checking the emergent fold against `Fredy/L128.lean`

  The relational catamorphism `cataFold (scalarAlg …)` is not `decide`-computable (its `snoc` case
  is an existential over the carrier), so we `decide` the computable witness
  `extract (foldSL (ofSnocList (isort …)))` — extensionally the derived answer
  (`derived_eq_longestConsec`) — and separately PROVE the emergent fold relates a concrete input. -/

-- The derived answer `decide`s on the computable witness (LeetCode 128 examples):
example : extract (foldSL (ofSnocList (LC242.isort [100, 4, 200, 1, 3, 2]))) = 4 := by decide
example : extract (foldSL (ofSnocList (LC242.isort [1, 2, 2, 3]))) = 3 := by decide
example : extract (foldSL (ofSnocList (LC242.isort ([] : List Int)))) = 0 := by decide

/-- The emergent catamorphism genuinely relates the reshaped array `[100,4,200,1,3,2]` (sorted) to
    `foldSL` of it (whose `extract` is 4). -/
example :
    cataFold (scalarAlg g stepOpt) (ofSnocList (LC242.isort [100, 4, 200, 1, 3, 2]))
      (foldSL (ofSnocList (LC242.isort [100, 4, 200, 1, 3, 2]))) := by
  have h : (graph foldSL : dSL Unit Int ⟶ ⟨Option (Int × Nat × Nat)⟩)
      (ofSnocList (LC242.isort [100, 4, 200, 1, 3, 2]))
      (foldSL (ofSnocList (LC242.isort [100, 4, 200, 1, 3, 2]))) := rfl
  rw [emerges] at h
  exact h

end Freyd.Alg.RelSet.LC128D
