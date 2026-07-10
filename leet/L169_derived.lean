/-
  LeetCode 169 — Majority Element (Boyer–Moore voting) — DERIVED from the general-carrier fold law.

  `leet/L169.lean` WRITES the voting fold by hand as a raw `List.foldl`:
  `majorityFn nums := (nums.foldl step (0,0)).1`, state `(cand, cnt) : Int × Nat`, and proves it
  correct by the Boyer–Moore invariant (`BMInv`, `step_inv`, `foldl_inv`, `majority_correct`).  A raw
  `List.foldl` is not a `cataR` as written (raw `List` carries no `Rel(Set)` initial-algebra
  machinery here), so — following the reshaping recipe (`AOP/A6_GenFold.lean`, as in
  `L300_derived`/`L322_derived`) — we mirror the SAME single-pass fold as a `SnocList Unit Int`
  fold `foldSL` and let it EMERGE from the reusable general-carrier law
  `Freyd.Alg.RelSet.SL.snocFold_unique`.

  The creative choice is the CARRIER `Int × Nat` — the running `(candidate, count)` pair (Boyer–Moore's
  whole idea: one candidate, one cancelling counter).  Its base `g` and step `st` are then FORCED —
  they are `foldSL`'s own defining equations (both hold by `rfl`), and `st` is `LC169.step` verbatim:

    * base   `g () = (0, 0)`                 = `foldSL (wrap ())`
    * step   `st (c,k) x = LC169.step (c,k) x` = `foldSL (snoc xs x)` with `(c,k) = foldSL xs`.

  Feeding `g`/`st`/`foldSL` to `snocFold_unique` PRODUCES the voting fold as `cataR (scalarAlg g st)`
  — we never write the recursion; it is the law's catamorphism.  `ofList` coerces a raw Lean list to
  the snoc-list initial algebra, and `foldSL_ofList` bridges the emergent fold back to the exact
  accumulator `majorityFn` runs (`foldSL (ofList xs) = xs.foldl LC169.step (0,0)`), so the derived
  program `derivedSolve` equals the hand-written `LC169.solve`.  The Boyer–Moore correctness
  (`LC169.majority_correct`: a strict majority pins the fold's final candidate) is REUSED unchanged —
  not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound} (the reshaping is `List` structural induction
  only, no `Classical.choice`).
-/
import AOP.A6_GenFold
import leet.L169

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC169D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The Boyer–Moore ANSATZ and its FORCED base/step

  The carrier of `snocFold_unique` is a bare type `C`; here `C = Int × Nat` — the running
  `(candidate, count)` pair.  The base `g` and step `st` are not guesses: `st` IS `LC169.step`, and
  both conditions hold by `rfl`. -/

/-- The base of the emergent algebra: an empty candidacy `(0, 0)`. -/
def g : Unit → Int × Nat := fun _ => (0, 0)

/-- The step of the emergent algebra — Boyer–Moore's one vote, verbatim `LC169.step`. -/
def st : Int × Nat → Int → Int × Nat := LC169.step

/-- The voting fold on the snoc-list initial algebra, mirroring `LC169.majorityFn`'s `List.foldl`. -/
def foldSL : SnocList Unit Int → Int × Nat
  | SnocList.wrap _      => (0, 0)
  | SnocList.snoc xs x => LC169.step (foldSL xs) x

/-- The base condition is a COMPUTATION, not a guess: `foldSL (wrap ()) = g ()`. -/
theorem foldSL_wrap : ∀ l : Unit, foldSL (SnocList.wrap l) = g l := fun _ => rfl

/-- The step condition IS `foldSL`'s snoc equation: `foldSL (snoc xs x) = st (foldSL xs) x`. -/
theorem foldSL_snoc : ∀ (xs : SnocList Unit Int) (x : Int),
    foldSL (SnocList.snoc xs x) = st (foldSL xs) x := fun _ _ => rfl

/-! ## The voting fold EMERGES via the general-carrier law -/

/-- **The derivation.**  The Boyer–Moore voting fold is PRODUCED by `snocFold_unique` from the base
    `g` and step `st` — it was never written recursively: `graph foldSL` equals the catamorphism of
    the emergent scalar algebra `scalarAlg g st`. -/
theorem majority_emerges :
    (graph foldSL : dSL Unit Int ⟶ ⟨Int × Nat⟩) = cataR (scalarAlg g st) :=
  SL.snocFold_unique g st foldSL foldSL_wrap foldSL_snoc

/-! ## Reshaping bridge: raw Lean `List Int` ↦ the snoc-list initial algebra -/

/-- Coerce a raw Lean list into the snoc-list initial algebra, in index order. -/
def ofList (xs : List Int) : SnocList Unit Int := xs.foldl SnocList.snoc (SnocList.wrap ())

/-- The emergent fold on `ofList` agrees, at ANY starting state, with `LC169.step`'s `List.foldl` —
    a plain structural induction on the raw list (generalized over the starting snoc-list). -/
theorem foldSL_foldl (rest : List Int) : ∀ sl : SnocList Unit Int,
    foldSL (rest.foldl SnocList.snoc sl) = rest.foldl LC169.step (foldSL sl) := by
  induction rest with
  | nil => intro sl; rfl
  | cons r rs ih =>
      intro sl
      show foldSL (rs.foldl SnocList.snoc (SnocList.snoc sl r))
          = rs.foldl LC169.step (LC169.step (foldSL sl) r)
      rw [ih (SnocList.snoc sl r)]; rfl

/-- The emergent fold, run on the coerced list, is exactly the accumulator `majorityFn` computes. -/
theorem foldSL_ofList (xs : List Int) : foldSL (ofList xs) = xs.foldl LC169.step (0, 0) := by
  show foldSL (xs.foldl SnocList.snoc (SnocList.wrap ())) = xs.foldl LC169.step (0, 0)
  rw [foldSL_foldl xs (SnocList.wrap ())]; rfl

/-! ## The derived allegory program equals `LC169.solve` -/

/-- The derived program: coerce to the initial algebra, run the emergent voting fold, take the
    candidate (first projection). -/
def derivedSolve : LC169.Nums ⟶ LC169.dZ :=
  graph ofList ≫ cataR (scalarAlg g st) ≫ graph (fun s : Int × Nat => s.1)

/-- The derived program equals the hand-written `LC169.solve`: the reshaping + emergent fold + first
    projection recover exactly `majorityFn`. -/
theorem derivedSolve_eq_solve : derivedSolve = LC169.solve := by
  show (graph ofList ≫ cataR (scalarAlg g st) ≫ graph (fun s : Int × Nat => s.1)) = LC169.solve
  rw [← majority_emerges]
  apply hom_ext; intro xs v
  constructor
  · rintro ⟨sl, hsl, s, hs, hv⟩
    show v = LC169.majorityFn xs
    rw [hv, hs, hsl]
    show (foldSL (ofList xs)).1 = LC169.majorityFn xs
    rw [foldSL_ofList]
    rfl
  · intro hv
    refine ⟨ofList xs, rfl, foldSL (ofList xs), rfl, ?_⟩
    show v = (foldSL (ofList xs)).1
    rw [foldSL_ofList]
    exact hv

/-! ## Correctness carries over from `L169.lean` (the Boyer–Moore invariant is NOT re-proved) -/

/-- **Headline.**  The law-derived voting fold computes the strict majority element whenever one
    exists: if `v` occurs strictly more than half the time in `nums`, the derived program relates
    `nums` to `v`.  The Boyer–Moore invariant is REUSED from `LC169.majority_correct` (via
    `derivedSolve_eq_solve`), not re-proved. -/
theorem majority_derived_correct (nums : List Int) (v : Int) (hv : LC169.IsMajority nums v) :
    derivedSolve nums v := by
  rw [derivedSolve_eq_solve]
  show v = LC169.majorityFn nums
  exact (LC169.majority_correct nums v hv).symm

/-! ## Running / cross-checking the emergent fold against `leet/L169.lean`

  As in `L300_derived`, the relational catamorphism `cataFold (scalarAlg …)` is not
  `decide`-computable (its `snoc` case is an existential over the carrier), so we `decide` the
  extensionally-equal computable witness `LC169.majorityFn` (equal to the emergent fold by
  `derivedSolve_eq_solve`). -/

example : LC169.majorityFn [3, 2, 3] = 3 := by decide
example : LC169.majorityFn [2, 2, 1, 1, 1, 2, 2] = 2 := by decide
example : LC169.majorityFn [6, 5, 5] = 5 := by decide

/-- The emergent fold genuinely relates `[2,2,1,1,1,2,2]` to `foldSL (ofList …)` (whose `.1` is 2). -/
example :
    cataFold (scalarAlg g st) (ofList [2, 2, 1, 1, 1, 2, 2]) (foldSL (ofList [2, 2, 1, 1, 1, 2, 2])) := by
  have h : (graph foldSL : dSL Unit Int ⟶ ⟨Int × Nat⟩)
      (ofList [2, 2, 1, 1, 1, 2, 2]) (foldSL (ofList [2, 2, 1, 1, 1, 2, 2])) := rfl
  rw [majority_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC169D
