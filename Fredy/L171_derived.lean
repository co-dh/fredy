/-
  LeetCode 171 — Excel Sheet Column Number — DERIVED as a base-26 Horner CATAMORPHISM.

  `Fredy/L171.lean` WRITES the program by hand as a raw `List.foldl`
  (`colNumberFn xs = xs.foldl (fun acc d => acc*26 + d) 0`, most-significant letter first) and
  verifies it against the honest positional value `LC171.value`.  This file makes that Horner fold
  EMERGE from the reusable general-carrier fold-uniqueness law `Freyd.Alg.RelSet.SL.snocFold_unique`
  (`Fredy/A6_GenFold.lean`), over the SNOC-LIST initial algebra with a single-accumulator carrier
  `C := Int` — the amount is combined at the BACK, so a left fold is exactly the snoc recursion
  `colNumberFn (snoc xs d) = colNumberFn xs * 26 + d`.

  Carrier `C = Int`, leaf `L = Unit`, element `E = Int`.  Its base `g` and step `st` are not
  guesses — they are `colNumberFn`'s own foldl equations:

    * base  `g () = 0`                           (empty numeral denotes 0)
    * step  `st acc d = acc * 26 + d`            (shift one base-26 place, add the new letter value)

  Feeding `g`/`st`/`foldSL` to `snocFold_unique` PRODUCES the Horner fold as `cataR (scalarAlg g st)`
  — never written by hand; it is the law's catamorphism (`colNumber_emerges`).  The raw-`List` input
  is a plain reshape: `ofList` reindexes a `List Int` onto the snoc-list initial algebra, and the
  raw program factors as `graph ofList ≫ derivedSolve` (`reshapes_solve`).  Correctness is REUSED
  from `L171.lean` (`LC171.colNumber_correct : colNumberFn = value`, the honest base-26 place value),
  not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.L171

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC171D

open Freyd Freyd.Alg.RelSet.SL

/-! ## The emergent algebra (base `g`, step `st`) and the Horner fold `foldSL`

  The carrier of `snocFold_unique` is a bare type `C`; here `C = Int` — the single Horner
  accumulator.  `g`/`st` are `colNumberFn`'s own foldl base/step, so `foldSL` (defined FROM them)
  satisfies the law's two hypotheses by `rfl`. -/

/-- Base: the empty base-26 numeral denotes `0`. -/
def g : Unit → Int := fun _ => 0

/-- Step: shift one base-26 place and add the new letter value — `colNumberFn`'s foldl step. -/
def st : Int → Int → Int := fun acc d => acc * 26 + d

/-- The base-26 Horner fold over the snoc-list initial algebra, defined FROM `g`/`st` so
    `snocFold_unique` applies: `foldSL (wrap _) = 0`, `foldSL (snoc xs d) = foldSL xs * 26 + d`. -/
def foldSL : SnocList Unit Int → Int
  | SnocList.wrap l => g l
  | SnocList.snoc xs d => st (foldSL xs) d

/-- The base condition is a COMPUTATION, not a guess: `foldSL (wrap l) = g l`. -/
theorem foldSL_wrap : ∀ l : Unit, foldSL (SnocList.wrap l) = g l := fun _ => rfl

/-- The step condition IS `foldSL`'s snoc equation: `foldSL (snoc xs d) = st (foldSL xs) d`. -/
theorem foldSL_snoc : ∀ (xs : SnocList Unit Int) (d : Int),
    foldSL (SnocList.snoc xs d) = st (foldSL xs) d := fun _ _ => rfl

/-- **The derivation.**  The base-26 Horner fold is PRODUCED by the general-carrier fold-uniqueness
    law — never written by hand: `graph foldSL` equals the catamorphism of the scalar algebra
    `scalarAlg g st`, carrier `Int` (the single Horner accumulator). -/
theorem colNumber_emerges :
    (graph foldSL : dSL Unit Int ⟶ ⟨Int⟩) = cataR (scalarAlg g st) :=
  SL.snocFold_unique g st foldSL foldSL_wrap foldSL_snoc

/-! ## Reshaping the raw-`List` input onto the snoc-list initial algebra

  `L171.lean`'s `colNumberFn` folds a plain `List Int`, which carries no `Rel(Set)` initial-algebra
  structure.  `ofList` reindexes it onto `SnocList Unit Int` (snoc = combine at the back), and the
  emergent Horner fold recovers `colNumberFn` on the nose (`foldSL_ofList`). -/

/-- Reindex a raw big-endian `List Int` onto the snoc-list initial algebra: each letter value is
    `snoc`-ed at the back, so the least-significant (last) letter is the outermost `snoc`. -/
def ofList (xs : List Int) : SnocList Unit Int := xs.foldl SnocList.snoc (SnocList.wrap ())

/-- The Horner fold over the reshaped snoc-list tracks the raw left fold, with any starting
    accumulator: both `foldl` the SAME step, so they agree once `foldSL` reads the seed. -/
theorem foldSL_foldl (xs : List Int) : ∀ sl : SnocList Unit Int,
    foldSL (xs.foldl SnocList.snoc sl) = xs.foldl (fun acc d => acc * 26 + d) (foldSL sl) := by
  induction xs with
  | nil => intro sl; rfl
  | cons d ds ih => intro sl; exact ih (SnocList.snoc sl d)

/-- **The bridge**: the emergent Horner fold on the reshaped input recovers the hand-written
    `colNumberFn` exactly. -/
theorem foldSL_ofList (xs : List Int) : foldSL (ofList xs) = LC171.colNumberFn xs := by
  show foldSL (xs.foldl SnocList.snoc (SnocList.wrap ())) = xs.foldl (fun acc d => acc * 26 + d) 0
  rw [foldSL_foldl xs (SnocList.wrap ())]
  rfl

/-! ## The derived program and its connection to `L171.lean`'s `solve` -/

/-- The derived allegory program: the law-produced base-26 Horner catamorphism, a morphism
    `dSL Unit Int ⟶ dNum` in `Rel(Set)`. -/
def derivedSolve : dSL Unit Int ⟶ LC171.dNum := cataR (scalarAlg g st)

/-- The derived program is a `Map`: it is the emergent catamorphism, equal to `graph foldSL`. -/
theorem derivedSolve_map : Map derivedSolve := by
  show Map (cataR (scalarAlg g st))
  rw [← colNumber_emerges]; exact graph_map foldSL

/-- **Connection to `solve`.**  The raw-`List` program `LC171.solve` factors as "reindex the input
    onto the snoc-list initial algebra (`graph ofList`), then run the emergent Horner catamorphism
    (`derivedSolve`)".  The recursion lives entirely in the law-produced `derivedSolve`. -/
theorem reshapes_solve :
    (graph ofList : LC171.dTitle ⟶ dSL Unit Int) ≫ derivedSolve = LC171.solve := by
  show graph ofList ≫ cataR (scalarAlg g st) = graph LC171.colNumberFn
  rw [← colNumber_emerges]
  apply hom_ext; intro xs v
  show (∃ sl, sl = ofList xs ∧ v = foldSL sl) ↔ v = LC171.colNumberFn xs
  constructor
  · rintro ⟨sl, hsl, hv⟩; rw [hsl, foldSL_ofList] at hv; exact hv
  · intro hv; exact ⟨ofList xs, rfl, by rw [hv, ← foldSL_ofList]⟩

/-! ## Correctness carries over from `L171.lean` (no re-proof of the place-value identity) -/

/-- **Headline.**  The law-derived Horner catamorphism computes the honest base-26 place value:
    `derivedSolve` relates the reshaped numeral `ofList xs` to `LC171.value xs`, the closed
    positional value `a·26^(n-1) + … + z`.  This BUNDLES the emergence (`colNumber_emerges`:
    `derivedSolve = cataR (scalarAlg g st)`) with the REUSED correctness (`LC171.colNumber_correct`:
    `colNumberFn = value`) — the place-value identity is not re-proved. -/
theorem colNumber_derived_correct (xs : List Int) :
    derivedSolve (ofList xs) (LC171.value xs) := by
  show cataR (scalarAlg g st) (ofList xs) (LC171.value xs)
  rw [← colNumber_emerges]
  show LC171.value xs = foldSL (ofList xs)
  rw [foldSL_ofList]
  exact (LC171.colNumber_correct xs).symm

/-! ## Running the emergent fold (`decide` on the computable Horner witness)

  The relational catamorphism `cataFold (scalarAlg g st)` is not `decide`-computable (its `snoc`
  case is an existential over `Int`), so we `decide` the extensionally-equal computable witness
  `foldSL ∘ ofList` (= `colNumberFn` by `foldSL_ofList`, = `derivedSolve ∘ ofList` by
  `colNumber_emerges`). -/

example : foldSL (ofList [1]) = 1 := by decide          -- "A"  = 1
example : foldSL (ofList [1, 1]) = 27 := by decide       -- "AA" = 27
example : foldSL (ofList [26, 26]) = 702 := by decide     -- "ZZ" = 702

end Freyd.Alg.RelSet.LC171D
