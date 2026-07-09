/-
  LeetCode 206 — Reverse Linked List — DERIVED as a cons-list catamorphism.

  `Fredy/L206.lean` packages the answer as `solve := graph revFn` with `revFn := List.reverse` over a
  RAW Lean `List Int` — Lean core's `List.reverse`, NOT the repo's initial-algebra list, so as written
  it is not a `cataR`.  This file RESHAPES the data onto the canonical cons-list initial algebra
  `ConsList Unit Int` (`list Int` of the book, base at `wrap ()`, recursion on the tail) and reads
  reversal off as an ordinary cons-fold with the carrier the list itself:

    * `C := List Int`  — the reversed-so-far list.

  The base/step are ordinary and FORCED (both `rfl`):

    * base   `g _      = []`                              = `revCL (wrap _)`
    * step   `st x acc = acc ++ [x]`  (snoc the head)     = `revCL (cons x xs)` with `acc = revCL xs`.

  A front-to-back cons-fold that SNOCs the head onto the folded tail reverses the list —
  `revCL (cons x xs) = revCL xs ++ [x]` is exactly `List.reverse_cons`.  Feeding `g`/`st`/`revCL` to
  the general-carrier law `Freyd.Alg.RelSet.CL.consFold_unique` (`Fredy/A6_GenFold.lean`) PRODUCES
  reversal as `cataR (consScalarAlg g st)` — the fold is emitted by the law, never written as a fold.
  The bridge `revCL_ofList` (`revCL (ofList xs) = LC206.revFn xs`) recovers the raw-`List` reversal.

  Only the DATA is reshaped; the structural laws (`revFn xs = xs.reverse`, involutivity `rev_rev`) are
  REUSED from `L206.lean`, not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.L206

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC206D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The cons-list carrier and its snocing fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here `C = List Int` — the
  reversed-so-far list.  A front-to-back cons-fold that appends the head AFTER the folded tail turns the
  list around. -/

/-- The base of the emergent algebra: the empty suffix reverses to the empty list. -/
def g : Unit → List Int := fun _ => []

/-- The step of the emergent algebra: snoc the head `x` onto the reversed tail `acc`. -/
def st : Int → List Int → List Int := fun x acc => acc ++ [x]

/-- Reversal as a fold over the cons-list initial algebra, mirroring `LC206.revFn`:
    `wrap _ ↦ []`, `cons x xs ↦ st x (revCL xs) = revCL xs ++ [x]`. -/
def revCL : ConsList Unit Int → List Int
  | ConsList.wrap _    => []
  | ConsList.cons x xs => st x (revCL xs)

/-- The base condition is a COMPUTATION, not a guess: `revCL (wrap d) = g d`. -/
theorem revCL_wrap : ∀ d : Unit, revCL (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition IS `revCL`'s cons equation: `revCL (cons x xs) = st x (revCL xs)`. -/
theorem revCL_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), revCL (ConsList.cons x xs) = st x (revCL xs) :=
  fun _ _ => rfl

/-! ## Reversal EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  Reversal, RESHAPED onto the cons-list initial algebra `ConsList Unit Int`, IS
    the catamorphism of the emergent scalar algebra `consScalarAlg g st` — it was never written as a
    fold: `graph revCL` equals `cataR (consScalarAlg g st)`.  Snocing the head onto the folded tail is
    the point: a list-reversing fold is emitted by `consFold_unique`. -/
theorem rev_emerges :
    (graph revCL : dCL Unit Int ⟶ ⟨List Int⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st revCL revCL_wrap revCL_cons

/-! ## Bridge to the hand-written raw-`List` solution -/

/-- The `List Int → ConsList Unit Int` conversion onto the initial algebra: `[] ↦ wrap ()`,
    `x :: xs ↦ cons x (ofList xs)`. -/
def ofList : List Int → ConsList Unit Int
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- The reshaped fold agrees with the raw-`List` reversal on converted input:
    `revCL (ofList xs) = LC206.revFn xs = xs.reverse`, by induction on `xs`, the cons step being
    exactly `List.reverse_cons` (`(x :: xs).reverse = xs.reverse ++ [x]`). -/
theorem revCL_ofList : ∀ xs : List Int, revCL (ofList xs) = LC206.revFn xs
  | []      => rfl
  | x :: xs => by
      show st x (revCL (ofList xs)) = (x :: xs).reverse
      rw [revCL_ofList xs]
      show xs.reverse ++ [x] = (x :: xs).reverse
      rw [List.reverse_cons]

/-! ## Correctness carries over from `L206.lean` (no re-proof) -/

/-- **Headline.**  The honest bundle for the STRUCTURAL-OUTPUT case:

    (1) reversal, reshaped onto the cons-list initial algebra, IS the catamorphism of
        `consScalarAlg g st` — the reversing fold EMERGES from `consFold_unique` (`rev_emerges`);
    (2) the `Map` `LC206.solve` (LeetCode 206's answer relation) relates each input to exactly the
        emergent catamorphism on the converted input (`revCL_ofList`); and
    (3) applying the reversal again returns the input — the REUSED involutivity `LC206.rev_rev`, not
        re-proved here.

    The program (the reversing fold) is PRODUCED by the law; the structural laws are reused. -/
theorem rev_derived_correct :
    ((graph revCL : dCL Unit Int ⟶ ⟨List Int⟩) = cataR (consScalarAlg g st))
      ∧ (∀ (xs ys : List Int), LC206.solve xs ys ↔ ys = revCL (ofList xs))
      ∧ (∀ xs : List Int, LC206.revFn (revCL (ofList xs)) = xs) := by
  refine ⟨rev_emerges, ?_, ?_⟩
  · intro xs ys
    show (ys = LC206.revFn xs) ↔ ys = revCL (ofList xs)
    rw [revCL_ofList xs]
  · intro xs
    rw [revCL_ofList xs]
    exact LC206.rev_rev xs

/-! ## Running / cross-checking the reshaped fold

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier), so we `decide` the extensionally-equal computable witness
  `revCL ∘ ofList` (LeetCode 206 examples). -/

/-- `[1,2,3] → [3,2,1]`. -/
example : revCL (ofList [1, 2, 3]) = [3, 2, 1] := by decide
/-- `[] → []`. -/
example : revCL (ofList []) = [] := by decide
/-- `[1] → [1]`. -/
example : revCL (ofList [1]) = [1] := by decide

/-- The reshaped fold genuinely relates the converted input to the catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg g st) (ofList [1, 2, 3]) (revCL (ofList [1, 2, 3])) := by
  have h : (graph revCL : dCL Unit Int ⟶ ⟨List Int⟩)
      (ofList [1, 2, 3]) (revCL (ofList [1, 2, 3])) := rfl
  rw [rev_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC206D
