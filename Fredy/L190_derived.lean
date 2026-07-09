/-
  LeetCode 190 — Reverse Bits — DERIVED as a cons-list catamorphism.

  `Fredy/L190.lean` packages the solution as `revBits := List.reverse` on the LSB-first bit-list,
  `solve : dBits ⟶ dBits := graph revBits` — a STRUCTURAL-OUTPUT endomorphism (source and target the
  same object `List Bool`, cf. `L206`).  Unlike `L226` (tree inversion, whose `solve_eq_cata` already
  exhibits it AS `cataR alg` — a wrapper we skip), `revBits` is Lean core's accumulator-based
  `List.reverse`, NOT written as a structural fold, so there is genuine content in making it EMERGE
  as a catamorphism.

  Bit-reversal is the textbook fold `reverse = foldr (fun x r => r ++ [x]) []`: reading the standard
  recurrence `reverse (x :: xs) = reverse xs ++ [x]` (`List.reverse_cons`) off the FRONT of the list,
  the leading bit `x` is snoc'd onto the reversed tail.  That is exactly a CONS-list catamorphism
  (`F X = 1 + Bool × X`, base at `wrap`/nil, recursion on the tail) with

    * base   `g _        = []`                      (the empty word reverses to itself), and
    * step   `st x prev  = prev ++ [x]`             (snoc the leading bit onto the folded tail),

  carrier `C := List Bool` — the SAME object as the input, the structural-output shape.  The input
  `List Bool` is not the initial-algebra list, so `revBits` as written is not a catamorphism; this
  file RESHAPES the data onto the repo's canonical cons-list initial algebra `ConsList Unit Bool`
  and lets the fold EMERGE via the general-carrier law `Freyd.Alg.RelSet.CL.consFold_unique`
  (`Fredy/A6_GenFold.lean`) — same recipe as `L1143_derived` (`ofList` + `consFold_unique` + a
  bridge to the raw-`List` program).  The SnocList axis would need a non-structural `ofList`
  (snoc at the innermost position); the cons axis is the structural, front-to-back one, matching the
  `reverse (x :: xs)` recurrence.

  Correctness is REUSED, not re-proved: the reshaped-then-converted fold reproduces `revBits`
  (`LC190.solve_correct` across the bridge `foldCL_ofList`), and reversing bits twice is the identity
  (`LC190.rev_rev`, `L190`'s structural extra law).

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.L190

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC190D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The cons-list carrier and its bit-reversal fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here `C = List Bool`,
  the SAME object as the input (the structural-output case).  `foldCL` mirrors bit-reversal on the
  cons-list initial algebra `ConsList Unit Bool`: `wrap _` is the empty word (`[]`), `cons x xs`
  reads the leading bit `x` and snoc's it onto the reversed tail. -/

/-- Bit-reversal as a fold over the cons-list initial algebra, mirroring `reverse (x :: xs) =
    reverse xs ++ [x]`: `wrap _ ↦ []`, `cons x xs ↦ foldCL xs ++ [x]`. -/
def foldCL : ConsList Unit Bool → List Bool
  | ConsList.wrap _    => []
  | ConsList.cons x xs => foldCL xs ++ [x]

/-- The base of the emergent algebra: the empty word reverses to itself, ignoring the `Unit` leaf. -/
def g : Unit → List Bool := fun _ => []

/-- The step of the emergent algebra: snoc the leading bit `x` onto the folded (reversed) tail. -/
def st : Bool → List Bool → List Bool := fun x prev => prev ++ [x]

/-- The base condition is a COMPUTATION, not a guess: `foldCL (wrap d) = g d`. -/
theorem foldCL_wrap : ∀ d : Unit, foldCL (ConsList.wrap d) = g d := fun d => rfl

/-- The step condition IS `foldCL`'s cons equation: `foldCL (cons x xs) = st x (foldCL xs)`. -/
theorem foldCL_cons : ∀ (x : Bool) (xs : ConsList Unit Bool),
    foldCL (ConsList.cons x xs) = st x (foldCL xs) := fun x xs => rfl

/-! ## Bit-reversal EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  Bit-reversal, RESHAPED onto the cons-list initial algebra `ConsList Unit
    Bool`, IS the catamorphism of the emergent scalar algebra `consScalarAlg g st` — it was never
    written as a fold: `graph foldCL` equals `cataR (consScalarAlg g st)`.  The program (the fold) is
    PRODUCED by `consFold_unique`; `List.reverse` (LeetCode 190's answer) is recovered below. -/
theorem revBits_emerges :
    (graph foldCL : dCL Unit Bool ⟶ ⟨List Bool⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st foldCL foldCL_wrap foldCL_cons

/-! ## Bridge to the hand-written `List.reverse` program -/

/-- The `List Bool → ConsList Unit Bool` conversion onto the initial algebra: `[] ↦ wrap ()`,
    `x :: xs ↦ cons x (ofList xs)`. -/
def ofList : List Bool → ConsList Unit Bool
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- The reshaped fold agrees with `LC190.revBits` (Lean core's `List.reverse`) on converted input,
    by induction on `xs` (`reverse (x :: xs) = reverse xs ++ [x]`). -/
theorem foldCL_ofList : ∀ bs : List Bool, foldCL (ofList bs) = LC190.revBits bs
  | []      => rfl
  | x :: xs => by
      show foldCL (ofList xs) ++ [x] = LC190.revBits (x :: xs)
      rw [foldCL_ofList xs]
      show xs.reverse ++ [x] = (x :: xs).reverse
      exact List.reverse_cons.symm

/-! ## Correctness carries over from `L190.lean` (no re-proof) -/

/-- **Headline.**  The honest bundle: (1) bit-reversal, reshaped onto the cons-list initial algebra,
    IS the catamorphism of `consScalarAlg g st` (`revBits_emerges`); (2) the reshaped-then-converted
    fold reproduces `LC190.revBits` — LeetCode 190's `List.reverse` program — the reused
    `LC190.solve_correct` carried across the bridge `foldCL_ofList`; and (3) reversing bits twice is
    the identity, the structural-output extra law reused from `LC190.rev_rev`.  The program (the
    fold) is PRODUCED by the law; correctness is REUSED, not re-proved. -/
theorem revBits_derived_correct :
    ((graph foldCL : dCL Unit Bool ⟶ ⟨List Bool⟩) = cataR (consScalarAlg g st))
      ∧ (∀ bs : List Bool, foldCL (ofList bs) = LC190.revBits bs)
      ∧ (∀ bs : List Bool, foldCL (ofList (foldCL (ofList bs))) = bs) := by
  refine ⟨revBits_emerges, foldCL_ofList, fun bs => ?_⟩
  rw [foldCL_ofList bs, foldCL_ofList (LC190.revBits bs)]
  exact LC190.rev_rev bs

/-! ## Running / cross-checking the reshaped fold

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier), so we `decide` the extensionally-equal computable witness
  `foldCL ∘ ofList` (equal to `revBits` by `foldCL_ofList`, and to the catamorphism by
  `revBits_emerges`) on the LeetCode 190 examples. -/

example : foldCL (ofList [true, false, false, false]) = [false, false, false, true] := by decide
example : foldCL (ofList ([] : List Bool)) = [] := by decide
example : foldCL (ofList [true]) = [true] := by decide
-- Reversing bits twice is the identity (the structural-output extra law), on the reshaped fold:
example : foldCL (ofList (foldCL (ofList [true, false, true]))) = [true, false, true] := by decide

/-- The reshaped fold genuinely relates the converted input to the catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg g st) (ofList [true, false, false, false])
      (foldCL (ofList [true, false, false, false])) := by
  have h : (graph foldCL : dCL Unit Bool ⟶ ⟨List Bool⟩)
      (ofList [true, false, false, false]) (foldCL (ofList [true, false, false, false])) := rfl
  rw [revBits_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC190D
