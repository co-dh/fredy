/-
  LeetCode 1 — Two Sum — DERIVED as a cons-list catamorphism.

  `Fredy/L1.lean` WRITES `twoSumFn nums target = go [] target nums` as a LEFT-TO-RIGHT scan over a raw
  Lean `List Int` carrying an ACCUMULATOR `seen : List (Int × Nat)` (the `(value, index)` pairs of the
  already-processed prefix, so the next element's index is `seen.length`):

    * base   `go seen target []       = none`
    * step   `go seen target (x :: r) = match findComplement (target - x) seen with`
                                         `| some i => some (i, seen.length)`
                                         `| none   => go ((x, seen.length) :: seen) target r`

  As written this is not a catamorphism for two reasons: its input `List Int` is not the repo's
  initial-algebra list, and — more essentially — it is an accumulator-passing LEFT fold with EARLY
  RETURN, whereas a plain cons-fold `st : E → C → C` (head, then folded tail) recurses on the tail
  first and has no left-accumulated `seen` to hand the step.

  This file RESHAPES the data onto the canonical cons-list initial algebra `ConsList Unit Int`
  (`list Int` of the book, base at `wrap ()`, recursion on the tail) and DEFEATS the left-accumulator
  by choosing the FUNCTION carrier

    * `C := List (Int × Nat) → Option (Nat × Nat)` — "given the seen-so-far, the answer" —

  the standard accumulator-as-function (CPS) reshaping: the folded tail is a CONTINUATION awaiting the
  `seen` that the (still-unprocessed) prefix will build.  The base/step are then ordinary and FORCED
  (both `rfl`):

    * base   `g _  = fun _ => none`                                = `foldCL target (wrap _)`
    * step   `st target x k = fun seen => match findComplement (target - x) seen with`
                              `| some i => some (i, seen.length) | none => k ((x, seen.length) :: seen)`
                                                                    = `foldCL target (cons x xs)` with
                                                                      `k = foldCL target xs`.

  The step `st target x` IS `go`'s cons equation with `seen` abstracted; the early return is the
  `some i` branch of the continuation.  Feeding `g`/`st target`/`foldCL target` to the general-carrier
  law `Freyd.Alg.RelSet.CL.consFold_unique` (`Fredy/A6_GenFold.lean`) PRODUCES the two-sum scan as
  `cataR (consScalarAlg g (st target))` — the accumulator-passing left scan is EMITTED by the law,
  never written by hand.  The bridge `foldCL_go` (`foldCL target (ofList xs) seen = go seen target xs`)
  recovers the hand-written raw-list scan, `seen` being exactly the accumulator the continuation awaits.

  Only the DATA is reshaped; the honest soundness+completeness (`LC1.twoSum_correct` — a `some` result
  is a genuine `TwoSum` hit, a `none` result rules out every valid pair) and the `Map` `LC1.solve` are
  REUSED from `L1.lean`, not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.L1

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC1D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The cons-list FUNCTION carrier and its accumulator-carrying fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here
  `C = List (Int × Nat) → Option (Nat × Nat)` — a CONTINUATION mapping the seen-so-far to the answer.
  Currying the left accumulator `seen` into the carrier is what lets an ordinary cons-fold (recursion
  on the tail) reproduce `go`'s left-to-right accumulator scan. -/

/-- The continuation carrier: given the `(value, index)` pairs seen so far, the optional answer pair. -/
abbrev Carrier : Type := List (Int × Nat) → Option (Nat × Nat)

/-- The base of the emergent algebra: the empty suffix yields no answer, whatever the seen prefix. -/
def g : Unit → Carrier := fun _ => fun _ => none

/-- The step of the emergent algebra: prepend symbol `x` to the folded-tail continuation `k`.  Given
    the seen-so-far `seen`, look the complement `target - x` up among earlier elements; a hit `some i`
    returns `some (i, seen.length)` (the EARLY RETURN), a miss hands the extended `seen` on to `k`. -/
def st (target : Int) : Int → Carrier → Carrier :=
  fun x k => fun seen =>
    match LC1.findComplement (target - x) seen with
    | some i => some (i, seen.length)
    | none   => k ((x, seen.length) :: seen)

/-- The two-sum scan as a fold over the cons-list initial algebra, mirroring `LC1.go`:
    `wrap _ ↦ (fun _ => none)`, `cons x xs ↦ st target x (foldCL target xs)`. -/
def foldCL (target : Int) : ConsList Unit Int → Carrier
  | ConsList.wrap _    => fun _ => none
  | ConsList.cons x xs => st target x (foldCL target xs)

/-- The base condition is a COMPUTATION, not a guess: `foldCL target (wrap d) = g d`. -/
theorem foldCL_wrap (target : Int) : ∀ d : Unit, foldCL target (ConsList.wrap d) = g d :=
  fun _ => rfl

/-- The step condition IS `foldCL`'s cons equation: `foldCL target (cons x xs) = st target x (…)`. -/
theorem foldCL_cons (target : Int) :
    ∀ (x : Int) (xs : ConsList Unit Int),
      foldCL target (ConsList.cons x xs) = st target x (foldCL target xs) :=
  fun _ _ => rfl

/-! ## The two-sum scan EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  For each `target`, the two-sum scan, RESHAPED onto the cons-list initial
    algebra `ConsList Unit Int`, IS the catamorphism of the emergent scalar algebra
    `consScalarAlg g (st target)` — it was never written as a fold: `graph (foldCL target)` equals
    `cataR (consScalarAlg g (st target))`.  Currying the left accumulator into the function carrier is
    the point: an accumulator-passing left scan with early return is emitted by `consFold_unique`. -/
theorem twoSum_emerges (target : Int) :
    (graph (foldCL target) : dCL Unit Int ⟶ ⟨Carrier⟩) = cataR (consScalarAlg g (st target)) :=
  consFold_unique g (st target) (foldCL target) (foldCL_wrap target) (foldCL_cons target)

/-! ## Bridge to the hand-written raw-`List` solution -/

/-- The `List Int → ConsList Unit Int` conversion onto the initial algebra: `[] ↦ wrap ()`,
    `x :: xs ↦ cons x (ofList xs)`. -/
def ofList : List Int → ConsList Unit Int
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- The reshaped continuation fold agrees with the raw-`List` scan on converted input, for EVERY seen
    accumulator: `foldCL target (ofList xs) seen = go seen target xs`.  The continuation applied to
    `seen` is exactly `go`'s scan started with that accumulator; the induction on `xs` (generalizing
    `seen`) threads the accumulator the same way `go` does. -/
theorem foldCL_go (target : Int) :
    ∀ (xs : List Int) (seen : List (Int × Nat)),
      foldCL target (ofList xs) seen = LC1.go seen target xs
  | [],      seen => rfl
  | x :: xs, seen => by
      show st target x (foldCL target (ofList xs)) seen = LC1.go seen target (x :: xs)
      simp only [st, LC1.go]
      cases LC1.findComplement (target - x) seen with
      | none   => exact foldCL_go target xs ((x, seen.length) :: seen)
      | some i => rfl

/-- The reshaped catamorphism, run at the empty accumulator, computes exactly `twoSumFn`. -/
theorem twoSum_via (nums : List Int) (target : Int) :
    LC1.twoSumFn nums target = foldCL target (ofList nums) [] :=
  (foldCL_go target nums []).symm

/-! ## Correctness carries over from `L1.lean` (no re-proof of soundness/completeness) -/

/-- **Headline.**  The honest bundle:

    (1) for each `target` the two-sum scan, reshaped onto the cons-list initial algebra, IS the
        catamorphism of `consScalarAlg g (st target)` — the accumulator-passing left scan with early
        return EMERGES from `consFold_unique` (`twoSum_emerges`);
    (2) the `Map` `LC1.solve` (LeetCode 1's answer relation) relates each input `(nums, target)` to
        exactly that emergent catamorphism run at the empty accumulator (`twoSum_via`); and
    (3) that answer is honestly SOUND and COMPLETE against the `TwoSum` spec — a `some (i, j)` is a
        genuine valid pair, a `none` rules out every valid pair — the REUSED `LC1.twoSum_correct`, not
        re-proved here.

    The program (the fold) is PRODUCED by the law; soundness/completeness is reused. -/
theorem twoSum_derived_correct :
    (∀ target : Int,
        (graph (foldCL target) : dCL Unit Int ⟶ ⟨Carrier⟩) = cataR (consScalarAlg g (st target)))
      ∧ (∀ (p : List Int × Int) (a : Option (Nat × Nat)),
            LC1.solve p a ↔ a = foldCL p.2 (ofList p.1) [])
      ∧ (∀ (nums : List Int) (target : Int),
            (∀ i j, foldCL target (ofList nums) [] = some (i, j) → LC1.TwoSum nums target i j) ∧
            (foldCL target (ofList nums) [] = none → ∀ i j, ¬ LC1.TwoSum nums target i j)) := by
  refine ⟨twoSum_emerges, ?_, ?_⟩
  · intro p a
    show (a = LC1.twoSumFn p.1 p.2) ↔ a = foldCL p.2 (ofList p.1) []
    rw [twoSum_via p.1 p.2]
  · intro nums target
    rw [← twoSum_via nums target]
    exact LC1.twoSum_correct nums target

/-! ## Running / cross-checking the reshaped fold

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier), so we `decide` the computable scalar answers `twoSumFn`
  (LeetCode 1 examples) and the extensionally-equal computable witness `foldCL target (ofList …) []`
  (the continuation carrier applied to the empty accumulator is an `Option`, hence decidable). -/

/-- `[2,7,11,15], 9 → (0,1)`. -/
example : LC1.twoSumFn [2, 7, 11, 15] 9 = some (0, 1) := by decide
/-- `[3,2,4], 6 → (1,2)`. -/
example : LC1.twoSumFn [3, 2, 4] 6 = some (1, 2) := by decide
/-- `[1,2,3], 100 → none` (no valid pair). -/
example : LC1.twoSumFn [1, 2, 3] 100 = none := by decide

-- The reshaped continuation fold, on converted input at the empty accumulator, reproduces them:
example : foldCL 9 (ofList [2, 7, 11, 15]) [] = some (0, 1) := by decide
example : foldCL 6 (ofList [3, 2, 4]) [] = some (1, 2) := by decide
example : foldCL 100 (ofList [1, 2, 3]) [] = none := by decide

/-- The reshaped fold genuinely relates the converted input to the catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg g (st 9)) (ofList [2, 7, 11, 15]) (foldCL 9 (ofList [2, 7, 11, 15])) := by
  have h : (graph (foldCL 9) : dCL Unit Int ⟶ ⟨Carrier⟩)
      (ofList [2, 7, 11, 15]) (foldCL 9 (ofList [2, 7, 11, 15])) := rfl
  rw [twoSum_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC1D
