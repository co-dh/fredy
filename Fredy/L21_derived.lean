/-
  LeetCode 21 — Merge Two Sorted Lists — DERIVED as a cons-list catamorphism (function carrier).

  `Fredy/L21.lean` writes `mergeFn` as a FUEL-indexed helper that recurses on BOTH lists at once —
  each step peels the smaller head off ONE of the two lists.  A merge is a two-input recursion, so a
  plain single-list value fold cannot express it.  The unlock (Skill AOP, "function carrier") is the
  HIGHER-ORDER fold: fold the FIRST list into a RESIDUAL function `List Int → List Int` that still
  awaits the second list.  Carrier `C := List Int → List Int`; the fold over the first list emits a
  merge-with-the-first-list-baked-in continuation.

  Reading the merge recurrence (`mergeFn_nil_left`, `mergeFn_nil_right`, `mergeFn_cons_eq`) as a fold
  over the first list gives:

    * base   `merge []        = fun ys => ys`                          (the identity residual)
    * step   `merge (x :: xs) = insert x (merge xs)`                   with

    `insert x rec []        = x :: rec []`
    `insert x rec (y :: ys) = if x ≤ y then x :: rec (y :: ys) else y :: insert x rec ys`.

  `insert x rec` is itself an ordinary structural recursion on the SECOND list — that inner recursion
  is exactly what a value fold cannot carry, and what the function carrier carries for free.  The
  else branch `y :: insert x rec ys` keeps the first list (via `rec` = `merge xs`) but decreases the
  second — impossible to phrase as `rec` alone, which is precisely why the carrier must be a function.

  This file RESHAPES the first list onto the repo's canonical cons-list initial algebra
  `ConsList Unit Int` (`ofList`), mirrors the fold as `foldCL`, and makes it EMERGE as a catamorphism
  via the general-carrier law `CL.consFold_unique` (`Fredy/A6_GenFold.lean`).  Only the DATA is
  reshaped; `mergeFn`, `spec`, and correctness (`solve_le_spec`, hence `merge_correct`) are REUSED
  from `LC21`, not re-proved.  The bridge `foldCL_ofList` recovers the hand-written program, giving
  `derivedSolve = LC21.solve` and thus `derivedSolve ⊑ spec`.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.L21

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC21D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The function carrier `List Int → List Int` and its merge fold

  `CL.consFold_unique` carries an arbitrary type `C`; here `C = List Int → List Int`, a RESIDUAL
  merge awaiting the second list.  `foldCL` folds the first list front-to-back into this residual:
  `wrap _` is the empty first list (the identity residual `fun ys => ys`), and `cons x xs` prepends
  the leading element `x` by `insert`ing it into the residual `foldCL xs = merge xs`. -/

/-- Insert the head `x` of the first list into the merge, given the residual `rec = merge xs`.  A
    structural recursion on the SECOND list `ys` — the inner recursion the function carrier carries.
    Read directly off `mergeFn`'s recurrence: nil-second returns `x :: rec []`; cons-second compares
    heads and either emits `x` (continuing with `rec`) or emits the second head `y` and recurses. -/
def insert (x : Int) (rec : List Int → List Int) : List Int → List Int
  | []      => x :: rec []
  | y :: ys => if x ≤ y then x :: rec (y :: ys) else y :: insert x rec ys

/-- The merge as a fold over the cons-list initial algebra, carrier `List Int → List Int`:
    `wrap _ ↦ fun ys => ys` (identity residual), `cons x xs ↦ insert x (foldCL xs)`. -/
def foldCL : ConsList Unit Int → (List Int → List Int)
  | ConsList.wrap _    => fun ys => ys
  | ConsList.cons x xs => insert x (foldCL xs)

/-- The base of the emergent algebra: the identity residual (`merge [] ys = ys`), ignoring the
    `Unit` leaf. -/
def g : Unit → (List Int → List Int) := fun _ => fun ys => ys

/-- The step of the emergent algebra: prepend the leading element `x` to the folded-tail residual
    `rec = merge xs` by `insert`ing it. -/
def st : Int → (List Int → List Int) → (List Int → List Int) := fun x rec => insert x rec

/-- The base condition is a COMPUTATION, not a guess: `foldCL (wrap d) = g d` (both `fun ys => ys`). -/
theorem foldCL_wrap : ∀ d : Unit, foldCL (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition IS `foldCL`'s cons equation: `foldCL (cons x xs) = st x (foldCL xs)`. -/
theorem foldCL_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), foldCL (ConsList.cons x xs) = st x (foldCL xs) :=
  fun _ _ => rfl

/-! ## The merge fold EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  The merge, reshaped onto the cons-list initial algebra `ConsList Unit Int`,
    IS the catamorphism of the emergent scalar algebra `consScalarAlg g st` — it was never written
    as a fold: `graph foldCL` equals `cataR (consScalarAlg g st)`.  The FUNCTION carrier
    `List Int → List Int` (a residual merge awaiting the second list) is the point: a two-input merge
    is emitted by the single-list `consFold_unique`. -/
theorem merge_emerges :
    (graph foldCL : dCL Unit Int ⟶ ⟨List Int → List Int⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st foldCL foldCL_wrap foldCL_cons

/-! ## Bridge to the hand-written raw-`List` program `mergeFn` -/

/-- The `List Int → ConsList Unit Int` conversion onto the initial algebra: `[] ↦ wrap ()`,
    `x :: xs ↦ cons x (ofList xs)`. -/
def ofList : List Int → ConsList Unit Int
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- `insert` applied to the exact residual `rec = merge xs` reproduces `mergeFn (x :: xs)`, by
    induction on the SECOND list.  This is the crux: the else branch keeps the first list (`rec`)
    while decreasing the second, which the function carrier tracks. -/
theorem insert_eq (x : Int) (rec : List Int → List Int) (xs : List Int)
    (hrec : ∀ zs, rec zs = LC21.mergeFn xs zs) :
    ∀ ys, insert x rec ys = LC21.mergeFn (x :: xs) ys
  | []      => by
      show x :: rec [] = LC21.mergeFn (x :: xs) []
      rw [hrec []]; simp only [LC21.mergeFn_nil_right]
  | y :: ys => by
      show (if x ≤ y then x :: rec (y :: ys) else y :: insert x rec ys)
          = LC21.mergeFn (x :: xs) (y :: ys)
      rw [LC21.mergeFn_cons_eq]
      split
      · rw [hrec (y :: ys)]
      · rw [insert_eq x rec xs hrec ys]

/-- The reshaped fold, on converted input, agrees with the raw-`List` program: `foldCL (ofList xs) ys
    = mergeFn xs ys`, by induction on the first list `xs` (the fold axis), reusing `insert_eq`. -/
theorem foldCL_ofList : ∀ (xs ys : List Int), foldCL (ofList xs) ys = LC21.mergeFn xs ys := by
  intro xs
  induction xs with
  | nil => intro ys; exact (LC21.mergeFn_nil_left ys).symm
  | cons x xs ih =>
    intro ys
    show insert x (foldCL (ofList xs)) ys = LC21.mergeFn (x :: xs) ys
    exact insert_eq x (foldCL (ofList xs)) xs ih ys

/-! ## Correctness carries over from `L21.lean` (no re-proof of the merge argument) -/

/-- The allegory program produced by the derivation: the merge as a morphism `dInput ⟶ dAns`,
    computed by the reshaped-then-converted fold. -/
def derivedSolve : LC21.dInput ⟶ LC21.dAns := graph (fun p => foldCL (ofList p.1) p.2)

/-- The derived program equals `LC21.solve` (the graphs of extensionally equal functions), via the
    bridge `foldCL_ofList`. -/
theorem derived_eq_solve : derivedSolve = LC21.solve := by
  apply congrArg graph
  funext p
  exact foldCL_ofList p.1 p.2

/-- **Headline.**  The honest bundle: (1) the merge, reshaped onto the cons-list initial algebra with
    the FUNCTION carrier `List Int → List Int`, IS the catamorphism of `consScalarAlg g st`
    (`merge_emerges`); (2) the derived program equals the hand-written `LC21.solve` (`derived_eq_solve`,
    via `foldCL_ofList`); and (3) it therefore refines the spec — `LC21.solve_le_spec` (sortedness +
    exact multiset preservation) carried across.  The merge argument is REUSED, not re-proved. -/
theorem merge_derived_correct :
    ((graph foldCL : dCL Unit Int ⟶ ⟨List Int → List Int⟩) = cataR (consScalarAlg g st))
      ∧ (derivedSolve = LC21.solve)
      ∧ (derivedSolve ⊑ LC21.spec) := by
  refine ⟨merge_emerges, derived_eq_solve, ?_⟩
  rw [derived_eq_solve]
  exact LC21.solve_le_spec

/-! ## Running / cross-checking the reshaped fold

  The relational catamorphism is not `decide`-computable (its `cons` case is an existential over the
  carrier, and the carrier here is a function), so we `decide` the extensionally-equal computable
  witness `foldCL ∘ ofList` APPLIED to a second list (never the bare function carrier), and check it
  against the reused program `LC21.mergeFn` (LeetCode 21 examples). -/

example : foldCL (ofList [(1 : Int), 2, 4]) [1, 3, 4] = [1, 1, 2, 3, 4, 4] := by decide
example : foldCL (ofList ([] : List Int)) [0] = [0] := by decide
example : foldCL (ofList [(2 : Int), 5, 8]) [1, 3, 3, 9] = [1, 2, 3, 3, 5, 8, 9] := by decide

-- The reshaped fold, on converted input, reproduces the hand-written program exactly:
example : foldCL (ofList [(1 : Int), 2, 4]) [1, 3, 4] = LC21.mergeFn [1, 2, 4] [1, 3, 4] := by decide

end Freyd.Alg.RelSet.LC21D
