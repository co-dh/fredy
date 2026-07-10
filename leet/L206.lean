/-
  LeetCode 206 — Reverse Linked List — as an ALLEGORY PROGRAM, the STRUCTURAL-OUTPUT case.

  Problem: reverse a (singly) linked list.

  Model the list as a plain `List Int` (cleanest for reversal) — the answer is again a `List Int`,
  so `solve` is an ENDOMORPHISM `dList ⟶ dList` in `Rel(Set)`, source and target the SAME object,
  exactly `L226`'s structural-output shape (there `dTree A ⟶ dTree A`; here the list analogue).

  1. **Program** — `revFn := List.reverse` (Lean core's own list reversal — no ad-hoc
     reimplementation needed, since the accumulator recursion `List.reverse` already IS the O(n)
     fold), packaged as `solve : dList ⟶ dList := graph revFn`, an endomorphism like `L226`'s
     `solve : dTree A ⟶ dTree A`.

  2. **Specification / correctness** — a structural-output program has no order to refine into (no
     `max(≤)·Λ spec` extremum, unlike `L121`/`L53`); correctness is the direct structural fact
     `solve_correct : revFn xs = xs.reverse` (definitional here, since `revFn := List.reverse`), plus
     the natural EXTRA laws of a same-object program (cf. `L226`'s `invert_invert`):
     **`rev_rev`** (reversing twice is the identity) and **`rev_length`** (reversal preserves length).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC206

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: the answer object is again a `List Int` — a STRUCTURAL-OUTPUT endomorphism -/

/-- The object of lists in `Rel(Set)` — reuses `SL`'s generic wrapper `dL` for a plain type. -/
abbrev dList : RelSet.{0} := dL (List Int)

/-! ## The program: `List.reverse` -/

/-- The concrete program: Lean core's list reversal. -/
def revFn : List Int → List Int := fun xs => xs.reverse

/-- **The allegory program**: LeetCode 206's solution as an ENDOMORPHISM `dList ⟶ dList` in
    `Rel(Set)` — the STRUCTURAL-OUTPUT case, source and target the SAME object. -/
def solve : dList ⟶ dList := graph revFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map revFn

/-! ## Correctness: `solve` reverses, and reversing twice is the identity -/

/-- **Correctness of the allegory program**: `revFn` computes `List.reverse`. -/
theorem solve_correct (xs : List Int) : revFn xs = xs.reverse := rfl

/-- **Involutivity**: reversing twice is the identity — the list analogue of `L226`'s
    `invert_invert`, the natural EXTRA law of a STRUCTURAL-OUTPUT program (no scalar/Bool answer
    object has this shape). -/
theorem rev_rev (xs : List Int) : revFn (revFn xs) = xs := by
  show xs.reverse.reverse = xs
  exact List.reverse_reverse xs

/-- **Length preservation**: reversal does not change the length. -/
theorem rev_length (xs : List Int) : (revFn xs).length = xs.length := by
  show xs.reverse.length = xs.length
  exact List.length_reverse

/-! ## Running the program -/

example : revFn ([1, 2, 3] : List Int) = [3, 2, 1] := by decide
example : revFn ([] : List Int) = [] := by decide
example : revFn ([1] : List Int) = [1] := by decide
example : revFn (revFn ([1, 2, 3] : List Int)) = [1, 2, 3] := by decide

end Freyd.Alg.RelSet.LC206
