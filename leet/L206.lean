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

/-! ## Specification and the structural-output headline -/

/-- `IsRev xs out` — `out` is the reversal of `xs`, characterized STRUCTURALLY and independently of
    the program `revFn`/`List.reverse`: the empty list reverses to empty; `a :: xs` reverses to
    "(reversal of `xs`) with `a` appended at the END".  A relation a priori, pinned to a function
    by `rev_unique` below. -/
def IsRev : List Int → List Int → Prop
  | [], out => out = []
  | a :: xs, out => ∃ r, IsRev xs r ∧ out = r ++ [a]

/-- **Existence**: `List.reverse` satisfies `IsRev` (uses `reverse_cons`: `(a::xs).reverse =
    xs.reverse ++ [a]`, exactly the recursive clause). -/
theorem reverse_isRev : ∀ xs : List Int, IsRev xs xs.reverse
  | [] => rfl
  | a :: xs => ⟨xs.reverse, reverse_isRev xs, List.reverse_cons⟩

/-- **Uniqueness**: the reversal of a list is unique.  Induction on `xs`; the append clause pins
    the last element and the IH pins the rest. -/
theorem rev_unique : ∀ (xs o₁ o₂ : List Int), IsRev xs o₁ → IsRev xs o₂ → o₁ = o₂
  | [], o₁, o₂, h₁, h₂ => by rw [h₁, h₂]
  | a :: xs, o₁, o₂, h₁, h₂ => by
      obtain ⟨r, hr, ho₁⟩ := h₁
      obtain ⟨r', hr', ho₂⟩ := h₂
      rw [ho₁, ho₂, rev_unique xs r r' hr hr']

/-- The **specification** as a morphism `dList ⟶ dList` in `Rel(Set)`: `out` is the reversal of
    `xs`, stated via `IsRev` (program-independent), NOT via `revFn`. -/
def spec : dList ⟶ dList := fun xs out => IsRev xs out

/-- **`solve` equals `spec` as relations** — the STRUCTURAL-OUTPUT headline: existence
    (`reverse_isRev`) plus uniqueness (`rev_unique`) make the program exactly the reversal
    relation. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro xs out
  show (out = revFn xs) ↔ IsRev xs out
  constructor
  · intro h; rw [h]; exact reverse_isRev xs
  · intro h; exact rev_unique xs out (revFn xs) h (reverse_isRev xs)

/-! ## Running the program -/

example : revFn ([1, 2, 3] : List Int) = [3, 2, 1] := by decide
example : revFn ([] : List Int) = [] := by decide
example : revFn ([1] : List Int) = [1] := by decide
example : revFn (revFn ([1, 2, 3] : List Int)) = [1, 2, 3] := by decide

end Freyd.Alg.RelSet.LC206
