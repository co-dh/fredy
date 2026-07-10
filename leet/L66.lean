/-
  LeetCode 66 — Plus One — as an ALLEGORY PROGRAM.

  Problem: a non-negative integer is given as a digit list `0..9`, MOST-significant digit first
  (big-endian), e.g. `[1,2,3]` denotes `123`.  Return the digit list of the integer plus one.

  1. **Value semantics.** `value : List Int → Int` reads a BIG-ENDIAN digit list back into the
     integer it denotes, via a left fold (Horner's method): `value xs := xs.foldl (fun acc d =>
     acc*10+d) 0`.  Internally the program works LITTLE-ENDIAN (least-significant digit first,
     matching `L2`'s `value`), where `valueLE (d :: ds) = d + 10 * valueLE ds` — the carry ripples
     by consing at the front, structural recursion, no fuel needed (contrast `L2`'s two-input
     carry-ripple, which genuinely needs fuel).

  2. **Program.** `plusOneRev : List Int → List Int` increments the REVERSED (little-endian)
     digits with carry: `[] ↦ [1]` (a fresh leading `1` past an empty number); `d :: ds ↦ if
     d + 1 = 10 then 0 :: plusOneRev ds else (d+1) :: ds` (roll over to `0` and carry into `ds`, or
     just bump the digit and stop).  `plusOneFn xs := (plusOneRev xs.reverse).reverse` undoes the
     endianness flip.

  3. **The bridge `value = valueLE ∘ reverse`.** Core `List.foldl_eq_foldr_reverse` turns the
     big-endian LEFT fold into a RIGHT fold over the reversed list with the flipped step
     `fun d acc => acc*10+d`; a one-line induction (`foldr_eq_valueLE`) then identifies that right
     fold with `valueLE`'s own (front-consing) recursion — no explicit powers of `10`, no append
     lemmas, since both sides recurse the SAME way (front-to-back on the little-endian list).

  4. **The carry lemma is UNCONDITIONAL.** `valueLE_plusOneRev : valueLE (plusOneRev ds) = valueLE
     ds + 1` needs NO digit-range hypothesis (`0 ≤ d ≤ 9`): the non-carry branch (`d+1 ≠ 10`) is a
     pure algebraic rearrangement for ANY `d`, and the carry branch consumes `d + 1 = 10` (from the
     `if`'s own condition) directly, so `0..9`-ness of the input digits is never needed for VALUE
     preservation — it only matters for reading the output as a conventional digit list (not
     claimed here, matching `L2`'s scope).

  Mathlib-free; fully constructive (no `Classical.choice` expected).
-/
import AOP.A6_1_RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC66

open Freyd

/-! ## Value semantics -/

/-- `value xs` reads a BIG-ENDIAN digit list (most-significant digit first) back into the integer
    it denotes, via a left fold (Horner's method): `value [1,2,3] = ((0*10+1)*10+2)*10+3 = 123`. -/
def value (xs : List Int) : Int := xs.foldl (fun acc d => acc * 10 + d) 0

/-- `valueLE ys` reads a LITTLE-ENDIAN digit list (least-significant digit first) back into the
    integer it denotes: `valueLE [] = 0`, `valueLE (d :: ds) = d + 10 * valueLE ds` — literally
    `L2.value`, restated here so this file stays self-contained (a different problem, not a
    wrapper around `L2`). -/
def valueLE : List Int → Int
  | [] => 0
  | d :: ds => d + 10 * valueLE ds

/-- **The bridge, crux half**: `value`'s left fold, once flipped to a right fold over the SAME
    (little-endian) list by `foldl_eq_foldr_reverse`, computes exactly `valueLE` — both recurse
    front-to-back on `ys`, so the step functions line up by one `omega` per cons, no powers. -/
theorem foldr_eq_valueLE : ∀ ys : List Int, ys.foldr (fun d acc => acc * 10 + d) 0 = valueLE ys
  | [] => rfl
  | d :: ds => by
      have ih := foldr_eq_valueLE ds
      show (ds.foldr (fun d acc => acc * 10 + d) 0) * 10 + d = valueLE (d :: ds)
      rw [ih]; simp only [valueLE]; omega

/-- **The bridge**: a big-endian value equals the little-endian value of the REVERSED list. -/
theorem value_eq_valueLE_reverse (xs : List Int) : value xs = valueLE xs.reverse := by
  show xs.foldl (fun acc d => acc * 10 + d) 0 = valueLE xs.reverse
  rw [List.foldl_eq_foldr_reverse]
  exact foldr_eq_valueLE xs.reverse

/-! ## Program: increment the little-endian (reversed) digits with carry, then flip back -/

/-- Increment a LITTLE-ENDIAN digit list by one, rippling a carry through leading (in this
    orientation) `9`s: `[] ↦ [1]`, `d :: ds ↦` roll to `0` and carry into `ds` if `d+1=10`, else
    just bump `d`. Plain structural recursion — no fuel (contrast `L2`'s two-input carry-ripple). -/
def plusOneRev : List Int → List Int
  | [] => [1]
  | d :: ds => if d + 1 = 10 then 0 :: plusOneRev ds else (d + 1) :: ds

/-- **The program**: increment a BIG-ENDIAN digit list by one — reverse to little-endian, ripple
    the carry, reverse back. -/
def plusOneFn (xs : List Int) : List Int := (plusOneRev xs.reverse).reverse

/-! ## Correctness: value preservation -/

/-- **The carry lemma, UNCONDITIONAL on digit range**: incrementing the little-endian list bumps
    its value by exactly `1`. The non-carry branch is algebra for any `d`; the carry branch
    consumes `d + 1 = 10` from the `if`'s own condition — no `0 ≤ d ≤ 9` hypothesis needed. -/
theorem valueLE_plusOneRev : ∀ ds : List Int, valueLE (plusOneRev ds) = valueLE ds + 1
  | [] => by simp only [plusOneRev, valueLE]; omega
  | d :: ds => by
      by_cases hd : d + 1 = 10
      · have ih := valueLE_plusOneRev ds
        simp only [plusOneRev, if_pos hd, valueLE] at ih ⊢
        omega
      · simp only [plusOneRev, if_neg hd, valueLE]
        omega

/-- **Correctness of the allegory program** (the headline theorem): `plusOneFn` preserves value
    plus one — the digit list of `value xs + 1`. Fully general, no digit-range hypothesis. -/
theorem plusOne_correct (xs : List Int) : value (plusOneFn xs) = value xs + 1 := by
  show value ((plusOneRev xs.reverse).reverse) = value xs + 1
  rw [value_eq_valueLE_reverse, List.reverse_reverse, valueLE_plusOneRev,
    ← value_eq_valueLE_reverse]

/-! ## `Rel(Set)` packaging -/

/-- The input/output object: big-endian digit lists. -/
abbrev dDigits : RelSet.{0} := ⟨List Int⟩

/-- **The allegory program**: LeetCode 66's plus-one as a morphism `dDigits ⟶ dDigits` in
    `Rel(Set)`. -/
def solve : dDigits ⟶ dDigits := graph plusOneFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map plusOneFn

/-! ## Running the program -/

example : plusOneFn ([1, 2, 3] : List Int) = [1, 2, 4] := by decide
example : plusOneFn ([9, 9] : List Int) = [1, 0, 0] := by decide

end Freyd.Alg.RelSet.LC66
