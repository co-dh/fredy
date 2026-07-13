/-
  LeetCode 171 — Excel Sheet Column Number — as an ALLEGORY PROGRAM.

  Problem: an Excel column title (`"A"`, `"AA"`, `"ZZ"`, …) is a base-26 numeral with digits
  `A=1,…,Z=26` (NOT `0..25` — there is no digit for zero). Model the title as a big-endian
  (most-significant letter first) `List Int` of letter values in `1..26`, e.g. `"AA" ↦ [1,1]`,
  `"ZZ" ↦ [26,26]`. Return the column number.

  1. **Program.** `colNumberFn : List Int → Int := xs.foldl (fun acc d => acc*26 + d) 0` — the
     base-26 Horner fold, most-significant digit first, literally `L66`'s `value` fold with
     `10 → 26`.

  2. **Honest spec — closed positional value.** `value xs := valueLE xs.reverse`, where
     `valueLE : List Int → Int` is the LITTLE-ENDIAN (least-significant first) place-value sum
     `valueLE [] = 0`, `valueLE (d :: ds) = d + 26 * valueLE ds` — i.e. `value [a,b,c] =
     a*26^2 + b*26 + c`, the honest closed-form definition of "the number this base-26 numeral
     denotes", not a restatement of the fold.

  3. **The bridge `value = valueLE ∘ reverse`, powers-free.** Exactly `L66`'s
     `value_eq_valueLE_reverse` move: core `List.foldl_eq_foldr_reverse` flips the big-endian LEFT
     fold to a RIGHT fold over `xs.reverse`; one induction (`foldr_eq_valueLE`) identifies that
     right fold with `valueLE`'s own front-consing recursion, since both recurse the SAME way
     (front-to-back on the reversed list) — no explicit powers of `26`, no append lemmas.

  4. **The digit range `1..26` is irrelevant to the value identity.** `colNumber_correct` holds for
     ANY `List Int`, exactly as `L66`'s carry lemma needed no `0 ≤ d ≤ 9` hypothesis — the base-26
     place-value identity doesn't care what the digits mean, only how they're folded.

  Mathlib-free; fully constructive (no `Classical.choice` expected).
-/
import AOP.A6_1_RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC171

open Freyd

/-! ## Program: base-26 Horner fold, most-significant digit first -/

/-- **The program**: `colNumberFn xs` folds a BIG-ENDIAN list of letter values (`A=1,…,Z=26`) into
    the column number via base-26 Horner's method: `colNumberFn [a,b,c] = ((0*26+a)*26+b)*26+c`. -/
def colNumberFn (xs : List Int) : Int := xs.foldl (fun acc d => acc * 26 + d) 0

/-! ## Spec: the honest closed-form positional value -/

/-- `valueLE ys` reads a LITTLE-ENDIAN digit list (least-significant digit first) back into the
    base-26 integer it denotes: `valueLE [] = 0`, `valueLE (d :: ds) = d + 26 * valueLE ds` — the
    closed place-value sum, e.g. `valueLE [c,b,a] = c + 26*b + 26^2*a`. -/
def valueLE : List Int → Int
  | [] => 0
  | d :: ds => d + 26 * valueLE ds

/-- **Honest spec**: the value of a BIG-ENDIAN digit list is the little-endian place-value sum of
    its reverse — `value [a,b,c] = a*26^2 + b*26 + c`, stated via `valueLE`, not via the fold. -/
def value (xs : List Int) : Int := valueLE xs.reverse

/-- **The bridge, crux half**: the base-26 left fold, once flipped to a right fold over the SAME
    (reversed) list by `foldl_eq_foldr_reverse`, computes exactly `valueLE` — both recurse
    front-to-back on `ys`, so the step functions line up by one `omega` per cons, no powers. -/
theorem foldr_eq_valueLE : ∀ ys : List Int, ys.foldr (fun d acc => acc * 26 + d) 0 = valueLE ys
  | [] => rfl
  | d :: ds => by
      have ih := foldr_eq_valueLE ds
      show (ds.foldr (fun d acc => acc * 26 + d) 0) * 26 + d = valueLE (d :: ds)
      rw [ih]; simp only [valueLE]; omega

/-! ## Correctness: the program computes the honest place value -/

/-- **Correctness of the allegory program** (the headline theorem): `colNumberFn` computes exactly
    the honest base-26 place value of the big-endian digit list. Fully general, no digit-range
    (`1..26`) hypothesis — the place-value identity doesn't care what the digits mean. -/
theorem colNumber_correct (xs : List Int) : colNumberFn xs = value xs := by
  show xs.foldl (fun acc d => acc * 26 + d) 0 = valueLE xs.reverse
  rw [List.foldl_eq_foldr_reverse]
  exact foldr_eq_valueLE xs.reverse

/-! ## `Rel(Set)` packaging -/

/-- The input object: big-endian lists of letter values (`A=1,…,Z=26`). -/
abbrev dTitle : RelSet.{0} := ⟨List Int⟩

/-- The output object: the column number. -/
abbrev dNum : RelSet.{0} := ⟨Int⟩

/-- **The allegory program**: LeetCode 171's column-number decoder as a morphism
    `dTitle ⟶ dNum` in `Rel(Set)`. -/
def solve : dTitle ⟶ dNum := graph colNumberFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map colNumberFn

/-! ## The morphism-equation headline -/

/-- **The specification** as a morphism `dTitle ⟶ dNum`: `v` is THE base-26 place value of the
    big-endian digit list — stated via `value`/`valueLE`, independently of the fold `colNumberFn`. -/
def spec : dTitle ⟶ dNum := fun xs v => v = value xs

/-- **The allegory-program headline**: `solve = spec` as morphisms in `Rel(Set)` — the program
    computes exactly the base-26 place value, not merely pointwise. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro xs v
  show (v = colNumberFn xs) ↔ (v = value xs)
  rw [colNumber_correct]

/-! ## Running the program -/

example : colNumberFn ([1] : List Int) = 1 := by decide      -- "A"  = 1
example : colNumberFn ([1, 1] : List Int) = 27 := by decide  -- "AA" = 27
example : colNumberFn ([26, 26] : List Int) = 702 := by decide -- "ZZ" = 702

end Freyd.Alg.RelSet.LC171
