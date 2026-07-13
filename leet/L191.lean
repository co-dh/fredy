/-
  LeetCode 191 — Number of 1 Bits — as an ALLEGORY PROGRAM.

  Problem: given a non-empty bit-list (`Bool`, `true` = a `1`-bit), return its Hamming weight —
  the number of `true` bits.

  This reuses the `L121` recipe (`Fredy/leetcode.md`) but with a NEW element type: the data is a
  `SnocList Bool Bool` (a non-empty list of bits, `A6_SnocList`'s engine instantiated at `L = E =
  Bool`), and the fold's running state is exactly the answer (a running bit-count), so no
  projection is needed after the catamorphism: `solve = cataR alg` on the nose.

  1. **Data** — a bit-list is `Bits := dSL Bool Bool`, the initial algebra of `F X = Bool + X×Bool`
     (`wrap b` a single bit, `snoc xs b` appends a bit).

  2. **Program** — `countFn` sums `b2n b ∈ {0,1}` over every bit, by structural recursion; it is
     the catamorphism of the algebra `alg = [ b ↦ b2n b, (n,b) ↦ n + b2n b ] : F(ℕ) → ℕ`, packaged
     as `solve : Bits ⟶ dNat := graph countFn` and proved equal to `cataR alg` (`solve_eq_cata`).

  3. **Specification** — the count is given REAL content, not a tautological restatement, via
     three characterizing theorems: it never exceeds the bit-list's `size` (`count_le_size`), it
     equals `size` exactly when every bit is `true` (`count_eq_size_iff_all_true`), and it is `0`
     exactly when every bit is `false` (`count_eq_zero_iff_all_false`).

  4. **Correctness** — `solve_correct` packages `solve = cataR alg` together with the three
     characterizations, so `solve` is both the catamorphism AND provably counts `1`-bits.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC191

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: a non-empty bit-list as a snoc-list of `Bool` -/

/-- The object of bit-lists in `Rel(Set)` — `SnocList Bool Bool` (`wrap b` = single bit, `snoc xs
    b` = `xs` with one more bit appended). -/
abbrev Bits : RelSet.{0} := dSL Bool Bool
/-- The object of natural numbers (bit counts) in `Rel(Set)`. -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## Bits as counts: `b2n` and its two extremes -/

/-- A bit's contribution to the count: `1` for `true`, `0` for `false`. -/
def b2n (b : Bool) : Nat := if b then 1 else 0

@[simp] theorem b2n_true : b2n true = 1 := rfl
@[simp] theorem b2n_false : b2n false = 0 := rfl

theorem b2n_le_one (b : Bool) : b2n b ≤ 1 := by cases b <;> simp [b2n]
theorem b2n_eq_one_iff (b : Bool) : b2n b = 1 ↔ b = true := by cases b <;> simp [b2n]
theorem b2n_eq_zero_iff (b : Bool) : b2n b = 0 ↔ b = false := by cases b <;> simp [b2n]

/-! ## The program: the count fold, packaged as a catamorphism -/

/-- The fold algebra `[ b ↦ b2n b,  (n,b) ↦ n + b2n b ] : F(ℕ) → ℕ`. -/
def algFn : (Fobj Bool Bool (dNat : RelSet.{0})).carrier → Nat
  | Sum.inl b => b2n b
  | Sum.inr (n, b) => n + b2n b

/-- The algebra as a morphism (a `Map`) `F(ℕ) ⟶ ℕ` in `Rel(Set)`. -/
def alg : Fobj Bool Bool (dNat : RelSet.{0}) ⟶ dNat := graph algFn

/-- The concrete fold (structural recursion): the running count of `true` bits. -/
def countFn : SnocList Bool Bool → Nat
  | SnocList.wrap b => b2n b
  | SnocList.snoc xs b => countFn xs + b2n b

/-- The answer IS the fold's state — no projection needed (unlike L121's `(min,best)` pair). -/
def solveFn : SnocList Bool Bool → Nat := countFn

/-- **The allegory program**: LeetCode 191's solution as a morphism `Bits ⟶ ℕ` in `Rel(Set)`. -/
def solve : Bits ⟶ dNat := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree. -/
theorem cataFold_alg : ∀ (xs : SnocList Bool Bool) (r : Nat),
    cataFold alg xs r ↔ r = countFn xs := by
  intro xs; induction xs with
  | wrap b => intro r; exact Iff.rfl
  | snoc xs b ih =>
    intro r
    simp only [cataFold_snoc]
    constructor
    · rintro ⟨r', hr', hfr⟩
      rw [ih r'] at hr'; subst hr'; exact hfr
    · intro h; exact ⟨countFn xs, (ih (countFn xs)).mpr rfl, h⟩

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈`, with NO trailing projection —
    the fold's running state already IS the answer (contrast L121's `≫ snd`). -/
theorem solve_eq_cata : solve = cataR alg := by
  apply hom_ext; intro xs v
  show v = solveFn xs ↔ cataFold alg xs v
  exact (cataFold_alg xs v).symm

/-! ## Spec: the count characterized by size bounds and membership extremes -/

/-- `size xs` — the number of bits in `xs`. -/
def size : SnocList Bool Bool → Nat
  | SnocList.wrap _ => 1
  | SnocList.snoc xs _ => size xs + 1

/-- The **specification** as a morphism `Bits ⟶ ℕ` in `Rel(Set)`: `k` is the count of `true` bits.
    (LeetCode 191's answer is exactly this relation's unique value.) -/
def spec : Bits ⟶ dNat := fun xs k => k = countFn xs

/-- Every bit of `xs` is `true`. -/
def allTrue : SnocList Bool Bool → Prop
  | SnocList.wrap b => b = true
  | SnocList.snoc xs b => allTrue xs ∧ b = true

/-- Every bit of `xs` is `false`. -/
def allFalse : SnocList Bool Bool → Prop
  | SnocList.wrap b => b = false
  | SnocList.snoc xs b => allFalse xs ∧ b = false

/-! ## Correctness: the count is bounded by, and characterizes, the extremes -/

/-- **The count never exceeds the size** — the number of `1`-bits is at most the number of bits. -/
theorem count_le_size : ∀ xs, countFn xs ≤ size xs := by
  intro xs; induction xs with
  | wrap b => show b2n b ≤ 1; exact b2n_le_one b
  | snoc xs b ih =>
    show countFn xs + b2n b ≤ size xs + 1
    have hb := b2n_le_one b
    omega

/-- **The count reaches the size exactly when every bit is `true`.** -/
theorem count_eq_size_iff_all_true : ∀ xs, countFn xs = size xs ↔ allTrue xs := by
  intro xs; induction xs with
  | wrap b =>
    show b2n b = 1 ↔ b = true
    exact b2n_eq_one_iff b
  | snoc xs b ih =>
    show countFn xs + b2n b = size xs + 1 ↔ allTrue xs ∧ b = true
    constructor
    · intro h
      have hle := count_le_size xs
      have hbnd := b2n_le_one b
      have hb1 : b2n b = 1 := by omega
      have heq : countFn xs = size xs := by omega
      exact ⟨ih.mp heq, (b2n_eq_one_iff b).mp hb1⟩
    · rintro ⟨hxs, hb⟩
      rw [ih.mpr hxs, (b2n_eq_one_iff b).mpr hb]

/-- **The count is `0` exactly when every bit is `false`.** -/
theorem count_eq_zero_iff_all_false : ∀ xs, countFn xs = 0 ↔ allFalse xs := by
  intro xs; induction xs with
  | wrap b =>
    show b2n b = 0 ↔ b = false
    exact b2n_eq_zero_iff b
  | snoc xs b ih =>
    show countFn xs + b2n b = 0 ↔ allFalse xs ∧ b = false
    constructor
    · intro h
      have h1 : countFn xs = 0 := by omega
      have h2 : b2n b = 0 := by omega
      exact ⟨ih.mp h1, (b2n_eq_zero_iff b).mp h2⟩
    · rintro ⟨hxs, hb⟩
      rw [ih.mpr hxs, (b2n_eq_zero_iff b).mpr hb]

/-- **Correctness of the allegory program**: `solve` IS the catamorphism of `alg`, and the count it
    computes is bounded by `size` and pins down the two extremes `allTrue`/`allFalse`. -/
theorem solve_correct (xs : SnocList Bool Bool) :
    solveFn xs ≤ size xs ∧
      (solveFn xs = size xs ↔ allTrue xs) ∧
      (solveFn xs = 0 ↔ allFalse xs) :=
  ⟨count_le_size xs, count_eq_size_iff_all_true xs, count_eq_zero_iff_all_false xs⟩

/-! ## Honest exact-value headline: ground the answer in Lean's standard `List.count`

  The `spec` above (`k = countFn xs`) merely restates the program (`solveFn := countFn`).  The honest
  characterization of "number of `1`-bits" grounds it in Lean core's own `List.count`: convert the
  bit-word to a plain `List Bool` and count the `true`s.  `countFn_eq_count` is the genuine bridge
  (the running fold equals the standard count), so `solve = specCount` is a real derivation. -/

/-- The bit-word as a plain `List Bool` (LSB-first, matching `countFn`'s fold order). -/
def toBits : SnocList Bool Bool → List Bool
  | SnocList.wrap b => [b]
  | SnocList.snoc xs b => toBits xs ++ [b]

/-- **The running count IS Lean's standard count of `true`** over the converted bit-list. -/
theorem countFn_eq_count : ∀ xs, countFn xs = (toBits xs).count true
  | SnocList.wrap b => by cases b <;> rfl
  | SnocList.snoc xs b => by
      show countFn xs + b2n b = (toBits xs ++ [b]).count true
      rw [List.count_append, countFn_eq_count xs]
      have hb : ([b] : List Bool).count true = b2n b := by cases b <;> rfl
      rw [hb]

/-- The **honest specification** as a morphism `Bits ⟶ ℕ` in `Rel(Set)`: the answer is the standard
    `List.count` of `true` bits — grounded in Lean core, not in the file's own fold. -/
def specCount : Bits ⟶ dNat := fun xs k => k = (toBits xs).count true

/-- **`solve` equals `specCount` as relations** — the EXACT-VALUE headline: the fold-based program
    equals the standard count of `true` bits.  The answer is pinned by the equation, so existence +
    uniqueness collapse to `countFn_eq_count`. -/
theorem solve_eq_specCount : solve = specCount := by
  apply hom_ext; intro xs k
  show (k = solveFn xs) ↔ (k = (toBits xs).count true)
  rw [show solveFn xs = (toBits xs).count true from countFn_eq_count xs]

/-! ## Running the program -/

/-- Build a bit-list from a first bit and the rest, in order. -/
def ofBits' (first : Bool) (rest : List Bool) : SnocList Bool Bool :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : countFn (ofBits' true [false, true, true]) = 3 := by decide
example : countFn (ofBits' false [false, false, false]) = 0 := by decide
example : countFn (ofBits' true [true, true, true]) = size (ofBits' true [true, true, true]) := by
  decide
example : countFn (ofBits' false []) = 0 := by decide

end Freyd.Alg.RelSet.LC191
