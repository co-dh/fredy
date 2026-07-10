/-
  LeetCode 67 — Add Binary — DERIVED as a relational HYLOMORPHISM (O(n+m)).

  `Fredy/L67.lean` writes binary addition as `addBitsRev : Nat → Int → List Int → List Int →
  List Int`, a structural recursion on an explicit FUEL parameter over the REVERSED (little-endian)
  inputs — the standard taming of a genuine two-input recursion, so `decide` reduces.  The fuel is
  scaffolding, exactly as in `L2_derived`'s base-`10` case: the real recursion consumes one bit off
  BOTH lists at once while threading a carry, the divide-and-conquer / two-input shape whose right
  scheme is the DUAL of a fold — a RECURSIVE COALGEBRA re-folded with an algebra.

  `Hylo.hyloFold_unique` (`Fredy/A6_GenHylo.lean`) is the uniqueness law: any `h : S → C` obeying
  `h s = match c s with | inl l => g l | inr (e,s') => st e (h s')` IS the hylomorphism
  `hyloR c μ hdec g st` of the `Nat`-measured recursive coalgebra `c`.  Instantiating it here KILLS
  the fuel exactly as `L2_derived.addH` did — the carry is folded into the STATE instead — with base
  `2` (`%2`/`/2`) replacing base `10` (`%10`/`/10`):

    * state      `S := Int × List Int × List Int` = (carry, xs, ys), LITTLE-ENDIAN (bit-reversed);
    * leaf `L := List Int`, digit `E := Int`, result `C := List Int`;
    * coalgebra  `c (carry,xs,ys)` — when both lists are empty, leaf `.inl` emitting the leftover
      carry-out bit (`[]` if the carry is `0`, else `[carry]`); otherwise pop a bit off each PRESENT
      list, form `s := carry + x + y`, and emit the node `.inr (s % 2, (s / 2, xs', ys'))`;
    * measure    `μ (carry,xs,ys) := xs.length + ys.length`, dropping on every `.inr` step (`hdec`);
    * algebra    base `g := id` (a leaf returns the leftover-carry list verbatim), step `st := (· :: ·)`
      (cons the emitted bit onto the sum's tail).

  On TOP of the base-2 mirroring, `L67` differs from `L2` in one genuine way: `L2`'s digit lists are
  already little-endian (LeetCode's convention there), but `L67`'s binary strings are BIG-ENDIAN
  (most-significant bit first, the natural convention for `"101" = 5`).  So the fuel-free
  hylomorphism-emerged `addH` only ever sees little-endian state; the derived PROGRAM
  `addBinaryH xs ys := (addH (0, xs.reverse, ys.reverse)).reverse` wraps it with the same
  reverse-in/reverse-out bridge `L67.addBinaryFn` uses, and `addBinaryH_eq_addBinaryFn` (the
  fuel-irrelevance bridge, transported through both reversals) identifies the two — so value
  preservation is REUSED from `L67.addBinary_correct`, not re-proved.

  Headline shape 4 (structural output / value).  Mathlib-free; headline axioms ⊆ {propext,
  Quot.sound}.
-/
import Fredy.A6_GenHylo
import Fredy.L67

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC67D

open Freyd

/-! ## Binary addition as a measured recursive coalgebra (carry threaded through the state) -/

/-- The addition coalgebra on state `(carry, xs, ys)`, LITTLE-ENDIAN inputs: emit a leaf (`.inl`)
    when both lists are exhausted — the answer is the leftover carry-out bit (`[]` if the carry is
    `0`) — otherwise pop a bit off each PRESENT list, form `s := carry + x + y`, and emit the node
    `.inr (s % 2, (s / 2, xs', ys'))`.  Branch order matches `LC67.addBitsRev`'s recurrence EXACTLY,
    base `2` in place of `L2`'s base `10`. -/
def c : Int × List Int × List Int → Sum (List Int) (Int × (Int × List Int × List Int))
  | (cr, [], []) => Sum.inl (if cr = 0 then [] else [cr])
  | (cr, x :: xs, []) => Sum.inr ((cr + x) % 2, ((cr + x) / 2, xs, []))
  | (cr, [], y :: ys) => Sum.inr ((cr + y) % 2, ((cr + y) / 2, [], ys))
  | (cr, x :: xs, y :: ys) => Sum.inr ((cr + x + y) % 2, ((cr + x + y) / 2, xs, ys))

/-- The measure: total remaining length of the two bit lists (the carry does not count).  The
    coalgebra's unfolding is well-founded because every `.inr` step drops at least one element. -/
def μ : Int × List Int × List Int → Nat := fun p => p.2.1.length + p.2.2.length

/-- Every `.inr` step drops at least one element, so `μ` strictly decreases — the well-foundedness
    witness the hylomorphism law demands. -/
theorem hdec : ∀ s e s', c s = Sum.inr (e, s') → μ s' < μ s := by
  intro s e s' h
  obtain ⟨cr, xs, ys⟩ := s
  cases xs with
  | nil =>
    cases ys with
    | nil => simp only [c] at h; nomatch h
    | cons y ys =>
      simp only [c] at h
      injection h with h1; injection h1 with h2 h3; subst h3
      simp only [μ, List.length_cons, List.length_nil]; omega
  | cons x xs =>
    cases ys with
    | nil =>
      simp only [c] at h
      injection h with h1; injection h1 with h2 h3; subst h3
      simp only [μ, List.length_cons, List.length_nil]; omega
    | cons y ys =>
      simp only [c] at h
      injection h with h1; injection h1 with h2 h3; subst h3
      simp only [μ, List.length_cons]; omega

/-- The fuel-free program named by the scheme: schoolbook carry-ripple BINARY addition, by
    well-founded recursion on the measure `μ` (no fuel).  Its four equations mirror the coalgebra
    `c` exactly. -/
def addH : Int × List Int × List Int → List Int
  | (cr, [], []) => if cr = 0 then [] else [cr]
  | (cr, x :: xs, []) => (cr + x) % 2 :: addH ((cr + x) / 2, xs, [])
  | (cr, [], y :: ys) => (cr + y) % 2 :: addH ((cr + y) / 2, [], ys)
  | (cr, x :: xs, y :: ys) => (cr + x + y) % 2 :: addH ((cr + x + y) / 2, xs, ys)
termination_by s => s.2.1.length + s.2.2.length
decreasing_by
  all_goals simp only [List.length_cons]; omega

/-! ## `addH` EMERGES as the relational hylomorphism -/

/-- **The derivation.**  The fuel-free program `addH` IS the relational hylomorphism of the measured
    coalgebra `c` with algebra `[id, (· :: ·)]` — it was never re-written as a hylomorphism;
    `hyloFold_unique` certifies it satisfies the hylomorphism recurrence.  The remaining goal is
    exactly "`addH s = match c s with | inl l => l | inr (e,s') => e :: addH s'`", discharged by the
    four-way case split on `(xs, ys)` using `addH`'s and `c`'s own defining equations. -/
theorem add_emerges :
    (graph addH : (⟨Int × List Int × List Int⟩ : RelSet.{0}) ⟶ ⟨List Int⟩)
      = Hylo.hyloR c μ hdec id (· :: ·) := by
  refine Hylo.hyloFold_unique c μ hdec id (· :: ·) addH ?_
  intro s
  obtain ⟨cr, xs, ys⟩ := s
  cases xs with
  | nil =>
    cases ys with
    | nil => simp only [c, addH, id_eq]
    | cons y ys => simp only [c, addH]
  | cons x xs =>
    cases ys with
    | nil => simp only [c, addH]
    | cons y ys => simp only [c, addH]

/-! ## Fuel-irrelevance bridge: `addH` agrees with `L67`'s fuelled `addBitsRev` -/

/-- **Structural fuel-irrelevance bridge**: whenever the fuel covers both lists' lengths, the
    fuelled program `LC67.addBitsRev` and the fuel-free `addH` agree.  By induction on the fuel;
    each cons step is the induction hypothesis after one unfolding — literally `L2_derived`'s
    `addFuel_eq_addH` with `10` replaced by `2`. -/
theorem addBitsRev_eq_addH : ∀ (f : Nat) (cr : Int) (xs ys : List Int),
    xs.length + ys.length ≤ f → LC67.addBitsRev f cr xs ys = addH (cr, xs, ys) := by
  intro f
  induction f with
  | zero =>
    intro cr xs ys hlen
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
    subst hx; subst hy
    simp only [LC67.addBitsRev, addH]
  | succ f ih =>
    intro cr xs ys hlen
    cases xs with
    | nil =>
      cases ys with
      | nil => simp only [LC67.addBitsRev, addH]
      | cons y ys =>
        have hlen' : ([] : List Int).length + ys.length ≤ f := by
          simp only [List.length_cons, List.length_nil] at hlen ⊢; omega
        simp only [LC67.addBitsRev, addH]
        rw [ih ((cr + y) / 2) [] ys hlen']
    | cons x xs =>
      cases ys with
      | nil =>
        have hlen' : xs.length + ([] : List Int).length ≤ f := by
          simp only [List.length_cons, List.length_nil] at hlen ⊢; omega
        simp only [LC67.addBitsRev, addH]
        rw [ih ((cr + x) / 2) xs [] hlen']
      | cons y ys =>
        have hlen' : xs.length + ys.length ≤ f := by
          simp only [List.length_cons] at hlen; omega
        simp only [LC67.addBitsRev, addH]
        rw [ih ((cr + x + y) / 2) xs ys hlen']

/-! ## The full program: BIG-ENDIAN inputs, reverse to little-endian, drain, reverse back -/

/-- **The derived program**: add two BIG-ENDIAN binary digit lists by reversing to little-endian
    (`L66`/`L67`'s BE↔LE bridge), draining the fuel-free hylomorphism `addH` from carry `0`, and
    reversing the result back — the exact same wrapping `LC67.addBinaryFn` uses around its fuelled
    `addBitsRev`, here around the hylomorphism-derived `addH`. -/
def addBinaryH (xs ys : List Int) : List Int :=
  (addH (0, xs.reverse, ys.reverse)).reverse

/-- `addBinaryH` and `LC67.addBinaryFn` name the same function: both reverse in, drain with
    sufficient fuel, reverse out; the drains agree by `addBitsRev_eq_addH` at
    `f := xs.reverse.length + ys.reverse.length + 1`. -/
theorem addBinaryH_eq_addBinaryFn (xs ys : List Int) :
    addBinaryH xs ys = LC67.addBinaryFn xs ys := by
  simp only [addBinaryH, LC67.addBinaryFn]
  congr 1
  have hlen : xs.reverse.length + ys.reverse.length ≤ xs.length + ys.length + 1 := by
    simp only [List.length_reverse]; omega
  exact (addBitsRev_eq_addH (xs.length + ys.length + 1) 0 xs.reverse ys.reverse hlen).symm

/-- Value preservation for the derived program, REUSED from `LC67.addBinary_correct` through
    `addBinaryH_eq_addBinaryFn` — the schoolbook binary-addition argument (and the BE↔LE bridge) are
    not re-proved. -/
theorem addBinaryH_value (xs ys : List Int) :
    LC67.value (addBinaryH xs ys) = LC67.value xs + LC67.value ys := by
  rw [addBinaryH_eq_addBinaryFn]; exact LC67.addBinary_correct xs ys

/-- **Headline.**  The honest bundle: (1) the fuel-free program `addH` IS the relational
    hylomorphism of the measured coalgebra `c` with algebra `[id, (· :: ·)]` (`add_emerges`); and
    (2) the full BE-wrapped program `addBinaryH` preserves value — the number denoted by the output
    big-endian binary digit list is the sum of the two inputs' values (`addBinaryH_value`, carried
    across from `LC67.addBinary_correct`, NOT re-proved).  The certified program is the fuel-free
    O(n+m) `addBinaryH`, not the fuelled `addBinaryFn`. -/
theorem addBinary_derived_correct :
    ((graph addH : (⟨Int × List Int × List Int⟩ : RelSet.{0}) ⟶ ⟨List Int⟩)
      = Hylo.hyloR c μ hdec id (· :: ·))
    ∧ (∀ xs ys : List Int, LC67.value (addBinaryH xs ys) = LC67.value xs + LC67.value ys) :=
  ⟨add_emerges, addBinaryH_value⟩

/-! ## Running the certified program

  `addH` is well-founded-recursive, so `decide` does not reduce it directly; through
  `addBinaryH_eq_addBinaryFn` the examples reduce to the kernel-reducible `LC67.addBinaryFn`. -/

example : addBinaryH ([1, 0, 1, 1] : List Int) [1, 0, 1] = [1, 0, 0, 0, 0] := by
  rw [addBinaryH_eq_addBinaryFn]; decide
example : addBinaryH ([1, 1] : List Int) [1] = [1, 0, 0] := by
  rw [addBinaryH_eq_addBinaryFn]; decide

end Freyd.Alg.RelSet.LC67D
