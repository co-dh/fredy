/-
  LeetCode 2 — Add Two Numbers — DERIVED as a relational HYLOMORPHISM (O(n+m)).

  `leet/L2.lean` writes carry-ripple addition as `addFuel : Nat → Int → List Int → List Int →
  List Int`, a structural recursion on an explicit FUEL parameter (the standard taming of a genuine
  two-input recursion, so `decide` reduces).  The fuel is scaffolding: the real recursion consumes one
  digit off BOTH lists at once while threading a carry, exactly the divide-and-conquer / two-input
  shape whose right scheme is the DUAL of a fold — a RECURSIVE COALGEBRA re-folded with an algebra.

  `Hylo.hyloFold_unique` (`AOP/A6_GenHylo.lean`) is the uniqueness law: any `h : S → C` obeying
  `h s = match c s with | inl l => g l | inr (e,s') => st e (h s')` IS the hylomorphism
  `hyloR c μ hdec g st` of the `Nat`-measured recursive coalgebra `c`.  Instantiating it here KILLS
  the fuel — the carry is folded into the STATE instead:

    * state      `S := Int × List Int × List Int` = (carry, xs, ys);
    * leaf `L := List Int`, digit `E := Int`, result `C := List Int`;
    * coalgebra  `c (carry,xs,ys)` — when both lists are empty, leaf `.inl` emitting the leftover
      carry-out digit (`[]` if the carry is `0`, else `[carry]`); otherwise pop a digit off each
      PRESENT list, form `s := carry + x + y`, and emit the node `.inr (s % 10, (s / 10, xs', ys'))`;
    * measure    `μ (carry,xs,ys) := xs.length + ys.length`, dropping on every `.inr` step (`hdec`);
    * algebra    base `g := id` (a leaf returns the leftover-carry list verbatim), step `st := (· :: ·)`
      (cons the emitted digit onto the sum's tail).

  `addH` is the fuel-free program this scheme names.  `add_emerges` runs `hyloFold_unique` on it: it
  certifies `addH` IS the relational hylomorphism of `c` with algebra `[id, (· :: ·)]` — the program
  was never re-written, only shown to satisfy the hylomorphism recurrence (a four-way case split,
  discharged in place).  Correctness is REUSED, not re-proved: the only new fact is the structural
  fuel-irrelevance bridge `addFuel_eq_addH` (fuel ≥ length ⟹ `addFuel = addH`), through which
  `addH (0, xs, ys) = LC2.addFn xs ys` and hence value preservation carries over from `LC2.add_correct`.

  Headline shape 4 (structural output / value).  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenHylo
import leet.L2

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC2D

open Freyd

/-! ## Addition as a measured recursive coalgebra (carry threaded through the state) -/

/-- The addition coalgebra on state `(carry, xs, ys)`: emit a leaf (`.inl`) when both lists are
    exhausted — the answer is the leftover carry-out digit (`[]` if the carry is `0`) — otherwise pop
    a digit off each PRESENT list, form `s := carry + x + y`, and emit the node `.inr (s % 10,
    (s / 10, xs', ys'))`.  Branch order matches `LC2.addFuel`'s recurrence EXACTLY. -/
def c : Int × List Int × List Int → Sum (List Int) (Int × (Int × List Int × List Int))
  | (cr, [], []) => Sum.inl (if cr = 0 then [] else [cr])
  | (cr, x :: xs, []) => Sum.inr ((cr + x) % 10, ((cr + x) / 10, xs, []))
  | (cr, [], y :: ys) => Sum.inr ((cr + y) % 10, ((cr + y) / 10, [], ys))
  | (cr, x :: xs, y :: ys) => Sum.inr ((cr + x + y) % 10, ((cr + x + y) / 10, xs, ys))

/-- The measure: total remaining length of the two digit lists (the carry does not count).  The
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

/-- The fuel-free program named by the scheme: schoolbook carry-ripple addition, by well-founded
    recursion on the measure `μ` (no fuel).  Its four equations mirror the coalgebra `c` exactly. -/
def addH : Int × List Int × List Int → List Int
  | (cr, [], []) => if cr = 0 then [] else [cr]
  | (cr, x :: xs, []) => (cr + x) % 10 :: addH ((cr + x) / 10, xs, [])
  | (cr, [], y :: ys) => (cr + y) % 10 :: addH ((cr + y) / 10, [], ys)
  | (cr, x :: xs, y :: ys) => (cr + x + y) % 10 :: addH ((cr + x + y) / 10, xs, ys)
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

/-! ## Correctness carries over from `L2.lean` (no re-proof of value preservation) -/

/-- **Structural fuel-irrelevance bridge**: whenever the fuel covers both lists' lengths, the fuelled
    program `LC2.addFuel` and the fuel-free `addH` agree.  By induction on the fuel; each cons step is
    the induction hypothesis after one unfolding.  This is the only new fact — it is a reshaping
    bridge between the two presentations, NOT a re-proof of value preservation. -/
theorem addFuel_eq_addH : ∀ (f : Nat) (cr : Int) (xs ys : List Int),
    xs.length + ys.length ≤ f → LC2.addFuel f cr xs ys = addH (cr, xs, ys) := by
  intro f
  induction f with
  | zero =>
    intro cr xs ys hlen
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
    subst hx; subst hy
    simp only [LC2.addFuel, addH]
  | succ f ih =>
    intro cr xs ys hlen
    cases xs with
    | nil =>
      cases ys with
      | nil => simp only [LC2.addFuel, addH]
      | cons y ys =>
        have hlen' : ([] : List Int).length + ys.length ≤ f := by
          simp only [List.length_cons, List.length_nil] at hlen ⊢; omega
        simp only [LC2.addFuel, addH]
        rw [ih ((cr + y) / 10) [] ys hlen']
    | cons x xs =>
      cases ys with
      | nil =>
        have hlen' : xs.length + ([] : List Int).length ≤ f := by
          simp only [List.length_cons, List.length_nil] at hlen ⊢; omega
        simp only [LC2.addFuel, addH]
        rw [ih ((cr + x) / 10) xs [] hlen']
      | cons y ys =>
        have hlen' : xs.length + ys.length ≤ f := by
          simp only [List.length_cons] at hlen; omega
        simp only [LC2.addFuel, addH]
        rw [ih ((cr + x + y) / 10) xs ys hlen']

/-- The hylomorphism program `addH` at carry `0` is exactly `LC2.addFn` — the two presentations name
    the same function.  Immediate from the fuel-irrelevance bridge at `f := xs.length + ys.length + 1`. -/
theorem addH_eq_addFn (xs ys : List Int) : addH (0, xs, ys) = LC2.addFn xs ys := by
  simp only [LC2.addFn]
  exact (addFuel_eq_addH (xs.length + ys.length + 1) 0 xs ys (by omega)).symm

/-- Value preservation for the derived program, REUSED from `LC2.add_correct` through
    `addH_eq_addFn` — the schoolbook-addition argument is not re-proved. -/
theorem addH_value (xs ys : List Int) :
    LC2.value (addH (0, xs, ys)) = LC2.value xs + LC2.value ys := by
  rw [addH_eq_addFn]; exact LC2.add_correct xs ys

/-- **Headline.**  The honest bundle: (1) the fuel-free program `addH` IS the relational hylomorphism
    of the measured coalgebra `c` with algebra `[id, (· :: ·)]` (`add_emerges`); and (2) it preserves
    value — the number denoted by the output digit list is the sum of the two inputs' values
    (`addH_value`, carried across from `LC2.add_correct`, NOT re-proved).  The certified program is the
    fuel-free O(n+m) `addH`, not the fuelled `addFuel`. -/
theorem add_derived_correct :
    ((graph addH : (⟨Int × List Int × List Int⟩ : RelSet.{0}) ⟶ ⟨List Int⟩)
      = Hylo.hyloR c μ hdec id (· :: ·))
    ∧ (∀ xs ys : List Int, LC2.value (addH (0, xs, ys)) = LC2.value xs + LC2.value ys) :=
  ⟨add_emerges, addH_value⟩

/-! ## Running the certified program

  `addH` is well-founded-recursive, so `decide` does not reduce it directly; through `addH_eq_addFn`
  the examples reduce to the kernel-reducible fuelled `LC2.addFn`. -/

example : addH (0, ([2, 4, 3] : List Int), [5, 6, 4]) = [7, 0, 8] := by
  rw [addH_eq_addFn]; decide
example : addH (0, ([9, 9] : List Int), [1]) = [0, 0, 1] := by
  rw [addH_eq_addFn]; decide

end Freyd.Alg.RelSet.LC2D
