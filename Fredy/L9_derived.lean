/-
  LeetCode 9 — Palindrome Number — DERIVED as a relational HYLOMORPHISM (fuel-free).

  `Fredy/L9.lean` extracts the digit sequence with a FUEL-guarded value-recursion,
  `toDigitsFuel fuel n`, because peeling `n / 10` decreases `n` but Lean's plain structural
  recursion has no handle on that — the fuel `n + 1` is supplied only to satisfy totality, and a
  side theorem ("fuel `n+1` is always enough") is folklore baked into the docstring, never stated.

  The right scheme for "peel while a `Nat` measure shrinks" is a RECURSIVE COALGEBRA
  `c : S → L + E×S` whose unfolding is well-founded, witnessed by a `Nat` measure `μ` that
  strictly drops on every `.inr` step, re-folded with an algebra `[g, st]`.
  `Hylo.hyloFold_unique` (`Fredy/A6_GenHylo.lean`) is the uniqueness law: any function `h`
  obeying `h s = match c s with | inl l => g l | inr (e,s') => st e (h s')` IS the hylomorphism
  `hyloR c μ hdec g st`.  Applied here, `μ := id` (the number `s` itself) replaces the fuel
  parameter outright: `s / 10 < s` for `s ≥ 1` is exactly `hdec`, so termination needs no
  externally-threaded budget at all.

  Instantiation:  `S := Nat`, `L := Unit`, `E := Nat`, `C := List Nat`.
    * coalgebra  `c s` — leaf `.inl ()` at `s = 0`; else `.inr (s % 10, s / 10)` (peel the last
      digit, recurse on the rest);
    * measure    `μ := id`, dropping on every `.inr` step since `s / 10 < s` for `s ≥ 1` (`hdec`);
    * algebra    base `g := fun _ => []` (leaf `0` contributes no digit), step `st := (· :: ·)`
      (cons the peeled digit onto the tail's digits).

  `digits_emerges` runs `hyloFold_unique` on the hand-written `digitsWF` (peeling by
  well-founded recursion on `s` itself, no fuel): it certifies `digitsWF` IS the relational
  hylomorphism of `c` — the program was never re-written, only shown to satisfy the recurrence
  (one case split on `s`, discharged in place — the law's wrinkle: never pass a separately-proved
  recurrence lemma AS `hyloFold_unique`'s `hstep` argument, it fails on a matcher-aux `isDefEq`
  mismatch; `refine … ?_` and unfold in place instead).

  `digitsWF` agrees with `LC9.toDigits` for every `n ≠ 0` (`digitsWF_eq_toDigits`, by one strong
  induction generalized over an ABSTRACT sufficient fuel — the induction itself IS the "fuel `n+1`
  is always enough" argument the original file left as folklore).  At `n = 0` the two digit lists
  differ AS LISTS (`[]` vs `[0]`) but both are trivially self-reverse, so the palindrome DECISION
  built on `digitsWF` (`isPalinNumFnWF`) agrees with `LC9.isPalinNumFn` for every `n`
  (`isPalinNumFnWF_eq`).  Correctness (`LC9.palin_correct`: the honest digit-palindrome `iff`) is
  REUSED through that bridge, not re-proved (`palin_derived_correct`) — headline shape 3
  (decision `iff`).  Complexity: O(#digits) — one measured pass, same order as the fuel version,
  but the fuel parameter and its "always enough" folklore are gone, replaced by one proven law.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenHylo
import Fredy.L9

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC9D

open Freyd Freyd.Alg.RelSet.LC9

/-! ## Digit-peeling as a measured recursive coalgebra (kills the fuel parameter) -/

/-- The digit-peeling coalgebra: leaf at `0`, otherwise peel the last digit `s % 10` and recurse
    on `s / 10`.  Unlike `LC9.toDigitsFuel`, there is no fuel budget — well-foundedness of the
    unfolding is witnessed directly by the measure `μ := id`, which strictly decreases on the
    `.inr` branch (`hdec`). -/
def c : Nat → Sum Unit (Nat × Nat)
  | 0 => Sum.inl ()
  | n + 1 => Sum.inr ((n + 1) % 10, (n + 1) / 10)

/-- The measure: `s` itself. -/
def μ : Nat → Nat := id

/-- Every `.inr` step strictly decreases the measure, since `s / 10 < s` for `s ≥ 1`. -/
theorem hdec : ∀ s e s', c s = Sum.inr (e, s') → μ s' < μ s := by
  intro s e s' h
  cases s with
  | zero => simp only [c] at h; nomatch h
  | succ n =>
      simp only [c] at h
      injection h with h1
      injection h1 with h2 h3
      subst h3
      simp only [μ, id]
      omega

/-! ## The well-founded digit function (no fuel) -/

/-- Digit-peeling by well-founded recursion on `s` itself — the fuel parameter of
    `LC9.toDigitsFuel` is gone; the same measure `μ = id` that proves `hdec` also proves
    termination here. -/
def digitsWF : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) % 10 :: digitsWF ((n + 1) / 10)
termination_by s => s
decreasing_by omega

/-- **Emergence.**  `digitsWF` IS the relational hylomorphism of the measured coalgebra `c` with
    algebra `[fun _ => [], (· :: ·)]` — it was never re-derived as a hylomorphism by hand; the
    goal below is exactly "`digitsWF` obeys the hylomorphism recurrence for `c`", discharged in
    place by case analysis (per the `hyloFold_unique` law wrinkle: never pass a separately-proved
    recurrence lemma AS the `hstep` argument — `refine … ?_` and unfold `digitsWF`/`c` in place). -/
theorem digits_emerges :
    (graph digitsWF : (⟨Nat⟩ : RelSet.{0}) ⟶ ⟨List Nat⟩)
      = Hylo.hyloR c μ hdec (fun _ => ([] : List Nat)) (· :: ·) := by
  refine Hylo.hyloFold_unique c μ hdec (fun _ => ([] : List Nat)) (· :: ·) digitsWF ?_
  intro s
  cases s with
  | zero => simp only [digitsWF, c]
  | succ n => simp only [digitsWF, c]

/-! ## Bridge: `digitsWF` computes `LC9.toDigits`'s digits, for `n ≠ 0`

  `LC9.toDigits n = LC9.toDigitsFuel (n+1) n` and `digitsWF` agree on every `n ≥ 1` — both peel
  `n % 10` and recurse into `n / 10`; the ONLY structural difference is that `LC9.toDigitsFuel`
  stops one layer earlier (as soon as the remaining value is `< 10`, returning it as a singleton
  leaf) while `digitsWF` stops exactly at `0` (returning `[]`), so a single-digit `n` still lands
  on the same list either way: `digitsWF n = n :: digitsWF 0 = [n] = LC9.toDigits n`.  At `n = 0`
  the two disagree as LISTS (`digitsWF 0 = []` vs `LC9.toDigits 0 = [0]`), but both are trivially
  self-reverse, so the disagreement never reaches the palindrome DECISION (`check_eq` below). -/

/-- `digitsWF n` computes the SAME digit list as `LC9.toDigitsFuel fuel n` for any sufficient
    fuel (`n ≤ fuel`) and any `n ≠ 0` — this single strong induction is what "killing the fuel
    parameter" means: the well-founded recursion on `n` itself replaces the whole
    fuel-sufficiency argument (the fuel `f` stays an opaque variable throughout, so `simp` never
    over-unfolds a second layer). -/
theorem digitsWF_eq_toDigitsFuel :
    ∀ n fuel, n ≤ fuel → n ≠ 0 → digitsWF n = toDigitsFuel fuel n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro fuel hfuel hn0
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases hn : m + 1 < 10
    · have h0 : (m + 1) / 10 = 0 := by omega
      simp only [digitsWF, toDigitsFuel, h0, hn, if_true]
      congr 1
      omega
    · have hIH : digitsWF ((m + 1) / 10) = toDigitsFuel f ((m + 1) / 10) :=
        IH ((m + 1) / 10) (by omega) f (by omega) (by omega)
      simp only [digitsWF, toDigitsFuel, hn, if_false]
      rw [hIH]

/-- `digitsWF` agrees with `LC9.toDigits` on every nonzero input — the bridge specialization at
    the "always enough" fuel `n + 1` (`LC9.toDigits n := toDigitsFuel (n+1) n`). -/
theorem digitsWF_eq_toDigits (n : Nat) (hn0 : n ≠ 0) : digitsWF n = toDigits n :=
  digitsWF_eq_toDigitsFuel n (n + 1) (by omega) hn0

/-! ## The certified decision procedure and its correctness

  The self-reversal check on `digitsWF` decides the SAME palindrome property as `LC9.isPalinNumFn`
  (built on `toDigits`).  At `n = 0` the two digit lists disagree (`[]` vs `[0]`) but both are
  trivially self-reverse, so the DECISION agrees for every `n`, not just `n ≠ 0`. -/

/-- The palindrome decision, recomputed on `digitsWF` — no fuel parameter anywhere. -/
def isPalinNumFnWF (n : Int) : Bool :=
  if n < 0 then false else decide (digitsWF n.toNat = (digitsWF n.toNat).reverse)

/-- `digitsWF`'s self-reversal check agrees with `toDigits`'s, for every `m : Nat` — at `m = 0`
    both sides compute directly (`[] = [].reverse` and `[0] = [0].reverse`, both `true`); for
    `m ≠ 0` the lists are literally equal (`digitsWF_eq_toDigits`), so the checks agree trivially. -/
theorem check_eq (m : Nat) :
    decide (digitsWF m = (digitsWF m).reverse) = decide (toDigits m = (toDigits m).reverse) := by
  rcases m with _ | m
  · simp [digitsWF, toDigits, toDigitsFuel]
  · rw [digitsWF_eq_toDigits (m + 1) (by omega)]

/-- `isPalinNumFnWF` is `LC9.isPalinNumFn`, computed without ever running a fuel-guarded
    recursion — the fuel-free hylomorphism `digitsWF` decides the identical Boolean. -/
theorem isPalinNumFnWF_eq (n : Int) : isPalinNumFnWF n = isPalinNumFn n := by
  unfold isPalinNumFnWF isPalinNumFn
  by_cases hn : n < 0
  · simp only [if_pos hn]
  · simp only [if_neg hn, check_eq n.toNat]

/-- **Headline.**  The fuel-free decision procedure `isPalinNumFnWF` — built from `digitsWF`, the
    program that EMERGED as `Hylo.hyloR c μ hdec (fun _ => []) (· :: ·)` (`digits_emerges`) —
    decides the honest digit-palindrome property: correctness is REUSED from `LC9.palin_correct`
    through `isPalinNumFnWF_eq`, not re-proved. -/
theorem palin_derived_correct (n : Int) :
    isPalinNumFnWF n = true ↔ (0 ≤ n ∧ toDigits n.toNat = (toDigits n.toNat).reverse) := by
  rw [isPalinNumFnWF_eq]
  exact palin_correct n

/-! ## Running the certified program -/

example : isPalinNumFnWF 121 = true := by rw [isPalinNumFnWF_eq]; decide
example : isPalinNumFnWF (-121) = false := by rw [isPalinNumFnWF_eq]; decide
example : isPalinNumFnWF 10 = false := by rw [isPalinNumFnWF_eq]; decide
example : isPalinNumFnWF 0 = true := by rw [isPalinNumFnWF_eq]; decide

end Freyd.Alg.RelSet.LC9D
