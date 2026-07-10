/-
  LeetCode 231 — Power of Two — DERIVED as a relational HYLOMORPHISM (O(log n)).

  `leet/L231.lean` decides the property by `pow2Fuel fuel m`, recursing on a separate FUEL
  argument (`Fredy/leetcode.md` S13) rather than on `m` itself, because `m / 2` is a second,
  independently-shrinking argument and so does not compile to plain structural recursion.  Fuel is
  scaffolding, not the algorithm: the real halving descent is well-founded on `m` alone (`m / 2 <
  m` for `m ≠ 0`), which is exactly a RECURSIVE COALGEBRA `c : S → L + E×S` in the sense of
  `Hylo.hyloFold_unique` (`AOP/A6_GenHylo.lean`) — the dual of the fold-uniqueness laws, for a
  well-founded unfold-then-fold rather than a structural fold.  This file kills the fuel: `pow2WF`
  recurses on `m` directly (Lean's own well-founded recursion, measure `m`), and is shown to BE the
  hylomorphism of the halving coalgebra.

  Instantiation:  `S := Nat`, `L := Bool` (the leaf carries the decision), `E := Unit` (a halving
  step carries no data of its own), `C := Bool`.
    * coalgebra `c m` — leaf `.inl true` at `m = 1` (accept); leaf `.inl false` at `m = 0` or `m`
      odd `> 1` (reject); otherwise (`m` even, `> 0`) node `.inr ((), m / 2)` (halve and recurse) —
      branch order matching `pow2WF`'s own recursion exactly;
    * measure `μ := id`, dropping on every `.inr` step since `m / 2 < m` for `m ≠ 0` (`hdec`);
    * algebra base `g := id` (a leaf's decision passes through unchanged), step `st := fun _ r => r`
      (a halving step does not touch the decision, it only descends to it).

  `pow2WF_emerges` runs `hyloFold_unique` on the hand-written O(log n) `pow2WF`: it certifies that
  the fuel-free program IS the relational hylomorphism of `c` — the program was never rewritten,
  only shown to satisfy the hylomorphism recurrence (case split on `pow2WF`'s own equation lemmas,
  discharged in place, matching `LC231.pow2Fuel`'s branch order).

  Correctness is REUSED, not re-proved: the only new content is `pow2Fuel_ge`, a technical bridge
  between the two RECURSION SCHEMES (fuel vs. measure) — "fuel `≥ m - 1` already suffices" — proved
  by strong induction on `m` and reusing `LC231.pow2Fuel_one` for the `m = 1` base case.  It is NOT
  a re-derivation of the power-of-two characterization.  Once `isPow2WF` (the `Int`-level function,
  guarding sign like `LC231.isPow2Fn`) is shown to equal `LC231.isPow2Fn` via this bridge,
  `isPow2WF_correct` is `LC231.pow2_correct` verbatim, composed through the equality.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenHylo
import leet.L231

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC231D

open Freyd

/-! ## The fuel-free halving decision: well-founded recursion directly on `m` -/

/-- **The program, fuel killed.**  Recurse on `m` itself (Lean's well-founded recursion, measure
    `m`), not on a separate fuel counter: `m = 0` rejects, `m = 1` accepts, `m + 2` (i.e. `m ≥ 2`)
    halves and recurses when even, else rejects.  Branch order matches `LC231.pow2Fuel` exactly. -/
def pow2WF : Nat → Bool
  | 0 => false
  | 1 => true
  | (m + 2) => if (m + 2) % 2 = 0 then pow2WF ((m + 2) / 2) else false
  termination_by n => n
  decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The defining equation at `0` — well-founded recursion, needs the auto-generated equation lemma
    (cf. `L338`'s `popcount`; a bare `simp [pow2WF]` risks looping on the recursive clause). -/
theorem pow2WF_zero : pow2WF 0 = false := pow2WF.eq_1

/-- The defining equation at `1`. -/
theorem pow2WF_one : pow2WF 1 = true := pow2WF.eq_2

/-- The defining equation at `m + 2` (i.e. every `m ≥ 2`). -/
theorem pow2WF_succ_succ (m : Nat) :
    pow2WF (m + 2) = if (m + 2) % 2 = 0 then pow2WF ((m + 2) / 2) else false :=
  pow2WF.eq_3 m

/-! ## The halving coalgebra -/

/-- The halving coalgebra: leaf `true` at `1`, leaf `false` at `0` or odd `> 1`, otherwise node
    `((), m / 2)`.  Branch order matches `pow2WF`'s own recursion exactly. -/
def c : Nat → Sum Bool (Unit × Nat)
  | 0 => Sum.inl false
  | 1 => Sum.inl true
  | (m + 2) => if (m + 2) % 2 = 0 then Sum.inr ((), (m + 2) / 2) else Sum.inl false

/-- The measure: `m` itself. -/
def μ : Nat → Nat := id

/-- Every `.inr` step halves, and halving a nonzero `m` strictly decreases it. -/
theorem hdec : ∀ s e s', c s = Sum.inr (e, s') → μ s' < μ s := by
  intro s e s' h
  match s with
  | 0 => simp only [c] at h; nomatch h
  | 1 => simp only [c] at h; nomatch h
  | (m + 2) =>
      simp only [c] at h
      split at h
      · rename_i heven
        injection h with h1; injection h1 with h2 h3; subst h3
        simp only [μ, id]; exact Nat.div_lt_self (by omega) (by omega)
      · nomatch h

/-! ## `pow2WF` EMERGES as the relational hylomorphism -/

/-- **The derivation.**  The hand-written O(log n) halving decision `pow2WF` IS the relational
    hylomorphism of the measured coalgebra `c` with algebra `[id, fun _ r => r]` — it was never
    rewritten, only shown to satisfy the hylomorphism recurrence (a case split on `pow2WF`'s own
    equation lemmas, matching `c`'s branches). -/
theorem pow2WF_emerges :
    (graph pow2WF : (⟨Nat⟩ : RelSet.{0}) ⟶ ⟨Bool⟩) = Hylo.hyloR c μ hdec id (fun _ r => r) :=
  Hylo.hyloFold_unique c μ hdec id (fun _ r => r) pow2WF (by
    intro s
    match s with
    | 0 => simp only [c, pow2WF_zero]; rfl
    | 1 => simp only [c, pow2WF_one]; rfl
    | (m + 2) =>
        simp only [c, pow2WF_succ_succ]
        split
        · rfl
        · rfl)

/-! ## Bridge: `pow2WF` agrees with `LC231.pow2Fuel` once fuel is sufficient

  A technical fact about the two RECURSION SCHEMES (fuel-counted vs. measure-well-founded), not a
  re-derivation of the power-of-two math: fuel `≥ m - 1` (i.e. `m ≤ fuel + 1`) already suffices for
  `LC231.pow2Fuel` to agree with `pow2WF`, by strong induction on `m`. -/

theorem pow2Fuel_ge : ∀ m fuel, m ≤ fuel + 1 → LC231.pow2Fuel fuel m = pow2WF m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    match m with
    | 0 =>
        intro fuel _
        rw [pow2WF_zero]
        cases fuel with
        | zero => rfl
        | succ f => simp [LC231.pow2Fuel]
    | 1 =>
        intro fuel _
        rw [pow2WF_one]
        exact LC231.pow2Fuel_one fuel
    | (m' + 2) =>
        intro fuel hfuel
        rw [pow2WF_succ_succ]
        have hfpos : 1 ≤ fuel := by omega
        obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := by
          cases fuel with
          | zero => exact False.elim (by omega)
          | succ f => exact ⟨f, rfl⟩
        have hne1 : m' + 2 ≠ 1 := by omega
        have hne0 : m' + 2 ≠ 0 := by omega
        have hstep : LC231.pow2Fuel (fuel' + 1) (m' + 2)
            = if (m' + 2) % 2 = 0 then LC231.pow2Fuel fuel' ((m' + 2) / 2) else false := by
          simp only [LC231.pow2Fuel, if_neg hne1, if_neg hne0]
        rw [hstep]
        split
        · rename_i heven
          have hhalf : (m' + 2) / 2 < m' + 2 := Nat.div_lt_self (by omega) (by omega)
          have hhalf_fuel : (m' + 2) / 2 ≤ fuel' + 1 := by omega
          exact ih ((m' + 2) / 2) hhalf fuel' hhalf_fuel
        · rfl

/-! ## `isPow2WF`: the `Int`-level function, guarding sign exactly like `LC231.isPow2Fn` -/

/-- **The certified `Int`-level decision.**  Guard the sign once, at the `Int` boundary — exactly
    `LC231.isPow2Fn`'s own shape — and call the fuel-free `pow2WF` for the halving descent. -/
def isPow2WF (n : Int) : Bool :=
  if n ≤ 0 then false else pow2WF n.toNat

/-- `isPow2WF` agrees with `LC231.isPow2Fn` pointwise, via `pow2Fuel_ge` at the sufficient fuel
    `n.toNat` (trivially `n.toNat ≤ n.toNat + 1`). -/
theorem isPow2WF_eq_isPow2Fn (n : Int) : isPow2WF n = LC231.isPow2Fn n := by
  unfold isPow2WF LC231.isPow2Fn
  by_cases hn : n ≤ 0
  · rw [if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn]
    exact (pow2Fuel_ge n.toNat n.toNat (by omega)).symm

/-- **Correctness, reused verbatim from `LC231.pow2_correct`** through `isPow2WF_eq_isPow2Fn`: `n`
    is a power of two iff `0 < n` and `n = 2 ^ k` for some `k` — LeetCode 231's definition, exactly
    as in `LC231.pow2_correct`, now certified for the O(log n) fuel-free program. -/
theorem isPow2WF_correct (n : Int) :
    isPow2WF n = true ↔ (0 < n ∧ ∃ k : Nat, n = (2 : Int) ^ k) := by
  rw [isPow2WF_eq_isPow2Fn]
  exact LC231.pow2_correct n

/-- **Headline.**  The honest bundle: (1) the hand-written O(log n) halving decision `pow2WF` IS
    the relational hylomorphism of the measured coalgebra `c` with algebra `[id, fun _ r => r]`
    (`pow2WF_emerges`); and (2) the `Int`-level wrapper `isPow2WF` decides the power-of-two
    property (`isPow2WF_correct`), reused from `LC231.pow2_correct` through the fuel/measure
    bridge — the power-of-two math is never re-derived. -/
theorem pow2WF_derived_correct :
    ((graph pow2WF : (⟨Nat⟩ : RelSet.{0}) ⟶ ⟨Bool⟩) = Hylo.hyloR c μ hdec id (fun _ r => r))
      ∧ (∀ n : Int, isPow2WF n = true ↔ (0 < n ∧ ∃ k : Nat, n = (2 : Int) ^ k)) :=
  ⟨pow2WF_emerges, isPow2WF_correct⟩

/-! ## Running the certified program

  `pow2WF` is well-founded recursive (does not reduce under `decide`/`rfl` — cf. `L338`'s
  `popcount`); run examples through the fuel bridge `pow2Fuel_ge`, which lands on the structurally
  recursive (hence kernel-reducible) `LC231.pow2Fuel`. -/

example : isPow2WF 1 = true := by rw [isPow2WF_eq_isPow2Fn]; decide
example : isPow2WF 16 = true := by rw [isPow2WF_eq_isPow2Fn]; decide
example : isPow2WF 6 = false := by rw [isPow2WF_eq_isPow2Fn]; decide

end Freyd.Alg.RelSet.LC231D
