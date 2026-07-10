/-
  LeetCode 367 — Valid Perfect Square — DERIVED as a relational HYLOMORPHISM (O(√n)).

  `Fredy/L367.lean` writes `sqFuel` as a FUEL-indexed upward search: search from `k = 0`,
  incrementing `k` while `k*k < n`, with a fuel budget of `n + 1` steps supplied so the definition
  stays *structural* on the fuel (kernel-reducible, `decide`-friendly).  The fuel is a SUFFICIENT
  bound, not an exact one (contrast `L21`'s merge, whose fuel spend is exact) — the search always
  terminates well before the fuel runs out, in genuinely `O(√n)` steps, but the definition still
  carries the bookkeeping.

  The right scheme to drop the fuel is the DUAL of a fold: a RECURSIVE COALGEBRA `c : S → L + E×S`
  whose unfolding is well-founded, witnessed by a `Nat` measure `μ` that strictly decreases on
  every recursive step (`Hylo.hyloFold_unique`, `Fredy/A6_GenHylo.lean` — the law `L21_derived`
  already exercises on 2-way merge).  Here the state is the search candidate itself:

    * state      `S := Nat` (the candidate root `k`; `n` is a fixed outer parameter, one coalgebra
      instance per `n`, exactly as `sqFuel`'s search runs against one fixed `n`);
    * measure    `μ n k := (n + 1) - k`, the same fuel bound `sqFuel` uses, but now read as a
      well-founded DECREASE rather than threaded fuel;
    * coalgebra  `c n k` — leaf `.inl (decide (k*k = n))` once `k*k ≥ n` (the search has reached or
      passed the root, so the leaf decides on the spot), else node `.inr ((), k+1)` (recurse
      upward, no payload beyond "keep going");
    * algebra    base `g := id` (the leaf's decision passes straight through), step `st _ b := b`
      (no accumulation — the answer is just whatever the recursive call found).

  `search_emerges` runs `hyloFold_unique` on `search` (defined here by ordinary Lean well-founded
  recursion on `μ`, NOT re-derived from `sqFuel`): it certifies `search n` IS the relational
  hylomorphism of `c n` with algebra `[id, fun _ b => b]` — `search` was never hand-verified against
  the coalgebra by induction, only shown to satisfy the hylomorphism recurrence, discharged in place
  (one `search.eq_1`/`c` unfold, one `dite`/`match` split).

  Correctness is REUSED, not re-proved: `sqFuel_eq_search` bridges the fuel-based and fuel-free
  searches (both walk the SAME sequence of candidates `0, 1, 2, …`, so `sqFuel`'s "enough fuel"
  hypothesis transfers to `search` by one induction on the fuel), giving `search n 0 =
  isPerfectSquareFn n`.  Composed with `LC367.perfectSquare_correct`, this yields the headline
  decision `search n 0 = true ↔ ∃ k, k*k = n` with NO re-derivation of the search's soundness or
  completeness arguments.

  Complexity: `O(√n)` — the coalgebra recurses only while `k*k < n`, i.e. exactly `⌈√n⌉ + 1`
  candidates, same asymptotic class as `sqFuel` itself (the fuel was already slack, never the
  bottleneck).  An `O(log n)` monotone-predicate BINARY search on `Nat` would need new infra (a
  general "binary search for the least `k` with a monotone `Bool` predicate" law) — OUT OF SCOPE
  here; this derivation only removes the fuel, it does not change the search strategy.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenHylo
import Fredy.L367

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC367D

open Freyd

/-! ## The upward search, fuel-free, by well-founded recursion on `μ n k := (n+1) - k` -/

/-- `search n k` — search upward from `k` for a root of `n`: recurse to `k+1` while `k*k < n`,
    else decide on the spot.  The `dite` keeps the guard `h : k*k < n` in scope for the
    `decreasing_by` termination proof. -/
def search (n : Nat) : Nat → Bool
  | k => if h : k * k < n then search n (k + 1) else decide (k * k = n)
  termination_by k => n + 1 - k
  decreasing_by
    rename_i h
    have hkn : k ≤ n := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · omega
      · have hle : k ≤ k * k := Nat.le_mul_of_pos_right k hpos
        omega
    omega

/-! ## The measured recursive coalgebra: one instance per fixed `n` -/

/-- The search coalgebra for a fixed `n`: leaf once `k*k ≥ n` (the decision `k*k = n`), else
    recurse to `k+1`.  Mirrors `search`'s `dite` exactly, non-dependently (no payload beyond
    `k+1`). -/
def c (n : Nat) : Nat → Sum Bool (Unit × Nat) :=
  fun k => if k * k < n then Sum.inr ((), k + 1) else Sum.inl (decide (k * k = n))

/-- The measure: `sqFuel`'s own fuel bound, `(n+1) - k`, read as a well-founded decrease. -/
def μ (n : Nat) : Nat → Nat := fun k => n + 1 - k

/-- Every `.inr` step strictly decreases `μ n`: `k*k < n` forces `k ≤ n` (`Nat.le_mul_of_pos_right`
    gives `k ≤ k*k` when `k > 0`; trivial at `k = 0`), so `(n+1)-(k+1) < (n+1)-k`. -/
theorem hdec (n : Nat) : ∀ k e k', c n k = Sum.inr (e, k') → μ n k' < μ n k := by
  intro k e k' h
  simp only [c] at h
  split at h
  case isTrue hlt =>
    injection h with h1
    injection h1 with h2 h3
    subst h3
    have hkn : k ≤ n := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · omega
      · have hle : k ≤ k * k := Nat.le_mul_of_pos_right k hpos
        omega
    simp only [μ]
    omega
  case isFalse hnlt => nomatch h

/-! ## `search` EMERGES as the relational hylomorphism -/

/-- **The derivation.**  `search n` (the fuel-free upward search) IS the relational hylomorphism of
    the measured coalgebra `c n` with algebra `[id, fun _ b => b]` — it was never re-written as a
    hylomorphism; `hyloFold_unique` certifies that it satisfies the hylomorphism recurrence, by
    unfolding `search`'s own equation (`search.eq_1`) and splitting on the shared guard `k*k < n`. -/
theorem search_emerges (n : Nat) :
    (graph (search n) : (⟨Nat⟩ : RelSet.{0}) ⟶ ⟨Bool⟩)
      = Hylo.hyloR (c n) (μ n) (hdec n) id (fun (_ : Unit) (b : Bool) => b) := by
  refine Hylo.hyloFold_unique (c n) (μ n) (hdec n) id (fun (_ : Unit) (b : Bool) => b)
    (search n) ?_
  intro k
  rw [search.eq_1]
  simp only [c]
  split
  · rfl
  · rfl

/-! ## Correctness carries over from `L367.lean` (no re-proof of soundness/completeness) -/

/-- **Bridge**: for sufficient fuel (`μ n k ≤ fuel`), `sqFuel` and `search` agree — both walk the
    SAME candidate sequence `k, k+1, k+2, …`, `sqFuel`'s three-way split (`=`, `>`, recurse)
    collapsing into `search`'s two-way split (`decide (k*k=n)` covers both `=` and `>`).  By
    induction on `fuel`. -/
theorem sqFuel_eq_search (n : Nat) :
    ∀ fuel k, μ n k ≤ fuel → LC367.sqFuel fuel k n = search n k := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hb
    have hkn : n < k := by simp only [μ] at hb; omega
    have hnotlt : ¬ k * k < n := by
      have hle : k ≤ k * k := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · omega
        · exact Nat.le_mul_of_pos_right k hpos
      omega
    show decide (k * k = n) = search n k
    rw [search.eq_1, dif_neg hnotlt]
  | succ fuel ih =>
    intro k hb
    show (if k * k = n then true else if k * k > n then false else LC367.sqFuel fuel (k + 1) n)
        = search n k
    by_cases heq : k * k = n
    · rw [if_pos heq, search.eq_1, dif_neg (by omega : ¬ k * k < n)]
      simp [heq]
    · by_cases hgt : k * k > n
      · rw [if_neg heq, if_pos hgt, search.eq_1, dif_neg (by omega : ¬ k * k < n)]
        simp [heq]
      · have hlt : k * k < n := by omega
        rw [if_neg heq, if_neg hgt, search.eq_1, dif_pos hlt]
        have hkn : k ≤ n := by
          rcases Nat.eq_zero_or_pos k with h0 | hpos
          · omega
          · have hle : k ≤ k * k := Nat.le_mul_of_pos_right k hpos
            omega
        have hbound' : μ n (k + 1) ≤ fuel := by simp only [μ] at hb ⊢; omega
        exact ih (k + 1) hbound'

/-- `search`'s answer at the start (`k = 0`) equals the original solved program
    `LC367.isPerfectSquareFn`. -/
theorem search_eq_isPerfectSquareFn (n : Nat) : search n 0 = LC367.isPerfectSquareFn n := by
  have hb : μ n 0 ≤ n + 1 := by simp only [μ]; omega
  exact (sqFuel_eq_search n (n + 1) 0 hb).symm

/-- **Headline** (decision `iff`, shape 3): `search`'s verdict at `k = 0` is `true` iff `n` is a
    perfect square — REUSED from `LC367.perfectSquare_correct` via `search_eq_isPerfectSquareFn`,
    no re-derivation of soundness/completeness. -/
theorem search_correct (n : Nat) : search n 0 = true ↔ ∃ k, k * k = n := by
  rw [search_eq_isPerfectSquareFn]
  exact LC367.perfectSquare_correct n

/-- **Bundle**: `search n` is both the relational hylomorphism of the measured coalgebra `c n`
    (`search_emerges`) and, at `k = 0`, the correct decision (`search_correct`). -/
theorem search_derived_correct (n : Nat) :
    ((graph (search n) : (⟨Nat⟩ : RelSet.{0}) ⟶ ⟨Bool⟩)
        = Hylo.hyloR (c n) (μ n) (hdec n) id (fun (_ : Unit) (b : Bool) => b))
      ∧ (search n 0 = true ↔ ∃ k, k * k = n) :=
  ⟨search_emerges n, search_correct n⟩

/-! ## Running the certified program -/

example : search 16 0 = true := by rw [search_eq_isPerfectSquareFn]; decide
example : search 14 0 = false := by rw [search_eq_isPerfectSquareFn]; decide
example : search 1 0 = true := by rw [search_eq_isPerfectSquareFn]; decide

end Freyd.Alg.RelSet.LC367D
