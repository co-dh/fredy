/-
  LeetCode 322 — Coin Change — DERIVED as a TABULATING DP over the AMOUNT axis.

  `Fredy/L322.lean` computes Coin Change with a FUEL recursion whose body folds `omin` over the
  COIN list (`coinFold`), the fuel structurally decreasing on each recursive amount.  That fold is
  written by hand and verified.  This file instead makes the DP *table* `dp[0..amount]` EMERGE
  from the general-carrier fold-uniqueness law `Freyd.Alg.RelSet.SL.snocFold_unique`
  (`Fredy/A6_GenFold.lean`), with carrier `C := List (Option Nat)` — a course-of-values fold
  whose step reads the WHOLE table of previous results.

  The amount axis `0, 1, …, amount` is `SnocList Unit Unit ≅ ℕ` (`SL.snocs`/`SL.natOf`,
  `Fredy/A6_8_Tupling.lean`), so tabulating over amounts is a snoc-fold with `L = E = Unit`.  The
  carried value is the table `T = [dp[0], …, dp[a]]`; its length is the next amount to fill, and
  the step appends `dp[a+1] = omin over coins c (1 ≤ c ≤ a+1) of osucc (T[a+1-c])` — the coin set
  captured as a closure parameter `coins`.

    * base  `g coins ()      = [some 0]`                                       (dp[0] = 0 coins)
    * step  `st coins T ()   = T ++ [coinFold (nth T) T.length coins]`         (append dp[T.length])

  Feeding `g`/`st`/`tab` to `snocFold_unique` PRODUCES the tabulating fold as
  `cataR (scalarAlg g st)` — the fold is never written by hand; it is the law's catamorphism
  (`fold_derived`).  Correctness (`tab_derived_correct`) is RE-PROVED here — the fuel proof of
  `L322.lean` does not transfer, because this fold recurses over the amount axis with a course-of-
  values step, not over fuel.  The re-proof reuses `L322`'s per-level `omin`-fold lemmas
  (`coinFold_achieves`/`coinFold_dominates`) and the `Achievable`-successor structure
  (`achievable_succ_iff`), abstracting the fuel proof's successor step over an arbitrary table-
  reading `step` (`coinFold_spec`), then running a bounded strong induction over amounts.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.L322
import Fredy.L322_dp   -- reuse the A9_2-derived Coin-Change optimality (solve_correct_inf)

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC322D

open Freyd Freyd.Alg.RelSet.SL

/-! ## Reading the DP table -/

/-- Index into a table of answers, `none` if out of range (never happens for a valid amount, since
    the step at amount `a+1` reads only indices `a+1-c ≤ a < a+1 = T.length`). -/
def nth : List (Option Nat) → Nat → Option Nat
  | [], _ => none
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nth xs n

/-- Reading below the appended cell is unaffected by the append. -/
theorem nth_append_lt :
    ∀ (T : List (Option Nat)) (x : Option Nat) (j : Nat),
      j < T.length → nth (T ++ [x]) j = nth T j := by
  intro T
  induction T with
  | nil => intro x j hj; exact absurd hj (Nat.not_lt_zero j)
  | cons y ys ih =>
    intro x j hj
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j + 1 < ys.length + 1 := hj
      exact ih x j (Nat.lt_of_succ_lt_succ hj')

/-- Reading the appended cell (at index `= T.length`) returns it. -/
theorem nth_append_length :
    ∀ (T : List (Option Nat)) (x : Option Nat), nth (T ++ [x]) T.length = x := by
  intro T
  induction T with
  | nil => intro x; rfl
  | cons y ys ih => intro x; exact ih x

/-! ## The emergent algebra (base `g`, step `st`) and the tabulating fold `tab`

  `g`/`st` are the base/step of the scalar algebra fed to `snocFold_unique`; `tab` is defined FROM
  them, so `snocFold_unique`'s two hypotheses hold by `rfl` (as in `L70_derived`/`L198_derived`). -/

/-- Base: the amount-0 table `[dp[0]] = [some 0]`. -/
def g (coins : SnocList Nat Nat) : Unit → List (Option Nat) := fun _ => [some 0]

/-- Step: append `dp[a+1]` where `a+1 = T.length`; `coinFold (nth T) T.length coins` folds `omin`
    over every denomination, contributing `osucc (T[a+1-c])` for each valid coin `c`. -/
def st (coins : SnocList Nat Nat) : List (Option Nat) → Unit → List (Option Nat) :=
  fun T _ => T ++ [LC322.coinFold (nth T) T.length coins]

/-- The tabulating fold, defined FROM `g`/`st` so `snocFold_unique` applies. -/
def tab (coins : SnocList Nat Nat) : SnocList Unit Unit → List (Option Nat)
  | SnocList.wrap l => g coins l
  | SnocList.snoc xs e => st coins (tab coins xs) e

/-- **The derivation.**  The tabulating DP fold is PRODUCED by the general-carrier fold-uniqueness
    law — never written by hand: `graph (tab coins)` equals the catamorphism of the scalar algebra
    `scalarAlg (g coins) (st coins)`, carrier `List (Option Nat)`. -/
theorem fold_derived (coins : SnocList Nat Nat) :
    (graph (tab coins) : dSL Unit Unit ⟶ ⟨List (Option Nat)⟩)
      = cataR (scalarAlg (g coins) (st coins)) :=
  SL.snocFold_unique (g coins) (st coins) (tab coins) (fun _ => rfl) (fun _ _ => rfl)

/-! ## Table structure: length, prefix-stability, the successor recurrence -/

/-- The table for amounts `0..n` has `n+1` entries. -/
theorem tab_length (coins : SnocList Nat Nat) :
    ∀ n, (tab coins (snocs n)).length = n + 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (tab coins (snocs n)
          ++ [LC322.coinFold (nth (tab coins (snocs n))) (tab coins (snocs n)).length coins]).length
        = n + 1 + 1
    rw [List.length_append, List.length_cons, List.length_nil, ih]

/-- The canonical answer for amount `a`: the last entry of the amount-`a` table. -/
def entry (coins : SnocList Nat Nat) (a : Nat) : Option Nat := nth (tab coins (snocs a)) a

/-- The amount-`(a+1)` table's new entry: `coinFold` reading the amount-`a` table. -/
theorem entry_succ (coins : SnocList Nat Nat) (a : Nat) :
    entry coins (a + 1) = LC322.coinFold (nth (tab coins (snocs a))) (a + 1) coins := by
  have hlen : (tab coins (snocs a)).length = a + 1 := tab_length coins a
  show nth (tab coins (snocs a)
        ++ [LC322.coinFold (nth (tab coins (snocs a))) (tab coins (snocs a)).length coins]) (a + 1)
      = LC322.coinFold (nth (tab coins (snocs a))) (a + 1) coins
  rw [← hlen]
  exact nth_append_length _ _

/-- **Prefix-stability.**  Reading the amount-`a` table at any index `j ≤ a` gives the canonical
    entry for `j` — later appends never disturb earlier cells. -/
theorem stab (coins : SnocList Nat Nat) :
    ∀ a j, j ≤ a → nth (tab coins (snocs a)) j = entry coins j := by
  intro a
  induction a with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0; rfl
  | succ a ih =>
    intro j hj
    rcases Nat.lt_or_ge j (a + 1) with h | h
    · have hlen : (tab coins (snocs a)).length = a + 1 := tab_length coins a
      show nth (tab coins (snocs a)
            ++ [LC322.coinFold (nth (tab coins (snocs a))) (tab coins (snocs a)).length coins]) j
          = entry coins j
      rw [nth_append_lt _ _ j (by rw [hlen]; exact h)]
      exact ih j (by omega)
    · have hj' : j = a + 1 := by omega
      subst hj'; rfl

/-! ## `coinFold` congruence: it depends only on the step's values below `t` -/

/-- `contrib` reads `step` only at `t - c` (`< t` for a valid coin), so it respects step equality
    below `t`. -/
theorem contrib_congr {step1 step2 : Nat → Option Nat} {t : Nat}
    (hst : ∀ j, j < t → step1 j = step2 j) (c : Nat) :
    LC322.contrib step1 t c = LC322.contrib step2 t c := by
  unfold LC322.contrib
  by_cases h : 1 ≤ c ∧ c ≤ t
  · rw [if_pos h, if_pos h, hst (t - c) (by omega)]
  · rw [if_neg h, if_neg h]

/-- The `omin`-fold over the coin list depends only on the step's values below `t`. -/
theorem coinFold_congr {step1 step2 : Nat → Option Nat} {t : Nat}
    (hst : ∀ j, j < t → step1 j = step2 j) :
    ∀ cs, LC322.coinFold step1 t cs = LC322.coinFold step2 t cs
  | SnocList.wrap c => contrib_congr hst c
  | SnocList.snoc cs c => by
      show LC322.omin (LC322.coinFold step1 t cs) (LC322.contrib step1 t c)
          = LC322.omin (LC322.coinFold step2 t cs) (LC322.contrib step2 t c)
      rw [coinFold_congr hst cs, contrib_congr hst c]

/-- The successor recurrence over CANONICAL entries: reading the amount-`a` table equals reading
    `entry coins` (prefix-stability), so the emergent step is a genuine course-of-values fold. -/
theorem entry_succ_eq (coins : SnocList Nat Nat) (a : Nat) :
    entry coins (a + 1) = LC322.coinFold (entry coins) (a + 1) coins := by
  rw [entry_succ]
  exact coinFold_congr (fun j hj => stab coins a j (by omega)) coins

/-! ## Correctness via the ∞-DP theorem (no re-proof)

  The tabulating fold computes exactly `L322.dp`: both obey `f 0 = some 0` and
  `f (a+1) = coinFold f (a+1) coins`.  So its correctness is `L322.solve_correct_inf` — the
  Coin-Change optimality DERIVED from the abstract `A9_2.dynamic_programming_inf` — not re-proved
  here.  `entry_eq_dpFuel` is a plain computational induction on the fuel bound (no `Achievable`
  reasoning); the extremum content lives once, in the A-layer. -/

/-- The tabulating fold's `a`-th entry equals `L322`'s fuel DP at any sufficient fuel bound `N ≥ a`.
    Both obey `f 0 = some 0`, `f (a+1) = coinFold f (a+1) coins`, so they agree by induction on `N`
    (via `coinFold_congr`, which needs only agreement at the sub-amounts `< a+1`). -/
theorem entry_eq_dpFuel (coins : SnocList Nat Nat) :
    ∀ N a, a ≤ N → entry coins a = LC322.dpFuel coins N a := by
  intro N
  induction N with
  | zero => intro a ha; obtain rfl := Nat.le_zero.mp ha; rfl
  | succ N ih =>
    intro a ha
    match a, ha with
    | 0, _ => rfl
    | a' + 1, ha =>
      rw [entry_succ_eq]
      show LC322.coinFold (entry coins) (a' + 1) coins
          = LC322.coinFold (LC322.dpFuel coins N) (a' + 1) coins
      exact coinFold_congr (fun j hj => ih j (by omega)) coins

/-- The tabulating fold's `a`-th entry equals `L322.dp coins a` (= `solveFn`). -/
theorem entry_eq_dp (coins : SnocList Nat Nat) (a : Nat) : entry coins a = LC322.dp coins a :=
  entry_eq_dpFuel coins a a (Nat.le_refl a)

/-- Each table entry `entry coins a` is the `≤`-minimum achievable coin-count for amount `a`
    (`none` if unreachable) — `coinSpec coins a`.  REUSED from `L322.solve_correct_inf` (the
    `A9_2.dynamic_programming_inf`-derived optimality) through `entry_eq_dp`; no bounded strong
    induction, no `Achievable` re-analysis. -/
theorem entry_spec (coins : SnocList Nat Nat) (a : Nat) :
    LC322.coinSpec coins a (entry coins a) := by
  rw [entry_eq_dp coins a]; exact LC322.solve_correct_inf coins a

/-- **Headline.**  The tabulating DP's answer for `amount` — the last cell of the amount-`amount`
    table, `nth (tab coins (snocs amount)) amount` — satisfies the Coin-Change extremum spec
    `coinSpec coins amount`.  The table itself is the emergent catamorphism (`fold_derived`). -/
theorem tab_derived_correct (coins : SnocList Nat Nat) (amount : Nat) :
    LC322.coinSpec coins amount (nth (tab coins (snocs amount)) amount) :=
  entry_spec coins amount

/-- **The derived fold computes the spec.**  The emergent catamorphism relates the amount axis
    `snocs amount` to the DP table `T`, and reading `T` at `amount` satisfies `coinSpec`.  Ties the
    course-of-values fold `cataR (scalarAlg (g coins) (st coins))` to the verified answer. -/
theorem answer_from_fold (coins : SnocList Nat Nat) (amount : Nat) :
    ∃ T, (cataR (scalarAlg (g coins) (st coins)) : dSL Unit Unit ⟶ ⟨List (Option Nat)⟩)
            (snocs amount) T
        ∧ LC322.coinSpec coins amount (nth T amount) := by
  refine ⟨tab coins (snocs amount), ?_, tab_derived_correct coins amount⟩
  have h : (graph (tab coins) : dSL Unit Unit ⟶ ⟨List (Option Nat)⟩)
      (snocs amount) (tab coins (snocs amount)) := rfl
  rw [fold_derived] at h
  exact h

/-! ## Cross-check against `L322.lean`'s verified answer

  The relational catamorphism `cataFold (scalarAlg …)` is not `decide`-computable (its `snoc` case
  is an existential over `List (Option Nat)`), so we `decide` the computable witness `tab` and read
  the last cell — extensionally the emergent fold's value (`fold_derived`). -/

example : nth (tab (LC322.ofList 1 [2, 5]) (snocs 11)) 11 = some 3 := by decide
example : nth (tab (LC322.ofList 2 []) (snocs 3)) 3 = none := by decide
example : nth (tab (LC322.ofList 1 []) (snocs 0)) 0 = some 0 := by decide
example : nth (tab (LC322.ofList 5 []) (snocs 3)) 3 = none := by decide

end Freyd.Alg.RelSet.LC322D
