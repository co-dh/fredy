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

/-! ## Correctness re-proof

  `coinFold_spec` is the fuel proof's successor step (`L322.dpFuel_spec`), abstracted over an
  arbitrary table-reading `step` that is already correct at the smaller amounts it reads.  A
  bounded strong induction then discharges every table entry against `coinSpec`. -/

/-- **Generic DP step.**  If `step` already computes the extremum spec at every sub-amount `a+1-c`
    a valid coin reaches, then the `omin`-fold over the coins computes the extremum spec at `a+1`.
    This is `L322.dpFuel_spec`'s successor case with the recursive `dpFuel` replaced by `step`. -/
theorem coinFold_spec (coins : SnocList Nat Nat) (step : Nat → Option Nat) (a : Nat)
    (hstep : ∀ c, 1 ≤ c → c ≤ a + 1 → LC322.coinSpec coins (a + 1 - c) (step (a + 1 - c))) :
    LC322.coinSpec coins (a + 1) (LC322.coinFold step (a + 1) coins) := by
  rcases hres : LC322.coinFold step (a + 1) coins with _ | m
  · -- impossibility
    intro n hn
    match n, hn with
    | 0, hn => exact absurd (LC322.achievable_zero_iff.mp hn) (by omega)
    | n' + 1, hn =>
      obtain ⟨c, hmem, hpos, hle, hach⟩ := LC322.achievable_succ_iff.mp hn
      have hspec := hstep c hpos hle
      rcases hstepv : step (a + 1 - c) with _ | mv
      · rw [hstepv] at hspec
        exact hspec n' hach
      · obtain ⟨m₀, hm₀, _⟩ := LC322.coinFold_dominates (step := step) (t := a + 1)
          coins hmem hpos hle hstepv
        rw [hres] at hm₀
        exact absurd hm₀ (by simp)
  · -- achievability + minimality
    obtain ⟨c, mv, hmem, hpos, hle, hstepv, hm⟩ := LC322.coinFold_achieves coins hres
    have hspecStep := hstep c hpos hle
    rw [hstepv] at hspecStep
    obtain ⟨hachStep, _⟩ := hspecStep
    have hsub : a + 1 - c + c = a + 1 := by omega
    have hachm : LC322.Achievable coins m (a + 1) := by
      rw [hm, ← hsub]
      exact LC322.Achievable.succ hachStep hmem hpos
    refine ⟨hachm, ?_⟩
    intro n' hn'
    match n', hn' with
    | 0, hn' => exact absurd (LC322.achievable_zero_iff.mp hn') (by omega)
    | n'' + 1, hn' =>
      obtain ⟨c', hmem', hpos', hle', hach'⟩ := LC322.achievable_succ_iff.mp hn'
      have hspec' := hstep c' hpos' hle'
      rcases hstepv' : step (a + 1 - c') with _ | mv'
      · rw [hstepv'] at hspec'
        exact absurd hach' (hspec' n'')
      · obtain ⟨hach'', hmin'⟩ := by rw [hstepv'] at hspec'; exact hspec'
        have hmv' : mv' ≤ n'' := hmin' n'' hach'
        obtain ⟨m₀, hm₀, hm₀le⟩ := LC322.coinFold_dominates (step := step) (t := a + 1)
          coins hmem' hpos' hle' hstepv'
        rw [hres] at hm₀
        have hmm : m = m₀ := by rw [Option.some.injEq] at hm₀; exact hm₀
        omega

/-- Every canonical table entry satisfies the extremum spec (bounded strong induction on `N`). -/
theorem entry_spec_bounded (coins : SnocList Nat Nat) :
    ∀ N a, a ≤ N → LC322.coinSpec coins a (entry coins a) := by
  intro N
  induction N with
  | zero =>
    intro a ha
    have ha0 : a = 0 := by omega
    subst ha0
    show LC322.coinSpec coins 0 (some 0)
    exact ⟨LC322.Achievable.zero, fun n' _ => Nat.zero_le n'⟩
  | succ N ih =>
    intro a ha
    rcases Nat.lt_or_ge a (N + 1) with h | h
    · exact ih a (by omega)
    · have ha' : a = N + 1 := by omega
      subst ha'
      rw [entry_succ_eq]
      exact coinFold_spec coins (entry coins) N
        (fun c hpos hle => ih (N + 1 - c) (by omega))

/-- Each table entry `entry coins a` is the `≤`-minimum achievable coin-count for amount `a`
    (`none` if unreachable) — `coinSpec coins a`. -/
theorem entry_spec (coins : SnocList Nat Nat) (a : Nat) :
    LC322.coinSpec coins a (entry coins a) :=
  entry_spec_bounded coins a a (Nat.le_refl a)

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
