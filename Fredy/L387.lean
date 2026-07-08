/-
  LeetCode 387 — First Unique Character in a String — as an ALLEGORY PROGRAM.

  Problem: return the index of the first character in a string `s` (char codes, `List Int`) that
  occurs exactly once; `none` (LeetCode's `-1`) if no character is unique.

  Like `Fredy/L1.lean` (`leetcode.md` S34), this is a WITNESS-SEARCH problem over a plain
  `List Int` (no `SnocList` engine: one left-to-right pass), phrased via `List.getElem?` (`L238`'s
  trick, `leetcode.md` S23) so index bounds are CONSEQUENCES of `= some _` facts, not separate
  hypotheses.

  1. **Data / program** — reuses `Fredy.L242`'s `countL : List Int → Int → Nat` ("unique" means
     `countL s c = 1` against the WHOLE string).  `scanFrom full l i` scans a suffix `l`, an
     `i`-offset tail of the FIXED full string, re-counting every candidate against `full` (never
     against `l`); `firstUniqFn s := scanFrom s s 0`.

  2. **Specification** — `IsFirstUniq s i` : the character at `i` is unique in `s`, and every
     earlier index holds a character occurring `≥ 2` times ("first" = leftmost).

  3. **Correctness** — `firstUniq_correct` bundles soundness (`some i` ⟹ `IsFirstUniq s i`) and
     none-completeness (`none` ⟹ no index of `s` holds a unique character at all).  Both come from
     ONE invariant lemma `scanFrom_correct`, proved by a single induction on the suffix `l`,
     carrying forward the precondition "nothing before index `i` is unique" — the S18/S19-style
     paired invariant, here unifying the `some`/`none` branches of a `match` instead of two
     separate theorems.

  Mathlib-free; axioms ⊆ {propext, Quot.sound} (fully constructive, no `Classical.choice`).
-/
import Fredy.L242

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC387

open Freyd Freyd.Alg.RelSet.LC242

/-! ## Data: a string is a plain `List Int` (char codes); answer is `Option Nat` -/

/-- The object of strings in `Rel(Set)`. -/
abbrev Str : RelSet.{0} := ⟨List Int⟩
/-- The answer object: an optional index. -/
abbrev Ans : RelSet.{0} := ⟨Option Nat⟩

/-! ## The program: scan `s`, carrying the FULL string (fixed, for `countL`) and the current
    index alongside the shrinking suffix being consumed. -/

/-- `scanFrom full l i` — the first index `≥ i` of a character unique in `full`, scanning the
    suffix `l` (an `i`-offset tail of `full`); `countL` is always taken against `full`, never
    against `l`. -/
def scanFrom (full : List Int) : List Int → Nat → Option Nat
  | [], _ => none
  | c :: rest, i => if countL full c = 1 then some i else scanFrom full rest (i + 1)

/-- The answer function: scan the whole string against itself, from index `0`. -/
def firstUniqFn (s : List Int) : Option Nat := scanFrom s s 0

/-- **The allegory program**: LeetCode 387's solution as a morphism `Str ⟶ Ans` in `Rel(Set)`. -/
def solve : Str ⟶ Ans := graph firstUniqFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map firstUniqFn

/-! ## Specification -/

/-- **The specification**: `i` is the first unique-character index of `s` — the character at `i`
    occurs exactly once in the WHOLE string, and every earlier index holds a character occurring
    at least twice. -/
def IsFirstUniq (s : List Int) (i : Nat) : Prop :=
  (∃ c, s[i]? = some c ∧ countL s c = 1) ∧
  ∀ j, j < i → ∀ c, s[j]? = some c → countL s c ≥ 2

/-! ## Correctness -/

/-- **The crux invariant.**  Given `l` is the `i`-offset suffix of `full` (`full = pre ++ l`,
    `i = pre.length`) and no index before `i` holds a unique character, `scanFrom full l i` finds
    the first unique index at or after `i` (`some` case), or — once `l` is exhausted — confirms NO
    index of `full` at all holds a unique character (`none` case).  Proved by ONE induction on
    `l`, propagating the "nothing seen so far is unique" precondition forward at each step. -/
theorem scanFrom_correct (full : List Int) : ∀ (l pre : List Int) (i : Nat),
    full = pre ++ l → i = pre.length →
    (∀ k, k < i → ∀ c, full[k]? = some c → countL full c ≥ 2) →
    match scanFrom full l i with
    | some j => (∃ c, full[j]? = some c ∧ countL full c = 1) ∧
                ∀ k, k < j → ∀ c, full[k]? = some c → countL full c ≥ 2
    | none => ∀ k, k < full.length → ∀ c, full[k]? = some c → countL full c ≥ 2 := by
  intro l
  induction l with
  | nil =>
    intro pre i hfull hi hprec
    have hlen : i = full.length := by rw [hi, hfull, List.append_nil]
    show ∀ k, k < full.length → ∀ c, full[k]? = some c → countL full c ≥ 2
    rw [← hlen]
    exact hprec
  | cons c rest ih =>
    intro pre i hfull hi hprec
    have hget : full[i]? = some c := by
      rw [hi, hfull, List.getElem?_append_right (Nat.le_refl pre.length), Nat.sub_self]
      rfl
    show match (if countL full c = 1 then some i else scanFrom full rest (i + 1)) with
      | some j => (∃ c, full[j]? = some c ∧ countL full c = 1) ∧
                  ∀ k, k < j → ∀ c, full[k]? = some c → countL full c ≥ 2
      | none => ∀ k, k < full.length → ∀ c, full[k]? = some c → countL full c ≥ 2
    by_cases hcount : countL full c = 1
    · rw [if_pos hcount]
      exact ⟨⟨c, hget, hcount⟩, hprec⟩
    · rw [if_neg hcount]
      have hmem : c ∈ full := List.mem_of_getElem? hget
      have hge2 : countL full c ≥ 2 := by
        have hpos : 0 < countL full c := (mem_iff_countL_pos full c).mp hmem
        omega
      have hprec' : ∀ k, k < i + 1 → ∀ c', full[k]? = some c' → countL full c' ≥ 2 := by
        intro k hk c' hkc'
        rcases Nat.lt_or_ge k i with hlt | hge
        · exact hprec k hlt c' hkc'
        · have hki : k = i := by omega
          subst hki
          have heqc : c = c' := Option.some.inj (hget.symm.trans hkc')
          rw [← heqc]
          exact hge2
      have hfull' : full = (pre ++ [c]) ++ rest := by
        rw [List.append_assoc]; exact hfull
      have hi' : i + 1 = (pre ++ [c]).length := by
        simp [hi]
      exact ih (pre ++ [c]) (i + 1) hfull' hi' hprec'

/-- **Soundness + none-completeness**, the LeetCode-387 headline: a `some i` result is a genuine
    first unique index, and a `none` result means no index of `s` holds a unique character. -/
theorem firstUniq_correct (s : List Int) :
    (∀ i, firstUniqFn s = some i → IsFirstUniq s i) ∧
    (firstUniqFn s = none → ∀ (i : Nat) (c : Int), s[i]? = some c → countL s c ≥ 2) := by
  have h := scanFrom_correct s s [] 0 rfl rfl (fun k hk => (Nat.not_lt_zero k hk).elim)
  refine ⟨fun i hi => ?_, fun hnone i c hic => ?_⟩
  · have hi' : scanFrom s s 0 = some i := hi
    rw [hi'] at h
    exact h
  · have hnone' : scanFrom s s 0 = none := hnone
    rw [hnone'] at h
    obtain ⟨hib, -⟩ := List.getElem?_eq_some_iff.mp hic
    exact h i hib c hic

/-! ## Running the program -/

-- letters encoded as distinct `Int`s: l=1 e=2 t=3 c=4 o=5 d=6
example : firstUniqFn [1, 2, 2, 3, 4, 5, 6, 2] = some 0 := by decide  -- "leetcode" → 'l' at 0
example : firstUniqFn [97, 97] = none := by decide  -- "aa" → no unique char

end Freyd.Alg.RelSet.LC387
