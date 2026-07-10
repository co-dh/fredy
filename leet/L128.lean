/-
  LeetCode 128 — Longest Consecutive Sequence — as an ALLEGORY PROGRAM.

  Problem: given an unsorted `nums : List Int` (duplicates allowed, order irrelevant), return the
  length of the longest run of CONSECUTIVE integers (by VALUE, not position) all present in
  `nums`.  E.g. `[100,4,200,1,3,2] ↦ 4` (the run `1,2,3,4`).  Empty list ↦ `0`.

  Same recipe as `leet/L56.lean`/`leet/L435.lean` (`Fredy/leetcode.md` S0/S22/S24): the data
  object is a plain `List Int`, and we REUSE `leet.L242`'s hand-rolled insertion sort
  (`isort`/`Sorted`/`linsert`/`countL`/`countL_isort`) rather than re-deriving sorting machinery.

  1. **Program** — `longestConsecFn nums := scanFn (isort nums)`: sort ascending, then a
     left-to-right scan tracks `(prev, runLen, best)` — on the next element `c`: if `c = prev`
     skip (dedup, a repeat doesn't extend a run), if `c = prev + 1` extend (`runLen + 1`), else
     reset (`runLen := 1`); `best := nmax best runLen` throughout (`nmax` is `L121`'s `imax`
     pattern, ported to `Nat` since the answer is a length).

  2. **Specification** — membership-based, NOT position-based (LeetCode's problem is about the
     VALUE-SET of `nums`, and sorting/scanning is only an algorithmic device): a length-`L`
     consecutive block starting at `s` is present iff `∀ i < L, (s + i) ∈ nums`.  Correctness is
     the `L121`-style refinement + domination pair (`Fredy/leetcode.md` S0):
       - achievability: `∃ s, ∀ i < longestConsecFn nums, (s + i) ∈ nums`;
       - domination:   `∀ s L, (∀ i < L, (s + i) ∈ nums) → L ≤ longestConsecFn nums`.

  3. **The crux (`scanAux_inv`)** — one combined induction on the sorted list's tail, generalizing
     the fold state, maintaining THREE invariants at every step (`RunOK`: the CURRENT run ending
     at `prev` is both achieved and locally MAXIMAL among all-in-`l` runs ending exactly at
     `prev`; `BestOK`: `best` is achieved and dominates every all-in-`l` run whose top is `≤ prev`;
     `Cover`: every value of `l` still to come is `≤ prev` or lies in the remaining suffix).  The
     load-bearing step: a candidate run's top value `top ≤ (new prev) = c`, `top ∈ l`, together
     with "everything in the remaining suffix is `≥ c`" (from sortedness) forces `top ≤ prev ∨
     top = c` — so every candidate either was already dominated by the OLD `best`, or ends
     EXACTLY at the new watermark `c`, where the freshly-proved LOCAL maximality (`RunOK`'s second
     half) finishes it. This is the Lean-native form of "a sorted list containing a whole
     value-block has that block as a literally adjacent (post-dedup) stretch" — no separate
     dedup/adjacency lemma needed, it falls out of the `Cover` invariant.

  4. **Bridge** — `isort_mem : x ∈ isort l ↔ x ∈ l`, derived LOCALLY from `L242`'s already-exported
     `mem_iff_countL_pos` + `countL_isort` (no new export needed from `L242`, per the "reuse, don't
     re-implement" rule) — membership is invariant under sorting, so the scan's answer over
     `isort nums` matches the membership-spec over `nums` directly.

  Mathlib-free.  Axioms `{propext, Quot.sound}` (target; verified below) — every `omega` call is
  on a PLAIN conjunction/hypothesis (never a negated conjunction, cf. `Fredy/leetcode.md` S3/S24),
  so no `Classical.choice`.
-/
import leet.L242

namespace Freyd.Alg.RelSet.LC128

open Freyd Freyd.Alg.RelSet.LC242

/-! ## Mathlib-free `Nat` max (the `L121`/`L56` `imax` pattern, ported to `Nat` — the answer is a
    length, so we track the running best as a `Nat`, not an `Int`; never reach for `Nat.max`). -/

def nmax (a b : Nat) : Nat := if a ≤ b then b else a

theorem nmax_ge_left (a b : Nat) : a ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_ge_right (a b : Nat) : b ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_eq_or (a b : Nat) : nmax a b = a ∨ nmax a b = b := by
  unfold nmax; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## The program: sort, then a left-to-right run-tracking scan -/

/-- `scanAux t (prev, runLen, best)` — scan a sorted-list SUFFIX `t`, given the state after the
    run ending at `prev` has already been folded. -/
def scanAux : List Int → Int × Nat × Nat → Int × Nat × Nat
  | [], st => st
  | c :: t, (prev, runLen, best) =>
      if c = prev then scanAux t (prev, runLen, best)
      else if c = prev + 1 then scanAux t (c, runLen + 1, nmax best (runLen + 1))
      else scanAux t (c, 1, nmax best 1)

/-- The full scan over a SORTED list: seed the state from the first element, scan the rest. -/
def scanFn : List Int → Nat
  | [] => 0
  | c :: t => (scanAux t (c, 1, 1)).2.2

/-- **The program**: sort, then scan. -/
def longestConsecFn (nums : List Int) : Nat := scanFn (isort nums)

/-! ## The sort-membership bridge — LOCAL to this file, built from `L242`'s already-exported
    `mem_iff_countL_pos` + `countL_isort` (no new `L242` export needed). -/

/-- Sorting a list changes neither its VALUE-SET nor its count function: membership is invariant
    under `isort`. -/
theorem isort_mem (l : List Int) (x : Int) : x ∈ isort l ↔ x ∈ l := by
  rw [mem_iff_countL_pos, countL_isort, ← mem_iff_countL_pos]

/-! ## The scan invariants -/

/-- `RunOK l prev runLen` — the run of length `runLen` ending at `prev` is BOTH achieved (all of
    `prev-runLen+1, …, prev` lie in `l`) AND locally MAXIMAL: no longer all-in-`l` run can end
    exactly at `prev`. -/
def RunOK (l : List Int) (prev : Int) (runLen : Nat) : Prop :=
  (∀ i : Nat, i < runLen → prev - (runLen : Int) + 1 + i ∈ l) ∧
  (∀ Lrun : Nat, (∀ i : Nat, i < Lrun → prev - (Lrun : Int) + 1 + i ∈ l) → Lrun ≤ runLen)

/-- `BestOK l prev best` — `best` is achieved (some length-`best` all-in-`l` run exists) and
    DOMINATES every all-in-`l` run whose top value is `≤ prev`. -/
def BestOK (l : List Int) (prev : Int) (best : Nat) : Prop :=
  (∃ s : Int, ∀ i : Nat, i < best → s + (i : Int) ∈ l) ∧
  (∀ (s : Int) (Lrun : Nat), (∀ i : Nat, i < Lrun → s + (i : Int) ∈ l) →
    s + (Lrun : Int) - 1 ≤ prev → Lrun ≤ best)

/-- A run achieved by `RunOK` is dominated by any `best` that is `≥ runLen` — used to bootstrap
    `runLen ≤ best` on demand instead of threading it as a fifth invariant. -/
theorem runLen_le_best {l : List Int} {prev : Int} {runLen best : Nat}
    (hR : RunOK l prev runLen) (hB : BestOK l prev best) : runLen ≤ best :=
  hB.2 (prev - (runLen : Int) + 1) runLen hR.1 (by omega)

/-- **The key dichotomy.** If `l`'s not-yet-processed suffix `t` is entirely `≥ c`, then any
    value of `l` that is `≤ c` was either already processed (`≤ prev`) or is exactly `c` — nothing
    can lie strictly between `prev` and `c`.  This is the "sorted list has no gap" fact, stated
    without ever mentioning dedup/adjacency directly. -/
theorem dichot_of_cover {l t : List Int} {prev c : Int} (hCover : ∀ x ∈ l, x ≤ prev ∨ x ∈ t)
    (hallge : ∀ x ∈ t, c ≤ x) : ∀ top : Int, top ∈ l → top ≤ c → top ≤ prev ∨ top = c := by
  intro top htopl htopc
  rcases hCover top htopl with h | h
  · exact Or.inl h
  · exact Or.inr (by have := hallge top h; omega)

/-- A value `c` present in `l` with `c - 1` absent starts a fresh run of length exactly `1`. -/
theorem run_singleton {l : List Int} {c : Int} (hcl : c ∈ l) (hgap : c - 1 ∉ l) :
    RunOK l c 1 := by
  refine ⟨fun i hi => ?_, fun Lrun hLrun => ?_⟩
  · have heq : c - ((1 : Nat) : Int) + 1 + (i : Int) = c := by omega
    rw [heq]; exact hcl
  · rcases Nat.lt_or_ge Lrun 2 with h2 | h2
    · omega
    · exfalso
      have hi2 : Lrun - 2 < Lrun := by omega
      have hx := hLrun (Lrun - 2) hi2
      have heq : c - (Lrun : Int) + 1 + ((Lrun - 2 : Nat) : Int) = c - 1 := by omega
      rw [heq] at hx
      exact hgap hx

/-- Extending a maximal run `[prev-runLen+1,…,prev]` by the adjacent value `c = prev+1` gives a
    maximal run `[prev-runLen+2,…,c]` of length `runLen+1`. -/
theorem run_extend {l : List Int} {prev c : Int} {runLen : Nat} (hR : RunOK l prev runLen)
    (hcl : c ∈ l) (hceq : c = prev + 1) : RunOK l c (runLen + 1) := by
  refine ⟨fun i hi => ?_, fun Lrun hLrun => ?_⟩
  · rcases Nat.lt_or_ge i runLen with hi' | hi'
    · have hx := hR.1 i hi'
      have heq : c - ((runLen + 1 : Nat) : Int) + 1 + (i : Int) = prev - (runLen : Int) + 1 + i := by
        omega
      rw [heq]; exact hx
    · have heq : c - ((runLen + 1 : Nat) : Int) + 1 + (i : Int) = c := by omega
      rw [heq]; exact hcl
  · rcases Nat.eq_zero_or_pos Lrun with hz | hz
    · omega
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Lrun ≠ 0)
      have hsub : ∀ i : Nat, i < k → prev - (k : Int) + 1 + i ∈ l := by
        intro i hi
        have hx := hLrun i (by omega)
        have heq : c - (Lrun : Int) + 1 + (i : Int) = prev - (k : Int) + 1 + i := by omega
        rw [heq] at hx; exact hx
      have hk' := hR.2 k hsub
      omega

/-- Propagate `BestOK` across one scan step: `best` becomes `nmax best newRunLen`, given the new
    watermark's run is `RunOK` and the dichotomy `dichot_of_cover` provides. -/
theorem best_update {l : List Int} {prev c : Int} {best newRunLen : Nat} (hB : BestOK l prev best)
    (hRnew : RunOK l c newRunLen)
    (hdichot : ∀ top : Int, top ∈ l → top ≤ c → top ≤ prev ∨ top = c) :
    BestOK l c (nmax best newRunLen) := by
  refine ⟨?_, fun s Lrun hs htop => ?_⟩
  · rcases nmax_eq_or best newRunLen with h | h
    · rw [h]; exact hB.1
    · rw [h]; exact ⟨c - (newRunLen : Int) + 1, hRnew.1⟩
  · rcases Nat.eq_zero_or_pos Lrun with hz | hz
    · omega
    · have htopl : s + (Lrun : Int) - 1 ∈ l := by
        have hx := hs (Lrun - 1) (by omega)
        have heq : s + ((Lrun - 1 : Nat) : Int) = s + (Lrun : Int) - 1 := by omega
        rwa [heq] at hx
      rcases hdichot (s + (Lrun : Int) - 1) htopl htop with h1 | h1
      · have hle := hB.2 s Lrun hs h1
        have hb := nmax_ge_left best newRunLen
        omega
      · have hseq : s = c - (Lrun : Int) + 1 := by omega
        have hsub : ∀ i : Nat, i < Lrun → c - (Lrun : Int) + 1 + i ∈ l := by
          intro i hi; rw [← hseq]; exact hs i hi
        have hle := hRnew.2 Lrun hsub
        have hb := nmax_ge_right best newRunLen
        omega

/-! ## The crux: one combined induction on the sorted suffix, generalizing the fold state -/

/-- **The scan invariant.** Given a `Sorted` suffix `t` (all `≥ prev`, all members of `l`) and a
    state `(prev, runLen, best)` already satisfying `RunOK`/`BestOK` w.r.t. `l`, scanning `t`
    produces a state still satisfying `RunOK`/`BestOK`, and the new watermark dominates ALL of
    `l` (`Cover` collapses once the suffix is fully consumed). -/
theorem scanAux_inv (l : List Int) : ∀ (t : List Int) (prev : Int) (runLen best : Nat),
    Sorted t → (∀ x ∈ t, prev ≤ x) → (∀ x ∈ t, x ∈ l) → (∀ x ∈ l, x ≤ prev ∨ x ∈ t) →
    RunOK l prev runLen → BestOK l prev best →
    RunOK l (scanAux t (prev, runLen, best)).1 (scanAux t (prev, runLen, best)).2.1 ∧
    BestOK l (scanAux t (prev, runLen, best)).1 (scanAux t (prev, runLen, best)).2.2 ∧
    (∀ x ∈ l, x ≤ (scanAux t (prev, runLen, best)).1) := by
  intro t
  induction t with
  | nil =>
    intro prev runLen best _ _ _ hCover hR hB
    refine ⟨hR, hB, fun x hx => ?_⟩
    rcases hCover x hx with h | h
    · exact h
    · exact absurd h (List.not_mem_nil)
  | cons c t' ih =>
    intro prev runLen best hSorted hGe hSub hCover hR hB
    obtain ⟨hSortedHead, hSortedTail⟩ := hSorted
    have hcprev : prev ≤ c := hGe c (List.mem_cons_self ..)
    have hcl : c ∈ l := hSub c (List.mem_cons_self ..)
    have hallge : ∀ x ∈ (c :: t'), c ≤ x := by
      intro x hx
      rcases List.mem_cons.mp hx with heq | hx
      · omega
      · exact hSortedHead x hx
    have hdichot := dichot_of_cover hCover hallge
    have hSub' : ∀ x ∈ t', x ∈ l := fun x hx => hSub x (List.mem_cons_of_mem c hx)
    by_cases hcp : c = prev
    · show RunOK l (scanAux (c :: t') (prev, runLen, best)).1
            (scanAux (c :: t') (prev, runLen, best)).2.1 ∧ _ ∧ _
      simp only [scanAux, if_pos hcp]
      have hGe' : ∀ x ∈ t', prev ≤ x := by
        intro x hx; have := hSortedHead x hx; omega
      have hCover' : ∀ x ∈ l, x ≤ prev ∨ x ∈ t' := by
        intro x hx
        rcases hCover x hx with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with heq | h
          · exact Or.inl (by omega)
          · exact Or.inr h
      exact ih prev runLen best hSortedTail hGe' hSub' hCover' hR hB
    · by_cases hcp1 : c = prev + 1
      · show RunOK l (scanAux (c :: t') (prev, runLen, best)).1
              (scanAux (c :: t') (prev, runLen, best)).2.1 ∧ _ ∧ _
        simp only [scanAux, if_neg hcp, if_pos hcp1]
        have hGe' : ∀ x ∈ t', c ≤ x := hSortedHead
        have hCover' : ∀ x ∈ l, x ≤ c ∨ x ∈ t' := by
          intro x hx
          rcases hCover x hx with h | h
          · exact Or.inl (by omega)
          · rcases List.mem_cons.mp h with heq | h
            · exact Or.inl (by omega)
            · exact Or.inr h
        have hR' : RunOK l c (runLen + 1) := run_extend hR hcl hcp1
        have hB' : BestOK l c (nmax best (runLen + 1)) := best_update hB hR' hdichot
        exact ih c (runLen + 1) (nmax best (runLen + 1)) hSortedTail hGe' hSub' hCover' hR' hB'
      · show RunOK l (scanAux (c :: t') (prev, runLen, best)).1
              (scanAux (c :: t') (prev, runLen, best)).2.1 ∧ _ ∧ _
        simp only [scanAux, if_neg hcp, if_neg hcp1]
        have hgapc : prev + 1 < c := by omega
        have hGe' : ∀ x ∈ t', c ≤ x := hSortedHead
        have hCover' : ∀ x ∈ l, x ≤ c ∨ x ∈ t' := by
          intro x hx
          rcases hCover x hx with h | h
          · exact Or.inl (by omega)
          · rcases List.mem_cons.mp h with heq | h
            · exact Or.inl (by omega)
            · exact Or.inr h
        have hgap1 : c - 1 ∉ l := by
          intro hc1
          rcases hdichot (c - 1) hc1 (by omega) with h | h
          · omega
          · omega
        have hR' : RunOK l c 1 := run_singleton hcl hgap1
        have hB' : BestOK l c (nmax best 1) := best_update hB hR' hdichot
        exact ih c 1 (nmax best 1) hSortedTail hGe' hSub' hCover' hR' hB'

/-! ## Base case: seed the scan from `l`'s first (= minimum) element -/

/-- **The scan is honest**: on a `Sorted` list, `scanFn` achieves a value-run of its own length,
    and dominates every value-run present in `l` — the refinement + domination pair (`Fredy/leetcode.md`
    S0), stated directly over `l` (before the sort-membership bridge to the original `nums`). -/
theorem scanFn_spec (l : List Int) (hSorted : Sorted l) :
    (∃ s : Int, ∀ i : Nat, i < scanFn l → s + (i : Int) ∈ l) ∧
    (∀ (s : Int) (Lrun : Nat), (∀ i : Nat, i < Lrun → s + (i : Int) ∈ l) → Lrun ≤ scanFn l) := by
  cases l with
  | nil =>
    refine ⟨⟨0, fun i hi => absurd hi (by simp [scanFn])⟩, fun s Lrun hLrun => ?_⟩
    rcases Nat.eq_zero_or_pos Lrun with hz | hz
    · omega
    · exact absurd (hLrun 0 hz) (List.not_mem_nil)
  | cons c t =>
    obtain ⟨hSortedHead, hSortedTail⟩ := hSorted
    have hGe : ∀ x ∈ t, c ≤ x := hSortedHead
    have hSub : ∀ x ∈ t, x ∈ (c :: t) := fun x hx => List.mem_cons_of_mem c hx
    have hCover : ∀ x ∈ (c :: t), x ≤ c ∨ x ∈ t := by
      intro x hx
      rcases List.mem_cons.mp hx with heq | hx
      · exact Or.inl (by omega)
      · exact Or.inr hx
    have hgap1 : c - 1 ∉ (c :: t) := by
      intro hc1
      rcases List.mem_cons.mp hc1 with heq | hmem
      · omega
      · have := hGe (c - 1) hmem; omega
    have hR : RunOK (c :: t) c 1 := run_singleton (List.mem_cons_self ..) hgap1
    have hB : BestOK (c :: t) c 1 := by
      refine ⟨⟨c, fun i hi => ?_⟩, fun s Lrun hs htop => ?_⟩
      · have heq : c + (i : Int) = c := by omega
        rw [heq]; exact List.mem_cons_self ..
      · rcases Nat.eq_zero_or_pos Lrun with hz | hz
        · omega
        · have htopl : s + (Lrun : Int) - 1 ∈ (c :: t) := by
            have hx := hs (Lrun - 1) (by omega)
            have heq : s + ((Lrun - 1 : Nat) : Int) = s + (Lrun : Int) - 1 := by omega
            rwa [heq] at hx
          have htopge : c ≤ s + (Lrun : Int) - 1 := by
            rcases List.mem_cons.mp htopl with h | h
            · omega
            · exact hGe _ h
          have hLrun1 := hR.2 Lrun (by
            intro i hi
            have hx := hs i hi
            have heq : c - (Lrun : Int) + 1 + (i : Int) = s + i := by omega
            rw [heq]; exact hx)
          exact hLrun1
    have hres := scanAux_inv (c :: t) t c 1 1 hSortedTail hGe hSub hCover hR hB
    refine ⟨hres.2.1.1, fun s Lrun hLrun => ?_⟩
    rcases Nat.eq_zero_or_pos Lrun with hz | hz
    · omega
    · have htopl : s + (Lrun : Int) - 1 ∈ (c :: t) := by
        have hx := hLrun (Lrun - 1) (by omega)
        have heq : s + ((Lrun - 1 : Nat) : Int) = s + (Lrun : Int) - 1 := by omega
        rwa [heq] at hx
      exact hres.2.1.2 s Lrun hLrun (hres.2.2 _ htopl)

/-! ## The bridge to `nums`: membership over `isort nums` = membership over `nums` -/

/-- **The allegory-program correctness statement** (`Fredy/leetcode.md` S0's refinement +
    domination pair): `longestConsecFn nums` achieves a value-run of its own length and dominates
    every value-run present in `nums`. -/
theorem longestConsec_correct (nums : List Int) :
    (∃ s : Int, ∀ i : Nat, i < longestConsecFn nums → s + (i : Int) ∈ nums) ∧
    (∀ (s : Int) (Lrun : Nat), (∀ i : Nat, i < Lrun → s + (i : Int) ∈ nums) →
      Lrun ≤ longestConsecFn nums) := by
  have h := scanFn_spec (isort nums) (isort_sorted nums)
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs⟩ := h.1
    exact ⟨s, fun i hi => (isort_mem nums (s + i)).mp (hs i hi)⟩
  · intro s Lrun hLrun
    exact h.2 s Lrun (fun i hi => (isort_mem nums (s + i)).mpr (hLrun i hi))

/-! ## The allegory program: package `longestConsecFn` as a morphism in `Rel(Set)` -/

/-- The object of number lists in `Rel(Set)`. -/
abbrev NumList : RelSet.{0} := ⟨List Int⟩
/-- The answer object: lengths. -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-- **The allegory program**: LeetCode 128's solution as a morphism `NumList ⟶ ℕ` in `Rel(Set)`. -/
def solve : NumList ⟶ dNat := graph longestConsecFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map longestConsecFn

/-- **The specification** as a morphism `NumList ⟶ ℕ`: `L` is achievable and dominates every
    achievable length. -/
def spec : NumList ⟶ dNat := fun nums L =>
  (∃ s : Int, ∀ i : Nat, i < L → s + (i : Int) ∈ nums) ∧
  (∀ (s : Int) (L' : Nat), (∀ i : Nat, i < L' → s + (i : Int) ∈ nums) → L' ≤ L)

/-- **`solve` equals `spec` as relations** (the allegory-program correctness statement). -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro nums L
  show (L = longestConsecFn nums) ↔ _
  constructor
  · intro h; rw [h]; exact longestConsec_correct nums
  · rintro ⟨⟨s, hs⟩, hdom⟩
    obtain ⟨s2, hs2⟩ := (longestConsec_correct nums).1
    have h1 : L ≤ longestConsecFn nums := (longestConsec_correct nums).2 s L hs
    have h2 : longestConsecFn nums ≤ L := hdom s2 (longestConsecFn nums) hs2
    exact Nat.le_antisymm h1 h2

/-! ## Running the program -/

example : longestConsecFn [100, 4, 200, 1, 3, 2] = 4 := by decide  -- the run 1,2,3,4
example : longestConsecFn [1, 2, 2, 3] = 3 := by decide            -- dedup: 1,2,3 despite the repeat

end Freyd.Alg.RelSet.LC128
