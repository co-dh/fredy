/-
  LeetCode 1 — Two Sum — as an ALLEGORY PROGRAM.

  Problem: given `nums : List Int` and `target : Int`, find two DISTINCT positions `i < j` with
  `nums[i] + nums[j] = target`.  Unlike `leet/L217.lean` (a Bool DECISION), this is a
  WITNESS-SEARCH problem: the answer object is `Option (Nat × Nat)`, and correctness is honest
  soundness + completeness — no assumption that a solution is unique (real Two Sum inputs can
  have several valid pairs; the program returns only ONE of them, so `solve` cannot equal a
  "the correct answer" spec relation the way `L217`'s Bool decision does).

  1. **Data** — a plain `List Int` (no `SnocList` engine needed: the scan is a single LEFT-TO-RIGHT
     pass, not a fold over an initial algebra with book-worthy structure).

  2. **Program** — `twoSumFn nums target` scans `nums` once, carrying a "seen" association list
     `(value, index)` of every EARLIER element.  At each new element `x` (about to be assigned
     index `seen.length`), `findComplement (target - x) seen` looks the complement up in `seen`;
     a hit `some i` returns `some (i, seen.length)`, a miss pushes `(x, seen.length)` and continues.

  3. **Specification** — `TwoSum nums target i j := i < j ∧ ∃ vi vj, nums[i]? = some vi ∧
     nums[j]? = some vj ∧ vi + vj = target`, phrased via `List.getElem?` (`L238`'s trick: this
     sidesteps `i < nums.length` proof-term bookkeeping — both bounds are *consequences* of the
     `getElem?  = some _` facts via `List.getElem?_eq_some_iff`, not separate hypotheses).

  4. **Correctness** — `twoSum_sound`/`twoSum_complete` (bundled as `twoSum_correct`): a `some`
     result is a genuine hit, a `none` result means NO valid pair exists anywhere in `nums`.  Both
     directions come from ONE generalized induction (`go_gen`) threading three invariants through
     the scan: `seen.length = done.length` (the running index), `SeenIff done seen` (`seen` is
     EXACTLY the (value,index) pairs of the processed prefix `done`), and `∀ i j, ¬TwoSum done
     target i j` (no valid pair has been missed in the prefix so far — carried so the `none` case
     at the very end also rules out pairs entirely inside an already-scanned prefix, not just
     pairs touching the current element).

  Mathlib-free; axioms ⊆ {propext, Quot.sound} (fully constructive, no `Classical.choice`).
-/
import AOP.A6_1_RelSet

namespace Freyd.Alg.RelSet.LC1

open Freyd

/-! ## The program: a left-to-right scan with a "seen" association-list sub-search -/

/-- `findComplement want seen` — the index of the first pair in `seen` whose value is `want`,
    if any (a linear search over the association list of earlier `(value, index)` pairs). -/
def findComplement (want : Int) : List (Int × Nat) → Option Nat
  | [] => none
  | (v, i) :: rest => if v = want then some i else findComplement want rest

/-- `go seen target xs` scans `xs`, carrying `seen` (the `(value, index)` pairs of everything
    already processed, so the next element's index is `seen.length`).  Returns the first hit. -/
def go (seen : List (Int × Nat)) (target : Int) : List Int → Option (Nat × Nat)
  | [] => none
  | x :: xs =>
    match findComplement (target - x) seen with
    | some i => some (i, seen.length)
    | none => go ((x, seen.length) :: seen) target xs

/-- **The program**: LeetCode 1's solution — a single left-to-right scan. -/
def twoSumFn (nums : List Int) (target : Int) : Option (Nat × Nat) := go [] target nums

/-! ## `Rel(Set)` packaging -/

/-- The input object: a list of integers paired with a target sum. -/
abbrev Input : RelSet.{0} := ⟨List Int × Int⟩
/-- The answer object: an optional pair of positions. -/
abbrev Ans : RelSet.{0} := ⟨Option (Nat × Nat)⟩

/-- **The allegory program**: LeetCode 1's solution as a morphism `Input ⟶ Ans` in `Rel(Set)`. -/
def solve : Input ⟶ Ans := graph (fun p : List Int × Int => twoSumFn p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map (fun p : List Int × Int => twoSumFn p.1 p.2)

/-! ## Specification: a genuine valid pair -/

/-- `TwoSum nums target i j` — `i` and `j` are DISTINCT positions (`i < j`) inside `nums` whose
    values sum to `target`.  `i < nums.length` is a consequence of `nums[i]? = some vi`, not a
    separate hypothesis (`List.getElem?_eq_some_iff`). -/
def TwoSum (nums : List Int) (target : Int) (i j : Nat) : Prop :=
  i < j ∧ ∃ vi vj, nums[i]? = some vi ∧ nums[j]? = some vj ∧ vi + vj = target

/-! ## `findComplement` reflects membership in `seen` -/

theorem findComplement_some : ∀ {seen : List (Int × Nat)} {want : Int} {i : Nat},
    findComplement want seen = some i → (want, i) ∈ seen := by
  intro seen
  induction seen with
  | nil => intro want i h; simp [findComplement] at h
  | cons p rest ih =>
    intro want i h
    obtain ⟨v, k⟩ := p
    simp only [findComplement] at h
    split at h
    · rename_i heq
      have hik : k = i := by injection h
      rw [← heq, ← hik]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

theorem findComplement_none : ∀ {seen : List (Int × Nat)} {want : Int},
    findComplement want seen = none → ∀ i, (want, i) ∉ seen := by
  intro seen
  induction seen with
  | nil => intro want _ i hmem; exact absurd hmem (List.not_mem_nil)
  | cons p rest ih =>
    intro want h i hmem
    obtain ⟨v, k⟩ := p
    simp only [findComplement] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hne
      rcases List.mem_cons.mp hmem with heq2 | hmem'
      · injection heq2 with hv _
        exact hne hv.symm
      · exact ih h i hmem'

/-! ## `getElem?` facts across an append at the boundary -/

/-- The freshly-appended element sits exactly at index `l1.length`. -/
theorem getElem?_append_right_zero {l1 l2 : List Int} {x : Int} :
    (l1 ++ x :: l2)[l1.length]? = some x := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

/-! ## The loop invariant: `seen` is EXACTLY the (value, index) pairs of the processed prefix -/

/-- `seen` records exactly the `(value, index)` pairs of `done`. -/
def SeenIff (done : List Int) (seen : List (Int × Nat)) : Prop :=
  ∀ v i, (v, i) ∈ seen ↔ done[i]? = some v

/-- Pushing the next element onto `seen` preserves the exact-record invariant. -/
theorem seenIff_push {done : List Int} {seen : List (Int × Nat)} {x : Int}
    (hlen : seen.length = done.length) (hseen : SeenIff done seen) :
    SeenIff (done ++ [x]) ((x, seen.length) :: seen) := by
  intro v i
  constructor
  · intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hvx hik
      rw [hvx, hik, hlen]
      exact getElem?_append_right_zero
    · have hdi := (hseen v i).mp hmem'
      have hib : i < done.length := (List.getElem?_eq_some_iff.mp hdi).1
      rw [List.getElem?_append_left hib]
      exact hdi
  · intro hdi'
    have hib : i < (done ++ [x]).length := (List.getElem?_eq_some_iff.mp hdi').1
    rcases Nat.lt_or_ge i done.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hdi'
      exact List.mem_cons_of_mem _ ((hseen v i).mpr hdi')
    · have hieq : i = done.length := by
        simp only [List.length_append, List.length_singleton] at hib
        omega
      rw [hieq, getElem?_append_right_zero] at hdi'
      injection hdi' with hxv
      have hiseen : i = seen.length := hieq.trans hlen.symm
      rw [← hxv, hiseen]
      exact List.mem_cons_self ..

/-- If the processed prefix has no valid pair and the complement search for the next element
    misses, the extended prefix still has no valid pair. -/
theorem noPair_push {done : List Int} {seen : List (Int × Nat)} {x target : Int}
    (hseen : SeenIff done seen) (hnp : ∀ i j, ¬ TwoSum done target i j)
    (hmiss : findComplement (target - x) seen = none) :
    ∀ i j, ¬ TwoSum (done ++ [x]) target i j := by
  have hnew : ∀ (v : Int) (i : Nat), done[i]? = some v → v ≠ target - x := by
    intro v i hdi heq
    subst heq
    exact findComplement_none hmiss i ((hseen (target - x) i).mpr hdi)
  rintro i j ⟨hij, vi, vj, hdi, hdj, hsum⟩
  have hjb : j < (done ++ [x]).length := (List.getElem?_eq_some_iff.mp hdj).1
  simp only [List.length_append, List.length_singleton] at hjb
  rcases Nat.lt_or_ge j done.length with hjlt | hjge
  · have hib : i < done.length := by omega
    rw [List.getElem?_append_left hib] at hdi
    rw [List.getElem?_append_left hjlt] at hdj
    exact hnp i j ⟨hij, vi, vj, hdi, hdj, hsum⟩
  · have hjeq : j = done.length := by omega
    have hib : i < done.length := by omega
    rw [List.getElem?_append_left hib] at hdi
    rw [hjeq, getElem?_append_right_zero] at hdj
    injection hdj with hxvj
    exact hnew vi i hdi (by omega)

/-! ## The main loop lemma: ONE generalized induction gives both soundness and completeness -/

theorem go_gen : ∀ (xs done : List Int) (seen : List (Int × Nat)) (target : Int),
    seen.length = done.length → SeenIff done seen → (∀ i j, ¬ TwoSum done target i j) →
    (∀ i j, go seen target xs = some (i, j) → TwoSum (done ++ xs) target i j) ∧
    (go seen target xs = none → ∀ i j, ¬ TwoSum (done ++ xs) target i j) := by
  intro xs
  induction xs with
  | nil =>
    intro done seen target _ _ hnp
    refine ⟨fun i j h => by simp [go] at h, fun _ => by rw [List.append_nil]; exact hnp⟩
  | cons x xs ih =>
    intro done seen target hlen hseen hnp
    show
      (∀ i j, go seen target (x :: xs) = some (i, j) → TwoSum (done ++ x :: xs) target i j) ∧
      (go seen target (x :: xs) = none → ∀ i j, ¬ TwoSum (done ++ x :: xs) target i j)
    rcases hfc : findComplement (target - x) seen with i0 | i0
    · -- `findComplement` missed: recurse with the new element pushed onto `seen`.
      have hgo : go seen target (x :: xs) = go ((x, seen.length) :: seen) target xs := by
        show
          (match findComplement (target - x) seen with
            | some i => some (i, seen.length)
            | none => go ((x, seen.length) :: seen) target xs) =
          go ((x, seen.length) :: seen) target xs
        rw [hfc]
      have hlen' : ((x, seen.length) :: seen).length = (done ++ [x]).length := by
        simp [hlen]
      have := ih (done ++ [x]) ((x, seen.length) :: seen) target hlen'
        (seenIff_push hlen hseen) (noPair_push hseen hnp hfc)
      rw [List.append_assoc, List.singleton_append] at this
      exact ⟨fun i j h => this.1 i j (by rw [hgo] at h; exact h),
             fun h => this.2 (by rw [hgo] at h; exact h)⟩
    · -- `findComplement` hit `i0`: the answer is `(i0, seen.length)`.
      have hgo : go seen target (x :: xs) = some (i0, seen.length) := by
        show
          (match findComplement (target - x) seen with
            | some i => some (i, seen.length)
            | none => go ((x, seen.length) :: seen) target xs) =
          some (i0, seen.length)
        rw [hfc]
      have hmem : (target - x, i0) ∈ seen := findComplement_some hfc
      have hdi0 : done[i0]? = some (target - x) := (hseen (target - x) i0).mp hmem
      have hib : i0 < done.length := (List.getElem?_eq_some_iff.mp hdi0).1
      refine ⟨fun i j h => ?_, fun h => absurd (hgo.symm.trans h) (by simp)⟩
      rw [hgo] at h
      injection h with hpair
      injection hpair with hi hj
      rw [← hi, ← hj]
      have hlt : i0 < seen.length := by rw [hlen]; exact hib
      have hdi : (done ++ x :: xs)[i0]? = some (target - x) := by
        rw [List.getElem?_append_left hib]; exact hdi0
      have hdj : (done ++ x :: xs)[seen.length]? = some x := by
        rw [hlen]; exact getElem?_append_right_zero
      exact ⟨hlt, target - x, x, hdi, hdj, by omega⟩

/-! ## Top-level correctness -/

/-- **Soundness**: a returned pair is a genuine hit. -/
theorem twoSum_sound (nums : List Int) (target : Int) (i j : Nat)
    (h : twoSumFn nums target = some (i, j)) : TwoSum nums target i j := by
  have hbase : SeenIff ([] : List Int) ([] : List (Int × Nat)) := by
    intro v i; simp
  have hnp0 : ∀ i j, ¬ TwoSum ([] : List Int) target i j := by
    rintro i j ⟨_, vi, vj, hdi, _⟩; simp at hdi
  have := (go_gen nums [] [] target rfl hbase hnp0).1 i j h
  rwa [List.nil_append] at this

/-- **Completeness**: a `none` result means no valid pair exists anywhere in `nums`. -/
theorem twoSum_complete (nums : List Int) (target : Int) (h : twoSumFn nums target = none) :
    ∀ i j, ¬ TwoSum nums target i j := by
  have hbase : SeenIff ([] : List Int) ([] : List (Int × Nat)) := by
    intro v i; simp
  have hnp0 : ∀ i j, ¬ TwoSum ([] : List Int) target i j := by
    rintro i j ⟨_, vi, vj, hdi, _⟩; simp at hdi
  have := (go_gen nums [] [] target rfl hbase hnp0).2 h
  rwa [List.nil_append] at this

/-- **Correctness of the allegory program**: honest soundness AND completeness, bundled. -/
theorem twoSum_correct (nums : List Int) (target : Int) :
    (∀ i j, twoSumFn nums target = some (i, j) → TwoSum nums target i j) ∧
    (twoSumFn nums target = none → ∀ i j, ¬ TwoSum nums target i j) :=
  ⟨twoSum_sound nums target, twoSum_complete nums target⟩

/-! ## Optimality: WHICH pair the scan returns

  Soundness says the returned pair is valid; completeness says `none` means no pair.  The scan
  in fact returns a canonical pair: the one with the SMALLEST second index (the first hit), and
  among those the LARGEST first index (`findComplement` searches `seen` prepend-newest, so the
  first hit is the most recent occurrence of the complement value).  This pins the scan's answer
  as the maximum under the order "smaller `j`, then larger `i`" — the fact that identifies it
  with the thinning-derived program of `leet/L1_thinned.lean`. -/

/-- `findComplement` returns a maximal index: no member of `seen` holding the same value has a
    larger index.  (An invariant of the scan's `seen`, whose entries are prepended with strictly
    increasing indices.) -/
def FCmax (seen : List (Int × Nat)) : Prop :=
  ∀ v i m, (v, i) ∈ seen → findComplement v seen = some m → i ≤ m

/-- Pushing a FRESH index (larger than everything in `seen`) preserves `FCmax`. -/
theorem fcmax_push {seen : List (Int × Nat)} {x : Int} {n : Nat}
    (hb : ∀ v i, (v, i) ∈ seen → i < n) (hm : FCmax seen) : FCmax ((x, n) :: seen) := by
  intro v i m hmem hfc
  simp only [findComplement] at hfc
  split at hfc
  · -- the head `(x, n)` answers the search: `m = n` bounds every index in `seen`
    injection hfc with hnm
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with _ hin
      omega
    · have := hb v i hmem'
      omega
  · rename_i hxv
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hvx _
      exact absurd hvx.symm hxv
    · exact hm v i m hmem' hfc

theorem go_opt : ∀ (xs done : List Int) (seen : List (Int × Nat)) (target : Int),
    seen.length = done.length → SeenIff done seen → FCmax seen →
    (∀ i j, ¬ TwoSum done target i j) →
    ∀ i₀ j₀, go seen target xs = some (i₀, j₀) →
    ∀ i j, TwoSum (done ++ xs) target i j → j₀ < j ∨ (j₀ = j ∧ i ≤ i₀) := by
  intro xs
  induction xs with
  | nil => intro done seen target _ _ _ _ i₀ j₀ h; simp [go] at h
  | cons x xs ih =>
    intro done seen target hlen hseen hfcm hnp i₀ j₀ hgo i j hts
    rcases hfc : findComplement (target - x) seen with _ | c
    · -- miss: the scan recurses; recurse with the pushed invariants
      have hgo' : go seen target (x :: xs) = go ((x, seen.length) :: seen) target xs := by
        show
          (match findComplement (target - x) seen with
            | some i => some (i, seen.length)
            | none => go ((x, seen.length) :: seen) target xs) =
          go ((x, seen.length) :: seen) target xs
        rw [hfc]
      have hb : ∀ v i, (v, i) ∈ seen → i < seen.length := by
        intro v i hm
        have hdi := (hseen v i).mp hm
        have := (List.getElem?_eq_some_iff.mp hdi).1
        omega
      have := ih (done ++ [x]) ((x, seen.length) :: seen) target
        (by simp [hlen]) (seenIff_push hlen hseen) (fcmax_push hb hfcm)
        (noPair_push hseen hnp hfc) i₀ j₀ (by rw [← hgo', hgo]) i j
        (by rwa [List.append_assoc, List.singleton_append])
      exact this
    · -- hit: the answer is `(c, seen.length)`; compare the given pair against it
      have hgo' : go seen target (x :: xs) = some (c, seen.length) := by
        show
          (match findComplement (target - x) seen with
            | some i => some (i, seen.length)
            | none => go ((x, seen.length) :: seen) target xs) =
          some (c, seen.length)
        rw [hfc]
      rw [hgo'] at hgo
      injection hgo with hp
      injection hp with hi hj
      obtain ⟨hij, vi, vj, hdi, hdj, hsum⟩ := hts
      rcases Nat.lt_trichotomy j done.length with hlt | heq | hgt
      · -- the pair would sit inside the processed prefix: excluded by the invariant
        have hib : i < done.length := Nat.lt_trans hij hlt
        rw [List.getElem?_append_left hib] at hdi
        rw [List.getElem?_append_left hlt] at hdj
        exact absurd ⟨hij, vi, vj, hdi, hdj, hsum⟩ (hnp i j)
      · -- `j` is the hit position: `i` is bounded by `findComplement`'s maximal index
        have hib : i < done.length := heq ▸ hij
        rw [List.getElem?_append_left hib] at hdi
        rw [heq, getElem?_append_right_zero] at hdj
        injection hdj with hxvj
        have hvi : vi = target - x := by omega
        have hmem : (target - x, i) ∈ seen := (hseen (target - x) i).mpr (hvi ▸ hdi)
        have hic : i ≤ c := hfcm (target - x) i c hmem hfc
        right
        exact ⟨by omega, by omega⟩
      · left; omega

/-- **Optimality of the returned pair**: the scan's answer is the valid pair with the smallest
    second index, and among those the largest first index — the maximum under
    "smaller `j` wins, then larger `i`". -/
theorem twoSum_opt (nums : List Int) (target : Int) (i₀ j₀ : Nat)
    (h : twoSumFn nums target = some (i₀, j₀)) :
    ∀ i j, TwoSum nums target i j → j₀ < j ∨ (j₀ = j ∧ i ≤ i₀) := by
  intro i j hts
  have hbase : SeenIff ([] : List Int) ([] : List (Int × Nat)) := by
    intro v i; simp
  have hnp0 : ∀ i j, ¬ TwoSum ([] : List Int) target i j := by
    rintro i j ⟨_, vi, vj, hdi, _⟩; simp at hdi
  have hfcm0 : FCmax [] := fun v i m hm _ => absurd hm List.not_mem_nil
  exact go_opt nums [] [] target rfl hbase hfcm0 hnp0 i₀ j₀ h i j
    (by rwa [List.nil_append])

/-! ## Running the program -/

example : twoSumFn [2, 7, 11, 15] 9 = some (0, 1) := by decide
example : twoSumFn [1, 2, 3] 100 = none := by decide
example : twoSumFn [3, 2, 4] 6 = some (1, 2) := by decide

end Freyd.Alg.RelSet.LC1
