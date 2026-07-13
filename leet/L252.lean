/-
  LeetCode 252 — Meeting Rooms — as an ALLEGORY PROGRAM.

  Problem: given meeting intervals `(lo, hi) : Int × Int` (each `lo < hi`, LeetCode 252's actual
  constraint `0 ≤ starti < endi`, the same STRICT validity as `leet/L435.lean`), decide whether a
  single person can attend ALL of them — i.e. no two meetings genuinely overlap.  Touching
  endpoints are allowed (`[5,10]`/`[10,20]` are attendable): `NoOverlap a b := a.2 ≤ b.1 ∨ b.2 ≤ a.1`.
  This is a DECISION problem (`Fredy/leetcode.md` S5), not an optimum — no `max(≤)·Λ`.

  Same recipe as `leet/L56.lean` (Merge Intervals) and `leet/L435.lean` (Non-overlapping
  Intervals): sort by START (`leet.L56`'s `isort`/`Sorted`, reused verbatim — no re-derivation),
  then a single left-to-right ADJACENT check on the sorted list.

  1. **Data** — `List (Int × Int)`, `.1` = lo, `.2` = hi (no `SnocList` engine needed).

  2. **Program** — `canAttendFn ivs := noAdj (isort ivs)`: `noAdj` seeds a threshold scan
     `noAdjFrom` from the sorted list's own head, exactly `L435`'s `keptSorted`/`keptList lastEnd`
     shape but simpler (a `Bool` fold, no witness list): `noAdjFrom lastHi (iv :: rest)` requires
     `lastHi ≤ iv.1` before recursing with the new threshold `iv.2`.

  3. **Specification** — the honest all-pairs one, `leet.L435`-style: `NonOverlap := List.Pairwise
     NoOverlap` (Lean core), not an adjacent-only predicate (which would be faithful only ON the
     sorted list, not as a spec of the ORIGINAL, unsorted input).

  4. **Correctness** — `canAttend_correct : Valid ivs → (canAttendFn ivs = true ↔ NonOverlap ivs)`,
     assembled from two independent facts, each proved on the SORTED list and bridged to the
     original input exactly once (`L435`'s discipline):
       - **`nonOverlap_isort_iff`** — `isort` is a permutation of its input (`isort_perm`, the
         classical "insertion sort permutes" induction, ported from `L435.ivs_perm_isortH` since
         `L56` exposes only `isort_mem`, not the full `List.Perm`), so `List.Perm.pairwise_iff`
         (symmetric `NoOverlap`) transports `NonOverlap` across the sort for free.
       - **`sorted_noAdj_iff`** — on a `Sorted`+`Valid` list, `noAdj = true ↔ NonOverlap`.  Forward
         (`noAdjFrom_inv`): sortedness (`.1` non-decreasing) propagates one adjacent bound
         `lastHi ≤ head.1` to `lastHi ≤ jv.1` for EVERY later `jv`, by transitivity alone — no
         validity needed.  Reverse (`noAdjFrom_of_nonOverlap`): the all-pairs `NonOverlap` gives
         `NoOverlap iv jv` at every step, and `noOverlap_lo` (using `Valid`'s STRICT `jv.1 < jv.2`
         together with sortedness `iv.1 ≤ jv.1`) rules out the OTHER disjunct
         (`jv.2 ≤ iv.1` would force `jv.2 ≤ iv.1 ≤ jv.1 < jv.2`, absurd), leaving exactly
         `iv.2 ≤ jv.1` — the one `noAdjFrom` needs.  `Valid` is load-bearing here exactly as in
         `L435`: with a non-strict `≤` (allowing zero-length meetings), a same-start pair like
         `(1,5)`/`(1,1)` is `NonOverlap` via the SECOND disjunct while failing the adjacent check.

  Mathlib-free (Lean core `Init` — `List.Pairwise`, `List.Perm` — plus `leet.L56`, itself only
  `AOP.A6_1_RelSet`).  No `Classical.choice`; axioms ⊆ {propext, Quot.sound}.
-/
import leet.L56

namespace Freyd.Alg.RelSet.LC252

open Freyd List Freyd.Alg.RelSet.LC56

/-! ## Data: intervals as a plain list of `Int × Int` (`.1` = lo, `.2` = hi) -/

/-- The object of interval lists in `Rel(Set)`. -/
abbrev Ivs : RelSet.{0} := ⟨List (Int × Int)⟩
/-- The answer object: a decision. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-- Every meeting is valid: `lo < hi`, STRICTLY — LeetCode 252's actual constraint (`0 ≤ starti <
    endi`).  Load-bearing, not cosmetic (see the file docstring): with a degenerate `lo = hi`
    meeting, the reverse direction of `sorted_noAdj_iff` has a genuine counterexample. -/
def Valid (l : List (Int × Int)) : Prop := ∀ iv ∈ l, iv.1 < iv.2

/-- Non-overlap, touching allowed (the problem's own test). -/
def NoOverlap (a b : Int × Int) : Prop := a.2 ≤ b.1 ∨ b.2 ≤ a.1

theorem noOverlap_symm {a b : Int × Int} (h : NoOverlap a b) : NoOverlap b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- `NonOverlap a b`, `a.1 ≤ b.1` (`a` sorted before `b`), and `b` `Valid` (`b.1 < b.2`, STRICT)
    together force the FIRST disjunct — the other (`b.2 ≤ a.1`) would give `b.2 ≤ a.1 ≤ b.1 < b.2`,
    absurd. -/
theorem noOverlap_lo {a b : Int × Int} (hab : a.1 ≤ b.1) (hvalb : b.1 < b.2) (h : NoOverlap a b) :
    a.2 ≤ b.1 := by
  rcases h with h | h
  · exact h
  · omega

/-- Pairwise (ALL pairs, not just adjacent) non-overlap — Lean core's `List.Pairwise` applied to
    the symmetric relation `NoOverlap`, so `Perm.pairwise_iff` transports it across the sort for
    free (`L435`'s discipline). -/
abbrev NonOverlap (l : List (Int × Int)) : Prop := List.Pairwise NoOverlap l

/-! ## `isort` is a permutation of its input (`L56` exposes only membership, not `List.Perm`;
    ported directly from `L435.ivs_perm_isortH`, `.1`-comparator instead of `.2`). -/

theorem cons_perm_linsert (iv : Int × Int) (l : List (Int × Int)) : iv :: l ~ linsert iv l := by
  induction l with
  | nil => exact List.Perm.refl [iv]
  | cons iv' rest ih =>
    show iv :: iv' :: rest ~ (if iv.1 ≤ iv'.1 then iv :: iv' :: rest else iv' :: linsert iv rest)
    split
    · exact List.Perm.refl _
    · exact (List.Perm.swap iv' iv rest).trans (ih.cons iv')

theorem isort_perm (l : List (Int × Int)) : l ~ isort l := by
  induction l with
  | nil => exact List.Perm.nil
  | cons iv rest ih =>
    show iv :: rest ~ linsert iv (isort rest)
    exact (ih.cons iv).trans (cons_perm_linsert iv (isort rest))

/-- `NonOverlap` is invariant under `isort` (via `Perm.pairwise_iff`, symmetric `NoOverlap`). -/
theorem nonOverlap_isort_iff (ivs : List (Int × Int)) :
    NonOverlap ivs ↔ NonOverlap (isort ivs) :=
  Perm.pairwise_iff (fun h => noOverlap_symm h) (isort_perm ivs)

/-! ## Step 2 of the program: the adjacent-check scan over the start-sorted list

    `noAdjFrom lastHi l` — exactly `L435.keptList lastEnd`'s shape: walk `l`, requiring the next
    head's `.1 ≥` the running threshold `lastHi`, then advance the threshold to that head's `.2`. -/

def noAdjFrom (lastHi : Int) : List (Int × Int) → Bool
  | [] => true
  | iv :: rest => if lastHi ≤ iv.1 then noAdjFrom iv.2 rest else false

/-- Seed the scan from the sorted list's own head (always attendable on its own). -/
def noAdj : List (Int × Int) → Bool
  | [] => true
  | iv :: rest => noAdjFrom iv.2 rest

/-! ### Forward: `noAdjFrom` passing propagates its threshold to EVERY later element (not just the
    immediate next one) purely via `.1`-sortedness — no `Valid` needed — and the scan passing
    implies all-pairs `NonOverlap` (`L56.mergeRun_inv`/`L435.keptList_inv`-style combined
    induction: the `NonOverlap` conclusion at each step needs the threshold-propagation fact about
    the RECURSIVE call's own tail to bridge the newly-checked head past the rest of the list). -/

theorem noAdjFrom_inv : ∀ (l : List (Int × Int)) (lastHi : Int), Sorted l →
    noAdjFrom lastHi l = true → (∀ jv ∈ l, lastHi ≤ jv.1) ∧ NonOverlap l := by
  intro l
  induction l with
  | nil => intro lastHi _ _; exact ⟨fun jv hjv => (List.not_mem_nil hjv).elim, List.Pairwise.nil⟩
  | cons iv rest ih =>
    intro lastHi hsorted hnoadj
    obtain ⟨hgehead, hsortedrest⟩ := hsorted
    have hnoadj' : (if lastHi ≤ iv.1 then noAdjFrom iv.2 rest else false) = true := hnoadj
    by_cases hle : lastHi ≤ iv.1
    · rw [if_pos hle] at hnoadj'
      obtain ⟨hge, hno⟩ := ih iv.2 hsortedrest hnoadj'
      refine ⟨fun jv hjv => ?_, List.Pairwise.cons (fun jv hjv => Or.inl (hge jv hjv)) hno⟩
      rcases List.mem_cons.mp hjv with h | h
      · rw [h]; exact hle
      · have h1 := hgehead jv h; omega
    · rw [if_neg hle] at hnoadj'; simp at hnoadj'

/-! ### Reverse: all-pairs `NonOverlap` (on a `Sorted`+`Valid` list) directly forces every adjacent
    check via `noOverlap_lo` — no propagation needed, one step suffices at a time. -/

theorem noAdjFrom_of_nonOverlap : ∀ (l : List (Int × Int)) (lastHi : Int),
    Valid l → Sorted l → (∀ jv ∈ l, lastHi ≤ jv.1) → NonOverlap l → noAdjFrom lastHi l = true := by
  intro l
  induction l with
  | nil => intro lastHi _ _ _ _; rfl
  | cons iv rest ih =>
    intro lastHi hval hsorted hge hno
    obtain ⟨hgehead, hsortedrest⟩ := hsorted
    have hleiv : lastHi ≤ iv.1 := hge iv List.mem_cons_self
    obtain ⟨hheadno, hnorest⟩ := List.pairwise_cons.mp hno
    have hvalrest : Valid rest := fun jv hjv => hval jv (List.mem_cons_of_mem iv hjv)
    have hge' : ∀ jv ∈ rest, iv.2 ≤ jv.1 := fun jv hjv =>
      noOverlap_lo (hgehead jv hjv) (hval jv (List.mem_cons_of_mem iv hjv)) (hheadno jv hjv)
    show (if lastHi ≤ iv.1 then noAdjFrom iv.2 rest else false) = true
    rw [if_pos hleiv]
    exact ih iv.2 hvalrest hsortedrest hge' hnorest

/-- **On a `Sorted`+`Valid` list, the adjacent scan decides all-pairs `NonOverlap`.** -/
theorem sorted_noAdj_iff (l : List (Int × Int)) (hsorted : Sorted l) (hval : Valid l) :
    noAdj l = true ↔ NonOverlap l := by
  cases l with
  | nil => exact ⟨fun _ => List.Pairwise.nil, fun _ => rfl⟩
  | cons iv rest =>
    obtain ⟨hgehead, hsortedrest⟩ := hsorted
    have hvalrest : Valid rest := fun jv hjv => hval jv (List.mem_cons_of_mem iv hjv)
    constructor
    · intro h
      have hrec : noAdjFrom iv.2 rest = true := h
      obtain ⟨hge, hno⟩ := noAdjFrom_inv rest iv.2 hsortedrest hrec
      exact List.Pairwise.cons (fun jv hjv => Or.inl (hge jv hjv)) hno
    · intro h
      show noAdjFrom iv.2 rest = true
      obtain ⟨hheadno, hnorest⟩ := List.pairwise_cons.mp h
      have hge2 : ∀ jv ∈ rest, iv.2 ≤ jv.1 := fun jv hjv =>
        noOverlap_lo (hgehead jv hjv) (hval jv (List.mem_cons_of_mem iv hjv)) (hheadno jv hjv)
      exact noAdjFrom_of_nonOverlap rest iv.2 hvalrest hsortedrest hge2 hnorest

/-! ## The program and its correctness -/

/-- **The allegory program's underlying function**: sort by start, then adjacent-check. -/
def canAttendFn (ivs : List (Int × Int)) : Bool := noAdj (isort ivs)

/-- **Correctness (headline)**: `canAttendFn` decides exactly whether `ivs` is pairwise
    non-overlapping. -/
theorem canAttend_correct (ivs : List (Int × Int)) (hval : Valid ivs) :
    canAttendFn ivs = true ↔ NonOverlap ivs := by
  show noAdj (isort ivs) = true ↔ NonOverlap ivs
  have hvalS : Valid (isort ivs) := fun iv hiv => hval iv ((isort_mem ivs iv).mp hiv)
  have hsortS : Sorted (isort ivs) := isort_sorted ivs
  rw [sorted_noAdj_iff (isort ivs) hsortS hvalS]
  exact (nonOverlap_isort_iff ivs).symm

/-! ## Packaging as a genuine `Rel(Set)` morphism -/

/-- **The allegory program**: LeetCode 252's solution as a morphism `Ivs ⟶ Bool` in `Rel(Set)`. -/
def solve : Ivs ⟶ dBool := graph canAttendFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map canAttendFn

/-- **The program refines the specification**: whatever `solve` relates `ivs` to is exactly the
    correct pairwise-non-overlap decision. -/
theorem solve_correct (ivs : List (Int × Int)) (hval : Valid ivs) (b : Bool) (h : solve ivs b) :
    b = true ↔ NonOverlap ivs := by
  have hb : b = canAttendFn ivs := h
  rw [hb]; exact canAttend_correct ivs hval

/-! ## Specification and the (preconditioned) decision headline -/

/-- The **specification** as a morphism `Ivs ⟶ Bool` in `Rel(Set)`: `r = true` iff the meetings are
    pairwise non-overlapping — the all-pairs `NonOverlap`, a genuine `Iff`, stated independently of
    the sorting algorithm `canAttendFn`. -/
def spec : Ivs ⟶ dBool := fun ivs r => (r = true ↔ NonOverlap ivs)

/-- The precondition coreflexive: the sub-identity carving out the WELL-FORMED inputs (every
    interval has `start < end`, LeetCode's guarantee), needed because `canAttend_correct` only
    decides `NonOverlap` on `Valid` inputs. -/
def pre : Ivs ⟶ Ivs := fun x y => x = y ∧ Valid x

/-- Two booleans that agree on being `true` are equal (Bool extensionality). -/
theorem bool_eq_of_iff_true {b c : Bool} (h : (b = true) ↔ (c = true)) : b = c := by
  cases b with
  | true => cases c with
    | true => rfl
    | false => exact (h.mp rfl).symm
  | false => cases c with
    | true => exact h.mpr rfl
    | false => rfl

/-- **Preconditioned decision headline**: restricted to `Valid` inputs (`pre`), the program `solve`
    is exactly the specification — `pre ≫ solve = pre ≫ spec`.  The precondition appears on both
    sides because `canAttendFn` decides `NonOverlap` only for well-formed intervals; off the `Valid`
    domain both composites are empty. -/
theorem pre_solve_eq_spec : pre ≫ solve = pre ≫ spec := by
  apply hom_ext; intro ivs b
  rw [comp_apply, comp_apply]
  constructor
  · rintro ⟨ivs', ⟨heq, hval⟩, hsolve⟩
    subst heq
    refine ⟨ivs, ⟨rfl, hval⟩, ?_⟩
    show b = true ↔ NonOverlap ivs
    rw [(hsolve : b = canAttendFn ivs)]; exact canAttend_correct ivs hval
  · rintro ⟨ivs', ⟨heq, hval⟩, hspec⟩
    subst heq
    refine ⟨ivs, ⟨rfl, hval⟩, ?_⟩
    show b = canAttendFn ivs
    exact bool_eq_of_iff_true ((hspec : b = true ↔ NonOverlap ivs).trans (canAttend_correct ivs hval).symm)

/-! ## Running the program -/

-- LeetCode 252's own example: `[[0,30],[5,10],[15,20]] → false` (`[0,30]` conflicts with both).
example : canAttendFn [(0, 30), (5, 10), (15, 20)] = false := by decide
-- `[[7,10],[2,4]] → true`.
example : canAttendFn [(7, 10), (2, 4)] = true := by decide
-- Touching endpoints are attendable: `[[1,5],[5,10]] → true`.
example : canAttendFn [(1, 5), (5, 10)] = true := by decide

end Freyd.Alg.RelSet.LC252
