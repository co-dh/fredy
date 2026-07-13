/-
  LeetCode 56 — Merge Intervals — as an ALLEGORY PROGRAM.

  Problem: given closed integer intervals `(lo, hi)` (each `lo ≤ hi`), merge all overlapping (or
  touching: `[1,3]`/`[3,5]` merge into `[1,5]`, using `≤` for the overlap test) intervals and
  return the non-overlapping result sorted by `lo`.

  Same recipe as `leet/L121.lean`/`leet/L20.lean` (`Fredy/leetcode.md` S0), but the data object
  is a plain `List (Int × Int)` (the recipe explicitly allows this — "or a SnocList/ConsList of
  pairs" is optional machinery, not needed here):

  1. **Data** — `List (Int × Int)`, `.1` = lo, `.2` = hi.

  2. **Program** — `mergeFn = mergeSorted ∘ isort`: `isort` (hand-rolled insertion sort by `.1`,
     the `List Int` insertion sort of `leet.L242` ported to pairs) sorts by start coordinate,
     then `mergeSorted` is a left-to-right RUN-MERGING fold over the sorted list: it keeps a
     "current running interval" `cur`, extending `cur.2` via `imax` whenever the next interval's
     `lo ≤ cur.2` (the `≤`-overlap test), or emitting `cur` and starting a new run otherwise.

  3. **Specification** — a POINT-SET relation, not an order to extremize (this is a structural-
     output problem, like `L226`'s tree-endomorphism, not an optimum): `covers ivs x` — the
     integer `x` lies inside some interval of `ivs`. The honest correctness statement is
     `IsMerge ivs out`: `out` covers exactly the same points as `ivs`, is sorted by `lo`
     (`Sorted`), has all consecutive-AND-beyond gaps strict (`GapSorted`: `a.2 < b.1` for every
     `a` before `b` in `out`, not just adjacent pairs — a stronger, more convenient induction
     invariant that implies the LeetCode-required "no two output intervals overlap or touch"),
     and is itself a list of valid intervals (`Valid`).

  4. **Correctness** — `merge_correct : Valid ivs → IsMerge ivs (mergeFn ivs)`. Proved in two
     layers: `mergeRun_inv` is the CRUX — one combined induction (S3: "prefer one conjunction over
     mutual theorems") on the sorted tail, generalizing the running interval `cur`, establishing
     FOUR invariants simultaneously (they cross-reference: `GapSorted`'s cons case needs the
     "every output `.1` is `≥` the run's `.1`" fact to bridge a strict gap past the run boundary).
     `mergeSorted_inv`/`isort`'s membership+sortedness lemmas then assemble the two composed
     stages. ALL of coverage-preservation, sortedness, AND disjointness are delivered — no
     obstruction; disjointness was NOT dropped as B-hard, because phrasing it as `GapSorted`
     (bound against the WHOLE sorted tail, not just the next element) turns out to compose with
     the same induction that already carries the running interval, at no extra cost.

  Mathlib-free, no `Classical.choice`, no `sorry`. `merge_correct` is pure `Prop`/`List`
  structural induction + `omega` (no `Rel(Set)` apparatus is even needed for the mathematical
  content); `#print axioms merge_correct` is `{propext, Quot.sound}` — inherited transitively from
  Lean core's own `List` membership lemmas (`List.mem_cons`, `List.mem_singleton`, …), not from
  anything in this file. The `Rel(Set)` packaging (`solve := graph mergeFn`) is added at the end
  per the recipe's "genuine allegory program" framing; `solve_map`/`solve_correct` carry the same
  `{propext, Quot.sound}` budget (via `graph_map`/`hom_ext`).
-/
import AOP.A6_1_RelSet

namespace Freyd.Alg.RelSet.LC56

open Freyd

/-! ## Mathlib-free `Int` max (so we control the rewrite lemmas, as in `L121`) -/

def imax (a b : Int) : Int := if a ≤ b then b else a

theorem imax_ge_left (a b : Int) : a ≤ imax a b := by unfold imax; split <;> omega
theorem imax_ge_right (a b : Int) : b ≤ imax a b := by unfold imax; split <;> omega
theorem imax_eq_or (a b : Int) : imax a b = a ∨ imax a b = b := by
  unfold imax; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## Data: intervals as a plain list of `Int × Int` (`.1` = lo, `.2` = hi) -/

/-- The object of interval lists in `Rel(Set)`. -/
abbrev Ivs : RelSet.{0} := ⟨List (Int × Int)⟩

/-- `Sorted l`: `l` is non-decreasing in `.1` — each head's `.1` is `≤` EVERY later element's `.1`
    (not just the immediate next one), so no separate transitivity/"head-below-all" lemma is
    needed downstream — it is definitional. -/
def Sorted : List (Int × Int) → Prop
  | [] => True
  | iv :: rest => (∀ jv ∈ rest, iv.1 ≤ jv.1) ∧ Sorted rest

/-- `GapSorted l`: every head's `.2` is STRICTLY below EVERY later element's `.1` — the
    (all-pairs, not just adjacent) disjointness/order invariant satisfied by `mergeFn`'s output.
    Stronger than "no two ADJACENT outputs overlap", but exactly what the run-merging induction
    produces for free, and it implies the adjacent form (and, with `Valid`, plain `Sorted` too —
    `gapSorted_sorted` below). -/
def GapSorted : List (Int × Int) → Prop
  | [] => True
  | iv :: rest => (∀ jv ∈ rest, iv.2 < jv.1) ∧ GapSorted rest

/-- Every interval in `l` is valid: `lo ≤ hi`. -/
def Valid (l : List (Int × Int)) : Prop := ∀ iv ∈ l, iv.1 ≤ iv.2

/-- `covers l x` — the point `x` lies inside SOME interval of `l`. The honest point-set meaning
    of "a list of intervals", and the notion `mergeFn` must preserve. -/
def covers (l : List (Int × Int)) (x : Int) : Prop := ∃ iv ∈ l, iv.1 ≤ x ∧ x ≤ iv.2

theorem covers_nil (x : Int) : covers ([] : List (Int × Int)) x ↔ False := by
  unfold covers
  constructor
  · rintro ⟨iv, hiv, _⟩; exact (List.not_mem_nil hiv)
  · exact False.elim

theorem covers_cons (a : Int × Int) (l : List (Int × Int)) (x : Int) :
    covers (a :: l) x ↔ (a.1 ≤ x ∧ x ≤ a.2) ∨ covers l x := by
  unfold covers
  constructor
  · rintro ⟨iv, hiv, h1, h2⟩
    rcases List.mem_cons.mp hiv with h | h
    · exact Or.inl (h ▸ ⟨h1, h2⟩)
    · exact Or.inr ⟨iv, h, h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨iv, hiv, h1, h2⟩)
    · exact ⟨a, List.mem_cons_self, h1, h2⟩
    · exact ⟨iv, List.mem_cons_of_mem a hiv, h1, h2⟩

/-- `GapSorted` (strict, all-pairs) plus `Valid` implies the weaker `Sorted` (`≤` between starts):
    a convenience corollary, not used in the main correctness chain. -/
theorem gapSorted_sorted (l : List (Int × Int)) (hval : Valid l) (hgap : GapSorted l) : Sorted l := by
  induction l with
  | nil => trivial
  | cons iv rest ih =>
    obtain ⟨hga, hgr⟩ := hgap
    refine ⟨fun jv hjv => ?_, ih (fun jv hjv => hval jv (List.mem_cons_of_mem iv hjv)) hgr⟩
    have h1 : iv.1 ≤ iv.2 := hval iv List.mem_cons_self
    have h2 : iv.2 < jv.1 := hga jv hjv
    omega

/-! ## Step 1 of the program: insertion sort by `.1` (`leet.L242`'s `linsert`/`isort` on `Int`,
    ported from a bare `Int` order to `Int × Int` compared by `.1`) -/

/-- Insert `iv` into an already-`Sorted` (by `.1`) list at the correct position. -/
def linsert (iv : Int × Int) : List (Int × Int) → List (Int × Int)
  | [] => [iv]
  | iv' :: rest => if iv.1 ≤ iv'.1 then iv :: iv' :: rest else iv' :: linsert iv rest

/-- Insertion sort by `.1`. -/
def isort : List (Int × Int) → List (Int × Int)
  | [] => []
  | iv :: rest => linsert iv (isort rest)

/-- `linsert` changes membership only by adding `iv`. -/
theorem linsert_mem (iv : Int × Int) (l : List (Int × Int)) (x : Int × Int) :
    x ∈ linsert iv l ↔ x = iv ∨ x ∈ l := by
  induction l with
  | nil => simp [linsert]
  | cons iv' rest ih =>
    show x ∈ (if iv.1 ≤ iv'.1 then iv :: iv' :: rest else iv' :: linsert iv rest) ↔ x = iv ∨ x ∈ iv' :: rest
    split
    · rw [List.mem_cons]
    · rw [List.mem_cons, ih, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- If `b ≤ iv.1` and `b` is `≤` every element of `l`, it stays `≤` every element after inserting
    `iv` — feeds `linsert_sorted`'s "keep the head-bound" step. -/
theorem linsert_allGe (iv : Int × Int) (l : List (Int × Int)) (b : Int) (hb : b ≤ iv.1)
    (hl : ∀ jv ∈ l, b ≤ jv.1) : ∀ jv ∈ linsert iv l, b ≤ jv.1 := by
  intro jv hjv
  rcases (linsert_mem iv l jv).mp hjv with h | h
  · rw [h]; exact hb
  · exact hl jv h

theorem linsert_sorted (iv : Int × Int) (l : List (Int × Int)) (hl : Sorted l) :
    Sorted (linsert iv l) := by
  induction l with
  | nil => exact ⟨fun jv hjv => (List.not_mem_nil hjv).elim, trivial⟩
  | cons iv' rest ih =>
    obtain ⟨hge, hsr⟩ := hl
    show Sorted (if iv.1 ≤ iv'.1 then iv :: iv' :: rest else iv' :: linsert iv rest)
    split
    · rename_i h
      refine ⟨fun jv hjv => ?_, hge, hsr⟩
      rcases List.mem_cons.mp hjv with h' | h'
      · rw [h']; exact h
      · have := hge jv h'; omega
    · rename_i h
      exact ⟨linsert_allGe iv rest iv'.1 (by omega) hge, ih hsr⟩

theorem isort_mem (l : List (Int × Int)) (x : Int × Int) : x ∈ isort l ↔ x ∈ l := by
  induction l with
  | nil => simp [isort]
  | cons iv rest ih =>
    show x ∈ linsert iv (isort rest) ↔ x ∈ iv :: rest
    rw [linsert_mem, ih, List.mem_cons]

theorem isort_sorted (l : List (Int × Int)) : Sorted (isort l) := by
  induction l with
  | nil => trivial
  | cons iv rest ih => exact linsert_sorted iv (isort rest) ih

theorem covers_isort (ivs : List (Int × Int)) (x : Int) : covers (isort ivs) x ↔ covers ivs x := by
  unfold covers
  constructor
  · rintro ⟨iv, hiv, h⟩; exact ⟨iv, (isort_mem ivs iv).mp hiv, h⟩
  · rintro ⟨iv, hiv, h⟩; exact ⟨iv, (isort_mem ivs iv).mpr hiv, h⟩

/-! ## Step 2 of the program: the run-merging fold over a sorted list

  `mergeRun cur rest` walks `rest` (assumed sorted, coming after `cur`), carrying the CURRENT
  running interval `cur`: if the next interval's `lo ≤ cur.2` (touches or overlaps `cur`) it
  EXTENDS `cur`'s `hi` via `imax`; otherwise it EMITS `cur` and starts a fresh run. This left-to-
  right scan-with-emission is the catamorphism the recipe calls for; `mergeSorted` seeds it from
  the sorted list's own head. -/

/-- The run-merging step: `cur` is the interval currently being extended. -/
def mergeRun (cur : Int × Int) : List (Int × Int) → List (Int × Int)
  | [] => [cur]
  | iv :: rest =>
      if iv.1 ≤ cur.2 then mergeRun (cur.1, imax cur.2 iv.2) rest else cur :: mergeRun iv rest

/-- Merge an already-`Sorted` list, seeding the run from its head. -/
def mergeSorted : List (Int × Int) → List (Int × Int)
  | [] => []
  | iv :: rest => mergeRun iv rest

/-- **The crux invariant** — one combined induction on the sorted tail `rest`, generalizing the
    running interval `cur`, establishing FOUR facts about `mergeRun cur rest` at once (they
    cross-reference: the `GapSorted` conclusion in the "emit" branch needs the "every output `.1`
    is `≥ cur.1`" fact — here specialised to the recursive call's own running interval — to bridge
    a strict gap past the emitted `cur` to every interval in the rest of the output, not just the
    immediate next one): membership-`.1`-lower-bound, output validity, output `GapSorted`-ness,
    and coverage (the output's point-set is the union of `cur`'s own span and `rest`'s). -/
theorem mergeRun_inv : ∀ (rest : List (Int × Int)) (cur : Int × Int),
    cur.1 ≤ cur.2 → (∀ iv ∈ rest, iv.1 ≤ iv.2) → (∀ iv ∈ rest, cur.1 ≤ iv.1) → Sorted rest →
    (∀ iv ∈ mergeRun cur rest, cur.1 ≤ iv.1) ∧ (∀ iv ∈ mergeRun cur rest, iv.1 ≤ iv.2) ∧
    GapSorted (mergeRun cur rest) ∧
    (∀ x, covers (mergeRun cur rest) x ↔ (cur.1 ≤ x ∧ x ≤ cur.2) ∨ covers rest x) := by
  intro rest
  induction rest with
  | nil =>
    intro cur hcv _ _ _
    have hgap : GapSorted (mergeRun cur ([] : List (Int × Int))) :=
      show GapSorted [cur] from ⟨fun jv hjv => (List.not_mem_nil hjv).elim, trivial⟩
    refine ⟨?_, ?_, hgap, ?_⟩
    · intro jv hjv
      have hjv' : jv ∈ ([cur] : List (Int × Int)) := hjv
      rw [List.mem_singleton] at hjv'; rw [hjv']; omega
    · intro jv hjv
      have hjv' : jv ∈ ([cur] : List (Int × Int)) := hjv
      rw [List.mem_singleton] at hjv'; rw [hjv']; exact hcv
    · intro x
      show covers ([cur] : List (Int × Int)) x ↔ (cur.1 ≤ x ∧ x ≤ cur.2) ∨ covers ([] : List (Int × Int)) x
      rw [covers_cons, covers_nil, or_false]
  | cons iv rest ih =>
    intro cur hcv hval hge hsort
    obtain ⟨hgehead, hsortrest⟩ := hsort
    have hvaliv : iv.1 ≤ iv.2 := hval iv List.mem_cons_self
    have hvalrest : ∀ jv ∈ rest, jv.1 ≤ jv.2 := fun jv hjv => hval jv (List.mem_cons_of_mem iv hjv)
    have hgeiv : cur.1 ≤ iv.1 := hge iv List.mem_cons_self
    show (∀ jv ∈ (if iv.1 ≤ cur.2 then mergeRun (cur.1, imax cur.2 iv.2) rest else cur :: mergeRun iv rest),
            cur.1 ≤ jv.1) ∧
         (∀ jv ∈ (if iv.1 ≤ cur.2 then mergeRun (cur.1, imax cur.2 iv.2) rest else cur :: mergeRun iv rest),
            jv.1 ≤ jv.2) ∧
         GapSorted (if iv.1 ≤ cur.2 then mergeRun (cur.1, imax cur.2 iv.2) rest else cur :: mergeRun iv rest) ∧
         (∀ x, covers (if iv.1 ≤ cur.2 then mergeRun (cur.1, imax cur.2 iv.2) rest else cur :: mergeRun iv rest) x
            ↔ (cur.1 ≤ x ∧ x ≤ cur.2) ∨ covers (iv :: rest) x)
    split
    · rename_i hext
      -- EXTEND: `iv.1 ≤ cur.2`, so `iv` merges into the running interval via `imax`.
      have hgerest' : ∀ jv ∈ rest, cur.1 ≤ jv.1 := fun jv hjv => hge jv (List.mem_cons_of_mem iv hjv)
      have hcv' : cur.1 ≤ imax cur.2 iv.2 := by have := imax_ge_left cur.2 iv.2; omega
      obtain ⟨hfst, hval', hgap', hcov'⟩ := ih (cur.1, imax cur.2 iv.2) hcv' hvalrest hgerest' hsortrest
      refine ⟨hfst, hval', hgap', fun x => ?_⟩
      rw [hcov', covers_cons]
      constructor
      · rintro (⟨h1, h2⟩ | h3)
        · rcases imax_eq_or cur.2 iv.2 with heq | heq
          · rw [heq] at h2; exact Or.inl ⟨h1, h2⟩
          · rw [heq] at h2
            by_cases hxc : x ≤ cur.2
            · exact Or.inl ⟨h1, hxc⟩
            · exact Or.inr (Or.inl ⟨by omega, h2⟩)
        · exact Or.inr (Or.inr h3)
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | h3)
        · exact Or.inl ⟨h1, by have := imax_ge_left cur.2 iv.2; omega⟩
        · exact Or.inl ⟨by omega, by have := imax_ge_right cur.2 iv.2; omega⟩
        · exact Or.inr h3
    · rename_i hnotext
      -- EMIT: `cur.2 < iv.1`, `cur` is finished; start a fresh run from `iv`.
      have hnotext' : cur.2 < iv.1 := by omega
      obtain ⟨hfst2, hval2, hgap2, hcov2⟩ := ih iv hvaliv hvalrest hgehead hsortrest
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro jv hjv
        rcases List.mem_cons.mp hjv with h | h
        · rw [h]; omega
        · have := hfst2 jv h; omega
      · intro jv hjv
        rcases List.mem_cons.mp hjv with h | h
        · rw [h]; exact hcv
        · exact hval2 jv h
      · refine ⟨fun jv hjv => ?_, hgap2⟩
        have := hfst2 jv hjv; omega
      · intro x
        rw [covers_cons, hcov2, covers_cons]

/-- Assembling `mergeRun_inv` from the sorted list's own head: `mergeSorted` produces a valid,
    `GapSorted`, coverage-preserving output. -/
theorem mergeSorted_inv (l : List (Int × Int)) (hval : Valid l) (hsort : Sorted l) :
    Valid (mergeSorted l) ∧ GapSorted (mergeSorted l) ∧ (∀ x, covers (mergeSorted l) x ↔ covers l x) := by
  cases l with
  | nil => exact ⟨fun iv h => (List.not_mem_nil h).elim, trivial, fun x => Iff.rfl⟩
  | cons iv rest =>
    have hvaliv : iv.1 ≤ iv.2 := hval iv List.mem_cons_self
    have hvalrest : ∀ jv ∈ rest, jv.1 ≤ jv.2 := fun jv hjv => hval jv (List.mem_cons_of_mem iv hjv)
    obtain ⟨hgehead, hsortrest⟩ := hsort
    obtain ⟨_, hval', hgap', hcov'⟩ := mergeRun_inv rest iv hvaliv hvalrest hgehead hsortrest
    exact ⟨hval', hgap', fun x => (hcov' x).trans (covers_cons iv rest x).symm⟩

/-! ## The program and its correctness -/

/-- **The allegory program's underlying function**: sort by `.1`, then run-merge. -/
def mergeFn (ivs : List (Int × Int)) : List (Int × Int) := mergeSorted (isort ivs)

/-- **The specification**: `out` is a faithful merge of `ivs` — same covered points, sorted,
    pairwise-disjoint (in the strong `GapSorted` sense), and itself a list of valid intervals. -/
def IsMerge (ivs out : List (Int × Int)) : Prop :=
  (∀ x, covers out x ↔ covers ivs x) ∧ Sorted out ∧ GapSorted out ∧ Valid out

/-- **Correctness (headline)**: for any list of valid intervals, `mergeFn` computes a faithful
    merge — coverage-preserving, sorted, pairwise-disjoint (`GapSorted`, hence also plain
    adjacent-non-overlap), and itself valid. Fully constructive; see the file docstring for the
    axiom count. -/
theorem merge_correct (ivs : List (Int × Int)) (hval : Valid ivs) : IsMerge ivs (mergeFn ivs) := by
  have hvs : Valid (isort ivs) := fun iv hiv => hval iv ((isort_mem ivs iv).mp hiv)
  have hss : Sorted (isort ivs) := isort_sorted ivs
  obtain ⟨hvalM, hgapM, hcovM⟩ := mergeSorted_inv (isort ivs) hvs hss
  exact ⟨fun x => (hcovM x).trans (covers_isort ivs x), gapSorted_sorted (mergeFn ivs) hvalM hgapM, hgapM, hvalM⟩

/-! ## Packaging as a genuine `Rel(Set)` morphism -/

/-- **The allegory program**: LeetCode 56's solution as a morphism `Ivs ⟶ Ivs` in `Rel(Set)`. -/
def solve : Ivs ⟶ Ivs := graph mergeFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map mergeFn

/-- **The program refines the specification** (pointwise in `Rel(Set)`): whatever `solve` relates
    `ivs` to is a faithful merge of `ivs`. -/
theorem solve_correct (ivs out : List (Int × Int)) (hval : Valid ivs) (h : solve ivs out) :
    IsMerge ivs out := by
  have hout : out = mergeFn ivs := h
  rw [hout]; exact merge_correct ivs hval

/-! ## The specification relation + honest headline (refinement — coverage does NOT pin)

  Coverage over `Int` does not pin the output: touching integer intervals like `[(1,2),(3,4)]` and
  the merged `[(1,4)]` have the SAME integer coverage and are both `Sorted`/`GapSorted`/`Valid`, yet
  differ — so `solve = spec` is FALSE.  `mergeFn` keeps them separate (it merges only OVERLAPping
  intervals, `iv.1 ≤ cur.2`).  The honest morphism statement is refinement: on valid input `solve`
  produces a faithful merge. -/

/-- **The specification** as a relation `Ivs ⟶ Ivs`: `out` is a faithful merge of `ivs`. -/
def spec : Ivs ⟶ Ivs := fun ivs out => IsMerge ivs out

/-- The precondition coreflexive passing only `Valid` interval lists. -/
def pre : Ivs ⟶ Ivs := fun ivs jvs => ivs = jvs ∧ Valid ivs

/-- **Refinement headline**: `pre ≫ solve ⊑ spec` — on valid input, whatever `solve` produces is a
    faithful merge.  (Equality fails: coverage under-determines the interval list — see above.) -/
theorem pre_solve_le_spec : pre ≫ solve ⊑ spec := by
  refine le_iff.mpr (fun ivs out h => ?_)
  obtain ⟨jvs, ⟨rfl, hval⟩, hout⟩ := h
  have hout' : out = mergeFn ivs := hout
  show IsMerge ivs out
  rw [hout']; exact merge_correct ivs hval

/-! ## Running the program -/

-- LeetCode 56's own example: `[[1,3],[2,6],[8,10],[15,18]] → [[1,6],[8,10],[15,18]]`.
example : mergeFn [(1, 3), (2, 6), (8, 10), (15, 18)] = [(1, 6), (8, 10), (15, 18)] := by decide
-- Touching intervals DO merge (`≤`, not `<`): `[[1,4],[4,5]] → [[1,5]]`.
example : mergeFn [(1, 4), (4, 5)] = [(1, 5)] := by decide
-- Unsorted input is sorted first; same answer as the first example.
example : mergeFn [(2, 6), (1, 3), (8, 10), (15, 18)] = [(1, 6), (8, 10), (15, 18)] := by decide

end Freyd.Alg.RelSet.LC56
