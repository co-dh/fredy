/-
  LeetCode 977 — Squares of a Sorted Array — DERIVED as a relational HYLOMORPHISM (O(n)).

  `leet/L977.lean` takes the clean-but-quadratic "square then sort" route: `sortedSquaresFn xs =
  isort (xs.map (·²))`, correct for ANY input list (the `.`-sortedness precondition is unused) but
  O(n²) because of the insertion sort.  This file replaces it with the classic **two-pointer merge**,
  which USES the input-sortedness to run in O(n): with pointers `lo`/`hi` at the two ends of the
  (sorted) array, the LARGER of the two endpoint squares is always the maximum of the whole remaining
  segment (the squares of a sorted array form a valley, so the extremes sit at the ends).  Emit that
  larger square and move the corresponding pointer inward; the emitted values come out in DESCENDING
  order, so consing each in front of a difference-list accumulator rebuilds the ASCENDING answer in
  O(1) per step.

  The right scheme for a measured two-input / shrinking-interval recursion is the DUAL of a fold: a
  RECURSIVE COALGEBRA `c : S → L + E×S` whose unfolding is well-founded.  Instantiation here:
    * state      `S := Nat × Nat` = `(lo, hi)` (the input `Array Int` is a fixed parameter);
    * leaf       `.inl ()` when `hi < lo` (interval empty);
    * node       compare `arr[hi]²` and `arr[lo]²`; emit the larger and move that pointer inward
                 (`(lo+1,hi)` or `(lo,hi-1)`), matching `hfn`'s recurrence EXACTLY;
    * measure    `μ (lo,hi) := hi + 1 - lo`, dropping by one on each `.inr` step (`hdec`);
    * carrier    `C := List Int → List Int` (a DIFFERENCE list), base `g := id`, step
                 `st e k := fun acc => k (e :: acc)` (prepend the emitted square, O(1)).

  `emerges` runs `Hylo.hyloFold_unique` on the hand-written O(n) `hfn`: it certifies that the program
  IS the relational hylomorphism of the measured coalgebra `c` — the program was never re-written,
  only shown to satisfy the hylomorphism recurrence (discharged in place off `hfn`'s own equation).

  Correctness is a GENUINE new proof (the two-pointer is NOT the square-then-sort program): the
  emitted multiset is exactly the squares (`count_ind`, unconditional — each index is visited once),
  and the output is `Sorted` (`sorted_ind`, using the valley property and hence the input-sortedness).
  These two facts plus `LC242.sorted_eq_of_countL_eq` bridge the two-pointer output to the solved
  file's answer: `twoPtrFn arr = LC977.sortedSquaresFn arr.toList` — the O(n) program computes exactly
  the O(n²) one, so `LC977.squares_correct` carries across verbatim.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenHylo
import leet.L977

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC977D

open Freyd
open Freyd.Alg.RelSet.LC242 (Sorted countL countL_append countL_cons countL_nil sorted_eq_of_countL_eq)

/-! ## The interval `[lo..hi]` of the input list, and the bridges it needs -/

/-- `segL l lo hi` = the contiguous sub-list `[l[lo], …, l[hi]]` (empty when `hi < lo`). -/
def segL (l : List Int) (lo hi : Nat) : List Int := (l.drop lo).take (hi + 1 - lo)

/-- The program indexes the `Array` (`arr.getD i 0`, O(1)); the proofs index its `toList`.  These
    agree (both return the element in bounds, `0` out of bounds). -/
theorem getD_bridge (arr : Array Int) (i : Nat) : arr.getD i 0 = arr.toList.getD i 0 := by
  rw [Array.getD]; split
  · rename_i h; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]; simp
  · rename_i h; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]; rfl

/-- Peel the leftmost element of a non-empty interval: `[l[lo]..l[hi]] = l[lo] :: [l[lo+1]..l[hi]]`. -/
theorem segL_peel_front (l : List Int) (lo hi : Nat) (h : lo ≤ hi) (hb : hi < l.length) :
    segL l lo hi = l.getD lo 0 :: segL l (lo + 1) hi := by
  have hlo : lo < l.length := Nat.lt_of_le_of_lt h hb
  rw [segL, segL, List.drop_eq_getElem_cons hlo, show hi + 1 - lo = (hi - lo) + 1 from by omega,
    List.take_succ_cons, show hi + 1 - (lo + 1) = hi - lo from by omega]
  congr 1; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlo]; simp

/-- Peel the rightmost element of a non-empty interval: `[l[lo]..l[hi]] = [l[lo]..l[hi-1]] ++ [l[hi]]`. -/
theorem segL_peel_back (l : List Int) (lo hi : Nat) (h : lo ≤ hi) (hhi : 1 ≤ hi) (hb : hi < l.length) :
    segL l lo hi = segL l lo (hi - 1) ++ [l.getD hi 0] := by
  rw [segL, segL, show hi + 1 - lo = (hi - lo) + 1 from by omega, List.take_add_one,
    show hi - 1 + 1 - lo = hi - lo from by omega]
  congr 1
  have hget : (l.drop lo)[hi - lo]? = some (l.getD hi 0) := by
    rw [List.getElem?_drop, List.getElem?_eq_getElem (by omega : lo + (hi - lo) < l.length),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]; simp; congr 1; omega
  rw [hget]; rfl

/-! ## `Sorted` is preserved by `take`/`drop`, and bounds the extremes of an interval -/

theorem Sorted_take : ∀ (l : List Int) (n : Nat), Sorted l → Sorted (l.take n)
  | [], _, _ => by rw [List.take_nil]; trivial
  | _ :: _, 0, _ => by rw [List.take_zero]; trivial
  | a :: t, n + 1, h => by
      rw [List.take_succ_cons]
      exact ⟨fun x hx => h.1 x (List.mem_of_mem_take hx), Sorted_take t n h.2⟩

theorem Sorted_drop : ∀ (l : List Int) (n : Nat), Sorted l → Sorted (l.drop n)
  | _, 0, h => by rwa [List.drop_zero]
  | [], _ + 1, _ => by rw [List.drop_nil]; trivial
  | a :: t, n + 1, h => by rw [List.drop_succ_cons]; exact Sorted_drop t n h.2

theorem segL_sorted (l : List Int) (lo hi : Nat) (h : Sorted l) : Sorted (segL l lo hi) :=
  Sorted_take _ _ (Sorted_drop _ _ h)

/-- The last element of a sorted list is `≥` every element. -/
theorem sorted_le_last : ∀ (zs : List Int) (b : Int), Sorted (zs ++ [b]) → ∀ v ∈ zs ++ [b], v ≤ b
  | [], b, _ => by
      intro v hv; rw [List.nil_append, List.mem_singleton] at hv; exact hv ▸ Int.le_refl b
  | a :: zs, b, h => by
      intro v hv; rw [List.cons_append] at h hv
      rcases List.mem_cons.mp hv with hv | hv
      · subst hv; exact h.1 b (by rw [List.mem_append]; exact Or.inr (List.mem_singleton.mpr rfl))
      · exact sorted_le_last zs b h.2 v hv

/-! ## Squares are monotone on `≥ 0` and antitone on `≤ 0`, hence the valley property -/

theorem sq_le_of_nonneg {v b : Int} (hv : 0 ≤ v) (hvb : v ≤ b) : v * v ≤ b * b :=
  Int.mul_le_mul hvb hvb hv (Int.le_trans hv hvb)

theorem sq_le_of_nonpos {a v : Int} (hav : a ≤ v) (hv : v ≤ 0) : v * v ≤ a * a := by
  have hmul := Int.mul_le_mul (show -v ≤ -a by omega) (show -v ≤ -a by omega)
    (show (0 : Int) ≤ -v by omega) (by omega)
  rw [Int.neg_mul_neg, Int.neg_mul_neg] at hmul; exact hmul

/-- **The valley property.**  In a sorted interval the square of every element is bounded by the
    square of one of the two endpoints — the mathematical heart of the two-pointer algorithm. -/
theorem valley (l : List Int) (lo hi : Nat) (hs : Sorted l) (h : lo ≤ hi) (hb : hi < l.length)
    (v : Int) (hv : v ∈ segL l lo hi) :
    v * v ≤ (l.getD lo 0) * (l.getD lo 0) ∨ v * v ≤ (l.getD hi 0) * (l.getD hi 0) := by
  have hss := segL_sorted l lo hi hs
  have hlow : l.getD lo 0 ≤ v := by
    rw [segL_peel_front l lo hi h hb] at hss hv
    rcases List.mem_cons.mp hv with hv | hv
    · exact hv ▸ Int.le_refl _
    · exact hss.1 v hv
  have hup : v ≤ l.getD hi 0 := by
    rcases Nat.eq_zero_or_pos hi with h0 | hpos
    · subst h0; have hl0 : lo = 0 := by omega
      subst hl0
      have hsing : segL l 0 0 = [l.getD 0 0] := by
        rw [segL]; simp only [List.drop_zero]
        rw [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < l.length),
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 0 < l.length)]; simp
      rw [hsing, List.mem_singleton] at hv; exact hv ▸ Int.le_refl _
    · rw [segL_peel_back l lo hi h hpos hb] at hss hv
      exact sorted_le_last _ _ hss v hv
  rcases Int.le_total 0 v with hv0 | hv0
  · exact Or.inr (sq_le_of_nonneg hv0 hup)
  · exact Or.inl (sq_le_of_nonpos hlow hv0)

/-! ## The two-pointer program `hfn` (O(n)) and its two correctness invariants -/

/-- The two-pointer difference-list program: compare the two endpoint squares, prepend the larger to
    `acc`, and move that pointer inward.  Well-founded on `μ (lo,hi) = hi + 1 - lo`.  Reading it out
    at the initial state `(0, size-1)` with `acc = []` gives the ascending squares. -/
def hfn (arr : Array Int) : Nat → Nat → List Int → List Int
  | lo, hi, acc =>
    if hi < lo then acc
    else if (arr.getD hi 0) * (arr.getD hi 0) ≤ (arr.getD lo 0) * (arr.getD lo 0) then
      hfn arr (lo + 1) hi ((arr.getD lo 0) * (arr.getD lo 0) :: acc)
    else hfn arr lo (hi - 1) ((arr.getD hi 0) * (arr.getD hi 0) :: acc)
  termination_by lo hi => hi + 1 - lo
  decreasing_by
  · omega
  · rename_i hcond
    have hne : lo ≠ hi := by rintro rfl; exact hcond (Int.le_refl _)
    omega

/-- **Multiset invariant** (needs NO sortedness): `hfn` emits each interval element's square exactly
    once, so its count function is the interval's squared-count plus the accumulator's.  Strong
    induction on the measure `hi + 1 - lo`. -/
theorem count_ind (arr : Array Int) : ∀ (n lo hi : Nat) (acc : List Int),
    hi + 1 - lo ≤ n → hi < arr.toList.length →
    ∀ v, countL (hfn arr lo hi acc) v
       = countL ((segL arr.toList lo hi).map (fun a => a * a)) v + countL acc v := by
  intro n
  induction n with
  | zero =>
    intro lo hi acc hn hb v
    rw [hfn, if_pos (by omega)]
    have hempty : segL arr.toList lo hi = [] := by rw [segL, show hi + 1 - lo = 0 from by omega]; simp
    rw [hempty]; simp
  | succ n ih =>
    intro lo hi acc hn hb v
    rw [hfn]
    by_cases hlt : hi < lo
    · rw [if_pos hlt]
      have hempty : segL arr.toList lo hi = [] := by
        rw [segL, show hi + 1 - lo = 0 from by omega]; simp
      rw [hempty]; simp
    · rw [if_neg hlt]
      have hle : lo ≤ hi := by omega
      by_cases hcond : (arr.getD hi 0) * (arr.getD hi 0) ≤ (arr.getD lo 0) * (arr.getD lo 0)
      · rw [if_pos hcond, ih (lo + 1) hi _ (by omega) hb v, segL_peel_front arr.toList lo hi hle hb]
        simp only [List.map_cons, countL_cons, getD_bridge]; omega
      · rw [if_neg hcond]
        have hpos : 1 ≤ hi := by
          rcases Nat.eq_zero_or_pos hi with h0 | h0
          · exfalso; subst h0; have hlo0 : lo = 0 := by omega
            subst hlo0; exact hcond (Int.le_refl _)
          · exact h0
        rw [ih lo (hi - 1) _ (by omega) (by omega) v, segL_peel_back arr.toList lo hi hle hpos hb]
        simp only [List.map_append, List.map_cons, List.map_nil, countL_append, countL_cons,
          countL_nil, getD_bridge]; omega

/-- **Sortedness invariant** (uses the valley property, hence the input-sortedness): if `acc` is
    sorted and every already-emitted square dominates every remaining interval square, then the whole
    output is sorted.  Strong induction on the measure. -/
theorem sorted_ind (arr : Array Int) (hs : Sorted arr.toList) : ∀ (n lo hi : Nat) (acc : List Int),
    hi + 1 - lo ≤ n → hi < arr.toList.length → Sorted acc →
    (∀ v ∈ segL arr.toList lo hi, ∀ w ∈ acc, v * v ≤ w) →
    Sorted (hfn arr lo hi acc) := by
  intro n
  induction n with
  | zero => intro lo hi acc hn _ hacc _; rw [hfn, if_pos (by omega)]; exact hacc
  | succ n ih =>
    intro lo hi acc hn hb hacc hbnd
    rw [hfn]
    by_cases hlt : hi < lo
    · rw [if_pos hlt]; exact hacc
    · rw [if_neg hlt]
      have hle : lo ≤ hi := by omega
      have hpf := segL_peel_front arr.toList lo hi hle hb
      by_cases hcond : (arr.getD hi 0) * (arr.getD hi 0) ≤ (arr.getD lo 0) * (arr.getD lo 0)
      · rw [if_pos hcond]
        have ha_mem : arr.toList.getD lo 0 ∈ segL arr.toList lo hi := by
          rw [hpf]; exact List.mem_cons_self
        have haw : ∀ w ∈ acc, (arr.getD lo 0) * (arr.getD lo 0) ≤ w := by
          intro w hw; rw [getD_bridge]; exact hbnd _ ha_mem w hw
        refine ih (lo + 1) hi _ (by omega) hb ⟨haw, hacc⟩ ?_
        intro v hv w hw
        have hvseg : v ∈ segL arr.toList lo hi := by rw [hpf]; exact List.mem_cons.mpr (Or.inr hv)
        rcases List.mem_cons.mp hw with hw | hw
        · subst hw; rw [getD_bridge]
          rcases valley arr.toList lo hi hs hle hb v hvseg with hle' | hle'
          · exact hle'
          · simp only [getD_bridge] at hcond; exact Int.le_trans hle' hcond
        · exact hbnd v hvseg w hw
      · rw [if_neg hcond]
        have hpos : 1 ≤ hi := by
          rcases Nat.eq_zero_or_pos hi with h0 | h0
          · exfalso; subst h0; have hlo0 : lo = 0 := by omega
            subst hlo0; exact hcond (Int.le_refl _)
          · exact h0
        have hpb := segL_peel_back arr.toList lo hi hle hpos hb
        have hb_mem : arr.toList.getD hi 0 ∈ segL arr.toList lo hi := by
          rw [hpb]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
        have hbw : ∀ w ∈ acc, (arr.getD hi 0) * (arr.getD hi 0) ≤ w := by
          intro w hw; rw [getD_bridge]; exact hbnd _ hb_mem w hw
        refine ih lo (hi - 1) _ (by omega) (by omega) ⟨hbw, hacc⟩ ?_
        intro v hv w hw
        have hvseg : v ∈ segL arr.toList lo hi := by rw [hpb]; exact List.mem_append.mpr (Or.inl hv)
        rcases List.mem_cons.mp hw with hw | hw
        · subst hw; rw [getD_bridge]
          rcases valley arr.toList lo hi hs hle hb v hvseg with hle' | hle'
          · have hab : (arr.getD lo 0) * (arr.getD lo 0) ≤ (arr.getD hi 0) * (arr.getD hi 0) := by omega
            simp only [getD_bridge] at hab; exact Int.le_trans hle' hab
          · exact hle'
        · exact hbnd v hvseg w hw

/-! ## `hfn` EMERGES as the relational hylomorphism of the measured coalgebra -/

/-- The two-pointer coalgebra: leaf when the interval is empty, else emit the larger endpoint square
    and move that pointer inward.  Branch order matches `hfn`'s recurrence EXACTLY. -/
def c (arr : Array Int) : Nat × Nat → Sum Unit (Int × (Nat × Nat))
  | (lo, hi) =>
    if hi < lo then Sum.inl ()
    else if (arr.getD hi 0) * (arr.getD hi 0) ≤ (arr.getD lo 0) * (arr.getD lo 0) then
      Sum.inr ((arr.getD lo 0) * (arr.getD lo 0), (lo + 1, hi))
    else Sum.inr ((arr.getD hi 0) * (arr.getD hi 0), (lo, hi - 1))

/-- The measure: interval length `hi + 1 - lo`, dropping by one on every `.inr` step. -/
def μ : Nat × Nat → Nat := fun p => p.2 + 1 - p.1

/-- Base of the algebra: an empty interval contributes the identity difference-list. -/
def gg : Unit → (List Int → List Int) := fun _ => id

/-- Step of the algebra: prepend the emitted square to the (difference-list) tail — O(1). -/
def st : Int → (List Int → List Int) → (List Int → List Int) := fun e k acc => k (e :: acc)

/-- Every `.inr` step drops exactly one element, so `μ` strictly decreases (the well-foundedness
    witness the hylomorphism law demands).  The `hi - 1` step needs `lo < hi`, forced by the branch
    condition: at `lo = hi` the two endpoint squares are equal, so the `≤` holds and we would take the
    other branch. -/
theorem hdec (arr : Array Int) : ∀ s e s', c arr s = Sum.inr (e, s') → μ s' < μ s := by
  intro s e s' h
  obtain ⟨lo, hi⟩ := s
  simp only [c] at h
  split at h
  · nomatch h
  · split at h
    · rename_i hlt hcond
      injection h with h1; injection h1 with h2 h3; subst h3; simp only [μ]; omega
    · rename_i hlt hcond
      injection h with h1; injection h1 with h2 h3; subst h3; simp only [μ]
      have hne : lo ≠ hi := by rintro rfl; exact hcond (Int.le_refl _)
      omega

/-- **The derivation.**  The hand-written O(n) two-pointer `hfn` IS the relational hylomorphism of the
    measured coalgebra `c` with algebra `[id, prepend]` — it was never re-written; `hyloFold_unique`
    certifies it satisfies the hylomorphism recurrence, discharged in place off `hfn`'s own equation. -/
theorem emerges (arr : Array Int) :
    (graph (fun s : Nat × Nat => hfn arr s.1 s.2) :
        (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ ⟨List Int → List Int⟩)
      = Hylo.hyloR (c arr) μ (hdec arr) gg st := by
  refine Hylo.hyloFold_unique (c arr) μ (hdec arr) gg st (fun s => hfn arr s.1 s.2) ?_
  intro s
  obtain ⟨lo, hi⟩ := s
  funext acc
  show hfn arr lo hi acc = _
  rw [hfn]
  simp only [c, gg]
  split
  · rfl
  · split <;> rfl

/-! ## The certified program equals the solved file's answer (O(n) upgrade of O(n²)) -/

/-- The O(n) two-pointer answer: read `hfn` out at the whole interval `[0, size-1]` from `[]`. -/
def twoPtrFn (arr : Array Int) : List Int := hfn arr 0 (arr.size - 1) []

/-- The whole interval `[0, size-1]` is the whole list. -/
theorem segL_full (arr : Array Int) (hne : 0 < arr.size) :
    segL arr.toList 0 (arr.size - 1) = arr.toList := by
  have hlen : arr.toList.length = arr.size := by simp
  rw [segL]; simp only [List.drop_zero]
  rw [show arr.size - 1 + 1 - 0 = arr.toList.length from by rw [hlen]; omega]
  exact List.take_length

/-- The two-pointer output is sorted (via `sorted_ind`; the empty accumulator makes the domination
    hypothesis vacuous).  Uses the input-sortedness. -/
theorem twoPtr_sorted (arr : Array Int) (hne : 0 < arr.size) (hs : Sorted arr.toList) :
    Sorted (twoPtrFn arr) := by
  have hlen : arr.toList.length = arr.size := by simp
  refine sorted_ind arr hs arr.size 0 (arr.size - 1) [] (by omega) (by rw [hlen]; omega) trivial ?_
  intro v _ w hw; nomatch hw

/-- The two-pointer output is exactly the multiset of squares (via `count_ind`; no sortedness). -/
theorem twoPtr_count (arr : Array Int) (hne : 0 < arr.size) (v : Int) :
    countL (twoPtrFn arr) v = countL (arr.toList.map (fun a => a * a)) v := by
  have hlen : arr.toList.length = arr.size := by simp
  rw [twoPtrFn, count_ind arr arr.size 0 (arr.size - 1) [] (by omega) (by rw [hlen]; omega) v,
    segL_full arr hne]
  simp

/-- **The two programs agree.**  The O(n) two-pointer answer equals the O(n²) square-then-sort answer
    of `L977.lean` — both are sorted with the same squared-multiset, so `sorted_eq_of_countL_eq` forces
    equality.  Correctness (`LC977.squares_correct`) therefore carries across verbatim. -/
theorem twoPtr_eq_sortedSquares (arr : Array Int) (hne : 0 < arr.size) (hs : Sorted arr.toList) :
    twoPtrFn arr = LC977.sortedSquaresFn arr.toList :=
  sorted_eq_of_countL_eq _ _ (twoPtr_sorted arr hne hs) (LC977.squares_correct arr.toList).1
    (fun v => by rw [twoPtr_count arr hne v, (LC977.squares_correct arr.toList).2 v])

/-! ## Headline correctness -/

/-- **Headline.**  The honest bundle for the O(n) two-pointer:
    (1) the hand-written program `hfn` IS the relational hylomorphism of the measured coalgebra `c`
        with algebra `[id, prepend]` (`emerges`);
    (2) read out at `(0, size-1)` from `[]` it computes EXACTLY the solved file's answer
        `LC977.sortedSquaresFn` (an O(n) upgrade of the same function); and hence
    (3) its output is sorted and is exactly the multiset of the squared inputs — `LC977.squares_correct`
        carried across, not re-proved.  The two-pointer, unlike square-then-sort, genuinely USES the
        input-sortedness (`hs`, the LeetCode precondition). -/
theorem twoPtr_derived_correct (arr : Array Int) (hne : 0 < arr.size) (hs : Sorted arr.toList) :
    ((graph (fun s : Nat × Nat => hfn arr s.1 s.2) :
        (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ ⟨List Int → List Int⟩) = Hylo.hyloR (c arr) μ (hdec arr) gg st)
      ∧ (twoPtrFn arr = LC977.sortedSquaresFn arr.toList)
      ∧ Sorted (twoPtrFn arr)
      ∧ (∀ v, countL (twoPtrFn arr) v = countL (arr.toList.map (fun a => a * a)) v) :=
  ⟨emerges arr, twoPtr_eq_sortedSquares arr hne hs, twoPtr_sorted arr hne hs, twoPtr_count arr hne⟩

/-! ## Running the certified program

  `hfn` uses well-founded recursion (`arr.getD`/measure), so it runs but does not `decide`-reduce in
  the kernel; `#guard` evaluates the compiled program on the LeetCode 977 examples.  The equality
  `twoPtr_eq_sortedSquares` cross-checks these against the kernel-reducible `LC977.sortedSquaresFn`. -/

#guard twoPtrFn #[-4, -1, 0, 3, 10] = [0, 1, 9, 16, 100]
#guard twoPtrFn #[-7, -3, 2, 3, 11] = [4, 9, 9, 49, 121]
#guard twoPtrFn #[-5, -3, -2, -1] = [1, 4, 9, 25]

example : LC977.sortedSquaresFn [-4, -1, 0, 3, 10] = [0, 1, 9, 16, 100] := by decide
example : LC977.sortedSquaresFn [-7, -3, 2, 3, 11] = [4, 9, 9, 49, 121] := by decide

end Freyd.Alg.RelSet.LC977D
