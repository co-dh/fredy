/-
  LeetCode 23 — Merge k Sorted Lists — an O(N log N) HEAP re-derivation (was O(k·N)).

  `Fredy/L23.lean` merges `k` sorted lists by RIGHT-FOLDING `L21`'s binary merge over the outer
  list, base `[]` (`mergeKFn lists = lists.foldr LC21.mergeFn []`).  That sequential fold rescans a
  growing accumulator on every one of the `k` cons steps, so it costs O(k·N) (`N` = total elements).

  This file replaces the PROGRAM with a min-heap heapsort of the flattened input and proves it
  correct Sorry-free, reusing `Fredy/A6_Heap.lean` (leftist min-heap over `Int`) UNMODIFIED:

    * `heapMerge lists := popN N (ofList (lists.flatten))`, `N = (lists.flatten).length`

    pour every element of every list into the heap (`ofList` = `N` inserts), then drain all `N`
    minima (`popN`).  With a leftist heap each `insert`/`popMin?` is O(log N), so the whole merge is
    O(N log N) — a genuine asymptotic win over O(k·N) once `k` is large.  (The complexity is
    INFORMAL, as in `A6_Heap`; only functional correctness is machine-checked.)

  This is option (b) of the task: a clean heapsort of the multiset, using `A6_Heap` as-is.  The
  further improvement to the textbook O(N log k) — keep only the `k` current heads in the heap and,
  after each `popMin?`, `insert` that list's NEXT element — needs a heap whose entries carry the
  REST of their list (`Int × List Int` keyed on the value), i.e. a small variant of `A6_Heap`; it is
  NOT done here to avoid duplicating the leftist-heap machinery.  Note this program is driven by an
  UNFOLD/drain loop over the heap, not a fold over the input, so the catamorphism framing is
  secondary — the deliverable is an EFFICIENT program proven correct.

  What is proved (all directly from `A6_Heap`'s exported lemmas):
    * `heapMerge_sorted`  — the output is `Sorted`, UNCONDITIONALLY (heapsort needs no sorted inputs);
    * `heapMerge_perm`    — the output is a permutation of `lists.flatten` (exact multiset);
    * `heapMerge_eq_mergeK` — on VALID (sorted) inputs it returns the IDENTICAL list to `L23.mergeKFn`
        (a genuine drop-in replacement), via `sorted_count_ext` (a sorted list is determined by its
        multiset);
    * `derivedSolve ⊑ LC23.spec` — the heap solver refines LeetCode 23's spec (sorted + summed
        multiplicity), the morphism-level statement analogous to `L23.solve_le_spec`.

  Correctness of the ORIGINAL `mergeKFn` (sortedness + exact summed multiplicity) is REUSED verbatim
  from `L23.merge_k_correct`, not re-proved.

  Mathlib-free (`import Fredy.A6_Heap` only); headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.L23
import Fredy.A6_Heap

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC23D

open Freyd Freyd.Heap

/-! ## Multiset `count` facts (all elementary `List` reasoning) -/

/-- `count` is additive over `++`. -/
theorem count_append (v : Int) (a b : List Int) :
    LC21.count v (a ++ b) = LC21.count v a + LC21.count v b := by
  induction a with
  | nil => show LC21.count v b = 0 + LC21.count v b; omega
  | cons x a ih =>
      show (if x = v then (1 : Nat) else 0) + LC21.count v (a ++ b)
         = ((if x = v then (1 : Nat) else 0) + LC21.count v a) + LC21.count v b
      rw [ih]; omega

/-- The count in the flattened input is exactly `L23.totalCount`, the sum of the per-list counts. -/
theorem count_flatten (v : Int) : ∀ lists : List (List Int),
    LC21.count v lists.flatten = LC23.totalCount v lists := by
  intro lists
  induction lists with
  | nil => rfl
  | cons l rest ih =>
      show LC21.count v (l ++ rest.flatten) = LC23.totalCount v (l :: rest)
      rw [count_append, ih]
      rfl

/-- `count` is invariant under permutation (proved by induction on the `List.Perm` derivation). -/
theorem count_perm {xs ys : List Int} (hp : List.Perm xs ys) (v : Int) :
    LC21.count v xs = LC21.count v ys := by
  induction hp with
  | nil => rfl
  | cons x hp ih => simp only [LC21.count]; rw [ih]
  | swap x y l => simp only [LC21.count]; omega
  | trans hp1 hp2 ih1 ih2 => rw [ih1, ih2]

/-- The head of a list occurs at least once. -/
theorem count_self_pos (a : Int) (l : List Int) : 0 < LC21.count a (a :: l) := by
  show 0 < (if a = a then (1 : Nat) else 0) + LC21.count a l
  rw [if_pos rfl]; omega

/-- A value with positive count is a member. -/
theorem mem_of_count_pos {v : Int} : ∀ l : List Int, 0 < LC21.count v l → v ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (Nat.lt_irrefl 0)
  | cons x xs ih =>
      intro h
      by_cases hxv : x = v
      · subst hxv; exact List.mem_cons_self
      · have e : LC21.count v (x :: xs) = LC21.count v xs := by
          show (if x = v then (1 : Nat) else 0) + LC21.count v xs = LC21.count v xs
          rw [if_neg hxv]; omega
        rw [e] at h
        exact List.mem_cons_of_mem x (ih h)

/-! ## A sorted list is determined by its multiset -/

/-- In a sorted list, the head is `≤` every other element. -/
theorem sorted_head_le : ∀ (a : Int) (l : List Int), LC21.Sorted (a :: l) → ∀ z ∈ l, a ≤ z := by
  intro a l
  induction l generalizing a with
  | nil => intro _ z hz; exact absurd hz List.not_mem_nil
  | cons c l ih =>
      intro hs z hz
      obtain ⟨hac, hScl⟩ := hs
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact hac
      · exact Int.le_trans hac (ih c hScl z hz')

/-- **Sorted lists with the same multiset are equal.**  The bridge that lets the heap output be
    identified with `L23.mergeKFn`'s: two sorted lists whose `count` agrees at every value coincide.
    Proof: matching heads must be equal (each is the minimum, so `≤` the other), then strip and
    recurse. -/
theorem sorted_count_ext : ∀ xs ys : List Int,
    LC21.Sorted xs → LC21.Sorted ys → (∀ v, LC21.count v xs = LC21.count v ys) → xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _ hc
      cases ys with
      | nil => rfl
      | cons b ys' =>
          exfalso
          have hpos := count_self_pos b ys'
          have hnil : LC21.count b ([] : List Int) = 0 := rfl
          have heq := hc b
          omega
  | cons a xs' ih =>
      intro ys hSx hSy hc
      cases ys with
      | nil =>
          exfalso
          have hpos := count_self_pos a xs'
          have hnil : LC21.count a ([] : List Int) = 0 := rfl
          have heq := hc a
          omega
      | cons b ys' =>
          have hax : ∀ z ∈ xs', a ≤ z := sorted_head_le a xs' hSx
          have hby : ∀ z ∈ ys', b ≤ z := sorted_head_le b ys' hSy
          have ha_in : a ∈ b :: ys' := by
            apply mem_of_count_pos
            have hpos := count_self_pos a xs'
            rw [hc a] at hpos; exact hpos
          have hb_in : b ∈ a :: xs' := by
            apply mem_of_count_pos
            have hpos := count_self_pos b ys'
            rw [← hc b] at hpos; exact hpos
          have hba : b ≤ a := by
            rcases List.mem_cons.mp ha_in with rfl | ha'
            · exact Int.le_refl _
            · exact hby a ha'
          have hab : a ≤ b := by
            rcases List.mem_cons.mp hb_in with rfl | hb'
            · exact Int.le_refl _
            · exact hax b hb'
          have hab_eq : a = b := Int.le_antisymm hab hba
          subst hab_eq
          have hSx' : LC21.Sorted xs' := ((LC21.sorted_cons a xs').mp hSx).2
          have hSy' : LC21.Sorted ys' := ((LC21.sorted_cons a ys').mp hSy).2
          have hc' : ∀ v, LC21.count v xs' = LC21.count v ys' := by
            intro v
            have h := hc v
            have e1 : LC21.count v (a :: xs') = (if a = v then (1 : Nat) else 0) + LC21.count v xs' := rfl
            have e2 : LC21.count v (a :: ys') = (if a = v then (1 : Nat) else 0) + LC21.count v ys' := rfl
            rw [e1, e2] at h
            omega
          rw [ih ys' hSx' hSy' hc']

/-! ## Draining the heap: sorted + permutation, straight from `A6_Heap`'s API

  All three drain lemmas induct on the fuel and reduce `popN (n+1) (node …)` DEFINITIONALLY to
  `v :: popN n (merge l r)` (`popN` is fuel-structural, not well-founded), so no unfolding lemma is
  needed — a `show` exposes the cons and the exported `popMin?_*` lemmas do the rest. -/

/-- Building a heap by repeated `insert` preserves the heap order. -/
theorem ofList_isHeap : ∀ xs : List Int, IsHeap (ofList xs)
  | [] => empty_isHeap
  | x :: xs => by
      show IsHeap (insert x (ofList xs))
      exact insert_isHeap (ofList_isHeap xs)

/-- Building a heap preserves the multiset: its elements permute the input list. -/
theorem ofList_perm : ∀ xs : List Int, List.Perm (toList (ofList xs)) xs
  | [] => List.Perm.refl _
  | x :: xs => by
      show List.Perm (toList (insert x (ofList xs))) (x :: xs)
      exact (insert_perm x (ofList xs)).trans (List.Perm.cons x (ofList_perm xs))

/-- Every element drained by `popN` came from the heap. -/
theorem popN_subset : ∀ (fuel : Nat) (h : LHeap) (x : Int), x ∈ popN fuel h → x ∈ toList h := by
  intro fuel
  induction fuel with
  | zero => intro h x hx; exact absurd hx List.not_mem_nil
  | succ n ih =>
      intro h x hx
      cases h with
      | empty => exact absurd hx List.not_mem_nil
      | node k v l r =>
          have hpop : popMin? (LHeap.node k v l r) = some (v, merge l r) := rfl
          have hperm : List.Perm (toList (LHeap.node k v l r)) (v :: toList (merge l r)) :=
            popMin?_perm hpop
          have hx' : x ∈ v :: popN n (merge l r) := hx
          rcases List.mem_cons.mp hx' with rfl | hx''
          · exact hperm.mem_iff.mpr List.mem_cons_self
          · exact hperm.mem_iff.mpr (List.mem_cons_of_mem v (ih (merge l r) x hx''))

/-- **The drain is sorted.**  Each popped minimum `v` is `≤` everything still in the heap
    (`popMin?_is_min`), hence `≤` the head of the rest of the drain (which came from the heap by
    `popN_subset`); with the tail sorted by induction, `sorted_cons` assembles `Sorted (v :: rest)`. -/
theorem popN_sorted : ∀ (fuel : Nat) (h : LHeap), IsHeap h → LC21.Sorted (popN fuel h) := by
  intro fuel
  induction fuel with
  | zero => intro h _; exact trivial
  | succ n ih =>
      intro h hh
      cases h with
      | empty => exact trivial
      | node k v l r =>
          have hpop : popMin? (LHeap.node k v l r) = some (v, merge l r) := rfl
          have hh' : IsHeap (merge l r) := popMin?_isHeap hh hpop
          have hmin : ∀ x ∈ toList (LHeap.node k v l r), v ≤ x := popMin?_is_min hh hpop
          have hperm : List.Perm (toList (LHeap.node k v l r)) (v :: toList (merge l r)) :=
            popMin?_perm hpop
          have hleHead : LC21.LeHead v (popN n (merge l r)) := by
            cases hpn : popN n (merge l r) with
            | nil => exact trivial
            | cons z t =>
                show v ≤ z
                have hz_rest : z ∈ popN n (merge l r) := by rw [hpn]; exact List.mem_cons_self
                have hz_mlr : z ∈ toList (merge l r) := popN_subset n (merge l r) z hz_rest
                exact hmin z (hperm.mem_iff.mpr (List.mem_cons_of_mem v hz_mlr))
          have hSrest : LC21.Sorted (popN n (merge l r)) := ih (merge l r) hh'
          show LC21.Sorted (v :: popN n (merge l r))
          exact (LC21.sorted_cons v _).mpr ⟨hleHead, hSrest⟩

/-- **The drain is a permutation of the heap**, when the fuel covers every element. -/
theorem popN_perm : ∀ (fuel : Nat) (h : LHeap),
    (toList h).length ≤ fuel → List.Perm (toList h) (popN fuel h) := by
  intro fuel
  induction fuel with
  | zero =>
      intro h hlen
      have hz : toList h = [] := by
        cases hE : toList h with
        | nil => rfl
        | cons a t => exfalso; rw [hE] at hlen; simp only [List.length_cons] at hlen; omega
      show List.Perm (toList h) (popN 0 h)
      rw [hz]; exact List.Perm.refl _
  | succ n ih =>
      intro h hlen
      cases h with
      | empty => exact List.Perm.refl _
      | node k v l r =>
          have hpop : popMin? (LHeap.node k v l r) = some (v, merge l r) := rfl
          have hperm : List.Perm (toList (LHeap.node k v l r)) (v :: toList (merge l r)) :=
            popMin?_perm hpop
          have hlen' : (toList (merge l r)).length ≤ n := by
            have hL := hperm.length_eq
            simp only [List.length_cons] at hL
            omega
          show List.Perm (toList (LHeap.node k v l r)) (v :: popN n (merge l r))
          exact hperm.trans (List.Perm.cons v (ih (merge l r) hlen'))

/-! ## The efficient program and its correctness -/

/-- **The O(N log N) program**: heapsort of the flattened input.  Pour every element of every list
    into a leftist min-heap (`ofList`), then drain all `N` minima (`popN`). -/
def heapMerge (lists : List (List Int)) : List Int :=
  popN lists.flatten.length (ofList lists.flatten)

/-- The heap merge is sorted — UNCONDITIONALLY (heapsort needs no assumption on the inputs). -/
theorem heapMerge_sorted (lists : List (List Int)) : LC21.Sorted (heapMerge lists) :=
  popN_sorted _ _ (ofList_isHeap lists.flatten)

/-- The heap merge is a permutation of the flattened input (exact multiset preservation). -/
theorem heapMerge_perm (lists : List (List Int)) : List.Perm (heapMerge lists) lists.flatten := by
  have hofl : List.Perm (toList (ofList lists.flatten)) lists.flatten := ofList_perm lists.flatten
  have hlen : (toList (ofList lists.flatten)).length ≤ lists.flatten.length := Nat.le_of_eq hofl.length_eq
  exact (popN_perm _ _ hlen).symm.trans hofl

/-- Consequently the heap merge realises the exact SUMMED multiplicity across all input lists. -/
theorem heapMerge_count (v : Int) (lists : List (List Int)) :
    LC21.count v (heapMerge lists) = LC23.totalCount v lists := by
  rw [count_perm (heapMerge_perm lists) v, count_flatten v lists]

/-- **Drop-in equivalence.**  On VALID (sorted) inputs the heap merge returns the IDENTICAL list to
    the original `L23.mergeKFn`: both are sorted with the same multiset, so `sorted_count_ext` forces
    them equal.  The O(N log N) heapsort is a faithful replacement for the O(k·N) sequential fold. -/
theorem heapMerge_eq_mergeK (lists : List (List Int)) (hpre : ∀ l ∈ lists, LC21.Sorted l) :
    heapMerge lists = LC23.mergeKFn lists := by
  obtain ⟨hSk, hCk⟩ := LC23.merge_k_correct lists hpre
  exact sorted_count_ext _ _ (heapMerge_sorted lists) hSk
    (fun v => (heapMerge_count v lists).trans (hCk v).symm)

/-! ## `Rel(Set)` packaging: the derived heap solver refines LeetCode 23's spec -/

/-- The derived solver as a morphism `dInput ⟶ dAns` in `Rel(Set)` — the graph of `heapMerge`. -/
def derivedSolve : LC23.dInput ⟶ LC23.dAns := graph heapMerge

/-- `derivedSolve` is a `Map` — a genuine function. -/
theorem derivedSolve_map : Map derivedSolve := graph_map heapMerge

/-- **The derived heap solver refines the LeetCode 23 specification** (the morphism-level headline,
    analogous to `L23.solve_le_spec`): every answer it returns is sorted with the summed multiplicity
    of the inputs.  In fact — heapsort — the spec's conclusion holds even without the sortedness
    precondition, so refinement is immediate from `heapMerge_sorted` and `heapMerge_count`. -/
theorem derivedSolve_refines_spec : derivedSolve ⊑ LC23.spec := by
  refine le_iff.mpr (fun lists l h => ?_)
  have hl : l = heapMerge lists := h
  subst hl
  intro _
  exact ⟨heapMerge_sorted lists, fun v => heapMerge_count v lists⟩

/-! ## Correctness headline -/

/-- **Headline** (`LC23D.merge_k_derived_correct`).  The O(N log N) heap merge:

    (1) is `Sorted` UNCONDITIONALLY (heapsort — `heapMerge_sorted`);
    (2) is a permutation of the flattened input, i.e. the EXACT multiset (`heapMerge_perm`);
    (3) on VALID (sorted) inputs returns the IDENTICAL list to the original O(k·N) `L23.mergeKFn`, a
        genuine drop-in replacement (`heapMerge_eq_mergeK`);
    (4) as a `Rel(Set)` morphism REFINES LeetCode 23's spec — sorted output with summed multiplicity
        (`derivedSolve_refines_spec`); and
    (5) the original program's correctness — sortedness AND exact summed multiplicity — is REUSED
        verbatim from `L23.merge_k_correct`, not re-proved.

    The efficient PROGRAM is the heap drain; the specification correctness is reused. -/
theorem merge_k_derived_correct :
    (∀ lists : List (List Int), LC21.Sorted (heapMerge lists))
      ∧ (∀ lists : List (List Int), List.Perm (heapMerge lists) lists.flatten)
      ∧ (∀ lists : List (List Int), (∀ l ∈ lists, LC21.Sorted l) →
           heapMerge lists = LC23.mergeKFn lists)
      ∧ (derivedSolve ⊑ LC23.spec)
      ∧ (∀ lists : List (List Int), (∀ l ∈ lists, LC21.Sorted l) →
           LC21.Sorted (LC23.mergeKFn lists) ∧
           ∀ v, LC21.count v (LC23.mergeKFn lists) = LC23.totalCount v lists) :=
  ⟨heapMerge_sorted, heapMerge_perm, heapMerge_eq_mergeK, derivedSolve_refines_spec,
   LC23.merge_k_correct⟩

/-! ## Running the heap merge

  `merge` in `A6_Heap` is well-founded, so `decide`/kernel `rfl` get stuck on any `heapMerge` result;
  we evaluate with the compiler (`#eval`) instead, as `A6_Heap` does.  Each `== …` prints `true`. -/

-- expect true: [[1,4,5],[1,3,4],[2,6]] → [1,1,2,3,4,4,5,6]
#eval heapMerge [[1, 4, 5], [1, 3, 4], [2, 6]] == [1, 1, 2, 3, 4, 4, 5, 6]
-- expect true: gaps / negatives  [[1],[],[-1,3]] → [-1,1,3]
#eval heapMerge [[1], [], [-1, 3]] == [-1, 1, 3]
-- expect true: empty input
#eval heapMerge ([] : List (List Int)) == []
-- expect true: agrees with the original L23 program on the LeetCode example
#eval heapMerge [[1, 4, 5], [1, 3, 4], [2, 6]] == LC23.mergeKFn [[1, 4, 5], [1, 3, 4], [2, 6]]

end Freyd.Alg.RelSet.LC23D
