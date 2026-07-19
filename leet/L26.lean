/-
  LeetCode 26 — Remove Duplicates from Sorted Array — as an ALLEGORY PROGRAM.

  Problem: given a SORTED list `xs : List Int`, remove duplicates, returning the sorted list of
  distinct values (adjacent dedup — sortedness means every duplicate is adjacent).

  Same recipe as `leet/L56.lean`/`leet/L242.lean` (`Freyd/leetcode.md` S0): the data object is a
  plain `List Int` (no `SnocList` needed — this is a one-pass structural transform, not a fold with
  auxiliary state). Reuses `LC242.Sorted : List Int → Prop` verbatim (`import leet.L242`), the DRY
  win the recipe already flags for `Sorted`/`isort` reuse on a bare `List Int` (S22/S24/S29).

  1. **Program** `dedupFn` — structural recursion peeling a leading element that equals the next.
  2. **Specification** (given `LC242.Sorted xs`) — THREE honest clauses: membership preserved,
     output still sorted, output has no duplicates (`List.Pairwise (· ≠ ·)`, Lean core — S24/S28's
     rule: reuse core `Pairwise`, don't hand-roll).
  3. **Correctness** `dedup_correct` — all three at once. The `Pairwise (· ≠ ·)` half is where
     sortedness is load-bearing: `dedupFn` only removes ADJACENT equal elements, so getting
     "no duplicates ANYWHERE" (not just no adjacent ones) needs sortedness to promote any
     non-adjacent repeat into an adjacent one by transitivity. The crux is a "head is a strict
     lower bound of the rest" invariant (`LtHead`, the strict analogue of `L21`'s `LeHead`)
     threaded through the induction: it both drives the no-adjacent-dup step (kept elements
     differ) and supplies the strict lower bound the OUTER `Pairwise` obligation needs.

  Mathlib-free. Axioms ⊆ {propext, Quot.sound}.
-/
import leet.L242

namespace Freyd.Alg.RelSet.LC26

open Freyd Freyd.Alg.RelSet List

/-! ## Data: a sorted list of `Int`; reuse `LC242.Sorted` -/

/-- The object of number lists in `Rel(Set)`. -/
abbrev Nums : RelSet.{0} := ⟨List Int⟩

/-! ## The program: adjacent dedup -/

/-- `dedupFn xs` — drop a leading element that equals the next one; structural recursion (each
    recursive call is on the strict tail `y :: rest`). -/
def dedupFn : List Int → List Int
  | [] => []
  | [x] => [x]
  | x :: y :: rest => if x = y then dedupFn (y :: rest) else x :: dedupFn (y :: rest)

@[simp] theorem dedupFn_nil : dedupFn [] = [] := rfl
@[simp] theorem dedupFn_single (x : Int) : dedupFn [x] = [x] := rfl
theorem dedupFn_cons_cons (x y : Int) (rest : List Int) :
    dedupFn (x :: y :: rest) = if x = y then dedupFn (y :: rest) else x :: dedupFn (y :: rest) :=
  rfl

/-- **The allegory program**: LeetCode 26's solution as a morphism `Nums ⟶ Nums` in `Rel(Set)`. -/
def solve : Nums ⟶ Nums := graph dedupFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map dedupFn

/-! ## The invariant: the head of a list strictly bounds every element of the list -/

/-- `LtHead x l` — `x` is `<` every element of `l` (the strict analogue of `L21`'s `LeHead`; used
    to promote the adjacent-dedup step to a global no-duplicates fact). -/
def LtHead (x : Int) (l : List Int) : Prop := ∀ v ∈ l, x < v

theorem LtHead_nil (x : Int) : LtHead x [] := fun _ h => nomatch h

/-! ## Crux: `dedupFn` on a sorted list preserves membership, stays sorted, has no duplicates, and
    its head strictly bounds its tail — proved as ONE conjunction by structural recursion mirroring
    `dedupFn`'s own three cases (`Freyd/leetcode.md` S3: one conjunction, no mutual theorems). -/

theorem dedup_inv : ∀ xs : List Int, LC242.Sorted xs →
    (∀ v, v ∈ dedupFn xs ↔ v ∈ xs) ∧ LC242.Sorted (dedupFn xs) ∧ Pairwise (· ≠ ·) (dedupFn xs) ∧
    (∀ x l', dedupFn xs = x :: l' → LtHead x l')
  | [], _ => ⟨fun _ => Iff.rfl, trivial, Pairwise.nil, fun _ _ h => nomatch h⟩
  | [x], _ =>
    ⟨fun _ => Iff.rfl, ⟨fun v hv => (nomatch hv), trivial⟩, Pairwise.cons (fun v hv => nomatch hv) Pairwise.nil,
      fun x' l' h => by
        have h' : x :: ([] : List Int) = x' :: l' := h
        injection h' with _ h2
        subst h2
        exact LtHead_nil x'⟩
  | x :: y :: rest, hs => by
    obtain ⟨hxrest, hsrest⟩ := hs
    have hxy : x ≤ y := hxrest y mem_cons_self
    obtain ⟨ihmem, ihsorted, ihpairwise, ihlt⟩ := dedup_inv (y :: rest) hsrest
    by_cases hxy' : x = y
    · -- `dedupFn (x :: y :: rest) = dedupFn (y :: rest)`; membership needs `x` folded into `y`'s slot
      rw [dedupFn_cons_cons, if_pos hxy']
      refine ⟨fun v => ?_, ihsorted, ihpairwise, ihlt⟩
      rw [ihmem]
      constructor
      · intro hv; exact mem_cons_of_mem x hv
      · intro hv
        rcases mem_cons.mp hv with rfl | hv
        · rw [hxy']; exact mem_cons_self
        · exact hv
    · -- `dedupFn (x :: y :: rest) = x :: dedupFn (y :: rest)`; `x < y` drives the new head bound
      rw [dedupFn_cons_cons, if_neg hxy']
      have hxy_lt : x < y := by omega
      have hltnew : LtHead x (dedupFn (y :: rest)) := by
        intro v hv
        rw [ihmem] at hv
        rcases mem_cons.mp hv with rfl | hv
        · exact hxy_lt
        · have hb : y ≤ v := hsrest.1 v hv
          omega
      refine ⟨fun v => ?_, ⟨fun v hv => by have := hltnew v hv; omega, ihsorted⟩,
        Pairwise.cons (fun v hv => by have := hltnew v hv; omega) ihpairwise,
        fun x' l' h => by
          have h' : x :: dedupFn (y :: rest) = x' :: l' := h
          injection h' with h1 h2
          subst h1; subst h2
          exact hltnew⟩
      constructor
      · intro hv
        rcases mem_cons.mp hv with rfl | hv
        · exact mem_cons_self
        · exact mem_cons_of_mem x ((ihmem v).mp hv)
      · intro hv
        rcases mem_cons.mp hv with rfl | hv
        · exact mem_cons_self
        · exact mem_cons_of_mem x ((ihmem v).mpr hv)

/-! ## Correctness -/

/-- **The headline**: given `xs` sorted, `dedupFn xs` preserves membership, stays sorted, and has
    NO duplicates anywhere. `List.Nodup` IS `List.Pairwise (· ≠ ·)` by definition (Lean core,
    `nodup_iff_pairwise_ne : Nodup l ↔ Pairwise (· ≠ ·) l` is `Iff.rfl`), so `dedup_inv`'s third
    component slots in directly, no conversion lemma needed. -/
theorem dedup_correct {xs : List Int} (hs : LC242.Sorted xs) :
    (∀ v, v ∈ dedupFn xs ↔ v ∈ xs) ∧ LC242.Sorted (dedupFn xs) ∧ (dedupFn xs).Nodup := by
  obtain ⟨h1, h2, h3, _⟩ := dedup_inv xs hs
  exact ⟨h1, h2, h3⟩

/-! ## The morphism-equation headline (sorted + nodup + membership pins the output) -/

/-- **Sorted-nodup extensionality**: two `Sorted`, duplicate-free lists with the same membership
    are equal.  Heads coincide (both are the minimum, by mutual `≤`); `Nodup` strips the head from
    each tail's membership so the induction goes through.  This is the uniqueness that lets the
    membership/sorted/nodup spec pin the dedup output. -/
theorem sorted_nodup_ext : ∀ (o1 o2 : List Int),
    LC242.Sorted o1 → o1.Nodup → LC242.Sorted o2 → o2.Nodup →
    (∀ v, v ∈ o1 ↔ v ∈ o2) → o1 = o2 := by
  intro o1
  induction o1 with
  | nil =>
    intro o2 _ _ _ _ hmem
    cases o2 with
    | nil => rfl
    | cons y ys => exact absurd ((hmem y).mpr mem_cons_self) not_mem_nil
  | cons x xs ih =>
    intro o2 hs1 hn1 hs2 hn2 hmem
    cases o2 with
    | nil => exact absurd ((hmem x).mp mem_cons_self) not_mem_nil
    | cons y ys =>
      obtain ⟨hx_le, hs1'⟩ := hs1
      obtain ⟨hy_le, hs2'⟩ := hs2
      have hxy : x = y := by
        have hxley : x ≤ y := by
          rcases mem_cons.mp ((hmem y).mpr mem_cons_self) with h | h
          · omega
          · exact hx_le y h
        have hylex : y ≤ x := by
          rcases mem_cons.mp ((hmem x).mp mem_cons_self) with h | h
          · omega
          · exact hy_le x h
        exact Int.le_antisymm hxley hylex
      subst hxy
      obtain ⟨hxni1, hn1'⟩ := List.nodup_cons.mp hn1
      obtain ⟨hxni2, hn2'⟩ := List.nodup_cons.mp hn2
      have hmem' : ∀ v, v ∈ xs ↔ v ∈ ys := by
        intro v; constructor
        · intro hv
          rcases mem_cons.mp ((hmem v).mp (mem_cons_of_mem x hv)) with h | h
          · exact absurd (h ▸ hv) hxni1
          · exact h
        · intro hv
          rcases mem_cons.mp ((hmem v).mpr (mem_cons_of_mem x hv)) with h | h
          · exact absurd (h ▸ hv) hxni2
          · exact h
      rw [ih ys hs1' hn1' hs2' hn2' hmem']

/-- The precondition coreflexive: the sub-identity passing only `Sorted` inputs (LeetCode 26's
    "sorted array" precondition — adjacent dedup is only correct when equal values are adjacent). -/
def pre : Nums ⟶ Nums := fun xs ys => xs = ys ∧ LC242.Sorted xs

/-- **The specification** as a morphism `Nums ⟶ Nums`: on a `Sorted` input, `out` has exactly the
    same elements, is itself `Sorted`, and has no duplicates — the honest "distinct values in order"
    reading, stated independently of `dedupFn`. -/
def spec : Nums ⟶ Nums :=
  fun xs out => LC242.Sorted xs ∧ (∀ v, v ∈ out ↔ v ∈ xs) ∧ LC242.Sorted out ∧ out.Nodup

/-- **The allegory-program headline**: `pre ≫ solve = spec` — restricted to sorted inputs, the
    adjacent-dedup fold is exactly the "sorted distinct values" spec, pinned by `sorted_nodup_ext`. -/
theorem pre_solve_eq_spec : pre ≫ solve = spec := by
  apply hom_ext; intro xs out
  constructor
  · rintro ⟨ys, ⟨rfl, hsort⟩, hv⟩
    have hv' : out = dedupFn xs := hv
    obtain ⟨hm, hso, hnd⟩ := dedup_correct hsort
    rw [hv']; exact ⟨hsort, hm, hso, hnd⟩
  · rintro ⟨hsort, hmem, hsout, hndout⟩
    refine ⟨xs, ⟨rfl, hsort⟩, ?_⟩
    show out = dedupFn xs
    obtain ⟨hm, hso, hnd⟩ := dedup_correct hsort
    exact sorted_nodup_ext out (dedupFn xs) hsout hndout hso hnd (fun v => (hmem v).trans (hm v).symm)

/-! ## Running the program -/

example : dedupFn [1, 1, 2] = [1, 2] := by decide
example : dedupFn [0, 0, 1, 1, 1, 2, 2] = [0, 1, 2] := by decide

end Freyd.Alg.RelSet.LC26
