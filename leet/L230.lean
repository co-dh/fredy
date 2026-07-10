/-
  LeetCode 230 — Kth Smallest Element in a BST — as an ALLEGORY PROGRAM.

  Problem: given the root of a BST (`Tree Int`, all labels distinct — LeetCode's guarantee) and a
  1-indexed `k`, return the `k`-th smallest label.

  Route (inorder → sorted list → index `k-1`), reusing `AOP.A6_TreeBin`'s `Tree` engine and
  `leet.L98`'s `IsBST`/`BSTwithin` as the precondition:

  1. **Program.** `inorder t` — plain structural recursion (`inorder nil = []`, `inorder (node l a
     r) = inorder l ++ a :: inorder r`, NO fuel). `kthSmallestFn t k := (inorder t)[k-1]?`.

  2. **The load-bearing lemma.** `inorder_sorted_bounded` — the `L98` (§S14) bounds-generalized
     recursion, PROVING `List.Pairwise (· < ·) (inorder t)` (strict — the ancestor-chain bounds give
     `<`, not merely `≤`) TOGETHER with "every element of `inorder t` respects the inherited bounds"
     (needed to combine grandparent-level bounds across the two recursive calls; kept as ONE
     conjunction-induction per the repo's S3 rule, not two separately re-derived theorems). Lean
     core's OWN `List.Pairwise`/`List.pairwise_append`/`List.pairwise_cons` are reused directly (no
     hand-rolled `Sorted` predicate) — `pairwise_append`'s cross-list clause is exactly the
     `Sorted (xs ++ a :: ys)` helper this route needs, closed with one `Int.lt_trans` bridging
     `x < a < y` for `x ∈ inorder l`, `y ∈ inorder r`.

  3. **Completeness (the membership bridge).** `memT` — a structural "is `x` a label of `t`"
     predicate — and `mem_inorder_iff_memT : x ∈ inorder t ↔ memT t x`, so `inorder t` is proved to
     be a faithful, order-forgetting enumeration of `t`'s own labels, not an opaque auxiliary list.

  4. **The rank characterization ("k-th smallest", pinned).** `sorted_rank` — a list-generic (tree-
     independent) fact: in a `List.Pairwise (· < ·)` list, the element at index `i` has EXACTLY `i`
     list elements `< ` it (`(xs.filter (· < v)).length = i` whenever `xs[i]? = some v`). Composed
     with `inorder_sorted_bounded`/`mem_inorder_iff_memT`, `kthSmallest_correct` shows: whenever
     `kthSmallestFn t k = some v` (`t` a `BST`), `v` is a genuine label of `t` AND exactly `k - 1`
     of `t`'s labels are strictly smaller than `v` — the precise, non-tautological meaning of
     "`v` is the `k`-th smallest label of `t`". `kthSmallest_exists` adds totality: for every `k` in
     `[1, (inorder t).length]`, `kthSmallestFn t k` is a genuine `some`.

  Honesty level achieved: FULL — sortedness (strict) + completeness (membership bridge) + rank
  (exact count-less-than) + totality on the valid range, per `Fredy/leetcode.md`'s "count-of-
  elements-`< v`" bar (not the weaker index-only fallback).

  Mathlib-free; axioms ⊆ {propext, Quot.sound} (no `Classical.choice` — every step is either
  structural recursion or a `List.Pairwise`/`getElem?`/`filter` fact from Lean core, `omega` used
  only on plain linear `Int`/`Nat` (in)equalities, never on a conjunction/negation goal — S3).
-/
import leet.L98

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC230

open Freyd Freyd.Alg.RelSet.TB
open Freyd.Alg.RelSet.LC98 (IsBST BSTwithin bstFn solve_correct)

/-! ## The program: inorder traversal (plain structural recursion, no fuel) -/

/-- The inorder traversal: left subtree, then the root label, then the right subtree. -/
def inorder : Tree Int → List Int
  | Tree.nil => []
  | Tree.node l a r => inorder l ++ a :: inorder r

@[simp] theorem inorder_nil : inorder Tree.nil = [] := rfl
theorem inorder_node (l r : Tree Int) (a : Int) :
    inorder (Tree.node l a r) = inorder l ++ a :: inorder r := rfl

/-- The answer: the label at (0-indexed) position `k - 1` of the inorder enumeration. -/
def kthSmallestFn (t : Tree Int) (k : Nat) : Option Int := (inorder t)[k - 1]?

/-! ## Completeness: `inorder` is a faithful enumeration of `t`'s own labels -/

/-- `memT t x` — `x` is a label occurring somewhere in `t` (structural tree membership). -/
def memT : Tree Int → Int → Prop
  | Tree.nil, _ => False
  | Tree.node l a r, x => x = a ∨ memT l x ∨ memT r x

theorem mem_inorder_iff_memT : ∀ (t : Tree Int) (x : Int), x ∈ inorder t ↔ memT t x
  | Tree.nil, x => by simp [inorder, memT]
  | Tree.node l a r, x => by
      have ihl := mem_inorder_iff_memT l x
      have ihr := mem_inorder_iff_memT r x
      have hx' : x ∈ inorder l ++ a :: inorder r ↔ x ∈ inorder l ∨ x = a ∨ x ∈ inorder r := by
        rw [List.mem_append, List.mem_cons]
      show x ∈ inorder l ++ a :: inorder r ↔ x = a ∨ memT l x ∨ memT r x
      rw [hx', ihl, ihr]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-! ## The load-bearing lemma: bounds ⟹ strict sortedness, `lo hi` GENERALIZED (`L98` §S14 shape)

    Proved as ONE conjunction (sortedness AND the bound facts), since the sortedness proof at a
    node needs "`inorder l` is `< a`"/"`a < inorder r`" — which are exactly the SAME facts the
    bound half produces for the child calls — so deriving them twice would be wasted work (S18). -/

theorem inorder_sorted_bounded : ∀ (lo hi : Option Int) (t : Tree Int), BSTwithin lo hi t →
    List.Pairwise (· < ·) (inorder t) ∧
      ∀ x ∈ inorder t, (∀ l0, lo = some l0 → l0 < x) ∧ (∀ h0, hi = some h0 → x < h0)
  | _, _, Tree.nil, _ => ⟨by simp [inorder], fun x hx => by simp [inorder] at hx⟩
  | lo, hi, Tree.node l a r, hbst => by
      obtain ⟨hlo, hhi, hbl, hbr⟩ := hbst
      obtain ⟨hsl, hbl'⟩ := inorder_sorted_bounded lo (some a) l hbl
      obtain ⟨hsr, hbr'⟩ := inorder_sorted_bounded (some a) hi r hbr
      -- every label in `l` is `< a`; every label in `r` is `> a` (child calls at bound `some a`)
      have hla : ∀ x ∈ inorder l, x < a := fun x hx => (hbl' x hx).2 a rfl
      have har : ∀ y ∈ inorder r, a < y := fun y hy => (hbr' y hy).1 a rfl
      have hlo_a : ∀ l0, lo = some l0 → l0 < a := by
        intro l0 heq; rw [heq] at hlo; exact hlo
      have hhi_a : ∀ h0, hi = some h0 → a < h0 := by
        intro h0 heq; rw [heq] at hhi; exact hhi
      refine ⟨?_, ?_⟩
      · show List.Pairwise (· < ·) (inorder l ++ a :: inorder r)
        rw [List.pairwise_append, List.pairwise_cons]
        refine ⟨hsl, ⟨har, hsr⟩, fun x hx b hb => ?_⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hla x hx
        · exact Int.lt_trans (hla x hx) (har b hb)
      · intro x hx
        have hx' : x ∈ inorder l ∨ x = a ∨ x ∈ inorder r := by
          have hx0 : x ∈ inorder l ++ a :: inorder r := hx
          rw [List.mem_append, List.mem_cons] at hx0; exact hx0
        rcases hx' with hx' | rfl | hx'
        · exact ⟨(hbl' x hx').1, fun h0 heq => Int.lt_trans (hla x hx') (hhi_a h0 heq)⟩
        · exact ⟨hlo_a, hhi_a⟩
        · exact ⟨fun l0 heq => Int.lt_trans (hlo_a l0 heq) (har x hx'), (hbr' x hx').2⟩

/-! ## A list-generic helper: `filter (· < v) = []` given every element is `> v` (constructive —
    `List.filter_eq_nil_iff` pulls in `Classical.choice`, so this is proved by direct structural
    recursion instead, via `List.filter_cons_of_neg` with EXPLICIT `p`/`a`/`l` — leaving them
    implicit lets `rw` try to re-derive them from the (possibly beta-reduced) hypothesis type and
    mis-unify against `decide`'s own internal application). -/

theorem filter_lt_eq_nil_of_forall_lt : ∀ (xs : List Int) (v : Int), (∀ y ∈ xs, v < y) →
    xs.filter (fun y => decide (y < v)) = []
  | [], _, _ => rfl
  | b :: s, v, hv => by
      have hvb : v < b := hv b List.mem_cons_self
      have hcond : ¬ (fun y : Int => decide (y < v)) b := by
        simp only [decide_eq_true_eq]; omega
      rw [List.filter_cons_of_neg (p := fun y : Int => decide (y < v)) (a := b) (l := s) hcond]
      exact filter_lt_eq_nil_of_forall_lt s v (fun y hy => hv y (List.mem_cons.mpr (Or.inr hy)))

/-! ## The rank lemma (list-generic, tree-independent): index ↔ count-less-than -/

/-- **The rank lemma**: in a strictly `<`-sorted list, the element at index `i` has EXACTLY `i`
    earlier (= smaller) elements — the precise "position `i` ⟺ `i` elements are `< v`" fact that
    pins down "`v` is the `(i+1)`-th smallest". -/
theorem sorted_rank : ∀ (xs : List Int) (i : Nat) (v : Int),
    List.Pairwise (· < ·) xs → xs[i]? = some v →
    (xs.filter (fun y => decide (y < v))).length = i
  | [], _, _, _, h => by simp at h
  | a :: t, 0, v, hp, h => by
      rw [List.getElem?_cons_zero] at h
      injection h with hav
      obtain ⟨ha, _⟩ := List.pairwise_cons.mp hp
      rw [← hav]
      have hnil : t.filter (fun y => decide (y < a)) = [] := filter_lt_eq_nil_of_forall_lt t a ha
      have hcond : ¬ (fun y : Int => decide (y < a)) a := by
        simp only [decide_eq_true_eq]; omega
      rw [List.filter_cons_of_neg (p := fun y : Int => decide (y < a)) (a := a) (l := t) hcond, hnil]
      rfl
  | a :: t, j + 1, v, hp, h => by
      rw [List.getElem?_cons_succ] at h
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hp
      have ihj := sorted_rank t j v ht h
      have hmem : v ∈ t := List.mem_of_getElem? h
      have hav : a < v := ha v hmem
      have hcond : (fun y : Int => decide (y < v)) a := by
        simp only [decide_eq_true_eq]; exact hav
      rw [List.filter_cons_of_pos (p := fun y : Int => decide (y < v)) (a := a) (l := t) hcond,
          List.length_cons, ihj]

/-! ## Data/answer objects in `Rel(Set)` -/

/-- The input object: a `BST` paired with the 1-indexed rank `k`. -/
abbrev dPair : RelSet.{0} := ⟨Tree Int × Nat⟩
/-- The answer object: `Option Int`, `none` only when `k` is out of range. -/
abbrev dAns : RelSet.{0} := ⟨Option Int⟩

/-- `kthSmallestFn`, uncurried to a function on `dPair`'s carrier (what `graph` needs). -/
def solveFn (p : Tree Int × Nat) : Option Int := kthSmallestFn p.1 p.2

/-- **The allegory program**: LeetCode 230's solution as a morphism `dPair ⟶ dAns` in `Rel(Set)`. -/
def solve : dPair ⟶ dAns := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## Correctness -/

/-- **The headline theorem**: whenever `kthSmallestFn` returns `some v` on a valid `BST` `t`, `v`
    is genuinely a label of `t` AND exactly `k - 1` of `t`'s labels are strictly smaller than
    `v` — the exact, non-tautological content of "`v` is the `k`-th smallest label of `t`". -/
theorem kthSmallest_correct {t : Tree Int} {k : Nat} (hbst : IsBST t) {v : Int}
    (hk : kthSmallestFn t k = some v) :
    memT t v ∧ ((inorder t).filter (fun y => decide (y < v))).length = k - 1 := by
  have hk' : (inorder t)[k - 1]? = some v := hk
  have hsorted := (inorder_sorted_bounded none none t hbst).1
  have hmem : v ∈ inorder t := List.mem_of_getElem? hk'
  exact ⟨(mem_inorder_iff_memT t v).mp hmem, sorted_rank (inorder t) (k - 1) v hsorted hk'⟩

/-- **Totality on the valid range**: for every `k` between `1` and the number of labels of `t`,
    `kthSmallestFn` genuinely returns a `some` — the program is total exactly where LeetCode's
    precondition (`1 ≤ k ≤ n`) says it should be. -/
theorem kthSmallest_exists (t : Tree Int) {k : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ (inorder t).length) :
    ∃ v, kthSmallestFn t k = some v := by
  have hlt : k - 1 < (inorder t).length := by omega
  exact ⟨(inorder t)[k - 1]'hlt, List.getElem?_eq_some_iff.mpr ⟨hlt, rfl⟩⟩

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

/-- A small sample BST:
```
        5
      /   \
     3     8
    / \     \
   2   4     9
```
-/
def sampleBST : Tree Int :=
  Tree.node (Tree.node (leaf 2) 3 (leaf 4)) 5 (Tree.node Tree.nil 8 (leaf 9))

example : IsBST sampleBST := solve_correct sampleBST |>.mp (by decide)

example : inorder sampleBST = [2, 3, 4, 5, 8, 9] := by decide
example : kthSmallestFn sampleBST 1 = some 2 := by decide
example : kthSmallestFn sampleBST 3 = some 4 := by decide
example : kthSmallestFn sampleBST 6 = some 9 := by decide
example : kthSmallestFn sampleBST 7 = none := by decide

end Freyd.Alg.RelSet.LC230
