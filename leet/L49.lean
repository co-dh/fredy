/-
  LeetCode 49 — Group Anagrams — as an ALLEGORY PROGRAM.

  Problem: given strings `strs` (each a `List Int` of character codes), partition them into
  groups so that two strings land in the same group iff they are anagrams (same multiset of
  characters).

  Same recipe as `leet/L242.lean` (Valid Anagram) — reuses its hard-won multiset machinery
  wholesale (`import leet.L242`):

  1. **Anagram key / test.** `key s := LC242.isort s` (the sorted character list). Two strings
     are anagrams iff their keys agree, `IsAnagram s t := key s = key t`. By `L242`'s
     `isort_eq_iff_countL_eq`, this is (once `key`/`isort` unfold) exactly "same character
     multiset": `key s = key t ↔ ∀ v, LC242.countL s v = LC242.countL t v` — the honest anagram
     test, delivered for free by the already-proven `L242` bridge.

  2. **Program.** `groupFn` folds `strs` right-to-left with `insertInto`: insert a string `s`
     into the FIRST existing group whose (shared) key matches `key s`; if none matches, start a
     fresh singleton group `[s]`.

  3. **Spec = an honest partition into anagram classes**, proved as `group_correct`: membership
     preserved (no string lost or invented, at the set level), every group non-empty,
     within-group homogeneity (every group is one anagram class), and across-group separation
     (anagrams never split across two different groups, so groups are FULL classes).

  4. **The real content — `GroupsWF`, an inductive well-formedness invariant** on the fold's
     running state (`List (List (List Int))`): every group is non-empty, homogeneous
     (`IsAnagram`-closed), and the groups are `List.Pairwise` cross-anagram-free (`NoCross`).
     `insertInto` preserves `GroupsWF` (`insertInto_wf`); the crux lemma is `noCross_insertInto`,
     which shows inserting a string anywhere inside a list of groups cannot break `NoCross g0 _`
     for a group `g0` whose key differs from the inserted string's key. `GroupsWF`'s
     `Pairwise`-based (POSITIONAL) form is what makes the invariant inductively self-sufficient;
     the task's membership-quantified separation statement is then read off as a corollary
     (`groupsWF_separation`), using `List.pairwise_cons` in BOTH orientations (the inserted
     element can land in either the earlier or the later of two compared groups).

  Mathlib-free (Lean core `Init` — `List.Pairwise`, `List.Perm` — plus `leet.L242`). Axioms
  target ⊆ {propext, Quot.sound} (fully constructive; no `Classical.choice`).
-/
import leet.L242

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC49

open Freyd Freyd.Alg.RelSet List

/-! ## Data: strings as plain `List Int`; a batch is `List (List Int)`; the answer is
    `List (List (List Int))` (the groups). -/

/-- The object of a batch of strings in `Rel(Set)`. -/
abbrev Strs : RelSet.{0} := ⟨List (List Int)⟩
/-- The object of a partition into groups. -/
abbrev Groups : RelSet.{0} := ⟨List (List (List Int))⟩

/-! ## The anagram key / test -/

/-- The anagram key of a string: its sorted character list (`L242`'s `isort`). -/
def key (s : List Int) : List Int := LC242.isort s

/-- Two strings are anagrams iff they share a key. By `LC242.isort_eq_iff_countL_eq` (unfolding
    `key`), this is exactly "same character multiset": `IsAnagram s t ↔ ∀ v, LC242.countL s v =
    LC242.countL t v` — the honest anagram test, for free. -/
def IsAnagram (s t : List Int) : Prop := key s = key t

/-- `IsAnagram` is symmetric. -/
theorem isAnagram_symm {s t : List Int} (h : IsAnagram s t) : IsAnagram t s := Eq.symm h

/-- `IsAnagram` is transitive. -/
theorem isAnagram_trans {s t u : List Int} (h1 : IsAnagram s t) (h2 : IsAnagram t u) :
    IsAnagram s u := Eq.trans h1 h2

/-! ## The program: fold-insert into the first key-matching group -/

/-- Insert `s` into `groups`: append it to the first existing group whose (shared) key matches
    `key s`; if none matches, append a fresh singleton group `[s]`. (`[] :: gs` cannot arise once
    started from `[]` — `GroupsWF` below rules it out — but the match must be exhaustive: skip
    over it and keep looking.) -/
def insertInto (s : List Int) : List (List (List Int)) → List (List (List Int))
  | [] => [[s]]
  | [] :: gs => [] :: insertInto s gs
  | (r :: rest) :: gs =>
      if key r = key s then (s :: r :: rest) :: gs else (r :: rest) :: insertInto s gs

/-! ### `insertInto`'s defining equations, exposed for `rw` (the `if` needs the decidability
    witness resolved via `if_pos`/`if_neg`, not bare defeq). -/

theorem insertInto_nilGroups (s : List Int) :
    insertInto s ([] : List (List (List Int))) = [[s]] := rfl

theorem insertInto_nilGroup (s : List Int) (gs : List (List (List Int))) :
    insertInto s (([] : List (List Int)) :: gs) = [] :: insertInto s gs := rfl

theorem insertInto_merge {r s : List Int} (rest : List (List Int)) (gs : List (List (List Int)))
    (hk : key r = key s) : insertInto s ((r :: rest) :: gs) = (s :: r :: rest) :: gs := by
  show (if key r = key s then (s :: r :: rest) :: gs else (r :: rest) :: insertInto s gs) = _
  rw [if_pos hk]

theorem insertInto_skip {r s : List Int} (rest : List (List Int)) (gs : List (List (List Int)))
    (hk : key r ≠ key s) :
    insertInto s ((r :: rest) :: gs) = (r :: rest) :: insertInto s gs := by
  show (if key r = key s then (s :: r :: rest) :: gs else (r :: rest) :: insertInto s gs) = _
  rw [if_neg hk]

/-- **The program**: partition `strs` into anagram groups by right-to-left fold-insert. -/
def groupFn (strs : List (List Int)) : List (List (List Int)) := strs.foldr insertInto []

/-- **The allegory program**: LeetCode 49's solution as a morphism `Strs ⟶ Groups` in `Rel(Set)`. -/
def solve : Strs ⟶ Groups := graph groupFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map groupFn

/-! ## Correctness, part 1: membership is preserved (set level) -/

/-- Inserting `s` adds exactly `s` to the flattened membership of `groups` — a `Perm`, since
    `insertInto` may drop `s` anywhere inside the list of groups. -/
theorem insertInto_flatten_perm (s : List Int) :
    ∀ groups, (insertInto s groups).flatten ~ s :: groups.flatten := by
  intro groups
  induction groups with
  | nil => rw [insertInto_nilGroups]; simp
  | cons g gs ih =>
    cases g with
    | nil =>
      rw [insertInto_nilGroup]
      simpa using ih
    | cons r rest =>
      by_cases hk : key r = key s
      · rw [insertInto_merge rest gs hk]
        exact List.Perm.of_eq (by simp [List.flatten_cons])
      · rw [insertInto_skip rest gs hk]
        simp only [List.flatten_cons]
        calc (r :: rest) ++ (insertInto s gs).flatten
            ~ (r :: rest) ++ (s :: gs.flatten) := List.Perm.append_left _ ih
          _ ~ s :: ((r :: rest) ++ gs.flatten) := List.perm_middle

theorem mem_insertInto (s x : List Int) (groups : List (List (List Int))) :
    x ∈ (insertInto s groups).flatten ↔ x = s ∨ x ∈ groups.flatten := by
  rw [(insertInto_flatten_perm s groups).mem_iff, List.mem_cons]

theorem mem_groupFn (strs : List (List Int)) (x : List Int) :
    x ∈ (groupFn strs).flatten ↔ x ∈ strs := by
  induction strs with
  | nil => simp [groupFn]
  | cons s strs ih =>
    show x ∈ (insertInto s (groupFn strs)).flatten ↔ x ∈ s :: strs
    rw [mem_insertInto, ih]
    exact List.mem_cons.symm

/-! ## The well-formedness invariant: non-empty, homogeneous, cross-anagram-free groups -/

/-- No element of `g1` is an anagram of any element of `g2`. -/
def NoCross (g1 g2 : List (List Int)) : Prop := ∀ s ∈ g1, ∀ t ∈ g2, ¬ IsAnagram s t

theorem noCross_symm {g1 g2 : List (List Int)} (h : NoCross g1 g2) : NoCross g2 g1 :=
  fun t ht s hs hts => h s hs t ht (isAnagram_symm hts)

/-- A list of groups is well-formed: every group is non-empty, homogeneous (all its elements are
    pairwise anagrams), and distinct groups (in the `List.Pairwise`, POSITIONAL sense — this is
    what makes the invariant inductively self-sufficient) share no anagram-related elements. -/
def GroupsWF (groups : List (List (List Int))) : Prop :=
  (∀ g ∈ groups, g ≠ []) ∧
  (∀ g ∈ groups, ∀ s ∈ g, ∀ t ∈ g, IsAnagram s t) ∧
  groups.Pairwise NoCross

theorem groupsWF_nil : GroupsWF ([] : List (List (List Int))) :=
  ⟨fun g h => absurd h List.not_mem_nil, fun g h => absurd h List.not_mem_nil, List.Pairwise.nil⟩

/-- Inserting `t0` anywhere inside `groups` cannot break `NoCross g0 _` for a group `g0` whose key
    disagrees with `t0`'s: `t0` can only ever join or found a group keyed by `key t0`, so it never
    lands next to `g0`. The crux lemma behind `insertInto_wf`'s separation clause. -/
theorem noCross_insertInto (t0 : List Int) (g0 : List (List Int))
    (hg0 : ∀ x ∈ g0, key x ≠ key t0) :
    ∀ groups, (∀ b ∈ groups, NoCross g0 b) → ∀ b ∈ insertInto t0 groups, NoCross g0 b := by
  intro groups
  induction groups with
  | nil =>
    intro _ b hb
    rw [insertInto_nilGroups, List.mem_singleton] at hb
    subst hb
    intro x hx y hy
    rw [List.mem_singleton] at hy
    subst hy
    exact hg0 x hx
  | cons g gs ih =>
    intro hcross b hb
    cases g with
    | nil =>
      rw [insertInto_nilGroup] at hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · intro x _hx y hy; exact absurd hy List.not_mem_nil
      · exact ih (fun b' hb' => hcross b' (List.mem_cons_of_mem _ hb')) b hb'
    | cons r rest =>
      by_cases hk : key r = key t0
      · rw [insertInto_merge rest gs hk] at hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · intro x hx y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hg0 x hx
          · exact hcross (r :: rest) List.mem_cons_self x hx y hy'
        · exact hcross b (List.mem_cons_of_mem _ hb')
      · rw [insertInto_skip rest gs hk] at hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hcross (r :: rest) List.mem_cons_self
        · exact ih (fun b' hb' => hcross b' (List.mem_cons_of_mem _ hb')) b hb'

/-- **`insertInto` preserves `GroupsWF`.** -/
theorem insertInto_wf (s : List Int) : ∀ groups, GroupsWF groups → GroupsWF (insertInto s groups) := by
  intro groups
  induction groups with
  | nil =>
    intro _
    rw [insertInto_nilGroups]
    refine ⟨?_, ?_, List.pairwise_singleton _ _⟩
    · intro g hg; rw [List.mem_singleton] at hg; subst hg; simp
    · intro g hg x hx y hy
      rw [List.mem_singleton] at hg; subst hg
      rw [List.mem_singleton] at hx hy; subst hx; subst hy
      rfl
  | cons g gs ih =>
    intro hwf
    obtain ⟨hne, hhom, hpw⟩ := hwf
    cases g with
    | nil => exact absurd rfl (hne [] List.mem_cons_self)
    | cons r rest =>
      by_cases hk : key r = key s
      · rw [insertInto_merge rest gs hk]
        refine ⟨?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_cons.mp hg' with rfl | hg''
          · simp
          · exact hne g' (List.mem_cons_of_mem _ hg'')
        · intro g' hg' x hx y hy
          rcases List.mem_cons.mp hg' with rfl | hg''
          · have hhomrest := hhom (r :: rest) List.mem_cons_self
            rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
            · rfl
            · exact isAnagram_trans (isAnagram_symm hk) (hhomrest r List.mem_cons_self y hy')
            · exact isAnagram_trans (hhomrest x hx' r List.mem_cons_self) hk
            · exact hhomrest x hx' y hy'
          · exact hhom g' (List.mem_cons_of_mem _ hg'') x hx y hy
        · rw [List.pairwise_cons] at hpw ⊢
          obtain ⟨hhead, htail⟩ := hpw
          refine ⟨?_, htail⟩
          intro b hb x hx y hy
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact fun hsy => hhead b hb r List.mem_cons_self y hy (isAnagram_trans hk hsy)
          · exact hhead b hb x hx' y hy
      · have hgnh : ∀ x ∈ (r :: rest), key x ≠ key s := by
          intro x hx heq
          exact hk (isAnagram_trans
            (isAnagram_symm (hhom (r :: rest) List.mem_cons_self x hx r List.mem_cons_self)) heq)
        have ihgs := ih ⟨fun g' hg' => hne g' (List.mem_cons_of_mem _ hg'),
            fun g' hg' => hhom g' (List.mem_cons_of_mem _ hg'), (List.pairwise_cons.mp hpw).2⟩
        rw [insertInto_skip rest gs hk]
        refine ⟨?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_cons.mp hg' with rfl | hg''
          · simp
          · exact ihgs.1 g' hg''
        · intro g' hg' x hx y hy
          rcases List.mem_cons.mp hg' with rfl | hg''
          · exact hhom (r :: rest) List.mem_cons_self x hx y hy
          · exact ihgs.2.1 g' hg'' x hx y hy
        · rw [List.pairwise_cons]
          exact ⟨noCross_insertInto s (r :: rest) hgnh gs (List.pairwise_cons.mp hpw).1, ihgs.2.2⟩

theorem groupFn_wf (strs : List (List Int)) : GroupsWF (groupFn strs) := by
  induction strs with
  | nil => exact groupsWF_nil
  | cons s strs ih => exact insertInto_wf s (groupFn strs) ih

/-- **Across-group separation**, the task's exact membership-quantified statement: read off from
    `GroupsWF`'s `Pairwise` form by a case split on which of `g1`/`g2` comes first in `groups`
    (needing `NoCross`'s symmetry, `noCross_symm`, for the "second comes first" orientation). -/
theorem groupsWF_separation : ∀ groups, GroupsWF groups →
    ∀ g1 ∈ groups, ∀ g2 ∈ groups, ∀ x ∈ g1, ∀ y ∈ g2, IsAnagram x y → g1 = g2 := by
  intro groups
  induction groups with
  | nil =>
    intro _ g1 hg1
    exact absurd hg1 List.not_mem_nil
  | cons g gs ih =>
    intro hwf g1 hg1 g2 hg2 x hx y hy hxy
    obtain ⟨hne, hhom, hpw⟩ := hwf
    rw [List.pairwise_cons] at hpw
    obtain ⟨hhead, htail⟩ := hpw
    rcases List.mem_cons.mp hg1 with rfl | hg1'
    · rcases List.mem_cons.mp hg2 with rfl | hg2'
      · rfl
      · exact absurd hxy (hhead g2 hg2' x hx y hy)
    · rcases List.mem_cons.mp hg2 with rfl | hg2'
      · exact absurd (isAnagram_symm hxy) (hhead g1 hg1' y hy x hx)
      · exact ih ⟨fun g' hg' => hne g' (List.mem_cons_of_mem _ hg'),
            fun g' hg' => hhom g' (List.mem_cons_of_mem _ hg'), htail⟩ g1 hg1' g2 hg2' x hx y hy hxy

/-! ## The headline: `groupFn` computes exactly the partition into anagram classes -/

/-- **`groupFn` is an honest partition into anagram classes.** Membership is preserved (at the
    set level — `strs` and `groupFn strs`'s flattened groups have the same elements), every group
    is non-empty, every group is homogeneous (one anagram class), and distinct groups never share
    an anagram-related pair (so groups are FULL classes, not fragments). -/
theorem group_correct (strs : List (List Int)) :
    (∀ x, x ∈ strs ↔ ∃ g ∈ groupFn strs, x ∈ g) ∧
    (∀ g ∈ groupFn strs, g ≠ []) ∧
    (∀ g ∈ groupFn strs, ∀ s ∈ g, ∀ t ∈ g, IsAnagram s t) ∧
    (∀ g1 ∈ groupFn strs, ∀ g2 ∈ groupFn strs, ∀ s ∈ g1, ∀ t ∈ g2, IsAnagram s t → g1 = g2) := by
  have hwf := groupFn_wf strs
  refine ⟨fun x => ?_, hwf.1, hwf.2.1, groupsWF_separation (groupFn strs) hwf⟩
  rw [← mem_groupFn strs x]
  exact List.mem_flatten

/-! ## Running the program -/

-- letters as distinct Ints: e=1 a=2 t=3 n=4 b=5
-- "eat"=[1,2,3] "tea"=[3,1,2] "tan"=[3,2,4] "ate"=[2,3,1] "nat"=[4,2,3] "bat"=[5,2,3]
example : groupFn [[1,2,3], [3,1,2], [3,2,4], [2,3,1], [4,2,3], [5,2,3]] =
    [[[5,2,3]], [[3,2,4],[4,2,3]], [[1,2,3],[3,1,2],[2,3,1]]] := by decide

example : groupFn ([] : List (List Int)) = [] := by decide

end Freyd.Alg.RelSet.LC49
