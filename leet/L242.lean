/-
  LeetCode 242 — Valid Anagram — as an ALLEGORY PROGRAM.

  Problem: two strings are anagrams iff they have the same multiset of characters.

  Same data/program recipe as `leet/L217.lean`/`leet/L125.lean` (`AOP.A6_SnocList`,
  `Fredy/leetcode.md` S0/S5): this is a DECISION problem, so correctness is a plain `iff`, not a
  refinement+domination extremum.

  1. **Data** — each string is the initial algebra `SnocList Int Int` (chars as `Int`); the
     answer is a *pair* of strings `⟨(SnocList Int Int) × (SnocList Int Int)⟩ ⟶ ⟨Bool⟩`.

  2. **Program (count function)** — `countOf xs c` is a fold counting how many times `c` occurs
     in `xs`.  The spec `Anagram s t := ∀ c, countOf s c = countOf t c` says "same multiset",
     but the char domain (`Int`) is infinite, so this `∀` is not directly decidable.  We DECIDE
     it via a mathlib-free canonical form: `toList` unpacks a `SnocList` into a plain `List Int`
     (as in `L125`), `isort` is hand-rolled insertion sort on `List Int`, and
     `anagramFn s t := decide (isort (toList s) = isort (toList t))` — equal *sorted* lists.

  3. **The bridge (the real work)** — `isort_eq_iff_countL_eq : isort l1 = isort l2 ↔
     ∀ x, countL l1 x = countL l2 x`.  The forward direction is easy (`isort` preserves counts,
     `countL_isort`).  The hard direction is `sorted_eq_of_countL_eq`: two `Sorted` lists with
     the same count function are equal — proved by induction, peeling off the (necessarily
     shared, by antisymmetry of `≤` on the two heads) minimum element at each step.

  4. **Correctness** — `solve_correct : anagramFn s t = true ↔ Anagram s t`, composing
     `countOf_eq_countL_toList` (bridges the `SnocList` fold to the `List` fold) with
     `isort_eq_iff_countL_eq`.  `solve = spec` then follows via `bool_eq_of_iff_true`
     (`L217`'s Bool-extensionality lemma), exactly as in `L217`/`L125`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC242

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: two strings, chars = `Int`; answer = `Bool` -/

/-- The object of a single string in `Rel(Set)` — `SnocList Int Int`. -/
abbrev Str : RelSet.{0} := dSL Int Int
/-- The object of a PAIR of strings — the input to the anagram decision. -/
abbrev Pair : RelSet.{0} := ⟨(SnocList Int Int) × (SnocList Int Int)⟩
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## `countOf` — the count-function spec (a fold): how many times does `c` occur in `xs`? -/

/-- `countOf xs c` — the number of occurrences of `c` in `xs`. -/
def countOf : SnocList Int Int → Int → Nat
  | SnocList.wrap x => fun c => if c = x then 1 else 0
  | SnocList.snoc xs q => fun c => countOf xs c + (if c = q then 1 else 0)

@[simp] theorem countOf_wrap (x c : Int) : countOf (SnocList.wrap x) c = if c = x then 1 else 0 := rfl
@[simp] theorem countOf_snoc (xs : SnocList Int Int) (q c : Int) :
    countOf (SnocList.snoc xs q) c = countOf xs c + (if c = q then 1 else 0) := rfl

/-- **The specification**: `s` and `t` are anagrams iff every character occurs the same number
    of times in both — "same multiset". -/
def Anagram (s t : SnocList Int Int) : Prop := ∀ c, countOf s c = countOf t c

/-! ## `toList` — unpack a `SnocList` into a plain `List Int` (as in `L125`) -/

/-- `toList xs` — the elements of `xs` in index order, as a plain `List Int`. -/
def toList : SnocList Int Int → List Int
  | SnocList.wrap x => [x]
  | SnocList.snoc xs q => toList xs ++ [q]

@[simp] theorem toList_wrap (x : Int) : toList (SnocList.wrap x) = [x] := rfl
@[simp] theorem toList_snoc (xs : SnocList Int Int) (q : Int) :
    toList (SnocList.snoc xs q) = toList xs ++ [q] := rfl

/-- `countL l c` — the number of occurrences of `c` in a plain `List Int` (the `List` mirror of
    `countOf`). -/
def countL : List Int → Int → Nat
  | [] => fun _ => 0
  | a :: t => fun c => countL t c + (if c = a then 1 else 0)

@[simp] theorem countL_nil (c : Int) : countL [] c = 0 := rfl
@[simp] theorem countL_cons (a : Int) (t : List Int) (c : Int) :
    countL (a :: t) c = countL t c + (if c = a then 1 else 0) := rfl

theorem countL_append (l1 l2 : List Int) (c : Int) :
    countL (l1 ++ l2) c = countL l1 c + countL l2 c := by
  induction l1 with
  | nil => simp
  | cons a t ih => simp [ih]; omega

/-- `countOf` on a `SnocList` agrees with `countL` on its unpacked `toList`. -/
theorem countOf_eq_countL_toList (xs : SnocList Int Int) (c : Int) :
    countOf xs c = countL (toList xs) c := by
  induction xs with
  | wrap x => simp
  | snoc xs q ih => simp [countL_append, ih]

/-- `Anagram`, restated via the `List`-level count function. -/
theorem anagram_iff_countL (s t : SnocList Int Int) :
    Anagram s t ↔ ∀ c, countL (toList s) c = countL (toList t) c := by
  unfold Anagram
  simp only [countOf_eq_countL_toList]

/-! ## `Sorted` and hand-rolled insertion sort on `List Int` -/

/-- A list is `Sorted` iff every element is `≤` every element to its right (recursively). -/
def Sorted : List Int → Prop
  | [] => True
  | a :: t => (∀ x ∈ t, a ≤ x) ∧ Sorted t

/-- Insert `c` into a sorted list `l`, keeping it sorted. -/
def linsert (c : Int) : List Int → List Int
  | [] => [c]
  | a :: t => if c ≤ a then c :: a :: t else a :: linsert c t

/-- Insertion sort. -/
def isort : List Int → List Int
  | [] => []
  | a :: t => linsert a (isort t)

/-! ### `linsert`/`isort` preserve the count function -/

theorem countL_linsert (c : Int) (l : List Int) (x : Int) :
    countL (linsert c l) x = countL l x + (if x = c then 1 else 0) := by
  induction l with
  | nil => simp [linsert]
  | cons a t ih =>
    show countL (if c ≤ a then c :: a :: t else a :: linsert c t) x
        = countL (a :: t) x + (if x = c then 1 else 0)
    split
    · rfl
    · show countL (linsert c t) x + (if x = a then 1 else 0)
          = countL t x + (if x = a then 1 else 0) + (if x = c then 1 else 0)
      rw [ih]; omega

theorem countL_isort (l : List Int) (x : Int) : countL (isort l) x = countL l x := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    show countL (linsert a (isort t)) x = countL t x + (if x = a then 1 else 0)
    rw [countL_linsert, ih]

/-! ### `linsert`/`isort` produce `Sorted` output -/

/-- If `a` is `≤` everything in `l`, and `a ≤ c`, then `a` is `≤` everything in `linsert c l`. -/
theorem forall_mem_linsert {a c : Int} (hac : a ≤ c) :
    ∀ (l : List Int), (∀ x ∈ l, a ≤ x) → ∀ x ∈ linsert c l, a ≤ x := by
  intro l
  induction l with
  | nil =>
    intro _hal x hx
    rcases List.mem_cons.mp (show x ∈ [c] from hx) with hx | hx
    · exact hx ▸ hac
    · nomatch hx
  | cons b t ih =>
    intro hal x hx
    show a ≤ x
    simp only [linsert] at hx
    split at hx
    · rename_i hcb
      rcases List.mem_cons.mp hx with hx | hx
      · exact hx ▸ hac
      · exact hal x hx
    · rcases List.mem_cons.mp hx with hx | hx
      · exact hx ▸ hal b List.mem_cons_self
      · exact ih (fun y hy => hal y (List.mem_cons.mpr (Or.inr hy))) x hx

theorem linsert_sorted (c : Int) (l : List Int) (hl : Sorted l) : Sorted (linsert c l) := by
  induction l with
  | nil => refine ⟨fun x hx => (nomatch hx), ?_⟩; trivial
  | cons b t ih =>
    obtain ⟨hb, hst⟩ := hl
    show Sorted (if c ≤ b then c :: b :: t else b :: linsert c t)
    split
    · rename_i h
      refine ⟨fun x hx => ?_, hb, hst⟩
      rcases List.mem_cons.mp hx with hx | hx
      · exact hx ▸ h
      · have := hb x hx; omega
    · rename_i h
      have hbc : b ≤ c := by omega
      exact ⟨forall_mem_linsert hbc t hb, ih hst⟩

theorem isort_sorted (l : List Int) : Sorted (isort l) := by
  induction l with
  | nil => trivial
  | cons a t ih => exact linsert_sorted a (isort t) ih

/-! ### The key lemma: sorted lists with the same count function are equal -/

theorem mem_iff_countL_pos (l : List Int) (x : Int) : x ∈ l ↔ 0 < countL l x := by
  induction l with
  | nil => simp
  | cons a t ih =>
    show x ∈ a :: t ↔ 0 < countL t x + (if x = a then 1 else 0)
    rw [List.mem_cons]
    constructor
    · rintro (h | h)
      · rw [if_pos h]; omega
      · have := ih.mp h; omega
    · intro h
      by_cases hxa : x = a
      · exact Or.inl hxa
      · refine Or.inr (ih.mpr ?_)
        simp [hxa] at h; omega

theorem sorted_eq_of_countL_eq : ∀ (l1 l2 : List Int), Sorted l1 → Sorted l2 →
    (∀ x, countL l1 x = countL l2 x) → l1 = l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ _ hc
    cases l2 with
    | nil => rfl
    | cons b t2 =>
      exfalso
      have h := hc b
      simp only [countL_nil, countL_cons] at h
      rw [if_pos trivial] at h
      omega
  | cons a t1 ih =>
    intro l2 h1 h2 hc
    cases l2 with
    | nil =>
      exfalso
      have h := hc a
      simp only [countL_nil, countL_cons] at h
      rw [if_pos trivial] at h
      omega
    | cons b t2 =>
      obtain ⟨ha, hst1⟩ := h1
      obtain ⟨hb, hst2⟩ := h2
      -- `b ∈ a :: t1` (its count in `l1` matches its positive count in `l2`)
      have hb_mem1 : b ∈ a :: t1 := (mem_iff_countL_pos (a :: t1) b).mpr (by
        have := hc b
        simp only [countL_cons] at this ⊢
        rw [if_pos trivial] at this
        omega)
      have hab : a ≤ b := by
        rcases List.mem_cons.mp hb_mem1 with heq | hmem
        · omega
        · exact ha b hmem
      -- `a ∈ b :: t2` (its count in `l2` matches its positive count in `l1`)
      have ha_mem2 : a ∈ b :: t2 := (mem_iff_countL_pos (b :: t2) a).mpr (by
        have := hc a
        simp only [countL_cons] at this ⊢
        rw [if_pos trivial] at this
        omega)
      have hba : b ≤ a := by
        rcases List.mem_cons.mp ha_mem2 with heq | hmem
        · omega
        · exact hb a hmem
      have hab' : a = b := by omega
      subst hab'
      have hc' : ∀ x, countL t1 x = countL t2 x := by
        intro x
        have := hc x
        simp only [countL_cons] at this
        omega
      exact congrArg (a :: ·) (ih t2 hst1 hst2 hc')

/-- **The bridge lemma**: `isort` decides multiset equality — `isort l1 = isort l2` iff `l1`, `l2`
    have the same count function. -/
theorem isort_eq_iff_countL_eq (l1 l2 : List Int) :
    isort l1 = isort l2 ↔ ∀ x, countL l1 x = countL l2 x := by
  constructor
  · intro h x
    have h1 := countL_isort l1 x
    have h2 := countL_isort l2 x
    rw [← h1, ← h2, h]
  · intro h
    exact sorted_eq_of_countL_eq (isort l1) (isort l2) (isort_sorted l1) (isort_sorted l2)
      (fun x => by rw [countL_isort, countL_isort]; exact h x)

/-! ## The program: decide sorted-list equality on the unpacked lists -/

/-- The answer function: are `s`, `t` anagrams? Decided via equal *sorted* character lists. -/
def anagramFn (s t : SnocList Int Int) : Bool := decide (isort (toList s) = isort (toList t))

/-- `anagramFn`, uncurried to a function on `Pair`'s carrier (what `graph` needs). -/
def solveFn (p : (SnocList Int Int) × (SnocList Int Int)) : Bool := anagramFn p.1 p.2

/-- **The allegory program**: LeetCode 242's solution as a morphism `Pair ⟶ Bool` in `Rel(Set)`. -/
def solve : Pair ⟶ dBool := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- **The specification** as a morphism `Pair ⟶ Bool`: `b` is THE correct boolean answer to "are
    `s`, `t` anagrams?" -/
def spec : Pair ⟶ dBool := fun p b => (b = true ↔ Anagram p.1 p.2)

/-! ## Correctness: `solve` decides `Anagram` -/

/-- **`anagramFn` decides `Anagram`**: the DECISION-problem correctness shape — an `iff`, not an
    extremum. -/
theorem solve_correct (s t : SnocList Int Int) : anagramFn s t = true ↔ Anagram s t := by
  show decide (isort (toList s) = isort (toList t)) = true ↔ Anagram s t
  rw [decide_eq_true_eq, isort_eq_iff_countL_eq, anagram_iff_countL]

/-- Two booleans that agree on being `true` are equal (Bool extensionality; cf. `L217`). -/
theorem bool_eq_of_iff_true {b c : Bool} (h : (b = true) ↔ (c = true)) : b = c := by
  cases b with
  | true => cases c with
    | true => rfl
    | false => exact (h.mp rfl).symm
  | false => cases c with
    | true => exact h.mpr rfl
    | false => rfl

/-- **`solve` equals `spec` as relations** (the allegory-program correctness statement). -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro p b
  show (b = solveFn p) ↔ (b = true ↔ Anagram p.1 p.2)
  constructor
  · intro h; rw [h]; exact solve_correct p.1 p.2
  · intro h
    have h' : (b = true) ↔ (solveFn p = true) := h.trans (solve_correct p.1 p.2).symm
    exact bool_eq_of_iff_true h'

/-! ## Running the program -/

/-- Build a string from a first character and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

-- letters encoded as distinct `Int`s: a=1 n=2 g=3 r=4 m=5 c=6 t=7
example : anagramFn (ofList 1 [2, 1, 3, 4, 1, 5]) (ofList 2 [1, 3, 1, 4, 1, 5]) = true := by
  decide  -- "anagram" / "nagaram"
example : anagramFn (ofList 4 [1, 7]) (ofList 6 [1, 4]) = false := by
  decide  -- "rat" / "car"
example : anagramFn (ofList 1 []) (ofList 1 []) = true := by decide  -- "a" / "a"

end Freyd.Alg.RelSet.LC242
