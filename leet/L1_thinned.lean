/-
  LeetCode 1 — Two Sum — DERIVED from its relational SPEC by the THINNING theorem (B&dM Cor 8.1).

  `leet/L1.lean` verifies a hand-written scan; `leet/L1_derived.lean` reshapes it onto the cons-list
  initial algebra (fold-uniqueness) and swaps in the hash map.  NEITHER derives the algorithm from
  the specification.  This file does, with `rel/AutoDeriveThin.lean`'s `ThinBest` driver — the
  mechanised THEOREM 8.1 / Corollary 8.1 (`AOP/A8_1.lean`), whose abstract program
  `⦇Λ(S·F∈)·thin Q⦈ ≫ min R` is a fold whose accumulator is a POWER-OBJECT point (the kept
  candidate set), pruned at every step:

  1. **Search space** (`tsB`): scanning left to right, a candidate is `start` (no commitment),
     `part k v` (first leg picked at index `k`, value `v`, waiting for its complement), or
     `found i j` (a finished pair).  The generator's reachable states are EXACTLY the spec
     (`gen_char`): `found i j` is generatable iff `LC1.TwoSum nums target i j`.

  2. **Thinning order `Q`** — the algorithmic content of the scan, as Pareto dominance:
     * same-value partials collapse — `part k' v ⊑ part k v` for `k' ≤ k` (any completion of the
       older leg is matched by the same completion of the newer one, second index equal, first
       index larger) — this is WHY the seen-map keeps ONE index per value, the most recent;
     * a `found i j` dominates everything once `j` is past (`j < n`) — any pair completed later
       has a strictly larger second index — this is WHY the scan may return at the first hit.
     Corollary 8.1 turns `Q` into the program `foldFn` (extend all kept candidates, prune) +
     final `R`-pick, and certifies it: the pick is the `R`-maximum of ALL generatable states.

  3. **Selection order `R`**: on outcomes `none < some (i, j)`, smaller `j` wins, then larger `i`
     (`ansLe`).  The derived program `thinTwoSum` therefore returns the valid pair with the
     SMALLEST second index, largest first index — and `leet/L1.lean`'s `twoSum_opt` shows the
     hand scan returns that same canonical pair, so they are EQUAL (`thin_eq_scan`), hence equal
     to the `O(n)` hash program (`thin_eq_hash`, via `LC1D.hashTwoSum_eq`).

  4. **Headline** (`solve_eq_A_maxRel`, the `leet/L53.lean` form): the allegory program
     `LC1.solve` IS `A tsSpec ≫ maxRel D` — B&dM's `max D · Λ spec`, the function DERIVED from
     the relational spec, as a morphism equation in `Rel(Set)`.

  What the allegory does NOT see: the O(1)-expected bucket lookup inside `AHashMap`.  Thinning
  licenses the ABSTRACT algorithm (one index per value + early return); the hash map is a data
  refinement below relation algebra, proved separately in `leet/L1_derived.lean`.

  Mathlib-free.  Axioms ⊆ {propext, Classical.choice, Quot.sound} (`Classical.choice` inherited
  from `cataR_eq_relCata` through Cor 8.1, as in `RunningBest`/`ThinBest`); the scan-side
  optimality `LC1.twoSum_opt` is fully constructive.
-/
import rel.AutoDeriveThin
import leet.L1_derived

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC1T

open Freyd Freyd.Alg.RelSet.SL

/-! ## Candidate states and the two orders -/

/-- A partial solution of the left-to-right scan. -/
inductive TSChoice where
  | start : TSChoice                -- no first leg committed yet
  | part  : Nat → Int → TSChoice    -- first leg at index `k` holding value `v`
  | found : Nat → Nat → TSChoice    -- a finished pair `(i, j)`

/-- The answer a state stands for. -/
def outc : TSChoice → Option (Nat × Nat)
  | .found i j => some (i, j)
  | _ => none

/-- The selection preorder on answers: `none` is worst; among pairs, smaller second index wins,
    then larger first index (`ansLe z w` = "`w` at least as good as `z`", the `minRel`
    convention).  This is the order under which the scan's answer is the maximum. -/
def ansLe : Option (Nat × Nat) → Option (Nat × Nat) → Prop
  | none, _ => True
  | some _, none => False
  | some (i, j), some (i', j') => j' < j ∨ (j' = j ∧ i ≤ i')

/-- Boolean test for `ansLe` (total). -/
def ansLeB : Option (Nat × Nat) → Option (Nat × Nat) → Bool
  | none, _ => true
  | some _, none => false
  | some (i, j), some (i', j') => decide (j' < j ∨ (j' = j ∧ i ≤ i'))

theorem ansLe_trans : ∀ {a b c : Option (Nat × Nat)}, ansLe a b → ansLe b c → ansLe a c := by
  intro a b c hab hbc
  match a, b, c with
  | none, _, _ => trivial
  | some _, none, _ => exact hab.elim
  | some _, some _, none => exact hbc.elim
  | some (i, j), some (i', j'), some (i'', j'') =>
    have h1 : j' < j ∨ (j' = j ∧ i ≤ i') := hab
    have h2 : j'' < j' ∨ (j'' = j' ∧ i' ≤ i'') := hbc
    show j'' < j ∨ (j'' = j ∧ i ≤ i'')
    omega

theorem ansLe_antisym : ∀ {a b : Option (Nat × Nat)}, ansLe a b → ansLe b a → a = b := by
  intro a b hab hba
  match a, b with
  | none, none => rfl
  | none, some _ => exact hba.elim
  | some _, none => exact hab.elim
  | some (i, j), some (i', j') =>
    have h1 : j' < j ∨ (j' = j ∧ i ≤ i') := hab
    have h2 : j < j' ∨ (j = j' ∧ i' ≤ i) := hba
    have : i = i' ∧ j = j' := by omega
    rw [this.1, this.2]

theorem ansLeB_true : ∀ {a b : Option (Nat × Nat)}, ansLeB a b = true → ansLe a b := by
  intro a b h
  match a, b with
  | none, _ => trivial
  | some _, none => exact absurd h (by simp [ansLeB])
  | some (i, j), some (i', j') =>
    have h' : j' < j ∨ (j' = j ∧ i ≤ i') := of_decide_eq_true h
    exact h'

theorem ansLeB_false : ∀ {a b : Option (Nat × Nat)}, ansLeB b a = false → ansLe a b := by
  intro a b h
  match a, b with
  | none, _ => trivial
  | some _, none => exact absurd h (by simp [ansLeB])
  | some (i, j), some (i', j') =>
    have hn : ¬ (j < j' ∨ (j = j' ∧ i' ≤ i)) := of_decide_eq_false h
    show j' < j ∨ (j' = j ∧ i ≤ i')
    omega

/-- The thinning preorder at scan position `n` (`Qc n z w` = "`w` dominates `z`"): same-value
    partials with a larger index dominate; a finished pair with `j < n` dominates every
    unfinished state (any later completion has second index `≥ n > j`); finished pairs compare
    by the answer order. -/
def Qc (n : Nat) : TSChoice → TSChoice → Prop
  | .start, .start => True
  | .part k v, .part k' v' => v' = v ∧ k ≤ k'
  | .start, .found _ j => j < n
  | .part _ _, .found _ j => j < n
  | .found i j, .found i' j' => j' < j ∨ (j' = j ∧ i ≤ i')
  | _, _ => False

/-- Boolean test for `Qc` (soundness is all the prune needs). -/
def qcB (n : Nat) : TSChoice → TSChoice → Bool
  | .start, .start => true
  | .part k v, .part k' v' => decide (v' = v) && decide (k ≤ k')
  | .start, .found _ j => decide (j < n)
  | .part _ _, .found _ j => decide (j < n)
  | .found i j, .found i' j' => decide (j' < j ∨ (j' = j ∧ i ≤ i'))
  | _, _ => false

theorem qcB_sound {n : Nat} : ∀ {c c'}, qcB n c c' = true → Qc n c c' := by
  intro c c' h
  match c, c' with
  | .start, .start => trivial
  | .part k v, .part k' v' =>
    have h' : (decide (v' = v) && decide (k ≤ k')) = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    exact h'
  | .start, .found i j =>
    have h' : j < n := of_decide_eq_true h
    exact h'
  | .part k v, .found i j =>
    have h' : j < n := of_decide_eq_true h
    exact h'
  | .found i j, .found i' j' =>
    have h' : j' < j ∨ (j' = j ∧ i ≤ i') := of_decide_eq_true h
    exact h'
  | .start, .part _ _ => exact absurd h (by simp [qcB])
  | .part _ _, .start => exact absurd h (by simp [qcB])
  | .found _ _, .start => exact absurd h (by simp [qcB])
  | .found _ _, .part _ _ => exact absurd h (by simp [qcB])

theorem Qc_refl {n : Nat} : ∀ c, Qc n c c := by
  intro c
  match c with
  | .start => trivial
  | .part k v => exact ⟨rfl, Nat.le_refl _⟩
  | .found i j => exact Or.inr ⟨rfl, Nat.le_refl _⟩

theorem Qc_trans {n : Nat} : ∀ {a b c}, Qc n a b → Qc n b c → Qc n a c := by
  intro a b c hab hbc
  match a, b, c with
  | .start, .start, .start => trivial
  | .start, .start, .found i j => exact hbc
  | .start, .found i1 j1, .found i j =>
    -- `.start ⊑ found(i₁,j₁) ⊑ found(i,j)`: `j ≤ j₁ < n`
    have h1 : j1 < n := hab
    have h2 : j < j1 ∨ (j = j1 ∧ i1 ≤ i) := hbc
    show j < n
    omega
  | .part k v, .part k' v', .part k'' v'' =>
    obtain ⟨hv1, hk1⟩ := hab
    obtain ⟨hv2, hk2⟩ := hbc
    exact ⟨hv2.trans hv1, Nat.le_trans hk1 hk2⟩
  | .part k v, .part k' v', .found i j => exact hbc
  | .part k v, .found i1 j1, .found i j =>
    have h1 : j1 < n := hab
    have h2 : j < j1 ∨ (j = j1 ∧ i1 ≤ i) := hbc
    show j < n
    omega
  | .found i1 j1, .found i2 j2, .found i j =>
    have h1 : j2 < j1 ∨ (j2 = j1 ∧ i1 ≤ i2) := hab
    have h2 : j < j2 ∨ (j = j2 ∧ i2 ≤ i) := hbc
    show j < j1 ∨ (j = j1 ∧ i1 ≤ i)
    omega
  -- everything else has a `False` hypothesis
  | .start, .part _ _, _ => exact hab.elim
  | .part _ _, .start, _ => exact hab.elim
  | .found _ _, .start, _ => exact hab.elim
  | .found _ _, .part _ _, _ => exact hab.elim
  | .start, .found _ _, .start => exact hbc.elim
  | .start, .found _ _, .part _ _ => exact hbc.elim
  | .part _ _, .found _ _, .start => exact hbc.elim
  | .part _ _, .found _ _, .part _ _ => exact hbc.elim
  | .start, .start, .part _ _ => exact hbc.elim
  | .part _ _, .part _ _, .start => exact hbc.elim
  | .found _ _, .found _ _, .start => exact hbc.elim
  | .found _ _, .found _ _, .part _ _ => exact hbc.elim

theorem Qc_le_ansLe {n : Nat} : ∀ {c c'}, Qc n c c' → ansLe (outc c) (outc c') := by
  intro c c' h
  match c, c' with
  | .start, .start => trivial
  | .part _ _, .part _ _ => trivial
  | .start, .found _ _ => trivial
  | .part _ _, .found _ _ => trivial
  | .found i j, .found i' j' => exact h
  | .start, .part _ _ => exact h.elim
  | .part _ _, .start => exact h.elim
  | .found _ _, .start => exact h.elim
  | .found _ _, .part _ _ => exact h.elim

/-! ## The thinning bundle: the CREATIVE inputs of the derivation (B&dM ch. 8) -/

/-- The Two Sum thinning bundle at a fixed `target`.  Leaf = the uncommitted scan; a step at
    element `x` (arriving at index `n`, the state's counter) lets `start` stay or commit the
    new element as a first leg, lets a partial stay or — when its complement arrived — finish,
    and keeps a finished pair.  `step_mono` is the §8.1 insight, case by case. -/
def tsB (target : Int) : ThinBest Unit Int (Nat × TSChoice) where
  leafOne _ := [(0, .start)]
  stepOne s x :=
    match s with
    | (n, .start) => [(n + 1, .start), (n + 1, .part n x)]
    | (n, .part k v) =>
      if v + x = target then [(n + 1, .part k v), (n + 1, .found k n)]
      else [(n + 1, .part k v)]
    | (n, .found i j) => [(n + 1, .found i j)]
  Q z w := z.1 = w.1 ∧ Qc z.1 z.2 w.2
  R z w := ansLe (outc z.2) (outc w.2)
  qDec z w := decide (z.1 = w.1) && qcB z.1 z.2 w.2
  rDec z w := ansLeB (outc w.2) (outc z.2)
  Q_refl s := ⟨rfl, Qc_refl s.2⟩
  Q_trans := by
    rintro s t u ⟨h1, hq1⟩ ⟨h2, hq2⟩
    refine ⟨h1.trans h2, ?_⟩
    rw [h1] at hq1 ⊢
    exact Qc_trans hq1 hq2
  Q_le_R := by
    rintro s t ⟨-, hq⟩
    exact Qc_le_ansLe hq
  R_trans := fun h1 h2 => ansLe_trans h1 h2
  qDec_sound := by
    intro s t h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, qcB_sound h.2⟩
  rDec_t := fun h => ansLeB_true h
  rDec_f := fun h => ansLeB_false h
  step_mono := by
    intro s s' x y hQ hy
    obtain ⟨n, c⟩ := s
    obtain ⟨n', c'⟩ := s'
    obtain ⟨hn, hqc⟩ := hQ
    -- `subst` on `n = n'` eliminates `n'`, keeping the dominator's counter name `n`
    have hn2 : n = n' := (hn : n' = n).symm
    subst hn2
    match c', c with
    | .start, .start =>
      -- the dominator generates the same two extensions: match `y` with itself
      exact ⟨y, hy, rfl, Qc_refl y.2⟩
    | .part k' v', .part k v =>
      obtain ⟨hv, hk⟩ := (hqc : v = v' ∧ k' ≤ k)
      subst hv
      have hy' : y ∈ (if v + x = target
          then [(n + 1, TSChoice.part k' v), (n + 1, TSChoice.found k' n)]
          else [(n + 1, TSChoice.part k' v)]) := hy
      by_cases ht : v + x = target
      · rw [if_pos ht] at hy'
        rcases List.mem_cons.mp hy' with rfl | hy2
        · -- the stay: matched by the dominator's stay
          refine ⟨(n + 1, .part k v), ?_, rfl, rfl, hk⟩
          show (n + 1, TSChoice.part k v) ∈ (if v + x = target
            then [(n + 1, TSChoice.part k v), (n + 1, TSChoice.found k n)]
            else [(n + 1, TSChoice.part k v)])
          rw [if_pos ht]; exact List.mem_cons.mpr (Or.inl rfl)
        · -- the completion: the SAME complement finishes the dominator's (larger-index) leg
          have hyf : y = (n + 1, TSChoice.found k' n) := List.mem_singleton.mp hy2
          subst hyf
          refine ⟨(n + 1, .found k n), ?_, rfl, Or.inr ⟨rfl, hk⟩⟩
          show (n + 1, TSChoice.found k n) ∈ (if v + x = target
            then [(n + 1, TSChoice.part k v), (n + 1, TSChoice.found k n)]
            else [(n + 1, TSChoice.part k v)])
          rw [if_pos ht]; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      · rw [if_neg ht] at hy'
        have hys : y = (n + 1, TSChoice.part k' v) := List.mem_singleton.mp hy'
        subst hys
        refine ⟨(n + 1, .part k v), ?_, rfl, rfl, hk⟩
        show (n + 1, TSChoice.part k v) ∈ (if v + x = target
          then [(n + 1, TSChoice.part k v), (n + 1, TSChoice.found k n)]
          else [(n + 1, TSChoice.part k v)])
        rw [if_neg ht]; exact List.mem_cons.mpr (Or.inl rfl)
    | .start, .found i j =>
      -- a past pair dominates whatever the uncommitted state spawns
      have hj : j < n := hqc
      have hy' : y ∈ [(n + 1, TSChoice.start), (n + 1, TSChoice.part n x)] := hy
      rcases List.mem_cons.mp hy' with rfl | hy2
      · exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl,
          (by omega : j < n + 1)⟩
      · have hyp : y = (n + 1, TSChoice.part n x) := List.mem_singleton.mp hy2
        subst hyp
        exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl,
          (by omega : j < n + 1)⟩
    | .part k' v', .found i j =>
      -- a past pair dominates a partial's stay AND its completion (second index `n > j`)
      have hj : j < n := hqc
      have hy' : y ∈ (if v' + x = target
          then [(n + 1, TSChoice.part k' v'), (n + 1, TSChoice.found k' n)]
          else [(n + 1, TSChoice.part k' v')]) := hy
      by_cases ht : v' + x = target
      · rw [if_pos ht] at hy'
        rcases List.mem_cons.mp hy' with rfl | hy2
        · exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl,
            (by omega : j < n + 1)⟩
        · have hyf : y = (n + 1, TSChoice.found k' n) := List.mem_singleton.mp hy2
          subst hyf
          exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl, Or.inl hj⟩
      · rw [if_neg ht] at hy'
        have hys : y = (n + 1, TSChoice.part k' v') := List.mem_singleton.mp hy'
        subst hys
        exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl,
          (by omega : j < n + 1)⟩
    | .found i' j', .found i j =>
      have hy' : y = (n + 1, TSChoice.found i' j') := List.mem_singleton.mp hy
      subst hy'
      exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl, hqc⟩
    | .start, .part _ _ => exact (hqc : False).elim
    | .part _ _, .start => exact (hqc : False).elim
    | .found _ _, .start => exact (hqc : False).elim
    | .found _ _, .part _ _ => exact (hqc : False).elim

/-! ## Snoc-list plumbing -/

/-- The `List` a snoc-list denotes. -/
def toList : SnocList Unit Int → List Int
  | .wrap _ => []
  | .snoc xs x => toList xs ++ [x]

/-- A `List Int` reindexed onto the snoc-list initial algebra. -/
def ofNums (nums : List Int) : SnocList Unit Int :=
  nums.foldl SnocList.snoc (SnocList.wrap ())

theorem toList_foldl : ∀ (nums : List Int) (acc : SnocList Unit Int),
    toList (nums.foldl SnocList.snoc acc) = toList acc ++ nums
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, toList_foldl xs (acc.snoc x)]
    show (toList acc ++ [x]) ++ xs = toList acc ++ x :: xs
    rw [List.append_assoc, List.singleton_append]

theorem toList_ofNums (nums : List Int) : toList (ofNums nums) = nums := by
  rw [ofNums, toList_foldl]; rfl

/-- Splitting a `getElem?` fact across the appended last element. -/
theorem getElem?_append_singleton {nums : List Int} {x v : Int} {k : Nat}
    (h : (nums ++ [x])[k]? = some v) :
    (k < nums.length ∧ nums[k]? = some v) ∨ (k = nums.length ∧ v = x) := by
  have hkb : k < (nums ++ [x]).length := (List.getElem?_eq_some_iff.mp h).1
  simp only [List.length_append, List.length_singleton] at hkb
  rcases Nat.lt_or_ge k nums.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at h
    exact Or.inl ⟨hlt, h⟩
  · have hkeq : k = nums.length := by omega
    rw [hkeq, LC1.getElem?_append_right_zero] at h
    injection h with hv
    exact Or.inr ⟨hkeq, hv.symm⟩

theorem twoSum_lift {nums : List Int} {x target : Int} {i j : Nat}
    (h : LC1.TwoSum nums target i j) : LC1.TwoSum (nums ++ [x]) target i j := by
  obtain ⟨hij, vi, vj, hdi, hdj, hsum⟩ := h
  have hib := (List.getElem?_eq_some_iff.mp hdi).1
  have hjb := (List.getElem?_eq_some_iff.mp hdj).1
  exact ⟨hij, vi, vj, by rw [List.getElem?_append_left hib]; exact hdi,
    by rw [List.getElem?_append_left hjb]; exact hdj, hsum⟩

theorem twoSum_restrict {nums : List Int} {x target : Int} {i j : Nat}
    (hj : j < nums.length) (h : LC1.TwoSum (nums ++ [x]) target i j) :
    LC1.TwoSum nums target i j := by
  obtain ⟨hij, vi, vj, hdi, hdj, hsum⟩ := h
  have hi : i < nums.length := Nat.lt_trans hij hj
  rw [List.getElem?_append_left hi] at hdi
  rw [List.getElem?_append_left hj] at hdj
  exact ⟨hij, vi, vj, hdi, hdj, hsum⟩

/-! ## The generator's reachable states are EXACTLY the spec -/

/-- What each candidate shape claims of the processed prefix. -/
def ReachC (nums : List Int) (target : Int) : TSChoice → Prop
  | .start => True
  | .part k v => nums[k]? = some v
  | .found i j => LC1.TwoSum nums target i j

/-- The generator-vs-spec characterisation (the one problem-specific induction, as in the
    knapsack demo's `gen_iff_choice`): a state is generatable iff its counter is the prefix
    length and its claim holds — in particular `found i j` is generatable iff `TwoSum i j`. -/
theorem gen_char (target : Int) : ∀ (xs : SnocList Unit Int) (s : Nat × TSChoice),
    cataFold (tsB target).gen xs s ↔
      s.1 = (toList xs).length ∧ ReachC (toList xs) target s.2 := by
  intro xs
  induction xs with
  | wrap u =>
    intro s
    constructor
    · intro h
      have hs : s = (0, TSChoice.start) := List.mem_singleton.mp h
      subst hs
      exact ⟨rfl, trivial⟩
    · rintro ⟨hn, hr⟩
      obtain ⟨n, c⟩ := s
      match c with
      | .start =>
        have hn0 : n = 0 := hn
        subst hn0
        exact List.mem_singleton.mpr rfl
      | .part k v =>
        have hkv : ([] : List Int)[k]? = some v := hr
        simp at hkv
      | .found i j =>
        have hts : LC1.TwoSum [] target i j := hr
        obtain ⟨-, vi, vj, hdi, -⟩ := hts
        simp at hdi
  | snoc xs x ih =>
    intro s
    constructor
    · rintro ⟨s', hprev, hstep⟩
      obtain ⟨n', c'⟩ := s'
      obtain ⟨hn', hrc⟩ := (ih (n', c')).mp hprev
      have hn'' : n' = (toList xs).length := hn'
      match c' with
      | .start =>
        have hy : s ∈ [(n' + 1, TSChoice.start), (n' + 1, TSChoice.part n' x)] := hstep
        rcases List.mem_cons.mp hy with rfl | hy2
        · refine ⟨?_, trivial⟩
          show n' + 1 = (toList xs ++ [x]).length
          simp only [List.length_append, List.length_singleton]
          omega
        · have hs : s = (n' + 1, TSChoice.part n' x) := List.mem_singleton.mp hy2
          subst hs
          refine ⟨?_, ?_⟩
          · show n' + 1 = (toList xs ++ [x]).length
            simp only [List.length_append, List.length_singleton]
            omega
          · show (toList xs ++ [x])[n']? = some x
            rw [hn'']
            exact LC1.getElem?_append_right_zero
      | .part k v =>
        have hkv : (toList xs)[k]? = some v := hrc
        have hkb : k < (toList xs).length := (List.getElem?_eq_some_iff.mp hkv).1
        have hy : s ∈ (if v + x = target
            then [(n' + 1, TSChoice.part k v), (n' + 1, TSChoice.found k n')]
            else [(n' + 1, TSChoice.part k v)]) := hstep
        have hlen1 : n' + 1 = (toList xs ++ [x]).length := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hstay : ReachC (toList xs ++ [x]) target (.part k v) := by
          show (toList xs ++ [x])[k]? = some v
          rw [List.getElem?_append_left hkb]
          exact hkv
        by_cases ht : v + x = target
        · rw [if_pos ht] at hy
          rcases List.mem_cons.mp hy with rfl | hy2
          · exact ⟨hlen1, hstay⟩
          · have hs : s = (n' + 1, TSChoice.found k n') := List.mem_singleton.mp hy2
            subst hs
            refine ⟨hlen1, ?_⟩
            show LC1.TwoSum (toList xs ++ [x]) target k n'
            refine ⟨by omega, v, x, ?_, ?_, ht⟩
            · rw [List.getElem?_append_left hkb]; exact hkv
            · rw [hn'']; exact LC1.getElem?_append_right_zero
        · rw [if_neg ht] at hy
          have hs : s = (n' + 1, TSChoice.part k v) := List.mem_singleton.mp hy
          subst hs
          exact ⟨hlen1, hstay⟩
      | .found i j =>
        have hs : s = (n' + 1, TSChoice.found i j) := List.mem_singleton.mp hstep
        subst hs
        refine ⟨?_, twoSum_lift (hrc : LC1.TwoSum (toList xs) target i j)⟩
        show n' + 1 = (toList xs ++ [x]).length
        simp only [List.length_append, List.length_singleton]
        omega
    · rintro ⟨hn, hr⟩
      obtain ⟨n, c⟩ := s
      have hn1 : n = (toList xs).length + 1 := by
        have h : n = (toList xs ++ [x]).length := hn
        simp only [List.length_append, List.length_singleton] at h
        omega
      subst hn1
      match c with
      | .start =>
        refine ⟨((toList xs).length, .start), (ih _).mpr ⟨rfl, trivial⟩, ?_⟩
        show ((toList xs).length + 1, TSChoice.start) ∈
          [((toList xs).length + 1, TSChoice.start),
           ((toList xs).length + 1, TSChoice.part (toList xs).length x)]
        exact List.mem_cons.mpr (Or.inl rfl)
      | .part k v =>
        rcases getElem?_append_singleton (hr : (toList xs ++ [x])[k]? = some v) with
          ⟨hk, hkv⟩ | ⟨hk, hv⟩
        · -- an older leg: it was already reachable, and it stays
          refine ⟨((toList xs).length, .part k v), (ih _).mpr ⟨rfl, hkv⟩, ?_⟩
          show ((toList xs).length + 1, TSChoice.part k v) ∈ (if v + x = target
            then [((toList xs).length + 1, TSChoice.part k v),
                  ((toList xs).length + 1, TSChoice.found k (toList xs).length)]
            else [((toList xs).length + 1, TSChoice.part k v)])
          by_cases ht : v + x = target
          · rw [if_pos ht]; exact List.mem_cons.mpr (Or.inl rfl)
          · rw [if_neg ht]; exact List.mem_cons.mpr (Or.inl rfl)
        · -- the leg committed at THIS step, spawned by `start`
          -- (`hv.symm : x = v` so `subst` eliminates `v`, keeping the snoc element name `x`)
          have hv' : x = v := hv.symm
          subst hv'
          subst hk
          refine ⟨((toList xs).length, .start), (ih _).mpr ⟨rfl, trivial⟩, ?_⟩
          show ((toList xs).length + 1, TSChoice.part (toList xs).length x) ∈
            [((toList xs).length + 1, TSChoice.start),
             ((toList xs).length + 1, TSChoice.part (toList xs).length x)]
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      | .found i j =>
        have hr' : LC1.TwoSum (toList xs ++ [x]) target i j := hr
        obtain ⟨hij, vi, vj, hdi, hdj, hsum⟩ := hr'
        have hjb : j < (toList xs).length + 1 := by
          have := (List.getElem?_eq_some_iff.mp hdj).1
          simp only [List.length_append, List.length_singleton] at this
          omega
        rcases Nat.lt_or_ge j (toList xs).length with hjlt | hjge
        · -- the pair finished earlier: it was reachable and persists
          refine ⟨((toList xs).length, .found i j),
            (ih _).mpr ⟨rfl, twoSum_restrict hjlt ⟨hij, vi, vj, hdi, hdj, hsum⟩⟩, ?_⟩
          show ((toList xs).length + 1, TSChoice.found i j) ∈
            [((toList xs).length + 1, TSChoice.found i j)]
          exact List.mem_singleton.mpr rfl
        · -- the pair finishes AT this step: complete the reachable partial `(i, vi)`
          have hje : j = (toList xs).length := by omega
          subst hje
          have hib : i < (toList xs).length := hij
          have hdi' : (toList xs)[i]? = some vi := by
            rw [List.getElem?_append_left hib] at hdi; exact hdi
          have hvj : x = vj := by
            rw [LC1.getElem?_append_right_zero] at hdj
            exact Option.some.inj hdj
          have ht : vi + x = target := by omega
          refine ⟨((toList xs).length, .part i vi), (ih _).mpr ⟨rfl, hdi'⟩, ?_⟩
          show ((toList xs).length + 1, TSChoice.found i (toList xs).length) ∈
            (if vi + x = target
              then [((toList xs).length + 1, TSChoice.part i vi),
                    ((toList xs).length + 1, TSChoice.found i (toList xs).length)]
              else [((toList xs).length + 1, TSChoice.part i vi)])
          rw [if_pos ht]
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-! ## The DERIVED program and its Corollary-8.1 correctness -/

/-- **The derived program**: run the thinning driver's emitted fold (extend the kept frontier,
    prune by `Q`) and read off the `R`-best kept candidate's answer.  Never written by hand —
    `foldFn`/`solveFn` come from `ThinBest`. -/
def thinTwoSum (nums : List Int) (target : Int) : Option (Nat × Nat) :=
  match (tsB target).solveFn (ofNums nums) with
  | some b => outc b.2
  | none => none

theorem gen_spec (target : Int) (xs : SnocList Unit Int) (s : Nat × TSChoice)
    (h : cataFold (tsB target).gen xs s) :
    outc s.2 = none ∨ ∃ i j, outc s.2 = some (i, j) ∧ LC1.TwoSum (toList xs) target i j := by
  obtain ⟨-, hrc⟩ := (gen_char target xs s).mp h
  obtain ⟨n, c⟩ := s
  match c with
  | .start => exact Or.inl rfl
  | .part k v => exact Or.inl rfl
  | .found i j => exact Or.inr ⟨i, j, rfl, hrc⟩

theorem spec_gen (target : Int) (xs : SnocList Unit Int) (v : Option (Nat × Nat))
    (h : v = none ∨ ∃ i j, v = some (i, j) ∧ LC1.TwoSum (toList xs) target i j) :
    ∃ s : Nat × TSChoice, cataFold (tsB target).gen xs s ∧ outc s.2 = v := by
  rcases h with rfl | ⟨i, j, rfl, hts⟩
  · exact ⟨((toList xs).length, .start), (gen_char target xs _).mpr ⟨rfl, trivial⟩, rfl⟩
  · exact ⟨((toList xs).length, .found i j), (gen_char target xs _).mpr ⟨rfl, hts⟩, rfl⟩

/-- **Corollary 8.1, read for Two Sum** (via `ThinBest.correct_value`): the derived program's
    `some (i, j)` is a genuine valid pair AND the `ansLe`-maximum of all valid pairs (smallest
    second index, then largest first index); its `none` rules every valid pair out. -/
theorem thinTwoSum_correct (nums : List Int) (target : Int) :
    (∀ i j, thinTwoSum nums target = some (i, j) →
      LC1.TwoSum nums target i j ∧
        ∀ i' j', LC1.TwoSum nums target i' j' → j < j' ∨ (j = j' ∧ i' ≤ i)) ∧
    (thinTwoSum nums target = none → ∀ i j, ¬ LC1.TwoSum nums target i j) := by
  have hsome : ((tsB target).solveFn (ofNums nums)).isSome = true := by
    apply ThinBest.solveFn_isSome
    · intro u; exact List.cons_ne_nil _ _
    · rintro ⟨n, c⟩ x
      match c with
      | .start => exact List.cons_ne_nil _ _
      | .part k v =>
        show (if v + x = target then _ else _) ≠ []
        by_cases ht : v + x = target
        · rw [if_pos ht]; exact List.cons_ne_nil _ _
        · rw [if_neg ht]; exact List.cons_ne_nil _ _
      | .found i j => exact List.cons_ne_nil _ _
  cases hb : (tsB target).solveFn (ofNums nums) with
  | none => rw [hb] at hsome; exact absurd hsome (by simp)
  | some b =>
    have hcv := (tsB target).correct_value
      (fun xs v => v = none ∨ ∃ i j, v = some (i, j) ∧ LC1.TwoSum (toList xs) target i j)
      (fun s => outc s.2) ansLe (fun {z w} h => h)
      (gen_spec target) (spec_gen target) (ofNums nums) b hb
    simp only [toList_ofNums] at hcv
    have hthin : thinTwoSum nums target = outc b.2 := by
      unfold thinTwoSum
      rw [hb]
    constructor
    · intro i j hij
      rw [hthin] at hij
      rcases hcv.1 with hnone | ⟨i', j', heq, hts⟩
      · rw [hnone] at hij; exact absurd hij (by simp)
      · rw [heq] at hij
        injection hij with hp
        injection hp with hi hj
        subst hi; subst hj
        refine ⟨hts, fun i' j' hts' => ?_⟩
        have := hcv.2 (some (i', j')) (Or.inr ⟨i', j', rfl, hts'⟩)
        rw [heq] at this
        exact this
    · intro hnone i j hts
      rw [hthin] at hnone
      have := hcv.2 (some (i, j)) (Or.inr ⟨i, j, rfl, hts⟩)
      rw [hnone] at this
      exact this

/-! ## The derived program IS the hand-written scan (and hence the O(n) hash program) -/

/-- Both programs return THE `ansLe`-maximum valid pair (Cor 8.1 on the derived side,
    `LC1.twoSum_opt` on the scan side), and a maximum is unique — so they are equal. -/
theorem thin_eq_scan (nums : List Int) (target : Int) :
    thinTwoSum nums target = LC1.twoSumFn nums target := by
  obtain ⟨hsome_c, hnone_c⟩ := thinTwoSum_correct nums target
  cases hscan : LC1.twoSumFn nums target with
  | none =>
    have hnp := LC1.twoSum_complete nums target hscan
    cases hthin : thinTwoSum nums target with
    | none => rfl
    | some p =>
      obtain ⟨i, j⟩ := p
      exact absurd (hsome_c i j hthin).1 (hnp i j)
  | some p =>
    obtain ⟨i₀, j₀⟩ := p
    have hts0 := LC1.twoSum_sound nums target i₀ j₀ hscan
    cases hthin : thinTwoSum nums target with
    | none => exact absurd hts0 (hnone_c hthin i₀ j₀)
    | some q =>
      obtain ⟨i, j⟩ := q
      obtain ⟨hts, hdom⟩ := hsome_c i j hthin
      have h1 := hdom i₀ j₀ hts0
      have h2 := LC1.twoSum_opt nums target i₀ j₀ hscan i j hts
      have heq : i = i₀ ∧ j = j₀ := by omega
      rw [heq.1, heq.2]

/-- The thinning-derived program computes exactly the `O(n)`-expected hash program of
    `leet/L1_derived.lean` — spec → (Cor 8.1) → pruned frontier fold → (data refinement,
    already proven) → hash scan. -/
theorem thin_eq_hash (nums : List Int) (target : Int) :
    thinTwoSum nums target = LC1D.hashTwoSum nums target := by
  rw [thin_eq_scan, LC1D.hashTwoSum_eq]

/-! ## Headline: `solve = A spec ≫ maxRel D` (the `leet/L53.lean` form, for Two Sum) -/

/-- The honest answer SPEC as a relation `Input ⟶ Ans`: an acceptable answer is a valid pair,
    or `none` exactly when no valid pair exists. -/
def tsSpec : LC1.Input ⟶ LC1.Ans := fun p a =>
  (a = none ∧ ∀ i j, ¬ LC1.TwoSum p.1 p.2 i j) ∨
    ∃ i j, a = some (i, j) ∧ LC1.TwoSum p.1 p.2 i j

/-- The DERIVED program as a morphism equation: `graph thinTwoSum = A tsSpec ≫ maxRel D` —
    B&dM's `max D · Λ spec`, both halves supplied by Corollary 8.1. -/
theorem thin_eq_A_maxRel :
    (graph (fun p : List Int × Int => thinTwoSum p.1 p.2) : LC1.Input ⟶ LC1.Ans)
      = A tsSpec ≫ maxRel (fun w z => ansLe z w) := by
  apply eq_A_comp_maxRel
  · exact fun x y h1 h2 => ansLe_antisym h2 h1
  · -- the program's answer is acceptable
    intro p
    cases h : thinTwoSum p.1 p.2 with
    | none => exact Or.inl ⟨rfl, (thinTwoSum_correct p.1 p.2).2 h⟩
    | some q =>
      obtain ⟨i, j⟩ := q
      exact Or.inr ⟨i, j, rfl, ((thinTwoSum_correct p.1 p.2).1 i j h).1⟩
  · -- ... and dominates every acceptable answer
    rintro p v (⟨rfl, hnp⟩ | ⟨i, j, rfl, hts⟩)
    · trivial
    · cases h : thinTwoSum p.1 p.2 with
      | none => exact absurd hts ((thinTwoSum_correct p.1 p.2).2 h i j)
      | some q =>
        obtain ⟨i', j'⟩ := q
        exact ((thinTwoSum_correct p.1 p.2).1 i' j' h).2 i j hts

/-- **HEADLINE.**  LeetCode 1's allegory program (`leet/L1.lean`'s `solve`, the hand-written
    scan = the `O(n)` hash program) IS the function derived from its relational specification:
    `solve = A tsSpec ≫ maxRel D` in `Rel(Set)` — Two Sum by CALCULATION, the same morphism
    equation shape as Kadane's (`leet/L53.lean`'s `solve_eq_maxRel`), obtained through the
    THINNING theorem rather than the greedy/Horner one. -/
theorem solve_eq_A_maxRel :
    LC1.solve = A tsSpec ≫ maxRel (fun w z => ansLe z w) := by
  rw [← thin_eq_A_maxRel]
  show (graph (fun p : List Int × Int => LC1.twoSumFn p.1 p.2) : LC1.Input ⟶ LC1.Ans) = _
  exact congrArg (fun f : List Int × Int → Option (Nat × Nat) =>
    (graph f : LC1.Input ⟶ LC1.Ans)) (funext fun p => (thin_eq_scan p.1 p.2).symm)

/-! ## Running the DERIVED program (the driver's fold, not the hand scan) -/

example : thinTwoSum [2, 7, 11, 15] 9 = some (0, 1) := by decide
-- duplicate values: the frontier keeps the LATEST index per value, like the scan
example : thinTwoSum [3, 3, 6] 9 = some (1, 2) := by decide
example : thinTwoSum [1, 2, 3] 100 = none := by decide

#eval thinTwoSum [2, 7, 11, 15] 9   -- some (0, 1)
#eval thinTwoSum [3, 2, 4] 6        -- some (1, 2)

end Freyd.Alg.RelSet.LC1T
