/-
  LeetCode 1 — Two Sum — DERIVED as a cons-list catamorphism, `O(n)` EXPECTED via a hash map.

  `leet/L1.lean` WRITES `twoSumFn nums target = go [] target nums` as a LEFT-TO-RIGHT scan carrying an
  ACCUMULATOR `seen : List (Int × Nat)` (the `(value, index)` pairs of the processed prefix) and, at each
  new element `x`, a LINEAR sub-search `findComplement (target - x) seen` — so the whole scan is `O(n²)`.

  This file RESHAPES the data onto the canonical cons-list initial algebra `ConsList Unit Int` (`list Int`
  of the book, base at `wrap ()`, recursion on the tail) and REPLACES the association list by the
  mathlib-free `Freyd.HashMap.AHashMap Nat` (value ↦ its index, `AOP/A6_HashMap.lean`).  Each step
  is now ONE `find?` + ONE `insert`, each `O(1)` EXPECTED (a single bucket touched; the bucket count is
  sized to `nums.length`, so the load factor is bounded) — the scan is `O(n)` expected, no linear
  sub-search.

  A plain cons-fold `st : E → C → C` recurses on the TAIL first, so it has no left-accumulated state to
  hand the step.  As in the assoc-list version, the fix is a FUNCTION carrier — here

    * `C := AHashMap Nat → Nat → Option (Nat × Nat)` — "given the map-so-far and the current index,
       the answer" —

  the accumulator-as-continuation (CPS) reshaping: the folded tail is a CONTINUATION awaiting the map and
  index that the still-unprocessed prefix will build.  The base/step are then ordinary and FORCED (`rfl`):

    * base   `g _  = fun _ _ => none`                                   = `foldCL target (wrap _)`
    * step   `st target x k = fun m i => match m.find? (target - x) with`
             `| some j => some (j, i)`                                   (the EARLY RETURN)
             `| none   => k (m.insert x i) (i + 1)`                      = `foldCL target (cons x xs)` with
                                                                          `k = foldCL target xs`.

  Feeding `g`/`st target`/`foldCL target` to the general-carrier law
  `Freyd.Alg.RelSet.CL.consFold_unique` (`AOP/A6_GenFold.lean`) PRODUCES the hash scan as
  `cataR (consScalarAlg g (st target))` — the accumulator-passing left scan with early return is EMITTED
  by the law, never written by hand.

  CORRECTNESS is REUSED, not re-proved.  The bridge `foldCL_go` shows the hash fold computes the SAME
  answer as `LC1.go` under the invariant `∀ w, m.find? w = LC1.findComplement w seen` (the map `find?`-
  models the assoc list) `∧ i = seen.length`; the step preserves it via `find?_insert_self` /
  `find?_insert_other` (`hashModels_insert`).  Both `find?` and `findComplement` return the MOST-RECENTLY
  stored index (bucket/list are both prepend-newest), so the answers coincide.  Hence
  `hashTwoSum = LC1.twoSumFn`, and the honest soundness+completeness `LC1.twoSum_correct` and the `Map`
  `LC1.solve` are REUSED from `L1.lean`.

  Mathlib-free (Lean core + `Fredy.*` only); headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_HashMap
import leet.L1

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC1D

open Freyd Freyd.Alg.RelSet.CL Freyd.HashMap

/-! ## The cons-list FUNCTION carrier and its accumulator-carrying hash fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here
  `C = AHashMap Nat → Nat → Option (Nat × Nat)` — a CONTINUATION mapping the map-so-far and the
  current index to the answer.  Currying the left accumulator `(map, index)` into the carrier is what
  lets an ordinary cons-fold (recursion on the tail) reproduce `go`'s left-to-right accumulator scan,
  now with `O(1)`-expected `find?`/`insert` instead of a linear assoc-list search. -/

/-- The continuation carrier: given the `value ↦ index` hash map seen so far and the current index, the
    optional answer pair. -/
abbrev Carrier : Type := AHashMap Nat → Nat → Option (Nat × Nat)

/-- The base of the emergent algebra: the empty suffix yields no answer, whatever the map/index. -/
def g : Unit → Carrier := fun _ => fun _ _ => none

/-- The step of the emergent algebra: prepend symbol `x` to the folded-tail continuation `k`.  Given the
    map-so-far `m` and current index `i`, look the complement `target - x` up in ONE bucket; a hit
    `some j` returns `some (j, i)` (the EARLY RETURN), a miss inserts `x ↦ i` (`O(1)` expected) and hands
    the extended map and next index `i + 1` on to `k`. -/
def st (target : Int) : Int → Carrier → Carrier :=
  fun x k => fun m i =>
    match find? m (target - x) with
    | some j => some (j, i)
    | none   => k (Freyd.HashMap.insert m x i) (i + 1)

/-- The hash two-sum scan as a fold over the cons-list initial algebra, mirroring `LC1.go`:
    `wrap _ ↦ (fun _ _ => none)`, `cons x xs ↦ st target x (foldCL target xs)`. -/
def foldCL (target : Int) : ConsList Unit Int → Carrier
  | ConsList.wrap _    => fun _ _ => none
  | ConsList.cons x xs => st target x (foldCL target xs)

/-- The base condition is a COMPUTATION, not a guess: `foldCL target (wrap d) = g d`. -/
theorem foldCL_wrap (target : Int) : ∀ d : Unit, foldCL target (ConsList.wrap d) = g d :=
  fun _ => rfl

/-- The step condition IS `foldCL`'s cons equation: `foldCL target (cons x xs) = st target x (…)`. -/
theorem foldCL_cons (target : Int) :
    ∀ (x : Int) (xs : ConsList Unit Int),
      foldCL target (ConsList.cons x xs) = st target x (foldCL target xs) :=
  fun _ _ => rfl

/-! ## The hash scan EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  For each `target`, the hash two-sum scan, RESHAPED onto the cons-list initial
    algebra `ConsList Unit Int`, IS the catamorphism of the emergent scalar algebra
    `consScalarAlg g (st target)` — it was never written as a fold: `graph (foldCL target)` equals
    `cataR (consScalarAlg g (st target))`.  Currying the left accumulator `(map, index)` into the
    function carrier is the point: an accumulator-passing left scan with early return is emitted by
    `consFold_unique`. -/
theorem twoSum_emerges (target : Int) :
    (graph (foldCL target) : dCL Unit Int ⟶ ⟨Carrier⟩) = cataR (consScalarAlg g (st target)) :=
  consFold_unique g (st target) (foldCL target) (foldCL_wrap target) (foldCL_cons target)

/-! ## Bridge to the hand-written raw-`List` solution -/

/-- The `List Int → ConsList Unit Int` conversion onto the initial algebra: `[] ↦ wrap ()`,
    `x :: xs ↦ cons x (ofList xs)`. -/
def ofList : List Int → ConsList Unit Int
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- The hash map `find?`-models the assoc list `seen`, preserved by a step: inserting `x ↦ i` into a map
    modelling `seen` yields one modelling `(x, i) :: seen`.  Uses `find?_insert_self`/`find?_insert_other`
    (both constructive, no `Classical.choice`). -/
theorem hashModels_insert (m : AHashMap Nat) (seen : List (Int × Nat)) (x : Int) (i : Nat)
    (hmodel : ∀ want, find? m want = LC1.findComplement want seen) :
    ∀ want, find? (Freyd.HashMap.insert m x i) want = LC1.findComplement want ((x, i) :: seen) := by
  intro want
  simp only [LC1.findComplement]
  split
  · rename_i hxw
    rw [← hxw]
    exact find?_insert_self m x i
  · rename_i hxw
    rw [find?_insert_other m x i want (fun h => hxw h.symm)]
    exact hmodel want

/-- The reshaped hash fold agrees with the raw-`List` scan on converted input, for EVERY map/index whose
    `find?` models the seen accumulator: `foldCL target (ofList xs) m i = go seen target xs`.  The step
    reproduces `go`'s branch because `m.find? (target - x) = findComplement (target - x) seen` by the
    invariant, and the miss branch re-establishes the invariant via `hashModels_insert`. -/
theorem foldCL_go (target : Int) :
    ∀ (xs : List Int) (m : AHashMap Nat) (seen : List (Int × Nat)) (i : Nat),
      (∀ want, find? m want = LC1.findComplement want seen) → i = seen.length →
      foldCL target (ofList xs) m i = LC1.go seen target xs
  | [],      m, seen, i, _,      _  => rfl
  | x :: xs, m, seen, i, hmodel, hi => by
      subst hi
      show st target x (foldCL target (ofList xs)) m seen.length = LC1.go seen target (x :: xs)
      simp only [st, LC1.go]
      rw [hmodel (target - x)]
      cases LC1.findComplement (target - x) seen with
      | some j => rfl
      | none   =>
          exact foldCL_go target xs (Freyd.HashMap.insert m x seen.length) ((x, seen.length) :: seen)
            (seen.length + 1) (hashModels_insert m seen x seen.length hmodel) rfl

/-- **The efficient program**: run the reshaped hash fold at the empty map (bucket count `nums.length`,
    so the load factor stays bounded) and index `0`. -/
def hashTwoSum (nums : List Int) (target : Int) : Option (Nat × Nat) :=
  foldCL target (ofList nums) (mkHashMap Nat nums.length) 0

/-- The hash program computes exactly `LC1.twoSumFn` — the empty map `find?`-models the empty accumulator
    (`find?_mkHashMap`) and index `0 = [].length`. -/
theorem hashTwoSum_eq (nums : List Int) (target : Int) :
    hashTwoSum nums target = LC1.twoSumFn nums target :=
  foldCL_go target nums (mkHashMap Nat nums.length) [] 0
    (fun want => by rw [find?_mkHashMap]; rfl) rfl

/-! ## Correctness carries over from `L1.lean` (no re-proof of soundness/completeness) -/

/-- **Headline.**  The honest bundle:

    (1) for each `target` the hash two-sum scan, reshaped onto the cons-list initial algebra, IS the
        catamorphism of `consScalarAlg g (st target)` — the `O(n)`-expected accumulator-passing left scan
        with early return EMERGES from `consFold_unique` (`twoSum_emerges`);
    (2) the `Map` `LC1.solve` (LeetCode 1's answer relation) relates each input `(nums, target)` to
        exactly the hash program `hashTwoSum` (`hashTwoSum_eq`); and
    (3) that answer is honestly SOUND and COMPLETE against the `TwoSum` spec — a `some (i, j)` is a
        genuine valid pair, a `none` rules out every valid pair — the REUSED `LC1.twoSum_correct`, not
        re-proved here.

    The program (the fold) is PRODUCED by the law; soundness/completeness is reused; only the DATA
    structure (hash map for `O(1)`-expected lookup) was changed. -/
theorem twoSum_derived_correct :
    (∀ target : Int,
        (graph (foldCL target) : dCL Unit Int ⟶ ⟨Carrier⟩) = cataR (consScalarAlg g (st target)))
      ∧ (∀ (p : List Int × Int) (a : Option (Nat × Nat)),
            LC1.solve p a ↔ a = hashTwoSum p.1 p.2)
      ∧ (∀ (nums : List Int) (target : Int),
            (∀ i j, hashTwoSum nums target = some (i, j) → LC1.TwoSum nums target i j) ∧
            (hashTwoSum nums target = none → ∀ i j, ¬ LC1.TwoSum nums target i j)) := by
  refine ⟨twoSum_emerges, ?_, ?_⟩
  · intro p a
    show (a = LC1.twoSumFn p.1 p.2) ↔ a = hashTwoSum p.1 p.2
    rw [hashTwoSum_eq p.1 p.2]
  · intro nums target
    rw [hashTwoSum_eq nums target]
    exact LC1.twoSum_correct nums target

/-! ## Running / cross-checking the reshaped hash fold

  The relational catamorphism is not `decide`-computable (its `cons` case is an existential over the
  carrier), so the sanity checks go through the computable `hashTwoSum`.  `hashTwoSum` runs on `AHashMap`
  (an `Array` of buckets); rather than reduce `decide` through the array, we rewrite by `hashTwoSum_eq`
  to the plain `LC1.twoSumFn` and `decide` there.  `#eval` exercises the actual hash program. -/

/-- `[2,7,11,15], 9 → (0,1)`. -/
example : hashTwoSum [2, 7, 11, 15] 9 = some (0, 1) := by rw [hashTwoSum_eq]; decide
/-- `[3,2,4], 6 → (1,2)`. -/
example : hashTwoSum [3, 2, 4] 6 = some (1, 2) := by rw [hashTwoSum_eq]; decide
/-- `[1,2,3], 100 → none` (no valid pair). -/
example : hashTwoSum [1, 2, 3] 100 = none := by rw [hashTwoSum_eq]; decide

-- The actual hash program (running through `AHashMap`/`Array`) computes the same answers:
#eval hashTwoSum [2, 7, 11, 15] 9   -- some (0, 1)
#eval hashTwoSum [3, 2, 4] 6        -- some (1, 2)
#eval hashTwoSum [1, 2, 3] 100      -- none

/-- The reshaped fold genuinely relates the converted input to the catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg g (st 9)) (ofList [2, 7, 11, 15]) (foldCL 9 (ofList [2, 7, 11, 15])) := by
  have h : (graph (foldCL 9) : dCL Unit Int ⟶ ⟨Carrier⟩)
      (ofList [2, 7, 11, 15]) (foldCL 9 (ofList [2, 7, 11, 15])) := rfl
  rw [twoSum_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC1D
