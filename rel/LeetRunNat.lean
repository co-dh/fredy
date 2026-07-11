/-
  LeetRunNat — L62 L70 L1: the NAT-AXIS DP and HASHMAP-CARRIER problems RUN in the
  relation-algebra interpreter's fold evaluator (`rel.RelInterp`'s `ProgEval`).

  These were previously skipped because their recursion is not a fold over the input LIST:
  L62/L70 fold over `Nat` — the initial algebra of `G X = 1 ⊕ X` (`zero`/`succ`) — and L1's
  scan carries a hash map.  Both fit the interpreter once

  * the Nat axis is bridged onto the term language: `natSL n` is `n` written in unary as an
    `SL Unit` (`n` snocs over a wrapped unit; `wrap () = zero`, each snoc = one successor), so
    a `Prog.cata` over `natSL n` IS the Nat catamorphism.  `natSL`, its defining law
    `ProgEval.foldSL_natSL : foldSL … (natSL n) = cataNat b s n`, and the genuine `Nat.rec` fold
    `cataNat` now live in the ONE unified `ProgEval` (`rel/RelInterp`), used here via `open`;
  * the fold CARRIER is a data structure: L1 carries the mathlib-free `Freyd.HashMap.AHashMap`
    (`AOP/A6_HashMap.lean`) — the `leet/L1.lean` "Two Sum carried AHashMap" pattern,
    reshaped from its cons-list CPS carrier onto the interpreter's snoc list.  A snoc fold
    accumulates left-to-right DIRECTLY (`foldSL` reaches the `wrap` — the leftmost element —
    first), so the carrier is the plain state `(map, next index, early-exit result)`; the CPS
    continuation was a cons-list artifact (recursion on the tail has no left state to hand on).

  Wired (3):
  * L62 unique paths — iterate the DP row down the grid's `m` axis: a cata over `natSL m` with
    the row (`SnocList Nat Nat`, `n+1` columns) as carrier, base `initRow n`, step `stepRow` —
    `LC62`'s own algebra verbatim; `evalP (prog62 n) (natSL m) = LC62.solveFn (m+1) (n+1)`
    (`prog62_solve`), so `LC62.solve_correct` transfers to the interpreter run.
  * L70 climbing stairs — the tupled `(climb k, climb (k+1))` linearization as the Nat-fold:
    base `(1, 1)`, step `(a, b) ↦ (b, a + b)` — `LC70.fibPair`'s algebra verbatim;
    `evalP prog70 (natSL k) = LC70.solveFn k` (`prog70_solve`).
  * L1 two sum — fold over the input `SL Int` carrying `(AHashMap, next index, Option result)`:
    each live step is ONE `find?` of the complement (+ ONE `insert` on a miss, both `O(1)`
    expected); a hit freezes the state — a total cata still consumes the rest of the input
    structurally, but every frozen step is an `O(1)` copy, the same early-exit economics as
    `leet/L1.lean`'s hash scan after a hit.  The run equals the L-file's program:
    `evalP (prog1 target nb) (slOf x rest) = LC1.twoSumFn (x :: rest) target` (`prog1_twoSum`)
    — the map `find?`-models the assoc list (`LC1.hashModels_insert`, reused) — so the honest
    soundness + completeness `LC1.twoSum_sound/complete` transfers to the interpreter run.

  `SL` is nonempty by design, and `natSL 0 = wrap ()` is the Nat leaf itself — the Nat axis has
  no out-of-range edge case; for L1 the empty `nums` is out of the bridge's range as in the
  other `LeetRun*` files (all demos are the L-files' own nonempty examples).

  Mathlib-free; axioms ⊆ {propext, Quot.sound} — the hash-map lemmas reused from
  `A6_HashMap`/`leet/L1.lean` are the constructive (`beq_iff_eq`) versions, no `Classical.choice`.
-/
import rel.RelInterp
import leet.L62
import leet.L70
import leet.L1

namespace Freyd.Alg.FinRel.NatH

open Freyd.Alg.FinRel.ProgEval
open Freyd.Alg.RelSet
open Freyd.HashMap

/-! ## The Nat axis: `cataNat`, the unary bridge `natSL`, and its bridge law `foldSL_natSL`
    all live in the ONE unified `ProgEval` (`rel/RelInterp`) — used here via `open ProgEval`. -/

/-! ## L62 — unique paths: the DP row folded down the grid's `m` axis

  `LC62.rowAt m n` — `rowAt 0 n = initRow n`, `rowAt (m+1) n = stepRow (rowAt m n)` — is
  literally `m`-fold iteration of `stepRow` from `initRow n`: a Nat-cata with the whole DP row
  (`SnocList Nat Nat`, `n+1` columns) as carrier.  The answer projects the row's last entry. -/

/-- LC 62 as a term: cata over the unary `m` axis, carrier the DP row (`LC62`'s own `initRow`
    base and `stepRow` prefix-sum step), then read off the bottom-right corner. -/
def prog62 (n : Nat) : Prog (SL Unit) Nat :=
  .comp (.cata (fun _ => LC62.initRow n) (fun row _ => LC62.stepRow row)) (.fn LC62.lastOf)

/-- The Nat-cata of `LC62`'s algebra is `LC62.rowAt` — the L-file's own DP row. -/
theorem cataNat_rowAt (n : Nat) :
    ∀ m, cataNat (LC62.initRow n) LC62.stepRow m = LC62.rowAt m n
  | 0 => rfl
  | m + 1 => by
    show LC62.stepRow (cataNat (LC62.initRow n) LC62.stepRow m) = LC62.stepRow (LC62.rowAt m n)
    rw [cataNat_rowAt n m]

/-- **The wiring is exact**: the interpreter run computes `LC62.solveFn` (whence, by
    `LC62.solve_correct`, the true path count `LC62.paths (m+1) (n+1)`). -/
theorem prog62_solve (n m : Nat) :
    evalP (prog62 n) (natSL m) = LC62.solveFn (m + 1) (n + 1) := by
  show LC62.lastOf (foldSL (fun _ => LC62.initRow n) (fun row _ => LC62.stepRow row) (natSL m))
    = LC62.solveFn (m + 1) (n + 1)
  rw [foldSL_natSL, cataNat_rowAt]
  rfl

-- The L-file's own examples (`solveFn 3 7 = 28` etc.), on the interpreter's Nat axis:
example : evalP (prog62 6) (natSL 2) = 28 := by decide  -- 3 × 7 grid
example : evalP (prog62 2) (natSL 2) = 6 := by decide   -- 3 × 3 grid
example : evalP (prog62 4) (natSL 0) = 1 := by decide   -- 1 × 5 grid
example : evalP (prog62 0) (natSL 4) = 1 := by decide   -- 5 × 1 grid

#eval evalP (prog62 6) (natSL 2)  -- 28

/-! ## L70 — climbing stairs: the tupled Fibonacci fold over `Nat`

  `LC70.fibPair` — `(1, 1)` at zero, `(a, b) ↦ (b, a + b)` at each successor — is already the
  Nat-cata with the pair `(climb k, climb (k+1))` as carrier (the tupling/linearization trick);
  the answer projects the first component. -/

/-- LC 70 as a term: the tupled fold over the unary `n` axis (`LC70.fibPair`'s algebra
    verbatim), then project `climb n`. -/
def prog70 : Prog (SL Unit) Nat :=
  .comp (.cata (fun _ => ((1, 1) : Nat × Nat)) (fun p _ => (p.2, p.1 + p.2))) (.fn Prod.fst)

/-- The Nat-cata of `LC70`'s algebra is `LC70.fibPair` — the L-file's own tupled fold. -/
theorem cataNat_fibPair :
    ∀ k, cataNat ((1, 1) : Nat × Nat) (fun p => (p.2, p.1 + p.2)) k = LC70.fibPair k
  | 0 => rfl
  | k + 1 => by
    show (fun p : Nat × Nat => (p.2, p.1 + p.2))
        (cataNat ((1, 1) : Nat × Nat) (fun p => (p.2, p.1 + p.2)) k)
      = LC70.fibPair (k + 1)
    rw [cataNat_fibPair k]
    rfl

/-- **The wiring is exact**: the interpreter run computes `LC70.solveFn` (whence, by
    `LC70.solve_correct`, the true stair count `LC70.climb k`). -/
theorem prog70_solve (k : Nat) : evalP prog70 (natSL k) = LC70.solveFn k := by
  show (foldSL (fun _ => ((1, 1) : Nat × Nat)) (fun p _ => (p.2, p.1 + p.2)) (natSL k)).1
    = LC70.solveFn k
  rw [foldSL_natSL, cataNat_fibPair]
  rfl

-- The L-file's own examples, on the interpreter's Nat axis:
example : evalP prog70 (natSL 0) = 1 := by decide
example : evalP prog70 (natSL 2) = 2 := by decide
example : evalP prog70 (natSL 3) = 3 := by decide
example : evalP prog70 (natSL 5) = 8 := by decide

#eval evalP prog70 (natSL 5)  -- 8

/-! ## L1 — two sum: the fold carrying an `AHashMap` (value ↦ index), early exit as frozen state

  The `leet/L1.lean` hash-scan pattern on the interpreter's snoc list: the carrier is the scan state
  `(map, next index, result)`.  A live step `find?`s the complement of the current element in
  ONE bucket — a hit `some j` records `some (j, i)` and freezes the state; a miss `insert`s
  `value ↦ index` and moves on.  Once frozen, every remaining step is an `O(1)` copy. -/

/-- The scan state: the value ↦ index hash map of the processed prefix, the index about to be
    assigned, and the sticky early-exit result. -/
abbrev St : Type := AHashMap Nat × Nat × Option (Nat × Nat)

/-- One scan step at element `x` (`leet/L1.lean`'s `hashGo` step): done ↦
    stay done; else a one-bucket `find?` of `target - x` — hit `j` ↦ answer `(j, i)`, miss ↦
    `insert x ↦ i` and advance. -/
def step1 (target : Int) (st : St) (x : Int) : St :=
  match st.2.2 with
  | some _ => st
  | none =>
    match find? st.1 (target - x) with
    | some j => (st.1, st.2.1, some (j, st.2.1))
    | none => (Freyd.HashMap.insert st.1 x st.2.1, st.2.1 + 1, none)

/-- LC 1 as a term: fold the prices carrying the hash-map state — the base runs `step1` on the
    first element from the empty map (bucket count `nb`) at index `0` — then project the
    result.  `target` and the bucket count are the curried parameters (as `prog383`'s
    magazine). -/
def prog1 (target : Int) (nb : Nat) : Prog (SL Int) (Option (Nat × Nat)) :=
  .comp
    (.cata (fun x => step1 target (mkHashMap Nat nb, 0, none) x) (step1 target))
    (.fn fun st => st.2.2)

/-! ### The bridge to the L-file's own scan: the run equals `LC1.twoSumFn` -/

/-- A frozen state stays frozen through any remaining input. -/
theorem foldl_step1_frozen (target : Int) :
    ∀ (xs : List Int) (m : AHashMap Nat) (i : Nat) (r : Nat × Nat),
      xs.foldl (step1 target) (m, i, some r) = (m, i, some r)
  | [], _, _, _ => rfl
  | _ :: xs, m, i, r => foldl_step1_frozen target xs m i r

/-- Snoc-building fuses with the fold: folding a snoc-extended list is `List.foldl` of the step
    from the folded seed (how `slOf`'s `List.foldl SL.snoc` meets `foldSL`). -/
theorem foldSL_foldl {A C : Type} (base : A → C) (step : C → A → C) :
    ∀ (rest : List A) (sl : SL A),
      foldSL base step (rest.foldl SL.snoc sl) = rest.foldl step (foldSL base step sl)
  | [], _ => rfl
  | x :: rest, sl => foldSL_foldl base step rest (SL.snoc sl x)

/-- The live scan tracks `LC1.go` under the `L1` hash-simulation invariant — the map `find?`-models the
    assoc list `seen` and the running index is `seen.length`; the miss branch re-establishes
    the invariant via the reused `LC1.hashModels_insert`. -/
theorem foldl_step1_go (target : Int) :
    ∀ (xs : List Int) (m : AHashMap Nat) (seen : List (Int × Nat)),
      (∀ want, find? m want = LC1.findComplement want seen) →
      (xs.foldl (step1 target) (m, seen.length, none)).2.2 = LC1.go seen target xs
  | [], _, _, _ => rfl
  | x :: xs, m, seen, hmodel => by
    show ((xs.foldl (step1 target) (step1 target (m, seen.length, none) x))).2.2
      = LC1.go seen target (x :: xs)
    show ((xs.foldl (step1 target)
        (match find? m (target - x) with
          | some j => (m, seen.length, some (j, seen.length))
          | none => (Freyd.HashMap.insert m x seen.length, seen.length + 1, none)))).2.2
      = LC1.go seen target (x :: xs)
    rw [hmodel (target - x)]
    show _ = (match LC1.findComplement (target - x) seen with
      | some i => some (i, seen.length)
      | none => LC1.go ((x, seen.length) :: seen) target xs)
    cases LC1.findComplement (target - x) seen with
    | some j => rw [foldl_step1_frozen]
    | none =>
      exact foldl_step1_go target xs (Freyd.HashMap.insert m x seen.length)
        ((x, seen.length) :: seen) (LC1.hashModels_insert m seen x seen.length hmodel)

/-- **The wiring is exact**: the interpreter run computes `LC1.twoSumFn` — whence the honest
    soundness + completeness `LC1.twoSum_sound/complete` holds of the interpreter's answers. -/
theorem prog1_twoSum (target : Int) (nb : Nat) (x : Int) (rest : List Int) :
    evalP (prog1 target nb) (slOf x rest) = LC1.twoSumFn (x :: rest) target := by
  show (foldSL (fun x => step1 target (mkHashMap Nat nb, 0, none) x) (step1 target)
      (rest.foldl SL.snoc (SL.wrap x))).2.2 = LC1.twoSumFn (x :: rest) target
  rw [foldSL_foldl]
  show (rest.foldl (step1 target) (step1 target (mkHashMap Nat nb, 0, none) x)).2.2 = _
  show (rest.foldl (step1 target)
      (match find? (mkHashMap Nat nb) (target - x) with
        | some j => ((mkHashMap Nat nb : AHashMap Nat), (0 : Nat), some (j, (0 : Nat)))
        | none => (Freyd.HashMap.insert (mkHashMap Nat nb) x 0, 1, none))).2.2 = _
  rw [find?_mkHashMap]
  exact foldl_step1_go target rest (Freyd.HashMap.insert (mkHashMap Nat nb) x 0) [(x, 0)]
    (LC1.hashModels_insert (mkHashMap Nat nb) [] x 0 fun want => by rw [find?_mkHashMap]; rfl)

-- The L-file's own examples.  As in `leet/L1.lean`, `decide` goes through the plain scan after
-- rewriting by the bridge (no kernel reduction through `Array` buckets); `#eval` below runs
-- the actual hash program.
example : evalP (prog1 9 4) (slOf 2 [7, 11, 15]) = some (0, 1) := by
  rw [prog1_twoSum]; decide
example : evalP (prog1 6 3) (slOf 3 [2, 4]) = some (1, 2) := by
  rw [prog1_twoSum]; decide
example : evalP (prog1 100 3) (slOf 1 [2, 3]) = none := by
  rw [prog1_twoSum]; decide

#eval evalP (prog1 9 4) (slOf 2 [7, 11, 15])  -- some (0, 1)
#eval evalP (prog1 6 3) (slOf 3 [2, 4])       -- some (1, 2)
#eval evalP (prog1 100 3) (slOf 1 [2, 3])     -- none

end Freyd.Alg.FinRel.NatH
