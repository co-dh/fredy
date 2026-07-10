/-
  LeetCodeRun3 — batch L56 L57 L62 L66 L67 L70 L91 L118 L121 RUN in the relation-algebra
  interpreter's fold evaluator (`rel.RelInterp`'s `ProgEval`: `SL`/`foldSL`/`Prog`/`evalP`),
  mirroring `rel.LeetRunTree` for list problems: each wired solution is a `Prog` TERM whose
  recursion lives in `cata` (the algebras are the L-files' own, transcribed to the `A → C` /
  `C → A → C` shape), run by `evalP` on the L-files' own examples.

  HONEST FRAMING: this runs the existing list programs (≈ `#eval solveFn`); the value is the
  breadth classification — which problems' programs ARE folds of the list functor.

  Wired (5): L56 merge intervals (sort-cata, run-merge as ground `.fn` — see its header),
  L57 insert interval (= the L56 term, `new` placed at the head by the input bridge),
  L66 plus one (banana-split carry paramorphism), L67 add binary (curried zip fold with a
  carry-function carrier, fuel replaced by input structure), L91 decode ways (the L-file's own
  `algFn`, split at the `Sum`).

  Not wired, and why:
  * L62 unique paths — input is `Nat × Nat`; the program iterates a row transition down the
    grid's `m` axis (recursion over `Nat`, the initial algebra of `1 + X`), not over an input
    list.  `Prog` has `cata`/`cataT` (list/tree formers) only.
  * L70 climbing stairs — input is `Nat`; the tupled Fibonacci fold `fibPair` is again a
    `Nat`-cata (`1 + X`), not a list fold.
  * L118 Pascal's triangle — input is `Nat` (`numRows`); `buildRows` iterates `nextRow` `n`
    times, generating rows (recursion over `Nat`, anamorphic in flavour), no input list.
  * L121 best time to buy/sell — ALREADY the interpreter's reference program
    (`ProgEval.Demo121` spec term + `ProgEval.prog121` fold term, `rel.RelInterp`); not
    re-wired here to avoid a duplicate term.
-/
import rel.RelInterp
import leet.L56
import leet.L57
import leet.L66
import leet.L67
import leet.L91

namespace Freyd.Alg.FinRel.Run3

open Freyd.Alg.FinRel.ProgEval
open Freyd.Alg.RelSet

/-- Build an `SL` from a first element and the rest, in order — the generic input bridge
    (`ProgEval.slOf` is `Int`-only; this batch also needs `Int × Int` and `Nat` elements). -/
def snocs {A : Type} (first : A) (rest : List A) : SL A := rest.foldl SL.snoc (SL.wrap first)

/-! ## L56 — merge intervals: insertion sort as the cata, run-merge as a ground map

  `LC56.mergeFn = mergeSorted ∘ isort` composes TWO list folds.  The term language folds only
  the `SL` input, and `Prog` composes through ground maps, so the first fold (insertion sort:
  base `[iv]`, step `linsert`) is the `cata`, and the second (the run-merging scan
  `mergeSorted`, itself a fold over the SORTED intermediate list) rides as a ground `.fn` —
  the same license as `LeetRunTree`'s `prog102` using `mergeLevels` as a ground helper.
  (`isort` inserts front-to-back, the `SL` fold back-to-front; insertion sort is
  order-insensitive, so the sorted intermediate agrees on the demos.) -/

/-- LC 56 as a term: fold to the `.1`-sorted list via `LC56.linsert`, then run-merge. -/
def prog56 : Prog (SL (Int × Int)) (List (Int × Int)) :=
  .comp (.cata (fun iv => [iv]) (fun sorted iv => LC56.linsert iv sorted))
    (.fn LC56.mergeSorted)

-- LeetCode 56's own example: `[[1,3],[2,6],[8,10],[15,18]] → [[1,6],[8,10],[15,18]]`.
example : evalP prog56 (snocs (1, 3) [(2, 6), (8, 10), (15, 18)])
    = [(1, 6), (8, 10), (15, 18)] := by decide
-- Touching intervals DO merge (`≤`, not `<`): `[[1,4],[4,5]] → [[1,5]]`.
example : evalP prog56 (snocs (1, 4) [(4, 5)]) = [(1, 5)] := by decide
-- Unsorted input is sorted first, and the term agrees with the L-file's own `mergeFn`.
example : evalP prog56 (snocs (2, 6) [(1, 3), (8, 10), (15, 18)])
    = LC56.mergeFn [(2, 6), (1, 3), (8, 10), (15, 18)] := by decide

/-! ## L57 — insert interval: the L56 term, `new` placed at the head by the bridge

  `LC57.insertFn ivs new = LC56.mergeFn (new :: ivs)` — inserting is merging the extended
  list, so the PROGRAM is `prog56` verbatim and the insert semantics live entirely in the
  input bridge `snocs new ivs` (no new term; a `prog57 := prog56` alias would be a forbidden
  one-liner). -/

-- LeetCode 57's own example: `[[1,3],[6,9]]` + `[2,5]` → `[[1,5],[6,9]]`.
example : evalP prog56 (snocs (2, 5) [(1, 3), (6, 9)]) = [(1, 5), (6, 9)] := by decide
-- Lands cleanly in a gap, no merge — and the term agrees with the L-file's own `insertFn`.
example : evalP prog56 (snocs (4, 4) [(1, 3), (6, 9)]) = [(1, 3), (4, 4), (6, 9)]
    ∧ evalP prog56 (snocs (2, 5) [(1, 3), (6, 9)]) = LC57.insertFn [(1, 3), (6, 9)] (2, 5) := by
  decide

/-! ## L66 — plus one: the carry paramorphism, closed by banana-split

  `LC66.plusOneRev` recurses least-significant-digit first and its no-carry branch returns the
  RAW tail — a paramorphism, not a plain fold.  Banana-split closes it (second carrier
  component rebuilds the little-endian input, as in `LeetRunTree`'s `prog572`).  Orientation:
  an `SL` fold consumes the LAST element outermost, so feeding the digits in their natural
  BIG-endian order makes the fold consume the least-significant digit first — exactly
  `plusOneRev` on the reversed list, with both `List.reverse`s of `LC66.plusOneFn` absorbed
  (input by the orientation, output by the final ground map). -/

/-- LC 66 as a term: fold big-endian digits to `(little-endian incremented digits, little-endian
    raw digits)`, then reverse the first component back to big-endian. -/
def prog66 : Prog (SL Int) (List Int) :=
  .comp
    (.cata (fun d => (LC66.plusOneRev [d], [d]))
      (fun st d => (if d + 1 = 10 then 0 :: st.1 else (d + 1) :: st.2, d :: st.2)))
    (.fn fun st => st.1.reverse)

-- LeetCode 66's own examples: `[1,2,3] → [1,2,4]`, `[9,9] → [1,0,0]` (full carry ripple).
example : evalP prog66 (snocs 1 [2, 3]) = [1, 2, 4] := by decide
example : evalP prog66 (snocs 9 [9]) = [1, 0, 0]
    ∧ evalP prog66 (snocs 9 [9]) = LC66.plusOneFn [9, 9] := by decide

/-! ## L67 — add binary: the curried zip fold, fuel replaced by input structure

  `LC67.addBitsRev` is a TWO-input carry ripple, made total in the L-file by an explicit FUEL
  parameter.  As a term it is a fold over the FIRST number's digits whose carrier is the
  function `carry → remaining second-number digits (little-endian) → sum digits (little-endian)`
  — the second input is applied at the call site (`Prog` has no pairing former, as in
  `LeetRunTree`'s `prog100`/`prog617`), and the fold's own structure replaces the fuel.  When
  the first number runs out (the innermost/base position, i.e. past its most significant bit),
  the leftover carry ripples through the second number's remaining bits by the L-file's own
  `addBitsRev` with its `[]` first argument (a ground helper, fuel `ys.length + 1` sufficing).
  Big-endian orientation as in `prog66`. -/

/-- The zip-fold step: absorb one bit `x` of the first number against the next remaining bit of
    the second (or `0` if the second is exhausted), emit the sum bit, pass the carry inward. -/
def step67 (f : Int → List Int → List Int) (x : Int) : Int → List Int → List Int :=
  fun c ys => match ys with
    | [] => (c + x) % 2 :: f ((c + x) / 2) []
    | y :: ys' => (c + x + y) % 2 :: f ((c + x + y) / 2) ys'

/-- LC 67 as a term: fold the first number's big-endian bits to the carry-adder function, then
    close it over the second number (reversed in, result reversed back to big-endian). -/
def prog67 : Prog (SL Int) (List Int → List Int) :=
  .comp
    (.cata (step67 fun c ys => LC67.addBitsRev (ys.length + 1) c [] ys) step67)
    (.fn fun f ys => (f 0 ys.reverse).reverse)

-- LeetCode 67's own examples: `1011 + 101 = 10000` (11 + 5 = 16), `11 + 1 = 100`.
example : evalP prog67 (snocs 1 [0, 1, 1]) [1, 0, 1] = [1, 0, 0, 0, 0] := by decide
example : evalP prog67 (snocs 1 [1]) [1] = [1, 0, 0]
    ∧ evalP prog67 (snocs 1 [0, 1, 1]) [1, 0, 1] = LC67.addBinaryFn [1, 0, 1, 1] [1, 0, 1] := by
  decide

/-! ## L91 — decode ways: the L-file's own algebra, split at the `Sum`

  `LC91.foldFn` is literally an `SL` fold with the tuple carrier `(ways, prevWays, lastDigit)`;
  its algebra is already packaged as `LC91.algFn` on the pattern functor `ℕ ⊕ (C × ℕ)`, so the
  term's base/step are its two `Sum` branches verbatim, followed by the `ways` projection
  (exactly the L-file's own `solve_eq_cata` factoring, now runnable). -/

/-- LC 91 as a term: `LC91.algFn`'s fold, then project the decode count. -/
def prog91 : Prog (SL Nat) Nat :=
  .comp
    (.cata (fun d => LC91.algFn (Sum.inl d)) (fun st d => LC91.algFn (Sum.inr (st, d))))
    (.fn (·.1))

-- LeetCode 91's own examples: `"12" → 2`, `"10" → 1`, `"0" → 0`, `"226" → 3`.
example : evalP prog91 (snocs 1 [2]) = 2 := by decide
example : evalP prog91 (snocs 1 [0]) = 1 := by decide
example : evalP prog91 (snocs 0 []) = 0 := by decide
example : evalP prog91 (snocs 2 [2, 6]) = 3
    ∧ evalP prog91 (snocs 2 [2, 6]) = LC91.solveFn (LC91.ofList 2 [2, 6]) := by decide

end Freyd.Alg.FinRel.Run3
