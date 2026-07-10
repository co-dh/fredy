/-
  LeetRun6 — batch L242 L252 L253 L268 L271 L279 L283 L300 L303 RUN in the relation-algebra
  interpreter's fold evaluator (`rel.RelInterp`'s `ProgEval`: `Prog.cata` evaluated by `foldSL`,
  the snoc-list mirror of `rel.LeetRunTree`'s `cataT`/`foldTB`).

  Each list-shaped problem's solution is re-wired as a `Prog` term whose recursion lives in
  `cata` (the algebras are the L-files' own, or their standard fold form), and RUN by `evalP`
  on the L-files' own examples.  Raw `List`/plain inputs are bridged by `snocs` (the `slOf`/
  `ofList` move of `Demo121`/`leet.L121`).

  Wired (7):
  * L242 valid anagram — canonical-form fold: insertion sort AS the cata (step = the L-file's
    own `linsert`); anagram = equality of the two canonical forms.  Two-input, so the second
    string is a second RUN compared at the call site (`Prog` has no pairing former — same
    story as `LeetRunTree`'s L100).
  * L252 meeting rooms — insertion-sort-by-start fold (`LC56.linsert`, the L-file's own sort,
    re-expressed as the cata) `≫ .fn noAdj` (the L-file's linear adjacent scan).
  * L268 missing number — the L-file's own `(size, sum)` pair fold `≫` the Gauss extraction
    `(n,s) ↦ triangle n − s`.
  * L271 encode strings — the encode half (`flatMap encode1`) as a fold with token-list
    carrier; round-tripped through the L-file's own `decodeFn`.  The decode half is a fuelled
    UNFOLD (anamorphism), outside the `cata`-only term language — exactly L297's split in
    `LeetRunTree`.
  * L283 move zeroes — the stable partition as its standard single-pass fold, carrier
    `(non-zeros in order, zero count)`, `≫` append-that-many-zeros.
  * L300 longest increasing subsequence — the L-file's own O(n²) records DP (`algFn`, proved
    `solve_eq_cata` there), carrier `(records, best)`, `≫ .fn Prod.snd`.
  * L303 range sum query — the prefix-sum SCAN as a fold, carrier `(table, running total)`,
    `≫` the O(1) two-lookup query (query indices are term parameters, like `LeetRunTree`'s
    needle-parameterised L572).

  Skipped (2), not a list-functor fold — no `cata` faked:
  * L253 meeting rooms II — `roomsFn` is an all-pairs counting formula (max over each start of
    a WHOLE-list cover count); each element's count reads the full list, not a prefix, so the
    L-file has no fold to rewire (an incremental records-carrying rewrite would be a new
    algorithm, not a rewiring).
  * L279 perfect squares — input is a scalar `Nat`, program is the memoised amount-axis DP
    (`memoOf` course-of-values recursion via `rel.AutoDeriveDP`), reading the memo at
    arbitrary smaller amounts `t − c²` — not a structural fold over any list of the input.
-/
import rel.RelInterp
import leet.L242
import leet.L252
import leet.L268
import leet.L271
import leet.L283
import leet.L300
import leet.L303

namespace Freyd.Alg.FinRel.Run6

open Freyd.Alg.FinRel.ProgEval
open Freyd.Alg.RelSet

/-- Bridge a first element and the rest (in order) onto the interpreter carrier `SL` — the
    generic form of `Demo121.slOf`/the L-files' `ofList`, one per element type needed below. -/
def snocs {A : Type} (first : A) (rest : List A) : SL A :=
  rest.foldl SL.snoc (SL.wrap first)

/-! ## L242 — valid anagram: the canonical-form (insertion-sort) fold

  `LC242.anagramFn s t = decide (isort (toList s) = isort (toList t))` — each side is the
  string's SORTED character list, and that canonical form IS a fold: base `x ↦ [x]`, step
  = the L-file's own `linsert` into the (sorted) carrier.  The anagram test compares two
  runs at the call site (`Prog` has no pairing former; cf. `LeetRunTree`'s L100). -/

/-- LC 242's canonical form as a term: fold a string to its sorted character list. -/
def prog242 : Prog (SL Int) (List Int) :=
  .cata (fun x => [x]) (fun l q => LC242.linsert q l)

-- the term's canonical form is the L-file's own `isort ∘ toList`, on its own example
example : evalP prog242 (snocs 1 [2, 1, 3, 4, 1, 5])
    = LC242.isort (LC242.toList (LC242.ofList 1 [2, 1, 3, 4, 1, 5])) := by decide
-- "anagram" / "nagaram" → true (letters coded a=1 n=2 g=3 r=4 m=5, as in the L-file)
example : evalP prog242 (snocs 1 [2, 1, 3, 4, 1, 5])
    = evalP prog242 (snocs 2 [1, 3, 1, 4, 1, 5]) := by decide
-- "rat" / "car" → false (r=4 a=1 t=7 c=6)
example : ¬ evalP prog242 (snocs 4 [1, 7]) = evalP prog242 (snocs 6 [1, 4]) := by decide

/-! ## L252 — meeting rooms: sort-by-start as the cata, then the adjacent scan

  `LC252.canAttendFn = noAdj ∘ isort` — the sort (the O(n²) work) is insertion sort, a fold
  with the L-file's own `LC56.linsert` as step; the linear adjacent check `noAdj` is the
  ground-map projection. -/

/-- LC 252 as a term: fold to the start-sorted interval list, then the adjacent scan. -/
def prog252 : Prog (SL (Int × Int)) Bool :=
  .comp (.cata (fun iv => [iv]) (fun l iv => LC56.linsert iv l)) (.fn LC252.noAdj)

-- LeetCode 252's own examples: `[[0,30],[5,10],[15,20]] → false`, `[[7,10],[2,4]] → true`
example : evalP prog252 (snocs (0, 30) [(5, 10), (15, 20)]) = false := by decide
example : evalP prog252 (snocs (7, 10) [(2, 4)]) = true := by decide
-- touching endpoints are attendable: `[[1,5],[5,10]] → true`
example : evalP prog252 (snocs (1, 5) [(5, 10)]) = true := by decide

/-! ## L268 — missing number: the L-file's own `(size, sum)` fold, Gauss extraction -/

/-- LC 268 as a term: `LC268.foldFn`'s pair algebra, then `(n,s) ↦ triangle n − s`. -/
def prog268 : Prog (SL Nat) Nat :=
  .comp (.cata (fun x => ((1 : Nat), x)) (fun st p => (st.1 + 1, st.2 + p)))
    (.fn fun st => LC268.triangle st.1 - st.2)

example : evalP prog268 (snocs 3 [0, 1]) = 2 := by decide
example : evalP prog268 (snocs 9 [6, 4, 2, 3, 5, 7, 0, 1]) = 8 := by decide

/-! ## L271 — encode strings: the encode (fold) half; decode is an unfold, see the header -/

/-- LC 271's encoder as a term: length-prefix each string and concatenate (`flatMap encode1`
    as a fold, token-list carrier). -/
def prog271 : Prog (SL (List Int)) (List Int) :=
  .cata LC271.encode1 (fun acc s => acc ++ LC271.encode1 s)

-- the term IS the L-file's `encode`, on its own example (an empty string exercises `n = 0`)
example : evalP prog271 (snocs ([104, 105] : List Int) [[]])
    = LC271.encode [[104, 105], []] := by decide
-- round-trip: the L-file's own (unfold) decoder parses the term's output back
example : LC271.decodeFn (evalP prog271 (snocs ([104, 105] : List Int) [[]]))
    = some [[104, 105], []] := by decide

/-! ## L283 — move zeroes: the stable partition as its standard single-pass fold

  `LC283.moveZeroesFn xs = xs.filter nz ++ replicate #zeros 0` — filter/count are the classic
  fold; carrier `(non-zeros in order, zero count)`, each element's treatment reads only the
  prefix. -/

/-- LC 283 as a term: fold to `(non-zeros, zero count)`, then append that many zeros. -/
def prog283 : Prog (SL Int) (List Int) :=
  .comp
    (.cata (fun x => if x = 0 then (([] : List Int), (1 : Nat)) else ([x], 0))
      (fun st x => if x = 0 then (st.1, st.2 + 1) else (st.1 ++ [x], st.2)))
    (.fn fun st => st.1 ++ List.replicate st.2 0)

-- LeetCode 283's own examples, checked against the L-file's own program
example : evalP prog283 (snocs 0 [1, 0, 3, 12]) = LC283.moveZeroesFn [0, 1, 0, 3, 12] := by
  decide
example : evalP prog283 (snocs 0 [1, 0, 3, 12]) = [1, 3, 12, 0, 0] := by decide
example : evalP prog283 (snocs 0 []) = [0] := by decide

/-! ## L300 — longest increasing subsequence: the L-file's own records DP fold

  `LC300.solve_eq_cata` already proves the L-file's program IS this catamorphism (algebra
  `algFn`, carrier `(records, best)`) followed by `Prod.snd`; here it runs as a term. -/

/-- LC 300 as a term: `LC300.algFn`'s records algebra, then the running best. -/
def prog300 : Prog (SL Int) Nat :=
  .comp
    (.cata (fun x => ([(x, (1 : Nat))], (1 : Nat)))
      (fun st p =>
        (st.1 ++ [(p, LC300.lisEnd st.1 p)], LC300.nmax st.2 (LC300.lisEnd st.1 p))))
    (.fn Prod.snd)

-- LeetCode 300's own example `[10,9,2,5,3,7,101,18] → 4`
example : evalP prog300 (snocs 10 [9, 2, 5, 3, 7, 101, 18]) = 4 := by decide
example : evalP prog300 (snocs 7 [7, 7]) = 1 := by decide

/-! ## L303 — range sum query: the prefix-sum scan as a fold, O(1) query projection

  `LC303.prefixSums` is the scan `[0, x₀, x₀+x₁, …]`; as a fold the carrier tuples the table
  built so far with the running total.  The query indices `(i, j)` parameterise the term
  (like `LeetRunTree`'s needle-parameterised L572). -/

/-- LC 303 as a term (query `(i, j)` fixed): fold to `(prefix-sum table, running total)`,
    then answer by the L-file's two-lookup subtraction. -/
def prog303 (i j : Nat) : Prog (SL Int) Int :=
  .comp
    (.cata (fun x => (([0, x] : List Int), x)) (fun st x => (st.1 ++ [st.2 + x], st.2 + x)))
    (.fn fun st => (st.1[j + 1]?.getD 0) - (st.1[i]?.getD 0))

-- the fold's table IS the L-file's `prefixSums`, on its own example
example : (evalP (Prog.cata (fun x => (([0, x] : List Int), x))
      (fun st x => (st.1 ++ [st.2 + x], st.2 + x))) (snocs (-2) [0, 3, -5, 2, -1])).1
    = LC303.prefixSums [-2, 0, 3, -5, 2, -1] := by decide
-- LeetCode 303's own queries: `sumRange(0,2) = 1`, `sumRange(2,5) = -1`
example : evalP (prog303 0 2) (snocs (-2) [0, 3, -5, 2, -1]) = 1 := by decide
example : evalP (prog303 2 5) (snocs (-2) [0, 3, -5, 2, -1]) = -1 := by decide

end Freyd.Alg.FinRel.Run6
