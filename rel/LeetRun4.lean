/-
  LeetCodeRun4 — batch 4 LIST-shaped LeetCode problems RUN in the relation-algebra interpreter.

  Mirror of `rel/LeetRunTree.lean` for the snoc-list functor: each L-file's solution is re-wired
  as a `Prog` TERM whose recursion lives in `Prog.cata` (evaluated by the structural fold
  `foldSL`), and RUN by `evalP` on the L-files' own examples.

  HONEST FRAMING: this runs the existing list programs (≈ `#eval solveFn`); the value is the
  classification — which of the batch fit the interpreter's fold fragment, and as what carrier.

  Wired (8):
  * L125 palindrome — banana-split `(toList, reversed)` pair fold, then decide equality;
  * L128 longest consecutive — TWO chained `cata`s (insertion sort with `LC242.linsert`, then
    the run-tracking scan), a reshaping ground map between them;
  * L136 single number — the XOR fold, scalar carrier, no projection;
  * L152 max product subarray — the `(minEnd, maxEnd, best)` fold, project `best`;
  * L169 majority element — the Boyer–Moore voting fold `(cand, cnt)`, project the candidate;
  * L171 Excel column number — the base-26 Horner fold, scalar carrier;
  * L190 reverse bits — the flip-cons fold (`List.reverse` as a fold), list carrier;
  * L191 number of 1 bits — the bit-count fold, scalar carrier.

  Not expressible, and why:
  * L139 word break — `wordBreakFuel` peels a whole DICTIONARY WORD off the front each step
    (fuelled well-founded recursion, decrease = word length, not one constructor), so it is not
    an algebra of the list functor; the term language has `cata`/`cataT` only.

  Carrier caveat (same as `Demo121.prog121`): `SL` is NON-EMPTY, so the L-files' empty-input
  cases (`LC128.longestConsecFn [] = 0`, `LC171.colNumberFn [] = 0`, `LC190.revBits [] = []`)
  are out of the term's domain — LeetCode's own instances are non-empty there anyway.
-/
import rel.RelInterp
import leet.L125
import leet.L128
import leet.L136
import leet.L152
import leet.L169
import leet.L171
import leet.L190
import leet.L191

namespace Freyd.Alg.FinRel.Run4

open Freyd.Alg.FinRel.ProgEval
-- `Freyd.Alg.RelSet.SL` is the snoc-list-infra NAMESPACE (`SnocList` lives there); the
-- interpreter carrier `SL` is a TYPE (`ProgEval.SL`) — same surface name, no clash (only one is
-- a constant), exactly the `TB` situation in `rel/LeetRunTree.lean`.
open Freyd.Alg.RelSet Freyd.Alg.RelSet.SL

/-- Transport a `SnocList A A` (the L-files' datatype, living in `Rel(Set)`) onto the interpreter
    carrier `SL` — lets every demo reuse the L-files' own example builders (`ofList`/`ofBits'`).
    The list counterpart of `RunTree.ofTree`. -/
def ofSnoc {A : Type} : SnocList A A → SL A
  | .wrap x    => .wrap x
  | .snoc xs a => .snoc (ofSnoc xs) a

/-- Build an `SL` carrier from a first element and the rest, in index order — the bridge for the
    L-files whose data is a raw `List` (L128/L169/L171/L190), cf. `ProgEval.slOf` (`Int`-only). -/
def snocs {A : Type} (first : A) (rest : List A) : SL A :=
  rest.foldl SL.snoc (SL.wrap first)

/-! ## L125 — valid palindrome: banana-split `(toList, reversed)`, then decide equality

  `LC125.palinFn = decide (toList xs = (toList xs).reverse)`.  `toList` is itself the fold
  `base [x]`, `step l ++ [q]`; the reversed listing is the flip-cons fold `step q :: r`.  The
  banana-split tuple fold computes both listings in one pass, leaving the ground map a pure
  `DecidableEq` comparison — no recursion hides in the `fn`. -/

/-- LC 125 as a term: fold to `(toList, reversed toList)`, decide list equality. -/
def prog125 : Prog (SL Int) Bool :=
  .comp
    (.cata (fun x => (([x], [x]) : List Int × List Int))
      (fun p q => (p.1 ++ [q], q :: p.2)))
    (.fn fun p => decide (p.1 = p.2))

example : evalP prog125 (ofSnoc (LC125.ofList 97 [98, 97])) = true := by decide      -- "aba"
example : evalP prog125 (ofSnoc (LC125.ofList 97 [98])) = false := by decide         -- "ab"
example : evalP prog125 (ofSnoc (LC125.ofList 97 [98, 98, 97])) = true := by decide  -- "abba"
example : evalP prog125 (ofSnoc (LC125.ofList 1 [])) = true := by decide             -- single char

/-! ## L128 — longest consecutive sequence: TWO chained folds (sort, then scan)

  `LC128.longestConsecFn = scanFn ∘ isort`: BOTH stages are folds of the list functor —
  insertion sort is the fold of `LC242.linsert` (list carrier; folding in snoc order inserts in
  the reverse order of `isort`, but any insertion order yields the one sorted arrangement of the
  multiset), and `scanAux` is the fold with state `(prev, runLen, best)`.  The ground map between
  them only RESHAPES the (non-empty) sorted list back onto the `SL` carrier; its `[]` branch is
  unreachable (a fold of a non-empty input is non-empty). -/

/-- LC 128 as a term: sort by folding `LC242.linsert`, reshape, scan with `(prev, runLen, best)`
    (the `LC128.scanAux` step verbatim), project `best`. -/
def prog128 : Prog (SL Int) Nat :=
  .comp (.cata (fun x => [x]) (fun l p => LC242.linsert p l))
    (.comp (.fn fun l => match l with | [] => SL.wrap 0 | c :: t => snocs c t)
      (.comp
        (.cata (fun c => ((c, 1, 1) : Int × Nat × Nat))
          (fun st c =>
            if c = st.1 then st
            else if c = st.1 + 1 then (c, st.2.1 + 1, LC128.nmax st.2.2 (st.2.1 + 1))
            else (c, 1, LC128.nmax st.2.2 1)))
        (.fn fun st => st.2.2)))

example : evalP prog128 (snocs 100 [4, 200, 1, 3, 2]) = 4 := by decide  -- the run 1,2,3,4
example : evalP prog128 (snocs 1 [2, 2, 3]) = 3 := by decide            -- dedup: repeat ignored

/-! ## L136 — single number: the XOR-cancellation fold, state IS the answer -/

/-- LC 136 as a term: `LC136.algFn`'s algebra, `wrap x ↦ x`, `snoc ↦ n ^^^ p`; no projection. -/
def prog136 : Prog (SL Nat) Nat := .cata (fun x => x) (fun n p => n ^^^ p)

example : evalP prog136 (ofSnoc (LC136.ofList 2 [2, 1])) = 1 := by decide
example : evalP prog136 (ofSnoc (LC136.ofList 4 [1, 2, 1, 2])) = 4 := by decide
example : evalP prog136 (ofSnoc (LC136.ofList 7 [])) = 7 := by decide

/-! ## L152 — maximum product subarray: the `(minEnd, maxEnd, best)` fold, project `best` -/

/-- LC 152 as a term: `LC152.algFn`'s algebra (its `imin`/`imax`), then the third projection. -/
def prog152 : Prog (SL Int) Int :=
  .comp
    (.cata (fun x => ((x, x, x) : Int × Int × Int))
      (fun st p =>
        let lo := LC152.imin p (LC152.imin (st.1 * p) (st.2.1 * p))
        let hi := LC152.imax p (LC152.imax (st.1 * p) (st.2.1 * p))
        (lo, hi, LC152.imax st.2.2 hi)))
    (.fn fun st => st.2.2)

example : evalP prog152 (ofSnoc (LC152.ofList 2 [3, -2, 4])) = 6 := by decide
example : evalP prog152 (ofSnoc (LC152.ofList (-2) [0, -1])) = 0 := by decide
example : evalP prog152 (ofSnoc (LC152.ofList (-2) [3, -4])) = 24 := by decide  -- sign flip
example : evalP prog152 (ofSnoc (LC152.ofList (-2) [])) = -2 := by decide

/-! ## L169 — majority element: the Boyer–Moore voting fold, project the candidate

  `LC169.majorityFn = (List.foldl step (0,0) ·).1`; on a non-empty list the seed's first move is
  `step (0,0) x = (x, 1)` (a fresh candidacy), which is exactly the `cata` base — the step is
  `LC169.step` itself. -/

/-- LC 169 as a term: base `x ↦ (x, 1)` (= `LC169.step (0,0) x`), step `LC169.step`, project the
    candidate. -/
def prog169 : Prog (SL Int) Int :=
  .comp (.cata (fun x => ((x, 1) : Int × Nat)) LC169.step) (.fn Prod.fst)

example : evalP prog169 (snocs 3 [2, 3]) = 3 := by decide
example : evalP prog169 (snocs 2 [2, 1, 1, 1, 2, 2]) = 2 := by decide

/-! ## L171 — Excel column number: the base-26 Horner fold, scalar carrier

  `LC171.colNumberFn = List.foldl (fun acc d => acc * 26 + d) 0`; on a non-empty (big-endian)
  title the seed's first move is `0 * 26 + d = d`, the `cata` base. -/

/-- LC 171 as a term: base `d ↦ d`, step `acc ↦ acc * 26 + d` — `LC171.colNumberFn`'s fold. -/
def prog171 : Prog (SL Int) Int := .cata (fun d => d) (fun acc d => acc * 26 + d)

example : evalP prog171 (snocs 1 []) = 1 := by decide       -- "A"  = 1
example : evalP prog171 (snocs 1 [1]) = 27 := by decide     -- "AA" = 27
example : evalP prog171 (snocs 26 [26]) = 702 := by decide  -- "ZZ" = 702

/-! ## L190 — reverse bits: `List.reverse` as the flip-cons fold, list carrier

  `LC190.revBits = List.reverse`, and reversal IS a fold: base `[b]`, step `b :: acc` — the
  same reversed-listing leg as `prog125`'s banana-split, here the whole answer (the
  STRUCTURAL-OUTPUT case, cf. `RunTree.prog226`). -/

/-- LC 190 as a term: the flip-cons fold; the output is the reversed bit-list itself. -/
def prog190 : Prog (SL Bool) (List Bool) := .cata (fun b => [b]) (fun acc b => b :: acc)

example : evalP prog190 (snocs true [false, false, false])
    = [false, false, false, true] := by decide
-- direct agreement with the L-file's own program on the same word
example : evalP prog190 (snocs true [false, true]) = LC190.revBits [true, false, true] := by
  decide
example : evalP prog190 (snocs true []) = [true] := by decide

/-! ## L191 — number of 1 bits: the bit-count fold, state IS the answer -/

/-- LC 191 as a term: `LC191.algFn`'s algebra, `wrap b ↦ b2n b`, `snoc ↦ n + b2n b`. -/
def prog191 : Prog (SL Bool) Nat := .cata LC191.b2n (fun n b => n + LC191.b2n b)

example : evalP prog191 (ofSnoc (LC191.ofBits' true [false, true, true])) = 3 := by decide
example : evalP prog191 (ofSnoc (LC191.ofBits' false [false, false, false])) = 0 := by decide
example : evalP prog191 (ofSnoc (LC191.ofBits' false [])) = 0 := by decide

end Freyd.Alg.FinRel.Run4
