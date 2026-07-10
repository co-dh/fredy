/-
  LeetCodeRun7 — batch L322 L338 L367 L383 L387 L392 L404 L435 L724 RUN in the
  relation-algebra interpreter's fold evaluator (`rel.RelInterp`'s `ProgEval`:
  `Prog.cata`/`foldSL` for snoc-lists, `Prog.cataT`/`foldTB` for trees), mirroring
  `rel.LeetRunTree`.  Every wired problem re-expresses the L-file's own program as a `Prog`
  TERM whose recursion lives in `cata`/`cataT`, run by `evalP` on the L-file's own examples.

  Wired (7):
  * L338 counting bits — Nat-iteration IS the cata over the unary bridge `natSL` (`SL Unit`);
    carrier = the growing DP table (`prev.length` recovers the next index).
  * L383 ransom note — the `ransom.all` fold; `countL ransom` reuses the input, closed by
    banana-split (carrier rebuilds `ransom`); magazine applied at the call site (curried).
  * L387 first unique char — first-match scan as a fold; banana-split again (`countL` runs
    against the rebuilt full string), the rebuilt prefix's length IS the running index.
  * L392 is subsequence — the greedy match is the left fold over `t` threading the unmatched
    remainder of `s`; carrier = the remainder-consumer, `s` applied at the call site.
  * L404 sum of left leaves — `cataT`; the down-threaded `isLeft` flag becomes a function
    carrier (`prog98`'s idiom) tupled with an is-`nil` flag (`prog112`'s idiom) so a genuine
    leaf is recognized from the folded children.
  * L435 non-overlapping intervals — PARTIAL: insertion sort (a genuine fold, `linsertH`
    step) and the length live in the cata; the greedy `keptSorted` scan runs on the SORTED
    list, a computed intermediate `List` that `Prog` cannot re-fold (no `List → SL` former),
    so that phase stays a ground map in the final `.fn`.  `foldSL` inserts left-to-right
    where `isortH` inserts right-to-left — same sorted list up to tie order, and the kept
    COUNT agrees (greedy-by-end-time is order-insensitive across ties); demos match the
    L-file's values.
  * L724 pivot index — single cata to `(sum, length, total ↦ leftmost pivot)`; the sum
    component doubles as the `total` the scan is finally applied to (banana-split: the
    two passes of `pivotFn` — `nums.sum` then the scan — are one fold + one application).

  Not wired (2), and why:
  * L322 coin change — the recursion is `dpFuel`, FUELLED descent on `amount` (a
    hylomorphism on Nat); `coinFold` over the coin list is a fold but is parameterized by
    the recursive call, so no clean `cata` form exists in the term language (`hyloF` is a
    standalone function, not a `Prog` former).  Its DP already runs via the
    `rel.AutoDeriveDP` driver (`leet.L322_dp`).
  * L367 valid perfect square — scalar `Nat` input, fuelled UPWARD search (`sqFuel`) with
    early exit: a search loop, not a fold over any list structure of the input; unary-encoding
    `n` and re-deriving an ∃-fold over `0..n` would fake a cata, not reuse the L-file's program.

  SL is nonempty by design (as in `Demo121`/`prog121`), so empty-list edge cases
  (empty `t` in L392, empty `nums` in L724, …) are out of the bridge's range; all demos are
  the L-files' own nonempty examples.
-/
import rel.RelInterp
import rel.LeetRunTree
import leet.L242
import leet.L338
import leet.L383
import leet.L387
import leet.L392
import leet.L404
import leet.L435
import leet.L724

namespace Freyd.Alg.FinRel.Run7

open Freyd.Alg.FinRel.ProgEval
open Freyd.Alg.RelSet Freyd.Alg.RelSet.TB

/-- Bridge a nonempty raw list onto the interpreter's snoc-list, first element at the `wrap`
    (generalizes `ProgEval.slOf` beyond `Int` — needed for `Int × Int` in L435). -/
def snocs {A : Type} (first : A) (rest : List A) : SL A := rest.foldl SL.snoc (SL.wrap first)

/-- Unary bridge for Nat-iteration problems (L338): `n` = `n` snocs over a wrapped unit, so a
    fold over `natSL n` IS `n`-fold iteration from the base. -/
def natSL : Nat → SL Unit
  | 0 => .wrap ()
  | n + 1 => .snoc (natSL n) ()

/-! ## L338 — counting bits: the DP-table fold over the unary Nat

  `LC338.solveFn : Nat → List Nat` is structural Nat-iteration — exactly a cata over `natSL`.
  The carrier is the growing table itself; `prev.length` is the index about to be filled
  (`solveFn n` has length `n + 1`), so the algebra needs no separate counter. -/

/-- LC 338 as a term: `0 ↦ [0]`, `n+1 ↦ prev ++ [prev[⌊i/2⌋] + i % 2]` at `i = prev.length`. -/
def prog338 : Prog (SL Unit) (List Nat) :=
  .cata (fun _ => [0])
    (fun prev _ => prev ++ [prev.getD (prev.length / 2) 0 + prev.length % 2])

example : evalP prog338 (natSL 2) = [0, 1, 1] := by decide
example : evalP prog338 (natSL 5) = [0, 1, 1, 2, 1, 2] := by decide
example : evalP prog338 (natSL 0) = [0] := by decide

/-! ## L383 — ransom note: the `all` fold, banana-split, curried over the magazine

  `LC383.canBuildFn ransom magazine = ransom.all (fun c => countL ransom c ≤ countL magazine c)`
  reads the FULL `ransom` inside the predicate — input reuse `Prog` cannot express directly.
  Banana-split: the carrier rebuilds `ransom` alongside a test abstracted over the (only
  finally known) full string and the magazine; the final `.fn` closes the knot. -/

/-- LC 383 as a term: fold `ransom` to `(rebuilt, (full, mag) ↦ every-count-bounded)`,
    then apply to the rebuilt string itself; the magazine is applied at the call site. -/
def prog383 : Prog (SL Int) (List Int → Bool) :=
  .comp
    (.cata
      (fun c => (([c], fun full mag => decide (LC242.countL full c ≤ LC242.countL mag c)) :
        List Int × (List Int → List Int → Bool)))
      (fun p c =>
        (p.1 ++ [c], fun full mag =>
          p.2 full mag && decide (LC242.countL full c ≤ LC242.countL mag c))))
    (.fn fun p => p.2 p.1)

example : evalP prog383 (snocs 97 []) [98] = false := by decide          -- "a" from "b"
example : evalP prog383 (snocs 97 [98]) [97, 98, 98] = true := by decide -- "ab" from "abb"
example : evalP prog383 (snocs 97 [97]) [97, 98] = false := by decide    -- "aa" from "ab"

/-! ## L387 — first unique character: the first-match scan as a fold

  `LC387.firstUniqFn s = scanFrom s s 0` re-counts every candidate against the FULL string —
  banana-split as in L383.  The rebuilt prefix's length is the index of the element being
  folded, and preferring an earlier `some` keeps the answer LEFTMOST, exactly `scanFrom`. -/

/-- LC 387 as a term: fold to `(rebuilt, full ↦ first index unique in full)`, self-apply. -/
def prog387 : Prog (SL Int) (Option Nat) :=
  .comp
    (.cata
      (fun c => (([c], fun full => if LC242.countL full c = 1 then some 0 else none) :
        List Int × (List Int → Option Nat)))
      (fun p c =>
        (p.1 ++ [c], fun full =>
          match p.2 full with
          | some i => some i
          | none => if LC242.countL full c = 1 then some p.1.length else none)))
    (.fn fun p => p.2 p.1)

example : evalP prog387 (snocs 1 [2, 2, 3, 4, 5, 6, 2]) = some 0 := by decide -- 'l' of "leetcode"
example : evalP prog387 (snocs 97 [97]) = none := by decide                   -- "aa"
example : evalP prog387 (snocs 2 [2, 3]) = some 2 := by decide                -- first unique NOT at 0

/-! ## L392 — is subsequence: the greedy match as the fold over `t`

  `LC392.isSubseqFn s t` recurses structurally on `t`, threading the unmatched remainder of
  `s` (consume both heads on a match, else skip only `t`'s head); `s` is a subsequence iff the
  remainder is exhausted at the end.  So it IS the left fold over `t` with carrier "remainder
  consumer", run curried (`s` applied at the call site, as `prog100`). -/

/-- One greedy step: match `b` against the remainder's head. -/
def consume : List Int → Int → List Int
  | [], _ => []
  | a :: rem, b => if a = b then rem else a :: rem

/-- LC 392 as a term: fold `t` to the composite remainder-consumer, accept iff `s` runs out. -/
def prog392 : Prog (SL Int) (List Int → Bool) :=
  .comp
    (.cata (fun b => fun s => consume s b) (fun f b => fun s => consume (f s) b))
    (.fn fun f s => (f s).isEmpty)

example : evalP prog392 (snocs 97 [104, 98, 103, 100, 99]) [97, 98, 99] = true := by decide
example : evalP prog392 (snocs 97 [104, 98, 103, 100, 99]) [97, 120, 99] = false := by decide
example : evalP prog392 (snocs 97 []) [] = true := by decide  -- `[]` is a subsequence of anything

/-! ## L404 — sum of left leaves: `cataT`, down-flag as function carrier + is-`nil` flag

  `LC404.sumLL` threads "am I a left child?" DOWN (a function carrier, `prog98`'s idiom) and
  matches leaf-vs-non-leaf by SHAPE — recovered from folded children by tupling an is-`nil`
  flag (`prog112`'s idiom).  A genuine leaf contributes `a` iff the flag; a non-leaf restarts
  its children under `true`/`false` (the flag is reset at every node). -/

/-- LC 404 as a term: fold to `(is-nil, isLeft ↦ left-leaf sum)`, apply the root flag `false`. -/
def prog404 : Prog (TB Int) Int :=
  .comp
    (.cataT ((true, fun _ => 0) : Bool × (Bool → Int))
      (fun cl a cr =>
        (false, fun isLeft =>
          if cl.1 && cr.1 then (if isLeft then a else 0) else cl.2 true + cr.2 false)))
    (.fn fun p => p.2 false)

-- LeetCode's own example: left leaves 9 and 15; 7 is a RIGHT leaf, excluded.
example : evalP prog404
    (RunTree.ofTree (Tree.node (LC404.leaf 9) 3 (Tree.node (LC404.leaf 15) 20 (LC404.leaf 7))))
    = 24 := by decide
-- lone root: a leaf but nobody's left child
example : evalP prog404 (RunTree.ofTree (LC404.leaf (5 : Int))) = 0 := by decide
example : evalP prog404 (RunTree.ofTree (Tree.nil : Tree Int)) = 0 := by decide

/-! ## L435 — non-overlapping intervals: sort-phase cata, greedy scan as the final ground map

  `LC435.solveFn ivs = ivs.length - (keptSorted (isortH ivs)).length`.  Insertion sort is a
  genuine fold (`linsertH` step), fused with the length count (banana-split of two folds);
  the greedy `keptSorted` needs the FINISHED sorted list, an intermediate `Prog` cannot
  re-fold, so it stays a ground map (see the header's PARTIAL note). -/

/-- LC 435 as a term: fold to `(length, end-sorted list)`, then `length − kept`. -/
def prog435 : Prog (SL (Int × Int)) Nat :=
  .comp
    (.cata (fun iv => ((1, [iv]) : Nat × List (Int × Int)))
      (fun p iv => (p.1 + 1, LC435.linsertH iv p.2)))
    (.fn fun p => p.1 - (LC435.keptSorted p.2).length)

-- LeetCode 435's own example: remove `[1,3]`.
example : evalP prog435 (snocs ((1 : Int), (2 : Int)) [(2, 3), (3, 4), (1, 3)]) = 1 := by decide
example : evalP prog435 (snocs ((1 : Int), (2 : Int)) [(1, 2), (1, 2)]) = 2 := by decide
example : evalP prog435 (snocs ((1 : Int), (2 : Int)) [(2, 3)]) = 0 := by decide

/-! ## L724 — pivot index: one fold, the sum component IS the deferred total

  `LC724.pivotFn nums = pivotScan nums.sum 0 0 nums` makes two passes; as a term, ONE cata
  builds `(sum, length, total ↦ leftmost pivot index)` — each element's pivot test
  `leftSum = total − leftSum − x` is closed over the still-unknown `total`, and the final
  `.fn` applies the scan to the fold's own sum (banana-split).  Preferring the earlier
  `some` keeps the answer leftmost, exactly `pivotScan`. -/

/-- LC 724 as a term: fold to `(sum, length, total ↦ first pivot)`, apply the scan to the sum. -/
def prog724 : Prog (SL Int) (Option Nat) :=
  .comp
    (.cata
      (fun a => ((a, 1, fun total => if (0 : Int) = total - 0 - a then some 0 else none) :
        Int × Nat × (Int → Option Nat)))
      (fun p x =>
        (p.1 + x, p.2.1 + 1, fun total =>
          match p.2.2 total with
          | some k => some k
          | none => if p.1 = total - p.1 - x then some p.2.1 else none)))
    (.fn fun p => p.2.2 p.1)

example : evalP prog724 (snocs 1 [7, 3, 6, 5, 6]) = some 3 := by decide
example : evalP prog724 (snocs 1 [2, 3]) = none := by decide
example : evalP prog724 (snocs 2 [1, -1]) = some 0 := by decide

end Freyd.Alg.FinRel.Run7
