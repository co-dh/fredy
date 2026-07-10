/-
  LeetRun8 — batch 8 list-shaped LeetCode problems RUN in the relation-algebra interpreter.

  Mirrors `rel.LeetRunTree` for the snoc-list functor: each problem's solution is re-wired as a
  `Prog` TERM whose recursion lives in `Prog.cata` (evaluated by the structural fold `foldSL`),
  REUSING the L-file's own algebra (its `foldFn` base/step, its `rowStep`, its `linsert`), and RUN
  by `evalP` on the L-files' own examples.  HONEST FRAMING: this runs the existing programs
  (≈ `#eval solveFn`); the value is the batch classification.

  Batch L746 L763 L977 L1137 L1143 — ALL FIVE ARE FOLDS, wired:
  * L746 min-cost stairs — the textbook paired-state DP fold `(reachHere, reachPrev)`, then
    project `imin` — the clean scalar-tuple-carrier case.
  * L763 partition labels — a two-pass greedy: `lastPos` needs the WHOLE string, and the L-file's
    top call is `scanFn xs xs` (input reuse `Prog` cannot express directly).  Reshaped by the
    standard banana-split (LeetRunTree's L101/L572): carrier = (whole ↦ scan-state, rebuilt
    input), self-apply at the end.  The scan itself is genuinely folded; `lastPos` is a ground
    map run against the rebuilt input inside the algebra, like L572's needle check.
  * L977 sorted squares — map+insertion-sort FUSED into one fold: step inserts the square into
    the sorted accumulator (`LC242.linsert`, the L-file's own sort's inner loop).  Same sorted
    multiset as the L-file's `isort ∘ map` (insertion order is irrelevant), so the demo values
    match its examples verbatim.
  * L1137 tribonacci — the input is `ℕ`, the initial algebra of `1 + X`: bridged as a UNARY
    snoc-list `snocs n : SL Unit` (n snocs past `wrap`), the fold carrying the L-file's triple
    `(T n, T(n+1), T(n+2))`, then project `.1`.
  * L1143 longest common subsequence — flagged "2-D DP" in the batch spec, but the L-file's own
    program is a 1-D FOLD: `col ys = foldr (rowStep · ys)` over `xs`, carrier = one DP row
    (`List Nat`, entry j = lcs · (ys.drop j)), `ys` a fixed needle parameter (like L572's `t`).
    `col` is a foldr on a cons-list, so the input is fed to the snoc-list fold REVERSED
    (foldr over `x₀…xₙ` = `foldSL` over the snoc-list `wrap xₙ, snoc …, snoc x₀`).

  Skipped: none.
-/
import rel.RelInterp
import leet.L746
import leet.L763
import leet.L977
import leet.L1137
import leet.L1143

namespace Freyd.Alg.FinRel.Run8

open Freyd.Alg.FinRel.ProgEval
-- `Freyd.Alg.RelSet.SL` is the snoc-list infra NAMESPACE (`SnocList` lives there); the
-- interpreter carrier `SL` is a TYPE (`ProgEval.SL`) — same surface name, no clash (only one is
-- a constant), exactly the `TB` situation in `rel.LeetRunTree`.
open Freyd.Alg.RelSet Freyd.Alg.RelSet.SL

/-! ## L746 — min cost climbing stairs: the paired-state DP fold, project the `min` -/

/-- LC 746 as a term: `LC746.foldFn`'s algebra `(x ↦ (x,0), ((h,p),c) ↦ (c + min h p, h))`,
    then `imin` the two components (step off from either of the last two steps). -/
def prog746 : Prog (SL Int) Int :=
  .comp
    (.cata (fun x => ((x, 0) : Int × Int))
      (fun st p => (p + LC746.imin st.1 st.2, st.1)))
    (.fn fun st => LC746.imin st.1 st.2)

example : evalP prog746 (slOf 10 [15, 20]) = 15 := by decide
example : evalP prog746 (slOf 1 [100, 1, 1, 1, 100, 1, 1, 100, 1]) = 6 := by decide
example : evalP prog746 (slOf 5 []) = 0 := by decide

/-! ## L763 — partition labels: the close-on-reach scan, closed by banana-split

  `LC763.scanFn whole` is a structural fold over the string once the fixed `whole` is a
  parameter, and the answer is the input-reusing `scanFn xs xs`.  Carrier = (whole ↦ scan
  state, input rebuilt as the L-file's `SnocList`); the rebuilt component both feeds `whole`
  at the final self-application and supplies the current absolute position (`topIdx`) inside
  the step, so the algebra is the L-file's `scanFn` equations verbatim. -/

/-- LC 763 as a term: fold to `(whole ↦ (reach, curSize, doneParts), rebuilt input)`,
    self-apply, reverse the closed pieces. -/
def prog763 : Prog (SL Int) (List Nat) :=
  .comp
    (.cata
      (fun x =>
        ((fun w => let r := LC763.lastPos w x
                   if r = 0 then (r, 0, [1]) else (r, 1, [])),
         SnocList.wrap x))
      (fun c p =>
        ((fun w =>
            let (r, sz, rp) := c.1 w
            let r' := LC763.nmax r (LC763.lastPos w p)
            if LC763.topIdx c.2 + 1 = r' then (r', 0, (sz + 1) :: rp) else (r', sz + 1, rp)),
         SnocList.snoc c.2 p)))
    (.fn fun c => (c.1 c.2).2.2.reverse)

-- "ababcbacadefegdehijhklij" (the L-file's classic example, same `Int` codes) → [9, 7, 8]
example : evalP prog763 (slOf 97 [98, 97, 98, 99, 98, 97, 99, 97, 100, 101, 102, 101, 103, 100,
    101, 104, 105, 106, 104, 107, 108, 105, 106]) = [9, 7, 8] := by decide
example : evalP prog763 (slOf 101 [105, 106, 101]) = [4] := by decide
example : evalP prog763 (slOf 101 []) = [1] := by decide

/-! ## L977 — squares of a sorted array: map + insertion sort fused into ONE fold

  `LC977.sortedSquaresFn = isort ∘ map (·²)` — two passes, both folds.  Fused: the step inserts
  the newly squared element into the already-sorted accumulator (`LC242.linsert`, the inner loop
  of the L-file's own `isort`).  Insertion order differs from `isort`'s right fold, but a sorted
  list is determined by its multiset, so the results agree — on the L-file's examples verbatim. -/

/-- LC 977 as a term: fold to the sorted list of squares seen so far. -/
def prog977 : Prog (SL Int) (List Int) :=
  .cata (fun x => [x * x]) (fun acc a => LC242.linsert (a * a) acc)

example : evalP prog977 (slOf (-4) [-1, 0, 3, 10]) = [0, 1, 9, 16, 100] := by decide
example : evalP prog977 (slOf (-7) [-3, 2, 3, 11]) = [4, 9, 9, 49, 121] := by decide

/-! ## L1137 — tribonacci: `ℕ` bridged as a UNARY snoc-list, the triple-carrier fold -/

/-- The `Nat → SL Unit` bridge: `n` as `wrap ()` followed by `n` unit snocs — the initial
    algebra `1 + X` of `ℕ` reshaped onto the (non-empty) snoc-list functor. -/
def snocs : Nat → SL Unit
  | 0 => .wrap ()
  | n + 1 => .snoc (snocs n) ()

/-- LC 1137 as a term: carry the L-file's triple `(T n, T(n+1), T(n+2))` (`LC1137.tribTriple`'s
    seed and step verbatim), project the first component. -/
def prog1137 : Prog (SL Unit) Nat :=
  .comp
    (.cata (fun _ => ((0, 1, 1) : Nat × Nat × Nat))
      (fun st _ => (st.2.1, st.2.2, st.1 + st.2.1 + st.2.2)))
    (.fn fun st => st.1)

example : evalP prog1137 (snocs 4) = 4 := by decide
example : evalP prog1137 (snocs 25) = 1389537 := by decide

/-! ## L1143 — longest common subsequence: the DP ROW fold, `ys` a needle parameter

  The L-file's program `col ys` is `foldr (rowStep · ys)` over `xs` — one `cata` whose carrier
  is a whole DP row (`List Nat`), reusing `LC1143.rowStep` verbatim; `ys` is fixed in the term
  like L572's needle.  `col` folds from the RIGHT of the cons-list, so the input is fed to the
  snoc-list fold reversed (`slOf xₙ [xₙ₋₁, …, x₀]`). -/

/-- LC 1143 as a term (second sequence `ys` fixed): fold `xs` (fed reversed) to the DP row,
    project entry 0 (= the row's head, the full-`ys` answer). -/
def prog1143 (ys : List Int) : Prog (SL Int) Nat :=
  .comp
    (.cata (fun x => LC1143.rowStep x ys (List.replicate (ys.length + 1) 0))
      (fun row x => LC1143.rowStep x ys row))
    (.fn fun row => row.headD 0)

-- xs = [1,2,3,4,5] (fed reversed), ys = [1,3,5] → LCS length 3
example : evalP (prog1143 [1, 3, 5]) (slOf 5 [4, 3, 2, 1]) = 3 := by decide
-- xs = [1,2] (fed reversed), ys = [3,4] → 0
example : evalP (prog1143 [3, 4]) (slOf 2 [1]) = 0 := by decide
example : evalP (prog1143 [1, 2, 3]) (slOf 3 [2, 1]) = 3 := by decide

end Freyd.Alg.FinRel.Run8
