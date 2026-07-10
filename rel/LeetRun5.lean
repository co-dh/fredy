/-
  LeetCodeRun5 — batch L198 L205 L206 L213 L217 L230 L231 L234 L238 RUN in the
  relation-algebra interpreter's fold evaluator.

  Mirrors `rel.LeetRunTree`: each L-file's solution that IS a structural fold is re-wired as a
  `Prog` term (`fn`/`comp`/`cata`/`cataT`, `rel.RelInterp`'s `ProgEval` fragment) whose recursion
  lives in `cata` (snoc-list) — one tree problem, L230, in `cataT` — and RUN by `evalP` on the
  L-files' own examples.  HONEST FRAMING: this runs the existing programs (≈ `#eval solveFn`);
  the value is coverage of the interpreter's applicative fragment.

  Wired (7):
  * L198 house robber — the L-file's own DP algebra `LC198.algFn`, reused through the `Fobj`
    injections, then `Prod.fst`.
  * L206 reverse list — reversal IS the snoc-list catamorphism `wrap x ↦ [x]`,
    `snoc xs a ↦ a :: rev xs` (the L-file's `revFn = List.reverse`, refolded).
  * L213 house robber II (circle) — ring-breaking as ONE fold: the carrier tracks THREE copies
    of L198's linear DP state (full row, row-without-last = the state before the latest snoc,
    row-without-first = never seeded with the wrap element) plus a singleton marker; the final
    ground map takes `imax` of the two broken rows (the L-file's `circAnswer`, whose two
    `robLine` passes are direction-symmetric to L198's snoc algebra).
  * L217 contains duplicate — `LC217.hasDup`'s snoc step needs the PREFIX itself (`memB xs q`),
    so it is not literally an algebra; banana-split (rebuild the prefix in the carrier, reusing
    the L-file's own `SnocList`/`memB`) closes it, then `Prod.snd`.
  * L230 kth smallest in a BST — the TREE functor (`cataT`): the inorder algebra
    `nil ↦ []`, `node ↦ Ll ++ a :: Lr` (the L-file's `inorder`), then index `k-1` (`k` a term
    parameter, like `LeetRunTree.prog572`'s needle).
  * L234 palindrome list — `isPalinFn xs = decide (xs = reverse xs)` uses its input twice;
    banana-split (carrier = rebuilt input × reversed input), then compare — both components
    grown by the one snoc algebra.
  * L238 product of array except self — the L-file's two passes (prefix × suffix products,
    zipped) read the input twice; as ONE fold the carrier is `(prefix product so far,
    continuation: product-of-what-comes-after ↦ answers of the processed part)` — a
    function carrier like `LeetRunTree.prog98`'s bounds — closed by applying to `1`.

  Not expressible as a fold, and why (2):
  * L205 isomorphic strings — a lockstep scan over TWO lists carrying two association maps
    (hashmap shape); the L-file itself notes it is "not a fold over a book-worthy datatype",
    and `Prog` has no pairing former to feed a term both lists.
  * L231 power of two — the input is a bare `Int`, no list/tree structure at all; the program
    is a fuel-guarded halving loop, i.e. an UNFOLD (anamorphism) — the term language has
    `cata`/`cataT` only (same reason `LeetRunTree` excludes L297's `deserialize`).
-/
import rel.RelInterp
import rel.LeetRunTree
import leet.L198
import leet.L206
import leet.L213
import leet.L217
import leet.L230
import leet.L234
import leet.L238

namespace Freyd.Alg.FinRel.Run5

open Freyd.Alg.FinRel.ProgEval
open Freyd.Alg.FinRel.RunTree (ofTree)
-- `Freyd.Alg.RelSet.SL` is the snoc-list infra NAMESPACE (`SnocList` lives there); the
-- interpreter carrier `SL` is a TYPE (`ProgEval.SL`) — same surface name, no clash
-- (`LeetRunTree`'s `TB` remark, list edition).
open Freyd.Alg.RelSet Freyd.Alg.RelSet.SL

/-! ## L198 — house robber: the `(best, prevBest)` DP fold, the L-file's own algebra -/

/-- LC 198 as a term: `LC198.algFn` reused verbatim through the `Fobj` injections
    (`wrap x ↦ (max x 0, 0)`, `snoc ↦ (max best (prevBest+p), best)`), then `Prod.fst`. -/
def prog198 : Prog (SL Int) Int :=
  .comp
    (.cata (fun x => LC198.algFn (Sum.inl x)) (fun st p => LC198.algFn (Sum.inr (st, p))))
    (.fn Prod.fst)

example : evalP prog198 (slOf 1 [2, 3, 1]) = 4 := by decide
example : evalP prog198 (slOf 2 [7, 9, 3, 1]) = 12 := by decide
example : evalP prog198 (slOf 5 []) = 5 := by decide
example : evalP prog198 (slOf (-3) [-1]) = 0 := by decide

/-! ## L206 — reverse list: reversal IS the snoc catamorphism -/

/-- LC 206 as a term: `rev (wrap x) = [x]`, `rev (snoc xs a) = a :: rev xs` — the snoc-list
    refolding of the L-file's `revFn = List.reverse` (structural output, `LeetRunTree.prog226`'s
    shape on lists). -/
def prog206 : Prog (SL Int) (List Int) :=
  .cata (fun a => [a]) (fun acc a => a :: acc)

example : evalP prog206 (slOf 1 [2, 3]) = [3, 2, 1] := by decide
example : evalP prog206 (slOf 1 []) = [1] := by decide
-- agrees with the L-file's own program on its example
example : evalP prog206 (slOf 1 [2, 3]) = LC206.revFn [1, 2, 3] := by decide

/-! ## L213 — house robber II: ring-breaking folded into ONE pass

  `LC213.circAnswer` runs the linear DP twice, on `dropLast` and on `tail` — two slices of the
  SAME input, which a term cannot read twice.  But both slices' DP states are maintainable in
  one left-to-right fold: `s_tail` is the linear state never seeded with the wrap element,
  `s_pre` (= row without its LAST house) is simply the full row's state BEFORE the latest snoc.
  A singleton marker handles the one-house case (`imax x 0`), exactly the L-file's own guard. -/

/-- LC 213 as a term: carrier `(singleton?, s_full, s_dropLast, s_tail)`, all three DP states
    stepped by L198's algebra; final ground map = the L-file's ring-breaking `imax`. -/
def prog213 : Prog (SL Int) Int :=
  .comp
    (.cata
      (fun x => ((some x, LC198.algFn (Sum.inl x), (0, 0), (0, 0)) :
        Option Int × (Int × Int) × (Int × Int) × (Int × Int)))
      (fun c p => match c with
        | (_, sf, _, st) =>
          (none, LC198.algFn (Sum.inr (sf, p)), sf, LC198.algFn (Sum.inr (st, p)))))
    (.fn fun c => match c with
      | (some x, _, _, _) => LC213.imax x 0
      | (none, _, sp, st) => LC213.imax sp.1 st.1)

example : evalP prog213 (slOf 2 [3, 2]) = 3 := by decide
example : evalP prog213 (slOf 1 [2, 3, 1]) = 4 := by decide
example : evalP prog213 (slOf 1 [2, 3]) = 3 := by decide
example : evalP prog213 (slOf 5 []) = 5 := by decide
-- agrees with the L-file's own program on its examples
example : evalP prog213 (slOf 1 [2, 3, 1]) = LC213.solveFn (LC213.ofList 1 [2, 3, 1]) := by decide

/-! ## L217 — contains duplicate: banana-split around the L-file's `memB` -/

/-- LC 217 as a term: `hasDup`'s step reads the prefix itself (`memB xs q`), so the carrier
    rebuilds the prefix — as the L-file's own `SnocList`, so `LC217.memB` is reused verbatim —
    alongside the dup flag; then `Prod.snd`. -/
def prog217 : Prog (SL Int) Bool :=
  .comp
    (.cata (fun x => ((SnocList.wrap x, false) : SnocList Int Int × Bool))
      (fun c q => (SnocList.snoc c.1 q, c.2 || LC217.memB c.1 q)))
    (.fn Prod.snd)

example : evalP prog217 (slOf 1 [2, 3, 1]) = true := by decide
example : evalP prog217 (slOf 1 [2, 3, 4]) = false := by decide
example : evalP prog217 (slOf 1 []) = false := by decide
example : evalP prog217 (slOf 1 [1]) = true := by decide

/-! ## L230 — kth smallest in a BST: the inorder tree fold, then index -/

/-- LC 230 as a term (`k` fixed, 1-indexed): the L-file's `inorder` algebra
    (`nil ↦ []`, `node ↦ Ll ++ a :: Lr`) as a `cataT`, then the ground map `·[k-1]?`. -/
def prog230 (k : Nat) : Prog (TB Int) (Option Int) :=
  .comp (.cataT [] fun Ll a Lr => Ll ++ a :: Lr) (.fn fun l => l[k - 1]?)

example : evalP (prog230 1) (ofTree LC230.sampleBST) = some 2 := by decide
example : evalP (prog230 3) (ofTree LC230.sampleBST) = some 4 := by decide
example : evalP (prog230 6) (ofTree LC230.sampleBST) = some 9 := by decide
example : evalP (prog230 7) (ofTree LC230.sampleBST) = none := by decide

/-! ## L234 — palindrome list: banana-split `(rebuilt, reversed)`, then compare

  `LC234.isPalinFn xs = decide (xs = revFn xs)` reads its input twice — `Prog` has no pairing
  former, so the fold's carrier carries BOTH lists: the rebuilt input (snoc at the back) and
  its reversal (cons at the front, `prog206`'s algebra). -/

/-- LC 234 as a term: fold to `(input, reversed input)`, then the equality ground map. -/
def prog234 : Prog (SL Int) Bool :=
  .comp
    (.cata (fun a => (([a], [a]) : List Int × List Int))
      (fun c a => (c.1 ++ [a], a :: c.2)))
    (.fn fun c => decide (c.1 = c.2))

example : evalP prog234 (slOf 1 [2, 2, 1]) = true := by decide
example : evalP prog234 (slOf 1 [2]) = false := by decide
example : evalP prog234 (slOf 1 []) = true := by decide
-- agrees with the L-file's own program on its examples
example : evalP prog234 (slOf 1 [2, 2, 1]) = LC234.isPalinFn [1, 2, 2, 1] := by decide

/-! ## L238 — product except self: the two passes fused by a continuation carrier

  `LC238.solveFn` zips a prefix-product pass with a suffix-product pass — the input read twice.
  As ONE fold the carrier is `(p, k)`: `p` = product of the processed prefix, and the
  continuation `k suf` = the answer row for the processed positions GIVEN that everything after
  the prefix multiplies to `suf` (a function carrier, `LeetRunTree.prog98`'s move).  Step at
  `a`: earlier positions' "after" now includes `a` (`k (a * suf)`), the new position's answer is
  `p * suf`.  Closing the fold applies `k` to the empty suffix product `1`. -/

/-- LC 238 as a term: fold to `(prefix product, suffix-continuation)`, apply to `1`. -/
def prog238 : Prog (SL Int) (List Int) :=
  .comp
    (.cata (fun x => ((x, fun suf => [suf]) : Int × (Int → List Int)))
      (fun c a => (c.1 * a, fun suf => c.2 (a * suf) ++ [c.1 * suf])))
    (.fn fun c => c.2 1)

example : evalP prog238 (slOf 1 [2, 3, 4]) = [24, 12, 8, 6] := by decide
example : evalP prog238 (slOf 0 [4, 0]) = [0, 0, 0] := by decide
example : evalP prog238 (slOf (-1) [1, 2]) = [2, -2, -1] := by decide
-- agrees with the L-file's own (two-pass) program on its example
example : evalP prog238 (slOf 1 [2, 3, 4]) = LC238.solveFn [1, 2, 3, 4] := by decide

end Freyd.Alg.FinRel.Run5
