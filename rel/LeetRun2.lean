/-
  LeetCodeRun2 — batch L20 L21 L23 L26 L35 L45 L49 L53 L55 RUN in the relation-algebra
  interpreter's fold evaluator (`rel.RelInterp`'s `ProgEval`: `Prog.cata` evaluated by `foldSL`),
  mirroring `rel.LeetRunTree`'s wiring of the tree problems.

  Every list L-file whose program is a fold of the (snoc-)list functor is re-wired as a `Prog`
  TERM whose recursion lives in `cata` — the algebras are the L-files' own `foldFn`s/`foldr`
  steps, transcribed — and RUN by `evalP` on the L-files' own examples.

  Classification of the batch:
  * L20 valid parentheses  — (A) the L-file's own snoc fold, carrier `Int × Bool`
    (depth, never-went-negative), then project `ok && depth = 0`.
  * L21 merge two sorted   — (B) SKIP: the canonical TWO-POINTER — a fuel-indexed lockstep
    recursion peeling the smaller head off EITHER list; not an algebra of the list functor on
    either input (a curried fold would have to replace the program by repeated insertion —
    a different algorithm, i.e. a faked `cata`).
  * L23 merge k sorted     — (A) the L-file IS `foldr LC21.mergeFn []` over the list of lists;
    the binary merge enters only as the algebra's GROUND step (cf. `LC102.mergeLevels` in
    `LeetRunTree`), so the term's recursion is exactly the list-functor fold.
  * L26 dedup sorted       — (A) the L-file's lookahead recursion IS a cons fold: since adjacent
    dedup preserves the head value (`head (dedupFn l) = head l` — dropping `x` from `x :: y :: _`
    happens only when `x = y`), the one-step lookahead reads off the FOLDED tail's head, giving
    the algebra `step c x = if x = head c then c else x :: c`.
  * L35 search insert      — (A) the L-file's linear scan is literally `foldr` with carrier `Nat`
    (target a term parameter, like `LeetRunTree.prog572`'s needle).
  * L45 jump game II       — (A) the L-file's layered-greedy snoc fold, carrier
    `(idx, curEnd, farthest, jumps)`; `solveFn` folds only the PREFIX (no jump is taken FROM the
    last index), recovered by tupling "answer if the input ended just before here" into the
    carrier (the same banana-split move as `LeetRunTree.prog572`'s rebuilt subtree).
  * L49 group anagrams     — (A) the L-file IS `foldr insertInto []`; `insertInto` (and the
    `isort` anagram key inside it) is the algebra's ground step.
  * L53 maximum subarray   — (A) Kadane, the L-file's snoc fold with carrier
    `(bestEndingHere, bestSoFar)`, then `Prod.snd` — the exact `prog121` shape.
  * L55 jump game          — (A) the L-file's greedy snoc fold, carrier `(maxReach, ok)`; the
    step consults the current POSITION (`len` of the processed prefix), recovered by tupling the
    running length into the carrier.

  Wired: 8 of 9.  Cons-side folds (`foldr`) run over the `consOf` bridge (the snoc fold replays
  `foldr` on the reversed spine); snoc-side folds transport the L-files' own `SnocList` examples
  via `ofSnoc`.  `SL` is non-empty (as is `SnocList`), so the `foldr` problems' empty-input cases
  (`mergeKFn [] = []`, `groupFn [] = []` — both just the seed) have no term-level counterpart.
-/
import rel.RelInterp
import leet.L20
import leet.L23
import leet.L26
import leet.L35
import leet.L45
import leet.L49
import leet.L53
import leet.L55

namespace Freyd.Alg.FinRel.Run2

open Freyd.Alg.FinRel.ProgEval
-- `Freyd.Alg.RelSet.SL` is the snoc-list infra NAMESPACE (`SnocList` lives there); the
-- interpreter carrier `SL` is a TYPE (`ProgEval.SL`) — same surface name, no clash (only one is
-- a constant; cf. the `TB` note in `rel.LeetRunTree`).  NOT opened, to keep `ProgEval.imax`
-- unambiguous.
open Freyd.Alg.RelSet

/-- Transport a `SnocList A A` (the L-files' datatype, living in `Rel(Set)`) onto the interpreter
    carrier `SL` — lets every snoc-side demo reuse the L-files' own example builders (`ofOpens`,
    `ofList`). -/
def ofSnoc {A : Type} : SL.SnocList A A → SL A
  | .wrap a    => .wrap a
  | .snoc xs a => .snoc (ofSnoc xs) a

/-- Read a non-empty CONS list `a :: rest` onto `SL` with the spine reversed, so that
    `foldSL base step` replays `foldr f e (a :: rest)` with `base x = f x e` (the last element
    against the seed) and `step c x = f x c` — the bridge for the L-files whose program is a
    `List.foldr`. -/
def consOf {A : Type} (a : A) : List A → SL A
  | []        => .wrap a
  | b :: rest => .snoc (consOf b rest) a

/-! ## L20 — valid parentheses: the depth-scan fold, project `ok && depth = 0` -/

/-- LC 20 as a term: `LC20.foldFn`'s algebra (running `(depth, never-negative)`), then
    `LC20.validFn`'s final test. -/
def prog20 : Prog (SL Bool) Bool :=
  .comp
    (.cata (fun b => if b then ((1 : Int), true) else (0, false))
      (fun st b =>
        if b then (st.1 + 1, st.2)
        else (st.1 - 1, st.2 && decide (1 ≤ st.1))))
    (.fn fun st => st.2 && decide (st.1 = 0))

example : evalP prog20 (ofSnoc (LC20.ofOpens true [false])) = true := by decide        -- "()"
example : evalP prog20 (ofSnoc (LC20.ofOpens true [true, false, false])) = true := by decide
example : evalP prog20 (ofSnoc (LC20.ofOpens false [true])) = false := by decide       -- ")("
example : evalP prog20 (ofSnoc (LC20.ofOpens true [true])) = false := by decide        -- "(("
example : evalP prog20 (ofSnoc (LC20.ofOpens true [false, false])) = false := by decide -- "())"

/-! ## L23 — merge k sorted lists: `foldr LC21.mergeFn []`, the binary merge as ground step

  (L21 itself is the SKIPPED two-pointer — see the header.  Here it is not recursed INTO by the
  term: the term's recursion is the fold over the list OF lists, `mergeFn` a ground map.) -/

/-- LC 23 as a term: `LC23.mergeKFn`'s `foldr` over the `consOf` bridge. -/
def prog23 : Prog (SL (List Int)) (List Int) :=
  .cata (fun l => LC21.mergeFn l []) (fun c l => LC21.mergeFn l c)

example : evalP prog23 (consOf ([1, 4, 5] : List Int) [[1, 3, 4], [2, 6]])
    = [1, 1, 2, 3, 4, 4, 5, 6] := by decide
example : evalP prog23 (consOf ([1] : List Int) [[], [-1, 3]]) = [-1, 1, 3] := by decide

/-! ## L26 — remove duplicates from sorted: the head-lookahead fold

  `LC26.dedupFn (x :: y :: rest)` branches on `y`, the UN-deduped tail's head — but adjacent
  dedup preserves the head value, so `y` is recoverable as the FOLDED tail's head, making the
  recursion a genuine cons fold (the `[]` branch of the step is unreachable: a fold of a
  non-empty list is non-empty). -/

/-- LC 26 as a term: `base x = [x]`, `step c x = if x = head c then c else x :: c`. -/
def prog26 : Prog (SL Int) (List Int) :=
  .cata (fun x => [x])
    (fun c x => match c with
      | []     => [x]
      | b :: _ => if x = b then c else x :: c)

example : evalP prog26 (consOf (1 : Int) [1, 2]) = [1, 2] := by decide
example : evalP prog26 (consOf (0 : Int) [0, 1, 1, 1, 2, 2]) = [0, 1, 2] := by decide

/-! ## L35 — search insert position: the linear scan as `foldr`, target a term parameter -/

/-- LC 35 as a term (target `t` fixed, like `LeetRunTree.prog572`'s needle):
    `LC35.insertPosFn`'s recurrence `f x c = if t ≤ x then 0 else 1 + c`, seed `0`. -/
def prog35 (t : Int) : Prog (SL Int) Nat :=
  .cata (fun x => if t ≤ x then 0 else 1) (fun c x => if t ≤ x then 0 else 1 + c)

example : evalP (prog35 5) (consOf (1 : Int) [3, 5, 6]) = 2 := by decide
example : evalP (prog35 2) (consOf (1 : Int) [3, 5, 6]) = 1 := by decide
example : evalP (prog35 7) (consOf (1 : Int) [3, 5, 6]) = 4 := by decide

/-! ## L45 — jump game II: the layered-greedy fold, answer-tupled

  `LC45.solveFn (snoc dec _)` is `(foldFn dec).jumps` — the fold of the PREFIX, because no jump
  is ever taken FROM the last index.  The term tuples "the answer if the input ended just before
  the current element" (= the previous state's `jumps`) into the carrier and projects it. -/

/-- LC 45 as a term: carrier `((idx, curEnd, farthest, jumps), answer-so-far)`; the state
    component steps by `LC45.foldFn`'s snoc branch, the answer component lags one element. -/
def prog45 : Prog (SL Nat) Nat :=
  .comp
    (.cata (fun x => (((0, x, x, 1) : Nat × Nat × Nat × Nat), (0 : Nat)))
      (fun c dig =>
        let st := c.1
        let idx' := st.1 + 1
        let far' := LC45.nmax st.2.2.1 (idx' + dig)
        ((if idx' = st.2.1 then (idx', far', far', st.2.2.2 + 1)
          else (idx', st.2.1, far', st.2.2.2)),
         st.2.2.2)))
    (.fn Prod.snd)

example : evalP prog45 (ofSnoc (LC45.ofList 2 [3, 1, 1, 4])) = 2 := by decide
example : evalP prog45 (ofSnoc (LC45.ofList 2 [3, 0, 1, 4])) = 2 := by decide
example : evalP prog45 (ofSnoc (LC45.ofList 0 [])) = 0 := by decide
example : evalP prog45 (ofSnoc (LC45.ofList 1 [1])) = 1 := by decide

/-! ## L49 — group anagrams: `foldr insertInto []`, the keyed insert as ground step -/

/-- LC 49 as a term: `LC49.groupFn`'s `foldr` over the `consOf` bridge (`insertInto` — and the
    `isort` anagram key inside it — is the algebra's ground step). -/
def prog49 : Prog (SL (List Int)) (List (List (List Int))) :=
  .cata (fun s => LC49.insertInto s []) (fun c s => LC49.insertInto s c)

-- letters as distinct Ints: e=1 a=2 t=3 n=4 b=5 — "eat" "tea" "tan" "ate" "nat" "bat"
example : evalP prog49
    (consOf ([1, 2, 3] : List Int) [[3, 1, 2], [3, 2, 4], [2, 3, 1], [4, 2, 3], [5, 2, 3]])
    = [[[5, 2, 3]], [[3, 2, 4], [4, 2, 3]], [[1, 2, 3], [3, 1, 2], [2, 3, 1]]] := by decide

/-! ## L53 — maximum subarray (Kadane): the `(bestEndingHere, bestSoFar)` fold, project the best -/

/-- LC 53 as a term: `LC53.foldFn`'s algebra, then `Prod.snd` — the exact `prog121` shape. -/
def prog53 : Prog (SL Int) Int :=
  .comp
    (.cata (fun x => ((x, x) : Int × Int))
      (fun st p => let e := imax p (st.1 + p); (e, imax st.2 e)))
    (.fn Prod.snd)

example : evalP prog53 (ofSnoc (LC53.ofList (-2) [1, -3, 4, -1, 2, 1, -5, 4])) = 6 := by decide
example : evalP prog53 (ofSnoc (LC53.ofList (-1) [])) = -1 := by decide
example : evalP prog53 (ofSnoc (LC53.ofList 1 [2, 3])) = 6 := by decide
example : evalP prog53 (ofSnoc (LC53.ofList (-3) [-1, -2])) = -1 := by decide

/-! ## L55 — jump game: the greedy `(maxReach, ok)` fold, position-tupled

  `LC55.foldFn`'s step consults the current position (`len` of the processed prefix), so the
  term tuples the running length into the carrier: `(len, maxReach, ok)`, projecting `ok`. -/

/-- LC 55 as a term: `LC55.foldFn`'s algebra with the index made part of the carrier. -/
def prog55 : Prog (SL Nat) Bool :=
  .comp
    (.cata (fun x => ((1, x, true) : Nat × Nat × Bool))
      (fun st p =>
        if st.1 > st.2.1 then (st.1 + 1, st.2.1, false)
        else (st.1 + 1, LC55.imax st.2.1 (st.1 + p), st.2.2)))
    (.fn fun st => st.2.2)

example : evalP prog55 (ofSnoc (LC55.ofList 2 [3, 1, 1, 4])) = true := by decide
example : evalP prog55 (ofSnoc (LC55.ofList 3 [2, 1, 0, 4])) = false := by decide
example : evalP prog55 (ofSnoc (LC55.ofList 0 [])) = true := by decide
example : evalP prog55 (ofSnoc (LC55.ofList 1 [0])) = true := by decide

end Freyd.Alg.FinRel.Run2
