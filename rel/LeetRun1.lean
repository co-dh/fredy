/-
  LeetCodeRun1 — batch L1 L2 L3 L5 L9 L11 L13 L14 L19 RUN in the relation-algebra interpreter.

  Breadth pass over the batch: every problem whose L-file solution is a fold of the LIST functor
  (a snoc-list catamorphism with a scalar/tuple carrier) is re-wired as a `Prog` term —
  `Prog.cata base step [≫ .fn proj]`, evaluated by `foldSL` via `evalP` — REUSING the L-file's own
  algebra, and run on the L-file's own examples.  Mirrors `rel/LeetRunTree.lean` (`cataT`) for the
  list former `cata`.

  Wired (3):
  * L3  longest substring without repeating — `LC3.algFn` verbatim: the sliding window carried as
    `(window content, best)`, project the best.
  * L13 roman to integer — the two-element-lookahead recurrence, tupled into a fold: carrier
    `(value so far, previous symbol)`; the pending symbol is resolved against each new symbol and
    flushed by the final projection.
  * L14 longest common prefix — fold the `<+:`-meet `LC14.commonPrefix2` over the strings
    (element type `List Int`: the carrier is one string, the running prefix).

  Not a list-functor fold, and why (6):
  * L1  two sum — the scan carries an unbounded seen-association-list (the hashmap) and exits
    early on a hit; the L-file has no fold ("not a fold over an initial algebra", its own header).
  * L2  add two numbers — two-input lockstep carry-ripple recursion, fuel-tamed; neither list is
    folded alone.
  * L5  longest palindromic substring — expand-around-center two-pointer: each step matches the
    reversed prefix against the ENTIRE remaining suffix (`commonPrefixLen left (x :: rest)`), so
    the step is not a function of (folded value, element).
  * L9  palindrome number — the input is a scalar `Int`; the digit sequence is produced by a
    fuel-guarded UNFOLD (anamorphism), and the term language has `cata`/`cataT` only.
  * L11 container with most water — two-pointer sweep with fuel; the L-file's own header:
    "no catamorphism to exploit".
  * L19 remove nth node from end — positional splice `take k ++ drop (k+1)` with `k` computed by
    formula; no fold anywhere (wiring it would be a lone `.fn`, i.e. a faked `cata`).
-/
import rel.RelInterp
import leet.L3
import leet.L13
import leet.L14

namespace Freyd.Alg.FinRel.Run1

open Freyd.Alg.FinRel.ProgEval
-- `Freyd.Alg.RelSet.SL` is the snoc-list infra NAMESPACE; the interpreter carrier `SL` is a TYPE
-- (`ProgEval.SL`) — same surface name, no clash (only one is a constant), cf. `LeetRunTree`'s `TB`.
open Freyd.Alg.RelSet

/-- Build an interpreter snoc-list from a first element and the rest, in order — the raw-`List`
    bridge (cf. `leet.L121.ofList`/`ProgEval.slOf`, generalized in the element type so the L14
    demos can fold over strings-as-lists). -/
def ofL {A : Type} (first : A) (rest : List A) : SL A := rest.foldl SL.snoc (SL.wrap first)

/-! ## L3 — longest substring without repeating characters: the sliding-window fold -/

/-- LC 3 as a term: `LC3.algFn`'s algebra verbatim — carrier `(window content, best)`,
    `wrap x ↦ ([x], 1)`, `snoc ↦ (slide the window, bump the best)` — then project the best. -/
def prog3 : Prog (SL Int) Nat :=
  .comp
    (.cata (fun x => LC3.algFn (Sum.inl x)) (fun st c => LC3.algFn (Sum.inr (st, c))))
    (.fn Prod.snd)

example : evalP prog3 (ofL 97 [98, 99, 97, 98, 98]) = 3 := by decide       -- "abcabb" → "abc"
example : evalP prog3 (ofL 112 [119, 119, 107, 101, 119]) = 3 := by decide -- "pwwkew" → "wke"
-- agreement with the L-file's own fold, on its own example
example : evalP prog3 (ofL 98 [98, 98]) = LC3.solveFn (LC3.ofList 98 [98, 98]) := by decide

/-! ## L13 — roman to integer: the lookahead recurrence tupled into a fold

  `LC13.romanFn` compares each symbol with its immediate SUCCESSOR — a two-element lookahead,
  not literally an algebra.  Tupling makes it one (the list-side analogue of `LeetRunTree`'s
  carrier reshapings): carry `(value so far, previous symbol)`; each new symbol `y` resolves the
  pending `prev` (subtracted iff `prev < y`), and the final projection flushes the last symbol,
  always added. -/

/-- LC 13 as a term: fold to `(resolved value, pending symbol)`, then flush the pending symbol. -/
def prog13 : Prog (SL Int) Int :=
  .comp
    (.cata (fun x => ((0 : Int), x))
      (fun st y => (st.1 + (if st.2 < y then -st.2 else st.2), y)))
    (.fn fun st => st.1 + st.2)

example : evalP prog13 (ofL 1 [1, 1]) = 3 := by decide                            -- III
example : evalP prog13 (ofL 1 [5]) = 4 := by decide                               -- IV
example : evalP prog13 (ofL 1000 [100, 1000, 10, 100, 1, 5]) = 1994 := by decide  -- MCMXCIV
-- agreement with the L-file's own recurrence, on its own example
example : evalP prog13 (ofL 1000 [100, 1000, 10, 100, 1, 5])
    = LC13.romanFn [1000, 100, 1000, 10, 100, 1, 5] := by decide

/-! ## L14 — longest common prefix: fold the `<+:`-meet over the strings

  `LC14.lcpFn` is a right fold of `LC14.commonPrefix2` (singleton base, cons step); the snoc
  term folds LEFT, which computes the same prefix because `commonPrefix2` is the `<+:`-meet
  (`commonPrefix2_prefix`/`commonPrefix2_greatest`), hence associative on values. -/

/-- LC 14 as a term: element type `List Int` (one string), carrier the running common prefix. -/
def prog14 : Prog (SL (List Int)) (List Int) :=
  .cata (fun s => s) fun acc s => LC14.commonPrefix2 acc s

-- ["flower","flow","flight"] → "fl"
example : evalP prog14
    (ofL [102, 108, 111, 119, 101, 114] [[102, 108, 111, 119], [102, 108, 105, 103, 104, 116]])
    = [102, 108] := by decide
-- ["dog","racecar","car"] → ""
example : evalP prog14
    (ofL [100, 111, 103] [[114, 97, 99, 101, 99, 97, 114], [99, 97, 114]]) = [] := by decide
-- agreement with the L-file's own fold, on its own example
example : evalP prog14
    (ofL [102, 108, 111, 119, 101, 114] [[102, 108, 111, 119], [102, 108, 105, 103, 104, 116]])
    = LC14.lcpFn [[102, 108, 111, 119, 101, 114], [102, 108, 111, 119],
                  [102, 108, 105, 103, 104, 116]] := by decide

end Freyd.Alg.FinRel.Run1
