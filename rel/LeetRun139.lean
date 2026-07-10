/-
  LeetRun139 — L139 Word Break RUN in the relation-algebra interpreter's fold evaluator
  (`rel.RelInterp`'s `ProgEval`).

  Word Break is a DECISION problem whose recursion is COURSE-OF-VALUES: the breakability of a
  suffix depends on the breakability of MANY shorter suffixes (`leet/L139`'s `wordBreakFuel`), so
  it is neither a raw structural fold nor a fixed-width tupling — exactly the `L322`/`L300`
  tabulating-DP shape.  `leet/L139_derived` already RESHAPES it into a TABULATING fold over the
  SUFFIX axis whose carrier is the growing table of sub-answers

      C := List α × List Bool        -- (the current suffix string, its dp table)

  produced by the general-carrier fold-uniqueness law (`LC139D.tab`, base `g`, step `st`, cell
  `cell = L139.stepBreak` reading the prior table course-of-values).  This file RUNS that exact
  fold in the interpreter, as a `Prog.cata` over the interpreter's snoc-list `SL`.

  Orientation.  The interpreter's `foldSL` reaches the `wrap` (deepest) element FIRST, so to fold
  the string right-to-left the way `LC139D.tab`'s cons fold does — reaching the empty suffix first
  and prepending chars — the string is loaded LAST char at the `wrap` (`revSlOf`).  Then the fold
  is `LC139D.tab` on the nose (`foldSL_revSlOf`): `base c = st c (g ())`, `step p c = st c p`.

  Deliverable.  `prog139 dict := .cata … ≫ .fn (read the last table cell)`, and a GENERAL bridge
  (not just examples): `prog139_decides : evalP (prog139 dict) (revSlOf c cs) = true ↔ Seg dict
  (c :: cs)` and `prog139_eq_wordBreakFn : evalP (prog139 dict) (revSlOf c cs) =
  L139.wordBreakFn dict (c :: cs)`, chaining `L139_derived`'s `tab_correct` / `L139`'s
  `wordBreak_correct`.  `SL` is nonempty by design, so the empty string is out of the bridge's
  range (as in every other `LeetRun*` file); all demos are `L139`'s own nonempty examples.

  Mathlib-free; sorry-free; axioms ⊆ {propext, Quot.sound}.
-/
import rel.RelInterp
import leet.L139_derived

namespace Freyd.Alg.FinRel.Break139

open Freyd.Alg.FinRel.ProgEval
open Freyd.Alg.RelSet

variable {α : Type} [DecidableEq α]

/-! ## Loading the string suffix-axis-first, and the tabulating algebra as an `SL` fold -/

/-- Load a nonempty string `first :: rest` into the interpreter's `SL` with its LAST char at the
    `wrap`, so `foldSL` consumes it right-to-left — the suffix-axis order the course-of-values
    table folds over (mirrors `LC139D.tab`'s cons fold reaching the empty suffix first). -/
def revSlOf (first : α) : List α → SL α
  | [] => .wrap first
  | c :: cs => .snoc (revSlOf c cs) first

/-- Base of the `SL` fold: process the single (last) char from the empty-suffix table —
    `L139_derived`'s `st` applied to `g ()`. -/
def base139 (dict : List (List α)) (c : α) : List α × List Bool := LC139D.st dict c (LC139D.g ())

/-- Step of the `SL` fold: prepend the next char and append its dp cell — `L139_derived`'s `st`
    with the fold's argument order (`C → A → C`). -/
def step139 (dict : List (List α)) (p : List α × List Bool) (c : α) : List α × List Bool :=
  LC139D.st dict c p

/-- **The `SL` fold IS `L139_derived`'s tabulating fold**: folding the suffix-axis-loaded string
    reproduces `LC139D.tab` on the nose (induction on `rest`, generalising `first`). -/
theorem foldSL_revSlOf (dict : List (List α)) :
    ∀ (first : α) (rest : List α),
      foldSL (base139 dict) (step139 dict) (revSlOf first rest)
        = LC139D.tab dict (LC139D.clist (first :: rest))
  | first, [] => rfl
  | first, c :: cs => by
    show step139 dict (foldSL (base139 dict) (step139 dict) (revSlOf c cs)) first
      = LC139D.tab dict (LC139D.clist (first :: c :: cs))
    rw [foldSL_revSlOf dict c cs]
    rfl

/-- **LC 139 as a term**: cata over the suffix-axis string into the growing dp table
    (`L139_derived`'s `g`/`st` algebra), then read the last cell (index `|s|`, the whole string's
    breakability). -/
def prog139 (dict : List (List α)) : Prog (SL α) Bool :=
  .comp (.cata (base139 dict) (step139 dict)) (.fn fun p => LC139D.nthB p.2 p.1.length)

/-! ## The wiring is exact: the interpreter run decides `Seg`, equals `wordBreakFn` -/

/-- **The interpreter run decides segmentation**: `prog139`'s answer on the suffix-axis-loaded
    `c :: cs` is `true` iff `c :: cs` splits into dictionary words — `foldSL_revSlOf` chained to
    `L139_derived`'s `tab_correct` (the reconstructed suffix's length is `|c::cs|` by `tab_fst`). -/
theorem prog139_decides (dict : List (List α)) (first : α) (rest : List α) :
    evalP (prog139 dict) (revSlOf first rest) = true ↔ LC139.Seg dict (first :: rest) := by
  show LC139D.nthB (foldSL (base139 dict) (step139 dict) (revSlOf first rest)).2
      (foldSL (base139 dict) (step139 dict) (revSlOf first rest)).1.length = true
    ↔ LC139.Seg dict (first :: rest)
  rw [foldSL_revSlOf dict first rest, LC139D.tab_fst dict (first :: rest)]
  exact LC139D.tab_correct dict (first :: rest)

/-- **The interpreter run equals `L139.wordBreakFn`** — both decide `Seg`, so they are equal
    Booleans (`L139.bool_eq_of_iff_true`). -/
theorem prog139_eq_wordBreakFn (dict : List (List α)) (first : α) (rest : List α) :
    evalP (prog139 dict) (revSlOf first rest) = LC139.wordBreakFn dict (first :: rest) :=
  LC139.bool_eq_of_iff_true
    ((prog139_decides dict first rest).trans (LC139.wordBreak_correct dict (first :: rest)).symm)

/-! ## Running the program, on L139's own examples (`Char`, so words read as words) -/

-- "leetcode" = "leet" ++ "code"  → true
example : evalP (prog139 ["leet".toList, "code".toList]) (revSlOf 'l' "eetcode".toList) = true := by
  decide
-- "applepenapple" = "apple" ++ "pen" ++ "apple"  → true
example :
    evalP (prog139 ["apple".toList, "pen".toList]) (revSlOf 'a' "pplepenapple".toList) = true := by
  decide
-- "catsandog" cannot be segmented by {cats,dog,sand,and,cat}  → false
example :
    evalP (prog139 ["cats".toList, "dog".toList, "sand".toList, "and".toList, "cat".toList])
      (revSlOf 'c' "atsandog".toList) = false := by decide
-- agreement with the L-file's own program, on its own example
example :
    evalP (prog139 ["leet".toList, "code".toList]) (revSlOf 'l' "eetcode".toList)
      = LC139.wordBreakFn ["leet".toList, "code".toList] "leetcode".toList := by decide

#eval evalP (prog139 ["leet".toList, "code".toList]) (revSlOf 'l' "eetcode".toList)         -- true
#eval evalP (prog139 ["apple".toList, "pen".toList]) (revSlOf 'a' "pplepenapple".toList)     -- true
#eval evalP (prog139 ["cats".toList, "dog".toList, "sand".toList, "and".toList, "cat".toList])
  (revSlOf 'c' "atsandog".toList)                                                            -- false

end Freyd.Alg.FinRel.Break139
