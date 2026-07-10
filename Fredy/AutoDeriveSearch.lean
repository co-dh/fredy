/-
  AUTO-DERIVE SEARCH — the PROPOSE → TEST → CERTIFY loop (proof of concept).

  Deriving an efficient program from a relational spec splits into (1) INVENTING the auxiliary
  fold state — undecidable in general — and (2) everything downstream, which is mechanical.
  For problems whose optimal state is a KNOWN shape, this file closes the loop automatically:

  * PROPOSE — a catalog of candidate programs, enumerated from standard state shapes:
    running scalars (`max`, `sum`), sixteen `(running, best)` pair combinations
    (2 seeds × 4 running-updates × 2 best-updates), and a memo-list fallback.  Each candidate
    is a `ProgEval.Prog` term, runnable by the structural-fold evaluator `evalP` (polynomial).

  * TEST — the differential tester runs the SPEC as the relation-algebra term
    `A spec ≫ max D` through the `FinRel` interpreter (`Demo121.answers`: exponential in the
    value range, exact) and compares its decoded answer with each candidate's `evalP` output
    on an EXHAUSTIVELY ENUMERATED set of small instances (every price list of length ≤ 3 over
    `{1,2,3}`).  Candidates that disagree anywhere are REJECTED; survivors are ranked by
    state cost (catalog order).  Fully automatic, `#eval`-able, and kernel-checkable
    (`by decide`).  No human picks the state shape or the tests.

  * CERTIFY — the surviving shape instantiates the `AutoDerive.RunningBest` driver: its eight
    arithmetic side conditions are one-line `imin`/`imax`/`omega` facts (auto-dischargeable);
    the driver then emits full extremum correctness on ALL inputs and the §7.5 morphism
    headline `solve = max (≤) · Λ spec`.

  Demonstrated end-to-end on LeetCode 121 (best time to buy/sell stock): the loop REJECTS
  the plain running-max and 16 other wrong shapes and SELECTS the `(runningMin, best)` pair,
  which is then certified.  The tested candidate and the certified fold are proved to be the
  SAME program (`tested_eq_certified`), so the empirical selection and the proof talk about
  one object.

  HONEST BOUNDARY.  Certification is automatic EXCEPT the spec characterisation
  `gen_sound`/`spec_gen` ("the generator's search space is exactly the spec") — a genuinely
  problem-specific induction (~70 lines in `Fredy.L121`, reused here via `gen_eq`).  That
  proof is the residual creative obligation; nothing in this file synthesises it.  Also:
  the tester validates FUNCTIONAL agreement only — the correct-but-expensive memo-list
  candidate passes too, and is rejected only by the catalog's state-cost RANKING, not by
  testing.  And the runnable spec (`Demo121.specFn`, offset-encoded over `Fin (2M+1)`) is a
  bounded encoding of the abstract spec `LC121.profit`; their agreement is by construction,
  not by a Lean proof.

  Mathlib-free.  Certified parts Sorry-free; axioms ⊆ {propext, Classical.choice, Quot.sound}
  (inherited from `horner_correct` via `RunningBest`).
-/
import Fredy.RelInterp
import Fredy.AutoDerive
import Fredy.L121

set_option linter.unusedVariables false

namespace Freyd.Alg.Search

open Freyd
open Freyd.Alg.RelSet          -- graph, LC121.*
open Freyd.Alg.RelSet.SL       -- SnocList, dSL, cataFold, RunningBest, imin/imax
open Freyd.Alg.FinRel          -- Demo121.*, ProgEval.*

/-! ## PROPOSE — the catalog of candidate state shapes -/

/-- A catalog entry: a named runnable program over non-empty price lists. -/
structure Candidate where
  name : String
  prog : ProgEval.Prog (ProgEval.SL Int) Int

/-- Pair-state shape: fold to `(running e, best b)` with seed `base`, running update `s1`,
    best update `s2` (both given the OLD running value), answer `b`. -/
def pairProg (base : Int → Int × Int) (s1 : Int → Int → Int) (s2 : Int → Int → Int → Int) :
    ProgEval.Prog (ProgEval.SL Int) Int :=
  .comp (.cata base fun st p => (s1 st.1 p, s2 st.1 st.2 p)) (.fn Prod.snd)

/-- Memo-list shape: keep ALL elements, post-process by brute force.  Always functionally
    correct — included to show the tester cannot reject it; only the cost RANKING does. -/
def bruteBest : List Int → Int
  | [] => 0
  | p :: rest => rest.foldl (fun acc b => imax acc (p - b)) (bruteBest rest)

/-- Pair-shape ingredient lists: seeds, running updates, best updates.  The names encode the
    combination; the enumeration below is the PROPOSE step. -/
def seeds : List (String × (Int → Int × Int)) :=
  [("b0=0", fun x => (x, 0)), ("b0=x", fun x => (x, x))]
def runUpds : List (String × (Int → Int → Int)) :=
  [("min", fun e p => imin e p), ("max", fun e p => imax e p),
   ("keep", fun e _ => e), ("kad", fun e p => imax p (e + p))]
def bestUpds : List (String × (Int → Int → Int → Int)) :=
  [("sell", fun e b p => imax b (p - e)), ("kadb", fun e b p => imax b (imax p (e + p)))]

/-- The catalog, ranked by state cost: scalars, then pairs, then the memo list. -/
def catalog : List Candidate :=
  ⟨"scalar max", .cata (fun x => x) imax⟩ ::
  ⟨"scalar sum", .cata (fun x => x) (· + ·)⟩ ::
  (seeds.flatMap fun b => runUpds.flatMap fun s1 => bestUpds.map fun s2 =>
    ⟨s!"pair {b.1}·{s1.1}·{s2.1}", pairProg b.2 s1.2 s2.2⟩) ++
  [⟨"memo list", .comp (.cata (fun x => [x]) fun l a => a :: l) (.fn bruteBest)⟩]

/-! ## TEST — differential testing against the interpreted spec term -/

/-- A test instance: a non-empty day-ordered price list. -/
structure Inst where
  first : Int
  rest : List Int

def Inst.prices (i : Inst) : List Int := i.first :: i.rest
def Inst.n (i : Inst) : Nat := i.rest.length + 1
/-- Profit bound: `maxPrice − minPrice`; all achievable profits lie in `[-M, M]`, so the
    offset encoding over `Fin (2M+1)` is faithful.  Computed FROM the instance. -/
def Inst.bound (i : Inst) : Nat :=
  (i.rest.foldl imax i.first - i.rest.foldl imin i.first).toNat
def Inst.priceFn (i : Inst) : Fin i.n → Int := fun k => i.prices.getD k.val 0

/-- THE SPEC SIDE: run `A spec ≫ max D` through the `FinRel` interpreter (exponential —
    `2^(2M+1)` subset codes) and decode the answer column.  A singleton list on every
    well-formed instance (the `≤`-maximum is unique). -/
def specAnswer (i : Inst) : List Int :=
  (Demo121.answers i.n i.bound i.priceFn).filterMap id

/-- THE CANDIDATE SIDE: run the program by structural fold (polynomial). -/
def progAnswer (p : ProgEval.Prog (ProgEval.SL Int) Int) (i : Inst) : Int :=
  ProgEval.evalP p (ProgEval.slOf i.first i.rest)

/-- Differential test on one instance. -/
def agree (p : ProgEval.Prog (ProgEval.SL Int) Int) (i : Inst) : Bool :=
  specAnswer i == [progAnswer p i]

def passes (p : ProgEval.Prog (ProgEval.SL Int) Int) (insts : List Inst) : Bool :=
  insts.all (agree p)

/-- Candidates surviving differential testing, in catalog (cost) order. -/
def survivors (cs : List Candidate) (insts : List Inst) : List String :=
  (cs.filter fun c => passes c.prog insts).map (·.name)

/-- THE LOOP'S OUTPUT: the cheapest surviving candidate. -/
def select (cs : List Candidate) (insts : List Inst) : Option String :=
  (cs.find? fun c => passes c.prog insts).map (·.name)

/-- Exhaustive test-instance enumeration: EVERY price list of length 2 or 3 over `{1, 2, 3}`
    (36 instances) — no human picks the tests either.  Among them, `⟨2,[1]⟩` kills every
    `b0=x` seed (profit must start at 0), `⟨2,[1,2]⟩` kills every wrong running update (the
    buy must move to the later minimum), `⟨1,[2]⟩` kills the scalars. -/
def smallInsts : List Inst :=
  let vals : List Int := [1, 2, 3]
  (vals.flatMap fun a => vals.map fun b => Inst.mk a [b]) ++
  (vals.flatMap fun a => vals.flatMap fun b => vals.map fun c => Inst.mk a [b, c])

/-! ### Running the loop -/

-- The interpreted spec answers on a sample of instances:
#eval ([⟨1, [2]⟩, ⟨2, [1]⟩, ⟨2, [1, 2]⟩, ⟨3, [2, 4, 1]⟩] : List Inst).map specAnswer
-- Every candidate's verdict over all 36 enumerated instances:
#eval catalog.map fun c => (c.name, passes c.prog smallInsts)
-- The survivors and the selection:
#eval survivors catalog smallInsts
#eval select catalog smallInsts

/-! ### Kernel-checked rejection / acceptance (`by decide`)

  The named exhibits.  `runMaxProg` is the catalog's "scalar max" (plain running max — the
  shape that misses the pair); `fromFirstProg` is "pair b0=0·keep·sell" (running max of
  `p − p₀` — it never updates the buy price); `winnerProg` is "pair b0=0·min·sell". -/

def runMaxProg : ProgEval.Prog (ProgEval.SL Int) Int := .cata (fun x => x) imax
def fromFirstProg : ProgEval.Prog (ProgEval.SL Int) Int :=
  pairProg (fun x => (x, 0)) (fun e _ => e) (fun e b p => imax b (p - e))
def winnerProg : ProgEval.Prog (ProgEval.SL Int) Int :=
  pairProg (fun x => (x, 0)) (fun e p => imin e p) (fun e b p => imax b (p - e))

/-- The winner is literally `RelInterp`'s hand-written derived program. -/
theorem winner_eq_prog121 : winnerProg = ProgEval.prog121 := rfl

-- REJECTED (kernel-checked): plain running max returns 2 on prices [1,2]; the interpreted
-- spec's maximum profit is 1.
example : agree runMaxProg ⟨1, [2]⟩ = false := by decide
-- REJECTED (kernel-checked): the from-first pair returns 0 on [2,1,2]; the spec says 1
-- (buy the LATER minimum 1, sell 2) — the running coordinate must actually run.
example : agree fromFirstProg ⟨2, [1, 2]⟩ = false := by decide
-- ACCEPTED (kernel-checked): the (runningMin, best) pair agrees on the whole suite's
-- kernel-sized prefix.
example : passes winnerProg [⟨1, [2]⟩, ⟨2, [1]⟩, ⟨2, [1, 2]⟩] = true := by decide

/-- **THE SELECTION, kernel-checked**: on the `M = 1` instances the loop's verdict vector over
    the full 19-candidate catalog is exactly this — every scalar and every wrong pair
    combination rejected, the `(runningMin, best)` pair and the memo list accepted — and the
    cost ranking picks the pair.  No human chose the shape. -/
theorem loop_verdicts :
    (catalog.map fun c => passes c.prog [⟨1, [2]⟩, ⟨2, [1]⟩, ⟨2, [1, 2]⟩])
      = [false, false, true, false, false, false, false, false, false, false,
         false, false, false, false, false, false, false, false, true] := by decide

theorem loop_selects_winner :
    select catalog [⟨1, [2]⟩, ⟨2, [1]⟩, ⟨2, [1, 2]⟩] = some "pair b0=0·min·sell" := by decide

/-! ## CERTIFY — the selected shape through the `RunningBest` driver

  The winning catalog entry instantiates `AutoDerive.RunningBest`.  Everything below the
  bundle is MECHANICAL: the eight side-condition fields are one-line `imin`/`imax`/`omega`
  facts (this is the "auto-discharge" half of certification), and the driver then emits
  extremum correctness and the §7.5 morphism headline.

  The one CREATIVE input is the spec characterisation — the generator's search space equals
  the achievable-profit spec.  It is a problem-specific induction; here it is `Fredy.L121`'s
  `gen_sound`/`spec_gen` (~70 lines there), transported along `gen_eq` because the bundle's
  generator is definitionally L121's. -/

/-- The certification bundle for the selected shape.  Data fields = the winning catalog
    combination (`b0=0`, `min`, `sell`) plus its generator candidates and dominance order;
    proof fields = the eight one-line arithmetic facts (the auto-dischargeable part). -/
def l121 : RunningBest Int Int Int where
  base x := (x, 0)
  step1 e p := imin e p
  step2 e b p := imax b (p - e)
  cand1 e p w1 := w1 = e ∨ w1 = p
  cand2 e b p _ w2 := w2 = b ∨ w2 = p - e
  ord e e' := e ≤ e'
  ord_refl e := Int.le_refl e
  ord_trans h1 h2 := Int.le_trans h1 h2
  step1_mono p h := imin_mono h (Int.le_refl p)
  step2_mono p h1 h2 := imax_mono h2 (by omega)
  step1_cand e p := imin_eq_or e p
  step2_cand e b p := imax_eq_or b (p - e)
  cand1_le h := by
    rcases h with h | h <;> rw [h]
    · exact imin_le_left _ _
    · exact imin_le_right _ _
  cand2_le h1 h2 := by
    rcases h2 with h | h <;> rw [h]
    · exact imax_ge_left _ _
    · exact imax_ge_right _ _

/-- The bundle's generator IS `L121`'s generator. -/
theorem gen_eq : l121.gen = LC121.gen := by
  funext u w
  cases u with
  | inl x => rfl
  | inr q => obtain ⟨st, p⟩ := q; rfl

/-- Generator soundness for the bundle — `LC121.gen_sound` transported along `gen_eq`.
    THE RESIDUAL CREATIVE OBLIGATION lives behind this line: `LC121.gen_sound` is a
    problem-specific induction, not derivable from the catalog. -/
theorem gen_spec' (xs : SnocList Int Int) (w : Int × Int) (h : cataFold l121.gen xs w) :
    LC121.spec xs w.2 :=
  (LC121.gen_sound xs w (by rw [← gen_eq]; exact h)).2

/-- Generator completeness for the bundle — `LC121.spec_gen` transported along `gen_eq`. -/
theorem spec_gen' (xs : SnocList Int Int) (v : Int) (hv : LC121.spec xs v) :
    ∃ e, cataFold l121.gen xs (e, v) := by
  rw [gen_eq]; exact LC121.spec_gen xs v hv

/-- **CERTIFIED**: the selected fold's best component is an achievable profit and dominates
    every achievable profit — on ALL inputs, not just the tested ones.  Emitted by the
    `RunningBest` driver from the bundle + the spec characterisation. -/
theorem solve_correct (xs : SnocList Int Int) :
    LC121.profit xs (l121.foldFn xs).2 ∧ ∀ v, LC121.profit xs v → v ≤ (l121.foldFn xs).2 :=
  l121.correct LC121.spec gen_spec' spec_gen' xs

/-- **CERTIFIED §7.5 headline**: the selected program IS `max (≤) · Λ spec` as a morphism of
    `Rel(Set)`. -/
theorem solve_eq_maxRel :
    (Freyd.Alg.RelSet.graph (fun xs => (l121.foldFn xs).2) : dSL Int Int ⟶ (⟨Int⟩ : RelSet.{0}))
      = A LC121.spec ≫ maxRel (fun w z : Int => z ≤ w) :=
  l121.eq_maxRel LC121.spec gen_spec' spec_gen'

/-! ### The tested candidate and the certified fold are the same program -/

/-- Convert the interpreter's snoc-lists to the derivation's. -/
def toSnoc : ProgEval.SL Int → SnocList Int Int
  | .wrap a => .wrap a
  | .snoc s a => .snoc (toSnoc s) a

/-- The pair-level bridge: the winner's structural fold is the bundle's fold. -/
theorem foldSL_eq_foldFn (s : ProgEval.SL Int) :
    ProgEval.foldSL ProgEval.base121 ProgEval.step121 s = l121.foldFn (toSnoc s) := by
  induction s with
  | wrap a => rfl
  | snoc s a ih =>
    show ProgEval.step121 (ProgEval.foldSL ProgEval.base121 ProgEval.step121 s) a
      = l121.foldFn (toSnoc (ProgEval.SL.snoc s a))
    rw [ih]; rfl

/-- What the tester RAN (`evalP winnerProg`) is what the driver CERTIFIED (`l121.foldFn`'s
    best component): the empirical selection and the proof are about one object. -/
theorem tested_eq_certified (s : ProgEval.SL Int) :
    ProgEval.evalP winnerProg s = (l121.foldFn (toSnoc s)).2 :=
  congrArg Prod.snd (foldSL_eq_foldFn s)

/-- The bundle's fold is `Fredy.L121`'s hand-derived fold — the loop reconstructed the
    existing certified program. -/
theorem foldFn_eq_L121 (xs : SnocList Int Int) : l121.foldFn xs = LC121.foldFn xs := by
  induction xs with
  | wrap x => rfl
  | snoc xs p ih =>
    show (imin (l121.foldFn xs).1 p, imax (l121.foldFn xs).2 (p - (l121.foldFn xs).1)) = _
    rw [ih]; rfl

/-- **END-TO-END**: the program the loop selected empirically is certified optimal on every
    input — the propose → test → certify loop, closed. -/
theorem selected_correct (s : ProgEval.SL Int) :
    LC121.profit (toSnoc s) (ProgEval.evalP winnerProg s) ∧
    ∀ v, LC121.profit (toSnoc s) v → v ≤ ProgEval.evalP winnerProg s := by
  rw [tested_eq_certified]; exact solve_correct (toSnoc s)

-- The certified selected program, run on LeetCode 121's own example:
#eval ProgEval.evalP winnerProg (ProgEval.slOf 7 [1, 5, 3, 6, 4])   -- 5

#print axioms selected_correct
#print axioms solve_eq_maxRel
#print axioms loop_verdicts

end Freyd.Alg.Search
