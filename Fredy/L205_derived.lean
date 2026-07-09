/-
  LeetCode 205 — Isomorphic Strings — DERIVED as a HIGHER-ORDER (lockstep) cons-list catamorphism.

  `Fredy/L205.lean` WRITES the two-input scan `isoGo mapST mapTS s t : Bool` by hand — a single
  left-to-right pass over BOTH lists `s`, `t` together, threading two association lists `mapST`/`mapTS`
  as accumulators, verified by ONE generalized induction (`isoGo_iff`).  A two-list scan carrying state
  is not a catamorphism over one list — until you CURRY it.  Read `isoGo mapST mapTS s t` as
  `s ↦ (mapST mapTS t ↦ …)`: folding the FIRST list `s` produces a RESIDUAL decision procedure

      `Resid := List (Int × Int) → List (Int × Int) → List Int → Bool`

  that still awaits the two maps and the second list `t`.  With this FUNCTION carrier the accumulator
  scan collapses to an ordinary front-to-back cons-list fold, exposed by the general-carrier
  fold-uniqueness law `CL.consFold_unique` (`Fredy/A6_GenFold.lean`) — the same law's `C = List D`
  instance is the tabulating DP used by `L139`/`L1143`, but here `C` is a FUNCTION type, so the
  two-input scan becomes a single catamorphism over `s`.

  Raw Lean `List Int` is not an initial algebra here, so we reshape `s` along the front-to-back axis
  into `ConsList Unit Int` (`ofList`), mirror `isoGo` (curried on `mapST`/`mapTS`/`t`) as the fold
  `foldCL : ConsList Unit Int → Resid`, and read its base `g = isoGo · · []`-shape and step off the two
  `isoGo` clauses.  `foldCL`'s two defining equations `foldCL (wrap ·) = g ·`,
  `foldCL (cons x ·) = step x ·` hold by `rfl`, so `CL.consFold_unique g step foldCL rfl rfl` PRODUCES
  the higher-order catamorphism `cataR (consScalarAlg g step)` and identifies it with `graph foldCL`
  (`iso_emerges`): the curried scan is not written, it emerges.  The bridge `foldCL_ofList`
  (`foldCL (ofList s) mapST mapTS t = isoGo mapST mapTS s t`, induction on `s`) reconnects the emergent
  residual to the concrete program; at the initial maps `[] []` this is `isIsoFn`, and `L205`'s decision
  correctness `iso_correct` (the two-way map-scan `iff`, NOT re-proved here) transports onto the
  emergent fold (`iso_derived_correct`).

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataFold` /
  `consFold_unique` only, never the `cataR_eq_relCata` bridge (which pulls `Classical.choice`).
-/
import Fredy.A6_GenFold
import Fredy.A6_ConsList
import Fredy.L205

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Freyd.Alg.RelSet.LC205D

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.LC205

/-! ## The residual carrier and the base/step, READ OFF `L205.isoGo` (curried on the maps and `t`)

  Carrier `Resid` — the RESIDUAL decision procedure that, having folded the first list, still awaits
  the two association lists `mapST`/`mapTS` and the second list `t`. -/

/-- The higher-order carrier: a decision procedure awaiting both maps and the second list. -/
abbrev Resid : Type := List (Int × Int) → List (Int × Int) → List Int → Bool

/-- The base of the emergent algebra: `g` = the residual after folding the EMPTY first list — it
    accepts exactly when the second list is also empty (`isoGo`'s `[], []` / `[], _::_` clauses,
    curried on the maps and `t`; the maps are irrelevant at the base). -/
def g : Unit → Resid := fun _ mapST mapTS t =>
  match t with
  | []     => true
  | _ :: _ => false

/-- The step of the emergent algebra: from the tail's residual `rec = foldCL xs` and the current
    `s`-head `x`, the parent's residual `foldCL (cons x xs)`.  It answers a second list `y :: ys` by
    the `isoGo` head logic — look `x` up in `mapST`, `y` up in `mapTS`; if both fresh, record the new
    pair in both maps and hand `ys` to `rec`; if both seen, accept iff the recorded partners agree and
    hand `ys` to `rec`; any mismatch rejects.  A `[]` second list rejects (`isoGo`'s `_::_, []`
    clause).  Read off `isoGo`'s `x::xs, y::ys` clause, curried on the awaited maps and `t`. -/
def step : Int → Resid → Resid := fun x rec mapST mapTS t =>
  match t with
  | []      => false
  | y :: ys =>
    match lookupL x mapST, lookupL y mapTS with
    | some y1, some x1 => decide (y1 = y) && decide (x1 = x) && rec mapST mapTS ys
    | none,    none    => rec ((x, y) :: mapST) ((y, x) :: mapTS) ys
    | some _,  none    => false
    | none,    some _  => false

/-- The curried scan as a cons-list fold, defined FROM `g`/`step` so `consFold_unique` applies by
    `rfl`.  Folding `s` front-to-back into its residual decision procedure `foldCL (ofList s) : Resid`,
    which still awaits the two maps and the second list. -/
def foldCL : ConsList Unit Int → Resid
  | ConsList.wrap l    => g l
  | ConsList.cons x xs => step x (foldCL xs)

/-! ## The FORCED first-order recursion of the curried scan (both hold by `rfl`) -/

/-- The base condition: `foldCL (wrap d) = g d`. -/
theorem hwrap : ∀ d, foldCL (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition: `foldCL (cons x xs) = step x (foldCL xs)` — the scan's first-order
    lockstep recurrence in curried form, defined not proved (it is `foldCL`'s own `cons` clause). -/
theorem hcons : ∀ (x : Int) (xs : ConsList Unit Int),
    foldCL (ConsList.cons x xs) = step x (foldCL xs) := fun _ _ => rfl

/-! ## The higher-order catamorphism EMERGES via the general-carrier law -/

/-- **The residual decision procedure EMERGES.**  `graph foldCL` equals the catamorphism of the
    scalar cons-list algebra `consScalarAlg g step = [ wrap ↦ g, (x, rec) ↦ step x rec ]` on the
    FUNCTION carrier `Resid`, PRODUCED by `CL.consFold_unique` from the forced base `g` and step
    `step`.  The two-list accumulator scan is now a single catamorphism over the first list, whose
    output is the residual `foldCL (ofList s) : Resid` awaiting the maps and the second list — the AOP
    curry that turns a two-input, state-threading decision into a fold. -/
theorem iso_emerges :
    (graph foldCL : dCL Unit Int ⟶ ⟨Resid⟩) = cataR (consScalarAlg g step) :=
  CL.consFold_unique g step foldCL hwrap hcons

/-! ## Reshaping `List Int` onto the initial algebra, and the bridge back to `isoGo` -/

/-- Reshape a raw list onto the front-to-back cons-list initial algebra. -/
def ofList : List Int → ConsList Unit Int
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- **Bridge**: the emergent residual applied to the maps and the second list is exactly the concrete
    scan `isoGo`.  Induction on `s`; each step is the two `isoGo`/`step` clauses aligned (the maps and
    `t` are handed through unchanged in the recursive positions). -/
theorem foldCL_ofList (s : List Int) :
    ∀ (mapST mapTS : List (Int × Int)) (t : List Int),
      foldCL (ofList s) mapST mapTS t = isoGo mapST mapTS s t := by
  induction s with
  | nil => intro mapST mapTS t; cases t <;> rfl
  | cons x xs ih =>
    intro mapST mapTS t
    cases t with
    | nil => rfl
    | cons y ys =>
      show step x (foldCL (ofList xs)) mapST mapTS (y :: ys)
          = isoGo mapST mapTS (x :: xs) (y :: ys)
      rcases hlx : lookupL x mapST with _ | y1 <;> rcases hly : lookupL y mapTS with _ | x1 <;>
        simp only [step, isoGo, hlx, hly, ih]

/-! ## Connecting the emergent residual back to the two-input `solve` -/

/-- The derived solver: feed the initial empty maps and the SECOND list `p.2` into the residual
    `foldCL (ofList p.1)` the emergent catamorphism produces from the first list `p.1`. -/
def derivedSolve : Input ⟶ dBool :=
  graph (fun p : List Int × List Int => foldCL (ofList p.1) [] [] p.2)

/-- The derived solver IS `L205.solve` — the two-input program is "fold the first list to a residual,
    then apply it to the empty maps and the second list" (`= isIsoFn` by the bridge at `[] []`). -/
theorem derivedSolve_eq_solve : derivedSolve = LC205.solve := by
  apply hom_ext; intro p b
  show (b = foldCL (ofList p.1) [] [] p.2) ↔ (b = isIsoFn p.1 p.2)
  rw [foldCL_ofList p.1 [] [] p.2]
  exact Iff.rfl

/-! ## Correctness of the derived program, transported from `L205.iso_correct` -/

/-- **The Isomorphic-Strings program is the higher-order catamorphism, and it is correct.**  The
    honest headline bundles:

    * `iso_emerges` — `graph foldCL = cataR (consScalarAlg g step)`: the curried scan IS the
      higher-order catamorphism over the FUNCTION carrier `Resid`; and
    * the transported correctness — for ANY residual `f` the emergent fold relates the first list
      `ofList s` to, `f` fed the initial empty maps decides `IsIso` against every second list `t`
      (`f [] [] t = true ↔ IsIso s t`).  Emergence pins `f = foldCL (ofList s)`, the bridge reduces
      `f [] [] t` to `isoGo [] [] s t = isIsoFn s t`, and `L205.iso_correct` (the existing
      map-scan decision correctness, NOT re-proved here) supplies the `iff`. -/
theorem iso_derived_correct :
    ((graph foldCL : dCL Unit Int ⟶ ⟨Resid⟩) = cataR (consScalarAlg g step)) ∧
    (∀ (s : List Int) (f : Resid),
        cataFold (consScalarAlg g step) (ofList s) f →
        ∀ t : List Int, f [] [] t = true ↔ LC205.IsIso s t) := by
  refine ⟨iso_emerges, ?_⟩
  intro s f hf t
  have hgr : (graph foldCL : dCL Unit Int ⟶ ⟨Resid⟩) (ofList s) f := by
    rw [iso_emerges]; exact hf
  have hfeq : f = foldCL (ofList s) := hgr
  subst hfeq
  rw [foldCL_ofList s [] [] t]
  exact iso_correct s t

/-! ## Running / cross-checking the emergent fold against `Fredy/L205.lean`

  The relational catamorphism `cataFold (consScalarAlg …)` has a FUNCTION carrier, so equality on it
  is not decidable — we never `decide` a residual.  We `decide` the residual's RESULT `Bool` after
  applying it to the empty maps and the second list (extensionally `isoGo [] [] s t = isIsoFn s t`),
  and separately PROVE the higher-order fold relates a first list to its residual. -/

-- "egg" / "add" → true (pattern a,b,b both times)
example : foldCL (ofList [101, 103, 103]) [] [] [97, 100, 100] = true := by decide
-- "foo" / "bar" → false (foo repeats, bar doesn't)
example : foldCL (ofList [102, 111, 111]) [] [] [98, 97, 114] = false := by decide
-- "paper" / "title" → true (pattern a,b,a,c,d both times)
example : foldCL (ofList [112, 97, 112, 101, 114]) [] [] [116, 105, 116, 108, 101] = true := by decide

/-- The emergent higher-order fold genuinely relates `ofList [101,103,103]` to its RESIDUAL decision
    procedure `foldCL (ofList [101,103,103]) : Resid` — the function the fold produces, proved via
    `iso_emerges` (no `decide` on the function carrier). -/
example : cataFold (consScalarAlg g step)
    (ofList [101, 103, 103]) (foldCL (ofList [101, 103, 103])) := by
  have h : (graph foldCL : dCL Unit Int ⟶ ⟨Resid⟩)
      (ofList [101, 103, 103]) (foldCL (ofList [101, 103, 103])) := rfl
  rw [iso_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC205D
