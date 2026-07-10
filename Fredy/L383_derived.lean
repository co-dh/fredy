/-
  LeetCode 383 — Ransom Note — DERIVED as a `ConsList` catamorphism (all-fold on `Bool`).

  `Fredy/L383.lean`'s `canBuildFn ransom magazine := ransom.all (fun c => decide (countL ransom c ≤
  countL magazine c))` is a `List.all` scan — head-first, `(c :: cs).all p = p c && cs.all p` — the
  exact shape of a `ConsList` cons-fold (`CL.consFold_unique`, `Fredy/A6_GenFold.lean`), reshaping
  `ransom : List Int` onto `CL.ofList ransom : ConsList Unit Int` (the shared bridge, NOT redefined
  here).

  1. **Carrier** — `C := Bool`, the SAME carrier `List.all` already returns; no tupling needed.

  2. **Base/step, `ransom`/`magazine` FIXED as parameters of the step** — unlike `L217D`'s hash-set
     carrier (where the accumulated state grows with the prefix), here the two lists that decide
     each letter's bound — `ransom` (for `countL ransom c`) and `magazine` (for `countL magazine c`)
     — are CLOSED OVER by `step`, not threaded through the fold: they are the same `ransom` at every
     cons, not a prefix. Forced by matching `canBuildFn`'s own equations:
     * base `g () = true` (`[].all p = true`);
     * step `step ransom magazine c b = decide (countL ransom c ≤ countL magazine c) && b`
       (`(c :: cs).all p = p c && cs.all p`).
     `CL.consFold_unique g (step ransom magazine) canBuildFold …` PRODUCES the fold as
     `cataR (consScalarAlg g (step ransom magazine))` — the scan over `ransom` is not hand-written,
     it emerges.

  3. **Bridge** — `canBuildFold_ofList` shows, by induction on ANY list `xs` (not just `ransom`),
     that `canBuildFold ransom magazine (CL.ofList xs) = xs.all (fun c => decide (countL ransom c ≤
     countL magazine c))`; specializing `xs := ransom` gives DEFINITIONAL equality with
     `LC383.canBuildFn ransom magazine`.

  4. **Correctness is REUSED, not re-proved** — shape-3 DECISION headline, transported from
     `LC383.canBuild_correct` (an `iff`, not a refinement+domination extremum).

  Complexity: `O(n·m)` natural (`n = ransom.length`, `m = magazine.length`; each of the `n` steps
  calls `countL ransom c` (`O(n)`) and `countL magazine c` (`O(m)`) once) — the same bound as
  `L383.canBuildFn`, unimproved; a hash-count carrier is a separate, unrequested optimization.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  Routes only through
  `CL.consFold_unique` (a plain uniqueness induction), never `cataR_eq_relCata` (pulls
  `Classical.choice`).
-/
import Fredy.A6_GenFold
import Fredy.A6_ConsList
import Fredy.L383

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC383D

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.LC383

/-! ## The `Bool` carrier and its FORCED base/step, `ransom`/`magazine` FIXED parameters -/

/-- The base of the emergent algebra: an empty ransom note trivially can be built
    (`[].all p = true`). -/
def g : Unit → Bool := fun _ => true

/-- The step of the emergent algebra, for FIXED `ransom magazine : List Int` (closed over, the same
    lists at every cons — NOT the growing prefix): test the head letter `c`'s bound against
    `magazine`, `&&` with the folded tail's answer.  Mirrors `List.all`'s own
    `(c :: cs).all p = p c && cs.all p`. -/
def step (ransom magazine : List Int) (c : Int) (b : Bool) : Bool :=
  decide (LC242.countL ransom c ≤ LC242.countL magazine c) && b

/-- The `Bool`-carrying fold, written as its two defining equations (so `canBuildFold_wrap`/
    `canBuildFold_cons` are `rfl` and `CL.consFold_unique` applies). -/
def canBuildFold (ransom magazine : List Int) : ConsList Unit Int → Bool
  | ConsList.wrap _    => g ()
  | ConsList.cons c xs => step ransom magazine c (canBuildFold ransom magazine xs)

theorem canBuildFold_wrap (ransom magazine : List Int) (u : Unit) :
    canBuildFold ransom magazine (ConsList.wrap u) = g u := rfl

theorem canBuildFold_cons (ransom magazine : List Int) (c : Int) (xs : ConsList Unit Int) :
    canBuildFold ransom magazine (ConsList.cons c xs) =
      step ransom magazine c (canBuildFold ransom magazine xs) := rfl

/-! ## The `Bool` fold EMERGES via the general cons-fold law -/

/-- **The all-fold EMERGES.**  `graph (canBuildFold ransom magazine)` equals the catamorphism of
    the emergent scalar algebra `consScalarAlg g (step ransom magazine)` — PRODUCED by
    `CL.consFold_unique` from the forced base `g` and step `step ransom magazine`, never written by
    hand.  The letter-checking scan over `ransom` is now one catamorphism over `F X = Unit + Int × X`
    on the carrier `Bool`. -/
theorem canBuild_emerges (ransom magazine : List Int) :
    (graph (canBuildFold ransom magazine) : dCL Unit Int ⟶ (⟨Bool⟩ : RelSet.{0})) =
      cataR (consScalarAlg g (step ransom magazine)) :=
  consFold_unique g (step ransom magazine) (canBuildFold ransom magazine)
    (canBuildFold_wrap ransom magazine) (canBuildFold_cons ransom magazine)

/-! ## Connecting the emergent fold back to `L383.canBuildFn` -/

/-- The emergent fold, run on `CL.ofList xs` for ANY list `xs` (not just `ransom`), computes exactly
    the `List.all` scan `xs.all (fun c => decide (countL ransom c ≤ countL magazine c))` — by
    induction on `xs`, unfolding `canBuildFold`'s `wrap`/`cons` equations against `List.all`'s own
    `all_nil`/`all_cons`. -/
theorem canBuildFold_ofList (ransom magazine : List Int) :
    ∀ xs : List Int, canBuildFold ransom magazine (ofList xs) =
      xs.all (fun c => decide (LC242.countL ransom c ≤ LC242.countL magazine c))
  | [] => rfl
  | c :: cs => by
      show step ransom magazine c (canBuildFold ransom magazine (ofList cs)) =
        (c :: cs).all (fun c => decide (LC242.countL ransom c ≤ LC242.countL magazine c))
      rw [canBuildFold_ofList ransom magazine cs, List.all_cons]
      rfl

/-- The emergent fold on `ofList ransom` IS `L383.canBuildFn ransom magazine` — definitional after
    specializing the bridge to `xs := ransom`. -/
theorem canBuildFold_eq_canBuildFn (ransom magazine : List Int) :
    canBuildFold ransom magazine (ofList ransom) = LC383.canBuildFn ransom magazine :=
  canBuildFold_ofList ransom magazine ransom

/-- The derived solver: the emergent cons-fold on `CL.ofList ransom`, uncurried on the pair. -/
def derivedSolveFn (p : (List Int) × (List Int)) : Bool :=
  canBuildFold p.1 p.2 (ofList p.1)

/-- The derived solver as a morphism `Pair ⟶ Bool`. -/
def derivedSolve : LC383.Pair ⟶ LC383.dBool := graph derivedSolveFn

/-- The derived solver IS `L383.solve` — `derivedSolveFn p = canBuildFold p.1 p.2 (ofList p.1) =
    canBuildFn p.1 p.2 = solveFn p` (`canBuildFold_eq_canBuildFn`, then `L383.solveFn`'s own
    definition). -/
theorem derivedSolve_eq_solve : derivedSolve = LC383.solve := by
  unfold derivedSolve LC383.solve
  congr 1
  funext p
  show derivedSolveFn p = LC383.solveFn p
  unfold derivedSolveFn LC383.solveFn
  exact canBuildFold_eq_canBuildFn p.1 p.2

/-! ## Correctness of the derived program, transported from `L383.canBuild_correct` -/

/-- **The Ransom-Note program is the `ConsList`-carrying catamorphism, and it is correct.**  The
    honest headline bundles:

    * `canBuild_emerges` — `graph (canBuildFold ransom magazine) = cataR (consScalarAlg g (step
      ransom magazine))`: the `List.all` scan IS the catamorphism over the carrier `Bool`; and
    * the transported correctness — for ANY value `v` the emergent fold relates `ofList ransom` to,
      `v` decides the "can build" question, `v = true ↔ CanBuild ransom magazine`. Emergence pins
      `v = canBuildFold ransom magazine (ofList ransom)`, `canBuildFold_eq_canBuildFn` identifies it
      with `L383.canBuildFn ransom magazine`, and `L383.canBuild_correct` (the existing decision
      `Iff`, NOT re-proved here) finishes. -/
theorem canBuild_derived_correct (ransom magazine : List Int) :
    ((graph (canBuildFold ransom magazine) : dCL Unit Int ⟶ (⟨Bool⟩ : RelSet.{0})) =
        cataR (consScalarAlg g (step ransom magazine))) ∧
    (∀ v : Bool, cataFold (consScalarAlg g (step ransom magazine)) (ofList ransom) v →
        (v = true ↔ LC383.CanBuild ransom magazine)) := by
  refine ⟨canBuild_emerges ransom magazine, ?_⟩
  intro v hv
  have hgr : (graph (canBuildFold ransom magazine) : dCL Unit Int ⟶ (⟨Bool⟩ : RelSet.{0}))
      (ofList ransom) v := by rw [canBuild_emerges]; exact hv
  have hveq : v = canBuildFold ransom magazine (ofList ransom) := hgr
  rw [hveq, canBuildFold_eq_canBuildFn]
  exact LC383.canBuild_correct ransom magazine

/-! ## Running the emergent program -/

-- letters encoded as distinct `Int`s: a=97 b=98 (same examples as `L383.lean`)
example : canBuildFold [97] [98] (ofList [97]) = false := by decide
example : canBuildFold [97, 98] [97, 98, 98] (ofList [97, 98]) = true := by decide
example : derivedSolveFn ([97], [98]) = false := by decide
example : derivedSolveFn ([97, 98], [97, 98, 98]) = true := by decide

end Freyd.Alg.RelSet.LC383D
