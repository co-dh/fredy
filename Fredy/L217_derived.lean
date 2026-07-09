/-
  LeetCode 217 — Contains Duplicate — DERIVED from the tupling law.

  `Fredy/L217.lean` WRITES two mutually-referencing folds by hand: `memB xs p` ("does `p` occur in
  the prefix `xs`?") and `hasDup xs` ("does `xs` repeat a value?").  The `snoc` step of `hasDup`
  reads `memB xs q` — the WHOLE prefix's membership tester, not just `hasDup xs` — so `hasDup` on its
  own is NOT the catamorphism of `F X = ℤ + X × ℤ` on the carrier `Bool`: its step looks at more than
  the accumulated boolean.  The AOP fix is the classic "carry the seen-so-far": TUPLE the membership
  tester with the flag into ONE state and the recurrence collapses to first order.  With carrier
  `C := (ℤ → Bool) × Bool` — the pair `(memB xs, hasDup xs)` (`C₁ = ℤ → Bool` the membership tester,
  `C₂ = Bool` the answer) — the tupling law `A6_8_Tupling.tupling` (`SL.tupling`) linearizes it:

    * the tupling ANSATZ `pairFold xs = (memB xs, hasDup xs)` carries the two quantities the naive
      recurrence cross-references (choosing WHICH to tuple is the whole insight);
    * base and step are READ OFF `L217`'s two fold equations, FORCED not guessed:
        `pairFold (wrap x)   = (fun p => eqi p x, false)`                       =: `g x`
        `pairFold (snoc xs q) = (fun p => (memB xs) p || eqi p q, hasDup xs || (memB xs) q)`
                             = step (pairFold xs) q`, writing `(mc, d) := pairFold xs`,
          `step (mc, d) q = (fun p => mc p || eqi p q, d || mc q)`
      the dup flag `d || mc q` READS the membership component `mc` at the new element `q`, so the
      second-order look-back is now a first-order step over the pair;
    * `SL.tupling g step pairFold pairFold_wrap pairFold_snoc` then PRODUCES the pair-carrying fold
      `cataR (pairAlg g step)` and identifies it with `graph pairFold` (`dup_emerges`) — the state
      fold is not written, it emerges.

  Projecting the SECOND component recovers the scalar answer `hasDup`; `derivedSolve` is the emergent
  fold followed by `Prod.snd`, and it equals `L217.solve` (`derivedSolve_eq_solve`).  The DECISION
  correctness is REUSED — `L217.solve_correct : solveFn xs = true ↔ dupP xs`, NOT re-proved — and
  transported onto the emergent fold in the bundled headline `dup_derived_correct`.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route only through `cataFold` /
  `tupling` (a plain uniqueness induction), never the `cataR_eq_relCata` bridge (which pulls
  `Classical.choice`).
-/
import Fredy.A6_8_Tupling
import Fredy.L217

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC217D

open Freyd Freyd.Alg.RelSet.SL Freyd.Alg.RelSet.LC217

/-! ## The tupling ANSATZ and its FORCED base/step

  Carrier `C := (ℤ → Bool) × Bool` — the pair `(memB, hasDup)`: the membership tester `C₁ = ℤ → Bool`
  carried alongside the answer flag `C₂ = Bool`.  All three of `memB`/`hasDup` come from
  `Fredy/L217.lean`; tupling them into one state is the insight. -/

/-- Carry the pair `(memB xs, hasDup xs)` — the tupling ansatz for the (second-order:
    `hasDup (snoc xs q)` reads `memB xs q`) contains-duplicate recurrence. -/
def pairFold (xs : SnocList Int Int) : (Int → Bool) × Bool := (memB xs, hasDup xs)

/-- The base of the emergent algebra, forced by
    `pairFold (wrap x) = (memB (wrap x), hasDup (wrap x)) = (fun p => eqi p x, false)`:
    a one-element array's tester matches only `x`, and it has no duplicate. -/
def g : Int → (Int → Bool) × Bool := fun x => (fun p => eqi p x, false)

/-- The step of the emergent algebra, forced by `L217`'s two `snoc` equations.  Carrying
    `(mc, d) = (memB xs, hasDup xs)`, appending `q` gives the new tester `fun p => mc p || eqi p q`
    (matches the prefix OR the new element) and the new flag `d || mc q` (the prefix already
    repeated, OR `q` already occurred in the prefix — READ OFF the membership component `mc`). -/
def step : (Int → Bool) × Bool → Int → (Int → Bool) × Bool :=
  fun st q => (fun p => st.1 p || eqi p q, st.2 || st.1 q)

/-- The base condition is a COMPUTATION, not a guess: `pairFold (wrap x) = g x` — both sides are
    `(fun p => eqi p x, false)` (`memB (wrap x) = fun p => eqi p x`, `hasDup (wrap x) = false`). -/
theorem pairFold_wrap : ∀ x : Int, pairFold (SnocList.wrap x) = g x := fun x => rfl

/-- The step condition is `L217`'s recurrence made first-order: `pairFold (snoc xs q) =
    step (pairFold xs) q`.  Definitional — `memB (snoc xs q) = fun p => memB xs p || eqi p q` and
    `hasDup (snoc xs q) = hasDup xs || memB xs q`, with `memB xs`/`hasDup xs` read off `pairFold xs`;
    the tupling has REMOVED the second-order look-back. -/
theorem pairFold_snoc (xs : SnocList Int Int) (q : Int) :
    pairFold (SnocList.snoc xs q) = step (pairFold xs) q := rfl

/-! ## The state fold EMERGES via the tupling law -/

/-- **The pair-carrying fold EMERGES.**  `graph pairFold` equals the catamorphism of the emergent
    algebra `pairAlg g step` — PRODUCED by `SL.tupling` from the forced base `g` and step `step`,
    never written by hand.  The seen-set-carrying single-pass scan is now one catamorphism over
    `F X = ℤ + X × ℤ` on the carrier `(ℤ → Bool) × Bool`. -/
theorem dup_emerges :
    (graph pairFold : Arr ⟶ (⟨(Int → Bool) × Bool⟩ : RelSet.{0})) = cataR (pairAlg g step) :=
  tupling g step pairFold pairFold_wrap pairFold_snoc

/-! ## Connecting the emergent fold back to `L217.solve` -/

/-- The derived solver: the emergent pair-fold followed by `Prod.snd`, projecting the answer flag
    out of the carried state `(memB xs, hasDup xs)`.  This is the honest "the program is produced by
    the law" morphism — `cataR (pairAlg g step)` is what `SL.tupling` emits. -/
def derivedSolve : Arr ⟶ dBool :=
  cataR (pairAlg g step) ≫ graph (Prod.snd : (Int → Bool) × Bool → Bool)

/-- The derived solver IS `L217.solve`.  Replacing the emergent catamorphism by `graph pairFold`
    (`dup_emerges`) and projecting the second component gives `graph (fun xs => (pairFold xs).2) =
    graph hasDup = graph solveFn = solve` (`(pairFold xs).2 = hasDup xs = solveFn xs` definitionally). -/
theorem derivedSolve_eq_solve : derivedSolve = LC217.solve := by
  unfold derivedSolve
  rw [← dup_emerges]
  apply hom_ext; intro xs b
  constructor
  · rintro ⟨v, hv, hb⟩
    show b = LC217.solveFn xs
    rw [hb, hv]; rfl
  · intro hb
    exact ⟨pairFold xs, rfl, hb⟩

/-! ## Correctness of the derived program, transported from `L217.solve_correct` -/

/-- **The Contains-Duplicate program is the pair-carrying catamorphism, and it is correct.**  The
    honest headline bundles:

    * `dup_emerges` — `graph pairFold = cataR (pairAlg g step)`: the seen-set-carrying program IS the
      catamorphism over the carrier `(ℤ → Bool) × Bool`; and
    * the transported correctness — for ANY state `v` the emergent fold relates the array `xs` to, its
      answer flag `v.2` decides the duplicate question, `v.2 = true ↔ dupP xs`.  Emergence pins
      `v = pairFold xs`, and `L217.solve_correct` (the existing decision `Iff`, NOT re-proved here)
      supplies the answer (`(pairFold xs).2 = hasDup xs = solveFn xs`). -/
theorem dup_derived_correct :
    ((graph pairFold : Arr ⟶ (⟨(Int → Bool) × Bool⟩ : RelSet.{0})) = cataR (pairAlg g step)) ∧
    (∀ (xs : SnocList Int Int) (v : (Int → Bool) × Bool),
        cataFold (pairAlg g step) xs v → (v.2 = true ↔ dupP xs)) := by
  refine ⟨dup_emerges, ?_⟩
  intro xs v hv
  have hgr : (graph pairFold : Arr ⟶ (⟨(Int → Bool) × Bool⟩ : RelSet.{0})) xs v := by
    rw [dup_emerges]; exact hv
  have hveq : v = pairFold xs := hgr
  subst hveq
  exact LC217.solve_correct xs

/-! ## Running / cross-checking the emergent fold against `Fredy/L217.lean`

  The relational catamorphism `cataFold (pairAlg …)` has a FUNCTION-valued first component, so
  equality on the pair carrier is not decidable — we never `decide` the state.  Instead we `decide`
  the answer flag `(pairFold xs).2` (= `hasDup xs`, a `Bool`) on concrete arrays, and separately
  PROVE the pair-fold relates an array to its state. -/

-- The derived answer flag matches `L217`'s stated results (only the final `Bool` is `decide`d).
example : (pairFold (ofList 1 [2, 3, 1])).2 = true := by decide
example : (pairFold (ofList 1 [2, 3, 4])).2 = false := by decide
example : (pairFold (ofList 1 [1])).2 = true := by decide

/-- The emergent pair-fold genuinely relates `ofList 1 [2,3,1]` to its state `pairFold (ofList 1
    [2,3,1])` (whose `.2` is the duplicate flag `true`), proved via `dup_emerges` — no `decide` on
    the function-carrying state. -/
example : cataFold (pairAlg g step) (ofList 1 [2, 3, 1]) (pairFold (ofList 1 [2, 3, 1])) := by
  have h : (graph pairFold : Arr ⟶ (⟨(Int → Bool) × Bool⟩ : RelSet.{0}))
      (ofList 1 [2, 3, 1]) (pairFold (ofList 1 [2, 3, 1])) := rfl
  rw [dup_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC217D
