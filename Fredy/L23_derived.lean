/-
  LeetCode 23 — Merge k Sorted Lists — DERIVED as a cons-list catamorphism.

  `Fredy/L23.lean` merges `k` sorted lists by RIGHT-FOLDING `L21`'s binary merge over the outer list
  of lists, base `[]`:

    * `mergeKFn []          = []`
    * `mergeKFn (l :: rest) = LC21.mergeFn l (mergeKFn rest)`     (`= lists.foldr LC21.mergeFn []`)

  This is already a plain front-to-back fold over the OUTER `List (List Int)`, so — unlike the
  lookahead/singleton repairs of `L13`/`L14` — no clever carrier is needed.  The carrier is simply the
  answer type itself,

    * `C := List Int`     -- the merged-so-far list

  the base is `[]`, and the step is `L21`'s binary merge `LC21.mergeFn : List Int → List Int → List Int`
  (head list merged into the accumulated merge of the tail).  There is no `proj`: the fold's carrier IS
  the output.

    * `g _        = []`                      = `foldCL (wrap _)`
    * `st l c     = LC21.mergeFn l c`        = `foldCL (cons l xs)` with `c = foldCL xs`.

  RESHAPING the outer list onto the repo's canonical cons-list initial algebra `ConsList Unit (List Int)`
  (`list (List Int)` of the book, base at `wrap ()`, recursion on the tail) and feeding `g`/`st`/`foldCL`
  to the general-carrier fold-uniqueness law `Freyd.Alg.RelSet.CL.consFold_unique`
  (`Fredy/A6_GenFold.lean`) PRODUCES the k-way merge as `cataR (consScalarAlg g st)` — the fold is never
  written by hand (`merge_emerges`).  The bridge `foldCL_ofList` recovers `L23.mergeKFn` on converted
  input, so the whole L23 program factors through the emergent catamorphism:
  `derivedSolve = graph ofList ≫ cataR (…)` equals `L23.solve` (`derivedSolve_eq_solve`).

  Only the PROGRAM is derived.  Correctness — sortedness of the output AND its exact SUMMED multiplicity
  across every input list — is REUSED verbatim from `L23.merge_k_correct`, not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_GenFold
import Fredy.L23

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC23D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The `List Int` carrier and its cons-list fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here the carrier is the
  answer type itself, `C = List Int` — the merged-so-far list.  No tag, no lookahead: the k-way merge
  is an ordinary right-fold over the outer list, so the fold's carrier and output coincide. -/

/-- Base of the emergent algebra: the empty outer list merges to `[]`. -/
def g : Unit → List Int := fun _ => []

/-- Step of the emergent algebra: merge the head list `l` into the accumulated merge `c` of the tail,
    via `L21`'s binary merge. -/
def st : List Int → List Int → List Int := LC21.mergeFn

/-- The k-way merge as a fold over the cons-list initial algebra `ConsList Unit (List Int)`, mirroring
    `L23.mergeKFn`: `wrap _ ↦ []`, `cons l xs ↦ st l (foldCL xs)`. -/
def foldCL : ConsList Unit (List Int) → List Int
  | ConsList.wrap _    => []
  | ConsList.cons l xs => st l (foldCL xs)

/-! ## The k-way merge EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  The k-way merge, reshaped onto the cons-list initial algebra
    `ConsList Unit (List Int)`, IS the catamorphism of the emergent scalar algebra `consScalarAlg g st`
    — it was never written as a fold: `graph foldCL` equals `cataR (consScalarAlg g st)`.  The base `[]`
    and step `L21.mergeFn` are FORCED (both defining equations are `rfl`); given them, `consFold_unique`
    emits the fold. -/
theorem merge_emerges :
    (graph foldCL : dCL Unit (List Int) ⟶ ⟨List Int⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st foldCL (fun _ => rfl) (fun _ _ => rfl)

/-! ## Bridge to the hand-written raw-`List` program `L23.mergeKFn` -/

/-- The `List (List Int) → ConsList Unit (List Int)` conversion onto the initial algebra:
    `[] ↦ wrap ()`, `l :: rest ↦ cons l (ofList rest)`. -/
def ofList : List (List Int) → ConsList Unit (List Int)
  | []        => ConsList.wrap ()
  | l :: rest => ConsList.cons l (ofList rest)

/-- The reshaped fold agrees with the raw-`List` right-fold on converted input:
    `foldCL (ofList lists) = L23.mergeKFn lists`, by induction on `lists` (the cons step is exactly
    `mergeKFn`'s `foldr` cons equation). -/
theorem foldCL_ofList : ∀ lists : List (List Int), foldCL (ofList lists) = LC23.mergeKFn lists
  | []          => rfl
  | l :: rest   => by
      show st l (foldCL (ofList rest)) = LC23.mergeKFn (l :: rest)
      rw [foldCL_ofList rest]
      rfl

/-! ## The whole L23 program factors through the emergent catamorphism -/

/-- The derived solver: convert the input to the cons-list (`graph ofList`), then run the emergent
    catamorphism (whose carrier is already the answer type, so no answer read-out is needed). -/
def derivedSolve : LC23.dInput ⟶ LC23.dAns :=
  (graph ofList : LC23.dInput ⟶ dCL Unit (List Int)) ≫ cataR (consScalarAlg g st)

/-- **The derived solver IS `L23.solve`.**  Rewriting the emergent catamorphism back to `graph foldCL`
    (via `merge_emerges`) turns `derivedSolve` into the graph of `foldCL ∘ ofList`, which the bridge
    `foldCL_ofList` identifies with `mergeKFn` — so `derivedSolve = graph mergeKFn = L23.solve`.  The
    hand-written L23 program is exactly the law-produced fold, wrapped by the data conversion. -/
theorem derivedSolve_eq_solve : derivedSolve = LC23.solve := by
  show (graph ofList : LC23.dInput ⟶ dCL Unit (List Int)) ≫ cataR (consScalarAlg g st)
      = graph LC23.mergeKFn
  rw [← merge_emerges]
  apply hom_ext; intro lists y
  constructor
  · rintro ⟨cl, rfl, rfl⟩
    exact foldCL_ofList lists
  · intro hy
    exact ⟨ofList lists, rfl, by rw [hy]; exact (foldCL_ofList lists).symm⟩

/-! ## Correctness carries over from `L23.lean` (no re-proof of sortedness / multiplicity) -/

/-- **Headline.**  The honest bundle:

    (1) the k-way merge, reshaped onto the cons-list initial algebra, IS the catamorphism of
        `consScalarAlg g st` — the fold EMERGES from `consFold_unique` (`merge_emerges`);
    (2) the whole L23 program factors through that emergent catamorphism —
        `derivedSolve = graph ofList ≫ cataR (…)` equals `L23.solve` (`derivedSolve_eq_solve`); and
    (3) it is correct — given a list of SORTED inputs, `mergeKFn` returns a SORTED list whose multiset
        is exactly the SUM (with multiplicity) of every input list's multiset — the REUSED
        `L23.merge_k_correct`, whose sortedness and multiplicity are NOT re-proved here.

    The program (the fold) is PRODUCED by the law; the correctness is reused. -/
theorem merge_k_derived_correct :
    ((graph foldCL : dCL Unit (List Int) ⟶ ⟨List Int⟩) = cataR (consScalarAlg g st))
      ∧ (derivedSolve = LC23.solve)
      ∧ (∀ lists : List (List Int), (∀ l ∈ lists, LC21.Sorted l) →
           LC21.Sorted (LC23.mergeKFn lists) ∧
           ∀ v, LC21.count v (LC23.mergeKFn lists) = LC23.totalCount v lists) :=
  ⟨merge_emerges, derivedSolve_eq_solve, LC23.merge_k_correct⟩

/-! ## Running / cross-checking the emergent fold against `Fredy/L23.lean`

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier), so we `decide` the extensionally-equal computable witnesses:
  `L23.mergeKFn` on LeetCode 23's own example, and the derived pipeline `foldCL ∘ ofList` (equal to
  `mergeKFn` by `foldCL_ofList`). -/

/-- `[[1,4,5],[1,3,4],[2,6]] → [1,1,2,3,4,4,5,6]`. -/
example : LC23.mergeKFn [[1, 4, 5], [1, 3, 4], [2, 6]] = [1, 1, 2, 3, 4, 4, 5, 6] := by decide

/-- The derived pipeline `foldCL ∘ ofList` reproduces the L23 answer. -/
example : foldCL (ofList [[1, 4, 5], [1, 3, 4], [2, 6]]) = [1, 1, 2, 3, 4, 4, 5, 6] := by decide

/-- The derived pipeline handles empty / gap inputs: `[[1],[],[-1,3]] → [-1,1,3]`. -/
example : foldCL (ofList [[1], [], [-1, 3]]) = [-1, 1, 3] := by decide

/-- The emergent fold genuinely relates the converted input to `foldCL` of it (whose value is the
    k-way merge). -/
example :
    cataFold (consScalarAlg g st) (ofList [[1, 3], [2]]) (foldCL (ofList [[1, 3], [2]])) := by
  have h : (graph foldCL : dCL Unit (List Int) ⟶ ⟨List Int⟩)
      (ofList [[1, 3], [2]]) (foldCL (ofList [[1, 3], [2]])) := rfl
  rw [merge_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC23D
