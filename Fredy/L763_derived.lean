/-
  LeetCode 763 — Partition Labels — DERIVED as a `SnocList` catamorphism, with the last-occurrence
  table precomputed into a HASH MAP for `O(1)`-expected lookup (upgrading `Fredy/L763.lean`'s two
  `O(n²)` `lastPos` list scans to an `O(n)`-expected two-pass sweep).

  `Fredy/L763.lean` writes the greedy pass-2 scan `scanFn whole` by hand: a left-to-right fold over
  `xs` that at each step consults `lastPos whole c` — an `O(n)` list scan of the whole string per
  character, so pass 2 is `O(n²)`.  Here:

    * **Pass 1** precomputes the table once into a `Freyd.HashMap.AHashMap Nat` (`buildLP`): insert
      `(char, position)` left-to-right, so the newest (rightmost) write wins and `find?` returns each
      character's LAST occurrence — exactly `lastPos whole`, but `O(1)` expected per lookup
      (`lookupLP_buildLPGo`, one induction via `find?_insert_self`/`_other`/`find?_mkHashMap`).

    * **Pass 2**, the greedy sweep, EMERGES via `SL.snocFold_unique` (`Fredy/A6_GenFold.lean`) as the
      catamorphism `cataR (scalarAlg (g lp) (st lp))` of the scalar algebra whose base `g lp` and step
      `st lp` are read straight off the scan.  The carrier is the 4-tuple
      `C := (idx, reach, curSize, parts)` (`Nat × Nat × Nat × List Nat`): the running max
      last-occurrence `reach`, the current open-piece size `curSize`, the emitted sizes `parts` (built
      by CONS, never `acc ++ [x]`) — PLUS the absolute index `idx`, which the carrier must thread
      because the scan closes a piece exactly when `idx = reach` (an ABSOLUTE comparison; from
      `(reach, curSize, parts)` alone the position is not recoverable in `O(1)`).  `scanH lp` is
      defined directly from `g lp`/`st lp`, so its two defining equations hold by `rfl` and
      `snocFold_unique` PRODUCES the fold (`scan_emerges`) — the sweep is not written, it emerges.

  CORRECTNESS is SOUNDNESS-ONLY, REUSED (not re-proved): `L763.solve_valid` already proves every
  output of the hand-written `solveFn` is a valid partition (self-contained pieces covering the
  string).  The bridge `scanH_eq` shows `scanH (buildLP whole) = (topIdx ·, scanFn whole ·)` whenever
  the table models `lastPos whole`, so the derived program equals `L763.solve` (`derivedSolve_eq_solve`)
  and inherits `solve_valid` (`derivedSolve_valid`).  MAXIMALITY / optimality (the finest partition) is
  NOT claimed — `L763.lean` does not prove it either (see its bottom note); this file makes no
  optimality claim and fabricates no maximality proof.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  Routed only through `snocFold_unique`
  (never `cataR_eq_relCata`); the hash lemmas use `beq_iff_eq` / `of_decide_eq_*`, never
  `beq_self_eq_true`.
-/
import Fredy.A6_GenFold
import Fredy.A6_HashMap
import Fredy.L763

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC763D

open Freyd Freyd.Alg.RelSet.SL
open Freyd.HashMap (AHashMap mkHashMap find? find?_insert_self find?_insert_other find?_mkHashMap)

/-! ## The carrier and the last-occurrence lookup -/

/-- The fold carrier: `(idx, reach, curSize, parts)`.  `idx` is the absolute index of the
    last-processed character (needed for the `idx = reach` close test), `reach` the running max
    last-occurrence over the current open piece, `curSize` that piece's size, `parts` the closed
    sizes (in reverse/closing order). -/
abbrev C : Type := Nat × Nat × Nat × List Nat

/-- Read the precomputed table: `lastPos`-equivalent, but `O(1)` expected.  A character absent from
    the table (`none`) defaults to `0` — matching `L763.lastPos`, which returns `0` for absent
    characters and for `wrap`'s single position. -/
def lookupLP (lp : AHashMap Nat) (c : Int) : Nat := (find? lp c).getD 0

/-! ## The base `g` and step `st`, READ OFF `L763.scanFn` (with `lastPos whole` replaced by `lookupLP lp`)

  `wrap x`  ↦ `if r = 0 then (0, r, 0, [1]) else (0, r, 1, [])`, `r := lookupLP lp x`  (index `0`).
  `snoc _ p ↦` from `(i, r, sz, rp)`: `i' := i+1`, `r' := nmax r (lookupLP lp p)`; close (`i' = r'`)
  ⟹ `(i', r', 0, (sz+1)::rp)`, else `(i', r', sz+1, rp)`. -/

/-- The base of the emergent algebra — forced by `scanFn whole (wrap x)` with `idx = 0`. -/
def g (lp : AHashMap Nat) : Int → C := fun x =>
  let r := lookupLP lp x
  if r = 0 then (0, r, 0, [1]) else (0, r, 1, [])

/-- The step of the emergent algebra — forced by `scanFn whole (snoc xs p)`; `i' = idx+1` is the new
    absolute position, `r'` the updated reach.  A piece closes exactly when `i' = r'`. -/
def st (lp : AHashMap Nat) : C → Int → C := fun s p =>
  let i := s.1; let r := s.2.1; let sz := s.2.2.1; let rp := s.2.2.2
  let i' := i + 1
  let r' := LC763.nmax r (lookupLP lp p)
  if i' = r' then (i', r', 0, (sz + 1) :: rp) else (i', r', sz + 1, rp)

/-- The pass-2 sweep, defined DIRECTLY from `g`/`st` so `snocFold_unique` applies by `rfl`. -/
def scanH (lp : AHashMap Nat) : SnocList Int Int → C
  | .wrap x => g lp x
  | .snoc xs p => st lp (scanH lp xs) p

/-! ## The sweep EMERGES via the general-carrier snoc-fold law -/

/-- **The greedy sweep is PRODUCED by `snocFold_unique`.**  For any precomputed table `lp`,
    `graph (scanH lp)` equals the catamorphism of the scalar algebra `scalarAlg (g lp) (st lp)` on
    the 4-tuple carrier `C`.  The two defining equations of `scanH lp` are `rfl` (it is literally
    built from `g lp`/`st lp`), so the sweep is not written — it emerges. -/
theorem scan_emerges (lp : AHashMap Nat) :
    (graph (scanH lp) : LC763.Arr ⟶ (⟨C⟩ : RelSet.{0})) = cataR (scalarAlg (g lp) (st lp)) :=
  snocFold_unique (g lp) (st lp) (scanH lp) (fun _ => rfl) (fun _ _ => rfl)

/-! ## Pass 1: precompute the last-occurrence table into a hash map -/

/-- Build the table with a FIXED bucket count `size`: insert `(char, position)` for every character
    left-to-right, so the rightmost (last) occurrence wins under `find?`. -/
def buildLPGo (size : Nat) : SnocList Int Int → AHashMap Nat
  | .wrap x => Freyd.HashMap.insert (mkHashMap Nat size) x 0
  | .snoc xs p => Freyd.HashMap.insert (buildLPGo size xs) p (LC763.topIdx xs + 1)

/-- The table for the whole string, sized to its length (`topIdx whole + 1` buckets). -/
def buildLP (whole : SnocList Int Int) : AHashMap Nat := buildLPGo (LC763.topIdx whole) whole

/-- **The hash table `find?`-MODELS `L763.lastPos` exactly.**  One induction: at `wrap` the single
    insert makes `find? = some 0` for the char and `none` (⟹ default `0`) for anything else — both
    `lastPos (wrap x) · = 0`; at `snoc xs p` the top insert wins for `p` (`= topIdx xs + 1`) and
    passes through (`find?_insert_other`) to the tail table for `c ≠ p` (`= lastPos xs c` by IH),
    matching `lastPos (snoc xs p)`'s `if p = c` split. -/
theorem lookupLP_buildLPGo (size : Nat) :
    ∀ (xs : SnocList Int Int) (c : Int), lookupLP (buildLPGo size xs) c = LC763.lastPos xs c := by
  intro xs
  induction xs with
  | wrap x =>
    intro c
    show (find? (Freyd.HashMap.insert (mkHashMap Nat size) x 0) c).getD 0 = (0 : Nat)
    cases hd : decide (c = x) with
    | true =>
      have hcx : c = x := of_decide_eq_true hd
      rw [hcx, find?_insert_self, Option.getD_some]
    | false =>
      have hne : c ≠ x := of_decide_eq_false hd
      rw [find?_insert_other _ _ _ _ hne, find?_mkHashMap, Option.getD_none]
  | snoc xs p ih =>
    intro c
    show (find? (Freyd.HashMap.insert (buildLPGo size xs) p (LC763.topIdx xs + 1)) c).getD 0
        = (if p = c then LC763.topIdx xs + 1 else LC763.lastPos xs c)
    cases hd : decide (c = p) with
    | true =>
      have hcp : c = p := of_decide_eq_true hd
      rw [hcp, find?_insert_self, Option.getD_some, if_pos rfl]
    | false =>
      have hne : c ≠ p := of_decide_eq_false hd
      rw [find?_insert_other _ _ _ _ hne, if_neg (fun h : p = c => hne h.symm)]
      exact ih c

/-! ## Bridge: the hash sweep equals `L763.scanFn` (paired with the index) whenever the table models `lastPos` -/

/-- **`scanH lp = (topIdx ·, scanFn whole ·)`** whenever `lp` models `lastPos whole`.  The carrier's
    first component is the absolute index `topIdx xs`; the other three are exactly `L763.scanFn`'s
    triple — so pass 2 computes the same partition as the hand-written scan. -/
theorem scanH_eq {lp : AHashMap Nat} {whole : SnocList Int Int}
    (hlp : ∀ c, lookupLP lp c = LC763.lastPos whole c) :
    ∀ xs, scanH lp xs = (LC763.topIdx xs, LC763.scanFn whole xs) := by
  intro xs
  induction xs with
  | wrap x =>
    show g lp x = (LC763.topIdx (.wrap x), LC763.scanFn whole (.wrap x))
    show (if lookupLP lp x = 0 then ((0 : Nat), lookupLP lp x, (0 : Nat), [1])
            else (0, lookupLP lp x, 1, []))
        = (0, if LC763.lastPos whole x = 0 then (LC763.lastPos whole x, 0, [1])
              else (LC763.lastPos whole x, 1, []))
    rw [hlp x]
    cases hz : decide (LC763.lastPos whole x = 0) with
    | true => rw [if_pos (of_decide_eq_true hz), if_pos (of_decide_eq_true hz)]
    | false => rw [if_neg (of_decide_eq_false hz), if_neg (of_decide_eq_false hz)]
  | snoc xs p ih =>
    show st lp (scanH lp xs) p = (LC763.topIdx (.snoc xs p), LC763.scanFn whole (.snoc xs p))
    rw [ih, LC763.scanFn_snoc]
    rcases hh : LC763.scanFn whole xs with ⟨r, sz, rp⟩
    show (if LC763.topIdx xs + 1 = LC763.nmax r (lookupLP lp p)
          then (LC763.topIdx xs + 1, LC763.nmax r (lookupLP lp p), 0, (sz + 1) :: rp)
          else (LC763.topIdx xs + 1, LC763.nmax r (lookupLP lp p), sz + 1, rp))
        = (LC763.topIdx xs + 1,
           if LC763.topIdx xs + 1 = LC763.nmax r (LC763.lastPos whole p)
           then (LC763.nmax r (LC763.lastPos whole p), 0, (sz + 1) :: rp)
           else (LC763.nmax r (LC763.lastPos whole p), sz + 1, rp))
    rw [hlp p]
    cases hc : decide (LC763.topIdx xs + 1 = LC763.nmax r (LC763.lastPos whole p)) with
    | true => rw [if_pos (of_decide_eq_true hc), if_pos (of_decide_eq_true hc)]
    | false => rw [if_neg (of_decide_eq_false hc), if_neg (of_decide_eq_false hc)]

/-! ## The derived program: two hash-backed passes, equal to `L763.solve` -/

/-- The answer: run pass 1 (`buildLP xs`) then pass 2 (`scanH … xs`) and read off the piece sizes in
    left-to-right order (`parts` is the `.2.2.2` component; reverse the closing order). -/
def derivedSolveFn (xs : SnocList Int Int) : List Nat := (scanH (buildLP xs) xs).2.2.2.reverse

/-- The derived program as a morphism `Arr ⟶ dParts` in `Rel(Set)`. -/
def derivedSolve : LC763.Arr ⟶ LC763.dParts := graph derivedSolveFn

/-- **The two-pass hash program computes exactly `L763.solveFn`.**  `buildLP xs` models `lastPos xs`
    (`lookupLP_buildLPGo` at `size = topIdx xs`), so `scanH_eq` gives `scanH (buildLP xs) xs =
    (topIdx xs, scanFn xs xs)`; its `.2.2.2` is `(scanFn xs xs).2.2`, whose reverse is `solveFn xs`. -/
theorem derivedSolveFn_eq (xs : SnocList Int Int) : derivedSolveFn xs = LC763.solveFn xs := by
  show (scanH (buildLP xs) xs).2.2.2.reverse = (LC763.scanFn xs xs).2.2.reverse
  rw [scanH_eq (whole := xs) (lp := buildLP xs)
        (fun c => lookupLP_buildLPGo (LC763.topIdx xs) xs c) xs]

/-- The derived morphism IS `L763.solve` — same graph, pointwise equal solvers. -/
theorem derivedSolve_eq_solve : derivedSolve = LC763.solve := by
  apply hom_ext; intro xs v
  show (v = derivedSolveFn xs) ↔ (v = LC763.solveFn xs)
  rw [derivedSolveFn_eq]

/-- **SOUNDNESS, REUSED from `L763.solve_valid`** — the derived program's output is always a valid
    partition (consecutive, non-empty, self-contained pieces covering the whole string).  No
    optimality/maximality is claimed (neither does `L763.lean`). -/
theorem derivedSolve_valid (xs : SnocList Int Int) :
    LC763.IsValidPartition (LC763.toList xs) (derivedSolveFn xs) := by
  rw [derivedSolveFn_eq]; exact LC763.solve_valid xs

/-- **LeetCode 763, derived — SOUNDNESS ONLY.**  The honest headline bundles:

    * `scan_emerges` — for any precomputed table `lp`, the greedy pass-2 sweep `graph (scanH lp)` is
      PRODUCED by `SL.snocFold_unique` as the catamorphism `cataR (scalarAlg (g lp) (st lp))` on the
      4-tuple carrier; the load-bearing new content — the sweep is not written, it emerges;
    * `derivedSolve = L763.solve` — the two hash-backed passes equal the hand-written solver; and
    * SOUNDNESS, reused from `L763.solve_valid` (NOT re-proved): every output is a valid partition.

    MAXIMALITY (the FINEST partition) is deliberately NOT claimed — `L763.lean` does not prove it, so
    this derivation stays honestly soundness-only. -/
theorem partition_labels_derived_sound :
    (∀ lp : AHashMap Nat,
      (graph (scanH lp) : LC763.Arr ⟶ (⟨C⟩ : RelSet.{0})) = cataR (scalarAlg (g lp) (st lp)))
    ∧ derivedSolve = LC763.solve
    ∧ ∀ xs : SnocList Int Int, LC763.IsValidPartition (LC763.toList xs) (derivedSolveFn xs) :=
  ⟨scan_emerges, derivedSolve_eq_solve, derivedSolve_valid⟩

/-! ## Running / cross-checking the emergent hash program against `Fredy/L763.lean`

  The `Array`-backed hash ops in `buildLP` do not reduce through the kernel's `decide`, so each check
  transports across `derivedSolveFn_eq` onto the kernel-reducible `L763.solveFn` and `decide`s that
  (the SAME `List Nat` value).  `#eval` runs the real `O(n)`-expected hash program via the compiler. -/

-- "ababcbacadefegdehijhklij" (the classic LeetCode example)
example :
    derivedSolveFn (LC763.ofList 97 [98, 97, 98, 99, 98, 97, 99, 97, 100, 101, 102, 101, 103, 100,
      101, 104, 105, 106, 104, 107, 108, 105, 106]) = [9, 7, 8] := by
  rw [derivedSolveFn_eq]; decide
example : derivedSolveFn (LC763.ofList 101 [105, 106, 101]) = [4] := by rw [derivedSolveFn_eq]; decide
example : derivedSolveFn (LC763.ofList 101 []) = [1] := by rw [derivedSolveFn_eq]; decide

-- `#eval` runs the actual O(n)-expected two-pass hash program:
#eval derivedSolveFn (LC763.ofList 97 [98, 97, 98, 99, 98, 97, 99, 97, 100, 101, 102, 101, 103, 100,
  101, 104, 105, 106, 104, 107, 108, 105, 106])   -- [9, 7, 8]
#eval derivedSolveFn (LC763.ofList 101 [105, 106, 101])   -- [4]

end Freyd.Alg.RelSet.LC763D
