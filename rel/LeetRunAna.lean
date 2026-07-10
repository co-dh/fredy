/-
  LeetRunAna — the ANAMORPHISM (unfold) LeetCode problems RUN in the relation-algebra
  interpreter: L9 L118 L231 L271 L297 L367.

  The catamorphism passes (`rel/LeetRun1`–`8`, `rel/LeetRunTree`) skipped every problem whose
  program PRODUCES structure from a seed instead of folding it away — each skip note reads "a
  fuel-guarded UNFOLD (anamorphism); the term language has `cata`/`cataT` only".  This file adds
  the missing unfold evaluators: fuel-bounded (structural recursion on a `Nat` fuel, so
  kernel-reducible and `decide`-runnable — no `WellFounded`), one per (functor × effect) the six
  problems actually need:

  * `anaSL` — the SL-functor unfold (coalgebra `S → A ⊕ (S × A)`: a leaf, or emit one element
    and a new seed), producing the interpreter's own nonempty snoc-list `ProgEval.SL`.  This is
    the missing unfold half of `ProgEval.hyloF`, and `hyloF_eq_ana_fold` PROVES it: a hylo IS
    the unfold followed by `foldSL` — so the scalar problems below (L9/L231/L367), wired
    through the existing `hyloF`, are officially unfold-then-fold.
  * `anaL` — the list-functor unfold (coalgebra `S → Option (E × S)`, i.e. `1 ⊕ (E × S)`:
    seed → nil, or emit one element + new seed), producing a possibly-empty `List` (L118).
  * `anaP` — `anaL` in the Kleisli category of `Option`: a PARSER's list unfold, whose
    coalgebra may also REJECT a malformed seed (L271's length-prefix decoder).
  * `anaT` — the tree-functor parser unfold, producing `ProgEval.TB` plus the LEFTOVER seed.
    The tree functor has TWO recursive positions and a token stream determines the right
    child's seed only AFTER the left child is parsed, so the unfold threads the seed as state
    and the coalgebra collapses to "pop one token" — exactly why L297's `deserialize` fit no
    plain-coalgebra scheme before.

  Wired (6/6), each coalgebra read VERBATIM off the L-file's own generator:
  * L9   palindrome number — `digitCoalg` = `LC9.toDigitsFuel`'s branch (leaf = the last,
    most-significant digit); the hylo folds the digit stream to (forward, reversed) and compares.
  * L231 power of two — `halveCoalg` = `LC231.pow2Fuel`'s four branches (halve while even;
    leaf = the first non-halvable value); the fold checks the leaf is `1`.
  * L367 valid perfect square — `sqCoalg` = `LC367.sqFuel`'s upward search (emit `k` while
    `k*k < n`, leaf at the first `k*k ≥ n`); the fold checks the stopping `k` squares to `n`.
  * L118 Pascal's triangle — `rowCoalg` = `LC118.buildRows`'s two clauses (step = the L-file's
    own `nextRow`); `anaL_buildRows` proves the unfold IS `buildRows` — at seed `([1], n)`,
    exactly `pascalFn n` — for EVERY `numRows`, not just the demos.
  * L271 decode — `decodeCoalg` = `LC271.decodeFuel`'s block pop (length-prefixed take/drop,
    reject when the claimed length overruns); `decode_is_ana` proves the parser unfold IS
    `decodeFn` on ALL inputs (malformed included), `ana_decode_encode` the round-trip through
    the L-file's own `encode`.
  * L297 deserialize — `tokCoalg` = the single-token pop (`none` token = nil marker, `some a` =
    node label, as in the L-file's grammar); `deser_is_ana` proves the tree unfold IS
    `parseFuel` on ALL inputs (up to the `Tree ↔ TB` carrier bridge `RunTree.ofTree`), and
    `ana_deserialize_serialize` the round-trip through the L-file's own `serialize`.

  As with `hyloF` ("a standalone function, not a `Prog` former", `rel/LeetRun7`), the unfolds
  are standalone evaluators rather than new `Prog` constructors: fuel puts `Option` in the
  OUTPUT type, which would infect every downstream `Prog.comp`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound} (the `decide` demos and the faithfulness
  theorems are axiom-free).
-/
import rel.RelInterp
import rel.LeetRunTree
import leet.L9
import leet.L104
import leet.L118
import leet.L231
import leet.L271
import leet.L297
import leet.L367

set_option linter.unusedVariables false

namespace Freyd.Alg.FinRel.Ana

open Freyd.Alg.FinRel.ProgEval
-- `Freyd.Alg.RelSet.SL`/`.TB` are infra NAMESPACES; the interpreter carriers `SL`/`TB` are
-- TYPES (`ProgEval.SL`/`ProgEval.TB`) — same surface names, no clash (only one is a constant),
-- cf. `LeetRun1`/`LeetRunTree`.
open Freyd.Alg.RelSet Freyd.Alg.RelSet.TB

/-! ## The unfold evaluators

  The fuel-bounded unfolds `anaSL` / `anaL` / `anaP` / `anaT` and the factorization law
  `hyloF_eq_ana_fold` (a hylo is the unfold then `foldSL`) now all live in the ONE unified
  `ProgEval` (`rel/RelInterp`), co-located with `hyloF`; this file uses them via `open ProgEval`
  and reads the coalgebras off the L-files' own generators.  Each is total by structural
  recursion on the fuel (`none` = fuel exhausted or a rejected parser seed); like `hyloF` they
  stay STANDALONE functions rather than `Prog` formers, since fuel puts `Option` in the OUTPUT
  type, which would infect every downstream `Prog.comp`. -/

/-- Read an interpreter snoc-list back as a `List`, left to right — the demo-side decoder for
    the unfold traces below. -/
def toL {A : Type} : SL A → List A := foldSL (fun a => [a]) (fun l a => l ++ [a])

/-! ## L9 — palindrome number: unfold the digits, fold the two readings

  `LC9.toDigitsFuel` peels `n % 10` while `n ≥ 10` and ends with the remaining digit — the
  SL-functor coalgebra verbatim (the leaf CARRIES the last digit, which is why the possibly-empty
  `anaL` shape would misfit).  The hylo folds the digit stream into (forward reading, reversed
  reading) and the final step compares them — self-reversal is order-insensitive, so the SL's
  most-significant-first order decides the same fact as the L-file's least-significant-first
  `toDigits` (its header makes the same remark). -/

/-- LC 9's digit generator as a coalgebra — `LC9.toDigitsFuel`'s branch verbatim:
    `n < 10` is the leaf (last digit), otherwise emit `n % 10` and continue from `n / 10`. -/
def digitCoalg (n : Nat) : Nat ⊕ (Nat × Nat) :=
  if n < 10 then .inl n else .inr (n / 10, n % 10)

/-- LC 9 as a HYLO: unfold the digits (`digitCoalg`), fold to (forward, reversed), compare.
    Sign guarded once at the `Int` boundary and fuel `n + 1`, both as in `LC9.isPalinNumFn`. -/
def isPalinAna (n : Int) : Bool :=
  if n < 0 then false
  else match hyloF digitCoalg (fun d => ([d], [d]))
      (fun p d => (p.1 ++ [d], d :: p.2)) (n.toNat + 1) n.toNat with
    | some p => decide (p.1 = p.2)
    | none => false

example : isPalinAna 121 = true := by decide
example : isPalinAna (-121) = false := by decide
example : isPalinAna 10 = false := by decide
-- agreement with the L-file's own program, on its own examples
example : (isPalinAna 121, isPalinAna (-121), isPalinAna 10)
    = (LC9.isPalinNumFn 121, LC9.isPalinNumFn (-121), LC9.isPalinNumFn 10) := by decide
-- the unfold alone: the digit SL reads most-significant-first — `LC9.toDigits` reversed
example : (anaSL digitCoalg 3 10).map toL = some (LC9.toDigits 10).reverse := by decide

/-! ## L231 — power of two: unfold the halving chain, check it bottoms out at 1 -/

/-- LC 231's halving generator as a coalgebra — `LC231.pow2Fuel`'s four branches verbatim:
    `1` and `0` are leaves (accept/reject), an even `m` emits itself and continues from `m / 2`,
    an odd `m > 1` is a (rejecting) leaf. -/
def halveCoalg (m : Nat) : Nat ⊕ (Nat × Nat) :=
  if m = 1 then .inl 1 else if m = 0 then .inl 0
  else if m % 2 = 0 then .inr (m / 2, m) else .inl m

/-- LC 231 as a HYLO: unfold the halving chain (`halveCoalg`), fold = "is the leaf `1`?"
    (the emitted trace is carried past unchanged).  Sign guard and fuel `n.toNat` as in
    `LC231.isPow2Fn`; halving reaches a leaf within `m` steps, so the fuel never runs out. -/
def isPow2Ana (n : Int) : Bool :=
  if n ≤ 0 then false
  else (hyloF halveCoalg (fun m => decide (m = 1)) (fun c _ => c) n.toNat n.toNat).getD false

example : isPow2Ana 1 = true := by decide
example : isPow2Ana 16 = true := by decide
example : isPow2Ana 6 = false := by decide
-- agreement with the L-file's own program, on its own examples
example : (isPow2Ana 1, isPow2Ana 16, isPow2Ana 6)
    = (LC231.isPow2Fn 1, LC231.isPow2Fn 16, LC231.isPow2Fn 6) := by decide
-- the unfold alone: the halving chain of 16, leaf first
example : (anaSL halveCoalg 5 16).map toL = some [1, 2, 4, 8, 16] := by decide

/-! ## L367 — valid perfect square: unfold the upward search, test the stopping point -/

/-- LC 367's search generator as a coalgebra — `LC367.sqFuel`'s branches: both stopping cases
    (`k*k = n` accept, `k*k > n` reject) are the leaf at the first `k` with `n ≤ k*k`; below it,
    emit `k` and continue upward from `k + 1`. -/
def sqCoalg (n : Nat) (k : Nat) : Nat ⊕ (Nat × Nat) :=
  if n ≤ k * k then .inl k else .inr (k + 1, k)

/-- LC 367 as a HYLO: unfold the search trace from `k = 0` (`sqCoalg`), fold = "does the
    stopping `k` square to `n`?".  Search from `0` and fuel `n + 1` as in
    `LC367.isPerfectSquareFn`; the leaf comes at some `k ≤ n`, so the fuel never runs out. -/
def isSquareAna (n : Nat) : Bool :=
  (hyloF (sqCoalg n) (fun k => decide (k * k = n)) (fun c _ => c) (n + 1) 0).getD false

example : isSquareAna 16 = true := by decide
example : isSquareAna 14 = false := by decide
example : isSquareAna 1 = true := by decide
-- agreement with the L-file's own program, on its own examples
example : (isSquareAna 16, isSquareAna 14, isSquareAna 1)
    = (LC367.isPerfectSquareFn 16, LC367.isPerfectSquareFn 14, LC367.isPerfectSquareFn 1) := by
  decide
-- the unfold alone: the search trace for 14 stops at 4 (16 ≥ 14), leaf first
example : (anaSL (sqCoalg 14) 5 0).map toL = some [4, 3, 2, 1, 0] := by decide

/-! ## L118 — Pascal's triangle: unfold `numRows` rows, each from the previous

  `LC118.buildRows` is a pure list anamorphism: seed = (current row, rows still to produce),
  emit the row, step with the L-file's own `nextRow`, stop at count `0`.  Faithfulness is a
  THEOREM over every seed, not just the demos. -/

/-- LC 118's row generator as a coalgebra — `LC118.buildRows`'s two clauses verbatim:
    count `0` stops; otherwise emit the current row and continue with `LC118.nextRow`. -/
def rowCoalg : List Nat × Nat → Option (List Nat × (List Nat × Nat))
  | (_, 0) => none
  | (r, n + 1) => some (r, (LC118.nextRow r, n))

/-- **The row unfold IS `LC118.buildRows`** — with fuel `n + 1` (`n` emissions + the stop), the
    anamorphism from seed `(r, n)` produces exactly `buildRows n r`; at `r = [1]` that is
    `LC118.pascalFn n` (definitionally), for EVERY `numRows`. -/
theorem anaL_buildRows : ∀ (n : Nat) (r : List Nat),
    anaL rowCoalg (n + 1) (r, n) = some (LC118.buildRows n r)
  | 0, r => rfl
  | n + 1, r => by
    show (anaL rowCoalg (n + 1) (LC118.nextRow r, n)).map (r :: ·)
        = some (LC118.buildRows (n + 1) r)
    rw [anaL_buildRows n (LC118.nextRow r)]
    rfl

example : anaL rowCoalg 6 ([1], 5) = some (LC118.pascalFn 5) := by decide
example : anaL rowCoalg 6 ([1], 5)
    = some [[1], [1, 1], [1, 2, 1], [1, 3, 3, 1], [1, 4, 6, 4, 1]] := by decide
example : anaL rowCoalg 2 ([1], 1) = some [[1]] := by decide

/-! ## L271 — decode: the unfold half (the fold half, `encode`, runs in `rel/LeetRun6`)

  `LC271.decodeFuel` peels one length-prefixed block per step — a list anamorphism whose
  coalgebra can REJECT (claimed length overrunning the remaining tokens), hence `anaP`.
  Faithfulness (`decode_is_ana`) covers ALL inputs, malformed included; the round-trip
  (`ana_decode_encode`) goes through the L-file's own `encode`. -/

/-- LC 271's block pop as a coalgebra — `LC271.decodeFuel`'s branches verbatim: end of input
    stops, a length prefix `n` within bounds emits `take n.toNat` and continues on
    `drop n.toNat`, an overrunning length rejects. -/
def decodeCoalg : List Int → Option (Option (List Int × List Int))
  | [] => some none
  | n :: rest =>
    if n.toNat ≤ rest.length then some (some (rest.take n.toNat, rest.drop n.toNat)) else none

/-- **The parser unfold IS `LC271.decodeFuel`** — same answer on EVERY token list (malformed
    ones included), with one extra fuel unit (`anaP` also spends fuel on the final stop, which
    `decodeFuel`'s `[] ↦ some []` clause answers even at fuel `0`). -/
theorem decode_is_ana : ∀ (fuel : Nat) (ts : List Int),
    anaP decodeCoalg (fuel + 1) ts = LC271.decodeFuel fuel ts
  | 0, [] => rfl
  | 0, n :: rest => by
    simp only [anaP, decodeCoalg]
    by_cases h : n.toNat ≤ rest.length
    · rw [if_pos h]; rfl
    · rw [if_neg h]; rfl
  | fuel + 1, [] => rfl
  | fuel + 1, n :: rest => by
    rw [anaP]
    simp only [decode_is_ana fuel]
    simp only [decodeCoalg, LC271.decodeFuel]
    by_cases h : n.toNat ≤ rest.length
    · simp only [if_pos h]
      cases LC271.decodeFuel fuel (rest.drop n.toNat) with
      | none => rfl
      | some strs => rfl
    · rw [if_neg h, if_neg h]

/-- **Round-trip through the L-file's own encoder**: the parser unfold decodes `encode strs`
    back to `strs`, for EVERY list of strings — `decode_is_ana` chained to `LC271.round_trip`
    (the fuel `length + 2` is `decodeFn`'s own `length + 1`, shifted by `decode_is_ana`'s one
    extra stop unit). -/
theorem ana_decode_encode (strs : List (List Int)) :
    anaP decodeCoalg ((LC271.encode strs).length + 2) (LC271.encode strs) = some strs := by
  rw [decode_is_ana ((LC271.encode strs).length + 1) (LC271.encode strs)]
  exact LC271.round_trip strs

-- the L-file's own example (`[[104,105], []]`, an empty string exercising `n = 0`)
example : LC271.encode [[104, 105], []] = [2, 104, 105, 0] := by decide
example : anaP decodeCoalg 6 [2, 104, 105, 0] = some [[104, 105], []] := by decide
example : anaP decodeCoalg 6 [2, 104, 105, 0] = LC271.decodeFn [2, 104, 105, 0] := by decide
-- a malformed input (claimed length 5, nothing follows) is REJECTED, agreeing with the L-file
example : anaP decodeCoalg 2 [5] = none ∧ LC271.decodeFn [5] = none := by decide

/-! ## L297 — deserialize: the unfold half (the fold half, `serialize`, runs in
  `rel/LeetRunTree`)

  The preorder parse is a TREE anamorphism with the token stream threaded as state: the
  coalgebra is the bare single-token pop, and the L-file's grammar (a `none` token = nil
  marker, `some a` = a node's label) is the `Option Int` the pop hands `anaT`.  Faithfulness
  (`deser_is_ana`) covers ALL inputs up to the `Tree ↔ TB` carrier bridge `RunTree.ofTree`;
  the round-trip (`ana_deserialize_serialize`) goes through the L-file's own `serialize`. -/

/-- LC 297's token pop as a coalgebra: end of input rejects (a well-formed parse never runs
    out mid-tree), otherwise hand the head token — `none` (nil marker) or `some a` (node
    label), the L-file's `Tok` — to the tree unfold, with the rest as the new state. -/
def tokCoalg : List LC297.Tok → Option (Option Int × List LC297.Tok)
  | [] => none
  | t :: rest => some (t, rest)

/-- **The tree unfold IS `LC297.parseFuel`** — same answer on EVERY token list and fuel, up to
    transporting the parsed tree along the `Tree ↔ TB` carrier bridge `RunTree.ofTree` (the
    leftover tokens agree on the nose). -/
theorem deser_is_ana : ∀ (fuel : Nat) (ts : List LC297.Tok),
    anaT tokCoalg fuel ts
      = (LC297.parseFuel fuel ts).map (fun p => (RunTree.ofTree p.1, p.2))
  | 0, _ => rfl
  | fuel + 1, [] => rfl
  | fuel + 1, none :: rest => rfl
  | fuel + 1, some a :: rest => by
    rw [anaT, LC297.parseFuel]
    simp only [deser_is_ana fuel]
    simp only [tokCoalg]
    cases LC297.parseFuel fuel rest with
    | none => rfl
    | some p =>
      obtain ⟨l, rest1⟩ := p
      simp only [Option.map]
      cases LC297.parseFuel fuel rest1 with
      | none => rfl
      | some q =>
        obtain ⟨r, rest2⟩ := q
        rfl

/-- **Round-trip through the L-file's own serializer**: the tree unfold parses `serialize t`
    back to `t` (as a `TB`, leftover `[]`), for EVERY tree — `deser_is_ana` chained to the
    L-file's generalized round-trip `LC297.parseFuel_serialize`. -/
theorem ana_deserialize_serialize (t : Tree Int) :
    anaT tokCoalg (LC297.serialize t).length (LC297.serialize t)
      = some (RunTree.ofTree t, []) := by
  have h := LC297.parseFuel_serialize t [] (LC297.serialize t).length (Nat.le_refl _)
  rw [List.append_nil] at h
  rw [deser_is_ana, h]
  rfl

-- the L-file's own examples, run: a balanced height-2 tree and the empty tree
example : anaT tokCoalg 7 (LC297.serialize (LC297.bal 1 2 3))
    = some (RunTree.ofTree (LC297.bal 1 2 3), []) := by decide
example : (anaT tokCoalg 1 (LC297.serialize (Tree.nil : Tree Int))).map Prod.fst
    = some TB.nil := by decide
example : anaT tokCoalg 5 (LC297.serialize (Tree.node (LC297.leaf 1) 2 Tree.nil))
    = some (RunTree.ofTree (Tree.node (LC297.leaf 1) 2 Tree.nil), []) := by decide
-- a TREE HYLO: unfold the token stream to a `TB`, then `foldTB` LC 104's depth algebra — the
-- deserialize-then-maxDepth pipeline, both halves running in the interpreter
example : (anaT tokCoalg 7 (LC297.serialize (LC297.bal 1 2 3))).map
      (fun p => foldTB 0 (fun dl _ dr => 1 + LC104.imax dl dr) p.1) = some 2 := by decide

end Freyd.Alg.FinRel.Ana
