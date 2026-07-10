/-
  LeetCodeRunPair — the TWO-INPUT / PAIRING LeetCode problems RUN in the relation-algebra
  interpreter, as single terms over a PAIR of inputs.

  The single-fold passes skipped these because `ProgEval.Prog` has no pairing former — "a term
  can never use its input twice" (`rel.LeetRunTree`'s header), so two-input problems either ran
  CURRIED with the second input applied OUTSIDE the term (L67 in `rel.LeetRun3`, L100/L617 in
  `rel.LeetRunTree`) or were skipped outright (L2 in `Run1`, L21 in `Run2`, L205 in `Run5`).
  AoP's point-free vocabulary has exactly the missing pieces — the product `⟨p,q⟩` and `p × q` —
  so this file extends the term language by the ONE former `Prog` lacks:

  * `Prog2` — `Prog`'s applicative vocabulary (ground `fn`, diagram-order `comp`, the `SL`
    catamorphism `cata` evaluated by the same `foldSL`) plus the pairing former
    `pair p q = ⟨p,q⟩` (run both sub-programs on the same input, tuple the results);
    `p × q = ⟨π₁≫p, π₂≫q⟩` is derived (`prodP`).  Evaluator `evalP2`; the product β-laws hold
    by `rfl` (`evalP2_pair`).
  * `zipCata base step close` — the ZIP-FOLD (curried-two-input) scheme as ONE term of type
    `Prog2 (SL A × SL B) C`: fold the FIRST input into a FUNCTION carrier that awaits the
    second, transport the second to the `List` read outermost-first (`revListOf` — the order
    the fold consumes), and close with the problem's application map:
    `(⦇base, step⦈ × revListOf) ≫ close`.  A snoc fold consumes its LAST element outermost, so
    the zip pairs the two inputs back-aligned; loading an input head-outermost (`Run2.consOf`)
    flips it to the front-aligned lockstep the problems need.

  Wired (4), each REUSING the L-file's own step clauses and run on the L-file's own examples:
  * L2   add two numbers   — lockstep carry ripple, base 10: `rippleStep`'s clauses are
    `LC2.addFuel`'s cons/cons + cons/nil with the `xs`-recursion abstracted as the carrier;
    the leftover second-number tail ripples by `LC2.addFuel` itself ([] first list).  O(n+m).
  * L67  add binary        — the SAME `rippleStep` at base 2, leftover tail by
    `LC67.addBitsRev`; big-endian in/out, little-endian inside (the L-file's own orientation).
    Previously CURRIED in `Run3`; here the second number is part of the term's input.  O(n+m).
  * L21  merge two sorted  — `mergeStep` is `LC21.mergeFuel`'s cons/cons clause with the
    `xs`-recursion abstracted as the continuation carrier `List Int → List Int`: emit the
    `ys`-elements strictly below `x`, then `x`, hand the REMAINING `ys` inward.  `Run2`'s skip
    note feared a curried fold degrades to repeated insertion (O(n·m)); the continuation
    carrier avoids that — every comparison consumes an element of one input, so the term is
    the textbook merge at the L-file's own O(n+m).
  * L205 isomorphic strings — lockstep scan carrying TWO association maps: `isoStep` is
    `LC205.isoGo`'s cons/cons match verbatim with the recursion abstracted as the carrier
    `mapST → mapTS → remaining t → Bool`; length mismatch rejects at the boundary clauses.
    Same per-step `lookupL` cost as the L-file.

  Caveat (as in `Run2`): `SL` is non-empty, so the L-files' empty-input cases
  (`mergeFn [] []`, an empty summand) have no term-level counterpart.
-/
import rel.RelInterp
import rel.LeetRun2
import leet.L2
import leet.L21
import leet.L67
import leet.L205

namespace Freyd.Alg.FinRel.Pair

open Freyd.Alg.FinRel.ProgEval
open Freyd.Alg.FinRel.Run2 (consOf)
open Freyd.Alg.RelSet

/-! ## The pairing machinery: `Prog` + the product former, over the same `SL`/`foldSL` -/

/-- Program terms WITH PAIRING: `ProgEval.Prog`'s applicative vocabulary (ground maps,
    diagram-order composition, the `SL` catamorphism) extended by the point-free product
    mediator `pair p q = ⟨p,q⟩` — the one former `Prog` lacks, which is exactly what a term
    needs to consume a PAIR of inputs (or read one input twice). -/
inductive Prog2 : Type → Type → Type 1 where
  | fn   {I O : Type} (f : I → O) : Prog2 I O
  | comp {I M O : Type} : Prog2 I M → Prog2 M O → Prog2 I O
  | cata {A C : Type} (base : A → C) (step : C → A → C) : Prog2 (SL A) C
  | pair {I O₁ O₂ : Type} : Prog2 I O₁ → Prog2 I O₂ → Prog2 I (O₁ × O₂)

/-- The evaluator: `Prog`'s clauses (`cata` by the same structural `foldSL`) plus
    `⟨p,q⟩ x = (p x, q x)`. -/
def evalP2 : {I O : Type} → Prog2 I O → I → O
  | _, _, .fn f => f
  | _, _, .comp p q => fun x => evalP2 q (evalP2 p x)
  | _, _, .cata base step => foldSL base step
  | _, _, .pair p q => fun x => (evalP2 p x, evalP2 q x)

/-- The product β-law: `⟨p,q⟩` runs both sub-programs on the same input and tuples — so
    `⟨p,q⟩ ≫ π₁ = p` and `⟨p,q⟩ ≫ π₂ = q` pointwise, definitionally. -/
theorem evalP2_pair {I O₁ O₂ : Type} (p : Prog2 I O₁) (q : Prog2 I O₂) (x : I) :
    evalP2 (Prog2.pair p q) x = (evalP2 p x, evalP2 q x) := rfl

/-- The product of programs `p × q = ⟨π₁ ≫ p, π₂ ≫ q⟩`, derived from the pairing former. -/
def prodP {I₁ I₂ O₁ O₂ : Type} (p : Prog2 I₁ O₁) (q : Prog2 I₂ O₂) :
    Prog2 (I₁ × I₂) (O₁ × O₂) :=
  .pair (.comp (.fn Prod.fst) p) (.comp (.fn Prod.snd) q)

/-- Read an `SL` outermost-first (last snoc first) — the order a function-carrier zip fold
    consumes elements, used to transport the SECOND input to the `List` the carrier awaits.
    Composed with head-outermost loading (`Run2.consOf`) it reads the original list in order. -/
def revListOf {A : Type} : SL A → List A
  | .wrap a    => [a]
  | .snoc xs a => a :: revListOf xs

/-- **The zip-fold scheme** — the curried-two-input trick as ONE term: fold the FIRST input
    into a FUNCTION carrier `K` that awaits the second, transport the second input to the
    outermost-first `List`, and close with the problem's application map:
    `(⦇base, step⦈ × revListOf) ≫ close`. -/
def zipCata {A B K C : Type} (base : A → K) (step : K → A → K) (close : K → List B → C) :
    Prog2 (SL A × SL B) C :=
  .comp (prodP (.cata base step) (.fn revListOf)) (.fn fun p => close p.1 p.2)

/-- What the scheme means: the first input is genuinely FOLDED (`foldSL`), the second closed
    over — definitionally. -/
theorem evalP2_zipCata {A B K C : Type} (base : A → K) (step : K → A → K)
    (close : K → List B → C) (xs : SL A) (ys : SL B) :
    evalP2 (zipCata base step close) (xs, ys) = close (foldSL base step xs) (revListOf ys) := rfl

/-! ## L2 / L67 — lockstep carry ripple over two digit lists

  One step, base `b`: absorb the current digit `x` of the first number against the next
  remaining digit of the second (`0` once the second is exhausted), emit the sum digit, pass
  the carry inward — `LC2.addFuel`/`LC67.addBitsRev`'s cons/cons and cons/nil clauses with the
  recursion on the first list abstracted as the function carrier `f`. -/

/-- The carry-ripple step (carrier `carry → remaining second-number digits → sum digits`,
    everything least-significant-first). -/
def rippleStep (b : Int) (f : Int → List Int → List Int) (x : Int) :
    Int → List Int → List Int
  | c, []      => (c + x) % b :: f ((c + x) / b) []
  | c, y :: ys => (c + x + y) % b :: f ((c + x + y) / b) ys

/-- LC 2 as ONE two-input term: zip-fold the first number into the base-10 carry adder and
    close over the second with carry `0`.  The digit lists are little-endian, so both inputs
    load head-outermost (`consOf`) to put the least significant digit at the fold's outermost
    step, and the output is little-endian as is.  When the first number runs out, the leftover
    carry ripples through the second's remaining digits by the L-file's own `LC2.addFuel`
    (`[]` first list, `ys.length + 1` fuel sufficing). -/
def prog2 : Prog2 (SL Int × SL Int) (List Int) :=
  zipCata (rippleStep 10 fun c ys => LC2.addFuel (ys.length + 1) c [] ys) (rippleStep 10)
    (fun f ys => f 0 ys)

-- LeetCode 2's own examples: 342 + 465 = 807; 99 + 1 = 100 (a genuine carry-out digit).
example : evalP2 prog2 (consOf (2 : Int) [4, 3], consOf (5 : Int) [6, 4]) = [7, 0, 8] := by decide
example : evalP2 prog2 (consOf (9 : Int) [9], consOf (1 : Int) []) = [0, 0, 1]
    ∧ evalP2 prog2 (consOf (2 : Int) [4, 3], consOf (5 : Int) [6, 4])
        = LC2.addFn [2, 4, 3] [5, 6, 4] := by decide
-- second number longer than the first: the leftover tail rides through `LC2.addFuel`
example : evalP2 prog2 (consOf (5 : Int) [], consOf (7 : Int) [9, 9]) = [2, 0, 0, 1]
    ∧ LC2.addFn [5] [7, 9, 9] = [2, 0, 0, 1] := by decide

/-- LC 67 as ONE two-input term: the same zip-fold at base 2, leftover tail by the L-file's
    own `LC67.addBitsRev`.  The bit lists are BIG-endian, so both inputs load in natural order
    (`slOf` — last bit outermost = least significant first, the L-file's own reversed
    orientation), and the little-endian sum is reversed back at the close.  (Previously ran
    CURRIED in `rel.LeetRun3`; here the second number is part of the term's input.) -/
def prog67 : Prog2 (SL Int × SL Int) (List Int) :=
  zipCata (rippleStep 2 fun c ys => LC67.addBitsRev (ys.length + 1) c [] ys) (rippleStep 2)
    (fun f ys => (f 0 ys).reverse)

-- LeetCode 67's own examples: `1011 + 101 = 10000` (11 + 5 = 16), `11 + 1 = 100`.
example : evalP2 prog67 (slOf 1 [0, 1, 1], slOf 1 [0, 1]) = [1, 0, 0, 0, 0] := by decide
example : evalP2 prog67 (slOf 1 [1], slOf 1 []) = [1, 0, 0]
    ∧ evalP2 prog67 (slOf 1 [0, 1, 1], slOf 1 [0, 1])
        = LC67.addBinaryFn [1, 0, 1, 1] [1, 0, 1] := by decide

/-! ## L21 — merge two sorted lists: the classic two-input recursion as a zip fold

  `Run2` skipped this fearing a curried fold degrades to repeated insertion (O(n·m)).  With
  the CONTINUATION carrier `List Int → List Int` it does not: the step places the current
  first-list element after the second-list elements strictly below it and hands the REMAINING
  second list inward, so every comparison consumes an element of one input — the textbook
  merge order at the L-file's own O(n+m). -/

/-- One merge step: emit the `ys`-elements strictly below `x`, then `x`, handing the remaining
    `ys` to the continuation — `LC21.mergeFuel`'s cons/cons clause (`if x ≤ y` takes `x`) with
    the recursion on the first list abstracted as the carrier `f`. -/
def mergeStep (f : List Int → List Int) (x : Int) : List Int → List Int
  | []      => x :: f []
  | y :: ys => if x ≤ y then x :: f (y :: ys) else y :: mergeStep f x ys

/-- LC 21 as ONE two-input term: zip-fold the first sorted list (loaded head-outermost, so the
    fold consumes it front-first) into the merge continuation, close over the second.  The
    base is the step with the identity continuation: after the first list's last element is
    placed, the second's remainder passes through verbatim — `mergeFuel`'s nil clauses. -/
def prog21 : Prog2 (SL Int × SL Int) (List Int) :=
  zipCata (mergeStep fun ys => ys) mergeStep (fun f ys => f ys)

-- LeetCode 21's own examples (the `[]` cases are not `SL`-representable, see the header).
example : evalP2 prog21 (consOf (1 : Int) [2, 4], consOf (1 : Int) [3, 4])
    = [1, 1, 2, 3, 4, 4] := by decide
example : evalP2 prog21 (consOf (2 : Int) [5, 8], consOf (1 : Int) [3, 3, 9])
    = [1, 2, 3, 3, 5, 8, 9]
    ∧ evalP2 prog21 (consOf (1 : Int) [2, 4], consOf (1 : Int) [3, 4])
        = LC21.mergeFn [1, 2, 4] [1, 3, 4] := by decide

/-! ## L205 — isomorphic strings: the lockstep two-map scan as a zip fold -/

/-- One scan step: consume the current `s`-value `x` against the next `t`-value, checking and
    updating the two association maps — `LC205.isoGo`'s cons/cons match verbatim (both seen:
    partners must agree; both fresh: record the pair both ways; one-sided: reject) with the
    recursion abstracted as the carrier `f`; an exhausted `t` (`s` longer) rejects. -/
def isoStep (f : List (Int × Int) → List (Int × Int) → List Int → Bool) (x : Int)
    (mST mTS : List (Int × Int)) : List Int → Bool
  | []      => false
  | y :: ys =>
    match LC205.lookupL x mST, LC205.lookupL y mTS with
    | some y1, some x1 => decide (y1 = y) && decide (x1 = x) && f mST mTS ys
    | none,    none    => f ((x, y) :: mST) ((y, x) :: mTS) ys
    | some _,  none    => false
    | none,    some _  => false

/-- LC 205 as ONE two-input term: zip-fold `s` (loaded head-outermost, scanning front-to-back
    exactly like the L-file) into the two-map consistency scan, close over `t` with both maps
    empty; leftover `t` (`t` longer) rejects at the base's continuation (`ys.isEmpty`). -/
def prog205 : Prog2 (SL Int × SL Int) Bool :=
  zipCata (isoStep fun _ _ ys => ys.isEmpty) isoStep (fun f ys => f [] [] ys)

-- "egg" / "add" → true (pattern a,b,b both times); "foo" / "bar" → false (foo repeats).
example : evalP2 prog205 (consOf (101 : Int) [103, 103], consOf (97 : Int) [100, 100])
    = true := by decide
example : evalP2 prog205 (consOf (102 : Int) [111, 111], consOf (98 : Int) [97, 114])
    = false := by decide
-- "paper" / "title" → true, agreeing with the L-file's own scan.
example : evalP2 prog205
      (consOf (112 : Int) [97, 112, 101, 114], consOf (116 : Int) [105, 116, 108, 101]) = true
    ∧ LC205.isIsoFn [112, 97, 112, 101, 114] [116, 105, 116, 108, 101] = true := by decide
-- length mismatch rejects in both directions (`s` longer / `t` longer).
example : evalP2 prog205 (consOf (1 : Int) [2], consOf (7 : Int) []) = false
    ∧ evalP2 prog205 (consOf (1 : Int) [], consOf (7 : Int) [8]) = false := by decide

end Freyd.Alg.FinRel.Pair
