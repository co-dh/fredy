/-
  LeetRunHard — the four "genuine misfit" LeetCode problems (L19, L5, L11, L253), classified
  RIGOROUSLY against the interpreter's recursion schemes.  Two-sided deliverable per problem:

  * a MACHINE-CHECKED NEGATIVE — the L-file's answer does not satisfy any fold recurrence on the
    answer carrier itself (`no_answer_fold` theorems below): concrete input pairs with EQUAL
    answers whose one-element extensions have DIFFERENT answers, so no step function
    `st : Answer → Elem → Answer` with `f (l ++ [x]) = st (f l) x` can exist.  This calibrates
    exactly WHY the breadth passes (`LeetRun1`/`LeetRun6`) skipped them: they are outside the
    answer-carrier `cata` fragment.  (Scope note: EVERY function is trivially a cata with a rich
    enough carrier — fold that rebuilds the input, then compute in the projection — so the honest
    question is never "is it a fold at all?" but "which carrier/scheme makes the step local?".
    The negatives pin the floor; the wirings exhibit the minimal honest enrichment.)

  * a WIRING through a genuine scheme — no computation hidden in a `.fn`:

    | num  | scheme                                                                            |
    |------|-----------------------------------------------------------------------------------|
    | L19  | catamorphism, ENRICHED carrier `Nat × List Int` (suffix counter + spliced suffix) |
    | L5   | catamorphism, ACCUMULATOR/CPS carrier `List Int → Nat × Nat` (higher-order fold)  |
    | L11  | HYLOMORPHISM — the interpreter's own `hyloF`; coalgebra = the two-pointer window  |
    | L253 | pipeline of TWO catamorphisms: insertion-sort-events fold `≫` counter/max scan    |

  * L19 (remove n-th from end): the raw `removeNthFn` is `take k ++ drop (k+1)` with
    `k = length − n` — index arithmetic, no fold.  `leet/L19_derived` already reshapes it onto the
    cons-list initial algebra with the carrier `(suffix length, suffix with the n-th-from-the-end
    removed)`; here that EXACT algebra (`LC19D.g`/`LC19D.st`) is run by the interpreter's
    `Prog.cata`/`foldSL` through the cons presentation `consToSL`, with a GENERAL theorem
    (`prog19_eq_removeNth`) — not just examples — chaining to `LC19D.remove_via`.

  * L5 (longest palindromic substring): each `bestFrom` step reads the ENTIRE remaining suffix
    (`commonPrefixLen left rest`), so no first-order carrier of the answer works (negative below).
    But `leet/L5_derived`'s insight makes it a genuine cata: the carrier
    `left ↦ (commonPrefixLen left rest, bestFrom left rest)` is a FUNCTION of the awaited
    accumulator, and the step (`LC5D.st`) reads only the head element and the folded carrier —
    the accumulation scheme (higher-order catamorphism).  Run by `Prog.cata`, general theorem
    `prog5_eq_longestPalin` via `LC5D.foldCL_ofList`.

  * L11 (container with most water): the sweep consumes the window from BOTH ends (move the
    shorter wall), so it is structural on no initial algebra of the input — not a cata and not a
    para (negative below).  It IS an unfold-then-fold: the interpreter's own fuel-bounded
    hylomorphism `ProgEval.hyloF`, with coalgebra `c11` peeling one wall per step (the L-file's
    exact branch order and `LC11.Area`) and algebra `imax`.  General theorem `maxArea11_eq`:
    equal to `LC11.maxAreaFn` on EVERY input.

  * L253 (meeting rooms II): the L-file's `roomsFn` maxes `countCover ivs iv.1` over its own
    starts — each step reads the WHOLE list, so `LeetRun6`'s "not a fold" verdict on that PROGRAM
    stands (and the negative below makes it rigorous; `leet/L253_derived`'s fold carries `ivs` as
    an input-dependent step parameter — a term family, not one program).  The PROBLEM, however,
    is the classic sweep-line, and the sweep is a fold PIPELINE, wired as ONE `Prog` term:
    insertion-sort cata (step = ordered event insert, the `LeetRun6` L242/L252 idiom, carrier
    `SL Ev` so no retagging `.fn` is needed) `≫` scan cata (carrier `(counter, best)`) `≫ .fn
    Prod.snd`.  Demos match `LC253.roomsFn` on the L-file's own examples (`by decide`); the
    general sweep = `roomsFn` theorem would be a full sweep-line correctness proof, out of scope
    for a wiring file.

  VERDICT: none of the four is outside the recursion-scheme world, but none fits the plain
  answer-carrier fold the breadth passes wire — each needs a genuinely stronger scheme (enriched
  carrier / higher-order accumulator / hylomorphism / multi-fold pipeline), and the negatives
  prove that necessity at the answer-carrier floor.

  Mathlib-free; sorry-free; axioms of the wirings ⊆ {propext, Quot.sound}.
-/
import rel.RelInterp
import leet.L19_derived
import leet.L5_derived
import leet.L11
import leet.L253

set_option linter.unusedVariables false

namespace Freyd.Alg.FinRel.Hard

open Freyd.Alg.FinRel.ProgEval
open Freyd.Alg.RelSet

/-! ## The cons presentation of `SL` — one bridge lemma serving L19 and L5

  `foldSL` is the snoc-cata (base at the FIRST element, elements combined left-to-right).  L19 and
  L5 recurse on the SUFFIX (their derived files fold the cons-list initial algebra `ConsList`), so
  their algebras are `st : E → C → C` with the base at the empty-suffix end.  `consToSL` presents
  a nonempty raw list inside the `SL` carrier so that `foldSL` computes exactly the cons-fold
  `List.foldr` — a data-presentation choice (O(n) restructuring, zero problem logic), the same
  move as the derived files' `ofList`. -/

/-- `consToSL x rest`: the `SL` value on which `foldSL (fun a => st a c0) (fun c a => st a c)`
    computes the CONS-fold `List.foldr st c0 (x :: rest)` — base at the last element. -/
def consToSL {A : Type} : A → List A → SL A
  | x, [] => SL.wrap x
  | x, y :: ys => SL.snoc (consToSL y ys) x

/-- The bridge: `foldSL` over the cons presentation IS `List.foldr` (of the same algebra). -/
theorem foldSL_consToSL {A C : Type} (st0 : A → C → C) (c0 : C) :
    ∀ (x : A) (rest : List A),
      foldSL (fun a => st0 a c0) (fun c a => st0 a c) (consToSL x rest)
        = List.foldr st0 c0 (x :: rest)
  | x, [] => rfl
  | x, y :: ys => by
      show st0 x (foldSL (fun a => st0 a c0) (fun c a => st0 a c) (consToSL y ys))
        = st0 x (List.foldr st0 c0 (y :: ys))
      rw [foldSL_consToSL st0 c0 y ys]

/-! ## L19 — remove n-th node from end: catamorphism with the ENRICHED carrier

  NEGATIVE first: the answer (the output list) satisfies no fold recurrence of its own — the
  carrier MUST be enriched.  POSITIVE: `leet/L19_derived`'s carrier `(suffix length, spliced
  suffix)` makes the step local (`c + 1 = n` detects "this head is the n-th from the end"); its
  algebra is reused VERBATIM and run by the interpreter's `Prog.cata`. -/

/-- **Rigorous negative**: no step function on the ANSWER carrier computes `removeNthFn` (here at
    `n = 1`): `[2]` and `[3]` have the same answer `[]`, but appending `5` gives `[2]` vs `[3]`. -/
theorem removeNth_no_answer_fold :
    ¬ ∃ st : List Int → Int → List Int, ∀ (p : List Int) (x : Int),
        LC19.removeNthFn (p ++ [x]) 1 = st (LC19.removeNthFn p 1) x := by
  rintro ⟨st, hst⟩
  have h1 := hst [2] 5
  have h2 := hst [3] 5
  have e1 : LC19.removeNthFn ([2] ++ [5]) 1 = [2] := by decide
  have e2 : LC19.removeNthFn ([3] ++ [5]) 1 = [3] := by decide
  have e3 : LC19.removeNthFn [2] 1 = [] := by decide
  have e4 : LC19.removeNthFn [3] 1 = [] := by decide
  rw [e1, e3] at h1
  rw [e2, e4] at h2
  exact absurd (h1.trans h2.symm) (by decide)

/-- **L19 as a term** (a family over the spec parameter `n`, like `LC19D.st n`): the derived
    file's algebra run by the interpreter's `cata`, then project the spliced suffix. -/
def prog19 (n : Nat) : Prog (SL Int) (List Int) :=
  .comp (.cata (fun x => LC19D.st n x (LC19D.g ())) (fun c x => LC19D.st n x c)) (.fn Prod.snd)

/-- The derived file's fold is the `List.foldr` of its own algebra (its `removeCL`/`ofList`
    equations, re-read as a foldr). -/
theorem removeCL_foldr (n : Nat) :
    ∀ l : List Int, LC19D.removeCL n (LC19D.ofList l) = List.foldr (LC19D.st n) (LC19D.g ()) l
  | [] => rfl
  | x :: xs => by
      show LC19D.st n x (LC19D.removeCL n (LC19D.ofList xs))
        = LC19D.st n x (List.foldr (LC19D.st n) (LC19D.g ()) xs)
      rw [removeCL_foldr n xs]

/-- **General correctness of the wiring** (not just examples): on the spec range `n ≤ length`,
    the interpreter's cata computes exactly `LC19.removeNthFn` — via `LC19D.remove_via`, so the
    splice correctness proved in `leet/L19.lean` transports to the interpreter run. -/
theorem prog19_eq_removeNth (n : Nat) (x : Int) (rest : List Int)
    (h : n ≤ (x :: rest).length) :
    evalP (prog19 n) (consToSL x rest) = LC19.removeNthFn (x :: rest) n := by
  show (foldSL (fun a => LC19D.st n a (LC19D.g ())) (fun c a => LC19D.st n a c)
    (consToSL x rest)).2 = LC19.removeNthFn (x :: rest) n
  rw [foldSL_consToSL (LC19D.st n) (LC19D.g ()) x rest, ← removeCL_foldr n (x :: rest)]
  exact (LC19D.remove_via (x :: rest) n h).symm

-- LeetCode 19's own examples, run in the interpreter (and cross-checked against the L-file):
example : evalP (prog19 2) (consToSL 1 [2, 3, 4, 5]) = [1, 2, 3, 5] := by decide
example : evalP (prog19 1) (consToSL 1 []) = [] := by decide
example : evalP (prog19 2) (consToSL 1 [2]) = [2] := by decide
example : evalP (prog19 2) (consToSL 1 [2, 3, 4, 5]) = LC19.removeNthFn [1, 2, 3, 4, 5] 2 := by
  decide

/-! ## L5 — longest palindromic substring: catamorphism with the ACCUMULATOR/CPS carrier

  NEGATIVE first: the answer length satisfies no fold recurrence — `bestFrom`'s step needs
  match-radii against the raw suffix, which no scalar folded value carries.  POSITIVE:
  `leet/L5_derived`'s carrier `List Int → Nat × Nat` ("the reversed-prefix accumulator awaits it,
  and carries the prefix-match radius alongside the best") makes the step (`LC5D.st`) a function
  of the head and the folded value alone — the accumulation scheme, run by `Prog.cata` (function
  carriers are ordinary carriers to `foldSL`). -/

/-- **Rigorous negative**: no step function on the ANSWER carrier computes `longestPalinFn`:
    `[98, 97]` and `[99, 98]` both answer `1`, but appending `98` gives `3` (`bab`) vs `2`
    (`bb`). -/
theorem palin_no_answer_fold :
    ¬ ∃ st : Nat → Int → Nat, ∀ (p : List Int) (x : Int),
        LC5.longestPalinFn (p ++ [x]) = st (LC5.longestPalinFn p) x := by
  rintro ⟨st, hst⟩
  have h1 := hst [98, 97] 98
  have h2 := hst [99, 98] 98
  have e1 : LC5.longestPalinFn ([98, 97] ++ [98]) = 3 := by decide
  have e2 : LC5.longestPalinFn ([99, 98] ++ [98]) = 2 := by decide
  have e3 : LC5.longestPalinFn [98, 97] = 1 := by decide
  have e4 : LC5.longestPalinFn [99, 98] = 1 := by decide
  rw [e1, e3] at h1
  rw [e2, e4] at h2
  omega

/-- **L5 as a term**: the derived file's CPS algebra run by the interpreter's `cata`, then apply
    the carrier at the empty accumulator and project the best. -/
def prog5 : Prog (SL Int) Nat :=
  .comp (.cata (fun x => LC5D.st x (LC5D.g ())) (fun k x => LC5D.st x k))
    (.fn (fun k => (k []).2))

/-- The derived file's fold is the `List.foldr` of its own algebra. -/
theorem foldCL_foldr :
    ∀ l : List Int, LC5D.foldCL (CL.ofList l) = List.foldr LC5D.st (LC5D.g ()) l
  | [] => rfl
  | x :: xs => by
      show LC5D.st x (LC5D.foldCL (CL.ofList xs))
        = LC5D.st x (List.foldr LC5D.st (LC5D.g ()) xs)
      rw [foldCL_foldr xs]

/-- **General correctness of the wiring**: the interpreter's cata computes exactly
    `LC5.longestPalinFn` on every nonempty input — via `LC5D.foldCL_ofList`, so the
    achievability/domination proved in `leet/L5.lean` transports to the interpreter run. -/
theorem prog5_eq_longestPalin (x : Int) (rest : List Int) :
    evalP prog5 (consToSL x rest) = LC5.longestPalinFn (x :: rest) := by
  show (foldSL (fun a => LC5D.st a (LC5D.g ())) (fun k a => LC5D.st a k)
    (consToSL x rest) []).2 = LC5.longestPalinFn (x :: rest)
  rw [foldSL_consToSL LC5D.st (LC5D.g ()) x rest, ← foldCL_foldr (x :: rest),
    LC5D.foldCL_ofList (x :: rest) []]
  rfl

-- LeetCode 5's own examples, run in the interpreter (and cross-checked against the L-file):
example : evalP prog5 (consToSL 98 [97, 98, 97, 100]) = 3 := by decide     -- "babad" → "bab"
example : evalP prog5 (consToSL 99 [98, 98, 100]) = 2 := by decide         -- "cbbd" → "bb"
example : evalP prog5 (consToSL 97 []) = 1 := by decide                    -- "a" → "a"
example : evalP prog5 (consToSL 114 [97, 99, 101, 99, 97, 114]) = 7 := by decide -- "racecar"
example : evalP prog5 (consToSL 98 [97, 98, 97, 100])
    = LC5.longestPalinFn [98, 97, 98, 97, 100] := by decide

/-! ## L11 — container with most water: HYLOMORPHISM (the interpreter's own `hyloF`)

  NEGATIVE first: the sweep consumes the window from BOTH ends, so the answer satisfies no fold
  recurrence on either end.  POSITIVE: dual-end convergence is exactly an UNFOLD — the coalgebra
  peels one wall per step (leaf when the window collapses), and the areas it emits are re-folded
  with `imax`.  The seed carries the list itself (no closure over the input), the branch order and
  `LC11.Area` are the L-file's own, and `ProgEval.hyloF` — already in the interpreter to show the
  fragment is not cata-only — runs it.  (`leet/L11_derived` proves the same shape as a RELATIONAL
  hylomorphism via `hyloFold_unique`; here it is the executable counterpart.) -/

/-- **Rigorous negative**: no step function on the ANSWER carrier computes `maxAreaFn`:
    `[1, 2]` and `[2, 1]` both answer `1`, but appending `2` gives `2` vs `4`. -/
theorem area_no_answer_fold :
    ¬ ∃ st : Int → Int → Int, ∀ (p : List Int) (x : Int),
        LC11.maxAreaFn (p ++ [x]) = st (LC11.maxAreaFn p) x := by
  rintro ⟨st, hst⟩
  have h1 := hst [1, 2] 2
  have h2 := hst [2, 1] 2
  have e1 : LC11.maxAreaFn ([1, 2] ++ [2]) = 2 := by decide
  have e2 : LC11.maxAreaFn ([2, 1] ++ [2]) = 4 := by decide
  have e3 : LC11.maxAreaFn [1, 2] = 1 := by decide
  have e4 : LC11.maxAreaFn [2, 1] = 1 := by decide
  rw [e1, e3] at h1
  rw [e2, e4] at h2
  omega

/-- The two-pointer coalgebra: seed `(heights, lo, hi)`; leaf `0` once the window has collapsed,
    else EMIT the window's own `LC11.Area` and move the SHORTER wall inward — the L-file's
    `twoPtrFuel` branch order exactly. -/
def c11 : (List Int × Nat × Nat) → Int ⊕ ((List Int × Nat × Nat) × Int)
  | (h, lo, hi) =>
    if lo < hi then
      if h[lo]! ≤ h[hi]! then Sum.inr ((h, lo + 1, hi), LC11.Area h lo hi)
      else Sum.inr ((h, lo, hi - 1), LC11.Area h lo hi)
    else Sum.inl 0

/-- **L11 as a hylomorphism**: unfold the window by `c11`, fold the emitted areas with `imax` —
    `ProgEval.hyloF` with fuel `length` (one unit per peeled wall plus the leaf), guarded by the
    L-file's own `n ≥ 2` test. -/
def maxArea11 (h : List Int) : Option Int :=
  if h.length ≥ 2 then
    hyloF c11 (fun a => a) (fun c a => LC11.imax c a) h.length (h, 0, h.length - 1)
  else some 0

/-- `imax` is commutative — needed because the hylo folds leaf-outward while `twoPtrFuel`
    accumulates root-inward. -/
theorem imax_comm (a b : Int) : LC11.imax a b = LC11.imax b a := by
  unfold LC11.imax; split <;> split <;> omega

/-- Unfold one `hyloF` step at a node of the coalgebra. -/
theorem hyloF_inr {S A C : Type} {g : S → A ⊕ (S × A)} {base : A → C} {step : C → A → C}
    {fuel : Nat} {s s' : S} {a : A} (hg : g s = Sum.inr (s', a)) :
    hyloF g base step (fuel + 1) s
      = match hyloF g base step fuel s' with
        | some c => some (step c a)
        | none => none := by
  simp only [hyloF]
  rw [hg]
  rfl

/-- Unfold one `hyloF` step at a leaf of the coalgebra. -/
theorem hyloF_inl {S A C : Type} {g : S → A ⊕ (S × A)} {base : A → C} {step : C → A → C}
    {fuel : Nat} {s : S} {a : A} (hg : g s = Sum.inl a) :
    hyloF g base step (fuel + 1) s = some (base a) := by
  simp only [hyloF]
  rw [hg]

/-- The hylo equals the L-file's fuelled two-pointer sweep, given enough fuel — by induction on
    fuel, `imax_comm` reconciling the two accumulation directions. -/
theorem hylo_eq_twoPtr (h : List Int) : ∀ fuel lo hi, hi - lo < fuel →
    hyloF c11 (fun a => a) (fun c a => LC11.imax c a) fuel (h, lo, hi)
      = some (LC11.twoPtrFuel h fuel lo hi) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi hf; omega
  | succ fuel ih =>
    intro lo hi hf
    by_cases hlt : lo < hi
    · by_cases hle : h[lo]! ≤ h[hi]!
      · have e : c11 (h, lo, hi) = Sum.inr ((h, lo + 1, hi), LC11.Area h lo hi) := by
          simp only [c11]; rw [if_pos hlt, if_pos hle]
        rw [hyloF_inr e, ih (lo + 1) hi (by omega)]
        simp only [LC11.twoPtrFuel]
        rw [if_pos hlt, if_pos hle]
        exact congrArg some (imax_comm _ _)
      · have e : c11 (h, lo, hi) = Sum.inr ((h, lo, hi - 1), LC11.Area h lo hi) := by
          simp only [c11]; rw [if_pos hlt, if_neg hle]
        rw [hyloF_inr e, ih lo (hi - 1) (by omega)]
        simp only [LC11.twoPtrFuel]
        rw [if_pos hlt, if_neg hle]
        exact congrArg some (imax_comm _ _)
    · have e : c11 (h, lo, hi) = Sum.inl 0 := by
        simp only [c11]; rw [if_neg hlt]
      rw [hyloF_inl e]
      simp only [LC11.twoPtrFuel]
      rw [if_neg hlt]

/-- **General correctness of the wiring** (every input, not just examples): the interpreter's
    hylomorphism computes exactly `LC11.maxAreaFn` — so the achievability/domination proved in
    `leet/L11.lean` transports to the interpreter run. -/
theorem maxArea11_eq (h : List Int) : maxArea11 h = some (LC11.maxAreaFn h) := by
  unfold maxArea11 LC11.maxAreaFn
  by_cases hl : h.length ≥ 2
  · rw [if_pos hl, if_pos hl, hylo_eq_twoPtr h h.length 0 (h.length - 1) (by omega)]
  · rw [if_neg hl, if_neg hl]

-- LeetCode 11's own examples, run through the hylo (and cross-checked against the L-file):
example : maxArea11 [1, 8, 6, 2, 5, 4, 8, 3, 7] = some 49 := by decide
example : maxArea11 [1, 1] = some 1 := by decide
example : maxArea11 [1, 8, 6, 2, 5, 4, 8, 3, 7]
    = some (LC11.maxAreaFn [1, 8, 6, 2, 5, 4, 8, 3, 7]) := by decide

/-! ## L253 — meeting rooms II: a PIPELINE of two catamorphisms (the sweep-line)

  NEGATIVE first: the answer satisfies no fold recurrence, and the L-file's `roomsFn` reads the
  WHOLE list at every step (`LeetRun6`'s verdict).  POSITIVE: the sweep-line algorithm — a
  DIFFERENT algorithm computing the same extremum — is a genuine fold pipeline: (1) insertion-sort
  the `2n` start/end events (the sort IS a cata: step = ordered insert, the `LeetRun6` L242/L252
  idiom), with carrier `SL Ev` so the sorted events flow straight into (2) the scan cata with
  carrier `(running counter, best)`; then project.  ONE `Prog` term, no logic in any `.fn`. -/

/-- **Rigorous negative**: no step function on the ANSWER carrier computes `roomsFn`:
    `[(0,10)]` and `[(5,15)]` both answer `1`, but appending `(0,3)` gives `2` vs `1`. -/
theorem rooms_no_answer_fold :
    ¬ ∃ st : Nat → Int × Int → Nat, ∀ (p : List (Int × Int)) (iv : Int × Int),
        LC253.roomsFn (p ++ [iv]) = st (LC253.roomsFn p) iv := by
  rintro ⟨st, hst⟩
  have h1 := hst [(0, 10)] (0, 3)
  have h2 := hst [(5, 15)] (0, 3)
  have e1 : LC253.roomsFn ([(0, 10)] ++ [(0, 3)]) = 2 := by decide
  have e2 : LC253.roomsFn ([(5, 15)] ++ [(0, 3)]) = 1 := by decide
  have e3 : LC253.roomsFn [(0, 10)] = 1 := by decide
  have e4 : LC253.roomsFn [(5, 15)] = 1 := by decide
  rw [e1, e3] at h1
  rw [e2, e4] at h2
  omega

/-- An event: `(time, +1)` = a meeting starts, `(time, -1)` = a meeting ends. -/
abbrev Ev : Type := Int × Int

/-- Event order: by time; at equal times ends (`-1`) BEFORE starts (`+1`) — meetings occupy the
    half-open `[start, end)` (the L-file's `countCover` test), so a meeting ending at `t` frees
    its room to one starting at `t`. -/
def evLe (a b : Ev) : Bool := decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 ≤ b.2))

/-- Ordered insert into a sorted snoc-list — the step of the insertion-sort cata, on the
    interpreter carrier `SL` itself (so `Prog.comp` chains the sort into the scan with no
    retagging `.fn`). -/
def insE (e : Ev) : SL Ev → SL Ev
  | SL.wrap a => if evLe e a then SL.snoc (SL.wrap e) a else SL.snoc (SL.wrap a) e
  | SL.snoc xs a => if evLe a e then SL.snoc (SL.snoc xs a) e else SL.snoc (insE e xs) a

/-- Order-preserving bridge onto the interpreter carrier (the `LeetRun6.snocs` move). -/
def snocs {A : Type} (first : A) (rest : List A) : SL A := rest.foldl SL.snoc (SL.wrap first)

/-- **L253 as one term**: sort-events cata `≫` counter/max scan cata `≫` project the best.
    Sort base: a single meeting's two events, ordered.  Sort step: insert the next meeting's two
    events.  Scan base: the earliest event alone (`imax 0` floors at "no meeting in progress").
    Scan step: bump the counter by the event's `±1`, keep the running max. -/
def prog253 : Prog (SL (Int × Int)) Int :=
  .comp (.cata (fun iv => insE (iv.2, -1) (SL.wrap (iv.1, 1)))
               (fun acc iv => insE (iv.1, 1) (insE (iv.2, -1) acc)))
    (.comp (.cata (fun e => (e.2, LC11.imax 0 e.2))
                  (fun p e => (p.1 + e.2, LC11.imax p.2 (p.1 + e.2))))
      (.fn Prod.snd))

-- LeetCode 253's own examples, run in the interpreter (and cross-checked against the L-file —
-- the sweep and the all-pairs `roomsFn` compute the same extremum):
example : evalP prog253 (snocs (0, 30) [(5, 10), (15, 20)]) = 2 := by decide
example : evalP prog253 (snocs (7, 10) [(2, 4)]) = 1 := by decide
example : evalP prog253 (snocs (0, 30) [(5, 10), (15, 20)])
    = (LC253.roomsFn [(0, 30), (5, 10), (15, 20)] : Int) := by decide
example : evalP prog253 (snocs (7, 10) [(2, 4)])
    = (LC253.roomsFn [(7, 10), (2, 4)] : Int) := by decide
-- back-to-back meetings share one room (half-open intervals: `[1,3)` then `[3,5)`):
example : evalP prog253 (snocs (1, 3) [(3, 5)]) = 1 := by decide

end Freyd.Alg.FinRel.Hard
