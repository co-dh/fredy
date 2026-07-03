# LeetCode in the Allegory — the Blind 75 as Bird–de Moor programs

Goal: solve the **Blind 75** LeetCode problems as *allegory programs* in `Rel(Set)`
(`Fredy/A6_1_RelSet.lean`), reusing the Algebra-of-Programming toolkit (`A6…A10`), each proved correct,
mathlib-free. `Fredy/L121.lean` is the seed example. This file is the running skills log + tracker;
update the **Skills** section after every solve.

## What "solving in allegory" means — the 4-step recipe

From `L121.lean`:

1. **Data = initial algebra.** A list is `SnocList L E` (`A6_SnocList.lean`), the initial algebra of
   `F X = L ⊕ X×E` (`wrap` a leaf, `snoc` an element). A left-to-right scan *is* a catamorphism.
2. **Program = catamorphism (a `Map`).** Write the fold `solveFn` by structural recursion, package it
   as `solve := graph solveFn : Data ⟶ Answer` in `Rel(Set)`, and prove it equals the relational cata
   `cataR alg ≫ …` (`solve_eq_cata`). Carry auxiliary state in the fold's result tuple (e.g.
   `(minSoFar, best)`), project out the answer.
3. **Spec = a relation.** `spec : Data ⟶ Answer` relates an input to *every* valid/achievable answer
   (e.g. `profit xs v ↔ v = 0 ∨ ∃ b before s, v = s−b`). LeetCode's "the best" is then `max(≤)·Λ spec`
   (or `min`) — the extremum of that relation.
4. **Correctness = `solve = extremum(≤)·Λ spec`.** Two halves:
   - **refinement** `solve ⊑ spec` — every answer the program returns is valid (`solve_profit`);
   - **domination** `∀ v, spec xs v → v ≤ solveFn xs` (or `≥` for `min`) — it beats every valid answer.

   This is exactly the shape of B&dM's **greedy theorem 7.2** (`A7_2`), **DP theorem 9.1** (`A9_1`), and
   **thinning theorem 8.1** (`A8_1`) — an abstract allegory program with this proof already done once.
   The per-problem job is to instantiate the algebra + monotonicity/optimality condition.

## The reusable toolkit

| piece                    | where                         | what                                                        |
|--------------------------|-------------------------------|-------------------------------------------------------------|
| `RelSet`, `⟶`, `⊑`, `≫`  | `A6_1_RelSet`                 | Freyd's `Rel(Set)` allegory (objects = sets, homs = relns)  |
| `graph f`, `Map`         | `A6_1_RelSet`                 | graph of a function; `Map` = entire+simple (a function)     |
| `SnocList L E`, `dSL`    | `A6_SnocList`                 | non-empty list as initial algebra of `F X = L ⊕ X×E`        |
| `Tree A`, `dTree`        | `A6_TreeBin`                  | binary tree as initial algebra of `F X = 1 + X×A×X` (cata, `cataR`) |
| `cataFold`, `cataR`      | `A6_SnocList`                 | the fold / relational catamorphism                          |
| `imin`, `imax` (+ omega) | `L121`                        | mathlib-free `Int` min/max with rewrite lemmas — copy these |
| `minRel`/`maxRel`, `Λ`   | `A7_1`, `A6_3`                | relational extremum and power-transpose (the `max(≤)·Λ`)    |
| greedy / DP / thinning   | `A7_2` / `A9_1` / `A8_1`      | the abstract optimality theorems to instantiate             |

Axiom budget target: `⊆ {propext, Quot.sound}` (fully constructive; no `Classical.choice`), like L121.

## Fit classification

Allegory programming shines on **folds / scans / DP / greedy / tree recursion**. Ratings below:
`★★★` natural catamorphism (do first — the AOP theorems apply directly); `★★` expressible with effort;
`★` awkward for the fold style (graph/matrix/hash/two-pointer) — reach via a relational spec + a fold
over an encoded structure, or defer. Trees are initial algebras too, so a `TreeCata` engine (analogous
to `SnocList`) unlocks the whole Tree block — **built: `A6_TreeBin` (see S12)**, reuse across ~14 problems.

## Blind 75 — tracker

Status: `·` todo, `▷` in progress, `✓` done (file). Do `★★★` first.

### Array
| #    | problem                                | fit | status         |
|------|----------------------------------------|-----|----------------|
| 121  | Best Time to Buy and Sell Stock        | ★★★ | ✓ `L121.lean`  |
| 53   | Maximum Subarray (Kadane)              | ★★★ | ✓ `L53.lean`   |
| 152  | Maximum Product Subarray               | ★★★ | ✓ `L152.lean`  |
| 217  | Contains Duplicate                     | ★★★ | ✓ `L217.lean`  |
| 238  | Product of Array Except Self           | ★★  | ·              |
| 1    | Two Sum                                | ★★  | ·              |
| 15   | 3Sum                                   | ★★  | ·              |
| 11   | Container With Most Water              | ★★  | ·              |
| 153  | Find Minimum in Rotated Sorted Array   | ★   | ·              |
| 33   | Search in Rotated Sorted Array         | ★   | ·              |

### Binary
| #    | problem                | fit | status |
|------|------------------------|-----|--------|
| 191  | Number of 1 Bits       | ★★★ | ✓ `L191.lean` |
| 338  | Counting Bits          | ★★  | ·      |
| 268  | Missing Number         | ★★  | ·      |
| 190  | Reverse Bits           | ★★  | ·      |
| 371  | Sum of Two Integers    | ★   | ·      |

### Dynamic Programming
| #    | problem                          | fit | status |
|------|----------------------------------|-----|--------|
| 70   | Climbing Stairs (Fibonacci fold) | ★★★ | ✓ `L70.lean`  |
| 198  | House Robber                     | ★★★ | ✓ `L198.lean` |
| 213  | House Robber II                  | ★★  | ·      |
| 91   | Decode Ways                      | ★★★ | ✓ `L91.lean`  |
| 62   | Unique Paths                     | ★★★ | ✓ `L62.lean`  |
| 55   | Jump Game (greedy 7.2)           | ★★★ | ·      |
| 322  | Coin Change (DP 9.1)             | ★★★ | ✓ `L322.lean` |
| 300  | Longest Increasing Subseq (thin) | ★★★ | ✓ `L300.lean` |
| 1143 | Longest Common Subsequence       | ★★★ | ·      |
| 139  | Word Break                       | ★★  | ·      |
| 39   | Combination Sum                  | ★★  | ·      |

### Interval
| #    | problem                        | fit | status |
|------|--------------------------------|-----|--------|
| 56   | Merge Intervals (sort + fold)  | ★★★ | ·      |
| 435  | Non-overlapping (greedy 7.2)   | ★★★ | ·      |
| 57   | Insert Interval                | ★★  | ·      |
| 252  | Meeting Rooms                  | ★★  | ·      |
| 253  | Meeting Rooms II               | ★★  | ·      |

### Linked List
| #    | problem                        | fit | status |
|------|--------------------------------|-----|--------|
| 206  | Reverse Linked List (cata)     | ★★★ | ·      |
| 21   | Merge Two Sorted Lists         | ★★★ | ·      |
| 23   | Merge k Sorted Lists           | ★★  | ·      |
| 19   | Remove Nth Node From End       | ★★  | ·      |
| 141  | Linked List Cycle              | ★   | ·      |
| 143  | Reorder List                   | ★   | ·      |

### String
| #    | problem                                     | fit | status |
|------|---------------------------------------------|-----|--------|
| 3    | Longest Substring Without Repeating (scan)  | ★★★ | ·      |
| 20   | Valid Parentheses (stack fold)              | ★★★ | ✓ `L20.lean` |
| 242  | Valid Anagram (fold to multiset)            | ★★★ | ·      |
| 125  | Valid Palindrome                            | ★★★ | ·      |
| 49   | Group Anagrams                              | ★★  | ·      |
| 424  | Longest Repeating Character Replacement     | ★★  | ·      |
| 76   | Minimum Window Substring                    | ★★  | ·      |
| 5    | Longest Palindromic Substring               | ★★  | ·      |
| 647  | Palindromic Substrings                      | ★★  | ·      |
| 271  | Encode and Decode Strings                   | ★★  | ·      |

### Tree  (build a `TreeCata` engine first → unlocks the block)
| #    | problem                                        | fit | status |
|------|------------------------------------------------|-----|--------|
| 104  | Maximum Depth of Binary Tree (cata)            | ★★★ | ✓ `L104.lean` |
| 226  | Invert/Flip Binary Tree (cata)                 | ★★★ | ✓ `L226.lean` |
| 100  | Same Tree                                      | ★★★ | ✓ `L100.lean` |
| 98   | Validate Binary Search Tree                    | ★★★ | ✓ `L98.lean`  |
| 124  | Binary Tree Maximum Path Sum (tupling cata)    | ★★★ | ✓ `L124.lean` |
| 102  | Binary Tree Level Order Traversal              | ★★  | ·      |
| 572  | Subtree of Another Tree                        | ★★  | ✓ `L572.lean` |
| 105  | Construct Binary Tree from Preorder + Inorder  | ★★  | ·      |
| 230  | Kth Smallest Element in a BST                  | ★★  | ·      |
| 235  | Lowest Common Ancestor of a BST                | ★★  | ·      |
| 297  | Serialize and Deserialize Binary Tree          | ★★  | ·      |
| 208  | Implement Trie                                 | ★   | ·      |
| 211  | Add and Search Word                            | ★   | ·      |
| 212  | Word Search II                                 | ★   | ·      |

### Graph / Matrix / Heap  (mostly `★`, defer — reach via relational spec)
| #    | problem                             | fit | status |
|------|-------------------------------------|-----|--------|
| 128  | Longest Consecutive Sequence        | ★★  | ·      |
| 207  | Course Schedule (topo sort)         | ★★  | ·      |
| 347  | Top K Frequent Elements             | ★★  | ·      |
| 200  | Number of Islands                   | ★   | ·      |
| 133  | Clone Graph                         | ★   | ·      |
| 417  | Pacific Atlantic Water Flow         | ★   | ·      |
| 269  | Alien Dictionary                    | ★   | ·      |
| 261  | Graph Valid Tree                    | ★   | ·      |
| 323  | Number of Connected Components      | ★   | ·      |
| 73   | Set Matrix Zeroes                   | ★   | ·      |
| 54   | Spiral Matrix                       | ★   | ·      |
| 48   | Rotate Image                        | ★   | ·      |
| 79   | Word Search                         | ★   | ·      |
| 295  | Find Median from Data Stream        | ★   | ·      |

## Skills (running log — append after each solve)

### S0 — the L121 template (seed)
- **State-in-the-tuple fold.** When the answer needs auxiliary running data, fold to a tuple and project
  (`solveFn = (foldFn …).2`). Prove `foldFn`'s components equal named invariants (`foldFn_fst =
  minPrice`) so the optimality proof can reason about them.
- **Correctness = refinement + domination**, each a straight `induction xs`. Refinement: the returned
  value is achievable (build the `∃ before …` witness). Domination: `∀ v, spec v → v ≤ solveFn`, using
  the invariant lemmas + `omega`.
- **Mathlib-free `min`/`max`:** copy `imin`/`imax` and their 6 `omega`-backed lemmas from `L121`; never
  reach for `Nat.max`/`Int.instMax` — you want to control the rewrite set.
- **Executable check:** end with `#eval`-style `example : solveFn (ofList …) = k := by decide` sanity
  cases — catches spec/impl mismatches instantly.
- **Axioms:** `graph`/`Map` route keeps it at `{propext, Quot.sound}`; check with `#print axioms`.

### S1 — L53 (Maximum Subarray / the Kadane family)
- **Two-layer spec, no `mutual`.** For subarray/substring answers, define the "ending at the last
  element" relation first (`suffixSum`), then the "anywhere" relation on top of it (`subSum`'s `snoc`
  case `= subSum xs v ∨ suffixSum (snoc xs p) v`) — a plain function calling an already-defined one, not
  a `mutual` block. This is the reusable template for L152, L3, L5, L647.
- **Invoke the fst-invariant at the *current* list.** In the domination proof's suffix case, don't
  re-induct on `suffixSum` — instantiate the already-proved `foldFn_fst_dominates` at `snoc xs p` (the
  list being processed). Turns a nested induction into one lemma application whenever a spec case reads
  "≤ the fold's first component".
- **Nested `imax_eq_or` for `max`-of-`max` state.** When the state is `best = max(prev, e)` with
  `e = max(p, prevEnd+p)`, the refinement witness needs `imax_eq_or` twice (outer: `best` stayed vs took
  `e`; inner: `e` is bare `p` vs `prevEnd+p`). This two-level split is the shape for any Kadane-family
  fold whose state is a `max`-of-`max`.
- **No empty/`0` floor when the empty selection is forbidden.** Unlike L121 (spec has a free `v=0` "do
  nothing"), a non-empty-subarray spec carries no floor — the negative answer on an all-negative input
  falls out for free, no side condition. Do NOT add a `0` disjunct for "must pick ≥1 element" problems.

### S2 — L152 (Maximum Product Subarray) — sandwich invariant + mathlib-free nonlinearity
- **Two-sided sandwich for non-monotone ops.** Addition is monotone (L53 tracked only `maxEnd`);
  multiplication is not, so the fold carries BOTH `minEnd` and `maxEnd`, and the domination invariant is
  two-sided: `minEnd ≤ v ≤ maxEnd` for every suffix product. A fold over a non-monotone binary op needs
  the running min AND max of the "ending here" quantity.
- **Sign-split lemma reusing core monotonicity.** `m ≤ v ≤ M ⟹ imin(mp,Mp) ≤ vp ≤ imax(mp,Mp)` is
  nonlinear (`omega` can't). `rcases Int.le_total 0 p` and chain via `Int.le_trans` with Lean core's
  `Int.mul_le_mul_of_nonneg_right` / `Int.mul_le_mul_of_nonpos_right` (both in `Init/Data/Int/Order`) —
  no hand-rolled monotonicity; never case-split on which side `imin`/`imax` equals.

### S3 — axiom-hygiene & Lean-craft traps (general; watch on every solve)
- **`omega` on a CONJUNCTION goal can pull in `Classical.choice`** even when each conjunct alone is
  omega-clean. If `lean_verify` shows `Classical.choice`, suspect an `omega` closing an `∧`; split it or
  give a constructive term. (Caught in L152.) ALWAYS `lean_verify` the headline theorem.
- **`subst h` on `h : v = x` with `x` a match/`induction`-bound pattern variable deletes `x`** ("unknown
  identifier" later). Use `rw [h]`.
- **A `/-- doc -/` comment cannot precede a `mutual` block** ("unexpected token 'mutual'"). Use `/- -/`.
- **Prefer one `∀ xs, P xs ∧ Q xs` induction over mutually-recursive *theorems*.** Mutual `def`s are fine;
  mutual `theorem`s are fragile. Interdependent invariants → one conjunction, split with `refine ⟨_,_⟩`
  before any `omega`.
- **`nomatch h` is comma-greedy** — `⟨fun h => nomatch h, g⟩` swallows `g`; write `(nomatch h)`.
- **`if (b : Bool) then …` elaborates to `ite (b = true) …`** — reduce on a concrete `true`/`false` with
  `decide`/full `simp`, not `simp only`. Bool programs: `Bool.or_eq_true`/`Bool.and_eq_true`/
  `decide_eq_true_eq`, not `omega`.
- **`ih.mp` vs `ih.mpr`** are trivially transposed in `iff` inductions — if one won't close, try the other.

### S4 — L198 (House Robber) — subset DP
- **Flag-indexed spec via a genuine `mutual`.** `robF`/`robT` (last house excluded/included) reference
  each other in their `snoc` cases on the strictly-smaller `xs` — a real `mutual def` (stays
  definitionally reducible). Extends L53's *sequential* two-layer spec to a *mutual* one.
- **Paired invariant + recycling.** Fold state `(best, prevBest)`; prove `best ⊇ robSpec` and
  `prevBest ⊇ robF` in one conjunction-induction. Load-bearing: `prevBest(snoc xs p) = best(xs)` closes
  the `robF` goals arithmetic-free — reuse for any DP where one state slot recycles another's prev value.

### S5 — L217 (Contains Duplicate) — the DECISION shape
- **Reflection bridge.** Program = Bool fold (`hasDup`, calling a Bool membership sub-fold `memB`); spec =
  Prop relations (`dupP`/`memP`) of the same shape. Prove `memB xs p = true ↔ memP xs p` by induction;
  then `rw` transports Bool↔Prop. Correctness is a one-level `iff` — no refinement+domination, no
  `max(≤)·Λ` extremum.
- **`solve = spec` without `Decidable`.** `spec xs b := (b = true ↔ dupP xs)` + `bool_eq_of_iff_true`
  (`cases b <;> cases c`) — sidesteps a `Decidable dupP` instance that `decide` would demand.

### S6 — L70 (Climbing Stairs) — tupling / linearization
- **Equality refinement by carrying a pair.** When the naive recurrence is already exact but exponential,
  fold `(f n, f(n+1))` for O(1) steps; one induction `fibPair n = (climb n, climb (n+1))` gives
  `solve = spec` (an *equality*, unlike the `⊑` of the optimization scans).
- **Use the problem's own initial algebra.** Object is plain `ℕ` (initial algebra of `1+X`), not a
  `SnocList` — not every allegory program needs the snoc-scan engine.

### S7 — L20 (Valid Parentheses) — stack/depth scan (decision)
- **Depth scan = `(Int depth, Bool ok)` fold**, `ok` short-circuiting once broken; correctness
  (`valid ↔ balancedP`) matches a **prefix-condition spec** (`neverNeg ∧ net = 0`) via two invariants.
  Template for Dyck / balanced-structure decisions.
- **Condition the invariant on the flag.** Once `ok = false` the numeric slot is a *don't-care* dummy, so
  `depth = depthP` holds only *given `ok = true`* (`&&` short-circuit never consults the dummy). When a
  fold's aux state stops meaning anything after failure, condition its invariant on the still-valid flag.

### S8 — L191 (Number of 1 Bits) — count catamorphism
- **State-is-answer cata.** `Nat`-count fold over a `Bool`-element `SnocList` (new element type); the
  state *is* the answer, so `solve = cataR alg` with **no** trailing projection (contrast L121's `≫ snd`).
- **Give a bare count real content.** Prove `count ≤ size`, `count = size ↔ allTrue`, `count = 0 ↔
  allFalse` (from `b2n_eq_one_iff`/`b2n_eq_zero_iff`) instead of a tautological spec.

### S9 — L91 (Decode Ways) — counting DP, not optimisation: took the `decode = climb` route
- **Counting problems are NOT the `L121`/`L198` recipe.** Those refine an ⊑-achievability spec into
  a `≤`-extremum (refinement + domination on a totally ordered type). A COUNT has no order to refine
  into — the honest spec is "the exact number of valid segmentations", and the only content is
  showing an O(n) fold computes that number. Reach for the enumeration-Prop-plus-cardinality route
  (build an inductive family of segmentation witnesses, prove the fold's value is its cardinality)
  ONLY if you actually need it: it requires bijections between witness sets at each recursive step
  (partitioning "segmentations of `snoc xs d`" into "ends in a 1-digit group" ∪ "ends in a 2-digit
  group", each in bijection with a smaller witness set) — real work, with no `Fintype`/`Nat.card`
  infra in this repo to lean on.
- **Route taken: `L70`'s tupling recipe, not the Prop/cardinality one.** Wrote `decode`/`decodePrev`
  as the mutually-recursive TEXTBOOK recurrence directly on `Nat` (no witness type) — the "last group
  is a single digit" / "last group is a valid pair" case split IS the standard decode-ways
  recurrence, accepted as *the* definition of the count exactly as `L70`'s naive `climb` is accepted
  as *the* definition of "ways to climb `n` stairs", with zero enumeration proof beyond that
  definition. It is exponential (each step recurses into two smaller lists, and those overlap), so
  the O(n) `foldFn` — which carries `(ways, prevWays, lastDigit)` — is proved equal to it by one
  induction (`foldFn_eq`), the `L70` linearisation move generalised from a pair to a TRIPLE.
- **A validity guard splits state into "current" vs "one-back".** The 2-digit-window check needs BOTH
  the last digit (`ld`, to form `ld*10+d`) and the count with the last digit removed (`prevWays`, the
  double-branch's contribution) — carry both, don't recompute either. `prevWays` after processing `d`
  is exactly the OLD `ways` (before `d`), the same "recycle the previous slot" trick as `L198`'s
  `prevBest`.
- **Trap: a `-` inside prose inside a `/- … -/` block comment can close it early.** `1-/2-digit` in a
  block comment silently ends the comment at the `-/` substring, cascading into "Function expected"/
  "Unknown identifier" errors dozens of lines later that look unrelated to the real cause. Grep any
  new block comment for a literal `-/` before debugging downstream errors.
- **Trap: `rw` across a `mutual`-def equation often leaves one `rfl` short.** After `rw` substitutes
  the IH equalities, the goal usually becomes definitionally the unfolded `mutual` equation but `rw`'s
  built-in `try rfl` doesn't always fire on it — append an explicit `rfl` after the `rw` (confirmed via
  `lean_multi_attempt`: `rw [...]` alone left "unsolved goals", `rw [...]; rfl` closed it).

### S10 — L62 (Unique Paths) — 2-D DP as a row-carrying fold, and a well-founded-recursion trap
- **2-D equality refinement = `L70`'s tupling, one dimension up.** The naive 2-argument recurrence
  `paths` is already the exact answer (an EQUALITY correctness proof, like `L70`, not `L121`'s
  refinement+domination `⊑`); the efficient program carries an entire DP ROW (`SnocList Nat Nat`, all
  `1`s initially) down the grid's rows instead of a scalar/pair, each new row the INCLUSIVE PREFIX SUM
  of the previous row. The crux proof strengthens "the fold equals the spec" from a single value to a
  WHOLE ROW (`rowAt m n = pathsRow m n`, `pathsRow` an explicit snoc-built list of `paths`-values),
  then a NESTED induction (outer on the row index `m`, inner on the column count `n` inside the crux
  lemma `scanStep_pathsRow`) reduces the row-step to exactly the book's 2-D recurrence at one column.
- **Trap: a genuine 2-argument recurrence (each recursive call decreasing a DIFFERENT argument) compiles
  to WELL-FOUNDED recursion, not structural — its equations are only propositionally true.** `paths (M+1)
  (N+1) = paths M (N+1) + paths (M+1) N` (and even the base cases like `paths (n+1) 0 = 0`) do **not**
  hold by `rfl`/`show … ; rfl`/`decide` (kernel reduction gets stuck on the `WellFounded.fix`/`Acc.rec`
  wrapper) — every unfolding step needs `simp [paths]` (which DOES use the auto-generated `paths.eq_def`
  equation lemmas). Contrast `L70`'s `climb`/`fibPair`, both simple *single*-argument structural
  recursions, where bare `rfl` sufficed throughout — that pattern silently breaks the moment a second
  argument becomes independently recursive. Diagnostic: `rfl`/`show`-then-`rfl` failing with "Type
  mismatch: rfl has type ?m = ?m" on a plain-looking recurrence unfold is the signature of this trap.
- **`simp [paths, Nat.add_comm]` can over-rewrite; isolate the commute instead.** Letting `simp` use
  `Nat.add_comm` alongside the recursive unfold reshuffled unrelated subterms (`m+2` became `1+(m+1)`)
  and left a mismatched goal. Fix: prove the *oriented* recurrence via `simp [paths]` alone first
  (`hbase`), then flip it with one targeted `rw [hbase, Nat.add_comm]` into the order the fold actually
  produces (`scanStep`'s `acc + p`, not the book's `p + acc`) — don't hand `Nat.add_comm` to a broader
  `simp` call.

### S11 — L300 (Longest Increasing Subsequence) — records-list DP + thinning connection
- **Two-layer spec with FLIPPED dependency.** `isSubseqInc = anyEnd = prefix ∨ lastEnd`; but unlike
  L53/L198 (whose "ending here" layer needs only a *suffix*), subsequences skip, so `lastEnd` needs the
  whole prefix's `anyEnd`. When the object can skip elements, the "ending-at-last" layer references the
  *broad* prefix relation, not a narrow suffix.
- **Growing-witness-list invariant pair.** The O(n²) fold carries a `List (Int × Nat)` of records; its
  correctness is a PAIR of invariants (`records_sound` + `records_complete`) — the L53-`foldFn_fst`
  analogue for any DP whose state is an accumulating witness list, not a scalar.
- **Thinning (`A8_1`) is the O(n log n) upgrade, not needed here.** Dropping a record `(v,l)` dominated by
  `(v',l')` (`v'≤v ∧ l'≥l`) is exactly `thinRel`; but `A8_1`'s abstract `thinning` lives in
  `UnguardedPowerLCDA` over power objects, so using it needs recasting the concrete list as a power-object
  frontier + proving the step `MonotonicAlg` — a real reindexing, deferred. Concrete-list route closes
  full O(n²) correctness.

### S12 — L104 + the `A6_TreeBin` engine — trees are initial algebras too
- **New reusable engine `Fredy/A6_TreeBin.lean`.** `Tree A = nil | node (Tree A) A (Tree A)` = initial
  algebra of `F X = 1 + X×A×X`; a section-for-section port of `A6_SnocList` (`cataTreeFold`,
  `InitialAlgebra`, `cataR`). **Unlocks the Tree block** (#226/#100/#98/#124…) as folds over it.
- **Two tree-port traps:** (1) the payload-free `nil` summand must map to `True`, not `x = y` (else
  `rfl`-vs-`trivial` term mismatches once `simp` collapses `Unit` equalities); (2) `node`'s TWO recursive
  fields — after `obtain ⟨l,a,r⟩`, a hyp `hv.2.1 : (l,a,r).snd.fst = …` is *defeq* to `a = a'` but not
  *syntactically*, so `rw` fails; first `have haq : a = a' := hv.2.1`, then `rw [haq]`.
- **Tree depth = `max(≤)·Λ pathLen`** (achievable root-to-`nil` path length) — the L121 extremum shape,
  walking the `imax`-larger child instead of scanning a list. State-is-answer, so `solve = cataR alg`.

### S13 — L322 (Coin Change) — ∞-lattice DP over an index axis + the fuel trick
- **`Option Nat` as the ∞-extended lattice.** `omin`/`osucc` (`none` = ∞) states achievability +
  minimality + impossibility as ONE `Option`-valued spec (`coinSpec`) — cleaner than a sentinel `Nat` or
  three separate theorems.
- **Recurse on the INDEX axis (amount), not the input list** — a new shape vs every linear scan so far.
  The descent `amount − c < amount` looks well-founded; **tame it with a fuel parameter**: `dpFuel : fuel
  → amount → Option Nat` recurses on `fuel` (ordinary `Nat.rec`), staying kernel-reducible so `decide`
  works (a `termination_by`/`WellFounded.fix` version is opaque to `decide` — cf. L62/S10's WF trap).
  Prove correctness by induction on `fuel` via a generic per-level `coinFold` lemma. **Reusable for any DP
  over a shrinking index** (LCS #1143 will need it).
- **Gotcha:** `rcases h : e with pat` *generalizes `e` in the goal*, so an existing witness `hs : … = some
  mv` can go useless (the goal's existential becomes `some mv = some mv₁`, closed by `rfl`). Inspect with
  `lean_goal`, don't guess from the error text.

## Tree block (wave 3, over the `A6_TreeBin` engine)

### S14 — L98 (Validate BST) — bounds accumulator threaded DOWN
- Opposite flow to every prior fold (depth/stack flow UP from leaves): `within lo hi t` carries `Option
  Int` sentinels (`none` = unconstrained), TIGHTENED at each node (`l` gets `hi := some a`, `r` gets
  `lo := some a`), so each node is checked against ancestor-inherited bounds — rules out the non-local BST
  bug by construction. Proof: keep `lo hi` GENERALIZED (structural recursion on `t`, not `induction t`
  with bounds fixed) so the two recursive calls instantiate at the tightened bounds. Template for any
  inherited-constraint tree decision (AVL / red-black invariants, range queries).

### S15 — L226 (Invert Tree) — structural OUTPUT (a `Rel(Set)` endomorphism)
- Answer object is `dTree A` again: `solve : dTree A ⟶ dTree A` is a genuine endomorphism, `cataR` fed
  `c := dTree A` (contrast L104's `c := ℕ`). No order to refine into — the spec is a structural relation
  `IsMirror` (simultaneous recursion on both trees, crosswise child swap in `node`). A structural-output
  program carries a natural extra law: **involutivity** `invert(invert t) = t` (the same-object analogue
  of a scalar fold's idempotence/monotonicity).
- **`Tree A` has no `DecidableEq`** (engine stays `Rel(Set)`-only) — add `deriving instance DecidableEq
  for Tree` locally for `decide` checks; and a `/-- doc -/` can't precede `deriving instance` (same family
  as the `mutual` trap — use `--`).

### S16 — L100 (Same Tree) — reflection bridge on a BINARY relation
- Generalize L217's bridge to two inputs: `induction t` while `t'` stays universally quantified (Lean
  threads it as `∀ t'` in each IH); a `cases t'` per case gives the 4 shape-combos, the `nil`/`node` cross
  cases close by `simp [sameFn, SameP]` (both literal `false`/`False`), and the real work is one
  `node/node` case reducing to a conjunction of two independent single-tree IHs.
- Mathlib-free: **`tauto` is unavailable** — use `and_assoc`/`or_assoc` for reassociations. Lambda params
  need explicit type ascription (`fun p : Tree Int × Tree Int => …`) before `.1`/`.2` project through the
  `Cat.Hom` unfold.

### S17 — L572 (Subtree) — nested-relation composition
- The outer `subFn` fold calls a SECOND fold (`sameFn`) at every node: `sameFn (node…) t || subFn l t ||
  subFn r t`. Each sub-fold gets its own reflection bridge (`same_correct`) before the outer
  `solve_correct` (induction on `s` only) composes them with `Bool.or_eq_true`. Wrinkle: `||`/`&&` are
  left-assoc but `∨`/`∧` right-assoc — the final `rw` needs one `or_assoc` to line up (silent "unsolved
  goals", not an error).

### S18 — L124 (Max Path Sum) — tupled tree extremum + `Option`-∞ + the nil-witness trap
- **Tupled tree cata `(best, gain)`**: `gain` = best non-bending downward path from this root (folds only
  children's `gain`); `best` = max over both children's `best` and the through-root bend value. Prove
  `gain`'s achieve/dominate FIRST, then reuse it as a lemma in `best`'s through-root case — don't re-derive
  the descent twice.
- **`Option`-∞ for the empty tree's "no path"** via a whole-value `omax_eq_or : omax x y = x ∨ omax x y =
  y` (4-way `cases` + `imax_eq_or`), NOT `none`/`some` decomposition at each use — turns a 3-way max into
  two chained applications.
- **The nil-child witness trap:** `imax`'s tie-break can credit `imax 0 (gain l)` to the child branch even
  when `l = nil` (`gain nil = 0`), where `downPath nil _` is `False`. Fix: prove `gain_achieves` as
  `l = nil ∨ downPath l (gain l)` and route through the "just the root" witness (`v = a`, since `a+0=a`)
  when the nil case fires.
