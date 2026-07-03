# AoP concrete case studies — "use allegory to program" track

Formalize Bird & de Moor's concrete programs (not the abstract theory, which is done in
`Fredy/A4_*`–`A10_*`) in the Set model `Rel(Set)` (`Fredy/A6_1_RelSet.lean`).  Each section =
new datatype(s) as initial algebra + the program derived point-free, following the pattern of
`Fredy/A6_1_Digits.lean`.  One section per file `Fredy/A<ch>_<sec>_<Name>.lean`, one commit each.

Foundation (DONE):
- [x] `A6_1_RelSet.lean` — Set model Rel(Set), full allegory stack (b744a7a)
- [x] §6.1 Digits of a number — `A6_1_Digits.lean` (5f186d1): Decimal initial algebra, val, val° recursion
- [x] `A6_SnocList.lean` — GENERIC snoc-list `SnocList L E = L + (·)×E` initial algebra + cata_converse_eq
      (reusable engine; §6.1 Decimal = SnocList Digit⁺ Digit, §6.4 Bin = SnocList Unit Bit)

## To do (in order)

- [x] §6.4  Fast exponentiation and modulus computation — `A6_4_FastExp.lean`: exp/mod as hylomorphisms
      over Bin, fast recursion = μ (divide-and-conquer least fixed point) via hylo_eq_mu
- [x] `A6_ConsList.lean` — GENERIC cons-list `ConsList L E = L + E×(·)` initial algebra (head/tail) +
      cata_converse_eq + `cataR_eq_relCata` bridge (cataFold IS the relational catamorphism)
- [x] §6.6  Sorting by selection — `A6_6_Sort.lean` (parameterised) + `A6_6b_SortConcrete.lean`
      (FULLY CONCRETE): `sort = ⦇[nil,select°]⦈°` + its recursion (cata_converse_eq); correctness
      `sort ⊑ perm≫ordered` via fusion (6.4).  A6_6b DISCHARGES ALL hypotheses — concrete
      `selectC x (a,y) := Perm(a::y) x ∧ (a below all y)`, concrete ordered algebra, and the fusion
      proviso (`hfus_concrete` via `perm_mem`) — so `selection_sort_correct_concrete` holds for ANY
      `R : A → A → Prop` with NO hypotheses.  ✅ FIRST fully un-parameterised optimisation case study.
- [~] §7.3  Planning a company party — `A7_3_Party.lean`: `choose_monotonic` (first claim, concrete
      product fact) + `company_party_greedy` (party planning = greedy theorem `greedy_max`).  PARTIAL:
      the rose-tree datatype `tree A = node(A, list(tree A))` (NESTED inductive) + concrete `party`
      catamorphism + `⟨include,exclude⟩` monotonicity DEFERRED — needs a rose-tree engine (mutual
      tree/list structural fold; harder than cons/snoc-lists).  Tree engine = the gate for §7.3 fully.
- [WALL] §7.4  Shortest paths on a cylinder — genuine heavy-machinery WALL: needs n-tuples (`LN A` =
      length-n lists), sets-as-lists (`PL A`), the transpose `trans`, `zip` (N commutes with F), `cp`,
      `union`/`setify`, and `generate` as a LAX NATURAL TRANSFORMATION (§5.7), all feeding Theorem 7.1.
      No cheap concrete extractable piece (unlike §7.3's choose); a parameterized version = Thm 7.1
      renamed (vacuous).  Deferred — would be a multi-hundred-line concrete build.
- [WALL] §7.5  The security van problem — needs the DEFERRED ch.5 §5.6 `partition : list(list⁺ A)←list A`
      combinator + `secure` prefix/suffix-closed coreflexives + fusion/greedy derivation.  Small
      concrete piece exists ("cons monotonic on R°", (7.14)) but the section rests on `partition`.
      Gated on the §5.6 combinator layer.
- [ ] §8.2  Paths in a layered network
- [ ] §8.3  Implementing thin
- [ ] §8.4  The knapsack problem
- [ ] §8.5  The paragraph problem
- [ ] §8.6  Bitonic tours
- [ ] §9.2  The string edit problem
- [ ] §9.3  Optimal bracketing
- [ ] §9.4  Data compression
- [ ] §10.2 The detab–entab problem
- [ ] §10.3 The minimum tardiness problem
- [ ] §10.4 The TeX problem

## Shared prerequisites for the remaining sections (build these first)

The rest are NOT independent one-offs — they share two prerequisite layers that must be built:

1. **Cons-list engine** `ConsList L E = L + E × X` (mirror of `A6_SnocList`, element on the LEFT of
   the product; needed for `head`/`tail`).  Most of §6.6–§10.4 use `list A` = cons-lists.
2. **Chapter-5 list combinators (DEFERRED, unbuilt)** — §5.6 concrete list combinatorics (`perm`,
   `subseq`, `inits`/`tails`, `partition`, `inlist`=membership) were never formalized (see
   [[algprog-a4-formalization]] Ch.5 drops).  §6.6 sorting needs `perm` + `ordered` + `inlist`;
   the optimisation case studies (§7.3+) need `subseq`/`partition`/`inits` as the coalgebra `T`.

Per-section dependency (⇒ = also needs the concrete optimisation layer already built abstractly):
- §6.6 sorting = cons-lists + `perm` + `ordered` catamorphism + fusion (⦇[nil,select°]⦈°).
- §7.3–7.5 = cons-lists + `subseq`/`partition` + `minRel`/greedy (A7) on concrete cost.
- §8.2–8.6 = cons-lists/trees + `thinRel` (A8) on concrete data.
- §9.2–9.4 = cons-lists + DP (A9) on concrete data; §9.1 case studies were the deferred ones.
- §10.2–10.4 = cons-lists + greedy (A10) on concrete data.

RECOMMENDED ORDER: (a) build `A6_ConsList.lean` (quick mirror of `A6_SnocList`); (b) build a
`perm`/`ordered`/`inlist` module (ch.5 §5.6 list combinators) — the real gate; (c) then §6.6; then
the optimisation case studies reuse (a)+(b)+ the abstract A7–A10 theorems.

§5.6 LAYER — CORE DONE: `A5_6_ListCombinators.lean` (`list A = ConsList Unit A`): `perm` (Perm
inductive; reflexive/symmetric/transitive — DISCHARGES the `hperm` hyp of §6.6/§7.5), `inlist`
(membership), `prefixR` (preorder), `subseq` (reflexive + weaken/of_cons).  STILL TODO for full
un-parameterisation: `ordered = ⦇[nil, cons·ok]⦈` (needs `inlist`+order R), `partition = concat°`
(needs list-of-nonempty-lists), and the concrete `select` fusion-proviso (§6.6) / secure (§7.5).

Notes:
- §6.5 "Unique fixed points" is theory (hylo uniqueness, already parameterised as `HyloUnique`
  in `A6_3`) — not a concrete program; skip.
- Reusable infra: `A6_1_RelSet` (Set model) + `A6_SnocList` (generic snoc-list initial algebra,
  cata_converse_eq) + `A6_1_Digits`/`A6_4_FastExp` (worked instances).  See [[relset-concrete-programming]].
- If a section hits a genuine wall, record it here and move on.
