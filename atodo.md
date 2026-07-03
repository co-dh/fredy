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
- [ ] §6.6  Sorting by selection
- [ ] §7.3  Planning a company party
- [ ] §7.4  Shortest paths on a cylinder
- [ ] §7.5  The security van problem
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

Notes:
- §6.5 "Unique fixed points" is theory (hylo uniqueness, already parameterised as `HyloUnique`
  in `A6_3`) — not a concrete program; skip unless it turns out to add content.
- Reusable infra lives in `A6_1_RelSet` + `A6_1_Digits` (graph=Map, cataFold-from-relation,
  rprodMap, entire_total/simple_uniq, Fmap equation-lemma pattern).  Lift shared datatype
  combinators (Nat/cons-list initial algebras, sumRel/prodRel relators) to a shared file when a
  second section needs them.
- If a section hits a genuine wall (e.g. needs machinery not yet built), record it here and move on.
