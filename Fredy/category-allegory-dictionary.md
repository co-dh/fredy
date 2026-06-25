# The Category ↔ Allegory dictionary (Freyd & Scedrov, Ch.1 ↔ Ch.2)

The heart of Chapter 2: each class of **categories** (functions-first, Ch.1) corresponds to a class of
**allegories** (relations-first, Ch.2). Caveat — the dictionary **starts at *regular*, not cartesian**: to
*compose* relations you need image factorization, so a merely cartesian category has no allegory of
relations yet.

| Ch.1 category (maps-side)    | Ch.2 allegory (relations-side)    | what the allegory adds                              |
|------------------------------|-----------------------------------|-----------------------------------------------------|
| cartesian (finite limits)    | — *(none yet)*                    | relations need images to compose                    |
| **regular**                  | unital **tabular** allegory       | every relation = a jointly-monic span (*tabulation*)|
| **exact** (Barr)             | **effective** tabular allegory    | equivalence relations split                         |
| **pre-logos** (= coherent)   | **distributive** allegory         | finite joins `∪`, `⊥`, stable under `∩` / `∘`       |
| **logos** (= Heyting / 1st-order) | **division** allegory        | residuation `R∖S`, `S/R` (gives `⇒` and `∀`)        |
| **pretopos**                 | effective + distributive + positive | exact + finite disjoint (extensive) coproducts    |
| **(elementary) topos**       | **power** allegory                | power objects / the relation-classifier `Λ`         |

## The bridge (every row)

Two mutually-inverse equivalences:

```
C  ↦  Rel(C)     relations in C            -- category  → allegory
A  ↦  Map(A)     total single-valued R     -- allegory  → category
```

`Map(A)` = the **maps** of `A` = relations `R` that are *entire* (total) and *simple* (single-valued).
A function is exactly a total single-valued relation.

So: **regular ≃ tabular, coherent ≃ distributive, Heyting ≃ division, topos ≃ power.** Each categorical
axiom about *functions and subobjects* becomes an algebraic axiom about *relations* (`∩`, `°`, `≤`,
division, power).

## Prototype anchors (bottom row)

- `Set` is a **topos**; `Rel` (sets and relations) is a **power allegory**; and `Map(Rel) = Set`.

## The two questions that prompted this

- **cartesian → ?**  Nothing. Relations aren't yet definable without image factorization; the relational
  hierarchy begins at *regular*.
- **pretopos → ?**  An **effective, distributive, positive** allegory: tabular + equivalence-relations-split
  + finite-joins + disjoint-coproducts. The one row without a single famous one-word name, because it is the
  *conjunction* exact ∧ coherent ∧ extensive rather than one fresh relational operator.

## Freyd's terminology note

Freyd writes **pre-logos** for *coherent category* and **logos** for *Heyting / first-order category*; this
repo follows that naming (e.g. `S1_60` pre-logos, `σ-pre-logos`, positive pre-logoi). Chapter 2 is developed
from its own axioms (allegory: composition, `≤`, `∩`, involution `°`, modular/Dedekind law) and does **not**
depend on Chapter 1's theorems — keep allegory axioms out of Ch.1 and vice-versa.
