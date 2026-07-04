# Dependency graph: finding duplicates, and what linear algebra does (and doesn't) tell us

Data: `graph/decls.tsv` (9135 declarations) + `graph/deps.tsv` (126847 edges), from
`scripts/ExtractGraph.lean`. Edge `i → j` means "declaration `i` uses declaration `j`" (the same
constants `#print axioms` walks). Written 2026-07-03.

The matrix **A** is 9135 × 9135, `A[i,j] = 1` if `i` uses `j`, else 0. Density 0.15% (very sparse).
One useful way to read it: **each row of A is a declaration's checklist of what it uses** — a 0/1
vector of length 9135. The matrix is 9135 such checklists stacked.

## Finding duplicates — the method that actually works (`scripts/dep_dup.py`)

Two declarations are likely the *same lemma proved twice under different names* if their rows are
nearly identical **after removing hubs**. Hubs = declarations used by almost everything
(`Cat.Hom` is used by 5556 decls, then `Cat`, `Cat.comp`, `Cat.id`, `Alg.Allegory.toCat`, …);
they're in almost every row, so they carry no information about who is a duplicate of whom. We drop
the 198 deps used by more than 100 decls, then compare the remaining ("rare") dependency sets.

Filters that separate real duplicates from lemmas that merely sit near each other:
- **cross-file** — same-file "siblings" (`inter_subset_left`/`right`, `Preserves`/`Reflects`) have
  identical rows but are distinct; a re-derived duplicate lives in a *different* file. This one filter
  removes most false positives.
- **same kind** (thm/def/instance) and **Jaccard ≥ 0.8** on the hub-removed rows.
- corroboration by **name** overlap and **type** overlap, used to rank — real duplicates keep a
  similar name (`recip_Sup` / `recip_Sup'`) and have the same type.

Validated on three known duplicates: recovered at ranks #3, #9, #49 (the #49 one is two tiny defs
sharing a single rare dep — rescued only because their types are identical). Result: **13
high-confidence pairs** (see `todo.md`), the biggest being a whole re-derived file — `CatColimitRegular`
re-proved as `RatCapHcanon` under a `LaxColim` namespace with primed names.

This method is **local** (compare two rows). The linear-algebra tools below are **global** (whole-matrix
structure). They answer different questions.

## Linear algebra on the matrix

### `eig(A)` — degenerate, gives nothing

The dependency graph has **no cycles** (proofs are well-founded; Lean requires termination). We
confirmed it: 9135 strongly-connected components = 9135 nodes, zero cycles. A no-cycle matrix, after
reordering nodes in dependency order, is triangular with a zero diagonal → **all 9135 eigenvalues are
exactly 0**, and the matrix can't be diagonalized. ARPACK's `eig(A)` literally failed to converge —
the expected symptom. So eigen-decomposition of the raw matrix is meaningless *by structure*, not by
numerics. You must build a symmetric matrix out of A first; that's what the next three do.

### SVD of A — `A = U · S · Vᵀ` — the one genuinely useful spectral tool

SVD works even when eigenvalues are all 0 (singular values are always real and ≥ 0). Concretely it
rewrites the whole matrix as a short sum of simple blocks, biggest first:

```
A  =  σ₁·(u₁ vᵀ₁)  +  σ₂·(u₂ vᵀ₂)  +  σ₃·(u₃ vᵀ₃)  +  …
```

Each `u vᵀ` is an outer product — a rank-1 matrix that says *"every declaration weighted by u uses
every dependency weighted by v."* So one block = **a group of declarations that share a group of
dependencies**. Reading off the three pieces for this matrix:

- **V (columns `vᵣ`) — weightings over the 9135 *dependencies*.** `v₁` here is
  `Cat.Hom (.51), Cat.comp (.41), Cat (.39), Cat.id (.21), Cat.assoc (.20), prod (.14)` — i.e. "the
  category primitives, used as a bundle." Each `vᵣ` is just a set of dependencies that tend to be used
  together.
- **U (columns `uᵣ`) — weightings over the 9135 *declarations*.** `uᵣ` says which declarations draw on
  bundle `vᵣ`. `u₁` is essentially every declaration (everything uses the category core).
- **S — the singular values `σ₁ ≥ σ₂ ≥ …`** (S is a diagonal matrix, zero off the diagonal). Each
  `σᵣ` is **how big / how common that block is** — how many of the matrix's 1s it accounts for. We got
  `133, 82, 58, 53, 51, 48, …`. Because `Σ σᵣ² = 126847` (the edge count), `σ₁² / 126847 ≈ 14%`: the
  single most common thing in the whole library is "declarations using the category core." The rest
  drop off slowly (no second big block) — the structure is spread thin.

So a single `(σ, u, v)` means, in plain words: *"a group of declarations (u) shares a group of
dependencies (v); σ is how large that shared-usage block is."* Biggest blocks first. Nothing more
mystical than "the most common co-usage patterns."

**Where it helps:** stack each declaration's coordinates along the top 12 `u`-directions (its row of U
scaled by S) → a 12-number summary of what it depends on. Duplicates have identical checklists, hence
identical summaries: measured cosine of the three known duplicates in this 12-D space was
**0.94, 1.00, 1.00**. So the SVD summary is a compact fingerprint and duplicates are nearest
neighbours — a fast *candidate generator* for dedup (denser recall than sharing a rare dep). It could
also give the graph viz a **deterministic** layout (top singular directions as x/y), replacing the
random force-layout.

**Its limit:** the top blocks just rediscover the core (same thing in-degree already tells you). SVD
finds coarse *groups*; the duplicate *decision* still needs the local row comparison above.

### PageRank — here it just re-finds the popular core (redundant)

PageRank ranks a declaration high if many (important) declarations depend on it. Result:
`Cat (143‰), Cat.Hom (42‰), Alg.Allegory, Cat.comp, Alg.Allegory.toCat, HasBinaryProducts,
Colim.Directed, HasTerminal`. Correct — these are the foundations — **but it's the same answer as just
sorting by in-degree**, which we already used to pick the hubs to remove. The extra machinery
(weighting a user by its own importance) barely reorders anything here. **Verdict: added nothing for
this task.**

### Graph Laplacian — a negative result: the code isn't modular by chapter

Symmetrize (`W = A + Aᵀ`) and look at the Laplacian's smallest eigenvectors — the standard way to split
a graph into cohesive groups (spectral clustering). Two findings:
- 46 disconnected pieces (46 zero eigenvalues) — small detached helpers; giant component 9005 nodes.
- Within the giant component, the smallest non-zero eigenvalues are tiny (`0.0025, 0.0033, …`) and the
  splitting vectors have **~0 average on Ch1, Ch2, and AOP alike** — they do **not** separate the
  chapters. If chapters were modular you'd see them land on opposite sides; they don't.

**Verdict: not useful for dedup, but the negative is informative** — the dependency graph is one
tightly-coupled blob around the `Cat`/`Allegory` core (Ch2 reuses Ch1, everything reuses the core), so
there's no clean split into chapter-shaped modules. This is the quantitative version of "Chapter 2
depends on Chapter 1."

## Bottom line

- `eig(A)`: meaningless (no cycles → all eigenvalues 0).
- **SVD: the only spectral tool that pays off** — a compact per-declaration fingerprint in which
  duplicates are nearest neighbours (dup candidate generator; also a deterministic viz layout).
- PageRank: same ranking as in-degree; nothing new.
- Laplacian: says the codebase isn't cleanly modular — a real diagnosis, but not a dedup tool.
- The actual duplicate finder is the **local, non-spectral** method: hub-removed row similarity +
  cross-file + name/type (`scripts/dep_dup.py`).
