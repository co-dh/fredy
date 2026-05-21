# Plan: prove the converse of τ3 (Freyd & Scedrov §1.494)

## Errors / gaps in `freyd_tau.md`

1. **Joint monicity is missing from the Table definition.** The transcribed
   "Table" in §"Earlier definitions referenced" is just a finite family of
   morphisms with a common source. But §1.492 ("supporting and pruning")
   says a subsequence is *supporting* when the resulting table "still satisfies
   the monic condition", which only makes sense if tables are jointly monic
   by definition. The user has confirmed: **a table requires `⟨x₁,…,xₙ⟩` to
   be jointly monic**. We add this to `Table`.

2. **`prune` is only a table when the omitted column is short.** §1.49 says:
   "If `xⱼ` is a short column, then `⟨T; x₁,…,x̂ⱼ,…,xₙ⟩` is *still a table*."
   Without `IsShort j`, removing a column can break joint monicity. The
   original `Freyd_tau_converse.lean` had `prune` unconditional, which is
   only correct if we drop monicity. We change `prune` to take an
   `IsShort` proof and use it to build the monic field.

3. **`mem_iff_resurfacing_id` is ill-typed as written.** The original
   `iso.hom : S.source ⟶ T.source` cannot be compared to `𝟙 S.source`
   without coercion. The book's claim "a table is in τ iff its resurfacing
   is an identity map" is informal shorthand for: the τ-representative
   equals the table itself (so the resurfacing iso has source = target =
   that table). We restate as `(τ.resurfacing S).1 = S`.

4. **`IsShort` is correctly stated.** The English in the book is
   "`f xⱼ ≠ g xⱼ → ∃ i<j, f xᵢ ≠ g xᵢ`"; the contrapositive is
   "`(∀ i<j, f xᵢ = g xᵢ) → f xⱼ = g xⱼ`", which is exactly the Lean
   definition. (The book's "as monic as" gloss is equivalent.)

## Definitions

```lean
structure Table where
  source : 𝒞
  length : Nat
  codom  : Fin length → 𝒞
  col    : (i : Fin length) → source ⟶ codom i
  monic  : ∀ ⦃X⦄ (f g : X ⟶ source), (∀ i, f ≫ col i = g ≫ col i) → f = g

def IsShort (S : Table) (j : Fin S.length) : Prop :=
  ∀ ⦃X⦄ (f g : X ⟶ S.source),
    (∀ i, i.val < j.val → f ≫ S.col i = g ≫ S.col i) →
    f ≫ S.col j = g ≫ S.col j

def prune (S : Table) (j : Fin S.length) (h : S.IsShort j) : Table where
  ... codom/col skip index j ...
  monic  := by
    -- agreement on cols ≠ j   ⟹ agreement on cols < j (since <  ⟹ ≠)
    -- ⟹ agreement on col j   (by `h`)
    -- ⟹ agreement on all cols
    -- ⟹ f = g                 (by S.monic)
```

## Why joint monicity unlocks the proof

Without monicity, the backward direction of `tau3_converse` stalls at
"`e.iso.hom` acts as identity on every column of `S`, but we cannot
conclude `e.iso.hom = 𝟙`". With monicity it is immediate: joint monicity
of `S.col` applied to `f := e.iso.hom`, `g := 𝟙 S.source` gives
`e.iso.hom = 𝟙`. Then `T = S` follows from the iso fields, hence `S ∈ τ`.

## Proof structure for `tau3_converse` (backward direction)

Given `hPrune : τ.mem (S.prune j h)` (with `h := hShort`):

1. **Resurface `S`.** Let `⟨T, hT, e⟩ := τ.resurfacing S`, so `T ∈ τ` and
   `e : Iso S T`. Write `j' := e.hLen ▸ j`.
2. **Transport shortness.** Show `T.IsShort j'`. For `f, g : X ⟶ T.source`
   agreeing on `T.col i'` for `i' < j'`: by `e.hCol`, `f ≫ e.iso.inv` and
   `g ≫ e.iso.inv` agree on `S.col i` for `i < j`; shortness in `S` gives
   agreement at `j`; backtrack with `e.iso.hom`.
3. **Prune `T`.** By `τ3`: `τ.mem (T.prune j' hShortT)`.
4. **Build `Iso (S.prune j h) (T.prune j' hShortT)`.** Same source iso,
   same codom equalities, columns differ only at the dropped index.
5. **τ1 uniqueness on `S.prune j h`.** Both it (by `hPrune`) and
   `T.prune j' hShortT` are τ-tables iso to it, so `S.prune j h = T.prune j' hShortT`.
6. **Conclude `T = S`.** From step 5, `e.iso.hom` fixes every column of
   `S` for `i ≠ j` (apply `e.hCol` against the prune equality). Shortness
   then forces it to fix the `j`-th column too. By `S.monic`,
   `e.iso.hom = 𝟙`. Read off `T = S` from the `Iso` fields.
7. **Done.** `T ∈ τ` and `T = S`, so `S ∈ τ`.

## Current status (as of session end)

**Fully proved:**
- `Table.prune` (with monic field using IsShort) ✓
- `Table.Iso.refl` ✓
- `TCat.resurfacing` ✓
- `TCat.mem_iff_resurfacing_eq` ✓
- `tau3_converse` forward direction (→, just τ3) ✓
- `isShort_of_iso` ✓ — proved using `eqToHom` + `eqToHom_trans` + `proof_irrel`

**Remaining sorries (3 sorry calls in 2 declarations):**

1. `iso_prune` — The hLen and hCodom fields are straightforward (proved).
   The hCol field fails because `T.x` has a dependent codomain: `T.x a`
   and `T.x b` have different TYPES when `a ≠ b`, so `rw [skip_eq] at h`
   reports "motive is not type correct". Fix: use `HEq` or restate hCol
   using a heterogeneous equality. Or: reformulate `hCol` using `▸` (which
   allows this kind of transport) in the `Table.Iso` structure.

2. `tau3_converse` backward: `hId` and `hTabEq` — Mathematical content is
   clear (see PLAN.md strategy). These also hit the dependent-type cast
   issue when trying to show `e.iso.iso.hom = eqToHom hSrc` (types differ
   unless `hSrc : tab.T = r.rep.T` is used as a cast) and `tab = r.rep`
   (structure equality with dependent fields).

**Root cause of remaining sorries:** `T.x` is indexed by `Fin T.n` and
has a dependent codomain `T.codom i`, making rewrites of the Fin argument
type-incorrect. The fix is either `HEq`-based reasoning or a refactoring
of `Table.Iso.hCol` to use `▸` notation (which handles heterogeneous
codomains naturally) instead of `eqToHom`.

Note: `isShort_of_iso` succeeded because it only rewrites in the composition
structure (not in T.x's argument), using `inv_col` + `eqToHom_trans`.
