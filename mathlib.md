# Revisiting the mathlib-free decision

Notes from a deliberate re-examination (2026-07-03) of whether this repo should stay mathlib-free, drop
the constraint, or contribute upstream. Conclusion up front: **stay mathlib-free.** The parts of Mathlib
we'd want either don't exist (allegories, the AoP relational calculus) or are the easy, already-finished
scaffolding; the hard/central layer is ours and has no Mathlib counterpart to borrow from.

## 1. What exists in Mathlib (verified against the live index, not memory)

| Freyd / AoP concept                                   | In Mathlib? | Where                                              |
|-------------------------------------------------------|-------------|----------------------------------------------------|
| Category, functor, limits, products, terminal, pullbacks | yes, mature | `CategoryTheory.Limits.*`                        |
| Cartesian closed                                      | yes, mature | `CategoryTheory.Closed.Cartesian`                  |
| Regular category                                      | yes, recent | `CategoryTheory.Regular`, `Preregular`             |
| Coherent category (≈ pre-logos territory)             | yes, recent | `CategoryTheory.Precoherent`                       |
| Extensive (disjoint coproducts)                       | yes         | `CategoryTheory.FinitaryExtensive`                 |
| Subobject classifier / elementary topos               | yes, recent | `CategoryTheory.HasClassifier` (`Topos.Classifier`)|
| Grothendieck / sheaf topos                            | yes, mature | `CategoryTheory.Sites.*`, `Sheaf`                  |
| Abelian categories                                    | yes, mature | `CategoryTheory.Abelian.*`                         |
| Category of relations (bare)                          | yes         | `CategoryTheory.RelCat` (`Category.RelCat`)        |
| **Allegory** (+ distributive/division/power, tabular) | **no**      | — (loogle `"Allegory"` returns nothing)            |
| **Pretopos / logos / pre-logos** as named structures  | **no**      | — (loogle `"Pretopos"` returns nothing)            |
| AoP relational calculus (cata/hylo/greedy/thin/DP)    | **no**      | —                                                  |

Notes: Mathlib's `≫` is the same diagram order we use. The regular/coherent hierarchy came in with the
condensed-mathematics work and is built on `EffectiveEpi`, not Freyd's `Cover`/`Entire` primitives —
same math, different packaging.

## 2. Would switching help? No — it doesn't buy the part that is the point

Allegories (all of Ch. 2) and the entire AoP relational-programming layer (every `A*.lean`, the LeetCode
`L*.lean` track) **do not exist in Mathlib in any form.** `RelCat` is a bare category with none of the
involution / modular-law / tabular / division / power structure — we'd hand-build all of it anyway, now
on top of Mathlib's primitives. What switching *would* import is the categorical hierarchy up to topos
plus our hand-rolled non-categorical infra (`WellOrdering.lean` Zermelo/Zorn, `Locale.lean` Frame theory,
order/lattice) — i.e. the scaffolding that is already built and stable. The trade is: import the easy,
done part in exchange for a heavy dependency (Mathlib is hours to compile or a large cache fetch; we build
in seconds and clone tiny) and an impedance mismatch (Freyd's elementary proofs are stated over his own
definitions; re-basing on `EffectiveEpi`-style packaging means translating, not reusing).

## 3. Contributing allegories upstream — off the table

Contributing to Mathlib is a rewrite, not a port (redefine everything over Mathlib primitives + idioms +
docstrings + naming linters, through months of human maintainer review). Two decisive points: (a) **PRs are
human-reviewed and AI-authored contributions are not welcome there**, and (b) even a successful allegory
contribution leaves the AoP / LeetCode layer downstream in a **Mathlib-dependent** repo — reintroducing the
exact dependency we went mathlib-free to avoid. One constraint would relax (Mathlib is classical, so the
constructive discipline stops mattering); two are lost (self-contained, fast build). Not worth it.

## 4. Design comparison — Rel(Set) vs Mathlib's RelCat

Both dodge the "category-of-relations collides with the ambient `Category (Type u)`" problem with a
`structure` wrapper. The difference is *which side* gets wrapped:

- **Mathlib**: bare object `def RelCat := Type u`, wrapped **morphism** `structure Hom where rel : SetRel X Y`.
- **Ours**: wrapped **object** `structure RelSet where carrier : Type u`, bare morphism `a ⟶ b := a.carrier → b.carrier → Prop`.

This resolves a gotcha in our own notes: `def RelSet := Type u` failed for us *because* our morphisms were
raw `→ → Prop` with nothing to disambiguate; Mathlib's bare-object `def` works only because its `Hom`
wrapper does the disambiguating. The wrapper has to go on exactly one side.

**Verdict: our side is right for us.** Our whole allegory stack is proven *pointwise on morphisms*
(`hom_ext fun x y => …`, `le_iff`); a hom-wrapper would tax every one of those lines with `.rel`/`.ofRel`.
We construct objects only occasionally. Mathlib affords the hom-wrapper because `RelCat` is a *thin* file
(bare category + op-functor, nothing else) — which is the real headline: **Mathlib's category of relations
stops before any allegory structure, so for the hard 90% of our file there is no Mathlib proof to borrow.**
One portable idea (marginal, do not act now): Mathlib factors relation algebra into a standalone
`Data.Rel` (`○`, `.inv`, `id`, `CompleteLattice` giving `⊑`/`∪`/`∩`/`Sup` for free); we re-prove those
pointwise inside each instance. A small mathlib-free `Rel` helper module would DRY the model file — but the
payoff scales with the number of models and we have exactly one.

## 5. Hierarchy proof comparison — do they have better proofs?

Six-level comparison (category → cartesian → regular → coherent/extensive → exact/effective → topos/CCC),
each level machine-checked and adversarially re-verified. **No single Mathlib proof is better in any sense
we can use.** At every level Mathlib looks shorter on the page, and at every level that brevity is borrowed
from imports we cannot take: the colimit/cofork apparatus, the adjunction/mates library, the van-Kampen
tower, plus `aesop_cat`/`ext`/`simp`-set automation and pervasive `Classical.choice`/`noncomputable`. Strip
the library and their one-liners become 10–75-line proofs too. Where the *same lemma* can be compared
honestly, ours is as short or shorter, because our defeq-based / data-carrying definitions make the equation
a field projection or a one-token dual, with no hidden automation.

| Level                | Cleaner for us | Mathlib's brevity comes from                       | Same-lemma check                                                        |
|----------------------|----------------|----------------------------------------------------|-------------------------------------------------------------------------|
| Category             | ours           | `Quiver→Struct→Category` + `cat_disch` auto-params | opposite-cat laws: ours 1 token vs their `simp only` op/unop coherence   |
| Cartesian            | comparable     | products = `HasLimitsOfShape`, UP proved once      | product β-rule: both 1 line; ours a field proj (computable), theirs choice|
| Regular              | ours           | `RegularEpi` carries `IsColimit(cofork)` as data   | "cover is epic": theirs 1 line off the field; ours ~60 from `Cover` alone |
| Coherent / extensive | ours           | mono derived from stronger van-Kampen + `aesop_cat`| "inr monic": theirs ~6 lines on vanKampen; ours a disjointness field proj |
| Exact / effective    | comparable     | `EffectiveEpi`/`RegularEpi` front-load coeq data   | "epi = coeq of kernel pair": theirs ~10 (hands in isColimit), ours ~75    |
| Topos / CCC          | comparable     | curry/eval = an adjunction hom-equiv               | `curry_precomp`: ours 4-line rewrite; theirs 1-line `homEquiv_naturality` |

Recurring shape: Mathlib is shorter exactly when it has *pre-loaded the universal property as data* (a
colimit/adjunction field) or *proved it once generically and inherited it*. That's a library-scale
investment, not a cleverer proof. We pay per-theorem in elementary steps but stay computable, constructive,
axiom-clean.

## 6. What the comparison surfaced — 4 mathlib-free internal wins (ideas, zero dependency)

Ranked by value. Our own DRY/hygiene improvements the comparison exposed; none imports anything.

1. **Regular — collapse `cover_epi` from ~60 lines to ~3** (verifier compiled it; axiom-free). The
   equalizer-as-pullback-of-graphs plumbing it inlines already exists as
   `products_pullbacks_implies_equalizers` (`S1_43.lean:135`); feed the singleton bridge
   `cover_iff_coveringFamily_singleton` into `covering_family_epic` (`S1_513.lean:73`). Pure
   duplicate-deletion. Highest value, low risk.
2. **Topos — derive `true_monic` instead of assuming it** (verifier: typechecks). `true : 1→Ω` is a split
   mono by terminal uniqueness, so drop the postulated field from `HasSubobjectClassifier` (`S1_9.lean:99`)
   and prove `mono_of_retraction _ (term omega) (term_uniq _ _)`. Removes one proof-obligation field from
   every instance. Small, clean.
3. **Exact — unbundled kernel-pair-legs form of `cover_is_coequalizer_of_level`** (reuse `Cone.IsPullback`,
   `S1_45.lean:54`). Removes the `HasPullbacks` instance-diamond friction that currently forces manual
   `(hpull := …)` pinning (`S1_59.lean:3655`). Narrow but real.
4. **Coherent — add an elementary `coprod_universal` field** (van-Kampen specialized to binary cofans,
   stated with our `case`/`HasPullbacks`/`IsIso`). *Closes* the acknowledged universality gap
   (`S1_64.md:78`) and unblocks amalgamation/pretopos-balanced obligations. Adds a feature, not a
   simplification — bigger scope.

Rejected as not worth doing: the cartesian `fst_pair_assoc` reassoc lemmas (fire on too narrow a shape),
and the category opposite-wrapper (a tradeoff that would trade one-token dual-axiom proofs for op/unop
rewrite chains — adopt only if the `OppCat 𝒞 = 𝒞` diamond becomes more painful).

## 7. The one architectural lesson

Every genuine win traces to the same thing: **where we use a defeq alias (`OppCat C := C`, chosen kernel
pairs, chosen `HasPullbacks`) it induces an instance diamond we then hand-patch** (`S1_44.lean:363`,
`S1_45.lean:483`, `S1_59.lean:3655`). Mathlib sidesteps these with thin wrappers and unbundled predicates
(`IsKernelPair := IsPullback`, the `Opposite` struct). The transferable idea is not their proofs but their
**diamond-avoidance discipline** — and both fixes are pure Lean core.
