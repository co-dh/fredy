# Formalization Coverage Map

**Repository**: Freyd & Scedrov, *Categories, Allegories* (North-Holland, 1990)
**Date**: 2026-06-16
**Methodology**: sorry counts exclude comment-only lines; real sorries are tactic `sorry`
on non-comment lines (block-comment-stripped Python scan). Total files: 60.

---

## Auxiliary infrastructure files (not section-named)

| File                   | Sorries | Notes                                                                                   |
| ---------------------- | ------- | --------------------------------------------------------------------------------------- |
| `DirectedColimit.lean` |       0 | Directed colimit of types (foundation for §1.543 transfinite argument); sorry-free      |
| `CatColimit.lean`      |       0 | Directed colimit of categories (CatSystem, Coherent, colimitCat); sorry-free            |
| `CatColimitRegular.lean` |     0 | M3a: colimit inherits terminal when transitions preserve it; sorry-free                 |
| `HornDiagram.lean`     |       0 | §1.39 Horn sentence ↔ Freyd diagram: syntactic `Horn`/`Diagram` types + constructive `hornDiagramIso` (axiom-free) + Typst/fletcher renderer obeying §1.391/§1.393 (objects not collapsed, explicit identities — left-invertibility drawn as the triangle, not an iso). `lake env lean --run` emits diagrams; tested on §1.39/§1.41/§1.45 book samples. Standalone. |
| `HornToQSeq.lean`      |       0 | Bridge to the semantic `QSeq` (`S1_38b`): `qLeftInv f` realizes the §1.39 left-invertible diagram as a genuine Q-sequence, and `satisfies_qLeftInv` proves its §1.395 `Satisfies` IS `∃ g, f≫g=1_A` (axiom-free); complement = negation (Classical, via Thm 2); iso-invariance (axiom-free). |
| `QSeqExamples.lean`    |       0 | TEN book Q-sequences generated as real `QSeq` terms, each PROVED `Satisfies = book meaning` (`ex01`–`ex10`): §1.39 left-invertible/∀∃-lifting, §1.3(9) factor-through/∃∃-conjunction, §1.395 complement (×2, Classical), `nil` ∀/∃ boundary, vacuous ∀-step, Thm-1 iso-invariance. ex01–04 constructive, ex05–06 Classical, ex07–10 axiom-free. |
| `QSeqRender.lean`      |       0 | IN-LEAN renderer for Freyd's §1.39 Q-sequence notation (panels of growing diagrams separated by vertical bars with ∀/∃/∃!/! ON TOP; covers `↠`, parallel pairs, puncture marks `÷`). `Panel`/`Item`/`QDiagram` + `render : QDiagram → String` (Typst/fletcher). Reproduces — MATCHING the book (verified vs PDF): left-invertible §1.39, single-monic §1.41, EQUALIZER §1.428, PROJECTIVE §1.524. (§1.523 well-pointed is a Q-*tree*, §1.398 — branching, beyond this linear-sequence renderer.) `lake env lean --run Fredy/QSeqRender.lean`. |

---

## Chapter 1

### §1.1  Basic definitions

| File        | Sections            | Sorries | Main results / status                                                                           |
| ----------- | ------------------- | ------- | ------------------------------------------------------------------------------------------------|
| `S1_1.lean` | §1.1                |       0 | `Cat` typeclass: Hom, id, comp, id_comp, comp_id, assoc. Notation `⟶` `≫`. Sorry-free.        |

### §1.14–§1.18  Monoids, groups, functors

| File          | Sections                   | Sorries | Main results / status                                                                      |
| ------------- | -------------------------- | ------- | ------------------------------------------------------------------------------------------ |
| `S1_14.lean`  | §1.14, §1.15, §1.17, §1.182, §1.1(10) | 0 | Monoid↔one-object cat; discrete cat; groupoid; opposite category; iso of cats. Sorry-free. |
| `S1_18.lean`  | §1.18, §1.181              |       0 | `Functor` typeclass (map, id, comp); functors preserve iso. Sorry-free.                    |

### §1.24–§1.27  Examples, slice, natural transformations

| File          | Sections                                     | Sorries | Main results / status                                                                      |
| ------------- | -------------------------------------------- | ------- | ------------------------------------------------------------------------------------------ |
| `S1_24.lean`  | §1.242, §1.245, §1.263, §1.271, §1.273, §1.283, §1.284 | 0 | Groups cat; preorder cat; pointed sets; right/left A-sets; strongly connected. Sorry-free. |
| `S1_26.lean`  | §1.26                                        |       0 | Slice category A/B (`Over`, `OverHom`, `overCat`). Sorry-free.                            |
| `S1_27.lean`  | §1.27, §1.271, §1.272, §1.273, §1.274        |       1 | `NaturalTransformation`; Cayley representation; natural equivalence. 1 sorry: §1.274 natural equivalence preservation of all first-order sentences. |

### §1.31–§1.39  Functor theory, equivalences

| File          | Sections                | Sorries | Main results / status                                                                                  |
| ------------- | ----------------------- | ------- | ------------------------------------------------------------------------------------------------------ |
| `S1_31.lean`  | §1.31, §1.32            |       0 | `Embedding`, `Full`, `Representative`; equivalence functor. Sorry-free.                               |
| `S1_33.lean`  | §1.33, §1.333           |       1 | `Faithful` functor; full embedding is faithful; 1 sorry in Cayley-rep faithfulness in a general cat.  |
| `S1_34.lean`  | §1.34, §1.341           |       1 | `Isomorphic` (reflexive, symmetric, transitive); equinumerosity; 1 sorry in iso-class well-definedness.|
| `S1_35.lean`  | §1.35, §1.243           |       0 | `ForgetfulFunctor`; always an embedding. Sorry-free.                                                   |
| `S1_36.lean`  | §1.36, §1.367           |       0 | `Inflation`; strong equivalence; equivalence kernel; factorization. Sorry-free.                        |
| `S1_38.lean`  | §1.38, §1.389, §1.392    |       0 | Duality; Stone duality (statement); finite-presentation Q-sequence (graph + path equations) + op-dual + functor preserve/reflect. NOT §1.395 (no quantifiers). Sorry-free. |
| `S1_38b.lean` | §1.395, §1.396, §1.397   |       1 | Genuine quantified Q-sequence (`QSeq`/`Satisfies`/`complement` with ∀/∃ steps). Thm1 iso-invariance (axiom-free); Thm2 complement=¬satisfies (constructive half axiom-free, full ↔ via Classical); §1.396 `DiagonalFill` preserve (axiom-free)/reflect; §1.397 iso case axiom-free. 1 documented sorry: §1.397 inflation-class general case (needs §1.361/§1.396 cross-category routing). |
| `S1_39.lean`  | §1.34–§1.39             |       0 | `EquivalentCategories`; skeleton/coskeleton; split idempotent; exact sequence; measures. Sorry-free.   |

### §1.41–§1.49  Limits, pullbacks, τ-categories

| File          | Sections                          | Sorries | Main results / status                                                                                       |
| ------------- | --------------------------------- | ------- | ----------------------------------------------------------------------------------------------------------- |
| `S1_41.lean`  | §1.41, §1.412                     |       0 | `Mono`, `MonicPair`, `MonicFamily`, `IsIso`; iso composition. Sorry-free.                                   |
| `S1_42.lean`  | §1.421–§1.425                     |       1 | `HasTerminal`, `HasBinaryProducts`; diagonal; finite product from terminal+binary products. 1 sorry: `finiteProduct_from_term_binary` inductive step (dependent rewriting). |
| `S1_43.lean`  | §1.43–§1.438                      |       2 | Equalizers; pullbacks from products+equalizers; Cartesian category; §1.437 representation criterion; §1.438 reflects-equalizers→faithful. 2 sorries in those two theorems. |
| `S1_44.lean`  | §1.44, §1.441                     |       0 | `SliceForget` Σ: A/B→A; A/B has terminal; Σ preserves pullbacks/equalizers; Σ faithful. Sorry-free.        |
| `S1_45.lean`  | §1.45, §1.451–§1.454              |       3 | `Cone`, `HasPullback`, `HasPullbacks`; kernel pair; mono iff kp-diag iso; pullback of mono is mono; `invImg`, `Sub.inter`. 3 sorries: pullback interchange law instances.   |
| `S1_47.lean`  | §1.442, §1.444, §1.47, §1.48      |       0 | Cayley preserves/reflects pullbacks+equalizers; Horn sentences (§1.444); dense monics; rational cats. Sorry-free (1 sorry previously resolved). |
| `S1_49.lean`  | §1.491–§1.49(11)                  |       0 | `Table`, `TCat`, τ-category axioms (τ1–τ3); resurfacing; pruning; supporting; auspicious; expansion lemma (+ converse). Sorry-free. STANDALONE — not imported by any downstream file (strictification scaffolding, mirrors the book: §1.49 feeds the §1.4(10) free-τ-cat and §1.74 representation, then is set aside). |

### §1.51–§1.55  Regular categories, capitalization, Henkin

| File          | Sections              | Sorries | Main results / status                                                                                                          |
| ------------- | --------------------- | ------- | ------------------------------------------------------------------------------------------------------------------------------ |
| `S1_51.lean`  | §1.51, §1.512         |       0 | `Subobject`, `Allows`, `Image`, `Cover`; cover factorization. Sorry-free.                                                     |
| `S1_52.lean`  | §1.52–§1.525          |       0 | `RegularCategory`, `PreRegularCategory`, `WellSupported`, `WellPointed`, `Capital`; `cover_epi`, `prod_fst_cover`. Sorry-free. |
| `S1_53.lean`  | §1.531–§1.532         |       0 | Σ reflects covers (slice lemma); pullback square for B×A₁→B×A₂. Sorry-free.                                                   |
| `S1_54.lean`  | §1.541–§1.545         |       1 | `IsRelativeCapitalization`; `slice_embedding_separates` (§1.544, sorry-free). **1 sorry: `capitalization_lemma` (§1.543)** — requires transfinite directed colimit of categories (no Ordinal/well-founded recursion on types in this mathlib-free setting). |
| `S1_55.lean`  | §1.55                 |       0 | Henkin-Lubkin representation (faithful embedding via covariant hom-functors); `cayley_faithful`. Sorry-free. NOTE: faithful only; exact representation (needed for §1.551 Horn metatheorem) is deferred — depends on §1.543. |

### §1.56–§1.59  Relations, choice, bicartesian, abelian

| File          | Sections              | Sorries | Main results / status                                                                                                                                   |
| ------------- | --------------------- | ------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `S1_56.lean`  | §1.56–§1.569          |       8 | `BinRel`, relation composition `⊚`, reciprocal `°`, intersection `⊓`, `RelLe`; graph, `Entire`, `Simple`, `Map`; modular identity; cover↔entire; cover_is_coequalizer; ⊚-associativity; `cover⊥mono`; `relLe_of_cover_factor`. 8 sorries: (R⊚S)° = S°⊚R°; (R⊚S)⊚T ≤ R⊚(S⊚T) (modular); Horn sentence reflection (§1.563, requires capitalization); regular_of_compose_assoc; constant-image subterminator; reciprocal_comp_le (×2); one more. Blocker: covers-are-epic positivity (epic⟹cover needs §1.56 relation-level argument). |
| `S1_57.lean`  | §1.57                 |       0 | `ChoiceObject`, `ACRegularCategory`; projective; every morphism factors as left-inv ∘ mono. Sorry-free.                                                |
| `S1_58.lean`  | §1.58–§1.59           |       4 | `BicartesianCategory` (coterminator, coproduct, coequalizer, pushout); half-additive; middle-two interchange. 4 sorries: details of middle-two interchange + coproduct from coequalizer+product.     |
| `S1_59.lean`  | §1.591–§1.599         |       1 | Abelian: kernel/cokernel; normal subobject; `EffectiveRegular` ↔ abelian; exact sequences stated. 1 sorry: abelian ↔ effective+regular+additive.       |

### §1.6–§1.66  Pre-logoi, positive pre-logoi, pre-topoi

| File          | Sections              | Sorries | Main results / status                                                                                                               |
| ------------- | --------------------- | ------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| `S1_60.lean`  | §1.6, §1.61, §1.612–§1.614 | 2  | `PreLogos` (bottom, unions, dist lattice); 0 as coterminator; distributive ↔ f# distributes over unions; poset is pre-logos ↔ dist lattice. 2 sorries: coterminator uniqueness and f#-distributivity proof. |
| `S1_61.lean`  | §1.61                 |       3 | 0 as coterminator (from bottom); Heyting-style construction; distributive lattice → pre-logos. 3 sorries: full invImage-preserves-union and distributive→PreLogos assembly.          |
| `S1_62.lean`  | §1.62–§1.635          |       6 | Pasting lemma (union = pushout of intersection); positive pre-logos; generating set; pre-filter; representation theorem. 6 sorries: pushout construction from subobject union; Cover instances; positivity for covers; pre-filter `T_F`; representation axioms.          |
| `S1_64.lean`  | §1.63–§1.65, §1.644–§1.652 | 12 | Slice of pre-logos is pre-logos; complemented subobjects; `BooleanPreLogos`; `PreTopos`; `amalgamation_lemma` (§1.651); covers=epics in pre-topos (§1.652); ultraproduct (§1.644). 12 sorries: most infrastructure including amalgamation and pre-topos cover/epic equivalence. |
| `S1_65.lean`  | §1.655–§1.656         |       3 | `PreToposFunctor`; bicartesian representation criterion (§1.655): three steps each sorry with documented blocker (step i needs amalgamation sorry in S1_64; step ii uses S1_43 sorry; step iii uses S1_64). Abelian functor analogue noted (§1.656). 3 sorries.              |

### §1.7–§1.78  Logoi, Heyting algebras, locales

| File          | Sections              | Sorries | Main results / status                                                                                                         |
| ------------- | --------------------- | ------- | ----------------------------------------------------------------------------------------------------------------------------- |
| `S1_70.lean`  | §1.7–§1.712, §1.722   |       5 | `Logos` class (right adjoint image f##); §1.711 logos⟹pre-logos; §1.712 locally complete; Heyting algebra on Sub(A). 5 sorries: `logos_implies_preLogos` construction (missing PreLogos fields = known build blocker); locally-complete instance.           |
| `S1_72.lean`  | §1.72–§1.734          |      12 | `HeytingAlgebra`; §1.725 equational theory; §1.726 derived equations; §1.727 negation; §1.728 law of excluded middle; §1.73 filter/quotient; §1.733 focal logos. 12 sorries: derivation of Heyting equations (modus ponens for ⊥, distributivity over sup, De Morgan, etc.). |
| `S1_74.lean`  | §1.744–§1.746         |       0 | Domination (§1.744: onto-on-objects + left-full functor); §1.745 every cat dominated by a tree; §1.746 countable → dominated by binary tree. Sorry-free. NOTE: §1.74 geometric representation theorem proper (§1.741–§1.743, §1.747–§1.74(10)) is MISSING — irreducibly topological (Lazard sheaves, Cantor space, Freyd curve). |
| `S1_75.lean`  | §1.751                |       1 | `Atom`; atomically-based logos; atomless logos. 1 sorry: "atomically based ⟹ boolean" (needs Stone topology). §1.75 Stone representation theorem proper is MISSING — requires Stone spaces and stalk/sheaf functor. |
| `S1_77.lean`  | §1.77–§1.787          |      11 | Transitive closure R^t; transitive-reflexive closure R*; ω-transitive logos; equivalence closure R^E; relational quotient R/S; §1.783 (R/S₁)/S₂ = R/(S₁S₂); §1.787 R̄ = R*. 11 sorries: closure-under-composition proofs; R* iteration equations; quotient lattice axioms.   |

### §1.8  Adjoint functors

| File          | Sections              | Sorries | Main results / status                                                                               |
| ------------- | --------------------- | ------- | --------------------------------------------------------------------------------------------------- |
| `S1_8.lean`   | §1.81, §1.813, §1.815, §1.816 | 1 | `Adjunction` (φ, ψ, naturality); reflective/coreflective subcategory; closure operation. 1 sorry: reflection axiom uniqueness in the coreflective case. |
| `S1_81.lean`  | §1.817–§1.818         |       0 | Representability for adjoints; contravariant adjunctions on right/left. Sorry-free.                 |
| `S1_82.lean`  | §1.82–§1.838          |       3 | Diagonal functor Δ; limits/colimits as cones; complete/cocomplete; continuous functor; weak limits; pre-adjoint; General/Special Adjoint Functor Theorems (stated). 3 sorries: completeness from equalizers+products; GAFT; SAFT. All three are deep infrastructure.  |
| `S1_84.lean`  | §1.84–§1.846          |       2 | Grothendieck topos (Giraud definition); well-powered; locally complete; coproducts/coequalizers in Rel(E). 2 sorries: well-powered instance + locally-complete instance (both need `logos_implies_preLogos` from S1_70 build blocker). |
| `S1_85.lean`  | §1.85–§1.859          |       6 | `HasExponentials`; poset exponential ↔ Heyting arrow; B^A as bifunctor (§1.853); exponential ideal (§1.857); Kuratowski interior; Lawvere-Tierney closure; baseable objects. 6 sorries: curry_inj; bifunctor variance; ideal/closure axioms.                       |

### §1.9–§1.98  Topoi

| File          | Sections              | Sorries | Main results / status                                                                                                                      |
| ------------- | --------------------- | ------- | ------------------------------------------------------------------------------------------------------------------------------------------ |
| `S1_9.lean`   | §1.9, §1.912–§1.913   |       1 | `BinRel`; `relPullback`; power-object `[C]`; `HasSubobjectClassifier` (Ω, t, classify, classify_sq); `Topos`; covers=epics in topos. 1 sorry in relPullback jointly-monic proof. |
| `S1_91.lean`  | §1.913–§1.919, §1.91(10) | 2   | Subobjects as equalizers (§1.913); omegaMeet (∧); heytingDoubleArrow (§1.914); `omega_monic_endo_is_involution` (§1.919); minimal topos definition. 2 sorries: §1.919 involution (needs classify-uniqueness axiom) and §1.91(10) minimal topos construction.           |
| `S1_92.lean`  | §1.92–§1.926          |       7 | `singletonMapCat` Δ₁: B→[B]; topos is exponential (§1.92); `powerMapCov` [f]:A→B→[A]→[B]; Lawvere definition (§1.921); Ω^(−) contravariant; B^A subobject of [A×B] (§1.923). 7 sorries: `singletonMapCat_monic` (needs classify pullback property); `powerMapCov` functoriality; §1.921 partial map classifier; §1.923 exp subobject embedding. Blocker: **powerMapCov/classify pullback**. |
| `S1_94.lean`  | §1.94–§1.94(10)       |       9 | Internally defined intersection ∩F (§1.94); name of A' (§1.942); ∩F properties (§1.943); strict coterminator (§1.944); topos is regular (§1.945); topos is logos (§1.946); transitive logos (§1.947); internally defined union ∪F (§1.949). 9 sorries: most require §1.54 capitalization or §1.943 glb + classify axiom. |
| `S1_95.lean`  | §1.951–§1.966         |      12 | Topos is effective (§1.951); topos is positive (§1.952); has coequalizers (§1.954); bicartesian (§1.955); injective objects (§1.961); Ω^A is injective (§1.962); value-based (§1.964); cogenerates (§1.965); progenitor (§1.966). 12 sorries: all major topos structure proofs — effective/positive/bicartesian all require internal Ω machinery not yet assembled. |
| `S1_97.lean`  | §1.97–§1.98(14)       |      16 | `BooleanTopos`; small objects (§1.971); IAC (§1.973); AC↔IAC+proj-1 (§1.974); `HasNaturalNumbersObject` (§1.98); primRec (§1.983); N≅1+N (§1.985); Peano property (§1.987); bicartesian characterization (§1.98(10–11)); free A-action (§1.98(12–14)). 16 sorries: AC↔IAC; NNO iterate; NNO characterization; free A-action characterization and existence. Blockers: §1.95 positivity sorries (topos bicartesian) and list-object construction. |

---

## Chapter 2

### §2.1  Allegories

| File        | Sections                          | Sorries | Main results / status                                                                                    |
| ----------- | --------------------------------- | ------- | -------------------------------------------------------------------------------------------------------- |
| `S2_1.lean` | §2.11–§2.16                       |       0 | `Allegory` typeclass (°, ∩, modular identity, semi-distributivity); reflexive/symmetric/transitive/coreflexive; domain; Entire/Simple/Map; Tabulates; tabular allegory; unitary allegory; pre-tabular; effective; semi-simple. `Rel(C)` is an allegory (§2.111). Sorry-free. |

### §2.2–§2.228  Distributive allegories

| File           | Sections               | Sorries | Main results / status                                                                                  |
| -------------- | ---------------------- | ------- | ------------------------------------------------------------------------------------------------------ |
| `S2_2.lean`    | §2.21–§2.223           |       1 | `DistributiveAllegory` (zero, union, distributivity); positive; locally complete; globally complete. 1 sorry: coproduct-five-equations to universal mediator proof.   |
| `S2_22.lean`   | §2.228                 |       2 | `UnionAllegory` (union distributes with comp but not inter); tabular+union ⟹ distributive (§2.228a); semi-simple+union ⟹ distributive (§2.228b); counterexample (§2.228c). 2 sorries: modular tabulation identity in the tabular case; semi-simple distributivity.     |

### §2.3  Division allegories

| File        | Sections               | Sorries | Main results / status                                                                              |
| ----------- | ---------------------- | ------- | -------------------------------------------------------------------------------------------------- |
| `S2_3.lean` | §2.31, §2.331, §2.35   |       2 | `DivisionAllegory` (R/S); symmetric division R/ₛS; straight morphism; simple part; le_div_iff; div_comp_le. 2 sorries: symmetric division transitivity (requires modularity chain) and straight-implies-simple part exists.   |

### §2.4  Power allegories

| File          | Sections               | Sorries | Main results / status                                                                                                         |
| ------------- | ---------------------- | ------- | ----------------------------------------------------------------------------------------------------------------------------- |
| `S2_4.lean`   | §2.41–§2.442           |       8 | `PowerAllegory` (∋, straight, thick); `A(R)` operator; singleton map; A(f)=f≫A(1); pre-power allegory; `Thick`; §2.431 thick_iff_existential; §2.441 pre-positive allegory; §2.442 law of metonymy. 8 sorries: `A_is_map`, `A_eps_eq`, `A_unique`, `singletonMap_monic`, `A_of_map`, `simple_le_A_eps` — the power-allegory axiom manipulation machinery. Blocker: **power-allegory algebraic bookkeeping** (R/ₛ, straightness, and domain formula §2.3571). |
| `S2_43.lean`  | §2.435–§2.436          |       0 | Cantor diagonal theorem in algebraic form: §2.436 thick endomorphism forces 1=𝟘 in one-object pre-power allegory; §2.435 connected division allegory with thick endomorphism ≃ trivial allegory. Sorry-free.                 |

### §2.5  Quotient allegories

| File        | Sections                | Sorries | Main results / status                                                                                                      |
| ----------- | ----------------------- | ------- | -------------------------------------------------------------------------------------------------------------------------- |
| `S2_5.lean` | §2.5–§2.542             |       7 | `Congruence`; `QuotientAllegory`; boolean quotient (§2.521); closed quotient (§2.522); amenable congruence (§2.53); amenable quotient of division allegory is division (§2.536); every topos admits a faithful bicartesian representation (§2.542). 7 sorries: quotient construction (recip/inter/comp-congr); amenable → division quotient; §2.542 topos representation. Blockers: **§2.416 splitting lemma** and **§2.441 pre-positive allegory** (not yet discharged). |

---

## MISSING sections (no file, no stub)

| Book section(s) | Why missing                                                                                    |
| --------------- | ---------------------------------------------------------------------------------------------- |
| §1.2 (§1.21–§1.23) | Elementary category theory remarks; very terse in the book; not yet filed.                 |
| §1.46           | Dense generators / cogenerators; not yet started.                                              |
| §1.543 (transfinite iteration) | The capitalization lemma `sorry` in S1_54 covers the statement; the full proof requires ordinal-indexed well-founded recursion producing types, which is out of scope for the mathlib-free repo (Mathlib ordinals are permitted for this section per CLAUDE.md, but the transfinite CatSystem construction is not yet built). |
| §1.66           | Coherent/geometric logic and classifying topoi; not yet started.                               |
| §1.71 (logos details beyond §1.711) | Heavy internal-hom machinery; deferred until S1_70 build blocker resolved. |
| §1.74 proper (§1.741–§1.743, §1.747–§1.74(10)) | Geometric representation theorem: Lazard sheaves on ℝ, Cantor space, sobrification, Freyd curve — all require point-set topology with no basis in this repo. |
| §1.75 Stone representation theorem proper (§1.752–§1.755) | Stone space construction, stalk/sheaf functor, Cantor space — requires topology. |
| §1.76           | Micro-sheaves; requires topos/sheaf infrastructure not yet built.                              |
| §1.83 (GAFT/SAFT proofs) | General/Special Adjoint Functor Theorems stated in S1_82 with sorry; full proofs need a genuine category of sets and size/smallness reasoning. |
| §2.416          | Splitting lemmas for power allegories; prerequisite to §2.442 and §2.542.                     |

---

## Totals and keystone blockers

**60 files total.  25 sorry-free.  165 real sorries.**

### Keystone blockers (everything funnels through these)

1. **Capitalization Lemma §1.543** (`S1_54.lean`): transfinite directed colimit of
   categories. Blocks: exact Henkin representation (§1.55), Horn metatheorem (§1.563),
   topos-is-logos (§1.946), topos-is-regular (§1.945), ∩F glb (§1.943), ∩F
   preservation under representations.

2. **logos_implies_preLogos build error** (`S1_70.lean`, 5 sorries): the `Logos`→`PreLogos`
   instance is missing PreLogos fields. Blocks S1_84 (Grothendieck topos well-powered
   and locally-complete instances), and prevents logos infrastructure from propagating.

3. **classify-uniqueness axiom** (`HasSubobjectClassifier` in `S1_9.lean`): the field
   "two maps A→Ω classifying the same subobject are equal" is not yet axiomatized.
   Blocks §1.919 (monic endomorphism of Ω is involution), §1.921 partial map classifier,
   §1.923 B^A ↪ [A×B], and ultimately all of §1.94.

4. **powerMapCov/singletonMapCat_monic** (`S1_92.lean`, 7 sorries): constructing [f]
   and proving Δ₁ is monic both require the classify pullback property. Blocks §1.92,
   §1.922, §1.923, §1.924 Yoneda.

5. **amalgamation_lemma §1.651** (`S1_64.lean`, 12 sorries): pushout of two monics in
   a pre-topos. Blocks §1.652 covers=epics, §1.655 bicartesian representation criterion
   (S1_65.lean), and the full pre-topos theory.

6. **Power allegory algebraic machinery §2.41** (`S2_4.lean`, 8 sorries): A(R)∋=R and
   A_is_map rely on domain formula §2.3571 (not yet derived in S2_3). Blocks §2.412,
   §2.415, §2.442, §2.5 amenable quotient, §2.542 topos faithful representation.

7. **List-object / NNO bicartesian structure** (`S1_97.lean`, 16 sorries): free A-action
   (§1.98(13–14)) and NNO bicartesian characterization (§1.98(10)) both wait on topos
   positivity/coequalizers (§1.952–§1.955 from S1_95) being discharged.
