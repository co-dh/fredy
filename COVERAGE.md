# Book → Lean coverage audit (Freyd & Scedrov, *Categories, Allegories*)

Generated 2026-06-16 by a 10-way parallel audit of `categories-allegories.txt` against `Fredy/*.lean`.
Filename convention (`Sa_bc.lean` for §a.bc) is **not** reliably followed (e.g. §1.281 lives in `S1_39.lean`),
so status below is by **content search across all files**, not by filename.

Legend: **DONE** = faithful def/theorem, real proof · **PARTIAL** = exists but `sorry`/`:= trivial`/`: True`/materially weaker ·
**MISSING** = no declaration anywhere.

This is the master gap list. Items are the book's CAPITALIZED definitions and its numbered theorems.

---

## §1.1–1.2  Basic definitions & constructions
MISSING: §1.13 `O(Ox)=Ox` derivation · §1.14 MONOIDS as categories (+converse) · §1.15 DISCRETE CATEGORIES ·
§1.182 CONTRAVARIANT FUNCTOR + OPPOSITE CATEGORY A° · §1.1(10) ISOMORPHISM OF CATEGORIES (bijective functor) ·
§1.242 CATEGORY OF GROUPS · §1.245 PRE-ORDERING as category · §1.262 LOCAL HOMEOMORPHISMS / LAZARD SHEAVES ·
§1.263 counter-slice; POINTED SETS · §1.271 right A-SETS (M-sets) · §1.273 LEFT A-SETS ·
§1.282 uniqueness up to iso of idempotent splittings · §1.283 STRONGLY CONNECTED category · §1.284 PREFUNCTOR.
PARTIAL: §1.17 GROUPOID/GROUP/uniqueness-of-inverse/`x⁻¹` (only IsIso/HasLeftInv exist) ·
§1.243 Founded/ConcreteCat/UnderlyingSetFunctor (only ForgetfulFunctor) ·
§1.27 FunctorCat as a Cat instance (NaturalTransformation exists, no id/comp) ·
§1.272 Cayley completeness metatheorem · §1.28 idempotent-completion category Y//(E) · §1.281 universality of canonical splitting.

## §1.3  Equivalence of categories
MISSING: §1.31 FULL SUBCATEGORY · §1.32 three cancellation principles + conjugation-invariance ·
§1.332 contravariant Cayley C° · §1.333 functor-between-posets characterisations ·
§1.341 equinumerous iso-classes ⇒ conjugate to iso · §1.36 inflation-forgetful is full embedding ·
§1.363 "equivalent" is an equivalence relation · §1.364 equiv functor of skeletals is iso; AoC conditions (a)–(g) ·
§1.366 quotient A/K + universal property · §1.367 factorisation of equivalence functors ·
§1.371–§1.375 right-A-set / Lazard-sheaf / presheaf / sheaf-functor / T₀-ification equivalences ·
§1.381–§1.388 duality/equivalence examples · §1.395–§1.399 Q-sequence preservation theorems ·
§1.3(10)–§1.3(10)6 stable = good Q-tree metatheorem.
PARTIAL: §1.331 `reflects_leftInv_reflects_iso` proof is `trivial` · §1.362 `inflation_strong_equiv` = `True` ·
§1.363 `EquivalentCategories` def not via isomorphic inflations · §1.38 `Duality` aliased to StrongEquivalence (no contravariance) ·
§1.373 `AdjointPair` missing triangle identities · §1.389 `StoneSpace` opaque · §1.392 `SatisfiesQSequence` body `True` ·
§1.395 `complementaryQSequence` complementarity unproven.

## §1.4  Cartesian categories
MISSING: §1.413 CONTAINED + poset-of-relations · §1.414 monic ↔ subterminator in A/B · §1.425 n-ary PRODUCT ·
§1.429 equalizers split idempotents · §1.437 REPRESENTATION OF CARTESIAN CATEGORIES + thms ·
§1.438 reflects/preserves-limit theorems · §1.442 Cayley preserves pullbacks/equalizers · §1.444 HORN SENTENCE + metatheorem ·
§1.45 pullback of monic is monic · §1.451 INVERSE IMAGE f# + Sub(−) contravariant · §1.452 Sub(A) semilattice ·
§1.453 properness lemma · §1.471–§1.474 SPECIAL-Cartesian characterisations · §1.481 rational category is Cartesian ·
§1.492 SUPPORTING subsequence · §1.494 expansion lemma · §1.496 subterminator ⇒ terminator ·
§1.497 CANCELLATION LEMMA · §1.498 CANONICAL CARTESIAN STRUCTURE · §1.4(10)1 free τ-category exists ·
§1.4(11)2–6 τ/B, Δ-functors, generic point theorems · §1.4(12) TERM language + metatheorem.
PARTIAL: §1.412 `Relation` not quotiented by TableIso · §1.47 `SpecialCartesianCategory` axiom wrong placeholder ·
§1.48 `DenseMonic` = `True`, `RationalCategory` malformed · §1.49 `Table.comp` placeholder ·
§1.4(10) `FreeTCategory.isFree:True` · §1.4(11) `canonicalSlice` = identity · §1.4(11)4 `GenericPoint` is a table not a map.

## §1.5  Regular categories
MISSING: §1.51 image⊣pullback adjunction · §1.512 cover left-cancellation · §1.513 covering family ·
§1.514 jointly-epic covers · §1.521 Y^A regular · §1.534 not-well-supported ⇒ not faithful · §1.552 SPECIAL pre-regular ·
§1.561 (RS)°=S°R° · §1.562 (R∩S)T⊆RT∩ST · §1.566 every coequalizer is a cover · §1.568 Quot(A)→EquivRel(A) ·
§1.56(10) constant image is subterminator · §1.572–§1.574 recursive-function category · §1.581 bicartesian-rep preserves covers ·
§1.583 effectiveness is Horn · §1.593 abelian ↔ regular-additive-all-normal · §1.595 Ab(A) construction.
PARTIAL: §1.524 projective sufficiency criterion · §1.526 Pts not proved a representation · §1.531 A/B pre-regular not assembled ·
§1.543 `capitalization_lemma` = `sorry` · §1.55 `henkin_lubkin` only Cayley (not exact) ·
§1.551 `horn_sentence_preservation` = `True` · §1.563 `modular_identity`/`horn_*` = `sorry` ·
§1.565 `pullback_of_covers_is_pushout` = `sorry` · §1.569 `regular_of_compose_assoc` = `sorry` ·
§1.582 `image_via_coeq` = `trivial` · §1.591 HalfAdditive/Additive fields = `True` · §1.593 `IsNormalSubobject` placeholder ·
§1.594 `effective_regular_additive_is_abelian` = `trivial`.

## §1.6  Pre-logoi
MISSING: §1.621 A₁∩A₂=0 ∧ A₁∪A₂=A ⇒ A≅A₁+A₂ · §1.625 preserves-disjoint-unions ↔ representation · §1.63 A/B pre-logos ·
§1.631 complemented-of-projective is projective · §1.633 capital ↔ complemented-subterminators basis · §1.635 BOOLEAN ALGEBRA def ·
§1.636 Horn for positive pre-logoi · §1.641 boolean-rep preserves structure · §1.642 Y^A boolean ↔ groupoid ·
§1.643 H(Y) boolean ↔ discrete · §1.644 ULTRA-PRODUCT/ULTRA-POWER FUNCTOR · §1.646 special ⇒ representable in Set ·
§1.647 boolean special ↔ two-valued · §1.653 pushout monic+arb · §1.655 bicartesian-rep criterion ·
§1.658 every-object-decidable ↔ boolean · §1.659 decidable in Y^A · §1.66–§1.662 choice objects + Diaconescu.
PARTIAL: §1.611 `sorry` · §1.612 `True` · §1.613 only one direction · §1.614 `PreLogosFunctor` = `True` ·
§1.615 `True` · §1.62 `pasting_lemma` = `sorry` · §1.624 `sorry` · §1.631 `IsComplemented` weak ·
§1.634 prefilter functor not a colimit · §1.635 `prelogos_representation_theorem` = `sorry` · §1.645 `killedValues` wrong target ·
§1.648 `CompleteMeasure` = `True` · §1.651 `amalgamation_lemma` = `sorry` · §1.652 `cover_eq_epic`/`monic_eq_cocover` `sorry` ·
§1.654/§1.657 `preTopos_opposite_regular` = `True` · §1.658 `DecidableObject` commented out.

## §1.7  Logoi
MISSING (almost all): §1.71 f##=¬f(¬·) · §1.713–§1.714 Sh locally complete / alt axiom · §1.721–§1.722 subobject lattice Heyting; poset logos ↔ Heyting ·
§1.723 LOCALE · §1.724 ↔ operation · §1.725–§1.726 Heyting equational theory · §1.727 NEGATION + De Morgan ·
§1.728 EXCLUDED MIDDLE ⇒ boolean · §1.729 f# preserves → · §1.72(10)–(11) scone/retract ·
§1.731 quotient logos A/ℱ · §1.732 slice-logos capitalization · §1.733 CONNECTED obj; focal ↔ connected-projective ·
§1.734 FOCAL REPRESENTATION · §1.735 cardinality · §1.741–§1.74(10) GEOMETRIC REP THEOREM chain (DOMINATES/LEFT-FULL, trees, Freyd curve, sobrification) ·
§1.75–§1.755 STONE REP THEOREM (ATOM, ATOMICALLY BASED, ATOMLESS) · §1.76–§1.761 MICRO-SHEAVES ·
§1.77–§1.777 TRANSITIVE CLOSURE R^t/R*, TRANSITIVE LOGOS, ω-TRANSITIVE, EQUIVALENCE CLOSURE, E-STANDARD ·
§1.78–§1.787 relational quotient R/S and all laws (R̄=R*).
PARTIAL: §1.7 `Logos` lattice cond split off · §1.711 `logos_implies_preLogos` all fields `sorry` ·
§1.712 `locallyComplete_*` = `sorry` · §1.72 `HeytingAlgebra` adjunction orientation · §1.73 `repFilter` predicate only;
`faithful_iff_trivial_filter` converse `sorry` · §1.733 `Coprime` misformulated; `FocalLogos` depends on it ·
§1.734 `focal_representation_theorem` = `True`+`sorry` · §1.74 `geometric_representation_theorem` = `True`+`sorry`.

## §1.8  Adjoint functors, Grothendieck topoi
MISSING: §1.817 representability ↔ left adjoint · §1.82 DIAGONAL FUNCTOR Δ:B→B^D · §1.822 LIMITS/COLIMITS ·
§1.823 COMPLETE/COCOMPLETE · §1.825 complete ↔ equalizers+products · §1.827 CONTINUOUS/COCONTINUOUS ·
§1.828 WEAK-LIMIT/WEAKLY-COMPLETE · §1.829 weak-limit preservation · §1.82(10) PRE-LIMIT/PRE-COMPLETE ·
§1.83 PRE-ADJOINT + GENERAL ADJOINT FUNCTOR THEOREM · §1.831 UNIFORMLY CONTINUOUS + MORE GENERAL AFT ·
§1.832 POINTWISE CONTINUOUS · §1.833 PETTY-FUNCTOR · §1.834 GENERAL REPRESENTABILITY THEOREM ·
§1.835/§1.837 coterminator criteria · §1.838 WELL-POWERED · §1.83(10) COGENERATING SET + SPECIAL AFT ·
§1.84 GIRAUD DEFINITION · §1.843–§1.846 Grothendieck topos properties · §1.852 poset exponential ↔ Heyting ·
§1.853 B^A bifunctor + limit preservation · §1.854 Σ⊣Δ, Π dependent products · §1.857 EXPONENTIAL IDEAL, REPLETE SUBCATEGORY ·
§1.858 KURATOWSKI INTERIOR, LAWVERE-TIERNEY CLOSURE · §1.859 BASEABLE objects.
PARTIAL: §1.815 `ClosureOperation` omits explicit poset axioms.

## §1.9  Topoi
MISSING: §1.9 UNIVERSAL RELATION · §1.914 algebra of Ω · §1.92 SINGLETON MAP Δ1 + laws · §1.921 LAWVERE DEFINITION (partial-map classifier) ·
§1.922 Ω^(−) functor · §1.923 B^A as subobject of [A×B] · §1.926 exponential ↔ Heyting on Sub(1) · §1.93 SLICE LEMMA ·
§1.931 FUNDAMENTAL LEMMA OF TOPOI (Πf) · §1.932 double-sharp · §1.933 topos pre-regular · §1.934 PARTIAL MAPS category + classifier Ã ·
§1.935 rep into capital topos · §1.94 SUBOBJECTS NAMED BY F, ∩F · §1.941–§1.943 ∩F props, NAME OF A' · §1.947 topos is transitive logos ·
§1.949 ∪F · §1.94(10) WELL-POINTED PART, SOLVABLE TOPOS · §1.951 topos effective · §1.952 topos positive · §1.954 topos has coequalizers ·
§1.955 topos bicartesian · §1.961–§1.966 INJECTIVE/INTERNALLY INJECTIVE/VALUE-BASED/PROGENITOR/COGENERATOR ·
§1.967–§1.968 power/copower/completeness equivalences · §1.969 LAWVERE/TIERNEY Grothendieck defs · §1.971 SMALL OBJECT ·
§1.972 projective-1 ↔ progenitor · §1.973 IAC · §1.974–§1.978 AC↔IAC, ETENDUE · §1.981/§1.983 NNO iterate-pairs, primitive recursion ·
§1.985–§1.989 N=1+N, PEANO PROPERTY · §1.98(10)–§1.98(14) bicartesian NNO, A-ACTION / FREE A-ACTION.
PARTIAL: §1.9 `Topos` conflates power-object with Ω-classifier · §1.919 `omega_monic_endo_is_involution` `sorry` ·
§1.91(10) `minimal_topos_has_terminator` = `True` · §1.92 `topos_has_exponentials` `sorry` ·
§1.944/§1.945/§1.946 `topos_has_strict_coterminator`/`topos_is_regular`/`topos_is_logos` = `True`.

## §2.1–2.2  Allegories, distributive allegories
MISSING: §2.111 Rel(C) is an allegory · §2.112 R⊑RR°R · §2.12 EQUIVALENCE RELATION def · §2.122 dom universal property ·
§2.123 dom(RS)⊑domR · §2.131 RS entire ⇒ R entire · §2.132 subcategory Map(A) · §2.135 isos coincide · §2.136 simple F distributes over ∩ ·
§2.142 Rel(C) tabular · §2.143–§2.146 tabulation characterisations · §2.147 Map(A) has pullbacks/equalizers/images ·
§2.148 A=Rel(Map(A)) · §2.151–§2.152 partial-unit / unit theorems · §2.154 REPRESENTATION OF ALLEGORIES ·
§2.162–§2.167 splitting / tabular-reflection theorems · §2.212–§2.213 Rel(pre-logos) distributive; Split distributive ·
§2.215 Map positive pre-logos · §2.216 POSITIVE REFLECTION A⁺ · §2.217–§2.219 representation theorems ·
§2.221–§2.226 LOCAL/GLOBAL/SYSTEMIC COMPLETION · §2.228 tabular+∪-distributive ⇒ distributive.
PARTIAL: §2.169 `EffectiveAllegory` over-specific (requires Tabular parent; uses symm-idempotents not equiv-rels) ·
§2.214 `Coproduct` universal property unproven.

## §2.3  Division allegories
MISSING: §2.311 ∪-distributivity · §2.312 LEFT DIVISION S\R · §2.313 adjunction · §2.314 R/(S₁∪S₂)=R/S₁∩R/S₂, S\(R/T)=(S\R)/T ·
§2.315 loc-complete-distributive is division · §2.316 (a,a) Heyting · §2.32 tabular-unitary-division ↔ Map logos ·
§2.33 geometric rep · §2.331 Moerdijk · §2.34 Split(E) division · §2.341 pre-tabular embeds · §2.342 positive reflection division ·
§2.343 logos ⇒ positive effective logos · §2.351 R/R equivalence relation · §2.352–§2.353 straight ↔ cancellation ·
§2.354 R=hS factorisation · §2.355 SR straight ⇒ S straight · §2.356 S straight ⇒ R/ₛS simple · §2.357 SIMPLE PART / domain of simplicity.

## §2.4  Power allegories
MISSING: §2.412 A(R) uniqueness · §2.413 thickness from factoring · §2.415 A(f)=f·A(1) · §2.416 Grothendieck ⇒ power allegory ·
§2.42 Split(Eqv) power · §2.421 R/S=A(R)A°(S) · §2.422 equiv rels are ff° · §2.423 unit existence · §2.424 Map(Split) is topos ·
§2.431 thickness characterisation · §2.433 Split(Eqv) pre-power · §2.434 systemic completion power · §2.435 Cantor ·
§2.436 inconsistency of 1-object · §2.441 PRE-POSITIVE / WELL-JOINED · §2.442 LAW OF METONYMY · §2.443 ∋ semi-simplicity · §2.446 zero/union derivable.
PARTIAL: §2.41 `A_is_map` entireness `sorry`; `A_eps_eq` second dir `sorry` · §2.414 `topos_allegory_is_power` = `True` ·
§2.432 `effective_pre_power_is_power` = `sorry`.

## §2.5  Quotient allegories
MISSING: §2.5 QUOTIENT ALLEGORY construction (only `Congruence` exists) · §2.51 quotient tabular/unitary · §2.52 zero/union congruence ·
§2.533 R⊑S ↔ R⁺⊑S⁺ · §2.534 T⁺S⁺⊑(TS)⁺ · §2.535 refl/symm/trans preserved · §2.537 amenable quotient power ·
§2.54 coreflexive named · §2.541 transitive closure preserved · §2.55 amenable quotient complete · §2.551 locale congruence ·
§2.56 SEPARATED / DENSE · §2.563 separated-target naming · §2.56(12) ΠHₙ empty (independence of AC).
PARTIAL: §2.521 `booleanQuotientRel` not shown a congruence · §2.522 `closedQuotientRel` amenability unproven ·
§2.536 `amenableQuotientDivision` = `sorry` · §2.542 `topos_boolean_representation` = `True`.

---

## Dispatch plan (wave 1 — 10 Sonnet worktree agents, definition-focused)
Each agent owns DISJOINT files, builds `lake build Fredy.<module>`, does NOT edit `Fredy.lean` (imports merged centrally),
states book-faithful definitions/theorems, proves the easy ones, leaves correctly-stated `sorry` for the hard ones
(never weakened to `True`/`trivial`), never adds `axiom`.

1. S1_82.lean (new) — §1.82–1.83 LIMIT/COLIMIT/COMPLETE/CONTINUOUS/WELL-POWERED/COGENERATING SET/PRE-ADJOINT (+AFT stmts)
2. S1_77.lean (new) — §1.77 TRANSITIVE CLOSURE R^t,R*, TRANSITIVE/ω-TRANSITIVE LOGOS; §1.78 relational quotient R/S + laws
3. S1_72.lean (own) — §1.72 HEYTING/LOCALE/NEGATION/EXCLUDED-MIDDLE + equational laws; fix Coprime/FocalLogos
4. S1_85.lean (own) — §1.857 EXPONENTIAL IDEAL/REPLETE; §1.858 KURATOWSKI/LAWVERE-TIERNEY; §1.859 BASEABLE
5. S1_84.lean (new) — §1.84 GIRAUD DEFINITION of Grothendieck topos + §1.843–846 statements
6. S1_95.lean (new) — §1.95 topos effective/positive/bicartesian/coequalizers; §1.96 INJECTIVE/VALUE-BASED/PROGENITOR/COGENERATOR
7. S1_14.lean (new) — §1.14 MONOID-as-cat, §1.15 DISCRETE CAT, §1.17 GROUPOID/GROUP/inverse, §1.182 CONTRAVARIANT FUNCTOR+OPPOSITE, §1.1(10) CAT ISO
8. S2_3.lean (own) — §2.312 LEFT DIVISION, §2.314 division laws, §2.351 R/R equiv, §2.352–356 STRAIGHT, §2.357 SIMPLE PART
9. S2_4.lean (own) — fix §2.41 A_is_map/A_eps_eq; §2.415 A(f)=f·A(1); §2.441 PRE-POSITIVE/WELL-JOINED; §2.442 LAW OF METONYMY
10. S2_5.lean (own) — §2.5 QUOTIENT ALLEGORY, §2.521/2.522 boolean/closed quotient congruences, §2.533–535 ⁺-laws, §2.56 SEPARATED/DENSE
