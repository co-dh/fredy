# Book → Lean coverage audit (Freyd & Scedrov, *Categories, Allegories*)

Regenerated **2026-06-29** at master **0bb431b** by a 10-way parallel audit of the book
(`/home/dh/anki/typst-book/chapters/<a.b>/section-<a.b>.fixed.md`) against `Fredy/*.lean`.
Status is by **content search across all files**, not by filename (the `Sa_bc.lean` convention is
not reliably followed — e.g. §1.281 lives in `S1_39.lean`, §1.438 in `FunctorReflects.lean`).

**Legend:** **DONE** = faithful def/theorem with a real proof · **PARTIAL** = exists but materially
weaker / hypothesis-laden / a definitional stub · **MISSING** = no declaration anywhere.

**Repo health:** the repo is **sorry-free** (0 reachable `sorry`) and has **no vacuous `: True` /
`:= trivial` stubs** in the core — so every PARTIAL below is a genuine real-but-weaker proof, and
every MISSING is an honest absence (recorded as a `-- BOOK …` comment), never a false-statement-with-sorry.
The old (2026-06-16) `topos_allegory_is_power` / `topos_boolean_representation` stubs have been removed.

---

## What's left — prioritized

The headline results are **done**: §1.543 capitalization, §1.55 Henkin, §1.635 pre-logos
representation, §1.9 topos theory (incl. NNO/list-object), §1.59 abelian (five/snake lemma),
§2.148/§2.16x reflections, §2.216/§2.217 positive reflection, and **§2.218** (positive *and* general
distributive: `tabular_repr_in_power_of_sets` / `_distributive`). What remains:

**Tier 1 — large unbuilt infrastructure**
- **§1.10 Sconing** — entirely unformalized (`S1_10.lean` = comments only, 0 declarations).
- **§1.3 sheaf/equivalence tail** — §1.371–§1.375 (presheaf / germ / stalk / associated-sheaf / T₀),
  §1.381–§1.388 duality examples, §1.3(10) "stable = good Q-tree" metatheorem.
- **§2.5 quotient-allegory type** — `Congruence`/`largest` algebra is done, but no `QuotAllegory`
  type is built, which blocks §2.51 / §2.536 / §2.537 / §2.55.
- **§2.4 power-allegory tail** — §2.416 progenitor ∋-construction (only monic half), §2.42 splitting
  lemma, §2.418 realizability topos, §2.433–§2.435.

**Tier 2 — topology / sheaf walls**
- **§1.74 geometric representation**, **§1.75 Stone (§1.754)**, **§2.331(iv)**, **§2.227 locale
  representation**, §1.76 micro-sheaves. All need point-set-topology / sheaf infra absent by design.

**Tier 3 — isolated residuals (infra present, one hypothesis to discharge)**
- **§1.636** Horn metatheorem for positive pre-logoi — proved in transfer form; takes the
  `StalkResidual`/`PushPowResidual` reflection as a hypothesis (2 colimit atoms + image-reflection
  not discharged unconditionally).
- **§1.55** exact (cover-preserving) Henkin — current witness separates maps but isn't shown to
  preserve covers.
- **§1.637** special pre-logos converse (the hard `iff`, explicit TODO).
- **§2.225 / §2.226** union-of-semisimple ⟹ semisimple / systemic-completion generating-set-unit.
- **§1.592 / §1.598** small-abelian faithful exact rep into Ab / normal-characterization converse.

**Tier 4 — optional / low value**
- **§1.4(10)–(12) free τ-category / term model** — confirmed **not used anywhere else in the book**
  (the τ-category is confined to §1.4; every "τ" elsewhere is the OCR rendering of the functor "T").
  Safe to skip. `S1_49.lean` is imported by nothing.
- §1.398 Q-trees; model/example items (§1.915–918, §1.948, §1.953, §1.572–574, §2.155–158); basic
  Ch1 definitions (monoids-as-categories, discrete categories, M-sets, full subcategory, …).

---

## §1.1  Basic definitions

DONE: CATEGORY (`Cat`, S1_1:9) · §1.13 IDENTITY six-way equiv (`isIdentity_iff_*`, S1_13) · §1.17
LEFT/RIGHT-INVERTIBLE, ISO, INVERSE-uniqueness, GROUPOID, GROUP (S1_14:76–136) · §1.18 FUNCTOR (S1_18:57) ·
§1.181 preserves-iso + F(x⁻¹)=(Fx)⁻¹ (S1_18:121–157) · §1.182 CONTRAVARIANT FUNCTOR + OPPOSITE (S1_18:179,
S1_14:151) · §1.19 |A| id-morphisms (S1_18:208) · §1.1(10) ISO OF CATEGORIES (`CatIso`, S1_14:182).
PARTIAL: §1.14 MONOID↔category (faithful, converse characterization unproven, S1_14:25) · §1.15 DISCRETE
(converse "□x=x ⟹ from a set" not a theorem, S1_14:55).
MISSING: §1.11 ESSENTIALLY ALGEBRAIC THEORY · §1.12 directed-equality remark · §1.16 □x=x ⟹ disjoint union of monoids.

## §1.2  Basic examples and constructions

DONE: §1.21/§1.22 SOURCE-TARGET PREDICATE + category-from-predicate (`FoundingData`, S1_35:83) · §1.241 𝒮
(`setCat`) · §1.242 GROUPS · §1.243 FOUNDED/FORGETFUL/CONCRETE/UNDERLYING-SET (S1_35) · §1.245 PRE-ORDERING ·
§1.26 SLICE A/B (`Over`, S1_26) · §1.263 pointed/counter-slice · §1.27 FUNCTOR CATEGORY 𝒮^A + NAT TRANS
(S1_27) · §1.273 LEFT A-SET · §1.274 NATURAL EQUIVALENCE.
PARTIAL: §1.271 RIGHT A-SET / M-SETS (↔functor A→𝒮 unproven) · §1.272 CAYLEY (faithfulness real, completeness
metatheorem not formalized) · §1.28/§1.281 IDEMPOTENT / SPLITS (`SplitIdempotent`; Split(𝓔) construction +
universal property absent) · §1.283 STRONGLY CONNECTED · §1.284 PRE-FUNCTOR.
MISSING: §1.24/§1.25/§1.251 presentations/notation · §1.261/§1.262 indexed families / LAZARD SHEAVES (topology) ·
§1.282 uniqueness of splitting · §1.27 SMALL-CATEGORY predicate, CONJUGATE functor F^η.

## §1.3  Equivalence of categories

DONE: §1.31 EMBEDDING/FULL/REP-IMAGE/EQUIVALENCE-FUNCTOR/FULL-SUBCATEGORY (S1_31) · §1.32 conjugation-
invariance + composition + cancellation + STRONG EQUIVALENCE · §1.33 FAITHFUL + reflects-leftInv⟹iso ·
§1.331/§1.332 contravariant Cayley faithful + combined-reflects-leftInv · §1.333 poset-functor characterizations ·
§1.34/§1.341 ISOMORPHIC equiv-rel + equinumerous⟹(AC)conjugate · §1.35 FORGETFUL/FOUNDED/CONCRETE · §1.36
INFLATION + cross-section strong-equiv · §1.361/§1.366/§1.367 factor-through-inflation / EQUIVALENCE KERNEL /
A→A/K universal-property · §1.363/§1.364 EQUIVALENT/SKELETAL defs · §1.38 DUALITY · §1.392/§1.395–§1.399 Q-SEQUENCE
+ satisfaction + diagonal-fill + preserve/reflect · §1.373 ADJOINT defs.
PARTIAL: §1.32 full-cancellation (only "G full on F-images"; book's unqualified form is false) · §1.389 STONE
SPACE (`opaque` placeholder) · §1.396 `DiagonalFillable` (vacuous `→True`, superseded).
MISSING: §1.32/§1.362 AC⟺equiv-functor-half-strong-equiv · §1.363 "equivalent" equiv-relation + bridge ·
§1.364 equiv-of-skeletals-is-iso, list (a)–(g)⟺AC · §1.365 every-cat≃skeletal · **§1.371–§1.375** 𝒮↓B≃𝒮^B,
Lazard-sheaves, PRESHEAF/GERM/STALK/ASSOC-SHEAF S, S⊣Γ*, T₀-reflection · **§1.381–§1.388** duality/equivalence
examples · §1.398 Q-TREE def + satisfaction · **§1.3(10)1–6** stable=good-Q-tree metatheorem.

## §1.4  Cartesian categories

DONE: §1.41 MONIC-PAIR/TABLE/RELATION/SUBOBJECT/SUBTERMINATOR · §1.413 CONTAINED order · §1.414 monic⇔subterminal-
in-A/B · §1.421–§1.429 TERMINATOR/PRODUCT/indexed-product/EQUALIZER/idempotent-split · §1.43–§1.435 CARTESIAN +
PULLBACK + three lemmas · §1.437 REPRESENTATION + preserves-pb · §1.438 reflects-eq⟹reflects-iso, iso-reflecting+
eq-pres⟹faithful (`FunctorReflects`) · §1.44 Σ-forgetful-universal · §1.441/§1.442 A/B-pullbacks, Cayley
preserve/reflect, representables collectively faithful, REPRESENTABLE FUNCTOR · §1.444 HORN SENTENCE + metatheorem ·
§1.45 pb-transfer-monics · §1.451/§1.452 INVERSE IMAGE f# / SEMILATTICE · §1.453 pb-faithful⇔properness · §1.454
LEVEL/DIAGONAL · §1.462/§1.464 αmonic⇔pointwise / YONEDA · §1.47/§1.471–§1.474 SPECIAL + characterizations · §1.48
DENSE CLASS/Fraction · §1.49/§1.491–§1.498/§1.49(10) τ-CATEGORY core (SHORT-COLUMN, Table.comp, SUPPORTING/PRUNE,
RESURFACING, CANCELLATION, CANONICAL CARTESIAN assoc/unit) · §1.4(10)/§1.4(11) τ-FUNCTOR / Σ-functor.
PARTIAL: §1.414 poset-iso Sub≅Val · §1.426 full poset-iso Rel≅Sub(A×B) (deferred §1.56) · §1.438 third claim
(only `isIso_of_two_*`) · §1.44 Δ not a named functor · **§1.48/§1.481 RATIONAL CATEGORY** A[D⁻¹] (well-def/
universal/cartesian-pres are STRUCTURE FIELDS, not constructed; TODO) · §1.463/§1.465 Yoneda partial · §1.4(10)
WELL-MADE-PART/CANONICAL-SLICE/GENERIC-POINT/FREE-τ-CATEGORY/AUSPICIOUS — definitional stubs (`:=tab`/`:=τ`/`:=idTable`).
MISSING: §1.411/§1.415/§1.422/§1.424/§1.427/§1.436/§1.461/§1.475 examples · §1.439 preserves-pb⟹preserves-eq ·
§1.443 universal-sentence⟹Set · §1.493/§1.495/§1.499 diversions · **§1.4(10)1–§1.4(12)2** free-τ-category / slice-τ /
generic-point-generates / Γ-universal / POINT+TERM defs / METATHEOREM / model P — all `-- BOOK …: TODO` in S1_49,
no declarations. *(Tier-4: not used downstream — see top.)*

## §1.5  Regular categories / capitalization

DONE: §1.51 ALLOWS/IMAGE/∃_f⊣f# · §1.511 reflect-images · §1.512 COVER + monic-cover-iso · §1.514 EPIC · §1.52
REGULAR/PRE-REGULAR + PTC + REPRESENTATION · §1.521 𝒮^𝒜 regular · §1.522/§1.523 SUPPORT/WELL-SUPPORTED/WELL-POINTED ·
§1.524 PROJECTIVE · §1.525 CAPITAL · §1.526 I=(1,−) rep · §1.53/§1.531/§1.532 A/B-pre-regular, Σ-reflects-covers,
(B×−)-pullback · §1.533/§1.534 Δ-faithful⇔well-supported · **§1.543 CAPITALIZATION LEMMA** (`capitalization_lemma`,
`_regular`, `_regular_positive`) · §1.544 inflation/strict-cancellation · §1.545 RELATIVE CAPITALIZATION · §1.546
transfinite well-ordered-union · §1.547 choice-free rational-category · §1.55 HENKIN-LUBKIN (`henkin_lubkin`) ·
§1.552 special pre-regular · §1.56–§1.56(11) calculus of relations (RECIPROCAL, GRAPH, MODULAR IDENTITY, ENTIRE/
SIMPLE/MAP, PUSHOUT, cover⟺coequalizer, EFFECTIVE, comp-assoc⟺regular, projective⟺entire-contains-map) · §1.57/§1.571
CHOICE/AC-REGULAR · §1.58–§1.583 BICARTESIAN/image-via-coeq/effectiveness · §1.59 abelian cluster (zero/kernel/
cokernel/abelian⟺normal/A(𝒜)-abelian/EXACT/FIVE+SNAKE LEMMA).
PARTIAL: §1.541–§1.542 abstract capitalization framework (realized concretely, not abstracted) · **§1.55 exact
(cover-preserving) Henkin** (witness separates maps, cover-pres conditional) · §1.551/§1.563/§1.564 regular/relational
Horn-metatheorem corollaries (hypothesis-laden) · §1.592 small-abelian↪Ab exact rep (interface hypothetical) · §1.598
normal+kernels/cokernels⟹abelian converse.
MISSING: §1.513 covering-FAMILY predicate · §1.568 Quot(A)→equiv-rels functor · §1.572–§1.574 R/P recursive
categories · §1.584–§1.587 cocartesian-slice/Lazard/diophantine · §1.596 A(𝒮^𝒜) · §1.59(10) modular-lattice Galois.

## §1.6  Pre-logoi

DONE: §1.6/§1.611 PRE-LOGOS + alt-def · §1.61 map-to-0-iso/degenerate · §1.612 DISTRIBUTIVE LATTICE + f#-pres-
union⟺distributive · §1.613 poset-cartesian⟺semilattice · §1.614 REP OF PRE-LOGOI · §1.615 union=image(A₁+A₂→A) ·
§1.616 Rel distrib-lattice + relational laws · §1.62 PASTING LEMMA · §1.621 disjoint-cover⟹coproduct · §1.623
POSITIVE PRE-LOGOS + DisjointBinaryCoproduct · §1.624 decompose f:A→B₁+B₂ · **§1.63** capital-positive faithful-rep ·
§1.631 COMPLEMENTED SUBOBJECT + projectivity · §1.632 GENERATING SET/BASIS · §1.633 capital⟺complemented-subterms-
projective+basis · §1.634 PRE-FILTER/FILTER + T_F preserves prod/pb/img/covers + pres-disjoint-unions⟺unionPrime ·
**§1.635 REPRESENTATION THEOREM** (ultrafilter-stalk family, `exists_ultrafilter_extending`, `stalk_separates`) · §1.64
BOOLEAN PRE-LOGOS · §1.65 PRE-TOPOS · §1.651 AMALGAMATION · §1.652/§1.653 covers=epics / pushout-of-monic · §1.655
PreToposFunctor bicartesian-rep · §1.657/§1.658 cocartesian⟺min-equiv / DECIDABLE⟺boolean · §1.66/§1.661/§1.662
choice objects + Diaconescu (choice⟺boolean).
PARTIAL: §1.615 finite-Horn⟺bicart-is-prelogos · §1.635 in-file `prelogos_representation_theorem` is only the weak
Henkin functor · **§1.636 Horn metatheorem for positive pre-logoi** (transfer form; takes StalkResidual hypothesis) ·
§1.637 SPECIAL PRE-LOGOS (forward only; converse iff is TODO) · §1.644 ULTRA-PRODUCT functor · §1.645 Kel(T)/PROP ·
§1.646 representation646 faithful properness-reflecting functor (no structure-pres) · §1.648 COMPLETE/ATOMIC MEASURE.
MISSING: §1.625 T-rep⟺preserves-disjoint-unions (stub removed) · §1.638 S^A special⟺strongly-connected (needs S^A
infra) · §1.639 R/P recursive · §1.641–§1.643 rep-preserves-boolean / S^A-boolean⟺groupoid / LH(Y)-boolean⟺discrete ·
§1.647 boolean-special⟺two-valued · §1.659 S^A-decidable⟺T(x)-monic · §1.631 complement-uniqueness-as-subobject.

## §1.7  Logoi

DONE: §1.7 LOGOS · §1.71 boolean f##=¬f(¬A') · §1.711 logos⟹pre-logos · §1.712 LOCALLY COMPLETE+union-pres⟹logos ·
§1.72 HEYTING ALGEBRA + is-logos · §1.722 poset-logos⟺Heyting · §1.723 LOCALE + is-Heyting (`Frame`/`himp_adjunction`) ·
§1.727 NEGATION laws · §1.728 LEM⟹Boolean · §1.733 COPRIME/CONNECTED/FOCAL + focal⟺connected-projective · §1.77 TRANS/
TRC closures + TRANSITIVE LOGOS · §1.772 σ-TRANSITIVE · §1.775 EQUIVALENCE CLOSURE/E-STANDARD · §1.78–§1.787 RELATIONAL
QUOTIENT R/S + R/f=Rf° + assoc + exists-in-logos + R̄=R*.
PARTIAL: §1.721 Sub(A)-Heyting (thin case only) · §1.724 double-arrow · §1.726 derived →-equations · §1.73 ℱ(T)
filter (`faithful_iff_trivial_filter` missing) · §1.771 R†=⋃Rⁿ.
MISSING: §1.713 𝒮^A/ℋ(Y) loc-complete · §1.725 HA equational theory · §1.729 f#-preserves-arrow · §1.72(10)/(11) HA
scone · §1.731/§1.732 A/ℱ quotient / logos-capitalization · §1.734/§1.735 FOCAL REPRESENTATION · **§1.74 GEOMETRIC
REPRESENTATION** (§1.744 Dominates def done; theorem missing — TOPOLOGY WALL) · **§1.75 STONE REPRESENTATION** (§1.751
ATOM/ATOMLESS + atomically-based⟹boolean done; §1.752–§1.755 incl §1.754 WALL) · §1.76 MICRO-SHEAVES · §1.773/§1.774/
§1.776/§1.777 · §1.781/§1.785.

## §1.8  Adjoints, Grothendieck topoi, exponentials

DONE: §1.81 ADJOINT PAIR + unit/counit/triangles · §1.813/§1.816 REFLECTIVE/COREFLECTIVE · §1.815 CLOSURE OPERATION ·
§1.817 representability⟺left-adjoint · §1.818 ADJOINT-ON-RIGHT/LEFT · §1.821–§1.823 LIMITS/COLIMITS/COMPLETE · §1.825
complete⟺eq+prod · §1.827–§1.829 CONTINUOUS/WEAK-LIMIT · §1.82(10) PRE-LIMIT · §1.83 PRE-ADJOINT + GENERAL ADJOINT
FUNCTOR THEOREM · §1.831 MORE-GENERAL-AFT · §1.834 GENERAL REPRESENTABILITY · §1.835/§1.837 coterminator/precocomplete ·
§1.83(10)/(11) COGENERATING SET + SPECIAL-AFT + duals · §1.84 GIRAUD def · §1.843/§1.844 well-(co)powered / loc-complete ·
§1.845/§1.846 coproducts/coequalizer-in-Rel(E) · §1.85 EXPONENTIAL CATEGORY + eval/curry · §1.852 poset-exp⟺meets+Heyting ·
§1.854 Σ⊣Δ/Π/Δ⊣Π · §1.857 EXPONENTIAL IDEAL/REPLETE · §1.858 KURATOWSKI/LAWVERE-TIERNEY · §1.859 BASEABLE.
PARTIAL: §1.832 PointwiseContinuous · §1.833 PettyFunctor · §1.838 WELL-POWERED (minimal-subobject embedded in SAFT) ·
§1.853 B^A bifunctor (contravariant deferred §1.95; identity family missing).
MISSING: §1.811/§1.812 poset-adjoint/free · §1.814 fullness⟺idempotent-reflection · §1.824 intersection-as-limit ·
§1.839 cardinality · §1.841/§1.842/§1.847 Giraud examples / graphing-functor adjoint (needs Rel(E) as Cat) · §1.851/
§1.855/§1.856 exp examples / Π-construction / slice-counterexample.

## §1.9  Toposes  *(very heavily and faithfully formalized)*

DONE: §1.9 UNIVERSAL-RELATION/POWER-OBJECT/TOPOS · §1.911–§1.914 Rel(−,B)≃(−,[B]) / Ω / subobjects-are-equalizers /
Ω-Heyting · §1.919 monic-endo-Ω involution · §1.91(10) terminator · §1.92/§1.921/§1.922/§1.923 SINGLETON / topos-
exponential / [B]≅Ω^B / partial-map-classifier / B^A-subobject · §1.926 Sub(1)-Heyting · §1.93 SLICE LEMMA (`overTopos`) ·
§1.931 FUNDAMENTAL LEMMA · §1.932 double-sharp · §1.933 pre-regular · §1.934 PARTIAL MAPS + classifier Ã · §1.94/§1.942/
§1.943 ∩F internal intersection + NAME-OF + glb · §1.944 strict coterminator · §1.945 regular(images) · §1.946 logos ·
§1.947 transitive-logos(RTC) · §1.94(10) WELL-POINTED PART/SOLVABLE · §1.95/§1.951/§1.952/§1.954/§1.955 pre-topos/effective/
positive/coequalizers/bicartesian · §1.961–§1.966 INJECTIVE/VALUE-BASED/COGENERATES/PROGENITOR · §1.967/§1.968 powers⟺
copowers⟹loc-complete / complete⟺cocomplete · §1.969 LAWVERE/TIERNEY · §1.973/§1.974 IAC + AC⟺IAC∧1-projective ·
**§1.98–§1.98(14)** NNO + full recursion/Peano/free-A-action/**LIST OBJECT** (`free_action_exists`).
PARTIAL: §1.941 ∩F preserved-by-reps characterization · §1.949 ∪F lub lemmas · §1.971 small-object thm.
MISSING: §1.915–§1.918 models (𝒮^G, N-sets, 𝒮^A, ℋ(X)) · §1.924/§1.925 exp examples · §1.935 capital-topos rep · §1.948
G-sets ∩F-empty · §1.953 𝒮 A+B · §1.96(10)/(11) counterexample/Grothendieck-slice · §1.963 Ã-injective · §1.972 boolean-
logos AC · §1.975–§1.979 slice-left-inverse/AC-rep/ETENDUE/boolean-bicartesian-rep · §1.984 named arithmetic (+,×,exp).

## §1.10  Sconing  *(entirely unformalized — `S1_10.lean` = BOOK comments only, 0 declarations)*

MISSING: EXACTING def · §1.(10)1 every-cat-slice-of-exacting-Â + SCONE · §1.(10)11–14 scone structure / both adjoints ·
§1.(10)2/§1.(10)21 Heyting / 𝒮(X̂) sconing · §1.(10)3/§1.(10)31/§1.(10)32 free⟹retract-of-scone · §1.(10)4 SMALL
PROJECTIVE · §1.(10)41 connected-projective-preserves-colimits.

## §2.1  Allegories

DONE: §2.11 ALLEGORY · §2.111 Rel(C)/𝒱-valued · §2.112 R⊑RR°R · §2.12 REFLEXIVE/SYMM/TRANS/COREFLEXIVE/EQUIV + idempotence ·
§2.121–§2.124 coref-AB=A∩B / DOMAIN / Dom-laws · §2.13/§2.131 ENTIRE/SIMPLE/MAP + composition · §2.132 Map(A) + C≃Map(Rel C) ·
§2.133–§2.136 map-order / recip-inverse / isos-coincide / simple-dist-inter · §2.14/§2.141–§2.146 TABULAR + UP + uniqueness +
coref-tab + pullback-tab · §2.147 Map(A) pullbacks/eq/images/covers · §2.148 A≃Rel(Map A) · §2.15/§2.151/§2.152 PARTIAL UNIT/
UNIT/UNITARY · §2.154 REPRESENTATION OF ALLEGORIES def + `tabular_repr_in_power_of_sets` · §2.162/§2.163 split-symm-idem⟹S=R° /
coref-split⟺tabular · §2.164 Spl(𝓔) + embHom-faithful · §2.165/§2.166/§2.167 PRE-TABULAR / tabular⟺pre-tabular+coref-split /
tabular-reflection=Spl(Cor) · §2.169 EFFECTIVE · §2.16(10) SEMI-SIMPLE · §2.16(12) 𝒱-valued sets.
DONE (newly): §2.113 l-monoid one-object allegory (`LMonObj`; the modular law — the one axiom a general l-monoid lacks —
isolated as `ModularLOCMonoid`, Bool witness) · §2.222 ideal-allegory LCDA (`idealAllegory_locallyComplete`/`_faithful`;
the Downdeal allegory IS the ideal allegory) · §2.225 union-of-SS⟹SS (`semiSimple_of_iSup_semiSimple`).
PARTIAL: §2.224 GLOBAL COMPLETION Aᴴ — now a FAITHFUL LCDA REPRESENTATION (`globalCat`/`globalAllegory`/
`globalDistributiveAllegory`/`globalLCDA`/`globalCompletion_faithful`, all constructive; infinite matrices over the LCDA Sup,
identity via propositional i=j + HEq, modular per-entry, assoc/Sup = Fubini interchange). The final GloballyComplete instance is
UNIVERSE-BLOCKED (disjoint union of u-indexed families escapes to u+1; the completion is complete only at the next universe level
— needs a class redesign, not just a universe-poly GlobalObj) · §2.226 SYSTEMIC COMPLETION (assumes splitting witness; full
unit-existence blocked by §2.224 GloballyComplete).
MISSING: §2.153 assemblies · §2.155–§2.158 examples/projective-planes/free-rep/no-finite-axiom ·
§2.154 categories-iso headline · §2.168 ⟨I,∃⟩ presentation · §2.16(11)/(13)/(14) neighbors/recursive/assemblies · §2.21(10).

## §2.2  Distributive allegories

DONE: §2.21/§2.211 DISTRIBUTIVE ALLEGORY + laws · §2.212 Rel(C) distrib + TUDist⟹Map pre-logos · §2.213 Spl(𝓔)
distrib/effective/positive · §2.214 5-eq coproduct↔universal + positive⟺Rel-finite-coproducts · §2.215 POSITIVE ALLEGORY +
coproduct⟺product + TUPos⟹Map positive · **§2.216 POSITIVE REFLECTION** A⁺ (`MatObj`, `embed1` faithful, Tabular/Unitary/Positive
instances) · **§2.217** pre-logos↪positive(+pre-topos) · **§2.218** `tabular_repr_in_power_of_sets` (+`_distributive`) · §2.219
positive-SS⟺polarization · §2.22 LOCALLY COMPLETE · §2.221 downdeal LOCAL COMPLETION + faithful-rep · §2.223 GLOBALLY COMPLETE
def · §2.228 finite-unions-distribute-comp + counterexample.
DONE (newly): §2.222 ideal-allegory LCDA · §2.225 union-of-SS⟹SS · §2.223 disjoint-unions=coproducts BOTH DIRECTIONS
(FORWARD `IndexedDisjointUnion.isCoproduct`: a disjoint-union datum's injections are an indexed coproduct, mediator ⋃Uᵢ°Rᵢ;
CONVERSE `indexedCoproduct_to_disjointUnion`/`IsIndexedCoproduct.toDisjointUnion`: a family enjoying the indexed coproduct
universal property satisfies the three §2.223 equations UᵢUᵢ°=1 / UᵢUⱼ°=0 / ⋃Uᵢ°Uᵢ=1, mirroring binary `coproduct_of_universal_eqs`).
PARTIAL: §2.224 GLOBAL COMPLETION — faithful LCDA representation built (`globalLCDA`); final GloballyComplete instance
universe-blocked · §2.226 SYSTEMIC COMPLETION — partial-unit-embedding DONE (`partialUnits_embed_in_partialUnit`: in a globally
complete allegory where equivalence relations split, every set of partial units embeds in one partial unit, via coproduct +
`topEndo` split; `target_max_partialUnit`/`topEndo`/`IndexedDisjointUnion.inject_map`); the "maintains global completeness" /
unit-existence-iff-set-of-iso-types remainder is §2.224-universe-blocked.
MISSING: §2.21(10) eqn-theory union-free · **§2.227 maps-of-O(Y)-valued-sets≃H(Y)** (needs sheaf infra).

## §2.3  Division / power allegories

DONE: §2.31 DIVISION ALLEGORY + adjunction · §2.312/§2.313 LEFT DIVISION / adjoint-reformulation · §2.314 division identities
+ Rel(C)-division · §2.315 LCDA⟹division + division↪LCDA faithful · §2.316 Heyting-impl + Cor-adjunction + endo-poset · §2.32
TUDivAllegory + mapLogos + rightAdj · §2.34 PRel(E) division + embHom faithful + **embHom preserves division**
(`embHom_div`) · §2.342 A⁺ division + embed1_div · §2.343
logos↪positive-effective-logos full+faithful · §2.35/§2.351 SYMMETRIC DIVISION / STRAIGHT · §2.352/§2.353 straight-cancel +
converse · §2.354/§2.355/§2.356 effective-factorization / straight-of-comp / symmDiv-simple · §2.357 SIMPLE PART R/ₛ1 +
**Dom(R/ₛS)=1∩(R/S)(S/R) + Dom(R/ₛ1)=1∩R(1/R)** (`dom_symmDiv`/`domSimplicity_eq`) · §2.314 **(R/R)²⊑R/R +
(S\R/T)°=T°\R°/S°** (`div_self_idem`/`leftDiv_div_recip`) · §2.351 **straight⟺every-symmetric-T-with-TS⊑S-coreflexive**
(`straight_iff_symmetric_invariant_coreflexive`).
DONE (newly): §2.316 converse — a Heyting algebra IS a one-object division allegory (`OneObj H`: comp=inter=⊓, div R S:=S⇨R;
Allegory/Distributive/Division instances axiom-free) + bundled `HeytAlg` instance on `Cor(a)` (`Cor.instHeytAlg`) · §2.341
pre-tabular division ⟹ faithful division-preserving rep in tabular Spl(Cor) (`preTabularDivision_repr`) + semi-simple ⟹ faithful
rep in tabular Spl(𝒜) (`semiSimple_faithful_Spl_repr`) · §2.353 cancellation-on-maps (`straight_of_cancel_on_maps`).
PARTIAL: §2.311 division⟹comp-over-union (not derived from axioms) · **§2.331(i)–(iii) Moerdijk** (algebraic reduction done;
faithfulness + §1.543 capital-data are hypotheses; topological existence unproven) · §2.341 exact PRel(Rel) target needs
arbitrary-tabular↪Rel(Set) (only unitary+distributive→power available).
MISSING: §2.33 geometric/Stone rep specialized to countable TUDA · **§2.331(iv)** coprime-terminator⟹single-H(X)
(TOPOLOGY WALL) + δ-DENSE defs.

## §2.4  Power allegories

DONE: §2.41 POWER ALLEGORY/THICK (box-guarded) · §2.412 A(R) simple/map/uniqueness · §2.413 thickness-inference · §2.415
POWER-OBJECT/SINGLETON · §2.421 R/S=A(R)A°(S) · §2.43/§2.431/§2.432 PRE-POWER + thickness-char + effective-pre-power-is-power ·
§2.436 one-object-pre-power-inconsistent (+ honest hBox; unconditional book form proven FALSE for faithful box-guard) · §2.442
LAW OF METONYMY + semi-simple⟺metonymic · §2.443 A-calculus.
DONE (newly): §2.416 progenitor ∋-construction EPIC half (`progenitor_straight_factor_iso`: full iso h≫h°=1 ∧ h°≫h=1, the
piece flagged out-of-reach) · §2.441 forward directions (1)⟹(2)⟹(3), (1)⟹(4) · §2.422 `E = E/E` for equivalence relations
(`equivRel_eq_div_self`, axiom-free) + effectivity-if-coreflexives-split (`equivRel_effective_of_coreflexives_split`) · §2.423
connected power + coreflexives-split ⟹ unit (`maxEndo`/`target_split_partialUnit` unconditional; unit theorem on the book's own
hypotheses) · §2.435 Cantor algebraic (`thick_endo_degenerate`/`cantor_thick_endo`: thick endo on strongly-connected ⟹ degenerate;
T=F∋ thick when F°F=1) · **§2.434** global completion of a one-object LCDA is PRE-POWER (`globalScPrePower :
PrePowerAllegory (GlobalObj (Sc 𝒜₀ pt))`; one-object reduction `Sc 𝒜₀ pt` = arbitrary one-object full subcategory, evaluation
matrix `T_{f,i}=f(i)`, boolean `R̂`, `R̂T=R`, `R̂°R=(R̂°R̂)T⊑T`; [I]=(I→scalars) stays in Type u — §2.224 universe wall N/A) · **§2.433
core** Spl(Eq) thickness witness (`splEq_thick_witness`/`splEq_chain1`/`splEq_chain2`: for an equivalence-rel object E with source
E', thick T box-matched to E, fixed R, the witness `R̂ = E'(R/ₛT)` is entire with `R̂(TE)⊑R`, `R̂°R⊑TE` — the §2.433 BECAUSE; the
OCR'd `R/T` is SYMMETRIC division `R/ₛT`, so chain 2 collapses via `le_symmDiv_iff`).
PARTIAL: §2.422 "Spl(Cor) effective power" needs Spl idempotent-completion (the E=E/E part is done) · §2.441 full equivalence —
(3)⟹(1) honest hyp `hSJtoPP` · §2.416 thick-conclusion takes `hCotuple` · §2.435 carries the box-guard hypothesis (repo's
box-guarded Thick makes unconditional collapse false) · **§2.433** SplObj-level thickness for equivalence-relation objects DONE
(`splEqTarget_thick`: equiv-rel object E + base thick T ⟹ `embObj x ⟶ E` thick in SplObj, gated on `SplEqBoxNaming` = Freyd's §2.41
box index / §2.537 `QuotBoxNaming` analogue, discharged hbox-free for embedded objects via `splEq_embObj_thick`); the full
`PrePowerAllegory (SplObj 𝒜)` instance remains (needs the reflexive-only `Spl(Eq)` subtype — non-reflexive PER/coreflexive objects
have no thick target by this route) · §2.434 "systemic completion is a power allegory" headline = §2.432 on the effective/systemic
completion of `globalScPrePower` (documented corollary).
NOTE: §2.42 "splitting lemmas" = the inequalities Λ(R)Λ°(S)⊑(R/∋)(∋/S)⊑R/S and back, which PROVE §2.421 R/S=A(R)A°(S) —
already DONE as `symm_div_eq_A_comp`; the content is covered.
MISSING: §2.414 C-topos⟹Rel(C)-power (topos↔power bridge) · §2.417 generator counterexample (model) · §2.418 REALIZABILITY
TOPOS (construction) · §2.424 connected-power topos corollary · §2.437/§2.438 r.e.-relations / Gödel (RECURSION THEORY) ·
§2.444–§2.446 metonymy-independence (model) · §2.451–§2.455 boolean/CH/WELL-POINTED/cocartesian (set-theoretic models).

## §2.5  Quotient allegories

DONE: §2.521 BOOLEAN QUOTIENT · §2.53 AMENABLE CONGRUENCE def · §2.531–§2.535 ⁺-laws (R⊑S⟹R⁺⊑S⁺, (R∩S)⁺, [R]⊑[S]⟺R⁺⊑S⁺,
T⁺S⁺⊑(TS)⁺, refl/symm/trans-preservation) · §2.54 coreflexive-named · §2.563 SEPARATED/DENSE (faithful R≡⊤) + named-by-simple ·
**§2.5/§2.52 `QuotAllegory` KEYSTONE** (type synonym, homs = congruence classes; `instCat`/`instAllegory`/`instDistributiveAllegory`
lifted via Quotient induction; `quotRep` = representation of allegories; quotRep preserves ∪,𝟘) · **§2.51** quotRep preserves
entire/simple/map/tabular/(partial)unit (`quotRep_preserves_*`, generic over AllegoryFunctor) · **§2.536** amenable quotient of
division is division (`QuotAllegory.instDivisionAllegory`, R̄/S̄=overline(R⁺/S⁺)) · **§2.55** amenable quotient of locally/globally
complete (`instLocallyComplete`/`instGloballyComplete`) · **§2.541** transitive closure in amenable quotient
(`quotRep_isTransClosure`).
DONE (newly): §2.522 CLOSED QUOTIENT amenability (`closedQuotient_amenable`, R⁺ = R ∪ pαUpβ°).
PARTIAL: **§2.537** amenable quotient of effective
power allegory (`quot_effective_power_is_power`; §2.536 division, §2.535 splitting, §2.51 tabularity, §2.537 thickness all
unconditional — single remaining hypothesis `hbox` = §2.41 box-naming ∋_R=∋_{R⁺}).
DONE (newly): §2.551 CORE disjoint-unions-coincide-with-products (`IndexedDisjointUnion.isProduct`: indexed product with
projections Uᵢ°, the other half of §2.551's "coincide with coproducts AND products [2.223,2.214]"; §2.215 reciprocal duality).
MISSING: §2.542 topos⟹boolean-topos+bicartesian-rep (twin §1.979, WALL) · §2.551 the locale/Z-valued-sets equivalence-of-
categories remainder (congruence on a locale extends to its global completion; (-)⁺ representation) needs the Z-valued-sets model ·
§2.56 independence of AC · §2.561/§2.562/§2.564–§2.56(12) (need presheaf infra).
