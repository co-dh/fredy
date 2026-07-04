# TODO — remaining Chapter-2 items (Freyd, *Categories, Allegories*)

Status as of 2026-07-03. Everything below is **not yet formalized**; the rest of Chapter 2 is done
(see `COVERAGE.md`). Grouped by how reachable each is.

## 2026-07-03 session — CLOSED (sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound})
- **§2.157 literal Desargues converse COMPLETE** — `desarguesND_iff_desarguesHorn` (four-family case
  tree `S2_157c`–`S2_157g`; coupled-shear key `cruxDesLeaf`).  Only the Veblen–Wedderburn 91-point
  non-Desarguesian model remains in §2.157.
- **§2.16(13)** recursive instance (`S2_16_Recursive`): effective reflection of R is not AC.
- **§2.158** core (`S2_158_GraphAllegory`): free representable one-object allegory = graph poset +
  decision procedure; Ĝ a one-object allegory.  OPEN: the no-finite-axiomatization metatheorem (Target 3).
- **§2.417** core (`S2_417_Generator`): category C + generator witness `G_generates`.  OPEN: "not a power
  allegory" (needs a Progenitor class) + Giraud conditions.
- **§2.16(14)** second presentation (`S2_16e_TwoPresentations`): E / Rel(A) as symmetric-idempotent /
  coreflexive splittings of the set-like subcategory, object/iso level.  OPEN: full categorical equivs.
- Chapter-1 also closed this session (see `COVERAGE.md`): §1.568 Quot(A), §1.596 Ab-functor-category iso,
  §1.513/514 covering families, §1.59(10) core (Frobenius eq I + adjunction).  Infra cleanup: S1_62's
  `Subobject.inter` meet-laws freed from a spurious `[PreLogos]` (commit 7717b47).

## ★ THE BOX-MATCHED THICKNESS — FAITHFUL to §2.431 (resolved 2026-06-30 from the original scan)

`PowerAllegory.eps_thick` is box-guarded (`codBox R = codBox ∋`). VERDICT after reading Freyd §2.431 (scan p.240):
this is **the book's definition**, not a deviation — §2.431 literally says "T is thick iff for all R such that
`R□ = T□` there exists R̂ ...". Freyd's thickness is box-matched, and §2.432/2.433/2.434 each construct a single
box-matched straight-thick `∋` per object — exactly this class. So **do NOT "fix" the class**: dropping the guard
(or adding an unguarded/box-family `∋`) would BREAK the faithful §2.432 `effective_pre_power_is_power` (and the
§2.433/§2.537 that build on it), which correctly produce only box-matched `∋`. (My earlier "deviation" framing
was wrong — extrapolated from §2.41's `∋_R = ∋_{R□}` notation without reading §2.431.)

So the four items below are NOT blocked by a class defect. They genuinely need MORE than a bare power allegory —
an UNGUARDED `∋` (classify every R, incl. naming `∅`). FOUNDATION DONE (commit 2f20f36): `UnguardedPowerAllegory`
(extends `PowerAllegory` with `eps_thick_all : ∀ R, ∃ map f, f∋=R`, Freyd §2.412/2.413) + `A_is_map'`/`A_eps_eq'`
(A(R) a map / A(R)∋=R for EVERY R) in `S2_4`; `relUnguardedPowerAllegory` (Rel(C) of a topos IS unguarded) in
`S2_41` = the non-vacuity witness. Bucket-1 items close OVER this refinement, no base-class change.
PROGRESS: §2.414-converse universal-property half DONE over it (`mapTranspose_existsUnique_all`, commit cccd487,
merged class `TabularUnitaryUnguardedPowerAllegory`): Map(A) has FULL power objects, ∅-naming included.

## Box-gated — ALL CLOSED over the `UnguardedPowerAllegory` foundation + `power_of_split_thick` (2026-06-30)

- ~~**§2.441 (3)⟹(1)**~~ — **DONE** (`straightJoin_to_prePositive`, `S2_441`, commit 44fc9c8): over
  `UnguardedPowerAllegory`, ℓ=A(1)≫A(1), ϰ=A(1/∋) into [[[γ]]], disjointness via `A_zero_inter_A_one`.
  `prePositive_wellJoined_straightJoin_tfae'` closes the TFAE. Axioms [propext].
- ~~**§2.433 full instance**~~ — **DONE** (`splEqPowerAllegory`, `S2_433_SplEqInstance2`, commit 7da9956):
  `PowerAllegory (Spl(Eq 𝒜))` for pre-power `𝒜` (+ §2.41 `hbox`). Route: `power_of_split_thick` (§2.432
  generalized tabular-free, commit 199cbd2) — Spl(Eq) is effective-by-splitting (`spl_equivalence_splits_map`,
  split object reflexive) but NOT tabular, and the effective→power chain never needed tabularity. Thick
  transfers SplObj→SplEqObj by defeq (full subcategory). Axioms [propext, Classical.choice].
- ~~**§2.537**~~ — **DONE** (`quot_effective_power_is_power_unguarded`, commit 28fe050): unconditional over the
  unguarded base (`EffectiveUnguardedPowerAllegory`); the §2.41 box-naming hbox is automatic when ∋ is unguarded.
- ~~**§2.414 converse**~~ — **DONE** (`mapTopos : Topos (Map A)`, `S2_41b`, commit af6d347): finite limits
  + full power objects + subobject classifier + `has_pow` all assembled over `TabularUnitaryUnguardedPower-
  Allegory`. Bridge `relOf(relPullback f U)=f≫relOf U` (from §2.147 cross-term) reduces `IsUniversalRel` to
  `mapTranspose_existsUnique_all`. §2.414 COMPLETE both directions. Axioms [propext, Classical.choice].
- ~~**§2.416 `hCotuple`**~~ — **DONE** (`hCotuple_of_coproduct` / `progenitor_straight_thick_of_coproduct`,
  S2_44, commit 308a811): discharged from binary coproducts + effectiveness via the coproduct mediator +
  §2.354 straightening. No box-gating.

## Real but large bridges/constructions (formalizable, multi-file)

- ~~**§2.414 forward**~~ — **DONE** (`relPowerAllegory`, S2_41, commit 5ce5b60): topos `C` ⟹ `Rel(C)` is a
  power allegory, via the topos membership `∋` (straight from classify-uniqueness, thick from the §2.413
  transpose). REMAINING for §2.414: the **converse** (a unitary tabular power allegory `A` ⟹ `Map(A)` is a
  topos) — needs the topos structure rebuilt on `Map(A)`. **§2.424** connected-power-topos corollary follows
  from the forward direction + §2.219.
- ~~**§2.168** (⟨I,∃⟩ locale-valued)~~ — **DONE** (`S2_168_ValuedSetsTabular`, merged fa02135): `instTabularOSet`
  (OSet(F) tabular, [Quot.sound] only — the §2.161 promise "Z-valued relations extend to a tabular allegory"),
  diagonal `ExtObj` ⟨I,∃⟩ full sub-allegory also tabular, entire/simple/map row characterizations, sharp
  embedding of the §2.111 Z-valued relations. Also ~~**§2.16(11)**~~ — **DONE** (S2_16b, f28699e): neighbors,
  `idempotent_splits_in_spl` (the two containments suffice to split in Spl(𝒮ℐ𝒹)), partial-order/strict-dense
  no-split corollaries (book's strict-dense containment misprint noted in doc comment).
- ~~**§2.155**~~ — **DONE** (`S2_155_BiEntire`, merged e53ff23): ∅-or-bientire relations B — all allegory axioms
  except the modular identity (concrete `modular_fails` witness), semi-lattice homs, not closed under ∩,
  `b_tabular` (modularity independent of tabularity), Map(B) has terminator but `map_b_no_products`.
- ~~**§2.156**~~ — **DONE** (`S2_156_PartitionRep`, merged 7f4ab7d, ALL axiom-free): modular lattice ⟹ §2.113
  one-object allegory; representations send elements to pairwise-commuting equivalence relations;
  `partition_representation` (join ↦ composition = equivalence-relation join); `equivRel_modular` converse.
- ~~**§2.16(13)** general theorem~~ — **DONE** (`S2_16c`, merged 80d6ee1, all [propext]): AC vs effective
  reflection — `projective_iff_isoEmbedded` (projectives of Spl(Eq 𝒜) = isomorphs of embedded objects),
  `not_coversSplit_of_not_effective` ("C not effective ⟹ Ĉ not AC"). The recursive/primitive-recursive
  instances remain (need §1.572/§1.573 as pre-logoi). PROGRESS: §1.572 positive part DONE
  (`S1_572_Recursive`, merged): hand-rolled Kleene codes + big-step Eval, category R on ExtNat,
  cartesian (products all six arms, equalizers via increasing enumeration), AC-regular via §1.571
  (`rFactorization`/`cover_split`/`all_projective`/`all_choice`, [propext,choice,Quot.sound]).
  Non-effectiveness also DONE (`S1_572b_NotEffective`, merged): arithmetized witness-checker acceptN
  (sound+complete+itself recursive), halting Kc r.e. + `K_not_recursive`, ERel from Kc as image of a
  recursive enumeration, headline `r_not_effective`. RECURSIVE INSTANCE NOW DONE
  (`S2_16_Recursive`, merged): `Freyd.RecEff.reflection_not_ac` — `Spl(Eq Rel(R))`, the effective
  reflection of the recursive category R, is NOT AC (`¬ CoversSplit (SplEqObj (RelObj ExtNat))`).
  Route: `eE = relClass ERel` reflexive/symmetric/idempotent in Rel(R) from `ERel_equivalence`;
  `no_splitsAsMap` via graph-embedding fullness (`embedRel_full`, §2.148) + `cover_iff_one_le_...`
  (§1.569) decodes any `SplitsAsMap` to `IsEffective ERel`, contradicting `ERel_not_effective`; then
  one-line `not_coversSplit_of_not_effective`. Axioms [propext,choice,Quot.sound]. §1.573/§1.574 also
  DONE (`S1_573_PrimRec`, merged): mu-free `IsPrim` fragment (pairing/div/mod redone mu-free), category P,
  §1.573 equalizer idempotent, P̂=Spl(P) with full+faithful `embP`, all idempotents split, headline
  `phatCartesian`; §1.574 faithful set-valued representation `phatPoints_separates`. Skipped
  (Ackermann-scale): "P not cartesian" counterexample, x⁻¹∉P / R as fractions of P.
- ~~**§2.157** core~~ — **DONE** (`S2_157_ProjectivePlane`, merged b4dd2af): plane axioms, height-4 lattice
  MODULAR (no interestingness) ⟹ associated allegory via §2.156; `DesarguesHorn` verified for Rel(S) and
  Horn ⟹ modularity (both axiom-free); Horn ⟹ Desargues under nondegeneracy. REMAINDER mostly DONE
  (`S2_157b_Desargues`, merged): degenerate cases ALL closed (`desarguesHorn_implies_desargues` needs only
  `DesarguesND`'s own 9 forced side conditions; `not_desargues_of_interesting` shows they're necessary);
  converse headline `desarguesND_iff_hornAtPoints` (Desargues ⟺ Horn at six-point configurations) +
  `desarguesHorn_iff_latticeHorn` + ⊤/⊥⊥/modularity-substitution Horn tuples. LITERAL CONVERSE NOW DONE
  (`S2_157c`/`S2_157d`/`S2_157e`/`S2_157f`/`S2_157g`, merged): `desarguesND_implies_desarguesHorn` and full
  `desarguesND_iff_desarguesHorn` — DesarguesND ⟹ HornConc at EVERY lattice 6-tuple, via the
  `latticeHorn_of_families` case tree on `H := (a₁⊔a₂)⊓(b₁⊔b₂)`: `H=⊥` disjoint core, `H=pt z`
  `hornCenter_famB` (the ONLY Desargues-consuming family — coupled-shear key `cruxDesLeaf` + 4 degeneracy
  chases feeding `hornConc_center_desargues`), `H=ln A` `hornLine_famC` (`M_κ` core + ⊤-mixed incidence
  bash), `H=⊤` `hornTop_famA` (12-leaf c-column bash). All [propext,Classical.choice,Quot.sound].
  STILL OPEN: Veblen–Wedderburn 91-point non-Desarguesian model (concrete counter-plane).
- ~~**§2.153**~~ — **DONE** (`S2_153_Assemblies`, merged 9e4a679): Assembly K is a POSITIVE PRE-LOGOS with
  disjoint stable coproducts (`asmPositivePreLogos`/`asmDisjointBinaryCoproduct`); ∇ functor; `allPartial`
  witness. BOOK DISCREPANCY: bare (i)(ii)(iii) provably insufficient — pairing + parameterized tag-cases
  closures made explicit `ModulusSystem` fields. REMAINING: non-effectiveness (needs recursive K).
- ~~**§2.16(14)**~~ — **DONE** (`S2_16d`, merged): generic `splEq_hom_iff` (Spl(Eq) homs = R with e≫R = R = R≫f,
  the book's IR = R = RJ form; axiom-free) + instantiation `AsmEffReflection K` = Spl(Eq (Rel(Assembly K))),
  A/I objects, `asmEmbed` A↦A/1_A full/faithful, graph functor on assembly morphisms, effectiveness
  `asmEffReflection_eqSplits`. SECOND PRESENTATION NOW DONE (`S2_16e_TwoPresentations`, merged): the
  book's closing remark, at the object/iso level. Set-like assemblies `IsSetLike K A` (all caucuses
  equal = the ∇-image = "simply sets"), `setGraph K A := ι` with DRY core `setGraph_comp_recip`
  (`ι≫ι°=1_⟨A⟩`), `e_A := ι°≫ι` coreflexive symmetric-idempotent. Generic `splObj_conj_iso` [propext]
  (any allegory, `ι≫ι°=1_a ⟹ (a,I)≅(s,ι°Iι)` in Spl). Presentation B
  `asm_iso_coreflexiveSplit_setLike` (Rel(A) = coreflexive splitting of the set-like subcategory);
  Presentation A `effReflObj_iso_symIdemSplit_setLike` (E = symmetric-idempotent splitting of same).
  [propext,Classical.choice,Quot.sound]. REMAINING: full categorical equivalences (standalone
  full-sub-allegory type + comparison functors + natural isos — infra absent); universal property.
- ~~**§2.154 headline**~~ — **DONE** (`S2_154_CategoriesIso`, merged): `smallRegCat_equiv_smallTabAlleg` —
  small regular categories (regular functors preserving terminators) ≃ small unitary tabular allegories
  (unitary representations), as a StrongEquivalence [propext,choice,Quot.sound]. Freyd's "isomorphic" downgraded
  to equivalence only because the `RelObj` wrapper changes the carrier type; components identity-on-objects up
  to the wrapper. INFRA: Map 𝒜 regular structure + CarrierBridge weakened to the book's tabular+unitary
  hypothesis (distributivity was over-assumed; S2_147/S2_111).
- ~~**§2.158** core~~ — **DONE** (`S2_158_GraphAllegory`, merged, choice-free [propext,Quot.sound]):
  `LGraph` (finite directed edge-labelled graphs with marks s,t), graph maps `Hom`, the tautological
  model `Trel`/`toRel`, `graph_yoneda` (the Yoneda engine), headline `decision` — a containment
  `E₁⊆E₂` holds in `Rel(S)` for ALL S iff there is a graph map `[E₂]→[E₁]` (the §2.158 DECISION
  PROCEDURE); `toRel_eq_Trel` (T is the graph model, preserves =/°/∩/∘); `ghatAllegory : Allegory
  (GStar L)` (Ĝ is a genuine one-object allegory over the repo's §2.11 class); recast SEPARATED axioms
  valid (`sep_semidistrib`/`sep_modular`/`sep_inter_idem`, `Gle_iff_hom`). Target 3 SCAFFOLDING DONE
  (`S2_158b_NoFiniteAxiom`): derivation system `Derives` + soundness `Derives_sound` + decision bridge
  `holdsInRel_iff_hom` + single rhombus `rhombus1_holds` (n=1, axiom-free) + CONDITIONAL metatheorem
  `no_finite_axiomatization` (axiom-free: valid n-rhombus family + `RhombusHard` ⟹ no finite valid axiom
  set is complete). OPEN combinatorial heart: (1) general-n rhombus validity; (2) `RhombusHard` =
  Freyd's counting/factorization (derivation⇒graph-map-chain bridge + bounded collapse invariant per axiom
  step + series-parallel `Ḡ` characterization: the n-rhombus admits no proper partial collapse staying in Ḡ).
- **§2.417** (generator counterexample) — power-object infra DONE (`S2_417b_NotPower`): `IsPowerObj`/
  `HasPowerObj`/`RelCIsPowerAllegory` (§2.414 phrasing), `singleton_of_power` (§2.415), positive half
  `coterminator_hasPowerObject`.  VERDICT on Target 3 (¬power-allegory): NOT faithfully reachable in the
  fixed-`L` (set-of-labels) encoding — Freyd's §1.96(10) collapse needs the map condition over ALL labels
  "in the universe" (a proper class); over a SET the obstruction vanishes (for |L|≤1, C = presheaf topos
  `[Bℕ,Set]` which HAS all power-objects, so ¬power-allegory is outright FALSE).  Faithful refutation needs
  a proper-class label re-encoding of C — a separate formalization.  Agent correctly did NOT assert the
  false negation.
- **§2.417** (original core, `S2_417_Generator`, merged): category `C` of
  quadruples `⟨S, s:S→S, A, f:L→S→S⟩` (`catC`, exponent `xᵃ = if a∈A then f a x else s x`, maps commute
  with every exponent — the map condition taken over ALL labels `a∈L` per §1.96(10), since the strict
  `A∪A'`-only reading breaks composition), and the HEADLINE `G_generates : Generates (G L)` +
  `generator_separates` — the book's `G=⟨{u,v},s,∅,∅⟩` with `sepRel x₀ = (w=v ∨ z=x₀)` giving
  `u(T⊚R)y` but `¬u(T⊚R')y`. `Rel(C)` modeled concretely as equivariant `CRel`. All
  [propext,Classical.choice,Quot.sound]. OPEN: "only the coterminator has a power-object in C ⟹ Rel(C)
  not a power allegory" (needs a Progenitor class + full Rel(C) allegory instance) and the Giraud-conditions
  verification.

## Universe wall (needs a class redesign, not a leaf file)

- **§2.224 `GloballyCompleteAllegory.disjointUnion`** instance — a `u`-indexed family's concatenated
  index escapes to `u+1`; global completion is complete only at the next universe level. Cascades to:
  - **§2.226 remainder** — "splitting maintains global completeness" / unit-iff-set-of-iso-types.
  - **§2.551 remainder** — the locale/Z-valued-sets equivalence of categories (`(-)⁺` representation).

## Genuine foundation walls (whole-subproject formalizations)

- **§2.227 / §2.33 / §2.331(iv)** — geometric/Stone representation, Moerdijk's theorem, `O(X)`-valued
  sets on metrizable spaces (locale/sheaf foundations + δ-dense defs).
- **§2.437 / §2.438** — r.e. relations / Gödel (recursion theory).
- **§2.418** — realizability topos (construction).
- **§2.451–§2.455 / §2.444–§2.446 / §2.56** — boolean/CH/well-pointed/cocartesian and metonymy-
  independence and independence-of-AC (set-theoretic model constructions).
- **§2.542** — topos ⟹ boolean topos + bicartesian rep (twin of §1.979).
- **§2.561 / §2.562 / §2.564–§2.56(12)** — need presheaf infrastructure.
- ~~**§2.21(10)**~~ — **DONE** (`S2_21c`, merged, self-contained): union normal form `DTerm.eval_toUnion`;
  product representation preserves union-free operations (`UTerm.eval_pi`, with explicit ∪-failure);
  headline `union_incl_iff` (⋃Eᵢ ⊆ ⋃Eⱼ' in Rel(Set) iff ∀i∃j Eᵢ⊆Eⱼ') via the book's
  product-of-counterexamples; `dIncl/dEq_iff_unionFree`. The §2.158-dependent no-finite-axiom remark
  stays with §2.158.

## Duplicate lemmas to dedup (from `scripts/dep_dup.py`, 2026-07-03)

Graph-based detector: nearest neighbours in the SVD embedding of the hub-removed dependency matrix,
then cross-file + same-kind + row-Jaccard, ranked by name+type. Method/plots: `graph/dependency-analysis.md`,
`graph/svd.pdf`. **Verify each before removing** (per `dedup-lean` skill: forward-or-delete the copy,
re-check `#print axioms`). Of the top 50 candidates:

| band | count | action |
|--------------------------------------|:-:|--------------------------------|
| A. real accidental duplicates        | ~15 | remove (verify) |
| B. intentional parallel copies       | ~13 | keep, or merge via one generic lemma |
| C. argument-order false positives    | ~10 | not dups — `type=1.0` fooled by token bag |
| D. verify individually               | ~12 | inspect |

**Caveat driving band C:** type equality here is token-set equality, which ignores argument order —
`product_mono_of_mono` (first factor) vs `_right` (second factor) score `type=1.0` but are different.
Clean precision needs a structure-aware type check or a proof-term hash.

### A — real accidental duplicates (remove) — HANDLED 2026-07-03 (dedup session)
- **★ §1.543 `Colim` → `LaxColim`, a whole re-derived file** (`CatColimitRegular` re-proved in
  `RatCapHcanon`/`RatCapPreReg`/`LaxGermPullbacks` under `LaxColim`, primed names):
  - ✅ `Colim.isIso_of_product_up` ~ `LaxColim.isIso_of_product_up'` — DONE: kept `Colim.isIso_of_product_up`
    (`S1_543_CatColimitRegular`), `isIso_of_product_up'` now `:= Colim.isIso_of_product_up p₁ p₂ hup`
    (`S1_543_RatCapHcanon.lean`, needed `import Fredy.S1_543_CatColimitRegular`).
  - ✅ `Colim.pullback_of_equalizer` ~ `LaxColim.pullback_of_equalizer'` — DONE: same forward. The `Colim`
    original is stated at two INDEPENDENT universes `{𝒟 : Type u} [Cat.{v} 𝒟]`; the `LaxColim` copy is the
    single-universe (`w`) specialization — a valid instantiation, not a generalization, so the forward
    direction is sound.
  - ✅ `Colim.isEqualizer_iso_apex` ~ `LaxColim.isEqualizer_iso_apex'` — DONE, same forward + same
    two-universe → single-universe specialization.
  - ✅ `Colim.isEqualizer_comp_iso` ~ `LaxColim.isEqualizer_comp_iso'` — DONE, same forward + same
    two-universe → single-universe specialization.
  - ✅ `LaxColim.objInclL_preserves_pullbacks` ~ `LaxColim.stageInclFunctorL_preservesPullbacks` — ALREADY
    forwarded (`objInclL_preserves_pullbacks := stageInclFunctorL_preservesPullbacks L hL tData pData
    eqData i f g` in `S1_543_LaxGermPullbacks.lean`); this scan entry was stale, no action needed.
  - ✅ `LaxColim.ratCapCat` ~ `LaxColim.ratCat` [def] — DONE: kept `ratCapCat` (`S1_543_CapitalizationLaxColimit`,
    upstream), `ratCat` (`S1_543_RatCapPreReg.lean`, downstream — that file already imports the former) now
    `:= ratCapCat P`, still `noncomputable abbrev` so its many downstream users (`RatCapImages`/
    `RatCapStagePTC`/`UniformCapStep`/`RatCapPositive`) are unaffected.
  - ✅ `innerSliceCartesianNil` ~ `innerSliceCartesianNilLoc` [instance, unused] — DONE: deleted the stale
    leftover `innerSliceCartesianNil` from `S1_541_RelativeCapitalization.lean` (an unreferenced `instance`;
    everything else in its "RELOCATED" block had already been moved upstream to `S1_543_Capitalization`'s
    `innerSliceCartesianNilLoc`, which that file already imports — typeclass search now finds only the one
    upstream instance).
- **Other cross-file:**
  - ✅ `Alg.recip_Sup` (`S2_3`) ~ `Alg.recip_Sup'` (`S2_22`) — DONE: deleted `recip_Sup'` (only 1 internal call
    site in `S2_22.lean`, rerouted to `recip_Sup`, already in scope — both declared in namespace `Freyd.Alg`
    and `S2_22` imports `S2_3`).
  - ✅ `Alg.AllegoryFunctor.mono` (`S2_51`) ~ `Alg.AllegoryFunctor.map_mono` (`S2_156_PartitionRep`) — DONE:
    kept `AllegoryFunctor.mono` (§2.51, the natural book-section home), `map_mono` now
    `:= AllegoryFunctor.mono F h` (kept as a name since `F.map_mono` dot-notation is used 3× locally in
    `S2_156_PartitionRep.lean`; added `import Fredy.S2_51`, no cycle).
  - ⏭ SKIPPED: `exists_ultrafilter_excluding` (`S1_75`) ~ `PreLogosHorn.Stalk.exists_ultrafilter_excluding`
    (`S1_62`) — genuine universe-generality mismatch, not a safe forward either direction. `S1_75`'s copy is
    stated at two INDEPENDENT universes (`variable {𝒞 : Type u} [Cat.{v} 𝒞]`, `v` and `u` unconnected —
    actually exercised downstream by `S1_635_StalkFamily.lean`'s own `Cat.{v} 𝒞`); `S1_62`'s `Stalk`-section
    copy is proven only at the single-universe specialization `[Cat.{u} 𝒞]`. Forwarding `S1_62 → S1_75`
    would cycle (S1_75 already imports S1_62; S1_62's own doc comment says as much). Forwarding
    `S1_75 → S1_62` needs special ⟹ general, which is invalid (would require narrowing `S1_75`'s stated
    generality, risking breakage of `S1_635_StalkFamily`'s genuine two-universe use — unlike the `Colim`
    cluster above, no evidence here that the extra universe is dead weight). Left both proofs intact.
  - ✅ `inter_mono` (`S1_62`) ~ `Subobject.inter_mono` (`S1_658_Complement`) — ALREADY forwarded
    (`Subobject.inter_mono := Freyd.inter_mono hS hT`); stale scan entry, no action needed.
  - ✅ `cover_comp'` (`S1_543_Capitalization`) ~ `cover_comp''` (`S1_48_RationalCapitalization`) — DONE:
    kept `cover_comp'` (upstream; `S1_48` reaches it transitively via `S1_541_RelativeCapitalization`),
    `cover_comp''` now `:= cover_comp' hf hg`. Needed `omit [PullbacksTransferCovers 𝒞] in` on `cover_comp'`
    first — Lean's default `variable` inclusion had pulled that ambient instance into its ELABORATED
    signature even though the proof never uses it (confirmed via `#check @Freyd.cover_comp'`); `omit`
    drops it, which is a strict generalization (backward-compatible with every existing call site).
  - ✅ `Alg.div_mono_left` (`S2_3`) ~ `Alg.div_num_mono` (`S2_441_StraightJoin`) — DONE: kept `div_mono_left`
    (`S2_441_StraightJoin` already reaches `S2_3` transitively via `S2_44`→`S2_4`→`S2_3`), `div_num_mono`
    now `:= div_mono_left h S`.
  - ⏭ SKIPPED: `FibreDensityProof.fibrePinEqualizers` (`S1_546`) ~ `UniformCap.uniformPinEqualizers`
    (`S1_547`) [def] — both are `local instance`s. `local` declarations are scoped to their own file/section
    and are NOT visible from other files even when imported, so neither can forward to the other; each file
    genuinely needs its own copy of the diamond-resolution pin. Not a real duplicate to remove.

  Verification: full `lake build` green (263 jobs) after every pair; `#print axioms` on all kept/forwarding
  lemmas ⊆ `{propext, Classical.choice, Quot.sound}` (several have `[]`), no `sorryAx`.

### B — intentional parallel copies (keep, or merge into one generic lemma) — INVESTIGATED 2026-07-03
- AoP case studies, same abstract theorem per problem: `{knapsack,bitonic,paragraph}_thinning`
  (`A8_4/6/5`), `{tardiness,tex}_greedy` (`A10_3/4`), `{bracketing,compression}_dp` (`A9_3/4`).
  → **KEEP.** Each already forwards `:= thinning_min …` / `:= greedy_dp …` / `:= dynamic_programming …`
  to the single generic abstract theorem; the wrappers are byte-identical to it (no per-problem
  specialization) and serve as per-section signposts. Already generalized; nothing to merge.
- Per-datatype `RelSet`: `{CL,SL,Digits}.simple_uniq`, `{CL,SL,Digits}.entire_total`
  (`A6_ConsList`/`A6_SnocList`/`A6_1_Digits`) → **DONE** (hoisted to the `A6_1_RelSet` base,
  commit 1835254; the three child copies deleted, uses resolve up via ancestor lookup).
  `ListRel.dList` ~ `Sort.dList` → **KEEP** (real dup but a 1-line `abbrev dList := dCL Unit A`;
  deduping needs a cross-file import for ~0 line savings — coupling costs more than it saves).

### C — argument-order false positives (NOT duplicates)
- `product_mono_of_mono` (`S1_47`, first factor) ~ `product_mono_of_mono_right` (`S1_64`, second factor)
- `Alg.modular_le_left'` (`S2_16b`) ~ `Alg.modular_le_right` (`A4_1`)  — the two modular inequalities
- `Colim.*_castHom` family — distinct properties of the same `castHom`: `heq_`/`mono_`/`cover_`/`castHom_`/`castHom_castHom`

### D — verify individually — ALL VERDICTS IN (investigated 2026-07-03)
- ✅ **DONE** `Alg.dom_comp_eq` (`S2_147:63`) ~ `Alg.dom_comp_self` (`S2_3:563`) — generalize-to-dedup:
  relaxed `dom_comp_self` to `[Allegory]` (`omit [DivisionAllegory]`), `dom_comp_eq := dom_comp_self R`
  (commit 4d5e60b).
- ✅ **DONE** `complementedSub_legs_iso` (`S1_62`) ~ `complemented_legs_iso` (`S1_64`) — forwarded
  `complemented_legs_iso := complementedSub_legs_iso …` (commit 6e9c80f, the main DRY sweep).
- ⏭ **KEEP (real dup, 1-liner)** `le_largest_self` (`S2_53:264`) ~ `self_le_largest` (`S2_55:63`) —
  identical 1-line lemma; forwarding needs `import S2_53` in S2_55 for ~0 line savings. Harmless dup.
- ⏭ **KEEP (documented-intentional)** `cover_comp_iso_cat` (`S1_543_CofinalHstage`, general `[Cat]`) ~
  `cover_comp_iso` (`S1_62`, `[PreLogos]`). The S1_543 copy is UPSTREAM and its docstring documents that
  S1_62's isn't reachable there; forwarding the S1_62 copy down would force S1_62 to import into the
  §1.543 cluster — coupling not worth 15 lines.
- ⏭ **KEEP (generalizable but 1-line def)** `LaxColim.stageZero` (`S1_61`) ~ `Colim.stageZero`
  (`S2_218`) — same expression against two structure bundles; a generic def over the object-family
  would unify them, but both are 1-line defs — not worth a new abstraction.
- ❌ **FALSE POSITIVE** `image` (`S1_51:149`, image of a morphism) ~ `DirectImage` (`S1_70:89`, image of
  a subobject) — different arity/role. `Alg.topHom` (`A4_4:105`) ~ `Alg.topRel` (`S2_5:566`) — real dup
  of a trivial `Sup (fun _ => True)` def, but deduping adds an import; KEEP.
- ❌ **FALSE POSITIVE** `Alg.le_comp_recip_comp` (`A4_1`, B&dM 4.10 `R ⊑ (R≫R°)≫R`) ~ `Alg.le_dom_comp`
  (`S2_1`, F&S §2.122 `R ⊑ dom R ≫ R`) — different RHS; le_dom_comp is strictly stronger.
- ❌ **FALSE POSITIVE** `overPreRegular` (`S1_53_SliceRegular`, slice of PRE-regular) ~ `overRegular`
  (`S1_65_SlicePreTopos`, slice of regular, needs `HasImages`) — distinct hierarchy levels.
- ❌ **FALSE POSITIVE** `monic_pair_of_monicPair` / `monicPair_of_monic_pair` (`S1_56`) ~ `QSeq139.*`
  (`QSeq139.lean`) — `QSeq139.monicPairQSeq` is Typst diagram DATA, not a proof.

### E — general-theorem dedup follow-ups (from the 2026-07-03 general-framework survey)

The survey concluded the big general frameworks already exist (S1_8 `Adjunction`, A4_4 `GaloisConn`,
S1_82 `HasLimit`, `RegularFunctor` bundles + `image_chosenPullback_isPullback`) or are net-negative to
introduce; see memory `general-framework-dedup-survey`. Three genuine NARROW wins remain:

- [~] **E1. Unify the 3 indexed-product structures** → **MOSTLY DONE / rest NOT WORTH** (worked 2026-07-03).
  Survey oversold it. `HasProducts {Type v}` (S1_82:142) is a DIFFERENT shape (a `class` bundling ALL small
  products, `∀{I}F` quantified inside `prodObj`/`tupling`), not a single-family structure — it does not fold
  into `HasIndexedProduct`, and is used only in S1_82's §1.825. The genuine overlap `HasIndexedProduct` (S1_42)
  ↔ `HasFinProd` (S1_43) is ALREADY bridged: `HasIndexedProduct.toHasFinProd` adaptor + `finProd_of_term_binary
  := finiteProduct_from_term_binary.toHasFinProd` (commit 29b168c, this session). Fully eliminating `HasFinProd`
  = a moderate refactor of the FOUNDATIONAL finite-products API (`FinProdCone`/`HasFiniteProducts`/`finProdObj/
  π/lift`) for ~15 lines, losing the cone-grouped ergonomics — not worth the risk. No further action.
- [x] **E2. Collapse the `∃_f ⊣ f#` triple** → **DONE** (commit 73c9241). `existsAlong` (S1_60), `DirectImage`
  (S1_70), `directImage` (S1_967) are all `image (arr ≫ f)`; generalized the upstream `existsAlong` to
  `[HasImages]` (`omit [PreLogos]`) and forwarded the two downstream copies to it — one canonical op. (The
  adjunction LEMMAS `directImage_adj`/`directImage_adjunction` genuinely differ — `InverseImage f T` instance
  vs `invImg f T hp` explicit-pullback — and `directImage_adj` is already 1-line via reusable bridges; kept.)
- [~] **E3. Re-route `objIncl_preservesPullbacks_generic`** → **FALSE LEAD** (no action). It already delegates
  the chosen pullback to `image_chosenPullback_isPullback` (via `objIncl_preserves_pullbacks`, S1_543_Capitalization:332)
  and adds a genuine chosen→generic upgrade (comparison iso). The survey agent conflated the chosen-pullback and
  generic-`PreservesPullbacks` levels; there is nothing to re-route.
