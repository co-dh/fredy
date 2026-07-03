# TODO — remaining Chapter-2 items (Freyd, *Categories, Allegories*)

Status as of 2026-06-30. Everything below is **not yet formalized**; the rest of Chapter 2 is done
(see `COVERAGE.md`). Grouped by how reachable each is.

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
  valid (`sep_semidistrib`/`sep_modular`/`sep_inter_idem`, `Gle_iff_hom`). OPEN (Target 3, large
  separate development, correctly not faked): the no-finite-axiomatization METATHEOREM — the n-rhombus
  separated family is valid in Rel(S) but not a consequence of any fixed finite set, needing an
  inductive representation of equational-theory DERIVATIONS + the graph-map factorization analysis.
- **§2.417** (generator counterexample) — CORE DONE (`S2_417_Generator`, merged): category `C` of
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
