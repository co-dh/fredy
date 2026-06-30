# TODO — remaining Chapter-2 items (Freyd, *Categories, Allegories*)

Status as of 2026-06-30. Everything below is **not yet formalized**; the rest of Chapter 2 is done
(see `COVERAGE.md`). Grouped by how reachable each is.

## Tractable, attempted, not yet landed

- **§2.441 (3)⟹(1)** — discharge `hSJtoPP` (`StraightJoinCond ⟹ PrePositiveCond`) in `S2_44.lean`.
  Book proof complete (typ §2.4 lines 293–360): `Λ(S)=A(S)` monic (already have `A_monic_of_straight`),
  then `ℓ,ϰ = (1/∋)(1/∋')` into the **double** power object with disjoint images `ℓϰ°=0`, reducing to
  `Λ(0) ∩ Λ(1) = 0`. The disjointness core is OCR-murky in the book *and* likely box-guard-gated
  (`Λ(S)` entire needs `codBox S = codBox ∋`, same box issue as §2.433/§2.537). Needs a focused session.
- **§2.433 full instance** — `PrePowerAllegory (SplObj 𝒜)` proper. Have `splEqTarget_thick` (equivalence-
  relation objects thick, gated on `SplEqBoxNaming`). Needs the reflexive-only `Spl(Eq)` **subtype**
  carrying its own `Cat`/`Division`/`Effective` instances, with per-object box-naming discharged.

## Box-naming-gated (the accepted §2.537 `hbox` pattern — repo design)

- **§2.537 `hbox`** — `quot_effective_power_is_power` carries the §2.41 box-naming `∋_R = ∋_{R⁺}`.
- **§2.416 `hCotuple`** — `progenitor_straight_thick` takes a cotuple/coproduct straightening hypothesis;
  may now be dischargeable in a positive/globally-complete setting given §2.223/§2.551 coproducts.

## Real but large bridges/constructions (formalizable, multi-file)

- **§2.414 forward** — topos `C` ⟹ `Rel(C)` is a power allegory. `RelObj C` currently stops at
  `DistributiveAllegory`; must build the topos power object as a `Rel(C)` membership `∋`, prove it
  straight + thick. (§2.424 connected-power-topos corollary follows.)
- **§2.155–§2.158**, **§2.168** (⟨I,∃⟩ locale-valued), **§2.417** (generator counterexample) — specific
  model/example constructions.

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
- **§2.21(10)** — equational theory of representable distributive allegories (meta-theory of
  representability: union-free normal form + counterexample product).
