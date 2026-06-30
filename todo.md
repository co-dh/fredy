# TODO — remaining Chapter-2 items (Freyd, *Categories, Allegories*)

Status as of 2026-06-30. Everything below is **not yet formalized**; the rest of Chapter 2 is done
(see `COVERAGE.md`). Grouped by how reachable each is.

## ★ THE BOX-GATING WALL — one root cause blocking FOUR items

The repo's `PowerAllegory.eps_thick` is **box-guarded** (`codBox R = codBox ∋`): the membership `∋` classifies
a relation `R̄` only when its box matches. This single limitation blocks the *full* versions of §2.441 (3)⟹(1),
§2.433, §2.537, AND the §2.414 converse (S2_41b). Each has its sorry-free **partial** committed (everything up
to the box-guard); the full closes need ONE of:
  (i)  an **unguarded thickness** `∀ R̄, ∃ map f, f ≫ ∋ = R̄` (equivalently: `A(𝟘)` is a map — `[C]` has a
       ⊥ point `∅`); or
  (ii) a **box-indexed membership family** `∋_K : [C]_K → C` per coreflexive box `K ⊑ 1_C` (Freyd's `∋_{R□}`).
Both are genuine ADDITIONS to the `PowerAllegory` interface, not derivable from box-guarded `eps_thick` (same
gap as `Spl.lean` Goal-B; `eps_entire`/`codBox ∋ = 1` is necessary but NOT sufficient — it still excludes `𝟘`).
**HIGH-VALUE NEXT STEP**: decide whether (i)/(ii) is a sound strengthening (esp. provable in a *tabular unitary*
power allegory, where `A(𝟘)`-as-a-map may follow from tabulation+unit — UNTESTED) or a genuine new axiom; either
way it unblocks all four at once. NB the box-guard was added deliberately (makes §2.431 a true biconditional;
§2.435 proved the *unconditional thickness collapse* false) — so (i)/(ii) must be checked for soundness first.

## Box-gated — partial committed, full close blocked by the wall above

- **§2.441 (3)⟹(1)** (`S2_44`) — disjointness crux DONE (`A_zero_inter_A_one`) + `A_monic_of_straight`; full
  `ℓ,ϰ:[γ]→[[[γ]]]` split-monic needs `Λ(S)` entire (the wall). (NB: trivial WITH coproducts via inl/inr — the
  triple-power trick is only for the FREE no-coproduct power allegory.)
- **§2.433 full instance** — needs the reflexive-only `Spl(Eq)` subtype + per-object `SplEqBoxNaming` (the wall);
  `splEqTarget_thick` (the per-object thickness) is done.
- **§2.537 `hbox`** — `quot_effective_power_is_power` carries the §2.41 box-naming `∋_R = ∋_{R⁺}` (the wall).
- **§2.414 converse** (`S2_41b`) — `Map(A)` topos: merged class + membership `mapMem` + box-guarded universal
  property DONE; full `Topos` needs the unguarded membership (the wall).
- ~~**§2.416 `hCotuple`**~~ — **DONE** (`hCotuple_of_coproduct` / `progenitor_straight_thick_of_coproduct`,
  S2_44, commit 308a811): discharged from binary coproducts + effectiveness via the coproduct mediator +
  §2.354 straightening. No box-gating.

## Real but large bridges/constructions (formalizable, multi-file)

- ~~**§2.414 forward**~~ — **DONE** (`relPowerAllegory`, S2_41, commit 5ce5b60): topos `C` ⟹ `Rel(C)` is a
  power allegory, via the topos membership `∋` (straight from classify-uniqueness, thick from the §2.413
  transpose). REMAINING for §2.414: the **converse** (a unitary tabular power allegory `A` ⟹ `Map(A)` is a
  topos) — needs the topos structure rebuilt on `Map(A)`. **§2.424** connected-power-topos corollary follows
  from the forward direction + §2.219.
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
