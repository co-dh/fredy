# Henkin / §1.543 Capitalization — Handoff

Last updated: 2026-06-16. Read this together with `CAPITALIZATION_ROADMAP.md` (the milestone map)
and the auto-memory `catcolimit-regular` (proof techniques + gotchas).

## Where the work lives

- **Branch: `master`, main checkout `/home/dh/repo/fredy`.** All my work is committed on `master`.
- I originally used worktree `.claude/worktrees/colimit` (branch `colimit-cover-reflect`), then
  **merged it into master** (merge commit `3f5cb5c`) and continued directly on master. That worktree
  is now **stale** (behind master) — safe to remove: `git worktree remove .claude/worktrees/colimit`.
- Master has since had unrelated "wave-formalize" commits added on top (HEAD around `eedcf1b`).
- Everything is in **`Fredy/CatColimitRegular.lean`** (plus one helper in `Fredy/S1_51.lean`).

## Build / verification state

- `lake build Fredy.CatColimitRegular` **succeeds**.
- There ARE `sorry` warnings, but they are in **dependencies from the wave-formalize work**
  (`S1_33`, `S1_43`, `S1_45`), NOT in my lemmas. My lemmas are sorry-free.
- Verify any of my lemmas is clean with, e.g.:
  ```
  lake env lean --run <(printf 'import Fredy.CatColimitRegular\n#print axioms Freyd.Colim.colimHom_cover_reflects\n')
  ```
  Expected axioms for all of them: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
  `Classical.choice` is expected — it enters via `colimOut` picking representatives (§1.543 needs
  choice anyway).
- **Tooling note:** the Lean LSP/MCP TIMES OUT loading `CatColimitRegular.lean` (huge file, depends on
  the 565-line `CatColimit.lean`). Iterate via `lake build` error dumps instead of MCP `lean_goal`.

## The big picture

`capitalization_lemma` (`Fredy/S1_54.lean`) is proved by: build the directed colimit of categories,
show it is **pre-regular** (`PreRegularCategory C.Obj`), then iterate the slice construction `A ↦ A*`
transfinitely to a fixed point that is capital. Exact Henkin-Lubkin (the representation theorem,
`Fredy/S1_55.lean`) is blocked ONLY on capitalization (projectivity of all objects). So finishing
this colimit-is-pre-regular + capitalization chain is what unblocks henkin.

Milestones (see roadmap for detail):
- M1 (colimit of types), M2 (colimit of categories = `colimitCat`): **DONE**.
- M3a/b terminal+products, M3-eq equalizers ⇒ pullbacks (via §1.432): **DONE**.
- **M3-cov reflection suite: DONE (this is what I just finished — see below).**
- M3-cov **assembly** (`PullbacksTransferCovers C.Obj` ⇒ `PreRegularCategory`): **OPEN — next task.**
- M4 (slice functor `A ↦ A*`), M5 (transfinite ordinal iteration — the WALL), M6 (final assembly):
  **OPEN, multi-session.**

## What is DONE (the M3-cov reflection suite, all sorry-free)

All in `Fredy/CatColimitRegular.lean`. These move covers/monos/isos between a single stage `C.A i`
and the colimit `colimitCat C hC`, in BOTH directions and BOTH representations.

Pre-existing (before my session): `colimHom_isIso_of_rep` (iso preservation), `homIncl_injective`
(faithfulness of `homIncl` given faithful transitions), `colimHom_mono_of_rep` (mono preservation),
`homInclObj` (stage-inclusion of morphisms), `homInclObj_injective`.

Added by me (in dependency order):
1. `homInclObj_comp` — functoriality of the stage inclusion (`homInclObj (g≫g') = colimComp …`).
2. `colimHom_mono_reflects` — colimit mono ⇒ stage-mono-under-transitions (converse of
   `colimHom_mono_of_rep`).
3. `homCompRaw_eq_stage` + `homCompRaw_eq_id_stage` — extract a stage equation from a colimit
   composite equality (`homCompRaw uf f ug g = homIncl uh hh`). KEY helper used everywhere below.
4. `isIso_of_castHom`, `castHom_injective`, `mono_castHom`, `cover_castHom` — `castHom` reflects/
   preserves iso/mono/cover (transport-along-object-equality lemmas).
5. `colimHom_isIso_reflects` — colimit iso ⇒ stage iso (after a transition to some higher stage `L`).
6. `colimHom_cover_of_rep` — **cover preservation**: a germ `f₀` that is a cover at every stage it
   transports to includes to a colimit cover. Hypothesis `hcov : ∀ L, Cover ((functF haL).map f₀)`.
7. `homInclObj_mono_of_stage`, `homInclObj_isIso_reflects`, `homInclObj_cover_reflects` — the same
   reflection lemmas in the `homInclObj` (same-stage) form.
8. `colimHom_cover_reflects` — **cover reflection in colimOut-rep form**: `Cover (homIncl a f₀) ⇒
   Cover f₀`. THIS is the form the assembly needs. Hypotheses: `hcons` (transitions conservative:
   `IsIso (functF.map φ) → IsIso φ`) and `hmono` (transitions preserve monos:
   `Mono φ → Mono (functF.map φ)`). Both true for slice projections `Σ:A/B→A`.

In `Fredy/S1_51.lean`:
9. `cover_precomp_iso` — pre-composing a cover with an iso is a cover (general category lemma; lets a
   pullback-square cover reduce to the canonical-pullback cover, since the two π₂'s differ by the
   comparison iso).

NET: cover/mono/iso **preserve AND reflect** are all available, in the colimOut-rep (`homIncl`) form
that the assembly consumes. Plus `cover_precomp_iso`.

## NEXT TASK: the assembly (PullbacksTransferCovers ⇒ PreRegularCategory)

Goal: produce `@PullbacksTransferCovers C.Obj (colimitCat C hC)` (given suitable hypotheses on the
system, deferred to M4 like `colimitHasEqualizers` defers `hpres`), then bundle terminal + products +
pullbacks + PTC into `PreRegularCategory C.Obj`.

`PullbacksTransferCovers.pullbacks_transfer_covers : ∀ {A B C'} {f : A⟶C'} {g : B⟶C'} (c : Cone f g),
c.IsPullback → Cover f → Cover c.π₂`  (defs in `Fredy/S1_45.lean`: `Cone`, `Cone.IsPullback`,
`HasPullback`, `HasPullbacks`; `PullbacksTransferCovers` in `Fredy/S1_52.lean`).

### The one genuinely-hard ingredient: PULLBACK REFLECTION

The colimit pullback square must reflect to a STAGE pullback square, so that the stage's own
`PullbacksTransferCovers` applies. This is the "filtered colimit of categories" content and is the
only real obstacle left in M3.

Recommended route (mirrors `colimitHasEqualizers`, ~150–200 lines):
- **Build the colimit pullback as the colimit of the stage pullbacks.** I.e. a
  `colimitHasPullbacks`-style construction taking a hypothesis "transitions preserve pullbacks"
  (analogous to `colimitHasEqualizers`'s `hpres`/`hpres_lift`). Because you CONSTRUCT it, you KNOW its
  `π₂`'s representative IS the stage pullback's `π₂₀` (a stage map) — no fullness argument needed.
  Mirror `colimitHasEqualizers` (line ~425 in `CatColimitRegular.lean`): package as one existence-Prop
  `hPBdata` so `Quotient.inductionOn` works on `f`, `g`, and the cone leg alike; extract the
  `HasPullback` structure by `Classical.choose` (the goal is a Type, so `obtain` is illegal); reuse the
  `hDirSubsingleton`/`hF_proof_irrel`/`cR`/`cT` cast-slide patterns.
- Then PTC for the CANONICAL pullback follows: `f₀` is a stage cover (`colimHom_cover_reflects`),
  stage `PullbacksTransferCovers (C.A L)` gives `π₂₀` a stage cover, then `colimHom_cover_of_rep`
  (cover preservation) lifts it back. (`colimHom_cover_of_rep` needs `π₂₀` a cover at EVERY stage —
  supply via "transitions preserve covers" hypothesis applied to the stage cover.)
- An ARBITRARY pullback cone `c` is iso to the canonical one (pullbacks unique up to iso); `c.π₂ =
  φ ≫ canonical.π₂` with `φ` the comparison iso, so `cover_precomp_iso` transfers `Cover canonical.π₂`
  to `Cover c.π₂`. (You may also want a `cover_postcomp_iso`/iso-invariance variant — check direction.)

Alternative (NOT recommended): reflect an arbitrary cone directly. This needs genuine
fullness-up-to-transition (the colimit mediating map only comes from a stage map at a *higher* stage,
so a fixed finite stage need not be a pullback). The "build as colim of stage pullbacks" route above
sidesteps this — prefer it.

### Final bundle
Once `colimitPullbacksTransferCovers` exists:
`instance : PreRegularCategory C.Obj := { ⟨terminal⟩, ⟨products⟩, ⟨pullbacks⟩, ⟨PTC⟩ }` — it just
extends `HasTerminal + HasBinaryProducts + HasPullbacks + PullbacksTransferCovers`, all now available.

## After M3 (still open, large): M4 / M5 / M6
- **M4** `Fredy/S1_546.lean`: the relative-capitalization functor `A ↦ A*` via slices; build the actual
  `CatSystem` whose transitions are the slice embeddings and DISCHARGE the deferred hypotheses
  (`hcons` conservative, `hmono`/`hcov_pres` preserve monos/covers, `hpres` preserve pullbacks/
  equalizers, faithful via `slice_embedding_separates`). The slice projections genuinely satisfy these.
- **M5** `Fredy/S1_543.lean`: ordinal-indexed transfinite iteration of M4 to a fixed point.
  **This is the wall** — a standalone foundational project; the ONLY file permitted to import mathlib
  `Mathlib.SetTheory.Ordinal.*` (keep everything else mathlib-free).
- **M6** `Fredy/S1_54.lean`: assemble — `Ā` = the colimit; prove `Capital Ā` + faithful `A → Ā`;
  discharge `capitalization_lemma`.

## Key gotchas / techniques (learned the hard way)
- **Reducible `Mono`/`Cover` leak metavars.** `refine/exact colimHom_mono_of_rep … ?_` against a
  `Mono`/`Cover` goal leaks an uninstantiated `W` metavar (the class unfolds to a `∀`/Π). FIX:
  `intro Z p q hpq` to expose the binders, then apply the lemma's RESULT to `p q hpq`. Also pass `{A,B}`
  EXPLICITLY to `colimHom_mono_of_rep`/`colimHom_isIso_reflects` — `colimOut` isn't invertible so Lean
  can't infer them from the morphism.
- **`Quotient.exact` on the hom-colimit gives an `UpperBound`, not a bare stage.** Its bound is not an
  explicit constructor, so `homTr_comp`/`homTr_trans` won't match. Push to a CONSTRUCTED stage `L` via
  `congrArg (homTr … ⟨L,..⟩)` first (see `homCompRaw_eq_stage`).
- **Cast directions in the `functF.map (germ)` computations** go `.symm` (`ed.symm`/`ec.symm`) and use
  `(hC.trans_map …).symm` — getting this backwards gives "application type mismatch". The `ec`-style
  proof is `rw [← C.F_trans (D.trans a.2.2 h_ts) hj xB, ← C.F_trans a.2.2 (D.trans h_ts hj) xB]`
  (closes by proof-irrelevance defeq).
- **Don't re-state germ compositions in a `show`.** Re-elaboration fails to unify the middle object
  (proof-irrelevance on let-bound witness `.K` fields doesn't zeta-reduce in fresh `isDefEq`). Instead
  `dsimp only [HioWitness.germ]` then `rw [castHom_comp, ← map_comp]` directly on the goal.
- **The "bridging" trap to AVOID.** Don't try to prove `homInclObj f₀ = castHom eqA eqB (homIncl …)`
  to connect the `homInclObj` and `homIncl` worlds — the object equalities `objIncl a.1 (C.F.. xA) = A`
  can't be `subst`'d (each colimit object appears inside its own representative → occurs check). Instead
  prove what you need DIRECTLY at the representative/germ level (as `colimHom_cover_reflects` does,
  mirroring `colimHom_mono_reflects`).
- `∃!` and the `set` tactic are UNAVAILABLE (mathlib-free): spell out `∃ l, P l ∧ ∀ l', P l' → l'=l`,
  and use `let`+`change` instead of `set`.
- `CatColimit.lean` is the 565-line foundation; if a merge ever drops it, restore from blob `d5eade0` /
  commit `dfcde49`.
