# Capitalization Lemma (§1.543) — sorry-free roadmap

Goal: prove `capitalization_lemma` (`Fredy/S1_54.lean`) sorry-free. Policy (see `AGENTS.md`): category
theory stays hand-built on this repo's `Cat`; only the ordinal-indexed iteration file may import
`Mathlib.SetTheory.Ordinal.*`.

Freyd's proof: iterate the relative-capitalization step `A ↦ A*` transfinitely and take the directed colimit;
the colimit is capital and receives `A` faithfully.

## Milestones

| # | Module | What | Status |
|---|--------|------|--------|
| **M1** | `Fredy/DirectedColimit.lean` | Directed colimit of **types** (`Quotient`), inclusions, `desc` universal property | ✅ **done, sorry-free** |
| **M2** | `Fredy/CatColimit.lean` | Directed colimit of **categories** on our `Cat` | ✅ **DONE, sorry-free** |
| **M2a** | ↑ | `CatSystem` structure + object-colimit (reuses M1) | ✅ done |
| **M2b** | ↑ | hom-colimit + `Cat` instance + category laws | ✅ done |

### M2 — COMPLETE (sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound})
`CatColimit.lean` now builds the directed colimit of categories as a genuine `Cat`:
`CatSystem` + `Coherent`, object-colimit (`Obj`/`objIncl`), hom-colimit (`homTr` + laws, `HomColim`),
chosen-rep morphisms (`colimOut`/`colimHom`/`colimId`), composition (`homCompRaw` → `colimComp`, well-defined
via `homCompRaw_wd` from `push_left`/`push_right`), identity laws, associativity (`colimComp_assoc`), and the
instance `colimitCat : Cat (C.Obj)`. (`Classical.choice` enters via `colimOut` picking representatives —
acceptable since §1.543 needs choice anyway.)

### M3 design note (next)
For the colimit to inherit terminal/products/pullbacks/covers, the transition functors must *preserve* them
(so they're computed at a finite stage and survive the colimit).  So `CatSystem` (or a `RegularCatSystem`
extending it) must carry "each `functF` preserves the regular structure" hypotheses — true for the
capitalization slice embeddings.  First tractable piece: the colimit has a **terminal object** (= colim of the
stagewise terminals, transitions preserving it).
| **M3** | `Fredy/CatColimitRegular.lean` | colimit preserves terminal / products / pullbacks / covers ⇒ `PreRegularCategory` | ◧ in progress |
| M3a/b | ↑ | terminal + binary products | ✅ done, sorry-free |
| M3-eq | ↑ | **`colimitHasEqualizers` — DONE sorry-free**; ⇒ pullbacks via §1.432 | ✅ done |
| M3-cov | ↑ | cover-transfer (`PullbacksTransferCovers`) ⇒ assemble `PreRegularCategory` | ◧ foundations done |

### M3-cov progress / plan
Foundation lemmas DONE sorry-free in `CatColimitRegular.lean`:
- `colimHom_isIso_of_rep` — stage iso ⇒ `colimitCat` iso (iso preservation).
- `homIncl_injective` — `homIncl` injective on homs given **faithful transitions** (`hfaith`).
- `colimHom_mono_of_rep` — stage-mono-under-transitions ⇒ `colimitCat` mono (mono preservation).

DONE additionally: `homInclObj` (stage-inclusion on morphisms, keystone), `castHom_injective`,
`homInclObj_injective` (the stage-inclusion is FAITHFUL given faithful transitions).

Remaining (each ~40–80 lines, fights the `colimOut` rep transport):
0. **`homInclObj` functoriality** (`homInclObj (g≫g') = homInclObj g ≫ homInclObj g'`). ✅ **DONE,
   sorry-free** (`homInclObj_comp`). Resolved via fix (b): the representative-independence lemma
   `homInclObj_eq` (build a common stage `L` where all three reps agree, compute each inclusion at a
   shared witness there) plus `homInclObj_germ_push`. Functoriality then reduces `colimComp` to
   `homCompRaw` at `L` (`homCompRaw_eq_compAt` + `homTr_refl`) and matches germs via `castHom_comp` +
   `map_comp`. KEY GOTCHA: do NOT `show`/re-state the germ composition `w_xy.germ g ≫ w_yz.germ g'`
   — re-elaboration fails to unify the middle object (proof-irrelevance on let-bound witness `.K`
   fields); instead `dsimp only [HioWitness.germ]` then `rw [castHom_comp, ← map_comp]` directly on
   the goal, leaving two `UpperBound`s that agree definitionally by proof irrelevance.
2. **Mono reflection** `colimitCat` mono ⇒ stage-mono-under-transitions. ✅ **DONE, sorry-free**
   (`colimHom_mono_reflects`, axioms {propext, Classical.choice, Quot.sound}). Exact converse of
   `colimHom_mono_of_rep`: include the stage maps `u,v` as `colimitCat` maps `objIncl j z ⟶ A` at
   the rep-agreement stage `s` of `objIncl j z` (from `Quotient.exact (colimOut_spec …)`); composing
   with `homIncl a f₀` reduces (`homCompRaw_eq_compAt` + `homTr_refl` + `castHom_comp` + `map_comp`,
   the `f₀`-push split via `hC.trans_map`) to `functF.map (u ≫ functF.map f₀)`, so the colimit mono
   gives `U=V`; then `homIncl_injective` + `castHom_injective` + faithfulness strip back to `u=v`.
3. **Cover reflection / preservation** (cover = factor-through-mono ⇒ uses 2).
4. **Assembly**: arbitrary pullback cone ≅ canonical (§1.432) so `Cover` is iso-invariant; reflect
   `f`/pullback to a stage, stage `PullbacksTransferCovers`, preserve back ⇒ `PullbacksTransferCovers C.Obj`;
   bundle with terminal+products+pullbacks ⇒ `PreRegularCategory C.Obj`.
`colimitPullbacksTransferCovers` will carry "transitions faithful + preserve covers/monos/pullbacks"
hypotheses (satisfied by the slice embeddings: `slice_embedding_separates` gives faithfulness).
| **M4** | `Fredy/S1_546.lean` | relative-capitalization functor `A ↦ A*` (slices), `IsRelativeCapitalization` witness | ☐ |
| **M5** | `Fredy/S1_543.lean` | ordinal-indexed iteration of M4; fixed-point/cardinality ⇒ capital (imports mathlib `Ordinal`) | ☐ hard |
| **M6** | `Fredy/S1_54.lean` | assemble: `Ā` = colimit; prove `Capital` + faithful `A → Ā`; discharge `capitalization_lemma` | ☐ |

### M3 next step — `colimitHasEqualizers` (validated spec)

M3a (`colimitHasTerminal`) and M3b (`colimitHasBinaryProducts`) are DONE sorry-free in
`CatColimitRegular.lean`. **Pullbacks need NOT be built directly:** §1.432
`products_equalizers_implies_pullbacks` (in `S1_43.lean`) assembles `HasPullbacks` from
terminal + binary products + equalizers. So M3-limits reduces to **`colimitHasEqualizers`**,
then `HasPullbacks (C.Obj) := { has := fun f g => products_equalizers_implies_pullbacks f g }`.

Validated signature (mirror of `colimitHasBinaryProducts`; the two hypotheses say the
transition functors preserve equalizers — true for the slice embeddings of M4):

```lean
noncomputable def colimitHasEqualizers (C : CatSystem ι D) (hC : C.Coherent)
    (he : ∀ i, HasEqualizers (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hpres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k) :
    @HasEqualizers C.Obj (colimitCat C hC)
```

Construction: given parallel `F G : colimHom C hC X Y`, `Quotient.inductionOn` both to
representatives, lift to a common stage `k` (via `D.bound`, `homTr`, `C.F`, `castHom` — exactly
as products lifts `f,g` to the product legs), take the stage equalizer `eqObj fk gk`, include via
`objIncl`/`homIncl`; `hpres` gives `uniq`, `hpres_lift` gives `lift`/`fac`. Reuse the
`hDirSubsingleton`/`hF_proof_irrel`/`cR`/`cT` cast-slide patterns from products.

## Honest risk

M2b, M3, M5 are the walls. M3 (a filtered colimit of pre-regular categories is pre-regular — finite limits and
covers are computed at finite stages) is the deepest piece and is real mathematics, not glue. This is a
multi-session effort; each milestone lands sorry-free and is verified by `lake build` before the next starts.
`colimitHasEqualizers` is ~250 lines of `castHom`/`Quotient` work mirroring the proven products theorem.

## Process

Implementation is delegated to DeepSeek subagents (`claude-deepseek.sh`) against precise specs with reference
code; every milestone's build + axiom-cleanliness is independently verified here before acceptance.
