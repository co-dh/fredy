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
| **M3** | `Fredy/CatColimitRegular.lean` | colimit preserves terminal / products / pullbacks / covers ⇒ `PreRegularCategory` | ☐ hard |
| **M4** | `Fredy/S1_546.lean` | relative-capitalization functor `A ↦ A*` (slices), `IsRelativeCapitalization` witness | ☐ |
| **M5** | `Fredy/S1_543.lean` | ordinal-indexed iteration of M4; fixed-point/cardinality ⇒ capital (imports mathlib `Ordinal`) | ☐ hard |
| **M6** | `Fredy/S1_54.lean` | assemble: `Ā` = colimit; prove `Capital` + faithful `A → Ā`; discharge `capitalization_lemma` | ☐ |

## Honest risk

M2b, M3, M5 are the walls. M3 (a filtered colimit of pre-regular categories is pre-regular — finite limits and
covers are computed at finite stages) is the deepest piece and is real mathematics, not glue. This is a
multi-session effort; each milestone lands sorry-free and is verified by `lake build` before the next starts.

## Process

Implementation is delegated to DeepSeek subagents (`claude-deepseek.sh`) against precise specs with reference
code; every milestone's build + axiom-cleanliness is independently verified here before acceptance.
