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
| **M2** | `Fredy/CatColimit.lean` | Directed colimit of **categories** on our `Cat` | ▶ in progress |
| **M2a** | ↑ | `CatSystem` structure + object-colimit (reuses M1) | ▶ delegated |
| **M2b** | ↑ | hom-colimit + `Cat` instance + category laws | ◐ in progress |

### M2b resume point (sorry-free so far)
Built in `CatColimit.lean`: `CatSystem.Coherent` (HEq morphism-coherence), `UpperBound`/`upperDirected`
(hom-colimit index), `castHom`, `castHom_of_heq`, `castHom_castHom`, `map_castHom`.

DONE (sorry-free, axioms ⊆ {propext, Quot.sound}): `homTr`, `homTr_refl`, `homTr_trans` (cast-heavy law
via `map_castHom`+`castHom_castHom`+`castHom_heq_congr`+coherence), `homSystem`, `HomColim` — the
hom-colimit for *fixed representatives* `x : C.A i`, `y : C.A j`.

NEXT (M2b-rest — the remaining wall): turn `HomColim` into a `Cat` instance on `CatSystem.Obj`.
- rep-independence: `Hom([⟨i,x⟩],[⟨j,y⟩])` must not depend on chosen reps. Per-rep `HomColim`s are
  canonically *isomorphic* but not *equal*, so `Quotient.lift₂` to `Type` doesn't apply directly. Likely
  define the colimit Hom as a single 2-sided germ quotient over all reps rather than "fix reps + show iso".
- then identity (`incl` of `id`), composition (push two morphisms to a common bound, compose, include),
  category laws, and finally the `Cat (CatSystem.Obj C)` instance.
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
