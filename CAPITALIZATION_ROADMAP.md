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

NEXT: assemble `homSystem C hC x y : System (UpperBound D i j) (upperDirected D i j)`:
- `X a := (C.F a.2.1 x) ⟶ (C.F a.2.2 y)` (in `C.A a.1`);
- `tr hab g := castHom hSrc hTgt ((C.functF hab).map g)` with `hSrc := (C.F_trans a.2.1 hab x).symm`
  (defeq-coerced to `… = C.F b.2.1 x` via proof-irrelevant le), `hTgt` likewise on `y`;
- `tr_refl := castHom_of_heq _ _ (hC.refl_map g)`;
- `tr_trans` via `hC.trans_map` + `map_castHom` + `castHom_castHom`.
Then `HomColim C hC x y := Colimit (homSystem …)`. After that: rep-independence over object classes,
composition, identity, category laws (the `Cat` instance on `CatSystem.Obj`).
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
