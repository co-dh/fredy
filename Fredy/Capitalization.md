# §1.543 Capitalization — assembly tracker

File: `Fredy/Capitalization.lean`

Assembles the §1.543 capitalization lemma from the directed-colimit-of-categories machinery
(`CatColimit.lean` / `CatColimitRegular.lean`).  Category theory stays on this repo's own
`Cat`; the file is mathlib-free (the §1.543 mathlib-ordinal exception in `CLAUDE.md` is
available but unused — the colimit machinery is `Directed`-indexed, not ordinal-indexed, and
mathlib is not a dependency of this repo).

## Universe note

The `CatSystem`/`colimitCat` machinery forces the object universe to equal the morphism
universe (`catA : Cat.{w} (A i)` with `A i : Type w`).  Hence the capitalization is built for
*small* categories with `Cat.{u}` on `Type u` — exactly Freyd's "small" hypothesis.  All
declarations here, and the final `capitalization_lemma`, are at this diagonal `u = v`.

## What is proved (sorry-free, axiom-clean: only `propext`/`Classical.choice`/`Quot.sound`)

| name                         | statement                                                                                 | status |
|------------------------------|-------------------------------------------------------------------------------------------|--------|
| `faithful_comp`              | composite of faithful functors is faithful (embedding via `S1_31.embedding_comp` + iso-reflection) | DONE |
| `Colim.homInclObj_id`        | the colimit stage-inclusion sends `id` to `id` (`homInclObj (id x) = colimId (objIncl i x)`) | DONE |
| `Colim.stageInclFunctor`     | the stage inclusion `A i → Ā` packaged as an honest `Functor` (`objIncl i`, `homInclObj`)  | DONE |
| `Colim.stageInclFaithful`    | that stage-inclusion `Functor` is `Faithful`, given transitions faithful + conservative    | DONE |
| `Colim.stageIncl_separates`  | embedding half (`homInclObj_injective`)                                                     | DONE |
| `Colim.stageIncl_reflectsIso`| reflects-iso half (`homInclObj_isIso_reflects`)                                             | DONE |
| `CapData A`                  | bundle of the §1.543 transfinite-construction output (system + preservation + capital)     | DONE (defn) |
| `capitalization_of_capData`  | **from a `CapData A`, derive capital pre-regular `Ā` + faithful `A → Ā`** — the colimit packaging | DONE |
| `capitalization_lemma_small` | the §1.543 lemma, reduced to `capData_exists`                                               | DONE (modulo the one sorry) |

`capitalization_of_capData` is the heart of the packaging: it applies `colimitPreRegular`
(colimit of pre-regular cats is pre-regular), takes the bundled `capital` proof, and builds
the faithful representation `A → Ā = objIncl i₀ ∘ base` via `faithful_comp` of the bundled
faithful base embedding with `stageInclFaithful`.

## ω-tower scaffolding for `capData_exists` (all sorry-free)

These were added to materially advance the residual transfinite construction.  The successor
level of Freyd's recursion is an ω-tower (`A₀ = A`, `A_{n+1} = (A_n)*`); the pieces below build
its index, stages, and iterated transitions, leaving only the cast-coherence / preservation-
lifting / capital-closure as the residual (see `capData_exists` docstring).

| name                | statement                                                                                     | status |
|---------------------|-----------------------------------------------------------------------------------------------|--------|
| `Colim.natDirected` | `ℕ` (`Nat`) as a `Directed` preorder (max as common upper bound)                              | DONE |
| `uliftNatDirected`  | `ULift.{u} Nat` as a `Directed` preorder — the `Type u` index the colimit machinery needs     | DONE |
| `CapStep S`         | the single successor-step interface: a faithful, pre-regular-target functor `S → T = S*`      | DONE (defn) |
| `PreRegBundle`      | a bundled small pre-regular category (carrier + `Cat` + `PreRegularCategory`) for `Nat.rec`   | DONE (defn) |
| `stageBundle`       | the `n`-th stage of the tower, by `Nat.rec` on a uniform successor `nextStep` (`stage 0 = A`)  | DONE |
| `stageStep`         | the single-step functor `stage n → stage (n+1)` (= bundled `CapStep.step`)                     | DONE |
| `transN`            | the iterated transition `stage n → stage (n+d)`, by recursion on the difference `d`            | DONE |
| `transNFun`         | `transN n d` is a `Functor` (composite of the `d` rung functors)                              | DONE |
| `transNFaithful`    | **`transN n d` is `Faithful`** (composite of faithful rungs via `faithful_comp`)              | DONE |
| `towerObj`          | object family of the tower `CatSystem`: `i ↦ (stageBundle b i.down).carrier`                   | DONE |
| `towerF`            | the `≤`-indexed transition `towerObj i → towerObj j`, casting `transN i (j-i)` along `i+(j-i)=j` | DONE |

`transNFaithful` is the key sorry-free advance: once the `CatSystem` is assembled, it
discharges the `hfaith`/`hcons` fields of `CapData` directly (every iterated transition is
faithful, hence conservative).

## The single remaining `sorry`

`Freyd.capData_exists : (A : Type u) [Cat.{u} A] [PreRegularCategory A] → Nonempty (CapData A)`

This is the genuine wall — the transfinite construction itself.  Freyd: `A₀ = A`,
`A_{α+1} = (A_α)*` (relative capitalization §1.545: the directed union over well-supported `B`
of the slices `A_α/B`, faithful pre-regular by §1.544 `slice_embedding_separates`),
`A_λ = colim_{β<λ} A_β`; closes at a regular cardinal `κ > |A|`.  Packaging it as a `CapData`
requires three substantial sub-steps, none a one-lemma gap:

1. **Type-level transfinite recursion** whose limit-stage *type* is the colimit of its
   predecessors (`colimitCat`) — producing the `ι` / `D` / `CatSystem` of the tower.
2. **The slice successor functor** `A_α → (A_α)*` as a coherent, faithful, pre-regular-
   preserving `CatSystem` transition.  Blocker: `PreRegularCategory (Over B)` is not yet
   established — `S1_44` gives `Over B` its `HasTerminal` and `HasPullbacks`, but
   `HasBinaryProducts (Over B)` and `PullbacksTransferCovers (Over B)` are still missing.
3. **The capital-closure proof** (`CapData.capital`): every well-supported object of the
   colimit appears at some stage `α<κ`, gets a point at `α+1`, and the point survives to the
   colimit by cover reflection.  The reflection lemmas it needs (`colimHom_cover_reflects`,
   `homInclObj_cover_reflects`) are already proved in `CatColimitRegular`.

The hard "colimit of pre-regular categories is pre-regular" (`colimitPreRegular`) and the
faithful stage-injection (`stageInclFaithful`) are already in hand, so this `CapData`
existence is precisely the residual obligation.

### Current state of the residual (after the ω-tower scaffolding)

The scaffolding table above reduces sub-step (1) to a single concrete obstruction:
**assembling `towerObj`/`towerF` into a `CatSystem (ULift Nat) uliftNatDirected`**.  `towerF` is
defined sorry-free, but its `CatSystem` laws (`F_refl`, `F_trans`) and `Coherent`
(`refl_map`/`trans_map`) require eliminating the `Nat`-difference cast `i + (j - i) = j` inside a
dependent motive — the classic "motive is not type correct" heterogeneous-cast bookkeeping.
This is the sharp blocker isolated for sub-step (1); it is mechanical but cast-heavy, and was
not completed here.  Sub-step (2) (preservation lifting to arbitrary `i ≤ j`) and sub-step (3)
(capital closure + the `nextStep` slice-successor needing `PreRegularCategory (Over B)`) remain
as stated.  `transNFaithful` already discharges `hfaith`/`hcons` once the system exists.
