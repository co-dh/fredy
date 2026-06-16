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

## CatSystem assembly — sub-step (1) now COMPLETE (sorry-free, `propext`/`Quot.sound`-only)

The `Nat`-difference cast `i + (j - i) = j` is handled by a layer of carrier-cast helpers, so
`towerF` becomes an honest `≤`-indexed `CatSystem.F` with full coherence — no "motive is not
type correct" remains.  All of the following are sorry-free and **constructive** (axiom-clean:
`towerSystem`/`towerCoherent` use only `propext`/`Quot.sound`, no `Classical.choice`).

| name                       | statement                                                                                        | status |
|----------------------------|--------------------------------------------------------------------------------------------------|--------|
| `stageCast`/`stageCastHom` | transport an object / morphism across the stage-carrier equality `stage m = stage n` for `m = n` | DONE |
| `stageCast_heq`/`stageCastHom_heq` | the transports are `HEq` to the original (the coherence engine)                          | DONE |
| `stageCastHom_id`/`_comp`/`_injective`/`_isIso_reflects` | the morphism transport is functorial and an iso              | DONE |
| `stageStep_stageCast`      | the successor rung commutes with the stage-cast                                                   | DONE |
| `transN_add`               | object additivity `transN n (d+e) = transN (n+d) e ∘ transN n d` (mod carrier id)                | DONE |
| `transN_add_heq`/`transN_congr_heq` | additivity / base-congruence in `HEq` form                                              | DONE |
| `transNFun_map_add`        | **morphism** additivity of the difference functor (HEq), by induction on `e`                      | DONE |
| `transNFun_map_congr_heq`/`stageStepFun_map_congr_heq` | `.map` respects `HEq` of args at carrier-equal stages          | DONE |
| `towerFmap`/`towerFunctF`  | the `≤`-transition's morphism map and its `Functor` structure (cast of `transNFun`)               | DONE |
| **`towerSystem`**          | **the ω-tower as a `CatSystem.{u,u} (ULift Nat) uliftNatDirected`** (`F_refl`/`F_trans` via the casts) | DONE |
| **`towerCoherent`**        | **its `Coherent` proof** (`refl_map`/`trans_map`) — both from the `HEq`-transparency principle    | DONE |
| `towerHfaith`/`towerHcons` | the tower transitions are faithful/conservative (cast-drop + `transNFaithful`)                    | DONE |
| **`capData_of_tower`**     | **assembles a full `CapData A`** from `towerSystem` + the preservation package + capital closure   | DONE |

`capData_of_tower` is the new packaging endpoint: it takes a uniform successor `nextStep`, the
`colimitPreRegular` preservation hypotheses for the tower, and the capital-closure proof, and
returns `CapData A` with `base = id` (stage 0 is `A`), `hfaith`/`hcons` discharged by
`towerHfaith`/`towerHcons`.  Everything categorical is now closed.

## The single remaining `sorry` (reduced to two bundled walls)

`Freyd.capData_exists : (A : Type u) [Cat.{u} A] [PreRegularCategory A] → Nonempty (CapData A)`

The proof now invokes `capData_of_tower`, so the only `sorry` is a **single bundled existential
`hwall`** producing exactly the two genuine §1.543 inputs `capData_of_tower` consumes:

1. **The uniform pre-regular-preserving successor** `nextStep : ∀ S, CapStep S` (§1.544/§1.545
   slice successor `A ↦ A/B`, now buildable from `overPreRegular = PreRegularCategory (Over B)`
   in `SliceRegular.lean` + the §1.544 separation), **together with the per-`i ≤ j` preservation
   package** for its tower (`ht`/`htpres`/`hp`/`hppres`/…/`hcanon`) — i.e. lifting the single-rung
   preservation to arbitrary `i ≤ j` by composing rungs.
2. **The capital closure** of the tower's colimit (§1.543 fixpoint: every well-supported object
   appears at a finite stage `n`, gets a point at `n+1`, and the point survives by cover
   reflection `colimHom_cover_reflects`/`homInclObj_cover_reflects`, already proved in
   `CatColimitRegular`).

Both are bundled into the one `hwall` existential; everything downstream of it is sorry-free.
`PreRegularCategory (Over B)` (previously the blocker for the successor) is now available as
`Freyd.overPreRegular`, so wall (1) is unblocked at the interface level — what remains is the
explicit slice-successor construction and the rung-composition preservation lift.
