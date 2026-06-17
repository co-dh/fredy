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

## The remaining `sorry`s — the ONE bundled `hwall` is now SPLIT into two named walls

`Freyd.capData_exists : (A : Type u) [Cat.{u} A] [PreRegularCategory A] → Nonempty (CapData A)`

The proof invokes `capData_of_tower`.  The previously single, opaque bundled existential `hwall`
has been **decomposed into two separately-stated sub-obligations, with the dependency between
them made explicit** (the capital closure is now stated *over* the colimit's concrete
pre-regular structure, which the successor's package supplies).  This is the real reduction:
two independently-attackable targets instead of one bundle.

### WALL 1 — `hwall_step` (line ~907): the uniform pre-regular-preserving SUCCESSOR

An existential producing `nextStep : ∀ S, CapStep S.carrier` **together with the full ω-tower
preservation package** (`ht`/`htpres`/`hp`/`hppres`/`hppres_pair`/`he`/`hepres`/`hepres_lift`/
`hcanon`).  This is Freyd's relative capitalization `A ↦ A*`: glue the slices `A/B` over
well-supported `B`, *adding a point* (generic element `1 → B`) per well-supported object.

- **Inputs available (do NOT re-prove):** `Freyd.overPreRegular` (`A/B` is pre-regular,
  `SliceRegular.lean`); §1.544 `slice_embedding_separates` (one slice step `(-)×B` separates
  morphisms — note: this is the *endofunctor* `prodRight B`, an `Embedding`, it does not by
  itself add a point); `Freyd.sliceCapStep B hws : CapStep S` (the per-`B` faithful pre-regular
  rung, sorry-free, `RelativeCapitalization.lean`); the `CatColimit`/`CatColimitRegular` machinery
  for the `A*` colimit-of-slices.
- **§1.547 facts now built sorry-free** (`RelativeCapitalization.lean`, this wave): the choice-free
  relative capitalization is the *directed union of product-slices* `A* | U = A/(∏U)` over finite
  sets `U` of well-supported objects (transition `A/(∏V) → A/(∏U)` for `V ⊆ U` = slice embedding).
  The point a product-slice rung adds for a factor `B ∈ U` is read off the projection `∏U → B`:
  - `sliceFactorPoint B (g : P ⟶ B) : OverHom (overTerm P) (sliceEmbedObj P B)` — the point of
    `sliceEmbedObj P B` in `A/P` along any `g`, underlying arrow `pair g id_P`;
  - `sliceAcquiresFactorPoint B g` — it IS a point (`. f ≫ hom = overTerm.hom`);
  - `prodSliceAcquiresBothFactors B B'` — the two-factor crux: the SINGLE slice `A/(B×B')` points
    BOTH factors (along `fst`, `snd`), so one rung over `∏U` simultaneously points every member.
  These generalize `sliceGenericPoint`/`sliceAcquiresPoint` (the `P = B`, `g = id` diagonal case).
- **Residual (the genuine wall — irreducible without the inner colimit):** assemble, *uniformly in
  `S`*, the inner finite-product-slice `CatSystem` (index = finite sets of well-supported objects)
  and discharge its `colimitPreRegular` hypotheses — **including the inner `hcanon`**.  This is the
  crux of why the sorry persists: `colimitPreRegular` on the inner system demands its OWN inner
  pullback-cover preservation, so building `nextStep` honestly RECURSES into the very same
  `colimitPreRegular` package `hwall_step` produces for the outer ω-tower (a full second copy of
  `towerSystem`/`capData_of_tower` over the finite-set index).  Then lift the single-step
  finite-limit preservation to the arbitrary `i ≤ j` outer tower package by rung composition.  A
  trivial inhabitant (`T := S`, `step := id`) is honest as a `CapStep` but makes WALL 2 *false*
  (constant tower never becomes capital) — confirming the wall is real and cannot be shortcut.

### WALL 2 — `hwall_cap` (line ~924): the CAPITAL CLOSURE (§1.543 fixpoint)

`hcap : Capital (𝒞 := (towerSystem b nextStep).Obj)`, stated *after* `obtain`ing WALL 1 and
introducing the colimit's `Cat` + `PreRegularCategory` instances (exactly the ones
`capData_of_tower`/`colimitPreRegular` use).  Every well-supported object of `Ā` is
well-pointed: it appears at a finite stage `n`, the successor (WALL 1) puts a point on it at
stage `n+1`, and the point survives the colimit because the stage inclusion REFLECTS covers.

- **Inputs available (do NOT re-prove):** `colimHom_cover_reflects` / `homInclObj_cover_reflects`
  (`CatColimitRegular`, both proved).
- **Residual:** the fixpoint argument that the finite-stage point witnesses well-pointedness in
  `Ā`.  This obligation *consumes* WALL 1's `nextStep`/package — it is genuinely nested under it
  (which is why the two were originally bundled into one `sorry`).

Everything else in `capData_exists` — the re-packaging into `capData_of_tower`, all the instance
plumbing — is sorry-free.  `hwall` is thus **reduced (not closed)**: from one opaque existential
to two sharp, documented, separately-attackable sorries with their dependency exposed.
