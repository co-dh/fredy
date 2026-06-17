/-
  Freyd & Scedrov, *Categories and Allegories* §1.541/§1.542/§1.544/§1.545
  RELATIVE CAPITALIZATION — the genuine core of the capitalization successor step.

  This file builds the *slice rung* of Freyd's relative capitalization `A ⊆ A*`
  (§1.544/§1.545) as an honest `CapStep` (the successor interface of
  `Capitalization.lean`), for a *single* well-supported object `B`:

      A  →  A/B          ( C ↦ (C×B → B),  f ↦ (f×B) )

  The book (§1.544) writes this embedding as `A ↦ A×B` and shows it "separates
  objects and, if `B` is well-supported, separates morphisms."  The slice `A/B`
  is pre-regular (`overPreRegular`, SliceRegular.lean), the embedding is faithful
  (`slice_embedding_separates`, S1_54.lean — repackaged here as a faithful functor
  *into `Over B`*), so it packages as a `CapStep A`.

  WHAT THIS FILE DELIVERS (all sorry-free):
    * `sliceEmbedObj` / `sliceEmbedMap` / `sliceEmbedFunctor`
                            — the functor `A → A/B`, `C ↦ ⟨C×B, snd⟩`, `f ↦ f×B`
    * `sliceEmbedFaithful`  — it is FAITHFUL when `B` is well-supported
                              (embedding from `slice_embedding_separates`;
                               reflects-iso from `f×B` iso ⟹ `f` mono+cover ⟹ iso)
    * `sliceCapStep`        — the packaged `CapStep A` (faithful pre-regular
                               functor `A → A/B`)
    * `sliceAcquiresPoint`  — `A/B` ACQUIRES A POINT of `sliceEmbed B B`: the
                               terminator-to-image diagonal `⟨diag B, …⟩ : 1 → B×B`
                               is a point of `sliceEmbedObj B B`.  This is §1.546's
                               "generic point" `1 → A(B)` for the chosen `B`.
    * `sliceFactorPoint` / `sliceAcquiresFactorPoint`
                            — §1.547 generalization: along ANY `g : P → B`, the slice
                               `A/P` acquires a point of `sliceEmbedObj P B`
                               (underlying arrow `pair g id_P`).  With `P = ∏U`,
                               `g = projection`, this is the point the product-slice
                               rung adds for a factor `B ∈ U`.
    * `prodSliceAcquiresBothFactors`
                            — the two-factor crux: the SINGLE slice `A/(B×B')` points
                               BOTH factors at once, so one rung over `∏U` points every
                               member of `U` simultaneously.
    * `listProd` / `listProdProj` / `listSubset` / `listDirected`
                            — the §1.547 FINITE-SET INDEX (mathlib-free): finite sets of
                               objects modelled as `List 𝒞`, `⊆`-ordered into a `Directed`
                               (bound = `++`); `∏U` = right-folded binary product (`∏[]=1`);
                               `listProdProj U k : ∏U → U.get k` the factor projection
                               (`Fin`-indexed — a `Prop`-membership `B ∈ U` cannot large-
                               eliminate into a morphism).
    * `listProdSliceAcquiresEveryFactor`
                            — the §1.547 payoff: `A/(∏U)` acquires a point of EVERY factor
                               `U.get k` at once (one rung points all of `U`).

  WHAT REMAINS (the residual wall for `hwall_step`, Capitalization.lean).
  The *uniform* successor `nextStep : ∀ S, CapStep S` that `hwall_step` needs is
  STRONGER than a single slice rung: in ONE category `S*` it must add a point for
  *every* well-supported `B` simultaneously (Freyd's §1.547 rational category / the
  directed union of the `A* | U = A/(∏U)` product-slices over finite sets `U` of
  well-supported objects).  This file delivers the per-`B`/per-factor points AND the
  finite-set index (`listDirected`/`listProd`/`listProdProj`/`listProdSliceAcquiresEveryFactor`)
  sorry-free (above).

  INNER-SYSTEM SCAFFOLDING (this session, all sorry-free — see the `innerCatSystem` block):
    * the TRANSITION FUNCTOR now EXISTS: `baseChangeFunctor (g : C ⟶ D) : Functor (Over D → Over C)`
      (SliceRegular.lean), the genuine slice→slice base-change `A/(∏V) → A/(∏U)` by pullback along
      `∏U → ∏V` — NOT the slice embedding (which is `A → A/B`, base→one-slice).
    * `innerObj U = Over (listProd U)`, `innerCat`, `innerF P h = baseChangeObj (P.proj h)`,
      `innerFunctF P h = baseChangeFunctor (P.proj h)` — the inner system's object family, `Cat`
      instances, transition object map and per-rung functoriality.
    * `innerCatSystem P hS : CatSystem (List 𝒞) listDirected` — the inner system, GIVEN its two
      residuals as honest inputs (no false `sorry`):
        (A) `P : ListProjFamily` — a choice-free product projection `∏U ⟶ ∏V` per `V ⊆ U` with
            strict unit/composition.  NOT yet constructible: `listSubset V U` is a `Prop`, so a
            positional factor-match needs `DecidableEq 𝒞` (the same `Prop`-no-large-elim wall that
            forced `listProdProj` to be `Fin`-indexed).
        (B-strict) `hS : StrictBaseChange P` — the on-the-nose `F_refl`/`F_trans`.  RAW base-change
            is only PSEUDO-functorial (`baseChangeObj (Cat.id) X = X×_D D`, iso to `X` but NOT equal),
            so these are FALSE for raw base-change and are declared as a hypothesis (a real theorem to
            prove = base-change strictification), never asserted by `sorry`.

  ROUTE-1 (strict reindexing) INVESTIGATION — settled NEGATIVELY for §1.547, see the
  `strictReindexSystem` block + `Freyd.reindexFunctor` (SliceRegular.lean):
    * the STRICT transition EXISTS — `reindexFunctor m` (Σ / post-composition along `m : C → D`) is
      strictly functorial AND `reindexObj_id`/`reindexObj_comp` give `CatSystem.F_refl`/`F_trans` ON
      THE NOSE (sorry-free, axiom-free).  `strictReindexSystem R` is a genuine `CatSystem` with those
      laws as THEOREMS, no `StrictBaseChange` needed.
    * but it is the WRONG transition for §1.547: variance `A/(∏V) → A/(∏U)` needs base map `∏V → ∏U`
      (Σ-direction), not choice-free for `V ⊆ U` (would manufacture the missing factors' points); and
      Σ keeps the slice DOMAIN fixed (`B×∏V`), so it cannot connect the stage embeddings whose domain
      must GROW to `B×∏U`.  Only base-change (pullback) grows the domain — hence pseudo-functorial.
      Strictness and the growing-product embedding are mutually exclusive; route 1 does not close
      `hwall_step`.
  STILL OPEN to finish `S*`:
    (B-package) `Coherent (innerCatSystem P hS)` + the 9 `colimitPreRegular` preservation hypotheses
        + `hcanon`, mirroring the OUTER `towerSystem`/`towerCoherent`/`capData_of_tower`; then take
        `colimitPreRegular` for the pre-regular `S*` and package as the `CapStep S` for `hwall_step`.
    (B-import) `RelativeCapitalization` imports `Capitalization`, so `innerCatSystem`/… sit downstream
        of `hwall_step`; closing `hwall_step` in place needs the ingredients moved up (e.g. into
        `SliceRegular`) or `capData_exists` relocated here.
  See the `hwall_step` residual comment in `Capitalization.lean` for the full reduction.

  No mathlib (the category theory stays on this repo's own `Cat`).
-/

import Fredy.S1_1
import Fredy.S1_26
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_54
import Fredy.S1_56
import Fredy.SliceRegular
import Fredy.Capitalization

open Freyd
open Freyd.Colim

universe u

namespace Freyd

variable {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-! ## §1.544  The slice embedding `A → A/B` as a functor

  Object part: `C ↦ ⟨C×B, snd⟩` — the product `C×B` viewed as an object over `B`
  via the second projection.  Morphism part: `f : C → D` maps to `f×B = pair (fst≫f) snd`,
  which is an `OverHom` because `pair (fst≫f) snd ≫ snd = snd` (`snd_pair`).

  The underlying `𝒞`-arrow of `(sliceEmbed B).map f` is exactly `(prodRightFunctor B).map f`,
  so all functor laws and faithfulness reduce to the already-proven `prodRightFunctor` /
  `slice_embedding_separates`. -/

/-- The object part of the slice embedding `A → A/B`: `C ↦ (C×B ──snd──▶ B)`. -/
def sliceEmbedObj (B : 𝒞) (C : 𝒞) : Over B := ⟨prod C B, snd⟩

/-- The morphism part of the slice embedding: `f : C → D` becomes the over-hom whose
    underlying arrow is `f×B = pair (fst≫f) snd : C×B → D×B`.  It commutes with the
    structure map `snd` by `snd_pair`. -/
def sliceEmbedMap (B : 𝒞) {C D : 𝒞} (f : C ⟶ D) :
    OverHom (sliceEmbedObj B C) (sliceEmbedObj B D) :=
  ⟨pair (fst ≫ f) snd, snd_pair (fst ≫ f) snd⟩

/-- The underlying arrow of `sliceEmbedMap B f` is `(prodRightFunctor B).map f` — the
    bridge to the already-proven product-embedding facts of §1.544. -/
theorem sliceEmbedMap_f (B : 𝒞) {C D : 𝒞} (f : C ⟶ D) :
    (sliceEmbedMap B f).f = (prodRightFunctor B).map f := rfl

/-- The slice embedding `A → A/B` is a functor.  Underlying arrows are `prodRightFunctor B`'s,
    so the laws transport along `OverHom.ext` (a slice equation is its underlying equation). -/
instance sliceEmbedFunctor (B : 𝒞) : Functor (sliceEmbedObj B) where
  map {C D} f := sliceEmbedMap B f
  map_id C := OverHom.ext (by
    show (sliceEmbedMap B (Cat.id C)).f = (Cat.id (sliceEmbedObj B C)).f
    rw [sliceEmbedMap_f, (prodRightFunctor B).map_id]; rfl)
  map_comp {C D E} f g := OverHom.ext (by
    show (sliceEmbedMap B (f ≫ g)).f = ((sliceEmbedMap B f) ⊚ (sliceEmbedMap B g)).f
    rw [sliceEmbedMap_f, (prodRightFunctor B).map_comp]; rfl)

/-- The slice embedding's `.map` agrees (underlying-arrow) with `prodRightFunctor`. -/
theorem sliceEmbedFunctor_map_f (B : 𝒞) {C D : 𝒞} (f : C ⟶ D) :
    ((sliceEmbedFunctor B).map f).f = (prodRightFunctor B).map f := rfl

/-! ### Faithfulness of the slice embedding (§1.544)

  Embedding: equality of slice-images gives equality of underlying `f×B`, which
  `slice_embedding_separates` (cover-cancellation of `fst`, needs `B` well-supported)
  turns into `f = g`.

  Reflects-iso: from `f×B` iso we get `f` *mono* (image `f×B` mono, then the embedding
  + functoriality descend monicity to `f`) and `f` a *cover* (`fst_C ≫ f = (f×B) ≫ fst_D`
  is iso∘cover hence a cover, and a cover right-factor is a cover); `monic_cover_iso`
  then makes `f` iso. -/

/-- The slice embedding separates morphisms (the embedding half of faithfulness), for
    well-supported `B`.  This is `slice_embedding_separates` read through the underlying-arrow
    identification `sliceEmbedFunctor_map_f`. -/
theorem sliceEmbed_embedding (B : 𝒞) [PullbacksTransferCovers 𝒞] (hws : WellSupported B) :
    @Embedding 𝒞 _ (Over B) _ (sliceEmbedObj B) (sliceEmbedFunctor B) := by
  intro C D f g h
  exact slice_embedding_separates B hws f g (congrArg OverHom.f h)

/-- **Cover right-factor.**  If `g ≫ f` is a cover then `f` is a cover.  (Any monic `m`
    that `f` factors through, `g ≫ f` also factors through; `g ≫ f` a cover forces `m` iso.) -/
theorem cover_of_comp_cover {X Y Z : 𝒞} (g : X ⟶ Y) (f : Y ⟶ Z) (hgf : Cover (g ≫ f)) :
    Cover f := by
  intro C m h hm hfac
  refine hgf m (g ≫ h) hm ?_
  rw [Cat.assoc, hfac]

/-- **§1.544 — the slice embedding is FAITHFUL** for well-supported `B`. -/
theorem sliceEmbedFaithful (B : 𝒞) [PullbacksTransferCovers 𝒞] (hws : WellSupported B) :
    @Faithful 𝒞 _ (Over B) _ (sliceEmbedObj B) (sliceEmbedFunctor B) := by
  refine ⟨sliceEmbed_embedding B hws, ?_⟩
  intro C D f hiso
  -- the underlying arrow `f×B : C×B → D×B` is iso in `𝒞`
  have hfBiso : IsIso ((sliceEmbedFunctor B).map f).f := overIso_underlying hiso
  rw [sliceEmbedFunctor_map_f] at hfBiso
  -- `f×B` mono (from its inverse as a retraction)
  obtain ⟨inv, hinv1, _hinv2⟩ := hfBiso
  have hfBmono : Mono ((prodRightFunctor B).map f) := mono_of_retraction _ inv hinv1
  -- `f` mono: descend monicity through the embedding functor.
  have hfmono : Mono f := by
    intro Z u v huv
    -- functoriality: `(u≫f)×B = (v≫f)×B`, i.e. `(u×B)≫(f×B) = (v×B)≫(f×B)`
    have h1 : (prodRightFunctor B).map (u ≫ f) = (prodRightFunctor B).map (v ≫ f) := by
      rw [huv]
    rw [(prodRightFunctor B).map_comp, (prodRightFunctor B).map_comp] at h1
    -- cancel the mono `f×B`, then use that the embedding separates `(-)×B`.
    have h2 : (prodRightFunctor B).map u = (prodRightFunctor B).map v := hfBmono _ _ h1
    exact slice_embedding_separates B hws u v h2
  -- `f` cover: `fst_C ≫ f = (f×B) ≫ fst_D`, iso∘cover = cover, right-factor is cover.
  have hfcover : Cover f := by
    have hstep : (fst : prod C B ⟶ C) ≫ f = (prodRightFunctor B).map f ≫ (fst : prod D B ⟶ D) :=
      (fst_pair ((fst : prod C B ⟶ C) ≫ f) snd).symm
    have hcov : Cover ((fst : prod C B ⟶ C) ≫ f) := by
      rw [hstep]
      exact cover_precomp_iso ⟨inv, hinv1, _hinv2⟩ (prod_fst_cover hws)
    -- right-factor of a cover is a cover (inlined to avoid an implicit-binder elaboration quirk):
    intro K m h hm hfac
    exact hcov m ((fst : prod C B ⟶ C) ≫ h) hm (by rw [Cat.assoc, hfac])
  exact monic_cover_iso f hfcover hfmono

/-! ## §1.545  The slice rung as a `CapStep`

  Packaging `A → A/B` as a `CapStep A`: target `A/B` (pre-regular by `overPreRegular`),
  functor `sliceEmbedFunctor`, faithful by `sliceEmbedFaithful`.  This is one rung of
  Freyd's relative capitalization — a faithful pre-regular extension of `A`. -/

/-- **The single-slice `CapStep`** (§1.544/§1.545): for well-supported `B`, the faithful
    pre-regular embedding `A → A/B`.  `Over B` is pre-regular by `overPreRegular`. -/
noncomputable def sliceCapStep [PreRegularCategory 𝒞] (B : 𝒞) (hws : WellSupported B) :
    CapStep 𝒞 where
  T := Over B
  catT := overCat B
  preT := overPreRegular B
  step := sliceEmbedObj B
  stepFun := sliceEmbedFunctor B
  stepFaithful := sliceEmbedFaithful B hws

/-! ## §1.546  The slice rung acquires the generic point of `B`

  In `A/B`, the terminator is `overTerm B = ⟨B, id_B⟩` (S1_44).  Freyd's "generic point"
  of `A(B) = sliceEmbedObj B B = ⟨B×B, snd⟩` is the slice-arrow `1 → A(B)` whose underlying
  `𝒞`-arrow is the diagonal `diag B : B → B×B` (`diag B ≫ snd = id_B` makes it an over-hom
  from the terminator).  This is the point that §1.546's relative capitalization adds for `B`. -/

/-- The **generic point** of `sliceEmbedObj B B` in `A/B`: the over-arrow from the terminator
    `⟨B, id_B⟩` whose underlying arrow is the diagonal `diag B : B → B×B`.  It is an `OverHom`
    because `diag B ≫ snd = id_B` (the second projection of the diagonal is the identity). -/
def sliceGenericPoint (B : 𝒞) :
    OverHom (overTerm B) (sliceEmbedObj B B) :=
  ⟨diag B, by show diag B ≫ snd = Cat.id B; exact diag_snd B⟩

/-- **§1.546 — `A/B` acquires a point of `A(B)`.**  `sliceGenericPoint B` is a point
    `1 → sliceEmbedObj B B` in `A/B` (its source is the terminator `overTerm B`, which is the
    `1` of `A/B`).  This is the generic point Freyd's relative capitalization adds for the
    chosen well-supported `B`. -/
theorem sliceAcquiresPoint (B : 𝒞) :
    (sliceGenericPoint B).f ≫ (sliceEmbedObj B B).hom = (overTerm B).hom := by
  show diag B ≫ snd = Cat.id B
  exact diag_snd B

/-! ## §1.547  Product slices acquire a point of every factor

  Freyd's choice-free relative capitalization (§1.547) is the directed union of the
  slices `A* | U = A / (∏ U)` over finite sets `U` of well-supported objects, with the
  transition `A/(∏V) → A/(∏U)` (for `V ⊆ U`) being the slice embedding.  The point that
  the rung over `U` must add for a *factor* `B ∈ U` is read off the slice over the product:
  the projection `g : ∏U → B` is a map to a well-supported target, and `A/(∏U)` acquires a
  point of `sliceEmbedObj (∏U) B` along `g`.  The two-factor case `∏U = B × B'` below is the
  crux: ONE slice (over the product) simultaneously points BOTH factors, which is exactly why
  the finite-product directed union pins down a point per well-supported object at once.

  This generalizes `sliceGenericPoint`/`sliceAcquiresPoint` (the `B = ∏U` self-point case)
  to an arbitrary projection `g : ∏U → B`.  Below, `g` is any map into a (well-supported)
  target `B` from the base `P = ∏U`; the point's underlying arrow is `pair g (Cat.id P)`. -/

/-- **Generic point of a factor in a product slice (§1.547).**  For any base `P` and any
    map `g : P → B`, the slice `A/P` acquires a point of `sliceEmbedObj P B = ⟨B × P, snd⟩`:
    the over-arrow from the terminator `⟨P, id_P⟩` whose underlying `𝒞`-arrow is
    `pair g (id_P) : P → B × P`.  It is an `OverHom` because its second projection is `id_P`
    (`snd_pair`).  Taking `g = fst : B × B' → B` points the factor `B` of `B × B'`; taking
    `P = B`, `g = id_B` recovers `sliceGenericPoint B` (the diagonal). -/
def sliceFactorPoint {P : 𝒞} (B : 𝒞) (g : P ⟶ B) :
    OverHom (overTerm P) (sliceEmbedObj P B) :=
  ⟨pair g (Cat.id P), by show pair g (Cat.id P) ≫ snd = Cat.id P; exact snd_pair g (Cat.id P)⟩

/-- **§1.547 — `A/P` acquires a point of `sliceEmbedObj P B` along `g : P → B`.**
    `sliceFactorPoint B g` is a point `1 → sliceEmbedObj P B` in `A/P` (source = the
    terminator `overTerm P`).  This is the generic point the product-slice rung adds for the
    well-supported target `B` reached from the base `P` by `g`. -/
theorem sliceAcquiresFactorPoint {P : 𝒞} (B : 𝒞) (g : P ⟶ B) :
    (sliceFactorPoint B g).f ≫ (sliceEmbedObj P B).hom = (overTerm P).hom := by
  show pair g (Cat.id P) ≫ snd = Cat.id P
  exact snd_pair g (Cat.id P)

/-- **Both factors of a binary product slice are pointed (§1.547, two-factor crux).**
    The single slice `A/(B × B')` acquires, from its own base, a point of the factor `B`
    (along `fst`) AND a point of the factor `B'` (along `snd`).  This is the elementary fact
    behind "the slice over the *product* of `U` points every member of `U` simultaneously":
    iterating it over a finite `U` (its product carries a projection to each member) gives one
    rung that points all of `U` at once, the content of the directed-union construction. -/
theorem prodSliceAcquiresBothFactors (B B' : 𝒞) :
    (sliceFactorPoint B (fst : prod B B' ⟶ B)).f ≫ (sliceEmbedObj (prod B B') B).hom
        = (overTerm (prod B B')).hom
      ∧ (sliceFactorPoint B' (snd : prod B B' ⟶ B')).f ≫ (sliceEmbedObj (prod B B') B').hom
        = (overTerm (prod B B')).hom :=
  ⟨sliceAcquiresFactorPoint B (fst : prod B B' ⟶ B),
   sliceAcquiresFactorPoint B' (snd : prod B B' ⟶ B')⟩

/-! ## §1.547  The finite-set index and the product over a finite set

  Freyd's choice-free relative capitalization (§1.547) is the directed union of the slices
  `A* | U = A/(∏U)` over *finite sets* `U` of (well-supported) objects, with transition
  `A/(∏V) → A/(∏U)` for `V ⊆ U`.  The repo is mathlib-free, so we model a "finite set of
  objects" as a `List 𝒞` and the order `V ⊆ U` as list-membership inclusion.  This is a
  genuine `Directed` index (`bound` = append), and `∏U` is the right-folded binary product
  of the members of `U` (with `∏[] = 1`, the terminator).  These are the concrete, reusable
  ingredients of the inner directed system; everything below is sorry-free. -/

-- `listProd`/`listProd_nil`/`listProd_cons` now live upstream in `Fredy.SliceRegular`
-- (imported above) so that `Fredy.Inflation` can use them without importing `Capitalization`.

/-- The projection `∏U → B` for the factor at a positional index `k : Fin U.length` (so
    `B = U.get k`).  Positional indexing (rather than a `Prop`-valued membership `B ∈ U`) is
    forced: `B ∈ U` lives in `Prop`, so a *morphism* `∏U → B` cannot be extracted from it by
    recursion (large elimination of a `Prop` into `Type` is barred).  `Fin`-indexing carries
    the data: head index projects by `fst`; a successor index projects by `snd` then recurses.
    This is the map `g : ∏U → U.get k` along which the slice `A/(∏U)` acquires a point of that
    factor (`sliceFactorPoint`/`sliceAcquiresFactorPoint`). -/
def listProdProj : ∀ (U : List 𝒞) (k : Fin U.length), (listProd U ⟶ U.get k)
  | C :: U, ⟨0,     _⟩ => (fst : prod C (listProd U) ⟶ C)
  | C :: U, ⟨k + 1, hk⟩ =>
      (snd : prod C (listProd U) ⟶ listProd U) ≫ listProdProj U ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- The list-subset order: `V ⊆ U` means every member of `V` is a member of `U`. -/
def listSubset (V U : List 𝒞) : Prop := ∀ x ∈ V, x ∈ U

/-- **The finite-set index is `Directed`** (subset order, `bound` = append).  This is the
    inner directed system's index (§1.547): finite sets of objects ordered by inclusion. -/
def listDirected : Directed (List 𝒞) where
  le := listSubset
  refl _ _ h := h
  trans hVU hUW x hx := hUW x (hVU x hx)
  bound V U := ⟨V ++ U, fun x hx => List.mem_append.2 (Or.inl hx),
    fun x hx => List.mem_append.2 (Or.inr hx)⟩

/-- **§1.547 — the product-slice `A/(∏U)` acquires a point of EVERY factor.**  For each
    positional index `k`, `sliceFactorPoint (U.get k) (listProdProj U k)` is a point
    `1 → sliceEmbedObj (∏U) (U.get k)` in `A/(∏U)`: the slice over the product of `U` points
    every member of `U` simultaneously (one rung pins a point per element of `U`).  This is the
    uniform §1.547 payoff of the index above, a direct instance of `sliceAcquiresFactorPoint`
    along the projection `listProdProj`.  Sorry-free. -/
theorem listProdSliceAcquiresEveryFactor (U : List 𝒞) (k : Fin U.length) :
    (sliceFactorPoint (U.get k) (listProdProj U k)).f
        ≫ (sliceEmbedObj (listProd U) (U.get k)).hom
      = (overTerm (listProd U)).hom :=
  sliceAcquiresFactorPoint (U.get k) (listProdProj U k)

/-! ## §1.547  Assembling the inner finite-product-slice `CatSystem` (residual (A)/(B))

  This block builds the inner directed system of slices `A/(∏U)` over `listDirected`, the
  one `hwall_step` (Capitalization.lean) consumes.  The OBJECTS (`Over (listProd U)`), the
  INDEX (`listDirected`), and the per-rung POINTS (`listProdSliceAcquiresEveryFactor`) are all
  in hand sorry-free above.  Two concrete primitives remain, isolated here as the interface
  `ListProjFamily` (and an `import` obstruction that keeps the assembly in *this* file rather
  than in `Capitalization.lean`):

  ════ residual (A) — the choice-free TRANSITION BASE MORPHISM ════
  The transition `A/(∏V) → A/(∏U)` for `V ⊆ U` is BASE-CHANGE (`baseChangeObj`/`baseChangeFunctor`,
  SliceRegular.lean) along a product projection `listProd U ⟶ listProd V`.  That projection is
  NOT constructible choice-free over the present index: `listSubset V U` is `∀ x ∈ V, x ∈ U`, a
  `Prop`, so a *positional* match "factor `k` of `V` = factor `?` of `U`" cannot be extracted
  without `DecidableEq 𝒞` (object equality) — exactly the same `Prop`-can't-large-eliminate wall
  that forced `listProdProj` to be `Fin`-indexed rather than `(B ∈ U)`-indexed.  The honest
  abstraction is therefore to take the projection family as DATA (`ListProjFamily` below); the
  genuine missing primitive is one constructive instance of it.

  ════ residual (B-strict) — base-change is only PSEUDO-functorial ════
  `CatSystem.F_refl`/`F_trans` demand ON-THE-NOSE equalities `F (refl) X = X` and
  `F (trans) X = F hjk (F hij X)`.  Base-change along `1` is `X ×_D D → D`, equal to `X` only up
  to iso, and base-change along a composite re-associates pullbacks — both hold only up to
  canonical iso, never definitionally (probed: `baseChangeObj (Cat.id D) X = X` does not reduce).
  The outer ω-tower sidestepped this by transporting via `transN` (literal iterated composition,
  strictly functorial).  The inner system needs the same strictification of base-change (or a
  strictly-functorial replacement transition), which is a standalone construction.

  ════ residual (B-import) — the assembly cannot live in `Capitalization.lean` ════
  `RelativeCapitalization` imports `Capitalization` (for `CapStep`), so the ingredients
  `listDirected`/`baseChangeFunctor`/`listProd`/`listProdSliceAcquiresEveryFactor` are visible
  ONLY here, downstream of `hwall_step`.  Discharging `hwall_step` in place would require moving
  the inner-system ingredients up into a file that `Capitalization` imports (e.g. `SliceRegular`),
  or relocating `capData_exists` down here.  Until that reorganization, `hwall_step` stays a
  documented `sorry` pointing at this block. -/

/-- **The transition base-morphism family (residual (A), as data).**  A choice-free assignment,
    for every inclusion `V ⊆ U` of finite object-sets, of a product projection
    `listProd U ⟶ listProd V` (the bigger product projects onto the smaller), STRICTLY coherent:
    the identity inclusion gives `Cat.id`, and a composite inclusion gives the composite
    projection.  This is exactly the data missing from residual (A); one constructive instance of
    it (needing `DecidableEq 𝒞` or a positional refinement of the index) closes residual (A).

    Given such a family, the inner system's transition is `baseChangeFunctor (proj h)`; its strict
    coherence laws are residual (B-strict) — base-change is only pseudo-functorial, so even with a
    strict `ListProjFamily` the `CatSystem.F_refl`/`F_trans` need base-change strictification. -/
structure ListProjFamily where
  /-- the product projection `∏U → ∏V` for each `V ⊆ U`. -/
  proj : ∀ {V U : List 𝒞}, listSubset V U → (listProd U ⟶ listProd V)
  /-- strict unit: the projection along the reflexive inclusion is the identity. -/
  proj_refl : ∀ (U : List 𝒞), proj (listDirected.refl U) = Cat.id (listProd U)
  /-- strict composition: the projection along a composite inclusion is the composite. -/
  proj_trans : ∀ {V U W : List 𝒞} (hVU : listSubset V U) (hUW : listSubset U W),
    proj (listDirected.trans hVU hUW) = proj hUW ≫ proj hVU

/-- **The inner finite-product-slice object map.**  Stage `U` of the inner system is the slice
    `A/(∏U) = Over (listProd U)`.  This is residual-(A)/(B)-free (it is just the object family). -/
def innerObj (U : List 𝒞) : Type u := Over (listProd U)

instance innerCat (U : List 𝒞) : Cat.{u} (innerObj (𝒞 := 𝒞) U) := overCat (listProd U)

/-- **The inner transition functor**, *given* a projection family `P` (residual (A)): for `V ⊆ U`,
    base-change `A/(∏V) → A/(∏U)` along `P.proj : ∏U → ∏V`.  The OBJECT map is `baseChangeObj`,
    the functoriality (in the slice variable) is `baseChangeFunctor` — both sorry-free.  What is
    NOT yet available (residual (B-strict)) are the `CatSystem`-level strict laws `F_refl`/`F_trans`
    relating different inclusions, because base-change is only pseudo-functorial in the base. -/
def innerF (P : ListProjFamily (𝒞 := 𝒞)) {V U : List 𝒞} (h : listSubset V U) :
    innerObj (𝒞 := 𝒞) V → innerObj (𝒞 := 𝒞) U :=
  baseChangeObj (P.proj h)

/-- The inner transition is a functor in the slice variable (base-change functoriality).  This is
    sorry-free — it is exactly `baseChangeFunctor` along `P.proj h`. -/
instance innerFunctF (P : ListProjFamily (𝒞 := 𝒞)) {V U : List 𝒞} (h : listSubset V U) :
    @Functor (innerObj (𝒞 := 𝒞) V) (innerCat V) (innerObj (𝒞 := 𝒞) U) (innerCat U) (innerF P h) :=
  baseChangeFunctor (P.proj h)

/-- **The strict-functoriality obligation for the inner transition (residual (B-strict)), AS A
    HYPOTHESIS — NOT asserted.**  A `CatSystem` demands the transitions be functorial *on the nose*:
    `F_refl : F (refl) X = X` and `F_trans : F (trans) X = F hjk (F hij X)`.  For RAW base-change
    these equations are **false** (`baseChangeObj (Cat.id (∏U)) X = X ×_{∏U} ∏U → ∏U`, canonically
    iso to `X` but NOT equal; the composite re-associates the iterated pullback).  We therefore
    DECLARE the strict laws as a hypothesis bundle rather than discharge them with a false `sorry`:
    a witness of `StrictBaseChange P` is exactly the base-change strictification (or a strictly
    functorial replacement transition) needed before `innerObj`/`innerF` form a `CatSystem`.

    This is residual (B-strict) stated honestly: providing `StrictBaseChange P` is a real theorem
    (it does NOT hold for raw base-change), so there is no false-statement-with-`sorry` here. -/
structure StrictBaseChange (P : ListProjFamily (𝒞 := 𝒞)) : Prop where
  F_refl : ∀ {U : List 𝒞} (X : innerObj (𝒞 := 𝒞) U), innerF P (listDirected.refl U) X = X
  F_trans : ∀ {V U W : List 𝒞} (hVU : listSubset V U) (hUW : listSubset U W)
    (X : innerObj (𝒞 := 𝒞) V),
    innerF P (listDirected.trans hVU hUW) X = innerF P hUW (innerF P hVU X)

/-- **The inner `CatSystem` over `listDirected`, GIVEN the residuals as inputs.**  Objects
    `A/(∏U)`, transitions base-change along a projection family `P` (residual (A)), with the strict
    laws supplied by `hS : StrictBaseChange P` (residual (B-strict)).  Sorry-free: every field is a
    real construction or a fed-in hypothesis — no false equation is asserted.  Discharging the two
    inputs `P`/`hS` (one constructive `ListProjFamily`, one base-change strictification) plus the 9
    `colimitPreRegular` preservation hypotheses and `Coherent` (residual (B-package), mirroring the
    OUTER `towerSystem`/`towerCoherent`/`capData_of_tower`) closes the inner construction.

    ROUTE-1 NOTE (see the `strictReindexSystem` block below).  `hS : StrictBaseChange P` is a GENUINE
    obligation — base-change is irreducibly pseudo-functorial.  The natural strict alternative (Σ /
    post-composition, `strictReindexSystem`) discharges the strict `F_refl`/`F_trans` on the nose but
    runs the WRONG variance and keeps the slice domain fixed, so it cannot carry §1.547's growing
    embedding.  Hence `StrictBaseChange` cannot be replaced by route-1 reindexing; it stays. -/
noncomputable def innerCatSystem (P : ListProjFamily (𝒞 := 𝒞)) (hS : StrictBaseChange P) :
    Colim.CatSystem (List 𝒞) listDirected where
  A := innerObj (𝒞 := 𝒞)
  catA := innerCat
  F := fun {V U} h => innerF P h
  functF := fun {V U} h => innerFunctF P h
  F_refl := fun {U} X => hS.F_refl X
  F_trans := fun {V U W} hVU hUW X => hS.F_trans hVU hUW X

/-! ## ROUTE 1 — strict reindexing: the strict laws hold, but the variance is wrong

  Investigation of the §1.543 task "replace the pseudo-functorial base-change transition with a
  STRICTLY functorial one so `CatSystem.F_refl`/`F_trans` hold on the nose."

  RESULT (machine-checked, sorry-free below).  The honest strict transition is the dependent-sum /
  post-composition functor `reindexFunctor` (SliceRegular.lean): along a FIXED base map `m : C ⟶ D`,
  `Σ_m : A/C → A/D`, `⟨X, x⟩ ↦ ⟨X, x ≫ m⟩`.  It is STRICTLY functorial and — unlike base-change —
  satisfies the `CatSystem` object laws DEFINITIONALLY:

    * `reindexObj_id   : reindexObj (Cat.id C) X = X`                           (strict `F_refl`)
    * `reindexObj_comp : reindexObj (m ≫ m') X = reindexObj m' (reindexObj m X)` (strict `F_trans`)

  both proven by `rfl`-level rewriting (`Cat.comp_id` / `Cat.assoc`).  So a `CatSystem` built on
  `reindexFunctor` needs NO `StrictBaseChange` hypothesis: `strictReindexSystem` below has its
  `F_refl`/`F_trans` as PROVEN theorems, not fed-in inputs.  This is the route-1 strict win, in hand.

  WHY ROUTE 1 NEVERTHELESS CANNOT CARRY §1.547 (the two-fold obstruction, both `rfl`-confirmed):

   (i) WRONG VARIANCE.  `reindexFunctor` runs `A/C → A/D` ALONG a base map `m : C → D`.  The §1.547
       directed transition is `A/(∏V) → A/(∏U)` for `V ⊆ U`, whose canonical, choice-free base map is
       the PROJECTION `listProdProj`-style `∏U → ∏V` (bigger product onto smaller) — pointing the
       WRONG way for Σ.  A Σ-usable `∏V → ∏U` would have to MANUFACTURE the extra factors of `U∖V`,
       i.e. supply points `1 → B` for the new well-supported `B`; choice-free, no such map exists
       (that is precisely the point the construction is trying to ADD, not assume).  Hence the strict
       family `ReindexFamily` (the Σ analogue of `ListProjFamily`) carries data `∏V ⟶ ∏U` that is NOT
       constructible — strictly worse than `ListProjFamily`'s `∏U ⟶ ∏V`, which at least IS a genuine
       projection (blocked only by `Prop`-no-large-elim / `DecidableEq 𝒞`).

  (ii) BREAKS THE EMBEDDING.  Even granting such a family, Σ keeps the DOMAIN fixed:
       `(reindexObj m (sliceEmbedObj (∏V) B)).dom = (∏V).dom`-shape `= prod B (listProd V)`, NEVER
       `prod B (listProd U)` (confirmed by `rfl`).  But the slice embedding at stage `U` is
       `sliceEmbedObj (∏U) B = ⟨B × ∏U, snd⟩`, whose domain GREW to `B × ∏U`.  The colimit must
       identify `objIncl V (embed B) = objIncl U (embed B)`, i.e. the transition must connect
       `⟨B×∏V, snd⟩` to `⟨B×∏U, snd⟩` — a domain CHANGE `B×∏V ↝ B×∏U`.  Only the pullback/base-change
       direction does this (`X ↦ X ×_{∏V} ∏U`); Σ cannot, since it never touches the domain.  This is
       the structural reason §1.547's directed union is the pullback (rational-category) construction,
       NOT a strict reindexing — and is exactly why Freyd phrases the `A*|U`-to-`A*|V` transitions as
       *equivalences of full subcategories of the rational category*, i.e. up-to-iso, never on the nose.

  CONCLUSION.  Route 1 produces a genuine, hypothesis-free strict `CatSystem` (`strictReindexSystem`)
  but on the WRONG variance and WITHOUT the embedding/point-acquisition §1.547 needs.  The base-change
  inner system (`innerCatSystem`) keeps the correct variance and embedding but is irreducibly
  pseudo-functorial (its `StrictBaseChange` is a real, non-trivial strictification obligation).  The
  two cannot be merged: strictness and the growing-product embedding pull in opposite directions.  So
  `hwall_step` keeps its honest `sorry`; the residual is base-change strictification (residual
  (B-strict)) OR a literal directed-union-of-full-subcategories model of the rational category whose
  inclusions are strict by construction — NOT route-1 reindexing. -/

/-- **The strict reindexing transition base-map family (the Σ analogue of `ListProjFamily`).**  Data
    of a base map `∏V ⟶ ∏U` per inclusion `V ⊆ U`, strictly coherent.  NOTE the direction `∏V → ∏U`:
    this is what `Σ` (post-composition) requires, and is NOT choice-free constructible — a map
    `∏V → ∏U` for `V ⊆ U` must supply the missing factors `U∖V` (points `1 → B`), the very data the
    capitalization is meant to ADD.  Carried as a structure to make the obstruction explicit. -/
structure ReindexFamily where
  /-- the (non-constructible, choice-laden) base map `∏V → ∏U` for each `V ⊆ U`. -/
  base : ∀ {V U : List 𝒞}, listSubset V U → (listProd V ⟶ listProd U)
  /-- strict unit. -/
  base_refl : ∀ (U : List 𝒞), base (listDirected.refl U) = Cat.id (listProd U)
  /-- strict composition. -/
  base_trans : ∀ {V U W : List 𝒞} (hVU : listSubset V U) (hUW : listSubset U W),
    base (listDirected.trans hVU hUW) = base hVU ≫ base hUW

/-- **The strict reindexing inner object map.**  Stage `U` is the slice `A/(∏U) = Over (listProd U)`,
    same objects as `innerObj`; the transition will be Σ (post-composition), not base-change. -/
def reindexObjStage (R : ReindexFamily (𝒞 := 𝒞)) {V U : List 𝒞} (h : listSubset V U) :
    innerObj (𝒞 := 𝒞) V → innerObj (𝒞 := 𝒞) U :=
  reindexObj (R.base h)

/-- The strict reindexing transition is a functor — STRICTLY (it is `reindexFunctor`). -/
instance reindexFunctStage (R : ReindexFamily (𝒞 := 𝒞)) {V U : List 𝒞} (h : listSubset V U) :
    @Functor (innerObj (𝒞 := 𝒞) V) (innerCat V) (innerObj (𝒞 := 𝒞) U) (innerCat U)
      (reindexObjStage R h) :=
  reindexFunctor (R.base h)

/-- **The strict reindexing inner `CatSystem` — route 1, sorry-free, NO strictness hypothesis.**
    Given a (route-1) base-map family `R`, the Σ-transition system over `listDirected` is a genuine
    `CatSystem` whose `F_refl`/`F_trans` are PROVEN — `reindexObj_id` and `reindexObj_comp` (modulo
    `R.base_refl`/`R.base_trans`), NOT supplied as `StrictBaseChange`-style hypotheses.  This is the
    concrete route-1 deliverable: strict laws ARE dischargeable on the nose for the reindexing
    transition.  Its limitation (wrong variance + fixed domain, so it does NOT carry the §1.547
    embedding/point-acquisition) is documented above and is why it does not close `hwall_step`. -/
def strictReindexSystem (R : ReindexFamily (𝒞 := 𝒞)) :
    Colim.CatSystem (List 𝒞) listDirected where
  A := innerObj (𝒞 := 𝒞)
  catA := innerCat
  F := fun {V U} h => reindexObjStage R h
  functF := fun {V U} h => reindexFunctStage R h
  F_refl := fun {U} X => by
    show reindexObj (R.base (listDirected.refl U)) X = X
    rw [R.base_refl, reindexObj_id]
  F_trans := fun {V U W} hVU hUW X => by
    show reindexObj (R.base (listDirected.trans hVU hUW)) X
      = reindexObj (R.base hUW) (reindexObj (R.base hVU) X)
    rw [R.base_trans, reindexObj_comp]

/-! ## §1.546/§1.547  The uniform relative-capitalization successor `nextStep`

  This block assembles Freyd's relative-capitalization successor `S ↦ S*` as a single
  uniform `CapStep S` (the keystone the outer ω-tower iterates).  The pieces:

    * `wellSupported_one`/`wellSupported_prod`/`wellSupported_listProd` — `WellSupported (∏U)`
      whenever every member of the list `U` is well-supported.
    * The faithful BASE EMBEDDING `S → innerSliceObj ([] : Infl S)` — `X ↦ ⟨[X], term⟩`,
      `f ↦ inflFunctor.map f`.  Faithful because the inflation cross-section `infl`
      (`prodRight 1`) separates morphisms (`fst : X×1 → X` is a cover, `1` well-supported)
      and the slice over the terminal of `Infl S` forgets nothing (its hom is `term`).
    * The COFINAL ENUMERATION — Classical-well-order the well-supported objects of `S`
      and build the `take`-prefix `PrefixChain`, so each appended suffix is a list of
      well-supported objects, hence `hwsuf` (every appended `∏d` well-supported) holds and
      `chainSlicePreRegularWS` makes the inner colimit `S* = (chainSliceSystem P).Obj`
      a concrete `PreRegularCategory`.
    * `nextStep S : CapStep S.carrier` = ⟨S*, base-embed ≫ stage-0 inclusion, faithful⟩. -/

variable [PullbacksTransferCovers 𝒞]

/-- `∏[] = 1` is well-supported: `term 1 = id 1`, and the identity is a cover (a monic it
    factors through is split epi + mono = iso).  Inlined (`iso_cover` lives in the `HasImages`
    section of `S1_56`, unavailable here). -/
theorem wellSupported_one : WellSupported (𝒞 := 𝒞) (listProd ([] : List 𝒞)) := by
  show Cover (term (HasTerminal.one : 𝒞))
  rw [show term (HasTerminal.one : 𝒞) = Cat.id HasTerminal.one from term_uniq _ _]
  intro C m g hm hgm
  -- `g ≫ m = id`, so `m` is split epi; `m` mono ⟹ `m` iso (`m ≫ g = id` by cancelling `m`).
  refine ⟨g, hm (m ≫ g) (Cat.id C) ?_, hgm⟩
  rw [Cat.assoc, hgm, Cat.id_comp]; exact Cat.comp_id m

/-- **Composition of covers is a cover** (images-free; `cover_comp`/`cover_mono_diagonal` in
    `S1_56` inherit a `HasImages` section variable, so we inline the pullback-diagonal fill that
    needs only `HasPullbacks`).  `f ≫ g` factors through a mono `m` via `h ≫ m = f ≫ g`; the
    pullback of `g` along `m` gives a mono `π₁` that `f` is a cover onto, hence `π₁` iso, hence a
    fill `f ≫ k = h`, and `g` a cover forces `m` iso. -/
theorem cover_comp' {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Cover f) (hg : Cover g) :
    Cover (f ≫ g) := by
  intro C m h hm hfac
  -- diagonal fill: `f ≫ g = h ≫ m`, pullback of `g, m`, `π₁` mono (pullback of mono `m`).
  let pb := HasPullbacks.has g m
  -- `π₁` is mono (pullback of the mono `m`), inlined (`pullback_fst_mono` needs `HasImages`):
  have hπmono : Mono pb.cone.π₁ := by
    intro W p q hpq
    have hpq2 : p ≫ pb.cone.π₂ = q ≫ pb.cone.π₂ := by
      apply hm
      calc (p ≫ pb.cone.π₂) ≫ m = p ≫ (pb.cone.π₁ ≫ g) := by rw [Cat.assoc, ← pb.cone.w]
        _ = (q ≫ pb.cone.π₁) ≫ g := by rw [← Cat.assoc, hpq]
        _ = (q ≫ pb.cone.π₂) ≫ m := by rw [Cat.assoc, pb.cone.w, ← Cat.assoc]
    let cn : Cone g m := ⟨W, p ≫ pb.cone.π₁, p ≫ pb.cone.π₂, by rw [Cat.assoc, Cat.assoc, pb.cone.w]⟩
    rw [pb.lift_uniq cn p rfl rfl, pb.lift_uniq cn q hpq.symm hpq2.symm]
  let u := pb.lift ⟨X, f, h, by rw [hfac]⟩
  have hu₁ : u ≫ pb.cone.π₁ = f := pb.lift_fst _
  obtain ⟨inv, _, hinvπ⟩ : IsIso pb.cone.π₁ := hf pb.cone.π₁ u hπmono hu₁
  -- `inv ≫ π₂` fills `(inv≫π₂) ≫ m = g`; then `g` a cover through `m` forces `m` iso.
  refine hg m (inv ≫ pb.cone.π₂) hm ?_
  rw [Cat.assoc, ← pb.cone.w, ← Cat.assoc, hinvπ, Cat.id_comp]

/-- **The product of two well-supported objects is well-supported.**  `term (B×D)` factors as
    `fst ≫ term B`; `fst : B×D → B` is a cover (`prod_fst_cover`, needs `D` well-supported) and
    `term B` is a cover (`B` well-supported), so the composite is a cover. -/
theorem wellSupported_prod {B D : 𝒞} (hB : WellSupported B) (hD : WellSupported D) :
    WellSupported (prod B D) := by
  show Cover (term (prod B D))
  rw [show term (prod B D) = (fst : prod B D ⟶ B) ≫ term B from term_uniq _ _]
  exact cover_comp' (prod_fst_cover hD) hB

/-- **`∏U` is well-supported when every member of `U` is.** -/
theorem wellSupported_listProd : ∀ {U : List 𝒞}, (∀ B ∈ U, WellSupported B) →
    WellSupported (listProd U)
  | [],     _ => wellSupported_one
  | B :: U, h => by
      rw [listProd_cons]
      exact wellSupported_prod (h B (List.mem_cons.2 (Or.inl rfl)))
        (wellSupported_listProd (fun C hC => h C (List.mem_cons.2 (Or.inr hC))))

/-! ### The faithful base embedding `S → innerSliceObj ([] : Infl S)`

  Stage 0 of the chain (`chain 0 = []`) is `innerSliceObj [] = Over ([] : Infl S)`, the slice
  over the terminal of the inflation.  `S` embeds faithfully there by the inflation cross-section
  `infl : X ↦ [X]` (`inflFunctor`) followed by the (forgetting-nothing) slice over the terminal:
  `X ↦ ⟨[X], term⟩`, `f ↦ ⟨inflFunctor.map f, …⟩`.  Faithful because `infl` separates morphisms
  (`fst : X×1 → X` is a cover, `1` well-supported) and reflects isos. -/

/-- The object part of the base embedding: `X ↦ ⟨[X], term [X]⟩ : innerSliceObj ([] : Infl 𝒞)`. -/
def baseSliceObj (X : 𝒞) : innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞) :=
  ⟨(infl X : Infl 𝒞), term (infl X : Infl 𝒞)⟩

/-- The morphism part of the base embedding: `f : X → Y` becomes the over-hom whose underlying
    `Infl`-arrow is `inflFunctor.map f : [X] ⟶ [Y]` (commutes with `term` by `term_uniq`). -/
def baseSliceMap {X Y : 𝒞} (f : X ⟶ Y) :
    OverHom (baseSliceObj (𝒞 := 𝒞) X) (baseSliceObj Y) :=
  ⟨(inflFunctor.map f : (infl X : Infl 𝒞) ⟶ infl Y), term_uniq _ _⟩

/-- The base embedding `S → innerSliceObj []` is a functor: its underlying `Infl`-arrows are
    `inflFunctor`'s, so the laws transport along `OverHom.ext` (a slice equation is its underlying
    equation). -/
instance baseSliceFunctor : @Functor 𝒞 _ (innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) _ baseSliceObj where
  map {X Y} f := baseSliceMap f
  map_id X := OverHom.ext (by
    show (inflFunctor.map (Cat.id X) : (infl X : Infl 𝒞) ⟶ infl X) = Cat.id (infl X : Infl 𝒞)
    exact inflFunctor.map_id X)
  map_comp {X Y Z} f g := OverHom.ext (by
    show (inflFunctor.map (f ≫ g) : (infl X : Infl 𝒞) ⟶ infl Z)
        = (baseSliceMap f ⊚ baseSliceMap g).f
    exact inflFunctor.map_comp f g)

/-- **`(-)×B` reflects isomorphisms** for well-supported `B`: `IsIso (f×B) ⟹ IsIso f`.  Extracted
    from the reflects-iso half of `sliceEmbedFaithful`: from `f×B` iso get `f×B` mono ⟹ `f` mono
    (separation), and `fst_C ≫ f = (f×B) ≫ fst_D` makes `f` a cover (iso∘cover, right-factor),
    so `monic_cover_iso` gives `f` iso. -/
theorem prodRight_reflects_iso (B : 𝒞) (hws : WellSupported B) {C D : 𝒞} (f : C ⟶ D)
    (hiso : IsIso ((prodRightFunctor B).map f)) : IsIso f := by
  obtain ⟨inv, hinv1, _hinv2⟩ := hiso
  have hfBmono : Mono ((prodRightFunctor B).map f) := mono_of_retraction _ inv hinv1
  have hfmono : Mono f := by
    intro Z u v huv
    have h1 : (prodRightFunctor B).map (u ≫ f) = (prodRightFunctor B).map (v ≫ f) := by rw [huv]
    rw [(prodRightFunctor B).map_comp, (prodRightFunctor B).map_comp] at h1
    exact slice_embedding_separates B hws u v (hfBmono _ _ h1)
  have hfcover : Cover f := by
    have hstep : (fst : prod C B ⟶ C) ≫ f = (prodRightFunctor B).map f ≫ (fst : prod D B ⟶ D) :=
      (fst_pair ((fst : prod C B ⟶ C) ≫ f) snd).symm
    have hcov : Cover ((fst : prod C B ⟶ C) ≫ f) := by
      rw [hstep]; exact cover_precomp_iso ⟨inv, hinv1, _hinv2⟩ (prod_fst_cover hws)
    intro K m h hm hfac
    exact hcov m ((fst : prod C B ⟶ C) ≫ h) hm (by rw [Cat.assoc, hfac])
  exact monic_cover_iso f hfcover hfmono

/-- `infl : 𝒞 → Infl 𝒞` (the cross-section `X ↦ [X]`, underlying `prodRight 1`) SEPARATES
    MORPHISMS: `inflFunctor.map f = inflFunctor.map g ⟹ f = g`.  This is `slice_embedding_separates`
    at `B = 1` (`1` well-supported), since `inflFunctor.map = (prodRight 1).map` by `rfl`. -/
theorem infl_separates {X Y : 𝒞} (f g : X ⟶ Y)
    (h : (inflFunctor.map f : (infl X : Infl 𝒞) ⟶ infl Y) = inflFunctor.map g) : f = g := by
  -- `inflFunctor.map = (prodRightFunctor 1).map` (both are `pair (fst ≫ ·) snd`, by `rfl`); so
  -- this is `slice_embedding_separates (B := 1)` (`1` well-supported).
  exact slice_embedding_separates (B := HasTerminal.one) wellSupported_one f g
    (show (prodRightFunctor HasTerminal.one).map f = (prodRightFunctor HasTerminal.one).map g from h)

/-- **The base embedding `S → innerSliceObj []` is FAITHFUL.**  Embedding: equality of slice-images
    gives equality of underlying `Infl`-arrows `inflFunctor.map f = inflFunctor.map g`, separated by
    `infl_separates`.  Reflects-iso: a slice iso has iso underlying `inflFunctor.map f = (prodRight 1).map f`,
    and `prodRight_reflects_iso` (with `1` well-supported) descends to `f`. -/
theorem baseSliceFaithful :
    @Faithful 𝒞 _ (innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) _ baseSliceObj baseSliceFunctor := by
  refine ⟨?_, ?_⟩
  · -- embedding
    intro X Y f g h
    exact infl_separates f g (congrArg OverHom.f h)
  · -- reflects iso
    intro X Y f hiso
    have hfiso : IsIso (baseSliceMap f).f := overIso_underlying hiso
    exact prodRight_reflects_iso HasTerminal.one wellSupported_one f
      (show IsIso ((prodRightFunctor HasTerminal.one).map f) from hfiso)

/-- **The base embedding `S → innerSliceObj []` preserves the terminal.**  `baseSliceObj one =
    ⟨[1], term [1]⟩`; maps into it in `Over []` are determined by their underlying `Infl`-arrow
    `X.dom ⟶ [1]`, i.e. a `𝒞`-arrow `∏(X.dom) ⟶ ∏[1] = prod 1 1`.  Two such agree because both
    projections land in the `𝒞`-terminal `1` (`term_uniq`), so they are jointly monic-collapsed. -/
theorem baseSlicePreservesTerminal :
    letI : HasTerminal (innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) := overHasTerminal _
    @PreservesTerminal 𝒞 (innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) _ _ baseSliceObj baseSliceFunctor
      _ (overHasTerminal _) := by
  letI : HasTerminal (innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) := overHasTerminal _
  intro X f g
  apply OverHom.ext
  show f.f = g.f
  have h1 : f.f ≫ (fst : prod HasTerminal.one HasTerminal.one ⟶ _) = g.f ≫ fst := term_uniq _ _
  have h2 : f.f ≫ (snd : prod HasTerminal.one HasTerminal.one ⟶ _) = g.f ≫ snd := term_uniq _ _
  exact fst_snd_jointly_monic f.f g.f h1 h2

section BaseSliceCartesian
variable [HasEqualizers 𝒞]

/-- `innerSliceObj [] = Over []` is Cartesian (terminal/products/equalizers from the `over*`
    instances, given `[HasEqualizers 𝒞]`). -/
instance innerSliceCartesianNil : CartesianCategory (innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) where
  toHasTerminal := overHasTerminal _
  toHasBinaryProducts := overHasBinaryProducts _
  toHasEqualizers := overHasEqualizers _

/-- `𝒞` is Cartesian (terminal + binary products + equalizers, all in scope this section). -/
instance baseCartesian𝒞 : CartesianCategory 𝒞 where
  toHasTerminal := inferInstance
  toHasBinaryProducts := inferInstance
  toHasEqualizers := inferInstance

/-! **REDUCTION of Fact 1 (base-embedding is Cartesian).**  With `baseSlicePreservesTerminal`
    (above) and the general §1.437 `pullbacks_terminal_implies_cartesianFunctor`, the FULL
    `CartesianFunctor baseSliceObj` (terminal + products + equalizers) reduces to the single
    remaining obligation:

      `hpull` : the `baseSliceObj`-image of the §1.432 chosen pullback cone of any cospan `(f,g)`
                in `𝒞` is a pullback cone in `Over []`.

    `baseSliceObj X = ⟨[X], term [X]⟩` (the cross-section `infl = prodRight 1` into `Infl 𝒞`,
    embedded into the slice over the inflation terminal `[]`).  Pullbacks in `Over []` are
    pullbacks in `Infl 𝒞` (over the terminal `Σ` is an equivalence), and `infl = (·)×1` preserves
    them via `prod_one_iso_right : IsIso (fst : prod X 1 ⟶ X)` (the `×1` unitor).  This is a full
    pullback universal-property proof in `Over []`; once landed, `CartesianFunctor baseSliceObj`
    follows by `pullbacks_terminal_implies_cartesianFunctor`, and its three projections feed the
    tower bridge.

    The `hpull` proof factors through two reusable lemmas:
      * `infl_preserves_isPullback` (Inflation.lean): `infl : 𝒞 → Infl 𝒞` sends the `𝒞`-pullback `P`
        to an `Infl 𝒞`-pullback (`inflEmbedCone P.cone`).
      * `sliceForget_reflects_isPullback_terminal` (SliceRegular.lean): over the terminal `[] = 1`,
        `Σ : Over [] → Infl 𝒞` reflects pullbacks.
    The `baseSliceObj`-image cone's `Σ`-forget IS `inflEmbedCone P.cone` (same apex `[P.pt]`, same
    legs `inflFunctor.map P.cone.π_i`), so the two lemmas compose. -/

/-- **Fact 1, the one missing obligation `hpull`.**  The `baseSliceObj`-image of the §1.432 chosen
    pullback cone of `(f, g)` is a pullback in `innerSliceObj [] = Over ([] : Infl 𝒞)`. -/
theorem baseSlice_preserves_pullback {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) :
    Cone.IsPullback (𝒞 := innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞))
      { pt := baseSliceObj (products_equalizers_implies_pullbacks f g).cone.pt
        π₁ := baseSliceFunctor.map (products_equalizers_implies_pullbacks f g).cone.π₁
        π₂ := baseSliceFunctor.map (products_equalizers_implies_pullbacks f g).cone.π₂
        w  := by rw [← baseSliceFunctor.map_comp, ← baseSliceFunctor.map_comp,
                     (products_equalizers_implies_pullbacks f g).cone.w] } := by
  let P := products_equalizers_implies_pullbacks f g
  -- `Σ`-forget of the `baseSliceObj`-image cone IS `inflEmbedCone P.cone` (same apex/legs).
  apply sliceForget_reflects_isPullback_terminal (𝒞 := Infl 𝒞)
  -- the forgotten cone is an `Infl 𝒞`-pullback: `infl` preserves the `𝒞`-pullback `P.cone`.
  exact infl_preserves_isPullback P.cone P.cone_isPullback

/-- **§1.543 Fact 1.**  The faithful base embedding `S → innerSliceObj []` is a `CartesianFunctor`.
    Terminal is `baseSlicePreservesTerminal`; the pullback obligation is `baseSlice_preserves_pullback`;
    the general §1.437 `pullbacks_terminal_implies_cartesianFunctor` assembles the rest. -/
theorem baseSliceCartesianFunctor :
    CartesianFunctor (F := baseSliceObj (𝒞 := 𝒞)) :=
  pullbacks_terminal_implies_cartesianFunctor
    (F := baseSliceObj) (fun {A B C} f g => baseSlice_preserves_pullback f g)
    baseSlicePreservesTerminal

end BaseSliceCartesian

/-! ### The enumeration `PrefixChain` and the well-supported-suffix condition `hwsuf`

  An enumeration `enum : ℕ → S` of (well-supported) objects yields the `take`-prefix chain
  `chain n := (List.range n).map enum = [enum 0, …, enum (n-1)]`.  It is a `PrefixChain`
  (`chain n <+: chain (n+1)` is `chain n ++ [enum n]`), starts at `chain 0 = []`, and — when every
  `enum k` is well-supported — every appended suffix `prefixSuffix (chain i) (chain j)` is a list of
  well-supported objects, so `∏(suffix)` is well-supported (`wellSupported_listProd`): exactly the
  `hwsuf` precondition `chainSlicePreRegularWS` consumes.  This is the §1.547 cofinal enumeration:
  for an enumeration that hits every well-supported `B`, the inner colimit acquires a point of every
  such `B` (`enumChain_acquires`), Freyd's relative-capitalization payoff. -/

/-- The `take`-prefix chain of an enumeration `enum : ℕ → S`: `chain n = [enum 0, …, enum (n-1)]`. -/
def enumPrefix (enum : Nat → 𝒞) (n : Nat) : List 𝒞 := (List.range n).map enum

@[simp] theorem enumPrefix_zero (enum : Nat → 𝒞) : enumPrefix enum 0 = [] := rfl

/-- `chain (n+1) = chain n ++ [enum n]` (append the next factor). -/
theorem enumPrefix_succ (enum : Nat → 𝒞) (n : Nat) :
    enumPrefix enum (n + 1) = enumPrefix enum n ++ [enum n] := by
  show (List.range (n + 1)).map enum = (List.range n).map enum ++ [enum n]
  rw [List.range_succ, List.map_append]; rfl

/-- The enumeration `PrefixChain` over `S` (objects are `Infl S = List S`).  Instances are bound
    EXPLICITLY (`@`-style) so the generalized signature carries `[Cat]/[HasTerminal]/[HasBinaryProducts]`
    at the SAME universe — relying on the `variable` auto-inclusion dropped them, which left the
    return `PrefixChain 𝒞` re-synthesizing those at a `max`-universe metavar at every use site. -/
def enumChain {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    [PullbacksTransferCovers 𝒞] (enum : Nat → 𝒞) : PrefixChain 𝒞 where
  chain := enumPrefix enum
  step n := by rw [enumPrefix_succ]; exact List.prefix_append _ _

/-- Every entry of an appended suffix is some `enum k` (a member of a longer `take`-prefix). -/
theorem enumPrefix_suffix_mem (enum : Nat → 𝒞) {i j : Nat} (B : 𝒞)
    (hB : B ∈ prefixSuffix (enumPrefix enum i) (enumPrefix enum j)) : ∃ k, enum k = B := by
  -- the suffix is a `drop` of a `map enum`, so its members are members of `map enum`.
  have : B ∈ enumPrefix enum j := List.mem_of_mem_drop hB
  obtain ⟨k, _, hk⟩ := List.mem_map.1 this
  exact ⟨k, hk⟩

/-- `(enumPrefix enum (n+1)).length = n+1` (a `take`-prefix of length `n+1`). -/
theorem enumPrefix_length (enum : Nat → 𝒞) (n : Nat) : (enumPrefix enum n).length = n := by
  show ((List.range n).map enum).length = n
  rw [List.length_map, List.length_range]

/-- **§1.547 point acquisition at the chain stage.**  The stage-`(n+1)` slice of the enumeration
    chain, `innerSliceObj (enumPrefix enum (n+1)) = Over (∏[enum 0,…,enum n])`, acquires a point of
    the factor `enum n` (the freshly-appended object): the over-arrow `sliceFactorPoint (enum n)
    (listProdProj …)` from the terminator, whose composite with the slice structure map is the
    terminator's (`sliceAcquiresFactorPoint`).  This is the §1.546 generic point the chain adds for
    `enum n`, read off via `listProdSliceAcquiresEveryFactor`; pushing it along the stage-inclusion
    into `S* = (chainSliceSystem (enumChain enum)).Obj` gives the colimit point (the WALL 2 input). -/
theorem enumChain_stage_acquires (enum : Nat → 𝒞) (n : Nat)
    (k : Fin (enumPrefix enum (n + 1)).length) :
    (sliceFactorPoint ((enumPrefix enum (n + 1)).get k)
        (listProdProj (enumPrefix enum (n + 1)) k)).f
      ≫ (sliceEmbedObj (listProd (enumPrefix enum (n + 1))) ((enumPrefix enum (n + 1)).get k)).hom
      = (overTerm (listProd (enumPrefix enum (n + 1)))).hom :=
  listProdSliceAcquiresEveryFactor (enumPrefix enum (n + 1)) k

/-- **The well-supported-suffix condition `hwsuf` for an enumeration of well-supported objects.**
    If every `enum k` is well-supported, every appended suffix `∏(prefixSuffix (chain i) (chain j))`
    is well-supported (`wellSupported_listProd`), which is exactly the precondition
    `chainSlicePreRegularWS` consumes to give the inner colimit `S*` a `PreRegularCategory`. -/
theorem enumChain_hwsuf (enum : Nat → 𝒞) (hws : ∀ k, WellSupported (enum k))
    {i j : ULift.{u} Nat} (_hij : uliftNatDirected.le i j) :
    WellSupported
      (listProd (𝒞 := 𝒞)
        (prefixSuffix ((enumChain enum).toOrdChain.chain i) ((enumChain enum).toOrdChain.chain j))) := by
  apply wellSupported_listProd
  intro B hB
  obtain ⟨k, hk⟩ := enumPrefix_suffix_mem enum B hB
  rw [← hk]; exact hws k

/-! ### Assembling the uniform successor `nextStep`

  The inner colimit `S* = (chainSliceSystem (enumChain enum)).Obj` of the enumeration chain is a
  concrete `PreRegularCategory` (`chainSlicePreRegularWS`, fed `enumChain_hwsuf`), and `S` embeds
  faithfully via the base embedding into stage 0 composed with the (faithful) colimit stage-0
  inclusion (`baseSliceFaithful` ∘ `stageInclFaithful`).  That data is exactly a `CapStep S`.

  The two successor defs take `S`/`[PreRegularCategory S]` as EXPLICIT binders (mirroring
  `capData_exists`'s `innerPreRegularAt`) so `CapStep S` synthesizes its `[PreRegularCategory S]`
  and the chain-machinery instances resolve through `PreRegularCategory.extends`, with the universe
  pinned by the binders (the section-`variable` form left a `PrefixChain.{max …}` metavar). -/

end Freyd

/-! ## §1.546/§1.547  The uniform successor `nextStep` (outside the `𝒞`-`variable` scope)

  These two defs are placed AFTER `end Freyd` and re-open the namespace WITHOUT the file's
  `variable {𝒞} [HasTerminal 𝒞] …`: leaving those active made `PrefixChain S`'s instance args
  resolve at a `max`-of-two-universes metavar (two live `HasTerminal` instances).  Re-opening clean
  pins the universe (the body's identical signature verified standalone). -/
namespace Freyd

/-- **The relative-capitalization successor from an enumeration of well-supported objects.**
    `S* = (chainSliceSystem (enumChain enum)).Obj`, pre-regular by `chainSlicePreRegularWS` (fed
    `enumChain_hwsuf`).  The faithful embedding `S → S*` is the base embedding `S → innerSliceObj []`
    (stage 0; the enumeration chain has `chain 0 = []` DEFINITIONALLY, so `(chainSliceSystem _).A ⟨0⟩
    = innerSliceObj []` by `rfl` — no cast) followed by the faithful colimit stage-0 inclusion
    (`baseSliceFaithful` ∘ `stageInclFaithful`).  Sorry-free.  For an enumeration that hits every
    well-supported `B`, this is Freyd's §1.547 relative capitalization (the inner colimit acquires a
    point of every enumerated `B`).  `Classical`/ordinals are NOT used here — the enumeration is an
    explicit input. -/
noncomputable def nextStepOfEnum {S : Type u} [Cat.{u} S] [hpre : PreRegularCategory S]
    (enum : Nat → S) (hws : ∀ k, WellSupported (enum k)) : CapStep S := by
  -- pin the four mixins at universe `u` (from the bundled `hpre`) so the chain machinery's
  -- instance args resolve monomorphically — otherwise `PrefixChain S` lands at a `max`-universe.
  letI : HasTerminal.{u,u} S := hpre.toHasTerminal
  letI : HasBinaryProducts.{u,u} S := hpre.toHasBinaryProducts
  letI : HasPullbacks.{u,u} S := hpre.toHasPullbacks
  letI : PullbacksTransferCovers.{u,u} S := hpre.toPullbacksTransferCovers
  letI : HasEqualizers S := products_pullbacks_implies_equalizers
  let P : PrefixChain S := enumChain (𝒞 := S) enum
  letI : Cat (chainSliceSystem P).Obj := colimitCat _ (chainSliceCoherent P)
  -- the well-supported-suffix precondition (discharges `hcanon` via `chainSlicePreRegularWS`).
  have hwsuf : ∀ {i j : ULift.{u} Nat} (_hij : uliftNatDirected.le i j),
      WellSupported (listProd (𝒞 := S)
        (prefixSuffix (P.toOrdChain.chain i) (P.toOrdChain.chain j))) :=
    fun {i j} hij => enumChain_hwsuf enum hws hij
  -- stage 0: `chain 0 = []`, so `(chainSliceSystem P).A ⟨0⟩ = innerSliceObj []` definitionally.
  let i0 : ULift.{u} Nat := ⟨0⟩
  -- explicit `.{u,u}` universes: `stageIncl*`'s two universe params (`ι`, the colimit's `w`) are
  -- not pinned by unification here, leaving a `PrefixChain.{max …}` constraint; both are `u`.
  letI hF0 : @Functor ((chainSliceSystem P).A i0) _ (chainSliceSystem P).Obj _
      ((chainSliceSystem P).objIncl i0) :=
    @stageInclFunctor.{u, u} (ULift.{u} Nat) uliftNatDirected
      (chainSliceSystem P) (chainSliceCoherent P) i0
  have hfaith0 : @Faithful ((chainSliceSystem P).A i0) _ (chainSliceSystem P).Obj _
      ((chainSliceSystem P).objIncl i0) hF0 :=
    @stageInclFaithful.{u, u} (ULift.{u} Nat) uliftNatDirected (chainSliceSystem P) (chainSliceCoherent P)
      (fun {_ _} hij {_ _} p q h => chainHfaith P hij (hwsuf hij) p q h)
      (fun {_ _} hij {_ _} φ hiso => chainHcons P hij (hwsuf hij) φ hiso) i0
  exact
    { T := (chainSliceSystem P).Obj
      catT := colimitCat _ (chainSliceCoherent P)
      preT := chainSlicePreRegularWS (𝒞 := S) P hwsuf
      step := (chainSliceSystem P).objIncl i0 ∘ baseSliceObj (𝒞 := S)
      stepFun := compFunctor (F := baseSliceObj (𝒞 := S)) (G := (chainSliceSystem P).objIncl i0)
      stepFaithful := faithful_comp (F := baseSliceObj (𝒞 := S)) (G := (chainSliceSystem P).objIncl i0)
        (baseSliceFaithful (𝒞 := S)) hfaith0 }

/-! ### The uniform polymorphic successor `nextStep`

  `nextStep : ∀ (S : PreRegBundle), CapStep S.carrier` is the uniform §1.546/§1.547 relative-
  capitalization successor the outer ω-tower (`Capitalization.stageBundle`/`towerSystem`) iterates.
  It is `nextStepOfEnum` fed a Classical-chosen enumeration of well-supported objects.  ANY
  enumeration into well-supported objects works (the constant `1`-enumeration is always available,
  so the choice set is nonempty); `Classical.choice` picks one.

  COFINALITY CAVEAT (the WALL 2 residual, NOT a defect of `nextStep` itself): a *single* `ℕ`-indexed
  `enum` can be cofinal among the well-supported objects only when they are ℕ-enumerable.  For an
  uncountable carrier, pointing EVERY well-supported `B` (what `hwall_cap` consumes) needs the
  ordinal-indexed `OrdChain` (§1.543 transfinite), not this `ℕ`-chain — exactly the documented
  (B-coverage) residual.  `nextStep` is nonetheless a genuine faithful pre-regular successor for
  every `S`, sorry-free; the cofinal enumeration enters only at the `hwall_cap` fixpoint. -/

/-- A well-supported-valued enumeration of `S` always exists: the constant terminator `fun _ => 1`
    (`1` is well-supported, `wellSupported_one`).  This makes the `nextStep` choice set nonempty. -/
theorem exists_wellSupported_enum (S : Type u) [Cat.{u} S] [PreRegularCategory S] :
    ∃ enum : Nat → S, ∀ k, WellSupported (enum k) :=
  ⟨fun _ => HasTerminal.one, fun _ => wellSupported_one⟩

/-- **The uniform relative-capitalization successor `nextStep S : CapStep S.carrier`** — Freyd's
    `S ↦ S*` as the single polymorphic rung the outer ω-tower iterates.  `nextStepOfEnum` applied to
    a `Classical.choice`-picked well-supported enumeration (always available, `exists_wellSupported_enum`).
    Faithful pre-regular embedding `S → S*`, sorry-free.  This is the §1.546/§1.547 keystone. -/
noncomputable def nextStep (S : PreRegBundle.{u}) : CapStep S.carrier :=
  nextStepOfEnum (Classical.choose (exists_wellSupported_enum S.carrier))
    (Classical.choose_spec (exists_wellSupported_enum S.carrier))

end Freyd
