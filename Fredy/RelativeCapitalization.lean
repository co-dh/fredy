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

end Freyd
