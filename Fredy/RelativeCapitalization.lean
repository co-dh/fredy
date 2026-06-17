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
  sorry-free (above).  Two concrete pieces remain OPEN:
    (A) the TRANSITION FUNCTOR `A/(∏V) → A/(∏U)` for `V ⊆ U` — this is BASE-CHANGE
        (pullback) along the projection `∏U → ∏V`, NOT the slice embedding `sliceEmbedFunctor`
        (which goes `A → A/B`, between base and one slice, not between two slices).  No
        base-change/reindexing functor exists in the repo yet (only the forgetful `Σ`).
    (B) assembling the inner finite-product-slice colimit `S*` (objects `A/(∏U)`, transitions
        from (A)) over `listDirected`, proving `Coherent`, and discharging its
        `colimitPreRegular` package — which itself needs the inner `hcanon`, hence recurses
        into the same colimit-pre-regularity wall.
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

/-- The product `∏U` of a finite list `U` of objects: right-folded binary product, with the
    empty product `∏[] = 1` (the terminator).  `∏(B :: U) = B × (∏U)`. -/
def listProd : List 𝒞 → 𝒞
  | [] => HasTerminal.one
  | B :: U => prod B (listProd U)

@[simp] theorem listProd_nil : listProd ([] : List 𝒞) = HasTerminal.one := rfl
@[simp] theorem listProd_cons (B : 𝒞) (U : List 𝒞) :
    listProd (B :: U) = prod B (listProd U) := rfl

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

end Freyd
