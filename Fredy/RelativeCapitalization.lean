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

  WHAT REMAINS (the residual wall for `hwall_step`, Capitalization.lean).
  The *uniform* successor `nextStep : ∀ S, CapStep S` that `hwall_step` needs is
  STRONGER than a single slice rung: in ONE category `S*` it must add a point for
  *every* well-supported `B` simultaneously (Freyd's §1.547 rational category / the
  directed union of the `A* I U` slice-products).  Building that glued category and
  lifting the per-rung preservation to the iterated `colimitPreRegular` package is
  the open part.  This file delivers the per-`B` slice rung sorry-free; see
  `RELATIVE_CAPITALIZATION.md` for the reduction.

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

end Freyd
