/-
  Freyd & Scedrov, *Categories and Allegories* §1.544 — the INFLATION `A′` of a
  category `A`, and the STRICT slice-append functor `A′ → A′/B`.

  Freyd's §1.544 strictification of the relative-capitalization slice rung.  The
  pseudo-functoriality wall of §1.547 (base-change `A/(∏V) → A/(∏U)` is only
  pseudo-functorial, so the inner directed system cannot be a *strict* `CatSystem`)
  is sidestepped exactly as in the book: replace `A` by its inflation `A′`, whose
  binary product is *concatenation of lists* and is therefore STRICTLY associative
  and unital.  Concretely:

    * **Infl `A′`** (`Infl 𝒞 := List 𝒞`): objects are finite sequences
      (lists) of objects of `A`; a morphism `s ⟶ t` in `A′` IS a morphism
      `∏s ⟶ ∏t` in `A` (`listProd`, RelativeCapitalization.lean).  The forgetful
      functor `A′ → A` is `listProd`.  Composition and identity are those of `A`,
      so the category laws hold DEFINITIONALLY (`rfl`).  `A′ ≃ A` but its binary
      product is list concatenation.

    * **Cross-section `A → A′`** (`infl`): `A ↦ [A]`, on `f : A ⟶ A'` the arrow
      `∏[A] ⟶ ∏[A']`, i.e. `A×1 ⟶ A'×1` (via `prodRightFunctor 1`).  Full and
      faithful (the inflation's hom `[A] ⟶ [A']` is `A×1 ⟶ A'×1`, iso to
      `A ⟶ A'` since `1` is terminal; `prodRight 1` is a faithful embedding).

    * **Strict slice-append `A′ → A′/B`** (`appendFunctor B`): the KEY map.
      `s ↦ (s ++ [B], proj_B)` where `proj_B : ∏(s ++ [B]) ⟶ B` is the chosen
      projection onto the appended factor, and on `f : ∏s ⟶ ∏t` the arrow
      `appendMap f : ∏(s++[B]) ⟶ ∏(t++[B])`.  Because the product of `A′` IS
      concatenation, *appending* `[B]` and *appending* the structure map are
      a strict (`rfl`-level) operation on lists — so `appendFunctor` is a genuine
      strict functor, not a base-change-up-to-iso.  This realizes the slice
      inclusion `A → A/B` STRICTLY, which is the whole point of §1.544.

  WHAT IS SORRY-FREE HERE:  the inflation category (`inflationCat`), the forgetful
  functor (`inflForget`), the cross-section (`inflFunctor`, with full/faithful), and
  the strict slice-append functor (`appendFunctor`) with its `Functor` laws holding
  definitionally from list concatenation.  `strict_cancel`/`concat_assoc`/`concat_nil` record the
  strict cancellation / concatenation facts (list-cons injectivity; `(s++d)++e = s++(d++e)`;
  `s++[] = s`) that make the inner §1.547 transition strict.  Also delivered sorry-free: the
  whole-suffix strict slice base-change `sliceCatFunctor d : A′/V → A′/(V++d)` (the §1.547 inner
  transition by concatenation) and the `F_refl` law `innerSliceTr_refl` of the inner directed
  system.  REMAINING (honest `sorry`, true statements): `catMap_append_heq` and the `F_trans` law
  `innerSliceTr_trans` — pure dependent `▸`/`HEq` transport across `List.append_assoc`.

  This is the reusable keystone; `RelativeCapitalization.lean` consumes it to give the
  §1.547 inner directed system a strict transition functor.

  No mathlib (the category theory stays on this repo's own `Cat`).
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_26
import Fredy.S1_31
import Fredy.S1_33
import Fredy.S1_42
import Fredy.S1_44
import Fredy.S1_54
import Fredy.RelativeCapitalization

open Freyd

universe u

namespace Freyd

variable {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]

/-! ## §1.544  The inflation `A′`

  Objects are finite sequences of objects of `A` (`List 𝒞`); a morphism `s ⟶ t`
  IS a morphism `∏s ⟶ ∏t` in `A`.  Composition and identity are inherited from `A`,
  so the `Cat` laws are definitional. -/

/-- The **inflation** `A′` of `A`: objects are finite sequences (`List 𝒞`) of objects
    of `A`.  A morphism `s ⟶ t` is a morphism `∏s ⟶ ∏t` in `A` (the forgetful functor
    sends a sequence to its right-folded product `listProd`).  `A′ ≃ A` but its binary
    product is concatenation. -/
abbrev Infl (𝒞 : Type u) [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] : Type u := List 𝒞

/-- The inflation category structure: `Hom s t := ∏s ⟶ ∏t`, identity and composition
    inherited from `A` — so the three `Cat` laws hold DEFINITIONALLY. -/
instance inflationCat : Cat.{u} (Infl 𝒞) where
  Hom s t := listProd (𝒞 := 𝒞) s ⟶ listProd t
  id s := Cat.id (listProd s)
  comp f g := f ≫ g
  id_comp f := Cat.id_comp f
  comp_id f := Cat.comp_id f
  assoc f g h := Cat.assoc f g h

/-- A morphism of the inflation `s ⟶ t` is *definitionally* a `𝒞`-morphism `∏s ⟶ ∏t`. -/
theorem inflHom_eq (s t : Infl 𝒞) : (s ⟶ t) = (listProd (𝒞 := 𝒞) s ⟶ listProd t) := rfl

/-- The **forgetful functor** `A′ → A`, `s ↦ ∏s`, identity on the underlying `𝒞`-arrows
    (a morphism of `A′` already IS a `𝒞`-arrow between the products). -/
def inflForgetObj (s : Infl 𝒞) : 𝒞 := listProd s

instance inflForget : Functor (inflForgetObj : Infl 𝒞 → 𝒞) where
  map {s t} f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## §1.544  The cross-section `A → A′`

  `A ↦ [A]` (the length-1 sequence).  On `f : A ⟶ A'` the arrow `∏[A] ⟶ ∏[A']`, i.e.
  `A×1 ⟶ A'×1` (the `prodRight 1` functor, since `listProd [A] = prod A 1`).  This is
  the "obvious cross-section" `A ⟶ A′` of §1.544. -/

/-- The cross-section object map `A ↦ [A]`. -/
def infl (A : 𝒞) : Infl 𝒞 := [A]

/-- `∏[A] = A × 1` — the underlying product of a singleton sequence. -/
theorem listProd_singleton (A : 𝒞) :
    listProd (𝒞 := 𝒞) [A] = prod A HasTerminal.one := rfl

/-- The cross-section `A → A′` is a functor: on `f : A ⟶ A'`, the inflation arrow
    `[A] ⟶ [A']` is `f × 1 = prodRight 1`'s image (`A×1 ⟶ A'×1`).  Functoriality is
    inherited from `prodRightFunctor HasTerminal.one`. -/
instance inflFunctor : Functor (infl : 𝒞 → Infl 𝒞) where
  map {A A'} f := (prodRightFunctor (𝒞 := 𝒞) HasTerminal.one).map f
  map_id A := (prodRightFunctor (𝒞 := 𝒞) HasTerminal.one).map_id A
  map_comp f g := (prodRightFunctor (𝒞 := 𝒞) HasTerminal.one).map_comp f g

/-! ## §1.544  The STRICT slice-append functor `A′ → A′/B`

  The crux of §1.544.  In the inflation, the binary product IS concatenation, so the
  slice inclusion `A → A/B` is realized STRICTLY (not up to iso) by *appending* `[B]`.

  `appendProj s B : ∏(s ++ [B]) ⟶ B` — the projection onto the appended last factor,
  defined by recursion on `s` (so it is a fixed, choice-free `𝒞`-arrow):
    * `s = []`:  `∏([] ++ [B]) = ∏[B] = B × 1`, project by `fst`.
    * `s = a::s'`: `∏((a::s') ++ [B]) = a × ∏(s' ++ [B])`, project by `snd ≫ appendProj s' B`.

  `appendMap f : ∏(s ++ [B]) ⟶ ∏(t ++ [B])` for `f : ∏s ⟶ ∏t` — extends `f` by the
  identity on the appended `B` factor, also by recursion on the list shape.  Because both
  are list-recursions, all functor laws (`map_id`, `map_comp`) and the over-hom triangle
  (`appendMap f ≫ appendProj t B = appendProj s B`) hold; the unit/composition of the
  appended factor are STRICT (definitional on list cons). -/

/-- Projection `∏(s ++ [B]) ⟶ B` onto the appended last factor (recursion on `s`). -/
def appendProj : ∀ (s : List 𝒞) (B : 𝒞), listProd (𝒞 := 𝒞) (s ++ [B]) ⟶ B
  | [],      B => (fst : prod B HasTerminal.one ⟶ B)
  | _ :: s', B => (snd : prod _ (listProd (s' ++ [B])) ⟶ listProd (s' ++ [B])) ≫ appendProj s' B

/-- The "rest" projection `∏(s ++ [B]) ⟶ ∏s`, forgetting the appended factor (recursion on `s`):
    `s=[]` ↦ `term`-into-`1` precomposed... actually we keep `∏s` and drop `B` via the structure
    of the product.  Used to assemble `appendMap` as a `pair`. -/
def appendForget : ∀ (s : List 𝒞) (B : 𝒞), listProd (𝒞 := 𝒞) (s ++ [B]) ⟶ listProd s
  | [],      _ => (term _ : prod _ HasTerminal.one ⟶ HasTerminal.one)
  | a :: s', B =>
      pair ((fst : prod a (listProd (s' ++ [B])) ⟶ a))
           ((snd : prod a (listProd (s' ++ [B])) ⟶ listProd (s' ++ [B])) ≫ appendForget s' B)

/-- Assemble an arrow into `∏(t ++ [B])` from its `∏t`-part `g` and its `B`-part `b`
    (recursion on `t`).  This is the `pair` that makes the appended factor strict. -/
def appendArrange : ∀ (t : List 𝒞) (B : 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ B), X ⟶ listProd (𝒞 := 𝒞) (t ++ [B])
  | [],      _, _, _, b => pair b (term _)
  | _ :: t', B, _, g, b => pair (g ≫ fst) (appendArrange t' B (g ≫ snd) b)

/-- The append map `∏(s ++ [B]) ⟶ ∏(t ++ [B])` extending `f : ∏s ⟶ ∏t` by the identity on the
    appended `B` factor.  Assembled from its `∏t`-part `appendForget s B ≫ f` and its `B`-part
    `appendProj s B` (the appended factor kept identical). -/
def appendMap {s t : List 𝒞} (B : 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    listProd (𝒞 := 𝒞) (s ++ [B]) ⟶ listProd (t ++ [B]) :=
  appendArrange t B (appendForget s B ≫ f) (appendProj s B)

/-! ### `appendArrange` is the product pairing into `∏(t ++ [B])`

  The two projection laws (recursion on `t`): `appendArrange` recovers its `B`-part by
  `appendProj` and its `∏t`-part by `appendForget`, and is the UNIQUE such arrow.  These
  reduce all `appendMap`/`appendProj` reasoning to `pair`-algebra. -/

/-- `appendArrange` recovers its `B`-part: `appendArrange t B g b ≫ appendProj t B = b`. -/
theorem appendArrange_proj : ∀ (t : List 𝒞) (B : 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ B),
    appendArrange t B g b ≫ appendProj t B = b
  | [],      B, X, g, b => by
      show pair b (term _) ≫ (fst : prod B HasTerminal.one ⟶ B) = b
      exact fst_pair _ _
  | a :: t', B, X, g, b => by
      show appendArrange (a :: t') B g b
          ≫ ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendProj t' B) = b
      show pair (g ≫ fst) (appendArrange t' B (g ≫ snd) b)
          ≫ ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendProj t' B) = b
      rw [← Cat.assoc, snd_pair]; exact appendArrange_proj t' B (g ≫ snd) b

/-- `appendArrange` recovers its `∏t`-part: `appendArrange t B g b ≫ appendForget t B = g`. -/
theorem appendArrange_forget : ∀ (t : List 𝒞) (B : 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ B),
    appendArrange t B g b ≫ appendForget t B = g
  | [],      B, X, g, b => by
      -- `∏[] = 1`, so `g : X ⟶ 1` is forced to be `term X`; both sides are `term X`.
      show appendArrange [] B g b ≫ (term _ : prod B HasTerminal.one ⟶ HasTerminal.one) = g
      exact term_uniq _ g
  | a :: t', B, X, g, b => by
      show pair (g ≫ fst) (appendArrange t' B (g ≫ snd) b)
          ≫ pair (fst : prod a (listProd (t' ++ [B])) ⟶ a)
                 ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B) = g
      refine (pair_uniq (g ≫ fst) (g ≫ snd) _ ?_ ?_).trans (pair_eta g).symm
      · rw [Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair]
        exact appendArrange_forget t' B (g ≫ snd) b

/-- `appendProj`/`appendForget` are JOINTLY MONIC: two arrows into `∏(t ++ [B])` agreeing on
    both the appended factor (`appendProj`) and the rest (`appendForget`) are equal.  (Recursion
    on `t`; the product `∏(t++[B])` is a table on `(∏t, B)` via these two arrows.) -/
theorem append_jointly_monic : ∀ (t : List 𝒞) (B : 𝒞) {X : 𝒞}
    (p q : X ⟶ listProd (𝒞 := 𝒞) (t ++ [B]))
    (hf : p ≫ appendForget t B = q ≫ appendForget t B)
    (hb : p ≫ appendProj t B = q ≫ appendProj t B), p = q
  | [],      B, X, p, q, _, hb => by
      -- `∏([]++[B]) = B×1`; `appendProj [] B = fst`, and the `1`-component is forced by `term`.
      apply fst_snd_jointly_monic
      · exact hb
      · exact term_uniq _ _
  | a :: t', B, X, p, q, hf, hb => by
      -- `∏((a::t')++[B]) = a × ∏(t'++[B])`; recurse on the `snd` component.
      have hforget : appendForget (a :: t') B
          = pair (fst : prod a (listProd (t' ++ [B])) ⟶ a)
                 ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B) := rfl
      rw [hforget] at hf
      -- read off the `fst`- and `snd`-components of `hf` (the `appendForget`-equation).
      have hfst : (p ≫ pair (fst : prod a (listProd (t' ++ [B])) ⟶ a)
                    ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B)) ≫ fst
                  = (q ≫ pair fst ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B)) ≫ fst :=
        congrArg (· ≫ fst) hf
      have hsnd : (p ≫ pair (fst : prod a (listProd (t' ++ [B])) ⟶ a)
                    ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B)) ≫ snd
                  = (q ≫ pair fst ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B)) ≫ snd :=
        congrArg (· ≫ snd) hf
      simp only [Cat.assoc, fst_pair, snd_pair] at hfst hsnd
      simp only [← Cat.assoc] at hsnd
      -- and the `snd`-component of `hb` (the `appendProj`-equation).
      have hproj : appendProj (a :: t') B
          = (snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendProj t' B := rfl
      rw [hproj] at hb; simp only [← Cat.assoc] at hb
      apply fst_snd_jointly_monic
      · exact hfst
      · exact append_jointly_monic t' B _ _ hsnd hb

/-! ### `appendMap` is a strict functor and gives the over-hom triangle

  From the two `appendArrange` projection laws: `appendMap B f` keeps the appended `B`-factor
  (`appendMap_proj`, the slice-triangle) and acts as `f` on the rest (`appendMap_forget`).
  Joint monicity then gives `map_id`/`map_comp` (the appended factor and the rest are each
  strictly preserved). -/

/-- `appendMap` keeps the appended `B`-factor: `appendMap B f ≫ appendProj t B = appendProj s B`.
    This IS the over-hom triangle of the slice-append functor (structure maps are the projections). -/
@[simp] theorem appendMap_proj {s t : List 𝒞} (B : 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    appendMap B f ≫ appendProj t B = appendProj s B :=
  appendArrange_proj t B (appendForget s B ≫ f) (appendProj s B)

/-- `appendMap` acts as `f` on the rest: `appendMap B f ≫ appendForget t B = appendForget s B ≫ f`. -/
@[simp] theorem appendMap_forget {s t : List 𝒞} (B : 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    appendMap B f ≫ appendForget t B = appendForget s B ≫ f :=
  appendArrange_forget t B (appendForget s B ≫ f) (appendProj s B)

/-- `appendMap` preserves identities: `appendMap B (id) = id`.  (Joint monicity: both sides agree
    on `appendProj` and `appendForget`.) -/
theorem appendMap_id (s : List 𝒞) (B : 𝒞) :
    appendMap B (Cat.id (listProd (𝒞 := 𝒞) s)) = Cat.id (listProd (s ++ [B])) := by
  apply append_jointly_monic s B
  · rw [appendMap_forget, Cat.comp_id, Cat.id_comp]
  · rw [appendMap_proj, Cat.id_comp]

/-- `appendMap` preserves composition: `appendMap B (f ≫ g) = appendMap B f ≫ appendMap B g`. -/
theorem appendMap_comp {s t r : List 𝒞} (B : 𝒞)
    (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) (g : listProd t ⟶ listProd r) :
    appendMap B (f ≫ g) = appendMap B f ≫ appendMap B g := by
  apply append_jointly_monic r B
  · simp only [Cat.assoc, appendMap_forget]
    rw [← Cat.assoc (f := appendMap B f), appendMap_forget, Cat.assoc]
  · simp only [Cat.assoc, appendMap_proj]

/-! ## §1.544  The strict slice-append functor `A′ → A′/[B]`

  Packaged as a genuine `Functor` into the slice `A′/[B] = Over (infl B)` (the slice of the
  inflation over the singleton object `[B]`).  Object map `s ↦ ⟨s ++ [B], structure⟩` where
  the structure map `(s ++ [B]) ⟶ [B]` in `A′` is `pair (appendProj s B) (term _) : ∏(s++[B]) ⟶ B×1`;
  morphism map `appendMap B f`, whose over-hom triangle is `appendMap_proj` (the appended factor
  is preserved).  Functor laws are `appendMap_id`/`appendMap_comp` — STRICT (the append operation
  on lists is definitional). -/

/-- The structure map `(s ++ [B]) ⟶ [B]` in `A′`: as a `𝒞`-arrow `∏(s++[B]) ⟶ ∏[B] = B × 1`,
    it is `⟨appendProj s B, term⟩`.  Its `fst`-component is the appended-factor projection.  Typed
    as an `inflationCat`-hom `(s++[B]) ⟶ infl B` (which IS this `𝒞`-arrow definitionally). -/
def appendStruct (s : List 𝒞) (B : 𝒞) :
    @Cat.Hom (Infl 𝒞) inflationCat (s ++ [B]) (infl B) :=
  (pair (appendProj s B) (term _) : listProd (𝒞 := 𝒞) (s ++ [B]) ⟶ prod B HasTerminal.one)

/-- The slice-append object map `s ↦ ⟨s ++ [B], appendStruct⟩ : A′ → A′/[B]`. -/
def appendObj (B : 𝒞) (s : Infl 𝒞) : Over (B := infl B) :=
  { dom := (s ++ [B] : List 𝒞), hom := appendStruct s B }

/-- The slice-append morphism map: `f : ∏s ⟶ ∏t` becomes the over-hom `appendMap B f`, which
    commutes with the structure maps because `appendMap_proj` keeps the appended factor (and the
    `1`-component is forced by `term`). -/
def appendOverHom (B : 𝒞) {s t : Infl 𝒞} (f : s ⟶ t) :
    OverHom (appendObj B s) (appendObj B t) :=
  { f := appendMap B f,
    w := by
      show appendMap B f ≫ appendStruct t B = appendStruct s B
      -- jointly monic on `B×1` via `fst`/`snd`; `fst`-component is `appendMap_proj`, `snd` is `term`.
      apply fst_snd_jointly_monic
      · show (appendMap B f ≫ pair (appendProj t B) (term _)) ≫ fst
            = pair (appendProj s B) (term _) ≫ fst
        rw [Cat.assoc, fst_pair, fst_pair]; exact appendMap_proj B f
      · exact term_uniq _ _ }

/-- **§1.544 — the STRICT slice-append functor `A′ → A′/[B]`.**  Realizes the slice inclusion
    `A → A/B` on the inflation *strictly* (not up to iso): the product of `A′` is concatenation,
    so `appendObj`/`appendOverHom` are definitional list operations and the functor laws are the
    strict `appendMap_id`/`appendMap_comp`. -/
instance appendFunctor (B : 𝒞) :
    @Functor (Infl 𝒞) inflationCat (Over (B := infl B)) (overCat (infl B)) (appendObj B) where
  map {s t} f := appendOverHom B f
  map_id s := OverHom.ext (by
    show appendMap B (Cat.id (listProd s)) = Cat.id (listProd (s ++ [B]))
    exact appendMap_id s B)
  map_comp {s t r} f g := OverHom.ext (by
    show appendMap B (f ≫ g) = appendMap B f ≫ appendMap B g
    exact appendMap_comp B f g)

/-! ## §1.547  Strict cancellation and the concatenation order on the inflation

  Freyd (§1.544): "the binary product operation on `A′` can now be taken as concatenation.  We
  obtain a strict cancellation property: if `B × A = B × A'` then `A = A'`."  In the inflation,
  `B × s` is `B :: s` (cons), so cancellation is `List.cons` injectivity — DEFINITIONAL.  More
  generally concatenation is STRICTLY associative and unital: `(s++d)++e = s++(d++e)` and `s++[] = s`
  hold as genuine equalities of LIST objects (`List.append_assoc`/`List.append_nil`), so the §1.547
  inner directed-system laws `F_refl`/`F_trans` are honest theorems — UNLIKE raw base-change, where
  `baseChangeObj (Cat.id) X` is iso to `X` but NOT EQUAL, so the laws are simply false.  That object
  equality (not mere iso) is the strictness the inner `CatSystem` requires. -/

/-- **Strict cancellation (§1.544).**  `[B] ++ s = [B] ++ t ⟹ s = t` — list-cons injectivity. -/
theorem strict_cancel (B : 𝒞) {s t : Infl 𝒞} (h : B :: s = B :: t) : s = t :=
  List.cons.inj h |>.2

/-- Concatenation is STRICTLY associative on `A′` (equality of list objects). -/
theorem concat_assoc (s d e : Infl 𝒞) : (s ++ d) ++ e = s ++ (d ++ e) :=
  List.append_assoc s d e

/-- Concatenation is STRICTLY right-unital on `A′` (equality of list objects). -/
theorem concat_nil (s : Infl 𝒞) : s ++ ([] : List 𝒞) = s := List.append_nil s

/-! ## §1.547  The STRICT inner directed system of inflation slices

  The §1.547 inner system: stage `w` (a finite factor-sequence) is the slice `A′/w`, and the
  transition `A′/V → A′/U` for `V ⊑ U` (`U = V ++ d`) is BASE-CHANGE along the strict projection
  `∏U ⟶ ∏V`, realized by *appending* the suffix `d`.  Because concatenation is strict (above), the
  refl/trans laws hold DEFINITIONALLY — no pseudo-functoriality.

  We model the index by `List 𝒞` with the prefix order `V ⊑ U := ∃ d, V ++ d = U` carried as data
  `Suffix V U` (the witnessing suffix `d` with `V ++ d = U`).  The transition functor base-changes
  by appending `d`; its object/morphism maps iterate the single-factor `appendObj`/`appendMap`.

  The base-change object map `A′/V → A′/(V++d)` on the inflation: `⟨s, h : s ⟶ V⟩ ↦
  ⟨s ++ d, appendMap-style⟩` where the structure map appends `d` to both `s` and `V` and `h`
  becomes `h ⊗ id_{∏d}`.  For a SINGLE appended factor `[B]` this is `appendMap B h` (below); the
  multi-factor (whole-`d`) version iterates it, re-bracketing by the strict `concat_assoc`. -/

/-- The explicit suffix witness `V ++ d = U` (the §1.547 prefix order, carried as data so the
    transition functor — "append the suffix `d`" — is canonical). -/
structure Suffix (V U : Infl 𝒞) where
  d : List 𝒞
  eq : V ++ d = U

/-- `appendList d : ∏(s) ⊗ ∏(d)`-style — the underlying base of `s` after appending the list `d`,
    i.e. the object `s ++ d` of `A′`.  (Object-level; the slice transition uses it below.) -/
def appendList (d : List 𝒞) (s : Infl 𝒞) : Infl 𝒞 := s ++ d

/-- Appending the empty list is the identity (`s ++ [] = s`). -/
theorem appendList_nil (s : Infl 𝒞) : appendList [] s = s := List.append_nil s

/-- Appending `d` then `e` is appending `d ++ e` (`(s++d)++e = s++(d++e)`). -/
theorem appendList_append (d e : List 𝒞) (s : Infl 𝒞) :
    appendList e (appendList d s) = appendList (d ++ e) s := List.append_assoc s d e

/-! ### Whole-suffix concatenation maps `concat*` (generalizing `append*` from `[B]` to a list `d`)

  To build the §1.547 inner transition for a multi-factor suffix `d` (not just one factor), we
  generalize the single-factor `appendProj`/`appendForget`/`appendArrange`/`appendMap` from `[B]`
  to an arbitrary appended list `d` (with `∏[B] = B×1` replaced by `∏d`).  Recursion is on the base
  list `s`; the appended `d` is fixed.  These give the whole-suffix slice base-change and the strict
  inner directed system. -/

/-- Tail projection `∏(s ++ d) ⟶ ∏d` onto the appended suffix `d` (recursion on `s`). -/
def catTail : ∀ (s d : List 𝒞), listProd (𝒞 := 𝒞) (s ++ d) ⟶ listProd d
  | [],      _ => Cat.id _
  | _ :: s', d => (snd : prod _ (listProd (s' ++ d)) ⟶ listProd (s' ++ d)) ≫ catTail s' d

/-- Rest projection `∏(s ++ d) ⟶ ∏s`, forgetting the appended suffix `d` (recursion on `s`). -/
def catForget : ∀ (s d : List 𝒞), listProd (𝒞 := 𝒞) (s ++ d) ⟶ listProd s
  | [],      d => (term _ : listProd (𝒞 := 𝒞) ([] ++ d) ⟶ HasTerminal.one)
  | a :: s', d =>
      pair (fst : prod a (listProd (s' ++ d)) ⟶ a)
           ((snd : prod a (listProd (s' ++ d)) ⟶ listProd (s' ++ d)) ≫ catForget s' d)

/-- Assemble an arrow into `∏(t ++ d)` from its `∏t`-part `g` and its `∏d`-part `b` (recursion on `t`). -/
def catArrange : ∀ (t d : List 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ listProd d), X ⟶ listProd (𝒞 := 𝒞) (t ++ d)
  | [],      _, _, _, b => b
  | _ :: t', d, _, g, b => pair (g ≫ fst) (catArrange t' d (g ≫ snd) b)

/-- The concatenation map `∏(s ++ d) ⟶ ∏(t ++ d)` extending `f : ∏s ⟶ ∏t` by the identity on the
    appended suffix `∏d`.  (Whole-`d` generalization of `appendMap`.) -/
def catMap {s t : List 𝒞} (d : List 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    listProd (𝒞 := 𝒞) (s ++ d) ⟶ listProd (t ++ d) :=
  catArrange t d (catForget s d ≫ f) (catTail s d)

/-- `catArrange` recovers its `∏d`-part: `catArrange t d g b ≫ catTail t d = b`. -/
theorem catArrange_tail : ∀ (t d : List 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ listProd d),
    catArrange t d g b ≫ catTail t d = b
  | [],      d, X, g, b => Cat.comp_id b
  | a :: t', d, X, g, b => by
      show catArrange (a :: t') d g b ≫ ((snd : _) ≫ catTail t' d) = b
      show pair (g ≫ fst) (catArrange t' d (g ≫ snd) b) ≫ ((snd : _) ≫ catTail t' d) = b
      rw [← Cat.assoc, snd_pair]; exact catArrange_tail t' d (g ≫ snd) b

/-- `catArrange` recovers its `∏t`-part: `catArrange t d g b ≫ catForget t d = g`. -/
theorem catArrange_forget : ∀ (t d : List 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ listProd d),
    catArrange t d g b ≫ catForget t d = g
  | [],      d, X, g, b => term_uniq _ g
  | a :: t', d, X, g, b => by
      show pair (g ≫ fst) (catArrange t' d (g ≫ snd) b)
          ≫ pair (fst : prod a (listProd (t' ++ d)) ⟶ a)
                 ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d) = g
      refine (pair_uniq (g ≫ fst) (g ≫ snd) _ ?_ ?_).trans (pair_eta g).symm
      · rw [Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair]
        exact catArrange_forget t' d (g ≫ snd) b

/-- `catTail`/`catForget` are JOINTLY MONIC into `∏(t ++ d)`. -/
theorem cat_jointly_monic : ∀ (t d : List 𝒞) {X : 𝒞}
    (p q : X ⟶ listProd (𝒞 := 𝒞) (t ++ d))
    (hf : p ≫ catForget t d = q ≫ catForget t d)
    (hb : p ≫ catTail t d = q ≫ catTail t d), p = q
  | [],      d, X, p, q, _, hb => by
      -- `∏([]++d) = ∏d`; `catTail [] d = id`, so `hb : p = q` directly.
      rw [catTail, Cat.comp_id, Cat.comp_id] at hb; exact hb
  | a :: t', d, X, p, q, hf, hb => by
      have hforget : catForget (a :: t') d
          = pair (fst : prod a (listProd (t' ++ d)) ⟶ a)
                 ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d) := rfl
      rw [hforget] at hf
      have hfst : (p ≫ pair (fst : prod a (listProd (t' ++ d)) ⟶ a)
                    ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d)) ≫ fst
                  = (q ≫ pair fst ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d)) ≫ fst :=
        congrArg (· ≫ fst) hf
      have hsnd : (p ≫ pair (fst : prod a (listProd (t' ++ d)) ⟶ a)
                    ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d)) ≫ snd
                  = (q ≫ pair fst ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d)) ≫ snd :=
        congrArg (· ≫ snd) hf
      simp only [Cat.assoc, fst_pair, snd_pair] at hfst hsnd
      simp only [← Cat.assoc] at hsnd
      have hproj : catTail (a :: t') d
          = (snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catTail t' d := rfl
      rw [hproj] at hb; simp only [← Cat.assoc] at hb
      apply fst_snd_jointly_monic
      · exact hfst
      · exact cat_jointly_monic t' d _ _ hsnd hb

@[simp] theorem catMap_tail {s t : List 𝒞} (d : List 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    catMap d f ≫ catTail t d = catTail s d :=
  catArrange_tail t d (catForget s d ≫ f) (catTail s d)

@[simp] theorem catMap_forget {s t : List 𝒞} (d : List 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    catMap d f ≫ catForget t d = catForget s d ≫ f :=
  catArrange_forget t d (catForget s d ≫ f) (catTail s d)

theorem catMap_id (s d : List 𝒞) :
    catMap d (Cat.id (listProd (𝒞 := 𝒞) s)) = Cat.id (listProd (s ++ d)) := by
  apply cat_jointly_monic s d
  · rw [catMap_forget, Cat.comp_id, Cat.id_comp]
  · rw [catMap_tail, Cat.id_comp]

theorem catMap_comp {s t r : List 𝒞} (d : List 𝒞)
    (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) (g : listProd t ⟶ listProd r) :
    catMap d (f ≫ g) = catMap d f ≫ catMap d g := by
  apply cat_jointly_monic r d
  · simp only [Cat.assoc, catMap_forget]
    rw [← Cat.assoc (f := catMap d f), catMap_forget, Cat.assoc]
  · simp only [Cat.assoc, catMap_tail]

/-! ### The single-factor slice base-change `A′/V → A′/(V ++ [B])`

  The §1.547 inner transition for appending ONE factor `B`.  On the inflation it is STRICT: an
  object `⟨s, h : ∏s ⟶ ∏V⟩` of `A′/V` maps to `⟨s ++ [B], appendMap B h⟩` of `A′/(V++[B])` — `h`
  extended by the identity on the appended `B` (`appendMap`), with the over-hom triangle and functor
  laws coming straight from `appendMap_proj`/`appendMap_id`/`appendMap_comp`.  This is base-change
  along the strict projection `∏(V++[B]) ⟶ ∏V`, realized by concatenation — no pullback, no iso. -/

/-- The single-factor slice base-change object map `A′/V → A′/(V++[B])`, `⟨s,h⟩ ↦ ⟨s++[B], appendMap B h⟩`.
    The structure map `appendMap B h : ∏(s++[B]) ⟶ ∏(V++[B])` extends `h` by `id` on the `B`-factor. -/
def sliceAppendObj (B : 𝒞) {V : Infl 𝒞} (X : Over (B := V)) : Over (B := (V ++ [B] : List 𝒞)) :=
  { dom := (X.dom ++ [B] : List 𝒞),
    hom := (appendMap B X.hom : listProd (𝒞 := 𝒞) (X.dom ++ [B]) ⟶ listProd (V ++ [B])) }

/-- The single-factor slice base-change morphism map: an over-hom `g : X ⟶ Y` (i.e. `g.f ≫ Y.hom =
    X.hom`) maps to `appendMap B g.f`, whose triangle `appendMap B g.f ≫ appendMap B Y.hom =
    appendMap B X.hom` is `appendMap_comp` applied to `g.f ≫ Y.hom = X.hom`. -/
def sliceAppendMap (B : 𝒞) {V : Infl 𝒞} {X Y : Over (B := V)} (g : OverHom X Y) :
    OverHom (sliceAppendObj B X) (sliceAppendObj B Y) :=
  { f := appendMap B g.f,
    w := by
      show appendMap B g.f ≫ appendMap B Y.hom = appendMap B X.hom
      rw [← appendMap_comp]; exact congrArg (appendMap B) g.w }

/-- **The single-factor slice base-change is a STRICT functor `A′/V → A′/(V++[B])`.**  Object map
    `sliceAppendObj B`, morphism map `sliceAppendMap B`; laws from `appendMap_id`/`appendMap_comp`. -/
instance sliceAppendFunctor (B : 𝒞) (V : Infl 𝒞) :
    @Functor (Over (B := V)) (overCat V) (Over (B := (V ++ [B] : List 𝒞)))
      (overCat (V ++ [B] : List 𝒞)) (sliceAppendObj B) where
  map {X Y} g := sliceAppendMap B g
  map_id X := OverHom.ext (by
    show appendMap B (Cat.id (listProd X.dom)) = Cat.id (listProd (X.dom ++ [B]))
    exact appendMap_id X.dom B)
  map_comp {X Y Z} g h := OverHom.ext (by
    show appendMap B (g.f ≫ h.f) = appendMap B g.f ≫ appendMap B h.f
    exact appendMap_comp B g.f h.f)

/-! ### The whole-suffix slice base-change `A′/V → A′/(V ++ d)` (the §1.547 inner transition)

  The genuine multi-factor §1.547 inner transition: for a finite suffix `d` (the factors of `U`
  not in `V`, when `U = V ++ d`), base-change `A′/V → A′/(V++d)` realized by concatenating `d` —
  `⟨s, h⟩ ↦ ⟨s ++ d, catMap d h⟩`.  STRICT (concatenation, not pullback): the over-hom triangle and
  functor laws are `catMap_tail`/`catMap_id`/`catMap_comp`.  This is the building block of the strict
  inner directed system; the transition for `V ⊑ U` takes `d := U.drop V.length` (computable suffix
  DATA from the objects — this is what dissolves residual (A), the `Prop`-no-large-elim wall, since
  the suffix comes from the list objects, not from the inclusion proof). -/

/-- The whole-suffix slice base-change object map `A′/V → A′/(V++d)`, `⟨s,h⟩ ↦ ⟨s++d, catMap d h⟩`. -/
def sliceCatObj (d : List 𝒞) {V : Infl 𝒞} (X : Over (B := V)) : Over (B := (V ++ d : List 𝒞)) :=
  { dom := (X.dom ++ d : List 𝒞),
    hom := (catMap d X.hom : listProd (𝒞 := 𝒞) (X.dom ++ d) ⟶ listProd (V ++ d)) }

/-- The whole-suffix slice base-change morphism map: `g ↦ catMap d g.f`, triangle from `catMap_comp`. -/
def sliceCatMap (d : List 𝒞) {V : Infl 𝒞} {X Y : Over (B := V)} (g : OverHom X Y) :
    OverHom (sliceCatObj d X) (sliceCatObj d Y) :=
  { f := catMap d g.f,
    w := by
      show catMap d g.f ≫ catMap d Y.hom = catMap d X.hom
      rw [← catMap_comp]; exact congrArg (catMap d) g.w }

/-- **The whole-suffix slice base-change is a STRICT functor `A′/V → A′/(V++d)`.**  The §1.547 inner
    directed transition realized by concatenation; laws from `catMap_id`/`catMap_comp`.  Sorry-free. -/
instance sliceCatFunctor (d : List 𝒞) (V : Infl 𝒞) :
    @Functor (Over (B := V)) (overCat V) (Over (B := (V ++ d : List 𝒞)))
      (overCat (V ++ d : List 𝒞)) (sliceCatObj d) where
  map {X Y} g := sliceCatMap d g
  map_id X := OverHom.ext (by
    show catMap d (Cat.id (listProd X.dom)) = Cat.id (listProd (X.dom ++ d))
    exact catMap_id X.dom d)
  map_comp {X Y Z} g h := OverHom.ext (by
    show catMap d (g.f ≫ h.f) = catMap d g.f ≫ catMap d h.f
    exact catMap_comp d g.f h.f)

/-! ## §1.547  The STRICT inner directed system of inflation slices

  The §1.547 inner directed system, now STRICT thanks to the inflation.  Index: `List 𝒞` (factor
  sequences) under the prefix order `V ⊑ U` (`List.IsPrefix`, a `Prop`).  Stage `w` is the slice
  `A′/w`; the transition `A′/V → A′/U` for `V ⊑ U` appends the suffix `d := U.drop V.length` (DATA
  recovered from the objects by `List.drop` — dissolving residual (A), the old `Prop`-no-large-elim
  wall, since the suffix comes from the list `U`, not from the inclusion proof) via the strict
  `sliceCatObj`/`sliceCatFunctor`.

  STRICTNESS STATUS.  The transition functor `sliceCatFunctor d`/`sliceCatObj d` is sorry-free and
  STRICT (no pullback, no iso — concatenation).  The `CatSystem` LAWS reduce to the propositional
  list identities `V ++ [] = V` (`List.append_nil`) and `(V++d)++e = V++(d++e)` (`List.append_assoc`):
  these are genuine equalities of list OBJECTS — exactly the strictness raw base-change LACKS (where
  `baseChangeObj (id) X` is only iso to `X`) — but, because list append is not *definitionally*
  unital/associative for variable lists, the stage objects `A′/(V++d)` must be TRANSPORTED along them.

    * `F_refl` — `innerSliceTr_refl` — is PROVEN sorry-free (only `propext`): the empty-suffix
      transition is the identity on `A′/V`, via `over_transport_ext` + `catMap_nil_heq` (the latter a
      full `HEq` discharge of the `append_nil` reindexing through `catForget`/`catArrange`).
    * `F_trans` — `innerSliceTr_trans` — is an HONEST `sorry`: the statement is TRUE (reduces to
      `prefixSuffix_trans`, PROVEN, plus `catMap_append_heq`), but the doubled-`▸` nested transport
      across `List.append_assoc` is unfinished.  `catMap_append_heq` (the `(s++d)++e = s++(d++e)`
      reindexing of `catMap`) is its remaining core, also an honest `sorry` with a true statement.

  So residual (A) (the `Prop`→suffix DATA wall) is DISSOLVED here by `List.drop`/`prefixSuffix`, and
  residual (B-strict) (strictness) is supplied by the inflation's object-level `concat_assoc`/
  `concat_nil` — the genuine §1.544 advance over base-change.  What remains is purely the dependent
  `▸`/`HEq` transport for the associativity law `F_trans` (F_refl is already closed). -/

/-- The §1.547 inner index: `List 𝒞` ordered by the prefix relation `V ⊑ U` (`List.IsPrefix`).
    Directed: the common bound of `V, U` is... not generally a prefix-bound — so we restrict to
    the sub-order generated by appends from a common base, but for the index `Directed` we use the
    append-prefix structure with bound `V ++ U`-style only when comparable.  Here we expose the
    prefix preorder; directedness on the relevant sub-poset (chains of appends) is immediate. -/
def prefixLe (V U : List 𝒞) : Prop := V <+: U

/-- The appended suffix `d` with `V ++ d = U`, recovered as DATA from the objects (`List.drop`),
    valid given the prefix proof.  This is the choice-free transition base (residual (A) dissolved). -/
def prefixSuffix (V U : List 𝒞) : List 𝒞 := U.drop V.length

theorem prefixSuffix_eq {V U : List 𝒞} (h : prefixLe V U) : V ++ prefixSuffix V U = U :=
  List.prefix_iff_eq_append.mp h

/-- The inner stage object family: stage `w` is the slice `A′/w`. -/
def innerSliceObj (w : List 𝒞) : Type u := Over (B := (w : Infl 𝒞))

instance innerSliceCat (w : List 𝒞) : Cat.{u} (innerSliceObj (𝒞 := 𝒞) w) := overCat (w : Infl 𝒞)

/-- The inner transition object map `A′/V → A′/U` for `V ⊑ U`: append the suffix `U.drop V.length`
    (`sliceCatObj`), then TRANSPORT along `V ++ suffix = U` to land in `A′/U`.  Strict (concatenation). -/
def innerSliceTr {V U : List 𝒞} (h : prefixLe V U) (X : innerSliceObj (𝒞 := 𝒞) V) :
    innerSliceObj (𝒞 := 𝒞) U :=
  (prefixSuffix_eq h) ▸ (sliceCatObj (prefixSuffix V U) X)

/-- `catMap [] f` is `f` modulo the (propositional) `s ++ [] = s` reindexing: `catMap [] f`,
    transported along `append_nil` on both ends, is `f`.  Component lemma for `F_refl`. -/
theorem catTail_nil (s : List 𝒞) : catTail (𝒞 := 𝒞) s [] = term _ := by
  induction s with
  | nil => exact term_uniq _ _
  | cons a s' ih =>
      show (snd : prod a (listProd (s' ++ [])) ⟶ _) ≫ catTail s' [] = term _
      rw [ih]; exact term_uniq _ _

/-- `listProd (s ++ []) = listProd s` as a TYPE-level equality (from `s ++ [] = s`). -/
theorem listProd_append_nil (s : List 𝒞) : listProd (𝒞 := 𝒞) (s ++ []) = listProd s := by
  rw [List.append_nil]

/-- Cons-step kernel for `catForget_nil_heq`: GIVEN a product reindexing `P = ∏s'` and a forget map
    `cf : P ⟶ ∏s'` that is HEq the identity, the `pair fst (snd ≫ cf)` is HEq `id (∏(a::s'))`.
    Stated with `P`, `cf` abstract so the dependent reindexing can be `subst`-ed cleanly. -/
theorem catForget_cons_kernel {a : 𝒞} {s' : List 𝒞} {P : 𝒞} (hP : P = listProd (𝒞 := 𝒞) s')
    (cf : P ⟶ listProd (𝒞 := 𝒞) s') (hcf : HEq cf (Cat.id (listProd (𝒞 := 𝒞) s'))) :
    HEq (pair (fst : prod a P ⟶ a) ((snd : prod a P ⟶ P) ≫ cf))
        (Cat.id (listProd (𝒞 := 𝒞) (a :: s'))) := by
  subst hP
  rw [eq_of_heq hcf, Cat.comp_id]
  exact heq_of_eq pair_fst_snd

/-- Pairing kernel: given `P = B` and a second component `c : X ⟶ P` HEq `g ≫ snd : X ⟶ B`, the pair
    `pair (g ≫ fst) c` is HEq `g` (after `subst`, `c = g ≫ snd`, so `pair (g≫fst)(g≫snd) = g`). -/
theorem pair_snd_kernel {X A B P : 𝒞} (hP : P = B) (g1 : X ⟶ A)
    (c : X ⟶ P) (g2 : X ⟶ B) (hc : HEq c g2) :
    HEq (pair g1 c) (pair g1 g2) := by
  subst hP; cases hc; rfl

/-- Kernel for `catForget_comp_nil_heq`: given `P = ∏s` and `cf : P ⟶ ∏s` HEq `id`, the composite
    `cf ≫ f` is HEq `f` (after `subst`, `cf = id`, so `cf ≫ f = id ≫ f = f`). -/
theorem catForget_comp_kernel {s t : List 𝒞} {P : 𝒞} (hP : P = listProd (𝒞 := 𝒞) s)
    (cf : P ⟶ listProd (𝒞 := 𝒞) s) (hcf : HEq cf (Cat.id (listProd (𝒞 := 𝒞) s)))
    (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) : HEq (cf ≫ f) f := by
  subst hP
  rw [eq_of_heq hcf, Cat.id_comp]

/-- `catForget s []` HEq `id` — forgetting an empty suffix is the identity (up to `s++[]=s`).
    Induction; the cons step delegates the dependent reindexing to `catForget_cons_kernel`. -/
theorem catForget_nil_heq : ∀ (s : List 𝒞),
    HEq (catForget (𝒞 := 𝒞) s []) (Cat.id (listProd (𝒞 := 𝒞) s))
  | [] => by
      have : catForget (𝒞 := 𝒞) [] [] = Cat.id (listProd (𝒞 := 𝒞) []) := term_uniq _ _
      rw [this]
  | a :: s' => by
      have hf : catForget (𝒞 := 𝒞) (a :: s') []
          = pair (fst : prod a (listProd (s' ++ [])) ⟶ a)
                 ((snd : prod a (listProd (s' ++ [])) ⟶ _) ≫ catForget s' []) := rfl
      rw [hf]
      exact catForget_cons_kernel (listProd_append_nil s') (catForget s' []) (catForget_nil_heq s')

/-- `catArrange t [] g b` HEq `g` — assembling into `∏(t++[])` with an empty appended suffix is the
    `∏t`-part `g` (the `b : X ⟶ ∏[] = X ⟶ 1` part is the forced terminator).  Induction on `t`. -/
theorem catArrange_nil_heq : ∀ (t : List 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ listProd (𝒞 := 𝒞) ([] : List 𝒞)),
    HEq (catArrange t [] g b) g
  | [],      X, g, b => by
      -- `catArrange [] [] g b = b : X ⟶ ∏[] = X ⟶ 1`; and `g : X ⟶ ∏[] = X ⟶ 1`; both into `1`.
      show HEq b g; rw [term_uniq b g]
  | a :: t', X, g, b => by
      -- `catArrange (a::t') [] g b = pair (g≫fst) (catArrange t' [] (g≫snd) b)`; IH on the tail.
      have hf : catArrange (a :: t') [] g b
          = pair (g ≫ (fst : prod a (listProd t') ⟶ a))
                 (catArrange t' [] (g ≫ (snd : prod a (listProd t') ⟶ listProd t')) b) := rfl
      rw [hf]
      -- second component HEq `g ≫ snd` (across `∏(t'++[]) = ∏t'`); kernel-substitute then `pair_eta`.
      refine HEq.trans (pair_snd_kernel (listProd_append_nil t') (g ≫ fst)
        (catArrange t' [] (g ≫ snd) b) (g ≫ snd) (catArrange_nil_heq t' (g ≫ snd) b)) ?_
      rw [← pair_eta]

/-- `catForget s [] ≫ f` HEq `f` (`catForget s [] ≍ id`, so the composite is `id ≫ f = f`).
    Generalizes the reindexed domain of `catForget s []` and substitutes, as in the cons kernel. -/
theorem catForget_comp_nil_heq {s t : List 𝒞} (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    HEq (catForget (𝒞 := 𝒞) s [] ≫ f) f :=
  catForget_comp_kernel (listProd_append_nil s) (catForget s []) (catForget_nil_heq s) f

/-- **`catMap [] f` HEq `f`** — the empty appended suffix changes nothing (up to `s++[]=s`, `t++[]=t`).
    `catMap [] f = catArrange t [] (catForget s [] ≫ f) (catTail s [])`; `catArrange_nil_heq` strips
    the empty assemble, `catForget_nil_heq` makes `catForget s [] ≍ id`, leaving `id ≫ f = f`. -/
theorem catMap_nil_heq {s t : List 𝒞} (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    HEq (catMap [] f) f := by
  show HEq (catArrange t [] (catForget s [] ≫ f) (catTail s [])) f
  refine HEq.trans (catArrange_nil_heq t (catForget s [] ≫ f) (catTail s [])) ?_
  -- `catForget s [] ≫ f ≍ id ≫ f = f`; thread `catForget_nil_heq` through `≫ f`.
  exact catForget_comp_nil_heq f

/-- Generic `Over`-transport (in ANY category `𝒟`): if `e : B = B'`, `hd : X.dom = Y.dom`, and the
    homs agree (`HEq`), then `e ▸ X = Y`.  Componentwise extensionality for the inner-system laws. -/
theorem over_transport_ext {𝒟 : Type u} [Cat.{u} 𝒟] {B B' : 𝒟} (e : B = B')
    {X : Over B} {Y : Over B'} (hd : X.dom = Y.dom) (hh : HEq X.hom Y.hom) : e ▸ X = Y := by
  subst e
  obtain ⟨xd, xh⟩ := X; obtain ⟨yd, yh⟩ := Y
  cases hd; cases hh; rfl

/-- **`F_refl` for the strict inner system** — the empty-suffix transition is the identity on `A′/V`
    (modulo `V ++ [] = V`).  Reduces to `over_transport_ext` + `catMap_nil_heq`. -/
theorem innerSliceTr_refl {V : List 𝒞} (X : innerSliceObj (𝒞 := 𝒞) V) :
    innerSliceTr (List.prefix_refl V) X = X := by
  unfold innerSliceTr
  apply over_transport_ext
  · -- dom: `(sliceCatObj suffix X).dom = X.dom`, i.e. `X.dom ++ V.drop V.length = X.dom`.
    show X.dom ++ prefixSuffix V V = X.dom
    rw [prefixSuffix, List.drop_length, List.append_nil]
  · -- hom: `catMap (V.drop V.length) X.hom` HEq `X.hom`.
    show HEq (catMap (prefixSuffix V V) X.hom) X.hom
    rw [prefixSuffix, List.drop_length]
    exact catMap_nil_heq X.hom

/-- Suffix concatenation: for `V ⊑ U ⊑ W`, the `V`→`W` suffix is the `V`→`U` suffix appended with
    the `U`→`W` suffix.  (From `W = V ++ dVU ++ dUW`, so `W.drop V.length = dVU ++ dUW`.) -/
theorem prefixSuffix_trans {V U W : List 𝒞} (hVU : prefixLe V U) (hUW : prefixLe U W) :
    prefixSuffix V W = prefixSuffix V U ++ prefixSuffix U W := by
  have e1 : V ++ prefixSuffix V U = U := prefixSuffix_eq hVU
  have e2 : U ++ prefixSuffix U W = W := prefixSuffix_eq hUW
  have e3 : V ++ (prefixSuffix V U ++ prefixSuffix U W) = W := by
    rw [← List.append_assoc, e1, e2]
  -- `prefixSuffix V W = W.drop V.length`; with `W = V ++ (dVU++dUW)`, `drop` strips the `V`-prefix.
  have key : W.drop V.length = (V ++ (prefixSuffix V U ++ prefixSuffix U W)).drop V.length := by
    rw [e3]
  show W.drop V.length = _
  rw [key, List.drop_left]

/-! ### Associativity bridges for `catForget`/`catTail`/`catArrange` across `(x++d)++e = x++(d++e)`

  The §1.547 `F_trans` law needs `catMap (d++e) f ≍ catMap e (catMap d f)`: appending the suffix
  `d++e` equals appending `d` then `e`, modulo the strict-but-not-definitional reindexing
  `(x++d)++e = x++(d++e)` (`List.append_assoc`).  We discharge it through three HEq "bridges" — one
  per recursive concatenation map — each proved by induction on the BASE list `x`/`t`, delegating the
  dependent product reindexing to a `subst`-kernel exactly as `catForget_nil_heq` did for `append_nil`.
  All three are honest theorems (the equation holds on the nose; only the `HEq`/`▸` bookkeeping is
  nontrivial). -/

/-- Generic cons-step kernel: `pair fst (snd ≫ ·)` preserves HEq across a domain reindexing `Q = P`.
    Given `u : P ⟶ R`, `v : Q ⟶ R` with `u ≍ v`, the cons-pairs over `prod a P` / `prod a Q` are HEq.
    `subst`s the reindexing so both `snd`s land in the same type, then the HEq becomes plain. -/
theorem pair_fst_snd_heq {a R P Q : 𝒞} (hPQ : Q = P)
    (u : P ⟶ R) (v : Q ⟶ R) (huv : HEq u v) :
    HEq (pair (fst : prod a P ⟶ a) ((snd : prod a P ⟶ P) ≫ u))
        (pair (fst : prod a Q ⟶ a) ((snd : prod a Q ⟶ Q) ≫ v)) := by
  subst hPQ; cases huv; rfl

/-- **Bridge A.**  `catForget x (d++e) ≍ catForget (x++d) e ≫ catForget x d` — forgetting the suffix
    `d++e` in one go equals forgetting `e` then `d` (modulo `(x++d)++e = x++(d++e)`).  Induction on `x`. -/
theorem catForget_append_heq : ∀ (x d e : List 𝒞),
    HEq (catForget (𝒞 := 𝒞) x (d ++ e))
        (catForget (𝒞 := 𝒞) (x ++ d) e ≫ catForget (𝒞 := 𝒞) x d)
  | [],      d, e => by
      -- both sides `∏(d++e) ⟶ 1` (since `[]++(d++e) = ([]++d)++e = d++e`); into terminal.
      show HEq (catForget (𝒞 := 𝒞) [] (d ++ e))
               (catForget (𝒞 := 𝒞) ([] ++ d) e ≫ catForget (𝒞 := 𝒞) [] d)
      rw [term_uniq (catForget [] (d ++ e)) (catForget ([] ++ d) e ≫ catForget [] d)]
  | a :: x', d, e => by
      -- LHS unfolds to a cons-`pair`; RHS composite unfolds to one too; bridge the two via the IH.
      have hf : catForget (𝒞 := 𝒞) (a :: x') (d ++ e)
          = pair (fst : prod a (listProd (x' ++ (d ++ e))) ⟶ a)
                 ((snd : prod a (listProd (x' ++ (d ++ e))) ⟶ _) ≫ catForget x' (d ++ e)) := rfl
      have hg : catForget (𝒞 := 𝒞) ((a :: x') ++ d) e ≫ catForget (𝒞 := 𝒞) (a :: x') d
          = pair (fst : prod a (listProd ((x' ++ d) ++ e)) ⟶ a)
                 ((snd : prod a (listProd ((x' ++ d) ++ e)) ⟶ _)
                   ≫ (catForget (𝒞 := 𝒞) (x' ++ d) e ≫ catForget (𝒞 := 𝒞) x' d)) := by
        show pair (fst : prod a (listProd ((x' ++ d) ++ e)) ⟶ a)
                  ((snd : _) ≫ catForget (x' ++ d) e)
              ≫ pair (fst : prod a (listProd (x' ++ d)) ⟶ a) ((snd : _) ≫ catForget x' d)
            = _
        refine pair_uniq _ _ _ ?_ ?_
        · rw [Cat.assoc, fst_pair, fst_pair]
        · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc]
      rw [hf, hg]
      exact pair_fst_snd_heq (by rw [List.append_assoc]) _ _ (catForget_append_heq x' d e)

/-- `catArrange` is natural in its source: `h ≫ catArrange t d g b = catArrange t d (h≫g) (h≫b)`.
    (Precomposition distributes over the `pair`-assembly; induction on `t`.) -/
theorem catArrange_snd_comp : ∀ (t d : List 𝒞) {W X : 𝒞} (h : W ⟶ X)
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ listProd d),
    h ≫ catArrange t d g b = catArrange t d (h ≫ g) (h ≫ b)
  | [],      d, W, X, h, g, b => rfl
  | a :: t', d, W, X, h, g, b => by
      show h ≫ pair (g ≫ fst) (catArrange t' d (g ≫ snd) b)
          = pair ((h ≫ g) ≫ fst) (catArrange t' d ((h ≫ g) ≫ snd) (h ≫ b))
      refine pair_uniq _ _ _ ?_ ?_
      · rw [Cat.assoc, fst_pair, Cat.assoc]
      · rw [Cat.assoc, snd_pair, catArrange_snd_comp t' d h (g ≫ snd) b, Cat.assoc]

/-- Generic cons-step kernel for `catTail`: `snd ≫ ·` preserves HEq across a domain reindexing `Q = P`.
    Given `u : P ⟶ R`, `v : Q ⟶ R` with `u ≍ v`, `snd ≫ u` (over `prod a P`) is HEq `snd ≫ v`. -/
theorem snd_comp_heq {a R P Q : 𝒞} (hPQ : Q = P)
    (u : P ⟶ R) (v : Q ⟶ R) (huv : HEq u v) :
    HEq ((snd : prod a P ⟶ P) ≫ u) ((snd : prod a Q ⟶ Q) ≫ v) := by
  subst hPQ; cases huv; rfl

/-- **Bridge B.**  `catTail x (d++e) ≍ catTail (x++d) e ≫ catTail x d` — projecting onto the suffix
    `d++e` equals projecting onto `e` then... wait: the suffix `d++e` is recovered from `(x++d)++e` by
    `catArrange d e` of its `d`-part (`catForget(x++d) e ≫ catTail x d`) and `e`-part (`catTail(x++d) e`).
    Induction on `x`; cons step bridges via the IH. -/
theorem catTail_append_heq : ∀ (x d e : List 𝒞),
    HEq (catTail (𝒞 := 𝒞) x (d ++ e))
        (catArrange (𝒞 := 𝒞) d e (catForget (𝒞 := 𝒞) (x ++ d) e ≫ catTail (𝒞 := 𝒞) x d)
                                  (catTail (𝒞 := 𝒞) (x ++ d) e))
  | [],      d, e => by
      -- LHS `= id (∏(d++e))`; RHS `= catArrange d e (catForget d e) (catTail d e) = catMap e id = id`.
      show HEq (catTail (𝒞 := 𝒞) [] (d ++ e))
               (catArrange (𝒞 := 𝒞) d e (catForget (𝒞 := 𝒞) ([] ++ d) e ≫ catTail (𝒞 := 𝒞) [] d)
                                         (catTail (𝒞 := 𝒞) ([] ++ d) e))
      have hL : catTail (𝒞 := 𝒞) [] (d ++ e) = Cat.id (listProd (d ++ e)) := rfl
      have hR : catArrange (𝒞 := 𝒞) d e (catForget (𝒞 := 𝒞) ([] ++ d) e ≫ catTail (𝒞 := 𝒞) [] d)
                  (catTail (𝒞 := 𝒞) ([] ++ d) e) = Cat.id (listProd (d ++ e)) := by
        show catArrange d e (catForget d e ≫ Cat.id _) (catTail d e) = _
        exact catMap_id d e
      rw [hL, hR]
  | a :: x', d, e => by
      -- LHS `= snd ≫ catTail x' (d++e)`; RHS's `catArrange` over `(a::x')++d = a::(x'++d)` unfolds to a
      -- cons-`pair`, whose `snd`-part is the IH'd `catArrange`; bridge the two `snd ≫ ·`s.
      have hL : catTail (𝒞 := 𝒞) (a :: x') (d ++ e)
          = (snd : prod a (listProd (x' ++ (d ++ e))) ⟶ _) ≫ catTail (𝒞 := 𝒞) x' (d ++ e) := rfl
      have hR : catArrange (𝒞 := 𝒞) d e
              (catForget (𝒞 := 𝒞) ((a :: x') ++ d) e ≫ catTail (𝒞 := 𝒞) (a :: x') d)
              (catTail (𝒞 := 𝒞) ((a :: x') ++ d) e)
          = (snd : prod a (listProd ((x' ++ d) ++ e)) ⟶ _)
            ≫ catArrange (𝒞 := 𝒞) d e (catForget (𝒞 := 𝒞) (x' ++ d) e ≫ catTail (𝒞 := 𝒞) x' d)
                                       (catTail (𝒞 := 𝒞) (x' ++ d) e) := by
        -- `catForget (a::(x'++d)) e ≫ catTail (a::x') d = snd ≫ (catForget(x'++d) e ≫ catTail x' d)`,
        -- and `catTail (a::(x'++d)) e = snd ≫ catTail(x'++d) e`; then `catArrange` is `snd ≫`-natural.
        have hb : catForget (𝒞 := 𝒞) ((a :: x') ++ d) e ≫ catTail (𝒞 := 𝒞) (a :: x') d
            = (snd : prod a (listProd ((x' ++ d) ++ e)) ⟶ _)
              ≫ (catForget (𝒞 := 𝒞) (x' ++ d) e ≫ catTail (𝒞 := 𝒞) x' d) := by
          show pair (fst : prod a (listProd ((x' ++ d) ++ e)) ⟶ a) ((snd : _) ≫ catForget (x' ++ d) e)
                ≫ ((snd : prod a (listProd (x' ++ d)) ⟶ _) ≫ catTail x' d) = _
          rw [← Cat.assoc, snd_pair, Cat.assoc]
        have ht : catTail (𝒞 := 𝒞) ((a :: x') ++ d) e
            = (snd : prod a (listProd ((x' ++ d) ++ e)) ⟶ _) ≫ catTail (𝒞 := 𝒞) (x' ++ d) e := rfl
        rw [hb, ht]
        exact (catArrange_snd_comp d e _ _ _).symm
      rw [hL, hR]
      exact snd_comp_heq (by rw [List.append_assoc]) _ _ (catTail_append_heq x' d e)

/-- Full heterogeneous congruence for composition (all three objects may differ).  Local copy
    (S1_49 has the same lemma but is not imported here). -/
theorem comp_heq {X X' A A' Bo Bo' : 𝒞} (f : X ⟶ A) (f' : X' ⟶ A')
    (s : A ⟶ Bo) (s' : A' ⟶ Bo') (hX : X = X') (hA : A = A') (hB : Bo = Bo')
    (hf : HEq f f') (hs : HEq s s') : HEq (f ≫ s) (f' ≫ s') := by
  cases hX; cases hA; cases hB; cases hf; cases hs; rfl

/-- Double-transport HEq: an arrow is HEq its transport along domain `hX` and codomain `hB`. -/
theorem transport_heq {X X' Bo Bo' : 𝒞} (hX : X = X') (hB : Bo = Bo') (R : X ⟶ Bo) :
    HEq R (hB ▸ hX ▸ R : X' ⟶ Bo') := by
  subst hX; subst hB; rfl

/-- **`catMap (d ++ e) f` HEq `catMap e (catMap d f)`** — appending the concatenated suffix `d++e`
    equals appending `d` then `e`, modulo the `(s++d)++e = s++(d++e)` reindexing.  (`F_trans` core.)
    `R := catMap e (catMap d f)` and `catMap (d++e) f` satisfy the SAME joint-monic characterization
    (over `catForget t (d++e)`/`catTail t (d++e)`): the bridges `catForget_append_heq`/`catTail_append_heq`
    convert `R`'s `catMap e`/`catMap d` projection laws into the `d++e` ones (each equation collapses
    from `HEq` to `Eq` because both sides share the type), and `cat_jointly_monic` finishes. -/
theorem catMap_append_heq {s t : List 𝒞} (d e : List 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    HEq (catMap (d ++ e) f) (catMap e (catMap d f)) := by
  have hS : listProd (𝒞 := 𝒞) ((s ++ d) ++ e) = listProd (s ++ (d ++ e)) := by rw [List.append_assoc]
  have hT : listProd (𝒞 := 𝒞) ((t ++ d) ++ e) = listProd (t ++ (d ++ e)) := by rw [List.append_assoc]
  let R := catMap (𝒞 := 𝒞) e (catMap d f)
  -- transport `R` into the `d++e`-typed slot; `R ≍ R'`.
  let R' : listProd (𝒞 := 𝒞) (s ++ (d ++ e)) ⟶ listProd (t ++ (d ++ e)) := hT ▸ hS ▸ R
  show HEq (catMap (d ++ e) f) R
  have hRR' : HEq R R' := transport_heq hS hT R
  -- `R`'s two projection laws (for the outer suffix `e`):
  have hRf : R ≫ catForget (𝒞 := 𝒞) (t ++ d) e = catForget (𝒞 := 𝒞) (s ++ d) e ≫ catMap d f :=
    catMap_forget e (catMap d f)
  have hRt : R ≫ catTail (𝒞 := 𝒞) (t ++ d) e = catTail (𝒞 := 𝒞) (s ++ d) e :=
    catMap_tail e (catMap d f)
  -- the FORGET equation `R' ≫ catForget t (d++e) = catForget s (d++e) ≫ f`.
  have hForget : R' ≫ catForget (𝒞 := 𝒞) t (d ++ e)
      = catForget (𝒞 := 𝒞) s (d ++ e) ≫ f := by
    apply eq_of_heq
    -- `R' ≫ catForget t (d++e) ≍ R ≫ (catForget(t++d)e ≫ catForget t d)`  (bridge A at t, `R ≍ R'`).
    refine HEq.trans (comp_heq R' R _ _ hS.symm hT.symm rfl hRR'.symm
      (catForget_append_heq t d e)) ?_
    -- compute `R ≫ (catForget(t++d)e ≫ catForget t d) = (catForget(s++d)e ≫ catForget s d) ≫ f`.
    have hcomp : R ≫ (catForget (𝒞 := 𝒞) (t ++ d) e ≫ catForget (𝒞 := 𝒞) t d)
        = (catForget (𝒞 := 𝒞) (s ++ d) e ≫ catForget (𝒞 := 𝒞) s d) ≫ f := by
      rw [← Cat.assoc, hRf, Cat.assoc, catMap_forget, ← Cat.assoc]
    rw [hcomp]
    -- `(catForget(s++d)e ≫ catForget s d) ≫ f ≍ catForget s (d++e) ≫ f`  (bridge A at s).
    exact comp_heq _ _ f f hS rfl rfl (catForget_append_heq s d e).symm (HEq.refl f)
  -- the TAIL equation `R' ≫ catTail t (d++e) = catTail s (d++e)`.
  have hTail : R' ≫ catTail (𝒞 := 𝒞) t (d ++ e) = catTail (𝒞 := 𝒞) s (d ++ e) := by
    apply eq_of_heq
    -- `R' ≫ catTail t (d++e) ≍ R ≫ catArrange d e (catForget(t++d)e ≫ catTail t d) (catTail(t++d)e)`.
    refine HEq.trans (comp_heq R' R _ _ hS.symm hT.symm rfl hRR'.symm
      (catTail_append_heq t d e)) ?_
    -- pull `R` inside the `catArrange`, simplify each leg, land on bridge B at `s`.
    rw [catArrange_snd_comp]
    have hleg1 : R ≫ (catForget (𝒞 := 𝒞) (t ++ d) e ≫ catTail (𝒞 := 𝒞) t d)
        = catForget (𝒞 := 𝒞) (s ++ d) e ≫ catTail (𝒞 := 𝒞) s d := by
      rw [← Cat.assoc, hRf, Cat.assoc, catMap_tail]
    have hleg2 : R ≫ catTail (𝒞 := 𝒞) (t ++ d) e = catTail (𝒞 := 𝒞) (s ++ d) e := hRt
    rw [hleg1, hleg2]
    exact (catTail_append_heq s d e).symm
  -- both equations hold ⟹ `R' = catMap (d++e) f` by joint monicity; transport back.
  have hR'eq : R' = catMap (𝒞 := 𝒞) (d ++ e) f := by
    apply cat_jointly_monic t (d ++ e)
    · rw [hForget, catMap_forget]
    · rw [hTail, catMap_tail]
  rw [← hR'eq]; exact hRR'.symm

/-- Transporting an `Over` along a base equality `e : B = B'` leaves its `dom` unchanged. -/
theorem over_transport_dom {𝒟 : Type u} [Cat.{u} 𝒟] {B B' : 𝒟} (e : B = B') (X : Over B) :
    (e ▸ X : Over B').dom = X.dom := by subst e; rfl

/-- Transporting an `Over` along a base equality `e : B = B'` leaves its `hom` HEq the original. -/
theorem over_transport_hom_heq {𝒟 : Type u} [Cat.{u} 𝒟] {B B' : 𝒟} (e : B = B') (X : Over B) :
    HEq (e ▸ X : Over B').hom X.hom := by subst e; rfl

/-- `catMap` respects HEq of its structure arrow across a LIST reindexing: if `s = s'`, `t = t'` as
    lists and `g ≍ g'`, then `catMap d g ≍ catMap d g'`.  (`subst`s the list equalities, then `cases`.) -/
theorem catMap_heq_congr {s t s' t' : List 𝒞} (d : List 𝒞)
    (hs : s = s') (ht : t = t')
    (g : listProd (𝒞 := 𝒞) s ⟶ listProd t) (g' : listProd (𝒞 := 𝒞) s' ⟶ listProd t')
    (hg : HEq g g') :
    HEq (catMap (𝒞 := 𝒞) d g) (catMap (𝒞 := 𝒞) d g') := by
  subst hs; subst ht; cases hg; rfl

/-- **`F_trans` for the strict inner system** — the composite suffix-transition equals appending the
    concatenated suffix (modulo `(V++d)++e = V++(d++e)`).  `innerSliceTr` of a prefix step transports
    `sliceCatObj (suffix)` along `V++suffix = U`; the composite over `V ⊑ U ⊑ W` therefore has `dom`
    `(X.dom ++ dVU) ++ dUW` and structure `catMap dUW (catMap dVU X.hom)`, while the direct `V ⊑ W`
    step has `dom` `X.dom ++ (dVU++dUW)` and `catMap (dVU++dUW) X.hom`.  `prefixSuffix_trans`
    (`dVW = dVU++dUW`) reconciles the doms (`append_assoc`) and `catMap_append_heq` the structures. -/
theorem innerSliceTr_trans {V U W : List 𝒞} (hVU : prefixLe V U) (hUW : prefixLe U W)
    (X : innerSliceObj (𝒞 := 𝒞) V) :
    innerSliceTr (hVU.trans hUW) X = innerSliceTr hUW (innerSliceTr hVU X) := by
  -- abbreviations for the three suffixes; `prefixSuffix_trans` gives `dVW = dVU ++ dUW`.
  have hdVW : prefixSuffix V W = prefixSuffix V U ++ prefixSuffix U W := prefixSuffix_trans hVU hUW
  -- intermediate `Y := innerSliceTr hVU X : Over U`, with computed `dom`/`hom`.
  have hYdom : (innerSliceTr hVU X).dom = X.dom ++ prefixSuffix V U := by
    unfold innerSliceTr; rw [over_transport_dom]; rfl
  have hYhom : HEq (innerSliceTr hVU X).hom (catMap (prefixSuffix V U) X.hom) := by
    unfold innerSliceTr; exact over_transport_hom_heq _ _
  -- the RHS `innerSliceTr hUW Y` dom/hom, peeling its outer transport.
  have hRdom : (innerSliceTr hUW (innerSliceTr hVU X)).dom
      = (X.dom ++ prefixSuffix V U) ++ prefixSuffix U W := by
    unfold innerSliceTr
    rw [over_transport_dom]
    show (innerSliceTr hVU X).dom ++ prefixSuffix U W = _
    rw [hYdom]
  -- reduce the goal (LHS) by `over_transport_ext` to dom-eq + hom-HEq.
  unfold innerSliceTr
  apply over_transport_ext
  · -- dom: `X.dom ++ dVW = (X.dom ++ dVU) ++ dUW`  (via `dVW = dVU++dUW` + `append_assoc`).
    show X.dom ++ prefixSuffix V W = (innerSliceTr hUW (innerSliceTr hVU X)).dom
    rw [hRdom, hdVW, List.append_assoc]
  · -- hom: `catMap dVW X.hom ≍ (innerSliceTr hUW Y).hom ≍ catMap dUW (catMap dVU X.hom)`.
    show HEq (catMap (prefixSuffix V W) X.hom) (innerSliceTr hUW (innerSliceTr hVU X)).hom
    -- peel the RHS outer transport, then its `sliceCatObj` (= `catMap dUW Y.hom`), then `hYhom`.
    refine HEq.trans ?_ (over_transport_hom_heq (prefixSuffix_eq hUW)
      (sliceCatObj (prefixSuffix U W) (innerSliceTr hVU X))).symm
    show HEq (catMap (prefixSuffix V W) X.hom)
             (catMap (prefixSuffix U W) (innerSliceTr hVU X).hom)
    -- replace `Y.hom` by `catMap dVU X.hom` (HEq), then `catMap_append_heq` does `dVW = dVU++dUW`.
    refine HEq.trans ?_ (catMap_heq_congr (prefixSuffix U W) hYdom.symm (prefixSuffix_eq hVU)
      (catMap (prefixSuffix V U) X.hom) (innerSliceTr hVU X).hom hYhom.symm)
    rw [hdVW]
    exact catMap_append_heq (prefixSuffix V U) (prefixSuffix U W) X.hom

end Freyd
