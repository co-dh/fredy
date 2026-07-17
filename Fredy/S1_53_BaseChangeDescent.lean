/-
  Base-change descent for subobjects (§1.53, regular-category folklore).

  In a `PreRegularCategory 𝒞`, base-change (pullback) along a COVER `g : C ↠ D`
  REFLECTS isomorphisms among monos: if `m : X ⟶ Y` is a mono in `Over D` whose
  base-change `g* m := baseChangeMap g m` is an iso in `Over C`, then `m` is itself
  an iso in `Over D`.

  Equivalently, on subobjects: a subobject `m : S ↣ Y` whose pullback along a cover
  `g : C ↠ Y.left` is iso is itself iso.

  The proof is elementary and uses ONLY `PreRegularCategory` data (no images, no
  effective descent):

    * Covers are pullback-stable (`PullbacksTransferCovers`), so the projection
      `π₁ : Y ×_D C → Y.left` of the base-change pullback of `Y` along `g` is a cover
      (`coverProj_of_cover`, the `fst`-oriented transfer derived from the
      `snd`-oriented class field via a cone swap).

    * The base-change square gives `(g* m).left ≫ π₁ʸ = π₁ˣ ≫ m.left`.  With `g* m` iso,
      `s := (g* m)⁻¹.left ≫ π₁ˣ` satisfies `s ≫ m.left = π₁ʸ`, i.e. the cover `π₁ʸ` factors
      through the mono `m.left`.  A cover factoring through a mono forces that mono iso
      (the `Cover` definition applied to `m.left`).

    * Hence `m.left` is iso, so `m` is iso in `Over D` (`overIso_of_underlying`).

  Mathlib-free; imports only existing repo files (`Fredy.SliceRegular` transitively
  brings in `Over`/`baseChangeMap`/`Cover`/`PreRegularCategory`/`sigma_preserves_mono`).
-/

import Fredy.S1_53_SliceRegular

universe v u

variable {𝒞 : Type u} [CategoryTheory.Category.{v} 𝒞]

namespace Freyd

open CategoryTheory

/-! ## `fst`-oriented cover transfer

  `PullbacksTransferCovers` is stated for the *second* leg: in a pullback over the
  cospan `(f, g)`, `Cover f` forces `Cover π₂`.  We need the mirror image: `Cover g`
  forces `Cover π₁`.  Swap the cospan (a pullback over `(f, g)` with legs `(π₁, π₂)`
  is a pullback over `(g, f)` with legs `(π₂, π₁)`) and apply the class field. -/

/-- A cone over `(f, g)` swapped into a cone over `(g, f)`. -/
def Cone.swap {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C} (c : Cone f g) : Cone g f :=
  ⟨c.pt, c.π₂, c.π₁, c.w.symm⟩

/-- The swapped cone is a pullback when the original is (the universal property is
    symmetric in the two legs). -/
theorem Cone.swap_isPullback {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C} {c : Cone f g}
    (hc : c.IsPullback) : (Cone.swap c).IsPullback := by
  intro d
  -- `d : Cone g f` is a `Cone f g` after swapping back.
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc (Cone.swap d)
  exact ⟨u, ⟨hu₂, hu₁⟩, fun v hv₁ hv₂ => huniq v hv₂ hv₁⟩

/-- **`fst`-oriented transfer.**  In a pullback over the cospan `(f, g)`, if `g` is a
    cover then the *first* projection `π₁` is a cover. -/
theorem coverProj_of_cover [PullbacksTransferCovers 𝒞] {A B C : 𝒞} {f : A ⟶ C}
    {g : B ⟶ C} {c : Cone f g} (hc : c.IsPullback) (hg : Cover g) : Cover c.π₁ :=
  PullbacksTransferCovers.pullbacks_transfer_covers (Cone.swap c) (Cone.swap_isPullback hc) hg

/-! ## Base-change along a cover reflects isos among monos -/

/-- **Base-change along a cover reflects isos among monos.**

  Let `g : C ⟶ D` be a cover, `m : X ⟶ Y` a mono in `Over D`, and suppose the
  base-change `baseChangeMap g m : g* X ⟶ g* Y` is an iso in `Over C`.  Then `m` is an
  iso in `Over D`.

  (Subobject form: a subobject `m : S ↣ Y` whose pullback along the cover
  `g : C ↠ Y.left` is iso is itself iso.) -/
theorem isIso_of_baseChange_isIso_of_cover {C D : 𝒞} [HasPullbacks 𝒞]
    [PullbacksTransferCovers 𝒞] (g : C ⟶ D) (hg : Cover g)
    {X Y : Over D} (m : OverHom X Y) (hm : OverMono m)
    (hbc : OverIso (baseChangeMap g m)) : OverIso m := by
  -- It suffices to show the underlying arrow `m.left` is iso (`overIso_of_underlying`).
  refine overIso_of_underlying m ?_
  -- `m.left` is mono in `𝒞` (Σ preserves monos).
  have hmf : Monic m.left := sigma_preserves_mono m hm
  -- The chosen base-change pullbacks for `X` and `Y` along `g` (kept as `let` so the
  -- `baseChangeMap`/`baseChangeObj` defs unfold to them definitionally).
  let PX := HasPullbacks.has X.hom g
  let PY := HasPullbacks.has Y.hom g
  -- `π₁ʸ : Y ×_D C → Y.left` is a cover: it is `fst` in the pullback of `g` along `Y.hom`.
  have hπ₁Y_cover : Cover PY.cone.π₁ := coverProj_of_cover PY.cone_isPullback hg
  -- The base-change square: `(g* m).left ≫ π₁ʸ = π₁ˣ ≫ m.left`  (`lift_fst` of the lift).
  have hsq : (baseChangeMap g m).left ≫ PY.cone.π₁ = PX.cone.π₁ ≫ m.left :=
    PY.lift_fst (baseChangeCone g m)
  -- `g* m` iso gives an inverse arrow `inv` with `inv ≫ (g* m).left = id`.
  obtain ⟨inv, _hinv₁, hinv₂⟩ := overIso_underlying hbc
  -- `s := inv ≫ π₁ˣ` factors the cover `π₁ʸ` through the mono `m.left`:
  --   `s ≫ m.left = inv ≫ (π₁ˣ ≫ m.left) = inv ≫ ((g* m).left ≫ π₁ʸ)
  --           = (inv ≫ (g* m).left) ≫ π₁ʸ = π₁ʸ`.
  have hfactor : (inv ≫ PX.cone.π₁) ≫ m.left = PY.cone.π₁ := by
    calc (inv ≫ PX.cone.π₁) ≫ m.left
        = inv ≫ (PX.cone.π₁ ≫ m.left) := CategoryTheory.Category.assoc _ _ _
      _ = inv ≫ ((baseChangeMap g m).left ≫ PY.cone.π₁) := by rw [hsq]
      _ = (inv ≫ (baseChangeMap g m).left) ≫ PY.cone.π₁ := (CategoryTheory.Category.assoc _ _ _).symm
      _ = PY.cone.π₁ := by rw [hinv₂, CategoryTheory.Category.id_comp]
  -- A cover (`π₁ʸ`) factoring through a mono (`m.left`) forces the mono iso.
  exact hπ₁Y_cover m.left (inv ≫ PX.cone.π₁) hmf hfactor

/-- Specialized to a `PreRegularCategory`: base-change along a cover reflects isos
    among monos.  (`HasPullbacks`/`PullbacksTransferCovers` come from
    `PreRegularCategory`.) -/
theorem isIso_of_baseChange_isIso_of_cover_preRegular [PreRegularCategory 𝒞]
    {C D : 𝒞} (g : C ⟶ D) (hg : Cover g) {X Y : Over D} (m : OverHom X Y)
    (hm : OverMono m) (hbc : OverIso (baseChangeMap g m)) : OverIso m :=
  isIso_of_baseChange_isIso_of_cover g hg m hm hbc

end Freyd
