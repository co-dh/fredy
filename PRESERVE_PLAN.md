# Task: extract a general "preservation" concept in `Fredy/S1_18.lean`

Add a reusable abstraction for "a functor preserves / reflects a property of morphisms",
and restate §1.181 (functor preserves isomorphisms) as an instance of it. This is a
mathlib-free Lean 4 project (toolchain `leanprover/lean4:v4.28.0`); do NOT add any imports
beyond what is already in the file.

## Context you need

`S1_18.lean` already defines `class Functor (F : 𝒞 → 𝒟)` with `map`/`map_id`/`map_comp`, and
(inside `section FunctorProperties`, which has `variable {F : 𝒞 → 𝒟} [h : Functor F]`) the
theorems `functor_preserves_left_inv`, `functor_preserves_right_inv`, `functor_preserves_iso`,
`functor_map_inv`. `IsIso` comes from the already-imported `Fredy.S1_41`. `Cat`, `⟶`, `≫` are
from `Fredy.S1_1`.

The file currently declares two *different* object universes:
`variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type w} [Cat.{v} 𝒟]` (with `universe v u w`).

## Why a universe change is required (do not skip)

The new `MorphProp` is a single predicate applied to arrows of BOTH `𝒞` and `𝒟`. Lean has no
first-class universe-polymorphic term arguments, so `𝒞` and `𝒟` must share one object
universe. Change `𝒟`'s universe from `w` to `u`.

## Exact edits

### Edit 1 — same object universe for 𝒟
In the file-level `variable` line, change `{𝒟 : Type w}` to `{𝒟 : Type u}`.
Then in the `universe v u w` line, drop `w` IF it is no longer used anywhere else in the file
(grep for `Type w` / `\bw\b` first; `compFunctor`'s `{ℰ : Type _}` introduces its own universe
and is unaffected). If `w` is still referenced, leave the `universe` line alone.

### Edit 2 — add the abstraction AFTER `end FunctorProperties`
Insert this block immediately after the `end FunctorProperties` line (these are top-level
defs that rely on the file-level `𝒞`/`𝒟` variables; `preserves_iso` reuses the section
theorems, so it must come after the section closes). Keep the existing four theorems exactly
as they are — do not rewrite them.

```lean
/-! ## §1.181 as a general concept: preservation / reflection of a morphism-property -/

/-- A property of morphisms, uniform across all categories (e.g. `@Mono`, `@IsIso`, `@Cover`). -/
abbrev MorphProp := ∀ {𝒜 : Type u} [Cat.{v} 𝒜] {X Y : 𝒜}, (X ⟶ Y) → Prop

/-- `F` PRESERVES `P` if it carries `P`-arrows to `P`-arrows. -/
def Preserves (F : 𝒞 → 𝒟) [hF : Functor F] (P : MorphProp.{v,u}) : Prop :=
  ∀ {X Y : 𝒞} {f : X ⟶ Y}, P f → P (hF.map f)

/-- `F` REFLECTS `P` if a `P`-image forces a `P`-arrow (the shape of the §1.531 Slice Lemma). -/
def Reflects (F : 𝒞 → 𝒟) [hF : Functor F] (P : MorphProp.{v,u}) : Prop :=
  ∀ {X Y : 𝒞} {f : X ⟶ Y}, P (hF.map f) → P f

/-- **§1.181 restated**: every functor preserves isomorphisms.  This is the one
    morphism-property preserved by *all* functors; preservation of `@Mono`, `@Cover`, … are
    separate statements that need hypotheses on `F`. -/
theorem preserves_iso (F : 𝒞 → 𝒟) [Functor F] : Preserves F @IsIso := by
  intro X Y f hf
  obtain ⟨g, hfg, hgf⟩ := hf
  exact ⟨_, functor_preserves_right_inv f g hfg, functor_preserves_left_inv f g hgf⟩
```

Note: `Preserves`/`Reflects` take `F` and its `Functor` instance explicitly, so they must be
defined OUTSIDE `section FunctorProperties` (otherwise the section's `variable F` collides).
`preserves_iso` takes `F` explicitly too — leave it that way.

## Do NOT

- Do not change `MorphProp`/`Preserves`/`Reflects` into mathlib's per-category
  `MorphismProperty C` style. Keep this lightweight single-universe version.
- Do not add a diagram/limit-preservation notion (preserves terminal/products/pullbacks) —
  that is a different shape (acts on `Cone`) and is out of scope.
- Do not touch any other file.

## Verify (must pass before you finish)

The build command for one file is `lake env lean Fredy/<name>.lean` (exit 0, no errors).
Run, from the repo root:

```
lake env lean Fredy/S1_18.lean
```

It must exit 0 with no errors or `sorry`. If the universe change broke `compFunctor` or any
existing theorem, fix the universe handling (the intended outcome is `𝒞` and `𝒟` both in
`Type u`) rather than reverting the abstraction. `S1_18.lean` has no dependents in the project,
so only this file needs to build, but if anything else imports it, build those too.

Report: the final `S1_18.lean` diff and the build result.
