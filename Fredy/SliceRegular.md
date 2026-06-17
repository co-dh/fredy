# `Fredy/SliceRegular.lean` — the slice `A/B` is pre-regular (§1.53), plus base-change (§1.547)

For a pre-regular base `A`, this file assembles `PreRegularCategory (Over B)` and the slice→slice
base-change (pullback) functor that §1.547 capitalization needs.

## `PreRegularCategory (Over B)` (§1.53)

The four mixins, all built constructively on this repo's hand-built `Cat`:

| mixin                          | instance                       | source                                              |
| ------------------------------ | ------------------------------ | --------------------------------------------------- |
| `HasTerminal (Over B)`         | `overHasTerminal` (`S1_44`)    | distinguished terminator `⟨B, 1_B⟩`                 |
| `HasPullbacks (Over B)`        | `overHasPullbacks`             | `overPullback*` of `S1_44` (§1.441: `A/B` Cartesian)|
| `HasBinaryProducts (Over B)`   | `overHasBinaryProducts`        | product = base pullback `X ×_B Y` of the structure maps |
| `PullbacksTransferCovers`      | `overPullbacksTransferCovers`  | §1.531 Slice Lemma: `Cover m ↔ Cover m.f`, `Σ` preserves pullbacks |

Result: `overPreRegular : PreRegularCategory (Over B)`.

## Base-change (pullback) functor `g* : A/D → A/C` (§1.547)

For a base arrow `g : C ⟶ D`, base-change `g*` sends an `A/D`-object to its pullback along `g`.
This is the slice→slice transition `A/(∏V) → A/(∏U)` used by the §1.547 capitalization inner
`CatSystem`.

| piece              | declaration             | what it is                                                        |
| ------------------ | ----------------------- | ----------------------------------------------------------------- |
| object part        | `baseChangeObj g X`     | `⟨X ×_D C, π₂ : X×_D C → C⟩`, the pullback of `X.hom` along `g`    |
| morphism cone      | `baseChangeCone g m`    | the `X`-pullback viewed over the cospan `(Y.hom, g)`, legs `(π₁ˣ ≫ m.f, π₂ˣ)` |
| morphism part      | `baseChangeMap g m`     | the induced map on pullbacks: the `Y`-pullback lift of `baseChangeCone g m` |
| functoriality      | `baseChangeFunctor g`   | `Functor (baseChangeObj g)` — `map_id`/`map_comp` via `Y`-pullback `lift_uniq` |

**Object part.** `⟨X, h : X → D⟩ ↦ ⟨X ×_D C, π₂⟩` where `X ×_D C` is the chosen pullback of the
cospan `X —h→ D ←g— C` and the structure map to `C` is the second projection.

**Morphism part.** For `m : ⟨X,h⟩ ⟶ ⟨Y,k⟩` (so `m.f ≫ k = h`), the `X`-cone `(π₁ˣ ≫ m.f, π₂ˣ)`
lands on the cospan `(k, g)` because
`(π₁ˣ ≫ m.f) ≫ k = π₁ˣ ≫ h = π₂ˣ ≫ g` (the first step is `m.w`, the second the `X`-pullback square).
Its lift through the `Y`-pullback preserves `π₂`, so it is an over-`C` arrow.

**Functoriality.** Both `map_id` and `map_comp` are uniqueness (`lift_uniq`) of the relevant
pullback lift: the candidate (identity, resp. the composite of the two induced maps) satisfies the
two projection equations, so it equals the canonical lift. No pullback-pasting lemma is needed
because uniqueness of the target lift does all the work.

## Status

Everything is sorry-free and axiom-free (`lean_verify` on `baseChangeFunctor` reports no axioms).
The construction is fully constructive on this repo's `Cat`; no mathlib, no choice.
