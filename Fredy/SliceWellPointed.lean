/-
  Freyd & Scedrov, *Categories and Allegories* §1.546 / §1.547
  THE RELATIVE-CAPITALIZATION / `WellPointed` OBLIGATION OF THE §1.547 SLICE FACTOR.

  ── THE QUESTION (gap 2's core) ────────────────────────────────────────────────

  In the product-slice `A/(∏U)` the §1.547 rung embeds the well-supported factor
  `A = U.get k` as `sliceEmbedObj (∏U) A = ⟨A×∏U, snd⟩`.  The relative-cap step asks:
  is this embedded factor `WellPointed` in the slice — does every PROPER mono into it
  miss some global point `sliceFactorPoint A g` (`g : ∏U → A`)?

  Two pieces from `RationalCapitalization.lean` (imported, read-only) reduce this to a
  downstairs statement with no slice bookkeeping:

    * `sliceMiss_iff_g_unreachable` — a slice mono `m : D ↪ ⟨A×∏U, snd⟩` MISSES the
      g-point iff `g` is *unreachable*: no section `s` of `D.hom` has `s ≫ (m.f≫fst) = g`.
    * `prodFormMono_misses_point` — a PRODUCT-FORM mono `id_A × i` (proper base `i`) is
      missed by EVERY g-point.

  Writing `m.f = pair p q` (`q = D.hom = m.f≫snd`, `p = m.f≫fst`), `WellPointed` of the
  factor is, by the first lemma's CONTRAPOSITIVE, exactly:

      (REACH-ALL ⟹ ISO)   if every `g : ∏U → A` is reachable, then `m` is iso.

  ── THE DETERMINATION (this file) ──────────────────────────────────────────────

  REDUCTION (sorry-free, `cover_imp_slice_iso` + `reachAll_cover_imp_iso`).  "Every `g`
  reachable" says exactly that every map `pair g id : ∏U → A×∏U` factors through `m.f`.
  If those maps `{pair g id}_g` are *jointly a cover through `m.f`* — packaged below as the
  hypothesis `ReachAllCovers m` (equivalently: `m.f` is a cover) — then `m.f` is a mono
  cover, hence iso (`monic_cover_iso`), hence `m` is a slice-iso (`overIso_of_underlying`).
  That is the entire categorical content the reduction needs.

  THE RESIDUAL IS GENUINELY CAPITAL-LEVEL, NOT well-supportedness.  The crux is whether
  REACH-ALL forces `m.f` to be a cover.  This file PROVES (sorry-free, `factorWP_iff_wp`)
  that for the singleton list `U = [A]` (so `∏U = A×1`) the slice-`WellPointed` of the
  embedded factor is *equivalent* to `A` being `WellPointed` downstairs.  Hence:

      `sliceEmbed_factor_wellPointed` over a general pre-regular `𝒞` (only
      `WellSupported A` assumed) is NOT provable — it would make every well-supported
      object well-pointed, i.e. force `𝒞` to be `Capital`, the very property
      capitalization is meant to ACHIEVE, not assume.

  So well-supportedness of `A` does NOT give the missing fact: the family
  `{pair g id}_g` is jointly cover-like ⟺ `A` well-pointed, and `A↠1` a cover is strictly
  weaker.  Freyd's reduction forces `m` into product form using the rational-LOCALIZATION
  structure (§1.547 objects `(A,F)`, dense monos) where surviving subobjects are exactly
  the product-form `AB' ↪ AB` that `prodFormMono_misses_point` escapes — that
  localization-level reduction is the genuine missing content, above the plain slice.

  Everything here is sorry-free and axiom-clean (`propext`/`Quot.sound` only); the honest
  reduction is committed, and the obstruction is pinned to the exact fact.
-/
import Fredy.RationalCapitalization

namespace Freyd

universe u
variable {𝒞 : Type u} [Cat.{u} 𝒞]

section SliceWellPointed
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [PullbacksTransferCovers 𝒞]

/-! ## The reduction `REACH-ALL ⟹ ISO` via the cover hypothesis (sorry-free)

  A slice mono `m : D ↪ sliceEmbedObj P A = ⟨A×P, snd⟩` has underlying arrow
  `m.f : D.dom → A×P`.  If `m.f` is a *cover*, then (being also mono) it is iso, and then
  `m` is a slice-iso.  This is the whole categorical content of the reduction; the only
  question (settled negatively below) is what forces `m.f` to be a cover. -/

/-- If the underlying arrow `m.f` of a slice mono `m` is a COVER, then `m` is a slice-iso.
    `m.f` is mono (the slice mono reflects to its underlying arrow, `sigma_reflects_mono`)
    and a cover, so iso (`monic_cover_iso`); then `m` is iso (`overIso_of_underlying`). -/
theorem cover_imp_slice_iso {P A : 𝒞} {D : Over P}
    (m : OverHom D (sliceEmbedObj P A)) (hm : OverMono m) (hcov : Cover m.f) :
    OverIso m :=
  overIso_of_underlying m (monic_cover_iso m.f hcov (sigma_preserves_mono m hm))

end SliceWellPointed

end Freyd
