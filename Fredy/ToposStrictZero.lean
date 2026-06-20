/-
  Freyd & Scedrov, *Categories and Allegories* §1.944 — a topos has a STRICT
  COTERMINATOR (initial object `0`).

  The carrier is `Z := (bottomSub one).dom`, the domain of the empty/bottom
  subobject `∅_1 ↪ 1` built (sorry-free) in `Fredy/ToposColimits.lean` as the
  family-glb `⋂{all σ ⊆ 1}`.  We show `StrictCoterminator Z`: every `f : X → Z`
  is an isomorphism, hence (via `HasCoterminator.ofStrict`, S1_58) `Z` is initial.

  The proof mirrors `Fredy.any_map_to_zero_is_iso` (S1_61), but replaces the
  `PreLogos.bottom` field — which a topos does NOT carry (that route is circular
  on §1.543) — by `bottomSub` plus the §1.946 right-adjoint EMPTINESS lemma
  `g*(∅) ≤ ∅` (`invImage_bottomSub_le`), proved from `radjImage_adjunction`.
-/

import Fredy.RightAdjointImage
import Fredy.ToposColimits
import Fredy.S1_58
import Fredy.S1_61

open Freyd HasSubobjectClassifier

universe v u
variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

namespace Freyd

/-- **§1.946 emptiness.** Inverse image carries the bottom subobject to (below) the
    bottom subobject: `g*(∅_B) ≤ ∅_A`.  This is the backward direction of the
    `f* ⊣ f##` adjunction applied to `∅_B ≤ f##(∅_A)` (= `bottomSub_le`, ⊥ ≤ anything). -/
theorem invImage_bottomSub_le {A B : 𝒞} (g : A ⟶ B) :
    (InverseImage g (bottomSub B)).le (bottomSub A) :=
  (radjImage_adjunction g (bottomSub B) (bottomSub A)).2
    (bottomSub_le (radjImage g (bottomSub A)))

/-- Two subobjects of a common base that are mutually `≤` have isomorphic domains:
    the factoring maps `h : S.dom → T.dom`, `k : T.dom → S.dom` are mutual inverses
    (by left-cancelling the monics `S.arr`, `T.arr`). -/
theorem le_le_dom_iso {A : 𝒞} (S T : Subobject 𝒞 A) (hST : S.le T) (hTS : T.le S) :
    Isomorphic S.dom T.dom := by
  obtain ⟨h, hh⟩ := hST
  obtain ⟨k, hk⟩ := hTS
  refine ⟨h, k, ?_, ?_⟩
  · apply S.monic; rw [Cat.assoc, hk, hh, Cat.id_comp]
  · apply T.monic; rw [Cat.assoc, hh, hk, Cat.id_comp]

/-- The inverse image `g*(∅_B)` of the bottom has the SAME domain (up to iso) as
    `∅_A`: `≤` holds both ways (emptiness lemma + `bottomSub_le`). -/
theorem invImage_bottomSub_dom_iso {A B : 𝒞} (g : A ⟶ B) :
    Isomorphic (InverseImage g (bottomSub B)).dom (bottomSub A).dom :=
  le_le_dom_iso _ _ (invImage_bottomSub_le g) (bottomSub_le _)

section IsoHelpers
omit [Topos 𝒞]

/-- `Isomorphic` is symmetric (inline; `Isomorphic X Y` unfolds to `∃ f, IsIso f`). -/
theorem Isomorphic.symm' {X Y : 𝒞} (h : Isomorphic X Y) : Isomorphic Y X := by
  obtain ⟨f, g, hfg, hgf⟩ := h; exact ⟨g, f, hgf, hfg⟩

/-- `Isomorphic` is transitive (the composite iso). -/
theorem Isomorphic.trans' {X Y Z : 𝒞} (h : Isomorphic X Y) (h' : Isomorphic Y Z) :
    Isomorphic X Z := by
  obtain ⟨f, hf⟩ := h; obtain ⟨g, hg⟩ := h'; exact ⟨f ≫ g, isIso_comp hf hg⟩

end IsoHelpers

/-- **Cross-base bottom-domain iso** — the ONE remaining gap.
    `∅_A.dom ≅ ∅_B.dom` for all `A B`.

    It SUFFICES to prove `bottomSub_dom_iso A one` (then symm/trans via
    `Isomorphic.symm'`/`Isomorphic.trans'`).  This is EQUIVALENT to strict-initiality of
    `∅_1.dom` (`Z₁`), i.e. to the seed `Z₁ × A ≅ Z₁` (`0 × A ≅ 0`).  The natural reduction:
    `invImage_bottomSub_dom_iso (term A) : (InverseImage (term A) ∅_1).dom ≅ ∅_A.dom` (sorry-free),
    and `(InverseImage (term A) ∅_1).dom ≅ prod A Z₁` (pullback over `1` = product), so
    `∅_A.dom ≅ prod A Z₁`; the residual is exactly `prod A Z₁ ≅ Z₁`.

    PROVEN SORRY-FREE (so this is genuinely ONLY the seed):
    * `Z₁` is SUBTERMINAL: any `u v : W ⟶ Z₁` satisfy `u = v` by `(bottomSub one).monic _ _ (term_uniq …)`.
    * maps OUT of `∅_A.dom` are UNIQUE once `(bottomSub (∅_A.dom))` is entire (equalizer +
      `bottomSub_le` makes the equalizer of any two parallel maps iso).
    The MISSING half is EXISTENCE of `Z₁ ⟶ A` (the universal arrow `0 → A`).

    WHY THE AVAILABLE ADJOINTS DO NOT CLOSE IT (verified obstructions):
    * The LEFT adjoint route (`existsAlong (term A) ⊣ (term A)*`, `existsAlong_le_iff`) is
      UNAVAILABLE for a bare topos: `existsAlong`/`existsAlong_le_iff` live inside
      `S1_60 :: section BinRelDistributive`, which carries `variable [PreLogos 𝒞]`; a topos is
      NOT a `PreLogos` (that is precisely why `bottomSub` replaces `PreLogos.bottom` here).
    * The sorry-free RIGHT adjoint `radjImage` (`f* ⊣ f##`) gives only EMPTINESS
      `f*(⊥) ≅ ⊥` (`invImage_bottomSub_dom_iso`), used above — NOT the product seed.
    * Cartesian-closedness (`S1_92.topos_has_exponentials`, now genuinely proved via
      `power_objects_imply_all_baseable`) and the per-codomain partial-map classifier
      (`partialMapClassifier_exists B : Nonempty (LawfulPMC 𝒞 B)`, sorry-free in
      `Fredy/PartialMapClassifier.lean`) are AVAILABLE sorry-free, but neither yields `0 → A`
      directly: the generic "CCC ⟹ strict initial" argument presupposes `0` is ALREADY a
      colimit, and the PMC route needs the "undefined point" `1 ⟶ Ã` = name of the EMPTY
      subsingleton subobject of `A` (a genuine development inside the `pmcObj`/`pmRel`
      internals, not yet present).  In this repo finite cocompleteness
      (`topos_is_bicartesian`, `topos_has_coequalizers`) is itself still `sorry`.

    MISSING-LEMMA SIGNATURE (the precise irreducible obstruction):
      `(A : 𝒞) → ∃ f : (bottomSub (one : 𝒞)).dom ⟶ A, True`   (existence of `0 → A`),
    equivalently `(A : 𝒞) → IsIso (snd : prod A (bottomSub (one:𝒞)).dom ⟶ (bottomSub (one:𝒞)).dom)`.
    Hence left as a single, clearly-marked faithful `sorry`; every OTHER ingredient of §1.944 is
    closed sorry-free. -/
theorem bottomSub_dom_iso (A B : 𝒞) :
    Isomorphic (bottomSub A).dom (bottomSub B).dom := by
  sorry

/-- **§1.944 strictness.** Every map into `Z := ∅_1.dom` is an isomorphism.
    Mirror of `any_map_to_zero_is_iso` (S1_61), with `bottomSub` for `PreLogos.bottom`,
    `invImage_bottomSub_dom_iso` for `invImage_preserves_bottom`, and
    `bottomSub_dom_iso` for `bottom_dom_iso`. -/
theorem strict_coterminator_bottomSub_one :
    StrictCoterminator (bottomSub (one : 𝒞)).dom := by
  intro X f
  have hzeroMonic_mono : Mono (bottomSub (one : 𝒞)).arr := (bottomSub one).monic
  let p : X ⟶ one := term X
  -- f·∅₁.arr = p (both the unique map X → 1)
  have hp_eq : f ≫ (bottomSub (one : 𝒞)).arr = p := term_uniq _ _
  let pb := HasPullbacks.has p (bottomSub (one : 𝒞)).arr
  let c : Cone p (bottomSub (one : 𝒞)).arr := ⟨X, Cat.id X, f, by
    calc Cat.id X ≫ p = p := Cat.id_comp _
      _ = f ≫ (bottomSub one).arr := hp_eq.symm⟩
  let u : X ⟶ pb.cone.pt := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = Cat.id X := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = f := pb.lift_snd c
  -- π₁ is monic (pullback of monic) = the inverse-image arr
  have hπ₁_mono : Mono pb.cone.π₁ := (InverseImage p (bottomSub one)).monic
  have hπ₁_iso : IsIso pb.cone.π₁ :=
    ⟨u, hπ₁_mono (pb.cone.π₁ ≫ u) (Cat.id pb.cone.pt) (by
      calc (pb.cone.π₁ ≫ u) ≫ pb.cone.π₁ = pb.cone.π₁ ≫ (u ≫ pb.cone.π₁) := Cat.assoc _ _ _
        _ = pb.cone.π₁ ≫ Cat.id X := by rw [hu₁]
        _ = pb.cone.π₁ := Cat.comp_id _
        _ = (Cat.id pb.cone.pt) ≫ pb.cone.π₁ := (Cat.id_comp _).symm), hu₁⟩
  have hu_iso : IsIso u := by
    rcases hπ₁_iso with ⟨inv, hπ₁_inv, hinv_π₁⟩
    have hu_eq_inv : u = inv := hπ₁_mono u inv (by rw [hu₁, hinv_π₁])
    rw [hu_eq_inv]; exact ⟨pb.cone.π₁, hinv_π₁, hπ₁_inv⟩
  -- emptiness iso + cross-base iso: pb.cone.pt ≅ ∅₁.dom
  have hinv : Isomorphic (InverseImage p (bottomSub one)).dom (bottomSub X).dom :=
    invImage_bottomSub_dom_iso p
  have hbot : Isomorphic (bottomSub X).dom (bottomSub (one : 𝒞)).dom :=
    bottomSub_dom_iso X one
  let φ : (InverseImage p (bottomSub one)).dom ⟶ (bottomSub X).dom := hinv.choose
  have hφ_iso : IsIso φ := hinv.choose_spec
  let ψ : (bottomSub X).dom ⟶ (bottomSub (one : 𝒞)).dom := hbot.choose
  have hψ_iso : IsIso ψ := hbot.choose_spec
  have hπ₂_eq : pb.cone.π₂ = φ ≫ ψ := by
    apply hzeroMonic_mono (pb.cone.π₂) (φ ≫ ψ)
    have h₁ : pb.cone.π₂ ≫ (bottomSub one).arr = pb.cone.π₁ ≫ p := pb.cone.w.symm
    have h₂ : (φ ≫ ψ) ≫ (bottomSub one).arr = pb.cone.π₁ ≫ p :=
      term_uniq ((φ ≫ ψ) ≫ (bottomSub one).arr) (pb.cone.π₁ ≫ p)
    calc pb.cone.π₂ ≫ (bottomSub one).arr = pb.cone.π₁ ≫ p := h₁
      _ = (φ ≫ ψ) ≫ (bottomSub one).arr := by rw [h₂]
  have hπ₂_iso : IsIso pb.cone.π₂ := by rw [hπ₂_eq]; exact isIso_comp hφ_iso hψ_iso
  rw [← hu₂]; exact isIso_comp hu_iso hπ₂_iso

/-- **§1.944** — a topos has a (strict) coterminator `Z := ∅_1.dom`.  Assembled from
    the strict-coterminator witness via `HasCoterminator.ofStrict` (S1_58), using the
    `[Topos 𝒞]`-supplied `HasBinaryProducts`.  (Modulo the single `bottomSub_dom_iso`
    seed above; every other step is sorry-free.) -/
theorem topos_has_coterminator : Nonempty (HasCoterminator 𝒞) :=
  ⟨HasCoterminator.ofStrict strict_coterminator_bottomSub_one⟩

end Freyd
