/-
  Bird & de Moor, *Algebra of Programming* §5.7  Lax natural transformations.

  Composition throughout is diagram order (`≫`); B&dM's `FR·φ ⊇ φ·GR` (with `φ : FA ← GA`)
  is mirrored to `G.map R ≫ φ b ⊑ φ a ≫ F.map R`.

  Lemma 5.1 (a relator preserves maps and their converses) is re-proved here as a PRIVATE
  copy — the canonical copy is being written in parallel in `Fredy.A5_1`; when it lands,
  this file's `relator_preserves_map_and_recip` should be deduped into a reference to it.
-/

import Fredy.A5_1
import Fredy.A5_4

universe v₁ v₂ u₁ u₂

namespace Freyd.Alg

/-- **B&dM 5.13** (LAX NATURAL TRANSFORMATION, mirrored to diagram order): `φ : G ⟶ F`,
    a family `φ a : G.obj a ⟶ F.obj a`, is LAX NATURAL when `G.map R ≫ φ b ⊑ φ a ≫ F.map R`
    for every `R : a ⟶ b`. -/
def LaxNatural {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
    (F G : Relator 𝒜 ℬ) (φ : ∀ a : 𝒜, G.obj a ⟶ F.obj a) : Prop :=
  ∀ {a b : 𝒜} (R : a ⟶ b), G.map R ≫ φ b ⊑ φ a ≫ F.map R

/-! ## §5.7 example (B&dM p.133): `∈` is lax natural from the power relator to the identity

  `powerRel_eps_lax` (`Fredy.A5_4`) is LITERALLY the defining inequality of `LaxNatural` with
  `G` the power relator (object map `PowerAllegory.powerObj`, hom map `powerRel`), `F` the
  identity relator, and `φ := ∋`.  The power relator is not bundled as a `Relator` here — its
  `map_comp` field needs the STRONGER `TabularUnitaryUnguardedPowerAllegory` hypothesis of
  `powerRel_comp`, more than this bare-`UnguardedPowerAllegory` section carries — so the
  example is stated as the raw inequality, with `Relator.idRelator`'s `map` unfolding to `id`
  on the nose. -/

section EpsExample

variable {𝒜 : Type u₁} [UnguardedPowerAllegory 𝒜]

/-- **B&dM p.133**: membership `∈` is lax natural from the power relator to the identity
    relator. -/
theorem eps_lax_natural {a b : 𝒜} (R : a ⟶ b) :
    powerRel R ≫ ∋ b ⊑ ∋ a ≫ (Relator.idRelator 𝒜).map R :=
  powerRel_eps_lax R

end EpsExample

/-! ## §5.7 Lemma 5.1: relators preserve maps and their converses

  Private copy (canonical copy lands in `Fredy.A5_1`).  Proof: apply `recip_of_comp_id`
  (`A4_2`, Prop 4.1) to `R := F.map f`, `S := F.map f°`, using `entire_id_le` +
  `F.map_mono`/`map_id`/`map_comp` both ways. -/

private theorem relator_preserves_map_and_recip {𝒜 : Type u₁} {ℬ : Type u₂}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
    (F : Relator 𝒜 ℬ) {a b : 𝒜} {f : a ⟶ b} (hf : Map f) :
    F.map f° = (F.map f)° ∧ Map (F.map f) := by
  have h1 : Cat.id (F.obj a) ⊑ F.map f ≫ F.map f° := by
    have h := F.map_mono (entire_id_le hf.1)
    rwa [F.map_id, F.map_comp] at h
  have h2 : F.map f° ≫ F.map f ⊑ Cat.id (F.obj b) := by
    have h := F.map_mono hf.2
    rwa [F.map_comp, F.map_id] at h
  exact recip_of_comp_id h1 h2

/-! ## §5.7 Theorem 5.2: lax naturality is equivalent to strict naturality on maps -/

section Theorem52

variable {𝒜 : Type u₁} {ℬ : Type u₂} [TabularAllegory 𝒜] [Allegory.{v₂} ℬ]
  (F G : Relator 𝒜 ℬ) (φ : ∀ a : 𝒜, G.obj a ⟶ F.obj a)

/-- **B&dM Theorem 5.2**: `φ` is lax natural from `G` to `F` iff it is STRICTLY natural on
    every map `f`. -/
theorem laxNatural_iff_strict_on_maps :
    LaxNatural F G φ ↔ ∀ {a b : 𝒜} (f : a ⟶ b), Map f → G.map f ≫ φ b = φ a ≫ F.map f := by
  constructor
  · intro hlax a b f hf
    have hFf : Map (F.map f) := (relator_preserves_map_and_recip F hf).2
    have hGf : Map (G.map f) := (relator_preserves_map_and_recip G hf).2
    have hFfrecip : F.map f° = (F.map f)° := (relator_preserves_map_and_recip F hf).1
    have hGfrecip : G.map f° = (G.map f)° := (relator_preserves_map_and_recip G hf).1
    have hle1 : G.map f ≫ φ b ⊑ φ a ≫ F.map f := hlax f
    have hle2 : G.map f° ≫ φ a ⊑ φ b ≫ F.map f° := hlax f°
    rw [hGfrecip, hFfrecip] at hle2
    have hle2a : φ a ⊑ G.map f ≫ (φ b ≫ (F.map f)°) := (map_shunt_left hGf _ _).mp hle2
    have hle2b : φ a ⊑ (G.map f ≫ φ b) ≫ (F.map f)° := by rw [Cat.assoc]; exact hle2a
    have hle2' : φ a ≫ F.map f ⊑ G.map f ≫ φ b := (map_shunt_right hFf _ _).mpr hle2b
    exact le_antisymm hle1 hle2'
  · intro hstrict a b R
    obtain ⟨c, h, k, hh, hk, hR, _⟩ := TabularAllegory.tabular (𝒜 := 𝒜) R
    have hFhmap : Map (F.map h) := (relator_preserves_map_and_recip F hh).2
    have hGhmap : Map (G.map h) := (relator_preserves_map_and_recip G hh).2
    have hFhrecip : F.map h° = (F.map h)° := (relator_preserves_map_and_recip F hh).1
    have hGhrecip : G.map h° = (G.map h)° := (relator_preserves_map_and_recip G hh).1
    have hstep_h : (G.map h)° ≫ φ c ⊑ φ a ≫ (F.map h)° := by
      have he : G.map h ≫ φ a = φ c ≫ F.map h := hstrict h hh
      apply (map_shunt_left hGhmap _ _).mpr
      have hent : Cat.id (F.obj c) ⊑ F.map h ≫ (F.map h)° := entire_id_le hFhmap.1
      calc φ c = φ c ≫ Cat.id (F.obj c) := (Cat.comp_id _).symm
        _ ⊑ φ c ≫ (F.map h ≫ (F.map h)°) := comp_mono_left _ hent
        _ = (φ c ≫ F.map h) ≫ (F.map h)° := (Cat.assoc _ _ _).symm
        _ = (G.map h ≫ φ a) ≫ (F.map h)° := by rw [he]
        _ = G.map h ≫ (φ a ≫ (F.map h)°) := Cat.assoc _ _ _
    have hFcomp : F.map (h° ≫ k) = (F.map h)° ≫ F.map k := by rw [F.map_comp, hFhrecip]
    have p1 : G.map R ≫ φ b = ((G.map h)° ≫ φ c) ≫ F.map k := by
      calc G.map R ≫ φ b
          = G.map (h° ≫ k) ≫ φ b := by rw [hR]
        _ = (G.map h° ≫ G.map k) ≫ φ b := by rw [G.map_comp]
        _ = ((G.map h)° ≫ G.map k) ≫ φ b := by rw [hGhrecip]
        _ = (G.map h)° ≫ (G.map k ≫ φ b) := Cat.assoc _ _ _
        _ = (G.map h)° ≫ (φ c ≫ F.map k) := by rw [hstrict k hk]
        _ = ((G.map h)° ≫ φ c) ≫ F.map k := (Cat.assoc _ _ _).symm
    have p2 : ((G.map h)° ≫ φ c) ≫ F.map k ⊑ φ a ≫ F.map R := by
      calc ((G.map h)° ≫ φ c) ≫ F.map k
          ⊑ (φ a ≫ (F.map h)°) ≫ F.map k := comp_mono_right hstep_h _
        _ = φ a ≫ ((F.map h)° ≫ F.map k) := Cat.assoc _ _ _
        _ = φ a ≫ F.map (h° ≫ k) := by rw [hFcomp]
        _ = φ a ≫ F.map R := by rw [← hR]
    rw [p1]; exact p2

end Theorem52

end Freyd.Alg
