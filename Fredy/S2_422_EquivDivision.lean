/-
  Freyd & Scedrov, *Categories and Allegories* §2.422.

  HEADLINE (§2.422, division allegory):
    For any equivalence relation `E`, `E = E / E` (right division of `E` by itself).

  COROLLARY (§2.421 + §2.422, power allegory):
    In a power allegory every equivalence relation has the form `f ≫ f°` for a map `f`
    (already proven upstream as `equivRel_eq_map_comp_recip`); hence if coreflexives split
    then every equivalence relation is *effective* — it splits as `h ≫ h° = E`, `h° ≫ h = 1`.

  Builds on:
    * `le_div_iff`, `div_self_comp_le`, `one_le_div_self`  (S2_3, §2.31/2.314)
    * `EquivalenceRel`, `Reflexive`, `Symmetric`, `Transitive`, `Map`, `Simple`, `Coreflexive`
      (S2_1, §2.12)
    * `equivRel_idem`, `equivRel_eq_map_comp_recip`  (S2_4, §2.422)
-/

import Fredy.S2_1
import Fredy.S2_2
import Fredy.S2_3
import Fredy.S2_4

universe v u

namespace Freyd.Alg

/-! ## §2.422  `E = E / E` for an equivalence relation -/

/-- **§2.422**: in any division allegory, every equivalence relation `E` satisfies `E = E / E`
    (right division of `E` by itself).

    * `E ⊑ E/E`: by `le_div_iff` this reduces to `E ≫ E ⊑ E`, i.e. transitivity.
    * `E/E ⊑ E`: `E/E = (E/E) ≫ 1 ⊑ (E/E) ≫ E ⊑ E`, using reflexivity `1 ⊑ E`
      and the division counit `(E/E) ≫ E ⊑ E`. -/
theorem equivRel_eq_div_self {𝒜 : Type u} [DivisionAllegory 𝒜] {a : 𝒜} {E : a ⟶ a}
    (hE : EquivalenceRel E) : E = E / E := by
  apply le_antisymm
  · -- E ⊑ E/E  ⟺  E ≫ E ⊑ E  (Transitive E)
    exact (le_div_iff E E E).mpr hE.2.2
  · -- E/E ⊑ E:  E/E = (E/E) ≫ 1 ⊑ (E/E) ≫ E ⊑ E
    have h1 : E / E ⊑ (E / E) ≫ E := by
      have h := comp_mono_left (E / E) hE.1        -- (E/E) ≫ 1 ⊑ (E/E) ≫ E
      rwa [Cat.comp_id] at h
    exact le_trans h1 (div_self_comp_le E)

/-! ## §2.421 + §2.422  Effectiveness in a power allegory

  In a power allegory, `equivRel_eq_map_comp_recip` already gives `E = f ≫ f°` with `f = A(E)`
  a map.  We upgrade this to *effectiveness* once coreflexives split.

  The coreflexive `f° ≫ f` (which `⊑ 1` because `f` is simple) splits as `g° ≫ g = f° ≫ f`,
  `g ≫ g° = 1`.  Setting `h = f ≫ g°` gives a map with `h ≫ h° = E`, `h° ≫ h = 1`:

      h ≫ h° = f (g° g) f° = f (f° f) f° = (f f°)(f f°) = E·E = E,
      h° ≫ h = g (f° f) g° = g (g° g) g° = (g g°)(g g°) = 1·1 = 1. -/

/-- **§2.421/§2.422 corollary**: in a power allegory in which coreflexives split, every
    equivalence relation `E` is effective — there is a map `h` with `h ≫ h° = E` and
    `h° ≫ h = 1`.  The "coreflexives split" hypothesis is taken in the exact shape produced by
    `coreflexive_splits` (S2_2): a coreflexive `A` splits as `g° ≫ g = A`, `g ≫ g° = 1`. -/
theorem equivRel_effective_of_coreflexives_split {𝒜 : Type u} [PowerAllegory 𝒜] {a : 𝒜}
    (E : a ⟶ a) (hE : EquivalenceRel E) (hbox : codBox E = codBox (∋ a))
    (hsplit : ∀ {x : 𝒜} {A : x ⟶ x}, Coreflexive A →
      ∃ (c : 𝒜) (g : c ⟶ x), Map g ∧ g° ≫ g = A ∧ g ≫ g° = Cat.id c) :
    ∃ (c : 𝒜) (h : a ⟶ c), Map h ∧ h ≫ h° = E ∧ h° ≫ h = Cat.id c := by
  -- §2.421/§2.422: E = f ≫ f° with f = A(E) a map.
  obtain ⟨f, hf, hEeq⟩ := equivRel_eq_map_comp_recip E hE hbox
  have hffE : f ≫ f° = E := hEeq.symm
  -- f° ≫ f is coreflexive (f is simple); split it.
  have hcor : Coreflexive (f° ≫ f) := hf.2
  obtain ⟨d, g, _, hgg, hgg1⟩ := hsplit hcor   -- hgg : g° ≫ g = f° ≫ f,  hgg1 : g ≫ g° = 1_d
  -- The candidate splitting map h = f ≫ g°.
  have hrecip : (f ≫ g°)° = g ≫ f° := by rw [Allegory.recip_comp, Allegory.recip_recip]
  -- h ≫ h° = E
  have hHHr : (f ≫ g°) ≫ (f ≫ g°)° = E := by
    rw [hrecip]
    have hstep : (f ≫ g°) ≫ (g ≫ f°) = (f ≫ f°) ≫ (f ≫ f°) := by
      have a1 : (f ≫ g°) ≫ (g ≫ f°) = f ≫ (g° ≫ g) ≫ f° := by simp only [Cat.assoc]
      have a2 : f ≫ (f° ≫ f) ≫ f° = (f ≫ f°) ≫ (f ≫ f°) := by simp only [Cat.assoc]
      rw [a1, hgg, a2]
    rw [hstep, hffE, equivRel_idem hE]
  -- h° ≫ h = 1_d
  have hHrH : (f ≫ g°)° ≫ (f ≫ g°) = Cat.id d := by
    rw [hrecip]
    have hstep : (g ≫ f°) ≫ (f ≫ g°) = (g ≫ g°) ≫ (g ≫ g°) := by
      have a1 : (g ≫ f°) ≫ (f ≫ g°) = g ≫ (f° ≫ f) ≫ g° := by simp only [Cat.assoc]
      have a2 : g ≫ (g° ≫ g) ≫ g° = (g ≫ g°) ≫ (g ≫ g°) := by simp only [Cat.assoc]
      rw [a1, ← hgg, a2]
    rw [hstep, hgg1, Cat.id_comp]
  refine ⟨d, f ≫ g°, ⟨?_, ?_⟩, hHHr, hHrH⟩
  · -- Entire (f ≫ g°): dom = id_a, i.e. id_a ⊑ (f≫g°)(f≫g°)° = E, by reflexivity.
    show Cat.id a ∩ (f ≫ g°) ≫ (f ≫ g°)° = Cat.id a
    have hle : Cat.id a ⊑ (f ≫ g°) ≫ (f ≫ g°)° := by rw [hHHr]; exact hE.1
    dsimp [le] at hle; exact hle
  · -- Simple (f ≫ g°): (f≫g°)°(f≫g°) = 1_d ⊑ 1_d.
    show (f ≫ g°)° ≫ (f ≫ g°) ⊑ Cat.id d
    rw [hHrH]; exact le_refl _

end Freyd.Alg
