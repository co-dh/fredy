/-
  Freyd & Scedrov, *Categories and Allegories* §1.57
  Choice objects, AC regular categories, projective objects.

  §1.57  CHOICE: every entire relation targeted at C contains a map.
  AC REGULAR CATEGORY: all objects are choice (⇔ all are projective).
  Equivalent: every morphism factors as left-invertible ∘ monic.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-! ## §1.57 Choice and projectivity -/

/-- **§1.57**: C is CHOICE if every entire relation R : A → C contains a map f : A → C.
    (The map condition: 1_A ≤ R°R and there is a section.) -/
def Choice (C : 𝒞) : Prop :=
  ∀ {A : 𝒞} (R : BinRel 𝒞 A C), Entire R →
    ∃ (f : A ⟶ C), ∃ (h : A ⟶ R.src), h ≫ R.colA = Cat.id A ∧ h ≫ R.colB = f

/-- C is PROJECTIVE if every cover f : A ↠ C splits (∃ s: C→A with s≫f = id). -/
def Projective (C : 𝒞) : Prop :=
  ∀ {A : 𝒞} (f : A ⟶ C), Cover f → ∃ (s : C ⟶ A), s ≫ f = Cat.id C

/-- Every object is choice iff every object is projective (§1.57). -/
theorem choice_iff_projective : (∀ C : 𝒞, Choice C) ↔ (∀ C : 𝒞, Projective C) := by
  constructor
  · intro h C A f hcov
    -- f: A → C is a cover.  (graph f)°: C → A has left leg = f which is a cover,
    -- hence (graph f)° is entire (by tabulated_is_entire_iff_left_cover).  Apply
    -- Choice at A (the target of the reciprocal) to extract the section.
    have hent : Entire ((graph f)°) :=
      ((tabulated_is_entire_iff_left_cover f (Cat.id A) ((graph f)°).isMonicPair).mpr hcov)
    rcases h A ((graph f)°) hent with ⟨s, k, hkA, hkB⟩
    -- hkA: k ≫ f = id_C,  hkB: k ≫ id_A = s  →  k = s  →  s ≫ f = id_C
    dsimp [graph, reciprocal] at hkA hkB
    rw [Cat.comp_id] at hkB
    -- hkB: k = s, so rewrite the goal (s ≫ f = id_C) to k ≫ f = id_C
    refine ⟨s, ?_⟩
    rw [← hkB]
    exact hkA
  · intro h C A R hent
    -- R entire ⇒ R.colA is a cover (§1.564).  Projective at A splits it,
    -- giving a section s: A → R.src; then s ≫ R.colB: A → C is the map we need.
    have hcov : Cover R.colA :=
      ((tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent)
    rcases h A R.colA hcov with ⟨s, hs⟩
    -- hs: s ≫ R.colA = id_A
    -- The map is s ≫ R.colB: A → C, witness h = s
    refine ⟨s ≫ R.colB, s, hs, rfl⟩

/-- AC REGULAR CATEGORY: all objects are choice. -/
class ACRegularCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasPullbacks 𝒞, HasImages 𝒞 where
  all_choice : ∀ C : 𝒞, Choice C

/-- In an AC regular category, every f factors as p≫m where p is a
    split epi (cover with section) and m is monic. -/
theorem ac_factorization [ACRegularCategory 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    ∃ (C : 𝒞) (p : A ⟶ C) (m : C ⟶ B),
      (∃ (s : C ⟶ A), s ≫ p = Cat.id C) ∧ Mono m ∧ p ≫ m = f := by
  -- Resolve instance diamond: the variable line supplies HasImages etc.,
  -- and ACRegularCategory supplies them again.  Use letI to pick one.
  letI : HasBinaryProducts 𝒞 := ACRegularCategory.toHasBinaryProducts
  letI : HasPullbacks 𝒞 := ACRegularCategory.toHasPullbacks
  letI : HasImages 𝒞 := ACRegularCategory.toHasImages
  -- From all_choice, directly prove all objects are projective
  have h_all_proj : ∀ C : 𝒞, Projective C := by
    intro C A' f' hcov
    have hent : Entire ((graph f')°) :=
      ((tabulated_is_entire_iff_left_cover f' (Cat.id A') ((graph f')°).isMonicPair).mpr hcov)
    rcases ACRegularCategory.all_choice A' ((graph f')°) hent with ⟨s, k, hkA, hkB⟩
    dsimp [graph, reciprocal] at hkA hkB
    rw [Cat.comp_id] at hkB
    -- hkB: k = s, hkA: k ≫ f' = id_C.  Provide s and rewrite to k.
    refine ⟨s, ?_⟩
    rw [← hkB]
    exact hkA
  let I := image f
  -- image.lift f is a cover: if it factors through a monic m, image-minimality
  -- forces m to be iso (standard: image factorizations give cover ∘ monic).
  have h_cover : Cover (image.lift f : A ⟶ I.dom) := by
    intro D m g hm hfac
    -- hfac: g ≫ m = image.lift f, so f = g ≫ (m ≫ I.arr)
    -- The subobject S with arr = m ≫ I.arr allows f via g.
    have hmono_comp : Mono (m ≫ I.arr) := by
      intro W u v huv
      have h1 : u ≫ m = v ≫ m := I.monic _ _ (by
        simpa [Cat.assoc] using huv)
      exact hm _ _ h1
    have h_allows : Allows ⟨D, m ≫ I.arr, hmono_comp⟩ f := by
      refine ⟨g, ?_⟩
      calc g ≫ (m ≫ I.arr) = (g ≫ m) ≫ I.arr := (Cat.assoc _ _ _).symm
        _ = (image.lift f) ≫ I.arr := by rw [hfac]
        _ = f := image.lift_fac f
    have h_le : I.le ⟨D, m ≫ I.arr, hmono_comp⟩ := image_min f _ h_allows
    rcases h_le with ⟨h, hh⟩
    -- hh: h ≫ (m ≫ I.arr) = I.arr
    dsimp at hh
    have hhm : h ≫ m = Cat.id I.dom := I.monic (h ≫ m) (Cat.id I.dom) (by
      calc (h ≫ m) ≫ I.arr = h ≫ (m ≫ I.arr) := Cat.assoc _ _ _
        _ = I.arr := hh
        _ = Cat.id I.dom ≫ I.arr := (Cat.id_comp _).symm)
    have hmh : m ≫ h = Cat.id D := hm (m ≫ h) (Cat.id D) (by
      calc (m ≫ h) ≫ m = m ≫ (h ≫ m) := Cat.assoc _ _ _
        _ = m ≫ Cat.id I.dom := by rw [hhm]
        _ = m := Cat.comp_id _
        _ = Cat.id D ≫ m := (Cat.id_comp _).symm)
    -- IsIso m expects: ∃ g, m ≫ g = id_D ∧ g ≫ m = id_I.dom
    exact ⟨h, hmh, hhm⟩
  -- Split the cover via projectivity
  rcases h_all_proj I.dom (image.lift f) h_cover with ⟨s, hs⟩
  -- hs: s ≫ (image.lift f) = id_I
  refine ⟨I.dom, image.lift f, I.arr, ⟨s, hs⟩, I.monic, image.lift_fac f⟩

end Freyd
