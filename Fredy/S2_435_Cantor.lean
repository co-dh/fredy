/-
  Freyd & Scedrov, *Categories and Allegories* §2.435 (Cantor, algebraic form)
  and §2.353 (cancellation on maps).

  §2.435  CANTOR (algebraic).  "If a connected division allegory has a thick
          endomorphism, then it is equivalent to the one-object one-morphism
          allegory."  The engine is §2.436 (`one_object_pre_power_inconsistent`,
          S2_43): a thick endomorphism `T : α ⟶ α` forces `1_α = 𝟘`, hence
          `T = 1_α`.  Connectivity (strong form: an entire morphism into α from
          every object) then spreads the collapse: every object β satisfies
          `1_β = 𝟘`, i.e. is a terminator, and every hom-set is the singleton
          `{𝟘}` — exactly the one-object one-morphism allegory.

          Cantor application: in a power allegory a morphism `F : a → [a]` with
          `F°F = 1` makes `T = F∋` thick (witness `R̂ = A(R)F°`), so it cannot
          coexist with strong connectivity unless the allegory is degenerate.

  §2.353  CANCELLATION ON MAPS.  "In a tabular division allegory it suffices to
          verify the [straight] cancellation property on maps."  Given a
          tabulation `S/ₛS = ℓ°r` (ℓ, r maps), the maps-only cancellation
          `fS = gS → f = g` forces `ℓ = r`, whence `S/ₛS = ℓ°ℓ ⊑ 1`, i.e. S is
          straight.  This is the map-restricted strengthening of S2_3's
          `straight_of_cancel` (which needs the property for all simple F, G).

  Self-contained, mathlib-free.  Lives on S2_1 (Map/Simple/Entire/Tabulation),
  S2_3 (symmetric division, Straight), S2_4 (Thick, PowerAllegory, A(R)) and
  S2_43 (diag, §2.436 inconsistency core).
-/

import Fredy.S1_1
import Fredy.S2_1
import Fredy.S2_2
import Fredy.S2_3
import Fredy.S2_4
import Fredy.S2_43
import Fredy.S2_423_ConnectedUnit  -- StronglyConnectedAllegory (canonical map-version)

universe v u

namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ## §2.435  Connectivity

  Freyd's "connected" allegory: there is a morphism between every ordered pair of
  objects.  Reciprocation `°` makes this relation symmetric, which is the sense in
  which "connectivity implies strong connectivity" (a morphism both ways).

  The §2.435 / §2.423 arguments consume the book's STRONG CONNECTIVITY: every object
  has a map into α (Freyd: "every object has a map to α").  In a power allegory that
  map is `Λ(R)`; in a bare division allegory it is NOT constructible from a mere
  morphism, so it is the explicit hypothesis `StronglyConnectedAllegory` (reused from
  `S2_423`; a map is entire, which is all the §2.436 spread needs). -/

/-! ## §2.435  A thick endomorphism collapses its object

  §2.436 (`one_object_pre_power_inconsistent`, S2_43) already shows a thick
  `T : α ⟶ α` (with Freyd's suppressed box guard `codBox (diag T) = codBox T`)
  forces `1_α = 𝟘`.  We package the two §2.435 consequences: `T = 1_α`, and —
  under strong connectivity — degeneracy of every object. -/

/-- §2.435 (local collapse): a thick endomorphism equals the identity.
    `1_α = 𝟘` (§2.436) gives `T = T·1 = T·𝟘 = 𝟘 = 1`. -/
theorem thick_endo_eq_id {α : 𝒜} (T : α ⟶ α) (hT : Thick T)
    (hBox : codBox (diag T) = codBox T) : T = Cat.id α := by
  have hα : Cat.id α = (𝟘 : α ⟶ α) := one_object_pre_power_inconsistent T hT hBox
  calc T = T ≫ Cat.id α := (Cat.comp_id T).symm
    _ = T ≫ (𝟘 : α ⟶ α) := by rw [hα]
    _ = (𝟘 : α ⟶ α) := DistributiveAllegory.comp_zero T
    _ = Cat.id α := hα.symm

/-- §2.435 (degeneracy): in a strongly connected division allegory, a thick
    endomorphism `T : α ⟶ α` forces EVERY object β to be a terminator, `1_β = 𝟘`.

    Freyd: "the morphism 0:β→α factors as an entire morphism 0̂ followed by 1; that
    is 0 is entire; hence every object is a terminator."  Here: `1_α = 𝟘` (§2.436);
    strong connectivity gives an entire `h : β ⟶ α`; `h = h·1_α = h·𝟘 = 𝟘`, so the
    zero morphism `β → α` is entire, whence `1_β ⊑ 𝟘·𝟘° = 𝟘`. -/
theorem thick_endo_degenerate (hSC : StronglyConnectedAllegory 𝒜)
    {α : 𝒜} (T : α ⟶ α) (hT : Thick T)
    (hBox : codBox (diag T) = codBox T) :
    ∀ (β : 𝒜), Cat.id β = (𝟘 : β ⟶ β) := by
  have hα : Cat.id α = (𝟘 : α ⟶ α) := one_object_pre_power_inconsistent T hT hBox
  intro β
  obtain ⟨h, hh⟩ := hSC β α
  -- h = 𝟘 : every morphism into α is zero once `1_α = 𝟘`.
  have hzero : h = (𝟘 : β ⟶ α) := by
    calc h = h ≫ Cat.id α := (Cat.comp_id h).symm
      _ = h ≫ (𝟘 : α ⟶ α) := by rw [hα]
      _ = (𝟘 : β ⟶ α) := DistributiveAllegory.comp_zero h
  -- Entire h gives `1_β ⊑ h h°`; with `h = 𝟘` this is `1_β ⊑ 𝟘`.
  have hEnt : Cat.id β ⊑ h ≫ h° := by
    have hd := hh.1; dsimp [Entire, dom] at hd; rw [← hd]; exact inter_lb_right _ _
  rw [hzero, recip_zero, DistributiveAllegory.zero_comp] at hEnt
  exact le_antisymm hEnt (zero_le _)

/-- §2.435 (every hom is a singleton): under the hypotheses of
    `thick_endo_degenerate`, every morphism is the zero morphism — the allegory is
    the one-object one-morphism allegory. -/
theorem thick_endo_all_zero (hSC : StronglyConnectedAllegory 𝒜)
    {α : 𝒜} (T : α ⟶ α) (hT : Thick T)
    (hBox : codBox (diag T) = codBox T) :
    ∀ {β γ : 𝒜} (R : β ⟶ γ), R = (𝟘 : β ⟶ γ) := by
  intro β γ R
  have hβ := thick_endo_degenerate hSC T hT hBox β
  calc R = Cat.id β ≫ R := (Cat.id_comp R).symm
    _ = (𝟘 : β ⟶ β) ≫ R := by rw [hβ]
    _ = (𝟘 : β ⟶ γ) := DistributiveAllegory.zero_comp R

/-- §2.435 (Freyd's exact phrasing "0 is entire"): under the hypotheses of
    `thick_endo_degenerate`, the zero morphism `β → γ` is entire. -/
theorem thick_endo_zero_entire (hSC : StronglyConnectedAllegory 𝒜)
    {α : 𝒜} (T : α ⟶ α) (hT : Thick T)
    (hBox : codBox (diag T) = codBox T) :
    ∀ (β γ : 𝒜), Entire (𝟘 : β ⟶ γ) := by
  intro β γ
  have hβ := thick_endo_degenerate hSC T hT hBox β
  dsimp [Entire, dom]
  rw [recip_zero, DistributiveAllegory.comp_zero, hβ, Allegory.inter_idem]

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [PowerAllegory 𝒜]

/-! ## §2.435  Cantor application: `T = F∋` is thick when `F°F = 1`

  Freyd: "Suppose in a power allegory there exists `F : a → [a]` with `F°F = 1`
  (a partial map covering `[a]`).  Then `T = F∋` is thick: given R define
  `R̂ = (R/∋)F°`; R̂ is entire; `R̂T ⊑ (R/∋)F°F∋ ⊑ (R/∋)∋ ⊑ R`,
  `R̂°R ⊑ F(∋/R)R ⊑ F∋ = T`.  (We used only the thickness of ∋.)"

  We take the honest witness `R̂ = A(R)F°` with `A(R) = R/ₛ∋` (S2_4), the map Freyd
  writes `R/∋`.  The three §2.431 containments fall out of `F°F = 1`, the map-ness
  of `A(R)` (§2.412/413, box-matched thickness of ∋) and `A(R)∋ = R`.  The box
  guard for `A(R)` is discharged because `F°F = 1` makes `codBox (F∋) = codBox ∋`. -/

/-- `codBox (F∋) = codBox ∋` when `F°F = 1` (§2.41 box bookkeeping).
    `codBox R = 1 ∩ R°R`; for `R = F∋`, `(F∋)°(F∋) = ∋°(F°F)∋ = ∋°∋`. -/
theorem codBox_comp_eps {a : 𝒜} (F : a ⟶ PowerAllegory.powerObj a)
    (hF : F° ≫ F = Cat.id (PowerAllegory.powerObj a)) :
    codBox (F ≫ ∋ a) = codBox (∋ a) := by
  show dom ((F ≫ ∋ a)°) = dom ((∋ a)°)
  dsimp only [dom]
  rw [Allegory.recip_recip, Allegory.recip_recip, Allegory.recip_comp]
  -- goal: 1 ∩ (∋° ≫ F°) ≫ (F ≫ ∋) = 1 ∩ ∋° ≫ ∋
  congr 1
  rw [Cat.assoc (∋ a)° F° (F ≫ ∋ a), ← Cat.assoc F° F (∋ a), hF, Cat.id_comp]

/-- §2.435 Cantor: in a power allegory, `F : a → [a]` with `F°F = 1` makes
    `T = F∋` a thick endomorphism.  Witness `R̂ = A(R)F°` (book `(R/∋)F°`). -/
theorem cantor_thick_endo {a : 𝒜} (F : a ⟶ PowerAllegory.powerObj a)
    (hF : F° ≫ F = Cat.id (PowerAllegory.powerObj a)) :
    Thick (F ≫ ∋ a) := by
  rw [thick_iff_existential]
  intro c R hbox
  -- translate the box guard of T = F∋ to the box guard of ∋.
  have hboxA : codBox R = codBox (∋ a) := hbox.trans (codBox_comp_eps F hF)
  have hAmap : Map (A R) := A_is_map R hboxA
  -- witness R̂ = A(R) ≫ F°
  refine ⟨A R ≫ F°, ?_, ?_, ?_⟩
  · -- Entire R̂ : R̂R̂° = A(R)(F°F)A(R)° = A(R)A(R)° ⊒ 1.
    have hAent : Cat.id c ⊑ A R ≫ (A R)° := by
      have hd := hAmap.1; dsimp [Entire, dom] at hd; rw [← hd]; exact inter_lb_right _ _
    have hcomp : (A R ≫ F°) ≫ (A R ≫ F°)° = A R ≫ (A R)° := by
      rw [Allegory.recip_comp, Allegory.recip_recip,
        Cat.assoc (A R) F° (F ≫ (A R)°), ← Cat.assoc F° F (A R)°, hF, Cat.id_comp]
    dsimp [Entire, dom]
    rw [hcomp]
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hAent)
  · -- R̂T ⊑ R : R̂T = A(R)(F°F)∋ = A(R)∋ = R.
    have hTeq : (A R ≫ F°) ≫ (F ≫ ∋ a) = R := by
      rw [Cat.assoc (A R) F° (F ≫ ∋ a), ← Cat.assoc F° F (∋ a), hF, Cat.id_comp,
        A_eps_eq R hboxA]
    rw [hTeq]
    exact le_refl R
  · -- R̂°R ⊑ T : R̂° = F A(R)°, and A(R)°R = A(R)°A(R)∋ ⊑ ∋ (A(R) simple), so ⊑ F∋ = T.
    have hRhat_recip : (A R ≫ F°)° = F ≫ (A R)° := by
      rw [Allegory.recip_comp, Allegory.recip_recip]
    rw [hRhat_recip]
    have hinner : (A R)° ≫ R ⊑ ∋ a := by
      have e1 : (A R)° ≫ R = ((A R)° ≫ A R) ≫ ∋ a := by
        rw [Cat.assoc, A_eps_eq R hboxA]
      rw [e1]
      have h2 := comp_mono_right (A_simple R) (∋ a)
      rwa [Cat.id_comp] at h2
    rw [Cat.assoc F (A R)° R]
    exact comp_mono_left F hinner

/-- §2.435 (Cantor, full): in a STRONGLY CONNECTED power allegory, no `F : a → [a]`
    with `F°F = 1` can exist unless the allegory is degenerate.  Concretely, such
    an `F` (via `T = F∋` thick, §2.436 collapse + connectivity) forces every object
    to be a terminator — provided Freyd's diagonal box guard for `T = F∋` holds.

    The box guard `codBox (diag (F∋)) = codBox (F∋)` is §2.436's load-bearing
    side-condition (S2_43 `one_object_pre_power_inconsistent`; it can fail for the
    box-guarded `Thick`, which is why it is an explicit hypothesis here). -/
theorem cantor_degenerate (hSC : StronglyConnectedAllegory 𝒜) {a : 𝒜}
    (F : a ⟶ PowerAllegory.powerObj a)
    (hF : F° ≫ F = Cat.id (PowerAllegory.powerObj a))
    (hBox : codBox (diag (F ≫ ∋ a)) = codBox (F ≫ ∋ a)) :
    ∀ (β : 𝒜), Cat.id β = (𝟘 : β ⟶ β) :=
  thick_endo_degenerate hSC (F ≫ ∋ a) (cantor_thick_endo F hF) hBox

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ## §2.353  Cancellation on maps

  Freyd: "In a tabular division allegory it suffices to verify the cancellation
  property on maps."  S2_3's `straight_of_cancel` needs the cancellation property
  `FS = GS → (dom F)G = (dom G)F` for all SIMPLE F, G (plus the §2.225 union
  hypothesis).  When `S/ₛS` is tabular we can drop both: tabulate `S/ₛS = ℓ°r`
  (ℓ, r maps), show `ℓS = rS`, and the maps-only cancellation `fS = gS → f = g`
  gives `ℓ = r`, whence `S/ₛS = ℓ°ℓ ⊑ 1`.

  Stated with an explicit `Tabular (S/ₛS)` hypothesis (rather than a
  `[TabularAllegory 𝒜]` instance) to keep `≫`/`°`/`∩` referring to the single
  `Allegory` underlying `DivisionAllegory` — no instance diamond.  In a full
  tabular division allegory `hTab` is `TabularAllegory.tabular (S/ₛS)`. -/

/-- §2.353 (cancellation on maps): if `S/ₛS` is tabular and the cancellation
    property holds for MAPS (`fS = gS → f = g`), then `S` is straight. -/
theorem straight_of_cancel_on_maps {a b : 𝒜} {S : a ⟶ b}
    (hTab : Tabular (S /ₛ S))
    (hmap : ∀ {d : 𝒜} (f g : d ⟶ a), Map f → Map g → f ≫ S = g ≫ S → f = g) :
    Straight S := by
  obtain ⟨c, ℓ, r, hℓmap, hrmap, hW, _hjoint⟩ := hTab
  -- counit of symmetric division: (S/ₛS) S ⊑ S.
  have hssS : (S /ₛ S) ≫ S ⊑ S := ((le_symmDiv_iff (S /ₛ S) S S).mp (le_refl _)).1
  -- ℓ, r entire (maps).
  have hℓent : Cat.id c ⊑ ℓ ≫ ℓ° := by
    have hd := hℓmap.1; dsimp [Entire, dom] at hd; rw [← hd]; exact inter_lb_right _ _
  have hrent : Cat.id c ⊑ r ≫ r° := by
    have hd := hrmap.1; dsimp [Entire, dom] at hd; rw [← hd]; exact inter_lb_right _ _
  -- ℓ°(rS) ⊑ S  (= (S/ₛS)S ⊑ S after the tabulation).
  have hℓrS : ℓ° ≫ r ≫ S ⊑ S := by
    have h := hssS; rw [hW, Cat.assoc] at h; exact h
  -- (S/ₛS)° = r°ℓ, and (S/ₛS)° ⊑ S/ₛS, so r°(ℓS) ⊑ (S/ₛS)S ⊑ S.
  have hrℓS : r° ≫ ℓ ≫ S ⊑ S := by
    have hWrec : (S /ₛ S)° = r° ≫ ℓ := by rw [hW, Allegory.recip_comp, Allegory.recip_recip]
    have h : (S /ₛ S)° ≫ S ⊑ S := le_trans (comp_mono_right (symmDiv_self_symmetric S) S) hssS
    rw [hWrec, Cat.assoc] at h; exact h
  -- rS ⊑ ℓS and ℓS ⊑ rS via entireness, hence ℓS = rS.
  have hrℓ : r ≫ S ⊑ ℓ ≫ S := by
    have h1 : r ≫ S ⊑ (ℓ ≫ ℓ°) ≫ (r ≫ S) := by
      have h := comp_mono_right hℓent (r ≫ S); rwa [Cat.id_comp] at h
    have h2 : (ℓ ≫ ℓ°) ≫ (r ≫ S) ⊑ ℓ ≫ S := by
      rw [Cat.assoc]; exact comp_mono_left ℓ hℓrS
    exact le_trans h1 h2
  have hℓr : ℓ ≫ S ⊑ r ≫ S := by
    have h1 : ℓ ≫ S ⊑ (r ≫ r°) ≫ (ℓ ≫ S) := by
      have h := comp_mono_right hrent (ℓ ≫ S); rwa [Cat.id_comp] at h
    have h2 : (r ≫ r°) ≫ (ℓ ≫ S) ⊑ r ≫ S := by
      rw [Cat.assoc]; exact comp_mono_left r hrℓS
    exact le_trans h1 h2
  -- maps-only cancellation: ℓ = r.
  have hℓr_eq : ℓ = r := hmap ℓ r hℓmap hrmap (le_antisymm hℓr hrℓ)
  -- S/ₛS = ℓ°r = ℓ°ℓ ⊑ 1 (ℓ simple).
  dsimp [Straight]
  rw [hW, ← hℓr_eq]
  exact hℓmap.2

end Freyd.Alg
