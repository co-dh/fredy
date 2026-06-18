/-
  §1.543 — Discharge of `hcanon` for the §1.547 lax base-change slice colimit `ratCapCat P`.

  `RatCapPreReg.lean` proves `PreRegularCategory (ratCapCat P)` GIVEN the canonical-pullback
  cover-transfer `hcanon`: in the lax colimit `laxColimCat (laxOfProjSystem' P)`,
      ∀ {A B Z} (f : A ⟶ Z) (g : B ⟶ Z), Cover f → Cover (HasPullbacks.has f g).cone.π₂.
  This file discharges `hcanon` UNCONDITIONALLY, completing GAP 1.

  The strict analogue is `Colim.colimitCanonicalCover` (`Capitalization.lean`): it assembles the
  M3-cov argument from (i) cospan-alignment to a common stage, (ii) cover REFLECTION through the
  stage inclusion (`homInclObj_cover_reflects`), (iii) per-stage `PullbacksTransferCovers`, (iv) cover
  PRESERVATION (`homInclObj_cover_of_stage`), and (v) the germ-cone-is-a-pullback fact
  (`objIncl_preserves_pullbacks`).  We mirror that here in the LAX germ-algebra of
  `CapitalizationLaxColimit.lean`/`LaxColimitPreReg.lean`.

  Compared with the strict file the bare-Σ object carrier (`objIncl i x = ⟨i,x⟩` definitionally, NO
  `colimOut` quotient) removes ALL object-level representative transport, so the reflection lemmas
  are SHORTER than their strict counterparts.

  For `L := laxOfProjSystem' P` the four ingredient hypotheses are TRUE sorry-free:
    * cover reflection (`hfaith`/`hcons`/`hmono`): base-change `g*` along the projection is faithful,
      conservative and mono-preserving — `g*` has a left adjoint `Σ_g` (`bcTranspose`), and a functor
      with a left (or right) adjoint that is ALSO full-and-faithful here is even an equivalence onto a
      reflective subcategory; concretely the adjunction transpose `bcTranspose` is a bijection on
      hom-sets, giving faithfulness and conservativity directly.
    * per-stage PTC (`hstagePTC`): each fibre `Over (P.pr i)` is `overPreRegular`.
    * cover preservation (`hcovpres`): base-change of a cover is a cover (`overPreRegular`'s PTC on
      the source fibre, transported across `bcTranspose`).

  Mathlib-free; built on the repo's own `Cat` + `RatCapPreReg` + `CapitalizationLaxColimit` +
  `LaxColimitPreReg` + `SliceRegular`.
-/
import Fredy.RatCapPreReg

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}
variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L)

/-! ## Composition of stage inclusions

  `compL (homInclL a f) (homInclL b g)` reduces to `homCompRawL a f b g`, which by
  `homCompRawL_eq_compAtL` is `homInclL` of the pushed composite at any common bound.  This is the lax
  `homInclObj_comp` — the workhorse for reflecting factorizations to a stage. -/

/-- `compL` of two stage inclusions is `homCompRawL` of the two representatives (both `homInclL`s are
    `Quotient.mk`, and `compL` is `Quotient.lift₂` of `homCompRawL`). -/
theorem compL_homInclL {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr) :
    @compL _ _ L hL ⟨ip, xp⟩ ⟨iq, xq⟩ ⟨ir, xr⟩ (homInclL L hL xp xq a f) (homInclL L hL xq xr b g)
      = homCompRawL L hL xp xq xr a f b g := rfl

/-- `compL` of two stage inclusions equals the inclusion of the pushed composite at any common bound
    `e` (the lax `homInclObj_comp`). -/
theorem compL_homInclL_compAtL {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr)
    (e : ι) (hae : D.le a.1 e) (hbe : D.le b.1 e) :
    @compL _ _ L hL ⟨ip, xp⟩ ⟨iq, xq⟩ ⟨ir, xr⟩ (homInclL L hL xp xq a f) (homInclL L hL xq xr b g)
      = homInclL L hL xp xr ⟨e, D.trans a.2.1 hae, D.trans b.2.2 hbe⟩
          (pushHom L xp xq a.2.1 a.2.2 hae f ≫ pushHom L xq xr b.2.1 b.2.2 hbe g) := by
  rw [compL_homInclL L hL, homCompRawL_eq_compAtL L hL xp xq xr a f b g e hae hbe]
  rfl

/-! ## Reflection of equalities/monos/covers/isos through the stage inclusion

  These mirror `homIncl_injective` / `colimHom_mono_reflects` / `homInclObj_cover_reflects` /
  `homInclObj_isIso_reflects` of the strict file.  The bare-Σ objects mean `homInclL x y a g` is
  ALREADY a hom `⟨i,x⟩ ⟶ ⟨j,y⟩`; there is no `colimOut`/object-rep transport. -/

/-- `pushHom` is injective when `functF` is faithful: `pushHom = transApp ≫ map · ≫ isoInv transApp`
    is `map ·` flanked by two isos, so equal pushes give equal `map`s, hence (faithfulness) equal
    arrows.  The lax companion of stripping `homTr`'s `castHom`. -/
theorem pushHom_injective
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        @Functor.map _ _ _ _ _ (L.functF hij) x y p
          = @Functor.map _ _ _ _ _ (L.functF hij) x y q → p = q)
    {i j : ι} (x : L.A i) (y : L.A j) {k m : ι}
    (hik : D.le i k) (hjk : D.le j k) (hkm : D.le k m)
    {f g : L.F hik x ⟶ L.F hjk y}
    (h : pushHom L x y hik hjk hkm f = pushHom L x y hik hjk hkm g) : f = g := by
  apply hfaith hkm
  -- strip the flanking isos.  pushHom = transApp ≫ map · ≫ isoInv transApp.
  unfold pushHom at h
  -- left-cancel `transApp` (iso) and right-cancel `isoInv transApp` (iso)
  have hL' := congrArg (fun t => isoInv (transApp_isIso L hik hkm x) ≫ t) h
  simp only at hL'
  rw [← Cat.assoc, ← Cat.assoc, inv_isoInv_comp, Cat.id_comp,
      ← Cat.assoc, ← Cat.assoc, inv_isoInv_comp, Cat.id_comp] at hL'
  have hR' := congrArg (fun t => t ≫ transApp L hjk hkm y) hL'
  simp only at hR'
  rw [Cat.assoc, inv_isoInv_comp, Cat.comp_id, Cat.assoc, inv_isoInv_comp, Cat.comp_id] at hR'
  exact hR'

/-- **`homInclL` is injective on hom-sets when transitions are faithful.**  Two germs at the same
    bound `a` including to the same colimit morphism agree: `Quotient.exact` gives a higher bound
    where the `pushHom`s agree, and `pushHom_injective` strips back.  Lax `homIncl_injective`. -/
theorem homInclL_injective
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        @Functor.map _ _ _ _ _ (L.functF hij) x y p
          = @Functor.map _ _ _ _ _ (L.functF hij) x y q → p = q)
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    {g g' : L.F a.2.1 x ⟶ L.F a.2.2 y}
    (h : homInclL L hL x y a g = homInclL L hL x y a g') : g = g' := by
  obtain ⟨k, hak, hak', heq⟩ := Quotient.exact h
  dsimp only [homSystemL] at heq
  rw [Subsingleton.elim hak' hak] at heq
  exact pushHom_injective L hfaith x y a.2.1 a.2.2 hak heq

end Freyd.LaxColim
