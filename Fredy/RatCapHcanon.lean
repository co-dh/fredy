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

/-- **A colimit composite equal to the identity becomes a stage identity.**  If the inclusions of
    germs `f` (at `a`) and `g` (at `b`) compose to `idL ⟨ip,xp⟩`, then at a common stage `N` the
    pushed composite `pushHom f ≫ pushHom g` is the stage identity.  Lax `homCompRaw_eq_id_stage`. -/
theorem homCompRawL_eq_id_stage {ip iq : ι} (xp : L.A ip) (xq : L.A iq)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ip) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xp)
    (h : homCompRawL L hL xp xq xp a f b g
        = homInclL L hL xp xp ⟨ip, D.refl ip, D.refl ip⟩ (Cat.id (L.F (D.refl ip) xp))) :
    ∃ (N : ι) (haN : D.le a.1 N) (hbN : D.le b.1 N),
      pushHom L xp xq a.2.1 a.2.2 haN f ≫ pushHom L xq xp b.2.1 b.2.2 hbN g
        = Cat.id (L.F (D.trans a.2.1 haN) xp) := by
  obtain ⟨M, hfM, hgM⟩ := D.bound a.1 b.1
  rw [homCompRawL_eq_compAtL L hL xp xq xp a f b g M hfM hgM] at h
  unfold compAtL at h
  obtain ⟨N, h1, h2, heq⟩ := Quotient.exact h
  dsimp only [homSystemL] at heq
  -- LHS: expand `pushHom (push f ≫ push g)` at bound `h1` into `pushHom f ≫ pushHom g` to `N.1`.
  rw [pushHom_comp L xp xq xp (D.trans a.2.1 hfM) (D.trans a.2.2 hfM) (D.trans b.2.2 hgM) h1
        (pushHom L xp xq a.2.1 a.2.2 hfM f) (pushHom L xq xp b.2.1 b.2.2 hgM g),
      ← hL.push_trans xp xq a.2.1 a.2.2 hfM h1 f, ← hL.push_trans xq xp b.2.1 b.2.2 hgM h1 g,
      pushHom_id L xp (D.refl ip) h2] at heq
  exact ⟨N.1, D.trans hfM h1, D.trans hgM h1, heq⟩

/-- **Iso reflection through the stage inclusion.**  If `homInclL a g` is iso in the colimit, then
    at some higher stage `L'` the transition `map g` is iso.  Lax `colimHom_isIso_reflects`. -/
theorem homInclL_isIso_reflects
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    (g : L.F a.2.1 x ⟶ L.F a.2.2 y)
    (hiso : @IsIso (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨j, y⟩ (homInclL L hL x y a g)) :
    ∃ (e : ι) (hae : D.le a.1 e),
      IsIso (pushHom L x y a.2.1 a.2.2 hae g) := by
  letI : Cat (Obj L) := laxColimCat L hL
  obtain ⟨ginv, hl, hr⟩ := hiso
  revert hl hr
  refine Quotient.inductionOn ginv (fun rep => ?_)
  obtain ⟨b, g'⟩ := rep
  intro hl hr
  -- `homInclL a g ⊚ (germ g' at b) = id` etc. are `homCompRawL = idL`
  have hl' : homCompRawL L hL x y x a g b g'
      = homInclL L hL x x ⟨i, D.refl i, D.refl i⟩ (Cat.id (L.F (D.refl i) x)) := hl
  have hr' : homCompRawL L hL y x y b g' a g
      = homInclL L hL y y ⟨j, D.refl j, D.refl j⟩ (Cat.id (L.F (D.refl j) y)) := hr
  obtain ⟨N1, haN1, hbN1, eq1⟩ := homCompRawL_eq_id_stage L hL x y a g b g' hl'
  obtain ⟨N2, hbN2, haN2, eq2⟩ := homCompRawL_eq_id_stage L hL y x b g' a g hr'
  obtain ⟨e, hN1e, hN2e⟩ := D.bound N1 N2
  have hae : D.le a.1 e := D.trans haN1 hN1e
  have hbe : D.le b.1 e := D.trans hbN1 hN1e
  -- push both stage identities to `e` (push_trans on a composite).
  have eq1e : pushHom L x y a.2.1 a.2.2 hae g ≫ pushHom L y x b.2.1 b.2.2 hbe g'
      = Cat.id (L.F (D.trans a.2.1 hae) x) := by
    have t := congrArg (pushHom L x x _ _ hN1e) eq1
    rw [pushHom_comp L x y x (D.trans a.2.1 haN1) (D.trans a.2.2 haN1) (D.trans b.2.2 hbN1) hN1e,
        ← hL.push_trans x y a.2.1 a.2.2 haN1 hN1e g,
        ← hL.push_trans y x b.2.1 b.2.2 hbN1 hN1e g',
        pushHom_id L x (D.trans a.2.1 haN1) hN1e] at t
    exact t
  have eq2e : pushHom L y x b.2.1 b.2.2 hbe g' ≫ pushHom L x y a.2.1 a.2.2 hae g
      = Cat.id (L.F (D.trans b.2.1 hbe) y) := by
    have t := congrArg (pushHom L y y _ _ hN2e) eq2
    rw [pushHom_comp L y x y (D.trans b.2.1 hbN2) (D.trans b.2.2 hbN2) (D.trans a.2.2 haN2) hN2e,
        ← hL.push_trans y x b.2.1 b.2.2 hbN2 hN2e g',
        ← hL.push_trans x y a.2.1 a.2.2 haN2 hN2e g,
        pushHom_id L y (D.trans b.2.1 hbN2) hN2e] at t
    -- `t` and the goal differ only in `D.le` proofs (proof-irrelevant).
    exact t
  exact ⟨e, hae, pushHom L y x b.2.1 b.2.2 hbe g', eq1e, eq2e⟩

end Freyd.LaxColim
