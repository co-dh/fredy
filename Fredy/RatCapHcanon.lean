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

/-- **A cover post-composed with an iso is a cover** (bare-`Cat` version; the `PreLogos`
    `cover_comp_iso` is unavailable here).  A mono `m` with `h ≫ m = f ≫ g` gives `m ≫ g⁻¹` mono with
    `h ≫ (m ≫ g⁻¹) = f`, so `f`'s cover forces `m ≫ g⁻¹` iso, hence `m` iso. -/
theorem cover_comp_iso' {𝒜 : Type w} [Cat.{w} 𝒜] {X Y Z : 𝒜} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Cover f) (hg : IsIso g) : Cover (f ≫ g) := by
  obtain ⟨gi, hg1, hg2⟩ := hg
  intro C m h hm hcm
  -- `m ≫ gi` is mono and factors `f` (via `h`).
  have hmgi_mono : Mono (m ≫ gi) := by
    intro W u v huv
    apply hm u v
    -- u ≫ m = v ≫ m from u ≫ (m ≫ gi) = v ≫ (m ≫ gi) by post-composing `g`.
    have := congrArg (fun t => t ≫ g) huv
    simp only [Cat.assoc, hg2, Cat.comp_id] at this
    exact this
  have hf_iso : IsIso (m ≫ gi) := hf (m ≫ gi) h hmgi_mono (by
    rw [← Cat.assoc, hcm, Cat.assoc, hg1, Cat.comp_id])
  -- `m = (m ≫ gi) ≫ g`, a composite of isos.
  obtain ⟨w, hw1, hw2⟩ := hf_iso
  -- `w ≫ m = g` (post-compose `hw2 : w ≫ (m ≫ gi) = id` with `g`).
  have hwm : w ≫ m = g := by
    have := congrArg (fun t => t ≫ g) hw2
    simp only [Cat.assoc, hg2, Cat.comp_id, Cat.id_comp] at this
    exact this
  refine ⟨gi ≫ w, ?_, ?_⟩
  · rw [← Cat.assoc m gi w, hw1]
  · rw [Cat.assoc, hwm, hg2]

/-- **Iso un-conjugation.**  If `i`, `j` are isos and `i ≫ f ≫ j` is an iso, then `f` is an iso
    (`f = i⁻¹ ≫ (i ≫ f ≫ j) ≫ j⁻¹`, a composite of isos).  Used to strip the coherence isos that
    flank `Functor.map` inside `pushHom`. -/
theorem isIso_unconj {𝒜 : Type w} [Cat.{w} 𝒜] {W X Y Z : 𝒜}
    {i : W ⟶ X} {f : X ⟶ Y} {j : Y ⟶ Z}
    (hi : IsIso i) (hj : IsIso j) (h : IsIso (i ≫ f ≫ j)) : IsIso f := by
  obtain ⟨ii, hi1, hi2⟩ := hi
  obtain ⟨jj, hj1, hj2⟩ := hj
  obtain ⟨w, hw1, hw2⟩ := h
  -- inverse of `f` is `j ≫ w ≫ i`.
  refine ⟨j ≫ w ≫ i, ?_, ?_⟩
  · calc f ≫ j ≫ w ≫ i = (ii ≫ i) ≫ f ≫ j ≫ w ≫ i := by rw [hi2, Cat.id_comp]
      _ = ii ≫ (i ≫ f ≫ j) ≫ w ≫ i := by simp only [Cat.assoc]
      _ = ii ≫ Cat.id W ≫ i := by rw [← Cat.assoc (i ≫ f ≫ j), hw1]
      _ = Cat.id X := by rw [Cat.id_comp, hi2]
  · calc (j ≫ w ≫ i) ≫ f = j ≫ (w ≫ i ≫ f ≫ j) ≫ jj := by
            simp only [Cat.assoc]; rw [hj1, Cat.comp_id]
      _ = j ≫ Cat.id Z ≫ jj := by rw [hw2]
      _ = Cat.id Y := by rw [Cat.id_comp, hj1]

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

/-- **Stage equation from a colimit composite equality.**  If `homInclL a f ⊚ homInclL b g`
    (= `homCompRawL a f b g`) equals `homInclL c hh`, then at a common stage `N` the pushed germs
    compose to the pushed `hh`.  Lax `homCompRaw_eq_stage`. -/
theorem homCompRawL_eq_stage {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr)
    (c : UpperBound D ip ir) (hh : L.F c.2.1 xp ⟶ L.F c.2.2 xr)
    (h : homCompRawL L hL xp xq xr a f b g = homInclL L hL xp xr c hh) :
    ∃ (N : ι) (haN : D.le a.1 N) (hbN : D.le b.1 N) (hcN : D.le c.1 N),
      pushHom L xp xq a.2.1 a.2.2 haN f ≫ pushHom L xq xr b.2.1 b.2.2 hbN g
        = pushHom L xp xr c.2.1 c.2.2 hcN hh := by
  obtain ⟨M, hfM, hgM⟩ := D.bound a.1 b.1
  rw [homCompRawL_eq_compAtL L hL xp xq xr a f b g M hfM hgM] at h
  unfold compAtL at h
  obtain ⟨N, h1, h2, heq⟩ := Quotient.exact h
  dsimp only [homSystemL] at heq
  rw [pushHom_comp L xp xq xr (D.trans a.2.1 hfM) (D.trans a.2.2 hfM) (D.trans b.2.2 hgM) h1
        (pushHom L xp xq a.2.1 a.2.2 hfM f) (pushHom L xq xr b.2.1 b.2.2 hgM g),
      ← hL.push_trans xp xq a.2.1 a.2.2 hfM h1 f, ← hL.push_trans xq xr b.2.1 b.2.2 hgM h1 g] at heq
  exact ⟨N.1, D.trans hfM h1, D.trans hgM h1, h2, heq⟩

/-- **A colimit composite equal to the identity becomes a stage identity.**  The `homInclL … id`
    special case of `homCompRawL_eq_stage`, finished by `pushHom_id`.  Lax `homCompRaw_eq_id_stage`. -/
theorem homCompRawL_eq_id_stage {ip iq : ι} (xp : L.A ip) (xq : L.A iq)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ip) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xp)
    (h : homCompRawL L hL xp xq xp a f b g
        = homInclL L hL xp xp ⟨ip, D.refl ip, D.refl ip⟩ (Cat.id (L.F (D.refl ip) xp))) :
    ∃ (N : ι) (haN : D.le a.1 N) (hbN : D.le b.1 N),
      pushHom L xp xq a.2.1 a.2.2 haN f ≫ pushHom L xq xp b.2.1 b.2.2 hbN g
        = Cat.id (L.F (D.trans a.2.1 haN) xp) := by
  obtain ⟨N, haN, hbN, hcN, key⟩ := homCompRawL_eq_stage L hL xp xq xp a f b g
    ⟨ip, D.refl ip, D.refl ip⟩ (Cat.id (L.F (D.refl ip) xp)) h
  rw [pushHom_id L xp (D.refl ip) hcN] at key
  exact ⟨N, haN, hbN, key⟩

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

/-- **Mono preservation through the stage inclusion.**  If a germ `g` is left-cancellable under
    EVERY transition from `a.1` (`hcancel`), then `homInclL a g` is monic in the colimit.  Reduce a
    colimit cancellation `u ⊚ (homInclL a g) = v ⊚ (homInclL a g)` to a stage equation of pushed
    competitors (`homCompRawL` + `Quotient.exact`), cancel by `hcancel`, repackage as a germ relation.
    Lax `colimHom_mono_of_rep`/`homInclObj_mono_of_stage`. -/
theorem homInclL_mono_of_stage
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    (g : L.F a.2.1 x ⟶ L.F a.2.2 y)
    (hcancel : ∀ {e : ι} (hae : D.le a.1 e) (z : L.A e)
        (u v : z ⟶ L.F (D.trans a.2.1 hae) x),
        u ≫ pushHom L x y a.2.1 a.2.2 hae g = v ≫ pushHom L x y a.2.1 a.2.2 hae g → u = v) :
    @Mono (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨j, y⟩ (homInclL L hL x y a g) := by
  letI : Cat (Obj L) := laxColimCat L hL
  intro W
  refine Quotient.ind₂ (fun pr qr hpq => ?_)
  obtain ⟨ap, p₀⟩ := pr
  obtain ⟨aq, q₀⟩ := qr
  -- common bound `P` of `ap.1, aq.1, a.1`
  obtain ⟨P0, hP0p, hP0q⟩ := D.bound ap.1 aq.1
  obtain ⟨P, hP0P, haP⟩ := D.bound P0 a.1
  have hapP : D.le ap.1 P := D.trans hP0p hP0P
  have haqP : D.le aq.1 P := D.trans hP0q hP0P
  -- both composites are `homInclL` of the pushed composite at bound `P`.
  change homCompRawL L hL W.2 x y ap p₀ a g = homCompRawL L hL W.2 x y aq q₀ a g at hpq
  rw [homCompRawL_eq_compAtL L hL W.2 x y ap p₀ a g P hapP haP,
      homCompRawL_eq_compAtL L hL W.2 x y aq q₀ a g P haqP haP] at hpq
  unfold compAtL at hpq
  obtain ⟨R, hPR, hPR', heq⟩ := Quotient.exact hpq
  dsimp only [homSystemL] at heq
  rw [Subsingleton.elim hPR' hPR] at heq
  -- split off the common `pushHom g` factor (pushed once more from `P` to `R.1`).
  rw [pushHom_comp L W.2 x y (D.trans ap.2.1 hapP) (D.trans ap.2.2 hapP) (D.trans a.2.2 haP) hPR
        (pushHom L W.2 x ap.2.1 ap.2.2 hapP p₀) (pushHom L x y a.2.1 a.2.2 haP g),
      pushHom_comp L W.2 x y (D.trans aq.2.1 haqP) (D.trans aq.2.2 haqP) (D.trans a.2.2 haP) hPR
        (pushHom L W.2 x aq.2.1 aq.2.2 haqP q₀) (pushHom L x y a.2.1 a.2.2 haP g),
      ← hL.push_trans x y a.2.1 a.2.2 haP hPR g,
      ← hL.push_trans W.2 x ap.2.1 ap.2.2 hapP hPR p₀,
      ← hL.push_trans W.2 x aq.2.1 aq.2.2 haqP hPR q₀] at heq
  -- cancel that common right factor by `hcancel` at `e := R.1`.
  have hu := hcancel (D.trans haP hPR) (L.F (D.trans (D.trans ap.2.1 hapP) hPR) W.2)
    (pushHom L W.2 x ap.2.1 ap.2.2 (D.trans hapP hPR) p₀)
    (pushHom L W.2 x aq.2.1 aq.2.2 (D.trans haqP hPR) q₀)
    heq
  -- repackage `hu` as a germ relation at bound `R.1`.
  refine Quotient.sound ⟨⟨R.1, D.trans (D.trans ap.2.1 hapP) hPR, D.trans (D.trans ap.2.2 hapP) hPR⟩,
    D.trans hapP hPR, D.trans haqP hPR, ?_⟩
  dsimp only [homSystemL]
  -- the goal's `.tr` reduces to the collapsed-bound pushes, matching `hu` directly.
  exact hu

/-- **Mono reflection through the stage inclusion.**  If `homInclL a g` is monic in the colimit and
    transitions are faithful, then the germ `g` is left-cancellable under every transition.  Include
    the two stage competitors `u, v` as colimit germs `⟨e,z⟩ ⟶ ⟨i,x⟩` and compose with `homInclL a g`;
    the colimit mono forces the inclusions equal, and `homInclL_injective`/`pushHom_injective` strip
    back.  Lax `colimHom_mono_reflects`. -/
theorem homInclL_mono_reflects
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        @Functor.map _ _ _ _ _ (L.functF hij) x y p
          = @Functor.map _ _ _ _ _ (L.functF hij) x y q → p = q)
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    (g : L.F a.2.1 x ⟶ L.F a.2.2 y)
    (hmono : @Mono (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨j, y⟩ (homInclL L hL x y a g))
    {e : ι} (hae : D.le a.1 e) (z : L.A e)
    (u v : z ⟶ L.F (D.trans a.2.1 hae) x)
    (huv : u ≫ pushHom L x y a.2.1 a.2.2 hae g = v ≫ pushHom L x y a.2.1 a.2.2 hae g) : u = v := by
  letI : Cat (Obj L) := laxColimCat L hL
  -- include `reflApp z ≫ u`, `reflApp z ≫ v` as germs `⟨e,z⟩ ⟶ ⟨i,x⟩` at bound `⟨e, refl e, i≤e⟩`.
  let bnd : UpperBound D e i := ⟨e, D.refl e, D.trans a.2.1 hae⟩
  let U : @homL _ _ L hL ⟨e, z⟩ ⟨i, x⟩ := homInclL L hL z x bnd (reflApp L z ≫ u)
  let V : @homL _ _ L hL ⟨e, z⟩ ⟨i, x⟩ := homInclL L hL z x bnd (reflApp L z ≫ v)
  have hUV : @compL _ _ L hL ⟨e, z⟩ ⟨i, x⟩ ⟨j, y⟩ U (homInclL L hL x y a g)
      = @compL _ _ L hL ⟨e, z⟩ ⟨i, x⟩ ⟨j, y⟩ V (homInclL L hL x y a g) := by
    rw [compL_homInclL_compAtL L hL z x y bnd _ a g e (D.refl e) hae,
        compL_homInclL_compAtL L hL z x y bnd _ a g e (D.refl e) hae]
    -- the left push at refl is identity (push_refl): both sides `homInclL ((reflApp z ≫ u|v) ≫ pushHom g)`.
    rw [hL.push_refl z x (D.refl e) (D.trans a.2.1 hae) (reflApp L z ≫ u),
        hL.push_refl z x (D.refl e) (D.trans a.2.1 hae) (reflApp L z ≫ v),
        Cat.assoc, Cat.assoc, huv]
  have hUVeq : U = V := hmono U V hUV
  -- strip the inclusion (faithful), then cancel the iso `reflApp z` (mono).
  have hstrip := homInclL_injective L hL hfaith z x bnd hUVeq
  -- `reflApp z ≫ u = reflApp z ≫ v` with `reflApp z` iso ⇒ `u = v`.
  have hiso := reflApp_isIso L z
  obtain ⟨rinv, hr1, hr2⟩ := hiso
  have := congrArg (fun t => rinv ≫ t) hstrip
  simpa only [← Cat.assoc, hr2, Cat.id_comp] using this

/-- **Cover of a germ that is a cover at every stage.**  If `pushHom g` is a cover for every
    transition from `a.1`, then `homInclL a g` is a cover in the colimit.  Given a colimit mono `m`
    and factor `homInclL a g = g' ⊚ m`, reflect the factorization to a stage `N`
    (`homCompRawL_eq_stage`); the stage `pushHom m` is mono (mono reflection) and factors the stage
    cover `pushHom g`, so it is a stage iso; lift to the colimit (`homInclL_isIso_of_rep`) and absorb
    the level shift (`homInclL_compat`).  Lax `colimHom_cover_of_rep`. -/
theorem homInclL_cover_of_rep
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        @Functor.map _ _ _ _ _ (L.functF hij) x y p
          = @Functor.map _ _ _ _ _ (L.functF hij) x y q → p = q)
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    (g : L.F a.2.1 x ⟶ L.F a.2.2 y)
    (hcov : ∀ (e : ι) (hae : D.le a.1 e), Cover (pushHom L x y a.2.1 a.2.2 hae g)) :
    @Cover (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨j, y⟩ (homInclL L hL x y a g) := by
  letI : Cat (Obj L) := laxColimCat L hL
  intro Cobj m g' hm hg'm
  -- `m : Cobj ⟶ ⟨j,y⟩`, `g' : ⟨i,x⟩ ⟶ Cobj`, both germs.
  revert hm hg'm
  refine Quotient.inductionOn₂ m g' (fun mrep grep => ?_)
  obtain ⟨bm, m₀⟩ := mrep
  obtain ⟨bg, g₀⟩ := grep
  obtain ⟨ck, cx⟩ := Cobj
  intro hm hg'm
  -- factorization `g₀ ⊚ m₀ = homInclL a g` ⇒ stage equation at `N`.
  have hg'm' : homCompRawL L hL x cx y bg g₀ bm m₀ = homInclL L hL x y a g := hg'm
  obtain ⟨N, hgN, hmN, hfN, eqN⟩ := homCompRawL_eq_stage L hL x cx y bg g₀ bm m₀ a g hg'm'
  -- `pushHom m₀` is mono at `N` (mono reflection of the colimit mono `m`).
  have hm_mono : Mono (pushHom L cx y bm.2.1 bm.2.2 hmN m₀) := by
    intro Z' u v huv
    exact homInclL_mono_reflects L hL hfaith cx y bm m₀ hm hmN Z' u v huv
  -- `pushHom g` is a cover at `N`; `pushHom m₀` factors it ⇒ `pushHom m₀` iso.
  have hcov_N : Cover (pushHom L x y a.2.1 a.2.2 hfN g) := hcov N hfN
  have hiso_mN : IsIso (pushHom L cx y bm.2.1 bm.2.2 hmN m₀) :=
    hcov_N _ _ hm_mono eqN
  obtain ⟨nN, hn1, hn2⟩ := hiso_mN
  -- lift the stage iso to the colimit; `homInclL_compat` absorbs the level shift `bm → N`.
  have hlift := homInclL_isIso_of_rep L hL cx y ⟨N, D.trans bm.2.1 hmN, D.trans bm.2.2 hmN⟩
    (pushHom L cx y bm.2.1 bm.2.2 hmN m₀) nN hn1 hn2
  rwa [homInclL_compat L hL cx y (a := bm)
    (b := ⟨N, D.trans bm.2.1 hmN, D.trans bm.2.2 hmN⟩) hmN m₀] at hlift

/-- **Cover preservation through the stage inclusion.**  If `g` is a cover stable under every
    transition from `a.1` (each `(functF hij).map g` a cover), then `homInclL a g` is a colimit
    cover.  Feed `homInclL_cover_of_rep` the pushed covers: `pushHom = transApp ≫ map · ≫ isoInv`, and
    pre/post-composing a cover with isos keeps it a cover.  Lax `homInclObj_cover_of_stage`. -/
theorem homInclL_cover_of_stage
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        @Functor.map _ _ _ _ _ (L.functF hij) x y p
          = @Functor.map _ _ _ _ _ (L.functF hij) x y q → p = q)
    {i : ι} (x y : L.A i) (g : x ⟶ y)
    (hcov : ∀ {e : ι} (hie : D.le i e), Cover (@Functor.map _ _ _ _ _ (L.functF hie) x y g)) :
    @Cover (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨i, y⟩
      (homInclL L hL x y ⟨i, D.refl i, D.refl i⟩ (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y))) := by
  -- the germ `gᵣ := reflApp x ≫ g ≫ (reflApp y)⁻¹` at the reflexive bound `⟨i, refl i, refl i⟩`.
  apply homInclL_cover_of_rep L hL hfaith x y ⟨i, D.refl i, D.refl i⟩
  intro e hie
  -- `pushHom gᵣ` (along `refl i ≤ e`) is a cover: it is `(functF hie').map g` flanked by isos.
  -- `pushHom x y (refl i)(refl i) hie gᵣ = transApp ≫ map gᵣ ≫ isoInv transApp`; and
  -- `map gᵣ = map (reflApp x) ≫ map g ≫ map (reflApp y)⁻¹`, all but `map g` being isos.
  unfold pushHom
  -- the middle `map gᵣ` factors through `map g` flanked by isos (functor preserves iso & comp).
  rw [@Functor.map_comp _ _ _ _ _ (L.functF hie) _ _ _ (reflApp L x) (g ≫ isoInv (reflApp_isIso L y)),
      @Functor.map_comp _ _ _ _ _ (L.functF hie) _ _ _ g (isoInv (reflApp_isIso L y))]
  -- assemble: cover flanked by four isos (transApp, map reflApp x, map (reflApp y)⁻¹, isoInv transApp).
  have hi1 : IsIso (transApp L (D.refl i) hie x) := transApp_isIso L (D.refl i) hie x
  have hi2 : IsIso (@Functor.map _ _ _ _ _ (L.functF hie) _ _ (reflApp L x)) :=
    @functor_preserves_iso _ _ _ _ _ (L.functF hie) _ _ (reflApp L x) (reflApp_isIso L x)
  have hi3 : IsIso (@Functor.map _ _ _ _ _ (L.functF hie) _ _ (isoInv (reflApp_isIso L y))) :=
    @functor_preserves_iso _ _ _ _ _ (L.functF hie) _ _ (isoInv (reflApp_isIso L y))
      ⟨reflApp L y, inv_isoInv_comp _, isoInv_comp _⟩
  have hi4 : IsIso (isoInv (transApp_isIso L (D.refl i) hie y)) :=
    ⟨transApp L (D.refl i) hie y, inv_isoInv_comp _, isoInv_comp _⟩
  -- cover (map g) ⇒ cover of the whole flanked composite (iso pre/post composition).
  have hg_cov : Cover (@Functor.map _ _ _ _ _ (L.functF hie) x y g) := hcov hie
  -- peel the flanking isos: transApp (pre), isoInv transApp (post), map reflApp x (pre), map isoInv (post).
  have c1 : Cover (@Functor.map _ _ _ _ _ (L.functF hie) x y g
      ≫ @Functor.map _ _ _ _ _ (L.functF hie) _ _ (isoInv (reflApp_isIso L y))) :=
    cover_comp_iso' hg_cov hi3
  have c2 : Cover (@Functor.map _ _ _ _ _ (L.functF hie) _ _ (reflApp L x)
      ≫ @Functor.map _ _ _ _ _ (L.functF hie) x y g
      ≫ @Functor.map _ _ _ _ _ (L.functF hie) _ _ (isoInv (reflApp_isIso L y))) :=
    cover_precomp_iso hi2 c1
  have c3 : Cover ((@Functor.map _ _ _ _ _ (L.functF hie) _ _ (reflApp L x)
      ≫ @Functor.map _ _ _ _ _ (L.functF hie) x y g
      ≫ @Functor.map _ _ _ _ _ (L.functF hie) _ _ (isoInv (reflApp_isIso L y)))
      ≫ isoInv (transApp_isIso L (D.refl i) hie y)) :=
    cover_comp_iso' c2 hi4
  exact @cover_precomp_iso _ _ _ _ _ _ hi1 _ c3

/-- **Iso reflection (clean form).**  If `homInclL a g` is iso and transitions are conservative,
    then `g` is iso.  `homInclL_isIso_reflects` gives a stage `e` with `pushHom g` iso; `pushHom` is
    `map g` flanked by isos, so `map g` is iso, and `hcons` reflects to `g`.  Lax
    `homInclObj_isIso_reflects`. -/
theorem homInclL_isIso_reflects'
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (φ : x ⟶ y),
        IsIso (@Functor.map _ _ _ _ _ (L.functF hij) x y φ) → IsIso φ)
    {i : ι} (x y : L.A i) (g : x ⟶ y)
    (hiso : @IsIso (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨i, y⟩
      (homInclL L hL x y ⟨i, D.refl i, D.refl i⟩ (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y)))) :
    IsIso g := by
  obtain ⟨e, hae, hpiso⟩ := homInclL_isIso_reflects L hL x y ⟨i, D.refl i, D.refl i⟩
    (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y)) hiso
  apply hcons hae
  -- `pushHom gᵣ = transApp ≫ (map gᵣ) ≫ isoInv transApp`; un-conjugate by the two isos.
  have hi1 : IsIso (transApp L (D.refl i) hae x) := transApp_isIso L (D.refl i) hae x
  have hi1' : IsIso (isoInv (transApp_isIso L (D.refl i) hae y)) :=
    ⟨transApp L (D.refl i) hae y, inv_isoInv_comp _, isoInv_comp _⟩
  have hmapr : IsIso (@Functor.map _ _ _ _ _ (L.functF hae) _ _
      (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y))) := by
    have := hpiso; unfold pushHom at this
    exact isIso_unconj hi1 hi1' this
  -- `map gᵣ = (map reflApp x) ≫ (map g) ≫ (map isoInv)`; un-conjugate again.
  rw [@Functor.map_comp _ _ _ _ _ (L.functF hae) _ _ _ (reflApp L x) (g ≫ isoInv (reflApp_isIso L y)),
      @Functor.map_comp _ _ _ _ _ (L.functF hae) _ _ _ g (isoInv (reflApp_isIso L y))] at hmapr
  have hi2 : IsIso (@Functor.map _ _ _ _ _ (L.functF hae) _ _ (reflApp L x)) :=
    @functor_preserves_iso _ _ _ _ _ (L.functF hae) _ _ (reflApp L x) (reflApp_isIso L x)
  have hi3 : IsIso (@Functor.map _ _ _ _ _ (L.functF hae) _ _ (isoInv (reflApp_isIso L y))) :=
    @functor_preserves_iso _ _ _ _ _ (L.functF hae) _ _ (isoInv (reflApp_isIso L y))
      ⟨reflApp L y, inv_isoInv_comp _, isoInv_comp _⟩
  exact isIso_unconj hi2 hi3 hmapr

end Freyd.LaxColim
