/-
  §1.543 (lax) — `objIncl i` PRESERVES BINARY PRODUCTS in the FILTERED lax colimit.

  ════════════════════════════════════════════════════════════════════════════════════════════
  This is the LAX port of `Colim.objIncl_preserves_products` (`CatColimitRegular.lean:1875`).

  Given a `LaxCatSystem L` with `Coherent L` and the lax binary-product preservation bundle
  `LaxProductData L` (per-fibre products + transition joint-monic preservation `pres` + transition
  pairing preservation `presPair`), the canonical comparison

      `pair (stageInclL fst) (stageInclL snd) : ⟨i, a×b⟩ ⟶ ⟨i,a⟩ ×_lax ⟨i,b⟩`

  out of the INCLUDED stage product `objIncl i (a×b) = ⟨i, (hp i).prod a b⟩` is an ISO in
  `laxColimCat L hL`.  (Here `×_lax` is the colimit product `prObj L data a b` at the common bound
  `prK D i i`, built by `laxColimHasBinaryProducts`.)

  PROOF (via the generic `Colim.isIso_of_product_up`).  The cone `(⟨i,a×b⟩, stageInclL fst,
  stageInclL snd)` is itself a universal product cone:

    * UNIQUENESS (joint monicity) — `homInclL_monicPair_of_stage`, the lax mirror of
      `Colim.colimHom_monicPair_of_rep`, built here.  Two competitor germs agreeing after both
      projections are pushed to a common bound where `data.pres` (the fibre's joint-monic
      preservation) forces them equal; the trailing coherence isos (`prUnit`/`transApp`/`reflApp`)
      are stripped by post-composition.  This generic helper is the joint analogue of
      `RatCapHcanon.homInclL_mono_of_stage`.

    * EXISTENCE — push the competitors `f,g` to a common stage `N ≥ i`, post-compose with the unit
      conjugator `prUnit` (the lax analogue of the strict castHom that lands the competitor in
      `F hiN a`), apply `data.presPair` to get the mediator germ `r`, and bake `isoInv (prUnit …)`
      into the included representative so the projection's `prUnit` prefactor cancels.  This mirrors
      `LaxColimitPreReg.prPairExists` (the lax product's pairing), specialised to the cone whose
      product object is the stage product `⟨i, a×b⟩` rather than the colimit product `prObj`.

  Mirrors the strict assembly line-by-line, replacing `castHom`/object-equalities with the lax
  `pushHom`/coherence-iso conjugations.  Mathlib-free.
-/
import Fredy.S1_543_RatCapHcanon
import Fredy.S1_543_CatColimitRegular

open CategoryTheory Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}
variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L) (data : LaxProductData L)

/-! ## Joint monicity of two single-stage projection germs (lax `colimHom_monicPair_of_rep`)

  Two germs `xP ⟶ xa`, `xP ⟶ xb` included at the reflexive-domain bound `⟨k0, refl k0, hcod⟩` from a
  common product-stage object `xP : L.A k0` are jointly left-cancellable, PROVIDED every pair of
  stage maps into `L.F hk0n xP` agreeing after `(functF hk0n).map projA` and after
  `(functF hk0n).map projB` is already equal (`hcancel`).  This is the joint dual of
  `RatCapHcanon.homInclL_mono_of_stage`, and the lax mirror of `Colim.colimHom_monicPair_of_rep`.

  PROOF.  Reduce both projection-composites of two competitor germs to single germs (`prCompProj`),
  extract a common bound from the two germ equalities, fold the level pushes by `prPsi_push`, strip
  the trailing `isoInv (transApp)` by post-composition, and apply `hcancel` to the `prUnit`-conjugated
  representatives; cancel `prUnit` to obtain the germ witness.  This is `prJointMono`'s argument with
  the per-fibre `data.pres` abstracted to the hypothesis `hcancel` and the product object left
  generic. -/
theorem homInclL_monicPair_of_stage
    {k0 ia ib : ι} (xP : L.A k0) (xa : L.A ia) (xb : L.A ib)
    (hia : D.le ia k0) (hib : D.le ib k0)
    (projA : xP ⟶ L.F hia xa) (projB : xP ⟶ L.F hib xb)
    (hcancel : ∀ {n : ι} (hk0n : D.le k0 n) (Zt : L.A n)
        (u v : Zt ⟶ L.F hk0n xP),
        u ≫ (L.functF hk0n).map projA = v ≫ (L.functF hk0n).map projA →
        u ≫ (L.functF hk0n).map projB = v ≫ (L.functF hk0n).map projB → u = v) :
    @MonicPair (Obj L) (laxColimCat L hL) ⟨k0, xP⟩ ⟨ia, xa⟩ ⟨ib, xb⟩
      (homInclL L hL xP xa ⟨k0, D.refl k0, hia⟩ (reflApp L xP ≫ projA))
      (homInclL L hL xP xb ⟨k0, D.refl k0, hib⟩ (reflApp L xP ≫ projB)) := by
  letI : Cat (Obj L) := laxColimCat L hL
  intro W h₁ h₂ hf hs
  revert hf hs
  refine Quotient.inductionOn₂ h₁ h₂ (fun rh₁ rh₂ hf hs => ?_)
  obtain ⟨a₁, m₁⟩ := rh₁
  obtain ⟨a₂, m₂⟩ := rh₂
  -- convert the laxColimCat `≫` to `compL` so the `prCompProj` rewrites match syntactically.
  replace hf : @compL _ _ L hL W ⟨k0, xP⟩ ⟨ia, xa⟩ (Quotient.mk _ ⟨a₁, m₁⟩)
        (homInclL L hL xP xa ⟨k0, D.refl k0, hia⟩ (reflApp L xP ≫ projA))
      = @compL _ _ L hL W ⟨k0, xP⟩ ⟨ia, xa⟩ (Quotient.mk _ ⟨a₂, m₂⟩)
        (homInclL L hL xP xa ⟨k0, D.refl k0, hia⟩ (reflApp L xP ≫ projA)) := hf
  replace hs : @compL _ _ L hL W ⟨k0, xP⟩ ⟨ib, xb⟩ (Quotient.mk _ ⟨a₁, m₁⟩)
        (homInclL L hL xP xb ⟨k0, D.refl k0, hib⟩ (reflApp L xP ≫ projB))
      = @compL _ _ L hL W ⟨k0, xP⟩ ⟨ib, xb⟩ (Quotient.mk _ ⟨a₂, m₂⟩)
        (homInclL L hL xP xb ⟨k0, D.refl k0, hib⟩ (reflApp L xP ≫ projB)) := hs
  -- reduce both projection composites to single germs at a common bound `e ≥ a₁.1, a₂.1, k0`.
  obtain ⟨w0, hw0a, hw0b⟩ := D.bound a₁.1 a₂.1
  obtain ⟨e, hew, hek⟩ := D.bound w0 k0
  have ha₁e : D.le a₁.1 e := D.trans hw0a hew
  have ha₂e : D.le a₂.1 e := D.trans hw0b hew
  rw [prCompProj L hL W.2 xP xa hia projA a₁ m₁ e ha₁e hek,
      prCompProj L hL W.2 xP xa hia projA a₂ m₂ e ha₂e hek] at hf
  rw [prCompProj L hL W.2 xP xb hib projB a₁ m₁ e ha₁e hek,
      prCompProj L hL W.2 xP xb hib projB a₂ m₂ e ha₂e hek] at hs
  -- extract germ relations from `hf`/`hs`, then a common bound `n`.
  obtain ⟨cf, hcf1, hcf2, eqf⟩ := Quotient.exact hf
  obtain ⟨cs, hcs1, hcs2, eqs⟩ := Quotient.exact hs
  obtain ⟨n, hcfn, hcsn⟩ := D.bound cf.1 cs.1
  simp only [homSystemL] at eqf eqs
  -- fold the pushes of `prPsi` to the level `cf.1`/`cs.1`, then on to `n`.
  rw [prPsi_push L hL W.2 xP xa hia projA a₁ m₁ e cf.1 ha₁e hek hcf1,
      prPsi_push L hL W.2 xP xa hia projA a₂ m₂ e cf.1 ha₂e hek hcf2] at eqf
  rw [prPsi_push L hL W.2 xP xb hib projB a₁ m₁ e cs.1 ha₁e hek hcs1,
      prPsi_push L hL W.2 xP xb hib projB a₂ m₂ e cs.1 ha₂e hek hcs2] at eqs
  have eqf' := congrArg (pushHom L W.2 xa (D.trans a₁.2.1 (D.trans ha₁e hcf1))
      (D.trans hia (D.trans hek hcf1)) hcfn) eqf
  have eqs' := congrArg (pushHom L W.2 xb (D.trans a₁.2.1 (D.trans ha₁e hcs1))
      (D.trans hib (D.trans hek hcs1)) hcsn) eqs
  rw [prPsi_push L hL W.2 xP xa hia projA a₁ m₁ cf.1 n _ _ hcfn,
      prPsi_push L hL W.2 xP xa hia projA a₂ m₂ cf.1 n _ _ hcfn] at eqf'
  rw [prPsi_push L hL W.2 xP xb hib projB a₁ m₁ cs.1 n _ _ hcsn,
      prPsi_push L hL W.2 xP xb hib projB a₂ m₂ cs.1 n _ _ hcsn] at eqs'
  -- unfold `prPsi` and fold the projection germ to `prUnit ≫ map proj ≫ isoInv (transApp)`.
  unfold prPsi at eqf' eqs'
  rw [pushHom_proj L xa xP hia _ projA] at eqf'
  rw [pushHom_proj L xb xP hib _ projB] at eqs'
  -- level data at `n`.
  have hkn : D.le k0 n := D.trans hek (D.trans hcf1 hcfn)
  have ha₁n : D.le a₁.1 n := D.trans ha₁e (D.trans hcf1 hcfn)
  have ha₂n : D.le a₂.1 n := D.trans ha₂e (D.trans hcf1 hcfn)
  -- the `prUnit`-conjugated reps `u₁,u₂ : F(W.1≤n) W.2 ⟶ F(k0≤n) xP`.
  let u₁ : L.F (D.trans a₁.2.1 ha₁n) W.2 ⟶ L.F hkn xP :=
    pushHom L W.2 xP a₁.2.1 a₁.2.2 ha₁n m₁ ≫ prUnit L xP hkn
  let u₂ : L.F (D.trans a₂.2.1 ha₂n) W.2 ⟶ L.F hkn xP :=
    pushHom L W.2 xP a₂.2.1 a₂.2.2 ha₂n m₂ ≫ prUnit L xP hkn
  -- cancel the trailing `isoInv (transApp)` (post-compose with `transApp`).
  have hfst : u₁ ≫ (L.functF hkn).map projA = u₂ ≫ (L.functF hkn).map projA := by
    have := congrArg (· ≫ transApp L hia hkn xa) eqf'
    simp only [CategoryTheory.Category.assoc, inv_isoInv_comp, CategoryTheory.Category.comp_id] at this
    simpa only [u₁, u₂, CategoryTheory.Category.assoc] using this
  have hsnd : u₁ ≫ (L.functF hkn).map projB = u₂ ≫ (L.functF hkn).map projB := by
    have := congrArg (· ≫ transApp L hib hkn xb) eqs'
    simp only [CategoryTheory.Category.assoc, inv_isoInv_comp, CategoryTheory.Category.comp_id] at this
    simpa only [u₁, u₂, CategoryTheory.Category.assoc] using this
  -- joint cancellation gives `u₁ = u₂`; cancel `prUnit` to get the germ witness.
  have huv : u₁ = u₂ :=
    hcancel hkn (L.F (D.trans a₁.2.1 ha₁n) W.2) u₁ u₂ hfst hsnd
  have hmm : pushHom L W.2 xP a₁.2.1 a₁.2.2 ha₁n m₁ = pushHom L W.2 xP a₂.2.1 a₂.2.2 ha₂n m₂ := by
    have h2 := congrArg (· ≫ isoInv (prUnit_isIso L xP hkn)) huv
    simpa only [u₁, u₂, CategoryTheory.Category.assoc, isoInv_comp, CategoryTheory.Category.comp_id] using h2
  exact Quotient.sound ⟨⟨n, D.trans a₁.2.1 ha₁n, hkn⟩, ha₁n, ha₂n, hmm⟩

/-! ## `objIncl i` preserves the stage product `(hp i).prod a b`

  Mirrors `Colim.objIncl_preserves_products`. -/
theorem objInclL_preserves_products (i : ι) (a b : L.A i) :
    @IsIso (Obj L) (laxColimCat L hL) _ _
      (@pair (Obj L) (laxColimCat L hL) (laxColimHasBinaryProducts L hL data)
        (objIncl L i ((data.hp i).prod a b)) (objIncl L i a) (objIncl L i b)
        (stageInclL L hL ((data.hp i).fst (A := a) (B := b)))
        (stageInclL L hL ((data.hp i).snd (A := a) (B := b)))) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasBinaryProducts (Obj L) := laxColimHasBinaryProducts L hL data
  let P0 : L.A i := (data.hp i).prod a b
  let fstS : P0 ⟶ a := (data.hp i).fst
  let sndS : P0 ⟶ b := (data.hp i).snd
  -- joint monicity (uniqueness half) of the two stage projections.  `hMP` is stated in the helper's
  -- `homInclL` form; `stageInclL` unfolds to exactly this, so it is reused below by defeq.
  have hcancel : ∀ {n : ι} (hk0n : D.le i n) (Zt : L.A n)
      (u v : Zt ⟶ L.F hk0n P0),
      u ≫ (L.functF hk0n).map (fstS ≫ isoInv (reflApp_isIso L a))
        = v ≫ (L.functF hk0n).map (fstS ≫ isoInv (reflApp_isIso L a)) →
      u ≫ (L.functF hk0n).map (sndS ≫ isoInv (reflApp_isIso L b))
        = v ≫ (L.functF hk0n).map (sndS ≫ isoInv (reflApp_isIso L b)) → u = v := by
    intro n hk0n Zt u v hu hv
    refine data.pres hk0n a b Zt u v ?_ ?_
    · have key := congrArg (· ≫ (L.functF hk0n).map (reflApp L a)) hu
      rw [(L.functF hk0n).map_comp fstS (isoInv (reflApp_isIso L a))] at key
      simp only [CategoryTheory.Category.assoc] at key
      rw [← (L.functF hk0n).map_comp (isoInv (reflApp_isIso L a)) (reflApp L a),
          inv_isoInv_comp, (L.functF hk0n).map_id, CategoryTheory.Category.comp_id] at key
      exact key
    · have key := congrArg (· ≫ (L.functF hk0n).map (reflApp L b)) hv
      rw [(L.functF hk0n).map_comp sndS (isoInv (reflApp_isIso L b))] at key
      simp only [CategoryTheory.Category.assoc] at key
      rw [← (L.functF hk0n).map_comp (isoInv (reflApp_isIso L b)) (reflApp L b),
          inv_isoInv_comp, (L.functF hk0n).map_id, CategoryTheory.Category.comp_id] at key
      exact key
  have hMP : @MonicPair (Obj L) (laxColimCat L hL) ⟨i, P0⟩ ⟨i, a⟩ ⟨i, b⟩
      (stageInclL L hL fstS) (stageInclL L hL sndS) :=
    homInclL_monicPair_of_stage L hL P0 a b (D.refl i) (D.refl i)
      (fstS ≫ isoInv (reflApp_isIso L a)) (sndS ≫ isoInv (reflApp_isIso L b)) hcancel
  refine isIso_of_product_up _ _ (fun {Z} f g => ?_)
  -- existence half: build the mediator at a common stage `N ≥ i`.
  refine Quotient.inductionOn f (fun rf => ?_)
  refine Quotient.inductionOn g (fun rg => ?_)
  obtain ⟨af, fa⟩ := rf
  obtain ⟨bg, ga⟩ := rg
  obtain ⟨e1, he1a, he1b⟩ := D.bound af.1 bg.1
  obtain ⟨N, hNe, hiN⟩ := D.bound e1 i
  have hafN : D.le af.1 N := D.trans he1a hNe
  have hbgN : D.le bg.1 N := D.trans he1b hNe
  -- competitor legs at `N`, post-composed with the unit conjugator `prUnit` (lands in `F hiN a/b`).
  let p_comp : L.F (D.trans af.2.1 hafN) Z.2 ⟶ L.F hiN a :=
    pushHom L Z.2 a af.2.1 af.2.2 hafN fa ≫ prUnit L a hiN
  let q_comp : L.F (D.trans af.2.1 hafN) Z.2 ⟶ L.F hiN b :=
    pushHom L Z.2 b bg.2.1 bg.2.2 hbgN ga ≫ prUnit L b hiN
  obtain ⟨r, hr_fst, hr_snd⟩ := data.presPair hiN a b (L.F (D.trans af.2.1 hafN) Z.2) p_comp q_comp
  let u : Z ⟶ ⟨i, P0⟩ :=
    homInclL L hL Z.2 P0 ⟨N, D.trans af.2.1 hafN, hiN⟩ (r ≫ isoInv (prUnit_isIso L P0 hiN))
  -- the `prPairExists.leg` argument, specialised: a projection composite of `u` reduces to the
  -- pushed competitor.  `proj = projS ≫ isoInv reflApp` and the trailing iso is `transApp`.
  have leg : ∀ (w : L.A i) (projS : P0 ⟶ w)
      (aw : UpperBound D Z.1 i) (wa : L.F aw.2.1 Z.2 ⟶ L.F aw.2.2 w) (hawN : D.le aw.1 N),
      r ≫ (L.functF hiN).map (projS ≫ isoInv (reflApp_isIso L w))
          = pushHom L Z.2 w aw.2.1 aw.2.2 hawN wa ≫ transApp L (D.refl i) hiN w →
      @compL _ _ L hL Z ⟨i, P0⟩ ⟨i, w⟩ u (stageInclL L hL projS)
        = Quotient.mk (setoid (homSystemL L hL Z.2 w)) ⟨aw, wa⟩ := by
    intro w projS aw wa hawN hcomp
    show homCompRawL L hL Z.2 P0 w ⟨N, D.trans af.2.1 hafN, hiN⟩ (r ≫ isoInv (prUnit_isIso L P0 hiN))
        ⟨i, D.refl i, D.refl i⟩ (reflApp L P0 ≫ (projS ≫ isoInv (reflApp_isIso L w)))
      = homInclL L hL Z.2 w aw wa
    rw [homCompRawL_eq_compAtL L hL Z.2 P0 w ⟨N, D.trans af.2.1 hafN, hiN⟩
          (r ≫ isoInv (prUnit_isIso L P0 hiN)) ⟨i, D.refl i, D.refl i⟩
          (reflApp L P0 ≫ (projS ≫ isoInv (reflApp_isIso L w))) N (D.refl N) hiN]
    unfold compAtL
    rw [hL.push_refl Z.2 P0 (D.trans af.2.1 hafN) hiN (r ≫ isoInv (prUnit_isIso L P0 hiN)),
        pushHom_proj L w P0 (D.refl i) hiN (projS ≫ isoInv (reflApp_isIso L w))]
    rw [CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc (isoInv (prUnit_isIso L P0 hiN)),
        inv_isoInv_comp, CategoryTheory.Category.id_comp, ← CategoryTheory.Category.assoc, hcomp,
        CategoryTheory.Category.assoc, isoInv_comp, CategoryTheory.Category.comp_id]
    exact homInclL_compat L hL Z.2 w (a := aw)
      (b := ⟨N, D.trans aw.2.1 hawN, D.trans aw.2.2 hawN⟩) hawN wa
  -- the two `hcomp` obligations: `prUnit ≫ map (isoInv reflApp) = transApp`.
  have hpu : ∀ (w : L.A i),
      prUnit L w hiN ≫ (L.functF hiN).map (isoInv (reflApp_isIso L w)) = transApp L (D.refl i) hiN w := by
    intro w
    unfold prUnit
    rw [CategoryTheory.Category.assoc, ← (L.functF hiN).map_comp (reflApp L w) (isoInv (reflApp_isIso L w)),
        isoInv_comp, (L.functF hiN).map_id, CategoryTheory.Category.comp_id]
  have hcomp_fst : r ≫ (L.functF hiN).map (fstS ≫ isoInv (reflApp_isIso L a))
      = pushHom L Z.2 a af.2.1 af.2.2 hafN fa ≫ transApp L (D.refl i) hiN a := by
    rw [(L.functF hiN).map_comp fstS (isoInv (reflApp_isIso L a)), ← CategoryTheory.Category.assoc, hr_fst]
    show (pushHom L Z.2 a af.2.1 af.2.2 hafN fa ≫ prUnit L a hiN)
        ≫ (L.functF hiN).map (isoInv (reflApp_isIso L a)) = _
    rw [CategoryTheory.Category.assoc, hpu a]
  have hcomp_snd : r ≫ (L.functF hiN).map (sndS ≫ isoInv (reflApp_isIso L b))
      = pushHom L Z.2 b bg.2.1 bg.2.2 hbgN ga ≫ transApp L (D.refl i) hiN b := by
    rw [(L.functF hiN).map_comp sndS (isoInv (reflApp_isIso L b)), ← CategoryTheory.Category.assoc, hr_snd]
    show (pushHom L Z.2 b bg.2.1 bg.2.2 hbgN ga ≫ prUnit L b hiN)
        ≫ (L.functF hiN).map (isoInv (reflApp_isIso L b)) = _
    rw [CategoryTheory.Category.assoc, hpu b]
  have hux : @compL _ _ L hL Z ⟨i, P0⟩ ⟨i, a⟩ u (stageInclL L hL fstS) = Quotient.mk _ ⟨af, fa⟩ :=
    leg a fstS af fa hafN hcomp_fst
  have huy : @compL _ _ L hL Z ⟨i, P0⟩ ⟨i, b⟩ u (stageInclL L hL sndS) = Quotient.mk _ ⟨bg, ga⟩ :=
    leg b sndS bg ga hbgN hcomp_snd
  exact ⟨u, ⟨hux, huy⟩, fun v hv₁ hv₂ => hMP v u (hv₁.trans hux.symm) (hv₂.trans huy.symm)⟩

end Freyd.LaxColim
