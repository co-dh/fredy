/-
  §1.543 — IMAGES in the lax hom-colimit `laxColimCat L hL`.

  Port of `Colim.colimitHasImages` (CatColimitRegular.lean, strict colimit) to the LAX colimit
  structure.  A germ `F = ⟨a, f₀⟩ : ⟨i,x⟩ ⟶ ⟨j,y⟩` factors as a COVER `E` followed by a MONO `M`:
  take the stage-`a.1` image factorization `f₀ = e₀ ≫ m₀` (`e₀ = image.lift`, `m₀ = (image f₀).arr`),
  put the image object at `Img = ⟨a.1, (image f₀).dom⟩`, and include `m₀`/`e₀` as germs (bridging the
  reflexive `F (refl a.1)` collapse by `reflApp`).  `M` is monic because `m₀` is and transitions
  preserve monos (`homInclL_mono_of_stage`); `E` is a cover because `e₀` (an image-lift) stays a cover
  under every transition (`preservesImage_lift_cover` from `himgpres`, then `homInclL_cover_of_rep`);
  `E ⊚ M = F` collapses at the common bound `a.1` (`push_refl` + `reflApp` cancellation).  `coverMono_
  isImage` then certifies `Subobject.mk Img M` as the image.

  This supplies the `hi : ∀ i, HasImages (stage i)` premise of `capitalization_regular_of_cofinalSystem`
  for the COFINAL `ratCapCat` tower (each stage being a `laxColimCat`), making §2.218 R3
  (`RegularCategory Ā`) reachable. -/
import Fredy.S1_543_RatCapHcanon
import Fredy.S1_543_CatColimitRegular

open Freyd
open Freyd.Colim

namespace Freyd.LaxColim

universe w

variable {ι : Type w} {D : Directed ι} (L : LaxCatSystem.{w, w} ι D) (hL : Coherent L)

/-- **The lax hom-colimit has images** (port of `Colim.colimitHasImages`).  Premises mirror the strict
    version: per-fibre images (`hi`), faithful (`hfaith`), mono-preserving (`hmono`) and image-preserving
    (`himgpres`) transitions, and pullbacks in the colimit. -/
noncomputable def laxColimHasImages
    (hi : ∀ i, @HasImages (L.A i) (L.catA i))
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        @Functor.map _ _ _ _ _ (L.functF hij) x y p
          = @Functor.map _ _ _ _ _ (L.functF hij) x y q → p = q)
    (hmono : ∀ {i j : ι} (hij : D.le i j),
        @PreservesMono _ (L.catA i) _ (L.catA j) (L.F hij) (L.functF hij))
    (himgpres : ∀ {i j : ι} (hij : D.le i j) {X Y : L.A i} (f : X ⟶ Y),
        @IsImage (L.A j) (L.catA j) _ _ (@Functor.map _ _ _ _ _ (L.functF hij) X Y f)
          (@Subobject.map _ _ (L.catA i) (L.catA j) (L.F hij) (L.functF hij) (hmono hij) _
            (@image _ (L.catA i) (hi i) _ _ f)))
    [hpull : @HasPullbacks (Obj L) (laxColimCat L hL)] :
    @HasImages (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  have hImgData : ∀ (X Y : Obj L) (F : X ⟶ Y),
      ∃ (I : Subobject (Obj L) Y), IsImage F I := by
    intro X Y
    obtain ⟨i, x⟩ := X
    obtain ⟨j, y⟩ := Y
    refine Quotient.ind (fun Fr => ?_)
    obtain ⟨a, f₀⟩ := Fr
    letI : HasImages (L.A a.1) := hi a.1
    -- stage-`a.1` image factorization of `f₀`.
    let Iobj : L.A a.1 := (image f₀).dom
    let m₀ : Iobj ⟶ L.F a.2.2 y := (image f₀).arr
    let e₀ : L.F a.2.1 x ⟶ Iobj := image.lift f₀
    have hfac : e₀ ≫ m₀ = f₀ := image.lift_fac f₀
    have hm₀_mono : @Monic (L.A a.1) (L.catA a.1) _ _ m₀ := (image f₀).monic
    -- image object and the two germ legs (refl-bridged at `a.1`).
    let Img : Obj L := ⟨a.1, Iobj⟩
    let gM : L.F (D.refl a.1) Iobj ⟶ L.F a.2.2 y := reflApp L Iobj ≫ m₀
    let gE : L.F a.2.1 x ⟶ L.F (D.refl a.1) Iobj := e₀ ≫ isoInv (reflApp_isIso L Iobj)
    let M : @Cat.Hom (Obj L) (laxColimCat L hL) Img ⟨j, y⟩ :=
      homInclL L hL Iobj y ⟨a.1, D.refl a.1, a.2.2⟩ gM
    let E : @Cat.Hom (Obj L) (laxColimCat L hL) ⟨i, x⟩ Img :=
      homInclL L hL x Iobj ⟨a.1, a.2.1, D.refl a.1⟩ gE
    -- (1) `M` is monic: `m₀` is monic and `pushHom gM = transApp ≫ map(reflApp ≫ m₀) ≫ isoInv` is
    --     `map m₀` (monic via `hmono`) flanked by isos.
    have hM_mono : @Monic (Obj L) (laxColimCat L hL) Img ⟨j, y⟩ M := by
      refine homInclL_mono_of_stage L hL Iobj y ⟨a.1, D.refl a.1, a.2.2⟩ gM ?_
      intro e hae z u v huv
      have hgM_mono : @Monic (L.A e) (L.catA e) _ _
          (pushHom L Iobj y (D.refl a.1) a.2.2 hae gM) := by
        simp only [gM]
        unfold pushHom
        rw [@Functor.map_comp _ _ _ _ _ (L.functF hae) _ _ _ (reflApp L Iobj) m₀]
        refine mono_precomp_iso' (transApp_isIso L (D.refl a.1) hae Iobj) ?_
        refine mono_postcomp_iso' ?_
          ⟨transApp L a.2.2 hae y, inv_isoInv_comp _, isoInv_comp _⟩
        exact mono_precomp_iso'
          (@functor_preserves_iso _ _ _ _ _ (L.functF hae) _ _ (reflApp L Iobj) (reflApp_isIso L Iobj))
          (hmono hae hm₀_mono)
      exact hgM_mono u v huv
    -- (2) `E` is a cover: `e₀ = image.lift f₀` stays a cover under every transition
    --     (`preservesImage_lift_cover` from `himgpres`), and `pushHom gE` is that cover flanked by isos.
    have hE_cover : @Cover (Obj L) (laxColimCat L hL) ⟨i, x⟩ Img E := by
      apply homInclL_cover_of_rep L hL hfaith x Iobj ⟨a.1, a.2.1, D.refl a.1⟩ gE
      intro e hae
      simp only [gE]
      unfold pushHom
      rw [@Functor.map_comp _ _ _ _ _ (L.functF hae) _ _ _ e₀ (isoInv (reflApp_isIso L Iobj))]
      refine cover_precomp_iso (transApp_isIso L a.2.1 hae x) ?_
      refine cover_comp_iso' ?_
        ⟨transApp L (D.refl a.1) hae Iobj, inv_isoInv_comp _, isoInv_comp _⟩
      refine cover_comp_iso'
        (preservesImage_lift_cover (L.F hae) (hF := L.functF hae) (hmono hae) f₀ (himgpres hae f₀)) ?_
      exact @functor_preserves_iso _ _ _ _ _ (L.functF hae) _ _ (isoInv (reflApp_isIso L Iobj))
        ⟨reflApp L Iobj, inv_isoInv_comp _, isoInv_comp _⟩
    -- (3) `E ⊚ M = F` (collapses at bound `a.1`).
    have hEM : @Cat.comp (Obj L) (laxColimCat L hL) ⟨i, x⟩ Img ⟨j, y⟩ E M
        = homInclL L hL x y a f₀ := by
      show @compL _ _ L hL ⟨i, x⟩ ⟨a.1, Iobj⟩ ⟨j, y⟩
          (homInclL L hL x Iobj ⟨a.1, a.2.1, D.refl a.1⟩ gE)
          (homInclL L hL Iobj y ⟨a.1, D.refl a.1, a.2.2⟩ gM)
        = homInclL L hL x y a f₀
      rw [compL_homInclL_compAtL L hL x Iobj y ⟨a.1, a.2.1, D.refl a.1⟩ gE
            ⟨a.1, D.refl a.1, a.2.2⟩ gM a.1 (D.refl a.1) (D.refl a.1),
          hL.push_refl x Iobj a.2.1 (D.refl a.1) gE,
          hL.push_refl Iobj y (D.refl a.1) a.2.2 gM]
      show homInclL L hL x y a (gE ≫ gM) = homInclL L hL x y a f₀
      congr 1
      show (e₀ ≫ isoInv (reflApp_isIso L Iobj)) ≫ (reflApp L Iobj ≫ m₀) = f₀
      rw [Cat.assoc, ← Cat.assoc (isoInv (reflApp_isIso L Iobj)) (reflApp L Iobj) m₀,
          inv_isoInv_comp (reflApp_isIso L Iobj), Cat.id_comp]
      exact hfac
    exact ⟨Subobject.mk Img M hM_mono, coverMono_isImage hM_mono hE_cover hEM⟩
  exact { image := fun {X Y} F => (hImgData X Y F).choose
          isImage := fun {X Y} F => (hImgData X Y F).choose_spec }

end Freyd.LaxColim
