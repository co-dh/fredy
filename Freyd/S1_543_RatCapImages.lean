/-
  §1.543 / §2.218 R3 — `ratCapCat P` HAS IMAGES (regular upgrade of the lax-colimit pre-regular target).

  Feeds `laxColimHasImages` (`LaxColimitImages.lean`) the slice premises for the base-change system
  `laxOfProjSystem' P` (fibres `Over (P.pr i)`, transitions = base-change `g*`):
    * per-fibre images          — `overHasImages` (slices of a category with images),
    * faithful transitions      — `projStage_faithful` (base-change along a cover is faithful),
    * mono-preserving           — `projStage_preservesMono`,
    * cover-preserving          — `projStage_preservesCover`,
    * image-preserving          — `transitions_preserve_images` (derived from mono + cover preservation),
    * pullbacks in the colimit  — `ratCapPreRegular_of_projCover … |>.toHasPullbacks`.

  This is the `hi : ∀ i, HasImages (stage i)` ingredient that upgrades the cofinal `ratCapCat` tower
  from pre-regular to REGULAR, hence makes §2.218 R3 (`RegularCategory Ā`) reachable. -/
import Freyd.S1_543_LaxColimitImages
import Freyd.S1_543_RatCapStagePTC
import Freyd.S1_65_SlicePreTopos

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u

variable {ι : Type u} {D : Directed ι} {𝒞 : Type u} [Cat.{u} 𝒞] [PreRegularCategory 𝒞] [HasImages 𝒞]

-- INSTANCE-DIAMOND PIN (§1.543) — see `UniformCapStep.lean`/`FibreDensityProof.lean`.  `laxOfProjSystem'`
-- resolves its `[HasPullbacks 𝒞]` to either `PreRegularCategory.toHasPullbacks` or the global
-- `exactPullbacks` inconsistently across def sites; pin both so every `laxOfProjSystem' P` agrees.
local instance (priority := 10000) ratCapImgPinEq : HasEqualizers 𝒞 :=
  products_pullbacks_implies_equalizers
local instance (priority := 10000) ratCapImgPinPb : HasPullbacks 𝒞 :=
  PreRegularCategory.toHasPullbacks

/-- **`ratCapCat P` has images**, given cover-projections.  The §1.547 lax-colimit successor target,
    pre-regular by `ratCapPreRegular_of_projCover`, is in fact REGULAR. -/
noncomputable def ratCapHasImages [Nonempty ι] (P : ProjSystem ι D 𝒞)
    (hpc : ∀ {i j : ι} (h : D.le i j), Cover (P.proj h)) :
    @HasImages (Obj (laxOfProjSystem' P)) (ratCapCat P) := by
  -- transition mono- and cover-preservation (as `Preserves…` props), shared by `himgpres`.
  have hmono : ∀ {i j : ι} (hij : D.le i j),
      @PreservesMono _ ((laxOfProjSystem' P).catA i) _ ((laxOfProjSystem' P).catA j)
        ((laxOfProjSystem' P).F hij) ((laxOfProjSystem' P).functF hij) :=
    fun {i j} hij {X Y} {f} hf => projStage_preservesMono P hij f hf
  have hcovpres : ∀ {i j : ι} (hij : D.le i j),
      @PreservesCovers _ _ ((laxOfProjSystem' P).catA i) ((laxOfProjSystem' P).catA j)
        ((laxOfProjSystem' P).F hij) ((laxOfProjSystem' P).functF hij) :=
    fun {i j} hij {A B} f hf => projStage_preservesCover P hij f hf
  -- pullbacks in `ratCapCat P` come from its pre-regularity.
  letI hpull : @HasPullbacks (Obj (laxOfProjSystem' P)) (ratCat P) :=
    (ratCapPreRegular_of_projCover P (fun h => hpc h)).toHasPullbacks
  exact laxColimHasImages (laxOfProjSystem' P) (coherentProj P)
    (fun i => overHasImages (P.pr i))
    (fun {i j} hij {x y} p q heq => projStage_faithful P hij (hpc hij) p q heq)
    hmono
    (fun {i j} hij {X Y} f =>
      letI : HasImages ((laxOfProjSystem' P).A i) := overHasImages (P.pr i)
      letI : HasPullbacks ((laxOfProjSystem' P).A j) := overHasPullbacks (P.pr j)
      transitions_preserve_images ((laxOfProjSystem' P).F hij)
        (hF := (laxOfProjSystem' P).functF hij) (hmono hij) (hcovpres hij) f)

end Freyd.LaxColim
