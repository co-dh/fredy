/-
  §1.543 (lax) — `objIncl i` PRESERVES PULLBACKS in the FILTERED lax colimit.

  ════════════════════════════════════════════════════════════════════════════════════════════
  This is the LAX port of `Capitalization.objIncl_preserves_pullbacks` (the M3-cov ingredient (3)).

  The strict template (`Fredy/Capitalization.lean:283`) is a ONE-LINER body:

      exact image_chosenPullback_isPullback (C.objIncl i) hFun
        (objIncl_preservesBinaryProducts …) (objIncl_preservesEqualizers …) f g

  where `image_chosenPullback_isPullback` is the GENERIC §1.45 lemma "a functor preserving binary
  products + equalizers sends the §1.432 chosen pullback to a pullback cone".  Its lax-compatible
  port is `RatCapHcanon.image_chosenPullback_isPullback'`.

  We reproduce that one-liner over the lax colimit.  The two `Preserves*` arguments are built here as
  WRAPPERS around the committed germ-preservation facts:

    * `objInclL_preserves_products`   (`Fredy/LaxGermProducts.lean`)   → `PreservesBinaryProducts`;
    * `objInclL_preserves_equalizers` (`Fredy/LaxGermEqualizers.lean`) → `PreservesEqualizers`.

  Mirrors the strict `objIncl_preservesBinaryProducts` / `objIncl_preservesEqualizers` wrappers
  line-for-line: products is a direct repackage of the `IsIso (pair …)` germ; equalizers converts
  the `EqualizerCone.IsEqualizer` germ to the comparison-map-iso form via `isIso_of_two_equalizers`
  against the chosen colimit equalizer.

  UNIVERSE.  Single universe `L : LaxCatSystem.{w,w} ι D` (`ι : Type w`), matching the
  `RatCapHcanon.SingleUniverse` section that hosts `stageInclFunctorL` and
  `image_chosenPullback_isPullback'` (both need source `L.A i` and target `Obj L` at the same
  hom-universe `w`).  The products germ is `{u,w}`; we instantiate it at `u = w`.  Mathlib-free.
-/
import Fredy.S1_543_LaxGermProducts
import Fredy.S1_543_LaxGermEqualizers

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe w

variable {ι : Type w} {D : Directed ι}
variable (L : LaxCatSystem.{w, w} ι D) (hL : Coherent L)

/-! ## `objIncl i` sends the §1.432 chosen pullback to a pullback cone

  Assembles the two germ-based `Preserves*` wrappers through `image_chosenPullback_isPullback'`. -/

/-- **`objIncl i` preserves pullbacks (lax M3-cov ingredient (3), assembled).**  The `objIncl i`-image
    of the §1.432 *stage* pullback of a cospan `(f, g)` in `L.A i` is a pullback cone in
    `laxColimCat L hL`.  Lax port of `Capitalization.objIncl_preserves_pullbacks`: assembles
    `objInclL_preservesBinaryProducts` and `objInclL_preservesEqualizers` through the generic
    `image_chosenPullback_isPullback'`. -/
theorem objInclL_preserves_pullbacks [Nonempty ι]
    (tData : LaxTerminalData L) (pData : LaxProductData L) (eqData : LaxEqualizerData L) (i : ι)
    {A B C : L.A i} (f : A ⟶ C) (g : B ⟶ C) :
    letI : HasTerminal (L.A i) := tData.ht i
    letI : HasBinaryProducts (L.A i) := pData.hp i
    letI : HasEqualizers (L.A i) := eqData.he i
    letI : Cat (Obj L) := laxColimCat L hL
    letI : HasTerminal (Obj L) := laxColimHasTerminal L hL tData
    letI : HasBinaryProducts (Obj L) := laxColimHasBinaryProducts L hL pData
    letI : HasEqualizers (Obj L) := laxColimHasEqualizers L hL eqData
    (Cone.mk (f := stageInclL L hL f) (g := stageInclL L hL g)
      ((⟨i, (products_equalizers_implies_pullbacks f g).cone.pt⟩ : Obj L))
      (stageInclL L hL (products_equalizers_implies_pullbacks f g).cone.π₁)
      (stageInclL L hL (products_equalizers_implies_pullbacks f g).cone.π₂)
      ((stageInclL_comp L hL _ f).symm.trans
        ((congrArg (stageInclL L hL ·) (products_equalizers_implies_pullbacks f g).cone.w).trans
          (stageInclL_comp L hL _ g)))).IsPullback :=
  stageInclFunctorL_preservesPullbacks L hL tData pData eqData i f g

end Freyd.LaxColim
