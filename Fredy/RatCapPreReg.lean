/-
  §1.543 — CONCRETE pre-regularity of the §1.547 base-change slice colimit `ratCapCat P`.

  `LaxColimitPreReg.lean` proves `laxColimPreRegular : PreRegularCategory (laxColimCat L hL)` from
  four hypothesis bundles `LaxTerminalData L`/`LaxProductData L`/`LaxEqualizerData L`/`hcanon`.  This
  file INHABITS those four bundles for `L := laxOfProjSystem' P`, the §1.547 base-change slice system
  (fibres `L.A i = Over (P.pr i)`, transitions `L.F hij = baseChangeObj (P.proj hij)`), and assembles

      instance : PreRegularCategory (ratCapCat P).

  The per-fibre finite-limit data is `overPreRegular` (`SliceRegular.lean`).  The transition
  PRESERVATION (each bundle's `pres`/`presPair`/`presLift`) is exactly "the pullback functor `g*`
  preserves finite limits".  We prove this constructively via the BASE-CHANGE ADJUNCTION
  `Σ_g ⊣ g*` (`reindexObj g ⊣ baseChangeObj g`): a slice map `z ⟶ g* W` in `Over C` is the SAME
  DATA as a slice map `reindexObj g z ⟶ W` in `Over D` (both are an arrow `z.dom ⟶ W.dom` with
  `· ≫ W.hom = z.hom ≫ g`).  The bijection `bcHomEquiv` transports the fibre's product/equalizer
  universal property (joint-monic, pairing, lift) across `g*`, giving every bundle field.

  Mathlib-free; built on the repo's own `Cat` + `SliceRegular` + `CapitalizationLaxColimit` +
  `LaxColimitPreReg`.
-/
import Fredy.LaxColimitPreReg

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}
variable {𝒞 : Type w} [Cat.{w} 𝒞] [HasPullbacks 𝒞]

/-! ## The base-change adjunction `Σ_g ⊣ g*` on the underlying-arrow level

  For `g : C ⟶ D`, base-change `baseChangeObj g : Over D → Over C` sends `W` to the pullback
  `W ×_D C` with structure map `π₂`.  A slice map `u : z ⟶ baseChangeObj g W` in `Over C` is an
  arrow `u.f : z.dom ⟶ (W ×_D C).pt` with `u.f ≫ π₂ = z.hom`.  Post-composing `u.f` with `π₁`
  gives an arrow `z.dom ⟶ W.dom`, and the pullback square turns the over-`C` law into the over-`D`
  law `(u.f ≫ π₁) ≫ W.hom = z.hom ≫ g`.  This is the adjunction transpose; we package its two
  directions as `bcRight`/`bcLeft` and prove they are mutually inverse, plus the naturality we need
  (it intertwines post-composition `· ≫ baseChangeMap g m` with `· ≫ m`). -/
section BaseChangeAdj

variable {C D : 𝒞} (g : C ⟶ D)

/-- The base pullback `W ×_D C` of `W.hom` along `g`.  `abbrev` so `(bcPB g W).cone.pt` is
    definitionally `(baseChangeObj g W).dom` (both unfold to `HasPullbacks.has W.hom g`). -/
abbrev bcPB (W : Over D) : HasPullback W.hom g := HasPullbacks.has W.hom g

/-- **Transpose (right→left): `(z ⟶ g* W) → (reindexObj g z ⟶ W)`.**  Post-compose with `π₁`.  The
    over-`D` law is the pullback square: `(u.f ≫ π₁) ≫ W.hom = u.f ≫ (π₂ ≫ g) = z.hom ≫ g`. -/
def bcTranspose {z : Over C} {W : Over D} (u : z ⟶ baseChangeObj g W) :
    reindexObj g z ⟶ W :=
  ⟨u.f ≫ (bcPB g W).cone.π₁, by
    show (u.f ≫ (bcPB g W).cone.π₁) ≫ W.hom = z.hom ≫ g
    rw [Cat.assoc, (bcPB g W).cone.w, ← Cat.assoc]
    show (u.f ≫ (bcPB g W).cone.π₂) ≫ g = z.hom ≫ g
    rw [show u.f ≫ (bcPB g W).cone.π₂ = z.hom from u.w]⟩

/-- **Transpose (left→right): `(reindexObj g z ⟶ W) → (z ⟶ g* W)`.**  Lift the cone `(a.f, z.hom)`
    into the pullback `W ×_D C`; the cone commutes because `a.f ≫ W.hom = z.hom ≫ g` (the over-`D`
    law).  The lift's `π₂`-leg is `z.hom`, the over-`C` law. -/
def bcLift {z : Over C} {W : Over D} (a : reindexObj g z ⟶ W) :
    z ⟶ baseChangeObj g W :=
  ⟨(bcPB g W).lift ⟨z.dom, a.f, z.hom, by
      show a.f ≫ W.hom = z.hom ≫ g; exact a.w⟩,
    (bcPB g W).lift_snd _⟩

@[simp] theorem bcTranspose_f {z : Over C} {W : Over D} (u : z ⟶ baseChangeObj g W) :
    (bcTranspose g u).f = u.f ≫ (bcPB g W).cone.π₁ := rfl

/-- `bcLift ∘ bcTranspose = id` (over `C`): both arrows lift the same pullback cone, by
    `lift_uniq`. -/
theorem bcLift_bcTranspose {z : Over C} {W : Over D} (u : z ⟶ baseChangeObj g W) :
    bcLift g (bcTranspose g u) = u :=
  OverHom.ext ((bcPB g W).lift_uniq
    ⟨z.dom, (bcTranspose g u).f, z.hom, (bcTranspose g u).w⟩ u.f rfl u.w).symm

/-- `bcTranspose ∘ bcLift = id` (over `D`): the lift's `π₁`-leg is `a.f`, by `lift_fst`. -/
theorem bcTranspose_bcLift {z : Over C} {W : Over D} (a : reindexObj g z ⟶ W) :
    bcTranspose g (bcLift g a) = a :=
  OverHom.ext ((bcPB g W).lift_fst _)

/-- **Naturality of the transpose.**  Post-composing in `Over D` with `m : W ⟶ W'` corresponds to
    post-composing in `Over C` with `baseChangeMap g m`: `bcTranspose (u ⊚ g*m) = bcTranspose u ⊚ m`.
    (Both underlying arrows are `u.f ≫ π₁ˣ ≫ ...`; the base-change map's `π₁`-leg is `lift_fst`.) -/
theorem bcTranspose_natural {z : Over C} {W W' : Over D} (u : z ⟶ baseChangeObj g W)
    (m : W ⟶ W') :
    bcTranspose g (u ⊚ baseChangeMap g m) = bcTranspose g u ⊚ m := by
  apply OverHom.ext
  show (u.f ≫ (baseChangeMap g m).f) ≫ (bcPB g W').cone.π₁
      = (u.f ≫ (bcPB g W).cone.π₁) ≫ m.f
  show (u.f ≫ (bcPB g W').lift (baseChangeCone g m)) ≫ (bcPB g W').cone.π₁
      = (u.f ≫ (bcPB g W).cone.π₁) ≫ m.f
  rw [Cat.assoc, (bcPB g W').lift_fst (baseChangeCone g m)]
  show u.f ≫ ((bcPB g W).cone.π₁ ≫ m.f) = (u.f ≫ (bcPB g W).cone.π₁) ≫ m.f
  rw [Cat.assoc]

end BaseChangeAdj

end Freyd.LaxColim
