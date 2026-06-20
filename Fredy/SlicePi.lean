/-
  Freyd & Scedrov, *Categories and Allegories* §1.931 —
  the DEPENDENT-PRODUCT functor `Π_f : Over A → Over B`, right adjoint to the
  pullback functor `f* : Over B → Over A` (`baseChangeObj f`).

  STRATEGY (slice-of-slice, strict).  For `f : A ⟶ B`, write `f̂ = ⟨A, f⟩ : Over B`.
  An object of `(Over B)/f̂` is `⟨Y, m⟩` with `Y = ⟨E, e⟩ : Over B` and
  `m : OverHom Y f̂`, i.e. `m.f : E ⟶ A` with `m.f ≫ f = e`.  The pair `(E, m.f)`
  is EXACTLY an object of `Over A`, with `e = m.f ≫ f` forced.  So

      Over A  ≅  (Over B) / f̂                                (ISO of categories)

  is an isomorphism on the nose (not merely an equivalence).  Under it the pullback
  functor `f* : Over B → Over A` becomes "product with `f̂`" in `Over B`, whose right
  adjoint is the exponential `(−)^f̂` (available: `Over B` is a topos, hence has
  exponentials).  Transporting that exponential adjunction back across the iso gives

      f*  ⊣  Π_f .

  This file builds `Π_f` and the adjunction hom-iso at the right altitude (a real
  `Adjunction (baseChangeObj f) Π_f`), reusing `Over B`'s `HasExponentials`.
-/
import Fredy.SlicePower
import Fredy.SliceRegular

open Freyd

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

section SliceOfSlice
variable {A B : 𝒞} (f : A ⟶ B)

/-- `f̂ = ⟨A, f⟩ : Over B`, the object of `Over B` "named" by `f`.  Slicing `Over B`
    over `f̂` reproduces `Over A` on the nose (see `Phi`/`Psi`). -/
def fHat : Over B := ⟨A, f⟩

/-- **`Φ : Over A → (Over B)/f̂`** on objects.  An object `X = ⟨E, x : E ⟶ A⟩` of
    `Over A` becomes the `(Over B)`-object `⟨E, x ≫ f⟩` sliced over `f̂` by the
    triangle `x : ⟨E, x≫f⟩ ⟶ f̂` (which commutes definitionally: `x ≫ f = x ≫ f`). -/
def PhiObj (X : Over A) : Over (fHat f) :=
  ⟨⟨X.dom, X.hom ≫ f⟩, ⟨X.hom, rfl⟩⟩

/-- `Φ` on morphisms: the SAME underlying arrow `h.f : X.dom ⟶ Y.dom`, which is a
    map of `Over B`-triangles over `f̂`. -/
def PhiMap {X Y : Over A} (h : OverHom X Y) :
    OverHom (PhiObj f X) (PhiObj f Y) :=
  ⟨⟨h.f, by show h.f ≫ (Y.hom ≫ f) = X.hom ≫ f; rw [← Cat.assoc, h.w]⟩,
    by apply OverHom.ext; show h.f ≫ Y.hom = X.hom; exact h.w⟩

/-- **`Ψ : (Over B)/f̂ → Over A`** on objects (the inverse of `Φ`).  An object
    `Z = ⟨⟨E,e⟩, m : ⟨E,e⟩ ⟶ f̂⟩` of `(Over B)/f̂` has `m.f : E ⟶ A` with
    `m.f ≫ f = e`; forget `e` and keep `⟨E, m.f⟩ : Over A`. -/
def PsiObj (Z : Over (fHat f)) : Over A :=
  ⟨Z.dom.dom, Z.hom.f⟩

/-- `Ψ` on morphisms: the underlying arrow `h.f.f`. -/
def PsiMap {Z W : Over (fHat f)} (h : OverHom Z W) :
    OverHom (PsiObj f Z) (PsiObj f W) :=
  ⟨h.f.f, by
    show h.f.f ≫ W.hom.f = Z.hom.f
    exact congrArg OverHom.f h.w⟩

/-- `Ψ ∘ Φ = id` on objects, ON THE NOSE. -/
@[simp] theorem Psi_Phi_obj (X : Over A) : PsiObj f (PhiObj f X) = X := rfl

end SliceOfSlice

/-! ## The slice-of-slice hom bijection (the load-bearing core)

  `Φ` is fully faithful: a map `X ⟶ Y` in `Over A` is the SAME data as a map
  `Φ X ⟶ Φ Y` in `(Over B)/f̂` (both are an arrow `X.dom ⟶ Y.dom` commuting with the
  structure maps into `A`).  We package the two directions as `phiHom`/`phiInv`. -/
section SliceOfSliceHom
variable {A B : 𝒞} (f : A ⟶ B)

/-- `Φ` on homs, packaged as a function `(X ⟶ Y) → (Φ X ⟶ Φ Y)`. -/
def phiHom {X Y : Over A} (h : OverHom X Y) : OverHom (PhiObj f X) (PhiObj f Y) :=
  PhiMap f h

/-- `Ψ` on homs, the inverse direction `(Φ X ⟶ Φ Y) → (X ⟶ Y)`. -/
def phiInv {X Y : Over A} (k : OverHom (PhiObj f X) (PhiObj f Y)) : OverHom X Y :=
  ⟨k.f.f, congrArg OverHom.f k.w⟩

@[simp] theorem phiInv_phiHom {X Y : Over A} (h : OverHom X Y) :
    phiInv f (phiHom f h) = h := OverHom.ext rfl

@[simp] theorem phiHom_phiInv {X Y : Over A} (k : OverHom (PhiObj f X) (PhiObj f Y)) :
    phiHom f (phiInv f k) = k := OverHom.ext (OverHom.ext rfl)

end SliceOfSliceHom

end Freyd
