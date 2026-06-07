/-
  Freyd & Scedrov, *Categories and Allegories* §1.45  Pullbacks and kernel pairs.

  Cone: a cone over a cospan A—f→C←g—B.
  HasPullback: a pullback (cone + universal property).  §1.454
  HasPullbacks: the category has all pullbacks.
  kernelPair f: pullback of f along f (§1.454).
  monic_iff_kp_diag_iso: f monic ↔ kp_diag f iso (§1.453).
-/

import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42

set_option linter.unusedSectionVars false

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-- A cone over the cospan `A —f→ C ←g— B` (§1.454). -/
structure Cone {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) where
  pt : 𝒞
  π₁ : pt ⟶ A
  π₂ : pt ⟶ B
  w  : π₁ ≫ f = π₂ ≫ g

/-- A pullback of the cospan `A —f→ C ←g— B`: a distinguished `cone` and
    universal lift.  §1.454 -/
class HasPullback {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) where
  cone : Cone f g
  lift      (c : Cone f g) : c.pt ⟶ cone.pt
  lift_fst  (c : Cone f g) : lift c ≫ cone.π₁ = c.π₁
  lift_snd  (c : Cone f g) : lift c ≫ cone.π₂ = c.π₂
  lift_uniq (c : Cone f g) (u : c.pt ⟶ cone.pt)
    (h₁ : u ≫ cone.π₁ = c.π₁) (h₂ : u ≫ cone.π₂ = c.π₂) : u = lift c

/-- The category has all pullbacks. -/
class HasPullbacks (𝒞 : Type u) [Cat.{v} 𝒞] where
  has {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) : HasPullback f g

variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

/-- The kernel pair of `f` : pullback of `f` along itself.  §1.454 -/
def kernelPair {A B : 𝒞} (f : A ⟶ B) : 𝒞 := (hpull.has f f).cone.pt

section
variable {A B X : 𝒞} {f : A ⟶ B}

def kp₁ : kernelPair f ⟶ A := (hpull.has f f).cone.π₁
def kp₂ : kernelPair f ⟶ A := (hpull.has f f).cone.π₂

theorem kp_sq : kp₁ (f:=f) ≫ f = kp₂ (f:=f) ≫ f := (hpull.has f f).cone.w

/-- The diagonal cone `(A, 1_A, 1_A)` over the cospan `(f, f)`. -/
def diagCone : Cone f f := ⟨A, Cat.id A, Cat.id A, rfl⟩

def kp_diag : A ⟶ kernelPair f := (hpull.has f f).lift diagCone

theorem kp_diag_p₁ : kp_diag (f:=f) ≫ kp₁ (f:=f) = Cat.id A := (hpull.has f f).lift_fst diagCone
theorem kp_diag_p₂ : kp_diag (f:=f) ≫ kp₂ (f:=f) = Cat.id A := (hpull.has f f).lift_snd diagCone

theorem kp_lift_p₁ (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) :
    (hpull.has f f).lift ⟨_, x₁, x₂, h⟩ ≫ kp₁ (f:=f) = x₁ := (hpull.has f f).lift_fst _

theorem kp_lift_p₂ (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) :
    (hpull.has f f).lift ⟨_, x₁, x₂, h⟩ ≫ kp₂ (f:=f) = x₂ := (hpull.has f f).lift_snd _

theorem kp_lift_uniq (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f)
    (g : X ⟶ kernelPair f) (h₁ : g ≫ kp₁ (f:=f) = x₁) (h₂ : g ≫ kp₂ (f:=f) = x₂) :
    g = (hpull.has f f).lift ⟨_, x₁, x₂, h⟩ := (hpull.has f f).lift_uniq ⟨_, x₁, x₂, h⟩ g h₁ h₂

/-- Lemma from §1.453: f is monic iff the diagonal into its kernel pair is iso. -/
theorem monic_iff_kp_diag_iso : Mono f ↔ IsIso (kp_diag (f:=f)) := by
  constructor
  · intro hm
    have h_eq : kp₁ (f:=f) = kp₂ (f:=f) := hm _ _ kp_sq
    refine ⟨kp₁ (f:=f), kp_diag_p₁, ?_⟩
    have h_id : (hpull.has f f).lift ⟨_, kp₁ (f:=f), kp₂ (f:=f), kp_sq⟩ = Cat.id (kernelPair f) :=
      (kp_lift_uniq (kp₁ (f:=f)) (kp₂ (f:=f)) kp_sq (Cat.id (kernelPair f))
        (Cat.id_comp _) (Cat.id_comp _)).symm
    have h_comp : (kp₁ (f:=f)) ≫ kp_diag (f:=f) =
        (hpull.has f f).lift ⟨_, kp₁ (f:=f), kp₂ (f:=f), kp_sq⟩ :=
      (kp_lift_uniq (kp₁ (f:=f)) (kp₂ (f:=f)) kp_sq ((kp₁ (f:=f)) ≫ kp_diag (f:=f))
        (by rw [Cat.assoc, kp_diag_p₁, Cat.comp_id])
        (by rw [Cat.assoc, kp_diag_p₂, Cat.comp_id, h_eq]))
    rw [h_comp, h_id]
  · intro hiso
    obtain ⟨inv, _diag_inv, inv_diag⟩ := hiso
    intro X x₁ x₂ h
    let hpair : X ⟶ kernelPair f := (hpull.has f f).lift ⟨_, x₁, x₂, h⟩
    let t : X ⟶ A := hpair ≫ inv
    have ht : hpair = t ≫ kp_diag (f:=f) := by
      dsimp [t]; rw [Cat.assoc, inv_diag]; rw [Cat.comp_id]
    calc
      x₁ = hpair ≫ kp₁ (f:=f) := by rw [kp_lift_p₁ x₁ x₂ h]
      _ = (t ≫ kp_diag (f:=f)) ≫ kp₁ (f:=f) := by rw [ht]
      _ = t ≫ (kp_diag (f:=f) ≫ kp₁ (f:=f)) := by rw [Cat.assoc]
      _ = t ≫ Cat.id A := by rw [kp_diag_p₁]
      _ = t := by rw [Cat.comp_id]
      _ = t ≫ Cat.id A := by rw [Cat.comp_id]
      _ = t ≫ (kp_diag (f:=f) ≫ kp₂ (f:=f)) := by rw [kp_diag_p₂]
      _ = (t ≫ kp_diag (f:=f)) ≫ kp₂ (f:=f) := by rw [← Cat.assoc]
      _ = hpair ≫ kp₂ (f:=f) := by rw [ht]
      _ = x₂ := by rw [kp_lift_p₂ x₁ x₂ h]

end
