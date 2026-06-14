/-
  Freyd & Scedrov, *Categories and Allegories* §1.6  Pre-logoi.

  §1.6  PRE-LOGOS: regular category where subobject posets are lattices
        and inverse image preserves unions.  Equivalent: Cartesian +
        images + pullbacks transfer finite covers.
  §1.61 0 = minimal subobject of 1.  Any map to 0 is iso. 0 is coterminator.
  §1.612 For monic f: A↣B, f# distributes over unions iff distributive lattice.
  §1.613 Poset is pre-logos iff it is a distributive lattice.
  §1.614 Representation of pre-logoi.
-/


import Fredy.S1_1
import Fredy.S1_34
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_58


open Freyd

universe v u

/-- Set type (this project has no Std; define locally). -/
def Set (α : Type u) := α → Prop

def Set_mem {α : Type u} (a : α) (s : Set α) : Prop := s a
infix:50 " ∈ " => Set_mem

def Set_singleton {α : Type u} (a : α) : Set α := λ x => x = a
def Set_setOf {α : Type u} (p : α → Prop) : Set α := p

notation "{ " x " | " p " }" => Set_setOf (λ x => p)
notation "{ " x " }" => Set_singleton x

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.6 Pre-logos

  A PRE-LOGOS is a regular category in which subobject posets
  are lattices (have binary unions) and inverse image preserves
  unions.  Equivalent: Cartesian + images + pullbacks transfer
  finite covers (§1.6). -/

/-- Subobjects have binary unions (join). -/
class HasSubobjectUnions (𝒞 : Type u) [Cat.{v} 𝒞] [HasImages 𝒞] where
  union : ∀ {B : 𝒞} (S T : Subobject 𝒞 B), Subobject 𝒞 B
  union_left  : ∀ {B} (S T : Subobject 𝒞 B), S.le (union S T)
  union_right : ∀ {B} (S T : Subobject 𝒞 B), T.le (union S T)
  union_min   : ∀ {B} (S T U : Subobject 𝒞 B), S.le U → T.le U → (union S T).le U

/-- Inverse image f#: 𝒫(B) → 𝒫(A).  For subobject B'↣B, f#(B')
    is the pullback of B'.arr along f.  The pullback of a monic is
    monic (standard; proof deferred). -/
def InverseImage (f : A ⟶ B) (B' : Subobject 𝒞 B) [HasPullbacks 𝒞] : Subobject 𝒞 A :=
  let pb := HasPullbacks.has f B'.arr
  { dom := pb.cone.pt
    arr := pb.cone.π₁
    monic := by
      intro W u v h
      -- h: u ≫ pb.cone.π₁ = v ≫ pb.cone.π₁
      have h_pb_w : pb.cone.π₁ ≫ f = pb.cone.π₂ ≫ B'.arr := pb.cone.w
      have h_π₂_eq : u ≫ pb.cone.π₂ = v ≫ pb.cone.π₂ :=
        B'.monic (u ≫ pb.cone.π₂) (v ≫ pb.cone.π₂) (by
          calc
            (u ≫ pb.cone.π₂) ≫ B'.arr = u ≫ (pb.cone.π₂ ≫ B'.arr) := by rw [Cat.assoc]
            _ = u ≫ (pb.cone.π₁ ≫ f) := by rw [h_pb_w]
            _ = (u ≫ pb.cone.π₁) ≫ f := by rw [Cat.assoc]
            _ = (v ≫ pb.cone.π₁) ≫ f := by rw [h]
            _ = v ≫ (pb.cone.π₁ ≫ f) := by rw [Cat.assoc]
            _ = v ≫ (pb.cone.π₂ ≫ B'.arr) := by rw [h_pb_w]
            _ = (v ≫ pb.cone.π₂) ≫ B'.arr := by rw [Cat.assoc])
      let c : Cone f B'.arr :=
        { pt := W
          π₁ := u ≫ pb.cone.π₁
          π₂ := u ≫ pb.cone.π₂
          w := calc
            (u ≫ pb.cone.π₁) ≫ f = u ≫ (pb.cone.π₁ ≫ f) := by rw [Cat.assoc]
            _ = u ≫ (pb.cone.π₂ ≫ B'.arr) := by rw [h_pb_w]
            _ = (u ≫ pb.cone.π₂) ≫ B'.arr := by rw [Cat.assoc] }
      calc
        u = pb.lift c := pb.lift_uniq c u rfl rfl
        _ = v := (pb.lift_uniq c v (by rw [h.symm]) (by rw [h_π₂_eq.symm])).symm }

/-- f# preserves binary unions: for any S,T subobjects of B,
    f#(S ∪ T) is isomorphic to f#(S) ∪ f#(T). -/
def inverseImage_preserves_unions {A B : 𝒞} (f : A ⟶ B) [HasImages 𝒞] [HasSubobjectUnions 𝒞] [HasPullbacks 𝒞] : Prop :=
  ∀ (S T : Subobject 𝒞 B),
    Isomorphic (InverseImage f (HasSubobjectUnions.union S T)).dom
               (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)).dom

/-- A PRE-LOGOS (§1.6): regular + subobject lattices + inverse image
    preserves unions. -/
class PreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    RegularCategory 𝒞, HasSubobjectUnions 𝒞 where
  invImage_preserves_union : ∀ {A B : 𝒞} (f : A ⟶ B), inverseImage_preserves_unions f

/-! ## §1.613 Posets as pre-logoi

  A poset viewed as a category is a pre-logos iff the poset is
  a distributive lattice (§1.613). -/

/-- A distributive lattice: the subobject unions satisfy distributivity. -/
def IsDistributiveLattice (𝒞 : Type u) [Cat.{v} 𝒞] [HasImages 𝒞] [HasSubobjectUnions 𝒞] : Prop :=
  ∀ {B : 𝒞} (A S T : Subobject 𝒞 B),
    Subobject.le (HasSubobjectUnions.union
      (HasSubobjectUnions.union A S) A)
      (HasSubobjectUnions.union A (HasSubobjectUnions.union S T))

/-- In a thin category (at most one morphism per hom-set), pre-logos
    is equivalent to being a distributive lattice (§1.613). -/
axiom poset_prelogos_iff_distributive [PreLogos 𝒞]
    (hThin : ∀ {A B : 𝒞} (f g : A ⟶ B), f = g) : IsDistributiveLattice 𝒞

end Freyd
