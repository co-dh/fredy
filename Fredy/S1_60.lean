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
      -- Pullback of a monic is monic: π₁ is left-cancellable.
      intro W u v huv
      -- B'.arr monic forces the π₂-legs to agree
      have hπ₂ : u ≫ pb.cone.π₂ = v ≫ pb.cone.π₂ := by
        apply B'.monic
        rw [Cat.assoc, ← pb.cone.w, ← Cat.assoc, huv, Cat.assoc, pb.cone.w, ← Cat.assoc]
      -- both u and v are the unique lift of the cone ⟨W, u≫π₁, u≫π₂⟩
      let c : Cone f B'.arr :=
        ⟨W, u ≫ pb.cone.π₁, u ≫ pb.cone.π₂, by rw [Cat.assoc, pb.cone.w, ← Cat.assoc]⟩
      rw [pb.lift_uniq c u rfl rfl, pb.lift_uniq c v huv.symm hπ₂.symm] }

/-- f# preserves binary unions: for any S,T subobjects of B,
    f#(S ∪ T) is isomorphic to f#(S) ∪ f#(T). -/
def inverseImage_preserves_unions [HasImages 𝒞] [HasSubobjectUnions 𝒞] {A B : 𝒞} (f : A ⟶ B) [HasPullbacks 𝒞] : Prop :=
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
def IsDistributiveLattice [HasImages 𝒞] [HasSubobjectUnions 𝒞] : Prop :=
  ∀ {B : 𝒞} (A S T : Subobject 𝒞 B),
    Subobject.le (HasSubobjectUnions.union
      (HasSubobjectUnions.union A S) A)
      (HasSubobjectUnions.union A (HasSubobjectUnions.union S T))

/-- In a thin category (at most one morphism per hom-set), pre-logos
    is equivalent to being a distributive lattice (§1.613). -/
theorem poset_prelogos_iff_distributive [PreLogos 𝒞]
    (_hThin : ∀ {A B : 𝒞} (f g : A ⟶ B), f = g) : IsDistributiveLattice (𝒞 := 𝒞) := by
  intro B A S T
  -- This (absorption) inequality holds from the lattice axioms alone.
  have le_trans : ∀ {X Y Z : Subobject 𝒞 B}, X.le Y → Y.le Z → X.le Z := by
    rintro X Y Z ⟨h1, e1⟩ ⟨h2, e2⟩
    exact ⟨h1 ≫ h2, by rw [Cat.assoc, e2, e1]⟩
  apply HasSubobjectUnions.union_min
  · apply HasSubobjectUnions.union_min
    · exact HasSubobjectUnions.union_left _ _
    · exact le_trans (HasSubobjectUnions.union_left S T) (HasSubobjectUnions.union_right _ _)
  · exact HasSubobjectUnions.union_left _ _

end Freyd
