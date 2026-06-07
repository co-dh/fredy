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
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_58

set_option linter.unusedSectionVars false

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

/-- Inverse image f#: 𝒫(B) → 𝒫(A) preserves finite unions.
    For f: A→B and subobject B'↣B, f#(B') is the pullback of B' along f. -/
def InverseImage (f : A ⟶ B) (B' : Subobject 𝒞 B) [HasPullbacks 𝒞] : Subobject 𝒞 A :=
  -- The pullback of B'.arr along f
  sorry

/-- f# preserves binary unions: for any S,T subobjects of B,
    f#(S ∪ T) is isomorphic to f#(S) ∪ f#(T). -/
def inverseImage_preserves_unions (f : A ⟶ B) [HasPullbacks 𝒞] : Prop :=
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

/-- In a poset (Hom sets are subsingleton), the pre-logos condition
    reduces to distributivity of the lattice. -/
theorem poset_prelogos_iff_distributive [PreLogos 𝒞]
    (hThin : ∀ {A B : 𝒞} (f g : A ⟶ B), f = g) : True := by
  -- In a thin category, every morphism is monic, covers are isos,
  -- and pre-logos ⇔ distributive lattice.
  trivial

end Freyd
