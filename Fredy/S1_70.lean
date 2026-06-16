/-
  Freyd & Scedrov, *Categories and Allegories* §1.7  Logoi.

  §1.7  LOGOS: regular + subobject lattices + f# has right adjoint f##.
  §1.71 In boolean pre-logos, f##(A') = ¬f(¬A') (complement of direct image).
  §1.711 Logos ⇒ pre-logos (f# preserves all unions).
  §1.712 Locally complete: subobject lattices are complete.
  §1.72  Heyting algebra: lattice with implication →.
  §1.721 Sub-object lattice of any object in a logos is a Heyting algebra.
  §1.722 Poset is logos iff Heyting algebra.
  §1.723 Locale: complete lattice with distributivity.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_60


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## Subobject order helpers -/

/-- Mutual ≤ between subobjects gives isomorphic domains. -/
theorem subobject_le_antisymm_iso {B : 𝒞} {S T : Subobject 𝒞 B}
    (hST : S.le T) (hTS : T.le S) : Isomorphic S.dom T.dom := by
  obtain ⟨h₁, h₁fac⟩ := hST
  obtain ⟨h₂, h₂fac⟩ := hTS
  refine ⟨h₁, h₂, ?_, ?_⟩
  · exact S.monic (h₁ ≫ h₂) (Cat.id S.dom) (by rw [Cat.assoc, h₂fac, h₁fac, Cat.id_comp])
  · exact T.monic (h₂ ≫ h₁) (Cat.id T.dom) (by rw [Cat.assoc, h₁fac, h₂fac, Cat.id_comp])

/-- Transitivity of Subobject.le. -/
theorem subobject_le_trans {B : 𝒞} {X Y Z : Subobject 𝒞 B}
    (hXY : X.le Y) (hYZ : Y.le Z) : X.le Z :=
  let ⟨h₁, e₁⟩ := hXY; let ⟨h₂, e₂⟩ := hYZ
  ⟨h₁ ≫ h₂, by rw [Cat.assoc, e₂, e₁]⟩

/-- Reflexivity of Subobject.le. -/
theorem subobject_le_refl {B : 𝒞} (S : Subobject 𝒞 B) : S.le S :=
  ⟨Cat.id S.dom, Cat.id_comp S.arr⟩

/-! ## §1.7 Logos

  A LOGOS is a regular category where subobject lattices have a right
  adjoint f## to the inverse image f# for every f: A → B (§1.7). -/

-- Class definitions need HasPullbacks etc. in scope.
section LogosClasses

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-- f##(A') is the right adjoint of f#: the maximal B' ⊆ B such that
    f#(B') ⊆ A'.  Satisfies: f#(B') ⊆ A' ⇔ B' ⊆ f##(A'). -/
class HasRightAdjointImage (𝒞 : Type u) [Cat.{v} 𝒞] extends HasImages 𝒞, HasPullbacks 𝒞 where
  rightAdj : ∀ {A B : 𝒞} (f : A ⟶ B), Subobject 𝒞 A → Subobject 𝒞 B
  adjunction : ∀ {A B : 𝒞} (f : A ⟶ B) (B' : Subobject 𝒞 B) (A' : Subobject 𝒞 A),
    Subobject.le (InverseImage f B') A' ↔ Subobject.le B' (rightAdj f A')

/-- A LOGOS (§1.7): regular + subobject lattices + right adjoint to f#. -/
class Logos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    RegularCategory 𝒞, HasSubobjectUnions 𝒞, HasRightAdjointImage 𝒞

end LogosClasses

/-! ## §1.711 Logos ⇒ pre-logos

  In a logos, f# preserves all unions that exist.  Hence a logos is a
  pre-logos. -/

-- §1.711 helper: proved in its own section so the outer variable block
-- [HasPullbacks] / [HasImages] is NOT in scope and the Logos instances win.
section LogosPreLogosHelper

variable [L : Logos 𝒞]

-- InverseImage and HasSubobjectUnions now use L's internal instances.

private theorem logos_invImage_pres_union {A B : 𝒞} (f : A ⟶ B)
    (S T : Subobject 𝒞 B) :
    Isomorphic (InverseImage f (HasSubobjectUnions.union S T)).dom
               (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)).dom := by
  -- §1.711: via the adjunction f# ⊣ f##.
  -- adj: (InverseImage f B').le A' ↔ B'.le (f## A')
  have adj : ∀ (B' : Subobject 𝒞 B) (A' : Subobject 𝒞 A),
      (InverseImage f B').le A' ↔ B'.le (HasRightAdjointImage.rightAdj f A') :=
    fun B' A' => L.adjunction f B' A'
  let ST   := HasSubobjectUnions.union S T
  let fST  := InverseImage f ST
  let fS   := InverseImage f S
  let fT   := InverseImage f T
  let join := HasSubobjectUnions.union fS fT
  -- Step 1: join ≤ fST  (f#S ∪ f#T ≤ f#(S∪T))
  -- S∪T ≤ f##(fST) from f#(S∪T) ≤ f#(S∪T) [refl] and adj.
  have h_ST_le_ra : ST.le (HasRightAdjointImage.rightAdj f fST) :=
    (adj ST fST).mp (subobject_le_refl fST)
  have hS_le : fS.le fST := (adj S fST).mpr
    (subobject_le_trans (HasSubobjectUnions.union_left S T) h_ST_le_ra)
  have hT_le : fT.le fST := (adj T fST).mpr
    (subobject_le_trans (HasSubobjectUnions.union_right S T) h_ST_le_ra)
  have hle : join.le fST := HasSubobjectUnions.union_min _ _ _ hS_le hT_le
  -- Step 2: fST ≤ join  (f#(S∪T) ≤ f#S ∪ f#T)
  -- S ≤ f##(join) from f#S ≤ join [union_left] and adj; idem T.
  have hS_le_ra : S.le (HasRightAdjointImage.rightAdj f join) :=
    (adj S join).mp (HasSubobjectUnions.union_left fS fT)
  have hT_le_ra : T.le (HasRightAdjointImage.rightAdj f join) :=
    (adj T join).mp (HasSubobjectUnions.union_right fS fT)
  have hle2 : fST.le join := (adj ST join).mpr
    (HasSubobjectUnions.union_min S T _ hS_le_ra hT_le_ra)
  exact subobject_le_antisymm_iso hle2 hle

end LogosPreLogosHelper

section LogosFacts

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

def logos_implies_preLogos [L : Logos 𝒞] : PreLogos 𝒞 where
  toRegularCategory    := L.toRegularCategory
  toHasSubobjectUnions := L.toHasSubobjectUnions
  invImage_preserves_union {A B} f S T := logos_invImage_pres_union f S T
  -- §1.61: bottom subobject needs empty-join / initial object infrastructure
  -- that Logos does not directly provide beyond binary unions; faithful sorry.
  bottom                    := fun _ => by sorry
  bottom_min                := by sorry
  bottom_dom_iso            := by sorry
  invImage_preserves_bottom := by sorry

/-! ## §1.712 Locally complete categories

  A category is LOCALLY COMPLETE if each subobject lattice is
  a complete lattice (all meets/joins exist). -/

/-- Subobjects of A form a complete lattice (all meets and joins exist). -/
class LocallyComplete (𝒞 : Type u) [Cat.{v} 𝒞] extends HasImages 𝒞 where
  sup : ∀ {A : 𝒞}, ((Subobject 𝒞 A) → Prop) → Subobject 𝒞 A
  sup_upper : ∀ {A} (S : (Subobject 𝒞 A) → Prop) (s : Subobject 𝒞 A), S s → Subobject.le s (sup S)
  sup_least : ∀ {A} (S : (Subobject 𝒞 A) → Prop) (U : Subobject 𝒞 A),
    (∀ (s : Subobject 𝒞 A), S s → Subobject.le s U) → Subobject.le (sup S) U

/-- In a locally complete regular category with f# preserving all unions,
    the right adjoint f## exists (constructible as sup of all B' with f#(B')⊆A').
    §1.712: faithful sorry pending full construction. -/
def locallyComplete_with_union_preserving_is_logos
    [LocallyComplete 𝒞] [PreLogos 𝒞]
    (h_preserves : ∀ {A B : 𝒞} (f : A ⟶ B) (S : (Subobject 𝒞 B) → Prop),
      Subobject.le (InverseImage f (LocallyComplete.sup S))
                   (LocallyComplete.sup (λ A' => ∃ B', S B' ∧ A' = InverseImage f B'))) : Logos 𝒞 := by
  sorry

/-! ## §1.721 Subobject lattice of any object in a logos is a Heyting algebra.

  Given A₁, A₂ ⊆ A in a logos, let i : A₁ ↪ A be the inclusion map.
  Then (A₁ → A₂) := i##(A₁ ∩ A₂) = rightAdj i (intersection A₁ A₂).
  The adjunction gives: A₃ ∧ A₁ ≤ A₂ ↔ A₃ ≤ (A₁ → A₂). -/

-- §1.721 (subobject lattice of a logos object is a Heyting algebra) is stated
-- and developed in S1_72 alongside the `HeytingAlgebra` class; not restated here
-- as a vacuous stub.

/-! ## §1.722 A poset viewed as a category is a logos iff it is a Heyting algebra.

  Proof sketch: In a poset, InverseImage f B' = x∧y (meet), and f## gives
  implication.  §1.722 combines §1.721 and §1.613. -/

-- §1.722 (a poset is a logos iff it is a Heyting algebra) belongs with the
-- `HeytingAlgebra` development in S1_72 (which imports this file); not restated
-- here as a vacuous stub.

-- §1.723 LOCALE is defined canonically in S1_72 (with the meet/Heyting structure);
-- not duplicated here.

end LogosFacts

end Freyd
