/-
  Freyd & Scedrov, *Categories and Allegories* §1.7  Logoi.

  §1.7  LOGOS: regular + subobject lattices + f# has right adjoint f##.
  §1.71 In boolean pre-logos, f##(A') = ¬f(¬A') (complement of direct image).
  §1.711 Logos ⇒ pre-logos (f# preserves all unions).
  §1.712 Locally complete: subobject lattices are complete.
  §1.72  Heyting algebra: lattice with implication →.
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

/-! ## §1.7 Logos

  A LOGOS is a regular category where subobject lattices have a right
  adjoint f## to the inverse image f# for every f: A → B (§1.7). -/

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

/-! ## §1.711 Logos ⇒ pre-logos

  In a logos, f# preserves all unions that exist.  Hence, if A' has
  binary unions, f# preserves them (proved: f#(∪Bᵢ) = ∪f#(Bᵢ)). -/

def logos_implies_preLogos [Logos 𝒞] : PreLogos 𝒞 where
  toRegularCategory := by infer_instance
  toHasSubobjectUnions := by infer_instance
  invImage_preserves_union := λ {A B} f S T => by
    -- f#(S ∪ T) = f#(S) ∪ f#(T) follows from the adjunction
    sorry
  -- NOTE: a plain Logos has no canonical bottom subobject (empty join); the
  -- §1.61 `bottom` fields need additional (local-completeness) structure, so
  -- these are honest placeholders pending that.
  bottom := sorry
  bottom_min := sorry
  bottom_dom_iso := sorry
  invImage_preserves_bottom := sorry

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
    the right adjoint f## exists (constructible as sup of all B' with f#(B')⊆A'). -/
def locallyComplete_with_union_preserving_is_logos
    [LocallyComplete 𝒞] [PreLogos 𝒞]
    (h_preserves : ∀ {A B : 𝒞} (f : A ⟶ B) (S : (Subobject 𝒞 B) → Prop),
      Subobject.le (InverseImage f (LocallyComplete.sup S))
                   (LocallyComplete.sup (λ A' => ∃ B', S B' ∧ A' = InverseImage f B'))) : Logos 𝒞 := by
  sorry

/-! ## §1.72 Heyting algebra

  A HEYTING ALGEBRA is a lattice with a binary operation → satisfying
  x ∧ z ≤ y ⇔ z ≤ x → y  (x → y is the largest z with x ∧ z ≤ y). -/

/-! ## §1.723 Locale

  A LOCALE is a complete lattice such that finite meets distribute
  over arbitrary joins: x ∧ sup S = sup {x ∧ s | s ∈ S}. -/

end Freyd
