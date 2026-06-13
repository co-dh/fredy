/-
  Freyd & Scedrov, *Categories and Allegories* §1.54
  Capitalization Lemma.

  §1.541: A framework ℱ of small (pre-)regular categories + faithful representations.
         ℱ = all small (pre-)regular categories satisfies the three conditions:
         (1) equivalence-invariant, (2) slice-closed (proved §1.53),
         (3) directed-union-closed.

  §1.544: For well-supported B ∈ A, A embeds faithfully in A/B.
  §1.545: Relative capitalization definition.
  §1.543: Capitalization Lemma.

  The Henkin-Lubkin representation theorem (§1.55) lives in `S1_55.lean`.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31
import Fredy.S1_33
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_44
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_53


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

/-! ## §1.544: A embeds faithfully in A/B for well-supported B

  The book describes interpreting A as a subcategory of A/B by sending
  A ↦ A × B (the product with B).  When B is well-supported, this
  functor is a faithful embedding. -/

/-- The "product with B" functor A → A/B: sends C ↦ C×B with the
    projection as the structure map into B.  Faithful when B is
    well-supported. -/
def sliceEmbedding (B : 𝒞) (hws : WellSupported B) : 𝒞 → 𝒞 :=
  λ C => prod C B

/-- §1.544: For well-supported B, the functor A → A/B given by
    C ↦ C×B is a faithful embedding. -/
theorem slice_embedding_faithful (B : 𝒞) (hws : WellSupported B) [Functor (sliceEmbedding B hws)] : Faithful (sliceEmbedding B hws) := by
  -- The book: "A: A → A/B separates objects and, if B is well-supported,
  -- separates morphisms."  The construction uses the product with B:
  -- for f,g: C → D, if C×B → D×B agree as A/B-morphisms, then f = g.
  -- This follows because B is well-supported, so the projection B → 1 is cover,
  -- and the pullback properties force equality.
  sorry

/-! ## §1.545 Relative capitalization

  A ⊆ A* is a RELATIVE CAPITALIZATION if for every proper subobject
  B' ↣ B in A with B well-supported, there exists a point x: 1 → B
  in A* that does not factor through B'.  §1.546 constructs it by
  iterating the slice functor A → A/B for each well-supported B. -/

/-- A* is a relative capitalization of A. -/
def IsRelativeCapitalization [HasTerminal 𝒞] [HasImages 𝒞] (A A_star : 𝒞) : Prop :=
  ∀ (B : 𝒞) (hws : WellSupported B) (B' : Subobject 𝒞 B)
    (hproper : ¬ Subobject.IsEntire B'),
    ∃ (x : one ⟶ B), ¬ Allows B' x

/-! ## §1.543 Capitalization Lemma

  If A is a small (pre-)regular category, there exists a capital
  (pre-)regular category Ā and a faithful representation A → Ā.

  The proof iterates the construction A ↦ A/B for each well-supported
  B (building a relative capitalization), well-orders the process, and
  takes the directed union.  This is the Capitalization Lemma.

  We state it as an existential; the full constructive proof (§1.544-6)
  requires transfinite recursion and is beyond the scope of this
  formalization. -/

theorem capitalization_lemma (A : Type u) [Cat.{v} A] [PreRegularCategory A] :
    ∃ (Ā : Type u) (hC : Cat.{v} Ā) (hP : PreRegularCategory Ā),
      @Capital.{v, u} Ā hC (hP.toHasTerminal) ∧
      ∃ (F : A → Ā) (hF : Functor F), @Faithful.{v, u} A _ Ā hC F hF := by
  -- The proof iterates the relative capitalization construction A ⊆ A*
  -- via A* = the category obtained by adding points to A for each
  -- well-supported object (essentially A ↦ union over B of A/B).
  -- This requires transfinite iteration.  We defer the constructive proof.
  sorry

end Freyd
