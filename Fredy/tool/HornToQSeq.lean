/-
  Bridge: a Freyd DIAGRAM (§1.39) realized as a genuine `QSeq` from `S1_38b`, with a
  proof that its §1.395 `Satisfies` relation is exactly the Horn sentence's meaning.

  `Fredy/HornDiagram.lean` gives the *syntactic* iso `Horn ≅ Diagram` (strings) and the
  Typst renderer.  But the repo's `QSeq` (`Fredy/S1_38b.lean`) is *semantic*: a telescope
  of real morphisms in an ambient category `𝒟`, with a satisfaction relation.  This file
  ties the two together for the canonical §1.39 example, LEFT-INVERTIBILITY, by:

    1. building the actual `QSeq` term (`qLeftInv f`), and
    2. proving `Satisfies (qLeftInv f) (1_A) ↔ ∃ g, f ≫ g = 1_A`   (§1.17 left-invertible).

  So the *diagram* (a `QSeq`) provably *means* the *Horn sentence*.  This is the
  §1.394 correspondence ("a blackboard diagram ↔ a Q-sequence") at the semantic level,
  using the repo's own `Satisfies` — not a re-implementation.

  Why left-invertibility and not, e.g., idempotent-splitting: the bare telescope `QSeq`
  quantifies over *fillers* `g : A' ⟶ B` (factorizations), with FIXED objects.  The §1.39
  factorization/extension examples (left-invertible, "α left-divides f") fit directly.
  Properties with an existential *object* (idempotents split: ∃ B …) need the ambient to
  be the category of small categories (§1.395's "e.g."), i.e. `QSeq.map` over Cat-of-Cats;
  that cross-category construction is the §1.394 free-category interpreter, deferred.
-/

import Fredy.S1_38b   -- QSeq, Satisfies, QSeq.complement, satisfies_*, IsIso, Cat

open Freyd

universe v u

variable {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd
namespace HornToQSeq

/-- §1.39 LEFT-INVERTIBLE, as a genuine Q-sequence: a single `∃`-step over `f`, then the
    (customarily omitted) trailing `∀`.  Rooted at `A = dom f`. -/
def qLeftInv {A B : 𝒟} (f : A ⟶ B) : QSeq 𝒟 A :=
  .cons .ex f (.nil B .all)

/-- **The diagram means the Horn sentence.**  Tested at the identity `1_A`, the §1.395
    `Satisfies` of `qLeftInv f` unfolds to exactly left-invertibility of `f`
    (`∃ g, f ≫ g = 1_A`, §1.17).  Constructive (axiom-free). -/
theorem satisfies_qLeftInv {A B : 𝒟} (f : A ⟶ B) :
    Satisfies (qLeftInv f) (Cat.id A) ↔ ∃ g : B ⟶ A, f ≫ g = Cat.id A := by
  simp [qLeftInv, Satisfies]

/-- The COMPLEMENTARY diagram (∀ where the original had ∃) means the NEGATION: by Thm 2
    of `S1_38b`, it is satisfied iff `f` is NOT left-invertible.  (Uses `Classical`, via
    that theorem's De Morgan converse — exactly where the book puts it.) -/
theorem satisfies_complement_qLeftInv {A B : 𝒟} (f : A ⟶ B) :
    Satisfies (qLeftInv f).complement (Cat.id A) ↔ ¬ ∃ g : B ⟶ A, f ≫ g = Cat.id A := by
  rw [satisfies_complement_iff_not]
  simp [qLeftInv, Satisfies]

/-- Reflection along an iso (Thm 1 of `S1_38b`) applies to the left-invertible diagram:
    satisfaction is invariant under post-composing the test morphism by an isomorphism
    `e : A ⟶ A'`.  Constructive corollary — shows the bridge inherits §1.395's invariance. -/
theorem qLeftInv_iso_invariant {A B A' : 𝒟} (f : A ⟶ B) {e : A ⟶ A'} (he : IsIso e) :
    Satisfies (qLeftInv f) (Cat.id A) ↔ Satisfies (qLeftInv f) (Cat.id A ≫ e) :=
  satisfies_iff_postcomp_iso (qLeftInv f) (Cat.id A) he

/-! ### Correspondence with the syntactic side (`HornDiagram.leftInvertible`)

  `HornDiagram.leftInvertible : Horn` is the string-level sentence
  `∀ f: A→B. ∃ g: B→A. f g = 1`, whose rendered diagram is the triangle
  `A →f B →g A` with explicit identity (the §1.391/§1.393-correct picture).  Under any
  interpretation of its objects/arrows into an ambient `𝒟` (objects `A,B`, arrow `f`),
  that diagram IS `qLeftInv f`, and `satisfies_qLeftInv` certifies it denotes
  left-invertibility.  A fully generic syntactic→semantic interpreter (the §1.394 free
  category on the diagram's graph) is the natural next step; this file anchors the
  canonical case rigorously against the repo's `Satisfies`. -/

end HornToQSeq
end Freyd
