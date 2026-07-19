/-
  TEN Q-sequences (§1.395) generated as genuine `QSeq` terms, each PROVED to satisfy
  exactly its book meaning — the diagrammatic property re-read as `∀/∃` over morphisms.

  The bare telescope `QSeq` (S1_38b) quantifies over fillers `g : Aᵢ ⟶ B` (factorizations
  of the test morphism), so it expresses Freyd's §1.39 factorization/lifting Q-sequences
  in-category, plus the §1.395 calculus (complement, the `nil` boundary quantifier, the
  Thm-1 iso invariance).  Each `exNN_*` theorem is the VERIFICATION: its right side is the
  book property; `Satisfies` of the generated `QSeq` is proved equal to it.

  (Atomic-predicate Q-sequences — mono / product / pullback, §1.443/§2796 — and the
  object-existential / branching ones — idempotents-split, linear-order, §1.39 — live over
  the category of small categories, §1.394; that ambient is the documented next tier.)
-/

import Freyd.HornToQSeq   -- qLeftInv, satisfies_qLeftInv, …; transitively S1_38b's QSeq/Satisfies

open Freyd Freyd.HornToQSeq

universe v u
variable {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd
namespace QSeqExamples

variable {A B M N : 𝒟}

/-- **Ex 1 — §1.39 LEFT-INVERTIBLE** (the book's first Q-sequence, a single `∃`).
    Q-seq `(∃, f)·∀`, tested at `1_A`.  Means `∃ g, f g = 1_A`. -/
theorem ex01_left_invertible (f : A ⟶ B) :
    Satisfies (qLeftInv f) (Cat.id A) ↔ ∃ g : B ⟶ A, f ≫ g = Cat.id A :=
  satisfies_qLeftInv f

/-- **Ex 2 — §1.3(9) FACTOR-THROUGH** (`α` left-divides `h`).
    Q-seq `(∃, α)·∀`, tested at `h`.  Means `∃ g, α g = h`. -/
def qFactor (α : A ⟶ M) : QSeq 𝒟 A := .cons .ex α (.nil M .all)

theorem ex02_factor_through (α : A ⟶ M) (h : A ⟶ B) :
    Satisfies (qFactor α) h ↔ ∃ g : M ⟶ B, α ≫ g = h := by
  simp [qFactor, Satisfies]

/-- **Ex 3 — §1.39 ∀∃ LIFTING** (the book's second example, `∀∃`).
    Q-seq `(∀, α)·(∃, β)·∀`, tested at `h`.  Means: every `α`-factor of `h` lifts through `β`. -/
def qLift (α : A ⟶ M) (β : M ⟶ N) : QSeq 𝒟 A := .cons .all α (.cons .ex β (.nil N .all))

theorem ex03_forall_exists_lift (α : A ⟶ M) (β : M ⟶ N) (h : A ⟶ B) :
    Satisfies (qLift α β) h ↔ ∀ g : M ⟶ B, α ≫ g = h → ∃ k : N ⟶ B, β ≫ k = g := by
  simp [qLift, Satisfies]

/-- **Ex 4 — §1.3(9) CONJUNCTION as nesting** (`∃∃`, two-stage factorization).
    Q-seq `(∃, α)·(∃, β)·∀`, tested at `h`.  Means `∃ g, α g = h ∧ ∃ k, β k = g`. -/
def qTwo (α : A ⟶ M) (β : M ⟶ N) : QSeq 𝒟 A := .cons .ex α (.cons .ex β (.nil N .all))

theorem ex04_two_stage (α : A ⟶ M) (β : M ⟶ N) (h : A ⟶ B) :
    Satisfies (qTwo α β) h ↔ ∃ g : M ⟶ B, α ≫ g = h ∧ ∃ k : N ⟶ B, β ≫ k = g := by
  simp [qTwo, Satisfies]

/-- **Ex 5 — §1.395 COMPLEMENT (negation)**: the complement of Ex 1 is satisfied iff `f`
    is NOT left-invertible.  (Classical, via S1_38b Thm 2.) -/
theorem ex05_not_left_invertible (f : A ⟶ B) :
    Satisfies (qLeftInv f).complement (Cat.id A) ↔ ¬ ∃ g : B ⟶ A, f ≫ g = Cat.id A :=
  satisfies_complement_qLeftInv f

/-- **Ex 6 — §1.395 COMPLEMENT**: complement of Ex 2 is satisfied iff `h` does NOT factor
    through `α`.  (Classical, via Thm 2.) -/
theorem ex06_not_factor (α : A ⟶ M) (h : A ⟶ B) :
    Satisfies (qFactor α).complement h ↔ ¬ ∃ g : M ⟶ B, α ≫ g = h := by
  rw [satisfies_complement_iff_not]; simp [qFactor, Satisfies]

/-- **Ex 7 — §1.395 BOUNDARY (trailing ∀, "customarily omitted")**: the empty telescope
    with `Q₀ = ∀` is always satisfied. -/
theorem ex07_nil_all (f : A ⟶ B) : Satisfies (QSeq.nil A .all) f :=
  satisfies_nil_all f

/-- **Ex 8 — §1.395 BOUNDARY (trailing ∃)**: the empty telescope with `Q₀ = ∃` is never
    satisfied ("A₀→B satisfies iff Q₀ = ∀"). -/
theorem ex08_nil_ex (f : A ⟶ B) : ¬ Satisfies (QSeq.nil A .ex) f :=
  not_satisfies_nil_ex f

/-- **Ex 9 — §1.395 ∀-STEP with trivial tail**: `(∀, α)·∀` is satisfied by every `h`
    (the universal obligation discharges into the omitted trailing ∀). -/
theorem ex09_forall_vacuous (α : A ⟶ M) (h : A ⟶ B) :
    Satisfies (.cons .all α (.nil M .all)) h := by
  intro g _; exact satisfies_nil_all g

/-- **Ex 10 — §1.395 Theorem 1 (iso-invariance)**: satisfaction of the left-invertible
    Q-sequence is invariant under post-composing the test morphism by an iso `e`. -/
theorem ex10_iso_invariant (f : A ⟶ B) {A' : 𝒟} {e : A ⟶ A'} (he : IsIso e) :
    Satisfies (qLeftInv f) (Cat.id A) ↔ Satisfies (qLeftInv f) (Cat.id A ≫ e) :=
  qLeftInv_iso_invariant f he

end QSeqExamples
end Freyd
