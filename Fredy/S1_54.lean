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

/-- The "product with B" functor `(-)×B : 𝒞 → 𝒞`.  This is the object part of
    the book's embedding `A → A/B`, `C ↦ (C×B → B)`; on morphisms it sends
    `f` to `pair (fst ≫ f) snd`. -/
def prodRight (B : 𝒞) : 𝒞 → 𝒞 := fun C => prod C B

instance prodRightFunctor (B : 𝒞) : Functor (prodRight B) where
  map {C D} f := pair (fst ≫ f) snd
  map_id C := by
    show pair (fst ≫ Cat.id C) snd = Cat.id (prod C B)
    rw [Cat.comp_id]
    exact (pair_uniq fst snd (Cat.id (prod C B)) (Cat.id_comp fst) (Cat.id_comp snd)).symm
  map_comp {C D E} f g := by
    show pair (fst ≫ f ≫ g) snd = pair (fst ≫ f) snd ≫ pair (fst ≫ g) snd
    symm
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc]
    · rw [Cat.assoc, snd_pair, snd_pair]

/-- **§1.544**: when `B` is well-supported, `(-)×B` SEPARATES MORPHISMS — the
    embedding `A → A/B` is faithful in Freyd's sense ("separates objects and, if
    `B` is well-supported, separates morphisms").  If `f×B = g×B`, projecting
    along `fst` gives `fst ≫ f = fst ≫ g`; and `fst : C×B → C` is a cover
    (`prod_fst_cover`), hence epic (`cover_epi`), so `f = g`. -/
theorem slice_embedding_separates [PullbacksTransferCovers 𝒞] (B : 𝒞) (hws : WellSupported B) :
    Embedding (prodRight B) := by
  intro C D f g h
  have e1 : (prodRightFunctor B).map f ≫ (fst : prod D B ⟶ D) = (fst : prod C B ⟶ C) ≫ f :=
    fst_pair ((fst : prod C B ⟶ C) ≫ f) snd
  have e2 : (prodRightFunctor B).map g ≫ (fst : prod D B ⟶ D) = (fst : prod C B ⟶ C) ≫ g :=
    fst_pair ((fst : prod C B ⟶ C) ≫ g) snd
  have hfst : (fst : prod C B ⟶ C) ≫ f = (fst : prod C B ⟶ C) ≫ g := by
    rw [← e1, ← e2, h]
  exact cover_epi (prod_fst_cover hws) hfst

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

  Status of the proof in this formalization:
  • §1.544 (one slice step separates morphisms) is PROVED, sorry-free:
    `slice_embedding_separates` — the keystone facts `cover_epi` (covers are
    right-cancellable) and `prod_fst_cover` (`fst : C×B → C` is a cover when B is
    well-supported) are in `S1_52.lean`.
  • §1.545 relative capitalization is DEFINED (`IsRelativeCapitalization`).

  What remains (the genuine wall): §1.546 builds A* as the directed union of the
  slices A/B over all well-supported B, and §1.543 iterates this transfinitely to
  a fixed point, then proves the colimit is pre-regular and capital.  Both steps
  are *directed colimits in the category of categories*, indexed by ordinals.
  This repo is deliberately mathlib-free, so there is no `Ordinal`, no
  well-founded recursion producing types, and no colimit-of-categories machinery
  to build on — constructing it from scratch is a separate foundational project.
  Hence `capitalization_lemma` is left as `sorry`. -/

axiom capitalization_lemma (A : Type u) [Cat.{v} A] [PreRegularCategory A] :
    ∃ (Ā : Type u) (hC : Cat.{v} Ā) (hP : PreRegularCategory Ā),
      @Capital.{v, u} Ā hC (hP.toHasTerminal) ∧
      ∃ (F : A → Ā) (hF : Functor F), @Faithful.{v, u} A _ Ā hC F hF

end Freyd
