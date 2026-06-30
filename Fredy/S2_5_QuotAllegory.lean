/-
  Freyd & Scedrov, *Categories and Allegories* §2.5  The QUOTIENT ALLEGORY.

  Given a `Congruence C` on an allegory `𝒜` (§2.5), the QUOTIENT ALLEGORY
  `QuotAllegory 𝒜 C` has the SAME objects as `𝒜` and hom-sets the congruence
  classes `Quotient (congSetoid C)`.  Composition, reciprocation and
  intersection descend to classes (`quotient_comp/recip/inter_wellDefined`,
  S2_5), so `QuotAllegory 𝒜 C` is an allegory and the assignment of equivalence
  classes `R ↦ [R]` is a representation of allegories (`quotRep`, an
  `AllegoryFunctor`).  This is the book's

      "the allegory of equivalence classes with the obvious operations
       (which makes the assignment of equivalence classes into a
       representation of allegories)."

  §2.52: if the congruence also respects binary unions, the quotient is a
  DISTRIBUTIVE ALLEGORY and `quotRep` is a representation of distributive
  allegories (`QuotAllegory.instDistributiveAllegory`, `quotRep_map_union`,
  `quotRep_map_zero`).  Zero is the class of `𝟘` — a constant, so it descends
  with NO extra hypothesis: this is the book's "any congruence on a
  distributive allegory respects zero".
-/

import Fredy.S2_5
import Fredy.MapCat   -- `AllegoryFunctor` (the "representation of allegories")

universe v u

namespace Freyd.Alg

/-! ## §2.5  The quotient-allegory type

  A type synonym on `𝒜`'s objects, carrying the congruence `C` in its type so a
  fresh `Cat`/`Allegory` structure (hom = congruence class) can be hung on it
  without colliding with `𝒜`'s own structure. -/

/-- §2.5  The QUOTIENT ALLEGORY `𝒜/C`: same objects as `𝒜`, homs = congruence
    classes.  (Body ignores `_C`; the parameter is carried only to key the
    instances below.) -/
def QuotAllegory (𝒜 : Type u) [Allegory 𝒜] (_C : Congruence 𝒜) : Type u := 𝒜

/-! ## §2.5  Category structure: hom-classes under congruence -/

/-- §2.5  `Cat (𝒜/C)`: `Hom a b = Quotient (congSetoid C)`, identity `[1]`,
    composition the lift of `≫` (well-defined by `quotient_comp_wellDefined`). -/
instance QuotAllegory.instCat {𝒜 : Type u} [Allegory 𝒜] (C : Congruence 𝒜) :
    Cat (QuotAllegory 𝒜 C) where
  Hom a b := Quotient (congSetoid C (a := a) (b := b))
  id a := Quotient.mk (congSetoid C) (@Cat.id 𝒜 _ a)
  comp {a b c} := Quotient.lift₂
    (fun R S => Quotient.mk (congSetoid C) (R ≫ S))
    (fun _ _ _ _ hR hS => Quotient.sound (quotient_comp_wellDefined C hR hS))
  id_comp := by
    intro a b f
    refine Quotient.inductionOn f (fun R => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Cat.id_comp R)
  comp_id := by
    intro a b f
    refine Quotient.inductionOn f (fun R => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Cat.comp_id R)
  assoc := by
    intro a b c d f g h
    refine Quotient.inductionOn₃ f g h (fun R S T => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Cat.assoc R S T)

/-! ## §2.5  Allegory structure: reciprocation and intersection on classes -/

/-- §2.5  `Allegory (𝒜/C)`: `[R]° = [R°]`, `[R] ∩ [S] = [R ∩ S]` (well-defined
    by `quotient_recip/inter_wellDefined`).  Every allegory axiom is the lift of
    `𝒜`'s — proved by inducting on the class representatives down to `𝒜`'s law. -/
instance QuotAllegory.instAllegory {𝒜 : Type u} [Allegory 𝒜] (C : Congruence 𝒜) :
    Allegory (QuotAllegory 𝒜 C) where
  recip {a b} := Quotient.lift
    (fun R => Quotient.mk (congSetoid C) (R°))
    (fun _ _ hR => Quotient.sound (quotient_recip_wellDefined C hR))
  inter {a b} := Quotient.lift₂
    (fun R S => Quotient.mk (congSetoid C) (R ∩ S))
    (fun _ _ _ _ hR hS => Quotient.sound (quotient_inter_wellDefined C hR hS))
  recip_recip := by
    intro a b R
    refine Quotient.inductionOn R (fun r => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.recip_recip r)
  recip_comp := by
    intro a b c R S
    refine Quotient.inductionOn₂ R S (fun r s => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.recip_comp r s)
  recip_inter := by
    intro a b R S
    refine Quotient.inductionOn₂ R S (fun r s => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.recip_inter r s)
  inter_idem := by
    intro a b R
    refine Quotient.inductionOn R (fun r => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.inter_idem r)
  inter_comm := by
    intro a b R S
    refine Quotient.inductionOn₂ R S (fun r s => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.inter_comm r s)
  inter_assoc := by
    intro a b R S T
    refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.inter_assoc r s t)
  semidistrib := by
    intro a b c R S T
    refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.semidistrib r s t)
  modular := by
    intro a b c R S T
    refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
    exact congrArg (Quotient.mk (congSetoid C)) (Allegory.modular r s t)

/-! ## §2.5  The representation `R ↦ [R]` -/

/-- §2.5  The ASSIGNMENT OF EQUIVALENCE CLASSES `R ↦ [R]` as a REPRESENTATION of
    allegories: an `AllegoryFunctor 𝒜 → 𝒜/C`, identity on objects.  All four
    functor laws hold definitionally (`[1] = 1`, `[R≫S] = [R]≫[S]`, etc.). -/
def quotRep {𝒜 : Type u} [Allegory 𝒜] (C : Congruence 𝒜) :
    AllegoryFunctor 𝒜 (QuotAllegory 𝒜 C) where
  obj a := a
  map {a b} R := Quotient.mk (congSetoid C) R
  map_id a := rfl
  map_comp R S := rfl
  map_recip R := rfl
  map_inter R S := rfl

/-- `quotRep` is faithful exactly when `C` is the discrete congruence; in
    general it is the canonical quotient map.  `[R]` of `R` unfolds to the
    class. -/
theorem quotRep_map {𝒜 : Type u} [Allegory 𝒜] (C : Congruence 𝒜) {a b : 𝒜} (R : a ⟶ b) :
    (quotRep C).map R = Quotient.mk (congSetoid C) R := rfl

/-! ## §2.52  Distributive quotient

  If the congruence respects binary unions, the quotient is distributive and
  `quotRep` preserves `∪` and `𝟘`.  The union hypothesis cannot be derived from
  a bare `Congruence` (it is exactly the extra closure the book demands), so it
  is taken as an explicit argument; zero needs none.  Because the union
  hypothesis is not part of `Congruence`, this is delivered as a `def`
  (apply via `letI`/`haveI`), not a global `instance`. -/

/-- §2.52  If `C` respects binary unions, `𝒜/C` is a DISTRIBUTIVE ALLEGORY.
    Zero `= [𝟘]` (a constant: descends with no hypothesis — "any congruence on a
    distributive allegory respects zero"); union `= [R ∪ S]`, well-defined by
    `hunion`.  Every distributive-lattice/zero axiom is the lift of `𝒜`'s. -/
def QuotAllegory.instDistributiveAllegory {𝒜 : Type u} [DistributiveAllegory 𝒜]
    (C : Congruence 𝒜)
    (hunion : ∀ {a b : 𝒜} {R S R' S' : a ⟶ b},
      C.rel R R' → C.rel S S' → C.rel (R ∪ S) (R' ∪ S')) :
    DistributiveAllegory (QuotAllegory 𝒜 C) :=
  { QuotAllegory.instAllegory C with
    zero := fun {a b} => Quotient.mk (congSetoid C) (@DistributiveAllegory.zero 𝒜 _ a b)
    union := fun {a b} => Quotient.lift₂
      (fun R S => Quotient.mk (congSetoid C) (R ∪ S))
      (fun _ _ _ _ hR hS => Quotient.sound (hunion hR hS))
    zero_comp := by
      intro a b c R
      refine Quotient.inductionOn R (fun r => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (@DistributiveAllegory.zero_comp 𝒜 _ a b c r)
    comp_zero := by
      intro a b c R
      refine Quotient.inductionOn R (fun r => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (@DistributiveAllegory.comp_zero 𝒜 _ a b c r)
    union_idem := by
      intro a b R
      refine Quotient.inductionOn R (fun r => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.union_idem r)
    union_comm := by
      intro a b R S
      refine Quotient.inductionOn₂ R S (fun r s => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.union_comm r s)
    union_assoc := by
      intro a b R S T
      refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.union_assoc r s t)
    union_inter_absorb := by
      intro a b R S
      refine Quotient.inductionOn₂ R S (fun r s => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.union_inter_absorb r s)
    inter_union_absorb := by
      intro a b R S
      refine Quotient.inductionOn₂ R S (fun r s => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.inter_union_absorb r s)
    comp_union_distrib := by
      intro a b c R S T
      refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.comp_union_distrib r s t)
    inter_union_distrib := by
      intro a b R S T
      refine Quotient.inductionOn₃ R S T (fun r s t => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.inter_union_distrib r s t)
    zero_union := by
      intro a b R
      refine Quotient.inductionOn R (fun r => ?_)
      exact congrArg (Quotient.mk (congSetoid C)) (DistributiveAllegory.zero_union r) }

/-- §2.52  `quotRep` preserves binary unions (it is a representation of
    distributive allegories), against the distributive structure of
    `QuotAllegory.instDistributiveAllegory`. -/
theorem quotRep_map_union {𝒜 : Type u} [DistributiveAllegory 𝒜] (C : Congruence 𝒜)
    (hunion : ∀ {a b : 𝒜} {R S R' S' : a ⟶ b},
      C.rel R R' → C.rel S S' → C.rel (R ∪ S) (R' ∪ S'))
    {a b : 𝒜} (R S : a ⟶ b) :
    letI := QuotAllegory.instDistributiveAllegory C hunion
    (quotRep C).map (R ∪ S) = (quotRep C).map R ∪ (quotRep C).map S := rfl

/-- §2.52  `quotRep` preserves zero. -/
theorem quotRep_map_zero {𝒜 : Type u} [DistributiveAllegory 𝒜] (C : Congruence 𝒜)
    (hunion : ∀ {a b : 𝒜} {R S R' S' : a ⟶ b},
      C.rel R R' → C.rel S S' → C.rel (R ∪ S) (R' ∪ S'))
    {a b : 𝒜} :
    letI := QuotAllegory.instDistributiveAllegory C hunion
    (quotRep C).map (𝟘 : a ⟶ b) = (𝟘 : (quotRep C).obj a ⟶ (quotRep C).obj b) := rfl

end Freyd.Alg
