/-
  Freyd & Scedrov, *Categories and Allegories* — internal disjunction `∨ : Ω×Ω → Ω`,
  the direct image `∃_f`, and (toward) binary coproducts, in a topos.

  Built on top of the now-available sorry-free topos primitives:
    * `HasImages 𝒞`              (`InternalForallTopos.toposHasImages`)
    * `HasSubobjectUnions 𝒞`     (`ToposColimits.toposHasSubobjectUnions`)
    * the subobject classifier `Sub(A) ≅ Hom(A,Ω)` (`S1_91`: `subChar`, `classify_surjective`,
      `le_iff_classify`, `classify_eq_of_le_le`, `classify_invImg`).

  GOAL 1  internal disjunction `orChar : Ω×Ω → Ω` as `χ_{Sfst ∪ Ssnd}`, where
          `Sfst = fst#(true-sub)` and `Ssnd = snd#(true-sub)` are the two "coordinate true"
          subobjects of `Ω×Ω`.  Its lattice UMP is recorded below.

  GOAL 2  direct image `∃_f S := image (S.arr ≫ f)` for `f : A → B`, `S ⊆ A`, with the
          Galois adjunction `∃_f S ≤ T ↔ S ≤ f# T`.
-/

import Fredy.S1_91
import Fredy.S1_92
import Fredy.S1_45
import Fredy.S1_60
import Fredy.InterIntersection
import Fredy.InternalForallTopos
import Fredy.ToposColimits

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-- Transitivity of the subobject order (local copy; avoids importing the heavy
    `Complement` tower). -/
theorem subLe_trans' {W : 𝒞} {X Y Z : Subobject 𝒞 W} (h₁ : X.le Y) (h₂ : Y.le Z) : X.le Z := by
  obtain ⟨f, hf⟩ := h₁; obtain ⟨g, hg⟩ := h₂
  exact ⟨f ≫ g, by rw [Cat.assoc, hg, hf]⟩

/-! ## Subobject ↔ classifier glue

  Every `χ : A → Ω` is `subChar` of *some* subobject (the pullback of `true` along `χ`).
  We package this choice as `subOfChar χ` with `subChar (subOfChar χ) = χ`, the workhorse
  for naming subobjects by their characteristic map. -/

/-- The subobject of `A` classified by `χ` (pullback of `true` along `χ`). -/
noncomputable def subOfChar {A : 𝒞} (χ : A ⟶ omega (𝒞 := 𝒞)) : Subobject 𝒞 A :=
  ⟨(classify_surjective χ).choose,
   (classify_surjective χ).choose_spec.choose,
   (classify_surjective χ).choose_spec.choose_spec.choose⟩

@[simp] theorem subChar_subOfChar {A : 𝒞} (χ : A ⟶ omega (𝒞 := 𝒞)) :
    subChar (subOfChar χ) = χ :=
  (classify_surjective χ).choose_spec.choose_spec.choose_spec

/-- A subobject equals (as `le` both ways) the subobject named by its own classifier — and
    more usefully: two subobjects with the same classifier are mutually `≤`. -/
theorem le_le_of_subChar_eq {A : 𝒞} {S T : Subobject 𝒞 A}
    (h : subChar S = subChar T) : S.le T ∧ T.le S := by
  constructor
  · rw [le_iff_classify]
    have : subChar S = subChar T := h
    show S.arr ≫ subChar T = _
    rw [← h]; exact (classify_sq S.arr S.monic)
  · rw [le_iff_classify]
    show T.arr ≫ subChar S = _
    rw [h]; exact (classify_sq T.arr T.monic)

/-! ## GOAL 1 — Internal disjunction `∨ : Ω×Ω → Ω` -/

/-- The "first coordinate is true" subobject of `Ω×Ω`: classified by `fst`. -/
noncomputable def trueFst : Subobject 𝒞 (prod (omega (𝒞 := 𝒞)) (omega (𝒞 := 𝒞))) :=
  subOfChar fst

/-- The "second coordinate is true" subobject of `Ω×Ω`: classified by `snd`. -/
noncomputable def trueSnd : Subobject 𝒞 (prod (omega (𝒞 := 𝒞)) (omega (𝒞 := 𝒞))) :=
  subOfChar snd

@[simp] theorem subChar_trueFst :
    subChar (trueFst (𝒞 := 𝒞)) = fst := subChar_subOfChar _
@[simp] theorem subChar_trueSnd :
    subChar (trueSnd (𝒞 := 𝒞)) = snd := subChar_subOfChar _

/-- **Internal disjunction** `∨ : Ω×Ω → Ω`: the classifier of the union of the two
    coordinate-true subobjects `{(⊤,·)} ∪ {(·,⊤)}` of `Ω×Ω`. -/
noncomputable def orChar : prod (omega (𝒞 := 𝒞)) (omega (𝒞 := 𝒞)) ⟶ omega (𝒞 := 𝒞) :=
  subChar (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) (trueSnd (𝒞 := 𝒞)))

/-! ## GOAL 2 — Direct image `∃_f` and the adjunction `∃_f ⊣ f#` -/

/-- **Direct image** `∃_f S ⊆ B` of a subobject `S ⊆ A` along `f : A → B`: the image of the
    composite `S ↣ A → B`. -/
noncomputable def directImage {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) : Subobject 𝒞 B :=
  image (S.arr ≫ f)

/-- `S ≤ f# (∃_f S)`: the unit of the adjunction.  `S.arr ≫ f` factors through its own image. -/
theorem directImage_unit {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A)
    (hp : HasPullback f (directImage f S).arr) :
    S.le (invImg f (directImage f S) hp) := by
  -- S.arr ≫ f factors through directImage; lift it into the pullback f# (∃_f S).
  obtain ⟨u, hu⟩ := image_allows (S.arr ≫ f)
  -- the cone (S.dom, S.arr, u) over (f, (∃_f S).arr) commutes: S.arr ≫ f = u ≫ (∃_f S).arr.
  refine ⟨hp.lift ⟨S.dom, S.arr, u, hu.symm⟩, ?_⟩
  exact hp.lift_fst _

/-- The **Galois adjunction** `∃_f ⊣ f#`: `∃_f S ≤ T ↔ S ≤ f# T`. -/
theorem directImage_adjunction {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) (T : Subobject 𝒞 B)
    (hp : HasPullback f T.arr) :
    (directImage f S).le T ↔ S.le (invImg f T hp) := by
  constructor
  · -- ∃_f S ≤ T : compose S ≤ f#(∃_f S) ≤ f# T (inverse image monotone).
    intro hle
    have hpI : HasPullback f (directImage f S).arr := HasPullbacks.has _ _
    exact subLe_trans' (directImage_unit f S hpI) (invImg_le f (directImage f S) T hpI hp hle)
  · -- S ≤ f# T : then S.arr ≫ f factors through T, so T is an upper bound — image is minimal.
    intro hle
    -- f# T allows S.arr (S ≤ f# T), and (f# T).arr ≫ f factors through T via π₂.
    obtain ⟨k, hk⟩ := hle           -- k ≫ (f#T).arr = S.arr
    -- T allows S.arr ≫ f : via k ≫ π₂ (the second pullback leg lands in T).
    refine image_min (S.arr ≫ f) T ?_
    refine ⟨k ≫ hp.cone.π₂, ?_⟩
    -- (k ≫ π₂) ≫ T.arr = k ≫ (π₁ ≫ f) = (k ≫ π₁) ≫ f = S.arr ≫ f.
    -- `(invImg f T hp).arr` is definitionally `hp.cone.π₁`, so `hk : k ≫ π₁ = S.arr`.
    have hk' : k ≫ hp.cone.π₁ = S.arr := hk
    rw [Cat.assoc, ← hp.cone.w, ← Cat.assoc, hk']

end Freyd
