/-
  Freyd & Scedrov, *Categories and Allegories* §1.94 — the INTERNAL UNIVERSAL
  QUANTIFIER `∀_C` for a topos, and the FAMILY-GLB / IMAGE it produces.

  ## What this file builds (the §1.945 cascade root)

  S1_94's `interIntersection F_name : 1 → [A] ⊢ Subobject A` is only the glb of the
  SINGLETON family named by one global element.  This file builds the genuine internal
  universal quantifier and from it the family-glb that `S1_94` flags as missing.

  ### The internal-∀ as "name of the top element"

  Let `topC : 1 → [C]` be the NAME of the entire subobject `(entire C)` — i.e.
  `nameOf id`.  Concretely `membershipMap topC = χ_{entire C} = true ∘ term`, so a point
  `c : 1 → C` always lies in `topC` (the entire subobject contains everything).

  Define `forallC : [C] → Ω` as the classifier of the singleton subobject `{topC} ↣ [C]`.
  Then for any `σ : X → [C]`, `σ ≫ forallC` is `true` (on points) iff `σ = topC`, i.e. iff
  the subobject named by `σ` is the entire one — iff `∀c. c ∈ σ`.  This is exactly the
  internal-∀ over `C`.

  The β-law `forall_beta` records: `σ ≫ forallC = true ∘ term`  ↔  `σ = topC ∘ term`.

  ### The family-glb

  Given a "comprehension" predicate on subobjects presented as a global name plus a test,
  the family-glb `⋂{B' | P(B')}` is `interIntersection` of the ∀-closure name.  We expose
  the two genuine topos primitives this unlocks:

  *  `HasLeastClosedSubobject 𝒞`  (the §1.987 least `(a,t)`-closed subobject), and
  *  `HasImages 𝒞`  (every `f : A → B` has an image), hence `topos_is_regular`.
-/

import Fredy.S1_94
import Fredy.InternalForall

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.94  The internal universal quantifier `∀_C` -/

/-- The NAME of the entire subobject `(entire C) : 1 → [C]`, the internal "top element"
    `⊤_C` of the power object.  `topName C = nameOf id_C`. -/
noncomputable def topName (C : 𝒞) : one ⟶ powObj C :=
  nameOf (Subobject.entire C).arr (Subobject.entire C).monic

/-- The membership test of `topName C` is `χ_{entire C}`: every point lies in `⊤_C`. -/
theorem membershipMap_topName (C : 𝒞) :
    membershipMap (topName C)
      = HasSubobjectClassifier.classify (Subobject.entire C).arr (Subobject.entire C).monic := by
  rw [topName, membershipMap_nameOf]

/-! ### The singleton subobject `{σ}` of `[C]` named by a global element `σ` -/

/-- The NAME `1 → [[C]]` of the singleton subobject `{σ}` of `[C]`, for a global element
    `σ : 1 → [C]`.  It is `σ ≫ singletonMap [C]`, where `singletonMap [C] : [C] → [[C]]`
    is the §1.92 singleton map (curry of the diagonal classifier). -/
noncomputable def singletonName (C : 𝒞) (σ : one ⟶ powObj C) : one ⟶ powObj (powObj C) :=
  σ ≫ singletonMap (powObj C)

/-- **Singleton membership computation.**  The membership test of the singleton-subobject
    name `σ ≫ singletonMap E` (for a global element `σ : 1 → E`) is
    `⟨id, term ≫ σ⟩ ≫ χ_Δ`, the map `E → Ω` that tests `x = σ`.

    Proof mirrors `membershipMap_nameOf`: `σ ≫ singletonMap E = curry(prodMap σ ≫ χ_Δ)`
    by `curry_precomp`; then `curry_eval_eq` collapses the `prodMap … ≫ eval`, and a
    `pair_uniq` recombines `⟨id, term⟩ ≫ prodMap σ = ⟨id, term ≫ σ⟩`. -/
theorem membershipMap_singletonMap (E : 𝒞) (σ : one ⟶ E) :
    membershipMap (σ ≫ singletonMap E)
      = pair (Cat.id E) (term E ≫ σ) ≫ HasSubobjectClassifier.classify (diag E) (diag_mono E) := by
  show pair (Cat.id E) (term E ≫ σ ≫ singletonMap E) ≫ eval_exp E (omega (𝒞 := 𝒞)) = _
  have hN : σ ≫ singletonMap E
      = curry (prodMap E one E σ ≫ HasSubobjectClassifier.classify (diag E) (diag_mono E)) := by
    rw [singletonMap, singletonMapCat, curry_precomp]
  rw [hN]
  have hfactor : pair (Cat.id E)
        (term E ≫ curry (prodMap E one E σ ≫ HasSubobjectClassifier.classify (diag E) (diag_mono E)))
      = pair (Cat.id E) (term E) ≫ prodMap E one (omega (𝒞 := 𝒞) ^^ E)
          (curry (prodMap E one E σ ≫ HasSubobjectClassifier.classify (diag E) (diag_mono E))) :=
    (pair_uniq _ _ _ (by rw [Cat.assoc, prodMap_fst, fst_pair])
      (by rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair])).symm
  rw [hfactor, Cat.assoc, curry_eval_eq, ← Cat.assoc]
  congr 1
  apply pair_uniq
  · rw [Cat.assoc, prodMap_fst, fst_pair]
  · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair]

/-- **Diagonal classifier as internal equality.**  `⟨a,b⟩ ≫ χ_Δ = ⊤∘!` iff `a = b`.
    Forward: the classifier pullback of `Δ` lifts `⟨a,b⟩` through `Δ`, forcing `a = b`
    via the two projections.  Backward: `a = b` makes `⟨a,a⟩ = a ≫ Δ`, and `Δ ≫ χ_Δ = ⊤∘!`. -/
theorem diag_classify_iff {E X : 𝒞} (a b : X ⟶ E) :
    pair a b ≫ HasSubobjectClassifier.classify (diag E) (diag_mono E)
        = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) ↔ a = b := by
  constructor
  · intro h
    obtain ⟨u, ⟨hu₁, _⟩, _⟩ := HasSubobjectClassifier.classify_pullback (diag E) (diag_mono E)
      ⟨X, pair a b, term X, h⟩
    have ha : a = u := by
      have := congrArg (· ≫ fst) hu₁
      simpa [Cat.assoc, diag_fst, Cat.comp_id, fst_pair] using this.symm
    have hb : b = u := by
      have := congrArg (· ≫ snd) hu₁
      simpa [Cat.assoc, diag_snd, Cat.comp_id, snd_pair] using this.symm
    rw [ha, hb]
  · intro h
    subst h
    have hpa : a ≫ diag E = pair a a := by
      apply pair_uniq <;> rw [Cat.assoc] <;> simp [diag_fst, diag_snd, Cat.comp_id]
    rw [← hpa, Cat.assoc, HasSubobjectClassifier.classify_sq, ← Cat.assoc]
    congr 1
    exact term_uniq _ _

/-- The internal universal quantifier `∀_C : [C] → Ω`: the membership test of the
    singleton subobject `{topName C}` of `[C]`.  On a global element `σ : 1 → [C]`,
    `σ ≫ forallC` is `true` iff `σ = topName C`, i.e. iff the subobject named by `σ`
    is the entire one (`∀ c. c ∈ σ`). -/
noncomputable def forallC (C : 𝒞) : powObj C ⟶ omega (𝒞 := 𝒞) :=
  membershipMap (singletonName C (topName C))

/-- `forallC C` unfolds (via `membershipMap_singletonMap`) to `⟨id, term ≫ topName C⟩ ≫ χ_Δ`
    on `[C]`. -/
theorem forallC_eq (C : 𝒞) :
    forallC C = pair (Cat.id (powObj C)) (term (powObj C) ≫ topName C)
      ≫ HasSubobjectClassifier.classify (diag (powObj C)) (diag_mono (powObj C)) := by
  rw [forallC, singletonName, membershipMap_singletonMap]

/-- Evaluating `forallC` at a generalized point `σ : X → [C]` gives
    `⟨σ, term X ≫ topName C⟩ ≫ χ_Δ`. -/
theorem comp_forallC {X : 𝒞} (C : 𝒞) (σ : X ⟶ powObj C) :
    σ ≫ forallC C = pair σ (term X ≫ topName C)
      ≫ HasSubobjectClassifier.classify (diag (powObj C)) (diag_mono (powObj C)) := by
  rw [forallC_eq, ← Cat.assoc]
  congr 1
  apply pair_uniq
  · rw [Cat.assoc, fst_pair, Cat.comp_id]
  · rw [Cat.assoc, snd_pair, ← Cat.assoc, term_uniq (σ ≫ term (powObj C)) (term X)]

/-- **§1.94 — β-law of the internal-∀ (generalized points).**  For `σ : X → [C]`,
    `σ ≫ forallC C = ⊤∘!_X` iff `σ = term X ≫ topName C`, i.e. iff the `X`-indexed
    subobject named by `σ` is constantly the entire one (`∀ c : C, c ∈ σ`). -/
theorem forall_beta {X : 𝒞} (C : 𝒞) (σ : X ⟶ powObj C) :
    σ ≫ forallC C = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
      ↔ σ = term X ≫ topName C := by
  rw [comp_forallC]; exact diag_classify_iff σ (term X ≫ topName C)

/-! ## §1.94  The family big-intersection `⋂F` via the internal-∀

  Given a subobject FAMILY `F ↣ [A]` presented by its name `Fname : 1 → [[A]]`, the
  big-intersection `⋂F : Subobject A` has characteristic map

      χ_{⋂F}(a)  =  ∀ σ : [A].  (σ ∈ F) ⇒ (a ∈ σ).

  The quantified body `body(σ, a) = (σ∈F) ⇒ (a∈σ)` is a map `[A] × A → Ω`; currying in
  the σ-slot gives `A → Ω^[A] = [[A]]`, and post-composing with `forallC [A]` performs
  the universal quantification over `σ` (the §1.94 trick: `forall_beta` reads
  `∀σ. P(σ)` as "the subobject `{σ | P}` of `[A]` is the entire one").

  This realises the genuine fibered internal-∀ `∀_[A] : Ω^([A]×A) → Ω^A` as
  `curry(−) ≫ forallC [A]`, the parameter `a` being absorbed by `curry`. -/

/-- The implication map on `Ω`, `impΩ = ⟨π₁, π₁ ∧ π₂⟩ ≫ ⇔` (Freyd's `x⇒y := x ⇔ (x∧y)`,
    the §1.91 `impChar` recipe at the level of `Ω×Ω`). -/
noncomputable def impΩ : prod (omega (𝒞 := 𝒞)) (omega (𝒞 := 𝒞)) ⟶ omega (𝒞 := 𝒞) :=
  pair fst (pair fst snd ≫ omegaMeet) ≫ heytingDoubleArrow

/-- The big-intersection body `[A]×A → Ω`: `(σ∈F) ⇒ (a∈σ)`.  `σ∈F` is
    `fst ≫ membershipMap Fname`; `a∈σ` is `⟨a,σ⟩ ≫ eval = ⟨snd,fst⟩ ≫ eval`. -/
noncomputable def bigInterBody {A : 𝒞} (Fname : one ⟶ powObj (powObj A)) :
    prod (powObj A) A ⟶ omega (𝒞 := 𝒞) :=
  pair (fst ≫ membershipMap Fname) (pair snd fst ≫ eval_exp A (omega (𝒞 := 𝒞))) ≫ impΩ

/-- The characteristic map `A → Ω` of `⋂F`: curry the body in the `[A]`-slot, then
    universally quantify with `forallC [A]`. -/
noncomputable def bigInterChar {A : 𝒞} (Fname : one ⟶ powObj (powObj A)) :
    A ⟶ omega (𝒞 := 𝒞) :=
  curry (bigInterBody Fname) ≫ forallC (powObj A)

/-- **§1.94 — the internal family big-intersection `⋂F`** for a family `F ↣ [A]` named
    by `Fname : 1 → [[A]]`.  It is the pullback of `true` along `bigInterChar Fname`. -/
noncomputable def bigInter {A : 𝒞} (Fname : one ⟶ powObj (powObj A)) : Subobject 𝒞 A :=
  InverseImage (bigInterChar Fname) ⟨one, true (𝒞 := 𝒞), true_monic⟩

end Freyd
