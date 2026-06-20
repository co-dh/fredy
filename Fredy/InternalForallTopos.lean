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

/-- The classifier of the entire subobject (`arr = id`) is `⊤∘!`.  From `classify_sq id`. -/
theorem classify_entire (C : 𝒞) :
    HasSubobjectClassifier.classify (Subobject.entire C).arr (Subobject.entire C).monic
      = term C ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  have h := HasSubobjectClassifier.classify_sq (Subobject.entire C).arr (Subobject.entire C).monic
  -- (entire C).arr = id_C, so id ≫ classify = classify, and term (entire).dom = term C.
  simpa [Subobject.entire, Cat.id_comp] using h

/-- **∀-elimination.**  If `g : X → [C]` is "constantly the entire subobject"
    (`g = term X ≫ topName C`, the conclusion of `forall_beta`), then EVERY generalized
    point `τ : X → C` lies in `g`: `⟨τ, g⟩ ≫ eval = ⊤∘!_X`.  (The entire subobject
    contains every point.) -/
theorem forall_elim {X C : 𝒞} (g : X ⟶ powObj C) (hg : g = term X ≫ topName C)
    (τ : X ⟶ C) :
    pair τ g ≫ eval_exp C (omega (𝒞 := 𝒞)) = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  -- ⟨τ, term X ≫ topName C⟩ ≫ eval = τ ≫ membershipMap (topName C) = τ ≫ (term C ≫ ⊤) = ⊤∘!.
  have hτ : pair τ (term X ≫ topName C) ≫ eval_exp C (omega (𝒞 := 𝒞))
      = τ ≫ membershipMap (topName C) := by
    rw [membershipMap, ← Cat.assoc]
    congr 1
    symm
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, Cat.comp_id]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, term_uniq (τ ≫ term C) (term X)]
  rw [hg, hτ, membershipMap_topName, classify_entire, ← Cat.assoc, term_uniq (τ ≫ term C) (term X)]

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

/-- `⟨χ₁,χ₂⟩ ≫ impΩ = ⟨χ₁, χ₁∧χ₂⟩ ≫ ⇔` — the `impΩ` recipe spelled out (matches `impChar`). -/
theorem pair_impΩ {X : 𝒞} (χ₁ χ₂ : X ⟶ omega (𝒞 := 𝒞)) :
    pair χ₁ χ₂ ≫ impΩ
      = pair χ₁ (pair χ₁ χ₂ ≫ omegaMeet) ≫ heytingDoubleArrow := by
  rw [impΩ, ← Cat.assoc]
  congr 1
  apply pair_uniq
  · rw [Cat.assoc, fst_pair, fst_pair]
  · rw [Cat.assoc, snd_pair, ← Cat.assoc, pair_fst_snd, Cat.comp_id]

/-- **impΩ forward (modus ponens).**  If `⟨χ₁,χ₂⟩ ≫ impΩ` is true along `k` and `χ₁`
    is true along `k`, then `χ₂` is true along `k`.  (Only the forward/MP half of `⇒`
    is a clean pointwise fact; the converse needs Ω-extensionality.) -/
theorem impΩ_forward {X W : 𝒞} (χ₁ χ₂ : X ⟶ omega (𝒞 := 𝒞)) (k : W ⟶ X)
    (himp : k ≫ (pair χ₁ χ₂ ≫ impΩ) = term W ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
    (h1 : k ≫ χ₁ = term W ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    k ≫ χ₂ = term W ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  -- impΩ = ⟨π₁, π₁∧π₂⟩ ≫ ⇔; along k this is ⟨χ₁, χ₁∧χ₂⟩ ≫ ⇔ = ⊤, so χ₁ = χ₁∧χ₂ along k.
  rw [pair_impΩ] at himp
  -- heyting_true_iff_eq: along k, χ₁ = (χ₁∧χ₂).
  have heq := (heyting_true_iff_eq χ₁ (pair χ₁ χ₂ ≫ omegaMeet) k).mp himp
  -- so k ≫ (χ₁∧χ₂) = k ≫ χ₁ = ⊤, then meet_true_iff_and gives k ≫ χ₂ = ⊤.
  have hmeet : k ≫ (pair χ₁ χ₂ ≫ omegaMeet) = term W ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    rw [← heq]; exact h1
  exact ((meet_true_iff_and χ₁ χ₂ k).mp hmeet).2

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

/-- **Uncurry-at-a-point bridge.**  For `h : prod E A → Ω`, `τ : K → E`, `c : K → A`,
    `⟨τ, c ≫ curry h⟩ ≫ eval = ⟨τ, c⟩ ≫ h`.  (Evaluating the curried `h` at the point
    `c` and pairing with `τ` reconstructs `h(τ,c)`.) -/
theorem eval_curry_point {E A K : 𝒞} (h : prod E A ⟶ omega (𝒞 := 𝒞))
    (τ : K ⟶ E) (c : K ⟶ A) :
    pair τ (c ≫ curry h) ≫ eval_exp E (omega (𝒞 := 𝒞)) = pair τ c ≫ h := by
  have hpm : pair τ (c ≫ curry h)
      = pair τ c ≫ prodMap E A (omega (𝒞 := 𝒞) ^^ E) (curry h) := by
    symm
    apply pair_uniq
    · rw [Cat.assoc, prodMap_fst, fst_pair]
    · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair]
  rw [hpm, Cat.assoc, curry_eval_eq]

/-- **§1.94 — the internal family big-intersection `⋂F`** for a family `F ↣ [A]` named
    by `Fname : 1 → [[A]]`.  It is the pullback of `true` along `bigInterChar Fname`. -/
noncomputable def bigInter {A : 𝒞} (Fname : one ⟶ powObj (powObj A)) : Subobject 𝒞 A :=
  InverseImage (bigInterChar Fname) ⟨one, true (𝒞 := 𝒞), true_monic⟩

/-- **`InverseImage χ {true}` is classified by `χ`.**  General form of
    `classify_interIntersection`: the pullback of `true` along any `χ : A → Ω` has `χ`
    as its characteristic map. -/
theorem classify_invImage_true {A : 𝒞} (χ : A ⟶ omega (𝒞 := 𝒞)) :
    HasSubobjectClassifier.classify
        (InverseImage χ ⟨one, true (𝒞 := 𝒞), true_monic⟩).arr
        (InverseImage χ ⟨one, true (𝒞 := 𝒞), true_monic⟩).monic = χ := by
  symm
  let pb := HasPullbacks.has χ (HasSubobjectClassifier.true (𝒞 := 𝒞))
  have hsq : (InverseImage χ ⟨one, true (𝒞 := 𝒞), true_monic⟩).arr ≫ χ
      = term (InverseImage χ ⟨one, true (𝒞 := 𝒞), true_monic⟩).dom
        ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    show pb.cone.π₁ ≫ χ = _
    rw [pb.cone.w]; congr 1; exact term_uniq _ _
  apply classify_eq_of_pullback _ _ χ hsq
  intro d
  obtain ⟨u, ⟨hu₁, _⟩, huniq⟩ := pb.cone_isPullback d
  exact ⟨u, ⟨hu₁, term_uniq _ _⟩, fun v hv₁ _ => huniq v hv₁ (term_uniq _ _)⟩

/-- `Allows (bigInter F) a ↔ a ≫ bigInterChar F = ⊤∘!`.  (`bigInter` is the pullback of
    `true` along `bigInterChar`, classified by it; then `allows_iff_classify`.) -/
theorem allows_bigInter_iff {A : 𝒞} (Fname : one ⟶ powObj (powObj A)) (a : one ⟶ A) :
    Allows (bigInter Fname) a
      ↔ a ≫ bigInterChar Fname = term one ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [allows_iff_classify (bigInter Fname) a]
  rw [show HasSubobjectClassifier.classify (bigInter Fname).arr (bigInter Fname).monic
        = bigInterChar Fname from classify_invImage_true (bigInterChar Fname)]

/-- The carrier of `⋂F` satisfies its characteristic map: `(⋂F).arr ≫ bigInterChar F = ⊤∘!`. -/
theorem bigInter_carrier_true {A : 𝒞} (Fname : one ⟶ powObj (powObj A)) :
    (bigInter Fname).arr ≫ bigInterChar Fname
      = term (bigInter Fname).dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  show (HasPullbacks.has (bigInterChar Fname) (HasSubobjectClassifier.true (𝒞 := 𝒞))).cone.π₁
      ≫ bigInterChar Fname = _
  rw [(HasPullbacks.has (bigInterChar Fname) (HasSubobjectClassifier.true (𝒞 := 𝒞))).cone.w]
  congr 1
  exact term_uniq _ _

/-- **Body-at-a-point.**  The membership map of the name `a ≫ curry h` (the `[A]`-indexed
    subobject `{σ | h(σ,a)}`) is `⟨id, term ≫ a⟩ ≫ h`, i.e. `h` with its `A`-slot fixed to `a`.
    Infrastructure for the (still-open) `bigInter` UPPER bound via `imp_adjunction`. -/
theorem membershipMap_curry_point {A : 𝒞} (h : prod (powObj A) A ⟶ omega (𝒞 := 𝒞))
    (a : one ⟶ A) :
    membershipMap (a ≫ curry h)
      = pair (Cat.id (powObj A)) (term (powObj A) ≫ a) ≫ h := by
  show pair (Cat.id (powObj A)) (term (powObj A) ≫ a ≫ curry h)
      ≫ eval_exp (powObj A) (omega (𝒞 := 𝒞)) = _
  rw [← eval_curry_point h (Cat.id (powObj A)) (term (powObj A) ≫ a)]
  congr 1
  rw [Cat.assoc]

/-- **§1.94 — `⋂F` is a lower bound (∀-elimination).**  For any `B ↣ A` whose name
    `'B' = nameOf B.arr` is a MEMBER of the family (`'B' ≫ χ_F = ⊤∘!`, i.e. `'B' ∈ F`),
    the big-intersection `⋂F` lies below `B`.

    Proof: the carrier `c = (⋂F).arr` satisfies `c ≫ χ_{⋂F} = ⊤`, so by `forall_beta`
    the `[A]`-indexed subobject `c ≫ curry body` is constantly entire; `forall_elim` at
    the constant point `τ = term ≫ 'B'` makes `body(τ,c) = ⊤` (i.e. `(τ∈F)⇒(c∈τ)` true);
    modus ponens (`impΩ_forward`) with `τ∈F = ⊤` (hypothesis) yields `c ∈ 'B' = ⊤`, which
    is exactly `c` factoring through `B` (`'B' = nameOf B.arr`, β-law `membershipMap_nameOf`). -/
theorem bigInter_le_named {A : 𝒞} (Fname : one ⟶ powObj (powObj A))
    (B : Subobject 𝒞 A)
    (hB : nameOf B.arr B.monic ≫ membershipMap Fname
        = term one ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    (bigInter Fname).le B := by
  let K := (bigInter Fname).dom
  let c := (bigInter Fname).arr
  -- Step 1: c ≫ curry body = term K ≫ topName [A]   (forall_beta on c ≫ bigInterChar)
  have hcar := bigInter_carrier_true Fname
  rw [bigInterChar, ← Cat.assoc] at hcar
  have hentire : c ≫ curry (bigInterBody Fname) = term K ≫ topName (powObj A) :=
    (forall_beta (powObj A) (c ≫ curry (bigInterBody Fname))).mp hcar
  -- Step 2: instantiate forall_elim at τ = term K ≫ nameOf B.arr to get body(τ,c) = ⊤.
  let τ : K ⟶ powObj A := term K ≫ nameOf B.arr B.monic
  have hbodyτ : pair τ c ≫ bigInterBody Fname
      = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    rw [← eval_curry_point (bigInterBody Fname) τ c]
    exact forall_elim _ hentire τ
  -- Step 3: unfold body = ⟨σ∈F, c∈σ⟩ ≫ impΩ; modus ponens needs τ∈F = ⊤ and yields c∈τ = ⊤.
  -- pair τ c ≫ bigInterBody = pair (pair τ c ≫ (fst≫memF)) (pair τ c ≫ (⟨snd,fst⟩≫eval)) ≫ impΩ.
  have hmemF : pair τ c ≫ (fst ≫ membershipMap Fname)
      = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    show pair τ c ≫ (fst ≫ membershipMap Fname) = _
    rw [← Cat.assoc, fst_pair]
    show (term K ≫ nameOf B.arr B.monic) ≫ membershipMap Fname = _
    rw [Cat.assoc, hB, ← Cat.assoc]
    congr 1
    exact term_uniq _ _
  -- the two components of the body, as maps K → Ω.
  have hbody_split : pair τ c ≫ bigInterBody Fname
      = pair (pair τ c ≫ (fst ≫ membershipMap Fname))
          (pair τ c ≫ (pair snd fst ≫ eval_exp A (omega (𝒞 := 𝒞)))) ≫ impΩ := by
    rw [bigInterBody, ← Cat.assoc]
    congr 1
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]
    · rw [Cat.assoc, snd_pair]
  rw [hbody_split] at hbodyτ
  have hcInτ : pair τ c ≫ (pair snd fst ≫ eval_exp A (omega (𝒞 := 𝒞)))
      = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    have := impΩ_forward _ _ (Cat.id K)
      (by rw [Cat.id_comp]; exact hbodyτ)
      (by rw [Cat.id_comp]; exact hmemF)
    rwa [Cat.id_comp] at this
  -- Step 4: c ∈ τ = ⊤ means c factors through B.  c∈τ = ⟨c, τ⟩ ≫ eval = c ≫ membershipMap('B').
  -- membershipMap (nameOf B.arr) = classify B.arr (β-law); so c ≫ χ_B = ⊤ ⟹ Allows B c.
  have hceval : pair τ c ≫ (pair snd fst ≫ eval_exp A (omega (𝒞 := 𝒞)))
      = c ≫ membershipMap (nameOf B.arr B.monic) := by
    -- ⟨τ,c⟩ ≫ ⟨snd,fst⟩ = ⟨c,τ⟩;  membershipMap G = ⟨id,term≫G⟩≫eval, so c ≫ memMap('B') = ⟨c, term≫'B'⟩≫eval = ⟨c,τ⟩≫eval.
    rw [← Cat.assoc]
    have h1 : pair τ c ≫ pair snd fst = pair c τ := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, snd_pair]
      · rw [Cat.assoc, snd_pair, fst_pair]
    rw [h1, membershipMap, ← Cat.assoc]
    congr 1
    symm
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, Cat.comp_id]
    · rw [Cat.assoc, snd_pair]
      show c ≫ term A ≫ nameOf B.arr B.monic = term K ≫ nameOf B.arr B.monic
      rw [← Cat.assoc]
      congr 1
      exact term_uniq _ _
  rw [hceval, membershipMap_nameOf] at hcInτ
  -- hcInτ : c ≫ classify B.arr = term K ≫ true.  Lift through classify_pullback ⟹ Allows B c.
  obtain ⟨u, ⟨hu₁, _⟩, _⟩ := HasSubobjectClassifier.classify_pullback B.arr B.monic
    ⟨K, c, term K, hcInτ⟩
  exact ⟨u, hu₁⟩

/-! ## §1.94  `⋂F` is the GREATEST lower bound — the upper-bound half via `imp_adjunction` -/

/-- The "membership at a point" map `[A] → Ω`, `σ ↦ a ∈ σ`, for a point `a : 1 → A`. -/
noncomputable def memAtPoint {A : 𝒞} (a : one ⟶ A) : powObj A ⟶ omega (𝒞 := 𝒞) :=
  pair (term (powObj A) ≫ a) (Cat.id (powObj A)) ≫ eval_exp A (omega (𝒞 := 𝒞))

/-- **The body of `⋂F` at a point `a` is the Heyting implication `(membershipMap Fname) ⇒ memAtPoint a`.**
    `⟨id,term≫a⟩ ≫ body = ⟨χ_F, a∈σ⟩ ≫ impΩ`, where `χ_F = membershipMap Fname` and
    `a∈σ = memAtPoint a`. -/
theorem bigInterBody_at_point {A : 𝒞} (Fname : one ⟶ powObj (powObj A)) (a : one ⟶ A) :
    pair (Cat.id (powObj A)) (term (powObj A) ≫ a) ≫ bigInterBody Fname
      = pair (membershipMap Fname) (memAtPoint a) ≫ impΩ := by
  rw [bigInterBody, ← Cat.assoc]
  congr 1
  apply pair_uniq
  · -- first component: ⟨id, term≫a⟩ ≫ (fst ≫ memF) = memF
    rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.id_comp]
  · -- second: ⟨id, term≫a⟩ ≫ (⟨snd,fst⟩ ≫ eval) = ⟨term≫a, id⟩ ≫ eval = memAtPoint a
    rw [Cat.assoc, snd_pair, ← Cat.assoc, memAtPoint]
    congr 1
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, snd_pair]
    · rw [Cat.assoc, snd_pair, fst_pair]

/-- **§1.94 — `⋂F` is a GREATEST lower bound (∀-introduction via `imp_adjunction`).**

    Let `F0 ↣ [A]` be the family as a subobject of `[A]` (`subChar F0 = membershipMap Fname`),
    and `Ga ↣ [A]` the subobject `{σ | a ∈ σ}` (`subChar Ga = memAtPoint a`).  If every member
    of the family contains `a` — i.e. `F0 ≤ Ga` — then `a` lies in `⋂F`.

    This is the genuine topos content (greatest-lower-bound / ∀-introduction).  It avoids
    Ω-extensionality by routing the internal `∀σ. (σ∈F)⇒(a∈σ)` through the §1.91 Heyting
    `imp_adjunction`: the comprehension `{σ | (σ∈F)⇒(a∈σ)} = Sub.imp F0 Ga`, which is entire
    iff `entire ≤ (F0 ⇒ Ga)` iff `F0 ∩ entire ≤ Ga` iff `F0 ≤ Ga`. -/
theorem bigInter_ge {A : 𝒞} (Fname : one ⟶ powObj (powObj A)) (a : one ⟶ A)
    (F0 Ga : Subobject 𝒞 (powObj A))
    (hF0 : subChar F0 = membershipMap Fname)
    (hGa : subChar Ga = memAtPoint a)
    (hle : F0.le Ga) :
    Allows (bigInter Fname) a := by
  rw [allows_bigInter_iff]
  -- a ≫ bigInterChar = ⊤  ↔  a ≫ curry body = topName [A]  (forall_beta, term one = id)
  rw [bigInterChar, ← Cat.assoc]
  rw [forall_beta (powObj A) (a ≫ curry (bigInterBody Fname))]
  -- Goal: a ≫ curry body = term one ≫ topName [A].  membershipMap is injective ⟹ compare memMaps.
  have hinj : ∀ (G H : one ⟶ powObj (powObj A)),
      membershipMap G = membershipMap H → G = H := by
    intro G H hGH
    rw [← curry_fst_membershipMap G, ← curry_fst_membershipMap H, hGH]
  apply hinj
  -- LHS memMap = bodyAt_a (membershipMap_curry_point); RHS memMap = χ_entire (topName).
  rw [membershipMap_curry_point]
  -- term one = id, so RHS = topName [A]; its memMap = classify (entire [A]).arr = χ_entire.
  rw [show term one ≫ topName (powObj A) = topName (powObj A) by
        rw [term_uniq (term one) (Cat.id one), Cat.id_comp]]
  rw [membershipMap_topName, classify_entire]
  -- Goal now: ⟨id, term≫a⟩ ≫ body = term [A] ≫ true.  Rewrite body-at-a = impChar; use entire-ness.
  rw [bigInterBody_at_point, ← hF0, ← hGa, pair_impΩ]
  -- LHS = impChar F0 Ga = subChar (Sub.imp F0 Ga); goal: that subobject is entire.
  rw [show pair (subChar F0) (pair (subChar F0) (subChar Ga) ≫ omegaMeet) ≫ heytingDoubleArrow
        = subChar (Sub.imp F0 Ga) from (classify_imp F0 Ga).symm]
  -- entire ≤ (F0 ⇒ Ga): by imp_adjunction, since F0 ∩ entire ≤ F0 ≤ Ga.
  have hp : HasPullback F0.arr (Subobject.entire (powObj A)).arr := HasPullbacks.has _ _
  have hentireLe : (Subobject.entire (powObj A)).le (Sub.imp F0 Ga) := by
    rw [imp_adjunction F0 Ga (Subobject.entire (powObj A)) hp]
    -- F0 ∩ entire ≤ F0 ≤ Ga, composed manually.
    obtain ⟨h₁, e₁⟩ := Sub.inter_le_left F0 (Subobject.entire (powObj A)) hp
    obtain ⟨h₂, e₂⟩ := hle
    exact ⟨h₁ ≫ h₂, by rw [Cat.assoc, e₂, e₁]⟩
  -- entire ≤ S, entire.arr = id ⟹ subChar S = term ≫ true.
  have hcl := (le_iff_classify (Subobject.entire (powObj A)) (Sub.imp F0 Ga)).mp hentireLe
  -- hcl : entire.arr ≫ subChar(Sub.imp F0 Ga) = term entire.dom ≫ true; entire.arr = id, dom = [A].
  show subChar (Sub.imp F0 Ga) = term (powObj A) ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
  have he : (Subobject.entire (powObj A)).arr ≫ subChar (Sub.imp F0 Ga)
      = subChar (Sub.imp F0 Ga) := Cat.id_comp _
  rw [he] at hcl
  rw [hcl]
  congr 1

end Freyd
