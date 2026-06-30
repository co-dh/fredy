/-
  Freyd & Scedrov, *Categories and Allegories* §1.95 — finite-colimit layer for a topos.

  This file builds the genuinely-now-reachable pieces of the §1.95 cocartesian story,
  on top of the regularity refactor that made these INSTANCES available from `[Topos 𝒞]`:

    * `HasImages 𝒞`               — `InternalForallTopos.toposHasImages` (family-glb `bigInter`)
    * `PullbacksTransferCovers 𝒞` — `SlicePi.toposPullbacksTransferCovers`
    * `RegularCategory 𝒞`         — `InternalForallTopos.topos_is_regular_real` (Nonempty)
    * `partialMapClassifier_exists` — `PartialMapClassifier` (LawfulPMC per codomain, SORRY-FREE)

  The §1.95 docstrings in `Fredy/S1_95.lean` predate this refactor and flag (U) `HasImages`,
  (P) the partial-map classifier `Ω₊`, and the carrier subobject-union as blockers — those
  three are now resolved upstream.  Here we assemble the next layer:

    §1.952(U)  `HasSubobjectUnions 𝒞` — binary subobject union `S ∪ T` as the family-glb
               `⋂{σ ⊆ [A] | S ⊆ σ ∧ T ⊆ σ}` of the common upper bounds, via `bigInter`.
               This is the (U) carrier ingredient AND a `PreLogos` field.

  WHAT REMAINS (precise residuals, each a multi-step relation/family construction, NOT a
  one-liner — left as faithful sorries with the missing-lemma signature in the docstring):

    §1.952(P)  the coproduct UMP carrier `A + B ⊂ [A]×[B]` and copairing — needs the
               singleton-or-empty subobject (internal disjunction `∨ : Ω×Ω → Ω`, itself an
               image/`∃` construction) plus the PMC copairing.
    §1.954     `topos_has_coequalizers` — needs `EffectiveRegular` (the per-relation quotient
               cover `q : A ↠ A/E`, `level q ≅ E`) and a `HasReflTransClosure` instance.
    §1.955     `topos_is_bicartesian` — needs coproducts + coequalizers + the initial object
               `0` (`topos_has_strict_coterminator`, S1_94, blocked on the empty subobject /
               `⋂∅` = `false`).
-/

import Fredy.S1_91
import Fredy.S1_92
import Fredy.S1_60
import Fredy.S1_94_InterIntersection
import Fredy.S1_94_InternalForallTopos
import Fredy.S1_934_PartialMapClassifier

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.952(U)  Binary subobject union via the upper-bound family-glb

  `S ∪ T` is the *least* subobject of `A` containing both `S` and `T`.  In a topos with the
  family-glb `bigInter` (= `⋂F` for a named family `F ↣ [A]`), the union is the glb of the
  family of *common upper bounds*:

      S ∪ T  =  ⋂ { σ ⊆ A | S ⊆ σ  ∧  T ⊆ σ }.

  The family is NAMED on `[A]` by the predicate `χ_∪(S,T) : [A] → Ω`,
      `σ  ↦  (S ⊆ σ) ∧ (T ⊆ σ)`,
  built from the internal inclusion predicate of `S1_91` (`Sub`-Heyting `⇒`/`∧` on `[A]`'s
  membership) and the family-name `1 → [[A]]` is `curry (fst ≫ χ_∪)`.

  Once `unionFamilyName S T : 1 → [[A]]` is built, `bigInter_glb` gives:
    * LOWER:    `bigInter ≤ σ` for every common upper bound `σ` ⟹ `union_min`;
    * GREATEST: `a ∈ bigInter` when every common upper bound contains `a`; since `S` itself
                is contained in every common upper bound, `S ≤ bigInter` ⟹ `union_left`
                (and symmetrically `union_right`). -/

/-- The internal "common-upper-bound" predicate `[A] → Ω` for two subobjects `S, T ⊆ A`:
    `σ ↦ (S ⊆ σ) ∧ (T ⊆ σ)`.

    A point `σ : [A]` is, via `membershipMap`-style evaluation, a subobject of `A`; the
    predicate tests that `S` and `T` are both contained in it.  Concretely this is the
    conjunction (S1_91 `omegaMeet`) of the two inclusion characteristic maps, each of which is
    the §1.914 internal `⊆` on `[A]` (the curried `Sub.imp`/membership comparison). -/
noncomputable def upperBoundPred {A : 𝒞} (S T : Subobject 𝒞 A) :
    powObj A ⟶ omega (𝒞 := 𝒞) :=
  -- (S ⊆ σ) ∧ (T ⊆ σ) : pair the two inclusion-tests, then internal meet (S1_91 `omegaMeet`).
  -- The single inclusion test `σ ↦ (S ⊆ σ)` is the §1.945 fibered-∀ `predF S.arr`, i.e.
  -- `σ ↦ ∀s. S.arr(s) ∈ σ`; its name-membership is exactly `Allows σ S.arr = S.le σ`.
  pair (predF S.arr) (predF T.arr) ≫ omegaMeet

/-- The family NAME `1 → [[A]]` of the common-upper-bound family `{σ | S ⊆ σ ∧ T ⊆ σ}`. -/
noncomputable def unionFamilyName {A : 𝒞} (S T : Subobject 𝒞 A) :
    one ⟶ powObj (powObj A) :=
  curry (fst ≫ upperBoundPred S T)

/-- **§1.952(U)** — binary subobject union as the upper-bound family-glb. -/
noncomputable def subUnion {A : 𝒞} (S T : Subobject 𝒞 A) : Subobject 𝒞 A :=
  bigInter (unionFamilyName S T)

/-- A subobject `σ ⊆ A` is a COMMON UPPER BOUND of `S, T` iff its name satisfies the
    upper-bound predicate, i.e. iff its name is a member of the union family.  This is the
    membership characterization bridging `bigInter_glb` to the lattice laws. -/
theorem name_mem_unionFamily_iff {A : 𝒞} (S T σ : Subobject 𝒞 A) :
    (nameOf σ.arr σ.monic ≫ membershipMap (unionFamilyName S T)
        = term one ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
      ↔ (S.le σ ∧ T.le σ) := by
  -- membershipMap (unionFamilyName S T) = upperBoundPred S T = ⟨predF S.arr, predF T.arr⟩ ≫ ∧.
  rw [unionFamilyName, membershipMap_curry_fst, upperBoundPred]
  -- meet_true_iff_and splits the conjunction into the two name-membership tests.
  rw [meet_true_iff_and (predF S.arr) (predF T.arr) (nameOf σ.arr σ.monic)]
  -- each test is `nameOf σ ≫ membershipMap (imageFamily ·.arr) = ⊤ ↔ Allows σ ·.arr = ·.le σ`.
  rw [show predF S.arr = membershipMap (imageFamily S.arr) from (membershipMap_imageFamily S.arr).symm,
    show predF T.arr = membershipMap (imageFamily T.arr) from (membershipMap_imageFamily T.arr).symm,
    name_mem_imageFamily_iff S.arr σ, name_mem_imageFamily_iff T.arr σ]
  -- Allows σ S.arr = S.le σ definitionally (both = ∃ h, h ≫ σ.arr = S.arr).
  rfl

/-! ### Generalized upper-bound (`Allows (bigInter F) f`) for a generic family `F`

  `InternalForallTopos.allows_imageF` proves `Allows (imageF f) f` for the SPECIFIC image
  family `imageFamily f`; its proof is family-generic except for the `imageF_carrier_in_mem`
  step (which is `private`).  We re-establish that generic reduction here, taking the
  family-specific *carrier-in-membership* fact as a hypothesis `hci`, so it can be reused for
  the union family `unionFamilyName S T`. -/

/-- **Carrier-in-membership for the union family.**  For any subobject `R ⊆ A` and any
    generalized point `k : K → [A] × Df` whose `[A]`-component lies in the `predF R.arr`
    family (`k ≫ fst ≫ predF R.arr = ⊤`), the body `(σ,a) ↦ R.arr(a) ∈ σ` is true along `k`:
    `k ≫ ⟨snd≫R.arr, fst⟩ ≫ eval = ⊤`.  Public re-proof of the `private`
    `InternalForallTopos.imageF_carrier_in_mem`, using only `predF`/`forall_beta`/`forall_elim`. -/
private theorem predF_carrier_in_mem {A Df K : 𝒞} (f : Df ⟶ A) (k : K ⟶ prod (powObj A) Df)
    (hk : k ≫ (fst ≫ predF f) = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    k ≫ (pair (snd (A := powObj A) (B := Df) ≫ f) fst ≫ eval_exp A (omega (𝒞 := 𝒞)))
      = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  -- σ := k ≫ fst : K → [A], τ := k ≫ snd : K → Df.  predF unfolds to curry(body) ≫ forallC.
  rw [← Cat.assoc, predF, ← Cat.assoc] at hk
  have hentire : (k ≫ fst) ≫ curry (pair (fst ≫ f) snd ≫ eval_exp A (omega (𝒞 := 𝒞)))
      = term K ≫ topName Df :=
    (forall_beta Df ((k ≫ fst)
      ≫ curry (pair (fst ≫ f) snd ≫ eval_exp A (omega (𝒞 := 𝒞))))).mp hk
  have helim := forall_elim ((k ≫ fst)
    ≫ curry (pair (fst ≫ f) snd ≫ eval_exp A (omega (𝒞 := 𝒞)))) hentire (k ≫ snd)
  rw [eval_curry_point (pair (fst ≫ f) snd ≫ eval_exp A (omega (𝒞 := 𝒞))) (k ≫ snd) (k ≫ fst)]
    at helim
  rw [← Cat.assoc] at helim
  rw [← helim, ← Cat.assoc]
  congr 1
  -- k ≫ ⟨snd≫f, fst⟩ = ⟨k≫snd≫f, k≫fst⟩ = ⟨k≫snd, k≫fst⟩ ≫ ⟨fst≫f, snd⟩.
  rw [show k ≫ pair (snd (A := powObj A) (B := Df) ≫ f) fst
        = pair (k ≫ snd ≫ f) (k ≫ fst) from by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair]
      · rw [Cat.assoc, snd_pair]]
  symm
  apply pair_uniq
  · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc]
  · rw [Cat.assoc, snd_pair, snd_pair]

/-- **Generalized upper bound.**  `Allows (bigInter Fname) f` whenever the family's
    carrier-in-membership holds: every generalized point `k : K → [A] × Df` whose `[A]`-slot
    is in `Fname` (`k ≫ fst ≫ membershipMap Fname = ⊤`) satisfies `f(k≫snd) ∈ (k≫fst)`.
    This is the §1.91 `imp_adjunction` greatest-lower-bound reduction, family-generic in the
    carrier-in-membership hypothesis. -/
theorem allows_bigInter_of_carrier {A Df : 𝒞} (f : Df ⟶ A)
    (Fname : one ⟶ powObj (powObj A))
    (hci : ∀ {K : 𝒞} (k : K ⟶ prod (powObj A) Df),
      k ≫ (fst ≫ membershipMap Fname) = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) →
      k ≫ (pair (snd (A := powObj A) (B := Df) ≫ f) fst ≫ eval_exp A (omega (𝒞 := 𝒞)))
        = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    Allows (bigInter Fname) f := by
  rw [allows_iff_classify]
  rw [show HasSubobjectClassifier.classify (bigInter Fname).arr (bigInter Fname).monic
        = bigInterChar Fname from classify_invImage_true (bigInterChar Fname)]
  rw [bigInterChar, ← Cat.assoc]
  rw [forall_beta (powObj A) (f ≫ curry (bigInterBody Fname))]
  rw [curry_precomp]
  rw [show topName (powObj A)
        = curry (fst ≫ HasSubobjectClassifier.classify (Subobject.entire (powObj A)).arr
            (Subobject.entire (powObj A)).monic) from rfl]
  rw [curry_precomp]
  apply congrArg curry
  rw [← Cat.assoc, prodMap_fst, classify_entire, ← Cat.assoc,
    term_uniq (fst ≫ term (powObj A)) (term (prod (powObj A) Df))]
  -- Goal: prodMap [A] Df A f ≫ bigInterBody Fname = term ≫ true.
  let chiF : prod (powObj A) Df ⟶ omega (𝒞 := 𝒞) := fst ≫ membershipMap Fname
  let chiIn : prod (powObj A) Df ⟶ omega (𝒞 := 𝒞) :=
    pair (snd (A := powObj A) (B := Df) ≫ f) fst ≫ eval_exp A (omega (𝒞 := 𝒞))
  have hsplit : prodMap (powObj A) Df A f ≫ bigInterBody Fname
      = pair chiF chiIn ≫ impΩ := by
    rw [bigInterBody, ← Cat.assoc]
    congr 1
    apply pair_uniq
    · show _ = chiF
      rw [Cat.assoc, fst_pair, ← Cat.assoc]
      congr 1
      rw [prodMap_fst]
    · show _ = chiIn
      rw [Cat.assoc, snd_pair, ← Cat.assoc]
      congr 1
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, prodMap_snd]
      · rw [Cat.assoc, snd_pair, prodMap_fst]
  rw [hsplit, pair_impΩ]
  obtain ⟨_, mF, hmF, hSF⟩ := classify_surjective chiF
  obtain ⟨_, mIn, hmIn, hSIn⟩ := classify_surjective chiIn
  let S_F : Subobject 𝒞 (prod (powObj A) Df) := ⟨_, mF, hmF⟩
  let S_In : Subobject 𝒞 (prod (powObj A) Df) := ⟨_, mIn, hmIn⟩
  have hcF : subChar S_F = chiF := hSF
  have hcIn : subChar S_In = chiIn := hSIn
  rw [show pair chiF (pair chiF chiIn ≫ omegaMeet) ≫ heytingDoubleArrow
        = subChar (Sub.imp S_F S_In) by rw [classify_imp, impChar, hcF, hcIn]]
  have hp : HasPullback S_F.arr (Subobject.entire (prod (powObj A) Df)).arr := HasPullbacks.has _ _
  have hSFle : S_F.le S_In := by
    apply (allows_iff_classify S_In S_F.arr).2
    rw [show HasSubobjectClassifier.classify S_In.arr S_In.monic = chiIn from hcIn]
    have hcarF : S_F.arr ≫ chiF = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      rw [show chiF = HasSubobjectClassifier.classify S_F.arr S_F.monic from hcF.symm]
      exact HasSubobjectClassifier.classify_sq S_F.arr S_F.monic
    exact hci S_F.arr hcarF
  have hentireLe : (Subobject.entire (prod (powObj A) Df)).le (Sub.imp S_F S_In) := by
    rw [imp_adjunction S_F S_In (Subobject.entire (prod (powObj A) Df)) hp]
    obtain ⟨h₁, e₁⟩ := Sub.inter_le_left S_F (Subobject.entire (prod (powObj A) Df)) hp
    obtain ⟨h₂, e₂⟩ := hSFle
    exact ⟨h₁ ≫ h₂, by rw [Cat.assoc, e₂, e₁]⟩
  have hcl := (le_iff_classify (Subobject.entire (prod (powObj A) Df))
    (Sub.imp S_F S_In)).mp hentireLe
  show subChar (Sub.imp S_F S_In) = term (prod (powObj A) Df) ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
  rw [show (Subobject.entire (prod (powObj A) Df)).arr ≫ subChar (Sub.imp S_F S_In)
        = subChar (Sub.imp S_F S_In) from Cat.id_comp _] at hcl
  rw [hcl]
  congr 1

/-- `union_left`: `S ≤ S ∪ T`.  `S` is contained in every common upper bound `σ`, so by the
    GREATEST direction (generalized upper bound `allows_bigInter_of_carrier`), `S ≤ ⋂{common
    upper bounds}`.  The carrier-in-mem hypothesis: if `σ ∈ unionFamily` then `σ ∈ predF S.arr`
    (the `S`-conjunct, via `meet_true_iff_and`), whence `S.arr(a) ∈ σ` (`predF_carrier_in_mem`). -/
theorem subUnion_left {A : 𝒞} (S T : Subobject 𝒞 A) : S.le (subUnion S T) := by
  show Allows (subUnion S T) S.arr
  rw [subUnion]
  apply allows_bigInter_of_carrier S.arr (unionFamilyName S T)
  intro K k hk
  -- hk : k ≫ fst ≫ membershipMap (unionFamily) = ⊤.  membershipMap = ⟨predF S.arr, predF T.arr⟩ ≫ ∧.
  rw [unionFamilyName, membershipMap_curry_fst, upperBoundPred, ← Cat.assoc] at hk
  -- extract the S-conjunct via meet_true_iff_and, then predF_carrier_in_mem.
  have hS := ((meet_true_iff_and (predF S.arr) (predF T.arr) (k ≫ fst)).mp hk).1
  exact predF_carrier_in_mem S.arr k (by rw [← Cat.assoc]; exact hS)

/-- `union_right`: `T ≤ S ∪ T` (symmetric to `subUnion_left`; uses the `T`-conjunct). -/
theorem subUnion_right {A : 𝒞} (S T : Subobject 𝒞 A) : T.le (subUnion S T) := by
  show Allows (subUnion S T) T.arr
  rw [subUnion]
  apply allows_bigInter_of_carrier T.arr (unionFamilyName S T)
  intro K k hk
  rw [unionFamilyName, membershipMap_curry_fst, upperBoundPred, ← Cat.assoc] at hk
  have hT := ((meet_true_iff_and (predF S.arr) (predF T.arr) (k ≫ fst)).mp hk).2
  exact predF_carrier_in_mem T.arr k (by rw [← Cat.assoc]; exact hT)

/-- `union_min`: `S ∪ T` is the LEAST common upper bound.  If `S ≤ U` and `T ≤ U` then `U`
    is a common upper bound, so it is named by the family, so the LOWER direction of
    `bigInter_glb` gives `⋂{common upper bounds} ≤ U`. -/
theorem subUnion_min {A : 𝒞} (S T U : Subobject 𝒞 A)
    (hS : S.le U) (hT : T.le U) : (subUnion S T).le U := by
  -- U is a common upper bound: (name_mem_unionFamily_iff).2 ⟨hS, hT⟩; then bigInter_le_named.
  exact (bigInter_glb (unionFamilyName S T)).1 U
    ((name_mem_unionFamily_iff S T U).2 ⟨hS, hT⟩)

/-- **§1.952(U)** — a topos HAS SUBOBJECT UNIONS.  The binary union is the family-glb of the
    common upper bounds (`subUnion`); the three lattice laws are `subUnion_left/right/min`. -/
noncomputable instance toposHasSubobjectUnions : HasSubobjectUnions 𝒞 where
  union S T := subUnion S T
  union_left := subUnion_left
  union_right := subUnion_right
  union_min := subUnion_min

/-! ## §1.95  The EMPTY / BOTTOM subobject `∅ ↪ A` via the all-subobjects family-glb

  The empty subobject `∅_A ↪ A` is `⋂{σ ⊆ A}` — the glb of the family of ALL subobjects of
  `A`.  That family is named on `[A]` by the TOP predicate (every `σ` qualifies), i.e. by
  `topName (powObj A) : 1 → [[A]]` (the name of the entire subobject of `[A]`).  Then
  `bottomSub A := bigInter (topName [A])` is below EVERY subobject `B ⊆ A`, because every `B`
  is named by the top family, so the LOWER direction of `bigInter_glb` applies.

  This is the `PreLogos.bottom` field (the empty join of `Sub(A)`) and the carrier of the
  initial object `0` (the §1.94 `topos_has_strict_coterminator` blocker): once `∅_A.dom`-iso
  across `A` and uniqueness of `∅_A.dom → X` are added, `0 := ∅_A.dom` is initial.  Here we
  build the subobject and its defining `≤`-law (the substantive family-glb content). -/

/-- **§1.95** — the EMPTY/BOTTOM subobject `∅_A ↪ A` as `⋂{all σ ⊆ A}`. -/
noncomputable def bottomSub (A : 𝒞) : Subobject 𝒞 A :=
  bigInter (topName (powObj A))

/-- **§1.95** — `∅_A` is the LEAST subobject: `∅_A ≤ B` for every `B ⊆ A`.  Every `B` is named
    by the top family `topName [A]` (its membership predicate is constantly `⊤` =
    `χ_{entire [A]}`), so the LOWER direction of `bigInter_glb` gives `⋂ ≤ B`. -/
theorem bottomSub_le {A : 𝒞} (B : Subobject 𝒞 A) : (bottomSub A).le B := by
  apply (bigInter_glb (topName (powObj A))).1 B
  -- name(B) ≫ membershipMap (topName [A]) = ⊤∘! : membershipMap (topName [A]) = χ_{entire} = term ≫ true.
  rw [membershipMap_topName, classify_entire, ← Cat.assoc,
    term_uniq (nameOf B.arr B.monic ≫ term (powObj A)) (term one)]

end Freyd
