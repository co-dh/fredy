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
import Fredy.ForallAlong

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-- Transitivity of the subobject order (local `private` copy; avoids importing the heavy
    `Complement` tower, and avoids a name clash with `Complement.subLe_transTE`). -/
private theorem subLe_transTE {W : 𝒞} {X Y Z : Subobject 𝒞 W} (h₁ : X.le Y) (h₂ : Y.le Z) : X.le Z := by
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

/-- **`orChar` UMP, forward half (sorry-free).**  `pair χ_S χ_T ≫ orChar` classifies a
    subobject of `A` that *contains* `S ∪ T`: i.e. `S ∪ T ≤ (pair χ_S χ_T)# (trueFst ∪ trueSnd)`,
    the subobject named by `⟨χ_S, χ_T⟩ ≫ orChar`.

    This is one half of `χ_{S∪T} = ⟨χ_S,χ_T⟩ ≫ orChar`.  The other half (`≤` the union)
    is exactly inverse-image-preserving-unions along `pair χ_S χ_T`, which is the frame /
    join-distributivity law `f#(X∪Y) ≤ f#X ∪ f#Y` — NOT a consequence of the bare join
    lattice laws, and not available at this layer (no `PreLogos 𝒞` instance for a topos yet;
    see residual note at end of file).  We therefore record the provable half here and the
    full equation as a precise residual rather than fake it. -/
theorem orChar_classifies_ge {A : 𝒞} (S T : Subobject 𝒞 A)
    (hpU : HasPullback (pair (subChar S) (subChar T))
      (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) trueSnd).arr)
    (hpF : HasPullback (pair (subChar S) (subChar T)) (trueFst (𝒞 := 𝒞)).arr)
    (hpS : HasPullback (pair (subChar S) (subChar T)) (trueSnd (𝒞 := 𝒞)).arr) :
    (HasSubobjectUnions.union S T).le
      (invImg (pair (subChar S) (subChar T))
        (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) trueSnd) hpU) := by
  -- S ≅ P# trueFst  and  T ≅ P# trueSnd  (same classifier).  P := pair χ_S χ_T.
  let P := pair (subChar S) (subChar T)
  have hSchar : subChar (invImg P trueFst hpF) = subChar S := by
    have h1 : subChar (invImg P trueFst hpF) = P ≫ subChar trueFst := classify_invImg P trueFst hpF
    rw [h1, subChar_trueFst]; exact fst_pair (subChar S) (subChar T)
  have hTchar : subChar (invImg P trueSnd hpS) = subChar T := by
    have h1 : subChar (invImg P trueSnd hpS) = P ≫ subChar trueSnd := classify_invImg P trueSnd hpS
    rw [h1, subChar_trueSnd]; exact snd_pair (subChar S) (subChar T)
  have hS_le : S.le (invImg P trueFst hpF) := (le_le_of_subChar_eq hSchar.symm).1
  have hT_le : T.le (invImg P trueSnd hpS) := (le_le_of_subChar_eq hTchar.symm).1
  have hF_le := invImg_le P trueFst (HasSubobjectUnions.union trueFst trueSnd) hpF hpU
    (HasSubobjectUnions.union_left trueFst trueSnd)
  have hG_le := invImg_le P trueSnd (HasSubobjectUnions.union trueFst trueSnd) hpS hpU
    (HasSubobjectUnions.union_right trueFst trueSnd)
  exact HasSubobjectUnions.union_min S T _ (subLe_transTE hS_le hF_le) (subLe_transTE hT_le hG_le)

/-- **`orChar` UMP, reverse half (now sorry-free via the frame law).**  `(pair χ_S χ_T)#(trueFst∪trueSnd)
    ≤ S ∪ T`: inverse image preserves unions (`ForallAlong.invImage_preserves_union`), and each
    `(pair χ_S χ_T)# trueFst ≅ S`, `(pair χ_S χ_T)# trueSnd ≅ T`. -/
theorem orChar_classifies_le {A : 𝒞} (S T : Subobject 𝒞 A)
    (hpU : HasPullback (pair (subChar S) (subChar T))
      (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) trueSnd).arr)
    (hpF : HasPullback (pair (subChar S) (subChar T)) (trueFst (𝒞 := 𝒞)).arr)
    (hpS : HasPullback (pair (subChar S) (subChar T)) (trueSnd (𝒞 := 𝒞)).arr) :
    (invImg (pair (subChar S) (subChar T))
        (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) trueSnd) hpU).le
      (HasSubobjectUnions.union S T) := by
  let P := pair (subChar S) (subChar T)
  -- frame law: P#(trueFst∪trueSnd) ≤ P#trueFst ∪ P#trueSnd.
  have hframe := invImage_preserves_union P trueFst trueSnd hpU hpF hpS
  -- P#trueFst ≅ S, P#trueSnd ≅ T  (same classifier, as in orChar_classifies_ge).
  have hSchar : subChar (invImg P trueFst hpF) = subChar S := by
    have h1 : subChar (invImg P trueFst hpF) = P ≫ subChar trueFst := classify_invImg P trueFst hpF
    rw [h1, subChar_trueFst]; exact fst_pair (subChar S) (subChar T)
  have hTchar : subChar (invImg P trueSnd hpS) = subChar T := by
    have h1 : subChar (invImg P trueSnd hpS) = P ≫ subChar trueSnd := classify_invImg P trueSnd hpS
    rw [h1, subChar_trueSnd]; exact snd_pair (subChar S) (subChar T)
  have hFS : (invImg P trueFst hpF).le S := (le_le_of_subChar_eq hSchar).1
  have hGT : (invImg P trueSnd hpS).le T := (le_le_of_subChar_eq hTchar).1
  -- P#trueFst ∪ P#trueSnd ≤ S ∪ T  (union_min + union_left/right).
  have hunion_le : (HasSubobjectUnions.union (invImg P trueFst hpF) (invImg P trueSnd hpS)).le
      (HasSubobjectUnions.union S T) :=
    HasSubobjectUnions.union_min _ _ _
      (subLe_transTE hFS (HasSubobjectUnions.union_left S T))
      (subLe_transTE hGT (HasSubobjectUnions.union_right S T))
  exact subLe_transTE hframe hunion_le

/-- **`orChar` UMP (full, sorry-free).**  `χ_{S∪T} = ⟨χ_S, χ_T⟩ ≫ orChar`: the internal
    disjunction `orChar` correctly classifies the union of any two subobjects via their
    classifiers.  Combines `orChar_classifies_ge` (≥) and `orChar_classifies_le` (≤). -/
theorem orChar_ump {A : 𝒞} (S T : Subobject 𝒞 A)
    (hpU : HasPullback (pair (subChar S) (subChar T))
      (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) trueSnd).arr)
    (hpF : HasPullback (pair (subChar S) (subChar T)) (trueFst (𝒞 := 𝒞)).arr)
    (hpS : HasPullback (pair (subChar S) (subChar T)) (trueSnd (𝒞 := 𝒞)).arr) :
    subChar (HasSubobjectUnions.union S T)
      = pair (subChar S) (subChar T) ≫ orChar (𝒞 := 𝒞) := by
  -- orChar = subChar(trueFst∪trueSnd); ⟨χ_S,χ_T⟩ ≫ orChar = subChar (P#(trueFst∪trueSnd)).
  rw [orChar, ← classify_invImg (pair (subChar S) (subChar T))
    (HasSubobjectUnions.union trueFst trueSnd) hpU]
  -- χ_{S∪T} = χ_{P#(trueFst∪trueSnd)} by mutual ≤ (the two UMP halves).
  exact classify_eq_of_le_le
    (orChar_classifies_ge S T hpU hpF hpS)
    (orChar_classifies_le S T hpU hpF hpS)

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
    exact subLe_transTE (directImage_unit f S hpI) (invImg_le f (directImage f S) T hpI hp hle)
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

/-! ## RESIDUALS — what remains, and the single missing lemma that closes it all

  DELIVERED sorry-free (axioms ⊆ {propext, Classical.choice}):
    * `orChar`             — internal disjunction `∨ : Ω×Ω → Ω`.
    * `orChar_classifies_ge` — forward half of the `∨` UMP.
    * `directImage` / `directImage_unit` / `directImage_adjunction` — `∃_f ⊣ f#` (FULL).

  The ONE missing lemma, which closes BOTH the `∨` UMP *and* binary coproducts:

      theorem invImage_preserves_union {A B : 𝒞} (f : A ⟶ B) (S T : Subobject 𝒞 B)
          (hpU : HasPullback f (HasSubobjectUnions.union S T).arr)
          (hpS : HasPullback f S.arr) (hpT : HasPullback f T.arr) :
          (invImg f (HasSubobjectUnions.union S T) hpU).le
            (HasSubobjectUnions.union (invImg f S hpS) (invImg f T hpT))

  This is the frame / join-distributivity law `f#(S∪T) ≤ f#S ∪ f#T`.  It is the forward
  conjunct of `inverseImage_preserves_unions` (S1_60:73), available today ONLY as an
  unproven *field* of the `PreLogos` class — and a topos is NOT yet an instance of `PreLogos`.
  The lattice UMP of the union (`union_left/right/min`) does NOT entail it; it needs the
  topos's frame structure on `Sub(A)`, i.e. one must first establish `PreLogos 𝒞` (equivalently
  `Logos 𝒞`) under `[Topos 𝒞]` (the regular half — image/cover pullback-stability — is already
  proven in `InternalForallTopos`/`SliceRegular`; the join-distributivity half is the gap).

  HOW IT CLOSES THE `∨` UMP.  With `invImage_preserves_union` at `f := pair χ_S χ_T`:
    `χ_{S∪T} = ⟨χ_S, χ_T⟩ ≫ orChar`  follows from `classify_eq_of_le_le`:
      * `≥` (i.e. `S∪T ≤ (pair χ_S χ_T)#(trueFst∪trueSnd)`) is `orChar_classifies_ge` (DONE);
      * `≤` is `invImage_preserves_union` + the two `subChar`-identities
        `(pair χ_S χ_T)# trueFst ≅ S`, `(pair χ_S χ_T)# trueSnd ≅ T` (already extracted inside
        `orChar_classifies_ge` as `hSchar`/`hTchar`), via `union_min`.

  HOW IT CLOSES BINARY COPRODUCTS (`S1_95.topos_is_positive`).  The carrier
  `A + B ⊂ [A]×[B]` is `union {(s,∅)} {(∅,t)}` (singletons via `singletonMap`, the empty
  slot via `bottomSub`/`subOfChar false`, carved with `orChar` + `topos_has_equalizers`).
  `inl`/`inr` factor through the carrier by `union_left`/`union_right` (FORWARD only — available).
  `case f g` is the partial-map copairing via `partialMapClassifier_exists` (LawfulPMC, sorry-free).
  `case_uniq` needs "the carrier is covered by `inl,inr`", i.e. `entire = union(im inl)(im inr)`,
  which is the SAME join-cover/`f#`-union fact.  So coproducts inherit exactly this one blocker.

  Once `invImage_preserves_union` (⇐ `PreLogos 𝒞` for a topos) lands, this file extends to:
  the full `orChar_ump`, the `HasBinaryCoproducts 𝒞` instance, and thence `topos_is_positive`
  becomes `exact ‹HasBinaryCoproducts 𝒞›` — unblocking §1.954 coequalizers (with
  `HasReflTransClosure`), §1.955 `topos_is_bicartesian`, and the strict coterminator `0`. -/

end Freyd
