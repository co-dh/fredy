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
import Fredy.S1_56
import Fredy.PartialMapClassifier

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

/-! ## RESIDUALS — binary coproducts: what is DONE, and the one remaining piece

  DELIVERED sorry-free (axioms ⊆ {propext, Classical.choice}):
    * `orChar` / `orChar_ump`  — internal disjunction `∨ : Ω×Ω → Ω` with its FULL UMP
      `χ_{S∪T} = ⟨χ_S,χ_T⟩ ≫ orChar` (closed via the now-proven frame law
      `ForallAlong.invImage_preserves_union`).
    * `directImage` / `directImage_unit` / `directImage_adjunction` — `∃_f ⊣ f#` (FULL).

  Binary coproducts `A + B ⊂ [A]×[B]` (GOAL 3 below), DELIVERED sorry-free:
    * `coprodSub` / `coprodObj` / `coprodArr`  — the CARRIER `A+B = union (image inlRaw)
      (image inrRaw) ⊆ [A]×[B]` and its monic embedding.
    * `coprodInl` / `coprodInr`  — the two INJECTIONS, with `coprodInl_arr`/`coprodInr_arr`
      (`inl ≫ embed = inlRaw`, `inr ≫ embed = inrRaw`) and monicity `coprodInl_monic`/
      `coprodInr_monic`.
    * `coprod_jointly_epi`  — the INJECTIONS ARE JOINTLY EPIC (the `case_uniq` content):
      any two `h,k : A+B → X` with `inl≫h=inl≫k` and `inr≫h=inr≫k` are equal.  Proved
      ELEMENTARILY (equalizer of `h,k` + `image_min` + `union_min`; no frame law needed).
    * `casePMf`/`casePMg` + `casePMf_sq`/`casePMg_sq` — `f`,`g` as partial maps `A+B ⇀ X`
      (injections are monic) with their classify β-squares `inl ≫ χf = f ≫ η`, etc.

  THE ONE REMAINING PIECE — the copairing `case f g : A+B → X` (existence of a map with
  `inl ≫ case = f`, `inr ≫ case = g`).  This is the genuine §1.935 amalgamation and is NOT
  reducible to the join-lattice/PMC data already present, for a precise reason:

    To build `case` one must GLUE `f : A → X` and `g : B → X` into a single map out of
    `A+B`.  `A+B` is the subobject JOIN `union (image inl)(image inr)`; but a subobject join
    carries only a *map-IN* universal property (`union_left/right/min` — containment), NOT a
    *map-OUT* (colimit) one.  So there is no way to define the value `(A+B) → X` from `f,g`
    using `union`.  The partial-map classifier reduces only TOTALITY of a candidate
    `χ : A+B → X̃` (it factors through `η : X ↪ X̃` exactly on its domain of definition); it
    does NOT produce the candidate.  Producing `χ` (= the join `χf ∨ χg` of the two partial
    classifiers as a single TOTAL map) is exactly the missing amalgamation, and it requires
    the DISJOINTNESS of the two injection images (`image inl ⊓ image inr = ⊥` in `Sub(A+B)`,
    i.e. `({a},∅) ≠ (∅,{b})`, a non-degeneracy fact: a singleton is not the empty subobject)
    together with the union-COVER (`entire (A+B) = union (image inl)(image inr)`, the
    frame-law `f#`-union fact at `coprodArr`) to certify that the glued map is well-defined
    and total.  This "join of two partial maps over a disjoint cover" is precisely Freyd's
    §1.935 value-object amalgamation; it is the SINGLE residual.

  PRECISE MISSING-LEMMA SIGNATURE (closes `case`, hence the whole instance):

      theorem coprod_case_exists {A B X : 𝒞} (f : A ⟶ X) (g : B ⟶ X) :
          ∃ c : coprodObj A B ⟶ X, coprodInl A B ≫ c = f ∧ coprodInr A B ≫ c = g

  With `coprod_case_exists` in hand, `case := (coprod_case_exists f g).choose`, the two
  β-laws are its `.choose_spec`, and `case_uniq` is `coprod_jointly_epi`.  That assembles
  `instance toposHasBinaryCoproducts : HasBinaryCoproducts 𝒞`, and then
  `S1_95.topos_is_positive` becomes `exact toposHasBinaryCoproducts` — unblocking §1.954
  coequalizers (with `HasReflTransClosure`), §1.955 `topos_is_bicartesian`, and the strict
  coterminator `0`. -/

/-! ## GOAL 3 — Binary coproducts `A + B ⊂ [A] × [B]`

  Carrier:  `A + B := union (image inlRaw) (image inrRaw)  ⊆  [A] × [B]`, where
    * `inlRaw a := ({a}, ∅)`   — `pair (singletonMap A) (term A ≫ emptyName B)`,
    * `inrRaw b := (∅, {b})`   — `pair (term B ≫ emptyName A) (singletonMap B)`,
  with `∅ := nameOf (bottomSub _)` the global name of the empty subobject (the empty
  relation `1 → [·]`).  `coprodInl`/`coprodInr` are the two injections, factoring through
  the carrier by `union_left`/`union_right`. -/

/-- The global NAME `1 → [A]` of the empty subobject `∅ ⊆ A` (the empty element of `[A]`). -/
noncomputable def emptyName (A : 𝒞) : one (𝒞 := 𝒞) ⟶ powObj A :=
  nameOf (bottomSub A).arr (bottomSub A).monic

/-- The raw left injection `A → [A]×[B]`, `a ↦ ({a}, ∅)`. -/
noncomputable def inlRaw (A B : 𝒞) : A ⟶ prod (powObj A) (powObj B) :=
  pair (singletonMap A) (term A ≫ emptyName B)

/-- The raw right injection `B → [A]×[B]`, `b ↦ (∅, {b})`. -/
noncomputable def inrRaw (A B : 𝒞) : B ⟶ prod (powObj A) (powObj B) :=
  pair (term B ≫ emptyName A) (singletonMap B)

/-- The CARRIER subobject `A + B ⊆ [A]×[B]`: the union of the two singleton-image
    subobjects. -/
noncomputable def coprodSub (A B : 𝒞) : Subobject 𝒞 (prod (powObj A) (powObj B)) :=
  HasSubobjectUnions.union (image (inlRaw A B)) (image (inrRaw A B))

/-- The coproduct OBJECT `A + B` (domain of the carrier subobject). -/
noncomputable def coprodObj (A B : 𝒞) : 𝒞 := (coprodSub A B).dom

/-- The carrier inclusion `A + B ↪ [A]×[B]` (monic). -/
noncomputable def coprodArr (A B : 𝒞) : coprodObj A B ⟶ prod (powObj A) (powObj B) :=
  (coprodSub A B).arr

theorem coprodArr_monic (A B : 𝒞) : Mono (coprodArr A B) := (coprodSub A B).monic

/-- The chosen factorization `image (inlRaw) ≤ coprodSub` (from `union_left`). -/
noncomputable def imLeftToCarrier (A B : 𝒞) : (image (inlRaw A B)).dom ⟶ coprodObj A B :=
  (HasSubobjectUnions.union_left (image (inlRaw A B)) (image (inrRaw A B))).choose

theorem imLeftToCarrier_fac (A B : 𝒞) :
    imLeftToCarrier A B ≫ coprodArr A B = (image (inlRaw A B)).arr :=
  (HasSubobjectUnions.union_left (image (inlRaw A B)) (image (inrRaw A B))).choose_spec

noncomputable def imRightToCarrier (A B : 𝒞) : (image (inrRaw A B)).dom ⟶ coprodObj A B :=
  (HasSubobjectUnions.union_right (image (inlRaw A B)) (image (inrRaw A B))).choose

theorem imRightToCarrier_fac (A B : 𝒞) :
    imRightToCarrier A B ≫ coprodArr A B = (image (inrRaw A B)).arr :=
  (HasSubobjectUnions.union_right (image (inlRaw A B)) (image (inrRaw A B))).choose_spec

/-- **Left injection** `inl : A → A + B`: factor `inlRaw` through its image, then into the
    carrier union. -/
noncomputable def coprodInl (A B : 𝒞) : A ⟶ coprodObj A B :=
  image.lift (inlRaw A B) ≫ imLeftToCarrier A B

/-- **Right injection** `inr : B → A + B`. -/
noncomputable def coprodInr (A B : 𝒞) : B ⟶ coprodObj A B :=
  image.lift (inrRaw A B) ≫ imRightToCarrier A B

/-- `coprodInl ≫ carrier-inclusion = inlRaw`: the left injection composed with the carrier
    embedding is the raw map `a ↦ ({a}, ∅)`. -/
theorem coprodInl_arr (A B : 𝒞) : coprodInl A B ≫ coprodArr A B = inlRaw A B := by
  rw [coprodInl, Cat.assoc, imLeftToCarrier_fac, image.lift_fac]

theorem coprodInr_arr (A B : 𝒞) : coprodInr A B ≫ coprodArr A B = inrRaw A B := by
  rw [coprodInr, Cat.assoc, imRightToCarrier_fac, image.lift_fac]

/-- `inlRaw` is monic: `inlRaw ≫ fst = singletonMap A`, which is monic. -/
theorem inlRaw_monic (A B : 𝒞) : Mono (inlRaw A B) := by
  intro W u v huv
  refine singletonMap_monic A u v ?_
  have : (u ≫ inlRaw A B) ≫ fst = (v ≫ inlRaw A B) ≫ fst := by rw [huv]
  rwa [Cat.assoc, Cat.assoc, inlRaw, fst_pair] at this

/-- `inrRaw` is monic: `inrRaw ≫ snd = singletonMap B`, which is monic. -/
theorem inrRaw_monic (A B : 𝒞) : Mono (inrRaw A B) := by
  intro W u v huv
  refine singletonMap_monic B u v ?_
  have : (u ≫ inrRaw A B) ≫ snd = (v ≫ inrRaw A B) ≫ snd := by rw [huv]
  rwa [Cat.assoc, Cat.assoc, inrRaw, snd_pair] at this

/-- **`inl` is monic.**  `coprodInl ≫ coprodArr = inlRaw` is monic, so `coprodInl` is. -/
theorem coprodInl_monic (A B : 𝒞) : Mono (coprodInl A B) := by
  intro W u v huv
  refine inlRaw_monic A B u v ?_
  rw [← coprodInl_arr, ← Cat.assoc, ← Cat.assoc, huv]

/-- **`inr` is monic.** -/
theorem coprodInr_monic (A B : 𝒞) : Mono (coprodInr A B) := by
  intro W u v huv
  refine inrRaw_monic A B u v ?_
  rw [← coprodInr_arr, ← Cat.assoc, ← Cat.assoc, huv]

/-- Equalizer maps are monic (local copy; `S1_57.eqMap_mono` is not imported here). -/
private theorem eqMap_mono_local {A B : 𝒞} (f g : A ⟶ B) : Mono (eqMap f g) := by
  intro W u v huv
  -- c := u ≫ eqMap equalizes f, g; both u and v are its (unique) lift.
  have hc : (u ≫ eqMap f g) ≫ f = (u ≫ eqMap f g) ≫ g := by
    rw [Cat.assoc, Cat.assoc, eqMap_eq]
  have h1 : u = eqLift f g (u ≫ eqMap f g) hc := eqLift_uniq f g _ hc u rfl
  have h2 : v = eqLift f g (u ≫ eqMap f g) hc := eqLift_uniq f g _ hc v huv.symm
  rw [h1, h2]

/-- **Joint epimorphism of the injections.**  `coprodInl` and `coprodInr` are jointly epic:
    any two maps out of `A + B` agreeing after `inl` and `inr` are equal.  This is the
    cover-by-injections fact (`case_uniq` content), proved elementarily via the equalizer of
    the two maps: both injections factor through it, so their image subobjects lie in it, so the
    whole carrier (the union of those images) lies in it — forcing the equalizer to be entire. -/
theorem coprod_jointly_epi {A B X : 𝒞} (h k : coprodObj A B ⟶ X)
    (hl : coprodInl A B ≫ h = coprodInl A B ≫ k)
    (hr : coprodInr A B ≫ h = coprodInr A B ≫ k) : h = k := by
  -- E = equalizer of h, k, with monic inclusion e : E ↪ A+B.
  let e : eqObj h k ⟶ coprodObj A B := eqMap h k
  have he_mono : Mono e := eqMap_mono_local h k
  let E : Subobject 𝒞 (coprodObj A B) := ⟨eqObj h k, e, he_mono⟩
  -- both injections factor through E.
  let l₁ : A ⟶ eqObj h k := eqLift h k (coprodInl A B) hl
  have hl₁ : l₁ ≫ e = coprodInl A B := eqLift_fac h k _ hl
  let l₂ : B ⟶ eqObj h k := eqLift h k (coprodInr A B) hr
  have hl₂ : l₂ ≫ e = coprodInr A B := eqLift_fac h k _ hr
  -- ⟨E, e ≫ coprodArr⟩ : a subobject of [A]×[B] (e and coprodArr both monic).
  have hec_mono : Mono (e ≫ coprodArr A B) := by
    intro W u v huv
    exact he_mono u v ((coprodArr_monic A B) _ _ (by rw [Cat.assoc, Cat.assoc, huv]))
  let Ec : Subobject 𝒞 (prod (powObj A) (powObj B)) := ⟨eqObj h k, e ≫ coprodArr A B, hec_mono⟩
  -- inlRaw and inrRaw both factor through Ec (via l₁, l₂), so the two image subobjects ≤ Ec.
  have him_l : (image (inlRaw A B)).le Ec := by
    refine image_min (inlRaw A B) Ec ⟨l₁, ?_⟩
    show l₁ ≫ (e ≫ coprodArr A B) = inlRaw A B
    rw [← Cat.assoc, hl₁, coprodInl_arr]
  have him_r : (image (inrRaw A B)).le Ec := by
    refine image_min (inrRaw A B) Ec ⟨l₂, ?_⟩
    show l₂ ≫ (e ≫ coprodArr A B) = inrRaw A B
    rw [← Cat.assoc, hl₂, coprodInr_arr]
  -- the carrier (union of the two images) lies in Ec.
  have hcarrier_le : (coprodSub A B).le Ec := HasSubobjectUnions.union_min _ _ _ him_l him_r
  -- coprodSub = ⟨coprodObj, coprodArr⟩, so we get j : coprodObj → E with j ≫ (e ≫ coprodArr) = coprodArr.
  obtain ⟨j, hj⟩ := hcarrier_le
  -- j ≫ e = id (coprodArr monic), so e is split epi; combined with monic ⇒ e iso.
  have hje : j ≫ e = Cat.id (coprodObj A B) := by
    apply coprodArr_monic A B
    rw [Cat.assoc]
    show (j ≫ (e ≫ coprodArr A B)) = Cat.id (coprodObj A B) ≫ coprodArr A B
    rw [Cat.id_comp]
    exact hj
  -- j ≫ e = id (coprodObj); compose with the equalizer identity to cancel.
  have heq_hk : e ≫ h = e ≫ k := eqMap_eq h k
  calc h = (j ≫ e) ≫ h := by rw [hje]; exact (Cat.id_comp h).symm
    _ = j ≫ (e ≫ h) := (Cat.assoc _ _ _)
    _ = j ≫ (e ≫ k) := by rw [heq_hk]
    _ = (j ≫ e) ≫ k := (Cat.assoc _ _ _).symm
    _ = k := by rw [hje]; exact Cat.id_comp k

/-! ### Copairing `case f g` via the partial-map classifier of `X`

  Given `f : A → X`, `g : B → X`, pick a lawful PMC `(X̃, η : X ↪ X̃)` for `X`.  The two
  injections are monic, so `f`/`g` are genuine partial maps `A+B ⇀ X`:
    `Pf := ⟨A, coprodInl, f⟩`,  `Pg := ⟨B, coprodInr, g⟩`.
  Their classifiers `χf := classify Pf`, `χg := classify Pg : A+B → X̃` satisfy the β-square
    `coprodInl ≫ χf = f ≫ η`,  `coprodInr ≫ χg = g ≫ η`.  -/

/-- The left partial map `A+B ⇀ X` carried by `f` (defined on the `inl` copy of `A`). -/
noncomputable def casePMf {A B X : 𝒞} (f : A ⟶ X) : PartialMap 𝒞 (coprodObj A B) X :=
  ⟨A, coprodInl A B, coprodInl_monic A B, f⟩

/-- The right partial map `A+B ⇀ X` carried by `g`. -/
noncomputable def casePMg {A B X : 𝒞} (g : B ⟶ X) : PartialMap 𝒞 (coprodObj A B) X :=
  ⟨B, coprodInr A B, coprodInr_monic A B, g⟩

/-- The β-square for the left partial map: `coprodInl ≫ classify Pf = f ≫ η`. -/
theorem casePMf_sq {A B X : 𝒞} (L : LawfulPMC 𝒞 X) (f : A ⟶ X) :
    coprodInl A B ≫ L.classify (casePMf (B := B) f) = f ≫ L.eta :=
  L.classify_sq (casePMf (B := B) f)

theorem casePMg_sq {A B X : 𝒞} (L : LawfulPMC 𝒞 X) (g : B ⟶ X) :
    coprodInr A B ≫ L.classify (casePMg (A := A) g) = g ≫ L.eta :=
  L.classify_sq (casePMg (A := A) g)

end Freyd
