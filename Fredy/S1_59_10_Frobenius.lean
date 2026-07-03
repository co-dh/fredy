/-
  Freyd & Scedrov, *Categories and Allegories* §1.59(10)

  The image–preimage adjunction on subobject lattices and the **projection
  (Frobenius) equation**.  For `f : A → B` the book gives the adjoint pair

      f  : Sub(A) → Sub(B)   (direct image),
      f* : Sub(B) → Sub(A)   (inverse image / preimage)

  and the two further equations

      (I)   f (A' ∩ f* B') = (f A') ∩ B'          -- projection / Frobenius reciprocity
      (II)  f* (f A' ∪ B') = A' ∪ f* B'.

  This file works in a bare `RegularCategory 𝒞` (weaker than abelian) and delivers:

    * the Galois adjunction  `f ⊣ f*`  :  `(f_* S).le T ↔ S.le (f^* T)`   (`directImage_adj`),
    * equation (I) as an equality of subobjects (mutual `Subobject.le`)     (`frobenius_eq`),
    * the easy half of (II)  `A' ∪ f* B' ≤ f* (f A' ∪ B')`                  (`join_le_inverseImage`).

  Infra reused:  `DirectImage` (S1_70, = `image (S.arr ≫ f)`), `InverseImage` (S1_60,
  pullback along `f`), `Subobject.inter` (S1_62, the pullback meet), `image`/`image_min`/
  `Cover`/`cover_pullback` (S1_51/S1_52).  Nothing edited outside this file.

  Composition is diagram order: `x ≫ y` is first `x` then `y`.
-/

import Fredy.S1_70
import Fredy.S1_658_Complement

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

namespace Frobenius

/-! ## The two bridge lemmas and the adjunction `f ⊣ f*` -/

/-- If `I ≤ Z` and `I` allows `g`, then `Z` allows `g` (compose the two factorings). -/
theorem allows_of_le {B : 𝒞} {I Z : Subobject 𝒞 B} {A : 𝒞} {g : A ⟶ B}
    (hIZ : I.le Z) (hg : Allows I g) : Allows Z g := by
  obtain ⟨k, hk⟩ := hIZ; obtain ⟨w, hw⟩ := hg
  exact ⟨w ≫ k, by rw [Cat.assoc, hk, hw]⟩

/-- **Direct-image bridge.**  `(f_* S).le T ↔ T` allows `S.arr ≫ f`.
    `f_* S` is the image of `S.arr ≫ f`, so this is just image minimality (`←`)
    together with the image's own allowance transported up a `≤` (`→`). -/
theorem directImage_le_iff [HasImages 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (S : Subobject 𝒞 A) (T : Subobject 𝒞 B) :
    (DirectImage f S).le T ↔ Allows T (S.arr ≫ f) := by
  constructor
  · intro h; exact allows_of_le h (image_allows (S.arr ≫ f))
  · intro h; exact image_min (S.arr ≫ f) T h

/-- **Inverse-image bridge.**  `S.le (f^* T) ↔ T` allows `S.arr ≫ f`.
    `f^* T` is the pullback of `T.arr` along `f`; the two directions are the two
    halves of the pullback's universal property. -/
theorem le_inverseImage_iff [HasPullbacks 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (S : Subobject 𝒞 A) (T : Subobject 𝒞 B) :
    S.le (InverseImage f T) ↔ Allows T (S.arr ≫ f) := by
  have hw := (HasPullbacks.has f T.arr).cone.w  -- π₁ ≫ f = π₂ ≫ T.arr
  constructor
  · rintro ⟨k, hk⟩
    -- `(f^* T).arr` is definitionally `π₁`, so `hk : k ≫ π₁ = S.arr`.
    have hk' : k ≫ (HasPullbacks.has f T.arr).cone.π₁ = S.arr := hk
    refine ⟨k ≫ (HasPullbacks.has f T.arr).cone.π₂, ?_⟩
    calc (k ≫ (HasPullbacks.has f T.arr).cone.π₂) ≫ T.arr
        = k ≫ ((HasPullbacks.has f T.arr).cone.π₂ ≫ T.arr) := Cat.assoc _ _ _
      _ = k ≫ ((HasPullbacks.has f T.arr).cone.π₁ ≫ f) := by rw [hw]
      _ = (k ≫ (HasPullbacks.has f T.arr).cone.π₁) ≫ f := (Cat.assoc _ _ _).symm
      _ = S.arr ≫ f := by rw [hk']
  · rintro ⟨h, hh⟩
    -- cone `⟨S.dom, S.arr, h⟩` over `(f, T.arr)`; lift into the pullback.
    refine ⟨(HasPullbacks.has f T.arr).lift ⟨S.dom, S.arr, h, hh.symm⟩, ?_⟩
    exact (HasPullbacks.has f T.arr).lift_fst _

/-- **The Galois adjunction `f ⊣ f*`** (direct image left adjoint to inverse image):
    `(f_* S).le T ↔ S.le (f^* T)`.  Immediate from the two bridge lemmas. -/
theorem directImage_adj [HasImages 𝒞] [HasPullbacks 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (S : Subobject 𝒞 A) (T : Subobject 𝒞 B) :
    (DirectImage f S).le T ↔ S.le (InverseImage f T) :=
  (directImage_le_iff f S T).trans (le_inverseImage_iff f S T).symm

/-- The **unit** `S ≤ f* (f_* S)` of the adjunction. -/
theorem le_inverseImage_directImage [HasImages 𝒞] [HasPullbacks 𝒞] {A B : 𝒞}
    (f : A ⟶ B) (S : Subobject 𝒞 A) : S.le (InverseImage f (DirectImage f S)) :=
  (directImage_adj f S (DirectImage f S)).mp (Subobject.le_refl _)

/-- Direct image is monotone: `S ≤ S' ⟹ f_* S ≤ f_* S'`. -/
theorem directImage_mono [HasImages 𝒞] {A B : 𝒞} (f : A ⟶ B)
    {S S' : Subobject 𝒞 A} (h : S.le S') : (DirectImage f S).le (DirectImage f S') := by
  refine (directImage_le_iff f S (DirectImage f S')).mpr ?_
  obtain ⟨k, hk⟩ := h                          -- k ≫ S'.arr = S.arr
  obtain ⟨w, hw⟩ := image_allows (S'.arr ≫ f)  -- w ≫ (f_* S').arr = S'.arr ≫ f
  have hw' : w ≫ (DirectImage f S').arr = S'.arr ≫ f := hw
  refine ⟨k ≫ w, ?_⟩
  calc (k ≫ w) ≫ (DirectImage f S').arr
      = k ≫ (w ≫ (DirectImage f S').arr) := Cat.assoc _ _ _
    _ = k ≫ (S'.arr ≫ f) := by rw [hw']
    _ = (k ≫ S'.arr) ≫ f := (Cat.assoc _ _ _).symm
    _ = S.arr ≫ f := by rw [hk]

/-! ## Meet laws, PreLogos-free

  `Subobject.inter` (S1_62) needs only `[HasPullbacks]`, but its meet lemmas
  `Subobject.inter_le_left`/`inter_le_right`/`le_inter` were compiled with a
  spurious ambient `[PreLogos 𝒞]` section hypothesis.  An abelian category is
  regular but generally NOT a pre-logos (its subobject lattices are modular, not
  distributive), so §1.59(10) must avoid `PreLogos`.  We reprove the three laws
  with `[HasPullbacks]` alone (same pullback-cone proofs as S1_62). -/

theorem inter_le_left [HasPullbacks 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B) :
    (Subobject.inter S T).le S :=
  ⟨(HasPullbacks.has S.arr T.arr).cone.π₁, rfl⟩

theorem inter_le_right [HasPullbacks 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B) :
    (Subobject.inter S T).le T :=
  ⟨(HasPullbacks.has S.arr T.arr).cone.π₂, ((HasPullbacks.has S.arr T.arr).cone.w).symm⟩

theorem le_inter [HasPullbacks 𝒞] {B : 𝒞} {X S T : Subobject 𝒞 B}
    (hS : X.le S) (hT : X.le T) : X.le (Subobject.inter S T) := by
  obtain ⟨p, hp⟩ := hS; obtain ⟨q, hq⟩ := hT
  let pb := HasPullbacks.has S.arr T.arr
  let c : Cone S.arr T.arr := { pt := X.dom, π₁ := p, π₂ := q, w := by rw [hp, hq] }
  refine ⟨pb.lift c, ?_⟩
  show pb.lift c ≫ (pb.cone.π₁ ≫ S.arr) = X.arr
  rw [← Cat.assoc, pb.lift_fst c]; exact hp

/-! ## Cover-descent lemma and equation (I) -/

/-- **Cover descent.**  If `c : W → Y.dom` is a cover and `Z` allows `c ≫ Y.arr`,
    then `Y ≤ Z`.  (`Y` is the image of `c ≫ Y.arr` because `c` is a cover onto the
    monic `Y.arr`; image minimality then puts `Y` below any `Z` that allows the
    composite.)  This is where regularity enters equation (I). -/
theorem le_of_cover_allows [HasImages 𝒞] {B : 𝒞} {Y Z : Subobject 𝒞 B} {W : 𝒞}
    {c : W ⟶ Y.dom} (hc : Cover c) (h : Allows Z (c ≫ Y.arr)) : Y.le Z := by
  obtain ⟨kY, hkY⟩ := image_min (c ≫ Y.arr) Y ⟨c, rfl⟩   -- kY ≫ Y.arr = (image _).arr
  obtain ⟨kZ, hkZ⟩ := image_min (c ≫ Y.arr) Z h          -- kZ ≫ Z.arr = (image _).arr
  obtain ⟨e', he'⟩ := image_allows (c ≫ Y.arr)           -- e' ≫ (image _).arr = c ≫ Y.arr
  -- `kY` is monic (it composes with the monic `Y.arr`).
  have hkY_monic : Monic kY := by
    intro X u v huv
    apply (image (c ≫ Y.arr)).monic
    rw [← hkY]
    calc u ≫ (kY ≫ Y.arr) = (u ≫ kY) ≫ Y.arr := (Cat.assoc _ _ _).symm
      _ = (v ≫ kY) ≫ Y.arr := by rw [huv]
      _ = v ≫ (kY ≫ Y.arr) := Cat.assoc _ _ _
  -- `e' ≫ kY = c`, so the cover `c` factors through the monic `kY`; hence `kY` is iso.
  have he'kY : e' ≫ kY = c := Y.monic _ _ (by
    calc (e' ≫ kY) ≫ Y.arr = e' ≫ (kY ≫ Y.arr) := Cat.assoc _ _ _
      _ = e' ≫ (image (c ≫ Y.arr)).arr := by rw [hkY]
      _ = c ≫ Y.arr := he')
  obtain ⟨kYinv, _hkY1, hkY2⟩ := hc kY e' hkY_monic he'kY
  -- `Y ≤ image ≤ Z`, using `kYinv` for the first and `kZ` for the second step.
  exact ⟨kYinv ≫ kZ, by
    calc (kYinv ≫ kZ) ≫ Z.arr = kYinv ≫ (kZ ≫ Z.arr) := Cat.assoc _ _ _
      _ = kYinv ≫ (image (c ≫ Y.arr)).arr := by rw [hkZ]
      _ = kYinv ≫ (kY ≫ Y.arr) := by rw [← hkY]
      _ = (kYinv ≫ kY) ≫ Y.arr := (Cat.assoc _ _ _).symm
      _ = Cat.id Y.dom ≫ Y.arr := by rw [hkY2]
      _ = Y.arr := Cat.id_comp _⟩

/-- Equation (I), easy half:  `f (A' ∩ f* B') ≤ (f A') ∩ B'`.
    Both components come for free: monotonicity of `f_*` for the `f A'` factor and
    the adjunction for the `B'` factor. -/
theorem frobenius_le [HasImages 𝒞] [HasPullbacks 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (S : Subobject 𝒞 A) (T : Subobject 𝒞 B) :
    (DirectImage f (Subobject.inter S (InverseImage f T))).le
      (Subobject.inter (DirectImage f S) T) :=
  le_inter
    (directImage_mono f (inter_le_left S (InverseImage f T)))
    ((directImage_adj f (Subobject.inter S (InverseImage f T)) T).mpr
      (inter_le_right S (InverseImage f T)))

/-- Equation (I), hard half:  `(f A') ∩ B' ≤ f (A' ∩ f* B')`.  This is where
    regularity is used: pull the image-cover `e : A' ↠ f A'` back along the meet
    projection `p₁ : (f A' ∩ B') → f A'`; the opposite leg `qF` is again a cover
    (`cover_pullback`), and its source maps into `A' ∩ f* B'`, so cover-descent
    (`le_of_cover_allows`) puts `f A' ∩ B'` below `f (A' ∩ f* B')`. -/
theorem frobenius_ge [RegularCategory 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (S : Subobject 𝒞 A) (T : Subobject 𝒞 B) :
    (Subobject.inter (DirectImage f S) T).le
      (DirectImage f (Subobject.inter S (InverseImage f T))) := by
  -- image cover `e : S.dom ↠ (f_* S).dom`.
  let e := image.lift (S.arr ≫ f)
  have he' : e ≫ (DirectImage f S).arr = S.arr ≫ f := image.lift_fac (S.arr ≫ f)
  have hcov_e : Cover e := image_lift_cover (S.arr ≫ f)
  -- meet pullback `pb1` (legs p1,p2) and its base-change `pb2 = pullback of (e, p1)`.
  let pb1 := HasPullbacks.has (DirectImage f S).arr T.arr
  let p1 := pb1.cone.π₁; let p2 := pb1.cone.π₂
  have hp1w : p1 ≫ (DirectImage f S).arr = p2 ≫ T.arr := pb1.cone.w
  let pb2 := HasPullbacks.has e p1
  let q1 := pb2.cone.π₁; let qF := pb2.cone.π₂
  have hqF_p1 : q1 ≫ e = qF ≫ p1 := pb2.cone.w
  have hcov_qF : Cover qF := cover_pullback p1 hcov_e
  refine le_of_cover_allows hcov_qF ?_
  -- key composite: `(q1 ≫ S.arr) ≫ f = (qF ≫ p2) ≫ T.arr`.
  have hcomp : (q1 ≫ S.arr) ≫ f = (qF ≫ p2) ≫ T.arr := by
    calc (q1 ≫ S.arr) ≫ f = q1 ≫ (S.arr ≫ f) := Cat.assoc _ _ _
      _ = q1 ≫ (e ≫ (DirectImage f S).arr) := by rw [he']
      _ = (q1 ≫ e) ≫ (DirectImage f S).arr := (Cat.assoc _ _ _).symm
      _ = (qF ≫ p1) ≫ (DirectImage f S).arr := by rw [hqF_p1]
      _ = qF ≫ (p1 ≫ (DirectImage f S).arr) := Cat.assoc _ _ _
      _ = qF ≫ (p2 ≫ T.arr) := by rw [hp1w]
      _ = (qF ≫ p2) ≫ T.arr := (Cat.assoc _ _ _).symm
  -- `q1 ≫ S.arr` factors through `f* T` (pullback UMP), hence through `S ∩ f* T`.
  let cwp : Cone f T.arr := ⟨pb2.cone.pt, q1 ≫ S.arr, qF ≫ p2, hcomp⟩
  let wp := (HasPullbacks.has f T.arr).lift cwp
  have hwp : wp ≫ (InverseImage f T).arr = q1 ≫ S.arr := (HasPullbacks.has f T.arr).lift_fst cwp
  let cw : Cone S.arr (InverseImage f T).arr := ⟨pb2.cone.pt, q1, wp, hwp.symm⟩
  let w := (HasPullbacks.has S.arr (InverseImage f T).arr).lift cw
  have hwW : w ≫ (Subobject.inter S (InverseImage f T)).arr = q1 ≫ S.arr := by
    show w ≫ ((HasPullbacks.has S.arr (InverseImage f T).arr).cone.π₁ ≫ S.arr) = q1 ≫ S.arr
    rw [← Cat.assoc, (HasPullbacks.has S.arr (InverseImage f T).arr).lift_fst cw]
  -- factor `qF ≫ (f A' ∩ B').arr` through `f_* (S ∩ f* T)`.
  obtain ⟨eW, heW⟩ := image_allows ((Subobject.inter S (InverseImage f T)).arr ≫ f)
  have heW' : eW ≫ (DirectImage f (Subobject.inter S (InverseImage f T))).arr
      = (Subobject.inter S (InverseImage f T)).arr ≫ f := heW
  refine ⟨w ≫ eW, ?_⟩
  calc (w ≫ eW) ≫ (DirectImage f (Subobject.inter S (InverseImage f T))).arr
      = w ≫ (eW ≫ (DirectImage f (Subobject.inter S (InverseImage f T))).arr) := Cat.assoc _ _ _
    _ = w ≫ ((Subobject.inter S (InverseImage f T)).arr ≫ f) := by rw [heW']
    _ = (w ≫ (Subobject.inter S (InverseImage f T)).arr) ≫ f := (Cat.assoc _ _ _).symm
    _ = (q1 ≫ S.arr) ≫ f := by rw [hwW]
    _ = q1 ≫ (S.arr ≫ f) := Cat.assoc _ _ _
    _ = q1 ≫ (e ≫ (DirectImage f S).arr) := by rw [he']
    _ = (q1 ≫ e) ≫ (DirectImage f S).arr := (Cat.assoc _ _ _).symm
    _ = (qF ≫ p1) ≫ (DirectImage f S).arr := by rw [hqF_p1]
    _ = qF ≫ (p1 ≫ (DirectImage f S).arr) := Cat.assoc _ _ _

/-- **Equation (I) — the projection / Frobenius equation**, as an equality of
    subobjects (mutual `Subobject.le`):

        f (A' ∩ f* B')  =  (f A') ∩ B'.

    This is Frobenius reciprocity for the image–preimage adjunction, valid in any
    regular category. -/
theorem frobenius_eq [RegularCategory 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (S : Subobject 𝒞 A) (T : Subobject 𝒞 B) :
    (DirectImage f (Subobject.inter S (InverseImage f T))).le (Subobject.inter (DirectImage f S) T)
    ∧ (Subobject.inter (DirectImage f S) T).le
        (DirectImage f (Subobject.inter S (InverseImage f T))) :=
  ⟨frobenius_le f S T, frobenius_ge f S T⟩

/-- Equation (I) with the two sides identified by a genuine domain isomorphism
    commuting with the two monics into `B` (`Subobject.le_antisymm_iso`). -/
theorem frobenius_iso [RegularCategory 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (S : Subobject 𝒞 A) (T : Subobject 𝒞 B) :
    ∃ e : (DirectImage f (Subobject.inter S (InverseImage f T))).dom
            ⟶ (Subobject.inter (DirectImage f S) T).dom,
      IsIso e ∧ e ≫ (Subobject.inter (DirectImage f S) T).arr
        = (DirectImage f (Subobject.inter S (InverseImage f T))).arr :=
  Subobject.le_antisymm_iso (frobenius_le f S T) (frobenius_ge f S T)

/-! ## Equation (II): the easy half, and what is open -/

/-- Equation (II), easy half:  `A' ∪ f* B' ≤ f* (f A' ∪ B')`.
    Both joinands sit below the right side: `A' ≤ f* f A' ≤ f* (f A' ∪ B')`
    (adjunction unit + `f*` monotone) and `f* B' ≤ f* (f A' ∪ B')` (`f*` monotone).
    Holds in any regular category with subobject unions. -/
theorem join_le_inverseImage [RegularCategory 𝒞] [HasSubobjectUnions 𝒞] {A B : 𝒞}
    (f : A ⟶ B) (S : Subobject 𝒞 A) (T : Subobject 𝒞 B) :
    (HasSubobjectUnions.union S (InverseImage f T)).le
      (InverseImage f (HasSubobjectUnions.union (DirectImage f S) T)) :=
  HasSubobjectUnions.union_min _ _ _
    (Subobject.le_trans (le_inverseImage_directImage f S)
      (inverseImage_mono f (HasSubobjectUnions.union_left (DirectImage f S) T)))
    (inverseImage_mono f (HasSubobjectUnions.union_right (DirectImage f S) T))

/-! **What (II) needs and why the reverse fails regularly.**  The reverse inequality
    `f* (f A' ∪ B') ≤ A' ∪ f* B'` — hence the full equation (II) and the modular-lattice
    corollary for `f` monic — is NOT a regular-category fact.  It already fails in
    **Set** (a topos, hence a logos): for `f : {0,1} → {∗}`, `A' = {0}`, `B' = ∅`, the
    left side is `f⁻¹({∗}) = {0,1}` but the right side is `{0}`.  It is specifically an
    ABELIAN phenomenon, resting on `f* (f A') = A' ∪ f* 0` (the kernel `f* 0` is absorbed
    into `A'`), which needs additive/kernel structure this file does not assume.  We
    therefore leave (II)-reverse and the modular corollary OPEN here. -/

end Frobenius
end Freyd
