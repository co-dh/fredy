/-
  §1.63 union condition for the FILTERED LAX colimit of positive pre-logoi (`laxColimCat L hL`).

  The lax port of `Colim.colimit_invImage_union_le` (`Fredy/ColimitInvImageUnion.lean`): the HARD
  direction of Freyd's §1.63 union condition,

      `f#(S ∪ T) ≤ f#S ∪ f#T`     (`laxColim_invImage_union_le`),

  for subobjects of an object `B` of the lax colimit, where union is built from
  `laxColimHasBinaryCoproducts` + the lax images via `hasSubobjectUnions_of_coproducts_images`, and
  `InverseImage` is the §1.432 pullback.

  STRATEGY.  Same germ-transport skeleton as the strict file, with one extra ingredient forced by the
  bare-Σ object carrier of the LAX colimit: there is NO object quotient, so the strict trick of
  `subst`-ing `A = objIncl N xA`, `B = objIncl N xB` is unavailable (`⟨N, F x⟩ ≠ ⟨iA, x⟩` on the
  nose, only iso).  Instead every datum (`A`, `B`, `S.dom`, `T.dom`) is moved to a common stage `N` by
  the canonical STAGE-ADVANCE isos `dA`/`dB`/`dSd`/`dTd` (`homInclL_isIso_of_rep`), and subobjects are
  transported across these isos by the generic `subConj` (post-compose the subobject arrow with an
  iso of the base).  `subConj` commutes (up to `≈`) with union (`subConj_union_equiv`) and with the
  inverse image on the codomain (`invImage_subConj_equiv`) and the domain (`invImage_iso_precomp_equiv`),
  built from the already-available pullback-transport lemmas `isPullback_of_iso_cospan` /
  `pullback_subobject_equiv` (`Fredy/S1_43`, `Fredy/ColimitInvImageUnion`).

  The per-stage germ-preservation steps reuse the committed lax keystones verbatim:
    * inverse image is a pullback, `objIncl N` preserves pullbacks (`objInclL_preserves_pullbacks`);
    * union is the image of a copairing, `objIncl N` preserves coproducts + images
      (`objInclL_preserves_coproducts`, `objInclL_preserves_images`);
    * `stageInclL` sends a stage `Subobject.le` to a colimit one (`germSubL_le`).
  The stage hard direction is the generic `stage_invImage_union_le` (per-stage `PreLogos`).

  All generic uniqueness lemmas (`Subobject.Equiv`, `pullback_subobject_equiv`, `union_equiv_image_case`,
  `image_equiv_isImage`, `isImage_precomp_iso`, `pbSub`, `unionImg`, `stage_invImage_union_le`, …) are
  IMPORTED from `Fredy/ColimitInvImageUnion.lean` — they are pure category theory and apply to the lax
  colimit unchanged.  Mathlib-free.  Single universe `{w, w}` (the equalizer-derived pullback germ).
-/
import Fredy.S1_63_ColimitInvImageUnion
import Fredy.S1_543_LaxGermPullbacks
import Fredy.S1_543_LaxGermCoproduct
import Fredy.S1_543_LaxGermImages
import Fredy.S1_543_LaxColimitImages
import Fredy.S1_543_UnionFromCoproduct

open Freyd
open Freyd.Colim
open Freyd.LaxColim

/-! ## PART A — generic subobject transport along an iso of the base (`subConj`)

  None of these mention the colimit; they are §1.5 category theory.  `subConj e he S` post-composes a
  subobject's arrow with an iso `e : B → B'`, giving a subobject of `B'`.  It is monotone, respects
  `≈`, cancels its inverse, commutes with the inverse image on either side, and commutes with unions.
  These are the bridge lemmas that replace the strict `subst`. -/

namespace Freyd

universe v u
variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- A mono post-composed with an iso is mono. -/
theorem monic_postcomp_iso {X Y Z : 𝒞} {f : X ⟶ Y} {j : Y ⟶ Z}
    (hf : Monic f) (hj : IsIso j) : Monic (f ≫ j) := by
  obtain ⟨jj, hj1, _⟩ := hj
  intro W u v huv
  apply hf
  have := congrArg (fun t => t ≫ jj) huv
  simpa only [Cat.assoc, hj1, Cat.comp_id] using this

/-- Transport a subobject `S ⊆ B` along an iso `e : B → B'` (post-compose the arrow). -/
def subConj {B B' : 𝒞} (e : B ⟶ B') (he : IsIso e) (S : Subobject 𝒞 B) : Subobject 𝒞 B' :=
  Subobject.mk S.dom (S.arr ≫ e) (monic_postcomp_iso S.monic he)

theorem subConj_arr {B B' : 𝒞} (e : B ⟶ B') (he : IsIso e) (S : Subobject 𝒞 B) :
    (subConj e he S).arr = S.arr ≫ e := rfl

/-- `subConj` is monotone for `Subobject.le`. -/
theorem subConj_le {B B' : 𝒞} (e : B ⟶ B') (he : IsIso e) {S T : Subobject 𝒞 B}
    (h : S.le T) : (subConj e he S).le (subConj e he T) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by
    show k ≫ (T.arr ≫ e) = S.arr ≫ e
    rw [← Cat.assoc, hk]⟩

theorem subConj_equiv {B B' : 𝒞} (e : B ⟶ B') (he : IsIso e) {S T : Subobject 𝒞 B}
    (h : S.Equiv T) : (subConj e he S).Equiv (subConj e he T) :=
  ⟨subConj_le e he h.1, subConj_le e he h.2⟩

/-- Conjugating by `e` then its inverse `e'` returns the original subobject (up to `≈`). -/
theorem subConj_cancel {B B' : 𝒞} (e : B ⟶ B') (e' : B' ⟶ B)
    (he : IsIso e) (he' : IsIso e') (h2 : e' ≫ e = Cat.id B')
    (U : Subobject 𝒞 B') : (subConj e he (subConj e' he' U)).Equiv U := by
  refine ⟨⟨Cat.id U.dom, ?_⟩, ⟨Cat.id U.dom, ?_⟩⟩
  · show Cat.id U.dom ≫ U.arr = (U.arr ≫ e') ≫ e
    rw [Cat.id_comp, Cat.assoc, h2, Cat.comp_id]
  · show Cat.id U.dom ≫ (U.arr ≫ e') ≫ e = U.arr
    rw [Cat.id_comp, Cat.assoc, h2, Cat.comp_id]

/-- **Inverse image commutes with codomain conjugation.**  `f#(X)` over `A` equals (up to `≈`) the
    inverse image of the conjugated subobject `subConj e he X ⊆ B'` along `f ≫ e`.  The chosen
    pullback of `(f, X.arr)` is, by `isPullback_of_iso_cospan`, also a pullback of `(f≫e, X.arr≫e)`. -/
theorem invImage_subConj_equiv [HasPullbacks 𝒞] {A B B' : 𝒞} (f : A ⟶ B)
    (e : B ⟶ B') (he : IsIso e) (X : Subobject 𝒞 B) :
    (InverseImage f X).Equiv (InverseImage (f ≫ e) (subConj e he X)) := by
  have hecopy := he
  obtain ⟨e', h1, _⟩ := hecopy
  let c := (HasPullbacks.has f X.arr).cone
  have hcPB : c.IsPullback := HasPullback.cone_isPullback (HasPullbacks.has f X.arr)
  have hw : c.π₁ ≫ (f ≫ e) = c.π₂ ≫ (X.arr ≫ e) := by
    rw [← Cat.assoc, ← Cat.assoc, c.w]
  have hc2 : (Cone.mk (f := f ≫ e) (g := X.arr ≫ e) c.pt c.π₁ c.π₂ hw).IsPullback :=
    isPullback_of_iso_cospan hcPB e e' h1 hw
  have hc' : (HasPullbacks.has (f ≫ e) (subConj e he X).arr).cone.IsPullback :=
    HasPullback.cone_isPullback _
  exact pullback_subobject_equiv hc2 hc' (InverseImage f X).monic
    (InverseImage (f ≫ e) (subConj e he X)).monic

/-- **Inverse image commutes with domain conjugation.**  Pre-composing `g : A'' → B` with an iso
    `d : A → A''` (inverse `e' : A'' → A`) pulls the inverse image back across `e'`:
    `(d ≫ g)#(Y) ≈ subConj e' (g#(Y))`.  Hand-built pullback (pullback pasting through the iso). -/
theorem invImage_iso_precomp_equiv [HasPullbacks 𝒞] {A A'' B : 𝒞}
    (d : A ⟶ A'') (e' : A'' ⟶ A) (h1 : d ≫ e' = Cat.id A) (h2 : e' ≫ d = Cat.id A'')
    (g : A'' ⟶ B) (Y : Subobject 𝒞 B) :
    (InverseImage (d ≫ g) Y).Equiv (subConj e' ⟨d, h2, h1⟩ (InverseImage g Y)) := by
  let c := (HasPullbacks.has g Y.arr).cone
  have hcPB : c.IsPullback := HasPullback.cone_isPullback (HasPullbacks.has g Y.arr)
  have hwc2 : (c.π₁ ≫ e') ≫ (d ≫ g) = c.π₂ ≫ Y.arr := by
    rw [Cat.assoc, ← Cat.assoc e' d g, h2, Cat.id_comp]; exact c.w
  have hc2PB : (Cone.mk (f := d ≫ g) (g := Y.arr) c.pt (c.π₁ ≫ e') c.π₂ hwc2).IsPullback := by
    intro dd
    have hdw : (dd.π₁ ≫ d) ≫ g = dd.π₂ ≫ Y.arr := by rw [Cat.assoc]; exact dd.w
    obtain ⟨u, ⟨hu1, hu2⟩, huniq⟩ := hcPB ⟨dd.pt, dd.π₁ ≫ d, dd.π₂, hdw⟩
    refine ⟨u, ⟨?_, hu2⟩, ?_⟩
    · show u ≫ (c.π₁ ≫ e') = dd.π₁
      rw [← Cat.assoc, hu1, Cat.assoc, h1, Cat.comp_id]
    · intro v hv1 hv2
      apply huniq
      · -- v ≫ c.π₁ = dd.π₁ ≫ d : post-compose `hv1` by `d` and cancel `e' ≫ d = id`.
        have hvd : (v ≫ (c.π₁ ≫ e')) ≫ d = dd.π₁ ≫ d := by rw [hv1]
        rw [Cat.assoc, Cat.assoc, h2, Cat.comp_id] at hvd
        exact hvd
      · exact hv2
  have hc' : (HasPullbacks.has (d ≫ g) Y.arr).cone.IsPullback := HasPullback.cone_isPullback _
  exact pullback_subobject_equiv hc' hc2PB (InverseImage (d ≫ g) Y).monic
    (subConj e' ⟨d, h2, h1⟩ (InverseImage g Y)).monic

/-- Inverse image is monotone using ONLY `HasPullbacks` (avoids the `inverseImage_mono`
    terminal/product instances, so it never forces the `HasTerminal`/`HasBinaryProducts` diamond
    against `laxColimHasPullbacks`).  `S ≤ T` (mediator `k`) lifts the pullback of `(f, S.arr)` to the
    pullback of `(f, T.arr)`. -/
theorem invImage_le_of_le [HasPullbacks 𝒞] {A B : 𝒞} (f : A ⟶ B) {S T : Subobject 𝒞 B}
    (h : S.le T) : (InverseImage f S).le (InverseImage f T) := by
  obtain ⟨k, hk⟩ := h
  let cS := (HasPullbacks.has f S.arr).cone
  have hw : cS.π₁ ≫ f = (cS.π₂ ≫ k) ≫ T.arr := by rw [Cat.assoc, hk]; exact cS.w
  exact ⟨(HasPullbacks.has f T.arr).lift ⟨cS.pt, cS.π₁, cS.π₂ ≫ k, hw⟩,
    (HasPullbacks.has f T.arr).lift_fst ⟨cS.pt, cS.π₁, cS.π₂ ≫ k, hw⟩⟩

theorem invImage_equiv_pb [HasPullbacks 𝒞] {A B : 𝒞} (f : A ⟶ B) {S T : Subobject 𝒞 B}
    (h : S.Equiv T) : (InverseImage f S).Equiv (InverseImage f T) :=
  ⟨invImage_le_of_le f h.1, invImage_le_of_le f h.2⟩

/-- **Conjugation commutes with binary union.**  `subConj e (S ∪ T) ≈ (subConj e S) ∪ (subConj e T)`:
    each side is the join of the two conjugated subobjects (joins are preserved by the order-iso
    `subConj e` / `subConj e'`). -/
theorem subConj_union_equiv [HasImages 𝒞] [HasSubobjectUnions 𝒞] {B B' : 𝒞}
    (e : B ⟶ B') (e' : B' ⟶ B) (he : IsIso e) (h1 : e ≫ e' = Cat.id B) (h2 : e' ≫ e = Cat.id B')
    (P Q : Subobject 𝒞 B) :
    (subConj e he (HasSubobjectUnions.union P Q)).Equiv
      (HasSubobjectUnions.union (subConj e he P) (subConj e he Q)) := by
  letI he' : IsIso e' := ⟨e, h2, h1⟩
  refine ⟨?_, ?_⟩
  · -- subConj e (P∪Q) ≤ (subConj e P) ∪ (subConj e Q):  transport competitors back by `e'`.
    -- It suffices that P ≤ subConj e' U' and Q ≤ subConj e' U' for U' := (subConj e P)∪(subConj e Q).
    have hPU : P.le (subConj e' he' (HasSubobjectUnions.union (subConj e he P) (subConj e he Q))) :=
      Subobject.le_of_equiv_le (subConj_cancel e' e he' he h1 P).symm
        (subConj_le e' he' (HasSubobjectUnions.union_left (subConj e he P) (subConj e he Q)))
    have hQU : Q.le (subConj e' he' (HasSubobjectUnions.union (subConj e he P) (subConj e he Q))) :=
      Subobject.le_of_equiv_le (subConj_cancel e' e he' he h1 Q).symm
        (subConj_le e' he' (HasSubobjectUnions.union_right (subConj e he P) (subConj e he Q)))
    have hmin := HasSubobjectUnions.union_min P Q _ hPU hQU
    exact Subobject.le_of_le_equiv (subConj_le e he hmin)
      (subConj_cancel e e' he he' h2 (HasSubobjectUnions.union (subConj e he P) (subConj e he Q)))
  · exact HasSubobjectUnions.union_min _ _ _
      (subConj_le e he (HasSubobjectUnions.union_left P Q))
      (subConj_le e he (HasSubobjectUnions.union_right P Q))

end Freyd

/-! ## PART B — the lax germ subobject and the two germ-transport equivalences

  `germSubL X` is the `stageInclL`-germ of a stage subobject `X ⊆ y` (of `L.A N`), a subobject of
  `objIncl N y = ⟨N, y⟩` in the colimit — the lax mirror of `Colim.germSub`.  `invImage_germ_equivL` /
  `union_germ_equivL` are the lax mirrors of `Colim.invImage_germ_equiv` / `Colim.union_germ_equiv`,
  proved from the committed lax keystones `objInclL_preserves_pullbacks` /
  `objInclL_preserves_coproducts` / `objInclL_preserves_images`. -/

namespace Freyd.LaxColim

universe w
variable {ι : Type w} {D : Directed ι} (L : LaxCatSystem.{w, w} ι D) (hL : Coherent L)

/-- The lax mono-preservation bundle (shared shape of the germ keystones), abbreviated. -/
abbrev TransMonoL : Prop :=
  ∀ {i j : ι} (hij : D.le i j),
    @PreservesMono _ (L.catA i) _ (L.catA j) (L.F hij) (L.functF hij)

/-- The colimit subobject GERM of a stage subobject `X ⊆ y` (of `L.A N`): `⟨N, X.dom⟩ ↣ ⟨N, y⟩` via
    `stageInclL X.arr`, monic since transitions preserve `X.arr`'s mono.  Lax mirror of
    `Colim.germSub`; exactly the form produced by `objInclL_preserves_images`. -/
noncomputable def germSubL (hmono : TransMonoL L) {N : ι} {y : L.A N} (X : Subobject (L.A N) y) :
    letI : Cat (Obj L) := laxColimCat L hL
    Subobject (Obj L) (objIncl L N y) :=
  letI : Cat (Obj L) := laxColimCat L hL
  Subobject.mk (objIncl L N X.dom) (stageInclL L hL X.arr)
    (stageInclL_mono_of_stage L hL hmono X.arr X.monic)

theorem germSubL_arr (hmono : TransMonoL L) {N : ι} {y : L.A N} (X : Subobject (L.A N) y) :
    letI : Cat (Obj L) := laxColimCat L hL
    (germSubL L hL hmono X).arr = stageInclL L hL X.arr := rfl

/-- The germ functor is monotone: a stage `X ≤ Y` gives a colimit `germSubL X ≤ germSubL Y`. -/
theorem germSubL_le (hmono : TransMonoL L) {N : ι} {y : L.A N} {X Y : Subobject (L.A N) y}
    (h : X.le Y) :
    letI : Cat (Obj L) := laxColimCat L hL
    (germSubL L hL hmono X).le (germSubL L hL hmono Y) := by
  letI : Cat (Obj L) := laxColimCat L hL
  obtain ⟨k, hk⟩ := h
  refine ⟨stageInclL L hL k, ?_⟩
  have hX : stageInclL L hL (k ≫ Y.arr) = stageInclL L hL X.arr := by rw [hk]
  exact (stageInclL_comp L hL k Y.arr).symm.trans hX

theorem germSubL_equiv (hmono : TransMonoL L) {N : ι} {y : L.A N} {X Y : Subobject (L.A N) y}
    (h : X.le Y ∧ Y.le X) :
    letI : Cat (Obj L) := laxColimCat L hL
    (germSubL L hL hmono X).Equiv (germSubL L hL hmono Y) :=
  ⟨germSubL_le L hL hmono h.1, germSubL_le L hL hmono h.2⟩

/-! ### Transport E (lax) — inverse image is a germ -/

set_option maxHeartbeats 1000000 in
/-- **Lax `invImage_germ_equiv`.**  The colimit inverse image of a germ is the germ of the stage
    inverse image (a pullback): `(stageInclL f_N)#(germSubL X_N) ≈ germSubL (pbSub f_N X_N)`, via
    `objInclL_preserves_pullbacks` + `pullback_subobject_equiv`. -/
theorem invImage_germ_equivL (hmono : TransMonoL L) [Nonempty ι]
    (tData : LaxTerminalData L) (pData : LaxProductData L) (eqData : LaxEqualizerData L)
    [hpull : @HasPullbacks (Obj L) (laxColimCat L hL)]
    (N : ι) {xA xB : L.A N} (f_N : xA ⟶ xB) (X_N : Subobject (L.A N) xB) :
    letI : Cat (Obj L) := laxColimCat L hL
    letI : HasTerminal (L.A N) := tData.ht N
    letI : HasBinaryProducts (L.A N) := pData.hp N
    letI : HasEqualizers (L.A N) := eqData.he N
    (InverseImage (stageInclL L hL f_N) (germSubL L hL hmono X_N)).Equiv
      (germSubL L hL hmono (pbSub (tData.ht N) (pData.hp N) (eqData.he N) f_N X_N)) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasTerminal (L.A N) := tData.ht N
  letI : HasBinaryProducts (L.A N) := pData.hp N
  letI : HasEqualizers (L.A N) := eqData.he N
  have himgPB := objInclL_preserves_pullbacks L hL tData pData eqData N f_N X_N.arr
  have hcanon : (HasPullbacks.has (stageInclL L hL f_N)
      (germSubL L hL hmono X_N).arr).cone.IsPullback := HasPullback.cone_isPullback _
  exact pullback_subobject_equiv hcanon himgPB
    (InverseImage (stageInclL L hL f_N) (germSubL L hL hmono X_N)).monic
    (himgPB.pi1_monic (germSubL L hL hmono X_N).monic)

/-! ### Transport D (lax) — union is a germ -/

set_option maxHeartbeats 1000000 in
/-- **Lax `union_germ_equiv`.**  The colimit union of two germs is the germ of the stage union (image
    of a copairing): `(germSubL S_N) ∪ (germSubL T_N) ≈ germSubL (unionImg S_N T_N)`, via
    `objInclL_preserves_coproducts` + `objInclL_preserves_images` + `union_equiv_image_case`. -/
theorem union_germ_equivL (hmono : TransMonoL L) (coprData : LaxCoproductData L)
    (hi : ∀ i, @HasImages (L.A i) (L.catA i))
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        @Functor.map _ _ _ _ _ (L.functF hij) x y p
          = @Functor.map _ _ _ _ _ (L.functF hij) x y q → p = q)
    (himgpres : ∀ {i j : ι} (hij : D.le i j) {X Y : L.A i} (f : X ⟶ Y),
        @IsImage (L.A j) (L.catA j) _ _ (@Functor.map _ _ _ _ _ (L.functF hij) X Y f)
          (@Subobject.map _ _ (L.catA i) (L.catA j) (L.F hij) (L.functF hij) (hmono hij) _
            (@image _ (L.catA i) (hi i) _ _ f)))
    [hpull : @HasPullbacks (Obj L) (laxColimCat L hL)]
    [hImg : @HasImages (Obj L) (laxColimCat L hL)]
    [hUn : @HasSubobjectUnions (Obj L) (laxColimCat L hL) hImg]
    (N : ι) {xB : L.A N} (S_N T_N : Subobject (L.A N) xB) :
    letI : Cat (Obj L) := laxColimCat L hL
    letI : HasImages (L.A N) := hi N
    letI : HasBinaryCoproducts (L.A N) := coprData.hcop N
    letI : HasBinaryCoproducts (Obj L) := laxColimHasBinaryCoproducts L hL coprData
    (HasSubobjectUnions.union (germSubL L hL hmono S_N) (germSubL L hL hmono T_N)).Equiv
      (germSubL L hL hmono (unionImg (hi N) (coprData.hcop N) S_N T_N)) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasImages (L.A N) := hi N
  letI : HasBinaryCoproducts (L.A N) := coprData.hcop N
  letI hcopC : HasBinaryCoproducts (Obj L) := laxColimHasBinaryCoproducts L hL coprData
  let cstage : (coprData.hcop N).coprod S_N.dom T_N.dom ⟶ xB :=
    HasBinaryCoproducts.case S_N.arr T_N.arr
  have hκ := objInclL_preserves_coproducts L hL coprData N S_N.dom T_N.dom
  let κ : @HasBinaryCoproducts.coprod (Obj L) (laxColimCat L hL) hcopC
      (objIncl L N S_N.dom) (objIncl L N T_N.dom)
      ⟶ objIncl L N ((coprData.hcop N).coprod S_N.dom T_N.dom) :=
    @HasBinaryCoproducts.case (Obj L) (laxColimCat L hL) hcopC
      (objIncl L N ((coprData.hcop N).coprod S_N.dom T_N.dom))
      (objIncl L N S_N.dom) (objIncl L N T_N.dom)
      (stageInclL L hL ((coprData.hcop N).inl (A := S_N.dom) (B := T_N.dom)))
      (stageInclL L hL ((coprData.hcop N).inr (A := S_N.dom) (B := T_N.dom)))
  have hD2 : HasBinaryCoproducts.case (germSubL L hL hmono S_N).arr (germSubL L hL hmono T_N).arr
      = κ ≫ stageInclL L hL cstage := by
    show @HasBinaryCoproducts.case (Obj L) (laxColimCat L hL) hcopC _ _ _
        (stageInclL L hL S_N.arr) (stageInclL L hL T_N.arr) = κ ≫ stageInclL L hL cstage
    refine Eq.symm (HasBinaryCoproducts.case_uniq (stageInclL L hL S_N.arr)
      (stageInclL L hL T_N.arr) (κ ≫ stageInclL L hL cstage) ?_ ?_)
    · show HasBinaryCoproducts.inl ≫ (κ ≫ stageInclL L hL cstage) = stageInclL L hL S_N.arr
      rw [← Cat.assoc, show (HasBinaryCoproducts.inl ≫ κ)
            = stageInclL L hL ((coprData.hcop N).inl (A := S_N.dom) (B := T_N.dom))
            from HasBinaryCoproducts.case_inl _ _]
      show @compL _ _ L hL (objIncl L N S_N.dom) (objIncl L N ((coprData.hcop N).coprod S_N.dom T_N.dom))
          (objIncl L N xB)
          (stageInclL L hL ((coprData.hcop N).inl (A := S_N.dom) (B := T_N.dom)))
          (stageInclL L hL cstage) = stageInclL L hL S_N.arr
      rw [← stageInclL_comp L hL ((coprData.hcop N).inl (A := S_N.dom) (B := T_N.dom)) cstage,
          show (coprData.hcop N).inl ≫ cstage = S_N.arr
            from HasBinaryCoproducts.case_inl S_N.arr T_N.arr]
    · show HasBinaryCoproducts.inr ≫ (κ ≫ stageInclL L hL cstage) = stageInclL L hL T_N.arr
      rw [← Cat.assoc, show (HasBinaryCoproducts.inr ≫ κ)
            = stageInclL L hL ((coprData.hcop N).inr (A := S_N.dom) (B := T_N.dom))
            from HasBinaryCoproducts.case_inr _ _]
      show @compL _ _ L hL (objIncl L N T_N.dom) (objIncl L N ((coprData.hcop N).coprod S_N.dom T_N.dom))
          (objIncl L N xB)
          (stageInclL L hL ((coprData.hcop N).inr (A := S_N.dom) (B := T_N.dom)))
          (stageInclL L hL cstage) = stageInclL L hL T_N.arr
      rw [← stageInclL_comp L hL ((coprData.hcop N).inr (A := S_N.dom) (B := T_N.dom)) cstage,
          show (coprData.hcop N).inr ≫ cstage = T_N.arr
            from HasBinaryCoproducts.case_inr S_N.arr T_N.arr]
  refine (union_equiv_image_case (germSubL L hL hmono S_N) (germSubL L hL hmono T_N)).trans ?_
  rw [hD2]
  refine (image_equiv_isImage
    (isImage_precomp_iso hκ (HasImages.isImage (stageInclL L hL cstage)))).trans ?_
  exact image_equiv_isImage (objInclL_preserves_images L hL hi hfaith hmono himgpres N cstage)

/-! ### Realization helpers — every datum is a germ; the stage-advance iso

  `hom_as_germL` destructs a colimit hom into `homInclL` of a germ.  `advIso x hiN` is the canonical
  iso `⟨i, x⟩ ≅ ⟨N, F x⟩` advancing an object's stage (`homInclL_isIso_of_rep`).  `advIso_stageInclL_eq`
  is the decisive germ-algebra identity: a general-bound germ `homInclL x y ⟨N,hiN,hjN⟩ g`,
  post-composed with the codomain stage-advance iso, equals the source stage-advance iso pre-composed
  with the `stageInclL` of the SAME pushed germ `g`.  This is the lax replacement for the strict
  `subst`-and-`HEq` alignment: it lets us bridge an arbitrary subobject of `B` to a `germSubL` over a
  stage object. -/

/-- Every colimit hom `p ⟶ q` is the germ `homInclL` of a representative at some bound. -/
theorem hom_as_germL (p q : Obj L) (m : @homL _ _ L hL p q) :
    ∃ (a : UpperBound D p.1 q.1) (g : L.F a.2.1 p.2 ⟶ L.F a.2.2 q.2),
      m = homInclL L hL p.2 q.2 a g :=
  Quotient.inductionOn m (fun rep => ⟨rep.1, rep.2, rfl⟩)

/-- The canonical stage-advance iso `⟨i, x⟩ → ⟨N, L.F hiN x⟩` (germ of `(reflApp)⁻¹` at bound `N`). -/
noncomputable def advIso {i : ι} (x : L.A i) {N : ι} (hiN : D.le i N) :
    @homL _ _ L hL ⟨i, x⟩ ⟨N, L.F hiN x⟩ :=
  homInclL L hL x (L.F hiN x) ⟨N, hiN, D.refl N⟩ (isoInv (reflApp_isIso L (L.F hiN x)))

theorem advIso_isIso {i : ι} (x : L.A i) {N : ι} (hiN : D.le i N) :
    @IsIso (Obj L) (laxColimCat L hL) _ _ (advIso L hL x hiN) :=
  homInclL_isIso_of_rep L hL x (L.F hiN x) ⟨N, hiN, D.refl N⟩
    (isoInv (reflApp_isIso L (L.F hiN x))) (reflApp L (L.F hiN x))
    (inv_isoInv_comp _) (isoInv_comp _)

set_option maxHeartbeats 1000000 in
/-- **The stage-advance bridge identity.**  `advIso x ⊚ stageInclL g = (homInclL x y ⟨N,hiN,hjN⟩ g) ⊚ advIso y`
    — both reduce to `homInclL x (F y) ⟨N,hiN,refl⟩ (g ≫ (reflApp)⁻¹)` at the common bound `N`. -/
theorem advIso_stageInclL_eq {i : ι} (x : L.A i) {N : ι} (hiN : D.le i N)
    {j : ι} (y : L.A j) (hjN : D.le j N) (g : L.F hiN x ⟶ L.F hjN y) :
    @compL _ _ L hL ⟨i, x⟩ ⟨N, L.F hiN x⟩ ⟨N, L.F hjN y⟩
        (advIso L hL x hiN) (stageInclL L hL g)
      = @compL _ _ L hL ⟨i, x⟩ ⟨j, y⟩ ⟨N, L.F hjN y⟩
        (homInclL L hL x y ⟨N, hiN, hjN⟩ g) (advIso L hL y hjN) := by
  unfold advIso stageInclL
  rw [compL_homInclL_compAtL L hL x (L.F hiN x) (L.F hjN y) ⟨N, hiN, D.refl N⟩ _
        ⟨N, D.refl N, D.refl N⟩ _ N (D.refl N) (D.refl N),
      compL_homInclL_compAtL L hL x y (L.F hjN y) ⟨N, hiN, hjN⟩ g ⟨N, hjN, D.refl N⟩ _
        N (D.refl N) (D.refl N)]
  rw [hL.push_refl x (L.F hiN x) hiN (D.refl N) (isoInv (reflApp_isIso L (L.F hiN x))),
      hL.push_refl (L.F hiN x) (L.F hjN y) (D.refl N) (D.refl N)
        (reflApp L (L.F hiN x) ≫ g ≫ isoInv (reflApp_isIso L (L.F hjN y))),
      hL.push_refl x y hiN hjN g,
      hL.push_refl y (L.F hjN y) hjN (D.refl N) (isoInv (reflApp_isIso L (L.F hjN y)))]
  rw [← Cat.assoc (isoInv (reflApp_isIso L (L.F hiN x))) (reflApp L (L.F hiN x)),
      inv_isoInv_comp, Cat.id_comp]

/-! ### The lax colimit union condition (the hard direction)

  `f#(S ∪ T) ≤ f#S ∪ f#T` in `laxColimCat L hL`.  Realize `f, S.arr, T.arr` as germs at a common stage
  `N`, advance every endpoint object to stage `N` by the `advIso`s, rewrite both sides as `subConj`s of
  `germSubL`s of the stage `pbSub`/`unionImg` (transports E, D + the `subConj` bridges), apply the
  per-stage hard direction `stage_invImage_union_le`, and transport the resulting `≤` up by
  `germSubL_le` + `subConj_le`.  Lax mirror of `Colim.colimit_invImage_union_le`. -/
set_option maxHeartbeats 4000000 in
theorem laxColim_invImage_union_le [Nonempty ι]
    (tData : LaxTerminalData L) (pData : LaxProductData L) (eqData : LaxEqualizerData L)
    (coprData : LaxCoproductData L)
    (hi : ∀ i, @HasImages (L.A i) (L.catA i))
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        @Functor.map _ _ _ _ _ (L.functF hij) x y p
          = @Functor.map _ _ _ _ _ (L.functF hij) x y q → p = q)
    (hmono : TransMonoL L)
    (himgpres : ∀ {i j : ι} (hij : D.le i j) {X Y : L.A i} (f : X ⟶ Y),
        @IsImage (L.A j) (L.catA j) _ _ (@Functor.map _ _ _ _ _ (L.functF hij) X Y f)
          (@Subobject.map _ _ (L.catA i) (L.catA j) (L.F hij) (L.functF hij) (hmono hij) _
            (@image _ (L.catA i) (hi i) _ _ f)))
    (hbot : ∀ i, PreLogos (L.A i))
    [hpullI : @HasPullbacks (Obj L) (laxColimCat L hL)]
    [hImgI : @HasImages (Obj L) (laxColimCat L hL)]
    [hUnI : @HasSubobjectUnions (Obj L) (laxColimCat L hL) hImgI] :
    letI : Cat (Obj L) := laxColimCat L hL
    ∀ {A B : Obj L} (f : A ⟶ B) (S T : Subobject (Obj L) B),
      (InverseImage f (HasSubobjectUnions.union S T)).le
        (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)) := by
  letI : Cat (Obj L) := laxColimCat L hL
  intro A B
  obtain ⟨iA, xA⟩ := A
  obtain ⟨iB, xB⟩ := B
  intro f S T
  -- germ representatives of `f`, `S.arr`, `T.arr`.
  obtain ⟨af, gf, hf⟩ := hom_as_germL L hL ⟨iA, xA⟩ ⟨iB, xB⟩ f
  obtain ⟨aS, gS, hSa⟩ := hom_as_germL L hL S.dom ⟨iB, xB⟩ S.arr
  obtain ⟨aT, gT, hTa⟩ := hom_as_germL L hL T.dom ⟨iB, xB⟩ T.arr
  -- a common stage `N ≥ af.1, aS.1, aT.1`.
  obtain ⟨N1, hN1a, hN1b⟩ := D.bound af.1 aS.1
  obtain ⟨N, hNN1, hNaT⟩ := D.bound N1 aT.1
  have hafN : D.le af.1 N := D.trans hN1a hNN1
  have haSN : D.le aS.1 N := D.trans hN1b hNN1
  have haTN : D.le aT.1 N := hNaT
  have hiAN : D.le iA N := D.trans af.2.1 hafN
  have hiBN : D.le iB N := D.trans af.2.2 hafN
  have hiSdN : D.le S.dom.1 N := D.trans aS.2.1 haSN
  have hiTdN : D.le T.dom.1 N := D.trans aT.2.1 haTN
  -- stage-`N` representatives of the three maps.
  let xAN := L.F hiAN xA
  let xBN := L.F hiBN xB
  let f_N : xAN ⟶ xBN := pushHom L xA xB af.2.1 af.2.2 hafN gf
  let gS' : L.F hiSdN S.dom.2 ⟶ xBN := pushHom L S.dom.2 xB aS.2.1 aS.2.2 haSN gS
  let gT' : L.F hiTdN T.dom.2 ⟶ xBN := pushHom L T.dom.2 xB aT.2.1 aT.2.2 haTN gT
  have hf' : f = homInclL L hL xA xB ⟨N, hiAN, hiBN⟩ f_N := by
    rw [hf]; exact (homInclL_compat L hL xA xB (a := af) (b := ⟨N, hiAN, hiBN⟩) hafN gf).symm
  have hSa' : S.arr = homInclL L hL S.dom.2 xB ⟨N, hiSdN, hiBN⟩ gS' := by
    rw [hSa]; exact (homInclL_compat L hL S.dom.2 xB (a := aS) (b := ⟨N, hiSdN, hiBN⟩) haSN gS).symm
  have hTa' : T.arr = homInclL L hL T.dom.2 xB ⟨N, hiTdN, hiBN⟩ gT' := by
    rw [hTa]; exact (homInclL_compat L hL T.dom.2 xB (a := aT) (b := ⟨N, hiTdN, hiBN⟩) haTN gT).symm
  -- stage monics (reflect the colimit monos of `S.arr`, `T.arr`).
  have hSarrM : @Monic (Obj L) (laxColimCat L hL) S.dom ⟨iB, xB⟩ (homInclL L hL S.dom.2 xB aS gS) := by
    rw [← hSa]; exact S.monic
  have hTarrM : @Monic (Obj L) (laxColimCat L hL) T.dom ⟨iB, xB⟩ (homInclL L hL T.dom.2 xB aT gT) := by
    rw [← hTa]; exact T.monic
  have hgS'M : @Monic (L.A N) _ _ _ gS' := by
    intro z u v huv
    exact homInclL_mono_reflects L hL hfaith S.dom.2 xB aS gS hSarrM haSN z u v huv
  have hgT'M : @Monic (L.A N) _ _ _ gT' := by
    intro z u v huv
    exact homInclL_mono_reflects L hL hfaith T.dom.2 xB aT gT hTarrM haTN z u v huv
  let S_N : Subobject (L.A N) xBN := ⟨L.F hiSdN S.dom.2, gS', hgS'M⟩
  let T_N : Subobject (L.A N) xBN := ⟨L.F hiTdN T.dom.2, gT', hgT'M⟩
  -- the stage-advance isos for the four endpoint objects.
  let dA := advIso L hL xA hiAN
  let dB := advIso L hL xB hiBN
  have hdAiso : @IsIso (Obj L) (laxColimCat L hL) _ _ dA := advIso_isIso L hL xA hiAN
  have hdBiso : @IsIso (Obj L) (laxColimCat L hL) _ _ dB := advIso_isIso L hL xB hiBN
  obtain ⟨dAi, hA1, hA2⟩ := hdAiso
  obtain ⟨dBi, hB1, hB2⟩ := hdBiso
  -- `f ⊚ dB = dA ⊚ stageInclL f_N`.
  have hBf : f ≫ dB = dA ≫ stageInclL L hL f_N := by
    rw [hf']; exact (advIso_stageInclL_eq L hL xA hiAN xB hiBN f_N).symm
  -- bridges: `subConj dB S ≈ germSubL S_N`, `subConj dB T ≈ germSubL T_N`.
  have heqS : advIso L hL S.dom.2 hiSdN ≫ stageInclL L hL gS' = S.arr ≫ dB := by
    rw [hSa']; exact advIso_stageInclL_eq L hL S.dom.2 hiSdN xB hiBN gS'
  have heqT : advIso L hL T.dom.2 hiTdN ≫ stageInclL L hL gT' = T.arr ≫ dB := by
    rw [hTa']; exact advIso_stageInclL_eq L hL T.dom.2 hiTdN xB hiBN gT'
  obtain ⟨dSi, _, hS2⟩ := advIso_isIso L hL S.dom.2 hiSdN
  obtain ⟨dTi, _, hT2⟩ := advIso_isIso L hL T.dom.2 hiTdN
  have hBS : (subConj dB ⟨dBi, hB1, hB2⟩ S).Equiv (germSubL L hL hmono S_N) := by
    refine ⟨⟨advIso L hL S.dom.2 hiSdN, ?_⟩, ⟨dSi, ?_⟩⟩
    · show advIso L hL S.dom.2 hiSdN ≫ stageInclL L hL gS' = S.arr ≫ dB; exact heqS
    · show dSi ≫ (S.arr ≫ dB) = stageInclL L hL gS'
      rw [← heqS, ← Cat.assoc, hS2, Cat.id_comp]
  have hBT : (subConj dB ⟨dBi, hB1, hB2⟩ T).Equiv (germSubL L hL hmono T_N) := by
    refine ⟨⟨advIso L hL T.dom.2 hiTdN, ?_⟩, ⟨dTi, ?_⟩⟩
    · show advIso L hL T.dom.2 hiTdN ≫ stageInclL L hL gT' = T.arr ≫ dB; exact heqT
    · show dTi ≫ (T.arr ≫ dB) = stageInclL L hL gT'
      rw [← heqT, ← Cat.assoc, hT2, Cat.id_comp]
  -- abbreviations for the stage pullbacks.
  let pbU := pbSub (tData.ht N) (pData.hp N) (eqData.he N) f_N (unionImg (hi N) (coprData.hcop N) S_N T_N)
  let pbS := pbSub (tData.ht N) (pData.hp N) (eqData.he N) f_N S_N
  let pbT := pbSub (tData.ht N) (pData.hp N) (eqData.he N) f_N T_N
  -- LHS as a `subConj dAi (germSubL pbU)`.
  have hLHS : (InverseImage f (HasSubobjectUnions.union S T)).Equiv
      (subConj dAi ⟨dA, hA2, hA1⟩ (germSubL L hL hmono pbU)) := by
    refine (invImage_subConj_equiv f dB ⟨dBi, hB1, hB2⟩ (HasSubobjectUnions.union S T)).trans ?_
    refine (invImage_equiv_pb (f ≫ dB)
      (((subConj_union_equiv dB dBi ⟨dBi, hB1, hB2⟩ hB1 hB2 S T).trans
        (union_equiv hBS hBT)).trans
        (union_germ_equivL L hL hmono coprData hi hfaith himgpres N S_N T_N))).trans ?_
    rw [hBf]
    refine (invImage_iso_precomp_equiv dA dAi hA1 hA2 (stageInclL L hL f_N)
      (germSubL L hL hmono (unionImg (hi N) (coprData.hcop N) S_N T_N))).trans ?_
    exact subConj_equiv dAi ⟨dA, hA2, hA1⟩
      (invImage_germ_equivL L hL hmono tData pData eqData N f_N
        (unionImg (hi N) (coprData.hcop N) S_N T_N))
  -- the two inverse-image legs as `subConj dAi (germSubL pbS|pbT)`.
  have hfS : (InverseImage f S).Equiv (subConj dAi ⟨dA, hA2, hA1⟩ (germSubL L hL hmono pbS)) := by
    refine (invImage_subConj_equiv f dB ⟨dBi, hB1, hB2⟩ S).trans ?_
    refine (invImage_equiv_pb (f ≫ dB) hBS).trans ?_
    rw [hBf]
    refine (invImage_iso_precomp_equiv dA dAi hA1 hA2 (stageInclL L hL f_N)
      (germSubL L hL hmono S_N)).trans ?_
    exact subConj_equiv dAi ⟨dA, hA2, hA1⟩
      (invImage_germ_equivL L hL hmono tData pData eqData N f_N S_N)
  have hfT : (InverseImage f T).Equiv (subConj dAi ⟨dA, hA2, hA1⟩ (germSubL L hL hmono pbT)) := by
    refine (invImage_subConj_equiv f dB ⟨dBi, hB1, hB2⟩ T).trans ?_
    refine (invImage_equiv_pb (f ≫ dB) hBT).trans ?_
    rw [hBf]
    refine (invImage_iso_precomp_equiv dA dAi hA1 hA2 (stageInclL L hL f_N)
      (germSubL L hL hmono T_N)).trans ?_
    exact subConj_equiv dAi ⟨dA, hA2, hA1⟩
      (invImage_germ_equivL L hL hmono tData pData eqData N f_N T_N)
  -- RHS as a `subConj dAi (germSubL (unionImg pbS pbT))`.
  have hRHS : (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)).Equiv
      (subConj dAi ⟨dA, hA2, hA1⟩
        (germSubL L hL hmono (unionImg (hi N) (coprData.hcop N) pbS pbT))) := by
    refine (union_equiv hfS hfT).trans ?_
    refine (subConj_union_equiv dAi dA ⟨dA, hA2, hA1⟩ hA2 hA1
      (germSubL L hL hmono pbS) (germSubL L hL hmono pbT)).symm.trans ?_
    exact subConj_equiv dAi ⟨dA, hA2, hA1⟩
      (union_germ_equivL L hL hmono coprData hi hfaith himgpres N pbS pbT)
  -- stage hard direction, transported up.
  have hstage := stage_invImage_union_le (𝒞 := L.A N) (hPL := hbot N)
    (tData.ht N) (pData.hp N) (eqData.he N) (hi N) (coprData.hcop N) f_N S_N T_N
  have hstageConj := subConj_le dAi ⟨dA, hA2, hA1⟩ (germSubL_le L hL hmono hstage)
  exact Subobject.le_of_equiv_le hLHS (Subobject.le_of_le_equiv hstageConj hRHS.symm)

end Freyd.LaxColim
