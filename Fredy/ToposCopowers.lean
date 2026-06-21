/-
  §1.967 — Building a genuine copower-of-1 `∐ᵢ1` in a locally small topos with arbitrary powers.

  The EFFECTIVE DISJOINT UNION route.  In a topos `1+1` exists (`topos_is_positive`) and, given
  arbitrary powers `hpow`, the power `∏ᵢ(1+1)` exists.  The copower object is carved as the
  subobject `obj := ⋁ᵢ imᵢ ⊆ ∏ᵢ(1+1)`, the JOIN (`extJoin`) of the images of the candidate
  injections `cand i : 1 → ∏ᵢ(1+1)` — the tuple that is `inr` (true) at coordinate `i` and `inl`
  (false) elsewhere.  The `imᵢ` are pairwise disjoint (`1+1` disjointness), each `≅ 1`.

  STATUS: SORRY-FREE.  `inj`, `inj_cotup`, `cotup_uniq`, AND `cotup` (map-OUT existence) are all
  built without `sorry` (`#print axioms Freyd.toposCopowerOfOne = [propext, Classical.choice,
  Quot.sound]`).

  * `cotup_uniq` (map-OUT uniqueness / jointly-epic injections) is the infinitary analogue of
    `coprod_jointly_epi` with `extJoin_least` (S1_95) for the binary `union_min`: form the
    equalizer `E = {h=k}`, show each `imᵢ ≤ E`, then `extJoin_least` forces `obj ≤ E`.  Banked as
    `copowerImages_jointly_epi`.
  * `cotup` (map-OUT EXISTENCE) is the infinitary disjoint GLUING, done honestly (no circular
    bootstrap through the binary `disjoint_cover_is_coproduct`).  The copairing is the map whose
    GRAPH is the join `G := ⋁ᵢ relSub P_i ⊆ obj × X` of the partial graphs
    `P_i := (graph (inj i))° ⊚ graph (f i)`, tabulated as a relation `obj ⇸ X`, shown TOTAL
    (`copowUnion_total`, via `copowInj_jointly_cover`) and SIMPLE (`copowUnion_simple`).
    FUNCTIONALITY is the genuine infinitary content: the §1.616 composition-over-join
    distributivity `compose_extJoin_right` (built here from STEP 1 `existsAlong_extJoin_le` +
    the §1.84 frame law `extJoin_invImage_le`) distributes `G° ⊚ G` over the join into
    `⋁ᵢⱼ (P_i° ⊚ P_j)`; the diagonal/off-diagonal bounds `P_i° ⊚ P_j ≤ 1`
    (`copowPartial_pair_le`, from `diag_le_one`/`cross_le_one` with `1+1` disjointness
    `copowInj_disjoint_maps_agree`) collapse the join into `graph (id X)`.

  Reusable lemmas banked here: `existsAlong_extJoin_le` (∃ preserves joins), `compose_extJoin_right`
  (composition distributes over arbitrary joins), `binRelSub` (subobject-as-relation).
-/
import Fredy.S1_95
import Fredy.ToposExists
import Fredy.ToposDistributive
import Fredy.ToposIndexedJoins

universe u v w

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [LocallySmallTopos 𝒞]

open Classical

/-! ## §1.843 — `WellPoweredSub` from the subobject classifier

  Freyd §1.843: a topos is well-powered.  The cleanest elementary route does NOT need a
  progenitor or copowers: the subobject classifier gives `Sub(A) ↪ Hom(A, Ω)` directly, since
  `χ : Sub(A) → Hom(A,Ω)` is injective up to subobject-equality (`subChar S = subChar T ⟹ S ≅ T`
  via `le_iff_classify` both ways).  `Hom(A,Ω) : Type v`, so it is a `Type v` enumeration.

  This BANKS `wellPoweredSub_of_topos : WellPoweredSub 𝒞` for any `[Topos 𝒞]`, hence the
  `LocallySmallTopos.wellPowered` datum from bare Tierney data — making every copower lemma here
  (which assumes `[LocallySmallTopos 𝒞]`) applicable from just `Topos`.  Axioms:
  `[propext, Classical.choice, Quot.sound]`. -/
section WellPoweredFromClassifier
variable (𝒟 : Type u) [Cat.{v} 𝒟] [Topos 𝒟]

/-- A subobject is detected by its characteristic map: equal `χ` forces `≤` in both directions.
    `S.arr ≫ χ_S = term ≫ true` always (`le_iff_classify` at `S ≤ S`); substituting `χ_S = χ_T`
    gives `S.arr ≫ χ_T = term ≫ true`, i.e. `S ≤ T`. -/
theorem le_of_subChar_eq {A : 𝒟} {S T : Subobject 𝒟 A} (h : subChar S = subChar T) :
    S.le T := by
  have hSS : S.arr ≫ subChar S = term S.dom ≫ HasSubobjectClassifier.true :=
    (le_iff_classify S S).mp (Sub.le_refl S)
  rw [h] at hSS
  exact (le_iff_classify S T).mpr hSS

/-- **§1.843**: every topos is well-powered.  Index `Sub(A)` by `Hom(A, Ω) : Type v`; enumerate a
    characteristic map `c` by SOME subobject with `χ = c` (if any), else the entire subobject.
    `surj S` uses `c := subChar S`, and `le_of_subChar_eq` (both ways) makes the chosen
    representative `≤`-equal to `S`. -/
noncomputable def wellPoweredSub_of_topos : WellPoweredSub.{v} 𝒟 where
  idx A := A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒟)
  enum {A} c := if h : ∃ S : Subobject 𝒟 A, subChar S = c then h.choose else Subobject.entire A
  surj {A} S := by
    refine ⟨subChar S, ?_, ?_⟩
    · -- S ≤ enum (χ_S): the chosen rep S' has χ_S' = χ_S, so S ≤ S' by `le_of_subChar_eq`.
      have hex : ∃ S' : Subobject 𝒟 A, subChar S' = subChar S := ⟨S, rfl⟩
      show S.le (if h : ∃ S' : Subobject 𝒟 A, subChar S' = subChar S then h.choose else _)
      rw [dif_pos hex]
      exact le_of_subChar_eq 𝒟 hex.choose_spec.symm
    · have hex : ∃ S' : Subobject 𝒟 A, subChar S' = subChar S := ⟨S, rfl⟩
      show (if h : ∃ S' : Subobject 𝒟 A, subChar S' = subChar S then h.choose else _).le S
      rw [dif_pos hex]
      exact le_of_subChar_eq 𝒟 hex.choose_spec

end WellPoweredFromClassifier

section CopowerBuild

variable (hpow : HasArbitraryPowers (𝒞 := 𝒞)) (I : Type v)

/-- The ambient power `∏ᵢ(1+1)`.  `1+1` exists by `topos_is_positive`; the `I`-fold power by
    `hpow`.  The copower object will be carved as a subobject of this. -/
noncomputable def copowAmbient : 𝒞 :=
  hpow.pow I (coprodObj (one : 𝒞) (one : 𝒞))

/-- The candidate `i`-th injection `1 → ∏ᵢ(1+1)`: the tuple that is `inr` (true) at coordinate
    `i` and `inl` (false) at every other coordinate. -/
noncomputable def copowCand (i : I) : (one : 𝒞) ⟶ copowAmbient hpow I :=
  hpow.tupling (fun j => term (one : 𝒞) ≫
    (if j = i then coprodInr (one : 𝒞) (one : 𝒞) else coprodInl (one : 𝒞) (one : 𝒞)))

/-- The `i`-th injection-image `imᵢ ⊆ ∏ᵢ(1+1)`. -/
noncomputable def copowImg (i : I) : Subobject 𝒞 (copowAmbient hpow I) :=
  image (copowCand hpow I i)

/-- The carving predicate: "is one of the injection-images `imᵢ`". -/
def copowImgPred (S : Subobject 𝒞 (copowAmbient hpow I)) : Prop := ∃ i, S = copowImg hpow I i

/-- The copower object `obj := ⋁ᵢ imᵢ`, as the `extJoin` subobject of `∏ᵢ(1+1)`. -/
noncomputable def copowSub : Subobject 𝒞 (copowAmbient hpow I) :=
  extJoin hpow LocallySmallTopos.wellPowered (copowImgPred hpow I)

noncomputable def copowObj : 𝒞 := (copowSub hpow I).dom

/-- `imᵢ ≤ obj` (every member is below the join) — `extJoin_upper`. -/
theorem copowImg_le (i : I) : (copowImg hpow I i).le (copowSub hpow I) :=
  extJoin_upper hpow LocallySmallTopos.wellPowered _ _ ⟨i, rfl⟩

/-- The `i`-th injection `1 → obj`.  `cand i` factors through `imᵢ` (image lift), and
    `imᵢ ≤ obj`, so it factors through `obj`. -/
noncomputable def copowInj (i : I) : (one : 𝒞) ⟶ copowObj hpow I :=
  image.lift (copowCand hpow I i) ≫ (copowImg_le hpow I i).choose

/-- `inj i ≫ obj.arr = cand i`. -/
theorem copowInj_arr (i : I) :
    copowInj hpow I i ≫ (copowSub hpow I).arr = copowCand hpow I i := by
  unfold copowInj
  rw [Cat.assoc, (copowImg_le hpow I i).choose_spec]
  exact image.lift_fac (copowCand hpow I i)

/-- **`cotup_uniq` (jointly-epic injections).**  Two maps `obj → X` agreeing on every `inj i`
    are equal.  This is the infinitary analogue of `coprod_jointly_epi` (ToposExists): form the
    equalizer `E = {h=k} ↪ obj`; each `imᵢ` (as a subobject of the ambient `∏ᵢ(1+1)`) lies in
    the push-forward `EP` of `E` (because `inj i` factors through `E` by agreement); then
    `extJoin_least` forces `obj = ⋁ᵢ imᵢ ≤ EP`, exhibiting `eqMap h k` as split epi — hence an
    iso (it is monic), so `h = k`.  Bankable, sorry-free. -/
theorem copowerImages_jointly_epi {X : 𝒞} (h k : copowObj hpow I ⟶ X)
    (hagree : ∀ i, copowInj hpow I i ≫ h = copowInj hpow I i ≫ k) : h = k := by
  -- E = equalizer of h, k, with monic inclusion `eqMap h k : E ↪ obj`.
  have heM : Mono (eqMap h k) := by
    intro W u v huv
    have hc : (u ≫ eqMap h k) ≫ h = (u ≫ eqMap h k) ≫ k := by
      rw [Cat.assoc, Cat.assoc, eqMap_eq]
    rw [eqLift_uniq h k _ hc u rfl, eqLift_uniq h k _ hc v huv.symm]
  -- push E forward into the ambient `∏ᵢ(1+1)`:  EP = ⟨E, eqMap ≫ obj.arr⟩.
  have hEPm : Mono (eqMap h k ≫ (copowSub hpow I).arr) := by
    intro W u v huv
    refine heM u v ((copowSub hpow I).monic _ _ ?_)
    rw [Cat.assoc, Cat.assoc, huv]
  let EP : Subobject 𝒞 (copowAmbient hpow I) := ⟨eqObj h k, eqMap h k ≫ (copowSub hpow I).arr, hEPm⟩
  -- each `imᵢ ≤ EP`: `inj i` factors through E (agreement), so `cand i` factors through EP.
  have himg_le : ∀ i, (copowImg hpow I i).le EP := by
    intro i
    -- li : 1 → E with li ≫ eqMap = inj i.
    let li : (one : 𝒞) ⟶ eqObj h k := eqLift h k (copowInj hpow I i) (hagree i)
    have hli : li ≫ eqMap h k = copowInj hpow I i := eqLift_fac h k _ (hagree i)
    -- cand i factors through EP directly via `li` (EP.dom = eqObj h k).
    refine image_min (copowCand hpow I i) EP ⟨li, ?_⟩
    show li ≫ (eqMap h k ≫ (copowSub hpow I).arr) = copowCand hpow I i
    -- li ≫ (eqMap ≫ obj.arr) = inj i ≫ obj.arr = cand i.
    rw [← Cat.assoc, hli, copowInj_arr]
  -- extJoin_least: obj = ⋁ᵢ imᵢ ≤ EP.
  have hobj_le : (copowSub hpow I).le EP :=
    extJoin_least hpow LocallySmallTopos.wellPowered _ EP
      (fun s ⟨i, hsi⟩ => hsi ▸ himg_le i)
  obtain ⟨w, hw⟩ := hobj_le
  -- hw : w ≫ (eqMap h k ≫ obj.arr) = obj.arr.  Cancel the monic obj.arr ⟹ w ≫ eqMap = id.
  have hwe : w ≫ eqMap h k = Cat.id (copowObj hpow I) := by
    apply (copowSub hpow I).monic
    rw [Cat.assoc]
    show w ≫ (eqMap h k ≫ (copowSub hpow I).arr) = Cat.id (copowObj hpow I) ≫ (copowSub hpow I).arr
    rw [Cat.id_comp]; exact hw
  -- w ≫ eqMap = id obj ⟹ split epi; with the equalizer law cancel to h = k.
  have heq_hk : eqMap h k ≫ h = eqMap h k ≫ k := eqMap_eq h k
  calc h = (w ≫ eqMap h k) ≫ h := by rw [hwe]; exact (Cat.id_comp h).symm
    _ = w ≫ (eqMap h k ≫ h) := Cat.assoc _ _ _
    _ = w ≫ (eqMap h k ≫ k) := by rw [heq_hk]
    _ = (w ≫ eqMap h k) ≫ k := (Cat.assoc _ _ _).symm
    _ = k := by rw [hwe]; exact Cat.id_comp k

/-- **TOTALITY — the injections jointly cover `obj`.**  A monic `m : C ↣ obj` through which
    every `inj i` factors is an isomorphism.  Same `extJoin_least` argument as
    `copowerImages_jointly_epi`: push `m` forward to the ambient `∏ᵢ(1+1)`, each `imᵢ` lies in
    the push-forward (the lift of `inj i` through `m`), so `extJoin_least` forces `obj ≤`
    push-forward, exhibiting `m` as split epi — hence iso.  Bankable, sorry-free. -/
theorem copowInj_jointly_cover {C : 𝒞} (m : C ⟶ copowObj hpow I) (hm : Mono m)
    (s : I → ((one : 𝒞) ⟶ C)) (hs : ∀ i, s i ≫ m = copowInj hpow I i) : IsIso m := by
  -- push `m` (subobject of obj) forward to the ambient: MP = ⟨C, m ≫ obj.arr⟩.
  have hMPm : Mono (m ≫ (copowSub hpow I).arr) := by
    intro W u v huv
    refine hm u v ((copowSub hpow I).monic _ _ ?_)
    rw [Cat.assoc, Cat.assoc, huv]
  let MP : Subobject 𝒞 (copowAmbient hpow I) := ⟨C, m ≫ (copowSub hpow I).arr, hMPm⟩
  -- each imᵢ ≤ MP: cand i factors through MP via s i (since s i ≫ m ≫ obj.arr = inj i ≫ obj.arr).
  have himg_le : ∀ i, (copowImg hpow I i).le MP := by
    intro i
    refine image_min (copowCand hpow I i) MP ⟨s i, ?_⟩
    show s i ≫ (m ≫ (copowSub hpow I).arr) = copowCand hpow I i
    rw [← Cat.assoc, hs i, copowInj_arr]
  -- extJoin_least: obj ≤ MP.
  have hobj_le : (copowSub hpow I).le MP :=
    extJoin_least hpow LocallySmallTopos.wellPowered _ MP
      (fun t ⟨i, hti⟩ => hti ▸ himg_le i)
  obtain ⟨w, hw⟩ := hobj_le
  -- hw : w ≫ (m ≫ obj.arr) = obj.arr.  Cancel monic obj.arr ⟹ w ≫ m = id obj.
  have hwm : w ≫ m = Cat.id (copowObj hpow I) := by
    apply (copowSub hpow I).monic
    rw [Cat.assoc]
    show w ≫ (m ≫ (copowSub hpow I).arr) = Cat.id (copowObj hpow I) ≫ (copowSub hpow I).arr
    rw [Cat.id_comp]; exact hw
  -- m ≫ w = id C: cancel monic m on (m ≫ w) ≫ m = m ≫ (w ≫ m) = m = id ≫ m.
  have hmw : m ≫ w = Cat.id C :=
    hm _ _ (by rw [Cat.assoc, hwm, Cat.comp_id, Cat.id_comp])
  exact ⟨w, hmw, hwm⟩

/-! ### STEP 1 — direct image preserves arbitrary joins

  `∃_g (⋁ S) ≤ ⋁ (∃_g '' S)`.  The infinitary analogue of `existsAlong_union_le` (S1_60),
  proven via the `∃_g ⊣ g#` Galois connection (`existsAlong_le_iff`, S1_60) with
  `extJoin_upper`/`extJoin_least` (S1_95) in place of the binary union laws. -/
theorem existsAlong_extJoin_le {A B : 𝒞} (g : A ⟶ B) (S : Subobject 𝒞 A → Prop) :
    (existsAlong g (extJoin hpow LocallySmallTopos.wellPowered S)).le
      (extJoin hpow LocallySmallTopos.wellPowered
        (fun V => ∃ s, S s ∧ V = existsAlong g s)) := by
  let V := extJoin hpow LocallySmallTopos.wellPowered (fun V => ∃ s, S s ∧ V = existsAlong g s)
  -- By the adjunction: suffices  extJoin S ≤ g# V.
  refine (existsAlong_le_iff g (extJoin hpow LocallySmallTopos.wellPowered S) V).2 ?_
  -- `extJoin_least`: each member `s` of `S` lies below `g# V`.
  refine extJoin_least hpow LocallySmallTopos.wellPowered S _ (fun s hs => ?_)
  -- s ≤ g# V  ↔  ∃_g s ≤ V; and ∃_g s IS a member of the image-predicate, so `extJoin_upper`.
  exact (existsAlong_le_iff g s V).1
    (extJoin_upper hpow LocallySmallTopos.wellPowered _ (existsAlong g s) ⟨s, hs, rfl⟩)

/-- A subobject of `A × B` viewed as a relation `A ⇸ B` (legs = `arr ≫ fst`, `arr ≫ snd`). -/
noncomputable def binRelSub {A B : 𝒞} (W : Subobject 𝒞 (prod A B)) : BinRel 𝒞 A B where
  src  := W.dom
  colA := W.arr ≫ fst
  colB := W.arr ≫ snd
  isMonicPair := by
    intro Z u v hA hB
    refine W.monic u v ?_
    have hfst : (u ≫ W.arr) ≫ fst = (v ≫ W.arr) ≫ fst := by simpa [Cat.assoc] using hA
    have hsnd : (u ≫ W.arr) ≫ snd = (v ≫ W.arr) ≫ snd := by simpa [Cat.assoc] using hB
    calc u ≫ W.arr
        = pair ((u ≫ W.arr) ≫ fst) ((u ≫ W.arr) ≫ snd) := pair_uniq _ _ _ rfl rfl
      _ = pair ((v ≫ W.arr) ≫ fst) ((v ≫ W.arr) ≫ snd) := by rw [hfst, hsnd]
      _ = v ≫ W.arr := (pair_uniq _ _ _ rfl rfl).symm

/-- `relSub (binRelSub W) = W` as subobjects (the pair of `W.arr`'s projections is `W.arr`). -/
theorem relSub_binRelSub_arr {A B : 𝒞} (W : Subobject 𝒞 (prod A B)) :
    (relSub (binRelSub W)).arr = W.arr := by
  show pair (W.arr ≫ fst) (W.arr ≫ snd) = W.arr
  exact (pair_uniq _ _ W.arr rfl rfl).symm

theorem relSub_binRelSub_le {A B : 𝒞} (W : Subobject 𝒞 (prod A B)) :
    (relSub (binRelSub W)).le W :=
  ⟨Cat.id _, by rw [Cat.id_comp, relSub_binRelSub_arr]⟩

theorem binRelSub_relSub_le {A B : 𝒞} (W : Subobject 𝒞 (prod A B)) :
    W.le (relSub (binRelSub W)) :=
  ⟨Cat.id _, by rw [Cat.id_comp, relSub_binRelSub_arr]⟩

/-- **Monotone in the predicate** for `extJoin`: if every member of `P` lies below some member of
    `Q`, then `extJoin P ≤ extJoin Q`. -/
theorem extJoin_mono_pred {A : 𝒞} {P Q : Subobject 𝒞 A → Prop}
    (h : ∀ s, P s → ∃ t, Q t ∧ s.le t) :
    (extJoin hpow LocallySmallTopos.wellPowered P).le
      (extJoin hpow LocallySmallTopos.wellPowered Q) := by
  refine extJoin_least hpow LocallySmallTopos.wellPowered P _ (fun s hs => ?_)
  obtain ⟨t, hQt, hst⟩ := h s hs
  exact subLe_trans hst (extJoin_upper hpow LocallySmallTopos.wellPowered Q t hQt)

/-! ### STEP 2 — composition distributes over arbitrary joins (right)

  `R ⊚ (⋁ᵢ Wᵢ) ≤ ⋁ᵢ (R ⊚ Wᵢ)` at the subobject level, where `Wᵢ ⊆ B × C` range over the
  predicate `S`, `extJoin S ⊆ B × C` is their join, and a subobject of a product is read as a
  relation via `binRelSub`.  The infinitary analogue of `compose_union_right` (S1_60): both
  factors of `compose = ∃_ω ∘ θ#` (`relSub_compose_eq`) preserve arbitrary joins —
  `θ#` by the §1.84 frame law `extJoin_invImage_le` (S1_95), `∃_ω` by STEP 1. -/
theorem compose_extJoin_right {A B C : 𝒞} (R : BinRel 𝒞 A B)
    (S : Subobject 𝒞 (prod B C) → Prop) :
    (relSub (R ⊚ binRelSub (extJoin hpow LocallySmallTopos.wellPowered S))).le
      (extJoin hpow LocallySmallTopos.wellPowered
        (fun U => ∃ W, S W ∧ U = relSub (R ⊚ binRelSub W))) := by
  let wp := LocallySmallTopos.wellPowered (𝒞 := 𝒞)
  -- LHS = ∃_ω (θ# relSub(binRelSub (extJoin S))) = ∃_ω (θ# (extJoin S)).
  have hL := (relSub_compose_eq R (binRelSub (extJoin hpow wp S))).1
  -- relSub(binRelSub (extJoin S)) ≤ extJoin S, so θ# of it ≤ θ#(extJoin S), and ∃_ω monotone.
  have hstep : (existsAlong (omegaR R C)
        (InverseImage (thetaR R C) (relSub (binRelSub (extJoin hpow wp S))))).le
      (existsAlong (omegaR R C)
        (InverseImage (thetaR R C) (extJoin hpow wp S))) :=
    existsAlong_mono (omegaR R C)
      (invImage_mono_local (thetaR R C) (relSub_binRelSub_le (extJoin hpow wp S)))
  -- θ#(extJoin S) ≤ extJoin {θ# W}.
  have hframe := extJoin_invImage_le hpow wp (thetaR R C) S
  have h2 : (existsAlong (omegaR R C) (InverseImage (thetaR R C) (extJoin hpow wp S))).le
      (existsAlong (omegaR R C)
        (extJoin hpow wp
          (fun A' => ∃ W, S W ∧ A' = InverseImage (thetaR R C) (relSub (binRelSub W))))) := by
    refine existsAlong_mono (omegaR R C) (subLe_trans hframe ?_)
    -- rewrite the inner predicate (θ# W vs θ#(relSub(binRelSub W))) — they coincide since
    -- relSub(binRelSub W) = W as subobjects.  Use `extJoin_mono_pred`.
    refine extJoin_mono_pred hpow (fun s ⟨W, hSW, hs⟩ => ?_)
    exact ⟨_, ⟨W, hSW, rfl⟩,
      hs ▸ invImage_mono_local (thetaR R C) (binRelSub_relSub_le W)⟩
  -- ∃_ω (extJoin {θ#(relSub(binRelSub W))}) ≤ extJoin {∃_ω (θ#(relSub(binRelSub W)))}.
  have h3 := existsAlong_extJoin_le hpow (omegaR R C)
    (fun A' => ∃ W, S W ∧ A' = InverseImage (thetaR R C) (relSub (binRelSub W)))
  -- each ∃_ω (θ#(relSub(binRelSub W))) = relSub(R ⊚ binRelSub W)  (reverse `relSub_compose_eq`).
  have h4 : (extJoin hpow wp
        (fun V => ∃ s,
          (∃ W, S W ∧ s = InverseImage (thetaR R C) (relSub (binRelSub W)))
          ∧ V = existsAlong (omegaR R C) s)).le
      (extJoin hpow wp (fun U => ∃ W, S W ∧ U = relSub (R ⊚ binRelSub W))) := by
    refine extJoin_mono_pred hpow (fun V ⟨s, ⟨W, hSW, hsW⟩, hV⟩ => ?_)
    refine ⟨relSub (R ⊚ binRelSub W), ⟨W, hSW, rfl⟩, ?_⟩
    -- V = ∃_ω s = ∃_ω(θ#(relSub(binRelSub W))) ≤ relSub(R ⊚ binRelSub W) by reverse compose_eq.
    rw [hV, hsW]
    exact (relSub_compose_eq R (binRelSub W)).2
  exact subLe_trans hL (subLe_trans hstep (subLe_trans h2 (subLe_trans h3 h4)))

/-- `binRelSub (relSub R)` is relationally equal to `R` (round-trip). -/
theorem binRelSub_relSub_relLe {A B : 𝒞} (R : BinRel 𝒞 A B) :
    RelLe (binRelSub (relSub R)) R ∧ RelLe R (binRelSub (relSub R)) :=
  ⟨relLe_of_subLe (relSub_binRelSub_le (relSub R)),
   relLe_of_subLe (binRelSub_relSub_le (relSub R))⟩

/-! ### STEP 3 — disjointness of distinct injection-images

  For `i ≠ j` the candidate points `cand i`, `cand j` differ at coordinate `i` (`inr` vs `inl`),
  so a common point of `inj i`, `inj j` maps to the pullback of `coprodInl`/`coprodInr` at that
  coordinate — which is `≅ 0` (`coprodInjections_disjoint`).  Hence the apex of the pullback of
  `(inj i, inj j)` admits a map to `0`, so it is `≅ 0`, so any two maps out of it agree.  This
  supplies the cocone equation `π₁ ≫ f i = π₂ ≫ f j` that the cross-term `cross_le_one` needs. -/

/-- A common point of `inj i`, `inj j` (`i ≠ j`) yields a map from the pullback apex to the
    `(coprodInl, coprodInr)` pullback apex: at coordinate `i`, `cand i` is `inr` and `cand j` is
    `inl`. -/
theorem copowInj_disjoint_apex_map {i j : I} (hij : i ≠ j) :
    ∃ _ : (HasPullbacks.has (copowInj hpow I i) (copowInj hpow I j)).cone.pt ⟶
        (HasPullbacks.has (coprodInl (one : 𝒞) (one : 𝒞))
          (coprodInr (one : 𝒞) (one : 𝒞))).cone.pt, True := by
  let pb := HasPullbacks.has (copowInj hpow I i) (copowInj hpow I j)
  let P := pb.cone.pt
  -- π₁ ≫ inj i = π₂ ≫ inj j, post-compose obj.arr ⟹ π₁ ≫ cand i = π₂ ≫ cand j.
  have hsq : pb.cone.π₁ ≫ copowInj hpow I i = pb.cone.π₂ ≫ copowInj hpow I j := pb.cone.w
  have hcand : pb.cone.π₁ ≫ copowCand hpow I i = pb.cone.π₂ ≫ copowCand hpow I j := by
    rw [← copowInj_arr hpow I i, ← copowInj_arr hpow I j, ← Cat.assoc, ← Cat.assoc, hsq]
  -- project to coordinate i.
  have hproj : (pb.cone.π₁ ≫ term (one : 𝒞)) ≫ coprodInr (one : 𝒞) (one : 𝒞)
      = (pb.cone.π₂ ≫ term (one : 𝒞)) ≫ coprodInl (one : 𝒞) (one : 𝒞) := by
    have h := congrArg (· ≫ hpow.proj i) hcand
    simp only at h
    rw [Cat.assoc, Cat.assoc, copowCand, copowCand, hpow.tupling_proj, hpow.tupling_proj] at h
    simp only [if_neg hij] at h
    -- h : π₁ ≫ (term ≫ inr) = π₂ ≫ (term ≫ inl)
    rw [← Cat.assoc, ← Cat.assoc] at h
    exact h
  -- term P collapses both prefactors; produce a cone over (inl, inr).
  have hcollapse : term P ≫ coprodInr (one : 𝒞) (one : 𝒞)
      = term P ≫ coprodInl (one : 𝒞) (one : 𝒞) := by
    rw [show (term P : P ⟶ (one : 𝒞)) = pb.cone.π₁ ≫ term (one : 𝒞) from term_uniq _ _] at *
    rw [show (pb.cone.π₂ ≫ term (one : 𝒞) : P ⟶ (one : 𝒞)) = pb.cone.π₁ ≫ term (one : 𝒞)
        from term_uniq _ _] at hproj
    exact hproj
  let pbC := HasPullbacks.has (coprodInl (one : 𝒞) (one : 𝒞)) (coprodInr (one : 𝒞) (one : 𝒞))
  let c : Cone (coprodInl (one : 𝒞) (one : 𝒞)) (coprodInr (one : 𝒞) (one : 𝒞)) :=
    ⟨P, term P, term P, hcollapse.symm⟩
  exact ⟨pbC.lift c, trivial⟩

/-- For `i ≠ j`, any two maps out of the `(inj i, inj j)` pullback apex agree (the apex is `≅ 0`
    via `coprodInjections_disjoint` + `any_map_to_zero_is_iso`). -/
theorem copowInj_disjoint_maps_agree {i j : I} (hij : i ≠ j) {Z : 𝒞}
    (u v : (HasPullbacks.has (copowInj hpow I i) (copowInj hpow I j)).cone.pt ⟶ Z) : u = v := by
  obtain ⟨δ, _⟩ := copowInj_disjoint_apex_map hpow I hij
  -- apex of (inl, inr) pullback ≅ bottomSub(coprodObj 1 1).dom ≅ 0; compose δ to land in 0.
  obtain ⟨e, he_iso⟩ := coprodInjections_disjoint (one : 𝒞) (one : 𝒞)
  -- e : pbC.apex → (bottomSub (coprodObj 1 1)).dom ;  then to (bottomSub 1).dom via dom-iso.
  obtain ⟨θ, hθ⟩ := bottomSub_dom_iso (coprodObj (one : 𝒞) (one : 𝒞)) (one : 𝒞)
  let z : (HasPullbacks.has (copowInj hpow I i) (copowInj hpow I j)).cone.pt
      ⟶ (bottomSub (one : 𝒞)).dom := δ ≫ e ≫ θ
  -- (bottomSub 1).dom = (PreLogos.bottom 1).dom = coterminator zero;  any map to 0 is iso.
  have hz_iso : IsIso z := any_map_to_zero_is_iso (inferInstance : PreLogos 𝒞) z
  -- z iso ⟹ apex ≅ 0 ⟹ any two maps out agree (precompose z⁻¹ and use init_uniq).
  obtain ⟨zinv, hzz, hzinv⟩ := hz_iso
  let ct := minimal_subobject_of_one_is_coterminator (inferInstance : PreLogos 𝒞)
  calc u = (z ≫ zinv) ≫ u := by rw [hzz, Cat.id_comp]
    _ = z ≫ (zinv ≫ u) := Cat.assoc _ _ _
    _ = z ≫ (zinv ≫ v) := by rw [ct.init_uniq (zinv ≫ u) (zinv ≫ v)]
    _ = (z ≫ zinv) ≫ v := (Cat.assoc _ _ _).symm
    _ = v := by rw [hzz, Cat.id_comp]

/-! ### STEP 4 — the map-OUT (cotupling) via the infinitary disjoint gluing

  `cotup f : obj → X` is built as the unique map whose GRAPH is the join of the `I` partial
  graphs.  Each partial graph is the relation `P_i := (graph (inj i))° ⊚ graph (f i) : obj ⇸ X`
  (the graph of "defined on `imᵢ`, value `f i`").  The relation `G := binRelSub (⋁ᵢ relSub P_i)`
  tabulated by their join is shown TOTAL (left leg a cover — `copowInj_jointly_cover`) and SIMPLE
  (left leg monic — functionality).

  Functionality is the honest infinitary content: `compose_extJoin_right` (STEP 2) distributes
  `G° ⊚ G` over the join into `⋁ⱼ (G° ⊚ P_j)`, and a second distribution reduces each
  `G° ⊚ P_j` to `⋁ᵢ (P_i° ⊚ P_j)` (via reciprocals); the diagonal terms `P_i° ⊚ P_i ≤ 1`
  (`diag_le_one`, `inj i` monic) and the off-diagonal `P_i° ⊚ P_j ≤ 1` (`cross_le_one`, from
  `1+1` disjointness `copowInj_disjoint_maps_agree`) collapse the join into `graph (id X)`. -/

/-- The `i`-th partial-graph relation `obj ⇸ X`: graph of "defined on `imᵢ`, value `f i`". -/
noncomputable def copowPartial {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) (i : I) :
    BinRel 𝒞 (copowObj hpow I) X :=
  (graph (copowInj hpow I i))° ⊚ graph (f i)

/-- Any map from terminal is monic. -/
private theorem mono_from_one {A : 𝒞} (g : (one : 𝒞) ⟶ A) : Mono g :=
  fun u v _ => term_uniq u v

/-- **The canonical point** of the partial graph `P_i = (graph (inj i))° ⊚ graph (f i)`:
    the pullback over `(id_1, id_1)` has the obvious point `id_1`, whose span value is
    `pair (inj i) (f i)`.  Gives `q : 1 → P_i.src` with `q ≫ pair P_i.colA P_i.colB
    = pair (inj i) (f i)` (so `P_i` "contains" the point `(inj i, f i)`). -/
theorem copowPartial_point {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) (i : I) :
    ∃ q : (one : 𝒞) ⟶ (copowPartial hpow I f i).src,
      q ≫ (copowPartial hpow I f i).colA = copowInj hpow I i ∧
      q ≫ (copowPartial hpow I f i).colB = f i := by
  -- unfold the composition `(graph (inj i))° ⊚ graph (f i)`.
  let xr : BinRel 𝒞 (copowObj hpow I) (one : 𝒞) := (graph (copowInj hpow I i))°
  let yr : BinRel 𝒞 (one : 𝒞) X := graph (f i)
  -- pb = pullback (xr.colB, yr.colA) = pullback (id_1, id_1).
  let pb := HasPullbacks.has xr.colB yr.colA
  have hcw : (Cat.id (one : 𝒞)) ≫ xr.colB = (Cat.id (one : 𝒞)) ≫ yr.colA := by
    show (Cat.id (one : 𝒞)) ≫ Cat.id (one : 𝒞) = (Cat.id (one : 𝒞)) ≫ Cat.id (one : 𝒞); rfl
  let c : Cone xr.colB yr.colA := ⟨(one : 𝒞), Cat.id (one : 𝒞), Cat.id (one : 𝒞), hcw⟩
  let u : (one : 𝒞) ⟶ pb.cone.pt := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = Cat.id (one : 𝒞) := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = Cat.id (one : 𝒞) := pb.lift_snd c
  let span : pb.cone.pt ⟶ prod (copowObj hpow I) X :=
    pair (pb.cone.π₁ ≫ xr.colA) (pb.cone.π₂ ≫ yr.colB)
  refine ⟨u ≫ image.lift span, ?_, ?_⟩
  · -- (u ≫ lift) ≫ (P_i.colA = (image span).arr ≫ fst) = u ≫ span ≫ fst = u ≫ π₁ ≫ inj i = inj i.
    show (u ≫ image.lift span) ≫ ((image span).arr ≫ fst) = copowInj hpow I i
    have hfac : (u ≫ image.lift span) ≫ ((image span).arr ≫ fst) = u ≫ (span ≫ fst) := by
      rw [← Cat.assoc, Cat.assoc u, image.lift_fac, Cat.assoc]
    rw [hfac, show span ≫ fst = pb.cone.π₁ ≫ xr.colA from fst_pair _ _, ← Cat.assoc, hu₁,
      Cat.id_comp]
    rfl
  · show (u ≫ image.lift span) ≫ ((image span).arr ≫ snd) = f i
    have hfac : (u ≫ image.lift span) ≫ ((image span).arr ≫ snd) = u ≫ (span ≫ snd) := by
      rw [← Cat.assoc, Cat.assoc u, image.lift_fac, Cat.assoc]
    rw [hfac, show span ≫ snd = pb.cone.π₂ ≫ yr.colB from snd_pair _ _, ← Cat.assoc, hu₂,
      Cat.id_comp]
    rfl

/-- **Per-pair atomic bound.**  `P_i° ⊚ P_j ≤ graph (id X)` for all `i, j` — single-valuedness of
    the union of partial graphs.  Diagonal: `diag_le_one`.  Off-diagonal: `cross_le_one` with the
    cocone equation from disjointness (`copowInj_disjoint_maps_agree`). -/
theorem copowPartial_pair_le {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) (i j : I) :
    RelLe ((copowPartial hpow I f i)° ⊚ (copowPartial hpow I f j)) (graph (Cat.id X)) := by
  by_cases hij : i = j
  · subst hij
    -- diagonal: P_i° ⊚ P_i ≤ 1  with  P_i = (inj i)° ⊚ (f i).
    exact diag_le_one (copowInj hpow I i) (f i) (mono_from_one (copowInj hpow I i))
  · -- cross term: needs `hxyg : (inj i ⊚ (inj j)°) ⊚ (f j) ≤ (f i)` from disjointness.
    let pb := HasPullbacks.has (copowInj hpow I i) (copowInj hpow I j)
    have hinter : RelLe (graph (copowInj hpow I i) ⊚ (graph (copowInj hpow I j))°)
        ((graph pb.cone.π₁)° ⊚ graph pb.cone.π₂) :=
      inter_lemma (copowInj hpow I i) (copowInj hpow I j) (Cat.id (copowObj hpow I))
        (copowInj hpow I i) (copowInj hpow I j) (Cat.comp_id _) (Cat.comp_id _)
    have hw : pb.cone.π₁ ≫ f i = pb.cone.π₂ ≫ f j :=
      copowInj_disjoint_maps_agree hpow I hij _ _
    have hxyg : RelLe ((graph (copowInj hpow I i) ⊚ (graph (copowInj hpow I j))°) ⊚ graph (f j))
        (graph (f i)) :=
      hxyg_lemma (f i) (f j) pb.cone.π₁ pb.cone.π₂
        (graph (copowInj hpow I i) ⊚ (graph (copowInj hpow I j))°) hinter hw
    exact cross_le_one (copowInj hpow I i) (copowInj hpow I j) (f i) (f j) hxyg

/-- **FUNCTIONALITY (simplicity).**  The union relation `G = binRelSub (⋁ᵢ relSub P_i)` is simple:
    `G° ⊚ G ≤ graph (id X)`.  Distribute the join twice (STEP 2 `compose_extJoin_right`), collapse
    each `P_i° ⊚ P_j` by `copowPartial_pair_le`. -/
theorem copowUnion_simple {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) :
    Simple (binRelSub (extJoin hpow LocallySmallTopos.wellPowered
      (fun U => ∃ i, U = relSub (copowPartial hpow I f i)))) := by
  let wp := LocallySmallTopos.wellPowered (𝒞 := 𝒞)
  let S : Subobject 𝒞 (prod (copowObj hpow I) X) → Prop :=
    fun U => ∃ i, U = relSub (copowPartial hpow I f i)
  let G : BinRel 𝒞 (copowObj hpow I) X := binRelSub (extJoin hpow wp S)
  -- A reusable bound: `T ⊚ binRelSub W ≤ graph id` whenever each `T ⊚ P_i ≤ graph id` and W∈S.
  -- We need: for each W with S W, `G° ⊚ binRelSub W ≤ graph (id X)`.
  -- Reduce via reciprocal to `(binRelSub W)° ⊚ G ≤ graph id`, then distribute G's join.
  have key : ∀ (T : BinRel 𝒞 X (copowObj hpow I)),
      (∀ i, RelLe (T ⊚ binRelSub (relSub (copowPartial hpow I f i)))
        (graph (Cat.id X))) →
      RelLe (T ⊚ G) (graph (Cat.id X)) := by
    intro T hpieces
    -- T ⊚ G = T ⊚ binRelSub(extJoin S) ≤ ⋁ {relSub (T ⊚ binRelSub W) | S W}  (STEP 2).
    have hdist := compose_extJoin_right hpow T S
    -- the join ≤ relSub(graph id), since each member ≤ relSub(graph id).
    have hbound : (extJoin hpow wp
          (fun U => ∃ W, S W ∧ U = relSub (T ⊚ binRelSub W))).le
        (relSub (graph (Cat.id X))) := by
      refine extJoin_least hpow wp _ (relSub (graph (Cat.id X))) (fun U hmem => ?_)
      obtain ⟨W, ⟨i, hWi⟩, hU⟩ := hmem
      rw [hU, hWi]
      exact subLe_of_relLe (hpieces i)
    exact relLe_of_subLe (subLe_trans hdist hbound)
  -- Now Simple G : G° ⊚ G ≤ graph (id X).  Apply `key` with T := G°.
  show RelLe (G° ⊚ G) (graph (Cat.id X))
  refine key (G°) (fun i => ?_)
  -- G° ⊚ binRelSub(relSub P_i) ≤ graph id  via reciprocal + a second distribution.
  -- reciprocal: (G° ⊚ binRelSub(relSub P_i))° = (binRelSub(relSub P_i))° ⊚ G.
  have hrecip : RelLe ((G° ⊚ binRelSub (relSub (copowPartial hpow I f i)))°)
      ((binRelSub (relSub (copowPartial hpow I f i)))° ⊚ G) := by
    have h := (reciprocal_comp (G°) (binRelSub (relSub (copowPartial hpow I f i)))).1
    rwa [reciprocal_invol] at h
  -- (binRelSub(relSub P_i))° ⊚ G ≤ graph id  via `key` with T := (binRelSub(relSub P_i))°.
  have hPiG : RelLe ((binRelSub (relSub (copowPartial hpow I f i)))° ⊚ G)
      (graph (Cat.id X)) := by
    refine key ((binRelSub (relSub (copowPartial hpow I f i)))°) (fun j => ?_)
    -- (binRelSub(relSub P_i))° ⊚ binRelSub(relSub P_j) ≤ P_i° ⊚ P_j ≤ graph id.
    refine rel_le_trans (compose_le (reciprocal_mono (binRelSub_relSub_relLe _).1)
      (binRelSub_relSub_relLe _).1) ?_
    exact copowPartial_pair_le hpow I f i j
  -- so (G° ⊚ binRelSub(relSub P_i))° ≤ graph id; take reciprocal, (graph id)° = graph id.
  have hco : RelLe ((G° ⊚ binRelSub (relSub (copowPartial hpow I f i)))°)
      (graph (Cat.id X)) := rel_le_trans hrecip hPiG
  have h2 := reciprocal_mono hco
  rwa [reciprocal_invol, show (graph (Cat.id X))° = graph (Cat.id X) from rfl] at h2

/-- **TOTALITY.**  The left leg of `G` is a cover: each `inj i` factors through it (`P_i`'s
    first leg lifts into the join), and `copowInj_jointly_cover` forces iso. -/
theorem copowUnion_total {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) :
    Cover (binRelSub (extJoin hpow LocallySmallTopos.wellPowered
      (fun U => ∃ i, U = relSub (copowPartial hpow I f i)))).colA := by
  let wp := LocallySmallTopos.wellPowered (𝒞 := 𝒞)
  let S : Subobject 𝒞 (prod (copowObj hpow I) X) → Prop :=
    fun U => ∃ i, U = relSub (copowPartial hpow I f i)
  let G : BinRel 𝒞 (copowObj hpow I) X := binRelSub (extJoin hpow wp S)
  -- factor each `inj i` through `G.colA`.  P_i = (inj i)° ⊚ (f i): its image contains the point
  -- (inj i, f i); so `pair (inj i) (f i)` factors through relSub P_i ≤ extJoin S = G.src, and
  -- the first leg recovers `inj i`.
  -- A direct factorization: `s i : 1 → G.src` with `s i ≫ G.colA = inj i`.
  have hfactor : ∀ i, ∃ s : (one : 𝒞) ⟶ G.src, s ≫ G.colA = copowInj hpow I i := by
    intro i
    -- the canonical point of P_i, with `q ≫ P_i.colA = inj i`, `q ≫ P_i.colB = f i`.
    obtain ⟨q, hqA, hqB⟩ := copowPartial_point hpow I f i
    have hq : q ≫ (relSub (copowPartial hpow I f i)).arr = pair (copowInj hpow I i) (f i) := by
      show q ≫ pair (copowPartial hpow I f i).colA (copowPartial hpow I f i).colB = _
      exact pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]; exact hqA)
        (by rw [Cat.assoc, snd_pair]; exact hqB)
    -- relSub P_i ≤ extJoin S, giving l with l ≫ (extJoin S).arr = (relSub P_i).arr.
    obtain ⟨l, hl⟩ := extJoin_upper hpow wp S (relSub (copowPartial hpow I f i)) ⟨i, rfl⟩
    refine ⟨q ≫ l, ?_⟩
    show (q ≫ l) ≫ ((extJoin hpow wp S).arr ≫ fst) = copowInj hpow I i
    have hpt : (q ≫ l) ≫ (extJoin hpow wp S).arr = pair (copowInj hpow I i) (f i) := by
      rw [Cat.assoc, hl]; exact hq
    rw [← Cat.assoc, hpt, fst_pair]
  -- now run the cover criterion through `copowInj_jointly_cover`.
  intro C m gg hm hgm
  refine copowInj_jointly_cover hpow I m hm (fun i => (hfactor i).choose ≫ gg) (fun i => ?_)
  rw [Cat.assoc, hgm, (hfactor i).choose_spec]

/-- The map-OUT (cotupling) — built sorry-free as the unique morphism whose graph is the join of
    the partial graphs `P_i`, shown TOTAL + SIMPLE, hence a map by
    `functional_total_relation_is_graph`; the β-law `inj i ≫ c = f i` from `relSub P_i ≤ join`. -/
theorem copowCotup_exists {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) :
    ∃ c : copowObj hpow I ⟶ X, ∀ i, copowInj hpow I i ≫ c = f i := by
  let wp := LocallySmallTopos.wellPowered (𝒞 := 𝒞)
  let S : Subobject 𝒞 (prod (copowObj hpow I) X) → Prop :=
    fun U => ∃ i, U = relSub (copowPartial hpow I f i)
  let G : BinRel 𝒞 (copowObj hpow I) X := binRelSub (extJoin hpow wp S)
  have hsimple : Mono G.colA :=
    (tabulated_is_simple_iff_left_monic G.colA G.colB G.isMonicPair).1 (copowUnion_simple hpow I f)
  have htotal : Cover G.colA := copowUnion_total hpow I f
  obtain ⟨c, ⟨⟨h, hhA, hhB⟩, _⟩, _⟩ :=
    functional_total_relation_is_graph G hsimple htotal
  -- key: G.colA ≫ c = G.colB.
  have hkey : G.colA ≫ c = G.colB := by
    have hh : h = G.colA := by
      have := hhA; dsimp [graph] at this; rwa [Cat.comp_id] at this
    have := hhB; dsimp [graph] at this; rw [hh] at this; exact this
  refine ⟨c, fun i => ?_⟩
  -- inj i factors through G.colA (totality factorization), and G.colA ≫ c = G.colB, so
  -- inj i ≫ c = (s ≫ G.colA) ≫ c = s ≫ G.colB = f i.
  obtain ⟨q, hq⟩ : ∃ q : (one : 𝒞) ⟶ G.src,
      q ≫ (extJoin hpow wp S).arr = pair (copowInj hpow I i) (f i) := by
    -- the canonical point of P_i (same as in `copowUnion_total`).
    obtain ⟨qp, hqA, hqB⟩ := copowPartial_point hpow I f i
    have hqp : qp ≫ pair (copowPartial hpow I f i).colA (copowPartial hpow I f i).colB
        = pair (copowInj hpow I i) (f i) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]; exact hqA)
        (by rw [Cat.assoc, snd_pair]; exact hqB)
    obtain ⟨l, hl⟩ := extJoin_upper hpow wp S (relSub (copowPartial hpow I f i)) ⟨i, rfl⟩
    refine ⟨qp ≫ l, ?_⟩
    rw [Cat.assoc, hl]
    show qp ≫ pair (copowPartial hpow I f i).colA (copowPartial hpow I f i).colB = _
    exact hqp
  have hA : q ≫ G.colA = copowInj hpow I i := by
    show q ≫ ((extJoin hpow wp S).arr ≫ fst) = copowInj hpow I i
    rw [← Cat.assoc, hq, fst_pair]
  have hB : q ≫ G.colB = f i := by
    show q ≫ ((extJoin hpow wp S).arr ≫ snd) = f i
    rw [← Cat.assoc, hq, snd_pair]
  calc copowInj hpow I i ≫ c = (q ≫ G.colA) ≫ c := by rw [hA]
    _ = q ≫ (G.colA ≫ c) := Cat.assoc _ _ _
    _ = q ≫ G.colB := by rw [hkey]
    _ = f i := hB

/-- **Copower-of-1 from arbitrary powers** — the effective-disjoint-union carving of `∐ᵢ1` as a
    subobject of `∏ᵢ(1+1)`.  Fully SORRY-FREE: `obj`, `inj`, `inj_cotup`, `cotup_uniq`, and
    `cotup` (map-OUT existence, `copowCotup_exists`) are all built; the latter via the honest
    infinitary disjoint gluing (TOTAL + SIMPLE union-of-partial-graphs, functionality from the
    §1.616/§1.84 composition-over-join distributivity).  Axioms `[propext, Classical.choice,
    Quot.sound]`.  See the module doc above. -/
noncomputable def toposCopowerOfOne (hpow : HasArbitraryPowers (𝒞 := 𝒞)) (I : Type v) :
    CopowerOfOne I 𝒞 where
  obj := copowObj hpow I
  inj := copowInj hpow I
  cotup {X} f := (copowCotup_exists hpow I f).choose
  inj_cotup {X} f i := (copowCotup_exists hpow I f).choose_spec i
  cotup_uniq {X} f h hh :=
    copowerImages_jointly_epi hpow I h (copowCotup_exists hpow I f).choose
      (fun i => by rw [hh i, (copowCotup_exists hpow I f).choose_spec i])

end CopowerBuild

/-! ## §1.968 — `Cocomplete` from general coproducts + coequalizers

  The colimit-dual of `eq_prod_complete` (S1_82:291).  Every small colimit is the COEQUALIZER of
  two maps between coproducts: `colim D = coeq( ∐_{arrows a} D(src a) ⇉ ∐_{objects i} D i )`, where
  the two maps send the `a`-injection to `D(arr a) ≫ inj(tgt a)` and `inj(src a)` respectively.
  Reuses the EXISTING general-family `Coproduct`/`HasAllCoproducts` (S1_84) and `HasCoequalizer`
  (S1_58).  Banked as `cocomplete_of_coproducts_coequalizers` — reusable infra (S1_97's ∐ₙAⁿ).
  Axioms: `[propext, Classical.choice, Quot.sound]` (inherited from its inputs only). -/
section CocompleteFromCoprodCoeq
variable {ℬ : Type u} [Cat.{v} ℬ]

/-- **§1.968**: general coproducts + coequalizers ⟹ cocomplete (dual of `eq_prod_complete`). -/
noncomputable def cocomplete_of_coproducts_coequalizers
    (hcp : HasAllCoproducts ℬ) (hce : HasCoequalizers ℬ) : Cocomplete ℬ where
  hasColimit {𝒟} _ D hD := by
    classical
    -- Σ of arrows in 𝒟; coproduct of sources over arrows, and of objects.
    let Arr := Σ (i : 𝒟) (j : 𝒟), (i ⟶ j)
    let srcOf : Arr → 𝒟 := fun a => a.fst
    let tgtOf : Arr → 𝒟 := fun a => a.snd.fst
    let arrOf : (a : Arr) → srcOf a ⟶ tgtOf a := fun a => a.snd.snd
    let P := hcp.coprod D                                  -- ∐_objects D
    let Q := hcp.coprod (fun a : Arr => D (srcOf a))       -- ∐_arrows D(src)
    -- mapF's a-leg = D(arr a) ≫ inj(tgt a); mapG's = inj(src a).
    let mapF : Q.obj ⟶ P.obj := Q.desc (fun a => hD.map (arrOf a) ≫ P.inj (tgtOf a))
    let mapG : Q.obj ⟶ P.obj := Q.desc (fun a => P.inj (srcOf a))
    let ce := hce.coeq mapF mapG
    let ιi : (i : 𝒟) → D i ⟶ ce.obj := fun i => P.inj i ≫ ce.map
    -- Cocone naturality: D(x) ≫ ιj = ιi.  From `inj(src⟨i,j,x⟩) ≫ map = D(x) ≫ inj(tgt) ≫ map`
    -- (the a=⟨i,j,x⟩ component of `mapG ≫ ce.map = mapF ≫ ce.map`).
    have nat_pf : ∀ {i j : 𝒟} (x : i ⟶ j), hD.map x ≫ ιi j = ιi i := by
      intro i j x
      let a : Arr := ⟨i, j, x⟩
      have hFG : mapF ≫ ce.map = mapG ≫ ce.map := by
        rw [ce.eq]
      -- a-leg of both sides of hFG.
      have hstep := congrArg (fun t => Q.inj a ≫ t) hFG
      simp only [mapF, mapG] at hstep
      rw [← Cat.assoc, ← Cat.assoc, Q.fac, Q.fac] at hstep
      -- hstep : (D(arr a) ≫ inj(tgt a)) ≫ map = inj(src a) ≫ map
      show hD.map x ≫ P.inj j ≫ ce.map = P.inj i ≫ ce.map
      calc hD.map x ≫ P.inj j ≫ ce.map
          = (hD.map (arrOf a) ≫ P.inj (tgtOf a)) ≫ ce.map := by rw [Cat.assoc]
        _ = P.inj (srcOf a) ≫ ce.map := hstep
        _ = P.inj i ≫ ce.map := rfl
    -- Given a cocone c, `P.desc c.ι` coequalizes mapF and mapG.
    have desc_eq : ∀ (c : DiagCocone D), mapF ≫ P.desc c.ι = mapG ≫ P.desc c.ι := by
      intro c
      have hF : mapF ≫ P.desc c.ι = Q.desc (fun a => hD.map (arrOf a) ≫ c.ι (tgtOf a)) := by
        apply Q.uniq; intro a
        rw [← Cat.assoc, Q.fac, Cat.assoc, P.fac]
      have hG : mapG ≫ P.desc c.ι = Q.desc (fun a => c.ι (srcOf a)) := by
        apply Q.uniq; intro a
        rw [← Cat.assoc, Q.fac, P.fac]
      rw [hF, hG]; congr 1; funext a; exact c.nat (arrOf a)
    exact
      { cocone := { nadir := ce.obj, ι := ιi, nat := nat_pf }
        lift := fun c => ce.desc (P.desc c.ι) (desc_eq c)
        fac := fun c i => by
          show (P.inj i ≫ ce.map) ≫ ce.desc (P.desc c.ι) (desc_eq c) = c.ι i
          rw [Cat.assoc, ce.fac, P.fac]
        uniq := fun c u hu => by
          apply ce.uniq
          apply P.uniq
          intro i
          rw [← Cat.assoc]; exact hu i }

/-- The DISCRETE CATEGORY on `I` (local copy; the S1_82 `discCat82` is private). -/
private instance discCatTC {I : Type v} : Cat.{v} I where
  Hom i j     := ULift.{v} (PLift (i = j))
  id _        := ⟨⟨rfl⟩⟩
  comp f g    := ⟨⟨f.down.down.trans g.down.down⟩⟩
  id_comp _   := rfl
  comp_id _   := rfl
  assoc _ _ _ := rfl

/-- Every `A : I → ℬ` is a functor on the discrete category (local copy). -/
private instance discFunTC {I : Type v} (A : I → ℬ) : @Functor I discCatTC ℬ _ A where
  map {i j} h  := h.down.down ▸ Cat.id (A i)
  map_id _     := rfl
  map_comp f g := by
    obtain ⟨⟨hij⟩⟩ := f; obtain ⟨⟨hjk⟩⟩ := g; subst hij; subst hjk; exact (Cat.id_comp _).symm

/-- **Cocomplete ⟹ all coproducts** (colimit-dual of `complete_hasProducts`).  A coproduct is the
    colimit of the discrete diagram; reusable infra (e.g. Lawvere→Tierney's `∐(gen set)`). -/
noncomputable def cocompleteCoconeOf {I : Type v} (A : I → ℬ) (X : ℬ) (f : ∀ i, A i ⟶ X) :
    @DiagCocone I discCatTC ℬ _ A (discFunTC A) :=
  { nadir := X, ι := f,
    nat := by intro i j x; obtain ⟨⟨hij⟩⟩ := x; subst hij; simp [Functor.map, Cat.id_comp] }

noncomputable def cocomplete_hasAllCoproducts (hc : Cocomplete ℬ) : HasAllCoproducts ℬ where
  coprod {I} A :=
    { obj  := (@hc.hasColimit I discCatTC A (discFunTC A)).cocone.nadir
      inj  := (@hc.hasColimit I discCatTC A (discFunTC A)).cocone.ι
      desc := fun {X} f => (@hc.hasColimit I discCatTC A (discFunTC A)).lift (cocompleteCoconeOf A X f)
      fac  := fun {X} f i => (@hc.hasColimit I discCatTC A (discFunTC A)).fac (cocompleteCoconeOf A X f) i
      uniq := fun {X} f h hh => (@hc.hasColimit I discCatTC A (discFunTC A)).uniq (cocompleteCoconeOf A X f) h hh }

end CocompleteFromCoprodCoeq

/-! ## §1.967 powers ↔ copowers, §1.968 complete ↔ cocomplete, §1.969 Lawvere = Tierney

  Relocated here from `Fredy/S1_95.lean` (which this file imports): the powers↔copowers
  equivalence is now CLOSED sorry-free because its sole residual — the (a)→(b) carving
  `∐ᵢ1 ⊂ ∏ᵢ(1+1)` (`toposCopowerOfOne`) — is built above.  §1.968/§1.969 remain honest
  `sorry`s, but the gap is now PRECISELY ISOLATED to general-family coproducts: BANKED sorry-free
  here are `wellPoweredSub_of_topos` (§1.843 well-poweredness from the classifier),
  `cocomplete_of_coproducts_coequalizers` (Cocomplete from coproducts+coeq) and
  `cocomplete_hasAllCoproducts` (the discrete-colimit coproduct).  The single missing construction
  is `HasAllCoproducts` via the §1.968 cogenerator-carving of `∐ᵢAᵢ` ⊆ `C^K`; see the sharpened
  residual on `lawvere_eq_tierney`. -/

-- Make the GENUINE `Topos.toHasBinaryProducts` win instance search for `HasBinaryProducts 𝒞`
-- (the §1.92 `topos_has_exponentials.toHasBinaryProducts` is deprioritised but could still be
-- picked, routing a products goal through `sorry`-derived structure).  Keeps these theorems
-- axiom-honest, mirroring the §1.92 `attribute [local instance]` pattern.
attribute [local instance 10000] Topos.toHasBinaryProducts

/-- **§1.967**: In a locally small topos, arbitrary powers exist iff arbitrary copowers exist.

    * **(a)→(b)** CLOSED sorry-free.  Build a copower-of-1 datum `CopowerOfOne I 𝒞` for every `I`
      via `toposCopowerOfOne` (the effective-disjoint-union carving `∐ᵢ1 ⊂ ∏ᵢ(1+1)`, with the
      map-OUT universal property supplied by the infinitary disjoint gluing above), then
      `topos_copowers_equiv_copowers_of_one` assembles `HasArbitraryCopowers`.
    * **(b)→(a)** CLOSED sorry-free.  Reduce to copowers-of-1 (sibling iff), then set
      `∏ᵢ A := A^(∐ᵢ1)` (`powersOfCopowersOfOne`); the power UP is the exponential law
      `Hom(X, A^cI) ≅ Hom(cI×X, A) ≅ ∏ᵢ Hom(X,A)` (`prod_distrib_copow`). -/
theorem topos_powers_copowers_equiv [LocallySmallTopos 𝒞] [HasBinaryCoproducts 𝒞] :
    (Nonempty (@HasArbitraryPowers 𝒞 _ Topos.toHasBinaryProducts)) ↔
    (Nonempty (HasArbitraryCopowers (𝒞 := 𝒞))) :=
  -- TERM MODE (not `by constructor`): the tactic `constructor` re-synthesizes the iff's
  -- `HasBinaryProducts` per goal, which can route the type through the §1.92
  -- `topos_has_exponentials.toHasBinaryProducts` and pick up `sorryAx`; the explicit
  -- `⟨forward, backward⟩` shares ONE elaboration of the statement, staying axiom-honest.
  ⟨fun ⟨hpow⟩ =>
      -- (a)→(b): every `I` has a copower-of-1 (`toposCopowerOfOne`), so the sibling iff yields
      -- `HasArbitraryCopowers`.
      (topos_copowers_equiv_copowers_of_one).mpr (fun I => ⟨toposCopowerOfOne hpow I⟩),
   fun hcop =>
      -- (b)→(a): reduce to copowers-of-1 (sibling iff), then `A^(∐ᵢ1)`.
      let hone : ∀ (I : Type v), Nonempty (CopowerOfOne I 𝒞) :=
        (topos_copowers_equiv_copowers_of_one).mp hcop
      let pw := powersOfCopowersOfOne (fun I => Classical.choice (hone I))
      ⟨{ pow := pw.pow, proj := fun {I A} => pw.proj, tupling := fun {I A X} => pw.tupling,
         tupling_proj := fun {I A X} => pw.tupling_proj,
         tupling_uniq := fun {I A X} => pw.tupling_uniq }⟩⟩

/-- **§1.968**: A locally small topos is complete iff it is cocomplete.

    RESIDUAL (honest `sorry`).  The two §1.96x results that just closed
    (`progenitor_omega_exp_cogenerates`, `toposCopowerOfOne`/`topos_powers_copowers_equiv`)
    do NOT reach this; the blocker is no longer the §1.543 capitalization wall but THREE
    genuinely-unbuilt elementary constructions, listed in precise dependency order:

    1. **`HasProducts`/`HasCoproducts` (general, distinct-object families)** — the entire
       copower/power layer here (`HasArbitraryPowers`, `HasArbitraryCopowers`, `CopowerOfOne`)
       handles only the CONSTANT family `∏ᵢA` / `∐ᵢA`.  `Complete`/`Cocomplete` (S1_82) and the
       GAFT-dual engine `cocomplete_of_complete_precocomplete` consume the general-family
       `HasProducts` (S1_82:133); no general `HasCoproducts` class even exists yet.

    2. **Cogenerator-carving of general coproducts** (Freyd §1.968/§1.969): given `{Aᵢ}` and the
       cogenerator `C := Ω^G`, embed each `Aᵢ ↣ B := ∏_{(Aᵢ,C)} C` and carve `∐ᵢAᵢ` as a
       subobject of the COPOWER `∐ᵢB` (= `extJoin` of the injection images).  The dual carves
       `∏ᵢAᵢ` from copowers.  This needs item 1 PLUS the §1.84 well-poweredness `extJoin`
       already available here — but NOT yet assembled into a coproduct/product object.

    3. **`coeq + general coproducts ⟹ Cocomplete`** — NOW BANKED as
       `cocomplete_of_coproducts_coequalizers` (above), the colimit-dual of `eq_prod_complete`
       (S1_82:291); `topos_has_coequalizers` supplies the coequalizers.  So `Cocomplete` reduces
       cleanly to item 1 (general `HasAllCoproducts`) once that lands.

    None of these is the cogenerator EXISTENCE (that is now supplied by
    `progenitor_omega_exp_cogenerates`) — but THIS theorem has NO progenitor hypothesis, so even
    a cogenerator is not in hand here (a bare complete locally-small topos need not be
    value-based).  Closing requires either a derived cogenerator or the three constructions
    above; left `sorry`. -/
theorem topos_complete_iff_cocomplete [LocallySmallTopos 𝒞]
    [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞] [HasEqualizers 𝒞] :
    Nonempty (Complete 𝒞) ↔ Nonempty (Cocomplete 𝒞) := by
  sorry

/-- **§1.969**: The LAWVERE DEFINITION of a Grothendieck topos: a cocomplete topos with a
    generating set. -/
class LawvereGrothendieckTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞 where
  /-- Arbitrary coproducts exist. -/
  cocomplete : Cocomplete 𝒞
  /-- A small generating set. -/
  gen_set : 𝒞 → Prop
  has_gen_set : IsGeneratingSet gen_set

/-- **§1.969**: The TIERNEY DEFINITION of a Grothendieck topos: a topos with a progenitor and
    arbitrary copowers of 1. -/
class TierneyGrothendieckTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞,
    HasBinaryCoproducts 𝒞 where
  /-- A progenitor exists. -/
  progenitor : 𝒞
  is_progenitor : IsProgenitor progenitor
  /-- Arbitrary copowers of 1 exist.  FIDELITY (§1.969): a copower IS a colimit and carries the
      FULL universal property — existence AND uniqueness of the cotupling.  The earlier bare
      `∃ h, ∀ i, inj i ≫ h = f i` dropped uniqueness, under-specifying "copower"; a genuine
      `CopowerOfOne I 𝒞` (with `cotup_uniq`, i.e. the injections jointly epic) is what
      "arbitrary copowers of 1" means and what `powersOfCopowersOfOne` (hence the cogenerator
      route) consumes. -/
  copow_one : (I : Type v) → CopowerOfOne I 𝒞

/-- **§1.969**: The Lawvere and Tierney definitions yield the same notion.

    RESIDUAL (honest `sorry`), SHARPENED.  Of the §1.968/§1.969 coproduct-assembly development,
    THREE of the four prerequisite pieces are now BANKED sorry-free in this file; the SOLE
    remaining blocker is general-family coproducts (`HasAllCoproducts`).

    BANKED (reusable, sorry-free):
    * **`wellPoweredSub_of_topos`** (§1.843, above) — `WellPoweredSub 𝒞` from the classifier alone,
      so `LocallySmallTopos.wellPowered` (hence every copower lemma here) is available from bare
      Tierney/Lawvere data.  (Old blocker 2 CLOSED.)
    * **`copow_one`** now delivers a genuine `CopowerOfOne I 𝒞` (with `cotup_uniq`), so the
      copower-of-1 → `HasArbitraryPowers` (`powersOfCopowersOfOne`) → cogenerator route is
      unobstructed.  (Old blocker 1 CLOSED, by the fidelity strengthening of the class field.)
    * **`cocomplete_of_coproducts_coequalizers`** (§1.968, above) — `Cocomplete` reduces to
      `HasAllCoproducts` + `HasCoequalizers`; the topos supplies `topos_has_coequalizers`.  (The
      `coeq + coproducts ⟹ Cocomplete` part of old blocker 3 CLOSED.)
    * **`cocomplete_hasAllCoproducts`** (above) — `Cocomplete ⟹ HasAllCoproducts` (discrete-diagram
      colimit), so the Lawvere side's bundled `cocomplete` field DOES give all coproducts directly.
    * Tierney→Lawvere generating set: `IsProgenitor G` IS `IsGeneratingSet (fun X => ∃ m:X⟶G, Mono m)`
      definitionally.  Lawvere→Tierney `copow_one`: `∐ᵢ1` is the `cocomplete_hasAllCoproducts`
      coproduct of the constant-`one` family, which IS a `CopowerOfOne` (`cotup_uniq` = `Coproduct.uniq`).

    TWO REMAINING BLOCKERS (genuinely unbuilt; statement may NOT be weakened):
    1. **Tierney→Lawvere `Cocomplete`** needs `HasAllCoproducts 𝒞` — general-family `∐ᵢAᵢ`
       (DISTINCT objects), Freyd §1.968 cogenerator-carving.  With `C := Ω^G`
       (`progenitor_omega_exp_cogenerates`), `K := ∏ᵢ[Aᵢ,C]` (`Type v` by
       `wellPoweredSub_of_topos`/local smallness), each `Aᵢ ↣ B := C^K` monically via the
       family-evaluation tuple; carve `∐ᵢAᵢ := ⋁ᵢ image(jᵢ) ⊆ B` (`extJoin`), map-OUT UP by the
       infinitary disjoint gluing of `CopowerBuild` — BUT that gluing (TOTAL+SIMPLE
       union-of-partial-graphs, functionality from `compose_extJoin_right`) was specialised to
       `Aᵢ = 1` / ambient `∏ᵢ(1+1)` with `1+1`-disjointness.  Re-running it for general `Aᵢ` with
       cogenerator-separation disjointness is the missing ~400-line development.  (Once it lands,
       Tierney→Lawvere = `cocomplete_of_coproducts_coequalizers` + the progenitor's gen set.)
    2. **Lawvere→Tierney `progenitor`** needs a SINGLE progenitor `G` from the generating set, e.g.
       `G := ∐(gen set)`.  But `LawvereGrothendieckTopos.gen_set : 𝒞 → Prop` carries NO `Type v`
       smallness index, so `{X // gen_set X}` lives in `Type u`; `cocomplete_hasAllCoproducts`
       needs a `Type v` index.  Freyd's generating set is small; this class under-specifies it (a
       fidelity gap parallel to the old `copow_one`).  Forming the coproduct of the gen set — hence
       the progenitor — is blocked without that small index, and the statement may not be changed.
    Left `sorry`; the remaining work is the general-coproduct carving (1), not a wall. -/
theorem lawvere_eq_tierney (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞]
    [HasEqualizers 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] :
    Nonempty (LawvereGrothendieckTopos 𝒞) ↔ Nonempty (TierneyGrothendieckTopos 𝒞) := by
  sorry

end Freyd
