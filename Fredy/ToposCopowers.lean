/-
  §1.967 — Building a genuine copower-of-1 `∐ᵢ1` in a locally small topos with arbitrary powers.

  The EFFECTIVE DISJOINT UNION route.  In a topos `1+1` exists (`topos_is_positive`) and, given
  arbitrary powers `hpow`, the power `∏ᵢ(1+1)` exists.  The copower object is carved as the
  subobject `obj := ⋁ᵢ imᵢ ⊆ ∏ᵢ(1+1)`, the JOIN (`extJoin`) of the images of the candidate
  injections `cand i : 1 → ∏ᵢ(1+1)` — the tuple that is `inr` (true) at coordinate `i` and `inl`
  (false) elsewhere.  The `imᵢ` are pairwise disjoint (`1+1` disjointness), each `≅ 1`.

  STATUS:
  * `inj`, `inj_cotup`, **`cotup_uniq`** — built SORRY-FREE.  `cotup_uniq` (the map-OUT
    uniqueness / jointly-epic injections) is the infinitary analogue of `coprod_jointly_epi`
    with `extJoin_least` (S1_95) in place of the binary `union_min`: form the equalizer
    `E = {h=k}`, show each `imᵢ ≤ E`, then `extJoin_least` forces `obj ≤ E`.  Banked as
    `copowerImages_jointly_epi`.
  * `cotup` (map-OUT EXISTENCE) — the SOLE residual `sorry`.  See the doc on
    `toposCopowerOfOne`: the infinitary disjoint GLUING.  The binary copairing
    `coprod_case_exists` (ToposExists) builds the map out of a union of TWO partial graphs and
    proves single-valuedness (functionality) from the §1.621 binary disjoint gluing
    `disjoint_cover_is_coproduct`.  The infinitary analogue needs FUNCTIONALITY of the
    `I`-indexed union of partial graphs `⋁ᵢ image⟨inj i, f i⟩ ⊆ obj × X`, which requires an
    infinitary `relUnionSub`-simplicity (pairwise-disjoint relational union over an arbitrary
    index) that is NOT built — `HasSubobjectUnions`/`relUnionSub` are binary.  TOTALITY (the
    injections jointly cover `obj`) IS available — same `extJoin_least` argument as `cotup_uniq`
    — and is banked as `copowerInj_jointly_cover`.

  Because `cotup` is the only hole and it is confined to THIS new def, the file is NOT wired into
  `Fredy.lean` (master sorry count unchanged); the bankable pieces above are sorry-free and
  reusable.
-/
import Fredy.S1_95
import Fredy.ToposExists
import Fredy.ToposDistributive
import Fredy.ToposIndexedJoins

universe u v w

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [LocallySmallTopos 𝒞]

open Classical

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

/-! ### The map-OUT (cotupling) residual

  Building `cotup f : obj → X` for a family `f : I → (1 ⟶ X)` is the infinitary DISJOINT
  GLUING.  Mirroring the binary `coprod_case_exists` (ToposExists): the copairing is the unique
  map whose GRAPH is the union of the `I` partial graphs

      `unionGraph f := ⋁ᵢ image⟨inj i ≫ obj.arr restricted, f i⟩ ⊆ obj × X`,

  tabulated as a relation `obj ⇸ X` whose left leg must be a COVER (totality — available via
  `copowInj_jointly_cover`) and MONIC (functionality / single-valuedness).

  FUNCTIONALITY is the wall.  In the binary case `caseRel_colA_monic` proves single-valuedness
  by exhibiting `caseRel ⊆ graph c` where `c` comes from the §1.621 BINARY disjoint gluing
  `disjoint_cover_is_coproduct` — a bootstrap that is itself binary and circular here.  The
  honest infinitary route needs:

    MISSING LEMMA — `relUnion_least_simple` (infinitary `relUnionSub`-simplicity):
      given an `I`-indexed family of partial graphs that are pairwise DISJOINT in their first
      coordinate (here from `1+1` disjointness `coprodInjections_disjoint`, lifted to the
      coordinates of `∏ᵢ(1+1)`), their `extJoin` union relation is SIMPLE (left leg monic).

  This is NOT reducible to the meet/join lattice (`extJoin_upper`/`extJoin_least` give only
  map-IN bounds, never single-valuedness of a tabulated union) and the relational union
  `relUnionSub` (S1_61) is binary.  It is the genuine, precisely-located gap.  Until it is
  built, `cotup` (and hence the full `CopowerOfOne` datum) is the sole `sorry`. -/

/-- The map-OUT (cotupling) — the SOLE residual `sorry` (infinitary disjoint gluing; see doc
    above).  Stated as a standalone existential so that `cotup_uniq` is provable sorry-free from
    `copowerImages_jointly_epi` given the β-law, isolating the hole to this one statement. -/
theorem copowCotup_exists {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) :
    ∃ c : copowObj hpow I ⟶ X, ∀ i, copowInj hpow I i ≫ c = f i := by
  sorry

/-- **Copower-of-1 from arbitrary powers** — the effective-disjoint-union carving of `∐ᵢ1` as a
    subobject of `∏ᵢ(1+1)`.  `obj`, `inj`, `inj_cotup`, and `cotup_uniq` are sorry-free; the
    LATTER uses the BANKED jointly-epic fact `copowerImages_jointly_epi`.  The SOLE residual
    `sorry` is `copowCotup_exists` (map-OUT existence): the infinitary disjoint gluing, blocked
    on the FUNCTIONALITY of the `I`-indexed union of partial graphs (`relUnion_least_simple`,
    the infinitary `relUnionSub`-simplicity — `relUnionSub` is binary; `extJoin` supplies only
    map-IN bounds).  See the doc above. -/
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

end Freyd
