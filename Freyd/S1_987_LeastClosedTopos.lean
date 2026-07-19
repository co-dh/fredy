/-
  Freyd & Scedrov, *Categories and Allegories* §1.987 — the LEAST `(a,t)`-closed
  subobject in a topos, constructed (Sorry-free) via the internal-∀ family-glb
  `bigInter` of `Freyd/InternalForallTopos.lean`.

  ## What this file builds

  For `A`, `a : 1 → A`, `t : A → A`, the predicate `IsClosedSub (named σ) a t` on
  subobjects internalizes to a characteristic map `closedChar a t : [A] → Ω`,
  `σ ↦ (a ∈ σ) ∧ (∀x:A. x∈σ ⇒ t(x)∈σ)`.  Naming the comprehension
  `F = {σ : [A] | closedChar a t}` by `closedFamily a t : 1 → [[A]]`, the family-glb
  `bigInter (closedFamily a t)` is the least `(a,t)`-closed subobject, and we register
  it as `instance : HasLeastClosedSubobject 𝒞`.

  This is the genuine §1.987 content that `Freyd/InternalForall.lean`'s header relocated
  to the hypothesis class; it is now DISCHARGED for every topos, unblocking S1_97.
-/

import Freyd.S1_94_InternalForallTopos

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.987  The closedness predicate `closedChar a t : [A] → Ω` -/

/-- The `t`-stability body `prod A [A] → Ω`, `(x,σ) ↦ (x∈σ) ⇒ (t(x)∈σ)`.  `x∈σ` is
    `⟨fst,snd⟩ ≫ eval`; `t(x)∈σ` is `⟨fst≫t, snd⟩ ≫ eval`. -/
noncomputable def tStableBody {A : 𝒞} (t : A ⟶ A) : prod A (powObj A) ⟶ omega (𝒞 := 𝒞) :=
  pair
    (pair fst snd ≫ eval_exp A (omega (𝒞 := 𝒞)))
    (pair (fst ≫ t) snd ≫ eval_exp A (omega (𝒞 := 𝒞)))
  ≫ impΩ

/-- The internal `t`-stability test `tStable t : [A] → Ω`, `σ ↦ ∀x:A. x∈σ ⇒ t(x)∈σ`.
    Built with the fibered-∀ trick: curry `tStableBody t` in the `x`-slot, then quantify
    over `x : A` with `forallC A` (same recipe as `predF`/`bigInterChar`). -/
noncomputable def tStable {A : 𝒞} (t : A ⟶ A) : powObj A ⟶ omega (𝒞 := 𝒞) :=
  curry (tStableBody t) ≫ forallC A

/-- The closedness characteristic map `closedChar a t : [A] → Ω`,
    `σ ↦ (a ∈ σ) ∧ (∀x. x∈σ ⇒ t(x)∈σ)`: the meet of `memAtPoint a` and `tStable t`. -/
noncomputable def closedChar {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) : powObj A ⟶ omega (𝒞 := 𝒞) :=
  pair (memAtPoint a) (tStable t) ≫ omegaMeet

/-- The family name `closedFamily a t : 1 → [[A]]` of `F = {σ : [A] | closedChar a t}`. -/
noncomputable def closedFamily {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) : one ⟶ powObj (powObj A) :=
  curry (fst ≫ closedChar a t)

/-- **KEY LEMMA — `membershipMap (closedFamily a t) = closedChar a t`.**  Mirrors
    `membershipMap_imageFamily`, via the general `membershipMap_curry_fst`. -/
theorem membershipMap_closedFamily {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) :
    membershipMap (closedFamily a t) = closedChar a t := by
  rw [closedFamily, membershipMap_curry_fst]

/-! ## §1.987  `least_le` — the family-glb is below every closed subobject -/

/-- **`memAtPoint` at a name.**  For `σ : 1 → [A]`, `σ ≫ memAtPoint a = a ≫ membershipMap σ`,
    i.e. `a ∈ (named σ)`.  Both sides are `⟨a, σ⟩ ≫ eval` after the terminal collapses. -/
theorem memAtPoint_at_name {A : 𝒞} (a : one ⟶ A) (σ : one ⟶ powObj A) :
    σ ≫ memAtPoint a = a ≫ membershipMap σ := by
  rw [memAtPoint, membershipMap, ← Cat.assoc, ← Cat.assoc]
  congr 1
  have hL : σ ≫ pair (term (powObj A) ≫ a) (Cat.id (powObj A)) = pair a σ := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, term_uniq (σ ≫ term (powObj A)) (Cat.id one), Cat.id_comp]
    · rw [Cat.assoc, snd_pair, Cat.comp_id]
  have hR : a ≫ pair (Cat.id A) (term A ≫ σ) = pair a σ := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, Cat.comp_id]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, term_uniq (a ≫ term A) (Cat.id one), Cat.id_comp]
  rw [hL, hR]

/-- **`tStable` at a name (membership-map form).**  For `σ : 1 → [A]`, the membership map of
    the `A`-indexed name `σ ≫ curry (tStableBody t)` is the Heyting implication
    `(membershipMap σ) ⇒ (t ≫ membershipMap σ)` on `A` — i.e. `x ↦ (x∈σ) ⇒ (t(x)∈σ)`. -/
theorem membershipMap_tStable_name {A : 𝒞} (t : A ⟶ A) (σ : one ⟶ powObj A) :
    membershipMap (σ ≫ curry (tStableBody t))
      = pair (membershipMap σ) (t ≫ membershipMap σ) ≫ impΩ := by
  -- membershipMap G = ⟨id, term ≫ G⟩ ≫ eval; eval_curry_point collapses curry at point σ.
  show pair (Cat.id A) (term A ≫ (σ ≫ curry (tStableBody t))) ≫ eval_exp A (omega (𝒞 := 𝒞)) = _
  rw [show term A ≫ (σ ≫ curry (tStableBody t)) = (term A ≫ σ) ≫ curry (tStableBody t) from
        (Cat.assoc _ _ _).symm]
  rw [eval_curry_point (tStableBody t) (Cat.id A) (term A ≫ σ)]
  -- now ⟨id, term≫σ⟩ ≫ tStableBody t = ⟨x∈σ, t(x)∈σ⟩ ≫ impΩ.
  rw [tStableBody, ← Cat.assoc]
  congr 1
  apply pair_uniq
  · -- first component: ⟨id, term≫σ⟩ ≫ (⟨fst,snd⟩ ≫ eval) = membershipMap σ
    rw [Cat.assoc, fst_pair, ← Cat.assoc, membershipMap]
    congr 1
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, fst_pair]
    · rw [Cat.assoc, snd_pair, snd_pair]
  · -- second: ⟨id, term≫σ⟩ ≫ (⟨fst≫t,snd⟩ ≫ eval) = t ≫ membershipMap σ
    rw [Cat.assoc, snd_pair, ← Cat.assoc, membershipMap, ← Cat.assoc]
    congr 1
    -- both sides equal pair t (term A ≫ σ).
    have hL : pair (Cat.id A) (term A ≫ σ) ≫ pair (fst ≫ t) snd = pair t (term A ≫ σ) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.id_comp]
      · rw [Cat.assoc, snd_pair, snd_pair]
    have hR : t ≫ pair (Cat.id A) (term A ≫ σ) = pair t (term A ≫ σ) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, Cat.comp_id]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, term_uniq (t ≫ term A) (term A)]
    rw [hL, hR]

/-- **Heyting implication entire from `≤` (reusable).**  If `χS, χT : A → Ω` are the
    characteristic maps of subobjects `S, T` with `S ≤ T`, then `⟨χS, χT⟩ ≫ impΩ = ⊤∘!`,
    i.e. the comprehension `{x | χS(x) ⇒ χT(x)}` is the entire subobject.  Routes through
    `imp_adjunction` exactly like `bigInter_ge`/`allows_imageF`. -/
theorem impΩ_entire_of_le {A : 𝒞} (S T : Subobject 𝒞 A) (hle : S.le T) :
    pair (subChar S) (subChar T) ≫ impΩ
      = term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [pair_impΩ]
  rw [show pair (subChar S) (pair (subChar S) (subChar T) ≫ omegaMeet) ≫ heytingDoubleArrow
        = subChar (Sub.imp S T) from (classify_imp S T).symm]
  have hp : HasPullback S.arr (Subobject.entire A).arr := HasPullbacks.has _ _
  have hentireLe : (Subobject.entire A).le (Sub.imp S T) := by
    rw [imp_adjunction S T (Subobject.entire A) hp]
    obtain ⟨h₁, e₁⟩ := Sub.inter_le_left S (Subobject.entire A) hp
    obtain ⟨h₂, e₂⟩ := hle
    exact ⟨h₁ ≫ h₂, by rw [Cat.assoc, e₂, e₁]⟩
  have hcl := (le_iff_classify (Subobject.entire A) (Sub.imp S T)).mp hentireLe
  show subChar (Sub.imp S T) = term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
  rw [show (Subobject.entire A).arr ≫ subChar (Sub.imp S T) = subChar (Sub.imp S T)
        from Cat.id_comp _] at hcl
  rw [hcl]
  congr 1

/-- **`t`-stability of a subobject `B`, internalized.**  If `B ↣ A` is `t`-stable
    (`tS ≫ B.arr = B.arr ≫ t` for some `tS`), then `'B' ≫ tStable t = ⊤∘!`: the name
    of `B` passes the internal `t`-stability test `∀x. x∈B ⇒ t(x)∈B`. -/
theorem tStable_name_true {A : 𝒞} (t : A ⟶ A) (B : Subobject 𝒞 A)
    (tS : B.dom ⟶ B.dom) (htS : tS ≫ B.arr = B.arr ≫ t) :
    nameOf B.arr B.monic ≫ tStable t = term one ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [tStable, ← Cat.assoc]
  rw [forall_beta A (nameOf B.arr B.monic ≫ curry (tStableBody t))]
  -- Compare names via membershipMap (injective on names 1 → [A]).
  have hinj : ∀ (G H : one ⟶ powObj A), membershipMap G = membershipMap H → G = H :=
    fun G H hGH => by rw [← curry_fst_membershipMap G, ← curry_fst_membershipMap H, hGH]
  apply hinj
  rw [show term one ≫ topName A = topName A by
        rw [term_uniq (term one) (Cat.id one), Cat.id_comp]]
  rw [membershipMap_topName, classify_entire]
  rw [membershipMap_tStable_name, membershipMap_nameOf]
  -- Goal: ⟨χ_B, t ≫ χ_B⟩ ≫ impΩ = term A ≫ true.  Realize t ≫ χ_B as subChar (t# B).
  rw [show t ≫ HasSubobjectClassifier.classify B.arr B.monic
        = subChar (InverseImage t B) from (classify_InverseImage t B).symm]
  rw [show HasSubobjectClassifier.classify B.arr B.monic = subChar B from rfl]
  apply impΩ_entire_of_le B (InverseImage t B)
  -- B ≤ t# B: B.arr ≫ t = tS ≫ B.arr factors through B, so χ_{t# B}(B.arr) = ⊤.
  apply (le_iff_classify B (InverseImage t B)).2
  rw [classify_InverseImage t B, ← Cat.assoc]
  rw [show B.arr ≫ t = tS ≫ B.arr from htS.symm, Cat.assoc]
  rw [HasSubobjectClassifier.classify_sq B.arr B.monic, ← Cat.assoc,
    term_uniq (tS ≫ term B.dom) (term B.dom)]

/-- **`memAtPoint` at a name is true iff the point is allowed.**  `'B' ≫ memAtPoint a = ⊤∘!`
    exactly when `Allows B a` (i.e. `a` factors through `B`). -/
theorem memAtPoint_name_true_iff {A : 𝒞} (a : one ⟶ A) (B : Subobject 𝒞 A) :
    nameOf B.arr B.monic ≫ memAtPoint a = term one ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
      ↔ Allows B a := by
  rw [memAtPoint_at_name, membershipMap_nameOf]
  exact (allows_iff_classify B a).symm

/-- **§1.987 — `least_le`.**  For every `(a,t)`-closed `B`, the family-glb
    `bigInter (closedFamily a t)` lies below `B`.  The name `'B'` is a member of the
    closedness family (`closedChar` true at `'B'`), so `bigInter_le_named` applies. -/
theorem least_le_closed {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) (B : Subobject 𝒞 A)
    (hB : IsClosedSub B a t) : (bigInter (closedFamily a t)).le B := by
  obtain ⟨hAllows, tS, htS⟩ := hB
  refine bigInter_le_named (closedFamily a t) B ?_
  rw [membershipMap_closedFamily, closedChar]
  -- meet true iff both conjuncts true at k = 'B'.
  apply (meet_true_iff_and (memAtPoint a) (tStable t) (nameOf B.arr B.monic)).2
  exact ⟨(memAtPoint_name_true_iff a B).2 hAllows, tStable_name_true t B tS htS⟩

/-! ## §1.987  `least_isClosed` — the family-glb is itself `(a,t)`-closed -/

/-- **§1.987 — the family-glb ALLOWS `a`.**  `Allows (bigInter (closedFamily a t)) a`.
    Via `bigInter_ge`: the closedness family `F0 = {σ | closedChar}` lies below
    `Ga = {σ | a∈σ}` (since `closedChar`'s first conjunct IS `memAtPoint a`), so `a ∈ ⋂F`. -/
theorem least_allows {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) :
    Allows (bigInter (closedFamily a t)) a := by
  -- realize closedChar and memAtPoint a as subobjects F0, Ga of [A].
  obtain ⟨_, mF, hmF, hSF⟩ := classify_surjective (closedChar a t)
  obtain ⟨_, mG, hmG, hSG⟩ := classify_surjective (memAtPoint a)
  let F0 : Subobject 𝒞 (powObj A) := ⟨_, mF, hmF⟩
  let Ga : Subobject 𝒞 (powObj A) := ⟨_, mG, hmG⟩
  have hcF : subChar F0 = closedChar a t := hSF
  have hcG : subChar Ga = memAtPoint a := hSG
  refine bigInter_ge (closedFamily a t) a F0 Ga ?_ hcG ?_
  · rw [hcF, membershipMap_closedFamily]
  · -- F0 ≤ Ga: on F0's carrier, closedChar = ⊤, hence its memAtPoint conjunct = ⊤.
    apply (le_iff_classify F0 Ga).2
    rw [show HasSubobjectClassifier.classify Ga.arr Ga.monic = memAtPoint a from hcG]
    -- carrier F0.arr satisfies closedChar = meet(memAtPoint, tStable) = ⊤; project to memAtPoint.
    have hcar : F0.arr ≫ closedChar a t = term F0.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      rw [show closedChar a t = subChar F0 from hcF.symm]
      exact HasSubobjectClassifier.classify_sq F0.arr F0.monic
    rw [closedChar] at hcar
    exact ((meet_true_iff_and (memAtPoint a) (tStable t) F0.arr).1 hcar).1

/-! ## §1.987  `least_isClosed` — t-stability of the family-glb -/

/-- **Generalized `t`-stability.**  If a generalized name `k : K → [A]` passes `tStable t`
    (`k ≫ tStable t = ⊤`) and a generalized point `x : K → A` lies in it
    (`⟨x,k⟩ ≫ eval = ⊤`), then `t(x)` lies in it too (`⟨x≫t, k⟩ ≫ eval = ⊤`).

    This is ∀-elimination of `tStableBody` at `x` plus modus ponens (`impΩ_forward`),
    mirroring `imageF_carrier_in_mem`. -/
theorem tStable_gen {A K : 𝒞} (t : A ⟶ A) (k : K ⟶ powObj A) (x : K ⟶ A)
    (hk : k ≫ tStable t = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
    (hx : pair x k ≫ eval_exp A (omega (𝒞 := 𝒞)) = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    pair (x ≫ t) k ≫ eval_exp A (omega (𝒞 := 𝒞))
      = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  -- forall_beta: k ≫ curry(tStableBody) = term K ≫ topName A.
  rw [tStable, ← Cat.assoc] at hk
  have hentire : k ≫ curry (tStableBody t) = term K ≫ topName A :=
    (forall_beta A (k ≫ curry (tStableBody t))).mp hk
  -- forall_elim at x: ⟨x, k ≫ curry body⟩ ≫ eval = ⊤; eval_curry_point ⟹ ⟨x,k⟩ ≫ tStableBody = ⊤.
  have helim := forall_elim (k ≫ curry (tStableBody t)) hentire x
  rw [eval_curry_point (tStableBody t) x k] at helim
  -- ⟨x,k⟩ ≫ tStableBody = ⟨x∈k, t(x)∈k⟩ ≫ impΩ.
  rw [tStableBody, ← Cat.assoc] at helim
  -- the two impΩ components along id K.
  have hsplit : pair x k ≫ pair
        (pair fst snd ≫ eval_exp A (omega (𝒞 := 𝒞)))
        (pair (fst ≫ t) snd ≫ eval_exp A (omega (𝒞 := 𝒞)))
      = pair (pair x k ≫ eval_exp A (omega (𝒞 := 𝒞)))
          (pair (x ≫ t) k ≫ eval_exp A (omega (𝒞 := 𝒞))) := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc]
      congr 1
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, snd_pair]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc]
      congr 1
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair]
      · rw [Cat.assoc, snd_pair, snd_pair]
  rw [hsplit] at helim
  -- modus ponens: impΩ true along id K and x∈k true ⟹ t(x)∈k true.
  have := impΩ_forward _ _ (Cat.id K)
    (by rw [Cat.id_comp]; exact helim)
    (by rw [Cat.id_comp]; exact hx)
  rwa [Cat.id_comp] at this

/-- **A point of `⋂F` lies in every member (generalized).**  If `p : K → A` lies in `⋂F`
    (`p ≫ bigInterChar Fname = ⊤`) and `σ : K → [A]` is a member of `F`
    (`σ ≫ membershipMap Fname = ⊤`), then `p` lies in `σ`: `⟨σ,p⟩ ≫ (⟨snd,fst⟩ ≫ eval) = ⊤`.

    ∀-elimination of `bigInterBody` at the member `σ` (from `p ∈ ⋂F`) plus modus ponens; the
    lower-bound argument of `bigInter_le_named` at a generalized point. -/
theorem bigInter_point_in_member {A K : 𝒞} (Fname : one ⟶ powObj (powObj A))
    (p : K ⟶ A) (σ : K ⟶ powObj A)
    (hp : p ≫ bigInterChar Fname = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
    (hmem : σ ≫ membershipMap Fname = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    pair σ p ≫ (pair snd fst ≫ eval_exp A (omega (𝒞 := 𝒞)))
      = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  -- p ≫ bigInterChar = ⊤ ⟹ (forall_beta) p ≫ curry body = term K ≫ topName [A].
  rw [bigInterChar, ← Cat.assoc] at hp
  have hentire : p ≫ curry (bigInterBody Fname) = term K ≫ topName (powObj A) :=
    (forall_beta (powObj A) (p ≫ curry (bigInterBody Fname))).mp hp
  -- forall_elim at σ : K → [A]: ⟨σ, p ≫ curry body⟩ ≫ eval = ⊤; eval_curry_point ⟹ ⟨σ,p⟩ ≫ body = ⊤.
  have helim := forall_elim (p ≫ curry (bigInterBody Fname)) hentire σ
  rw [eval_curry_point (bigInterBody Fname) σ p] at helim
  rw [bigInterBody, ← Cat.assoc] at helim
  have hsplit : pair σ p ≫ pair (fst ≫ membershipMap Fname)
          (pair snd fst ≫ eval_exp A (omega (𝒞 := 𝒞)))
      = pair (σ ≫ membershipMap Fname)
          (pair σ p ≫ (pair snd fst ≫ eval_exp A (omega (𝒞 := 𝒞)))) := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair]
    · rw [Cat.assoc, snd_pair]
  rw [hsplit] at helim
  have := impΩ_forward _ _ (Cat.id K)
    (by rw [Cat.id_comp]; exact helim)
    (by rw [Cat.id_comp]; exact hmem)
  rwa [Cat.id_comp] at this

/-- **§1.987 — the family-glb is `t`-STABLE.**  `c ≫ t` factors through `⋂F` for `c = (⋂F).arr`,
    giving the restriction `tS : (⋂F).dom → (⋂F).dom` with `tS ≫ c = c ≫ t`.

    The carrier `c` lies in every closed member σ (`bigInter_point_in_member`), and each σ is
    `t`-stable (`tStable_gen`), so `t(c) ∈ σ` for every member σ; hence `t(c) ∈ ⋂F`.  The proof
    mirrors `allows_imageF`: reduce `Allows (⋂F) (c≫t)` to a prod-body equation over `prod [A] D`
    and discharge it by `imp_adjunction` (`impΩ_entire_of_le`-style) from `S_F ≤ S_In`. -/
theorem least_tStable {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) :
    ∃ tS : (bigInter (closedFamily a t)).dom ⟶ (bigInter (closedFamily a t)).dom,
      tS ≫ (bigInter (closedFamily a t)).arr = (bigInter (closedFamily a t)).arr ≫ t := by
  -- It suffices to show Allows (⋂F) (c ≫ t).
  have hAllows : Allows (bigInter (closedFamily a t))
      ((bigInter (closedFamily a t)).arr ≫ t) := by
    rw [allows_iff_classify]
    rw [show HasSubobjectClassifier.classify (bigInter (closedFamily a t)).arr
          (bigInter (closedFamily a t)).monic = bigInterChar (closedFamily a t) from
        classify_invImage_true (bigInterChar (closedFamily a t))]
    rw [bigInterChar, ← Cat.assoc]
    rw [forall_beta (powObj A)
      (((bigInter (closedFamily a t)).arr ≫ t) ≫ curry (bigInterBody (closedFamily a t)))]
    rw [curry_precomp]
    rw [show topName (powObj A)
          = curry (fst ≫ HasSubobjectClassifier.classify (Subobject.entire (powObj A)).arr
              (Subobject.entire (powObj A)).monic) from rfl]
    rw [curry_precomp]
    apply congrArg curry
    rw [← Cat.assoc, prodMap_fst, classify_entire, ← Cat.assoc,
      term_uniq (fst ≫ term (powObj A)) (term (prod (powObj A) (bigInter (closedFamily a t)).dom))]
    -- Goal: prodMap [A] D A (c≫t) ≫ bigInterBody F = term ≫ true.  Split into impΩ.
    let D := (bigInter (closedFamily a t)).dom
    let c := (bigInter (closedFamily a t)).arr
    let chiF : prod (powObj A) D ⟶ omega (𝒞 := 𝒞) :=
      fst ≫ membershipMap (closedFamily a t)
    let chiIn : prod (powObj A) D ⟶ omega (𝒞 := 𝒞) :=
      pair (snd ≫ c ≫ t) fst ≫ eval_exp A (omega (𝒞 := 𝒞))
    have hsplit : prodMap (powObj A) D A (c ≫ t) ≫ bigInterBody (closedFamily a t)
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
        · rw [Cat.assoc, fst_pair, prodMap_snd, ← Cat.assoc]
        · rw [Cat.assoc, snd_pair, prodMap_fst]
    rw [hsplit, pair_impΩ]
    -- Realize chiF, chiIn as subobjects S_F, S_In of prod [A] D.
    obtain ⟨_, mF, hmF, hSF⟩ := classify_surjective chiF
    obtain ⟨_, mIn, hmIn, hSIn⟩ := classify_surjective chiIn
    let S_F : Subobject 𝒞 (prod (powObj A) D) := ⟨_, mF, hmF⟩
    let S_In : Subobject 𝒞 (prod (powObj A) D) := ⟨_, mIn, hmIn⟩
    have hcF : subChar S_F = chiF := hSF
    have hcIn : subChar S_In = chiIn := hSIn
    rw [show pair chiF (pair chiF chiIn ≫ omegaMeet) ≫ heytingDoubleArrow
          = subChar (Sub.imp S_F S_In) by rw [classify_imp, impChar, hcF, hcIn]]
    have hp : HasPullback S_F.arr (Subobject.entire (prod (powObj A) D)).arr :=
      HasPullbacks.has _ _
    -- pointwise S_F ≤ S_In.
    have hSFle : S_F.le S_In := by
      apply (allows_iff_classify S_In S_F.arr).2
      rw [show HasSubobjectClassifier.classify S_In.arr S_In.monic = chiIn from hcIn]
      -- carrier k := S_F.arr; σ := k ≫ fst (a member), d := k ≫ snd.
      have hcarF : S_F.arr ≫ chiF = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
        rw [show chiF = HasSubobjectClassifier.classify S_F.arr S_F.monic from hcF.symm]
        exact HasSubobjectClassifier.classify_sq S_F.arr S_F.monic
      -- σ is a member of F: σ ≫ membershipMap = k ≫ chiF = ⊤.
      have hσmem : (S_F.arr ≫ fst) ≫ membershipMap (closedFamily a t)
          = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
        rw [Cat.assoc]; exact hcarF
      -- c(d) ∈ σ : bigInter_point_in_member at p = (k≫snd) ≫ c.
      have hpInter : ((S_F.arr ≫ snd) ≫ c) ≫ bigInterChar (closedFamily a t)
          = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
        rw [Cat.assoc, show c ≫ bigInterChar (closedFamily a t)
              = term D ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) from by
            have := bigInter_carrier_true (closedFamily a t); exact this]
        rw [← Cat.assoc, term_uniq ((S_F.arr ≫ snd) ≫ term D) (term S_F.dom)]
      have hcInσ := bigInter_point_in_member (closedFamily a t)
        ((S_F.arr ≫ snd) ≫ c) (S_F.arr ≫ fst) hpInter hσmem
      -- σ is t-stable: σ ≫ tStable t = ⊤  (second conjunct of closedChar at σ).
      have hσclosed : (S_F.arr ≫ fst) ≫ closedChar a t
          = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
        rw [show closedChar a t = membershipMap (closedFamily a t) from
              (membershipMap_closedFamily a t).symm]
        exact hσmem
      rw [closedChar] at hσclosed
      have hσtStable : (S_F.arr ≫ fst) ≫ tStable t
          = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) :=
        ((meet_true_iff_and (memAtPoint a) (tStable t) (S_F.arr ≫ fst)).1 hσclosed).2
      -- t(c(d)) ∈ σ via tStable_gen at x = (k≫snd)≫c.
      have hxIn : pair ((S_F.arr ≫ snd) ≫ c) (S_F.arr ≫ fst) ≫ eval_exp A (omega (𝒞 := 𝒞))
          = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
        -- hcInσ : pair σ p ≫ (pair snd fst ≫ eval) = ⊤; swap to pair p σ ≫ eval.
        rw [← hcInσ, ← Cat.assoc]
        congr 1
        symm
        apply pair_uniq
        · rw [Cat.assoc, fst_pair, snd_pair]
        · rw [Cat.assoc, snd_pair, fst_pair]
      have htcIn := tStable_gen t (S_F.arr ≫ fst) ((S_F.arr ≫ snd) ≫ c) hσtStable hxIn
      -- Conclude S_F.arr ≫ chiIn = ⊤ by matching htcIn's first component up to assoc.
      have hchiIn : S_F.arr ≫ chiIn
          = pair (((S_F.arr ≫ snd) ≫ c) ≫ t) (S_F.arr ≫ fst) ≫ eval_exp A (omega (𝒞 := 𝒞)) := by
        show S_F.arr ≫ (pair (snd ≫ c ≫ t) fst ≫ eval_exp A (omega (𝒞 := 𝒞))) = _
        rw [← Cat.assoc]
        congr 1
        apply pair_uniq
        · rw [Cat.assoc, fst_pair]
          rw [show snd ≫ c ≫ t = (snd ≫ c) ≫ t from (Cat.assoc _ _ _).symm]
          rw [show ((S_F.arr ≫ snd) ≫ c) ≫ t = S_F.arr ≫ ((snd ≫ c) ≫ t) from by
            rw [Cat.assoc, Cat.assoc, Cat.assoc]]
        · rw [Cat.assoc, snd_pair]
      show S_F.arr ≫ chiIn = _
      rw [hchiIn]
      exact htcIn
    have hentireLe : (Subobject.entire (prod (powObj A) D)).le (Sub.imp S_F S_In) := by
      rw [imp_adjunction S_F S_In (Subobject.entire (prod (powObj A) D)) hp]
      obtain ⟨h₁, e₁⟩ := Sub.inter_le_left S_F (Subobject.entire (prod (powObj A) D)) hp
      obtain ⟨h₂, e₂⟩ := hSFle
      exact ⟨h₁ ≫ h₂, by rw [Cat.assoc, e₂, e₁]⟩
    have hcl := (le_iff_classify (Subobject.entire (prod (powObj A) D))
      (Sub.imp S_F S_In)).mp hentireLe
    show subChar (Sub.imp S_F S_In) = term (prod (powObj A) D) ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
    rw [show (Subobject.entire (prod (powObj A) D)).arr ≫ subChar (Sub.imp S_F S_In)
          = subChar (Sub.imp S_F S_In) from Cat.id_comp _] at hcl
    rw [hcl]
    congr 1
  -- Unfold Allows to get the restriction tS.
  obtain ⟨u, hu⟩ := hAllows
  exact ⟨u, hu⟩

/-- **§1.987 — the family-glb is `(a,t)`-closed.**  Bundles `least_allows` (allows `a`) and
    `least_tStable` (`t`-stable). -/
theorem least_isClosed_closed {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) :
    IsClosedSub (bigInter (closedFamily a t)) a t :=
  ⟨least_allows a t, least_tStable a t⟩

/-- **§1.987 — every topos HAS a LEAST `(a,t)`-closed subobject.**  Constructed Sorry-free as
    the internal-∀ family-glb `bigInter (closedFamily a t)` of the closedness comprehension
    `{σ : [A] | (a∈σ) ∧ (∀x. x∈σ ⇒ t(x)∈σ)}`.  This discharges, for every topos, the
    `HasLeastClosedSubobject` hypothesis that `Freyd/InternalForall.lean` relocated — unblocking
    S1_97's `least_peano_subobject`. -/
noncomputable instance toposHasLeastClosedSubobject : HasLeastClosedSubobject 𝒞 where
  least a t := bigInter (closedFamily a t)
  least_isClosed a t := least_isClosed_closed a t
  least_le a t B hB := least_le_closed a t B hB

/-! ## §1.988  PARAMETRISED least `(a, r∘proj)`-closed subobject (for `1 + A×(−)`)

  The endo development above closes a subobject `σ ⊆ [M]` under a SINGLE endo `t : M → M`.
  Freyd's free-A-action Peano property (§1.98(13)) needs closure under an ACTION
  `act : A × M → M` — equivalently, under the GENERALISED "endo" given by two maps out of a
  PARAMETER object `P`: a `proj : P → M` (the membership probe) and an `r : P → M` (the result).
  `σ` is `(r,proj)`-stable when `∀p:P. (proj(p)∈σ) ⇒ (r(p)∈σ)`.  Taking `P := A×M`,
  `proj := snd`, `r := act` recovers free-A-action closure; `P=M, proj=id, r=t` recovers the endo
  case.  We rebuild `tStable`/`closedChar`/`least`'s STABILITY half generalised over `(P,proj,r)`;
  the ALLOWS half and `least_le`/`bigInter_*` are object-only and reused verbatim. -/

/-- Generalised stability body `prod P [M] → Ω`, `(p,σ) ↦ (proj(p)∈σ) ⇒ (r(p)∈σ)`. -/
noncomputable def genStableBody {M P : 𝒞} (r proj : P ⟶ M) :
    prod P (powObj M) ⟶ omega (𝒞 := 𝒞) :=
  pair
    (pair (fst ≫ proj) snd ≫ eval_exp M (omega (𝒞 := 𝒞)))
    (pair (fst ≫ r) snd ≫ eval_exp M (omega (𝒞 := 𝒞)))
  ≫ impΩ

/-- Generalised stability test `genStable r proj : [M] → Ω`,
    `σ ↦ ∀p:P. proj(p)∈σ ⇒ r(p)∈σ`. -/
noncomputable def genStable {M P : 𝒞} (r proj : P ⟶ M) : powObj M ⟶ omega (𝒞 := 𝒞) :=
  curry (genStableBody r proj) ≫ forallC P

/-- Membership-map of a `genStable` name (mirrors `membershipMap_tStable_name`). -/
theorem membershipMap_genStable_name {M P : 𝒞} (r proj : P ⟶ M) (σ : one ⟶ powObj M) :
    membershipMap (σ ≫ curry (genStableBody r proj))
      = pair (proj ≫ membershipMap σ) (r ≫ membershipMap σ) ≫ impΩ := by
  show pair (Cat.id P) (term P ≫ (σ ≫ curry (genStableBody r proj)))
      ≫ eval_exp P (omega (𝒞 := 𝒞)) = _
  rw [show term P ≫ (σ ≫ curry (genStableBody r proj))
        = (term P ≫ σ) ≫ curry (genStableBody r proj) from (Cat.assoc _ _ _).symm]
  rw [eval_curry_point (genStableBody r proj) (Cat.id P) (term P ≫ σ)]
  rw [genStableBody, ← Cat.assoc]
  congr 1
  apply pair_uniq
  · -- first: ⟨id, term≫σ⟩ ≫ (⟨fst≫proj,snd⟩ ≫ eval) = proj ≫ membershipMap σ
    rw [Cat.assoc, fst_pair, ← Cat.assoc, membershipMap, ← Cat.assoc]
    congr 1
    have hL : pair (Cat.id P) (term P ≫ σ) ≫ pair (fst ≫ proj) snd
        = pair proj (term P ≫ σ) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.id_comp]
      · rw [Cat.assoc, snd_pair, snd_pair]
    have hR : proj ≫ pair (Cat.id M) (term M ≫ σ) = pair proj (term P ≫ σ) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, Cat.comp_id]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, term_uniq (proj ≫ term M) (term P)]
    rw [hL, hR]
  · -- second: ⟨id, term≫σ⟩ ≫ (⟨fst≫r,snd⟩ ≫ eval) = r ≫ membershipMap σ
    rw [Cat.assoc, snd_pair, ← Cat.assoc, membershipMap, ← Cat.assoc]
    congr 1
    have hL : pair (Cat.id P) (term P ≫ σ) ≫ pair (fst ≫ r) snd = pair r (term P ≫ σ) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.id_comp]
      · rw [Cat.assoc, snd_pair, snd_pair]
    have hR : r ≫ pair (Cat.id M) (term M ≫ σ) = pair r (term P ≫ σ) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, Cat.comp_id]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, term_uniq (r ≫ term M) (term P)]
    rw [hL, hR]

/-- A `(r,proj)`-stable subobject `B ↣ M` passes `genStable`.  `B` is `(r,proj)`-STABLE exactly
    when its `proj`-preimage lies in its `r`-preimage (`proj(p)∈B ⟹ r(p)∈B`); then
    `'B' ≫ genStable r proj = ⊤`.  Mirrors `tStable_name_true` (the endo case `proj=id,r=t`,
    where `B ≤ InverseImage t B` is exactly that). -/
theorem genStable_name_true {M P : 𝒞} (r proj : P ⟶ M) (B : Subobject 𝒞 M)
    (hstab : (InverseImage proj B).le (InverseImage r B)) :
    nameOf B.arr B.monic ≫ genStable r proj
      = term one ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [genStable, ← Cat.assoc]
  rw [forall_beta P (nameOf B.arr B.monic ≫ curry (genStableBody r proj))]
  have hinj : ∀ (G H : one ⟶ powObj P), membershipMap G = membershipMap H → G = H :=
    fun G H hGH => by rw [← curry_fst_membershipMap G, ← curry_fst_membershipMap H, hGH]
  apply hinj
  rw [show term one ≫ topName P = topName P by
        rw [term_uniq (term one) (Cat.id one), Cat.id_comp]]
  rw [membershipMap_topName, classify_entire]
  rw [membershipMap_genStable_name, membershipMap_nameOf]
  -- Goal: ⟨proj ≫ χ_B, r ≫ χ_B⟩ ≫ impΩ = ⊤.  Realize proj ≫ χ_B = χ_{proj#B}, r ≫ χ_B = χ_{r#B}.
  rw [show proj ≫ HasSubobjectClassifier.classify B.arr B.monic
        = subChar (InverseImage proj B) from (classify_InverseImage proj B).symm]
  rw [show r ≫ HasSubobjectClassifier.classify B.arr B.monic
        = subChar (InverseImage r B) from (classify_InverseImage r B).symm]
  exact impΩ_entire_of_le (InverseImage proj B) (InverseImage r B) hstab

/-- Generalised `genStable_gen` (∀-elimination + MP).  If `k : K → [M]` passes `genStable r proj`
    and a generalised point `proj(p) : K → M` lies in `k` (via `p : K → P`), then `r(p)` lies in
    `k` too.  Mirrors `tStable_gen`. -/
theorem genStable_gen {M P K : 𝒞} (r proj : P ⟶ M) (k : K ⟶ powObj M) (p : K ⟶ P)
    (hk : k ≫ genStable r proj = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
    (hx : pair (p ≫ proj) k ≫ eval_exp M (omega (𝒞 := 𝒞))
        = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    pair (p ≫ r) k ≫ eval_exp M (omega (𝒞 := 𝒞))
      = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [genStable, ← Cat.assoc] at hk
  have hentire : k ≫ curry (genStableBody r proj) = term K ≫ topName P :=
    (forall_beta P (k ≫ curry (genStableBody r proj))).mp hk
  have helim := forall_elim (k ≫ curry (genStableBody r proj)) hentire p
  rw [eval_curry_point (genStableBody r proj) p k] at helim
  rw [genStableBody, ← Cat.assoc] at helim
  have hsplit : pair p k ≫ pair
        (pair (fst ≫ proj) snd ≫ eval_exp M (omega (𝒞 := 𝒞)))
        (pair (fst ≫ r) snd ≫ eval_exp M (omega (𝒞 := 𝒞)))
      = pair (pair (p ≫ proj) k ≫ eval_exp M (omega (𝒞 := 𝒞)))
          (pair (p ≫ r) k ≫ eval_exp M (omega (𝒞 := 𝒞))) := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc]
      congr 1
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair]
      · rw [Cat.assoc, snd_pair, snd_pair]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc]
      congr 1
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair]
      · rw [Cat.assoc, snd_pair, snd_pair]
  rw [hsplit] at helim
  have := impΩ_forward _ _ (Cat.id K)
    (by rw [Cat.id_comp]; exact helim)
    (by rw [Cat.id_comp]; exact hx)
  rwa [Cat.id_comp] at this

/-! ## §1.988  The parametrised closedness comprehension and its least subobject -/

/-- Parametrised closedness characteristic `actClosedChar a r proj : [M] → Ω`,
    `σ ↦ (a∈σ) ∧ ∀p:P. proj(p)∈σ ⇒ r(p)∈σ`. -/
noncomputable def actClosedChar {M P : 𝒞} (a : one ⟶ M) (r proj : P ⟶ M) :
    powObj M ⟶ omega (𝒞 := 𝒞) :=
  pair (memAtPoint a) (genStable r proj) ≫ omegaMeet

/-- Family name of `{σ : [M] | actClosedChar a r proj}`. -/
noncomputable def actClosedFamily {M P : 𝒞} (a : one ⟶ M) (r proj : P ⟶ M) :
    one ⟶ powObj (powObj M) :=
  curry (fst ≫ actClosedChar a r proj)

theorem membershipMap_actClosedFamily {M P : 𝒞} (a : one ⟶ M) (r proj : P ⟶ M) :
    membershipMap (actClosedFamily a r proj) = actClosedChar a r proj := by
  rw [actClosedFamily, membershipMap_curry_fst]

/-- The parametrised least `(a, r, proj)`-closed subobject `actLeast a r proj ⊆ M`. -/
noncomputable def actLeast {M P : 𝒞} (a : one ⟶ M) (r proj : P ⟶ M) : Subobject 𝒞 M :=
  bigInter (actClosedFamily a r proj)

/-- **ALLOWS `a`** (mirrors `least_allows`). -/
theorem actLeast_allows {M P : 𝒞} (a : one ⟶ M) (r proj : P ⟶ M) :
    Allows (actLeast a r proj) a := by
  obtain ⟨_, mF, hmF, hSF⟩ := classify_surjective (actClosedChar a r proj)
  obtain ⟨_, mG, hmG, hSG⟩ := classify_surjective (memAtPoint a)
  let F0 : Subobject 𝒞 (powObj M) := ⟨_, mF, hmF⟩
  let Ga : Subobject 𝒞 (powObj M) := ⟨_, mG, hmG⟩
  have hcF : subChar F0 = actClosedChar a r proj := hSF
  have hcG : subChar Ga = memAtPoint a := hSG
  refine bigInter_ge (actClosedFamily a r proj) a F0 Ga ?_ hcG ?_
  · rw [hcF, membershipMap_actClosedFamily]
  · apply (le_iff_classify F0 Ga).2
    rw [show HasSubobjectClassifier.classify Ga.arr Ga.monic = memAtPoint a from hcG]
    have hcar : F0.arr ≫ actClosedChar a r proj
        = term F0.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      rw [show actClosedChar a r proj = subChar F0 from hcF.symm]
      exact HasSubobjectClassifier.classify_sq F0.arr F0.monic
    rw [actClosedChar] at hcar
    exact ((meet_true_iff_and (memAtPoint a) (genStable r proj) F0.arr).1 hcar).1

/-- **`actLeast ≤ B`** for every `(a, r, proj)`-closed `B` (mirrors `least_le_closed`). -/
theorem actLeast_le {M P : 𝒞} (a : one ⟶ M) (r proj : P ⟶ M) (B : Subobject 𝒞 M)
    (hAllows : Allows B a) (hstab : (InverseImage proj B).le (InverseImage r B)) :
    (actLeast a r proj).le B := by
  refine bigInter_le_named (actClosedFamily a r proj) B ?_
  rw [membershipMap_actClosedFamily, actClosedChar]
  apply (meet_true_iff_and (memAtPoint a) (genStable r proj) (nameOf B.arr B.monic)).2
  exact ⟨(memAtPoint_name_true_iff a B).2 hAllows, genStable_name_true r proj B hstab⟩

/-- **`actLeast` is `(r,proj)`-STABLE** (mirrors `least_tStable`).  Its `proj`-preimage lies in its
    `r`-preimage: `proj(p) ∈ actLeast ⟹ r(p) ∈ actLeast`. -/
theorem actLeast_stable {M P : 𝒞} (a : one ⟶ M) (r proj : P ⟶ M) :
    (InverseImage proj (actLeast a r proj)).le (InverseImage r (actLeast a r proj)) := by
  let Fname : one ⟶ powObj (powObj M) := actClosedFamily a r proj
  show (InverseImage proj (bigInter Fname)).le (InverseImage r (bigInter Fname))
  let L : Subobject 𝒞 M := bigInter Fname
  -- `subChar L = bigInterChar Fname` (L is a pullback of `true` along `bigInterChar`).
  have hsubL : subChar L = bigInterChar Fname := classify_invImage_true (bigInterChar Fname)
  -- Reduce `proj#L ≤ r#L` to `(proj#L).arr ≫ r ≫ χ_L = ⊤`, i.e. `r(probe) ∈ ⋂F`.
  apply (le_iff_classify (InverseImage proj L) (InverseImage r L)).2
  rw [classify_InverseImage r L]
  let q : (InverseImage proj L).dom ⟶ P := (InverseImage proj L).arr
  -- `q ≫ proj ∈ ⋂F`:  classify(proj#L) carrier = ⊤  ⟹  (q ≫ proj) ≫ bigInterChar = ⊤.
  have hprobeIn : (q ≫ proj) ≫ bigInterChar Fname
      = term (InverseImage proj L).dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    have hcar := HasSubobjectClassifier.classify_sq
      (InverseImage proj L).arr (InverseImage proj L).monic
    -- classify (proj#L).arr = proj ≫ classify L.arr, and classify L.arr = bigInterChar Fname.
    rw [classify_InverseImage proj L] at hcar
    rw [show (classify L.arr (bigInter Fname).monic : M ⟶ _) = bigInterChar Fname from hsubL] at hcar
    rw [← Cat.assoc] at hcar
    exact hcar
  -- Goal: `q ≫ r ≫ χ_L = ⊤`.  Unfold χ_L = bigInterChar Fname; forall over members via S_F ≤ S_In.
  show q ≫ r ≫ subChar L = term (InverseImage proj L).dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
  rw [hsubL, bigInterChar, ← Cat.assoc, ← Cat.assoc]
  rw [forall_beta (powObj M) ((q ≫ r) ≫ curry (bigInterBody Fname))]
  rw [curry_precomp]
  rw [show topName (powObj M)
        = curry (fst ≫ HasSubobjectClassifier.classify (Subobject.entire (powObj M)).arr
            (Subobject.entire (powObj M)).monic) from rfl]
  rw [curry_precomp]
  apply congrArg curry
  rw [← Cat.assoc, prodMap_fst, classify_entire, ← Cat.assoc,
    term_uniq (fst ≫ term (powObj M)) (term (prod (powObj M) (InverseImage proj L).dom))]
  -- Goal: prodMap [M] D' M (q≫r) ≫ bigInterBody F = term ≫ true.  Split into impΩ.
  let D' := (InverseImage proj L).dom
  let chiF : prod (powObj M) D' ⟶ omega (𝒞 := 𝒞) :=
    fst ≫ membershipMap Fname
  let chiIn : prod (powObj M) D' ⟶ omega (𝒞 := 𝒞) :=
    pair (snd ≫ q ≫ r) fst ≫ eval_exp M (omega (𝒞 := 𝒞))
  have hsplit : prodMap (powObj M) D' M (q ≫ r) ≫ bigInterBody Fname
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
      · rw [Cat.assoc, fst_pair, prodMap_snd, ← Cat.assoc]
      · rw [Cat.assoc, snd_pair, prodMap_fst]
  rw [hsplit, pair_impΩ]
  obtain ⟨_, mF, hmF, hSF⟩ := classify_surjective chiF
  obtain ⟨_, mIn, hmIn, hSIn⟩ := classify_surjective chiIn
  let S_F : Subobject 𝒞 (prod (powObj M) D') := ⟨_, mF, hmF⟩
  let S_In : Subobject 𝒞 (prod (powObj M) D') := ⟨_, mIn, hmIn⟩
  have hcF : subChar S_F = chiF := hSF
  have hcIn : subChar S_In = chiIn := hSIn
  rw [show pair chiF (pair chiF chiIn ≫ omegaMeet) ≫ heytingDoubleArrow
        = subChar (Sub.imp S_F S_In) by rw [classify_imp, impChar, hcF, hcIn]]
  have hp : HasPullback S_F.arr (Subobject.entire (prod (powObj M) D')).arr :=
    HasPullbacks.has _ _
  -- pointwise S_F ≤ S_In: a member σ (= k≫fst) containing the probe `proj(q(d))` also contains `r(q(d))`.
  have hSFle : S_F.le S_In := by
    apply (allows_iff_classify S_In S_F.arr).2
    rw [show HasSubobjectClassifier.classify S_In.arr S_In.monic = chiIn from hcIn]
    have hcarF : S_F.arr ≫ chiF = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      rw [show chiF = HasSubobjectClassifier.classify S_F.arr S_F.monic from hcF.symm]
      exact HasSubobjectClassifier.classify_sq S_F.arr S_F.monic
    -- σ := (k≫fst) is a member of F.
    have hσmem : (S_F.arr ≫ fst) ≫ membershipMap Fname
        = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      rw [Cat.assoc]; exact hcarF
    -- σ is `(r,proj)`-stable: σ ≫ genStable = ⊤ (second conjunct of actClosedChar at σ).
    have hσclosed : (S_F.arr ≫ fst) ≫ actClosedChar a r proj
        = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      rw [show actClosedChar a r proj = membershipMap Fname from
            (membershipMap_actClosedFamily a r proj).symm]
      exact hσmem
    rw [actClosedChar] at hσclosed
    have hσgen : (S_F.arr ≫ fst) ≫ genStable r proj
        = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) :=
      ((meet_true_iff_and (memAtPoint a) (genStable r proj) (S_F.arr ≫ fst)).1 hσclosed).2
    -- the probe `proj(q(d)) ∈ σ`:  `bigInter_point_in_member` at `pt := (k≫snd)≫q`.
    have hpInter : (((S_F.arr ≫ snd) ≫ q) ≫ proj) ≫ bigInterChar Fname
        = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      rw [Cat.assoc, Cat.assoc, ← Cat.assoc q proj (bigInterChar Fname), hprobeIn, ← Cat.assoc,
        term_uniq ((S_F.arr ≫ snd) ≫ term D') (term S_F.dom)]
    have hprobeInσ := bigInter_point_in_member Fname
      (((S_F.arr ≫ snd) ≫ q) ≫ proj) (S_F.arr ≫ fst) hpInter hσmem
    -- pivot to `eval` form: `proj(q(d)) ∈ σ`.
    have hxIn : pair (((S_F.arr ≫ snd) ≫ q) ≫ proj) (S_F.arr ≫ fst) ≫ eval_exp M (omega (𝒞 := 𝒞))
        = term S_F.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      rw [← hprobeInσ, ← Cat.assoc]
      congr 1
      symm
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, snd_pair]
      · rw [Cat.assoc, snd_pair, fst_pair]
    -- genStable_gen at the point `pt := (k≫snd)≫q : S_F.dom → P`.
    have hrIn := genStable_gen r proj (S_F.arr ≫ fst) ((S_F.arr ≫ snd) ≫ q)
      hσgen hxIn
    -- Conclude S_F.arr ≫ chiIn = ⊤ (= `r(q(d)) ∈ σ`).
    have hchiIn : S_F.arr ≫ chiIn
        = pair (((S_F.arr ≫ snd) ≫ q) ≫ r) (S_F.arr ≫ fst) ≫ eval_exp M (omega (𝒞 := 𝒞)) := by
      show S_F.arr ≫ (pair (snd ≫ q ≫ r) fst ≫ eval_exp M (omega (𝒞 := 𝒞))) = _
      rw [← Cat.assoc]
      congr 1
      apply pair_uniq
      · rw [Cat.assoc, fst_pair]
        rw [show snd ≫ q ≫ r = (snd ≫ q) ≫ r from (Cat.assoc _ _ _).symm]
        rw [show ((S_F.arr ≫ snd) ≫ q) ≫ r = S_F.arr ≫ ((snd ≫ q) ≫ r) from by
          rw [Cat.assoc, Cat.assoc, Cat.assoc]]
      · rw [Cat.assoc, snd_pair]
    show S_F.arr ≫ chiIn = _
    rw [hchiIn]
    exact hrIn
  have hentireLe : (Subobject.entire (prod (powObj M) D')).le (Sub.imp S_F S_In) := by
    rw [imp_adjunction S_F S_In (Subobject.entire (prod (powObj M) D')) hp]
    obtain ⟨h₁, e₁⟩ := Sub.inter_le_left S_F (Subobject.entire (prod (powObj M) D')) hp
    obtain ⟨h₂, e₂⟩ := hSFle
    exact ⟨h₁ ≫ h₂, by rw [Cat.assoc, e₂, e₁]⟩
  have hcl := (le_iff_classify (Subobject.entire (prod (powObj M) D'))
    (Sub.imp S_F S_In)).mp hentireLe
  show subChar (Sub.imp S_F S_In) = term (prod (powObj M) D') ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
  rw [show (Subobject.entire (prod (powObj M) D')).arr ≫ subChar (Sub.imp S_F S_In)
        = subChar (Sub.imp S_F S_In) from Cat.id_comp _] at hcl
  rw [hcl]
  congr 1

end Freyd
