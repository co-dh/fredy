/-
  Freyd & Scedrov, *Categories and Allegories* — the right adjoint to inverse image
  (`∀_f : Sub(A) → Sub(B)`, the internal universal quantifier along `f : A → B`) in a topos,
  and the resulting FRAME LAW that inverse image preserves binary unions:

      f#(S ∪ T)  ≤  f#S ∪ f#T.

  Mathematically `∀_f S = { b : B | ∀ a : A. (f a = b) ⇒ (a ∈ S) }`.  As a characteristic
  map `B → Ω` this is the fibered-∀ over `A` of the body `(a,b) ↦ (f a = b) ⇒ (a ∈ S)`,
  built from `forallC A` (internal ∀), the diagonal classifier `χ_Δ` (internal equality),
  and `impΩ` (internal implication) — all already in `InternalForallTopos`.

  The adjunction `f# ⊣ ∀_f` is proven on subobjects: `f# T ≤ S  ↔  T ≤ ∀_f S`.  A left
  adjoint (here `f#`) preserves joins, which yields the frame law `≤` direction directly.
-/

import Freyd.S1_94_InternalForallTopos
import Freyd.S1_45
import Freyd.S1_60
import Freyd.S1_95_ToposColimits

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## The internal equality predicate `eqChar : B × B → Ω`. -/

/-- Internal equality on `B`: the classifier of the diagonal `Δ : B ↣ B × B`.
    `⟨a,b⟩ ≫ eqChar B = ⊤∘! ↔ a = b` (`diag_classify_iff`). -/
noncomputable def eqChar (B : 𝒞) : prod B B ⟶ omega (𝒞 := 𝒞) :=
  HasSubobjectClassifier.classify (diag B) (diag_mono B)

/-! ## The `∀_f` body, characteristic map, and subobject. -/

/-- The body `(a,b) ↦ (f a = b) ⇒ (a ∈ S)` as a map `A × B → Ω`. -/
noncomputable def forallBody {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) :
    prod A B ⟶ omega (𝒞 := 𝒞) :=
  pair (pair (fst ≫ f) snd ≫ eqChar B) (fst ≫ subChar S) ≫ impΩ

/-- The characteristic map `B → Ω` of `∀_f S`: curry the body in the `A`-slot, then
    universally quantify over `a : A` with `forallC A`. -/
noncomputable def forallChar {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) : B ⟶ omega (𝒞 := 𝒞) :=
  curry (forallBody f S) ≫ forallC A

/-- **`∀_f S` — the internal universal image of `S` along `f`.**  Pullback of `true` along
    `forallChar f S` (so it is classified by `forallChar f S`). -/
noncomputable def forallAlong {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) : Subobject 𝒞 B :=
  InverseImage (forallChar f S) ⟨one, true (𝒞 := 𝒞), HasSubobjectClassifier.true_monic⟩

theorem classify_forallAlong {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) :
    HasSubobjectClassifier.classify (forallAlong f S).arr (forallAlong f S).monic
      = forallChar f S :=
  classify_invImage_true (forallChar f S)

/-- `Allows (∀_f S) b ↔ b ≫ forallChar f S = ⊤∘!`. -/
theorem allows_forallAlong_iff {A B W : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) (b : W ⟶ B) :
    Allows (forallAlong f S) b
      ↔ b ≫ forallChar f S = term W ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [allows_iff_classify (forallAlong f S) b, classify_forallAlong]

/-! ## The adjunction `f# ⊣ ∀_f`.

  `f# T ≤ S ↔ T ≤ ∀_f S`.  Both directions reduce, via `allows_iff_classify`, `forall_beta`,
  `forall_elim`, `impΩ_forward`, and `diag_classify_iff`, to the semantic fact
  `(∀ a. f a = b → a ∈ S)` along generalized points. -/

/-- The body unfolds at a generalized point `⟨a,b⟩ = pair u v` to
    `⟨(f∘u = v), u ∈ S⟩ ≫ impΩ`. -/
theorem forallBody_at {A B W : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) (u : W ⟶ A) (v : W ⟶ B) :
    pair u v ≫ forallBody f S
      = pair (pair (u ≫ f) v ≫ eqChar B) (u ≫ subChar S) ≫ impΩ := by
  rw [forallBody, ← Cat.assoc]
  congr 1
  apply pair_uniq
  · rw [Cat.assoc, fst_pair, ← Cat.assoc]
    congr 1
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair]
    · rw [Cat.assoc, snd_pair, snd_pair]
  · rw [Cat.assoc, snd_pair, ← Cat.assoc, fst_pair]

/-- The carrier `c := (f#T).arr` of the inverse image satisfies the pullback square
    `c ≫ f = hp.cone.π₂ ≫ T.arr`. -/
theorem invImg_sq {A B : 𝒞} (f : A ⟶ B) (T : Subobject 𝒞 B) (hp : HasPullback f T.arr) :
    (invImg f T hp).arr ≫ f = hp.cone.π₂ ≫ T.arr :=
  hp.cone.w

theorem forallAlong_adjunction {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) (T : Subobject 𝒞 B)
    (hp : HasPullback f T.arr) :
    (invImg f T hp).le S ↔ T.le (forallAlong f S) := by
  constructor
  · -- ⇒ : f#T ≤ S  ⟹  T ≤ ∀_f S.
    -- Want T.arr ≫ forallChar f S = ⊤, i.e. (by forall_beta backwards)
    --   T.arr ≫ curry (forallBody f S) = term ≫ topName A.
    -- By Ω-extensionality / generalized points: for every k : W → A × T.dom-fiber, the
    -- body (a,b)=(k, b=T.arr·) is ⊤.  The genuine content is "∀-introduction": the
    -- comprehension {(a,b) | (f a = b) ⇒ (a ∈ S)} restricted along T.arr is entire,
    -- because (f a = T.arr·) forces a to factor through f#T (pullback UMP), hence a ∈ S
    -- (hle : f#T ≤ S).  Mirror `InternalForallTopos.bigInter_ge` (imp_adjunction route).
    intro hle
    -- Reduce to: T.arr ≫ curry (forallBody f S) = term T.dom ≫ topName A   (forall_beta).
    apply (le_iff_classify T (forallAlong f S)).2
    rw [classify_forallAlong, forallChar, ← Cat.assoc, forall_beta]
    -- Push T.arr inside the curries on both sides (curry_precomp); reduce to a prod-body equation.
    rw [curry_precomp]
    rw [show topName A
          = curry (fst ≫ HasSubobjectClassifier.classify (Subobject.entire A).arr
              (Subobject.entire A).monic) from rfl]
    rw [curry_precomp]
    apply congrArg curry
    -- RHS = ⊤∘! :  prodMap … ≫ fst = fst, classify(entire) = term ≫ true.
    rw [← Cat.assoc, prodMap_fst, classify_entire, ← Cat.assoc,
      term_uniq (fst ≫ term A) (term (prod A T.dom))]
    -- Goal: prodMap A T.dom B T.arr ≫ forallBody f S = term ≫ true, i.e. the Heyting
    -- implication (S_eq ⇒ S_S) over prod A T.dom is entire, via imp_adjunction.
    -- The two component characteristic maps on P = prod A T.dom.
    -- chiEq = (f a = T.arr·b),  chiS = (a ∈ S).
    let chiEq : prod A T.dom ⟶ omega (𝒞 := 𝒞) :=
      pair (fst ≫ f) (snd ≫ T.arr) ≫ eqChar B
    let chiS : prod A T.dom ⟶ omega (𝒞 := 𝒞) := fst ≫ subChar S
    -- LHS = ⟨chiEq, chiS⟩ ≫ impΩ.
    have hsplit : prodMap A T.dom B T.arr ≫ forallBody f S
        = pair chiEq chiS ≫ impΩ := by
      rw [forallBody, ← Cat.assoc]
      congr 1
      apply pair_uniq
      · show _ = chiEq
        rw [Cat.assoc, fst_pair, ← Cat.assoc]
        congr 1
        apply pair_uniq
        · rw [Cat.assoc, fst_pair, ← Cat.assoc, prodMap_fst]
        · rw [Cat.assoc, snd_pair, prodMap_snd]
      · show _ = chiS
        rw [Cat.assoc, snd_pair, ← Cat.assoc, prodMap_fst]
    rw [hsplit, pair_impΩ]
    -- Realise chiEq, chiS as subobjects S_eq, S_S of P.
    obtain ⟨_, mEq, hmEq, hSEq⟩ := classify_surjective chiEq
    obtain ⟨_, mS, hmS, hSS⟩ := classify_surjective chiS
    let S_eq : Subobject 𝒞 (prod A T.dom) := ⟨_, mEq, hmEq⟩
    let S_S : Subobject 𝒞 (prod A T.dom) := ⟨_, mS, hmS⟩
    have hcEq : subChar S_eq = chiEq := hSEq
    have hcS : subChar S_S = chiS := hSS
    -- LHS = impChar S_eq S_S = subChar (Sub.imp S_eq S_S).
    rw [show pair chiEq (pair chiEq chiS ≫ omegaMeet) ≫ heytingDoubleArrow
          = subChar (Sub.imp S_eq S_S) by rw [classify_imp, impChar, hcEq, hcS]]
    -- Goal: (S_eq ⇒ S_S) is entire.  Via imp_adjunction this is S_eq ≤ S_S.
    have hp' : HasPullback S_eq.arr (Subobject.entire (prod A T.dom)).arr := HasPullbacks.has _ _
    -- The genuine content: S_eq ≤ S_S.  A carrier point of S_eq satisfies (f a = T.arr·b);
    -- the pullback UMP factors a through f#T, and hle : f#T ≤ S gives a ∈ S.
    have hSEqle : S_eq.le S_S := by
      apply (allows_iff_classify S_S S_eq.arr).2
      rw [show HasSubobjectClassifier.classify S_S.arr S_S.monic = chiS from hcS]
      -- carrier c := S_eq.arr : S_eq.dom → prod A T.dom; c ≫ chiEq = ⊤.
      have hcarEq : S_eq.arr ≫ chiEq = term S_eq.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
        rw [show chiEq = HasSubobjectClassifier.classify S_eq.arr S_eq.monic from hcEq.symm]
        exact HasSubobjectClassifier.classify_sq S_eq.arr S_eq.monic
      -- chiEq = ⟨(fst≫f),(snd≫T.arr)⟩ ≫ eqChar; ⊤ means (c≫fst≫f) = (c≫snd≫T.arr) (diag_classify_iff).
      have hpaireq : S_eq.arr ≫ pair (fst ≫ f) (snd ≫ T.arr)
          = pair (S_eq.arr ≫ fst ≫ f) (S_eq.arr ≫ snd ≫ T.arr) := by
        apply pair_uniq
        · rw [Cat.assoc, fst_pair]
        · rw [Cat.assoc, snd_pair]
      have heq : S_eq.arr ≫ fst ≫ f = S_eq.arr ≫ snd ≫ T.arr := by
        apply (diag_classify_iff (S_eq.arr ≫ fst ≫ f) (S_eq.arr ≫ snd ≫ T.arr)).1
        rw [← hpaireq, Cat.assoc]
        show S_eq.arr ≫ chiEq = _
        rw [hcarEq]
      -- Pullback UMP: ⟨e≫fst, e≫snd≫T.arr⟩… actually e≫fst : S_eq.dom → A and e≫snd : → T.dom
      -- with (e≫fst) ≫ f = (e≫snd) ≫ T.arr (heq, reassociated).  This is a cone over (f, T.arr),
      -- so it factors through f#T = hp.cone; the resulting map composed with hp.cone.π₁ = e≫fst.
      have hcone : (S_eq.arr ≫ fst) ≫ f = (S_eq.arr ≫ snd) ≫ T.arr := by
        rw [Cat.assoc, Cat.assoc]; exact heq
      obtain ⟨u, ⟨hu₁, _hu₂⟩, _⟩ := hp.cone_isPullback
        ⟨S_eq.dom, S_eq.arr ≫ fst, S_eq.arr ≫ snd, hcone⟩
      -- u : S_eq.dom → (f#T).dom with u ≫ hp.cone.π₁ = e≫fst.  hp.cone.π₁ = (f#T).arr.
      -- hle : f#T ≤ S gives v : (f#T).dom → S.dom with v ≫ S.arr = (f#T).arr.
      obtain ⟨v, hv⟩ := hle
      -- So (u ≫ v) ≫ S.arr = e ≫ fst, i.e. e ≫ fst factors through S ⟹ e ≫ chiS = ⊤.
      have hfactor : (u ≫ v) ≫ S.arr = S_eq.arr ≫ fst := by
        rw [Cat.assoc, hv]; exact hu₁
      -- chiS = fst ≫ subChar S; goal S_eq.arr ≫ chiS = ⊤  ⟺  Allows S (e≫fst).
      show S_eq.arr ≫ chiS = _
      have : Allows S (S_eq.arr ≫ fst) := ⟨u ≫ v, hfactor⟩
      have hk := (allows_iff_classify S (S_eq.arr ≫ fst)).1 this
      show S_eq.arr ≫ (fst ≫ subChar S) = _
      rw [← Cat.assoc]; exact hk
    have hentireLe : (Subobject.entire (prod A T.dom)).le (Sub.imp S_eq S_S) := by
      rw [imp_adjunction S_eq S_S (Subobject.entire (prod A T.dom)) hp']
      obtain ⟨h₁, e₁⟩ := Sub.inter_le_left S_eq (Subobject.entire (prod A T.dom)) hp'
      obtain ⟨h₂, e₂⟩ := hSEqle
      exact ⟨h₁ ≫ h₂, by rw [Cat.assoc, e₂, e₁]⟩
    have hcl := (le_iff_classify (Subobject.entire (prod A T.dom)) (Sub.imp S_eq S_S)).mp hentireLe
    show subChar (Sub.imp S_eq S_S) = term (prod A T.dom) ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
    rw [show (Subobject.entire (prod A T.dom)).arr ≫ subChar (Sub.imp S_eq S_S)
          = subChar (Sub.imp S_eq S_S) from Cat.id_comp _] at hcl
    rw [hcl]
    congr 1
  · -- ⇐ : T ≤ ∀_f S  ⟹  f#T ≤ S.   Mirror `InternalForallTopos.bigInter_le_named`.
    intro hle
    -- Want f#T ≤ S, i.e. c := (f#T).arr is allowed by S: c ≫ χ_S = ⊤.
    apply (le_iff_classify (invImg f T hp) S).2
    show (invImg f T hp).arr ≫ subChar S = _
    -- T allowed by ∀_f S (from hle): T.arr ≫ forallChar f S = ⊤.
    have hTallow : T.arr ≫ forallChar f S
        = term T.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      have h := (le_iff_classify T (forallAlong f S)).1 hle
      rwa [classify_forallAlong] at h
    -- the pullback square c ≫ f = hp.cone.π₂ ≫ T.arr  lets us evaluate hTallow at the
    -- point hp.cone.π₂ : (f#T).dom → T.dom and pull the ∀ out via forall_beta/forall_elim
    -- at τ := c, where (f c = c≫f) makes the equality body reflexively true; MP (impΩ_forward)
    -- then gives c ∈ S.
    let K := (invImg f T hp).dom
    let c := (invImg f T hp).arr
    -- Step 1: evaluate hTallow at the point hp.cone.π₂ : K → T.dom, using c ≫ f = π₂ ≫ T.arr.
    -- LHS becomes (c ≫ f) ≫ curry body ≫ forallC A = ⊤, so (c≫f) ≫ curry body is entire.
    have hsq : c ≫ f = hp.cone.π₂ ≫ T.arr := invImg_sq f T hp
    have hentire : (c ≫ f) ≫ curry (forallBody f S) = term K ≫ topName A := by
      apply (forall_beta A ((c ≫ f) ≫ curry (forallBody f S))).mp
      rw [Cat.assoc]
      show (c ≫ f) ≫ forallChar f S = _
      rw [hsq, Cat.assoc, hTallow, ← Cat.assoc]
      congr 1
      exact term_uniq _ _
    -- Step 2: forall_elim at τ = c, then eval_curry_point: pair c (c≫f) ≫ forallBody = ⊤.
    have hbodyτ : pair c (c ≫ f) ≫ forallBody f S
        = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      rw [← eval_curry_point (forallBody f S) c (c ≫ f)]
      exact forall_elim _ hentire c
    -- Step 3: unfold body via forallBody_at; antecedent is reflexive equality (eqChar).
    rw [forallBody_at f S c (c ≫ f)] at hbodyτ
    -- Step 4: modus ponens with the reflexive equality (c≫f) = (c≫f).
    have hrefl : pair (c ≫ f) (c ≫ f) ≫ eqChar B
        = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) :=
      (diag_classify_iff (c ≫ f) (c ≫ f)).2 rfl
    have := impΩ_forward _ _ (Cat.id K)
      (by rw [Cat.id_comp]; exact hbodyτ)
      (by rw [Cat.id_comp]; exact hrefl)
    rwa [Cat.id_comp] at this

/-! ## Consequence: inverse image preserves binary unions (the FRAME LAW). -/

/-- **Frame law** (forward direction): `f#(S ∪ T) ≤ f#S ∪ f#T`.  `f#` is a left adjoint
    (to `∀_f`), so it preserves the join `∪`. -/
theorem invImage_preserves_union {A B : 𝒞} (f : A ⟶ B) (S T : Subobject 𝒞 B)
    (hpU : HasPullback f (HasSubobjectUnions.union S T).arr)
    (hpS : HasPullback f S.arr) (hpT : HasPullback f T.arr) :
    (invImg f (HasSubobjectUnions.union S T) hpU).le
      (HasSubobjectUnions.union (invImg f S hpS) (invImg f T hpT)) := by
  -- `f#` is left adjoint to `∀_f`, so it preserves the join `∪`.  Write `U := f#S ∪ f#T`.
  -- f#(S∪T) ≤ U  ↔  (S∪T) ≤ ∀_f U.
  rw [forallAlong_adjunction f (HasSubobjectUnions.union (invImg f S hpS) (invImg f T hpT))
    (HasSubobjectUnions.union S T) hpU]
  -- by union_min, suffices S ≤ ∀_f U and T ≤ ∀_f U.
  refine HasSubobjectUnions.union_min S T _ ?_ ?_
  · -- S ≤ ∀_f U  ↔  f#S ≤ U = f#S ∪ f#T,  which is union_left.
    rw [← forallAlong_adjunction f _ S hpS]
    exact HasSubobjectUnions.union_left _ _
  · -- T ≤ ∀_f U  ↔  f#T ≤ U,  which is union_right.
    rw [← forallAlong_adjunction f _ T hpT]
    exact HasSubobjectUnions.union_right _ _

end Freyd
