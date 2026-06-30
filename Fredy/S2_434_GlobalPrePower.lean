/-
  Freyd & Scedrov, *Categories and Allegories* §2.434.

  > 2.434. The systemic completion of a small locally complete distributive
  > allegory is a power allegory.
  > BECAUSE: We may reduce to the case of a one-object locally complete
  > distributive allegory A.  The global completion is easily seen to be a
  > pre-power allegory: given a set I let [I] be the set of functions from I to A
  > and let T be the [I]×I matrix defined via evaluation, that is, T_{f,i} = f(i).
  > Given any J×I matrix R define R̂ as the J×[I] matrix such that R̂_{j,f} = 1 or
  > 0 depending on whether or not R_{j,i}=f(i) for all i∈I.  R̂ is a map (each row
  > has exactly one 1).  R̂T = R and R̂°R = R̂°R̂T ⊑ T (because R̂ is simple).

  THIS FILE delivers the body of that argument: **the global completion of a
  one-object locally complete distributive allegory is a PRE-POWER allegory**
  (`globalScPrePower : PrePowerAllegory (GlobalObj (Sc 𝒜₀ pt))`), via the
  evaluation matrix `T`.  The headline "systemic completion is a power allegory"
  is then the corollary `effective_pre_power_is_power` (§2.432, already in the
  repo) applied to the systemic = effective completion of this pre-power
  allegory (§2.433/§2.226); see the closing note.

  ## The one-object reduction (`Sc`)

  Freyd reduces to a ONE-OBJECT locally complete distributive allegory `A`.  We
  encode such an `A` faithfully and at full generality as the one-object FULL
  SUBCATEGORY `Sc 𝒜₀ pt` of an arbitrary locally complete distributive allegory
  `𝒜₀` on a chosen object `pt` — i.e. the scalars are the endo-hom-set
  `pt ⟶ pt`, with the inherited `≫`, `°`, `∩`, `∪`, `𝟘`, `Sup`.  Every one-object
  l.c.d. allegory arises this way (take `𝒜₀` to be it, `pt` its object), and
  unlike `S2_316.OneObj` — whose composition is forced to be `∩` (locales only) —
  `Sc` keeps the composition of `𝒜₀` arbitrary, so the theorem is faithful to "an
  ARBITRARY one-object l.c.d. allegory", not just the meet-idempotent ones.

  The crucial structural fact that makes the matrix algebra clean is that `Sc`'s
  `Hom` is CONSTANT (`Hom _ _ := pt ⟶ pt`), so every entry of a matrix in
  `GlobalObj (Sc 𝒜₀ pt)` is a scalar `pt ⟶ pt`, the power-object index type
  `[I] = (I → (pt ⟶ pt))` does not depend on a source, and (since function types
  do not raise the universe, `max u u = u`) `[I]` stays in `Type u`.  The §2.224
  `GloballyComplete` universe wall therefore does NOT apply here.

  STRICTLY MATHLIB-FREE.  Reuses the §2.224 global completion verbatim; the only
  nonconstructive ingredient is classical decidability of `∀ i, R_{j,i} = f i`
  (`Classical.propDecidable`), which is what makes `R̂` boolean.
-/

import Fredy.S2_224_GlobalCompletion
import Fredy.S2_4

universe u

namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

attribute [local instance] Classical.propDecidable

/-! ## A one-object locally complete distributive allegory `Sc 𝒜₀ pt`

  The one-object full subcategory of `𝒜₀` on `pt`: a single object, hom-set the
  scalars `pt ⟶ pt`, every operation inherited from `𝒜₀`. -/

/-- The single object of the one-object l.c.d. allegory carved out of `𝒜₀` at
    `pt`.  Carries `𝒜₀` and `pt` as parameters so instance resolution recovers
    them (cf. `S2_316.OneObj`). -/
inductive Sc (𝒜₀ : Type u) (pt : 𝒜₀) : Type u
  | star

variable {𝒜₀ : Type u} [LocallyCompleteDistributiveAllegory.{u, u} 𝒜₀] {pt : 𝒜₀}

/-- Hom-set is the scalars `pt ⟶ pt`; identity/composition inherited from `𝒜₀`. -/
instance scCat : Cat.{u} (Sc 𝒜₀ pt) where
  Hom _ _ := pt ⟶ pt
  id _ := Cat.id pt
  comp f g := f ≫ g
  id_comp f := Cat.id_comp f
  comp_id f := Cat.comp_id f
  assoc f g h := Cat.assoc f g h

/-- Reciprocation/intersection inherited from `𝒜₀`. -/
instance scAllegory : Allegory (Sc 𝒜₀ pt) where
  toCat := scCat
  recip R := R°
  inter R S := R ∩ S
  recip_recip R := Allegory.recip_recip R
  recip_comp R S := Allegory.recip_comp R S
  recip_inter R S := Allegory.recip_inter R S
  inter_idem R := Allegory.inter_idem R
  inter_comm R S := Allegory.inter_comm R S
  inter_assoc R S T := Allegory.inter_assoc R S T
  semidistrib R S T := Allegory.semidistrib R S T
  modular R S T := Allegory.modular R S T

/-- Zero/union inherited from `𝒜₀`. -/
instance scDist : DistributiveAllegory (Sc 𝒜₀ pt) where
  toAllegory := scAllegory
  zero := fun {_ _} => (𝟘 : pt ⟶ pt)
  union R S := R ∪ S
  zero_comp R := DistributiveAllegory.zero_comp R
  comp_zero R := DistributiveAllegory.comp_zero R
  union_idem R := DistributiveAllegory.union_idem R
  union_comm R S := DistributiveAllegory.union_comm R S
  union_assoc R S T := DistributiveAllegory.union_assoc R S T
  union_inter_absorb R S := DistributiveAllegory.union_inter_absorb R S
  inter_union_absorb R S := DistributiveAllegory.inter_union_absorb R S
  comp_union_distrib R S T := DistributiveAllegory.comp_union_distrib R S T
  inter_union_distrib R S T := DistributiveAllegory.inter_union_distrib R S T
  zero_union R := DistributiveAllegory.zero_union R

/-- Arbitrary `Sup` inherited from `𝒜₀`. -/
instance scLCDA : LocallyCompleteDistributiveAllegory (Sc 𝒜₀ pt) where
  toDistributiveAllegory := scDist
  Sup P := LocallyCompleteDistributiveAllegory.Sup P
  le_Sup h := LocallyCompleteDistributiveAllegory.le_Sup h
  Sup_le h := LocallyCompleteDistributiveAllegory.Sup_le h
  comp_Sup_distrib R P := LocallyCompleteDistributiveAllegory.comp_Sup_distrib R P
  inter_Sup_distrib R P := LocallyCompleteDistributiveAllegory.inter_Sup_distrib R P

/-! ## A generic off-diagonal fact for the §2.224 identity matrix -/

/-- Off the diagonal the global identity matrix is `𝟘`: `i ≠ j ⟹ (1)_{ij} = 0`.
    (The diagonal case `(1)_{ii} = 1` is `globalId_diag`.) -/
theorem globalId_offdiag {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
    (A : GlobalObj 𝒜) {i j : A.idx} (h : i ≠ j) :
    globalId A i j = (𝟘 : A.obj i ⟶ A.obj j) := by
  rw [globalId_apply]
  apply gcSup_eq_zero
  rintro U ⟨he, _⟩
  exact absurd he h

/-- Entry form of `globalId_diag` (LHS as `Cat.id A i i`, for `rw` on goals). -/
theorem globalCatId_diag {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
    (A : GlobalObj 𝒜) (i : A.idx) : (Cat.id A : A ⟶ A) i i = Cat.id (A.obj i) :=
  globalId_diag A i

/-- Entry form of `globalId_offdiag` (LHS as `Cat.id A i j`, for `rw` on goals). -/
theorem globalCatId_offdiag {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
    (A : GlobalObj 𝒜) {i j : A.idx} (h : i ≠ j) :
    (Cat.id A : A ⟶ A) i j = (𝟘 : A.obj i ⟶ A.obj j) :=
  globalId_offdiag A h

/-! ## §2.434  The evaluation matrix and the boolean `R̂` -/

/-- `[I]`: the power object of the `I`-object `B`.  Its index type is the set
    `B.idx → (pt ⟶ pt)` of "rows" — functions assigning a scalar to each `i ∈ I`
    (Freyd: "the set of functions from I to A"); its carrier is the single
    object. -/
def powObj (B : GlobalObj (Sc 𝒜₀ pt)) : GlobalObj (Sc 𝒜₀ pt) :=
  ⟨B.idx → (pt ⟶ pt), fun _ => Sc.star⟩

/-- The EVALUATION matrix `T : [I] → I`, `T_{f,i} = f(i)` (§2.434). -/
def evalMat (B : GlobalObj (Sc 𝒜₀ pt)) : powObj B ⟶ B :=
  fun f i => f i

/-- Freyd's boolean `R̂ : J → [I]`, `R̂_{j,f} = 1` or `0` according to whether or
    not `R_{j,i} = f(i)` for all `i ∈ I` (§2.434).  The condition holds for
    exactly one `f`, namely the `j`-th row `f = R j`, so each row of `R̂` has
    exactly one `1` — `R̂` is a map. -/
noncomputable def hatMat {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B) : C ⟶ powObj B :=
  fun j f => if (∀ i, R j i = f i) then Cat.id pt else (𝟘 : pt ⟶ pt)

@[simp] theorem hatMat_pos {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B)
    (j : C.idx) (f : B.idx → (pt ⟶ pt)) (h : ∀ i, R j i = f i) :
    hatMat R j f = Cat.id pt := if_pos h

@[simp] theorem hatMat_neg {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B)
    (j : C.idx) (f : B.idx → (pt ⟶ pt)) (h : ¬ (∀ i, R j i = f i)) :
    hatMat R j f = (𝟘 : pt ⟶ pt) := if_neg h

/-! ### `R̂ T = R` -/

/-- `R̂T = R` (§2.434).  At entry `(j,i)` the sum over `f` of `R̂_{j,f} ≫ f(i)`
    collapses: only `f = R j` contributes (giving `1 ≫ R_{j,i} = R_{j,i}`); every
    other `f` contributes `0 ≫ f(i) = 0`. -/
theorem evalMat_hat_eq {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B) :
    hatMat R ≫ evalMat B = R := by
  funext j i
  show GlobalMorphism.comp (hatMat R) (evalMat B) j i = R j i
  rw [globalComp_apply]
  refine gcSup_eq ⟨R j, ?_⟩ ?_
  · -- membership: the row `f = R j` gives the value `R_{j,i}`.
    rw [hatMat_pos R j (R j) (fun _ => rfl)]
    show R j i = Cat.id pt ≫ R j i
    rw [Cat.id_comp]
  · -- upper bound: every term is `≤ R_{j,i}`.
    rintro X ⟨f, rfl⟩
    by_cases hf : ∀ i', R j i' = f i'
    · rw [hatMat_pos R j f hf]
      show Cat.id pt ≫ f i ⊑ R j i
      rw [Cat.id_comp, ← hf i]
      exact le_refl _
    · rw [hatMat_neg R j f hf]
      show (𝟘 : pt ⟶ pt) ≫ f i ⊑ R j i
      rw [DistributiveAllegory.zero_comp]
      exact zero_le _

/-! ### `R̂` is a map -/

/-- `R̂` is SIMPLE: `R̂° R̂ ⊑ 1` (§2.434, "each row has exactly one 1").  At entry
    `(f,g)` the sum over `j` of `(R̂_{j,f})° ≫ R̂_{j,g}` is non-zero only when both
    `f` and `g` equal the row `R j`, forcing `f = g`. -/
theorem hatMat_simple {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B) :
    Simple (hatMat R) := by
  show (hatMat R)° ≫ hatMat R ⊑ Cat.id (powObj B)
  apply global_le_of_entry
  intro f g
  show GlobalMorphism.comp (GlobalMorphism.recip (hatMat R)) (hatMat R) f g ⊑ _
  rw [globalComp_apply]
  apply Sup_le
  rintro X ⟨j, rfl⟩
  rw [globalRecip_apply]
  -- entry `(R̂_{j,f})° ≫ R̂_{j,g}` of `R̂° R̂`.  Convert each branch to the
  -- 𝒜₀-native scalar form (where `recip_id`/`recip_zero` apply at `pt`).
  by_cases hfg : f = g
  · subst hfg
    rw [globalCatId_diag]
    by_cases hf : ∀ i, R j i = f i
    · rw [hatMat_pos R j f hf]
      show (Cat.id pt)° ≫ Cat.id pt ⊑ Cat.id pt
      rw [recip_id, Cat.id_comp]
      exact le_refl _
    · rw [hatMat_neg R j f hf]
      show (𝟘 : pt ⟶ pt)° ≫ (𝟘 : pt ⟶ pt) ⊑ Cat.id ((powObj B).obj f)
      rw [recip_zero, DistributiveAllegory.zero_comp]
      exact zero_le _
  · by_cases hf : ∀ i, R j i = f i
    · by_cases hg : ∀ i, R j i = g i
      · exact absurd (funext fun i => (hf i).symm.trans (hg i)) hfg
      · rw [hatMat_pos R j f hf, hatMat_neg R j g hg]
        show (Cat.id pt)° ≫ (𝟘 : pt ⟶ pt) ⊑ Cat.id (powObj B) f g
        rw [DistributiveAllegory.comp_zero]
        exact zero_le _
    · rw [hatMat_neg R j f hf]
      show (𝟘 : pt ⟶ pt)° ≫ hatMat R j g ⊑ Cat.id (powObj B) f g
      rw [recip_zero, DistributiveAllegory.zero_comp]
      exact zero_le _

/-- `R̂` is ENTIRE: `1 ⊑ R̂ R̂°` (§2.434, "each row has exactly one 1" — at least
    one).  At the diagonal entry `(j,j)` the row `f = R j` contributes
    `1 ≫ 1° = 1`, so `1_{C.obj j} ⊑ (R̂ R̂°)_{jj}`. -/
theorem hatMat_entire {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B) :
    Entire (hatMat R) := by
  show Cat.id C ∩ (hatMat R ≫ (hatMat R)°) = Cat.id C
  refine le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) ?_)
  apply global_le_of_entry
  intro j j'
  by_cases hjj : j = j'
  · subst hjj
    rw [globalCatId_diag]
    show Cat.id (C.obj j) ⊑ GlobalMorphism.comp (hatMat R) (GlobalMorphism.recip (hatMat R)) j j
    rw [globalComp_apply]
    refine le_trans ?_ (le_Sup ⟨R j, rfl⟩)
    rw [globalRecip_apply, hatMat_pos R j (R j) (fun _ => rfl)]
    show Cat.id pt ⊑ Cat.id pt ≫ (Cat.id pt)°
    rw [recip_id, Cat.id_comp]
    exact le_refl _
  · rw [globalCatId_offdiag C hjj]
    exact zero_le _

/-- `R̂` is a MAP (§2.434). -/
theorem hatMat_map {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B) : Map (hatMat R) :=
  ⟨hatMat_entire R, hatMat_simple R⟩

/-! ### The evaluation matrix is thick (the matrix-algebra core, division-free) -/

/-- §2.434 core: for every matrix `R : J → I` there is a map `R̂` (namely `hatMat
    R`) with `R̂T ⊑ R` (in fact `= R`) and `R̂°R ⊑ T`.  This is exactly Freyd's
    three containments witnessing that the evaluation matrix `T` is thick (the
    right-hand side of §2.431/`thick_iff_existential`), and it needs only the
    allegory structure — no division.

    `R̂°R = R̂°(R̂T) = (R̂°R̂)T ⊑ 1·T = T` since `R̂` is simple. -/
theorem evalMat_thick_exists (B : GlobalObj (Sc 𝒜₀ pt)) (C : GlobalObj (Sc 𝒜₀ pt))
    (R : C ⟶ B) :
    ∃ (R' : C ⟶ powObj B),
      Entire R' ∧ R' ≫ evalMat B ⊑ R ∧ R'° ≫ R ⊑ evalMat B := by
  refine ⟨hatMat R, hatMat_entire R, ?_, ?_⟩
  · rw [evalMat_hat_eq]; exact le_refl _
  · calc (hatMat R)° ≫ R
        = (hatMat R)° ≫ (hatMat R ≫ evalMat B) := by rw [evalMat_hat_eq]
      _ = ((hatMat R)° ≫ hatMat R) ≫ evalMat B := by rw [Cat.assoc]
      _ ⊑ Cat.id (powObj B) ≫ evalMat B := comp_mono_right (hatMat_simple R) _
      _ = evalMat B := Cat.id_comp _

/-! ## §2.434  The global completion of a one-object l.c.d. allegory is pre-power

  Packaging: equip `GlobalObj (Sc 𝒜₀ pt)` with its (§2.315a) division-allegory
  structure `divisionAllegoryLCDA` (via `letI`), under which `Thick`/§2.431 are
  available; each object `B` is then the target of the thick evaluation matrix
  `T = evalMat B` by `thick_iff_existential` applied to `evalMat_thick_exists`. -/

/-- §2.434: **the global completion of a one-object locally complete distributive
    allegory is a PRE-POWER allegory**, via the evaluation matrix.  Each object
    `B` is the target of the thick morphism `evalMat B : [B] → B`. -/
noncomputable def globalScPrePower : PrePowerAllegory (GlobalObj (Sc 𝒜₀ pt)) :=
  letI dva := divisionAllegoryLCDA (𝒜 := GlobalObj (Sc 𝒜₀ pt))
  { dva with
    thick_target := fun B =>
      ⟨powObj B, evalMat B,
        (thick_iff_existential (evalMat B)).mpr
          (fun C R _hbox => evalMat_thick_exists B C R)⟩ }

/-! ## §2.434  Corollary: the systemic completion is a power allegory

  The SYSTEMIC completion of `𝒜₀` is the EFFECTIVE completion (split symmetric
  idempotents, §2.226) of the global completion `GlobalObj (Sc 𝒜₀ pt)`.  Splitting
  symmetric idempotents preserves the pre-power structure and makes the result
  effective, so by §2.432 (`effective_pre_power_is_power`, already in the repo)
  it is a power allegory.  Concretely: if the systemic completion `𝒮` of a
  one-object l.c.d. allegory is presented as an `EffectivePrePowerAllegory` — its
  thick targets are the images of the `evalMat B` under the splitting embedding —
  then `effective_pre_power_is_power : PowerAllegory 𝒮`.

  We do NOT re-prove the §2.226/§2.433 effective-completion bridge here (it is
  formalised separately); `globalScPrePower` is the §2.434 content proper (the
  pre-power half), and the headline is its image under that bridge. -/

-- BOOK §2.434 headline: the systemic completion of a small l.c.d. allegory is a
-- power allegory.  = `effective_pre_power_is_power` (§2.432) applied to the
-- effective/systemic completion (§2.226/§2.433) of `globalScPrePower` above.

end Freyd.Alg
