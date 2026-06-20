/-
  Freyd & Scedrov, *Categories and Allegories* §1.943 / §1.77 — toward the
  reflexive-transitive closure `R*` in a topos as the internal-∀ family-glb
  `⋂{ S : BinRel A A | 1 ⊑ S ∧ R ⊑ S ∧ S⊚S ⊑ S }` over a subobject family of `[A×A]`.

  ## Status (HONEST)

  This file delivers the *reusable bridge* the `bigInter`-over-`prod A A` construction
  needs — the `Subobject (prod A A) → BinRel A A` converter `subToRel`, inverse to
  `relSub` — together with its round-trip laws and the order-correspondence
  `RelLe ↔ Subobject.le` lifted through it.  These were genuinely MISSING (the codebase
  had only `relSub : BinRel → Subobject` one-way, S1_60).

  The full `toposHasReflTransClosure` instance is NOT registered here.  See the
  RESIDUAL note at the bottom for the precise reason: the family-membership predicate
  `χ_F : [A×A] → Ω` must internally test transitivity `S⊚S ⊑ S` of the *variable*
  relation `S`, which needs a fibered internal relational composition (an internal
  existential `∃b. aSb ∧ bSc` over the variable `S`).  That operation is the genuine
  §1.543/§1.54-class residual; it is not yet available in the repo, and faking any
  `TransRefClos` field (or registering a `sorry`-backed instance to discharge the
  downstream `topos_has_coequalizers`/`topos_is_bicartesian`) would be a false close.
-/

import Fredy.S1_60
import Fredy.S1_77

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

section
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- **`subToRel` — a subobject of `A×B` as a binary relation `A → B`.**  Inverse to
    `relSub` (S1_60): split the monic `m : S ↣ A×B` into its two projections
    `m≫fst, m≫snd`, jointly monic because `pair (m≫fst) (m≫snd) = m` is monic.

    This is exactly the converter the family-glb RTC construction needs to turn the
    `bigInter : Subobject (prod A A)` back into a `BinRel A A`. -/
noncomputable def subToRel {A B : 𝒞} (S : Subobject 𝒞 (prod A B)) : BinRel 𝒞 A B where
  src  := S.dom
  colA := S.arr ≫ fst
  colB := S.arr ≫ snd
  isMonicPair := by
    -- jointly monic: if `f, g` agree on both legs they agree on `S.arr` (product η),
    -- and `S.arr` is monic.  (`pair (S.arr≫fst) (S.arr≫snd) = S.arr`.)
    intro W f g hfA hgA
    apply S.monic
    -- `f ≫ S.arr = g ≫ S.arr` from agreement on `fst`/`snd` legs of `S.arr`.
    have hf : f ≫ S.arr = pair (f ≫ (S.arr ≫ fst)) (f ≫ (S.arr ≫ snd)) :=
      pair_uniq _ _ _ (by rw [Cat.assoc]) (by rw [Cat.assoc])
    have hg : g ≫ S.arr = pair (f ≫ (S.arr ≫ fst)) (f ≫ (S.arr ≫ snd)) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, hfA]) (by rw [Cat.assoc, hgA])
    rw [hf, hg]

/-- `(subToRel S).arr`-pairing is `S.arr`: `pair (S.arr≫fst) (S.arr≫snd) = S.arr`. -/
theorem relSub_subToRel_arr {A B : 𝒞} (S : Subobject 𝒞 (prod A B)) :
    pair (subToRel S).colA (subToRel S).colB = S.arr :=
  (pair_uniq (S.arr ≫ fst) (S.arr ≫ snd) S.arr rfl rfl).symm

end

section
variable [PreLogos 𝒞]

/-- **Round-trip `subToRel (relSub R) = R`.**  `relSub R` has arrow `pair R.colA R.colB`,
    whose two projections are `R.colA`, `R.colB` again. -/
theorem subToRel_relSub {A B : 𝒞} (R : BinRel 𝒞 A B) : subToRel (relSub R) = R := by
  -- `subToRel (relSub R)` is `BinRel.mk R.src (pair R.colA R.colB ≫ fst) (… ≫ snd) …`;
  -- the two cols recover `R.colA`, `R.colB` by the fst/snd β-laws; `src` is `R.src`
  -- definitionally and `isMonicPair` is a `Prop` (proof-irrelevant).  Field-wise congruence.
  simp only [subToRel, relSub, fst_pair, snd_pair]

/-- **Order correspondence through `subToRel`.**  `RelLe (subToRel S) (subToRel T)`
    is exactly `S.le T` for subobjects `S, T` of `A×B`.  (Via `relLe_iff_subLe` and the
    `relSub_subToRel_arr` η-law: `relSub (subToRel S)` has the same arrow as `S`.) -/
theorem relLe_subToRel_iff_subLe {A B : 𝒞} (S T : Subobject 𝒞 (prod A B)) :
    RelLe (subToRel S) (subToRel T) ↔ S.le T := by
  rw [relLe_iff_subLe]
  -- `(relSub (subToRel S)).arr = pair (subToRel S).colA (subToRel S).colB = S.arr`
  -- (`relSub_subToRel_arr`); same for T.  Both directions just rewrite the arrows.
  have hS : (relSub (subToRel S)).arr = S.arr := relSub_subToRel_arr S
  have hT : (relSub (subToRel T)).arr = T.arr := relSub_subToRel_arr T
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    rw [hT] at hh
    rw [← hS]; exact hh
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    rw [hT, hS]; exact hh

end

/-! ## RESIDUAL — why the `toposHasReflTransClosure` instance is not registered here

  TARGET.  `instance toposHasReflTransClosure [Topos 𝒞] : HasReflTransClosure 𝒞`, i.e. for
  every `R : BinRel A A`, a `TransRefClos R` with fields `clos, le, refl, trans, minimal`.

  INTENDED CONSTRUCTION (§1.943 family-glb).
    `R* = subToRel (bigInter Fname_R)`  where  `bigInter` (InternalForallTopos, sorry-free)
    is the internal-∀ big-intersection over `prod A A`, and `Fname_R : 1 → [[A×A]]` names the
    family  `F_R = { S ⊆ A×A | (1_A ⊆ S) ∧ (R ⊆ S) ∧ (S⊚S ⊆ S) }`  of reflexive-transitive
    relations containing `R`.  Then, modelled on `Fredy/LeastClosedTopos.lean`:
      · `minimal` — `bigInter_le_named`: every reflexive-transitive `T ⊇ R` has its name in
        `F_R`, so `R* ⊑ T`.  REACHABLE once `Fname_R` exists.
      · `le` / `refl` — `bigInter_ge`: `relSub R` (resp. the diagonal) lies below every member,
        hence below `⋂F_R`.  REACHABLE once `Fname_R` exists.
      · `trans` — the `least_tStable`-analog: `⋂F_R` is itself transitive (glb of transitive
        relations is transitive).

  THE BLOCKER (genuine §1.543/§1.54-class residual).  Even merely DEFINING `Fname_R` requires
  the family predicate `χ_{F_R} : [A×A] → Ω`, whose transitivity conjunct must internally test
  `S⊚S ⊑ S` for the *variable* relation `S` (a point of `[A×A]`).  Relational composition
  `⊚` is EXTERNAL (S1_56: a pullback-then-image on `BinRel`); there is no fibered internal
  relational composition / internal existential `∃b. aSb ∧ bSc` as an Ω-valued map of the
  variable `S`.  Contrast `Fredy/LeastClosedTopos.lean`, which succeeds precisely because its
  stability operator `t : A → A` is a FUNCTION — `t(x)∈σ` is `⟨fst≫t,snd⟩≫eval`, needing NO
  existential.  The internal-relation machinery that exists (`evalRel`, `univClassify`,
  `relPullback`, `relPullback_compose_dist`, `compose_assoc_of_regular`; S1_92/S1_95) composes
  relations named by FIXED points, not the fibered/variable composition the predicate needs.

  Building that fibered internal composition is the genuine open piece; faking any field, or
  registering a `sorry`-backed instance to silence `topos_has_coequalizers` /
  `topos_is_bicartesian` (S1_95), is disallowed.  `subToRel` and its round-trip laws above are
  the reusable converter that construction will need.

  Once `[HasReflTransClosure 𝒞]` lands, the two S1_95 sorries close immediately:
    `topos_has_coequalizers`  :=  `preTopos_rtc_has_coequalizers` (S1_95, sorry-free given the
        instance); `topos_is_bicartesian`  :=  Cartesian + `topos_has_strict_coterminator`
        + `topos_is_positive` + that `HasCoequalizers`.
-/

end Freyd
