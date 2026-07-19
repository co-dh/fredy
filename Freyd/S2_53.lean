import Freyd.S2_3
import Freyd.S2_5
import Freyd.S2_51

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* §2.536.

      "An amenable quotient of a division allegory is a division allegory."

  Given a DIVISION ALLEGORY `𝒜` and an `AmenableCongruence amen` on it, the
  quotient allegory `QuotAllegory 𝒜 amen.cong` (§2.5) carries a right division.
  On classes it is

      R̄ / S̄  :=  overline(R⁺ / S⁺)        ( = `Quotient.mk _ (largest R / largest S)` )

  where `R⁺ = amen.largest R` is the largest element of `R`'s congruence class
  (§2.53) and `R⁺ / S⁺` is the BASE division.  Since `⁺` depends only on the
  congruence class (`amenable_largest_class_invariant`), this is well-defined.

  The division adjunction `T̄ ⊑ R̄/S̄ ↔ T̄S̄ ⊑ R̄` is the book's argument:

    * `(R⁺/S⁺)S⁺ ⊑ R⁺` gives `(overline(R⁺/S⁺))S̄ ⊑ R̄`            [div_comp_le];
    * if `overline(TS) ⊑ R̄` then `(TS)⁺ ⊑ R⁺` by §2.533, hence `T⁺S⁺ ⊑ R⁺`
      by §2.534, so `T⁺ ⊑ R⁺/S⁺` by the BASE adjunction, hence
      `T̄ ⊑ overline(R⁺/S⁺) = R̄/S̄`                                  [le_div].

  The quotient order is detected by the largest-element calculus
  (`quotLe_iff_largest`, a repackaging of §2.532/§2.533): in the quotient
  `[R] ⊑ [S] ↔ R⁺ ⊑ S⁺`.

  STRICTLY mathlib-free; only `Freyd.*` + Lean core.
-/



namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ## The quotient order via the largest-element calculus

  In the quotient allegory `QuotAllegory 𝒜 amen.cong`, `[R] ⊑ [S]` holds iff
  `R⁺ ⊑ S⁺` (§2.533).  This is the only fact about the order we need; it is
  proven elementarily from §2.532 `(R∩S)⁺ = R⁺ ∩ S⁺` and the class-invariance of
  `⁺`.  The instance is PINNED to `QuotAllegory.instAllegory` (rather than left to
  typeclass search) so it cannot be confused with the under-construction division
  structure below. -/

/-- §2.533 (order form).  In `QuotAllegory 𝒜 amen.cong`,
    `[R] ⊑ [S]  ↔  R⁺ ⊑ S⁺`. -/
theorem quotLe_iff_largest (amen : AmenableCongruence 𝒜) {a b : 𝒜} (R S : a ⟶ b) :
    @le (QuotAllegory 𝒜 amen.cong) a b (QuotAllegory.instAllegory amen.cong)
        (Quotient.mk (congSetoid amen.cong) R) (Quotient.mk (congSetoid amen.cong) S)
      ↔ amen.largest R ⊑ amen.largest S := by
  -- `[R] ⊑ [S]` unfolds to `[R] ∩ [S] = [R]`, and `[R] ∩ [S] = [R ∩ S]`.
  show (Quotient.mk (congSetoid amen.cong) (R ∩ S) = Quotient.mk (congSetoid amen.cong) R)
        ↔ amen.largest R ⊑ amen.largest S
  constructor
  · intro h
    -- `[R ∩ S] = [R]` means `R ∩ S ≡ R`, so `(R ∩ S)⁺ = R⁺`; and `(R ∩ S)⁺ = R⁺ ∩ S⁺`.
    have hrel : amen.cong.rel (R ∩ S) R := Quotient.exact h
    have e1 : amen.largest (R ∩ S) = amen.largest R := amenable_largest_class_invariant amen hrel
    have e2 : amen.largest (R ∩ S) = amen.largest R ∩ amen.largest S := amenable_inter_largest amen R S
    show amen.largest R ∩ amen.largest S = amen.largest R
    rw [← e2, e1]
  · intro h
    -- `R⁺ ∩ S⁺ = R⁺` and `(R ∩ S)⁺ = R⁺ ∩ S⁺` give `(R ∩ S)⁺ = R⁺`, hence `R ∩ S ≡ R`.
    have e2 : amen.largest (R ∩ S) = amen.largest R ∩ amen.largest S := amenable_inter_largest amen R S
    have e1 : amen.largest (R ∩ S) = amen.largest R := by rw [e2]; exact h
    have hRS : amen.cong.rel (R ∩ S) (amen.largest (R ∩ S)) := amen.largest_rel (R ∩ S)
    rw [e1] at hRS
    exact Quotient.sound (amen.cong.trans hRS (amen.cong.symm (amen.largest_rel R)))


/-! ## §2.536  The quotient division allegory

  `R̄ / S̄ := overline(R⁺ / S⁺)`, well-defined by class-invariance of `⁺`.  The
  adjunction is the book's proof, routed through `quotLe_iff_largest`. -/

/-- §2.536  An amenable quotient of a division allegory is a division allegory.

    `R̄ / S̄ = overline(R⁺ / S⁺)`; the distributive structure is
    `QuotAllegory.instDistributiveAllegory` (using `amen.union_congr`). -/
def QuotAllegory.instDivisionAllegory (amen : AmenableCongruence 𝒜) :
    DivisionAllegory (QuotAllegory 𝒜 amen.cong) :=
  { QuotAllegory.instDistributiveAllegory amen.cong
      (fun hR hS => amen.union_congr hR hS) with
    div := fun {_ _ _} Rq Sq =>
      Quotient.lift₂
        (fun R S => Quotient.mk (congSetoid amen.cong) (amen.largest R / amen.largest S))
        (fun _ _ _ _ hR hS => by
          refine congrArg (Quotient.mk (congSetoid amen.cong)) ?_
          rw [amenable_largest_class_invariant amen hR,
            amenable_largest_class_invariant amen hS])
        Rq Sq
    -- §2.536: `(R⁺/S⁺)S⁺ ⊑ R⁺` implies `(overline(R⁺/S⁺))S̄ ⊑ R̄`.
    div_comp_le := by
      intro a b c Rq Sq
      refine Quotient.inductionOn₂ Rq Sq (fun R S => ?_)
      -- Goal (defeq): `[(R⁺/S⁺) ≫ S] ⊑ [R]`.  By `quotLe_iff_largest`:
      --   `((R⁺/S⁺) ≫ S)⁺ ⊑ R⁺`.
      refine (quotLe_iff_largest amen ((amen.largest R / amen.largest S) ≫ S) R).mpr ?_
      -- Base triangle `(R⁺/S⁺) ≫ S⁺ ⊑ R⁺`.
      have base : (amen.largest R / amen.largest S) ≫ amen.largest S ⊑ amen.largest R :=
        DivisionAllegory.div_comp_le (amen.largest R) (amen.largest S)
      -- `S ≡ S⁺`, so `((R⁺/S⁺) ≫ S)⁺ = ((R⁺/S⁺) ≫ S⁺)⁺`.
      have heq : amen.largest ((amen.largest R / amen.largest S) ≫ S)
               = amen.largest ((amen.largest R / amen.largest S) ≫ amen.largest S) :=
        amenable_largest_class_invariant amen
          (amen.cong.comp_congr (amen.cong.refl _) (amen.largest_rel S))
      -- `((R⁺/S⁺) ≫ S⁺)⁺ ⊑ R⁺⁺ = R⁺`.
      have hmono : amen.largest ((amen.largest R / amen.largest S) ≫ amen.largest S)
                 ⊑ amen.largest (amen.largest R) := amenable_le_largest amen base
      rw [largest_idem amen R] at hmono
      rw [heq]; exact hmono
    -- §2.536: if `overline(TS) ⊑ R̄` then `T̄ ⊑ overline(R⁺/S⁺)`.
    le_div := by
      intro a b c Tq Rq Sq
      refine Quotient.inductionOn₃ Tq Rq Sq (fun T R S => ?_)
      intro h
      -- `h : [T ≫ S] ⊑ [R]`, i.e. `(TS)⁺ ⊑ R⁺` by §2.533.
      have hTS : amen.largest (T ≫ S) ⊑ amen.largest R :=
        (quotLe_iff_largest amen (T ≫ S) R).mp h
      -- §2.534: `T⁺S⁺ ⊑ (TS)⁺`, so `T⁺S⁺ ⊑ R⁺`.
      have hcomp : amen.largest T ≫ amen.largest S ⊑ amen.largest R :=
        le_trans (largest_comp_le amen T S) hTS
      -- Base adjunction: `T⁺ ⊑ R⁺/S⁺`.
      have hdiv : amen.largest T ⊑ amen.largest R / amen.largest S :=
        (le_div_iff _ _ _).mpr hcomp
      -- `⁺`-monotone (§2.531): `T⁺⁺ ⊑ (R⁺/S⁺)⁺`, and `T⁺⁺ = T⁺`.
      have hmono : amen.largest (amen.largest T)
                 ⊑ amen.largest (amen.largest R / amen.largest S) := amenable_le_largest amen hdiv
      rw [largest_idem amen T] at hmono
      -- Goal (defeq): `[T] ⊑ [R⁺/S⁺]`.  By `quotLe_iff_largest`: `T⁺ ⊑ (R⁺/S⁺)⁺`.
      exact (quotLe_iff_largest amen T (amen.largest R / amen.largest S)).mpr hmono }

/-- §2.536 (statement of the delivered adjunction).  In the amenable quotient,
    `T̄ ⊑ R̄/S̄  ↔  T̄ ≫ S̄ ⊑ R̄`, where `R̄/S̄ = overline(R⁺/S⁺)`.  This is the
    division-allegory law `le_div_iff` re-exported against
    `QuotAllegory.instDivisionAllegory`. -/
theorem quotient_le_div_iff (amen : AmenableCongruence 𝒜) {a b c : 𝒜}
    (Tq : @Cat.Hom (QuotAllegory 𝒜 amen.cong) _ a b)
    (Rq : @Cat.Hom (QuotAllegory 𝒜 amen.cong) _ a c)
    (Sq : @Cat.Hom (QuotAllegory 𝒜 amen.cong) _ b c) :
    letI := QuotAllegory.instDivisionAllegory amen
    Tq ⊑ Rq / Sq ↔ Tq ≫ Sq ⊑ Rq := by
  letI := QuotAllegory.instDivisionAllegory amen
  exact le_div_iff Tq Rq Sq

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* §2.537

      "An amenable quotient of an effective power allegory is an effective power allegory."

  BOOK PROOF (§2.537, verbatim):
    "Effectivity is preserved by [2.535].  Thus it suffices to show that the quotient
     allegory is a pre-power allegory [2.432].  We show that overline(∋_R) is thick.
     Note that ∋_R = ∋_{R⁺} [2.41].  From  1 ⊑ (R⁺/∋_R)(∋_R/R⁺) ⊑ (R⁺/∋_R)(∋_{R⁺}/R⁺),
     we obtain  1̄ ⊑ (R̄/overline(∋_R))(overline(∋_R)/R̄)  as in the last section [§2.536]."

  STRUCTURE OF THE FORMALISATION.
  The quotient allegory `QuotAllegory 𝒜 amen.cong` is already built (S2_5_QuotAllegory)
  as a genuine `Allegory`; here we equip it with the rest of the power-allegory tower and
  prove the §2.537 theorem.  Following the book, the proof has three layers:

  1.  §2.536 division on the quotient — `R̄/S̄ := overline(R⁺/S⁺)`.  Built UNCONDITIONALLY
      as a `DivisionAllegory (QuotAllegory …)` instance (`quotDiv`) from the amenable ⁺
      calculus (§2.531 `amenable_le_largest`, §2.532 `amenable_inter_largest`, §2.534
      `largest_comp_le`).  The bridge `quot_le_iff` (§2.533, `[R]⊑[S] ↔ R⁺⊑S⁺`) is the
      workhorse.

  2.  §2.535 effectivity — every quotient equivalence relation splits.  Built
      UNCONDITIONALLY (`quotSplit`): a quotient equivalence relation `[E₀]` forces `E₀⁺`
      reflexive/symmetric/transitive (§2.535 `largest_reflexive/symmetric/transitive`),
      hence an equivalence relation in `𝒜`, which splits by effectiveness of `𝒜`; the
      splitting descends.

  3.  §2.537 pre-power — each object is the target of the thick morphism `[∋_b]`.  Proven
      (`quotThickEps`) from `thick_iff_existential` (§2.431) by transporting the box-matched
      thickness of `∋_b` in `𝒜` through the ⁺-calculus, exactly the book's inequality.

  HYPOTHESES we must surface (precisely the book steps the repo does not yet build):
  *  `htab` — §2.51 "a quotient of a tabular allegory is tabular".  The repo's
     `EffectiveAllegory` bundles `TabularAllegory`, and §2.51 (tabulation of `[R]` via the
     tabulation of `R⁺`) is a separate, unbuilt section; we take quotient-tabularity as a
     named hypothesis.  (Effectivity's *splitting* half, §2.535, IS proven, layer 2.)
  *  `hbox` — the book's "∋_R = ∋_{R⁺} [2.41]": the membership's box-index depends only on
     the congruence class, so a quotient box-match `codBox [R] = codBox [∋_b]` descends to an
     EXACT box-match `codBox R⁺ = codBox (∋_b)` in `𝒜` (the domain on which `𝒜`'s
     box-guarded membership thickness, §2.41/§2.43, is defined).  Stated as a named
     hypothesis because §2.41's box-naming for the quotient membership is not built.

  Everything else — the division allegory, the effectivity splitting, and the thickness
  inequality itself — is UNCONDITIONAL.  Final assembly `quot_effective_power_is_power`
  produces `PowerAllegory (QuotAllegory 𝒜 amen.cong)` via `effective_pre_power_is_power`
  (§2.432).  No `sorry`.
-/

-- (S2_5 → S2_4 → S2_1/2/3 imported transitively: PowerAllegory, Thick, EffectivePrePowerAllegory,
--  effective_pre_power_is_power, AmenableCongruence + §2.531-2.535 ⁺-calculus.)


namespace Freyd.Alg

/-! ## §2.537  An effective power allegory

  The book's hypothesis "effective power allegory" is a power allegory that is also
  effective.  `PowerAllegory` and `EffectiveAllegory` both extend `Allegory` by distinct
  paths; combining them as two separate context instances would create an `Allegory`
  diamond (a freshly bound morphism's `⟶` resolves through one parent's `Allegory`, but a
  predicate like `Thick`/`Map` through the other).  Following the repo's idiom
  (`EffectiveDivisionAllegory`, `PrePositivePowerAllegory`), we flatten them into one class
  over a single shared `Allegory`. -/

/-- An EFFECTIVE POWER ALLEGORY (§2.537 hypothesis): a `PowerAllegory` that is also
    `EffectiveAllegory`, over ONE underlying `Allegory` (no instance diamond). -/
class EffectivePowerAllegory (𝒜 : Type u) extends PowerAllegory 𝒜, EffectiveAllegory 𝒜

section
variable {𝒜 : Type u} [DivisionAllegory 𝒜] (amen : AmenableCongruence 𝒜)

/-! ## §2.533  The order bridge `[R] ⊑ [S] ↔ R⁺ ⊑ S⁺`

  `QuotAllegory`'s order `⊑` is the lattice order `[R] ∩ [S] = [R]`, i.e. `R∩S ≡ R`.  The
  amenable ⁺-calculus turns this into `R⁺ ⊑ S⁺` (§2.533), the single fact through which all
  quotient (in)equalities are decided.

  We write the hom-class of `R` as `(quotRep amen.cong).map R`; this carries the quotient
  allegory's `⟶` type syntactically (so `⊑`/`≫`/`∩` resolve to the quotient instances),
  while being definitionally `Quotient.mk (congSetoid amen.cong) R`. -/

/-- §2.533: in `QuotAllegory 𝒜 amen.cong`, `[R] ⊑ [S] ↔ R⁺ ⊑ S⁺`.
    `[R] ⊑ [S]` unfolds (lattice order) to `[R∩S] = [R]`, i.e. `R∩S ≡ R`; then §2.532
    `(R∩S)⁺ = R⁺∩S⁺` plus class-invariance of `⁺` give the equivalence with `R⁺ ⊑ S⁺`. -/
theorem quot_le_iff {a b : 𝒜} (R S : a ⟶ b) :
    (quotRep amen.cong).map R ⊑ (quotRep amen.cong).map S ↔
      amen.largest R ⊑ amen.largest S := by
  -- `[R] ⊑ [S]` is `[R] ∩ [S] = [R]`; the quotient `∩` lifts to `[R∩S]`.
  show (quotRep amen.cong).map R ∩ (quotRep amen.cong).map S = (quotRep amen.cong).map R ↔ _
  rw [← (quotRep amen.cong).map_inter R S, quotRep_map, quotRep_map]
  constructor
  · intro h
    -- (R∩S) ≡ R ⟹ (R∩S)⁺ = R⁺; and (R∩S)⁺ = R⁺ ∩ S⁺ (§2.532) ⟹ R⁺ ⊑ S⁺.
    have hrel : amen.cong.rel (R ∩ S) R := Quotient.exact h
    have hcl : amen.largest (R ∩ S) = amen.largest R := amenable_largest_class_invariant amen hrel
    rw [amenable_inter_largest amen] at hcl
    -- `⊑` is definitionally `_ ∩ _ = _`.
    exact hcl
  · intro h
    -- R⁺ ⊑ S⁺ ⟹ R⁺∩S⁺ = R⁺ = (R∩S)⁺ (§2.532); X ≡ X⁺ gives (R∩S) ≡ R.
    apply Quotient.sound
    show amen.cong.rel (R ∩ S) R
    have hcl : amen.largest (R ∩ S) = amen.largest R := by
      rw [amenable_inter_largest amen]; exact h
    -- R∩S ≡ (R∩S)⁺ = R⁺ ≡ R.
    refine amen.cong.trans (amen.largest_rel (R ∩ S)) ?_
    rw [hcl]; exact amen.cong.symm (amen.largest_rel R)

/-- `X ⊑ X⁺` — every element sits below the largest in its class. -/
theorem le_largest_self {a b : 𝒜} (R : a ⟶ b) : R ⊑ amen.largest R :=
  amen.largest_max (amen.cong.refl R)


end

/-! ## §2.536  The division allegory of the quotient

  `R̄/S̄ := overline(R⁺/S⁺)`.  Well-defined because `⁺` is class-invariant; the two
  division laws reduce, via `quot_le_iff`, to the ⁺-calculus (`amenable_le_largest §2.531`,
  `largest_comp_le §2.534`). -/

section Division
variable {𝒜 : Type u} [DivisionAllegory 𝒜] (amen : AmenableCongruence 𝒜)

/-- §2.536: the quotient of a division allegory is a division allegory, with
    `R̄/S̄ = overline(R⁺/S⁺)`.  Built on the existing distributive structure
    (`QuotAllegory.instDistributiveAllegory`, fed `amen.union_congr`).

    The two division laws use `quot_le_iff` (§2.533) via `.mp`/`.mpr`, relying on the
    defeq `(quotRep).map X = Quotient.mk _ X` so that the quotient `div`/`≫`/`⊑` of the
    `Quotient.lift₂` body match the `(quotRep).map …` form of `quot_le_iff`. -/
noncomputable def quotDiv : DivisionAllegory (QuotAllegory 𝒜 amen.cong) :=
  { QuotAllegory.instDistributiveAllegory amen.cong amen.union_congr with
    div := fun {a b c} => Quotient.lift₂
      (fun R S => (quotRep amen.cong).map (amen.largest R / amen.largest S))
      (by
        -- Well-defined: R ≡ R', S ≡ S' ⟹ R⁺ = R'⁺, S⁺ = S'⁺ (class-inv), so the
        -- representatives R⁺/S⁺ and R'⁺/S'⁺ are literally equal.
        intro R S R' S' hR hS
        have e1 : amen.largest R = amen.largest R' := amenable_largest_class_invariant amen hR
        have e2 : amen.largest S = amen.largest S' := amenable_largest_class_invariant amen hS
        simp only [e1, e2])
    div_comp_le := by
      -- (R̄/S̄)S̄ ⊑ R̄ :  [R⁺/S⁺][S] = [(R⁺/S⁺)≫S]; (R⁺/S⁺)≫S ⊑ (R⁺/S⁺)≫S⁺ ⊑ R⁺, so by
      -- §2.531 its ⁺ sits below (R⁺)⁺ = R⁺; conclude with quot_le_iff.
      intro a b c R S
      refine Quotient.inductionOn₂ R S (fun R S => ?_)
      -- (R⁺/S⁺)≫S ⊑ R⁺ :  S ⊑ S⁺, then the division law (R⁺/S⁺)≫S⁺ ⊑ R⁺.
      have hstep : (amen.largest R / amen.largest S) ≫ S ⊑ amen.largest R :=
        le_trans (comp_mono_left _ (le_largest_self amen S))
          (DivisionAllegory.div_comp_le (amen.largest R) (amen.largest S))
      -- ((R⁺/S⁺)≫S)⁺ ⊑ (R⁺)⁺ = R⁺.
      refine (quot_le_iff amen ((amen.largest R / amen.largest S) ≫ S) R).mpr ?_
      refine le_trans (amenable_le_largest amen hstep) ?_
      rw [largest_idem amen]; exact le_refl _
    le_div := by
      -- T̄S̄ ⊑ R̄ ⟹ T̄ ⊑ R̄/S̄ :  via quot_le_iff (TS)⁺ ⊑ R⁺; with §2.534 T⁺S⁺ ⊑ (TS)⁺ ⊑ R⁺,
      -- so T⁺ ⊑ R⁺/S⁺ ⊑ (R⁺/S⁺)⁺ = the largest of the RHS representative.
      intro a b c T R S h
      refine Quotient.inductionOn₃ T R S (fun T R S h => ?_) h
      -- h : [T][S] ⊑ [R];  convert to (T≫S)⁺ ⊑ R⁺.
      have h' : amen.largest (T ≫ S) ⊑ amen.largest R := (quot_le_iff amen (T ≫ S) R).mp h
      -- T⁺S⁺ ⊑ (TS)⁺ ⊑ R⁺  ⟹  T⁺ ⊑ R⁺/S⁺  ⟹  T⁺ ⊑ (R⁺/S⁺)⁺.
      have hTS : amen.largest T ≫ amen.largest S ⊑ amen.largest R :=
        le_trans (largest_comp_le amen T S) h'
      have hdiv : amen.largest T ⊑ amen.largest R / amen.largest S :=
        DivisionAllegory.le_div _ _ _ hTS
      exact (quot_le_iff amen T (amen.largest R / amen.largest S)).mpr
        (le_trans hdiv (le_largest_self amen _)) }

end Division

/-! ## Class-map descent helpers

  `quotRep` is a representation of allegories (`AllegoryFunctor`), so it preserves `dom`
  (and hence `Entire`/`Simple`/`Map`).  These let the §2.535 splitting and the §2.537
  thickness witness be *descended* from `𝒜` to the quotient. -/

section Descent
variable {𝒜 : Type u} [DistributiveAllegory 𝒜] (amen : AmenableCongruence 𝒜)

/-- `quotRep` preserves `dom`: `dom [R] = [dom R]`. -/
theorem quotRep_dom {a b : 𝒜} (R : a ⟶ b) :
    dom ((quotRep amen.cong).map R) = (quotRep amen.cong).map (dom R) := by
  dsimp [dom]
  rw [(quotRep amen.cong).map_inter, (quotRep amen.cong).map_comp,
    (quotRep amen.cong).map_recip, (quotRep amen.cong).map_id]

/-- `quotRep` preserves `Entire`: `[R]` entire when `R` is. -/
theorem quotRep_entire {a b : 𝒜} {R : a ⟶ b} (h : Entire R) :
    Entire ((quotRep amen.cong).map R) := by
  dsimp [Entire] at h ⊢
  rw [quotRep_dom, h, (quotRep amen.cong).map_id]

/-- `quotRep` preserves `Simple`: `[R]` simple when `R` is. -/
theorem quotRep_simple {a b : 𝒜} {R : a ⟶ b} (h : Simple R) :
    Simple ((quotRep amen.cong).map R) := by
  dsimp [Simple] at h ⊢
  rw [← (quotRep amen.cong).map_recip, ← (quotRep amen.cong).map_comp]
  -- [R°≫R] ⊑ [Cat.id b] = [R°≫R ∩ Cat.id b] = [R°≫R] (since R°≫R ⊑ Cat.id b).
  show (quotRep amen.cong).map (R° ≫ R) ∩ (quotRep amen.cong).map (Cat.id b) = _
  rw [← (quotRep amen.cong).map_inter]
  -- R°≫R ⊑ Cat.id b is `(R°≫R) ∩ Cat.id b = R°≫R`.
  rw [show (R° ≫ R) ∩ Cat.id b = R° ≫ R from h]

/-- `quotRep` preserves `Map`. -/
theorem quotRep_map_isMap {a b : 𝒜} {R : a ⟶ b} (h : Map R) :
    Map ((quotRep amen.cong).map R) :=
  ⟨quotRep_entire amen h.1, quotRep_simple amen h.2⟩

end Descent

/-! ## §2.535  Effectivity of the quotient

  A quotient equivalence relation `[E₀]` forces `E₀⁺` reflexive/symmetric/transitive
  (§2.535), hence an equivalence relation of `𝒜`, which splits by effectiveness of `𝒜`;
  the splitting `f₀` descends to `[f₀]` (`quotRep_map_isMap`), giving the quotient
  splitting. -/

section Effectivity
variable {𝒜 : Type u} [EffectivePowerAllegory 𝒜] (amen : AmenableCongruence 𝒜)

/-- §2.535: a quotient-reflexive `[E₀]` forces `E₀⁺` reflexive. -/
theorem quot_largest_reflexive {a : 𝒜} {E₀ : a ⟶ a}
    (h : Reflexive ((quotRep amen.cong).map E₀)) : Reflexive (amen.largest E₀) := by
  have h2 : (quotRep amen.cong).map (Cat.id a) ⊑ (quotRep amen.cong).map E₀ := by
    rw [(quotRep amen.cong).map_id]; exact h
  exact le_trans (le_largest_self amen (Cat.id a)) ((quot_le_iff amen (Cat.id a) E₀).mp h2)

/-- §2.535: a quotient-symmetric `[E₀]` forces `E₀⁺` symmetric. -/
theorem quot_largest_symmetric {a : 𝒜} {E₀ : a ⟶ a}
    (h : Symmetric ((quotRep amen.cong).map E₀)) : Symmetric (amen.largest E₀) := by
  have h2 : (quotRep amen.cong).map (E₀°) ⊑ (quotRep amen.cong).map E₀ := by
    rw [(quotRep amen.cong).map_recip]; exact h
  exact le_trans (largest_recip_le amen E₀) ((quot_le_iff amen (E₀°) E₀).mp h2)

/-- §2.535: a quotient-idempotent `[E₀]` (with `E₀⁺` reflexive) forces `E₀⁺` idempotent. -/
theorem quot_largest_idempotent {a : 𝒜} {E₀ : a ⟶ a}
    (hRefl : Reflexive (amen.largest E₀))
    (h : (quotRep amen.cong).map E₀ ≫ (quotRep amen.cong).map E₀ = (quotRep amen.cong).map E₀) :
    amen.largest E₀ ≫ amen.largest E₀ = amen.largest E₀ := by
  rw [← (quotRep amen.cong).map_comp] at h
  have hrel : amen.cong.rel (E₀ ≫ E₀) E₀ := Quotient.exact h
  have hcl : amen.largest (E₀ ≫ E₀) = amen.largest E₀ := amenable_largest_class_invariant amen hrel
  apply le_antisymm
  · have hle := largest_comp_le amen E₀ E₀
    rwa [hcl] at hle
  · have := comp_mono_right hRefl (amen.largest E₀)
    rwa [Cat.id_comp] at this

/-- §2.535: EVERY quotient equivalence relation splits — the quotient is effective.
    `E₀⁺` is a reflexive/symmetric/idempotent (equivalence) relation of `𝒜`, so it splits
    in `𝒜` (`EffectiveAllegory.split_symmetric_idempotent`); the leg `[f₀]` is a map
    (`quotRep_map_isMap`) and the two split equations descend. -/
theorem quotSplit {a : 𝒜} (E : (quotRep amen.cong).obj a ⟶ (quotRep amen.cong).obj a)
    (hR : Reflexive E) (hS : Symmetric E) (hI : E ≫ E = E) :
    ∃ (c : QuotAllegory 𝒜 amen.cong) (f : (quotRep amen.cong).obj a ⟶ c),
      Map f ∧ f ≫ f° = E ∧ f° ≫ f = Cat.id c := by
  refine Quotient.inductionOn E (fun E₀ => ?_) hR hS hI
  intro hR hS hI
  -- E₀⁺ is a reflexive, symmetric, idempotent equivalence relation of 𝒜.
  have hRefl' : Reflexive (amen.largest E₀) := quot_largest_reflexive amen hR
  have hSym' : Symmetric (amen.largest E₀) := quot_largest_symmetric amen hS
  have hIdem' : amen.largest E₀ ≫ amen.largest E₀ = amen.largest E₀ :=
    quot_largest_idempotent amen hRefl' hI
  obtain ⟨c, f₀, hf₀Map, hff, hffid⟩ :=
    EffectiveAllegory.split_symmetric_idempotent (amen.largest E₀) hRefl' hSym' hIdem'
  refine ⟨c, (quotRep amen.cong).map f₀, quotRep_map_isMap amen hf₀Map, ?_, ?_⟩
  · -- [f₀][f₀]° = [f₀f₀°] = [E₀⁺] = [E₀] = E.
    rw [← (quotRep amen.cong).map_recip, ← (quotRep amen.cong).map_comp, hff]
    exact Quotient.sound (amen.cong.symm (amen.largest_rel E₀))
  · -- [f₀]°[f₀] = [f₀°f₀] = [Cat.id c] = Cat.id c.
    rw [← (quotRep amen.cong).map_recip, ← (quotRep amen.cong).map_comp, hffid]
    exact (quotRep amen.cong).map_id c

end Effectivity

/-! ## §2.537  The membership `[∋_b]` is thick

  Following the book.  In `𝒜`, the membership `∋_b` is (box-guarded) thick (§2.41:
  `R/ₛ∋ = A(R)` is entire).  For a quotient relation `[R₀] : [c] → [b]` box-matched to
  `[∋_b]`, the book's inequality `1 ⊑ (R⁺/∋_R)(∋_R/R⁺) ⊑ (R⁺/∋_{R⁺}/R⁺)` is realised by
  applying `𝒜`-thickness to the largest `R₀⁺` and transporting the resulting witness
  `f₀ = A(R₀⁺)` to `[f₀]` via the ⁺-calculus.  The only non-derivable input is the box
  descent `codBox [R₀] = codBox [∋_b] ⟹ codBox R₀⁺ = codBox (∋_b)`, the book's
  "∋_R = ∋_{R⁺} [2.41]" — surfaced as a named hypothesis. -/

section Thickness
variable {𝒜 : Type u} [EffectivePowerAllegory 𝒜] (amen : AmenableCongruence 𝒜)

/-- `quotRep` preserves `codBox`: `codBox [R] = [codBox R]`. -/
theorem quotRep_codBox {a b : 𝒜} (R : a ⟶ b) :
    codBox ((quotRep amen.cong).map R) = (quotRep amen.cong).map (codBox R) := by
  show dom (((quotRep amen.cong).map R)°) = _
  rw [← (quotRep amen.cong).map_recip, quotRep_dom]

/-- §2.537 (the crux): the quotient membership `[∋_b]` is thick.

    `hbox` is the book's "∋_R = ∋_{R⁺} [2.41]" — a quotient box-match descends to an exact
    `𝒜`-box-match for the largest representative, the domain on which `𝒜`'s membership
    thickness is defined.  Given it, the witness for `thick_iff_existential` is `[f₀]` where
    `f₀ = A(R₀⁺)` comes from `𝒜`-thickness of `∋_b` applied to `R₀⁺`; the three quotient
    containments are read off from `f₀`'s three `𝒜`-containments through `quot_le_iff`
    (§2.533) and `amenable_le_largest` (§2.531). -/
theorem quotThickEps (b : 𝒜)
    (hbox : ∀ {c : 𝒜} (R₀ : c ⟶ b),
      amen.cong.rel (codBox R₀) (codBox (∋ b)) → codBox (amen.largest R₀) = codBox (∋ b)) :
    letI := quotDiv amen
    Thick ((quotRep amen.cong).map (∋ b)) := by
  letI := quotDiv amen
  rw [thick_iff_existential]
  intro c R hboxQ
  refine Quotient.inductionOn R (fun R₀ => ?_) hboxQ
  intro hboxQ
  -- Descend the quotient box-match to `codBox R₀ ≡ codBox (∋ b)`, then to the exact
  -- `𝒜`-box-match for `R₀⁺`.
  rw [← quotRep_map amen.cong R₀, quotRep_codBox, quotRep_codBox] at hboxQ
  have hrelBox : amen.cong.rel (codBox R₀) (codBox (∋ b)) := Quotient.exact hboxQ
  have hboxA : codBox (amen.largest R₀) = codBox (∋ b) := hbox R₀ hrelBox
  -- 𝒜-thickness of ∋_b applied to R₀⁺ gives the witness f₀ = A(R₀⁺).
  obtain ⟨f₀, hEnt, hf₀_le, hf₀o⟩ :=
    (thick_iff_existential (∋ b)).mp (fun _ R hbox => (A_is_map R hbox).1)
      c (amen.largest R₀) hboxA
  refine ⟨(quotRep amen.cong).map f₀, quotRep_entire amen hEnt, ?_, ?_⟩
  · -- [f₀][∋] ⊑ [R₀] :  largest(f₀∋) ⊑ largest(R₀⁺) = R₀⁺ = largest R₀  (§2.531).
    refine (quot_le_iff amen (f₀ ≫ ∋ b) R₀).mpr ?_
    have h := amenable_le_largest amen hf₀_le
    rwa [largest_idem amen] at h
  · -- [f₀]°[R₀] ⊑ [∋] :  R₀ ≡ R₀⁺ ⟹ largest(f₀°R₀)=largest(f₀°R₀⁺) ⊑ largest(∋)  (§2.531).
    refine (quot_le_iff amen (f₀° ≫ R₀) (∋ b)).mpr ?_
    have hcong : amen.cong.rel (f₀° ≫ R₀) (f₀° ≫ amen.largest R₀) :=
      amen.cong.comp_congr (amen.cong.refl _) (amen.largest_rel R₀)
    rw [amenable_largest_class_invariant amen hcong]
    exact amenable_le_largest amen hf₀o

end Thickness

/-! ## §2.537  Assembly: the quotient is an (effective) pre-power, hence a power allegory

  Combine layers 1–3 into an `EffectivePrePowerAllegory (QuotAllegory 𝒜 amen.cong)`, then
  apply `effective_pre_power_is_power` (§2.432).  Two named hypotheses remain (documented
  at each):  `htab` (§2.51, quotient tabularity) and `hbox` (§2.41, the membership
  box-naming "∋_R = ∋_{R⁺}"). -/

section Assembly
variable {𝒜 : Type u} [EffectivePowerAllegory 𝒜] (amen : AmenableCongruence 𝒜)

/-- The §2.537 box-naming hypothesis bundled per object (the book's "∋_R = ∋_{R⁺} [2.41]").
    For every object `b` and relation `R₀` targeted at `b`, a quotient box-match descends to
    an exact `𝒜`-box-match for the largest representative `R₀⁺`. -/
def QuotBoxNaming : Prop :=
  ∀ (b : 𝒜) {c : 𝒜} (R₀ : c ⟶ b),
    amen.cong.rel (codBox R₀) (codBox (∋ b)) → codBox (amen.largest R₀) = codBox (∋ b)

/-- §2.535 + §2.536 + §2.537: the amenable quotient of an effective power allegory is an
    EFFECTIVE PRE-POWER ALLEGORY.

    Quotient-tabularity (§2.51) is now discharged unconditionally: every `R : a ⟶ b` is
    tabular in the effective base (`TabularAllegory.tabular`), and `quotRep_preserves_tabular`
    carries that to `[R]`.  The *splitting* half of effectivity (§2.535) is the proven
    `quotSplit`.  The one remaining named book step is

    `hbox`  — §2.41 membership box-naming `∋_R = ∋_{R⁺}` (`QuotBoxNaming`). -/
noncomputable def quotEffectivePrePower
    (hbox : QuotBoxNaming amen) :
    EffectivePrePowerAllegory (QuotAllegory 𝒜 amen.cong) :=
  { quotDiv amen with
    tabular := fun {_ _} R => Quotient.inductionOn R
      (fun R₀ => quotRep_preserves_tabular amen.cong (TabularAllegory.tabular R₀))
    split_symmetric_idempotent := fun {_a} E hR hS hI => quotSplit amen E hR hS hI
    thick_target := fun b =>
      -- `powerObj`/`∋` are taken in `𝒜` (the syntactic quotient object `b` would otherwise
      -- send instance resolution looking for the very `PowerAllegory` we are building).
      ⟨@PowerAllegory.powerObj 𝒜 _ b, (quotRep amen.cong).map (@PowerAllegory.eps 𝒜 _ b),
        quotThickEps amen b (hbox b)⟩ }

/-- §2.537 (HEADLINE): **An amenable quotient of an effective power allegory is an effective
    power allegory.**  Conditional on the single named book step `hbox` (§2.41 membership
    box-naming); everything else — §2.51 quotient-tabularity, §2.536 division, §2.535
    splitting, and the §2.537 thickness inequality — is unconditional.  Produced from
    `quotEffectivePrePower` via §2.432 `effective_pre_power_is_power`. -/
noncomputable def quot_effective_power_is_power
    (hbox : QuotBoxNaming amen) :
    PowerAllegory (QuotAllegory 𝒜 amen.cong) :=
  @effective_pre_power_is_power _ (quotEffectivePrePower amen hbox)

end Assembly

/-! ## §2.537  Unconditional over an UNGUARDED base — the `hbox` is FREE

  The §2.41 box-naming `hbox` is needed only to box-match the largest representative `R₀⁺`
  for the BASE membership's box-matched thickness (§2.431).  If the base is an UNGUARDED power
  allegory (Freyd §2.412/§2.413 — `∋` classifies EVERY `R`, the form genuine examples like
  `Rel(C)` of a topos satisfy), that box-match is unnecessary: `eps_thick_all` classifies
  `R₀⁺` for any box.  So over `EffectiveUnguardedPowerAllegory` §2.537 is UNCONDITIONAL. -/

/-- An EFFECTIVE UNGUARDED power allegory: effective + the full (unguarded) §2.41 membership
    (`∋` classifies every relation).  One `Allegory` base (structure inheritance). -/
class EffectiveUnguardedPowerAllegory (𝒜 : Type u) extends
    EffectivePowerAllegory 𝒜, UnguardedPowerAllegory 𝒜

section UnguardedAssembly
variable {𝒜 : Type u} [EffectiveUnguardedPowerAllegory 𝒜] (amen : AmenableCongruence 𝒜)

/-- §2.537 over an unguarded base: the quotient membership `[∋_b]` is thick — `hbox`-free.
    The witness `[f₀]` comes from the UNGUARDED thickness `eps_thick_all` applied to `R₀⁺`
    (a map with `f₀ ∋ = R₀⁺`); the two quotient containments are read off exactly as in
    `quotThickEps` via `quot_le_iff`/`amenable_le_largest`/`largest_idem`. -/
theorem quotThickEps_unguarded (b : 𝒜) :
    letI := quotDiv amen
    Thick ((quotRep amen.cong).map (∋ b)) := by
  letI := quotDiv amen
  rw [thick_iff_existential]
  intro c R _hboxQ
  refine Quotient.inductionOn R (fun R₀ => ?_) _hboxQ
  intro _
  obtain ⟨f₀, hf₀map, hf₀eq⟩ := UnguardedPowerAllegory.eps_thick_all (b := b) (amen.largest R₀)
  have hf₀_le : f₀ ≫ ∋ b ⊑ amen.largest R₀ := by rw [hf₀eq]; exact le_refl _
  have hf₀o : f₀° ≫ amen.largest R₀ ⊑ ∋ b := by
    rw [← hf₀eq, ← Cat.assoc]
    have h := comp_mono_right hf₀map.2 (∋ b); rwa [Cat.id_comp] at h
  refine ⟨(quotRep amen.cong).map f₀, quotRep_entire amen hf₀map.1, ?_, ?_⟩
  · refine (quot_le_iff amen (f₀ ≫ ∋ b) R₀).mpr ?_
    have h := amenable_le_largest amen hf₀_le
    rwa [largest_idem amen] at h
  · refine (quot_le_iff amen (f₀° ≫ R₀) (∋ b)).mpr ?_
    have hcong : amen.cong.rel (f₀° ≫ R₀) (f₀° ≫ amen.largest R₀) :=
      amen.cong.comp_congr (amen.cong.refl _) (amen.largest_rel R₀)
    rw [amenable_largest_class_invariant amen hcong]
    exact amenable_le_largest amen hf₀o

/-- §2.537 (unguarded): the amenable quotient is an effective pre-power allegory — no `hbox`. -/
noncomputable def quotEffectivePrePower_unguarded :
    EffectivePrePowerAllegory (QuotAllegory 𝒜 amen.cong) :=
  { quotDiv amen with
    tabular := fun {_ _} R => Quotient.inductionOn R
      (fun R₀ => quotRep_preserves_tabular amen.cong (TabularAllegory.tabular R₀))
    split_symmetric_idempotent := fun {_a} E hR hS hI => quotSplit amen E hR hS hI
    thick_target := fun b =>
      ⟨@PowerAllegory.powerObj 𝒜 _ b, (quotRep amen.cong).map (@PowerAllegory.eps 𝒜 _ b),
        quotThickEps_unguarded amen b⟩ }

/-- **§2.537 (unconditional)**: an amenable quotient of an effective UNGUARDED power allegory
    is a power allegory — `hbox`-free (the §2.41 box-naming is automatic when `∋` is unguarded). -/
noncomputable def quot_effective_power_is_power_unguarded :
    PowerAllegory (QuotAllegory 𝒜 amen.cong) :=
  @effective_pre_power_is_power _ (quotEffectivePrePower_unguarded amen)

end UnguardedAssembly

end Freyd.Alg
