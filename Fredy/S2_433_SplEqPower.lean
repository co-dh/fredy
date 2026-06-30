/-
  Freyd & Scedrov, *Categories and Allegories* §2.433.

  §2.433  If `𝒜` is a pre-power allegory and `Eq` its class of equivalence
          relations, then `Spl(Eq 𝒜)` is a power allegory.

  BECAUSE (Freyd): by §2.432 (`effective_pre_power_is_power`, already in the repo)
  it suffices that `Spl(Eq 𝒜)` is a pre-power allegory (it is automatically
  effective, §2.169).  Given an equivalence-relation object `E` of `Spl(Eq 𝒜)`,
  let `T` be a thick morphism of `𝒜` with `T□ = E□`.  Then the morphism `T ≫ E`
  into `E` is THICK in `Spl(Eq 𝒜)`: for a test `R : E' → E` (so `R` is fixed by
  the source/target equivalence relations, `E' ≫ R ≫ E = R`) the witness is

        R̂  =  E' ≫ (R /ₛ T)        (SYMMETRIC division — the OCR'd `R/T`)

  which is *clearly entire* because `R /ₛ T` is entire (`T` thick, box-matched)
  and `E'` is entire (a reflexive symmetric idempotent), and which satisfies the
  two thickness containments

        R̂ ≫ (T ≫ E)  ⊑  R        (`chain1`)
        R̂° ≫ R       ⊑  T ≫ E    (`chain2`)

  Both are pure division-allegory algebra.  `chain1` uses `(R/ₛT)≫T ⊑ R` (the
  first `le_symmDiv_iff` component) and the fixing `E'RE = R`.  `chain2` uses
  `(R/ₛT)°≫R ⊑ T` (the *second* `le_symmDiv_iff` component) — which is exactly the
  defining property of symmetric division, dissolving Freyd's roundabout
  `(R̂°R ⊑ (T/R)E'R ⊑ (T/R)RE ⊑ TE)` chain — together with `E'R = R` and `E`
  reflexive.

  This file proves the carrier-level CORE (`splEq_thick_witness` and its three
  components), which IS the §2.433 BECAUSE: it produces the
  `thick_iff_existential` witness `R̂` for the morphism `T ≫ E` against any fixed
  test `R`.  The packaging of this into the `SplObj`-level `PrePowerAllegory`
  instance (then `PowerAllegory` via §2.432) is the remaining `SplObj`-API wiring.
-/

import Fredy.S2_4

universe u

namespace Freyd.Alg

section SplEqCore
variable {𝒜 : Type u} [DivisionAllegory 𝒜] {x a b : 𝒜}

/-- A morphism fixed on the left by an idempotent is absorbed by it: if
    `E' ≫ R ≫ E = R` and `E'` is idempotent then `E' ≫ R = R`. -/
theorem fix_absorb_left (E' : b ⟶ b) (E : a ⟶ a) (R : b ⟶ a)
    (hE'_idem : E' ≫ E' = E') (hfix : E' ≫ R ≫ E = R) : E' ≫ R = R := by
  calc E' ≫ R = E' ≫ (E' ≫ R ≫ E) := by rw [hfix]
    _ = (E' ≫ E') ≫ R ≫ E := by simp only [Cat.assoc]
    _ = E' ≫ R ≫ E := by rw [hE'_idem]
    _ = R := hfix

/-- A reflexive symmetric idempotent (an equivalence relation) is ENTIRE.
    `dom E = 1 ∩ E≫E° = 1 ∩ E = 1` (symmetric, idempotent, reflexive). -/
theorem equiv_entire (E : b ⟶ b)
    (hrefl : Cat.id b ⊑ E) (hsym : E° = E) (hidem : E ≫ E = E) : Entire E := by
  show Cat.id b ∩ E ≫ E° = Cat.id b
  rw [hsym, hidem]; exact inter_eq_left hrefl

/-- **§2.433 (chain 1).**  `R̂ ≫ (T ≫ E) ⊑ R`, where `R̂ = E' ≫ (R /ₛ T)`.
    `E'(R/ₛT)TE ⊑ E'RE = R`, using `(R/ₛT)≫T ⊑ R` and the fixing `E'RE = R`. -/
theorem splEq_chain1 (E : a ⟶ a) (E' : b ⟶ b) (T : x ⟶ a) (R : b ⟶ a)
    (hfix : E' ≫ R ≫ E = R) :
    (E' ≫ (R /ₛ T)) ≫ (T ≫ E) ⊑ R := by
  have h1 : (R /ₛ T) ≫ T ⊑ R := ((le_symmDiv_iff (R /ₛ T) R T).mp (le_refl _)).1
  calc (E' ≫ (R /ₛ T)) ≫ (T ≫ E)
      = E' ≫ ((R /ₛ T) ≫ T) ≫ E := by simp only [Cat.assoc]
    _ ⊑ E' ≫ R ≫ E := comp_mono_left _ (comp_mono_right h1 E)
    _ = R := hfix

/-- **§2.433 (chain 2).**  `R̂° ≫ R ⊑ T ≫ E`.  `R̂° = (R/ₛT)° ≫ E'`, so
    `R̂°R = (R/ₛT)° ≫ E' ≫ R = (R/ₛT)° ≫ R ⊑ T ⊑ T ≫ E`, using `(R/ₛT)°≫R ⊑ T`
    (second `le_symmDiv_iff` component), `E'R = R`, and `E` reflexive. -/
theorem splEq_chain2 (E : a ⟶ a) (E' : b ⟶ b) (T : x ⟶ a) (R : b ⟶ a)
    (hErefl : Cat.id a ⊑ E) (hE'_sym : E'° = E') (hE'_idem : E' ≫ E' = E')
    (hfix : E' ≫ R ≫ E = R) :
    (E' ≫ (R /ₛ T))° ≫ R ⊑ T ≫ E := by
  have h2 : (R /ₛ T)° ≫ R ⊑ T := ((le_symmDiv_iff (R /ₛ T) R T).mp (le_refl _)).2
  have hE'R : E' ≫ R = R := fix_absorb_left E' E R hE'_idem hfix
  have hTE : T ⊑ T ≫ E := by have h := comp_mono_left T hErefl; rwa [Cat.comp_id] at h
  have key : (E' ≫ (R /ₛ T))° ≫ R = (R /ₛ T)° ≫ R := by
    rw [Allegory.recip_comp, Cat.assoc, hE'_sym, hE'R]
  rw [key]; exact le_trans h2 hTE

/-- **§2.433 (the thickness witness, BECAUSE).**  For an equivalence-relation
    object `E` (reflexive symmetric idempotent), its companion source equivalence
    relation `E'`, a thick `T` of `𝒜` box-matched to `E` (so `R /ₛ T` is entire
    for the fixed test `R`), and a test `R : E' → E` fixed by `E', E`
    (`E' ≫ R ≫ E = R`), the morphism `R̂ = E' ≫ (R /ₛ T)` is an ENTIRE witness
    realizing the thickness of `T ≫ E` against `R`:
      `Entire R̂`,  `R̂ ≫ (T ≫ E) ⊑ R`,  `R̂° ≫ R ⊑ T ≫ E`.
    This is precisely the `thick_iff_existential` body (§2.431) for `T ≫ E`. -/
theorem splEq_thick_witness (E : a ⟶ a) (E' : b ⟶ b) (T : x ⟶ a) (R : b ⟶ a)
    (hErefl : Cat.id a ⊑ E)
    (hE'refl : Cat.id b ⊑ E') (hE'_sym : E'° = E') (hE'_idem : E' ≫ E' = E')
    (hfix : E' ≫ R ≫ E = R) (hent : Entire (R /ₛ T)) :
    Entire (E' ≫ (R /ₛ T)) ∧
    (E' ≫ (R /ₛ T)) ≫ (T ≫ E) ⊑ R ∧
    (E' ≫ (R /ₛ T))° ≫ R ⊑ T ≫ E :=
  ⟨entire_comp (equiv_entire E' hE'refl hE'_sym hE'_idem) hent,
   splEq_chain1 E E' T R hfix,
   splEq_chain2 E E' T R hErefl hE'_sym hE'_idem hfix⟩

end SplEqCore

end Freyd.Alg
