/-
  Freyd & Scedrov, *Categories and Allegories* §2.433 — the `SplObj`-level wrapper.

  §2.433  If `𝒜` is a pre-power allegory and `Eq` its class of equivalence relations,
          then `Spl(Eq 𝒜)` is a power allegory.

  This file packages the carrier-level core of `Fredy.S2_433_SplEqPower`
  (`splEq_chain1`, `splEq_chain2`) into the `SplObj 𝒜` ("split" allegory) API: for an
  *equivalence-relation* object `E` of `SplObj 𝒜` (one whose idempotent `E.idem.e` is
  REFLEXIVE) and a base thick morphism `T : x → E.carrier` of `𝒜`, the split-hom

        S = splEqTarget : embObj x ⟶ E,   S.R = T ≫ E.idem.e

  is THICK in `SplObj 𝒜`.  For a test `R : Q ⟶ E` (so `Q.idem.e ≫ R.R ≫ E.idem.e = R.R`)
  the `thick_iff_existential` witness is

        R̂ = Q.idem.e ≫ (R.R /ₛ T)        (the carrier-level §2.433 witness),

  with its three properties read off the core:
    • `Entire R̂` (SplObj) — proved directly: `1 ⊑ (R.R/ₛT)(R.R/ₛT)°` (box-matched
      thickness of `T`) sandwiched by the source idempotent `Q.idem.e`.  This needs only
      that `Q` is a symmetric idempotent — NOT that the test source is reflexive — which
      is why the bundled `splEq_thick_witness` (whose Entire demands a reflexive source)
      is sidestepped in favour of `splEq_chain1`/`splEq_chain2` + this direct Entire.
    • `R̂ ≫ S ⊑ R`  —  exactly `splEq_chain1`.
    • `R̂° ≫ R ⊑ S` —  exactly `splEq_chain2` (uses the TARGET reflexivity `1 ⊑ E.idem.e`).

  The construction depends on the TARGET being reflexive, never the test source.  The
  box-matching `codBox_{SplObj} R = codBox_{SplObj} S ⟹ codBox_{𝒜} R.R = codBox_{𝒜} T`
  is carried as the named hypothesis `hbox`, exactly Freyd's §2.41 box index "∋_R = ∋_{R□}"
  (the same device as §2.537 `QuotBoxNaming`); it is codBox bookkeeping, not thickness.

  SCOPE.  This is the §2.433 content for the EQUIVALENCE-RELATION objects of `SplObj 𝒜`.
  A FULL `PrePowerAllegory (SplObj 𝒜)` instance is NOT produced: `SplObj 𝒜` splits ALL
  symmetric idempotents, including PER/coreflexive (non-reflexive) objects, which have no
  thick target by this construction — Freyd's `Spl(Eq 𝒜)` is precisely the reflexive-only
  subobject type.  `splEqTarget_thick` below is the reusable core for that subtype.
-/

import Fredy.S2_433_SplEqPower
import Fredy.Spl

universe u

namespace Freyd.Alg

section Core
variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- The §2.433 thick target of an equivalence-relation object `E` of `SplObj 𝒜`: from a
    base thick `T : x → E.carrier` of `𝒜`, the split-hom `embObj x ⟶ E` with underlying
    morphism `T ≫ E.idem.e` (fixed because `embObj x` carries the identity idempotent on
    the source and `E.idem.e` is idempotent on the target). -/
def splEqTarget (E : SplObj 𝒜) {x : 𝒜} (T : x ⟶ E.carrier) :
    embObj x ⟶ E :=
  ⟨T ≫ E.idem.e, by
    show Cat.id x ≫ (T ≫ E.idem.e) ≫ E.idem.e = T ≫ E.idem.e
    rw [Cat.id_comp, Cat.assoc, E.idem.idem]⟩

@[simp] theorem splEqTarget_R (E : SplObj 𝒜) {x : 𝒜} (T : x ⟶ E.carrier) :
    (splEqTarget E T).R = T ≫ E.idem.e := rfl

/-- The §2.433 box-naming side condition for an equivalence-relation object `E` of
    `SplObj 𝒜` (Freyd's §2.41 box index "∋_R = ∋_{R□}", the §2.537 `QuotBoxNaming` analogue):
    for every base `T : x → E.carrier` and test `R : Q ⟶ E`, a `SplObj` box-match
    `codBox R = codBox (splEqTarget E T)` descends to the exact `𝒜` box-match
    `codBox R.R = codBox T` (the domain on which `𝒜`-thickness of `T` is defined).  It is
    codBox bookkeeping; it does NOT assume thickness, and it is discharged automatically for
    the embedded objects (`splEq_embObj_thick`). -/
def SplEqBoxNaming (E : SplObj 𝒜) : Prop :=
  ∀ {x : 𝒜} (T : x ⟶ E.carrier) {Q : SplObj 𝒜} (R : Q ⟶ E),
    codBox R = codBox (splEqTarget E T) → codBox R.R = codBox T

/-- **§2.433 (the `SplObj` wrapper).**  For an EQUIVALENCE-RELATION object `E` of
    `SplObj 𝒜` (idempotent reflexive, `1 ⊑ E.idem.e`) and a base thick `T : x → E.carrier`
    of `𝒜`, the target `S = splEqTarget E T : embObj x ⟶ E` (underlying `T ≫ E.idem.e`) is
    THICK in `SplObj 𝒜`.

    For a test `R : Q ⟶ E` the witness for `thick_iff_existential` is
    `R̂ = Q.idem.e ≫ (R.R /ₛ T)`, the carrier-level §2.433 witness; its three properties
    come from `splEq_chain1`, `splEq_chain2`, and a direct `SplObj`-Entire argument.

    `hbox` is Freyd's §2.41 box index (the §2.537 `QuotBoxNaming` device): a `SplObj`
    box-match `codBox R = codBox S` descends to the exact `𝒜` box-match
    `codBox R.R = codBox T` on which `𝒜`-thickness of `T` is defined.  It is codBox
    bookkeeping, not a thickness assumption. -/
theorem splEqTarget_thick (E : SplObj 𝒜) (hErefl : Cat.id E.carrier ⊑ E.idem.e)
    {x : 𝒜} (T : x ⟶ E.carrier) (hThickT : Thick T) (hbox : SplEqBoxNaming E) :
    Thick (splEqTarget E T) := by
  rw [thick_iff_existential]
  intro Q R hboxQ
  -- Descend the `SplObj` box-match to the exact `𝒜` box-match, then `𝒜`-thickness of `T`.
  have hbox𝒜 : codBox R.R = codBox T := hbox T R hboxQ
  have hent : Entire (R.R /ₛ T) := hThickT Q.carrier R.R hbox𝒜
  -- The witness `R̂ : Q ⟶ embObj x`, underlying `Q.idem.e ≫ (R.R /ₛ T)`.
  refine ⟨⟨Q.idem.e ≫ (R.R /ₛ T), ?_⟩, ?_, ?_, ?_⟩
  · -- fixed: `Q.idem.e ≫ (Q.idem.e ≫ (R.R/ₛT)) ≫ 1_x = Q.idem.e ≫ (R.R/ₛT)`.
    show Q.idem.e ≫ (Q.idem.e ≫ (R.R /ₛ T)) ≫ Cat.id x = Q.idem.e ≫ (R.R /ₛ T)
    rw [Cat.comp_id, ← Cat.assoc, Q.idem.idem]
  · -- `Entire R̂` (SplObj): `Q.idem.e ∩ (Q.idem.e≫F)(Q.idem.e≫F)° = Q.idem.e`, `F = R.R/ₛT`.
    unfold Entire dom; apply SplHom.ext
    show Q.idem.e ∩ (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))° = Q.idem.e
    have hFF : (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))°
        = Q.idem.e ≫ ((R.R /ₛ T) ≫ (R.R /ₛ T)°) ≫ Q.idem.e := by
      rw [Allegory.recip_comp, Q.idem.sym]; simp only [Cat.assoc]
    have hFFent : Cat.id Q.carrier ⊑ (R.R /ₛ T) ≫ (R.R /ₛ T)° := by
      have h := hent; unfold Entire dom at h; exact h ▸ inter_lb_right _ _
    have hge : Q.idem.e ⊑ (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))° := by
      rw [hFF]
      calc Q.idem.e = Q.idem.e ≫ Cat.id Q.carrier ≫ Q.idem.e := by rw [Cat.id_comp, Q.idem.idem]
        _ ⊑ Q.idem.e ≫ ((R.R /ₛ T) ≫ (R.R /ₛ T)°) ≫ Q.idem.e :=
            comp_mono_left _ (comp_mono_right hFFent _)
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hge)
  · -- `R̂ ≫ S ⊑ R`:  underlying `(Q.idem.e≫(R.R/ₛT)) ≫ (T≫E.idem.e) ⊑ R.R` = `splEq_chain1`.
    rw [splLe_iff]
    show (Q.idem.e ≫ (R.R /ₛ T)) ≫ (T ≫ E.idem.e) ⊑ R.R
    exact splEq_chain1 E.idem.e Q.idem.e T R.R R.fixed
  · -- `R̂° ≫ R ⊑ S`:  underlying `(Q.idem.e≫(R.R/ₛT))° ≫ R.R ⊑ T≫E.idem.e` = `splEq_chain2`.
    rw [splLe_iff]
    show (Q.idem.e ≫ (R.R /ₛ T))° ≫ R.R ⊑ T ≫ E.idem.e
    exact splEq_chain2 E.idem.e Q.idem.e T R.R hErefl Q.idem.sym Q.idem.idem R.fixed

/-- **§2.433 (thick target, existence form).**  Every equivalence-relation object `E` of
    `SplObj 𝒜` is the target of a THICK split-hom, given a base thick `T : x → E.carrier`
    of `𝒜` and the §2.41 box-naming `hbox`.  The witness object is `embObj x` and the witness
    morphism is `splEqTarget E T`.  This is the `PrePowerAllegory.thick_target`-shaped
    statement, restricted to the reflexive (equivalence-relation) objects of `SplObj 𝒜`. -/
theorem splEq_thick_target (E : SplObj 𝒜) (hErefl : Cat.id E.carrier ⊑ E.idem.e)
    {x : 𝒜} (T : x ⟶ E.carrier) (hThickT : Thick T) (hbox : SplEqBoxNaming E) :
    ∃ (P : SplObj 𝒜) (S : P ⟶ E), Thick S :=
  ⟨embObj x, splEqTarget E T, splEqTarget_thick E hErefl T hThickT hbox⟩

/-- **Non-vacuity of `SplEqBoxNaming`.**  For an EMBEDDED object `embObj a` (identity
    idempotent `1_a`), the box-naming is DISCHARGED: `SplObj`-`codBox` collapses to the base
    `𝒜`-`codBox` (no `E.idem.e` to weaken it), and `splEqTarget (embObj a) T` has underlying
    `T ≫ 1_a = T`.  So the hypothesis `hbox` of `splEqTarget_thick` is genuinely satisfiable
    (it is codBox bookkeeping, not the thickness conclusion in disguise). -/
theorem splEq_embObj_boxNaming (a : 𝒜) : SplEqBoxNaming (embObj a) := by
  intro x T Q R hboxQ
  -- For the embedded target the underlying `SplObj`-`codBox` IS the `𝒜`-`codBox`.
  have h : codBox R.R = codBox ((splEqTarget (embObj a) T).R) := congrArg SplHom.R hboxQ
  simpa only [splEqTarget_R, embObj, idSymIdem, Cat.comp_id] using h

/-- **§2.433 (embedded case, `hbox`-free).**  For an embedded object `embObj a` and a base
    thick `T : x → a` of `𝒜`, the split-hom `splEqTarget (embObj a) T` is THICK in `SplObj 𝒜`
    with NO box-naming hypothesis — here `splEqTarget (embObj a) T` is just `embHom T` and the
    `SplObj` thickness reduces verbatim to the `𝒜` thickness of `T`. -/
theorem splEq_embObj_thick (a : 𝒜) {x : 𝒜} (T : x ⟶ a) (hThickT : Thick T) :
    Thick (splEqTarget (embObj a) T) :=
  splEqTarget_thick (embObj a) (le_refl _) T hThickT (splEq_embObj_boxNaming a)

end Core

section PrePower
-- ONLY `[PrePowerAllegory 𝒜]` here: a second ambient `[DivisionAllegory 𝒜]` would create an
-- instance diamond (two distinct `Cat.Hom` on `𝒜`), so `DivisionAllegory 𝒜` is resolved
-- through the single parent projection `PrePowerAllegory.toDivisionAllegory`.
variable {𝒜 : Type u} [PrePowerAllegory 𝒜]

/-- **§2.433 (thick target from a pre-power base).**  When `𝒜` is a `PrePowerAllegory`, the
    base thick `T : x → E.carrier` is sourced from `PrePowerAllegory.thick_target`, so every
    equivalence-relation object `E` of `SplObj 𝒜` has a thick target under the §2.41
    box-naming `SplEqBoxNaming E`.  Exercises the instance path `PrePowerAllegory 𝒜 →
    DivisionAllegory 𝒜 → instDivisionSpl`, i.e. `DivisionAllegory (SplObj 𝒜)`, used by
    `Thick` on `SplObj 𝒜`. -/
theorem splEq_thick_target_of_prePower [PrePowerAllegory 𝒜]
    (E : SplObj 𝒜) (hErefl : Cat.id E.carrier ⊑ E.idem.e)
    (hbox : SplEqBoxNaming E) :
    ∃ (P : SplObj 𝒜) (S : P ⟶ E), Thick S := by
  obtain ⟨x, T, hThickT⟩ := PrePowerAllegory.thick_target E.carrier
  exact splEq_thick_target E hErefl T hThickT hbox

end PrePower

end Freyd.Alg
