/-
  Freyd & Scedrov, *Categories and Allegories* — §2.433: the REFLEXIVE splitting
  completion `Spl(Eq 𝒜)`.

  `SplEqObj 𝒜 = { E : SplObj 𝒜 // Cat.id E.carrier ⊑ E.idem.e }` restricts `SplObj 𝒜`
  to the objects whose symmetric idempotent is REFLEXIVE — i.e. the EQUIVALENCE
  RELATIONS of `𝒜`.  This is the reflexive analogue of the COREFLEXIVE sub-completion
  `SplCorObj 𝒜` (§2.34 / S2_165_Spl); homs are again the underlying `SplObj`-homs
  `SplHom E.1 F.1`, so `Cat`/`Allegory`/`Distributive`/`Division` all descend pointwise
  via `SplHom.ext`, byte-for-byte as for `SplCorObj`.

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, intersection
  `R ∩ S`, order `R ⊑ S`.  Mathlib-free.
-/
import Fredy.S2_43
import Fredy.S2_4

universe v u

namespace Freyd.Alg

open Cat

/-- The REFLEXIVE splitting completion of `𝒜`: restrict `SplObj 𝒜` to objects whose
    symmetric idempotent `E.idem.e` is REFLEXIVE (`Cat.id E.carrier ⊑ E.idem.e`), i.e.
    the EQUIVALENCE RELATIONS of `𝒜`.  This is Freyd's `Spl(Eq 𝒜)` (§2.433): split only
    the reflexive symmetric idempotents (equivalence relations).  The reflexive dual of
    `SplCorObj 𝒜` (§2.34), which splits only the coreflexives. -/
def SplEqObj (𝒜 : Type u) [Allegory 𝒜] : Type u :=
  { E : SplObj 𝒜 // Cat.id E.carrier ⊑ E.idem.e }

namespace SplEqObj

variable {𝒜 : Type u} [Allegory 𝒜]

/-- Category structure on `SplEqObj 𝒜`: homs and composition inherited from `SplObj 𝒜`. -/
instance instCatSplEq : Cat (SplEqObj 𝒜) where
  Hom E F     := SplHom E.1 F.1
  id E        := splId E.1
  comp R S    := splComp R S
  id_comp R   := SplHom.ext R.fixed_left
  comp_id R   := SplHom.ext R.fixed_right
  assoc R S T := SplHom.ext (Cat.assoc _ _ _)

/-- Allegory structure on `SplEqObj 𝒜`: reciprocation and intersection inherited
    from `SplObj 𝒜`; all axioms reduce to the underlying `𝒜` axioms via `SplHom.ext`. -/
instance instAllegorySplEq : Allegory (SplEqObj 𝒜) where
  recip R             := splRecip R
  inter R S           := splInter R S
  recip_recip R       := SplHom.ext (Allegory.recip_recip _)
  recip_comp R S      := SplHom.ext (Allegory.recip_comp _ _)
  recip_inter R S     := SplHom.ext (Allegory.recip_inter _ _)
  inter_idem R        := SplHom.ext (Allegory.inter_idem _)
  inter_comm R S      := SplHom.ext (Allegory.inter_comm _ _)
  inter_assoc R S T   := SplHom.ext (Allegory.inter_assoc _ _ _)
  semidistrib R S T   := SplHom.ext (Allegory.semidistrib _ _ _)
  modular R S T       := SplHom.ext (Allegory.modular _ _ _)

end SplEqObj

/-- Order on `SplEqObj 𝒜` is read off the underlying `𝒜`-morphisms (the reflexive analogue
    of `splCorLe_iff`): `Φ ⊑ Ψ ↔ Φ.R ⊑ Ψ.R`. -/
theorem splEqLe_iff {𝒜 : Type u} [Allegory 𝒜] {E F : SplEqObj 𝒜} (Φ Ψ : E ⟶ F) :
    Φ ⊑ Ψ ↔ Φ.R ⊑ Ψ.R := by
  show splInter Φ Ψ = Φ ↔ Φ.R ∩ Ψ.R = Φ.R
  exact ⟨fun h => congrArg SplHom.R h, fun h => SplHom.ext h⟩

/-- **§2.21 (reflexive)**: if `𝒜` is distributive then so is `Spl(Eq 𝒜)`, with union and
    zero taken pointwise (`splUnion`, `splZero`).  Each law descends via `SplHom.ext`. -/
instance instDistributiveSplEq {𝒜 : Type u} [DistributiveAllegory 𝒜] :
    DistributiveAllegory (SplEqObj 𝒜) :=
  { SplEqObj.instAllegorySplEq with
    zero := splZero
    union := splUnion
    zero_comp := fun R => by
      apply SplHom.ext; show (𝟘 : _ ⟶ _) ≫ R.R = 𝟘; exact DistributiveAllegory.zero_comp _
    comp_zero := fun R => by
      apply SplHom.ext; show R.R ≫ (𝟘 : _ ⟶ _) = 𝟘; exact DistributiveAllegory.comp_zero _
    union_idem := fun R => by
      apply SplHom.ext; show R.R ∪ R.R = R.R; exact DistributiveAllegory.union_idem _
    union_comm := fun R S => by
      apply SplHom.ext; show R.R ∪ S.R = S.R ∪ R.R; exact DistributiveAllegory.union_comm _ _
    union_assoc := fun R S T => by
      apply SplHom.ext; show R.R ∪ (S.R ∪ T.R) = (R.R ∪ S.R) ∪ T.R
      exact DistributiveAllegory.union_assoc _ _ _
    union_inter_absorb := fun R S => by
      apply SplHom.ext; show R.R ∪ (S.R ∩ R.R) = R.R
      exact DistributiveAllegory.union_inter_absorb _ _
    inter_union_absorb := fun R S => by
      apply SplHom.ext; show (R.R ∪ S.R) ∩ R.R = R.R
      exact DistributiveAllegory.inter_union_absorb _ _
    comp_union_distrib := fun R S T => by
      apply SplHom.ext; show R.R ≫ (S.R ∪ T.R) = (R.R ≫ S.R) ∪ (R.R ≫ T.R)
      exact DistributiveAllegory.comp_union_distrib _ _ _
    inter_union_distrib := fun R S T => by
      apply SplHom.ext; show R.R ∩ (S.R ∪ T.R) = (R.R ∩ S.R) ∪ (R.R ∩ T.R)
      exact DistributiveAllegory.inter_union_distrib _ _ _
    zero_union := fun R => by
      apply SplHom.ext; show (𝟘 : _ ⟶ _) ∪ R.R = R.R; exact DistributiveAllegory.zero_union _ }

/-- **§2.34 (reflexive)**: if `𝒜` is a DIVISION allegory then so is `Spl(Eq 𝒜)`, with right
    division taken pointwise (`splDiv`).  Both §2.31 laws reduce to the base `div_comp_le` /
    `le_div`, exactly as for the full `SplObj 𝒜` (`instDivisionSpl`). -/
noncomputable instance instDivisionSplEq {𝒜 : Type u} [DivisionAllegory 𝒜] :
    DivisionAllegory (SplEqObj 𝒜) :=
  { instDistributiveSplEq with
    div := fun Φ Ψ => splDiv Φ Ψ
    div_comp_le := fun {E F G} Φ Ψ => by
      rw [splEqLe_iff]
      show (E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e) ≫ Ψ.R ⊑ Φ.R
      calc (E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e) ≫ Ψ.R
          = E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ (F.1.idem.e ≫ Ψ.R) := by simp only [Cat.assoc]
        _ = E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ Ψ.R := by rw [Ψ.fixed_left]
        _ ⊑ E.1.idem.e ≫ Φ.R := comp_mono_left _ (DivisionAllegory.div_comp_le _ _)
        _ = Φ.R := Φ.fixed_left
    le_div := fun {E F G} T Φ Ψ h => by
      rw [splEqLe_iff] at h ⊢
      show T.R ⊑ E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e
      have hbase : T.R ⊑ Φ.R / Ψ.R := DivisionAllegory.le_div T.R Φ.R Ψ.R h
      calc T.R = E.1.idem.e ≫ T.R ≫ F.1.idem.e := T.fixed.symm
        _ ⊑ E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e :=
            comp_mono_left _ (comp_mono_right hbase _) }

end Freyd.Alg
