/-
  §1.61 (lax) — the STRICT INITIAL object of a FILTERED lax colimit of pre-logoi.

  Lax port of `Colim.colimitStrictInitial` (`ColimitPreLogos.lean`).  For a `LaxCatSystem` whose
  every stage `L.A i` is a `PreLogos` (§1.6) and whose transitions preserve the chosen stage
  strict-initial object `0_i` on the nose (`hinitpres`), the `objIncl`-image of one stage's strict
  initial `0_{i₀}` is a STRICT COTERMINATOR (strict initial) of the lax colimit `laxColimCat L hL`:
  every lax-colimit map INTO it is an iso.

  KEY SIMPLIFICATION over the strict version.  The lax colimit's objects are the BARE Σ-type
  `Obj L = Σ i, L.A i` — NOT a quotient.  So the codomain `objIncl L i₀ 0_{i₀} = ⟨i₀, 0_{i₀}⟩` is
  literal, and a germ representative `f₀ : L.F a.2.1 xX ⟶ L.F a.2.2 0_{i₀}` of a map into it has its
  codomain `L.F a.2.2 0_{i₀}` EQUAL (on the nose, `hinitpres a.2.2`) to the stage strict-initial
  `0_{a.1}`.  Hence NO push to a common stage `M'` is needed (the strict proof's object-alignment
  `objIncl_eq_commonStage`/`colimHom_as_homInclObj` collapses): cast `f₀` to a map into `0_{a.1}`,
  which is iso by `any_map_to_zero_is_iso` (§1.61); `isIso_of_castHom` strips the cast to `IsIso f₀`,
  whose inverse-and-equations feed `homInclL_isIso_of_rep` (`LaxColimitPreReg.lean`) to lift the
  stage iso to the colimit.

  Mathlib-free; built on `Fredy.LaxColimitPreReg` + the §1.61 strict-initial API.
-/
import Fredy.LaxColimitPreReg
import Fredy.S1_61

open Freyd
open Freyd.Colim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}

/-- `castHom` reflects isomorphisms (it is a transport along object equalities).  Local copy of
    `Colim.isIso_of_castHom`, duplicated here to avoid importing the heavy §2.218 regular tower
    (`CatColimitRegular`) for a two-line generic utility. -/
private theorem isIso_of_castHom {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜}
    (hX : X = X') (hY : Y = Y') (m : X ⟶ Y) (h : IsIso (castHom hX hY m)) : IsIso m := by
  subst hX; subst hY; exact h

/-- The chosen strict initial object of stage `i` (the minimal subobject of `1`, §1.61).  Lax
    analogue of `Colim.stageZero`. -/
noncomputable def stageZero (L : LaxCatSystem ι D) (hbot : ∀ i, PreLogos (L.A i)) (i : ι) : L.A i :=
  (minimal_subobject_of_one_is_coterminator (hbot i)).zero

/-- **The lax colimit-zero brick.**  The `objIncl`-image of one stage's strict initial `0_{i₀}` is a
    STRICT COTERMINATOR (strict initial) of `laxColimCat L hL`: every lax-colimit map into it is an
    iso.  Lax port of `Colim.colimitStrictInitial`.

    PROOF.  A map `g : X ⟶ objIncl L i₀ 0_{i₀}` is a germ; pick a representative `⟨a, f₀⟩` with
    `f₀ : L.F a.2.1 xX ⟶ L.F a.2.2 0_{i₀}` at an upper bound `a` of `(jX, i₀)`.  Its codomain
    `L.F a.2.2 0_{i₀}` IS the stage strict-initial `0_{a.1}` on the nose (`hinitpres a.2.2`), so
    casting `f₀` to a map into `0_{a.1}` makes it a map into the stage strict initial, hence iso
    (`any_map_to_zero_is_iso`, §1.61).  `isIso_of_castHom` strips the cast to `IsIso f₀`, whose
    inverse-and-equations feed `homInclL_isIso_of_rep` to lift the stage iso to the colimit. -/
theorem laxColimStrictInitial (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L) [Nonempty ι]
    (hbot : ∀ i, PreLogos (L.A i))
    (hinitpres : ∀ {i j : ι} (hij : D.le i j), L.F hij (stageZero L hbot i) = stageZero L hbot j)
    (i₀ : ι) :
    letI : Cat (Obj L) := laxColimCat L hL
    StrictCoterminator (objIncl L i₀ (stageZero L hbot i₀)) := by
  letI : Cat (Obj L) := laxColimCat L hL
  intro X g
  obtain ⟨jX, xX⟩ := X
  -- a germ representative `⟨a, f₀⟩` of the lax-colimit map `g`
  refine Quotient.inductionOn g (fun rep => ?_)
  obtain ⟨a, f₀⟩ := rep
  -- `f₀ : L.F a.2.1 xX ⟶ L.F a.2.2 0_{i₀}`; its codomain IS `0_{a.1}` on the nose
  have e : L.F a.2.2 (stageZero L hbot i₀) = stageZero L hbot a.1 := hinitpres a.2.2
  -- cast into `0_{a.1}` ⟹ a map into a strict initial ⟹ iso (§1.61); strip the cast
  have hf0 : IsIso f₀ :=
    isIso_of_castHom rfl e f₀ (any_map_to_zero_is_iso (hbot a.1) (castHom rfl e f₀))
  obtain ⟨g₀, h1, h2⟩ := hf0
  -- lift the stage iso to the colimit
  exact homInclL_isIso_of_rep L hL xX (stageZero L hbot i₀) a f₀ g₀ h1 h2

end Freyd.LaxColim
