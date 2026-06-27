/-
  Freyd & Scedrov, *Categories and Allegories* — §2.218.

  "A small pre-tabular or semi-simple unitary distributive allegory may be faithfully
  represented in a power of the allegory of sets."

  This file ASSEMBLES the §2.218 representation from the bricks built elsewhere:
    • BRICK 1  `Freyd.SetRegular.{setRegular,powerRegular}`   (S1_62)   — `Set`, `Set^I` regular.
    • BRICK 2  `Freyd.RelFunctor.RegularFunctor` + `relAllegoryHom`     (RelCat) — `Rel(F)`.
    • BRICK 2c `Freyd.homRep_regularFunctor`                            (RelCat) — `homRep` regular.
    • BRICK 3  `Freyd.PowerAllegory.powerAllegory`                      (RelCat) — `𝒜^I` allegory.
    • R1       `RegularFunctor.relAllegoryHom_faithful_of_reflects`     (RelCat) — Rel(F) faithful
               for a NON-FULL `F` (reflects isos + split covers) — the §2.218 wall, now CLOSED.

  The genuine residuals isolated as explicit hypotheses are documented at `repr_in_power_of_sets`.
-/

import Fredy.RelCat
import Fredy.FiniteSeparation
import Fredy.Capitalization

universe u

namespace Freyd

open Cat RelFunctor

/-! ## §2.218  `Rel(homRep 𝒞)` is faithful for a capital regular category

  For a regular category `𝒞` in which every cover splits (`hproj` — the §1.543 capital
  situation) and which has *images* (`RegularCategory`), the Henkin–Lubkin representation
  `homRep 𝒞 : 𝒞 → Set^|𝒞|` is a `RegularFunctor` (BRICK 2c) that reflects isos
  (`homRep_reflects_iso`); covers in `Set^|𝒞|` split (fibrewise surjections, `power_cover_iff`).
  So the §2.218 (2b′) non-full faithfulness `relAllegoryHom_faithful_of_reflects` (R1) applies. -/

/-- Every cover in the power category `𝒞 → Type u` splits: a cover is fibrewise surjective
    (`power_cover_iff`), and each fibre surjection has a section (choice). -/
theorem power_cover_splits {𝒞 : Type u} {X Y : 𝒞 → Type u} (e : X ⟶ Y) (he : Cover e) :
    ∃ s : Y ⟶ X, s ≫ e = Cat.id Y := by
  have hsurj : ∀ i, Function.Surjective (e i) := (SetRegular.power_cover_iff e).1 he
  exact ⟨fun i b => (hsurj i b).choose, by funext i b; exact (hsurj i b).choose_spec⟩

/-- **§2.218 — `Rel(homRep 𝒞)` is a FAITHFUL allegory morphism** `Rel(𝒞) → Rel(Set^|𝒞|)`.
    Needs `𝒞` regular (images), capital (`hproj` — every cover splits, the §1.543 case).
    Combines BRICK 2c (`homRep_regularFunctor`), `homRep_reflects_iso`, and the §2.218 (2b′)
    image-reflection faithfulness (R1). -/
theorem relHomRep_faithful {𝒞 : Type u} [Cat.{u} 𝒞] [RegularCategory 𝒞]
    (hproj : ∀ C : 𝒞, ∀ {P : 𝒞} (e : P ⟶ C), Cover e → ∃ s : C ⟶ P, s ≫ e = Cat.id C) :
    (homRep_regularFunctor hproj).relAllegoryHom.Faithful :=
  (homRep_regularFunctor hproj).relAllegoryHom_faithful_of_reflects
    (fun f hiso => homRep_reflects_iso 𝒞 f hiso)
    (fun e he => power_cover_splits e he)

/-! ## §2.218  The faithful representation in a power of the allegory of sets

  `RelObj (𝒞 → Type u)` is the allegory of (jointly-monic) relations in `Set^|𝒞|`.  Up to the
  fibrewise comparison `RelObj(Set^I) ≅ (RelObj Set)^I` (BRICK 3 `powerAllegory`, the
  un-built routine half), it is a *power of the allegory of sets*; the §2.218 headline names the
  target as exactly this allegory of relations in `Set^I`. -/

/-- **§2.218 (assembly).**  Let `𝒜` be a (small) unitary distributive allegory which is tabular
    — the hypothesis discharged from *pre-tabular*/*semi-simple* by §2.16(10)/§2.167 (Spl).  Given:
      • `bridge`  — a FAITHFUL allegory morphism `𝒜 ⟶ Rel(Map 𝒜)` presenting `𝒜` as relations in
        the regular category `Map 𝒜` (R2: the §2.148 carrier equivalence in span form);
      • `Ā`, regular (`RegularCategory Ā`) and capital (`hproj`: every cover in `Ā` splits), with a
        FAITHFUL regular allegory morphism `cap : Rel(Map 𝒜) ⟶ Rel(Ā)` from capitalizing
        `Map 𝒜 ↪ Ā` (R3: §1.543 — `capitalization_of_capData`, supplying regularity + projectivity
        of the capital colimit) —
    THEN `𝒜` is FAITHFULLY represented in `Rel(Set^|Ā|)`, the allegory of relations in a power of
    sets, via `bridge ⋙ cap ⋙ Rel(homRep Ā)`.

    The composite is an `AllegoryFunctor` (`AllegoryFunctor.comp`); its faithfulness is the
    composite of the three faithfulnesses (`AllegoryFunctor.Faithful.comp`), the last of which is
    the §2.218 wall `relHomRep_faithful` (R1 + BRICK 2c).  ALL bricks are built; the two `bridge`/
    `cap`+`Ā` hypotheses are the precisely-isolated residuals (R2 / R3). -/
theorem repr_in_power_of_sets
    {𝒜 : Type u} [Alg.Allegory 𝒜]
    {MapA : Type u} [Cat.{u} MapA] [RegularCategory MapA]
    (bridge : Alg.AllegoryFunctor 𝒜 (RelObj MapA)) (hbridge : bridge.Faithful)
    {Ā : Type u} [Cat.{u} Ā] [RegularCategory Ā]
    (hproj : ∀ C : Ā, ∀ {P : Ā} (e : P ⟶ C), Cover e → ∃ s : C ⟶ P, s ≫ e = Cat.id C)
    (cap : Alg.AllegoryFunctor (RelObj MapA) (RelObj Ā)) (hcap : cap.Faithful) :
    ∃ rep : Alg.AllegoryFunctor 𝒜 (RelObj (Ā → Type u)), rep.Faithful := by
  refine ⟨(bridge.comp cap).comp (homRep_regularFunctor hproj).relAllegoryHom, ?_⟩
  exact Alg.AllegoryFunctor.Faithful.comp
    (Alg.AllegoryFunctor.Faithful.comp hbridge hcap) (relHomRep_faithful hproj)

end Freyd
