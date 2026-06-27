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
import Fredy.StalkRegular
import Fredy.FiniteSeparation
import Fredy.Capitalization
import Fredy.CapitalProjective

universe u w

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
    {MapA : Type u} [Cat.{w} MapA] [RegularCategory MapA]
    (bridge : Alg.AllegoryFunctor 𝒜 (RelObj MapA)) (hbridge : bridge.Faithful)
    {Ā : Type u} [Cat.{u} Ā] [RegularCategory Ā]
    (hproj : ∀ C : Ā, ∀ {P : Ā} (e : P ⟶ C), Cover e → ∃ s : C ⟶ P, s ≫ e = Cat.id C)
    (cap : Alg.AllegoryFunctor (RelObj MapA) (RelObj Ā)) (hcap : cap.Faithful) :
    ∃ rep : Alg.AllegoryFunctor 𝒜 (RelObj (Ā → Type u)), rep.Faithful := by
  refine ⟨(bridge.comp cap).comp (homRep_regularFunctor hproj).relAllegoryHom, ?_⟩
  exact Alg.AllegoryFunctor.Faithful.comp
    (Alg.AllegoryFunctor.Faithful.comp hbridge hcap) (relHomRep_faithful hproj)

/-- **§2.218 (R2 discharged).**  Specialization of `repr_in_power_of_sets` to a *tabular* unitary
    distributive allegory `𝒜`, with the CARRIER BRIDGE (R2) supplied internally by the §2.148/§2.217(2)
    span equivalence `bridgeFunctor` (faithful by `bridgeFunctor_faithful`, built from the `relOf`
    dictionary + the meet-tabulation `relOf_inter`).  `MapA := Map 𝒜` (`mapRegularCategory`).

    Only the §1.543 CAPITAL-TARGET data (R3) remains as hypotheses: a regular capital `Ā`
    (`[RegularCategory Ā]` + `hproj`) with a faithful regular allegory morphism
    `cap : Rel(Map 𝒜) ⟶ Rel(Ā)`.  See the §2.218 marker in `S2_21.lean` for R3's status. -/
theorem repr_in_power_of_sets_of_tabular
    {𝒜 : Type u} [Alg.TabularUnitaryDistributiveAllegory 𝒜]
    {Ā : Type u} [Cat.{u} Ā] [RegularCategory Ā]
    (hproj : ∀ C : Ā, ∀ {P : Ā} (e : P ⟶ C), Cover e → ∃ s : C ⟶ P, s ≫ e = Cat.id C)
    (cap : @Alg.AllegoryFunctor (RelObj (Alg.MapObj 𝒜)) (RelObj Ā)
        (@relAllegory (Alg.MapObj 𝒜) Alg.mapCat Alg.mapRegularCategory) (relAllegory)
      ) (hcap : cap.Faithful) :
    ∃ rep : Alg.AllegoryFunctor 𝒜 (RelObj (Ā → Type u)), rep.Faithful := by
  -- Pin `Map 𝒜`'s category / regular structure to `mapCat` (hom-universe `v`, NOT forced to `u`),
  -- so `RelObj (Map 𝒜)`'s `relAllegory` matches the one baked into `bridgeFunctor`/`cap`.
  letI : Cat (Alg.MapObj 𝒜) := Alg.mapCat
  letI : RegularCategory (Alg.MapObj 𝒜) := Alg.mapRegularCategory
  exact repr_in_power_of_sets (MapA := Alg.MapObj 𝒜)
    (bridgeFunctor 𝒜) (bridgeFunctor_faithful 𝒜) hproj cap hcap

/-! ## §2.218 (K2) — the ULTRA-FILTER STALK route to a faithful `Rel(𝒞) → Rel(Set)`

  Freyd's §1.635 proves the representation theorem through the stalk functors `T_F̂` rather than the
  raw hom-representation.  The keystone `TF_regularFunctor` (K1, `Fredy/StalkRegular.lean`) makes a
  single stalk a `RegularFunctor 𝒞 → Set`, so `Rel(T_F̂)` is an allegory morphism `Rel(𝒞) → Rel(Set)`.
  Its FAITHFULNESS, via `relAllegoryHom_faithful_of_reflects`, needs exactly two facts about the
  stalk — and the stalk route does NOT remove either of the §2.218 residuals, it RELOCATES them:

    (R3, projectivity)  `T_F̂` preserves COVERS only when the elements of `F̂` are PROJECTIVE
        (`TF_preserves_covers_of_projective`).  This is Freyd's own hypothesis — his §1.635 proof
        opens *"We may concentrate on a CAPITAL positive pre-logos A [1.63]"* precisely so that the
        complemented subterminators (the ultra-filter's members) are projective (§1.633).  So
        capitalization is STILL required; the colimit does not buy cover-preservation for free
        (covers are not a finite-limit notion — only `pres_prod`/`pres_pullback`/`pres_mono` are
        unconditional).

    (CONSERVATIVITY)  `relAllegoryHom_faithful_of_reflects` needs `T_F̂` to REFLECT ISOS.  A single
        stalk does not; this is the §2.217-grade joint conservativity of the stalk FAMILY, the
        genuinely irreducible residual (`StalkResidual.reflect` in `S1_62`).

  Covers in `Set` split (choice, `set_cover_splits`), so the third ingredient is free. -/

/-- Every cover in `Set = Type u` splits (fibrewise surjection has a section). -/
theorem set_cover_splits {X Y : Type u} (e : X ⟶ Y) (he : Cover e) :
    ∃ s : Y ⟶ X, s ≫ e = Cat.id Y := by
  have hsurj : Function.Surjective e := (SetRegular.set_cover_iff_surjective e).1 he
  exact ⟨fun b => (hsurj b).choose, by funext b; exact (hsurj b).choose_spec⟩

open PreLogosHorn.Stalk in
/-- **§2.218 (K2, single stalk).**  For a positive pre-logos `𝒞` and an ultra-filter `F̂` whose
    members are PROJECTIVE (the capital case, §1.633) and whose stalk `T_F̂` REFLECTS ISOS
    (conservativity), `Rel(T_F̂) : Rel(𝒞) ⟶ Rel(Set)` is a FAITHFUL allegory morphism.

    This is the stalk-route analogue of `relHomRep_faithful`; it shows the stalk does not bypass
    either §2.218 residual (projectivity + conservativity) but packages them cleanly via K1. -/
theorem relStalk_faithful {𝒞 : Type u} [Cat.{u} 𝒞] [PreLogos 𝒞]
    (ℱ : Subobject 𝒞 one → Prop) (hℱ : IsPreFilter ℱ)
    (hproj : ∀ U : Subobject 𝒞 one, ℱ U → Projective U.dom)
    (hrefl : ∀ {X Y : 𝒞} (f : X ⟶ Y), IsIso ((TF_functor ℱ).map f) → IsIso f) :
    (TF_regularFunctor ℱ hℱ hproj).relAllegoryHom.Faithful :=
  (TF_regularFunctor ℱ hℱ hproj).relAllegoryHom_faithful_of_reflects
    (fun f hiso => hrefl f hiso)
    (fun e he => set_cover_splits e he)

/-! ## §1.633 discharges the stalk-route PROJECTIVITY residual (R3) in the capital case

  Freyd's §1.635 stalk construction takes `ℱ` to be an ultra-filter on the boolean algebra `ℬ`
  of COMPLEMENTED SUBTERMINATORS of a CAPITAL positive pre-logos.  For such an `ℱ` the
  `hproj` hypothesis of `TF_regularFunctor`/`relStalk_faithful` (each member projective) is no
  longer an assumption: it is `capital_complementedSub_projective` (§1.633).  This is exactly why
  Freyd opens §1.635 with *"we may concentrate on a capital positive pre-logos"*. -/

/-- **§1.633 ⟹ stalk projectivity.**  In a CAPITAL positive pre-logos, if every member of the
    pre-filter `ℱ` is a complemented subterminator, then every member's domain is projective —
    discharging the `hproj` residual of the stalk route. -/
theorem capital_filter_projective {𝒞 : Type u} [Cat.{u} 𝒞] [DisjointBinaryCoproduct 𝒞]
    (hcap : Capital (𝒞 := 𝒞)) (ℱ : Subobject 𝒞 one → Prop)
    (hcompl : ∀ U : Subobject 𝒞 one, ℱ U → IsComplementedSub U) :
    ∀ U : Subobject 𝒞 one, ℱ U → Projective U.dom :=
  fun U hU => capital_complementedSub_projective hcap U (hcompl U hU)

open PreLogosHorn.Stalk in
/-- **§2.218 (K2, capital stalk).**  Freyd's actual §1.635 hypotheses: a CAPITAL positive pre-logos
    `𝒞`, an ultra-filter `ℱ` of COMPLEMENTED SUBTERMINATORS whose stalk reflects isos.  The
    projectivity residual is discharged by §1.633 (`capital_filter_projective`); only the
    single-stalk CONSERVATIVITY (`hrefl`) remains — the genuinely irreducible §2.217-grade residual
    that needs the stalk FAMILY, not `Capital` alone (a single stalk forgets every subterminator
    outside `ℱ`, so cannot detect an iso supported off `ℱ`). -/
theorem relStalk_faithful_capital {𝒞 : Type u} [Cat.{u} 𝒞] [DisjointBinaryCoproduct 𝒞]
    (hcap : Capital (𝒞 := 𝒞)) (ℱ : Subobject 𝒞 one → Prop) (hℱ : IsPreFilter ℱ)
    (hcompl : ∀ U : Subobject 𝒞 one, ℱ U → IsComplementedSub U)
    (hrefl : ∀ {X Y : 𝒞} (f : X ⟶ Y), IsIso ((TF_functor ℱ).map f) → IsIso f) :
    (TF_regularFunctor ℱ hℱ (capital_filter_projective hcap ℱ hcompl)).relAllegoryHom.Faithful :=
  relStalk_faithful ℱ hℱ (capital_filter_projective hcap ℱ hcompl) hrefl

end Freyd
