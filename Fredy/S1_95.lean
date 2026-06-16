/-
  Freyd & Scedrov, *Categories and Allegories* §1.95–§1.96  Topos theorems.

  §1.951  A topos is EFFECTIVE (every equivalence relation is effective).
  §1.952  A topos is POSITIVE.
  §1.954  A topos has coequalizers.
  §1.955  A topos is bicartesian.
  §1.961  INJECTIVE object; INTERNALLY INJECTIVE; Ω is internally injective.
  §1.962  Ω^A is injective; every object embeds in an injective.
  §1.964  VALUE-BASED category/topos; Ω cogenerates in a value-based topos.
  §1.965  INTERNALLY COGENERATES.
  §1.966  PROGENITOR.
  §1.967  Arbitrary powers ↔ arbitrary copowers ↔ arbitrary copowers of 1 (locally small topos).
  §1.968  Locally small topos: complete ↔ cocomplete.
  §1.969  Lawvere and Tierney definitions of Grothendieck topos.
-/

import Fredy.S1_1
import Fredy.S1_9
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58
import Fredy.S1_59
import Fredy.S1_60
import Fredy.S1_62
import Fredy.S1_64
import Fredy.S1_77
import Fredy.S1_82
import Fredy.S1_84
import Fredy.S1_85
import Fredy.S1_91
import Fredy.S1_92
import Fredy.S1_94


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## §1.951  A topos is effective -/

section Effective
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-- `(graph g) ⊚ (graph g)° ⊂ level g`.  A composed point `(a,c)` satisfies
    `a ≫ g = c ≫ g` (the pullback square forces it), so its span lifts into
    `kernelPair g`, and image-minimality turns that into the `RelHom`.
    (Re-proved locally: the S1_64 version is `private`.) -/
private theorem graphComp_le_level {A Q : 𝒞} (g : A ⟶ Q) :
    RelLe ((graph g) ⊚ (graph g)°) (kernelPairRel g) := by
  let pb := HasPullbacks.has (graph g).colB ((graph g)°).colA
  let a' := pb.cone.π₁ ≫ (graph g).colA
  let c' := pb.cone.π₂ ≫ ((graph g)°).colB
  let sp : pb.cone.pt ⟶ prod A A := pair a' c'
  have hw : a' ≫ g = c' ≫ g := by
    have := pb.cone.w
    dsimp [a', c']; simpa [graph, reciprocal, Cat.comp_id] using this
  let S : Subobject 𝒞 (prod A A) :=
    ⟨kernelPair g, pair (kp₁ (f := g)) (kp₂ (f := g)),
      monic_pair_of_monicPair _ _ (kernelPairRel g).isMonicPair⟩
  let w := (HasPullbacks.has g g).lift ⟨_, a', c', hw⟩
  have hspan : w ≫ pair (kp₁ (f := g)) (kp₂ (f := g)) = sp := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]; exact kp_lift_p₁ _ _ hw
    · rw [Cat.assoc, snd_pair]; exact kp_lift_p₂ _ _ hw
  obtain ⟨k, hk⟩ := image_min sp S ⟨w, hspan⟩
  refine ⟨⟨k, ?_, ?_⟩⟩
  · show k ≫ kp₁ (f := g) = (image sp).arr ≫ fst
    calc k ≫ kp₁ (f := g) = (k ≫ pair (kp₁ (f := g)) (kp₂ (f := g))) ≫ fst := by
            rw [Cat.assoc, fst_pair]
      _ = (image sp).arr ≫ fst := by rw [hk]
  · show k ≫ kp₂ (f := g) = (image sp).arr ≫ snd
    calc k ≫ kp₂ (f := g) = (k ≫ pair (kp₁ (f := g)) (kp₂ (f := g))) ≫ snd := by
            rw [Cat.assoc, snd_pair]
      _ = (image sp).arr ≫ snd := by rw [hk]

/-- `level g ⊂ (graph g) ⊚ (graph g)°`: the kernel-pair legs `(kp₁, kp₂)` form a
    cone over `g,g`, hence lift into the composition's pullback, then through
    `image.lift`.  (Re-proved locally: the S1_64 version is `private`.) -/
private theorem level_le_graphComp {A Q : 𝒞} (g : A ⟶ Q) :
    RelLe (kernelPairRel g) ((graph g) ⊚ (graph g)°) := by
  let pb := HasPullbacks.has (graph g).colB ((graph g)°).colA
  let a' := pb.cone.π₁ ≫ (graph g).colA
  let c' := pb.cone.π₂ ≫ ((graph g)°).colB
  let sp : pb.cone.pt ⟶ prod A A := pair a' c'
  have hcone : kp₁ (f := g) ≫ (graph g).colB = kp₂ (f := g) ≫ ((graph g)°).colA := by
    simp only [graph, reciprocal]; exact kp_sq
  let v := pb.lift ⟨_, kp₁ (f := g), kp₂ (f := g), hcone⟩
  have hv1 : v ≫ pb.cone.π₁ = kp₁ (f := g) := pb.lift_fst _
  have hv2 : v ≫ pb.cone.π₂ = kp₂ (f := g) := pb.lift_snd _
  refine ⟨⟨v ≫ image.lift sp, ?_, ?_⟩⟩
  · show (v ≫ image.lift sp) ≫ ((image sp).arr ≫ fst) = kp₁ (f := g)
    calc (v ≫ image.lift sp) ≫ ((image sp).arr ≫ fst)
        = v ≫ ((image.lift sp ≫ (image sp).arr) ≫ fst) := by simp [Cat.assoc]
      _ = v ≫ (sp ≫ fst) := by rw [image.lift_fac]
      _ = v ≫ a' := by rw [fst_pair]
      _ = (v ≫ pb.cone.π₁) ≫ (graph g).colA := by dsimp [a']; rw [Cat.assoc]
      _ = kp₁ (f := g) := by rw [hv1]; simp [graph, Cat.comp_id]
  · show (v ≫ image.lift sp) ≫ ((image sp).arr ≫ snd) = kp₂ (f := g)
    calc (v ≫ image.lift sp) ≫ ((image sp).arr ≫ snd)
        = v ≫ ((image.lift sp ≫ (image sp).arr) ≫ snd) := by simp [Cat.assoc]
      _ = v ≫ (sp ≫ snd) := by rw [image.lift_fac]
      _ = v ≫ c' := by rw [snd_pair]
      _ = (v ≫ pb.cone.π₂) ≫ ((graph g)°).colB := by dsimp [c']; rw [Cat.assoc]
      _ = kp₂ (f := g) := by rw [hv2]; simp [graph, reciprocal, Cat.comp_id]

/-- **§1.951, recovery half (fully proved)**: in a Cartesian category with images,
    if an equivalence relation `E` is the level (kernel pair) of a cover
    `x : A → Q` — i.e. `E ⊂ level x` and `level x ⊂ E` — then `E` is EFFECTIVE.

    This is the *substantive content* of §1.568/§1.951 once the quotient cover is
    available: it packages `E ≅ level x ≅ (graph x) ⊚ (graph x)°` using the two
    bridges above, producing the `IsEffective` data (`Q`, `x`, `Cover x`, and the
    mutual relational containments with `(graph x) ⊚ (graph x)°`).  No `sorry`. -/
theorem effective_of_quotient_cover {A Q : 𝒞} (E : BinRel 𝒞 A A)
    (hE : EquivalenceRelation E) (x : A ⟶ Q) (hx : Cover x)
    (hElx : RelLe E (kernelPairRel x)) (hlxE : RelLe (kernelPairRel x) E) :
    IsEffective E :=
  ⟨hE, Q, x, hx,
    rel_le_trans hElx (level_le_graphComp x),
    rel_le_trans (graphComp_le_level x) hlxE⟩

end Effective

/-- **§1.951**: A topos is effective: every equivalence relation on any object is
    the level of some cover (i.e., is effective in the sense of §1.568).

    Freyd's route (the power-object construction): an equivalence relation
    `E ⊆ A×A` is tabulated; the quotient `A/E` is obtained as the image of the
    classifying / characteristic map `A → Ω^A` (singleton `Δ₁` composed with the
    quotient that names `E`-classes), and `q : A ↠ A/E` is a cover whose level
    (kernel pair) is exactly `E`.  Granting that quotient cover,
    `effective_of_quotient_cover` discharges effectiveness completely.

    **Sharpened blocker (faithful sorry).**  Building the `EffectiveRegular`
    instance from bare `[Topos 𝒞]` needs THREE ingredients, of which only the
    last is genuinely absent here:

      (1) `HasImages 𝒞` — NOT derivable from `Topos` in this repo.  The only topos
          construction of `image f` is `⋂{B' ↣ B | f factors through B'}`
          (§1.943), the glb over a subobject *family*, which rests on §1.54's
          `capitalization_lemma` (still `sorry`; see `topos_is_regular`,
          S1_94:321).

      (2) `PullbacksTransferCovers 𝒞` — topos exactness; likewise reducible to the
          §1.54 / image machinery (cf. `regular_of_compose_assoc`, S1_56:1255).

      (3) THE QUOTIENT COVER — for each equivalence relation `E`, a cover
          `q : A ↠ A/E` with `level q ≅ E`.  This is Freyd's power-object
          construction `A → Ω^A` and needs the power object `Ω^A = exp A Ω`,
          which is opaque here because `topos_has_exponentials` (S1_92) is itself
          an unfilled `sorry` (blocked on §1.543 capitalization).

    Once (1)–(3) are available, this instance is
    `⟨…, fun E hE => effective_of_quotient_cover E hE q hq hElq hlqE⟩`
    with `(q, hq, hElq, hlqE)` the quotient cover from (3).  The recovery half (the
    relation-algebra identity `E ≅ level q ≅ (graph q)⊚(graph q)°`) is now PROVED
    above (`effective_of_quotient_cover`), so the residual gap is exactly the
    quotient-cover existence (3) on top of the §1.54-blocked (1)–(2). -/
instance topos_is_effective [Topos 𝒞] : EffectiveRegular 𝒞 := by
  sorry

/-! ## §1.952  A topos is positive -/

/-- **§1.952**: A topos is positive: it has binary coproducts A + B.
    Proof sketch (Freyd): For any A, ΔR factors through ΔA1 iff R is a map,
    and through Δ0 iff R = 0.  So A + 1 exists.  Then A + B is constructed
    as a subobject of [A] × [B] = [A + B]. -/
instance topos_is_positive [Topos 𝒞] : HasBinaryCoproducts 𝒞 := by
  sorry

/-! ## §1.954  A topos has coequalizers -/

section Coequalizers
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-- **Bridge (§1.77 ↔ §1.56)**: the relation-algebra notion of equivalence
    (`IsEquivRel`: `1 ⊑ E`, `E° ⊑ E`, `E⊚E ⊑ E`) yields the §1.56 notion
    `EquivalenceRelation` (reflexivity *witness*, `RelHom E E°`, `RelHom (E⊚E) E`).

    * reflexivity: a `RelHom (graph 1_A) E` is exactly a map `h : A → E.src` with
      `h ≫ E.colA = 1_A` and `h ≫ E.colB = 1_A`;
    * symmetry: `RelLe E° E` reciprocates (involution) to `RelLe E E°`, i.e.
      `RelHom E E°`;
    * transitivity: `RelLe (E⊚E) E` is literally `Nonempty (RelHom (E⊚E) E)`. -/
theorem equivalenceRelation_of_isEquivRel {A : 𝒞} {E : BinRel 𝒞 A A}
    (hE : IsEquivRel E) : EquivalenceRelation E := by
  obtain ⟨⟨h, hA, hB⟩, hsym, htrans⟩ := hE
  refine ⟨⟨h, ?_, ?_⟩, ?_, htrans⟩
  · -- `h : (graph 1_A).src ⟶ E.src` with the graph(1) columns = 1_A.
    simpa [graph] using hA
  · simpa [graph] using hB
  · -- symmetry: reciprocate `E° ⊑ E` and use involution `E°° = E`.
    have := reciprocal_monotone hsym
    rwa [reciprocal_invol] at this

end Coequalizers

/-- **§1.954, core reduction**: in a category with reflexive-transitive closures
    every endo-relation has a *minimal equivalence relation* containing it
    (`HasMinEquivContaining`).  The minimal equivalence containing `R` is the
    equivalence closure `(R ∪ R° ∪ 1)*`: form the symmetrisation
    `Rsym := (R ∪ᵣ R°) ∪ᵣ graph 1_A`, take its reflexive-transitive closure with
    `rtc`, and feed both to `equivClos_from_symm_transRefClos`.

    `Rsym` is the *join* of `R`, `R°`, `1` (hence the `hJoin` universal property is
    `le_relUnion`), and is symmetric: `Rsym° = R° ∪ R ∪ 1 = Rsym` (proved one
    direction via the join property + reciprocal involution, the other by
    reciprocating).  The resulting `EquivClos`'s `minimal` field is exactly the
    minimality required by `HasMinEquivContaining` (after the `IsEquivRel ↔
    EquivalenceRelation` bridge). -/
theorem minEquiv_of_rtc [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [HasBinaryCoproducts 𝒞] [HasReflTransClosure 𝒞] :
    HasMinEquivContaining 𝒞 := by
  intro A R
  -- Symmetrisation Rsym = (R ∪ R°) ∪ 1, the join of R, R°, graph(1_A).
  let G : BinRel 𝒞 A A := graph (Cat.id A)
  let Rsym : BinRel 𝒞 A A := (R ∪ᵣ R°) ∪ᵣ G
  -- Each generator sits below Rsym.
  have hR_sym : RelLe R Rsym :=
    rel_le_trans (relUnion_le_left R (R°)) (relUnion_le_left (R ∪ᵣ R°) G)
  have hRrec_sym : RelLe (R°) Rsym :=
    rel_le_trans (relUnion_le_right R (R°)) (relUnion_le_left (R ∪ᵣ R°) G)
  have hG_sym : RelLe G Rsym := relUnion_le_right (R ∪ᵣ R°) G
  -- Join universal property: any U above R, R°, 1 is above Rsym.
  have hJoin : ∀ (U : BinRel 𝒞 A A),
      RelLe R U → RelLe (R°) U → RelLe G U → RelLe Rsym U := by
    intro U hRU hRrecU hGU
    exact le_relUnion (le_relUnion hRU hRrecU) hGU
  -- Symmetry of Rsym: Rsym ⊑ Rsym°, then reciprocate.
  have hsym : IsSymmetric Rsym := by
    have hle : RelLe Rsym (Rsym°) := by
      apply hJoin
      · -- R = R°° ⊑ Rsym°: from R° ⊑ Rsym reciprocate, involution.
        have := reciprocal_monotone hRrec_sym
        rwa [reciprocal_invol] at this
      · -- R° ⊑ Rsym°: from R ⊑ Rsym reciprocate.
        exact reciprocal_monotone hR_sym
      · -- 1 ⊑ Rsym°: 1 ⊑ 1° ⊑ Rsym°.
        exact rel_le_trans graph_id_le_reciprocal (reciprocal_monotone hG_sym)
    have h3 : RelLe (Rsym°) (Rsym°°) := reciprocal_monotone hle
    rwa [reciprocal_invol] at h3
  -- Reflexive-transitive closure of Rsym, then equivalence closure of R.
  let hr := HasReflTransClosure.transRefClos Rsym
  let ec := equivClos_from_symm_transRefClos R Rsym hR_sym hsym hJoin hr
  refine ⟨ec.clos, equivalenceRelation_of_isEquivRel ec.isEquiv, ec.le, ?_⟩
  -- Minimality, transported through the `IsEquivRel`/`EquivalenceRelation` bridge.
  intro F hFeq hRF
  refine ec.minimal F hRF ?_
  -- EquivalenceRelation F ⟹ IsEquivRel F.
  obtain ⟨⟨h, hA, hB⟩, ⟨symF⟩, ⟨transF⟩⟩ := hFeq
  refine ⟨⟨⟨h, ?_, ?_⟩⟩, ?_, ⟨transF⟩⟩
  · simpa [graph] using hA
  · simpa [graph] using hB
  · -- F° ⊑ F: reciprocate the symmetry RelHom F F° (uses involution).
    have : RelLe (F°) (F°°) := reciprocal_monotone ⟨symF⟩
    rwa [reciprocal_invol] at this

/-- **§1.954, substantive reduction (no `sorry`)**: a PRE-TOPOS that has
    reflexive-transitive closures has coequalizers.

    Construction: from `[HasReflTransClosure 𝒞]`, `minEquiv_of_rtc` gives
    `HasMinEquivContaining` (the equivalence closure `(R ∪ R° ∪ 1)*` is the minimal
    equivalence containing `R`); then `preTopos_minEquiv_to_cocartesian` (§1.657)
    builds coequalizers via the *effective-regular* route — the minimal equivalence
    `S` containing `R = «f,g»` is the level of a cover `q : B ↠ C` (effectiveness,
    §1.951), and `q` is the coequalizer of `f, g`.  No `sorry`. -/
noncomputable def preTopos_rtc_has_coequalizers [inst : PreTopos 𝒞]
    [hRtc : @HasReflTransClosure 𝒞 _ PreTopos.toPositivePreLogos.toHasBinaryProducts
      PreTopos.toPositivePreLogos.toHasPullbacks PreTopos.toPositivePreLogos.toHasImages] :
    HasCoequalizers 𝒞 :=
  -- The `HasReflTransClosure` hypothesis is stated over the *canonical*
  -- `PreTopos → PositivePreLogos` products, the same instance
  -- `preTopos_minEquiv_to_cocartesian` resolves with.  (Pinned to avoid the
  -- `topos_has_exponentials` products instance that `[PreTopos]` also makes
  -- available — defeq, but not syntactically equal, which derails instance-implicit
  -- unification.)
  Classical.choice (preTopos_minEquiv_to_cocartesian
    (@minEquiv_of_rtc 𝒞 _ PreTopos.toPositivePreLogos.toPreLogos.toRegularCategory.toHasTerminal
      PreTopos.toPositivePreLogos.toHasBinaryProducts
      PreTopos.toPositivePreLogos.toHasPullbacks PreTopos.toPositivePreLogos.toHasImages
      PreTopos.toPositivePreLogos.toHasBinaryCoproducts hRtc))

/-- **§1.954**: A topos has coequalizers.
    Given f, g : A → B, let R = f"g, S = (R ∪ R")* (the equivalence closure).
    A topos is effective [1.951], so S is the level of some B → C.
    This B → C is the coequalizer of f and g.

    The *substantive content* is fully discharged in `preTopos_rtc_has_coequalizers`
    (no `sorry`): once `[PreTopos 𝒞]` (= effective-regular + positive pre-logos) and
    `[HasReflTransClosure 𝒞]` are available, the equivalence-closure construction
    `(R ∪ R° ∪ 1)*` (now constructive via `rtc`) plus §1.657/§1.951 yield
    coequalizers.

    **Sharpened blocker (faithful sorry).**  Synthesising the instance from bare
    `[Topos 𝒞]` needs two things this repo cannot yet provide from `Topos`:

      (1) `PreTopos 𝒞` — in particular `EffectiveRegular 𝒞` (and the underlying
          `RegularCategory`/`HasImages`/`PullbacksTransferCovers`).  This is
          `topos_is_effective` (line 161), still a `sorry` blocked on the §1.54
          capitalization lemma (the topos image construction
          `⋂{B' ↣ B | f ↦ B'}` rests on `capitalization_lemma`, S1_94:321).

      (2) `HasReflTransClosure 𝒞` — there is NO `topos_has_rtc` instance: a topos's
          reflexive-transitive closures are themselves obtained by the §1.543
          transfinite (capitalization) colimit, the same blocker as (1).

    `rtc` being now available means the *equivalence-closure* sub-problem is no
    longer the gap: the residual blocker is exactly the existence of `rtc`
    *instances* on a topos (2) on top of the §1.54-blocked effectiveness (1).  With
    both, this instance is literally `preTopos_rtc_has_coequalizers`. -/
instance topos_has_coequalizers [Topos 𝒞] : HasCoequalizers 𝒞 := by
  sorry

/-! ## §1.955  A topos is bicartesian -/

/-- **§1.955**: A topos is bicartesian: it has terminal, coterminator, binary products,
    and binary coproducts.  Follows from: topos has coequalizers [1.954], a coterminator
    [1.944], and binary coproducts [1.952, 1.946]. -/
instance topos_is_bicartesian [Topos 𝒞] : BicartesianCategory 𝒞 := by
  sorry

/-! ## §1.961  Injective objects -/

/-- **§1.961**: An object E is INJECTIVE if the functor (-, E) carries monics to epics.
    Elementary version (in a pre-topos, pushouts of monics are monic):
    E is injective iff every monic E ↣ A has a right-inverse. -/
def IsInjective [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] (E : 𝒞) : Prop :=
  ∀ {A B : 𝒞} (f : A ⟶ B), Mono f →
    ∀ (g : A ⟶ E), ∃ (h : B ⟶ E), f ≫ h = g

/-- The composite of two monics is monic (§1.41). -/
private theorem mono_comp {X Y Z : 𝒞} {m : X ⟶ Y} {n : Y ⟶ Z}
    (hm : Mono m) (hn : Mono n) : Mono (m ≫ n) := by
  intro W u v huv
  exact hm _ _ (hn _ _ (by simpa [Cat.assoc] using huv))

/-- **§1.961**: Ω is INJECTIVE in a topos.  Given a monic `f : A ↣ B` and any
    `g : A → Ω`, classify the subobject `m : S ↣ A` that `g` names, then classify
    its composite `m ≫ f : S ↣ B` to obtain `h : B → Ω`.  Because `f` is monic the
    pullback of the subobject `m ≫ f` along `f` is `m` itself, so `f ≫ h` classifies
    `m`; by uniqueness of characteristic maps `f ≫ h = g`.  (This is the elementary
    form of "Ω is injective": maps into Ω extend along monics via `classify`.) -/
theorem omega_is_injective [Topos 𝒞] :
    IsInjective (𝒞 := 𝒞) (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  intro A B f hf g
  -- m : S ↣ A is the subobject named by g (pullback of `true` along g).
  let cone := (HasPullbacks.has g (HasSubobjectClassifier.true (𝒞 := 𝒞))).cone
  let m : cone.pt ⟶ A := cone.π₁
  have hm : Mono m := by
    -- m is monic: it is the pullback of the monic `true` along g.  The other leg
    -- `cone.π₂` lands in the terminal `one`, so cones over (g, true) are determined
    -- by their first leg; joint pullback uniqueness then forces u = v.
    intro W u v huv
    have hpb := (HasPullbacks.has g (HasSubobjectClassifier.true (𝒞 := 𝒞))).cone_isPullback
    have hwu : (u ≫ m) ≫ g = (u ≫ cone.π₂) ≫ HasSubobjectClassifier.true := by
      rw [Cat.assoc, Cat.assoc, cone.w]
    obtain ⟨_, _, huniq⟩ := hpb ⟨W, u ≫ m, u ≫ cone.π₂, hwu⟩
    rw [huniq u rfl rfl, huniq v huv.symm (term_uniq _ _)]
  -- g classifies m.
  have hsq_m : m ≫ g = term cone.pt ≫ HasSubobjectClassifier.true :=
    cone.w.trans (congrArg (· ≫ HasSubobjectClassifier.true) (term_uniq cone.π₂ (term cone.pt)))
  have hg : g = HasSubobjectClassifier.classify m hm :=
    classify_eq_of_pullback m hm g hsq_m (by
      -- the chosen cone is a pullback; replace its π₂ by `term` (terminal uniqueness)
      have hpb := (HasPullbacks.has g (HasSubobjectClassifier.true (𝒞 := 𝒞))).cone_isPullback
      intro d
      obtain ⟨u, ⟨hu₁, _⟩, huniq⟩ := hpb d
      exact ⟨u, ⟨hu₁, term_uniq _ _⟩, fun w hw₁ _ => huniq w hw₁ (term_uniq _ _)⟩)
  -- h = classify(m ≫ f).
  refine ⟨HasSubobjectClassifier.classify (m ≫ f) (mono_comp hm hf), ?_⟩
  -- f ≫ h classifies m, hence f ≫ h = classify m = g.
  refine Eq.trans ?_ hg.symm
  -- m ≫ (f ≫ classify(m≫f)) = term ≫ true
  have hsq_fh : m ≫ (f ≫ HasSubobjectClassifier.classify (m ≫ f) (mono_comp hm hf))
      = term cone.pt ≫ HasSubobjectClassifier.true := by
    rw [← Cat.assoc, HasSubobjectClassifier.classify_sq (m ≫ f) (mono_comp hm hf)]
  refine classify_eq_of_pullback m hm _ hsq_fh ?_
  -- (S, m, term) is a pullback of (f ≫ classify(m≫f), true)
  · intro d
    -- d.π₁ : d.pt → A with d.π₁ ≫ (f ≫ classify(m≫f)) = d.π₂ ≫ true
    have hsq : (d.π₁ ≫ f) ≫ HasSubobjectClassifier.classify (m ≫ f) (mono_comp hm hf)
        = d.π₂ ≫ HasSubobjectClassifier.true := by rw [Cat.assoc]; exact d.w
    have hpb := HasSubobjectClassifier.classify_pullback (m ≫ f) (mono_comp hm hf)
    obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hpb ⟨d.pt, d.π₁ ≫ f, d.π₂, hsq⟩
    -- u ≫ (m≫f) = d.π₁ ≫ f.  f monic ⟹ u ≫ m = d.π₁.
    have hum : u ≫ m = d.π₁ := hf _ _ (by rw [Cat.assoc]; exact hu₁)
    refine ⟨u, ⟨hum, term_uniq _ _⟩, ?_⟩
    intro v hv₁ _
    exact huniq v (by rw [← Cat.assoc, hv₁]) (term_uniq _ _)

/-- The map f × 1_Z : A × Z → B × Z for f : A → B (mapping the left factor). -/
def prodMapLeft [HasBinaryProducts 𝒞] {A B : 𝒞} (Z : 𝒞) (f : A ⟶ B) : prod A Z ⟶ prod B Z :=
  pair (fst ≫ f) snd

/-- The contravariant exponential map E^f : E^^B → E^^A induced by f : A → B
    (§1.853).  Defined by curry(e_B ∘ (f × 1_{E^^B})), where
    e_B : B × E^^B → E is evaluation and (f × 1) : A × E^^B → B × E^^B. -/
def expMap [HasExponentials 𝒞] {A B : 𝒞} (E : 𝒞) (f : A ⟶ B) : E ^^ B ⟶ E ^^ A :=
  -- (f × 1_{E^^B}) : prod A (E^^B) → prod B (E^^B)  (left-factor map)
  -- eval_exp B E   : prod B (E^^B) → E
  curry (prodMapLeft (E ^^ B) f ≫ eval_exp B E)

/-- **§1.961**: An object E in an exponential category is INTERNALLY INJECTIVE if
    E^(−) carries monics to epics: for every monic f : A ↣ B,
    the induced map E^f : E^^B → E^^A is a cover (= epic in a regular category). -/
def IsInternallyInjective [HasExponentials 𝒞] (E : 𝒞) : Prop :=
  ∀ {A B : 𝒞} (f : A ⟶ B), Mono f → Cover (expMap E f)

/-- A SPLIT EPI (a map with a section) is a COVER.  If `s ≫ e = 1_Y`, then any
    monic `m` that `e` factors through (`g ≫ m = e`) is split epi (`(g ≫ s) ≫ m`…)
    and monic, hence iso.  Generic; used to turn the `Ω^f`-has-section argument of
    §1.961 into a cover once the section `powerMapCov f` is available. -/
theorem cover_of_section {X Y : 𝒞} (e : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ e = Cat.id Y) :
    Cover e := by
  intro C m g hm hgm
  -- m is split epi: `(s ≫ g) ≫ m = s ≫ e = 1_Y`; with m monic this gives iso.
  refine ⟨s ≫ g, ?_, ?_⟩
  · -- m ≫ (s ≫ g) = 1_C, by monic cancellation against m.
    refine hm _ _ ?_
    rw [Cat.assoc, Cat.assoc, hgm, hs, Cat.comp_id, Cat.id_comp]
  · -- (s ≫ g) ≫ m = s ≫ e = 1_Y.
    rw [Cat.assoc, hgm, hs]

/-- **DRY bridge (§1.92 ↔ §1.961)**: the §1.961 contravariant exponential action
    `expMap Ω f` on the classifier coincides with the §1.922 power-functor map
    `omegaPowContra.map f = Ω^f`.  Both are `curry (pair (fst ≫ f) snd ≫ eval)`,
    so the equality is definitional (`rfl`).  Lets §1.961 reuse the proved
    contravariant-functoriality (`map_id`, `map_comp`) of `omegaPowContra`. -/
theorem expMap_omega_eq_omegaPow [Topos 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    expMap (𝒞 := 𝒞) (HasSubobjectClassifier.omega (𝒞 := 𝒞)) f
      = (omegaPowContra (𝒞 := 𝒞)).map f := rfl

/-- **§1.961**: In a topos, Ω is internally injective.

    Freyd's proof: for monic `f : A ↣ B`, the contravariant action `Ω^f` is the
    inverse-image `[f"]` (post-composition by the reciprocal `f°`), and it has a
    LEFT INVERSE — the covariant direct image `[f] = powerMapCov f` — because `f`
    monic is equivalent to `f"f = 1` (`powerMapCov`'s defining identity).  A split
    epi is a cover, so `Ω^f` is a cover.

    **Sharpened blocker (faithful sorry).**  The section needed is exactly
    `powerMapCov f : Ω^A → Ω^B` (the direct-image action), which is an unfilled
    `sorry` in §1.92: it requires the §1.56 image factorization packaged as a
    power-object morphism together with the membership/Λ universal property of the
    power object `Ω^A = exp A Ω`.  That universal property is unavailable here
    because `exp A Ω` is opaque while `topos_has_exponentials` (S1_92) is itself a
    `sorry` (blocked on §1.543).  The DRY bridge `expMap_omega_eq_omegaPow` above
    identifies `expMap Ω f` with the proved `omegaPowContra.map f`, so once
    `powerMapCov f` and its identity `f"f = 1` are available, this is
    `Cover (expMap Ω f)` via "split epi ⟹ cover".  The residual gap is precisely
    `powerMapCov` (§1.92 keystone (2)). -/
theorem omega_is_internally_injective [Topos 𝒞] :
    IsInternallyInjective (𝒞 := 𝒞) (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  sorry

/-! ## §1.962  Ω^A is injective; every object embeds in an injective -/

/-- The right-factor product map `A × f : A × X → A × Y` is monic when `f` is.
    (Joint cancellation on `fst`/`snd`; `f` monic kills the `snd` component.) -/
private theorem prodMap_mono [HasBinaryProducts 𝒞] (A : 𝒞) {X Y : 𝒞} {f : X ⟶ Y}
    (hf : Mono f) : Mono (prodMap A X Y f) := by
  intro W u v huv
  -- u ≫ fst = v ≫ fst (from prodMap_fst) and u ≫ snd = v ≫ snd (f monic via prodMap_snd).
  have hfst : u ≫ fst = v ≫ fst := by
    have := congrArg (· ≫ fst (A := A) (B := Y)) huv
    simpa [Cat.assoc, prodMap_fst] using this
  have hsnd : u ≫ snd = v ≫ snd := by
    apply hf
    have := congrArg (· ≫ snd (A := A) (B := Y)) huv
    simpa [Cat.assoc, prodMap_snd] using this
  -- Both agree on fst and snd ⟹ equal (product extensionality).
  calc u = pair (u ≫ fst) (u ≫ snd) := pair_uniq _ _ u rfl rfl
    _ = pair (v ≫ fst) (v ≫ snd) := by rw [hfst, hsnd]
    _ = v := (pair_uniq _ _ v rfl rfl).symm

/-- Transpose naturality (in the parameter): `f ≫ curry k = curry (A×f ≫ k)`.
    Holds in any exponential category (no topos needed); it is the adjoint-transpose
    naturality of `A × −`.  Proved here from `prodMap_comp` + `curry_eval_eq`. -/
private theorem curry_precomp_exp [HasExponentials 𝒞] {A E X Y : 𝒞}
    (f : X ⟶ Y) (k : prod A Y ⟶ E) :
    f ≫ curry k = curry (prodMap A X Y f ≫ k) := by
  apply curry_unique_eq
  rw [prodMap_comp, Cat.assoc, curry_eval_eq]

/-- **§1.962**: If E is injective in an exponential category, then E^A is injective
    for any A.  Proof: (−, E^A) ≅ (− × A, E) and − × A preserves monics in any category.
    Concretely: given a monic `f : X ↣ Y` and `g : X → E^A`, uncurry `g` to
    `ĝ : A×X → E`; the map `A×f : A×X ↣ A×Y` is monic, so by injectivity of E it
    extends to `k : A×Y → E` with `(A×f) ≫ k = ĝ`; then `h = curry k` satisfies
    `f ≫ h = g` by transpose naturality. -/
theorem exp_of_injective_is_injective [HasExponentials 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {E : 𝒞} (hE : IsInjective E) (A : 𝒞) : IsInjective (E ^^ A) := by
  intro X Y f hf g
  -- ĝ : A × X → E is the uncurried g; by construction g = curry ĝ.
  let ghat : prod A X ⟶ E := prodMap A X (E ^^ A) g ≫ eval_exp A E
  have hg : g = curry ghat := curry_unique_eq rfl
  -- Extend ĝ along the monic A × f using injectivity of E.
  obtain ⟨k, hk⟩ := hE (prodMap A X Y f) (prodMap_mono A hf) ghat
  -- h = curry k.  Then f ≫ h = curry (A×f ≫ k) = curry ĝ = g.
  refine ⟨curry k, ?_⟩
  rw [curry_precomp_exp, hk, ← hg]

/-- **§1.962**: Consequently, in a topos, Ω^A is injective for all A.
    Since the singleton map embeds A into Ω^A, every object appears as a subobject
    of an injective. -/
theorem topos_every_object_embeds_in_injective [Topos 𝒞] (A : 𝒞) :
    ∃ (I : 𝒞) (m : A ⟶ I), Mono m ∧ IsInjective (𝒞 := 𝒞) I :=
  -- I = Ω^A = [A]; the singleton map Δ₁ : A ↣ [A] is monic (§1.92); [A] is injective
  -- because Ω is injective (`omega_is_injective`) and exponentials of injectives are
  -- injective (`exp_of_injective_is_injective`).
  ⟨HasSubobjectClassifier.omega (𝒞 := 𝒞) ^^ A, singletonMapCat A,
    singletonMapCat_monic A,
    exp_of_injective_is_injective omega_is_injective A⟩

/-! ## §1.964  Value-based categories -/

/-- **§1.964**: A category is VALUE-BASED if its values (= morphisms from subterminators)
    form a basis (§1.632): the class of objects of the form U (for U ≤ 1) generates
    in the sense that the representable functors {(U, −)} for subterminators U are
    collectively faithful. -/
def IsValueBased [HasTerminal 𝒞] : Prop :=
  IsGeneratingSet (𝒞 := 𝒞) (fun G => ∃ (m : G ⟶ one), Mono m)

/-- **§1.964**: In a value-based topos, Ω is a cogenerator: for any f ≠ g : A → B,
    there exists h : B → Ω such that f ≫ h ≠ g ≫ h.

    Freyd's route is `(−, Ω) = χ?(−)` plus `B' = Im(xf)` for a subterminator value
    `x : U → A` with `xf ≠ xg`.  Under this repo's *bare* `[Topos 𝒞]` that route is
    not directly available (it needs `HasImages` / image-of-`xf`, both blocked on the
    §1.54 capitalization lemma; cf. `topos_is_effective`).  We give an equivalent
    proof needing only the classifier:

    A value `x : U → A` out of a subterminator `U` (`Mono (term U)`) makes ANY map out
    of `U` monic — any two maps INTO `U` agree (`term`-uniqueness + `term U` monic).  So
    `x ≫ f : U ↣ B` is itself monic; take `h := χ(x ≫ f)`.  Then `(x≫f)≫h = term≫true`,
    and the no-separation hypothesis forces `(x≫g)≫h = term≫true` too.  `monic_is_equalizer`
    (§1.913) factors `x≫g = k ≫ (x≫f)` with `k : U → U`; subterminal collapse gives `k = id`,
    so `x≫g = x≫f`.  This holds for every subterminator value, so `IsValueBased` forces
    `f = g`, contradicting `f ≠ g`.  (Sorry-free; axioms: propext, choice, Quot.sound.) -/
theorem omega_cogenerates_in_value_based_topos [Topos 𝒞] (hVB : IsValueBased (𝒞 := 𝒞)) :
    ∀ {A B : 𝒞} (f g : A ⟶ B), f ≠ g →
      ∃ (h : B ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)), f ≫ h ≠ g ≫ h := by
  intro A B f g hfg
  -- Contrapositive: if NO `h` separates, then `f = g`, contradicting `f ≠ g`.
  apply Classical.byContradiction; intro hcon'
  -- `hcon' : ¬ ∃ h, f ≫ h ≠ g ≫ h`, i.e. every `h` fails to separate.
  have hcon : ∀ h : B ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞), f ≫ h = g ≫ h := fun h =>
    Classical.byContradiction (fun hne => hcon' ⟨h, hne⟩)
  apply hfg
  -- `hVB` reduces `f = g` to: every value `x : U → A` from a subterminator `U`
  -- has `x ≫ f = x ≫ g`.
  refine hVB f g (fun U hU x => ?_)
  obtain ⟨mU, hmU⟩ := hU
  -- A map OUT of a subterminator is monic: any two maps into `U` already agree
  -- (their composites with `term U` agree by terminal uniqueness, and `term U` is
  -- monic), so `x ≫ f` is monic with subterminal domain.
  have hsub : ∀ {Z : 𝒞} (a b : Z ⟶ U), a = b := fun a b => hmU a b (term_uniq _ _)
  have hm : Mono (x ≫ f) := fun a b _ => hsub a b
  -- Take `h := χ(x ≫ f)` (the classifier of the monic `x ≫ f : U ↣ B`).
  let h : B ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) := HasSubobjectClassifier.classify (x ≫ f) hm
  -- `x ≫ f` factors through itself, so `(x ≫ f) ≫ h = term U ≫ true`.
  have hf_sq : (x ≫ f) ≫ h = term U ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq (x ≫ f) hm
  -- From the contradiction hypothesis `f ≫ h = g ≫ h`, also `(x ≫ g) ≫ h = term U ≫ true`.
  have hg_sq : (x ≫ g) ≫ h = term U ≫ HasSubobjectClassifier.true := by
    calc (x ≫ g) ≫ h = x ≫ (g ≫ h) := Cat.assoc _ _ _
      _ = x ≫ (f ≫ h) := by rw [hcon h]
      _ = (x ≫ f) ≫ h := (Cat.assoc _ _ _).symm
      _ = term U ≫ HasSubobjectClassifier.true := hf_sq
  -- `monic_is_equalizer` turns `(x ≫ g) ≫ χ = (x ≫ g) ≫ (term ≫ true)` into a
  -- factorization `k ≫ (x ≫ f) = x ≫ g`.
  obtain ⟨_, huniv⟩ := monic_is_equalizer (x ≫ f) hm
  obtain ⟨k, hk, _⟩ := huniv (x ≫ g) (by
    rw [hg_sq, ← Cat.assoc]
    exact congrArg (· ≫ HasSubobjectClassifier.true) (term_uniq (term U) ((x ≫ g) ≫ term B)))
  -- `k : U → U` equals `id U` (subterminal), hence `x ≫ g = x ≫ f`.
  calc x ≫ f = Cat.id U ≫ (x ≫ f) := (Cat.id_comp _).symm
    _ = k ≫ (x ≫ f) := by rw [hsub (Cat.id U) k]
    _ = x ≫ g := hk

/-! ## §1.965  Internally cogenerates -/

/-- **§1.965**: An object C in an exponential category INTERNALLY COGENERATES if
    the functor C^(−) is a contravariant embedding: the maps C^f for varying f
    together distinguish morphisms.  Formally: for f ≠ g : A → B, C^f ≠ C^g. -/
def InternallyCogenerates [HasExponentials 𝒞] (C : 𝒞) : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B), expMap C f = expMap C g → f = g

/-- **§1.965**: A cogenerator internally cogenerates.
    If C cogenerates (i.e., (−, C) is an embedding) then C^(−) is also an embedding:
    for f ≠ g, T(C^f) ≠ T(C^g), hence C^f ≠ C^g. -/
theorem cogenerator_internally_cogenerates [HasExponentials 𝒞] [HasTerminal 𝒞]
    (C : 𝒞)
    (hcog : ∀ {A B : 𝒞} (f g : A ⟶ B), f ≠ g →
      ∃ (h : B ⟶ C), f ≫ h ≠ g ≫ h) :
    InternallyCogenerates C := by
  intro A B f g heq
  apply Classical.byContradiction; intro hne
  obtain ⟨h, hh⟩ := hcog f g hne
  -- expMap C f = expMap C g; curry_inj gives the uncurried identity.
  have hunc : prodMapLeft (C ^^ B) f ≫ eval_exp B C =
              prodMapLeft (C ^^ B) g ≫ eval_exp B C := curry_inj heq
  -- Let s := pair fstA (sndA ≫ curry(fstB ≫ h)) : prod A one → prod A (C^^B).
  -- Key: s ≫ prodMapLeft(k) ≫ eval_exp B C = fstA ≫ k ≫ h for any k : A → B.
  have heval_A : ∀ (k : A ⟶ B),
      pair (fst (A := A) (B := one)) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫
        prodMapLeft (C ^^ B) k ≫ eval_exp B C =
      fst (A := A) (B := one) ≫ k ≫ h := by
    intro k
    -- s ≫ prodMapLeft(k) = pair(fstA≫k)(sndA≫curry(fstB≫h))
    have step1 : pair (fst (A := A) (B := one)) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫
        prodMapLeft (C ^^ B) k =
      pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) :=
      pair_uniq _ _ _
        (by rw [Cat.assoc, prodMapLeft, fst_pair, ← Cat.assoc, fst_pair])
        (by rw [Cat.assoc, prodMapLeft, snd_pair, snd_pair])
    -- pair(fstA≫k)(sndA≫t) = pair(fstA≫k) sndAone ≫ pair fstBone (sndBone≫t), via prod B one
    have hfactor : pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) =
        (pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one)) : prod A one ⟶ prod B one) ≫
        pair (fst (A := B) (B := one)) (snd (A := B) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) :=
      (pair_uniq _ _ _
        (by rw [Cat.assoc, fst_pair, fst_pair])
        (by rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair])).symm
    calc pair (fst (A := A) (B := one)) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫
            prodMapLeft (C ^^ B) k ≫ eval_exp B C
        = pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫
            eval_exp B C := by rw [← Cat.assoc, step1]
      _ = (pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one)) : prod A one ⟶ prod B one) ≫
            pair (fst (A := B) (B := one)) (snd (A := B) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫
            eval_exp B C := by rw [hfactor, Cat.assoc]
      _ = (pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one)) : prod A one ⟶ prod B one) ≫
            (fst (A := B) (B := one) ≫ h) := by congr 1; exact curry_eval_eq _
      _ = fst (A := A) (B := one) ≫ k ≫ h := by rw [← Cat.assoc, fst_pair, Cat.assoc]
  -- Precompose hunc with s to get fstA ≫ f ≫ h = fstA ≫ g ≫ h.
  have heqh : fst (A := A) (B := one) ≫ f ≫ h = fst (A := A) (B := one) ≫ g ≫ h := by
    rw [← heval_A f, ← heval_A g]
    exact congrArg (pair (fst (A := A) (B := one)) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫ ·) hunc
  -- Cancel fstA via its right-inverse prodOneRightInv A, concluding f ≫ h = g ≫ h.
  exact hh (by
    have := congrArg (prodOneRightInv A ≫ ·) heqh
    simp only [← Cat.assoc, prodOneRightInv_fst, Cat.id_comp] at this
    exact this)

/-- **§1.965**: In a topos, Ω internally cogenerates.
    Proof: suppose Ω^f = Ω^g.  Embed the small subtopos containing f,g faithfully
    into a capital (value-based) topos; there Ω cogenerates [1.964], so f = g. -/
theorem omega_internally_cogenerates [Topos 𝒞] : InternallyCogenerates (𝒞 := 𝒞) (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  sorry

/-! ## §1.966  Progenitor -/

/-- **§1.966**: An object G is a PROGENITOR if its subobjects form a generating set:
    for any monic m : A' ↣ A that is not an iso, there exists a subobject G' ≤ G
    and a map G' → A that does not factor through A'. -/
def IsProgenitor (G : 𝒞) : Prop :=
  IsGeneratingSet (𝒞 := 𝒞) (fun X => ∃ (m : X ⟶ G), Mono m)

/-- **§1.966**: A topos is value-based iff its terminator 1 is a progenitor.
    Any Grothendieck topos has a progenitor (disjoint union of a generating set). -/
theorem topos_value_based_iff_terminal_progenitor [Topos 𝒞] :
    IsValueBased (𝒞 := 𝒞) ↔ IsProgenitor (𝒞 := 𝒞) one :=
  -- both sides unfold to `IsGeneratingSet (fun X => ∃ m : X ⟶ one, Mono m)`
  Iff.rfl

/-- **§1.966**: If G is a progenitor for a topos, then Ω^G is a cogenerator:
    given f ≠ g : A → B there exists h : B → Ω^G with f ≫ h ≠ g ≫ h.
    Proof: (−, Ω^G) and (G, Ω^(−)) are naturally equivalent (exponential adjunction),
    so Ω^G cogenerates iff (G, Ω^(−)) is an embedding; use that Ω^f ≠ Ω^g
    (Ω internally cogenerates [1.965]) and G generates to find the witness. -/
theorem progenitor_omega_exp_cogenerates [Topos 𝒞] (G : 𝒞) (hG : IsProgenitor G) :
    ∀ {A B : 𝒞} (f g : A ⟶ B), f ≠ g →
      ∃ (h : B ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) ^^ G), f ≫ h ≠ g ≫ h := by
  sorry

/-! ## §1.967  Arbitrary powers ↔ arbitrary copowers ↔ arbitrary copowers of 1 -/

/-- **§1.967**: A category has arbitrary POWERS if for every object A and index set I,
    the I-fold product of A with itself exists (i.e., A^I in the exponential sense).
    In a topos this is A^(Ω^I) but here we mean the indexed product ∏_{i:I} A.
    Formally: for every type I : Type v and object A, an indexed product of the
    constant family (fun _ : I => A) exists. -/
class HasArbitraryPowers (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryProducts 𝒞] where
  /-- For each index type I and object A, the I-fold power of A. -/
  pow : (I : Type v) → 𝒞 → 𝒞
  /-- Projection from the power to A. -/
  proj : {I : Type v} → {A : 𝒞} → I → pow I A ⟶ A
  /-- Universal property: maps into the power correspond to I-indexed families of maps into A. -/
  tupling : {I : Type v} → {A X : 𝒞} → (I → X ⟶ A) → X ⟶ pow I A
  tupling_proj : ∀ {I : Type v} {A X : 𝒞} (f : I → X ⟶ A) (i : I),
    tupling f ≫ proj i = f i
  tupling_uniq : ∀ {I : Type v} {A X : 𝒞} (f : I → X ⟶ A) (h : X ⟶ pow I A),
    (∀ i, h ≫ proj i = f i) → h = tupling f

/-- **§1.967**: A category has arbitrary COPOWERS if for every object A and index set I,
    the I-fold coproduct of A with itself exists (the copower I ⊗ A = ∐_{i:I} A). -/
class HasArbitraryCopowers (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryCoproducts 𝒞] where
  /-- For each index type I and object A, the I-fold copower of A. -/
  copow : (I : Type v) → 𝒞 → 𝒞
  /-- Injection into the copower. -/
  inj : {I : Type v} → {A : 𝒞} → I → A ⟶ copow I A
  /-- Universal property: maps out of the copower correspond to I-indexed families of maps from A. -/
  cotupling : {I : Type v} → {A X : 𝒞} → (I → A ⟶ X) → copow I A ⟶ X
  inj_cotupling : ∀ {I : Type v} {A X : 𝒞} (f : I → A ⟶ X) (i : I),
    inj i ≫ cotupling f = f i
  cotupling_uniq : ∀ {I : Type v} {A X : 𝒞} (f : I → A ⟶ X) (h : copow I A ⟶ X),
    (∀ i, inj i ≫ h = f i) → h = cotupling f

/-- A LOCALLY SMALL TOPOS is a topos in which each hom-set (A, B) is a set
    (i.e., lives in the same universe as the index types for products).
    In our universe setup: the morphisms A ⟶ B form a type in universe v,
    matching the index universe for HasProducts / HasArbitraryPowers.
    This is a property, not extra structure — Lean's universe constraint
    already guarantees it when `[Cat.{v} 𝒞]` has v ≥ universe of hom-sets.
    We record it as a typeclass for use as a hypothesis in §1.967/1.968. -/
class LocallySmallTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞

/-- **§1.967**: In a locally small topos the following are equivalent:
    (a) Arbitrary powers of objects exist.
    (b) Arbitrary copowers of objects exist.
    (c) Arbitrary copowers of 1 exist (i.e., 1 has an I-fold copower for every I).

    Each condition implies local completeness.

    Proof sketch (Freyd):
    (a)→local completeness: given {Bᵢ} ⊆ B, let f : B → ∏ᵢ Ω be the map with
      i-th component χ(Bᵢ), let g have i-th component χ(B); the equalizer is ⋂Bᵢ.
      Since the topos is well-powered (|(−,Ω)| = |Sub(−)|), arbitrary intersections
      imply arbitrary unions.
    (a)→(b): construct the copower I ⊗ A as a subobject of ∏ᵢ (A+1) using the
      complemented injections uᵢ (where uᵢuᵢ° = 1, uᵢuⱼ° = 0 for i ≠ j).
    (b)→(c): trivially, copower of A specializes to copower of 1.
    (c)→(a): ∏ᵢ A ≅ A^(I⊗1) using the exponential structure of the topos.

    We state (a)↔(b)↔(c) and each implies local completeness; all proofs are sorry
    since each direction requires substantial topos-theory infrastructure. -/
theorem topos_powers_copowers_equiv [LocallySmallTopos 𝒞]
    [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞] :
    (Nonempty (HasArbitraryPowers (𝒞 := 𝒞))) ↔
    (Nonempty (HasArbitraryCopowers (𝒞 := 𝒞))) := by
  sorry

/-- **§1.967**: Arbitrary copowers of objects exist iff arbitrary copowers of 1 exist.
    (b)↔(c): (b)→(c) is trivial; (c)→(b) uses ∐ᵢ A ≅ (∐ᵢ 1) × A in a Cartesian category
    (the copower of 1 is an I-indexed colimit, and products distribute over coproducts
    in a topos). -/
theorem topos_copowers_equiv_copowers_of_one [LocallySmallTopos 𝒞]
    [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞] :
    (Nonempty (HasArbitraryCopowers (𝒞 := 𝒞))) ↔
    (∀ (I : Type v), ∃ (cI : 𝒞) (inj : I → one ⟶ cI),
      ∀ {X : 𝒞} (f : I → one ⟶ X), ∃ (h : cI ⟶ X), ∀ i, inj i ≫ h = f i) := by
  sorry

/-- **§1.967**: Arbitrary powers imply local completeness in a locally small topos.
    Proof: let {Bᵢ ↣ B} be a family of subobjects.  Since the topos is locally small,
    (B, Ω) is a set, so the power ∏ᵢ Ω exists.  The maps χ(Bᵢ) and χ(B) : B → ∏ᵢ Ω
    have an equalizer that is ⋂ᵢ Bᵢ.  Arbitrary intersections + well-poweredness
    give arbitrary unions via the Ω-internal complement structure. -/
noncomputable def topos_powers_implies_locally_complete [LocallySmallTopos 𝒞]
    [HasBinaryProducts 𝒞] [HasEqualizers 𝒞] (hpow : HasArbitraryPowers (𝒞 := 𝒞)) :
    LocallyComplete' 𝒞 := by
  sorry

/-! ## §1.968  Complete ↔ cocomplete for locally small topoi -/

/-- **§1.968**: A locally small topos is complete iff it is cocomplete.

    (cocomplete → complete): If arbitrary coproducts exist, embed each Aᵢ into
    S = ∐ᵢ Aᵢ.  By §1.967 arbitrary powers exist (via copowers).  For each i,
    the arrow Aᵢ → S witnesses Aᵢ as a subobject of S.  Set P = ∏ᵢ S.
    The product of the embeddings Aᵢ ↣ S (pulling back via the projections)
    extracts ∏ᵢ Aᵢ as the subobject of P where all components agree.

    (complete → cocomplete): Arbitrary products imply arbitrary copowers (§1.967),
    and from copowers coproducts are built as subobjects of copowers of a cogenerator. -/
theorem topos_complete_iff_cocomplete [LocallySmallTopos 𝒞]
    [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞] [HasEqualizers 𝒞] :
    Nonempty (Complete 𝒞) ↔ Nonempty (Cocomplete 𝒞) := by
  sorry

/-! ## §1.969  Lawvere and Tierney definitions of a Grothendieck topos -/

/-- **§1.969**: The LAWVERE DEFINITION of a Grothendieck topos:
    a cocomplete topos with a generating set.
    (By §1.967 copowers of 1 give all copowers, hence all coproducts,
     so with a generating set one recovers the Giraud axioms.) -/
class LawvereGrothendieckTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞 where
  /-- Arbitrary coproducts exist. -/
  cocomplete : Cocomplete 𝒞
  /-- A small generating set. -/
  gen_set : 𝒞 → Prop
  has_gen_set : IsGeneratingSet gen_set

/-- **§1.969**: The TIERNEY DEFINITION of a Grothendieck topos:
    a topos with a progenitor and arbitrary copowers of 1.
    (The copowers-of-1 condition is equivalent to having a geometric morphism to Set.) -/
class TierneyGrothendieckTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞,
    HasBinaryCoproducts 𝒞 where
  /-- A progenitor exists. -/
  progenitor : 𝒞
  is_progenitor : IsProgenitor progenitor
  /-- Arbitrary copowers of 1 exist. -/
  copow_one : (I : Type v) → ∃ (cI : 𝒞) (inj : I → one ⟶ cI),
    ∀ {X : 𝒞} (f : I → one ⟶ X), ∃ (h : cI ⟶ X), (∀ i, inj i ≫ h = f i)

/-- **§1.969**: The Lawvere and Tierney definitions yield the same notion.
    Given the Tierney definition, use §1.966 to get Ω^G as cogenerator,
    then §1.967 (c)→(a) to get arbitrary powers, then the coproduct construction
    in the proof of §1.968. -/
theorem lawvere_eq_tierney (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞]
    [HasEqualizers 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] :
    Nonempty (LawvereGrothendieckTopos 𝒞) ↔ Nonempty (TierneyGrothendieckTopos 𝒞) := by
  sorry

end Freyd
