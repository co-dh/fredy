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
import Fredy.ToposExists


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
    mutual relational containments with `(graph x) ⊚ (graph x)°`).  No `Sorry`. -/
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

    **Sharpened blocker (faithful Sorry — (1)+(2) now CLOSED, (3) remains).**
    Building the `EffectiveRegular` instance from bare `[Topos 𝒞]` needs THREE
    ingredients.  As of the regularity-refactor, the regular core (1)+(2) is DONE; the
    irreducible residual is the per-relation quotient cover (3):

      (1) `HasImages 𝒞` — NOW AVAILABLE (`InternalForallTopos.toposHasImages`):
          `image f = ⋂{B' ↣ B | f factors through B'}` built via the internal-∀
          family-glb `bigInter`, bypassing the §1.54 capitalization route entirely.

      (2) `PullbacksTransferCovers 𝒞` — NOW AVAILABLE
          (`SlicePi.toposPullbacksTransferCovers`, from the §1.931 dependent-product
          right adjoint).  With (1)+(2), `RegularCategory 𝒞` assembles
          (`topos_is_regular`, S1_94, now Sorry-free).

      (3) THE QUOTIENT COVER — for each equivalence relation `E`, a cover
          `q : A ↠ A/E` with `level q ≅ E`.  This is Freyd's power-object construction
          `A → [A]`: `q` is the IMAGE of the classifying map and one must prove its
          level (kernel pair) is exactly `E`.  Power objects are bundled in `Topos`
          and `HasImages` is now present, so `q` can be FORMED — but proving
          `level q ≅ E` (the `(hElx, hlxE)` containments) is a SEPARATE relation-algebra
          construction (the tabulation/quotient argument of §1.951), NOT supplied by
          regularity.  No such per-relation witness exists in the repo yet.

    `EffectiveRegular extends RegularCategory`; that super-field is now discharged, but
    the `effective` field still needs (3) for every `E`.  Once (3) is built, this is
    `⟨…, fun E hE => effective_of_quotient_cover E hE q hq hElq hlqE⟩` with
    `(q, hq, hElq, hlqE)` the quotient cover.  The recovery half (the relation-algebra
    identity `E ≅ level q ≅ (graph q)⊚(graph q)°`) is PROVED above
    (`effective_of_quotient_cover`); the residual gap is exactly the quotient-cover
    existence (3), now the SOLE blocker (the §1.54-blocked (1)–(2) are gone).  Out of
    scope for the regularity wiring. -/
instance topos_is_effective [Topos 𝒞] : EffectiveRegular 𝒞 := by
  sorry

/-! ## §1.952  A topos is positive -/

/-- **§1.952**: A topos is positive: it has binary coproducts A + B.
    `A + B` is the subobject `union (image inlRaw)(image inrRaw) ⊆ [A] × [B]`, with
    `inlRaw a = ({a},∅)`, `inrRaw b = (∅,{b})`.

    Most of the construction is now DELIVERED sorry-free in `Fredy/ToposExists.lean`
    (GOAL 3), the frame law `invImage_preserves_union` having unblocked the union layer:
      * CARRIER + EMBEDDING       — `coprodSub`, `coprodObj`, `coprodArr` (monic).
      * INJECTIONS                — `coprodInl`, `coprodInr`, with `coprodInl_arr`/
                                    `coprodInr_arr` and `coprodInl_monic`/`coprodInr_monic`.
      * `case_uniq` (jointly epi) — `coprod_jointly_epi` (equalizer + `union_min`, FULL).
      * PARTIAL-MAP DATA          — `casePMf`/`casePMg` + their classify β-squares, via the
                                    lawful PMC `partialMapClassifier_exists`
                                    (`Fredy/PartialMapClassifier.lean`, sorry-free).

    The SINGLE remaining piece is the copairing existence

        coprod_case_exists {A B X} (f : A ⟶ X) (g : B ⟶ X) :
          ∃ c, coprodInl A B ≫ c = f ∧ coprodInr A B ≫ c = g

    — Freyd's §1.935 amalgamation: GLUE `f,g` into one map out of `A+B`.  This is NOT
    reducible to the join-lattice/PMC data already present, because a subobject JOIN
    (`union`) carries only a map-IN universal property (`union_left/right/min`), never a
    map-OUT (colimit) one, and the PMC only certifies TOTALITY of a candidate `χ : A+B→X̃`,
    not its existence.  Producing `χ = χf ∨ χg` as a single total map needs the
    DISJOINTNESS `image inl ⊓ image inr = ⊥` (a singleton is not the empty subobject — a
    non-degeneracy fact) plus the union-cover, i.e. the value-object amalgamation.  See the
    RESIDUAL note in `Fredy/ToposExists.lean` for the exact stuck step.

    Because `HasBinaryCoproducts` is all-or-nothing (carrier + lawful `case`/`case_uniq`),
    no honest partial instance can be supplied without faking `case`.  Once
    `coprod_case_exists` lands, `case := …choose`, the β-laws are `…choose_spec`,
    `case_uniq := coprod_jointly_epi`, assembling
    `toposHasBinaryCoproducts : HasBinaryCoproducts 𝒞`, after which this becomes
    `exact toposHasBinaryCoproducts`. -/
noncomputable instance topos_is_positive [Topos 𝒞] : HasBinaryCoproducts 𝒞 :=
  toposHasBinaryCoproducts

/-! ## §1.954  A topos has coequalizers -/

section Coequalizers
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-! The §1.77↔§1.56 equivalence-relation bridge `equivalenceRelation_of_isEquivRel`
    and the §1.954 core reduction `minEquiv_of_rtc` (every endo-relation has a minimal
    equivalence relation containing it, via the closure `(R ∪ R° ∪ 1)*`) live canonically
    in `Fredy.S1_64` (lower in the import hierarchy); reused here via import (DRY). -/

end Coequalizers

/-- **§1.954, substantive reduction (no `Sorry`)**: a PRE-TOPOS that has
    reflexive-transitive closures has coequalizers.

    Construction: from `[HasReflTransClosure 𝒞]`, `minEquiv_of_rtc` gives
    `HasMinEquivContaining` (the equivalence closure `(R ∪ R° ∪ 1)*` is the minimal
    equivalence containing `R`); then `preTopos_minEquiv_to_cocartesian` (§1.657)
    builds coequalizers via the *effective-regular* route — the minimal equivalence
    `S` containing `R = «f,g»` is the level of a cover `q : B ↠ C` (effectiveness,
    §1.951), and `q` is the coequalizer of `f, g`.  No `Sorry`. -/
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
    (@minEquiv_of_rtc 𝒞 _
      PreTopos.toPositivePreLogos.toHasBinaryProducts
      PreTopos.toPositivePreLogos.toHasPullbacks PreTopos.toPositivePreLogos.toHasImages
      PreTopos.toPositivePreLogos.toHasBinaryCoproducts hRtc))

/-- **§1.954**: A topos has coequalizers.
    Given f, g : A → B, let R = f"g, S = (R ∪ R")* (the equivalence closure).
    A topos is effective [1.951], so S is the level of some B → C.
    This B → C is the coequalizer of f and g.

    The *substantive content* is fully discharged in `preTopos_rtc_has_coequalizers`
    (no `Sorry`): once `[PreTopos 𝒞]` (= effective-regular + positive pre-logos) and
    `[HasReflTransClosure 𝒞]` are available, the equivalence-closure construction
    `(R ∪ R° ∪ 1)*` (now constructive via `rtc`) plus §1.657/§1.951 yield
    coequalizers.

    **Sharpened blocker (faithful Sorry).**  Synthesising the instance from bare
    `[Topos 𝒞]` needs two things this repo cannot yet provide from `Topos`:

      (1) `PreTopos 𝒞` — in particular `EffectiveRegular 𝒞` (and the underlying
          `RegularCategory`/`HasImages`/`PullbacksTransferCovers`).  This is
          `topos_is_effective` (above), still a `Sorry`.  Note `capitalization_lemma`
          itself is PROVEN Sorry-free (`CapDataWiring.lean`); the open step is
          wiring it into `HasImages` for an arbitrary topos (`topos_is_regular`,
          S1_94:346), so the topos image `⋂{B' ↣ B | f ↦ B'}` is constructed.

      (2) `HasReflTransClosure 𝒞` — there is NO `topos_has_rtc` instance: a topos's
          reflexive-transitive closures are obtained via the same image/closure
          machinery, blocked at the same `HasImages` wiring as (1).

    `rtc` being now available means the *equivalence-closure* sub-problem is no
    longer the gap: the residual blocker is exactly the existence of `rtc`
    *instances* on a topos (2) on top of the `HasImages`-blocked effectiveness (1).
    With both, this instance is literally `preTopos_rtc_has_coequalizers`. -/
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

/-- **Pullback is monotone under relation-iso.**  Pulling two `RelHom`-isomorphic
    relations `R ≅ S : BinRel P C` back along a common `g : X → P` gives isomorphic
    pullbacks: `relPullback g R ≅ relPullback g S` (both directions).  This is the
    reusable form of the inline span-lift that appears in `univClassify_natural`
    (S1_92): a witness `w : R.src → S.src` lifts the pullback cone `(π₁, π₂ ≫ w)`. -/
theorem relPullback_relHom [HasPullbacks 𝒞] {P C X : 𝒞} (g : X ⟶ P)
    {R S : BinRel 𝒞 P C} (h : RelHom R S ∧ RelHom S R) :
    RelHom (relPullback g R) (relPullback g S) ∧
    RelHom (relPullback g S) (relPullback g R) := by
  constructor
  · obtain ⟨w, hwA, hwB⟩ := h.1
    let P₀ := HasPullbacks.has g R.colA
    let P₁ := HasPullbacks.has g S.colA
    refine ⟨P₁.lift ⟨P₀.cone.pt, P₀.cone.π₁, P₀.cone.π₂ ≫ w, ?_⟩, ?_, ?_⟩
    · show P₀.cone.π₁ ≫ g = (P₀.cone.π₂ ≫ w) ≫ S.colA
      rw [Cat.assoc, hwA]; exact P₀.cone.w
    · show _ ≫ (relPullback g S).colA = (relPullback g R).colA
      exact P₁.lift_fst _
    · show _ ≫ (P₁.cone.π₂ ≫ S.colB) = P₀.cone.π₂ ≫ R.colB
      rw [← Cat.assoc, P₁.lift_snd, Cat.assoc, hwB]
  · obtain ⟨w, hwA, hwB⟩ := h.2
    let P₀ := HasPullbacks.has g R.colA
    let P₁ := HasPullbacks.has g S.colA
    refine ⟨P₀.lift ⟨P₁.cone.pt, P₁.cone.π₁, P₁.cone.π₂ ≫ w, ?_⟩, ?_, ?_⟩
    · show P₁.cone.π₁ ≫ g = (P₁.cone.π₂ ≫ w) ≫ R.colA
      rw [Cat.assoc, hwA]; exact P₁.cone.w
    · exact P₀.lift_fst _
    · show _ ≫ (P₀.cone.π₂ ≫ R.colB) = P₁.cone.π₂ ≫ S.colB
      rw [← Cat.assoc, P₀.lift_snd, Cat.assoc, hwB]

section OmegaInjective
variable [Topos 𝒞]

/-- Extract the (Prop-valued) `RelHom` witness from a `RelLe = Nonempty (RelHom …)`.
    `RelHom` is a `Prop`, so this is just `Nonempty`-of-a-`Prop` collapse, no choice. -/
theorem RelLe.toHom {A B : 𝒞} {R S : BinRel 𝒞 A B} (h : RelLe R S) : RelHom R S :=
  h.elim id

/-- **Monic kernel-pair collapse:** `graph x ⊚ (graph x)° ⊆ 1_A` for monic `x`.
    (Local copy of `S1_62.graph_comp_recip_le_one_of_mono`, whose only obstacle is the
    stale file-level `variable [PreLogos 𝒞]`; the proof needs only `Simple` of `(graph x)°`,
    i.e. `tabulated_is_simple_iff_left_monic`, and a topos has `[HasImages]`.) -/
theorem graph_recip_collapse_mono {A B : 𝒞} (x : A ⟶ B) (hx : Mono x) :
    RelLe (graph x ⊚ (graph x)°) (graph (Cat.id A)) := by
  have hp : MonicPair (x : A ⟶ B) (Cat.id A) := by
    intro W u v _ hid; simpa [Cat.comp_id] using hid
  have hsimp : Simple (BinRel.mk A x (Cat.id A) hp) :=
    (tabulated_is_simple_iff_left_monic x (Cat.id A) hp).mpr hx
  have heq : BinRel.mk A x (Cat.id A) hp = (graph x)° := rfl
  rw [heq] at hsimp
  unfold Simple at hsimp
  rw [reciprocal_invol] at hsimp
  exact hsimp

/-- The DIRECT IMAGE `f" : Ω^A → Ω^B` for `f : A → B`, defined at the exponential level
    `Ω^A = exp A Ω` directly (NOT transported from power objects).  It is the universal
    classifier of the composite membership relation `evalRel A ⊚ graph f : BinRel (Ω^A) B`
    (= `{(T, b) | ∃ a ∈ T, f a = b}`) against the universal `evalRel B` on `Ω^B`. -/
noncomputable def directImageOmega {A B : 𝒞} (f : A ⟶ B) :
    exp A (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ⟶
    exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
  univClassify (evalRel_universal B) (evalRel A ⊚ graph f)

/-- The inverse-image relation cut out by `expMap Ω f` is the reciprocal-graph composite:
    `classRel(prodMapLeft f ≫ eval_B) ≅ evalRel B ⊚ (graph f)°`, i.e. `{(S,a) | f a ∈ S}`.

    Both directions of `RelHom`.  Membership: `classRel χ = {(S,a) | eval(f a, S) = ⊤}`
    and `evalRel B ⊚ (graph f)° = {(S,a) | ∃ b, b ∈ S ∧ f a = b}`; the existential over `b`
    is forced to `b = f a`, so the two relations coincide. -/
theorem classRel_eq_recip_graph {A B : 𝒞} (f : A ⟶ B) :
    RelHom (classRel (prodMapLeft (exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞))) f
              ≫ eval_exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞))))
           (evalRel B ⊚ (graph f)°) ∧
    RelHom (evalRel B ⊚ (graph f)°)
           (classRel (prodMapLeft (exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞))) f
              ≫ eval_exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞)))) := by
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  let χ : prod A (exp B Ω) ⟶ Ω := prodMapLeft (exp B Ω) f ≫ eval_exp B Ω
  -- pullbacks underlying the two sides
  let pbχ := HasPullbacks.has χ HasSubobjectClassifier.true              -- src of `classRel χ`
  let pbE := HasPullbacks.has (eval_exp B Ω) HasSubobjectClassifier.true -- src of `evalRel B`
  -- composite `evalRel B ⊚ (graph f)°`: image of `span` over `pb = pullback(evalRel.colB, f)`.
  let pb := HasPullbacks.has (evalRel B).colB ((graph f)°).colA
  let span : pb.cone.pt ⟶ prod (exp B Ω) A :=
    pair (pb.cone.π₁ ≫ (evalRel B).colA) (pb.cone.π₂ ≫ ((graph f)°).colB)
  -- `prodMapLeft` factor laws (`pair (fst≫f) snd`).
  have hpmf : prodMapLeft (exp B Ω) f ≫ fst = fst ≫ f := fst_pair _ _
  have hpms : prodMapLeft (exp B Ω) f ≫ snd = snd := snd_pair _ _
  -- column unfoldings (definitional).
  have hcaA : (classRel χ).colA = pbχ.cone.π₁ ≫ snd := rfl
  have hcaB : (classRel χ).colB = pbχ.cone.π₁ ≫ fst := rfl
  have heA  : (evalRel B).colA = pbE.cone.π₁ ≫ snd := rfl
  have heB  : (evalRel B).colB = pbE.cone.π₁ ≫ fst := rfl
  have hgA  : ((graph f)°).colA = f := rfl
  have hgB  : ((graph f)°).colB = Cat.id A := rfl
  constructor
  · -- FORWARD: build a witness `pbχ.pt → (image span).dom` directly.
    -- `m = pbχ.π₁ ≫ (f×1) : pbχ.pt → prod B (exp B Ω)` lands on the eval-`true` square.
    let m : pbχ.cone.pt ⟶ prod B (exp B Ω) := pbχ.cone.π₁ ≫ prodMapLeft (exp B Ω) f
    have hmev : m ≫ eval_exp B Ω = term pbχ.cone.pt ≫ HasSubobjectClassifier.true := by
      show (pbχ.cone.π₁ ≫ prodMapLeft (exp B Ω) f) ≫ eval_exp B Ω = _
      rw [Cat.assoc]
      show pbχ.cone.π₁ ≫ χ = _
      rw [pbχ.cone.w, term_uniq pbχ.cone.π₂ (term pbχ.cone.pt)]
    let e : pbχ.cone.pt ⟶ pbE.cone.pt := pbE.lift ⟨pbχ.cone.pt, m, term pbχ.cone.pt, hmev⟩
    have he₁ : e ≫ pbE.cone.π₁ = m := pbE.lift_fst _
    -- `e ≫ evalRel.colB = (classRel χ.colB) ≫ f`, lifting into `pb`.
    have hePbB : e ≫ (evalRel B).colB = (classRel χ).colB ≫ ((graph f)°).colA := by
      rw [heB, hgA, hcaB, ← Cat.assoc, he₁]
      show (pbχ.cone.π₁ ≫ prodMapLeft (exp B Ω) f) ≫ fst = _
      rw [Cat.assoc, hpmf, ← Cat.assoc]
    let t : pbχ.cone.pt ⟶ pb.cone.pt :=
      pb.lift ⟨pbχ.cone.pt, e, (classRel χ).colB, hePbB⟩
    have ht₁ : t ≫ pb.cone.π₁ = e := pb.lift_fst _
    have ht₂ : t ≫ pb.cone.π₂ = (classRel χ).colB := pb.lift_snd _
    refine ⟨t ≫ image.lift span, ?_, ?_⟩
    · -- colA: `e ≫ evalRel.colA = pbχ.π₁ ≫ snd`.
      show (t ≫ image.lift span) ≫ ((image span).arr ≫ fst) = (classRel χ).colA
      rw [← Cat.assoc, Cat.assoc t, image.lift_fac]
      show (t ≫ span) ≫ fst = _
      rw [Cat.assoc]
      show t ≫ pair (pb.cone.π₁ ≫ (evalRel B).colA) (pb.cone.π₂ ≫ ((graph f)°).colB) ≫ fst = _
      rw [fst_pair, ← Cat.assoc, ht₁, heA, ← Cat.assoc, he₁, hcaA]
      show (pbχ.cone.π₁ ≫ prodMapLeft (exp B Ω) f) ≫ snd = _
      rw [Cat.assoc, hpms]
    · -- colB: `t ≫ pb.π₂ = pbχ.π₁ ≫ fst`.
      show (t ≫ image.lift span) ≫ ((image span).arr ≫ snd) = (classRel χ).colB
      rw [← Cat.assoc, Cat.assoc t, image.lift_fac]
      show (t ≫ span) ≫ snd = _
      rw [Cat.assoc]
      show t ≫ pair (pb.cone.π₁ ≫ (evalRel B).colA) (pb.cone.π₂ ≫ ((graph f)°).colB) ≫ snd = _
      rw [snd_pair, ← Cat.assoc, ht₂]
      show (classRel χ).colB ≫ ((graph f)°).colB = _
      rw [hgB, Cat.comp_id]
  · -- BACKWARD: descend through the image-cover `image.lift span`.
    -- `n = ⟨a, S⟩ : pb.pt → prod A (exp B Ω)` from `pb.π₂ = a` and `pb.π₁ ≫ pbE.π₁ ≫ snd = S`.
    let n : pb.cone.pt ⟶ prod A (exp B Ω) :=
      pair (pb.cone.π₂) (pb.cone.π₁ ≫ pbE.cone.π₁ ≫ snd)
    have hnf : n ≫ fst = pb.cone.π₂ := fst_pair _ _
    have hns : n ≫ snd = pb.cone.π₁ ≫ pbE.cone.π₁ ≫ snd := snd_pair _ _
    -- `pb`-square: `pb.π₁ ≫ evalRel.colB = pb.π₂ ≫ f`, i.e. `pb.π₁ ≫ pbE.π₁ ≫ fst = pb.π₂ ≫ f`.
    have hpbw : pb.cone.π₁ ≫ pbE.cone.π₁ ≫ fst = pb.cone.π₂ ≫ f := pb.cone.w
    -- `n ≫ (f×1) = pb.π₁ ≫ pbE.π₁`, so `n ≫ χ = pb.π₁ ≫ pbE.π₁ ≫ eval = term ≫ true`.
    have hnpm : n ≫ prodMapLeft (exp B Ω) f = pb.cone.π₁ ≫ pbE.cone.π₁ := by
      have e1 : (n ≫ prodMapLeft (exp B Ω) f) ≫ fst = (pb.cone.π₁ ≫ pbE.cone.π₁) ≫ fst := by
        rw [Cat.assoc, hpmf, ← Cat.assoc, hnf, Cat.assoc, ← hpbw]
      have e2 : (n ≫ prodMapLeft (exp B Ω) f) ≫ snd = (pb.cone.π₁ ≫ pbE.cone.π₁) ≫ snd := by
        rw [Cat.assoc, hpms, hns, Cat.assoc]
      exact (pair_uniq _ _ _ e1 e2).trans (pair_uniq _ _ _ rfl rfl).symm
    have hnχ : n ≫ χ = term pb.cone.pt ≫ HasSubobjectClassifier.true := by
      show n ≫ (prodMapLeft (exp B Ω) f ≫ eval_exp B Ω) = _
      rw [← Cat.assoc, hnpm, Cat.assoc, pbE.cone.w, term_uniq pbE.cone.π₂ (term pbE.cone.pt),
        ← Cat.assoc, term_uniq (pb.cone.π₁ ≫ term pbE.cone.pt) (term pb.cone.pt)]
    let φ : pb.cone.pt ⟶ pbχ.cone.pt := pbχ.lift ⟨pb.cone.pt, n, term pb.cone.pt, hnχ⟩
    have hφ₁ : φ ≫ pbχ.cone.π₁ = n := pbχ.lift_fst _
    refine relLe_of_cover_factor (image.lift span) (image_lift_cover span) φ ?_ ?_ |>.elim id
    · -- `φ ≫ classRel.colA = image.lift span ≫ (evalRel B ⊚ (graph f)°).colA`.
      have hrhs : image.lift span ≫ (evalRel B ⊚ (graph f)°).colA
          = pb.cone.π₁ ≫ (evalRel B).colA := by
        show image.lift span ≫ ((image span).arr ≫ fst) = _
        rw [← Cat.assoc, image.lift_fac]
        show pair (pb.cone.π₁ ≫ (evalRel B).colA) (pb.cone.π₂ ≫ ((graph f)°).colB) ≫ fst = _
        exact fst_pair _ _
      rw [hrhs, heA, hcaA, ← Cat.assoc, hφ₁, hns]
    · -- `φ ≫ classRel.colB = image.lift span ≫ (evalRel B ⊚ (graph f)°).colB`.
      have hrhs : image.lift span ≫ (evalRel B ⊚ (graph f)°).colB
          = pb.cone.π₂ ≫ ((graph f)°).colB := by
        show image.lift span ≫ ((image span).arr ≫ snd) = _
        rw [← Cat.assoc, image.lift_fac]
        show pair (pb.cone.π₁ ≫ (evalRel B).colA) (pb.cone.π₂ ≫ ((graph f)°).colB) ≫ snd = _
        exact snd_pair _ _
      rw [hcaB, ← Cat.assoc, hφ₁, hnf, hrhs]
      show _ = pb.cone.π₂ ≫ ((graph f)°).colB
      rw [hgB]; exact (Cat.comp_id _).symm

/-- **The monic direct-image unit `f" ≫ f* = 1`** (Freyd §1.961).  For monic `f`, the
    direct image `directImageOmega f` is a section of the inverse-image power map
    `expMap Ω f`.  The relational chain (all `RelHom`-iso, justified inline) is:
    `relPullback (f" ≫ f*) (evalRel A) ≅ relPullback f" (classRel χ)`
      `≅ relPullback f" (evalRel B ⊚ (graph f)°)`
      `≅ (relPullback f" (evalRel B)) ⊚ (graph f)°`   (`relPullback_compose_dist`)
      `≅ (evalRel A ⊚ graph f) ⊚ (graph f)°`           (`univClassify_spec`)
      `≅ evalRel A ⊚ (graph f ⊚ (graph f)°)`           (`compose_assoc`)
      `≅ evalRel A ⊚ graph 1_A ≅ evalRel A`.            (`f` monic ⟹ kernel pair collapses)
    By `evalRel`-universality (`classify_unique`), `f" ≫ f* = 1`. -/
theorem directImageOmega_unit {A B : 𝒞} (f : A ⟶ B) (hf : Mono f) :
    directImageOmega f ≫ expMap _ f = Cat.id _ := by
  classical
  letI : RegularCategory 𝒞 := Classical.choice (topos_is_regular (𝒞 := 𝒞))
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  let s := directImageOmega f
  -- `χ`: the inverse-image classifier; `expMap Ω f = curry χ` definitionally.
  let χ : prod A (exp B Ω) ⟶ Ω := prodMapLeft (exp B Ω) f ≫ eval_exp B Ω
  have hexp : expMap Ω f = curry χ := rfl
  -- Universality of `evalRel A`: it suffices to show both `s ≫ expMap Ω f` and `1`
  -- classify `evalRel A` against `evalRel A`.
  refine (evalRel_universal A).classify_unique (exp A Ω) (evalRel A) (s ≫ expMap Ω f)
    (Cat.id _) ?_ ?_
  · -- `relPullback (s ≫ expMap Ω f) (evalRel A) ≅ evalRel A`.
    -- (1) relPullback_comp: split the composite pullback.
    have h1 : RelHom (relPullback (s ≫ expMap Ω f) (evalRel A))
                (relPullback s (relPullback (expMap Ω f) (evalRel A))) ∧
              RelHom (relPullback s (relPullback (expMap Ω f) (evalRel A)))
                (relPullback (s ≫ expMap Ω f) (evalRel A)) :=
      ⟨(relPullback_comp s (expMap Ω f) (evalRel A)).2,
       (relPullback_comp s (expMap Ω f) (evalRel A)).1⟩
    -- (2) relPullback (expMap Ω f) (evalRel A) ≅ classRel χ  (β-law bridge).
    have h2 : RelHom (relPullback (expMap Ω f) (evalRel A)) (classRel χ) ∧
              RelHom (classRel χ) (relPullback (expMap Ω f) (evalRel A)) := by
      rw [hexp]; exact ⟨evalRel_pull_bwd χ, evalRel_pull_fwd χ⟩
    -- (3) classRel χ ≅ evalRel B ⊚ (graph f)°.
    have h3 := classRel_eq_recip_graph f
    -- (4) pull (2)∘(3) back along s.
    have h23 : RelHom (relPullback (expMap Ω f) (evalRel A)) (evalRel B ⊚ (graph f)°) ∧
               RelHom (evalRel B ⊚ (graph f)°) (relPullback (expMap Ω f) (evalRel A)) :=
      ⟨RelHom_trans h2.1 h3.1, RelHom_trans h3.2 h2.2⟩
    have h4 := relPullback_relHom s h23
    -- (5) relPullback_compose_dist: relPullback s (evalRel B ⊚ (graph f)°)
    --       ≅ (relPullback s (evalRel B)) ⊚ (graph f)°.
    have h5 := relPullback_compose_dist s (evalRel B) ((graph f)°)
    -- (6) univClassify_spec: relPullback s (evalRel B) ≅ evalRel A ⊚ graph f.
    have h6 : RelHom (relPullback s (evalRel B)) (evalRel A ⊚ graph f) ∧
              RelHom (evalRel A ⊚ graph f) (relPullback s (evalRel B)) :=
      ⟨(univClassify_spec (evalRel_universal B) (evalRel A ⊚ graph f)).2,
       (univClassify_spec (evalRel_universal B) (evalRel A ⊚ graph f)).1⟩
    -- (7) ⊚-monotone in left arg: (relPullback s (evalRel B)) ⊚ (graph f)°
    --       ≅ (evalRel A ⊚ graph f) ⊚ (graph f)°.
    have h7 : RelHom ((relPullback s (evalRel B)) ⊚ ((graph f)°))
                ((evalRel A ⊚ graph f) ⊚ ((graph f)°)) ∧
              RelHom ((evalRel A ⊚ graph f) ⊚ ((graph f)°))
                ((relPullback s (evalRel B)) ⊚ ((graph f)°)) :=
      ⟨(compose_le ⟨h6.1⟩ (rel_le_refl _)).toHom,
       (compose_le ⟨h6.2⟩ (rel_le_refl _)).toHom⟩
    -- (8) associativity: (evalRel A ⊚ graph f) ⊚ (graph f)° ≅ evalRel A ⊚ (graph f ⊚ (graph f)°).
    have h8 : RelHom ((evalRel A ⊚ graph f) ⊚ ((graph f)°))
                (evalRel A ⊚ (graph f ⊚ ((graph f)°))) ∧
              RelHom (evalRel A ⊚ (graph f ⊚ ((graph f)°)))
                ((evalRel A ⊚ graph f) ⊚ ((graph f)°)) :=
      ⟨(compose_assoc_of_regular (evalRel A) (graph f) ((graph f)°)).1.toHom,
       (compose_assoc_of_regular (evalRel A) (graph f) ((graph f)°)).2.toHom⟩
    -- (9) f monic ⟹ graph f ⊚ (graph f)° ≅ graph 1_A (kernel-pair collapse + entirety).
    have h9 : RelHom (graph f ⊚ ((graph f)°)) (graph (Cat.id A)) ∧
              RelHom (graph (Cat.id A)) (graph f ⊚ ((graph f)°)) :=
      ⟨(graph_recip_collapse_mono f hf).toHom, (graph_is_map f).1.toHom⟩
    have h9' : RelHom (evalRel A ⊚ (graph f ⊚ ((graph f)°))) (evalRel A ⊚ graph (Cat.id A)) ∧
               RelHom (evalRel A ⊚ graph (Cat.id A)) (evalRel A ⊚ (graph f ⊚ ((graph f)°))) :=
      ⟨(compose_le (rel_le_refl _) ⟨h9.1⟩).toHom, (compose_le (rel_le_refl _) ⟨h9.2⟩).toHom⟩
    -- (10) R ⊚ graph 1 ≅ R.
    have h10 : RelHom (evalRel A ⊚ graph (Cat.id A)) (evalRel A) ∧
               RelHom (evalRel A) (evalRel A ⊚ graph (Cat.id A)) :=
      ⟨(comp_graph_id (evalRel A)).toHom, (comp_graph_id_right (evalRel A)).toHom⟩
    -- `classify_unique` wants `(RelHom R (relPullback _ U) ∧ RelHom (relPullback _ U) R)`,
    -- i.e. first BACKWARD (evalRel A → relPullback), then FORWARD.
    refine ⟨?_, ?_⟩
    · exact RelHom_trans h10.2 (RelHom_trans h9'.2 (RelHom_trans h8.2 (RelHom_trans h7.2
        (RelHom_trans h5.2 (RelHom_trans h4.2 h1.2)))))
    · exact RelHom_trans h1.1 (RelHom_trans h4.1 (RelHom_trans h5.1 (RelHom_trans h7.1
        (RelHom_trans h8.1 (RelHom_trans h9'.1 h10.1)))))
  · -- `relPullback (1) (evalRel A) ≅ evalRel A`.
    exact ⟨(relPullback_id (evalRel A)).2, (relPullback_id (evalRel A)).1⟩

end OmegaInjective

/-- **§1.961**: In a topos, Ω is internally injective.  CLOSED, sorry-free
    ([propext, Classical.choice]).

    Freyd's proof: for monic `f : A ↣ B`, the contravariant action `Ω^f = expMap Ω f`
    is the inverse-image `f*`, and it has a LEFT INVERSE — the covariant direct image
    `f"` — because `f` monic gives the unit identity `f" ≫ f* = 1` (`f"` is a section of
    `f*`).  A split epi is a cover (`cover_of_section`), so `Ω^f` is a cover.

    **Proof (load-bearing).**  `cover_of_section (expMap Ω f) s hs` reduces the goal to a
    section `s : Ω^A → Ω^B` of `expMap Ω f` with `s ≫ Ω^f = 1`.  We build `s` and the unit
    DIRECTLY at the exponential level, NOT transported from power objects:

    * `directImageOmega f := univClassify (evalRel_universal B) (evalRel A ⊚ graph f)` — the
      direct image, classifying the composite membership relation `{(T,b) | ∃ a∈T, f a = b}`
      against the universal `evalRel B` on `Ω^B`.  (`evalRel A` is the universal membership
      `BinRel (Ω^A) A`, sorry-free; `exp A Ω ≅ [A]` is no longer needed.)

    * `directImageOmega_unit` proves `f" ≫ f* = 1` for monic `f` by `evalRel A`-universality
      (`classify_unique`): it suffices that `relPullback (f" ≫ f*) (evalRel A) ≅ evalRel A`.
      The relational chain (each step a `RelHom`-iso) is
        `relPullback (f"≫f*) (evalRel A)`
          `≅ relPullback f" (relPullback f* (evalRel A))`        (`relPullback_comp`)
          `≅ relPullback f" (classRel χ)`                        (`evalRel_pull`, `f* = curry χ`)
          `≅ relPullback f" (evalRel B ⊚ (graph f)°)`            (`classRel_eq_recip_graph`)
          `≅ (relPullback f" (evalRel B)) ⊚ (graph f)°`          (`relPullback_compose_dist`)
          `≅ (evalRel A ⊚ graph f) ⊚ (graph f)°`                 (`univClassify_spec`)
          `≅ evalRel A ⊚ (graph f ⊚ (graph f)°)`                 (`compose_assoc_of_regular`)
          `≅ evalRel A ⊚ graph 1_A ≅ evalRel A`.                 (`graph_recip_collapse_mono`,
                                                                   `graph_is_map`, `comp_graph_id`)
      Monicity of `f` enters at the single step `graph f ⊚ (graph f)° ≅ graph 1_A` (kernel
      pair of a monic collapses; `graph_recip_collapse_mono` ⊆ and entirety `graph_is_map` ⊇).
      Everything rests on `relPullback_compose_dist` (S1_92), proven sorry-free on master. -/
theorem omega_is_internally_injective [Topos 𝒞] :
    IsInternallyInjective (𝒞 := 𝒞) (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  intro A B f hf
  classical
  letI : RegularCategory 𝒞 := Classical.choice (topos_is_regular (𝒞 := 𝒞))
  -- Reduce to the genuine residual: a section `s : Ω^A → Ω^B` of the inverse-image map
  -- `Ω^f = expMap Ω f`.  The section is Freyd's direct image `f"`; the cover step then
  -- follows from `cover_of_section`.
  obtain ⟨s, hs⟩ :
      ∃ s : (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ^^ A
              ⟶ (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ^^ B,
        s ≫ expMap _ f = Cat.id _ := by
    exact ⟨directImageOmega f, directImageOmega_unit f hf⟩
  intro C m g hm hgm
  exact cover_of_section (expMap _ f) s hs m g hm hgm

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

    We state (a)↔(b)↔(c) and each implies local completeness; all proofs are Sorry
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
