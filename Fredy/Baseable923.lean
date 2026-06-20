/-
  Freyd & Scedrov, *Categories and Allegories* §1.923.

  CONDITIONAL theorem: in a category with terminal, binary products, pullbacks,
  equalizers, AND a power object `[C]` for EVERY object `C`, every object `B` is
  BASEABLE (i.e. the exponential `B^A` exists for every `A`).

  This is the "Kock" half of §1.921/§1.923: exponentiation follows from power
  objects.  The exponential `B^A` is constructed as the subobject of
  `[A × B] = powerObj (A × B)` cut out by the FUNCTIONAL relations — those
  `R ⊆ X × (A × B)` (equivalently `R ⊆ (A × X) → B`) that are graphs of maps
  `A → B`.

  STATUS.  This file keeps the HONEST §1.923 statement.  It builds the genuinely
  power-object-only infrastructure (the relation/classifier correspondence
  `Hom(X,[C]) ≅ BinRel(X,C)` as a bijection, packaged below) and reduces the main
  theorem to TWO precisely-typed sub-lemmas, both of which are real §1.912/§1.923
  content not yet available sorry-free in this repo:

    (D1) `power_object_gives_subobject_classifier` :
            from `[1] = powerObj one` build a `HasSubobjectClassifier 𝒞`.
         Signature (target):  `Nonempty (HasSubobjectClassifier 𝒞)`
         (Freyd §1.912.  The repo's `HasSubobjectClassifier` is only ever
          *assumed* via `[Topos 𝒞]`; deriving it from `HasPowerObject one`
          is unformalized.)

    (D2) `functional_subobject_is_exponential` :
            given a subobject classifier, cut out the functional relations of
            `[A × B]` (the §1.923 pullback `B^A → [A×B] ⇉ [A]`) and equip it with
            `ev` + curry + uniqueness, i.e. exactly `Baseable B` for that `A`.
         (The repo HAS this construction in `S1_92 :: expSubobj` /
          `graph_classifies`, but only relative to the sorry-contaminated `exp`
          instance `topos_has_exponentials`; redoing it on the power-object `E`
          with NO `exp` dependency is the remaining work.)

  (D1) is the NEXT DOMINO: it unlocks the existing §1.92 graph/classifier
  machinery (`graph_classifies`, `classRel_classify`, `monic_is_equalizer`) on
  *our* hypotheses, after which (D2) is the (S1_92-style) curry/eval bookkeeping.

  NO new axioms or hypotheses are introduced; the only gaps are the two sorries
  named above, each pinned to its exact signature.

  ⚠ SCOPE / RELATION TO THE KEYSTONE `S1_92 :: topos_has_exponentials`.
  This theorem is CONDITIONAL on `[∀ C, HasPowerObject C]`, which the repo's
  `Topos` class does NOT bundle (it provides only a subobject classifier
  `Ω = [1]`).  So even once (D1)+(D2) are closed, this does NOT directly discharge
  the keystone: that would additionally require building `∀ C, HasPowerObject C`
  FROM a bare subobject classifier — the converse of (D1) — which is the genuine
  open obstacle (constructing `[C] = Ω^C` from `Ω` alone is itself exponentiation,
  hence circular under the minimal `Topos` presentation).  This file is therefore
  scaffolding for the *power-object → exponential* direction (Kock's half) plus
  reusable, axiom-clean power-object correspondence lemmas; it is intentionally
  NOT imported by `S1_92`, so it adds no `sorryAx` to the main line.
-/

import Fredy.S1_91
import Fredy.S1_85

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

section Baseable923

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
variable [∀ C : 𝒞, HasPowerObject C] [HasEqualizers 𝒞]

/-! ## Power-object correspondence as a bijection (genuine, power-object-only)

  For any `Z, C`, the universality of `∈_C` (`HasPowerObject.is_universal`) makes
  `powerClassify : BinRel 𝒞 Z C → (Z ⟶ [C])` and `f ↦ relPullback f ∈_C` mutually
  inverse up to `RelHom`.  These lemmas are exactly what `(D2)` needs, proved here
  with NO dependence on `exp`/`Topos`. -/

/-- `powerClassify` classifies `R` up to relation iso.  Stated directly from the
    universality field `classify_exists` (NOT via the `[Topos 𝒞]`-contaminated
    `S1_91 :: powerClassify_spec`), so it depends only on power objects. -/
theorem powerClassify_pullback_iso {C Z : 𝒞} (R : BinRel 𝒞 Z C) :
    RelHom R (relPullback (powerClassify R) HasPowerObject.mem) ∧
    RelHom (relPullback (powerClassify R) HasPowerObject.mem) R :=
  (HasPowerObject.is_universal.classify_exists Z R).choose_spec

/-- **Uniqueness of the classifying map** (universality `classify_unique`). -/
theorem powerClassify_unique {C Z : 𝒞} (R : BinRel 𝒞 Z C)
    (f g : Z ⟶ HasPowerObject.powerObj (C := C))
    (hf : RelHom R (relPullback f HasPowerObject.mem) ∧ RelHom (relPullback f HasPowerObject.mem) R)
    (hg : RelHom R (relPullback g HasPowerObject.mem) ∧ RelHom (relPullback g HasPowerObject.mem) R) :
    f = g :=
  HasPowerObject.is_universal.classify_unique Z R f g hf hg

/-- **Maps into `[C]` are determined by their relation**: if `f g : Z ⟶ [C]` pull
    `∈_C` back to iso relations, they are equal. -/
theorem powerObj_hom_ext {C Z : 𝒞} (f g : Z ⟶ HasPowerObject.powerObj (C := C))
    (h : RelHom (relPullback f HasPowerObject.mem) (relPullback g HasPowerObject.mem) ∧
         RelHom (relPullback g HasPowerObject.mem) (relPullback f HasPowerObject.mem)) :
    f = g :=
  HasPowerObject.is_universal.classify_unique Z (relPullback f HasPowerObject.mem) f g
    ⟨⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩,
     ⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩⟩
    ⟨h.1, h.2⟩

/-! ## Relation reindexing `BinRel(A×X, B) ≅ BinRel(X, A×B)` (curry on relations)

  The exponential `B^A` from a power object rests on the "uncurry" bijection on
  RELATIONS: a relation `R ⊆ (A×X) × B` (= a possibly-partial multivalued map
  `A×X ⇀ B`) is the same data as a relation `R̂ ⊆ X × (A×B)` (the A-index folded
  into the target).  This is a pure product-rearrangement of the jointly-monic
  span and is `RelHom`-iso, axiom-clean.  It is the load-bearing isomorphism that
  feeds the power object `[A×B]`: `Hom(X,[A×B]) ≅ BinRel(X,A×B) ≅ BinRel(A×X,B)`. -/

/-- Fold the `A`-index of a relation `R ⊆ (A×X) × B` into its target:
    `R̂ ⊆ X × (A×B)`, with `colA := R.colA ≫ snd : src → X` and
    `colB := ⟨R.colA ≫ fst, R.colB⟩ : src → A×B`. -/
def relUncurry {A X B : 𝒞} (R : BinRel 𝒞 (prod A X) B) : BinRel 𝒞 X (prod A B) where
  src  := R.src
  colA := R.colA ≫ snd
  colB := pair (R.colA ≫ fst) R.colB
  isMonicPair := by
    intro W f g hX hAB
    -- agreement on X (hX) and on A×B (hAB) ⟹ agreement on the original (A×X, B) legs.
    apply R.isMonicPair f g
    · -- f ≫ R.colA = g ≫ R.colA : agree after fst (from hAB) and after snd (from hX).
      apply fst_snd_jointly_monic (f ≫ R.colA) (g ≫ R.colA)
      · have := congrArg (· ≫ fst) hAB
        simpa only [Cat.assoc, fst_pair] using this
      · rw [Cat.assoc, Cat.assoc]; exact hX
    · -- f ≫ R.colB = g ≫ R.colB : agree after snd of the A×B leg.
      have := congrArg (· ≫ snd) hAB
      simpa only [Cat.assoc, snd_pair] using this

/-- Inverse: unfold a relation `S ⊆ X × (A×B)` to `Š ⊆ (A×X) × B`, with
    `colA := ⟨S.colB ≫ fst, S.colA⟩ : src → A×X` and `colB := S.colB ≫ snd`. -/
def relCurry {A X B : 𝒞} (S : BinRel 𝒞 X (prod A B)) : BinRel 𝒞 (prod A X) B where
  src  := S.src
  colA := pair (S.colB ≫ fst) S.colA
  colB := S.colB ≫ snd
  isMonicPair := by
    intro W f g hAX hB
    apply S.isMonicPair f g
    · -- f ≫ S.colA = g ≫ S.colA : the X-coordinate of the A×X leg (snd).
      have := congrArg (· ≫ snd) hAX
      simpa only [Cat.assoc, snd_pair] using this
    · -- f ≫ S.colB = g ≫ S.colB : agree after fst (from hAX) and snd (from hB).
      apply fst_snd_jointly_monic (f ≫ S.colB) (g ≫ S.colB)
      · have := congrArg (· ≫ fst) hAX
        simpa only [Cat.assoc, fst_pair] using this
      · rw [Cat.assoc, Cat.assoc]; exact hB

/-- `relCurry` and `relUncurry` are mutually inverse on the nose (same `src`,
    legs equal by product-eta).  Stated as the two round-trip equalities of the
    *spans* (`colA`,`colB`), which is what the `RelHom` bijection needs. -/
theorem relCurry_uncurry {A X B : 𝒞} (R : BinRel 𝒞 (prod A X) B) :
    (relCurry (relUncurry R)).colA = R.colA ∧ (relCurry (relUncurry R)).colB = R.colB := by
  refine ⟨?_, ?_⟩
  · show pair ((pair (R.colA ≫ fst) R.colB) ≫ fst) (R.colA ≫ snd) = R.colA
    rw [fst_pair]; exact (pair_eta R.colA).symm
  · show (pair (R.colA ≫ fst) R.colB) ≫ snd = R.colB
    rw [snd_pair]

theorem relUncurry_curry {A X B : 𝒞} (S : BinRel 𝒞 X (prod A B)) :
    (relUncurry (relCurry S)).colA = S.colA ∧ (relUncurry (relCurry S)).colB = S.colB := by
  refine ⟨?_, ?_⟩
  · show (pair (S.colB ≫ fst) S.colA) ≫ snd = S.colA
    rw [snd_pair]
  · show pair ((pair (S.colB ≫ fst) S.colA) ≫ fst) (S.colB ≫ snd) = S.colB
    rw [fst_pair]; exact (pair_eta S.colB).symm

/-! ## Local `RelHom` plumbing (clean under bare power-object hypotheses)

  The S1_91 lemmas `relHom_trans`/`relHom_pullback`/`powerClassify_natural` live
  AFTER a file-level `variable [Topos 𝒞]`, so they silently require a full topos;
  under our bare `[∀ C, HasPowerObject C]` they are not applicable.  We re-bank the
  three we need here (the proofs use only products/pullbacks, no classifier). -/

/-- Transitivity of `RelHom` (local, classifier-free). -/
theorem relHom_trans923 {A C : 𝒞} {R S T : BinRel 𝒞 A C}
    (h₁ : RelHom R S) (h₂ : RelHom S T) : RelHom R T := by
  obtain ⟨h, hA, hB⟩ := h₁; obtain ⟨k, kA, kB⟩ := h₂
  exact ⟨h ≫ k, by rw [Cat.assoc, kA, hA], by rw [Cat.assoc, kB, hB]⟩

/-- `RelHom` is preserved by pulling back along a fixed `g` (local copy). -/
theorem relHom_pullback923 {A C X : 𝒞} (g : X ⟶ A) {R S : BinRel 𝒞 A C}
    (h : RelHom R S) : RelHom (relPullback g R) (relPullback g S) := by
  obtain ⟨w, hwA, hwB⟩ := h
  let P  := HasPullbacks.has g R.colA
  let P' := HasPullbacks.has g S.colA
  have hsq : P.cone.π₁ ≫ g = (P.cone.π₂ ≫ w) ≫ S.colA :=
    calc P.cone.π₁ ≫ g = P.cone.π₂ ≫ R.colA := P.cone.w
      _ = P.cone.π₂ ≫ (w ≫ S.colA) := congrArg (P.cone.π₂ ≫ ·) hwA.symm
      _ = (P.cone.π₂ ≫ w) ≫ S.colA := (Cat.assoc P.cone.π₂ w S.colA).symm
  let c : Cone g S.colA := ⟨P.cone.pt, P.cone.π₁, P.cone.π₂ ≫ w, hsq⟩
  refine ⟨P'.lift c, P'.lift_fst c, ?_⟩
  show P'.lift c ≫ (P'.cone.π₂ ≫ S.colB) = P.cone.π₂ ≫ R.colB
  calc P'.lift c ≫ (P'.cone.π₂ ≫ S.colB)
      = (P'.lift c ≫ P'.cone.π₂) ≫ S.colB := (Cat.assoc _ _ _).symm
    _ = (P.cone.π₂ ≫ w) ≫ S.colB := congrArg (· ≫ S.colB) (P'.lift_snd c)
    _ = P.cone.π₂ ≫ (w ≫ S.colB) := Cat.assoc _ _ _
    _ = P.cone.π₂ ≫ R.colB := congrArg (P.cone.π₂ ≫ ·) hwB

/-- **Naturality of `Λ`** (local, classifier-free): `Λ(relPullback g R) = g ≫ Λ(R)`. -/
theorem powerClassify_natural923 {C A X : 𝒞} (R : BinRel 𝒞 A C) (g : X ⟶ A) :
    powerClassify (relPullback g R) = g ≫ powerClassify R := by
  have hR := powerClassify_pullback_iso R
  obtain ⟨hc1, hc2⟩ := relPullback_comp g (powerClassify R) HasPowerObject.mem
  have hf : RelHom (relPullback g R)
              (relPullback (g ≫ powerClassify R) HasPowerObject.mem) ∧
            RelHom (relPullback (g ≫ powerClassify R) HasPowerObject.mem)
              (relPullback g R) :=
    ⟨relHom_trans923 (relHom_pullback923 g hR.1) hc1,
     relHom_trans923 hc2 (relHom_pullback923 g hR.2)⟩
  exact HasPowerObject.is_universal.classify_unique X (relPullback g R) _ _
    (powerClassify_pullback_iso (relPullback g R)) hf

/-! ## Step A — image-free "functional-total relation is a graph"

  A relation `R ⊆ Y × B` whose left leg `R.colA : R.src → Y` is BOTH monic and a
  cover is (single-valued + total =) a MAP, hence the graph of a unique morphism
  `m := R.colA⁻¹ ≫ R.colB`.  This is `tabulated_left_iso_eq_graph` (S1_56:647),
  but reproved INLINE here so as to avoid that lemma's enclosing `[HasImages 𝒞]`
  section.  No images are used: just `monic_cover_iso` (S1_51:70) to split the leg
  and product/graph rewrites. -/

/-- **Step A**: a functional-total relation `R` (left leg monic + cover) is the
    graph of a unique morphism `m : Y ⟶ B`, with mutual `RelHom`s `R ↔ graph m`. -/
theorem functional_total_relation_is_graph {Y B : 𝒞} (R : BinRel 𝒞 Y B)
    (hmono : Mono R.colA) (hcover : Cover R.colA) :
    ∃ m : Y ⟶ B, (RelHom R (graph m) ∧ RelHom (graph m) R) ∧
      ∀ m' : Y ⟶ B, (RelHom R (graph m') ∧ RelHom (graph m') R) → m' = m := by
  -- The left leg is iso since it is a monic cover.
  obtain ⟨ainv, ha_ainv, hainv_a⟩ := monic_cover_iso R.colA hcover hmono
  refine ⟨ainv ≫ R.colB, ⟨?_, ?_⟩, ?_⟩
  · -- RelHom R (graph (ainv ≫ R.colB)): witness R.colA.
    refine ⟨R.colA, ?_, ?_⟩
    · dsimp [graph]; rw [Cat.comp_id]
    · dsimp [graph]
      calc R.colA ≫ (ainv ≫ R.colB) = (R.colA ≫ ainv) ≫ R.colB := (Cat.assoc _ _ _).symm
        _ = Cat.id _ ≫ R.colB := by rw [ha_ainv]
        _ = R.colB := Cat.id_comp _
  · -- RelHom (graph (ainv ≫ R.colB)) R: witness ainv.
    refine ⟨ainv, ?_, ?_⟩
    · dsimp [graph]; rw [hainv_a]
    · rfl
  · -- Uniqueness: any m' with RelHom (graph m') R gives a section of R.colA = ainv.
    rintro m' ⟨_, ⟨w, hwA, hwB⟩⟩
    -- hwA : w ≫ R.colA = (graph m').colA = id Y ; hwB : w ≫ R.colB = m'
    dsimp [graph] at hwA hwB
    -- w is a section of R.colA, which is iso, so w = ainv.
    have hw_eq : w = ainv := by
      calc w = w ≫ Cat.id _ := (Cat.comp_id _).symm
        _ = w ≫ (R.colA ≫ ainv) := by rw [ha_ainv]
        _ = (w ≫ R.colA) ≫ ainv := (Cat.assoc _ _ _).symm
        _ = Cat.id _ ≫ ainv := by rw [hwA]
        _ = ainv := Cat.id_comp _
    rw [← hwB, hw_eq]

/-! ## Step B — the singleton map `{·} : B ↣ [B]` (classifier-free)

  `singletonMap B := Λ(graph (id B)) : B ⟶ [B]` names the diagonal relation
  `Δ_B = graph(id B) ⊆ B × B`.  Built purely from power objects (no classifier,
  no `exp`/`curry`), it is the power-object analogue of `singletonMapCat`
  (S1_92), and is MONIC: precomposing it with `h, k : X ⟶ B` names the graphs of
  `h, k` (via `powerClassify_natural` + `relPullback h (graph id) ≅ graph h`), so
  equal names force `h = k`. -/

/-- The singleton (description) map `{·} : B ⟶ [B]`, naming the diagonal. -/
noncomputable def singletonMap (B : 𝒞) : B ⟶ HasPowerObject.powerObj (C := B) :=
  powerClassify (graph (Cat.id B))

/-- Pulling the diagonal `graph (id B)` back along `h : X ⟶ B` gives `graph h`
    (up to relation iso, both directions).  The pullback of `Δ_B` along `h` is
    `{(x) | (h x, x)} = graph h`; concretely the pullback span has a section. -/
theorem relPullback_graph_id {X B : 𝒞} (h : X ⟶ B) :
    RelHom (graph h) (relPullback h (graph (Cat.id B))) ∧
    RelHom (relPullback h (graph (Cat.id B))) (graph h) := by
  -- graph h : src=X, colA=id X, colB=h.  relPullback h (graph id): pullback of
  -- (h : X→B) and (graph id).colA = id B; its apex ≅ X with π₁ a section.
  have hsq : (Cat.id X) ≫ h = h ≫ (graph (Cat.id B)).colA := by
    dsimp [graph]; rw [Cat.id_comp, Cat.comp_id]
  constructor
  · -- graph h ⊂ relPullback: witness `s := lift ⟨X, id X, h, hsq⟩ : X → pb.pt`.
    refine ⟨(HasPullbacks.has h (graph (Cat.id B)).colA).lift ⟨X, Cat.id X, h, hsq⟩, ?_, ?_⟩
    · -- s ≫ colA = s ≫ π₁ = id X = (graph h).colA
      dsimp [relPullback, graph]
      exact (HasPullbacks.has h (Cat.id B)).lift_fst _
    · -- s ≫ colB = s ≫ (π₂ ≫ id) = (s ≫ π₂) = h = (graph h).colB
      dsimp [relPullback, graph]
      rw [Cat.comp_id]
      exact (HasPullbacks.has h (Cat.id B)).lift_snd ⟨X, Cat.id X, h, hsq⟩
  · -- relPullback ⊂ graph h: witness π₁ : pb.pt → X.
    refine ⟨(HasPullbacks.has h (graph (Cat.id B)).colA).cone.π₁, ?_, ?_⟩
    · -- π₁ ≫ (graph h).colA = π₁ ≫ id X = π₁ = colA
      dsimp [relPullback, graph]; rw [Cat.comp_id]
    · -- π₁ ≫ (graph h).colB = π₁ ≫ h = π₂ ≫ id = colB
      have hw := (HasPullbacks.has h (graph (Cat.id B)).colA).cone.w
      dsimp [relPullback, graph] at hw ⊢
      rw [Cat.comp_id, hw, Cat.comp_id]

/-- Naming a graph: `h ≫ singletonMap B = Λ(graph h)`. -/
theorem singletonMap_naming {X B : 𝒞} (h : X ⟶ B) :
    h ≫ singletonMap B = powerClassify (graph h) := by
  rw [singletonMap, ← powerClassify_natural923 (graph (Cat.id B)) h]
  -- Goal: Λ(relPullback h (graph id)) = Λ(graph h).  Both classify the relation
  -- `relPullback h (graph id)` (the RHS via the iso to `graph h`); classify_unique.
  obtain ⟨hf, hg⟩ := relPullback_graph_id h  -- graph h ↔ relPullback h (graph id)
  apply HasPowerObject.is_universal.classify_unique X (relPullback h (graph (Cat.id B)))
  · exact powerClassify_pullback_iso _
  · -- relPullback h (graph id) ↔ relPullback (Λ(graph h)) ∈, via graph h.
    exact ⟨relHom_trans923 hg (powerClassify_pullback_iso (graph h)).1,
           relHom_trans923 (powerClassify_pullback_iso (graph h)).2 hf⟩

/-- **Step B**: the singleton map `{·} : B ↣ [B]` is MONIC.  If `h, k : X ⟶ B`
    have `h ≫ {·} = k ≫ {·}`, both name `graph h` resp. `graph k`; the names being
    equal makes `graph h ≅ graph k`, whose right legs are `h, k`, forcing `h = k`. -/
theorem singletonMap_monic (B : 𝒞) : Mono (singletonMap (𝒞 := 𝒞) B) := by
  intro X h k hΔ
  -- Λ(graph h) = Λ(graph k).
  have hΛ : powerClassify (graph h) = powerClassify (graph k) := by
    rw [← singletonMap_naming, ← singletonMap_naming]; exact hΔ
  -- Hence graph h ≅ graph k (both classify the same name).
  have hiso : RelHom (graph h) (graph k) := by
    have h1 := (powerClassify_pullback_iso (graph h)).1   -- graph h ⊂ relPullback Λ(graph h) mem
    have h2 := (powerClassify_pullback_iso (graph k)).2   -- relPullback Λ(graph k) mem ⊂ graph k
    rw [hΛ] at h1
    exact relHom_trans923 h1 h2
  -- A RelHom graph h → graph k gives a witness w with w ≫ id = id (so w = id) and w ≫ k = h.
  obtain ⟨w, hwA, hwB⟩ := hiso
  dsimp [graph] at hwA hwB
  -- hwA : w ≫ id X = id X  ⟹ w = id X ; hwB : w ≫ k = h.
  have hw : w = Cat.id X := by rw [← Cat.comp_id w]; exact hwA
  rw [← hwB, hw, Cat.id_comp]

/-! ## §1.923 missing dominoes (honest sorries, pinned signatures) -/

/-- **(D1)** §1.912: a power object for the terminal object is a subobject
    classifier.  `Ω := powerObj one`, `true := Λ(graph (term 1))`, and
    `classify m := Λ` of the relation `m : A' ↣ A → 1`.  Freyd §1.912; not yet
    formalized (the repo only *assumes* `HasSubobjectClassifier` via `[Topos 𝒞]`).

    NEXT DOMINO: closing this unlocks the existing `S1_92` graph/classifier
    machinery on the present hypotheses. -/
theorem power_object_gives_subobject_classifier :
    Nonempty (HasSubobjectClassifier 𝒞) :=
  sorry

/-- **(D2)** §1.923: given a subobject classifier, the FUNCTIONAL-relation
    subobject of `[A × B]` is the exponential `B^A`, yielding for each `A` the
    object `E`, evaluation `ev : A × E → B`, and the curry/eval bijection that is
    exactly `Baseable B` at `A`.

    BANKED INFRASTRUCTURE (this file, axiom-clean):
    *  `relUncurry`/`relCurry` + `relCurry_uncurry`/`relUncurry_curry` — the
       relation transpose `BinRel(A×X, B) ≅ BinRel(X, A×B)`.
    *  `powerClassify` / `powerObj_hom_ext` / `powerClassify_pullback_iso` — the
       power-object bijection `Hom(X,[A×B]) ≅ BinRel(X, A×B)`.
    Chaining these gives, for free, the half-bijection
       `Hom(X, [A×B]) ≅ BinRel(A×X, B)`  ( ≅ "multivalued partial maps A×X ⇀ B" ).

    REMAINING RESIDUAL (the genuine §1.923 content still missing from the repo).
    The carrier is `E := the subobject of [A×B]` of those relations that are
    `relUncurry`-images of GRAPHS of maps `A×X → B` — i.e. FUNCTIONAL (single
    valued) and TOTAL in the `A×X` direction.  `ev : A×E → B` is then the unique
    map whose graph is `relUncurry⁻¹ (relPullback ι mem)` (ι : E ↣ [A×B]).
    Extracting that `ev`, and proving the β/η bijection, factors through ONE sharp
    topos lemma absent from this repo:

      `functional_total_relation_is_graph` :
        ∀ {Y B} (R : BinRel 𝒞 Y B),
          (single-valued R) → (total R) → ∃! m : Y ⟶ B, RelHom R (graph m) ∧ RelHom (graph m) R

    (Freyd §1.912/§1.252: a relation is a map iff it is everywhere-defined and
    single-valued.)  Proving it needs the classifier-only DESCRIPTION operator
    (the singleton map `{·} : B ↣ [B]` and "a total single-valued relation factors
    through `{·}`"), which the repo currently builds only via the `exp`-dependent
    `singletonMapCat` (S1_92).  A classifier-only `singletonMap` + its equalizer
    presentation of `B` is the NEXT DOMINO; with it, D2 (and the keystone) close.

    The repo realizes the eval/curry bookkeeping in `S1_92 :: expSubobj` /
    `graph_classifies`, but only over the sorry-contaminated `exp` instance;
    reproving on the power object `E` is blocked solely on the lemma above. -/
theorem functional_subobject_is_exponential
    (_hΩ : HasSubobjectClassifier 𝒞) (B A : 𝒞) :
    ∃ (E : 𝒞) (ev : prod A E ⟶ B),
      ∀ (X : 𝒞) (f : prod A X ⟶ B),
        ∃ (g : X ⟶ E), prodMap A X E g ≫ ev = f ∧
          ∀ (g' : X ⟶ E), prodMap A X E g' ≫ ev = f → g' = g :=
  sorry

/-- **§1.923**: GIVEN a power object for every object, every object is baseable.
    Reduces to `(D1)` (power object of `1` is a subobject classifier) and `(D2)`
    (functional-relation subobject of `[A×B]` is the exponential). -/
theorem power_objects_imply_all_baseable :
    ∀ B : 𝒞, Baseable B := by
  intro B A
  obtain ⟨hΩ⟩ := power_object_gives_subobject_classifier (𝒞 := 𝒞)
  exact functional_subobject_is_exponential hΩ B A

end Baseable923

end Freyd
