/-
  Freyd & Scedrov, *Categories and Allegories* §1.63–§1.66
  Slice pre-logos, Boolean pre-logoi, Pre-topoi, Amalgamation.

  §1.63  If A is a (positive) pre-logos, so is A/B (§1.63).
  §1.631 Complemented subobject: A₁∩A₂=0, A₁∪A₂=A.
  §1.64  Boolean pre-logos: subobject lattices are Boolean algebras.
  §1.644 Ultra-product / ultra-power functors (§1.644).
  §1.645 𝒦𝓮𝓇(T) = values killed by representation T.
  §1.65  Pre-topos = effective positive pre-logos.
  §1.651 Amalgamation Lemma: pushout of two monics exists.
  §1.652 In a pre-topos: covers = epics, monics = cocovers.
  §1.66  (if applicable)
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58
import Fredy.S1_59
import Fredy.S1_60
import Fredy.S1_57
import Fredy.S1_62
import Fredy.S1_77


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.631 Complemented subobject

  A₁ ⊆ A is COMPLEMENTED if ∃ A₂ ⊆ A with A₁∩A₂=0, A₁∪A₂=A. -/

-- NOTE: `[PreLogos 𝒞]` is attached locally to each declaration that needs it rather
-- than as a module-level `variable`.  A module-level `[PreLogos 𝒞]` would form a
-- diamond with `DisjointBinaryCoproduct.toPreLogos` (§1.621 block below), since that
-- class also supplies a `PreLogos` instance for the same `𝒞`.

/-- A₁ is COMPLEMENTED (§1.631): ∃ A₂ with A₁∩A₂ = 0 and A₁∪A₂ = A.
    The disjointness "A₁∩A₂ = 0" is phrased as the *meet-is-bottom* universal property
    `∀ S, S≤A₁ → S≤A₂ → S≤⊥` — equivalent to `inter A₁ A₂ ≤ bottom` (`IsComplementedSub`,
    §1.62; bridge lemma `isComplemented_iff_sub` below), but mentioning NO `HasPullbacks`
    instance, so it avoids the `PreLogos`/`PreTopos` diamond.
    NB: the earlier form wrote `→ False` instead of `→ S≤⊥`; that is UNSATISFIABLE (take
    `S := bottom`, which is `≤` everything), so it held for no subobject and made
    `BooleanPreLogos` uninhabitable — a stale placeholder, now corrected. -/
def IsComplemented [PreLogos 𝒞] {A : 𝒞} (A₁ : Subobject 𝒞 A) : Prop :=
  ∃ (A₂ : Subobject 𝒞 A),
    (∀ (S : Subobject 𝒞 A), Subobject.le S A₁ → Subobject.le S A₂ → Subobject.le S (PreLogos.bottom A))
    -- A₁∩A₂ ≤ 0 (meet is bottom — instance-free phrasing of `inter A₁ A₂ ≤ bottom`)
    ∧ Subobject.le (Subobject.entire A) (HasSubobjectUnions.union A₁ A₂)
    -- A₁∪A₂ = A (entire)

/-! ## §1.64 Boolean pre-logos

  A BOOLEAN PRE-LOGOS is a pre-logos where every subobject lattice
  is Boolean (every subobject has a complement). -/

class BooleanPreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends PreLogos 𝒞 where
  hasComplement : ∀ {A : 𝒞} (S : Subobject 𝒞 A), IsComplemented S

/-! ## §1.645 𝒦𝓮𝓇(T) — values killed by a representation

  For T: A → B a representation of boolean pre-logoi, Kℯℛ(T) is
  the set of subterminators U ⊆ 1 such that T(U) = 0. -/

/-- **§1.645** `Kℯℛ(T) = { U ⊆ 1 | T(U) = 0 }` — the set of subterminators whose
    value under the representation `T` is the NULL (zero) object.

    Book text (§1.645): "we define `𝒦ℯℛ(T)` as the set of values killed by `T`:
    `𝒦ℯℛ(T) = { U ⊆ 1 | T(U) = 0 }`".  Here `0` is the bottom of the target's
    subobject lattice (`PreLogos.bottom`, the empty join / null object) — the
    OPPOSITE extreme from the terminator `1`.

    INTEGRITY FIX: the previous definition tested `Isomorphic (T U.dom) one`
    (the terminator, i.e. `T(U) = 1`), which is exactly backwards — it would make
    `Kℯℛ(T)` the values sent to the TOP rather than killed.  Corrected to test
    against the zero object `(PreLogos.bottom _).dom`. -/
def killedValues {𝒟 : Type u} [Cat.{v} 𝒟] [PreLogos 𝒞] [PreLogos 𝒟]
    (T : 𝒞 → 𝒟) [Functor T] : (Subobject 𝒞 one) → Prop :=
  λ U => @Isomorphic 𝒟 _ (T U.dom) (PreLogos.bottom (T U.dom)).dom

/-! ## §1.646 Faithful representability of small special categories

  Every small special Cartesian category is faithfully representable in Set.
  Every small special positive pre-logos is faithfully representable in Set.
  PROOF (§1.646): Combine §1.472/§1.637 (finite separation) with a diagonal
  ultra-filter argument: I = finite sets of proper subobjects, choose T_S for
  each S, form T : A → Set^I, extend to an ultra-filter F ⊇ principal coideals.
  T^F is faithful.  (Requires ultra-filter machinery; sorry.) -/

-- §1.646 (note): Every small special Cartesian category embeds faithfully in Set.
-- Proof combines §1.472/§1.637 with an ultra-filter diagonal argument.
-- Requires ultra-filter infrastructure outside this repo's scope.

-- §1.647 (note): A boolean pre-logos is special iff two-valued.
-- Proof: complement of (A₁×B₂)∪(B₁×A₂) in B₁×B₂ is A₁°×A₂°.
-- Requires complement intersection/union infrastructure not yet formalized.

-- §1.648 (note): Ultra-power T = Set^I → Set^I/F is bicartesian iff F is
-- a complete measure (meets every countable partition of I).
-- Requires ultra-filter/ultra-product infrastructure outside this repo.

/-! ## §1.65 Pre-topos

  A PRE-TOPOS is an effective positive pre-logos:
  effective regular + positive pre-logos. -/

class PreTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    EffectiveRegular 𝒞, PositivePreLogos 𝒞

/-! ## §1.621/§1.623 Disjointness of positive coproducts — RELOCATED to S1_62

  `inlSub`, `inrSub`, `DisjointBinaryCoproduct`, and the disjointness lemmas
  (`inl_mono`, `inr_mono`, `inl_inter_inr_le_bottom`, `inl_union_inr_entire`,
  `coprod_inl_inr_disjoint_elt`) now live in `Fredy.S1_62`, next to their natural
  home `PositivePreLogos` (§1.623), so the §1.624/§1.631 corollaries there can
  consume them without a cyclic import back into this file.  They remain in scope
  here via `import Fredy.S1_62`.  Only `PreToposDisjoint` stays below, because it
  extends `PreTopos` (§1.65), which is defined in this file. -/

variable (𝒞)

/-- A pre-topos has disjoint coproducts (§1.621): every pre-topos is positive, and
    positivity *means* the coproduct is the disjoint complemented union §1.623, so the
    §1.621 disjointness conditions hold.  Recorded as the class field bundle that
    downstream pre-topos proofs consume; concrete `PreTopos` instances must supply it
    exactly as Freyd builds it. -/
class PreToposDisjoint (𝒞 : Type u) [Cat.{v} 𝒞] extends
    PreTopos 𝒞, DisjointBinaryCoproduct 𝒞

variable {𝒞}

/-! ## §1.654/§1.657 Pre-topos is cocartesian iff minimal equivalence relations exist

  A pre-topos is COCARTESIAN (its opposite is regular) if and only if
  for every endo-relation R on an object A there exists a minimal
  equivalence relation Ê ⊇ R on A.
  (§1.657: effectiveness means Ê is the level of some coequalizer A → B.)

  Proof sketch (§1.657):
  · (⇒) If A has coequalizers, given f: A→B with level E ⊇ R, then E is
    the minimal equivalence relation containing R (effectiveness).
  · (⇐) Conversely, given R = x°y (level of x,y : C⇒A), form the
    minimal equivalence Ê containing x°y; by effectiveness, Ê = level of
    some cover z: A→B; then z is a coequalizer of x and y. -/

/-- Every endo-relation on every object has a minimal equivalence relation containing it. -/
def HasMinEquivContaining (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] [HasImages 𝒞] : Prop :=
  ∀ (A : 𝒞) (R : BinRel 𝒞 A A),
    ∃ (E : BinRel 𝒞 A A), EquivalenceRelation E
      ∧ RelLe R E
      ∧ ∀ (F : BinRel 𝒞 A A), EquivalenceRelation F → RelLe R F → RelLe E F

/-- The reciprocal-composition relation `(graph g) ⊚ (graph g)°` is contained in the
    level (kernel pair) of `g`: a composed point `(a, c)` satisfies `a ≫ g = c ≫ g`
    (the pullback square forces it), so its span lifts into `kernelPair g`, and
    image-minimality (`image_min`) turns that into the required `RelHom`. -/
private theorem graphComp_le_kernelPairRel [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] [HasImages 𝒞] {A Q : 𝒞} (g : A ⟶ Q) :
    RelLe ((graph g) ⊚ (graph g)°) (kernelPairRel g) := by
  let pb := HasPullbacks.has (graph g).colB ((graph g)°).colA
  let a' := pb.cone.π₁ ≫ (graph g).colA
  let c' := pb.cone.π₂ ≫ ((graph g)°).colB
  let sp : pb.cone.pt ⟶ prod A A := pair a' c'
  have hw : a' ≫ g = c' ≫ g := by
    have := pb.cone.w
    simp only [graph, reciprocal] at this ⊢
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

/-- The level (kernel pair) of `g` is contained in `(graph g) ⊚ (graph g)°`: the
    kernel-pair legs `(kp₁, kp₂)` form a cone over `g, g`, hence lift into the
    composition's pullback, then through `image.lift`. -/
private theorem kernelPairRel_le_graphComp [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] [HasImages 𝒞] {A Q : 𝒞} (g : A ⟶ Q) :
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

/-- **§1.657**: A pre-topos with coequalizers satisfies HasMinEquivContaining.
    Given `R` on `A`, take the coequalizer `q : A → Q` of `R.colA, R.colB`; its
    level `Ê := kernelPairRel q` is an equivalence relation (§1.567) containing `R`
    (lift via `q`'s coequalizing equation).  Minimality: any equivalence `F ⊇ R` is,
    by effectiveness, the level of a cover `g`; from `R ⊂ F ⊂ level g` we get
    `R.colA ≫ g = R.colB ≫ g`, the coequalizer UMP factors `g = q ≫ d`, hence
    `level q ⊂ level g ⊂ F`. -/
theorem preTopos_cocartesian_to_minEquiv {𝒞 : Type u} [Cat.{v} 𝒞] [PreTopos 𝒞]
    [HasCoequalizers 𝒞] : HasMinEquivContaining 𝒞 := by
  intro A R
  let hcoeq := HasCoequalizers.coeq R.colA R.colB
  refine ⟨kernelPairRel hcoeq.map, level_is_equivalence_relation hcoeq.map, ?_, ?_⟩
  · -- R ⊂ kernelPairRel hcoeq.map : lift R into the kernel pair via hcoeq.eq.
    let l := (HasPullbacks.has hcoeq.map hcoeq.map).lift ⟨_, R.colA, R.colB, hcoeq.eq⟩
    refine ⟨⟨l, ?_, ?_⟩⟩
    · exact kp_lift_p₁ R.colA R.colB hcoeq.eq
    · exact kp_lift_p₂ R.colA R.colB hcoeq.eq
  · -- Minimality.
    intro F hF hRF
    obtain ⟨_, Q, g, _hgcov, hFle, hleF⟩ := EffectiveRegular.effective F hF
    -- R ⊂ F ⊂ (graph g ⊚ graph g°) ⊂ kernelPairRel g.
    have hRkp : RelLe R (kernelPairRel g) :=
      rel_le_trans (rel_le_trans hRF hFle) (graphComp_le_kernelPairRel g)
    obtain ⟨⟨w, hwA, hwB⟩⟩ := hRkp
    -- The coequalized pair becomes equal after g.
    have hRg : R.colA ≫ g = R.colB ≫ g := by
      have e1 : w ≫ kp₁ (f := g) = R.colA := hwA
      have e2 : w ≫ kp₂ (f := g) = R.colB := hwB
      rw [← e1, ← e2, Cat.assoc, Cat.assoc, kp_sq]
    -- Coequalizer UMP: g factors as hcoeq.map ≫ d.
    have hd : hcoeq.map ≫ hcoeq.desc g hRg = g := hcoeq.fac g hRg
    -- kernelPairRel hcoeq.map ⊂ kernelPairRel g (legs of one kernel pair land in the other).
    have hkpkp : RelLe (kernelPairRel hcoeq.map) (kernelPairRel g) := by
      have hsq : kp₁ (f := hcoeq.map) ≫ g = kp₂ (f := hcoeq.map) ≫ g := by
        rw [← hd, ← Cat.assoc, ← Cat.assoc, kp_sq]
      let l := (HasPullbacks.has g g).lift ⟨_, kp₁ (f := hcoeq.map), kp₂ (f := hcoeq.map), hsq⟩
      exact ⟨⟨l, kp_lift_p₁ _ _ hsq, kp_lift_p₂ _ _ hsq⟩⟩
    -- kernelPairRel g ⊂ (graph g ⊚ graph g°) ⊂ F.
    have hkpF : RelLe (kernelPairRel g) F :=
      rel_le_trans (kernelPairRel_le_graphComp g) hleF
    exact rel_le_trans hkpkp hkpF

/-! ### Bridge: §1.775 `IsEquivRel` (RelLe-form) ↔ §1.567 `EquivalenceRelation` (RelHom-form).

  `HasMinEquivContaining` is phrased with the §1.567 `EquivalenceRelation` (a *section*
  `h≫colA = h≫colB = id` for reflexivity, `Nonempty (RelHom E E°)` for symmetry, `Nonempty
  (RelHom (E⊚E) E)` for transitivity).  The §1.775 equivalence closure produces the `IsEquivRel`
  form (`graph(id) ⊑ E`, `E° ⊑ E`, `E⊚E ⊑ E`).  The two are interderivable. -/
theorem equivalenceRelation_of_isEquivRel {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} {E : BinRel 𝒞 A A} (h : IsEquivRel E) : EquivalenceRelation E := by
  obtain ⟨hRefl, hSym, hTrans⟩ := h
  refine ⟨?_, ?_, hTrans⟩
  · -- reflexivity: graph(id) ⊑ E (RelHom witness w with w≫colA = w≫colB = id) is the section.
    obtain ⟨⟨w, hwA, hwB⟩⟩ := hRefl
    exact ⟨w, by simpa [graph] using hwA, by simpa [graph] using hwB⟩
  · -- symmetry: E° ⊑ E  ⟹  E ⊑ E°  (reciprocate, use involution).
    have h2 : RelLe (E°°) (E°) := reciprocal_monotone hSym
    rwa [reciprocal_invol] at h2

/-- Reverse bridge: §1.567 `EquivalenceRelation` ⟹ §1.775 `IsEquivRel`. -/
theorem isEquivRel_of_equivalenceRelation {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} {E : BinRel 𝒞 A A} (h : EquivalenceRelation E) : IsEquivRel E := by
  obtain ⟨⟨hsec, hsA, hsB⟩, ⟨hsym⟩, htrans⟩ := h
  refine ⟨?_, ?_, htrans⟩
  · exact ⟨⟨hsec, by simpa [graph] using hsA, by simpa [graph] using hsB⟩⟩
  · -- field gives E ⊑ E°; reciprocate to E° ⊑ E.
    have h2 : RelLe (E°) (E°°) := reciprocal_monotone ⟨hsym⟩
    rwa [reciprocal_invol] at h2

/-- **§1.775/§1.657 (the `HasReflTransClosure` payoff)**: a category with all reflexive-transitive
    closures has all minimal equivalence relations.

    Given `R` on `A`, form the symmetrisation `Rsym := (R ∪ᵣ R°) ∪ᵣ graph(id A)` (the join of `R`,
    its reciprocal, and the diagonal), then take `E := rtc Rsym`.  By §1.775
    (`equivClos_from_symm_transRefClos`), `E` is the *equivalence closure* of `R`: the minimum
    equivalence relation containing `R`.  Converting the §1.775 `IsEquivRel` form to the §1.567
    `EquivalenceRelation` form yields exactly `HasMinEquivContaining`.

    This is the constructive replacement for `preTopos_cocartesian_to_minEquiv` (which built the
    minimal equivalence from coequalizers + effectiveness): here it is built from R* directly. -/
theorem minEquiv_of_rtc {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [HasBinaryCoproducts 𝒞] [HasReflTransClosure 𝒞] :
    HasMinEquivContaining 𝒞 := by
  intro A R
  let Rsym : BinRel 𝒞 A A := (R ∪ᵣ R°) ∪ᵣ graph (Cat.id A)
  have hR_le_Rsym   : RelLe R Rsym :=
    rel_le_trans (relUnion_le_left R (R°)) (relUnion_le_left (R ∪ᵣ R°) (graph (Cat.id A)))
  have hRop_le_Rsym : RelLe (R°) Rsym :=
    rel_le_trans (relUnion_le_right R (R°)) (relUnion_le_left (R ∪ᵣ R°) (graph (Cat.id A)))
  have hId_le_Rsym  : RelLe (graph (Cat.id A)) Rsym :=
    relUnion_le_right (R ∪ᵣ R°) (graph (Cat.id A))
  have hR_op : RelLe ((R°)°) Rsym := by rwa [reciprocal_invol]
  -- (graph id)° ⊑ Rsym:  (graph id)° ⊑ graph id ⊑ Rsym.
  have hIdop_le_Rsym : RelLe ((graph (Cat.id A))°) Rsym := by
    have h0 : RelLe ((graph (Cat.id A))°) ((graph (Cat.id A))°°) :=
      reciprocal_monotone graph_id_le_reciprocal
    rw [reciprocal_invol] at h0
    exact rel_le_trans h0 hId_le_Rsym
  -- Rsym is symmetric: Rsym° ⊑ Rsym (distribute ° over ∪ᵣ, each piece lands in Rsym).
  have hSym : IsSymmetric Rsym := by
    refine rel_le_trans (relUnion_le_reciprocal (R ∪ᵣ R°) (graph (Cat.id A))) ?_
    apply le_relUnion
    · exact hIdop_le_Rsym
    · refine rel_le_trans (relUnion_le_reciprocal R (R°)) ?_
      exact le_relUnion hR_op hRop_le_Rsym
  -- Rsym is the join of R, R°, 1.
  have hJoin : ∀ (U : BinRel 𝒞 A A),
      RelLe R U → RelLe (R°) U → RelLe (graph (Cat.id A)) U → RelLe Rsym U := by
    intro U hRU hRopU hIdU; exact le_relUnion (le_relUnion hRU hRopU) hIdU
  -- E := rtc Rsym, packaged as the §1.775 equivalence closure of R.
  let ec := equivClos_from_symm_transRefClos R Rsym hR_le_Rsym hSym hJoin
              (HasReflTransClosure.transRefClos Rsym)
  refine ⟨ec.clos, equivalenceRelation_of_isEquivRel ec.isEquiv, ec.le, ?_⟩
  intro F hF hRF
  exact ec.minimal F hRF (isEquivRel_of_equivalenceRelation hF)


/-! ### Relation-algebra infrastructure for amalgamation leg-monicity (§1.651)

  The leg-monicity `Mono (inl ≫ q)` reduces to a relation containment
  `graph inl ⊚ E ⊚ (graph inl)° ⊂ 1_B`.  Distributing `E ⊂ F = 1 ∪ R₀ ∪ R₀°`
  (minimality of `E`), the cross terms `R₀, R₀°` vanish because `R₀` only relates
  `inl(B)` to `inr(C)`: composing them against `graph inl` hits the disjoint
  intersection `inl ∩ inr = 0` (§1.62 positivity), so the composite relation's
  tabulation sits below the bottom subobject — hence below *every* relation, in
  particular the diagonal.  The diagonal term `graph inl ⊚ 1 ⊚ (graph inl)° =
  graph inl ⊚ (graph inl)°` is `⊂ 1_B` since `inl` is monic. -/

/-- `f : A → B` is monic if its level (kernel pair) lies inside the diagonal. -/
private theorem mono_of_kernelPairRel_le_diag [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (h : RelLe (kernelPairRel f) (graph (Cat.id A))) : Mono f := by
  intro W u v huv
  have hw1 : ((HasPullbacks.has f f).lift ⟨W, u, v, huv⟩) ≫ kp₁ (f := f) = u :=
    kp_lift_p₁ u v huv
  have hw2 : ((HasPullbacks.has f f).lift ⟨W, u, v, huv⟩) ≫ kp₂ (f := f) = v :=
    kp_lift_p₂ u v huv
  obtain ⟨⟨z, hzA, hzB⟩⟩ := h
  have hcol : kp₁ (f := f) = kp₂ (f := f) := by
    have ha : z ≫ Cat.id A = (kernelPairRel f).colA := hzA
    have hb : z ≫ Cat.id A = (kernelPairRel f).colB := hzB
    show (kernelPairRel f).colA = (kernelPairRel f).colB; rw [← ha, ← hb]
  calc u = _ ≫ kp₁ (f := f) := hw1.symm
    _ = _ ≫ kp₂ (f := f) := by rw [hcol]
    _ = v := hw2

/-- A relation whose tabulation `pair colA colB` factors through the bottom subobject of
    `A×B` is contained in EVERY relation `A → B` (bottom is the minimal subobject). -/
private theorem relLe_of_relSub_le_bottom [PreLogos 𝒞] [HasBinaryCoproducts 𝒞]
    {X Y : 𝒞} {R U : BinRel 𝒞 X Y}
    (h : (relSub R).le (PreLogos.bottom (prod X Y))) : RelLe R U :=
  relLe_of_subLe (subLe_trans h (PreLogos.bottom_min (relSub U)))

/-- Left distributivity of composition over union (pre-logos): `(S ∪ T) ⊚ U ⊂ (S⊚U) ∪ (T⊚U)`.
    Derived from the right-distributive `compose_union_right` by reciprocation. -/
private theorem compose_union_left [PreLogos 𝒞] [HasBinaryCoproducts 𝒞]
    {X Y Z : 𝒞} (S T : BinRel 𝒞 X Y) (U : BinRel 𝒞 Y Z) :
    RelLe ((S ∪ᵣ T) ⊚ U) ((S ⊚ U) ∪ᵣ (T ⊚ U)) := by
  have h1 : RelLe (((S ∪ᵣ T) ⊚ U)°) (U° ⊚ (S ∪ᵣ T)°) := reciprocal_comp_le _ _
  have h2 : RelLe (U° ⊚ (S ∪ᵣ T)°) (U° ⊚ (T° ∪ᵣ S°)) :=
    compose_le (rel_le_refl _) (relUnion_le_reciprocal S T)
  have h3 : RelLe (U° ⊚ (T° ∪ᵣ S°)) ((U° ⊚ T°) ∪ᵣ (U° ⊚ S°)) := compose_union_right _ _ _
  have h4 : RelLe ((U° ⊚ T°) ∪ᵣ (U° ⊚ S°)) (((T ⊚ U)°) ∪ᵣ ((S ⊚ U)°)) :=
    le_relUnion (rel_le_trans (comp_reciprocal_le T U) (relUnion_le_left _ _))
                (rel_le_trans (comp_reciprocal_le S U) (relUnion_le_right _ _))
  have h5 : RelLe (((T ⊚ U)°) ∪ᵣ ((S ⊚ U)°)) (((S ⊚ U) ∪ᵣ (T ⊚ U))°) :=
    relUnion_reciprocal_le (S ⊚ U) (T ⊚ U)
  have hrec := rel_le_trans h1 (rel_le_trans h2 (rel_le_trans h3 (rel_le_trans h4 h5)))
  have := reciprocal_monotone hrec
  rwa [reciprocal_invol, reciprocal_invol] at this

/-- DISJOINTNESS VANISHING (§1.62 positivity): if `R`'s right column factors through `inl`
    and `S`'s left column factors through `inr`, then the composite `R ⊚ S` is "empty" — its
    tabulation factors through the bottom subobject.  The composition pullback equalises a
    map into `inl(B)` with a map into `inr(C)`; `inl ∩ inr = 0` (`coprod_inl_inr_disjoint_elt`)
    sends that pullback to `0`, which is initial (`any_map_to_zero_is_iso`), so the whole span
    factors through `bottom`. -/
private theorem relSub_comp_le_bottom [PreToposDisjoint 𝒞]
    {X Y B C : 𝒞} (R : BinRel 𝒞 X (HasBinaryCoproducts.coprod B C))
    (S : BinRel 𝒞 (HasBinaryCoproducts.coprod B C) Y)
    (rB : R.src ⟶ B) (hrB : rB ≫ HasBinaryCoproducts.inl = R.colB)
    (sC : S.src ⟶ C) (hsC : sC ≫ HasBinaryCoproducts.inr = S.colA) :
    (relSub (R ⊚ S)).le (PreLogos.bottom (prod X Y)) := by
  let hPL : PreLogos 𝒞 := inferInstance
  let pb := HasPullbacks.has R.colB S.colA
  have hw : pb.cone.π₁ ≫ R.colB = pb.cone.π₂ ≫ S.colA := pb.cone.w
  have hdisj : (pb.cone.π₁ ≫ rB) ≫ HasBinaryCoproducts.inl
             = (pb.cone.π₂ ≫ sC) ≫ HasBinaryCoproducts.inr := by
    rw [Cat.assoc, hrB, Cat.assoc, hsC]; exact hw
  obtain ⟨e, _⟩ := coprod_inl_inr_disjoint_elt (pb.cone.π₁ ≫ rB) (pb.cone.π₂ ≫ sC) hdisj
  let zeroObj := (minimal_subobject_of_one_is_coterminator hPL).zero
  obtain ⟨ζ, _⟩ := hPL.bottom_dom_iso (HasBinaryCoproducts.coprod B C) hPL.toHasTerminal.one
  let g₀ : pb.cone.pt ⟶ zeroObj := e ≫ ζ
  obtain ⟨g₀inv, hg₀g₀inv, _⟩ := any_map_to_zero_is_iso hPL g₀
  let span : pb.cone.pt ⟶ prod X Y := pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)
  let t : pb.cone.pt ⟶ (PreLogos.bottom (prod X Y)).dom :=
    g₀ ≫ (minimal_subobject_of_one_is_coterminator hPL).init _
  have hfac : span = t ≫ (PreLogos.bottom (prod X Y)).arr := by
    have key : ∀ (w : pb.cone.pt ⟶ prod X Y), w = g₀ ≫ (g₀inv ≫ w) := by
      intro w; rw [← Cat.assoc, hg₀g₀inv, Cat.id_comp]
    rw [key span, key (t ≫ (PreLogos.bottom (prod X Y)).arr)]; congr 1
    exact (minimal_subobject_of_one_is_coterminator hPL).init_uniq _ _
  obtain ⟨k, hk⟩ := image_min span (PreLogos.bottom (prod X Y)) ⟨t, hfac.symm⟩
  exact ⟨k, by rw [hk]; exact (pair_uniq _ _ _ rfl rfl)⟩

/-- Mirror of `relSub_comp_le_bottom`: `R`'s right column through `inr`, `S`'s left through `inl`. -/
private theorem relSub_comp_le_bottom_mirror [PreToposDisjoint 𝒞]
    {X Y B C : 𝒞} (R : BinRel 𝒞 X (HasBinaryCoproducts.coprod B C))
    (S : BinRel 𝒞 (HasBinaryCoproducts.coprod B C) Y)
    (rC : R.src ⟶ C) (hrC : rC ≫ HasBinaryCoproducts.inr = R.colB)
    (sB : S.src ⟶ B) (hsB : sB ≫ HasBinaryCoproducts.inl = S.colA) :
    (relSub (R ⊚ S)).le (PreLogos.bottom (prod X Y)) := by
  let hPL : PreLogos 𝒞 := inferInstance
  let pb := HasPullbacks.has R.colB S.colA
  have hw : pb.cone.π₁ ≫ R.colB = pb.cone.π₂ ≫ S.colA := pb.cone.w
  have hdisj : (pb.cone.π₂ ≫ sB) ≫ HasBinaryCoproducts.inl
             = (pb.cone.π₁ ≫ rC) ≫ HasBinaryCoproducts.inr := by
    rw [Cat.assoc, hsB, Cat.assoc, hrC]; exact hw.symm
  obtain ⟨e, _⟩ := coprod_inl_inr_disjoint_elt (pb.cone.π₂ ≫ sB) (pb.cone.π₁ ≫ rC) hdisj
  let zeroObj := (minimal_subobject_of_one_is_coterminator hPL).zero
  obtain ⟨ζ, _⟩ := hPL.bottom_dom_iso (HasBinaryCoproducts.coprod B C) hPL.toHasTerminal.one
  let g₀ : pb.cone.pt ⟶ zeroObj := e ≫ ζ
  obtain ⟨g₀inv, hg₀g₀inv, _⟩ := any_map_to_zero_is_iso hPL g₀
  let span : pb.cone.pt ⟶ prod X Y := pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)
  let t : pb.cone.pt ⟶ (PreLogos.bottom (prod X Y)).dom :=
    g₀ ≫ (minimal_subobject_of_one_is_coterminator hPL).init _
  have hfac : span = t ≫ (PreLogos.bottom (prod X Y)).arr := by
    have key : ∀ (w : pb.cone.pt ⟶ prod X Y), w = g₀ ≫ (g₀inv ≫ w) := by
      intro w; rw [← Cat.assoc, hg₀g₀inv, Cat.id_comp]
    rw [key span, key (t ≫ (PreLogos.bottom (prod X Y)).arr)]; congr 1
    exact (minimal_subobject_of_one_is_coterminator hPL).init_uniq _ _
  obtain ⟨k, hk⟩ := image_min span (PreLogos.bottom (prod X Y)) ⟨t, hfac.symm⟩
  exact ⟨k, by rw [hk]; exact (pair_uniq _ _ _ rfl rfl)⟩

/-- Below-bottom propagates through right-composition: if `Z`'s tabulation is below bottom
    (so `Z.src ≅ 0`), then so is `T ⊚ Z`'s (its composition pullback maps to the initial
    `Z.src`, hence is initial). -/
private theorem relSub_comp_le_bottom_right [PreToposDisjoint 𝒞]
    {X Y W : 𝒞} (T : BinRel 𝒞 W X) (Z : BinRel 𝒞 X Y)
    (h : (relSub Z).le (PreLogos.bottom (prod X Y))) :
    (relSub (T ⊚ Z)).le (PreLogos.bottom (prod W Y)) := by
  let hPL : PreLogos 𝒞 := inferInstance
  let zeroObj := (minimal_subobject_of_one_is_coterminator hPL).zero
  obtain ⟨zb, _⟩ := h
  obtain ⟨ζ, _⟩ := hPL.bottom_dom_iso (prod X Y) hPL.toHasTerminal.one
  let pb := HasPullbacks.has T.colB Z.colA
  let span : pb.cone.pt ⟶ prod W Y := pair (pb.cone.π₁ ≫ T.colA) (pb.cone.π₂ ≫ Z.colB)
  let g₀ : pb.cone.pt ⟶ zeroObj := pb.cone.π₂ ≫ zb ≫ ζ
  obtain ⟨g₀inv, hg₀g₀inv, _⟩ := any_map_to_zero_is_iso hPL g₀
  let t : pb.cone.pt ⟶ (PreLogos.bottom (prod W Y)).dom :=
    g₀ ≫ (minimal_subobject_of_one_is_coterminator hPL).init _
  have hfac : span = t ≫ (PreLogos.bottom (prod W Y)).arr := by
    have key : ∀ (w : pb.cone.pt ⟶ prod W Y), w = g₀ ≫ (g₀inv ≫ w) := by
      intro w; rw [← Cat.assoc, hg₀g₀inv, Cat.id_comp]
    rw [key span, key (t ≫ (PreLogos.bottom (prod W Y)).arr)]; congr 1
    exact (minimal_subobject_of_one_is_coterminator hPL).init_uniq _ _
  obtain ⟨k, hk⟩ := image_min span (PreLogos.bottom (prod W Y)) ⟨t, hfac.symm⟩
  exact ⟨k, by rw [hk]; exact (pair_uniq _ _ _ rfl rfl)⟩

/-- Below-bottom propagates through left-composition (mirror of `relSub_comp_le_bottom_right`). -/
private theorem relSub_comp_le_bottom_left [PreToposDisjoint 𝒞]
    {W X Y : 𝒞} (Z : BinRel 𝒞 W X) (T : BinRel 𝒞 X Y)
    (h : (relSub Z).le (PreLogos.bottom (prod W X))) :
    (relSub (Z ⊚ T)).le (PreLogos.bottom (prod W Y)) := by
  let hPL : PreLogos 𝒞 := inferInstance
  let zeroObj := (minimal_subobject_of_one_is_coterminator hPL).zero
  obtain ⟨zb, _⟩ := h
  obtain ⟨ζ, _⟩ := hPL.bottom_dom_iso (prod W X) hPL.toHasTerminal.one
  let pb := HasPullbacks.has Z.colB T.colA
  let span : pb.cone.pt ⟶ prod W Y := pair (pb.cone.π₁ ≫ Z.colA) (pb.cone.π₂ ≫ T.colB)
  let g₀ : pb.cone.pt ⟶ zeroObj := pb.cone.π₁ ≫ zb ≫ ζ
  obtain ⟨g₀inv, hg₀g₀inv, _⟩ := any_map_to_zero_is_iso hPL g₀
  let t : pb.cone.pt ⟶ (PreLogos.bottom (prod W Y)).dom :=
    g₀ ≫ (minimal_subobject_of_one_is_coterminator hPL).init _
  have hfac : span = t ≫ (PreLogos.bottom (prod W Y)).arr := by
    have key : ∀ (w : pb.cone.pt ⟶ prod W Y), w = g₀ ≫ (g₀inv ≫ w) := by
      intro w; rw [← Cat.assoc, hg₀g₀inv, Cat.id_comp]
    rw [key span, key (t ≫ (PreLogos.bottom (prod W Y)).arr)]; congr 1
    exact (minimal_subobject_of_one_is_coterminator hPL).init_uniq _ _
  obtain ⟨k, hk⟩ := image_min span (PreLogos.bottom (prod W Y)) ⟨t, hfac.symm⟩
  exact ⟨k, by rw [hk]; exact (pair_uniq _ _ _ rfl rfl)⟩

/-- The amalgamation descent core: with `LE := level q` packaged inside the minimal
    equivalence `E` (`LE ⊂ E ⊂ F = 1 ∪ R₀ ∪ R₀°`), and the cross terms vanishing against the
    monic injection `j` (positivity), the level of `j ≫ q` is contained in the diagonal, so
    `j ≫ q` is monic.  Both legs (`inl`, `inr`) of §1.651 are instances of this. -/
private theorem amalgamation_leg_mono [PreToposDisjoint 𝒞]
    {Bj M D : 𝒞} (j : Bj ⟶ M) (hj : Mono j) (q : M ⟶ D)
    (R₀ : BinRel 𝒞 M M)
    (hLELE : RelLe (kernelPairRel (j ≫ q)) (graph j ⊚ ((graph q ⊚ (graph q)°) ⊚ (graph j)°)))
    (hLEF : RelLe (graph q ⊚ (graph q)°) ((graph (Cat.id M) ∪ᵣ R₀) ∪ᵣ R₀°))
    (hc1 : RelLe (graph j ⊚ (R₀ ⊚ (graph j)°)) (graph (Cat.id Bj)))
    (hc2 : RelLe (graph j ⊚ (R₀° ⊚ (graph j)°)) (graph (Cat.id Bj))) :
    Mono (j ≫ q) := by
  apply mono_of_kernelPairRel_le_diag
  -- bound graph j ⊚ ((graph q ⊚ (graph q)°) ⊚ (graph j)°) ⊂ 1_Bj
  let Δ : BinRel 𝒞 M M := graph (Cat.id M)
  let G := graph q ⊚ (graph q)°
  let F := (Δ ∪ᵣ R₀) ∪ᵣ R₀°
  have hmono : RelLe (graph j ⊚ (G ⊚ (graph j)°)) (graph j ⊚ (F ⊚ (graph j)°)) :=
    compose_le (rel_le_refl _) (compose_le hLEF (rel_le_refl _))
  have hdL : RelLe (F ⊚ (graph j)°)
      ((((Δ ⊚ (graph j)°) ∪ᵣ (R₀ ⊚ (graph j)°))) ∪ᵣ (R₀° ⊚ (graph j)°)) := by
    refine rel_le_trans (compose_union_left (Δ ∪ᵣ R₀) R₀° ((graph j)°)) ?_
    exact le_relUnion
      (rel_le_trans (compose_union_left Δ R₀ ((graph j)°))
        (le_relUnion (rel_le_trans (relUnion_le_left _ _) (relUnion_le_left _ _))
                     (rel_le_trans (relUnion_le_right _ _) (relUnion_le_left _ _))))
      (relUnion_le_right _ _)
  have hpushL : RelLe (graph j ⊚ (F ⊚ (graph j)°))
      (graph j ⊚ ((((Δ ⊚ (graph j)°) ∪ᵣ (R₀ ⊚ (graph j)°))) ∪ᵣ (R₀° ⊚ (graph j)°))) :=
    compose_le (rel_le_refl _) hdL
  have hdR : RelLe (graph j ⊚ ((((Δ ⊚ (graph j)°) ∪ᵣ (R₀ ⊚ (graph j)°))) ∪ᵣ (R₀° ⊚ (graph j)°)))
      ((((graph j ⊚ (Δ ⊚ (graph j)°)) ∪ᵣ (graph j ⊚ (R₀ ⊚ (graph j)°))))
        ∪ᵣ (graph j ⊚ (R₀° ⊚ (graph j)°))) := by
    refine rel_le_trans (compose_union_right (graph j) _ _) ?_
    exact le_relUnion
      (rel_le_trans (compose_union_right (graph j) _ _)
        (le_relUnion (rel_le_trans (relUnion_le_left _ _) (relUnion_le_left _ _))
                     (rel_le_trans (relUnion_le_right _ _) (relUnion_le_left _ _))))
      (relUnion_le_right _ _)
  have hdiag : RelLe (graph j ⊚ (Δ ⊚ (graph j)°)) (graph (Cat.id Bj)) :=
    rel_le_trans (compose_le (rel_le_refl _) (graph_id_comp ((graph j)°)))
      (graph_comp_recip_le_one_of_mono j hj)
  have hfinal : RelLe ((((graph j ⊚ (Δ ⊚ (graph j)°)) ∪ᵣ (graph j ⊚ (R₀ ⊚ (graph j)°))))
        ∪ᵣ (graph j ⊚ (R₀° ⊚ (graph j)°))) (graph (Cat.id Bj)) :=
    le_relUnion (le_relUnion hdiag hc1) hc2
  exact rel_le_trans hLELE
    (rel_le_trans hmono (rel_le_trans hpushL (rel_le_trans hdR hfinal)))

/-- The generated relation `R₀` (image of `pair xi yi`) is contained in the reciprocal
    composite `(graph xi)° ⊚ (graph yi)`: a point `a : A` lifts to the pullback diagonal,
    and the image of its span allows `R₀`'s tabulation. -/
private theorem image_pair_le_recip_comp [PreToposDisjoint 𝒞] {A M N : 𝒞}
    (xi : A ⟶ M) (yi : A ⟶ N) :
    RelLe (⟨(image (pair xi yi)).dom, (image (pair xi yi)).arr ≫ fst,
            (image (pair xi yi)).arr ≫ snd,
            monicPair_of_monic_pair _ _ (by rw [← pair_eta]; exact (image (pair xi yi)).monic)⟩
            : BinRel 𝒞 M N)
      ((graph xi)° ⊚ (graph yi)) := by
  let P := (graph xi)° ⊚ (graph yi)
  let pbP := HasPullbacks.has ((graph xi)°).colB ((graph yi).colA)
  have hcw : (Cat.id A) ≫ ((graph xi)°).colB = (Cat.id A) ≫ ((graph yi).colA) := by
    simp [graph, reciprocal]
  let dpt : A ⟶ pbP.cone.pt := pbP.lift ⟨A, Cat.id A, Cat.id A, hcw⟩
  have hd1 : dpt ≫ pbP.cone.π₁ = Cat.id A := pbP.lift_fst _
  have hd2 : dpt ≫ pbP.cone.π₂ = Cat.id A := pbP.lift_snd _
  let spanP : pbP.cone.pt ⟶ prod M N :=
    pair (pbP.cone.π₁ ≫ ((graph xi)°).colA) (pbP.cone.π₂ ≫ (graph yi).colB)
  have hdsp : dpt ≫ spanP = pair xi yi := by
    apply pair_uniq
    · show (dpt ≫ spanP) ≫ fst = xi
      rw [Cat.assoc, fst_pair, ← Cat.assoc, hd1, Cat.id_comp]; rfl
    · show (dpt ≫ spanP) ≫ snd = yi
      rw [Cat.assoc, snd_pair, ← Cat.assoc, hd2, Cat.id_comp]; rfl
  let Psub : Subobject 𝒞 (prod M N) := relSub P
  have hPsub_arr : Psub.arr = (image spanP).arr := (pair_uniq _ _ _ rfl rfl).symm
  have hallow : Allows Psub (pair xi yi) :=
    ⟨dpt ≫ image.lift spanP, by rw [hPsub_arr, Cat.assoc, image.lift_fac, hdsp]⟩
  obtain ⟨k, hk⟩ := image_min (pair xi yi) Psub hallow
  have hkP : k ≫ (image spanP).arr = (image (pair xi yi)).arr := by rw [← hPsub_arr]; exact hk
  refine ⟨⟨k, ?_, ?_⟩⟩
  · show k ≫ ((image spanP).arr ≫ fst) = (image (pair xi yi)).arr ≫ fst
    rw [← Cat.assoc, hkP]
  · show k ≫ ((image spanP).arr ≫ snd) = (image (pair xi yi)).arr ≫ snd
    rw [← Cat.assoc, hkP]

/-- Partial-bijection lemma: `P ⊚ P° ⊂ 1` for `P = (graph s)° ⊚ graph t` when the RIGHT
    morphism `t` is monic.  (Companion to the §1.62 `diag_le_one`, which gives `P° ⊚ P ⊂ 1`
    for `s` monic.)  Both feed the transitivity of the generated equivalence `F`. -/
private theorem comp_recip_self_le_diag [PreToposDisjoint 𝒞] {Bj N M : 𝒞}
    (s : Bj ⟶ M) (t : Bj ⟶ N) (ht : Mono t) :
    RelLe (((graph s)° ⊚ graph t) ⊚ ((graph s)° ⊚ graph t)°) (graph (Cat.id M)) := by
  let P := (graph s)° ⊚ graph t
  have hP : RelLe (P°) ((graph t)° ⊚ graph s) := by
    have h := reciprocal_comp_le ((graph s)°) (graph t)
    rw [reciprocal_invol] at h; exact h
  have h1 : RelLe (P ⊚ P°) (P ⊚ ((graph t)° ⊚ graph s)) := compose_le (rel_le_refl _) hP
  have h2 : RelLe (P ⊚ ((graph t)° ⊚ graph s))
      ((graph s)° ⊚ (graph t ⊚ ((graph t)° ⊚ graph s))) :=
    (compose_assoc_of_regular ((graph s)°) (graph t) ((graph t)° ⊚ graph s)).1
  have h3 : RelLe (graph t ⊚ ((graph t)° ⊚ graph s)) ((graph t ⊚ (graph t)°) ⊚ graph s) :=
    (compose_assoc_of_regular (graph t) ((graph t)°) (graph s)).2
  have h4 : RelLe ((graph t ⊚ (graph t)°) ⊚ graph s) (graph (Cat.id Bj) ⊚ graph s) :=
    compose_le (graph_comp_recip_le_one_of_mono t ht) (rel_le_refl _)
  have h345 : RelLe (graph t ⊚ ((graph t)° ⊚ graph s)) (graph s) :=
    rel_le_trans h3 (rel_le_trans h4 (graph_id_comp (graph s)))
  have h6 : RelLe ((graph s)° ⊚ (graph t ⊚ ((graph t)° ⊚ graph s))) ((graph s)° ⊚ graph s) :=
    compose_le (rel_le_refl _) h345
  exact rel_le_trans h1 (rel_le_trans h2 (rel_le_trans h6 (reciprocal_comp_self_le_one s)))

/-- The generated relation `F = 1 ∪ R₀ ∪ R₀°` is an equivalence relation, given the four
    cross-composite bounds (`R₀R₀°, R₀°R₀ ⊂ 1` from partial-bijectivity; `R₀R₀, R₀°R₀° ⊂ 1`
    from coproduct disjointness).  Reflexivity and symmetry are union bookkeeping; transitivity
    distributes `F ⊚ F` into nine pieces, each landing back inside `F`. -/
private theorem amalgamation_F_equiv [PreToposDisjoint 𝒞] {M : 𝒞} (R₀ : BinRel 𝒞 M M)
    (hRRop : RelLe (R₀ ⊚ R₀°) (graph (Cat.id M)))
    (hRopR : RelLe (R₀° ⊚ R₀) (graph (Cat.id M)))
    (hRR : RelLe (R₀ ⊚ R₀) (graph (Cat.id M)))
    (hRopRop : RelLe (R₀° ⊚ R₀°) (graph (Cat.id M))) :
    EquivalenceRelation ((graph (Cat.id M) ∪ᵣ R₀) ∪ᵣ R₀°) := by
  let Δ : BinRel 𝒞 M M := graph (Cat.id M)
  let F : BinRel 𝒞 M M := (Δ ∪ᵣ R₀) ∪ᵣ R₀°
  have hΔF : RelLe Δ F := rel_le_trans (relUnion_le_left Δ R₀) (relUnion_le_left _ _)
  have hRF : RelLe R₀ F := rel_le_trans (relUnion_le_right Δ R₀) (relUnion_le_left _ _)
  have hRopF : RelLe (R₀°) F := relUnion_le_right _ _
  apply equivalenceRelation_of_isEquivRel
  refine ⟨hΔF, ?_, ?_⟩
  · show RelLe (F°) F
    have e1 : RelLe (F°) ((R₀°)° ∪ᵣ (Δ ∪ᵣ R₀)°) := relUnion_le_reciprocal (Δ ∪ᵣ R₀) (R₀°)
    have e2 : RelLe ((Δ ∪ᵣ R₀)°) (R₀° ∪ᵣ Δ°) := relUnion_le_reciprocal Δ R₀
    have e3 : RelLe ((R₀°)° ∪ᵣ (Δ ∪ᵣ R₀)°) F := by
      apply le_relUnion
      · rw [reciprocal_invol]; exact hRF
      · refine rel_le_trans e2 (le_relUnion hRopF ?_)
        refine rel_le_trans ?_ hΔF
        have h := reciprocal_monotone (graph_id_le_reciprocal (A := M))
        rwa [reciprocal_invol] at h
    exact rel_le_trans e1 e3
  · show RelLe (F ⊚ F) F
    refine rel_le_trans (compose_union_left (Δ ∪ᵣ R₀) (R₀°) F) ?_
    apply le_relUnion
    · refine rel_le_trans (compose_union_left Δ R₀ F) ?_
      apply le_relUnion
      · exact graph_id_comp F
      · refine rel_le_trans (compose_union_right R₀ (Δ ∪ᵣ R₀) (R₀°)) ?_
        apply le_relUnion
        · refine rel_le_trans (compose_union_right R₀ Δ R₀) ?_
          exact le_relUnion (rel_le_trans (comp_graph_id R₀) hRF) (rel_le_trans hRR hΔF)
        · exact rel_le_trans hRRop hΔF
    · refine rel_le_trans (compose_union_right (R₀°) (Δ ∪ᵣ R₀) (R₀°)) ?_
      apply le_relUnion
      · refine rel_le_trans (compose_union_right (R₀°) Δ R₀) ?_
        exact le_relUnion (rel_le_trans (comp_graph_id (R₀°)) hRopF) (rel_le_trans hRopR hΔF)
      · exact rel_le_trans hRopRop hΔF

/-! ## §1.651 Amalgamation Lemma

  In a pre-topos, given monics x: A↣B, y: A↣C, there exists a
  pushout B ↣ D, C ↣ D completing the square. -/

set_option maxHeartbeats 1000000 in
/-- **§1.651 Amalgamation Lemma**: In a pre-topos, the pushout of two
    monics with a common source exists and the resulting maps are monic.
    Proof: form B+C, define equivalence relation E identifying x(a)∼y(a),
    then the effective quotient B+C ↠ D gives the pushout.

    CONSTRUCTIVE PROGRESS (this file): with `[DisjointBinaryCoproduct 𝒞]` supplying §1.62
    positivity and `[HasReflTransClosure 𝒞]` supplying the reflexive-transitive closure R*
    (§1.77/§1.947), the pushout is now built EXACTLY as Freyd describes (§1.651): on `B+C` take the
    relation `R₀` generated by `{x(a)≫inl ∼ y(a)≫inr}` (the image relation of
    `pair(x≫inl, y≫inr)`), close it to the *minimal equivalence relation* `E ⊇ R₀` — now a
    genuine constructive object via `minEquiv_of_rtc` (the §1.775 equivalence closure
    `(R₀ ∪ R₀°)*`) — and let `q : B+C ↠ D` be the effective quotient by `E` (effectiveness,
    §1.568/§1.65).  Then `u := inl≫q`, `v := inr≫q`.  The commutativity leg `x≫u = y≫v` is
    discharged sorry-free: `R₀ ⊑ E ⊑ level q`, and `R₀`'s two columns are exactly `x≫inl`,
    `y≫inr`, so they agree after `q`.

    SHARPENED RESIDUAL (the `sorry`s below): leg-monicity `Mono u`, `Mono v` — that the level of
    `q` (= `E`, the generated equivalence relation) restricts to the *diagonal* on `inl(B)` (resp.
    `inr(C)`).  Disjointness (`inl_inter_inr_le_bottom`, `coprod_inl_inr_disjoint_elt`) and
    `inl/inr_mono` are necessary, but the proof additionally needs a zigzag/path-length induction
    over the transitive-closure structure of `E`, which the `rtc` abstraction does NOT expose (it
    gives the four closure properties, not an induction principle on `relPow` path length).  That
    path-length descent is exactly the §1.543 effective-quotient analysis.  Faithful sorry on
    precisely the two leg monicities; the object `D`, the maps `u, v`, and the commuting square are
    now real and routed through Freyd's generated-equivalence-relation construction. -/
theorem amalgamation_lemma [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]
    {A B C : 𝒞}
    (x : A ⟶ B) (hx : Mono x) (y : A ⟶ C) (hy : Mono y) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D), Mono u ∧ Mono v ∧ x ≫ u = y ≫ v := by
  -- `PreTopos` supplies the coproduct (via `PositivePreLogos`) and the full regular structure on a
  -- single coherent path; we take *only* `[PreTopos 𝒞]` (plus `[HasReflTransClosure 𝒞]`) so that
  -- the `EquivalenceRelation E` proof from `minEquiv_of_rtc`, the `HasReflTransClosure` binder, and
  -- `EffectiveRegular.effective` all share one `RegularCategory` instance (no diamond).  §1.62
  -- disjointness (`inl_inter_inr_le_bottom`, `inl/inr_mono`) is what the *leg-monicity* residual
  -- below needs; it is documented there, supplied by `[DisjointBinaryCoproduct 𝒞]` when that proof
  -- is completed.
  -- Generated relation R₀ on B+C: image of pair(x≫inl, y≫inr) : A → (B+C)×(B+C).
  let xi : A ⟶ HasBinaryCoproducts.coprod B C := x ≫ HasBinaryCoproducts.inl
  let yi : A ⟶ HasBinaryCoproducts.coprod B C := y ≫ HasBinaryCoproducts.inr
  let sp : A ⟶ prod (HasBinaryCoproducts.coprod B C) (HasBinaryCoproducts.coprod B C) := pair xi yi
  let I := image sp
  have hImp : MonicPair (I.arr ≫ fst) (I.arr ≫ snd) :=
    monicPair_of_monic_pair _ _ (by rw [← pair_eta I.arr]; exact I.monic)
  let R₀ : BinRel 𝒞 (HasBinaryCoproducts.coprod B C) (HasBinaryCoproducts.coprod B C) :=
    ⟨I.dom, I.arr ≫ fst, I.arr ≫ snd, hImp⟩
  have hR₀A : image.lift sp ≫ R₀.colA = xi := by
    show image.lift sp ≫ I.arr ≫ fst = xi; rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hR₀B : image.lift sp ≫ R₀.colB = yi := by
    show image.lift sp ≫ I.arr ≫ snd = yi; rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- Generated minimal equivalence relation E ⊇ R₀ (the §1.775 equivalence closure, via rtc).
  obtain ⟨E, hEeq, hR₀E, _hEmin⟩ := minEquiv_of_rtc (HasBinaryCoproducts.coprod B C) R₀
  -- Effective quotient: a cover q : B+C ↠ D with level(q) ⊇ E.
  obtain ⟨_, D, q, _hqcov, hEle, _hleE⟩ := EffectiveRegular.effective E hEeq
  -- ===== Shared leg-monicity infrastructure (used for both `u` and `v`) =====
  -- `xi`, `yi` are monic (composites of monics with the monic injections).
  have hxi : Mono xi := by
    intro W f g h
    apply hx; apply inl_mono (A := B) (B := C)
    show (f ≫ x) ≫ HasBinaryCoproducts.inl = (g ≫ x) ≫ HasBinaryCoproducts.inl
    simpa [xi, Cat.assoc] using h
  have hyi : Mono yi := by
    intro W f g h
    apply hy; apply inr_mono (A := B) (B := C)
    show (f ≫ y) ≫ HasBinaryCoproducts.inr = (g ≫ y) ≫ HasBinaryCoproducts.inr
    simpa [yi, Cat.assoc] using h
  -- `R₀`'s columns factor through the injections (cover⊥mono descent over the image cover).
  obtain ⟨tA, htA⟩ : ∃ t : R₀.src ⟶ B, t ≫ HasBinaryCoproducts.inl = R₀.colA := by
    obtain ⟨t, _, ht⟩ := cover_mono_diagonal (image_lift_cover sp) inl_mono
      (c := image.lift sp) (f := R₀.colA) (m := HasBinaryCoproducts.inl) (d := x) (by rw [hR₀A])
    exact ⟨t, ht⟩
  obtain ⟨tB, htB⟩ : ∃ t : R₀.src ⟶ C, t ≫ HasBinaryCoproducts.inr = R₀.colB := by
    obtain ⟨t, _, ht⟩ := cover_mono_diagonal (image_lift_cover sp) inr_mono
      (c := image.lift sp) (f := R₀.colB) (m := HasBinaryCoproducts.inr) (d := y) (by rw [hR₀B])
    exact ⟨t, ht⟩
  -- `R₀ ⊂ P := (graph xi)° ⊚ (graph yi)` (proof-irrelevant monic-pair field makes `R₀` defeq).
  have hR₀P : RelLe R₀ ((graph xi)° ⊚ (graph yi)) := image_pair_le_recip_comp xi yi
  -- The four cross-composite bounds for the generated relation `F = 1 ∪ R₀ ∪ R₀°`.
  have hRRop : RelLe (R₀ ⊚ R₀°) (graph (Cat.id (HasBinaryCoproducts.coprod B C))) :=
    rel_le_trans (compose_le hR₀P (reciprocal_monotone hR₀P))
      (comp_recip_self_le_diag xi yi hyi)
  have hRopR : RelLe (R₀° ⊚ R₀) (graph (Cat.id (HasBinaryCoproducts.coprod B C))) :=
    rel_le_trans (compose_le (reciprocal_monotone hR₀P) hR₀P) (diag_le_one xi yi hxi)
  have hRR : RelLe (R₀ ⊚ R₀) (graph (Cat.id (HasBinaryCoproducts.coprod B C))) :=
    relLe_of_relSub_le_bottom (relSub_comp_le_bottom_mirror R₀ R₀ tB htB tA htA)
  have hRopRop : RelLe (R₀° ⊚ R₀°) (graph (Cat.id (HasBinaryCoproducts.coprod B C))) :=
    relLe_of_relSub_le_bottom (relSub_comp_le_bottom R₀° R₀° tA htA tB htB)
  -- `F` is an equivalence relation ⊇ R₀; minimality of `E` gives `level q ⊂ E ⊂ F`.
  have hFeq : EquivalenceRelation
      ((graph (Cat.id (HasBinaryCoproducts.coprod B C)) ∪ᵣ R₀) ∪ᵣ R₀°) :=
    amalgamation_F_equiv R₀ hRRop hRopR hRR hRopRop
  have hR₀F : RelLe R₀
      ((graph (Cat.id (HasBinaryCoproducts.coprod B C)) ∪ᵣ R₀) ∪ᵣ R₀°) :=
    rel_le_trans (relUnion_le_right _ R₀) (relUnion_le_left _ _)
  have hEF : RelLe E ((graph (Cat.id (HasBinaryCoproducts.coprod B C)) ∪ᵣ R₀) ∪ᵣ R₀°) :=
    _hEmin _ hFeq hR₀F
  have hLEF : RelLe (graph q ⊚ (graph q)°)
      ((graph (Cat.id (HasBinaryCoproducts.coprod B C)) ∪ᵣ R₀) ∪ᵣ R₀°) :=
    rel_le_trans _hleE hEF
  -- The level-of-`(j ≫ q)` containment chain (shared shape for both legs).
  have hLELE : ∀ {Bj : 𝒞} (j : Bj ⟶ HasBinaryCoproducts.coprod B C),
      RelLe (kernelPairRel (j ≫ q)) (graph j ⊚ ((graph q ⊚ (graph q)°) ⊚ (graph j)°)) := by
    intro Bj j
    have s0 : RelLe (kernelPairRel (j ≫ q)) (graph (j ≫ q) ⊚ (graph (j ≫ q))°) :=
      kernelPairRel_le_graphComp (j ≫ q)
    have s1 : RelLe (graph (j ≫ q)) (graph j ⊚ graph q) := graph_comp j q
    have s2 : RelLe ((graph (j ≫ q))°) ((graph q)° ⊚ (graph j)°) :=
      rel_le_trans (reciprocal_monotone s1) (reciprocal_comp_le (graph j) (graph q))
    have s3 : RelLe (graph (j ≫ q) ⊚ (graph (j ≫ q))°)
        ((graph j ⊚ graph q) ⊚ ((graph q)° ⊚ (graph j)°)) := compose_le s1 s2
    have s4 : RelLe ((graph j ⊚ graph q) ⊚ ((graph q)° ⊚ (graph j)°))
        (graph j ⊚ (graph q ⊚ ((graph q)° ⊚ (graph j)°))) :=
      (compose_assoc_of_regular (graph j) (graph q) ((graph q)° ⊚ (graph j)°)).1
    have s5 : RelLe (graph q ⊚ ((graph q)° ⊚ (graph j)°))
        ((graph q ⊚ (graph q)°) ⊚ (graph j)°) :=
      (compose_assoc_of_regular (graph q) ((graph q)°) ((graph j)°)).2
    have s6 : RelLe (graph j ⊚ (graph q ⊚ ((graph q)° ⊚ (graph j)°)))
        (graph j ⊚ ((graph q ⊚ (graph q)°) ⊚ (graph j)°)) := compose_le (rel_le_refl _) s5
    exact rel_le_trans s0 (rel_le_trans s3 (rel_le_trans s4 s6))
  refine ⟨D, HasBinaryCoproducts.inl ≫ q, HasBinaryCoproducts.inr ≫ q, ?_, ?_, ?_⟩
  · -- Mono u = Mono (inl ≫ q): minimality-descent leg-monicity (§1.651, positivity).
    refine amalgamation_leg_mono HasBinaryCoproducts.inl inl_mono q R₀ (hLELE _) hLEF ?_ ?_
    · -- graph inl ⊚ (R₀ ⊚ (graph inl)°) ⊂ 1_B
      refine relLe_of_relSub_le_bottom
        (relSub_comp_le_bottom_right (graph HasBinaryCoproducts.inl) _ ?_)
      refine relSub_comp_le_bottom_mirror R₀ ((graph HasBinaryCoproducts.inl)°) tB htB
        (Cat.id B) ?_
      exact Cat.id_comp _
    · -- graph inl ⊚ (R₀° ⊚ (graph inl)°) ⊂ 1_B  (reassociate, vanish at graph inl / R₀°)
      refine rel_le_trans (compose_assoc_of_regular (graph HasBinaryCoproducts.inl) (R₀°)
        ((graph HasBinaryCoproducts.inl)°)).2 ?_
      refine relLe_of_relSub_le_bottom (relSub_comp_le_bottom_left _ ((graph HasBinaryCoproducts.inl)°) ?_)
      refine relSub_comp_le_bottom (graph HasBinaryCoproducts.inl) (R₀°) (Cat.id B) ?_ tB htB
      exact Cat.id_comp _
  · -- Mono v = Mono (inr ≫ q): symmetric (swap inl↔inr, R₀↔R₀° at the junctions).
    refine amalgamation_leg_mono HasBinaryCoproducts.inr inr_mono q R₀ (hLELE _) hLEF ?_ ?_
    · -- graph inr ⊚ (R₀ ⊚ (graph inr)°) ⊂ 1_C  (reassociate, vanish at graph inr / R₀)
      refine rel_le_trans (compose_assoc_of_regular (graph HasBinaryCoproducts.inr) R₀
        ((graph HasBinaryCoproducts.inr)°)).2 ?_
      refine relLe_of_relSub_le_bottom
        (relSub_comp_le_bottom_left _ ((graph HasBinaryCoproducts.inr)°) ?_)
      refine relSub_comp_le_bottom_mirror (graph HasBinaryCoproducts.inr) R₀ (Cat.id C) ?_ tA htA
      exact Cat.id_comp _
    · -- graph inr ⊚ (R₀° ⊚ (graph inr)°) ⊂ 1_C
      refine relLe_of_relSub_le_bottom
        (relSub_comp_le_bottom_right (graph HasBinaryCoproducts.inr) _ ?_)
      refine relSub_comp_le_bottom R₀° ((graph HasBinaryCoproducts.inr)°) tA htA
        (Cat.id C) ?_
      exact Cat.id_comp _
  · -- commutativity: x≫(inl≫q) = y≫(inr≫q), since R₀ ⊑ E ⊑ level q and R₀'s columns are x≫inl, y≫inr.
    have hR₀kp : RelLe R₀ (kernelPairRel q) :=
      rel_le_trans (rel_le_trans hR₀E hEle) (graphComp_le_kernelPairRel q)
    obtain ⟨⟨w, hwA, hwB⟩⟩ := hR₀kp
    have e1 : w ≫ kp₁ (f := q) = R₀.colA := by simpa [kernelPairRel] using hwA
    have e2 : w ≫ kp₂ (f := q) = R₀.colB := by simpa [kernelPairRel] using hwB
    have hcolq : R₀.colA ≫ q = R₀.colB ≫ q := by
      calc R₀.colA ≫ q = (w ≫ kp₁ (f := q)) ≫ q := by rw [e1]
        _ = w ≫ kp₂ (f := q) ≫ q := by rw [Cat.assoc, kp_sq]
        _ = R₀.colB ≫ q := by rw [← Cat.assoc, e2]
    calc x ≫ HasBinaryCoproducts.inl ≫ q
        = xi ≫ q := by rw [← Cat.assoc]
      _ = (image.lift sp ≫ R₀.colA) ≫ q := by rw [hR₀A]
      _ = image.lift sp ≫ R₀.colA ≫ q := Cat.assoc _ _ _
      _ = image.lift sp ≫ R₀.colB ≫ q := by rw [hcolq]
      _ = (image.lift sp ≫ R₀.colB) ≫ q := (Cat.assoc _ _ _).symm
      _ = yi ≫ q := by rw [hR₀B]
      _ = y ≫ HasBinaryCoproducts.inr ≫ q := Cat.assoc _ _ _

/-! ## §1.652 Covers = epics, Monics = cocovers

  In a pre-topos, covers coincide with epimorphisms, and monics
  coincide with coequalizers (cocovers). -/

theorem preTopos_minEquiv_to_cocartesian {𝒞 : Type u} [Cat.{v} 𝒞] [PreTopos 𝒞]
    (h : HasMinEquivContaining 𝒞) : Nonempty (HasCoequalizers 𝒞) := by
  -- Build coequalizers from the minimal-equivalence hypothesis (§1.657 backward direction).
  -- Key: all Prop reasoning is packaged into hcoeProp via obtain; Classical.choose
  -- then lifts the existential data into the Type world for HasCoequalizer.
  suffices ∀ {C A : 𝒞} (f g : C ⟶ A), HasCoequalizer f g by exact ⟨⟨fun f g => this f g⟩⟩
  intro C A f g
  -- Step 1: Build R = image relation of (f,g) : C → A×A.
  let sp : C ⟶ prod A A := pair f g
  let I := image sp
  have hImp : MonicPair (I.arr ≫ fst) (I.arr ≫ snd) :=
    monicPair_of_monic_pair _ _ (by rw [← pair_eta I.arr]; exact I.monic)
  let R : BinRel 𝒞 A A := ⟨I.dom, I.arr ≫ fst, I.arr ≫ snd, hImp⟩
  have hRA : image.lift sp ≫ R.colA = f := by
    show image.lift sp ≫ I.arr ≫ fst = f; rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hRB : image.lift sp ≫ R.colB = g := by
    show image.lift sp ≫ I.arr ≫ snd = g; rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- Step 2–4: packaged as a Prop lemma so obtain works throughout.
  have hcoeProp : ∃ (Q : 𝒞) (z : A ⟶ Q), Cover z ∧ f ≫ z = g ≫ z ∧
      ∀ {X : 𝒞} (k : A ⟶ X), f ≫ k = g ≫ k →
        ∃ d : Q ⟶ X, z ≫ d = k ∧ ∀ d' : Q ⟶ X, z ≫ d' = k → d' = d := by
    -- Step 2: get minimal equivalence E ⊇ R.
    obtain ⟨E, hEeq, hRE, hEmin⟩ := h A R
    -- Step 3: effectiveness gives cover z : A → Q.
    obtain ⟨_, Q, z, hzcov, hEle, hleE⟩ := EffectiveRegular.effective E hEeq
    -- R ⊂ kernelPairRel z.
    have hRkpz : RelLe R (kernelPairRel z) :=
      rel_le_trans (rel_le_trans hRE hEle) (graphComp_le_kernelPairRel z)
    -- Step 4a: f ≫ z = g ≫ z.
    have hfz : f ≫ z = g ≫ z := by
      obtain ⟨⟨w, hwA, hwB⟩⟩ := hRkpz
      -- hwA : w ≫ (kernelPairRel z).colA = R.colA, i.e. w ≫ kp₁(z) = R.colA
      -- hwB : w ≫ (kernelPairRel z).colB = R.colB, i.e. w ≫ kp₂(z) = R.colB
      have hcolAz : R.colA ≫ z = R.colB ≫ z := by
        have e1 : w ≫ kp₁ (f := z) = R.colA := by simpa [kernelPairRel] using hwA
        have e2 : w ≫ kp₂ (f := z) = R.colB := by simpa [kernelPairRel] using hwB
        calc R.colA ≫ z = (w ≫ kp₁ (f := z)) ≫ z := by rw [e1]
          _ = w ≫ kp₂ (f := z) ≫ z := by rw [Cat.assoc, kp_sq]
          _ = R.colB ≫ z := by rw [← Cat.assoc, e2]
      calc f ≫ z = image.lift sp ≫ R.colA ≫ z := by rw [← hRA, Cat.assoc]
        _ = image.lift sp ≫ R.colB ≫ z := by rw [hcolAz]
        _ = g ≫ z := by rw [← Cat.assoc, hRB]
    -- Step 4b: UMP.
    refine ⟨Q, z, hzcov, hfz, fun {X} k hfk => ?_⟩
    -- R.colA ≫ k = R.colB ≫ k via cover_epi on image.lift sp.
    have hRk : R.colA ≫ k = R.colB ≫ k := by
      apply cover_epi (image_lift_cover sp)
      calc image.lift sp ≫ R.colA ≫ k = f ≫ k := by rw [← Cat.assoc, hRA]
        _ = g ≫ k := hfk
        _ = image.lift sp ≫ R.colB ≫ k := by rw [← Cat.assoc, hRB]
    -- R ⊂ kernelPairRel k.
    have hRkpk : RelLe R (kernelPairRel k) := by
      let l := (HasPullbacks.has k k).lift ⟨_, R.colA, R.colB, hRk⟩
      exact ⟨⟨l, kp_lift_p₁ R.colA R.colB hRk, kp_lift_p₂ R.colA R.colB hRk⟩⟩
    -- E ⊂ kernelPairRel k by minimality.
    have hEkpk := hEmin (kernelPairRel k) (level_is_equivalence_relation k) hRkpk
    -- kernelPairRel z ⊂ kernelPairRel k.
    have hkpzkpk : RelLe (kernelPairRel z) (kernelPairRel k) :=
      rel_le_trans (rel_le_trans (kernelPairRel_le_graphComp z) hleE) hEkpk
    -- kp₁(z) ≫ k = kp₂(z) ≫ k.
    have hkpeq : kp₁ (f := z) ≫ k = kp₂ (f := z) ≫ k := by
      obtain ⟨⟨φ, hφA, hφB⟩⟩ := hkpzkpk
      -- hφA : φ ≫ (kernelPairRel k).colA = (kernelPairRel z).colA, i.e. φ ≫ kp₁(k) = kp₁(z)
      -- hφB : φ ≫ (kernelPairRel k).colB = (kernelPairRel z).colB, i.e. φ ≫ kp₂(k) = kp₂(z)
      have e1 : φ ≫ kp₁ (f := k) = kp₁ (f := z) := by simpa [kernelPairRel] using hφA
      have e2 : φ ≫ kp₂ (f := k) = kp₂ (f := z) := by simpa [kernelPairRel] using hφB
      calc kp₁ (f := z) ≫ k = (φ ≫ kp₁ (f := k)) ≫ k := by rw [e1]
        _ = φ ≫ kp₂ (f := k) ≫ k := by rw [Cat.assoc, kp_sq]
        _ = kp₂ (f := z) ≫ k := by rw [← Cat.assoc, e2]
    exact cover_is_coequalizer_of_level z hzcov k hkpeq
  -- Lift the Prop data into the HasCoequalizer structure using Classical.choose.
  let Q  := Classical.choose hcoeProp
  let hz := Classical.choose_spec hcoeProp  -- ∃ z, ...
  let z  := Classical.choose hz
  let hzdata := Classical.choose_spec hz    -- Cover z ∧ f≫z=g≫z ∧ UMP
  have hzcov : Cover z := hzdata.1
  have hfz   : f ≫ z = g ≫ z := hzdata.2.1
  have hUMP  : ∀ {X : 𝒞} (k : A ⟶ X), f ≫ k = g ≫ k →
      ∃ d : Q ⟶ X, z ≫ d = k ∧ ∀ d' : Q ⟶ X, z ≫ d' = k → d' = d := hzdata.2.2
  exact {
    obj  := Q
    map  := z
    eq   := hfz
    desc := fun k hfk => Classical.choose (hUMP k hfk)
    fac  := fun k hfk => (Classical.choose_spec (hUMP k hfk)).1
    uniq := fun k hfk m hm => (Classical.choose_spec (hUMP k hfk)).2 m hm
  }

/-! ### §1.652 cokernel-pair infrastructure (effective-coregularity scaffolding)

  The cokernel pair of `m : A → B` is the pushout of `(m, m)`, equivalently the
  COEQUALIZER of the two injections `m ≫ inl, m ≫ inr : A ⇉ B ⊕ B`.  A pre-topos has
  binary coproducts (via `PositivePreLogos`) and — with `[HasReflTransClosure 𝒞]` —
  coequalizers (`preTopos_minEquiv_to_cocartesian (minEquiv_of_rtc)`), so this object is
  a genuine, sorry-free construction.  It is the dual of the kernel pair used throughout
  §1.566/§1.567, and is the carrier of the §1.652 balancedness / monic-is-cocover content.

  Built here as standalone data so all three §1.652/§1.653 obligations share one
  construction (DRY).  The coequalizer map `c : B ⊕ B ↠ P` is a cover (`coeq_map_is_cover`),
  hence (§1.566) the coequalizer of its own kernel pair; the two legs `u := inl ≫ c`,
  `v := inr ≫ c` satisfy `m ≫ u = m ≫ v`, and `m` factors through the equalizer of `(u, v)`. -/

/-- The cokernel pair of `m`, packaged as the coequalizer of `(m ≫ inl, m ≫ inr)`. -/
noncomputable def cokernelPair [PreTopos 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (m : A ⟶ B) :
    HasCoequalizer (m ≫ HasBinaryCoproducts.inl (B := B))
                   (m ≫ HasBinaryCoproducts.inr (B := B)) :=
  HasCoequalizers.coeq _ _

/-- Left cokernel-pair leg `u := inl ≫ c : B → P`. -/
noncomputable def cokernelPairU [PreTopos 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (m : A ⟶ B) :
    B ⟶ (cokernelPair m).obj :=
  HasBinaryCoproducts.inl ≫ (cokernelPair m).map

/-- Right cokernel-pair leg `v := inr ≫ c : B → P`. -/
noncomputable def cokernelPairV [PreTopos 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (m : A ⟶ B) :
    B ⟶ (cokernelPair m).obj :=
  HasBinaryCoproducts.inr ≫ (cokernelPair m).map

/-- The cokernel-pair square commutes: `m ≫ u = m ≫ v` (the coequalizer equation). -/
theorem cokernelPair_sq [PreTopos 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (m : A ⟶ B) :
    m ≫ cokernelPairU m = m ≫ cokernelPairV m := by
  unfold cokernelPairU cokernelPairV
  rw [← Cat.assoc, ← Cat.assoc]; exact (cokernelPair m).eq

/-- The coequalizer map `c : B ⊕ B ↠ P` of the cokernel pair is a cover. -/
theorem cokernelPair_cover [PreTopos 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (m : A ⟶ B) :
    Cover (cokernelPair m).map :=
  coeq_map_is_cover (cokernelPair m)

/-- FORWARD half of effective coregularity: `m` factors through the equalizer of its
    cokernel-pair legs `(u, v)`, via the equalizer universal property applied to the
    commuting square `m ≫ u = m ≫ v`.  (The REVERSE half — that this equalizer factor is
    iso, i.e. `m` IS the equalizer of `(u, v)` — is the open §1.543 residual documented on
    `pretopos_balanced`.) -/
theorem cokernelPair_m_factors_eq [PreTopos 𝒞] [HasCoequalizers 𝒞] [HasEqualizers 𝒞]
    {A B : 𝒞} (m : A ⟶ B) :
    eqLift (cokernelPairU m) (cokernelPairV m) m (cokernelPair_sq m)
      ≫ eqMap (cokernelPairU m) (cokernelPairV m) = m :=
  eqLift_fac _ _ _ _

/-- **§1.652 (crux): a pre-topos is BALANCED** — a map that is both monic and
    epic is an isomorphism.  This is the genuine positivity content of §1.652:
    the cokernel pair of `m` is built from the *disjoint* coproduct `B + B`
    (positivity) via the effective quotient, and a monic that is also epic
    equalizes a pair of equal legs, hence splits.  It is **not** derivable from
    the current axioms — `HasBinaryCoproducts` carries only the bare universal
    property, with no disjointness/universality, so the cokernel-pair argument
    has no axiom to stand on.  Isolated here as the single obligation that both
    reverse-directions below (`cover_eq_epic_preTopos`, `monic_eq_cocover`) rest
    on; closing it needs §1.62 positivity axiomatized as Freyd states it
    (disjoint + universal coproducts).

    STATE (cokernel-pair infrastructure now in place, independent of `amalgamation_lemma`):
    the cokernel pair of `m` is built FRESH as the coequalizer `c : B ⊕ B ↠ P` of
    `(m ≫ inl, m ≫ inr)` (`cokernelPair`/`cokernelPairU`/`cokernelPairV`), with legs `u, v`
    satisfying `m ≫ u = m ≫ v` (`cokernelPair_sq`) and `c` a cover (`cokernelPair_cover`).
    `m` epic immediately forces `u = v` (`hepi`).  The proof is reduced to ONE sharp
    reverse-factorization obligation `hsplit` below: `m` is SPLIT EPIC (`∃ s, s ≫ m = id`).
    That is the REVERSE half of "`m` is the equalizer of its cokernel pair `(u, v)`" applied to
    `id_B` (which equalizes `(u, v)` since `u = v`).  Mono + split-epi ⟹ iso closes it.

    Why `hsplit` is genuinely open (effective COregularity, §1.543).  The forward half is done
    (`cokernelPair_m_factors_eq`: `m` factors through `eq(u, v)`).  The reverse needs: the kernel
    pair of the cover `c` is the equivalence relation GENERATED by `(m ≫ inl, m ≫ inr)` over the
    DISJOINT coproduct `B ⊕ B`, and that this generated relation, restricted to the inl-copy ×
    inr-copy cross, relates `inl(b) ∼ inr(b')` only when `b = m(a) = b'` for a common `a : A`.
    `preTopos_cocartesian_to_minEquiv` gives `kernelPairRel c` = *minimal* equiv relation ⊇ the
    generator, but the cross-descent requires a path-length induction over `relPow` of the
    generator on the disjoint coproduct — and `HasReflTransClosure.rtc`/`minEquiv_of_rtc`/
    `EffectiveRegular.effective` expose only `le`/`refl`/`trans`/`minimal`, NOT a `relPow`
    induction principle (that lives on the constructive `transClos`, not the ambient `rtc`).
    This is the documented §1.543 effective-quotient descent; closing it is a NEW
    relational-descent infrastructure build, not a missing axiom.  Faithful sorry on exactly
    `hsplit`; the cokernel pair, its cover, the square, `u = v`, and the forward factorization
    are all real and sorry-free. -/
theorem pretopos_balanced [PreTopos 𝒞] [HasReflTransClosure 𝒞] {A B : 𝒞}
    (m : A ⟶ B) (hm : Mono m)
    (hepi : ∀ {C : 𝒞} (g h : B ⟶ C), m ≫ g = m ≫ h → g = h) : IsIso m := by
  -- Coequalizers are available from the reflexive-transitive closure (§1.657 backward).
  obtain ⟨hcoeq⟩ := preTopos_minEquiv_to_cocartesian (𝒞 := 𝒞) (minEquiv_of_rtc)
  -- Cokernel pair of m (fresh, independent of amalgamation_lemma): legs u, v with m≫u = m≫v.
  have hsq : m ≫ cokernelPairU m = m ≫ cokernelPairV m := cokernelPair_sq m
  -- m epic forces the two legs equal.
  have huv : cokernelPairU m = cokernelPairV m := hepi _ _ hsq
  -- RESIDUAL (effective coregularity, §1.543): id_B equalizes (u, v) (since u = v), so by the
  -- reverse half of "m = equalizer of its cokernel pair" it factors through m, i.e. m is SPLIT
  -- epic.  See the docstring for why this reverse cross-descent is the open §1.543 step.
  have hsplit : ∃ s : B ⟶ A, s ≫ m = Cat.id B := by
    sorry
  -- m monic + split epic ⟹ iso: from s ≫ m = id, m ≫ (s ≫ m) = m = m ≫ id forces m ≫ s = id.
  obtain ⟨s, hs⟩ := hsplit
  refine ⟨s, hm (m ≫ s) (Cat.id A) ?_, hs⟩
  rw [Cat.assoc, hs, Cat.comp_id, Cat.id_comp]

theorem cover_eq_epic_preTopos [PreTopos 𝒞] [HasReflTransClosure 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Cover f ↔ (∀ {C : 𝒞} (g h : B ⟶ C), f ≫ g = f ≫ h → g = h) := by
  constructor
  · -- Cover → epic (§1.512): already proved
    exact cover_epi
  · intro hepi
    rw [cover_iff_image_entire]
    -- Goal: Subobject.IsEntire (image f), i.e., IsIso (image f).arr.
    -- `(image f).arr` is monic; since `f = lift ≫ arr` is epic, `arr` is epic too.
    have h_arr_epi : ∀ {C : 𝒞} (g h : B ⟶ C), (image f).arr ≫ g = (image f).arr ≫ h → g = h := by
      intro C g h heq
      apply hepi
      calc f ≫ g = (image.lift f ≫ (image f).arr) ≫ g := by rw [image.lift_fac f]
        _ = image.lift f ≫ ((image f).arr ≫ g) := Cat.assoc _ _ _
        _ = image.lift f ≫ ((image f).arr ≫ h) := by rw [heq]
        _ = (image.lift f ≫ (image f).arr) ≫ h := by rw [← Cat.assoc]
        _ = f ≫ h := by rw [image.lift_fac f]
    -- monic + epic ⟹ iso by balancedness (`pretopos_balanced`), so `image f` is entire.
    exact pretopos_balanced (image f).arr (image f).monic h_arr_epi

/-- **§1.652**: In a pre-topos, monics coincide with cocovers
    (maps that are coequalizers of some pair).
    Requires effective regularity (every monic is a regular monic = an equalizer,
    dually every epic is a regular epic = a coequalizer).
    The `HEq` in the statement is a placeholder for an isomorphism between
    the coequalizer map and `f`.

    STATE: with `[HasReflTransClosure 𝒞]` the category now has all coequalizers (via
    `minEquiv_of_rtc` fed to `preTopos_minEquiv_to_cocartesian`), so `HasCoequalizers` is no longer
    an *unproven* hypothesis — it is derivable.  It is kept in the signature only because the
    *statement* mentions `HasCoequalizers.coeq`.  The natural witness pair is the cokernel pair of
    `f`: `p := cokernelPairU f`, `q := cokernelPairV f` (now built sorry-free), and the residual is
    EXACTLY the same effective-coregularity step as `pretopos_balanced` — that the mono `f` is the
    equalizer of `(u, v)` and dually that this exhibits `f` as a coequalizer-map.  That cross-descent
    over the disjoint coproduct `B ⊕ B` is the open §1.543 effective-quotient analysis (see the
    `pretopos_balanced` docstring for why `rtc`/`minEquiv`/`effective` do not expose the needed
    `relPow` path-length induction).  Faithful sorry on that shared residual. -/
theorem monic_eq_cocover_preTopos [PreTopos 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Mono f ↔ ∃ (C : 𝒞) (p q : C ⟶ A), HEq ((HasCoequalizers.coeq p q).map) f := by
  sorry

/-! ## §1.653 Pushout of a monic and any morphism in a pre-topos

  Given morphisms f: A → B and monic y: A ↣ C in a pre-topos, there is a pushout
  square with the top map monic.  The proof factors f as cover ∘ monic (image
  factorization) and applies the amalgamation lemma §1.651 to the two monics. -/

/-- **§1.653**: In a pre-topos, given f : A → B and monic y : A ↣ C, there exists a
    pushout square (with the B-map monic).
    PROOF: Factor A → B as A ↠ I ↣ B.  Apply §1.651 to I ↣ B and I ↣ C' (pushing y
    through the cover A ↠ I), stack the two squares, and use the pasting lemma.

    STATE: `amalgamation_lemma` (§1.651) is now a real construction routed through the generated
    equivalence relation (`minEquiv_of_rtc`) and the effective quotient; this §1.653 result is the
    standard reduction to it (image-factor `f`, push `y` through the cover, paste).  The two unmet
    pieces are (a) the cover/image transport of `y` into the slice over the image of `f` and (b) the
    pasting lemma for the stacked square — pullback/pasting infrastructure orthogonal to §1.62
    positivity; the leg-monicity it inherits is the same §1.543 descent residual as §1.651.
    Hypotheses now match `amalgamation_lemma` (`[PreTopos 𝒞] [HasReflTransClosure 𝒞]`).  Faithful
    sorry. -/
theorem pushout_monic_in_pretopos [PreTopos 𝒞] [HasReflTransClosure 𝒞]
    {A B C : 𝒞}
    (f : A ⟶ B) (y : A ⟶ C) (hy : Mono y) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D), Mono u ∧ f ≫ u = y ≫ v := by
  sorry

/-! ## §1.655 Bicartesian representation criterion

  If A and B are pre-topoi and T : A → B a functor preserving 0, pushouts,
  finite products and monics, then T is a bicartesian representation.
  PROOF SKETCH (§1.655): T preserves pullbacks of monics (by §1.651 + pasting);
  T preserves equalizers (products ⟹ equalizers); T preserves covers (=
  coequalizers, §1.652; T preserves pushouts and 0). -/

-- §1.655 (note): A functor T between pre-topoi preserving 0, pushouts, products
-- and monics is a bicartesian representation.
-- PROOF: Products + §1.651 → T preserves pullbacks of monics; products → equalizers
-- (§1.434); covers = coequalizers + pushout preservation → T preserves covers.
-- Requires formalizing the Functor API for inter-category morphisms.

/-! ## §1.658 Decidable object

  An object A in a pre-logos is DECIDABLE if the diagonal (1,1): A → A×A
  has a complement in the subobject lattice of A×A.

  Every object in a pre-topos is decidable iff the pre-topos is boolean.

  PROOF SKETCH:
  (⇐) Boolean ⇒ every subobject is complemented, in particular the diagonal.
  (⇒) Given A decidable, let A' → A×B be any subobject; form the equalizer of
      (A' → A×B → B → B×B) and (A' → A×B → A×B → B×B via diag∘second).
      Because pullbacks of complemented subobjects are complemented (§1.658),
      the Boolean algebra structure transfers to all subobjects via slices. -/

/-- **§1.658**: A in a pre-logos is DECIDABLE if the diagonal `diag A : A → A×A`
    has a complement in `Subobject 𝒞 (prod A A)`.
    Lean note: `diag A` is monic (§1.42: `diag_mono`); the subobject is `{ dom := A, arr := diag A, monic := diag_mono A }`. -/
def DecidableObject [PreLogos 𝒞] [HasBinaryProducts 𝒞] (A : 𝒞) : Prop :=
  IsComplemented ({ dom := A, arr := diag A, monic := diag_mono A } : Subobject 𝒞 (prod A A))

/-- **§1.658**: Every object in a pre-topos is decidable iff the pre-topos is boolean.
    The harder direction (all decidable → boolean) follows because pullbacks of
    complemented subobjects are complemented, and every subobject U ⊆ 1 can be
    pulled back to any slice, where it coincides with the diagonal. -/
theorem preTopos_boolean_iff_all_decidable [PreTopos 𝒞] [HasBinaryProducts 𝒞] :
    (Nonempty (BooleanPreLogos 𝒞)) ↔ ∀ (A : 𝒞), DecidableObject A := by
  refine ⟨fun ⟨hbool⟩ A => ?_, fun h => ?_⟩
  · -- (⇒) BooleanPreLogos → every diagonal subobject is complemented = DecidableObject A.
    -- The instance mismatch between hbool.toPreLogos and the ambient [PreLogos 𝒞] variable
    -- is resolved by using hbool's union_min to bridge to the ambient union.
    unfold DecidableObject IsComplemented
    let diagSub : Subobject 𝒞 (prod A A) := { dom := A, arr := diag A, monic := diag_mono A }
    obtain ⟨A₂, hdisj, hunion⟩ := hbool.hasComplement diagSub
    -- `hdisj` concludes in `hbool`'s bottom; the goal wants the ambient `PreTopos` bottom.
    -- Both are minimal, so `hbool.bottom ≤ ambient.bottom` (`bottom_min`) bridges by composition.
    have hdisj' : ∀ (S : Subobject 𝒞 (prod A A)),
        Subobject.le S diagSub → Subobject.le S A₂ →
        Subobject.le S (@PreLogos.bottom 𝒞 _ PreTopos.toPositivePreLogos.toPreLogos (prod A A)) := by
      intro S h1 h2
      obtain ⟨g1, hg1⟩ := hdisj S h1 h2
      obtain ⟨g2, hg2⟩ := hbool.toPreLogos.bottom_min
        (@PreLogos.bottom 𝒞 _ PreTopos.toPositivePreLogos.toPreLogos (prod A A))
      exact ⟨g1 ≫ g2, by rw [Cat.assoc, hg2, hg1]⟩
    refine ⟨A₂, hdisj', ?_⟩
    -- hunion : entire ≤ hbool.union diagSub A₂; goal: entire ≤ ambient(PreTopos).union diagSub A₂.
    -- Bridge hbool's union to the PreTopos union via hbool.union_min applied with the
    -- PreTopos-union as the common upper bound.  All `union_*` calls are taken from
    -- `hbool.toPreLogos.toHasSubobjectUnions` so they agree with `hunion`.
    let unionAmb := @HasSubobjectUnions.union 𝒞 _ _
      (PreTopos.toPositivePreLogos.toPreLogos.toHasSubobjectUnions) (prod A A) diagSub A₂
    have hleft  : diagSub.le unionAmb :=
      @HasSubobjectUnions.union_left 𝒞 _ _
        (PreTopos.toPositivePreLogos.toPreLogos.toHasSubobjectUnions) (prod A A) diagSub A₂
    have hright : A₂.le unionAmb :=
      @HasSubobjectUnions.union_right 𝒞 _ _
        (PreTopos.toPositivePreLogos.toPreLogos.toHasSubobjectUnions) (prod A A) diagSub A₂
    have hle : (hbool.toPreLogos.toHasSubobjectUnions.union diagSub A₂).le unionAmb :=
      hbool.toPreLogos.toHasSubobjectUnions.union_min diagSub A₂ _ hleft hright
    obtain ⟨e1, he1⟩ := hunion
    obtain ⟨e2, he2⟩ := hle
    exact ⟨e1 ≫ e2, by rw [Cat.assoc, he2, he1]⟩
  · -- (⇐) All decidable → BooleanPreLogos.
    -- Requires pullback stability of complements (§1.658): if K is complemented and f : B → C,
    -- then InverseImage f K is complemented. Every subobject S of B can then be shown
    -- complemented by pulling back the diagonal (which is decidable) along an appropriate map.
    --
    -- SHARPENED BLOCKER (infra audit):
    --   • InverseImage (S1_60:51) and its union-preservation (PreLogos.invImage_preserves_union,
    --     invImage_preserves_bottom, S1_60:89/91) ARE available — so "f# of a complement is a
    --     complement" is *almost* in reach for the `IsComplementedSub` formulation
    --     (Subobject.inter, S1_62:75), but NOT for the `IsComplemented` placeholder used here,
    --     whose intersection clause is the ad-hoc "no nontrivial common lower bound" predicate
    --     rather than `Subobject.inter _ _ ≤ bottom`.  The two are not interchangeable without a
    --     bridge lemma `IsComplemented ↔ IsComplementedSub` (also unformalized).
    --   • The genuine missing step is the *construction* exhibiting an arbitrary S ⊆ B as a
    --     pullback of the (decidable, hence complemented) diagonal diag A ⊆ A×A along some
    --     classifying map B → A×A.  Freyd builds this in the slice 𝒮(1) and transports along the
    --     slice projection; the slice pre-topos and its complement transport are not in this repo.
    -- Reduces to: (a) IsComplemented↔IsComplementedSub bridge, (b) the diagonal-classifies-S
    -- slice construction. Faithful sorry.
    sorry

/-! ## §1.659 Decidability in functor categories and sheaves

  T ∈ Fᴬ is decidable iff T(x) is a monic map for all x : A → B ∈ A.
  For sheaves: X → Y is decidable iff every pair of points with the same
  stalk have disjoint neighborhoods; in particular, decidable iff Y is Hausdorff.
  (These results require the sheaf/functor-category infrastructure; stated
  with sorry pending that development.) -/

-- §1.659 (note): T ∈ Fᴬ is decidable iff T(x) is a monic map for all x : A → B in A.
-- For sheaves on Y: X → Y is decidable iff stalk-equal points have disjoint neighborhoods
-- (Y Hausdorff → X → Y decidable iff X Hausdorff).
-- Requires functor category and sheaf infrastructure.

/-! ## §1.66 Choice objects in a pre-topos

  We study choice objects [§1.57] in a regular category. -/

section Choice66

variable [RegularCategory 𝒞]

/-- **§1.66**: A subobject of a choice object is choice.
    If C is choice and m: A↣C is monic, then A is choice.
    PROOF: Let R be an entire relation from X to A.
    Then m ≫ R is an entire relation from X to C (composition with a map).
    Because C is choice, m ≫ R contains a map f: X → C.
    Since m is monic, f factors uniquely through A: the factorization gives
    the required map in R. (Requires: entire relations compose with maps.) -/
theorem subobject_of_choice_is_choice {A C : 𝒞} (m : A ⟶ C) (hm : Mono m)
    (hC : Choice C) : Choice A := by
  intro X R hent
  -- Post-compose R : X → A with the monic m to get R' : X → C, same left leg.
  have hp' : MonicPair R.colA (R.colB ≫ m) := by
    intro W f g hA hB
    have hB' : f ≫ R.colB = g ≫ R.colB :=
      hm _ _ (by simpa [Cat.assoc] using hB)
    exact R.isMonicPair f g hA hB'
  let R' : BinRel 𝒞 X C := BinRel.mk R.src R.colA (R.colB ≫ m) hp'
  -- R is entire ⇒ R.colA is a cover ⇒ R' is entire (same left leg).
  have hcov : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  have hent' : Entire R' :=
    (tabulated_is_entire_iff_left_cover R.colA (R.colB ≫ m) hp').mpr hcov
  -- C is choice: R' contains a map; its witness `h : X → R.src` also witnesses
  -- the map `h ≫ R.colB : X → A` inside R.
  obtain ⟨_f, h, hA, _hB⟩ := hC R' hent'
  exact ⟨h ≫ R.colB, h, hA, rfl⟩

/-- **§1.66**: A quotient (cover target) of a choice object is choice.
    If C is choice and x: C↠B is a cover, then B is choice.
    PROOF (book §1.66): x: C → B is also a subobject of C via x° ⊂ 1_C
    (the inclusion via a map contained in x°). Apply subobject_of_choice. -/
theorem quotient_of_choice_is_choice {B C : 𝒞} (x : C ⟶ B) (hx : Cover x)
    (hC : Choice C) : Choice B := by
  intro X R hent
  -- R : X → B entire ⇒ R.colA : R.src → X is a cover.
  have hcovA : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  -- Pull the cover x : C → B back along R.colB : R.src → B.
  -- `has x R.colB` cone: π₁ : pt → C, π₂ : pt → R.src, π₁ ≫ x = π₂ ≫ R.colB.
  let pb := HasPullbacks.has x R.colB
  have hcov_π₂ : Cover pb.cone.π₂ := cover_pullback (f := x) R.colB hx
  have hw : pb.cone.π₁ ≫ x = pb.cone.π₂ ≫ R.colB := pb.cone.w
  -- Build R'' : X → C with src = pb.pt, left leg = π₂ ≫ R.colA (a cover),
  -- right leg = π₁ : pt → C.  Monic pair: left leg cancels the R-data and the
  -- pullback's π₁ is determined by π₂ via the universal property... we instead
  -- check joint-monicity directly.
  have hp'' : MonicPair (pb.cone.π₂ ≫ R.colA) pb.cone.π₁ := by
    intro W f g hA hB
    -- hA : f ≫ (π₂ ≫ R.colA) = g ≫ (π₂ ≫ R.colA),  hB : f ≫ π₁ = g ≫ π₁.
    -- From hB and hw: f ≫ π₂ ≫ R.colB = g ≫ π₂ ≫ R.colB.
    have hB2 : (f ≫ pb.cone.π₂) ≫ R.colB = (g ≫ pb.cone.π₂) ≫ R.colB := by
      have : f ≫ (pb.cone.π₁ ≫ x) = g ≫ (pb.cone.π₁ ≫ x) := by
        rw [← Cat.assoc, ← Cat.assoc, hB]
      rw [hw] at this
      simpa [Cat.assoc] using this
    have hA2 : (f ≫ pb.cone.π₂) ≫ R.colA = (g ≫ pb.cone.π₂) ≫ R.colA := by
      simpa [Cat.assoc] using hA
    -- (π₂'s composites with R.colA, R.colB) agree ⇒ f ≫ π₂ = g ≫ π₂ (R monic pair).
    have hπ₂ : f ≫ pb.cone.π₂ = g ≫ pb.cone.π₂ :=
      R.isMonicPair (f ≫ pb.cone.π₂) (g ≫ pb.cone.π₂) hA2 hB2
    -- Together with hB (agreement on π₁), the pullback's joint monicity (lift_uniq) gives f = g.
    have hw' : (f ≫ pb.cone.π₁) ≫ x = (f ≫ pb.cone.π₂) ≫ R.colB := by
      rw [Cat.assoc, Cat.assoc, hw]
    let c : Cone x R.colB := ⟨W, f ≫ pb.cone.π₁, f ≫ pb.cone.π₂, hw'⟩
    have hf : f = pb.lift c := pb.lift_uniq c f rfl rfl
    have hg : g = pb.lift c := pb.lift_uniq c g hB.symm hπ₂.symm
    rw [hf, hg]
  let R'' : BinRel 𝒞 X C := BinRel.mk pb.cone.pt (pb.cone.π₂ ≫ R.colA) pb.cone.π₁ hp''
  have hent'' : Entire R'' :=
    (tabulated_is_entire_iff_left_cover (pb.cone.π₂ ≫ R.colA) pb.cone.π₁ hp'').mpr
      (cover_comp hcov_π₂ hcovA)
  -- C choice: R'' contains a map with witness h : X → pb.pt.
  obtain ⟨_f, h, hA, _hB⟩ := hC R'' hent''
  -- hA : h ≫ (π₂ ≫ R.colA) = id_X.  The map into B is h ≫ π₁ ≫ x = h ≫ π₂ ≫ R.colB.
  refine ⟨h ≫ pb.cone.π₁ ≫ x, h ≫ pb.cone.π₂, ?_, ?_⟩
  · -- (h ≫ π₂) ≫ R.colA = id_X
    rw [Cat.assoc]; exact hA
  · -- (h ≫ π₂) ≫ R.colB = h ≫ π₁ ≫ x
    calc (h ≫ pb.cone.π₂) ≫ R.colB = h ≫ (pb.cone.π₂ ≫ R.colB) := Cat.assoc _ _ _
      _ = h ≫ (pb.cone.π₁ ≫ x) := by rw [← hw]
      _ = h ≫ pb.cone.π₁ ≫ x := rfl

end Choice66

/-! ## §1.661 Finite products of choice objects are choice

  In a regular category, finite products of choice objects are choice.
  (Proof uses: any entire relation targeted at a terminator is already a map;
  for binary products, decompose R : X → B₁×B₂ via its projections.) -/

section Choice661

variable [RegularCategory 𝒞]

/-- **§1.661**: The terminator is always choice in a regular category.
    PROOF: Any entire relation R : X → 1 is automatically simple, because all maps
    to `one` are equal (terminal uniqueness), so `R° ⊚ R : one → one` trivially lies
    inside `graph id_one`.  Hence R is a map, its left leg R.colA is an iso, and its
    inverse is the required section. -/
theorem terminator_is_choice : Choice (one : 𝒞) := by
  intro A R hent
  -- Terminal uniqueness forces R to be simple.
  have h_simple : Simple R :=
    ⟨⟨(R° ⊚ R).colA,
      by simp [graph, Cat.comp_id],
      by simp [graph]; rw [Cat.comp_id]; exact term_uniq _ _⟩⟩
  -- Entire + Simple = Map, so R.colA is an isomorphism.
  have h_iso : IsIso R.colA :=
    (tabulated_is_map_iff_left_iso R.colA R.colB R.isMonicPair).mp ⟨hent, h_simple⟩
  obtain ⟨inv, _hinv_left, hinv_right⟩ := h_iso
  exact ⟨inv ≫ R.colB, inv, hinv_right, rfl⟩

/-- Helper for §1.661: project an entire relation `R : A → C` through a *map*
    `g : C → D` and extract, from `Choice D`, an actual morphism `f : A → D` that is
    realized inside `R` after `g` — there is a witness `w : A → R.src` with
    `w ≫ R.colA = id_A` and `w ≫ R.colB ≫ g = f`.  This is the constructive,
    sorry-free half of §1.661: the image relation
    `R_g := {(R.colA a, (R.colB ≫ g) a)}` is jointly monic and its left leg is a
    cover (it post-factors the cover `R.colA`), hence entire; choice of `D` hands
    back the factor map together with its section.  (No modular law needed here.) -/
private theorem choice_factor_through_map {A C D : 𝒞}
    (R : BinRel 𝒞 A C) (hent : Entire R) (g : C ⟶ D) (hD : Choice D) :
    ∃ (f : A ⟶ D) (E : BinRel 𝒞 A D) (w : A ⟶ E.src),
      Cover E.colA ∧ w ≫ E.colA = Cat.id A ∧ w ≫ E.colB = f := by
  -- R_g = image of ⟨R.colA, R.colB ≫ g⟩ : R.src → A × D, viewed as a relation A → D.
  let sp : R.src ⟶ prod A D := pair R.colA (R.colB ≫ g)
  let I := image sp
  have hp : MonicPair (I.arr ≫ fst) (I.arr ≫ snd) := by
    intro W u v hA hB
    have hfst : (u ≫ I.arr) ≫ fst = (v ≫ I.arr) ≫ fst := by
      rw [Cat.assoc, Cat.assoc]; exact hA
    have hsnd : (u ≫ I.arr) ≫ snd = (v ≫ I.arr) ≫ snd := by
      rw [Cat.assoc, Cat.assoc]; exact hB
    have : u ≫ I.arr = v ≫ I.arr := by
      rw [pair_eta (u ≫ I.arr), pair_eta (v ≫ I.arr), hfst, hsnd]
    exact I.monic u v this
  let R_g : BinRel 𝒞 A D := BinRel.mk I.dom (I.arr ≫ fst) (I.arr ≫ snd) hp
  -- left leg of R_g is a cover: `image.lift sp ≫ R_g.colA = R.colA` (a cover, R entire).
  have hcovA : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  have hfac : image.lift sp ≫ R_g.colA = R.colA := by
    show image.lift sp ≫ (I.arr ≫ fst) = R.colA
    rw [← Cat.assoc, image.lift_fac]; exact fst_pair _ _
  -- right factor of a cover is a cover.
  have hcov_Rg : Cover R_g.colA := by
    intro K m k hm hk
    refine hcovA m (image.lift sp ≫ k) hm ?_
    rw [Cat.assoc, hk]; exact hfac
  have hent_g : Entire R_g :=
    (tabulated_is_entire_iff_left_cover R_g.colA R_g.colB hp).mpr hcov_Rg
  obtain ⟨f, w, hwA, hwB⟩ := hD R_g hent_g
  exact ⟨f, R_g, w, hcov_Rg, hwA, hwB⟩

/-- A morphism with a section is a cover (split epi ⟹ cover):
    given `s ≫ e = id`, any monic `m` that `e` factors through is split epi
    (via `s ≫ g`), and a monic split epi is an iso. -/
private theorem cover_of_section {X Y : 𝒞} (e : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ e = Cat.id Y) : Cover e := by
  intro C m g hm hgm
  -- m is split epi: (s ≫ g) ≫ m = s ≫ e = id_Y.
  have hsplit : (s ≫ g) ≫ m = Cat.id Y := by rw [Cat.assoc, hgm, hs]
  -- m monic + (s≫g) a section ⟹ m iso.
  refine ⟨s ≫ g, ?_, hsplit⟩
  -- m ≫ (s ≫ g) = id_C : m is monic, and m ≫ (s≫g) ≫ m = m ≫ id by hsplit.
  apply hm
  rw [Cat.assoc, hsplit, Cat.comp_id, Cat.id_comp]

/-- If a composite `c ≫ g` is a cover then its right factor `g` is a cover:
    any monic `m` that `g` factors through, `c ≫ g` also factors through, so
    `c ≫ g` being a cover forces `m` iso. -/
private theorem cover_right_factor {X Y Z : 𝒞} (c : X ⟶ Y) (g : Y ⟶ Z)
    (h : Cover (c ≫ g)) : Cover g := by
  intro D m k hm hkm
  refine h m (c ≫ k) hm ?_
  rw [Cat.assoc, hkm]

/-- A relation composed with the graph of a map stays entire (the totality of
    `R` is preserved by post-composition with a total map `p`).  Used in §1.661 to
    project the entire `R : A → B₁×B₂` through `fst`/`snd` into the choice factors. -/
private theorem entire_comp_graph {A B C : 𝒞} [PullbacksTransferCovers 𝒞]
    (R : BinRel 𝒞 A B) (hent : Entire R) (p : B ⟶ C) : Entire (R ⊚ graph p) := by
  have hRcov : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  let pb := HasPullbacks.has R.colB (Cat.id B)
  let span : pb.cone.pt ⟶ prod A C := pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ p)
  have hfac : image.lift span ≫ (R ⊚ graph p).colA = pb.cone.π₁ ≫ R.colA := by
    show image.lift span ≫ ((image span).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac]; exact fst_pair _ _
  -- pb.π₁ is iso (pullback against id_B), so pb.π₁ ≫ R.colA is a cover.
  have hsq : Cat.id R.src ≫ R.colB = R.colB ≫ Cat.id B := by rw [Cat.id_comp, Cat.comp_id]
  let s : R.src ⟶ pb.cone.pt := pb.lift ⟨R.src, Cat.id R.src, R.colB, hsq⟩
  have hs₁ : s ≫ pb.cone.π₁ = Cat.id R.src := pb.lift_fst _
  have hs₂ : s ≫ pb.cone.π₂ = R.colB := pb.lift_snd _
  have hπ₁s : pb.cone.π₁ ≫ s = Cat.id pb.cone.pt := by
    have e1 : (pb.cone.π₁ ≫ s) ≫ pb.cone.π₁ = pb.cone.π₁ := by rw [Cat.assoc, hs₁, Cat.comp_id]
    have e2 : (pb.cone.π₁ ≫ s) ≫ pb.cone.π₂ = pb.cone.π₂ := by
      rw [Cat.assoc, hs₂]; have hw := pb.cone.w; rw [Cat.comp_id] at hw; exact hw
    have hid₁ : Cat.id pb.cone.pt ≫ pb.cone.π₁ = pb.cone.π₁ := Cat.id_comp _
    have hid₂ : Cat.id pb.cone.pt ≫ pb.cone.π₂ = pb.cone.π₂ := Cat.id_comp _
    let cn : Cone R.colB (Cat.id B) := ⟨pb.cone.pt, pb.cone.π₁, pb.cone.π₂, pb.cone.w⟩
    exact (pb.lift_uniq cn _ e1 e2).trans (pb.lift_uniq cn _ hid₁ hid₂).symm
  have hcov_pre : Cover (pb.cone.π₁ ≫ R.colA) :=
    cover_precomp_iso ⟨s, hπ₁s, hs₁⟩ hRcov
  -- image.lift span ≫ (R⊚graph p).colA is a cover ⟹ (R⊚graph p).colA is a cover.
  have hcomp : Cover (image.lift span ≫ (R ⊚ graph p).colA) := by rw [hfac]; exact hcov_pre
  have : Cover (R ⊚ graph p).colA := cover_right_factor _ _ hcomp
  exact (tabulated_is_entire_iff_left_cover _ _ (R ⊚ graph p).isMonicPair).mpr this

/-- **Pinning lemma**: the relation `graph f ⊚ (graph p)°` (for maps `f : A → C`,
    `p : B → C`) is contained in the "agree at C" relation: its two legs satisfy
    `colA ≫ f = colB ≫ p`.  (Its image-cover `image.lift span` carries the pullback
    square `π₁ ≫ f = π₂ ≫ p`; covers are epic, so the equation descends.) -/
private theorem comp_recip_pin {A B C : 𝒞} (f : A ⟶ C) (p : B ⟶ C) :
    (graph f ⊚ (graph p)°).colA ≫ f = (graph f ⊚ (graph p)°).colB ≫ p := by
  let pb := HasPullbacks.has (graph f).colB ((graph p)°).colA
  let span : pb.cone.pt ⟶ prod A B :=
    pair (pb.cone.π₁ ≫ (graph f).colA) (pb.cone.π₂ ≫ ((graph p)°).colB)
  -- image.lift span ≫ colA = π₁ (since (graph f).colA = id_A), likewise colB = π₂.
  have hA : image.lift span ≫ (graph f ⊚ (graph p)°).colA = pb.cone.π₁ := by
    show image.lift span ≫ ((image span).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac]
    show pair (pb.cone.π₁ ≫ Cat.id A) (pb.cone.π₂ ≫ Cat.id B) ≫ fst = _
    rw [fst_pair]; exact Cat.comp_id _
  have hB : image.lift span ≫ (graph f ⊚ (graph p)°).colB = pb.cone.π₂ := by
    show image.lift span ≫ ((image span).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac]
    show pair (pb.cone.π₁ ≫ Cat.id A) (pb.cone.π₂ ≫ Cat.id B) ≫ snd = _
    rw [snd_pair]; exact Cat.comp_id _
  -- pullback square: π₁ ≫ (graph f).colB = π₂ ≫ (graph p)°.colA, i.e. π₁ ≫ f = π₂ ≫ p.
  have hw : pb.cone.π₁ ≫ f = pb.cone.π₂ ≫ p := pb.cone.w
  -- descend along the cover `image.lift span` (covers are epic).
  apply cover_epi (image_lift_cover span)
  calc image.lift span ≫ ((graph f ⊚ (graph p)°).colA ≫ f)
      = (image.lift span ≫ (graph f ⊚ (graph p)°).colA) ≫ f := (Cat.assoc _ _ _).symm
    _ = pb.cone.π₁ ≫ f := by rw [hA]
    _ = pb.cone.π₂ ≫ p := hw
    _ = (image.lift span ≫ (graph f ⊚ (graph p)°).colB) ≫ p := by rw [hB]
    _ = image.lift span ≫ ((graph f ⊚ (graph p)°).colB ≫ p) := Cat.assoc _ _ _

/-- **§1.563 entire-refinement** (the §1.661 gluing engine): if `f : A → C` is a map with
    `graph f ⊂ R ⊚ graph p` (for `R : A → B` and a morphism `p : B → C`), then the *refined*
    relation `R' := R ⊓ (graph f ⊚ (graph p)°)` is entire.  (Totality is carried by the map
    `f`; `R` itself need not be entire — in §1.661 it is, which is what supplies `hf`.)

    Constructive proof via the intersection-form modular law (`modular_identity`):
    setting `R, S := graph p, T := graph f` and using `graph f ⊂ R⊚graph p`
    (so `(R⊚graph p) ⊓ graph f = graph f`), modularity gives `graph f ⊂ R' ⊚ graph p`.
    The witnessing `RelHom` provides `h : A → (R'⊚graph p).src` with `h ≫ (R'⊚graph p).colA
    = id_A`, i.e. `(R'⊚graph p).colA` is split epi hence a cover; its left leg factors the
    cover `image.lift` of `R'.colA`, so `R'.colA` is a composite of covers, hence a cover —
    which is exactly `Entire R'`. -/
private theorem entire_refine {A B C : 𝒞} [PullbacksTransferCovers 𝒞]
    (R : BinRel 𝒞 A B) (p : B ⟶ C) (f : A ⟶ C)
    (hf : graph f ⊂ R ⊚ graph p) :
    Entire (R ⊓ (graph f ⊚ (graph p)°)) := by
  -- abbreviation: R' := R ⊓ (graph f ⊚ (graph p)°)
  let R' := R ⊓ (graph f ⊚ (graph p)°)
  -- modular_identity with (R, graph p, graph f):
  --   (R ⊚ graph p) ⊓ graph f ⊂ (R ⊓ (graph f ⊚ (graph p)°)) ⊚ graph p = R' ⊚ graph p
  have hmod : ((R ⊚ graph p) ⊓ graph f) ⊂ R' ⊚ graph p :=
    modular_identity R (graph p) (graph f)
  -- graph f ⊂ R ⊚ graph p  ⟹  graph f ⊂ (R ⊚ graph p) ⊓ graph f, so graph f ⊂ R'⊚graph p.
  have hgf : graph f ⊂ R' ⊚ graph p :=
    rel_le_trans (le_intersect hf (rel_le_refl (graph f))) hmod
  -- It suffices to show R'.colA is a cover (Entire ⟺ left leg cover).
  suffices hcov : Cover R'.colA by
    exact (tabulated_is_entire_iff_left_cover R'.colA R'.colB R'.isMonicPair).mpr hcov
  -- The composite R' ⊚ graph p factors R'.colA through a pullback-against-identity:
  --   image.lift span ≫ (R'⊚graph p).colA = pb.π₁ ≫ R'.colA,  pb := pullback(R'.colB, id_B).
  let pb := HasPullbacks.has R'.colB (Cat.id B)
  let span : pb.cone.pt ⟶ prod A C :=
    pair (pb.cone.π₁ ≫ R'.colA) (pb.cone.π₂ ≫ p)
  -- (R'⊚graph p).colA = (image span).arr ≫ fst, definitionally.
  have hcolA_def : (R' ⊚ graph p).colA = (image span).arr ≫ fst := rfl
  -- factorization: image.lift span ≫ (R'⊚graph p).colA = pb.π₁ ≫ R'.colA.
  have hfac : image.lift span ≫ (R' ⊚ graph p).colA = pb.cone.π₁ ≫ R'.colA := by
    rw [hcolA_def, ← Cat.assoc, image.lift_fac]; exact fst_pair _ _
  -- (R'⊚graph p).colA is a cover: graph f ⊂ R'⊚graph p gives a section (graph f has colA = id_A).
  obtain ⟨h, hA, _hB⟩ := hgf
  have hsec : h ≫ (R' ⊚ graph p).colA = Cat.id A := by simpa [graph] using hA
  have hcov_comp : Cover (R' ⊚ graph p).colA := cover_of_section _ h hsec
  -- pb.cone.π₁ is iso (pullback against id_B): section s := pb.lift ⟨_, id, R'.colB, _⟩.
  have hsq : Cat.id R'.src ≫ R'.colB = R'.colB ≫ Cat.id B := by rw [Cat.id_comp, Cat.comp_id]
  let s : R'.src ⟶ pb.cone.pt := pb.lift ⟨R'.src, Cat.id R'.src, R'.colB, hsq⟩
  have hs₁ : s ≫ pb.cone.π₁ = Cat.id R'.src := pb.lift_fst _
  have hs₂ : s ≫ pb.cone.π₂ = R'.colB := pb.lift_snd _
  -- π₁ ≫ s = id_pt: both `π₁ ≫ s` and `id` lift the canonical cone over (R'.colB, id_B).
  have hπ₁s : pb.cone.π₁ ≫ s = Cat.id pb.cone.pt := by
    have e1 : (pb.cone.π₁ ≫ s) ≫ pb.cone.π₁ = pb.cone.π₁ := by rw [Cat.assoc, hs₁, Cat.comp_id]
    have e2 : (pb.cone.π₁ ≫ s) ≫ pb.cone.π₂ = pb.cone.π₂ := by
      rw [Cat.assoc, hs₂]; have hw := pb.cone.w; rw [Cat.comp_id] at hw; exact hw
    have hid₁ : Cat.id pb.cone.pt ≫ pb.cone.π₁ = pb.cone.π₁ := Cat.id_comp _
    have hid₂ : Cat.id pb.cone.pt ≫ pb.cone.π₂ = pb.cone.π₂ := Cat.id_comp _
    let cn : Cone R'.colB (Cat.id B) := ⟨pb.cone.pt, pb.cone.π₁, pb.cone.π₂, pb.cone.w⟩
    exact (pb.lift_uniq cn _ e1 e2).trans (pb.lift_uniq cn _ hid₁ hid₂).symm
  have hπ₁_iso : IsIso pb.cone.π₁ := ⟨s, hπ₁s, hs₁⟩
  -- pb.π₁ ≫ R'.colA is a cover (image.lift cover ≫ (R'⊚graph p).colA cover, via hfac).
  have hcov_pre : Cover (pb.cone.π₁ ≫ R'.colA) := by
    rw [← hfac]; exact cover_comp (image_lift_cover span) hcov_comp
  -- R'.colA = s ≫ (π₁ ≫ R'.colA), a cover precomposed by the iso s ⟹ cover.
  have hR'colA : s ≫ (pb.cone.π₁ ≫ R'.colA) = R'.colA := by
    rw [← Cat.assoc, hs₁, Cat.id_comp]
  have hfin : Cover (s ≫ (pb.cone.π₁ ≫ R'.colA)) :=
    cover_precomp_iso ⟨pb.cone.π₁, hs₁, hπ₁s⟩ hcov_pre
  rwa [hR'colA] at hfin

/-- **§1.661**: The binary product of two choice objects is choice.
    PROOF (book §1.661): Let R be entire from A to B₁×B₂.
    R∘fst° is entire targeted at B₁, so it contains a map f₁ (`entire_comp_graph` +
    `Choice B₁`).  The *refined* relation R' := R ∩ (f₁∘fst°) is again entire — this is
    the §1.563 intersection-modular content, discharged here sorry-free by `entire_refine`
    (built on `modular_identity`).  R' pins the B₁-coordinate to f₁ (`comp_recip_pin`),
    so ⟨R'.colA, R'.colB ≫ snd⟩ is jointly monic; its left leg is the cover R'.colA, hence
    the B₂-valued relation R'₂ is entire and `Choice B₂` extracts f₂ *together with a single
    witness `w : A → R'.src`*.  By the pinning, w ≫ R'.colB = pair f₁ f₂, and R' ⊂ R carries
    w into R.src — giving the map ⟨f₁,f₂⟩ ⊂ R.  Fully constructive on `modular_identity`. -/
theorem prod_choice_is_choice [PullbacksTransferCovers 𝒞] {B₁ B₂ : 𝒞}
    (h₁ : Choice B₁) (h₂ : Choice B₂) : Choice (prod B₁ B₂) := by
  intro A R hent
  -- (1) f₁ : A → B₁ contained in R ⊚ graph fst  (R⊚fst° entire, B₁ choice).
  have hent_fst : Entire (R ⊚ graph (fst : prod B₁ B₂ ⟶ B₁)) := entire_comp_graph R hent fst
  obtain ⟨f₁, h₁w, h₁A, h₁B⟩ := h₁ (R ⊚ graph fst) hent_fst
  have hgf₁ : graph f₁ ⊂ R ⊚ graph fst := ⟨⟨h₁w, by simpa [graph] using h₁A, h₁B⟩⟩
  -- (2) the refined relation R' := R ⊓ (graph f₁ ⊚ (graph fst)°), entire by `entire_refine`.
  let R' : BinRel 𝒞 A (prod B₁ B₂) := R ⊓ (graph f₁ ⊚ (graph fst)°)
  have hentR' : Entire R' := entire_refine R fst f₁ hgf₁
  -- (3) pinning: every R'-point has fst-coordinate = f₁ of its A-coordinate.
  obtain ⟨z, hzA, hzB⟩ := intersect_le_right R (graph f₁ ⊚ (graph fst)°)
  have hpin : R'.colB ≫ fst = R'.colA ≫ f₁ := by
    have hbase := comp_recip_pin f₁ (fst : prod B₁ B₂ ⟶ B₁)
    -- transport along z : R'.src → (graph f₁ ⊚ (graph fst)°).src.
    calc R'.colB ≫ fst = (z ≫ (graph f₁ ⊚ (graph fst)°).colB) ≫ fst := by rw [hzB]
      _ = z ≫ ((graph f₁ ⊚ (graph fst)°).colB ≫ fst) := Cat.assoc _ _ _
      _ = z ≫ ((graph f₁ ⊚ (graph fst)°).colA ≫ f₁) := by rw [hbase]
      _ = (z ≫ (graph f₁ ⊚ (graph fst)°).colA) ≫ f₁ := (Cat.assoc _ _ _).symm
      _ = R'.colA ≫ f₁ := by rw [hzA]
  -- (4) R'₂ : A → B₂ with source R'.src, legs (R'.colA, R'.colB ≫ snd) — jointly monic
  --     thanks to the pinning, left leg R'.colA a cover (R' entire) ⟹ R'₂ entire.
  have hR'cov : Cover R'.colA :=
    (tabulated_is_entire_iff_left_cover R'.colA R'.colB R'.isMonicPair).mp hentR'
  have hp₂ : MonicPair R'.colA (R'.colB ≫ snd) := by
    intro W u v hua hub
    -- hua : u ≫ R'.colA = v ≫ R'.colA,  hub : u ≫ (R'.colB ≫ snd) = v ≫ (R'.colB ≫ snd).
    -- fst-coordinates agree by pinning; together with snd, R'.colB-coords agree ⟹ R'.isMonicPair.
    have hfst : (u ≫ R'.colB) ≫ fst = (v ≫ R'.colB) ≫ fst := by
      calc (u ≫ R'.colB) ≫ fst = u ≫ (R'.colB ≫ fst) := Cat.assoc _ _ _
        _ = u ≫ (R'.colA ≫ f₁) := by rw [hpin]
        _ = (u ≫ R'.colA) ≫ f₁ := (Cat.assoc _ _ _).symm
        _ = (v ≫ R'.colA) ≫ f₁ := by rw [hua]
        _ = v ≫ (R'.colA ≫ f₁) := Cat.assoc _ _ _
        _ = v ≫ (R'.colB ≫ fst) := by rw [hpin]
        _ = (v ≫ R'.colB) ≫ fst := (Cat.assoc _ _ _).symm
    have hsnd : (u ≫ R'.colB) ≫ snd = (v ≫ R'.colB) ≫ snd := by
      rw [Cat.assoc, Cat.assoc]; exact hub
    have hcolB : u ≫ R'.colB = v ≫ R'.colB := by
      rw [pair_eta (u ≫ R'.colB), pair_eta (v ≫ R'.colB), hfst, hsnd]
    exact R'.isMonicPair u v hua hcolB
  let R'₂ : BinRel 𝒞 A B₂ := BinRel.mk R'.src R'.colA (R'.colB ≫ snd) hp₂
  have hentR'₂ : Entire R'₂ :=
    (tabulated_is_entire_iff_left_cover R'.colA (R'.colB ≫ snd) hp₂).mpr hR'cov
  -- (5) Choice B₂ extracts f₂ with a single witness w : A → R'.src.
  obtain ⟨f₂, w, hwA, hwB⟩ := h₂ R'₂ hentR'₂
  -- hwA : w ≫ R'.colA = id_A,  hwB : w ≫ (R'.colB ≫ snd) = f₂.
  -- (6) w ≫ R'.colB = pair f₁ f₂  (snd by hwB, fst by pinning + hwA).
  have hwBfull : w ≫ R'.colB = pair f₁ f₂ := by
    rw [pair_eta (w ≫ R'.colB)]
    congr 1
    · -- w ≫ R'.colB ≫ fst = w ≫ R'.colA ≫ f₁ = f₁.
      calc (w ≫ R'.colB) ≫ fst = w ≫ (R'.colB ≫ fst) := Cat.assoc _ _ _
        _ = w ≫ (R'.colA ≫ f₁) := by rw [hpin]
        _ = (w ≫ R'.colA) ≫ f₁ := (Cat.assoc _ _ _).symm
        _ = f₁ := by rw [hwA, Cat.id_comp]
    · calc (w ≫ R'.colB) ≫ snd = w ≫ (R'.colB ≫ snd) := Cat.assoc _ _ _
        _ = f₂ := hwB
  -- (7) transport the witness into R.src via R' ⊂ R, giving ⟨f₁,f₂⟩ ⊂ R.
  obtain ⟨k, hkA, hkB⟩ := intersect_le_left R (graph f₁ ⊚ (graph fst)°)
  refine ⟨pair f₁ f₂, w ≫ k, ?_, ?_⟩
  · calc (w ≫ k) ≫ R.colA = w ≫ (k ≫ R.colA) := Cat.assoc _ _ _
      _ = w ≫ R'.colA := by rw [hkA]
      _ = Cat.id A := hwA
  · calc (w ≫ k) ≫ R.colB = w ≫ (k ≫ R.colB) := Cat.assoc _ _ _
      _ = w ≫ R'.colB := by rw [hkB]
      _ = pair f₁ f₂ := hwBfull

end Choice661

/-! ## §1.662 Diaconescu's theorem in a pre-topos

  In a pre-topos, the following are equivalent:
  (1) Binary coproducts of choice objects are choice.
  (2) 1+1 is choice.
  (3) The pre-topos is boolean. -/

section Diaconescu

variable [PreTopos 𝒞] [HasBinaryCoproducts 𝒞]

/-- **§1.662**: (1) → (2): trivially, 1+1 is a coproduct of 1 and 1, and 1 is choice. -/
theorem coprod_choice_to_one_one_choice
    (h : ∀ (B₁ B₂ : 𝒞), Choice B₁ → Choice B₂ →
         Choice (HasBinaryCoproducts.coprod B₁ B₂)) :
    Choice (HasBinaryCoproducts.coprod (one : 𝒞) one) :=
  h one one terminator_is_choice terminator_is_choice

/-- **§1.662**: (2) → (3): 1+1 choice implies boolean.
    PROOF: The intermediate condition (2a) — every cover X∪Y=B can be
    refined to a partition X'⊆X, Y'⊆Y with X'∪Y'=B and X'∩Y'=∅ —
    is a restatement of (2) because maps B → 1+1 are partitions of B.
    (2a) is inherited by slices, so it suffices to show 𝒮(1) is boolean.
    Any U ⊆ 1 gives a pushout P = 1 +_U 1; 1+1 choice ⟹ P is a subobject
    of 1+1; 1+1 is decidable (§1.658) and so is P; U is complemented as a
    pullback of a complemented subobject.

    BLOCKER: the chain needs (a) the slice pre-topos 𝒮(1)=𝒞 inheriting condition
    (2a), (b) the pushout P = 1 +_U 1 — now a real construction via `amalgamation_lemma`
    (§1.651), whose residual is only the leg-monicity descent, (c) "pullback of a
    complemented subobject is complemented" (§1.658 complement intersection/union infra,
    not yet formalized — IsComplemented uses a placeholder intersection).  The §1.62
    disjointness lemmas (`coprod_inl_inr_disjoint_elt`, `inl_union_inr_entire`) supply the
    "maps B→1+1 are disjoint-complemented partitions" content for (2a), but the slice
    transport (a) and complement pullback-stability (c) remain genuinely absent.  Faithful
    statement; reduces to amalgamation_lemma + complement pullback-stability. -/
theorem one_one_choice_to_boolean [HasBinaryProducts 𝒞]
    (h : Choice (HasBinaryCoproducts.coprod (one : 𝒞) one)) :
    Nonempty (BooleanPreLogos 𝒞) := by
  sorry

/-- **§1.662**: (3) → (1): boolean implies binary coproducts of choice objects are choice.
    PROOF: Given S: A → B₁+B₂ entire, the subobject Dom(S∘inl°) ⊆ A is complemented
    (boolean pre-topos). The restriction of S to Dom(S∘inl°) is entire into B₁, so
    contains f₁ (B₁ choice). The restriction to the complement is entire into B₂,
    so contains f₂ (B₂ choice). Then f₁+f₂ (copairing) is a map in S.

    BLOCKER (genuine residual): "Dom(S∘inl°) ⊆ A is complemented" and "the restriction of S
    to that (complemented) subobject is entire into B₁" require a relation domain/restriction
    operator (`Dom`, not yet defined in this repo) and the §1.658 complement infrastructure
    (`IsComplemented` currently a placeholder; complement pullback-stability absent).  The
    §1.563 modular gluing is now AVAILABLE (`modular_identity` proven; cf. the sorry-free
    `entire_refine`/`prod_choice_is_choice` above), so the only remaining gap is the §1.658
    complement layer + the relation-domain operator.  Faithful statement; reduces to those. -/
theorem boolean_to_coprod_choice_is_choice [HasBinaryProducts 𝒞]
    (hbool : Nonempty (BooleanPreLogos 𝒞)) :
    ∀ (B₁ B₂ : 𝒞), Choice B₁ → Choice B₂ →
      Choice (HasBinaryCoproducts.coprod B₁ B₂) := by
  sorry

end Diaconescu

end Freyd
