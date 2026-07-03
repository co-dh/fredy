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
import Fredy.S1_47
import Fredy.S1_62
import Fredy.S1_77
import Fredy.S1_658_Complement


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.63 Slice of a (positive) pre-logos is a (positive) pre-logos

  Freyd §1.63: for any pre-logos A and object B, the slice A/B is again a
  pre-logos, and Σ : A/B → A is an iso on subobject lattices.  The two
  italic propositions at §1.63 are:

  (1) "If A is a (positive) pre-logos then so is A/B."
  (2) "Any (positive) pre-logos is faithfully representable in a capital
      (positive) pre-logos."

  Both are proven downstream.  The slice infrastructure:
  - `PreRegularCategory (Over B)` — `SliceRegular.lean`
  - `HasImages (Over B)`, `HasSubobjectUnions (Over B)` — `SlicePreTopos.lean`
  - `overPreLogos (B : 𝒞) : PreLogos (Over B)` — `SlicePreTopos.lean` §643–752
  - `overPositivePreLogos (B : 𝒞) : PositivePreLogos (Over B)` — `SlicePreTopos.lean` §754

  `S1_64` cannot import `SlicePreTopos` because `SlicePreTopos` imports `S1_64`. -/

-- BOOK §1.63 (1): If A is a (positive) pre-logos then so is A/B.
-- ✅ DONE: `overPreLogos` and `overPositivePreLogos` in `Fredy.SlicePreTopos`.

-- BOOK §1.63 (2): Any (positive) pre-logos is faithfully representable in a capital
-- (positive) pre-logos.
-- ✅ DONE: §1.543 capitalization lemma + `overPreLogos`/`overPositivePreLogos`
-- from `Fredy.SlicePreTopos`.  Recorded as a downstream corollary there.

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

/-- **Bridge** (§1.631 ⇔ §1.62): the meet-universal form `IsComplemented` (this file) and the
    inter-based form `IsComplementedSub` (`S1_62`, consumed by `Complement.lean`) agree.
    Same witness `A₂`; the union clauses are literally identical, and the two disjointness
    clauses are equivalent because `Subobject.inter A₁ A₂` is the meet (greatest common lower
    bound): `inter A₁ A₂ ≤ ⊥` iff every common lower bound `S` of `A₁`, `A₂` is `≤ ⊥`. -/
theorem isComplemented_iff_sub [PreLogos 𝒞] {A : 𝒞} (A₁ : Subobject 𝒞 A) :
    IsComplemented A₁ ↔ IsComplementedSub A₁ := by
  constructor
  · rintro ⟨A₂, hdisj, hcover⟩
    refine ⟨A₂, ?_, hcover⟩
    -- inter A₁ A₂ is a common lower bound of A₁, A₂, so the universal clause sends it to ⊥.
    exact hdisj (Subobject.inter A₁ A₂)
      (Subobject.inter_le_left A₁ A₂) (Subobject.inter_le_right A₁ A₂)
  · rintro ⟨A₂, hdisj, hcover⟩
    refine ⟨A₂, ?_, hcover⟩
    -- any common lower bound S factors through the meet inter A₁ A₂, which is ≤ ⊥.
    intro S h1 h2
    exact Subobject.le_trans (Subobject.le_inter h1 h2) hdisj

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

/-! ## §1.637 Special pre-logos and characterization

  A pre-logos is SPECIAL if it satisfies every universal sentence in the
  predicates of pre-logoi satisfied by the category of sets.
  The book gives an elementary internal characterization at §1.637 and
  studies S^A and LH(Y) at §1.638. -/

/-! A pre-logos is SPECIAL if for every pair of proper subobjects A'⊂A, B'⊂B,
    the subobject (A'×B)∪(A×B') is proper in A×B.
    §1.637: this is the elementary internal characterization of special pre-logoi. -/

/-- Symmetric counterpart of `product_mono_of_mono` (S1_47): `mB : B' → B` monic implies
    `pair fst (snd ≫ mB) : A×B' → A×B` is monic.
    Proof: if `u ≫ pair fst (snd ≫ mB) = v ≫ pair fst (snd ≫ mB)`, post-composing with `fst`
    gives `u ≫ fst = v ≫ fst`; post-composing with `snd` then using `mB` monic gives
    `u ≫ snd = v ≫ snd`; then `fst_snd_jointly_monic` closes the goal. -/
theorem product_mono_of_mono_right [HasBinaryProducts 𝒞] (A : 𝒞) {B' B : 𝒞} (mB : B' ⟶ B)
    (hmB : Monic mB) : Monic (pair (fst (A := A) (B := B')) (snd (A := A) (B := B') ≫ mB)) := by
  intro W u v huv
  have h1 : u ≫ fst = v ≫ fst := by
    have := congrArg (· ≫ fst) huv; simpa only [Cat.assoc, fst_pair] using this
  have h2 : u ≫ snd = v ≫ snd := by
    have h : (u ≫ snd) ≫ mB = (v ≫ snd) ≫ mB := by
      have := congrArg (· ≫ snd) huv; simpa only [Cat.assoc, snd_pair] using this
    exact hmB _ _ h
  exact fst_snd_jointly_monic u v h1 h2

/-- **§1.637 characterization of SPECIAL pre-logos** (internal form).
    A positive pre-logos is SPECIAL iff for every pair of proper subobjects
    `mA : A' ↪ A`, `mB : B' ↪ B`, the join subobject `(A'×B) ∪ (A×B')` in `A×B`
    is PROPER (not an isomorphism on its `.arr`).

    Here `(A'×B)` is the subobject with arrow `pair (fst ≫ mA) snd : A'×B → A×B`
    (monic by `product_mono_of_mono`) and `(A×B')` is the subobject with arrow
    `pair fst (snd ≫ mB) : A×B' → A×B` (monic by `product_mono_of_mono_right`).
    Their join is `HasSubobjectUnions.union S1 S2 : Subobject 𝒞 (prod A B)`.

    The EASY direction `IsSpecialPreLogos → ProperMono` is proven below as
    `isSpecialPreLogos_implies_properMono`.
    The HARD direction `IsSpecial ∧ PositivePreLogos → IsSpecialPreLogos` requires the
    ultra-filter diagonal representation argument (§1.646); left as a TODO comment. -/
class IsSpecialPreLogos (𝒞 : Type u) [Cat.{v} 𝒞] [PreLogos 𝒞] : Prop where
  special : ∀ {A' A B' B : 𝒞} (mA : A' ⟶ A) (mB : B' ⟶ B)
      (hmA : ProperMono mA) (hmB : ProperMono mB),
    ¬ (HasSubobjectUnions.union
        ⟨prod A' B, pair (fst ≫ mA) snd, product_mono_of_mono B mA hmA.1⟩
        ⟨prod A B', pair fst (snd ≫ mB), product_mono_of_mono_right A mB hmB.1⟩
      ).IsEntire

/-- **§1.637 easy direction**: if `IsSpecialPreLogos 𝒞` and `mA : A' → A`, `mB : B' → B`
    are proper monos, then `pair (fst ≫ mA) snd : A'×B → A×B` is a proper mono.
    Monic: by `product_mono_of_mono`.  Non-iso: if iso, then `S1 = A'×B ↪ A×B` is
    entire; `union_left` gives `entire ≤ S1∪S2`, so `entire_of_entire_le` makes
    `S1∪S2` entire, contradicting `IsSpecialPreLogos.special`. -/
theorem isSpecialPreLogos_implies_properMono [PreLogos 𝒞]
    (h : IsSpecialPreLogos 𝒞) {A' A B' B : 𝒞}
    {mA : A' ⟶ A} {mB : B' ⟶ B} (hmA : ProperMono mA) (hmB : ProperMono mB) :
    ProperMono (pair (fst (A := A') (B := B) ≫ mA) (snd (A := A') (B := B))) := by
  refine ⟨product_mono_of_mono B mA hmA.1, ?_⟩
  -- Goal: ¬ IsIso (pair (fst ≫ mA) snd)
  intro hiso
  let S1 : Subobject 𝒞 (prod A B) :=
    ⟨prod A' B, pair (fst ≫ mA) snd, product_mono_of_mono B mA hmA.1⟩
  let S2 : Subobject 𝒞 (prod A B) :=
    ⟨prod A B', pair fst (snd ≫ mB), product_mono_of_mono_right A mB hmB.1⟩
  obtain ⟨g, _, hg2⟩ := hiso
  -- g ≫ S1.arr = Cat.id (prod A B), so entire ≤ S1; S1 ≤ S1∪S2 gives entire ≤ S1∪S2
  have hentire_le_S1 : (Subobject.entire (prod A B)).le S1 := by
    exact ⟨g, hg2⟩
  exact h.special mA mB hmA hmB
    (entire_of_entire_le (Subobject.le_trans hentire_le_S1 (HasSubobjectUnions.union_left S1 S2)))

-- BOOK §1.637 hard direction (TODO): IsSpecial ∧ PositivePreLogos → IsSpecialPreLogos.
-- Proof sketch: if (A'×B)∪(A×B') were entire, the diagonal homRep T would give
-- T(A'×B) ∪ T(A×B') = T(A×B) in Set.  But A'×B ∪ A×B' ≠ A×B for proper A', B' in Set
-- (take any (a,b) ∉ A'×B ∪ A×B'), so T sends the union to a proper subobject — contradicting
-- entireness.  Making this precise requires the ultra-filter diagonal representation
-- from `finite_separation` (FiniteSeparation.lean, §1.646).

-- BOOK §1.642: For A a small category, S^A is a boolean pre-logos iff A is a groupoid.
-- TODO: needs Set-valued functor category (S^A) infrastructure not in this repo.

/-! ## §1.646 Faithful representability of small special categories

  Every small special Cartesian category is faithfully representable in Set.
  Every small special positive pre-logos is faithfully representable in Set.
  PROOF (§1.646): Combine §1.472/§1.637 (finite separation) with a diagonal
  ultra-filter argument: I = finite sets of proper subobjects, choose T_S for
  each S, form T : A → Set^I, extend to an ultra-filter F ⊇ principal coideals.
  T^F is faithful.  (Requires ultra-filter machinery; Sorry.) -/

-- §1.646 (note): Every small special Cartesian category embeds faithfully in Set.
-- Proof combines §1.472/§1.637 with an ultra-filter diagonal argument.
-- Requires ultra-filter infrastructure outside this repo's scope.

-- §1.646 (note): Every small special positive pre-logos embeds faithfully in Set.
-- Same proof as above, additionally using that T_F̂ preserves disjoint unions
-- (§1.634, for an ultra-filter F̂).  Requires ultra-filter infrastructure.

-- §1.647 (note): A boolean pre-logos is special iff two-valued.
-- Proof: complement of (A₁×B)∪(A×B₂) in A×B is A₁'×B₂' (§1.647 formula);
-- two-valued iff every subobject lattice is {0,1} (degenerate or two-element boolean alg).
-- TODO: needs `complement_product_union` lemma (complement arithmetic in BooleanPreLogos).

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
theorem graphComp_le_kernelPairRel [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
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
theorem kernelPairRel_le_graphComp [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
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
    have h2 : RelLe (E°°) (E°) := reciprocal_mono hSym
    rwa [reciprocal_invol] at h2

/-- Reverse bridge: §1.567 `EquivalenceRelation` ⟹ §1.775 `IsEquivRel`. -/
theorem isEquivRel_of_equivalenceRelation {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} {E : BinRel 𝒞 A A} (h : EquivalenceRelation E) : IsEquivRel E := by
  obtain ⟨⟨hsec, hsA, hsB⟩, ⟨hsym⟩, htrans⟩ := h
  refine ⟨?_, ?_, htrans⟩
  · exact ⟨⟨hsec, by simpa [graph] using hsA, by simpa [graph] using hsB⟩⟩
  · -- field gives E ⊑ E°; reciprocate to E° ⊑ E.
    have h2 : RelLe (E°) (E°°) := reciprocal_mono ⟨hsym⟩
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
    [HasSubobjectUnions 𝒞] [HasReflTransClosure 𝒞] :
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
      reciprocal_mono graph_id_le_reciprocal
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

  The leg-monicity `Monic (inl ≫ q)` reduces to a relation containment
  `graph inl ⊚ E ⊚ (graph inl)° ⊂ 1_B`.  Distributing `E ⊂ F = 1 ∪ R₀ ∪ R₀°`
  (minimality of `E`), the cross terms `R₀, R₀°` vanish because `R₀` only relates
  `inl(B)` to `inr(C)`: composing them against `graph inl` hits the disjoint
  intersection `inl ∩ inr = 0` (§1.62 positivity), so the composite relation's
  tabulation sits below the bottom subobject — hence below *every* relation, in
  particular the diagonal.  The diagonal term `graph inl ⊚ 1 ⊚ (graph inl)° =
  graph inl ⊚ (graph inl)°` is `⊂ 1_B` since `inl` is monic. -/

/-- `f : A → B` is monic if its level (kernel pair) lies inside the diagonal. -/
theorem mono_of_kernelPairRel_le_diag [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (h : RelLe (kernelPairRel f) (graph (Cat.id A))) : Monic f := by
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
  relLe_of_subLe (Subobject.le_trans h (PreLogos.bottom_min (relSub U)))

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
  have := reciprocal_mono hrec
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
    {Bj M D : 𝒞} (j : Bj ⟶ M) (hj : Monic j) (q : M ⟶ D)
    (R₀ : BinRel 𝒞 M M)
    (hLELE : RelLe (kernelPairRel (j ≫ q)) (graph j ⊚ ((graph q ⊚ (graph q)°) ⊚ (graph j)°)))
    (hLEF : RelLe (graph q ⊚ (graph q)°) ((graph (Cat.id M) ∪ᵣ R₀) ∪ᵣ R₀°))
    (hc1 : RelLe (graph j ⊚ (R₀ ⊚ (graph j)°)) (graph (Cat.id Bj)))
    (hc2 : RelLe (graph j ⊚ (R₀° ⊚ (graph j)°)) (graph (Cat.id Bj))) :
    Monic (j ≫ q) := by
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
    (s : Bj ⟶ M) (t : Bj ⟶ N) (ht : Monic t) :
    RelLe (((graph s)° ⊚ graph t) ⊚ ((graph s)° ⊚ graph t)°) (graph (Cat.id M)) := by
  -- Book (maps as relations via `↑`):  PP° = (s°t)(s°t)° = (s°t)(t°s) ⊆ s°(tt°)s
  --   ⊆ s°·1·s = s°s ⊆ 1, the bracket using t monic (tt° ⊆ 1).
  let sr : BinRel 𝒞 Bj M := s          -- ↑s
  let tr : BinRel 𝒞 Bj N := t          -- ↑t
  let P := sr° ⊚ tr
  have hP : RelLe (P°) (tr° ⊚ sr) := by
    have h := reciprocal_comp_le (sr°) tr
    rw [reciprocal_invol] at h; exact h
  -- inner bracket  t(t°s) ⊆ (tt°)s ⊆ 1·s = s, using t monic.
  have htts : RelLe (tr ⊚ (tr° ⊚ sr)) sr :=
    rel_le_trans (compose_assoc_of_regular tr (tr°) sr).2
      (rel_le_trans (compose_le (graph_comp_recip_le_one_of_mono t ht) (rel_le_refl _))
        (graph_id_comp sr))
  calc P ⊚ P°
      ⊂ P ⊚ (tr° ⊚ sr) := compose_le (rel_le_refl _) hP
    _ ⊂ sr° ⊚ (tr ⊚ (tr° ⊚ sr)) := (compose_assoc_of_regular (sr°) tr (tr° ⊚ sr)).1
    _ ⊂ sr° ⊚ sr := compose_le (rel_le_refl _) htts
    _ ⊂ graph (Cat.id M) := reciprocal_comp_self_le_one s

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
        have h := reciprocal_mono (graph_id_le_reciprocal (A := M))
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

/-- A *point* of a composite relation `R ⊚ S`: given matching span legs `w₁ : T → R.src`,
    `w₂ : T → S.src` whose middle columns agree (`w₁ ≫ R.colB = w₂ ≫ S.colA`), the pair
    `(w₁≫R.colA, w₂≫S.colB)` is allowed by `relSub (R ⊚ S)`.  This is the introduction rule
    for composite relations used in the §1.651 pullback read-off (dual to the elimination
    `compose_le`): it threads a `d.pt`-point through the composition pullback + image. -/
private theorem compose_point_allows [PreLogos 𝒞] [HasBinaryCoproducts 𝒞]
    {A B C : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C)
    {T : 𝒞} (w₁ : T ⟶ R.src) (w₂ : T ⟶ S.src)
    (hmid : w₁ ≫ R.colB = w₂ ≫ S.colA) :
    Allows (relSub (R ⊚ S)) (pair (w₁ ≫ R.colA) (w₂ ≫ S.colB)) := by
  let pb := HasPullbacks.has R.colB S.colA
  let span : pb.cone.pt ⟶ prod A C :=
    pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)
  let t : T ⟶ pb.cone.pt := pb.lift ⟨T, w₁, w₂, hmid⟩
  have ht₁ : t ≫ pb.cone.π₁ = w₁ := pb.lift_fst _
  have ht₂ : t ≫ pb.cone.π₂ = w₂ := pb.lift_snd _
  have harr : (relSub (R ⊚ S)).arr = (image span).arr := by
    show pair (R ⊚ S).colA (R ⊚ S).colB = (image span).arr
    exact (pair_uniq (R ⊚ S).colA (R ⊚ S).colB (image span).arr rfl rfl).symm
  refine ⟨t ≫ image.lift span, ?_⟩
  rw [harr, Cat.assoc, image.lift_fac]
  exact pair_uniq (w₁ ≫ R.colA) (w₂ ≫ S.colB) (t ≫ span)
    (by show (t ≫ pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)) ≫ fst = _
        rw [Cat.assoc, fst_pair, ← Cat.assoc, ht₁])
    (by show (t ≫ pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)) ≫ snd = _
        rw [Cat.assoc, snd_pair, ← Cat.assoc, ht₂])

/-- `(graph m)° ⊚ graph n ≤ ⟨A, m, n⟩`: the reciprocal composite, whose composition
    pullback is the trivial diagonal `A` (both middle columns are `id_A`), factors through the
    span relation `(m, n)` (a monic pair when `n` is monic).  This is the read-off lemma that
    turns a point of `(graph m)° ⊚ graph n` into a genuine pullback factor through `A`. -/
private theorem recipGraph_comp_graph_le_span [PreLogos 𝒞] [HasBinaryCoproducts 𝒞]
    {A B C : 𝒞} (m : A ⟶ B) (n : A ⟶ C) (hn : Monic n) :
    RelLe ((graph m)° ⊚ graph n)
      (⟨A, m, n, monicPair_of_monic_pair m n (monic_pair_of_monic m n hn)⟩ : BinRel 𝒞 B C) := by
  let pb := HasPullbacks.has ((graph m)°).colB ((graph n).colA)
  let span : pb.cone.pt ⟶ prod B C :=
    pair (pb.cone.π₁ ≫ ((graph m)°).colA) (pb.cone.π₂ ≫ (graph n).colB)
  have h_simp : pb.cone.π₁ = pb.cone.π₂ := by
    have h := pb.cone.w; show pb.cone.π₁ = pb.cone.π₂
    simpa [reciprocal, graph, Cat.comp_id] using h
  let I := image span
  let S : Subobject 𝒞 (prod B C) := ⟨A, pair m n, monic_pair_of_monic m n hn⟩
  have h_span_eq : span = pb.cone.π₁ ≫ pair m n := by
    show pair (pb.cone.π₁ ≫ m) (pb.cone.π₂ ≫ n) = pb.cone.π₁ ≫ pair m n
    refine (pair_uniq _ _ _ ?_ ?_).symm
    · rw [Cat.assoc, fst_pair]
    · rw [Cat.assoc, snd_pair, h_simp]
  obtain ⟨k, hk⟩ := image_min span S ⟨pb.cone.π₁, h_span_eq.symm⟩
  refine ⟨⟨k, ?_, ?_⟩⟩
  · show k ≫ m = I.arr ≫ fst
    calc k ≫ m = (k ≫ pair m n) ≫ fst := by rw [Cat.assoc, fst_pair]
      _ = I.arr ≫ fst := by rw [hk]
  · show k ≫ n = I.arr ≫ snd
    calc k ≫ n = (k ≫ pair m n) ≫ snd := by rw [Cat.assoc, snd_pair]
      _ = I.arr ≫ snd := by rw [hk]

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
    discharged Sorry-free: `R₀ ⊑ E ⊑ level q`, and `R₀`'s two columns are exactly `x≫inl`,
    `y≫inr`, so they agree after `q`.

    CLOSED (axioms `propext, Classical.choice`).  Leg-monicity `Monic u`, `Monic v` — the former
    residual — was proved via a zigzag/path-length induction over the transitive-closure structure
    of `E` using `relPow` path length (disjointness `inl_inter_inr_le_bottom` /
    `coprod_inl_inr_disjoint_elt` + `inl/inr_mono` + the path-length descent in
    `level_minEquiv_restrict_diagonal`).  The object `D`, the maps `u, v`, and the commuting
    square are routed through Freyd's generated-equivalence-relation construction. -/
theorem amalgamation_lemma [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]
    {A B C : 𝒞}
    (x : A ⟶ B) (hx : Monic x) (y : A ⟶ C) (hy : Monic y) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D), Monic u ∧ Monic v ∧ x ≫ u = y ≫ v := by
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
  have hxi : Monic xi := by
    intro W f g h
    apply hx; apply inl_mono (A := B) (B := C)
    show (f ≫ x) ≫ HasBinaryCoproducts.inl = (g ≫ x) ≫ HasBinaryCoproducts.inl
    simpa [xi, Cat.assoc] using h
  have hyi : Monic yi := by
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
    rel_le_trans (compose_le hR₀P (reciprocal_mono hR₀P))
      (comp_recip_self_le_diag xi yi hyi)
  have hRopR : RelLe (R₀° ⊚ R₀) (graph (Cat.id (HasBinaryCoproducts.coprod B C))) :=
    rel_le_trans (compose_le (reciprocal_mono hR₀P) hR₀P) (diag_le_one xi yi hxi)
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
      rel_le_trans (reciprocal_mono s1) (reciprocal_comp_le (graph j) (graph q))
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
  · -- Monic u = Monic (inl ≫ q): minimality-descent leg-monicity (§1.651, positivity).
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
  · -- Monic v = Monic (inr ≫ q): symmetric (swap inl↔inr, R₀↔R₀° at the junctions).
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

set_option maxHeartbeats 1000000 in
/-- **§1.651 (pullback half)**: the amalgamating square of two monics is a PULLBACK.

    For monics `m : A↣B`, `n : A↣C`, run the §1.651 amalgamation construction on `B+C`:
    `R₀ :=` image of `pair(m≫inl, n≫inr)`, minimal equivalence `E ⊇ R₀`, effective quotient
    `q : B+C ↠ D`, legs `u := inl≫q`, `v := inr≫q`.  The square `m≫u = n≫v` (the
    commutativity leg) is a pullback: `A` with `(m, n)` IS `B ×_D C`.

    The factorization is the CROSS read-off, dual to `amalgamation_lemma`'s diagonal
    leg-monicity.  A cone point `(b, c)` with `b≫u = c≫v` means `b≫inl ∼_E c≫inr`, i.e.
    `(b≫inl, c≫inr)` lies in `kernelPairRel q`.  Pre/post-composing with `inl`, `inr°`
    keeps the point in the inl×inr CROSS, where (by `E ⊆ F = 1 ∪ R₀ ∪ R₀°` minimality and
    §1.62 disjointness vanishing the `1`/`R₀°` summands) the relation collapses to
    `R₀ ≤ (m≫inl)° ⊚ (n≫inr)`, and the two monic injections cancel to `m° ⊚ n`.  So the
    point factors through `relSub(m° ⊚ n) = image(pair m n)`, giving `a : pt → A` with
    `a≫m = b`, `a≫n = c`; uniqueness from `m` monic. -/
theorem amalgamation_is_pullback [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]
    {A B C : 𝒞} (m : A ⟶ B) (hm : Monic m) (n : A ⟶ C) (hn : Monic n) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D) (hsq : m ≫ u = n ≫ v),
      (Cone.mk (f := u) (g := v) A m n hsq).IsPullback ∧
      (∀ (Q : 𝒞) (uQ : B ⟶ Q) (vQ : C ⟶ Q), m ≫ uQ = n ≫ vQ →
        ∃ dd : D ⟶ Q, u ≫ dd = uQ ∧ v ≫ dd = vQ ∧
          ∀ d' : D ⟶ Q, u ≫ d' = uQ → v ≫ d' = vQ → d' = dd) ∧
      Cover (HasBinaryCoproducts.case u v) := by
  -- ===== Reconstruct the §1.651 relational scaffold (DRY with amalgamation_lemma). =====
  let xi : A ⟶ HasBinaryCoproducts.coprod B C := m ≫ HasBinaryCoproducts.inl
  let yi : A ⟶ HasBinaryCoproducts.coprod B C := n ≫ HasBinaryCoproducts.inr
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
  obtain ⟨E, hEeq, hR₀E, hEmin⟩ := minEquiv_of_rtc (HasBinaryCoproducts.coprod B C) R₀
  obtain ⟨_, D, q, hqcov, _hEle, hleE⟩ := EffectiveRegular.effective E hEeq
  let inl' := HasBinaryCoproducts.inl (A := B) (B := C)
  let inr' := HasBinaryCoproducts.inr (A := B) (B := C)
  have hinl : Monic inl' := inl_mono
  have hinr : Monic inr' := inr_mono
  -- `xi`, `yi` monic; `R₀`'s columns factor through the injections (cover⊥mono descent).
  have hxi : Monic xi := by
    intro W f g h; apply hm; apply hinl
    show (f ≫ m) ≫ inl' = (g ≫ m) ≫ inl'; simpa [xi, Cat.assoc] using h
  have hyi : Monic yi := by
    intro W f g h; apply hn; apply hinr
    show (f ≫ n) ≫ inr' = (g ≫ n) ≫ inr'; simpa [yi, Cat.assoc] using h
  obtain ⟨tA, htA⟩ : ∃ t : R₀.src ⟶ B, t ≫ inl' = R₀.colA := by
    obtain ⟨t, _, ht⟩ := cover_mono_diagonal (image_lift_cover sp) inl_mono
      (c := image.lift sp) (f := R₀.colA) (m := inl') (d := m) (by rw [hR₀A])
    exact ⟨t, ht⟩
  obtain ⟨tB, htB⟩ : ∃ t : R₀.src ⟶ C, t ≫ inr' = R₀.colB := by
    obtain ⟨t, _, ht⟩ := cover_mono_diagonal (image_lift_cover sp) inr_mono
      (c := image.lift sp) (f := R₀.colB) (m := inr') (d := n) (by rw [hR₀B])
    exact ⟨t, ht⟩
  -- The four cross bounds + F-equivalence + E ⊆ F (verbatim from §1.651).
  have hR₀P : RelLe R₀ ((graph xi)° ⊚ (graph yi)) := image_pair_le_recip_comp xi yi
  have hRRop : RelLe (R₀ ⊚ R₀°) (graph (Cat.id (HasBinaryCoproducts.coprod B C))) :=
    rel_le_trans (compose_le hR₀P (reciprocal_mono hR₀P))
      (comp_recip_self_le_diag xi yi hyi)
  have hRopR : RelLe (R₀° ⊚ R₀) (graph (Cat.id (HasBinaryCoproducts.coprod B C))) :=
    rel_le_trans (compose_le (reciprocal_mono hR₀P) hR₀P) (diag_le_one xi yi hxi)
  have hRR : RelLe (R₀ ⊚ R₀) (graph (Cat.id (HasBinaryCoproducts.coprod B C))) :=
    relLe_of_relSub_le_bottom (relSub_comp_le_bottom_mirror R₀ R₀ tB htB tA htA)
  have hRopRop : RelLe (R₀° ⊚ R₀°) (graph (Cat.id (HasBinaryCoproducts.coprod B C))) :=
    relLe_of_relSub_le_bottom (relSub_comp_le_bottom R₀° R₀° tA htA tB htB)
  let Δ : BinRel 𝒞 (HasBinaryCoproducts.coprod B C) (HasBinaryCoproducts.coprod B C) :=
    graph (Cat.id (HasBinaryCoproducts.coprod B C))
  have hFeq : EquivalenceRelation ((Δ ∪ᵣ R₀) ∪ᵣ R₀°) :=
    amalgamation_F_equiv R₀ hRRop hRopR hRR hRopRop
  have hR₀F : RelLe R₀ ((Δ ∪ᵣ R₀) ∪ᵣ R₀°) :=
    rel_le_trans (relUnion_le_right _ R₀) (relUnion_le_left _ _)
  have hEF : RelLe E ((Δ ∪ᵣ R₀) ∪ᵣ R₀°) := hEmin _ hFeq hR₀F
  -- ===== CROSS COLLAPSE: graph inl ⊚ (E ⊚ graph inr°) ≤ graph m° ⊚ graph n. =====
  -- (a) E ⊆ F.
  have hEFcross : RelLe (graph inl' ⊚ (E ⊚ (graph inr')°))
      (graph inl' ⊚ (((Δ ∪ᵣ R₀) ∪ᵣ R₀°) ⊚ (graph inr')°)) :=
    compose_le (rel_le_refl _) (compose_le hEF (rel_le_refl _))
  -- (b) distribute F over the cross, vanish 1/R₀° summands (disjointness) → inl ⊚ (R₀ ⊚ inr°).
  have hcollapseF : RelLe (graph inl' ⊚ (((Δ ∪ᵣ R₀) ∪ᵣ R₀°) ⊚ (graph inr')°))
      (graph inl' ⊚ (R₀ ⊚ (graph inr')°)) := by
    have hΔ0 : RelLe (graph inl' ⊚ (Δ ⊚ (graph inr')°)) (graph inl' ⊚ (R₀ ⊚ (graph inr')°)) := by
      refine rel_le_trans (compose_le (rel_le_refl _) (graph_id_comp ((graph inr')°))) ?_
      refine relLe_of_relSub_le_bottom (relSub_comp_le_bottom (graph inl') ((graph inr')°)
        (Cat.id B) (Cat.id_comp _) (Cat.id C) ?_)
      exact Cat.id_comp _
    have hRop0 : RelLe (graph inl' ⊚ (R₀° ⊚ (graph inr')°))
        (graph inl' ⊚ (R₀ ⊚ (graph inr')°)) := by
      refine relLe_of_relSub_le_bottom (relSub_comp_le_bottom_right (graph inl') _ ?_)
      exact relSub_comp_le_bottom R₀° ((graph inr')°) tA htA (Cat.id C) (Cat.id_comp _)
    have hdistL : RelLe (((Δ ∪ᵣ R₀) ∪ᵣ R₀°) ⊚ (graph inr')°)
        (((Δ ⊚ (graph inr')°) ∪ᵣ (R₀ ⊚ (graph inr')°)) ∪ᵣ (R₀° ⊚ (graph inr')°)) := by
      refine rel_le_trans (compose_union_left (Δ ∪ᵣ R₀) R₀° ((graph inr')°)) ?_
      exact le_relUnion
        (rel_le_trans (compose_union_left Δ R₀ ((graph inr')°))
          (relUnion_le_left _ _))
        (relUnion_le_right _ _)
    refine rel_le_trans (compose_le (rel_le_refl _) hdistL) ?_
    refine rel_le_trans (compose_union_right (graph inl') _ _) ?_
    refine le_relUnion ?_ hRop0
    refine rel_le_trans (compose_union_right (graph inl') _ _) ?_
    exact le_relUnion hΔ0 (rel_le_refl _)
  -- (c) inl ⊚ (R₀ ⊚ inr°) ≤ graph m° ⊚ graph n  (both inl, inr monic; R₀ ≤ xi° ⊚ yi).
  have hcollapse : RelLe (graph inl' ⊚ (R₀ ⊚ (graph inr')°)) ((graph m)° ⊚ graph n) := by
    have hR₀P' : RelLe (graph inl' ⊚ (R₀ ⊚ (graph inr')°))
        (graph inl' ⊚ (((graph xi)° ⊚ graph yi) ⊚ (graph inr')°)) :=
      compose_le (rel_le_refl _) (compose_le hR₀P (rel_le_refl _))
    refine rel_le_trans hR₀P' ?_
    have hA : RelLe (graph inl' ⊚ (((graph xi)° ⊚ graph yi) ⊚ (graph inr')°))
        ((graph inl' ⊚ (graph xi)°) ⊚ (graph yi ⊚ (graph inr')°)) := by
      refine rel_le_trans (compose_le (rel_le_refl _)
        (compose_assoc_of_regular ((graph xi)°) (graph yi) ((graph inr')°)).1) ?_
      exact (compose_assoc_of_regular (graph inl') ((graph xi)°)
        (graph yi ⊚ (graph inr')°)).2
    refine rel_le_trans hA ?_
    -- inl ⊚ xi° = inl ⊚ (inl° ⊚ m°) ≤ (inl ⊚ inl°) ⊚ m° ≤ m° (inl monic).
    have hL : RelLe (graph inl' ⊚ (graph xi)°) ((graph m)°) := by
      have hxirec : RelLe ((graph xi)°) ((graph inl')° ⊚ (graph m)°) := by
        refine rel_le_trans ?_ (rel_le_trans (reciprocal_comp_le (graph m) (graph inl')) ?_)
        · exact reciprocal_mono (show RelLe (graph xi) (graph m ⊚ graph inl') from graph_comp m inl')
        · exact rel_le_refl _
      refine rel_le_trans (compose_le (rel_le_refl _) hxirec) ?_
      refine rel_le_trans (compose_assoc_of_regular (graph inl') ((graph inl')°) ((graph m)°)).2 ?_
      refine rel_le_trans (compose_le (graph_comp_recip_le_one_of_mono inl' hinl) (rel_le_refl _)) ?_
      exact graph_id_comp ((graph m)°)
    -- yi ⊚ inr° = (n ≫ inr) ⊚ inr° ≤ n ⊚ (inr ⊚ inr°) ≤ n (inr monic).
    have hR : RelLe (graph yi ⊚ (graph inr')°) (graph n) := by
      have hyile : RelLe (graph yi) (graph n ⊚ graph inr') := graph_comp n inr'
      refine rel_le_trans (compose_le hyile (rel_le_refl _)) ?_
      refine rel_le_trans (compose_assoc_of_regular (graph n) (graph inr') ((graph inr')°)).1 ?_
      refine rel_le_trans (compose_le (rel_le_refl _) (graph_comp_recip_le_one_of_mono inr' hinr)) ?_
      exact comp_graph_id (graph n)
    exact compose_le hL hR
  -- Full cross collapse as a SUBOBJECT containment (for the pointwise factorization).
  have hcross : RelLe (graph inl' ⊚ ((kernelPairRel q) ⊚ (graph inr')°)) ((graph m)° ⊚ graph n) := by
    have hkpE : RelLe (kernelPairRel q) E :=
      rel_le_trans (kernelPairRel_le_graphComp q) hleE
    refine rel_le_trans (compose_le (rel_le_refl _) (compose_le hkpE (rel_le_refl _))) ?_
    exact rel_le_trans hEFcross (rel_le_trans hcollapseF hcollapse)
  have hcrossSub : (relSub (graph inl' ⊚ ((kernelPairRel q) ⊚ (graph inr')°))).le
      (relSub ((graph m)° ⊚ graph n)) := subLe_of_relLe hcross
  -- the commutativity leg, exactly as in §1.651.
  have hR₀kp : RelLe R₀ (kernelPairRel q) :=
    rel_le_trans (rel_le_trans hR₀E _hEle) (graphComp_le_kernelPairRel q)
  have hsq : m ≫ (inl' ≫ q) = n ≫ (inr' ≫ q) := by
    obtain ⟨⟨w, hwA, hwB⟩⟩ := hR₀kp
    have e1 : w ≫ kp₁ (f := q) = R₀.colA := by simpa [kernelPairRel] using hwA
    have e2 : w ≫ kp₂ (f := q) = R₀.colB := by simpa [kernelPairRel] using hwB
    have hcolq : R₀.colA ≫ q = R₀.colB ≫ q := by
      calc R₀.colA ≫ q = (w ≫ kp₁ (f := q)) ≫ q := by rw [e1]
        _ = w ≫ kp₂ (f := q) ≫ q := by rw [Cat.assoc, kp_sq]
        _ = R₀.colB ≫ q := by rw [← Cat.assoc, e2]
    calc m ≫ inl' ≫ q = xi ≫ q := by rw [← Cat.assoc]
      _ = (image.lift sp ≫ R₀.colA) ≫ q := by rw [hR₀A]
      _ = image.lift sp ≫ R₀.colA ≫ q := Cat.assoc _ _ _
      _ = image.lift sp ≫ R₀.colB ≫ q := by rw [hcolq]
      _ = (image.lift sp ≫ R₀.colB) ≫ q := (Cat.assoc _ _ _).symm
      _ = yi ≫ q := by rw [hR₀B]
      _ = n ≫ inr' ≫ q := Cat.assoc _ _ _
  -- ===== Assemble the pullback. =====
  refine ⟨D, inl' ≫ q, inr' ≫ q, hsq, ?_, ?_, ?_⟩
  -- ===== (1) PULLBACK property. =====
  -- `(graph m)° ⊚ graph n ≤ mn := ⟨A, m, n⟩` (pair m n monic, n monic): the cross point
  -- descends through `A`.  relSub(mn).arr = pair m n.
  let mn : BinRel 𝒞 B C := ⟨A, m, n, monicPair_of_monic_pair m n (monic_pair_of_monic m n hn)⟩
  have hmnSub : (relSub ((graph m)° ⊚ graph n)).le (relSub mn) :=
    subLe_of_relLe (recipGraph_comp_graph_le_span m n hn)
  have hmnarr : (relSub mn).arr = pair m n := rfl
  -- chained subobject containment: relSub Λ ≤ relSub(m°⊚n) ≤ relSub mn.
  let Λ : BinRel 𝒞 B C := graph inl' ⊚ ((kernelPairRel q) ⊚ (graph inr')°)
  have hΛmn : (relSub Λ).le (relSub mn) := Subobject.le_trans hcrossSub hmnSub
  -- ===== Pullback universal property. =====
  intro d
  -- `d.π₁ ≫ (inl'≫q) = d.π₂ ≫ (inr'≫q)`, i.e. `(d.π₁≫inl')≫q = (d.π₂≫inr')≫q`.
  have hdq : (d.π₁ ≫ inl') ≫ q = (d.π₂ ≫ inr') ≫ q := by
    rw [Cat.assoc, Cat.assoc]; exact d.w
  -- lift into the kernel pair of q.
  let wk : d.pt ⟶ kernelPair q := (HasPullbacks.has q q).lift ⟨d.pt, d.π₁ ≫ inl', d.π₂ ≫ inr', hdq⟩
  have hwk₁ : wk ≫ kp₁ (f := q) = d.π₁ ≫ inl' := kp_lift_p₁ _ _ hdq
  have hwk₂ : wk ≫ kp₂ (f := q) = d.π₂ ≫ inr' := kp_lift_p₂ _ _ hdq
  -- point of X := kernelPairRel q ⊚ (graph inr')°  →  allows pair (d.π₁≫inl') d.π₂.
  let X : BinRel 𝒞 (HasBinaryCoproducts.coprod B C) C := (kernelPairRel q) ⊚ (graph inr')°
  have hXmid : wk ≫ (kernelPairRel q).colB = d.π₂ ≫ ((graph inr')°).colA := by
    show wk ≫ kp₂ (f := q) = d.π₂ ≫ inr'; exact hwk₂
  have hXallows : Allows (relSub X) (pair (wk ≫ kp₁ (f := q)) (d.π₂ ≫ ((graph inr')°).colB)) :=
    compose_point_allows (kernelPairRel q) ((graph inr')°) wk d.π₂ hXmid
  -- normalise the allowed pair to `pair (d.π₁≫inl') d.π₂`.
  obtain ⟨kX, hkX⟩ := hXallows
  have hkXA : kX ≫ X.colA = d.π₁ ≫ inl' := by
    have := congrArg (· ≫ fst) hkX
    simp only [Cat.assoc] at this
    rw [show (relSub X).arr ≫ fst = X.colA from fst_pair _ _, fst_pair] at this
    rw [this, hwk₁]
  have hkXB : kX ≫ X.colB = d.π₂ := by
    have := congrArg (· ≫ snd) hkX
    simp only [Cat.assoc] at this
    rw [show (relSub X).arr ≫ snd = X.colB from snd_pair _ _, snd_pair] at this
    show kX ≫ X.colB = d.π₂; rw [this]; exact Cat.comp_id _
  -- point of Λ = graph inl' ⊚ X  →  allows pair d.π₁ d.π₂.
  have hΛmid : d.π₁ ≫ (graph inl').colB = kX ≫ X.colA := by
    show d.π₁ ≫ inl' = kX ≫ X.colA; exact hkXA.symm
  have hΛallows : Allows (relSub Λ) (pair (d.π₁ ≫ (graph inl').colA) (kX ≫ X.colB)) :=
    compose_point_allows (graph inl') X d.π₁ kX hΛmid
  have hΛpair : pair (d.π₁ ≫ (graph inl').colA) (kX ≫ X.colB) = pair d.π₁ d.π₂ := by
    rw [hkXB]; congr 1; exact Cat.comp_id _
  rw [hΛpair] at hΛallows
  -- descend through relSub mn ⟹ a : d.pt → A with a ≫ pair m n = pair d.π₁ d.π₂.
  obtain ⟨gΛ, hgΛ⟩ := hΛallows
  obtain ⟨h, hh⟩ := hΛmn
  let a : d.pt ⟶ A := gΛ ≫ h
  have ha : a ≫ pair m n = pair d.π₁ d.π₂ := by
    show (gΛ ≫ h) ≫ (relSub mn).arr = pair d.π₁ d.π₂
    rw [Cat.assoc, hh, hgΛ]
  have ha₁ : a ≫ m = d.π₁ := by
    have := congrArg (· ≫ fst) ha; simpa [Cat.assoc, fst_pair] using this
  have ha₂ : a ≫ n = d.π₂ := by
    have := congrArg (· ≫ snd) ha; simpa [Cat.assoc, snd_pair] using this
  refine ⟨a, ⟨ha₁, ha₂⟩, fun w hw₁ hw₂ => ?_⟩
  -- uniqueness from m monic: w ≫ m = d.π₁ = a ≫ m.
  exact hm w a (by rw [hw₁, ha₁])
  -- ===== (2) PUSHOUT universal property (identifies D with the §1.62 union). =====
  intro Q uQ vQ hQ
  let caseuv : HasBinaryCoproducts.coprod B C ⟶ Q := HasBinaryCoproducts.case uQ vQ
  have hxicase : xi ≫ caseuv = m ≫ uQ := by
    show (m ≫ inl') ≫ caseuv = m ≫ uQ
    rw [Cat.assoc]; congr 1; exact HasBinaryCoproducts.case_inl _ _
  have hyicase : yi ≫ caseuv = n ≫ vQ := by
    show (n ≫ inr') ≫ caseuv = n ≫ vQ
    rw [Cat.assoc]; congr 1; exact HasBinaryCoproducts.case_inr _ _
  have hR₀case : R₀.colA ≫ caseuv = R₀.colB ≫ caseuv := by
    apply cover_epi (image_lift_cover sp)
    calc image.lift sp ≫ R₀.colA ≫ caseuv = xi ≫ caseuv := by rw [← Cat.assoc, hR₀A]
      _ = m ≫ uQ := hxicase
      _ = n ≫ vQ := hQ
      _ = yi ≫ caseuv := hyicase.symm
      _ = image.lift sp ≫ R₀.colB ≫ caseuv := by rw [← Cat.assoc, hR₀B]
  have hR₀kpc : RelLe R₀ (kernelPairRel caseuv) := by
    let l := (HasPullbacks.has caseuv caseuv).lift ⟨_, R₀.colA, R₀.colB, hR₀case⟩
    exact ⟨⟨l, kp_lift_p₁ R₀.colA R₀.colB hR₀case, kp_lift_p₂ R₀.colA R₀.colB hR₀case⟩⟩
  have hEkpc := hEmin (kernelPairRel caseuv) (level_is_equivalence_relation caseuv) hR₀kpc
  have hkpqkpc : RelLe (kernelPairRel q) (kernelPairRel caseuv) :=
    rel_le_trans (rel_le_trans (kernelPairRel_le_graphComp q) hleE) hEkpc
  have hkpeq : kp₁ (f := q) ≫ caseuv = kp₂ (f := q) ≫ caseuv := by
    obtain ⟨⟨φ, hφA, hφB⟩⟩ := hkpqkpc
    have e1 : φ ≫ kp₁ (f := caseuv) = kp₁ (f := q) := by simpa [kernelPairRel] using hφA
    have e2 : φ ≫ kp₂ (f := caseuv) = kp₂ (f := q) := by simpa [kernelPairRel] using hφB
    calc kp₁ (f := q) ≫ caseuv = (φ ≫ kp₁ (f := caseuv)) ≫ caseuv := by rw [e1]
      _ = φ ≫ kp₂ (f := caseuv) ≫ caseuv := by rw [Cat.assoc, kp_sq]
      _ = kp₂ (f := q) ≫ caseuv := by rw [← Cat.assoc, e2]
  obtain ⟨dd, hdd, huniqdd⟩ := cover_is_coequalizer_of_level q hqcov caseuv hkpeq
  refine ⟨dd, ?_, ?_, ?_⟩
  · show (inl' ≫ q) ≫ dd = uQ
    rw [Cat.assoc, hdd]; exact HasBinaryCoproducts.case_inl _ _
  · show (inr' ≫ q) ≫ dd = vQ
    rw [Cat.assoc, hdd]; exact HasBinaryCoproducts.case_inr _ _
  · intro d' hd'1 hd'2
    apply huniqdd
    refine HasBinaryCoproducts.case_uniq uQ vQ (q ≫ d') ?_ ?_
    · rw [← Cat.assoc]; exact hd'1
    · rw [← Cat.assoc]; exact hd'2
  -- ===== (3) `case u v` is a cover: `case (inl'≫q) (inr'≫q) = q` (`case_uniq`), `q` a cover. =====
  have hcase : HasBinaryCoproducts.case (inl' ≫ q) (inr' ≫ q) = q :=
    (HasBinaryCoproducts.case_uniq (inl' ≫ q) (inr' ≫ q) q rfl rfl).symm
  intro Z mm g hmm hfac
  exact hqcov mm g hmm (by rw [hfac, hcase])

set_option maxHeartbeats 1000000 in
/-- **§1.651 (pushout property)**: the amalgamating square of two maps is a PUSHOUT.

    Companion to `amalgamation_is_pullback` (which needs `m, n` monic); the pushout
    universal property holds for ARBITRARY `m, n`.  The effective quotient `q : B+C ↠ D` by
    the minimal equivalence `E ⊇ R₀` is universal: any cocone `(Q; uQ, vQ)` over `(m, n)`
    yields `case uQ vQ : B+C → Q` respecting `R₀` (so `E ⊆ level(case uQ vQ)` by minimality),
    hence factoring uniquely through the cover `q` (`cover_is_coequalizer_of_level`).  This is
    what identifies the §1.651 `D` with the §1.62 union `A₁∪A₂` (both pushouts of the same
    span), the missing converse flagged on `preTopos_functor_preserves_monic_pullbacks`. -/
theorem amalgamation_is_pushout [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]
    {A B C : 𝒞} (m : A ⟶ B) (n : A ⟶ C) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D) (_hsq : m ≫ u = n ≫ v),
      ∀ (Q : 𝒞) (uQ : B ⟶ Q) (vQ : C ⟶ Q), m ≫ uQ = n ≫ vQ →
        ∃ d : D ⟶ Q, u ≫ d = uQ ∧ v ≫ d = vQ ∧
          ∀ d' : D ⟶ Q, u ≫ d' = uQ → v ≫ d' = vQ → d' = d := by
  let inl' := HasBinaryCoproducts.inl (A := B) (B := C)
  let inr' := HasBinaryCoproducts.inr (A := B) (B := C)
  let xi : A ⟶ HasBinaryCoproducts.coprod B C := m ≫ inl'
  let yi : A ⟶ HasBinaryCoproducts.coprod B C := n ≫ inr'
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
  obtain ⟨E, hEeq, hR₀E, hEmin⟩ := minEquiv_of_rtc (HasBinaryCoproducts.coprod B C) R₀
  obtain ⟨_, D, q, hqcov, hEle, hleE⟩ := EffectiveRegular.effective E hEeq
  have hR₀kp : RelLe R₀ (kernelPairRel q) :=
    rel_le_trans (rel_le_trans hR₀E hEle) (graphComp_le_kernelPairRel q)
  have hsq : m ≫ (inl' ≫ q) = n ≫ (inr' ≫ q) := by
    obtain ⟨⟨w, hwA, hwB⟩⟩ := hR₀kp
    have e1 : w ≫ kp₁ (f := q) = R₀.colA := by simpa [kernelPairRel] using hwA
    have e2 : w ≫ kp₂ (f := q) = R₀.colB := by simpa [kernelPairRel] using hwB
    have hcolq : R₀.colA ≫ q = R₀.colB ≫ q := by
      calc R₀.colA ≫ q = (w ≫ kp₁ (f := q)) ≫ q := by rw [e1]
        _ = w ≫ kp₂ (f := q) ≫ q := by rw [Cat.assoc, kp_sq]
        _ = R₀.colB ≫ q := by rw [← Cat.assoc, e2]
    calc m ≫ inl' ≫ q = xi ≫ q := by rw [← Cat.assoc]
      _ = (image.lift sp ≫ R₀.colA) ≫ q := by rw [hR₀A]
      _ = image.lift sp ≫ R₀.colA ≫ q := Cat.assoc _ _ _
      _ = image.lift sp ≫ R₀.colB ≫ q := by rw [hcolq]
      _ = (image.lift sp ≫ R₀.colB) ≫ q := (Cat.assoc _ _ _).symm
      _ = yi ≫ q := by rw [hR₀B]
      _ = n ≫ inr' ≫ q := Cat.assoc _ _ _
  refine ⟨D, inl' ≫ q, inr' ≫ q, hsq, ?_⟩
  intro Q uQ vQ hQ
  let caseuv : HasBinaryCoproducts.coprod B C ⟶ Q := HasBinaryCoproducts.case uQ vQ
  have hxicase : xi ≫ caseuv = m ≫ uQ := by
    show (m ≫ inl') ≫ caseuv = m ≫ uQ
    rw [Cat.assoc]; congr 1; exact HasBinaryCoproducts.case_inl _ _
  have hyicase : yi ≫ caseuv = n ≫ vQ := by
    show (n ≫ inr') ≫ caseuv = n ≫ vQ
    rw [Cat.assoc]; congr 1; exact HasBinaryCoproducts.case_inr _ _
  have hR₀case : R₀.colA ≫ caseuv = R₀.colB ≫ caseuv := by
    apply cover_epi (image_lift_cover sp)
    calc image.lift sp ≫ R₀.colA ≫ caseuv = xi ≫ caseuv := by rw [← Cat.assoc, hR₀A]
      _ = m ≫ uQ := hxicase
      _ = n ≫ vQ := hQ
      _ = yi ≫ caseuv := hyicase.symm
      _ = image.lift sp ≫ R₀.colB ≫ caseuv := by rw [← Cat.assoc, hR₀B]
  have hR₀kpc : RelLe R₀ (kernelPairRel caseuv) := by
    let l := (HasPullbacks.has caseuv caseuv).lift ⟨_, R₀.colA, R₀.colB, hR₀case⟩
    exact ⟨⟨l, kp_lift_p₁ R₀.colA R₀.colB hR₀case, kp_lift_p₂ R₀.colA R₀.colB hR₀case⟩⟩
  have hEkpc := hEmin (kernelPairRel caseuv) (level_is_equivalence_relation caseuv) hR₀kpc
  have hkpqkpc : RelLe (kernelPairRel q) (kernelPairRel caseuv) :=
    rel_le_trans (rel_le_trans (kernelPairRel_le_graphComp q) hleE) hEkpc
  have hkpeq : kp₁ (f := q) ≫ caseuv = kp₂ (f := q) ≫ caseuv := by
    obtain ⟨⟨φ, hφA, hφB⟩⟩ := hkpqkpc
    have e1 : φ ≫ kp₁ (f := caseuv) = kp₁ (f := q) := by simpa [kernelPairRel] using hφA
    have e2 : φ ≫ kp₂ (f := caseuv) = kp₂ (f := q) := by simpa [kernelPairRel] using hφB
    calc kp₁ (f := q) ≫ caseuv = (φ ≫ kp₁ (f := caseuv)) ≫ caseuv := by rw [e1]
      _ = φ ≫ kp₂ (f := caseuv) ≫ caseuv := by rw [Cat.assoc, kp_sq]
      _ = kp₂ (f := q) ≫ caseuv := by rw [← Cat.assoc, e2]
  obtain ⟨d, hd, huniqd⟩ := cover_is_coequalizer_of_level q hqcov caseuv hkpeq
  refine ⟨d, ?_, ?_, ?_⟩
  · show (inl' ≫ q) ≫ d = uQ
    rw [Cat.assoc, hd]; exact HasBinaryCoproducts.case_inl _ _
  · show (inr' ≫ q) ≫ d = vQ
    rw [Cat.assoc, hd]; exact HasBinaryCoproducts.case_inr _ _
  · intro d' hd'1 hd'2
    apply huniqd
    refine HasBinaryCoproducts.case_uniq uQ vQ (q ≫ d') ?_ ?_
    · rw [← Cat.assoc]; exact hd'1
    · rw [← Cat.assoc]; exact hd'2

/-- Post-composing a pullback cospan with a MONIC leaves it a pullback: a cone over
    `(f≫w, g≫w)` is, after cancelling the monic `w`, a cone over `(f, g)`.  (Pasting a
    pullback square with a trivial monic square.)  Used to descend the §1.651 pullback over
    the union legs to a pullback over the original monic cospan. -/
theorem isPullback_postcomp_mono {A B C' D : 𝒞} {f : A ⟶ C'} {g : B ⟶ C'}
    {c : Cone f g} (hc : c.IsPullback) {w : C' ⟶ D} (hw : Monic w) :
    (Cone.mk (f := f ≫ w) (g := g ≫ w) c.pt c.π₁ c.π₂
      (by rw [← Cat.assoc, ← Cat.assoc, c.w])).IsPullback := by
  intro d
  have hdw : d.π₁ ≫ f = d.π₂ ≫ g := by
    apply hw; rw [Cat.assoc, Cat.assoc]; exact d.w
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc (Cone.mk d.pt d.π₁ d.π₂ hdw)
  exact ⟨u, ⟨hu₁, hu₂⟩, fun v hv₁ hv₂ => huniq v hv₁ hv₂⟩

/-- A descent out of one pushout that factors through a MONIC on a SECOND pushout of the SAME
    span is itself monic.  Two pushouts of `(f, g)` are canonically isomorphic (`θ : D ≅ W` by
    mutual universal descent); the `D`-descent `δ` to `(AA; ι₁≫w, ι₂≫w)` equals `θ ≫ w`, and
    `θ` (split monic) composed with the monic `w` is monic.  This is how the §1.651 amalgamation
    `D` (a pushout) is identified with the §1.62 union `W ↪ AA` (monic), making the descent
    `δ : D → AA` monic — the missing leg of `preTopos_functor_preserves_monic_pullbacks`. -/
theorem pushout_descent_mono {A B C D W AA : 𝒞} {f : A ⟶ B} {g : A ⟶ C}
    {u : B ⟶ D} {v : C ⟶ D} (hsqD : f ≫ u = g ≫ v)
    (hUMPD : ∀ (Q : 𝒞) (uQ : B ⟶ Q) (vQ : C ⟶ Q), f ≫ uQ = g ≫ vQ →
        ∃ dd : D ⟶ Q, u ≫ dd = uQ ∧ v ≫ dd = vQ ∧
          ∀ d' : D ⟶ Q, u ≫ d' = uQ → v ≫ d' = vQ → d' = dd)
    {ι₁ : B ⟶ W} {ι₂ : C ⟶ W} (hsqW : f ≫ ι₁ = g ≫ ι₂)
    (hUMPW : ∀ (Q : 𝒞) (uQ : B ⟶ Q) (vQ : C ⟶ Q), f ≫ uQ = g ≫ vQ →
        ∃ dd : W ⟶ Q, ι₁ ≫ dd = uQ ∧ ι₂ ≫ dd = vQ ∧
          ∀ d' : W ⟶ Q, ι₁ ≫ d' = uQ → ι₂ ≫ d' = vQ → d' = dd)
    {w : W ⟶ AA} (hw : Monic w) {δ : D ⟶ AA}
    (hδ₁ : u ≫ δ = ι₁ ≫ w) (hδ₂ : v ≫ δ = ι₂ ≫ w) :
    Monic δ := by
  obtain ⟨θ, hθ₁, hθ₂, _⟩ := hUMPD W ι₁ ι₂ hsqW
  obtain ⟨θ', hθ'₁, hθ'₂, _⟩ := hUMPW D u v hsqD
  obtain ⟨_, _, _, huniqD⟩ := hUMPD D u v hsqD
  have hθθ' : θ ≫ θ' = Cat.id D := by
    rw [huniqD (θ ≫ θ') (by rw [← Cat.assoc, hθ₁, hθ'₁]) (by rw [← Cat.assoc, hθ₂, hθ'₂]),
        ← huniqD (Cat.id D) (Cat.comp_id _) (Cat.comp_id _)]
  obtain ⟨_, _, _, huniqDA⟩ := hUMPD AA (ι₁ ≫ w) (ι₂ ≫ w) (by rw [← Cat.assoc, ← Cat.assoc, hsqW])
  have hδ_eq : δ = θ ≫ w := by
    rw [huniqDA δ hδ₁ hδ₂,
        ← huniqDA (θ ≫ w) (by rw [← Cat.assoc, hθ₁]) (by rw [← Cat.assoc, hθ₂])]
  rw [hδ_eq]
  intro X p₁ p₂ hp
  apply (show Monic θ from by
    intro Y a b hab
    have : a ≫ (θ ≫ θ') = b ≫ (θ ≫ θ') := by rw [← Cat.assoc, ← Cat.assoc, hab]
    rwa [hθθ', Cat.comp_id, Cat.comp_id] at this)
  apply hw
  simpa only [Cat.assoc] using hp

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
  a genuine, Sorry-free construction.  It is the dual of the kernel pair used throughout
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
    iso, i.e. `m` IS the equalizer of `(u, v)` — is the open effective-coregularity
    residual; `pretopos_balanced` is now proven Sorry-free, so it no longer carries this
    obligation.  Unrelated to the §1.543 capitalization lemma, which is itself proven.) -/
theorem cokernelPair_m_factors_eq [PreTopos 𝒞] [HasCoequalizers 𝒞] [HasEqualizers 𝒞]
    {A B : 𝒞} (m : A ⟶ B) :
    eqLift (cokernelPairU m) (cokernelPairV m) m (cokernelPair_sq m)
      ≫ eqMap (cokernelPairU m) (cokernelPairV m) = m :=
  eqLift_fac _ _ _ _

/-- **§1.652 (the reverse F-analysis)**: in a pre-topos, a MONIC that is also EPIC is a COVER.

    This is the dual read-off of `amalgamation_lemma`'s leg-monicity, on the SAME generated
    equivalence relation `E ⊆ F = 1 ∪ R₀ ∪ R₀°` over the disjoint coproduct `B ⊕ B`.  Apply the
    §1.651 amalgamation construction to `x = y = m`: on `B ⊕ B` take `R₀ =` image of
    `pair(m≫inl, m≫inr)`, close it to the minimal equivalence `E` (via `minEquiv_of_rtc`), and let
    `q : B ⊕ B ↠ D` be its effective quotient, with legs `u := inl≫q`, `v := inr≫q`.

    `m` epic forces `u = v` (`hepi` applied to the cokernel-pair square `m≫u = m≫v`).  Then:
    * (totality, lower bound) `1_B ≤ u ⊚ u° = (inl≫q) ⊚ (inr≫q)°` (using `u = v`)
      `≤ inl ⊚ (q ⊚ q°) ⊚ inr° ≤ inl ⊚ E ⊚ inr°` (since `q⊚q° ≤ E`);
    * (`E ⊆ F` + cross-vanishing) `inl ⊚ E ⊚ inr° ≤ inl ⊚ F ⊚ inr° ≤ inl ⊚ R₀ ⊚ inr°`, because the
      `1` and `R₀°` summands of `F` vanish on the inl/inr cross by §1.62 disjointness
      (`inl ∩ inr = 0`);
    * (collapse) `inl ⊚ R₀ ⊚ inr° ≤ inl ⊚ (m≫inl)° ⊚ (m≫inr) ⊚ inr° = (inl⊚inl°) ⊚ m° ⊚ m ⊚ (inr⊚inr°)
      = m° ⊚ m` (both `inl`, `inr` monic, so their levels are the diagonal).
    Chaining: `1_B ≤ m° ⊚ m`, which is exactly the relational cover criterion §1.569
    (`cover_iff_one_le_reciprocal_comp_self`).  No path-length / `relPow` induction is needed: the
    cross-vanishing is the same `relSub_*_le_bottom` positivity used for leg-monicity. -/
theorem monic_epic_is_cover [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞] {A B : 𝒞}
    (m : A ⟶ B) (hm : Monic m)
    (hepi : ∀ {C : 𝒞} (g h : B ⟶ C), m ≫ g = m ≫ h → g = h) : Cover m := by
  -- ===== Reconstruct the amalgamation relational scaffold for x = y = m (DRY with §1.651). =====
  let xi : A ⟶ HasBinaryCoproducts.coprod B B := m ≫ HasBinaryCoproducts.inl
  let yi : A ⟶ HasBinaryCoproducts.coprod B B := m ≫ HasBinaryCoproducts.inr
  let sp : A ⟶ prod (HasBinaryCoproducts.coprod B B) (HasBinaryCoproducts.coprod B B) := pair xi yi
  let I := image sp
  have hImp : MonicPair (I.arr ≫ fst) (I.arr ≫ snd) :=
    monicPair_of_monic_pair _ _ (by rw [← pair_eta I.arr]; exact I.monic)
  let R₀ : BinRel 𝒞 (HasBinaryCoproducts.coprod B B) (HasBinaryCoproducts.coprod B B) :=
    ⟨I.dom, I.arr ≫ fst, I.arr ≫ snd, hImp⟩
  -- Generated minimal equivalence relation E ⊇ R₀ and its effective quotient q : B⊕B ↠ D.
  obtain ⟨E, hEeq, hR₀E, _hEmin⟩ := minEquiv_of_rtc (HasBinaryCoproducts.coprod B B) R₀
  obtain ⟨_, D, q, _hqcov, _hEle, hleE⟩ := EffectiveRegular.effective E hEeq
  -- `inl`, `inr` are monic (§1.62 positivity).
  have hinl : Monic (HasBinaryCoproducts.inl (A := B) (B := B)) := inl_mono
  have hinr : Monic (HasBinaryCoproducts.inr (A := B) (B := B)) := inr_mono
  -- The cokernel-pair square `m ≫ (inl≫q) = m ≫ (inr≫q)`, from R₀ ⊑ E ⊑ level q.
  have hR₀kp : RelLe R₀ (kernelPairRel q) :=
    rel_le_trans (rel_le_trans hR₀E _hEle) (graphComp_le_kernelPairRel q)
  have hR₀A : image.lift sp ≫ R₀.colA = xi := by
    show image.lift sp ≫ I.arr ≫ fst = xi; rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hR₀B : image.lift sp ≫ R₀.colB = yi := by
    show image.lift sp ≫ I.arr ≫ snd = yi; rw [← Cat.assoc, image.lift_fac, snd_pair]
  have hsq : m ≫ (HasBinaryCoproducts.inl ≫ q) = m ≫ (HasBinaryCoproducts.inr ≫ q) := by
    obtain ⟨⟨w, hwA, hwB⟩⟩ := hR₀kp
    have e1 : w ≫ kp₁ (f := q) = R₀.colA := by simpa [kernelPairRel] using hwA
    have e2 : w ≫ kp₂ (f := q) = R₀.colB := by simpa [kernelPairRel] using hwB
    have hcolq : R₀.colA ≫ q = R₀.colB ≫ q := by
      calc R₀.colA ≫ q = (w ≫ kp₁ (f := q)) ≫ q := by rw [e1]
        _ = w ≫ kp₂ (f := q) ≫ q := by rw [Cat.assoc, kp_sq]
        _ = R₀.colB ≫ q := by rw [← Cat.assoc, e2]
    calc m ≫ HasBinaryCoproducts.inl ≫ q = xi ≫ q := by rw [← Cat.assoc]
      _ = (image.lift sp ≫ R₀.colA) ≫ q := by rw [hR₀A]
      _ = image.lift sp ≫ R₀.colA ≫ q := Cat.assoc _ _ _
      _ = image.lift sp ≫ R₀.colB ≫ q := by rw [hcolq]
      _ = (image.lift sp ≫ R₀.colB) ≫ q := (Cat.assoc _ _ _).symm
      _ = yi ≫ q := by rw [hR₀B]
      _ = m ≫ HasBinaryCoproducts.inr ≫ q := Cat.assoc _ _ _
  -- m epic ⟹ the two legs are EQUAL.
  have huv : HasBinaryCoproducts.inl ≫ q = HasBinaryCoproducts.inr ≫ q := hepi _ _ hsq
  -- ===== Abbreviations for the relation-algebra chain. =====
  let inl' := HasBinaryCoproducts.inl (A := B) (B := B)
  let inr' := HasBinaryCoproducts.inr (A := B) (B := B)
  -- (1) LOWER BOUND: 1_B ≤ graph inl ⊚ ((graph q ⊚ graph q°) ⊚ graph inr°).
  have hlow : RelLe (graph (Cat.id B))
      (graph inl' ⊚ ((graph q ⊚ (graph q)°) ⊚ (graph inr')°)) := by
    -- totality of u := inl ≫ q (any morphism's graph is entire): 1 ≤ u ⊚ u°.
    have htot : RelLe (graph (Cat.id B))
        (graph (inl' ≫ q) ⊚ (graph (inl' ≫ q))°) := (graph_is_map (inl' ≫ q)).1
    -- u ⊚ u° ≤ (graph inl ⊚ graph q) ⊚ (graph inr ⊚ graph q)°: left factor via graph_comp,
    -- right factor via u = v (u° = v° ≤ (graph inr ⊚ graph q)°).
    have hrecv : RelLe ((graph (inl' ≫ q))°) ((graph inr' ⊚ graph q)°) := by
      have h := reciprocal_mono (graph_comp inr' q)  -- (graph(inr≫q))° ≤ (graph inr ⊚ graph q)°
      rwa [show inr' ≫ q = inl' ≫ q from huv.symm] at h
    have h1 : RelLe (graph (inl' ≫ q) ⊚ (graph (inl' ≫ q))°)
        ((graph inl' ⊚ graph q) ⊚ ((graph inr' ⊚ graph q)°)) :=
      compose_le (graph_comp inl' q) hrecv
    -- reassociate (graph inl ⊚ graph q) ⊚ (graph inr ⊚ graph q)° into the target shape.
    have h2 : RelLe ((graph inl' ⊚ graph q) ⊚ ((graph inr' ⊚ graph q)°))
        (graph inl' ⊚ ((graph q ⊚ (graph q)°) ⊚ (graph inr')°)) := by
      -- (graph inr ⊚ graph q)° ≤ graph q° ⊚ graph inr°.
      have hrec : RelLe ((graph inr' ⊚ graph q)°) ((graph q)° ⊚ (graph inr')°) :=
        reciprocal_comp_le (graph inr') (graph q)
      refine rel_le_trans (compose_le (rel_le_refl _) hrec) ?_
      -- (graph inl ⊚ graph q) ⊚ (graph q° ⊚ graph inr°) reassociates to the target.
      refine rel_le_trans (compose_assoc_of_regular (graph inl') (graph q)
        ((graph q)° ⊚ (graph inr')°)).1 ?_
      exact compose_le (rel_le_refl _)
        (compose_assoc_of_regular (graph q) ((graph q)°) ((graph inr')°)).2
    exact rel_le_trans htot (rel_le_trans h1 h2)
  -- (2) push graph q ⊚ graph q° up to E.
  have hupE : RelLe (graph inl' ⊚ ((graph q ⊚ (graph q)°) ⊚ (graph inr')°))
      (graph inl' ⊚ (E ⊚ (graph inr')°)) :=
    compose_le (rel_le_refl _) (compose_le hleE (rel_le_refl _))
  -- (3) E ⊆ F = 1 ∪ R₀ ∪ R₀°, and the cross-vanishing collapses inl ⊚ F ⊚ inr° to inl ⊚ R₀ ⊚ inr°.
  let Δ : BinRel 𝒞 (HasBinaryCoproducts.coprod B B) (HasBinaryCoproducts.coprod B B) :=
    graph (Cat.id (HasBinaryCoproducts.coprod B B))
  -- the four cross-composite bounds (reused exactly as in §1.651, for the F-equivalence).
  have hxi : Monic xi := by
    intro W f g h
    apply hm; apply hinl
    show (f ≫ m) ≫ HasBinaryCoproducts.inl = (g ≫ m) ≫ HasBinaryCoproducts.inl
    simpa [xi, Cat.assoc] using h
  have hyi : Monic yi := by
    intro W f g h
    apply hm; apply hinr
    show (f ≫ m) ≫ HasBinaryCoproducts.inr = (g ≫ m) ≫ HasBinaryCoproducts.inr
    simpa [yi, Cat.assoc] using h
  obtain ⟨tA, htA⟩ : ∃ t : R₀.src ⟶ B, t ≫ HasBinaryCoproducts.inl = R₀.colA := by
    obtain ⟨t, _, ht⟩ := cover_mono_diagonal (image_lift_cover sp) inl_mono
      (c := image.lift sp) (f := R₀.colA) (m := HasBinaryCoproducts.inl) (d := m) (by rw [hR₀A])
    exact ⟨t, ht⟩
  obtain ⟨tB, htB⟩ : ∃ t : R₀.src ⟶ B, t ≫ HasBinaryCoproducts.inr = R₀.colB := by
    obtain ⟨t, _, ht⟩ := cover_mono_diagonal (image_lift_cover sp) inr_mono
      (c := image.lift sp) (f := R₀.colB) (m := HasBinaryCoproducts.inr) (d := m) (by rw [hR₀B])
    exact ⟨t, ht⟩
  have hR₀P : RelLe R₀ ((graph xi)° ⊚ (graph yi)) := image_pair_le_recip_comp xi yi
  have hRRop : RelLe (R₀ ⊚ R₀°) (graph (Cat.id (HasBinaryCoproducts.coprod B B))) :=
    rel_le_trans (compose_le hR₀P (reciprocal_mono hR₀P))
      (comp_recip_self_le_diag xi yi hyi)
  have hRopR : RelLe (R₀° ⊚ R₀) (graph (Cat.id (HasBinaryCoproducts.coprod B B))) :=
    rel_le_trans (compose_le (reciprocal_mono hR₀P) hR₀P) (diag_le_one xi yi hxi)
  have hRR : RelLe (R₀ ⊚ R₀) (graph (Cat.id (HasBinaryCoproducts.coprod B B))) :=
    relLe_of_relSub_le_bottom (relSub_comp_le_bottom_mirror R₀ R₀ tB htB tA htA)
  have hRopRop : RelLe (R₀° ⊚ R₀°) (graph (Cat.id (HasBinaryCoproducts.coprod B B))) :=
    relLe_of_relSub_le_bottom (relSub_comp_le_bottom R₀° R₀° tA htA tB htB)
  have hFeq : EquivalenceRelation ((Δ ∪ᵣ R₀) ∪ᵣ R₀°) :=
    amalgamation_F_equiv R₀ hRRop hRopR hRR hRopRop
  have hR₀F : RelLe R₀ ((Δ ∪ᵣ R₀) ∪ᵣ R₀°) :=
    rel_le_trans (relUnion_le_right _ R₀) (relUnion_le_left _ _)
  have hEF : RelLe E ((Δ ∪ᵣ R₀) ∪ᵣ R₀°) := _hEmin _ hFeq hR₀F
  -- inl ⊚ E ⊚ inr° ≤ inl ⊚ F ⊚ inr°.
  have hEFcross : RelLe (graph inl' ⊚ (E ⊚ (graph inr')°))
      (graph inl' ⊚ (((Δ ∪ᵣ R₀) ∪ᵣ R₀°) ⊚ (graph inr')°)) :=
    compose_le (rel_le_refl _) (compose_le hEF (rel_le_refl _))
  -- distribute F over the cross and vanish the 1 / R₀° summands (disjointness).
  -- inl ⊚ ((Δ ∪ R₀ ∪ R₀°) ⊚ inr°) ≤ inl ⊚ (R₀ ⊚ inr°).
  have hcollapseF : RelLe (graph inl' ⊚ (((Δ ∪ᵣ R₀) ∪ᵣ R₀°) ⊚ (graph inr')°))
      (graph inl' ⊚ (R₀ ⊚ (graph inr')°)) := by
    -- inl ⊚ (Δ ⊚ inr°) vanishes: = inl ⊚ inr° below bottom (disjointness).
    have hΔ0 : RelLe (graph inl' ⊚ (Δ ⊚ (graph inr')°)) (graph inl' ⊚ (R₀ ⊚ (graph inr')°)) := by
      refine rel_le_trans (compose_le (rel_le_refl _) (graph_id_comp ((graph inr')°))) ?_
      refine relLe_of_relSub_le_bottom (relSub_comp_le_bottom (graph inl') ((graph inr')°)
        (Cat.id B) (Cat.id_comp _) (Cat.id B) ?_)
      exact Cat.id_comp _
    -- inl ⊚ (R₀° ⊚ inr°) vanishes: R₀°'s left column factors through inr, inl ∩ inr = 0.
    have hRop0 : RelLe (graph inl' ⊚ (R₀° ⊚ (graph inr')°))
        (graph inl' ⊚ (R₀ ⊚ (graph inr')°)) := by
      refine relLe_of_relSub_le_bottom (relSub_comp_le_bottom_right (graph inl') _ ?_)
      exact relSub_comp_le_bottom R₀° ((graph inr')°) tA htA (Cat.id B) (Cat.id_comp _)
    -- distribute inl ⊚ (F ⊚ inr°) = inl ⊚ ((Δ⊚inr° ∪ R₀⊚inr°) ∪ R₀°⊚inr°) and push past inl.
    have hdistL : RelLe (((Δ ∪ᵣ R₀) ∪ᵣ R₀°) ⊚ (graph inr')°)
        (((Δ ⊚ (graph inr')°) ∪ᵣ (R₀ ⊚ (graph inr')°)) ∪ᵣ (R₀° ⊚ (graph inr')°)) := by
      refine rel_le_trans (compose_union_left (Δ ∪ᵣ R₀) R₀° ((graph inr')°)) ?_
      exact le_relUnion
        (rel_le_trans (compose_union_left Δ R₀ ((graph inr')°))
          (relUnion_le_left _ _))
        (relUnion_le_right _ _)
    refine rel_le_trans (compose_le (rel_le_refl _) hdistL) ?_
    refine rel_le_trans (compose_union_right (graph inl') _ _) ?_
    refine le_relUnion ?_ hRop0
    refine rel_le_trans (compose_union_right (graph inl') _ _) ?_
    exact le_relUnion hΔ0 (rel_le_refl _)
  -- (4) COLLAPSE: inl ⊚ (R₀ ⊚ inr°) ≤ m° ⊚ m  (both inl, inr monic; R₀ ≤ (m≫inl)° ⊚ (m≫inr)).
  have hcollapse : RelLe (graph inl' ⊚ (R₀ ⊚ (graph inr')°)) ((graph m)° ⊚ graph m) := by
    -- R₀ ≤ (graph xi)° ⊚ graph yi = (graph(m≫inl))° ⊚ graph(m≫inr).
    have hR₀P' : RelLe (graph inl' ⊚ (R₀ ⊚ (graph inr')°))
        (graph inl' ⊚ (((graph xi)° ⊚ graph yi) ⊚ (graph inr')°)) :=
      compose_le (rel_le_refl _) (compose_le hR₀P (rel_le_refl _))
    refine rel_le_trans hR₀P' ?_
    -- reassociate to (inl ⊚ xi°) ⊚ (yi ⊚ inr°).
    have hA : RelLe (graph inl' ⊚ (((graph xi)° ⊚ graph yi) ⊚ (graph inr')°))
        ((graph inl' ⊚ (graph xi)°) ⊚ (graph yi ⊚ (graph inr')°)) := by
      refine rel_le_trans (compose_le (rel_le_refl _)
        (compose_assoc_of_regular ((graph xi)°) (graph yi) ((graph inr')°)).1) ?_
      exact (compose_assoc_of_regular (graph inl') ((graph xi)°)
        (graph yi ⊚ (graph inr')°)).2
    refine rel_le_trans hA ?_
    -- inl ⊚ xi° = inl ⊚ (inl° ⊚ m°) ≤ (inl ⊚ inl°) ⊚ m° ≤ m° (inl monic).
    have hL : RelLe (graph inl' ⊚ (graph xi)°) ((graph m)°) := by
      have hxirec : RelLe ((graph xi)°) ((graph inl')° ⊚ (graph m)°) := by
        have h := reciprocal_mono (comp_graph m inl')  -- graph m ⊚ graph inl ≤ graph (m≫inl)=graph xi
        refine rel_le_trans ?_ (rel_le_trans (reciprocal_comp_le (graph m) (graph inl')) ?_)
        · exact reciprocal_mono (show RelLe (graph xi) (graph m ⊚ graph inl') from graph_comp m inl')
        · exact rel_le_refl _
      refine rel_le_trans (compose_le (rel_le_refl _) hxirec) ?_
      refine rel_le_trans (compose_assoc_of_regular (graph inl') ((graph inl')°) ((graph m)°)).2 ?_
      refine rel_le_trans (compose_le (graph_comp_recip_le_one_of_mono inl' hinl) (rel_le_refl _)) ?_
      exact graph_id_comp ((graph m)°)
    -- yi ⊚ inr° = (m ⊚ inr) ⊚ inr° ≤ m ⊚ (inr ⊚ inr°) ≤ m (inr monic).
    have hR : RelLe (graph yi ⊚ (graph inr')°) (graph m) := by
      have hyile : RelLe (graph yi) (graph m ⊚ graph inr') := graph_comp m inr'
      refine rel_le_trans (compose_le hyile (rel_le_refl _)) ?_
      refine rel_le_trans (compose_assoc_of_regular (graph m) (graph inr') ((graph inr')°)).1 ?_
      refine rel_le_trans (compose_le (rel_le_refl _) (graph_comp_recip_le_one_of_mono inr' hinr)) ?_
      exact comp_graph_id (graph m)
    exact compose_le hL hR
  -- ===== Chain everything: 1_B ≤ m° ⊚ m, hence m is a cover (§1.569). =====
  have hcover : RelLe (graph (Cat.id B)) ((graph m)° ⊚ graph m) :=
    rel_le_trans hlow (rel_le_trans hupE (rel_le_trans hEFcross
      (rel_le_trans hcollapseF hcollapse)))
  intro C n g hn hg
  exact (cover_iff_one_le_reciprocal_comp_self m).mpr hcover n g hn hg

/-- **§1.652 (crux): a pre-topos is BALANCED** — a map that is both monic and epic is an
    isomorphism.  Now Sorry-free: monic + epic ⟹ cover (`monic_epic_is_cover`, the reverse
    F-analysis), and monic + cover ⟹ iso (`monic_cover_iso`). -/
theorem pretopos_balanced [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞] {A B : 𝒞}
    (m : A ⟶ B) (hm : Monic m)
    (hepi : ∀ {C : 𝒞} (g h : B ⟶ C), m ≫ g = m ≫ h → g = h) : IsIso m :=
  monic_cover_iso m (monic_epic_is_cover m hm hepi) hm

theorem cover_eq_epic_preTopos [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞] {A B : 𝒞}
    (f : A ⟶ B) :
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

/-- **§1.652**: In a pre-topos, monics coincide with cocovers.

    A *cocover* is the dual of a cover: a regular mono = the equalizer of some parallel pair.
    Freyd's argument (§1.652) is: given a monic `x : A ↣ B`, form its cokernel pair `y, z : B ⇉ C`
    (so `x ≫ y = x ≫ z`); then "`x` is an equalizer of `y, z`, hence a cocover."  The amalgamation
    lemma §1.651 makes the cokernel-pair square `(A; x, x)` a *pullback*, and a pullback of `(y, z)`
    whose two legs coincide is exactly an equalizer of `(y, z)`.

    STATEMENT REDRAFT (the previous `HEq` encoding was a defect):
    the old form `∃ C p q, HEq ((coeq p q).map) f` is unprovable.  `HEq` between
    `(coeq p q).map : C ⟶ (coeq p q).obj` and `f : A ⟶ B` forces the *objects* `(coeq p q).obj` and
    `B` to be heterogeneously equal — but a (co)limit object is only ever *isomorphic* to `B`, never
    definitionally equal.  So forward would need an arbitrary mono's witness object to be defeq to
    `B`, and reverse would make a cover (coequalizer-map) monic.  The faithful statement, matching
    "`x` is an equalizer of `y, z`", is: `f` is monic iff `f` is the equalizer of some parallel pair
    `p, q : B ⇉ C` out of its codomain (predicate `EqualizerCone.IsEqualizer`, choice-free, with no
    object collapse).  This is precisely the book's "monics coincide with cocovers (= regular
    monos)".  The extra `[PreToposDisjoint]`/`[HasReflTransClosure]` instances are the same ambient
    pre-topos data §1.651 uses for the amalgamation pullback. -/
theorem monic_eq_cocover_preTopos [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞] {A B : 𝒞}
    (f : A ⟶ B) :
    Monic f ↔ ∃ (C : 𝒞) (p q : B ⟶ C) (h : f ≫ p = f ≫ q),
      (EqualizerCone.mk A f h).IsEqualizer := by
  constructor
  · -- FORWARD: a monic is the equalizer of its cokernel pair (§1.651 makes the square a pullback).
    intro hf
    obtain ⟨D, u, v, hsq, hpb, _, _⟩ := amalgamation_is_pullback f hf f hf
    refine ⟨D, u, v, hsq, ?_⟩
    -- The pullback cone of `(u, v)` is `(A; f, f)`; convert its UMP into the equalizer UMP of `(u,v)`.
    intro d
    -- `d : EqualizerCone u v` gives a cone over the cospan `(u, v)` with both legs `d.map`.
    obtain ⟨w, ⟨hw₁, _⟩, huniq⟩ := hpb (Cone.mk d.dom d.map d.map d.eq)
    refine ⟨w, hw₁, ?_⟩
    intro v' hv'
    exact huniq v' hv' hv'
  · -- REVERSE: an equalizer map is monic (two factors of the same cone are equal by uniqueness).
    rintro ⟨C, p, q, h, heq⟩ W g₁ g₂ hg
    -- `g₁, g₂ : W ⟶ A` with `g₁ ≫ f = g₂ ≫ f`; both equalize `(p, q)` via `f`, so both lift the
    -- equalizer cone `(W, g₁ ≫ f)` and are forced equal by uniqueness of the equalizer factor.
    have hk : (g₁ ≫ f) ≫ p = (g₁ ≫ f) ≫ q := by rw [Cat.assoc, Cat.assoc, h]
    obtain ⟨_, _, huniq⟩ := heq (EqualizerCone.mk W (g₁ ≫ f) hk)
    rw [huniq g₁ rfl, huniq g₂ hg.symm]

/-! ## §1.653 Pushout of a monic and any morphism in a pre-topos

  Given morphisms f: A → B and monic y: A ↣ C in a pre-topos, there is a pushout
  square with the top map monic.  The proof factors f as cover ∘ monic (image
  factorization) and applies the amalgamation lemma §1.651 to the two monics. -/

/-- Composition membership: a point `k` whose images sit in `R` (over `(α, m)`) and in `S`
    (over `(m, γ)`) yields a point of `R ⊚ S` over `(α, γ)`.  The shared midpoint `m` matches
    the two columns at the pullback, and the span factors through the composition image. -/
private theorem pair_mem_compose [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A B C K : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C)
    {α : K ⟶ A} {m : K ⟶ B} {γ : K ⟶ C}
    (p : K ⟶ R.src) (hpA : p ≫ R.colA = α) (hpB : p ≫ R.colB = m)
    (q : K ⟶ S.src) (hqA : q ≫ S.colA = m) (hqB : q ≫ S.colB = γ) :
    ∃ g : K ⟶ (R ⊚ S).src, g ≫ (R ⊚ S).colA = α ∧ g ≫ (R ⊚ S).colB = γ := by
  let pb := HasPullbacks.has R.colB S.colA
  have hcompat : p ≫ R.colB = q ≫ S.colA := by rw [hpB, hqA]
  let z : K ⟶ pb.cone.pt := pb.lift ⟨K, p, q, hcompat⟩
  have hz1 : z ≫ pb.cone.π₁ = p := pb.lift_fst _
  have hz2 : z ≫ pb.cone.π₂ = q := pb.lift_snd _
  let spanRS : pb.cone.pt ⟶ prod A C :=
    pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)
  -- z ≫ spanRS = pair α γ.
  have hzs : z ≫ spanRS = pair α γ := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, hz1, hpA]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, hz2, hqB]
  -- (R⊚S).src = (image spanRS).dom; its arr = pair (R⊚S).colA (R⊚S).colB.
  refine ⟨z ≫ image.lift spanRS, ?_, ?_⟩
  · show (z ≫ image.lift spanRS) ≫ ((image spanRS).arr ≫ fst) = α
    rw [Cat.assoc, ← Cat.assoc (image.lift spanRS), image.lift_fac, ← Cat.assoc, hzs, fst_pair]
  · show (z ≫ image.lift spanRS) ≫ ((image spanRS).arr ≫ snd) = γ
    rw [Cat.assoc, ← Cat.assoc (image.lift spanRS), image.lift_fac, ← Cat.assoc, hzs, snd_pair]

/-- **§1.653 (cover transport)**: given a cover `e : A ↠ I` and a monic `y : A ↣ C`,
    push `y` along `e` to a monic `y' : I ↣ C'` over a fresh codomain `C'`, with a
    comparison cover `c' : C ↠ C'` making the square commute (`e ≫ y' = y ≫ c'`).
    Freyd's construction (§1.653): on `C` form `R₀ := y° (level e) y` (the image, under
    `y`, of the kernel-pair relation of `e`), generate the equivalence relation
    `E' := Δ_C ∪ R₀`, and let `c' : C ↠ C'` be its effective quotient.  Then `level e =
    level (y ≫ c')`, so `y ≫ c'` coequalizes the kernel pair of `e` (gives `y'`), and
    `y'` is monic because `level (y ≫ c') ⊂ Δ_I`. -/
private theorem cover_transport_mono [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]
    {A I C : 𝒞} (e : A ⟶ I) (he : Cover e) (y : A ⟶ C) (hy : Monic y) :
    ∃ (C' : 𝒞) (y' : I ⟶ C') (c' : C ⟶ C'), Monic y' ∧ e ≫ y' = y ≫ c' := by
  -- E = level e = graph e ⊚ (graph e)° on A; R₀ = (graph y)° ⊚ E ⊚ graph y on C.
  let E : BinRel 𝒞 A A := graph e ⊚ (graph e)°
  let R₀ : BinRel 𝒞 C C := ((graph y)° ⊚ E) ⊚ graph y
  -- E is symmetric (E° = E) and transitive (E ⊚ E ⊂ E, from kernelPair transitivity).
  have hEsym : RelLe (E°) E := by
    have h1 : RelLe (E°) ((graph e)°° ⊚ (graph e)°) := reciprocal_comp_le (graph e) ((graph e)°)
    rw [reciprocal_invol] at h1; exact h1
  have hEsym' : RelLe E (E°) := by
    have h2 := reciprocal_mono hEsym; rwa [reciprocal_invol] at h2
  have hEtrans : RelLe (E ⊚ E) E := by
    have h1 : RelLe (kernelPairRel e) E := kernelPairRel_le_graphComp e
    have h2 : RelLe E (kernelPairRel e) := graphComp_le_kernelPairRel e
    have h3 : RelLe (E ⊚ E) (kernelPairRel e ⊚ kernelPairRel e) := compose_le h2 h2
    exact rel_le_trans h3 (rel_le_trans (kernelPair_transitive e) h1)
  -- y ⊚ y° ⊂ 1  (y monic).
  have hyy : RelLe (graph y ⊚ (graph y)°) (graph (Cat.id A)) :=
    graph_comp_recip_le_one_of_mono y hy
  -- R₀ symmetric:  R₀° ⊂ y° ⊚ (E° ⊚ y) ⊂ y° ⊚ (E ⊚ y) reassociated to (y° ⊚ E) ⊚ y = R₀.
  have hR₀sym : RelLe (R₀°) R₀ := by
    have s1 : RelLe (R₀°) ((graph y)° ⊚ ((graph y)° ⊚ E)°) :=
      reciprocal_comp_le ((graph y)° ⊚ E) (graph y)
    have s2 : RelLe (((graph y)° ⊚ E)°) (E° ⊚ (graph y)°°) :=
      reciprocal_comp_le ((graph y)°) E
    have s2' : RelLe (E° ⊚ (graph y)°°) (E ⊚ graph y) := by
      rw [reciprocal_invol]; exact compose_le hEsym (rel_le_refl _)
    have s3 : RelLe ((graph y)° ⊚ ((graph y)° ⊚ E)°) ((graph y)° ⊚ (E ⊚ graph y)) :=
      compose_le (rel_le_refl _) (rel_le_trans s2 s2')
    have s4 : RelLe ((graph y)° ⊚ (E ⊚ graph y)) (((graph y)° ⊚ E) ⊚ graph y) :=
      (compose_assoc_of_regular ((graph y)°) E (graph y)).2
    exact rel_le_trans s1 (rel_le_trans s3 s4)
  -- R₀ transitive:  reassociate R₀⊚R₀ = (y°E) ⊚ ((y⊚y°) ⊚ (E y)); kill y⊚y° ⊂ 1, then E⊚E ⊂ E.
  have hR₀trans : RelLe (R₀ ⊚ R₀) R₀ := by
    -- Abbreviations matching `R₀ = ((y°⊚E)⊚y)`.
    let yo : BinRel 𝒞 C A := (graph y)°
    let gy : BinRel 𝒞 A C := graph y
    -- Step A: ((yo⊚E)⊚gy) ⊚ R₀  ⊂  (yo⊚E) ⊚ (gy ⊚ R₀).
    have a1 : RelLe (R₀ ⊚ R₀) ((yo ⊚ E) ⊚ (gy ⊚ R₀)) :=
      (compose_assoc_of_regular (yo ⊚ E) gy R₀).1
    -- Step B: gy ⊚ R₀ = gy ⊚ ((yo⊚E)⊚gy) ⊂ (gy ⊚ (yo⊚E)) ⊚ gy ⊂ ((gy⊚yo)⊚E) ⊚ gy.
    have b1 : RelLe (gy ⊚ R₀) ((gy ⊚ (yo ⊚ E)) ⊚ gy) :=
      (compose_assoc_of_regular gy (yo ⊚ E) gy).2
    have b2 : RelLe (gy ⊚ (yo ⊚ E)) ((gy ⊚ yo) ⊚ E) :=
      (compose_assoc_of_regular gy yo E).2
    have b3 : RelLe ((gy ⊚ yo) ⊚ E) (graph (Cat.id A) ⊚ E) := compose_le hyy (rel_le_refl _)
    have b4 : RelLe (graph (Cat.id A) ⊚ E) E := graph_id_comp E
    have b5 : RelLe (gy ⊚ R₀) (E ⊚ gy) :=
      rel_le_trans b1 (compose_le (rel_le_trans b2 (rel_le_trans b3 b4)) (rel_le_refl _))
    -- Step C: (yo⊚E) ⊚ (E⊚gy) ⊂ yo ⊚ ((E⊚E)⊚gy) ⊂ yo ⊚ (E⊚gy) ⊂ (yo⊚E)⊚gy = R₀.
    have c1 : RelLe ((yo ⊚ E) ⊚ (gy ⊚ R₀)) ((yo ⊚ E) ⊚ (E ⊚ gy)) :=
      compose_le (rel_le_refl _) b5
    have c2 : RelLe ((yo ⊚ E) ⊚ (E ⊚ gy)) (yo ⊚ (E ⊚ (E ⊚ gy))) :=
      (compose_assoc_of_regular yo E (E ⊚ gy)).1
    have c3 : RelLe (E ⊚ (E ⊚ gy)) ((E ⊚ E) ⊚ gy) :=
      (compose_assoc_of_regular E E gy).2
    have c4 : RelLe ((E ⊚ E) ⊚ gy) (E ⊚ gy) := compose_le hEtrans (rel_le_refl _)
    have c5 : RelLe (yo ⊚ (E ⊚ (E ⊚ gy))) (yo ⊚ (E ⊚ gy)) :=
      compose_le (rel_le_refl _) (rel_le_trans c3 c4)
    have c6 : RelLe (yo ⊚ (E ⊚ gy)) ((yo ⊚ E) ⊚ gy) :=
      (compose_assoc_of_regular yo E gy).2
    exact rel_le_trans a1 (rel_le_trans c1 (rel_le_trans c2 (rel_le_trans c5 c6)))
  -- E' := Δ_C ∪ R₀ is an equivalence relation.
  let Δ : BinRel 𝒞 C C := graph (Cat.id C)
  let E' : BinRel 𝒞 C C := Δ ∪ᵣ R₀
  have hΔE' : RelLe Δ E' := relUnion_le_left Δ R₀
  have hRE' : RelLe R₀ E' := relUnion_le_right Δ R₀
  have hE'eq : EquivalenceRelation E' := by
    apply equivalenceRelation_of_isEquivRel
    refine ⟨?_, ?_, ?_⟩
    · -- reflexivity: graph(id) ⊂ E'.
      exact hΔE'
    · -- symmetry: E'° ⊂ E'  (distribute ° over ∪, Δ° ⊂ Δ, R₀° ⊂ R₀).
      refine rel_le_trans (relUnion_le_reciprocal Δ R₀) ?_
      apply le_relUnion
      · exact rel_le_trans hR₀sym hRE'
      · -- Δ° ⊂ Δ ⊂ E'.
        have h0 : RelLe (Δ°) (Δ°°) := reciprocal_mono graph_id_le_reciprocal
        rw [reciprocal_invol] at h0
        exact rel_le_trans h0 hΔE'
    · -- transitivity: E'⊚E' ⊂ E'  (four pieces ΔΔ, ΔR₀, R₀Δ, R₀R₀).
      refine rel_le_trans (compose_union_left Δ R₀ E') ?_
      apply le_relUnion
      · -- Δ ⊚ E' ⊂ E'.
        exact graph_id_comp E'
      · -- R₀ ⊚ E' = R₀ ⊚ (Δ ∪ R₀) ⊂ (R₀⊚Δ) ∪ (R₀⊚R₀) ⊂ E'.
        refine rel_le_trans (compose_union_right R₀ Δ R₀) ?_
        apply le_relUnion
        · exact rel_le_trans (comp_graph_id R₀) hRE'
        · exact rel_le_trans hR₀trans hRE'
  -- Effective quotient: cover c' : C ↠ C' with level c' = E' (both directions).
  obtain ⟨_, C', c', hc'cov, hle, hge⟩ := EffectiveRegular.effective E' hE'eq
  -- hle : E' ⊂ graph c' ⊚ (graph c')°   ;   hge : graph c' ⊚ (graph c')° ⊂ E'.
  -- ===== level e = level (y ≫ c'), giving y' and its monicity. =====
  -- (1) y ≫ c' coequalizes the kernel pair of e:  e's two preimages get identified by c'.
  -- R₀ = y°(level e)y ⊂ E' ⊂ level c', so y maps level-e-related points to c'-equal points.
  have hkpe_g : kp₁ (f := e) ≫ (y ≫ c') = kp₂ (f := e) ≫ (y ≫ c') := by
    -- The kernel-pair span (kp₁, kp₂) of `e` sits inside `E = level e` (via kernelPairRel ⊂ E).
    have hkpE : RelLe (kernelPairRel e) E := kernelPairRel_le_graphComp e
    obtain ⟨⟨w, hwA, hwB⟩⟩ := hkpE
    -- w : kernelPair e → E.src with w ≫ E.colA = kp₁, w ≫ E.colB = kp₂.
    have hwA' : w ≫ E.colA = kp₁ (f := e) := by simpa [kernelPairRel] using hwA
    have hwB' : w ≫ E.colB = kp₂ (f := e) := by simpa [kernelPairRel] using hwB
    -- R₀ ⊂ E' ⊂ level c' ⊂ kernelPairRel c'.
    have hR₀kp : RelLe R₀ (kernelPairRel c') :=
      rel_le_trans (rel_le_trans hRE' hle) (graphComp_le_kernelPairRel c')
    -- P-witness over (kp₁≫y, kp₂):  p = kp₁ into (graph y)°, q = w into E.
    obtain ⟨pP, hpPA, hpPB⟩ := pair_mem_compose ((graph y)°) E
      (α := kp₁ (f := e) ≫ y) (m := kp₁ (f := e)) (γ := kp₂ (f := e))
      (kp₁ (f := e)) (by show kp₁ (f := e) ≫ y = _; rfl)
        (by show kp₁ (f := e) ≫ Cat.id A = _; rw [Cat.comp_id])
      w hwA' hwB'
    -- R₀-witness over (kp₁≫y, kp₂≫y):  p = pP into P, q = kp₂ into graph y.
    obtain ⟨g, hgA, hgB⟩ := pair_mem_compose ((graph y)° ⊚ E) (graph y)
      (α := kp₁ (f := e) ≫ y) (m := kp₂ (f := e)) (γ := kp₂ (f := e) ≫ y)
      pP hpPA hpPB
      (kp₂ (f := e)) (by show kp₂ (f := e) ≫ Cat.id A = _; rw [Cat.comp_id])
        (by show kp₂ (f := e) ≫ y = _; rfl)
    -- Transport g through R₀ ⊂ kernelPairRel c'.
    obtain ⟨⟨h, hhA, hhB⟩⟩ := hR₀kp
    -- (g≫h) lands in kernelPair c' with legs kp₁≫y, kp₂≫y; kp_sq closes after c'.
    have ek1 : (g ≫ h) ≫ kp₁ (f := c') = kp₁ (f := e) ≫ y := by
      rw [Cat.assoc]; show g ≫ (h ≫ (kernelPairRel c').colA) = _
      rw [hhA]; exact hgA
    have ek2 : (g ≫ h) ≫ kp₂ (f := c') = kp₂ (f := e) ≫ y := by
      rw [Cat.assoc]; show g ≫ (h ≫ (kernelPairRel c').colB) = _
      rw [hhB]; exact hgB
    calc kp₁ (f := e) ≫ (y ≫ c')
        = (kp₁ (f := e) ≫ y) ≫ c' := (Cat.assoc _ _ _).symm
      _ = ((g ≫ h) ≫ kp₁ (f := c')) ≫ c' := by rw [ek1]
      _ = (g ≫ h) ≫ (kp₁ (f := c') ≫ c') := Cat.assoc _ _ _
      _ = (g ≫ h) ≫ (kp₂ (f := c') ≫ c') := by rw [kp_sq]
      _ = ((g ≫ h) ≫ kp₂ (f := c')) ≫ c' := (Cat.assoc _ _ _).symm
      _ = (kp₂ (f := e) ≫ y) ≫ c' := by rw [ek2]
      _ = kp₂ (f := e) ≫ (y ≫ c') := Cat.assoc _ _ _
  obtain ⟨y', hy'fac, _⟩ := cover_is_coequalizer_of_level e he (y ≫ c') hkpe_g
  -- (2) y' is monic.  First: level (y≫c') ⊂ E = level e (the reverse containment).
  --     graph(y≫c')⊚graph(y≫c')° ⊂ y ⊚ (level c') ⊚ y° ⊂ y ⊚ (Δ_C ∪ R₀) ⊚ y° ⊂ E.
  have hge2 : RelLe (graph (y ≫ c') ⊚ (graph (y ≫ c'))°) E := by
    have gc : RelLe (graph (y ≫ c')) (graph y ⊚ graph c') := graph_comp y c'
    have gcr : RelLe ((graph (y ≫ c'))°) ((graph c')° ⊚ (graph y)°) :=
      rel_le_trans (reciprocal_mono gc) (reciprocal_comp_le (graph y) (graph c'))
    have t1 : RelLe (graph (y ≫ c') ⊚ (graph (y ≫ c'))°)
        ((graph y ⊚ graph c') ⊚ ((graph c')° ⊚ (graph y)°)) := compose_le gc gcr
    -- reassociate to graph y ⊚ ((graph c' ⊚ graph c'°) ⊚ graph y°).
    have t2 : RelLe ((graph y ⊚ graph c') ⊚ ((graph c')° ⊚ (graph y)°))
        (graph y ⊚ (graph c' ⊚ ((graph c')° ⊚ (graph y)°))) :=
      (compose_assoc_of_regular (graph y) (graph c') ((graph c')° ⊚ (graph y)°)).1
    have t3 : RelLe (graph c' ⊚ ((graph c')° ⊚ (graph y)°))
        ((graph c' ⊚ (graph c')°) ⊚ (graph y)°) :=
      (compose_assoc_of_regular (graph c') ((graph c')°) ((graph y)°)).2
    have t4 : RelLe (graph y ⊚ (graph c' ⊚ ((graph c')° ⊚ (graph y)°)))
        (graph y ⊚ ((graph c' ⊚ (graph c')°) ⊚ (graph y)°)) :=
      compose_le (rel_le_refl _) t3
    -- graph c' ⊚ graph c'° ⊂ E' = Δ_C ∪ R₀ (effectiveness reverse bound).
    have t5 : RelLe (graph y ⊚ ((graph c' ⊚ (graph c')°) ⊚ (graph y)°))
        (graph y ⊚ ((Δ ∪ᵣ R₀) ⊚ (graph y)°)) :=
      compose_le (rel_le_refl _) (compose_le hge (rel_le_refl _))
    -- distribute the union: graph y ⊚ ((Δ ∪ R₀) ⊚ y°) ⊂ (y⊚(Δ⊚y°)) ∪ (y⊚(R₀⊚y°)).
    have t6 : RelLe (graph y ⊚ ((Δ ∪ᵣ R₀) ⊚ (graph y)°))
        ((graph y ⊚ (Δ ⊚ (graph y)°)) ∪ᵣ (graph y ⊚ (R₀ ⊚ (graph y)°))) := by
      refine rel_le_trans (compose_le (rel_le_refl _) (compose_union_left Δ R₀ ((graph y)°))) ?_
      exact compose_union_right (graph y) (Δ ⊚ (graph y)°) (R₀ ⊚ (graph y)°)
    -- piece 1:  y ⊚ (Δ_C ⊚ y°) ⊂ y ⊚ y° ⊂ 1_A ⊂ E.
    have hΔE : RelLe (graph (Cat.id A)) E :=
      rel_le_trans
        (show RelLe (graph (Cat.id A)) (kernelPairRel e) from
          ⟨⟨kp_diag (f := e), by simpa [kernelPairRel, graph] using kp_diag_p₁ (f := e),
            by simpa [kernelPairRel, graph] using kp_diag_p₂ (f := e)⟩⟩)
        (kernelPairRel_le_graphComp e)
    have p1 : RelLe (graph y ⊚ (Δ ⊚ (graph y)°)) E :=
      rel_le_trans (compose_le (rel_le_refl _) (graph_id_comp ((graph y)°)))
        (rel_le_trans hyy hΔE)
    -- piece 2:  y ⊚ (R₀ ⊚ y°) = y ⊚ (((y°⊚E)⊚y) ⊚ y°);  collapse y⊚y° ⊂ 1 on both ends.
    have p2 : RelLe (graph y ⊚ (R₀ ⊚ (graph y)°)) E := by
      -- R₀ ⊚ y° = ((y°⊚E)⊚y) ⊚ y° ⊂ (y°⊚E) ⊚ (y⊚y°) ⊂ (y°⊚E) ⊚ 1 ⊂ y°⊚E.
      have q1 : RelLe (R₀ ⊚ (graph y)°) (((graph y)° ⊚ E) ⊚ (graph y ⊚ (graph y)°)) :=
        (compose_assoc_of_regular ((graph y)° ⊚ E) (graph y) ((graph y)°)).1
      have q2 : RelLe (((graph y)° ⊚ E) ⊚ (graph y ⊚ (graph y)°))
          (((graph y)° ⊚ E) ⊚ graph (Cat.id A)) :=
        compose_le (rel_le_refl _) hyy
      have q3 : RelLe (((graph y)° ⊚ E) ⊚ graph (Cat.id A)) ((graph y)° ⊚ E) :=
        comp_graph_id ((graph y)° ⊚ E)
      have qR : RelLe (R₀ ⊚ (graph y)°) ((graph y)° ⊚ E) :=
        rel_le_trans q1 (rel_le_trans q2 q3)
      -- y ⊚ (R₀ ⊚ y°) ⊂ y ⊚ (y°⊚E) ⊂ (y⊚y°)⊚E ⊂ 1⊚E ⊂ E.
      have q4 : RelLe (graph y ⊚ (R₀ ⊚ (graph y)°)) (graph y ⊚ ((graph y)° ⊚ E)) :=
        compose_le (rel_le_refl _) qR
      have q5 : RelLe (graph y ⊚ ((graph y)° ⊚ E)) ((graph y ⊚ (graph y)°) ⊚ E) :=
        (compose_assoc_of_regular (graph y) ((graph y)°) E).2
      have q6 : RelLe ((graph y ⊚ (graph y)°) ⊚ E) (graph (Cat.id A) ⊚ E) :=
        compose_le hyy (rel_le_refl _)
      exact rel_le_trans q4 (rel_le_trans q5 (rel_le_trans q6 (graph_id_comp E)))
    have t7 : RelLe ((graph y ⊚ (Δ ⊚ (graph y)°)) ∪ᵣ (graph y ⊚ (R₀ ⊚ (graph y)°))) E :=
      le_relUnion p1 p2
    exact rel_le_trans t1 (rel_le_trans t2 (rel_le_trans t4
      (rel_le_trans t5 (rel_le_trans t6 t7))))
  -- level (y≫c') ⊂ E ⊂ kernelPairRel e.
  have hkp_le : RelLe (kernelPairRel (y ≫ c')) (kernelPairRel e) :=
    rel_le_trans (kernelPairRel_le_graphComp (y ≫ c'))
      (rel_le_trans hge2 (graphComp_le_kernelPairRel e))
  -- Monic y':  pull the cover `e` back along any pair `u,v : W → I` with `u≫y' = v≫y'`.
  have hy'mono : Monic y' := by
    intro W u v huv
    -- pull cover e back along u, then along (that pullback ≫ v).
    let pb1 := HasPullbacks.has e u
    have hπ₂u_cover : Cover pb1.cone.π₂ := cover_pullback u he
    let pb2 := HasPullbacks.has e (pb1.cone.π₂ ≫ v)
    have hρ_cover : Cover pb2.cone.π₂ := cover_pullback (pb1.cone.π₂ ≫ v) he
    let c := pb2.cone.π₂ ≫ pb1.cone.π₂
    let au := pb2.cone.π₂ ≫ pb1.cone.π₁
    let av := pb2.cone.π₁
    have hau_e : au ≫ e = c ≫ u := by
      dsimp only [au, c]; rw [Cat.assoc, pb1.cone.w, ← Cat.assoc]
    have hav_e : av ≫ e = c ≫ v := by
      dsimp only [av, c]; rw [pb2.cone.w, ← Cat.assoc]
    -- au, av agree after y≫c' (= e≫y'), so land in kernelPair (y≫c').
    have hag : au ≫ (y ≫ c') = av ≫ (y ≫ c') := by
      calc au ≫ (y ≫ c') = au ≫ (e ≫ y') := by rw [hy'fac]
        _ = (au ≫ e) ≫ y' := (Cat.assoc _ _ _).symm
        _ = (c ≫ u) ≫ y' := by rw [hau_e]
        _ = c ≫ (u ≫ y') := Cat.assoc _ _ _
        _ = c ≫ (v ≫ y') := by rw [huv]
        _ = (c ≫ v) ≫ y' := (Cat.assoc _ _ _).symm
        _ = (av ≫ e) ≫ y' := by rw [hav_e]
        _ = av ≫ (e ≫ y') := Cat.assoc _ _ _
        _ = av ≫ (y ≫ c') := by rw [hy'fac]
    -- (au, av) ∈ kernelPairRel (y≫c') ⊂ kernelPairRel e, so au ≫ e = av ≫ e.
    let l := (HasPullbacks.has (y ≫ c') (y ≫ c')).lift ⟨_, au, av, hag⟩
    have hl1 : l ≫ kp₁ (f := y ≫ c') = au := kp_lift_p₁ au av hag
    have hl2 : l ≫ kp₂ (f := y ≫ c') = av := kp_lift_p₂ au av hag
    obtain ⟨⟨t, htA, htB⟩⟩ := hkp_le
    have hae : au ≫ e = av ≫ e := by
      have ha : (l ≫ t) ≫ kp₁ (f := e) = au := by
        rw [Cat.assoc]; show l ≫ (t ≫ (kernelPairRel e).colA) = au
        rw [htA]; show l ≫ (kernelPairRel (y ≫ c')).colA = au; exact hl1
      have hb : (l ≫ t) ≫ kp₂ (f := e) = av := by
        rw [Cat.assoc]; show l ≫ (t ≫ (kernelPairRel e).colB) = av
        rw [htB]; show l ≫ (kernelPairRel (y ≫ c')).colB = av; exact hl2
      calc au ≫ e = ((l ≫ t) ≫ kp₁ (f := e)) ≫ e := by rw [ha]
        _ = (l ≫ t) ≫ (kp₁ (f := e) ≫ e) := Cat.assoc _ _ _
        _ = (l ≫ t) ≫ (kp₂ (f := e) ≫ e) := by rw [kp_sq]
        _ = ((l ≫ t) ≫ kp₂ (f := e)) ≫ e := (Cat.assoc _ _ _).symm
        _ = av ≫ e := by rw [hb]
    -- au≫e = av≫e ⟹ c≫u = c≫v ⟹ u = v (cancel the two covers).
    have hcuv : c ≫ u = c ≫ v := by rw [← hau_e, ← hav_e, hae]
    -- c = pb2.π₂ ≫ pb1.π₂; cancel pb2.π₂ to get pb1.π₂≫u = pb1.π₂≫v, then cancel pb1.π₂.
    apply cover_epi hπ₂u_cover
    apply cover_epi hρ_cover
    show pb2.cone.π₂ ≫ (pb1.cone.π₂ ≫ u) = pb2.cone.π₂ ≫ (pb1.cone.π₂ ≫ v)
    rw [← Cat.assoc, ← Cat.assoc]; exact hcuv
  exact ⟨C', y', c', hy'mono, hy'fac⟩

/-! ## §1.653 Pushout of a monic and any morphism in a pre-topos (assembly)

  Given morphisms f: A → B and monic y: A ↣ C in a pre-topos, there is a pushout
  square with the top map monic.  The proof factors f as cover ∘ monic (image
  factorization) and applies the amalgamation lemma §1.651 to the two monics. -/

/-- **§1.653**: In a pre-topos, given f : A → B and monic y : A ↣ C, there exists a
    pushout square (with the B-map monic).
    PROOF: Factor A → B as A ↠ I ↣ B (image factorization, `e := image.lift f`, `i :=
    (image f).arr`).  Transport `y` along the cover `e` to a monic `y' : I ↣ C'` with a
    comparison cover `c' : C ↠ C'` (`cover_transport_mono`), giving `e ≫ y' = y ≫ c'`.
    Apply the amalgamation lemma §1.651 to the two monics `i : I ↣ B` and `y' : I ↣ C',
    yielding monics `u : B ↣ D`, `w : C' ↣ D` with `i ≫ u = y' ≫ w`.  The pushout square is
    `(u, c' ≫ w)`: `f ≫ u = e ≫ i ≫ u = e ≫ y' ≫ w = y ≫ c' ≫ w`. -/
theorem pushout_monic_in_pretopos [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]
    {A B C : 𝒞}
    (f : A ⟶ B) (y : A ⟶ C) (hy : Monic y) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D), Monic u ∧ f ≫ u = y ≫ v := by
  -- Image factorization of f:  e : A ↠ I (cover),  i : I ↣ B (monic),  e ≫ i = f.
  let e : A ⟶ (image f).dom := image.lift f
  let i : (image f).dom ⟶ B := (image f).arr
  have he : Cover e := image_lift_cover f
  have hi : Monic i := (image f).monic
  have hei : e ≫ i = f := image.lift_fac f
  -- Transport y along the cover e to a monic y' : I ↣ C', with comparison cover c'.
  obtain ⟨C', y', c', hy', hsq⟩ := cover_transport_mono e he y hy
  -- Amalgamate the two monics i : I ↣ B and y' : I ↣ C'.
  obtain ⟨D, u, w, hu, _hw, hiu⟩ := amalgamation_lemma i hi y' hy'
  -- The pushout square:  u : B ↣ D (monic),  v := c' ≫ w : C → D.
  refine ⟨D, u, c' ≫ w, hu, ?_⟩
  calc f ≫ u = (e ≫ i) ≫ u := by rw [hei]
    _ = e ≫ (i ≫ u) := Cat.assoc _ _ _
    _ = e ≫ (y' ≫ w) := by rw [hiu]
    _ = (e ≫ y') ≫ w := (Cat.assoc _ _ _).symm
    _ = (y ≫ c') ≫ w := by rw [hsq]
    _ = y ≫ (c' ≫ w) := Cat.assoc _ _ _

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

/-- **§1.658 (engine, sharpened)**: a subobject `S ⊆ B` is complemented as soon as ITS OWN
    amalgamation `D = B +_S B` is decidable.  Identical body to `subobject_complemented_of_decidable`
    except the decidability of `D` is taken as a hypothesis (`hD`) rather than from a global
    `∀ A, DecidableObject A`.  This is the form needed inside a slice where only `1_𝒮+1_𝒮` (and
    thence the specific amalgam) is known decidable.  The classifier `c := pair u v` makes
    `S = c#(Δ D)` (`hS₁`/`hS₂`), and `diagonal_classifies hD` + the bridge finish. -/
theorem subobject_complemented_of_amalg_decidable [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]
    {B : 𝒞} (S : Subobject 𝒞 B) {D : 𝒞} {u v : B ⟶ D} (hsq : S.arr ≫ u = S.arr ≫ v)
    (hpb : (Cone.mk (f := u) (g := v) S.dom S.arr S.arr hsq).IsPullback)
    (hD : DecidableObjectSub D) :
    IsComplemented S := by
  let c : B ⟶ prod D D := pair u v
  -- The chosen pullback computing `c # (Δ D)`.
  let pb := HasPullbacks.has c (diagSub D).arr
  -- `S ≤ c#(Δ D)`: `S.arr ≫ c` factors through `Δ D` via `S.arr ≫ u` (square commutes).
  have hS₁ : S.le (InverseImage c (diagSub D)) := by
    have hw : S.arr ≫ c = (S.arr ≫ u) ≫ (diagSub D).arr := by
      show S.arr ≫ pair u v = (S.arr ≫ u) ≫ diag D
      -- compare projections: fst both give `S.arr ≫ u`; snd give `S.arr ≫ v` vs `S.arr ≫ u`.
      have e1 : (S.arr ≫ pair u v) ≫ fst = ((S.arr ≫ u) ≫ diag D) ≫ fst := by
        rw [Cat.assoc, fst_pair, Cat.assoc, diag_fst, Cat.comp_id]
      have e2 : (S.arr ≫ pair u v) ≫ snd = ((S.arr ≫ u) ≫ diag D) ≫ snd := by
        rw [Cat.assoc, snd_pair, Cat.assoc, diag_snd, Cat.comp_id, ← hsq]
      calc S.arr ≫ pair u v
          = pair ((S.arr ≫ pair u v) ≫ fst) ((S.arr ≫ pair u v) ≫ snd) := pair_eta _
        _ = pair (((S.arr ≫ u) ≫ diag D) ≫ fst) (((S.arr ≫ u) ≫ diag D) ≫ snd) := by rw [e1, e2]
        _ = (S.arr ≫ u) ≫ diag D := (pair_eta _).symm
    let d : Cone c (diagSub D).arr := ⟨S.dom, S.arr, S.arr ≫ u, hw⟩
    exact ⟨pb.lift d, pb.lift_fst d⟩
  -- `c#(Δ D) ≤ S`: pullback `pt = {b : u b = v b}`; the IsPullback of the amalgamation square
  -- factors any such `b` through `S.arr`.
  have hS₂ : (InverseImage c (diagSub D)).le S := by
    -- `π₁ ≫ u = π₂ = π₁ ≫ v` from the pullback square `π₁ ≫ c = π₂ ≫ Δ D`, by post-fst/snd.
    have hw : pb.cone.π₁ ≫ c = pb.cone.π₂ ≫ diag D := pb.cone.w
    have hfst : pb.cone.π₁ ≫ u = pb.cone.π₂ := by
      calc pb.cone.π₁ ≫ u
          = (pb.cone.π₁ ≫ c) ≫ fst := by rw [Cat.assoc, fst_pair]
        _ = (pb.cone.π₂ ≫ diag D) ≫ fst := by rw [hw]
        _ = pb.cone.π₂ := by rw [Cat.assoc, diag_fst (A := D)]; exact Cat.comp_id _
    have hsnd : pb.cone.π₁ ≫ v = pb.cone.π₂ := by
      calc pb.cone.π₁ ≫ v
          = (pb.cone.π₁ ≫ c) ≫ snd := by rw [Cat.assoc, snd_pair]
        _ = (pb.cone.π₂ ≫ diag D) ≫ snd := by rw [hw]
        _ = pb.cone.π₂ := by rw [Cat.assoc, diag_snd (A := D)]; exact Cat.comp_id _
    have heq : pb.cone.π₁ ≫ u = pb.cone.π₁ ≫ v := by rw [hfst, hsnd]
    obtain ⟨g, ⟨hg₁, _hg₂⟩, _⟩ := hpb ⟨pb.cone.pt, pb.cone.π₁, pb.cone.π₁, heq⟩
    exact ⟨g, hg₁⟩
  -- Assemble: `S` complemented (inter-form via `diagonal_classifies`, then the bridge back).
  exact (isComplemented_iff_sub S).mpr (diagonal_classifies hD c hS₁ hS₂)

/-- **§1.658 (engine)**: every subobject `S ⊆ B` is the inverse image of a DECIDABLE diagonal,
    hence complemented.  Thin caller of `subobject_complemented_of_amalg_decidable`: build the
    amalgamation `D := B +_S B` (`amalgamation_is_pullback`), decidable from the global `h`. -/
theorem subobject_complemented_of_decidable [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]
    (h : ∀ (A : 𝒞), DecidableObject A) {B : 𝒞} (S : Subobject 𝒞 B) :
    IsComplemented S := by
  obtain ⟨D, u, v, hsq, hpb, _hpush, _hcov⟩ :=
    amalgamation_is_pullback S.arr S.monic S.arr S.monic
  have hD : DecidableObjectSub D := (isComplemented_iff_sub (diagSub D)).mp (h D)
  exact subobject_complemented_of_amalg_decidable S hsq hpb hD

/-- **§1.658**: Every object in a pre-topos is decidable iff the pre-topos is boolean.
    The harder direction (all decidable → boolean) follows because pullbacks of
    complemented subobjects are complemented, and every subobject U ⊆ 1 can be
    pulled back to any slice, where it coincides with the diagonal. -/
theorem preTopos_boolean_iff_all_decidable [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞] :
    (Nonempty (BooleanPreLogos 𝒞)) ↔ ∀ (A : 𝒞), DecidableObject A := by
  refine ⟨fun ⟨hbool⟩ A => ?_, fun h => ?_⟩
  · -- (⇒) BooleanPreLogos → every diagonal subobject is complemented = DecidableObject A.
    -- The instance mismatch between hbool.toPreLogos and the ambient [PreLogos 𝒞] variable
    -- is resolved by using hbool's union_min to bridge to the ambient union.
    unfold DecidableObject IsComplemented
    -- Pin `prod A A`, `diag A` to the ambient `PreTopos` products (NOT `hbool`'s), so the
    -- complement `A₂` produced below lives in the same lattice the goal `DecidableObject A` uses.
    letI hP : HasBinaryProducts 𝒞 := PreTopos.toPositivePreLogos.toHasBinaryProducts
    let diagSub : Subobject 𝒞 (@prod 𝒞 _ hP A A) :=
      { dom := A, arr := @diag 𝒞 _ hP A, monic := @diag_mono 𝒞 _ hP A }
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
  · -- (⇐) All decidable → BooleanPreLogos.  Every subobject `S ⊆ B` is complemented via the
    -- amalgamation classifier `c = pair u v : B → D×D` for `D = B +_S B`:
    -- `subobject_complemented_of_decidable` packages the `S = c#(Δ D)` argument (using the
    -- `amalgamation_is_pullback` UMP) and the `diagonal_classifies` + `isComplemented_iff_sub`
    -- discharge.  We construct `BooleanPreLogos` directly from `h` (no `hbool` in scope here,
    -- so no product-instance diamond).
    exact ⟨{ toPreLogos := PreTopos.toPositivePreLogos.toPreLogos
             hasComplement := fun {A} S => subobject_complemented_of_decidable h S }⟩

/-! ## §1.659 Decidability in functor categories and sheaves

  T ∈ Fᴬ is decidable iff T(x) is a monic map for all x : A → B ∈ A.
  For sheaves: X → Y is decidable iff every pair of points with the same
  stalk have disjoint neighborhoods; in particular, decidable iff Y is Hausdorff.
  (These results require the sheaf/functor-category infrastructure; not yet formalized.) -/

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
theorem subobject_of_choice_is_choice {A C : 𝒞} (m : A ⟶ C) (hm : Monic m)
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
    Sorry-free half of §1.661: the image relation
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
theorem entire_comp_graph {A B C : 𝒞} [PullbacksTransferCovers 𝒞]
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
theorem comp_recip_pin {A B C : 𝒞} (f : A ⟶ C) (p : B ⟶ C) :
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
theorem entire_refine {A B C : 𝒞} [PullbacksTransferCovers 𝒞]
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
    the §1.563 intersection-modular content, discharged here Sorry-free by `entire_refine`
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

/-- **Pinned-coordinate choice** (§1.661, the engine behind Diaconescu's slice step).
    Let `R : X → T×C` be entire whose `C`-coordinate is *pinned* to a map `p : X → C`:
    `R.colB ≫ snd = R.colA ≫ p`.  Then `Choice T` ALONE supplies a map `f : X → T×C`
    contained in `R` — no `Choice C`.  The pin forces the `C`-coordinate, so the relation
    `R₁ := ⟨R.colA, R.colB ≫ fst⟩ : X → T` (jointly monic precisely BECAUSE the `snd`-leg
    is determined by `colA ≫ p`) is entire, and `Choice T`'s single witness `w : X → R.src`
    already pairs the forced `snd`-coordinate into a full section.  This is exactly the
    coordinate at which `prod_choice_is_choice` used a second `Choice C` extraction; pinning
    replaces it. -/
theorem choice_prod_pinned [PullbacksTransferCovers 𝒞] {T C X : 𝒞}
    (hT : Choice T) (R : BinRel 𝒞 X (prod T C)) (hent : Entire R)
    (p : X ⟶ C) (hpin : R.colB ≫ snd = R.colA ≫ p) :
    ∃ (f : X ⟶ prod T C) (w : X ⟶ R.src),
      w ≫ R.colA = Cat.id X ∧ w ≫ R.colB = f := by
  -- R₁ := ⟨R.colA, R.colB ≫ fst⟩ : X → T.  Jointly monic: the fst-leg + the pinned snd-leg
  -- recover the full colB, then R.isMonicPair cancels.
  have hp₁ : MonicPair R.colA (R.colB ≫ fst) := by
    intro W u v hua hub
    have hsnd : (u ≫ R.colB) ≫ snd = (v ≫ R.colB) ≫ snd := by
      calc (u ≫ R.colB) ≫ snd = u ≫ (R.colB ≫ snd) := Cat.assoc _ _ _
        _ = u ≫ (R.colA ≫ p) := by rw [hpin]
        _ = (u ≫ R.colA) ≫ p := (Cat.assoc _ _ _).symm
        _ = (v ≫ R.colA) ≫ p := by rw [hua]
        _ = v ≫ (R.colA ≫ p) := Cat.assoc _ _ _
        _ = v ≫ (R.colB ≫ snd) := by rw [hpin]
        _ = (v ≫ R.colB) ≫ snd := (Cat.assoc _ _ _).symm
    have hfst : (u ≫ R.colB) ≫ fst = (v ≫ R.colB) ≫ fst := by
      rw [Cat.assoc, Cat.assoc]; exact hub
    have hcolB : u ≫ R.colB = v ≫ R.colB := by
      rw [pair_eta (u ≫ R.colB), pair_eta (v ≫ R.colB), hfst, hsnd]
    exact R.isMonicPair u v hua hcolB
  have hR_cov : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  let R₁ : BinRel 𝒞 X T := BinRel.mk R.src R.colA (R.colB ≫ fst) hp₁
  have hentR₁ : Entire R₁ :=
    (tabulated_is_entire_iff_left_cover R.colA (R.colB ≫ fst) hp₁).mpr hR_cov
  -- Choice T gives a single witness w : X → R.src with w ≫ R.colA = id and w ≫ R.colB ≫ fst = f₁.
  obtain ⟨_f₁, w, hwA, hwB⟩ := hT R₁ hentR₁
  -- The full map is f := w ≫ R.colB; its snd-coordinate is forced by the pin, fst by hwB.
  exact ⟨w ≫ R.colB, w, hwA, rfl⟩

end Choice661

/-! ## §1.662 Diaconescu's theorem in a pre-topos

  In a pre-topos, the following are equivalent:
  (1) Binary coproducts of choice objects are choice.
  (2) 1+1 is choice.
  (3) The pre-topos is boolean. -/

section Diaconescu

variable [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]

/-- **§1.662**: (1) → (2): trivially, 1+1 is a coproduct of 1 and 1, and 1 is choice. -/
theorem coprod_choice_to_one_one_choice
    (h : ∀ (B₁ B₂ : 𝒞), Choice B₁ → Choice B₂ →
         Choice (HasBinaryCoproducts.coprod B₁ B₂)) :
    Choice (HasBinaryCoproducts.coprod (one : 𝒞) one) :=
  h one one terminator_is_choice terminator_is_choice

/- §1.662 (2)→(3) `one_one_choice_to_boolean` proved in `Fredy.Diaconescu` (which imports the slice
   pre-topos instances of `Fredy.SlicePreTopos`, themselves importing this file). -/

/-- A complemented partition `(U, U₂)` of `A` realises `A` as the coproduct of the two
    domains *with the injections matching the subobject inclusions*: there is an iso
    `ψ : U.dom + U₂.dom ≅ A` with `inl ≫ ψ = U.arr` and `inr ≫ ψ = U₂.arr`.  This is
    `complementedSub_iso_coproduct` refined to expose the legs (needed so a copairing
    `case s₁ s₂` post-composed with `ψ⁻¹` restricts each section to its half of `A`). -/
theorem complemented_legs_iso [HasBinaryProducts 𝒞] {A : 𝒞} (U U₂ : Subobject 𝒞 A)
    (hdisj : Subobject.le (Subobject.inter U U₂) (PreLogos.bottom A))
    (hentire : Subobject.le (Subobject.entire A) (HasSubobjectUnions.union U U₂)) :
    ∃ (ψ : HasBinaryCoproducts.coprod U.dom U₂.dom ⟶ A)
      (ψinv : A ⟶ HasBinaryCoproducts.coprod U.dom U₂.dom),
      ψ ≫ ψinv = Cat.id _ ∧ ψinv ≫ ψ = Cat.id _ ∧
      HasBinaryCoproducts.inl ≫ ψ = U.arr ∧ HasBinaryCoproducts.inr ≫ ψ = U₂.arr :=
  complementedSub_legs_iso U U₂ hdisj hentire

-- `complement_le_other` (used below) is now the canonical upstream copy from `S1_62` (§1.631);
-- both live in `namespace Freyd`, so the plain name resolves without a local redeclaration. The
-- ambient `PreToposDisjoint 𝒞 extends DisjointBinaryCoproduct 𝒞 extends PositivePreLogos 𝒞`
-- supplies the `[HasBinaryCoproducts 𝒞]` it needs.

/-- Restriction of an entire relation `R : A → B` to the part landing in a monic summand
    `inj : B' ↣ B`.  Set `D := ∃_{R.colA}(R.colB # ⟨inj⟩) ⊆ A` (the image in `A` of the
    points whose `R`-value factors through `inj`).  The relation `D → B'` tabulated by that
    pullback has cover left leg, so is entire; `Choice B'` extracts a map `f : D → B'` together
    with a section `s : D → R.src` of `R` over `D` whose `B`-value is `f ≫ inj`. -/
private theorem restrict_to_summand [HasBinaryProducts 𝒞] {A B B' : 𝒞} (R : BinRel 𝒞 A B)
    (inj : B' ⟶ B) (hinj : Monic inj) (hch : Choice B') :
    ∃ (f : (existsAlong R.colA (InverseImage R.colB ⟨B', inj, hinj⟩)).dom ⟶ B')
      (s : (existsAlong R.colA (InverseImage R.colB ⟨B', inj, hinj⟩)).dom ⟶ R.src),
      s ≫ R.colA = (existsAlong R.colA (InverseImage R.colB ⟨B', inj, hinj⟩)).arr
      ∧ s ≫ R.colB = f ≫ inj := by
  classical
  let M : Subobject 𝒞 B := ⟨B', inj, hinj⟩
  let P : Subobject 𝒞 R.src := InverseImage R.colB M
  let pb := HasPullbacks.has R.colB M.arr
  have hsq : P.arr ≫ R.colB = pb.cone.π₂ ≫ inj := by
    show pb.cone.π₁ ≫ R.colB = pb.cone.π₂ ≫ M.arr; exact pb.cone.w
  let D : Subobject 𝒞 A := existsAlong R.colA P
  let il : P.dom ⟶ D.dom := image.lift (P.arr ≫ R.colA)
  have hil : il ≫ D.arr = P.arr ≫ R.colA := image.lift_fac _
  let q : P.dom ⟶ B' := pb.cone.π₂
  have hp : MonicPair il q := by
    intro W u v hua hub
    apply P.monic
    apply R.isMonicPair
    · calc (u ≫ P.arr) ≫ R.colA = u ≫ (P.arr ≫ R.colA) := Cat.assoc _ _ _
        _ = u ≫ (il ≫ D.arr) := by rw [hil]
        _ = (u ≫ il) ≫ D.arr := (Cat.assoc _ _ _).symm
        _ = (v ≫ il) ≫ D.arr := by rw [hua]
        _ = v ≫ (il ≫ D.arr) := Cat.assoc _ _ _
        _ = v ≫ (P.arr ≫ R.colA) := by rw [hil]
        _ = (v ≫ P.arr) ≫ R.colA := (Cat.assoc _ _ _).symm
    · calc (u ≫ P.arr) ≫ R.colB = u ≫ (P.arr ≫ R.colB) := Cat.assoc _ _ _
        _ = u ≫ (q ≫ inj) := by rw [hsq]
        _ = (u ≫ q) ≫ inj := (Cat.assoc _ _ _).symm
        _ = (v ≫ q) ≫ inj := by rw [hub]
        _ = v ≫ (q ≫ inj) := Cat.assoc _ _ _
        _ = v ≫ (P.arr ≫ R.colB) := by rw [hsq]
        _ = (v ≫ P.arr) ≫ R.colB := (Cat.assoc _ _ _).symm
  let T : BinRel 𝒞 D.dom B' := BinRel.mk P.dom il q hp
  have hcov : Cover il := image_lift_cover (P.arr ≫ R.colA)
  have hentT : Entire T := (tabulated_is_entire_iff_left_cover il q hp).mpr hcov
  obtain ⟨f, w, hwA, hwB⟩ := hch T hentT
  refine ⟨f, w ≫ P.arr, ?_, ?_⟩
  · calc (w ≫ P.arr) ≫ R.colA = w ≫ (P.arr ≫ R.colA) := Cat.assoc _ _ _
      _ = w ≫ (il ≫ D.arr) := by rw [hil]
      _ = (w ≫ il) ≫ D.arr := (Cat.assoc _ _ _).symm
      _ = (Cat.id _) ≫ D.arr := by rw [hwA]
      _ = D.arr := Cat.id_comp _
  · calc (w ≫ P.arr) ≫ R.colB = w ≫ (P.arr ≫ R.colB) := Cat.assoc _ _ _
      _ = w ≫ (q ≫ inj) := by rw [hsq]
      _ = (w ≫ q) ≫ inj := (Cat.assoc _ _ _).symm
      _ = f ≫ inj := by rw [hwB]

/-- A `BooleanPreLogos` witness complements every subobject **in the ambient pre-topos
    lattice**.  The witness `bl` carries its own `PreLogos` instance, distinct from the one
    `PreToposDisjoint` supplies; we bridge `bl`'s complement to the ambient lattice exactly as
    in `preTopos_boolean_iff_all_decidable` — `bl.bottom_min` upgrades the disjointness clause
    and `bl.union_min` (against the ambient union as common bound) upgrades the cover clause. -/
private theorem boolean_complementedSub (hbool : Nonempty (BooleanPreLogos 𝒞)) {A : 𝒞}
    (S : Subobject 𝒞 A) : IsComplementedSub S := by
  -- Produce the *meet-universal* `IsComplemented S` in the ambient lattice (its disjointness
  -- clause quantifies over arbitrary subobjects `S'`, so it never mentions a specific `inter`
  -- and avoids the `bl`/ambient pullback-instance diamond); then convert via the §1.631 bridge.
  apply (isComplemented_iff_sub S).mp
  obtain ⟨bl⟩ := hbool
  obtain ⟨S₂, hdisj, hunion⟩ := bl.hasComplement S
  refine ⟨S₂, ?_, ?_⟩
  · -- disjointness (universal): any common lower bound `S'` lands in `bl`-bottom (`hdisj`),
    -- then `bl`-bottom ≤ ambient-bottom by minimality.
    intro S' h1 h2
    obtain ⟨g1, hg1⟩ := hdisj S' h1 h2
    obtain ⟨g2, hg2⟩ := bl.toPreLogos.bottom_min
      (@PreLogos.bottom 𝒞 _ (‹PreToposDisjoint 𝒞›).toPositivePreLogos.toPreLogos A)
    exact ⟨g1 ≫ g2, by rw [Cat.assoc, hg2]; exact hg1⟩
  · -- cover: bl-union ≤ ambient-union bridges `⊤ ≤ S ∪ S₂`.
    refine Subobject.le_trans hunion ?_
    exact bl.toPreLogos.toHasSubobjectUnions.union_min S S₂ _
      (HasSubobjectUnions.union_left
        (self := (‹PreToposDisjoint 𝒞›).toPositivePreLogos.toPreLogos.toHasSubobjectUnions) S S₂)
      (HasSubobjectUnions.union_right
        (self := (‹PreToposDisjoint 𝒞›).toPositivePreLogos.toPreLogos.toHasSubobjectUnions) S S₂)

/-- **§1.662**: (3) → (1): boolean implies binary coproducts of choice objects are choice.
    PROOF: Given S: A → B₁+B₂ entire, the subobject Dom(S∘inl°) ⊆ A is complemented
    (boolean pre-topos). The restriction of S to Dom(S∘inl°) is entire into B₁, so
    contains f₁ (B₁ choice). The restriction to the complement is entire into B₂,
    so contains f₂ (B₂ choice). Then f₁+f₂ (copairing) is a map in S.

    STATUS (Gap C audit): the §1.658 complement layer is now AVAILABLE — `Subobject.Dom`
    (Complement.lean) gives the relation-domain operator, `invImage_complementedSub` +
    `isComplemented_iff_sub` give "Dom(S∘inl°) is complemented", and `modular_identity`
    (§1.563) the gluing.  Two pieces are still genuinely missing and are NOT supplied by
    Complement.lean: (i) a BRIDGE turning the `BinRel` `S ⊚ (graph inl)°` into the
    `Subobject 𝒞 (prod A B₁)` that `Subobject.Dom` consumes (tabulation of a relation as a
    subobject of the product), together with the lemma that RESTRICTING `S` to a complemented
    subobject `D ⊆ A` of its source yields an entire relation `D.dom → B₁`; and (ii) the
    DISJOINT-COPRODUCT copairing that recombines the two restriction-maps `f₁ : D.dom → B₁`,
    `f₂ : Dᶜ.dom → B₂` into a single map `A → B₁+B₂` lying in `S` — this needs `A ≅ D ⊔ Dᶜ`
    from the §1.62 positive/effective structure.  Neither the relation⇄subobject tabulation
    bridge nor the source-restriction-is-entire lemma exists at §1.64.  Faithful statement;
    reduces to those two relation-restriction pieces (the complement layer itself is done). -/
theorem boolean_to_coprod_choice_is_choice [HasBinaryProducts 𝒞]
    (hbool : Nonempty (BooleanPreLogos 𝒞)) :
    ∀ (B₁ B₂ : 𝒞), Choice B₁ → Choice B₂ →
      Choice (HasBinaryCoproducts.coprod B₁ B₂) := by
  classical
  intro B₁ B₂ hch₁ hch₂ A R hent
  -- R.colA is a cover (entire left leg, §1.564).
  have hcovA : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  -- The two summand subobjects of `B₁ + B₂` and the inverse images carving `R.src` in two.
  let Inl : Subobject 𝒞 (HasBinaryCoproducts.coprod B₁ B₂) :=
    ⟨B₁, HasBinaryCoproducts.inl, inl_mono⟩
  let Inr : Subobject 𝒞 (HasBinaryCoproducts.coprod B₁ B₂) :=
    ⟨B₂, HasBinaryCoproducts.inr, inr_mono⟩
  -- restriction of R to each summand: maps f₁ : D₁ → B₁, f₂ : D₂ → B₂ with sections of R.
  obtain ⟨f₁, s₁, hs₁A, hs₁B⟩ :=
    restrict_to_summand R HasBinaryCoproducts.inl inl_mono hch₁
  obtain ⟨f₂, s₂, hs₂A, hs₂B⟩ :=
    restrict_to_summand R HasBinaryCoproducts.inr inr_mono hch₂
  let D₁ : Subobject 𝒞 A := existsAlong R.colA (InverseImage R.colB Inl)
  let D₂ : Subobject 𝒞 A := existsAlong R.colA (InverseImage R.colB Inr)
  -- (1) D₁ ∪ D₂ is entire: entire A ≤ ∃(entire R.src) ≤ ∃(P₁∪P₂) ≤ D₁ ∪ D₂.
  let Bc := HasBinaryCoproducts.coprod B₁ B₂
  have hRsrc : (Subobject.entire R.src).le
      (HasSubobjectUnions.union (InverseImage R.colB Inl) (InverseImage R.colB Inr)) := by
    have ha : (Subobject.entire R.src).le (InverseImage R.colB (Subobject.entire Bc)) :=
      entire_le_invImage_entire R.colB
    have hbu : (Subobject.entire Bc).le (HasSubobjectUnions.union Inl Inr) :=
      inl_union_inr_entire (𝒟 := 𝒞) (A := B₁) (B := B₂)
    exact Subobject.le_trans ha (Subobject.le_trans (invImage_mono_local R.colB hbu)
      (PreLogos.invImage_preserves_union R.colB Inl Inr).1)
  have hAex : (Subobject.entire A).le (existsAlong R.colA (Subobject.entire R.src)) := by
    -- existsAlong R.colA (entire R.src) = image ((entire).arr ≫ colA); (entire).arr ≫ colA
    -- is a cover (= colA up to the iso id), so its image is entire.
    have hcov' : Cover ((Subobject.entire R.src).arr ≫ R.colA) := by
      -- (entire R.src).arr = id, so the composite is defeq to R.colA, which is a cover.
      intro C m g hm hfac
      refine hcovA m g hm ?_
      have : g ≫ m = Cat.id R.src ≫ R.colA := hfac
      rwa [Cat.id_comp] at this
    obtain ⟨inv, _, hinv2⟩ :=
      (cover_iff_image_entire ((Subobject.entire R.src).arr ≫ R.colA)).1 hcov'
    exact ⟨inv, hinv2⟩
  have hcov : (Subobject.entire A).le (HasSubobjectUnions.union D₁ D₂) :=
    Subobject.le_trans hAex (Subobject.le_trans (existsAlong_mono R.colA hRsrc)
      (existsAlong_union_le R.colA _ _))
  -- (2) boolean: D₁ is complemented; pick complement Dc with D₁ ∩ Dc ≤ ⊥, entire A ≤ D₁ ∪ Dc.
  obtain ⟨Dc, hDcdisj, hDccov⟩ := boolean_complementedSub hbool D₁
  -- Dc ≤ D₂ (complement of D₁ lands in any D₂ completing the cover).
  have hDcD₂ : Dc.le D₂ := complement_le_other D₁ D₂ Dc hDcdisj hcov
  obtain ⟨k, hk⟩ := hDcD₂
  -- (3) A ≅ D₁.dom + Dc.dom with injections matching the inclusions.
  obtain ⟨ψ, ψinv, _hψψ, hψinvψ, hl, hr⟩ := complemented_legs_iso D₁ Dc hDcdisj hDccov
  -- (4) restrict s₂ to Dc, copair with s₁ over the iso to get the global section h : A → R.src.
  let s₂' : Dc.dom ⟶ R.src := k ≫ s₂
  have hs₂'A : s₂' ≫ R.colA = Dc.arr := by
    calc (k ≫ s₂) ≫ R.colA = k ≫ (s₂ ≫ R.colA) := Cat.assoc _ _ _
      _ = k ≫ D₂.arr := by rw [hs₂A]
      _ = Dc.arr := hk
  let h : A ⟶ R.src := ψinv ≫ HasBinaryCoproducts.case s₁ s₂'
  -- case s₁ s₂' ≫ colA = ψ, since both have inl-leg D₁.arr and inr-leg Dc.arr.
  have hcase : HasBinaryCoproducts.case s₁ s₂' ≫ R.colA = ψ := by
    rw [HasBinaryCoproducts.case_uniq (s₁ ≫ R.colA) (s₂' ≫ R.colA)
          (HasBinaryCoproducts.case s₁ s₂' ≫ R.colA)
          (by rw [← Cat.assoc, HasBinaryCoproducts.case_inl])
          (by rw [← Cat.assoc, HasBinaryCoproducts.case_inr]),
        hs₁A, hs₂'A]
    exact (HasBinaryCoproducts.case_uniq D₁.arr Dc.arr ψ hl hr).symm
  refine ⟨h ≫ R.colB, h, ?_, rfl⟩
  calc h ≫ R.colA = ψinv ≫ (HasBinaryCoproducts.case s₁ s₂' ≫ R.colA) := Cat.assoc _ _ _
    _ = ψinv ≫ ψ := by rw [hcase]
    _ = Cat.id A := hψinvψ

end Diaconescu

end Freyd
