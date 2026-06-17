/-
  Freyd & Scedrov, *Categories and Allegories* §2.228.

  §2.228  UNION ALLEGORIES (finite unions distributing with composition,
          but not necessarily with intersection)

  Freyd considers allegories equipped with finite unions which distribute
  with COMPOSITION, but NOT necessarily with INTERSECTION.  This is a
  structure strictly weaker than a distributive allegory (§2.21): a
  distributive allegory additionally satisfies the law
      R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T).

  The three observations of §2.228:
    (a) A TABULAR allegory with this property IS distributive.
    (b) A SEMI-SIMPLE allegory with this property IS distributive.
    (c) An allegory with this property in which every morphism is the
        union of the semi-simple morphisms it contains [2.225] NEED NOT be
        distributive: for any group G of size > 2, adjoining a zero 0 and a
        maximal element M to the one-object allegory on G (with the discrete
        order, RM = MR = M for R ≠ 0, and 0 absorbing) yields such an
        allegory that is not distributive.

  All allegory infrastructure (Allegory, Tabular, SemiSimple, Simple, the
  order ⊑, ∩, °) is reused from S2_1; the distributive-allegory laws are
  reused from S2_2 for comparison.  This file adds ONLY the §2.228 weaker
  structure and the three observations.
-/

import Fredy.S2_1
import Fredy.S2_2

universe v u

namespace Freyd.Alg

variable {𝒜 : Type u}

/-! ## §2.228  Union allegories

  An allegory with finite unions distributing with composition but not
  necessarily with intersection.  Concretely: a zero morphism and a binary
  union forming a commutative-idempotent-associative semigroup with zero as
  unit, absorbing into intersection (so that ⊑ from ∩ agrees with ⊑ from ∪),
  zero absorbing under composition, and COMPOSITION distributing over union.

  This is exactly the `DistributiveAllegory` data of §2.21 MINUS the single
  axiom `inter_union_distrib` (intersection distributing over union).  We
  keep the absorption laws (`union_inter_absorb`, `inter_union_absorb`)
  because they are part of "finite unions" forming a lattice with ∩ — they
  express that ∪ is the join of the same partial order ⊑ that ∩ furnishes;
  Freyd never weakens these, only the ∩-over-∪ distributive law. -/

/-- A **UNION ALLEGORY** (§2.228): an allegory with finite unions that
    distribute with composition, but not necessarily with intersection.
    It carries the full distributive-lattice/zero structure on each hom-set
    together with composition-over-union distribution, but omits the
    intersection-over-union distributive law of §2.21. -/
class UnionAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  /-- Zero morphism 0 : a → b for each pair of objects. -/
  zero {a b : 𝒜} : a ⟶ b
  /-- Union (join) R ∪ S : a → b when R, S : a → b. -/
  union {a b : 𝒜} (R S : a ⟶ b) : a ⟶ b

  /-- Zero is absorbing on the left: 0 ≫ R = 0. -/
  zero_comp {a b c : 𝒜} (R : b ⟶ c) : (zero : a ⟶ b) ≫ R = zero
  /-- Zero is absorbing on the right: R ≫ 0 = 0. -/
  comp_zero {a b c : 𝒜} (R : a ⟶ b) : R ≫ (zero : b ⟶ c) = zero

  /-- Union is idempotent: R ∪ R = R. -/
  union_idem {a b : 𝒜} (R : a ⟶ b) : union R R = R
  /-- Union is commutative: R ∪ S = S ∪ R. -/
  union_comm {a b : 𝒜} (R S : a ⟶ b) : union R S = union S R
  /-- Union is associative: R ∪ (S ∪ T) = (R ∪ S) ∪ T. -/
  union_assoc {a b : 𝒜} (R S T : a ⟶ b) : union R (union S T) = union (union R S) T

  /-- Absorption: R ∪ (S ∩ R) = R. -/
  union_inter_absorb {a b : 𝒜} (R S : a ⟶ b) : union R (Allegory.inter S R) = R
  /-- Absorption: (R ∪ S) ∩ R = R. -/
  inter_union_absorb {a b : 𝒜} (R S : a ⟶ b) : Allegory.inter (union R S) R = R

  /-- **Composition distributes over union**: R ≫ (S ∪ T) = RS ∪ RT.
      This is the defining property of §2.228. -/
  comp_union_distrib {a b c : 𝒜} (R : a ⟶ b) (S T : b ⟶ c) :
    R ≫ union S T = union (R ≫ S) (R ≫ T)
  /-- Zero is identity for union: 0 ∪ R = R. -/
  zero_union {a b : 𝒜} (R : a ⟶ b) : union zero R = R

  -- NOTE (§2.228): the distributive-allegory law `inter_union_distrib`,
  --   R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T),
  -- is DELIBERATELY ABSENT here.  §2.228(a),(b) show it follows from
  -- tabularity / semi-simplicity; §2.228(c) shows it can genuinely fail.

/-- Zero notation for a union allegory. -/
notation "𝟘ᵤ" => UnionAllegory.zero

/-- Union notation for a union allegory. -/
infixl:65 " ∪ᵤ " => UnionAllegory.union

/-- Every distributive allegory (§2.21) is in particular a union allegory:
    it has all the §2.228 data and laws (and more). -/
instance distributiveAllegory_isUnionAllegory [DistributiveAllegory 𝒜] : UnionAllegory 𝒜 where
  zero := DistributiveAllegory.zero
  union := DistributiveAllegory.union
  zero_comp := DistributiveAllegory.zero_comp
  comp_zero := DistributiveAllegory.comp_zero
  union_idem := DistributiveAllegory.union_idem
  union_comm := DistributiveAllegory.union_comm
  union_assoc := DistributiveAllegory.union_assoc
  union_inter_absorb := DistributiveAllegory.union_inter_absorb
  inter_union_absorb := DistributiveAllegory.inter_union_absorb
  comp_union_distrib := DistributiveAllegory.comp_union_distrib
  zero_union := DistributiveAllegory.zero_union

/-! ### Order theory for a union allegory

  The lattice axioms shared with §2.21 (`union_inter_absorb`,
  `inter_union_absorb`, the union semigroup laws) suffice to recover the
  order/least-upper-bound theory of ∪ — none of these proofs uses the absent
  `inter_union_distrib`.  We re-derive them here for `UnionAllegory` so the
  §2.228 arguments can speak about ⊑ and ∪. -/

/-- In a union allegory, `R ⊑ S ↔ R ∪ S = S` (cf. §2.211; uses only the
    absorption laws, not ∩-over-∪ distribution). -/
theorem le_iff_unionU_eq_left [UnionAllegory 𝒜] {a b : 𝒜} (R S : a ⟶ b) :
    (R ⊑ S) ↔ R ∪ᵤ S = S := by
  constructor
  · intro h
    dsimp [le] at h
    have h_absorb : S ∪ᵤ (R ∩ S) = S := UnionAllegory.union_inter_absorb S R
    calc
      R ∪ᵤ S = (R ∩ S) ∪ᵤ S := by rw [h]
      _ = S ∪ᵤ (R ∩ S) := UnionAllegory.union_comm _ _
      _ = S := h_absorb
  · intro h
    dsimp [le]
    calc
      R ∩ S = S ∩ R := Allegory.inter_comm R S
      _ = (R ∪ᵤ S) ∩ R := by rw [h]
      _ = R := UnionAllegory.inter_union_absorb R S

/-- Union is the least upper bound: `A ⊑ C → B ⊑ C → A ∪ B ⊑ C`. -/
theorem unionU_lub [UnionAllegory 𝒜] {a b : 𝒜} {A B C : a ⟶ b}
    (hA : A ⊑ C) (hB : B ⊑ C) : A ∪ᵤ B ⊑ C := by
  rw [le_iff_unionU_eq_left] at hA hB ⊢
  calc
    (A ∪ᵤ B) ∪ᵤ C = A ∪ᵤ (B ∪ᵤ C) := (UnionAllegory.union_assoc A B C).symm
    _ = A ∪ᵤ C := by rw [hB]
    _ = C := hA

/-- `R ⊑ R ∪ S`. -/
theorem le_unionU_left [UnionAllegory 𝒜] {a b : 𝒜} (R S : a ⟶ b) : R ⊑ R ∪ᵤ S := by
  dsimp [le]; rw [Allegory.inter_comm, UnionAllegory.inter_union_absorb]

/-- `S ⊑ R ∪ S`. -/
theorem le_unionU_right [UnionAllegory 𝒜] {a b : 𝒜} (R S : a ⟶ b) : S ⊑ R ∪ᵤ S := by
  rw [UnionAllegory.union_comm]; exact le_unionU_left S R

/-- Union is monotone in both arguments. -/
theorem unionU_mono [UnionAllegory 𝒜] {a b : 𝒜} {R R' S S' : a ⟶ b}
    (hR : R ⊑ R') (hS : S ⊑ S') : R ∪ᵤ S ⊑ R' ∪ᵤ S' :=
  unionU_lub (le_trans hR (le_unionU_left R' S')) (le_trans hS (le_unionU_right R' S'))

/-! ### The intersection-over-union law as a property

  In a `UnionAllegory` the law `R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)` is *not*
  assumed.  We isolate it as a predicate `InterUnionDistrib`; "is a
  distributive allegory" for a union allegory means exactly that this law
  holds (the remaining distributive-allegory axioms are already present). -/

/-- The intersection-over-union distributive law of §2.21, as a property of
    a union allegory.  When this holds, the union allegory is distributive. -/
def InterUnionDistrib (𝒜 : Type u) [UnionAllegory 𝒜] : Prop :=
  ∀ {a b : 𝒜} (R S T : a ⟶ b), R ∩ (S ∪ᵤ T) = (R ∩ S) ∪ᵤ (R ∩ T)

/-! ### Tabulation transport lemmas (for §2.228(a))

  Fix a tabulation `(f,g)` of `U` (so `f° f = g° g = 1`).  The map
  `φ Q := f° ≫ Q ≫ g` carries `{Q | Q ⊑ U}` to coreflexives on the apex
  (`tab_phi_coreflexive`), with intended inverse `ψ A := f ≫ A ≫ g°`.
  Freyd states this is an order-iso; in fact `ψ` is NOT a section of `φ`
  in a general tabular allegory (the round-trip `ψ(φ Q) = Q` FAILS — see the
  Rel counterexample in `tab_transport_gap`'s docstring).  The genuinely
  constructive content (`tab_phi_coreflexive`, `tab_deflate_source/target`)
  is recorded below; the distributivity itself is the faithful sorry. -/

/-- For a tabulation, `φ Q = f° Q g` is coreflexive whenever `Q ⊑ f g°`. -/
theorem tab_phi_coreflexive [UnionAllegory 𝒜] {a p c : 𝒜}
    {f : a ⟶ c} {g : p ⟶ c} (hff1 : f° ≫ f = Cat.id c) (hgg1 : g° ≫ g = Cat.id c)
    {Q : a ⟶ p} (hQ : Q ⊑ f ≫ g°) : Coreflexive (f° ≫ Q ≫ g) := by
  dsimp [Coreflexive]
  have h1 : f° ≫ Q ≫ g ⊑ f° ≫ (f ≫ g°) ≫ g :=
    comp_mono_left f° (comp_mono_right hQ g)
  have h2 : f° ≫ (f ≫ g°) ≫ g = Cat.id c := by
    calc f° ≫ (f ≫ g°) ≫ g
        = (f° ≫ f) ≫ (g° ≫ g) := by simp [Cat.assoc]
      _ = Cat.id c ≫ Cat.id c := by rw [hff1, hgg1]
      _ = Cat.id c := by rw [Cat.id_comp]
  rw [h2] at h1; exact h1

/-! ### Tabulation deflation calculus (constructive half-identities)

  For a tabulation `(f,g)` (so `f° f = 1`, `g° g = 1`) and `Q ⊑ f g°`, the
  two one-sided "deflations" below ARE provable constructively from the meet
  equations alone (no modular law even needed): `f° Q ⊑ g°` and `Q g ⊑ f`.
  They feed `tab_phi_coreflexive` and would feed the transport round-trip.

  WHAT IS NOT PROVABLE here (see `tab_transport_gap`): the full fixed-point
  identity `f (f° Q g) g° = Q` is FALSE in a general tabular allegory — it
  fails already in `Rel`.  Concrete witness (apex `c = {∗}`, `a = b = {1,2}`,
  `f,g` the unique maps to `{∗}`; both are maps with `f° f = g° g = 1_c`, so
  `(f,g)` tabulates the full relation `U = f g°`): for `Q = {(1,1)} ⊑ U` one
  computes `f° Q g = 1_c`, whence `f (f° Q g) g° = f g° = U ≠ Q`.  Hence the
  transport map `ψ A = f A g°` is NOT a section of `φ Q = f° Q g` on
  `{Q ⊑ U}`, and §2.228(a) genuinely needs the coreflexive/idempotent-
  splitting of §2.213/§2.226, absent from this repo. -/

/-- Tabulation deflation (source side): `f° Q ⊑ g°` for `Q ⊑ f g°` when
    `f° f = 1`.  Constructive, modular law not needed. -/
theorem tab_deflate_source [UnionAllegory 𝒜] {a c p : 𝒜}
    {f : a ⟶ c} {g : p ⟶ c} (hff1 : f° ≫ f = Cat.id c)
    {Q : a ⟶ p} (hQ : Q ⊑ f ≫ g°) : f° ≫ Q ⊑ g° := by
  calc f° ≫ Q ⊑ f° ≫ (f ≫ g°) := comp_mono_left f° hQ
    _ = (f° ≫ f) ≫ g° := by simp [Cat.assoc]
    _ = g° := by rw [hff1, Cat.id_comp]

/-- Tabulation deflation (target side): `Q g ⊑ f` for `Q ⊑ f g°` when
    `g° g = 1`.  Constructive, modular law not needed. -/
theorem tab_deflate_target [UnionAllegory 𝒜] {a c p : 𝒜}
    {f : a ⟶ c} {g : p ⟶ c} (hgg1 : g° ≫ g = Cat.id c)
    {Q : a ⟶ p} (hQ : Q ⊑ f ≫ g°) : Q ≫ g ⊑ f := by
  calc Q ≫ g ⊑ (f ≫ g°) ≫ g := comp_mono_right hQ g
    _ = f ≫ (g° ≫ g) := by simp [Cat.assoc]
    _ = f := by rw [hgg1, Cat.comp_id]

/-! ### The "easy" half of intersection-over-union

  In *any* union allegory the join-semidistributive inequality
      `(R ∩ S) ∪ (R ∩ T) ⊑ R ∩ (S ∪ T)`
  holds with no further hypotheses — both `R ∩ S` and `R ∩ T` sit below `R`
  and below `S ∪ T`.  So `InterUnionDistrib` is equivalent to the *reverse*
  containment, and §2.228(a),(b) only have to supply
      `R ∩ (S ∪ T) ⊑ (R ∩ S) ∪ (R ∩ T)`. -/

/-- The always-available half of ∩-over-∪: `(R∩S) ∪ (R∩T) ⊑ R ∩ (S∪T)`. -/
theorem interUnionU_distrib_ge [UnionAllegory 𝒜] {a b : 𝒜} (R S T : a ⟶ b) :
    (R ∩ S) ∪ᵤ (R ∩ T) ⊑ R ∩ (S ∪ᵤ T) := by
  refine unionU_lub (le_inter (inter_lb_left R S) ?_) (le_inter (inter_lb_left R T) ?_)
  · exact le_trans (inter_lb_right R S) (le_unionU_left S T)
  · exact le_trans (inter_lb_right R T) (le_unionU_right S T)

/-- `InterUnionDistrib` holds iff the *reverse* (hard) containment holds for
    every `R,S,T` — the easy direction `interUnionU_distrib_ge` is free. -/
theorem interUnionDistrib_iff_le [UnionAllegory 𝒜] :
    InterUnionDistrib 𝒜 ↔
      ∀ {a b : 𝒜} (R S T : a ⟶ b), R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) := by
  constructor
  · intro h a b R S T; rw [h R S T]; exact le_refl _
  · intro h a b R S T
    exact le_antisymm (h R S T) (interUnionU_distrib_ge R S T)

/-! ## §2.213 / §2.226  Idempotent-splitting transport calculus

  This is the constructive heart of §2.228(a),(b): the *systemic / Cauchy
  completion* machinery (§2.213, §2.226) that lets a tabulation `(f,g)` of
  `U = f g°` transport the order/lattice structure of `{Q | Q ⊑ U}` onto the
  coreflexives of the apex `c`, where ∩ and composition coincide
  (`coreflexive_comp_eq_inter`, §2.121) so that the lattice is distributive.

  Everything in this block is sorry-free.  The *bridge* hypotheses
  (`hsplit*`, `hψcap`, `hψcup`) of `interUnionU_distrib_of_transport` package
  exactly the §2.213/§2.226 splitting: a coreflexive-valued retraction `ψ` of
  `φ Q := f° Q g` on `{Q ⊑ U}` that preserves ∩ and ∪.  In an EFFECTIVE
  allegory those hypotheses are *theorems* (split the coreflexive `□f`); for a
  bare tabular allegory they are NOT derivable (see `tab_transport_gap`). -/

/-- Reciprocation distributes over union (`(R ∪ S)° = R° ∪ S°`) in a union
    allegory — proved from the lub characterisation of ∪ and `recip` mono. -/
theorem recip_unionU [UnionAllegory 𝒜] {a b : 𝒜} (R S : a ⟶ b) :
    (R ∪ᵤ S)° = R° ∪ᵤ S° := by
  apply le_antisymm
  · rw [recip_le_iff]
    exact unionU_lub (recip_le_iff.mp (le_unionU_left R° S°))
      (recip_le_iff.mp (le_unionU_right R° S°))
  · exact unionU_lub (recip_mono (le_unionU_left R S)) (recip_mono (le_unionU_right R S))

/-- Composition distributes over union on the *right*: `(S ∪ T) g = Sg ∪ Tg`.
    The left law `comp_union_distrib` is an axiom; this is its reciprocal. -/
theorem unionU_comp_distrib [UnionAllegory 𝒜] {a b c : 𝒜} (S T : a ⟶ b) (g : b ⟶ c) :
    (S ∪ᵤ T) ≫ g = (S ≫ g) ∪ᵤ (T ≫ g) := by
  have h : ((S ∪ᵤ T) ≫ g)° = ((S ≫ g) ∪ᵤ (T ≫ g))° := by
    rw [recip_unionU, Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_comp,
        recip_unionU, UnionAllegory.comp_union_distrib]
  calc (S ∪ᵤ T) ≫ g = (((S ∪ᵤ T) ≫ g)°)° := (Allegory.recip_recip _).symm
    _ = (((S ≫ g) ∪ᵤ (T ≫ g))°)° := by rw [h]
    _ = (S ≫ g) ∪ᵤ (T ≫ g) := Allegory.recip_recip _

/-- The transport map `φ Q := f° Q g` preserves union:
    `f° (S ∪ T) g = f° S g ∪ f° T g`. -/
theorem phi_unionU [UnionAllegory 𝒜] {a p c : 𝒜} (f : a ⟶ c) (g : p ⟶ c) (S T : a ⟶ p) :
    f° ≫ (S ∪ᵤ T) ≫ g = (f° ≫ S ≫ g) ∪ᵤ (f° ≫ T ≫ g) := by
  rw [unionU_comp_distrib, UnionAllegory.comp_union_distrib]

/-- `φ` is a retraction of `ψ A := f A g°` on the apex coreflexives:
    `φ (ψ A) = f° (f A g°) g = A`, using `f° f = g° g = 1_c`.  (This is the
    direction of the §2.226 splitting that holds unconditionally; the *other*
    round-trip `ψ (φ Q) = Q` is the genuine gap — see `tab_transport_gap`.) -/
theorem phi_psi_apex [UnionAllegory 𝒜] {a p c : 𝒜} {f : a ⟶ c} {g : p ⟶ c}
    (hff1 : f° ≫ f = Cat.id c) (hgg1 : g° ≫ g = Cat.id c) (A : c ⟶ c) :
    f° ≫ (f ≫ A ≫ g°) ≫ g = A := by
  calc f° ≫ (f ≫ A ≫ g°) ≫ g
      = (f° ≫ f) ≫ A ≫ (g° ≫ g) := by simp [Cat.assoc]
    _ = Cat.id c ≫ A ≫ Cat.id c := by rw [hff1, hgg1]
    _ = A := by rw [Cat.id_comp, Cat.comp_id]

/-- **`ψ∘φ`-deflation, free half** (the *entirety* containment of the §2.226
    round-trip).  When `f, g` are *entire* (in particular maps), the round-trip
    `ψ (φ Q) = f (f° Q g) g°` always *contains* `Q`:
        `Q ⊑ f f° Q g g°`.
    Proof: entirety gives `1_a ⊑ f f°` and `1_p ⊑ g g°`, then bracket `Q`.
    The *reverse* containment `f f° Q g g° ⊑ Q` is the genuine obstruction —
    it fails for the bare maps-to-terminal tabulation (`f f° = ⊤`), and is
    exactly what splitting the symmetric idempotent `□f` repairs (§2.166,
    §2.213, §2.226).  See `tab_transport_gap`. -/
theorem psi_phi_deflation [UnionAllegory 𝒜] {a p c : 𝒜} {f : a ⟶ c} {g : p ⟶ c}
    (hfe : Entire f) (hge : Entire g) (Q : a ⟶ p) :
    Q ⊑ f ≫ (f° ≫ Q ≫ g) ≫ g° := by
  dsimp [Entire, dom] at hfe hge
  have hf1 : Cat.id a ⊑ f ≫ f° := by
    have := inter_lb_right (Cat.id a) (f ≫ f°); rwa [hfe] at this
  have hg1 : Cat.id p ⊑ g ≫ g° := by
    have := inter_lb_right (Cat.id p) (g ≫ g°); rwa [hge] at this
  have step1 : Q ⊑ (f ≫ f°) ≫ Q := by
    have := comp_mono_right hf1 Q; rwa [Cat.id_comp] at this
  have step2 : (f ≫ f°) ≫ Q ⊑ ((f ≫ f°) ≫ Q) ≫ (g ≫ g°) := by
    have := comp_mono_left ((f ≫ f°) ≫ Q) hg1; rwa [Cat.comp_id] at this
  have h := le_trans step1 step2
  have heq : ((f ≫ f°) ≫ Q) ≫ (g ≫ g°) = f ≫ (f° ≫ Q ≫ g) ≫ g° := by simp [Cat.assoc]
  rwa [heq] at h

/-- `ψ A := f A g°` preserves union: `ψ (A ∪ B) = ψ A ∪ ψ B`.  This is the
    `hψcup` bridge hypothesis of `interUnionU_distrib_of_transport`, available
    unconditionally (no splitting needed) from composition-over-union. -/
theorem psi_unionU [UnionAllegory 𝒜] {a p c : 𝒜} (f : a ⟶ c) (g : p ⟶ c) (A B : c ⟶ c) :
    f ≫ (A ∪ᵤ B) ≫ g° = (f ≫ A ≫ g°) ∪ᵤ (f ≫ B ≫ g°) := by
  rw [unionU_comp_distrib, UnionAllegory.comp_union_distrib]

/-- **The coreflexive distributive law** (§2.121 → §2.213).  On the
    coreflexives of any object, intersection *equals* composition
    (`coreflexive_comp_eq_inter`), and composition distributes over union
    (`comp_union_distrib`); hence ∩ distributes over ∪ *as an equality*.
    This is the distributivity that §2.228(a) transports back to `{Q ⊑ U}`. -/
theorem coreflexive_inter_unionU_distrib [UnionAllegory 𝒜] {c : 𝒜} {A B C : c ⟶ c}
    (hA : Coreflexive A) (hB : Coreflexive B) (hC : Coreflexive C) :
    A ∩ (B ∪ᵤ C) = (A ∩ B) ∪ᵤ (A ∩ C) := by
  have hBC : Coreflexive (B ∪ᵤ C) := unionU_lub hB hC
  rw [← coreflexive_comp_eq_inter hA hBC, UnionAllegory.comp_union_distrib,
      coreflexive_comp_eq_inter hA hB, coreflexive_comp_eq_inter hA hC]

/-- **§2.213/§2.226 transport theorem** (sorry-free, conditional).  Given a
    coreflexive-valued retraction `ψ` of `φ Q := f° Q g` on `{Q ⊑ U}` that
    preserves ∩ (on coreflexives) and ∪, the coreflexive distributive law
    transports back to give the full ∩-over-∪ *equality* `R ∩ (S∪T) =
    (R∩S)∪(R∩T)`, hence the §2.228(a) containment, for `R,S,T` whose
    `φ`-images are coreflexive and which `ψ∘φ` fixes.

    The hypotheses `hsplit*` (ψ∘φ = id), `hψcap`, `hψcup` are *precisely* what
    splitting the symmetric idempotent `□f` (§2.213/§2.226) supplies in an
    effective allegory.  Supplying them is the only remaining content of
    §2.228(a),(b); see `tab_transport_gap`. -/
theorem interUnionU_distrib_of_transport [UnionAllegory 𝒜] {a p c : 𝒜}
    {f : a ⟶ c} {g : p ⟶ c} {R S T : a ⟶ p}
    (ψ : (c ⟶ c) → (a ⟶ p))
    (hsplitR : ψ (f° ≫ R ≫ g) = R) (hsplitS : ψ (f° ≫ S ≫ g) = S)
    (hsplitT : ψ (f° ≫ T ≫ g) = T)
    (hcR : Coreflexive (f° ≫ R ≫ g)) (hcS : Coreflexive (f° ≫ S ≫ g))
    (hcT : Coreflexive (f° ≫ T ≫ g))
    (hψcap : ∀ A B : c ⟶ c, Coreflexive A → Coreflexive B → ψ (A ∩ B) = ψ A ∩ ψ B)
    (hψcup : ∀ A B : c ⟶ c, ψ (A ∪ᵤ B) = ψ A ∪ᵤ ψ B) :
    R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) := by
  have key := coreflexive_inter_unionU_distrib hcR hcS hcT
  have happ := congrArg ψ key
  rw [hψcap _ _ hcR (unionU_lub hcS hcT), hψcup, hψcup,
      hψcap _ _ hcR hcS, hψcap _ _ hcR hcT, hsplitR, hsplitS, hsplitT] at happ
  rw [happ]; exact le_refl _

/-! ## §2.228(a)  A tabular union allegory is distributive

  *A tabular allegory with this property is distributive.*

  Freyd's argument: given R, S, T ∈ (a,p), let (f,g) tabulate R ∪ S ∪ T.
  The poset { Q | Q ⊑ f°g } is isomorphic to the coreflexives of □f, where
  coreflexives form a distributive lattice (intersection and composition of
  coreflexives coincide).  Hence ∩ distributes over ∪. -/

/-- **Tabulation transport gap** (the one genuine §2.228(a) infrastructure
    hole).  In the context of a tabulation `(f,g)` of `U = f g°`, with the
    three morphisms `R,S,T ⊑ U` and their `φ`-images coreflexive, Freyd
    transports the *distributive* coreflexive lattice on the apex back along
    `φ Q = f° Q g`, `ψ A = f A g°` to conclude the ∩-over-∪ containment.

    The STATEMENT is true (it holds in `Rel`, which is distributive), and the
    hypotheses here are exactly those produced inside
    `interUnionDistrib_of_tabular`; none is vacuous.

    The statement is also CONSISTENT: the §2.228(c) `Q3` counterexample to
    `InterUnionDistrib` cannot satisfy these hypotheses — achieving its non-
    distributive `R,S,T` forces `f g° = top`, whence `f° f = top ≠ 1_c`,
    contradicting that `(f,g)` is a tabulation.  So no instance refutes it.

    PRECISE REDUCTION (now isolated): `interUnionU_distrib_of_transport`
    proves this containment — in fact the full ∩-over-∪ *equality* — from a
    coreflexive-valued retraction `ψ` of `φ Q := f° Q g` on `{Q ⊑ U}` with
    `ψ∘φ = id` (`hsplit*`) and `ψ` preserving ∩, ∪ (`hψcap`, `hψcup`).  Those
    bridge facts are exactly the §2.213/§2.226 splitting of the symmetric
    idempotent `□f` (effective-allegory data).  THE GAP IS PRECISELY: produce
    that splitting from a bare tabulation.

    WHY IT IS NOT ELEMENTARY (Lean-verified counterexample).  Earlier notes
    claimed the gap was the order-reflection `φ Q₁ ⊑ φ Q₂ → Q₁ ⊑ Q₂`; that is
    in fact FALSE for the bare repo datum `Tabulates` (so it cannot be the
    residual lemma).  Witness, computed in `Rel`: apex `c = {∗}`,
    `a = p = {1,2}`, `f,g` the unique total maps to `{∗}`.  Then
    `f° f = g° g = 1_c` (a valid `Tabulates` apex condition) and `U = f g° =
    ⊤`.  But `φ` collapses EVERY nonempty `Q ⊑ U` to `1_c`: e.g.
    `φ{(1,1)} = φ{(1,2)} = 1_c` while `{(1,1)} ⋢ {(1,2)}`.  Equivalently
    `ψ (φ Q) = f f° Q g g° = ⊤ ≠ Q`.  The defect is that `(f,g)` is *not a
    monic pair* (`f f° ∩ g g° = ⊤ ≠ 1`), and `f f° ∩ g g°` is not even
    well-typed when `a ≠ p`.  So the apex of a bare tabulation can be a proper
    quotient of the true subobject lattice; only SPLITTING (§2.166, §2.213,
    §2.226) repairs the apex so that `ψ` becomes a genuine section.

    INFRASTRUCTURE NOW AVAILABLE (the splitting half).  The *free* half of the
    round-trip, `Q ⊑ f f° Q g g°`, is `psi_phi_deflation` (entirety of `f,g`);
    `ψ` preserves ∪ unconditionally (`psi_unionU`); and a tabular *coreflexive*
    genuinely SPLITS — `coreflexive_split_of_tabulation` / `coreflexive_splits`
    (§2.145 / §2.163): for coreflexive `A`, a tabulation `(f,g)` has `f = g` and
    `g g° = A`, `g° g = 1`.  THE PRECISE RESIDUAL is the §2.166 *apex
    refinement*: split the coreflexive `□ := 1_c ∩ f° U g`-style idempotent to
    pass to the refined tabulation `(h f, h g)` (a genuine monic pair), where the
    reverse containment `f f° Q g g° ⊑ Q` and ∩-preservation `hψcap` of `ψ` hold
    (§2.143).  Carrying *all three* of `R,S,T` onto one refined apex is the
    systemic completion (§2.226); that single completed-allegory construction is
    the only piece still absent. -/
theorem tab_transport_gap [UnionAllegory 𝒜] {a p c : 𝒜}
    {f : a ⟶ c} {g : p ⟶ c} {R S T : a ⟶ p}
    (_hcR : Coreflexive (f° ≫ R ≫ g)) (_hcS : Coreflexive (f° ≫ S ≫ g))
    (_hcT : Coreflexive (f° ≫ T ≫ g))
    (_hRU : R ⊑ f ≫ g°) (_hSU : S ⊑ f ≫ g°) (_hTU : T ⊑ f ≫ g°) :
    R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) := by
  sorry

/-- **§2.228(a)**: a tabular union allegory satisfies the intersection-over-
    union distributive law, hence is distributive.

    By `interUnionDistrib_iff_le` it suffices to prove the *reverse*
    containment `R ∩ (S∪T) ⊑ (R∩S) ∪ (R∩T)`; the forward one is free.

    FAITHFUL SORRY: that remaining containment is Freyd's tabulation argument
    — tabulate `U := R ∪ S ∪ T` by maps `(f,g)`, transport `{Q | Q ⊑ f g°}`
    isomorphically onto the coreflexives of `c` via `Q ↦ f° Q g`,
    `A ↦ f A g°`, where for coreflexives `A ∩ B = A ≫ B` and composition
    distributes over union (`coreflexive_comp_eq_inter`,
    `comp_union_distrib`), so the coreflexive lattice is distributive and the
    law transports back.  The fixed-point identity `f f° Q g g° = Q` for
    `Q ⊑ f g°` needs the modular calculus on tabulations, infrastructure not
    yet on this repo. -/
theorem interUnionDistrib_of_tabular [UnionAllegory 𝒜]
    (h : ∀ {a b : 𝒜} (R : a ⟶ b), Tabular R) : InterUnionDistrib 𝒜 := by
  rw [interUnionDistrib_iff_le]
  intro a b R S T
  -- Tabulate U := R ∪ S ∪ T by maps (f,g); each of R,S,T sits below U.
  obtain ⟨c, f, g, hf, hg, hUeq, htab⟩ := h (R ∪ᵤ S ∪ᵤ T)
  -- f°f = 1_c and g°g = 1_c: the tabulation eq forces 1 ⊑ f°f, simplicity gives ⊒.
  have hff1 : f° ≫ f = Cat.id c :=
    le_antisymm hf.2 (by have := inter_lb_left (f° ≫ f) (g° ≫ g); rwa [htab] at this)
  have hgg1 : g° ≫ g = Cat.id c :=
    le_antisymm hg.2 (by have := inter_lb_right (f° ≫ f) (g° ≫ g); rwa [htab] at this)
  -- R,S,T ⊑ U = f g°, so their images under φ Q := f° Q g are coreflexive on c.
  have hRU : R ⊑ f ≫ g° := by rw [← hUeq]; exact le_trans (le_unionU_left _ _) (le_unionU_left _ _)
  have hSU : S ⊑ f ≫ g° := by
    rw [← hUeq]; exact le_trans (le_unionU_right _ _) (le_unionU_left _ _)
  have hTU : T ⊑ f ≫ g° := by rw [← hUeq]; exact le_unionU_right _ _
  have hcR : Coreflexive (f° ≫ R ≫ g) := tab_phi_coreflexive hff1 hgg1 hRU
  have hcS : Coreflexive (f° ≫ S ≫ g) := tab_phi_coreflexive hff1 hgg1 hSU
  have hcT : Coreflexive (f° ≫ T ≫ g) := tab_phi_coreflexive hff1 hgg1 hTU
  -- On the coreflexive lattice, ∩ = composition, which distributes over ∪
  -- (`coreflexive_comp_eq_inter` + `comp_union_distrib`); transporting that
  -- distributivity back along φ⁻¹ = (f · g°) is the remaining gap.
  exact tab_transport_gap hcR hcS hcT hRU hSU hTU


/-! ## §2.228(b)  A semi-simple union allegory is distributive

  *A semi-simple allegory with the above-mentioned property is distributive.*

  Freyd's argument: split the symmetric idempotents to obtain a tabular
  allegory with the same property, then apply §2.228(a). -/

/-- **Semi-simple → tabular transport gap** (the §2.228(b) infrastructure
    hole).  Given the semi-simple factorizations `R = Fᵣ° Gᵣ`, etc. (each
    factor simple), the intersection-over-union containment follows by
    splitting the symmetric idempotents `Fᵣ° Fᵣ`, … to land in a *tabular*
    union allegory with the same composition-over-union structure, where
    §2.228(a) applies, and pulling the result back.

    FAITHFUL SORRY: the SAME gap as `tab_transport_gap` blocks this, and it is
    the §2.213/§2.226 *splitting* (not the false order-reflection — see the
    Lean-verified `Rel` singleton counterexample in `tab_transport_gap`).
    Freyd's route is: split the symmetric idempotents `Fᵣ° Fᵣ`, … to pass to
    an *effective* tabular allegory with the same composition-over-union
    structure, where §2.228(a) closes (via `interUnionU_distrib_of_transport`,
    whose `hsplit*`/`hψcap`/`hψcup` are now theorems), then pull back.  A
    semi-simple factor `R = Fᵣ° Gᵣ` yields a genuine TABULATION only after this
    splitting (simplicity of `Fᵣ, Gᵣ` alone is not enough — one also needs the
    monic-pair condition the splitting supplies).  Per §2.16(10): for `R = F°G`,
    `F F° ∩ G G°` is a symmetric idempotent; splitting it by `H` (`H H° = 1`,
    `H° H = F F° ∩ G G°`) makes `H F, H G` MAPS tabulating `R`.

    INFRASTRUCTURE NOW AVAILABLE.  The coreflexive case of this splitting is a
    theorem (`coreflexive_splits`, §2.145/§2.163), and the free deflation half
    plus ∪-preservation of `ψ` are theorems (`psi_phi_deflation`, `psi_unionU`).
    THE PRECISE RESIDUAL is splitting the *equivalence-relation* symmetric
    idempotent `F F° ∩ G G°` (not merely a coreflexive) — i.e. effectiveness, the
    systemic completion (§2.226) — which is the single construction still absent.
    The hypotheses are genuine semi-simple witnesses of `R, S, T`; none is
    vacuous. -/
theorem semiSimple_transport_gap [UnionAllegory 𝒜] {a b : 𝒜} {R S T : a ⟶ b}
    (_hR : SemiSimple R) (_hS : SemiSimple S) (_hT : SemiSimple T) :
    R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) := by
  sorry

/-- **§2.228(b)**: a semi-simple union allegory satisfies the
    intersection-over-union distributive law, hence is distributive.

    By `interUnionDistrib_iff_le` it suffices to prove the reverse
    containment; feeding the semi-simple witnesses of `R,S,T` to
    `semiSimple_transport_gap` discharges it (modulo that gap). -/
theorem interUnionDistrib_of_semiSimple [UnionAllegory 𝒜]
    (h : ∀ {a b : 𝒜} (R : a ⟶ b), SemiSimple R) : InterUnionDistrib 𝒜 := by
  rw [interUnionDistrib_iff_le]
  intro a b R S T
  exact semiSimple_transport_gap (h R) (h S) (h T)

/-! ## §2.228(c)  Necessity of one of the two hypotheses

  *An allegory with this property in which, further, every morphism is the
  union of semi-simple morphisms it contains [2.225] need not be
  distributive.*

  The witness: for any group G with more than two elements, adjoin a zero 0
  and a maximal element M to the one-object allegory on G (G discretely
  ordered; composition uses the group multiplication and RM = MR = M for
  R ≠ 0; 0 absorbs everything; reciprocation uses inverses, fixing 0 and M).
  This is a union allegory in which every morphism is the union of the
  semi-simple morphisms it contains, yet it is not distributive. -/

/-- A morphism `R : a → b` is the **union of the semi-simple morphisms it
    contains** (§2.225 / §2.228(c)): `R` is a finite union of semi-simple
    morphisms, each contained in `R`.  Stated via a list of semi-simple
    sub-morphisms whose union is `R`. -/
def UnionOfSemiSimpleUA [UnionAllegory 𝒜] {a b : 𝒜} (R : a ⟶ b) : Prop :=
  ∃ (l : List (a ⟶ b)),
    (∀ S ∈ l, SemiSimple S ∧ S ⊑ R) ∧
    l.foldr (· ∪ᵤ ·) (𝟘ᵤ : a ⟶ b) = R

/-! ### The explicit witness: the group `ℤ/3` with `0` and `M` adjoined

  We take Freyd's construction for the smallest admissible group `G = ℤ/3 =
  {e, a, a²}` (|G| = 3 > 2).  The one-object allegory has hom-set
  `Q3 = {𝟎, e, a, a², M}` with:

  * **order / lattice**: `𝟎` bottom, `M` top, the three group elements
    pairwise incomparable (discrete order on `G`).  `∩` = meet, `∪` = join.
  * **composition**: group multiplication on `G`; `𝟎` absorbing; `M ∘ x =
    x ∘ M = M` for `x ≠ 𝟎`; identity is `e`.
  * **reciprocation**: inverse on `G` (`a° = a²`), fixing `𝟎` and `M`.

  All allegory and union-allegory axioms are finite identities on `Q3`,
  discharged by `decide`.  The single object is modelled by `Unit`. -/

/-- Hom-set of the §2.228(c) counterexample: `ℤ/3 ∪ {𝟎, M}`. -/
inductive Q3 where
  | zero | e | a | a2 | top
  deriving DecidableEq, Repr

namespace Q3

/-- Lattice meet: `𝟎` bottom, `top` top, distinct group elements meet to `𝟎`. -/
def meet : Q3 → Q3 → Q3
  | zero, _ => zero
  | _, zero => zero
  | top, y => y
  | x, top => x
  | e, e => e | a, a => a | a2, a2 => a2
  | _, _ => zero

/-- Lattice join (dual of `meet`): `top` top, distinct group elements join to `top`. -/
def join : Q3 → Q3 → Q3
  | zero, y => y
  | x, zero => x
  | top, _ => top
  | _, top => top
  | e, e => e | a, a => a | a2, a2 => a2
  | _, _ => top

/-- Composition: group multiplication on `G`, `𝟎` absorbing, `M` maximal. -/
def comp : Q3 → Q3 → Q3
  | zero, _ => zero
  | _, zero => zero
  -- e is the group identity
  | e, y => y
  | x, e => x
  -- M is absorbing among the nonzero elements
  | top, _ => top
  | _, top => top
  -- the remaining products are inside G = {a, a²}
  | a, a => a2
  | a, a2 => e
  | a2, a => e
  | a2, a2 => a

/-- Reciprocation: group inverse (`a° = a²`), `𝟎` and `M` symmetric. -/
def recip : Q3 → Q3
  | zero => zero | e => e | a => a2 | a2 => a | top => top

end Q3

/-- The one-object category of the §2.228(c) counterexample. -/
instance : Cat.{0} Unit where
  Hom _ _ := Q3
  id _ := Q3.e
  comp R S := Q3.comp R S
  id_comp := by intro X Y f; cases f <;> rfl
  comp_id := by intro X Y f; cases f <;> rfl
  assoc := by intro W X Y Z f g h; cases f <;> cases g <;> cases h <;> rfl

/-- The §2.228(c) allegory structure on `Unit` (hom-set `Q3`). -/
instance counterAllegory : Allegory.{0} Unit where
  recip R := Q3.recip R
  inter R S := Q3.meet R S
  recip_recip := by intro a b R; cases R <;> rfl
  recip_comp := by intro a b c R S; cases R <;> cases S <;> rfl
  recip_inter := by intro a b R S; cases R <;> cases S <;> rfl
  inter_idem := by intro a b R; cases R <;> rfl
  inter_comm := by intro a b R S; cases R <;> cases S <;> rfl
  inter_assoc := by intro a b R S T; cases R <;> cases S <;> cases T <;> rfl
  semidistrib := by intro a b c R S T; cases R <;> cases S <;> cases T <;> rfl
  modular := by intro a b c R S T; cases R <;> cases S <;> cases T <;> rfl

/-- The §2.228(c) union-allegory structure: `𝟎 = Q3.zero`, `∪ = Q3.join`,
    composition distributing over union, but NOT intersection. -/
instance counterUnionAllegory : UnionAllegory.{0} Unit where
  zero := Q3.zero
  union R S := Q3.join R S
  zero_comp := by intro a b c R; cases R <;> rfl
  comp_zero := by intro a b c R; cases R <;> rfl
  union_idem := by intro a b R; cases R <;> rfl
  union_comm := by intro a b R S; cases R <;> cases S <;> rfl
  union_assoc := by intro a b R S T; cases R <;> cases S <;> cases T <;> rfl
  union_inter_absorb := by intro a b R S; cases R <;> cases S <;> rfl
  inter_union_absorb := by intro a b R S; cases R <;> cases S <;> rfl
  comp_union_distrib := by intro a b c R S T; cases R <;> cases S <;> cases T <;> rfl
  zero_union := by intro a b R; cases R <;> rfl

/-- In the §2.228(c) model the simple morphisms are exactly `{𝟎, e, a, a²}`
    (everything but `M`): `F° F ⊑ e` fails only for `F = M` (`M° M = M ⋢ e`). -/
theorem Q3.simple_of {F : Q3} (hF : F ≠ Q3.top) :
    Simple (𝒜 := Unit) (a := ()) (b := ()) F := by
  dsimp [Simple, le]
  cases F <;> first | rfl | exact absurd rfl hF

/-- Each group element `g` (and `𝟎`) is semi-simple: `g = e° ≫ g` with `e, g`
    simple; `𝟎 = 𝟎° ≫ 𝟎`. -/
theorem Q3.semiSimple_of {R : Q3} (hR : R ≠ Q3.top) :
    SemiSimple (𝒜 := Unit) (a := ()) (b := ()) R :=
  ⟨(), Q3.e, R, Q3.simple_of (by decide), Q3.simple_of hR, by cases R <;> rfl⟩

/-- `S ⊑ R` in the §2.228(c) model is the decidable identity `S ∩ R = S`. -/
theorem Q3.le_of {S R : Q3} (h : Q3.meet S R = S) :
    @le Unit () () counterAllegory S R := h

/-- Every morphism of the §2.228(c) model is the union of the semi-simple
    morphisms it contains.  Non-`M` morphisms are themselves semi-simple;
    `M = e ∪ a` is the union of two distinct (semi-simple) group elements. -/
theorem counter_unionOfSemiSimple (R : Q3) :
    UnionOfSemiSimpleUA (𝒜 := Unit) (a := ()) (b := ()) R := by
  -- helper: a non-M element x with x ∩ R = x is a semi-simple sub-morphism of R
  have ss : ∀ (x : Q3), x ≠ Q3.top → Q3.meet x R = x →
      SemiSimple (𝒜 := Unit) (a := ()) (b := ()) x ∧
        @le Unit () () counterAllegory x R :=
    fun _ hx hle => ⟨Q3.semiSimple_of hx, Q3.le_of hle⟩
  cases R
  · refine ⟨[Q3.zero], ?_, rfl⟩
    intro S hS; simp only [List.mem_singleton] at hS; subst hS; exact ss _ (by decide) rfl
  · refine ⟨[Q3.e], ?_, rfl⟩
    intro S hS; simp only [List.mem_singleton] at hS; subst hS; exact ss _ (by decide) rfl
  · refine ⟨[Q3.a], ?_, rfl⟩
    intro S hS; simp only [List.mem_singleton] at hS; subst hS; exact ss _ (by decide) rfl
  · refine ⟨[Q3.a2], ?_, rfl⟩
    intro S hS; simp only [List.mem_singleton] at hS; subst hS; exact ss _ (by decide) rfl
  · -- M = e ∪ a, both simple group elements, both ⊑ M
    refine ⟨[Q3.e, Q3.a], ?_, rfl⟩
    intro S hS; simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl
    · exact ss _ (by decide) rfl
    · exact ss _ (by decide) rfl

/-- **§2.228(c)**: there is a union allegory in which every morphism is the
    union of the semi-simple morphisms it contains, but the intersection-
    over-union distributive law FAILS — so the union-of-semi-simples
    hypothesis alone does not force distributivity (in contrast to the
    tabular and semi-simple hypotheses of (a),(b)).

    Witness: the explicit `ℤ/3 ∪ {𝟎, M}` allegory above. Non-distributivity
    is exhibited by `R = a`, `S = e`, `T = a²`:
    `a ∩ (e ∪ a²) = a ∩ M = a`, but `(a ∩ e) ∪ (a ∩ a²) = 𝟎 ∪ 𝟎 = 𝟎`. -/
theorem exists_unionOfSemiSimple_not_distributive :
    ∃ (𝒜 : Type 0) (_ : UnionAllegory.{0, 0} 𝒜),
      (∀ {a b : 𝒜} (R : a ⟶ b), UnionOfSemiSimpleUA R) ∧ ¬ InterUnionDistrib 𝒜 := by
  refine ⟨Unit, counterUnionAllegory, ?_, ?_⟩
  · -- every morphism is the union of the semi-simple morphisms it contains
    intro a b R
    exact counter_unionOfSemiSimple R
  · -- non-distributivity at R=a, S=e, T=a²
    intro hd
    have h := hd (a := ()) (b := ()) Q3.a Q3.e Q3.a2
    -- LHS = a ∩ M = a, RHS = 𝟎 ∪ 𝟎 = 𝟎; unfold the instance projections.
    simp only [Allegory.inter, UnionAllegory.union, counterAllegory, counterUnionAllegory,
      Q3.meet, Q3.join] at h
    exact Q3.noConfusion h

end Freyd.Alg
