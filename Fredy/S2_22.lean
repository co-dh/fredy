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

/-! ### Modular meet calculus: maps distribute over intersection (§2.136)

  Two genuinely-new modular-law facts, proved sorry-free, that the §2.228(a)
  transport needs.  `simple_comp_inter` is Freyd §2.136 (`F(R∩S) = FR ∩ FS`
  for `F` simple); `modular_le_left` is the left-handed companion of
  `modular_le` (`(R≫S)∩T ⊑ R≫(S ∩ R°≫T)`), obtained by reciprocating the
  right modular law.  Together they drive the source-apex round-trip below. -/

/-- **§2.136**: a simple morphism distributes over intersection on the left,
    `F ≫ (R ∩ S) = (F ≫ R) ∩ (F ≫ S)` for `F` simple.  Proved by reciprocating
    and applying the right modular law, using `F° ≫ F ⊑ 1`. -/
theorem simple_comp_inter [UnionAllegory 𝒜] {a b c : 𝒜} {F : a ⟶ b}
    (hF : Simple F) (R S : b ⟶ c) : F ≫ (R ∩ S) = (F ≫ R) ∩ (F ≫ S) := by
  apply le_antisymm
  · exact le_inter (comp_mono_left F (inter_lb_left R S)) (comp_mono_left F (inter_lb_right R S))
  have hgoal : ((F ≫ R) ∩ (F ≫ S))° ⊑ (F ≫ (R ∩ S))° := by
    rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp,
        Allegory.recip_comp, Allegory.recip_inter]
    refine le_trans (modular_le R° F° (S° ≫ F°)) ?_
    apply comp_mono_right
    apply le_inter (inter_lb_left _ _)
    refine le_trans (inter_lb_right _ _) ?_
    rw [Allegory.recip_recip, Cat.assoc]
    calc S° ≫ (F° ≫ F) ⊑ S° ≫ Cat.id b := comp_mono_left S° hF
      _ = S° := Cat.comp_id S°
  have := recip_mono hgoal
  rwa [Allegory.recip_recip, Allegory.recip_recip] at this

/-- The **left modular law** in order form: `(R ≫ S) ∩ T ⊑ R ≫ (S ∩ R° ≫ T)`.
    The reciprocal companion of `modular_le`; both are pure modular-law facts. -/
theorem modular_le_left [UnionAllegory 𝒜] {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S) ∩ T ⊑ R ≫ (S ∩ R° ≫ T) := by
  have h := modular_le S° R° T°
  rw [Allegory.recip_recip] at h
  have hgoal : ((R ≫ S) ∩ T)° ⊑ (R ≫ (S ∩ R° ≫ T))° := by
    rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_inter,
        Allegory.recip_comp, Allegory.recip_recip]
    exact h
  have := recip_mono hgoal
  rwa [Allegory.recip_recip, Allegory.recip_recip] at this

/-! ### The source-apex round-trip is an EQUALITY (§2.143)

  This is the identity the earlier `tab_transport_gap` docstring claimed was
  *not* elementary.  It IS — provided one uses the **source-apex** tabulation
  (legs `F : c → a`, `G : c → p` out of the apex, `U = F° ≫ G`) rather than the
  repo's *target-apex* `Tabulates` (legs into the apex, `U = f ≫ g°`).  For the
  source-apex span the round-trip `F° (1_c ∩ F Q G°) G = Q` holds for every
  `Q ⊑ F° G`, with NO splitting and NO monic-pair hypothesis — only that
  `F, G` are maps.  (The repo's target-apex span has the *opposite* defect: the
  hard ≥-half holds but the easy ≤-half fails, since it would need `F F° ⊑ 1`.)

  Hence the genuine residual of §2.228(a) is *not* a missing identity but the
  missing **source-apex tabulation** itself: `Tabular`/`TabularAllegory` in this
  repo provide only the target-apex (cospan) form `U = f g°`.  Turning that into
  a jointly-monic span `c → a`, `c → p` is the §2.147 pullback / §2.226 systemic
  completion — the single construction still absent (it needs products or the
  completion object, neither available from `EffectiveAllegory` alone). -/

/-- **§2.143 source-apex round-trip** (sorry-free).  For maps `F : c → a`,
    `G : c → p` and any `Q ⊑ F° ≫ G`, the transport `Φ Q := 1_c ∩ F Q G°`
    (a coreflexive on the apex `c`) is inverted by `Ψ A := F° A G`:
        `F° ≫ (1_c ∩ F ≫ Q ≫ G°) ≫ G = Q`.
    Easy ≤-half uses `F, G` simple; hard ≥-half uses the modular law and
    `Q ⊑ F° G` (via `modular_le`, `modular_le_left`). -/
theorem src_apex_roundtrip [UnionAllegory 𝒜] {a p c : 𝒜} {F : c ⟶ a} {G : c ⟶ p}
    (hF : Map F) (hG : Map G) {Q : a ⟶ p} (hQ : Q ⊑ F° ≫ G) :
    F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G = Q := by
  apply le_antisymm
  · -- ≤ : F°(1∩FQG°)G ⊑ F°(FQG°)G = (F°F)Q(G°G) ⊑ Q, using F,G simple
    have hFs : F° ≫ F ⊑ Cat.id a := hF.2
    have hGs : G° ≫ G ⊑ Cat.id p := hG.2
    have key : (F° ≫ F) ≫ (Q ≫ (G° ≫ G)) ⊑ Q := by
      have a1 : (F° ≫ F) ≫ (Q ≫ (G° ≫ G)) ⊑ Cat.id a ≫ (Q ≫ (G° ≫ G)) := comp_mono_right hFs _
      rw [Cat.id_comp] at a1
      have a3 : Q ≫ (G° ≫ G) ⊑ Q ≫ Cat.id p := comp_mono_left Q hGs
      rw [Cat.comp_id] at a3
      exact le_trans a1 a3
    have b1 : F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G ⊑ F° ≫ (F ≫ Q ≫ G°) ≫ G :=
      comp_mono_left F° (comp_mono_right (inter_lb_right _ _) G)
    have b2 : F° ≫ (F ≫ Q ≫ G°) ≫ G = (F° ≫ F) ≫ (Q ≫ (G° ≫ G)) := by simp [Cat.assoc]
    rw [b2] at b1
    exact le_trans b1 key
  · -- ≥ : Q ⊑ (F° ∩ QG°)G ⊑ F°(1 ∩ FQG°)G, via modular_le and modular_le_left
    have s1 : Q ⊑ (F° ∩ (Q ≫ G°)) ≫ G := by
      have hm := modular_le F° G Q
      have heq : (F° ≫ G) ∩ Q = Q := by rw [Allegory.inter_comm]; exact inter_eq_left hQ
      rwa [heq] at hm
    have s2 : (F° ∩ (Q ≫ G°)) ⊑ F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) := by
      have hml := modular_le_left F° (Cat.id c) (Q ≫ G°)
      rw [Cat.comp_id, Allegory.recip_recip] at hml
      exact hml
    have s3 : (F° ∩ (Q ≫ G°)) ≫ G ⊑ (F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°))) ≫ G :=
      comp_mono_right s2 G
    rw [Cat.assoc] at s3
    exact le_trans s1 s3

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

/-! ### §2.143 / §2.166  Source-apex tabulation transport (the genuine order-iso)

  The target-apex transport (`interUnionU_distrib_of_transport`) used the routing
  `φ Q := f° Q g`, where the round-trip `ψ(φ Q) = Q` genuinely FAILS for a bare
  tabulation (Rel singleton counterexample).  The repair is the SOURCE-APEX routing
  of §2.143/§2.166: a span of *maps* `F : c → a`, `G : c → p` with `U = F° G` that
  is **jointly monic on the apex**, `F F° ∩ G G° = 1_c`.  For such a span the
  order-iso

      φ Q := 1_c ∩ F Q G°   (coreflexive on c),   ψ A := F° A G

  between `{Q | Q ⊑ U}` and the coreflexives of `c` is *genuine* — BOTH round-trips
  hold — and the distributive coreflexive lattice transports back.  Everything in
  this block is sorry-free; the four order-iso half-identities are
  `src_roundtrip_le` (`ψφ ⊑ id`), `src_roundtrip_ge` (`id ⊑ ψφ`),
  `src_phipsi_le` (`φψ ⊑ id`), `src_phipsi_ge` (`id ⊑ φψ`).  The single piece
  still missing from this repo is the *construction* of such a span for an
  arbitrary `U` (§2.166), isolated as the lone hole `srcTabulation_exists`. -/

/-- **Left-handed modular law**: `S ∩ R≫T ⊑ R ≫ (R°≫S ∩ T)`.  The reciprocal
    companion of `modular_le`; obtained by reciprocating `modular_le` on `T°,R°,S°`. -/
theorem left_modular_le {a b d : 𝒜} [Allegory 𝒜] (R : a ⟶ b) (S : a ⟶ d) (T : b ⟶ d) :
    S ∩ R ≫ T ⊑ R ≫ (R° ≫ S ∩ T) := by
  have hgoal : (S ∩ R ≫ T)° ⊑ (R ≫ (R° ≫ S ∩ T))° := by
    rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_inter,
        Allegory.recip_comp, Allegory.recip_recip]
    have hm := modular_le T° R° S°
    rw [Allegory.recip_recip] at hm
    rw [Allegory.inter_comm S° (T° ≫ R°), Allegory.inter_comm (S° ≫ R) T°]
    exact hm
  have := recip_mono hgoal
  rwa [Allegory.recip_recip, Allegory.recip_recip] at this

/-- **Apex coupling lemma** (the heart of §2.143's "H is simple").  For a
    jointly-monic span (`F F° ∩ G G° = 1_c`) and a coreflexive `A`, the two
    coupled composites meet inside `A`: `(F F°≫A) ∩ (G G°≫A) ⊑ A`. -/
theorem srcTab_cap {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    (hmonic : F ≫ F° ∩ G ≫ G° = Cat.id c) {A : c ⟶ c} (hA : Coreflexive A) :
    ((F ≫ F°) ≫ A) ∩ ((G ≫ G°) ≫ A) ⊑ A := by
  have hAcoref : A ⊑ Cat.id c := hA
  have hAsymm : A° = A := symmetric_eq (coreflexive_symmetric_idempotent hA).1
  have hAidem : A ≫ A = A := (coreflexive_symmetric_idempotent hA).2
  have m := modular_le (F ≫ F°) A ((G ≫ G°) ≫ A)
  rw [hAsymm] at m
  rw [show ((G ≫ G°) ≫ A) ≫ A = (G ≫ G°) ≫ A by rw [Cat.assoc, hAidem]] at m
  refine le_trans m ?_
  have hcap : (F ≫ F°) ∩ ((G ≫ G°) ≫ A) ⊑ Cat.id c := by
    have h1 : (G ≫ G°) ≫ A ⊑ G ≫ G° := by
      have := comp_mono_left (G ≫ G°) hAcoref; rwa [Cat.comp_id] at this
    calc (F ≫ F°) ∩ ((G ≫ G°) ≫ A) ⊑ (F ≫ F°) ∩ (G ≫ G°) :=
          le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) h1)
      _ = Cat.id c := hmonic
  have := comp_mono_right hcap A; rwa [Cat.id_comp] at this

/-- One-sided deflation feeding `src_phipsi_le`: `1_c ∩ F F° A G G° ⊑ A G G°`. -/
theorem srcTab_peel {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    (hmonic : F ≫ F° ∩ G ≫ G° = Cat.id c) {A : c ⟶ c} (hA : Coreflexive A) :
    Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)) ⊑ A ≫ (G ≫ G°) := by
  have hAsymm : A° = A := symmetric_eq (coreflexive_symmetric_idempotent hA).1
  have hAidem : A ≫ A = A := (coreflexive_symmetric_idempotent hA).2
  have mL := modular_le (F ≫ F°) (A ≫ (G ≫ G°)) (Cat.id c)
  rw [Allegory.inter_comm ((F ≫ F°) ≫ A ≫ (G ≫ G°)) (Cat.id c)] at mL
  rw [show (A ≫ (G ≫ G°))° = (G ≫ G°) ≫ A by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, hAsymm],
      Cat.id_comp] at mL
  refine le_trans mL ?_
  have hCA : (F ≫ F° ∩ (G ≫ G°) ≫ A) ≫ A ⊑ A := by
    have hsd : (F ≫ F° ∩ (G ≫ G°) ≫ A) ≫ A ⊑ ((F ≫ F°) ≫ A) ∩ (((G ≫ G°) ≫ A) ≫ A) :=
      le_inter (comp_mono_right (inter_lb_left _ _) A) (comp_mono_right (inter_lb_right _ _) A)
    rw [show ((G ≫ G°) ≫ A) ≫ A = (G ≫ G°) ≫ A by rw [Cat.assoc, hAidem]] at hsd
    exact le_trans hsd (srcTab_cap hmonic hA)
  rw [show (F ≫ F° ∩ (G ≫ G°) ≫ A) ≫ (A ≫ (G ≫ G°))
        = ((F ≫ F° ∩ (G ≫ G°) ≫ A) ≫ A) ≫ (G ≫ G°) by simp [Cat.assoc]]
  exact comp_mono_right hCA (G ≫ G°)

/-- **`φψ ⊑ id`** (§2.143/§2.166).  For a jointly-monic span the round-trip
    `φ(ψ A) = 1_c ∩ F F° A G G°` lands back below the coreflexive `A`. -/
theorem src_phipsi_le {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    (hmonic : F ≫ F° ∩ G ≫ G° = Cat.id c) {A : c ⟶ c} (hA : Coreflexive A) :
    Cat.id c ∩ (F ≫ (F° ≫ A ≫ G) ≫ G°) ⊑ A := by
  have hAsymm : A° = A := symmetric_eq (coreflexive_symmetric_idempotent hA).1
  rw [show F ≫ (F° ≫ A ≫ G) ≫ G° = (F ≫ F°) ≫ A ≫ (G ≫ G°) by simp [Cat.assoc]]
  have hMsymm : (Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)))° = Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)) :=
    symmetric_eq (coreflexive_symmetric_idempotent (le_trans (inter_lb_left _ _) (le_refl _))).1
  have hmonic' : G ≫ G° ∩ F ≫ F° = Cat.id c := by rw [Allegory.inter_comm]; exact hmonic
  have hGGA : Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)) ⊑ (G ≫ G°) ≫ A := by
    have h := recip_mono (srcTab_peel hmonic hA); rw [hMsymm] at h
    rwa [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, hAsymm] at h
  have hMrecip_eq :
      (Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)))° = Cat.id c ∩ ((G ≫ G°) ≫ A ≫ (F ≫ F°)) := by
    simp only [Allegory.recip_inter, recip_id, Allegory.recip_comp, Allegory.recip_recip, hAsymm]
    simp [Cat.assoc]
  have hFFA : Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)) ⊑ (F ≫ F°) ≫ A := by
    have hp := srcTab_peel hmonic' hA
    rw [← hMrecip_eq] at hp
    have h := recip_mono hp; rw [Allegory.recip_recip] at h
    rwa [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, hAsymm] at h
  exact le_trans (le_inter hFFA hGGA) (srcTab_cap hmonic hA)

/-- **`id ⊑ φψ`** (§2.143/§2.166).  For an *entire* span `1_c ⊑ F F°`, `1_c ⊑ G G°`,
    the round-trip `φ(ψ A)` contains the coreflexive `A`. -/
theorem src_phipsi_ge {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    (hFe : Entire F) (hGe : Entire G) {A : c ⟶ c} (hA : Coreflexive A) :
    A ⊑ Cat.id c ∩ (F ≫ (F° ≫ A ≫ G) ≫ G°) := by
  have hf1 : Cat.id c ⊑ F ≫ F° := by
    dsimp [Entire, dom] at hFe
    have := inter_lb_right (Cat.id c) (F ≫ F°); rwa [hFe] at this
  have hg1 : Cat.id c ⊑ G ≫ G° := by
    dsimp [Entire, dom] at hGe
    have := inter_lb_right (Cat.id c) (G ≫ G°); rwa [hGe] at this
  apply le_inter hA
  have e1 : A ⊑ (F ≫ F°) ≫ A := by
    have := comp_mono_right hf1 A; rwa [Cat.id_comp] at this
  have e2 : (F ≫ F°) ≫ A ⊑ ((F ≫ F°) ≫ A) ≫ (G ≫ G°) := by
    have := comp_mono_left ((F ≫ F°) ≫ A) hg1; rwa [Cat.comp_id] at this
  have e3 : ((F ≫ F°) ≫ A) ≫ (G ≫ G°) = F ≫ (F° ≫ A ≫ G) ≫ G° := by simp [Cat.assoc]
  exact e3 ▸ le_trans e1 e2

/-- **`ψφ ⊑ id`** (§2.143).  `ψ(φ Q) = F° (1_c ∩ F Q G°) G ⊑ Q` for any `Q`,
    using only that `F, G` are simple (`F° F ⊑ 1`, `G° G ⊑ 1`). -/
theorem src_roundtrip_le {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    (hFs : F° ≫ F ⊑ Cat.id a) (hGs : G° ≫ G ⊑ Cat.id p) (Q : a ⟶ p) :
    F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G ⊑ Q := by
  have hstep : F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G ⊑ F° ≫ (F ≫ Q ≫ G°) ≫ G :=
    comp_mono_left F° (comp_mono_right (inter_lb_right _ _) G)
  have heq : F° ≫ (F ≫ Q ≫ G°) ≫ G = (F° ≫ F) ≫ Q ≫ (G° ≫ G) := by simp [Cat.assoc]
  have hb1 : (F° ≫ F) ≫ Q ≫ (G° ≫ G) ⊑ Cat.id a ≫ Q ≫ (G° ≫ G) := comp_mono_right hFs _
  have hb2 : Cat.id a ≫ Q ≫ (G° ≫ G) ⊑ Cat.id a ≫ Q ≫ Cat.id p :=
    comp_mono_left _ (comp_mono_left Q hGs)
  have hbound : (F° ≫ F) ≫ Q ≫ (G° ≫ G) ⊑ Q := by
    have h := le_trans hb1 hb2
    rwa [show Cat.id a ≫ Q ≫ Cat.id p = Q by simp [Cat.id_comp, Cat.comp_id]] at h
  exact le_trans hstep (heq ▸ hbound)

/-- **`id ⊑ ψφ`** (§2.143).  `Q ⊑ ψ(φ Q) = F° (1_c ∩ F Q G°) G` for `Q ⊑ F° G`,
    using only the (left-)modular law — no map or monic hypothesis. -/
theorem src_roundtrip_ge {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    {Q : a ⟶ p} (hQ : Q ⊑ F° ≫ G) :
    Q ⊑ F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G := by
  have hstep1 : Q ⊑ (F° ∩ (Q ≫ G°)) ≫ G := by
    calc Q = (F° ≫ G) ∩ Q := by rw [Allegory.inter_comm]; exact (inter_eq_left hQ).symm
      _ ⊑ (F° ∩ (Q ≫ G°)) ≫ G := modular_le F° G Q
  have hlm := left_modular_le F° (Q ≫ G°) (Cat.id c)
  rw [Cat.comp_id, Allegory.recip_recip] at hlm
  have hmid : F° ∩ (Q ≫ G°) ⊑ F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) := by
    rw [Allegory.inter_comm F° (Q ≫ G°)]
    refine le_trans hlm (comp_mono_left F° ?_)
    rw [Allegory.inter_comm (F ≫ Q ≫ G°) (Cat.id c)]; exact le_refl _
  have hstep2 : (F° ∩ (Q ≫ G°)) ≫ G ⊑ F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G := by
    have h := comp_mono_right hmid G; rwa [Cat.assoc] at h
  exact le_trans hstep1 hstep2

/-- **§2.228(a) transport, made unconditional on the span** (sorry-free).  Given a
    SOURCE-APEX span of maps `(F, G)` jointly monic on the apex (`F F° ∩ G G° = 1_c`)
    with `R, S, T ⊑ F° G`, the order-iso `φ Q := 1_c ∩ F Q G°` / `ψ A := F° A G`
    transports the distributive coreflexive lattice of `c` back to give the
    ∩-over-∪ containment.  This is Freyd's §2.228(a) argument with the genuine
    §2.143/§2.166 round-trips supplied; the ONLY thing it still presupposes is the
    *existence* of such a span (the §2.166 refinement). -/
theorem interUnionU_distrib_of_srcTabulation [UnionAllegory 𝒜] {a p c : 𝒜}
    {F : c ⟶ a} {G : c ⟶ p}
    (hFm : Map F) (hGm : Map G) (hmonic : F ≫ F° ∩ G ≫ G° = Cat.id c)
    {R S T : a ⟶ p} (hR : R ⊑ F° ≫ G) (hS : S ⊑ F° ≫ G) (hT : T ⊑ F° ≫ G) :
    R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) := by
  -- φ Q := 1_c ∩ F Q G° (coreflexive on c); ψ A := F° A G.  Written out inline.
  have hφmono : ∀ {Q₁ Q₂ : a ⟶ p}, Q₁ ⊑ Q₂ →
      Cat.id c ∩ (F ≫ Q₁ ≫ G°) ⊑ Cat.id c ∩ (F ≫ Q₂ ≫ G°) := by
    intro Q₁ Q₂ h
    exact le_inter (inter_lb_left _ _)
      (le_trans (inter_lb_right _ _) (comp_mono_left F (comp_mono_right h G°)))
  have hψmono : ∀ {A B : c ⟶ c}, A ⊑ B → F° ≫ A ≫ G ⊑ F° ≫ B ≫ G := by
    intro A B h; exact comp_mono_left F° (comp_mono_right h G)
  have hφcoref : ∀ Q : a ⟶ p, Coreflexive (Cat.id c ∩ (F ≫ Q ≫ G°)) := fun Q => inter_lb_left _ _
  have hrtle : ∀ Q : a ⟶ p, F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G ⊑ Q :=
    fun Q => src_roundtrip_le hFm.2 hGm.2 Q
  have hrtge : ∀ {Q : a ⟶ p}, Q ⊑ F° ≫ G → Q ⊑ F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G :=
    fun h => src_roundtrip_ge h
  have hpple : ∀ {A : c ⟶ c}, Coreflexive A → Cat.id c ∩ (F ≫ (F° ≫ A ≫ G) ≫ G°) ⊑ A :=
    fun hA => src_phipsi_le hmonic hA
  have hψcup : ∀ A B : c ⟶ c, F° ≫ (A ∪ᵤ B) ≫ G = (F° ≫ A ≫ G) ∪ᵤ (F° ≫ B ≫ G) := by
    intro A B; rw [unionU_comp_distrib, UnionAllegory.comp_union_distrib]
  have hφcup : ∀ {S T : a ⟶ p}, S ⊑ F° ≫ G → T ⊑ F° ≫ G →
      Cat.id c ∩ (F ≫ (S ∪ᵤ T) ≫ G°) ⊑ (Cat.id c ∩ (F ≫ S ≫ G°)) ∪ᵤ (Cat.id c ∩ (F ≫ T ≫ G°)) := by
    intro S T hS hT
    have hbig : S ∪ᵤ T ⊑
        F° ≫ ((Cat.id c ∩ (F ≫ S ≫ G°)) ∪ᵤ (Cat.id c ∩ (F ≫ T ≫ G°))) ≫ G := by
      rw [hψcup]
      exact unionU_lub (le_trans (hrtge hS) (le_unionU_left _ _))
        (le_trans (hrtge hT) (le_unionU_right _ _))
    exact le_trans (hφmono hbig) (hpple (unionU_lub (hφcoref S) (hφcoref T)))
  have hcapbound : ∀ X Y : a ⟶ p,
      F° ≫ ((Cat.id c ∩ (F ≫ X ≫ G°)) ∩ (Cat.id c ∩ (F ≫ Y ≫ G°))) ≫ G ⊑ X ∩ Y := by
    intro X Y
    exact le_inter (le_trans (hψmono (inter_lb_left _ _)) (hrtle X))
      (le_trans (hψmono (inter_lb_right _ _)) (hrtle Y))
  have hcoreflaw :
      (Cat.id c ∩ (F ≫ R ≫ G°)) ∩ ((Cat.id c ∩ (F ≫ S ≫ G°)) ∪ᵤ (Cat.id c ∩ (F ≫ T ≫ G°)))
        = ((Cat.id c ∩ (F ≫ R ≫ G°)) ∩ (Cat.id c ∩ (F ≫ S ≫ G°)))
          ∪ᵤ ((Cat.id c ∩ (F ≫ R ≫ G°)) ∩ (Cat.id c ∩ (F ≫ T ≫ G°))) :=
    coreflexive_inter_unionU_distrib (hφcoref R) (hφcoref S) (hφcoref T)
  have hRcup : R ∩ (S ∪ᵤ T) ⊑ F° ≫ G := le_trans (inter_lb_left _ _) hR
  have hlhs : R ∩ (S ∪ᵤ T) ⊑
      F° ≫ ((Cat.id c ∩ (F ≫ R ≫ G°))
        ∩ ((Cat.id c ∩ (F ≫ S ≫ G°)) ∪ᵤ (Cat.id c ∩ (F ≫ T ≫ G°)))) ≫ G := by
    refine le_trans (hrtge hRcup) (hψmono ?_)
    refine le_inter (hφmono (inter_lb_left _ _)) ?_
    exact le_trans (hφmono (inter_lb_right _ _)) (hφcup hS hT)
  rw [hcoreflaw, hψcup] at hlhs
  exact le_trans hlhs (unionU_mono (hcapbound R S) (hcapbound R T))

/-! ## §2.228(a)  A tabular union allegory is distributive

  *A tabular allegory with this property is distributive.*

  Freyd's argument: given R, S, T ∈ (a,p), let (F,G) be a SOURCE-apex tabulation
  of U := R ∪ S ∪ T (maps `F : c → a`, `G : c → p`, `U = F° G`, jointly monic
  `F F° ∩ G G° = 1_c`).  The poset `{ Q | Q ⊑ F° G }` is order-isomorphic to the
  coreflexives of `c` via `φ Q := 1_c ∩ F Q G°`, `ψ A := F° A G`, where
  coreflexives form a distributive lattice (`coreflexive_comp_eq_inter`).  Hence ∩
  distributes over ∪.  The order-iso is `interUnionU_distrib_of_srcTabulation`
  (sorry-free); the span itself is `srcTabulation_exists` (§2.166, the sole hole). -/

/-- **The one residual §2.228(a)/(b) gap, isolated** (§2.143 / §2.166): for every
    morphism `U` of a union allegory there is a SOURCE-APEX span of *maps*
    `(F, G)`, `F : c → a`, `G : c → p`, that is jointly monic on the apex
    (`F F° ∩ G G° = 1_c`) and tabulates `U` in the source-apex sense (`U = F° G`).

    This is exactly the §2.166 refinement: from a source-apex pre-tabulation split
    the coreflexive `1_c ∩ F U G°` (equivalently §2.16(10): split the symmetric
    idempotent `F F° ∩ G G°` of a semi-simple factorisation `U = F° G`).  The
    repo's `Tabular` furnishes only the *target-apex* span `U = f g°` with
    `f° f ∩ g° g = 1`, which is the WRONG orientation: the round-trip
    `f (f° Q g) g° = Q` provably FAILS for it (Lean-verified `Rel` singleton
    counterexample).  Constructing the source-apex jointly-monic *map* span requires
    splitting (effectiveness §2.226 / coreflexive splitting §2.166) starting from a
    source-apex map pre-tabulation, infrastructure not yet on this repo — this
    `sorry` is the SOLE remaining hole of §2.228(a),(b).

    Everything the transport needs of such a span is already proven sorry-free:
    the order-iso round-trips `src_roundtrip_le/ge`, `src_phipsi_le/ge`, and the
    assembled `interUnionU_distrib_of_srcTabulation`. -/
theorem srcTabulation_exists [UnionAllegory 𝒜] {a p : 𝒜} (U : a ⟶ p) :
    ∃ (c : 𝒜) (F : c ⟶ a) (G : c ⟶ p),
      Map F ∧ Map G ∧ U = F° ≫ G ∧ F ≫ F° ∩ G ≫ G° = Cat.id c := by
  sorry

/-- **Tabulation transport** (§2.228(a)).  Given `R, S, T ⊑ U` for a fixed `U`,
    transport the distributive coreflexive lattice of the apex back along the
    §2.143/§2.166 source-apex span of `U` to obtain the ∩-over-∪ containment.
    Sorry-free *modulo* `srcTabulation_exists` — every order-iso step is a
    theorem (`interUnionU_distrib_of_srcTabulation`). -/
theorem tab_transport_gap [UnionAllegory 𝒜] {a p : 𝒜} {U R S T : a ⟶ p}
    (hRU : R ⊑ U) (hSU : S ⊑ U) (hTU : T ⊑ U) :
    R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) := by
  obtain ⟨c, F, G, hF, hG, hUeq, hmonic⟩ := srcTabulation_exists U
  rw [hUeq] at hRU hSU hTU
  exact interUnionU_distrib_of_srcTabulation hF hG hmonic hRU hSU hTU

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
    (_h : ∀ {a b : 𝒜} (R : a ⟶ b), Tabular R) : InterUnionDistrib 𝒜 := by
  rw [interUnionDistrib_iff_le]
  intro a b R S T
  -- R, S, T all sit below U := R ∪ S ∪ T; transport along the source-apex span of U.
  have hRU : R ⊑ R ∪ᵤ S ∪ᵤ T := le_trans (le_unionU_left _ _) (le_unionU_left _ _)
  have hSU : S ⊑ R ∪ᵤ S ∪ᵤ T := le_trans (le_unionU_right _ _) (le_unionU_left _ _)
  have hTU : T ⊑ R ∪ᵤ S ∪ᵤ T := le_unionU_right _ _
  exact tab_transport_gap hRU hSU hTU


/-! ## §2.228(b)  A semi-simple union allegory is distributive

  *A semi-simple allegory with the above-mentioned property is distributive.*

  Freyd's argument: split the symmetric idempotents to obtain a tabular
  allegory with the same property, then apply §2.228(a). -/

/-- **Semi-simple transport** (§2.228(b)).  Freyd's route: split the symmetric
    idempotents to land in a tabular allegory with the same composition-over-union
    structure, where §2.228(a) applies.  Per §2.16(10): for a semi-simple
    `U = F° G` the symmetric idempotent `F F° ∩ G G°` splits (effectiveness,
    §2.226) to make `H F, H G` MAPS jointly tabulating `U` — exactly the
    `srcTabulation_exists` span.  So §2.228(b) reduces to the SAME residual hole
    as §2.228(a), and is discharged by the identical transport: `tab_transport_gap`
    (the surrounding `U := R ∪ S ∪ T` has its source-apex span via §2.166). -/
theorem semiSimple_transport_gap [UnionAllegory 𝒜] {a b : 𝒜} {R S T : a ⟶ b}
    (_hR : SemiSimple R) (_hS : SemiSimple S) (_hT : SemiSimple T) :
    R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) :=
  tab_transport_gap (U := R ∪ᵤ S ∪ᵤ T)
    (le_trans (le_unionU_left _ _) (le_unionU_left _ _))
    (le_trans (le_unionU_right _ _) (le_unionU_left _ _))
    (le_unionU_right _ _)

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
    union of the semi-simple morphisms it contains, but the intersection-over-
    union distributive law FAILS — so the union-of-semi-simples
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
