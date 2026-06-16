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

/-! ### The intersection-over-union law as a property

  In a `UnionAllegory` the law `R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)` is *not*
  assumed.  We isolate it as a predicate `InterUnionDistrib`; "is a
  distributive allegory" for a union allegory means exactly that this law
  holds (the remaining distributive-allegory axioms are already present). -/

/-- The intersection-over-union distributive law of §2.21, as a property of
    a union allegory.  When this holds, the union allegory is distributive. -/
def InterUnionDistrib (𝒜 : Type u) [UnionAllegory 𝒜] : Prop :=
  ∀ {a b : 𝒜} (R S T : a ⟶ b), R ∩ (S ∪ᵤ T) = (R ∩ S) ∪ᵤ (R ∩ T)

/-! ## §2.228(a)  A tabular union allegory is distributive

  *A tabular allegory with this property is distributive.*

  Freyd's argument: given R, S, T ∈ (a,p), let (f,g) tabulate R ∪ S ∪ T.
  The poset { Q | Q ⊑ f°g } is isomorphic to the coreflexives of □f, where
  coreflexives form a distributive lattice (intersection and composition of
  coreflexives coincide).  Hence ∩ distributes over ∪. -/

/-- **§2.228(a)**: a tabular union allegory satisfies the intersection-over-
    union distributive law, hence is distributive.

    FAITHFUL SORRY: the proof requires Freyd's tabulation argument
    (isomorphism of `{Q | Q ⊑ f°g}` with the distributive lattice of
    coreflexives of `□f`), which is not yet available on this repo's
    allegory infrastructure. -/
theorem interUnionDistrib_of_tabular [UnionAllegory 𝒜]
    (h : ∀ {a b : 𝒜} (R : a ⟶ b), Tabular R) : InterUnionDistrib 𝒜 := by
  sorry

/-! ## §2.228(b)  A semi-simple union allegory is distributive

  *A semi-simple allegory with the above-mentioned property is distributive.*

  Freyd's argument: split the symmetric idempotents to obtain a tabular
  allegory with the same property, then apply §2.228(a). -/

/-- **§2.228(b)**: a semi-simple union allegory satisfies the
    intersection-over-union distributive law, hence is distributive.

    FAITHFUL SORRY: Freyd reduces this to §2.228(a) by splitting symmetric
    idempotents (the systemic/tabular completion), infrastructure not yet
    available here. -/
theorem interUnionDistrib_of_semiSimple [UnionAllegory 𝒜]
    (h : ∀ {a b : 𝒜} (R : a ⟶ b), SemiSimple R) : InterUnionDistrib 𝒜 := by
  sorry

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

/-- **§2.228(c)**: there is a union allegory in which every morphism is the
    union of the semi-simple morphisms it contains, but the intersection-
    over-union distributive law FAILS — so the union-of-semi-simples
    hypothesis alone does not force distributivity (in contrast to the
    tabular and semi-simple hypotheses of (a),(b)).

    FAITHFUL SORRY: the witness is Freyd's group construction (G a group with
    |G| > 2, adjoin 0 and a maximal M).  Building it as an `Allegory`/
    `UnionAllegory` instance and verifying non-distributivity is a sizable
    explicit construction left as future work. -/
theorem exists_unionOfSemiSimple_not_distributive :
    ∃ (𝒜 : Type) (_ : UnionAllegory 𝒜),
      (∀ {a b : 𝒜} (R : a ⟶ b), UnionOfSemiSimpleUA R) ∧ ¬ InterUnionDistrib 𝒜 := by
  sorry

end Freyd.Alg
