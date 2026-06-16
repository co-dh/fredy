/-
  Freyd & Scedrov, *Categories, Allegories* §1.77–§1.78

  §1.77   TRANSITIVE CLOSURE R^t; TRANSITIVE-REFLEXIVE CLOSURE R*.
          Relations between R^t and R* in a pre-logos.
          TRANSITIVE (PRE-)LOGOS.
  §1.772  ω-TRANSITIVE LOGOS / ω-TRANSITIVE PRE-LOGOS.
  §1.775  EQUIVALENCE CLOSURE R^E; E-STANDARD pre-logos.
  §1.78   Relational quotient R/S (largest T with TS ⊑ R).
  §1.781  Set description of R/S.
  §1.782  R/f = Rf° (quotient by a map).
  §1.783  (R/S₁)/S₂ = R/(S₁S₂).
  §1.786  (R/S)(S/T) ⊑ R/T.
  §1.787  In a logos, R̄ = R* (closure via quotient equals transitive-reflexive closure).
-/

import Fredy.S1_56
import Fredy.S1_60

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.77 Transitive and transitive-reflexive closures -/

/-- An endo-relation R on A is TRANSITIVE if R ⊚ R ⊑ R (§1.77). -/
def IsTransitive [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) : Prop :=
  RelLe (R ⊚ R) R

/-- An endo-relation R on A is REFLEXIVE if 1_A ⊑ R (§1.77). -/
def IsReflexive {A : 𝒞} (R : BinRel 𝒞 A A) : Prop :=
  RelLe (graph (Cat.id A)) R

/-- TRANSITIVE CLOSURE R^t (§1.77): minimum transitive relation containing R.
    Existence is not guaranteed in every regular category. -/
structure TransClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) where
  clos    : BinRel 𝒞 A A
  le      : RelLe R clos
  trans   : IsTransitive clos
  minimal : ∀ (T : BinRel 𝒞 A A), RelLe R T → IsTransitive T → RelLe clos T

/-- TRANSITIVE-REFLEXIVE CLOSURE R* (§1.77): minimum reflexive-transitive relation ⊇ R. -/
structure TransRefClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) where
  clos    : BinRel 𝒞 A A
  le      : RelLe R clos
  refl    : IsReflexive clos
  trans   : IsTransitive clos
  minimal : ∀ (T : BinRel 𝒞 A A), RelLe R T → IsReflexive T → IsTransitive T → RelLe clos T

/-! ## §1.77 R^t ⊑ R* when both exist -/

/-- §1.77: R^t ⊑ R* (transitive closure contained in transitive-reflexive closure). -/
theorem transClos_le_transRefClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (ht : TransClos R) (hr : TransRefClos R) :
    RelLe ht.clos hr.clos :=
  ht.minimal hr.clos hr.le hr.trans

/-! ## §1.77 Transitive (pre-)logos -/

/-- A TRANSITIVE PRE-LOGOS (§1.77): every endo-relation has a transitive closure. -/
class TransitivePreLogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    extends PreLogos 𝒞 where
  transClos : ∀ {A : 𝒞} (R : BinRel 𝒞 A A), TransClos R

set_option linter.unusedVariables false in
/-- A TRANSITIVE LOGOS (§1.77): transitive pre-logos with right adjoint f##.
    We inline the logos axiom (f## existence) to avoid importing S1_70. -/
class TransitiveLogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    extends TransitivePreLogos 𝒞 where
  rightAdj  : ∀ {A B : 𝒞} (f : A ⟶ B), Subobject 𝒞 A → Subobject 𝒞 B
  adjunction : ∀ {A B : 𝒞} (f : A ⟶ B) (B' : Subobject 𝒞 B) (A' : Subobject 𝒞 A),
    Subobject.le (InverseImage f B') A' ↔ Subobject.le B' (rightAdj f A')

/-! ## §1.772 ω-Transitive logos / ω-transitive pre-logos -/

/-- Relational power R^n (diagram order): R^0 = 1_A, R^(n+1) = R^n ⊚ R. -/
def relPow [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (n : Nat) : BinRel 𝒞 A A :=
  Nat.rec (graph (Cat.id A)) (fun _ rec => rec ⊚ R) n

theorem relPow_zero [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) : relPow R 0 = graph (Cat.id A) := rfl

theorem relPow_succ [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (n : Nat) : relPow R (n + 1) = relPow R n ⊚ R := rfl

/-- An ω-TRANSITIVE LOGOS (§1.772): transitive logos in which R^t is
    the least upper bound of the positive finite powers {R^n | n ≥ 1}. -/
class OmegaTransitiveLogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    extends TransitiveLogos 𝒞 where
  pow_le_transClos : ∀ {A : 𝒞} (R : BinRel 𝒞 A A) (n : Nat), 1 ≤ n →
    RelLe (relPow R n) (transClos R).clos
  transClos_le_of_pow_le : ∀ {A : 𝒞} (R : BinRel 𝒞 A A) (T : BinRel 𝒞 A A),
    (∀ n : Nat, 1 ≤ n → RelLe (relPow R n) T) → RelLe (transClos R).clos T

/-- An ω-TRANSITIVE PRE-LOGOS (§1.772): transitive pre-logos in which R^t is
    the STABLE least upper bound of {R^n | n ≥ 1}.
    Stability: the countable union is preserved under all inverse images f#. -/
class OmegaTransitivePreLogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    extends TransitivePreLogos 𝒞 where
  pow_le_transClos : ∀ {A : 𝒞} (R : BinRel 𝒞 A A) (n : Nat), 1 ≤ n →
    RelLe (relPow R n) (transClos R).clos
  transClos_stable_lub : ∀ {A : 𝒞} (R : BinRel 𝒞 A A) (T : BinRel 𝒞 A A),
    (∀ n : Nat, 1 ≤ n → RelLe (relPow R n) T) → RelLe (transClos R).clos T

/-! ## §1.775 Equivalence closure R^E and E-standard pre-logos -/

/-- R is SYMMETRIC if R° ⊑ R. -/
def IsSymmetric {A : 𝒞} (R : BinRel 𝒞 A A) : Prop :=
  RelLe (R°) R

/-- R is an EQUIVALENCE RELATION: reflexive, symmetric, transitive. -/
def IsEquivRel [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) : Prop :=
  IsReflexive R ∧ IsSymmetric R ∧ IsTransitive R

/-- EQUIVALENCE CLOSURE R^E (§1.775): minimum equivalence relation containing R. -/
structure EquivClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) where
  clos    : BinRel 𝒞 A A
  le      : RelLe R clos
  isEquiv : IsEquivRel clos
  minimal : ∀ (E : BinRel 𝒞 A A), RelLe R E → IsEquivRel E → RelLe clos E

/-- Reciprocal is monotone: R ⊑ S → R° ⊑ S°.
    The RelHom witness for R ⊑ S also witnesses R° ⊑ S° with its column equations swapped. -/
theorem reciprocal_monotone {A B : 𝒞} {R S : BinRel 𝒞 A B} (h : RelLe R S) :
    RelLe (R°) (S°) := by
  rcases h with ⟨⟨w, hA, hB⟩⟩; exact ⟨⟨w, hB, hA⟩⟩

/-- The reciprocal of the diagonal is the diagonal: graph(id) ⊑ (graph(id))°.
    Both have colA = colB = id, so the identity RelHom witnesses the containment. -/
theorem graph_id_le_reciprocal {A : 𝒞} :
    RelLe (graph (Cat.id A)) ((graph (Cat.id A))°) :=
  ⟨⟨Cat.id _, by simp [graph, reciprocal, Cat.id_comp], by simp [graph, reciprocal, Cat.id_comp]⟩⟩

/-- §1.775: In a transitive pre-logos, R^E is constructible as (R ∪ R°)*.
    Stated: given a relation Rsym with R ⊑ Rsym, R° ⊑ Rsym, 1 ⊑ Rsym,
    and Rsym is symmetric, any TransRefClos of Rsym gives an EquivClos of R.
    `hJoin` records that Rsym is the JOIN of R, R° and 1 (its universal property as the
    symmetrisation), which is what makes the equivalence-closure minimality go through. -/
def equivClos_from_symm_transRefClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (Rsym : BinRel 𝒞 A A)
    (hR   : RelLe R Rsym)
    (hSym : IsSymmetric Rsym)
    (hJoin : ∀ (U : BinRel 𝒞 A A),
      RelLe R U → RelLe (R°) U → RelLe (graph (Cat.id A)) U → RelLe Rsym U)
    (hr   : TransRefClos Rsym) :
    EquivClos R where
  clos    := hr.clos
  le      := rel_le_trans hR hr.le
  isEquiv := ⟨hr.refl, by
    -- Rsym* is symmetric: (Rsym*)° ⊑ Rsym*.
    -- The candidate (Rsym*)° is itself reflexive, transitive and contains Rsym, so by
    -- minimality Rsym* ⊑ (Rsym*)°; reciprocate (and use involution) to flip the direction.
    have hle : RelLe hr.clos (hr.clos°) := by
      apply hr.minimal
      · -- Rsym ⊑ (Rsym*)°:  Rsym° ⊑ Rsym ⊑ Rsym*, reciprocate and use involution.
        have h1 : RelLe (Rsym°) hr.clos := rel_le_trans hSym hr.le
        have h2 : RelLe (Rsym°°) (hr.clos°) := reciprocal_monotone h1
        rwa [reciprocal_invol] at h2
      · -- (Rsym*)° reflexive:  graph(id) ⊑ (graph(id))° ⊑ (Rsym*)°.
        exact rel_le_trans graph_id_le_reciprocal (reciprocal_monotone hr.refl)
      · -- (Rsym*)° transitive:  (Rsym*)°(Rsym*)° ⊑ (Rsym* Rsym*)° ⊑ (Rsym*)°.
        exact rel_le_trans (comp_reciprocal_le hr.clos hr.clos) (reciprocal_monotone hr.trans)
    have h3 : RelLe (hr.clos°) (hr.clos°°) := reciprocal_monotone hle
    rwa [reciprocal_invol] at h3,
   hr.trans⟩
  minimal := by
    intro E hRE hEquiv
    apply hr.minimal
    · -- Rsym ⊑ E: R ⊑ E (hRE), R° ⊑ E (R ⊑ E reciprocated, E symmetric), 1 ⊑ E (E reflexive).
      apply hJoin
      · exact hRE
      · -- R° ⊑ E:  R° ⊑ E° ⊑ E  (E symmetric).
        exact rel_le_trans (reciprocal_monotone hRE) hEquiv.2.1
      · exact hEquiv.1
    · exact hEquiv.1
    · exact hEquiv.2.2

/-- An E-STANDARD PRE-LOGOS (§1.775): every endo-relation has an equivalence closure,
    and R^E is the stable union of finite powers of the symmetrisation. -/
class EStandardPreLogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    extends PreLogos 𝒞 where
  equivClos : ∀ {A : 𝒞} (R : BinRel 𝒞 A A), EquivClos R
  equivClos_stable_lub : ∀ {A : 𝒞} (R : BinRel 𝒞 A A) (Rsym T : BinRel 𝒞 A A),
    RelLe R Rsym → RelLe (graph (Cat.id A)) Rsym → RelLe (Rsym°) Rsym →
    (∀ n : Nat, RelLe (relPow Rsym n) T) →
    RelLe (equivClos R).clos T

/-! ## §1.78 Relational quotient R/S -/

/-- RELATIONAL QUOTIENT R/S (§1.78): given R : A → C and S : B → C,
    R/S is the maximum T : A → B with T ⊚ S ⊑ R.
    Universal property: T ⊑ R/S ↔ T ⊚ S ⊑ R. -/
structure RelQuot [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A B C : 𝒞} (R : BinRel 𝒞 A C) (S : BinRel 𝒞 B C) where
  quot    : BinRel 𝒞 A B
  le      : RelLe (quot ⊚ S) R
  maximal : ∀ (T : BinRel 𝒞 A B), RelLe (T ⊚ S) R → RelLe T quot

/-- Compose is monotone in the left argument: R ⊑ S → R ⊚ T ⊑ S ⊚ T.
    This is `compose_le_left` from S1_56. -/
theorem relLe_comp_right [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A B C : 𝒞} {R S : BinRel 𝒞 A B} (h : RelLe R S) (T : BinRel 𝒞 B C) :
    RelLe (R ⊚ T) (S ⊚ T) :=
  compose_le_left h T

/-- §1.78 universal property: T ⊑ R/S ↔ T ⊚ S ⊑ R. -/
theorem relQuot_iff [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A B C : 𝒞} {R : BinRel 𝒞 A C} {S : BinRel 𝒞 B C}
    (q : RelQuot R S) (T : BinRel 𝒞 A B) :
    RelLe T q.quot ↔ RelLe (T ⊚ S) R := by
  constructor
  · intro hT; exact rel_le_trans (relLe_comp_right hT S) q.le
  · exact q.maximal T

/-! ## §1.781 Set description

  In 𝒮et: x(R/S)y iff ∀z, ySz → xRz.
  This is exactly the categorical universal property (relQuot_iff):
  T ⊑ R/S ↔ TS ⊑ R. -/

/-! ## §1.782 R/f = R ⊚ f° -/

/-- §1.782: R/(graph f) is represented by R ⊚ (graph f)°.
    Proof: Tf ⊑ R ↔ T ⊑ Rf°, using simplicity (f°f ⊑ 1) and entireness (1 ⊑ ff°) of graph f.
    Requires composition associativity (regular category). -/
def relQuotByMap [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A B C : 𝒞} (R : BinRel 𝒞 A C) (f : B ⟶ C) : RelQuot R (graph f) where
  quot    := R ⊚ (graph f)°
  le      := by
    -- Goal: (R ⊚ (graph f)°) ⊚ (graph f) ⊑ R
    -- = R ⊚ ((graph f)° ⊚ (graph f)) ⊑ R ⊚ graph(id) ⊑ R
    -- via: assoc, simplicity of (graph f), right unit
    have h_assoc : RelLe ((R ⊚ (graph f)°) ⊚ graph f) (R ⊚ ((graph f)° ⊚ graph f)) :=
      compose_assoc R ((graph f)°) (graph f)
    -- Simple (graph f) : (graph f)° ⊚ (graph f) ⊑ graph(id_C) where C is target of graph f
    have h_simp_le : RelLe ((graph f)° ⊚ graph f) (graph (Cat.id C)) := (graph_is_map f).2
    have h_step2 : RelLe (R ⊚ ((graph f)° ⊚ graph f)) (R ⊚ graph (Cat.id C)) :=
      compose_le (rel_le_refl R) h_simp_le
    have h_unit : RelLe (R ⊚ graph (Cat.id C)) R := comp_graph_id R
    exact rel_le_trans (rel_le_trans h_assoc h_step2) h_unit
  maximal := by
    intro T hTf
    -- Goal: T ⊑ R ⊚ (graph f)°
    -- T ⊑ T ⊚ graph(id_B) ⊑ T ⊚ ((graph f) ⊚ (graph f)°)  [entireness]
    --   ⊑ (T ⊚ (graph f)) ⊚ (graph f)°                       [assoc']
    --   ⊑ R ⊚ (graph f)°                                       [hTf + monotone]
    -- Entire (graph f) : graph(id_B) ⊑ (graph f) ⊚ (graph f)°  (B = source of graph f)
    have h_ent_le : RelLe (graph (Cat.id B)) (graph f ⊚ (graph f)°) := (graph_is_map f).1
    have h_step1 : RelLe T (T ⊚ graph (Cat.id B)) := comp_graph_id_right T
    have h_step2 : RelLe (T ⊚ graph (Cat.id B)) (T ⊚ (graph f ⊚ (graph f)°)) :=
      compose_le (rel_le_refl T) h_ent_le
    have h_step3 : RelLe (T ⊚ (graph f ⊚ (graph f)°)) ((T ⊚ graph f) ⊚ (graph f)°) :=
      compose_assoc' T (graph f) ((graph f)°)
    have h_step4 : RelLe ((T ⊚ graph f) ⊚ (graph f)°) (R ⊚ (graph f)°) :=
      compose_le_left hTf ((graph f)°)
    exact rel_le_trans h_step1 (rel_le_trans h_step2 (rel_le_trans h_step3 h_step4))

/-- §1.782: T ⊑ R/(graph f) ↔ T ⊚ (graph f) ⊑ R. -/
theorem relQuot_map_iff [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A B C : 𝒞} (R : BinRel 𝒞 A C) (f : B ⟶ C) (T : BinRel 𝒞 A B) :
    RelLe T (relQuotByMap R f).quot ↔ RelLe (T ⊚ graph f) R :=
  relQuot_iff (relQuotByMap R f) T

/-! ## §1.783 (R/S₁)/S₂ = R/(S₂ ⊚ S₁) -/

/-- §1.783: T ⊑ (R/S₁)/S₂ ↔ T ⊑ R/(S₂ ⊚ S₁).
    Book proof: T ⊑ (R/S₁)/S₂ ↔ TS₂ ⊑ R/S₁ ↔ TS₂S₁ ⊑ R ↔ T(S₂S₁) ⊑ R ↔ T ⊑ R/(S₂S₁). -/
theorem relQuot_assoc_iff [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A B C D : 𝒞}
    (R : BinRel 𝒞 A D) (S₁ : BinRel 𝒞 C D) (S₂ : BinRel 𝒞 B C)
    (q₁  : RelQuot R S₁)
    (q₂  : RelQuot q₁.quot S₂)
    (q₁₂ : RelQuot R (S₂ ⊚ S₁))
    (T : BinRel 𝒞 A B) :
    RelLe T q₂.quot ↔ RelLe T q₁₂.quot := by
  -- T ⊑ q₂.quot ↔ T ⊚ S₂ ⊑ q₁.quot ↔ (T ⊚ S₂) ⊚ S₁ ⊑ R
  -- T ⊑ q₁₂.quot ↔ T ⊚ (S₂ ⊚ S₁) ⊑ R
  -- These are equal by compose_assoc / compose_assoc'.
  constructor
  · intro h
    rw [relQuot_iff q₁₂]
    exact rel_le_trans (compose_assoc' T S₂ S₁) ((relQuot_iff q₁ _).mp ((relQuot_iff q₂ _).mp h))
  · intro h
    rw [relQuot_iff q₂, relQuot_iff q₁]
    exact rel_le_trans (compose_assoc T S₂ S₁) ((relQuot_iff q₁₂ _).mp h)

/-! ## §1.786 (R/S)(S/T) ⊑ R/T -/

/-- §1.786: (R/S) ⊚ (S/T) ⊑ R/T.
    Proof: ((R/S)(S/T)) ⊚ T ⊑ (R/S) ⊚ ((S/T) ⊚ T) ⊑ (R/S) ⊚ S ⊑ R. -/
theorem relQuot_comp_le [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A B C D : 𝒞}
    (R : BinRel 𝒞 A D) (S : BinRel 𝒞 B D) (T : BinRel 𝒞 C D)
    (qRS : RelQuot R S) (qST : RelQuot S T) (qRT : RelQuot R T) :
    RelLe (qRS.quot ⊚ qST.quot) qRT.quot := by
  apply qRT.maximal
  -- ((R/S) ⊚ (S/T)) ⊚ T ⊑ R.
  -- Step 1: ((R/S) ⊚ (S/T)) ⊚ T ⊑ (R/S) ⊚ ((S/T) ⊚ T)  [assoc]
  -- Step 2: (S/T) ⊚ T ⊑ S                                  [qST.le]
  -- Step 3: (R/S) ⊚ ((S/T) ⊚ T) ⊑ (R/S) ⊚ S              [monotone in right]
  -- Step 4: (R/S) ⊚ S ⊑ R                                   [qRS.le]
  have h1 : RelLe ((qRS.quot ⊚ qST.quot) ⊚ T) (qRS.quot ⊚ (qST.quot ⊚ T)) :=
    compose_assoc qRS.quot qST.quot T
  have h2 : RelLe (qRS.quot ⊚ (qST.quot ⊚ T)) (qRS.quot ⊚ S) :=
    compose_le (rel_le_refl qRS.quot) qST.le
  exact rel_le_trans h1 (rel_le_trans h2 qRS.le)

/-- §1.786: R/R is reflexive: graph(id) ⊑ R/R. -/
theorem relQuot_self_refl [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (qRR : RelQuot R R) :
    IsReflexive qRR.quot := by
  apply qRR.maximal
  -- graph(id_A) ⊚ R ⊑ R: identity is a left unit for composition.
  exact graph_id_comp R

/-- §1.786: R/R is transitive: (R/R) ⊚ (R/R) ⊑ R/R. -/
theorem relQuot_self_trans [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (qRR : RelQuot R R) :
    IsTransitive qRR.quot :=
  relQuot_comp_le R R R qRR qRR qRR

/-! ## §1.787 In a logos, R̄ = R* -/

/-- R̄ (§1.787): minimum reflexive S with R ⊚ S ⊑ S ("right-quotient closure"). -/
structure QuotClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) where
  clos    : BinRel 𝒞 A A
  refl    : IsReflexive clos
  stable  : RelLe (R ⊚ clos) clos
  minimal : ∀ (S : BinRel 𝒞 A A), IsReflexive S → RelLe (R ⊚ S) S → RelLe clos S

/-- §1.787: R* satisfies R ⊚ R* ⊑ R*. -/
theorem transRefClos_stable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (hr : TransRefClos R) :
    RelLe (R ⊚ hr.clos) hr.clos :=
  -- R ⊚ R* ⊑ R* ⊚ R* ⊑ R* (using R ⊑ R* and R* transitivity)
  rel_le_trans (relLe_comp_right hr.le hr.clos) hr.trans

/-- §1.787: R̄ ⊑ R* (R* is reflexive and satisfies R ⊚ R* ⊑ R*). -/
theorem quotClos_le_transRefClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (hr : TransRefClos R) (qBar : QuotClos R) :
    RelLe qBar.clos hr.clos :=
  qBar.minimal hr.clos hr.refl (transRefClos_stable R hr)

/-- §1.787: R ⊑ R̄ (R̄ contains R).
    R ⊑ R ⊚ graph(id) ⊑ R ⊚ R̄ ⊑ R̄ (using R̄ reflexive and qBar.stable). -/
theorem le_quotClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (qBar : QuotClos R) :
    RelLe R qBar.clos :=
  rel_le_trans (comp_graph_id_right R)
    (rel_le_trans (compose_le (rel_le_refl R) qBar.refl) qBar.stable)

/-- §1.787: R* ⊑ R̄ — the reflexive-transitive closure is contained in the quotient closure.
    Book proof (§1.787, first half): with S = R̄ (reflexive, R·S ⊑ S), the self-quotient S/S
    is reflexive and transitive, and R ⊑ S/S (since R·S ⊑ S), so by minimality of R*,
    R* ⊑ S/S.  Hence R*·S ⊑ (S/S)·S ⊑ S, and R* = R*·1 ⊑ R*·S ⊑ S.
    Needs a RelQuot R̄ R̄ (self-quotient S/S; exists in a logos by §1.784) and assoc. -/
theorem transRefClos_le_quotClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (hr : TransRefClos R) (qBar : QuotClos R) (qSS : RelQuot qBar.clos qBar.clos) :
    RelLe hr.clos qBar.clos := by
  -- S := qBar.clos = R̄.  S/S := qSS.quot.
  -- R ⊑ S/S: by univ prop of S/S, need R ⊚ S ⊑ S — that is qBar.stable.
  have hR_le_SS : RelLe R qSS.quot := qSS.maximal R qBar.stable
  -- S/S is reflexive and transitive (§1.786).
  have hrefl_SS  : IsReflexive  qSS.quot := relQuot_self_refl  qBar.clos qSS
  have htrans_SS : IsTransitive qSS.quot := relQuot_self_trans qBar.clos qSS
  -- R* ⊑ S/S by minimality of R*.
  have hstar_le_SS : RelLe hr.clos qSS.quot :=
    hr.minimal qSS.quot hR_le_SS hrefl_SS htrans_SS
  -- R*·S ⊑ (S/S)·S ⊑ S.
  have hstarS_le_S : RelLe (hr.clos ⊚ qBar.clos) qBar.clos :=
    rel_le_trans (compose_le_left hstar_le_SS qBar.clos) qSS.le
  -- R* = R*·1 ⊑ R*·S ⊑ S  (S reflexive).
  exact rel_le_trans (comp_graph_id_right hr.clos)
    (rel_le_trans (compose_le (rel_le_refl hr.clos) qBar.refl) hstarS_le_S)

/-- §1.787: R̄ is transitive: R̄ ⊚ R̄ ⊑ R̄.
    Book proof (§1.787): once R* exists, R̄ = R* (mutual containment), and R* is transitive.
    `quotClos_le_transRefClos` gives R̄ ⊑ R*; `transRefClos_le_quotClos` gives R* ⊑ R̄, so
    R̄ ⊚ R̄ ⊑ R* ⊚ R* ⊑ R* ⊑ R̄ using transitivity of R*.
    Needs the self-quotient R̄/R̄ (`qSS`), available in a logos by §1.784. -/
theorem quotClos_is_transitive [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (hr : TransRefClos R) (qBar : QuotClos R) (qSS : RelQuot qBar.clos qBar.clos) :
    IsTransitive qBar.clos := by
  -- R̄ ⊑ R* and R* ⊑ R̄ (mutual containment).
  have h_bar_le_star : RelLe qBar.clos hr.clos := quotClos_le_transRefClos R hr qBar
  have h_star_le_bar : RelLe hr.clos qBar.clos := transRefClos_le_quotClos R hr qBar qSS
  -- R̄·R̄ ⊑ R*·R* ⊑ R* ⊑ R̄.
  exact rel_le_trans (compose_le h_bar_le_star h_bar_le_star)
    (rel_le_trans hr.trans h_star_le_bar)

/-- §1.787 main: R̄ = R* — the quotient closure and transitive-reflexive closure coincide.
    Needs the self-quotient R̄/R̄ (`qSS`), available in a logos by §1.784. -/
theorem quotClos_eq_transRefClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (hr : TransRefClos R) (qBar : QuotClos R) (qSS : RelQuot qBar.clos qBar.clos) :
    RelLe qBar.clos hr.clos ∧ RelLe hr.clos qBar.clos :=
  ⟨quotClos_le_transRefClos R hr qBar, transRefClos_le_quotClos R hr qBar qSS⟩

end Freyd
