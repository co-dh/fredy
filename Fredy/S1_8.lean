/-
  Freyd & Scedrov, *Categories and Allegories* §1.8–§1.81
  Adjoint functors, reflective/coreflective subcategories.

  §1.81  ADJOINT PAIR OF FUNCTORS — hom-set bijection, unit, counit, triangle identities
  §1.813 REFLECTIVE SUBCATEGORY, REFLECTION
  §1.816 COREFLECTIVE INCLUSION
  §1.815 CLOSURE OPERATION (poset case: idempotent, inflationary, order-preserving)
-/

import Fredy.S1_1
import Fredy.S1_18


universe v u u₁ u₂

namespace Freyd

variable {𝒞 : Type u₁} [Cat.{v} 𝒞] {𝒟 : Type u₂} [Cat.{v} 𝒟]

/-! ## §1.81  Adjoint pair of functors

  F : 𝒞 → 𝒟 and G : 𝒟 → 𝒞 form an ADJOINT PAIR if there is a
  natural equivalence (F A ⟶ B) ≃ (A ⟶ G B) (§1.81).
  F = LEFT-ADJOINT of G, G = RIGHT-ADJOINT of F. -/

/-- An adjoint pair F ⊣ G: a bijection (F A ⟶ B) ≃ (A ⟶ G B)
    natural in A (contravariant) and B (covariant) (§1.81). -/
structure Adjunction (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞) [Functor F] [Functor G] where
  φ {A B} (f : F A ⟶ B) : (A ⟶ G B)
  ψ {A B} (f : A ⟶ G B) : (F A ⟶ B)
  φψ {A B} (f : A ⟶ G B) : φ (ψ f) = f
  ψφ {A B} (f : F A ⟶ B) : ψ (φ f) = f
  φ_nat_left {A' A B} (a : A' ⟶ A) (h : F A ⟶ B) : φ (Functor.map a ≫ h) = a ≫ φ h
  φ_nat_right {A B B'} (h : F A ⟶ B) (b : B ⟶ B') : φ (h ≫ b) = φ h ≫ Functor.map b

infix:25 " ⊣ " => Adjunction

/-- F is a LEFT-ADJOINT of G. -/
class LeftAdjoint (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞) [Functor F] [Functor G] where
  adj : F ⊣ G

/-- G is a RIGHT-ADJOINT of F. -/
class RightAdjoint (G : 𝒟 → 𝒞) (F : 𝒞 → 𝒟) [Functor G] [Functor F] where
  adj : F ⊣ G

section AdjunctionProperties
variable {F : 𝒞 → 𝒟} {G : 𝒟 → 𝒞} [Functor F] [Functor G] (adj : F ⊣ G)

theorem φ_inj {A B} {f₁ f₂ : F A ⟶ B} (h : adj.φ f₁ = adj.φ f₂) : f₁ = f₂ := by
  calc
    f₁ = adj.ψ (adj.φ f₁) := by rw [adj.ψφ]
    _ = adj.ψ (adj.φ f₂) := by rw [h]
    _ = f₂ := by rw [adj.ψφ]

/-! ### Derived naturality for ψ (= φ⁻¹) -/

theorem ψ_nat_left {A' A B} (a : A' ⟶ A) (g : A ⟶ G B) :
    adj.ψ (a ≫ g) = Functor.map a ≫ adj.ψ g :=
  φ_inj adj <| by
    rw [adj.φ_nat_left, adj.φψ, adj.φψ]

theorem ψ_nat_right {A B B'} (g : A ⟶ G B) (b : B ⟶ B') :
    adj.ψ (g ≫ Functor.map b) = adj.ψ g ≫ b :=
  φ_inj adj <| by
    rw [adj.φ_nat_right, adj.φψ, adj.φψ]

/-! ### Unit and counit -/

/-- The UNIT η_A : A → G(F A) is the adjoint of id_{F A} (§1.81). -/
def unit (A : 𝒞) : A ⟶ G (F A) := adj.φ (Cat.id (F A))

/-- The COUNIT ε_B : F(G B) → B is the adjoint of id_{G B} (§1.81). -/
def counit (B : 𝒟) : F (G B) ⟶ B := adj.ψ (Cat.id (G B))

/-- Unit naturality: f ≫ η_B = η_A ≫ G(F f). -/
theorem unit_naturality {A B : 𝒞} (f : A ⟶ B) :
    f ≫ unit adj B = unit adj A ≫ Functor.map (Functor.map f) := by
  dsimp [unit]
  calc
    f ≫ adj.φ (Cat.id (F B)) = adj.φ (Functor.map f ≫ Cat.id (F B)) := by
      rw [adj.φ_nat_left]
    _ = adj.φ (Functor.map f) := by rw [Cat.comp_id]
    _ = adj.φ (Cat.id (F A) ≫ Functor.map f) := by rw [Cat.id_comp]
    _ = adj.φ (Cat.id (F A)) ≫ Functor.map (Functor.map f) := by rw [adj.φ_nat_right]

/-- Counit naturality: F(G f) ≫ ε_B = ε_A ≫ f. -/
theorem counit_naturality {A B : 𝒟} (f : A ⟶ B) :
    Functor.map (Functor.map f) ≫ counit adj B = counit adj A ≫ f := by
  dsimp [counit]
  calc
    Functor.map (Functor.map f) ≫ adj.ψ (Cat.id (G B)) =
      adj.ψ (Functor.map f ≫ Cat.id (G B)) := by
      rw [← ψ_nat_left adj (Functor.map f) (Cat.id (G B))]
    _ = adj.ψ (Functor.map f) := by rw [Cat.comp_id]
    _ = adj.ψ (Cat.id (G A) ≫ Functor.map f) := by rw [Cat.id_comp]
    _ = adj.ψ (Cat.id (G A)) ≫ f := by rw [ψ_nat_right adj (Cat.id (G A)) f]

/-- Triangle identity I: F(η_A) ≫ ε_{F A} = id_{F A}. -/
theorem triangle_one (A : 𝒞) : Functor.map (unit adj A) ≫ counit adj (F A) = Cat.id (F A) := by
  dsimp [unit, counit]
  calc
    Functor.map (adj.φ (Cat.id (F A))) ≫ adj.ψ (Cat.id (G (F A))) =
      adj.ψ (adj.φ (Cat.id (F A)) ≫ Cat.id (G (F A))) := by
      rw [ψ_nat_left adj (adj.φ (Cat.id (F A))) (Cat.id (G (F A)))]
    _ = adj.ψ (adj.φ (Cat.id (F A))) := by rw [Cat.comp_id]
    _ = Cat.id (F A) := by rw [adj.ψφ]

/-- Triangle identity II: η_{G B} ≫ G(ε_B) = id_{G B}. -/
theorem triangle_two (B : 𝒟) : unit adj (G B) ≫ Functor.map (counit adj B) = Cat.id (G B) := by
  dsimp [unit, counit]
  calc
    adj.φ (Cat.id (F (G B))) ≫ Functor.map (adj.ψ (Cat.id (G B))) =
      adj.φ (Cat.id (F (G B)) ≫ adj.ψ (Cat.id (G B))) := by rw [adj.φ_nat_right]
    _ = adj.φ (adj.ψ (Cat.id (G B))) := by rw [Cat.id_comp]
    _ = Cat.id (G B) := by rw [adj.φψ]

/-- φ(h) = η_A ≫ G(h) — reconstruct φ from the unit. -/
theorem φ_eq (h : F A ⟶ B) : adj.φ h = unit adj A ≫ Functor.map h := by
  dsimp [unit]
  calc
    adj.φ h = adj.φ (Cat.id (F A) ≫ h) := by rw [Cat.id_comp]
    _ = adj.φ (Cat.id (F A)) ≫ Functor.map h := by rw [adj.φ_nat_right]

/-- ψ(g) = F(g) ≫ ε_B — reconstruct ψ from the counit. -/
theorem ψ_eq (g : A ⟶ G B) : adj.ψ g = Functor.map g ≫ counit adj B := by
  dsimp [counit]
  calc
    adj.ψ g = adj.ψ (g ≫ Cat.id (G B)) := by rw [Cat.comp_id]
    _ = Functor.map g ≫ adj.ψ (Cat.id (G B)) := by rw [ψ_nat_left adj g (Cat.id (G B))]

end AdjunctionProperties

/-! ## §1.813 Reflective subcategories -/

/-- A subcategory via inclusion I : 𝒜' → 𝒞 is REFLECTIVE
    if I has a left adjoint (§1.813). The left adjoint is the REFLECTION. -/
class ReflectiveSubcategory {𝒜' : Type u₁} [Cat.{v} 𝒜'] (I : 𝒜' → 𝒞) [Functor I] where
  reflection : 𝒞 → 𝒜'
  [refl_functor : Functor reflection]
  adj : LeftAdjoint reflection I

/-- §1.816: A subcategory is COREFLECTIVE if the inclusion has a right adjoint. -/
class CoreflectiveSubcategory {𝒜' : Type u₁} [Cat.{v} 𝒜'] (I : 𝒜' → 𝒞) [Functor I] where
  coreflection : 𝒞 → 𝒜'
  [corefl_functor : Functor coreflection]
  adj : RightAdjoint coreflection I

/-! ## §1.815  Closure operation

  On a poset, a CLOSURE OPERATION is order-preserving, idempotent,
  inflationary (§1.815). For a general category this is an idempotent monad.

  The book states three explicit axioms for the poset case:
    (i)  order-preserving:  x ≤ y → x̄ ≤ ȳ
    (ii) idempotent:        x̄ = x̄̄  (i.e. applying closure twice = once)
    (iii) inflationary:     x ≤ x̄ -/

/-- A CLOSURE OPERATION on a category (§1.815). T is the closure,
    η is the unit (inflationary), idem says Tη is an isomorphism. -/
structure ClosureOperation (𝒞 : Type u) [Cat.{v} 𝒞] where
  T : 𝒞 → 𝒞
  [functor_T : Functor T]
  η : (A : 𝒞) → A ⟶ T A
  η_natural : ∀ {A B} (f : A ⟶ B), f ≫ η B = η A ≫ (Functor.map (F := T) f)
  idem : ∀ (A : 𝒞), IsIso (Functor.map (F := T) (η A))

/-! ### §1.815 Poset case: three explicit axioms

  When the ambient category is a poset (hom-sets are propositions),
  the three axioms reduce to the statements the book gives explicitly. -/

/-- Minimal partial-order typeclass used for the poset case of §1.815.
    (The repo avoids mathlib; this bundles LE with the three order axioms.) -/
class PosetOrder (P : Type u) extends LE P where
  le_refl  : ∀ (x : P), x ≤ x
  le_trans : ∀ {x y z : P}, x ≤ y → y ≤ z → x ≤ z
  le_antisymm : ∀ {x y : P}, x ≤ y → y ≤ x → x = y

/-- A CLOSURE OPERATION on a poset (§1.815, poset case).
    op is order-preserving, inflationary, and idempotent:

      (i)  x ≤ y  →  op x ≤ op y
      (ii) x ≤ op x
      (iii) op (op x) ≤ op x  (equivalently op (op x) = op x) -/
structure ClosureOpPoset (P : Type u) [PosetOrder P] where
  /-- The closure operation -/
  op : P → P
  /-- (i) order-preserving: x ≤ y → op x ≤ op y -/
  order_preserving : ∀ {x y : P}, x ≤ y → op x ≤ op y
  /-- (ii) inflationary: x ≤ op x -/
  inflationary : ∀ (x : P), x ≤ op x
  /-- (iii) idempotent (≤ half): op (op x) ≤ op x -/
  idempotent : ∀ (x : P), op (op x) ≤ op x

/-- The closure is idempotent as an equality: op(op x) = op x (§1.815). -/
theorem ClosureOpPoset.idem_eq {P : Type u} [po : PosetOrder P]
    (cl : ClosureOpPoset P) (x : P) : cl.op (cl.op x) = cl.op x :=
  po.le_antisymm (cl.idempotent x) (cl.inflationary (cl.op x))

/-- A point x is CLOSED if op x = x (§1.815). -/
def ClosureOpPoset.IsClosed {P : Type u} [PosetOrder P]
    (cl : ClosureOpPoset P) (x : P) : Prop := cl.op x = x

/-- Every value of op is closed (§1.815). -/
theorem ClosureOpPoset.value_is_closed {P : Type u} [PosetOrder P]
    (cl : ClosureOpPoset P) (x : P) : cl.IsClosed (cl.op x) := cl.idem_eq x

/-- Universal property of the reflection: x ≤ y ↔ op x ≤ y for closed y (§1.815).
    This shows closed elements form a reflective sub-poset. -/
theorem ClosureOpPoset.reflection_universal {P : Type u} [po : PosetOrder P]
    (cl : ClosureOpPoset P) {x y : P} (hy : cl.IsClosed y) :
    x ≤ y ↔ cl.op x ≤ y := by
  constructor
  · intro h
    exact hy ▸ cl.order_preserving h
  · intro h
    exact po.le_trans (cl.inflationary x) h

/-! ## §1.817  Representability ⟺ left-adjoint criterion

  §1.817: G : 𝒟 → 𝒞 has a left-adjoint F iff (A, G(-)) is representable for all A.
  The forward direction: F A represents (A, G(-)) via the adjunction bijection.
  The converse: choose representing objects FA and the equivalence (A,G(-)) ≅ (FA,-);
  define Fx as the unique map making the naturality square commute. -/

/-- (A, G(-)) is REPRESENTABLE BY an object R ∈ 𝒟: a bijection
    (A ⟶ G B) ≃ (R ⟶ B), natural in B (§1.817). -/
structure RepresentedBy {𝒞 : Type u₁} [Cat.{v} 𝒞] {𝒟 : Type u₂} [Cat.{v} 𝒟]
    (G : 𝒟 → 𝒞) [Functor G] (A : 𝒞) (R : 𝒟) where
  φ {B : 𝒟} : (A ⟶ G B) → (R ⟶ B)
  ψ {B : 𝒟} : (R ⟶ B) → (A ⟶ G B)
  φψ {B : 𝒟} (f : R ⟶ B) : φ (ψ f) = f
  ψφ {B : 𝒟} (g : A ⟶ G B) : ψ (φ g) = g
  /-- φ is natural in B: precomposing with G(b) on the right corresponds to
      postcomposing with b on the R side. -/
  φ_nat {B B' : 𝒟} (g : A ⟶ G B) (b : B ⟶ B') :
    φ (g ≫ Functor.map b) = φ g ≫ b

/-- §1.817 (→): if F ⊣ G then (A, G(-)) is represented by F A. -/
def repr_of_adj {𝒞 : Type u₁} [Cat.{v} 𝒞] {𝒟 : Type u₂} [Cat.{v} 𝒟]
    {F : 𝒞 → 𝒟} {G : 𝒟 → 𝒞} [Functor F] [Functor G]
    (adj : F ⊣ G) (A : 𝒞) : RepresentedBy G A (F A) where
  φ g  := adj.ψ g
  ψ h  := adj.φ h
  φψ f := adj.ψφ f
  ψφ g := adj.φψ g
  -- naturality: ψ (g ≫ G(b)) = ψ g ≫ b  (ψ_nat_right)
  φ_nat g b := ψ_nat_right adj g b

/-! ### Derived laws for `RepresentedBy` -/

section RepresentedByLaws
variable {𝒞 : Type u₁} [Cat.{v} 𝒞] {𝒟 : Type u₂} [Cat.{v} 𝒟]
variable {G : 𝒟 → 𝒞} [Functor G] {A : 𝒞} {R : 𝒟} (r : RepresentedBy G A R)

/-- φ is injective on `(A ⟶ G B)` (it is a bijection). -/
theorem RepresentedBy.φ_inj {B : 𝒟} {g₁ g₂ : A ⟶ G B} (h : r.φ g₁ = r.φ g₂) : g₁ = g₂ := by
  rw [← r.ψφ g₁, ← r.ψφ g₂, h]

/-- ψ is natural in B (the inverse of `φ_nat`): ψ(f ≫ b) = ψ f ≫ G(b). -/
theorem RepresentedBy.ψ_nat {B B' : 𝒟} (f : R ⟶ B) (b : B ⟶ B') :
    r.ψ (f ≫ b) = r.ψ f ≫ Functor.map (F := G) b :=
  r.φ_inj <| by rw [r.φ_nat, r.φψ, r.φψ]

end RepresentedByLaws

/-- §1.817 (←): if (A, G(-)) is representable for every A, we can construct
    a left adjoint for G.

    On objects `F A := (repr A).1`.  The unit `η_A : A ⟶ G(F A)` is `ψ(id_{F A})`,
    and the key identity `ψ h = η_A ≫ G h` (proved from `ψ_nat`) makes the bijection
    `φ_adj := ψ`, `ψ_adj := φ` an adjunction.  On a map `x : A' ⟶ A` set
    `F x := φ_{A'}(x ≫ η_A) : F A' ⟶ F A`; functoriality and the two naturality
    squares all reduce to unit-naturality `η_{A'} ≫ G(F x) = x ≫ η_A`. -/
def adj_of_repr {𝒞 : Type u₁} [Cat.{v} 𝒞] {𝒟 : Type u₂} [Cat.{v} 𝒟]
    (G : 𝒟 → 𝒞) [Functor G]
    (repr : ∀ A : 𝒞, Σ R : 𝒟, RepresentedBy G A R) :
    Σ (F : 𝒞 → 𝒟), Σ (_ : Functor F), F ⊣ G := by
  -- Object map and the chosen representation for each A.
  let Fobj : 𝒞 → 𝒟 := fun A => (repr A).1
  let r : (A : 𝒞) → RepresentedBy G A (Fobj A) := fun A => (repr A).2
  -- Unit η_A : A ⟶ G(F A) := ψ(id_{F A}).
  let η : (A : 𝒞) → A ⟶ G (Fobj A) := fun A => (r A).ψ (Cat.id (Fobj A))
  -- Map on morphisms: F x := φ_{A'}(x ≫ η_A).
  let Fmap : {A' A : 𝒞} → (A' ⟶ A) → (Fobj A' ⟶ Fobj A) :=
    fun {A' A} x => (r A').φ (x ≫ η A)
  -- Key identity: ψ h = η_A ≫ G h, for h : F A ⟶ B.
  have ψ_eq : ∀ {A : 𝒞} {B : 𝒟} (h : Fobj A ⟶ B), (r A).ψ h = η A ≫ Functor.map (F := G) h := by
    intro A B h
    have := (r A).ψ_nat (Cat.id (Fobj A)) h
    rwa [Cat.id_comp] at this
  -- Unit naturality: η_{A'} ≫ G(F x) = x ≫ η_A.
  have η_nat : ∀ {A' A : 𝒞} (x : A' ⟶ A), η A' ≫ Functor.map (F := G) (Fmap x) = x ≫ η A := by
    intro A' A x
    rw [← ψ_eq (Fmap x)]
    show (r A').ψ ((r A').φ (x ≫ η A)) = x ≫ η A
    rw [(r A').ψφ]
  -- F is a functor.
  let hF : Functor Fobj := {
    map := Fmap
    map_id := by
      intro A
      show (r A).φ (Cat.id A ≫ η A) = Cat.id (Fobj A)
      rw [Cat.id_comp]
      -- η A = ψ(id), so φ(η A) = φ(ψ id) = id.
      show (r A).φ ((r A).ψ (Cat.id (Fobj A))) = Cat.id (Fobj A)
      rw [(r A).φψ]
    map_comp := by
      intro A'' A' A x y
      show (r A'').φ ((x ≫ y) ≫ η A) = Fmap x ≫ Fmap y
      -- Fmap x ≫ Fmap y = φ(x ≫ η A') ≫ Fmap y = φ((x ≫ η A') ≫ G(Fmap y))  [φ_nat]
      show (r A'').φ ((x ≫ y) ≫ η A) = (r A'').φ (x ≫ η A') ≫ Fmap y
      rw [← (r A'').φ_nat (x ≫ η A') (Fmap y)]
      congr 1
      -- (x ≫ y) ≫ η A = (x ≫ η A') ≫ G(Fmap y), via assoc + η_nat y.
      rw [Cat.assoc, Cat.assoc, η_nat y] }
  refine ⟨Fobj, hF, ?_⟩
  -- The adjunction: φ := ψ_repr, ψ := φ_repr.
  exact {
    φ := fun {A B} h => (r A).ψ h
    ψ := fun {A B} g => (r A).φ g
    φψ := fun {A B} g => (r A).ψφ g
    ψφ := fun {A B} h => (r A).φψ h
    -- φ_nat_left: ψ(F a ≫ h) = a ≫ ψ h.
    φ_nat_left := by
      intro A' A B a h
      -- show (r A').ψ (Fmap a ≫ h) = a ≫ (r A).ψ h
      rw [ψ_eq (Functor.map a ≫ h), ψ_eq h, Functor.map_comp, ← Cat.assoc]
      -- η A' ≫ G(F a) = a ≫ η A  (η_nat); F a = Functor.map a here.
      rw [show Functor.map (F := G) (Functor.map (F := Fobj) a) = Functor.map (F := G) (Fmap a) from rfl,
        η_nat a, Cat.assoc]
    -- φ_nat_right: ψ(h ≫ b) = ψ h ≫ G b  (exactly ψ_nat).
    φ_nat_right := by
      intro A B B' h b
      exact (r A).ψ_nat h b }

end Freyd
