/-
  Freyd & Scedrov, *Categories and Allegories* §1.43–§1.437
  Cartesian categories: equalizers, pullbacks, equivalences.

  Constructive proofs (adapted from mathlib).
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## Equalizers -/

structure EqualizerCone {A B : 𝒞} (f g : A ⟶ B) where
  dom : 𝒞
  map : dom ⟶ A
  eq  : map ≫ f = map ≫ g

class HasEqualizer {A B : 𝒞} (f g : A ⟶ B) where
  cone : EqualizerCone f g
  lift : ∀ (c : EqualizerCone f g), c.dom ⟶ cone.dom
  fac  : ∀ (c : EqualizerCone f g), lift c ≫ cone.map = c.map
  uniq : ∀ (c : EqualizerCone f g) (m : c.dom ⟶ cone.dom), m ≫ cone.map = c.map → m = lift c

class HasEqualizers (𝒞 : Type u) [Cat.{v} 𝒞] where
  eq (A B : 𝒞) (f g : A ⟶ B) : HasEqualizer f g

section EqualizerAPI
variable [HasEqualizers 𝒞]

def eqObj {A B : 𝒞} (f g : A ⟶ B) : 𝒞 := (HasEqualizers.eq A B f g).cone.dom
def eqMap {A B : 𝒞} (f g : A ⟶ B) : eqObj f g ⟶ A := (HasEqualizers.eq A B f g).cone.map
theorem eqMap_eq {A B : 𝒞} (f g : A ⟶ B) : eqMap f g ≫ f = eqMap f g ≫ g :=
  (HasEqualizers.eq A B f g).cone.eq

def eqLift {A B X : 𝒞} (f g : A ⟶ B) (k : X ⟶ A) (h : k ≫ f = k ≫ g) : X ⟶ eqObj f g :=
  (HasEqualizers.eq A B f g).lift ⟨X, k, h⟩

theorem eqLift_fac {A B X : 𝒞} (f g : A ⟶ B) (k : X ⟶ A) (h : k ≫ f = k ≫ g) :
    eqLift f g k h ≫ eqMap f g = k := (HasEqualizers.eq A B f g).fac ⟨X, k, h⟩

theorem eqLift_uniq {A B X : 𝒞} (f g : A ⟶ B) (k : X ⟶ A) (h : k ≫ f = k ≫ g)
    (m : X ⟶ eqObj f g) (hm : m ≫ eqMap f g = k) : m = eqLift f g k h :=
  (HasEqualizers.eq A B f g).uniq ⟨X, k, h⟩ m hm
end EqualizerAPI

/-! ## Cartesian category (§1.43) -/

class CartesianCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasEqualizers 𝒞

/-! ## §1.432 Products + equalizers → pullbacks -/

section PB_from_ProdEq
variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [heq : HasEqualizers 𝒞]

def products_equalizers_implies_pullbacks {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) : HasPullback f g :=
  let pbObj := eqObj (fst ≫ f) (snd ≫ g)
  let pbMap : pbObj ⟶ prod A B := eqMap (fst ≫ f) (snd ≫ g)
  have h_sq : (pbMap ≫ fst) ≫ f = (pbMap ≫ snd) ≫ g :=
    calc
      (pbMap ≫ fst) ≫ f = pbMap ≫ (fst ≫ f) := by rw [Cat.assoc]
      _ = pbMap ≫ (snd ≫ g) := eqMap_eq (fst ≫ f) (snd ≫ g)
      _ = (pbMap ≫ snd) ≫ g := by rw [Cat.assoc]
  let pullCone : Cone f g := { pt := pbObj, π₁ := pbMap ≫ fst, π₂ := pbMap ≫ snd, w := h_sq }
  have mk_h_cond : ∀ (c : Cone f g), pair c.π₁ c.π₂ ≫ (fst ≫ f) = pair c.π₁ c.π₂ ≫ (snd ≫ g) := by
    intro c
    calc
      pair c.π₁ c.π₂ ≫ (fst ≫ f) = (pair c.π₁ c.π₂ ≫ fst) ≫ f := by rw [Cat.assoc]
      _ = c.π₁ ≫ f := by rw [fst_pair]
      _ = c.π₂ ≫ g := by rw [c.w]
      _ = (pair c.π₁ c.π₂ ≫ snd) ≫ g := by rw [snd_pair]
      _ = pair c.π₁ c.π₂ ≫ (snd ≫ g) := by rw [Cat.assoc]
  { cone := pullCone
    lift := λ c => eqLift (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c)
    lift_fst := λ c => by
      dsimp [pullCone, pbMap]
      calc
        eqLift (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c) ≫ eqMap (fst ≫ f) (snd ≫ g) ≫ fst
            = (eqLift (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c) ≫ eqMap (fst ≫ f) (snd ≫ g)) ≫ fst := by rw [Cat.assoc]
        _ = pair c.π₁ c.π₂ ≫ fst := by rw [eqLift_fac]
        _ = c.π₁ := fst_pair _ _
    lift_snd := λ c => by
      dsimp [pullCone, pbMap]
      calc
        eqLift (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c) ≫ eqMap (fst ≫ f) (snd ≫ g) ≫ snd
            = (eqLift (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c) ≫ eqMap (fst ≫ f) (snd ≫ g)) ≫ snd := by rw [Cat.assoc]
        _ = pair c.π₁ c.π₂ ≫ snd := by rw [eqLift_fac]
        _ = c.π₂ := snd_pair _ _
    lift_uniq := λ c u hu₁ hu₂ => by
      dsimp [pullCone] at hu₁ hu₂ ⊢
      apply eqLift_uniq (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c) u
      apply pair_uniq c.π₁ c.π₂ (u ≫ pbMap)
      · rw [Cat.assoc, hu₁]
      · rw [Cat.assoc, hu₂] }
end PB_from_ProdEq

/-! ## §1.433 Pullbacks + terminator → binary products -/

section Prod_from_PB_Term
variable [ht : HasTerminal 𝒞] [hpull : HasPullbacks 𝒞]

def pullbacks_terminator_implies_products : HasBinaryProducts 𝒞 where
  prod A B := (hpull.has (term A) (term B)).cone.pt
  fst := λ {A B} => (hpull.has (term A) (term B)).cone.π₁
  snd := λ {A B} => (hpull.has (term A) (term B)).cone.π₂
  pair := λ {X A B} f g => (hpull.has (term A) (term B)).lift
    { pt := X, π₁ := f, π₂ := g, w := term_uniq (f ≫ term A) (g ≫ term B) }
  fst_pair := λ {X A B} f g => (hpull.has (term A) (term B)).lift_fst
    { pt := X, π₁ := f, π₂ := g, w := term_uniq (f ≫ term A) (g ≫ term B) }
  snd_pair := λ {X A B} f g => (hpull.has (term A) (term B)).lift_snd
    { pt := X, π₁ := f, π₂ := g, w := term_uniq (f ≫ term A) (g ≫ term B) }
  pair_uniq := λ {X A B} f g h h₁ h₂ => (hpull.has (term A) (term B)).lift_uniq
    { pt := X, π₁ := f, π₂ := g, w := term_uniq (f ≫ term A) (g ≫ term B) } h h₁ h₂
end Prod_from_PB_Term

/-! ## §1.434 Products + pullbacks → equalizers -/

section Eq_from_ProdPB
variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

def products_pullbacks_implies_equalizers : HasEqualizers 𝒞 where
  eq A B f g :=
    let u : A ⟶ prod A B := pair (Cat.id A) f
    let v : A ⟶ prod A B := pair (Cat.id A) g
    let pb := hpull.has u v
    have h_pb_sq : pb.cone.π₁ ≫ u = pb.cone.π₂ ≫ v := pb.cone.w
    have h_fst_eq : pb.cone.π₁ = pb.cone.π₂ := by
      have h1 : pb.cone.π₁ ≫ Cat.id A = pb.cone.π₂ ≫ Cat.id A := by
        calc
          pb.cone.π₁ ≫ Cat.id A = pb.cone.π₁ ≫ (u ≫ fst) := by rw [fst_pair, Cat.comp_id]
          _ = (pb.cone.π₁ ≫ u) ≫ fst := by rw [Cat.assoc]
          _ = (pb.cone.π₂ ≫ v) ≫ fst := by rw [h_pb_sq]
          _ = pb.cone.π₂ ≫ (v ≫ fst) := by rw [Cat.assoc]
          _ = pb.cone.π₂ ≫ Cat.id A := by rw [fst_pair, Cat.comp_id]
      exact (by
        simpa [Cat.comp_id] using h1)
    have h_eq_cond : pb.cone.π₁ ≫ f = pb.cone.π₁ ≫ g := by
      calc
        pb.cone.π₁ ≫ f = pb.cone.π₁ ≫ (u ≫ snd) := by rw [snd_pair]
        _ = (pb.cone.π₁ ≫ u) ≫ snd := by rw [Cat.assoc]
        _ = (pb.cone.π₂ ≫ v) ≫ snd := by rw [h_pb_sq]
        _ = pb.cone.π₂ ≫ (v ≫ snd) := by rw [Cat.assoc]
        _ = pb.cone.π₂ ≫ g := by rw [snd_pair]
        _ = pb.cone.π₁ ≫ g := by rw [h_fst_eq]
    have mk_hcone_w : ∀ (c : EqualizerCone f g), c.map ≫ u = c.map ≫ v := by
      intro c
      calc
        c.map ≫ u = pair c.map (c.map ≫ f) :=
          pair_uniq c.map (c.map ≫ f) (c.map ≫ u)
            (by rw [Cat.assoc, fst_pair, Cat.comp_id])
            (by rw [Cat.assoc, snd_pair])
        _ = pair c.map (c.map ≫ g) := by rw [c.eq]
        _ = c.map ≫ v :=
          (pair_uniq c.map (c.map ≫ g) (c.map ≫ v)
            (by rw [Cat.assoc, fst_pair, Cat.comp_id])
            (by rw [Cat.assoc, snd_pair])).symm
    { cone := { dom := pb.cone.pt, map := pb.cone.π₁, eq := h_eq_cond }
      lift := λ c =>
        pb.lift { pt := c.dom, π₁ := c.map, π₂ := c.map, w := mk_hcone_w c }
      fac := λ c => pb.lift_fst _
      uniq := λ c m hm => by
        have hm₂ : m ≫ pb.cone.π₂ = c.map := by
          calc
            m ≫ pb.cone.π₂ = m ≫ pb.cone.π₁ := by
              dsimp [pb]; rw [h_fst_eq]
            _ = c.map := hm
        exact pb.lift_uniq { pt := c.dom, π₁ := c.map, π₂ := c.map, w := mk_hcone_w c } m hm hm₂ }
end Eq_from_ProdPB

/-! ## §1.435 Pullbacks + terminator → Cartesian -/

section Cartesian_from_PB_Term
variable [ht : HasTerminal 𝒞] [hpull : HasPullbacks 𝒞]

def pullbacks_terminator_implies_cartesian : CartesianCategory 𝒞 :=
  letI hp : HasBinaryProducts 𝒞 := pullbacks_terminator_implies_products
  letI heq : HasEqualizers 𝒞 := products_pullbacks_implies_equalizers
  { toHasTerminal := ht
    toHasBinaryProducts := hp
    toHasEqualizers := heq }
end Cartesian_from_PB_Term

/-! ## §1.439 Terminal + Pullbacks ↔ Cartesian

  The diagram (Freyd & Scedrov, §1.439):

  ```
              §1.432
  Cartesian -----------> HasPullbacks
     ^                      |
     |                      | §1.433 (pb → prod)
     |                      v
     └── §1.434 ── (HasTerm, HasProd, HasPullbacks)
       (prod+pb → eq)
  ```

  Given a terminal object, binary products + equalizers together are
  equivalent to pullbacks.  Hence `Cartesian` ⇔ `HasTerminal + HasPullbacks`. -/

section S1_439
variable [HasTerminal 𝒞]

/-- **§1.439**: In a category with a terminal object,
    `HasBinaryProducts 𝒞 ∧ HasEqualizers 𝒞 ↔ HasPullbacks 𝒞`.

    → (§1.432): Given products and equalizers, construct the pullback of
      `f` and `g` as the equalizer of `fst≫f` and `snd≫g` on `A×B`.

    ← (§1.433 + §1.434): Given pullbacks, build products as the pullback
      of `A→1` and `B→1`; then build the equalizer of `f,g` as the
      pullback of `⟨id,f⟩` and `⟨id,g⟩` over `A×B`. -/
theorem cartesian_iff_pullbacks :
    (Nonempty (HasBinaryProducts 𝒞) ∧ Nonempty (HasEqualizers 𝒞)) ↔ Nonempty (HasPullbacks 𝒞) := by
  constructor
  · -- (§1.432): Prod + Eq → Pullbacks
    rintro ⟨⟨hp⟩, ⟨heq⟩⟩
    haveI := hp; haveI := heq
    refine ⟨⟨λ {A B C} f g => products_equalizers_implies_pullbacks f g⟩⟩
  · -- (§1.433 + §1.434): Pullbacks → Prod, then Prod + Pullbacks → Eq
    intro ⟨hpull⟩
    haveI := hpull
    have hp : HasBinaryProducts 𝒞 := pullbacks_terminator_implies_products
    have heq : HasEqualizers 𝒞 :=
      haveI := hp
      products_pullbacks_implies_equalizers
    exact ⟨⟨hp⟩, ⟨heq⟩⟩

/-- **§1.439** bundled: `Cartesian 𝒞 ↔ HasPullbacks 𝒞` given a terminator. -/
theorem cartesianCategory_iff_pullbacks :
    Nonempty (CartesianCategory 𝒞) ↔ Nonempty (HasPullbacks 𝒞) := by
  constructor
  · intro ⟨h⟩
    haveI : HasBinaryProducts 𝒞 := h.toHasBinaryProducts
    haveI : HasEqualizers 𝒞 := h.toHasEqualizers
    have hpb : HasPullbacks 𝒞 :=
      { has := λ f g => products_equalizers_implies_pullbacks f g }
    exact ⟨hpb⟩
  · intro ⟨h⟩
    haveI := h
    exact ⟨pullbacks_terminator_implies_cartesian⟩

end S1_439

/-! ## §1.425 Finite (n-ary) products

  Given an indexed family `{Aᵢ}_{i ∈ Fin n}` of objects, a PRODUCT is an
  object `P` with projections `πᵢ : P → Aᵢ` universal for all cones.  The
  empty product (n = 0) is a terminator.  Non-empty finite products are built
  by iterating binary products (§1.425).
  Note: use `Nat` not `ℕ` since `ℕ` is a single-char auto-implicit under
  `relaxedAutoImplicit = false`. -/

structure FinProdCone {n : Nat} (A : Fin n → 𝒞) where
  apex : 𝒞
  π    : (i : Fin n) → apex ⟶ A i

structure HasFinProd {n : Nat} (A : Fin n → 𝒞) where
  cone : FinProdCone A
  lift : ∀ (c : FinProdCone A), c.apex ⟶ cone.apex
  fac  : ∀ (c : FinProdCone A) (i : Fin n), lift c ≫ cone.π i = c.π i
  uniq : ∀ (c : FinProdCone A) (m : c.apex ⟶ cone.apex),
    (∀ i, m ≫ cone.π i = c.π i) → m = lift c

class HasFiniteProducts (𝒞 : Type u) [Cat.{v} 𝒞] where
  fin_prod : ∀ {n : Nat} (A : Fin n → 𝒞), HasFinProd A

section FinProdAPI
variable [hfp : HasFiniteProducts 𝒞]

def finProdObj {n : Nat} (A : Fin n → 𝒞) : 𝒞 := (hfp.fin_prod A).cone.apex
def finProdπ   {n : Nat} (A : Fin n → 𝒞) (i : Fin n) : finProdObj A ⟶ A i :=
  (hfp.fin_prod A).cone.π i

def finProdLift {n : Nat} (A : Fin n → 𝒞) {X : 𝒞} (f : (i : Fin n) → X ⟶ A i) :
    X ⟶ finProdObj A :=
  (hfp.fin_prod A).lift ⟨X, f⟩

theorem finProdLift_fac {n : Nat} (A : Fin n → 𝒞) {X : 𝒞} (f : (i : Fin n) → X ⟶ A i)
    (i : Fin n) : finProdLift A f ≫ finProdπ A i = f i :=
  (hfp.fin_prod A).fac ⟨X, f⟩ i

theorem finProdLift_uniq {n : Nat} (A : Fin n → 𝒞) {X : 𝒞} (f : (i : Fin n) → X ⟶ A i)
    (m : X ⟶ finProdObj A) (hm : ∀ i, m ≫ finProdπ A i = f i) : m = finProdLift A f :=
  (hfp.fin_prod A).uniq ⟨X, f⟩ m hm

end FinProdAPI

section FinProd_equiv

-- Helper: 2-object family from two objects (avoids Matrix/Fin.cons)
private def fin2 (A B : 𝒞) : Fin 2 → 𝒞 := Fin.cases A (Fin.cases B (fun i => i.elim0))

/-- **§1.425** (→): `HasFiniteProducts` gives a terminator (empty product). -/
def finiteProducts_implies_terminal (hfp : HasFiniteProducts 𝒞) : HasTerminal 𝒞 where
  one  := (hfp.fin_prod (n := 0) Fin.elim0).cone.apex
  trm  := fun X => (hfp.fin_prod (n := 0) Fin.elim0).lift ⟨X, fun i => i.elim0⟩
  uniq := fun {X} f g => by
    have hf := (hfp.fin_prod (n := 0) Fin.elim0).uniq ⟨X, fun i => i.elim0⟩ f
                (fun i => i.elim0)
    have hg := (hfp.fin_prod (n := 0) Fin.elim0).uniq ⟨X, fun i => i.elim0⟩ g
                (fun i => i.elim0)
    rw [hf, hg]

/-- **§1.425** (→): `HasFiniteProducts` gives binary products. -/
def finiteProducts_implies_binary (hfp : HasFiniteProducts 𝒞) : HasBinaryProducts 𝒞 where
  prod  := fun A B => (hfp.fin_prod (n := 2) (fin2 A B)).cone.apex
  fst   := fun {A B} => (hfp.fin_prod (fin2 A B)).cone.π 0
  snd   := fun {A B} => (hfp.fin_prod (fin2 A B)).cone.π 1
  pair  := fun {X A B} f g =>
    (hfp.fin_prod (fin2 A B)).lift ⟨X, Fin.cases f (Fin.cases g (fun i => i.elim0))⟩
  fst_pair := fun {X A B} f g =>
    (hfp.fin_prod (fin2 A B)).fac ⟨X, Fin.cases f (Fin.cases g (fun i => i.elim0))⟩ 0
  snd_pair := fun {X A B} f g =>
    (hfp.fin_prod (fin2 A B)).fac ⟨X, Fin.cases f (Fin.cases g (fun i => i.elim0))⟩ 1
  pair_uniq := fun {X A B} f g h h₁ h₂ =>
    (hfp.fin_prod (fin2 A B)).uniq ⟨X, Fin.cases f (Fin.cases g (fun i => i.elim0))⟩ h
      (fun i => Fin.cases h₁ (fun j => Fin.cases h₂ (fun k => k.elim0) j) i)

/-- **§1.425** helper: build `HasFinProd` by induction on `n`. -/
def finProd_of_term_binary [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] :
    ∀ (n : Nat) (A : Fin n → 𝒞), HasFinProd A
  | 0,     _ => { cone := ⟨one, fun i => i.elim0⟩
                  lift := fun c => term c.apex
                  fac  := fun c i => i.elim0
                  uniq := fun c m _ => term_uniq m (term c.apex) }
  | n + 1, A =>
    let tail := finProd_of_term_binary n (A ∘ Fin.succ)
    { cone := ⟨prod (A 0) tail.cone.apex,
                fun i => Fin.cases fst (fun j => snd ≫ tail.cone.π j) i⟩
      lift := fun c => pair (c.π 0) (tail.lift ⟨c.apex, fun j => c.π j.succ⟩)
      fac  := fun c i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [fst_pair]
        · show pair (c.π 0) (tail.lift ⟨c.apex, fun j => c.π j.succ⟩) ≫
                (snd ≫ tail.cone.π _) = c.π _
          rw [← Cat.assoc, snd_pair, tail.fac]
      uniq := fun c m hm => by
        apply pair_uniq
        · -- m ≫ fst = c.π 0
          have h0 := hm 0; simp at h0; exact h0
        · -- m ≫ snd = tail.lift {...}
          apply tail.uniq ⟨c.apex, fun j => c.π j.succ⟩
          intro j
          have hj := hm j.succ
          simp only [Fin.cases_succ, ← Cat.assoc] at hj
          exact hj }

/-- **§1.425** (←): Terminal + binary products give all finite products. -/
def terminal_binary_implies_finiteProducts [HasTerminal 𝒞] [HasBinaryProducts 𝒞] :
    HasFiniteProducts 𝒞 where
  fin_prod A := finProd_of_term_binary _ A

/-- **§1.425**: finite products ↔ terminator + binary products. -/
theorem finiteProducts_iff :
    Nonempty (HasFiniteProducts 𝒞) ↔ Nonempty (HasTerminal 𝒞) ∧ Nonempty (HasBinaryProducts 𝒞) := by
  constructor
  · intro ⟨hfp⟩
    exact ⟨⟨finiteProducts_implies_terminal hfp⟩, ⟨finiteProducts_implies_binary hfp⟩⟩
  · intro ⟨⟨ht⟩, ⟨hp⟩⟩
    haveI := ht; haveI := hp
    exact ⟨terminal_binary_implies_finiteProducts⟩

end FinProd_equiv

/-! ## §1.429 Equalizers split idempotents

  If a category has equalizers, then every idempotent `e : A → A` splits:
  the equalizer of `e` and `1_A` gives the splitting.
  `Idempotent`/`SplitIdempotent` are defined in S1_39; they're re-stated
  locally here since S1_39 cannot be imported (it has pre-existing errors
  unrelated to this file). -/

/-- IDEMPOTENT: e² = e (S1_39, defined locally to avoid import of broken S1_39). -/
def Idempotent' {A : 𝒞} (e : A ⟶ A) : Prop := e ≫ e = e

/-- SPLIT IDEMPOTENT: ∃ B, r : A→B, s : B→A with s≫r = id and r≫s = e. -/
def SplitIdempotent' {A : 𝒞} (e : A ⟶ A) : Prop :=
  ∃ (B : 𝒞) (r : A ⟶ B) (s : B ⟶ A), s ≫ r = Cat.id B ∧ r ≫ s = e

section S1_429
variable [HasEqualizers 𝒞]

/-- **§1.429**: In a category with equalizers, every idempotent splits.

  PROOF (Freyd §1.429): Given `e : A → A`, `e² = e`, let `y : B → A` be the
  equalizer of `e` and `id_A`.  Define `x : A → B` as the unique map with
  `x ≫ y = e` (exists since `e ≫ e = e ≫ id_A`).  Then
  `(y ≫ x) ≫ y = y ≫ (x ≫ y) = y ≫ e = y ≫ id_A = y`,
  so `y ≫ x = id_B` by equalizer uniqueness (canceling `y` on the right). -/
theorem equalizers_split_idempotents {A : 𝒞} (e : A ⟶ A) (he : Idempotent' e) :
    SplitIdempotent' e := by
  -- Equalizer y : B → A of e and id_A
  let B := eqObj e (Cat.id A)
  let y := eqMap e (Cat.id A)
  have hy : y ≫ e = y ≫ Cat.id A := eqMap_eq e (Cat.id A)
  -- x : A → B, the unique lift of e through y (uses e ≫ e = e ≫ id_A)
  have hee : e ≫ e = e ≫ Cat.id A := by rw [Cat.comp_id]; exact he
  let x := eqLift e (Cat.id A) e hee
  have hxy : x ≫ y = e := eqLift_fac e (Cat.id A) e hee
  -- y ≫ x = id_B: both (y≫x) and id_B satisfy `? ≫ y = y`
  have hyx_fac : (y ≫ x) ≫ y = y := by
    rw [Cat.assoc, hxy]; exact hy.trans (Cat.comp_id _)
  have hid_fac : Cat.id B ≫ y = y := Cat.id_comp _
  have hyx : y ≫ x = Cat.id B := by
    have h1 : y ≫ x = eqLift e (Cat.id A) y hy := eqLift_uniq _ _ _ hy _ hyx_fac
    have h2 : Cat.id B = eqLift e (Cat.id A) y hy := eqLift_uniq _ _ _ hy _ hid_fac
    rw [h1, ← h2]
  exact ⟨B, x, y, hyx, hxy⟩

end S1_429

/-! ## §1.437 Representation of Cartesian categories

  A REPRESENTATION OF CARTESIAN CATEGORIES is a functor between Cartesian
  categories that preserves finite products and equalizers (§1.437). -/

section S1_437

/-- A functor `F : 𝒞 → 𝒟` PRESERVES EQUALIZERS if for each equalizer
    `y : E → A` of `f, g : A → B` in `𝒞`, the image `F(y) : F E → F A`
    is an equalizer of `F f, F g` in `𝒟`. -/
def PreservesEqualizers {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F : 𝒞 → 𝒟) [hF : Functor F] [HasEqualizers 𝒞] [HasEqualizers 𝒟] : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B),
    -- the canonical comparison map F(eqObj f g) → eqObj (Ff) (Fg) is iso
    IsIso ((HasEqualizers.eq (F A) (F B) (hF.map f) (hF.map g)).lift
            { dom := F (eqObj f g)
              map := hF.map (eqMap f g)
              eq  := by rw [← hF.map_comp, ← hF.map_comp, eqMap_eq] })

/-- A functor `F : 𝒞 → 𝒟` PRESERVES TERMINAL if `F(1_𝒞)` is terminal in `𝒟`. -/
def PreservesTerminal {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F : 𝒞 → 𝒟) [hF : Functor F] [HasTerminal 𝒞] [HasTerminal 𝒟] : Prop :=
  ∀ (X : 𝒟) (f g : X ⟶ F one), f = g

/-- A functor `F : 𝒞 → 𝒟` PRESERVES BINARY PRODUCTS if the canonical map
    `F(A × B) → F A × F B` (given by `⟨F fst, F snd⟩`) is an isomorphism. -/
def PreservesBinaryProducts {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F : 𝒞 → 𝒟) [hF : Functor F] [HasBinaryProducts 𝒞] [HasBinaryProducts 𝒟] : Prop :=
  ∀ {A B : 𝒞},
    IsIso (pair (hF.map (fst (A := A) (B := B))) (hF.map (snd (A := A) (B := B))) :
             F (prod A B) ⟶ prod (F A) (F B))

/-- **§1.437** A REPRESENTATION OF CARTESIAN CATEGORIES: a functor between
    Cartesian categories preserving finite products (= terminal + binary products)
    and equalizers. -/
structure CartesianFunctor {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    [CartesianCategory 𝒞] [CartesianCategory 𝒟]
    (F : 𝒞 → 𝒟) [Functor F] : Prop where
  pres_terminal  : PreservesTerminal F
  pres_products  : PreservesBinaryProducts F
  pres_equalizers : PreservesEqualizers F

/-- **§1.437**: A CartesianFunctor preserves pullbacks.

  PROOF: By §1.432 a pullback of `f : A → C`, `g : B → C` is the equalizer
  of `fst ≫ f`, `snd ≫ g` on `A × B`.  Since `F` preserves products and
  equalizers, it preserves this construction. -/
theorem cartesianFunctor_preserves_pullbacks {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    [CartesianCategory 𝒞] [CartesianCategory 𝒟]
    {F : 𝒞 → 𝒟} [hF : Functor F] (hcf : CartesianFunctor F) :
    ∀ {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C),
      (products_equalizers_implies_pullbacks f g).cone.IsPullback := by
  sorry

/-- **§1.437**: A functor preserving pullbacks and the terminator is a
    representation of Cartesian categories.

  PROOF: §1.433 gives binary products (pullback over terminator);
  §1.434 gives equalizers (pullback of ⟨id,f⟩ vs ⟨id,g⟩). -/
theorem pullbacks_terminal_implies_cartesianFunctor {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    [CartesianCategory 𝒞] [CartesianCategory 𝒟]
    {F : 𝒞 → 𝒟} [hF : Functor F]
    (hpull : ∀ {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C),
      Cone.IsPullback
        { pt := F (products_equalizers_implies_pullbacks f g).cone.pt
          π₁ := hF.map (products_equalizers_implies_pullbacks f g).cone.π₁
          π₂ := hF.map (products_equalizers_implies_pullbacks f g).cone.π₂
          w  := by rw [← hF.map_comp, ← hF.map_comp,
                       (products_equalizers_implies_pullbacks f g).cone.w] })
    (hterm : PreservesTerminal F) : CartesianFunctor F := by
  sorry

end S1_437

/-! ## §1.438 Reflects equalizers ⟹ reflects isomorphisms; faithfulness

  A functor reflecting equalizers reflects isomorphisms (§1.438).
  An iso-reflecting equalizer-preserving functor is faithful (§1.438). -/

section S1_438

variable {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
variable (F : 𝒞 → 𝒟) [hF : Functor F]

/-- A functor REFLECTS EQUALIZERS if: whenever `F` carries a cone to an
    equalizer cone in `𝒟`, the original cone is an equalizer cone in `𝒞`. -/
def ReflectsEqualizers [HasEqualizers 𝒞] [HasEqualizers 𝒟] : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B),
    IsIso ((HasEqualizers.eq (F A) (F B) (hF.map f) (hF.map g)).lift
            { dom := F (eqObj f g)
              map := hF.map (eqMap f g)
              eq  := by rw [← hF.map_comp, ← hF.map_comp, eqMap_eq] }) →
    IsIso (eqLift f g (eqMap f g) (eqMap_eq f g) ≫ eqMap f g)  -- i.e. eqMap is split-monic

/-- **§1.438**: A functor that reflects equalizers reflects isomorphisms.

  PROOF: `f : A → B` is an isomorphism iff it is the equalizer of `1_B`
  and `1_B` (it equalizes since `f ≫ 1 = f ≫ 1`, and any lift is iso).
  So if `F f` is iso in `𝒟`, then `F f` equalizes in `𝒟`, reflecting back
  to `f` equalizing in `𝒞`, which forces `f` to be iso. -/
theorem reflects_equalizers_reflects_isos [HasEqualizers 𝒞] [HasEqualizers 𝒟]
    (hre : ReflectsEqualizers F) :
    ∀ {A B : 𝒞} (f : A ⟶ B), IsIso (hF.map f) → IsIso f := by
  sorry

/-- **§1.438**: A source-category-with-equalizers functor that preserves
    equalizers and reflects isomorphisms is faithful (an embedding).

  PROOF (book §1.438): given `f g : A → B` with `F f = F g`, then `F f`
  equalizes `F h` and `F h` for any `h`, so by preservation `f` equalizes
  `h` and `h`.  The equalizer of `h, h` is `id_A` (any map equalizes equal
  maps), so `f = g`. -/
theorem iso_reflecting_eq_preserving_faithful [HasEqualizers 𝒞] [HasEqualizers 𝒟]
    (hre : ∀ {A B : 𝒞} (f : A ⟶ B), IsIso (hF.map f) → IsIso f)
    (hpe : PreservesEqualizers F) :
    Embedding F := by
  sorry

end S1_438

end Freyd
