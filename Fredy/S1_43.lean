/-
  Freyd & Scedrov, *Categories and Allegories* §1.43–§1.437
  Cartesian categories: equalizers, pullbacks, equivalences.

  Constructive proofs (adapted from mathlib).
-/


import Fredy.S1_1
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

end Freyd
