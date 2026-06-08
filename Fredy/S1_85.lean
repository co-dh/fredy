/-
  Freyd & Scedrov, *Categories and Allegories* §1.85
  Exponential categories (cartesian closed).

  §1.85  EXPONENTIAL CATEGORY: binary products + for each A,
         the functor A × - has a right adjoint (-)^A.
  §1.853 B^A as a bifunctor (covariant in B, contravariant in A)
  §1.859 BASEABLE objects
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41
import Fredy.S1_42


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ### Product functor A × -

  For each object A, the endofunctor A × - sends X ↦ A × X, f ↦ A × f. -/

section ProductFunctor

variable [hp' : HasBinaryProducts 𝒞]

/-- A × f : A × X → A × Y, with (A×f)≫fst = fst, (A×f)≫snd = snd≫f. -/
def prodMap (A X Y : 𝒞) (f : X ⟶ Y) : prod A X ⟶ prod A Y :=
  pair (X := prod A X) (A := A) (B := Y) fst (snd ≫ f)

theorem prodMap_fst (A X Y : 𝒞) (f : X ⟶ Y) : prodMap A X Y f ≫ fst (A := A) (B := Y) = fst := by
  dsimp [prodMap]; rw [fst_pair]

theorem prodMap_snd (A X Y : 𝒞) (f : X ⟶ Y) : prodMap A X Y f ≫ snd = snd ≫ f := by
  dsimp [prodMap]; rw [snd_pair]

theorem pair_fst_snd (A X : 𝒞) :
    pair (X := prod A X) (A := A) (B := X) fst snd = Cat.id (prod A X) :=
  (pair_uniq (X := prod A X) (A := A) (B := X) fst snd (Cat.id _)
    (Cat.id_comp _) (Cat.id_comp _)).symm

theorem prodMap_id (A X : 𝒞) : prodMap A X X (Cat.id X) = Cat.id (prod A X) := by
  dsimp [prodMap]; rw [Cat.comp_id, pair_fst_snd]

theorem prodMap_comp (A X Y Z : 𝒞) (f : X ⟶ Y) (g : Y ⟶ Z) :
    prodMap A X Z (f ≫ g) = prodMap A X Y f ≫ prodMap A Y Z g := by
  dsimp [prodMap]
  let RHS := pair (X := prod A X) (A := A) (B := Y) fst (snd ≫ f) ≫
             pair (X := prod A Y) (A := A) (B := Z) fst (snd ≫ g)
  have h_fst : RHS ≫ fst (A := A) (B := Z) = fst := by
    dsimp [RHS]; rw [Cat.assoc, fst_pair, fst_pair]
  have h_snd : RHS ≫ snd = snd ≫ (f ≫ g) := by
    dsimp [RHS]
    rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc]
  apply (pair_uniq (X := prod A X) (A := A) (B := Z) fst (snd ≫ (f ≫ g)) RHS h_fst h_snd).symm

/-- Functor instance for A × -. -/
instance prodFunctor (A : 𝒞) : Functor (λ X => prod A X) where
  map {X Y} f := prodMap A X Y f
  map_id X := prodMap_id A X
  map_comp f g := prodMap_comp A _ _ _ f g

end ProductFunctor

/-! ## §1.85  Exponential categories

  A category with binary products is EXPONENTIAL if each functor
  A × - has a right adjoint.  The counit is the EVALUATION MAP e,
  the adjoint transpose is CARRYING (curry). -/

class HasExponentials (𝒞 : Type u) [Cat.{v} 𝒞] extends HasBinaryProducts 𝒞 where
  exp_obj : 𝒞 → 𝒞 → 𝒞
  eval_map {A B : 𝒞} : prod A (exp_obj A B) ⟶ B
  curry_map {A B X : 𝒞} (f : prod A X ⟶ B) : X ⟶ exp_obj A B
  curry_eval {A B X : 𝒞} (f : prod A X ⟶ B) :
    prodMap A X (exp_obj A B) (curry_map f) ≫ eval_map = f
  curry_unique {A B X : 𝒞} {f : prod A X ⟶ B} {g : X ⟶ exp_obj A B}
    (h_eq : prodMap A X (exp_obj A B) g ≫ eval_map = f) : g = curry_map f

variable [HasExponentials 𝒞]

/-- The exponential object B^A (§1.85). -/
def exp (A B : 𝒞) : 𝒞 := HasExponentials.exp_obj A B

notation:30 B " ^^ " A:30 => exp A B

/-- The EVALUATION MAP e : A × B^A → B (§1.85). -/
def eval_exp (A B : 𝒞) : prod A (B ^^ A) ⟶ B := HasExponentials.eval_map (A := A) (B := B)

/-- The EXPONENTIAL TRANSPOSE (curry): f : A × X → B gives Λf : X → B^A. -/
def curry {A B X : 𝒞} (f : prod A X ⟶ B) : X ⟶ B ^^ A := HasExponentials.curry_map f

/-- The characteristic equation: (A × curry f) ≫ eval = f. -/
@[simp] theorem curry_eval_eq {A B X : 𝒞} (f : prod A X ⟶ B) :
    prodMap A X (B ^^ A) (curry f) ≫ eval_exp A B = f :=
  HasExponentials.curry_eval f

/-- curry is unique: if (A × g) ≫ eval = f then g = curry f. -/
theorem curry_unique_eq {A B X : 𝒞} {f : prod A X ⟶ B} {g : X ⟶ B ^^ A}
    (h : prodMap A X (B ^^ A) g ≫ eval_exp A B = f) : g = curry f :=
  HasExponentials.curry_unique h

/-- curry is injective. -/
theorem curry_inj {A B X : 𝒞} {f₁ f₂ : prod A X ⟶ B}
    (h : curry f₁ = curry f₂) : f₁ = f₂ := by
  rw [← curry_eval_eq f₁, ← curry_eval_eq f₂, h]

end Freyd
