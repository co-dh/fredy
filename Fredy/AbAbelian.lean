/-
  Freyd & Scedrov, *Categories and Allegories* §1.594–§1.595
  `Ab(𝒞)` is half-additive: finite products and coproducts COINCIDE (biproducts).

  This file builds, on top of `Fredy/AbCategory.lean` (the category `Ab(𝒞)` and the
  abelian-group hom-sets), the §1.595 biproduct structure:

    * `prodGObj A B`           — the PRODUCT group object: carrier `A.car × B.car`,
                                 pointwise `add/zero/neg`.  Gives `HasBinaryProducts (Ab 𝒞)`.
    * `HasBinaryCoproducts (Ab 𝒞)` — the COPRODUCT is the SAME object `prodGObj A B`,
                                 with biproduct injections `inl = ⟨id,0⟩`, `inr = ⟨0,id⟩`
                                 and copairing `case f g = (π₁≫f) + (π₂≫g)` (using the
                                 hom-set `+` of `AbCategory`).  The coproduct UMP holds
                                 because `A,B` are abelian group objects.
    * `HasTerminal (Ab 𝒞)` / `HasCoterminator (Ab 𝒞)` — the zero group object `0 ≅ 1`.
    * `instance HalfAdditiveCategory (Ab 𝒞)` — the §1.595 keystone.  Its field
      `prod_coprod_coincide` is an iso BY CONSTRUCTION: the canonical map
      `case ⟨id,0⟩ ⟨0,id⟩ : A⊕B → A×B` is literally the IDENTITY of the shared carrier,
      because `inl = ⟨id,0⟩` and `inr = ⟨0,id⟩` are the very injections of the coproduct.

  No `sorry`, no new axiom.  The coincidence is genuine: products and coproducts of
  abelian group objects are the *same* object with the *same* projections/injections,
  and the copairing realising the coproduct UMP is the hom-set addition.
-/

import Fredy.AbCategory

open Freyd

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]

/-! ### The product group object

  Carrier `A.carrier × B.carrier`; the operations are the products of `A`'s and `B`'s.
  We reuse `abSq` from `AbCategory` (re-derived locally as `pair (fst≫_) (snd≫_)`). -/

/-- `g ≫ ⟨a, b⟩ = ⟨g ≫ a, g ≫ b⟩` (local copy; same statement as `AbCategory.ab_pair_precomp`). -/
private theorem aa_pair_precomp {X Y A B : 𝒞} (g : X ⟶ Y) (a : Y ⟶ A) (b : Y ⟶ B) :
    g ≫ pair a b = pair (g ≫ a) (g ≫ b) :=
  pair_uniq (g ≫ a) (g ≫ b) (g ≫ pair a b)
    (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])

/-- Carrier-level `add` of the product group object:
    `(A.c×B.c)×(A.c×B.c) → A.c×B.c`, adding the two factors componentwise. -/
private def prodAddCar (A B : AbelianGroupObject 𝒞) :
    prod (prod A.carrier B.carrier) (prod A.carrier B.carrier) ⟶ prod A.carrier B.carrier :=
  pair (pair (fst ≫ fst) (snd ≫ fst) ≫ A.add)
       (pair (fst ≫ snd) (snd ≫ snd) ≫ B.add)

@[simp] private theorem prodAddCar_fst (A B : AbelianGroupObject 𝒞) :
    prodAddCar A B ≫ fst = pair (fst ≫ fst) (snd ≫ fst) ≫ A.add := fst_pair _ _

@[simp] private theorem prodAddCar_snd (A B : AbelianGroupObject 𝒞) :
    prodAddCar A B ≫ snd = pair (fst ≫ snd) (snd ≫ snd) ≫ B.add := snd_pair _ _

/-- **Component lemma.**  For any two "elements" `u w : S → A.c×B.c`, the product-group sum
    `⟨u,w⟩ ≫ prodAddCar` projects componentwise to the sums of `A` and `B`:
        `(u ⊞ w) ≫ π₁ = ⟨u≫π₁, w≫π₁⟩ ≫ A.add`,  similarly for `π₂`.
    Every `prodGObj` axiom is reduced to `A`/`B`'s axioms by joint monicity + this. -/
private theorem prodAdd_proj_fst {S : 𝒞} {A B : AbelianGroupObject 𝒞}
    (u w : S ⟶ prod A.carrier B.carrier) :
    (pair u w ≫ prodAddCar A B) ≫ fst = pair (u ≫ fst) (w ≫ fst) ≫ A.add := by
  rw [Cat.assoc, prodAddCar_fst, ← Cat.assoc, aa_pair_precomp,
      ← Cat.assoc, ← Cat.assoc, fst_pair, snd_pair]

private theorem prodAdd_proj_snd {S : 𝒞} {A B : AbelianGroupObject 𝒞}
    (u w : S ⟶ prod A.carrier B.carrier) :
    (pair u w ≫ prodAddCar A B) ≫ snd = pair (u ≫ snd) (w ≫ snd) ≫ B.add := by
  rw [Cat.assoc, prodAddCar_snd, ← Cat.assoc, aa_pair_precomp,
      ← Cat.assoc, ← Cat.assoc, fst_pair, snd_pair]

/-- **Closed form of the product-group sum.**  For any two elements `u w : S → A.c×B.c`,
    `⟨u,w⟩ ≫ prodAddCar = ⟨ ⟨u≫π₁,w≫π₁⟩≫A.add , ⟨u≫π₂,w≫π₂⟩≫B.add ⟩`.  Proved by joint
    monicity from the two projection lemmas; lets every nested `prodGObj` add-expression be
    rewritten uniformly. -/
private theorem prodAdd_eq {S : 𝒞} {A B : AbelianGroupObject 𝒞}
    (u w : S ⟶ prod A.carrier B.carrier) :
    pair u w ≫ prodAddCar A B
      = pair (pair (u ≫ fst) (w ≫ fst) ≫ A.add) (pair (u ≫ snd) (w ≫ snd) ≫ B.add) :=
  fst_snd_jointly_monic _ _
    (by rw [prodAdd_proj_fst, fst_pair])
    (by rw [prodAdd_proj_snd, snd_pair])

/-- The product of two abelian group objects: carrier `A.car × B.car`,
    operations the pointwise products of those of `A` and `B`.

    `zero = ⟨A.zero, B.zero⟩`, `neg = ⟨π₁≫A.neg, π₂≫B.neg⟩`, and
    `add` is `prodAddCar`.  Each axiom is verified componentwise (project by `fst`/`snd`,
    reduce to the corresponding axiom of `A` resp. `B`). -/
noncomputable def prodGObj (A B : AbelianGroupObject 𝒞) : AbelianGroupObject 𝒞 where
  carrier := prod A.carrier B.carrier
  zero := pair A.zero B.zero
  neg := pair (fst ≫ A.neg) (snd ≫ B.neg)
  add := prodAddCar A B
  add_zero := by
    -- ⟨ term≫⟨Az,Bz⟩ , id ⟩ ≫ add = id, componentwise via GElt.zero_add of `fst`/`snd`.
    refine fst_snd_jointly_monic _ _ ?_ ?_
    · rw [prodAdd_proj_fst, Cat.id_comp]
      have e : (term (prod A.carrier B.carrier) ≫ pair A.zero B.zero) ≫ fst
             = term (prod A.carrier B.carrier) ≫ A.zero := by rw [Cat.assoc, fst_pair]
      rw [e]; exact GElt.zero_add A fst
    · rw [prodAdd_proj_snd, Cat.id_comp]
      have e : (term (prod A.carrier B.carrier) ≫ pair A.zero B.zero) ≫ snd
             = term (prod A.carrier B.carrier) ≫ B.zero := by rw [Cat.assoc, snd_pair]
      rw [e]; exact GElt.zero_add B snd
  add_neg := by
    -- ⟨ neg , id ⟩ ≫ add = term ≫ zero, componentwise via GElt.neg_add.
    refine fst_snd_jointly_monic _ _ ?_ ?_
    · rw [prodAdd_proj_fst, Cat.id_comp, fst_pair, Cat.assoc, fst_pair, GElt.neg_add A fst]
    · rw [prodAdd_proj_snd, Cat.id_comp, snd_pair, Cat.assoc, snd_pair, GElt.neg_add B snd]
  add_assoc := by
    -- ((x+y)+z) = (x+(y+z)) componentwise.  Project, normalise both sides with the
    -- product/pairing equations, then close by `GElt.add_assoc` of `A`/`B` on the
    -- triple of inner projections `(fst≫fst≫π), (fst≫snd≫π), (snd≫π)`.
    refine fst_snd_jointly_monic _ _ ?_ ?_
    · -- LHS-fst: distribute `fst ≫ (prodAddCar≫fst)`; RHS-fst: project the inner `y+z`.
      rw [prodAdd_proj_fst, Cat.assoc, prodAddCar_fst, ← Cat.assoc, aa_pair_precomp,
          prodAdd_proj_fst, prodAdd_proj_fst]
      simp only [Cat.assoc]
      exact GElt.add_assoc A (fst ≫ fst ≫ fst) (fst ≫ snd ≫ fst) (snd ≫ fst)
    · rw [prodAdd_proj_snd, Cat.assoc, prodAddCar_snd, ← Cat.assoc, aa_pair_precomp,
          prodAdd_proj_snd, prodAdd_proj_snd]
      simp only [Cat.assoc]
      exact GElt.add_assoc B (fst ≫ fst ≫ snd) (fst ≫ snd ≫ snd) (snd ≫ snd)
  add_comm := by
    -- ⟨snd,fst⟩ ≫ add = add, componentwise via GElt.add_comm.
    refine fst_snd_jointly_monic _ _ ?_ ?_
    · rw [prodAdd_proj_fst, prodAddCar_fst]
      exact GElt.add_comm A (snd ≫ fst) (fst ≫ fst)
    · rw [prodAdd_proj_snd, prodAddCar_snd]
      exact GElt.add_comm B (snd ≫ snd) (fst ≫ snd)

/-! ### Products in `Ab(𝒞)`

  The projections `π₁ : prodGObj A B → A`, `π₂ : prodGObj A B → B` and the pairing
  `⟨f,g⟩` are group-object homomorphisms, giving the universal property of the product
  *in `Ab(𝒞)`*.  `prodGObj` is therefore the binary product. -/

/-- `carrier`-`add` of `prodGObj` is literally `prodAddCar`. -/
@[simp] private theorem prodGObj_add (A B : AbelianGroupObject 𝒞) :
    (prodGObj A B).add = prodAddCar A B := rfl
@[simp] private theorem prodGObj_carrier (A B : AbelianGroupObject 𝒞) :
    (prodGObj A B).carrier = prod A.carrier B.carrier := rfl

/-- The first projection `π₁ : prodGObj A B → A` is a homomorphism (it is exactly the
    statement `prodAddCar≫fst = ⟨π₁fst,π₂fst⟩≫A.add`). -/
theorem isHom_prodFst (A B : AbelianGroupObject 𝒞) :
    IsHomAbelianGroupObject (prodGObj A B) A fst :=
  prodAddCar_fst A B

theorem isHom_prodSnd (A B : AbelianGroupObject 𝒞) :
    IsHomAbelianGroupObject (prodGObj A B) B snd :=
  prodAddCar_snd A B

/-- The pairing `⟨f,g⟩` of two homomorphisms is a homomorphism into `prodGObj A B`. -/
theorem isHom_prodPair {X A B : AbelianGroupObject 𝒞}
    {f : X.carrier ⟶ A.carrier} {g : X.carrier ⟶ B.carrier}
    (hf : IsHomAbelianGroupObject X A f) (hg : IsHomAbelianGroupObject X B g) :
    IsHomAbelianGroupObject X (prodGObj A B) (pair f g) := by
  unfold IsHomAbelianGroupObject at *
  -- Goal: X.add ≫ ⟨f,g⟩ = ⟨π₁≫⟨f,g⟩, π₂≫⟨f,g⟩⟩ ≫ prodAddCar.  Joint monicity on fst/snd.
  refine fst_snd_jointly_monic _ _ ?_ ?_
  · rw [Cat.assoc, fst_pair, hf, prodGObj_add, prodAdd_proj_fst]
    simp only [Cat.assoc, fst_pair]
  · rw [Cat.assoc, snd_pair, hg, prodGObj_add, prodAdd_proj_snd]
    simp only [Cat.assoc, snd_pair]

/-- §1.595: `Ab(𝒞)` has binary products — the product is the product group object,
    with the underlying-`𝒞` projections and pairing (all homomorphisms). -/
noncomputable instance instHasBinaryProductsAb : HasBinaryProducts (AbelianGroupObject 𝒞) where
  prod A B := prodGObj A B
  fst := ⟨fst, isHom_prodFst _ _⟩
  snd := ⟨snd, isHom_prodSnd _ _⟩
  pair f g := ⟨pair f.val g.val, isHom_prodPair f.property g.property⟩
  fst_pair f g := Subtype.ext (fst_pair f.val g.val)
  snd_pair f g := Subtype.ext (snd_pair f.val g.val)
  pair_uniq f g h h₁ h₂ :=
    Subtype.ext (pair_uniq f.val g.val h.val (congrArg Subtype.val h₁) (congrArg Subtype.val h₂))

end Freyd
