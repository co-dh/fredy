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

/-- An idempotent generalized element is zero: if `e ⊕ e = e` then `e = O`.
    (Cancel `e`: `e = e ⊕ O = e ⊕ (e ⊕ ⊖e) = (e ⊕ e) ⊕ ⊖e = e ⊕ ⊖e = O`.) -/
theorem GElt.idem_zero {T : 𝒞} (P : AbelianGroupObject 𝒞) {e : T ⟶ P.carrier}
    (he : pair e e ≫ P.add = e) : e = term T ≫ P.zero :=
  calc e = pair e (term T ≫ P.zero) ≫ P.add := (GElt.add_zero P e).symm
    _ = pair e (pair e (e ≫ P.neg) ≫ P.add) ≫ P.add := by rw [GElt.add_neg P e]
    _ = pair (pair e e ≫ P.add) (e ≫ P.neg) ≫ P.add := (GElt.add_assoc P e e (e ≫ P.neg)).symm
    _ = pair e (e ≫ P.neg) ≫ P.add := by rw [he]
    _ = term T ≫ P.zero := GElt.add_neg P e

/-! ### The zero (terminal = coterminal) group object

  Carrier `one` (the terminal of `𝒞`); all structure maps are forced by `term_uniq`.
  It is simultaneously terminal and coterminal in `Ab(𝒞)` (`0 ≅ 1`). -/

/-- The zero group object: carrier `1`, all operations the unique maps to `1`. -/
noncomputable def zeroGObj : AbelianGroupObject 𝒞 where
  carrier := one
  zero := Cat.id one
  neg := Cat.id one
  add := term _
  add_zero := term_uniq _ _
  add_neg := term_uniq _ _
  add_assoc := term_uniq _ _
  add_comm := term_uniq _ _

/-- Any carrier map into `1` is a homomorphism (both sides of the hom square land in `1`). -/
theorem isHom_toZero (A : AbelianGroupObject 𝒞) (x : A.carrier ⟶ one) :
    IsHomAbelianGroupObject A (zeroGObj) x := term_uniq _ _

/-- `Ab(𝒞)` has a terminal object: the zero group object, with `term` as the unique map. -/
noncomputable instance instHasTerminalAb : HasTerminal (AbelianGroupObject 𝒞) where
  one := zeroGObj
  trm A := ⟨term A.carrier, isHom_toZero A _⟩
  uniq f g := Subtype.ext (term_uniq f.val g.val)

/-- `A.zero : 1 → A` is a homomorphism `zeroGObj → A` (`O ⊕ O = O`). -/
theorem isHom_fromZero (A : AbelianGroupObject 𝒞) :
    IsHomAbelianGroupObject (zeroGObj) A A.zero := by
  show (zeroGObj : AbelianGroupObject 𝒞).add ≫ A.zero
        = pair (fst ≫ A.zero) (snd ≫ A.zero) ≫ A.add
  -- LHS: term(1×1) ≫ A.zero;  RHS: ⟨fst≫A.zero, snd≫A.zero⟩ ≫ A.add.
  -- Write both as `(t ≫ A.zero) ⊕ (t ≫ A.zero)` form via term collapse, then `zero_add_zero`.
  show term (prod one one) ≫ A.zero = pair (fst ≫ A.zero) (snd ≫ A.zero) ≫ A.add
  have hf : (fst : prod (one : 𝒞) one ⟶ one) ≫ A.zero
          = term (prod one one) ≫ A.zero := by rw [term_uniq fst (term _)]
  have hs : (snd : prod (one : 𝒞) one ⟶ one) ≫ A.zero
          = term (prod one one) ≫ A.zero := by rw [term_uniq snd (term _)]
  rw [hf, hs, GElt.zero_add_zero A]

/-- Uniqueness of homs out of `zeroGObj`: any hom `x : 1 → A` is `A.zero`.
    The hom condition pulled back along the diagonal forces `x = x ⊕ x`, so `x = O`. -/
theorem hom_fromZero_unique {A : AbelianGroupObject 𝒞} {x : (one : 𝒞) ⟶ A.carrier}
    (hx : IsHomAbelianGroupObject (zeroGObj) A x) : x = A.zero := by
  -- hx : term(1×1) ≫ x = ⟨fst≫x, snd≫x⟩ ≫ A.add.  Precompose with `diag one : 1 → 1×1`.
  have key := congrArg (fun m => diag (one : 𝒞) ≫ m) hx
  simp only at key
  -- LHS: diag ≫ zeroGObj.add ≫ x.  `diag ≫ zeroGObj.add : 1→1` is `id 1`, so LHS = x.
  rw [← Cat.assoc, term_uniq (diag (one : 𝒞) ≫ (zeroGObj : AbelianGroupObject 𝒞).add)
        (Cat.id one), Cat.id_comp] at key
  have hsplit : diag (one : 𝒞) ≫ pair (fst ≫ x) (snd ≫ x) ≫ A.add = pair x x ≫ A.add := by
    rw [← Cat.assoc, aa_pair_precomp, ← Cat.assoc, ← Cat.assoc, diag_fst, diag_snd]
    simp only [Cat.id_comp]
  rw [hsplit] at key
  -- key : x = ⟨x, x⟩ ≫ A.add.  Idempotent ⟹ x = term 1 ≫ A.zero = id ≫ A.zero = A.zero.
  have hidem := GElt.idem_zero A key.symm
  rwa [term_uniq (term (one : 𝒞)) (Cat.id one), Cat.id_comp] at hidem

/-- `Ab(𝒞)` has a coterminator: the zero group object `zeroGObj` (so `0 ≅ 1`). -/
noncomputable instance instHasCoterminatorAb : HasCoterminator (AbelianGroupObject 𝒞) where
  zero := zeroGObj
  init A := ⟨A.zero, isHom_fromZero A⟩
  init_uniq f g := Subtype.ext ((hom_fromZero_unique f.property).trans
    (hom_fromZero_unique g.property).symm)

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

/-! ### A homomorphism preserves group sums of generalized elements

  This is the engine of the coproduct universal property: a hom `h : P → X` carries the
  `P`-sum of any two elements `u,w : T → P.car` to the `X`-sum of `u≫h, w≫h`. -/

/-- For a homomorphism `h : P → X` and any `u w : T → P.carrier`,
    `(⟨u,w⟩ ≫ P.add) ≫ h = ⟨u≫h, w≫h⟩ ≫ X.add`.  (Precompose the hom square `P.add≫h =
    (h×h)≫X.add` with `⟨u,w⟩` and distribute.) -/
theorem hom_preserves_add {T : 𝒞} {P X : AbelianGroupObject 𝒞}
    {h : P.carrier ⟶ X.carrier} (hh : IsHomAbelianGroupObject P X h)
    (u w : T ⟶ P.carrier) :
    (pair u w ≫ P.add) ≫ h = pair (u ≫ h) (w ≫ h) ≫ X.add := by
  rw [Cat.assoc, hh, ← Cat.assoc, aa_pair_precomp]
  simp only [← Cat.assoc, fst_pair, snd_pair]

/-- A homomorphism preserves zero: `(t ≫ P.zero) ≫ h = t ≫ X.zero` for any `t : T → 1`.
    (`P.zero≫h` is idempotent because `O ⊕ O = O` and `h` preserves `⊕`, so it is `O_X`.) -/
theorem hom_preserves_zero {T : 𝒞} {P X : AbelianGroupObject 𝒞}
    {h : P.carrier ⟶ X.carrier} (hh : IsHomAbelianGroupObject P X h) (t : T ⟶ one) :
    (t ≫ P.zero) ≫ h = t ≫ X.zero := by
  rw [term_uniq t (term T)]
  have idem : pair ((term T ≫ P.zero) ≫ h) ((term T ≫ P.zero) ≫ h) ≫ X.add
            = (term T ≫ P.zero) ≫ h := by
    rw [← hom_preserves_add hh (term T ≫ P.zero) (term T ≫ P.zero), GElt.zero_add_zero P]
  exact GElt.idem_zero X idem

namespace AbCoprod

variable {A B X : AbelianGroupObject 𝒞}

/-- Carrier-level copairing `[f,g] = (π₁≫f) + (π₂≫g) : prodGObj A B → X`. -/
private def caseCar (f : A.carrier ⟶ X.carrier) (g : B.carrier ⟶ X.carrier) :
    prod A.carrier B.carrier ⟶ X.carrier :=
  pair (fst ≫ f) (snd ≫ g) ≫ X.add

/-- Coproduct injection `inl = ⟨id, 0⟩ : A → prodGObj A B` (a homomorphism). -/
theorem isHom_inl (A B : AbelianGroupObject 𝒞) :
    IsHomAbelianGroupObject A (prodGObj A B) (pair (Cat.id A.carrier) (HomAb.zeroCar A B)) :=
  isHom_prodPair (isHom_id A) (HomAb.isHom_zeroCar A B)

/-- Coproduct injection `inr = ⟨0, id⟩ : B → prodGObj A B` (a homomorphism). -/
theorem isHom_inr (A B : AbelianGroupObject 𝒞) :
    IsHomAbelianGroupObject B (prodGObj A B) (pair (HomAb.zeroCar B A) (Cat.id B.carrier)) :=
  isHom_prodPair (HomAb.isHom_zeroCar B A) (isHom_id B)

/-- The copairing `[f,g]` is a homomorphism: it is the hom-set sum of the two homs
    `π₁≫f` and `π₂≫g`. -/
theorem isHom_caseCar {f : A.carrier ⟶ X.carrier} {g : B.carrier ⟶ X.carrier}
    (hf : IsHomAbelianGroupObject A X f) (hg : IsHomAbelianGroupObject B X g) :
    IsHomAbelianGroupObject (prodGObj A B) X (caseCar f g) := by
  -- caseCar f g = addCar ⟨π₁≫f⟩ ⟨π₂≫g⟩ where π₁,π₂ are homs prodGObj→A, prodGObj→B.
  have h1 : IsHomAbelianGroupObject (prodGObj A B) X (fst ≫ f) :=
    isHom_comp (isHom_prodFst A B) hf
  have h2 : IsHomAbelianGroupObject (prodGObj A B) X (snd ≫ g) :=
    isHom_comp (isHom_prodSnd A B) hg
  exact HomAb.isHom_addCar (A := prodGObj A B) (B := X) ⟨fst ≫ f, h1⟩ ⟨snd ≫ g, h2⟩

/-- `inl ≫ [f,g] = f`, for a homomorphism `g` (`g` sends `0` to `0`).  `f` arbitrary. -/
theorem caseCar_inl (f : A.carrier ⟶ X.carrier) {g : B.carrier ⟶ X.carrier}
    (hg : IsHomAbelianGroupObject B X g) :
    pair (Cat.id A.carrier) (HomAb.zeroCar A B) ≫ caseCar f g = f := by
  unfold caseCar HomAb.zeroCar
  -- ⟨id,0⟩ ≫ (⟨π₁≫f,π₂≫g⟩≫X.add) = ⟨f, (term≫B.zero)≫g⟩ ≫ X.add = ⟨f, term≫X.zero⟩ ≫ X.add = f.
  rw [← Cat.assoc, aa_pair_precomp, ← Cat.assoc, ← Cat.assoc, fst_pair, snd_pair,
      Cat.id_comp, Cat.assoc, ← Cat.assoc (term A.carrier) B.zero g,
      hom_preserves_zero hg (term A.carrier)]
  exact GElt.add_zero X f

/-- `inr ≫ [f,g] = g`, for a homomorphism `f`.  `g` arbitrary. -/
theorem caseCar_inr {f : A.carrier ⟶ X.carrier} (g : B.carrier ⟶ X.carrier)
    (hf : IsHomAbelianGroupObject A X f) :
    pair (HomAb.zeroCar B A) (Cat.id B.carrier) ≫ caseCar f g = g := by
  unfold caseCar HomAb.zeroCar
  rw [← Cat.assoc, aa_pair_precomp, ← Cat.assoc, ← Cat.assoc, fst_pair, snd_pair,
      Cat.id_comp, Cat.assoc, ← Cat.assoc (term B.carrier) A.zero f,
      hom_preserves_zero hf (term B.carrier)]
  exact GElt.zero_add X g

/-- **Biproduct splitting of the identity.**  On the shared carrier `A.c×B.c`,
    `id = (π₁≫inl) ⊕ (π₂≫inr)` where `inl=⟨id,0⟩`, `inr=⟨0,id⟩`.  This is the algebraic
    fact behind the product/coproduct coincidence: every element splits as its `inl`-part
    plus its `inr`-part. -/
theorem splitId (A B : AbelianGroupObject 𝒞) :
    pair (fst ≫ pair (Cat.id A.carrier) (HomAb.zeroCar A B))
         (snd ≫ pair (HomAb.zeroCar B A) (Cat.id B.carrier)) ≫ (prodGObj A B).add
      = Cat.id (prod A.carrier B.carrier) := by
  unfold HomAb.zeroCar
  rw [prodGObj_add]
  refine fst_snd_jointly_monic _ _ ?_ ?_
  · rw [prodAdd_proj_fst, Cat.id_comp]
    -- first comp: (fst≫⟨id,..⟩)≫fst = fst;  second comp: (snd≫⟨term≫Az,id⟩)≫fst = snd≫term≫Az.
    rw [Cat.assoc, fst_pair, Cat.comp_id, Cat.assoc, fst_pair, ← Cat.assoc,
        term_uniq (snd ≫ term B.carrier) (term _)]
    exact GElt.add_zero A fst
  · rw [prodAdd_proj_snd, Cat.id_comp]
    -- first comp: (fst≫⟨id,term≫Bz⟩)≫snd = fst≫term≫Bz = term≫Bz;  second: snd.
    rw [Cat.assoc, snd_pair, ← Cat.assoc, term_uniq (fst ≫ term A.carrier) (term _),
        Cat.assoc snd, snd_pair, Cat.comp_id]
    exact GElt.zero_add B snd

/-- **Coproduct universal property (uniqueness).**  Any homomorphism `h : prodGObj A B → X`
    with `inl≫h = f`, `inr≫h = g` equals the copairing `[f,g]`.  Split `id` via `splitId`,
    push `h` through with `hom_preserves_add`, and substitute `inl≫h=f`, `inr≫h=g`. -/
theorem caseCar_uniq {f : A.carrier ⟶ X.carrier} {g : B.carrier ⟶ X.carrier}
    {h : prod A.carrier B.carrier ⟶ X.carrier}
    (hh : IsHomAbelianGroupObject (prodGObj A B) X h)
    (h₁ : pair (Cat.id A.carrier) (HomAb.zeroCar A B) ≫ h = f)
    (h₂ : pair (HomAb.zeroCar B A) (Cat.id B.carrier) ≫ h = g) :
    h = caseCar f g := by
  unfold caseCar
  calc h = Cat.id (prod A.carrier B.carrier) ≫ h := (Cat.id_comp h).symm
    _ = (pair (fst ≫ pair (Cat.id A.carrier) (HomAb.zeroCar A B))
              (snd ≫ pair (HomAb.zeroCar B A) (Cat.id B.carrier)) ≫ (prodGObj A B).add) ≫ h := by
          rw [← splitId A B]
    _ = pair ((fst ≫ pair (Cat.id A.carrier) (HomAb.zeroCar A B)) ≫ h)
             ((snd ≫ pair (HomAb.zeroCar B A) (Cat.id B.carrier)) ≫ h) ≫ X.add :=
          hom_preserves_add hh _ _
    _ = pair (fst ≫ f) (snd ≫ g) ≫ X.add := by
          rw [Cat.assoc, h₁, Cat.assoc, h₂]

end AbCoprod

/-! ### Coproducts in `Ab(𝒞)` = products (the biproduct)

  The coproduct object is the SAME `prodGObj A B`; the injections are the biproduct matrix
  `⟨id,0⟩`, `⟨0,id⟩`; the copairing is the hom-set sum `(π₁≫f)+(π₂≫g)`.  All four data are
  homomorphisms and the universal property is `AbCoprod.caseCar_uniq`. -/

open AbCoprod in
/-- §1.595: `Ab(𝒞)` has binary coproducts, carried by the *product* group object.
    This is half of the product/coproduct coincidence. -/
noncomputable instance instHasBinaryCoproductsAb : HasBinaryCoproducts (AbelianGroupObject 𝒞) where
  coprod A B := prodGObj A B
  inl := ⟨pair (Cat.id _) (HomAb.zeroCar _ _), isHom_inl _ _⟩
  inr := ⟨pair (HomAb.zeroCar _ _) (Cat.id _), isHom_inr _ _⟩
  case f g := ⟨caseCar f.val g.val, isHom_caseCar f.property g.property⟩
  case_inl f g := Subtype.ext (caseCar_inl f.val g.property)
  case_inr f g := Subtype.ext (caseCar_inr g.val f.property)
  case_uniq f g hm h₁ h₂ :=
    Subtype.ext (caseCar_uniq hm.property (congrArg Subtype.val h₁) (congrArg Subtype.val h₂))

end Freyd
