/-
  Freyd & Scedrov, *Categories and Allegories* §1.595
  The forgetful functor `U : Ab(𝒞) → 𝒞` and the lifted limit/regular structure.

  This file builds, on top of `Fredy/AbAbelian.lean` (the category `Ab(𝒞)`, its
  half-additive biproduct structure, terminal/products), the structure the §1.55 /
  §1.595 exact-representation argument consumes from the FORGETFUL functor:

    * `U : Ab(𝒞) → 𝒞`,  `A ↦ A.carrier`,  `f ↦ f.val` — a `Functor` (Sorry-free).
    * `U` is FAITHFUL on hom-sets (`SeparatesMaps U`): homs are subtypes of 𝒞-maps,
      so `Subtype.ext` gives injectivity.  Cross-universe — `AbelianGroupObject 𝒞`
      lives in `Type (max u v)`, `𝒞` in `Type u` — so we use the cross-universe
      `SeparatesMaps`/`PreservesMono`/`ReflectsMono` API, not the same-universe `Faithful`.
    * `U` REFLECTS isos and monos (`U_reflectsMono`): a 𝒞-mono carrier forces an
      `Ab(𝒞)`-mono, because joint cancellation in `Ab(𝒞)` is carrier cancellation.
    * `U` PRESERVES the terminal and binary products ON THE NOSE: the carrier of the
      zero/product group object *is* `1` / `A.car × B.car`, with carrier projections
      `fst`/`snd`.  (`U_map_fst`, `U_map_snd`, `U_terminal_carrier`.)
    * `U` PRESERVES and REFLECTS isos in both directions (faithful + carrier).

  RESIDUAL (precise): full `HasImages (Ab 𝒞)` / `RegularCategory (Ab 𝒞)` /
  `EffectiveRegular (Ab 𝒞)` is the §1.594 content — it needs the image and the
  effective quotient of a group hom to carry a group structure (image = subgroup
  object, quotient by a congruence).  That requires `[HasImages 𝒞]` / `[EffectiveRegular 𝒞]`
  PLUS transporting the group operations across the 𝒞-image/quotient via their universal
  properties.  We stop at the forgetful functor + faithfulness + finite-limit preservation
  + mono/iso reflection + the additive structure (`instAdditiveAb`, in `AbAbelian`), which is
  exactly the "faithful exact functor that creates finite limits" half of the §1.595
  representation.  See the residual note at the bottom.

  No `Sorry`, no new axiom.
-/

import Fredy.AbAbelian
import Fredy.S1_31
import Fredy.S1_33
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56

open Freyd

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]

/-! ### §1.595 The forgetful functor `U : Ab(𝒞) → 𝒞`

  `U A := A.carrier`,  `U f := f.val`.  Functoriality is immediate: identity and
  composition of `Ab(𝒞)`-morphisms are those of `𝒞` on the carriers (`ab_id_val`,
  `ab_comp_val` from `AbCategory`). -/

/-- The forgetful object map `Ab(𝒞) → 𝒞`. -/
def U (A : AbelianGroupObject 𝒞) : 𝒞 := A.carrier

/-- §1.595: the forgetful functor is a functor.  `map f = f.val`; both functor laws
    hold definitionally because `Ab(𝒞)`-id/comp ARE 𝒞-id/comp on carriers. -/
instance instFunctorU : Functor (U (𝒞 := 𝒞)) where
  map {_ _} f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem U_map_val {A B : AbelianGroupObject 𝒞} (f : A ⟶ B) :
    instFunctorU.map f = f.val := rfl

@[simp] theorem U_obj (A : AbelianGroupObject 𝒞) : U A = A.carrier := rfl

/-! ### §1.595 `U` is faithful

  Homs are `{ x : A.car ⟶ B.car // IsHom … }`, so equal carriers means equal homs.
  Because source/target live in different universes (`AbelianGroupObject 𝒞 : Type (max u v)`
  vs `𝒞 : Type u`), we record the cross-universe `SeparatesMaps`, plus reflection of isos
  by hand — which together are exactly the content of `Faithful` for a same-universe functor. -/

/-- §1.595: `U` SEPARATES MAPS (is injective on each hom-set) — the cross-universe
    form of an embedding.  Two `Ab(𝒞)`-homs with equal carriers are equal (`Subtype.ext`). -/
theorem U_separatesMaps : SeparatesMaps (U (𝒞 := 𝒞)) := by
  intro A B f g h
  exact Subtype.ext h

/-- `U` reflects isomorphisms: a carrier iso whose inverse is itself a homomorphism
    lifts to an `Ab(𝒞)`-iso.  Stated in the form actually available: if `f`'s carrier
    is iso with inverse `g` that is a homomorphism, `f` is iso in `Ab(𝒞)`. -/
theorem U_reflectsIso {A B : AbelianGroupObject 𝒞} (f : A ⟶ B)
    (_hiso : IsIso (instFunctorU.map f)) (g : B.carrier ⟶ A.carrier)
    (hg : IsHomAbelianGroupObject B A g)
    (h1 : f.val ≫ g = Cat.id A.carrier) (h2 : g ≫ f.val = Cat.id B.carrier) :
    IsIso f :=
  ⟨⟨g, hg⟩, Subtype.ext h1, Subtype.ext h2⟩

/-! ### §1.595 `U` reflects monos

  An `Ab(𝒞)`-mono is exactly a carrier-mono.  REFLECTION (`Monic (U f) → Monic f`) is the
  immediate half: jointly cancelling carriers cancels homs.  This is what the §1.55
  representation uses to test monicity of group homs in `𝒞`. -/

/-- §1.595: `U` REFLECTS monos.  If the carrier `f.val` is monic in `𝒞`, then `f` is
    monic in `Ab(𝒞)`: any two homs `p q : W → A` with `p ≫ f = q ≫ f` have equal carriers
    (`p.val ≫ f.val = q.val ≫ f.val`), so `p.val = q.val`, so `p = q`. -/
theorem U_reflectsMono : ReflectsMono (U (𝒞 := 𝒞)) := by
  intro A B f hf W p q hpq
  -- `hpq : p ≫ f = q ≫ f` in Ab(𝒞); take carriers.
  have hval : p.val ≫ f.val = q.val ≫ f.val := congrArg Subtype.val hpq
  exact Subtype.ext (hf p.val q.val hval)

/-! ### §1.595 `U` preserves the terminal object and binary products

  These are ON THE NOSE: the zero group object's carrier IS `1`, the product group
  object's carrier IS `A.car × B.car`, and `U` sends the `Ab(𝒞)`-projections to the
  underlying `𝒞`-projections `fst`/`snd`.  So `U` creates finite limits. -/

/-- `U(1_{Ab}) = 1_𝒞`: the terminal group object is carried by `one`. -/
@[simp] theorem U_terminal_carrier :
    U (instHasTerminalAb.one : AbelianGroupObject 𝒞) = (one : 𝒞) := rfl

/-- `U` sends the unique map `A → 1_{Ab}` to the unique map `A.car → 1`. -/
theorem U_terminal_map (A : AbelianGroupObject 𝒞) :
    instFunctorU.map (instHasTerminalAb.trm A) = term A.carrier := rfl

/-- `U(A ×_{Ab} B) = U A × U B` on carriers. -/
@[simp] theorem U_prod_carrier (A B : AbelianGroupObject 𝒞) :
    U (instHasBinaryProductsAb.prod A B) = prod (U A) (U B) := rfl

/-- `U` sends the `Ab(𝒞)`-first-projection to the underlying `𝒞`-`fst`. -/
@[simp] theorem U_map_fst (A B : AbelianGroupObject 𝒞) :
    instFunctorU.map (instHasBinaryProductsAb.fst (A := A) (B := B)) = fst := rfl

/-- `U` sends the `Ab(𝒞)`-second-projection to the underlying `𝒞`-`snd`. -/
@[simp] theorem U_map_snd (A B : AbelianGroupObject 𝒞) :
    instFunctorU.map (instHasBinaryProductsAb.snd (A := A) (B := B)) = snd := rfl

/-- `U` sends the `Ab(𝒞)`-pairing to the underlying `𝒞`-pairing. -/
@[simp] theorem U_map_pair {X A B : AbelianGroupObject 𝒞}
    (f : X ⟶ A) (g : X ⟶ B) :
    instFunctorU.map (instHasBinaryProductsAb.pair f g) = pair f.val g.val := rfl

/-- **`U` preserves binary products** as a universal property witness: the `U`-image of the
    product cone `(A ×_{Ab} B, fst, snd)` is the genuine 𝒞-product cone of `A.car, B.car`,
    with the SAME projections.  Concretely the three product equations transport verbatim. -/
theorem U_preserves_prod_fst (A B : AbelianGroupObject 𝒞)
    {X : AbelianGroupObject 𝒞} (f : X ⟶ A) (g : X ⟶ B) :
    instFunctorU.map (instHasBinaryProductsAb.pair f g) ≫ fst = f.val := by
  rw [U_map_pair]; exact fst_pair f.val g.val

theorem U_preserves_prod_snd (A B : AbelianGroupObject 𝒞)
    {X : AbelianGroupObject 𝒞} (f : X ⟶ A) (g : X ⟶ B) :
    instFunctorU.map (instHasBinaryProductsAb.pair f g) ≫ snd = g.val := by
  rw [U_map_pair]; exact snd_pair f.val g.val

/-! ### A homomorphism preserves negation

  The companion of `hom_preserves_add`/`hom_preserves_zero`: a hom `h : P → X` carries
  the `P`-inverse of an element to the `X`-inverse of its image. -/

/-- For a homomorphism `h : P → X` and any `u : T → P.carrier`,
    `(u ≫ P.neg) ≫ h = (u ≫ h) ≫ X.neg`.  Both are the additive inverse of `u ≫ h`
    in `X` (uniqueness of inverses, `GElt.neg_unique`). -/
theorem hom_preserves_neg {T : 𝒞} {P X : AbelianGroupObject 𝒞}
    {h : P.carrier ⟶ X.carrier} (hh : IsHomAbelianGroupObject P X h)
    (u : T ⟶ P.carrier) :
    (u ≫ P.neg) ≫ h = (u ≫ h) ≫ X.neg := by
  -- `(u ≫ h) ⊕ ((u ≫ P.neg) ≫ h) = ((u ⊕ ⊖u) ≫ h) = (O_P ≫ h) = O_X`, so the second
  -- summand is `⊖(u ≫ h)` by inverse-uniqueness.
  apply GElt.neg_unique X
  rw [← hom_preserves_add hh u (u ≫ P.neg), GElt.add_neg P u,
      hom_preserves_zero hh (term T)]

/-! ### §1.594 Pullbacks in `Ab(𝒞)`

  Given two homs `f : A → B`, `g : C → B`, their pullback in `Ab(𝒞)` is carried by the
  𝒞-pullback `P` of `f.val, g.val`.  The group operations on `P` are induced by the pullback
  universal property: each operation is the unique map into `P` whose two projections are
  the corresponding operations of `A` and `C`.  The compatibility "agrees after `f`/`g`"
  always holds because `f`/`g` are homomorphisms (they preserve `add`/`zero`/`neg`).
  The four group axioms then transport from `A` and `C` by joint monicity of the pullback
  projections.  This yields `HasPullbacks (Ab 𝒞)` from `[HasPullbacks 𝒞]`. -/

section Pullback

variable [HasPullbacks 𝒞]

namespace AbPullback


variable {A B C : AbelianGroupObject 𝒞} (f : A ⟶ C) (g : B ⟶ C)

/-- The chosen 𝒞-pullback cone of the carrier maps `f.val, g.val`. -/
private noncomputable def pb : HasPullback f.val g.val := HasPullbacks.has f.val g.val

/-- Carrier of the pullback group object: the 𝒞-pullback point. -/
private noncomputable def pbPt : 𝒞 := (pb f g).cone.pt
private noncomputable def p₁ : pbPt f g ⟶ A.carrier := (pb f g).cone.π₁
private noncomputable def p₂ : pbPt f g ⟶ B.carrier := (pb f g).cone.π₂

private theorem pb_w : p₁ f g ≫ f.val = p₂ f g ≫ g.val := (pb f g).cone.w

/-- The lift of a compatible pair `(a, b)` into the pullback. -/
private noncomputable def pbLift {T : 𝒞} (a : T ⟶ A.carrier) (b : T ⟶ B.carrier)
    (h : a ≫ f.val = b ≫ g.val) : T ⟶ pbPt f g :=
  (pb f g).lift ⟨T, a, b, h⟩

@[simp] private theorem pbLift_p₁ {T : 𝒞} (a : T ⟶ A.carrier) (b : T ⟶ B.carrier)
    (h : a ≫ f.val = b ≫ g.val) : pbLift f g a b h ≫ p₁ f g = a :=
  (pb f g).lift_fst ⟨T, a, b, h⟩

@[simp] private theorem pbLift_p₂ {T : 𝒞} (a : T ⟶ A.carrier) (b : T ⟶ B.carrier)
    (h : a ≫ f.val = b ≫ g.val) : pbLift f g a b h ≫ p₂ f g = b :=
  (pb f g).lift_snd ⟨T, a, b, h⟩

/-- The pullback projections are jointly monic (pullback lift-uniqueness). -/
private theorem pb_jointly_monic {T : 𝒞} (u v : T ⟶ pbPt f g)
    (h₁ : u ≫ p₁ f g = v ≫ p₁ f g) (h₂ : u ≫ p₂ f g = v ≫ p₂ f g) : u = v := by
  let c : Cone f.val g.val := ⟨T, v ≫ p₁ f g, v ≫ p₂ f g, by rw [Cat.assoc, Cat.assoc, pb_w]⟩
  have hu : u = (pb f g).lift c := (pb f g).lift_uniq c u h₁ h₂
  have hv : v = (pb f g).lift c := (pb f g).lift_uniq c v rfl rfl
  rw [hu, hv]

/-! The three group operations on `pbPt`, each induced by the pullback. -/

/-- Zero of the pullback group object: lift of `(A.zero, B.zero)`. -/
private noncomputable def pbZero : (one : 𝒞) ⟶ pbPt f g :=
  pbLift f g (term one ≫ A.zero) (term one ≫ B.zero) (by
    -- both equal `term ≫ C.zero`, since `f, g` preserve zero.
    rw [hom_preserves_zero f.property (term one), hom_preserves_zero g.property (term one)])

/-- Negation of the pullback group object: lift of `(p₁ ≫ A.neg, p₂ ≫ B.neg)`. -/
private noncomputable def pbNeg : pbPt f g ⟶ pbPt f g :=
  pbLift f g (p₁ f g ≫ A.neg) (p₂ f g ≫ B.neg) (by
    rw [hom_preserves_neg f.property (p₁ f g), hom_preserves_neg g.property (p₂ f g), pb_w])

/-- Addition of the pullback group object: lift of the componentwise sums. -/
private noncomputable def pbAdd : prod (pbPt f g) (pbPt f g) ⟶ pbPt f g :=
  pbLift f g
    (pair (fst ≫ p₁ f g) (snd ≫ p₁ f g) ≫ A.add)
    (pair (fst ≫ p₂ f g) (snd ≫ p₂ f g) ≫ B.add) (by
      -- push `f` through the `A`-sum, `g` through the `B`-sum, then use `pb_w` componentwise.
      rw [hom_preserves_add f.property (fst ≫ p₁ f g) (snd ≫ p₁ f g),
          hom_preserves_add g.property (fst ≫ p₂ f g) (snd ≫ p₂ f g)]
      simp only [Cat.assoc, pb_w])

/-! ### Projections of the pullback operations

  Each operation projects (via `p₁`/`p₂`) to the corresponding operation of `A`/`C`.
  These reduce every `pbPt` axiom to the axioms of `A` and `C` by `pb_jointly_monic`. -/

@[simp] private theorem pbZero_p₁ : pbZero f g ≫ p₁ f g = term one ≫ A.zero :=
  pbLift_p₁ f g _ _ _
@[simp] private theorem pbZero_p₂ : pbZero f g ≫ p₂ f g = term one ≫ B.zero :=
  pbLift_p₂ f g _ _ _
@[simp] private theorem pbNeg_p₁ : pbNeg f g ≫ p₁ f g = p₁ f g ≫ A.neg :=
  pbLift_p₁ f g _ _ _
@[simp] private theorem pbNeg_p₂ : pbNeg f g ≫ p₂ f g = p₂ f g ≫ B.neg :=
  pbLift_p₂ f g _ _ _
@[simp] private theorem pbAdd_p₁ :
    pbAdd f g ≫ p₁ f g = pair (fst ≫ p₁ f g) (snd ≫ p₁ f g) ≫ A.add :=
  pbLift_p₁ f g _ _ _
@[simp] private theorem pbAdd_p₂ :
    pbAdd f g ≫ p₂ f g = pair (fst ≫ p₂ f g) (snd ≫ p₂ f g) ≫ B.add :=
  pbLift_p₂ f g _ _ _

/-- **Component lemma** for the pullback sum: for any `u w : S → pbPt`,
    `(⟨u,w⟩ ≫ pbAdd) ≫ p₁ = ⟨u≫p₁, w≫p₁⟩ ≫ A.add` (and likewise `p₂`/`B`). -/
private theorem pbAdd_proj_p₁ {S : 𝒞} (u w : S ⟶ pbPt f g) :
    (pair u w ≫ pbAdd f g) ≫ p₁ f g = pair (u ≫ p₁ f g) (w ≫ p₁ f g) ≫ A.add := by
  rw [Cat.assoc, pbAdd_p₁, ← Cat.assoc, ab_pair_precomp, ← Cat.assoc, ← Cat.assoc,
      fst_pair, snd_pair]

private theorem pbAdd_proj_p₂ {S : 𝒞} (u w : S ⟶ pbPt f g) :
    (pair u w ≫ pbAdd f g) ≫ p₂ f g = pair (u ≫ p₂ f g) (w ≫ p₂ f g) ≫ B.add := by
  rw [Cat.assoc, pbAdd_p₂, ← Cat.assoc, ab_pair_precomp, ← Cat.assoc, ← Cat.assoc,
      fst_pair, snd_pair]

/-- The pullback group object: carrier the 𝒞-pullback point, operations induced by
    the pullback universal property; each axiom proved componentwise via `pb_jointly_monic`
    from the corresponding axiom of `A` resp. `B`. -/
noncomputable def pullbackGObj : AbelianGroupObject 𝒞 where
  carrier := pbPt f g
  zero := pbZero f g
  neg := pbNeg f g
  add := pbAdd f g
  add_zero := by
    refine pb_jointly_monic f g _ _ ?_ ?_
    · rw [pbAdd_proj_p₁, Cat.id_comp]
      have e : (term (pbPt f g) ≫ pbZero f g) ≫ p₁ f g = term (pbPt f g) ≫ A.zero := by
        rw [Cat.assoc, pbZero_p₁, ← Cat.assoc, term_uniq (term (pbPt f g) ≫ term one) (term _)]
      rw [e]; exact GElt.zero_add A (p₁ f g)
    · rw [pbAdd_proj_p₂, Cat.id_comp]
      have e : (term (pbPt f g) ≫ pbZero f g) ≫ p₂ f g = term (pbPt f g) ≫ B.zero := by
        rw [Cat.assoc, pbZero_p₂, ← Cat.assoc, term_uniq (term (pbPt f g) ≫ term one) (term _)]
      rw [e]; exact GElt.zero_add B (p₂ f g)
  add_neg := by
    refine pb_jointly_monic f g _ _ ?_ ?_
    · rw [pbAdd_proj_p₁, Cat.id_comp, pbNeg_p₁, Cat.assoc, pbZero_p₁, ← Cat.assoc,
          term_uniq (term (pbPt f g) ≫ term one) (term (pbPt f g))]
      exact GElt.neg_add A (p₁ f g)
    · rw [pbAdd_proj_p₂, Cat.id_comp, pbNeg_p₂, Cat.assoc, pbZero_p₂, ← Cat.assoc,
          term_uniq (term (pbPt f g) ≫ term one) (term (pbPt f g))]
      exact GElt.neg_add B (p₂ f g)
  add_assoc := by
    refine pb_jointly_monic f g _ _ ?_ ?_
    · rw [pbAdd_proj_p₁, Cat.assoc, pbAdd_p₁, ← Cat.assoc, ab_pair_precomp,
          pbAdd_proj_p₁, pbAdd_proj_p₁]
      simp only [Cat.assoc]
      exact GElt.add_assoc A (fst ≫ fst ≫ p₁ f g) (fst ≫ snd ≫ p₁ f g) (snd ≫ p₁ f g)
    · rw [pbAdd_proj_p₂, Cat.assoc, pbAdd_p₂, ← Cat.assoc, ab_pair_precomp,
          pbAdd_proj_p₂, pbAdd_proj_p₂]
      simp only [Cat.assoc]
      exact GElt.add_assoc B (fst ≫ fst ≫ p₂ f g) (fst ≫ snd ≫ p₂ f g) (snd ≫ p₂ f g)
  add_comm := by
    refine pb_jointly_monic f g _ _ ?_ ?_
    · rw [pbAdd_proj_p₁, pbAdd_p₁]
      exact GElt.add_comm A (snd ≫ p₁ f g) (fst ≫ p₁ f g)
    · rw [pbAdd_proj_p₂, pbAdd_p₂]
      exact GElt.add_comm B (snd ≫ p₂ f g) (fst ≫ p₂ f g)

/-! ### The projections and lifts are homomorphisms — `HasPullback` in `Ab(𝒞)` -/

@[simp] private theorem pullbackGObj_add :
    (pullbackGObj f g).add = pbAdd f g := rfl
@[simp] private theorem pullbackGObj_carrier :
    (pullbackGObj f g).carrier = pbPt f g := rfl

/-- `p₁ : pullbackGObj → A` is a homomorphism (its hom square is `pbAdd_p₁`). -/
theorem isHom_p₁ : IsHomAbelianGroupObject (pullbackGObj f g) A (p₁ f g) :=
  pbAdd_p₁ f g
/-- `p₂ : pullbackGObj → B` is a homomorphism (its hom square is `pbAdd_p₂`). -/
theorem isHom_p₂ : IsHomAbelianGroupObject (pullbackGObj f g) B (p₂ f g) :=
  pbAdd_p₂ f g

/-- The lift of a compatible pair of homs `a : D → A`, `b : D → B` (with `a≫f = b≫g`) is a
    homomorphism `D → pullbackGObj`.  Proved by joint monicity of `(p₁, p₂)`: project the
    hom square and reduce to the hom squares of `a` and `b`. -/
theorem isHom_pbLift {D : AbelianGroupObject 𝒞} {a : D.carrier ⟶ A.carrier}
    {b : D.carrier ⟶ B.carrier} (ha : IsHomAbelianGroupObject D A a)
    (hb : IsHomAbelianGroupObject D B b) (h : a ≫ f.val = b ≫ g.val) :
    IsHomAbelianGroupObject D (pullbackGObj f g) (pbLift f g a b h) := by
  unfold IsHomAbelianGroupObject
  refine pb_jointly_monic f g _ _ ?_ ?_
  · rw [Cat.assoc, pbLift_p₁, ha, pullbackGObj_add, pbAdd_proj_p₁]
    simp only [Cat.assoc, pbLift_p₁]
  · rw [Cat.assoc, pbLift_p₂, hb, pullbackGObj_add, pbAdd_proj_p₂]
    simp only [Cat.assoc, pbLift_p₂]

/-- `p₁ ≫ f = p₂ ≫ g` as `Ab(𝒞)`-morphisms (carrier-level `pb_w`). -/
theorem pbCone_w :
    (⟨p₁ f g, isHom_p₁ f g⟩ : pullbackGObj f g ⟶ A) ≫ f
      = (⟨p₂ f g, isHom_p₂ f g⟩ : pullbackGObj f g ⟶ B) ≫ g :=
  Subtype.ext (pb_w f g)

/-- The pullback cone of `f, g` in `Ab(𝒞)`. -/
noncomputable def pbCone : Cone f g :=
  ⟨pullbackGObj f g, ⟨p₁ f g, isHom_p₁ f g⟩, ⟨p₂ f g, isHom_p₂ f g⟩, pbCone_w f g⟩

/-- §1.594: `Ab(𝒞)` has the pullback of `f, g`: the cone `pbCone`, with lift induced from
    the carrier pullback (a homomorphism by `isHom_pbLift`), unique by `pb_jointly_monic`. -/
noncomputable def hasPullbackAb : HasPullback f g where
  cone := pbCone f g
  lift c := ⟨pbLift f g c.π₁.val c.π₂.val (congrArg Subtype.val c.w),
    isHom_pbLift f g c.π₁.property c.π₂.property (congrArg Subtype.val c.w)⟩
  lift_fst _ := Subtype.ext (pbLift_p₁ f g _ _ _)
  lift_snd _ := Subtype.ext (pbLift_p₂ f g _ _ _)
  lift_uniq _ u h₁ h₂ := Subtype.ext (pb_jointly_monic f g u.val _
    ((congrArg Subtype.val h₁).trans (pbLift_p₁ f g _ _ _).symm)
    ((congrArg Subtype.val h₂).trans (pbLift_p₂ f g _ _ _).symm))

end AbPullback

open AbPullback in
/-- §1.594: `Ab(𝒞)` has all pullbacks (lifted from `[HasPullbacks 𝒞]`, computed on carriers). -/
noncomputable instance instHasPullbacksAb : HasPullbacks (AbelianGroupObject 𝒞) where
  has f g := hasPullbackAb f g

end Pullback

/-! ### §1.594 Equalizers in `Ab(𝒞)`

  Given `f g : A ⟶ B` in `Ab(𝒞)`, their equalizer is carried by the 𝒞-equalizer
  `E = eqObj f.val g.val ↪ A.carrier`.  The group structure on `E` is induced by the equalizer
  universal property (same pattern as `AbPullback`): each operation is the unique lift into `E`
  whose post-composition with `eqMap` gives the corresponding operation of `A`, and the
  coherence conditions hold because `f` and `g` are group homs.  The four group axioms
  transport from `A` by monicity of `eqMap`.  This yields `HasEqualizers (Ab 𝒞)` from
  `[HasEqualizers 𝒞]`. -/

section Equalizer

variable [HasEqualizers 𝒞]

namespace AbEqualizer

variable {A B : AbelianGroupObject 𝒞} (f g : A ⟶ B)

private noncomputable def em : eqObj f.val g.val ⟶ A.carrier := eqMap f.val g.val

private theorem em_eq : em f g ≫ f.val = em f g ≫ g.val := eqMap_eq f.val g.val

/-- The equalizer map is monic in 𝒞. -/
private theorem em_mono : Monic (em f g) := eqMap_mono' f.val g.val

/-- The equalizer lift. -/
private noncomputable def eLift {X : 𝒞} (k : X ⟶ A.carrier) (h : k ≫ f.val = k ≫ g.val) :
    X ⟶ eqObj f.val g.val :=
  eqLift f.val g.val k h

@[simp] private theorem eLift_fac {X : 𝒞} (k : X ⟶ A.carrier) (h : k ≫ f.val = k ≫ g.val) :
    eLift f g k h ≫ em f g = k :=
  eqLift_fac f.val g.val k h

private theorem eLift_uniq {X : 𝒞} (k : X ⟶ A.carrier) (h : k ≫ f.val = k ≫ g.val)
    (u : X ⟶ eqObj f.val g.val) (hu : u ≫ em f g = k) : u = eLift f g k h :=
  eqLift_uniq f.val g.val k h u hu

/-! Three group operations on `eqObj f.val g.val`, each the unique lift whose composite with
    `eqMap` gives the corresponding operation of `A`.  Coherence holds because `f` and `g` are
    group homs. -/

/-- Zero of the equalizer group object: lift of `term one ≫ A.zero`. -/
private noncomputable def eqZero : (one : 𝒞) ⟶ eqObj f.val g.val :=
  eLift f g (term one ≫ A.zero) (by
    rw [hom_preserves_zero f.property (term one), hom_preserves_zero g.property (term one)])

/-- Negation of the equalizer group object: lift of `eqMap ≫ A.neg`. -/
private noncomputable def eqNeg : eqObj f.val g.val ⟶ eqObj f.val g.val :=
  eLift f g (em f g ≫ A.neg) (by
    rw [hom_preserves_neg f.property (em f g), hom_preserves_neg g.property (em f g), em_eq])

/-- Addition of the equalizer group object: lift of componentwise sum. -/
private noncomputable def eqAdd :
    prod (eqObj f.val g.val) (eqObj f.val g.val) ⟶ eqObj f.val g.val :=
  eLift f g (pair (fst ≫ em f g) (snd ≫ em f g) ≫ A.add) (by
    rw [hom_preserves_add f.property (fst ≫ em f g) (snd ≫ em f g),
        hom_preserves_add g.property (fst ≫ em f g) (snd ≫ em f g)]
    -- goal: pair (fst ≫ em f g ≫ f.val) (snd ≫ em f g ≫ f.val) ≫ B.add
    --     = pair (fst ≫ em f g ≫ g.val) (snd ≫ em f g ≫ g.val) ≫ B.add
    -- follows by rewriting em_eq : em f g ≫ f.val = em f g ≫ g.val in both slots.
    have := em_eq f g
    congr 2 <;> simp [Cat.assoc, this])

/-! Projection lemmas: each operation composes with `eqMap` to give the corresponding `A`-op. -/

@[simp] private theorem eqZero_em : eqZero f g ≫ em f g = term one ≫ A.zero :=
  eLift_fac f g _ _

@[simp] private theorem eqNeg_em : eqNeg f g ≫ em f g = em f g ≫ A.neg :=
  eLift_fac f g _ _

@[simp] private theorem eqAdd_em :
    eqAdd f g ≫ em f g = pair (fst ≫ em f g) (snd ≫ em f g) ≫ A.add :=
  eLift_fac f g _ _

/-- Component lemma for the sum: `⟨u,w⟩ ≫ eqAdd ≫ eqMap = ⟨u≫eqMap, w≫eqMap⟩ ≫ A.add`. -/
private theorem eqAdd_proj {S : 𝒞} (u w : S ⟶ eqObj f.val g.val) :
    (pair u w ≫ eqAdd f g) ≫ em f g = pair (u ≫ em f g) (w ≫ em f g) ≫ A.add := by
  rw [Cat.assoc, eqAdd_em, ← Cat.assoc, ab_pair_precomp, ← Cat.assoc, ← Cat.assoc,
      fst_pair, snd_pair]

/-- The equalizer group object: carrier `eqObj f.val g.val`, operations induced above.
    Each group axiom is proved by monicity of `eqMap` from the corresponding axiom of `A`. -/
noncomputable def eqGObj : AbelianGroupObject 𝒞 where
  carrier := eqObj f.val g.val
  zero := eqZero f g
  neg := eqNeg f g
  add := eqAdd f g
  add_zero := by
    apply em_mono f g
    rw [eqAdd_proj, Cat.id_comp]
    have e : (term (eqObj f.val g.val) ≫ eqZero f g) ≫ em f g
           = term (eqObj f.val g.val) ≫ A.zero := by
      rw [Cat.assoc, eqZero_em, ← Cat.assoc,
          term_uniq (term (eqObj f.val g.val) ≫ term one) (term _)]
    rw [e]; exact GElt.zero_add A (em f g)
  add_neg := by
    apply em_mono f g
    rw [eqAdd_proj, Cat.id_comp, eqNeg_em, Cat.assoc, eqZero_em, ← Cat.assoc,
        term_uniq (term (eqObj f.val g.val) ≫ term one) (term _)]
    exact GElt.neg_add A (em f g)
  add_assoc := by
    apply em_mono f g
    rw [eqAdd_proj, Cat.assoc, eqAdd_em, ← Cat.assoc, ab_pair_precomp,
        eqAdd_proj, eqAdd_proj]
    simp only [Cat.assoc]
    exact GElt.add_assoc A (fst ≫ fst ≫ em f g) (fst ≫ snd ≫ em f g) (snd ≫ em f g)
  add_comm := by
    apply em_mono f g
    rw [eqAdd_proj, eqAdd_em]
    exact GElt.add_comm A (snd ≫ em f g) (fst ≫ em f g)

@[simp] private theorem eqGObj_add : (eqGObj f g).add = eqAdd f g := rfl
@[simp] private theorem eqGObj_carrier : (eqGObj f g).carrier = eqObj f.val g.val := rfl

/-- The equalizer inclusion `eqMap : eqGObj → A` is a homomorphism. -/
theorem isHom_em : IsHomAbelianGroupObject (eqGObj f g) A (em f g) :=
  eqAdd_em f g

/-- The lift of a group hom `k : D → A` (with `k ≫ f = k ≫ g`) into `eqGObj` is a hom. -/
theorem isHom_eLift {D : AbelianGroupObject 𝒞} {k : D.carrier ⟶ A.carrier}
    (hk : IsHomAbelianGroupObject D A k) (h : k ≫ f.val = k ≫ g.val) :
    IsHomAbelianGroupObject D (eqGObj f g) (eLift f g k h) := by
  -- Goal: D.add ≫ eLift k h = pair (fst ≫ eLift k h) (snd ≫ eLift k h) ≫ (eqGObj f g).add
  -- Post-compose with em (monic) and show both sides give pair (fst≫k) (snd≫k) ≫ A.add.
  apply em_mono f g
  -- After apply: (D.add ≫ eLift f g k h) ≫ em = (pair(...) ≫ eqGObj.add) ≫ em
  -- LHS = pair (fst ≫ k) (snd ≫ k) ≫ A.add = RHS.
  have lhs : (D.add ≫ eLift f g k h) ≫ em f g = pair (fst ≫ k) (snd ≫ k) ≫ A.add := by
    rw [Cat.assoc, eLift_fac]; exact hk
  have rhs : (pair (fst ≫ eLift f g k h) (snd ≫ eLift f g k h) ≫ (eqGObj f g).add) ≫ em f g
           = pair (fst ≫ k) (snd ≫ k) ≫ A.add := by
    rw [Cat.assoc, eqGObj_add, eqAdd_em, ← Cat.assoc, ab_pair_precomp]
    -- goal: pair (pair(fst≫eLift)(snd≫eLift) ≫ fst ≫ em) (pair(fst≫eLift)(snd≫eLift) ≫ snd ≫ em) ≫ A.add
    --     = pair (fst ≫ k) (snd ≫ k) ≫ A.add
    -- Use fst_pair: pair a b ≫ fst = a; snd_pair: pair a b ≫ snd = b.
    -- After ← Cat.assoc at the pair applications: (pair ≫ fst) ≫ em = eLift ≫ em = k; similarly snd.
    have h1 : pair (fst ≫ eLift f g k h) (snd ≫ eLift f g k h) ≫ fst ≫ em f g = fst ≫ k := by
      rw [← Cat.assoc, fst_pair, Cat.assoc, eLift_fac]
    have h2 : pair (fst ≫ eLift f g k h) (snd ≫ eLift f g k h) ≫ snd ≫ em f g = snd ≫ k := by
      rw [← Cat.assoc, snd_pair, Cat.assoc, eLift_fac]
    rw [h1, h2]
  rw [lhs, rhs]

/-- `eqMap ≫ f = eqMap ≫ g` as Ab-morphisms. -/
theorem eqGObj_w :
    (⟨em f g, isHom_em f g⟩ : eqGObj f g ⟶ A) ≫ f
      = (⟨em f g, isHom_em f g⟩ : eqGObj f g ⟶ A) ≫ g :=
  Subtype.ext (em_eq f g)

/-- The equalizer cone of `f, g` in `Ab(𝒞)`. -/
noncomputable def eqCone : EqualizerCone f g :=
  ⟨eqGObj f g, ⟨em f g, isHom_em f g⟩, eqGObj_w f g⟩

/-- §1.594: `Ab(𝒞)` has the equalizer of `f, g`: the cone `eqCone`, with lift induced from
    the carrier equalizer (a homomorphism by `isHom_eLift`), unique by monicity of `eqMap`. -/
noncomputable def hasEqualizerAb : HasEqualizer f g where
  cone := eqCone f g
  lift c := ⟨eLift f g c.map.val (congrArg Subtype.val c.eq),
    isHom_eLift f g c.map.property (congrArg Subtype.val c.eq)⟩
  fac c := Subtype.ext (eLift_fac f g c.map.val (congrArg Subtype.val c.eq))
  uniq c u hu := Subtype.ext (eLift_uniq f g c.map.val (congrArg Subtype.val c.eq) u.val
    (congrArg Subtype.val hu))

end AbEqualizer

open AbEqualizer in
/-- §1.594: `Ab(𝒞)` has all equalizers (lifted from `[HasEqualizers 𝒞]`, computed on carriers). -/
noncomputable instance instHasEqualizersAb : HasEqualizers (AbelianGroupObject 𝒞) where
  eq _ _ f g := hasEqualizerAb f g

end Equalizer

/-! ### §1.595 `ab_monic_carrier_monic` — U preserves/reflects monics via zero-kernel

  **SHARP MARKER (§1.595 residual).**

  Claim: if `m : M ⟶ B` is monic in `Ab(𝒞)` and `𝒞` is EFFECTIVE REGULAR, then `m.val`
  is monic in `𝒞`.

  PROOF SKETCH (requires `[EffectiveRegular 𝒞]`):
  (1) Factor `m` as `e ≫ i` in `Ab(𝒞)` where `e` is an Ab-cover and `i` is Ab-monic.
      `HasImages (Ab 𝒞)` (from `[EffectiveRegular 𝒞]`) provides this factorization.
  (2) `m` being Ab-monic forces `e` to be Ab-iso (cover + monic = iso in a regular category,
      §1.512). So `m = e ≫ i` with `e` iso, hence `m` is Ab-monic iff `i` is.
      Wait: `m` is Ab-monic, and `m = e ≫ i`. For `m` to be monic, `e` must be iso.
      Proof: if `m` is monic and `e` is a cover, apply `m.monic` to `e` and `id ≫ m`:
      `(id ≫ m) ≫ ... ` — no, simpler: `m = e ≫ i`, `e` cover, `i` monic → in
      a regular category covers are left-cancellable for monics; actually monic ≫ cover ≠ iso.
      The right direction: since `m` is monic and `i` is monic and `m = e ≫ i`,
      `e` must be monic (since a composition of two maps where the first makes the result monic...
      this requires `e` to be monic). `e` is a cover and monic ⟹ `e` is iso.
  (3) Hence `m.val = e.val ≫ i.val`, `e.val` is iso, `i.val` is monic ⟹ `m.val` is monic.

  EXACT DEPENDENCY: `HasImages (Ab 𝒞)` — requires `[EffectiveRegular 𝒞]` for the
  `add_I` operation (closure of image under + via effective-quotient descent).

  NOTE: The weaker `[HasEqualizers 𝒞]` alone does NOT suffice: the 𝒞-hom-sets are plain sets
  (not abelian groups), so "trivial kernel of m.val in 𝒞" (eqObj m.val 0 = one) does not imply
  m.val is monic among all 𝒞-maps — only among those maps `p` satisfying `p ≫ m.val = 0`,
  which is not the same as `p ≫ m.val = q ≫ m.val` for general `p, q`.

  PullbacksTransferCovers and RegularCategory for Ab(𝒞) follow once HasImages + this hold. -/

/-! ### §1.595 Carrier-iso lifts to `Ab(𝒞)`-iso; covers in `Ab(𝒞)` reflect carrier covers

  The key structural lemma: if the carrier of a `HomAb` morphism is an isomorphism,
  then the whole morphism is an isomorphism (the carrier inverse is automatically a group hom).
  This lets us show `Cover f.val → Cover f` for maps in `Ab(𝒞)`. -/

section Covers

/-- If `m : M ⟶ B` is a `HomAb` morphism and `m.val` is an isomorphism in 𝒞,
    then `m` is an isomorphism in `Ab(𝒞)`.

    The inverse hom property of `inv = m.val⁻¹` follows by post-composing with the monic
    `m.val`: `B.add ≫ inv ≫ m.val = B.add` (LHS) equals `pair (fst≫inv) (snd≫inv) ≫ M.add ≫ m.val`
    (RHS, via `m.property` + `inv ≫ m.val = id`), so monicity of `m.val` gives the hom square. -/
theorem isHom_of_carrier_iso {M B : AbelianGroupObject 𝒞} (m : M ⟶ B)
    (hiso : IsIso m.val) : IsIso m := by
  obtain ⟨inv, hinv_l, hinv_r⟩ := hiso
  -- m.val is monic (it has a retraction inv with m.val ≫ inv = id).
  have hm_mono : Monic m.val := mono_of_retraction m.val inv hinv_l
  have hinv_hom : IsHomAbelianGroupObject B M inv := by
    -- Goal: B.add ≫ inv = pair (fst ≫ inv) (snd ≫ inv) ≫ M.add.
    -- Post-compose with m.val (monic) and show both sides equal B.add.
    apply hm_mono
    -- After apply: goal is (B.add ≫ inv) ≫ m.val = (pair(fst≫inv)(snd≫inv) ≫ M.add) ≫ m.val.
    -- LHS = B.add (by hinv_r).  RHS = B.add (by m.property + hinv_r + pair_fst_snd).
    have lhs : (B.add ≫ inv) ≫ m.val = B.add := by
      rw [Cat.assoc, hinv_r, Cat.comp_id]
    have rhs : (pair (fst ≫ inv) (snd ≫ inv) ≫ M.add) ≫ m.val = B.add := by
      -- reassociate inner: pair(a)(b) ≫ (x ≫ m.val) = (pair(a)(b) ≫ x) ≫ m.val = ... ≫ m.val
      have fst_eq : pair (fst ≫ inv) (snd ≫ inv) ≫ (fst ≫ m.val) = fst ≫ inv ≫ m.val := by
        rw [← Cat.assoc, fst_pair]; exact Cat.assoc _ _ _
      have snd_eq : pair (fst ≫ inv) (snd ≫ inv) ≫ (snd ≫ m.val) = snd ≫ inv ≫ m.val := by
        rw [← Cat.assoc, snd_pair]; exact Cat.assoc _ _ _
      rw [Cat.assoc, m.property, ← Cat.assoc, ab_pair_precomp, fst_eq, snd_eq, hinv_r]
      simp only [Cat.comp_id, pair_fst_snd, Cat.id_comp]
    rw [lhs, rhs]
  exact ⟨⟨inv, hinv_hom⟩, Subtype.ext hinv_l, Subtype.ext hinv_r⟩

/-! **RESIDUAL: Ab-monics have monic carriers** (`ab_monic_carrier_monic`)

    STATUS: `HasEqualizers (Ab 𝒞)` is NOW PROVED (see `instHasEqualizersAb` above).
    The remaining blocker for `ab_monic_carrier_monic` is NOT just `HasEqualizers (Ab 𝒞)`:

    The claim "if `m` is Ab-monic then `m.val` is monic in 𝒞" CANNOT be proved from
    `[HasEqualizers 𝒞]` alone.  The 𝒞-hom-sets are plain sets, not abelian groups, so
    "trivial kernel of m.val" (eqObj m.val 0 = one) does NOT imply m.val is monic among
    all 𝒞-maps.  The correct dependency is `[EffectiveRegular 𝒞]` (for `HasImages (Ab 𝒞)`).

    See the SHARP MARKER above (§1.595 residual section) for the precise proof path. -/

/-- If `f.val` is a cover in 𝒞 and `m.val` is monic in 𝒞 (additional hypothesis), then
    `f` is a cover in `Ab(𝒞)`.  This is the clean (←) half of the cover equivalence.

    The full `Cover f.val → Cover f` also needs `U` to preserve monics (see
    `ab_monic_carrier_monic`); once that is available, the proof is immediate. -/
theorem carrier_cover_to_ab_cover_aux {A B M : AbelianGroupObject 𝒞} {f : A ⟶ B}
    (hfval : Cover f.val) (m : M ⟶ B)
    (hm_carrier : Monic m.val) (g : A ⟶ M) (hgm : g ≫ m = f) : IsIso m :=
  isHom_of_carrier_iso m (hfval m.val g.val hm_carrier (congrArg Subtype.val hgm))

end Covers

/-! ### §1.595 Covers of products

  The image construction below descends the addition `A.add ≫ e` along the cover
  `pair (fst ≫ e) (snd ≫ e) : A×A ⟶ I×I`.  We first record that this map of products
  is a cover whenever `e` is.  Both factors are base changes of `e` (each is a pullback of
  `e` along a projection), so `cover_pullback` + `cover_comp` apply.  This is the
  product-of-covers content; it is the only place the descent needs `PullbacksTransferCovers`,
  which `[RegularCategory 𝒞]` supplies. -/

section ProdCovers

variable [HasPullbacks 𝒞] [PullbacksTransferCovers 𝒞] [HasImages 𝒞]

/-- `pair (fst ≫ e) snd : A×X ⟶ I×X` is a cover when `e : A ⟶ I` is (it is the base change
    of `e` along `fst : I×X ⟶ I`).  The cone `(pair (fst≫e) snd, snd)` is a pullback of the
    cospan `(e, fst)`, so `cover_pullback` transfers the cover `e`. -/
theorem coverProdLeft {A I X : 𝒞} {e : A ⟶ I} (he : Cover e) :
    Cover (pair (fst ≫ e) (snd : prod A X ⟶ X)) := by
  -- Pullback of cospan `(e : A → I, fst : I×X → I)`: apex `A×X`, π₁ = fst, π₂ = pair (fst≫e) snd.
  have hpb : (⟨prod A X, fst, pair (fst ≫ e) snd,
      (fst_pair (fst ≫ e) snd).symm⟩ : Cone e (fst (A := I) (B := X))).IsPullback := by
    intro d
    -- d.π₁ : d.pt → A,  d.π₂ : d.pt → I×X,  d.w : d.π₁ ≫ e = d.π₂ ≫ fst.
    refine ⟨pair d.π₁ (d.π₂ ≫ snd), ⟨fst_pair _ _, ?_⟩, ?_⟩
    · show pair d.π₁ (d.π₂ ≫ snd) ≫ pair (fst ≫ e) snd = d.π₂
      apply fst_snd_jointly_monic
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair]; exact d.w
      · rw [Cat.assoc, snd_pair, snd_pair]
    · intro v hv₁ hv₂
      have hv₂' : v ≫ pair (fst ≫ e) snd = d.π₂ := hv₂
      apply fst_snd_jointly_monic
      · rw [fst_pair]; exact hv₁
      · rw [snd_pair, ← hv₂', Cat.assoc, snd_pair]
  intro D m g hm hgm
  exact PullbacksTransferCovers.pullbacks_transfer_covers _ hpb he m g hm hgm

/-- `pair fst (snd ≫ e) : X×A ⟶ X×I` is a cover when `e : A ⟶ I` is (base change of `e`
    along `snd : X×I ⟶ I`). -/
theorem coverProdRight {A I X : 𝒞} {e : A ⟶ I} (he : Cover e) :
    Cover (pair (fst : prod X A ⟶ X) (snd ≫ e)) := by
  have hpb : (⟨prod X A, snd, pair fst (snd ≫ e),
      (snd_pair fst (snd ≫ e)).symm⟩ : Cone e (snd (A := X) (B := I))).IsPullback := by
    intro d
    refine ⟨pair (d.π₂ ≫ fst) d.π₁, ⟨snd_pair _ _, ?_⟩, ?_⟩
    · show pair (d.π₂ ≫ fst) d.π₁ ≫ pair fst (snd ≫ e) = d.π₂
      apply fst_snd_jointly_monic
      · rw [Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair]; exact d.w
    · intro v hv₁ hv₂
      have hv₂' : v ≫ pair fst (snd ≫ e) = d.π₂ := hv₂
      apply fst_snd_jointly_monic
      · rw [fst_pair, ← hv₂', Cat.assoc, fst_pair]
      · rw [snd_pair]; exact hv₁
  intro D m g hm hgm
  exact PullbacksTransferCovers.pullbacks_transfer_covers _ hpb he m g hm hgm

/-- `pair (fst ≫ e) (snd ≫ e) : A×A ⟶ I×I` is a cover when `e : A ⟶ I` is.  Factor as
    `pair (fst≫e) snd ≫ pair fst (snd≫e)` (change left factor, then right). -/
theorem coverProdBoth {A I : 𝒞} {e : A ⟶ I} (he : Cover e) :
    Cover (pair (fst ≫ e) (snd ≫ e) : prod A A ⟶ prod I I) := by
  have hfac : (pair (fst ≫ e) (snd : prod A A ⟶ A)) ≫ pair (fst : prod I A ⟶ I) (snd ≫ e)
      = pair (fst ≫ e) (snd ≫ e) := by
    apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, fst_pair, fst_pair]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, snd_pair]
  have hc : Cover ((pair (fst ≫ e) (snd : prod A A ⟶ A)) ≫ pair (fst : prod I A ⟶ I) (snd ≫ e)) :=
    cover_comp (coverProdLeft he) (coverProdRight he)
  rwa [hfac] at hc

end ProdCovers

/-! ### §1.595 `HasImages (Ab 𝒞)` — the image of a group hom carries a group structure

  For `f : A ⟶ B` in `Ab(𝒞)`, write `e := image.lift f.val : A.car ⟶ I` (a cover,
  `image_lift_cover`) and `m := (image f.val).arr : I ⟶ B.car` (monic), with `e ≫ m = f.val`.
  We put an `AbelianGroupObject` structure on `I = (image f.val).dom`:

  * `zero := A.zero ≫ e` — directly, `(A.zero ≫ e) ≫ m = A.zero ≫ f.val = B.zero`.
  * `neg`  — the DESCENT of `A.neg ≫ e` along the cover `e` (§1.566
    `cover_is_coequalizer_of_level`): the unique `nI` with `e ≫ nI = A.neg ≫ e`.
    Well-defined because `A.neg ≫ e` equalizes the kernel pair of `e` (post-compose the
    monic `m`: `A.neg ≫ f.val = f.val ≫ B.neg`, and `kp_sq` for `f.val`/`e` matches them).
  * `add`  — the DESCENT of `A.add ≫ e` along the cover `ee := pair (fst≫e) (snd≫e)`
    (`coverProdBoth`): the unique `aI` with `ee ≫ aI = A.add ≫ e`.  Well-defined because
    `A.add ≫ e` equalizes the kernel pair of `ee` (post-compose `m`; `f` is a hom, and the
    kernel-pair square of `ee` matches the two summands componentwise).

  All four group axioms transport to `I` by monicity of `m` from those of `A` and `B`, and
  `m` is a homomorphism by construction.  This needs only `[RegularCategory 𝒞]`. -/

section Images

variable [RegularCategory 𝒞]

namespace AbImage

variable {A B : AbelianGroupObject 𝒞} (f : A ⟶ B)

/-- The image carrier of `f.val`. -/
def imI : 𝒞 := (image f.val).dom
/-- The image inclusion `imI ⟶ B.carrier` (monic). -/
def imArr : imI f ⟶ B.carrier := (image f.val).arr
/-- The image cover `A.carrier ⟶ imI` (`= image.lift f.val`). -/
noncomputable def imE : A.carrier ⟶ imI f := image.lift f.val

theorem imArr_monic : Monic (imArr f) := (image f.val).monic
theorem imE_cover : Cover (imE f) := image_lift_cover f.val
theorem imE_imArr : imE f ≫ imArr f = f.val := image.lift_fac f.val

/-- Zero of the image group object: `A.zero ≫ e`. -/
noncomputable def imZero : (one : 𝒞) ⟶ imI f := A.zero ≫ imE f

@[simp] theorem imZero_imArr : imZero f ≫ imArr f = term one ≫ B.zero := by
  rw [imZero, Cat.assoc, imE_imArr]
  have h1 : A.zero = term one ≫ A.zero := by rw [term_uniq (term one) (Cat.id one), Cat.id_comp]
  rw [h1]
  exact hom_preserves_zero f.property (term one)

/-- The descent equation for negation: `A.neg ≫ e` equalizes the kernel pair of `e`. -/
theorem neg_descends :
    kp₁ (f := imE f) ≫ (A.neg ≫ imE f) = kp₂ (f := imE f) ≫ (A.neg ≫ imE f) := by
  apply imArr_monic f
  -- post-compose with the monic `m`; use `A.neg ≫ f.val = f.val ≫ B.neg` and `kp_sq`.
  have key : ∀ k : kernelPair (imE f) ⟶ A.carrier,
      (k ≫ (A.neg ≫ imE f)) ≫ imArr f = (k ≫ imE f) ≫ (imArr f ≫ B.neg) := by
    intro k
    calc (k ≫ (A.neg ≫ imE f)) ≫ imArr f
        = (k ≫ A.neg) ≫ f.val := by
          rw [Cat.assoc, Cat.assoc, imE_imArr, ← Cat.assoc]
      _ = (k ≫ f.val) ≫ B.neg := hom_preserves_neg f.property k
      _ = (k ≫ imE f) ≫ (imArr f ≫ B.neg) := by rw [← imE_imArr]; simp only [Cat.assoc]
  rw [key, key, kp_sq]

/-- Negation of the image group object: the descent of `A.neg ≫ e` along the cover `e`. -/
noncomputable def imNeg : imI f ⟶ imI f :=
  (cover_is_coequalizer_of_level (imE f) (imE_cover f) (A.neg ≫ imE f) (neg_descends f)).choose

theorem imE_imNeg : imE f ≫ imNeg f = A.neg ≫ imE f :=
  (cover_is_coequalizer_of_level (imE f) (imE_cover f) (A.neg ≫ imE f)
    (neg_descends f)).choose_spec.1

@[simp] theorem imNeg_imArr : imNeg f ≫ imArr f = imArr f ≫ B.neg := by
  apply cover_epi (imE_cover f)
  rw [← Cat.assoc, imE_imNeg, Cat.assoc, imE_imArr, ← Cat.assoc, imE_imArr]
  -- goal: A.neg ≫ f.val = f.val ≫ B.neg
  have := hom_preserves_neg f.property (Cat.id A.carrier)
  rwa [Cat.id_comp, Cat.id_comp] at this

/-- The product cover `ee := pair (fst≫e) (snd≫e) : A×A ⟶ I×I`. -/
noncomputable def imEE : prod A.carrier A.carrier ⟶ prod (imI f) (imI f) :=
  pair (fst ≫ imE f) (snd ≫ imE f)

theorem imEE_cover : Cover (imEE f) := coverProdBoth (imE_cover f)

@[simp] theorem imEE_fst : imEE f ≫ fst = fst ≫ imE f := by rw [imEE, fst_pair]
@[simp] theorem imEE_snd : imEE f ≫ snd = snd ≫ imE f := by rw [imEE, snd_pair]

theorem imEE_fst_imArr : imEE f ≫ fst ≫ imArr f = fst ≫ f.val := by
  rw [← Cat.assoc, imEE_fst, Cat.assoc, imE_imArr]
theorem imEE_snd_imArr : imEE f ≫ snd ≫ imArr f = snd ≫ f.val := by
  rw [← Cat.assoc, imEE_snd, Cat.assoc, imE_imArr]

/-- The descent equation for addition: `A.add ≫ e` equalizes the kernel pair of `ee`. -/
theorem add_descends :
    kp₁ (f := imEE f) ≫ (A.add ≫ imE f) = kp₂ (f := imEE f) ≫ (A.add ≫ imE f) := by
  apply imArr_monic f
  -- post-compose `m`: both kp-projections, after `m`, become `(kp_i ≫ ee) ≫ (B-sum of m's)`;
  -- they agree by `kp_sq` for `ee`.
  have key : ∀ k : kernelPair (imEE f) ⟶ prod A.carrier A.carrier,
      (k ≫ (A.add ≫ imE f)) ≫ imArr f
        = (k ≫ imEE f) ≫ (pair (fst ≫ imArr f) (snd ≫ imArr f) ≫ B.add) := by
    intro k
    have hlhs : (k ≫ (A.add ≫ imE f)) ≫ imArr f
        = pair (k ≫ fst ≫ f.val) (k ≫ snd ≫ f.val) ≫ B.add := by
      rw [Cat.assoc, Cat.assoc, imE_imArr,
          show A.add ≫ f.val = pair (fst ≫ f.val) (snd ≫ f.val) ≫ B.add from f.property,
          ← Cat.assoc, ab_pair_precomp]
    have hrhs : (k ≫ imEE f) ≫ (pair (fst ≫ imArr f) (snd ≫ imArr f) ≫ B.add)
        = pair (k ≫ fst ≫ f.val) (k ≫ snd ≫ f.val) ≫ B.add := by
      rw [← Cat.assoc, ab_pair_precomp]
      congr 2
      · rw [Cat.assoc, imEE_fst_imArr]
      · rw [Cat.assoc, imEE_snd_imArr]
    rw [hlhs, hrhs]
  rw [key, key, kp_sq]

/-- Addition of the image group object: the descent of `A.add ≫ e` along the cover `ee`. -/
noncomputable def imAdd : prod (imI f) (imI f) ⟶ imI f :=
  (cover_is_coequalizer_of_level (imEE f) (imEE_cover f) (A.add ≫ imE f)
    (add_descends f)).choose

theorem imEE_imAdd : imEE f ≫ imAdd f = A.add ≫ imE f :=
  (cover_is_coequalizer_of_level (imEE f) (imEE_cover f) (A.add ≫ imE f)
    (add_descends f)).choose_spec.1

/-- The addition projects through `m` to the componentwise `B`-sum. -/
@[simp] theorem imAdd_imArr :
    imAdd f ≫ imArr f = pair (fst ≫ imArr f) (snd ≫ imArr f) ≫ B.add := by
  apply cover_epi (imEE_cover f)
  rw [← Cat.assoc, imEE_imAdd, Cat.assoc, imE_imArr,
      show A.add ≫ f.val = pair (fst ≫ f.val) (snd ≫ f.val) ≫ B.add from f.property,
      ← Cat.assoc, ab_pair_precomp]
  -- RHS now: pair (imEE f ≫ fst ≫ imArr) (imEE f ≫ snd ≫ imArr) ≫ B.add
  congr 2
  · rw [imEE_fst_imArr]
  · rw [imEE_snd_imArr]

/-- **Component lemma** for the image sum: `(⟨u,w⟩ ≫ imAdd) ≫ m = ⟨u≫m, w≫m⟩ ≫ B.add`. -/
theorem imAdd_proj {S : 𝒞} (u w : S ⟶ imI f) :
    (pair u w ≫ imAdd f) ≫ imArr f = pair (u ≫ imArr f) (w ≫ imArr f) ≫ B.add := by
  rw [Cat.assoc, imAdd_imArr, ← Cat.assoc, ab_pair_precomp, ← Cat.assoc, ← Cat.assoc,
      fst_pair, snd_pair]

/-! The group axioms on `imI`, each proved by monicity of `m` from the axioms of `B`,
    using that `m` intertwines the image operations with `B`'s (`imAdd_proj`). -/

/-- The image group object: carrier `(image f.val).dom`, operations descended above. -/
noncomputable def imageGObj : AbelianGroupObject 𝒞 where
  carrier := imI f
  zero := imZero f
  neg := imNeg f
  add := imAdd f
  add_zero := by
    apply imArr_monic f
    rw [imAdd_proj, Cat.id_comp]
    have e : (term (imI f) ≫ imZero f) ≫ imArr f = term (imI f) ≫ B.zero := by
      rw [Cat.assoc, imZero_imArr, ← Cat.assoc, term_uniq (term (imI f) ≫ term one) (term _)]
    rw [e]; exact GElt.zero_add B (imArr f)
  add_neg := by
    apply imArr_monic f
    rw [imAdd_proj, Cat.id_comp, imNeg_imArr, Cat.assoc, imZero_imArr, ← Cat.assoc,
        term_uniq (term (imI f) ≫ term one) (term (imI f))]
    exact GElt.neg_add B (imArr f)
  add_assoc := by
    apply imArr_monic f
    rw [imAdd_proj, Cat.assoc, imAdd_imArr, ← Cat.assoc, ab_pair_precomp,
        imAdd_proj, imAdd_proj]
    simp only [Cat.assoc]
    exact GElt.add_assoc B (fst ≫ fst ≫ imArr f) (fst ≫ snd ≫ imArr f) (snd ≫ imArr f)
  add_comm := by
    apply imArr_monic f
    rw [imAdd_proj, imAdd_imArr]
    exact GElt.add_comm B (snd ≫ imArr f) (fst ≫ imArr f)

@[simp] theorem imageGObj_carrier : (imageGObj f).carrier = imI f := rfl
@[simp] theorem imageGObj_add : (imageGObj f).add = imAdd f := rfl

/-- `m = (image f.val).arr : imageGObj → B` is a homomorphism (its hom square is `imAdd_imArr`). -/
theorem isHom_imArr : IsHomAbelianGroupObject (imageGObj f) B (imArr f) :=
  imAdd_imArr f

/-- `e = image.lift f.val : A → imageGObj` is a homomorphism: post-compose the monic `m`;
    `(A.add ≫ e) ≫ m = pair (fst≫e) (snd≫e) ≫ imAdd ≫ m`, both `= A.add ≫ f.val`. -/
theorem isHom_imE : IsHomAbelianGroupObject A (imageGObj f) (imE f) := by
  show A.add ≫ imE f = pair (fst ≫ imE f) (snd ≫ imE f) ≫ (imageGObj f).add
  rw [imageGObj_add, ← imEE, imEE_imAdd]

/-- The `Ab(𝒞)` morphism carried by `m`. -/
def imArrHom : imageGObj f ⟶ B := ⟨imArr f, isHom_imArr f⟩
/-- The `Ab(𝒞)` morphism carried by `e` (the image cover). -/
noncomputable def imEHom : A ⟶ imageGObj f := ⟨imE f, isHom_imE f⟩

theorem imArrHom_val : (imArrHom f).val = imArr f := rfl
theorem imEHom_val : (imEHom f).val = imE f := rfl

/-- `imArrHom` is monic in `Ab(𝒞)` (carrier monic + `U` reflects monos). -/
theorem imArrHom_monic : Monic (imArrHom f) :=
  U_reflectsMono (f := imArrHom f) (imArr_monic f)

/-- `e ≫ m = f` in `Ab(𝒞)`: the image factorization. -/
theorem image_factorization : imEHom f ≫ imArrHom f = f :=
  Subtype.ext (imE_imArr f)

end AbImage

end Images

/-! ### §1.595 `ab_monic_carrier_monic` — `U` preserves monics (the KERNEL-PAIR route)

  An Ab-monic `m₀ : M → B` has a monic carrier `m₀.val`.  The proof avoids images entirely
  and uses that `Ab(𝒞)` has pullbacks COMPUTED ON CARRIERS (`instHasPullbacksAb`):

  The 𝒞-kernel pair `kernelPair m₀.val` of the carrier carries a group structure
  (`AbPullback.pullbackGObj m₀ m₀`), and its two projections `kp₁, kp₂` are Ab-homomorphisms
  (`AbPullback.isHom_p₁/p₂`) satisfying `⟨kp₁⟩ ≫ m₀ = ⟨kp₂⟩ ≫ m₀` in `Ab(𝒞)`
  (`AbPullback.pbCone_w`).  Since `m₀` is Ab-monic, `⟨kp₁⟩ = ⟨kp₂⟩` as Ab-homs, so `kp₁ = kp₂`
  on carriers.  A map whose kernel-pair projections coincide is 𝒞-monic (lift-uniqueness). -/

section MonicCarrier

variable [HasPullbacks 𝒞]

open AbPullback in
/-- §1.595: an `Ab(𝒞)`-monic `m₀` has a monic carrier.  Kernel-pair route: the carrier
    kernel pair is an internal group object, its projections are homs equalised by `m₀`, so
    Ab-monicity collapses them, forcing `m₀.val` monic. -/
theorem ab_monic_carrier_monic {M B : AbelianGroupObject 𝒞} {m₀ : M ⟶ B}
    (hm₀ : Monic m₀) : Monic m₀.val := by
  have hkp_w : (⟨kp₁ (f := m₀.val), isHom_p₁ m₀ m₀⟩ : pullbackGObj m₀ m₀ ⟶ M) ≫ m₀
             = (⟨kp₂ (f := m₀.val), isHom_p₂ m₀ m₀⟩ : pullbackGObj m₀ m₀ ⟶ M) ≫ m₀ :=
    Subtype.ext kp_sq
  have hkp_eq : kp₁ (f := m₀.val) = kp₂ (f := m₀.val) :=
    congrArg Subtype.val (hm₀ _ _ hkp_w)
  intro W p q hpq
  -- the kernel-pair lift `l` recovers `p, q` as its two projections; `kp₁ = kp₂` collapses them.
  let l := (HasPullbacks.has m₀.val m₀.val).lift ⟨W, p, q, hpq⟩
  have hl₁ : l ≫ kp₁ (f := m₀.val) = p := kp_lift_p₁ p q hpq
  have hl₂ : l ≫ kp₂ (f := m₀.val) = q := kp_lift_p₂ p q hpq
  calc p = l ≫ kp₁ (f := m₀.val) := hl₁.symm
    _ = l ≫ kp₂ (f := m₀.val) := by rw [hkp_eq]
    _ = q := hl₂

end MonicCarrier

/-! ### §1.595 The image factorization, minimality, and `HasImages (Ab 𝒞)`

  With `ab_monic_carrier_monic` the Ab-image is minimal: given an Ab-subobject `S` of `B`
  allowing `f`, `S.arr.val` is 𝒞-monic; `f.val` factors through it, so 𝒞-image minimality
  (`image_min`) yields a comparison carrier `t : imI f → S.dom.carrier`, a hom by monicity
  of `S.arr.val`.  This gives `HasImages (Ab 𝒞)`. -/

section Images2

variable [RegularCategory 𝒞]

open AbImage

/-- The image of `f` as an `Ab(𝒞)`-subobject of `B`.  (Named `abImageSub` to avoid the
    §1.59 `imageSub` for general categories, which carries different hypotheses.) -/
noncomputable def abImageSub {A B : AbelianGroupObject 𝒞} (f : A ⟶ B) :
    Subobject (AbelianGroupObject 𝒞) B :=
  ⟨imageGObj f, imArrHom f, imArrHom_monic f⟩

/-- `abImageSub` allows `f` (via `imEHom`). -/
theorem abImageSub_allows {A B : AbelianGroupObject 𝒞} (f : A ⟶ B) : Allows (abImageSub f) f :=
  ⟨imEHom f, image_factorization f⟩

/-- **Minimality** of the Ab-image: any Ab-subobject `S` of `B` allowing `f` dominates it. -/
theorem abImageSub_min {A B : AbelianGroupObject 𝒞} (f : A ⟶ B)
    (S : Subobject (AbelianGroupObject 𝒞) B) (hAllow : Allows S f) : (abImageSub f).le S := by
  obtain ⟨g, hg⟩ := hAllow
  have hSmono : Monic S.arr.val := ab_monic_carrier_monic S.monic
  have hfac : g.val ≫ S.arr.val = f.val := congrArg Subtype.val hg
  obtain ⟨t, ht⟩ := image_min f.val ⟨S.dom.carrier, S.arr.val, hSmono⟩ ⟨g.val, hfac⟩
  -- `ht : t ≫ S.arr.val = (image f.val).arr`; fold to `imArr f`.
  have hti : t ≫ S.arr.val = imArr f := ht
  have ht_hom : IsHomAbelianGroupObject (imageGObj f) S.dom t := by
    apply hSmono
    -- LHS: (imageGObj.add ≫ t) ≫ m = imAdd ≫ (t≫m) = imAdd ≫ imArr = ⟨fst≫imArr,snd≫imArr⟩≫B.add
    rw [Cat.assoc, hti, imageGObj_add, imAdd_imArr]
    -- RHS: (⟨fst≫t,snd≫t⟩ ≫ S.dom.add) ≫ m = ⟨fst≫t,snd≫t⟩ ≫ ⟨fst≫m,snd≫m⟩ ≫ B.add
    rw [Cat.assoc, S.arr.property, ← Cat.assoc, ab_pair_precomp]
    congr 2
    · rw [← Cat.assoc, fst_pair, Cat.assoc, hti]
    · rw [← Cat.assoc, snd_pair, Cat.assoc, hti]
  exact ⟨⟨t, ht_hom⟩, Subtype.ext ht⟩

/-- §1.595: `abImageSub f` IS the image of `f` in `Ab(𝒞)`. -/
theorem isImage_abImageSub {A B : AbelianGroupObject 𝒞} (f : A ⟶ B) :
    IsImage f (abImageSub f) :=
  ⟨abImageSub_allows f, abImageSub_min f⟩

/-- §1.595: **`Ab(𝒞)` has images** (the 𝒞-image with a descended group structure). -/
noncomputable instance instHasImagesAb : HasImages (AbelianGroupObject 𝒞) where
  image f := abImageSub f
  isImage f := isImage_abImageSub f

/-! ### §1.595 `U` preserves and reflects covers; `PullbacksTransferCovers (Ab 𝒞)`

  `ab_monic_carrier_monic` lets `U` both REFLECT covers (a HomAb with a 𝒞-cover carrier is an
  Ab-cover) and PRESERVE covers (an Ab-cover has a 𝒞-cover carrier, via the image factorization
  `f = e ≫ i`: `f` Ab-cover ⟹ `i` Ab-iso ⟹ `i.val` 𝒞-iso ⟹ `f.val = e.val ≫ i.val` 𝒞-cover). -/

/-- §1.595: a HomAb whose carrier is a 𝒞-cover is an `Ab(𝒞)`-cover.  Test an Ab-monic `n`
    factoring `φ`; its carrier `n.val` is 𝒞-monic (`ab_monic_carrier_monic`), so the 𝒞-cover
    `φ.val` forces `n.val` iso, hence `n` Ab-iso (`isHom_of_carrier_iso`). -/
theorem ab_cover_of_carrier_cover {X Y : AbelianGroupObject 𝒞} {φ : X ⟶ Y}
    (hφ : Cover φ.val) : Cover φ := by
  intro N n k hn hkn
  exact carrier_cover_to_ab_cover_aux hφ n (ab_monic_carrier_monic hn) k hkn

/-- §1.595: an `Ab(𝒞)`-cover has a 𝒞-cover carrier.  Factor `φ = e ≫ i` (image in `Ab(𝒞)`):
    `e = imEHom` (carrier a 𝒞-cover), `i = imArrHom` (Ab-monic).  `φ` Ab-cover and `i` Ab-monic
    ⟹ `i` Ab-iso ⟹ `i.val` 𝒞-iso ⟹ `φ.val = e.val ≫ i.val` is a 𝒞-cover. -/
theorem ab_cover_carrier_cover {X Y : AbelianGroupObject 𝒞} {φ : X ⟶ Y}
    (hφ : Cover φ) : Cover φ.val := by
  -- `φ` factors through the Ab-monic image inclusion `imArrHom φ`; cover forces it iso.
  have hi_iso : IsIso (AbImage.imArrHom φ) :=
    hφ (AbImage.imArrHom φ) (AbImage.imEHom φ) (AbImage.imArrHom_monic φ)
      (AbImage.image_factorization φ)
  obtain ⟨i', hi'1, hi'2⟩ := hi_iso
  -- carrier iso: `imArr φ` has inverse `i'.val`.
  have hival_iso : IsIso (AbImage.imArr φ) :=
    ⟨i'.val, congrArg Subtype.val hi'1, congrArg Subtype.val hi'2⟩
  -- `φ.val = imE φ ≫ imArr φ`, `imE φ` a 𝒞-cover, `imArr φ` a 𝒞-iso (hence cover).
  rw [← AbImage.imE_imArr φ]
  intro D m k hm hkm
  exact cover_comp (AbImage.imE_cover φ) (iso_cover _ hival_iso) m k hm hkm

/-- §1.595: **`Ab(𝒞)` transfers covers across pullbacks.**  The Ab-pullback is computed on
    carriers (`instHasPullbacksAb`), so the comparison to the canonical cone is an Ab-iso; the
    canonical projection's carrier is the 𝒞-pullback projection, a 𝒞-cover by `[PullbacksTransferCovers 𝒞]`
    applied to the 𝒞-cover `φ.val` (`ab_cover_carrier_cover`); reflect back with `ab_cover_of_carrier_cover`. -/
theorem ab_pullbacks_transfer_covers {A B C : AbelianGroupObject 𝒞} {f : A ⟶ B} {g : C ⟶ B}
    (c : Cone f g) (hc : c.IsPullback) (hf : Cover f) : Cover c.π₂ := by
  -- carrier cover of `f`
  have hfval : Cover f.val := ab_cover_carrier_cover hf
  -- the canonical Ab-pullback `P` and its comparison iso to `c`.
  let P := AbPullback.hasPullbackAb f g
  -- φ : c.pt → P.cone.pt (from P universal), ψ : P.cone.pt → c.pt (from c universal).
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, _⟩ := P.cone_isPullback c
  obtain ⟨ψ, ⟨hψ₁, hψ₂⟩, _⟩ := hc P.cone
  -- φ, ψ are mutually inverse (joint monicity of `c` resp. `P`).
  have hφψ : φ ≫ ψ = Cat.id c.pt := by
    have e1 : (φ ≫ ψ) ≫ c.π₁ = c.π₁ := by rw [Cat.assoc, hψ₁, hφ₁]
    have e2 : (φ ≫ ψ) ≫ c.π₂ = c.π₂ := by rw [Cat.assoc, hψ₂, hφ₂]
    obtain ⟨u, _, huniq⟩ := hc c
    exact (huniq _ e1 e2).trans (huniq _ (Cat.id_comp _) (Cat.id_comp _)).symm
  have hψφ : ψ ≫ φ = Cat.id P.cone.pt := by
    have e1 : (ψ ≫ φ) ≫ P.cone.π₁ = P.cone.π₁ := by rw [Cat.assoc, hφ₁, hψ₁]
    have e2 : (ψ ≫ φ) ≫ P.cone.π₂ = P.cone.π₂ := by rw [Cat.assoc, hφ₂, hψ₂]
    obtain ⟨u, _, huniq⟩ := P.cone_isPullback P.cone
    exact (huniq _ e1 e2).trans (huniq _ (Cat.id_comp _) (Cat.id_comp _)).symm
  -- `c.π₂ = φ ≫ P.cone.π₂` (hφ₂); `φ` iso, so `Cover c.π₂ ⟸ Cover P.cone.π₂`.
  have hcanon : Cover P.cone.π₂ := by
    -- carrier `P.cone.π₂.val = (HasPullbacks.has f.val g.val).cone.π₂`, a 𝒞-cover by 𝒞-PTC.
    apply ab_cover_of_carrier_cover
    exact cover_pullback g.val hfval
  rw [← hφ₂]
  intro D m k hm hkm
  exact cover_precomp_iso ⟨ψ, hφψ, hψφ⟩ hcanon m k hm hkm

/-- §1.595: **`Ab(𝒞)` transfers covers across pullbacks** (instance form). -/
instance instPullbacksTransferCoversAb : PullbacksTransferCovers (AbelianGroupObject 𝒞) where
  pullbacks_transfer_covers c hc hf := ab_pullbacks_transfer_covers c hc hf

/-- §1.595 (Freyd, the headline of the section): **`Ab(𝒞)` is a regular category** whenever
    `𝒞` is effective regular.  Assembles `HasTerminal`/`HasBinaryProducts` (`AbAbelian`),
    `HasPullbacks` (`instHasPullbacksAb`), `HasImages` (`instHasImagesAb`), and
    `PullbacksTransferCovers` (`instPullbacksTransferCoversAb`). -/
noncomputable instance instRegularCategoryAb : RegularCategory (AbelianGroupObject 𝒞) :=
  @RegularCategory.mk (AbelianGroupObject 𝒞) instCatAb
    instHasTerminalAb instHasBinaryProductsAb instHasPullbacksAb
    instHasImagesAb instPullbacksTransferCoversAb

/-! ### §1.595 SHARP MARKER — remaining step to `AbelianCategory (Ab 𝒞)` (STAGE 5)

  `RegularCategory (Ab 𝒞)` (above) + `AdditiveCategory (Ab 𝒞)` (`instAdditiveAb`, `AbAbelian`)
  is the hard structural half.  To reach `AbelianCategory (Ab 𝒞)` via the §1.598 route
  `abelian_iff_normal_kernels_cokernels` (which needs `[HasZeroObject][HasEqualizers]
  [HasCoequalizers][HasBinaryProducts] + IsNormalCategory`), THREE pieces remain, each a
  self-contained construction on `Ab(𝒞)`:

  1. **`HasZeroObject (Ab 𝒞)`** — ✅ DONE (`instHasZeroObjectAb`, `AbAbelian`): the zero group
     object is at once terminal (`instHasTerminalAb`) and coterminal (`instHasCoterminatorAb`),
     with `one = coterm` on the nose (`zero_eq_one := rfl`).

  2. **`HasCoequalizers (Ab 𝒞)`** — the coequalizer of `f, g : A → B` is `B ↠ Q` where `Q` is the
     IMAGE (in `Ab(𝒞)`, now available via `instHasImagesAb`) of `B → B/⟨im(f−g)⟩` — concretely
     the effective quotient of `B` by the congruence generated by `f − g` (`f − g := homAddL f
     (neg g)` from `instAdditiveAb`).  In a regular category a coequalizer of a reflexive pair
     is the cover onto the image of the induced relation; for `Ab` use that `Ab(𝒞)` is regular
     (above) + EFFECTIVE: `[EffectiveRegular 𝒞]` should lift to `EffectiveRegular (Ab 𝒞)` because
     the carrier effective quotient (`IsEffective`, §1.56/§1.64) descends a group structure exactly
     as `imageGObj` did.  EXACT BLOCKER: `EffectiveRegular (Ab 𝒞)` — every Ab-equivalence-relation
     is the kernel pair of an Ab-cover; reduce to the carrier `IsEffective` + descend the group
     operations onto the quotient object (mirror `imageGObj`'s `add_descends`/`neg_descends`).

  3. **`IsNormalCategory (Ab 𝒞)`** (= `IsLeftNormal ∧ IsRightNormal`) — every Ab-mono is a kernel
     and every Ab-cover is a cokernel.  This is the genuine §1.598 content and follows from
     1+2 + additivity (`instAdditiveAb`): in an additive regular category with a zero object and
     (co)kernels, mono = ker(coker) and epi = coker(ker).  Mirror the elementary §1.597 argument
     in S1_59 (`exactOfNormal` is the converse; here we need the normality itself, available once
     `Ab(𝒞)` has kernels (= equalizers with 0, DONE via `instHasEqualizersAb`) and cokernels (piece 2)).

  Then: `Nonempty (AbelianCategory (Ab 𝒞)) := abelian_iff_normal_kernels_cokernels hN`.
  The crux is piece 2 (`HasCoequalizers`/`EffectiveRegular (Ab 𝒞)`); pieces 1 and 3 are short
  once it lands.  All of stages 1-4 above are sorry-free with axioms `[propext, Classical.choice]`. -/

end Images2
