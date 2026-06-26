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
  + mono/iso reflection, which is exactly the "faithful exact functor that creates finite
  limits" half of the §1.595 representation.  See the residual note at the bottom.

  No `Sorry`, no new axiom.
-/

import Fredy.AbAbelian
import Fredy.S1_31
import Fredy.S1_33
import Fredy.S1_51
import Fredy.S1_52

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

/-- `g ≫ ⟨a, b⟩ = ⟨g ≫ a, g ≫ b⟩` (local copy; `ab_pair_precomp` of `AbCategory` is private). -/
private theorem ab_pair_precomp' {X Y P Q : 𝒞} (g : X ⟶ Y) (a : Y ⟶ P) (b : Y ⟶ Q) :
    g ≫ pair a b = pair (g ≫ a) (g ≫ b) :=
  pair_uniq (g ≫ a) (g ≫ b) (g ≫ pair a b)
    (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])

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
  rw [Cat.assoc, pbAdd_p₁, ← Cat.assoc, ab_pair_precomp', ← Cat.assoc, ← Cat.assoc,
      fst_pair, snd_pair]

private theorem pbAdd_proj_p₂ {S : 𝒞} (u w : S ⟶ pbPt f g) :
    (pair u w ≫ pbAdd f g) ≫ p₂ f g = pair (u ≫ p₂ f g) (w ≫ p₂ f g) ≫ B.add := by
  rw [Cat.assoc, pbAdd_p₂, ← Cat.assoc, ab_pair_precomp', ← Cat.assoc, ← Cat.assoc,
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
    · rw [pbAdd_proj_p₁, Cat.assoc, pbAdd_p₁, ← Cat.assoc, ab_pair_precomp',
          pbAdd_proj_p₁, pbAdd_proj_p₁]
      simp only [Cat.assoc]
      exact GElt.add_assoc A (fst ≫ fst ≫ p₁ f g) (fst ≫ snd ≫ p₁ f g) (snd ≫ p₁ f g)
    · rw [pbAdd_proj_p₂, Cat.assoc, pbAdd_p₂, ← Cat.assoc, ab_pair_precomp',
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

end Freyd
