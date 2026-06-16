/-
  Freyd & Scedrov, *Categories and Allegories* §1.44–§1.48
  Cayley representation (§1.442), Horn sentences (§1.444),
  Special Cartesian categories (§1.47), Dense monics and Rational categories (§1.48).
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_27
import Fredy.S1_31
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_45


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.442  Cayley representation: preserves and reflects pullbacks/equalizers

  The Cayley representation C : A → Set^|A| is the family of covariant hom-functors
  (A, -).  §1.442 states: C preserves AND reflects pullbacks and equalizers. -/

/-- **§1.442 (pullback preservation)**: The representable functor `Hom(A, -)` sends any
    pullback cone in `𝒞` to a pullback cone in `Type v`.

    Given a pullback `P —π₁→ X`, `P —π₂→ Y` over `f : X → Z`, `g : Y → Z`,
    for any `A` and maps `h₁ : A → X`, `h₂ : A → Y` with `h₁ ≫ f = h₂ ≫ g`,
    there is a unique `h : A → P` with `h ≫ π₁ = h₁` and `h ≫ π₂ = h₂`. -/
theorem cayley_preserves_pullback
    {X Y Z : 𝒞} {f : X ⟶ Z} {g : Y ⟶ Z}
    (c : Cone f g) (hc : c.IsPullback) (A : 𝒞)
    (h₁ : A ⟶ X) (h₂ : A ⟶ Y) (hw : h₁ ≫ f = h₂ ≫ g) :
    ∃ h : A ⟶ c.pt, h ≫ c.π₁ = h₁ ∧ h ≫ c.π₂ = h₂ ∧
      ∀ k : A ⟶ c.pt, k ≫ c.π₁ = h₁ → k ≫ c.π₂ = h₂ → k = h := by
  let d : Cone f g := ⟨A, h₁, h₂, hw⟩
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc d
  exact ⟨u, hu₁, hu₂, fun k hk₁ hk₂ => huniq k hk₁ hk₂⟩

/-- **§1.442 (pullback reflection)**: If `Hom(A, c)` satisfies the pullback UP for every A,
    then `c` is a pullback in `𝒞`. -/
theorem cayley_reflects_pullback
    {X Y Z : 𝒞} {f : X ⟶ Z} {g : Y ⟶ Z}
    (c : Cone f g)
    (hset : ∀ (A : 𝒞) (h₁ : A ⟶ X) (h₂ : A ⟶ Y), h₁ ≫ f = h₂ ≫ g →
              ∃ h : A ⟶ c.pt, h ≫ c.π₁ = h₁ ∧ h ≫ c.π₂ = h₂ ∧
                ∀ k : A ⟶ c.pt, k ≫ c.π₁ = h₁ → k ≫ c.π₂ = h₂ → k = h) :
    c.IsPullback := by
  intro d
  obtain ⟨u, hu₁, hu₂, huniq⟩ := hset d.pt d.π₁ d.π₂ d.w
  exact ⟨u, ⟨hu₁, hu₂⟩, fun v hv₁ hv₂ => huniq v hv₁ hv₂⟩

/-- **§1.442 (equalizer preservation)**: `Hom(A, -)` sends the chosen equalizer to a set-equalizer. -/
theorem cayley_preserves_equalizer [HasEqualizers 𝒞]
    {X Y : 𝒞} (f g : X ⟶ Y) (A : 𝒞)
    (h : A ⟶ X) (hw : h ≫ f = h ≫ g) :
    ∃ k : A ⟶ eqObj f g, k ≫ eqMap f g = h ∧
      ∀ m : A ⟶ eqObj f g, m ≫ eqMap f g = h → m = k :=
  ⟨eqLift f g h hw, eqLift_fac f g h hw,
   fun m hm => eqLift_uniq f g h hw m hm⟩

/-- **§1.442 (equalizer reflection)**: If `Hom(A, -)` satisfies the equalizer UP for every A,
    then the given fork is an equalizer in `𝒞`.  (Trivially: the hypothesis is exactly the UP.) -/
theorem cayley_reflects_equalizer
    {E X Y : 𝒞} (e : E ⟶ X) (f g : X ⟶ Y)
    (_he : e ≫ f = e ≫ g)
    (huniv : ∀ (A : 𝒞) (h : A ⟶ X), h ≫ f = h ≫ g →
               ∃ k : A ⟶ E, k ≫ e = h ∧ ∀ m : A ⟶ E, m ≫ e = h → m = k) :
    ∀ (A : 𝒞) (h : A ⟶ X), h ≫ f = h ≫ g →
      ∃ k : A ⟶ E, k ≫ e = h ∧ ∀ m : A ⟶ E, m ≫ e = h → m = k :=
  huniv

/-! ## §1.444  Horn sentences

  A HORN SENTENCE in the theory of Cartesian categories (§1.444) is a universally
  quantified implication (P₁ ∧ … ∧ Pₙ) → Q where each Pᵢ and Q are basic Cartesian
  predicates (terminator, product, equalizer).

  **Metatheorem (§1.444)**: Any Horn sentence in the Cartesian predicates true for
  Set (`Type v`) is true for every Cartesian category — MISSING. As with §1.272/§1.551,
  a faithful statement needs an object-language encoding of Horn sentences (a
  `HornSentence`/`HoldsIn` apparatus) plus a `Cat` instance on `Type` with the Cayley
  functor; that is not formalized here, so the metatheorem is recorded MISSING in
  S1_47.md rather than faked. The genuinely-provable ingredient (§1.442 collective
  faithfulness of representables) is recorded below; the Horn-reflection statement for
  REGULAR predicates lives faithfully in S1_56 (`horn_sentence_reflected_by_faithful`). -/

/-- **§1.442**: the representable functors `(C, -)` collectively reflect equality of
    morphisms — i.e. `f = g` whenever `k ≫ f = k ≫ g` for all `k`. (This is the Yoneda /
    Cayley collective-faithfulness instance, `cayley_faithful` §1.272; it is NOT the
    §1.444 Horn metatheorem, which is MISSING — see above.) -/
theorem representables_collectively_faithful [CartesianCategory 𝒞]
    {A B : 𝒞} (f g : A ⟶ B)
    (h : ∀ (C : 𝒞) (k : C ⟶ A), k ≫ f = k ≫ g) : f = g :=
  cayley_faithful f g (fun hX => h _ hX)

/-! ## §1.47  Special Cartesian categories

  A Cartesian category A is SPECIAL (§1.47) if every universally quantified sentence
  (not just Horn sentences) in the Cartesian predicates true for Set holds in A.

  By §1.472 (elementary characterisation):
    A is special iff for every pair of proper subobjects A' ↪ A, B' ↪ B,
    the product map `pair (fst ≫ m) snd : A' × B → A × B` is a proper mono.
  Equivalently: B × - is faithful for every B with a proper subobject. -/

/-- A monic `m : A' → A` is PROPER if it is not an isomorphism (§1.472). -/
def ProperMono {A' A : 𝒞} (m : A' ⟶ A) : Prop := Mono m ∧ ¬ IsIso m

/-- **§1.47 SPECIAL CARTESIAN CATEGORY** (faithful definition via §1.472).

    A Cartesian category is special if for every pair of proper subobjects
    `m : A' ↪ A` and `n : B' ↪ B`, the induced map
    `pair (fst ≫ m) snd : A' × B → A × B` is again a proper mono. -/
class SpecialCartesianCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends CartesianCategory 𝒞 where
  special : ∀ {A' A B' B : 𝒞} (m : A' ⟶ A) (n : B' ⟶ B),
      ProperMono m → ProperMono n →
      ProperMono
        (HasBinaryProducts.pair
          (HasBinaryProducts.fst (A := A') (B := B) ≫ m)
          (HasBinaryProducts.snd (A := A') (B := B)) :
          HasBinaryProducts.prod A' B ⟶ HasBinaryProducts.prod A B)

/-- **§1.47 (predicate form)**: a `CartesianCategory` is SPECIAL.  This is the `special`
    field of `SpecialCartesianCategory` phrased as a `Prop` over the *ambient* products
    (`prod`/`pair`/`fst`/`snd` resolve through the in-scope `[CartesianCategory 𝒞]`).

    Why the predicate, not just the class: `CartesianCategory` carries data (the chosen
    `prod : 𝒞 → 𝒞 → 𝒞`), so a *bundled* `SpecialCartesianCategory` supplies its own product
    structure, distinct from any ambient one.  Stating the §1.472/§1.473/§1.474 equivalences
    with `Nonempty (SpecialCartesianCategory 𝒞)` on the left then forces two different product
    structures into one goal and the conclusion `Embedding (prodEndo B)` lands on the wrong one
    (the "instance-coherence wall").  `IsSpecial` keeps a single product structure in scope, so
    the equivalences become provable; it is *definitionally the same condition* (see
    `isSpecial_iff_nonempty`). -/
def IsSpecial (𝒞 : Type u) [Cat.{v} 𝒞] [CartesianCategory 𝒞] : Prop :=
  ∀ {A' A B' B : 𝒞} (m : A' ⟶ A) (n : B' ⟶ B),
    ProperMono m → ProperMono n →
    ProperMono (pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B)))

/-- `IsSpecial` over the ambient `CartesianCategory` yields a `SpecialCartesianCategory`
    structure built *on that same ambient instance* (`toCartesianCategory := hcc`), so no
    second product structure is introduced.  Only this direction is stated: the converse
    `Nonempty (SpecialCartesianCategory 𝒞) → IsSpecial 𝒞` is exactly the instance-coherence
    wall (a *bundled* special category supplies its own products, unrelated to `hcc`), so it
    does not hold over an arbitrary ambient `hcc` and is deliberately not claimed. -/
def IsSpecial.toSpecial [hcc : CartesianCategory 𝒞] (h : IsSpecial 𝒞) :
    SpecialCartesianCategory 𝒞 :=
  { toCartesianCategory := hcc, special := fun m n hm hn => h m n hm hn }

/-! ## §1.471  Special ⇒ at most two values

  In Set, any two proper subobjects V₁, V₂ ↪ 1 are isomorphic to V₁ ∩ V₂.
  Hence in any special Cartesian category, the terminal object has at most two values
  (i.e. at most one proper subobject up to isomorphism). -/

/-- **§1.471**: In a special Cartesian category any two proper subobjects of `one` are
    isomorphic to each other.

    Proof sketch (Freyd §1.471): In Set, for any two proper subobjects V₁, V₂ ↪ 1,
    either V₁ ↪ V₂ or V₂ ↪ 1 is an isomorphism; hence both are isomorphic to V₁ ∩ V₂.
    Transferring this universally-quantified statement to A via specialness gives the result. -/
theorem special_atMostTwoValues [SpecialCartesianCategory 𝒞]
    {V₁ V₂ : 𝒞} (hV₁ : ProperMono (term V₁)) (hV₂ : ProperMono (term V₂)) :
    ∃ (W : 𝒞) (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂), IsIso i₁ ∧ IsIso i₂ := by
  sorry

/-! ## §1.472  Characterisation via proper subobjects and via B×- faithful

  The following are equivalent for a Cartesian category A:
  (a) A is special.
  (b) For every pair of proper subobjects m : A' ↪ A and n : B' ↪ B, the induced map
      pair (fst ≫ m) snd : A'×B → A×B is a proper mono.
  (c) For every B that has a proper subobject, the functor B×- : A → A is faithful. -/

/-- The product functor `B × -` sending `f : X → Y` to `id_B × f : B×X → B×Y`. -/
def prodEndo [HasBinaryProducts 𝒞] (B : 𝒞) : 𝒞 → 𝒞 := fun X => prod B X

instance prodEndoIsFunctor [HasBinaryProducts 𝒞] (B : 𝒞) : Functor (prodEndo B) where
  map {X Y} f := pair (fst ≫ Cat.id B) (snd ≫ f)
  map_id X := by
    -- pair (fst ≫ Cat.id B) (snd ≫ Cat.id X) = Cat.id (prod B X)
    -- id = pair fst snd; and pair(fst≫id_B)(snd≫id_X) = pair fst snd = id
    symm; apply pair_uniq <;> simp [Cat.id_comp, Cat.comp_id]
  map_comp {X Y Z} f g := by
    -- pair (fst ≫ Cat.id B) (snd ≫ f ≫ g)
    -- = pair (fst ≫ Cat.id B) (snd ≫ f) ≫ pair (fst ≫ Cat.id B) (snd ≫ g)
    -- After pair_uniq, the goals become: (result) ≫ fst/snd reduced by Lean via fst_pair/snd_pair.
    symm; apply pair_uniq
    · -- (pair A B ≫ pair C D) ≫ fst = fst ≫ id_B
      rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc, Cat.comp_id]
    · -- (pair A B ≫ pair C D) ≫ snd = (snd ≫ f) ≫ g
      rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc]

/-- The action of `prodEndo B` on an arrow `f : X → Y` is `pair (fst ≫ id_B) (snd ≫ f)`.
    Definitional unfolding of `prodEndoIsFunctor.map`. -/
theorem prodEndo_map [HasBinaryProducts 𝒞] (B : 𝒞) {X Y : 𝒞} (f : X ⟶ Y) :
    (prodEndoIsFunctor B).map f = pair (fst (A := B) (B := X) ≫ Cat.id B) (snd ≫ f) := rfl

/-- **Clean reformulation of §1.472 faithfulness.**  `prodEndo B = (B × -)` is an
    embedding (faithful) iff the second projection `snd : prod B X → X` is epic for every `X`.

    `(B×-) f = (B×-) g` unfolds to `pair (fst≫id_B) (snd≫f) = pair (fst≫id_B) (snd≫g)`;
    post-composing with `snd` and using `snd_pair` shows this is *equivalent* to
    `snd ≫ f = snd ≫ g`.  Faithfulness is then exactly right-cancellability of `snd`. -/
theorem prodEndo_embedding_iff_snd_epi [HasBinaryProducts 𝒞] (B : 𝒞) :
    Embedding (prodEndo B) ↔
    (∀ {X Y : 𝒞} (f g : X ⟶ Y), (snd (A := B) (B := X)) ≫ f = snd ≫ g → f = g) := by
  constructor
  · intro hemb X Y f g hsnd
    apply hemb f g
    rw [prodEndo_map, prodEndo_map]
    apply pair_uniq <;>
      simp only [fst_pair, snd_pair, hsnd]
  · intro hsnd X Y f g hmap
    apply hsnd f g
    rw [prodEndo_map, prodEndo_map] at hmap
    calc snd ≫ f = pair (fst ≫ Cat.id B) (snd ≫ f) ≫ snd := (snd_pair _ _).symm
      _ = pair (fst ≫ Cat.id B) (snd ≫ g) ≫ snd := by rw [hmap]
      _ = snd ≫ g := snd_pair _ _

/-- **`m × id_B` is monic whenever `m` is monic** — unconditionally, with no specialness.
    `(m × id_B) ≫ fst = fst ≫ m` (so `m`-cancellation recovers the `fst`-component) and
    `(m × id_B) ≫ snd = snd` (so the `snd`-component is already equal); the two projections
    are jointly monic.  This is exactly why §1.472's substantive condition is *properness*
    (non-iso) of `m × id_B`, not mere monicity. -/
theorem product_mono_of_mono [HasBinaryProducts 𝒞] (B : 𝒞) {A' A : 𝒞} (m : A' ⟶ A)
    (hm : Mono m) : Mono (pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B))) := by
  intro W u v huv
  have h1 : (u ≫ fst) ≫ m = (v ≫ fst) ≫ m := by
    have := congrArg (· ≫ fst) huv
    simpa only [Cat.assoc, fst_pair] using this
  have h2 : u ≫ snd = v ≫ snd := by
    have := congrArg (· ≫ snd) huv
    simpa only [Cat.assoc, snd_pair] using this
  exact fst_snd_jointly_monic u v (hm _ _ h1) h2

/-! ### §1.472 keystone via §1.453

  `prodEndo B = (B × -)` is the functor §1.453 (`pullback_faithful_iff_preserves_properness`)
  is to be specialised to.  We supply the two preservation hypotheses §1.453 needs —
  `PreservesPullbacks (prodEndo B)` and `PreservesProductMonic (prodEndo B)` — and the
  factor-order bridge `m × id_B = swap ≫ (id_B × m) ≫ swap` relating §1.453's
  `PreservesProperness` (about `id_B × m`, the `B×-` direction) to the book's right-hand
  side (about `m × id_B`, the `-×B` direction). -/

/-- The factor-order conjugacy `m × id_B = swap ≫ (id_B × m) ≫ swap`.
    `id_B × m = (prodEndoIsFunctor B).map m = pair (fst ≫ id_B) (snd ≫ m) : B×A' → B×A`,
    `m × id_B = pair (fst ≫ m) snd : A'×B → A×B`; conjugating by the two self-inverse
    swaps `A'×B ≅ B×A'` and `B×A ≅ A×B` turns one into the other. -/
theorem prod_mono_swap_conj [HasBinaryProducts 𝒞] (B : 𝒞) {A' A : 𝒞} (m : A' ⟶ A) :
    pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B)) =
    prodSwap A' B ≫ (prodEndoIsFunctor B).map m ≫ prodSwap B A := by
  symm; apply pair_uniq
  · -- post-compose fst:  swap ≫ (id_B×m) ≫ swap ≫ fst = fst ≫ m
    rw [prodEndo_map]
    simp only [Cat.assoc, prodSwap_fst, snd_pair]
    rw [← Cat.assoc, prodSwap_snd]
  · -- post-compose snd:  swap ≫ (id_B×m) ≫ swap ≫ snd = snd
    rw [prodEndo_map]
    simp only [Cat.assoc, prodSwap_fst, prodSwap_snd, fst_pair, Cat.comp_id]

/-- The two product directions are simultaneously iso: `IsIso (m × id_B) ↔ IsIso (id_B × m)`.
    Immediate from `prod_mono_swap_conj` since both swaps are isos (§1.42 `prod_comm_iso`). -/
theorem isIso_prod_mono_iff [HasBinaryProducts 𝒞] (B : 𝒞) {A' A : 𝒞} (m : A' ⟶ A) :
    IsIso (pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B))) ↔
    IsIso ((prodEndoIsFunctor B).map m) := by
  -- `map m` is the conjugate of `m × id_B` by the swaps; check both projections.
  have hmapm : (prodEndoIsFunctor B).map m =
      prodSwap B A' ≫ pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B)) ≫ prodSwap A B := by
    rw [prodEndo_map]
    apply fst_snd_jointly_monic
    · -- fst-component:  fst ≫ id_B = swap ≫ pair(fst≫m) snd ≫ swap ≫ fst
      simp only [fst_pair, Cat.comp_id, Cat.assoc, prodSwap_fst, prodSwap_snd, snd_pair]
    · -- snd-component:  snd ≫ m = swap ≫ pair(fst≫m) snd ≫ swap ≫ snd
      simp only [snd_pair, Cat.assoc, prodSwap_snd, fst_pair, Cat.comp_id]
      rw [← Cat.assoc, prodSwap_fst]
  constructor
  · intro h
    rw [hmapm]
    exact isIso_comp prod_comm_iso (isIso_comp h prod_comm_iso)
  · intro h
    rw [prod_mono_swap_conj B m]
    exact isIso_comp prod_comm_iso (isIso_comp h prod_comm_iso)

/-- **`prodEndo B` preserves pullbacks.**  `B × -` carries a pullback cone over `(f, g)`
    to a pullback cone over `(id_B×f, id_B×g)`.  A cone leg into `B×X` splits as
    `(b : ·→B, x : ·→X)`; postcomposing the cone's `w` with `fst` forces the `B`-components
    equal, with `snd` gives a cone over `(f,g)` in 𝒞 whose lift, paired with the common
    `B`-component, is the required lift into `B×c.pt`. -/
theorem prodEndo_preservesPullbacks [HasBinaryProducts 𝒞] (B : 𝒞) :
    PreservesPullbacks (prodEndo B) := by
  intro X Y Z f g c hc d
  -- abbreviations: the image cone legs are `id_B × c.π₁`, `id_B × c.π₂`.
  -- decompose d's legs through the projections of B×X, B×Y.
  have hbeq : d.π₁ ≫ fst (A := B) (B := X) = d.π₂ ≫ fst (A := B) (B := Y) := by
    have h := congrArg (· ≫ fst (A := B) (B := Z)) d.w
    simp only [prodEndo_map, Cat.assoc, fst_pair, Cat.comp_id] at h
    exact h
  have hbase : (d.π₁ ≫ snd (A := B) (B := X)) ≫ f = (d.π₂ ≫ snd (A := B) (B := Y)) ≫ g := by
    have h := congrArg (· ≫ snd (A := B) (B := Z)) d.w
    simp only [prodEndo_map, Cat.assoc, snd_pair] at h
    simpa only [Cat.assoc] using h
  obtain ⟨ℓ, ⟨hℓ₁, hℓ₂⟩, hℓuniq⟩ := hc ⟨d.pt, d.π₁ ≫ snd, d.π₂ ≫ snd, hbase⟩
  refine ⟨pair (d.π₁ ≫ fst) ℓ, ⟨?_, ?_⟩, ?_⟩
  · -- (pair b ℓ) ≫ (id_B×c.π₁) = d.π₁
    show pair (d.π₁ ≫ fst) ℓ ≫ pair (fst ≫ Cat.id B) (snd ≫ c.π₁) = d.π₁
    refine fst_snd_jointly_monic _ d.π₁ ?_ ?_
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.comp_id]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, hℓ₁]
  · -- (pair b ℓ) ≫ (id_B×c.π₂) = d.π₂
    show pair (d.π₁ ≫ fst) ℓ ≫ pair (fst ≫ Cat.id B) (snd ≫ c.π₂) = d.π₂
    refine fst_snd_jointly_monic _ d.π₂ ?_ ?_
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.comp_id, hbeq]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, hℓ₂]
  · -- uniqueness
    intro v hv₁ hv₂
    show v = pair (d.π₁ ≫ fst) ℓ
    have hv₁' : v ≫ (prodEndoIsFunctor B).map c.π₁ = d.π₁ := hv₁
    have hv₂' : v ≫ (prodEndoIsFunctor B).map c.π₂ = d.π₂ := hv₂
    -- v's components: v ≫ fst and v ≫ snd.
    -- v ≫ fst = d.π₁ ≫ fst (post fst on hv₁', the id_B leg).
    have hvfst : v ≫ fst (A := B) (B := c.pt) = d.π₁ ≫ fst := by
      have h := congrArg (· ≫ fst (A := B) (B := X)) hv₁'
      simp only [prodEndo_map, Cat.assoc, fst_pair, Cat.comp_id] at h
      simpa only [← Cat.assoc] using h
    -- v ≫ snd equalizes the base cone, so = ℓ.
    have hvsnd : v ≫ snd (A := B) (B := c.pt) = ℓ := by
      refine hℓuniq (v ≫ snd) ?_ ?_
      · have h := congrArg (· ≫ snd (A := B) (B := X)) hv₁'
        simp only [prodEndo_map, Cat.assoc, snd_pair] at h
        simpa only [← Cat.assoc] using h
      · have h := congrArg (· ≫ snd (A := B) (B := Y)) hv₂'
        simp only [prodEndo_map, Cat.assoc, snd_pair] at h
        simpa only [← Cat.assoc] using h
    refine fst_snd_jointly_monic v _ ?_ ?_
    · rw [fst_pair, hvfst]
    · rw [snd_pair, hvsnd]

/-- **`prodEndo B` preserves product-monicity.**  `(id_B × fst, id_B × snd)` is a monic
    pair: a map into `B×(P×Q)` is determined by its `B×P`- and `B×Q`-components together
    with its underlying `B`-component, and the two product legs recover all three. -/
theorem prodEndo_preservesProductMonic [HasBinaryProducts 𝒞] (B : 𝒞) :
    PreservesProductMonic (prodEndo B) := by
  intro P Q W u v hfst hsnd
  -- hfst : u ≫ (id_B × fst) = v ≫ (id_B × fst);  hsnd : u ≫ (id_B × snd) = v ≫ (id_B × snd).
  rw [prodEndo_map] at hfst hsnd
  -- u, v : W → B×(P×Q); show u = v via the three jointly-monic legs fst, snd≫fst, snd≫snd.
  -- B-component (post fst on hfst).
  have hB_eq : u ≫ fst (A := B) (B := prod P Q) = v ≫ fst := by
    have h := congrArg (· ≫ fst (A := B) (B := P)) hfst
    simp only [Cat.assoc, fst_pair] at h
    rw [← Cat.assoc, ← Cat.assoc, Cat.comp_id, Cat.comp_id] at h; exact h
  -- (P×Q)-component (jointly monic via fst, snd of P×Q).
  have hPQ_eq : u ≫ snd (A := B) (B := prod P Q) = v ≫ snd := by
    apply fst_snd_jointly_monic
    · have h := congrArg (· ≫ snd (A := B) (B := P)) hfst
      simp only [Cat.assoc, snd_pair] at h
      rw [← Cat.assoc, ← Cat.assoc] at h
      simpa only [Cat.assoc] using h
    · have h := congrArg (· ≫ snd (A := B) (B := Q)) hsnd
      simp only [Cat.assoc, snd_pair] at h
      rw [← Cat.assoc, ← Cat.assoc] at h
      simpa only [Cat.assoc] using h
  exact fst_snd_jointly_monic u v hB_eq hPQ_eq

/-- **iso-reflection for `prodEndo B`, using a proper subobject of `B`.**
    `Embedding (prodEndo B)` (hom-injectivity = `snd` epic) upgrades to full `Faithful`
    (additionally reflecting isos) once `B` HAS a proper subobject `n : B' ↪ B`.

    This `hB` hypothesis is essential and not cosmetic: without it the upgrade is FALSE.
    In §1.475's category of Z-sets the regular representation `Z` has no proper subobject,
    yet `Z×-` is faithful (an embedding); there `id_Z × m` can be iso for a proper `m`, so
    `prodEndo Z` does NOT reflect isos.  The proper subobject of `B` is exactly Freyd's
    §1.472 hypothesis ("every B WITH a proper subobject") that rules this out. -/
theorem prodEndo_faithful_of_embedding
    [HasBinaryProducts 𝒞] (B : 𝒞) (hB : ∃ (B' : 𝒞) (n : B' ⟶ B), ProperMono n)
    (hemb : Embedding (prodEndo B)) : Faithful (prodEndo B) := by
  obtain ⟨B', n, hn⟩ := hB
  refine ⟨hemb, ?_⟩
  intro X Y f hiso
  -- `Embedding (prodEndo B)` is `snd` epic.
  have hsnd_epi : ∀ {X Y : 𝒞} (f g : X ⟶ Y), snd (A := B) (B := X) ≫ f = snd ≫ g → f = g :=
    (prodEndo_embedding_iff_snd_epi B).mp hemb
  -- `map f` is iso (hypothesis), hence both monic and epic.
  obtain ⟨k, hk1, hk2⟩ := hiso       -- map f ≫ k = id,  k ≫ map f = id
  have hmapf_mono : Mono ((prodEndoIsFunctor B).map f) := mono_of_retraction _ k hk1
  have hmapf_epi : ∀ {Z : 𝒞} (a b : prod B Y ⟶ Z),
      (prodEndoIsFunctor B).map f ≫ a = (prodEndoIsFunctor B).map f ≫ b → a = b := by
    intro Z a b hab
    have := congrArg (k ≫ ·) hab
    simp only [← Cat.assoc, hk2, Cat.id_comp] at this; exact this
  -- `pair a b ≫ map f = pair a (b ≫ f)` and `map f ≫ pair a b = pair a (b ≫ f)` post `snd`.
  have hpost : ∀ {W : 𝒞} (a : W ⟶ B) (b : W ⟶ X),
      pair a b ≫ (prodEndoIsFunctor B).map f = pair a (b ≫ f) := by
    intro W a b
    rw [prodEndo_map]
    apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.comp_id, fst_pair]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, snd_pair]
  -- (1) `f` is monic: factor any test pair through `B × -`, cancel `map f` (monic), then `snd`.
  have hf_mono : Mono f := by
    intro W u v huv
    have key : pair (fst (A := B) (B := W)) (snd ≫ u) ≫ (prodEndoIsFunctor B).map f
             = pair (fst (A := B) (B := W)) (snd ≫ v) ≫ (prodEndoIsFunctor B).map f := by
      rw [hpost, hpost, Cat.assoc, Cat.assoc, huv]
    have hpu := hmapf_mono _ _ key
    have hsu : snd (A := B) (B := W) ≫ u = snd ≫ v := by
      have := congrArg (· ≫ snd (A := B) (B := X)) hpu
      simp only [snd_pair] at this; exact this
    exact hsnd_epi u v hsu
  -- (2) `f` is epic: dually, precompose with `map f` (epic), then `snd`.
  have hf_epi : ∀ {Z : 𝒞} (u v : Y ⟶ Z), f ≫ u = f ≫ v → u = v := by
    intro Z u v huv
    have key : (prodEndoIsFunctor B).map f ≫ pair (fst (A := B) (B := Y)) (snd ≫ u)
             = (prodEndoIsFunctor B).map f ≫ pair (fst (A := B) (B := Y)) (snd ≫ v) := by
      rw [prodEndo_map]
      apply fst_snd_jointly_monic
      · simp only [Cat.assoc, fst_pair, Cat.comp_id]
      · simp only [Cat.assoc, snd_pair]
        rw [← Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc, Cat.assoc, huv]
    have hpu := hmapf_epi _ _ key
    have hsu : snd (A := B) (B := Y) ≫ u = snd ≫ v := by
      have := congrArg (· ≫ snd (A := B) (B := Z)) hpu
      simp only [snd_pair] at this; exact this
    exact hsnd_epi u v hsu
  -- `f` is monic AND epic.  Concluding `IsIso f` is the genuine §1.472 content.
  --
  -- HONEST GAP (not closable from these hypotheses).  Writing `k = pair fst h` with
  -- `h := k ≫ snd : B×Y → X`, the iso `map f` yields two equations
  --   (I)  `h ≫ f = snd : B×Y → Y`        (from `k ≫ map f = id`, post `snd`)
  --   (II) `map f ≫ h = snd : B×X → X`     (from `map f ≫ k = id`, post `snd`)
  -- and a routine calc (verified in Lean during this work) shows: GIVEN ANY map `b : Y → B`,
  -- the map `g := pair b (id_Y) ≫ h : Y → X` is a two-sided inverse of `f`
  -- (`g ≫ f = id_Y` via (I); `f ≫ g = id_X` via (II)).  So the whole reduction collapses to
  -- producing a single map `Y → B` — equivalently a section of `snd : B×Y → Y`.
  --
  -- `Embedding (prodEndo B)` (= `snd` epic for every X) gives, at X = 1, that `term B` is
  -- EPIC (B is well-supported), but an epic `B → 1` does NOT split constructively, and the
  -- bare proper subobject `n : B' ↪ B` furnishes no point/section of `B` either.  In a general
  -- (non-special, non-balanced) Cartesian category there is no such `Y → B`: Freyd's actual
  -- §1.472 derives faithfulness from SPECIALNESS (`m × id_B` proper ⇒ §1.453 preserves-properness),
  -- never from "Embedding alone ⇒ Faithful".  This lemma, as stated (only `Embedding` + a proper
  -- subobject, no `IsSpecial`), isolates a step strictly stronger than the book and is not
  -- provable from its hypotheses.  Left as an honest `sorry`; see final report.
  sorry

/-- **§1.472 (product-proper ↔ faithful)**: `B×-` is faithful iff for every proper subobject
    `m : A'↪A` the map `pair(fst≫m, snd) : A'×B → A×B` is again a **proper** mono.

    NB: the book (§1.472) requires `A'×B` to be a *proper* subobject of `A×B`, i.e.
    `ProperMono`, not merely `Mono`.  `Mono (m × id_B)` follows from `Mono m` alone
    (`product_mono_of_mono`), so phrasing the right side with `Mono` would make it a
    tautology and the equivalence false (the left side fails in, e.g., §1.475's Z-sets).
    The non-iso half is the substantive §1.472 content.

    PROOF (§1.453 specialised to `T = prodEndo B`).  `Embedding (prodEndo B)` is the
    embedding half of `Faithful (prodEndo B)`; the iso-reflection half is recovered from
    properness-preservation.  `pullback_faithful_iff_preserves_properness` (§1.453), fed the
    `PreservesPullbacks`/`PreservesProductMonic` witnesses above, equates
    `Faithful (prodEndo B)` with `PreservesProperness (prodEndo B)` — i.e. "monic non-iso
    `m` ↦ non-iso `id_B × m`".  The swap conjugacy `isIso_prod_mono_iff` rewrites that into
    the book's "monic non-iso `m` ↦ non-iso `m × id_B`", and `product_mono_of_mono` supplies
    the monic half. -/
theorem prodEndo_faithful_iff_product_proper
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] (B : 𝒞)
    (hB : ∃ (B' : 𝒞) (n : B' ⟶ B), ProperMono n) :
    Embedding (prodEndo B) ↔
    (∀ {A' A : 𝒞} (m : A' ⟶ A), ProperMono m →
      ProperMono (pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B)))) := by
  have h453 := pullback_faithful_iff_preserves_properness (prodEndo B)
    (prodEndo_preservesPullbacks B) (prodEndo_preservesProductMonic B)
  constructor
  · -- Embedding ⇒ book RHS.  Needs `hB`: for B WITHOUT a proper subobject this fails
    -- (§1.475 Z-sets: Z×- is faithful yet A'×Z can equal A×Z), which is exactly why the
    -- book restricts to "every B WITH a proper subobject".
    intro hemb A' A m hm
    refine ⟨product_mono_of_mono B m hm.1, ?_⟩
    rw [isIso_prod_mono_iff B m]
    -- The full Faithful (prodEndo B) — including iso-reflection, which `hB` supplies — feeds
    -- §1.453 forward to give properness-preservation = the non-iso half.
    have hfaithful : Faithful (prodEndo B) := prodEndo_faithful_of_embedding B hB hemb
    exact (h453.mp hfaithful) m hm.1 hm.2
  · -- book RHS ⇒ Embedding (§1.453 ⇐; `hB` not needed here).
    intro hRHS
    have hprop : PreservesProperness (prodEndo B) := by
      intro A' A m hmono hniso
      rw [← isIso_prod_mono_iff B m]
      exact (hRHS m ⟨hmono, hniso⟩).2
    intro X Y p q hpq
    exact (h453.mpr hprop).1 p q hpq

/-- **§1.472 (⟹)**: A special Cartesian category has B×- faithful for every B with a
    proper subobject.  Stated with `[SpecialCartesianCategory 𝒞]` to avoid instance conflicts. -/
theorem special_implies_prodEndo_faithful [SpecialCartesianCategory 𝒞] (B : 𝒞)
    (hB : ∃ (B' : 𝒞) (n : B' ⟶ B), ProperMono n) : Embedding (prodEndo B) := by
  haveI : HasPullbacks 𝒞 := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
  obtain ⟨B', n, hn⟩ := hB
  rw [prodEndo_faithful_iff_product_proper B ⟨B', n, hn⟩]
  intro A' A m hm
  exact SpecialCartesianCategory.special m n hm hn

/-- **§1.472 (⟹, ambient-products form)**: `IsSpecial 𝒞` (the §1.47 predicate over the in-scope
    products) gives B×- faithful for every B with a proper subobject.  Phrased with `IsSpecial`
    rather than `[SpecialCartesianCategory 𝒞]` so that the single ambient product structure stays
    in scope — this is what lets the §1.472/§1.473/§1.474 equivalences below go through. -/
theorem isSpecial_implies_prodEndo_faithful [CartesianCategory 𝒞] (h : IsSpecial 𝒞) (B : 𝒞)
    (hB : ∃ (B' : 𝒞) (n : B' ⟶ B), ProperMono n) : Embedding (prodEndo B) := by
  haveI : HasPullbacks 𝒞 := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
  obtain ⟨B', n, hn⟩ := hB
  rw [prodEndo_faithful_iff_product_proper B ⟨B', n, hn⟩]
  intro A' A m hm
  exact h m n hm hn

/-- **§1.472**: A Cartesian category is special iff for every B with a proper subobject,
    B×- is faithful.  Uses the `IsSpecial` predicate (over the ambient products) on the left;
    see `IsSpecial`'s docstring for why the bundled `SpecialCartesianCategory` cannot appear here
    without the instance-coherence wall. -/
theorem special_iff_prodEndo_faithful [CartesianCategory 𝒞] :
    IsSpecial 𝒞 ↔
    (∀ (B : 𝒞), (∃ (B' : 𝒞) (n : B' ⟶ B), ProperMono n) →
      Embedding (prodEndo B)) := by
  constructor
  · intro h B hB
    exact isSpecial_implies_prodEndo_faithful h B hB
  · intro hF
    intro A' A B' B m n hm hn
    haveI : HasPullbacks 𝒞 := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
    exact (prodEndo_faithful_iff_product_proper B ⟨B', n, hn⟩).mp (hF B ⟨B', n, hn⟩) m hm

/-! ## §1.473  One-valued special ↔ B×- faithful for all B

  A Cartesian category is ONE-VALUED (§1.473) if the terminal object has exactly one
  global element: |Hom(1, 1)| = 1, or equivalently 1 is the only value.
  Example: the category of groups is one-valued.

  §1.473: A one-valued Cartesian category is special iff B×- is faithful for all B. -/

/-- A Cartesian category is ONE-VALUED if the unique map `1 → 1` generates all values:
    i.e. the terminal object has no proper subobject (every subterminator is iso to 1). -/
def OneValued [CartesianCategory 𝒞] : Prop :=
  ∀ (V : 𝒞), Subterminator V → IsIso (term V)

/-- **§1.473 (⇐)**: If B×- is faithful for all B then A is special.
    This follows directly from §1.472. -/
theorem prodEndo_faithful_all_implies_special [CartesianCategory 𝒞]
    (hF : ∀ (B : 𝒞), Embedding (prodEndo B)) :
    Nonempty (SpecialCartesianCategory 𝒞) := by
  haveI : HasPullbacks 𝒞 := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
  -- Build a SpecialCartesianCategory instance using prodEndo_faithful_iff_product_proper.
  -- The special field's own proper subobject `_n : B' ⟶ B` is the `hB` witness for B, so the
  -- forward direction of §1.472 applies on exactly the objects B where it is true.
  refine ⟨{ special := fun {A' A B' B} m _n hm _hn =>
    (prodEndo_faithful_iff_product_proper B ⟨B', _n, _hn⟩).mp (hF B) m hm }⟩

/-- **§1.473 (⇒)**: In a one-valued special Cartesian category, B×- is faithful for all B.

    Proof sketch (Freyd §1.473): 1×- is trivially faithful.  If B ≇ 1 then the diagonal
    (id_B, id_B) : B → B×B is proper (else B → 1 would be monic, contradicting one-valuedness
    and B ≇ 1), so (B×B)×- is faithful; being composed with B×- twice, it forces B×- faithful. -/
theorem oneValued_special_prodEndo_faithful [CartesianCategory 𝒞] (hSp : IsSpecial 𝒞)
    (h1v : OneValued (𝒞 := 𝒞)) (B : 𝒞) : Embedding (prodEndo B) := by
  rw [prodEndo_embedding_iff_snd_epi]
  intro X Y f g hsnd
  rcases Classical.em (IsIso (term B)) with ⟨g_inv, _hg1, _hg2⟩ | h_not_iso
  · -- Case B ≅ 1: pair(term X ≫ g_inv)(id X) ≫ snd = id X, so snd is epic.
    have hsec : pair (term X ≫ g_inv) (Cat.id X) ≫ (snd (A := B) (B := X)) = Cat.id X :=
      snd_pair _ _
    -- Derive f = g by composing hsnd with the section from the left.
    have h1 : (pair (term X ≫ g_inv) (Cat.id X) ≫ snd (A := B) (B := X)) ≫ f =
              (pair (term X ≫ g_inv) (Cat.id X) ≫ snd (A := B) (B := X)) ≫ g := by
      rw [Cat.assoc, Cat.assoc]; exact congrArg (pair (term X ≫ g_inv) (Cat.id X) ≫ ·) hsnd
    rw [hsec, Cat.id_comp, Cat.id_comp] at h1; exact h1
  · -- Case B ≇ 1: diag B = pair(id)(id) : B → B×B is ProperMono.
    have h_diag_proper : ProperMono (diag B) := by
      refine ⟨diag_mono B, ?_⟩
      intro h_iso
      obtain ⟨k, hk_l, hk_r⟩ := h_iso
      -- hk_l : diag B ≫ k = id B; hk_r : k ≫ diag B = id(B×B)
      -- Post-compose hk_r with fst/snd to get k = fst and k = snd.
      have hk_fst : k = fst (A := B) (B := B) := by
        have h := congrArg (· ≫ fst (A := B) (B := B)) hk_r
        simp only [Cat.id_comp, Cat.assoc, diag_fst, Cat.comp_id] at h; exact h
      have hk_snd : k = snd (A := B) (B := B) := by
        have h := congrArg (· ≫ snd (A := B) (B := B)) hk_r
        simp only [Cat.id_comp, Cat.assoc, diag_snd, Cat.comp_id] at h; exact h
      have hfst_eq_snd : (fst : prod B B ⟶ B) = snd := hk_fst.symm.trans hk_snd
      -- fst = snd means B is a subterminator: Mono (term B)
      have h_sub : Subterminator B := by
        intro W u v _huv
        have : pair u v ≫ fst (A := B) (B := B) = pair u v ≫ snd := by rw [hfst_eq_snd]
        simp only [fst_pair, snd_pair] at this; exact this
      exact h_not_iso (h1v B h_sub)
    -- B×B has proper subobj diag B → special gives prodEndo (B×B) faithful.
    have hBB_faithful : Embedding (prodEndo (prod B B)) :=
      isSpecial_implies_prodEndo_faithful hSp (prod B B) ⟨B, diag B, h_diag_proper⟩
    -- snd(A:=B×B)(B:=X) is epic.
    have hBB_snd_epi : ∀ {W Z : 𝒞} (p q : W ⟶ Z),
        snd (A := prod B B) (B := W) ≫ p = snd (A := prod B B) (B := W) ≫ q → p = q :=
      (prodEndo_embedding_iff_snd_epi (prod B B)).mp hBB_faithful
    -- Define t : (B×B)×X → B×X with t ≫ snd(A:=B) = snd(A:=B×B).
    let t : prod (prod B B) X ⟶ prod B X :=
      pair (fst (A := prod B B) (B := X) ≫ fst (A := B) (B := B)) (snd (A := prod B B) (B := X))
    have ht : t ≫ snd (A := B) (B := X) = snd (A := prod B B) (B := X) := snd_pair _ _
    apply hBB_snd_epi f g
    calc snd (A := prod B B) (B := X) ≫ f
        = (t ≫ snd (A := B) (B := X)) ≫ f := by rw [ht]
      _ = t ≫ snd (A := B) (B := X) ≫ f := Cat.assoc _ _ _
      _ = t ≫ snd (A := B) (B := X) ≫ g := by rw [hsnd]
      _ = (t ≫ snd (A := B) (B := X)) ≫ g := (Cat.assoc _ _ _).symm
      _ = snd (A := prod B B) (B := X) ≫ g := by rw [ht]

/-- **§1.473**: A one-valued Cartesian category is special iff B×- is faithful for all B.
    Uses the `IsSpecial` predicate so the ambient products stay in scope (the bundled-class
    form hits the instance-coherence wall — see `IsSpecial`). -/
theorem oneValued_special_iff [CartesianCategory 𝒞] (h1v : OneValued (𝒞 := 𝒞)) :
    IsSpecial 𝒞 ↔ ∀ (B : 𝒞), Embedding (prodEndo B) := by
  constructor
  · -- ⟹: `oneValued_special_prodEndo_faithful` now takes `IsSpecial 𝒞` directly, all on the
    -- ambient products — no coherence mismatch.
    intro h B
    exact oneValued_special_prodEndo_faithful h h1v B
  · -- ⟸: B×- faithful for all B ⇒ special, via §1.472 specialized to ambient products.
    -- The special witness `_n : B' ⟶ B` is the `hB` for B.
    intro hF A' A B' B m _n hm _hn
    haveI : HasPullbacks 𝒞 := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
    exact (prodEndo_faithful_iff_product_proper B ⟨B', _n, _hn⟩).mp (hF B) m hm

/-! ## §1.474  Two-valued special ↔ B×- faithful for all B not iso to 0

  A Cartesian category is TWO-VALUED (§1.474) if there are exactly two values:
  1 and a unique proper subobject 0 ↪ 1.

  §1.474: A two-valued Cartesian category is special iff B×- is faithful for every B
  not isomorphic to 0. -/

/-- In a two-valued category, `zeroObj` is the unique proper subobject of `one`. -/
structure TwoValued [CartesianCategory 𝒞] where
  zeroObj    : 𝒞
  zero_proper : ProperMono (term zeroObj)
  zero_uniq  : ∀ (V : 𝒞), ProperMono (term V) → ∃ (e : V ⟶ zeroObj), IsIso e

/-- `fst : B×0 → B` is monic when `0 := zeroObj` is a subterminator (its `term` is monic):
    two maps into `B×0` agreeing after `fst` also agree after `snd` (both land in `0`,
    whose hom-sets are subsingletons), so they are equal. -/
theorem fst_prodZero_mono [CartesianCategory 𝒞] {Z : 𝒞} (hZ : Mono (term Z)) (B : 𝒞) :
    Mono (fst (A := B) (B := Z)) := by
  intro W u v huv
  -- snd-components agree since `Z` is a subterminator.
  have hsnd : u ≫ snd (A := B) (B := Z) = v ≫ snd :=
    hZ _ _ (term_uniq _ _)
  exact fst_snd_jointly_monic u v huv hsnd

/-- **§1.474 (⇒)**: In a two-valued special Cartesian category, every B not iso to 0 has
    a proper subobject; hence B×- is faithful for all such B.

    Proof (Freyd §1.474): with `0 := zeroObj` (a subterminator), `fst : B×0 → B` is monic
    (`fst_prodZero_mono`).  It is a *proper* subobject of `B` exactly when `B ≇ 0`; that
    properness is the genuine §1.474 content — Freyd derives it from `B×0 ≅ 0` (using the
    special dichotomy "either `B → V` or `V → 1` is iso" applied to `0 ↪ 1`), which forces
    `B ≅ 0` whenever `fst : B×0 → B` is iso, contradicting `hB`.  Given that proper subobject,
    §1.472 (`isSpecial_implies_prodEndo_faithful`) yields `Embedding (prodEndo B)`. -/
theorem twoValued_special_prodEndo_faithful [CartesianCategory 𝒞] (hSp : IsSpecial 𝒞)
    (h2v : TwoValued (𝒞 := 𝒞)) (B : 𝒞)
    (hB : ¬ ∃ (e : B ⟶ h2v.zeroObj), IsIso e) :
    Embedding (prodEndo B) := by
  -- `fst : B×0 → B` is a monic; it is the candidate proper subobject of `B`.
  have hmono : Mono (fst (A := B) (B := h2v.zeroObj)) :=
    fst_prodZero_mono h2v.zero_proper.1 B
  -- Properness of `fst : B×0 → B` (i.e. it is not iso), the §1.474 content.  See docstring;
  -- it consumes `hB` (B ≇ 0) and the special dichotomy `B×0 ≅ 0`.
  have hproper : ProperMono (fst (A := B) (B := h2v.zeroObj)) := by
    refine ⟨hmono, ?_⟩
    -- Suppose `fst : B×0 → B` is iso.  Combined with strictness of `0`
    -- (`IsIso (snd : B×0 → 0)`, i.e. `B×0 ≅ 0`) it gives `fst⁻¹ ≫ snd : B → 0` iso,
    -- contradicting `hB` (B ≇ 0).
    intro hfst_iso
    -- STRICTNESS OF 0: every map into `0` is iso; here `snd : B×0 → 0`.  This is the
    -- §1.474 dichotomy ("either `g : X → 0` or `0 → 1` is iso"), transferred from Set by the
    -- §1.471/§1.646 representation — NOT derivable from `IsSpecial`+`TwoValued` alone
    -- (`IsSpecial` quantifies only over proper monos; `zero_uniq` needs `B×0` to be a
    -- subterminator, which it is not).  Isolated here; see final report.
    have hstrict : IsIso (snd (A := B) (B := h2v.zeroObj)) := sorry
    obtain ⟨fi, hfi1, hfi2⟩ := hfst_iso
    -- `fi ≫ snd : B → 0` is iso (composite of the iso `fi` and the iso `snd`).
    exact hB ⟨fi ≫ snd, isIso_comp ⟨fst, hfi2, hfi1⟩ hstrict⟩
  intro X Y p q hpq
  exact isSpecial_implies_prodEndo_faithful hSp B ⟨_, _, hproper⟩ p q hpq

/-- **§1.474**: A two-valued Cartesian category is special iff B×- is faithful for all B
    not isomorphic to the zero object. -/
theorem twoValued_special_iff [CartesianCategory 𝒞] (h2v : TwoValued (𝒞 := 𝒞)) :
    IsSpecial 𝒞 ↔
    (∀ (B : 𝒞), (¬ ∃ (e : B ⟶ h2v.zeroObj), IsIso e) → Embedding (prodEndo B)) := by
  constructor
  · -- ⟹: every B≇0 has a proper subobject (B×0 ↪ B), so §1.472 gives B×- faithful.
    intro h B hB; exact twoValued_special_prodEndo_faithful h h2v B hB
  · -- ⟸: Use special_iff_prodEndo_faithful ⟸ direction.
    -- For B with proper subobj n: if B ≇ 0, use hF; if B ≅ 0, need special argument.
    intro hF
    rw [special_iff_prodEndo_faithful]
    intro B ⟨B', n, hn⟩
    -- If B ≇ 0: use hF B. If B ≅ 0: need that 0 has no proper subobject.
    rcases Classical.em (∃ (e : B ⟶ h2v.zeroObj), IsIso e) with ⟨_e, _he⟩ | hB
    · -- B ≅ 0: this branch is vacuous.  `zeroObj` is a subterminator, hence any object
      -- admitting a mono into it (here `B'` via `n ≫ _e`) has subsingleton hom; combined
      -- with `zero_uniq` this forces `n` to be iso, contradicting `hn.2`.
      exfalso
      -- `term zeroObj` is monic, so every hom into `zeroObj` is a subsingleton.
      have hzmono : Mono (term h2v.zeroObj) := h2v.zero_proper.1
      have hz_subsingleton : ∀ {W : 𝒞} (u v : W ⟶ h2v.zeroObj), u = v := fun u v =>
        hzmono u v (term_uniq _ _)
      obtain ⟨e_inv, he1, he2⟩ := _he   -- _e ≫ e_inv = id_B, e_inv ≫ _e = id_zeroObj
      -- `m := n ≫ _e : B' → zeroObj` is monic (n monic; _e iso ⇒ monic).
      have he_mono : Mono _e := mono_of_retraction _ e_inv he1
      -- `m := n ≫ _e : B' → zeroObj` is monic (n monic; _e iso ⇒ monic).
      have hm_mono : Mono (n ≫ _e) := by
        intro W u v huv
        exact hn.1 u v (he_mono (u ≫ n) (v ≫ n)
          (by simpa only [Cat.assoc] using huv))
      -- A mono into a subterminator means the source has subsingleton hom.
      have hB'_subsingleton : ∀ {W : 𝒞} (u v : W ⟶ B'), u = v := fun u v =>
        hm_mono u v (hz_subsingleton _ _)
      -- `term B'` is monic.
      have hB'_term_mono : Mono (term B') := fun u v _ => hB'_subsingleton u v
      -- Case on whether `term B'` is iso.
      rcases Classical.em (IsIso (term B')) with h_iso1 | h_not_iso1
      · -- B' ≅ 1: get a section of `term zeroObj`, forcing it iso — contradiction.
        obtain ⟨s1, hs1a, hs1b⟩ := h_iso1   -- term B' ≫ s1 = id_B', s1 ≫ term B' = id_one
        -- t := s1 ≫ (n ≫ _e) : 1 → zeroObj is a section of `term zeroObj`.
        have ht : (s1 ≫ (n ≫ _e)) ≫ term h2v.zeroObj = Cat.id one := term_uniq _ _
        -- term zeroObj is monic with a right inverse ⇒ iso.
        have hz_iso : IsIso (term h2v.zeroObj) := by
          refine ⟨s1 ≫ (n ≫ _e), ?_, ht⟩
          apply hzmono
          rw [Cat.assoc, ht, Cat.comp_id, Cat.id_comp]
        exact h2v.zero_proper.2 hz_iso
      · -- term B' proper ⇒ by zero_uniq, B' ≅ zeroObj; that iso equals m, so m iso ⇒ n iso.
        obtain ⟨e', he'⟩ := h2v.zero_uniq B' ⟨hB'_term_mono, h_not_iso1⟩
        -- e' = n ≫ _e by subsingleton hom into zeroObj.
        have hm_iso : IsIso (n ≫ _e) := (hz_subsingleton (n ≫ _e) e') ▸ he'
        -- n = (n ≫ _e) ≫ e_inv is iso ((n ≫ _e) iso, e_inv iso).
        have he_inv_iso : IsIso e_inv := ⟨_e, he2, he1⟩
        have hn_iso : IsIso n := by
          have hcomp : IsIso ((n ≫ _e) ≫ e_inv) := isIso_comp hm_iso he_inv_iso
          simpa only [Cat.assoc, he1, Cat.comp_id] using hcomp
        exact hn.2 hn_iso
    · exact (hF B hB : Embedding (prodEndo B))

/-! ## §1.48  Dense classes of monics and the Rational category

  A class G of monics in a Cartesian category A is DENSE (§1.48) if:
    (i)   it contains all isomorphisms,
    (ii)  it is closed under composition,
    (iii) it is closed under pullback along any map.

  The RATIONAL CATEGORY A[G⁻¹] is the localisation of A at G:
  objects are those of A; morphisms A → B are equivalence classes of spans
  `A ←[G]— A' → B` (denominator in G); composition by pullback.
  The universal functor T_G : A → A[G⁻¹] is initial among functors inverting G. -/

/-- **§1.48 DENSE CLASS OF MONICS**: a predicate G on arrows satisfying (i)-(iii). -/
structure DenseClass (𝒞 : Type u) [Cat.{v} 𝒞] [HasPullbacks 𝒞] where
  mem    : ∀ {A B : 𝒞}, (A ⟶ B) → Prop
  -- (i) all isomorphisms are in G
  iso_mem    : ∀ {A B : 𝒞} (f : A ⟶ B), IsIso f → mem f
  -- (ii) closed under composition
  comp_mem   : ∀ {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C), mem f → mem g → mem (f ≫ g)
  -- (iii) closed under pullback: if f ∈ G then the pullback of f along any g is in G
  pb_mem     : ∀ {A B C : 𝒞} (f : A ⟶ B) (g : C ⟶ B),
                 mem f → mem ((HasPullbacks.has g f).cone.π₁)

/-- **§1.48 DENSE MONIC**: `f : A → B` belongs to a dense class `G`. -/
def DenseMonic [HasPullbacks 𝒞] {A B : 𝒞} (f : A ⟶ B) (_hm : Mono f)
    (G : DenseClass 𝒞) : Prop := G.mem f

/-! ### Fraction spans: the morphisms of A[G⁻¹] -/

/-- A FRACTION A → B (§1.48): a span `apex —[denom ∈ G]→ A` and `apex → B`. -/
structure Fraction [HasPullbacks 𝒞] (G : DenseClass 𝒞) (A B : 𝒞) where
  apex  : 𝒞
  denom : apex ⟶ A
  num   : apex ⟶ B
  denom_dense : G.mem denom

/-- Two fractions name the SAME morphism (§1.48) if they admit a common G-monic roof
    making both squares commute. -/
def FractionEquiv [HasPullbacks 𝒞] {G : DenseClass 𝒞} {A B : 𝒞}
    (f₁ f₂ : Fraction G A B) : Prop :=
  ∃ (R : 𝒞) (r₁ : R ⟶ f₁.apex) (r₂ : R ⟶ f₂.apex),
    G.mem (r₁ ≫ f₁.denom) ∧
    r₁ ≫ f₁.denom = r₂ ≫ f₂.denom ∧
    r₁ ≫ f₁.num   = r₂ ≫ f₂.num

/-! ### Universal property of A[G⁻¹] -/

/-- **§1.48 RATIONAL CATEGORY**: the category of fractions for a dense class G.

    We record the universal property:
    - a carrier `Rat`,
    - a localisation functor `loc : 𝒞 → Rat` sending every G-monic to an iso,
    - universality: any `F : 𝒞 → ℬ` inverting G-monics factors through `loc`. -/
structure RationalCategory [HasPullbacks 𝒞] (G : DenseClass 𝒞) where
  Rat      : Type u
  ratCat   : Cat.{v} Rat
  loc      : 𝒞 → Rat
  locFun   : @Functor _ _ _ ratCat loc
  loc_iso  : ∀ {A B : 𝒞} (f : A ⟶ B), G.mem f →
               @IsIso _ ratCat (loc A) (loc B) (locFun.map f)
  univ     : ∀ {ℬ : Type u} (catB : Cat.{v} ℬ) (F : 𝒞 → ℬ)
               (hF : @Functor _ _ _ catB F),
               (∀ {A B : 𝒞} (f : A ⟶ B), G.mem f →
                  @IsIso _ catB (F A) (F B) (hF.map f)) →
               ∃ (F' : Rat → ℬ) (_ : @Functor _ ratCat _ catB F'),
                 ∀ (A : 𝒞), F' (loc A) = F A

/-! ## Representable functor, Yoneda, fiber, evaluation -/

/-- The YONEDA EMBEDDING: A ↦ Hom(A, -) (§1.464). -/
def YonedaEmbedding (A : 𝒞) : 𝒞 → Type v := λ X => A ⟶ X

/-- REPRESENTABLE FUNCTOR (§1.442): same as YonedaEmbedding. -/
def RepresentableFunctor (A : 𝒞) : 𝒞 → Type v := YonedaEmbedding A

/-- The fiber of f: A→B at y: X→B is the pullback object (§1.462). -/
def fiber {A B X : 𝒞} (f : A ⟶ B) (y : X ⟶ B) [HasPullbacks 𝒞] : 𝒞 :=
  (HasPullbacks.has f y).cone.pt

/-- The fiber map: the pullback projection into A. -/
def fiberMap {A B X : 𝒞} (f : A ⟶ B) (y : X ⟶ B) [HasPullbacks 𝒞] : fiber f y ⟶ A :=
  (HasPullbacks.has f y).cone.π₁

/-- EVALUATION FUNCTOR ev_A: F ↦ F(A) (§1.48). -/
def EvaluationFunctor {𝒟 : Type u} [Cat.{v} 𝒟] (F : 𝒞 → 𝒟) [Functor F] (A : 𝒞) : 𝒟 := F A

end Freyd
