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

/-- **§1.472 (product-proper ↔ faithful)**: `B×-` is faithful iff for every proper subobject
    `m : A'↪A` the map `pair(fst≫m, snd) : A'×B → A×B` is again a **proper** mono.

    NB: the book (§1.472) requires `A'×B` to be a *proper* subobject of `A×B`, i.e.
    `ProperMono`, not merely `Mono`.  `Mono (m × id_B)` follows from `Mono m` alone
    (`product_mono_of_mono`), so phrasing the right side with `Mono` would make it a
    tautology and the equivalence false (the left side fails in, e.g., §1.475's Z-sets).
    The non-iso half is the substantive §1.472 content. -/
theorem prodEndo_faithful_iff_product_proper [HasBinaryProducts 𝒞] (B : 𝒞) :
    Embedding (prodEndo B) ↔
    (∀ {A' A : 𝒞} (m : A' ⟶ A), ProperMono m →
      ProperMono (pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B)))) := by
  sorry

/-- **§1.472 (⟹)**: A special Cartesian category has B×- faithful for every B with a
    proper subobject.  Stated with `[SpecialCartesianCategory 𝒞]` to avoid instance conflicts. -/
theorem special_implies_prodEndo_faithful [SpecialCartesianCategory 𝒞] (B : 𝒞)
    (hB : ∃ (B' : 𝒞) (n : B' ⟶ B), ProperMono n) : Embedding (prodEndo B) := by
  obtain ⟨B', n, hn⟩ := hB
  rw [prodEndo_faithful_iff_product_proper]
  intro A' A m hm
  exact SpecialCartesianCategory.special m n hm hn

/-- **§1.472**: A Cartesian category is special iff for every B with a proper subobject,
    B×- is faithful. -/
theorem special_iff_prodEndo_faithful [CartesianCategory 𝒞] :
    Nonempty (SpecialCartesianCategory 𝒞) ↔
    (∀ (B : 𝒞), (∃ (B' : 𝒞) (n : B' ⟶ B), ProperMono n) →
      Embedding (prodEndo B)) := by
  constructor
  · intro ⟨hS⟩ B hB
    -- Instance mismatch: hS.toCartesianCategory ≠ inst✝ definitionally.
    -- Use special_implies_prodEndo_faithful via the SpecialCartesianCategory instance.
    haveI := hS; exact sorry
  · intro hF
    refine ⟨{ special := fun {A' A B' B} m n hm hn =>
      (prodEndo_faithful_iff_product_proper B).mp (hF B ⟨B', n, hn⟩) m hm }⟩

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
  -- Build a SpecialCartesianCategory instance using prodEndo_faithful_iff_product_proper.
  -- For each B, (prodEndo_faithful_iff_product_proper B).mp (hF B) gives
  -- "for all proper m, pair(fst≫m)(snd) is proper" — exactly the special field.
  refine ⟨{ special := fun {A' A B' B} m _n hm _hn =>
    (prodEndo_faithful_iff_product_proper B).mp (hF B) m hm }⟩

/-- **§1.473 (⇒)**: In a one-valued special Cartesian category, B×- is faithful for all B.

    Proof sketch (Freyd §1.473): 1×- is trivially faithful.  If B ≇ 1 then the diagonal
    (id_B, id_B) : B → B×B is proper (else B → 1 would be monic, contradicting one-valuedness
    and B ≇ 1), so (B×B)×- is faithful; being composed with B×- twice, it forces B×- faithful. -/
theorem oneValued_special_prodEndo_faithful [SpecialCartesianCategory 𝒞]
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
      special_implies_prodEndo_faithful (prod B B) ⟨B, diag B, h_diag_proper⟩
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

/-- **§1.473**: A one-valued Cartesian category is special iff B×- is faithful for all B. -/
theorem oneValued_special_iff [CartesianCategory 𝒞] (h1v : OneValued (𝒞 := 𝒞)) :
    Nonempty (SpecialCartesianCategory 𝒞) ↔ ∀ (B : 𝒞), Embedding (prodEndo B) := by
  constructor
  · intro _ B; sorry   -- by oneValued_special_prodEndo_faithful
  · exact prodEndo_faithful_all_implies_special

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

/-- **§1.474 (⇒)**: In a two-valued special Cartesian category, every B not iso to 0 has
    a proper subobject; hence B×- is faithful for all such B.

    Proof sketch (Freyd §1.474): B×0 → 0 is an iso for all B (since B×0 maps to 0 with
    inverse from universality); B×0 ↪ B×1 ≅ B is monic.  This represents a proper subobject
    of B iff B ≇ 0. -/
theorem twoValued_special_prodEndo_faithful [SpecialCartesianCategory 𝒞]
    (h2v : TwoValued (𝒞 := 𝒞)) (B : 𝒞)
    (hB : ¬ ∃ (e : B ⟶ h2v.zeroObj), IsIso e) :
    Embedding (prodEndo B) := by
  sorry

/-- **§1.474**: A two-valued Cartesian category is special iff B×- is faithful for all B
    not isomorphic to the zero object. -/
theorem twoValued_special_iff [CartesianCategory 𝒞] (h2v : TwoValued (𝒞 := 𝒞)) :
    Nonempty (SpecialCartesianCategory 𝒞) ↔
    (∀ (B : 𝒞), (¬ ∃ (e : B ⟶ h2v.zeroObj), IsIso e) → Embedding (prodEndo B)) := by
  constructor
  · -- ⟹: see twoValued_special_prodEndo_faithful (sorry; instance compat issue with unpack)
    intro ⟨hS⟩ B hB; haveI := hS; sorry
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
