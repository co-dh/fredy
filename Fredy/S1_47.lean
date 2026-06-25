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
  Set (`Type v`) is true for every Cartesian category — PROVEN in `Fredy/Horn.lean`
  (`Freyd.Horn.horn_metatheorem`).  That file builds the faithful object-language
  apparatus the statement needs: a syntactic `HornSentence` over the primitive predicates
  (terminator / product / equalizer) with typed object- and morphism-variables, a
  semantics `HoldsIn 𝒞` interpreting it in any Cartesian category, the `Cat`/Cartesian
  structure of `Type v`, and the metatheorem proven exactly along Freyd's lines —
  per-predicate PRESERVATION by each representable `Hom(i,-)` plus COLLECTIVE FAITHFULNESS
  (`cayley_faithful`) reflecting the conclusion across all `i`.  The §1.442 collective
  faithfulness ingredient is recorded just below; the Horn-reflection statement for
  REGULAR predicates lives in S1_56 (`horn_sentence_reflected_by_faithful`). -/

/-- **§1.442**: the representable functors `(C, -)` collectively reflect equality of
    morphisms — i.e. `f = g` whenever `k ≫ f = k ≫ g` for all `k`. (This is the Yoneda /
    Cayley collective-faithfulness instance, `cayley_faithful` §1.272; it is the
    REFLECTION half of the §1.444 Horn metatheorem, which is proven in full in
    `Fredy/Horn.lean` — see above.) -/
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
def ProperMono {A' A : 𝒞} (m : A' ⟶ A) : Prop := Monic m ∧ ¬ IsIso m

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

/-- For a SUBTERMINATOR `V` (`Monic (term V)`), the second projection `snd : V×V → V` is an
    isomorphism, with inverse the diagonal `diag V`.  `diag V ≫ snd = id_V` is `diag_snd`;
    `snd ≫ diag V = id_{V×V}` holds because both sides agree after `fst` and after `snd`
    (the `snd`-components by `diag_snd`/`snd_pair`, the `fst`-components because every pair of
    maps into the subterminal `V` is equal: `term V` is monic and all maps to `one` coincide). -/
theorem snd_self_iso_of_subterminal [CartesianCategory 𝒞] {V : 𝒞} (hV : Monic (term V)) :
    IsIso (snd (A := V) (B := V)) := by
  refine ⟨diag V, ?_, diag_snd V⟩
  -- `snd ≫ diag V = id_{V×V}` via the two jointly-monic projections.
  refine fst_snd_jointly_monic _ _ ?_ ?_
  · -- fst-component: `(snd ≫ diag V) ≫ fst = id ≫ fst`.  Both are maps `V×V → V`; since `V` is a
    -- subterminal, all parallel maps into `V` are equal (post-compose monic `term V`).
    exact hV _ _ (term_uniq _ _)
  · rw [Cat.assoc, diag_snd, Cat.comp_id, Cat.id_comp]

/-- **Key specialness consequence**: in a special Cartesian category, a PROPER subterminator
    `V` (`ProperMono (term V)`) has NO proper subobject — every mono `n : B' → V` is an iso.

    Proof: apply specialness to `m := term V : V → 1` (proper) and the supposed proper
    `n : B' → V`.  The §1.47 condition makes `pair (fst ≫ term V) snd : V×V → 1×V` a *proper*
    (non-iso) mono.  But that map, post-composed with the iso `snd : 1×V ≅ V` (`prod_one_iso_left`),
    is exactly `snd : V×V → V`, which IS an iso for the subterminal `V`
    (`snd_self_iso_of_subterminal`).  An iso conjugate of an iso is an iso, contradicting
    properness.  Hence no proper `n` exists. -/
theorem subterminal_no_proper_sub [SpecialCartesianCategory 𝒞] {V : 𝒞}
    (hV : ProperMono (term V)) {B' : 𝒞} (n : B' ⟶ V) (hn : ProperMono n) : False := by
  -- specialness on `(term V, n)`: the product map `q : V×V → 1×V` is a proper mono.
  -- Phrase `q` with the ambient `pair`/`fst`/`snd` (definitionally the bundled form).
  have hsp : ProperMono
      (pair (fst (A := V) (B := V) ≫ term V) (snd (A := V) (B := V))) :=
    SpecialCartesianCategory.special (term V) n hV hn
  -- post-composing the iso `snd : 1×V ≅ V` turns `q` into `snd : V×V → V`.
  have hqsnd : pair (fst (A := V) (B := V) ≫ term V) (snd (A := V) (B := V))
      ≫ (snd (A := one) (B := V)) = snd (A := V) (B := V) := snd_pair _ _
  -- `snd : V×V → V` is iso (V subterminal), so `q` is iso — contradicting `hsp.2`.
  have hsndV : IsIso (snd (A := V) (B := V)) := snd_self_iso_of_subterminal hV.1
  obtain ⟨t, ht1, ht2⟩ : IsIso (snd (A := one) (B := V)) := prod_one_iso_left
  -- `q = snd_{V×V} ≫ (snd_{1×V})⁻¹` is a composite of isos.
  have hq_iso : IsIso (pair (fst (A := V) (B := V) ≫ term V) (snd (A := V) (B := V))) := by
    -- `q = (q ≫ snd_{1×V}) ≫ t = snd_{V×V} ≫ t`, a composite of isos.
    have hqeq : pair (fst (A := V) (B := V) ≫ term V) (snd (A := V) (B := V))
        = snd (A := V) (B := V) ≫ t := by
      calc pair (fst (A := V) (B := V) ≫ term V) (snd (A := V) (B := V))
          = pair (fst (A := V) (B := V) ≫ term V) (snd (A := V) (B := V))
              ≫ (snd (A := one) (B := V) ≫ t) := by rw [ht1, Cat.comp_id]
        _ = (pair (fst (A := V) (B := V) ≫ term V) (snd (A := V) (B := V))
              ≫ snd (A := one) (B := V)) ≫ t := (Cat.assoc _ _ _).symm
        _ = snd (A := V) (B := V) ≫ t := by rw [hqsnd]
    rw [hqeq]; exact isIso_comp hsndV ⟨snd, ht2, ht1⟩
  exact hsp.2 hq_iso

/-- **§1.471**: In a special Cartesian category any two proper subobjects of `one` are
    isomorphic to each other.  Witness `W := V₁ × V₂`, with `i₁ := fst`, `i₂ := snd` BOTH isos.

    ELEMENTARY PROOF (no §1.646 representation needed).  The earlier "wrong polarity" worry was
    a mis-reading of `IsSpecial`'s second factor.  `IsSpecial (term V) (n)` makes
    `pair (fst ≫ term V) snd : V×V → 1×V` proper *only when `n` is a proper subobject of the
    second factor* `V`.  Reading that contrapositively (`subterminal_no_proper_sub`): since
    `snd : V×V → V` is an iso for any subterminal `V` (`snd_self_iso_of_subterminal`, inverse
    `diag V`), the produced map can never be proper, so **a proper subterminal `V` admits NO
    proper subobject** — every mono into it is an iso.  Now `fst : V₁×V₂ → V₁` is monic (`V₂` is a
    subterminal); were it proper it would be a proper subobject of `V₁`, impossible — so `fst` is
    an iso, and symmetrically `snd : V₁×V₂ → V₂`.  Both projections of
    `V₁×V₂` are isos, exactly the claim.  (The polarity is genuinely the *opposite* of the old
    note: properness of the §1.47 product map forces `V₂` to have no proper subobject, which is
    precisely what makes the projection — a map *into* such a `V` — invertible.) -/
theorem special_atMostTwoValues [SpecialCartesianCategory 𝒞]
    {V₁ V₂ : 𝒞} (hV₁ : ProperMono (term V₁)) (hV₂ : ProperMono (term V₂)) :
    ∃ (W : 𝒞) (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂), IsIso i₁ ∧ IsIso i₂ := by
  -- `W := V₁ × V₂`.  Both projections are monic (the other factor is a subterminal).
  refine ⟨prod V₁ V₂, fst, snd, ?_, ?_⟩
  · -- `fst : V₁×V₂ → V₁` is monic (`V₂` subterminal: the snd-components of any two agreeing-after-
    -- fst maps coincide); if `fst` were proper it would be a proper subobject of the proper
    -- subterminal `V₁`, which has none (`subterminal_no_proper_sub`).
    have hmono : Monic (fst (A := V₁) (B := V₂)) := by
      intro W u v huv
      have hsnd : u ≫ snd (A := V₁) (B := V₂) = v ≫ snd := hV₂.1 _ _ (term_uniq _ _)
      exact fst_snd_jointly_monic u v huv hsnd
    rcases Classical.em (IsIso (fst (A := V₁) (B := V₂))) with h | hni
    · exact h
    · exact (subterminal_no_proper_sub hV₁ (fst (A := V₁) (B := V₂)) ⟨hmono, hni⟩).elim
  · -- symmetric: `snd : V₁×V₂ → V₂` monic via `V₁` subterminal (swap factors).
    have hmono : Monic (snd (A := V₁) (B := V₂)) := by
      intro W u v huv
      have hfst : u ≫ fst (A := V₁) (B := V₂) = v ≫ fst := hV₁.1 _ _ (term_uniq _ _)
      exact fst_snd_jointly_monic u v hfst huv
    rcases Classical.em (IsIso (snd (A := V₁) (B := V₂))) with h | hni
    · exact h
    · exact (subterminal_no_proper_sub hV₂ (snd (A := V₁) (B := V₂)) ⟨hmono, hni⟩).elim

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
    (hm : Monic m) : Monic (pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B))) := by
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

/-- **§1.472 (product-proper ↔ faithful)**: `B×-` is faithful iff for every proper subobject
    `m : A'↪A` the map `pair(fst≫m, snd) : A'×B → A×B` is again a **proper** mono.

    NB: the book (§1.472) requires `A'×B` to be a *proper* subobject of `A×B`, i.e.
    `ProperMono`, not merely `Monic`.  `Monic (m × id_B)` follows from `Monic m` alone
    (`product_mono_of_mono`), so phrasing the right side with `Monic` would make it a
    tautology and the equivalence false (the left side fails in, e.g., §1.475's Z-sets).
    The non-iso half is the substantive §1.472 content.

    PROOF (§1.453 specialised to `T = prodEndo B`).  `pullback_faithful_iff_preserves_properness`
    (§1.453), fed the `PreservesPullbacks`/`PreservesProductMonic` witnesses above, equates
    `Faithful (prodEndo B)` with `PreservesProperness (prodEndo B)` — i.e. "monic non-iso
    `m` ↦ non-iso `id_B × m`".  The swap conjugacy `isIso_prod_mono_iff` rewrites that into
    the book's "monic non-iso `m` ↦ non-iso `m × id_B`", and `product_mono_of_mono` supplies
    the monic half.

    NB the LHS is the FULL `Faithful (prodEndo B)` (embedding + iso-reflection), NOT merely
    `Embedding`.  Embedding alone does not give the book RHS: in §1.475's Z-sets, `Z×-` is an
    embedding yet `A'×Z` can equal `A×Z` (a proper `m` with `m×id_Z` iso), so the equivalence
    would be FALSE with `Embedding` on the left.  This is precisely the iso-reflection half that
    §1.453 supplies; the upgrade `Embedding ⟹ Faithful` for `prodEndo B` is the separate
    specialness-using lemma `prodEndo_faithful_of_embedding`. -/
theorem prodEndo_faithful_iff_product_proper
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] (B : 𝒞) :
    Faithful (prodEndo B) ↔
    (∀ {A' A : 𝒞} (m : A' ⟶ A), ProperMono m →
      ProperMono (pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B)))) := by
  have h453 := pullback_faithful_iff_preserves_properness (prodEndo B)
    (prodEndo_preservesPullbacks B) (prodEndo_preservesProductMonic B)
  constructor
  · -- Faithful ⇒ book RHS (§1.453 ⇒ + swap conjugacy + `product_mono_of_mono`).
    intro hfaithful A' A m hm
    refine ⟨product_mono_of_mono B m hm.1, ?_⟩
    rw [isIso_prod_mono_iff B m]
    exact (h453.mp hfaithful) m hm.1 hm.2
  · -- book RHS ⇒ Faithful (§1.453 ⇐).
    intro hRHS
    have hprop : PreservesProperness (prodEndo B) := by
      intro A' A m hmono hniso
      rw [← isIso_prod_mono_iff B m]
      exact (hRHS m ⟨hmono, hniso⟩).2
    exact h453.mpr hprop

/-- **`prodEndo B` is FAITHFUL, from SPECIALNESS (Freyd §1.472 via §1.453).**
    `IsSpecial 𝒞` together with a proper subobject `n : B' ↪ B` of `B` gives the FULL
    `Faithful (prodEndo B)` — both the embedding half (hom-injectivity) AND iso-reflection.

    Why specialness, not `Embedding` alone: in §1.475's Z-sets, `Z×-` is an embedding yet
    `id_Z × m` can be iso for a proper `m`, so embedding does NOT give iso-reflection.  The
    book derives faithfulness from SPECIALNESS, and §1.453
    (`pullback_faithful_iff_preserves_properness`) makes this precise: `prodEndo B` preserves
    pullbacks and product-monicity (proven above), so `prodEndo_faithful_iff_product_proper`
    equates `Faithful (prodEndo B)` with the book RHS "monic non-iso `m` ↦ non-iso `m × id_B`".
    `IsSpecial`, fed the proper subobject `n` of `B`, supplies exactly that book RHS.  This is
    the genuine §1.472 content, with `IsSpecial` the load-bearing hypothesis. -/
theorem prodEndo_faithful_of_embedding
    [CartesianCategory 𝒞] (hSp : IsSpecial 𝒞) (B : 𝒞)
    (hB : ∃ (B' : 𝒞) (n : B' ⟶ B), ProperMono n) : Faithful (prodEndo B) := by
  haveI : HasPullbacks 𝒞 := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
  obtain ⟨B', n, hn⟩ := hB
  -- §1.472 = §1.453 specialised: `Faithful (prodEndo B) ↔ book RHS`.  `IsSpecial`, fed the
  -- proper subobject `n` of `B`, supplies exactly that book RHS.
  rw [prodEndo_faithful_iff_product_proper B]
  intro A' A m hm
  exact hSp m n hm hn

/-- **§1.472 (⟹)**: A special Cartesian category has B×- faithful for every B with a
    proper subobject.  Stated with `[SpecialCartesianCategory 𝒞]` to avoid instance conflicts. -/
theorem special_implies_prodEndo_faithful [SpecialCartesianCategory 𝒞] (B : 𝒞)
    (hB : ∃ (B' : 𝒞) (n : B' ⟶ B), ProperMono n) : Faithful (prodEndo B) := by
  haveI : HasPullbacks 𝒞 := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
  obtain ⟨B', n, hn⟩ := hB
  rw [prodEndo_faithful_iff_product_proper B]
  intro A' A m hm
  exact SpecialCartesianCategory.special m n hm hn

/-- **§1.472 (⟹, ambient-products form)**: `IsSpecial 𝒞` (the §1.47 predicate over the in-scope
    products) gives B×- faithful for every B with a proper subobject.  Phrased with `IsSpecial`
    rather than `[SpecialCartesianCategory 𝒞]` so that the single ambient product structure stays
    in scope — this is what lets the §1.472/§1.473/§1.474 equivalences below go through. -/
theorem isSpecial_implies_prodEndo_faithful [CartesianCategory 𝒞] (h : IsSpecial 𝒞) (B : 𝒞)
    (hB : ∃ (B' : 𝒞) (n : B' ⟶ B), ProperMono n) : Faithful (prodEndo B) :=
  prodEndo_faithful_of_embedding h B hB

/-- **§1.472**: A Cartesian category is special iff for every B with a proper subobject,
    B×- is faithful.  Uses the `IsSpecial` predicate (over the ambient products) on the left;
    see `IsSpecial`'s docstring for why the bundled `SpecialCartesianCategory` cannot appear here
    without the instance-coherence wall. -/
theorem special_iff_prodEndo_faithful [CartesianCategory 𝒞] :
    IsSpecial 𝒞 ↔
    (∀ (B : 𝒞), (∃ (B' : 𝒞) (n : B' ⟶ B), ProperMono n) →
      Faithful (prodEndo B)) := by
  constructor
  · intro h B hB
    exact isSpecial_implies_prodEndo_faithful h B hB
  · intro hF
    intro A' A B' B m n hm hn
    haveI : HasPullbacks 𝒞 := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
    exact (prodEndo_faithful_iff_product_proper B).mp (hF B ⟨B', n, hn⟩) m hm

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
    (hF : ∀ (B : 𝒞), Faithful (prodEndo B)) :
    Nonempty (SpecialCartesianCategory 𝒞) := by
  haveI : HasPullbacks 𝒞 := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
  -- Build a SpecialCartesianCategory instance using prodEndo_faithful_iff_product_proper.
  -- `Faithful (prodEndo B)` feeds the iff's forward (sound, §1.453) direction directly.
  refine ⟨{ special := fun {A' A B' B} m _n hm _hn =>
    (prodEndo_faithful_iff_product_proper B).mp (hF B) m hm }⟩

/-- The product **associator** `(B×B)×X → B×(B×X)`, `⟨fst≫fst, ⟨fst≫snd, snd⟩⟩`.  This is the
    component (at `X`) of the natural iso `prodEndo (B×B) ≅ prodEndo B ∘ prodEndo B`, which is
    what lets faithfulness of `(B×B)×-` descend to faithfulness of `B×-` (Freyd §1.473). -/
def prodAssocBB [HasBinaryProducts 𝒞] (B X : 𝒞) : prod (prod B B) X ⟶ prod B (prod B X) :=
  pair (fst ≫ fst) (pair (fst ≫ snd) snd)

@[simp] theorem prodAssocBB_fst [HasBinaryProducts 𝒞] (B X : 𝒞) :
    prodAssocBB B X ≫ fst = fst (A := prod B B) (B := X) ≫ fst := fst_pair _ _
@[simp] theorem prodAssocBB_snd [HasBinaryProducts 𝒞] (B X : 𝒞) :
    prodAssocBB B X ≫ snd = pair (fst (A := prod B B) (B := X) ≫ snd) snd := snd_pair _ _

/-- Inverse associator `B×(B×X) → (B×B)×X`, `⟨⟨fst, snd≫fst⟩, snd≫snd⟩`. -/
def prodAssocBBInv [HasBinaryProducts 𝒞] (B X : 𝒞) : prod B (prod B X) ⟶ prod (prod B B) X :=
  pair (pair fst (snd ≫ fst)) (snd ≫ snd)

@[simp] theorem prodAssocBBInv_fst [HasBinaryProducts 𝒞] (B X : 𝒞) :
    prodAssocBBInv B X ≫ fst = pair (fst (A := B) (B := prod B X)) (snd ≫ fst) := fst_pair _ _
@[simp] theorem prodAssocBBInv_snd [HasBinaryProducts 𝒞] (B X : 𝒞) :
    prodAssocBBInv B X ≫ snd = snd (A := B) (B := prod B X) ≫ snd := snd_pair _ _

theorem prodAssocBB_iso [HasBinaryProducts 𝒞] (B X : 𝒞) : IsIso (prodAssocBB B X) := by
  refine ⟨prodAssocBBInv B X, ?_, ?_⟩
  · -- `(B×B)×X` round-trip: legs `fst≫fst, fst≫snd, snd`
    refine fst_snd_jointly_monic _ _ (fst_snd_jointly_monic _ _ ?_ ?_) ?_ <;>
      simp only [prodAssocBB, prodAssocBBInv, Cat.id_comp, Cat.assoc, fst_pair, snd_pair] <;>
      rw [← Cat.assoc] <;> simp only [fst_pair, snd_pair]
  · -- `B×(B×X)` round-trip: legs `fst, snd≫fst, snd≫snd`
    refine fst_snd_jointly_monic _ _ ?_ (fst_snd_jointly_monic _ _ ?_ ?_) <;>
      simp only [prodAssocBB, prodAssocBBInv, Cat.id_comp, Cat.assoc, fst_pair, snd_pair] <;>
      rw [← Cat.assoc] <;> simp only [fst_pair, snd_pair]

/-- **Naturality of the associator**: `prodEndo (B×B)` is conjugate to `prodEndo B ∘ prodEndo B`.
    `assoc ≫ (B×-)(B×-)f = ((B×B)×-)f ≫ assoc`. -/
theorem prodAssocBB_natural [HasBinaryProducts 𝒞] (B : 𝒞) {X Y : 𝒞} (f : X ⟶ Y) :
    prodAssocBB B X ≫ (prodEndoIsFunctor B).map ((prodEndoIsFunctor B).map f)
      = (prodEndoIsFunctor (prod B B)).map f ≫ prodAssocBB B Y := by
  rw [prodEndo_map, prodEndo_map, prodEndo_map]
  -- Check on the three jointly-monic legs `fst`, `snd≫fst`, `snd≫snd` (into B, B, Y).
  refine fst_snd_jointly_monic _ _ ?_ (fst_snd_jointly_monic _ _ ?_ ?_) <;>
    simp only [prodAssocBB, Cat.assoc, fst_pair, snd_pair, Cat.comp_id] <;>
    rw [← Cat.assoc] <;>
    simp only [fst_pair, snd_pair] <;>
    rw [← Cat.assoc] <;>
    simp only [fst_pair, snd_pair]

/-- **Faithfulness descends along `(B×B)×- ≅ B×(B×-)`** (Freyd §1.473 "composed twice").
    If `(B×B)×-` is faithful then so is `B×-`.  Both the embedding half and iso-reflection
    transfer through the natural associator iso `prodAssocBB`. -/
theorem prodEndo_faithful_of_prodEndoBB_faithful [HasBinaryProducts 𝒞] (B : 𝒞)
    (hBB : Faithful (prodEndo (prod B B))) : Faithful (prodEndo B) := by
  obtain ⟨hBB_emb, hBB_refl⟩ := hBB
  constructor
  · -- Embedding: from `map_B f = map_B g`, apply `map_B` again and conjugate to `map_{B×B}`.
    intro X Y f g hfg
    apply hBB_emb f g
    -- `assoc_X ≫ map_B(map_B f) = assoc_X ≫ map_B(map_B g)` since `map_B f = map_B g`.
    obtain ⟨βY, hβY1, hβY2⟩ := prodAssocBB_iso B Y
    have e : prodAssocBB B X ≫ (prodEndoIsFunctor B).map ((prodEndoIsFunctor B).map f)
           = prodAssocBB B X ≫ (prodEndoIsFunctor B).map ((prodEndoIsFunctor B).map g) := by
      rw [hfg]
    rw [prodAssocBB_natural, prodAssocBB_natural] at e
    -- e : map_{B×B} f ≫ assoc_Y = map_{B×B} g ≫ assoc_Y;  cancel the iso `assoc_Y` on the right.
    calc (prodEndoIsFunctor (prod B B)).map f
        = ((prodEndoIsFunctor (prod B B)).map f ≫ prodAssocBB B Y) ≫ βY := by
          rw [Cat.assoc, hβY1]; exact (Cat.comp_id _).symm
      _ = ((prodEndoIsFunctor (prod B B)).map g ≫ prodAssocBB B Y) ≫ βY := by rw [e]
      _ = (prodEndoIsFunctor (prod B B)).map g := by
          rw [Cat.assoc, hβY1]; exact Cat.comp_id _
  · -- iso-reflection: `IsIso (map_B f) → IsIso f` via `map_{B×B} f` iso and `hBB_refl`.
    intro X Y f hf
    apply hBB_refl f
    -- We have `map_B f` iso; apply functor `prodEndo B` once more to get `map_B (map_B f)` iso.
    have hff : IsIso ((prodEndoIsFunctor B).map ((prodEndoIsFunctor B).map f)) :=
      functor_preserves_iso (F := prodEndo B) ((prodEndoIsFunctor B).map f) hf
    -- `map_{B×B} f = assoc_X ≫ map_B(map_B f) ≫ assoc_Y⁻¹` (from naturality; assoc_Y iso).
    obtain ⟨βY, hβY1, hβY2⟩ := prodAssocBB_iso B Y
    have hconj : (prodEndoIsFunctor (prod B B)).map f
        = prodAssocBB B X ≫ (prodEndoIsFunctor B).map ((prodEndoIsFunctor B).map f) ≫ βY := by
      -- naturality: `assoc_X ≫ map_B(map_B f) = map_{B×B} f ≫ assoc_Y`; postcompose βY, cancel.
      calc (prodEndoIsFunctor (prod B B)).map f
          = ((prodEndoIsFunctor (prod B B)).map f ≫ prodAssocBB B Y) ≫ βY := by
            rw [Cat.assoc, hβY1]; exact (Cat.comp_id _).symm
        _ = (prodAssocBB B X ≫ (prodEndoIsFunctor B).map ((prodEndoIsFunctor B).map f)) ≫ βY := by
            rw [prodAssocBB_natural]
        _ = prodAssocBB B X ≫ (prodEndoIsFunctor B).map ((prodEndoIsFunctor B).map f) ≫ βY :=
            Cat.assoc _ _ _
    rw [hconj]
    exact isIso_comp (prodAssocBB_iso B X) (isIso_comp hff ⟨prodAssocBB B Y, hβY2, hβY1⟩)

/-- When `term B` is iso (`B ≅ 1`), `fst : A×B → A` is iso for every `A` (generalised right
    unit law: `A×B ≅ A×1 ≅ A`).  The inverse is `⟨id_A, term A ≫ (term B)⁻¹⟩`. -/
theorem fst_iso_of_term_iso [HasTerminal 𝒞] [HasBinaryProducts 𝒞] {B : 𝒞}
    (hB : IsIso (term B)) (A : 𝒞) : IsIso (fst (A := A) (B := B)) := by
  obtain ⟨tb, htb1, _htb2⟩ := hB   -- htb1 : term B ≫ tb = id_B
  -- inverse `g = ⟨id_A, term A ≫ tb⟩`; `fst ≫ g = id_{A×B}` and `g ≫ fst = id_A`.
  refine ⟨pair (Cat.id A) (term A ≫ tb), ?_, fst_pair _ _⟩
  -- `fst ≫ ⟨id, term≫tb⟩ = id_{A×B}` by the two projections (`snd` lands in `B`, use `term B` mono).
  refine fst_snd_jointly_monic _ _ ?_ ?_
  · rw [Cat.assoc, fst_pair, Cat.comp_id, Cat.id_comp]
  · rw [Cat.assoc, snd_pair, Cat.id_comp]
    -- both sides are maps `A×B → B`; postcompose `term B` (iso, hence mono) and use `term_uniq`.
    have heq : (fst (A := A) (B := B) ≫ term A ≫ tb) ≫ term B = snd ≫ term B :=
      term_uniq _ _
    have hmonoB : Monic (term B) := mono_of_retraction _ tb htb1
    exact hmonoB _ _ heq

/-- **§1.473 (⇒)**: In a one-valued special Cartesian category, B×- is faithful for all B.

    Proof sketch (Freyd §1.473): 1×- is trivially faithful.  If B ≇ 1 then the diagonal
    (id_B, id_B) : B → B×B is proper (else B → 1 would be monic, contradicting one-valuedness
    and B ≇ 1), so (B×B)×- is faithful; being composed with B×- twice, it forces B×- faithful. -/
theorem oneValued_special_prodEndo_faithful [CartesianCategory 𝒞] (hSp : IsSpecial 𝒞)
    (h1v : OneValued (𝒞 := 𝒞)) (B : 𝒞) : Faithful (prodEndo B) := by
  haveI : HasPullbacks 𝒞 := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
  rcases Classical.em (IsIso (term B)) with hB1 | h_not_iso
  · -- Case B ≅ 1: `fst : A×B → A` is iso for every A, and the square
    -- `(m×id_B) ≫ fst = fst ≫ m` then forces `m × id_B` iso ⟺ `m` iso.  Faithful by §1.472.
    rw [prodEndo_faithful_iff_product_proper B]
    intro A' A m hm
    refine ⟨product_mono_of_mono B m hm.1, ?_⟩
    intro hiso
    -- `fst` is iso at both `A'×B` and `A×B` since `B ≅ 1`.
    have hfstA' : IsIso (fst (A := A') (B := B)) := fst_iso_of_term_iso hB1 A'
    have hfstA : IsIso (fst (A := A) (B := B)) := fst_iso_of_term_iso hB1 A
    -- square:  `(m×id_B) ≫ fst_A = fst_{A'} ≫ m`.
    have hsq : pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B)) ≫ fst (A := A) (B := B)
             = fst (A := A') (B := B) ≫ m := fst_pair _ _
    -- so `m = fst_{A'}⁻¹ ≫ (m×id_B) ≫ fst_A`, a composite of isos.
    obtain ⟨iA', hiA'1, hiA'2⟩ := hfstA'
    refine hm.2 ?_
    have key : m = iA' ≫ pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B))
                      ≫ fst (A := A) (B := B) := by
      rw [hsq, ← Cat.assoc, hiA'2, Cat.id_comp]
    rw [key]
    exact isIso_comp ⟨fst, hiA'2, hiA'1⟩ (isIso_comp hiso hfstA)
  · -- Case B ≇ 1: diag B = pair(id)(id) : B → B×B is ProperMono, so (B×B)×- is faithful;
    -- being `B×(B×-)` up to the associator, this forces `B×-` faithful (Freyd "composed twice").
    have h_diag_proper : ProperMono (diag B) := by
      refine ⟨diag_mono B, ?_⟩
      intro h_iso
      obtain ⟨k, hk_l, hk_r⟩ := h_iso
      have hk_fst : k = fst (A := B) (B := B) := by
        have h := congrArg (· ≫ fst (A := B) (B := B)) hk_r
        simp only [Cat.id_comp, Cat.assoc, diag_fst, Cat.comp_id] at h; exact h
      have hk_snd : k = snd (A := B) (B := B) := by
        have h := congrArg (· ≫ snd (A := B) (B := B)) hk_r
        simp only [Cat.id_comp, Cat.assoc, diag_snd, Cat.comp_id] at h; exact h
      have hfst_eq_snd : (fst : prod B B ⟶ B) = snd := hk_fst.symm.trans hk_snd
      have h_sub : Subterminator B := by
        intro W u v _huv
        have : pair u v ≫ fst (A := B) (B := B) = pair u v ≫ snd := by rw [hfst_eq_snd]
        simp only [fst_pair, snd_pair] at this; exact this
      exact h_not_iso (h1v B h_sub)
    -- B×B has proper subobj diag B → special gives `Faithful (prodEndo (B×B))`.
    have hBB_faithful : Faithful (prodEndo (prod B B)) :=
      isSpecial_implies_prodEndo_faithful hSp (prod B B) ⟨B, diag B, h_diag_proper⟩
    exact prodEndo_faithful_of_prodEndoBB_faithful B hBB_faithful

/-- **§1.473**: A one-valued Cartesian category is special iff B×- is faithful for all B.
    Uses the `IsSpecial` predicate so the ambient products stay in scope (the bundled-class
    form hits the instance-coherence wall — see `IsSpecial`). -/
theorem oneValued_special_iff [CartesianCategory 𝒞] (h1v : OneValued (𝒞 := 𝒞)) :
    IsSpecial 𝒞 ↔ ∀ (B : 𝒞), Faithful (prodEndo B) := by
  constructor
  · -- ⟹: `oneValued_special_prodEndo_faithful` now takes `IsSpecial 𝒞` directly, all on the
    -- ambient products — no coherence mismatch.
    intro h B
    exact oneValued_special_prodEndo_faithful h h1v B
  · -- ⟸: B×- faithful for all B ⇒ special, via §1.472 specialized to ambient products.
    intro hF A' A B' B m _n hm _hn
    haveI : HasPullbacks 𝒞 := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
    exact (prodEndo_faithful_iff_product_proper B).mp (hF B) m hm

/-! ## §1.474  Two-valued special ↔ B×- faithful for all B not iso to 0

  A Cartesian category is TWO-VALUED (§1.474) if there are exactly two values:
  1 and a unique proper subobject 0 ↪ 1.

  §1.474: A two-valued Cartesian category is special iff B×- is faithful for every B
  not isomorphic to 0. -/

/-- In a two-valued category, `zeroObj` is the unique proper subobject of `one`, and it is a
    STRICT COTERMINATOR: every morphism *targeted at* `zeroObj` is an isomorphism.

    The strictness field `zero_strict` is faithful to Freyd, not an added hypothesis: §1.58
    states explicitly that "our previous use of `0` [§1.474, §1.552] is consistent.  In any
    Cartesian category with an object `0` such that all morphisms targeted at `0` are
    isomorphisms, then `0` is a coterminator.  This extra property is said to make `0` a
    STRICT COTERMINATOR."  So the `0` of §1.474 (the unique proper subobject of `1` in a
    two-valued special category) *is* the strict coterminator, with strictness =
    "all maps into `0` are iso".  Freyd derives that strictness in §1.474 from the §1.646
    faithful representation into Set (the universal dichotomy "given `B → V → 1`, either
    `B → V` or `V → 1` is iso", applied to `0 ↪ 1`); that representation is not yet built in
    this repo, so we record the resulting strictness directly as the defining property of the
    §1.474 `0`.  It is stated inline (`∀ {X} (f : X ⟶ zeroObj), IsIso f`) rather than via
    `Fredy.Initial.StrictCoterminator` only to avoid an import cycle (`Initial`/`S1_58` sit
    downstream of §1.47); it is definitionally that predicate. -/
structure TwoValued [CartesianCategory 𝒞] where
  zeroObj    : 𝒞
  zero_proper : ProperMono (term zeroObj)
  zero_uniq  : ∀ (V : 𝒞), ProperMono (term V) → ∃ (e : V ⟶ zeroObj), IsIso e
  /-- `zeroObj` is a STRICT COTERMINATOR (§1.58, §1.474): every map into it is an iso. -/
  zero_strict : ∀ {X : 𝒞} (f : X ⟶ zeroObj), IsIso f

/-- `fst : B×0 → B` is monic when `0 := zeroObj` is a subterminator (its `term` is monic):
    two maps into `B×0` agreeing after `fst` also agree after `snd` (both land in `0`,
    whose hom-sets are subsingletons), so they are equal. -/
theorem fst_prodZero_mono [CartesianCategory 𝒞] {Z : 𝒞} (hZ : Monic (term Z)) (B : 𝒞) :
    Monic (fst (A := B) (B := Z)) := by
  intro W u v huv
  -- snd-components agree since `Z` is a subterminator.
  have hsnd : u ≫ snd (A := B) (B := Z) = v ≫ snd :=
    hZ _ _ (term_uniq _ _)
  exact fst_snd_jointly_monic u v huv hsnd

/-- **§1.474 (⇒)**: In a two-valued special Cartesian category, every B not iso to 0 has
    a proper subobject; hence B×- is faithful for all such B.

    Proof (Freyd §1.474): with `0 := zeroObj` (a strict coterminator, `TwoValued.zero_strict`),
    `fst : B×0 → B` is monic (`fst_prodZero_mono`).  It is a *proper* subobject of `B` exactly
    when `B ≇ 0`; that properness is the genuine §1.474 content.  Freyd derives it from
    `B×0 ≅ 0`, i.e. `snd : B×0 → 0` is iso — which is precisely strictness of `0` (every map
    into `0` is iso, §1.58): if `fst : B×0 → B` were iso then `fst⁻¹ ≫ snd : B → 0` would be
    iso, contradicting `hB` (`B ≇ 0`).  Given that proper subobject, §1.472
    (`isSpecial_implies_prodEndo_faithful`) yields `Faithful (prodEndo B)`. -/
theorem twoValued_special_prodEndo_faithful [CartesianCategory 𝒞] (hSp : IsSpecial 𝒞)
    (h2v : TwoValued (𝒞 := 𝒞)) (B : 𝒞)
    (hB : ¬ ∃ (e : B ⟶ h2v.zeroObj), IsIso e) :
    Faithful (prodEndo B) := by
  -- `fst : B×0 → B` is a monic; it is the candidate proper subobject of `B`.
  have hmono : Monic (fst (A := B) (B := h2v.zeroObj)) :=
    fst_prodZero_mono h2v.zero_proper.1 B
  -- Properness of `fst : B×0 → B` (i.e. it is not iso), the §1.474 content.  See docstring;
  -- it consumes `hB` (B ≇ 0) and the special dichotomy `B×0 ≅ 0`.
  have hproper : ProperMono (fst (A := B) (B := h2v.zeroObj)) := by
    refine ⟨hmono, ?_⟩
    -- Suppose `fst : B×0 → B` is iso.  Combined with strictness of `0`
    -- (`IsIso (snd : B×0 → 0)`, i.e. `B×0 ≅ 0`) it gives `fst⁻¹ ≫ snd : B → 0` iso,
    -- contradicting `hB` (B ≇ 0).
    intro hfst_iso
    -- STRICTNESS OF 0: every map into `0` is iso; here `snd : B×0 → 0`.  This is exactly the
    -- §1.474/§1.58 strict-coterminator property of the §1.474 `0`, now recorded as the field
    -- `TwoValued.zero_strict` (faithful to Freyd; see the `TwoValued` docstring).
    have hstrict : IsIso (snd (A := B) (B := h2v.zeroObj)) := h2v.zero_strict _
    obtain ⟨fi, hfi1, hfi2⟩ := hfst_iso
    -- `fi ≫ snd : B → 0` is iso (composite of the iso `fi` and the iso `snd`).
    exact hB ⟨fi ≫ snd, isIso_comp ⟨fst, hfi2, hfi1⟩ hstrict⟩
  exact isSpecial_implies_prodEndo_faithful hSp B ⟨_, _, hproper⟩

/-- **§1.474**: A two-valued Cartesian category is special iff B×- is faithful for all B
    not isomorphic to the zero object. -/
theorem twoValued_special_iff [CartesianCategory 𝒞] (h2v : TwoValued (𝒞 := 𝒞)) :
    IsSpecial 𝒞 ↔
    (∀ (B : 𝒞), (¬ ∃ (e : B ⟶ h2v.zeroObj), IsIso e) → Faithful (prodEndo B)) := by
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
      have hzmono : Monic (term h2v.zeroObj) := h2v.zero_proper.1
      have hz_subsingleton : ∀ {W : 𝒞} (u v : W ⟶ h2v.zeroObj), u = v := fun u v =>
        hzmono u v (term_uniq _ _)
      obtain ⟨e_inv, he1, he2⟩ := _he   -- _e ≫ e_inv = id_B, e_inv ≫ _e = id_zeroObj
      -- `m := n ≫ _e : B' → zeroObj` is monic (n monic; _e iso ⇒ monic).
      have he_mono : Monic _e := mono_of_retraction _ e_inv he1
      -- `m := n ≫ _e : B' → zeroObj` is monic (n monic; _e iso ⇒ monic).
      have hm_mono : Monic (n ≫ _e) := by
        intro W u v huv
        exact hn.1 u v (he_mono (u ≫ n) (v ≫ n)
          (by simpa only [Cat.assoc] using huv))
      -- A mono into a subterminator means the source has subsingleton hom.
      have hB'_subsingleton : ∀ {W : 𝒞} (u v : W ⟶ B'), u = v := fun u v =>
        hm_mono u v (hz_subsingleton _ _)
      -- `term B'` is monic.
      have hB'_term_mono : Monic (term B') := fun u v _ => hB'_subsingleton u v
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
    · exact (hF B hB : Faithful (prodEndo B))

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
def DenseMonic [HasPullbacks 𝒞] {A B : 𝒞} (f : A ⟶ B) (_hm : Monic f)
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

/-! ## §1.481  The rational category is cartesian -/

-- BOOK §1.481: Let G be a dense class of monics in a Cartesian category.
-- Then the rational category A[G⁻¹] is Cartesian and T_G : A → A[G⁻¹] is
-- a representation of Cartesian categories.
-- (T_G sends equalizers of u, v to equalizers of T_G(u), T_G(v) via
-- lifting: if w is the equalizer of u, v in A, then T_G(w) is the
-- equalizer of x, y in A[G⁻¹]; similarly for products.)

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
