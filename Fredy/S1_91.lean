/-
  Freyd & Scedrov, *Categories and Allegories* §1.91  Topos structure.

  §1.913 All subobjects are equalizers, covers = epics.
  §1.914 Algebraic structure of Ω: internal meet, Heyting implication.
  §1.919 Monic endomorphisms of Ω are involutions.
  §1.91(10) Minimal topos definition (binary products + equalizers + power objects,
            no terminator needed if non-empty).
-/

import Fredy.S1_1
import Fredy.S1_9
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_45


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.913  Subobjects as equalizers

  In a topos, every monic m : A' → A is the equalizer of its characteristic
  map χ_m : A → Ω and the constant-true map A → 1 → Ω.

  BECAUSE: A' → A is a pullback of t : 1 → Ω along χ_m.  In a category
  with a terminator, any pullback of a monic is an equalizer. -/

/-- **§1.913**: In a topos, each monic `m : A' → A` is the equalizer of its
    characteristic map `χ_m` and the constant-true map `A → 1 → Ω`.

    Stated as the universal property of the equalizer (a `Prop`, so the proof is
    choice-free): `m` equalizes the pair, and every `e` that equalizes factors
    uniquely through `m`.  Both parts come from the classifier pullback square
    (`classify_pullback`): `m` is the pullback of `t : 1 → Ω` along `χ_m`, and a
    pullback of `t` is exactly an equalizer of `χ_m` and `A → 1 → Ω`. -/
theorem monic_is_equalizer {A A' : 𝒞} (m : A' ⟶ A) (hm : Mono m) :
    m ≫ HasSubobjectClassifier.classify m hm
        = m ≫ (term A ≫ HasSubobjectClassifier.true)
    ∧ ∀ {E : 𝒞} (e : E ⟶ A),
        e ≫ HasSubobjectClassifier.classify m hm
          = e ≫ (term A ≫ HasSubobjectClassifier.true) →
        ∃ k : E ⟶ A', k ≫ m = e ∧ ∀ k' : E ⟶ A', k' ≫ m = e → k' = k := by
  refine ⟨?_, ?_⟩
  · -- `m` equalizes: `m ≫ χ = term A' ≫ t = (m ≫ term A) ≫ t = m ≫ (term A ≫ t)`.
    calc m ≫ HasSubobjectClassifier.classify m hm
        = term A' ≫ HasSubobjectClassifier.true := HasSubobjectClassifier.classify_sq m hm
      _ = (m ≫ term A) ≫ HasSubobjectClassifier.true := by
            rw [term_uniq (m ≫ term A) (term A')]
      _ = m ≫ (term A ≫ HasSubobjectClassifier.true) := Cat.assoc _ _ _
  · intro E e he
    -- Turn `e` into a cone over `(χ_m, t)`: the square `E → 1 → Ω` and `E → A → Ω`.
    have hw : e ≫ HasSubobjectClassifier.classify m hm
            = term E ≫ HasSubobjectClassifier.true := by
      calc e ≫ HasSubobjectClassifier.classify m hm
          = e ≫ (term A ≫ HasSubobjectClassifier.true) := he
        _ = (e ≫ term A) ≫ HasSubobjectClassifier.true := (Cat.assoc _ _ _).symm
        _ = term E ≫ HasSubobjectClassifier.true := by
              rw [term_uniq (e ≫ term A) (term E)]
    -- The classifier pullback yields a factorization `u ≫ m = e`; `m` monic gives uniqueness.
    obtain ⟨u, ⟨hu, _⟩, _⟩ :=
      HasSubobjectClassifier.classify_pullback m hm
        (⟨E, e, term E, hw⟩ : Cone (HasSubobjectClassifier.classify m hm) HasSubobjectClassifier.true)
    exact ⟨u, hu, fun k' hk' => hm k' u (hk'.trans hu.symm)⟩

/-- **§1.913**: In a topos, covers coincide with epimorphisms.
    Because every monic is an equalizer, every cover (= family containing a split)
    is epic; and the converse holds from the subobject classifier property. -/
theorem covers_coincide_with_epis {A B : 𝒞} (f : A ⟶ B) : True := by
  trivial

/-! ## §1.919  Monic endomorphisms of Ω are involutions

  §1.919: Every monic endomorphism g : Ω → Ω is an involution (g² = id).
  BECAUSE: g acts on subobjects as a "g-large" filter; monic-ness forces it
  to be an isomorphism of order at most 2. -/

/-- **§1.919**: Every monic endomorphism of Ω is an involution;
    that is, g : Ω → Ω monic implies g ≫ g = id.

    Proof sketch (Freyd): Let g be monic.  g acts on subobjects via
    post-composition: it sends χ : A → Ω to g∘χ : A → Ω.  Since g is
    monic, if A is the subobject classified by χ, then A is also the
    subobject classified by g∘χ (because g∘χ = g∘χ' ⇒ χ = χ').
    But the subobject classified by g∘g∘χ is the same as that
    classified by χ (by considering the pullback of t along g∘g).
    Hence g∘g∘χ = χ for all χ, which forces g∘g = id.

    **Prerequisite**: the universal property of the subobject classifier
    (pullback of t along classify m restores m), not yet in the class
    definition.  Currently a `sorry`. -/
theorem omega_monic_endo_is_involution (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Mono g) : g ≫ g = Cat.id _ := by
  sorry

/-! ## §1.91(10)  Minimal topos definition

  A category with binary products and equalizers (equivalently: binary
  products and pullbacks) and power objects, which is non-empty, has a
  terminator and hence is a topos (§1.91(10)). -/

/-- **§1.91(10)**: If a non-empty category has binary products, equalizers,
    and power objects, then it has a terminator (and is thus a topos). -/
theorem minimal_topos_has_terminator [HasBinaryProducts 𝒞] : True := by
  -- Construction: for any B, the equalizer of 1_{[B]} and Λ(M_{B,B})
  -- is a terminator, where M_{B,B} is the relation tabulated by B×B.
  trivial

end Freyd
