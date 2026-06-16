/-
  Freyd & Scedrov, *Categories and Allegories* §1.95–§1.96  Topos theorems.

  §1.951  A topos is EFFECTIVE (every equivalence relation is effective).
  §1.952  A topos is POSITIVE.
  §1.954  A topos has coequalizers.
  §1.955  A topos is bicartesian.
  §1.961  INJECTIVE object; INTERNALLY INJECTIVE; Ω is internally injective.
  §1.962  Ω^A is injective; every object embeds in an injective.
  §1.964  VALUE-BASED category/topos; Ω cogenerates in a value-based topos.
  §1.965  INTERNALLY COGENERATES.
  §1.966  PROGENITOR.
  §1.967  Arbitrary powers ↔ arbitrary copowers ↔ arbitrary copowers of 1 (locally small topos).
  §1.968  Locally small topos: complete ↔ cocomplete.
  §1.969  Lawvere and Tierney definitions of Grothendieck topos.
-/

import Fredy.S1_1
import Fredy.S1_9
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58
import Fredy.S1_59
import Fredy.S1_62
import Fredy.S1_64
import Fredy.S1_82
import Fredy.S1_84
import Fredy.S1_85
import Fredy.S1_91
import Fredy.S1_92
import Fredy.S1_94


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## §1.951  A topos is effective -/

/-- **§1.951**: A topos is effective: every equivalence relation on any object
    is the level of some morphism (i.e., is effective in the sense of §1.56).
    Proof sketch (Freyd): factor A →(h) B →(H) [A] via the image.  The key
    lemma in a regular category is: an equivalence relation E is distinguished
    by the pairs (f,g) with fE = gE.  Applying this to hh" shows hh" = E. -/
instance topos_is_effective [Topos 𝒞] : EffectiveRegular 𝒞 := by
  sorry

/-! ## §1.952  A topos is positive -/

/-- **§1.952**: A topos is positive: it has binary coproducts A + B.
    Proof sketch (Freyd): For any A, ΔR factors through ΔA1 iff R is a map,
    and through Δ0 iff R = 0.  So A + 1 exists.  Then A + B is constructed
    as a subobject of [A] × [B] = [A + B]. -/
instance topos_is_positive [Topos 𝒞] : HasBinaryCoproducts 𝒞 := by
  sorry

/-! ## §1.954  A topos has coequalizers -/

/-- **§1.954**: A topos has coequalizers.
    Given f, g : A → B, let R = f"g, S = (R ∪ R")* (the equivalence closure).
    A topos is effective [1.951], so S is the level of some B → C.
    This B → C is the coequalizer of f and g. -/
instance topos_has_coequalizers [Topos 𝒞] : HasCoequalizers 𝒞 := by
  sorry

/-! ## §1.955  A topos is bicartesian -/

/-- **§1.955**: A topos is bicartesian: it has terminal, coterminator, binary products,
    and binary coproducts.  Follows from: topos has coequalizers [1.954], a coterminator
    [1.944], and binary coproducts [1.952, 1.946]. -/
instance topos_is_bicartesian [Topos 𝒞] : BicartesianCategory 𝒞 := by
  sorry

/-! ## §1.961  Injective objects -/

/-- **§1.961**: An object E is INJECTIVE if the functor (-, E) carries monics to epics.
    Elementary version (in a pre-topos, pushouts of monics are monic):
    E is injective iff every monic E ↣ A has a right-inverse. -/
def IsInjective [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] (E : 𝒞) : Prop :=
  ∀ {A B : 𝒞} (f : A ⟶ B), Mono f →
    ∀ (g : A ⟶ E), ∃ (h : B ⟶ E), f ≫ h = g

/-- The map f × 1_Z : A × Z → B × Z for f : A → B (mapping the left factor). -/
def prodMapLeft [HasBinaryProducts 𝒞] {A B : 𝒞} (Z : 𝒞) (f : A ⟶ B) : prod A Z ⟶ prod B Z :=
  pair (fst ≫ f) snd

/-- The contravariant exponential map E^f : E^^B → E^^A induced by f : A → B
    (§1.853).  Defined by curry(e_B ∘ (f × 1_{E^^B})), where
    e_B : B × E^^B → E is evaluation and (f × 1) : A × E^^B → B × E^^B. -/
def expMap [HasExponentials 𝒞] {A B : 𝒞} (E : 𝒞) (f : A ⟶ B) : E ^^ B ⟶ E ^^ A :=
  -- (f × 1_{E^^B}) : prod A (E^^B) → prod B (E^^B)  (left-factor map)
  -- eval_exp B E   : prod B (E^^B) → E
  curry (prodMapLeft (E ^^ B) f ≫ eval_exp B E)

/-- **§1.961**: An object E in an exponential category is INTERNALLY INJECTIVE if
    E^(−) carries monics to epics: for every monic f : A ↣ B,
    the induced map E^f : E^^B → E^^A is a cover (= epic in a regular category). -/
def IsInternallyInjective [HasExponentials 𝒞] (E : 𝒞) : Prop :=
  ∀ {A B : 𝒞} (f : A ⟶ B), Mono f → Cover (expMap E f)

/-- **§1.961**: In a topos, Ω is internally injective.
    Proof: if f : A ↣ B is monic then Ω^f = [f"] (post-composition by f°),
    and [f"] has a left-inverse [f] (since f is monic iff f"f = 1).
    Hence Ω^f is epic (a cover). -/
theorem omega_is_internally_injective [Topos 𝒞] :
    IsInternallyInjective (𝒞 := 𝒞) (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  sorry

/-! ## §1.962  Ω^A is injective; every object embeds in an injective -/

/-- **§1.962**: If E is injective in an exponential category, then E^A is injective
    for any A.  Proof: (−, E^A) ≅ (− × A, E) and − × A preserves monics in any category. -/
theorem exp_of_injective_is_injective [HasExponentials 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {E : 𝒞} (hE : IsInjective E) (A : 𝒞) : IsInjective (E ^^ A) := by
  sorry

/-- **§1.962**: Consequently, in a topos, Ω^A is injective for all A.
    Since the singleton map embeds A into Ω^A, every object appears as a subobject
    of an injective. -/
theorem topos_every_object_embeds_in_injective [Topos 𝒞] (A : 𝒞) :
    ∃ (I : 𝒞) (m : A ⟶ I), Mono m ∧ IsInjective (𝒞 := 𝒞) I := by
  sorry

/-! ## §1.964  Value-based categories -/

/-- **§1.964**: A category is VALUE-BASED if its values (= morphisms from subterminators)
    form a basis (§1.632): the class of objects of the form U (for U ≤ 1) generates
    in the sense that the representable functors {(U, −)} for subterminators U are
    collectively faithful. -/
def IsValueBased [HasTerminal 𝒞] : Prop :=
  IsGeneratingSet (𝒞 := 𝒞) (fun G => ∃ (m : G ⟶ one), Mono m)

/-- **§1.964**: In a value-based topos, Ω is a cogenerator: for any f ≠ g : A → B,
    there exists h : B → Ω such that f ≫ h ≠ g ≫ h.
    Proof sketch (Freyd): (−, Ω) = χ?(−), so it suffices to find a subobject
    B' ⊆ B with f#(B') ≠ g#(B').  Use a subterminator x : U → A with xf ≠ xg
    and let B' = Im(xf); then x factors through f#(B') but not g#(B'). -/
theorem omega_cogenerates_in_value_based_topos [Topos 𝒞] (hVB : IsValueBased (𝒞 := 𝒞)) :
    ∀ {A B : 𝒞} (f g : A ⟶ B), f ≠ g →
      ∃ (h : B ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)), f ≫ h ≠ g ≫ h := by
  sorry

/-! ## §1.965  Internally cogenerates -/

/-- **§1.965**: An object C in an exponential category INTERNALLY COGENERATES if
    the functor C^(−) is a contravariant embedding: the maps C^f for varying f
    together distinguish morphisms.  Formally: for f ≠ g : A → B, C^f ≠ C^g. -/
def InternallyCogenerates [HasExponentials 𝒞] (C : 𝒞) : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B), expMap C f = expMap C g → f = g

/-- **§1.965**: A cogenerator internally cogenerates.
    If C cogenerates (i.e., (−, C) is an embedding) then C^(−) is also an embedding:
    for f ≠ g, T(C^f) ≠ T(C^g), hence C^f ≠ C^g. -/
theorem cogenerator_internally_cogenerates [HasExponentials 𝒞]
    (C : 𝒞)
    (hcog : ∀ {A B : 𝒞} (f g : A ⟶ B), f ≠ g →
      ∃ (h : B ⟶ C), f ≫ h ≠ g ≫ h) :
    InternallyCogenerates C := by
  sorry

/-- **§1.965**: In a topos, Ω internally cogenerates.
    Proof: suppose Ω^f = Ω^g.  Embed the small subtopos containing f,g faithfully
    into a capital (value-based) topos; there Ω cogenerates [1.964], so f = g. -/
theorem omega_internally_cogenerates [Topos 𝒞] : InternallyCogenerates (𝒞 := 𝒞) (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  sorry

/-! ## §1.966  Progenitor -/

/-- **§1.966**: An object G is a PROGENITOR if its subobjects form a generating set:
    for any monic m : A' ↣ A that is not an iso, there exists a subobject G' ≤ G
    and a map G' → A that does not factor through A'. -/
def IsProgenitor (G : 𝒞) : Prop :=
  IsGeneratingSet (𝒞 := 𝒞) (fun X => ∃ (m : X ⟶ G), Mono m)

/-- **§1.966**: A topos is value-based iff its terminator 1 is a progenitor.
    Any Grothendieck topos has a progenitor (disjoint union of a generating set). -/
theorem topos_value_based_iff_terminal_progenitor [Topos 𝒞] :
    IsValueBased (𝒞 := 𝒞) ↔ IsProgenitor (𝒞 := 𝒞) one := by
  sorry

/-- **§1.966**: If G is a progenitor for a topos, then Ω^G is a cogenerator:
    given f ≠ g : A → B there exists h : B → Ω^G with f ≫ h ≠ g ≫ h.
    Proof: (−, Ω^G) and (G, Ω^(−)) are naturally equivalent (exponential adjunction),
    so Ω^G cogenerates iff (G, Ω^(−)) is an embedding; use that Ω^f ≠ Ω^g
    (Ω internally cogenerates [1.965]) and G generates to find the witness. -/
theorem progenitor_omega_exp_cogenerates [Topos 𝒞] (G : 𝒞) (hG : IsProgenitor G) :
    ∀ {A B : 𝒞} (f g : A ⟶ B), f ≠ g →
      ∃ (h : B ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) ^^ G), f ≫ h ≠ g ≫ h := by
  sorry

/-! ## §1.967  Arbitrary powers ↔ arbitrary copowers ↔ arbitrary copowers of 1 -/

/-- **§1.967**: A category has arbitrary POWERS if for every object A and index set I,
    the I-fold product of A with itself exists (i.e., A^I in the exponential sense).
    In a topos this is A^(Ω^I) but here we mean the indexed product ∏_{i:I} A.
    Formally: for every type I : Type v and object A, an indexed product of the
    constant family (fun _ : I => A) exists. -/
class HasArbitraryPowers (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryProducts 𝒞] where
  /-- For each index type I and object A, the I-fold power of A. -/
  pow : (I : Type v) → 𝒞 → 𝒞
  /-- Projection from the power to A. -/
  proj : {I : Type v} → {A : 𝒞} → I → pow I A ⟶ A
  /-- Universal property: maps into the power correspond to I-indexed families of maps into A. -/
  tupling : {I : Type v} → {A X : 𝒞} → (I → X ⟶ A) → X ⟶ pow I A
  tupling_proj : ∀ {I : Type v} {A X : 𝒞} (f : I → X ⟶ A) (i : I),
    tupling f ≫ proj i = f i
  tupling_uniq : ∀ {I : Type v} {A X : 𝒞} (f : I → X ⟶ A) (h : X ⟶ pow I A),
    (∀ i, h ≫ proj i = f i) → h = tupling f

/-- **§1.967**: A category has arbitrary COPOWERS if for every object A and index set I,
    the I-fold coproduct of A with itself exists (the copower I ⊗ A = ∐_{i:I} A). -/
class HasArbitraryCopowers (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryCoproducts 𝒞] where
  /-- For each index type I and object A, the I-fold copower of A. -/
  copow : (I : Type v) → 𝒞 → 𝒞
  /-- Injection into the copower. -/
  inj : {I : Type v} → {A : 𝒞} → I → A ⟶ copow I A
  /-- Universal property: maps out of the copower correspond to I-indexed families of maps from A. -/
  cotupling : {I : Type v} → {A X : 𝒞} → (I → A ⟶ X) → copow I A ⟶ X
  inj_cotupling : ∀ {I : Type v} {A X : 𝒞} (f : I → A ⟶ X) (i : I),
    inj i ≫ cotupling f = f i
  cotupling_uniq : ∀ {I : Type v} {A X : 𝒞} (f : I → A ⟶ X) (h : copow I A ⟶ X),
    (∀ i, inj i ≫ h = f i) → h = cotupling f

/-- A LOCALLY SMALL TOPOS is a topos in which each hom-set (A, B) is a set
    (i.e., lives in the same universe as the index types for products).
    In our universe setup: the morphisms A ⟶ B form a type in universe v,
    matching the index universe for HasProducts / HasArbitraryPowers.
    This is a property, not extra structure — Lean's universe constraint
    already guarantees it when `[Cat.{v} 𝒞]` has v ≥ universe of hom-sets.
    We record it as a typeclass for use as a hypothesis in §1.967/1.968. -/
class LocallySmallTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞

/-- **§1.967**: In a locally small topos the following are equivalent:
    (a) Arbitrary powers of objects exist.
    (b) Arbitrary copowers of objects exist.
    (c) Arbitrary copowers of 1 exist (i.e., 1 has an I-fold copower for every I).

    Each condition implies local completeness.

    Proof sketch (Freyd):
    (a)→local completeness: given {Bᵢ} ⊆ B, let f : B → ∏ᵢ Ω be the map with
      i-th component χ(Bᵢ), let g have i-th component χ(B); the equalizer is ⋂Bᵢ.
      Since the topos is well-powered (|(−,Ω)| = |Sub(−)|), arbitrary intersections
      imply arbitrary unions.
    (a)→(b): construct the copower I ⊗ A as a subobject of ∏ᵢ (A+1) using the
      complemented injections uᵢ (where uᵢuᵢ° = 1, uᵢuⱼ° = 0 for i ≠ j).
    (b)→(c): trivially, copower of A specializes to copower of 1.
    (c)→(a): ∏ᵢ A ≅ A^(I⊗1) using the exponential structure of the topos.

    We state (a)↔(b)↔(c) and each implies local completeness; all proofs are sorry
    since each direction requires substantial topos-theory infrastructure. -/
theorem topos_powers_copowers_equiv [LocallySmallTopos 𝒞]
    [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞] :
    (Nonempty (HasArbitraryPowers (𝒞 := 𝒞))) ↔
    (Nonempty (HasArbitraryCopowers (𝒞 := 𝒞))) := by
  sorry

/-- **§1.967**: Arbitrary copowers of objects exist iff arbitrary copowers of 1 exist.
    (b)↔(c): (b)→(c) is trivial; (c)→(b) uses ∐ᵢ A ≅ (∐ᵢ 1) × A in a Cartesian category
    (the copower of 1 is an I-indexed colimit, and products distribute over coproducts
    in a topos). -/
theorem topos_copowers_equiv_copowers_of_one [LocallySmallTopos 𝒞]
    [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞] :
    (Nonempty (HasArbitraryCopowers (𝒞 := 𝒞))) ↔
    (∀ (I : Type v), ∃ (cI : 𝒞) (inj : I → one ⟶ cI),
      ∀ {X : 𝒞} (f : I → one ⟶ X), ∃ (h : cI ⟶ X), ∀ i, inj i ≫ h = f i) := by
  sorry

/-- **§1.967**: Arbitrary powers imply local completeness in a locally small topos.
    Proof: let {Bᵢ ↣ B} be a family of subobjects.  Since the topos is locally small,
    (B, Ω) is a set, so the power ∏ᵢ Ω exists.  The maps χ(Bᵢ) and χ(B) : B → ∏ᵢ Ω
    have an equalizer that is ⋂ᵢ Bᵢ.  Arbitrary intersections + well-poweredness
    give arbitrary unions via the Ω-internal complement structure. -/
noncomputable def topos_powers_implies_locally_complete [LocallySmallTopos 𝒞]
    [HasBinaryProducts 𝒞] [HasEqualizers 𝒞] (hpow : HasArbitraryPowers (𝒞 := 𝒞)) :
    LocallyComplete' 𝒞 := by
  sorry

/-! ## §1.968  Complete ↔ cocomplete for locally small topoi -/

/-- **§1.968**: A locally small topos is complete iff it is cocomplete.

    (cocomplete → complete): If arbitrary coproducts exist, embed each Aᵢ into
    S = ∐ᵢ Aᵢ.  By §1.967 arbitrary powers exist (via copowers).  For each i,
    the arrow Aᵢ → S witnesses Aᵢ as a subobject of S.  Set P = ∏ᵢ S.
    The product of the embeddings Aᵢ ↣ S (pulling back via the projections)
    extracts ∏ᵢ Aᵢ as the subobject of P where all components agree.

    (complete → cocomplete): Arbitrary products imply arbitrary copowers (§1.967),
    and from copowers coproducts are built as subobjects of copowers of a cogenerator. -/
theorem topos_complete_iff_cocomplete [LocallySmallTopos 𝒞]
    [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞] [HasEqualizers 𝒞] :
    Nonempty (Complete 𝒞) ↔ Nonempty (Cocomplete 𝒞) := by
  sorry

/-! ## §1.969  Lawvere and Tierney definitions of a Grothendieck topos -/

/-- **§1.969**: The LAWVERE DEFINITION of a Grothendieck topos:
    a cocomplete topos with a generating set.
    (By §1.967 copowers of 1 give all copowers, hence all coproducts,
     so with a generating set one recovers the Giraud axioms.) -/
class LawvereGrothendieckTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞 where
  /-- Arbitrary coproducts exist. -/
  cocomplete : Cocomplete 𝒞
  /-- A small generating set. -/
  gen_set : 𝒞 → Prop
  has_gen_set : IsGeneratingSet gen_set

/-- **§1.969**: The TIERNEY DEFINITION of a Grothendieck topos:
    a topos with a progenitor and arbitrary copowers of 1.
    (The copowers-of-1 condition is equivalent to having a geometric morphism to Set.) -/
class TierneyGrothendieckTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞,
    HasBinaryCoproducts 𝒞 where
  /-- A progenitor exists. -/
  progenitor : 𝒞
  is_progenitor : IsProgenitor progenitor
  /-- Arbitrary copowers of 1 exist. -/
  copow_one : (I : Type v) → ∃ (cI : 𝒞) (inj : I → one ⟶ cI),
    ∀ {X : 𝒞} (f : I → one ⟶ X), ∃ (h : cI ⟶ X), (∀ i, inj i ≫ h = f i)

/-- **§1.969**: The Lawvere and Tierney definitions yield the same notion.
    Given the Tierney definition, use §1.966 to get Ω^G as cogenerator,
    then §1.967 (c)→(a) to get arbitrary powers, then the coproduct construction
    in the proof of §1.968. -/
theorem lawvere_eq_tierney (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞]
    [HasEqualizers 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] :
    Nonempty (LawvereGrothendieckTopos 𝒞) ↔ Nonempty (TierneyGrothendieckTopos 𝒞) := by
  sorry

end Freyd
