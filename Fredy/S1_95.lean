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

end Freyd
