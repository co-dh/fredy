/-
  Freyd & Scedrov, *Categories and Allegories* §1.63–§1.66
  Slice pre-logos, Boolean pre-logoi, Pre-topoi, Amalgamation.

  §1.63  If A is a (positive) pre-logos, so is A/B (§1.63).
  §1.631 Complemented subobject: A₁∩A₂=0, A₁∪A₂=A.
  §1.64  Boolean pre-logos: subobject lattices are Boolean algebras.
  §1.644 Ultra-product / ultra-power functors (§1.644).
  §1.645 𝒦𝓮𝓇(T) = values killed by representation T.
  §1.65  Pre-topos = effective positive pre-logos.
  §1.651 Amalgamation Lemma: pushout of two monics exists.
  §1.652 In a pre-topos: covers = epics, monics = cocovers.
  §1.66  (if applicable)
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58
import Fredy.S1_59
import Fredy.S1_60
import Fredy.S1_57
import Fredy.S1_62


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.631 Complemented subobject

  A₁ ⊆ A is COMPLEMENTED if ∃ A₂ ⊆ A with A₁∩A₂=0, A₁∪A₂=A. -/

variable [PreLogos 𝒞]

/-- A₁ is COMPLEMENTED if there's A₂ with A₁∩A₂=0 and A₁∪A₂=A.
    (Placeholder: intersection not yet defined.) -/
def IsComplemented {A : 𝒞} (A₁ : Subobject 𝒞 A) : Prop :=
  ∃ (A₂ : Subobject 𝒞 A),
    (∀ (S : Subobject 𝒞 A), Subobject.le S A₁ → Subobject.le S A₂ → False)
    -- A₁∩A₂ is minimal (no non-trivial common subobject)
    ∧ Subobject.le (Subobject.entire A) (HasSubobjectUnions.union A₁ A₂)
    -- A₁∪A₂ = A (entire)

/-! ## §1.64 Boolean pre-logos

  A BOOLEAN PRE-LOGOS is a pre-logos where every subobject lattice
  is Boolean (every subobject has a complement). -/

class BooleanPreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends PreLogos 𝒞 where
  hasComplement : ∀ {A : 𝒞} (S : Subobject 𝒞 A), IsComplemented S

/-! ## §1.645 𝒦𝓮𝓇(T) — values killed by a representation

  For T: A → B a representation of boolean pre-logoi, Kℯℛ(T) is
  the set of subterminators U ⊆ 1 such that T(U) = 0. -/

/-- The kernel of a representation T: the set of subterminators sent to 0. -/
def killedValues {𝒟 : Type u} [Cat.{v} 𝒟] [PreLogos 𝒞] [PreLogos 𝒟]
    (T : 𝒞 → 𝒟) [Functor T] : (Subobject 𝒞 one) → Prop :=
  λ U => @Isomorphic 𝒟 _ (T U.dom) one

/-! ## §1.646 Faithful representability of small special categories

  Every small special Cartesian category is faithfully representable in Set.
  Every small special positive pre-logos is faithfully representable in Set.
  PROOF (§1.646): Combine §1.472/§1.637 (finite separation) with a diagonal
  ultra-filter argument: I = finite sets of proper subobjects, choose T_S for
  each S, form T : A → Set^I, extend to an ultra-filter F ⊇ principal coideals.
  T^F is faithful.  (Requires ultra-filter machinery; sorry.) -/

-- §1.646 (note): Every small special Cartesian category embeds faithfully in Set.
-- Proof combines §1.472/§1.637 with an ultra-filter diagonal argument.
-- Requires ultra-filter infrastructure outside this repo's scope.

-- §1.647 (note): A boolean pre-logos is special iff two-valued.
-- Proof: complement of (A₁×B₂)∪(B₁×A₂) in B₁×B₂ is A₁°×A₂°.
-- Requires complement intersection/union infrastructure not yet formalized.

-- §1.648 (note): Ultra-power T = Set^I → Set^I/F is bicartesian iff F is
-- a complete measure (meets every countable partition of I).
-- Requires ultra-filter/ultra-product infrastructure outside this repo.

/-! ## §1.65 Pre-topos

  A PRE-TOPOS is an effective positive pre-logos:
  effective regular + positive pre-logos. -/

class PreTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    EffectiveRegular 𝒞, PositivePreLogos 𝒞

/-! ## §1.651 Amalgamation Lemma

  In a pre-topos, given monics x: A↣B, y: A↣C, there exists a
  pushout B ↣ D, C ↣ D completing the square. -/

/-- **§1.651 Amalgamation Lemma**: In a pre-topos, the pushout of two
    monics with a common source exists and the resulting maps are monic.
    Proof: form B+C, define equivalence relation E identifying x(a)∼y(a),
    then the effective quotient B+C ↠ D gives the pushout.
    Requires effective regularity (every equivalence relation has a coequalizer)
    which needs additional structure in `EffectiveRegular`. -/
theorem amalgamation_lemma [PreTopos 𝒞] {A B C : 𝒞}
    (x : A ⟶ B) (hx : Mono x) (y : A ⟶ C) (hy : Mono y) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D), Mono u ∧ Mono v ∧ x ≫ u = y ≫ v := by
  sorry

/-! ## §1.652 Covers = epics, Monics = cocovers

  In a pre-topos, covers coincide with epimorphisms, and monics
  coincide with coequalizers (cocovers). -/

/-- **§1.652 (crux): a pre-topos is BALANCED** — a map that is both monic and
    epic is an isomorphism.  This is the genuine positivity content of §1.652:
    the cokernel pair of `m` is built from the *disjoint* coproduct `B + B`
    (positivity) via the effective quotient, and a monic that is also epic
    equalizes a pair of equal legs, hence splits.  It is **not** derivable from
    the current axioms — `HasBinaryCoproducts` carries only the bare universal
    property, with no disjointness/universality, so the cokernel-pair argument
    has no axiom to stand on.  Isolated here as the single obligation that both
    reverse-directions below (`cover_eq_epic_preTopos`, `monic_eq_cocover`) rest
    on; closing it needs §1.62 positivity axiomatized as Freyd states it
    (disjoint + universal coproducts). -/
theorem pretopos_balanced [PreTopos 𝒞] {A B : 𝒞} (m : A ⟶ B) (hm : Mono m)
    (hepi : ∀ {C : 𝒞} (g h : B ⟶ C), m ≫ g = m ≫ h → g = h) : IsIso m := by
  sorry

theorem cover_eq_epic_preTopos [PreTopos 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Cover f ↔ (∀ {C : 𝒞} (g h : B ⟶ C), f ≫ g = f ≫ h → g = h) := by
  constructor
  · -- Cover → epic (§1.512): already proved
    exact cover_epi
  · intro hepi
    rw [cover_iff_image_entire]
    -- Goal: Subobject.IsEntire (image f), i.e., IsIso (image f).arr.
    -- `(image f).arr` is monic; since `f = lift ≫ arr` is epic, `arr` is epic too.
    have h_arr_epi : ∀ {C : 𝒞} (g h : B ⟶ C), (image f).arr ≫ g = (image f).arr ≫ h → g = h := by
      intro C g h heq
      apply hepi
      calc f ≫ g = (image.lift f ≫ (image f).arr) ≫ g := by rw [image.lift_fac f]
        _ = image.lift f ≫ ((image f).arr ≫ g) := Cat.assoc _ _ _
        _ = image.lift f ≫ ((image f).arr ≫ h) := by rw [heq]
        _ = (image.lift f ≫ (image f).arr) ≫ h := by rw [← Cat.assoc]
        _ = f ≫ h := by rw [image.lift_fac f]
    -- monic + epic ⟹ iso by balancedness (`pretopos_balanced`), so `image f` is entire.
    exact pretopos_balanced (image f).arr (image f).monic h_arr_epi

/-- **§1.652**: In a pre-topos, monics coincide with cocovers
    (maps that are coequalizers of some pair).
    Requires effective regularity (every monic is a regular monic = an equalizer,
    dually every epic is a regular epic = a coequalizer).
    The `HEq` in the statement is a placeholder for an isomorphism between
    the coequalizer map and `f`. -/
theorem monic_eq_cocover_preTopos [PreTopos 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Mono f ↔ ∃ (C : 𝒞) (p q : C ⟶ A), HEq ((HasCoequalizers.coeq p q).map) f := by
  sorry

/-! ## §1.653 Pushout of a monic and any morphism in a pre-topos

  Given morphisms f: A → B and monic y: A ↣ C in a pre-topos, there is a pushout
  square with the top map monic.  The proof factors f as cover ∘ monic (image
  factorization) and applies the amalgamation lemma §1.651 to the two monics. -/

/-- **§1.653**: In a pre-topos, given f : A → B and monic y : A ↣ C, there exists a
    pushout square (with the B-map monic).
    PROOF: Factor A → B as A ↠ I ↣ B.  Apply §1.651 to I ↣ B and I ↣ C' (pushing y
    through the cover A ↠ I), stack the two squares, and use the pasting lemma. -/
theorem pushout_monic_in_pretopos [PreTopos 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) (y : A ⟶ C) (hy : Mono y) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D), Mono u ∧ f ≫ u = y ≫ v := by
  sorry

/-! ## §1.654/§1.657 Pre-topos is cocartesian iff minimal equivalence relations exist

  A pre-topos is COCARTESIAN (its opposite is regular) if and only if
  for every endo-relation R on an object A there exists a minimal
  equivalence relation Ê ⊇ R on A.
  (§1.657: effectiveness means Ê is the level of some coequalizer A → B.)

  Proof sketch (§1.657):
  · (⇒) If A has coequalizers, given f: A→B with level E ⊇ R, then E is
    the minimal equivalence relation containing R (effectiveness).
  · (⇐) Conversely, given R = x°y (level of x,y : C⇒A), form the
    minimal equivalence Ê containing x°y; by effectiveness, Ê = level of
    some cover z: A→B; then z is a coequalizer of x and y. -/

/-- Every endo-relation on every object has a minimal equivalence relation containing it. -/
def HasMinEquivContaining (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] [HasImages 𝒞] : Prop :=
  ∀ (A : 𝒞) (R : BinRel 𝒞 A A),
    ∃ (E : BinRel 𝒞 A A), EquivalenceRelation E
      ∧ RelLe R E
      ∧ ∀ (F : BinRel 𝒞 A A), EquivalenceRelation F → RelLe R F → RelLe E F

/-- **§1.657**: A pre-topos with coequalizers satisfies HasMinEquivContaining.
    Effectiveness supplies the minimal equivalence relation as the level of
    the coequalizer, and conversely the minimal equivalence relation yields
    the coequalizer by effectiveness.
    (Both directions require the full machinery of §1.567–§1.568; sorry.) -/
theorem preTopos_cocartesian_to_minEquiv [PreTopos 𝒞] [HasCoequalizers 𝒞] :
    HasMinEquivContaining 𝒞 := by
  sorry

theorem preTopos_minEquiv_to_cocartesian [PreTopos 𝒞]
    (h : HasMinEquivContaining 𝒞) : Nonempty (HasCoequalizers 𝒞) := by
  sorry

/-! ## §1.655 Bicartesian representation criterion

  If A and B are pre-topoi and T : A → B a functor preserving 0, pushouts,
  finite products and monics, then T is a bicartesian representation.
  PROOF SKETCH (§1.655): T preserves pullbacks of monics (by §1.651 + pasting);
  T preserves equalizers (products ⟹ equalizers); T preserves covers (=
  coequalizers, §1.652; T preserves pushouts and 0). -/

-- §1.655 (note): A functor T between pre-topoi preserving 0, pushouts, products
-- and monics is a bicartesian representation.
-- PROOF: Products + §1.651 → T preserves pullbacks of monics; products → equalizers
-- (§1.434); covers = coequalizers + pushout preservation → T preserves covers.
-- Requires formalizing the Functor API for inter-category morphisms.

/-! ## §1.658 Decidable object

  An object A in a pre-logos is DECIDABLE if the diagonal (1,1): A → A×A
  has a complement in the subobject lattice of A×A.

  Every object in a pre-topos is decidable iff the pre-topos is boolean.

  PROOF SKETCH:
  (⇐) Boolean ⇒ every subobject is complemented, in particular the diagonal.
  (⇒) Given A decidable, let A' → A×B be any subobject; form the equalizer of
      (A' → A×B → B → B×B) and (A' → A×B → A×B → B×B via diag∘second).
      Because pullbacks of complemented subobjects are complemented (§1.658),
      the Boolean algebra structure transfers to all subobjects via slices. -/

/-- **§1.658**: A in a pre-logos is DECIDABLE if the diagonal `diag A : A → A×A`
    has a complement in `Subobject 𝒞 (prod A A)`.
    Lean note: `diag A` is monic (§1.42: `diag_mono`); the subobject is `{ dom := A, arr := diag A, monic := diag_mono A }`. -/
def DecidableObject [PreLogos 𝒞] [HasBinaryProducts 𝒞] (A : 𝒞) : Prop :=
  IsComplemented ({ dom := A, arr := diag A, monic := diag_mono A } : Subobject 𝒞 (prod A A))

/-- **§1.658**: Every object in a pre-topos is decidable iff the pre-topos is boolean.
    The harder direction (all decidable → boolean) follows because pullbacks of
    complemented subobjects are complemented, and every subobject U ⊆ 1 can be
    pulled back to any slice, where it coincides with the diagonal. -/
theorem preTopos_boolean_iff_all_decidable [PreTopos 𝒞] [HasBinaryProducts 𝒞] :
    (Nonempty (BooleanPreLogos 𝒞)) ↔ ∀ (A : 𝒞), DecidableObject A := by
  sorry

/-! ## §1.659 Decidability in functor categories and sheaves

  T ∈ Fᴬ is decidable iff T(x) is a monic map for all x : A → B ∈ A.
  For sheaves: X → Y is decidable iff every pair of points with the same
  stalk have disjoint neighborhoods; in particular, decidable iff Y is Hausdorff.
  (These results require the sheaf/functor-category infrastructure; stated
  with sorry pending that development.) -/

-- §1.659 (note): T ∈ Fᴬ is decidable iff T(x) is a monic map for all x : A → B in A.
-- For sheaves on Y: X → Y is decidable iff stalk-equal points have disjoint neighborhoods
-- (Y Hausdorff → X → Y decidable iff X Hausdorff).
-- Requires functor category and sheaf infrastructure.

/-! ## §1.66 Choice objects in a pre-topos

  We study choice objects [§1.57] in a regular category. -/

section Choice66

variable [RegularCategory 𝒞]

/-- **§1.66**: A subobject of a choice object is choice.
    If C is choice and m: A↣C is monic, then A is choice.
    PROOF: Let R be an entire relation from X to A.
    Then m ≫ R is an entire relation from X to C (composition with a map).
    Because C is choice, m ≫ R contains a map f: X → C.
    Since m is monic, f factors uniquely through A: the factorization gives
    the required map in R. (Requires: entire relations compose with maps.) -/
theorem subobject_of_choice_is_choice {A C : 𝒞} (m : A ⟶ C) (hm : Mono m)
    (hC : Choice C) : Choice A := by
  sorry

/-- **§1.66**: A quotient (cover target) of a choice object is choice.
    If C is choice and x: C↠B is a cover, then B is choice.
    PROOF (book §1.66): x: C → B is also a subobject of C via x° ⊂ 1_C
    (the inclusion via a map contained in x°). Apply subobject_of_choice. -/
theorem quotient_of_choice_is_choice {B C : 𝒞} (x : C ⟶ B) (hx : Cover x)
    (hC : Choice C) : Choice B := by
  sorry

end Choice66

/-! ## §1.661 Finite products of choice objects are choice

  In a regular category, finite products of choice objects are choice.
  (Proof uses: any entire relation targeted at a terminator is already a map;
  for binary products, decompose R : X → B₁×B₂ via its projections.) -/

section Choice661

variable [RegularCategory 𝒞]

/-- **§1.661**: The terminator is always choice in a regular category.
    PROOF: Any entire relation R : X → 1 is automatically simple, because all maps
    to `one` are equal (terminal uniqueness), so `R° ⊚ R : one → one` trivially lies
    inside `graph id_one`.  Hence R is a map, its left leg R.colA is an iso, and its
    inverse is the required section. -/
theorem terminator_is_choice : Choice (one : 𝒞) := by
  intro A R hent
  -- Terminal uniqueness forces R to be simple.
  have h_simple : Simple R :=
    ⟨⟨(R° ⊚ R).colA,
      by simp [graph, Cat.comp_id],
      by simp [graph]; rw [Cat.comp_id]; exact term_uniq _ _⟩⟩
  -- Entire + Simple = Map, so R.colA is an isomorphism.
  have h_iso : IsIso R.colA :=
    (tabulated_is_map_iff_left_iso R.colA R.colB R.isMonicPair).mp ⟨hent, h_simple⟩
  obtain ⟨inv, _hinv_left, hinv_right⟩ := h_iso
  exact ⟨inv ≫ R.colB, inv, hinv_right, rfl⟩

/-- **§1.661**: The binary product of two choice objects is choice.
    PROOF (book §1.661): Let R be entire from A to B₁×B₂.
    R∘fst° is entire targeted at B₁, so it contains a map f₁.
    In Sets, R ∩ f₁∘fst° is entire (§1.551, §1.563 transfer to any regular category).
    Its projection R ∩ f₁∘fst°∘snd° is entire targeted at B₂, so it contains f₂.
    Then (f₁, f₂): A → B₁×B₂ is contained in R. -/
theorem prod_choice_is_choice {B₁ B₂ : 𝒞} (h₁ : Choice B₁) (h₂ : Choice B₂) :
    Choice (prod B₁ B₂) := by
  sorry

end Choice661

/-! ## §1.662 Diaconescu's theorem in a pre-topos

  In a pre-topos, the following are equivalent:
  (1) Binary coproducts of choice objects are choice.
  (2) 1+1 is choice.
  (3) The pre-topos is boolean. -/

section Diaconescu

variable [PreTopos 𝒞] [HasBinaryCoproducts 𝒞]

/-- **§1.662**: (1) → (2): trivially, 1+1 is a coproduct of 1 and 1, and 1 is choice. -/
theorem coprod_choice_to_one_one_choice
    (h : ∀ (B₁ B₂ : 𝒞), Choice B₁ → Choice B₂ →
         Choice (HasBinaryCoproducts.coprod B₁ B₂)) :
    Choice (HasBinaryCoproducts.coprod (one : 𝒞) one) :=
  h one one terminator_is_choice terminator_is_choice

/-- **§1.662**: (2) → (3): 1+1 choice implies boolean.
    PROOF: The intermediate condition (2a) — every cover X∪Y=B can be
    refined to a partition X'⊆X, Y'⊆Y with X'∪Y'=B and X'∩Y'=∅ —
    is a restatement of (2) because maps B → 1+1 are partitions of B.
    (2a) is inherited by slices, so it suffices to show 𝒮(1) is boolean.
    Any U ⊆ 1 gives a pushout P = 1 +_U 1; 1+1 choice ⟹ P is a subobject
    of 1+1; 1+1 is decidable (§1.658) and so is P; U is complemented as a
    pullback of a complemented subobject. -/
theorem one_one_choice_to_boolean [HasBinaryProducts 𝒞]
    (h : Choice (HasBinaryCoproducts.coprod (one : 𝒞) one)) :
    Nonempty (BooleanPreLogos 𝒞) := by
  sorry

/-- **§1.662**: (3) → (1): boolean implies binary coproducts of choice objects are choice.
    PROOF: Given S: A → B₁+B₂ entire, the subobject Dom(S∘inl°) ⊆ A is complemented
    (boolean pre-topos). The restriction of S to Dom(S∘inl°) is entire into B₁, so
    contains f₁ (B₁ choice). The restriction to the complement is entire into B₂,
    so contains f₂ (B₂ choice). Then f₁+f₂ (copairing) is a map in S. -/
theorem boolean_to_coprod_choice_is_choice [HasBinaryProducts 𝒞]
    (hbool : Nonempty (BooleanPreLogos 𝒞)) :
    ∀ (B₁ B₂ : 𝒞), Choice B₁ → Choice B₂ →
      Choice (HasBinaryCoproducts.coprod B₁ B₂) := by
  sorry

end Diaconescu

end Freyd
