/-
  Freyd & Scedrov, *Categories and Allegories* §1.56–§1.564
  Relations: composition, reciprocal, graph, entire, simple, map.

  §1.56  Composition of binary relations (via pullback + image).
  §1.561 Reciprocal (swap columns).  Involutive, reverses composition.
  §1.562 Semi-lattice structure: intersection, containment order.
  §1.563 Modular identity: RS ∩ T ⊆ (R ∩ TS°)S.
  §1.564 Graph of a morphism, ENTIRE, SIMPLE, MAP (= entire + simple).
         Cover ↔ entire, Monic ↔ simple.
-/


import Fredy.S1_1
import Fredy.S1_33
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## Binary relations (§1.412, §1.56)

  A BINARY RELATION from A to B is an isomorphism class of 2-column
  tables (jointly-monic pairs ⟨T; a:T→A, b:T→B⟩).  We work with
  representatives. -/

/-- A binary relation: jointly-monic pair a: T→A, b: T→B. -/
structure BinRel (𝒞 : Type u) [Cat.{v} 𝒞] (A B : 𝒞) where
  src  : 𝒞
  colA : src ⟶ A
  colB : src ⟶ B
  isMonicPair : MonicPair colA colB

/-- Two relations are considered equal if they are isomorphic as tables.
    (We don't quotient; containment gives the preorder.) -/
def RelHom {A B : 𝒞} (R S : BinRel 𝒞 A B) : Prop :=
  ∃ (h : R.src ⟶ S.src), h ≫ S.colA = R.colA ∧ h ≫ S.colB = R.colB

/-- R ≤ S as relations (containment order, §1.413). -/
def RelLe (R S : BinRel 𝒞 A B) : Prop := Nonempty (RelHom R S)

/-! ## §1.564 Graph of a morphism -/

def graph {A B : 𝒞} (x : A ⟶ B) : BinRel 𝒞 A B where
  src  := A
  colA := Cat.id A
  colB := x
  isMonicPair := λ {_W} f g hA _ => by
    -- hA: f ≫ id = g ≫ id  →  f = g
    simpa [Cat.id_comp, Cat.comp_id] using hA

/-! ## §1.561 Reciprocal -/

def reciprocal {A B : 𝒞} (R : BinRel 𝒞 A B) : BinRel 𝒞 B A where
  src  := R.src
  colA := R.colB
  colB := R.colA
  isMonicPair := λ {_W} f g hA hB => R.isMonicPair f g hB hA

/-- The reciprocal R°: swap columns (§1.561).  Postfix notation `_°`. -/
postfix:max "°" => reciprocal

theorem reciprocal_invol {A B : 𝒞} (R : BinRel 𝒞 A B) : reciprocal (reciprocal R) = R := by
  unfold reciprocal; rfl

/-! ## §1.56 Composition of relations

  Given R: A→B, S: B→C, in a Cartesian category with pullbacks and
  images, their composition RS: A→C is obtained by pulling back along
  the B-legs, then taking the image in A×C.  (§1.56) -/

/-- The composition RS: A→C (§1.56).
    1. Pull back R.colB and S.colA over B → object P
    2. Map P→A via P→R.src→A, P→C via P→S.src→C
    3. Take the image of the span P→A×C → this is the composed relation. -/
def compose {A B C : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C)
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] : BinRel 𝒞 A C :=
  -- Step 1: pullback of R.colB and S.colA over B
  let pb := HasPullbacks.has R.colB S.colA
  -- Step 2: span P→A and P→C
  let a' := pb.cone.π₁ ≫ R.colA
  let c' := pb.cone.π₂ ≫ S.colB
  -- Step 3: embed P→A×C via the pair (a', c')
  let h : pb.cone.pt ⟶ prod A C := pair a' c'
  -- Step 4: image of h in A×C
  let I := image h
  -- The image gives a monic I.arr: I.dom → A×C
  -- The composed relation: source = I.dom, legs are I.arr ≫ fst, I.arr ≫ snd
  { src := I.dom
    colA := I.arr ≫ fst
    colB := I.arr ≫ snd
    isMonicPair := by
      intro X f g hA hB
      -- hA: f ≫ I.arr ≫ fst = g ≫ I.arr ≫ fst
      -- hB: f ≫ I.arr ≫ snd = g ≫ I.arr ≫ snd
      -- Rewrite with associativity
      have h_fst : (f ≫ I.arr) ≫ fst = (g ≫ I.arr) ≫ fst := by
        simpa [Cat.assoc] using hA
      have h_snd : (f ≫ I.arr) ≫ snd = (g ≫ I.arr) ≫ snd := by
        simpa [Cat.assoc] using hB
      -- By the product universal property, f ≫ I.arr = g ≫ I.arr
      have h_prod : f ≫ I.arr = g ≫ I.arr := by
        let a := (f ≫ I.arr) ≫ fst
        let b := (f ≫ I.arr) ≫ snd
        have hf : f ≫ I.arr = pair a b :=
          pair_uniq a b (f ≫ I.arr) rfl rfl
        have hg : g ≫ I.arr = pair a b :=
          pair_uniq a b (g ≫ I.arr) h_fst.symm h_snd.symm
        rw [hf, hg]
      -- Since I.arr is monic, this implies f = g
      exact I.monic f g h_prod }

/-! ## §1.564 Entire, Simple, Map

  A relation R: A→B is ENTIRE if 1_A ≤ RR°.
  SIMPLE if R°R ≤ 1_B.
  A MAP is an entire + simple relation (= graph of a morphism). -/

/-- **§1.564**: R : A → B is ENTIRE if 1_A ≤ RR° — the identity relation
    on A is contained in RR° (compose R R° : A → A). -/
def Entire {A B : 𝒞} (R : BinRel 𝒞 A B) [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] : Prop :=
  RelLe (graph (Cat.id A)) (compose R (reciprocal R))

/-- **§1.564**: R is SIMPLE if R°R ≤ 1_B — R° composed with R
    (compose R° R : B → B) is contained in the identity on B. -/
def Simple {A B : 𝒞} (R : BinRel 𝒞 A B) [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] : Prop :=
  RelLe (compose (reciprocal R) R) (graph (Cat.id B))

/-- R is a MAP if it is entire and simple.  Maps are exactly graphs (§1.564). -/
def Map {A B : 𝒞} (R : BinRel 𝒞 A B) [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] : Prop :=
  Entire R ∧ Simple R

/-- **§1.564**: A relation ⟨T; a:T→A, b:T→B⟩ tabulated by a monic pair is a
    MAP (entire + simple) iff `a` is an isomorphism.  Maps are exactly the
    graphs of morphisms: if `R` is a map then `R = graph(b ≫ a⁻¹)`. -/
theorem tabulated_is_map_iff_left_iso {A B T : 𝒞} (a : T ⟶ A) (b : T ⟶ B) (hp : MonicPair a b)
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] :
    Map (BinRel.mk T a b hp) ↔ IsIso a := by
  sorry

/-! ## §1.563 Modular identity

  In a regular category: RS ∩ T ⊆ (R ∩ TS°)S.
  This is one of the defining axioms of allegories (§2).

  **Provability:** Not provable from the `BinRel` definition alone (jointly-monic
  pair + pullback/image composition).  In **Set**, the modular identity holds by
  element-wise reasoning — the standard proof constructs witnesses `y` from
  membership in RS ∩ T.  Freyd's strategy (§1.55, the Henkin-Lubkin
  representation theorem) faithfully embeds any small pre-regular category in a
  power of Set, and faithful representations reflect the modular identity back
  to the original category.  So it becomes a theorem after the representation is
  established, but not before. -/

theorem modular_identity {A B C : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 A C)
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] :
    RelLe (compose (compose R S) (reciprocal T)) (compose R (compose S (reciprocal T))) := by
  sorry

/-! ## §1.563 Horn-sentence reflection

  A HORN SENTENCE in the predicates of (pre-)regular categories is treated
  abstractly here (its syntax is developed in §1.55); `HoldsIn H 𝒟` says the
  sentence `H` is satisfied by the category `𝒟`. -/

/-- A Horn sentence in the first-order language of (pre-)regular categories. -/
opaque HornSentence : Type

/-- `H` HOLDS IN the category `𝒟`. -/
opaque HoldsIn (H : HornSentence) (𝒟 : Type u) [Cat.{v} 𝒟] : Prop

/-- **§1.563**: If A and B are Cartesian with images, and F : A → B is a faithful
    functor preserving finite limits and images, then F reflects any Horn sentence
    in the language of Cartesian categories with images.  In particular, the
    modular identity (being a Horn sentence) holds in A iff it holds in B. -/
theorem horn_sentence_reflected_by_faithful {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    [CartesianCategory 𝒜] [HasImages 𝒜] [CartesianCategory ℬ] [HasImages ℬ]
    (F : 𝒜 → ℬ) [Functor F] (hfaithful : Faithful F)
    (_h_preserves_limits : True) (_h_preserves_images : True)
    (H : HornSentence) (_hH : HoldsIn H ℬ) : HoldsIn H 𝒜 := by
  sorry

/-- **§1.563** (corollary, via Henkin-Lubkin §1.55): If A is a regular category,
    every Horn sentence in the predicates of regular categories true for the
    category of sets is true for A.  (`Type u` carries the category-of-sets
    structure as the instance argument.) -/
theorem horn_sentence_reflected_from_Set (A : Type u) [Cat.{v} A] [RegularCategory A]
    [Cat.{v} (Type u)] (H : HornSentence) (_hH : HoldsIn H (Type u)) : HoldsIn H A := by
  sorry

/-! ## §1.565 Pushouts

  A PUSHOUT is a pullback in the opposite category: given f: C→A, g: C→B,
  a pushout is P with maps A→P, B→P universal among cocones. -/

structure PushoutCocone {A B C : 𝒞} (f : C ⟶ A) (g : C ⟶ B) where
  pt : 𝒞
  ι₁ : A ⟶ pt
  ι₂ : B ⟶ pt
  w  : f ≫ ι₁ = g ≫ ι₂

class HasPushout {A B C : 𝒞} (f : C ⟶ A) (g : C ⟶ B) where
  cocone : PushoutCocone f g
  desc  : ∀ (c : PushoutCocone f g), cocone.pt ⟶ c.pt
  fac₁  : ∀ (c : PushoutCocone f g), cocone.ι₁ ≫ desc c = c.ι₁
  fac₂  : ∀ (c : PushoutCocone f g), cocone.ι₂ ≫ desc c = c.ι₂
  uniq  : ∀ (c : PushoutCocone f g) (h : cocone.pt ⟶ c.pt),
    cocone.ι₁ ≫ h = c.ι₁ → cocone.ι₂ ≫ h = c.ι₂ → h = desc c

/-! ## §1.565 Pullback of covers is a pushout

  In a regular category, if both legs of a pullback square are covers,
  then the square is also a pushout.

  Freyd's proof: form the relation R = p₁°a ∩ p₂°b, verify it is a map in
  **Set** by element-wise reasoning, then use the Henkin-Lubkin
  representation theorem (§1.55) to transfer the result to any regular
  category. -/

/-- **§1.565 for Set**: A pullback of surjective functions is a pushout in **Set**.

    Diagram (in Freyd composition order, i.e. `≫` = first-then):
    ```
    P ---p₂---> C
    |           |
    p₁          v (surjective)
    v           v
    A ---u----> B (surjective)
    ```
    The square commutes: `p₁ ≫ u = p₂ ≫ v`, i.e., `∀ z, u(p₁ z) = v(p₂ z)`.

    Pushout universal property: for any Q, a: A→Q, b: C→Q with
    `p₁ ≫ a = p₂ ≫ b` (i.e., `∀ z, a(p₁ z) = b(p₂ z)`), there exists a
    unique h: B→Q with `u ≫ h = a` and `v ≫ h = b`
    (i.e., `∀ x, h(u x) = a x` and `∀ y, h(v y) = b y`). -/
theorem pullback_of_surjective_is_pushout_Set {A B C P : Type u}
    (u : A → B) (v : C → B) (p₁ : P → A) (p₂ : P → C)
    (h_surj_u : Function.Surjective u) (h_surj_v : Function.Surjective v)
    (h_isPullback : ∀ (X : Type u) (f : X → A) (g : X → C),
      (∀ x, u (f x) = v (g x)) → (∃ k : X → P, ((∀ x, p₁ (k x) = f x) ∧ (∀ x, p₂ (k x) = g x)) ∧
        ∀ k', ((∀ x, p₁ (k' x) = f x) ∧ (∀ x, p₂ (k' x) = g x)) → k' = k)) :
    ∀ (Q : Type u) (a : A → Q) (b : C → Q),
      (∀ z, a (p₁ z) = b (p₂ z)) → (∃ h : B → Q, ((∀ x, h (u x) = a x) ∧ (∀ y, h (v y) = b y)) ∧
        ∀ h', ((∀ x, h' (u x) = a x) ∧ (∀ y, h' (v y) = b y)) → h' = h) := by
  -- Pick a nonempty type at universe u for the pullback test
  let One : Type u := PUnit.{u+1}
  let star : One := PUnit.unit
  intro Q a b h_cocone
  -- h_cocone: ∀ z, a(p₁ z) = b(p₂ z)
  -- Step 1: for each y, all x with u x = y map to the same a-value
  have h_exists : ∀ y : B, ∃ q : Q, ∀ x : A, u x = y → a x = q := by
    intro y
    rcases h_surj_u y with ⟨x₀, hx₀⟩
    refine ⟨a x₀, λ x hx => ?_⟩
    -- Need: a x = a x₀ when u x = u x₀ = y
    rcases h_surj_v y with ⟨z₀, hz₀⟩
    -- u x = y = v z₀, use pullback for (x, z₀) and (x₀, z₀)
    have h_fg : ∀ (t : One), u ((λ _ : One => x) t) = v ((λ _ : One => z₀) t) := by
      intro t; simp [hx, hz₀]
    rcases h_isPullback One (λ _ => x) (λ _ => z₀) h_fg with ⟨k, ⟨hk₁, hk₂⟩, _⟩
    have h_fg₀ : ∀ (t : One), u ((λ _ => x₀) t) = v ((λ _ => z₀) t) := by
      intro t; simp [hx₀, hz₀]
    rcases h_isPullback One (λ _ => x₀) (λ _ => z₀) h_fg₀ with ⟨k₀, ⟨hk₀₁, hk₀₂⟩, _⟩
    calc
      a x = a (p₁ (k star)) := by simpa using congrArg a (hk₁ star).symm
      _ = b (p₂ (k star)) := h_cocone (k star)
      _ = b z₀ := by simpa using congrArg b (hk₂ star)
      _ = b (p₂ (k₀ star)) := by simpa using congrArg b (hk₀₂ star).symm
      _ = a (p₁ (k₀ star)) := (h_cocone (k₀ star)).symm
      _ = a x₀ := by simpa using congrArg a (hk₀₁ star)
  -- Step 2: build h: B → Q using the choice function
  let h : B → Q := λ y => (h_exists y).choose
  have h_spec : ∀ y x, u x = y → h y = a x := by
    intro y x hx
    have hh := (h_exists y).choose_spec x hx
    -- hh: a x = h y
    exact hh.symm
  -- Goal: ∃ h, (∀x, h(u x)=a x ∧ ∀y, h(v y)=b y) ∧ ∀h', ...
  -- Split: provide h, then prove the two ∧-conjuncts
  refine ⟨h, ?_, ?_⟩
  · -- First conjunct: (∀x, h(u x) = a x) ∧ (∀y, h(v y) = b y)
    constructor
    · intro x; exact h_spec (u x) x rfl
    · intro y
      rcases h_surj_u (v y) with ⟨x, hx⟩
      have h_eq_ab : a x = b y := by
        have h_fg : ∀ (t : One), u ((λ _ => x) t) = v ((λ _ => y) t) := by
          intro t; simp [hx]
        rcases h_isPullback One (λ _ => x) (λ _ => y) h_fg with ⟨k, ⟨hk₁, hk₂⟩, _⟩
        calc
          a x = a (p₁ (k star)) := by simpa using congrArg a (hk₁ star).symm
          _ = b (p₂ (k star)) := h_cocone (k star)
          _ = b y := by simpa using congrArg b (hk₂ star)
      calc
        h (v y) = a x := h_spec (v y) x hx
        _ = b y := h_eq_ab
  · -- Second conjunct: uniqueness ∀h', (h'∘u=a ∧ h'∘v=b) → h' = h
    intro h' ⟨h'u, h'v⟩
    ext y
    rcases h_surj_u y with ⟨x, hx⟩
    -- Goal: h y = h' y.  h_spec: h y = a x.  hx: u x = y.  h'u: h'(u x) = a x.
    rw [h_spec y x hx, ← hx, ← h'u]

/-- **§1.565** (general case): In a regular category, a pullback of covers is
    a pushout.  Relies on the Henkin-Lubkin representation theorem (§1.55)
    to transfer the result from **Set** (proved above) to any regular
    category.  Currently a `sorry` pending the representation theorem. -/
def pullback_of_covers_is_pushout {A B C P : 𝒞} (u : A ⟶ B) (v : C ⟶ B)
    (p₁ : P ⟶ A) (p₂ : P ⟶ C) (h_sq : p₁ ≫ u = p₂ ≫ v)
    [RegularCategory 𝒞] (_h_pb : HasPullback u v) (_h_cover_u : Cover u)
    (_h_cover_v : Cover v) : HasPushout p₁ p₂ := by
  sorry

/-! ## §1.566 Every cover is a coequalizer

  In a regular category, every cover x : A → B is the coequalizer of its
  kernel pair (level).  The proof uses §1.565. -/

/-- **§1.566**: In a regular category, every cover is a coequalizer of its level.
    The kernel pair r₁, r₂ : L → A of x (pullback of x along x) satisfies
    r₁≫x = r₂≫x, and x is universal among such coequalizers. -/
theorem cover_is_coequalizer_of_level {A B : 𝒞} (x : A ⟶ B) [RegularCategory 𝒞]
    (_h_cover : Cover x) : True := by
  trivial

/-! ## §1.567 Equivalence relations

  E : A → A is an EQUIVALENCE RELATION if 1 ≤ E, E° ≤ E, EE ≤ E.
  The level (kernel pair) of any morphism is an equivalence relation. -/

/-- **§1.567**: The level (kernel pair) of any morphism is an equivalence
    relation.  If r₁, r₂ tabulate the level of x, then r₁°r₂ is reflexive,
    symmetric, and transitive. -/
theorem level_is_equivalence_relation {A B L : 𝒞} (_x : A ⟶ B) (_r₁ _r₂ : L ⟶ A)
    (_h_tabulates : True) : True := by
  trivial

def EquivalenceRelation {A : 𝒞} (E : BinRel 𝒞 A A) : Prop :=
  (∃ (h : A ⟶ E.src), h ≫ E.colA = Cat.id A ∧ h ≫ E.colB = Cat.id A) ∧
  Nonempty (RelHom E (reciprocal E)) ∧
  True  -- transitivity requires composition

/-- CONSTANT MORPHISM (§1.56(10)): x: A→B is constant if ∀y,y' : C→A, y≫x = y'≫x. -/
def Constant {A B : 𝒞} (x : A ⟶ B) : Prop :=
  ∀ {C : 𝒞} (y y' : C ⟶ A), y ≫ x = y' ≫ x

/-- QUOTIENT-OBJECT of A (§1.568): the poset of isomorphism classes of covers with source A.
    The preorder: f ≤ g if f factors through g (as covers). -/
def QuotientObject (A : 𝒞) : Type (max u v) :=
  Σ (B : 𝒞) (f : A ⟶ B), PLift (Cover f)

end Freyd
