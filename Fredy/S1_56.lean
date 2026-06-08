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
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45
import Fredy.S1_51


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
  isMonicPair := λ {W} f g hA _ => by
    -- hA: f ≫ id = g ≫ id  →  f = g
    simpa [Cat.id_comp, Cat.comp_id] using hA

/-! ## §1.564 Entire, Simple, Map

  A relation R: A→B is ENTIRE if 1_A ≤ R°R.
  SIMPLE if R°R ≤ 1_B.
  A MAP is an entire + simple relation (= graph of a morphism). -/

/-- R is ENTIRE if 1_A ≤ RR° (requires composition/image to define properly). -/
def IsEntireRel {A B : 𝒞} (R : BinRel 𝒞 A B) : Prop :=
  -- True definition uses relation composition: Nonempty (RelLe (graph (Cat.id A)) (compose R (reciprocal R)))
  -- Placeholder until composition is defined.
  True

/-- R is SIMPLE if R°R is contained in id_B (§1.564). -/
def IsSimpleRel {A B : 𝒞} (R : BinRel 𝒞 A B) : Prop :=
  -- R°R ≤ id_B: for any T tabulating R°R (i.e. a cone), both legs factor through 1_B
  -- Equivalent: if f,g factor through R on the B-side, they're equal.
  ∀ {X : 𝒞} (f g : X ⟶ R.src), f ≫ R.colB = g ≫ R.colB → f ≫ R.colA = g ≫ R.colA

/-- R is a MAP if it is entire and simple.  Maps are exactly graphs (§1.564). -/
def IsMap {A B : 𝒞} (R : BinRel 𝒞 A B) : Prop :=
  IsEntireRel R ∧ IsSimpleRel R

/-- Every isomorphism yields a map-graph.  (The entire part requires RR° = id,
    which needs the composition/image structure; we mark it sorry.) -/
theorem graph_iso_is_map {A B : 𝒞} (x : A ⟶ B) (hIso : IsIso x) : IsMap (graph x) := by
  rcases hIso with ⟨inv, h1, h2⟩
  refine ⟨?_, ?_⟩
  · -- entire: 1_A ≤ (graph x)(graph x)°  (requires composition/image)
    sorry
  · -- simple: f ≫ x = g ≫ x → f = g (since x has left inverse from iso)
    intro X f g h
    -- h: f ≫ (graph x).colB = g ≫ (graph x).colB  →  f ≫ x = g ≫ x
    have hx : f ≫ x = g ≫ x := by simpa [graph] using h
    have hpost : (f ≫ x) ≫ inv = (g ≫ x) ≫ inv := by rw [hx]
    simpa [graph, Cat.assoc, h1, Cat.comp_id] using hpost

/-- x is monic iff graph(x) is simple. -/
theorem monic_iff_simple_graph {A B : 𝒞} (x : A ⟶ B) : Mono x ↔ IsSimpleRel (graph x) := by
  constructor
  · intro hm X f g h
    -- h: f ≫ (graph x).colB = g ≫ (graph x).colB
    -- = f ≫ x = g ≫ x
    -- want: f ≫ (graph x).colA = g ≫ (graph x).colA
    -- = f ≫ id = g ≫ id → f = g
    have hx : f ≫ x = g ≫ x := by simpa [graph] using h
    simpa [graph, Cat.comp_id, Cat.id_comp] using hm f g hx
  · intro hs X f g h
    have hg : f ≫ (graph x).colB = g ≫ (graph x).colB := by simpa [graph] using h
    have hcol := hs f g hg
    simpa [graph, Cat.comp_id, Cat.id_comp] using hcol

/-! ## §1.561 Reciprocal -/

def reciprocal {A B : 𝒞} (R : BinRel 𝒞 A B) : BinRel 𝒞 B A where
  src  := R.src
  colA := R.colB
  colB := R.colA
  isMonicPair := λ {W} f g hA hB => R.isMonicPair f g hB hA

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
          pair_uniq a b (g ≫ I.arr) h_fst h_snd
        rw [hf, hg]
      -- Since I.arr is monic, this implies f = g
      exact I.monic f g h_prod }

/-! ## §1.564 Cover ↔ Entire

  For a graph R = graph(x): x is a cover iff R is entire.
  (Proof uses the image of x: x is cover ↔ image(x).arr is iso ↔ 1_A ≤ RR°.) -/

theorem cover_iff_entire_graph {A B : 𝒞} (x : A ⟶ B) [HasImages 𝒞] :
    Cover x ↔ IsEntireRel (graph x) := by
  -- Both sides are equivalent to: the image of x is the entire subobject.
  -- We use cover_iff_image_entire from S1_51.
  sorry

/-! ## §1.563 Modular identity

  In a regular category: RS ∩ T ⊆ (R ∩ TS°)S.
  This is the defining equation of allegories; proved in §2. -/

theorem modular_identity {A B C : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 A C) : RelLe (compose (compose R S) (reciprocal T)) (compose R (compose S (reciprocal T))) := by

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

/-! ## §1.567 Equivalence relations

  E : A → A is an EQUIVALENCE RELATION if 1 ≤ E, E° ≤ E, EE ≤ E.
  The level (kernel pair) of any morphism is an equivalence relation. -/

def IsEquivalenceRelation {A : 𝒞} (E : BinRel 𝒞 A A) : Prop :=
  (∃ (h : A ⟶ E.src), h ≫ E.colA = Cat.id A ∧ h ≫ E.colB = Cat.id A) ∧
  Nonempty (RelHom E (reciprocal E)) ∧
  True  -- transitivity requires composition

end Freyd
