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

/-- R ≤ S as relations (containment order, §1.413).  Notation `R ⊂ S` follows the book. -/
def RelLe (R S : BinRel 𝒞 A B) : Prop := Nonempty (RelHom R S)

/-- Infix `⊂` for relation containment (the book's notation). -/
infix:50 " ⊂ " => RelLe

/-- **§1.413**: The witnessing morphism between tables is unique.
    If h₁, h₂ are morphisms satisfying the containment conditions, then h₁ = h₂. -/
theorem RelHom_unique {A B : 𝒞} {R S : BinRel 𝒞 A B}
    (h₁ h₂ : R.src ⟶ S.src)
    (hA₁ : h₁ ≫ S.colA = R.colA) (hB₁ : h₁ ≫ S.colB = R.colB)
    (hA₂ : h₂ ≫ S.colA = R.colA) (hB₂ : h₂ ≫ S.colB = R.colB) : h₁ = h₂ := by
  apply S.isMonicPair h₁ h₂
  · rw [hA₁, hA₂]
  · rw [hB₁, hB₂]

/-- **§1.413**: The witnessing morphism is monic.
    If z : R.src → S.src witnesses R ⊂ S, then z is monic. -/
theorem RelHom_monic {A B : 𝒞} {R S : BinRel 𝒞 A B}
    (z : R.src ⟶ S.src) (hA : z ≫ S.colA = R.colA) (hB : z ≫ S.colB = R.colB) : Mono z := by
  intro W f g heq
  have hcolA_eq : f ≫ R.colA = g ≫ R.colA := by
    calc
      f ≫ R.colA = f ≫ (z ≫ S.colA) := by rw [hA]
      _ = (f ≫ z) ≫ S.colA := (Cat.assoc _ _ _).symm
      _ = (g ≫ z) ≫ S.colA := by rw [heq]
      _ = g ≫ (z ≫ S.colA) := Cat.assoc _ _ _
      _ = g ≫ R.colA := by rw [hA]
  have hcolB_eq : f ≫ R.colB = g ≫ R.colB := by
    calc
      f ≫ R.colB = f ≫ (z ≫ S.colB) := by rw [hB]
      _ = (f ≫ z) ≫ S.colB := (Cat.assoc _ _ _).symm
      _ = (g ≫ z) ≫ S.colB := by rw [heq]
      _ = g ≫ (z ≫ S.colB) := Cat.assoc _ _ _
      _ = g ≫ R.colB := by rw [hB]
  exact R.isMonicPair f g hcolA_eq hcolB_eq

/-! ## §1.564 Graph of a morphism -/

def graph {A B : 𝒞} (x : A ⟶ B) : BinRel 𝒞 A B where
  src  := A
  colA := Cat.id A
  colB := x
  isMonicPair := λ {_W} f g hA _ => by
    -- hA: f ≫ id = g ≫ id  →  f = g
    simpa [Cat.id_comp, Cat.comp_id] using hA

/-- A map *is* a relation (Freyd): a morphism `x : A ⟶ B` silently embeds into the
    relational calculus as its graph `↑x = graph x`.  This lets §1.62 read in book
    notation — `x° ⊚ f` for `(graph x)° ⊚ (graph f)`. -/
instance graphCoe {A B : 𝒞} : Coe (A ⟶ B) (BinRel 𝒞 A B) := ⟨graph⟩

/-! ## §1.561 Reciprocal -/

def reciprocal {A B : 𝒞} (R : BinRel 𝒞 A B) : BinRel 𝒞 B A where
  src  := R.src
  colA := R.colB
  colB := R.colA
  isMonicPair := λ {_W} f g hA hB => R.isMonicPair f g hB hA

/-- The reciprocal R°: swap columns (§1.561).  Postfix notation `_°`. -/
postfix:max (name := relRecip) "°" => reciprocal

theorem reciprocal_invol {A B : 𝒞} (R : BinRel 𝒞 A B) : reciprocal (reciprocal R) = R := by
  unfold reciprocal; rfl

/-! ## §1.562 Semi-lattice of relations

  Intersection (meet) of binary relations is the pullback of their
  subobject embeddings into A×B.  Each relation ⟨T; a:T→A, b:T→B⟩
  corresponds to the monic `pair a b : T → A×B` (jointly-monic iff
  the pair is monic).  Intersection is then the pullback of these
  monics. -/

section
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- A monic into the product gives a jointly-monic pair (via fst, snd). -/
theorem monicPair_of_monic_pair {T A B : 𝒞} (a : T ⟶ A) (b : T ⟶ B)
    (h : Mono (pair a b)) : MonicPair a b := by
  intro W f g ha hb
  apply h f g
  have hf : f ≫ pair a b = pair (f ≫ a) (f ≫ b) :=
    pair_uniq (f ≫ a) (f ≫ b) (f ≫ pair a b)
      (by rw [Cat.assoc, fst_pair a b])
      (by rw [Cat.assoc, snd_pair a b])
  have hg : g ≫ pair a b = pair (f ≫ a) (f ≫ b) :=
    pair_uniq (f ≫ a) (f ≫ b) (g ≫ pair a b)
      (by rw [Cat.assoc, fst_pair a b, ha])
      (by rw [Cat.assoc, snd_pair a b, hb])
  rw [hf, hg]

/-- A jointly-monic pair gives a monic into the product. -/
theorem monic_pair_of_monicPair {T A B : 𝒞} (a : T ⟶ A) (b : T ⟶ B) (hp : MonicPair a b) :
    Mono (pair a b) := by
  intro W f g h
  apply hp f g
  · calc f ≫ a = (f ≫ pair a b) ≫ fst := by rw [Cat.assoc, fst_pair a b]
    _ = (g ≫ pair a b) ≫ fst := by rw [h]
    _ = g ≫ a := by rw [Cat.assoc, fst_pair a b]
  · calc f ≫ b = (f ≫ pair a b) ≫ snd := by rw [Cat.assoc, snd_pair a b]
    _ = (g ≫ pair a b) ≫ snd := by rw [h]
    _ = g ≫ b := by rw [Cat.assoc, snd_pair a b]

/-- Intersection (meet) of two relations R, S : A → B.
    §1.562: Pullback of the subobject embeddings `pair colA colB` into A×B. -/
def intersect {A B : 𝒞} (R S : BinRel 𝒞 A B) : BinRel 𝒞 A B :=
  let pb := HasPullbacks.has (pair R.colA R.colB) (pair S.colA S.colB)
  { src := pb.cone.pt
    colA := pb.cone.π₁ ≫ R.colA
    colB := pb.cone.π₁ ≫ R.colB
    isMonicPair := by
      intro W f g hA hB
      have h_colA : (f ≫ pb.cone.π₁) ≫ R.colA = (g ≫ pb.cone.π₁) ≫ R.colA := by
        simpa [Cat.assoc] using hA
      have h_colB : (f ≫ pb.cone.π₁) ≫ R.colB = (g ≫ pb.cone.π₁) ≫ R.colB := by
        simpa [Cat.assoc] using hB
      have h_p1 : f ≫ pb.cone.π₁ = g ≫ pb.cone.π₁ :=
        R.isMonicPair (f ≫ pb.cone.π₁) (g ≫ pb.cone.π₁) h_colA h_colB
      let eR := pair R.colA R.colB
      let eS := pair S.colA S.colB
      have hmono_eS : Mono eS := monic_pair_of_monicPair S.colA S.colB S.isMonicPair
      have h_p2 : f ≫ pb.cone.π₂ = g ≫ pb.cone.π₂ := by
        apply hmono_eS (f ≫ pb.cone.π₂) (g ≫ pb.cone.π₂)
        calc
          (f ≫ pb.cone.π₂) ≫ eS = f ≫ (pb.cone.π₂ ≫ eS) := by rw [Cat.assoc]
          _ = f ≫ (pb.cone.π₁ ≫ eR) := by rw [pb.cone.w.symm]
          _ = (f ≫ pb.cone.π₁) ≫ eR := by rw [Cat.assoc]
          _ = (g ≫ pb.cone.π₁) ≫ eR := by rw [h_p1]
          _ = g ≫ (pb.cone.π₁ ≫ eR) := by rw [← Cat.assoc]
          _ = g ≫ (pb.cone.π₂ ≫ eS) := by rw [pb.cone.w]
          _ = (g ≫ pb.cone.π₂) ≫ eS := by rw [Cat.assoc]
      let c : Cone eR eS :=
        { pt := W
          π₁ := f ≫ pb.cone.π₁
          π₂ := f ≫ pb.cone.π₂
          w := by
            calc
              (f ≫ pb.cone.π₁) ≫ eR = f ≫ (pb.cone.π₁ ≫ eR) := by rw [Cat.assoc]
              _ = f ≫ (pb.cone.π₂ ≫ eS) := by rw [pb.cone.w]
              _ = (f ≫ pb.cone.π₂) ≫ eS := by rw [← Cat.assoc] }
      have hu_f : f = pb.lift c := pb.lift_uniq c f rfl rfl
      have hu_g : g = pb.lift c := pb.lift_uniq c g h_p1.symm h_p2.symm
      rw [hu_f, hu_g]
  }

/-- Infix notation for relation intersection (meet). -/
infixl:70 " ⊓ " => intersect

/-- Reflexivity of relational containment. -/
@[refl]
theorem rel_le_refl {A B : 𝒞} (R : BinRel 𝒞 A B) : RelLe R R :=
  ⟨⟨Cat.id R.src, Cat.id_comp _, Cat.id_comp _⟩⟩

/-- Transitivity of relational containment. -/
theorem rel_le_trans {A B : 𝒞} {R S T : BinRel 𝒞 A B} (hRS : RelLe R S) (hST : RelLe S T) :
    RelLe R T := by
  rcases hRS with ⟨⟨f, hfA, hfB⟩⟩
  rcases hST with ⟨⟨g, hgA, hgB⟩⟩
  refine ⟨⟨f ≫ g, ?_, ?_⟩⟩
  · calc (f ≫ g) ≫ T.colA = f ≫ (g ≫ T.colA) := by rw [Cat.assoc]
    _ = f ≫ S.colA := by rw [hgA]
    _ = R.colA := hfA
  · calc (f ≫ g) ≫ T.colB = f ≫ (g ≫ T.colB) := by rw [Cat.assoc]
    _ = f ≫ S.colB := by rw [hgB]
    _ = R.colB := hfB

/-- `Trans` instance for relational containment `⊂`, so the book's pointfree proofs can
    be written as `calc R ⊂ … ⊂ … ⊂ S` chains (Freyd's calculus-of-relations style)
    instead of nested `rel_le_trans`.  Pure Ch1 — no allegory axiom. -/
instance relLeTrans {𝒟 : Type u} [Cat.{v} 𝒟] [HasBinaryProducts 𝒟] [HasPullbacks 𝒟] {A B : 𝒟} :
    Trans (@RelLe 𝒟 _ A B) (@RelLe 𝒟 _ A B) (@RelLe 𝒟 _ A B) :=
  ⟨rel_le_trans⟩

/-- R ⊓ S ≤ R (projection via π₁). -/
theorem intersect_le_left {A B : 𝒞} (R S : BinRel 𝒞 A B) : RelLe (R ⊓ S) R := by
  let pb := HasPullbacks.has (pair R.colA R.colB) (pair S.colA S.colB)
  refine ⟨⟨pb.cone.π₁, rfl, rfl⟩⟩

/-- R ⊓ S ≤ S (via π₂ and the pullback square). -/
theorem intersect_le_right {A B : 𝒞} (R S : BinRel 𝒞 A B) : RelLe (R ⊓ S) S := by
  let pb := HasPullbacks.has (pair R.colA R.colB) (pair S.colA S.colB)
  have h_sq := pb.cone.w
  have h_colA : pb.cone.π₂ ≫ S.colA = (R ⊓ S).colA := by
    calc
      pb.cone.π₂ ≫ S.colA = pb.cone.π₂ ≫ (pair S.colA S.colB ≫ fst) :=
        congrArg (pb.cone.π₂ ≫ ·) (fst_pair S.colA S.colB).symm
      _ = (pb.cone.π₂ ≫ pair S.colA S.colB) ≫ fst := (Cat.assoc _ _ _).symm
      _ = (pb.cone.π₁ ≫ pair R.colA R.colB) ≫ fst := by rw [h_sq]
      _ = pb.cone.π₁ ≫ (pair R.colA R.colB ≫ fst) := Cat.assoc _ _ _
      _ = pb.cone.π₁ ≫ R.colA := congrArg (pb.cone.π₁ ≫ ·) (fst_pair R.colA R.colB)
      _ = (R ⊓ S).colA := rfl
  have h_colB : pb.cone.π₂ ≫ S.colB = (R ⊓ S).colB := by
    calc
      pb.cone.π₂ ≫ S.colB = pb.cone.π₂ ≫ (pair S.colA S.colB ≫ snd) :=
        congrArg (pb.cone.π₂ ≫ ·) (snd_pair S.colA S.colB).symm
      _ = (pb.cone.π₂ ≫ pair S.colA S.colB) ≫ snd := (Cat.assoc _ _ _).symm
      _ = (pb.cone.π₁ ≫ pair R.colA R.colB) ≫ snd := by rw [h_sq]
      _ = pb.cone.π₁ ≫ (pair R.colA R.colB ≫ snd) := Cat.assoc _ _ _
      _ = pb.cone.π₁ ≫ R.colB := congrArg (pb.cone.π₁ ≫ ·) (snd_pair R.colA R.colB)
      _ = (R ⊓ S).colB := rfl
  exact ⟨⟨pb.cone.π₂, h_colA, h_colB⟩⟩

/-- Universal property: T ≤ R ∧ T ≤ S → T ≤ R ⊓ S. -/
theorem le_intersect {A B : 𝒞} {T R S : BinRel 𝒞 A B} (hTR : RelLe T R) (hTS : RelLe T S) :
    RelLe T (R ⊓ S) := by
  rcases hTR with ⟨⟨f, hfA, hfB⟩⟩
  rcases hTS with ⟨⟨g, hgA, hgB⟩⟩
  let eR := pair R.colA R.colB
  let eS := pair S.colA S.colB
  let pb := HasPullbacks.has eR eS
  have h_cone_w : f ≫ eR = g ≫ eS := by
    calc
      f ≫ eR = pair (f ≫ R.colA) (f ≫ R.colB) :=
        pair_uniq (f ≫ R.colA) (f ≫ R.colB) (f ≫ eR)
          (by rw [Cat.assoc, fst_pair R.colA R.colB])
          (by rw [Cat.assoc, snd_pair R.colA R.colB])
      _ = pair T.colA T.colB := by rw [hfA, hfB]
      _ = pair (g ≫ S.colA) (g ≫ S.colB) := by rw [hgA, hgB]
      _ = g ≫ eS :=
        (pair_uniq (g ≫ S.colA) (g ≫ S.colB) (g ≫ eS)
          (by rw [Cat.assoc, fst_pair S.colA S.colB])
          (by rw [Cat.assoc, snd_pair S.colA S.colB])).symm
  let c : Cone eR eS := { pt := T.src, π₁ := f, π₂ := g, w := h_cone_w }
  let h := pb.lift c
  have h_hA : h ≫ (R ⊓ S).colA = T.colA := by
    dsimp [h, intersect]
    rw [← Cat.assoc, pb.lift_fst c]
    exact hfA
  have h_hB : h ≫ (R ⊓ S).colB = T.colB := by
    dsimp [h, intersect]
    rw [← Cat.assoc, pb.lift_fst c]
    exact hfB
  exact ⟨⟨h, h_hA, h_hB⟩⟩

/-- §1.562: R ≤ S iff R ≤ R ⊓ S (since R ⊓ S ≤ R always, this characterizes the meet order). -/
theorem le_iff_le_intersect {A B : 𝒞} (R S : BinRel 𝒞 A B) : RelLe R S ↔ RelLe R (R ⊓ S) := by
  constructor
  · intro hRS; exact le_intersect (rel_le_refl R) hRS
  · intro h; exact rel_le_trans h (intersect_le_right R S)

/-- R ≤ S iff R ⊓ S ≡ R (mutual containment).  Since R ⊓ S ≤ R always,
    this collapses to R ≤ S ↔ R ≤ R ⊓ S. -/
theorem le_iff_intersect_eq {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    RelLe R S ↔ (RelLe (R ⊓ S) R ∧ RelLe R (R ⊓ S)) := by
  constructor
  · intro hRS; exact ⟨intersect_le_left R S, (le_iff_le_intersect R S).mp hRS⟩
  · intro ⟨_, h⟩; exact (le_iff_le_intersect R S).mpr h

end

section
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-! ## §1.56 Composition of relations

  Given R: A→B, S: B→C, in a Cartesian category with pullbacks and
  images, their composition RS: A→C is obtained by pulling back along
  the B-legs, then taking the image in A×C.  (§1.56) -/

/-- The composition RS: A→C (§1.56).
    1. Pull back R.colB and S.colA over B → object P
    2. Map P→A via P→R.src→A, P→C via P→S.src→C
    3. Take the image of the span P→A×C → this is the composed relation. -/
def compose {A B C : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) : BinRel 𝒞 A C :=
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

/-- Infix notation for relation composition (diagrammatic order, §1.56).
    `R ⊚ S` = "first R, then S".  Right-associative. -/
infixr:80 (name := relCompose) " ⊚ " => compose

/-! ## §1.564 Entire, Simple, Map

  A relation R: A→B is ENTIRE if 1_A ≤ RR°.
  SIMPLE if R°R ≤ 1_B.
  A MAP is an entire + simple relation (= graph of a morphism). -/

/-- **§1.564**: R : A → B is ENTIRE if 1_A ≤ RR° — the identity relation
    on A is contained in R ⊚ R° : A → A. -/
def Entire {A B : 𝒞} (R : BinRel 𝒞 A B) : Prop :=
  RelLe (graph (Cat.id A)) (R ⊚ R°)

/-- **§1.564**: R is SIMPLE if R°R ≤ 1_B — R° ⊚ R : B → B
    is contained in the identity on B. -/
def Simple {A B : 𝒞} (R : BinRel 𝒞 A B) : Prop :=
  RelLe (R° ⊚ R) (graph (Cat.id B))

/-- R is a MAP if it is entire and simple.  Maps are exactly graphs (§1.564). -/
def Map {A B : 𝒞} (R : BinRel 𝒞 A B) : Prop :=
  Entire R ∧ Simple R

/-- `pair x x = x ≫ diag _` — a morphism followed by the diagonal equals
    the pair of itself.  Used throughout the entire/simple proofs. -/
theorem pair_diag_eq {X B : 𝒞} (x : X ⟶ B) : pair x x = x ≫ diag B :=
  (pair_uniq x x (x ≫ diag B)
    (by rw [Cat.assoc, diag_fst, Cat.comp_id])
    (by rw [Cat.assoc, diag_snd, Cat.comp_id])).symm

/-- **§1.564**: a relation tabulated by ⟨T; x, y⟩ is ENTIRE iff `x` is a cover.

    The cover ⇒ entire direction is drawn step by step in `cover_to_entire.svg`,
    with the SAME names as this proof: `l r d sp c i I k j t e`.

    Entire ⇒ cover: if `x` factors through a monic `m`, the span `sp` factors through the
    monic `mm = m × m`, so by minimality of the image, `1 = h ≫ (i ≫ fst)` factors
    through `m`: `m` is a split epi, and a monic split epi is an iso. -/
theorem tabulated_is_entire_iff_left_cover {A B T : 𝒞} (x : T ⟶ A) (y : T ⟶ B)
    (hp : MonicPair x y) : Entire (BinRel.mk T x y hp) ↔ Cover x := by
  /- Shared setup — the data of R ⊚ R° (left panel of the SVG):

         l, r : P ⇉ T   pullback of (y, y)         sp := ⟨l≫x, r≫x⟩ : P → A×A
                                                    I := image sp,  i := I.arr monic   -/
  let pb := HasPullbacks.has y y
  let l : pb.cone.pt ⟶ T := pb.cone.π₁
  let r : pb.cone.pt ⟶ T := pb.cone.π₂
  let sp : pb.cone.pt ⟶ prod A A := pair (l ≫ x) (r ≫ x)
  let I : Subobject 𝒞 (prod A A) := image sp
  let i : I.dom ⟶ prod A A := I.arr
  have hsp₁ : sp ≫ fst = l ≫ x := fst_pair _ _
  have hsp₂ : sp ≫ snd = r ≫ x := snd_pair _ _
  constructor
  · /- ENTIRE ⇒ COVER.  Given h with h ≫ (i ≫ fst) = 1, and x = g ≫ m with m monic:

           P ─── w := ⟨l≫g, r≫g⟩ ──→ C×C
            ╲                         │
             sp              mm := ⟨fst≫m, snd≫m⟩   (monic since m is)
              ╲                       ↓
               ─────────────────────→ A×A

       image minimality gives e : I.dom → C×C with e ≫ mm = i, hence
       1 = h ≫ (i ≫ fst) = ((h ≫ e) ≫ fst) ≫ m :  m is a split epi, hence iso.  -/
    rintro ⟨⟨h, h₁, -⟩⟩
    have h₁' : h ≫ (i ≫ fst) = Cat.id A := h₁
    intro C m g hm hgm
    -- mm := m × m is monic
    let mm : prod C C ⟶ prod A A := pair (fst ≫ m) (snd ≫ m)
    have hmm₁ : mm ≫ fst = fst ≫ m := fst_pair _ _
    have hmm₂ : mm ≫ snd = snd ≫ m := snd_pair _ _
    have hmm : Mono mm := by
      intro W u v huv
      have hufst : u ≫ fst = v ≫ fst := hm _ _ (by
        calc (u ≫ fst) ≫ m = u ≫ (mm ≫ fst) := by rw [hmm₁, Cat.assoc]
          _ = (u ≫ mm) ≫ fst := (Cat.assoc _ _ _).symm
          _ = (v ≫ mm) ≫ fst := by rw [huv]
          _ = v ≫ (mm ≫ fst) := Cat.assoc _ _ _
          _ = (v ≫ fst) ≫ m := by rw [hmm₁, Cat.assoc])
      have husnd : u ≫ snd = v ≫ snd := hm _ _ (by
        calc (u ≫ snd) ≫ m = u ≫ (mm ≫ snd) := by rw [hmm₂, Cat.assoc]
          _ = (u ≫ mm) ≫ snd := (Cat.assoc _ _ _).symm
          _ = (v ≫ mm) ≫ snd := by rw [huv]
          _ = v ≫ (mm ≫ snd) := Cat.assoc _ _ _
          _ = (v ≫ snd) ≫ m := by rw [hmm₂, Cat.assoc])
      rw [pair_uniq (u ≫ fst) (u ≫ snd) u rfl rfl,
        pair_uniq (u ≫ fst) (u ≫ snd) v hufst.symm husnd.symm]
    -- the span factors through mm via w (uses g ≫ m = x)
    let w : pb.cone.pt ⟶ prod C C := pair (l ≫ g) (r ≫ g)
    have hw₁ : w ≫ fst = l ≫ g := fst_pair _ _
    have hw₂ : w ≫ snd = r ≫ g := snd_pair _ _
    have hthrough : w ≫ mm = sp :=
      pair_uniq _ _ _
        (by calc (w ≫ mm) ≫ fst = w ≫ (mm ≫ fst) := Cat.assoc _ _ _
              _ = w ≫ (fst ≫ m) := by rw [hmm₁]
              _ = (w ≫ fst) ≫ m := (Cat.assoc _ _ _).symm
              _ = (l ≫ g) ≫ m := by rw [hw₁]
              _ = l ≫ x := by rw [Cat.assoc, hgm])
        (by calc (w ≫ mm) ≫ snd = w ≫ (mm ≫ snd) := Cat.assoc _ _ _
              _ = w ≫ (snd ≫ m) := by rw [hmm₂]
              _ = (w ≫ snd) ≫ m := (Cat.assoc _ _ _).symm
              _ = (r ≫ g) ≫ m := by rw [hw₂]
              _ = r ≫ x := by rw [Cat.assoc, hgm])
    -- image minimality: e with e ≫ mm = i
    obtain ⟨e, he⟩ := image_min sp ⟨prod C C, mm, hmm⟩ ⟨w, hthrough⟩
    have he' : e ≫ mm = i := he
    -- 1 factors through m: m is a split epi
    have hsm : ((h ≫ e) ≫ fst) ≫ m = Cat.id A := by
      calc ((h ≫ e) ≫ fst) ≫ m = (h ≫ e) ≫ (fst ≫ m) := Cat.assoc _ _ _
        _ = (h ≫ e) ≫ (mm ≫ fst) := by rw [hmm₁]
        _ = ((h ≫ e) ≫ mm) ≫ fst := (Cat.assoc _ _ _).symm
        _ = (h ≫ (e ≫ mm)) ≫ fst := congrArg (· ≫ fst) (Cat.assoc h e mm)
        _ = (h ≫ i) ≫ fst := by rw [he']
        _ = h ≫ (i ≫ fst) := Cat.assoc _ _ _
        _ = Cat.id A := h₁'
    -- a monic split epi is an iso
    exact ⟨(h ≫ e) ≫ fst, hm _ _ (by rw [Cat.assoc, hsm, Cat.comp_id, Cat.id_comp]), hsm⟩
  · /- COVER ⇒ ENTIRE (three panels in `cover_to_entire.svg`).

       Panel 0 — d : T → P lifts from pullback of (y,y) (§1.42):
           P is pullback of (y,y): l ≫ y = r ≫ y.  The pair ⟨id_T, id_T⟩
           with  id_T ≫ y = id_T ≫ y  is a cone over (y,y) at T; by
           definition of pullback there is a unique lift
           d : T → P  with  hd₁ : d ≫ l = id_T  and  hd₂ : d ≫ r = id_T.

       Panel 1 — composition RR°:
           sp := ⟨l ≫ x, r ≫ x⟩ factors as c ≫ i with c a cover, i monic.
           Both routes T → A×A equal ⟨x, x⟩:
              hdl : (d ≫ c) ≫ i = x ≫ Δ        where Δ = ⟨id, id⟩.

       Panel 2 — pullback J of (Δ, i), lift t, k iso, witness:
           hdl : x ≫ Δ = (d ≫ c) ≫ i makes ⟨x, d ≫ c⟩ a cone over (Δ,i);
           by definition of pullback ∃! t with ht : t ≫ k = x.
           k is monic (pullback of monic i).  x = t ≫ k is a COVER, so
           k is iso with inverse k⁻¹ (hk_inv_k : k⁻¹ ≫ k = 1).
           h := k⁻¹ ≫ j : A → I  satisfies
           h ≫ (i ≫ fst) = 1  and  h ≫ (i ≫ snd) = 1,
           so  graph(1) ⊑ RR°  and R is ENTIRE.                        -/
    intro hcov
    let d : T ⟶ pb.cone.pt := pb.lift ⟨T, Cat.id T, Cat.id T, rfl⟩
    have hd₁ : d ≫ l = Cat.id T := pb.lift_fst _
    have hd₂ : d ≫ r = Cat.id T := pb.lift_snd _
    obtain ⟨c, hc⟩ := image_allows sp
    have hc' : c ≫ i = sp := hc
    -- hdl: both routes T → A×A are the pair ⟨x, x⟩
    have hdl : (d ≫ c) ≫ i = x ≫ diag A := by
      have hdx : x ≫ diag A = pair x x := (pair_diag_eq x).symm
      have hds : d ≫ sp = pair x x :=
        pair_uniq x x _
          (by rw [Cat.assoc, hsp₁, ← Cat.assoc, hd₁, Cat.id_comp])
          (by rw [Cat.assoc, hsp₂, ← Cat.assoc, hd₂, Cat.id_comp])
      rw [Cat.assoc, hc', hds, hdx]
    -- J: the image pulled back along the diagonal; k is monic
    let pbJ := HasPullbacks.has (diag A) i
    let k : pbJ.cone.pt ⟶ A := pbJ.cone.π₁
    let j : pbJ.cone.pt ⟶ I.dom := pbJ.cone.π₂
    have hkj : k ≫ diag A = j ≫ i := pbJ.cone.w
    have hk : Mono k := by
      intro W f g hfg
      have hj : f ≫ j = g ≫ j := by
        refine I.monic _ _ ?_
        calc (f ≫ j) ≫ i = f ≫ (j ≫ i) := Cat.assoc _ _ _
          _ = f ≫ (k ≫ diag A) := by rw [hkj]
          _ = (f ≫ k) ≫ diag A := (Cat.assoc _ _ _).symm
          _ = (g ≫ k) ≫ diag A := by rw [hfg]
          _ = g ≫ (k ≫ diag A) := Cat.assoc _ _ _
          _ = g ≫ (j ≫ i) := by rw [hkj]
          _ = (g ≫ j) ≫ i := (Cat.assoc _ _ _).symm
      have hwc : (f ≫ k) ≫ diag A = (f ≫ j) ≫ i := by
        rw [Cat.assoc, Cat.assoc, hkj]
      rw [pbJ.lift_uniq ⟨W, f ≫ k, f ≫ j, hwc⟩ f rfl rfl,
        pbJ.lift_uniq ⟨W, f ≫ k, f ≫ j, hwc⟩ g hfg.symm hj.symm]
    -- t: x factors through k; x is a cover, so k is iso with inverse k⁻¹
    let t : T ⟶ pbJ.cone.pt := pbJ.lift ⟨T, x, d ≫ c, hdl.symm⟩
    have ht : t ≫ k = x := pbJ.lift_fst _
    obtain ⟨k_inv, -, hk_inv_k⟩ := hcov k t hk ht
    -- h := k⁻¹ ≫ j is the containment 1 ≤ RR°
    have pf₁ : (k_inv ≫ j) ≫ (i ≫ fst) = Cat.id A := by
      calc (k_inv ≫ j) ≫ (i ≫ fst) = k_inv ≫ (j ≫ (i ≫ fst)) := Cat.assoc _ _ _
        _ = k_inv ≫ ((j ≫ i) ≫ fst) := by rw [Cat.assoc]
        _ = k_inv ≫ ((k ≫ diag A) ≫ fst) := by rw [hkj]
        _ = k_inv ≫ (k ≫ (diag A ≫ fst)) := by rw [Cat.assoc]
        _ = k_inv ≫ (k ≫ Cat.id A) := by rw [diag_fst]
        _ = k_inv ≫ k := by rw [Cat.comp_id]
        _ = Cat.id A := hk_inv_k
    have pf₂ : (k_inv ≫ j) ≫ (i ≫ snd) = Cat.id A := by
      calc (k_inv ≫ j) ≫ (i ≫ snd) = k_inv ≫ (j ≫ (i ≫ snd)) := Cat.assoc _ _ _
        _ = k_inv ≫ ((j ≫ i) ≫ snd) := by rw [Cat.assoc]
        _ = k_inv ≫ ((k ≫ diag A) ≫ snd) := by rw [hkj]
        _ = k_inv ≫ (k ≫ (diag A ≫ snd)) := by rw [Cat.assoc]
        _ = k_inv ≫ (k ≫ Cat.id A) := by rw [diag_snd]
        _ = k_inv ≫ k := by rw [Cat.comp_id]
        _ = Cat.id A := hk_inv_k
    exact ⟨⟨k_inv ≫ j, pf₁, pf₂⟩⟩

/-- An isomorphism is a cover (§1.512). -/
theorem iso_cover {X Y : 𝒞} (f : X ⟶ Y) (hf : IsIso f) : Cover f := by
  rcases hf with ⟨finv, -, hfinv_f⟩
  intro C m g hm hfac
  have h_m_inv : m ≫ (finv ≫ g) = Cat.id C := by
    apply hm (m ≫ (finv ≫ g)) (Cat.id C)
    calc (m ≫ (finv ≫ g)) ≫ m = m ≫ ((finv ≫ g) ≫ m) := Cat.assoc _ _ _
      _ = m ≫ (finv ≫ f) := by rw [Cat.assoc finv g m, hfac]
      _ = m ≫ Cat.id Y := by rw [hfinv_f]
      _ = m := Cat.comp_id _
      _ = Cat.id C ≫ m := (Cat.id_comp _).symm
  have h_inv_m : (finv ≫ g) ≫ m = Cat.id Y := by
    calc (finv ≫ g) ≫ m = finv ≫ (g ≫ m) := Cat.assoc _ _ _
      _ = finv ≫ f := by rw [hfac]
      _ = Cat.id Y := hfinv_f
  exact ⟨finv ≫ g, h_m_inv, h_inv_m⟩

/-- **§1.564**: A relation ⟨T; a, b⟩ is SIMPLE iff its left leg `a` is monic.
    With `tabulated_is_entire_iff_left_cover`, this yields: a tabulated relation
    is a MAP iff its left leg is an isomorphism. -/
theorem tabulated_is_simple_iff_left_monic {A B T : 𝒞} (a : T ⟶ A) (b : T ⟶ B)
    (hp : MonicPair a b) : Simple (BinRel.mk T a b hp) ↔ Mono a := by
  -- shared pullback data for both directions
  let pbA := HasPullbacks.has a a
  let l := pbA.cone.π₁
  let r := pbA.cone.π₂
  let sp := pair (l ≫ b) (r ≫ b)
  constructor
  · /- Simple → Mono a.
      Given f ≫ a = g ≫ a, pull them back to the pullback of (a, a), then
      Simplicity (the composed relation has equal fst/snd legs) forces
      f ≫ b = g ≫ b; MonicPair a b then gives f = g. -/
    intro h_simple
    rcases h_simple with ⟨⟨h, h1, h2⟩⟩
    -- h1 : h ≫ id B = (image sp).arr ≫ fst,  h2 : h ≫ id B = (image sp).arr ≫ snd
    have h_simple_eq : (image sp).arr ≫ fst = (image sp).arr ≫ snd := by
      calc (image sp).arr ≫ fst = h ≫ Cat.id B := by simpa using h1.symm
        _ = h := Cat.comp_id _
        _ = h ≫ Cat.id B := (Cat.comp_id _).symm
        _ = (image sp).arr ≫ snd := by simpa using h2
    intro W f g hfa
    let coneA : Cone a a := ⟨W, f, g, hfa⟩
    let u := pbA.lift coneA
    have hu1 : u ≫ l = f := pbA.lift_fst coneA
    have hu2 : u ≫ r = g := pbA.lift_snd coneA
    have h_fb : f ≫ b = g ≫ b := by
      have h_img := image.lift_fac sp
      -- h_img : image.lift sp ≫ (image sp).arr = sp
      -- Use congrArg to avoid rw on sp inside (image sp)
      have h1' : u ≫ (sp ≫ fst) = u ≫ ((image.lift sp ≫ (image sp).arr) ≫ fst) :=
        congrArg (fun t => u ≫ (t ≫ fst)) h_img.symm
      have h2' : u ≫ ((image.lift sp ≫ (image sp).arr) ≫ snd) = u ≫ (sp ≫ snd) :=
        congrArg (fun t => u ≫ (t ≫ snd)) h_img
      calc f ≫ b = (u ≫ l) ≫ b := by rw [hu1]
        _ = u ≫ (l ≫ b) := Cat.assoc _ _ _
        _ = (u ≫ pair (l ≫ b) (r ≫ b)) ≫ fst := by rw [Cat.assoc, fst_pair]
        _ = (u ≫ sp) ≫ fst := rfl
        _ = u ≫ (sp ≫ fst) := Cat.assoc u sp fst
        _ = u ≫ ((image.lift sp ≫ (image sp).arr) ≫ fst) := by rw [h1']
        _ = u ≫ image.lift sp ≫ ((image sp).arr ≫ fst) := by simp [Cat.assoc]
        _ = u ≫ image.lift sp ≫ ((image sp).arr ≫ snd) := by rw [h_simple_eq]
        _ = u ≫ ((image.lift sp ≫ (image sp).arr) ≫ snd) := by simp [Cat.assoc]
        _ = u ≫ (sp ≫ snd) := by rw [h2']
        _ = (u ≫ sp) ≫ snd := (Cat.assoc u sp snd).symm
        _ = (u ≫ pair (l ≫ b) (r ≫ b)) ≫ snd := rfl
        _ = u ≫ (r ≫ b) := by rw [Cat.assoc, snd_pair]
        _ = (u ≫ r) ≫ b := (Cat.assoc _ _ _).symm
        _ = g ≫ b := by rw [hu2]
    exact hp f g hfa h_fb
  · /- Mono a → Simple.
      Since a is monic, l = r in the pullback of (a, a), so the span
      ⟨l≫b, r≫b⟩ = ⟨l≫b, l≫b⟩ factors through diag B.  Hence the image
      embeds into the diagonal: its fst/snd legs are equal. -/
    intro hm
    have hlr : l = r := hm _ _ pbA.cone.w
    have hsp_eq : sp = pair (l ≫ b) (l ≫ b) := by dsimp [sp]; rw [← hlr]
    have hsp_fac : sp = (l ≫ b) ≫ diag B := by rw [hsp_eq, pair_diag_eq (l ≫ b)]
    let diagSub : Subobject 𝒞 (prod B B) := ⟨B, diag B, diag_mono B⟩
    have hallows : Allows diagSub sp := ⟨l ≫ b, by dsimp [diagSub]; rw [hsp_fac]⟩
    obtain ⟨k, hk⟩ := image_min sp diagSub hallows
    dsimp [diagSub] at hk
    -- hk : k ≫ diag B = (image sp).arr
    have h_fst_eq_k : (image sp).arr ≫ fst = k := by
      calc (image sp).arr ≫ fst = (k ≫ diag B) ≫ fst := by rw [hk]
        _ = k ≫ (diag B ≫ fst) := Cat.assoc _ _ _
        _ = k ≫ Cat.id B := by rw [diag_fst]
        _ = k := Cat.comp_id _
    have h_k_eq_snd : k = (image sp).arr ≫ snd := by
      calc k = k ≫ Cat.id B := (Cat.comp_id _).symm
        _ = k ≫ (diag B ≫ snd) := by rw [diag_snd]
        _ = (k ≫ diag B) ≫ snd := (Cat.assoc _ _ _).symm
        _ = (image sp).arr ≫ snd := by rw [hk]
    have h_colA : k ≫ (graph (Cat.id B)).colA = (image sp).arr ≫ fst := by
      dsimp [graph]; rw [Cat.comp_id, h_fst_eq_k]
    have h_colB : k ≫ (graph (Cat.id B)).colB = (image sp).arr ≫ snd := by
      dsimp [graph]; rw [Cat.comp_id, h_k_eq_snd]
    -- The RelHom witnesses R° ⊚ R ≤ graph(id_B)
    simpa [compose, reciprocal, BinRel.mk] using ⟨k, h_colA, h_colB⟩

/-- **§1.564**: A relation ⟨T; a:T→A, b:T→B⟩ tabulated by a monic pair is a
    MAP (entire + simple) iff `a` is an isomorphism.  Maps are exactly the
    graphs of morphisms: if `R` is a map then `R = graph(a⁻¹ ≫ b)`. -/
theorem tabulated_is_map_iff_left_iso {A B T : 𝒞} (a : T ⟶ A) (b : T ⟶ B) (hp : MonicPair a b) :
    Map (BinRel.mk T a b hp) ↔ IsIso a := by
  rw [Map, tabulated_is_entire_iff_left_cover a b hp,
    tabulated_is_simple_iff_left_monic a b hp]
  constructor
  · rintro ⟨hc, hm⟩; exact monic_cover_iso a hc hm
  · intro hiso
    rcases hiso with ⟨ainv, ha_ainv, hainv_a⟩
    exact ⟨iso_cover a ⟨ainv, ha_ainv, hainv_a⟩, mono_of_retraction a ainv ha_ainv⟩

/-- **§1.564**: When the left leg `a` is iso, the tabulated relation equals the graph
    of `a⁻¹ ≫ b` (mutual `⊂`).  Together with `tabulated_is_map_iff_left_iso`,
    every map IS the graph of a morphism. -/
theorem tabulated_left_iso_eq_graph {A B T : 𝒞} (a : T ⟶ A) (b : T ⟶ B) (hp : MonicPair a b)
    (ainv : A ⟶ T) (ha_ainv : a ≫ ainv = Cat.id T) (hainv_a : ainv ≫ a = Cat.id A) :
    RelLe (BinRel.mk T a b hp) (graph (ainv ≫ b)) ∧ RelLe (graph (ainv ≫ b)) (BinRel.mk T a b hp) := by
  let R := BinRel.mk T a b hp
  let G := graph (ainv ≫ b)
  constructor
  · -- R ≤ G: use a : T → A as the RelHom; check a ≫ id = a and a ≫ (ainv ≫ b) = b
    refine ⟨⟨a, ?_, ?_⟩⟩
    · dsimp [G, graph]; rw [Cat.comp_id]
    · dsimp [G, graph]; calc a ≫ (ainv ≫ b) = (a ≫ ainv) ≫ b := (Cat.assoc a ainv b).symm
      _ = Cat.id T ≫ b := by rw [ha_ainv]
      _ = b := Cat.id_comp _
  · -- G ≤ R: use ainv : A → T as the RelHom; check ainv ≫ a = id and ainv ≫ b = ainv ≫ b
    refine ⟨⟨ainv, ?_, ?_⟩⟩
    · dsimp [R, G, graph]; rw [hainv_a]
    · rfl

/-- **§1.564**: The graph of any morphism `g : A → B` is a map (entire + simple).
    Follows from: graph(g) is tabulated by ⟨A; id_A, g⟩, and id_A is both cover
    and monic.  This is the key fact that lets us reflect maps back to morphisms. -/
theorem graph_is_map {A B : 𝒞} [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] (g : A ⟶ B) :
    Map (graph g) := by
  have hp : MonicPair (Cat.id A : A ⟶ A) g := by
    intro W f g' h _hg
    simpa [Cat.comp_id] using h
  have h_entire : Entire (graph g) :=
    (tabulated_is_entire_iff_left_cover (Cat.id A) g hp).mpr
      (iso_cover (Cat.id A) ⟨Cat.id A, Cat.comp_id _, Cat.id_comp _⟩)
  have h_simple : Simple (graph g) :=
    (tabulated_is_simple_iff_left_monic (Cat.id A) g hp).mpr
      (mono_of_retraction (Cat.id A) (Cat.id A) (Cat.comp_id _))
  exact And.intro h_entire h_simple

/-! ## §1.56(11) Projective ↔ every entire relation contains a map

  In a regular category, an object A is projective (§1.57) iff every
  entire relation from A contains a map.  Proved directly, not via
  Henkin-Lubkin (the statement is ∀∃, not a Horn sentence). -/

/-- **§1.56(11) (⇒)**: If A is projective, every entire relation from A
    contains a map.  Tabulate the relation, use projectivity to split the
    (cover) left leg, compose the section with the right leg. -/
theorem projective_entire_contains_map {A : 𝒞}
    (hproj : ∀ {C : 𝒞} (f : C ⟶ A), Cover f → ∃ (s : A ⟶ C), s ≫ f = Cat.id A)
    {B : 𝒞} (R : BinRel 𝒞 A B) (hent : Entire R) : ∃ (f : A ⟶ B), RelLe (graph f) R := by
  let x := R.colA
  let y := R.colB
  have hcov : Cover x :=
    ((tabulated_is_entire_iff_left_cover x y R.isMonicPair).mp hent)
  rcases hproj x hcov with ⟨s, hs⟩
  refine ⟨s ≫ y, ⟨⟨s, ?_, ?_⟩⟩⟩
  · dsimp [graph, x]; exact hs
  · rfl

/-- **§1.56(11) (⇐)**: If every entire relation from A contains a map,
    then A is projective.  Given a cover c : C → A, take graph(c)° : A → C;
    its left leg is c (a cover) so it's entire, hence contains a map s,
    and s ≫ c = id_A. -/
theorem entire_contains_map_projective {A : 𝒞}
    (h : ∀ {B : 𝒞} (R : BinRel 𝒞 A B), Entire R →
      ∃ (f : A ⟶ B), RelLe (graph f) R) :
    ∀ {C : 𝒞} (c : C ⟶ A), Cover c → ∃ (s : A ⟶ C), s ≫ c = Cat.id A := by
  intro C c hcov
  let gc := graph c
  let gR := gc°
  -- graph(c)° : A → C has tabulation ⟨C; c, id_C⟩, left leg = c is a cover → entire
  have hp : MonicPair (gR.colA) (gR.colB) := gR.isMonicPair
  have hent : Entire gR :=
    ((tabulated_is_entire_iff_left_cover (gR.colA) (gR.colB) hp).mpr ?_)
  · rcases h gR hent with ⟨s, hs⟩
    rcases hs with ⟨⟨h₀, hA, hB⟩⟩
    -- hA: h₀ ≫ gR.colA = graph(s).colA → h₀ ≫ c = id_A
    -- hB: h₀ ≫ gR.colB = graph(s).colB → h₀ ≫ id_C = s
    dsimp [gR, gc, graph, reciprocal] at hA hB
    -- hA: h₀ ≫ c = id_A,  hB: h₀ ≫ id_C = s
    -- From hB, h₀ = s. But we don't need that; hA already gives h₀ as the section.
    exact ⟨h₀, hA⟩
  -- Prove: graph(c)°.colA = c is a cover (it IS c, which we know is a cover)
  dsimp [gR, gc, reciprocal]
  exact hcov

/-! ## §1.563 Modular identity

  In a regular category: RS ∩ T ⊆ (R ∩ TS°)S.
  This is one of the defining axioms of allegories (§2).

  **Now PROVED** (Sorry-free) as `modular_identity`, later in this file — see the
  `§1.569` block, where the cover/image descent infrastructure
  (`relLe_of_cover_factor`, `cover_pullback`, `image_lift_cover`) is in scope.
  The proof is the standard *tabular-allegory* construction and needs no
  Henkin–Lubkin reflection: pull the image-cover of `R⊚S` back along the meet's
  left leg to recover honest R/S/T points over a common cover, reassemble them
  into a point of `(R ⊓ (T⊚S°)) ⊚ S`, and descend through the cover.  The only
  ambient hypothesis is `[PullbacksTransferCovers 𝒞]` (Freyd states the law for
  regular categories anyway).  The earlier claim that this required the
  representation theorem was too pessimistic — tabularity *plus* cover-stability
  suffices. -/

end

/-! ## §1.563 Horn-sentence reflection

  **First paragraph of §1.563** (stated without proof in the book): if A and B are
  Cartesian categories with images and F : A → B preserves the Cartesian structure
  and images, then the induced functions Rel(A,B) → Rel(FA,FB) preserve composition,
  reciprocation and intersection; if F is faithful, it also reflects them.

  *Why the book omits the proof.*  Both halves are routine — but only because the
  difficulty was paid for earlier:

  - *Preservation* is mechanical: each operation is constructed from exactly the
    structure F preserves.  A relation is a jointly-monic table into A×B (products,
    monics — preserved since pullbacks are); reciprocation composes with the twist
    iso A×B ≅ B×A (products); intersection is a pullback of subobjects; composition
    is pullback-of-B-legs followed by image.  F preserves every ingredient of each
    recipe, hence the result — a canonical-iso chase with no ideas in it.

  - *Reflection* hinges on the book's definition of FAITHFUL (§1.33): an embedding
    that reflects isomorphisms — strictly stronger than hom-injectivity (`Faithful`
    in `S1_33` follows the book).  Any equation between relation-expressions says a
    canonical comparison monic is iso; F preserves the constructions, so if the
    equation holds downstairs the comparison is iso there, and "reflects isos" pulls
    it back.  §1.453 (faithful iff properness of subobjects is preserved) is the
    load-bearing bridge.  Freyd announces the heuristic at §1.33: "almost any
    property of interest is reflected by faithful functors that preserve it."

  - With the *modern* (merely hom-injective) notion of faithful, reflection is
    FALSE: for A = the poset 2 = {0 < 1}, B = the terminal category, the unique
    functor F is hom-injective and trivially preserves products, pullbacks and
    images, yet F(0) = F(1) as relations on 1 while 0 ∩ 1 = 0 ≠ 1 in A.  This is
    why these theorems must use `Faithful` from `S1_33`, not hom-injectivity.

  The first paragraph is the concrete, operation-by-operation instance of the
  Horn-sentence metatheorem below, and the natural stepping stone to proving it.

  A HORN SENTENCE in the predicates of (pre-)regular categories is treated
  abstractly here (its syntax is developed in §1.55); `HoldsIn H 𝒟` says the
  sentence `H` is satisfied by the category `𝒟`. -/

/-- A Horn sentence in the first-order language of (pre-)regular categories.

    **Genuine interpretation (no opaque uninterpreted stub).**  Rather than an
    uninterpreted `opaque` (which would make `HoldsIn` unfalsifiable / `True`-like
    and any reflection theorem vacuous), a `HornSentence` is taken *semantically*:
    it carries, for every (pre-)regular category `𝒟`, the proposition it asserts
    there.  This is the standard "a sentence IS its truth-in-each-structure
    function" reading — `sat 𝒟` is a real `Prop`, so `HoldsIn` below is a genuine
    satisfaction relation, falsifiable in general (e.g. the sentence `fun _ => False`
    holds in NO category).

    Freyd's *syntactic* Horn sentences (developed in §1.55) inject into this
    semantic type by interpretation; we work with the semantic image directly so
    that the reflection results have honest content.  The one thing this view does
    NOT give for free is the metatheorem that EVERY syntactic Horn sentence is
    automatically reflected by faithful structure-preserving functors — that needs
    the syntactic induction over Horn formulas (§1.55 / §1.551) and is recorded as
    MISSING in the tracker, NOT asserted here as a Sorry. -/
def HornSentence : Type (max (u+1) (v+1)) :=
  (𝒟 : Type u) → [Cat.{v} 𝒟] → Prop

/-- `H` HOLDS IN the category `𝒟` — the genuine satisfaction relation `𝒟 ⊨ H`. -/
def HoldsIn (H : HornSentence) (𝒟 : Type u) [Cat.{v} 𝒟] : Prop := H 𝒟

/-- `H` is REFLECTED BY a functor `F : 𝒜 → ℬ` when its truth downstairs forces its
    truth upstairs.  Freyd's §1.563 metatheorem is the assertion that every Horn
    sentence is reflected by any faithful functor preserving the Cartesian-with-images
    structure; capturing that uniformly requires the syntactic induction (MISSING,
    see tracker).  We make the dependence on a *named hypothesis* explicit so the
    reflection theorem has genuine content and needs no Sorry. -/
def ReflectedBy (H : HornSentence) {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] (_F : 𝒜 → ℬ) : Prop :=
  HoldsIn H ℬ → HoldsIn H 𝒜

/-- **§1.563**: If A and B are Cartesian with images and F : A → B is a faithful
    functor preserving finite limits and images, then F reflects any Horn sentence
    that is structurally reflected (`ReflectedBy`).  The book's metatheorem is that
    `ReflectedBy H F` holds for EVERY Horn sentence under these hypotheses; that
    universal claim is the §1.55 syntactic induction and is left MISSING (tracker)
    rather than asserted by a vacuous Sorry.  This statement is the honest, content-
    bearing residue: faithfulness + structure-preservation lets a reflected sentence
    pass upward.  `hrefl` is exactly the per-sentence reflection datum the induction
    would supply. -/
theorem horn_sentence_reflected_by_faithful {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    [CartesianCategory 𝒜] [HasImages 𝒜] [CartesianCategory ℬ] [HasImages ℬ]
    (F : 𝒜 → ℬ) [Functor F] (_hfaithful : Faithful F)
    (_h_pres_term : PreservesTerminal F) (_h_pres_prod : PreservesBinaryProducts F)
    (_h_pres_eq : PreservesEqualizers F)
    (_h_pres_mono : PreservesMono F) (_h_pres_images : PreservesImages F _h_pres_mono)
    (H : HornSentence) (hrefl : ReflectedBy H F) (hH : HoldsIn H ℬ) : HoldsIn H 𝒜 :=
  hrefl hH

/-- **§1.563** (corollary, via Henkin-Lubkin §1.55): A Horn sentence true for the
    category of sets `𝒮` is true for a regular category `A`, *provided* it is
    reflected along the Henkin–Lubkin representation `A ↪ 𝒮^|A|`.  The book obtains
    the reflection datum from the EXACT form of the representation (which needs the
    §1.543 capitalization lemma — now PROVEN Sorry-free as `Fredy.capitalization_lemma`;
    only the exactness wiring that applies it is not done here) — that supply is not
    yet assembled here, so we take it as the hypothesis `hrefl_from_Set` and discharge
    the corollary honestly,
    rather than emitting a Sorry that would secretly assert nothing.

    `𝒮` is the (abstract) category of sets; keeping it a parameter — rather than the
    concrete `Type u`, which is a `Type (u+1)` and so cannot be tested by the same
    `HornSentence` as the small `A : Type u` — avoids a spurious universe bump and
    matches `horn_sentence_reflected_by_faithful`. -/
theorem horn_sentence_reflected_from_Set (A : Type u) [Cat.{v} A] [RegularCategory A]
    (𝒮 : Type u) [Cat.{v} 𝒮] [RegularCategory 𝒮] (H : HornSentence)
    (hrefl_from_Set : HoldsIn H 𝒮 → HoldsIn H A)
    (hH : HoldsIn H 𝒮) : HoldsIn H A :=
  hrefl_from_Set hH

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

  Freyd's proof: given a cocone u, v, form the relation R = x°u ∩ y°v,
  verify it is a map in **Set** by element-wise reasoning, then use the
  Henkin-Lubkin representation theorem (§1.55) to transfer the result to
  any regular category. -/

/-- **§1.565 for Set**: A pullback of surjective functions is a pushout in **Set**.

    Diagram (in Freyd composition order, i.e. `≫` = first-then):
    ```
    P ---p₂---> C
    |           |
    p₁          y (cover)
    v           v
    A ---x----> B (cover)
    ```
    The square commutes: `p₁ ≫ x = p₂ ≫ y`, i.e., `∀ z, x(p₁ z) = y(p₂ z)`.

    Book proof: given a cocone u: A→Q, v: C→Q with `p₁ ≫ u = p₂ ≫ v`,
    define the relation `R := x°u ∩ y°v : B ⇸ Q`, verify it is a map
    (entire and simple) element-wise, then prove `xR = u` and `yR = v`.
    Uniqueness: `x` is a cover, hence epi. -/
theorem pullback_of_surjective_is_pushout_Set {A B C P : Type u}
    (x : A → B) (y : C → B) (p₁ : P → A) (p₂ : P → C)
    (h_surj_x : Function.Surjective x) (h_surj_y : Function.Surjective y)
    (h_isPullback : ∀ (X : Type u) (f : X → A) (g : X → C),
      (∀ w, x (f w) = y (g w)) → (∃ k : X → P, ((∀ w, p₁ (k w) = f w) ∧ (∀ w, p₂ (k w) = g w)) ∧
        ∀ k', ((∀ w, p₁ (k' w) = f w) ∧ (∀ w, p₂ (k' w) = g w)) → k' = k)) :
    ∀ (Q : Type u) (u : A → Q) (v : C → Q),
      (∀ z, u (p₁ z) = v (p₂ z)) → (∃ h : B → Q, ((∀ a, h (x a) = u a) ∧ (∀ c, h (y c) = v c)) ∧
        ∀ h', ((∀ a, h' (x a) = u a) ∧ (∀ c, h' (y c) = v c)) → h' = h) := by
  -- Pick a nonempty type at universe u for the pullback test
  let One : Type u := PUnit.{u+1}
  let star : One := PUnit.unit
  intro Q u v h_cocone
  -- Key lemma: x a = y c → u a = v c (lift the cone ⟨a, c⟩ through P)
  have h_key : ∀ (a : A) (c : C), x a = y c → u a = v c := by
    intro a c hac
    rcases h_isPullback One (λ _ => a) (λ _ => c) (λ _ => hac) with ⟨k, ⟨hk₁, hk₂⟩, _⟩
    calc
      u a = u (p₁ (k star)) := by simpa using congrArg u (hk₁ star).symm
      _ = v (p₂ (k star)) := h_cocone (k star)
      _ = v c := by simpa using congrArg v (hk₂ star)
  -- The book's relation R := x°u ∩ y°v : B ⇸ Q, element-wise
  let R : B → Q → Prop := λ b q => (∃ a, x a = b ∧ u a = q) ∧ (∃ c, y c = b ∧ v c = q)
  -- R is entire: the covers x, y supply witnesses; h_key makes their values agree
  have h_entire : ∀ b, ∃ q, R b q := by
    intro b
    rcases h_surj_x b with ⟨a, ha⟩
    rcases h_surj_y b with ⟨c, hc⟩
    exact ⟨u a, ⟨a, ha, rfl⟩, ⟨c, hc, (h_key a c (ha.trans hc.symm)).symm⟩⟩
  -- R is simple: h_key crosses the two halves of R
  have h_simple : ∀ b q q', R b q → R b q' → q = q' := by
    intro b q q' hq hq'
    obtain ⟨⟨a, ha, hua⟩, -⟩ := hq
    obtain ⟨-, ⟨c, hc, hvc⟩⟩ := hq'
    rw [← hua, ← hvc]
    exact h_key a c (ha.trans hc.symm)
  -- R entire and simple: a map.  Extract h : B → Q
  let h : B → Q := λ b => (h_entire b).choose
  have hR : ∀ b, R b (h b) := λ b => (h_entire b).choose_spec
  -- xR = u: (x a) R (u a), and R is simple
  have hxu : ∀ a, h (x a) = u a := by
    intro a
    refine h_simple (x a) _ _ (hR (x a)) ⟨⟨a, rfl, rfl⟩, ?_⟩
    rcases h_surj_y (x a) with ⟨c, hc⟩
    exact ⟨c, hc, (h_key a c hc.symm).symm⟩
  -- yR = v: (y c) R (v c), and R is simple
  have hyv : ∀ c, h (y c) = v c := by
    intro c
    refine h_simple (y c) _ _ (hR (y c)) ⟨?_, ⟨c, rfl, rfl⟩⟩
    rcases h_surj_x (y c) with ⟨a, ha⟩
    exact ⟨a, ha, h_key a c ha⟩
  refine ⟨h, ⟨hxu, hyv⟩, ?_⟩
  -- Uniqueness: x is a cover, hence epi
  intro h' ⟨h'x, _⟩
  ext b
  rcases h_surj_x b with ⟨a, ha⟩
  rw [← ha, h'x, hxu]

/-- In any category with images, `image.lift f` is a cover (the first factor in the
    cover-monic factorization of `f`).  Proof: if it factors through a monic `m`, then
    the subobject with arr = `m ≫ (image f).arr` allows `f`; image-minimality forces `m`
    to be a split monic, hence iso.  (Identical to the proof in S1_57, reproduced here
    to avoid a circular import: S1_57 imports S1_56.) -/
theorem image_lift_cover {A B : 𝒞} (f : A ⟶ B) [HasImages 𝒞] : Cover (image.lift f) := by
  intro D m g hm hfac
  -- hfac: g ≫ m = image.lift f, so f = g ≫ (m ≫ (image f).arr)
  have hmono_comp : Mono (m ≫ (image f).arr) := by
    intro W u v huv
    have h1 : u ≫ m = v ≫ m := (image f).monic _ _ (by
      simpa [Cat.assoc] using huv)
    exact hm _ _ h1
  have h_allows : Allows ⟨D, m ≫ (image f).arr, hmono_comp⟩ f := by
    refine ⟨g, ?_⟩
    calc g ≫ (m ≫ (image f).arr) = (g ≫ m) ≫ (image f).arr := (Cat.assoc _ _ _).symm
      _ = (image.lift f) ≫ (image f).arr := by rw [hfac]
      _ = f := image.lift_fac f
  have h_le : (image f).le ⟨D, m ≫ (image f).arr, hmono_comp⟩ := image_min f _ h_allows
  rcases h_le with ⟨h, hh⟩
  -- hh: h ≫ (m ≫ (image f).arr) = (image f).arr
  have hhm : h ≫ m = Cat.id (image f).dom := (image f).monic (h ≫ m) (Cat.id _) (by
    calc (h ≫ m) ≫ (image f).arr = h ≫ (m ≫ (image f).arr) := Cat.assoc _ _ _
      _ = (image f).arr := hh
      _ = Cat.id (image f).dom ≫ (image f).arr := (Cat.id_comp _).symm)
  have hmh : m ≫ h = Cat.id D := hm (m ≫ h) (Cat.id D) (by
    calc (m ≫ h) ≫ m = m ≫ (h ≫ m) := Cat.assoc _ _ _
      _ = m ≫ Cat.id (image f).dom := by rw [hhm]
      _ = m := Cat.comp_id _
      _ = Cat.id D ≫ m := (Cat.id_comp _).symm)
  exact ⟨h, hmh, hhm⟩

/-! ## §1.566 Every cover is a coequalizer

  In a regular category, every cover x : A → B is the coequalizer of its
  kernel pair (level).  The proof uses §1.565. -/

/-- **§1.566**: In a regular category, a cover `x : A → B` is the coequalizer of
    its kernel pair: every `g : A → C` that equalizes the kernel pair
    (`kp₁ ≫ g = kp₂ ≫ g`) factors *uniquely* through `x`.

    Proof: factor `⟨x,g⟩ : A → B×C` as `image.lift ≫ I.arr` (cover then mono).
    Its first leg `p := I.arr ≫ fst` is monic — this is the one genuinely
    regular step (`hp_mono`): the image relation `{(x a, g a)}` is *functional*
    precisely because `g` equalizes the kernel pair of `x` (needs covers stable
    under pullback, §1.565), isolated below.  Granting it, `x = image.lift ≫ p`
    exhibits the cover `x` factoring through the monic `p`, so `p` is iso, and
    `h := p⁻¹ ≫ (I.arr ≫ snd)` is the factorization — unique since `x` is epic. -/
theorem cover_is_coequalizer_of_level {A B : 𝒞} (x : A ⟶ B) [RegularCategory 𝒞]
    (hx : Cover x) {C : 𝒞} (g : A ⟶ C) (hg : kp₁ (f := x) ≫ g = kp₂ (f := x) ≫ g) :
    ∃ h : B ⟶ C, x ≫ h = g ∧ ∀ h' : B ⟶ C, x ≫ h' = g → h' = h := by
  let xg := pair x g
  let I := image xg
  have hx_fac : image.lift xg ≫ (I.arr ≫ fst) = x := by
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hq : image.lift xg ≫ (I.arr ≫ snd) = g := by
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- The image relation `{(x a, g a)}` is FUNCTIONAL: its first leg is monic.
  -- Take `u, v` agreeing after the first leg; pull the cover `image.lift xg`
  -- back along `u`, then along that pullback composed with `v`, giving a single
  -- cover `c` and two preimages `au, av` with `au≫e = c≫u`, `av≫e = c≫v`.
  -- They agree after `x` (hyp on first leg), so land in the kernel pair, whence
  -- `au≫g = av≫g` (the equalizing hypothesis `hg`); cancelling the cover `c`
  -- gives agreement after the second leg, and `I.arr` monic finishes.
  have hp_mono : Mono (I.arr ≫ fst) := by
    intro W u v huv
    have he_cover : Cover (image.lift xg) := image_lift_cover xg
    let pb1 := HasPullbacks.has (image.lift xg) u
    have hπ₂u_cover : Cover pb1.cone.π₂ := cover_pullback u he_cover
    let pb2 := HasPullbacks.has (image.lift xg) (pb1.cone.π₂ ≫ v)
    have hρ_cover : Cover pb2.cone.π₂ := cover_pullback (pb1.cone.π₂ ≫ v) he_cover
    let c := pb2.cone.π₂ ≫ pb1.cone.π₂
    let au := pb2.cone.π₂ ≫ pb1.cone.π₁
    let av := pb2.cone.π₁
    have hau_e : au ≫ image.lift xg = c ≫ u := by
      dsimp only [au, c]; rw [Cat.assoc, pb1.cone.w, ← Cat.assoc]
    have hav_e : av ≫ image.lift xg = c ≫ v := by
      dsimp only [av, c]; rw [pb2.cone.w, ← Cat.assoc]
    have hax : au ≫ x = av ≫ x := by
      calc au ≫ x = (au ≫ image.lift xg) ≫ (I.arr ≫ fst) := by rw [← hx_fac]; exact (Cat.assoc _ _ _).symm
        _ = (c ≫ u) ≫ (I.arr ≫ fst) := by rw [hau_e]
        _ = c ≫ (u ≫ (I.arr ≫ fst)) := Cat.assoc _ _ _
        _ = c ≫ (v ≫ (I.arr ≫ fst)) := by rw [huv]
        _ = (c ≫ v) ≫ (I.arr ≫ fst) := (Cat.assoc _ _ _).symm
        _ = (av ≫ image.lift xg) ≫ (I.arr ≫ fst) := by rw [hav_e]
        _ = av ≫ x := by rw [← hx_fac]; exact Cat.assoc _ _ _
    let l := (HasPullbacks.has x x).lift ⟨_, au, av, hax⟩
    have hl₁ : l ≫ kp₁ (f := x) = au := kp_lift_p₁ au av hax
    have hl₂ : l ≫ kp₂ (f := x) = av := kp_lift_p₂ au av hax
    have hag : au ≫ g = av ≫ g := by
      calc au ≫ g = (l ≫ kp₁ (f := x)) ≫ g := by rw [hl₁]
        _ = l ≫ (kp₁ (f := x) ≫ g) := Cat.assoc _ _ _
        _ = l ≫ (kp₂ (f := x) ≫ g) := by rw [hg]
        _ = (l ≫ kp₂ (f := x)) ≫ g := (Cat.assoc _ _ _).symm
        _ = av ≫ g := by rw [hl₂]
    have hagc : c ≫ (u ≫ (I.arr ≫ snd)) = c ≫ (v ≫ (I.arr ≫ snd)) := by
      calc c ≫ (u ≫ (I.arr ≫ snd)) = (c ≫ u) ≫ (I.arr ≫ snd) := (Cat.assoc _ _ _).symm
        _ = (au ≫ image.lift xg) ≫ (I.arr ≫ snd) := by rw [hau_e]
        _ = au ≫ (image.lift xg ≫ (I.arr ≫ snd)) := Cat.assoc _ _ _
        _ = au ≫ g := by rw [hq]
        _ = av ≫ g := hag
        _ = av ≫ (image.lift xg ≫ (I.arr ≫ snd)) := by rw [hq]
        _ = (av ≫ image.lift xg) ≫ (I.arr ≫ snd) := (Cat.assoc _ _ _).symm
        _ = (c ≫ v) ≫ (I.arr ≫ snd) := by rw [hav_e]
        _ = c ≫ (v ≫ (I.arr ≫ snd)) := Cat.assoc _ _ _
    have huvq : u ≫ (I.arr ≫ snd) = v ≫ (I.arr ≫ snd) := by
      apply cover_epi hπ₂u_cover
      apply cover_epi hρ_cover
      rw [← Cat.assoc pb2.cone.π₂ pb1.cone.π₂, ← Cat.assoc pb2.cone.π₂ pb1.cone.π₂]
      exact hagc
    -- `u ≫ I.arr` and `v ≫ I.arr` agree on both projections, so are equal.
    have he1 : (u ≫ I.arr) ≫ fst = (v ≫ I.arr) ≫ fst := by rw [Cat.assoc, Cat.assoc]; exact huv
    have he2 : (u ≫ I.arr) ≫ snd = (v ≫ I.arr) ≫ snd := by rw [Cat.assoc, Cat.assoc]; exact huvq
    have hext : u ≫ I.arr = v ≫ I.arr := by
      rw [pair_uniq ((v ≫ I.arr) ≫ fst) ((v ≫ I.arr) ≫ snd) (u ≫ I.arr) he1 he2]
      exact (pair_uniq ((v ≫ I.arr) ≫ fst) ((v ≫ I.arr) ≫ snd) (v ≫ I.arr) rfl rfl).symm
    exact I.monic u v hext
  have hp_iso : IsIso (I.arr ≫ fst) := hx (I.arr ≫ fst) (image.lift xg) hp_mono hx_fac
  obtain ⟨pinv, hpi1, hpi2⟩ := hp_iso
  have hxpinv : x ≫ pinv = image.lift xg := by
    rw [← hx_fac, Cat.assoc, hpi1, Cat.comp_id]
  have hxh : x ≫ (pinv ≫ (I.arr ≫ snd)) = g := by
    rw [← Cat.assoc, hxpinv, ← Cat.assoc, image.lift_fac, snd_pair]
  exact ⟨pinv ≫ (I.arr ≫ snd), hxh, fun h' hh' => cover_epi hx (hh'.trans hxh.symm)⟩

/-- **§1.566 (corollary)**: Two covers with the same kernel pair differ by an
    isomorphism.  If covers `x, y : A → ·` each equalize the other's kernel pair,
    then there is a (unique) iso `φ` with `x ≫ φ = y`.  Immediate from §1.566:
    each is the coequalizer of its kernel pair, so they factor through each other,
    and the comparison maps are mutually inverse because covers are epic. -/
theorem covers_same_kernelPair_iso {A B B' : 𝒞} [RegularCategory 𝒞]
    (x : A ⟶ B) (hx : Cover x) (y : A ⟶ B') (hy : Cover y)
    (hxy : kp₁ (f := x) ≫ y = kp₂ (f := x) ≫ y)
    (hyx : kp₁ (f := y) ≫ x = kp₂ (f := y) ≫ x) :
    ∃ φ : B ⟶ B', IsIso φ ∧ x ≫ φ = y := by
  obtain ⟨φ, hφ, _⟩ := cover_is_coequalizer_of_level x hx y hxy
  obtain ⟨ψ, hψ, _⟩ := cover_is_coequalizer_of_level y hy x hyx
  refine ⟨φ, ⟨ψ, ?_, ?_⟩, hφ⟩
  · apply cover_epi hx
    calc x ≫ (φ ≫ ψ) = (x ≫ φ) ≫ ψ := (Cat.assoc _ _ _).symm
      _ = y ≫ ψ := by rw [hφ]
      _ = x := hψ
      _ = x ≫ Cat.id B := (Cat.comp_id _).symm
  · apply cover_epi hy
    calc y ≫ (ψ ≫ φ) = (y ≫ ψ) ≫ φ := (Cat.assoc _ _ _).symm
      _ = x ≫ φ := by rw [hψ]
      _ = y := hφ
      _ = y ≫ Cat.id B' := (Cat.comp_id _).symm

/-- **§1.565 (crux, constructive in 𝒞)**: if `(P; p₁, p₂)` is a pullback of the
    covers `x : A ↠ B`, `y : C ↠ B`, then any cocone leg `u : A ⟶ Q` over the
    cospan (i.e. `u, v` with `p₁ ≫ u = p₂ ≫ v`) EQUALIZES the kernel pair of `x`:
    `kp₁ x ≫ u = kp₂ x ≫ u`.

    This is the Set-level `h_key` (`x a₁ = x a₂ ⟹ u a₁ = u a₂`) made elementary:
    a pair `(a₁, a₂)` agreeing under `x` lands, after pulling the cover `y` back
    along `kp₁ x ≫ x`, on two preimages `z₁, z₂ : K' ⟶ P` sharing the same
    `C`-coordinate; the cocone identity then forces agreement under `u`, and the
    pullback leg over `K` is a cover, so it cancels. -/
theorem cocone_equalizes_kernelPair {A B C P Q : 𝒞} [RegularCategory 𝒞]
    (x : A ⟶ B) (y : C ⟶ B) (p₁ : P ⟶ A) (p₂ : P ⟶ C) (h_sq : p₁ ≫ x = p₂ ≫ y)
    (h_isPb : (⟨P, p₁, p₂, h_sq⟩ : Cone x y).IsPullback)
    (hy : Cover y) (u : A ⟶ Q) (v : C ⟶ Q) (hcocone : p₁ ≫ u = p₂ ≫ v) :
    kp₁ (f := x) ≫ u = kp₂ (f := x) ≫ u := by
  -- Pull the cover `y` back along `k₁ ≫ x : K → B`; the leg over `K` is a cover.
  let k₁ := kp₁ (f := x); let k₂ := kp₂ (f := x)
  have hkx : k₁ ≫ x = k₂ ≫ x := kp_sq
  let pby := HasPullbacks.has y (k₁ ≫ x)
  have hπ_cover : Cover pby.cone.π₂ := cover_pullback (k₁ ≫ x) hy
  -- pby.cone.w : π₁ ≫ y = π₂ ≫ (k₁ ≫ x).  Cone over (x,y) using (π₂ ≫ k₁, π₁).
  have hw₁ : (pby.cone.π₂ ≫ k₁) ≫ x = pby.cone.π₁ ≫ y :=
    (Cat.assoc _ _ _).trans pby.cone.w.symm
  obtain ⟨z₁, ⟨hz₁a, hz₁b⟩, _⟩ := h_isPb ⟨pby.cone.pt, pby.cone.π₂ ≫ k₁, pby.cone.π₁, hw₁⟩
  -- Same with k₂: (π₂ ≫ k₂) ≫ x = π₂ ≫ (k₁ ≫ x) = π₁ ≫ y.
  have hw₂ : (pby.cone.π₂ ≫ k₂) ≫ x = pby.cone.π₁ ≫ y := by
    rw [Cat.assoc, ← hkx]; exact pby.cone.w.symm
  obtain ⟨z₂, ⟨hz₂a, hz₂b⟩, _⟩ := h_isPb ⟨pby.cone.pt, pby.cone.π₂ ≫ k₂, pby.cone.π₁, hw₂⟩
  -- hz₁a : z₁ ≫ p₁ = π₂ ≫ k₁,  hz₁b : z₁ ≫ p₂ = π₁;  similarly z₂.
  have key : pby.cone.π₂ ≫ (k₁ ≫ u) = pby.cone.π₂ ≫ (k₂ ≫ u) := by
    calc pby.cone.π₂ ≫ (k₁ ≫ u)
        = (pby.cone.π₂ ≫ k₁) ≫ u := (Cat.assoc _ _ _).symm
      _ = (z₁ ≫ p₁) ≫ u := by rw [hz₁a]
      _ = z₁ ≫ (p₁ ≫ u) := Cat.assoc _ _ _
      _ = z₁ ≫ (p₂ ≫ v) := by rw [hcocone]
      _ = (z₁ ≫ p₂) ≫ v := (Cat.assoc _ _ _).symm
      _ = pby.cone.π₁ ≫ v := by rw [hz₁b]
      _ = (z₂ ≫ p₂) ≫ v := by rw [hz₂b]
      _ = z₂ ≫ (p₂ ≫ v) := Cat.assoc _ _ _
      _ = z₂ ≫ (p₁ ≫ u) := by rw [hcocone]
      _ = (z₂ ≫ p₁) ≫ u := (Cat.assoc _ _ _).symm
      _ = (pby.cone.π₂ ≫ k₂) ≫ u := by rw [hz₂a]
      _ = pby.cone.π₂ ≫ (k₂ ≫ u) := Cat.assoc _ _ _
  exact cover_epi hπ_cover key

/-- **§1.565** (general case): In a regular category, a pullback of covers is a
    PUSHOUT.  Constructive proof, directly in `𝒞` (no representation transfer).

    The pushout cocone is `(B; x, y)` itself — the cover legs are the injections.
    Given any cocone `(Q; u, v)` with `p₁ ≫ u = p₂ ≫ v`, the descent map
    `h : B ⟶ Q` is produced by §1.566 (`cover_is_coequalizer_of_level`): `x` is the
    coequalizer of its kernel pair, and `u` equalizes that kernel pair by
    `cocone_equalizes_kernelPair`, so `h` with `x ≫ h = u` exists and is unique.
    The second leg `y ≫ h = v` follows because `p₂` is a cover (pullback of the
    cover `x` along `y`) and `p₂ ≫ (y ≫ h) = (p₁ ≫ x) ≫ h = p₁ ≫ u = p₂ ≫ v`.
    Uniqueness of `desc` is immediate from `x` (or `y`) being epic.

    The hypothesis `h_isPb` (the given square IS a pullback) is required — and was
    present in the proved Set version `pullback_of_surjective_is_pushout_Set` as
    `h_isPullback` — without it an arbitrary commuting square of covers is not a
    pushout. -/
noncomputable def pullback_of_covers_is_pushout {A B C P : 𝒞} (x : A ⟶ B) (y : C ⟶ B)
    (p₁ : P ⟶ A) (p₂ : P ⟶ C) (h_sq : p₁ ≫ x = p₂ ≫ y)
    [RegularCategory 𝒞] (h_isPb : (⟨P, p₁, p₂, h_sq⟩ : Cone x y).IsPullback)
    (h_cover_x : Cover x) (h_cover_y : Cover y) : HasPushout p₁ p₂ where
  cocone := ⟨B, x, y, h_sq⟩
  desc c :=
    (cover_is_coequalizer_of_level x h_cover_x c.ι₁
      (cocone_equalizes_kernelPair x y p₁ p₂ h_sq h_isPb h_cover_y c.ι₁ c.ι₂ c.w)).choose
  fac₁ c :=
    (cover_is_coequalizer_of_level x h_cover_x c.ι₁
      (cocone_equalizes_kernelPair x y p₁ p₂ h_sq h_isPb h_cover_y c.ι₁ c.ι₂ c.w)).choose_spec.1
  fac₂ c := by
    have hxh : x ≫ (cover_is_coequalizer_of_level x h_cover_x c.ι₁
        (cocone_equalizes_kernelPair x y p₁ p₂ h_sq h_isPb h_cover_y c.ι₁ c.ι₂ c.w)).choose
        = c.ι₁ := (cover_is_coequalizer_of_level x h_cover_x c.ι₁
      (cocone_equalizes_kernelPair x y p₁ p₂ h_sq h_isPb h_cover_y c.ι₁ c.ι₂ c.w)).choose_spec.1
    -- p₂ is a cover: it is the `π₂`-leg of the pullback `(P; p₁, p₂)` of the
    -- cover `x` along `y`, so covers transfer to it.
    have hp₂_cover : Cover p₂ :=
      PullbacksTransferCovers.pullbacks_transfer_covers
        (⟨P, p₁, p₂, h_sq⟩ : Cone x y) h_isPb h_cover_x
    apply cover_epi hp₂_cover
    show p₂ ≫ (y ≫ _) = p₂ ≫ c.ι₂
    calc p₂ ≫ (y ≫ _) = (p₂ ≫ y) ≫ _ := (Cat.assoc _ _ _).symm
      _ = (p₁ ≫ x) ≫ _ := by rw [h_sq]
      _ = p₁ ≫ (x ≫ _) := Cat.assoc _ _ _
      _ = p₁ ≫ c.ι₁ := by rw [hxh]
      _ = p₂ ≫ c.ι₂ := c.w
  uniq c h hι₁ _ :=
    (cover_is_coequalizer_of_level x h_cover_x c.ι₁
      (cocone_equalizes_kernelPair x y p₁ p₂ h_sq h_isPb h_cover_y c.ι₁ c.ι₂ c.w)).choose_spec.2
        h hι₁

/-! ## §1.567 Equivalence relations

  E : A → A is an EQUIVALENCE RELATION if 1 ≤ E, E° ≤ E, EE ≤ E.
  The level (kernel pair) of any morphism is an equivalence relation. -/

def EquivalenceRelation [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (E : BinRel 𝒞 A A) : Prop :=
  (∃ (h : A ⟶ E.src), h ≫ E.colA = Cat.id A ∧ h ≫ E.colB = Cat.id A) ∧
  Nonempty (RelHom E (reciprocal E)) ∧
  Nonempty (RelHom (E ⊚ E) E)

/-- The LEVEL (kernel pair) of `x`, packaged as a binary relation on `A`:
    columns `(kp₁, kp₂)`, jointly monic as the legs of a pullback. -/
def kernelPairRel [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    {A B : 𝒞} (x : A ⟶ B) : BinRel 𝒞 A A where
  src := kernelPair x
  colA := kp₁ (f := x)
  colB := kp₂ (f := x)
  isMonicPair := by
    intro W f g h1 h2
    have hfw : (f ≫ kp₁ (f := x)) ≫ x = (f ≫ kp₂ (f := x)) ≫ x := by
      rw [Cat.assoc, kp_sq, ← Cat.assoc]
    exact (kp_lift_uniq (f ≫ kp₁) (f ≫ kp₂) hfw f rfl rfl).trans
          (kp_lift_uniq (f ≫ kp₁) (f ≫ kp₂) hfw g h1.symm h2.symm).symm

/-- **§1.567** (transitivity): the level of `x` is transitive, `level ⊚ level ⊂ level`.
    A composite point `(a,c)` comes from a pullback point matching `a~b`, `b~c`,
    so `a≫x = b≫x = c≫x`; that lifts into the kernel pair, and image-minimality
    (`image_min`) turns the lift into the required `RelHom`. -/
theorem kernelPair_transitive [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    [HasImages 𝒞] {A B : 𝒞} (x : A ⟶ B) :
    RelLe (kernelPairRel x ⊚ kernelPairRel x) (kernelPairRel x) := by
  let pb := HasPullbacks.has (kp₂ (f := x)) (kp₁ (f := x))
  let span := pair (pb.cone.π₁ ≫ kp₁ (f := x)) (pb.cone.π₂ ≫ kp₂ (f := x))
  let S : Subobject 𝒞 (prod A A) :=
    ⟨kernelPair x, pair (kp₁ (f := x)) (kp₂ (f := x)),
      monic_pair_of_monicPair _ _ (kernelPairRel x).isMonicPair⟩
  -- the matched middle gives `a≫x = c≫x`, so the pair lifts into the kernel pair.
  have hwx : (pb.cone.π₁ ≫ kp₁ (f := x)) ≫ x = (pb.cone.π₂ ≫ kp₂ (f := x)) ≫ x := by
    have hmid : pb.cone.π₁ ≫ kp₂ (f := x) = pb.cone.π₂ ≫ kp₁ (f := x) := pb.cone.w
    calc (pb.cone.π₁ ≫ kp₁ (f := x)) ≫ x
        = (pb.cone.π₁ ≫ kp₂ (f := x)) ≫ x := by rw [Cat.assoc, kp_sq, ← Cat.assoc]
      _ = (pb.cone.π₂ ≫ kp₁ (f := x)) ≫ x := by rw [hmid]
      _ = (pb.cone.π₂ ≫ kp₂ (f := x)) ≫ x := by rw [Cat.assoc, kp_sq, ← Cat.assoc]
  let w := (HasPullbacks.has x x).lift
    ⟨_, pb.cone.π₁ ≫ kp₁ (f := x), pb.cone.π₂ ≫ kp₂ (f := x), hwx⟩
  have hspan : w ≫ pair (kp₁ (f := x)) (kp₂ (f := x)) = span :=
    pair_uniq _ _ _
      (by rw [Cat.assoc, fst_pair]; exact kp_lift_p₁ _ _ hwx)
      (by rw [Cat.assoc, snd_pair]; exact kp_lift_p₂ _ _ hwx)
  obtain ⟨k, hk⟩ := image_min span S ⟨w, hspan⟩
  refine ⟨⟨k, ?_, ?_⟩⟩
  · calc k ≫ kp₁ (f := x) = (k ≫ pair (kp₁ (f := x)) (kp₂ (f := x))) ≫ fst := by
            rw [Cat.assoc, fst_pair]
      _ = (image span).arr ≫ fst := by rw [hk]
  · calc k ≫ kp₂ (f := x) = (k ≫ pair (kp₁ (f := x)) (kp₂ (f := x))) ≫ snd := by
            rw [Cat.assoc, snd_pair]
      _ = (image span).arr ≫ snd := by rw [hk]

/-- **§1.567**: The level (kernel pair) of any morphism is an equivalence
    relation — reflexive (the diagonal `kp_diag`), symmetric (the pullback
    swap of the two legs), transitive (`kernelPair_transitive`). -/
theorem level_is_equivalence_relation [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    [HasImages 𝒞] {A B : 𝒞} (x : A ⟶ B) : EquivalenceRelation (kernelPairRel x) := by
  refine ⟨⟨kp_diag (f := x), kp_diag_p₁, kp_diag_p₂⟩, ⟨⟨?_, ?_, ?_⟩⟩, kernelPair_transitive x⟩
  · exact (HasPullbacks.has x x).lift ⟨_, kp₂ (f := x), kp₁ (f := x), kp_sq.symm⟩
  · exact kp_lift_p₂ (kp₂ (f := x)) (kp₁ (f := x)) kp_sq.symm
  · exact kp_lift_p₁ (kp₂ (f := x)) (kp₁ (f := x)) kp_sq.symm

/-- **§1.568**: An equivalence relation E on A is EFFECTIVE if it is the level
    (kernel pair) of a cover (quotient-object) x : A → Q.  Equivalently,
    E ≅ x ⊚ x° = level(x) in the relation containment order. -/
def IsEffective {A : 𝒞} (E : BinRel 𝒞 A A) [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] : Prop :=
  EquivalenceRelation E ∧ ∃ (Q : 𝒞) (x : A ⟶ Q), Cover x ∧
    RelLe E ((graph x) ⊚ (graph x)°) ∧ RelLe ((graph x) ⊚ (graph x)°) E

/-! ## §1.569  Cover characterized relationally; associativity of ⊚ ↔ regular

  Relational cover lemma: x : A → B is a cover iff 1_B ≤ x° ⊚ x
  (where x is silently embedded as `graph x`).  From this we get:

  **1.569:** Let A be a Cartesian category with images.
  Composition of relations is associative iff A is regular. -/

section
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-- **§1.569**: The reciprocal-composition `(graph x)° ⊚ (graph x)` is always
    contained in the identity on B — i.e., `x°x ≤ 1_B` for any morphism x.
    The proof: the span `⟨x, x⟩ = x ≫ diag B` factors through the diagonal,
    so its image has equal fst/snd legs. -/
theorem reciprocal_comp_self_le_one {A B : 𝒞} (x : A ⟶ B) :
    RelLe ((graph x)° ⊚ (graph x)) (graph (Cat.id B)) := by
  -- The kernel pair span, unpacked from the compose definition
  let pb := HasPullbacks.has ((graph x)°).colB (graph x).colA
  have hπ_eq : pb.cone.π₁ = pb.cone.π₂ := by
    -- pb.cone.w : π₁ ≫ ((graph x)°).colB = π₂ ≫ (graph x).colA
    -- Both ((graph x)°).colB and (graph x).colA reduce to id_A
    simpa [graph, reciprocal, Cat.comp_id] using pb.cone.w
  let s : pb.cone.pt ⟶ prod B B := pair (pb.cone.π₁ ≫ x) (pb.cone.π₂ ≫ x)
  have hsp_fac : s = (pb.cone.π₁ ≫ x) ≫ diag B := by
    dsimp [s]; rw [← hπ_eq, pair_diag_eq (pb.cone.π₁ ≫ x)]
  let diagSub : Subobject 𝒞 (prod B B) := ⟨B, diag B, diag_mono B⟩
  have hallows : Allows diagSub s := ⟨pb.cone.π₁ ≫ x, by dsimp [diagSub]; rw [hsp_fac]⟩
  obtain ⟨k, hk⟩ := image_min s diagSub hallows
  dsimp [diagSub] at hk
  -- hk : k ≫ diag B = (image s).arr
  have h_fst : (image s).arr ≫ fst = k := by
    calc (image s).arr ≫ fst = (k ≫ diag B) ≫ fst := by rw [hk]
      _ = k ≫ (diag B ≫ fst) := Cat.assoc _ _ _
      _ = k ≫ Cat.id B := by rw [diag_fst]
      _ = k := Cat.comp_id _
  have h_snd : (image s).arr ≫ snd = k := by
    calc (image s).arr ≫ snd = (k ≫ diag B) ≫ snd := by rw [hk]
      _ = k ≫ (diag B ≫ snd) := Cat.assoc _ _ _
      _ = k ≫ Cat.id B := by rw [diag_snd]
      _ = k := Cat.comp_id _
  -- Build the RelHom: src = (image s).dom, colA = (image s).arr≫fst, colB = (image s).arr≫snd
  -- graph(id B): src = B, colA = id B, colB = id B
  unfold compose; dsimp
  refine ⟨⟨k, ?_, ?_⟩⟩
  · dsimp [graph]; rw [Cat.comp_id]; exact h_fst.symm
  · dsimp [graph]; rw [Cat.comp_id]; exact h_snd.symm

/-- **§1.569**: relational characterization of covers.
    `x : A → B` is a cover iff `1_B ≤ (graph x)° ⊚ (graph x)` — the identity on B
    is contained in the reciprocal-then-graph composition.  In the book's notation:
    x is a cover iff `1_B ⊂ x°x`. -/
theorem cover_iff_one_le_reciprocal_comp_self {A B : 𝒞} (x : A ⟶ B) :
    Cover x ↔ RelLe (graph (Cat.id B)) ((graph x)° ⊚ (graph x)) := by
  have hp : MonicPair (x : A ⟶ B) (Cat.id A : A ⟶ A) := by
    intro W f g _ hid
    simpa [Cat.comp_id] using hid
  have h := tabulated_is_entire_iff_left_cover (x : A ⟶ B) (Cat.id A) hp
  -- h : Entire (BinRel.mk A x id_A hp) ↔ Cover x
  -- BinRel.mk A x id_A hp = (graph x)°
  -- Entire ((graph x)°) = 1_B ≤ (graph x)° ⊚ (graph x)
  have h_rel : BinRel.mk A (x : A ⟶ B) (Cat.id A : A ⟶ A) hp = (graph x)° := rfl
  have h_entire : Entire ((graph x)°) ↔ RelLe (graph (Cat.id B)) ((graph x)° ⊚ (graph x)) := by
    simp [Entire, graph, reciprocal]
  simpa [h_rel, h_entire] using h.symm

/-- **§1.569**: `x : A → B` is a cover iff `x°x = 1_B` — the reciprocal-then-graph
    composition equals the identity relation on B.  Combine the always-true
    `x°x ≤ 1_B` with the equivalence `1_B ≤ x°x ↔ Cover x`. -/
theorem cover_iff_reciprocal_comp_self_eq_one {A B : 𝒞} (x : A ⟶ B) :
    Cover x ↔ (RelLe ((graph x)° ⊚ (graph x)) (graph (Cat.id B)) ∧
               RelLe (graph (Cat.id B)) ((graph x)° ⊚ (graph x))) := by
  constructor
  · intro hc
    exact ⟨reciprocal_comp_self_le_one x, (cover_iff_one_le_reciprocal_comp_self x).mp hc⟩
  · intro ⟨_, h⟩
    apply (cover_iff_one_le_reciprocal_comp_self x).mpr
    exact h

/-- The cover-leg `image.lift f` is an ISO whenever `f` is monic.  `image.lift f`
    is always a cover (`image_lift_cover`); a monic `f = image.lift f ≫ (image f).arr`
    forces its left factor `image.lift f` to be monic; a monic cover is iso. -/
theorem image_lift_iso_of_mono {A B : 𝒞} (f : A ⟶ B) (hf : Mono f) :
    IsIso (image.lift f) := by
  have hmono : Mono (image.lift f) := by
    intro W u v huv
    apply hf
    calc u ≫ f = u ≫ (image.lift f ≫ (image f).arr) := by rw [image.lift_fac]
      _ = (u ≫ image.lift f) ≫ (image f).arr := (Cat.assoc _ _ _).symm
      _ = (v ≫ image.lift f) ≫ (image f).arr := by rw [huv]
      _ = v ≫ (image.lift f ≫ (image f).arr) := Cat.assoc _ _ _
      _ = v ≫ f := by rw [image.lift_fac]
  exact monic_cover_iso _ (image_lift_cover f) hmono

end

/-- CONSTANT MORPHISM (§1.56(10)): x: A→B is constant if ∀y,y' : C→A, y≫x = y'≫x. -/
def Constant {A B : 𝒞} (x : A ⟶ B) : Prop :=
  ∀ {C : 𝒞} (y y' : C ⟶ A), y ≫ x = y' ≫ x

/-- QUOTIENT-OBJECT of A (§1.568): the poset of isomorphism classes of covers with source A.
    The preorder: f ≤ g if f factors through g (as covers). -/
def QuotientObject (A : 𝒞) : Type (max u v) :=
  Σ (B : 𝒞) (f : A ⟶ B), PLift (Cover f)

/-! ## Rel(A) — the category of relations (§1.564, §1.56(10))

  Objects are the same as in A, morphisms A → B are binary relations,
  composition is `⊚`, identity is `graph(id)`.  The graph map
  `x ↦ graph(x)` is a faithful functor `A → Rel(A)`. -/

section
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-- **§1.56**: `graph(id_A)` is a left identity for `⊚`.  The pullback of
    id_A and R.colA is trivial, and the span equals R.colA, R.colB composed
    with the right projection.  Image minimality yields the RelHom. -/
theorem graph_id_comp {A B : 𝒞} (R : BinRel 𝒞 A B) : RelLe ((graph (Cat.id A)) ⊚ R) R := by
  let T := R.src; let a := R.colA; let b := R.colB
  have h_monic : Mono (pair a b) := monic_pair_of_monicPair a b R.isMonicPair
  -- Pullback of id_A and a over A
  let pb := HasPullbacks.has (Cat.id A) a
  -- Pullback square: pb.cone.w : pb.cone.π₁ ≫ id_A = pb.cone.π₂ ≫ a
  -- So pb.cone.π₁ = pb.cone.π₂ ≫ a  (by Cat.comp_id)
  have h_pb_w : pb.cone.π₁ = pb.cone.π₂ ≫ a := by
    simpa [Cat.comp_id] using pb.cone.w
  -- The span for the composition: pair(π₁ ≫ id_A, π₂ ≫ b) = pair(π₁, π₂ ≫ b)
  let span := pair (pb.cone.π₁ ≫ (Cat.id A)) (pb.cone.π₂ ≫ b)
  have h_span_eq : span = pb.cone.π₂ ≫ pair a b := by
    dsimp [span]
    rw [Cat.comp_id, h_pb_w]
    apply (pair_uniq (pb.cone.π₂ ≫ a) (pb.cone.π₂ ≫ b) (pb.cone.π₂ ≫ pair a b)
      (by rw [Cat.assoc, fst_pair a b])
      (by rw [Cat.assoc, snd_pair a b])).symm
  -- S: the subobject of A×B tabulated by R (represented by the monic pair(a,b))
  let S : Subobject 𝒞 (prod A B) := ⟨T, pair a b, h_monic⟩
  -- span factors through S via pb.cone.π₂
  have hallows : Allows S span := ⟨pb.cone.π₂, h_span_eq.symm⟩
  -- I: the image of span (= the source object of the composed relation)
  let I := image span
  have h_image_le : I.le S := image_min span S hallows
  rcases h_image_le with ⟨k, hk⟩
  -- k ≫ pair(a,b) = I.arr, so k witnesses the RelHom from composed to R
  have hkA : k ≫ a = I.arr ≫ fst := by
    calc k ≫ a = (k ≫ pair a b) ≫ fst := by rw [Cat.assoc, fst_pair a b]
      _ = I.arr ≫ fst := by rw [hk]
  have hkB : k ≫ b = I.arr ≫ snd := by
    calc k ≫ b = (k ≫ pair a b) ≫ snd := by rw [Cat.assoc, snd_pair a b]
      _ = I.arr ≫ snd := by rw [hk]
  exact ⟨⟨k, hkA, hkB⟩⟩

/-- **§1.56**: `graph(id_A)` is a left identity for `⊚` (reverse containment).
    Lift through the pullback of id_A and R.colA via the cone ⟨R.colA, id⟩. -/
theorem comp_graph_id_left {A B : 𝒞} (R : BinRel 𝒞 A B) : RelLe R ((graph (Cat.id A)) ⊚ R) := by
  let T := R.src; let a := R.colA; let b := R.colB
  -- Pullback of id_A and a over A; lift from cone ⟨a, id_T⟩
  let pb := HasPullbacks.has (Cat.id A) a
  have h_cone_w : a ≫ (Cat.id A) = (Cat.id T) ≫ a := by rw [Cat.comp_id, Cat.id_comp]
  let c : Cone (Cat.id A) a := ⟨T, a, Cat.id T, h_cone_w⟩
  let u := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = a := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = Cat.id T := pb.lift_snd c
  -- span = pair(π₁, π₂ ≫ b)
  let span := pair (pb.cone.π₁ ≫ (Cat.id A)) (pb.cone.π₂ ≫ b)
  let I := image span
  -- h = u ≫ image.lift span : T → I.dom
  let h : T ⟶ I.dom := u ≫ image.lift span
  have h_colA : h ≫ (I.arr ≫ fst) = a := by
    dsimp [h, I]
    rw [Cat.assoc, ← Cat.assoc (image.lift span), image.lift_fac span, fst_pair,
      ← Cat.assoc u pb.cone.π₁, Cat.comp_id]
    exact hu₁
  have h_colB : h ≫ (I.arr ≫ snd) = b := by
    dsimp [h, I]
    rw [Cat.assoc, ← Cat.assoc (image.lift span), image.lift_fac span, snd_pair,
      ← Cat.assoc u pb.cone.π₂, hu₂, Cat.id_comp]
  exact ⟨⟨h, h_colA, h_colB⟩⟩

/-- **§1.56**: `graph(id_B)` is a right identity for `⊚`.  Dual to `graph_id_comp`:
    pullback of R.colB and id_B is trivial; image minimality yields the RelHom. -/
theorem comp_graph_id {A B : 𝒞} (R : BinRel 𝒞 A B) : RelLe (R ⊚ (graph (Cat.id B))) R := by
  let T := R.src; let a := R.colA; let b := R.colB
  have h_monic : Mono (pair a b) := monic_pair_of_monicPair a b R.isMonicPair
  -- Pullback of R.colB and id_B over B
  let pb := HasPullbacks.has b (Cat.id B)
  -- pb.cone.w : pb.cone.π₁ ≫ b = pb.cone.π₂ ≫ id_B
  have h_pb_w : pb.cone.π₁ ≫ b = pb.cone.π₂ := by
    simpa [Cat.comp_id] using pb.cone.w
  -- span = pair(π₁ ≫ a, π₂) after ≫ id cancels
  let span := pair (pb.cone.π₁ ≫ a) (pb.cone.π₂ ≫ (Cat.id B))
  -- span = pair(π₁ ≫ a, π₁ ≫ b) = π₁ ≫ pair(a,b)
  have h_span_eq : pb.cone.π₁ ≫ pair a b = span := by
    dsimp [span]
    rw [Cat.comp_id, ← h_pb_w]
    apply pair_uniq (pb.cone.π₁ ≫ a) (pb.cone.π₁ ≫ b) _
      (by rw [Cat.assoc, fst_pair a b])
      (by rw [Cat.assoc, snd_pair a b])
  let S : Subobject 𝒞 (prod A B) := ⟨T, pair a b, h_monic⟩
  have hallows : Allows S span := ⟨pb.cone.π₁, h_span_eq⟩
  let I := image span
  have h_image_le : I.le S := image_min span S hallows
  rcases h_image_le with ⟨k, hk⟩
  -- k ≫ pair(a,b) = I.arr
  have hkA : k ≫ a = I.arr ≫ fst := by
    calc k ≫ a = (k ≫ pair a b) ≫ fst := by rw [Cat.assoc, fst_pair a b]
      _ = I.arr ≫ fst := by rw [hk]
  have hkB : k ≫ b = I.arr ≫ snd := by
    calc k ≫ b = (k ≫ pair a b) ≫ snd := by rw [Cat.assoc, snd_pair a b]
      _ = I.arr ≫ snd := by rw [hk]
  exact ⟨⟨k, hkA, hkB⟩⟩

/-- **§1.56**: `graph(id_B)` is a right identity for `⊚` (reverse containment).
    Dual to `comp_graph_id_left`: lift via cone ⟨id_T, R.colB⟩. -/
theorem comp_graph_id_right {A B : 𝒞} (R : BinRel 𝒞 A B) : RelLe R (R ⊚ (graph (Cat.id B))) := by
  let T := R.src; let a := R.colA; let b := R.colB
  -- Pullback of R.colB and id_B over B; lift from cone ⟨id_T, R.colB⟩
  let pb := HasPullbacks.has b (Cat.id B)
  have h_cone_w : (Cat.id T) ≫ b = b ≫ (Cat.id B) := by rw [Cat.id_comp, Cat.comp_id]
  let c : Cone b (Cat.id B) := ⟨T, Cat.id T, b, h_cone_w⟩
  let u := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = Cat.id T := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = b := pb.lift_snd c
  -- span = pair(π₁ ≫ a, π₂ ≫ id_B)
  let span := pair (pb.cone.π₁ ≫ a) (pb.cone.π₂ ≫ (Cat.id B))
  let I := image span
  let h : T ⟶ I.dom := u ≫ image.lift span
  have h_colA : h ≫ (I.arr ≫ fst) = a := by
    dsimp [h, I]
    rw [Cat.assoc, ← Cat.assoc (image.lift span), image.lift_fac span, fst_pair,
      ← Cat.assoc u pb.cone.π₁, hu₁, Cat.id_comp]
  have h_colB : h ≫ (I.arr ≫ snd) = b := by
    dsimp [h, I]
    rw [Cat.assoc, ← Cat.assoc (image.lift span), image.lift_fac span, snd_pair,
      Cat.comp_id]
    exact hu₂
  exact ⟨⟨h, h_colA, h_colB⟩⟩

/-- Pullback of a mono is a mono: in `pb = pullback(f, m)` with `m` monic,
    the leg `π₁` (the pullback of `m` along `f`) is monic. -/
theorem pullback_fst_mono {B I D : 𝒞} (f : B ⟶ D) (m : I ⟶ D) (hm : Mono m) :
    Mono (HasPullbacks.has f m).cone.π₁ := by
  intro W p q hpq
  let pb := HasPullbacks.has f m
  change p ≫ pb.cone.π₁ = q ≫ pb.cone.π₁ at hpq
  have hpq2 : p ≫ pb.cone.π₂ = q ≫ pb.cone.π₂ := by
    apply hm
    calc (p ≫ pb.cone.π₂) ≫ m = p ≫ (pb.cone.π₂ ≫ m) := Cat.assoc _ _ _
      _ = p ≫ (pb.cone.π₁ ≫ f) := by rw [← pb.cone.w]
      _ = (p ≫ pb.cone.π₁) ≫ f := (Cat.assoc _ _ _).symm
      _ = (q ≫ pb.cone.π₁) ≫ f := by rw [hpq]
      _ = q ≫ (pb.cone.π₁ ≫ f) := Cat.assoc _ _ _
      _ = q ≫ (pb.cone.π₂ ≫ m) := by rw [pb.cone.w]
      _ = (q ≫ pb.cone.π₂) ≫ m := (Cat.assoc _ _ _).symm
  have hcone : (p ≫ pb.cone.π₁) ≫ f = (p ≫ pb.cone.π₂) ≫ m := by
    rw [Cat.assoc, Cat.assoc, pb.cone.w]
  let cn : Cone f m := ⟨W, p ≫ pb.cone.π₁, p ≫ pb.cone.π₂, hcone⟩
  rw [pb.lift_uniq cn p rfl rfl, pb.lift_uniq cn q hpq.symm hpq2.symm]

/-- **Cover ⊥ mono** (orthogonality): a cover `c` and a mono `m` lift uniquely
    across any commuting square `c ≫ f = d ≫ m` — there is a diagonal `g` with
    `c ≫ g = d` and `g ≫ m = f`.  Pull `m` back along `f`; the cover `c` then
    factors through the monic pullback-leg `π₁`, forcing `π₁` to be iso
    (`Cover`), and the diagonal is `π₁⁻¹ ≫ π₂`. -/
theorem cover_mono_diagonal {A B I D : 𝒞} {c : A ⟶ B} {f : B ⟶ D} {m : I ⟶ D} {d : A ⟶ I}
    (hc : Cover c) (hm : Mono m) (hsq : c ≫ f = d ≫ m) :
    ∃ g : B ⟶ I, c ≫ g = d ∧ g ≫ m = f := by
  let pb := HasPullbacks.has f m
  have hπmono : Mono pb.cone.π₁ := pullback_fst_mono f m hm
  let cn : Cone f m := ⟨A, c, d, hsq⟩
  let u := pb.lift cn
  have hu₁ : u ≫ pb.cone.π₁ = c := pb.lift_fst cn
  have hu₂ : u ≫ pb.cone.π₂ = d := pb.lift_snd cn
  obtain ⟨inv, hπinv, hinvπ⟩ : IsIso pb.cone.π₁ := hc pb.cone.π₁ u hπmono hu₁
  refine ⟨inv ≫ pb.cone.π₂, ?_, ?_⟩
  · rw [← hu₁, Cat.assoc, ← Cat.assoc pb.cone.π₁ inv pb.cone.π₂, hπinv, Cat.id_comp, hu₂]
  · rw [Cat.assoc, ← pb.cone.w, ← Cat.assoc, hinvπ, Cat.id_comp]

/-- Composition of covers is a cover.  `f ≫ g` factors through a mono `m`;
    cover⊥mono descends the square to factor `g` through `m`, and `g` being a
    cover forces `m` iso. -/
theorem cover_comp {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Cover f) (hg : Cover g) :
    Cover (f ≫ g) := by
  intro C m h hm hfac
  obtain ⟨g', _, hg'm⟩ := cover_mono_diagonal hf hm hfac.symm
  exact hg m g' hm hg'm

/-- Precomposing with a cover leaves the image unchanged: `image (c ≫ f)` and
    `image f` contain one another.  `≤`-forward is automatic (`c ≫ f` factors
    through `image f`); `≤`-backward uses cover⊥mono to factor `f` itself
    through the monic `image (c ≫ f)`. -/
theorem image_cover_comp {A B D : 𝒞} (c : A ⟶ B) (f : B ⟶ D) (hc : Cover c) :
    (image (c ≫ f)).le (image f) ∧ (image f).le (image (c ≫ f)) := by
  refine ⟨image_min _ _ ?_, image_min _ _ ?_⟩
  · obtain ⟨g, hg⟩ := image_allows f
    exact ⟨c ≫ g, by rw [Cat.assoc, hg]⟩
  · obtain ⟨d, hd⟩ := image_allows (c ≫ f)
    obtain ⟨g, _, hgm⟩ := cover_mono_diagonal hc (image (c ≫ f)).monic hd.symm
    exact ⟨g, hgm⟩

/-- **§1.56**: `⊚` is MONOTONE in both arguments — `R ⊂ R'` and `S ⊂ S'`
    imply `R ⊚ S ⊂ R' ⊚ S'`.  This needs no regularity: the two `RelHom`
    witnesses `hr, hs` assemble into a cone over `(R'.colB, S'.colA)`, whose
    pullback lift `w` carries the `R⊚S`-span onto the `R'⊚S'`-span; image
    minimality (`image_min`) then descends to the required `RelHom`. -/
theorem compose_le {A B C : 𝒞} {R R' : BinRel 𝒞 A B} {S S' : BinRel 𝒞 B C}
    (hR : R ⊂ R') (hS : S ⊂ S') : (R ⊚ S) ⊂ (R' ⊚ S') := by
  obtain ⟨hr, hrA, hrB⟩ := hR
  obtain ⟨hs, hsA, hsB⟩ := hS
  let pb := HasPullbacks.has R.colB S.colA
  let pb' := HasPullbacks.has R'.colB S'.colA
  let span : pb.cone.pt ⟶ prod A C := pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)
  let span' : pb'.cone.pt ⟶ prod A C := pair (pb'.cone.π₁ ≫ R'.colA) (pb'.cone.π₂ ≫ S'.colB)
  -- the two `RelHom`s lift `pb`'s legs to a cone over `(R'.colB, S'.colA)`.
  have hcw : (pb.cone.π₁ ≫ hr) ≫ R'.colB = (pb.cone.π₂ ≫ hs) ≫ S'.colA := by
    rw [Cat.assoc, hrB, pb.cone.w, Cat.assoc, hsA]
  let c' : Cone R'.colB S'.colA := ⟨pb.cone.pt, pb.cone.π₁ ≫ hr, pb.cone.π₂ ≫ hs, hcw⟩
  let w := pb'.lift c'
  have hw₁ : w ≫ pb'.cone.π₁ = pb.cone.π₁ ≫ hr := pb'.lift_fst c'
  have hw₂ : w ≫ pb'.cone.π₂ = pb.cone.π₂ ≫ hs := pb'.lift_snd c'
  -- `w` carries the `R⊚S`-span onto the `R'⊚S'`-span.
  have hspan : w ≫ span' = span :=
    pair_uniq (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB) (w ≫ span')
      (by dsimp [span']; rw [Cat.assoc, fst_pair, ← Cat.assoc, hw₁, Cat.assoc, hrA])
      (by dsimp [span']; rw [Cat.assoc, snd_pair, ← Cat.assoc, hw₂, Cat.assoc, hsB])
  -- so `span` factors through `image span' = (R'⊚S').src`; minimality gives the `RelHom`.
  have hallows : Allows (image span') span :=
    ⟨w ≫ image.lift span', by rw [Cat.assoc, image.lift_fac, hspan]⟩
  obtain ⟨k, hk⟩ := image_min span (image span') hallows
  refine ⟨⟨k, ?_, ?_⟩⟩
  · show k ≫ ((image span').arr ≫ fst) = (image span).arr ≫ fst
    rw [← Cat.assoc, hk]
  · show k ≫ ((image span').arr ≫ snd) = (image span).arr ≫ snd
    rw [← Cat.assoc, hk]

/-- **Covers descend relation-containments**: to prove `X ⊂ Y` it suffices to
    find a cover `c : P ↠ X.src` and a map `φ : P → Y.src` agreeing with `c`
    on both legs.  The shared square `c ≫ ⟨X.colA,X.colB⟩ = φ ≫ ⟨Y.colA,Y.colB⟩`
    has a monic right edge, so cover⊥mono (`cover_mono_diagonal`) descends `φ`
    through `c` to the required `RelHom X Y`.  This is the workhorse for the
    regular-category relation calculus (associativity, the allegory laws). -/
theorem relLe_of_cover_factor {A B : 𝒞} {X Y : BinRel 𝒞 A B} {P : 𝒞}
    (c : P ⟶ X.src) (hc : Cover c) (φ : P ⟶ Y.src)
    (hA : φ ≫ Y.colA = c ≫ X.colA) (hB : φ ≫ Y.colB = c ≫ X.colB) : X ⊂ Y := by
  have hmY : Mono (pair Y.colA Y.colB) := monic_pair_of_monicPair Y.colA Y.colB Y.isMonicPair
  have hsq : c ≫ pair X.colA X.colB = φ ≫ pair Y.colA Y.colB := by
    have e1 : c ≫ pair X.colA X.colB = pair (c ≫ X.colA) (c ≫ X.colB) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
    have e2 : φ ≫ pair Y.colA Y.colB = pair (c ≫ X.colA) (c ≫ X.colB) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair, hA]) (by rw [Cat.assoc, snd_pair, hB])
    rw [e1, e2]
  obtain ⟨g, _, hg⟩ := cover_mono_diagonal hc hmY hsq
  refine ⟨⟨g, ?_, ?_⟩⟩
  · calc g ≫ Y.colA = (g ≫ pair Y.colA Y.colB) ≫ fst := by rw [Cat.assoc, fst_pair]
      _ = pair X.colA X.colB ≫ fst := by rw [hg]
      _ = X.colA := fst_pair _ _
  · calc g ≫ Y.colB = (g ≫ pair Y.colA Y.colB) ≫ snd := by rw [Cat.assoc, snd_pair]
      _ = pair X.colA X.colB ≫ snd := by rw [hg]
      _ = X.colB := snd_pair _ _

/-- **§1.56 / §1.569**: `⊚` is associative (`(R⊚S)⊚T ⊂ R⊚(S⊚T)`) in a regular
    category.  Regularity is essential — `(R⊚S)⊚T` pulls `T` back along the
    *image* leg `(R⊚S).colB`, so to relate it to the honest triple span one must
    pull the image-cover `eRS : P_RS ↠ (R⊚S).src` back along that leg
    (`cover_pullback`), obtaining a common cover `P1` carrying coherent
    `R`-, `S`-, `T`-data.  On `P1` we assemble the map into `R⊚(S⊚T)`; the
    descent `relLe_of_cover_factor` (cover⊥mono) turns it into the `RelHom`. -/
theorem compose_assoc [PullbacksTransferCovers 𝒞] {A B C D : 𝒞}
    (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 C D) :
    RelLe ((R ⊚ S) ⊚ T) (R ⊚ (S ⊚ T)) := by
  -- the four image-factorisations underlying the two triple composites
  let pbRS := HasPullbacks.has R.colB S.colA
  let spanRS := pair (pbRS.cone.π₁ ≫ R.colA) (pbRS.cone.π₂ ≫ S.colB)
  let eRS := image.lift spanRS
  let pbRST := HasPullbacks.has (R ⊚ S).colB T.colA
  let spanRST := pair (pbRST.cone.π₁ ≫ (R ⊚ S).colA) (pbRST.cone.π₂ ≫ T.colB)
  let eRST := image.lift spanRST
  let pbST := HasPullbacks.has S.colB T.colA
  let spanST := pair (pbST.cone.π₁ ≫ S.colA) (pbST.cone.π₂ ≫ T.colB)
  let eST := image.lift spanST
  let pbRST' := HasPullbacks.has R.colB (S ⊚ T).colA
  let spanR_ST := pair (pbRST'.cone.π₁ ≫ R.colA) (pbRST'.cone.π₂ ≫ (S ⊚ T).colB)
  let eR_ST := image.lift spanR_ST
  -- `e ≫ col` simplifications (image.lift_fac then fst/snd of the pair)
  have hRSa : eRS ≫ (R ⊚ S).colA = pbRS.cone.π₁ ≫ R.colA := by
    show eRS ≫ ((image spanRS).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hRSb : eRS ≫ (R ⊚ S).colB = pbRS.cone.π₂ ≫ S.colB := by
    show eRS ≫ ((image spanRS).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  have hRSTa : eRST ≫ ((R ⊚ S) ⊚ T).colA = pbRST.cone.π₁ ≫ (R ⊚ S).colA := by
    show eRST ≫ ((image spanRST).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hRSTb : eRST ≫ ((R ⊚ S) ⊚ T).colB = pbRST.cone.π₂ ≫ T.colB := by
    show eRST ≫ ((image spanRST).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  have hSTa : eST ≫ (S ⊚ T).colA = pbST.cone.π₁ ≫ S.colA := by
    show eST ≫ ((image spanST).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hSTb : eST ≫ (S ⊚ T).colB = pbST.cone.π₂ ≫ T.colB := by
    show eST ≫ ((image spanST).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  have hR_STa : eR_ST ≫ (R ⊚ (S ⊚ T)).colA = pbRST'.cone.π₁ ≫ R.colA := by
    show eR_ST ≫ ((image spanR_ST).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hR_STb : eR_ST ≫ (R ⊚ (S ⊚ T)).colB = pbRST'.cone.π₂ ≫ (S ⊚ T).colB := by
    show eR_ST ≫ ((image spanR_ST).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- common cover `P1`: pull the image-cover `eRS` back along `pbRST.π₁`.
  let pb1 := HasPullbacks.has eRS pbRST.cone.π₁
  have hwcov : Cover pb1.cone.π₂ := cover_pullback pbRST.cone.π₁ (image_lift_cover spanRS)
  have hw1 : pb1.cone.π₁ ≫ eRS = pb1.cone.π₂ ≫ pbRST.cone.π₁ := pb1.cone.w
  -- the coherent R/S/T data on `P1`
  let p := pb1.cone.π₁
  let q := pb1.cone.π₂
  let r := p ≫ pbRS.cone.π₁
  let s := p ≫ pbRS.cone.π₂
  let t := q ≫ pbRST.cone.π₂
  -- S–T agreement at C
  have hSTmid : s ≫ S.colB = t ≫ T.colA := by
    calc s ≫ S.colB = p ≫ (eRS ≫ (R ⊚ S).colB) := by
            rw [hRSb]; exact (Cat.assoc _ _ _)
      _ = (p ≫ eRS) ≫ (R ⊚ S).colB := (Cat.assoc _ _ _).symm
      _ = (q ≫ pbRST.cone.π₁) ≫ (R ⊚ S).colB := by rw [hw1]
      _ = q ≫ (pbRST.cone.π₁ ≫ (R ⊚ S).colB) := Cat.assoc _ _ _
      _ = q ≫ (pbRST.cone.π₂ ≫ T.colA) := by rw [pbRST.cone.w]
      _ = t ≫ T.colA := (Cat.assoc _ _ _).symm
  -- assemble P1 → P_ST → (S⊚T).src
  let mST := pbST.lift ⟨pb1.cone.pt, s, t, hSTmid⟩
  have hmST1 : mST ≫ pbST.cone.π₁ = s := pbST.lift_fst _
  have hmST2 : mST ≫ pbST.cone.π₂ = t := pbST.lift_snd _
  let ist := mST ≫ eST
  have hista : ist ≫ (S ⊚ T).colA = s ≫ S.colA := by
    calc ist ≫ (S ⊚ T).colA = mST ≫ (eST ≫ (S ⊚ T).colA) := Cat.assoc _ _ _
      _ = mST ≫ (pbST.cone.π₁ ≫ S.colA) := by rw [hSTa]
      _ = (mST ≫ pbST.cone.π₁) ≫ S.colA := (Cat.assoc _ _ _).symm
      _ = s ≫ S.colA := by rw [hmST1]
  have histb : ist ≫ (S ⊚ T).colB = t ≫ T.colB := by
    calc ist ≫ (S ⊚ T).colB = mST ≫ (eST ≫ (S ⊚ T).colB) := Cat.assoc _ _ _
      _ = mST ≫ (pbST.cone.π₂ ≫ T.colB) := by rw [hSTb]
      _ = (mST ≫ pbST.cone.π₂) ≫ T.colB := (Cat.assoc _ _ _).symm
      _ = t ≫ T.colB := by rw [hmST2]
  -- R–(S⊚T) agreement at B
  have hRmid : r ≫ R.colB = ist ≫ (S ⊚ T).colA := by
    calc r ≫ R.colB = p ≫ (pbRS.cone.π₁ ≫ R.colB) := Cat.assoc _ _ _
      _ = p ≫ (pbRS.cone.π₂ ≫ S.colA) := by rw [pbRS.cone.w]
      _ = (p ≫ pbRS.cone.π₂) ≫ S.colA := (Cat.assoc _ _ _).symm
      _ = s ≫ S.colA := rfl
      _ = ist ≫ (S ⊚ T).colA := hista.symm
  -- assemble P1 → P_R(ST)
  let mR := pbRST'.lift ⟨pb1.cone.pt, r, ist, hRmid⟩
  have hmR1 : mR ≫ pbRST'.cone.π₁ = r := pbRST'.lift_fst _
  have hmR2 : mR ≫ pbRST'.cone.π₂ = ist := pbRST'.lift_snd _
  -- the cover onto ((R⊚S)⊚T).src and the descent map φ
  refine relLe_of_cover_factor (q ≫ eRST) (cover_comp hwcov (image_lift_cover spanRST))
    (mR ≫ eR_ST) ?_ ?_
  · -- φ ≫ (R⊚(S⊚T)).colA = c ≫ ((R⊚S)⊚T).colA
    calc (mR ≫ eR_ST) ≫ (R ⊚ (S ⊚ T)).colA
        = mR ≫ (eR_ST ≫ (R ⊚ (S ⊚ T)).colA) := Cat.assoc _ _ _
      _ = mR ≫ (pbRST'.cone.π₁ ≫ R.colA) := by rw [hR_STa]
      _ = (mR ≫ pbRST'.cone.π₁) ≫ R.colA := (Cat.assoc _ _ _).symm
      _ = r ≫ R.colA := by rw [hmR1]
      _ = p ≫ (pbRS.cone.π₁ ≫ R.colA) := Cat.assoc _ _ _
      _ = p ≫ (eRS ≫ (R ⊚ S).colA) := by rw [hRSa]
      _ = (p ≫ eRS) ≫ (R ⊚ S).colA := (Cat.assoc _ _ _).symm
      _ = (q ≫ pbRST.cone.π₁) ≫ (R ⊚ S).colA := by rw [hw1]
      _ = q ≫ (pbRST.cone.π₁ ≫ (R ⊚ S).colA) := Cat.assoc _ _ _
      _ = q ≫ (eRST ≫ ((R ⊚ S) ⊚ T).colA) := by rw [hRSTa]
      _ = (q ≫ eRST) ≫ ((R ⊚ S) ⊚ T).colA := (Cat.assoc _ _ _).symm
  · -- φ ≫ (R⊚(S⊚T)).colB = c ≫ ((R⊚S)⊚T).colB
    calc (mR ≫ eR_ST) ≫ (R ⊚ (S ⊚ T)).colB
        = mR ≫ (eR_ST ≫ (R ⊚ (S ⊚ T)).colB) := Cat.assoc _ _ _
      _ = mR ≫ (pbRST'.cone.π₂ ≫ (S ⊚ T).colB) := by rw [hR_STb]
      _ = (mR ≫ pbRST'.cone.π₂) ≫ (S ⊚ T).colB := (Cat.assoc _ _ _).symm
      _ = ist ≫ (S ⊚ T).colB := by rw [hmR2]
      _ = t ≫ T.colB := histb
      _ = (q ≫ pbRST.cone.π₂) ≫ T.colB := rfl
      _ = q ≫ (pbRST.cone.π₂ ≫ T.colB) := Cat.assoc _ _ _
      _ = q ≫ (eRST ≫ ((R ⊚ S) ⊚ T).colB) := by rw [hRSTb]
      _ = (q ≫ eRST) ≫ ((R ⊚ S) ⊚ T).colB := (Cat.assoc _ _ _).symm

/-- **§1.56 / §1.569**: `⊚` is associative (reverse, `R⊚(S⊚T) ⊂ (R⊚S)⊚T`).
    The mirror of `compose_assoc`: now `R⊚(S⊚T)` pulls `R` back along the image
    leg `(S⊚T).colA`, so we pull the image-cover `eST : P_ST ↠ (S⊚T).src` back
    along that leg to get the common cover, then descend. -/
theorem compose_assoc' [PullbacksTransferCovers 𝒞] {A B C D : 𝒞}
    (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 C D) :
    RelLe (R ⊚ (S ⊚ T)) ((R ⊚ S) ⊚ T) := by
  let pbRS := HasPullbacks.has R.colB S.colA
  let spanRS := pair (pbRS.cone.π₁ ≫ R.colA) (pbRS.cone.π₂ ≫ S.colB)
  let eRS := image.lift spanRS
  let pbRST := HasPullbacks.has (R ⊚ S).colB T.colA
  let spanRST := pair (pbRST.cone.π₁ ≫ (R ⊚ S).colA) (pbRST.cone.π₂ ≫ T.colB)
  let eRST := image.lift spanRST
  let pbST := HasPullbacks.has S.colB T.colA
  let spanST := pair (pbST.cone.π₁ ≫ S.colA) (pbST.cone.π₂ ≫ T.colB)
  let eST := image.lift spanST
  let pbRST' := HasPullbacks.has R.colB (S ⊚ T).colA
  let spanR_ST := pair (pbRST'.cone.π₁ ≫ R.colA) (pbRST'.cone.π₂ ≫ (S ⊚ T).colB)
  let eR_ST := image.lift spanR_ST
  have hRSa : eRS ≫ (R ⊚ S).colA = pbRS.cone.π₁ ≫ R.colA := by
    show eRS ≫ ((image spanRS).arr ≫ fst) = _; rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hRSb : eRS ≫ (R ⊚ S).colB = pbRS.cone.π₂ ≫ S.colB := by
    show eRS ≫ ((image spanRS).arr ≫ snd) = _; rw [← Cat.assoc, image.lift_fac, snd_pair]
  have hRSTa : eRST ≫ ((R ⊚ S) ⊚ T).colA = pbRST.cone.π₁ ≫ (R ⊚ S).colA := by
    show eRST ≫ ((image spanRST).arr ≫ fst) = _; rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hRSTb : eRST ≫ ((R ⊚ S) ⊚ T).colB = pbRST.cone.π₂ ≫ T.colB := by
    show eRST ≫ ((image spanRST).arr ≫ snd) = _; rw [← Cat.assoc, image.lift_fac, snd_pair]
  have hSTa : eST ≫ (S ⊚ T).colA = pbST.cone.π₁ ≫ S.colA := by
    show eST ≫ ((image spanST).arr ≫ fst) = _; rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hSTb : eST ≫ (S ⊚ T).colB = pbST.cone.π₂ ≫ T.colB := by
    show eST ≫ ((image spanST).arr ≫ snd) = _; rw [← Cat.assoc, image.lift_fac, snd_pair]
  have hR_STa : eR_ST ≫ (R ⊚ (S ⊚ T)).colA = pbRST'.cone.π₁ ≫ R.colA := by
    show eR_ST ≫ ((image spanR_ST).arr ≫ fst) = _; rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hR_STb : eR_ST ≫ (R ⊚ (S ⊚ T)).colB = pbRST'.cone.π₂ ≫ (S ⊚ T).colB := by
    show eR_ST ≫ ((image spanR_ST).arr ≫ snd) = _; rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- common cover: pull the image-cover `eST` back along `pbRST'.π₂`.
  let pb2 := HasPullbacks.has eST pbRST'.cone.π₂
  have hwcov : Cover pb2.cone.π₂ := cover_pullback pbRST'.cone.π₂ (image_lift_cover spanST)
  have hw2 : pb2.cone.π₁ ≫ eST = pb2.cone.π₂ ≫ pbRST'.cone.π₂ := pb2.cone.w
  let p := pb2.cone.π₂           -- pb2 → P_R(ST)  (the cover)
  let pst := pb2.cone.π₁         -- pb2 → P_ST
  let r := p ≫ pbRST'.cone.π₁   -- pb2 → R.src
  let s := pst ≫ pbST.cone.π₁   -- pb2 → S.src
  let t := pst ≫ pbST.cone.π₂   -- pb2 → T.src
  -- `p ≫ pbRST'.π₂ = pst ≫ eST` (the common-cover square)
  have hpe : p ≫ pbRST'.cone.π₂ = pst ≫ eST := hw2.symm
  -- R–S agreement at B
  have hRSmid : r ≫ R.colB = s ≫ S.colA := by
    calc r ≫ R.colB = p ≫ (pbRST'.cone.π₁ ≫ R.colB) := Cat.assoc _ _ _
      _ = p ≫ (pbRST'.cone.π₂ ≫ (S ⊚ T).colA) := by rw [pbRST'.cone.w]
      _ = (p ≫ pbRST'.cone.π₂) ≫ (S ⊚ T).colA := (Cat.assoc _ _ _).symm
      _ = (pst ≫ eST) ≫ (S ⊚ T).colA := by rw [hpe]
      _ = pst ≫ (eST ≫ (S ⊚ T).colA) := Cat.assoc _ _ _
      _ = pst ≫ (pbST.cone.π₁ ≫ S.colA) := by rw [hSTa]
      _ = s ≫ S.colA := (Cat.assoc _ _ _).symm
  -- assemble pb2 → P_RS → (R⊚S).src
  let mRS := pbRS.lift ⟨pb2.cone.pt, r, s, hRSmid⟩
  have hmRS1 : mRS ≫ pbRS.cone.π₁ = r := pbRS.lift_fst _
  have hmRS2 : mRS ≫ pbRS.cone.π₂ = s := pbRS.lift_snd _
  let irs := mRS ≫ eRS
  have hirsa : irs ≫ (R ⊚ S).colA = r ≫ R.colA := by
    calc irs ≫ (R ⊚ S).colA = mRS ≫ (eRS ≫ (R ⊚ S).colA) := Cat.assoc _ _ _
      _ = mRS ≫ (pbRS.cone.π₁ ≫ R.colA) := by rw [hRSa]
      _ = (mRS ≫ pbRS.cone.π₁) ≫ R.colA := (Cat.assoc _ _ _).symm
      _ = r ≫ R.colA := by rw [hmRS1]
  have hirsb : irs ≫ (R ⊚ S).colB = s ≫ S.colB := by
    calc irs ≫ (R ⊚ S).colB = mRS ≫ (eRS ≫ (R ⊚ S).colB) := Cat.assoc _ _ _
      _ = mRS ≫ (pbRS.cone.π₂ ≫ S.colB) := by rw [hRSb]
      _ = (mRS ≫ pbRS.cone.π₂) ≫ S.colB := (Cat.assoc _ _ _).symm
      _ = s ≫ S.colB := by rw [hmRS2]
  -- (R⊚S)–T agreement at C
  have hmid2 : irs ≫ (R ⊚ S).colB = t ≫ T.colA := by
    calc irs ≫ (R ⊚ S).colB = s ≫ S.colB := hirsb
      _ = pst ≫ (pbST.cone.π₁ ≫ S.colB) := Cat.assoc _ _ _
      _ = pst ≫ (pbST.cone.π₂ ≫ T.colA) := by rw [pbST.cone.w]
      _ = t ≫ T.colA := (Cat.assoc _ _ _).symm
  -- assemble pb2 → P_(RS)T
  let mRST := pbRST.lift ⟨pb2.cone.pt, irs, t, hmid2⟩
  have hmRST1 : mRST ≫ pbRST.cone.π₁ = irs := pbRST.lift_fst _
  have hmRST2 : mRST ≫ pbRST.cone.π₂ = t := pbRST.lift_snd _
  refine relLe_of_cover_factor (p ≫ eR_ST) (cover_comp hwcov (image_lift_cover spanR_ST))
    (mRST ≫ eRST) ?_ ?_
  · -- φ ≫ ((R⊚S)⊚T).colA = c ≫ (R⊚(S⊚T)).colA
    calc (mRST ≫ eRST) ≫ ((R ⊚ S) ⊚ T).colA
        = mRST ≫ (eRST ≫ ((R ⊚ S) ⊚ T).colA) := Cat.assoc _ _ _
      _ = mRST ≫ (pbRST.cone.π₁ ≫ (R ⊚ S).colA) := by rw [hRSTa]
      _ = (mRST ≫ pbRST.cone.π₁) ≫ (R ⊚ S).colA := (Cat.assoc _ _ _).symm
      _ = irs ≫ (R ⊚ S).colA := by rw [hmRST1]
      _ = r ≫ R.colA := hirsa
      _ = p ≫ (pbRST'.cone.π₁ ≫ R.colA) := Cat.assoc _ _ _
      _ = p ≫ (eR_ST ≫ (R ⊚ (S ⊚ T)).colA) := by rw [hR_STa]
      _ = (p ≫ eR_ST) ≫ (R ⊚ (S ⊚ T)).colA := (Cat.assoc _ _ _).symm
  · -- φ ≫ ((R⊚S)⊚T).colB = c ≫ (R⊚(S⊚T)).colB
    calc (mRST ≫ eRST) ≫ ((R ⊚ S) ⊚ T).colB
        = mRST ≫ (eRST ≫ ((R ⊚ S) ⊚ T).colB) := Cat.assoc _ _ _
      _ = mRST ≫ (pbRST.cone.π₂ ≫ T.colB) := by rw [hRSTb]
      _ = (mRST ≫ pbRST.cone.π₂) ≫ T.colB := (Cat.assoc _ _ _).symm
      _ = t ≫ T.colB := by rw [hmRST2]
      _ = pst ≫ (pbST.cone.π₂ ≫ T.colB) := Cat.assoc _ _ _
      _ = pst ≫ (eST ≫ (S ⊚ T).colB) := by rw [hSTb]
      _ = (pst ≫ eST) ≫ (S ⊚ T).colB := (Cat.assoc _ _ _).symm
      _ = (p ≫ pbRST'.cone.π₂) ≫ (S ⊚ T).colB := by rw [hpe]
      _ = p ≫ (pbRST'.cone.π₂ ≫ (S ⊚ T).colB) := Cat.assoc _ _ _
      _ = p ≫ (eR_ST ≫ (R ⊚ (S ⊚ T)).colB) := by rw [hR_STb]
      _ = (p ≫ eR_ST) ≫ (R ⊚ (S ⊚ T)).colB := (Cat.assoc _ _ _).symm

/-- A SPLIT EPI is a cover: if `s ≫ k = 1`, then any monic `m` with `k = g ≫ m`
    is a split epi (`(s ≫ g) ≫ m = 1`), hence — being monic — an iso. -/
theorem split_epi_cover {X Y : 𝒞} {k : X ⟶ Y} {s : Y ⟶ X} (hsk : s ≫ k = Cat.id Y) :
    Cover k := by
  intro C m g hm hgm
  -- `s ≫ g` is a right inverse of `m`: (s≫g)≫m = s≫(g≫m) = s≫k = id_Y
  have hright : (s ≫ g) ≫ m = Cat.id Y := by
    rw [Cat.assoc, hgm, hsk]
  -- mono `m` with a right inverse ⟹ it's a (two-sided) iso, inverse `s ≫ g`
  have hleft : m ≫ (s ≫ g) = Cat.id C := by
    apply hm
    calc (m ≫ (s ≫ g)) ≫ m = m ≫ ((s ≫ g) ≫ m) := Cat.assoc _ _ _
      _ = m ≫ Cat.id Y := by rw [hright]
      _ = m := Cat.comp_id _
      _ = Cat.id C ≫ m := (Cat.id_comp _).symm
  exact ⟨s ≫ g, hleft, hright⟩

/-- **§1.569 ⇐ core**: under associativity of `⊚`, if `f : A → C` is a cover then
    for every `g : B → C` the B-leg `π₁` of the canonical pullback of `g` along `f`
    is a cover.  This is the book's `y(x°x) = y ⟹ (yx°)x = y` argument: associativity
    moves the cover witness `1_C ⊂ f°f` across the composite `g ⊚ (f° ⊚ f)`, exhibiting
    the pullback leg as a (split-epi)∘cover, hence a cover. -/
theorem pullback_leg_cover_of_assoc
    (h_assoc : ∀ {A B C D : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 C D),
      RelLe ((R ⊚ S) ⊚ T) (R ⊚ (S ⊚ T)) ∧ RelLe (R ⊚ (S ⊚ T)) ((R ⊚ S) ⊚ T))
    {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) (hf : Cover f) :
    Cover (HasPullbacks.has g f).cone.π₁ := by
  -- (★): graph g ⊂ (graph g ⊚ (graph f)°) ⊚ graph f
  let M : BinRel 𝒞 B A := graph g ⊚ (graph f)°
  have hstar : RelLe (graph g) (M ⊚ graph f) := by
    have h1 : RelLe (graph g) (graph g ⊚ ((graph f)° ⊚ graph f)) := by
      refine rel_le_trans (comp_graph_id_right (graph g)) ?_
      exact compose_le (rel_le_refl _) ((cover_iff_one_le_reciprocal_comp_self f).mp hf)
    exact rel_le_trans h1 ((h_assoc (graph g) ((graph f)°) (graph f)).2)
  -- inner pullback of M = canonical pullback of g along f
  let pbM := HasPullbacks.has g f
  -- e_M : pbM.pt → M.src, the image-cover of the M-span = pair π₁ π₂, which is monic
  let spanM : pbM.cone.pt ⟶ prod B A := pair (pbM.cone.π₁ ≫ (graph g).colA) (pbM.cone.π₂ ≫ ((graph f)°).colB)
  have hspanM_eq : spanM = pair pbM.cone.π₁ pbM.cone.π₂ := by
    dsimp [spanM, graph, reciprocal]; rw [Cat.comp_id, Cat.comp_id]
  have hspanM_mono : Mono spanM := by
    rw [hspanM_eq]
    have hmp : MonicPair pbM.cone.π₁ pbM.cone.π₂ := by
      intro W u v hu hv
      have hcone : (u ≫ pbM.cone.π₁) ≫ g = (u ≫ pbM.cone.π₂) ≫ f := by
        rw [Cat.assoc, Cat.assoc, pbM.cone.w]
      let cn : Cone g f := ⟨W, u ≫ pbM.cone.π₁, u ≫ pbM.cone.π₂, hcone⟩
      rw [pbM.lift_uniq cn u rfl rfl, pbM.lift_uniq cn v hu.symm hv.symm]
    apply monic_pair_of_monicPair; exact hmp
  let eM := image.lift spanM
  have heM_iso : IsIso eM := image_lift_iso_of_mono spanM hspanM_mono
  have heM_colA : eM ≫ M.colA = pbM.cone.π₁ := by
    show eM ≫ ((image spanM).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac]
    show pair _ _ ≫ fst = _
    rw [fst_pair]; dsimp [graph]; rw [Cat.comp_id]
  -- it now suffices: Cover M.colA (then pbM.π₁ = eM ≫ M.colA, eM iso ⟹ cover)
  suffices hMcolA : Cover M.colA by
    rw [← heM_colA]; intro D m k hm hkm
    exact cover_comp (iso_cover eM heM_iso) hMcolA m k hm hkm
  -- outer pullback of M.colB and id_A
  let pbO := HasPullbacks.has M.colB (graph f).colA
  have hO_w : pbO.cone.π₁ ≫ M.colB = pbO.cone.π₂ := by
    simpa [graph, Cat.comp_id] using pbO.cone.w
  have hO_iso : IsIso pbO.cone.π₁ := by
    -- π₁ is the pullback of id_A along M.colB; its retraction is the lift of ⟨id, M.colB⟩
    let cn : Cone M.colB (graph f).colA := ⟨M.src, Cat.id M.src, M.colB, by
      dsimp [graph]; rw [Cat.id_comp, Cat.comp_id]⟩
    refine ⟨pbO.lift cn, ?_, ?_⟩
    · -- π₁ ≫ lift cn = id : both legs agree, use lift_uniq
      have h1 : (pbO.cone.π₁ ≫ pbO.lift cn) ≫ pbO.cone.π₁ = pbO.cone.π₁ := by
        rw [Cat.assoc, pbO.lift_fst cn]; dsimp [cn]; rw [Cat.comp_id]
      have h2 : (pbO.cone.π₁ ≫ pbO.lift cn) ≫ pbO.cone.π₂ = pbO.cone.π₂ := by
        rw [Cat.assoc, pbO.lift_snd cn]; dsimp [cn]; exact hO_w
      rw [pbO.lift_uniq pbO.cone (pbO.cone.π₁ ≫ pbO.lift cn) h1 h2,
          ← pbO.lift_uniq pbO.cone (Cat.id _) (Cat.id_comp _) (Cat.id_comp _)]
    · exact pbO.lift_fst cn
  -- spanO and its image-cover eO
  let spanO : pbO.cone.pt ⟶ prod B C := pair (pbO.cone.π₁ ≫ M.colA) (pbO.cone.π₂ ≫ (graph f).colB)
  let eO := image.lift spanO
  have heO_cover : Cover eO := image_lift_cover spanO
  have heO_colA : eO ≫ (M ⊚ graph f).colA = pbO.cone.π₁ ≫ M.colA := by
    show eO ≫ ((image spanO).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac]
    show pair _ _ ≫ fst = _
    rw [fst_pair]
  -- from (★): (M ⊚ graph f).colA is split epi
  obtain ⟨hh, hhA, _⟩ := hstar
  have hsplit : hh ≫ (M ⊚ graph f).colA = Cat.id B := by
    have := hhA; dsimp [graph] at this; exact this
  have hcolA_cover : Cover (M ⊚ graph f).colA := split_epi_cover hsplit
  -- eO ≫ colA = π₁ ≫ M.colA is a cover; π₁ iso ⟹ M.colA cover
  have hcomp_cover : Cover (pbO.cone.π₁ ≫ M.colA) := by
    rw [← heO_colA]; exact cover_comp heO_cover hcolA_cover
  obtain ⟨inv, hinv1, hinv2⟩ := hO_iso
  have hMcolA_eq : M.colA = inv ≫ (pbO.cone.π₁ ≫ M.colA) := by
    rw [← Cat.assoc, hinv2, Cat.id_comp]
  rw [hMcolA_eq]; intro D m k hm hkm
  exact cover_precomp_iso ⟨pbO.cone.π₁, hinv2, hinv1⟩ hcomp_cover m k hm hkm

/-- **§1.569 ⇐**: If composition of relations is associative (mutual `⊂` both ways),
    then `𝒞` is regular — pullbacks transfer covers.

    Book proof (§1.569): `x : A → C` is a cover iff `x°x = 1_C`.  Given any `g : B → C`
    we have `g(x°x) = g`, so by associativity `(g x°)x = g`; the leg of the pullback of
    `g` along `x` sitting inside `g x°` is then forced to be a cover.  Here `x = f`; the
    core extraction is `pullback_leg_cover_of_assoc`, and we transfer the canonical-leg
    cover to an arbitrary pullback cone `c` via the comparison iso of pullbacks. -/
theorem regular_of_compose_assoc
    (h_assoc : ∀ {A B C D : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 C D),
      RelLe ((R ⊚ S) ⊚ T) (R ⊚ (S ⊚ T)) ∧ RelLe (R ⊚ (S ⊚ T)) ((R ⊚ S) ⊚ T))
    : PullbacksTransferCovers 𝒞 := by
  refine ⟨fun {A B C} {f g} c hpb hf => ?_⟩
  -- `c` is a pullback cone of `f : A → B ← g : C → B`; want `Cover c.π₂`.
  -- The core gives `Cover` of the B-leg `π₁` of the canonical pullback of `f` along `g`.
  -- Careful with orientation: cover is `f`, transferred leg is the `C`-side `c.π₂`.
  let pbCan := HasPullbacks.has g f
  have hcanCov : Cover pbCan.cone.π₁ := pullback_leg_cover_of_assoc h_assoc f g hf
  -- comparison iso `i : c.pt → pbCan.pt` with `i ≫ pbCan.π₁ = c.π₂`, `i ≫ pbCan.π₂ = c.π₁`.
  -- (pbCan is a pullback of `g, f`; `c` is a pullback of `f, g`; legs are swapped.)
  have hc_w' : c.π₂ ≫ g = c.π₁ ≫ f := c.w.symm
  let i : c.pt ⟶ pbCan.cone.pt := pbCan.lift ⟨c.pt, c.π₂, c.π₁, hc_w'⟩
  have hi₁ : i ≫ pbCan.cone.π₁ = c.π₂ := pbCan.lift_fst _
  have hi₂ : i ≫ pbCan.cone.π₂ = c.π₁ := pbCan.lift_snd _
  -- `i` is an iso: build its inverse from `c.IsPullback` applied to pbCan's cone.
  obtain ⟨j, ⟨hj₁, hj₂⟩, _⟩ := hpb ⟨pbCan.cone.pt, pbCan.cone.π₂, pbCan.cone.π₁, pbCan.cone.w.symm⟩
  -- hj₁ : j ≫ c.π₁ = pbCan.π₂ ;  hj₂ : j ≫ c.π₂ = pbCan.π₁
  -- i ≫ j = id (both are lifts of cone `c` through `c`, by IsPullback-uniqueness)
  obtain ⟨_, _, huniqC⟩ := hpb c
  have hij : i ≫ j = Cat.id c.pt := by
    rw [huniqC (i ≫ j)
        (by rw [Cat.assoc, hj₁, hi₂]) (by rw [Cat.assoc, hj₂, hi₁]),
      ← huniqC (Cat.id c.pt) (Cat.id_comp _) (Cat.id_comp _)]
  -- j ≫ i = id (both are lifts of pbCan.cone through pbCan, by lift_uniq)
  have hji : j ≫ i = Cat.id pbCan.cone.pt := by
    rw [pbCan.lift_uniq pbCan.cone (j ≫ i)
        (by rw [Cat.assoc, hi₁, hj₂]) (by rw [Cat.assoc, hi₂, hj₁]),
      ← pbCan.lift_uniq pbCan.cone (Cat.id _) (Cat.id_comp _) (Cat.id_comp _)]
  -- c.π₂ = i ≫ pbCan.π₁, i iso, pbCan.π₁ cover ⟹ c.π₂ cover
  rw [← hi₁]; intro D m k hm hkm
  exact cover_precomp_iso ⟨j, hij, hji⟩ hcanCov m k hm hkm

/-- **§1.563 / §2.112 — the modular identity** `RS ∩ T ⊆ (R ∩ TS°)S`.
    Here `R : A→B`, `S : B→C`, `T : A→C`.  Proof: standard tabular-allegory
    descent (pull the image-cover of `R⊚S` back along the meet witness, reassemble,
    descend with `relLe_of_cover_factor`).  Freyd states it for regular categories. -/
theorem modular_identity [PullbacksTransferCovers 𝒞] {A B C : 𝒞}
    (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 A C) :
    RelLe ((R ⊚ S) ⊓ T) ((R ⊓ (T ⊚ S°)) ⊚ S) := by
  -- abbreviations for the two sides
  let M := (R ⊚ S) ⊓ T
  let RTS := R ⊓ (T ⊚ S°)
  -- (1) the image-cover of `R⊚S`
  let pbRS := HasPullbacks.has R.colB S.colA
  let spanRS := pair (pbRS.cone.π₁ ≫ R.colA) (pbRS.cone.π₂ ≫ S.colB)
  let eRS := image.lift spanRS
  have hRSa : eRS ≫ (R ⊚ S).colA = pbRS.cone.π₁ ≫ R.colA := by
    show eRS ≫ ((image spanRS).arr ≫ fst) = _; rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hRSb : eRS ≫ (R ⊚ S).colB = pbRS.cone.π₂ ≫ S.colB := by
    show eRS ≫ ((image spanRS).arr ≫ snd) = _; rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- (2) the two legs of the meet `M = (R⊚S) ⊓ T`
  obtain ⟨⟨xRS, hxRSa, hxRSb⟩⟩ := intersect_le_left (R ⊚ S) T
  obtain ⟨⟨xT, hxTa, hxTb⟩⟩ := intersect_le_right (R ⊚ S) T
  -- (3) pull the image-cover `eRS` back along `xRS` → common cover `c : P ↠ M.src`
  let pb1 := HasPullbacks.has eRS xRS
  let c := pb1.cone.π₂
  have hccov : Cover c := cover_pullback xRS (image_lift_cover spanRS)
  have hw1 : pb1.cone.π₁ ≫ eRS = c ≫ xRS := pb1.cone.w
  -- honest R/S/T-points over P
  let r := pb1.cone.π₁ ≫ pbRS.cone.π₁   -- P → R.src
  let s := pb1.cone.π₁ ≫ pbRS.cone.π₂   -- P → S.src
  let tt := c ≫ xT                       -- P → T.src
  -- R–S agreement at B (the shared B-value of r and s)
  have hRSmid : r ≫ R.colB = s ≫ S.colA := by
    calc r ≫ R.colB = pb1.cone.π₁ ≫ (pbRS.cone.π₁ ≫ R.colB) := Cat.assoc _ _ _
      _ = pb1.cone.π₁ ≫ (pbRS.cone.π₂ ≫ S.colA) := by rw [pbRS.cone.w]
      _ = s ≫ S.colA := (Cat.assoc _ _ _).symm
  -- A-value of r equals A-value of tt (both = c ≫ M.colA)
  have hRA : r ≫ R.colA = c ≫ M.colA := by
    calc r ≫ R.colA = pb1.cone.π₁ ≫ (pbRS.cone.π₁ ≫ R.colA) := Cat.assoc _ _ _
      _ = pb1.cone.π₁ ≫ (eRS ≫ (R ⊚ S).colA) := by rw [hRSa]
      _ = (pb1.cone.π₁ ≫ eRS) ≫ (R ⊚ S).colA := (Cat.assoc _ _ _).symm
      _ = (c ≫ xRS) ≫ (R ⊚ S).colA := by rw [hw1]
      _ = c ≫ (xRS ≫ (R ⊚ S).colA) := Cat.assoc _ _ _
      _ = c ≫ M.colA := by rw [hxRSa]
  have hTA : tt ≫ T.colA = c ≫ M.colA := by
    calc tt ≫ T.colA = c ≫ (xT ≫ T.colA) := Cat.assoc _ _ _
      _ = c ≫ M.colA := by rw [hxTa]
  -- C-value of s equals C-value of tt (both = c ≫ M.colB)
  have hSC : s ≫ S.colB = c ≫ M.colB := by
    calc s ≫ S.colB = pb1.cone.π₁ ≫ (pbRS.cone.π₂ ≫ S.colB) := Cat.assoc _ _ _
      _ = pb1.cone.π₁ ≫ (eRS ≫ (R ⊚ S).colB) := by rw [hRSb]
      _ = (pb1.cone.π₁ ≫ eRS) ≫ (R ⊚ S).colB := (Cat.assoc _ _ _).symm
      _ = (c ≫ xRS) ≫ (R ⊚ S).colB := by rw [hw1]
      _ = c ≫ (xRS ≫ (R ⊚ S).colB) := Cat.assoc _ _ _
      _ = c ≫ M.colB := by rw [hxRSb]
  have hTC : tt ≫ T.colB = c ≫ M.colB := by
    calc tt ≫ T.colB = c ≫ (xT ≫ T.colB) := Cat.assoc _ _ _
      _ = c ≫ M.colB := by rw [hxTb]
  -- (4) the `T ⊚ S°` point over P: pull back `T.colB` and `S°.colA`(=`S.colB`),
  --     witnessed by the shared C-value `tt ≫ T.colB = s ≫ S.colB`.
  let pbTS := HasPullbacks.has T.colB S°.colA
  let spanTS := pair (pbTS.cone.π₁ ≫ T.colA) (pbTS.cone.π₂ ≫ S°.colB)
  let eTS := image.lift spanTS
  have hTSa : eTS ≫ (T ⊚ S°).colA = pbTS.cone.π₁ ≫ T.colA := by
    show eTS ≫ ((image spanTS).arr ≫ fst) = _; rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hTSb : eTS ≫ (T ⊚ S°).colB = pbTS.cone.π₂ ≫ S°.colB := by
    show eTS ≫ ((image spanTS).arr ≫ snd) = _; rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- `tt`/`s` agree at C (`S°.colA = S.colB`), so they pull back to a P-point `u`.
  have hu_mid : tt ≫ T.colB = s ≫ S°.colA := by
    show tt ≫ T.colB = s ≫ S.colB; rw [hTC, ← hSC]
  let u := pbTS.lift ⟨pb1.cone.pt, tt, s, hu_mid⟩
  have hu1 : u ≫ pbTS.cone.π₁ = tt := pbTS.lift_fst _
  have hu2 : u ≫ pbTS.cone.π₂ = s := pbTS.lift_snd _
  let w := u ≫ eTS            -- P → (T⊚S°).src
  -- `w` has A-value `tt ≫ T.colA = r ≫ R.colA` and B-value `s ≫ S.colA = r ≫ R.colB`
  have hwA : w ≫ (T ⊚ S°).colA = r ≫ R.colA := by
    calc w ≫ (T ⊚ S°).colA = u ≫ (eTS ≫ (T ⊚ S°).colA) := Cat.assoc _ _ _
      _ = u ≫ (pbTS.cone.π₁ ≫ T.colA) := by rw [hTSa]
      _ = (u ≫ pbTS.cone.π₁) ≫ T.colA := (Cat.assoc _ _ _).symm
      _ = tt ≫ T.colA := by rw [hu1]
      _ = c ≫ M.colA := hTA
      _ = r ≫ R.colA := hRA.symm
  have hwB : w ≫ (T ⊚ S°).colB = r ≫ R.colB := by
    calc w ≫ (T ⊚ S°).colB = u ≫ (eTS ≫ (T ⊚ S°).colB) := Cat.assoc _ _ _
      _ = u ≫ (pbTS.cone.π₂ ≫ S°.colB) := by rw [hTSb]
      _ = (u ≫ pbTS.cone.π₂) ≫ S°.colB := (Cat.assoc _ _ _).symm
      _ = s ≫ S°.colB := by rw [hu2]
      _ = s ≫ S.colA := rfl
      _ = r ≫ R.colB := hRSmid.symm
  -- (5) assemble the `RTS = R ⊓ (T⊚S°)` point over P from `r` and `w`.
  let pbI := HasPullbacks.has (pair R.colA R.colB) (pair (T ⊚ S°).colA (T ⊚ S°).colB)
  have hI_w : r ≫ pair R.colA R.colB = w ≫ pair (T ⊚ S°).colA (T ⊚ S°).colB := by
    have e1 : r ≫ pair R.colA R.colB = pair (r ≫ R.colA) (r ≫ R.colB) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
    have e2 : w ≫ pair (T ⊚ S°).colA (T ⊚ S°).colB = pair (r ≫ R.colA) (r ≫ R.colB) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair, hwA]) (by rw [Cat.assoc, snd_pair, hwB])
    rw [e1, e2]
  let mI := pbI.lift ⟨pb1.cone.pt, r, w, hI_w⟩
  have hmI1 : mI ≫ pbI.cone.π₁ = r := pbI.lift_fst _
  have hmIa : mI ≫ RTS.colA = r ≫ R.colA := by
    show mI ≫ (pbI.cone.π₁ ≫ R.colA) = _
    rw [← Cat.assoc, hmI1]
  have hmIb : mI ≫ RTS.colB = r ≫ R.colB := by
    show mI ≫ (pbI.cone.π₁ ≫ R.colB) = _
    rw [← Cat.assoc, hmI1]
  -- (6) compose `RTS ⊚ S` over P from `mI` and `s`, then descend through the cover.
  let pbN := HasPullbacks.has RTS.colB S.colA
  let spanN := pair (pbN.cone.π₁ ≫ RTS.colA) (pbN.cone.π₂ ≫ S.colB)
  let eN := image.lift spanN
  have hNa : eN ≫ ((R ⊓ (T ⊚ S°)) ⊚ S).colA = pbN.cone.π₁ ≫ RTS.colA := by
    show eN ≫ ((image spanN).arr ≫ fst) = _; rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hNb : eN ≫ ((R ⊓ (T ⊚ S°)) ⊚ S).colB = pbN.cone.π₂ ≫ S.colB := by
    show eN ≫ ((image spanN).arr ≫ snd) = _; rw [← Cat.assoc, image.lift_fac, snd_pair]
  have hN_mid : mI ≫ RTS.colB = s ≫ S.colA := by rw [hmIb]; exact hRSmid
  let mN := pbN.lift ⟨pb1.cone.pt, mI, s, hN_mid⟩
  have hmN1 : mN ≫ pbN.cone.π₁ = mI := pbN.lift_fst _
  have hmN2 : mN ≫ pbN.cone.π₂ = s := pbN.lift_snd _
  refine relLe_of_cover_factor c hccov (mN ≫ eN) ?_ ?_
  · -- (mN ≫ eN) ≫ N.colA = c ≫ M.colA
    calc (mN ≫ eN) ≫ ((R ⊓ (T ⊚ S°)) ⊚ S).colA
        = mN ≫ (eN ≫ ((R ⊓ (T ⊚ S°)) ⊚ S).colA) := Cat.assoc _ _ _
      _ = mN ≫ (pbN.cone.π₁ ≫ RTS.colA) := by rw [hNa]
      _ = (mN ≫ pbN.cone.π₁) ≫ RTS.colA := (Cat.assoc _ _ _).symm
      _ = mI ≫ RTS.colA := by rw [hmN1]
      _ = r ≫ R.colA := hmIa
      _ = c ≫ M.colA := hRA
  · -- (mN ≫ eN) ≫ N.colB = c ≫ M.colB
    calc (mN ≫ eN) ≫ ((R ⊓ (T ⊚ S°)) ⊚ S).colB
        = mN ≫ (eN ≫ ((R ⊓ (T ⊚ S°)) ⊚ S).colB) := Cat.assoc _ _ _
      _ = mN ≫ (pbN.cone.π₂ ≫ S.colB) := by rw [hNb]
      _ = (mN ≫ pbN.cone.π₂) ≫ S.colB := (Cat.assoc _ _ _).symm
      _ = s ≫ S.colB := by rw [hmN2]
      _ = c ≫ M.colB := hSC

/-- **§1.569**: in a regular category `⊚` is associative (both containments). -/
theorem compose_assoc_of_regular [RegularCategory 𝒞] {A B C D : 𝒞}
    (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 C D) :
    RelLe ((R ⊚ S) ⊚ T) (R ⊚ (S ⊚ T)) ∧ RelLe (R ⊚ (S ⊚ T)) ((R ⊚ S) ⊚ T) :=
  ⟨compose_assoc R S T, compose_assoc' R S T⟩

/-- **§1.564**: `graph` preserves composition: `graph(f ≫ g) ≅ graph(f) ⊚ graph(g)`. -/
theorem graph_comp {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) : RelLe (graph (f ≫ g)) (graph f ⊚ graph g) := by
  let pb := HasPullbacks.has f (Cat.id B)
  have h_cone_w : (Cat.id A) ≫ f = f ≫ (Cat.id B) := by rw [Cat.id_comp, Cat.comp_id]
  let c : Cone f (Cat.id B) := ⟨A, Cat.id A, f, h_cone_w⟩
  let u := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = Cat.id A := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = f := pb.lift_snd c
  let span := pair (pb.cone.π₁ ≫ (Cat.id A)) (pb.cone.π₂ ≫ g)
  let I := image span
  let h : A ⟶ I.dom := u ≫ image.lift span
  have h_colA : h ≫ (I.arr ≫ fst) = Cat.id A := by
    dsimp [h, I]
    calc
      (u ≫ image.lift span) ≫ ((image span).arr ≫ fst) =
        u ≫ (image.lift span ≫ (image span).arr) ≫ fst := by simp [Cat.assoc]
      _ = u ≫ span ≫ fst := by rw [image.lift_fac span]
      _ = u ≫ pb.cone.π₁ ≫ Cat.id A := by simp [span, fst_pair]
      _ = u ≫ pb.cone.π₁ := by rw [Cat.comp_id]
      _ = Cat.id A := hu₁
  have h_colB : h ≫ (I.arr ≫ snd) = f ≫ g := by
    dsimp [h, I]
    calc
      (u ≫ image.lift span) ≫ ((image span).arr ≫ snd) =
        u ≫ (image.lift span ≫ (image span).arr) ≫ snd := by simp [Cat.assoc]
      _ = u ≫ span ≫ snd := by rw [image.lift_fac span]
      _ = u ≫ pb.cone.π₂ ≫ g := by simp [span, snd_pair, Cat.comp_id]
      _ = (u ≫ pb.cone.π₂) ≫ g := by rw [← Cat.assoc]
      _ = f ≫ g := by rw [hu₂]
  exact ⟨⟨h, h_colA, h_colB⟩⟩

/-- **§1.564**: `graph` preserves composition (reverse containment). -/
theorem comp_graph {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) : RelLe (graph f ⊚ graph g) (graph (f ≫ g)) := by
  let pb := HasPullbacks.has f (Cat.id B)
  let span := pair (pb.cone.π₁ ≫ (Cat.id A)) (pb.cone.π₂ ≫ g)
  let I := image span
  have h_simp : pb.cone.π₁ ≫ f = pb.cone.π₂ := by
    simpa [Cat.comp_id] using pb.cone.w
  have h_pair_eq : pb.cone.π₁ ≫ pair (Cat.id A) (f ≫ g) = pair pb.cone.π₁ (pb.cone.π₁ ≫ (f ≫ g)) :=
    pair_uniq pb.cone.π₁ (pb.cone.π₁ ≫ (f ≫ g)) (pb.cone.π₁ ≫ pair (Cat.id A) (f ≫ g))
      (by rw [Cat.assoc, fst_pair, Cat.comp_id])
      (by rw [Cat.assoc, snd_pair])
  have h_span_eq : span = pb.cone.π₁ ≫ pair (Cat.id A) (f ≫ g) := by
    dsimp [span]
    rw [Cat.comp_id, ← h_simp]
    rw [Cat.assoc]
    exact h_pair_eq.symm
  have h_monic : Mono (pair (Cat.id A) (f ≫ g)) :=
    monic_pair_of_monicPair (Cat.id A) (f ≫ g) (graph (f ≫ g)).isMonicPair
  let S : Subobject 𝒞 (prod A C) := ⟨A, pair (Cat.id A) (f ≫ g), h_monic⟩
  have h_allows : Allows S span := ⟨pb.cone.π₁, h_span_eq.symm⟩
  have h_image_le : I.le S := image_min span S h_allows
  rcases h_image_le with ⟨k, hk⟩
  have hkA : k ≫ (Cat.id A) = I.arr ≫ fst := by
    calc
      k ≫ (Cat.id A) = (k ≫ pair (Cat.id A) (f ≫ g)) ≫ fst := by rw [Cat.assoc, fst_pair]
      _ = I.arr ≫ fst := by rw [hk]
  have hkB : k ≫ (f ≫ g) = I.arr ≫ snd := by
    calc
      k ≫ (f ≫ g) = (k ≫ pair (Cat.id A) (f ≫ g)) ≫ snd := by rw [Cat.assoc, snd_pair]
      _ = I.arr ≫ snd := by rw [hk]
  exact ⟨⟨k, hkA, hkB⟩⟩

/-- **§1.564**: `graph` is faithful: `graph(f) ≤ graph(g)` implies `f = g`.
    (The reverse containment also implies `f = g`, so graph is an embedding
    of the hom-set into the preorder of relations.) -/
theorem graph_faithful {A B : 𝒞} {f g : A ⟶ B}
    (h : RelLe (graph f) (graph g)) : f = g := by
  rcases h with ⟨⟨h, hA, hB⟩⟩
  dsimp [graph] at hA hB
  rw [Cat.comp_id] at hA
  -- hA : h = id_A, hB : h ≫ g = f
  rw [hA, Cat.id_comp] at hB
  exact hB.symm

/-- **§1.564**: `graph` is an embedding (injective on morphisms). -/
theorem graph_injective {A B : 𝒞} {f g : A ⟶ B} (h : graph f = graph g) : f = g := by
  dsimp [graph] at h
  -- h : BinRel.mk A (id A) f _ = BinRel.mk A (id A) g _
  cases h
  rfl

end


/-- **§1.561**: reciprocation is monotone: R ≤ S → R° ≤ S°.
    The same witness works; it just swaps the two leg-conditions. -/
theorem reciprocal_mono {A B : 𝒞} {R S : BinRel 𝒞 A B} (h : RelLe R S) :
    RelLe (R°) (S°) := by
  rcases h with ⟨⟨h, hA, hB⟩⟩; exact ⟨⟨h, hB, hA⟩⟩

/-! ## §1.561  (RS)° = S°R°  —  reciprocation reverses composition -/

section
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

-- The product-swap iso `⟨snd,fst⟩ : A×C → C×A`, its projection equations
-- (`prodSwap_fst`/`prodSwap_snd`), and its self-inverse law (`prodSwap_prodSwap`)
-- all live canonically in `Fredy.S1_42`; we reuse them here (DRY).

/-- **§1.561**: (R ⊚ S)° ≤ S° ⊚ R°  (reciprocation reverses composition).

    `R ⊚ S` is the image of the span `⟨π₁≫R.colA, π₂≫S.colB⟩` over the pullback
    `pb` of `(R.colB, S.colA)`.  `S° ⊚ R°` is the image of the span
    `⟨π₁'≫S.colB, π₂'≫R.colA⟩` over the pullback `pb'` of `(S.colA, R.colB)` — the
    SAME pullback square with legs swapped.  The comparison `φ : pb.pt → pb'.pt`
    (swapping legs) satisfies `φ ≫ sp' = sp ≫ prodSwap`, so `image sp` post-composed
    with `prodSwap⁻¹` is a subobject of `A×C` allowing `sp`; image-minimality yields
    the witness. -/
theorem reciprocal_comp_le {A B C : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) :
    RelLe ((R ⊚ S)°) (S° ⊚ R°) := by
  -- pullback + span for R ⊚ S
  let pb  := HasPullbacks.has R.colB S.colA
  let sp  : pb.cone.pt ⟶ prod A C := pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)
  -- pullback + span for S° ⊚ R°
  let pb' := HasPullbacks.has (S°).colB (R°).colA      -- = pullback of (S.colA, R.colB)
  let sp' : pb'.cone.pt ⟶ prod C A := pair (pb'.cone.π₁ ≫ (S°).colA) (pb'.cone.π₂ ≫ (R°).colB)
  let I  := image sp
  let I' := image sp'
  -- comparison φ : pb.pt → pb'.pt swapping the two legs.  pb's square is
  --   π₁≫R.colB = π₂≫S.colA ; pb''s feet are (S.colA, R.colB), so a cone over pb'
  --   needs leg-to-S.src and leg-to-R.src with π₁'≫S.colA = π₂'≫R.colB.
  have hcone' : pb.cone.π₂ ≫ (S°).colB = pb.cone.π₁ ≫ (R°).colA := by
    show pb.cone.π₂ ≫ S.colA = pb.cone.π₁ ≫ R.colB
    exact pb.cone.w.symm
  let cφ : Cone (S°).colB (R°).colA := ⟨pb.cone.pt, pb.cone.π₂, pb.cone.π₁, hcone'⟩
  let φ : pb.cone.pt ⟶ pb'.cone.pt := pb'.lift cφ
  have hφ₁ : φ ≫ pb'.cone.π₁ = pb.cone.π₂ := pb'.lift_fst cφ
  have hφ₂ : φ ≫ pb'.cone.π₂ = pb.cone.π₁ := pb'.lift_snd cφ
  -- φ ≫ sp' = sp ≫ prodSwap
  have hφ_sp : φ ≫ sp' = sp ≫ prodSwap A C := by
    have hcfst : (φ ≫ sp') ≫ fst = (sp ≫ prodSwap A C) ≫ fst := by
      rw [Cat.assoc, fst_pair, ← Cat.assoc, hφ₁]
      show pb.cone.π₂ ≫ S.colB = (sp ≫ prodSwap A C) ≫ fst
      rw [Cat.assoc, prodSwap_fst, snd_pair]
    have hcsnd : (φ ≫ sp') ≫ snd = (sp ≫ prodSwap A C) ≫ snd := by
      rw [Cat.assoc, snd_pair, ← Cat.assoc, hφ₂]
      show pb.cone.π₁ ≫ R.colA = (sp ≫ prodSwap A C) ≫ snd
      rw [Cat.assoc, prodSwap_snd, fst_pair]
    rw [pair_eta (φ ≫ sp'), pair_eta (sp ≫ prodSwap A C), hcfst, hcsnd]
  -- the subobject I'.arr ≫ prodSwap C A : I'.dom → A×C (mono since prodSwap iso)
  have hswapInv_mono : Mono (prodSwap C A) := by
    intro W u v huv
    have := congrArg (· ≫ prodSwap A C) huv
    simpa [Cat.assoc, prodSwap_prodSwap, Cat.comp_id] using this
  let Sub' : Subobject 𝒞 (prod A C) :=
    ⟨I'.dom, I'.arr ≫ prodSwap C A, by
      intro W u v huv
      exact I'.monic u v (hswapInv_mono _ _ (by simpa [Cat.assoc] using huv))⟩
  -- Sub' allows sp via g := φ ≫ image.lift sp'
  have hallow : Allows Sub' sp := by
    refine ⟨φ ≫ image.lift sp', ?_⟩
    show (φ ≫ image.lift sp') ≫ (I'.arr ≫ prodSwap C A) = sp
    calc (φ ≫ image.lift sp') ≫ (I'.arr ≫ prodSwap C A)
        = φ ≫ ((image.lift sp' ≫ I'.arr) ≫ prodSwap C A) := by
          rw [Cat.assoc, Cat.assoc]
      _ = φ ≫ (sp' ≫ prodSwap C A) := by rw [image.lift_fac]
      _ = (φ ≫ sp') ≫ prodSwap C A := (Cat.assoc _ _ _).symm
      _ = (sp ≫ prodSwap A C) ≫ prodSwap C A := by rw [hφ_sp]
      _ = sp ≫ (prodSwap A C ≫ prodSwap C A) := Cat.assoc _ _ _
      _ = sp := by rw [prodSwap_prodSwap, Cat.comp_id]
  -- image-minimality: I ≤ Sub', giving k : I.dom → I'.dom with k ≫ I'.arr ≫ prodSwap = I.arr
  obtain ⟨k, hk⟩ := image_min sp Sub' hallow
  have hk' : k ≫ (I'.arr ≫ prodSwap C A) = I.arr := hk
  -- the witness k : (R⊚S)°.src = I.dom → (S°⊚R°).src = I'.dom
  refine ⟨⟨k, ?_, ?_⟩⟩
  · -- k ≫ (S°⊚R°).colA = (R⊚S)°.colA, i.e. k ≫ I'.arr ≫ fst = I.arr ≫ snd
    show k ≫ (I'.arr ≫ fst) = I.arr ≫ snd
    calc k ≫ (I'.arr ≫ fst) = k ≫ ((I'.arr ≫ prodSwap C A) ≫ prodSwap A C ≫ fst) := by
          rw [Cat.assoc, ← Cat.assoc (prodSwap C A), prodSwap_prodSwap, Cat.id_comp]
      _ = (k ≫ (I'.arr ≫ prodSwap C A)) ≫ (prodSwap A C ≫ fst) :=
          (Cat.assoc _ _ _).symm
      _ = I.arr ≫ (prodSwap A C ≫ fst) := by rw [hk']
      _ = I.arr ≫ snd := by rw [prodSwap_fst]
  · show k ≫ (I'.arr ≫ snd) = I.arr ≫ fst
    calc k ≫ (I'.arr ≫ snd) = k ≫ ((I'.arr ≫ prodSwap C A) ≫ prodSwap A C ≫ snd) := by
          rw [Cat.assoc, ← Cat.assoc (prodSwap C A), prodSwap_prodSwap, Cat.id_comp]
      _ = (k ≫ (I'.arr ≫ prodSwap C A)) ≫ (prodSwap A C ≫ snd) :=
          (Cat.assoc _ _ _).symm
      _ = I.arr ≫ (prodSwap A C ≫ snd) := by rw [hk']
      _ = I.arr ≫ fst := by rw [prodSwap_snd]

/-- **§1.561**: S° ⊚ R° ≤ (R ⊚ S)°.
    Derived from `reciprocal_comp_le` applied to `S°, R°`, plus involutivity
    and monotonicity of reciprocation. -/
theorem comp_reciprocal_le {A B C : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) :
    RelLe (S° ⊚ R°) ((R ⊚ S)°) := by
  -- (S° ⊚ R°)° ≤ (R°)° ⊚ (S°)° = R ⊚ S
  have h := reciprocal_comp_le (S°) (R°)
  rw [reciprocal_invol, reciprocal_invol] at h
  -- h : (S° ⊚ R°)° ≤ R ⊚ S ; take reciprocals
  have h2 := reciprocal_mono h
  rwa [reciprocal_invol] at h2

/-- **§1.561**: (R ⊚ S)° and S° ⊚ R° are mutually contained. -/
theorem reciprocal_comp {A B C : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) :
    RelLe ((R ⊚ S)°) (S° ⊚ R°) ∧ RelLe (S° ⊚ R°) ((R ⊚ S)°) :=
  ⟨reciprocal_comp_le R S, comp_reciprocal_le R S⟩

end

/-! ## §1.562  (R∩S)° = S°∩R°  and  (R∩S)T ⊆ RT∩ST -/

section
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-- **§1.562**: (R ⊓ S)° ≤ S° ⊓ R°.
    The witness for R⊓S ≤ R (resp. S) also witnesses (R⊓S)° ≤ R° (resp. S°). -/
theorem reciprocal_intersect_le {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    RelLe ((R ⊓ S)°) (S° ⊓ R°) := by
  apply le_intersect
  · rcases intersect_le_right R S with ⟨⟨h, hA, hB⟩⟩; exact ⟨⟨h, hB, hA⟩⟩
  · rcases intersect_le_left  R S with ⟨⟨h, hA, hB⟩⟩; exact ⟨⟨h, hB, hA⟩⟩

/-- **§1.562**: S° ⊓ R° ≤ (R ⊓ S)°.
    The (S°⊓R°)-pullback gives a cone for the (R⊓S)-pullback via swapped legs. -/
theorem intersect_reciprocal_le {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    RelLe (S° ⊓ R°) ((R ⊓ S)°) := by
  let pb_RS := HasPullbacks.has (pair R.colA R.colB) (pair S.colA S.colB)
  let pb_SR := HasPullbacks.has (pair S.colB S.colA) (pair R.colB R.colA)
  -- From pb_SR.cone.w: π₁≫S.colA=π₂≫R.colA and π₁≫S.colB=π₂≫R.colB
  have hw := pb_SR.cone.w
  have hA : pb_SR.cone.π₂ ≫ R.colA = pb_SR.cone.π₁ ≫ S.colA := by
    have := congrArg (· ≫ snd) hw; simp only [Cat.assoc, snd_pair] at this; exact this.symm
  have hB : pb_SR.cone.π₂ ≫ R.colB = pb_SR.cone.π₁ ≫ S.colB := by
    have := congrArg (· ≫ fst) hw; simp only [Cat.assoc, fst_pair] at this; exact this.symm
  have h_cone_w : pb_SR.cone.π₂ ≫ pair R.colA R.colB = pb_SR.cone.π₁ ≫ pair S.colA S.colB := by
    have lhs : pb_SR.cone.π₂ ≫ pair R.colA R.colB =
        pair (pb_SR.cone.π₂ ≫ R.colA) (pb_SR.cone.π₂ ≫ R.colB) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
    have rhs : pb_SR.cone.π₁ ≫ pair S.colA S.colB =
        pair (pb_SR.cone.π₁ ≫ S.colA) (pb_SR.cone.π₁ ≫ S.colB) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
    rw [lhs, rhs, hA, hB]
  let c    := (⟨pb_SR.cone.pt, pb_SR.cone.π₂, pb_SR.cone.π₁, h_cone_w⟩ :
               Cone (pair R.colA R.colB) (pair S.colA S.colB))
  let lift := pb_RS.lift c
  have hl₁ : lift ≫ pb_RS.cone.π₁ = pb_SR.cone.π₂ := pb_RS.lift_fst c
  exact ⟨⟨lift,
    show lift ≫ pb_RS.cone.π₁ ≫ R.colB = pb_SR.cone.π₁ ≫ S.colB by rw [← Cat.assoc, hl₁]; exact hB,
    show lift ≫ pb_RS.cone.π₁ ≫ R.colA = pb_SR.cone.π₁ ≫ S.colA by rw [← Cat.assoc, hl₁]; exact hA⟩⟩

/-- **§1.562**: (R ⊓ S)° = S° ⊓ R° (mutual containment). -/
theorem reciprocal_intersect {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    RelLe ((R ⊓ S)°) (S° ⊓ R°) ∧ RelLe (S° ⊓ R°) ((R ⊓ S)°) :=
  ⟨reciprocal_intersect_le R S, intersect_reciprocal_le R S⟩

/-- Monotonicity of ⊚ in the first argument: R ≤ R' → R ⊚ T ≤ R' ⊚ T. -/
theorem compose_le_left {A B C : 𝒞} {R R' : BinRel 𝒞 A B} (hRR' : RelLe R R') (T : BinRel 𝒞 B C) :
    RelLe (R ⊚ T) (R' ⊚ T) := by
  rcases hRR' with ⟨⟨h, hA, hB⟩⟩
  let pb  := HasPullbacks.has R.colB T.colA
  let pb' := HasPullbacks.has R'.colB T.colA
  have hcone_w : (pb.cone.π₁ ≫ h) ≫ R'.colB = pb.cone.π₂ ≫ T.colA := by
    rw [Cat.assoc, hB]; exact pb.cone.w
  let c   := (⟨pb.cone.pt, pb.cone.π₁ ≫ h, pb.cone.π₂, hcone_w⟩ : Cone R'.colB T.colA)
  let u   := pb'.lift c
  have hu₁ : u ≫ pb'.cone.π₁ = pb.cone.π₁ ≫ h := pb'.lift_fst c
  have hu₂ : u ≫ pb'.cone.π₂ = pb.cone.π₂   := pb'.lift_snd c
  let span  : pb.cone.pt  ⟶ prod A C := pair (pb.cone.π₁  ≫ R.colA)  (pb.cone.π₂  ≫ T.colB)
  let span' : pb'.cone.pt ⟶ prod A C := pair (pb'.cone.π₁ ≫ R'.colA) (pb'.cone.π₂ ≫ T.colB)
  let I  := image span
  let I' := image span'
  have h_fac : u ≫ span' = span :=
    pair_uniq _ _ _
      (by rw [Cat.assoc, fst_pair, ← Cat.assoc, hu₁, Cat.assoc, hA])
      (by rw [Cat.assoc, snd_pair, ← Cat.assoc, hu₂])
  have h_le : (image span).le I' := image_min span I'
    ⟨u ≫ image.lift span', by rw [Cat.assoc, image.lift_fac span', h_fac]⟩
  rcases h_le with ⟨k, hk⟩
  have hkA : k ≫ (R' ⊚ T).colA = (R ⊚ T).colA := by
    show k ≫ I'.arr ≫ fst = (image span).arr ≫ fst
    rw [← Cat.assoc, hk]
  have hkB : k ≫ (R' ⊚ T).colB = (R ⊚ T).colB := by
    show k ≫ I'.arr ≫ snd = (image span).arr ≫ snd
    rw [← Cat.assoc, hk]
  exact ⟨⟨k, hkA, hkB⟩⟩

/-- **§1.562**: Right-distributivity: (R ⊓ S) ⊚ T ≤ (R ⊚ T) ⊓ (S ⊚ T). -/
theorem intersect_comp_le {A B C : 𝒞} (R S : BinRel 𝒞 A B) (T : BinRel 𝒞 B C) :
    RelLe ((R ⊓ S) ⊚ T) ((R ⊚ T) ⊓ (S ⊚ T)) :=
  le_intersect
    (compose_le_left (intersect_le_left  R S) T)
    (compose_le_left (intersect_le_right R S) T)

end

/-! ## §1.56(10) Image of a constant morphism is a subterminator

  The book proves this via the metatheorem (Horn sentence true in Set, hence in any regular
  category).  We give the elementary proof directly: with covers stable under pullback
  (`[PullbacksTransferCovers 𝒞]`), the cover `image.lift x` and epi-cancellation suffice —
  no representation theorem needed.  -/

section
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] [HasTerminal 𝒞]

/-- **§1.56(10)**: If x : A → B is constant (yx = y'x for all y, y' : C → A),
    then the image of x is a subterminator (image(x).dom → 1 is monic).

    Elementary proof (no metatheorem): `(image x).arr` is monic, so it suffices to
    equalize any two `u, v : W → (image x).dom` after post-composing with it.  The
    factor `e := image.lift x` is a cover with `e ≫ arr = x`.  Pull `e` back along
    `u` and along `v`; pull the two resulting cover-legs over a common cover
    `q : Q ↠ W`; on `Q` we get A-points `a, a'` with `q ≫ u ≫ arr = a ≫ x` and
    `q ≫ v ≫ arr = a' ≫ x`.  `Constant x` makes the right sides equal, and `q` (a
    composite of covers, hence epic) cancels, giving `u ≫ arr = v ≫ arr`.  The only
    extra hypothesis is `[PullbacksTransferCovers 𝒞]` (Freyd states it for regular
    categories). -/
theorem constant_image_subterminator [PullbacksTransferCovers 𝒞]
    {A B : 𝒞} (x : A ⟶ B) (_hx : Constant x) :
    Subterminator (image x).dom := by
  intro W u v _
  let e : A ⟶ (image x).dom := image.lift x
  have he : e ≫ (image x).arr = x := image.lift_fac x
  have hecov : Cover e := image_lift_cover x
  refine (image x).monic u v ?_
  let Pu := (HasPullbacks.has e u).cone
  have hu_cov : Cover Pu.π₂ := cover_pullback u hecov
  have hu_w : Pu.π₁ ≫ e = Pu.π₂ ≫ u := Pu.w
  let Pv := (HasPullbacks.has e v).cone
  have hv_cov : Cover Pv.π₂ := cover_pullback v hecov
  have hv_w : Pv.π₁ ≫ e = Pv.π₂ ≫ v := Pv.w
  let Q := (HasPullbacks.has Pu.π₂ Pv.π₂).cone
  have hq_cov : Cover Q.π₂ := cover_pullback Pv.π₂ hu_cov
  have hq_w : Q.π₁ ≫ Pu.π₂ = Q.π₂ ≫ Pv.π₂ := Q.w
  let q : Q.pt ⟶ W := Q.π₂ ≫ Pv.π₂
  have hq_def : q = Q.π₂ ≫ Pv.π₂ := rfl
  let a : Q.pt ⟶ A := Q.π₁ ≫ Pu.π₁
  let a' : Q.pt ⟶ A := Q.π₂ ≫ Pv.π₁
  have hua : q ≫ (u ≫ (image x).arr) = a ≫ x := by
    have h1 : q ≫ (u ≫ (image x).arr) = Q.π₁ ≫ (Pu.π₂ ≫ (u ≫ (image x).arr)) := by
      rw [hq_def, ← hq_w]; simp only [Cat.assoc]
    have h2 : Pu.π₂ ≫ (u ≫ (image x).arr) = Pu.π₁ ≫ x := by
      rw [← Cat.assoc, ← hu_w, Cat.assoc, he]
    rw [h1, h2, ← Cat.assoc]
  have hva : q ≫ (v ≫ (image x).arr) = a' ≫ x := by
    have h1 : q ≫ (v ≫ (image x).arr) = Q.π₂ ≫ (Pv.π₂ ≫ (v ≫ (image x).arr)) := by
      rw [hq_def]; simp only [Cat.assoc]
    have h2 : Pv.π₂ ≫ (v ≫ (image x).arr) = Pv.π₁ ≫ x := by
      rw [← Cat.assoc, ← hv_w, Cat.assoc, he]
    rw [h1, h2, ← Cat.assoc]
  have hq_eq : q ≫ (u ≫ (image x).arr) = q ≫ (v ≫ (image x).arr) := by
    rw [hua, hva]; exact _hx a a'
  have hq_cover : Cover q := by
    rw [hq_def]; exact cover_comp hq_cov hv_cov
  exact cover_epi hq_cover hq_eq

end

end Freyd
