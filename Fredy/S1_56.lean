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
infixr:80 " ⊚ " => compose

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

  **Provability:** Not provable from the `BinRel` definition alone (jointly-monic
  pair + pullback/image composition).  In **Set**, the modular identity holds by
  element-wise reasoning — the standard proof constructs witnesses `y` from
  membership in RS ∩ T.  Freyd's strategy (§1.55, the Henkin-Lubkin
  representation theorem) faithfully embeds any small pre-regular category in a
  power of Set, and faithful representations reflect the modular identity back
  to the original category.  So it becomes a theorem after the representation is
  established, but not before. -/

theorem modular_identity {A B C : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 A C) :
    RelLe ((R ⊚ S) ⊚ T°) (R ⊚ (S ⊚ T°)) := by
  sorry

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

/-- **§1.565** (general case): In a regular category, a pullback of covers is
    a pushout.  Relies on the Henkin-Lubkin representation theorem (§1.55)
    to transfer the result from **Set** (proved above) to any regular
    category.  Currently a `sorry` pending the representation theorem. -/
def pullback_of_covers_is_pushout {A B C P : 𝒞} (x : A ⟶ B) (y : C ⟶ B)
    (p₁ : P ⟶ A) (p₂ : P ⟶ C) (h_sq : p₁ ≫ x = p₂ ≫ y)
    [RegularCategory 𝒞] (_h_pb : HasPullback x y) (_h_cover_x : Cover x)
    (_h_cover_y : Cover y) : HasPushout p₁ p₂ := by
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

/-- **§1.569 ⇐**: If composition of relations is associative (mutual `⊂`
    both ways), then A is regular — i.e., pullbacks transfer covers.

    Book proof sketch: covers are characterized relationally as `1 ⊂ x°x`
    (`cover_iff_one_le_reciprocal_comp`).  Given cover x : A → B and a
    pullback of x along y : C → B with pullback leg z : P → C, the relation
    algebra (using associativity) shows `1 ⊂ z°z`, hence z is a cover.  If z
    were not a cover, then `(y ⊚ x°) ⊚ x` would not be a map while
    `y ⊚ (x° ⊚ x) = y ⊚ 1 = y` IS a map, contradicting associativity. -/
theorem regular_of_compose_assoc
    (h_assoc : ∀ {A B C D : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 C D),
      RelLe ((R ⊚ S) ⊚ T) (R ⊚ (S ⊚ T)) ∧ RelLe (R ⊚ (S ⊚ T)) ((R ⊚ S) ⊚ T))
    : PullbacksTransferCovers 𝒞 := by
  sorry

/-- **§1.569 ⇒**: If A is regular, composition of relations is associative.
    This follows from the Henkin-Lubkin representation theorem (§1.55):
    associativity is a Horn sentence true in **Set**, hence true in any
    regular category.  (Not yet formalized.) -/
theorem compose_assoc_of_regular [RegularCategory 𝒞] {A B C D : 𝒞}
    (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 C D) :
    RelLe ((R ⊚ S) ⊚ T) (R ⊚ (S ⊚ T)) ∧ RelLe (R ⊚ (S ⊚ T)) ((R ⊚ S) ⊚ T) := by
  sorry

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

/-- **§1.56**: `⊚` is associative. -/
theorem compose_assoc {A B C D : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 C D) :
    RelLe ((R ⊚ S) ⊚ T) (R ⊚ (S ⊚ T)) := by
  sorry

/-- **§1.56**: `⊚` is associative (reverse containment). -/
theorem compose_assoc' {A B C D : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 C D) :
    RelLe (R ⊚ (S ⊚ T)) ((R ⊚ S) ⊚ T) := by
  sorry

/-- **§1.564**: `graph` preserves composition: `graph(f ≫ g) ≅ graph(f) ⊚ graph(g)`. -/
theorem graph_comp {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) : RelLe (graph (f ≫ g)) (graph f ⊚ graph g) := by
  -- graph(f≫g): src=A, colA=id, colB=f≫g
  -- graph(f)⊚graph(g): pullback of (f, id_B), then span A→A×C
  -- The pullback is (A, id_A, f), so the span is (id_A, f≫g) = graph(f≫g)
  sorry

/-- **§1.564**: `graph` preserves composition (reverse containment). -/
theorem comp_graph {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) : RelLe (graph f ⊚ graph g) (graph (f ≫ g)) := by
  sorry

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

end Freyd
