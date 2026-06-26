/-
  Freyd & Scedrov, *Categories and Allegories* §2.111 / §2.142 / §2.214
  The bridge Rel(C): relations in a (pre-)regular category form an ALLEGORY.

  This is the Ch1→Ch2 dual of `Fredy/MapCat.lean` (which built `Map(𝒜)` of an
  allegory).  Here we build `Rel(C)` of a category C: its objects are those of C,
  its morphisms `a ⟶ b` are binary relations `BinRel C a b` (§1.56) — taken up to
  mutual containment so the allegory's *equational* laws hold on the nose — with
  composition `⊚`, reciprocal `°`, intersection `⊓`, union `relUnionSub`, all from
  Chapter 1.

  **The quotient.**  `BinRel C a b` is only a PREORDER under `RelLe` (`⊂`): two
  isomorphic tables are mutually contained but not Lean-equal.  The `Allegory` class
  (S2_1) states its laws as *equalities* (`inter_idem`, `recip_comp`, `modular`, …),
  so we quotient `BinRel C a b` by the equivalence "mutual `RelLe`".  Every Ch1
  operation is monotone (`compose_le`, `reciprocal_mono`, `intersect`-UMP, …), hence
  descends to the quotient, and every Ch1 containment lemma becomes the corresponding
  allegory equation via `le_antisymm`.

  **Built (Sorry-free):**
    • `Cat (RelObj C)`            for `[RegularCategory C]`        — §2.111
    • `Allegory (RelObj C)`        for `[RegularCategory C]`        — §2.111 (modular = §2.142)
    • `DistributiveAllegory (RelObj C)` for `[PositivePreLogos C]`  — §2.21
    • §2.214 (positive ⇒ Rel(C) has finite coproducts), forward direction over
      `[DisjointBinaryCoproduct C]`: the full five-equation `Coproduct (RelObj C)` record
      (`relCoproduct`).  Eqs (1),(4) [monic injections], (2),(3) [disjointness], and
      (5) [joint cover, `relGraph_recip_union_eq_id`] are all PROVED.

  This is a BRIDGE file: it imports BOTH Ch1 (BinRel) and Ch2 (Allegory class).  Ch1
  facts are NEVER proved from allegory axioms — only the reverse.
-/

import Fredy.S1_56
import Fredy.S1_60
import Fredy.S1_61
import Fredy.S1_62
import Fredy.S2_1
import Fredy.S2_2
import Fredy.MapCat
import Fredy.MatrixAllegory   -- §2.217(1): the positive reflection Mat(𝒜) (acyclic: Mat imports only S2_*)

open Freyd
open Freyd.Alg

universe v u

namespace Freyd

/-! ## The object type of `Rel(C)`

  A wrapper structure (like `MapObj` is an alias, but we use a `structure` to FORCE a
  distinct `Cat` instance that does not clash with C's own `Cat`/`RegularCategory`). -/

/-- Objects of `Rel(C)`: a wrapper around objects of `C`. -/
structure RelObj (𝒞 : Type u) where
  /-- The underlying object of `C`. -/
  carrier : 𝒞

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## Mutual-containment equivalence on `BinRel`

  `RelLe` (`⊂`) is reflexive (`rel_le_refl`) and transitive (`rel_le_trans`); mutual
  containment is therefore an equivalence.  We quotient by it. -/

section Equiv
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- The setoid on `BinRel C a b`: `R ≈ S` iff `R ⊂ S` and `S ⊂ R`. -/
def relSetoid (a b : 𝒞) : Setoid (BinRel 𝒞 a b) where
  r R S := RelLe R S ∧ RelLe S R
  iseqv :=
    { refl  := fun R => ⟨rel_le_refl R, rel_le_refl R⟩
      symm  := fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩
      trans := fun ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ =>
        ⟨rel_le_trans h₁ h₂, rel_le_trans h₂' h₁'⟩ }

end Equiv

/-! ## The hom-type and its order

  `BinRelQuot C a b := Quotient (relSetoid a b)`.  Containment descends to a genuine
  partial order on the quotient (antisymmetric by construction). -/

section Quot
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- A morphism `a ⟶ b` in `Rel(C)`: an `RelLe`-equivalence class of relations. -/
def BinRelQuot (a b : 𝒞) : Type _ := Quotient (relSetoid (𝒞 := 𝒞) a b)

/-- The canonical class of a relation. -/
def relClass {a b : 𝒞} (R : BinRel 𝒞 a b) : BinRelQuot a b := Quotient.mk _ R

/-- Containment descends to the quotient (well-defined: monotone in both slots). -/
def quotLe {a b : 𝒞} (x y : BinRelQuot (𝒞 := 𝒞) a b) : Prop :=
  Quotient.liftOn₂ x y (fun R S => RelLe R S)
    (fun _ _ _ _ hR hS => propext
      ⟨fun h => rel_le_trans (rel_le_trans hR.2 h) hS.1,
       fun h => rel_le_trans (rel_le_trans hR.1 h) hS.2⟩)

theorem quotLe_refl {a b : 𝒞} (x : BinRelQuot (𝒞 := 𝒞) a b) : quotLe x x :=
  Quotient.inductionOn x (fun R => rel_le_refl R)

theorem quotLe_trans {a b : 𝒞} {x y z : BinRelQuot (𝒞 := 𝒞) a b}
    (h₁ : quotLe x y) (h₂ : quotLe y z) : quotLe x z :=
  Quotient.inductionOn₃ x y z (fun _ _ _ h₁ h₂ => rel_le_trans h₁ h₂) h₁ h₂

/-- Antisymmetry: mutual containment IS Lean equality on the quotient. -/
theorem quotLe_antisymm {a b : 𝒞} {x y : BinRelQuot (𝒞 := 𝒞) a b}
    (h₁ : quotLe x y) (h₂ : quotLe y x) : x = y :=
  Quotient.inductionOn₂ x y (fun _ _ h₁ h₂ => Quotient.sound ⟨h₁, h₂⟩) h₁ h₂

/-- `relClass` is monotone: `R ⊂ S → relClass R ≤ relClass S`. -/
theorem relClass_mono {a b : 𝒞} {R S : BinRel 𝒞 a b} (h : RelLe R S) :
    quotLe (relClass R) (relClass S) := h

end Quot

/-! ## §2.111  `Rel(C)` is a category

  Composition is relation composition `⊚` (diagram order: `relClass R ≫ relClass S`
  is "first R then S"); identity is the graph of `id`.  All three category laws come
  from the Ch1 identity/associativity containments (`graph_id_comp`, `comp_graph_id`,
  `compose_assoc_of_regular`) collapsed by `quotLe_antisymm`. -/

section RelCat
variable [RegularCategory 𝒞]

/-- Composition on the quotient: `[R] ⊚ [S] = [R ⊚ S]`, well-defined by `compose_le`. -/
def qComp {a b c : 𝒞} (x : BinRelQuot (𝒞 := 𝒞) a b) (y : BinRelQuot (𝒞 := 𝒞) b c) :
    BinRelQuot (𝒞 := 𝒞) a c :=
  Quotient.liftOn₂ x y (fun R S => relClass (R ⊚ S))
    (fun _ _ _ _ hR hS => Quotient.sound
      ⟨compose_le hR.1 hS.1, compose_le hR.2 hS.2⟩)

@[simp] theorem qComp_mk {a b c : 𝒞} (R : BinRel 𝒞 a b) (S : BinRel 𝒞 b c) :
    qComp (relClass R) (relClass S) = relClass (R ⊚ S) := rfl

/-- The identity relation `[graph id]`. -/
def relId (a : 𝒞) : BinRelQuot (𝒞 := 𝒞) a a := relClass (graph (Cat.id a))

/-- **§2.111**: `Rel(C)` is a category.  Objects `RelObj C`; homs the `RelLe`-classes. -/
instance (priority := 0) relCat : Cat.{max u v} (RelObj 𝒞) where
  Hom A B := BinRelQuot (𝒞 := 𝒞) A.carrier B.carrier
  id  A   := relId A.carrier
  comp x y := qComp x y
  id_comp {A B} x := by
    refine Quotient.inductionOn x (fun R => ?_)
    exact quotLe_antisymm (graph_id_comp R) (comp_graph_id_left R)
  comp_id {A B} x := by
    refine Quotient.inductionOn x (fun R => ?_)
    exact quotLe_antisymm (comp_graph_id R) (comp_graph_id_right R)
  assoc {A B C D} x y z := by
    refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
    exact quotLe_antisymm (compose_assoc_of_regular R S T).1
      (compose_assoc_of_regular R S T).2

end RelCat

/-! ## §2.111 / §2.142  `Rel(C)` is an allegory

  `°` = `reciprocal`, `∩` = `intersect`.  The semi-lattice laws come from the
  intersection UMP (`intersect_le_*`, `le_intersect`); reciprocation laws from
  `reciprocal_invol`/`reciprocal_comp`/`reciprocal_intersect`; semi-distributivity
  from monotonicity of `⊚`; and the MODULAR law is exactly Freyd's `modular_identity`
  (§1.563 / §2.142 — the crux, holding in any regular C). -/

section RelAllegory
variable [RegularCategory 𝒞]

/-- Reciprocal on the quotient: `[R]° = [R°]`, well-defined by `reciprocal_mono`. -/
def qRecip {a b : 𝒞} (x : BinRelQuot (𝒞 := 𝒞) a b) : BinRelQuot (𝒞 := 𝒞) b a :=
  Quotient.liftOn x (fun R => relClass R°)
    (fun _ _ h => Quotient.sound ⟨reciprocal_mono h.1, reciprocal_mono h.2⟩)

@[simp] theorem qRecip_mk {a b : 𝒞} (R : BinRel 𝒞 a b) :
    qRecip (relClass R) = relClass R° := rfl

/-- Intersection on the quotient: `[R] ∩ [S] = [R ⊓ S]`, well-defined by the meet UMP. -/
def qInter {a b : 𝒞} (x y : BinRelQuot (𝒞 := 𝒞) a b) : BinRelQuot (𝒞 := 𝒞) a b :=
  Quotient.liftOn₂ x y (fun R S => relClass (R ⊓ S))
    (fun _ _ _ _ hR hS => Quotient.sound
      ⟨le_intersect (rel_le_trans (intersect_le_left _ _) hR.1)
          (rel_le_trans (intersect_le_right _ _) hS.1),
       le_intersect (rel_le_trans (intersect_le_left _ _) hR.2)
          (rel_le_trans (intersect_le_right _ _) hS.2)⟩)

@[simp] theorem qInter_mk {a b : 𝒞} (R S : BinRel 𝒞 a b) :
    qInter (relClass R) (relClass S) = relClass (R ⊓ S) := rfl

/-- **§2.111**: `Rel(C)` is an allegory. -/
instance (priority := 0) relAllegory : Allegory.{max u v} (RelObj 𝒞) where
  recip {a b} x := qRecip x
  inter {a b} x y := qInter x y
  -- (R°)° = R  —  a genuine equality from `reciprocal_invol`.
  recip_recip {a b} x := by
    refine Quotient.inductionOn x (fun R => ?_)
    show relClass R°° = relClass R
    rw [reciprocal_invol]
  -- (R ⊚ S)° = S° ⊚ R°
  recip_comp {a b c} x y := by
    refine Quotient.inductionOn₂ x y (fun R S => ?_)
    exact quotLe_antisymm (reciprocal_comp_le R S) (comp_reciprocal_le R S)
  -- (R ⊓ S)° = R° ⊓ S°  (note: book's recip_inter has same-order R°∩S°;
  --  Ch1 gives S°⊓R°, equal by inter_comm — we route via antisymmetry to R°⊓S°).
  recip_inter {a b} x y := by
    refine Quotient.inductionOn₂ x y (fun R S => ?_)
    refine quotLe_antisymm ?_ ?_
    · exact le_intersect
        (reciprocal_mono (intersect_le_left R S)) (reciprocal_mono (intersect_le_right R S))
    · -- R°⊓S° ⊆ (R⊓S)°: factor through S°⊓R° (inter_comm) then intersect_reciprocal_le.
      have w  : RelLe (S° ⊓ R°) ((R ⊓ S)°) := intersect_reciprocal_le R S
      have w' : RelLe (R° ⊓ S°) (S° ⊓ R°) :=
        le_intersect (intersect_le_right (R°) (S°)) (intersect_le_left (R°) (S°))
      exact rel_le_trans w' w
  inter_idem {a b} x := by
    refine Quotient.inductionOn x (fun R => ?_)
    exact quotLe_antisymm (intersect_le_left R R) (le_intersect (rel_le_refl R) (rel_le_refl R))
  inter_comm {a b} x y := by
    refine Quotient.inductionOn₂ x y (fun R S => ?_)
    exact quotLe_antisymm
      (le_intersect (intersect_le_right R S) (intersect_le_left R S))
      (le_intersect (intersect_le_right S R) (intersect_le_left S R))
  inter_assoc {a b} x y z := by
    refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
    refine quotLe_antisymm ?_ ?_
    · exact le_intersect
        (le_intersect (intersect_le_left R _) (rel_le_trans (intersect_le_right R _) (intersect_le_left S T)))
        (rel_le_trans (intersect_le_right R _) (intersect_le_right S T))
    · exact le_intersect
        (rel_le_trans (intersect_le_left _ T) (intersect_le_left R S))
        (le_intersect (rel_le_trans (intersect_le_left _ T) (intersect_le_right R S)) (intersect_le_right _ T))
  -- semi-distributivity: R⊚(S⊓T) = (R⊚S) ⊓ (R⊚(S⊓T)) ⊓ (R⊚T).
  semidistrib {a b c} x y z := by
    refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
    -- LHS = R⊚(S⊓T); RHS = ((R⊚S) ⊓ (R⊚(S⊓T))) ⊓ (R⊚T).
    refine quotLe_antisymm ?_ ?_
    · -- R⊚(S⊓T) ⊆ RHS: below each conjunct by monotonicity.
      exact le_intersect
        (le_intersect (compose_le (rel_le_refl R) (intersect_le_left S T))
          (rel_le_refl _))
        (compose_le (rel_le_refl R) (intersect_le_right S T))
    · -- RHS ⊆ R⊚(S⊓T): the middle conjunct already IS R⊚(S⊓T).
      exact rel_le_trans (intersect_le_left _ _) (intersect_le_right _ _)
  -- modular law: (R⊚S)⊓T = ((R⊚S)⊓T) ⊓ ((R ⊓ (T⊚S°)) ⊚ S).
  modular {a b c} x y z := by
    refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
    refine quotLe_antisymm ?_ ?_
    · -- LHS ⊆ RHS: LHS ⊆ LHS (refl) and LHS ⊆ (R⊓(T⊚S°))⊚S by modular_identity.
      exact le_intersect (rel_le_refl _) (modular_identity R S T)
    · -- RHS ⊆ LHS = (R⊚S)⊓T: the first conjunct.
      exact intersect_le_left _ _

/-- The lattice order `⊑` on `Rel(C)` is exactly the relation containment `quotLe`
    (`= RelLe` on representatives).  `x ⊑ y` unfolds to `x ∩ y = x`, i.e. `[R⊓S] = [R]`,
    i.e. `R⊓S ≈ R`; the nontrivial half is `R ⊑ R⊓S ↔ R ⊑ S` (meet UMP). -/
theorem quotLe_iff_algLe {a b : 𝒞} (x y : BinRelQuot (𝒞 := 𝒞) a b) :
    quotLe x y ↔ Freyd.Alg.le (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) x y := by
  refine Quotient.inductionOn₂ x y (fun R S => ?_)
  show RelLe R S ↔ qInter (relClass R) (relClass S) = relClass R
  rw [qInter_mk]
  constructor
  · intro h
    exact quotLe_antisymm (intersect_le_left R S)
      (le_intersect (rel_le_refl R) h)
  · intro h
    -- [R⊓S] = [R] gives R ⊑ R⊓S, hence R ⊑ S via intersect_le_right.
    have hRRS : quotLe (relClass R) (relClass (R ⊓ S)) := by rw [h]; exact quotLe_refl _
    exact rel_le_trans hRRS (intersect_le_right R S)

end RelAllegory

/-! ## §2.21  `Rel(C)` is a distributive allegory

  For `[PreLogos C]` we add `0` = the empty relation (`subRel` of the bottom subobject
  of `A×B`) and `∪` = `relUnionSub` (the coproduct-free relational union of §1.61).
  The lattice + distributivity laws come from the Ch1 union UMP (`le_relUnionSub`,
  `relUnionSub_le_*`) and the §1.616 distributivity (`compose_relUnionSub_right`, the
  pre-logos `invImage`-preservation).  The zero laws use that the empty relation is the
  global minimum (`bottom_min`) and that composing with it stays empty
  (`invImage_preserves_bottom` + `existsAlong`/`invImage` adjunction). -/

namespace DisjointGluing

open Freyd.DisjointGluing

section RelDistributive
-- A BARE pre-logos (§1.6) now suffices.  The §1.616 `∪ᵣ` (`relUnion`) distributivity lemmas
-- (compose-over-union, meet-over-union, reciprocal-over-union, in S1_60) were re-based on the
-- SUBOBJECT-union, so they need only `[HasSubobjectUnions]` (supplied by any pre-logos) — no
-- finite coproducts.  This matches Freyd §2.212: "Rel(C) is distributive for ANY pre-logos."
variable [PreLogos 𝒞]

/-- The coterminator `0` (initial object) of a pre-logos (§1.61). -/
private noncomputable def zeroObj : 𝒞 := (minimal_subobject_of_one_is_coterminator (inferInstance)).zero

/-- The EMPTY relation `a → b`: the bottom subobject of `a × b` read as a relation. -/
def emptyRel (a b : 𝒞) : BinRel 𝒞 a b := subRel (PreLogos.bottom (prod a b))

/-- **Strict-initial key**: a subobject `S` whose domain admits a map into the
    coterminator `0` is `≤` every subobject.  (Such an `S.dom` is iso to `0`, hence
    initial, so any two maps out of it — in particular `h ≫ T.arr` and `S.arr` — agree.) -/
theorem subobject_le_of_dom_to_zero {B : 𝒞} {S : Subobject 𝒞 B}
    (m : S.dom ⟶ zeroObj (𝒞 := 𝒞)) (T : Subobject 𝒞 B) : S.le T := by
  -- m is iso (strict initial, §1.61); let minv be its inverse.
  obtain ⟨minv, _hmm, _hmm'⟩ := any_map_to_zero_is_iso (inferInstance) m
  -- S.dom is initial (iso to 0): any two maps S.dom → X agree.
  have hinit : ∀ {X : 𝒞} (f g : S.dom ⟶ X), f = g := by
    intro X f g
    have key : m ≫ (minv ≫ f) = m ≫ (minv ≫ g) :=
      congrArg (m ≫ ·)
        ((minimal_subobject_of_one_is_coterminator (inferInstance)).init_uniq (minv ≫ f) (minv ≫ g))
    calc f = (m ≫ minv) ≫ f := by rw [_hmm, Cat.id_comp]
      _ = m ≫ (minv ≫ f) := Cat.assoc _ _ _
      _ = m ≫ (minv ≫ g) := key
      _ = (m ≫ minv) ≫ g := (Cat.assoc _ _ _).symm
      _ = g := by rw [_hmm, Cat.id_comp]
  -- any map S.dom → T.dom works; the factorization holds automatically by initiality.
  exact ⟨m ≫ (minimal_subobject_of_one_is_coterminator (inferInstance)).init T.dom, hinit _ _⟩

/-- `bottom B`'s domain maps to the coterminator `0` (it is iso to it, §1.61).
    `0 = (bottom one).dom` definitionally, so `bottom_dom_iso B one` provides the map. -/
private noncomputable def bottomToZero (B : 𝒞) : (PreLogos.bottom B).dom ⟶ zeroObj (𝒞 := 𝒞) :=
  (PreLogos.bottom_dom_iso (𝒞 := 𝒞) B (Freyd.one)).choose

/-- The empty relation is the global minimum: `emptyRel a b ⊂ R` for every `R`. -/
theorem emptyRel_le {a b : 𝒞} (R : BinRel 𝒞 a b) : RelLe (emptyRel a b) R := by
  apply relLe_of_subLe
  -- relSub(emptyRel) ≤ relSub R via subobject_le_of_dom_to_zero (its dom maps to 0).
  have hm : (relSub (emptyRel a b)).dom ⟶ zeroObj (𝒞 := 𝒞) := by
    -- (relSub (subRel (bottom))).dom = (bottom).dom
    exact bottomToZero (prod a b)
  exact subobject_le_of_dom_to_zero hm (relSub R)

/-- A map out of an object that maps to the coterminator `0` is determined by `0`: any two
    such maps agree (the source is iso to initial `0`). -/
private theorem hom_uniq_of_to_zero {X Y : 𝒞} (m : X ⟶ zeroObj (𝒞 := 𝒞)) (f g : X ⟶ Y) :
    f = g := by
  obtain ⟨minv, hmm, _⟩ := any_map_to_zero_is_iso (inferInstance) m
  have key : m ≫ (minv ≫ f) = m ≫ (minv ≫ g) :=
    congrArg (m ≫ ·)
      ((minimal_subobject_of_one_is_coterminator (inferInstance)).init_uniq (minv ≫ f) (minv ≫ g))
  calc f = (m ≫ minv) ≫ f := by rw [hmm, Cat.id_comp]
    _ = m ≫ (minv ≫ f) := Cat.assoc _ _ _
    _ = m ≫ (minv ≫ g) := key
    _ = (m ≫ minv) ≫ g := (Cat.assoc _ _ _).symm
    _ = g := by rw [hmm, Cat.id_comp]

/-- **§2.21 absorbing (right)**: `R ⊚ emptyRel ⊂ emptyRel`.  The composition span sits over
    the pullback whose `π₂`-leg lands in `emptyRel.src ≅ 0`; so the span's source is initial.
    Then `bottom (a×c)` allows the span (any two maps out of an initial object agree), and
    image-minimality gives `relSub(R⊚emptyRel) = image span ≤ bottom = relSub(emptyRel)`.
    (`emptyRel` minimal gives the reverse, so this is the equation `R ⊚ 0 = 0`.) -/
theorem comp_emptyRel_le {a b c : 𝒞} (R : BinRel 𝒞 a b) :
    RelLe (R ⊚ emptyRel b c) (emptyRel a c) := by
  apply relLe_of_subLe
  let pb := HasPullbacks.has R.colB (emptyRel b c).colA
  let s : pb.cone.pt ⟶ prod a c :=
    pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ (emptyRel b c).colB)
  -- pb.pt is initial: π₂ → emptyRel.src = (bottom (b×c)).dom → 0.
  let m0 : pb.cone.pt ⟶ zeroObj (𝒞 := 𝒞) := pb.cone.π₂ ≫ bottomToZero (prod b c)
  -- relSub(R⊚emptyRel) = image s as a subobject of a×c.
  have hRX_arr : (relSub (R ⊚ emptyRel b c)).arr = (image s).arr := by
    show pair (R ⊚ emptyRel b c).colA (R ⊚ emptyRel b c).colB = (image s).arr
    exact (pair_uniq (R ⊚ emptyRel b c).colA (R ⊚ emptyRel b c).colB (image s).arr rfl rfl).symm
  -- bottom (a×c) allows s: pick any q : pb.pt → bottom.dom; q ≫ bottom.arr = s by initiality.
  have hallow : Allows (PreLogos.bottom (prod a c)) s := by
    obtain ⟨q, _hq⟩ := PreLogos.bottom_min (A := prod a c) (image s)  -- bottom.dom ← ... ; need pb.pt → bottom.dom
    refine ⟨pb.cone.π₂ ≫ bottomToZero (prod b c) ≫
      (minimal_subobject_of_one_is_coterminator (inferInstance)).init (PreLogos.bottom (prod a c)).dom, ?_⟩
    exact hom_uniq_of_to_zero m0 _ s
  -- image s ≤ bottom (a×c).
  have himg_le : (image s).le (PreLogos.bottom (prod a c)) := image_min s _ hallow
  -- transport to relSub(emptyRel a c) (= subRel bottom, same arr as bottom).
  obtain ⟨k, hk⟩ := himg_le   -- k ≫ bottom.arr = (image s).arr
  refine ⟨k, ?_⟩
  -- goal: k ≫ (relSub (emptyRel a c)).arr = (relSub (R⊚emptyRel)).arr
  show k ≫ pair (emptyRel a c).colA (emptyRel a c).colB = (relSub (R ⊚ emptyRel b c)).arr
  rw [hRX_arr]
  -- (emptyRel a c) = subRel (bottom): pair colA colB = bottom.arr (relSub_subRel_arr).
  have hbarr : pair (emptyRel a c).colA (emptyRel a c).colB = (PreLogos.bottom (prod a c)).arr := by
    have := relSub_subRel_arr (𝒞 := 𝒞) (PreLogos.bottom (prod a c))
    -- (relSub (subRel bottom)).arr = bottom.arr; LHS arr is pair of subRel's legs = emptyRel legs.
    simpa [emptyRel, relSub] using this
  rw [hbarr, hk]

/-- **§2.21 absorbing (left)**: `emptyRel ⊚ R ⊂ emptyRel`.  Symmetric to `comp_emptyRel_le`:
    now the pullback's `π₁`-leg lands in `emptyRel.src ≅ 0`. -/
theorem emptyRel_comp_le {a b c : 𝒞} (R : BinRel 𝒞 b c) :
    RelLe (emptyRel a b ⊚ R) (emptyRel a c) := by
  apply relLe_of_subLe
  let pb := HasPullbacks.has (emptyRel a b).colB R.colA
  let s : pb.cone.pt ⟶ prod a c :=
    pair (pb.cone.π₁ ≫ (emptyRel a b).colA) (pb.cone.π₂ ≫ R.colB)
  let m0 : pb.cone.pt ⟶ zeroObj (𝒞 := 𝒞) := pb.cone.π₁ ≫ bottomToZero (prod a b)
  have hRX_arr : (relSub (emptyRel a b ⊚ R)).arr = (image s).arr := by
    show pair (emptyRel a b ⊚ R).colA (emptyRel a b ⊚ R).colB = (image s).arr
    exact (pair_uniq (emptyRel a b ⊚ R).colA (emptyRel a b ⊚ R).colB (image s).arr rfl rfl).symm
  have hallow : Allows (PreLogos.bottom (prod a c)) s := by
    refine ⟨pb.cone.π₁ ≫ bottomToZero (prod a b) ≫
      (minimal_subobject_of_one_is_coterminator (inferInstance)).init (PreLogos.bottom (prod a c)).dom, ?_⟩
    exact hom_uniq_of_to_zero m0 _ s
  have himg_le : (image s).le (PreLogos.bottom (prod a c)) := image_min s _ hallow
  obtain ⟨k, hk⟩ := himg_le
  refine ⟨k, ?_⟩
  show k ≫ pair (emptyRel a c).colA (emptyRel a c).colB = (relSub (emptyRel a b ⊚ R)).arr
  rw [hRX_arr]
  have hbarr : pair (emptyRel a c).colA (emptyRel a c).colB = (PreLogos.bottom (prod a c)).arr := by
    have := relSub_subRel_arr (𝒞 := 𝒞) (PreLogos.bottom (prod a c))
    simpa [emptyRel, relSub] using this
  rw [hbarr, hk]

/-! ### Union on the quotient and the distributive-allegory instance

  Union on `Rel(C)` is the §1.616 relational union `∪ᵣ` (`relUnion`, the image of the
  coproduct-of-tables).  All distributivity laws are reused from S1_60. -/

/-- Union on the quotient: `[R] ∪ [S] = [R ∪ᵣ S]`, well-defined by the union UMP. -/
def qUnion {a b : 𝒞} (x y : BinRelQuot (𝒞 := 𝒞) a b) : BinRelQuot (𝒞 := 𝒞) a b :=
  Quotient.liftOn₂ x y (fun R S => relClass (R ∪ᵣ S))
    (fun _ _ _ _ hR hS => Quotient.sound
      ⟨le_relUnion (rel_le_trans hR.1 (relUnion_le_left _ _))
          (rel_le_trans hS.1 (relUnion_le_right _ _)),
       le_relUnion (rel_le_trans hR.2 (relUnion_le_left _ _))
          (rel_le_trans hS.2 (relUnion_le_right _ _))⟩)

@[simp] theorem qUnion_mk {a b : 𝒞} (R S : BinRel 𝒞 a b) :
    qUnion (relClass R) (relClass S) = relClass (R ∪ᵣ S) := rfl

/-- **§2.21**: `Rel(C)` is a distributive allegory (for a positive pre-logos C).
    `0` = the empty relation, `∪` = the §1.616 relational union `∪ᵣ`. -/
instance (priority := 0) relDistributiveAllegory : DistributiveAllegory (RelObj 𝒞) :=
  { relAllegory with
    zero  := fun {A B} => relClass (emptyRel A.carrier B.carrier)
    union := fun x y => qUnion x y
    -- 0 ⊚ R = 0  and  R ⊚ 0 = 0  (antisymmetry: emptyRel minimal + absorbing).
    zero_comp := fun {A B C} R => by
      refine Quotient.inductionOn R (fun S => ?_)
      exact quotLe_antisymm (emptyRel_comp_le S) (emptyRel_le _)
    comp_zero := fun {A B C} R => by
      refine Quotient.inductionOn R (fun S => ?_)
      exact quotLe_antisymm (comp_emptyRel_le S) (emptyRel_le _)
    -- union semi-lattice laws (UMP of ∪ᵣ).
    union_idem := fun {A B} x => by
      refine Quotient.inductionOn x (fun R => ?_)
      exact quotLe_antisymm (le_relUnion (rel_le_refl R) (rel_le_refl R)) (relUnion_le_left R R)
    union_comm := fun {A B} x y => by
      refine Quotient.inductionOn₂ x y (fun R S => ?_)
      exact quotLe_antisymm
        (le_relUnion (relUnion_le_right S R) (relUnion_le_left S R))
        (le_relUnion (relUnion_le_right R S) (relUnion_le_left R S))
    union_assoc := fun {A B} x y z => by
      refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
      refine quotLe_antisymm ?_ ?_
      · -- R∪(S∪T) ⊆ (R∪S)∪T
        refine le_relUnion ?_ ?_
        · exact rel_le_trans (relUnion_le_left R S) (relUnion_le_left _ T)
        · refine le_relUnion ?_ ?_
          · exact rel_le_trans (relUnion_le_right R S) (relUnion_le_left _ T)
          · exact relUnion_le_right _ T
      · -- (R∪S)∪T ⊆ R∪(S∪T)
        refine le_relUnion ?_ ?_
        · refine le_relUnion ?_ ?_
          · exact relUnion_le_left R _
          · exact rel_le_trans (relUnion_le_left S T) (relUnion_le_right R _)
        · exact rel_le_trans (relUnion_le_right S T) (relUnion_le_right R _)
    -- absorption laws.
    union_inter_absorb := fun {A B} x y => by
      refine Quotient.inductionOn₂ x y (fun R S => ?_)
      exact quotLe_antisymm
        (le_relUnion (rel_le_refl R) (intersect_le_right S R)) (relUnion_le_left R _)
    inter_union_absorb := fun {A B} x y => by
      refine Quotient.inductionOn₂ x y (fun R S => ?_)
      exact quotLe_antisymm (intersect_le_right (R ∪ᵣ S) R)
        (le_intersect (relUnion_le_left R S) (rel_le_refl R))
    -- composition distributes over union (§1.616, both directions).
    comp_union_distrib := fun {A B C} x y z => by
      refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
      exact quotLe_antisymm (compose_union_right R S T)
        (le_relUnion (compose_le (rel_le_refl R) (relUnion_le_left S T))
          (compose_le (rel_le_refl R) (relUnion_le_right S T)))
    -- intersection distributes over union (§1.616, both directions).
    inter_union_distrib := fun {A B} x y z => by
      refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
      exact quotLe_antisymm (rel_inter_union_le R S T) (rel_union_inter_le R S T)
    -- 0 ∪ R = R.
    zero_union := fun {A B} x => by
      refine Quotient.inductionOn x (fun R => ?_)
      exact quotLe_antisymm
        (le_relUnion (emptyRel_le R) (rel_le_refl R)) (relUnion_le_right _ R) }

end RelDistributive

/-! ## §2.214  Coproducts in `Rel(C)` from a positive coproduct of `C`

  Freyd §2.214: *a pre-logos `C` is POSITIVE iff `Rel(C)` has finite coproducts.*  The
  reachable (forward) direction builds the allegory `Coproduct` (the §2.214 five-equation
  diagram, S2_2) of `Rel(C)` from a disjoint binary coproduct of `C`: the injections are the
  graphs `[graph inl], [graph inr]`, and the five equations are the relational forms of

    (1,4)  `inl`, `inr` MONIC          ⟹  `[inl]⊚[inl]° = 1`,  `[inr]⊚[inr]° = 1`
    (2,3)  `inl ∩ inr = 0` (§1.621)    ⟹  `[inl]⊚[inr]° = 0`,  `[inr]⊚[inl]° = 0`
    (5)    `inl ∪ inr = A+B` (§1.621)  ⟹  `[inl]°⊚[inl] ∪ [inr]°⊚[inr] = 1`.

  Equations (1) and (4) are fully reachable from Ch1 (`graph_comp_recip_le_one_of_mono`
  for `⊆`; `graph` ENTIRE for `⊇`) and are proved below.  Equations (2,3,5) require a
  bridge translating the SUBOBJECT-level §1.621 facts (`inl_inter_inr_le_bottom`,
  `inl_union_inr_entire`, both about subobjects of `A+B`) into the RELATION-composite
  forms `[inl]⊚[inr]° = 0` and `[inl]°⊚[inl] ∪ [inr]°⊚[inr] = 1` — i.e. identifying the
  pullback `pullback(inl, inr)` (a subobject of `A+B`) with the composite relation
  `graph inl ⊚ graph inr°` (a relation `A → B`).  That `compose`-vs-`pullback` dictionary
  for graphs of monics is not yet in the Ch1 layer, so (2,3,5) and the full `Coproduct`
  assembly are left as a precise BOOK TODO (see below). -/

section Coproduct214
-- The §2.214 forward direction lives over a positive (disjoint) coproduct of `C`.
variable [DisjointBinaryCoproduct 𝒞]

/-- The graph injection `[graph f]` as a `Rel(C)`-morphism (an element of `BinRelQuot a b`). -/
def relGraph {a b : 𝒞} (f : a ⟶ b) : BinRelQuot (𝒞 := 𝒞) a b := relClass (graph f)

/-- **§2.214 eq (1)/(4) — the monic injection equation.**  For a MONIC `f : a → b`, the
    graph satisfies `[graph f] ≫ [graph f]° = 1` in `Rel(C)`.  (`⊆` from
    `graph_comp_recip_le_one_of_mono`; `⊇` from `graph` ENTIRE.)  This is the §2.214
    `u₁u₁° = 1` / `u₂u₂° = 1` equation. -/
theorem relGraph_comp_recip_of_monic {a b : 𝒞} (f : a ⟶ b) (hf : Monic f) :
    qComp (relGraph f) (qRecip (relGraph f)) = relId a := by
  show relClass (graph f ⊚ (graph f)°) = relClass (graph (Cat.id a))
  exact quotLe_antisymm (graph_comp_recip_le_one_of_mono f hf) (graph_is_map f).1

/-- **§2.214 (graph injections are maps).**  Every graph `[graph f]` is entire + simple
    (a MAP) in `Rel(C)`; in particular the would-be coproduct injections are maps. -/
theorem relGraph_entire {a b : 𝒞} (f : a ⟶ b) :
    quotLe (relId a) (qComp (relGraph f) (qRecip (relGraph f))) :=
  (graph_is_map f).1

theorem relGraph_simple {a b : 𝒞} (f : a ⟶ b) :
    quotLe (qComp (qRecip (relGraph f)) (relGraph f)) (relId b) :=
  (graph_is_map f).2

/-- A composite `R ⊚ S` whose composition-pullback apex maps to the coterminator `0` is
    the empty relation.  (The composite's source is the image of a span out of that apex;
    since the apex is initial the span factors through `bottom`, so `image ⊂ bottom`.)
    The two §2.214 disjointness equations are instances with `R, S` the injection graphs:
    `pullback(inl, inr)` is initial by §1.621 disjointness. -/
theorem comp_le_empty_of_pullback_to_zero {a b c : 𝒞} (R : BinRel 𝒞 a b) (S : BinRel 𝒞 b c)
    (m : (HasPullbacks.has R.colB S.colA).cone.pt ⟶ zeroObj (𝒞 := 𝒞)) :
    RelLe (R ⊚ S) (emptyRel a c) := by
  apply relLe_of_subLe
  let pb := HasPullbacks.has R.colB S.colA
  let s : pb.cone.pt ⟶ prod a c := pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)
  have hRX_arr : (relSub (R ⊚ S)).arr = (image s).arr := by
    show pair (R ⊚ S).colA (R ⊚ S).colB = (image s).arr
    exact (pair_uniq (R ⊚ S).colA (R ⊚ S).colB (image s).arr rfl rfl).symm
  have hallow : Allows (PreLogos.bottom (prod a c)) s := by
    refine ⟨m ≫ (minimal_subobject_of_one_is_coterminator (inferInstance)).init
      (PreLogos.bottom (prod a c)).dom, ?_⟩
    exact hom_uniq_of_to_zero m _ s
  obtain ⟨k, hk⟩ := image_min s _ hallow
  refine ⟨k, ?_⟩
  show k ≫ pair (emptyRel a c).colA (emptyRel a c).colB = (relSub (R ⊚ S)).arr
  rw [hRX_arr]
  have hbarr : pair (emptyRel a c).colA (emptyRel a c).colB = (PreLogos.bottom (prod a c)).arr := by
    have := relSub_subRel_arr (𝒞 := 𝒞) (PreLogos.bottom (prod a c)); simpa [emptyRel, relSub] using this
  rw [hbarr, hk]

/-- The pullback apex of the injections `inl, inr` maps to the coterminator `0`: it is the
    domain of `inl ∩ inr`, which §1.621 disjointness places `≤ bottom ≅ 0`. -/
private noncomputable def inlInrPullbackToZero (A B : 𝒞) :
    (HasPullbacks.has (HasBinaryCoproducts.inl (A := A) (B := B)) HasBinaryCoproducts.inr).cone.pt
      ⟶ zeroObj (𝒞 := 𝒞) :=
  (inl_inter_inr_le_bottom (𝒟 := 𝒞) (A := A) (B := B)).choose ≫ bottomToZero _

/-- **§2.214 eq (2) — left/right disjointness.**  `[graph inl] ⊚ [graph inr]° = 0` in
    `Rel(C)`: the composition pullback is `pullback(inl, inr) ≅ 0` (§1.621 disjointness),
    so the composite is empty. -/
theorem relGraph_inl_comp_recip_inr {A B : 𝒞} :
    qComp (relGraph (HasBinaryCoproducts.inl (A := A) (B := B)))
          (qRecip (relGraph (HasBinaryCoproducts.inr (A := A) (B := B))))
      = (relClass (emptyRel A B)) := by
  show relClass (graph HasBinaryCoproducts.inl ⊚ (graph HasBinaryCoproducts.inr)°)
      = relClass (emptyRel A B)
  exact quotLe_antisymm
    (comp_le_empty_of_pullback_to_zero (graph HasBinaryCoproducts.inl)
      ((graph HasBinaryCoproducts.inr)°) (inlInrPullbackToZero A B))
    (emptyRel_le _)

/-- **§2.214 eq (3) — right/left disjointness** (symmetric). -/
theorem relGraph_inr_comp_recip_inl {A B : 𝒞} :
    qComp (relGraph (HasBinaryCoproducts.inr (A := A) (B := B)))
          (qRecip (relGraph (HasBinaryCoproducts.inl (A := A) (B := B))))
      = (relClass (emptyRel B A)) := by
  show relClass (graph HasBinaryCoproducts.inr ⊚ (graph HasBinaryCoproducts.inl)°)
      = relClass (emptyRel B A)
  refine quotLe_antisymm
    (comp_le_empty_of_pullback_to_zero (graph HasBinaryCoproducts.inr)
      ((graph HasBinaryCoproducts.inl)°) ?_) (emptyRel_le _)
  -- pullback(inr, inl).pt → pullback(inl, inr).pt (swap legs) → 0.
  let pbRL := HasPullbacks.has (HasBinaryCoproducts.inr (A := A) (B := B)) HasBinaryCoproducts.inl
  let pbLR := HasPullbacks.has (HasBinaryCoproducts.inl (A := A) (B := B)) HasBinaryCoproducts.inr
  -- pbRL square: π₁≫inr = π₂≫inl, so (π₂, π₁) is a cone over (inl, inr).
  let cswap : Cone (HasBinaryCoproducts.inl (A := A) (B := B)) HasBinaryCoproducts.inr :=
    ⟨pbRL.cone.pt, pbRL.cone.π₂, pbRL.cone.π₁, pbRL.cone.w.symm⟩
  exact pbLR.lift cswap ≫ inlInrPullbackToZero A B

/-! ### §2.214 eq (5) and the full `Coproduct (RelObj C)` record.

  `u₁_self_comp_recip`, `u₂_self_comp_recip` : `relGraph_comp_recip_of_monic`.
  `u₁_u₂_recip`, `u₂_u₁_recip`               : `relGraph_inl_comp_recip_inr` /
                                               `relGraph_inr_comp_recip_inl`.
  `recip_union_eq_id : [inl]°⊚[inl] ∪ [inr]°⊚[inr] = 1` : proved below
  (`relGraph_recip_union_eq_id`).  Strategy: the union inclusions `x : A → U.dom`,
  `y : B → U.dom` (`U := inlSub ∪ inrSub`) jointly cover `U.dom` (`union_joint_cover`),
  and the union arrow `e := U.arr : U.dom → A+B` is an ISO (`inl_union_inr_entire` makes
  `U = entire`).  Conjugating `1_{U.dom} ⊑ x°x ∪ y°y` by the iso graph `[e]` and using
  `[inl] = [x]⊚[e]`, `[inr] = [y]⊚[e]` (graph respects composition) lands the unit at
  `A+B`. -/

/-- **`graph` respects composition on the quotient** (§1.564): `[graph (f ≫ g)] =
    [graph f] ⊚ [graph g]`.  Both containments are Ch1 (`graph_comp` / `comp_graph`). -/
theorem relGraph_comp {a b c : 𝒞} (f : a ⟶ b) (g : b ⟶ c) :
    relGraph (f ≫ g) = qComp (relGraph f) (relGraph g) :=
  quotLe_antisymm (graph_comp f g) (comp_graph f g)

/-- **`[graph e]° ≫ [graph e] = 1` for a cover `e`** (in particular an iso): a cover's
    reciprocal-then-graph composite is the unit (`cover_iff_reciprocal_comp_self_eq_one`).
    Stated with the `Rel(C)` allegory operations on `RelObj C`. -/
theorem relGraph_recip_comp_self_of_cover {a b : 𝒞} (e : a ⟶ b) (he : Cover e) :
    (relGraph e)° ≫ (relGraph e) = @Cat.id (RelObj 𝒞) _ ⟨b⟩ := by
  show relClass ((graph e)° ⊚ graph e) = relClass (graph (Cat.id b))
  obtain ⟨hle, hge⟩ := (cover_iff_reciprocal_comp_self_eq_one e).mp he
  exact quotLe_antisymm hle hge

open Freyd.Alg in
/-- **§2.214 eq (5)** — the joint-cover equation.  `[inl]° ≫ [inl] ∪ [inr]° ≫ [inr] = 1`
    on `A+B` in `Rel(C)` (allegory operations).  The union inclusions jointly cover
    `U := inlSub ∪ inrSub` (`union_joint_cover`), and the union arrow is an iso
    (`inl_union_inr_entire`), so conjugating the `U`-unit by the iso graph transports it
    to `A+B`. -/
theorem relGraph_recip_union_eq_id {A B : 𝒞} :
    ((relGraph (HasBinaryCoproducts.inl (A := A) (B := B)))°
        ≫ relGraph (HasBinaryCoproducts.inl (A := A) (B := B)))
      ∪ ((relGraph (HasBinaryCoproducts.inr (A := A) (B := B)))°
        ≫ relGraph (HasBinaryCoproducts.inr (A := A) (B := B)))
      = @Cat.id (RelObj 𝒞) _ ⟨HasBinaryCoproducts.coprod A B⟩ := by
  -- The union subobject and its inclusions.
  let U := HasSubobjectUnions.union (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono)
                                    (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono)
  obtain ⟨x, hx⟩ := HasSubobjectUnions.union_left
    (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono) (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono)
  obtain ⟨y, hy⟩ := HasSubobjectUnions.union_right
    (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono) (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono)
  -- hx : x ≫ U.arr = inlSub.arr = inl ;  hy : y ≫ U.arr = inrSub.arr = inr.
  change x ≫ U.arr = HasBinaryCoproducts.inl at hx
  change y ≫ U.arr = HasBinaryCoproducts.inr at hy
  -- U.arr is an ISO: entire ≤ U (inl_union_inr_entire) gives a section, so U.arr is a
  -- split-epi monic, hence a cover.
  obtain ⟨e, he⟩ := inl_union_inr_entire (𝒟 := 𝒞) (A := A) (B := B)  -- e ≫ U.arr = (entire).arr = id
  have heU : e ≫ U.arr = Cat.id (HasBinaryCoproducts.coprod A B) := he
  have hcov : Cover U.arr := cover_of_section U.arr e heU
  -- Allegory-level abbreviations (morphisms of `RelObj C`).  `let` keeps them defeq to
  -- the underlying graphs so the bridge lemmas apply on the nose.
  let inlR : (⟨A⟩ : RelObj 𝒞) ⟶ ⟨HasBinaryCoproducts.coprod A B⟩ :=
    relGraph (HasBinaryCoproducts.inl (A := A) (B := B))
  let inrR : (⟨B⟩ : RelObj 𝒞) ⟶ ⟨HasBinaryCoproducts.coprod A B⟩ :=
    relGraph (HasBinaryCoproducts.inr (A := A) (B := B))
  let eR : (⟨U.dom⟩ : RelObj 𝒞) ⟶ ⟨HasBinaryCoproducts.coprod A B⟩ := relGraph U.arr
  let xR : (⟨A⟩ : RelObj 𝒞) ⟶ ⟨U.dom⟩ := relGraph x
  let yR : (⟨B⟩ : RelObj 𝒞) ⟶ ⟨U.dom⟩ := relGraph y
  -- rewrite the goal in terms of the abbreviations.
  show (inlR° ≫ inlR) ∪ (inrR° ≫ inrR) = @Cat.id (RelObj 𝒞) _ ⟨HasBinaryCoproducts.coprod A B⟩
  -- [inl] = [x] ≫ [e],  [inr] = [y] ≫ [e]  (graph respects composition).
  have hinl_fac : inlR = xR ≫ eR := by
    show relGraph (HasBinaryCoproducts.inl (A := A) (B := B)) = qComp (relGraph x) (relGraph U.arr)
    rw [← hx]; exact relGraph_comp x U.arr
  have hinr_fac : inrR = yR ≫ eR := by
    show relGraph (HasBinaryCoproducts.inr (A := A) (B := B)) = qComp (relGraph y) (relGraph U.arr)
    rw [← hy]; exact relGraph_comp y U.arr
  -- [e]° ≫ [e] = 1_{A+B}.
  have heRe : eR° ≫ eR = @Cat.id (RelObj 𝒞) _ ⟨HasBinaryCoproducts.coprod A B⟩ :=
    relGraph_recip_comp_self_of_cover U.arr hcov
  -- The joint cover at U: 1_{U.dom} ⊑ x°x ∪ y°y (bridge `quotLe → ⊑`).
  have hjoint : (@Cat.id (RelObj 𝒞) _ ⟨U.dom⟩) ⊑ (xR° ≫ xR) ∪ (yR° ≫ yR) :=
    (quotLe_iff_algLe _ _).mp
      (union_joint_cover (𝒞 := 𝒞) (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono)
        (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono) hx hy)
  -- `relGraph_simple` summands ⊑ 1 (bridge).
  have hsimp_l : inlR° ≫ inlR ⊑ @Cat.id (RelObj 𝒞) _ ⟨HasBinaryCoproducts.coprod A B⟩ :=
    (quotLe_iff_algLe _ _).mp (relGraph_simple (HasBinaryCoproducts.inl (A := A) (B := B)))
  have hsimp_r : inrR° ≫ inrR ⊑ @Cat.id (RelObj 𝒞) _ ⟨HasBinaryCoproducts.coprod A B⟩ :=
    (quotLe_iff_algLe _ _).mp (relGraph_simple (HasBinaryCoproducts.inr (A := A) (B := B)))
  apply Freyd.Alg.le_antisymm
  · -- (u₁°u₁ ∪ u₂°u₂) ⊑ 1 : each summand is simple.
    exact union_lub hsimp_l hsimp_r
  · -- 1 = e°≫e = e°≫1_U≫e ⊑ e°≫(x°x∪y°y)≫e = u₁°u₁∪u₂°u₂.
    have hconj : (eR° ≫ ((@Cat.id (RelObj 𝒞) _ ⟨U.dom⟩)) ≫ eR)
        ⊑ (eR° ≫ ((xR° ≫ xR) ∪ (yR° ≫ yR)) ≫ eR) :=
      comp_mono_left _ (comp_mono_right hjoint _)
    -- LHS = e°≫e = 1.
    rw [Cat.id_comp, heRe] at hconj
    -- RHS = u₁°u₁ ∪ u₂°u₂.
    have hRHS : eR° ≫ ((xR° ≫ xR) ∪ (yR° ≫ yR)) ≫ eR
        = (inlR° ≫ inlR) ∪ (inrR° ≫ inrR) := by
      rw [union_comp_distrib, DistributiveAllegory.comp_union_distrib, hinl_fac, hinr_fac]
      -- both summands: e°≫(z°≫z)≫e = (z≫e)°≫(z≫e)  via assoc + recip_comp.
      congr 1 <;>
        · rw [Allegory.recip_comp]
          simp only [Cat.assoc]
    rw [hRHS] at hconj
    exact hconj

/-- **§2.214 (forward direction).**  A disjoint/positive binary coproduct of `C` gives a
    coproduct in `Rel(C)`: the §2.214 five-equation `Coproduct` record over `RelObj C`,
    with injections the graphs `[inl], [inr]`. -/
noncomputable def relCoproduct (A B : 𝒞) :
    Coproduct (𝒜 := RelObj 𝒞) ⟨HasBinaryCoproducts.coprod A B⟩ ⟨A⟩ ⟨B⟩ where
  u₁ := relGraph (HasBinaryCoproducts.inl (A := A) (B := B))
  u₂ := relGraph (HasBinaryCoproducts.inr (A := A) (B := B))
  u₁_self_comp_recip := relGraph_comp_recip_of_monic _ inl_mono
  u₂_self_comp_recip := relGraph_comp_recip_of_monic _ inr_mono
  u₁_u₂_recip := relGraph_inl_comp_recip_inr
  u₂_u₁_recip := relGraph_inr_comp_recip_inl
  recip_union_eq_id := relGraph_recip_union_eq_id

end Coproduct214

end DisjointGluing

/-! ## §2.14 / §2.15  `Rel(C)` is a tabular, unitary allegory

  The two structural facts of `Rel(C)` that, with `Map(Rel C)`, make it a pre-logos
  (the §2.217 faithful-representation route):

    • **Tabular** (§2.14): every relation tabulates.  A relation `R : a → b`, picked as
      a `BinRel` table `⟨src; colA, colB⟩`, is tabulated by its own legs read as graphs:
      `f = [graph colA] : ⟨src⟩ → ⟨a⟩`, `g = [graph colB] : ⟨src⟩ → ⟨b⟩`.  These are
      maps (`graph_is_map`), `R = f° ≫ g` (span reconstitution), and `ff° ∩ gg° = 1`
      (joint monicity of the tabulating pair).

    • **Unitary** (§2.15): the unit object is `C`'s terminator `1`.  Every relation
      `T → T` (T := ⟨1⟩) is `⊑ 1` because both legs of any table over `1` are the unique
      map to the terminator; and every object has an entire relation to `1` (the graph of
      the terminal map). -/

section TabularUnitary
variable [RegularCategory 𝒞]

/-! ### BinRel-level reconstitution and joint monicity -/

/-- **Span reconstitution (⊆)**: `(graph R.colA)° ⊚ graph R.colB ⊂ R`.  The composite's
    pullback is `pullback(id, id)` over `R.src`, on which `π₁ = π₂`, so its span is
    `π₁ ≫ pair R.colA R.colB`, which `Allows` the subobject `⟨R.src; pair colA colB⟩`;
    image-minimality gives the `RelHom`. -/
private theorem reconstitute_le {a b : 𝒞} (R : BinRel 𝒞 a b) :
    RelLe ((graph R.colA)° ⊚ graph R.colB) R := by
  let pb := HasPullbacks.has ((graph R.colA)°).colB (graph R.colB).colA
  -- both pullback maps are id_{R.src}, so π₁ = π₂.
  have h_pb_w : pb.cone.π₁ = pb.cone.π₂ := by
    have := pb.cone.w; simpa [graph, reciprocal, Cat.comp_id] using this
  let span := pair (pb.cone.π₁ ≫ ((graph R.colA)°).colA) (pb.cone.π₂ ≫ (graph R.colB).colB)
  have h_monic : Monic (pair R.colA R.colB) := monic_pair_of_monicPair R.colA R.colB R.isMonicPair
  let S : Subobject 𝒞 (prod a b) := ⟨R.src, pair R.colA R.colB, h_monic⟩
  -- span = π₁ ≫ pair R.colA R.colB.
  have h_span_eq : pb.cone.π₁ ≫ pair R.colA R.colB = span := by
    show pb.cone.π₁ ≫ pair R.colA R.colB
       = pair (pb.cone.π₁ ≫ ((graph R.colA)°).colA) (pb.cone.π₂ ≫ (graph R.colB).colB)
    rw [← h_pb_w]
    apply pair_uniq (pb.cone.π₁ ≫ ((graph R.colA)°).colA) (pb.cone.π₁ ≫ (graph R.colB).colB) _
      (by rw [Cat.assoc, fst_pair]; rfl)
      (by rw [Cat.assoc, snd_pair]; rfl)
  have hallows : Allows S span := ⟨pb.cone.π₁, h_span_eq⟩
  let I := image span
  rcases image_min span S hallows with ⟨k, hk⟩
  refine ⟨⟨k, ?_, ?_⟩⟩
  · show k ≫ R.colA = (I.arr ≫ fst)
    calc k ≫ R.colA = (k ≫ pair R.colA R.colB) ≫ fst := by rw [Cat.assoc, fst_pair]
      _ = I.arr ≫ fst := by rw [hk]
  · show k ≫ R.colB = (I.arr ≫ snd)
    calc k ≫ R.colB = (k ≫ pair R.colA R.colB) ≫ snd := by rw [Cat.assoc, snd_pair]
      _ = I.arr ≫ snd := by rw [hk]

/-- **Span reconstitution (⊇)**: `R ⊂ (graph R.colA)° ⊚ graph R.colB`.  Lift `R.src` into
    the trivial pullback via the cone `⟨id, id⟩`, then `R.src → I.dom` through the image
    lift; its legs are `R.colA`, `R.colB`. -/
private theorem le_reconstitute {a b : 𝒞} (R : BinRel 𝒞 a b) :
    RelLe R ((graph R.colA)° ⊚ graph R.colB) := by
  let pb := HasPullbacks.has ((graph R.colA)°).colB (graph R.colB).colA
  -- cone ⟨R.src; id, id⟩ over (id, id).
  have h_cone_w : (Cat.id R.src) ≫ ((graph R.colA)°).colB
      = (Cat.id R.src) ≫ (graph R.colB).colA := by
    show (Cat.id R.src) ≫ (Cat.id R.src) = (Cat.id R.src) ≫ (Cat.id R.src); rfl
  let c : Cone ((graph R.colA)°).colB (graph R.colB).colA :=
    ⟨R.src, Cat.id R.src, Cat.id R.src, h_cone_w⟩
  let u := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = Cat.id R.src := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = Cat.id R.src := pb.lift_snd c
  let span := pair (pb.cone.π₁ ≫ ((graph R.colA)°).colA) (pb.cone.π₂ ≫ (graph R.colB).colB)
  let I := image span
  let h : R.src ⟶ I.dom := u ≫ image.lift span
  refine ⟨⟨h, ?_, ?_⟩⟩
  · show h ≫ (I.arr ≫ fst) = R.colA
    rw [Cat.assoc, ← Cat.assoc (image.lift span), image.lift_fac, fst_pair,
        ← Cat.assoc u pb.cone.π₁, hu₁, Cat.id_comp]
    rfl
  · show h ≫ (I.arr ≫ snd) = R.colB
    rw [Cat.assoc, ← Cat.assoc (image.lift span), image.lift_fac, snd_pair,
        ← Cat.assoc u pb.cone.π₂, hu₂, Cat.id_comp]
    rfl

/-- **Joint monicity (⊆)**: the legs of the meet `P ⊓ Q`, where `P = graph colA ⊚
    (graph colA)°` and `Q = graph colB ⊚ (graph colB)°` are the levels of the two
    columns, are equal.  `(P⊓Q).colA = π₁ ≫ P.colA`, `(P⊓Q).colB = π₁ ≫ P.colB`; the two
    agree under `colA` (`level_legs_comp` for colA, since `P.colA, P.colB` are `P`'s legs)
    and under `colB` (the pullback identifies `π₁≫P.legs` with `π₂≫Q.legs`, then
    `level_legs_comp` for colB), so `R.isMonicPair` collapses them — giving
    `graph colA ⊚ (graph colA)° ∩ graph colB ⊚ (graph colB)° ⊂ graph (id R.src)`. -/
private theorem jointMonic_le {a b : 𝒞} (R : BinRel 𝒞 a b) :
    RelLe ((graph R.colA ⊚ (graph R.colA)°) ⊓ (graph R.colB ⊚ (graph R.colB)°))
          (graph (Cat.id R.src)) := by
  let P := graph R.colA ⊚ (graph R.colA)°
  let Q := graph R.colB ⊚ (graph R.colB)°
  -- the meet is the pullback of eP, eQ into R.src × R.src.
  let eP := pair P.colA P.colB
  let eQ := pair Q.colA Q.colB
  let pb := HasPullbacks.has eP eQ
  -- `level_legs_comp` for each column (defeq to P, Q).
  have hlevP : P.colA ≫ R.colA = P.colB ≫ R.colA := level_legs_comp R.colA
  have hlevQ : Q.colA ≫ R.colB = Q.colB ≫ R.colB := level_legs_comp R.colB
  -- (P⊓Q).colA = π₁ ≫ P.colA, (P⊓Q).colB = π₁ ≫ P.colB.
  -- pullback identification: π₁ ≫ eP = π₂ ≫ eQ, projecting to:
  have hidA : pb.cone.π₁ ≫ P.colA = pb.cone.π₂ ≫ Q.colA := by
    have hsq := pb.cone.w
    calc pb.cone.π₁ ≫ P.colA = pb.cone.π₁ ≫ (eP ≫ fst) := by rw [fst_pair]
      _ = (pb.cone.π₁ ≫ eP) ≫ fst := (Cat.assoc _ _ _).symm
      _ = (pb.cone.π₂ ≫ eQ) ≫ fst := by rw [hsq]
      _ = pb.cone.π₂ ≫ (eQ ≫ fst) := Cat.assoc _ _ _
      _ = pb.cone.π₂ ≫ Q.colA := by rw [fst_pair]
  have hidB : pb.cone.π₁ ≫ P.colB = pb.cone.π₂ ≫ Q.colB := by
    have hsq := pb.cone.w
    calc pb.cone.π₁ ≫ P.colB = pb.cone.π₁ ≫ (eP ≫ snd) := by rw [snd_pair]
      _ = (pb.cone.π₁ ≫ eP) ≫ snd := (Cat.assoc _ _ _).symm
      _ = (pb.cone.π₂ ≫ eQ) ≫ snd := by rw [hsq]
      _ = pb.cone.π₂ ≫ (eQ ≫ snd) := Cat.assoc _ _ _
      _ = pb.cone.π₂ ≫ Q.colB := by rw [snd_pair]
  -- legs equal under colA : (π₁≫P.colA)≫colA = (π₁≫P.colB)≫colA  [level of colA].
  have hcolA : (pb.cone.π₁ ≫ P.colA) ≫ R.colA = (pb.cone.π₁ ≫ P.colB) ≫ R.colA := by
    calc (pb.cone.π₁ ≫ P.colA) ≫ R.colA = pb.cone.π₁ ≫ (P.colA ≫ R.colA) := Cat.assoc _ _ _
      _ = pb.cone.π₁ ≫ (P.colB ≫ R.colA) := by rw [hlevP]
      _ = (pb.cone.π₁ ≫ P.colB) ≫ R.colA := (Cat.assoc _ _ _).symm
  -- legs equal under colB : (π₁≫P.colA)≫colB = (π₁≫P.colB)≫colB  [via Q, level of colB].
  have hcolB : (pb.cone.π₁ ≫ P.colA) ≫ R.colB = (pb.cone.π₁ ≫ P.colB) ≫ R.colB := by
    calc (pb.cone.π₁ ≫ P.colA) ≫ R.colB = (pb.cone.π₂ ≫ Q.colA) ≫ R.colB := by rw [hidA]
      _ = pb.cone.π₂ ≫ (Q.colA ≫ R.colB) := Cat.assoc _ _ _
      _ = pb.cone.π₂ ≫ (Q.colB ≫ R.colB) := by rw [hlevQ]
      _ = (pb.cone.π₂ ≫ Q.colB) ≫ R.colB := (Cat.assoc _ _ _).symm
      _ = (pb.cone.π₁ ≫ P.colB) ≫ R.colB := by rw [hidB]
  -- joint monicity collapses the two legs.
  have hlegs : pb.cone.π₁ ≫ P.colA = pb.cone.π₁ ≫ P.colB :=
    R.isMonicPair _ _ hcolA hcolB
  -- the RelHom into graph(id): witness = (P⊓Q).colA; `graph(id).colA = graph(id).colB = id`,
  -- so both legs reduce to `(P⊓Q).colA` (using `hlegs : (P⊓Q).colA = (P⊓Q).colB`).
  refine ⟨⟨(P ⊓ Q).colA, ?_, ?_⟩⟩
  · show (P ⊓ Q).colA ≫ Cat.id R.src = (P ⊓ Q).colA; rw [Cat.comp_id]
  · show (P ⊓ Q).colA ≫ Cat.id R.src = (P ⊓ Q).colB
    rw [Cat.comp_id]; exact hlegs

/-! ### Allegory-level bridges: `Map`, `Entire`, `Simple` of a `relClass` -/

/-- The allegory domain `dom` of a `relClass` is the class of `graph id ⊓ R⊚R°`. -/
private theorem dom_relClass {a b : 𝒞} (R : BinRel 𝒞 a b) :
    Freyd.Alg.dom (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass R)
      = relClass (graph (Cat.id a) ⊓ (R ⊚ R°)) := by
  show qInter (relId a) (qComp (relClass R) (qRecip (relClass R))) = _
  rw [qRecip_mk, qComp_mk]; rfl

/-- **Entire bridge**: `Alg.Entire (relClass R) ↔ Entire R` (BinRel).  Both say
    `graph id ⊂ R⊚R°`. -/
private theorem entire_relClass {a b : 𝒞} (R : BinRel 𝒞 a b) :
    Freyd.Alg.Entire (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass R) ↔ Freyd.Entire R := by
  show Freyd.Alg.dom (𝒜 := RelObj 𝒞) (relClass R) = relId a ↔ _
  rw [dom_relClass]
  constructor
  · intro h
    -- relClass (graph id ⊓ R⊚R°) = relClass (graph id) gives graph id ⊂ R⊚R°.
    have hqe : quotLe (relClass (graph (Cat.id a))) (relClass (graph (Cat.id a) ⊓ (R ⊚ R°))) := by
      rw [h]; exact quotLe_refl _
    exact rel_le_trans hqe (intersect_le_right _ _)
  · intro h
    -- graph id ⊂ R⊚R° gives graph id ⊓ R⊚R° ≈ graph id.
    exact quotLe_antisymm (intersect_le_left _ _) (le_intersect (rel_le_refl _) h)

/-- **Simple bridge**: `Alg.Simple (relClass R) ↔ Simple R` (BinRel).  Both say
    `R°⊚R ⊂ graph id`. -/
private theorem simple_relClass {a b : 𝒞} (R : BinRel 𝒞 a b) :
    Freyd.Alg.Simple (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass R) ↔ Freyd.Simple R := by
  -- `Alg.Simple (relClass R)` is `Alg.le (relClass (R°⊚R)) (relId b)`; `Simple R` is the
  -- corresponding `quotLe`, which `quotLe_iff_algLe` identifies.
  change Freyd.Alg.le (𝒜 := RelObj 𝒞) (relClass (R° ⊚ R)) (relId b) ↔ _
  exact (quotLe_iff_algLe (relClass (R° ⊚ R)) (relId b)).symm

/-- **Map bridge**: `Alg.Map (relClass R) ↔ Map R`. -/
private theorem map_relClass {a b : 𝒞} (R : BinRel 𝒞 a b) :
    Freyd.Alg.Map (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass R) ↔ Freyd.Map R :=
  and_congr (entire_relClass R) (simple_relClass R)

/-- A graph's class is a `Map` in `Rel(C)` (from `graph_is_map`). -/
private theorem relClass_graph_map {a b : 𝒞} (f : a ⟶ b) :
    Freyd.Alg.Map (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass (graph f)) :=
  (map_relClass (graph f)).mpr (graph_is_map f)

/-! ### §2.14  `Rel(C)` is a tabular allegory -/

/-- **§2.14**: `Rel(C)` is a TABULAR allegory.  A relation `[R]` is tabulated by the
    graphs of its own legs: apex `⟨R.src⟩`, `f = [graph R.colA]`, `g = [graph R.colB]`.
    The four conjuncts are: both graphs are maps (`relClass_graph_map`); `[R] = f° ≫ g`
    (`reconstitute_le`/`le_reconstitute`); `f f° ∩ g g° = 1` (`jointMonic_le` for `⊆`,
    `relGraph_entire`-style entirety for `⊇`). -/
instance (priority := 0) relTabularAllegory : TabularAllegory (RelObj 𝒞) :=
  { relAllegory with
    tabular := fun {A B} x => by
      refine Quotient.inductionOn x (fun R => ?_)
      refine ⟨⟨R.src⟩, relClass (graph R.colA), relClass (graph R.colB),
        relClass_graph_map R.colA, relClass_graph_map R.colB, ?_, ?_⟩
      · -- [R] = [graph R.colA]° ≫ [graph R.colB]
        show relClass R = relClass ((graph R.colA)° ⊚ graph R.colB)
        exact quotLe_antisymm (le_reconstitute R) (reconstitute_le R)
      · -- f f° ∩ g g° = 1_{R.src}
        show qInter (relClass (graph R.colA ⊚ (graph R.colA)°))
              (relClass (graph R.colB ⊚ (graph R.colB)°)) = relId R.src
        rw [qInter_mk]
        -- relClass (graph colA ⊚ (graph colA)° ⊓ graph colB ⊚ (graph colB)°) = relId R.src
        refine quotLe_antisymm (jointMonic_le R) ?_
        -- 1 ⊂ ff° ∩ gg° : both columns are entire (graphs are maps).
        exact le_intersect (graph_is_map R.colA).1 (graph_is_map R.colB).1 }

/-! ### §2.15  `Rel(C)` is a unitary allegory: the unit is `C`'s terminator `1` -/

/-- Every relation over the terminator `T → T` (`T = ⟨1⟩`) is `⊑ 1`: both legs of any
    table over `1` are the unique map to `1`, so the table is `⊂ graph (id 1)`. -/
private theorem partialUnit_one : PartialUnit (𝒜 := RelObj 𝒞) ⟨Freyd.one (𝒞 := 𝒞)⟩ := by
  intro x
  refine Quotient.inductionOn x (fun R => ?_)
  rw [← quotLe_iff_algLe]
  -- RelHom R (graph (id 1)) : witness R.colA; both legs land on the terminator.
  refine ⟨⟨R.colA, ?_, ?_⟩⟩
  · show R.colA ≫ Cat.id Freyd.one = R.colA; rw [Cat.comp_id]
  · -- R.colA ≫ id = R.colB : both R.colA, R.colB : R.src → 1 are the unique terminal map.
    show R.colA ≫ Cat.id Freyd.one = R.colB
    rw [Cat.comp_id]; exact Freyd.term_uniq R.colA R.colB

/-- The graph of the terminal map `a → 1` is an entire relation `⟨a⟩ → ⟨1⟩`. -/
private theorem entire_to_one (a : 𝒞) :
    Freyd.Alg.Entire (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨Freyd.one (𝒞 := 𝒞)⟩)
      (relClass (graph (Freyd.term a))) :=
  (entire_relClass (graph (Freyd.term a))).mpr (graph_is_map (Freyd.term a)).1

/-- **§2.15**: `Rel(C)` is a UNITARY allegory with unit object `⟨1⟩` (`C`'s terminator).
    Partial-unit: `partialUnit_one`.  Entirety: each object `⟨a⟩` has the entire relation
    `[graph (a → 1)]` (`entire_to_one`). -/
instance (priority := 0) relUnitaryAllegory : UnitaryAllegory (RelObj 𝒞) :=
  { relAllegory with
    unit_obj := ⟨Freyd.one (𝒞 := 𝒞)⟩
    unit_prop := ⟨partialUnit_one,
      fun a => ⟨relClass (graph (Freyd.term a.carrier)), entire_to_one a.carrier⟩⟩ }

end TabularUnitary

/-! ### §2.217  `Rel(C)` is a tabular-unitary-distributive allegory; `Map(Rel C)` is a pre-logos;
    and `C ↪ Map(Rel C)` is a faithful embedding.

  Assembling `relTabularAllegory`, `relUnitaryAllegory` (§2.14/§2.15) and the positive-pre-logos
  `relDistributiveAllegory` (§2.21) onto the SINGLE diamond-merged class
  `TabularUnitaryDistributiveAllegory` lets `MapCat`'s `mapPreLogos` fire, giving a pre-logos
  `Map(Rel C)`.  The graph functor `C → Map(Rel C)` is faithful because graphs of distinct maps
  are distinct relations (`relClass_graph_inj`). -/

section MapRel

variable [PreLogos 𝒞]

/-- **§2.217**: for a pre-logos `C`, `Rel(C)` is a tabular-unitary-distributive allegory.
    All three parents (`relTabularAllegory`, `relUnitaryAllegory`,
    `DisjointGluing.relDistributiveAllegory`) are built `{ relAllegory with … }`, so their shared
    `toAllegory` grandparent is the SAME `relAllegory` — the diamond merges cleanly. -/
instance (priority := 0) relTabularUnitaryDistributiveAllegory :
    TabularUnitaryDistributiveAllegory (RelObj 𝒞) :=
  { relTabularAllegory, relUnitaryAllegory, DisjointGluing.relDistributiveAllegory with }

/-- **§2.217**: `Map(Rel C)` is a pre-logos for a positive pre-logos `C` — immediate from
    `MapCat.mapPreLogos` applied to `relTabularUnitaryDistributiveAllegory`.  Stated explicitly so
    typeclass resolution finds it (the `MapObj (RelObj C)` instance head). -/
noncomputable instance relMapPreLogos :
    @PreLogos (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) :=
  Freyd.Alg.mapPreLogos (A := RelObj 𝒞)

end MapRel

/-! ### §2.217  Faithful graph embedding `C ↪ Map(Rel C)`.

  The crux is `relClass_graph_inj`: graphs of distinct morphisms are distinct relations, so the
  object-and-graph assignment `f ↦ [graph f]` is injective on hom-sets.  This needs only
  `[RegularCategory C]` (it is pure §1.413 table algebra), NOT positivity. -/

section GraphEmbedding

variable [RegularCategory 𝒞]

/-- **§2.217 core**: `graph` is injective up to relational equality.  If `[graph f] = [graph g]`
    as morphisms of `Rel(C)` then `f = g`.  Proof: equality of classes gives `graph f ⊂ graph g`,
    i.e. a `RelHom` — a map `h : A ⟶ A` with `h ≫ (graph g).colA = (graph f).colA` and
    `h ≫ (graph g).colB = (graph f).colB`.  Since `(graph _).colA = id A` and `(graph _).colB = _`,
    the first equation forces `h = id A` and the second then reads `g = id ≫ g = h ≫ g = f`. -/
theorem relClass_graph_inj {a b : 𝒞} {f g : a ⟶ b}
    (h : relClass (graph f) = relClass (graph g)) : f = g := by
  -- [graph f] = [graph g] ⇒ graph f ≈ graph g (mutual RelLe); take the ⊂ direction.
  have hle : RelLe (graph f) (graph g) := (Quotient.exact h).1
  obtain ⟨w, hA, hB⟩ := hle
  -- w : A ⟶ A.  (graph _).colA = id A (defeq), (graph _).colB = f resp g (defeq).
  -- hA : w ≫ id a = id a  ⇒  w = id a.
  have hw : w = Cat.id a := by
    have hA' : w ≫ Cat.id a = Cat.id a := hA
    exact (Cat.comp_id w).symm.trans hA'
  -- hB : w ≫ g = f  ⇒  f = id a ≫ g = g.
  have hB' : w ≫ g = f := hB
  rw [hw] at hB'
  exact ((Cat.id_comp g).symm.trans hB').symm

/-- **§2.217**: the graph of `f` is a `Map` in `Rel(C)`, packaged as a `Map(Rel C)` morphism
    `⟨a⟩ ⟶ ⟨b⟩` (a `mapCat` hom = subtype `{ R // Map R }`).  This is the morphism part of the
    embedding `C → Map(Rel C)`. -/
noncomputable def embedRel {a b : 𝒞} (f : a ⟶ b) :
    @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩ :=
  ⟨relClass (graph f), relClass_graph_map f⟩

/-- **§2.217**: the graph embedding `C → Map(Rel C)` is FAITHFUL — distinct morphisms have
    distinct graph-maps.  Reduces (via `Subtype.ext_iff`) to `relClass_graph_inj`. -/
theorem embedRel_faithful {a b : 𝒞} {f g : a ⟶ b} (h : embedRel f = embedRel g) : f = g :=
  relClass_graph_inj (a := a) (b := b) (Subtype.ext_iff.mp h)

/-- **§2.148-dual (fullness)**: every `Map` in `Rel(C)` is the graph of a unique `C`-morphism.
    Given `R : BinRel C a b` whose class is a map (`Alg.Map (relClass R)`), there is `f : a ⟶ b`
    with `relClass R = relClass (graph f)` — i.e. `f` realises `R` via `embedRel f`.

    Proof: `map_relClass` lowers `Alg.Map (relClass R)` to `Map R` (entire+simple at the BinRel
    level).  `tabulated_is_map_iff_left_iso` (§1.564) turns that into `IsIso R.colA` — its left
    leg is a cover (entire) and monic (simple), and a regular category is balanced, so cover+mono
    ⟹ iso (`monic_cover_iso`).  With the inverse `i := R.colA⁻¹`, set `f := i ≫ R.colB`;
    `tabulated_left_iso_eq_graph` (§1.564) gives `R ≈ graph f` (mutual `⊂`), collapsed by
    `quotLe_antisymm`.  (`R` and `BinRel.mk R.src R.colA R.colB R.isMonicPair` are defeq by η.) -/
theorem embedRel_full {a b : 𝒞} (R : BinRel 𝒞 a b)
    (M : Freyd.Alg.Map (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass R)) :
    ∃ f : a ⟶ b, relClass R = relClass (graph f) := by
  have hmapR : Map R := (map_relClass R).mp M
  -- left leg is an iso (cover ∧ monic, then balance)
  have hiso : IsIso R.colA :=
    (tabulated_is_map_iff_left_iso R.colA R.colB R.isMonicPair).mp hmapR
  obtain ⟨i, hi₁, hi₂⟩ := hiso  -- i = R.colA⁻¹ : a ⟶ R.src
  refine ⟨i ≫ R.colB, ?_⟩
  obtain ⟨hle, hge⟩ :=
    tabulated_left_iso_eq_graph R.colA R.colB R.isMonicPair i hi₁ hi₂
  exact quotLe_antisymm (relClass_mono hle) (relClass_mono hge)

/-! ### The functor `embedRel : C → Map(Rel C)` and the category iso `C ≅ Map(Rel C)`.

  `embedRel` is identity-on-objects (`⟨a⟩ = RelObj.mk a`), functorial (`embedRel_id`,
  `embedRel_comp`), faithful (`embedRel_faithful`) and full (`embedRel_full` — every Map is a
  graph).  These four facts ARE the iso of categories `C ≅ Map(Rel C)` (§2.148 dual / §2.214). -/

/-- `embedRel` preserves identities: `embedRel (id a) = id ⟨a⟩` in `Map(Rel C)`.  Both sides have
    `val = relClass (graph (id a)) = relId a` (the `relCat` identity), and `Map`-witnesses are
    proof-irrelevant, so `Subtype.ext` closes it. -/
theorem embedRel_id (a : 𝒞) :
    embedRel (Cat.id a) = @Cat.id (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ :=
  Subtype.ext rfl

/-- `embedRel` preserves composition: `embedRel (f ≫ g) = embedRel f ≫ embedRel g`.  On `val`
    this is `relClass (graph (f ≫ g)) = qComp (relClass (graph f)) (relClass (graph g))`, the
    mutual-`⊂` graph-composition law (`graph_comp` / `comp_graph`) collapsed by `quotLe_antisymm`. -/
theorem embedRel_comp {a b c : 𝒞} (f : a ⟶ b) (g : b ⟶ c) :
    embedRel (f ≫ g)
      = @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩ ⟨c⟩
          (embedRel f) (embedRel g) :=
  Subtype.ext (quotLe_antisymm (graph_comp f g) (comp_graph f g))

/-- **§2.148 dual / §2.214 core — `C ≅ Map(Rel C)`.**  The graph embedding is an isomorphism of
    categories: identity-on-objects (`⟨·⟩`), functorial (`embedRel_id`/`embedRel_comp`), FAITHFUL
    (`embedRel_faithful`) and FULL (`embedRel_full`: every Map of `Rel C` is a unique graph).
    Packaged as the conjunction of the bijection-on-homs facts; downstream transport of structure
    (limits, coproducts) along this iso uses fullness to lift a `Map`-morphism back to a
    `C`-morphism. -/
theorem embedRel_cat_iso :
    (∀ {a b : 𝒞} {f g : a ⟶ b}, embedRel f = embedRel g → f = g) ∧
    (∀ {a b : 𝒞} (m : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩),
        ∃ f : a ⟶ b, m = embedRel f) :=
  ⟨fun h => embedRel_faithful h,
   fun {a b} m => by
     -- `m.val : BinRelQuot a b` is a quotient class; pick a representative `R` with `[R] = m.val`.
     refine Quotient.inductionOn (motive := fun q => (hq : Freyd.Alg.Map (𝒜 := RelObj 𝒞) q) →
        ∃ f : a ⟶ b, (⟨q, hq⟩ : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩)
          = embedRel f) m.val ?_ m.property
     intro R hq
     obtain ⟨f, hf⟩ := embedRel_full (a := a) (b := b) R hq
     exact ⟨f, Subtype.ext hf⟩⟩

/-- **A full + faithful identity-on-objects functor reflects monos.**  If `embedRel f` is monic in
    `Map(Rel C)` then `f` is monic in `C`.  Given `g h : W ⟶ a` with `g ≫ f = h ≫ f`, lift the
    Map-arrows `embedRel g`, `embedRel h : ⟨W⟩ ⟶ ⟨a⟩` (already in the image of `embedRel`);
    functoriality (`embedRel_comp`) sends `g ≫ f = h ≫ f` to `embedRel g ≫ embedRel f =
    embedRel h ≫ embedRel f`, monicity of `embedRel f` gives `embedRel g = embedRel h`, and
    faithfulness (`embedRel_faithful`) returns `g = h`. -/
theorem embedRel_reflects_monic {a b : 𝒞} {f : a ⟶ b}
    (hm : @Monic (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩ (embedRel f)) :
    Monic f := by
  intro W g h hgh
  apply embedRel_faithful
  -- map both sides through `embedRel` (functorial), then cancel `embedRel f` (monic).
  refine hm (embedRel g) (embedRel h) ?_
  rw [← embedRel_comp, ← embedRel_comp, hgh]

end GraphEmbedding

/-! ### §2.217(1)  A positive pre-logos embeds faithfully in a POSITIVE pre-logos.

  `relMapPreLogos` above gives only a *pre-logos* `Map(Rel C)`; §2.217(1) wants the target
  to be *positive* as well.  The positive reflection is Freyd's matrix construction `Mat(-)`:
  `Map(Mat(Rel C))` is a positive pre-logos, and `C` embeds into it as 1×1 matrices of graphs.

  Assembly:
    1. `Rel(C)` is a `TabularDistributiveAllegory` and a `UnitaryDistributiveAllegory`
       (the two local §2.342 hypothesis classes of `MatrixAllegory`).  Both diamonds merge
       because every parent is built `{ relAllegory with … }`.
    2. Hence `Mat(Rel C)` is tabular + unitary + distributive + positive
       (`instTabularAllegoryMat`, `instUnitaryAllegoryMat`, `instDistributiveAllegoryMat`,
       `instPositiveAllegoryMat`), i.e. a `TabularUnitaryPositiveAllegory`.
    3. So `Map(Mat(Rel C))` is a POSITIVE pre-logos (`MapCat.mapPositivePreLogos`).
    4. `C ↪ Map(Mat(Rel C))`, `f ↦ embed1 (embedRel f)` (1×1 matrix of the graph of `f`),
       is faithful (peel the 1×1 matrix, then `relClass_graph_inj`). -/

section Positivize

open Freyd.DisjointGluing Freyd.Alg.Mat

variable [PositivePreLogos 𝒞]

/-- **§2.217(1) step 1**: `Rel(C)` is a tabular *distributive* allegory — the §2.342 hypothesis
    class of the matrix construction.  Parents share the SAME `relAllegory` grandparent, so the
    diamond merges. -/
instance relTabularDistributiveAllegory :
    Freyd.Alg.Mat.TabularDistributiveAllegory (RelObj 𝒞) :=
  { relTabularAllegory, DisjointGluing.relDistributiveAllegory with }

/-- **§2.217(1) step 1**: `Rel(C)` is a unitary *distributive* allegory — the other §2.342
    matrix hypothesis class. -/
instance relUnitaryDistributiveAllegory :
    Freyd.Alg.Mat.UnitaryDistributiveAllegory (RelObj 𝒞) :=
  { relUnitaryAllegory, DisjointGluing.relDistributiveAllegory with }

/-- **§2.217(1) step 2**: `Mat(Rel C)` is a tabular-unitary-POSITIVE allegory.  Combines the four
    matrix instances (`instTabularAllegoryMat`, `instUnitaryAllegoryMat`,
    `instDistributiveAllegoryMat`, `instPositiveAllegoryMat`), all now resolvable from step 1. -/
noncomputable instance matRelTabularUnitaryPositiveAllegory :
    Freyd.Alg.TabularUnitaryPositiveAllegory (MatObj (RelObj 𝒞)) :=
  { (instTabularAllegoryMat : TabularAllegory (MatObj (RelObj 𝒞))),
    (instUnitaryAllegoryMat  : UnitaryAllegory  (MatObj (RelObj 𝒞))),
    (instPositiveAllegoryMat : PositiveAllegory (MatObj (RelObj 𝒞))) with }

/-- **§2.217(1) step 3**: `Map(Mat(Rel C))` is a POSITIVE pre-logos — the target object of the
    embedding.  Immediate from `MapCat.mapPositivePreLogos` over the
    `TabularUnitaryPositiveAllegory (MatObj (RelObj C))` of step 2.  Stated explicitly so
    typeclass resolution finds the `MapObj (MatObj (RelObj C))` instance head. -/
noncomputable instance s217PreLogos :
    @PositivePreLogos (MapObj (MatObj (RelObj 𝒞))) (mapCat (𝒜 := MatObj (RelObj 𝒞))) :=
  Freyd.Alg.mapPositivePreLogos (A := MatObj (RelObj 𝒞))

end Positivize

/-! ### §2.217(1)  Faithful embedding `C ↪ Map(Mat(Rel C))`.

  `embed1 : 𝒜 → MatObj 𝒜` (§H) wraps a base morphism as a 1×1 matrix and is a faithful allegory
  homomorphism (preserves `≫`, `°`, `∩`, `id`).  We show it carries `Map`s to `Map`s, so the
  graph-map `embedRel f : ⟨a⟩ ⟶ ⟨b⟩` in `Map(Rel C)` lifts to a Map in `Mat(Rel C)`, giving the
  morphism part of `C → Map(Mat(Rel C))`.  Faithfulness peels the 1×1 matrix back to
  `embedRel`, then `embedRel_faithful`. -/

section MatEmbedding

open Freyd.Alg.Mat

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- `embed1` sends the identity to the matrix identity (1×1 case: `matId` of `unitObj a`). -/
theorem embed1_id {a : 𝒜} : embed1 (Cat.id a) = matId (unitObj a) := by
  funext i j
  have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.fin_one_eq_zero i
  have hj : j = ⟨0, Nat.zero_lt_one⟩ := Fin.fin_one_eq_zero j
  subst hi; subst hj
  simp only [embed1, matId, unitObj, ↓reduceDIte]

/-- `embed1 R`, retyped as a category morphism `unitObj a ⟶ unitObj b` (defeq to its `MatHom`
    type, but `⟶`-headed so the allegory operations `⊑`/`°`/`≫`/`dom` elaborate). -/
def embed1' {a b : 𝒜} (R : a ⟶ b) : (unitObj a) ⟶ (unitObj b) := embed1 R

theorem embed1'_injective {a b : 𝒜} {R S : a ⟶ b} (h : embed1' R = embed1' S) : R = S :=
  embed1_injective h

/-- `embed1` reflects/preserves the allegory order (1×1 entrywise). -/
theorem embed1_le_iff {a b : 𝒜} {R S : a ⟶ b} :
    (embed1' R ⊑ embed1' S) ↔ (R ⊑ S) := by
  -- `X ⊑ Y` unfolds to `X ∩ Y = X`; `embed1` preserves `∩` and is injective, so the two
  -- equations `embed1 (R∩S) = embed1 R` and `R∩S = R` are interchangeable.
  show (Allegory.inter (embed1' R) (embed1' S) = embed1' R) ↔ (R ∩ S = R)
  rw [show Allegory.inter (embed1' R) (embed1' S) = embed1' (R ∩ S) from (embed1_inter R S).symm]
  exact ⟨fun h => embed1'_injective h, fun h => congrArg embed1' h⟩

/-- `embed1` commutes with `dom` (`dom = id ∩ R ≫ R°`; all preserved by `embed1`). -/
theorem embed1_dom {a b : 𝒜} (R : a ⟶ b) : dom (embed1' R) = embed1' (dom R) := by
  show Allegory.inter (Cat.id (unitObj a)) (matComp (embed1 R) (matRecip (embed1 R)))
      = embed1 (Cat.id a ∩ R ≫ R°)
  -- Expand the RHS through `embed1`'s homomorphism laws to match the LHS (all `mat*` primitives).
  rw [embed1_inter, embed1_comp, embed1_recip, embed1_id]
  rfl

/-- **§2.217(1) step 4 (preservation)**: `embed1` carries a `Map` of `𝒜` to a `Map` of
    `Mat 𝒜`.  `Entire`: `dom (embed1 R) = embed1 (dom R) = embed1 id = matId`.
    `Simple`: `(embed1 R)° ≫ embed1 R = embed1 (R° ≫ R) ⊑ embed1 id = matId`. -/
theorem embed1_map {a b : 𝒜} {R : a ⟶ b} (hR : Freyd.Alg.Map R) :
    Freyd.Alg.Map (𝒜 := MatObj 𝒜) (embed1' R) := by
  obtain ⟨hEnt, hSim⟩ := hR
  refine ⟨?_, ?_⟩
  · -- Entire
    show dom (embed1' R) = Cat.id (unitObj a)
    rw [embed1_dom, show dom R = Cat.id a from hEnt]
    show embed1 (Cat.id a) = matId (unitObj a)
    rw [embed1_id]
  · -- Simple: `(embed1 R)° ≫ embed1 R = embed1 (R° ≫ R) ⊑ embed1 (id) = id`.
    have hkey : embed1' (R° ≫ R) ⊑ embed1' (Cat.id b) := embed1_le_iff.mpr hSim
    show ((embed1' R)° ≫ embed1' R) ⊑ Cat.id (unitObj b)
    have hlhs : ((embed1' R)° ≫ embed1' R) = embed1' (R° ≫ R) := by
      show matComp (matRecip (embed1 R)) (embed1 R) = embed1 (R° ≫ R)
      rw [embed1_comp, embed1_recip]
    have hrhs : Cat.id (unitObj b) = embed1' (Cat.id b) := by
      show matId (unitObj b) = embed1 (Cat.id b); rw [embed1_id]
    rw [hlhs, hrhs]; exact hkey

end MatEmbedding

section GraphMatEmbedding

open Freyd.Alg.Mat

variable [PositivePreLogos 𝒞]

/-- **§2.217(1)**: the object part `C → Map(Mat(Rel C))`: `a ↦ unitObj ⟨a⟩` (the 1×1 matrix on
    the relation-object `⟨a⟩`). -/
def embed217Obj (a : 𝒞) : MapObj (MatObj (RelObj 𝒞)) := unitObj (⟨a⟩ : RelObj 𝒞)

/-- **§2.217(1)**: the morphism part `f ↦ embed1 (embedRel f)` — the 1×1 matrix whose single
    entry is the graph-map `[graph f]` of `Rel(C)`, packaged as a Map of `Mat(Rel C)`. -/
noncomputable def embed217 {a b : 𝒞} (f : a ⟶ b) :
    @Cat.Hom (MapObj (MatObj (RelObj 𝒞))) (mapCat (𝒜 := MatObj (RelObj 𝒞)))
      (embed217Obj a) (embed217Obj b) :=
  ⟨embed1' (embedRel f).val, embed1_map (embedRel f).property⟩

/-- **§2.217(1)**: the embedding `C ↪ Map(Mat(Rel C))` is FAITHFUL.  Peel the 1×1 matrix
    (`embed1'_injective`) to recover `embedRel f = embedRel g`, then `embedRel_faithful`. -/
theorem embed217_faithful {a b : 𝒞} {f g : a ⟶ b} (h : embed217 f = embed217 g) : f = g := by
  have hval : embed1' (embedRel f).val = embed1' (embedRel g).val := congrArg Subtype.val h
  exact embedRel_faithful (Subtype.ext (embed1'_injective hval))

end GraphMatEmbedding

/-! ### §2.217(1)  Headline. -/

section S217

open Freyd.Alg.Mat

variable [PositivePreLogos 𝒞]

/-- **§2.217(1)**: *every positive pre-logos `C` embeds faithfully in a positive pre-logos.*
    Take `D := Map(Mat(Rel C))`; it is a positive pre-logos (`s217PreLogos`) and `embed217` is a
    faithful functor `C ↪ D` (`embed217_faithful`).  Packaged as: there exist a positive-pre-logos
    structure on `D` and a per-hom injection of `C` into `D`.

    BOOK §2.217(1) (general): for a NON-positive pre-logos `C` this same construction works, but it
    needs `relDistributiveAllegory` weakened from `[PositivePreLogos C]` to `[PreLogos C]` — `Rel(C)`
    is distributive for any pre-logos (positivity of `C` is used ONLY to obtain the disjoint
    coproducts that make `Rel(C)` distributive *here*; the TARGET's positivity is supplied entirely
    by `Mat`, not by `C`).  Reproving `DisjointGluing.relDistributiveAllegory` over `[PreLogos C]`
    (distributivity of `Rel(C)` without disjoint coproducts) discharges the general statement with
    the identical `Mat`/`Map` assembly below. -/
theorem s217_faithful_embed_into_positive :
    Nonempty (@PositivePreLogos (MapObj (MatObj (RelObj 𝒞))) (mapCat (𝒜 := MatObj (RelObj 𝒞)))) ∧
    ∀ {a b : 𝒞} {f g : a ⟶ b}, embed217 f = embed217 g → f = g :=
  ⟨⟨s217PreLogos⟩, fun {_ _ _ _} h => embed217_faithful h⟩

end S217

/-! ### §2.214 REVERSE — `Rel(C)` has finite coproducts ⟹ `C` is positive.

  Freyd §2.214: a pre-logos `C` is positive **iff** `Rel(C)` has finite coproducts.  The forward
  direction (`positive ⟹ coproducts`) is `DisjointGluing.relCoproduct` above.  This is the REVERSE.

  THE DIAMOND DODGE (marker option (b)).  We do NOT take an opaque `[PositiveAllegory (RelObj C)]`
  hypothesis: that instance would carry its OWN `Allegory (RelObj C)`/`Cat (RelObj C)` not defeq to
  `relAllegory`, so it could not be merged with `relTabularUnitaryDistributiveAllegory` to feed the
  `Map`-coproduct machinery.  Instead we hypothesize the positive part as raw coproduct DATA over the
  EXISTING `relAllegory`: a coterminal `zero`, a binary `coprodObj`, and a §2.2 `Coproduct` record
  for each pair.  Assembling `{ relTabularUnitaryDistributiveAllegory with … }` keeps the single
  `relAllegory` grandparent, so `MapCat.mapHasBinaryCoproducts` fires with no diamond.

  TRANSPORT across `C ≅ Map(Rel C)` (`embedRel_cat_iso`, identity-on-objects).  The Map(Rel C)
  coproduct of `⟨a⟩,⟨b⟩` lives over a `RelObj C` whose `carrier` IS the C-coproduct object; the
  injections / copairing are Maps of `Rel C`, pulled back to unique `C`-morphisms by fullness
  (`embedRel_full`), with the universal property transferred by faithfulness + `embedRel_comp/_id`.

  What lands here SORRY-FREE: `relReverseHasBinaryCoproducts` (full `HasBinaryCoproducts C`) and
  `relReverse_inl_monic`/`relReverse_inr_monic` (injections monic in `C`).  The remaining content of
  the FULL `DisjointBinaryCoproduct C` is the two §1.621 disjointness inequalities `inl∩inr ≤ 0` and
  `entire ≤ inl∪inr`, which live in the PRE-LOGOS subobject structure (intersection / union / bottom)
  and would need `embedRel` to PRESERVE/REFLECT that structure — see the sharpened marker in S2_21. -/

section ReverseCoproduct

-- A BARE pre-logos suffices for the REVERSE direction: we CONSTRUCT `C`'s (disjoint) coproducts
-- from the supplied `Rel(C)`-coproduct DATA (`hcop`), so no ambient positivity is assumed.  This
-- matches Freyd §2.214 ("`C` positive ⟺ `Rel(C)` has finite coproducts"): the ⟸ direction holds
-- over any pre-logos.  Everything below uses only `[PreLogos]` (the relaxed `relUnion`,
-- `relTUPositiveAllegory`, `relMapPreLogos`, and the `PreLogos.bottom` coterminator).
variable [PreLogos 𝒞]

/-- Assemble a `TabularUnitaryPositiveAllegory (RelObj C)` from the existing tabular/unitary/
    distributive structure on `relAllegory` plus supplied positive coproduct DATA.  Because
    `relTabularUnitaryDistributiveAllegory` is itself `{ relAllegory with … }`, the resulting
    `toAllegory` grandparent is `relAllegory` — no competing `Allegory (RelObj C)` instance, so the
    `Map`-coproduct lemmas of `MapCat` apply directly.  This is the marker's option (b). -/
def relTUPositiveAllegory (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) :
    Freyd.Alg.TabularUnitaryPositiveAllegory (RelObj 𝒞) :=
  { relTabularUnitaryDistributiveAllegory with
    coterm := zero, coprod := coprodObj, has_coproduct := hcop }

/-- **§2.214 REVERSE (coproduct object + UMP).**  Given finite coproducts of `Rel(C)` (as positive
    coproduct data over `relAllegory`), `C` has binary coproducts.

    Construction.  The assembled `TabularUnitaryPositiveAllegory (RelObj C)` makes
    `Map(Rel C) = MapObj (RelObj C)` a category with binary coproducts (`mapHasBinaryCoproducts`),
    call it `H`.  Since `embedRel` is identity-on-objects, `H.coprod ⟨a⟩ ⟨b⟩ : RelObj C` is `⟨q⟩`
    with `q := (H.coprod ⟨a⟩ ⟨b⟩).carrier` the C-coproduct.  By fullness (`embedRel_cat_iso.2`)
    each Map-injection `H.inl`/`H.inr` and each copairing `H.case (embedRel f) (embedRel g)` is the
    graph of a UNIQUE C-morphism; faithfulness + `embedRel_comp`/`embedRel_id` transport the
    case-equations and uniqueness back to `C`. -/
noncomputable def relReverseHasBinaryCoproducts (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) :
    HasBinaryCoproducts 𝒞 := by
  letI tup := relTUPositiveAllegory zero coprodObj hcop
  letI H : @HasBinaryCoproducts (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) :=
    Freyd.Alg.mapHasBinaryCoproducts (A := RelObj 𝒞)
  -- Faithfulness, and the fullness lift: every Map(Rel C) morphism between `⟨·⟩` objects is the
  -- graph of a UNIQUE C-morphism.  `lift m` is that C-morphism; `lift_spec` is `embedRel (lift m) = m`.
  have hfaithful : ∀ {a b : 𝒞} {f g : a ⟶ b}, embedRel f = embedRel g → f = g :=
    fun {a b f g} h => (embedRel_cat_iso (𝒞 := 𝒞)).1 h
  let lift : ∀ {a b : 𝒞}, (@Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩) → (a ⟶ b) :=
    fun {a b} m => ((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose
  have lift_spec : ∀ {a b : 𝒞} (m : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩),
      embedRel (lift m) = m :=
    fun {a b} m => (((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose_spec).symm
  refine
    { coprod := fun a b => (H.coprod ⟨a⟩ ⟨b⟩).carrier
      inl := fun {a b} => lift (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inl
      inr := fun {a b} => lift (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inr
      case := fun {x a b} f g =>
        lift (a := (H.coprod ⟨a⟩ ⟨b⟩).carrier) (H.case (embedRel f) (embedRel g))
      case_inl := ?_
      case_inr := ?_
      case_uniq := ?_ }
  all_goals intro x a b f g
  · -- inl ≫ case f g = f
    apply hfaithful
    rw [embedRel_comp, lift_spec (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inl,
        lift_spec (a := (H.coprod ⟨a⟩ ⟨b⟩).carrier) (H.case (embedRel f) (embedRel g)), H.case_inl]
  · -- inr ≫ case f g = g
    apply hfaithful
    rw [embedRel_comp, lift_spec (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inr,
        lift_spec (a := (H.coprod ⟨a⟩ ⟨b⟩).carrier) (H.case (embedRel f) (embedRel g)), H.case_inr]
  · -- uniqueness
    intro h hl hr
    -- Push each C-hypothesis through `embedRel` (functorial) to Map(Rel C), using `embedRel_comp`
    -- forward (so the Map-composition instance is exactly `mapCat`, matching `H.case_uniq`).
    have hl' : @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _
        H.inl (embedRel h) = embedRel f := by
      have := congrArg embedRel hl
      rw [embedRel_comp, lift_spec (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inl] at this
      exact this
    have hr' : @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _
        H.inr (embedRel h) = embedRel g := by
      have := congrArg embedRel hr
      rw [embedRel_comp, lift_spec (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inr] at this
      exact this
    have huniq : embedRel h = H.case (embedRel f) (embedRel g) := H.case_uniq _ _ _ hl' hr'
    -- Goal: `case f g = h`, i.e. `lift (H.case …) = h`.  Apply faithfulness then collapse.
    apply hfaithful
    rw [lift_spec (a := (H.coprod ⟨a⟩ ⟨b⟩).carrier) (H.case (embedRel f) (embedRel g)), huniq]

/-- **§2.214 REVERSE (left injection monic).**  Under the coproduct structure of
    `relReverseHasBinaryCoproducts`, the left injection `inl : a ⟶ a+b` is monic in `C`.  Its
    `embedRel`-image is `Map(Rel C)`'s `inl`, which is monic there (`DisjointBinaryCoproduct`),
    and `embedRel_reflects_monic` pulls monicity back to `C`. -/
theorem relReverse_inl_monic (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) {a b : 𝒞} :
    @Monic 𝒞 _ a _
      (@HasBinaryCoproducts.inl 𝒞 _ (relReverseHasBinaryCoproducts zero coprodObj hcop) a b) := by
  letI tup := relTUPositiveAllegory zero coprodObj hcop
  letI H : @HasBinaryCoproducts (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) :=
    Freyd.Alg.mapHasBinaryCoproducts (A := RelObj 𝒞)
  -- `inl` of the C-structure is `lift H.inl`; its `embedRel`-image is `H.inl`, monic in Map(Rel C).
  apply embedRel_reflects_monic
  -- typed `have` so the leading `{a b}` implicits are not eagerly synthesized.
  have lift_spec : ∀ {a b : 𝒞} (m : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩),
      embedRel (((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose) = m :=
    fun {a b} m => (((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose_spec).symm
  have hsp : embedRel (@HasBinaryCoproducts.inl 𝒞 _ (relReverseHasBinaryCoproducts zero coprodObj hcop) a b)
      = @HasBinaryCoproducts.inl (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) H ⟨a⟩ ⟨b⟩ :=
    lift_spec (@HasBinaryCoproducts.inl (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) H ⟨a⟩ ⟨b⟩)
  rw [hsp]
  exact @DisjointBinaryCoproduct.inl_monic (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞))
    Freyd.Alg.mapDisjointBinaryCoproduct ⟨a⟩ ⟨b⟩

/-- **§2.214 REVERSE (right injection monic).**  Dual of `relReverse_inl_monic`. -/
theorem relReverse_inr_monic (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) {a b : 𝒞} :
    @Monic 𝒞 _ b _
      (@HasBinaryCoproducts.inr 𝒞 _ (relReverseHasBinaryCoproducts zero coprodObj hcop) a b) := by
  letI tup := relTUPositiveAllegory zero coprodObj hcop
  letI H : @HasBinaryCoproducts (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) :=
    Freyd.Alg.mapHasBinaryCoproducts (A := RelObj 𝒞)
  apply embedRel_reflects_monic
  have lift_spec : ∀ {a b : 𝒞} (m : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩),
      embedRel (((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose) = m :=
    fun {a b} m => (((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose_spec).symm
  have hsp : embedRel (@HasBinaryCoproducts.inr 𝒞 _ (relReverseHasBinaryCoproducts zero coprodObj hcop) a b)
      = @HasBinaryCoproducts.inr (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) H ⟨a⟩ ⟨b⟩ :=
    lift_spec (@HasBinaryCoproducts.inr (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) H ⟨a⟩ ⟨b⟩)
  rw [hsp]
  exact @DisjointBinaryCoproduct.inr_monic (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞))
    Freyd.Alg.mapDisjointBinaryCoproduct ⟨a⟩ ⟨b⟩

/-- **§2.214 REVERSE — union inequality `entire ≤ inl ∪ inr` (PURELY in C).**  The union
    `inlSub ∪ inrSub` is the image of `case inl inr` (`union_is_image`); by the coproduct UMP
    `case inl inr = id` (uniqueness against the identity), so the union is the image of the identity,
    which the entire subobject allows.  No transport across `embedRel` is needed for this half. -/
theorem relReverse_inl_union_inr (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) {a b : 𝒞} :
    letI H := relReverseHasBinaryCoproducts zero coprodObj hcop
    Subobject.le
      (Subobject.entire (HasBinaryCoproducts.coprod a b))
      (HasSubobjectUnions.union
        (inlSub (𝒞 := 𝒞) (A := a) (B := b)
          (relReverse_inl_monic zero coprodObj hcop))
        (inrSub (𝒞 := 𝒞) (A := a) (B := b)
          (relReverse_inr_monic zero coprodObj hcop))) := by
  letI H := relReverseHasBinaryCoproducts zero coprodObj hcop
  let Il := inlSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inl_monic zero coprodObj hcop)
  let Ir := inrSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inr_monic zero coprodObj hcop)
  -- `case Il.arr Ir.arr = case inl inr = id` by the coproduct uniqueness UMP.
  have hcase : HasBinaryCoproducts.case Il.arr Ir.arr
      = Cat.id (HasBinaryCoproducts.coprod a b) :=
    (HasBinaryCoproducts.case_uniq Il.arr Ir.arr (Cat.id _)
      (Cat.comp_id _) (Cat.comp_id _)).symm
  -- The union is an image of `case Il.arr Ir.arr`, hence allows it; rewriting by `hcase`
  -- it allows the identity, which is exactly `entire ≤ union`.
  obtain ⟨l, hl⟩ := (union_is_image Il Ir).1
  exact ⟨l, by rw [hl, hcase]; rfl⟩

/-- A subobject `Z` of `B` whose domain admits **any** map into a bottom domain is `≤ ⊥ B`.
    The map makes `Z.dom` initial (`dom_initial_of_map_to_bottom`); transporting along
    `bottom_dom_iso` yields a map `Z.dom → (⊥ B).dom`, and the factorization
    `· ≫ (⊥ B).arr = Z.arr` is forced because both sides are maps out of the initial `Z.dom`. -/
private theorem le_bottom_of_map_to_bottom {B W : 𝒞} (Z : Subobject 𝒞 B)
    (g : Z.dom ⟶ (PreLogos.bottom W).dom) : Z.le (PreLogos.bottom B) := by
  -- `Z.dom` is initial: any two maps out agree.
  have hinit : ∀ {Y : 𝒞} (u v : Z.dom ⟶ Y), u = v := dom_initial_of_map_to_bottom g
  -- a map `Z.dom → (⊥ B).dom`, via `bottom_dom_iso W B`.
  obtain ⟨ι, _⟩ := PreLogos.bottom_dom_iso W B
  refine ⟨g ≫ ι, ?_⟩
  -- `(g ≫ ι) ≫ (⊥ B).arr` and `Z.arr` are both maps out of the initial `Z.dom`.
  exact hinit ((g ≫ ι) ≫ (PreLogos.bottom B).arr) Z.arr

/-- **§2.214 REVERSE — disjointness inequality `inl ∩ inr ≤ 0` (TRANSPORTED through `embedRel`).**
    The intersection's domain `P` is the C-pullback of `(inl, inr)`.  Pushing the pullback square
    through `embedRel` (functorial, sending `inl ↦ inl_Map`, `inr ↦ inr_Map`) makes `⟨P⟩` a cone over
    `Map(Rel C)`'s `(inl_Map, inr_Map)`; `Map`'s own disjointness (`coprod_inl_inr_disjoint_elt` via
    `mapDisjointBinaryCoproduct`) provides a `Map`-map `⟨P⟩ → bottom_Map.dom`, so `⟨P⟩` is initial in
    `Map(Rel C)` (`dom_initial_of_map_to_bottom`).  Routed through the `Map`-coterminator and lifted
    back by fullness, that yields a C-map `P → (⊥ _).dom`; `le_bottom_of_map_to_bottom` closes it. -/
theorem relReverse_inl_inter_inr (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) {a b : 𝒞} :
    letI H := relReverseHasBinaryCoproducts zero coprodObj hcop
    Subobject.le
      (Subobject.inter
        (inlSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inl_monic zero coprodObj hcop))
        (inrSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inr_monic zero coprodObj hcop)))
      (PreLogos.bottom (HasBinaryCoproducts.coprod a b)) := by
  letI H := relReverseHasBinaryCoproducts zero coprodObj hcop
  let Il := inlSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inl_monic zero coprodObj hcop)
  let Ir := inrSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inr_monic zero coprodObj hcop)
  -- the C-pullback defining the intersection.
  let pb := HasPullbacks.has Il.arr Ir.arr
  -- `Map(Rel C)`'s DisjointBinaryCoproduct instance.  The positive-allegory witness `tup` is passed
  -- EXPLICITLY (not as a `letI` instance) so it does NOT shadow the global `Allegory (RelObj C)`
  -- (`relAllegory`): `mapCat`/`relMapPreLogos` then resolve along the SAME global chain, and
  -- `DM.toPreLogos` is defeq `relMapPreLogos`, dissolving the diamond the marker warned about.
  let DM : @DisjointBinaryCoproduct (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) :=
    @Freyd.Alg.mapDisjointBinaryCoproduct (RelObj 𝒞) (relTUPositiveAllegory zero coprodObj hcop)
  -- `Map(Rel C)`'s injections, projected from `DM`'s coproduct.
  let il := @HasBinaryCoproducts.inl (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞))
    DM.toPositivePreLogos.toHasBinaryCoproducts ⟨a⟩ ⟨b⟩
  let ir := @HasBinaryCoproducts.inr (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞))
    DM.toPositivePreLogos.toHasBinaryCoproducts ⟨a⟩ ⟨b⟩
  -- `embedRel`-images of the two injections are `Map(Rel C)`'s injections.
  have hinl : embedRel (Il.arr) = il :=
    (((embedRel_cat_iso (𝒞 := 𝒞)).2 il).choose_spec).symm
  have hinr : embedRel (Ir.arr) = ir :=
    (((embedRel_cat_iso (𝒞 := 𝒞)).2 ir).choose_spec).symm
  -- the pullback square in C, pushed through `embedRel` to a cone over `(inl_Map, inr_Map)`.
  have hsq : @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _ (embedRel pb.cone.π₁) il
      = @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _ (embedRel pb.cone.π₂) ir := by
    rw [← hinl, ← hinr, ← embedRel_comp, ← embedRel_comp]
    exact congrArg embedRel pb.cone.w
  -- `Map`'s disjointness: `⟨P⟩` admits a map into `Map`'s bottom domain (over `DM.toPreLogos`).
  obtain ⟨e, _he⟩ := @coprod_inl_inr_disjoint_elt (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) DM
    ⟨a⟩ ⟨b⟩ ⟨pb.cone.pt⟩ (embedRel pb.cone.π₁) (embedRel pb.cone.π₂) hsq
  -- `⟨P⟩` is initial in `Map(Rel C)`; route through the coterminator on `DM`'s own PreLogos
  -- (= `relMapPreLogos` definitionally, avoids the Cat-instance diamond) and lift back to C.
  let PLM := DM.toPositivePreLogos.toPreLogos
  letI ct := @minimal_subobject_of_one_is_coterminator (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) PLM
  have hbotiso := @PreLogos.bottom_dom_iso (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) PLM
    (@HasBinaryCoproducts.coprod (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞))
      DM.toPositivePreLogos.toHasBinaryCoproducts ⟨a⟩ ⟨b⟩)
    PLM.toHasTerminal.one
  obtain ⟨ι, _⟩ := hbotiso
  -- the `Map`-morphism `⟨P⟩ → ⟨(⊥ A+B in C).dom⟩`.
  let m₀ : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨pb.cone.pt⟩
      ⟨(PreLogos.bottom (HasBinaryCoproducts.coprod a b)).dom⟩ :=
    @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _
      (@Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _ e ι)
      (ct.init ⟨(PreLogos.bottom (HasBinaryCoproducts.coprod a b)).dom⟩)
  -- lift `m₀` through fullness to a C-morphism `P → (⊥ A+B).dom`.
  obtain ⟨h, _hh⟩ := (embedRel_cat_iso (𝒞 := 𝒞)).2 m₀
  -- `inter.dom = pb.cone.pt = P`, so `h : inter.dom → (⊥ A+B).dom`; close by the helper.
  exact le_bottom_of_map_to_bottom _ h

/-- **§2.214 REVERSE — full assembly.**  From finite coproducts of `Rel(C)` (the
    positive-allegory coproduct DATA `zero`/`coprodObj`/`hcop`), `C` has disjoint binary
    coproducts.  The four §1.621 fields are `relReverse_inl_monic`, `relReverse_inr_monic`,
    `relReverse_inl_inter_inr`, `relReverse_inl_union_inr`.

    Instance plumbing: build `PPL := { inst✝.toPreLogos, HBC with }` where
    `HBC = relReverseHasBinaryCoproducts[inst✝]`, then pass `PPL` explicitly to all four
    field lemmas via `@`.  Lean accepts `hcop` at `PPL`-type because
    `relTabularUnitaryDistributiveAllegory[PPL] = relTabularUnitaryDistributiveAllegory[inst✝]`
    definitionally (the allegory only uses `PreLogos`, not `HasBinaryCoproducts`). -/
noncomputable def relReverseDisjointBinaryCoproduct (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) :
    DisjointBinaryCoproduct 𝒞 :=
  -- `PPL` stores the ambient `PreLogos` LITERALLY (`mk ‹PreLogos 𝒞›`, not a `{…with}` rebuild) and
  -- pins the coproduct to `relReverseHasBinaryCoproducts` over the AMBIENT instance.  The four field
  -- lemmas are therefore applied at the AMBIENT `[PreLogos 𝒞]` (plain calls): their
  -- `relReverseHasBinaryCoproducts`/`bottom`/`inter`/`union` then match `PPL`'s projections
  -- definitionally, so no `relAllegory`/`hcop` re-elaboration diamond arises.
  @DisjointBinaryCoproduct.mk 𝒞 _
    (@PositivePreLogos.mk 𝒞 _ (‹PreLogos 𝒞›)
      (relReverseHasBinaryCoproducts zero coprodObj hcop))
    (fun {a b} => relReverse_inl_monic zero coprodObj hcop)
    (fun {a b} => relReverse_inr_monic zero coprodObj hcop)
    (fun {a b} => relReverse_inl_inter_inr zero coprodObj hcop)
    (fun {a b} => relReverse_inl_union_inr zero coprodObj hcop)

/-- **§2.214 (the iff).**  A pre-logos `C` is positive (has disjoint binary coproducts) iff
    `Rel(C)` has finite coproducts.  Forward: `DisjointGluing.relCoproduct`.
    Reverse: `relReverseDisjointBinaryCoproduct`. -/
theorem relReverse_positive_of_relCoproducts (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) :
    Nonempty (DisjointBinaryCoproduct 𝒞) :=
  ⟨relReverseDisjointBinaryCoproduct zero coprodObj hcop⟩

end ReverseCoproduct

end Freyd
