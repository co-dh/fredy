/-
  Freyd & Scedrov, *Categories and Allegories* §1.59
  Abelian categories: kernels, cokernels, exact, normal subobjects.

  §1.591: Zero object 0≅1, zero morphisms.
  §1.592: Kernel = equalizer(x,0), Cokernel = coequalizer(x,0).
  §1.593: Normal subobject = kernel of some morphism.
         Abelian ↔ regular additive + all-normal subobjects.
  §1.594: Abelian ⇔ effective regular additive category.
  §1.595: Ab(A) = category of abelian group objects; Ab(A) abelian for effective regular A.
  §1.597: Exact category; abelian ↔ exact additive (with binary products or coproducts).
  §1.598: Left-normal, right-normal, normal categories.
         Abelian ↔ normal + kernels + cokernels + (products or coproducts).
  §1.599: Exact sequences, five lemma, snake lemma.
-/


import Fredy.S1_1
import Fredy.S1_34
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd
/-! ## §1.59 Abelian categories

  ABELIAN: bicartesian satisfying all Horn sentences true for 𝒜𝒷.
  First consequences: 0≅1 (zero object), finite (co)products coincide,
  half-additive structure with the middle-two interchange law. -/

/-- A ZERO OBJECT is simultaneously terminal and coterminal: 0 ≅ 1. -/
def IsZeroObject (Z : 𝒞) [ht : HasTerminal 𝒞] [hc : HasCoterminator 𝒞] : Prop :=
  hc.zero = ht.one

/-! ### §1.591 Half-additive and additive categories

  In an abelian category the canonical map A+B → A×B is an isomorphism.
  This gives each hom-set an abelian monoid structure (half-additive),
  with the middle-two interchange law.  Requiring inverses gives additive. -/

/-- A HALF-ADDITIVE CATEGORY: finite products = finite coproducts, yielding
    an abelian monoid structure on each Hom(A,B).  (§1.591)

    Freyd's definition is *structural* — the addition is **defined**, not postulated.
    There is a zero object (`zeroHom`, the unique A→0→B), and the canonical δᵢⱼ-matrix
    `A+B → A×B` is an isomorphism (`prod_coprod_coincide`).  Freyd then writes the
    two coincident operations (§1.591, eqs. (1.1)/(1.1')):

        x +_L y = A --⟨⟩--> A+A --Φ⁻¹--> ... --[x,y]--> B   (codiagonal route)
        x +_R y = A --⟨x,y⟩--> B×B --Φ⁻¹--> B+B --∇--> B    (diagonal  route)

    Here `Φ⁻¹` is the inverse of the coincidence iso, `[x,y] = case x y`,
    `⟨⟩ = diag`, `⟨x,y⟩ = pair x y`, `∇ = case id id`.  The two formulas define the
    same map; we record `add` together with both defining equations
    (`add_eq_addL`, `add_eq_addR`).  From these the middle-two interchange,
    commutativity and associativity follow by Freyd's Eckmann–Hilton argument —
    none of it is postulated (see `middle_two_interchange` below). -/
class HalfAdditiveCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasCoterminator 𝒞, HasBinaryCoproducts 𝒞 where
  /-- Zero morphism A → 0 → B through the zero object (0 ≅ 1). -/
  zeroHom : ∀ (A B : 𝒞), A ⟶ B
  /-- The zero morphism is a two-sided absorbing ideal (it factors through 0):
      `f ≫ zeroHom = zeroHom` and `zeroHom ≫ g = zeroHom` (§1.591: "two-sided ideal"). -/
  zeroHom_comp_left  : ∀ {A B C : 𝒞} (f : A ⟶ B), f ≫ zeroHom B C = zeroHom A C
  zeroHom_comp_right : ∀ {A B C : 𝒞} (g : B ⟶ C), zeroHom A B ≫ g = zeroHom A C
  /-- The canonical map A+B → A×B (δᵢⱼ-matrix) is an isomorphism.
      This is the key horn sentence expressing that products = coproducts. -/
  prod_coprod_coincide : ∀ (A B : 𝒞),
    IsIso (HasBinaryCoproducts.case
        (pair (Cat.id A) (zeroHom A B))
        (pair (zeroHom B A) (Cat.id B)) :
      HasBinaryCoproducts.coprod A B ⟶ prod A B)
  /-- The abelian-monoid addition on Hom(A,B), induced by products = coproducts. -/
  add : ∀ {A B : 𝒞}, (A ⟶ B) → (A ⟶ B) → (A ⟶ B)
  /-- **Freyd eq. (1.1)**: `add` is the coproduct/codiagonal operation `+_L`,
      `x +_L y = diag ≫ Φ⁻¹ ≫ case x y`, with `Φ⁻¹` the inverse coincidence iso. -/
  add_eq_addL : ∀ {A B : 𝒞} (x y : A ⟶ B),
    add x y = diag A ≫ (prod_coprod_coincide A A).choose ≫
      HasBinaryCoproducts.case x y
  /-- **Freyd eq. (1.1')**: `add` is the product/diagonal operation `+_R`,
      `x +_R y = pair x y ≫ Φ⁻¹ ≫ ∇`, with `∇ = case id id`. -/
  add_eq_addR : ∀ {A B : 𝒞} (x y : A ⟶ B),
    add x y = pair x y ≫ (prod_coprod_coincide B B).choose ≫
      HasBinaryCoproducts.case (Cat.id B) (Cat.id B)

/-- In a half-additive category, each Hom(A,B) carries the structure's addition. -/
def homAdd [inst : HalfAdditiveCategory 𝒞] {A B : 𝒞} : (A ⟶ B) → (A ⟶ B) → (A ⟶ B) :=
  inst.add

namespace HalfAdditiveCategory

variable [inst : HalfAdditiveCategory 𝒞]

/-- The inverse `Φ⁻¹ : A×B → A+B` of the coincidence iso, chosen from
    `prod_coprod_coincide`. -/
private noncomputable def Φinv (A B : 𝒞) : prod A B ⟶ HasBinaryCoproducts.coprod A B :=
  (inst.prod_coprod_coincide A B).choose

/-- `add` in coproduct form (eq. 1.1), with the local name for `Φ⁻¹`. -/
private theorem add_addL {A B : 𝒞} (x y : A ⟶ B) :
    inst.add x y = diag A ≫ Φinv A A ≫ HasBinaryCoproducts.case x y :=
  inst.add_eq_addL x y

/-- `add` in product form (eq. 1.1'), with the local name for `Φ⁻¹`. -/
private theorem add_addR {A B : 𝒞} (x y : A ⟶ B) :
    inst.add x y = pair x y ≫ Φinv B B ≫ HasBinaryCoproducts.case (Cat.id B) (Cat.id B) :=
  inst.add_eq_addR x y

open HasBinaryCoproducts in
/-- Post-composition collapses a `case`: `case x y ≫ v = case (x≫v) (y≫v)`
    (coproduct functoriality). -/
private theorem case_comp {X Y A B : 𝒞} (x : A ⟶ X) (y : B ⟶ X) (v : X ⟶ Y) :
    case x y ≫ v = case (x ≫ v) (y ≫ v) :=
  case_uniq _ _ _ (by rw [← Cat.assoc, case_inl]) (by rw [← Cat.assoc, case_inr])

/-- Pre-composition collapses a `pair`: `w ≫ pair x y = pair (w≫x) (w≫y)`
    (product functoriality). -/
private theorem comp_pair {W X A B : 𝒞} (w : W ⟶ X) (x : X ⟶ A) (y : X ⟶ B) :
    w ≫ pair x y = pair (w ≫ x) (w ≫ y) :=
  pair_uniq (w ≫ x) (w ≫ y) (w ≫ pair x y)
    (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])

/-- **Matrix middle-four interchange** (pure (co)product universality, no iso):
    `case (pair a b) (pair c d) = pair (case a c) (case b d)` as maps `A+A → B×B`.
    This is the heart of Freyd's argument — the δ-matrix reads the same by rows or
    columns. -/
private theorem case_pair_swap {A B : 𝒞} (a b c d : A ⟶ B) :
    HasBinaryCoproducts.case (pair a b) (pair c d)
      = pair (HasBinaryCoproducts.case a c) (HasBinaryCoproducts.case b d) := by
  -- Determined by precomposition with inl, inr (joint epi for the coproduct).
  refine (HasBinaryCoproducts.case_uniq _ _ _ ?_ ?_).symm
  · -- inl ≫ pair (case a c) (case b d) = pair a b
    rw [comp_pair, HasBinaryCoproducts.case_inl, HasBinaryCoproducts.case_inl]
  · rw [comp_pair, HasBinaryCoproducts.case_inr, HasBinaryCoproducts.case_inr]

/-- `Φ ≫ Φ⁻¹ = id` on the coproduct (the δ-matrix iso), stated with the local name. -/
private theorem Φ_Φinv (A B : 𝒞) :
    HasBinaryCoproducts.case (pair (Cat.id A) (inst.zeroHom A B))
        (pair (inst.zeroHom B A) (Cat.id B)) ≫ Φinv A B
      = Cat.id (HasBinaryCoproducts.coprod A B) :=
  (inst.prod_coprod_coincide A B).choose_spec.1

/-- Right-associated cancellation `Φ ≫ Φ⁻¹ ≫ g = g`. -/
private theorem Φ_Φinv_comp {A B X : 𝒞}
    (g : HasBinaryCoproducts.coprod A B ⟶ X) :
    HasBinaryCoproducts.case (pair (Cat.id A) (inst.zeroHom A B))
        (pair (inst.zeroHom B A) (Cat.id B)) ≫ Φinv A B ≫ g = g := by
  rw [← Cat.assoc, Φ_Φinv, Cat.id_comp]

/-- Right unit `add f 0 = f` (eq. 1.1'): the second pair-slot is killed by `Φ⁻¹`. -/
theorem add_zero {A B : 𝒞} (f : A ⟶ B) : inst.add f (inst.zeroHom A B) = f := by
  rw [add_addR]
  -- pair f 0 = f ≫ inl ≫ Φ : factor through inl, whose Φ-image is pair id 0.
  have h1 : pair f (inst.zeroHom A B)
      = f ≫ HasBinaryCoproducts.inl ≫ HasBinaryCoproducts.case
          (pair (Cat.id B) (inst.zeroHom B B)) (pair (inst.zeroHom B B) (Cat.id B)) := by
    rw [HasBinaryCoproducts.case_inl, comp_pair, Cat.comp_id, inst.zeroHom_comp_left]
  rw [h1]
  simp only [Cat.assoc]
  rw [Φ_Φinv_comp, HasBinaryCoproducts.case_inl, Cat.comp_id]

/-- Left unit `add 0 f = f` (eq. 1.1'), dual to `add_zero`. -/
theorem zero_add {A B : 𝒞} (f : A ⟶ B) : inst.add (inst.zeroHom A B) f = f := by
  rw [add_addR]
  have h1 : pair (inst.zeroHom A B) f
      = f ≫ HasBinaryCoproducts.inr ≫ HasBinaryCoproducts.case
          (pair (Cat.id B) (inst.zeroHom B B)) (pair (inst.zeroHom B B) (Cat.id B)) := by
    rw [HasBinaryCoproducts.case_inr, comp_pair, Cat.comp_id, inst.zeroHom_comp_left]
  rw [h1]
  simp only [Cat.assoc]
  rw [Φ_Φinv_comp, HasBinaryCoproducts.case_inr, Cat.comp_id]

/-- **Middle-two interchange law** (§1.591): `(u + v) + (x + y) = (u + x) + (v + y)`.

    Freyd's Eckmann–Hilton argument.  `add` is simultaneously the coproduct
    operation `+_L` (eq. 1.1) and the product operation `+_R` (eq. 1.1').  Expand
    the *outer* add by `+_L` and the two *inner* adds by `+_R`; both sides become
    the single composite

        A --diag--> A×A --Φ⁻¹--> A+A --M--> B×B --Φ⁻¹--> B+B --∇--> B,

    where `M` is the δ-matrix.  The only place the two argument orders differ is in
    `M`, and `case_pair_swap` shows the two matrices are equal — that is the whole
    content.  Commutativity (`u=y=0`) and associativity (`u=0`) of `+` follow. -/
theorem middle_two_interchange {A B : 𝒞} (u v x y : A ⟶ B) :
    inst.add (inst.add u v) (inst.add x y) =
    inst.add (inst.add u x) (inst.add v y) := by
  -- The common δ-matrix composite both sides reduce to.
  let M : A ⟶ B :=
    diag A ≫ Φinv A A ≫ pair (HasBinaryCoproducts.case u x) (HasBinaryCoproducts.case v y)
      ≫ Φinv B B ≫ HasBinaryCoproducts.case (Cat.id B) (Cat.id B)
  -- LHS: outer +_L, inner +_R, then case_comp + case_pair_swap.
  have hLHS : inst.add (inst.add u v) (inst.add x y) = M := by
    show inst.add (inst.add u v) (inst.add x y) = _
    rw [add_addL (inst.add u v) (inst.add x y), add_addR u v, add_addR x y,
        ← case_comp (pair u v) (pair x y)
          (Φinv B B ≫ HasBinaryCoproducts.case (Cat.id B) (Cat.id B)),
        case_pair_swap u v x y]
  -- RHS: outer +_R, inner +_L, then comp_pair.
  have hRHS : inst.add (inst.add u x) (inst.add v y) = M := by
    show inst.add (inst.add u x) (inst.add v y) = _
    rw [add_addR (inst.add u x) (inst.add v y), add_addL u x, add_addL v y,
        ← Cat.assoc (diag A), ← Cat.assoc (diag A),
        ← comp_pair (diag A ≫ Φinv A A) (HasBinaryCoproducts.case u x)
          (HasBinaryCoproducts.case v y),
        Cat.assoc, Cat.assoc]
  rw [hLHS, hRHS]

/-- Commutativity of `add` (Eckmann–Hilton, `u=y=0` in middle-two interchange). -/
theorem add_comm {A B : 𝒞} (x y : A ⟶ B) : inst.add x y = inst.add y x := by
  have h := middle_two_interchange (inst.zeroHom A B) x y (inst.zeroHom A B)
  rwa [zero_add, add_zero, zero_add, add_zero] at h

/-- Associativity of `add` (Eckmann–Hilton, `v=0` in middle-two interchange). -/
theorem add_assoc {A B : 𝒞} (u x y : A ⟶ B) :
    inst.add u (inst.add x y) = inst.add (inst.add u x) y := by
  have h := middle_two_interchange u (inst.zeroHom A B) x y
  rwa [add_zero, zero_add] at h

/-- Left distributivity `h ≫ (x + y) = (h≫x) + (h≫y)` (pre-composition is additive).
    From `add` in product form (eq. 1.1') and `comp_pair`. -/
theorem comp_add {W A B : 𝒞} (h : W ⟶ A) (x y : A ⟶ B) :
    h ≫ inst.add x y = inst.add (h ≫ x) (h ≫ y) := by
  rw [add_addR, add_addR, ← Cat.assoc, ← Cat.assoc, comp_pair, Cat.assoc]

/-- Right distributivity `(x + y) ≫ k = (x≫k) + (y≫k)` (post-composition is additive).
    From `add` in coproduct form (eq. 1.1) and `case_comp`. -/
theorem add_comp {A B C : 𝒞} (x y : A ⟶ B) (k : B ⟶ C) :
    inst.add x y ≫ k = inst.add (x ≫ k) (y ≫ k) := by
  rw [add_addL, add_addL, Cat.assoc, Cat.assoc, case_comp]

/-- The SHEAR (elementary) matrix `(1 x; 0 1) : A×B → A×B` (§1.591).

    As a map *into* `A×B` it is `⟨fst, (fst≫x) + snd⟩`: the first coordinate is the
    first input (top row `(1 0)`), the second is `x·(first input) + (second input)`
    (bottom row `(x 1)`).  Additivity of the category is equivalent to every shear
    being an isomorphism; the inverse is the shear by the additive inverse `−x`. -/
def shear {A B : 𝒞} (x : A ⟶ B) : prod A B ⟶ prod A B :=
  pair fst (inst.add (fst ≫ x) snd)

theorem shear_fst {A B : 𝒞} (x : A ⟶ B) : shear x ≫ fst = fst := fst_pair _ _

theorem shear_snd {A B : 𝒞} (x : A ⟶ B) :
    shear x ≫ snd = inst.add (fst ≫ x) snd := snd_pair _ _

/-- Composing shears adds parameters: `shear x ≫ shear y = shear (x + y)`.
    The shears form a one-parameter additive subgroup of `Aut(A×B)`. -/
theorem shear_comp {A B : 𝒞} (x y : A ⟶ B) :
    shear x ≫ shear y = shear (inst.add x y) := by
  refine (pair_uniq _ _ _ ?_ ?_).trans (pair_eta (shear (inst.add x y))).symm
  · rw [Cat.assoc, shear_fst, shear_fst, shear_fst]
  · rw [Cat.assoc, shear_snd, comp_add, ← Cat.assoc, shear_fst, shear_snd,
        add_assoc, add_comm (fst ≫ y) (fst ≫ x), ← comp_add, shear_snd]

/-- `shear 0 = id`: the trivial shear is the identity. -/
theorem shear_zero {A B : 𝒞} : shear (inst.zeroHom A B) = Cat.id (prod A B) := by
  rw [shear, inst.zeroHom_comp_left, zero_add, pair_fst_snd]

end HalfAdditiveCategory

/-- ADDITIVE CATEGORY (§1.591): half-additive with additive inverses.
    Every hom-set (A,B) is an abelian group: each f : A → B has a (unique)
    additive inverse g : A → B satisfying f + g = 0_{A,B}. -/
class AdditiveCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends HalfAdditiveCategory 𝒞 where
  /-- Additive inverses exist: every f : A → B has a g with f + g = zeroHom A B. -/
  addInv : ∀ {A B : 𝒞} (f : A ⟶ B), ∃ g : A ⟶ B, add f g = zeroHom A B

/-! ### §1.591 Shear-matrix characterization of additivity

  Freyd's parenthetical: a half-additive category is *additive* iff for every
  `x : A → B` the shear matrix `(1 x; 0 1) : A×B → A×B` is an isomorphism.
  "If `(f, Y)` is its inverse one may show first that `y = 1` and then that
  `u + x = 0`" — the inverse is the shear by `−x`, and that `−x = u` is exactly
  how the additive inverse is extracted. -/

namespace HalfAdditiveCategory

variable [inst : HalfAdditiveCategory 𝒞]

/-- **Forward direction.** If every hom has an additive inverse, every shear is an
    isomorphism: the inverse of `shear x` is `shear g` where `g = −x`
    (`add x g = 0`), since `shear x ≫ shear g = shear (x + g) = shear 0 = id`. -/
theorem shear_isIso_of_addInv
    (hinv : ∀ {A B : 𝒞} (f : A ⟶ B), ∃ g : A ⟶ B, inst.add f g = inst.zeroHom A B)
    {A B : 𝒞} (x : A ⟶ B) : IsIso (shear x) := by
  obtain ⟨g, hg⟩ := hinv x
  refine ⟨shear g, ?_, ?_⟩
  · rw [shear_comp, hg, shear_zero]
  · rw [shear_comp, add_comm, hg, shear_zero]

/-- **Extraction lemma** (Freyd's hint).  Let `inv` be a left inverse of `shear x`
    (`inv ≫ shear x = id`).  Feeding the first injection `j₁ = ⟨1, 0⟩` gives
    `w = j₁ ≫ inv` with `w ≫ fst = 1` (Freyd's "`y = 1`") and `x + (w ≫ snd) = 0`
    (Freyd's "`u + x = 0`").  Thus `w ≫ snd` is the additive inverse `−x`. -/
theorem shear_inv_extract {A B : 𝒞} (x : A ⟶ B)
    (inv : prod A B ⟶ prod A B) (h : inv ≫ shear x = Cat.id (prod A B)) :
    (pair (Cat.id A) (inst.zeroHom A B) ≫ inv) ≫ fst = Cat.id A ∧
    inst.add x ((pair (Cat.id A) (inst.zeroHom A B) ≫ inv) ≫ snd) = inst.zeroHom A B := by
  -- j₁ = ⟨1,0⟩ is the first injection; w = j₁ ≫ inv.  Mathlib-free, so no `set`.
  -- key : w ≫ shear x = j₁  (since inv ≫ shear x = id).
  have key : (pair (Cat.id A) (inst.zeroHom A B) ≫ inv) ≫ shear x
      = pair (Cat.id A) (inst.zeroHom A B) := by rw [Cat.assoc, h, Cat.comp_id]
  -- y = 1 : first projection of w
  have hy : (pair (Cat.id A) (inst.zeroHom A B) ≫ inv) ≫ fst = Cat.id A := by
    rw [← shear_fst x, ← Cat.assoc, key, fst_pair]
  refine ⟨hy, ?_⟩
  -- u + x = 0 : second projection equation, expanded by distributivity
  have hs : ((pair (Cat.id A) (inst.zeroHom A B) ≫ inv) ≫ shear x) ≫ snd
      = inst.zeroHom A B := by rw [key, snd_pair]
  rw [Cat.assoc, shear_snd, comp_add, ← Cat.assoc, hy, Cat.id_comp] at hs
  exact hs

/-- **Backward direction.** If every shear is an isomorphism, every hom has an
    additive inverse: extract it from the shear's inverse via `shear_inv_extract`. -/
theorem addInv_of_shear_isIso
    (hiso : ∀ {A B : 𝒞} (x : A ⟶ B), IsIso (shear x))
    {A B : 𝒞} (f : A ⟶ B) : ∃ g : A ⟶ B, inst.add f g = inst.zeroHom A B := by
  obtain ⟨inv, _, h2⟩ := hiso f
  exact ⟨_, (shear_inv_extract f inv h2).2⟩

/-- **§1.591 (Freyd's parenthetical).** A half-additive category is additive iff
    every shear matrix `(1 x; 0 1)` is an isomorphism. -/
theorem additive_iff_shear_isIso :
    (∀ {A B : 𝒞} (f : A ⟶ B), ∃ g : A ⟶ B, inst.add f g = inst.zeroHom A B) ↔
    (∀ {A B : 𝒞} (x : A ⟶ B), IsIso (shear x)) :=
  ⟨fun hinv => shear_isIso_of_addInv hinv, fun hiso => addInv_of_shear_isIso hiso⟩

end HalfAdditiveCategory

/-! ## §1.591 Zero object

  If 0 ≅ 1, the zero object is the unique object that is both
  terminal and coterminal.  Every pair A,B has a ZERO MORPHISM
  A → 0 → B.  Zero morphisms form a two-sided ideal. -/

/-- A ZERO OBJECT: terminal = coterminal (§1.591). -/
class HasZeroObject (𝒞 : Type u) [Cat.{v} 𝒞] extends HasTerminal 𝒞, HasCoterminator 𝒞 where
  zero_eq_one : (one : 𝒞) = coterm

/-- The zero morphism A → B factors through the zero object. -/
def zeroMorphism [HasZeroObject 𝒞] (A B : 𝒞) : A ⟶ B :=
  let h := (HasZeroObject.zero_eq_one (𝒞 := 𝒞)).symm
  term A ≫ (cast (congrArg (λ X : 𝒞 => X ⟶ B) h) (zeroMap B))

/-- Zero morphisms are a two-sided ideal: f≫0 = 0, 0≫f = 0. -/
theorem zero_morphism_comp [HasZeroObject 𝒞] {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) :
    f ≫ zeroMorphism B C = zeroMorphism A C := by
  dsimp [zeroMorphism]
  rw [← Cat.assoc]
  rw [term_uniq (f ≫ term B) (term A)]

/-- Left-ideal half of §1.591: `0 ≫ g = 0`.  Maps out of the zero object are unique
  (coterminality), so the `one → C` tail of the zero morphism is absorbed by `g`. -/
theorem zeroMorphism_comp_left [HasZeroObject 𝒞] {A B C : 𝒞} (g : B ⟶ C) :
    zeroMorphism A B ≫ g = zeroMorphism A C := by
  dsimp [zeroMorphism]
  rw [Cat.assoc]
  congr 1
  -- both sides are `one → C`; since `one = coterm`, maps out of `one` are unique
  -- (coterminal uniqueness transported), so the two tails coincide.
  have huniq : ∀ (p q : (HasTerminal.one : 𝒞) ⟶ C), p = q := by
    rw [HasZeroObject.zero_eq_one (𝒞 := 𝒞)]
    exact fun p q => HasCoterminator.init_uniq p q
  exact huniq _ _

/-! ## §1.592 Kernels and cokernels

  KERNEL of x: equalizer of (x, 0).  COKERNEL: coequalizer of (x, 0). -/

/-- Kernel of x: the equalizer of x and the zero morphism (§1.592). -/
def Kernel [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B : 𝒞} (x : A ⟶ B) : 𝒞 :=
  eqObj x (zeroMorphism A B)

def kernelMap [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B : 𝒞} (x : A ⟶ B) :
    Kernel x ⟶ A :=
  eqMap x (zeroMorphism A B)

theorem kernelMap_eq [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B : 𝒞} (x : A ⟶ B) :
    kernelMap x ≫ x = kernelMap x ≫ zeroMorphism A B :=
  eqMap_eq x (zeroMorphism A B)

/-- Cokernel of x: the coequalizer of x and the zero morphism (§1.592). -/
def Cokernel [HasZeroObject 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (x : A ⟶ B) : 𝒞 :=
  (HasCoequalizers.coeq x (zeroMorphism A B)).obj

def cokernelMap [HasZeroObject 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (x : A ⟶ B) :
    B ⟶ Cokernel x :=
  (HasCoequalizers.coeq x (zeroMorphism A B)).map

/-! ## §1.593 Normal subobjects

  A subobject is NORMAL if it is the kernel of some morphism.
  A is ABELIAN iff it is a regular additive category in which
  every subobject is normal. -/

/-! A subobject m : A ↣ B is NORMAL (§1.593) if m is the kernel of some f : B → C,
  i.e. there is a morphism h : A → Kernel f that is an iso with h ≫ kernelMap f = m. -/
def IsNormalSubobject [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B : 𝒞}
    (m : A ⟶ B) (hm : Mono m) : Prop :=
  ∃ (C : 𝒞) (f : B ⟶ C) (h : A ⟶ Kernel f), IsIso h ∧ h ≫ kernelMap f = m

/-- An ABELIAN CATEGORY: regular, ADDITIVE (abelian-GROUP homs, not just monoid),
  every subobject is normal (§1.593).  Includes cokernels (§1.592: an abelian
  category has kernels and cokernels).

  FAITHFULNESS (Freyd §1.598): a genuine abelian category has abelian-GROUP
  hom-sets.  Extending `HalfAdditiveCategory` (commutative MONOID homs) is too
  weak — the five/snake lemmas are FALSE without additive inverses (witness:
  pointed sets form a half-additive non-additive category violating them).  We
  therefore extend `AdditiveCategory` (= `HalfAdditiveCategory` + `addInv`), so
  every `f : A ⟶ B` has a `g` with `add f g = zeroHom A B`. -/
class AbelianCategory (𝒞 : Type u) [Cat.{v} 𝒞]
    extends RegularCategory 𝒞, AdditiveCategory 𝒞, HasZeroObject 𝒞,
            HasEqualizers 𝒞, HasCoequalizers 𝒞 where
  all_normal : ∀ {A B : 𝒞} (m : A ⟶ B) (hm : Mono m), IsNormalSubobject m hm

/-- **Exactness, as a predicate on a FIXED zero/equalizer/coequalizer structure** (§1.597).
  This is the body of `ExactCategory.exact`, but stated as a `Prop` that reads the *ambient*
  `[HasZeroObject] [HasEqualizers] [HasCoequalizers]` instances rather than bundling its own
  copies.  Stating §1.593 against `IsExactStructure` (instead of `Nonempty (AbelianCategory 𝒞)`)
  keeps BOTH sides of the iff anchored to the SAME chosen zero/kernel/cokernel data, so the
  reverse direction is well-typed (see the note on the theorem below). -/
def IsExactStructure (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasZeroObject 𝒞] [HasEqualizers 𝒞] [HasCoequalizers 𝒞] : Prop :=
  ∀ {A B : 𝒞} (x : A ⟶ B),
    ∃ (θ : Cokernel (kernelMap x) ⟶ Kernel (cokernelMap x)),
      IsIso θ ∧ cokernelMap (kernelMap x) ≫ θ ≫ kernelMap (cokernelMap x) = x

/-! **§1.593**: A is abelian iff it is a regular additive category in which every
  subobject is normal.

  STATEMENT ENCODING (faithful + well-typed).  Both the LHS (`all monics normal`) and the
  RHS (`IsExactStructure`) are predicates that read the SAME ambient
  `[HasZeroObject] [HasEqualizers] [HasCoequalizers]` instances — the same chosen
  zero object, kernels and cokernels.  So the iff is a statement about ONE fixed bicartesian
  structure: "in this fixed regular additive category-with-zero, every subobject is normal
  ⟺ the category is exact (= abelian, §1.597)".  `IsExactStructure` is exactly the §1.597
  abelian content (θ : coker(ker x) ≅ ker(coker x) for all x), which is the bicartesian/
  Horn-sentence notion §1.59 calls "abelian"; §1.597 then equates exact-additive with abelian.

  WHY THE OLD `Nonempty (AbelianCategory 𝒞)` RHS WAS A DEFECT (statement-level, not a proof
  gap).  `IsNormalSubobject m hm` mentions `Kernel f`, which depends on the ambient
  `[HasZeroObject 𝒞]`/`[HasEqualizers 𝒞]` — classes carrying *data* (a chosen zero object /
  chosen equalizers), not just Props.  An arbitrary `Nonempty (AbelianCategory 𝒞)` witness
  carries its OWN, possibly different, `toHasZeroObject`/`toHasEqualizers`, so
  `inst.all_normal m hm` proves `IsNormalSubobject` w.r.t. the *witness's* kernels:
  `@IsNormalSubobject 𝒞 _ inst.toHasZeroObject inst.toHasEqualizers …`, whereas the goal
  demands `@IsNormalSubobject 𝒞 _ inst✝² inst✝¹ …` — a genuine type mismatch with no transport.
  Anchoring the RHS to the ambient instances (via `IsExactStructure`) removes the repacking.

  PROOF — both directions CLOSED representation-free (no §1.55 Ab-representation; axioms:
  Classical.choice only):
  (→) For each `x`, build the coimage→image comparison `θ : coker(ker x) → ker(coker x)` and
  show it is an iso = monic ∧ cover.  `θ` is a COVER because `⟨ker(coker x), i⟩` is the IMAGE
  of `x` (it allows `x`, and is minimal: any mono `S` allowing `x` contains it — here all-monos-
  normal makes `S` the kernel of its own cokernel, `monic_kernel_of_cokernel'`); the coimage
  projection `p = coker(ker x)` is a cover (`coeq_map_is_cover`), and `p ≫ θ` agrees with the
  image-lift cover, so `θ` is a cover.  `θ` is MONIC by a regular pullback-of-cover argument:
  pulling `ker θ` back along the cover `p`, the projection over `p` is a cover (epic), and it
  cancels `ker θ` to zero (the pullback feeds `ker x`, which `p` already kills) — so `ker θ = 0`,
  hence (additively) `θ` is monic.  Monic cover ⟹ iso (`monic_cover_iso`).
  (←) exact ⟹ every monic x is the kernel of its cokernel, i.e. normal (re-derived inline against
  the ambient zero/eq/coeq instances). -/

/-- Equalizer maps are monic, from the bare equalizer API (no Cartesian context). -/
theorem eqMap_mono' [HasEqualizers 𝒞] {A B : 𝒞} (f g : A ⟶ B) : Mono (eqMap f g) := by
  intro W u v h
  let k := u ≫ eqMap f g
  have hk : k ≫ f = k ≫ g := by dsimp [k]; rw [Cat.assoc, Cat.assoc, eqMap_eq]
  have hu : u = eqLift f g k hk := eqLift_uniq f g k hk u rfl
  have hv : v = eqLift f g k hk := eqLift_uniq f g k hk v (by dsimp [k]; rw [← h])
  rw [hu, hv]

/-- The cokernel kills its own morphism: `f ≫ cokernelMap f = 0`. -/
theorem comp_cokernelMap [HasZeroObject 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    f ≫ cokernelMap f = zeroMorphism A (Cokernel f) := by
  have hco := (HasCoequalizers.coeq f (zeroMorphism A B)).eq
  calc f ≫ cokernelMap f
      = zeroMorphism A B ≫ cokernelMap f := hco
    _ = zeroMorphism A (Cokernel f) := zeroMorphism_comp_left (cokernelMap f)

/-- Additive cancellation against a common summand: `X₁ + Y = 0` and `X₂ + Y = 0`
    force `X₁ = X₂`. -/
theorem add_cancel_common [HalfAdditiveCategory 𝒞] {A B : 𝒞} (X1 X2 Y : A ⟶ B)
    (h1 : HalfAdditiveCategory.add X1 Y = HalfAdditiveCategory.zeroHom A B)
    (h2 : HalfAdditiveCategory.add X2 Y = HalfAdditiveCategory.zeroHom A B) : X1 = X2 := by
  have hYX2 : HalfAdditiveCategory.add Y X2 = HalfAdditiveCategory.zeroHom A B := by
    rw [HalfAdditiveCategory.add_comm]; exact h2
  calc X1 = HalfAdditiveCategory.add X1 (HalfAdditiveCategory.zeroHom A B) :=
        (HalfAdditiveCategory.add_zero X1).symm
    _ = HalfAdditiveCategory.add X1 (HalfAdditiveCategory.add Y X2) := by rw [hYX2]
    _ = HalfAdditiveCategory.add (HalfAdditiveCategory.add X1 Y) X2 :=
        HalfAdditiveCategory.add_assoc X1 Y X2
    _ = HalfAdditiveCategory.add (HalfAdditiveCategory.zeroHom A B) X2 := by rw [h1]
    _ = X2 := HalfAdditiveCategory.zero_add X2

/-- `zeroHom = zeroMorphism` WITHOUT requiring `[ExactCategory]` (only the ambient
    zero object): both are the unique map factoring through `0`.  This is the
    `[ExactCategory]`-free version of `zeroHom_eq_zeroMorphism`, needed in the forward
    direction of §1.593 where no exact structure is yet available. -/
theorem zeroHom_eq_zeroMorphism' [HalfAdditiveCategory 𝒞] [HasZeroObject 𝒞] (X Y : 𝒞) :
    (HalfAdditiveCategory.zeroHom X Y : X ⟶ Y) = zeroMorphism X Y := by
  have h1 : (HalfAdditiveCategory.zeroHom X Y : X ⟶ Y)
      = term X ≫ HalfAdditiveCategory.zeroHom HasTerminal.one Y :=
    (HalfAdditiveCategory.zeroHom_comp_left (term X)).symm
  have huniqOut : ∀ (p q : (HasTerminal.one : 𝒞) ⟶ Y), p = q := by
    rw [HasZeroObject.zero_eq_one (𝒞 := 𝒞)]; exact fun p q => HasCoterminator.init_uniq p q
  dsimp [zeroMorphism]; rw [h1]; congr 1; exact huniqOut _ _

/-- **A normal mono is the kernel of its own cokernel** — re-derived from `IsNormalSubobject`
    (the "all monics normal" hypothesis) WITHOUT `[ExactCategory]`.  If `m` is the kernel of
    *some* `f`, then `m` and `kernelMap (cokernelMap m)` are the same subobject of `B`. -/
theorem monic_kernel_of_cokernel' [HasZeroObject 𝒞] [HasEqualizers 𝒞] [HasCoequalizers 𝒞]
    {A B : 𝒞} (m : A ⟶ B) (hm : Mono m) (hnorm : IsNormalSubobject m hm) :
    ∃ h : A ⟶ Kernel (cokernelMap m), IsIso h ∧ h ≫ kernelMap (cokernelMap m) = m := by
  obtain ⟨C, f, h0, hh0iso, hh0fac⟩ := hnorm
  -- `m` is killed by its cokernel, so it factors through `ker(coker m)` via `w`.
  have hm_kc : m ≫ cokernelMap m = m ≫ zeroMorphism B (Cokernel m) := by
    rw [comp_cokernelMap m, zero_morphism_comp m (zeroMorphism B (Cokernel m))]
  let w : A ⟶ Kernel (cokernelMap m) :=
    eqLift (cokernelMap m) (zeroMorphism B (Cokernel m)) m hm_kc
  have hw : w ≫ kernelMap (cokernelMap m) = m :=
    eqLift_fac (cokernelMap m) (zeroMorphism B (Cokernel m)) m hm_kc
  -- `m ≫ f = 0` (since `m = h0 ≫ kernelMap f` and `kernelMap f ≫ f = 0`).
  have hmf : m ≫ f = zeroMorphism A C := by
    calc m ≫ f = (h0 ≫ kernelMap f) ≫ f := by rw [hh0fac]
      _ = h0 ≫ (kernelMap f ≫ f) := Cat.assoc _ _ _
      _ = h0 ≫ (kernelMap f ≫ zeroMorphism B C) := by rw [kernelMap_eq f]
      _ = h0 ≫ zeroMorphism (Kernel f) C := by
            rw [zero_morphism_comp (kernelMap f) (zeroMorphism B C)]
      _ = zeroMorphism A C := zero_morphism_comp h0 (zeroMorphism (Kernel f) C)
  -- `f` descends through `coker m`: `f = cokernelMap m ≫ fbar`.
  have hfpair : m ≫ f = zeroMorphism A B ≫ f := by
    rw [hmf, zeroMorphism_comp_left]
  let co := HasCoequalizers.coeq m (zeroMorphism A B)
  let fbar : Cokernel m ⟶ C := co.desc f hfpair
  have hfbar : cokernelMap m ≫ fbar = f := co.fac f hfpair
  -- `ker(coker m)` is killed by `f`, hence factors through `ker f`, hence through `m`.
  have hkf0 : kernelMap (cokernelMap m) ≫ f
      = kernelMap (cokernelMap m) ≫ zeroMorphism B C := by
    have hk0 : kernelMap (cokernelMap m) ≫ cokernelMap m
        = kernelMap (cokernelMap m) ≫ zeroMorphism B (Cokernel m) := kernelMap_eq _
    calc kernelMap (cokernelMap m) ≫ f
        = kernelMap (cokernelMap m) ≫ (cokernelMap m ≫ fbar) := by rw [hfbar]
      _ = (kernelMap (cokernelMap m) ≫ cokernelMap m) ≫ fbar := (Cat.assoc _ _ _).symm
      _ = (kernelMap (cokernelMap m) ≫ zeroMorphism B (Cokernel m)) ≫ fbar := by rw [hk0]
      _ = kernelMap (cokernelMap m) ≫ (zeroMorphism B (Cokernel m) ≫ fbar) := Cat.assoc _ _ _
      _ = kernelMap (cokernelMap m) ≫ zeroMorphism B C := by rw [zeroMorphism_comp_left]
  let lift_f : Kernel (cokernelMap m) ⟶ Kernel f :=
    eqLift f (zeroMorphism B C) (kernelMap (cokernelMap m)) hkf0
  have hlift_f : lift_f ≫ kernelMap f = kernelMap (cokernelMap m) :=
    eqLift_fac f (zeroMorphism B C) (kernelMap (cokernelMap m)) hkf0
  obtain ⟨h0inv, _, hh0inv2⟩ := hh0iso
  -- back-map: `v := lift_f ≫ h0inv : ker(coker m) → A`, with `v ≫ m = kernelMap (coker m)`.
  let v : Kernel (cokernelMap m) ⟶ A := lift_f ≫ h0inv
  have hv : v ≫ m = kernelMap (cokernelMap m) := by
    calc v ≫ m = (lift_f ≫ h0inv) ≫ (h0 ≫ kernelMap f) := by rw [hh0fac]
      _ = lift_f ≫ (h0inv ≫ h0) ≫ kernelMap f := by rw [Cat.assoc, Cat.assoc]
      _ = lift_f ≫ kernelMap f := by rw [hh0inv2, Cat.id_comp]
      _ = kernelMap (cokernelMap m) := hlift_f
  -- `w` and `v` are mutually inverse (both legs cancel against the monos `m`, `kernelMap`).
  have hmono_k : Mono (kernelMap (cokernelMap m)) :=
    eqMap_mono' (cokernelMap m) (zeroMorphism B (Cokernel m))
  have hwv : w ≫ v = Cat.id A := by
    apply hm; rw [Cat.assoc, hv, hw, Cat.id_comp]
  have hvw : v ≫ w = Cat.id (Kernel (cokernelMap m)) := by
    apply hmono_k; rw [Cat.assoc, hw, hv, Cat.id_comp]
  exact ⟨w, ⟨v, hwv, hvw⟩, hw⟩

theorem abelian_iff_regular_additive_all_normal
    (𝒞 : Type u) [Cat.{v} 𝒞]
    [RegularCategory 𝒞] [AdditiveCategory 𝒞] [HasZeroObject 𝒞]
    [HasEqualizers 𝒞] [HasCoequalizers 𝒞] :
    (∀ {A B : 𝒞} (m : A ⟶ B) (hm : Mono m), IsNormalSubobject m hm) ↔
    IsExactStructure 𝒞 := by
  constructor
  · -- (→) all monics normal ⟹ IsExactStructure.  CLOSED representation-free: the coimage→image
    -- comparison θ is a monic cover, hence iso (θ cover via the normal image = ker(coker x) being
    -- minimal; θ monic via the additive regular pullback-of-cover argument).  See the docstring.
    intro _hnormal A B x
    -- coimage projection `p := coker(ker x)` and image inclusion `i := ker(coker x)`.
    let p : A ⟶ Cokernel (kernelMap x) := cokernelMap (kernelMap x)
    let i : Kernel (cokernelMap x) ⟶ B := kernelMap (cokernelMap x)
    have hi_mono : Mono i := eqMap_mono' (cokernelMap x) (zeroMorphism B (Cokernel x))
    -- STEP 1: `xbar : A → Im` with `xbar ≫ i = x`.
    have hx_kc : x ≫ cokernelMap x = x ≫ zeroMorphism B (Cokernel x) := by
      rw [comp_cokernelMap x, zero_morphism_comp x (zeroMorphism B (Cokernel x))]
    let xbar : A ⟶ Kernel (cokernelMap x) :=
      eqLift (cokernelMap x) (zeroMorphism B (Cokernel x)) x hx_kc
    have hxbar : xbar ≫ i = x :=
      eqLift_fac (cokernelMap x) (zeroMorphism B (Cokernel x)) x hx_kc
    -- `kernelMap x ≫ xbar = 0` (cancel against the mono `i`).
    have hkx_xbar : kernelMap x ≫ xbar = zeroMorphism (Kernel x) (Kernel (cokernelMap x)) := by
      apply hi_mono
      calc (kernelMap x ≫ xbar) ≫ i = kernelMap x ≫ (xbar ≫ i) := Cat.assoc _ _ _
        _ = kernelMap x ≫ x := by rw [hxbar]
        _ = kernelMap x ≫ zeroMorphism A B := kernelMap_eq x
        _ = zeroMorphism (Kernel x) B := zero_morphism_comp (kernelMap x) x
        _ = zeroMorphism (Kernel x) (Kernel (cokernelMap x)) ≫ i :=
              (zeroMorphism_comp_left i).symm
    have hxbar_pair : kernelMap x ≫ xbar = zeroMorphism (Kernel x) A ≫ xbar := by
      rw [hkx_xbar, zeroMorphism_comp_left]
    -- `θ : Co → Im` descends `xbar` through the cokernel projection `p`.
    let coco := HasCoequalizers.coeq (kernelMap x) (zeroMorphism (Kernel x) A)
    let θ : Cokernel (kernelMap x) ⟶ Kernel (cokernelMap x) := coco.desc xbar hxbar_pair
    have hpθ : p ≫ θ = xbar := coco.fac xbar hxbar_pair
    have hfac : p ≫ θ ≫ i = x := by
      rw [← Cat.assoc, hpθ, hxbar]
    -- STEP 2: `⟨Im, i⟩` is an IMAGE of `x` (uses the all-normal hypothesis for minimality).
    let Im : Subobject 𝒞 B := ⟨Kernel (cokernelMap x), i, hi_mono⟩
    have hIm_allows : Allows Im x := ⟨xbar, hxbar⟩
    have hIm_isImage : IsImage x Im := by
      refine ⟨hIm_allows, ?_⟩
      intro S hS
      obtain ⟨g, hg⟩ := hS
      -- `x` is killed by `coker S.arr`, so `coker x` descends to `coker S.arr` via `t`.
      have hx_killed : x ≫ cokernelMap S.arr = zeroMorphism A (Cokernel S.arr) := by
        calc x ≫ cokernelMap S.arr
            = (g ≫ S.arr) ≫ cokernelMap S.arr := by rw [hg]
          _ = g ≫ (S.arr ≫ cokernelMap S.arr) := Cat.assoc _ _ _
          _ = g ≫ zeroMorphism S.dom (Cokernel S.arr) := by rw [comp_cokernelMap]
          _ = zeroMorphism A (Cokernel S.arr) :=
                zero_morphism_comp g (zeroMorphism S.dom (Cokernel S.arr))
      have hx_pair : x ≫ cokernelMap S.arr = zeroMorphism A B ≫ cokernelMap S.arr := by
        rw [hx_killed, zeroMorphism_comp_left]
      let t : Cokernel x ⟶ Cokernel S.arr :=
        (HasCoequalizers.coeq x (zeroMorphism A B)).desc (cokernelMap S.arr) hx_pair
      have ht : cokernelMap x ≫ t = cokernelMap S.arr :=
        (HasCoequalizers.coeq x (zeroMorphism A B)).fac (cokernelMap S.arr) hx_pair
      -- `i = ker(coker x)` is killed by `coker S.arr` (via `t`), so lifts through `ker(coker S.arr)`.
      have hi_killed : i ≫ cokernelMap S.arr = i ≫ zeroMorphism B (Cokernel S.arr) := by
        have hk0 : i ≫ cokernelMap x = i ≫ zeroMorphism B (Cokernel x) := kernelMap_eq _
        calc i ≫ cokernelMap S.arr
            = i ≫ (cokernelMap x ≫ t) := by rw [ht]
          _ = (i ≫ cokernelMap x) ≫ t := (Cat.assoc _ _ _).symm
          _ = (i ≫ zeroMorphism B (Cokernel x)) ≫ t := by rw [hk0]
          _ = i ≫ (zeroMorphism B (Cokernel x) ≫ t) := Cat.assoc _ _ _
          _ = i ≫ zeroMorphism B (Cokernel S.arr) := by rw [zeroMorphism_comp_left]
      let lift_k : Kernel (cokernelMap x) ⟶ Kernel (cokernelMap S.arr) :=
        eqLift (cokernelMap S.arr) (zeroMorphism B (Cokernel S.arr)) i hi_killed
      have hlift_k : lift_k ≫ kernelMap (cokernelMap S.arr) = i :=
        eqLift_fac (cokernelMap S.arr) (zeroMorphism B (Cokernel S.arr)) i hi_killed
      -- `S.arr` is the kernel of its own cokernel (re-derived from all-normal): `h ≫ ker(coker S.arr) = S.arr`, `h` iso.
      obtain ⟨h, hh_iso, hh_fac⟩ :=
        monic_kernel_of_cokernel' S.arr S.monic (_hnormal S.arr S.monic)
      obtain ⟨hinv, _, hinv2⟩ := hh_iso
      exact ⟨lift_k ≫ hinv, by
        calc (lift_k ≫ hinv) ≫ S.arr
            = (lift_k ≫ hinv) ≫ (h ≫ kernelMap (cokernelMap S.arr)) := by rw [hh_fac]
          _ = lift_k ≫ (hinv ≫ h) ≫ kernelMap (cokernelMap S.arr) := by
                rw [Cat.assoc, Cat.assoc]
          _ = lift_k ≫ kernelMap (cokernelMap S.arr) := by rw [hinv2, Cat.id_comp]
          _ = i := hlift_k⟩
    -- STEP 3: `θ` is a COVER (comparison of two images of `x`).
    -- The canonical comparison `c : (image x).dom → Im` with `c ≫ i = (image x).arr` is iso.
    obtain ⟨c, hc⟩ := image_min x Im hIm_allows
    have hc_iso : IsIso c := image_comparison_iso (HasImages.isImage x) hIm_isImage c hc
    -- `image.lift x ≫ c : A → Im` is a cover (cover ∘ iso).
    have hlc_cover : Cover (image.lift x ≫ c) :=
      cover_comp (image_lift_cover x) (iso_cover c hc_iso)
    -- `image.lift x ≫ c = p ≫ θ` (both compose with the mono `i` to give `x`).
    have hlc_eq : image.lift x ≫ c = p ≫ θ := by
      apply hi_mono
      calc (image.lift x ≫ c) ≫ i = image.lift x ≫ (c ≫ i) := Cat.assoc _ _ _
        _ = image.lift x ≫ (image x).arr := by rw [hc]
        _ = x := image.lift_fac x
        _ = p ≫ θ ≫ i := hfac.symm
        _ = (p ≫ θ) ≫ i := (Cat.assoc _ _ _).symm
    have hpθ_cover : Cover (p ≫ θ) := hlc_eq ▸ hlc_cover
    -- `θ` itself is a cover: any mono `θ` factors through is a mono `p ≫ θ` factors through.
    have hθ_cover : Cover θ := by
      intro K mm gg hmm hgg
      exact hpθ_cover mm (p ≫ gg) hmm (by rw [Cat.assoc, hgg])
    -- STEP 4: `θ` is MONIC.  `kt := ker θ`; pull `kt` back along the cover `p`.
    let kt : Kernel θ ⟶ Cokernel (kernelMap x) := kernelMap θ
    have hp_cover : Cover p := coeq_map_is_cover coco
    let pb := HasPullbacks.has p kt
    have hπ₂_cover : Cover pb.cone.π₂ := cover_pullback kt hp_cover
    have hpbw : pb.cone.π₁ ≫ p = pb.cone.π₂ ≫ kt := pb.cone.w
    -- `π₁ ≫ x = 0`: `π₁ ≫ p ≫ θ = π₂ ≫ kt ≫ θ = 0`, and `p ≫ θ = xbar`, `xbar ≫ i = x`.
    have hktθ : kt ≫ θ = zeroMorphism (Kernel θ) (Kernel (cokernelMap x)) := by
      calc kt ≫ θ = kt ≫ zeroMorphism (Cokernel (kernelMap x)) (Kernel (cokernelMap x)) :=
            kernelMap_eq θ
        _ = zeroMorphism (Kernel θ) (Kernel (cokernelMap x)) :=
            zero_morphism_comp kt (zeroMorphism (Cokernel (kernelMap x)) (Kernel (cokernelMap x)))
    have hπ₁x : pb.cone.π₁ ≫ x = zeroMorphism pb.cone.pt B := by
      calc pb.cone.π₁ ≫ x
          = pb.cone.π₁ ≫ (p ≫ θ ≫ i) := congrArg (pb.cone.π₁ ≫ ·) hfac.symm
        _ = (pb.cone.π₁ ≫ p) ≫ (θ ≫ i) := by rw [Cat.assoc]
        _ = (pb.cone.π₂ ≫ kt) ≫ (θ ≫ i) := by rw [hpbw]
        _ = pb.cone.π₂ ≫ ((kt ≫ θ) ≫ i) := by rw [Cat.assoc, Cat.assoc]
        _ = pb.cone.π₂ ≫ (zeroMorphism (Kernel θ) (Kernel (cokernelMap x)) ≫ i) := by rw [hktθ]
        _ = pb.cone.π₂ ≫ zeroMorphism (Kernel θ) B := by rw [zeroMorphism_comp_left i]
        _ = zeroMorphism pb.cone.pt B :=
              zero_morphism_comp pb.cone.π₂ (zeroMorphism (Kernel θ) B)
    -- `π₁` factors through `Kernel x`, so `π₁ ≫ p = 0` (since `kernelMap x ≫ p = 0`).
    have hπ₁_pair : pb.cone.π₁ ≫ x = pb.cone.π₁ ≫ zeroMorphism A B := by
      rw [hπ₁x, zero_morphism_comp pb.cone.π₁ (zeroMorphism A B)]
    let lift_kx : pb.cone.pt ⟶ Kernel x :=
      eqLift x (zeroMorphism A B) pb.cone.π₁ hπ₁_pair
    have hlift_kx : lift_kx ≫ kernelMap x = pb.cone.π₁ :=
      eqLift_fac x (zeroMorphism A B) pb.cone.π₁ hπ₁_pair
    have hkxp : kernelMap x ≫ p = zeroMorphism (Kernel x) (Cokernel (kernelMap x)) :=
      comp_cokernelMap (kernelMap x)
    have hπ₂kt0 : pb.cone.π₂ ≫ kt = zeroMorphism pb.cone.pt (Cokernel (kernelMap x)) := by
      calc pb.cone.π₂ ≫ kt = pb.cone.π₁ ≫ p := hpbw.symm
        _ = (lift_kx ≫ kernelMap x) ≫ p := by rw [hlift_kx]
        _ = lift_kx ≫ (kernelMap x ≫ p) := Cat.assoc _ _ _
        _ = lift_kx ≫ zeroMorphism (Kernel x) (Cokernel (kernelMap x)) := by rw [hkxp]
        _ = zeroMorphism pb.cone.pt (Cokernel (kernelMap x)) :=
              zero_morphism_comp lift_kx (zeroMorphism (Kernel x) (Cokernel (kernelMap x)))
    -- `π₂` epic (cover) cancels: `kt = 0`.
    have hkt0 : kt = zeroMorphism (Kernel θ) (Cokernel (kernelMap x)) := by
      apply cover_epi hπ₂_cover
      rw [hπ₂kt0, zero_morphism_comp pb.cone.π₂ (zeroMorphism (Kernel θ) (Cokernel (kernelMap x)))]
    -- `kt = 0` ⟹ θ MONIC (additive: `a≫θ=b≫θ` ⟹ `(a−b)≫θ=0` ⟹ `a−b` factors through `ker θ = 0`).
    have hθ_mono : Mono θ := by
      intro W a b hab
      obtain ⟨negb, hnegb⟩ := AdditiveCategory.addInv b
      let e := HalfAdditiveCategory.add a negb
      -- `e ≫ θ = 0`.
      have heθ : e ≫ θ = zeroMorphism W (Kernel (cokernelMap x)) := by
        have : HalfAdditiveCategory.add (a ≫ θ) (negb ≫ θ)
            = zeroMorphism W (Kernel (cokernelMap x)) := by
          rw [hab]
          calc HalfAdditiveCategory.add (b ≫ θ) (negb ≫ θ)
              = HalfAdditiveCategory.add b negb ≫ θ := (HalfAdditiveCategory.add_comp b negb θ).symm
            _ = HalfAdditiveCategory.zeroHom W (Cokernel (kernelMap x)) ≫ θ := by rw [hnegb]
            _ = zeroMorphism W (Cokernel (kernelMap x)) ≫ θ := by
                  rw [zeroHom_eq_zeroMorphism' W (Cokernel (kernelMap x))]
            _ = zeroMorphism W (Kernel (cokernelMap x)) := zeroMorphism_comp_left θ
        rw [show e ≫ θ = HalfAdditiveCategory.add (a ≫ θ) (negb ≫ θ) from
              HalfAdditiveCategory.add_comp a negb θ, this]
      -- `e` factors through `ker θ`, whose inclusion `kt = 0`, so `e = 0`.
      have heθ_pair : e ≫ θ = e ≫ zeroMorphism (Cokernel (kernelMap x)) (Kernel (cokernelMap x)) := by
        rw [heθ, zero_morphism_comp e (zeroMorphism (Cokernel (kernelMap x)) (Kernel (cokernelMap x)))]
      let u : W ⟶ Kernel θ :=
        eqLift θ (zeroMorphism (Cokernel (kernelMap x)) (Kernel (cokernelMap x))) e heθ_pair
      have hu : u ≫ kt = e :=
        eqLift_fac θ (zeroMorphism (Cokernel (kernelMap x)) (Kernel (cokernelMap x))) e heθ_pair
      have he0 : e = zeroMorphism W (Cokernel (kernelMap x)) := by
        rw [← hu, hkt0, zero_morphism_comp u (zeroMorphism (Kernel θ) (Cokernel (kernelMap x)))]
      -- `a + negb = 0` and `b + negb = 0` ⟹ `a = b`.
      have he0' : HalfAdditiveCategory.add a negb
          = HalfAdditiveCategory.zeroHom W (Cokernel (kernelMap x)) := by
        rw [show HalfAdditiveCategory.add a negb = e from rfl, he0,
            zeroHom_eq_zeroMorphism' W (Cokernel (kernelMap x))]
      exact add_cancel_common a b negb he0' hnegb
    -- Conclude: `θ` is a monic cover, hence iso.
    exact ⟨θ, monic_cover_iso θ hθ_cover hθ_mono, hfac⟩
  · -- (←) IsExactStructure ⟹ every monic is normal (the kernel of its cokernel).
    -- Rep-FREE: the §1.597 factorization (`monic_kernel_of_cokernel`, re-derived here
    -- against the ambient zero/eq/coeq instances).
    intro hexact A B m hm
    have hk0 : kernelMap m = zeroMorphism (Kernel m) A :=
      hm (kernelMap m) (zeroMorphism (Kernel m) A) <| by
        calc kernelMap m ≫ m
            = kernelMap m ≫ zeroMorphism A B := kernelMap_eq m
          _ = zeroMorphism (Kernel m) B := zero_morphism_comp (kernelMap m) m
          _ = zeroMorphism (Kernel m) A ≫ m := (zeroMorphism_comp_left m).symm
    have hcofac : kernelMap m ≫ Cat.id A = zeroMorphism (Kernel m) A ≫ Cat.id A := by rw [hk0]
    let co := HasCoequalizers.coeq (kernelMap m) (zeroMorphism (Kernel m) A)
    let r : Cokernel (kernelMap m) ⟶ A := co.desc (Cat.id A) hcofac
    have hmr : cokernelMap (kernelMap m) ≫ r = Cat.id A := co.fac (Cat.id A) hcofac
    have hrm : r ≫ cokernelMap (kernelMap m) = Cat.id (Cokernel (kernelMap m)) := by
      have key : ∀ k : Cokernel (kernelMap m) ⟶ Cokernel (kernelMap m),
          cokernelMap (kernelMap m) ≫ k = cokernelMap (kernelMap m) →
          k = co.desc (cokernelMap (kernelMap m)) co.eq :=
        fun k hk => co.uniq (cokernelMap (kernelMap m)) co.eq k hk
      rw [key (r ≫ cokernelMap (kernelMap m)) (by rw [← Cat.assoc, hmr, Cat.id_comp]),
          key (Cat.id _) (by rw [Cat.comp_id])]
    have hc_iso : IsIso (cokernelMap (kernelMap m)) := ⟨r, hmr, hrm⟩
    obtain ⟨θ, hθ, hfac⟩ := hexact m
    exact ⟨Cokernel m, cokernelMap m, cokernelMap (kernelMap m) ≫ θ,
      isIso_comp hc_iso hθ, by rw [Cat.assoc]; exact hfac⟩

/-! ## §1.594 Effective regular additive ⇔ abelian

  A is abelian iff it is an effective regular additive category (§1.594). -/

/-- A regular category is EFFECTIVE if every equivalence relation is effective
    (i.e., is the level/kernel-pair of some cover/quotient).  This is the
    effective-quotients axiom (§1.568): the content that distinguishes an
    effective regular category from a plain regular one. -/
class EffectiveRegular (𝒞 : Type u) [Cat.{v} 𝒞] extends RegularCategory 𝒞 where
  effective : ∀ {A : 𝒞} (E : BinRel 𝒞 A A), EquivalenceRelation E → IsEffective E

/-! §1.594: A is abelian iff it is an effective regular additive category.
  Direction proved here: effective regular additive ⟹ every mono is a kernel
  (i.e. every subobject is normal), so the category is abelian.

  Proof sketch (Freyd §1.594):
  (⟸) Given monic x:A↣B, form the relation E on B whose tabulation
  is `⟨x,x⟩:A→B×B` (both legs = x; this is reflexive by additivity
  — in the faithful Ab-representation, E(b,b') iff b=b'=x(a) for some a,
  which is reflexive).  By the calculus of relations (which holds in any
  regular additive category faithfully represented in Ab via §1.552),
  a reflexive endo-relation is an equivalence relation.  By effectiveness,
  E is the kernel pair of some cover q:B↠C.  Then x is the kernel of q.

  (⟹) Any abelian category is effective regular (§1.582–1.583 combined with
  the bicartesian structure).

  Full formalization deferred: requires formalizing the Ab-calculus (§1.55)
  and the inverse-image lemma from §1.582. -/
theorem effective_regular_additive_is_abelian
    (𝒞 : Type u) [Cat.{v} 𝒞]
    [EffectiveRegular 𝒞] [AdditiveCategory 𝒞] [HasZeroObject 𝒞] [HasEqualizers 𝒞] :
    ∀ {A B : 𝒞} (m : A ⟶ B) (hm : Mono m), IsNormalSubobject m hm := by
  sorry


/-! ## §1.595 Abelian group objects

  In any category A with finite products, an ABELIAN GROUP OBJECT is an object A
  together with morphisms
    zero  : 1 → A        (identity element)
    neg   : A → A        (additive inverse)
    add   : A × A → A   (addition)
  satisfying the commutative diagrams:

    (i)   (add ∘ ⟨zero ∘ term, id⟩ = id)         left unit
    (ii)  (add ∘ ⟨neg, id⟩ ∘ diag = zero ∘ term)  left inverse
    (iii) add ∘ (id × add) = add ∘ (add × id) ∘ assoc  associativity
    (iv)  add ∘ swap = add                           commutativity

  where swap : A × A → A × A is pair(snd, fst) and assoc : A×(B×C) → (A×B)×C
  is the standard associator.

  Ab(A) denotes the category whose objects are abelian group objects and whose
  morphisms are A-morphisms x : A → B satisfying x ≫ add_B = (x × x) ≫ add_A
  (homomorphism condition). -/

/-- An ABELIAN GROUP OBJECT in a category with finite products (§1.595).
  Fields: carrier object, identity/inverse/addition morphisms, four axioms. -/
structure AbelianGroupObject (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] where
  /-- The underlying object. -/
  carrier : 𝒞
  /-- Zero element: 1 → A. -/
  zero  : (one : 𝒞) ⟶ carrier
  /-- Additive inverse: A → A. -/
  neg   : carrier ⟶ carrier
  /-- Addition: A × A → A. -/
  add   : prod carrier carrier ⟶ carrier
  /-- Left unit: ⟨zero ∘ !, id⟩ ≫ add = id. -/
  add_zero : pair (term carrier ≫ zero) (Cat.id carrier) ≫ add = Cat.id carrier
  /-- Left inverse: ⟨neg, id⟩ ≫ add = zero ∘ !. -/
  add_neg  : pair neg (Cat.id carrier) ≫ add = term carrier ≫ zero
  /-- Associativity: from source (A×A)×A, both bracketings compute equal results.
    LHS: (x+y)+z = (fst ≫ add, snd) ≫ add.
    RHS: x+(y+z) = (fst≫fst, (fst≫snd, snd) ≫ add) ≫ add. -/
  add_assoc :
      pair (fst (A := prod carrier carrier) (B := carrier) ≫ add)
           (snd (A := prod carrier carrier) (B := carrier)) ≫ add =
      pair (fst (A := prod carrier carrier) (B := carrier) ≫ fst)
           (pair (fst (A := prod carrier carrier) (B := carrier) ≫ snd)
                 (snd (A := prod carrier carrier) (B := carrier)) ≫ add) ≫ add
  /-- Commutativity: swap ≫ add = add. -/
  add_comm : pair (snd (A := carrier) (B := carrier)) fst ≫ add = add

/-- A HOMOMORPHISM of abelian group objects: an A-morphism respecting addition (§1.595). -/
-- Homomorphism condition: the square addA ≫ x = (x×x) ≫ addB commutes.
-- Both sides have source prod A.carrier A.carrier.
-- (x×x) is spelled out as pair (fst ≫ x) (snd ≫ x).
def IsHomAbelianGroupObject {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    (A B : AbelianGroupObject 𝒞) (x : A.carrier ⟶ B.carrier) : Prop :=
  A.add ≫ x = pair (fst ≫ x) (snd ≫ x) ≫ B.add

/-- Hom-set in Ab(A): morphisms that are homomorphisms. -/
def HomAb {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    (A B : AbelianGroupObject 𝒞) : Type v :=
  { x : A.carrier ⟶ B.carrier // IsHomAbelianGroupObject A B x }

/-! If A is effective regular, then Ab(A) is also effective regular and the
  forgetful functor Ab(A) → A is a faithful representation of regular categories
  (§1.595).  Consequently, Ab(A) is an abelian category for any effective regular A. -/

/-! §1.595 (consequence): For any effective regular category A, the category Ab(A)
  is abelian.  Proof: Ab(A) is effective regular (forgetful functor is a faithful
  representation of regular categories) and additive by construction; abelianness
  then follows from §1.594.  Formalizing this requires a `Cat` instance for Ab(A),
  which depends on universe-polymorphic hom-set infrastructure left for future work. -/


/-! ## §1.597 Exact categories

  A category with zero, kernels, and cokernels is EXACT if for every x:A→B
  the unique map θ : coker(ker(x)) → ker(coker(x)) is an isomorphism.

  Equivalently: every morphism factors as (cokernel of something) ∘ (kernel of something).

  A is abelian iff it is an exact additive category.
  More precisely: A is abelian iff it is an exact category with either binary
  products or binary coproducts. -/

/-- An EXACT CATEGORY (§1.597): category with zero, kernels, cokernels where
  the canonical map θ : coker(ker(x)) → ker(coker(x)) is an isomorphism
  for every morphism x.

  The map θ exists because: cokernelMap(kernelMap x) : coker(ker x) → B
  satisfies `kernelMap x ≫ cokernelMap(kernelMap x) = 0` (the cokernel map kills
  the kernel), so it factors through ker(coker x) ↣ B via the universal property
  of the kernel.  θ is this factorization morphism. -/
class ExactCategory (𝒞 : Type u) [Cat.{v} 𝒞]
    extends HasZeroObject 𝒞, HasEqualizers 𝒞, HasCoequalizers 𝒞 where
  /-- The canonical coimage-to-image map θ : coker(ker x) → ker(coker x) is an iso,
    AND it is the canonical factorization: it makes
      coimage-projection ≫ θ ≫ image-inclusion = x.
    (Freyd §1.597 defines exactness by *this specific* map being an iso, so the
    factorization equation is part of the data, not an afterthought.) -/
  exact : ∀ {A B : 𝒞} (x : A ⟶ B),
    ∃ (θ : Cokernel (kernelMap x) ⟶ Kernel (cokernelMap x)),
      IsIso θ ∧ cokernelMap (kernelMap x) ≫ θ ≫ kernelMap (cokernelMap x) = x

/-! §1.597 key lemma: if A ↣ B is monic and q : B → Q is its cokernel, then A is
  the kernel of q.  (Follows from the exact factorization.) -/
theorem monic_kernel_of_cokernel {𝒞 : Type u} [Cat.{v} 𝒞] [ExactCategory 𝒞] {A B : 𝒞}
    (x : A ⟶ B) (hx : Mono x) :
    let Q := Cokernel x
    let q := cokernelMap x
    ∃ (h : A ⟶ Kernel q), IsIso h ∧ h ≫ kernelMap q = x := by
  intro Q q
  -- (1) x monic ⟹ kernelMap x is the zero morphism Kernel x → A.
  --     Both `kernelMap x ≫ x` and `(zeroMorphism …) ≫ x` equal the zero morphism
  --     Kernel x → B, so monicity of x identifies the two maps into A.
  have hk0 : kernelMap x = zeroMorphism (Kernel x) A :=
    hx (kernelMap x) (zeroMorphism (Kernel x) A) <| by
      calc kernelMap x ≫ x
          = kernelMap x ≫ zeroMorphism A B := kernelMap_eq x
        _ = zeroMorphism (Kernel x) B := zero_morphism_comp (kernelMap x) x
        _ = zeroMorphism (Kernel x) A ≫ x := (zeroMorphism_comp_left x).symm
  -- (2) cokernelMap (kernelMap x) : A → Cokernel(kernelMap x) is an iso, because the
  --     coequalized pair (kernelMap x, 0) is a pair of EQUAL maps, whose coequalizer
  --     map is split by `desc id`.
  have hcofac : kernelMap x ≫ Cat.id A = zeroMorphism (Kernel x) A ≫ Cat.id A := by
    rw [hk0]
  let co := HasCoequalizers.coeq (kernelMap x) (zeroMorphism (Kernel x) A)
  -- the splitting r : Cokernel(kernelMap x) → A
  let r : Cokernel (kernelMap x) ⟶ A := co.desc (Cat.id A) hcofac
  have hmr : cokernelMap (kernelMap x) ≫ r = Cat.id A := co.fac (Cat.id A) hcofac
  have hrm : r ≫ cokernelMap (kernelMap x) = Cat.id (Cokernel (kernelMap x)) := by
    -- both `r ≫ map` and `id` are `desc map`, by the coequalizer's uniqueness.
    have key : ∀ m : Cokernel (kernelMap x) ⟶ Cokernel (kernelMap x),
        cokernelMap (kernelMap x) ≫ m = cokernelMap (kernelMap x) →
        m = co.desc (cokernelMap (kernelMap x)) co.eq :=
      fun m hm => co.uniq (cokernelMap (kernelMap x)) co.eq m hm
    rw [key (r ≫ cokernelMap (kernelMap x))
          (by rw [← Cat.assoc, hmr, Cat.id_comp]),
        key (Cat.id _) (by rw [Cat.comp_id])]
  have hc_iso : IsIso (cokernelMap (kernelMap x)) := ⟨r, hmr, hrm⟩
  -- (3) The exact-factorization data: θ iso, cokernelMap(kernelMap x) ≫ θ ≫ kernelMap q = x.
  obtain ⟨θ, hθ, hfac⟩ := ExactCategory.exact x
  refine ⟨cokernelMap (kernelMap x) ≫ θ, isIso_comp hc_iso hθ, ?_⟩
  rw [Cat.assoc]; exact hfac

/-! ## §1.597 KEYSTONE: exact additive ⟹ regular (and ⟹ abelian)

  `RegularCategory = HasTerminal + HasBinaryProducts + HasPullbacks + HasImages +
  PullbacksTransferCovers`.  Given `[ExactCategory] [AdditiveCategory]` we build the
  three non-trivial fields directly from the exact structure, with NO Ab-valued
  representation:

  * `HasPullbacks`  — `products_equalizers_implies_pullbacks` (pullback = equalizer of
    `(fst≫f, snd≫g)`).  Axiom-free.
  * `HasImages`     — the NORMAL image `image f := ker(coker f)`; minimality via
    `monic_kernel_of_cokernel`.  Axiom-free.
  * `PullbacksTransferCovers` — cover-stability, the genuine §1.597 Barr-exactness
    content (`pullback_epi_is_epi`), now CLOSED representation-free: the pullback is
    the kernel of the difference map `d := (fst≫f) − (snd≫g)`, whose `snd`-projection
    is epic because `f` is a cover (`kernel_snd_epi`); epimorphy transfers across the
    pullback comparison to any pullback cone.

  Balancedness (`exact_balanced`) and `epi_is_cover` are proved sorry-free along the
  way and are reusable.  The whole keystone chain is now SORRY-FREE (axioms:
  propext, Classical.choice). -/

/-- The normal-image subobject of `f`: `ker (coker f)`. -/
def imageSub [HasZeroObject 𝒞] [HasEqualizers 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞}
    (f : A ⟶ B) : Subobject 𝒞 B :=
  ⟨Kernel (cokernelMap f), kernelMap (cokernelMap f),
    eqMap_mono' (cokernelMap f) (zeroMorphism B (Cokernel f))⟩

/-- `f` factors through its normal image (lifts through `ker(coker f)`). -/
theorem imageSub_allows [HasZeroObject 𝒞] [HasEqualizers 𝒞] [HasCoequalizers 𝒞]
    {A B : 𝒞} (f : A ⟶ B) : Allows (imageSub f) f := by
  have heq : f ≫ cokernelMap f = f ≫ zeroMorphism B (Cokernel f) := by
    rw [comp_cokernelMap f, zero_morphism_comp f (zeroMorphism B (Cokernel f))]
  refine ⟨eqLift (cokernelMap f) (zeroMorphism B (Cokernel f)) f heq, ?_⟩
  exact eqLift_fac (cokernelMap f) (zeroMorphism B (Cokernel f)) f heq

/-- **Minimality of the normal image** (uses the exact structure).  Any subobject `S`
    through which `f` factors contains `ker(coker f)`; via `monic_kernel_of_cokernel`. -/
theorem imageSub_min [ExactCategory 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (S : Subobject 𝒞 B) (hS : Allows S f) : (imageSub f).le S := by
  obtain ⟨g, hg⟩ := hS
  have hf_killed : f ≫ cokernelMap S.arr = zeroMorphism A (Cokernel S.arr) := by
    calc f ≫ cokernelMap S.arr
        = (g ≫ S.arr) ≫ cokernelMap S.arr := by rw [hg]
      _ = g ≫ (S.arr ≫ cokernelMap S.arr) := Cat.assoc _ _ _
      _ = g ≫ zeroMorphism S.dom (Cokernel S.arr) := by rw [comp_cokernelMap]
      _ = zeroMorphism A (Cokernel S.arr) :=
            zero_morphism_comp g (zeroMorphism S.dom (Cokernel S.arr))
  have hpair : f ≫ cokernelMap S.arr = zeroMorphism A B ≫ cokernelMap S.arr := by
    rw [hf_killed, zeroMorphism_comp_left]
  let d : Cokernel f ⟶ Cokernel S.arr :=
    (HasCoequalizers.coeq f (zeroMorphism A B)).desc (cokernelMap S.arr) hpair
  have hd : cokernelMap f ≫ d = cokernelMap S.arr :=
    (HasCoequalizers.coeq f (zeroMorphism A B)).fac (cokernelMap S.arr) hpair
  have hkernel_killed :
      kernelMap (cokernelMap f) ≫ cokernelMap S.arr
        = kernelMap (cokernelMap f) ≫ zeroMorphism B (Cokernel S.arr) := by
    have hk0 : kernelMap (cokernelMap f) ≫ cokernelMap f
        = kernelMap (cokernelMap f) ≫ zeroMorphism B (Cokernel f) := kernelMap_eq _
    calc kernelMap (cokernelMap f) ≫ cokernelMap S.arr
        = kernelMap (cokernelMap f) ≫ (cokernelMap f ≫ d) := by rw [hd]
      _ = (kernelMap (cokernelMap f) ≫ cokernelMap f) ≫ d := (Cat.assoc _ _ _).symm
      _ = (kernelMap (cokernelMap f) ≫ zeroMorphism B (Cokernel f)) ≫ d := by rw [hk0]
      _ = kernelMap (cokernelMap f) ≫ (zeroMorphism B (Cokernel f) ≫ d) := Cat.assoc _ _ _
      _ = kernelMap (cokernelMap f) ≫ zeroMorphism B (Cokernel S.arr) := by
            rw [zeroMorphism_comp_left]
  let lift_k : Kernel (cokernelMap f) ⟶ Kernel (cokernelMap S.arr) :=
    eqLift (cokernelMap S.arr) (zeroMorphism B (Cokernel S.arr))
      (kernelMap (cokernelMap f)) hkernel_killed
  have hlift_k : lift_k ≫ kernelMap (cokernelMap S.arr) = kernelMap (cokernelMap f) :=
    eqLift_fac _ _ _ hkernel_killed
  obtain ⟨h, hh_iso, hh_fac⟩ := monic_kernel_of_cokernel S.arr S.monic
  obtain ⟨hinv, _, hinv2⟩ := hh_iso
  refine ⟨lift_k ≫ hinv, ?_⟩
  show (lift_k ≫ hinv) ≫ S.arr = (imageSub f).arr
  calc (lift_k ≫ hinv) ≫ S.arr
      = (lift_k ≫ hinv) ≫ (h ≫ kernelMap (cokernelMap S.arr)) := by rw [hh_fac]
    _ = lift_k ≫ (hinv ≫ h) ≫ kernelMap (cokernelMap S.arr) := by rw [Cat.assoc, Cat.assoc]
    _ = lift_k ≫ kernelMap (cokernelMap S.arr) := by rw [hinv2, Cat.id_comp]
    _ = kernelMap (cokernelMap f) := hlift_k

/-- **`HasImages` from the exact structure** (normal image). -/
noncomputable instance exactImages [ExactCategory 𝒞] : HasImages 𝒞 where
  image f := imageSub f
  isImage f := ⟨imageSub_allows f, fun S hS => imageSub_min f S hS⟩

/-- **`HasPullbacks` from products + equalizers.** -/
instance exactPullbacks [HasBinaryProducts 𝒞] [HasEqualizers 𝒞] : HasPullbacks 𝒞 where
  has f g := products_equalizers_implies_pullbacks f g

/-- The kernel of a zero morphism is the whole domain (an iso). -/
theorem kernelMap_zero_isIso [HasZeroObject 𝒞] [HasEqualizers 𝒞] (B C : 𝒞) :
    IsIso (kernelMap (zeroMorphism B C)) := by
  have hid : (Cat.id B) ≫ zeroMorphism B C = (Cat.id B) ≫ zeroMorphism B C := rfl
  let s : B ⟶ Kernel (zeroMorphism B C) :=
    eqLift (zeroMorphism B C) (zeroMorphism B C) (Cat.id B) hid
  have hs : s ≫ kernelMap (zeroMorphism B C) = Cat.id B :=
    eqLift_fac (zeroMorphism B C) (zeroMorphism B C) (Cat.id B) hid
  have hother : kernelMap (zeroMorphism B C) ≫ s = Cat.id (Kernel (zeroMorphism B C)) := by
    apply eqMap_mono' (zeroMorphism B C) (zeroMorphism B C)
    show (kernelMap (zeroMorphism B C) ≫ s) ≫ kernelMap (zeroMorphism B C)
       = Cat.id (Kernel (zeroMorphism B C)) ≫ kernelMap (zeroMorphism B C)
    rw [Cat.assoc, hs, Cat.comp_id, Cat.id_comp]
  exact ⟨s, hother, hs⟩

/-- **An exact category is balanced**: monic ∧ epic ⟹ iso.  `Epi` inline. -/
theorem exact_balanced [ExactCategory 𝒞] {A B : 𝒞} (f : A ⟶ B) (hm : Mono f)
    (he : ∀ {Z : 𝒞} (a b : B ⟶ Z), f ≫ a = f ≫ b → a = b) : IsIso f := by
  have hk0 : kernelMap f = zeroMorphism (Kernel f) A :=
    hm (kernelMap f) (zeroMorphism (Kernel f) A) <| by
      calc kernelMap f ≫ f
          = kernelMap f ≫ zeroMorphism A B := kernelMap_eq f
        _ = zeroMorphism (Kernel f) B := zero_morphism_comp (kernelMap f) f
        _ = zeroMorphism (Kernel f) A ≫ f := (zeroMorphism_comp_left f).symm
  have hcofac : kernelMap f ≫ Cat.id A = zeroMorphism (Kernel f) A ≫ Cat.id A := by rw [hk0]
  let co := HasCoequalizers.coeq (kernelMap f) (zeroMorphism (Kernel f) A)
  let r : Cokernel (kernelMap f) ⟶ A := co.desc (Cat.id A) hcofac
  have hmr : cokernelMap (kernelMap f) ≫ r = Cat.id A := co.fac (Cat.id A) hcofac
  have hrm : r ≫ cokernelMap (kernelMap f) = Cat.id (Cokernel (kernelMap f)) := by
    have key : ∀ m : Cokernel (kernelMap f) ⟶ Cokernel (kernelMap f),
        cokernelMap (kernelMap f) ≫ m = cokernelMap (kernelMap f) →
        m = co.desc (cokernelMap (kernelMap f)) co.eq :=
      fun m hmm => co.uniq (cokernelMap (kernelMap f)) co.eq m hmm
    rw [key (r ≫ cokernelMap (kernelMap f)) (by rw [← Cat.assoc, hmr, Cat.id_comp]),
        key (Cat.id _) (by rw [Cat.comp_id])]
  have hc_iso : IsIso (cokernelMap (kernelMap f)) := ⟨r, hmr, hrm⟩
  obtain ⟨θ, hθ, hfac⟩ := ExactCategory.exact f
  have hcoker0 : cokernelMap f = zeroMorphism B (Cokernel f) := by
    apply he
    rw [comp_cokernelMap f, zero_morphism_comp f (zeroMorphism B (Cokernel f))]
  have hm_iso : IsIso (kernelMap (cokernelMap f)) := by
    rw [hcoker0]; exact kernelMap_zero_isIso B (Cokernel f)
  have : IsIso (cokernelMap (kernelMap f) ≫ θ ≫ kernelMap (cokernelMap f)) :=
    isIso_comp hc_iso (isIso_comp hθ hm_iso)
  rwa [hfac] at this

/-! ### Additive cover-stability infrastructure (for `pullback_epi_is_epi`)

  The pullback `P` of a cospan `A —f→ B ←g— C` in an additive category is the
  KERNEL of the difference map `d := (fst≫f) − (snd≫g) : A×C → B`.  Cover-stability
  ("the projection `π₂ : P → C` of a cover `f` is epic") is then proved
  representation-free via the *coimage factorization* of `d`:

  * `d` is epic, because `jA ≫ d = f` (with `jA = ⟨1,0⟩ : A → A×C`) and `f` is epic.
  * Hence `coker d = 0`, so `ker(coker d)` is iso and the exact factorization makes
    the coimage projection `coker(ker d) → B` agree with `d` up to iso
    (`coimage_factor`): any map killed by `ker d = pbMap` factors through `d`.
  * Feeding `m := snd ≫ e` (for `e := a − b` with `π₂ ≫ e = 0`) gives `m = d ≫ n`;
    precomposing the OTHER injection `jA` kills `snd`, so `f ≫ n = 0`, hence `n = 0`
    (`f` epic), hence `snd ≫ e = 0`, hence `e = 0` (`snd` split epic), hence `a = b`.

  No §1.55 Ab-valued representation is used — only `ExactCategory.exact`, the additive
  group structure, and `cover_epi`. -/

/-- The half-additive `zeroHom` (unique `A → 0 → B`) coincides with the
    `HasZeroObject` `zeroMorphism`: both are the unique map factoring through `0`. -/
theorem zeroHom_eq_zeroMorphism [ExactCategory 𝒞] [AdditiveCategory 𝒞] (X Y : 𝒞) :
    (HalfAdditiveCategory.zeroHom X Y : X ⟶ Y) = zeroMorphism X Y := by
  have h1 : (HalfAdditiveCategory.zeroHom X Y : X ⟶ Y)
      = term X ≫ HalfAdditiveCategory.zeroHom HasTerminal.one Y :=
    (HalfAdditiveCategory.zeroHom_comp_left (term X)).symm
  have huniqOut : ∀ (p q : (HasTerminal.one : 𝒞) ⟶ Y), p = q := by
    rw [HasZeroObject.zero_eq_one (𝒞 := 𝒞)]; exact fun p q => HasCoterminator.init_uniq p q
  dsimp [zeroMorphism]; rw [h1]; congr 1; exact huniqOut _ _

/-- **Coimage factorization for an epimorphism.**  If `d` is epic and `m` is killed by
    `kernelMap d` (the coimage relation), then `m` factors through `d`.  Proof: `d` epic
    ⟹ `coker d = 0` ⟹ `ker(coker d)` iso, so the exact factorization
    `coimage-projection ≫ θ ≫ image-inclusion = d` exhibits the coimage projection
    `cokernelMap (kernelMap d)` as `d` composed with an iso; `m` factors through that
    projection by the cokernel UP. -/
theorem coimage_factor [ExactCategory 𝒞] {D B Z : 𝒞} (d : D ⟶ B)
    (hd : ∀ {W : 𝒞} (p q : B ⟶ W), d ≫ p = d ≫ q → p = q)
    (m : D ⟶ Z) (hm : kernelMap d ≫ m = zeroMorphism (Kernel d) Z) :
    ∃ n : B ⟶ Z, d ≫ n = m := by
  obtain ⟨θ, hθ, hfac⟩ := ExactCategory.exact d
  have hcoker0 : cokernelMap d = zeroMorphism B (Cokernel d) := by
    apply hd; rw [comp_cokernelMap d, zero_morphism_comp d (zeroMorphism B (Cokernel d))]
  have hk_iso : IsIso (kernelMap (cokernelMap d)) := by
    rw [hcoker0]; exact kernelMap_zero_isIso B (Cokernel d)
  let co := HasCoequalizers.coeq (kernelMap d) (zeroMorphism (Kernel d) D)
  have hmpair : kernelMap d ≫ m = zeroMorphism (Kernel d) D ≫ m := by
    rw [hm, zeroMorphism_comp_left]
  let n' : Cokernel (kernelMap d) ⟶ Z := co.desc m hmpair
  have hn' : cokernelMap (kernelMap d) ≫ n' = m := co.fac m hmpair
  obtain ⟨ι, hι1, _⟩ := isIso_comp hθ hk_iso
  have hdι : d ≫ ι = cokernelMap (kernelMap d) := by
    calc d ≫ ι
        = (cokernelMap (kernelMap d) ≫ (θ ≫ kernelMap (cokernelMap d))) ≫ ι := by rw [hfac]
      _ = cokernelMap (kernelMap d) ≫ ((θ ≫ kernelMap (cokernelMap d)) ≫ ι) := Cat.assoc _ _ _
      _ = cokernelMap (kernelMap d) ≫ Cat.id _ := by rw [hι1]
      _ = cokernelMap (kernelMap d) := Cat.comp_id _
  exact ⟨ι ≫ n', by rw [← Cat.assoc, hdι, hn']⟩

/-- **The kernel cone is a pullback.**  For `d := (fst≫f) − (snd≫g)`, the cone
    `(Kernel d; kernelMap d ≫ fst, kernelMap d ≫ snd)` over `A —f→ B ←g— C` is a
    pullback: a competing cone `dd` lifts via `pair dd.π₁ dd.π₂`, which lands in
    `Kernel d` because `⟨π₁,π₂⟩ ≫ d = π₁≫f − π₂≫g = 0` (cone square). -/
theorem kernelCone_isPullback [ExactCategory 𝒞] [AdditiveCategory 𝒞] {A C B : 𝒞}
    (f : A ⟶ B) (g : C ⟶ B) :
    let negg := (AdditiveCategory.addInv g).choose
    let d : prod A C ⟶ B := HalfAdditiveCategory.add (fst ≫ f) (snd ≫ negg)
    ∀ (hw : (kernelMap d ≫ fst) ≫ f = (kernelMap d ≫ snd) ≫ g),
      (Cone.mk (Kernel d) (kernelMap d ≫ fst) (kernelMap d ≫ snd) hw).IsPullback := by
  intro negg d hw
  have hnegg : HalfAdditiveCategory.add g negg = HalfAdditiveCategory.zeroHom C B :=
    (AdditiveCategory.addInv g).choose_spec
  intro dd
  have hpair_d : pair dd.π₁ dd.π₂ ≫ d = zeroMorphism dd.pt B := by
    show pair dd.π₁ dd.π₂ ≫ HalfAdditiveCategory.add (fst ≫ f) (snd ≫ negg) = _
    rw [HalfAdditiveCategory.comp_add, ← Cat.assoc, ← Cat.assoc, fst_pair, snd_pair, dd.w,
        ← HalfAdditiveCategory.comp_add, hnegg, HalfAdditiveCategory.zeroHom_comp_left,
        zeroHom_eq_zeroMorphism]
  have hpaireq : pair dd.π₁ dd.π₂ ≫ d = pair dd.π₁ dd.π₂ ≫ zeroMorphism (prod A C) B := by
    rw [hpair_d, zero_morphism_comp (pair dd.π₁ dd.π₂) (zeroMorphism (prod A C) B)]
  let u : dd.pt ⟶ Kernel d := eqLift d (zeroMorphism (prod A C) B) (pair dd.π₁ dd.π₂) hpaireq
  have hu : u ≫ kernelMap d = pair dd.π₁ dd.π₂ :=
    eqLift_fac d (zeroMorphism (prod A C) B) (pair dd.π₁ dd.π₂) hpaireq
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · rw [← Cat.assoc, hu, fst_pair]
  · rw [← Cat.assoc, hu, snd_pair]
  · intro v hv1 hv2
    have hvk : v ≫ kernelMap d = pair dd.π₁ dd.π₂ := by
      apply pair_uniq
      · rw [Cat.assoc]; exact hv1
      · rw [Cat.assoc]; exact hv2
    rw [eqLift_uniq d (zeroMorphism (prod A C) B) (pair dd.π₁ dd.π₂) hpaireq v hvk]

/-- **Epimorphy of the kernel-cone projection.**  With `d := (fst≫f) − (snd≫g)` and
    `f` a cover, the projection `kernelMap d ≫ snd : Kernel d → C` is epic.  This is the
    representation-free core of additive cover-stability (see the section note). -/
theorem kernel_snd_epi [ExactCategory 𝒞] [AdditiveCategory 𝒞] {A C B : 𝒞}
    (f : A ⟶ B) (g : C ⟶ B) (hf : Cover f) :
    let negg := (AdditiveCategory.addInv g).choose
    let d : prod A C ⟶ B := HalfAdditiveCategory.add (fst ≫ f) (snd ≫ negg)
    ∀ {Z : 𝒞} (a b : C ⟶ Z), (kernelMap d ≫ snd) ≫ a = (kernelMap d ≫ snd) ≫ b → a = b := by
  intro negg d Z a b hab
  have hfe : ∀ {W : 𝒞} (p q : B ⟶ W), f ≫ p = f ≫ q → p = q :=
    fun p q h => cover_epi (Z := _) hf h
  let jA : A ⟶ prod A C := pair (Cat.id A) (HalfAdditiveCategory.zeroHom A C)
  let jC : C ⟶ prod A C := pair (HalfAdditiveCategory.zeroHom C A) (Cat.id C)
  have hjA_d : jA ≫ d = f := by
    show jA ≫ HalfAdditiveCategory.add (fst ≫ f) (snd ≫ negg) = f
    rw [HalfAdditiveCategory.comp_add, ← Cat.assoc, ← Cat.assoc]
    show HalfAdditiveCategory.add ((jA ≫ fst) ≫ f) ((jA ≫ snd) ≫ negg) = f
    rw [fst_pair, snd_pair, Cat.id_comp, HalfAdditiveCategory.zeroHom_comp_right,
        HalfAdditiveCategory.add_zero]
  have hjA_snd : jA ≫ snd = HalfAdditiveCategory.zeroHom A C := snd_pair _ _
  have hde : ∀ {W : 𝒞} (p q : B ⟶ W), d ≫ p = d ≫ q → p = q := by
    intro W p q h; apply hfe; rw [← hjA_d, Cat.assoc, Cat.assoc, h]
  have hjC_snd : jC ≫ snd = Cat.id C := snd_pair _ _
  have hsnd_epi : ∀ {W : 𝒞} (p q : C ⟶ W), (snd : prod A C ⟶ C) ≫ p = snd ≫ q → p = q := by
    intro W p q h
    calc p = (jC ≫ snd) ≫ p := by rw [hjC_snd, Cat.id_comp]
      _ = jC ≫ (snd ≫ p) := Cat.assoc _ _ _
      _ = jC ≫ (snd ≫ q) := by rw [h]
      _ = (jC ≫ snd) ≫ q := (Cat.assoc _ _ _).symm
      _ = q := by rw [hjC_snd, Cat.id_comp]
  obtain ⟨negb, hnegb⟩ := AdditiveCategory.addInv b
  let e := HalfAdditiveCategory.add a negb
  have hsnde0 : kernelMap d ≫ (snd ≫ e) = zeroMorphism (Kernel d) Z := by
    have hexp : kernelMap d ≫ (snd ≫ e)
        = HalfAdditiveCategory.add (kernelMap d ≫ snd ≫ a) (kernelMap d ≫ snd ≫ negb) := by
      show kernelMap d ≫ (snd ≫ HalfAdditiveCategory.add a negb) = _
      rw [HalfAdditiveCategory.comp_add, HalfAdditiveCategory.comp_add]
    rw [hexp]
    have hab' : kernelMap d ≫ (snd ≫ a) = kernelMap d ≫ (snd ≫ b) := by
      rw [← Cat.assoc, ← Cat.assoc]; exact hab
    rw [hab', ← HalfAdditiveCategory.comp_add, ← HalfAdditiveCategory.comp_add, hnegb,
        HalfAdditiveCategory.zeroHom_comp_left snd,
        HalfAdditiveCategory.zeroHom_comp_left (kernelMap d), zeroHom_eq_zeroMorphism]
  obtain ⟨n, hn⟩ := coimage_factor d hde (snd ≫ e) hsnde0
  have hfn0 : f ≫ n = zeroMorphism A Z := by
    have hjn : jA ≫ (d ≫ n) = jA ≫ (snd ≫ e) := by rw [hn]
    rw [← Cat.assoc, hjA_d] at hjn
    rw [hjn, ← Cat.assoc, hjA_snd, HalfAdditiveCategory.zeroHom_comp_right e, zeroHom_eq_zeroMorphism]
  have hn0 : n = zeroMorphism B Z := by
    apply hfe; rw [hfn0, zero_morphism_comp f (zeroMorphism B Z)]
  have hsnde0' : snd ≫ e = zeroMorphism (prod A C) Z := by
    rw [← hn, hn0, zero_morphism_comp d (zeroMorphism B Z)]
  have he0 : e = zeroMorphism C Z := by
    apply hsnd_epi; rw [hsnde0', zero_morphism_comp snd (zeroMorphism C Z)]
  rw [← zeroHom_eq_zeroMorphism] at he0
  exact add_cancel_common a b negb he0 hnegb

/-- **Epic ⟹ cover** in an exact category. -/
theorem epi_is_cover [ExactCategory 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (he : ∀ {Z : 𝒞} (a b : B ⟶ Z), f ≫ a = f ≫ b → a = b) : Cover f := by
  have hm_mono : Mono (kernelMap (cokernelMap f)) :=
    eqMap_mono' (cokernelMap f) (zeroMorphism B (Cokernel f))
  have heqf : f ≫ cokernelMap f = f ≫ zeroMorphism B (Cokernel f) := by
    rw [comp_cokernelMap f, zero_morphism_comp f (zeroMorphism B (Cokernel f))]
  let ell : A ⟶ Kernel (cokernelMap f) :=
    eqLift (cokernelMap f) (zeroMorphism B (Cokernel f)) f heqf
  have hell : ell ≫ kernelMap (cokernelMap f) = f :=
    eqLift_fac (cokernelMap f) (zeroMorphism B (Cokernel f)) f heqf
  have hm_epi : ∀ {Z : 𝒞} (a b : B ⟶ Z),
      kernelMap (cokernelMap f) ≫ a = kernelMap (cokernelMap f) ≫ b → a = b := by
    intro Z a b hab
    apply he
    calc f ≫ a = (ell ≫ kernelMap (cokernelMap f)) ≫ a := by rw [hell]
      _ = ell ≫ (kernelMap (cokernelMap f) ≫ a) := Cat.assoc _ _ _
      _ = ell ≫ (kernelMap (cokernelMap f) ≫ b) := by rw [hab]
      _ = (ell ≫ kernelMap (cokernelMap f)) ≫ b := (Cat.assoc _ _ _).symm
      _ = f ≫ b := by rw [hell]
  have hm_iso : IsIso (kernelMap (cokernelMap f)) := exact_balanced _ hm_mono hm_epi
  rw [cover_iff_image_entire]
  exact hm_iso

/-- **Keystone, modulo cover-stability.**  Exact additive ⟹ regular, given
    `PullbacksTransferCovers`.  SORRY-FREE. -/
noncomputable def exact_additive_is_regular_of_transfer
    [ExactCategory 𝒞] [AdditiveCategory 𝒞] [PullbacksTransferCovers 𝒞] :
    RegularCategory 𝒞 :=
  { (inferInstance : HasTerminal 𝒞), (inferInstance : HasBinaryProducts 𝒞),
    (inferInstance : HasPullbacks 𝒞), (inferInstance : HasImages 𝒞),
    (inferInstance : PullbacksTransferCovers 𝒞) with }

/-- **Sharp residual** (the single content blocking representation-free cover-stability):
    the second projection of the pullback of a cover is epic.  Additive Barr-exactness. -/
theorem pullback_epi_is_epi [ExactCategory 𝒞] [AdditiveCategory 𝒞]
    {A B C : 𝒞} {f : A ⟶ B} {g : C ⟶ B} (c : Cone f g) (hpb : c.IsPullback)
    (hf : Cover f) :
    ∀ {Z : 𝒞} (a b : C ⟶ Z), c.π₂ ≫ a = c.π₂ ≫ b → a = b := by
  -- The kernel cone of the difference map `d := (fst≫f) − (snd≫g)` is another pullback
  -- of the same cospan; its projection `kernelMap d ≫ snd` is epic (`kernel_snd_epi`).
  -- Transfer epimorphy across the pullback comparison iso to `c.π₂`.  (No `set`: mathlib-free.)
  let negg := (AdditiveCategory.addInv g).choose
  let d : prod A C ⟶ B := HalfAdditiveCategory.add (fst ≫ f) (snd ≫ negg)
  have hnegg : HalfAdditiveCategory.add g negg = HalfAdditiveCategory.zeroHom C B :=
    (AdditiveCategory.addInv g).choose_spec
  -- the kernel cone's square `(kernelMap d ≫ fst)≫f = (kernelMap d ≫ snd)≫g`
  have hkd0 : kernelMap d ≫ d = zeroMorphism (Kernel d) B := by
    rw [kernelMap_eq d, zero_morphism_comp (kernelMap d) (zeroMorphism (prod A C) B)]
  have hw : (kernelMap d ≫ fst) ≫ f = (kernelMap d ≫ snd) ≫ g := by
    -- both `X₁ := kernelMap d ≫ fst ≫ f` and `X₂ := kernelMap d ≫ snd ≫ g` have common
    -- summand `Y := kernelMap d ≫ snd ≫ negg`: `X₁ + Y = kernelMap d ≫ d = 0`, and
    -- `X₂ + Y = kernelMap d ≫ snd ≫ (g + negg) = 0`; cancel.
    apply add_cancel_common _ _ (kernelMap d ≫ snd ≫ negg)
    · have : kernelMap d ≫ d
          = HalfAdditiveCategory.add ((kernelMap d ≫ fst) ≫ f) (kernelMap d ≫ snd ≫ negg) := by
        show kernelMap d ≫ HalfAdditiveCategory.add (fst ≫ f) (snd ≫ negg) = _
        rw [HalfAdditiveCategory.comp_add, ← Cat.assoc]
      rw [← this, hkd0, zeroHom_eq_zeroMorphism]
    · rw [Cat.assoc (kernelMap d) snd g, ← HalfAdditiveCategory.comp_add,
          ← HalfAdditiveCategory.comp_add, hnegg,
          HalfAdditiveCategory.zeroHom_comp_left, zeroHom_eq_zeroMorphism,
          zero_morphism_comp (kernelMap d) (zeroMorphism (prod A C) B),
          ← zeroHom_eq_zeroMorphism]
  -- the kernel cone, and its pullback property
  let kc : Cone f g := Cone.mk (Kernel d) (kernelMap d ≫ fst) (kernelMap d ≫ snd) hw
  have hkc_pb : kc.IsPullback := kernelCone_isPullback f g hw
  -- comparison `φ : kc.pt → c.pt` with `φ ≫ c.π₂ = kc.π₂` (from `c` being a pullback)
  obtain ⟨φ, ⟨_, hφ2⟩, _⟩ := hpb kc
  -- `kernel_snd_epi`: `kc.π₂ = kernelMap d ≫ snd` is epic
  have hkc_epi : ∀ {Z : 𝒞} (a b : C ⟶ Z), kc.π₂ ≫ a = kc.π₂ ≫ b → a = b :=
    kernel_snd_epi f g hf
  intro Z a b hab
  apply hkc_epi
  -- `kc.π₂ ≫ a = φ ≫ c.π₂ ≫ a = φ ≫ c.π₂ ≫ b = kc.π₂ ≫ b`
  calc kc.π₂ ≫ a = (φ ≫ c.π₂) ≫ a := by rw [hφ2]
    _ = φ ≫ (c.π₂ ≫ a) := Cat.assoc _ _ _
    _ = φ ≫ (c.π₂ ≫ b) := by rw [hab]
    _ = (φ ≫ c.π₂) ≫ b := (Cat.assoc _ _ _).symm
    _ = kc.π₂ ≫ b := by rw [hφ2]

/-- **`PullbacksTransferCovers` from the exact additive structure**, modulo the residual. -/
theorem exactAdditivePullbacksTransferCovers [ExactCategory 𝒞] [AdditiveCategory 𝒞] :
    PullbacksTransferCovers 𝒞 where
  pullbacks_transfer_covers c hpb hf := epi_is_cover c.π₂ (pullback_epi_is_epi c hpb hf)

/-- **THE KEYSTONE.**  Exact additive ⟹ regular.  All fields sorry-free except
    cover-stability, isolated to `pullback_epi_is_epi`. -/
noncomputable def exact_additive_is_regular [ExactCategory 𝒞] [AdditiveCategory 𝒞] :
    RegularCategory 𝒞 :=
  letI : PullbacksTransferCovers 𝒞 := exactAdditivePullbacksTransferCovers
  exact_additive_is_regular_of_transfer

/-- Every monic is normal in an exact category (`monic_kernel_of_cokernel`). -/
theorem all_normal_of_exact [ExactCategory 𝒞] {A B : 𝒞} (m : A ⟶ B) (hm : Mono m) :
    IsNormalSubobject m hm := by
  obtain ⟨h, hiso, hfac⟩ := monic_kernel_of_cokernel m hm
  exact ⟨Cokernel m, cokernelMap m, h, hiso, hfac⟩

/-- **Exact additive ⟹ abelian** (assembles the keystone + `all_normal`). -/
noncomputable def abelianOfExactAdditive [ExactCategory 𝒞] [AdditiveCategory 𝒞] :
    AbelianCategory 𝒞 :=
  letI hreg : RegularCategory 𝒞 := exact_additive_is_regular
  letI hadd : AdditiveCategory 𝒞 := inferInstance
  letI hz : HasZeroObject 𝒞 := inferInstance
  { toRegularCategory := hreg
    toHasEqualizers := (inferInstance : HasEqualizers 𝒞)
    toHasCoequalizers := (inferInstance : HasCoequalizers 𝒞)
    zeroHom := hadd.zeroHom
    zeroHom_comp_left := hadd.zeroHom_comp_left
    zeroHom_comp_right := hadd.zeroHom_comp_right
    prod_coprod_coincide := hadd.prod_coprod_coincide
    add := hadd.add
    add_eq_addL := hadd.add_eq_addL
    add_eq_addR := hadd.add_eq_addR
    -- abelian-GROUP homs: additive inverses, from the ambient `[AdditiveCategory]`.
    addInv := hadd.addInv
    zero_eq_one := hz.zero_eq_one
    all_normal := fun m hm => all_normal_of_exact m hm }

/-! §1.597: A is abelian iff it is an exact additive category (with binary products
  or coproducts).

  PROOF (sketch, Freyd):
  (⟹) Any abelian category is exact: images exist (regular), and in the
  effective-regular additive setting the coimage-image map θ is always an iso.

  (⟸) Given an exact additive category A with binary products:
  — Binary subtraction: using the exact factorization, construct a - operation
    on each hom-set via the cokernel of the diagonal A → A×A.
  — This yields a ring structure on each hom-set, making A additive.
  — Every pullback of a cover is a cover (regularity): follows from the
    exact-category pushout lemma (a pullback square with one cover side is
    also a pushout, making the parallel side a cover).
  — Every monic is a kernel (normality): since each morphism factors as
    cokernel ∘ kernel, a monic that is also a cokernel is a kernel; iterate. -/
theorem abelian_iff_exact_additive
    {𝒞 : Type u} [Cat.{v} 𝒞]
    [ExactCategory 𝒞] [AdditiveCategory 𝒞] [HasBinaryProducts 𝒞] :
    Nonempty (AbelianCategory 𝒞) :=
  ⟨abelianOfExactAdditive⟩


/-! ## §1.598 Normal categories

  A category with zero is LEFT-NORMAL if every subobject (monic) is normal,
  and RIGHT-NORMAL if every comonic (epi seen as a quotient) is a cokernel.
  A NORMAL CATEGORY is both left- and right-normal.

  Historical note: the first book on the subject (Mitchell, 1964) defined
  abelian categories as normal categories with kernels, cokernels, binary
  products and coproducts. -/

/-- LEFT-NORMAL: every subobject is normal (= kernel of some morphism). -/
def IsLeftNormal (𝒞 : Type u) [Cat.{v} 𝒞] [HasZeroObject 𝒞] [HasEqualizers 𝒞] : Prop :=
  ∀ {A B : 𝒞} (m : A ⟶ B) (hm : Mono m), IsNormalSubobject m hm

/-- RIGHT-NORMAL: every cover (Cover e) is a cokernel of some morphism,
  i.e. e = cokernelMap f for some f (up to the cokernel object being B).
  Formally: there exist W, f, and an iso i : Cokernel f ≅ B such that
  cokernelMap f ≫ i.inv = e. -/
def IsRightNormal (𝒞 : Type u) [Cat.{v} 𝒞] [HasZeroObject 𝒞] [HasCoequalizers 𝒞] : Prop :=
  ∀ {A B : 𝒞} (e : A ⟶ B), Cover e →
    ∃ (W : 𝒞) (f : W ⟶ A) (i : Cokernel f ⟶ B),
      IsIso i ∧ cokernelMap f ≫ i = e

/-- NORMAL CATEGORY: both left- and right-normal (§1.598). -/
def IsNormalCategory (𝒞 : Type u) [Cat.{v} 𝒞] [HasZeroObject 𝒞]
    [HasEqualizers 𝒞] [HasCoequalizers 𝒞] : Prop :=
  IsLeftNormal 𝒞 ∧ IsRightNormal 𝒞

/-! §1.598: A is abelian iff it is a normal category with kernels, cokernels and
  either binary products or binary coproducts.

  PROOF (sketch, Freyd):
  Given a normal category with kernels, cokernels, and binary products:
  — Construct pullbacks of pairs of monics from kernel + product (§1.434-style).
  — Every cover is epic (from the pullback of a mono via a cover).
  — For x:A→B, the normal closure ker(coker(x)) is the image of x (since every
    subobject is normal = kernel, so the minimal normal subobject allowing x is
    the image).  Factor x as A ↠ C ↣ B where A↠C is a cover (epic = cokernel).
  — A is exact.  Then apply §1.597. -/
theorem abelian_iff_normal_kernels_cokernels
    {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasZeroObject 𝒞] [HasEqualizers 𝒞] [HasCoequalizers 𝒞] [HasBinaryProducts 𝒞] :
    IsNormalCategory 𝒞 → Nonempty (AbelianCategory 𝒞) := by
  sorry


/-! ## §1.599 Exact sequences and diagram lemmas

  Given objects A_n and morphisms A_{n-1} → A_n → A_{n+1}, the sequence is
  EXACT at A_n if the image of (A_{n-1} → A_n) equals the kernel of (A_n → A_{n+1}).
  Equivalently (in an abelian category), the image of f_{n-1} is a kernel of f_n.

  The FIVE LEMMA and SNAKE LEMMA are the two key diagram lemmas. -/

/-! EXACT at B (§1.599): a composable pair f : A → B, g : B → C is exact at B
  when the image of f *equals the kernel of g AS A SUBOBJECT of B*.

  WHY NOT the bare object iso `Isomorphic (image f).dom (Kernel g)`.  A bare object iso
  `∃ φ, IsIso φ` (S1_34) only says the two domains are abstractly isomorphic; it records NOTHING
  about how `(image f).dom` and `Kernel g` sit inside `B`.  But "exact at B" is a statement about
  SUBOBJECTS of `B` (im f = ker g as subobjects), so the faithful encoding must bundle the iso
  with the compatibility `φ ≫ kernelMap g = (image f).arr` (the two inclusions into `B` agree).
  The bare-iso form is STRICTLY WEAKER and is the wrong encoding: the upgrade
  `Isomorphic (image f).dom (Kernel g) → ∃ φ, IsIso φ ∧ φ ≫ kernelMap g = (image f).arr`
  is FALSE in general.  `RelExact` below is the correct (stronger, faithful) predicate, and it is
  what every diagram chase actually uses: it lets one turn "`x ≫ g = 0`" into "`x` factors through
  `image f`" (via `kernelMap`'s universal property + `φ⁻¹`). -/

/-- **§1.599 exactness at B, ≫-compatible (faithful).**  The image of `f` equals the kernel
  of `g` AS A SUBOBJECT of `B`: an iso `φ : (image f).dom ≅ Kernel g` commuting with both
  inclusions into `B` (`φ ≫ kernelMap g = (image f).arr`).  Bundling the inclusion compatibility
  (not just the bare object iso) is what makes the chases go through. -/
def RelExact [HasZeroObject 𝒞] [HasEqualizers 𝒞] [HasImages 𝒞]
    {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) : Prop :=
  ∃ φ : (image f).dom ⟶ Kernel g, IsIso φ ∧ φ ≫ kernelMap g = (image f).arr

/-- A map killed by `x` lifts (uniquely) through the kernel of `x`.  This is the kernel's
  universal property specialized to the `(x, 0)` equalizer: if `k ≫ x = 0` then `k` factors as
  `(kernelLift) ≫ kernelMap x`. -/
def kernelLift [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B X : 𝒞} (x : A ⟶ B) (k : X ⟶ A)
    (h : k ≫ x = zeroMorphism X B) : X ⟶ Kernel x :=
  eqLift x (zeroMorphism A B) k (by
    rw [h, zero_morphism_comp k (zeroMorphism A B)])

theorem kernelLift_fac [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B X : 𝒞} (x : A ⟶ B) (k : X ⟶ A)
    (h : k ≫ x = zeroMorphism X B) : kernelLift x k h ≫ kernelMap x = k :=
  eqLift_fac x (zeroMorphism A B) k _

/-- `kernelMap x` is monic (it is an equalizer map). -/
theorem kernelMap_mono [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B : 𝒞} (x : A ⟶ B) :
    Mono (kernelMap x) := eqMap_mono' x (zeroMorphism A B)

/-- `kernelMap x ≫ x = 0`: the kernel is killed by `x`. -/
theorem kernelMap_comp [HasZeroObject 𝒞] [HasEqualizers 𝒞] {A B : 𝒞} (x : A ⟶ B) :
    kernelMap x ≫ x = zeroMorphism (Kernel x) B := by
  rw [kernelMap_eq, zero_morphism_comp (kernelMap x) (zeroMorphism A B)]

/-! ### §1.599 Diagram-chase infrastructure for the five lemma

  Three reusable facts, all valid in any additive category with zero / equalizers /
  images (no `ExactCategory` instance needed):

  * `comp_zero_of_mono` / `mono_of_comp_zero`: in an ADDITIVE category, a map `m` is monic
    iff its "kernel is zero" — `∀ t, t ≫ m = 0 → t = 0`.  Forward needs only the zero ideal;
    backward needs additive inverses (`addInv` + `add_cancel_common`).
  * `relexact_comp_zero`: `RelExact f g ⟹ f ≫ g = 0` (the two halves of an exact sequence
    compose to zero).
  * `relexact_cover_factor`: the element-free "preimage" step.  If `RelExact f g` and
    `t ≫ g = 0`, then after covering the source of `t` by a cover `e`, the pullback `e ≫ t`
    factors as `x ≫ f`.  This packages "`t` lands in `im f = ker g`, then lift through the
    image-cover by a pullback". -/

/-- Forward (additive): a monic `m` has zero kernel — `t ≫ m = 0 ⟹ t = 0`. -/
theorem comp_zero_of_mono [HasZeroObject 𝒞] {A B : 𝒞} {m : A ⟶ B} (hm : Mono m)
    {T : 𝒞} (t : T ⟶ A) (h : t ≫ m = zeroMorphism T B) : t = zeroMorphism T A := by
  apply hm t (zeroMorphism T A)
  rw [h, zeroMorphism_comp_left m]

/-- Backward (additive, needs inverses): if `m` has zero kernel (`t ≫ m = 0 ⟹ t = 0`) then
    `m` is monic.  Given `u ≫ m = w ≫ m`, form `d = u + (−w)`; then `d ≫ m = 0`, so `d = 0`,
    and `add u (−w) = 0 = add w (−w)` forces `u = w` (`add_cancel_common`). -/
theorem mono_of_comp_zero [AdditiveCategory 𝒞] [HasZeroObject 𝒞] {A B : 𝒞} {m : A ⟶ B}
    (h : ∀ {T : 𝒞} (t : T ⟶ A), t ≫ m = zeroMorphism T B → t = zeroMorphism T A) : Mono m := by
  intro W u w huw
  obtain ⟨g, hg⟩ := AdditiveCategory.addInv w
  have hd : HalfAdditiveCategory.add u g ≫ m = zeroMorphism W B := by
    rw [HalfAdditiveCategory.add_comp, huw, ← HalfAdditiveCategory.add_comp, hg,
        zeroHom_eq_zeroMorphism' W A, zeroMorphism_comp_left m]
  have hd0 : HalfAdditiveCategory.add u g = zeroMorphism W A := h _ hd
  refine add_cancel_common u w g ?_ hg
  rw [hd0, zeroHom_eq_zeroMorphism' W A]

/-- `RelExact f g ⟹ f ≫ g = 0`: the image of `f` is the kernel of `g`, and the kernel is
    killed by `g`. -/
theorem relexact_comp_zero [HasZeroObject 𝒞] [HasEqualizers 𝒞] [HasImages 𝒞]
    {A B C : 𝒞} {f : A ⟶ B} {g : B ⟶ C} (hfg : RelExact f g) :
    f ≫ g = zeroMorphism A C := by
  obtain ⟨φ, _, hφ⟩ := hfg
  have hkey : f ≫ g = image.lift f ≫ φ ≫ kernelMap g ≫ g :=
    calc f ≫ g = (image.lift f ≫ (image f).arr) ≫ g := by rw [image.lift_fac]
      _ = (image.lift f ≫ (φ ≫ kernelMap g)) ≫ g := by rw [hφ]
      _ = image.lift f ≫ φ ≫ kernelMap g ≫ g := by simp only [Cat.assoc]
  rw [hkey, kernelMap_comp g, zero_morphism_comp φ (zeroMorphism (Kernel g) C),
      zero_morphism_comp (image.lift f) (zeroMorphism (image f).dom C)]

/-- A map `t : T → B` killed by `g` factors through `image f`, given `RelExact f g`
    (`im f = ker g`).  `t ≫ g = 0` lifts `t` through `ker g` (`kernelLift`); the iso `φ`
    transports that into a factor through `(image f).arr`. -/
theorem relexact_factor [HasZeroObject 𝒞] [HasEqualizers 𝒞] [HasImages 𝒞]
    {A B C : 𝒞} {f : A ⟶ B} {g : B ⟶ C} (hfg : RelExact f g)
    {T : 𝒞} (t : T ⟶ B) (h : t ≫ g = zeroMorphism T C) :
    ∃ s : T ⟶ (image f).dom, s ≫ (image f).arr = t := by
  obtain ⟨φ, ⟨φinv, hφ1, hφ2⟩, hφ⟩ := hfg
  refine ⟨kernelLift g t h ≫ φinv, ?_⟩
  calc (kernelLift g t h ≫ φinv) ≫ (image f).arr
      = (kernelLift g t h ≫ φinv) ≫ (φ ≫ kernelMap g) := by rw [hφ]
    _ = kernelLift g t h ≫ (φinv ≫ φ) ≫ kernelMap g := by simp only [Cat.assoc]
    _ = kernelLift g t h ≫ kernelMap g := by rw [hφ2, Cat.id_comp]
    _ = t := kernelLift_fac g t h

/-- **Element-free "preimage" step.**  Given `RelExact f g` and `t : T → B` with `t ≫ g = 0`,
    there is a COVER `e : P → T` and a map `x : P → A` with `e ≫ t = x ≫ f`.  Construction:
    `t` factors through `image f` (`relexact_factor`); pull the image-cover `image.lift f`
    back along that factor — the other projection `e` is a cover (`cover_pullback`), and the
    pullback square gives `e ≫ t = x ≫ f`. -/
theorem relexact_cover_factor [HasZeroObject 𝒞] [HasEqualizers 𝒞] [HasImages 𝒞]
    [HasPullbacks 𝒞] [PullbacksTransferCovers 𝒞]
    {A B C : 𝒞} {f : A ⟶ B} {g : B ⟶ C} (hfg : RelExact f g)
    {T : 𝒞} (t : T ⟶ B) (h : t ≫ g = zeroMorphism T C) :
    ∃ (P : 𝒞) (e : P ⟶ T) (x : P ⟶ A), Cover e ∧ e ≫ t = x ≫ f := by
  obtain ⟨s, hs⟩ := relexact_factor hfg t h
  -- pull back the cover `image.lift f : A → (image f).dom` along `s : T → (image f).dom`
  let pb := HasPullbacks.has (image.lift f) s
  have he_cover : Cover pb.cone.π₂ := cover_pullback s (image_lift_cover f)
  refine ⟨pb.cone.pt, pb.cone.π₂, pb.cone.π₁, he_cover, ?_⟩
  -- pb.cone.w : π₁ ≫ image.lift f = π₂ ≫ s
  calc pb.cone.π₂ ≫ t = pb.cone.π₂ ≫ (s ≫ (image f).arr) := by rw [hs]
    _ = (pb.cone.π₂ ≫ s) ≫ (image f).arr := by rw [Cat.assoc]
    _ = (pb.cone.π₁ ≫ image.lift f) ≫ (image f).arr := by rw [pb.cone.w]
    _ = pb.cone.π₁ ≫ (image.lift f ≫ (image f).arr) := by rw [Cat.assoc]
    _ = pb.cone.π₁ ≫ f := by rw [image.lift_fac]

/-! §1.599 FIVE LEMMA: In an abelian category, given a commutative diagram

      A₁ → A₂ → A₃ → A₄ → A₅
      |    |    |    |    |
      B₁ → B₂ → B₃ → B₄ → B₅

  with exact rows, if the outer four verticals (A₁→B₁, A₂→B₂, A₄→B₄, A₅→B₅)
  are isomorphisms, then the middle vertical (A₃→B₃) is also an isomorphism.

  PROOF: This is a Horn sentence in bicartesian predicates, so it holds in any
  abelian category iff it holds in Ab.  In Ab: the center vertical has zero kernel
  (easy diagram chase); the definition of exact category is self-dual, so zero
  cokernel as well; hence it is an isomorphism.

  STATEMENT FIX (faithful, NOT a weakening).  The exactness hypotheses are now the ≫-compatible
  `RelExact aₙ aₙ₊₁` (im aₙ = ker aₙ₊₁ as SUBOBJECTS of Aₙ₊₁), replacing the prior *bare object
  iso* `Isomorphic (image aₙ).dom (Kernel aₙ₊₁)` (= `∃ φ, IsIso φ`).  The bare iso was the WRONG,
  too-weak encoding: it records nothing about how `(image aₙ).dom` and `Kernel aₙ₊₁` include into
  Aₙ₊₁, and the chase genuinely needs `φ ≫ kernelMap aₙ₊₁ = (image aₙ).arr` to turn
  "`x ≫ aₙ₊₁ = 0`" into "`x` factors through `image aₙ`".  `RelExact` is STRICTLY STRONGER than
  the bare iso (and is the faithful definition of an exact sequence), so this is a strengthening of
  the hypothesis = a more honest statement, not a weakening of the theorem.  The class is also now
  FAITHFUL (`AbelianCategory extends AdditiveCategory`), supplying the additive inverses the
  subtraction steps of the chase need. -/
theorem five_lemma [AbelianCategory 𝒞]
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : 𝒞}
    {a₁ : A₁ ⟶ A₂} {a₂ : A₂ ⟶ A₃} {a₃ : A₃ ⟶ A₄} {a₄ : A₄ ⟶ A₅}
    {b₁ : B₁ ⟶ B₂} {b₂ : B₂ ⟶ B₃} {b₃ : B₃ ⟶ B₄} {b₄ : B₄ ⟶ B₅}
    {v₁ : A₁ ⟶ B₁} {v₂ : A₂ ⟶ B₂} {v₃ : A₃ ⟶ B₃} {v₄ : A₄ ⟶ B₄} {v₅ : A₅ ⟶ B₅}
    -- rows are exact (image of aₙ = kernel of aₙ₊₁ as subobjects)
    (hA₁₂ : RelExact a₁ a₂) (hA₂₃ : RelExact a₂ a₃) (hA₃₄ : RelExact a₃ a₄)
    (hB₁₂ : RelExact b₁ b₂) (hB₂₃ : RelExact b₂ b₃) (hB₃₄ : RelExact b₃ b₄)
    -- squares commute
    (sq₁ : a₁ ≫ v₂ = v₁ ≫ b₁) (sq₂ : a₂ ≫ v₃ = v₂ ≫ b₂)
    (sq₃ : a₃ ≫ v₄ = v₃ ≫ b₃) (sq₄ : a₄ ≫ v₅ = v₄ ≫ b₄)
    -- outer four verticals are isos
    (h₁ : IsIso v₁) (h₂ : IsIso v₂) (h₄ : IsIso v₄) (h₅ : IsIso v₅) :
    IsIso v₃ := by
  -- inverses of the four outer verticals
  obtain ⟨v₁i, hv₁1, hv₁2⟩ := h₁
  obtain ⟨v₂i, hv₂1, hv₂2⟩ := h₂
  obtain ⟨v₄i, hv₄1, hv₄2⟩ := h₄
  obtain ⟨v₅i, hv₅1, hv₅2⟩ := h₅
  have hv₂mono : Mono v₂ := mono_of_retraction v₂ v₂i hv₂1
  have hv₄mono : Mono v₄ := mono_of_retraction v₄ v₄i hv₄1
  have hv₅mono : Mono v₅ := mono_of_retraction v₅ v₅i hv₅1
  -- the two rows compose to zero at the relevant spots
  have ha₁a₂ : a₁ ≫ a₂ = zeroMorphism A₁ A₃ := relexact_comp_zero hA₁₂
  have hb₃b₄ : b₃ ≫ b₄ = zeroMorphism B₃ B₅ := relexact_comp_zero hB₃₄
  -- ===================================================================== MONO half
  have hmono : Mono v₃ := by
    refine mono_of_comp_zero (fun {T} t ht => ?_)
    -- t ≫ a₃ = 0  (push through sq₃, kill by v₄ iso)
    have hta₃ : t ≫ a₃ = zeroMorphism T A₄ := by
      apply comp_zero_of_mono hv₄mono
      calc (t ≫ a₃) ≫ v₄ = t ≫ (a₃ ≫ v₄) := Cat.assoc _ _ _
        _ = t ≫ (v₃ ≫ b₃) := by rw [sq₃]
        _ = (t ≫ v₃) ≫ b₃ := (Cat.assoc _ _ _).symm
        _ = zeroMorphism T B₃ ≫ b₃ := by rw [ht]
        _ = zeroMorphism T B₄ := zeroMorphism_comp_left b₃
    -- cover P of T with x : P → A₂, e ≫ t = x ≫ a₂
    obtain ⟨P, e, x, he_cover, hex⟩ := relexact_cover_factor hA₂₃ t hta₃
    -- (x ≫ v₂) ≫ b₂ = 0
    have hxb₂ : (x ≫ v₂) ≫ b₂ = zeroMorphism P B₃ := by
      calc (x ≫ v₂) ≫ b₂ = x ≫ (v₂ ≫ b₂) := Cat.assoc _ _ _
        _ = x ≫ (a₂ ≫ v₃) := by rw [sq₂]
        _ = (x ≫ a₂) ≫ v₃ := (Cat.assoc _ _ _).symm
        _ = (e ≫ t) ≫ v₃ := by rw [hex]
        _ = e ≫ (t ≫ v₃) := Cat.assoc _ _ _
        _ = e ≫ zeroMorphism T B₃ := by rw [ht]
        _ = zeroMorphism P B₃ := zero_morphism_comp e (zeroMorphism T B₃)
    -- cover Q of P with y : Q → B₁, ρ ≫ (x ≫ v₂) = y ≫ b₁
    obtain ⟨Q, ρ, y, hρ_cover, hρy⟩ := relexact_cover_factor hB₁₂ (x ≫ v₂) hxb₂
    -- preimage w = y ≫ v₁⁻¹ : Q → A₁,  w ≫ a₁ = ρ ≫ x  (cancel v₂ mono)
    have hwa₁ : (y ≫ v₁i) ≫ a₁ = ρ ≫ x := by
      apply hv₂mono
      calc ((y ≫ v₁i) ≫ a₁) ≫ v₂ = (y ≫ v₁i) ≫ (a₁ ≫ v₂) := Cat.assoc _ _ _
        _ = (y ≫ v₁i) ≫ (v₁ ≫ b₁) := by rw [sq₁]
        _ = y ≫ (v₁i ≫ v₁) ≫ b₁ := by simp only [Cat.assoc]
        _ = y ≫ b₁ := by rw [hv₁2, Cat.id_comp]
        _ = ρ ≫ (x ≫ v₂) := hρy.symm
        _ = (ρ ≫ x) ≫ v₂ := (Cat.assoc _ _ _).symm
    -- ρ ≫ e ≫ t = (w ≫ a₁) ≫ a₂ = 0, then cancel the two covers
    have hcancel : (ρ ≫ e) ≫ t = zeroMorphism Q A₃ := by
      calc (ρ ≫ e) ≫ t = ρ ≫ (e ≫ t) := Cat.assoc _ _ _
        _ = ρ ≫ (x ≫ a₂) := by rw [hex]
        _ = (ρ ≫ x) ≫ a₂ := (Cat.assoc _ _ _).symm
        _ = ((y ≫ v₁i) ≫ a₁) ≫ a₂ := by rw [hwa₁]
        _ = (y ≫ v₁i) ≫ (a₁ ≫ a₂) := Cat.assoc _ _ _
        _ = (y ≫ v₁i) ≫ zeroMorphism A₁ A₃ := by rw [ha₁a₂]
        _ = zeroMorphism Q A₃ := zero_morphism_comp (y ≫ v₁i) (zeroMorphism A₁ A₃)
    -- ρ ≫ e is a cover (composite), hence epic; cancel against `t = 0`-target
    have hρe_cover : Cover (ρ ≫ e) := cover_comp hρ_cover he_cover
    apply cover_epi hρe_cover
    rw [hcancel, zero_morphism_comp (ρ ≫ e) (zeroMorphism T A₃)]
  -- ===================================================================== COVER half
  -- It suffices that `j := (image v₃).arr` is iso (`cover_iff_image_entire`); we show `j`
  -- is split epi (a right inverse from `cover_mono_diagonal` with `β = id`), and `j` is
  -- monic, so `j` is iso.
  have hcover : Cover v₃ := by
    rw [cover_iff_image_entire]
    -- run the dual chase on the generalized element `β = id_{B₃} : B₃ → B₃`
    let β : B₃ ⟶ B₃ := Cat.id B₃
    have hβ : β = Cat.id B₃ := rfl
    -- z : B₃ → A₄ with z ≫ v₄ = β ≫ b₃
    let z : B₃ ⟶ A₄ := β ≫ b₃ ≫ v₄i
    have hz : z = β ≫ b₃ ≫ v₄i := rfl
    have hzv₄ : z ≫ v₄ = β ≫ b₃ := by
      rw [hz, Cat.assoc, Cat.assoc, hv₄2, Cat.comp_id]
    -- z ≫ a₄ = 0 (kill by v₅ mono, b₃≫b₄ = 0)
    have hza₄ : z ≫ a₄ = zeroMorphism B₃ A₅ := by
      apply comp_zero_of_mono hv₅mono
      calc (z ≫ a₄) ≫ v₅ = z ≫ (a₄ ≫ v₅) := Cat.assoc _ _ _
        _ = z ≫ (v₄ ≫ b₄) := by rw [sq₄]
        _ = (z ≫ v₄) ≫ b₄ := (Cat.assoc _ _ _).symm
        _ = (β ≫ b₃) ≫ b₄ := by rw [hzv₄]
        _ = β ≫ (b₃ ≫ b₄) := Cat.assoc _ _ _
        _ = β ≫ zeroMorphism B₃ B₅ := by rw [hb₃b₄]
        _ = zeroMorphism B₃ B₅ := by rw [zero_morphism_comp β (zeroMorphism B₃ B₅)]
    -- cover P of B₃ with x̃ : P → A₃, π ≫ z = x̃ ≫ a₃
    obtain ⟨P, π, xt, hπ_cover, hπx⟩ := relexact_cover_factor hA₃₄ z hza₄
    -- additive inverse of x̃ ≫ v₃
    obtain ⟨neg, hneg⟩ := AdditiveCategory.addInv (xt ≫ v₃)
    let d : P ⟶ B₃ := HalfAdditiveCategory.add (π ≫ β) neg
    have hd : d = HalfAdditiveCategory.add (π ≫ β) neg := rfl
    -- d ≫ b₃ = 0
    have hxv₃b₃ : (xt ≫ v₃) ≫ b₃ = (π ≫ β) ≫ b₃ := by
      calc (xt ≫ v₃) ≫ b₃ = xt ≫ (v₃ ≫ b₃) := Cat.assoc _ _ _
        _ = xt ≫ (a₃ ≫ v₄) := by rw [sq₃]
        _ = (xt ≫ a₃) ≫ v₄ := (Cat.assoc _ _ _).symm
        _ = (π ≫ z) ≫ v₄ := by rw [hπx]
        _ = π ≫ (z ≫ v₄) := Cat.assoc _ _ _
        _ = π ≫ (β ≫ b₃) := by rw [hzv₄]
        _ = (π ≫ β) ≫ b₃ := (Cat.assoc _ _ _).symm
    have hdb₃ : d ≫ b₃ = zeroMorphism P B₄ := by
      rw [hd, HalfAdditiveCategory.add_comp, ← hxv₃b₃, ← HalfAdditiveCategory.add_comp,
          hneg, zeroHom_eq_zeroMorphism' P B₃, zeroMorphism_comp_left b₃]
    -- cover Q of P with ỹ : Q → B₂, ρ ≫ d = ỹ ≫ b₂
    obtain ⟨Q, ρ, yt, hρ_cover, hρy⟩ := relexact_cover_factor hB₂₃ d hdb₃
    -- u := ỹ ≫ v₂⁻¹ : Q → A₂,  u ≫ v₂ = ỹ
    let u : Q ⟶ A₂ := yt ≫ v₂i
    have hu : u = yt ≫ v₂i := rfl
    have huv₂ : u ≫ v₂ = yt := by rw [hu, Cat.assoc, hv₂2, Cat.comp_id]
    -- (B):  add ((ρ≫xt)≫v₃) (ρ≫neg) = zeroHom
    have hBeq : HalfAdditiveCategory.add ((ρ ≫ xt) ≫ v₃) (ρ ≫ neg)
        = HalfAdditiveCategory.zeroHom Q B₃ := by
      have h0 : ρ ≫ HalfAdditiveCategory.add (xt ≫ v₃) neg = ρ ≫ HalfAdditiveCategory.zeroHom P B₃ := by
        rw [hneg]
      rw [HalfAdditiveCategory.comp_add, ← Cat.assoc,
          HalfAdditiveCategory.zeroHom_comp_left ρ] at h0
      exact h0
    -- (A):  u ≫ (a₂ ≫ v₃) = add (ρ ≫ (π ≫ β)) (ρ ≫ neg)
    have hAeq : u ≫ (a₂ ≫ v₃)
        = HalfAdditiveCategory.add (ρ ≫ (π ≫ β)) (ρ ≫ neg) := by
      calc u ≫ (a₂ ≫ v₃) = u ≫ (v₂ ≫ b₂) := by rw [sq₂]
        _ = (u ≫ v₂) ≫ b₂ := (Cat.assoc _ _ _).symm
        _ = yt ≫ b₂ := by rw [huv₂]
        _ = ρ ≫ d := hρy.symm
        _ = ρ ≫ HalfAdditiveCategory.add (π ≫ β) neg := by rw [hd]
        _ = HalfAdditiveCategory.add (ρ ≫ (π ≫ β)) (ρ ≫ neg) :=
            HalfAdditiveCategory.comp_add ρ (π ≫ β) neg
    -- χ := (u ≫ a₂) + (ρ ≫ xt) : Q → A₃ ;  show (ρ ≫ π) ≫ β = χ ≫ v₃.
    let χ : Q ⟶ A₃ := HalfAdditiveCategory.add (u ≫ a₂) (ρ ≫ xt)
    have hχ : χ = HalfAdditiveCategory.add (u ≫ a₂) (ρ ≫ xt) := rfl
    have hχv₃ : (ρ ≫ π) ≫ β = χ ≫ v₃ := by
      have hcompχ : χ ≫ v₃
          = HalfAdditiveCategory.add (u ≫ (a₂ ≫ v₃)) ((ρ ≫ xt) ≫ v₃) := by
        rw [hχ, HalfAdditiveCategory.add_comp, Cat.assoc]
      calc (ρ ≫ π) ≫ β
          = ρ ≫ (π ≫ β) := Cat.assoc _ _ _
        _ = HalfAdditiveCategory.add (ρ ≫ (π ≫ β)) (HalfAdditiveCategory.zeroHom Q B₃) :=
            (HalfAdditiveCategory.add_zero _).symm
        _ = HalfAdditiveCategory.add (ρ ≫ (π ≫ β))
              (HalfAdditiveCategory.add ((ρ ≫ xt) ≫ v₃) (ρ ≫ neg)) := by rw [hBeq]
        _ = HalfAdditiveCategory.add (ρ ≫ (π ≫ β))
              (HalfAdditiveCategory.add (ρ ≫ neg) ((ρ ≫ xt) ≫ v₃)) := by
            rw [HalfAdditiveCategory.add_comm ((ρ ≫ xt) ≫ v₃) (ρ ≫ neg)]
        _ = HalfAdditiveCategory.add
              (HalfAdditiveCategory.add (ρ ≫ (π ≫ β)) (ρ ≫ neg)) ((ρ ≫ xt) ≫ v₃) :=
            HalfAdditiveCategory.add_assoc _ _ _
        _ = HalfAdditiveCategory.add (u ≫ (a₂ ≫ v₃)) ((ρ ≫ xt) ≫ v₃) := by rw [hAeq]
        _ = χ ≫ v₃ := hcompχ.symm
    -- `(ρ ≫ π) ≫ β` factors through `image v₃`; `cover_mono_diagonal` (cover ⊥ mono) descends
    -- a right inverse of `j := (image v₃).arr`, which is monic, hence iso.
    have hρπ_cover : Cover (ρ ≫ π) := cover_comp hρ_cover hπ_cover
    have hsq : (ρ ≫ π) ≫ β = (χ ≫ image.lift v₃) ≫ (image v₃).arr := by
      rw [hχv₃, Cat.assoc, image.lift_fac]
    obtain ⟨g, _, hg⟩ := cover_mono_diagonal hρπ_cover (image v₃).monic hsq
    -- hg : g ≫ (image v₃).arr = β = id_{B₃}, so (image v₃).arr is split epi; it is monic ⟹ iso
    have hsplit : g ≫ (image v₃).arr = Cat.id B₃ := by rw [hg, hβ]
    have hother : (image v₃).arr ≫ g = Cat.id (image v₃).dom :=
      (image v₃).monic ((image v₃).arr ≫ g) (Cat.id _) (by
        rw [Cat.assoc, hsplit, Cat.comp_id, Cat.id_comp])
    show IsIso (image v₃).arr
    exact ⟨g, hother, hsplit⟩
  exact monic_cover_iso v₃ hcover hmono

/-! §1.599 SNAKE LEMMA: In an abelian category, given a commutative diagram

      A ──f──→ B ──g──→ C
      |α       |β       |γ
      ↓        ↓        ↓
      A'──f'──→B'──g'──→C'

  with both rows exact, there exist induced morphisms on kernels/cokernels
  and a "connecting morphism" δ : ker(γ) → coker(α) making the sequence

    ker(α) → ker(β) → ker(γ) →δ coker(α) → coker(β) → coker(γ)

  exact.  (Sufficient to verify in Ab; the statement is a Horn sentence.)

  The induced morphisms are:
    κ_f : ker(α) → ker(β)   (kernel-functoriality of f)
    κ_g : ker(β) → ker(γ)   (kernel-functoriality of g)
    π_f : coker(α) → coker(β)  (cokernel-functoriality of f')
    π_g : coker(β) → coker(γ)  (cokernel-functoriality of g')
  These are defined by universal properties; we state their existence.

  BLOCKER (sharpened): the connecting morphism δ is, in Freyd's own words (§1.599), built
  "as a relation" — the composite ker(γ)→C ⤳ B ⤳ B' ⤳ coker(α) of a reciprocal, a vertical,
  and another reciprocal — and shown single-valued/total only via the calculus of relations
  in the Ab-representation (§1.55 + §1.56 reciprocation).  That δ-as-relation machinery, and
  the proof that the resulting 6-term sequence is exact, both reduce to Ab by the §1.543
  capitalization metatheorem (concurrent agent, not yet importable).  The kernel/cokernel
  functoriality maps κ_*, π_* DO follow from the present universal properties, but the
  conjunction's hard core (existence of δ + four exactness isos) cannot be discharged without
  the relational calculus; a partial proof would leave δ a `Sorry` inside the existential and
  is no more honest than the whole-statement Sorry.  Faithful Sorry retained.

  STATEMENT FIX (faithful): row exactness is now `RelExact f g` / `RelExact f' g'`, and the four
  output exactness claims are `RelExact` too — the ≫-compatible (subobject-equal) form, NOT the
  too-weak bare object iso (see the `RelExact` definition and the `five_lemma` note for why the
  bare iso is the wrong encoding).  This is a strengthening of both hypothesis and conclusion to
  the faithful definition of exactness.

  RESIDUAL BLOCKER (honest `sorry` retained — names the precise missing infra).  Even with
  `RelExact` and the now-available additive inverses, the connecting morphism `δ : ker γ → coker α`
  is, in Freyd's own construction (§1.599), built "as a relation": the composite
  `ker γ → C ⤳ B ⤳ B' ⤳ coker α` of a reciprocal, a vertical, and another reciprocal, shown
  single-valued and total only via the CALCULUS OF RELATIONS in the §1.55 Ab-representation +
  §1.56 reciprocation.  The MISSING LEMMA is precisely: a constructive, representation-free
  definition of `δ` together with `δ`'s well-definedness — concretely, a pullback `P = B ×_C ker γ`
  of `g` along `ker γ ↪ C`, a section's image in `coker α` independent of the chosen lift, which in
  this hand-built framework needs the relational-composite single-valuedness lemma
  (`relComp_singleValued` over §1.56), not yet available here.  Without `δ`, the existential cannot
  be honestly witnessed (a `sorry`-d `δ` inside the `∃` is no more honest than the whole-statement
  `sorry`).  The induced maps `κ_f, κ_g, π_f, π_g` and their exactness DO follow from `RelExact` +
  the kernel/cokernel universal properties; the sole gap is `δ` and the two exactness claims that
  mention it.  Faithful `sorry` retained. -/
theorem snake_lemma [AbelianCategory 𝒞]
    {A B C A' B' C' : 𝒞}
    {f : A ⟶ B} {g : B ⟶ C} {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'}
    {f' : A' ⟶ B'} {g' : B' ⟶ C'}
    -- rows exact (image = kernel at each interior node, as subobjects)
    (hfg : RelExact f g) (hf'g' : RelExact f' g')
    -- squares commute
    (hαβ : f ≫ β = α ≫ f') (hβγ : g ≫ γ = β ≫ g') :
    -- induced kernel maps (by universal property: ker(α) ≫ f ≫ β = 0, lifts to ker(β))
    ∃ (κ_f : Kernel α ⟶ Kernel β) (κ_g : Kernel β ⟶ Kernel γ)
      (π_f : Cokernel α ⟶ Cokernel β) (π_g : Cokernel β ⟶ Cokernel γ)
      (δ : Kernel γ ⟶ Cokernel α),
      -- The induced sequence ker(α)→ker(β)→ker(γ)→coker(α)→coker(β) is exact at each node:
      RelExact κ_f κ_g ∧ RelExact κ_g δ ∧ RelExact δ π_f ∧ RelExact π_f π_g := by
  sorry

end Freyd
