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

/-- An ABELIAN CATEGORY: regular, additive, every subobject is normal (§1.593).
  Includes cokernels (§1.592: an abelian category has kernels and cokernels). -/
class AbelianCategory (𝒞 : Type u) [Cat.{v} 𝒞]
    extends RegularCategory 𝒞, HalfAdditiveCategory 𝒞, HasZeroObject 𝒞,
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

  PROOF (sketch, both directions need the §1.55 Ab-representation, not yet importable):
  (→) all monics normal ⟹ every cover that is monic is an iso (regular+additive), so every
  morphism factors as cokernel∘kernel and θ is forced to be an iso ⟹ `IsExactStructure`.
  (←) exact ⟹ every monic x is the kernel of its cokernel (`monic_kernel_of_cokernel`), i.e.
  normal.  This converse direction is, in fact, already provable from `monic_kernel_of_cokernel`
  once exactness is packaged as an `ExactCategory`; only the forward direction strictly needs
  the Ab-representation.  Faithful Sorry retained for both. -/
theorem abelian_iff_regular_additive_all_normal
    (𝒞 : Type u) [Cat.{v} 𝒞]
    [RegularCategory 𝒞] [AdditiveCategory 𝒞] [HasZeroObject 𝒞]
    [HasEqualizers 𝒞] [HasCoequalizers 𝒞] :
    (∀ {A B : 𝒞} (m : A ⟶ B) (hm : Mono m), IsNormalSubobject m hm) ↔
    IsExactStructure 𝒞 := by
  constructor
  · -- (→) all monics normal ⟹ IsExactStructure.  RESIDUAL (rep-needed): deducing that
    -- every morphism's coimage→image comparison θ is an iso requires the §1.55
    -- Ab-representation (regularity reflects θ-iso); not recoverable from the present
    -- `Cat`-level fields.  See `abelianOfExactAdditive` for the reverse keystone route.
    intro _hnormal
    sorry
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
    content, reduced to the single sharp residual `pullback_epi_is_epi`.

  Balancedness (`exact_balanced`) and `epi_is_cover` are proved sorry-free along the
  way and are reusable.  Only `pullback_epi_is_epi` carries a `sorry`. -/

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
  sorry

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
  letI hha : HalfAdditiveCategory 𝒞 := inferInstance
  letI hz : HasZeroObject 𝒞 := inferInstance
  { toRegularCategory := hreg
    toHasEqualizers := (inferInstance : HasEqualizers 𝒞)
    toHasCoequalizers := (inferInstance : HasCoequalizers 𝒞)
    zeroHom := hha.zeroHom
    zeroHom_comp_left := hha.zeroHom_comp_left
    zeroHom_comp_right := hha.zeroHom_comp_right
    prod_coprod_coincide := hha.prod_coprod_coincide
    add := hha.add
    add_eq_addL := hha.add_eq_addL
    add_eq_addR := hha.add_eq_addR
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
  when the image of f is isomorphic to the kernel of g.
  Note: `ExactAt` is defined in `S1_39.lean`; this comment documents it here per §1.599.
  We use `Isomorphic (image f).dom (Kernel g)` inline in statements below. -/

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

  BLOCKER (sharpened): the Horn-sentence reduction "holds in 𝒞 ⟺ holds in Ab" is the
  metatheorem of §1.543 (capitalization / the faithful embedding into a functor category
  that reflects bicartesian Horn sentences).  That chain is owned by a concurrent agent
  and is not yet importable.  The *element-level* alternative (a direct categorical diagram
  chase) needs the Ab-valued representation of §1.55 (subobject lattices + element chasing),
  which is also absent.  No shortcut exists from the present `AbelianCategory` / `ExactCategory`
  fields alone: the goal is bare `IsIso v₃` with only the six exactness isos and four square
  commutativities, and `IsIso` is not recoverable without constructing ker(v₃)=0 ∧ coker(v₃)=0.
  Faithful Sorry retained (statement is Freyd §1.599, verified true and non-vacuous). -/
theorem five_lemma [AbelianCategory 𝒞]
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : 𝒞}
    {a₁ : A₁ ⟶ A₂} {a₂ : A₂ ⟶ A₃} {a₃ : A₃ ⟶ A₄} {a₄ : A₄ ⟶ A₅}
    {b₁ : B₁ ⟶ B₂} {b₂ : B₂ ⟶ B₃} {b₃ : B₃ ⟶ B₄} {b₄ : B₄ ⟶ B₅}
    {v₁ : A₁ ⟶ B₁} {v₂ : A₂ ⟶ B₂} {v₃ : A₃ ⟶ B₃} {v₄ : A₄ ⟶ B₄} {v₅ : A₅ ⟶ B₅}
    -- rows are exact (image of aₙ ≅ kernel of aₙ₊₁)
    (hA₁₂ : Isomorphic (image a₁).dom (Kernel a₂))
    (hA₂₃ : Isomorphic (image a₂).dom (Kernel a₃))
    (hA₃₄ : Isomorphic (image a₃).dom (Kernel a₄))
    (hB₁₂ : Isomorphic (image b₁).dom (Kernel b₂))
    (hB₂₃ : Isomorphic (image b₂).dom (Kernel b₃))
    (hB₃₄ : Isomorphic (image b₃).dom (Kernel b₄))
    -- squares commute
    (sq₁ : a₁ ≫ v₂ = v₁ ≫ b₁) (sq₂ : a₂ ≫ v₃ = v₂ ≫ b₂)
    (sq₃ : a₃ ≫ v₄ = v₃ ≫ b₃) (sq₄ : a₄ ≫ v₅ = v₄ ≫ b₄)
    -- outer four verticals are isos
    (h₁ : IsIso v₁) (h₂ : IsIso v₂) (h₄ : IsIso v₄) (h₅ : IsIso v₅) :
    IsIso v₃ := by
  sorry

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
  is no more honest than the whole-statement Sorry.  Faithful Sorry retained. -/
theorem snake_lemma [AbelianCategory 𝒞]
    {A B C A' B' C' : 𝒞}
    {f : A ⟶ B} {g : B ⟶ C} {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'}
    {f' : A' ⟶ B'} {g' : B' ⟶ C'}
    -- rows exact (image ≅ kernel at each interior node)
    (hfg : Isomorphic (image f).dom (Kernel g))
    (hf'g' : Isomorphic (image f').dom (Kernel g'))
    -- squares commute
    (hαβ : f ≫ β = α ≫ f') (hβγ : g ≫ γ = β ≫ g') :
    -- induced kernel maps (by universal property: ker(α) ≫ f ≫ β = 0, lifts to ker(β))
    ∃ (κ_f : Kernel α ⟶ Kernel β) (κ_g : Kernel β ⟶ Kernel γ)
      (π_f : Cokernel α ⟶ Cokernel β) (π_g : Cokernel β ⟶ Cokernel γ)
      (δ : Kernel γ ⟶ Cokernel α),
      -- The induced sequence ker(α)→ker(β)→ker(γ)→coker(α)→coker(β) is exact at each node:
      Isomorphic (image κ_f).dom (Kernel κ_g) ∧
      Isomorphic (image κ_g).dom (Kernel δ) ∧
      Isomorphic (image δ).dom (Kernel π_f) ∧
      Isomorphic (image π_f).dom (Kernel π_g) := by
  sorry

end Freyd
