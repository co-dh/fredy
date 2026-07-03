/-
  Bird & de Moor, *Algebra of Programming* §5.6  Combinatorial functions (book pp. 125-132) —
  the list combinators, as concrete relations on `list A = ConsList Unit A` in the Set model.

  These are the relations the optimisation case studies (§6.6 sorting, §7.5 security van, §8.x
  thinning, …) take as their coalgebra / specification: `perm` (permutation), `prefix`/`suffix`,
  `subseq` (subsequence), `inlist` (membership).  B&dM define them point-free (catamorphisms:
  `perm = ⦇[nil, perm·cons]⦈`, `prefix = ⦇[nil, nil∪cons]⦈`, `partition = concat°`, …); here we
  give the equivalent concrete meaning as an inductive/structural relation and prove the algebraic
  properties (reflexivity, symmetry, transitivity) that the derivations use.  Built on the cons-list
  engine `Fredy.A6_ConsList` (`list A = ConsList Unit A`).
-/
import Fredy.A6_ConsList

namespace Freyd.Alg.RelSet.ListRel

open Freyd Freyd.Alg.RelSet.CL

variable {A : Type}

/-- `list A = ConsList Unit A` (`nil = wrap ()`, `cons a x`). -/
abbrev dList (A : Type) : RelSet.{0} := dCL Unit A

/-! ## Membership `inlist : A ← list A` -/

/-- `a ∈ x`. -/
def inlistP : ConsList Unit A → A → Prop
  | ConsList.wrap _, _ => False
  | ConsList.cons b x, a => a = b ∨ inlistP x a

/-- The membership relation `inlist : list A ⟶ A`. -/
def inlist : dList A ⟶ dE A := inlistP

/-! ## Permutation `perm : list A ← list A` -/

/-- The permutation relation, inductively (equivalent to B&dM's `⦇[nil, perm·cons]⦈`): `y` is a
    rearrangement of `x`. -/
inductive Perm : ConsList Unit A → ConsList Unit A → Prop
  | nil : Perm (ConsList.wrap ()) (ConsList.wrap ())
  | cons (a : A) {x y : ConsList Unit A} : Perm x y → Perm (ConsList.cons a x) (ConsList.cons a y)
  | swap (a b : A) (x : ConsList Unit A) :
      Perm (ConsList.cons a (ConsList.cons b x)) (ConsList.cons b (ConsList.cons a x))
  | trans {x y z : ConsList Unit A} : Perm x y → Perm y z → Perm x z

theorem Perm.refl : ∀ x : ConsList Unit A, Perm x x
  | ConsList.wrap () => Perm.nil
  | ConsList.cons a x => Perm.cons a (Perm.refl x)

theorem Perm.symm : ∀ {x y : ConsList Unit A}, Perm x y → Perm y x
  | _, _, Perm.nil => Perm.nil
  | _, _, Perm.cons a h => Perm.cons a h.symm
  | _, _, Perm.swap a b x => Perm.swap b a x
  | _, _, Perm.trans h1 h2 => Perm.trans h2.symm h1.symm

/-- The permutation relation `perm : list A ⟶ list A`. -/
def perm : dList A ⟶ dList A := Perm

/-- **`perm` is reflexive**: `id ⊑ perm`. -/
theorem perm_reflexive : Cat.id (dList A) ⊑ perm :=
  le_iff.mpr fun x y hxy => hxy ▸ Perm.refl x

/-- **`perm` is symmetric**: `perm° = perm` (B&dM `perm = perm°`, used throughout §6.6). -/
theorem perm_symmetric : (perm : dList A ⟶ dList A)° = perm :=
  hom_ext fun x y => ⟨fun h => Perm.symm h, fun h => Perm.symm h⟩

/-- **`perm` is transitive**: `perm ≫ perm ⊑ perm`. -/
theorem perm_transitive : (perm : dList A ⟶ dList A) ≫ perm ⊑ perm :=
  le_iff.mpr fun x z h => by obtain ⟨y, hxy, hyz⟩ := h; exact Perm.trans hxy hyz

/-! ## Prefix `prefix : list A ← list A` -/

/-- `x` is a prefix of `y`. -/
def prefixP : ConsList Unit A → ConsList Unit A → Prop
  | ConsList.wrap _, _ => True
  | ConsList.cons _ _, ConsList.wrap _ => False
  | ConsList.cons a x, ConsList.cons b y => a = b ∧ prefixP x y

/-- The prefix relation `prefix : list A ⟶ list A`. -/
def prefixR : dList A ⟶ dList A := prefixP

theorem prefixP.refl : ∀ x : ConsList Unit A, prefixP x x
  | ConsList.wrap _ => trivial
  | ConsList.cons a x => ⟨rfl, prefixP.refl x⟩

theorem prefixP.trans : ∀ {x y z : ConsList Unit A}, prefixP x y → prefixP y z → prefixP x z
  | ConsList.wrap _, _, _, _, _ => trivial
  | ConsList.cons a x, ConsList.cons b y, ConsList.cons c z, ⟨hab, hxy⟩, ⟨hbc, hyz⟩ =>
      ⟨hab.trans hbc, prefixP.trans hxy hyz⟩

/-- **`prefix` is a preorder**: reflexive and transitive. -/
theorem prefix_reflexive : Cat.id (dList A) ⊑ prefixR :=
  le_iff.mpr fun x y hxy => hxy ▸ prefixP.refl x
theorem prefix_transitive : (prefixR : dList A ⟶ dList A) ≫ prefixR ⊑ prefixR :=
  le_iff.mpr fun x z h => by obtain ⟨y, hxy, hyz⟩ := h; exact prefixP.trans hxy hyz

/-! ## Subsequence `subseq : list A ← list A` -/

/-- `x` is a subsequence of `y` (drop some elements of `y`). -/
def subseqP : ConsList Unit A → ConsList Unit A → Prop
  | ConsList.wrap _, _ => True
  | ConsList.cons _ _, ConsList.wrap _ => False
  | ConsList.cons a x, ConsList.cons b y => (a = b ∧ subseqP x y) ∨ subseqP (ConsList.cons a x) y

/-- The subsequence relation `subseq : list A ⟶ list A`. -/
def subseq : dList A ⟶ dList A := subseqP

theorem subseqP.refl : ∀ x : ConsList Unit A, subseqP x x
  | ConsList.wrap _ => trivial
  | ConsList.cons a x => Or.inl ⟨rfl, subseqP.refl x⟩

/-- Extending the larger list on the front preserves subsequence: `subseq x y → subseq x (b::y)`. -/
theorem subseqP.weaken {b : A} : ∀ {x y : ConsList Unit A}, subseqP x y → subseqP x (ConsList.cons b y)
  | ConsList.wrap _, _, _ => trivial
  | ConsList.cons a x, y, h => Or.inr h

/-- Dropping the front element of the smaller list preserves subsequence. -/
theorem subseqP.of_cons {a : A} :
    ∀ {x y : ConsList Unit A}, subseqP (ConsList.cons a x) y → subseqP x y
  | x, ConsList.wrap _, h => h.elim
  | x, ConsList.cons b y, h => by
    cases h with
    | inl h => exact subseqP.weaken h.2
    | inr h => exact subseqP.weaken (subseqP.of_cons h)

/-- **`subseq` is reflexive**. -/
theorem subseq_reflexive : Cat.id (dList A) ⊑ subseq :=
  le_iff.mpr fun x y hxy => hxy ▸ subseqP.refl x

end Freyd.Alg.RelSet.ListRel
