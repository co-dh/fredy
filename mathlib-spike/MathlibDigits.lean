import Mathlib.CategoryTheory.Category.RelCat

/-!
Experimental vertical slice: B&dM p.138 directly over Mathlib's `RelCat`.
This deliberately does not import or modify Fredy's custom category hierarchy.
-/

namespace FredyMathlibSpike

open CategoryTheory
open SetRel

abbrev Rel := CategoryTheory.RelCat

/-- The ten decimal digits, directly as an object of Mathlib's relation category. -/
def Digit : Rel := Fin 10

/-- The book's `Digit⁺`, spelled `DigitP` in Lean source. -/
def DigitP : Rel := { d : Digit // d.val ≠ 0 }

/-- `Decimal ::= wrap Digit⁺ | snoc (Decimal, Digit)`. -/
inductive Decimal.Carrier where
  | wrap : DigitP → Carrier
  | snoc : Carrier → Digit → Carrier

/-- Decimal representations, directly as an object of Mathlib's relation category. -/
def Decimal : Rel := Decimal.Carrier

/-- Binary product of `RelCat` objects, kept under a `Rel`-valued name so `⟶` selects `RelCat`. -/
def Prod (A B : Rel) : Rel := A × B

/-- Build a Mathlib `RelCat` morphism from its underlying relation. -/
def rel {A B : Rel} (R : A → B → Prop) : A ⟶ B := .ofRel fun p => R p.1 p.2

/-- Converse of a relation. -/
def recip {A B : Rel} (R : A ⟶ B) : B ⟶ A := rel fun b a => R.rel (a, b)

postfix:max "°" => recip

/-- Union of relations. -/
def union {A B : Rel} (R S : A ⟶ B) : A ⟶ B :=
  rel fun a b => R.rel (a, b) ∨ S.rel (a, b)

infixl:65 " ∪ " => union

/-- Product action of two relations. -/
def rprod {A A' B B' : Rel} (R : A ⟶ A') (S : B ⟶ B') :
    Prod A B ⟶ Prod A' B' :=
  rel fun (p : A × B) (q : A' × B') => R.rel (p.1, q.1) ∧ S.rel (p.2, q.2)

/-- Identity relation, named as in the book. -/
def rid (A : Rel) : A ⟶ A := 𝟙 A

/-- The book's constructor relation `wrap : Digit⁺ → Decimal`. -/
def wrap : DigitP ⟶ Decimal := rel fun d x => x = Decimal.Carrier.wrap d

/-- The book's constructor relation `snoc : Decimal × Digit → Decimal`. -/
def snoc : Prod Decimal Digit ⟶ Decimal :=
  rel fun (p : Decimal × Digit) x => x = Decimal.Carrier.snoc p.1 p.2

/-- The book's `embed : Digit⁺ → Nat⁺`, using `Nat` as in the existing development. -/
def embed : DigitP ⟶ Nat := rel fun d n => n = d.1.val

/-- The book's `op (n,d) = 10n+d`. -/
def op : Prod Nat Digit ⟶ Nat :=
  rel fun (p : Nat × Digit) n => n = 10 * p.1 + p.2.val

/-- The valuation function underlying the catamorphism `⦇[embed,op]⦈`. -/
def valFn : Decimal → Nat
  | .wrap d => d.1.val
  | .snoc x d => 10 * valFn x + d.val

/-- `val : Decimal → Nat`, now with exactly the book-level object names in its categorical type. -/
def val : Decimal ⟶ Nat := rel fun x n => n = valFn x

/-- B&dM p.138's recursive equation, in the repository's diagram-order composition.
The statement has no object wrappers and no `.carrier`; `.rel` appears only when proving equality
of bundled morphisms. -/
theorem val_converse_eq :
    val° = embed° ≫ wrap ∪ op° ≫ rprod val° (rid Digit) ≫ snoc := by
  apply RelCat.Hom.ext
  funext p
  rcases p with ⟨n, x⟩
  apply propext
  cases x with
  | wrap d =>
      change n = d.1.val ↔
        (∃ e : DigitP, n = e.1.val ∧ Decimal.Carrier.wrap d = Decimal.Carrier.wrap e) ∨
        ∃ p : Nat × Digit, n = 10 * p.1 + p.2.val ∧
          ∃ q : Decimal × Digit,
            (p.1 = valFn q.1 ∧ p.2 = q.2) ∧
              Decimal.Carrier.wrap d = Decimal.Carrier.snoc q.1 q.2
      constructor
      · intro h; exact Or.inl ⟨d, h, rfl⟩
      · rintro (⟨e, h, he⟩ | ⟨p, hp, q, hq, hbad⟩)
        · exact h.trans (congrArg (fun z => z.1.val) (Decimal.Carrier.wrap.inj he.symm))
        · exact Decimal.Carrier.noConfusion hbad
  | snoc x d =>
      change n = 10 * valFn x + d.val ↔
        (∃ e : DigitP, n = e.1.val ∧ Decimal.Carrier.snoc x d = Decimal.Carrier.wrap e) ∨
        ∃ p : Nat × Digit, n = 10 * p.1 + p.2.val ∧
          ∃ q : Decimal × Digit,
            (p.1 = valFn q.1 ∧ p.2 = q.2) ∧
              Decimal.Carrier.snoc x d = Decimal.Carrier.snoc q.1 q.2
      constructor
      · intro h
        exact Or.inr ⟨(valFn x, d), h, (x, d), ⟨rfl, rfl⟩, rfl⟩
      · rintro (⟨e, he, hbad⟩ | ⟨p, hp, q, hq, hs⟩)
        · exact Decimal.Carrier.noConfusion hbad
        · obtain ⟨hx, hd⟩ := Decimal.Carrier.snoc.inj hs
          rw [hq.1, hq.2, ← hx, ← hd] at hp
          exact hp

end FredyMathlibSpike
