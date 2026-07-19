import Mathlib.CategoryTheory.Category.RelCat
import Mathlib.CategoryTheory.Endofunctor.Algebra

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

/-! ## General polynomial relator and initial algebra

This is the direct Mathlib version of the reusable machinery in `A6_1_Digits.lean`.
Mathlib supplies `Functor`, `Endofunctor.Algebra`, and `Limits.IsInitial`; only the
order-enrichment (the extra condition that makes a functor a book relator) is local.
-/

/-- Pointwise inclusion of relations. -/
def subrel {A B : Rel} (R S : A ⟶ B) : Prop := ∀ a b, R.rel (a, b) → S.rel (a, b)

/-- The book's relator: an ordinary endofunctor whose action is monotone. -/
structure Relator where
  toFunctor : Rel ⥤ Rel
  map_mono : ∀ {A B : Rel} {R S : A ⟶ B}, subrel R S →
    subrel (toFunctor.map R) (toFunctor.map S)

instance : Coe Relator (Rel ⥤ Rel) := ⟨Relator.toFunctor⟩

/-- `F A = Digit⁺ + (A × Digit)`. -/
def Fobj (A : Rel) : Rel := DigitP ⊕ (A × Digit)

/-- `F R = id + (R × id)`. -/
def Fmap {A B : Rel} (R : A ⟶ B) : Fobj A ⟶ Fobj B :=
  rel fun u v => match u, v with
    | Sum.inl d, Sum.inl e => d = e
    | Sum.inr p, Sum.inr q => R.rel (p.1, q.1) ∧ p.2 = q.2
    | _, _ => False

/-- The digits polynomial as a Mathlib functor. -/
def FFunctor : Rel ⥤ Rel where
  obj := Fobj
  map := Fmap
  map_id A := by
    apply RelCat.Hom.ext
    funext ⟨u, v⟩
    apply propext
    cases u with
    | inl d => cases v with
      | inl e => exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
      | inr q => exact ⟨False.elim, fun h => nomatch h⟩
    | inr p => cases v with
      | inl e => exact ⟨False.elim, fun h => nomatch h⟩
      | inr q => exact ⟨fun h => congrArg Sum.inr (Prod.ext_iff.mpr h),
          fun h => Prod.ext_iff.mp (Sum.inr.inj h)⟩
  map_comp R S := by
    apply RelCat.Hom.ext
    funext ⟨u, v⟩
    apply propext
    cases u with
    | inl d => cases v with
      | inl e => exact ⟨fun h => ⟨Sum.inl d, rfl, h⟩,
          fun ⟨w, hw, hw'⟩ => by cases w with
            | inl k => exact hw.trans hw'
            | inr q => exact hw.elim⟩
      | inr q => exact ⟨False.elim, fun ⟨w, hw, hw'⟩ => by
          cases w <;> first | exact hw.elim | exact hw'.elim⟩
    | inr p => cases v with
      | inl e => exact ⟨False.elim, fun ⟨w, hw, hw'⟩ => by
          cases w <;> first | exact hw.elim | exact hw'.elim⟩
      | inr q =>
          exact ⟨fun ⟨⟨m, hm, hm'⟩, hd⟩ =>
              ⟨Sum.inr (m, p.2), ⟨hm, rfl⟩, ⟨hm', hd⟩⟩,
            fun ⟨w, hw, hw'⟩ => by cases w with
              | inl e => exact hw.elim
              | inr z => exact ⟨⟨z.1, hw.1, hw'.1⟩, hw.2.trans hw'.2⟩⟩

/-- The digits polynomial is a relator in the book's sense. -/
def F : Relator where
  toFunctor := FFunctor
  map_mono h := by
    intro u v huv
    cases u <;> cases v <;> simp_all [FFunctor, Fmap, rel, subrel]

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

/-- Constructor algebra `⁅wrap,snoc⁆ : F Decimal ⟶ Decimal`. -/
def constructors : Fobj Decimal ⟶ Decimal := rel fun u x =>
  (match u with
    | Sum.inl d => Decimal.Carrier.wrap d
    | Sum.inr p => Decimal.Carrier.snoc p.1 p.2) = x

/-- Constructive fold of an arbitrary relation algebra. -/
def cataFold {A : Rel} (φ : Fobj A ⟶ A) : Decimal → A → Prop
  | .wrap d, a => φ.rel (Sum.inl d, a)
  | .snoc x d, a => ∃ b, cataFold φ x b ∧ φ.rel (Sum.inr (b, d), a)

/-- The fold, bundled as a `RelCat` morphism. -/
def cata {A : Rel} (φ : Fobj A ⟶ A) : Decimal ⟶ A := rel (cataFold φ)

/-- The initial digits algebra in Mathlib's standard algebra category. -/
def decimalAlgebra : Endofunctor.Algebra FFunctor := ⟨Decimal, constructors⟩

/-- The constructive fold is an algebra homomorphism. -/
def cataHom (A : Endofunctor.Algebra FFunctor) : decimalAlgebra ⟶ A where
  f := cata A.str
  h := by
    apply RelCat.Hom.ext
    funext ⟨u, a⟩
    apply propext
    cases u with
    | inl d =>
      constructor
      · rintro ⟨v, hv, ha⟩
        cases v with
        | inl e => subst e; exact ⟨Decimal.Carrier.wrap d, rfl, ha⟩
        | inr q => exact hv.elim
      · rintro ⟨x, hx, ha⟩
        change Decimal.Carrier.wrap d = x at hx
        subst x; exact ⟨Sum.inl d, rfl, ha⟩
    | inr p =>
      constructor
      · rintro ⟨v, hv, ha⟩
        cases v with
        | inl e => exact hv.elim
        | inr q =>
          obtain ⟨hq, hd⟩ := hv
          exact ⟨Decimal.Carrier.snoc p.1 p.2, rfl, q.1, hq, hd ▸ ha⟩
      · rintro ⟨x, hx, ha⟩
        change Decimal.Carrier.snoc p.1 p.2 = x at hx
        subst x
        obtain ⟨b, hb, hφ⟩ := ha
        exact ⟨Sum.inr (b, p.2), ⟨hb, rfl⟩, hφ⟩

/-- `Decimal` is initial, hence `cataHom` is the general catamorphism theorem.
Unlike the project-specific structure, no `Map` premises are needed in concrete `RelCat`. -/
def decimalIsInitial : Limits.IsInitial decimalAlgebra :=
  Limits.IsInitial.ofUniqueHom cataHom fun A h => by
    apply Endofunctor.Algebra.Hom.ext
    apply RelCat.Hom.ext
    funext ⟨x, a⟩
    apply propext
    induction x generalizing a with
    | wrap d =>
        have e := congrArg (fun k => k.rel (Sum.inl d, a)) h.h
        change (FFunctor.map h.f ≫ A.str).rel (Sum.inl d, a) =
          (decimalAlgebra.str ≫ h.f).rel (Sum.inl d, a) at e
        constructor
        · intro hh
          have lhs : (decimalAlgebra.str ≫ h.f).rel (Sum.inl d, a) :=
            ⟨Decimal.Carrier.wrap d, rfl, hh⟩
          rw [← e] at lhs
          obtain ⟨v, hv, ha⟩ := lhs
          cases v with
          | inl k => subst k; exact ha
          | inr q => exact hv.elim
        · intro ha
          have rhs : (FFunctor.map h.f ≫ A.str).rel (Sum.inl d, a) :=
            ⟨Sum.inl d, rfl, ha⟩
          rw [e] at rhs
          obtain ⟨x, hx, hh⟩ := rhs
          change Decimal.Carrier.wrap d = x at hx
          subst x; exact hh
    | snoc x d ih =>
        have e := congrArg (fun k => k.rel (Sum.inr (x, d), a)) h.h
        change (FFunctor.map h.f ≫ A.str).rel (Sum.inr (x, d), a) =
          (decimalAlgebra.str ≫ h.f).rel (Sum.inr (x, d), a) at e
        constructor
        · intro hh
          have lhs : (decimalAlgebra.str ≫ h.f).rel (Sum.inr (x, d), a) :=
            ⟨Decimal.Carrier.snoc x d, rfl, hh⟩
          rw [← e] at lhs
          obtain ⟨v, hv, ha⟩ := lhs
          cases v with
          | inl k => exact hv.elim
          | inr q =>
              obtain ⟨qb, qd⟩ := q
              change h.f.rel (x, qb) ∧ d = qd at hv
              rw [← hv.2] at ha
              exact ⟨qb, (ih qb).mp hv.1, ha⟩
        · rintro ⟨b, hb, ha⟩
          have rhs : (FFunctor.map h.f ≫ A.str).rel (Sum.inr (x, d), a) :=
            ⟨Sum.inr (b, d), ⟨(ih b).mpr hb, rfl⟩, ha⟩
          rw [e] at rhs
          obtain ⟨y, hy, hh⟩ := rhs
          change Decimal.Carrier.snoc x d = y at hy
          subst y; exact hh

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
