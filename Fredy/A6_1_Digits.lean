/-
  Bird & de Moor, *Algebra of Programming* §6.1  Digits of a number (book pp. 137-140)
  — the first WORKED PROGRAM, derived in the concrete allegory `Rel(Set)` (`Fredy.A6_1_RelSet`).

  A decimal representation is a non-empty sequence of digits starting with a nonzero digit:
    `Decimal ::= wrap Digit⁺ | snoc (Decimal, Digit)`,
  the INITIAL ALGEBRA of the functor `F A = Digit⁺ + (A × Digit)` (book p.138).  `val` reads a
  decimal as a number — the catamorphism `⦇[embed, op]⦈` — and the program `digits` is a
  functional refinement of `val°` (spec (6.1): `digits ⊆ val°`).

  This file builds the reusable DATATYPE-AS-INITIAL-ALGEBRA core (the `Relator` `F` and the
  `InitialAlgebra` instance for `Decimal`, the first in the repo), then derives §6.1's headline:
  the recursive equation the converse of a catamorphism satisfies (mirrored to diagram order),
    `(cata φ)° = (g° ≫ wrap) ∪ (h° ≫ (⟨(cata φ)°, id⟩) ≫ snoc)`   for `φ = [g, h]`,
  which is exactly `val° = (wrap·embed°) ∪ (snoc·(val°×id)·op°)` of book p.138 at `φ = [embed, op]`.
  Everything is constructive (the fold is defined FROM the algebra-relation, no choice).
-/
import Fredy.A6_1_RelSet

namespace Freyd.Alg.RelSet.Digits

open Freyd

/-! ## Datatypes and their objects in `Rel(Set)` (universe 0) -/

/-- The ten decimal digits `{0,…,9}`. -/
def Digit : Type := Fin 10
/-- The nine nonzero digits `{1,…,9}`. -/
def DigitPos : Type := { d : Fin 10 // d.val ≠ 0 }

/-- Decimal representations: `wrap` a leading nonzero digit, then `snoc` further digits. -/
inductive Decimal where
  | wrap : DigitPos → Decimal
  | snoc : Decimal → Digit → Decimal

/-- Object of `Rel(Set)` carrying `Digit`.  `abbrev` so `.carrier` reduces to `Digit`. -/
abbrev dDigit : RelSet.{0} := ⟨Digit⟩
/-- Object of `Rel(Set)` carrying `Digit⁺`. -/
abbrev dDigitPos : RelSet.{0} := ⟨DigitPos⟩
/-- Object of `Rel(Set)` carrying `Decimal`. -/
abbrev dDec : RelSet.{0} := ⟨Decimal⟩

/-! ## Two elementary `Rel(Set)` facts about maps -/

/-- An entire relation relates every point to something. -/
theorem entire_total {a b : RelSet.{u}} {R : a ⟶ b} (h : Entire R) (x : a.carrier) :
    ∃ y, R x y := by
  have hd : (dom R) x x := by
    have e : (dom R) x x = (Cat.id a) x x := congrFun (congrFun h x) x
    rw [e]; rfl
  obtain ⟨_, y, hy, _⟩ := hd
  exact ⟨y, hy⟩

/-- A simple relation is single-valued. -/
theorem simple_uniq {a b : RelSet.{u}} {R : a ⟶ b} (h : Simple R) {x : a.carrier}
    {y y' : b.carrier} (hy : R x y) (hy' : R x y') : y = y' :=
  le_iff.mp h y y' ⟨x, hy, hy'⟩

/-! ## The functor `F A = Digit⁺ + (A × Digit)` -/

/-- Carrier of `F A`. -/
def Fobj (c : RelSet.{0}) : RelSet.{0} := ⟨DigitPos ⊕ (c.carrier × Digit)⟩

/-- Action of `F` on a relation: identity on the `Digit⁺` summand, `R × id` on `A × Digit`. -/
def Fmap {c c' : RelSet.{0}} (R : c ⟶ c') : Fobj c ⟶ Fobj c' :=
  fun u v => match u, v with
    | Sum.inl d, Sum.inl d' => d = d'
    | Sum.inr p, Sum.inr q => R p.1 q.1 ∧ p.2 = q.2
    | _, _ => False

@[simp] theorem Fmap_ll {c c' : RelSet.{0}} (R : c ⟶ c') (d d' : DigitPos) :
    Fmap R (Sum.inl d) (Sum.inl d') = (d = d') := rfl
@[simp] theorem Fmap_rr {c c' : RelSet.{0}} (R : c ⟶ c') (p : c.carrier × Digit)
    (q : c'.carrier × Digit) :
    Fmap R (Sum.inr p) (Sum.inr q) = (R p.1 q.1 ∧ p.2 = q.2) := rfl
@[simp] theorem Fmap_lr {c c' : RelSet.{0}} (R : c ⟶ c') (d : DigitPos) (q : c'.carrier × Digit) :
    Fmap R (Sum.inl d) (Sum.inr q) = False := rfl
@[simp] theorem Fmap_rl {c c' : RelSet.{0}} (R : c ⟶ c') (p : c.carrier × Digit) (d : DigitPos) :
    Fmap R (Sum.inr p) (Sum.inl d) = False := rfl

/-- `F` is a relator (monotone functor) on `Rel(Set)`. -/
def F : Relator RelSet.{0} RelSet.{0} where
  obj := Fobj
  map := Fmap
  map_id c := hom_ext fun u v => by
    cases u <;> cases v <;> simp only [Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl, id_apply] <;> grind
  map_comp R S := hom_ext fun u v => by
    cases u with
    | inl d => cases v with
      | inl d' => exact ⟨fun h => ⟨Sum.inl d, rfl, h⟩,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw1.trans hw2
            | inr q => exact hw1.elim⟩
      | inr q => exact ⟨fun h => h.elim,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw2.elim
            | inr q' => exact hw1.elim⟩
    | inr p => cases v with
      | inl d' => exact ⟨fun h => h.elim,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw1.elim
            | inr q' => exact hw2.elim⟩
      | inr q =>
        obtain ⟨pa, pd⟩ := p; obtain ⟨qa, qd⟩ := q
        exact ⟨fun ⟨⟨m, hRm, hSm⟩, hpd⟩ => ⟨Sum.inr (m, pd), ⟨hRm, rfl⟩, ⟨hSm, hpd⟩⟩,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw1.elim
            | inr md => exact ⟨⟨md.1, hw1.1, hw2.1⟩, hw1.2.trans hw2.2⟩⟩
  map_mono {c c' R S} h := le_iff.mpr fun u v => by
    cases u <;> cases v <;> simp only [Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl] <;>
      first | exact id | exact fun hh => ⟨le_iff.mp h _ _ hh.1, hh.2⟩ | exact False.elim

/-! ## `Decimal` is the initial algebra of `F` -/

/-- The constructor map `[wrap, snoc] : F Decimal → Decimal`. -/
def con : (Fobj dDec).carrier → Decimal
  | Sum.inl d => Decimal.wrap d
  | Sum.inr p => Decimal.snoc p.1 p.2

/-- The structural fold of a decimal through an algebra `f`, defined DIRECTLY from the
    algebra-RELATION `f` (so no choice is needed to turn `f` into a function). -/
def cataFold {c : RelSet.{0}} (f : Fobj c ⟶ c) : Decimal → c.carrier → Prop
  | Decimal.wrap d => fun r => f (Sum.inl d) r
  | Decimal.snoc dec dig => fun r => ∃ r', cataFold f dec r' ∧ f (Sum.inr (r', dig)) r

@[simp] theorem cataFold_wrap {c : RelSet.{0}} (f : Fobj c ⟶ c) (d : DigitPos) (r : c.carrier) :
    cataFold f (Decimal.wrap d) r = f (Sum.inl d) r := rfl
@[simp] theorem cataFold_snoc {c : RelSet.{0}} (f : Fobj c ⟶ c) (dec : Decimal) (dig : Digit)
    (r : c.carrier) :
    cataFold f (Decimal.snoc dec dig) r = ∃ r', cataFold f dec r' ∧ f (Sum.inr (r', dig)) r := rfl

/-- Every decimal folds to at least one value: the fold is entire when `f` is. -/
theorem cataFold_total {c : RelSet.{0}} (f : Fobj c ⟶ c) (hf : Map f) :
    ∀ dec : Decimal, ∃ r, cataFold f dec r
  | Decimal.wrap d => entire_total hf.1 (Sum.inl d)
  | Decimal.snoc dec dig => by
    obtain ⟨r', hr'⟩ := cataFold_total f hf dec
    obtain ⟨r, hr⟩ := entire_total hf.1 (Sum.inr (r', dig))
    exact ⟨r, r', hr', hr⟩

/-- The fold is single-valued: it is simple when `f` is. -/
theorem cataFold_functional {c : RelSet.{0}} (f : Fobj c ⟶ c) (hf : Map f) :
    ∀ (dec : Decimal) (r r' : c.carrier), cataFold f dec r → cataFold f dec r' → r = r'
  | Decimal.wrap d, r, r', h1, h2 => simple_uniq hf.2 h1 h2
  | Decimal.snoc dec dig, r, r', h1, h2 => by
    obtain ⟨s, hs, hfs⟩ := h1
    obtain ⟨s', hs', hfs'⟩ := h2
    have hss : s = s' := cataFold_functional f hf dec s s' hs hs'
    subst hss
    exact simple_uniq hf.2 hfs hfs'

theorem cataFold_map {c : RelSet.{0}} (f : Fobj c ⟶ c) (hf : Map f) :
    Map (a := dDec) (b := c) (cataFold f) := by
  refine ⟨?_, ?_⟩
  · show dom (cataFold f) = Cat.id dDec
    apply hom_ext; intro dec dec'
    refine ⟨fun h => h.1, fun (h : dec = dec') => ⟨h, ?_⟩⟩
    subst h
    obtain ⟨r, hr⟩ := cataFold_total f hf dec
    exact ⟨r, hr, hr⟩
  · refine le_iff.mpr fun r r' h => ?_
    obtain ⟨dec, h1, h2⟩ := h
    exact cataFold_functional f hf dec r r' h1 h2

/-- The initial `F`-algebra: `Decimal` with the constructor `[wrap, snoc]`, folds as
    catamorphisms.  This is the first concrete `InitialAlgebra` instance in the repo. -/
def decInitial : InitialAlgebra F where
  t := dDec
  α := graph con
  α_map := graph_map con
  cata f _ := cataFold f
  cata_map f hf := cataFold_map f hf
  cata_comm f hf := by
    apply hom_ext; intro u r
    cases u with
    | inl d =>
      constructor
      · intro h; obtain ⟨dec, hdec, hfold⟩ := h
        have hd : dec = Decimal.wrap d := hdec; subst hd
        exact ⟨Sum.inl d, rfl, hfold⟩
      · intro h; obtain ⟨v, hv, hfv⟩ := h
        cases v with
        | inl d' => have hdd : d = d' := hv; subst hdd; exact ⟨Decimal.wrap d, rfl, hfv⟩
        | inr q => exact hv.elim
    | inr p =>
      obtain ⟨pa, pd⟩ := p
      constructor
      · intro h; obtain ⟨dec, hdec, hfold⟩ := h
        have hd : dec = Decimal.snoc pa pd := hdec; subst hd
        obtain ⟨r', hr', hfr'⟩ := hfold
        exact ⟨Sum.inr (r', pd), ⟨hr', rfl⟩, hfr'⟩
      · intro h; obtain ⟨v, hv, hfv⟩ := h
        cases v with
        | inl d' => exact hv.elim
        | inr q =>
          obtain ⟨qa, qd⟩ := q
          obtain ⟨hq1, hq2⟩ := hv
          have hpq : pd = qd := hq2
          refine ⟨Decimal.snoc pa pd, rfl, qa, hq1, ?_⟩
          rw [hpq]; exact hfv
  cata_unique f hf h hmap hcomm := by
    apply hom_ext; intro dec
    induction dec with
    | wrap d =>
      intro r
      have key := congrFun (congrFun hcomm (Sum.inl d)) r
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inl d) r := ⟨Decimal.wrap d, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, hv, hfv⟩ := hlhs
        cases v with
        | inl d' => have hdd : d = d' := hv; subst hdd; exact hfv
        | inr q => exact hv.elim
      · intro hc
        have hrhs : (F.map h ≫ f) (Sum.inl d) r := ⟨Sum.inl d, rfl, hc⟩
        rw [← key] at hrhs
        obtain ⟨dec, hdec, hh⟩ := hrhs
        have hd : dec = Decimal.wrap d := hdec; subst hd; exact hh
    | snoc dec dig ih =>
      intro r
      have key := congrFun (congrFun hcomm (Sum.inr (dec, dig))) r
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inr (dec, dig)) r := ⟨Decimal.snoc dec dig, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, hv, hfv⟩ := hlhs
        cases v with
        | inl d' => exact hv.elim
        | inr q =>
          obtain ⟨qa, qd⟩ := q
          obtain ⟨hq1, hq2⟩ := hv
          have hpq : dig = qd := hq2
          refine ⟨qa, (ih qa).mp hq1, ?_⟩
          rw [hpq]; exact hfv
      · intro hc
        obtain ⟨r', hr', hfr'⟩ := hc
        have hrhs : (F.map h ≫ f) (Sum.inr (dec, dig)) r :=
          ⟨Sum.inr (r', dig), ⟨(ih r').mpr hr', rfl⟩, hfr'⟩
        rw [← key] at hrhs
        obtain ⟨d', hd', hh⟩ := hrhs
        have hd : d' = Decimal.snoc dec dig := hd'; subst hd; exact hh

/-! ## §6.1 headline: the recursive equation for the converse of a catamorphism

  Book p.138 derives, for `val = ⦇[embed, op]⦈`,
    `val° = (wrap·embed°) ∪ (snoc·(val°×id)·op°)`.
  We prove the general form for ANY algebra `φ = [g, h]` on `F`: the converse of the fold
  satisfies exactly this recursion.  Mirrored to diagram order, `wrap·embed°` becomes
  `embed° ≫ wrap` and `snoc·(val°×id)·op°` becomes `op° ≫ (val° ×× id) ≫ snoc`.  This is the
  point-free "expand the catamorphism, converse it, split the coproduct" derivation of §6.1. -/

/-- The catamorphism (fold) of `φ` as a genuine morphism `dDec ⟶ c`. -/
def cataR {c : RelSet.{0}} (φ : Fobj c ⟶ c) : dDec ⟶ c := cataFold φ

/-- The `wrap`-component `embed` of an algebra `φ = [g, h]` (its restriction to `Digit⁺`). -/
def algWrap {c : RelSet.{0}} (φ : Fobj c ⟶ c) : dDigitPos ⟶ c := fun d r => φ (Sum.inl d) r
/-- The `snoc`-component `op` of an algebra `φ = [g, h]` (its restriction to `A × Digit`). -/
def algSnoc {c : RelSet.{0}} (φ : Fobj c ⟶ c) : (⟨c.carrier × Digit⟩ : RelSet.{0}) ⟶ c :=
  fun p r => φ (Sum.inr p) r

/-- The constructor `wrap` as a relation. -/
def wrapR : dDigitPos ⟶ dDec := graph Decimal.wrap
/-- The constructor `snoc` as a relation. -/
def snocR : (⟨Decimal × Digit⟩ : RelSet.{0}) ⟶ dDec := graph (fun p => Decimal.snoc p.1 p.2)

/-- The product action `R × S` in `Rel(Set)`: `(x,y) ~ (x',y')` iff `R x x'` and `S y y'`. -/
def rprodMap {a a' b b' : RelSet.{0}} (R : a ⟶ a') (S : b ⟶ b') :
    (⟨a.carrier × b.carrier⟩ : RelSet.{0}) ⟶ ⟨a'.carrier × b'.carrier⟩ :=
  fun p q => R p.1 q.1 ∧ S p.2 q.2

/-- **§6.1 (B&dM p.138)**: the converse of a catamorphism satisfies the recursive equation
    `val° = (wrap·embed°) ∪ (snoc·(val°×id)·op°)` (mirrored), for any algebra `φ = [embed, op]`.
    Instantiating `φ := [embed, op]` gives Freyd/B&dM's `val°` recursion verbatim. -/
theorem cata_converse_eq {c : RelSet.{0}} (φ : Fobj c ⟶ c) :
    (cataR φ)° = (algWrap φ)° ≫ wrapR
      ∪ (algSnoc φ)° ≫ rprodMap (cataR φ)° (Cat.id dDigit) ≫ snocR := by
  apply hom_ext; intro r dec
  cases dec with
  | wrap d =>
    constructor
    · intro h
      exact Or.inl ⟨d, h, rfl⟩
    · intro h
      cases h with
      | inl h =>
        obtain ⟨e, he, hde⟩ := h
        have hd : d = e := Decimal.wrap.inj hde
        rw [hd]; exact he
      | inr h =>
        obtain ⟨p, hp, q, hq, hsnoc⟩ := h
        exact Decimal.noConfusion hsnoc
  | snoc dec dig =>
    constructor
    · intro h
      obtain ⟨r', hr', hφ⟩ := h
      exact Or.inr ⟨(r', dig), hφ, (dec, dig), ⟨hr', rfl⟩, rfl⟩
    · intro h
      cases h with
      | inl h =>
        obtain ⟨e, he, hde⟩ := h
        exact Decimal.noConfusion hde
      | inr h =>
        obtain ⟨p, hp, q, hq, hsnoc⟩ := h
        obtain ⟨pa, pd⟩ := p
        obtain ⟨qa, qd⟩ := q
        obtain ⟨hcata, hpq⟩ := hq
        obtain ⟨hda, hdd⟩ := Decimal.snoc.inj hsnoc
        refine ⟨pa, ?_, ?_⟩
        · rw [hda]; exact hcata
        · have hpd : pd = dig := hpq.trans hdd.symm
          rw [hpd] at hp; exact hp

/-! ## The `val`uation catamorphism and its recursion (book p.138)

  `embed d = d` includes a nonzero digit as a number; `op (n, d) = 10·n + d`.  `val = ⦇[embed,
  op]⦈ : Decimal → ℕ` reads a decimal representation as a number.  (The book works in `ℕ⁺`; the
  positivity of the result is a side condition irrelevant to the recursion, so we land in `ℕ`.) -/

/-- The codomain object: the natural numbers. -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-- The underlying function of the algebra `[embed, op]`: `inl d ↦ d`, `inr (n, dig) ↦ 10n + dig`. -/
def con_eo : (Fobj dNat).carrier → Nat
  | Sum.inl d => d.1.val
  | Sum.inr p => 10 * p.1 + p.2.val

/-- The algebra `[embed, op] : F ℕ → ℕ` of book p.138 (a map — the graph of `con_eo`). -/
def algEO : Fobj dNat ⟶ dNat := graph con_eo

/-- `val : Decimal → ℕ`, the reading catamorphism `⦇[embed, op]⦈`. -/
def val : dDec ⟶ dNat := cataR algEO

/-- **§6.1 (B&dM p.138)** for the actual valuation: `val°` satisfies the recursive equation
    `val° = (wrap·embed°) ∪ (snoc·(val°×id)·op°)` — a direct instance of `cata_converse_eq`. -/
theorem val_converse_eq :
    val° = (algWrap algEO)° ≫ wrapR
      ∪ (algSnoc algEO)° ≫ rprodMap val° (Cat.id dDigit) ≫ snocR :=
  cata_converse_eq algEO

end Freyd.Alg.RelSet.Digits
