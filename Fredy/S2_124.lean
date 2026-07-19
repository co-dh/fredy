/-
  Freyd & Scedrov, *Categories and Allegories* §2.124 — the string-diagram proof, checked in Lean.

  The companion note `Fredy/S2_124.typ` proves  `Dom(R ∩ S) = 1 ∩ S R°`  graphically: it rewrites BOTH
  sides, with the special-Frobenius axioms, to one normal form  `W = Δ³;(1⊗R⊗S);(1⊗cap)`.  That proof
  rests on three identities.  This file works in the concrete category `Rel` of relations,
  `Rel A B := A → B → Prop`, composition in DIAGRAM order (the book's `x y`), so that `Dom P = 1∩PP°`
  matches Freyd §2.122.  It does two things:

  1. §"AXIOMS" — states the axioms of the calculus (special commutative Frobenius (co)monoid on each
     object + converse + the monoidal-category laws) as theorems, i.e. PROVES that `Rel` is a model of
     them.  This is what the note draws.  Two of them (`coassoc`, `frobenius`) carry an explicit
     associator `assocLR` because `Prod` is not strictly associative — the coherence maps that string
     diagrams silently suppress.  One extra law, `adequacy` (`Δ;(R⊗R);∇ = R`), is the *relational* fact
     beyond bare Frobenius that Lemma 1 needs (it fails in a general hypergraph category).

  2. §"LEMMAS" — the three identities the graphical proof uses, and §2.124 itself, for ARBITRARY
     relations `R S : Rel A B`:
         Lemma 1 `dom_cd`        `Dom P = Δ;(1⊗P);keepFst`
         Lemma 2 `cv_merge`      `(1⊗P°);∇ = (Δ⊗1);((1⊗P)⊗1);capKeep`
         §2.124  `dom_inter_rel` `1 ∩ S R° = Dom(R∩S) = W`

  These are verified in `Rel`, which (by the §"AXIOMS" theorems) is a model of the calculus; the
  graphical calculus is sound AND complete for `Rel`, so "holds in `Rel`" is equivalent to "derivable
  from these axioms".  We do NOT use the modular law anywhere — the abstract, allegory-level §2.124
  (which does use the modular law) is `Fredy.S2_1.dom_inter`.  A purely point-free Lean *derivation*
  from the axioms would additionally need the monoidal-coherence lemmas (associator/unitor naturality)
  as rewrite steps — the bookkeeping string diagrams suppress; that infrastructure is not built here.

  Mathlib-free: no imports, Lean-core tactics only.
-/

namespace Fredy.S2_124

/-- A relation `A → B`. -/
def Rel (A B : Type) : Type := A → B → Prop

variable {A B C D E F : Type}

/-- Composition in diagram order: `(comp R S) a c` iff some `b` has `a R b` and `b S c`. -/
def comp (R : Rel A B) (S : Rel B C) : Rel A C := fun a c => ∃ b, R a b ∧ S b c
/-- Identity relation `1 = {(a,a)}`. -/
def idr (A : Type) : Rel A A := fun a a' => a = a'
/-- Converse `R°`: `b R° a` iff `a R b`. -/
def conv (R : Rel A B) : Rel B A := fun b a => R a b
/-- Meet `R ∩ S`. -/
def meet (R S : Rel A B) : Rel A B := fun a b => R a b ∧ S a b
/-- Monoidal product `R ⊗ S` on product objects. -/
def tens (R : Rel A B) (S : Rel C D) : Rel (A × C) (B × D) := fun p q => R p.1 q.1 ∧ S p.2 q.2

-- The special commutative Frobenius (co)monoid on an object `A`.
/-- copy  `Δ : A → A × A`. -/
def delta (A : Type) : Rel A (A × A) := fun a p => a = p.1 ∧ a = p.2
/-- merge `∇ : A × A → A`. -/
def nabla (A : Type) : Rel (A × A) A := fun p a => p.1 = a ∧ p.2 = a
/-- discard `! : A → Unit`. -/
def bang (A : Type) : Rel A Unit := fun _ _ => True
/-- unit `? : Unit → A` — the converse of discard; a wire created from nothing. -/
def unitR (A : Type) : Rel Unit A := fun _ _ => True
/-- cap `= ∇ ; ! : A × A → Unit` — force the two inputs equal, then vanish. -/
def cap (A : Type) : Rel (A × A) Unit := fun p _ => p.1 = p.2
/-- wire swap `σ : A × B → B × A`. -/
def swp (A B : Type) : Rel (A × B) (B × A) := fun p q => p.1 = q.2 ∧ p.2 = q.1

-- Monoidal coherence maps.  String diagrams suppress these; we keep them explicit, and the two
-- "collapsed" maps below (`keepFst`, `capKeep`) are proved equal to the honest generator composites
-- in `keepFst_eq` / `capKeep_eq`.
/-- right unitor `ρ : A × Unit → A`. -/
def ru (A : Type) : Rel (A × Unit) A := fun p a => p.1 = a
/-- associator `α : (A × B) × C → A × (B × C)`. -/
def assocLR (A B C : Type) : Rel ((A × B) × C) (A × (B × C)) :=
  fun p q => p.1.1 = q.1 ∧ p.1.2 = q.2.1 ∧ p.2 = q.2.2
/-- `keepFst = (1 ⊗ !) ; ρ : A × B → A` — keep the first wire, existentially forget the second. -/
def keepFst (A B : Type) : Rel (A × B) A := fun p a => p.1 = a
/-- `capKeep = α ; (1 ⊗ cap) ; ρ : (A × B) × B → A` — keep the first wire, cap the two `b`-wires. -/
def capKeep (A B : Type) : Rel ((A × B) × B) A := fun p a => p.1.1 = a ∧ p.1.2 = p.2

/-- DOMAIN, Freyd §2.122:  `Dom R = 1 ∩ R R°`. -/
def Dom (R : Rel A B) : Rel A A := meet (idr A) (comp R (conv R))

/-- The normal form the diagrammatic proof drives both sides to:
    `W = Δ³ ; (1 ⊗ R ⊗ S) ; (1 ⊗ cap)`   (`Δ³ = Δ ; (Δ ⊗ 1)`). -/
def W (R S : Rel A B) : Rel A A :=
  comp (comp (comp (delta A) (tens (delta A) (idr A))) (tens (tens (idr A) R) S)) (capKeep A B)

/-! ## AXIOMS OF THE CALCULUS — `Rel` is a model.
    The equations the note lists in "§ The axioms of the calculus", each verified for `Rel`. -/

-- Monoidal-category laws (with converse).
theorem comp_assoc (R : Rel A B) (S : Rel B C) (T : Rel C D) :
    comp (comp R S) T = comp R (comp S T) := by
  funext a d; apply propext; simp only [comp]; grind
theorem id_comp (R : Rel A B) : comp (idr A) R = R := by
  funext a b; apply propext; simp only [comp, idr]; grind
theorem comp_id (R : Rel A B) : comp R (idr B) = R := by
  funext a b; apply propext; simp only [comp, idr]; grind
theorem tens_comp (R : Rel A B) (S : Rel B C) (R' : Rel D E) (S' : Rel E F) :
    comp (tens R R') (tens S S') = tens (comp R S) (comp R' S') := by
  funext a c; apply propext; simp only [comp, tens, Prod.exists]; grind
theorem tens_id : tens (idr A) (idr B) = idr (A × B) := by
  funext a b; apply propext; simp only [tens, idr]; grind

-- Special commutative Frobenius (co)monoid.
/-- special: `Δ ; ∇ = 1`. -/
theorem special : comp (delta A) (nabla A) = idr A := by
  funext a b; apply propext; simp only [comp, delta, nabla, idr, Prod.exists]; grind
/-- cocommutative: `Δ ; σ = Δ`. -/
theorem cocomm : comp (delta A) (swp A A) = delta A := by
  funext a p; apply propext; simp only [comp, delta, swp, Prod.exists]; grind
/-- counit: `Δ ; (1 ⊗ !) ; ρ = 1`. -/
theorem counit : comp (comp (delta A) (tens (idr A) (bang A))) (ru A) = idr A := by
  funext a b; apply propext; simp only [comp, delta, tens, idr, bang, ru, Prod.exists]; grind
/-- coassociative (up to the associator `α`): `Δ ; (Δ ⊗ 1) = Δ ; (1 ⊗ Δ) ; α°`. -/
theorem coassoc :
    comp (delta A) (tens (delta A) (idr A))
      = comp (comp (delta A) (tens (idr A) (delta A))) (conv (assocLR A A A)) := by
  funext a p; apply propext; simp only [comp, delta, tens, idr, conv, assocLR, Prod.exists]; grind
/-- Frobenius (through the associator): `(Δ ⊗ 1) ; α ; (1 ⊗ ∇) = ∇ ; Δ`. -/
theorem frobenius :
    comp (tens (delta A) (idr A)) (comp (assocLR A A A) (tens (idr A) (nabla A)))
      = comp (nabla A) (delta A) := by
  funext p q; apply propext; simp only [comp, tens, delta, nabla, idr, assocLR, Prod.exists]; grind
/-- cap is merge-then-discard: `cap = ∇ ; !`. -/
theorem cap_def : cap A = comp (nabla A) (bang A) := by
  funext p u; apply propext; simp only [cap, comp, nabla, bang]; grind

-- Converse is an involutive contravariant functor fixing the structure.
theorem conv_comp (R : Rel A B) (S : Rel B C) : conv (comp R S) = comp (conv S) (conv R) := by
  funext c a; apply propext; simp only [conv, comp]; grind
theorem conv_conv (R : Rel A B) : conv (conv R) = R := rfl
theorem conv_delta : conv (delta A) = nabla A := by
  funext p a; apply propext; exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
theorem conv_bang : conv (bang A) = unitR A := rfl
theorem conv_tens (R : Rel A B) (S : Rel C D) : conv (tens R S) = tens (conv R) (conv S) := rfl
theorem conv_meet (R S : Rel A B) : conv (meet R S) = meet (conv R) (conv S) := rfl

/-- Diagrammatic definition of `∩`:  `R ∩ S = Δ ; (R ⊗ S) ; ∇`. -/
theorem meet_eq (R S : Rel A B) : meet R S = comp (comp (delta A) (tens R S)) (nabla B) := by
  funext a b; apply propext; simp only [meet, comp, delta, tens, nabla, Prod.exists]; grind

/-- The RELATIONAL adequacy law beyond bare Frobenius (it fails in a general hypergraph category, holds
    in `Rel`):  copying, running `R` on both copies and re-merging is just `R`,  `Δ ; (R ⊗ R) ; ∇ = R`.
    This is what makes the two `P`'s in `Dom P = 1∩PP°` collapse to the single `P` of Lemma 1. -/
theorem adequacy (R : Rel A B) : comp (comp (delta A) (tens R R)) (nabla B) = R := by
  funext a b; apply propext; simp only [comp, delta, tens, nabla, Prod.exists]; grind

/-! ## The collapsed coherence maps are the honest generator composites -/

theorem keepFst_eq (A B : Type) : keepFst A B = comp (tens (idr A) (bang B)) (ru A) := by
  funext p a; apply propext; simp only [keepFst, comp, tens, idr, bang, ru, Prod.exists]; grind

theorem capKeep_eq (A B : Type) :
    capKeep A B = comp (comp (assocLR A B B) (tens (idr A) (cap B))) (ru A) := by
  funext p a; apply propext; simp only [capKeep, comp, tens, idr, cap, ru, assocLR, Prod.exists]; grind

/-! ## LEMMAS — the three identities the graphical proof rests on, and §2.124.
    Verified in `Rel`; by the §AXIOMS theorems `Rel` is a model of the calculus, and the calculus is
    complete for `Rel`, so these are exactly its theorems.  No modular law is used. -/

/-- **Lemma 1.** `Dom P = Δ ; (1 ⊗ P) ; keepFst`.  (The `1∩PP°` form has two copies of `P`; this one
    has a single `P` whose output is discarded — the collapse is `adequacy`.  Both are `{(a,a):∃b.aPb}`.) -/
theorem dom_cd (P : Rel A B) :
    Dom P = comp (comp (delta A) (tens (idr A) P)) (keepFst A B) := by
  funext a a'; apply propext
  simp only [Dom, meet, idr, comp, conv, tens, delta, keepFst, Prod.exists]
  grind

/-- **Lemma 2.** `(1 ⊗ P°) ; ∇ = (Δ ⊗ 1) ; ((1 ⊗ P) ⊗ 1) ; capKeep`.  The move that turns `S R°` into a
    witness: copy the surviving wire, run `P` forward, cap its output against the incoming one. -/
theorem cv_merge (P : Rel A B) :
    comp (tens (idr A) (conv P)) (nabla A)
      = comp (comp (tens (delta A) (idr B)) (tens (tens (idr A) P) (idr B))) (capKeep A B) := by
  funext p a; apply propext
  simp only [comp, tens, idr, conv, nabla, delta, capKeep, Prod.exists]
  grind

/-- Right side: `Dom (R ∩ S) = W`. -/
theorem right_eq_W (R S : Rel A B) : Dom (meet R S) = W R S := by
  funext a a'; apply propext
  simp only [Dom, W, meet, idr, comp, conv, tens, delta, capKeep, Prod.exists]
  grind

/-- Left side: `1 ∩ S R° = W`. -/
theorem left_eq_W (R S : Rel A B) : meet (idr A) (comp S (conv R)) = W R S := by
  funext a a'; apply propext
  simp only [meet, W, idr, comp, conv, tens, delta, capKeep, Prod.exists]
  grind

/-- **§2.124 in `Rel`.**  `1 ∩ S R° = Dom (R ∩ S)`, obtained by driving both sides to the normal form
    `W`.  (Abstract allegory version, via the modular law: `Fredy.S2_1.dom_inter`.) -/
theorem dom_inter_rel (R S : Rel A B) : meet (idr A) (comp S (conv R)) = Dom (meet R S) :=
  (left_eq_W R S).trans (right_eq_W R S).symm

/-- For the record, the shared normal form as an explicit predicate:
    `W R S a a' ↔ a = a' ∧ ∃ b, a R b ∧ a S b`. -/
theorem W_eq (R S : Rel A B) : W R S = fun a a' => a = a' ∧ ∃ b, R a b ∧ S a b := by
  funext a a'; apply propext
  simp only [W, comp, tens, idr, delta, capKeep, Prod.exists]
  grind

end Fredy.S2_124
