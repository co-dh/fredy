/-
  The §1.426 MONIC-PAIR diagram, realized as a genuine Q-sequence whose satisfaction
  PROVABLY means `Monic (pair x y)` — the semantic counterpart of `HornToQSeq`'s
  `satisfies_qLeftInv` (§1.39 left-invertible), but for §1.41/§1.426 monicness.

  Why a sibling engine and not `S1_38b.QSeq`/`Satisfies`:  that telescope quantifies
  fillers by POST-composition (`α ≫ g = f`) with only `∀`/`∃`, and so captures the §1.39
  left-DIVISION properties.  Monicness is different in two ways the book's picture makes
  plain (§1.41):  it is a LIFT (`u ≫ m = w`, filler PRE-composed) and it is an AT-MOST-ONE
  claim (Freyd's `!` bar), which `∀`/`∃` over factorizations cannot express (the base case
  can only say `True`/`False`, never `u = u'`).  So we add exactly the `!` quantifier and the
  lift direction, keep everything else as in `S1_38b`, and prove the diagram ⇔ the property.

  Punchline (`msat_qMonicPair_iff_monicPair`):
      (the §1.426 monic Q-sequence for ⟨x,y⟩ is satisfied at every test map)
        ↔ MonicPair x y                               -- x, y is a monic pair (§1.41)
  routed through `Monic (pair x y)` via the real §1.426 theorem `monicPair_iff_monic_pair`.
-/

import Fredy.S1_42   -- Monic, MonicPair (§1.41); pair, prod, monicPair_iff_monic_pair (§1.42/§1.426)

universe v u

namespace Freyd
namespace QSeqMonic

/-- A monic-flavoured Q-sequence step quantifier: `all` = ∀, `ex` = ∃ (as in §1.395), plus
    `atMostOne` = the §1.41 AT-MOST-ONE bar (Freyd's `!`). -/
inductive MQ | all | ex | atMostOne

/-- A §1.41-style Q-sequence rooted at a fixed TEST object `W`, indexed by the current leg's
    target.  `cons q m rest` reads "along the fixed arrow `m : T ⟶ P`, quantify (`q`) a LIFT
    `u : W ⟶ T` of the current leg `W ⟶ P`, then continue with `u` as the new leg".  This is
    the lift (pre-composition) dual of `S1_38b.QSeq`. -/
inductive MSeq (𝒟 : Type u) [Cat.{v} 𝒟] (W : 𝒟) : 𝒟 → Type (max u v)
  | nil  (P : 𝒟) : MSeq 𝒟 W P
  | cons {P T : 𝒟} (q : MQ) (m : T ⟶ P) (rest : MSeq 𝒟 W T) : MSeq 𝒟 W P

variable {𝒟 : Type u} [Cat.{v} 𝒟] {W : 𝒟}

/-- Satisfaction of a monic Q-sequence by a leg `f : W ⟶ P`.  `nil` is satisfied (the leg is
    accepted); each `cons` extends the witness over the fixed arrow by a lift, quantified per
    `q` — the `atMostOne` clause is Freyd's `!`: any two lifts that both continue must agree. -/
def MSat : {P : 𝒟} → MSeq 𝒟 W P → (W ⟶ P) → Prop
  | _, .nil _,                  _ => True
  | _, .cons .all       m rest, f => ∀ u, u ≫ m = f → MSat rest u
  | _, .cons .ex        m rest, f => ∃ u, u ≫ m = f ∧ MSat rest u
  | _, .cons .atMostOne m rest, f =>
        ∀ u u', u ≫ m = f → u' ≫ m = f → MSat rest u → MSat rest u' → u = u'

@[simp] theorem msat_nil {P : 𝒟} (f : W ⟶ P) : MSat (.nil P : MSeq 𝒟 W P) f := trivial

@[simp] theorem msat_cons_atMostOne {P T : 𝒟} (m : T ⟶ P) (rest : MSeq 𝒟 W T) (f : W ⟶ P) :
    MSat (.cons .atMostOne m rest) f ↔
      ∀ u u', u ≫ m = f → u' ≫ m = f → MSat rest u → MSat rest u' → u = u' := Iff.rfl

/-- §1.41 MONIC, as a one-step Q-sequence: a single `!`-bar binding the lift `u : W ⟶ T` of a
    test leg `w : W ⟶ P` along `m`.  (Trailing `nil`, as the book customarily omits.) -/
def qMonic {T P : 𝒟} (m : T ⟶ P) : MSeq 𝒟 W P := .cons .atMostOne m (.nil T)

/-- The §1.41 monic diagram unfolds to exactly "at most one lift of `w` along `m`". -/
@[simp] theorem msat_qMonic {T P : 𝒟} (m : T ⟶ P) (w : W ⟶ P) :
    MSat (qMonic m) w ↔ ∀ u u' : W ⟶ T, u ≫ m = w → u' ≫ m = w → u = u' := by
  simp [qMonic]

/-- The whole §1.41 diagram: satisfied at every test object `W` and every test leg `w`. -/
def MonicDiag {T P : 𝒟} (m : T ⟶ P) : Prop := ∀ {W : 𝒟} (w : W ⟶ P), MSat (qMonic m) w

/-- **The monic diagram means monicness.**  The §1.41 Q-sequence `qMonic m` is satisfied at
    every test leg iff `m` is monic — the analogue of `satisfies_qLeftInv` for §1.41.
    Constructive, no choice. -/
theorem monicDiag_iff_monic {T P : 𝒟} (m : T ⟶ P) : MonicDiag m ↔ Monic m := by
  constructor
  · intro h W g g' he
    exact (msat_qMonic m (g ≫ m)).mp (h (g ≫ m)) g g' rfl he.symm
  · intro hm W w
    rw [msat_qMonic]
    exact fun u u' hu hu' => hm u u' (hu.trans hu'.symm)

variable [HasBinaryProducts 𝒟]

/-- **§1.426, the diagram form.**  The monic Q-sequence for the pairing `⟨x,y⟩ : T → A×B`
    is satisfied at every test leg iff `x, y` is a MONIC PAIR — the picture provably means the
    theorem.  Chains `monicDiag_iff_monic` with the real §1.426 `monicPair_iff_monic_pair`. -/
theorem monicDiag_pair_iff_monicPair {T A B : 𝒟} (x : T ⟶ A) (y : T ⟶ B) :
    MonicDiag (pair x y) ↔ MonicPair x y := by
  rw [monicDiag_iff_monic]; exact (monicPair_iff_monic_pair x y).symm

end QSeqMonic
end Freyd
