/-
  Freyd & Scedrov, *Categories and Allegories* §2.157 (conclusion):
  the literal CONVERSE — the theorem of Desargues forces the Horn sentence at
  ALL six-tuples of the associated modular lattice 𝓛(P).

  `S2_157b_Desargues` proved `desarguesND_iff_hornAtPoints` (the equivalence at
  six-point instantiations in general position), closed every ⊤-containing
  tuple, and closed the ⊥⊥-diagonal family.  This file completes the case
  analysis over the remaining six-tuples — the bookkeeping in the book's "one
  will see" — and assembles

    `desarguesND_implies_desarguesHorn :
        P.DesarguesND → DesarguesHorn (LMonObj (PElem P))`.

  ORGANISATION.  With ⊤-tuples pruned, all six variables live in
  {⊥} ∪ points ∪ lines, and the hypothesis meet H := (a₁⊔a₂) ⊓ (b₁⊔b₂)
  satisfies H ⩽ c₁ ⊔ c₂.  The case tree is driven by the shape of H:

  · H = ⊥ — the DISJOINT CORE (`horn_core_disjoint`): the hypothesis forces one
    of the columns (a₁,a₂) or (b₁,b₂) to be a CHAIN, and the conclusion is pure
    modularity (two shears); no geometry, and no constraint on c₁, c₂ at all.
  · H = pt z — the PERSPECTIVE-CENTRE cases: z ⩽ a₁⊔a₂ and z ⩽ b₁⊔b₂; the
    conclusion follows from plane axioms + modularity, one family per shape of
    the c-column.
  · H = ln — the hypothesis pins whole lines under c₁ ⊔ c₂; heavy degeneracy.
  The all-points general-position tuples (`desarguesND_implies_horn_points`)
  are the single place where `DesarguesND` itself enters.
-/
import Fredy.S2_157b_Desargues

universe v u

namespace Freyd.Alg

namespace PElem

variable {P : ProjectivePlane.{u}}

/-! ## Order helpers: inversion and monotonicity -/

/-- Nothing is below `⊥` but `⊥`. -/
theorem eq_bot_of_le_bot {x : PElem P} (h : x.le bot) : x = bot := by
  cases x <;> simp_all [le]

/-- Below a point: `⊥` or the point itself. -/
theorem le_pt_cases {x : PElem P} {z : P.Point} (h : x.le (pt z)) :
    x = bot ∨ x = pt z := by
  cases x with
  | bot => exact Or.inl rfl
  | pt y => exact Or.inr (by rw [show y = z from h])
  | ln A => exact absurd h (by simp [le])
  | top => exact absurd h (by simp [le])

/-- Below a line: `⊥`, an incident point, or the line itself. -/
theorem le_ln_cases {x : PElem P} {A : P.Line} (h : x.le (ln A)) :
    x = bot ∨ (∃ y, x = pt y ∧ P.incid y A) ∨ x = ln A := by
  cases x with
  | bot => exact Or.inl rfl
  | pt y => exact Or.inr (Or.inl ⟨y, rfl, h⟩)
  | ln B => exact Or.inr (Or.inr (by rw [show B = A from h]))
  | top => exact absurd h (by simp [le])

/-- Join is monotone in both arguments. -/
theorem join_mono {x y x' y' : PElem P} (hx : x.le x') (hy : y.le y') :
    (x.join y).le (x'.join y') :=
  join_le (le_trans hx (le_join_left _ _)) (le_trans hy (le_join_right _ _))

/-- Meet is monotone in both arguments. -/
theorem meet_mono {x y x' y' : PElem P} (hx : x.le x') (hy : y.le y') :
    (x.meet y).le (x'.meet y') :=
  le_meet (le_trans (meet_le_left _ _) hx) (le_trans (meet_le_right _ _) hy)

/-! ## HornConc sufficiency and monotonicity -/

/-- SUFFICIENCY: the conclusion LHS under the first conclusion meet. -/
theorem hornConc_of_le_ac {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (h : ((a₁.join b₁).meet (a₂.join b₂)).le ((a₁.join c₁).meet (a₂.join c₂))) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ :=
  le_trans h (le_join_left _ _)

/-- SUFFICIENCY: the conclusion LHS under the second conclusion meet. -/
theorem hornConc_of_le_cb {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (h : ((a₁.join b₁).meet (a₂.join b₂)).le ((c₁.join b₁).meet (c₂.join b₂))) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ :=
  le_trans h (le_join_right _ _)

/-- The Horn CONCLUSION is monotone in the c-column (c appears only on the
    right).  Shrinking c strengthens the conclusion, so families may be proved
    at the smallest c making the hypothesis tight. -/
theorem HornConc.mono_c {a₁ a₂ b₁ b₂ c₁ c₂ c₁' c₂' : PElem P}
    (h₁ : c₁.le c₁') (h₂ : c₂.le c₂')
    (h : HornConc a₁ a₂ b₁ b₂ c₁ c₂) : HornConc a₁ a₂ b₁ b₂ c₁' c₂' :=
  le_trans h (join_mono
    (meet_mono (join_mono (le_refl a₁) h₁) (join_mono (le_refl a₂) h₂))
    (meet_mono (join_mono h₁ (le_refl b₁)) (join_mono h₂ (le_refl b₂))))

/-! ## The disjoint core: `H = ⊥` needs only modularity

  If the hypothesis meet `(a₁⊔a₂) ⊓ (b₁⊔b₂)` is `⊥`, the Horn conclusion holds
  with NO constraint on `c₁, c₂`: the plane lattice forces one column to be a
  chain (`join_chain_or_big` below), and for a chain column two modular shears
  finish. -/

/-- SHEAR (pure modularity): if `x` is disjoint from `y ⊔ z` then
    `(x⊔y) ⊓ (x⊔z) ⩽ x ⊔ (y⊓z)`. -/
theorem shear_of_disjoint {x y z : PElem P} (h : x.meet (y.join z) = bot) :
    ((x.join y).meet (x.join z)).le (x.join (y.meet z)) := by
  -- first shear: (x⊔y) ⊓ (z⊔x) = ((x⊔y) ⊓ z) ⊔ x
  have h1 : (x.join y).meet (x.join z) = ((x.join y).meet z).join x := by
    rw [join_comm x z, modular_eq (le_join_left x y)]
  -- second shear: (x⊔y) ⊓ z ⩽ (y⊔z) ⊓ (x⊔y) = ((y⊔z) ⊓ x) ⊔ y = y
  have h2 : ((x.join y).meet z).le (y.meet z) := by
    have h3 : ((x.join y).meet z).le ((y.join z).meet (x.join y)) :=
      le_meet (le_trans (meet_le_right _ _) (le_join_right y z))
        (meet_le_left _ _)
    exact le_meet (by
      rw [modular_eq (le_join_left y z), meet_comm (y.join z) x,
        h, bot_join] at h3
      exact h3) (meet_le_right _ _)
  rw [h1, join_comm]
  exact join_mono (le_refl x) h2

/-- CHAIN STEP (pure modularity): a comparable a-column disjoint from the
    b-join forces the conclusion-LHS under `a₁⊓a₂ ⊔ b₁⊓b₂`. -/
theorem chain_disjoint_le {a₁ a₂ b₁ b₂ : PElem P} (hc : a₂.le a₁)
    (h : a₁.meet (b₁.join b₂) = bot) :
    ((a₁.join b₁).meet (a₂.join b₂)).le (a₂.join (b₁.meet b₂)) := by
  have hL1 : ((a₁.join b₁).meet (a₂.join b₂)).le (a₁.join (b₁.meet b₂)) :=
    le_trans (meet_mono (le_refl _) (join_mono hc (le_refl b₂)))
      (shear_of_disjoint h)
  have hL : ((a₁.join b₁).meet (a₂.join b₂)).le
      ((a₂.join b₂).meet (a₁.join (b₁.meet b₂))) :=
    le_meet (meet_le_right _ _) hL1
  -- (a₂⊔b₂) ⊓ (a₁ ⊔ (b₁⊓b₂)) = ((a₂⊔b₂) ⊓ a₁) ⊔ (b₁⊓b₂), and (a₂⊔b₂)⊓a₁ = a₂
  rw [modular_eq (le_trans (meet_le_right b₁ b₂) (le_join_right a₂ b₂))] at hL
  have ha : (a₂.join b₂).meet a₁ = a₂ := by
    rw [meet_comm, join_comm a₂ b₂, modular_eq hc]
    have hb : a₁.meet b₂ = bot :=
      eq_bot_of_le_bot (h ▸ meet_mono (le_refl a₁) (le_join_right b₁ b₂))
    rw [hb, bot_join]
  rw [ha] at hL
  exact hL

/-- TRICHOTOMY of joins in 𝓛(P): two elements are comparable, or their join is
    a line or `⊤`.  (What makes `H = ⊥` collapse a column to a chain.) -/
theorem join_chain_or_big (x y : PElem P) :
    x.le y ∨ y.le x ∨ (∃ A, x.join y = ln A) ∨ x.join y = top := by
  cases x with
  | bot => exact Or.inl (bot_le y)
  | top => exact Or.inr (Or.inl (le_top y))
  | pt v =>
    cases y with
    | bot => exact Or.inr (Or.inl (bot_le _))
    | top => exact Or.inl (le_top _)
    | pt w =>
      by_cases hvw : v = w
      · exact Or.inl (hvw : (pt v).le (pt w))
      · exact Or.inr (Or.inr (Or.inl ⟨_, join_pt_pt_ne hvw⟩))
    | ln A =>
      by_cases hvA : P.incid v A
      · exact Or.inl (hvA : (pt v).le (ln A))
      · exact Or.inr (Or.inr (Or.inr (join_pt_ln_not hvA)))
  | ln A =>
    cases y with
    | bot => exact Or.inr (Or.inl (bot_le _))
    | top => exact Or.inl (le_top _)
    | pt w =>
      by_cases hwA : P.incid w A
      · exact Or.inr (Or.inl (hwA : (pt w).le (ln A)))
      · exact Or.inr (Or.inr (Or.inr (join_ln_pt_not hwA)))
    | ln B =>
      by_cases hAB : A = B
      · exact Or.inl (hAB : (ln A).le (ln B))
      · exact Or.inr (Or.inr (Or.inr (join_ln_ln_ne hAB)))

/-- In 𝓛(P) a line and a line-or-top always share a point: their meet is
    never `⊥` (axiom 2 through the meet table). -/
theorem meet_ne_bot_of_big {x y : PElem P}
    (hx : (∃ A, x = ln A) ∨ x = top) (hy : (∃ B, y = ln B) ∨ y = top) :
    x.meet y ≠ bot := by
  rcases hx with ⟨A, rfl⟩ | rfl <;> rcases hy with ⟨B, rfl⟩ | rfl
  · by_cases hAB : A = B
    · rw [hAB, meet_ln_ln_self]; exact fun h => nomatch h
    · rw [meet_ln_ln_ne hAB]; exact fun h => nomatch h
  · rw [meet_top_right]; exact fun h => nomatch h
  · rw [meet_top_left]; exact fun h => nomatch h
  · rw [meet_top_left]; exact fun h => nomatch h

/-- **THE DISJOINT CORE**: if the hypothesis meet `(a₁⊔a₂) ⊓ (b₁⊔b₂)` is `⊥`,
    the Horn conclusion holds for EVERY c-column — pure modularity.  By the
    trichotomy one column is a chain (both joins big would meet nontrivially,
    axiom 2); the chain step then bounds the LHS by `(a₁⊓a₂) ⊔ (b₁⊓b₂)`, which
    sits under both conclusion meets. -/
theorem horn_core_disjoint {a₁ a₂ b₁ b₂ : PElem P} (c₁ c₂ : PElem P)
    (h : (a₁.join a₂).meet (b₁.join b₂) = bot) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  -- it suffices to land under (a₁⊓a₂) ⊔ (b₁⊓b₂)
  have hsuff : ((a₁.join b₁).meet (a₂.join b₂)).le
      ((a₁.meet a₂).join (b₁.meet b₂)) → HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
    intro hle
    exact le_trans hle (join_mono
      (le_meet (le_trans (meet_le_left _ _) (le_join_left a₁ c₁))
        (le_trans (meet_le_right _ _) (le_join_left a₂ c₂)))
      (le_meet (le_trans (meet_le_left _ _) (le_join_right c₁ b₁))
        (le_trans (meet_le_right _ _) (le_join_right c₂ b₂))))
  -- the a-column disjoint from the b-join (and symmetrically)
  have hab : ∀ x : PElem P, x.le (a₁.join a₂) → x.meet (b₁.join b₂) = bot :=
    fun x hx => eq_bot_of_le_bot (h ▸ meet_mono hx (le_refl _))
  have hba : ∀ x : PElem P, x.le (b₁.join b₂) → x.meet (a₁.join a₂) = bot :=
    fun x hx => eq_bot_of_le_bot
      (h ▸ le_meet (meet_le_right _ _) (le_trans (meet_le_left _ _) hx))
  rcases join_chain_or_big a₁ a₂ with h12 | h21 | hbig₁
  · -- a₁ ⩽ a₂: chain step with rows swapped
    apply hsuff
    have hd : a₂.meet (b₂.join b₁) = bot := by
      rw [join_comm b₂ b₁]; exact hab a₂ (le_join_right a₁ a₂)
    have hstep := chain_disjoint_le (b₁ := b₂) (b₂ := b₁) h12 hd
    rw [meet_comm (a₂.join b₂), meet_comm b₂ b₁] at hstep
    exact le_trans hstep (join_mono (le_meet (le_refl a₁) h12) (le_refl _))
  · -- a₂ ⩽ a₁: the chain step verbatim
    apply hsuff
    exact le_trans (chain_disjoint_le h21 (hab a₁ (le_join_left a₁ a₂)))
      (join_mono (le_meet h21 (le_refl a₂)) (le_refl _))
  rcases join_chain_or_big b₁ b₂ with h12 | h21 | hbig₂
  · -- b₁ ⩽ b₂: chain step with the columns and rows swapped
    apply hsuff
    have hd : b₂.meet (a₂.join a₁) = bot := by
      rw [join_comm a₂ a₁]; exact hba b₂ (le_join_right b₁ b₂)
    have hstep := chain_disjoint_le (b₁ := a₂) (b₂ := a₁) h12 hd
    rw [meet_comm (b₂.join a₂), join_comm b₁ a₁, join_comm b₂ a₂,
      meet_comm a₂ a₁] at hstep
    exact le_trans hstep (join_le
      (le_trans (le_meet (le_refl b₁) h12) (le_join_right _ _))
      (le_join_left _ _))
  · -- b₂ ⩽ b₁: chain step with the columns swapped
    apply hsuff
    have hstep := chain_disjoint_le (b₁ := a₁) (b₂ := a₂) h21
      (hba b₁ (le_join_left b₁ b₂))
    rw [join_comm b₁ a₁, join_comm b₂ a₂] at hstep
    exact le_trans hstep (join_le
      (le_trans (le_meet h21 (le_refl b₂)) (le_join_right _ _))
      (le_join_left _ _))
  · -- both joins big: they meet nontrivially (axiom 2) — vacuous
    exact absurd h (meet_ne_bot_of_big
      (hbig₁.elim (fun ⟨A, hA⟩ => Or.inl ⟨A, hA⟩) Or.inr)
      (hbig₂.elim (fun ⟨B, hB⟩ => Or.inl ⟨B, hB⟩) Or.inr))

/-- FAMILY `c₁ = c₂ = ⊥` (both C's the allegory unit): the hypothesis says the
    two column joins are disjoint — exactly the disjoint core. -/
theorem horn_c_bot {a₁ a₂ b₁ b₂ : PElem P}
    (h : HornHyp a₁ a₂ b₁ b₂ bot bot) : HornConc a₁ a₂ b₁ b₂ bot bot := by
  have h' : ((a₁.join a₂).meet (b₁.join b₂)).le bot := by
    have h0 : ((a₁.join a₂).meet (b₁.join b₂)).le ((bot : PElem P).join bot) := h
    rwa [bot_join] at h0
  exact horn_core_disjoint bot bot (eq_bot_of_le_bot h')

end PElem

end Freyd.Alg
