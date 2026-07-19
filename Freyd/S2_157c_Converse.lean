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
import Freyd.S2_157b_Desargues

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

/-! ## Chain steps: a comparable column closes `c₁ = ⊥` tuples by modularity

  For the families with `c₁ = ⊥` the hypothesis meet is `(a₁⊔a₂) ⊓ (b₁⊔b₂) ⩽
  c₂`.  When one column is a CHAIN the conclusion needs no geometry: split the
  small column element off the LHS by one modular shear, bound the remainder by
  the hypothesis with a second shear. -/

theorem join_eq_of_le_left {x y : PElem P} (h : y.le x) : x.join y = x :=
  le_antisymm (join_le (le_refl x) h) (le_join_left x y)

theorem join_eq_of_le_right {x y : PElem P} (h : x.le y) : x.join y = y :=
  le_antisymm (join_le h (le_refl y)) (le_join_right x y)

/-- CHAIN STEP, descending a-column (`a₂ ⩽ a₁`): if moreover `c₂ ⩽ a₁` and
    `a₁ ⊓ (b₁⊔b₂) ⩽ c₂`, the Horn conclusion at `c₁ = ⊥` holds. -/
theorem center_chain_step {a₁ a₂ b₁ b₂ c₂ : PElem P} (hc : a₂.le a₁)
    (hca : c₂.le a₁) (hup : (a₁.meet (b₁.join b₂)).le c₂) :
    HornConc a₁ a₂ b₁ b₂ bot c₂ := by
  show ((a₁.join b₁).meet (a₂.join b₂)).le
    (((a₁.join bot).meet (a₂.join c₂)).join
      ((PElem.bot.join b₁).meet (c₂.join b₂)))
  rw [join_bot_right a₁, bot_join b₁]
  -- split off a₂: L = ((a₁⊔b₁) ⊓ b₂) ⊔ a₂  (modularity, a₂ ⩽ a₁⊔b₁)
  have hL : (a₁.join b₁).meet (a₂.join b₂) = ((a₁.join b₁).meet b₂).join a₂ := by
    rw [join_comm a₂ b₂, modular_eq (le_trans hc (le_join_left a₁ b₁))]
  -- W := (a₁⊔b₁) ⊓ b₂ ⩽ c₂ ⊔ b₁  (second shear + the hypothesis)
  have hW1 : ((a₁.join b₁).meet b₂).le (c₂.join b₁) := by
    have h1 : ((a₁.join b₁).meet b₂).le ((b₁.join b₂).meet (a₁.join b₁)) :=
      le_meet (le_trans (meet_le_right _ _) (le_join_right b₁ b₂))
        (meet_le_left _ _)
    rw [modular_eq (le_join_left b₁ b₂), meet_comm (b₁.join b₂) a₁] at h1
    exact le_trans h1 (join_mono hup (le_refl b₁))
  -- hence W ⩽ (b₁ ⊓ (c₂⊔b₂)) ⊔ c₂  (third shear)
  have hW : ((a₁.join b₁).meet b₂).le ((b₁.meet (c₂.join b₂)).join c₂) := by
    have h2 : ((a₁.join b₁).meet b₂).le ((c₂.join b₂).meet (b₁.join c₂)) :=
      le_meet (le_trans (meet_le_right _ _) (le_join_right c₂ b₂))
        (join_comm c₂ b₁ ▸ hW1)
    rwa [modular_eq (le_join_left c₂ b₂), meet_comm (c₂.join b₂) b₁] at h2
  rw [hL]
  exact join_le
    (le_trans hW (join_le (le_join_right _ _)
      (le_trans (le_meet hca (le_join_right a₂ c₂)) (le_join_left _ _))))
    (le_trans (le_meet hc (le_join_left a₂ c₂)) (le_join_left _ _))

/-- CHAIN STEP, ascending a-column (`a₁ ⩽ a₂`): if `a₂ ⊓ (b₁⊔b₂) ⩽ c₂`, the
    Horn conclusion at `c₁ = ⊥` holds — no constraint on `c₂` at all. -/
theorem center_chain_step' {a₁ a₂ b₁ b₂ c₂ : PElem P} (hc : a₁.le a₂)
    (hup : (a₂.meet (b₁.join b₂)).le c₂) :
    HornConc a₁ a₂ b₁ b₂ bot c₂ := by
  show ((a₁.join b₁).meet (a₂.join b₂)).le
    (((a₁.join bot).meet (a₂.join c₂)).join
      ((PElem.bot.join b₁).meet (c₂.join b₂)))
  rw [join_bot_right a₁, bot_join b₁]
  -- split off a₁: L = ((a₂⊔b₂) ⊓ b₁) ⊔ a₁  (modularity, a₁ ⩽ a₂⊔b₂)
  have hL : (a₁.join b₁).meet (a₂.join b₂) = ((a₂.join b₂).meet b₁).join a₁ := by
    rw [meet_comm, join_comm a₁ b₁,
      modular_eq (le_trans hc (le_join_left a₂ b₂))]
  -- W := (a₂⊔b₂) ⊓ b₁ ⩽ b₁ ⊓ (c₂⊔b₂)  (shear + the hypothesis)
  have hW : ((a₂.join b₂).meet b₁).le (b₁.meet (c₂.join b₂)) := by
    apply le_meet (meet_le_right _ _)
    have h1 : ((a₂.join b₂).meet b₁).le ((b₁.join b₂).meet (a₂.join b₂)) :=
      le_meet (le_trans (meet_le_right _ _) (le_join_left b₁ b₂))
        (meet_le_left _ _)
    rw [modular_eq (le_join_right b₁ b₂), meet_comm (b₁.join b₂) a₂] at h1
    exact le_trans h1 (join_mono hup (le_refl b₂))
  rw [hL]
  exact join_le (le_trans hW (le_join_right _ _))
    (le_trans (le_meet (le_refl a₁) (le_trans hc (le_join_left a₂ c₂)))
      (le_join_left _ _))

/-! ## The geometric centre core: four points in two perspective lines

  The only `c₁ = ⊥`-tuples not killed by a chain column: both columns are
  distinct-point pairs spanning two DISTINCT lines, and the hypothesis pins
  `c₂` to a point `z` on both (the perspective centre).  Plane axioms close
  every position of `z`; Desargues is never needed (only five points). -/

open ProjectivePlane in
/-- Centre core: `(x₁⊔y₁) ⊓ (x₂⊔y₂) ⩽ (x₁ ⊓ (x₂⊔z)) ⊔ (y₁ ⊓ (z⊔y₂))` for
    distinct-point columns spanning distinct lines through `z`. -/
theorem horn_center_ptpt {x₁ x₂ y₁ y₂ z : P.Point}
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂)
    (hXY : P.lineThrough x₁ x₂ ≠ P.lineThrough y₁ y₂)
    (hzX : P.incid z (P.lineThrough x₁ x₂))
    (hzY : P.incid z (P.lineThrough y₁ y₂)) :
    HornConc (pt x₁) (pt x₂) (pt y₁) (pt y₂) bot (pt z) := by
  -- any common point of the two spanned lines is z (axiom 3)
  have huniq : ∀ w, P.incid w (P.lineThrough x₁ x₂) →
      P.incid w (P.lineThrough y₁ y₂) → w = z := fun w hwX hwY =>
    (meetPoint_eq hXY hwX hwY).trans (meetPoint_eq hXY hzX hzY).symm
  show (((pt x₁).join (pt y₁)).meet ((pt x₂).join (pt y₂))).le
    ((((pt x₁).join bot).meet ((pt x₂).join (pt z))).join
      ((PElem.bot.join (pt y₁)).meet ((pt z).join (pt y₂))))
  rw [join_bot_right, bot_join]
  by_cases hzx : z = x₂ <;> by_cases hzy : z = y₂
  · -- z = x₂ = y₂: the second-row join is a point OFF the line x₁y₁
    have hx₂y₂ : x₂ = y₂ := hzx.symm.trans hzy
    have hx₁y₁ : x₁ ≠ y₁ := fun h =>
      hx ((huniq x₁ (P.lineThrough_incid_left x₁ x₂)
        (h ▸ P.lineThrough_incid_left y₁ y₂)).trans hzx)
    have hzW : ¬ P.incid z (P.lineThrough x₁ y₁) := by
      intro hzW
      have hx₁z : x₁ ≠ z := fun h => hx (h.trans hzx)
      have hy₁z : y₁ ≠ z := fun h => hy (h.trans hzy)
      have e1 : P.lineThrough x₁ x₂ = P.lineThrough x₁ y₁ :=
        (lineThrough_eq hx₁z (P.lineThrough_incid_left x₁ x₂) hzX).trans
          (lineThrough_eq hx₁z (P.lineThrough_incid_left x₁ y₁) hzW).symm
      have e2 : P.lineThrough x₁ y₁ = P.lineThrough y₁ y₂ :=
        (lineThrough_eq hy₁z (P.lineThrough_incid_right x₁ y₁) hzW).trans
          (lineThrough_eq hy₁z (P.lineThrough_incid_left y₁ y₂) hzY).symm
      exact hXY (e1.trans e2)
    have hL : ((pt x₁).join (pt y₁)).meet ((pt x₂).join (pt y₂)) = bot := by
      rw [← hx₂y₂, join_pt_pt_self, join_pt_pt_ne hx₁y₁,
        meet_ln_pt_not (hzx ▸ hzW)]
    rw [hL]
    exact bot_le _
  · -- z = x₂ only: the LHS is pinned to y₁, which is the whole second meet
    have hx₂Y : P.incid x₂ (P.lineThrough y₁ y₂) := hzx ▸ hzY
    have hx₂y₂ : x₂ ≠ y₂ := fun h => hzy (hzx.trans h)
    have hV : (pt y₁).meet ((pt z).join (pt y₂)) = pt y₁ := by
      rw [join_pt_pt_ne hzy,
        ← lineThrough_eq hzy hzY (P.lineThrough_incid_right y₁ y₂),
        meet_pt_ln_incid (P.lineThrough_incid_left y₁ y₂)]
    have hx₁Y : ¬ P.incid x₁ (P.lineThrough y₁ y₂) := fun hmem =>
      hx ((huniq x₁ (P.lineThrough_incid_left x₁ x₂) hmem).trans hzx)
    have hx₁y₁ : x₁ ≠ y₁ := fun h =>
      hx₁Y (h ▸ P.lineThrough_incid_left y₁ y₂)
    have hWY : P.lineThrough x₁ y₁ ≠ P.lineThrough y₁ y₂ := fun h =>
      hx₁Y (h ▸ P.lineThrough_incid_left x₁ y₁)
    have hL : ((pt x₁).join (pt y₁)).meet ((pt x₂).join (pt y₂)) = pt y₁ := by
      rw [join_pt_pt_ne hx₁y₁, join_pt_pt_ne hx₂y₂,
        ← lineThrough_eq hx₂y₂ hx₂Y (P.lineThrough_incid_right y₁ y₂),
        meet_ln_ln_ne hWY,
        ← meetPoint_eq hWY (P.lineThrough_incid_right x₁ y₁)
          (P.lineThrough_incid_left y₁ y₂)]
    rw [hL, hV]
    exact le_join_right _ _
  · -- z = y₂ only: mirror — the LHS is pinned to x₁, the whole first meet
    have hy₂X : P.incid y₂ (P.lineThrough x₁ x₂) := hzy ▸ hzX
    have hx₂y₂ : x₂ ≠ y₂ := fun h => hzx (hzy.trans h.symm)
    have hU : (pt x₁).meet ((pt x₂).join (pt z)) = pt x₁ := by
      rw [join_pt_pt_ne (fun h => hzx h.symm),
        ← lineThrough_eq (fun h => hzx h.symm)
          (P.lineThrough_incid_right x₁ x₂) hzX,
        meet_pt_ln_incid (P.lineThrough_incid_left x₁ x₂)]
    have hy₁X : ¬ P.incid y₁ (P.lineThrough x₁ x₂) := fun hmem =>
      hy ((huniq y₁ hmem (P.lineThrough_incid_left y₁ y₂)).trans hzy)
    have hx₁y₁ : x₁ ≠ y₁ := fun h =>
      hy₁X (h ▸ P.lineThrough_incid_left x₁ x₂)
    have hWX : P.lineThrough x₁ y₁ ≠ P.lineThrough x₁ x₂ := fun h =>
      hy₁X (h ▸ P.lineThrough_incid_right x₁ y₁)
    have hL : ((pt x₁).join (pt y₁)).meet ((pt x₂).join (pt y₂)) = pt x₁ := by
      rw [join_pt_pt_ne hx₁y₁, join_pt_pt_ne hx₂y₂,
        ← lineThrough_eq hx₂y₂ (P.lineThrough_incid_right x₁ x₂) hy₂X,
        meet_ln_ln_ne hWX,
        ← meetPoint_eq hWX (P.lineThrough_incid_left x₁ y₁)
          (P.lineThrough_incid_left x₁ x₂)]
    rw [hL, hU]
    exact le_join_left _ _
  · -- z off both column pairs: both conclusion meets are the column tops
    have hU : (pt x₁).meet ((pt x₂).join (pt z)) = pt x₁ := by
      rw [join_pt_pt_ne (fun h => hzx h.symm),
        ← lineThrough_eq (fun h => hzx h.symm)
          (P.lineThrough_incid_right x₁ x₂) hzX,
        meet_pt_ln_incid (P.lineThrough_incid_left x₁ x₂)]
    have hV : (pt y₁).meet ((pt z).join (pt y₂)) = pt y₁ := by
      rw [join_pt_pt_ne hzy,
        ← lineThrough_eq hzy hzY (P.lineThrough_incid_right y₁ y₂),
        meet_pt_ln_incid (P.lineThrough_incid_left y₁ y₂)]
    rw [hU, hV]
    exact meet_le_left _ _

/-- INVERSION: an incomparable pair joins to a line only as two distinct
    points spanning it. -/
theorem join_ln_cases {x y : PElem P} {A : P.Line} (h : x.join y = ln A) :
    (x.le y ∨ y.le x) ∨
    (∃ v w, x = pt v ∧ y = pt w ∧ v ≠ w ∧ A = P.lineThrough v w) := by
  cases x with
  | bot => exact Or.inl (Or.inl (bot_le y))
  | top => rw [join_top_left] at h; exact nomatch h
  | pt v =>
    cases y with
    | bot => exact Or.inl (Or.inr (bot_le _))
    | top => rw [join_top_right] at h; exact nomatch h
    | pt w =>
      by_cases hvw : v = w
      · exact Or.inl (Or.inl (hvw : (pt v).le (pt w)))
      · rw [join_pt_pt_ne hvw] at h
        exact Or.inr ⟨v, w, rfl, rfl, hvw, (PElem.ln.inj h).symm⟩
    | ln B =>
      by_cases hvB : P.incid v B
      · exact Or.inl (Or.inl (hvB : (pt v).le (ln B)))
      · rw [join_pt_ln_not hvB] at h; exact nomatch h
  | ln B =>
    cases y with
    | bot => exact Or.inl (Or.inr (bot_le _))
    | top => rw [join_top_right] at h; exact nomatch h
    | pt w =>
      by_cases hwB : P.incid w B
      · exact Or.inl (Or.inr (hwB : (pt w).le (ln B)))
      · rw [join_ln_pt_not hwB] at h; exact nomatch h
    | ln C =>
      by_cases hBC : B = C
      · exact Or.inl (Or.inl (hBC : (ln B).le (ln C)))
      · rw [join_ln_ln_ne hBC] at h; exact nomatch h

/-- **THE CENTRE CASE**: if the hypothesis meet is EXACTLY a point `z`, the
    Horn conclusion at `(⊥, pt z)` holds.  Chain columns go to the chain steps;
    the residual shape (two distinct-point columns spanning two distinct lines
    through `z`) is the geometric core. -/
theorem horn_center {a₁ a₂ b₁ b₂ : PElem P} {z : P.Point}
    (h : (a₁.join a₂).meet (b₁.join b₂) = pt z) :
    HornConc a₁ a₂ b₁ b₂ bot (pt z) := by
  have hup : ((a₁.join a₂).meet (b₁.join b₂)).le (pt z) := by
    rw [h]; exact le_refl _
  have hzK₁ : (pt z : PElem P).le (a₁.join a₂) := by
    have h1 := meet_le_left (a₁.join a₂) (b₁.join b₂); rwa [h] at h1
  have hzK₂ : (pt z : PElem P).le (b₁.join b₂) := by
    have h1 := meet_le_right (a₁.join a₂) (b₁.join b₂); rwa [h] at h1
  have hup' : ((b₁.join b₂).meet (a₁.join a₂)).le (pt z) := by
    rw [meet_comm]; exact hup
  -- the four chain handlers
  have hA12 : a₁.le a₂ → HornConc a₁ a₂ b₁ b₂ bot (pt z) := fun h12 =>
    center_chain_step' h12 (join_eq_of_le_right h12 ▸ hup)
  have hA21 : a₂.le a₁ → HornConc a₁ a₂ b₁ b₂ bot (pt z) := fun h21 =>
    center_chain_step h21 (join_eq_of_le_left h21 ▸ hzK₁)
      (join_eq_of_le_left h21 ▸ hup)
  have hB12 : b₁.le b₂ → HornConc a₁ a₂ b₁ b₂ bot (pt z) := fun h12 =>
    HornConc.of_swap_ab (center_chain_step' h12 (join_eq_of_le_right h12 ▸ hup'))
  have hB21 : b₂.le b₁ → HornConc a₁ a₂ b₁ b₂ bot (pt z) := fun h21 =>
    HornConc.of_swap_ab (center_chain_step h21 (join_eq_of_le_left h21 ▸ hzK₂)
      (join_eq_of_le_left h21 ▸ hup'))
  rcases join_chain_or_big a₁ a₂ with h12 | h21 | (⟨A, hA⟩ | hA)
  · exact hA12 h12
  · exact hA21 h21
  · -- a-column spans the line A
    rcases join_ln_cases hA with (h12 | h21) | ⟨x₁, x₂, rfl, rfl, hx, hAeq⟩
    · exact hA12 h12
    · exact hA21 h21
    rcases join_chain_or_big b₁ b₂ with h12 | h21 | (⟨B, hB⟩ | hB)
    · exact hB12 h12
    · exact hB21 h21
    · -- b-column spans the line B: the geometric core (or a chain after all)
      rcases join_ln_cases hB with (h12 | h21) | ⟨y₁, y₂, rfl, rfl, hy, hBeq⟩
      · exact hB12 h12
      · exact hB21 h21
      rw [hA, hB] at h
      by_cases hAB : A = B
      · rw [hAB, meet_ln_ln_self] at h; exact nomatch h
      · rw [meet_ln_ln_ne hAB] at h
        have hmz : P.meetPoint A B = z := PElem.pt.inj h
        have hzX : P.incid z (P.lineThrough x₁ x₂) := by
          rw [← hAeq, ← hmz]; exact P.meetPoint_incid_left A B
        have hzY : P.incid z (P.lineThrough y₁ y₂) := by
          rw [← hBeq, ← hmz]; exact P.meetPoint_incid_right A B
        exact horn_center_ptpt hx hy (hBeq ▸ hAeq ▸ hAB) hzX hzY
    · -- b-column joins to ⊤: the hypothesis meet is a whole line — vacuous
      rw [hA, hB, meet_top_right] at h; exact nomatch h
  · -- a-column joins to ⊤: the hypothesis pins the b-join to the point z,
    -- so the b-column is a chain
    rw [hA, meet_top_left] at h
    rcases le_pt_cases (h ▸ le_join_left b₁ b₂) with h1 | h1
    · exact hB12 (h1 ▸ bot_le b₂)
    · rcases le_pt_cases (h ▸ le_join_right b₁ b₂) with h2 | h2
      · exact hB21 (h2 ▸ bot_le b₁)
      · exact hB21 (h2 ▸ h1 ▸ le_refl (pt z))

/-- FAMILY `c₁ = ⊥, c₂ = pt`: the hypothesis meet is `⊥` (disjoint core) or
    exactly the point (centre case). -/
theorem horn_c_bot_pt {a₁ a₂ b₁ b₂ : PElem P} {z : P.Point}
    (h : HornHyp a₁ a₂ b₁ b₂ bot (pt z)) : HornConc a₁ a₂ b₁ b₂ bot (pt z) := by
  have h' : ((a₁.join a₂).meet (b₁.join b₂)).le (pt z) := by
    have h0 : ((a₁.join a₂).meet (b₁.join b₂)).le (PElem.bot.join (pt z)) := h
    rwa [bot_join] at h0
  rcases le_pt_cases h' with hbot | hpt
  · exact horn_core_disjoint _ _ hbot
  · exact horn_center hpt

/-- FAMILY `c₁ = pt, c₂ = ⊥`, by the row symmetry. -/
theorem horn_c_pt_bot {a₁ a₂ b₁ b₂ : PElem P} {z : P.Point}
    (h : HornHyp a₁ a₂ b₁ b₂ (pt z) bot) : HornConc a₁ a₂ b₁ b₂ (pt z) bot :=
  HornConc.of_swap_idx (horn_c_bot_pt h.swap_idx)

/-- FAMILY `c₁ = c₂ = ` the SAME point (distinct points span a line and belong
    to the line families): centre case + c-monotonicity. -/
theorem horn_c_pt_pt_eq {a₁ a₂ b₁ b₂ : PElem P} {z : P.Point}
    (h : HornHyp a₁ a₂ b₁ b₂ (pt z) (pt z)) :
    HornConc a₁ a₂ b₁ b₂ (pt z) (pt z) := by
  have h' : ((a₁.join a₂).meet (b₁.join b₂)).le (pt z) := by
    have h0 : ((a₁.join a₂).meet (b₁.join b₂)).le ((pt z).join (pt z)) := h
    rwa [join_pt_pt_self] at h0
  rcases le_pt_cases h' with hbot | hpt
  · exact horn_core_disjoint _ _ hbot
  · exact (horn_center hpt).mono_c (bot_le _) (le_refl _)

/-! ## Line-hypothesis infrastructure -/

/-- Above a line: the line itself or `⊤`. -/
theorem ge_ln_cases {K : PElem P} {C : P.Line} (h : (ln C).le K) :
    K = ln C ∨ K = top := by
  cases K with
  | bot => exact absurd h (by simp [le])
  | pt w => exact absurd h (by simp [le])
  | ln B => exact Or.inl (by rw [show C = B from h])
  | top => exact Or.inr rfl

/-- INVERSION: an incomparable pair joins to `⊤` only in the three genuinely
    big shapes (non-incident point/line, either order, or distinct lines). -/
theorem join_top_cases {x y : PElem P} (h : x.join y = top) :
    (x.le y ∨ y.le x) ∨
    (∃ v B, x = pt v ∧ y = ln B ∧ ¬ P.incid v B) ∨
    (∃ A w, x = ln A ∧ y = pt w ∧ ¬ P.incid w A) ∨
    (∃ A B, x = ln A ∧ y = ln B ∧ A ≠ B) := by
  cases x with
  | bot => exact Or.inl (Or.inl (bot_le y))
  | top => exact Or.inl (Or.inr (le_top y))
  | pt v =>
    cases y with
    | bot => exact Or.inl (Or.inr (bot_le _))
    | top => exact Or.inl (Or.inl (le_top _))
    | pt w =>
      by_cases hvw : v = w
      · exact Or.inl (Or.inl (hvw : (pt v).le (pt w)))
      · rw [join_pt_pt_ne hvw] at h; exact nomatch h
    | ln B =>
      by_cases hvB : P.incid v B
      · exact Or.inl (Or.inl (hvB : (pt v).le (ln B)))
      · exact Or.inr (Or.inl ⟨v, B, rfl, rfl, hvB⟩)
  | ln A =>
    cases y with
    | bot => exact Or.inl (Or.inr (bot_le _))
    | top => exact Or.inl (Or.inl (le_top _))
    | pt w =>
      by_cases hwA : P.incid w A
      · exact Or.inl (Or.inr (hwA : (pt w).le (ln A)))
      · exact Or.inr (Or.inr (Or.inl ⟨A, w, rfl, rfl, hwA⟩))
    | ln B =>
      by_cases hAB : A = B
      · exact Or.inl (Or.inl (hAB : (ln A).le (ln B)))
      · exact Or.inr (Or.inr (Or.inr ⟨A, B, rfl, rfl, hAB⟩))

/-- Two distinct points of a line `C` join to `ln C` (axiom 3). -/
theorem join_pt_pt_line {x y : P.Point} {C : P.Line} (hxy : x ≠ y)
    (hx : P.incid x C) (hy : P.incid y C) : (pt x).join (pt y) = ln C := by
  rw [join_pt_pt_ne hxy, ← ProjectivePlane.lineThrough_eq hxy hx hy]

/-- Two distinct lines through a common point meet in it (axiom 3). -/
theorem meet_ln_ln_pt {A B : P.Line} {x : P.Point} (hAB : A ≠ B)
    (hxA : P.incid x A) (hxB : P.incid x B) : (ln A).meet (ln B) = pt x := by
  rw [meet_ln_ln_ne hAB, ← ProjectivePlane.meetPoint_eq hAB hxA hxB]

/-! ## The centre case with `z` under one c-column entry (easy half of `H = pt`)

  When the perspective centre `z := (a₁⊔a₂) ⊓ (b₁⊔b₂)` already lies under one of
  `c₁`, `c₂` the whole family reduces to `horn_center` by c-monotonicity: prove
  the conclusion at the tight column `(⊥, pt z)` (resp. `(pt z, ⊥)`) and inflate
  the free entry up to the actual `cᵢ`. -/

/-- Mirror of `horn_center`: the Horn conclusion at `(pt z, ⊥)`. -/
theorem horn_center_c₁ {a₁ a₂ b₁ b₂ : PElem P} {z : P.Point}
    (h : (a₁.join a₂).meet (b₁.join b₂) = pt z) :
    HornConc a₁ a₂ b₁ b₂ (pt z) bot :=
  HornConc.of_swap_idx (horn_center (by rw [join_comm a₂ a₁, join_comm b₂ b₁]; exact h))

/-- **`H = pt z`, easy half**: if the centre `z` lies under `c₁` or under `c₂`,
    the family reduces to `horn_center` by c-monotonicity. -/
theorem horn_center_under {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P} {z : P.Point}
    (hH : (a₁.join a₂).meet (b₁.join b₂) = pt z)
    (hz : (pt z : PElem P).le c₁ ∨ (pt z : PElem P).le c₂) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  rcases hz with h | h
  · exact (horn_center_c₁ hH).mono_c h (bot_le c₂)
  · exact (horn_center hH).mono_c (bot_le c₁) h

/-! ## Reduction of the literal converse to three shape families

  Everything above (the ⊤-tuples of `S2_157b_Desargues`, the disjoint core, the
  centre case with `z` under a c-column entry) reduces the lattice Horn sentence
  at an ARBITRARY 6-tuple, by a four-way split on the SHAPE of the hypothesis
  meet `H := (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂)`, to exactly three residual families:

  · `H = ⊥` — `horn_core_disjoint` (pure modularity; CLOSED, any `c`);
  · `H = pt z` — the PERSPECTIVE-CENTRE family (`famB`); the easy half is
    `horn_center_under`, the residue (`z` under NEITHER `c₁` nor `c₂`, so
    `c₁ ⊔ c₂` is a line/⊤ meeting the centre off both entries) is where the
    Desargues AXIS enters (`desarguesND_implies_horn_points`);
  · `H = ln A` (`famC`) and `H = ⊤` (`famA`) — the line/top degeneracies.

  `latticeHorn_of_families` records the split, machine-checking that these
  three families EXHAUST the remaining cases; `famA/famB/famC` are the residual
  obligations for a fully literal §2.157 converse. -/

/-- **The remaining-gap reduction (exhaustive).**  Given the three residual
    shape families, the lattice Horn sentence holds at every 6-tuple: split on
    the shape of the hypothesis meet and dispatch. -/
theorem latticeHorn_of_families
    (famB : ∀ (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P) (z : P.Point),
        (a₁.join a₂).meet (b₁.join b₂) = pt z →
        HornHyp a₁ a₂ b₁ b₂ c₁ c₂ → HornConc a₁ a₂ b₁ b₂ c₁ c₂)
    (famC : ∀ (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P) (A : P.Line),
        (a₁.join a₂).meet (b₁.join b₂) = ln A →
        HornHyp a₁ a₂ b₁ b₂ c₁ c₂ → HornConc a₁ a₂ b₁ b₂ c₁ c₂)
    (famA : ∀ (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P),
        (a₁.join a₂).meet (b₁.join b₂) = top →
        HornHyp a₁ a₂ b₁ b₂ c₁ c₂ → HornConc a₁ a₂ b₁ b₂ c₁ c₂)
    (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P) (h : HornHyp a₁ a₂ b₁ b₂ c₁ c₂) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  rcases hH : (a₁.join a₂).meet (b₁.join b₂) with _ | z | A | _
  · exact horn_core_disjoint c₁ c₂ hH
  · exact famB a₁ a₂ b₁ b₂ c₁ c₂ z hH h
  · exact famC a₁ a₂ b₁ b₂ c₁ c₂ A hH h
  · exact famA a₁ a₂ b₁ b₂ c₁ c₂ hH h

/-- COATOM: anything not below a line joins that line to `⊤` (the three shapes
    `x ∈ {pt off A, line ≠ A, ⊤}` all overflow).  Hoisted to this shared ancestor of
    `S2_157e`/`S2_157f` so the two identical copies collapse to one. -/
theorem join_ln_top_of_not_le {x : PElem P} {A : P.Line} (h : ¬ x.le (ln A)) :
    x.join (ln A) = top := by
  cases x with
  | bot => exact absurd (bot_le (ln A)) h
  | pt v => exact join_pt_ln_not h
  | ln B => exact join_ln_ln_ne h
  | top => exact join_top_left (ln A)

end PElem

end Freyd.Alg
