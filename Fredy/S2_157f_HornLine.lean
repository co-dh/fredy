/-
  Freyd & Scedrov, *Categories and Allegories* §2.157 (converse, `famC`):
  the LINE-DEGENERACY of the Desargues Horn sentence in the associated lattice
  𝓛(P).  This file discharges the `famC` obligation of
  `latticeHorn_of_families` (`S2_157c_Converse`): the family where the
  hypothesis meet `H := (a₁⊔a₂) ⊓ (b₁⊔b₂)` is a LINE `ln A`.

  Since `meet KA KB = ln A` (with `KA := a₁⊔a₂`, `KB := b₁⊔b₂`), the pair
  `(KA, KB)` is one of `(ln A, ln A)`, `(ln A, ⊤)`, `(⊤, ln A)`, and the
  hypothesis forces `KC := c₁⊔c₂ ⊒ ln A`.  The heart is the SUB-CORE
  `KA = KB = KC = ln A`: all six inputs live in the interval `[⊥, ln A]`, a
  height-2 modular lattice `M_κ` (⊥, the points incident to `A`, `ln A`), and
  `HornConc` there is pure `M_κ` modular-lattice algebra — NO Desargues, only
  incidence and modularity.  This SUB-CORE is discharged in full here:
  `horn_shape_lll` (`KA = KB = KC = ln A`), whose engine is `horn_atoms` (the
  `M_κ` combinatorial heart) together with the `hornConc_*_ln` sufficiency
  lemmas that peel any entry equal to `ln A`.

  Also discharged in full: `KA = KB = ln A`, `KC = ⊤` — `horn_shape_llt`.
  `join_top_cases` splits the `⊤` `c`-column into a single `⊤` entry (closed by
  the `hornConc_top_*` prunings) plus three "big" shapes; `bigshape_lnln`/
  `bigshape_lnpt` peel any `ln A` entry (via `hornConc_*_topc`) and hand the
  point columns to the generic leaves `horn_lines_bb'`/`horn_line_ptw`, the
  `w ∈ A` sub-case being closed by `HornConc.mono_c` from `horn_shape_lll`.

  STILL OPEN (see the note at the end of the file): the `KB = ⊤` shape
  (`horn_shape_lt`) and its `swap_ab` mirror `KA = ⊤`.  Both reduce to
  `horn_KB_top` (`b₁⊔b₂ = ⊤` and `a₁⊔a₂ ⩽ c₁⊔c₂` imply `HornConc`), where the
  `⊤`-column is `b` (resp. `a`), which — unlike the `c`-column — occurs on BOTH
  sides of the conclusion, so neither `HornConc.mono_c` nor the peeling route
  applies directly; that shape is a separate incidence case-bash.
-/
import Fredy.S2_157c_Converse

universe v u

namespace Freyd.Alg

namespace PElem

variable {P : ProjectivePlane.{u}}

/-! ## Shape of a meet that is a line -/

/-- If `x ⊓ y = ln A` then `(x, y)` is `(ln A, ln A)`, `(ln A, ⊤)` or
    `(⊤, ln A)` — the only meet-table entries producing a line. -/
theorem meet_eq_ln_cases {x y : PElem P} {A : P.Line} (h : x.meet y = ln A) :
    (x = ln A ∧ y = ln A) ∨ (x = ln A ∧ y = top) ∨ (x = top ∧ y = ln A) := by
  cases x with
  | bot => exact absurd h (by simp [meet])
  | pt v => cases y <;> simp [meet] at h <;> (try split at h) <;> exact absurd h (by simp)
  | top =>
    -- `top ⊓ y = y`
    exact Or.inr (Or.inr ⟨rfl, by rw [meet_top_left] at h; exact h⟩)
  | ln B =>
    cases y with
    | bot => exact absurd h (by simp [meet])
    | pt w => exact absurd h (by rw [meet]; split <;> simp)
    | top =>
      -- `ln B ⊓ top = ln B = ln A`
      rw [meet_top_right] at h
      exact Or.inr (Or.inl ⟨h, rfl⟩)
    | ln C =>
      by_cases hBC : B = C
      · subst hBC; rw [meet_ln_ln_self] at h; exact Or.inl ⟨h, h⟩
      · rw [meet_ln_ln_ne hBC] at h; exact absurd h (by simp)

/-! ## The sub-core `H = ln A`: sufficiency when a column entry is `ln A`

  Whenever one of the six inputs equals `ln A` (the top of the interval) the
  conclusion closes by pure lub/glb reasoning: the two `ln A`-joins collapse to
  `ln A`, so the corresponding conclusion meets dominate the second column. -/

/-- `c₁ = ln A`: the conclusion holds provided `a₂, b₂ ⩽ ln A`. -/
theorem hornConc_c₁_ln {a₁ a₂ b₁ b₂ c₂ : PElem P} {A : P.Line}
    (ha₂ : a₂.le (ln A)) (hb₂ : b₂.le (ln A)) :
    HornConc a₁ a₂ b₁ b₂ (ln A) c₂ :=
  le_trans (meet_le_right _ _)
    (join_le
      (le_trans
        (le_meet (le_trans ha₂ (le_join_right a₁ (ln A))) (le_join_left a₂ c₂))
        (le_join_left _ _))
      (le_trans
        (le_meet (le_trans hb₂ (le_join_left (ln A) b₁)) (le_join_right c₂ b₂))
        (le_join_right _ _)))

/-- `c₂ = ln A`, by the row symmetry. -/
theorem hornConc_c₂_ln {a₁ a₂ b₁ b₂ c₁ : PElem P} {A : P.Line}
    (ha₁ : a₁.le (ln A)) (hb₁ : b₁.le (ln A)) :
    HornConc a₁ a₂ b₁ b₂ c₁ (ln A) :=
  HornConc.of_swap_idx (hornConc_c₁_ln ha₁ hb₁)

/-- MODULAR IDENTITY (given `c₁ ⊔ c₂ = ln A`): `((c₁⊔b₁) ⊓ (c₂⊔b₂)) ⊔ c₂ =
    c₂ ⊔ b₂`.  One shear absorbs `c₂` into the meet's first factor via
    `c₁ ⊔ c₂ = ln A`. -/
theorem mcb_join_c₂ {b₁ b₂ c₁ c₂ : PElem P} {A : P.Line}
    (hc : c₁.join c₂ = ln A) (hb₁ : b₁.le (ln A)) (hc₂ : c₂.le (ln A))
    (hb₂ : b₂.le (ln A)) :
    ((c₁.join b₁).meet (c₂.join b₂)).join c₂ = c₂.join b₂ := by
  have hc₁ : c₁.le (ln A) := hc ▸ le_join_left c₁ c₂
  -- `(c₁⊔b₁) ⊔ c₂ = ln A`
  have hbig : (c₁.join b₁).join c₂ = ln A := by
    apply le_antisymm
    · exact join_le (join_le hc₁ hb₁) hc₂
    · rw [← hc]
      exact join_le (le_trans (le_join_left c₁ b₁) (le_join_left _ c₂))
        (le_join_right _ c₂)
  calc ((c₁.join b₁).meet (c₂.join b₂)).join c₂
      = (c₂.join b₂).meet ((c₁.join b₁).join c₂) := by
        rw [meet_comm (c₁.join b₁) (c₂.join b₂),
          ← modular_eq (le_join_left c₂ b₂)]
    _ = (c₂.join b₂).meet (ln A) := by rw [hbig]
    _ = c₂.join b₂ := (le_iff_meet_eq.mp (join_le hc₂ hb₂)).symm ▸ rfl

/-- `a₁ = ln A` (given `c₁ ⊔ c₂ = ln A` and all others `⩽ ln A`): the
    conclusion holds.  `M_ac` collapses to `a₂ ⊔ c₂ ⊒ a₂, c₂`; the identity
    `mcb_join_c₂` lifts `c₂ ⊔ M_cb` to `c₂ ⊔ b₂ ⊒ b₂`, so the collapsed LHS
    `a₂ ⊔ b₂` sits under the conclusion. -/
theorem hornConc_a₁_ln {a₂ b₁ b₂ c₁ c₂ : PElem P} {A : P.Line}
    (hb₁ : b₁.le (ln A)) (hb₂ : b₂.le (ln A)) (ha₂ : a₂.le (ln A))
    (hc₂ : c₂.le (ln A)) (hc : c₁.join c₂ = ln A) :
    HornConc (ln A) a₂ b₁ b₂ c₁ c₂ := by
  -- LHS ⩽ a₂ ⊔ b₂
  have hlhs : ((((ln A) : PElem P).join b₁).meet (a₂.join b₂)).le (a₂.join b₂) :=
    meet_le_right _ _
  -- c₂ ⩽ M_ac  and  a₂ ⩽ M_ac
  have hc_ac : c₂.le ((((ln A) : PElem P).join c₁).meet (a₂.join c₂)) :=
    le_meet (le_trans hc₂ (le_join_left (ln A) c₁)) (le_join_right a₂ c₂)
  have ha_ac : a₂.le ((((ln A) : PElem P).join c₁).meet (a₂.join c₂)) :=
    le_meet (le_trans ha₂ (le_join_left (ln A) c₁)) (le_join_left a₂ c₂)
  -- b₂ ⩽ M_cb ⊔ c₂ = c₂ ⊔ b₂
  have hb_le : b₂.le (((c₁.join b₁).meet (c₂.join b₂)).join c₂) := by
    rw [mcb_join_c₂ hc hb₁ hc₂ hb₂]; exact le_join_right c₂ b₂
  refine le_trans hlhs (join_le (le_trans ha_ac (le_join_left _ _)) ?_)
  -- b₂ ⩽ M_ac ⊔ M_cb
  exact le_trans hb_le
    (join_le (le_join_right _ _) (le_trans hc_ac (le_join_left _ _)))

/-- `a₂ = ln A`, by the row symmetry. -/
theorem hornConc_a₂_ln {a₁ b₁ b₂ c₁ c₂ : PElem P} {A : P.Line}
    (hb₁ : b₁.le (ln A)) (hb₂ : b₂.le (ln A)) (ha₁ : a₁.le (ln A))
    (hc₁ : c₁.le (ln A)) (hc : c₁.join c₂ = ln A) :
    HornConc a₁ (ln A) b₁ b₂ c₁ c₂ :=
  HornConc.of_swap_idx
    (hornConc_a₁_ln hb₂ hb₁ ha₁ hc₁ (by rw [join_comm c₂ c₁]; exact hc))

/-- `b₁ = ln A`, by the column symmetry. -/
theorem hornConc_b₁_ln {a₁ a₂ b₂ c₁ c₂ : PElem P} {A : P.Line}
    (ha₁ : a₁.le (ln A)) (ha₂ : a₂.le (ln A)) (hb₂ : b₂.le (ln A))
    (hc₂ : c₂.le (ln A)) (hc : c₁.join c₂ = ln A) :
    HornConc a₁ a₂ (ln A) b₂ c₁ c₂ :=
  HornConc.of_swap_ab (hornConc_a₁_ln ha₁ ha₂ hb₂ hc₂ hc)

/-- `b₂ = ln A`, by both symmetries. -/
theorem hornConc_b₂_ln {a₁ a₂ b₁ c₁ c₂ : PElem P} {A : P.Line}
    (ha₁ : a₁.le (ln A)) (ha₂ : a₂.le (ln A)) (hb₁ : b₁.le (ln A))
    (hc₁ : c₁.le (ln A)) (hc : c₁.join c₂ = ln A) :
    HornConc a₁ a₂ b₁ (ln A) c₁ c₂ :=
  HornConc.of_swap_ab (hornConc_a₂_ln ha₁ ha₂ hb₁ hc₁ hc)

/-! ## The M_κ heart: six points on the line `A`

  When every column joins to `ln A` and none of the six inputs is `ln A`
  itself, all six are POINTS incident to `A`.  In the height-2 interval
  `[⊥, ln A]` distinct points join to `ln A` and meet in `⊥`, so `HornConc` is
  decided by the equalities among the six points.  A four-way split routes all
  but one shape to the sufficiency lemmas; the residual shape (`c₁ = b₁`,
  `c₂ = a₂`) is the single genuine lattice computation. -/

/-- The residual `M_κ` shape (`c₁ = b₁`, `c₂ = a₂`): a four-cell equality split
    on `(a₁ =? b₁, a₂ =? b₂)`.  The `c`-spread hypothesis `b₁ ≠ a₂` closes the
    top cell. -/
theorem horn_atoms_case3 {a₁ a₂ b₁ b₂ : P.Point} {A : P.Line}
    (ha₁ : P.incid a₁ A) (ha₂ : P.incid a₂ A) (hb₁ : P.incid b₁ A)
    (hb₂ : P.incid b₂ A) (hne_a : a₁ ≠ a₂) (hb₁a₂ : b₁ ≠ a₂) :
    HornConc (pt a₁) (pt a₂) (pt b₁) (pt b₂) (pt b₁) (pt a₂) := by
  by_cases hab1 : a₁ = b₁
  · subst hab1
    by_cases hab2 : a₂ = b₂
    · subst hab2
      show ((((pt a₁) : PElem P).join (pt a₁)).meet ((pt a₂).join (pt a₂))).le _
      rw [join_pt_pt_self, join_pt_pt_self, meet_pt_pt_ne hne_a]; exact bot_le _
    · exact hornConc_of_le_cb (le_refl _)
  · by_cases hab2 : a₂ = b₂
    · subst hab2; exact hornConc_of_le_ac (le_refl _)
    · show ((((pt a₁) : PElem P).join (pt b₁)).meet ((pt a₂).join (pt b₂))).le
        ((((pt a₁).join (pt b₁)).meet ((pt a₂).join (pt a₂))).join
          (((pt b₁).join (pt b₁)).meet ((pt a₂).join (pt b₂))))
      rw [join_pt_pt_line hab1 ha₁ hb₁, join_pt_pt_line hab2 ha₂ hb₂,
        meet_ln_ln_self, join_pt_pt_self a₂, join_pt_pt_self b₁,
        meet_ln_pt_incid ha₂, meet_pt_ln_incid hb₁,
        join_pt_pt_line hb₁a₂.symm ha₂ hb₁]
      exact le_refl _

/-- **The `M_κ` heart** (`KA = KB = KC = ln A`, no entry `ln A`): six points on
    the line `A` with distinct columns.  All but the residual shapes route to
    `hornConc_of_left`/`_right`; the `c = a` and `c = b` shapes are `le_cb`/
    `le_ac`; the two crossed shapes are `horn_atoms_case3` (and its `swap_idx`
    mirror). -/
theorem horn_atoms {a₁ a₂ b₁ b₂ c₁ c₂ : P.Point} {A : P.Line}
    (ha₁ : P.incid a₁ A) (ha₂ : P.incid a₂ A) (hb₁ : P.incid b₁ A)
    (hb₂ : P.incid b₂ A) (hc₁ : P.incid c₁ A) (hc₂ : P.incid c₂ A)
    (hne_a : a₁ ≠ a₂) (hne_c : c₁ ≠ c₂) :
    HornConc (pt a₁) (pt a₂) (pt b₁) (pt b₂) (pt c₁) (pt c₂) := by
  by_cases hL : a₂ ≠ c₂ ∧ c₂ ≠ b₂
  · exact hornConc_of_left
      (by rw [join_pt_pt_line hL.1 ha₂ hc₂]; exact ha₁)
      (by rw [join_pt_pt_line hL.2 hc₂ hb₂]; exact hb₁)
  · by_cases hR : a₁ ≠ c₁ ∧ c₁ ≠ b₁
    · exact hornConc_of_right
        (by rw [join_pt_pt_line hR.1 ha₁ hc₁]; exact ha₂)
        (by rw [join_pt_pt_line hR.2 hc₁ hb₁]; exact hb₂)
    · -- residual: `(a₂=c₂ ∨ c₂=b₂) ∧ (a₁=c₁ ∨ c₁=b₁)` (no `push_neg` in core)
      have hLb : a₂ ≠ c₂ → c₂ = b₂ :=
        fun hne => Classical.byContradiction fun hcb => hL ⟨hne, hcb⟩
      have hRb : a₁ ≠ c₁ → c₁ = b₁ :=
        fun hne => Classical.byContradiction fun hcb => hR ⟨hne, hcb⟩
      by_cases h1 : a₂ = c₂
      · subst h1
        by_cases h2 : a₁ = c₁
        · subst h2; exact hornConc_of_le_cb (le_refl _)
        · have hcb : c₁ = b₁ := hRb h2
          subst hcb; exact horn_atoms_case3 ha₁ ha₂ hb₁ hb₂ hne_a hne_c
      · have hc2b2 : c₂ = b₂ := hLb h1
        subst hc2b2
        by_cases h2 : a₁ = c₁
        · subst h2
          exact HornConc.of_swap_idx
            (horn_atoms_case3 ha₂ ha₁ hb₂ hb₁ hne_a.symm hne_c.symm)
        · have hcb : c₁ = b₁ := hRb h2
          subst hcb; exact hornConc_of_le_ac (le_refl _)

/-- Below `ln A` and neither `⊥` nor `ln A`: a point incident to `A`. -/
theorem pt_of_le_ln_ne {x : PElem P} {A : P.Line} (hx : x.le (ln A))
    (hbot : x ≠ bot) (hln : x ≠ ln A) : ∃ y, x = pt y ∧ P.incid y A := by
  rcases le_ln_cases hx with h | h | h
  · exact absurd h hbot
  · exact h
  · exact absurd h hln

/-! ## SHAPE `(ln A, ln A)`: `KA = KB = ln A`

  If additionally `KC = ln A` this is the `M_κ` heart; if `KC = ⊤` the
  `c`-column joins to `⊤` and is handled with the point columns fixed on `A`. -/

/-- SUB-CORE `KA = KB = KC = ln A`: reduce to `horn_atoms` after peeling off any
    entry that is itself `ln A` via the `hornConc_*_ln` sufficiency lemmas. -/
theorem horn_shape_lll {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P} {A : P.Line}
    (hKA : a₁.join a₂ = ln A) (hKB : b₁.join b₂ = ln A)
    (hKC : c₁.join c₂ = ln A) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  have ha₁ : a₁.le (ln A) := hKA ▸ le_join_left a₁ a₂
  have ha₂ : a₂.le (ln A) := hKA ▸ le_join_right a₁ a₂
  have hb₁ : b₁.le (ln A) := hKB ▸ le_join_left b₁ b₂
  have hb₂ : b₂.le (ln A) := hKB ▸ le_join_right b₁ b₂
  have hc₁ : c₁.le (ln A) := hKC ▸ le_join_left c₁ c₂
  have hc₂ : c₂.le (ln A) := hKC ▸ le_join_right c₁ c₂
  by_cases hca : c₁ = ln A
  · subst hca; exact hornConc_c₁_ln ha₂ hb₂
  by_cases hcb : c₂ = ln A
  · subst hcb; exact hornConc_c₂_ln ha₁ hb₁
  by_cases haa : a₁ = ln A
  · subst haa; exact hornConc_a₁_ln hb₁ hb₂ ha₂ hc₂ hKC
  by_cases hab : a₂ = ln A
  · subst hab; exact hornConc_a₂_ln hb₁ hb₂ ha₁ hc₁ hKC
  by_cases hba : b₁ = ln A
  · subst hba; exact hornConc_b₁_ln ha₁ ha₂ hb₂ hc₂ hKC
  by_cases hbb : b₂ = ln A
  · subst hbb; exact hornConc_b₂_ln ha₁ ha₂ hb₁ hc₁ hKC
  -- none is `ln A`: every entry is a point incident to `A`
  obtain ⟨pa₁, ea₁, ia₁⟩ := pt_of_le_ln_ne ha₁
    (fun h => hab (by rw [h, bot_join] at hKA; exact hKA)) haa
  obtain ⟨pa₂, ea₂, ia₂⟩ := pt_of_le_ln_ne ha₂
    (fun h => haa (by rw [h, join_bot_right] at hKA; exact hKA)) hab
  obtain ⟨pb₁, eb₁, ib₁⟩ := pt_of_le_ln_ne hb₁
    (fun h => hbb (by rw [h, bot_join] at hKB; exact hKB)) hba
  obtain ⟨pb₂, eb₂, ib₂⟩ := pt_of_le_ln_ne hb₂
    (fun h => hba (by rw [h, join_bot_right] at hKB; exact hKB)) hbb
  obtain ⟨pc₁, ec₁, ic₁⟩ := pt_of_le_ln_ne hc₁
    (fun h => hcb (by rw [h, bot_join] at hKC; exact hKC)) hca
  obtain ⟨pc₂, ec₂, ic₂⟩ := pt_of_le_ln_ne hc₂
    (fun h => hca (by rw [h, join_bot_right] at hKC; exact hKC)) hcb
  subst ea₁ ea₂ eb₁ eb₂ ec₁ ec₂
  have hne_a : pa₁ ≠ pa₂ := by
    intro h; rw [h, join_pt_pt_self] at hKA; exact absurd hKA (by simp)
  have hne_c : pc₁ ≠ pc₂ := by
    intro h; rw [h, join_pt_pt_self] at hKC; exact absurd hKC (by simp)
  exact horn_atoms ia₁ ia₂ ib₁ ib₂ ic₁ ic₂ hne_a hne_c

/-! ## The `⊤`-mixed shapes: `KC = ⊤`, `KB = ⊤`, `KA = ⊤`

  Machinery first: the pure-modular absorption identity `topjoin_absorb` (the
  `c₁⊔c₂ = ⊤` analogue of `mcb_join_c₂`), the "a foreign line joins to `⊤`"
  evaluation, and the `ln A`-entry sufficiency lemmas for the top case. -/

/-- ABSORPTION (`c₁⊔c₂ = ⊤`, pure modular): `((c₁⊔x)⊓(c₂⊔y)) ⊔ c₂ = c₂⊔y`. -/
theorem topjoin_absorb {x y c₁ c₂ : PElem P} (hc : c₁.join c₂ = top) :
    ((c₁.join x).meet (c₂.join y)).join c₂ = c₂.join y := by
  have hbig : (c₁.join x).join c₂ = top := by
    apply le_antisymm (le_top _)
    rw [← hc]
    exact join_le (le_trans (le_join_left c₁ x) (le_join_left _ c₂))
      (le_join_right _ c₂)
  calc ((c₁.join x).meet (c₂.join y)).join c₂
      = (c₂.join y).meet ((c₁.join x).join c₂) := by
        rw [meet_comm (c₁.join x) (c₂.join y), ← modular_eq (le_join_left c₂ y)]
    _ = (c₂.join y).meet top := by rw [hbig]
    _ = c₂.join y := meet_top_right _

/-- The `c₁`-side of `topjoin_absorb`. -/
theorem topjoin_absorb' {x y c₁ c₂ : PElem P} (hc : c₁.join c₂ = top) :
    ((c₁.join x).meet (c₂.join y)).join c₁ = c₁.join x := by
  rw [meet_comm]
  exact topjoin_absorb (by rw [join_comm]; exact hc)

/-- A point-or-line `x ⩽ ln A` joins a FOREIGN line `ln B` (`A ≠ B`) to `⊤`
    unless it already lies on `B`. -/
theorem join_ln_top_of_le {x : PElem P} {A B : P.Line} (hx : x.le (ln A))
    (hAB : A ≠ B) (hxB : ¬ x.le (ln B)) : x.join (ln B) = top := by
  rcases le_ln_cases hx with h | ⟨y, hy, _⟩ | h
  · subst h; exact absurd (bot_le (ln B)) hxB
  · subst hy; exact join_pt_ln_not hxB
  · subst h; exact join_ln_ln_ne hAB

/-- `a₁ = ln A` sufficiency in the top case: if `ln A ⊔ c₁ = ⊤` and
    `c₁ ⊔ c₂ = ⊤`, the conclusion holds (`M_ac` collapses to `a₂⊔c₂`, and
    `topjoin_absorb` lifts `c₂ ⊔ M_cb` to `c₂⊔b₂ ⊒ b₂`). -/
theorem hornConc_a₁_topc {a₂ b₁ b₂ c₁ c₂ : PElem P} {A : P.Line}
    (hac₁ : ((ln A : PElem P)).join c₁ = top) (hc : c₁.join c₂ = top) :
    HornConc (ln A) a₂ b₁ b₂ c₁ c₂ := by
  have ha_ac : a₂.le ((((ln A) : PElem P).join c₁).meet (a₂.join c₂)) :=
    le_meet (by rw [hac₁]; exact le_top a₂) (le_join_left a₂ c₂)
  have hc_ac : c₂.le ((((ln A) : PElem P).join c₁).meet (a₂.join c₂)) :=
    le_meet (by rw [hac₁]; exact le_top c₂) (le_join_right a₂ c₂)
  have hb_le : b₂.le (((c₁.join b₁).meet (c₂.join b₂)).join c₂) := by
    rw [topjoin_absorb hc]; exact le_join_right c₂ b₂
  refine le_trans (meet_le_right _ _)
    (join_le (le_trans ha_ac (le_join_left _ _)) ?_)
  exact le_trans hb_le
    (join_le (le_join_right _ _) (le_trans hc_ac (le_join_left _ _)))

/-- `a₂ = ln A` sufficiency (top case), by the row symmetry. -/
theorem hornConc_a₂_topc {a₁ b₁ b₂ c₁ c₂ : PElem P} {A : P.Line}
    (hac₂ : ((ln A : PElem P)).join c₂ = top) (hc : c₁.join c₂ = top) :
    HornConc a₁ (ln A) b₁ b₂ c₁ c₂ :=
  HornConc.of_swap_idx (hornConc_a₁_topc hac₂ (by rw [join_comm c₂ c₁]; exact hc))

/-- `b₁ = ln A` sufficiency (top case), by the column symmetry. -/
theorem hornConc_b₁_topc {a₁ a₂ b₂ c₁ c₂ : PElem P} {A : P.Line}
    (hac₁ : ((ln A : PElem P)).join c₁ = top) (hc : c₁.join c₂ = top) :
    HornConc a₁ a₂ (ln A) b₂ c₁ c₂ :=
  HornConc.of_swap_ab (hornConc_a₁_topc hac₁ hc)

/-- `b₂ = ln A` sufficiency (top case), by both symmetries. -/
theorem hornConc_b₂_topc {a₁ a₂ b₁ c₁ c₂ : PElem P} {A : P.Line}
    (hac₂ : ((ln A : PElem P)).join c₂ = top) (hc : c₁.join c₂ = top) :
    HornConc a₁ a₂ b₁ (ln A) c₁ c₂ :=
  HornConc.of_swap_ab (hornConc_a₂_topc hac₂ hc)

/-- **Generic leaf, `c = (ln B, ln B')`** (`A,B,B'` pairwise distinct): six
    points on `A`, `c` two foreign lines.  Casing the four incidences
    `pa₁∈B, pa₂∈B', pb₁∈B, pb₂∈B'`, the sufficiency lemmas
    `hornConc_of_le_cb/_ac/_right/_left` cover 14 of 16 combos; the two residual
    combos both give `M_ac ⊔ M_cb = ⊤`. -/
theorem horn_lines_bb' {pa₁ pa₂ pb₁ pb₂ : P.Point} {A B B' : P.Line}
    (ia₁ : P.incid pa₁ A) (ia₂ : P.incid pa₂ A) (ib₁ : P.incid pb₁ A)
    (ib₂ : P.incid pb₂ A) (hAB : A ≠ B) (hAB' : A ≠ B') (hBB : B ≠ B') :
    HornConc (pt pa₁) (pt pa₂) (pt pb₁) (pt pb₂) (ln B) (ln B') := by
  have la₁ : (pt pa₁ : PElem P).le (ln A) := ia₁
  have la₂ : (pt pa₂ : PElem P).le (ln A) := ia₂
  have lb₁ : (pt pb₁ : PElem P).le (ln A) := ib₁
  have lb₂ : (pt pb₂ : PElem P).le (ln A) := ib₂
  by_cases hcb : (pt pa₁ : PElem P).le (ln B) ∧ (pt pa₂ : PElem P).le (ln B')
  · exact hornConc_of_le_cb (le_meet
      (le_trans (meet_le_left _ _) (join_mono hcb.1 (le_refl _)))
      (le_trans (meet_le_right _ _) (join_mono hcb.2 (le_refl _))))
  by_cases hac : (pt pb₁ : PElem P).le (ln B) ∧ (pt pb₂ : PElem P).le (ln B')
  · exact hornConc_of_le_ac (le_meet
      (le_trans (meet_le_left _ _) (join_mono (le_refl _) hac.1))
      (le_trans (meet_le_right _ _) (join_mono (le_refl _) hac.2)))
  by_cases hr : ¬(pt pa₁ : PElem P).le (ln B) ∧ ¬(pt pb₁ : PElem P).le (ln B)
  · exact hornConc_of_right
      (by rw [join_ln_top_of_le la₁ hAB hr.1]; exact le_top _)
      (by rw [join_comm (ln B) (pt pb₁), join_ln_top_of_le lb₁ hAB hr.2]
          exact le_top _)
  by_cases hl : ¬(pt pa₂ : PElem P).le (ln B') ∧ ¬(pt pb₂ : PElem P).le (ln B')
  · exact hornConc_of_left
      (by rw [join_ln_top_of_le la₂ hAB' hl.1]; exact le_top _)
      (by rw [join_comm (ln B') (pt pb₂), join_ln_top_of_le lb₂ hAB' hl.2]
          exact le_top _)
  -- residual: two uncovered combos, both `RHS = ⊤`
  by_cases hw : (pt pa₁ : PElem P).le (ln B)
  · have hx : ¬(pt pa₂ : PElem P).le (ln B') := fun h => hcb ⟨hw, h⟩
    have hz : (pt pb₂ : PElem P).le (ln B') :=
      Classical.byContradiction fun hz' => hl ⟨hx, hz'⟩
    have hy : ¬(pt pb₁ : PElem P).le (ln B) := fun h => hac ⟨h, hz⟩
    show (((pt pa₁ : PElem P).join (pt pb₁)).meet ((pt pa₂).join (pt pb₂))).le
      ((((pt pa₁).join (ln B)).meet ((pt pa₂).join (ln B'))).join
        (((ln B).join (pt pb₁)).meet ((ln B').join (pt pb₂))))
    rw [join_eq_of_le_right hw, join_ln_top_of_le la₂ hAB' hx, meet_top_right,
      join_comm (ln B) (pt pb₁), join_ln_top_of_le lb₁ hAB hy,
      join_comm (ln B') (pt pb₂), join_eq_of_le_right hz, meet_top_left,
      join_ln_ln_ne hBB]
    exact le_top _
  · -- pa₁ ∉ B → the mirror combo `(F,T,T,F)`
    have hy : (pt pb₁ : PElem P).le (ln B) :=
      Classical.byContradiction fun hy' => hr ⟨hw, hy'⟩
    have hz : ¬(pt pb₂ : PElem P).le (ln B') := fun h => hac ⟨hy, h⟩
    have hx : (pt pa₂ : PElem P).le (ln B') :=
      Classical.byContradiction fun hx' => hl ⟨hx', hz⟩
    show (((pt pa₁ : PElem P).join (pt pb₁)).meet ((pt pa₂).join (pt pb₂))).le
      ((((pt pa₁).join (ln B)).meet ((pt pa₂).join (ln B'))).join
        (((ln B).join (pt pb₁)).meet ((ln B').join (pt pb₂))))
    rw [join_ln_top_of_le la₁ hAB hw, join_eq_of_le_right hx, meet_top_left,
      join_comm (ln B) (pt pb₁), join_eq_of_le_right hy,
      join_comm (ln B') (pt pb₂), join_ln_top_of_le lb₂ hAB' hz, meet_top_right,
      join_ln_ln_ne hBB.symm]
    exact le_top _

/-- ABSORPTION, `M_ac` orientation (`c₁⊔c₂ = ⊤`): `((a₁⊔c₁)⊓(a₂⊔c₂)) ⊔ c₂ =
    a₂⊔c₂`. -/
theorem mac_join_c₂ {a₁ a₂ c₁ c₂ : PElem P} (hc : c₁.join c₂ = top) :
    ((a₁.join c₁).meet (a₂.join c₂)).join c₂ = a₂.join c₂ := by
  have hbig : (a₁.join c₁).join c₂ = top := by
    apply le_antisymm (le_top _)
    rw [← hc]
    exact join_le (le_trans (le_join_right a₁ c₁) (le_join_left _ c₂))
      (le_join_right _ c₂)
  calc ((a₁.join c₁).meet (a₂.join c₂)).join c₂
      = (a₂.join c₂).meet ((a₁.join c₁).join c₂) := by
        rw [meet_comm (a₁.join c₁) (a₂.join c₂), ← modular_eq (le_join_right a₂ c₂)]
    _ = (a₂.join c₂).meet top := by rw [hbig]
    _ = a₂.join c₂ := meet_top_right _

/-- **Generic leaf, `c = (ln B, pt w)`** (`B ≠ A`, `w ∉ B`): six points on `A`,
    `c` a foreign line and a point off it.  Case the `B`-incidences of `a₁, b₁`:
    both off `B` → `hornConc_of_right`; exactly one on `B` → an absorption
    argument (`mac_join_c₂`/`topjoin_absorb`); both on `B` (so `a₁ = b₁ = A∩B`
    by axiom 3) → the modular shear `LHS ⩽ ln B ⊓ (RHS ⊔ pt w) = RHS`. -/
theorem horn_line_ptw {pa₁ pa₂ pb₁ pb₂ w : P.Point} {A B : P.Line}
    (ia₁ : P.incid pa₁ A) (ia₂ : P.incid pa₂ A) (ib₁ : P.incid pb₁ A)
    (_ib₂ : P.incid pb₂ A) (hAB : A ≠ B) (hwB : ¬ P.incid w B) :
    HornConc (pt pa₁) (pt pa₂) (pt pb₁) (pt pb₂) (ln B) (pt w) := by
  have la₁ : (pt pa₁ : PElem P).le (ln A) := ia₁
  have lb₁ : (pt pb₁ : PElem P).le (ln A) := ib₁
  have hc : ((ln B : PElem P)).join (pt w) = top := join_ln_pt_not hwB
  by_cases hpa₁ : (pt pa₁ : PElem P).le (ln B)
  · by_cases hpb₁ : (pt pb₁ : PElem P).le (ln B)
    · -- both on `B`: `pa₁ = pb₁` (axiom 3), the modular shear
      have heq : pb₁ = pa₁ := (P.unique ib₁ hpb₁ ia₁ hpa₁).resolve_right hAB
      subst pb₁
      have hMac : (((pt pa₁ : PElem P).join (ln B)).meet ((pt pa₂).join (pt w))).le
          (ln B) :=
        le_trans (meet_le_left _ _)
          (show ((pt pa₁ : PElem P).join (ln B)).le (ln B) by
            rw [join_eq_of_le_right hpa₁]; exact le_refl _)
      have hMcb : (((ln B : PElem P).join (pt pa₁)).meet ((pt w).join (pt pb₂))).le
          (ln B) :=
        le_trans (meet_le_left _ _)
          (show ((ln B : PElem P).join (pt pa₁)).le (ln B) by
            rw [join_eq_of_le_left hpa₁]; exact le_refl _)
      have hR : ((((pt pa₁ : PElem P).join (ln B)).meet ((pt pa₂).join (pt w))).join
          (((ln B).join (pt pa₁)).meet ((pt w).join (pt pb₂)))).le (ln B) :=
        join_le hMac hMcb
      have ha₂ : (pt pa₂ : PElem P).le
          ((((pt pa₁).join (ln B)).meet ((pt pa₂).join (pt w))).join (pt w)) := by
        rw [mac_join_c₂ hc]; exact le_join_left _ _
      have hb₂ : (pt pb₂ : PElem P).le
          ((((ln B).join (pt pa₁)).meet ((pt w).join (pt pb₂))).join (pt w)) := by
        rw [topjoin_absorb hc]; exact le_join_right _ _
      have hLHS_lnB :
          (((pt pa₁ : PElem P).join (pt pa₁)).meet ((pt pa₂).join (pt pb₂))).le (ln B) :=
        le_trans (meet_le_left _ _)
          (show ((pt pa₁ : PElem P).join (pt pa₁)).le (ln B) by
            rw [join_pt_pt_self]; exact hpa₁)
      have h2 : (((pt pa₁ : PElem P).join (pt pa₁)).meet ((pt pa₂).join (pt pb₂))).le
          ((pt w).join ((((pt pa₁).join (ln B)).meet ((pt pa₂).join (pt w))).join
            (((ln B).join (pt pa₁)).meet ((pt w).join (pt pb₂))))) :=
        le_trans (meet_le_right _ _)
          (join_le
            (le_trans ha₂ (join_le
              (le_trans (le_join_left _ _) (le_join_right (pt w) _))
              (le_join_left (pt w) _)))
            (le_trans hb₂ (join_le
              (le_trans (le_join_right _ _) (le_join_right (pt w) _))
              (le_join_left (pt w) _))))
      have hkey : ((ln B : PElem P)).meet
          ((pt w).join ((((pt pa₁).join (ln B)).meet ((pt pa₂).join (pt w))).join
            (((ln B).join (pt pa₁)).meet ((pt w).join (pt pb₂))))) =
          (((pt pa₁).join (ln B)).meet ((pt pa₂).join (pt w))).join
            (((ln B).join (pt pa₁)).meet ((pt w).join (pt pb₂))) := by
        rw [modular_eq hR, meet_ln_pt_not hwB, bot_join]
      have hfin : (((pt pa₁ : PElem P).join (pt pa₁)).meet ((pt pa₂).join (pt pb₂))).le
          ((((pt pa₁).join (ln B)).meet ((pt pa₂).join (pt w))).join
            (((ln B).join (pt pa₁)).meet ((pt w).join (pt pb₂)))) :=
        hkey ▸ le_meet hLHS_lnB h2
      exact hfin
    · -- `pa₁ ∈ B`, `pb₁ ∉ B`: absorption on the `a`-side
      have htop : ((ln B : PElem P).join (pt pb₁)) = top := by
        rw [join_comm]; exact join_ln_top_of_le lb₁ hAB hpb₁
      have ha₂ : (pt pa₂ : PElem P).le
          ((((pt pa₁).join (ln B)).meet ((pt pa₂).join (pt w))).join (pt w)) := by
        rw [mac_join_c₂ hc]; exact le_join_left _ _
      have hwR : (pt w : PElem P).le
          (((ln B).join (pt pb₁)).meet ((pt w).join (pt pb₂))) :=
        le_meet (by rw [htop]; exact le_top _) (le_join_left _ _)
      have hb₂R : (pt pb₂ : PElem P).le
          (((ln B).join (pt pb₁)).meet ((pt w).join (pt pb₂))) :=
        le_meet (by rw [htop]; exact le_top _) (le_join_right _ _)
      exact le_trans (meet_le_right _ _)
        (join_le
          (le_trans ha₂ (join_le (le_join_left _ _)
            (le_trans hwR (le_join_right _ _))))
          (le_trans hb₂R (le_join_right _ _)))
  · by_cases hpb₁ : (pt pb₁ : PElem P).le (ln B)
    · -- `pa₁ ∉ B`, `pb₁ ∈ B`: absorption on the `b`-side
      have htop : ((pt pa₁ : PElem P).join (ln B)) = top :=
        join_ln_top_of_le la₁ hAB hpa₁
      have hb₂ : (pt pb₂ : PElem P).le
          ((((ln B).join (pt pb₁)).meet ((pt w).join (pt pb₂))).join (pt w)) := by
        rw [topjoin_absorb hc]; exact le_join_right _ _
      have hwR : (pt w : PElem P).le
          (((pt pa₁).join (ln B)).meet ((pt pa₂).join (pt w))) :=
        le_meet (by rw [htop]; exact le_top _) (le_join_right _ _)
      have ha₂R : (pt pa₂ : PElem P).le
          (((pt pa₁).join (ln B)).meet ((pt pa₂).join (pt w))) :=
        le_meet (by rw [htop]; exact le_top _) (le_join_left _ _)
      exact le_trans (meet_le_right _ _)
        (join_le (le_trans ha₂R (le_join_left _ _))
          (le_trans hb₂ (join_le (le_join_right _ _)
            (le_trans hwR (le_join_left _ _)))))
    · -- both off `B`: right
      exact hornConc_of_right
        (by rw [join_ln_top_of_le la₁ hAB hpa₁]; exact le_top _)
        (by rw [join_comm (ln B) (pt pb₁), join_ln_top_of_le lb₁ hAB hpb₁]
            exact le_top _)

/-! ## `⊤`-column wrappers and the `KC = ⊤` shape

  Each wrapper peels any `ln A` entry (via `hornConc_*_topc`, using the LINE
  entry to reach `⊤`) and extracts the point columns for the generic leaf.  For
  `(ln B, pt w)` with `w ∈ A` the point columns cannot be peeled uniformly, so
  that sub-case is closed by `HornConc.mono_c` from `horn_shape_lll` at the
  smaller `c`-column `(A∩B, w)` (whose join is `ln A`). -/

/-- `c = (ln B, ln B')` with `B ≠ B'` and `a,b` columns spanning `ln A`. -/
theorem bigshape_lnln {a₁ a₂ b₁ b₂ : PElem P} {A B B' : P.Line}
    (hKA : a₁.join a₂ = ln A) (hKB : b₁.join b₂ = ln A) (hBB : B ≠ B') :
    HornConc a₁ a₂ b₁ b₂ (ln B) (ln B') := by
  have ha₁ : a₁.le (ln A) := hKA ▸ le_join_left a₁ a₂
  have ha₂ : a₂.le (ln A) := hKA ▸ le_join_right a₁ a₂
  have hb₁ : b₁.le (ln A) := hKB ▸ le_join_left b₁ b₂
  have hb₂ : b₂.le (ln A) := hKB ▸ le_join_right b₁ b₂
  by_cases hBA : B = A
  · subst hBA; exact hornConc_c₁_ln ha₂ hb₂
  by_cases hB'A : B' = A
  · subst hB'A; exact hornConc_c₂_ln ha₁ hb₁
  have hAB : A ≠ B := fun h => hBA h.symm
  have hAB' : A ≠ B' := fun h => hB'A h.symm
  by_cases haa1 : a₁ = ln A
  · subst haa1; exact hornConc_a₁_topc (join_ln_ln_ne hAB) (join_ln_ln_ne hBB)
  by_cases haa2 : a₂ = ln A
  · subst haa2; exact hornConc_a₂_topc (join_ln_ln_ne hAB') (join_ln_ln_ne hBB)
  by_cases hba1 : b₁ = ln A
  · subst hba1; exact hornConc_b₁_topc (join_ln_ln_ne hAB) (join_ln_ln_ne hBB)
  by_cases hba2 : b₂ = ln A
  · subst hba2; exact hornConc_b₂_topc (join_ln_ln_ne hAB') (join_ln_ln_ne hBB)
  obtain ⟨pa₁, ea₁, ia₁⟩ := pt_of_le_ln_ne ha₁
    (fun h => haa2 (by rw [h, bot_join] at hKA; exact hKA)) haa1
  obtain ⟨pa₂, ea₂, ia₂⟩ := pt_of_le_ln_ne ha₂
    (fun h => haa1 (by rw [h, join_bot_right] at hKA; exact hKA)) haa2
  obtain ⟨pb₁, eb₁, ib₁⟩ := pt_of_le_ln_ne hb₁
    (fun h => hba2 (by rw [h, bot_join] at hKB; exact hKB)) hba1
  obtain ⟨pb₂, eb₂, ib₂⟩ := pt_of_le_ln_ne hb₂
    (fun h => hba1 (by rw [h, join_bot_right] at hKB; exact hKB)) hba2
  subst ea₁ ea₂ eb₁ eb₂
  exact horn_lines_bb' ia₁ ia₂ ib₁ ib₂ hAB hAB' hBB

/-- `c = (ln B, pt w)` with `w ∉ B` and `a,b` columns spanning `ln A`. -/
theorem bigshape_lnpt {a₁ a₂ b₁ b₂ : PElem P} {A B : P.Line} {w : P.Point}
    (hKA : a₁.join a₂ = ln A) (hKB : b₁.join b₂ = ln A) (hwB : ¬ P.incid w B) :
    HornConc a₁ a₂ b₁ b₂ (ln B) (pt w) := by
  have ha₁ : a₁.le (ln A) := hKA ▸ le_join_left a₁ a₂
  have ha₂ : a₂.le (ln A) := hKA ▸ le_join_right a₁ a₂
  have hb₁ : b₁.le (ln A) := hKB ▸ le_join_left b₁ b₂
  have hb₂ : b₂.le (ln A) := hKB ▸ le_join_right b₁ b₂
  by_cases hBA : B = A
  · subst hBA; exact hornConc_c₁_ln ha₂ hb₂
  have hAB : A ≠ B := fun h => hBA h.symm
  have hc : ((ln B : PElem P)).join (pt w) = top := join_ln_pt_not hwB
  by_cases hwA : P.incid w A
  · -- w ∈ A: `HornConc.mono_c` from `horn_shape_lll` at `(A∩B, w)`
    have iqA : P.incid (P.meetPoint A B) A := P.meetPoint_incid_left A B
    have iqB : P.incid (P.meetPoint A B) B := P.meetPoint_incid_right A B
    have hqw : P.meetPoint A B ≠ w := fun h => hwB (h ▸ iqB)
    exact HornConc.mono_c
      (show (pt (P.meetPoint A B) : PElem P).le (ln B) from iqB) (le_refl (pt w))
      (horn_shape_lll hKA hKB (join_pt_pt_line hqw iqA hwA))
  · -- w ∉ A: peel `ln A` entries, then the all-points leaf
    by_cases haa1 : a₁ = ln A
    · subst haa1; exact hornConc_a₁_topc (join_ln_ln_ne hAB) hc
    by_cases haa2 : a₂ = ln A
    · subst haa2; exact hornConc_a₂_topc (join_ln_pt_not hwA) hc
    by_cases hba1 : b₁ = ln A
    · subst hba1; exact hornConc_b₁_topc (join_ln_ln_ne hAB) hc
    by_cases hba2 : b₂ = ln A
    · subst hba2; exact hornConc_b₂_topc (join_ln_pt_not hwA) hc
    obtain ⟨pa₁, ea₁, ia₁⟩ := pt_of_le_ln_ne ha₁
      (fun h => haa2 (by rw [h, bot_join] at hKA; exact hKA)) haa1
    obtain ⟨pa₂, ea₂, ia₂⟩ := pt_of_le_ln_ne ha₂
      (fun h => haa1 (by rw [h, join_bot_right] at hKA; exact hKA)) haa2
    obtain ⟨pb₁, eb₁, ib₁⟩ := pt_of_le_ln_ne hb₁
      (fun h => hba2 (by rw [h, bot_join] at hKB; exact hKB)) hba1
    obtain ⟨pb₂, eb₂, ib₂⟩ := pt_of_le_ln_ne hb₂
      (fun h => hba1 (by rw [h, join_bot_right] at hKB; exact hKB)) hba2
    subst ea₁ ea₂ eb₁ eb₂
    exact horn_line_ptw ia₁ ia₂ ib₁ ib₂ hAB hwB

/-- **SHAPE `KA = KB = ln A`, `KC = ⊤`**: split the `⊤`-column by
    `join_top_cases`, closing a single `⊤` entry by the prunings and the three
    big shapes by the wrappers above. -/
theorem horn_shape_llt {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P} {A : P.Line}
    (hKA : a₁.join a₂ = ln A) (hKB : b₁.join b₂ = ln A) (hKC : c₁.join c₂ = top) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  rcases join_top_cases hKC with (h | h) | ⟨v, B, ec₁, ec₂, hvB⟩ |
    ⟨B, w, ec₁, ec₂, hwB⟩ | ⟨B, B', ec₁, ec₂, hBB⟩
  · have hc₂ : c₂ = top := by rw [← join_eq_of_le_right h]; exact hKC
    subst hc₂; exact hornConc_top_c₂ a₁ a₂ b₁ b₂ c₁
  · have hc₁ : c₁ = top := by rw [← join_eq_of_le_left h]; exact hKC
    subst hc₁; exact hornConc_top_c₁ a₁ a₂ b₁ b₂ c₂
  · subst ec₁; subst ec₂
    exact HornConc.of_swap_idx (bigshape_lnpt
      (by rw [join_comm]; exact hKA) (by rw [join_comm]; exact hKB) hvB)
  · subst ec₁; subst ec₂; exact bigshape_lnpt hKA hKB hwB
  · subst ec₁; subst ec₂; exact bigshape_lnln hKA hKB hBB

/-! ## Machinery for the `KB = ⊤` shape

  The `⊤`-column `b` occurs on BOTH sides of the conclusion, so the peeling
  route of `KC = ⊤` does not transfer.  We split `b` by `join_top_cases`; the
  two comparable cases give a `⊤` entry (closed by `horn_top_b₁/₂`), and the
  three big shapes need incidence.  Workhorses below: the `c₁ ⊔ c₂`-relative
  `M_ac` absorptions (needing only `a₁, a₂ ⩽ c₁ ⊔ c₂`, NOT `c₁ ⊔ c₂ = ⊤`) and
  the coatom evaluation. -/

/-- ABSORPTION (`M_ac`, `c₂`-side), needing only `a₁, a₂ ⩽ c₁ ⊔ c₂`:
    `((a₁ ⊔ c₁) ⊓ (a₂ ⊔ c₂)) ⊔ c₂ = a₂ ⊔ c₂`. -/
theorem mac_join_c₂' {a₁ a₂ c₁ c₂ : PElem P}
    (ha₁ : a₁.le (c₁.join c₂)) (ha₂ : a₂.le (c₁.join c₂)) :
    ((a₁.join c₁).meet (a₂.join c₂)).join c₂ = a₂.join c₂ := by
  have hbig : (a₁.join c₁).join c₂ = c₁.join c₂ := by
    apply le_antisymm
    · exact join_le (join_le ha₁ (le_join_left c₁ c₂)) (le_join_right c₁ c₂)
    · exact join_le (le_trans (le_join_right a₁ c₁) (le_join_left (a₁.join c₁) c₂))
        (le_join_right (a₁.join c₁) c₂)
  calc ((a₁.join c₁).meet (a₂.join c₂)).join c₂
      = (a₂.join c₂).meet ((a₁.join c₁).join c₂) := by
        rw [meet_comm (a₁.join c₁) (a₂.join c₂), ← modular_eq (le_join_right a₂ c₂)]
    _ = (a₂.join c₂).meet (c₁.join c₂) := by rw [hbig]
    _ = a₂.join c₂ := (le_iff_meet_eq.mp (join_le ha₂ (le_join_right c₁ c₂))).symm ▸ rfl

/-- ABSORPTION (`M_ac`, `c₁`-side), the mirror of `mac_join_c₂'`. -/
theorem mac_join_c₁' {a₁ a₂ c₁ c₂ : PElem P}
    (ha₁ : a₁.le (c₁.join c₂)) (ha₂ : a₂.le (c₁.join c₂)) :
    ((a₁.join c₁).meet (a₂.join c₂)).join c₁ = a₁.join c₁ := by
  rw [meet_comm]
  exact mac_join_c₂' (c₁ := c₂) (c₂ := c₁) (by rw [join_comm]; exact ha₂)
    (by rw [join_comm]; exact ha₁)


/-- If `c₂ ⩽ ln B` but `a₂ ⋠ ln B` (and `a₁, a₂ ⩽ c₁ ⊔ c₂`), then
    `M_ac ⊔ ln B = ⊤` (the `M_ac`-`c₂` absorption lifts `a₂ ⊔ c₂` to `⊤`). -/
theorem mac_join_ln_top_2 {a₁ a₂ c₁ c₂ : PElem P} {B : P.Line}
    (ha₁ : a₁.le (c₁.join c₂)) (ha₂ : a₂.le (c₁.join c₂))
    (hc2 : c₂.le (ln B)) (hA2 : ¬ a₂.le (ln B)) :
    ((a₁.join c₁).meet (a₂.join c₂)).join (ln B) = top := by
  apply le_antisymm (le_top _)
  rw [← join_ln_top_of_not_le hA2]
  have step1 : a₂.le (((a₁.join c₁).meet (a₂.join c₂)).join (ln B)) := by
    refine le_trans ?_ (join_mono (le_refl _) hc2)
    rw [mac_join_c₂' ha₁ ha₂]; exact le_join_left a₂ c₂
  exact join_le step1 (le_join_right _ _)

/-- The `c₁`/`ln A` mirror of `mac_join_ln_top_2`. -/
theorem mac_join_ln_top_1 {a₁ a₂ c₁ c₂ : PElem P} {A : P.Line}
    (ha₁ : a₁.le (c₁.join c₂)) (ha₂ : a₂.le (c₁.join c₂))
    (hc1 : c₁.le (ln A)) (hA1 : ¬ a₁.le (ln A)) :
    ((a₁.join c₁).meet (a₂.join c₂)).join (ln A) = top := by
  apply le_antisymm (le_top _)
  rw [← join_ln_top_of_not_le hA1]
  have step1 : a₁.le (((a₁.join c₁).meet (a₂.join c₂)).join (ln A)) := by
    refine le_trans ?_ (join_mono (le_refl _) hc1)
    rw [mac_join_c₁' ha₁ ha₂]; exact le_join_left a₁ c₁
  exact join_le step1 (le_join_right _ _)

/-- `x = y → x ⩽ y` (mathlib-free). -/
theorem le_of_eq' {x y : PElem P} (h : x = y) : x.le y := h ▸ le_refl x

/-- **Incidence core of the `(ln A, ln B)` shape**: `c₁ ⩽ ln A ∧ c₂ ⩽ ln B`, so
    `M_cb = ln A ⊓ ln B = A∩B`.  A `le_ln_cases` bash on `(c₁, c₂)`: the pure-`ln`
    combos close by a modular pull (rewriting a coatom as `c ⊔ (A∩B)` and pulling
    `A∩B` out through modularity); the two-point combo splits on `p ∈ B`, `q ∈ A`
    (`p = A∩B`, `q = A∩B` collapse the join to a line), the generic sub-case
    (`p ∉ B`, `q ∉ A`) closing by `shear_of_disjoint` since then `A∩B ∉ p⊔q`. -/
theorem hkb_lnln_TT {a₁ a₂ c₁ c₂ : PElem P} {A B : P.Line} (hAB : A ≠ B)
    (ha1 : a₁.le (c₁.join c₂)) (ha2 : a₂.le (c₁.join c₂))
    (hc1 : c₁.le (ln A)) (hc2 : c₂.le (ln B)) :
    ((a₁.join (ln A)).meet (a₂.join (ln B))).le
      (((a₁.join c₁).meet (a₂.join c₂)).join ((c₁.join (ln A)).meet (c₂.join (ln B)))) := by
  have imA : P.incid (P.meetPoint A B) A := P.meetPoint_incid_left A B
  have imB : P.incid (P.meetPoint A B) B := P.meetPoint_incid_right A B
  have hpmA : (pt (P.meetPoint A B) : PElem P).le (ln A) := imA
  have hpmB : (pt (P.meetPoint A B) : PElem P).le (ln B) := imB
  have hMcb : (c₁.join (ln A)).meet (c₂.join (ln B)) = pt (P.meetPoint A B) := by
    rw [join_eq_of_le_right hc1, join_eq_of_le_right hc2, meet_ln_ln_ne hAB]
  rw [hMcb]
  have pmLe1 : (pt (P.meetPoint A B) : PElem P).le (a₁.join (ln A)) :=
    le_trans hpmA (le_join_right a₁ (ln A))
  have pmLe2 : (pt (P.meetPoint A B) : PElem P).le (a₂.join (ln B)) :=
    le_trans hpmB (le_join_right a₂ (ln B))
  rcases le_ln_cases hc1 with rfl | ⟨p, rfl, hpA⟩ | rfl
  · rw [bot_join] at ha1 ha2
    rcases le_ln_cases hc2 with rfl | ⟨q, rfl, hqB⟩ | rfl
    · obtain rfl := eq_bot_of_le_bot ha1; obtain rfl := eq_bot_of_le_bot ha2
      rw [bot_join, bot_join, meet_ln_ln_ne hAB]; exact le_join_right _ _
    · have hqB' : (pt q : PElem P).le (ln B) := hqB
      have ha1B : a₁.le (ln B) := le_trans ha1 hqB'
      rw [join_bot_right, join_eq_of_le_right ha2, le_iff_meet_eq.mp ha1,
        join_eq_of_le_right (le_trans ha2 hqB'), meet_comm (a₁.join (ln A)) (ln B),
        join_comm a₁ (ln A), modular_eq ha1B, meet_comm (ln B) (ln A), meet_ln_ln_ne hAB]
      exact join_le (le_join_right _ _) (le_join_left _ _)
    · rw [join_bot_right, join_eq_of_le_right ha2, le_iff_meet_eq.mp ha1,
        meet_comm (a₁.join (ln A)) (ln B), join_comm a₁ (ln A),
        modular_eq ha1, meet_comm (ln B) (ln A), meet_ln_ln_ne hAB]
      exact join_le (le_join_right _ _) (le_join_left _ _)
  · rcases le_ln_cases hc2 with rfl | ⟨q, rfl, hqB⟩ | rfl
    · rw [join_bot_right] at ha1 ha2
      have hpA' : (pt p : PElem P).le (ln A) := hpA
      have ha2A : a₂.le (ln A) := le_trans ha2 hpA'
      rw [join_bot_right, join_eq_of_le_right ha1, meet_comm (pt p) a₂, le_iff_meet_eq.mp ha2,
        join_eq_of_le_right (le_trans ha1 hpA'), join_comm a₂ (ln B), modular_eq ha2A,
        meet_ln_ln_ne hAB]
      exact join_le (le_join_right _ _) (le_join_left _ _)
    · by_cases hpB : (pt p : PElem P).le (ln B)
      · by_cases hqA : (pt q : PElem P).le (ln A)
        · have ha1A : a₁.le (ln A) := le_trans ha1 (join_le hpA hqA)
          have ha2B : a₂.le (ln B) := le_trans ha2 (join_le hpB hqB)
          rw [join_eq_of_le_right ha1A, join_eq_of_le_right ha2B, meet_ln_ln_ne hAB]
          exact le_join_right _ _
        · have hpm : p = P.meetPoint A B := by
            have h : (pt p : PElem P).le ((ln A).meet (ln B)) := le_meet hpA hpB
            rw [meet_ln_ln_ne hAB] at h; exact h
          subst hpm
          have ha1B : a₁.le (ln B) := le_trans ha1 (join_le hpmB hqB)
          have ha2B : a₂.le (ln B) := le_trans ha2 (join_le hpmB hqB)
          have hqne : q ≠ P.meetPoint A B := fun h => hqA (h ▸ imA)
          have hlnB : (pt q : PElem P).join (pt (P.meetPoint A B)) = ln B :=
            join_pt_pt_line hqne hqB imB
          have key : ((a₁.join (pt (P.meetPoint A B))).meet (a₂.join (pt q))).join
              (pt (P.meetPoint A B)) = a₁.join (pt (P.meetPoint A B)) := by
            rw [← modular_eq (le_join_right a₁ (pt (P.meetPoint A B))), ← join_assoc, hlnB,
              join_eq_of_le_right ha2B, le_iff_meet_eq.mp (join_le ha1B hpmB)]
          rw [key, join_eq_of_le_right ha2B, meet_comm (a₁.join (ln A)) (ln B),
            join_comm a₁ (ln A), modular_eq ha1B, meet_comm (ln B) (ln A), meet_ln_ln_ne hAB]
          exact join_le (le_join_right _ _) (le_join_left _ _)
      · by_cases hqA : (pt q : PElem P).le (ln A)
        · have hqm : q = P.meetPoint A B := by
            have h : (pt q : PElem P).le ((ln A).meet (ln B)) := le_meet hqA hqB
            rw [meet_ln_ln_ne hAB] at h; exact h
          subst hqm
          have ha1A : a₁.le (ln A) := le_trans ha1 (join_le hpA hpmA)
          have ha2A : a₂.le (ln A) := le_trans ha2 (join_le hpA hpmA)
          have hpne : p ≠ P.meetPoint A B := fun h => hpB (h ▸ imB)
          have hlnA : (pt p : PElem P).join (pt (P.meetPoint A B)) = ln A :=
            join_pt_pt_line hpne hpA imA
          have key : ((a₁.join (pt p)).meet (a₂.join (pt (P.meetPoint A B)))).join
              (pt (P.meetPoint A B)) = a₂.join (pt (P.meetPoint A B)) := by
            rw [meet_comm, ← modular_eq (le_join_right a₂ (pt (P.meetPoint A B))), ← join_assoc,
              hlnA, join_eq_of_le_right ha1A, le_iff_meet_eq.mp (join_le ha2A hpmA)]
          rw [key, join_eq_of_le_right ha1A, join_comm a₂ (ln B), modular_eq ha2A,
            meet_ln_ln_ne hAB]
          exact join_le (le_join_right _ _) (le_join_left _ _)
        · have hpne : p ≠ P.meetPoint A B := fun h => hpB (h ▸ imB)
          have hqne : q ≠ P.meetPoint A B := fun h => hqA (h ▸ imA)
          have hlnA : (pt p : PElem P).join (pt (P.meetPoint A B)) = ln A :=
            join_pt_pt_line hpne hpA imA
          have hlnB : (pt q : PElem P).join (pt (P.meetPoint A B)) = ln B :=
            join_pt_pt_line hqne hqB imB
          have hKtop : (pt p : PElem P).join (pt q) ≠ top := by
            by_cases hpq : p = q
            · subst hpq; rw [join_pt_pt_self]; exact fun h => nomatch h
            · rw [join_pt_pt_ne hpq]; exact fun h => nomatch h
          have hmK : ¬ (pt (P.meetPoint A B) : PElem P).le ((pt p).join (pt q)) := fun hmle =>
            hKtop (by
              apply le_antisymm (le_top _)
              have hlA : (ln A : PElem P).le ((pt p).join (pt q)) := by
                rw [← hlnA]; exact join_le (le_join_left (pt p) (pt q)) hmle
              have hlB : (ln B : PElem P).le ((pt p).join (pt q)) := by
                rw [← hlnB]; exact join_le (le_join_right (pt p) (pt q)) hmle
              rw [← join_ln_ln_ne hAB]; exact join_le hlA hlB)
          have hdis : (pt (P.meetPoint A B) : PElem P).meet
              ((a₁.join (pt p)).join (a₂.join (pt q))) = bot := by
            rcases le_pt_cases (meet_le_left (pt (P.meetPoint A B))
                ((a₁.join (pt p)).join (a₂.join (pt q)))) with h | h
            · exact h
            · exact absurd (h ▸ meet_le_right _ _ :
                (pt (P.meetPoint A B) : PElem P).le _)
                (fun hmle => hmK (le_trans hmle (join_le
                  (join_le ha1 (le_join_left (pt p) (pt q)))
                  (join_le ha2 (le_join_right (pt p) (pt q))))))
          have e1 : a₁.join (ln A) = (pt (P.meetPoint A B)).join (a₁.join (pt p)) := by
            rw [← hlnA, join_assoc, join_comm (a₁.join (pt p)) (pt (P.meetPoint A B))]
          have e2 : a₂.join (ln B) = (pt (P.meetPoint A B)).join (a₂.join (pt q)) := by
            rw [← hlnB, join_assoc, join_comm (a₂.join (pt q)) (pt (P.meetPoint A B))]
          rw [e1, e2]
          exact le_trans (shear_of_disjoint hdis) (join_le (le_join_right _ _) (le_join_left _ _))
    · by_cases hpB : (pt p : PElem P).le (ln B)
      · have ha1B : a₁.le (ln B) := by rw [join_eq_of_le_right hpB] at ha1; exact ha1
        have ha2B : a₂.le (ln B) := by rw [join_eq_of_le_right hpB] at ha2; exact ha2
        rw [join_eq_of_le_right ha2B, meet_comm (a₁.join (ln A)) (ln B), join_comm a₁ (ln A),
          modular_eq ha1B, meet_comm (ln B) (ln A), meet_ln_ln_ne hAB]
        exact join_le (le_join_right _ _)
          (le_trans (le_meet (le_join_left a₁ (pt p)) ha1B) (le_join_left _ _))
      · have hpne : p ≠ P.meetPoint A B := fun h => hpB (h ▸ imB)
        have hlnA : (pt p : PElem P).join (pt (P.meetPoint A B)) = ln A :=
          join_pt_pt_line hpne hpA imA
        rw [meet_comm (a₁.join (pt p)) (a₂.join (ln B)), ← modular_eq pmLe2,
          meet_comm (a₁.join (ln A)) (a₂.join (ln B))]
        exact meet_mono (le_refl _)
          (hlnA ▸ le_of_eq' (join_assoc a₁ (pt p) (pt (P.meetPoint A B))))
  · rcases le_ln_cases hc2 with rfl | ⟨q, rfl, hqB⟩ | rfl
    · rw [join_bot_right] at ha2
      have ha1A : a₁.le (ln A) := by rw [join_bot_right] at ha1; exact ha1
      rw [join_eq_of_le_right ha1A, join_bot_right, meet_comm (ln A) a₂, le_iff_meet_eq.mp ha2,
        join_comm a₂ (ln B), modular_eq ha2, meet_ln_ln_ne hAB]
      exact join_le (le_join_right _ _) (le_join_left _ _)
    · by_cases hqA : (pt q : PElem P).le (ln A)
      · have ha1A : a₁.le (ln A) := by rw [join_eq_of_le_left hqA] at ha1; exact ha1
        have ha2A : a₂.le (ln A) := by rw [join_eq_of_le_left hqA] at ha2; exact ha2
        rw [join_eq_of_le_right ha1A, join_comm a₂ (ln B), modular_eq ha2A, meet_ln_ln_ne hAB]
        exact join_le (le_join_right _ _)
          (le_trans (le_meet ha2A (le_join_left a₂ (pt q))) (le_join_left _ _))
      · have hqne : q ≠ P.meetPoint A B := fun h => hqA (h ▸ imA)
        have hlnB : (pt q : PElem P).join (pt (P.meetPoint A B)) = ln B :=
          join_pt_pt_line hqne hqB imB
        rw [← modular_eq pmLe1]
        exact meet_mono (le_refl _)
          (hlnB ▸ le_of_eq' (join_assoc a₂ (pt q) (pt (P.meetPoint A B))))
    · exact le_join_left _ _

/-- **Big `b`-shape `(ln A, ln B)`, `A ≠ B`.**  Split the two coatom conditions
    `c₁ ⩽ ln A`, `c₂ ⩽ ln B`.  Three configs close by the modular core; the
    fourth (`c₁ ⩽ ln A ∧ c₂ ⩽ ln B`, so `M_cb = A∩B`) is the incidence core
    `hkb_lnln_TT`. -/
theorem hkb_lnln {a₁ a₂ c₁ c₂ : PElem P} {A B : P.Line} (hAB : A ≠ B)
    (ha : (a₁.join a₂).le (c₁.join c₂)) :
    HornConc a₁ a₂ (ln A) (ln B) c₁ c₂ := by
  have ha1 : a₁.le (c₁.join c₂) := le_trans (le_join_left a₁ a₂) ha
  have ha2 : a₂.le (c₁.join c₂) := le_trans (le_join_right a₁ a₂) ha
  show ((a₁.join (ln A)).meet (a₂.join (ln B))).le
    (((a₁.join c₁).meet (a₂.join c₂)).join ((c₁.join (ln A)).meet (c₂.join (ln B))))
  by_cases hc1 : c₁.le (ln A)
  · by_cases hc2 : c₂.le (ln B)
    · exact hkb_lnln_TT hAB ha1 ha2 hc1 hc2
    · by_cases hA1 : a₁.le (ln A)
      · refine hornConc_of_le_cb (le_meet ?_ (by rw [join_ln_top_of_not_le hc2]; exact le_top _))
        rw [join_eq_of_le_right hc1]
        exact le_trans (meet_le_left _ _) (by rw [join_eq_of_le_right hA1]; exact le_refl _)
      · have hMcb : (c₁.join (ln A)).meet (c₂.join (ln B)) = ln A := by
          rw [join_ln_top_of_not_le hc2, meet_top_right, join_eq_of_le_right hc1]
        rw [hMcb, mac_join_ln_top_1 ha1 ha2 hc1 hA1]; exact le_top _
  · by_cases hc2 : c₂.le (ln B)
    · by_cases hA2 : a₂.le (ln B)
      · refine hornConc_of_le_cb (le_meet (by rw [join_ln_top_of_not_le hc1]; exact le_top _) ?_)
        rw [join_eq_of_le_right hc2]
        exact le_trans (meet_le_right _ _) (by rw [join_eq_of_le_right hA2]; exact le_refl _)
      · have hMcb : (c₁.join (ln A)).meet (c₂.join (ln B)) = ln B := by
          rw [join_ln_top_of_not_le hc1, meet_top_left, join_eq_of_le_right hc2]
        rw [hMcb, mac_join_ln_top_2 ha1 ha2 hc2 hA2]; exact le_top _
    · refine hornConc_of_le_cb (le_meet (by rw [join_ln_top_of_not_le hc1]; exact le_top _)
        (by rw [join_ln_top_of_not_le hc2]; exact le_top _))

/-- ATOM ABSORPTION: an atom `pt w` below a join `a ⊔ (pt w) ⊔ c` but with `a ⋠ c`
    is already below `a ⊔ c` (the `⊥` alternative forces `a ⩽ c`). -/
theorem atom_absorb {a c : PElem P} {w : P.Point} (h : a.le ((pt w).join c))
    (hac : ¬ a.le c) : (pt w : PElem P).le (a.join c) := by
  rcases le_pt_cases (meet_le_left (pt w) (a.join c)) with hbot | hpt
  · exfalso
    apply hac
    have hle : (a.join c).le ((pt w).join c) := join_le h (le_join_right (pt w) c)
    have heq : (a.join c).meet ((pt w).join c) = c := by
      rw [modular_eq (le_join_right a c), meet_comm (a.join c) (pt w), hbot, bot_join]
    rw [le_iff_meet_eq.mp hle] at heq
    exact le_trans (le_join_left a c) (le_of_eq' heq)
  · exact hpt ▸ meet_le_right (pt w) (a.join c)

/-- **Incidence core of `(pt v, ln B)`**: `c₂ ⩽ ln B` but `a₂ ⋠ ln B` (so
    `c₁ ⊔ ln B = ⊤`).  Case `c₁`: `⊥` is impossible; `⊤` and `ln C` with `v ∉ C`
    give `M_cb = ln B` (so `M_ac ⊔ ln B = ⊤`); `pt w` (`w ∉ B`) closes by the atom
    absorption (`pt w ⩽ M_ac`); `ln C` with `v ∈ C` reduces to `hkb_lnln`, since
    there `ln C ⊔ pt v = ln C` makes `M_cb` and the RHS coincide with the two-line
    shape while the LHS only shrinks. -/
theorem hkb_ptln_c2 {a₁ a₂ c₁ c₂ : PElem P} {v : P.Point} {B : P.Line}
    (ha1 : a₁.le (c₁.join c₂)) (ha2 : a₂.le (c₁.join c₂))
    (hc2 : c₂.le (ln B)) (hA2 : ¬ a₂.le (ln B)) :
    ((a₁.join (pt v)).meet (a₂.join (ln B))).le
      (((a₁.join c₁).meet (a₂.join c₂)).join ((c₁.join (pt v)).meet (c₂.join (ln B)))) := by
  have hc1B : ¬ c₁.le (ln B) := fun h => hA2 (le_trans ha2 (join_le h hc2))
  cases c₁ with
  | bot => exact absurd (bot_le (ln B)) hc1B
  | top =>
    have hMcb : (top.join (pt v)).meet (c₂.join (ln B)) = ln B := by
      rw [join_top_left, meet_top_left, join_eq_of_le_right hc2]
    rw [hMcb, mac_join_ln_top_2 ha1 ha2 hc2 hA2]; exact le_top _
  | pt w =>
    have hbLw : (ln B : PElem P).join (pt w) = top := by
      rw [join_comm]; exact join_ln_top_of_not_le hc1B
    have haw : (pt w : PElem P).le (a₂.join c₂) :=
      atom_absorb ha2 (fun h => hA2 (le_trans h hc2))
    have hpwR : (pt w : PElem P).le (((a₁.join (pt w)).meet (a₂.join c₂)).join
        (((pt w).join (pt v)).meet (c₂.join (ln B)))) :=
      le_trans (le_meet (le_join_right a₁ (pt w)) haw) (le_join_left _ _)
    have hMcbw : (((pt w).join (pt v)).meet (c₂.join (ln B))).join (pt w) =
        (pt w).join (pt v) := by
      rw [← modular_eq (le_join_left (pt w) (pt v)), ← join_assoc, hbLw, join_top_right,
        meet_top_right]
    refine le_trans (meet_le_left _ _) (join_le ?_ ?_)
    · exact le_trans (le_join_left a₁ (pt w)) (le_trans (le_of_eq' (mac_join_c₁' ha1 ha2).symm)
        (join_le (le_join_left _ _) hpwR))
    · exact le_trans (le_join_right (pt w) (pt v)) (le_trans (le_of_eq' hMcbw.symm)
        (join_le (le_join_right _ _) hpwR))
  | ln C =>
    by_cases hvC : (pt v : PElem P).le (ln C)
    · rw [join_ln_pt_incid hvC]
      refine le_trans (meet_mono (join_mono (le_refl a₁) hvC) (le_refl (a₂.join (ln B)))) ?_
      have hcb : C ≠ B := hc1B
      have hlnln : ((a₁.join (ln C)).meet (a₂.join (ln B))).le
          (((a₁.join (ln C)).meet (a₂.join c₂)).join
            (((ln C).join (ln C)).meet (c₂.join (ln B)))) := hkb_lnln hcb (join_le ha1 ha2)
      rw [join_idem] at hlnln
      exact hlnln
    · have hMcb : ((ln C).join (pt v)).meet (c₂.join (ln B)) = ln B := by
        rw [join_ln_pt_not hvC, meet_top_left, join_eq_of_le_right hc2]
      rw [hMcb, mac_join_ln_top_2 ha1 ha2 hc2 hA2]; exact le_top _

/-- **Big `b`-shape `(pt v, ln B)`, `v ∉ B`.**  The atom `pt v` is on the `1`-
    column, the coatom `ln B` on the `2`-column.  Split `c₂ ⩽ ln B`: the negative
    config drops `M_cb` to `c₁ ⊔ pt v` (closed by the `M_ac`-`c₁` absorption); the
    positive config with `a₂ ⩽ ln B` closes by a coatom shear (`M_ac, M_cb ⩽ ln B`,
    `pt v ⊓ ln B = ⊥`), and with `a₂ ⋠ ln B` by the incidence core `hkb_ptln_c2`. -/
theorem hkb_ptln {a₁ a₂ c₁ c₂ : PElem P} {v : P.Point} {B : P.Line}
    (hvB : ¬ P.incid v B) (ha : (a₁.join a₂).le (c₁.join c₂)) :
    HornConc a₁ a₂ (pt v) (ln B) c₁ c₂ := by
  have hbv : ((ln B : PElem P)).meet (pt v) = bot := meet_ln_pt_not hvB
  have hbLv : (ln B : PElem P).join (pt v) = top := by rw [join_comm]; exact join_pt_ln_not hvB
  have ha1 : a₁.le (c₁.join c₂) := le_trans (le_join_left a₁ a₂) ha
  have ha2 : a₂.le (c₁.join c₂) := le_trans (le_join_right a₁ a₂) ha
  show ((a₁.join (pt v)).meet (a₂.join (ln B))).le
    (((a₁.join c₁).meet (a₂.join c₂)).join ((c₁.join (pt v)).meet (c₂.join (ln B))))
  by_cases hc2 : c₂.le (ln B)
  · by_cases hA2 : a₂.le (ln B)
    · -- coatom shear: `M_ac, M_cb ⩽ ln B`, `pt v ⊓ ln B = ⊥`
      have hMcbv : ((c₁.join (pt v)).meet (c₂.join (ln B))).join (pt v) = c₁.join (pt v) := by
        rw [← modular_eq (le_join_right c₁ (pt v)), ← join_assoc, hbLv, join_top_right,
          meet_top_right]
      have hMacB : ((a₁.join c₁).meet (a₂.join c₂)).le (ln B) :=
        le_trans (meet_le_right _ _) (join_le hA2 hc2)
      have hMcbB : ((c₁.join (pt v)).meet (c₂.join (ln B))).le (ln B) :=
        le_trans (meet_le_right _ _) (join_le hc2 (le_refl (ln B)))
      have hRHSB := join_le hMacB hMcbB
      have htB : ((a₁.join (pt v)).meet (a₂.join (ln B))).le (ln B) :=
        le_trans (meet_le_right _ _) (join_le hA2 (le_refl (ln B)))
      have hc1RHS : c₁.le ((pt v).join (((a₁.join c₁).meet (a₂.join c₂)).join
          ((c₁.join (pt v)).meet (c₂.join (ln B))))) :=
        le_trans (le_join_left c₁ (pt v)) (le_trans (le_of_eq' hMcbv.symm)
          (le_trans (join_mono (le_join_right _ _) (le_refl (pt v)))
            (le_of_eq' (join_comm _ (pt v)))))
      have htv : ((a₁.join (pt v)).meet (a₂.join (ln B))).le
          ((pt v).join (((a₁.join c₁).meet (a₂.join c₂)).join
            ((c₁.join (pt v)).meet (c₂.join (ln B))))) := by
        refine le_trans (meet_le_left _ _) (join_le ?_ (le_join_left (pt v) _))
        exact le_trans (le_join_left a₁ c₁) (le_trans (le_of_eq' (mac_join_c₁' ha1 ha2).symm)
          (join_le (le_trans (le_join_left _ _) (le_join_right (pt v) _)) hc1RHS))
      have key : (ln B : PElem P).meet ((pt v).join (((a₁.join c₁).meet (a₂.join c₂)).join
          ((c₁.join (pt v)).meet (c₂.join (ln B))))) =
          ((a₁.join c₁).meet (a₂.join c₂)).join ((c₁.join (pt v)).meet (c₂.join (ln B))) := by
        rw [modular_eq hRHSB, hbv, bot_join]
      exact key ▸ le_meet htB htv
    · exact hkb_ptln_c2 ha1 ha2 hc2 hA2
  · -- `¬ c₂ ⩽ ln B`: `M_cb = c₁ ⊔ pt v`
    have hMcb : (c₁.join (pt v)).meet (c₂.join (ln B)) = c₁.join (pt v) := by
      rw [join_ln_top_of_not_le hc2, meet_top_right]
    rw [hMcb]
    refine le_trans (meet_le_left _ _) (join_le ?_ ?_)
    · exact le_trans (le_join_left a₁ c₁) (le_trans (le_of_eq' (mac_join_c₁' ha1 ha2).symm)
        (join_mono (le_refl _) (le_join_left c₁ (pt v))))
    · exact le_trans (le_join_right c₁ (pt v)) (le_join_right _ _)

/-- **The `KB = ⊤` shape** (`b₁ ⊔ b₂ = ⊤`, `a₁ ⊔ a₂ ⩽ c₁ ⊔ c₂`).  Split the
    `⊤` `b`-column by `join_top_cases`. -/
theorem horn_KB_top {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P} (hb : b₁.join b₂ = top)
    (ha : (a₁.join a₂).le (c₁.join c₂)) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  have hHyp : HornHyp a₁ a₂ b₁ b₂ c₁ c₂ := by
    show ((a₁.join a₂).meet (b₁.join b₂)).le (c₁.join c₂)
    rw [hb, meet_top_right]; exact ha
  rcases join_top_cases hb with (h | h) | ⟨v, B, eb₁, eb₂, hvB⟩ |
    ⟨A, w, eb₁, eb₂, hwA⟩ | ⟨A, B, eb₁, eb₂, hAB⟩
  · have hb₂ : b₂ = top := by rw [← join_eq_of_le_right h]; exact hb
    subst hb₂; exact horn_top_b₂ hHyp
  · have hb₁ : b₁ = top := by rw [← join_eq_of_le_left h]; exact hb
    subst hb₁; exact horn_top_b₁ hHyp
  · subst eb₁; subst eb₂; exact hkb_ptln hvB ha
  · subst eb₁; subst eb₂
    exact HornConc.of_swap_idx
      (hkb_ptln hwA (by rw [join_comm a₂ a₁, join_comm c₂ c₁]; exact ha))
  · subst eb₁; subst eb₂; exact hkb_lnln hAB ha

/-- **§2.157 `famC`**: the line-degeneracy of the converse Horn sentence — the
    obligation of `latticeHorn_of_families`. -/
theorem hornLine_famC : ∀ (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P) (A : P.Line),
    (a₁.join a₂).meet (b₁.join b₂) = ln A →
    HornHyp a₁ a₂ b₁ b₂ c₁ c₂ → HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  intro a₁ a₂ b₁ b₂ c₁ c₂ A hH hHyp
  have h : ((a₁.join a₂).meet (b₁.join b₂)).le (c₁.join c₂) := hHyp
  rcases meet_eq_ln_cases hH with ⟨hKA, hKB⟩ | ⟨hKA, hKB⟩ | ⟨hKA, hKB⟩
  · have hge : (ln A : PElem P).le (c₁.join c₂) := by rw [hH] at h; exact h
    rcases ge_ln_cases hge with hKC | hKC
    · exact horn_shape_lll hKA hKB hKC
    · exact horn_shape_llt hKA hKB hKC
  · have hac : (a₁.join a₂).le (c₁.join c₂) := by
      rw [hKB, meet_top_right] at h; exact h
    exact horn_KB_top hKB hac
  · have hbc : (b₁.join b₂).le (c₁.join c₂) := by
      rw [hKA, meet_top_left] at h; exact h
    exact HornConc.of_swap_ab (horn_KB_top hKA hbc)

end PElem

/-! ## Residual: the `KA = ⊤` / `KB = ⊤` shapes of `famC`

  `hornLine_famC` (the `famC` obligation of `latticeHorn_of_families`) splits by
  `meet_eq_ln_cases` into `(KA, KB) ∈ {(ln A, ln A), (ln A, ⊤), (⊤, ln A)}`, and
  `HornHyp` forces `KC := c₁ ⊔ c₂ ⊒ ln A`.  DISCHARGED IN FULL above:

  · `(ln A, ln A)`, `KC = ln A` — the `M_κ` SUB-CORE `PElem.horn_shape_lll`
    (heart `PElem.horn_atoms`): the roadmap's "pure `M_κ` modular-lattice
    algebra, no Desargues";
  · `(ln A, ln A)`, `KC = ⊤` — `PElem.horn_shape_llt`, the full line/top
    constructor case-bash (`bigshape_lnln`, `bigshape_lnpt`, `horn_lines_bb'`,
    `horn_line_ptw`, plus the `mono_c`-from-`horn_shape_lll` shortcut).

  STILL OPEN — the two shapes with the `⊤` on the `a`- or `b`-column:

  · `(ln A, ⊤)` — `horn_shape_lt`;
  · `(⊤, ln A)` — its `HornConc.of_swap_ab` mirror.

  Both are the single obligation `horn_KB_top`:
  `b₁ ⊔ b₂ = ⊤ → (a₁ ⊔ a₂) ⩽ (c₁ ⊔ c₂) → HornConc a₁ a₂ b₁ b₂ c₁ c₂`
  (`HornHyp` gives exactly `(a₁⊔a₂) ⊓ ⊤ = a₁⊔a₂ ⩽ c₁⊔c₂`).  NO Desargues and NO
  missing plane axiom — but, unlike `KC = ⊤`, the `⊤`-column `b` occurs on BOTH
  sides of the conclusion (in `LHS` and in `M_cb`), so neither the c-monotone
  `HornConc.mono_c` shortcut nor the `hornConc_*_topc` peeling route transfers;
  it needs its own line/top incidence case analysis (a `join_top_cases` split of
  the `b`-column into a `⊤` entry — closed by `horn_top_b₁`/`_b₂` — plus the
  three "big" `b`-shapes, dispatched against the point `a`-column and the
  `⊒ ln A` `c`-column).  Once `horn_shape_lt` is assembled, `hornLine_famC`
  follows by `meet_eq_ln_cases` + `horn_shape_lll`/`horn_shape_llt`/
  `horn_shape_lt` (+ `swap_ab`). -/

end Freyd.Alg
