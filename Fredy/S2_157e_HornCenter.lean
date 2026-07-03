/-
  Freyd & Scedrov, *Categories and Allegories* §2.157 (converse, famB):
  the PERSPECTIVE-CENTRE family — the ONLY family of the literal converse that
  consumes the theorem of Desargues.

  `S2_157c_Converse` reduced the lattice Horn sentence, at an arbitrary 6-tuple
  of 𝓛(P), to three residual shape families keyed on the hypothesis meet
  `H := (a₁⊔a₂) ⊓ (b₁⊔b₂)` (`latticeHorn_of_families`):

  · `H = ⊥` — CLOSED (`horn_core_disjoint`, pure modularity);
  · `H = pt z` — famB, HERE;
  · `H = ln`/`⊤` — famC/famA (line/top degeneracies).

  This file proves famB (`hornCenter_famB`).  With `H = pt z`, the Horn
  hypothesis is `pt z ⩽ c₁ ⊔ c₂`.  We split on where `z` sits:

  · `z ⩽ c₁` or `z ⩽ c₂` — the EASY HALF, `horn_center_under` (c-monotonicity
    onto `horn_center`, already proved in `S2_157c_Converse`);
  · `z` under NEITHER — the RESIDUE, split on the shape of `c₁ ⊔ c₂`:
    - `c₁ ⊔ c₂ = ln D` (a line through `z`, `z` off both entries): this forces
      `c = (pt d₁, pt d₂)` with `d₁ ≠ d₂`, `z ∈ line d₁d₂`, `z ∉ {d₁,d₂}` — THE
      GENUINE DESARGUES INSTANCE, routed through
      `desarguesND_implies_horn_points`;
    - `c₁ ⊔ c₂ = ⊤` (the hypothesis is vacuous): the DEGENERATE families
      `c = (pt,ln)`, `(ln,pt)`, `(ln,ln)` — no Desargues, incidence + modularity.
  The driver `hornCenter_famB_of` records the residue split; the two leaf
  obligations are the genuine-Desargues instance and the ⊤-column degeneracy.
-/
import Fredy.S2_157c_Converse

universe v u

namespace Freyd.Alg

namespace PElem

variable {P : ProjectivePlane.{u}}

/-! ## The residue split: famB from the two leaf obligations

  Given the genuine-Desargues leaf (`c₁ ⊔ c₂` a line through the centre `z`,
  forcing `c` to a distinct-point pair off `z`) and the ⊤-column degeneracy
  leaf, the full `H = pt z` family follows by an elementary case analysis on the
  shape of `c₁ ⊔ c₂` — no geometry beyond axiom 3 in the driver itself. -/

/-- **famB reduced to its two leaves.**  `hDesLeaf` is the genuine-Desargues
    instance at `c = (pt d₁, pt d₂)` with the centre `z` on the line `d₁d₂` but
    distinct from both; `hTop` is the degenerate family where the c-column joins
    to `⊤` (vacuous hypothesis).  The driver splits on the shape of `c₁ ⊔ c₂`:
    `⊥`/`pt` are excluded by the residue, `ln D` feeds `hDesLeaf`, `⊤` feeds
    `hTop`; when `z` already lies under a c-entry the easy half
    (`horn_center_under`) fires. -/
theorem hornCenter_famB_of
    (hDesLeaf : ∀ (a₁ a₂ b₁ b₂ : PElem P) (d₁ d₂ z : P.Point),
        (a₁.join a₂).meet (b₁.join b₂) = pt z →
        d₁ ≠ d₂ → z ≠ d₁ → z ≠ d₂ → P.incid z (P.lineThrough d₁ d₂) →
        HornConc a₁ a₂ b₁ b₂ (pt d₁) (pt d₂))
    (hTop : ∀ (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P) (z : P.Point),
        (a₁.join a₂).meet (b₁.join b₂) = pt z →
        c₁.join c₂ = top →
        HornConc a₁ a₂ b₁ b₂ c₁ c₂) :
    ∀ (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P) (z : P.Point),
      (a₁.join a₂).meet (b₁.join b₂) = pt z →
      HornHyp a₁ a₂ b₁ b₂ c₁ c₂ → HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  intro a₁ a₂ b₁ b₂ c₁ c₂ z hH hHyp
  -- the Horn hypothesis, with `H = pt z`, says the centre lies under `c₁ ⊔ c₂`
  have hz_le : (pt z : PElem P).le (c₁.join c₂) := by
    have h0 : ((a₁.join a₂).meet (b₁.join b₂)).le (c₁.join c₂) := hHyp
    rwa [hH] at h0
  -- EASY HALF: `z` under one c-entry reduces to `horn_center`
  by_cases hzc1 : (pt z : PElem P).le c₁
  · exact horn_center_under hH (Or.inl hzc1)
  by_cases hzc2 : (pt z : PElem P).le c₂
  · exact horn_center_under hH (Or.inr hzc2)
  -- RESIDUE: split on the shape of `c₁ ⊔ c₂`
  rcases hCJ : c₁.join c₂ with _ | e | D | _
  · -- `⊥`: `pt z ⩽ ⊥` is impossible
    rw [hCJ] at hz_le; exact absurd hz_le (by simp [le])
  · -- `pt e`: forces `c₁ = c₂ = ⊥`, contradicting `c₁ ⊔ c₂ = pt e`
    exfalso
    rw [hCJ] at hz_le
    have hze : z = e := hz_le
    have hc1 : c₁.le (pt e) := hCJ ▸ le_join_left c₁ c₂
    have hc2 : c₂.le (pt e) := hCJ ▸ le_join_right c₁ c₂
    rcases le_pt_cases hc1 with h1 | h1
    · rcases le_pt_cases hc2 with h2 | h2
      · rw [h1, h2, bot_join] at hCJ; exact nomatch hCJ
      · exact hzc2 (by rw [h2]; exact hze)
    · exact hzc1 (by rw [h1]; exact hze)
  · -- `ln D`: `z ∈ D`, and the residue forces `c = (pt d₁, pt d₂)` on `D`
    rw [hCJ] at hz_le
    have hzD : P.incid z D := hz_le
    have hc1 : c₁.le (ln D) := hCJ ▸ le_join_left c₁ c₂
    have hc2 : c₂.le (ln D) := hCJ ▸ le_join_right c₁ c₂
    rcases le_ln_cases hc1 with h1 | ⟨d₁, hd1eq, hd1D⟩ | h1
    · -- `c₁ = ⊥`: then `c₂ = ln D`, so `z ⩽ c₂` — excluded
      rw [h1, bot_join] at hCJ
      exact absurd (show (pt z : PElem P).le c₂ by rw [hCJ]; exact hzD) hzc2
    · -- `c₁ = pt d₁`, `d₁ ∈ D`, `z ≠ d₁`
      have hzd1 : z ≠ d₁ := fun e => hzc1 (by rw [hd1eq]; exact e)
      rcases le_ln_cases hc2 with h2 | ⟨d₂, hd2eq, hd2D⟩ | h2
      · -- `c₂ = ⊥`: then `c₁ = ln D`, contradicting `c₁ = pt d₁`
        rw [hd1eq, h2, join_bot_right] at hCJ; exact nomatch hCJ
      · -- `c₂ = pt d₂`, `d₂ ∈ D`, `z ≠ d₂`: the genuine instance
        have hzd2 : z ≠ d₂ := fun e => hzc2 (by rw [hd2eq]; exact e)
        rw [hd1eq, hd2eq]
        rw [hd1eq, hd2eq] at hCJ
        by_cases hd12 : d₁ = d₂
        · rw [hd12, join_pt_pt_self] at hCJ; exact nomatch hCJ
        · rw [join_pt_pt_ne hd12] at hCJ
          have hDeq : P.lineThrough d₁ d₂ = D := PElem.ln.inj hCJ
          exact hDesLeaf a₁ a₂ b₁ b₂ d₁ d₂ z hH hd12 hzd1 hzd2
            (by rw [hDeq]; exact hzD)
      · -- `c₂ = ln D`: `z ⩽ c₂` — excluded
        exact absurd (show (pt z : PElem P).le c₂ by rw [h2]; exact hzD) hzc2
    · -- `c₁ = ln D`: `z ⩽ c₁` — excluded
      exact absurd (show (pt z : PElem P).le c₁ by rw [h1]; exact hzD) hzc1
  · -- `⊤`: the degenerate c-column family
    exact hTop a₁ a₂ b₁ b₂ c₁ c₂ z hH hCJ

/-! ## The genuine-Desargues instance (both columns distinct-point pairs)

  When both a- and b-columns are distinct-point pairs spanning distinct lines
  through the centre `z`, and the c-column is a distinct-point pair on a line
  `D` through `z` (off both entries), the Horn conclusion is EXACTLY the theorem
  of Desargues at the six points, extracted by `desarguesND_implies_horn_points`.
  This is the single leaf of the whole converse that consumes `DesarguesND`. -/

open ProjectivePlane in
/-- **The genuine-Desargues leaf, general position.**  Two triangles with
    vertices `x₁,y₁,d₁` and `x₂,y₂,d₂`, perspective from the centre `z`
    (`z ∈ x₁x₂ ∩ y₁y₂`, and `z ∈ d₁d₂`), with all fifteen general-position side
    conditions, satisfy the Horn conclusion — precisely
    `desarguesND_implies_horn_points`, with the Horn hypothesis `pt z ⩽ ln(d₁d₂)`
    supplied from `z ∈ d₁d₂`. -/
theorem hornConc_center_desargues (hDes : P.DesarguesND)
    {x₁ x₂ y₁ y₂ d₁ d₂ z : P.Point}
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) (hd12 : d₁ ≠ d₂)
    (hab₁ : x₁ ≠ y₁) (hac₁ : x₁ ≠ d₁) (hcb₁ : d₁ ≠ y₁)
    (hab₂ : x₂ ≠ y₂) (hac₂ : x₂ ≠ d₂) (hcb₂ : d₂ ≠ y₂)
    (hAB : P.lineThrough x₁ x₂ ≠ P.lineThrough y₁ y₂)
    (hSab : P.lineThrough x₁ y₁ ≠ P.lineThrough x₂ y₂)
    (hSac : P.lineThrough x₁ d₁ ≠ P.lineThrough x₂ d₂)
    (hScb : P.lineThrough d₁ y₁ ≠ P.lineThrough d₂ y₂)
    (hT₁ : P.lineThrough x₁ d₁ ≠ P.lineThrough d₁ y₁)
    (hT₂ : P.lineThrough x₂ d₂ ≠ P.lineThrough d₂ y₂)
    (hzA : P.incid z (P.lineThrough x₁ x₂)) (hzB : P.incid z (P.lineThrough y₁ y₂))
    (hzD : P.incid z (P.lineThrough d₁ d₂)) :
    HornConc (pt x₁) (pt x₂) (pt y₁) (pt y₂) (pt d₁) (pt d₂) := by
  -- the Horn hypothesis: the centre `z = x₁x₂ ∩ y₁y₂` lies on `d₁d₂`
  have hyp : HornHyp (pt x₁) (pt x₂) (pt y₁) (pt y₂) (pt d₁) (pt d₂) := by
    show (((pt x₁).join (pt x₂)).meet ((pt y₁).join (pt y₂))).le
      ((pt d₁).join (pt d₂))
    rw [join_pt_pt_ne hx, join_pt_pt_ne hy, join_pt_pt_ne hd12, meet_ln_ln_ne hAB]
    have hmz : P.meetPoint (P.lineThrough x₁ x₂) (P.lineThrough y₁ y₂) = z :=
      (meetPoint_eq hAB hzA hzB).symm
    rw [hmz]; exact hzD
  exact desarguesND_implies_horn_points hDes x₁ x₂ y₁ y₂ d₁ d₂
    hx hy hd12 hab₁ hac₁ hcb₁ hab₂ hac₂ hcb₂ hAB hSab hSac hScb hT₁ hT₂ hyp

/-! ## The degenerate ⊤-column family (no Desargues)

  When `c₁ ⊔ c₂ = ⊤` the Horn hypothesis `pt z ⩽ ⊤` is vacuous, so the
  conclusion must hold outright.  After the ⊤-entry prunings of
  `S2_157b_Desargues` and the row symmetry, the shapes with `c₁ ⊔ c₂ = ⊤` and
  neither entry `⊤` are `(pt d, ln B)`, `(ln A, pt d)`, `(ln A, ln B)`.  Each
  closes by incidence + modularity; the workhorse is a single geometric shear.
-/

/-- A non-incident join with a line is `⊤`: if `x ⋠ ln A` then `x ⊔ ln A = ⊤`
    (the only three shapes `x ∈ {pt off A, line ≠ A, ⊤}` all overflow). -/
theorem join_ln_top_of_not_le {x : PElem P} {A : P.Line} (h : ¬ x.le (ln A)) :
    x.join (ln A) = top := by
  cases x with
  | bot => exact absurd (bot_le _) h
  | pt p => exact join_pt_ln_not h
  | ln B => exact join_ln_ln_ne h
  | top => rfl

/-- Mirror of `join_ln_top_of_not_le` with the line on the left. -/
theorem join_ln_left_top_of_not_le {x : PElem P} {A : P.Line}
    (h : ¬ x.le (ln A)) : (ln A).join x = top := by
  rw [join_comm]; exact join_ln_top_of_not_le h

/-- **GEOMETRIC SHEAR** (incidence, not just modularity).  For ANY element `m`
    and a LINE `B`: `m ⊓ (p ⊔ q) ⩽ (m ⊓ (p ⊔ B)) ⊔ (m ⊓ (q ⊔ B))`.  Either
    `p ⩽ B` — then `p ⊔ q ⩽ q ⊔ B`, so the whole meet sits under the second
    summand; or `p ⋠ B` — then `p ⊔ B = ⊤` (a line overflows), so the first
    summand is already `m ⊒ m ⊓ (p⊔q)`.  This one fact drives every degenerate
    ⊤-column leaf. -/
theorem geomShear (m : PElem P) (B : P.Line) (p q : PElem P) :
    (m.meet (p.join q)).le
      ((m.meet (p.join (ln B))).join (m.meet (q.join (ln B)))) := by
  by_cases hp : p.le (ln B)
  · exact le_trans (meet_mono (le_refl _)
      (join_le (le_trans hp (le_join_right q (ln B))) (le_join_left q (ln B))))
      (le_join_right _ _)
  · rw [join_ln_top_of_not_le hp, meet_top_right]
    exact le_trans (meet_le_left _ _) (le_join_left _ _)

/-- **POINT-SLOT SHEAR.**  The `(pt d, ln B)` shape needs the mirror of
    `geomShear` where the extra element is the point `pt d` *off* the line `B`.
    The line-overflow trick fails (a point does not overflow), but a single
    modular identity closes it uniformly: writing `rᵢ := ln B ⊓ (·⊔pt d)`, one
    has `rᵢ ⊔ pt d = · ⊔ pt d` (since `ln B ⊔ pt d = ⊤`), so
    `p⊔q ⩽ (r₁⊔r₂) ⊔ pt d`; and `ln B ⊓ ((r₁⊔r₂) ⊔ pt d) = r₁⊔r₂` because
    `ln B ⊓ pt d = ⊥` (`d ∉ B`) and `r₁⊔r₂ ⩽ ln B` (modular law, `b ⩽ a`). -/
theorem geomShearPt {d : P.Point} {B : P.Line} (hd : ¬ P.incid d B) (p q : PElem P) :
    ((ln B).meet (p.join q)).le
      (((ln B).meet (p.join (pt d))).join ((ln B).meet (q.join (pt d)))) := by
  -- abbreviations (spelled out; `set` is unavailable mathlib-free)
  have hbd : (ln B).join (pt d) = top := join_ln_pt_not hd
  -- rᵢ ⊔ pt d = · ⊔ pt d, from `ln B ⊔ pt d = ⊤` and one modular shear
  have e1 : p.join (pt d) = ((ln B).meet (p.join (pt d))).join (pt d) := by
    have h := modular_eq (a := p.join (pt d)) (b := ln B) (c := pt d)
      (le_join_right p (pt d))
    rw [hbd, meet_top_right, meet_comm] at h; exact h
  have e2 : q.join (pt d) = ((ln B).meet (q.join (pt d))).join (pt d) := by
    have h := modular_eq (a := q.join (pt d)) (b := ln B) (c := pt d)
      (le_join_right q (pt d))
    rw [hbd, meet_top_right, meet_comm] at h; exact h
  have hrr : (((ln B).meet (p.join (pt d))).join
      ((ln B).meet (q.join (pt d)))).le (ln B) :=
    join_le (meet_le_left _ _) (meet_le_left _ _)
  -- p ⊔ q ⩽ (r₁ ⊔ r₂) ⊔ pt d  (using `p ⩽ p⊔pt d = r₁⊔pt d`, via e1/e2)
  have hpq : (p.join q).le ((((ln B).meet (p.join (pt d))).join
      ((ln B).meet (q.join (pt d)))).join (pt d)) :=
    join_le
      (le_trans (e1 ▸ le_join_left p (pt d))
        (join_mono (le_join_left _ _) (le_refl (pt d))))
      (le_trans (e2 ▸ le_join_left q (pt d))
        (join_mono (le_join_right _ _) (le_refl (pt d))))
  -- ln B ⊓ ((r₁⊔r₂) ⊔ pt d) = r₁⊔r₂  (modular, r₁⊔r₂ ⩽ ln B; ln B ⊓ pt d = ⊥)
  have hcomm : (((ln B).meet (p.join (pt d))).join
        ((ln B).meet (q.join (pt d)))).join (pt d)
      = (pt d).join (((ln B).meet (p.join (pt d))).join
        ((ln B).meet (q.join (pt d)))) := join_comm _ _
  have final := meet_mono (le_refl (ln B)) hpq
  rw [hcomm, modular_eq hrr, meet_ln_pt_not hd, bot_join] at final
  exact final

/-- **Shape `(ln A, ln B)`, `A ≠ B`.**  No hypothesis on `a,b` is needed (the
    conclusion is unconditional here).  Three structural cases: `a₁,b₁ ⩽ A`
    (`geomShear` on the second row), `a₂,b₂ ⩽ B` (`geomShear` on the first row),
    else one conclusion meet dominates a full line making the join `⊤`. -/
theorem hornConc_ln_ln (a₁ a₂ b₁ b₂ : PElem P) {A B : P.Line} (hAB : A ≠ B) :
    HornConc a₁ a₂ b₁ b₂ (ln A) (ln B) := by
  show ((a₁.join b₁).meet (a₂.join b₂)).le
    (((a₁.join (ln A)).meet (a₂.join (ln B))).join
      (((ln A).join b₁).meet ((ln B).join b₂)))
  by_cases ha1 : a₁.le (ln A)
  · by_cases hb1 : b₁.le (ln A)
    · -- a₁,b₁ ⩽ A: geomShear on the second-row column
      refine le_trans (le_meet (le_trans (meet_le_left _ _) (join_le ha1 hb1))
        (meet_le_right _ _)) ?_
      rw [join_eq_of_le_right ha1, join_eq_of_le_left hb1, join_comm (ln B) b₂]
      exact geomShear (ln A) B a₂ b₂
    · by_cases hb2 : b₂.le (ln B)
      · by_cases ha2 : a₂.le (ln B)
        · -- a₂,b₂ ⩽ B: geomShear on the first-row column
          refine le_trans (le_meet (meet_le_left _ _)
            (le_trans (meet_le_right _ _) (join_le ha2 hb2))) ?_
          rw [join_eq_of_le_right ha2, join_eq_of_le_left hb2,
            meet_comm (a₁.join b₁) (ln B), meet_comm (a₁.join (ln A)) (ln B),
            meet_comm ((ln A).join b₁) (ln B), join_comm (ln A) b₁]
          exact geomShear (ln B) A a₁ b₁
        · -- a₁⩽A, ¬b₁⩽A, ¬a₂⩽B, b₂⩽B: M₁ = ln A, M₂ ⊒ ln B, join = ⊤
          rw [join_eq_of_le_right ha1, join_ln_top_of_not_le ha2, meet_top_right,
            join_ln_left_top_of_not_le hb1, meet_top_left, join_assoc,
            join_ln_ln_ne hAB, join_top_left]
          exact le_top _
      · -- ¬b₁⩽A, ¬b₂⩽B: M₂ = ⊤
        rw [join_ln_left_top_of_not_le hb1, join_ln_left_top_of_not_le hb2,
          meet_top_left, join_top_right]
        exact le_top _
  · by_cases ha2 : a₂.le (ln B)
    · by_cases hb2 : b₂.le (ln B)
      · -- a₂,b₂ ⩽ B: geomShear on the first-row column
        refine le_trans (le_meet (meet_le_left _ _)
          (le_trans (meet_le_right _ _) (join_le ha2 hb2))) ?_
        rw [join_eq_of_le_right ha2, join_eq_of_le_left hb2,
          meet_comm (a₁.join b₁) (ln B), meet_comm (a₁.join (ln A)) (ln B),
          meet_comm ((ln A).join b₁) (ln B), join_comm (ln A) b₁]
        exact geomShear (ln B) A a₁ b₁
      · by_cases hb1 : b₁.le (ln A)
        · -- ¬a₁⩽A, a₂⩽B, ¬b₂⩽B, b₁⩽A: M₁ ⊒ ln B, M₂ = ln A, join = ⊤
          rw [join_ln_top_of_not_le ha1, meet_top_left, join_eq_of_le_left hb1,
            join_ln_left_top_of_not_le hb2, meet_top_right, ← join_assoc,
            join_ln_ln_ne (fun h => hAB h.symm), join_top_right]
          exact le_top _
        · -- ¬b₁⩽A, ¬b₂⩽B: M₂ = ⊤
          rw [join_ln_left_top_of_not_le hb1, join_ln_left_top_of_not_le hb2,
            meet_top_left, join_top_right]
          exact le_top _
    · -- ¬a₁⩽A, ¬a₂⩽B: M₁ = ⊤
      rw [join_ln_top_of_not_le ha1, join_ln_top_of_not_le ha2, meet_top_left,
        join_top_left]
      exact le_top _

/-- **Shape `(pt d, ln B)`, `d ∉ B`.**  When `a₂, b₂ ⩽ B` the meet sits under
    `ln B` and `geomShearPt` closes it; otherwise `d ∉ B` makes `Mᵢ ⊔ pt d`
    absorb (`M₁ ⊔ pt d = a₁ ⊔ pt d`, `M₂ ⊔ pt d = b₁ ⊔ pt d`, by one modular
    shear each), so `M₁ ⊔ M₂ ⊒ a₁ ⊔ b₁ ⊒` the conclusion LHS. -/
theorem hornConc_pt_ln (a₁ a₂ b₁ b₂ : PElem P) {d : P.Point} {B : P.Line}
    (hd : ¬ P.incid d B) : HornConc a₁ a₂ b₁ b₂ (pt d) (ln B) := by
  have hbd : (ln B).join (pt d) = top := join_ln_pt_not hd
  -- unconditional absorptions Mᵢ ⊔ pt d = (a₁/b₁) ⊔ pt d
  have idM1 : ((a₁.join (pt d)).meet (a₂.join (ln B))).join (pt d) = a₁.join (pt d) := by
    rw [← modular_eq (le_join_right a₁ (pt d)), ← join_assoc, hbd, join_top_right,
      meet_top_right]
  have htop2 : ((ln B).join b₂).join (pt d) = top := by
    rw [join_comm (ln B) b₂, ← join_assoc, hbd, join_top_right]
  have idM2 : (((pt d).join b₁).meet ((ln B).join b₂)).join (pt d) = b₁.join (pt d) := by
    rw [← modular_eq (le_join_left (pt d) b₁), htop2, meet_top_right, join_comm (pt d) b₁]
  -- easy branch: pt d ⩽ M₁ ⊔ M₂ ⟹ M₁ ⊔ M₂ ⊒ a₁ ⊔ b₁ ⊒ LHS
  have heasy : (pt d : PElem P).le
      (((a₁.join (pt d)).meet (a₂.join (ln B))).join
        (((pt d).join b₁).meet ((ln B).join b₂))) →
      HornConc a₁ a₂ b₁ b₂ (pt d) (ln B) := by
    intro hpt
    show ((a₁.join b₁).meet (a₂.join b₂)).le
      (((a₁.join (pt d)).meet (a₂.join (ln B))).join
        (((pt d).join b₁).meet ((ln B).join b₂)))
    refine le_trans (meet_le_left _ _) (join_le ?_ ?_)
    · have key1 : (a₁ : PElem P).le
          (((a₁.join (pt d)).meet (a₂.join (ln B))).join (pt d)) := by
        rw [idM1]; exact le_join_left a₁ (pt d)
      exact le_trans key1 (join_le (le_join_left _ _) hpt)
    · have key2 : (b₁ : PElem P).le
          ((((pt d).join b₁).meet ((ln B).join b₂)).join (pt d)) := by
        rw [idM2]; exact le_join_left b₁ (pt d)
      exact le_trans key2 (join_le (le_join_right _ _) hpt)
  by_cases ha2 : a₂.le (ln B)
  · by_cases hb2 : b₂.le (ln B)
    · -- a₂,b₂ ⩽ B: meet under ln B, geomShearPt
      show ((a₁.join b₁).meet (a₂.join b₂)).le _
      refine le_trans (le_meet (meet_le_left _ _)
        (le_trans (meet_le_right _ _) (join_le ha2 hb2))) ?_
      rw [join_eq_of_le_right ha2, join_eq_of_le_left hb2,
        meet_comm (a₁.join b₁) (ln B), meet_comm (a₁.join (pt d)) (ln B),
        meet_comm ((pt d).join b₁) (ln B), join_comm (pt d) b₁]
      exact geomShearPt hd a₁ b₁
    · exact heasy (le_trans (le_meet (le_join_left (pt d) b₁)
        (by rw [join_ln_left_top_of_not_le hb2]; exact le_top _)) (le_join_right _ _))
  · exact heasy (le_trans (le_meet (le_join_right a₁ (pt d))
      (by rw [join_ln_top_of_not_le ha2]; exact le_top _)) (le_join_left _ _))

/-- **The ⊤-column leaf (`hTop`), unconditional in `a,b`.**  When `c₁ ⊔ c₂ = ⊤`
    the Horn hypothesis is vacuous; the conclusion holds by `join_top_cases`:
    a `⊤` entry is the ⊤-prunings of `S2_157b_Desargues`, and the three genuine
    shapes are the two degenerate leaves (`(ln,pt)` via the row symmetry). -/
theorem hornConc_top_col (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P) (hc : c₁.join c₂ = top) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  rcases join_top_cases hc with (h | h) | ⟨v, C, rfl, rfl, hvC⟩ |
    ⟨C, w, rfl, rfl, hwC⟩ | ⟨A, B, rfl, rfl, hAB⟩
  · rw [(join_eq_of_le_right h).symm.trans hc]; exact hornConc_top_c₂ a₁ a₂ b₁ b₂ c₁
  · rw [(join_eq_of_le_left h).symm.trans hc]; exact hornConc_top_c₁ a₁ a₂ b₁ b₂ c₂
  · exact hornConc_pt_ln a₁ a₂ b₁ b₂ hvC
  · exact HornConc.of_swap_idx (hornConc_pt_ln a₂ a₁ b₂ b₁ hwC)
  · exact hornConc_ln_ln a₁ a₂ b₁ b₂ hAB

/-! ## The chain leaf of the Desargues family (Cluster 1, DESARGUES-FREE)

  When one of the a,b columns is a CHAIN (comparable pair) the Horn conclusion at
  `c = (pt d₁, pt d₂)` follows by pure modularity + one incidence fact: the centre
  `z` lies on the line `d₁d₂`, so `a₁ ⊔ pt d₁ ⊒ pt z ⊔ pt d₁ = ln(d₁d₂) ∋ d₂`,
  hence the "`pt d₂`-excess" of the b-column shear is absorbed by the a-column
  conclusion meet `M₁`.  No triangle, no Desargues — only the plane's uniqueness
  axiom through `join_pt_pt_line`. -/

/-- **C3 SHEAR** (pure modularity): `(d₁⊔d₂⊔b₁) ⊓ b₂ ⩽ M₂ ⊔ pt d₂`, where
    `M₂ = (d₁⊔b₁) ⊓ (d₂⊔b₂)` is the second conclusion meet.  One modular shear
    factoring `pt d₂` out of the `(d₂⊔b₂)` side. -/
theorem c3shear (b₁ b₂ : PElem P) (d₁ d₂ : P.Point) :
    ((((pt d₁).join (pt d₂)).join b₁).meet b₂).le
      ((((pt d₁).join b₁).meet ((pt d₂).join b₂)).join (pt d₂)) := by
  have h1 : ((((pt d₁).join (pt d₂)).join b₁).meet b₂).le
      (((pt d₂).join b₂).meet (((pt d₁).join b₁).join (pt d₂))) := by
    apply le_meet
    · exact le_trans (meet_le_right _ _) (le_join_right _ _)
    · refine le_trans (meet_le_left _ _) (join_le (join_le ?_ ?_) ?_)
      · exact le_trans (le_join_left (pt d₁) b₁) (le_join_left _ _)
      · exact le_join_right _ _
      · exact le_trans (le_join_right (pt d₁) b₁) (le_join_left _ _)
  rw [modular_eq (le_join_left (pt d₂) b₂),
    meet_comm ((pt d₂).join b₂) ((pt d₁).join b₁)] at h1
  exact h1

/-- **The coupled shear (Cluster 1 crux).**  For `pt z ⩽ a₁` and the centre `z`
    on the line `d₁d₂` (off both, `d₁ ≠ d₂`): the reduced b-column meet
    `V' = (pt z ⊔ b₁) ⊓ b₂` sits under `M₁ ⊔ M₂`.  The `pt d₂`-excess produced by
    `c3shear` is absorbed by `M₁`, since `a₁ ⊔ pt d₁ ⊒ pt z ⊔ pt d₁ = ln(d₁d₂)`
    already contains `d₂`. -/
theorem cruxDesLeaf (a₁ a₂ b₁ b₂ : PElem P) (z d₁ d₂ : P.Point)
    (hza1 : (pt z : PElem P).le a₁)
    (hzD : (pt z : PElem P).le ((pt d₁).join (pt d₂)))
    (hzd1 : z ≠ d₁) (hd12 : d₁ ≠ d₂) :
    (((pt z).join b₁).meet b₂).le
      ((((a₁.join (pt d₁)).meet (a₂.join (pt d₂)))).join
        (((pt d₁).join b₁).meet ((pt d₂).join b₂))) := by
  have hV : (((pt z).join b₁).meet b₂).le
      ((((pt d₁).join (pt d₂)).join b₁).meet b₂) :=
    meet_mono (join_mono hzD (le_refl _)) (le_refl _)
  have hV2 : (((pt z).join b₁).meet b₂).le
      ((((pt d₁).join b₁).meet ((pt d₂).join b₂)).join (pt d₂)) :=
    le_trans hV (c3shear b₁ b₂ d₁ d₂)
  have hzinc : P.incid z (P.lineThrough d₁ d₂) := by rwa [join_pt_pt_ne hd12] at hzD
  have hzd1line : (pt z).join (pt d₁) = ln (P.lineThrough d₁ d₂) :=
    join_pt_pt_line hzd1 hzinc (P.lineThrough_incid_left d₁ d₂)
  have hlnD_le : (ln (P.lineThrough d₁ d₂) : PElem P).le (a₁.join (pt d₁)) := by
    rw [← hzd1line]; exact join_mono hza1 (le_refl _)
  have hd2lnD : (pt d₂ : PElem P).le (ln (P.lineThrough d₁ d₂)) :=
    P.lineThrough_incid_right d₁ d₂
  have hd2M1 : (pt d₂ : PElem P).le ((a₁.join (pt d₁)).meet (a₂.join (pt d₂))) :=
    le_meet (le_trans hd2lnD hlnD_le) (le_join_right a₂ (pt d₂))
  exact le_trans hV2 (join_le (le_join_right _ _) (le_trans hd2M1 (le_join_left _ _)))

/-- **The chain leaf, canonical form** (`a₂ ⩽ a₁`): the whole conclusion follows
    from `cruxDesLeaf`.  `W` splits as `V ⊔ a₂` (modular); `a₂ ⩽ M₁`; and the
    tight meet `a₁ ⊓ (b₁⊔b₂) = pt z` shears `V` down to `V' = (pt z⊔b₁)⊓b₂`,
    closed by `cruxDesLeaf`. -/
theorem chainDesLeaf (a₁ a₂ b₁ b₂ : PElem P) (z d₁ d₂ : P.Point)
    (hchain : a₂.le a₁)
    (hmeet : a₁.meet (b₁.join b₂) = pt z)
    (hzD : (pt z : PElem P).le ((pt d₁).join (pt d₂)))
    (hzd1 : z ≠ d₁) (hd12 : d₁ ≠ d₂) :
    HornConc a₁ a₂ b₁ b₂ (pt d₁) (pt d₂) := by
  have hza1 : (pt z : PElem P).le a₁ := by
    have := meet_le_left a₁ (b₁.join b₂); rwa [hmeet] at this
  show ((a₁.join b₁).meet (a₂.join b₂)).le
    (((a₁.join (pt d₁)).meet (a₂.join (pt d₂))).join
      (((pt d₁).join b₁).meet ((pt d₂).join b₂)))
  have hW : (a₁.join b₁).meet (a₂.join b₂) = ((a₁.join b₁).meet b₂).join a₂ := by
    rw [join_comm a₂ b₂, modular_eq (le_trans hchain (le_join_left a₁ b₁))]
  have hVshear : ((a₁.join b₁).meet b₂).le (((pt z).join b₁).meet b₂) := by
    apply le_meet _ (meet_le_right _ _)
    have h1 : ((a₁.join b₁).meet b₂).le ((b₁.join b₂).meet (a₁.join b₁)) :=
      le_meet (le_trans (meet_le_right _ _) (le_join_right b₁ b₂)) (meet_le_left _ _)
    rw [modular_eq (le_join_left b₁ b₂), meet_comm (b₁.join b₂) a₁, hmeet] at h1
    exact h1
  have ha2M1 : a₂.le ((a₁.join (pt d₁)).meet (a₂.join (pt d₂))) :=
    le_meet (le_trans hchain (le_join_left a₁ (pt d₁))) (le_join_left a₂ (pt d₂))
  rw [hW]
  exact join_le
    (le_trans hVshear (cruxDesLeaf a₁ a₂ b₁ b₂ z d₁ d₂ hza1 hzD hzd1 hd12))
    (le_trans ha2M1 (le_join_left _ _))

/-- **famB reduced to the single Desargues leaf.**  The ⊤-column leaf `hTop` is
    discharged by `hornConc_top_col`; the whole perspective-centre family thus
    depends only on the genuine-Desargues instance `hDesLeaf`
    (`c = (pt d₁, pt d₂)` with the centre `z` on `d₁d₂`, off both). -/
theorem hornCenter_famB_of_desLeaf
    (hDesLeaf : ∀ (a₁ a₂ b₁ b₂ : PElem P) (d₁ d₂ z : P.Point),
        (a₁.join a₂).meet (b₁.join b₂) = pt z →
        d₁ ≠ d₂ → z ≠ d₁ → z ≠ d₂ → P.incid z (P.lineThrough d₁ d₂) →
        HornConc a₁ a₂ b₁ b₂ (pt d₁) (pt d₂)) :
    ∀ (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P) (z : P.Point),
      (a₁.join a₂).meet (b₁.join b₂) = pt z →
      HornHyp a₁ a₂ b₁ b₂ c₁ c₂ → HornConc a₁ a₂ b₁ b₂ c₁ c₂ :=
  hornCenter_famB_of hDesLeaf
    (fun a₁ a₂ b₁ b₂ c₁ c₂ _ _ hc => hornConc_top_col a₁ a₂ b₁ b₂ c₁ c₂ hc)

/-! ## The genuine-Desargues leaf, ALL configurations (Cluster 2)

  `hornConc_center_desargues` handles the general-position instance (both columns
  distinct-point pairs, all fifteen side conditions).  The remaining degenerate
  instantiations are discharged synthetically (mirroring
  `hornAtPoints_implies_desarguesND`), each producing the Horn lattice inequality
  directly.  By the two symmetries of the sentence (`of_swap_idx`, `of_swap_ab`)
  the eleven degeneracies reduce to four representative chases:
  · `c2_xy_eq`  — a collapsed corresponding side (`x₁ = y₁`) forces `W = ⊥`;
  · `c2_xd_eq`  — a collapsed vertex (`x₁ = d₁`) pins `w, v` onto `d₁y₁`;
  · `c2_flat1`  — a flat triangle (`x₁d₁ = d₁y₁`) is the point-split shear
    `geomShearPt` (off-line case) plus a whole-line collapse (on-line case);
  · `c2_Sac`    — coincident corresponding sides (`x₁d₁ = x₂d₂`) make one meet the
    whole line `L`, the other `⊤`.
  `c2` assembles them; `hDesLeaf` maps the residue split's point-pair leaf here. -/

/-- Two distinct points join in a line symmetric in its endpoints (axiom 3). -/
theorem lineThrough_comm {x y : P.Point} (h : x ≠ y) :
    P.lineThrough x y = P.lineThrough y x :=
  (ProjectivePlane.lineThrough_eq h (P.lineThrough_incid_right y x)
    (P.lineThrough_incid_left y x)).symm

/-- **Degeneracy `x₁ = y₁`** (a collapsed corresponding side).  The centre is
    pinned to `x₁ = y₁` (axiom 3 on the two perspective lines), and lies off
    `x₂y₂`, so the conclusion LHS `W` is `⊥`. -/
theorem c2_xy_eq (x₂ y₂ w d₁ d₂ z : P.Point)
    (hx : w ≠ x₂) (hy : w ≠ y₂)
    (hAB : P.lineThrough w x₂ ≠ P.lineThrough w y₂)
    (hzA : P.incid z (P.lineThrough w x₂)) (hzB : P.incid z (P.lineThrough w y₂)) :
    HornConc (pt w) (pt x₂) (pt w) (pt y₂) (pt d₁) (pt d₂) := by
  have hzw : z = w :=
    ProjectivePlane.eq_of_incid_two_lines hAB hzA hzB
      (P.lineThrough_incid_left w x₂) (P.lineThrough_incid_left w y₂)
  subst hzw
  show (((pt z).join (pt z)).meet ((pt x₂).join (pt y₂))).le _
  rw [join_pt_pt_self]
  have hW : (pt z).meet ((pt x₂).join (pt y₂)) = bot := by
    by_cases hx2y2 : x₂ = y₂
    · rw [hx2y2, join_pt_pt_self, meet_pt_pt_ne hy]
    · rw [join_pt_pt_ne hx2y2]
      apply meet_pt_ln_not
      intro hzL
      have hA : P.lineThrough z x₂ = P.lineThrough x₂ y₂ :=
        (P.unique hzA hzL (P.lineThrough_incid_right z x₂)
          (P.lineThrough_incid_left x₂ y₂)).resolve_left hx
      have hB : P.lineThrough z y₂ = P.lineThrough x₂ y₂ :=
        (P.unique hzB hzL (P.lineThrough_incid_right z y₂)
          (P.lineThrough_incid_right x₂ y₂)).resolve_left hy
      exact hAB (hA.trans hB.symm)
  rw [hW]; exact bot_le _

/-- **Degeneracy `x₁ = d₁`** (a collapsed vertex).  The centre `z` on `x₁x₂` and
    on `d₁d₂` forces `x₂ ∈ d₁d₂`; then the conclusion meets `w` (`= W`) and `v`
    (`= M₂`) both lie on `d₁y₁`, so the excess `pt d₁` is absorbed by `M₁`. -/
theorem c2_xd_eq (x₂ y₁ y₂ d₁ d₂ z : P.Point)
    (hx : d₁ ≠ x₂)
    (hAB : P.lineThrough d₁ x₂ ≠ P.lineThrough y₁ y₂)
    (hzA : P.incid z (P.lineThrough d₁ x₂))
    (hd12 : d₁ ≠ d₂) (hzd1 : z ≠ d₁)
    (hzD : P.incid z (P.lineThrough d₁ d₂)) :
    HornConc (pt d₁) (pt x₂) (pt y₁) (pt y₂) (pt d₁) (pt d₂) := by
  have hAD : P.lineThrough d₁ x₂ = P.lineThrough d₁ d₂ :=
    (P.unique hzA hzD (P.lineThrough_incid_left d₁ x₂)
      (P.lineThrough_incid_left d₁ d₂)).resolve_left hzd1
  have hx2D : (pt x₂ : PElem P).le ((pt d₁).join (pt d₂)) := by
    rw [join_pt_pt_ne hd12]; exact hAD ▸ P.lineThrough_incid_right d₁ x₂
  show (((pt d₁).join (pt y₁)).meet ((pt x₂).join (pt y₂))).le
    ((((pt d₁).join (pt d₁)).meet ((pt x₂).join (pt d₂))).join
      (((pt d₁).join (pt y₁)).meet ((pt d₂).join (pt y₂))))
  by_cases hx2d2 : x₂ = d₂
  · subst hx2d2
    exact le_trans (le_refl _) (le_join_right _ _)
  · have hLx2d2 : P.lineThrough x₂ d₂ = P.lineThrough d₁ d₂ :=
      (ProjectivePlane.lineThrough_eq hx2d2 (hAD ▸ P.lineThrough_incid_right d₁ x₂)
        (P.lineThrough_incid_right d₁ d₂)).symm
    have hd1M1 : (pt d₁ : PElem P).le
        (((pt d₁).join (pt d₁)).meet ((pt x₂).join (pt d₂))) := by
      refine le_meet (le_join_left _ _) ?_
      rw [join_pt_pt_ne hx2d2]
      exact hLx2d2 ▸ P.lineThrough_incid_left d₁ d₂
    have hWshear : (((pt d₁).join (pt y₁)).meet ((pt x₂).join (pt y₂))).le
        ((((pt d₁).join (pt y₁)).meet ((pt d₂).join (pt y₂))).join (pt d₁)) := by
      have hle : (((pt d₁).join (pt y₁)).meet ((pt x₂).join (pt y₂))).le
          (((pt d₁).join (pt y₁)).meet (((pt d₂).join (pt y₂)).join (pt d₁))) := by
        refine le_meet (meet_le_left _ _) ?_
        refine le_trans (meet_le_right _ _) (join_le ?_ ?_)
        · exact le_trans hx2D (join_le (le_join_right _ (pt d₁))
            (le_trans (le_join_left (pt d₂) (pt y₂)) (le_join_left _ (pt d₁))))
        · exact le_trans (le_join_right (pt d₂) (pt y₂)) (le_join_left _ (pt d₁))
      rwa [modular_eq (le_join_left (pt d₁) (pt y₁))] at hle
    exact le_trans hWshear (join_le (le_join_right _ _)
      (le_trans hd1M1 (le_join_left _ _)))

/-- Flat-triangle shear core (flat line `ℓ` explicit).  `d₂ ∉ ℓ` is the genuine
    point-split shear (`geomShearPt`); `d₂ ∈ ℓ` forces `x₂ ∈ ℓ` or `y₂ ∈ ℓ`,
    collapsing one conclusion meet to the whole line `ln ℓ`. -/
theorem flat_core (ℓ : P.Line) (x₂ y₂ d₂ : P.Point) (hxd2 : x₂ ≠ d₂) (hdy2 : d₂ ≠ y₂)
    (hd2imp : P.incid d₂ ℓ → P.incid x₂ ℓ ∨ P.incid y₂ ℓ) :
    ((ln ℓ).meet ((pt x₂).join (pt y₂))).le
      (((ln ℓ).meet ((pt x₂).join (pt d₂))).join ((ln ℓ).meet ((pt d₂).join (pt y₂)))) := by
  by_cases hd2 : P.incid d₂ ℓ
  · rcases hd2imp hd2 with hx2 | hy2
    · rw [join_pt_pt_line hxd2 hx2 hd2, meet_ln_ln_self]
      exact le_trans (meet_le_left _ _) (le_join_left _ _)
    · rw [join_pt_pt_line hdy2 hd2 hy2, meet_ln_ln_self]
      exact le_trans (meet_le_left _ _) (le_join_right _ _)
  · rw [join_comm (pt d₂) (pt y₂)]
    exact geomShearPt hd2 (pt x₂) (pt y₂)

/-- **Degeneracy `x₁d₁ = d₁y₁`** (a flat triangle: `x₁, d₁, y₁` colinear on `ℓ`).
    `W`, `M₁`, `M₂` all meet with `ln ℓ`; `flat_core` closes it, with `x₂ ∈ ℓ ∨
    y₂ ∈ ℓ` (when `d₂ ∈ ℓ`) supplied by the centre `z ∈ ℓ`. -/
theorem c2_flat1 (x₁ x₂ y₁ y₂ d₁ d₂ z : P.Point)
    (hzA : P.incid z (P.lineThrough x₁ x₂)) (hzB : P.incid z (P.lineThrough y₁ y₂))
    (hd12 : d₁ ≠ d₂) (hzD : P.incid z (P.lineThrough d₁ d₂))
    (hac₁ : x₁ ≠ d₁) (hac₂ : x₂ ≠ d₂) (hcb₁ : d₁ ≠ y₁) (hcb₂ : d₂ ≠ y₂)
    (hab₁ : x₁ ≠ y₁)
    (hT₁ : P.lineThrough x₁ d₁ = P.lineThrough d₁ y₁) :
    HornConc (pt x₁) (pt x₂) (pt y₁) (pt y₂) (pt d₁) (pt d₂) := by
  have hx₁ℓ : P.incid x₁ (P.lineThrough x₁ d₁) := P.lineThrough_incid_left x₁ d₁
  have hd₁ℓ : P.incid d₁ (P.lineThrough x₁ d₁) := P.lineThrough_incid_right x₁ d₁
  have hy₁ℓ : P.incid y₁ (P.lineThrough x₁ d₁) := by
    rw [hT₁]; exact P.lineThrough_incid_right d₁ y₁
  have hxy₁ : (pt x₁).join (pt y₁) = ln (P.lineThrough x₁ d₁) :=
    join_pt_pt_line hab₁ hx₁ℓ hy₁ℓ
  have hxd₁ : (pt x₁).join (pt d₁) = ln (P.lineThrough x₁ d₁) :=
    join_pt_pt_line hac₁ hx₁ℓ hd₁ℓ
  have hdy₁ : (pt d₁).join (pt y₁) = ln (P.lineThrough x₁ d₁) :=
    join_pt_pt_line hcb₁ hd₁ℓ hy₁ℓ
  show (((pt x₁).join (pt y₁)).meet ((pt x₂).join (pt y₂))).le
    ((((pt x₁).join (pt d₁)).meet ((pt x₂).join (pt d₂))).join
      (((pt d₁).join (pt y₁)).meet ((pt d₂).join (pt y₂))))
  rw [hxy₁, hxd₁, hdy₁]
  refine flat_core (P.lineThrough x₁ d₁) x₂ y₂ d₂ hac₂ hcb₂ (fun hd2 => ?_)
  have hDℓ : P.lineThrough d₁ d₂ = P.lineThrough x₁ d₁ :=
    (ProjectivePlane.lineThrough_eq hd12 hd₁ℓ hd2).symm
  have hzℓ : P.incid z (P.lineThrough x₁ d₁) := hDℓ ▸ hzD
  by_cases hzx1 : z = x₁
  · right
    have hzy1 : z ≠ y₁ := by rw [hzx1]; exact hab₁
    exact (P.unique hzB hzℓ (P.lineThrough_incid_left y₁ y₂) hy₁ℓ).resolve_left hzy1 ▸
      P.lineThrough_incid_right y₁ y₂
  · left
    exact (P.unique hzA hzℓ (P.lineThrough_incid_left x₁ x₂) hx₁ℓ).resolve_left hzx1 ▸
      P.lineThrough_incid_right x₁ x₂

/-- **Degeneracy `x₁d₁ = x₂d₂`** (coincident corresponding sides).  Then all of
    `x₁,x₂,d₁,d₂` lie on one line `L` and `M₁ = ln L`.  If `y₂ ∈ L` (or `y₁ ∈ L`)
    the LHS `W ⩽ ln L = M₁`; else the second meet `v ∉ L`, so `M₁ ⊔ M₂ = ⊤`. -/
theorem c2_Sac (x₁ x₂ y₁ y₂ d₁ d₂ : P.Point)
    (hd12 : d₁ ≠ d₂)
    (hac₁ : x₁ ≠ d₁) (hac₂ : x₂ ≠ d₂) (hcb₁ : d₁ ≠ y₁) (hcb₂ : d₂ ≠ y₂)
    (hab₁ : x₁ ≠ y₁) (hab₂ : x₂ ≠ y₂)
    (hScb : P.lineThrough d₁ y₁ ≠ P.lineThrough d₂ y₂)
    (hSac : P.lineThrough x₁ d₁ = P.lineThrough x₂ d₂) :
    HornConc (pt x₁) (pt x₂) (pt y₁) (pt y₂) (pt d₁) (pt d₂) := by
  have hx₁L : P.incid x₁ (P.lineThrough x₁ d₁) := P.lineThrough_incid_left x₁ d₁
  have hd₁L : P.incid d₁ (P.lineThrough x₁ d₁) := P.lineThrough_incid_right x₁ d₁
  have hx₂L : P.incid x₂ (P.lineThrough x₁ d₁) := hSac ▸ P.lineThrough_incid_left x₂ d₂
  have hd₂L : P.incid d₂ (P.lineThrough x₁ d₁) := hSac ▸ P.lineThrough_incid_right x₂ d₂
  have hxd₁ : (pt x₁).join (pt d₁) = ln (P.lineThrough x₁ d₁) :=
    join_pt_pt_line hac₁ hx₁L hd₁L
  have hx2d2 : (pt x₂).join (pt d₂) = ln (P.lineThrough x₁ d₁) :=
    join_pt_pt_line hac₂ hx₂L hd₂L
  show (((pt x₁).join (pt y₁)).meet ((pt x₂).join (pt y₂))).le
    ((((pt x₁).join (pt d₁)).meet ((pt x₂).join (pt d₂))).join
      (((pt d₁).join (pt y₁)).meet ((pt d₂).join (pt y₂))))
  rw [hxd₁, hx2d2, meet_ln_ln_self]
  by_cases hy2L : P.incid y₂ (P.lineThrough x₁ d₁)
  · have hx2y2 : (pt x₂).join (pt y₂) = ln (P.lineThrough x₁ d₁) :=
      join_pt_pt_line hab₂ hx₂L hy2L
    exact le_trans (hx2y2 ▸ meet_le_right _ _) (le_join_left _ _)
  · by_cases hy1L : P.incid y₁ (P.lineThrough x₁ d₁)
    · have hx1y1 : (pt x₁).join (pt y₁) = ln (P.lineThrough x₁ d₁) :=
        join_pt_pt_line hab₁ hx₁L hy1L
      exact le_trans (hx1y1 ▸ meet_le_left _ _) (le_join_left _ _)
    · rw [join_pt_pt_ne hcb₁, join_pt_pt_ne hcb₂, meet_ln_ln_ne hScb]
      have hvnotL : ¬ P.incid
          (P.meetPoint (P.lineThrough d₁ y₁) (P.lineThrough d₂ y₂))
          (P.lineThrough x₁ d₁) := by
        intro hvL
        have hvd1 : P.meetPoint (P.lineThrough d₁ y₁) (P.lineThrough d₂ y₂) = d₁ := by
          rcases P.unique (P.meetPoint_incid_left _ _) hvL
            (P.lineThrough_incid_left d₁ y₁) hd₁L with h | h
          · exact h
          · exact absurd (h ▸ P.lineThrough_incid_right d₁ y₁) hy1L
        have hvd2 : P.meetPoint (P.lineThrough d₁ y₁) (P.lineThrough d₂ y₂) = d₂ := by
          rcases P.unique (P.meetPoint_incid_right _ _) hvL
            (P.lineThrough_incid_left d₂ y₂) hd₂L with h | h
          · exact h
          · exact absurd (h ▸ P.lineThrough_incid_right d₂ y₂) hy2L
        exact hd12 (hvd1.symm.trans hvd2)
      rw [join_ln_pt_not hvnotL]
      exact le_top _

/-- Corresponding `x-y` sides are distinct (the derived `hSab`): else all four
    of `x₁,x₂,y₁,y₂` lie on `line x₁y₁`, forcing `x₁x₂ = y₁y₂` (contra `hAB`). -/
theorem c2_Sab (x₁ x₂ y₁ y₂ : P.Point) (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂)
    (hab₁ : x₁ ≠ y₁) (hab₂ : x₂ ≠ y₂)
    (hAB : P.lineThrough x₁ x₂ ≠ P.lineThrough y₁ y₂) :
    P.lineThrough x₁ y₁ ≠ P.lineThrough x₂ y₂ := by
  intro hS
  have hx₂ : P.incid x₂ (P.lineThrough x₁ y₁) := by
    rw [hS]; exact P.lineThrough_incid_left x₂ y₂
  have hy₂ : P.incid y₂ (P.lineThrough x₁ y₁) := by
    rw [hS]; exact P.lineThrough_incid_right x₂ y₂
  have e1 : P.lineThrough x₁ x₂ = P.lineThrough x₁ y₁ :=
    (ProjectivePlane.lineThrough_eq hx (P.lineThrough_incid_left x₁ y₁) hx₂).symm
  have e2 : P.lineThrough y₁ y₂ = P.lineThrough x₁ y₁ :=
    (ProjectivePlane.lineThrough_eq hy (P.lineThrough_incid_right x₁ y₁) hy₂).symm
  exact hAB (e1.trans e2.symm)

/-- **The genuine-Desargues leaf at a point-pair configuration.**  Both columns
    are distinct-point pairs spanning distinct lines through the centre `z`, and
    `c = (pt d₁, pt d₂)` with `z ∈ d₁d₂` off both.  General position feeds
    `hornConc_center_desargues` (the sole consumer of `DesarguesND`); the eleven
    degeneracies reduce, by the sentence's two symmetries, to the four chases
    above (with the both-sides-coincident case excluded by `hAB`). -/
theorem c2 (hDes : P.DesarguesND) (x₁ x₂ y₁ y₂ d₁ d₂ z : P.Point)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂)
    (hAB : P.lineThrough x₁ x₂ ≠ P.lineThrough y₁ y₂)
    (hzA : P.incid z (P.lineThrough x₁ x₂)) (hzB : P.incid z (P.lineThrough y₁ y₂))
    (hd12 : d₁ ≠ d₂) (hzd1 : z ≠ d₁) (hzd2 : z ≠ d₂)
    (hzD : P.incid z (P.lineThrough d₁ d₂)) :
    HornConc (pt x₁) (pt x₂) (pt y₁) (pt y₂) (pt d₁) (pt d₂) := by
  by_cases hab₁ : x₁ = y₁
  · subst hab₁; exact c2_xy_eq x₂ y₂ x₁ d₁ d₂ z hx hy hAB hzA hzB
  by_cases hab₂ : x₂ = y₂
  · subst hab₂
    refine HornConc.of_swap_idx (c2_xy_eq x₁ y₁ x₂ d₂ d₁ z hx.symm (Ne.symm hy) ?_ ?_ ?_)
    · rw [lineThrough_comm (Ne.symm hx), lineThrough_comm (Ne.symm hy)]; exact hAB
    · rw [lineThrough_comm (Ne.symm hx)]; exact hzA
    · rw [lineThrough_comm (Ne.symm hy)]; exact hzB
  by_cases hac₁ : x₁ = d₁
  · subst hac₁; exact c2_xd_eq x₂ y₁ y₂ x₁ d₂ z hx hAB hzA hd12 hzd1 hzD
  by_cases hac₂ : x₂ = d₂
  · subst hac₂
    refine HornConc.of_swap_idx
      (c2_xd_eq x₁ y₂ y₁ x₂ d₁ z (Ne.symm hx) ?_ ?_ (Ne.symm hd12) hzd2 ?_)
    · rw [lineThrough_comm (Ne.symm hx), lineThrough_comm (Ne.symm hy)]; exact hAB
    · rw [lineThrough_comm (Ne.symm hx)]; exact hzA
    · rw [lineThrough_comm (Ne.symm hd12)]; exact hzD
  by_cases hcb₁ : d₁ = y₁
  · subst hcb₁
    exact HornConc.of_swap_ab
      (c2_xd_eq y₂ x₁ x₂ d₁ d₂ z hy (Ne.symm hAB) hzB hd12 hzd1 hzD)
  by_cases hcb₂ : d₂ = y₂
  · subst hcb₂
    refine HornConc.of_swap_ab (HornConc.of_swap_idx
      (c2_xd_eq y₁ x₂ x₁ d₂ d₁ z (Ne.symm hy) ?_ ?_ (Ne.symm hd12) hzd2 ?_))
    · rw [lineThrough_comm (Ne.symm hy), lineThrough_comm (Ne.symm hx)]; exact Ne.symm hAB
    · rw [lineThrough_comm (Ne.symm hy)]; exact hzB
    · rw [lineThrough_comm (Ne.symm hd12)]; exact hzD
  have hSab := c2_Sab x₁ x₂ y₁ y₂ hx hy hab₁ hab₂ hAB
  by_cases hT₁ : P.lineThrough x₁ d₁ = P.lineThrough d₁ y₁
  · exact c2_flat1 x₁ x₂ y₁ y₂ d₁ d₂ z hzA hzB hd12 hzD hac₁ hac₂ hcb₁ hcb₂ hab₁ hT₁
  by_cases hT₂ : P.lineThrough x₂ d₂ = P.lineThrough d₂ y₂
  · refine HornConc.of_swap_idx
      (c2_flat1 x₂ x₁ y₂ y₁ d₂ d₁ z ?_ ?_ (Ne.symm hd12) ?_ hac₂ hac₁ hcb₂ hcb₁ hab₂ hT₂)
    · rw [lineThrough_comm (Ne.symm hx)]; exact hzA
    · rw [lineThrough_comm (Ne.symm hy)]; exact hzB
    · rw [lineThrough_comm (Ne.symm hd12)]; exact hzD
  by_cases hSac : P.lineThrough x₁ d₁ = P.lineThrough x₂ d₂
  · by_cases hScb : P.lineThrough d₁ y₁ = P.lineThrough d₂ y₂
    · exfalso
      have hx₁L : P.incid x₁ (P.lineThrough x₁ d₁) := P.lineThrough_incid_left x₁ d₁
      have hd₁L : P.incid d₁ (P.lineThrough x₁ d₁) := P.lineThrough_incid_right x₁ d₁
      have hx₂L : P.incid x₂ (P.lineThrough x₁ d₁) := hSac ▸ P.lineThrough_incid_left x₂ d₂
      have hd₂L : P.incid d₂ (P.lineThrough x₁ d₁) := hSac ▸ P.lineThrough_incid_right x₂ d₂
      have hdy1L : P.lineThrough d₁ y₁ = P.lineThrough x₁ d₁ :=
        (P.unique (P.lineThrough_incid_left d₁ y₁) hd₁L
          (hScb.symm ▸ P.lineThrough_incid_left d₂ y₂) hd₂L).resolve_left hd12
      have hy₁L : P.incid y₁ (P.lineThrough x₁ d₁) :=
        hdy1L ▸ P.lineThrough_incid_right d₁ y₁
      have hy₂L : P.incid y₂ (P.lineThrough x₁ d₁) := by
        rw [← hdy1L, hScb]; exact P.lineThrough_incid_right d₂ y₂
      exact hAB ((ProjectivePlane.lineThrough_eq hx hx₁L hx₂L).symm.trans
        (ProjectivePlane.lineThrough_eq hy hy₁L hy₂L))
    · exact c2_Sac x₁ x₂ y₁ y₂ d₁ d₂ hd12 hac₁ hac₂ hcb₁ hcb₂ hab₁ hab₂ hScb hSac
  by_cases hScb : P.lineThrough d₁ y₁ = P.lineThrough d₂ y₂
  · refine HornConc.of_swap_ab (c2_Sac y₁ y₂ x₁ x₂ d₁ d₂ hd12
      (Ne.symm hcb₁) (Ne.symm hcb₂) (Ne.symm hac₁) (Ne.symm hac₂)
      (Ne.symm hab₁) (Ne.symm hab₂) ?_ ?_)
    · rw [lineThrough_comm (Ne.symm hac₁), lineThrough_comm (Ne.symm hac₂)]; exact hSac
    · rw [lineThrough_comm (Ne.symm hcb₁), lineThrough_comm (Ne.symm hcb₂)]; exact hScb
  exact hornConc_center_desargues hDes hx hy hd12 hab₁ hac₁ hcb₁ hab₂ hac₂ hcb₂
    hAB hSab hSac hScb hT₁ hT₂ hzA hzB hzD

/-! ## The Desargues leaf, assembled

  The residue split (`hornCenter_famB_of`/`hornCenter_famB_of_desLeaf`) reduced the
  perspective-centre family to ONE obligation: `c = (pt d₁, pt d₂)` with the centre
  `z` on `d₁d₂`, off both.  The a,b columns are split by shape exactly as in
  `horn_center`: chain columns close by `chainDesLeaf` (Cluster 1, modularity), and
  the both-point-pair core closes by `c2` (Cluster 2, the genuine theorem of
  Desargues).  This is the SOLE leaf of the whole converse consuming `DesarguesND`. -/

/-- **The Desargues leaf** (`hDesLeaf`).  For arbitrary a,b columns whose join-meet
    is a single centre `z` on the line `d₁d₂` (distinct from both `d₁, d₂`), the
    Horn conclusion at `c = (pt d₁, pt d₂)` holds: chain columns via `chainDesLeaf`
    (Desargues-free), the both-point-pair core via `c2` (Desargues). -/
theorem hDesLeaf (hDes : P.DesarguesND) :
    ∀ (a₁ a₂ b₁ b₂ : PElem P) (d₁ d₂ z : P.Point),
      (a₁.join a₂).meet (b₁.join b₂) = pt z →
      d₁ ≠ d₂ → z ≠ d₁ → z ≠ d₂ → P.incid z (P.lineThrough d₁ d₂) →
      HornConc a₁ a₂ b₁ b₂ (pt d₁) (pt d₂) := by
  intro a₁ a₂ b₁ b₂ d₁ d₂ z hH hd12 hzd1 hzd2 hzinc
  have hzD : (pt z : PElem P).le ((pt d₁).join (pt d₂)) := by
    rw [join_pt_pt_ne hd12]; exact hzinc
  have hA21 : a₂.le a₁ → HornConc a₁ a₂ b₁ b₂ (pt d₁) (pt d₂) := fun h21 =>
    chainDesLeaf a₁ a₂ b₁ b₂ z d₁ d₂ h21
      (by rw [← join_eq_of_le_left h21]; exact hH) hzD hzd1 hd12
  have hA12 : a₁.le a₂ → HornConc a₁ a₂ b₁ b₂ (pt d₁) (pt d₂) := fun h12 =>
    HornConc.of_swap_idx (chainDesLeaf a₂ a₁ b₂ b₁ z d₂ d₁ h12
      (by rw [join_comm b₂ b₁, ← join_eq_of_le_right h12]; exact hH)
      (by rw [join_comm]; exact hzD) hzd2 (Ne.symm hd12))
  have hB21 : b₂.le b₁ → HornConc a₁ a₂ b₁ b₂ (pt d₁) (pt d₂) := fun h21 =>
    HornConc.of_swap_ab (chainDesLeaf b₁ b₂ a₁ a₂ z d₁ d₂ h21
      (by rw [← join_eq_of_le_left h21, meet_comm]; exact hH) hzD hzd1 hd12)
  have hB12 : b₁.le b₂ → HornConc a₁ a₂ b₁ b₂ (pt d₁) (pt d₂) := fun h12 =>
    HornConc.of_swap_ab (HornConc.of_swap_idx (chainDesLeaf b₂ b₁ a₂ a₁ z d₂ d₁ h12
      (by rw [join_comm a₂ a₁, ← join_eq_of_le_right h12, meet_comm]; exact hH)
      (by rw [join_comm]; exact hzD) hzd2 (Ne.symm hd12)))
  rcases join_chain_or_big a₁ a₂ with h12 | h21 | (⟨A, hA⟩ | hA)
  · exact hA12 h12
  · exact hA21 h21
  · rcases join_ln_cases hA with (h12 | h21) | ⟨x₁, x₂, rfl, rfl, hx, hAeq⟩
    · exact hA12 h12
    · exact hA21 h21
    rcases join_chain_or_big b₁ b₂ with h12 | h21 | (⟨B, hB⟩ | hB)
    · exact hB12 h12
    · exact hB21 h21
    · rcases join_ln_cases hB with (h12 | h21) | ⟨y₁, y₂, rfl, rfl, hy, hBeq⟩
      · exact hB12 h12
      · exact hB21 h21
      rw [hA, hB] at hH
      by_cases hAB : A = B
      · rw [hAB, meet_ln_ln_self] at hH; exact nomatch hH
      · rw [meet_ln_ln_ne hAB] at hH
        have hmz : P.meetPoint A B = z := PElem.pt.inj hH
        have hzA : P.incid z (P.lineThrough x₁ x₂) := by
          rw [← hAeq, ← hmz]; exact P.meetPoint_incid_left A B
        have hzB : P.incid z (P.lineThrough y₁ y₂) := by
          rw [← hBeq, ← hmz]; exact P.meetPoint_incid_right A B
        exact c2 hDes x₁ x₂ y₁ y₂ d₁ d₂ z hx hy (hBeq ▸ hAeq ▸ hAB) hzA hzB
          hd12 hzd1 hzd2 hzinc
    · rw [hA, hB, meet_top_right] at hH; exact nomatch hH
  · rw [hA, meet_top_left] at hH
    rcases le_pt_cases (hH ▸ le_join_left b₁ b₂) with h1 | h1
    · exact hB12 (h1 ▸ bot_le b₂)
    · rcases le_pt_cases (hH ▸ le_join_right b₁ b₂) with h2 | h2
      · exact hB21 (h2 ▸ bot_le b₁)
      · exact hB21 (h2 ▸ h1 ▸ le_refl (pt z))

/-- **§2.157 converse, the perspective-centre family (`famB`).**  With the
    hypothesis meet a single point `z`, the Horn sentence holds at every c-column;
    the sole Desargues consumption is the point-pair leaf.  This type is exactly
    `famB` of `latticeHorn_of_families` (`S2_157c_Converse`). -/
theorem hornCenter_famB (hDes : P.DesarguesND) :
    ∀ (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P) (z : P.Point),
      (a₁.join a₂).meet (b₁.join b₂) = pt z →
      HornHyp a₁ a₂ b₁ b₂ c₁ c₂ → HornConc a₁ a₂ b₁ b₂ c₁ c₂ :=
  fun a₁ a₂ b₁ b₂ c₁ c₂ z hH h =>
    hornCenter_famB_of_desLeaf (hDesLeaf hDes) a₁ a₂ b₁ b₂ c₁ c₂ z hH h

end PElem

end Freyd.Alg
