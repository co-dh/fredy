/-
  Freyd & Scedrov, *Categories and Allegories* §2.157 (converse, `famA`):
  the `H = ⊤` degeneracy of the lattice Horn sentence.

  `latticeHorn_of_families` (in `S2_157c_Converse`) splits the literal converse
  on the shape of the hypothesis meet `H := (a₁⊔a₂) ⊓ (b₁⊔b₂)`.  This file
  supplies the residual family `famA` — the case `H = ⊤`.

  When `H = ⊤` the meet forces BOTH column joins to `⊤` (`meet ⩽` each factor),
  and the Horn HYPOTHESIS `H ⩽ c₁⊔c₂` then forces `c₁⊔c₂ = ⊤` as well.  So all
  three columns `(a₁,a₂)`, `(b₁,b₂)`, `(c₁,c₂)` join to `⊤`: each is a genuine
  "big pair" (a point off a line, or two distinct lines — never a chain, else
  the larger entry would be `⊤`).  With every `⊤`-entry pruned by the §2.157b
  pruning lemmas, all six entries are points or lines, and the conclusion is a
  finite incidence degeneracy: Desargues is NEVER needed (it lives in `famB`,
  `H = pt`).  The case tree runs on the shape of the c-column and closes each
  leaf by one of

  · `topA_S_ac` / `topA_S_cb` — domination: the LHS sits under one conclusion
    meet (used whenever `b_i ⩽ a_i⊔c_i`, in particular when a corner join is
    `⊤`), or
  · a per-incidence `meetPoint`/`lineThrough` chase exhibiting the common line
    on which the two conclusion points already lie.
-/
import Freyd.S2_157c_Converse

universe v u

namespace Freyd.Alg

namespace PElem

variable {P : ProjectivePlane.{u}}

/-! ## Big-pair inversion and the two domination closers -/

/-- A pair joining to `⊤`, with neither entry `⊤`, is one of the three genuine
    "big" shapes: a point off a line (either order) or two distinct lines.  The
    comparable alternatives of `join_top_cases` would force an entry to `⊤`. -/
theorem bigPair_cases {x y : PElem P} (hxy : x.join y = top)
    (hx : x ≠ top) (hy : y ≠ top) :
    (∃ v B, x = pt v ∧ y = ln B ∧ ¬ P.incid v B) ∨
    (∃ A w, x = ln A ∧ y = pt w ∧ ¬ P.incid w A) ∨
    (∃ A B, x = ln A ∧ y = ln B ∧ A ≠ B) := by
  rcases join_top_cases hxy with (hle | hle) | h | h | h
  · exact absurd ((join_eq_of_le_right hle).symm.trans hxy) hy
  · exact absurd ((join_eq_of_le_left hle).symm.trans hxy) hx
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- DOMINATION (a,c side): if each `bᵢ` sits under `aᵢ ⊔ cᵢ` then the LHS sits
    under the first conclusion meet `(a₁⊔c₁) ⊓ (a₂⊔c₂)`.  Trivial whenever a
    corner join `aᵢ ⊔ cᵢ` is `⊤`. -/
theorem topA_S_ac {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (hb1 : b₁.le (a₁.join c₁)) (hb2 : b₂.le (a₂.join c₂)) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ :=
  hornConc_of_le_ac
    (meet_mono (join_le (le_join_left _ _) hb1) (join_le (le_join_left _ _) hb2))

/-- DOMINATION (c,b side): if each `aᵢ` sits under `cᵢ ⊔ bᵢ` then the LHS sits
    under the second conclusion meet `(c₁⊔b₁) ⊓ (c₂⊔b₂)`. -/
theorem topA_S_cb {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (ha1 : a₁.le (c₁.join b₁)) (ha2 : a₂.le (c₂.join b₂)) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ :=
  hornConc_of_le_cb
    (meet_mono (join_le ha1 (le_join_right _ _)) (join_le ha2 (le_join_right _ _)))

/-- DOMINATION (column-2): if `c₁` joins to `⊤` with BOTH `a₁` and `b₁`, then
    both conclusion meets collapse onto their row-2 factors, whose join already
    dominates `a₂⊔b₂ ⊒ LHS`.  (No geometry: `⊤⊓x = x`.) -/
theorem topA_S_col2 {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (hac1 : a₁.join c₁ = top) (hcb1 : c₁.join b₁ = top) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  show ((a₁.join b₁).meet (a₂.join b₂)).le
    (((a₁.join c₁).meet (a₂.join c₂)).join ((c₁.join b₁).meet (c₂.join b₂)))
  rw [hac1, hcb1, meet_top_left, meet_top_left]
  exact le_trans (meet_le_right _ _)
    (join_le (le_trans (le_join_left a₂ c₂) (le_join_left _ _))
      (le_trans (le_join_right c₂ b₂) (le_join_right _ _)))

/-- DOMINATION (row-1), the row-symmetric partner of `topA_S_col2`: if `c₂`
    joins to `⊤` with both `a₂` and `b₂`, the conclusion meets collapse onto
    their row-1 factors, dominating `a₁⊔b₁ ⊒ LHS`. -/
theorem topA_S_row1 {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (hac2 : a₂.join c₂ = top) (hcb2 : c₂.join b₂ = top) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  show ((a₁.join b₁).meet (a₂.join b₂)).le
    (((a₁.join c₁).meet (a₂.join c₂)).join ((c₁.join b₁).meet (c₂.join b₂)))
  rw [hac2, hcb2, meet_top_right, meet_top_right]
  exact le_trans (meet_le_left _ _)
    (join_le (le_trans (le_join_left a₁ c₁) (le_join_left _ _))
      (le_trans (le_join_right c₁ b₁) (le_join_right _ _)))

/-! ## Geometric micro-helpers for the residual (double-incidence) cores -/

/-- Any point of a line `L` lies under the join of two DISTINCT points of `L`
    (their join is `ln L`, axiom 3). -/
theorem pt_le_join_line {u v m : P.Point} {L : P.Line} (huv : u ≠ v)
    (hu : P.incid u L) (hv : P.incid v L) (hm : P.incid m L) :
    (pt m).le ((pt u).join (pt v)) := by
  rw [join_pt_pt_line huv hu hv]; exact hm

/-- Two lines `X ≠ Y` sharing a point `z ∉ L` meet `L` in DISTINCT points: a
    common point `u = v` of `X ∩ L` and `Y ∩ L` would be a second common point
    of `X, Y` besides `z` (axiom 3), forcing `z ∈ L`. -/
theorem meetL_ne {X Y L : P.Line} {z u v : P.Point} (hXY : X ≠ Y)
    (hzX : P.incid z X) (hzY : P.incid z Y) (hzL : ¬ P.incid z L)
    (huX : P.incid u X) (huL : P.incid u L) (hvY : P.incid v Y) (hvL : P.incid v L) :
    u ≠ v := by
  intro h
  rcases P.unique huX (h.symm ▸ hvY) hzX hzY with h' | h'
  · exact hzL (h' ▸ huL)
  · exact hXY h'

/-! ## c-column = point over line: the six canonical `(a,b)`-shape leaves

  With the c-column fixed to `(pt cv, ln cB)` (`cv ∉ cB`) there are nine
  `(a-shape, b-shape)` combinations; the a↔b symmetry `HornConc.of_swap_ab`
  folds three of them onto the others, leaving these six canonical leaves. -/

section cP
variable {cv : P.Point} {cB : P.Line}

/-- cP leaf `(aLL, bLL)`.  Split on `p : cv∈aA`, `q : cv∈bA`, `r : aB=cB`,
    `s : cB=bB`; the four corner-`⊤` regions dominate, five double-incidence
    leaves need a point chase. -/
theorem cP_LLLL {aA aB bA bB : P.Line} (hc : ¬ P.incid cv cB)
    (haAB : aA ≠ aB) (hbAB : bA ≠ bB) :
    HornConc (ln aA) (ln aB) (ln bA) (ln bB) (pt cv) (ln cB) := by
  by_cases p : P.incid cv aA
  · by_cases q : P.incid cv bA
    · by_cases r : aB = cB
      · by_cases s : cB = bB
        · -- combo1 TTTT: aB=cB=bB=:L; M_ac=pt u, M_cb=pt v both on L
          subst cB; subst s
          by_cases haAbA : aA = bA
          · subst haAbA
            unfold HornConc
            simp only [join_ln_pt_incid p, join_pt_ln_incid q, join_ln_ln_self]
            exact le_join_left _ _
          · have huv : P.meetPoint aA aB ≠ P.meetPoint bA aB :=
              meetL_ne haAbA p q hc (P.meetPoint_incid_left aA aB)
                (P.meetPoint_incid_right aA aB) (P.meetPoint_incid_left bA aB)
                (P.meetPoint_incid_right bA aB)
            unfold HornConc
            rw [join_ln_pt_incid p, join_pt_ln_incid q, join_ln_ln_ne haAbA,
              join_ln_ln_self, meet_top_left, meet_ln_ln_ne haAB, meet_ln_ln_ne hbAB,
              join_pt_pt_line huv (P.meetPoint_incid_right aA aB)
                (P.meetPoint_incid_right bA aB)]
            exact le_refl _
        · -- combo2 TTTF: c₂=a₂ (aB=cB); M_ac=pt(aA∧aB), M_cb=ln bA
          have hA2 : (ln aB).join (ln cB) = ln aB := by rw [← r]; exact join_ln_ln_self aB
          by_cases haAbA : aA = bA
          · subst haAbA
            unfold HornConc
            rw [join_pt_ln_incid q, join_ln_ln_ne s, meet_top_right, join_ln_pt_incid p,
              hA2, join_ln_ln_self, join_eq_of_le_right (meet_le_left (ln aA) (ln aB))]
            exact meet_le_left _ _
          · have hmnbA : ¬ P.incid (P.meetPoint aA aB) bA := by
              intro hm
              rcases P.unique (P.meetPoint_incid_left aA aB) hm p q with h' | h'
              · exact hc (r ▸ (h' ▸ P.meetPoint_incid_right aA aB))
              · exact haAbA h'
            unfold HornConc
            rw [join_ln_pt_incid p, hA2, meet_ln_ln_ne haAB, join_pt_ln_incid q,
              join_ln_ln_ne s, meet_top_right, join_pt_ln_not hmnbA]
            exact le_top _
      · by_cases s : cB = bB
        · -- combo3 TTFT: c₂=b₂ (cB=bB); M_ac=ln aA, M_cb=pt(bA∧bB)
          have hB2 : (ln cB).join (ln bB) = ln bB := by rw [s]; exact join_ln_ln_self bB
          by_cases haAbA : aA = bA
          · subst haAbA
            have haAbB : aA ≠ bB := fun h => hc (s.symm ▸ h ▸ p)
            unfold HornConc
            rw [join_ln_pt_incid p, join_ln_ln_ne r, meet_top_right, join_pt_ln_incid q,
              hB2, meet_ln_ln_ne haAbB,
              join_ln_pt_incid (P.meetPoint_incid_left aA bB), join_ln_ln_self]
            exact meet_le_left _ _
          · have hnnaA : ¬ P.incid (P.meetPoint bA bB) aA := by
              intro hn
              rcases P.unique (P.meetPoint_incid_left bA bB) hn q p with h' | h'
              · exact hc (s.symm ▸ (h' ▸ P.meetPoint_incid_right bA bB))
              · exact haAbA h'.symm
            unfold HornConc
            rw [join_ln_pt_incid p, join_ln_ln_ne r, meet_top_right, join_pt_ln_incid q,
              hB2, meet_ln_ln_ne hbAB, join_ln_pt_not hnnaA]
            exact le_top _
        · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_ln_ne s)
    · by_cases r : aB = cB
      · by_cases s : cB = bB
        · -- combo5 TFTT
          exact hornConc_of_le_cb (le_meet (by rw [join_pt_ln_not q]; exact le_top _)
            (by rw [← r]; exact meet_le_right _ _))
        · exact topA_S_cb (by rw [join_pt_ln_not q]; exact le_top _)
            (by rw [join_ln_ln_ne s]; exact le_top _)
      · by_cases s : cB = bB
        · -- combo7 TFFT: c₂=b₂ line bB; M_ac=ln aA, M_cb=ln bB
          have haBbB : aB ≠ bB := fun h => r (h.trans s.symm)
          have haAbB : aA ≠ bB := fun h => hc (s.symm ▸ h ▸ p)
          have hB2 : (ln cB).join (ln bB) = ln bB := by rw [s]; exact join_ln_ln_self bB
          unfold HornConc
          rw [join_ln_pt_incid p, join_ln_ln_ne r, join_pt_ln_not q, hB2, meet_top_left,
            join_ln_ln_ne haBbB, meet_top_right, meet_top_right]
          by_cases haAbA : aA = bA
          · rw [haAbA, join_ln_ln_self]; exact le_join_left _ _
          · rw [join_ln_ln_ne haAbA, join_ln_ln_ne haAbB]; exact le_top _
        · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_ln_ne s)
  · by_cases q : P.incid cv bA
    · by_cases r : aB = cB
      · by_cases s : cB = bB
        · -- combo9 FTTT
          exact hornConc_of_le_ac (le_meet (by rw [join_ln_pt_not p]; exact le_top _)
            (by rw [s]; exact meet_le_right _ _))
        · -- combo10 FTTF: M_ac=ln aB, M_cb=ln bA, join ⊤ since aB≠bA
          have hbAaB : bA ≠ aB := fun h => hc (r ▸ h ▸ q)
          have hA2 : (ln aB).join (ln cB) = ln aB := by rw [← r]; exact join_ln_ln_self aB
          unfold HornConc
          rw [join_ln_pt_not p, hA2, meet_top_left, join_pt_ln_incid q,
            join_ln_ln_ne s, meet_top_right, join_ln_ln_ne (fun h => hbAaB h.symm)]
          exact le_top _
      · exact topA_S_ac (by rw [join_ln_pt_not p]; exact le_top _)
          (by rw [join_ln_ln_ne r]; exact le_top _)
    · exact topA_S_col2 (join_ln_pt_not p) (join_pt_ln_not q)

/-- cP leaf `(aPL, bPL)`.  Row-1 all points, row-2 all lines.  Collinearity of
    `av, bv, cv` (i.e. `pt bv ⩽ av⊔cv` or `pt av ⩽ cv⊔bv`) dominates through
    `topA_S_ac`/`topA_S_cb`; the non-collinear residues with a repeated row-2
    line close by projecting the three points onto that line. -/
theorem cP_PLPL {av bv : P.Point} {aB bB : P.Line} (hc : ¬ P.incid cv cB)
    (hav : ¬ P.incid av aB) (hbv : ¬ P.incid bv bB) :
    HornConc (pt av) (ln aB) (pt bv) (ln bB) (pt cv) (ln cB) := by
  by_cases r : aB = cB
  · by_cases s : cB = bB
    · -- aB = cB = bB
      have hbBaB : bB = aB := s.symm.trans r.symm
      by_cases hbvac : (pt bv).le ((pt av).join (pt cv))
      · exact topA_S_ac hbvac
          (le_trans (show (ln bB).le (ln aB) from hbBaB) (le_join_left _ _))
      · by_cases havcb : (pt av).le ((pt cv).join (pt bv))
        · exact topA_S_cb havcb
            (le_trans (show (ln aB).le (ln cB) from r) (le_join_left _ _))
        · -- non-collinear, all lines = aB: project onto aB
          subst cB; subst bB
          have havcv : av ≠ cv := fun h => havcb (by rw [← h]; exact le_join_left _ _)
          have hcvbv : cv ≠ bv := fun h => hbvac (by rw [h]; exact le_join_right _ _)
          have havbv : av ≠ bv := fun h => hbvac (by rw [← h]; exact le_join_left _ _)
          have havL : ¬ P.incid av (P.lineThrough cv bv) :=
            fun hh => havcb (by rw [join_pt_pt_ne hcvbv]; exact hh)
          have hLL : P.lineThrough av cv ≠ P.lineThrough cv bv :=
            fun h => havL (h ▸ P.lineThrough_incid_left av cv)
          have hLacaB : P.lineThrough av cv ≠ aB :=
            fun h => hav (h ▸ P.lineThrough_incid_left av cv)
          have hLcbaB : P.lineThrough cv bv ≠ aB :=
            fun h => hc (h ▸ P.lineThrough_incid_left cv bv)
          have hLabaB : P.lineThrough av bv ≠ aB :=
            fun h => hav (h ▸ P.lineThrough_incid_left av bv)
          have hmn : P.meetPoint (P.lineThrough av cv) aB ≠
              P.meetPoint (P.lineThrough cv bv) aB :=
            meetL_ne hLL (P.lineThrough_incid_right av cv) (P.lineThrough_incid_left cv bv)
              hc (P.meetPoint_incid_left (P.lineThrough av cv) aB)
              (P.meetPoint_incid_right (P.lineThrough av cv) aB)
              (P.meetPoint_incid_left (P.lineThrough cv bv) aB)
              (P.meetPoint_incid_right (P.lineThrough cv bv) aB)
          have hMac : ((pt av).join (pt cv)).meet ((ln aB).join (ln aB)) =
              pt (P.meetPoint (P.lineThrough av cv) aB) := by
            rw [join_pt_pt_ne havcv, join_ln_ln_self, meet_ln_ln_ne hLacaB]
          have hMcb : ((pt cv).join (pt bv)).meet ((ln aB).join (ln aB)) =
              pt (P.meetPoint (P.lineThrough cv bv) aB) := by
            rw [join_pt_pt_ne hcvbv, join_ln_ln_self, meet_ln_ln_ne hLcbaB]
          unfold HornConc
          rw [hMac, hMcb, join_pt_pt_ne havbv, join_ln_ln_self, meet_ln_ln_ne hLabaB,
            join_pt_pt_line hmn (P.meetPoint_incid_right (P.lineThrough av cv) aB)
              (P.meetPoint_incid_right (P.lineThrough cv bv) aB)]
          exact P.meetPoint_incid_right (P.lineThrough av bv) aB
    · -- aB = cB ≠ bB
      by_cases havcb : (pt av).le ((pt cv).join (pt bv))
      · exact topA_S_cb havcb (by rw [join_ln_ln_ne s]; exact le_top _)
      · -- non-collinear, aB = cB, aB ≠ bB
        subst cB
        have havcv : av ≠ cv := fun h => havcb (by rw [← h]; exact le_join_left _ _)
        have hLacaB : P.lineThrough av cv ≠ aB :=
          fun h => hav (h ▸ P.lineThrough_incid_left av cv)
        by_cases hcvbv : cv = bv
        · subst hcvbv
          have hmcv : P.meetPoint (P.lineThrough av cv) aB ≠ cv :=
            fun h => hc (h ▸ P.meetPoint_incid_right (P.lineThrough av cv) aB)
          have hMac : ((pt av).join (pt cv)).meet ((ln aB).join (ln aB)) =
              pt (P.meetPoint (P.lineThrough av cv) aB) := by
            rw [join_pt_pt_ne havcv, join_ln_ln_self, meet_ln_ln_ne hLacaB]
          have hMcb : ((pt cv).join (pt cv)).meet ((ln aB).join (ln bB)) = pt cv := by
            rw [join_pt_pt_self, join_ln_ln_ne s, meet_top_right]
          unfold HornConc
          rw [hMac, hMcb, join_pt_pt_ne havcv, join_ln_ln_ne s, meet_top_right,
            join_pt_pt_line hmcv (P.meetPoint_incid_left (P.lineThrough av cv) aB)
              (P.lineThrough_incid_right av cv)]
          exact le_refl _
        · have havbv : av ≠ bv := fun h => havcb (by rw [← h]; exact le_join_right _ _)
          have havL : ¬ P.incid av (P.lineThrough cv bv) :=
            fun hh => havcb (by rw [join_pt_pt_ne hcvbv]; exact hh)
          have hLL : P.lineThrough av cv ≠ P.lineThrough cv bv :=
            fun h => havL (h ▸ P.lineThrough_incid_left av cv)
          have hmL : ¬ P.incid (P.meetPoint (P.lineThrough av cv) aB)
              (P.lineThrough cv bv) := by
            intro hm
            rcases P.unique (P.meetPoint_incid_left (P.lineThrough av cv) aB) hm
                (P.lineThrough_incid_right av cv) (P.lineThrough_incid_left cv bv) with h' | h'
            · exact hc (h' ▸ P.meetPoint_incid_right (P.lineThrough av cv) aB)
            · exact hLL h'
          have hMac : ((pt av).join (pt cv)).meet ((ln aB).join (ln aB)) =
              pt (P.meetPoint (P.lineThrough av cv) aB) := by
            rw [join_pt_pt_ne havcv, join_ln_ln_self, meet_ln_ln_ne hLacaB]
          have hMcb : ((pt cv).join (pt bv)).meet ((ln aB).join (ln bB)) =
              ln (P.lineThrough cv bv) := by
            rw [join_pt_pt_ne hcvbv, join_ln_ln_ne s, meet_top_right]
          unfold HornConc
          rw [hMac, hMcb, join_pt_ln_not hmL]
          exact le_top _
  · by_cases s : cB = bB
    · -- aB ≠ cB = bB
      by_cases hbvac : (pt bv).le ((pt av).join (pt cv))
      · exact topA_S_ac hbvac (by rw [join_ln_ln_ne r]; exact le_top _)
      · -- non-collinear, aB ≠ cB, cB = bB
        subst cB
        have hcvbv : cv ≠ bv := fun h => hbvac (by rw [h]; exact le_join_right _ _)
        have hLcbbB : P.lineThrough cv bv ≠ bB :=
          fun h => hc (h ▸ P.lineThrough_incid_left cv bv)
        by_cases haveq : av = cv
        · have hncv : P.meetPoint (P.lineThrough cv bv) bB ≠ cv :=
            fun h => hc (h ▸ P.meetPoint_incid_right (P.lineThrough cv bv) bB)
          have hMac : ((pt av).join (pt cv)).meet ((ln aB).join (ln bB)) = pt cv := by
            rw [haveq, join_pt_pt_self, join_ln_ln_ne r, meet_top_right]
          have hMcb : ((pt cv).join (pt bv)).meet ((ln bB).join (ln bB)) =
              pt (P.meetPoint (P.lineThrough cv bv) bB) := by
            rw [join_pt_pt_ne hcvbv, join_ln_ln_self, meet_ln_ln_ne hLcbbB]
          unfold HornConc
          rw [hMac, hMcb, haveq, join_pt_pt_ne hcvbv, join_ln_ln_ne r, meet_top_right,
            join_pt_pt_line (Ne.symm hncv) (P.lineThrough_incid_left cv bv)
              (P.meetPoint_incid_left (P.lineThrough cv bv) bB)]
          exact le_refl _
        · have havbv : av ≠ bv := fun h => hbvac (by rw [← h]; exact le_join_left _ _)
          have hbvL : ¬ P.incid bv (P.lineThrough av cv) :=
            fun hh => hbvac (by rw [join_pt_pt_ne haveq]; exact hh)
          have hLL : P.lineThrough av cv ≠ P.lineThrough cv bv :=
            fun h => hbvL (h.symm ▸ P.lineThrough_incid_right cv bv)
          have hLacaB : P.lineThrough av cv ≠ aB :=
            fun h => hav (h ▸ P.lineThrough_incid_left av cv)
          have hnL : ¬ P.incid (P.meetPoint (P.lineThrough cv bv) bB)
              (P.lineThrough av cv) := by
            intro hm
            rcases P.unique (P.meetPoint_incid_left (P.lineThrough cv bv) bB) hm
                (P.lineThrough_incid_left cv bv) (P.lineThrough_incid_right av cv) with h' | h'
            · exact hc (h' ▸ P.meetPoint_incid_right (P.lineThrough cv bv) bB)
            · exact hLL h'.symm
          have hMac : ((pt av).join (pt cv)).meet ((ln aB).join (ln bB)) =
              ln (P.lineThrough av cv) := by
            rw [join_pt_pt_ne haveq, join_ln_ln_ne r, meet_top_right]
          have hMcb : ((pt cv).join (pt bv)).meet ((ln bB).join (ln bB)) =
              pt (P.meetPoint (P.lineThrough cv bv) bB) := by
            rw [join_pt_pt_ne hcvbv, join_ln_ln_self, meet_ln_ln_ne hLcbbB]
          unfold HornConc
          rw [hMac, hMcb, join_ln_pt_not hnL]
          exact le_top _
    · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_ln_ne s)

/-- cP leaf `(aLP, bLP)`. -/
theorem cP_LPLP {aw bw : P.Point} {aA bA : P.Line} (hc : ¬ P.incid cv cB)
    (haw : ¬ P.incid aw aA) (hbw : ¬ P.incid bw bA) :
    HornConc (ln aA) (pt aw) (ln bA) (pt bw) (pt cv) (ln cB) := by
  by_cases hab : aA = bA
  · subst hab
    have hL : (((ln aA).join (ln aA)).meet ((pt aw).join (pt bw))).le (ln aA) :=
      le_trans (meet_le_left _ _) (join_le (le_refl _) (le_refl _))
    by_cases u : P.incid bw cB
    · exact hornConc_of_le_ac (le_meet (le_trans hL (le_join_left _ _))
        (le_trans (meet_le_right _ _) (join_mono (le_refl _) u)))
    · by_cases t : P.incid aw cB
      · exact hornConc_of_le_cb (le_meet (le_trans hL (le_join_right _ _))
          (le_trans (meet_le_right _ _) (join_mono t (le_refl _))))
      · exact hornConc_of_le_ac (le_meet (le_trans hL (le_join_left _ _))
          (by rw [join_pt_ln_not t]; exact le_top _))
  · by_cases hcvA : P.incid cv aA
    · by_cases hcvB : P.incid cv bA
      · -- core: cv ∈ aA ∩ bA, aA ≠ bA
        have haAcB : aA ≠ cB := fun h => hc (h ▸ hcvA)
        have hbAcB : bA ≠ cB := fun h => hc (h ▸ hcvB)
        by_cases t : P.incid aw cB
        · by_cases u : P.incid bw cB
          · -- t,u: M_ac,M_cb are distinct points of cB, span it
            have hmn : P.meetPoint aA cB ≠ P.meetPoint bA cB := by
              intro h
              rcases P.unique (P.meetPoint_incid_left aA cB)
                  (h ▸ P.meetPoint_incid_left bA cB) hcvA hcvB with h' | h'
              · exact hc (h' ▸ P.meetPoint_incid_right aA cB)
              · exact hab h'
            have hMac : ((ln aA).join (pt cv)).meet ((pt aw).join (ln cB)) =
                pt (P.meetPoint aA cB) := by
              rw [join_ln_pt_incid hcvA, join_pt_ln_incid t, meet_ln_ln_ne haAcB]
            have hMcb : ((pt cv).join (ln bA)).meet ((ln cB).join (pt bw)) =
                pt (P.meetPoint bA cB) := by
              rw [join_pt_ln_incid hcvB, join_ln_pt_incid u, meet_ln_ln_ne hbAcB]
            unfold HornConc
            rw [hMac, hMcb, join_pt_pt_line hmn (P.meetPoint_incid_right aA cB)
              (P.meetPoint_incid_right bA cB)]
            exact le_trans (meet_le_right _ _) (join_le t u)
          · -- t,¬u: M_ac=pt(aA∩cB) off bA, M_cb=ln bA, join ⊤
            have hmbA : ¬ P.incid (P.meetPoint aA cB) bA := by
              intro hm
              rcases P.unique (P.meetPoint_incid_left aA cB) hm hcvA hcvB with h' | h'
              · exact hc (h' ▸ P.meetPoint_incid_right aA cB)
              · exact hab h'
            have hMac : ((ln aA).join (pt cv)).meet ((pt aw).join (ln cB)) =
                pt (P.meetPoint aA cB) := by
              rw [join_ln_pt_incid hcvA, join_pt_ln_incid t, meet_ln_ln_ne haAcB]
            have hMcb : ((pt cv).join (ln bA)).meet ((ln cB).join (pt bw)) = ln bA := by
              rw [join_pt_ln_incid hcvB, join_ln_pt_not u, meet_top_right]
            unfold HornConc
            rw [hMac, hMcb, join_pt_ln_not hmbA]
            exact le_top _
        · by_cases u : P.incid bw cB
          · -- ¬t,u: M_ac=ln aA, M_cb=pt(bA∩cB) off aA, join ⊤
            have hnaA : ¬ P.incid (P.meetPoint bA cB) aA := by
              intro hn
              rcases P.unique (P.meetPoint_incid_left bA cB) hn hcvB hcvA with h' | h'
              · exact hc (h' ▸ P.meetPoint_incid_right bA cB)
              · exact hab h'.symm
            have hMac : ((ln aA).join (pt cv)).meet ((pt aw).join (ln cB)) = ln aA := by
              rw [join_ln_pt_incid hcvA, join_pt_ln_not t, meet_top_right]
            have hMcb : ((pt cv).join (ln bA)).meet ((ln cB).join (pt bw)) =
                pt (P.meetPoint bA cB) := by
              rw [join_pt_ln_incid hcvB, join_ln_pt_incid u, meet_ln_ln_ne hbAcB]
            unfold HornConc
            rw [hMac, hMcb, join_ln_pt_not hnaA]
            exact le_top _
          · -- ¬t,¬u: M_ac=ln aA, M_cb=ln bA, join ⊤
            have hMac : ((ln aA).join (pt cv)).meet ((pt aw).join (ln cB)) = ln aA := by
              rw [join_ln_pt_incid hcvA, join_pt_ln_not t, meet_top_right]
            have hMcb : ((pt cv).join (ln bA)).meet ((ln cB).join (pt bw)) = ln bA := by
              rw [join_pt_ln_incid hcvB, join_ln_pt_not u, meet_top_right]
            unfold HornConc
            rw [hMac, hMcb, join_ln_ln_ne hab]
            exact le_top _
      · -- cv ∈ aA, cv ∉ bA : c₁⊔b₁ = ⊤ (le_cb cond1)
        by_cases t : P.incid aw cB
        · exact hornConc_of_le_cb (le_meet (by rw [join_pt_ln_not hcvB]; exact le_top _)
            (le_trans (meet_le_right _ _) (join_mono t (le_refl _))))
        · by_cases u : P.incid bw cB
          · -- F3: aw∉cB, bw∈cB, cv∈aA, cv∉bA
            have haAcB : aA ≠ cB := fun h => hc (h ▸ hcvA)
            have hMac : ((ln aA).join (pt cv)).meet ((pt aw).join (ln cB)) = ln aA := by
              rw [join_ln_pt_incid hcvA, join_pt_ln_not t, meet_top_right]
            have hMcb : ((pt cv).join (ln bA)).meet ((ln cB).join (pt bw)) = ln cB := by
              rw [join_pt_ln_not hcvB, join_ln_pt_incid u, meet_top_left]
            unfold HornConc
            rw [hMac, hMcb, join_ln_ln_ne haAcB]
            exact le_top _
          · exact hornConc_of_le_cb (le_meet (by rw [join_pt_ln_not hcvB]; exact le_top _)
              (by rw [join_ln_pt_not u]; exact le_top _))
    · -- cv ∉ aA : a₁⊔c₁ = ⊤ (le_ac cond1)
      by_cases u : P.incid bw cB
      · exact hornConc_of_le_ac (le_meet (by rw [join_ln_pt_not hcvA]; exact le_top _)
          (le_trans (meet_le_right _ _) (join_mono (le_refl _) u)))
      · by_cases hcvB : P.incid cv bA
        · by_cases t : P.incid aw cB
          · -- F2: cv∉aA, cv∈bA, aw∈cB, bw∉cB
            have hbAcB : bA ≠ cB := fun h => hc (h ▸ hcvB)
            have hMac : ((ln aA).join (pt cv)).meet ((pt aw).join (ln cB)) = ln cB := by
              rw [join_ln_pt_not hcvA, join_pt_ln_incid t, meet_top_left]
            have hMcb : ((pt cv).join (ln bA)).meet ((ln cB).join (pt bw)) = ln bA := by
              rw [join_pt_ln_incid hcvB, join_ln_pt_not u, meet_top_right]
            unfold HornConc
            rw [hMac, hMcb, join_ln_ln_ne (fun h => hbAcB h.symm)]
            exact le_top _
          · exact hornConc_of_le_ac (le_meet (by rw [join_ln_pt_not hcvA]; exact le_top _)
              (by rw [join_pt_ln_not t]; exact le_top _))
        · exact hornConc_of_le_cb (le_meet (by rw [join_pt_ln_not hcvB]; exact le_top _)
            (by rw [join_ln_pt_not u]; exact le_top _))

/-- cP leaf `(aLL, bPL)`.  `M_cb` carries the point-point join `pt cv ⊔ pt bv`;
    the residual leaves are closed either by regrouping the three collinear
    points `aA∩aB, cv, bv` onto `aA`, or by a `⊤`-join off `lineThrough cv bv`. -/
theorem cP_LLPL {aA aB bB : P.Line} {bv : P.Point} (hc : ¬ P.incid cv cB)
    (haAB : aA ≠ aB) (hbv : ¬ P.incid bv bB) :
    HornConc (ln aA) (ln aB) (pt bv) (ln bB) (pt cv) (ln cB) := by
  by_cases hcvA : P.incid cv aA
  · by_cases hbvA : P.incid bv aA
    · by_cases r : aB = cB
      · by_cases hbB : bB = aB
        · exact topA_S_ac (le_trans (show (pt bv).le (ln aA) from hbvA) (le_join_left _ _))
            (le_trans (show (ln bB).le (ln aB) from hbB) (le_join_left _ _))
        · -- G1
          have hmaA : P.incid (P.meetPoint aA aB) aA := P.meetPoint_incid_left aA aB
          have hmcv : P.meetPoint aA aB ≠ cv :=
            fun h => hc (r ▸ h ▸ P.meetPoint_incid_right aA aB)
          have hA2 : (ln aB).join (ln cB) = ln aB := by rw [← r]; exact join_ln_ln_self aB
          have hB2 : (ln cB).join (ln bB) = top := by
            rw [← r]; exact join_ln_ln_ne (fun h => hbB h.symm)
          unfold HornConc
          rw [join_ln_pt_incid hbvA, join_ln_ln_ne (fun h => hbB h.symm), meet_top_right,
            join_ln_pt_incid hcvA, hA2, meet_ln_ln_ne haAB, hB2, meet_top_right,
            join_assoc, join_pt_pt_line hmcv hmaA hcvA]
          exact le_join_left _ _
      · exact topA_S_ac (le_trans (show (pt bv).le (ln aA) from hbvA) (le_join_left _ _))
          (by rw [join_ln_ln_ne r]; exact le_top _)
    · -- G2: cv∈aA, bv∉aA
      have hcvbv : cv ≠ bv := fun h => hbvA (h ▸ hcvA)
      have haAL : aA ≠ P.lineThrough cv bv :=
        fun h => hbvA (h.symm ▸ P.lineThrough_incid_right cv bv)
      by_cases r : aB = cB
      · by_cases s : cB = bB
        · -- G2-rs: aB = cB = bB
          subst cB; subst bB
          have hmn : P.meetPoint aA aB ≠ P.meetPoint (P.lineThrough cv bv) aB := by
            intro h
            rcases P.unique (P.meetPoint_incid_left aA aB)
                (h ▸ P.meetPoint_incid_left (P.lineThrough cv bv) aB) hcvA
                (P.lineThrough_incid_left cv bv) with h' | h'
            · exact hc (h' ▸ P.meetPoint_incid_right aA aB)
            · exact haAL h'
          have hLaB : P.lineThrough cv bv ≠ aB :=
            fun h => hc (h ▸ P.lineThrough_incid_left cv bv)
          have hMac : ((ln aA).join (pt cv)).meet ((ln aB).join (ln aB)) =
              pt (P.meetPoint aA aB) := by
            rw [join_ln_pt_incid hcvA, join_ln_ln_self, meet_ln_ln_ne haAB]
          have hMcb : ((pt cv).join (pt bv)).meet ((ln aB).join (ln aB)) =
              pt (P.meetPoint (P.lineThrough cv bv) aB) := by
            rw [join_pt_pt_ne hcvbv, join_ln_ln_self, meet_ln_ln_ne hLaB]
          unfold HornConc
          rw [hMac, hMcb, join_ln_pt_not hbvA, join_ln_ln_self, meet_top_left,
            join_pt_pt_line hmn (P.meetPoint_incid_right aA aB)
              (P.meetPoint_incid_right (P.lineThrough cv bv) aB)]
          exact le_refl _
        · -- G2-r¬s
          have hmL : ¬ P.incid (P.meetPoint aA aB) (P.lineThrough cv bv) := by
            intro hm
            rcases P.unique (P.meetPoint_incid_left aA aB) hm hcvA
                (P.lineThrough_incid_left cv bv) with h' | h'
            · exact hc (r ▸ h' ▸ P.meetPoint_incid_right aA aB)
            · exact haAL h'
          have hMac : ((ln aA).join (pt cv)).meet ((ln aB).join (ln cB)) =
              pt (P.meetPoint aA aB) := by
            rw [join_ln_pt_incid hcvA, ← r, join_ln_ln_self, meet_ln_ln_ne haAB]
          have hMcb : ((pt cv).join (pt bv)).meet ((ln cB).join (ln bB)) =
              ln (P.lineThrough cv bv) := by
            rw [join_pt_pt_ne hcvbv, join_ln_ln_ne s, meet_top_right]
          unfold HornConc
          rw [hMac, hMcb, join_pt_ln_not hmL]
          exact le_top _
      · by_cases s : cB = bB
        · -- G2-¬rs
          have hLbB : P.lineThrough cv bv ≠ bB :=
            fun h => hc (s.symm ▸ (h ▸ P.lineThrough_incid_left cv bv))
          have hnaA : ¬ P.incid (P.meetPoint (P.lineThrough cv bv) bB) aA := by
            intro hn
            rcases P.unique (P.meetPoint_incid_left (P.lineThrough cv bv) bB) hn
                (P.lineThrough_incid_left cv bv) hcvA with h' | h'
            · exact hc (s.symm ▸ h' ▸ P.meetPoint_incid_right (P.lineThrough cv bv) bB)
            · exact haAL h'.symm
          have hMac : ((ln aA).join (pt cv)).meet ((ln aB).join (ln cB)) = ln aA := by
            rw [join_ln_pt_incid hcvA, join_ln_ln_ne r, meet_top_right]
          have hMcb : ((pt cv).join (pt bv)).meet ((ln cB).join (ln bB)) =
              pt (P.meetPoint (P.lineThrough cv bv) bB) := by
            rw [join_pt_pt_ne hcvbv, s, join_ln_ln_self, meet_ln_ln_ne hLbB]
          unfold HornConc
          rw [hMac, hMcb, join_ln_pt_not hnaA]
          exact le_top _
        · -- G2-¬r¬s
          have hMac : ((ln aA).join (pt cv)).meet ((ln aB).join (ln cB)) = ln aA := by
            rw [join_ln_pt_incid hcvA, join_ln_ln_ne r, meet_top_right]
          have hMcb : ((pt cv).join (pt bv)).meet ((ln cB).join (ln bB)) =
              ln (P.lineThrough cv bv) := by
            rw [join_pt_pt_ne hcvbv, join_ln_ln_ne s, meet_top_right]
          unfold HornConc
          rw [hMac, hMcb, join_ln_ln_ne haAL]
          exact le_top _
  · by_cases r : aB = cB
    · by_cases hbB : bB = aB
      · exact topA_S_ac (by rw [join_ln_pt_not hcvA]; exact le_top _)
          (le_trans (show (ln bB).le (ln aB) from hbB) (le_join_left _ _))
      · -- G3
        have hcvaB : ¬ P.incid cv aB := fun h => hc (r ▸ h)
        have hcBbB : cB ≠ bB := fun h => hbB (h.symm.trans r.symm)
        have hA2 : (ln aB).join (ln cB) = ln aB := by rw [← r]; exact join_ln_ln_self aB
        unfold HornConc
        rw [join_ln_pt_not hcvA, hA2, meet_top_left, join_ln_ln_ne hcBbB, meet_top_right,
          join_assoc, join_ln_pt_not hcvaB, join_top_left]
        exact le_top _
    · exact topA_S_ac (by rw [join_ln_pt_not hcvA]; exact le_top _)
        (by rw [join_ln_ln_ne r]; exact le_top _)

/-- cP leaf `(aLL, bLP)`.  Same case tree as `cP_LLLL` with `s : bw∈cB` in the
    role of `cB=bB`. -/
theorem cP_LLLP {aA aB bA : P.Line} {bw : P.Point} (hc : ¬ P.incid cv cB)
    (haAB : aA ≠ aB) (hbw : ¬ P.incid bw bA) :
    HornConc (ln aA) (ln aB) (ln bA) (pt bw) (pt cv) (ln cB) := by
  by_cases p : P.incid cv aA
  · by_cases q : P.incid cv bA
    · by_cases r : aB = cB
      · by_cases s : P.incid bw cB
        · -- combo1 TTTT
          subst cB
          have hbAaB : bA ≠ aB := fun h => hc (h ▸ q)
          by_cases haAbA : aA = bA
          · subst haAbA
            unfold HornConc
            simp only [join_ln_pt_incid p, join_pt_ln_incid q, join_ln_ln_self,
              join_ln_pt_incid s]
            exact le_join_left _ _
          · have huv : P.meetPoint aA aB ≠ P.meetPoint bA aB :=
              meetL_ne haAbA p q hc (P.meetPoint_incid_left aA aB)
                (P.meetPoint_incid_right aA aB) (P.meetPoint_incid_left bA aB)
                (P.meetPoint_incid_right bA aB)
            unfold HornConc
            rw [join_ln_pt_incid p, join_pt_ln_incid q, join_ln_ln_ne haAbA,
              join_ln_ln_self, join_ln_pt_incid s, meet_top_left, meet_ln_ln_ne haAB,
              meet_ln_ln_ne hbAaB, join_pt_pt_line huv (P.meetPoint_incid_right aA aB)
                (P.meetPoint_incid_right bA aB)]
            exact le_refl _
        · -- combo2 TTTF
          have hA2 : (ln aB).join (ln cB) = ln aB := by rw [← r]; exact join_ln_ln_self aB
          by_cases haAbA : aA = bA
          · subst haAbA
            unfold HornConc
            rw [join_pt_ln_incid q, join_ln_pt_not s, meet_top_right, join_ln_pt_incid p,
              hA2, join_ln_ln_self, join_eq_of_le_right (meet_le_left (ln aA) (ln aB))]
            exact meet_le_left _ _
          · have hmnbA : ¬ P.incid (P.meetPoint aA aB) bA := by
              intro hm
              rcases P.unique (P.meetPoint_incid_left aA aB) hm p q with h' | h'
              · exact hc (r ▸ (h' ▸ P.meetPoint_incid_right aA aB))
              · exact haAbA h'
            unfold HornConc
            rw [join_ln_pt_incid p, hA2, meet_ln_ln_ne haAB, join_pt_ln_incid q,
              join_ln_pt_not s, meet_top_right, join_pt_ln_not hmnbA]
            exact le_top _
      · by_cases s : P.incid bw cB
        · -- combo3 TTFT
          have hbAcB : bA ≠ cB := fun h => hc (h ▸ q)
          by_cases haAbA : aA = bA
          · subst haAbA
            unfold HornConc
            rw [join_ln_pt_incid p, join_ln_ln_ne r, meet_top_right, join_pt_ln_incid q,
              join_ln_pt_incid s, meet_ln_ln_ne hbAcB,
              join_ln_pt_incid (P.meetPoint_incid_left aA cB), join_ln_ln_self]
            exact meet_le_left _ _
          · have hnnaA : ¬ P.incid (P.meetPoint bA cB) aA := by
              intro hn
              rcases P.unique (P.meetPoint_incid_left bA cB) hn q p with h' | h'
              · exact hc (h' ▸ P.meetPoint_incid_right bA cB)
              · exact haAbA h'.symm
            unfold HornConc
            rw [join_ln_pt_incid p, join_ln_ln_ne r, meet_top_right, join_pt_ln_incid q,
              join_ln_pt_incid s, meet_ln_ln_ne hbAcB, join_ln_pt_not hnnaA]
            exact le_top _
        · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_pt_not s)
    · by_cases r : aB = cB
      · by_cases s : P.incid bw cB
        · -- combo5 TFTT
          exact hornConc_of_le_cb (le_meet (by rw [join_pt_ln_not q]; exact le_top _)
            (by rw [← r]; exact meet_le_right _ _))
        · exact topA_S_cb (by rw [join_pt_ln_not q]; exact le_top _)
            (by rw [join_ln_pt_not s]; exact le_top _)
      · by_cases s : P.incid bw cB
        · -- combo7 TFFT: M_ac=ln aA, M_cb=ln cB, join ⊤ since aA≠cB
          have haAcB : aA ≠ cB := fun h => hc (h ▸ p)
          unfold HornConc
          rw [join_ln_pt_incid p, join_ln_ln_ne r, meet_top_right, join_pt_ln_not q,
            join_ln_pt_incid s, meet_top_left, join_ln_ln_ne haAcB]
          exact le_top _
        · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_pt_not s)
  · by_cases q : P.incid cv bA
    · by_cases r : aB = cB
      · by_cases s : P.incid bw cB
        · -- combo9 FTTT
          have hbwaB : P.incid bw aB := by rw [r]; exact s
          exact hornConc_of_le_ac (le_meet (by rw [join_ln_pt_not p]; exact le_top _)
            (by rw [← r, join_ln_ln_self, join_ln_pt_incid hbwaB]; exact meet_le_right _ _))
        · -- combo10 FTTF
          have hbAaB : bA ≠ aB := fun h => hc (r ▸ h ▸ q)
          have hA2 : (ln aB).join (ln cB) = ln aB := by rw [← r]; exact join_ln_ln_self aB
          unfold HornConc
          rw [join_ln_pt_not p, hA2, meet_top_left, join_pt_ln_incid q,
            join_ln_pt_not s, meet_top_right, join_ln_ln_ne (fun h => hbAaB h.symm)]
          exact le_top _
      · exact topA_S_ac (by rw [join_ln_pt_not p]; exact le_top _)
          (by rw [join_ln_ln_ne r]; exact le_top _)
    · exact topA_S_col2 (join_ln_pt_not p) (join_pt_ln_not q)

/-- cP leaf `(aPL, bLP)`.  `M_ac` carries `pt av ⊔ pt cv`; `topA_S_cb`
    dominates through the line-based `M_cb` except where `cv` and `av` split on
    `bA` / `bw` on `cB`. -/
theorem cP_PLLP {av bw : P.Point} {aB bA : P.Line} (hc : ¬ P.incid cv cB)
    (hav : ¬ P.incid av aB) (hbw : ¬ P.incid bw bA) :
    HornConc (pt av) (ln aB) (ln bA) (pt bw) (pt cv) (ln cB) := by
  by_cases q : P.incid cv bA
  · by_cases havbA : P.incid av bA
    · by_cases r : aB = cB
      · exact topA_S_cb (le_trans (show (pt av).le (ln bA) from havbA) (le_join_right _ _))
          (le_trans (show (ln aB).le (ln cB) from r) (le_join_left _ _))
      · by_cases u : P.incid bw cB
        · -- GA: av,cv,(bA∩cB) collinear on bA
          have hncv : P.meetPoint bA cB ≠ cv :=
            fun h => hc (h ▸ P.meetPoint_incid_right bA cB)
          have hbAcB : bA ≠ cB := fun h => hc (h ▸ q)
          have hMac : ((pt av).join (pt cv)).meet ((ln aB).join (ln cB)) =
              (pt av).join (pt cv) := by rw [join_ln_ln_ne r, meet_top_right]
          have hMcb : ((pt cv).join (ln bA)).meet ((ln cB).join (pt bw)) =
              pt (P.meetPoint bA cB) := by
            rw [join_pt_ln_incid q, join_ln_pt_incid u, meet_ln_ln_ne hbAcB]
          unfold HornConc
          rw [hMac, hMcb, ← join_assoc,
            join_pt_pt_line (Ne.symm hncv) q (P.meetPoint_incid_left bA cB),
            join_pt_ln_incid havbA]
          exact meet_le_left _ _
        · exact topA_S_cb (le_trans (show (pt av).le (ln bA) from havbA) (le_join_right _ _))
            (by rw [join_ln_pt_not u]; exact le_top _)
    · -- GB: cv∈bA, av∉bA, so av≠cv and bA ≠ lineThrough av cv
      have havcv : av ≠ cv := fun h => havbA (h.symm ▸ q)
      have hbAL : bA ≠ P.lineThrough av cv :=
        fun h => havbA (h.symm ▸ P.lineThrough_incid_left av cv)
      by_cases r : aB = cB
      · by_cases u : P.incid bw cB
        · -- GB-r,u
          subst cB
          have hLaB : P.lineThrough av cv ≠ aB :=
            fun h => hav (h ▸ P.lineThrough_incid_left av cv)
          have hbAaB : bA ≠ aB := fun h => hc (h ▸ q)
          have hmn : P.meetPoint (P.lineThrough av cv) aB ≠ P.meetPoint bA aB := by
            intro h
            rcases P.unique (P.meetPoint_incid_left (P.lineThrough av cv) aB)
                (h ▸ P.meetPoint_incid_left bA aB) (P.lineThrough_incid_right av cv) q
                with h' | h'
            · exact hc (h' ▸ P.meetPoint_incid_right (P.lineThrough av cv) aB)
            · exact hbAL h'.symm
          have hMac : ((pt av).join (pt cv)).meet ((ln aB).join (ln aB)) =
              pt (P.meetPoint (P.lineThrough av cv) aB) := by
            rw [join_pt_pt_ne havcv, join_ln_ln_self, meet_ln_ln_ne hLaB]
          have hMcb : ((pt cv).join (ln bA)).meet ((ln aB).join (pt bw)) =
              pt (P.meetPoint bA aB) := by
            rw [join_pt_ln_incid q, join_ln_pt_incid u, meet_ln_ln_ne hbAaB]
          unfold HornConc
          rw [hMac, hMcb, join_pt_ln_not havbA, join_ln_pt_incid u, meet_top_left,
            join_pt_pt_line hmn (P.meetPoint_incid_right (P.lineThrough av cv) aB)
              (P.meetPoint_incid_right bA aB)]
          exact le_refl _
        · -- GB-r,¬u
          have hLaB : P.lineThrough av cv ≠ aB :=
            fun h => hav (h ▸ P.lineThrough_incid_left av cv)
          have hmaB : ¬ P.incid (P.meetPoint (P.lineThrough av cv) aB) bA := by
            intro hm
            rcases P.unique hm (P.meetPoint_incid_left (P.lineThrough av cv) aB) q
                (P.lineThrough_incid_right av cv) with h' | h'
            · exact hc (r ▸ h' ▸ P.meetPoint_incid_right (P.lineThrough av cv) aB)
            · exact hbAL h'
          have hMac : ((pt av).join (pt cv)).meet ((ln aB).join (ln cB)) =
              pt (P.meetPoint (P.lineThrough av cv) aB) := by
            rw [join_pt_pt_ne havcv, ← r, join_ln_ln_self, meet_ln_ln_ne hLaB]
          have hMcb : ((pt cv).join (ln bA)).meet ((ln cB).join (pt bw)) = ln bA := by
            rw [join_pt_ln_incid q, join_ln_pt_not u, meet_top_right]
          unfold HornConc
          rw [hMac, hMcb, join_pt_ln_not hmaB]
          exact le_top _
      · by_cases u : P.incid bw cB
        · -- GB-¬r,u
          have hbAcB : bA ≠ cB := fun h => hc (h ▸ q)
          have hnL : ¬ P.incid (P.meetPoint bA cB) (P.lineThrough av cv) := by
            intro hn
            rcases P.unique (P.meetPoint_incid_left bA cB) hn q
                (P.lineThrough_incid_right av cv) with h' | h'
            · exact hc (h' ▸ P.meetPoint_incid_right bA cB)
            · exact hbAL h'
          have hMac : ((pt av).join (pt cv)).meet ((ln aB).join (ln cB)) =
              ln (P.lineThrough av cv) := by
            rw [join_pt_pt_ne havcv, join_ln_ln_ne r, meet_top_right]
          have hMcb : ((pt cv).join (ln bA)).meet ((ln cB).join (pt bw)) =
              pt (P.meetPoint bA cB) := by
            rw [join_pt_ln_incid q, join_ln_pt_incid u, meet_ln_ln_ne hbAcB]
          unfold HornConc
          rw [hMac, hMcb, join_ln_pt_not hnL]
          exact le_top _
        · -- GB-¬r,¬u
          unfold HornConc
          rw [join_pt_pt_ne havcv, join_ln_ln_ne r, meet_top_right,
            join_pt_ln_incid q, join_ln_pt_not u, meet_top_right,
            join_ln_ln_ne (Ne.symm hbAL)]
          exact le_top _
  · by_cases r : aB = cB
    · exact topA_S_cb (by rw [join_pt_ln_not q]; exact le_top _)
        (le_trans (show (ln aB).le (ln cB) from r) (le_join_left _ _))
    · by_cases u : P.incid bw cB
      · -- GC: RHS ⊤ via pt cv ⊔ ln cB
        unfold HornConc
        rw [join_ln_ln_ne r, meet_top_right, join_pt_ln_not q, join_ln_pt_incid u,
          meet_top_left, ← join_assoc, join_pt_ln_not hc, join_top_right]
        exact le_top _
      · exact topA_S_cb (by rw [join_pt_ln_not q]; exact le_top _)
          (by rw [join_ln_pt_not u]; exact le_top _)

/-- Dispatcher: the `famA` conclusion for a c-column `(pt cv, ln cB)` and
    arbitrary big a-, b-columns.  Folds the nine shape leaves onto the six
    canonical ones by the a↔b symmetry. -/
theorem htA_cP (a₁ a₂ b₁ b₂ : PElem P) (hc : ¬ P.incid cv cB)
    (ha1 : a₁ ≠ top) (ha2 : a₂ ≠ top) (hb1 : b₁ ≠ top) (hb2 : b₂ ≠ top)
    (hKA : a₁.join a₂ = top) (hKB : b₁.join b₂ = top) :
    HornConc a₁ a₂ b₁ b₂ (pt cv) (ln cB) := by
  rcases bigPair_cases hKA ha1 ha2 with
      ⟨av, aB, rfl, rfl, hav⟩ | ⟨aA, aw, rfl, rfl, haw⟩ | ⟨aA, aB, rfl, rfl, haAB⟩ <;>
    rcases bigPair_cases hKB hb1 hb2 with
      ⟨bv, bB, rfl, rfl, hbv⟩ | ⟨bA, bw, rfl, rfl, hbw⟩ | ⟨bA, bB, rfl, rfl, hbAB⟩
  · exact cP_PLPL hc hav hbv
  · exact cP_PLLP hc hav hbw
  · exact HornConc.of_swap_ab (cP_LLPL hc hbAB hav)
  · exact HornConc.of_swap_ab (cP_PLLP hc hbv haw)
  · exact cP_LPLP hc haw hbw
  · exact HornConc.of_swap_ab (cP_LLLP hc hbAB haw)
  · exact cP_LLPL hc haAB hbv
  · exact cP_LLLP hc haAB hbw
  · exact cP_LLLL hc haAB hbAB

end cP

/-! ## c-column = two distinct lines: the six canonical `(a,b)`-shape leaves -/

section cL
variable {cA cB : P.Line}

/-- cL leaf `(aLL, bLL)`.  Shortcuts: `c=a` (resp. `c=b`) makes `M_cb` (resp.
    `M_ac`) EQUAL the LHS.  Only two residual combos need a `⊤`-join. -/
theorem cL_LLLL {aA aB bA bB : P.Line} (hcAB : cA ≠ cB)
    (haAB : aA ≠ aB) (hbAB : bA ≠ bB) :
    HornConc (ln aA) (ln aB) (ln bA) (ln bB) (ln cA) (ln cB) := by
  by_cases hpr : aA = cA ∧ aB = cB
  · obtain ⟨p, r⟩ := hpr; subst p; subst r; exact hornConc_of_le_cb (le_refl _)
  by_cases hqs : cA = bA ∧ cB = bB
  · obtain ⟨q, s⟩ := hqs; subst q; subst s; exact hornConc_of_le_ac (le_refl _)
  by_cases p : aA = cA
  · have r : aB ≠ cB := fun h => hpr ⟨p, h⟩
    by_cases q : cA = bA
    · have s : cB ≠ bB := fun h => hqs ⟨q, h⟩
      exact topA_S_row1 (join_ln_ln_ne r) (join_ln_ln_ne s)
    · by_cases s : cB = bB
      · -- TFFT: M_ac=ln aA, M_cb=ln bB, join ⊤ since aA≠bB
        subst p
        have haAbB : aA ≠ bB := fun h => hcAB (h.trans s.symm)
        have hMac : ((ln aA).join (ln aA)).meet ((ln aB).join (ln cB)) = ln aA := by
          rw [join_ln_ln_self, join_ln_ln_ne r, meet_top_right]
        have hMcb : ((ln aA).join (ln bA)).meet ((ln cB).join (ln bB)) = ln bB := by
          rw [join_ln_ln_ne q, s, join_ln_ln_self, meet_top_left]
        unfold HornConc
        rw [hMac, hMcb, join_ln_ln_ne haAbB]
        exact le_top _
      · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_ln_ne s)
  · by_cases q : cA = bA
    · have s : cB ≠ bB := fun h => hqs ⟨q, h⟩
      by_cases r : aB = cB
      · -- FTTF: M_ac=ln aB, M_cb=ln cA, join ⊤ since aB≠cA
        subst q
        have haBcA : aB ≠ cA := fun h => hcAB (h.symm.trans r)
        have hMac : ((ln aA).join (ln cA)).meet ((ln aB).join (ln cB)) = ln aB := by
          rw [join_ln_ln_ne p, ← r, join_ln_ln_self, meet_top_left]
        have hMcb : ((ln cA).join (ln cA)).meet ((ln cB).join (ln bB)) = ln cA := by
          rw [join_ln_ln_self, join_ln_ln_ne s, meet_top_right]
        unfold HornConc
        rw [hMac, hMcb, join_ln_ln_ne haBcA]
        exact le_top _
      · exact topA_S_ac (by rw [join_ln_ln_ne p]; exact le_top _)
          (by rw [join_ln_ln_ne r]; exact le_top _)
    · exact topA_S_col2 (join_ln_ln_ne p) (join_ln_ln_ne q)

/-- cL leaf `(aPL, bPL)`.  The point-point join lives only in the LHS; `M_ac`
    and `M_cb` are line-based, so all 14 non-residual combos dominate through
    `join_mono` against `incid`-as-`le`.  Two residual combos join to `⊤`. -/
theorem cL_PLPL {av bv : P.Point} {aB bB : P.Line} (hcAB : cA ≠ cB)
    (hav : ¬ P.incid av aB) (hbv : ¬ P.incid bv bB) :
    HornConc (pt av) (ln aB) (pt bv) (ln bB) (ln cA) (ln cB) := by
  by_cases p : P.incid av cA <;> by_cases q : P.incid bv cA <;>
    by_cases r : aB = cB <;> by_cases s : cB = bB <;>
  first
    | exact hornConc_of_le_ac (le_meet
        (by first | exact le_trans (meet_le_left _ _) (join_mono (le_refl _) q)
                  | (rw [join_pt_ln_not p]; exact le_top _))
        (by first | (rw [join_ln_ln_ne r]; exact le_top _)
                  | exact le_trans (meet_le_right _ _) (join_mono (le_refl _) s.symm)))
    | exact hornConc_of_le_cb (le_meet
        (by first | exact le_trans (meet_le_left _ _) (join_mono p (le_refl _))
                  | (rw [join_ln_pt_not q]; exact le_top _))
        (by first | exact le_trans (meet_le_right _ _) (join_mono r (le_refl _))
                  | (rw [join_ln_ln_ne s]; exact le_top _)))
    | (have hMac : ((pt av).join (ln cA)).meet ((ln aB).join (ln cB)) = ln cA := by
          rw [join_pt_ln_incid p, join_ln_ln_ne r, meet_top_right]
       have hMcb : ((ln cA).join (pt bv)).meet ((ln cB).join (ln bB)) = ln cB := by
          rw [join_ln_pt_not q, ← s, join_ln_ln_self, meet_top_left]
       unfold HornConc
       rw [hMac, hMcb, join_ln_ln_ne hcAB]; exact le_top _)
    | (have haBcA : aB ≠ cA := fun h => hcAB (h.symm.trans r)
       have hMac : ((pt av).join (ln cA)).meet ((ln aB).join (ln cB)) = ln aB := by
          rw [join_pt_ln_not p, ← r, join_ln_ln_self, meet_top_left]
       have hMcb : ((ln cA).join (pt bv)).meet ((ln cB).join (ln bB)) = ln cA := by
          rw [join_ln_pt_incid q, join_ln_ln_ne s, meet_top_right]
       unfold HornConc
       rw [hMac, hMcb, join_ln_ln_ne haBcA]; exact le_top _)

/-- cL leaf `(aLP, bLP)`.  Mirror of `cL_PLPL` with the point-point join in
    row 2. -/
theorem cL_LPLP {aw bw : P.Point} {aA bA : P.Line} (hcAB : cA ≠ cB)
    (haw : ¬ P.incid aw aA) (hbw : ¬ P.incid bw bA) :
    HornConc (ln aA) (pt aw) (ln bA) (pt bw) (ln cA) (ln cB) := by
  by_cases p : aA = cA <;> by_cases q : cA = bA <;>
    by_cases t : P.incid aw cB <;> by_cases u : P.incid bw cB <;>
  first
    | exact hornConc_of_le_ac (le_meet
        (by first | exact le_trans (meet_le_left _ _) (join_mono (le_refl _) q.symm)
                  | (rw [join_ln_ln_ne p]; exact le_top _))
        (by first | (rw [join_pt_ln_not t]; exact le_top _)
                  | exact le_trans (meet_le_right _ _) (join_mono (le_refl _) u)))
    | exact hornConc_of_le_cb (le_meet
        (by first | exact le_trans (meet_le_left _ _) (join_mono p (le_refl _))
                  | (rw [join_ln_ln_ne q]; exact le_top _))
        (by first | exact le_trans (meet_le_right _ _) (join_mono t (le_refl _))
                  | (rw [join_ln_pt_not u]; exact le_top _)))
    | (have haAcB : aA ≠ cB := fun h => hcAB (p.symm.trans h)
       have hMac : ((ln aA).join (ln cA)).meet ((pt aw).join (ln cB)) = ln aA := by
          rw [← p, join_ln_ln_self, join_pt_ln_not t, meet_top_right]
       have hMcb : ((ln cA).join (ln bA)).meet ((ln cB).join (pt bw)) = ln cB := by
          rw [join_ln_ln_ne q, join_ln_pt_incid u, meet_top_left]
       unfold HornConc
       rw [hMac, hMcb, join_ln_ln_ne haAcB]; exact le_top _)
    | (have hMac : ((ln aA).join (ln cA)).meet ((pt aw).join (ln cB)) = ln cB := by
          rw [join_ln_ln_ne p, join_pt_ln_incid t, meet_top_left]
       have hMcb : ((ln cA).join (ln bA)).meet ((ln cB).join (pt bw)) = ln cA := by
          rw [← q, join_ln_ln_self, join_ln_pt_not u, meet_top_right]
       unfold HornConc
       rw [hMac, hMcb, join_ln_ln_ne (fun h => hcAB h.symm)]; exact le_top _)

/-- cL leaf `(aLL, bPL)`. -/
theorem cL_LLPL {aA aB bB : P.Line} {bv : P.Point} (hcAB : cA ≠ cB)
    (haAB : aA ≠ aB) (hbv : ¬ P.incid bv bB) :
    HornConc (ln aA) (ln aB) (pt bv) (ln bB) (ln cA) (ln cB) := by
  by_cases hpr : aA = cA ∧ aB = cB
  · obtain ⟨p, r⟩ := hpr; subst p; subst r; exact hornConc_of_le_cb (le_refl _)
  by_cases p : aA = cA
  · have r : aB ≠ cB := fun h => hpr ⟨p, h⟩
    by_cases q : P.incid bv cA
    · by_cases s : cB = bB
      · -- combo3 TTFT: M_ac=ln aA ⊒ LHS
        subst p
        exact hornConc_of_le_ac (le_meet
          (by rw [join_ln_ln_self, join_ln_pt_incid q]; exact meet_le_left _ _)
          (by rw [join_ln_ln_ne r]; exact le_top _))
      · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_ln_ne s)
    · by_cases s : cB = bB
      · -- combo7 TFFT: M_ac=ln aA, M_cb=ln bB, join ⊤
        subst p
        have haAbB : aA ≠ bB := fun h => hcAB (h.trans s.symm)
        have hMac : ((ln aA).join (ln aA)).meet ((ln aB).join (ln cB)) = ln aA := by
          rw [join_ln_ln_self, join_ln_ln_ne r, meet_top_right]
        have hMcb : ((ln aA).join (pt bv)).meet ((ln cB).join (ln bB)) = ln bB := by
          rw [join_ln_pt_not q, s, join_ln_ln_self, meet_top_left]
        unfold HornConc
        rw [hMac, hMcb, join_ln_ln_ne haAbB]
        exact le_top _
      · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_ln_ne s)
  · by_cases q : P.incid bv cA
    · by_cases r : aB = cB
      · by_cases s : cB = bB
        · -- combo9 FTTT: M_ac=ln aB ⊒ LHS
          subst r; subst s
          exact hornConc_of_le_ac (le_meet (by rw [join_ln_ln_ne p]; exact le_top _)
            (by rw [join_ln_ln_self]; exact meet_le_right _ _))
        · -- combo10 FTTF: M_ac=ln aB, M_cb=ln cA, join ⊤
          have haBcA : aB ≠ cA := fun h => hcAB (h.symm.trans r)
          have hMac : ((ln aA).join (ln cA)).meet ((ln aB).join (ln cB)) = ln aB := by
            rw [join_ln_ln_ne p, ← r, join_ln_ln_self, meet_top_left]
          have hMcb : ((ln cA).join (pt bv)).meet ((ln cB).join (ln bB)) = ln cA := by
            rw [join_ln_pt_incid q, join_ln_ln_ne s, meet_top_right]
          unfold HornConc
          rw [hMac, hMcb, join_ln_ln_ne haBcA]
          exact le_top _
      · exact topA_S_ac (by rw [join_ln_ln_ne p]; exact le_top _)
          (by rw [join_ln_ln_ne r]; exact le_top _)
    · exact topA_S_col2 (join_ln_ln_ne p) (join_ln_pt_not q)

/-- cL leaf `(aLL, bLP)`. -/
theorem cL_LLLP {aA aB bA : P.Line} {bw : P.Point} (hcAB : cA ≠ cB)
    (haAB : aA ≠ aB) (hbw : ¬ P.incid bw bA) :
    HornConc (ln aA) (ln aB) (ln bA) (pt bw) (ln cA) (ln cB) := by
  by_cases hpr : aA = cA ∧ aB = cB
  · obtain ⟨p, r⟩ := hpr; subst p; subst r; exact hornConc_of_le_cb (le_refl _)
  by_cases p : aA = cA
  · have r : aB ≠ cB := fun h => hpr ⟨p, h⟩
    by_cases q : cA = bA
    · by_cases s : P.incid bw cB
      · -- combo3
        subst p; subst q
        exact hornConc_of_le_ac (le_meet
          (by rw [join_ln_ln_self]; exact meet_le_left _ _)
          (by rw [join_ln_ln_ne r]; exact le_top _))
      · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_pt_not s)
    · by_cases s : P.incid bw cB
      · -- combo7
        subst p
        have hMac : ((ln aA).join (ln aA)).meet ((ln aB).join (ln cB)) = ln aA := by
          rw [join_ln_ln_self, join_ln_ln_ne r, meet_top_right]
        have hMcb : ((ln aA).join (ln bA)).meet ((ln cB).join (pt bw)) = ln cB := by
          rw [join_ln_ln_ne q, join_ln_pt_incid s, meet_top_left]
        unfold HornConc
        rw [hMac, hMcb, join_ln_ln_ne hcAB]
        exact le_top _
      · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_pt_not s)
  · by_cases q : cA = bA
    · by_cases r : aB = cB
      · by_cases s : P.incid bw cB
        · -- combo9
          have hbwaB : P.incid bw aB := by rw [r]; exact s
          exact hornConc_of_le_ac (le_meet (by rw [join_ln_ln_ne p]; exact le_top _)
            (by rw [← r, join_ln_ln_self, join_ln_pt_incid hbwaB]; exact meet_le_right _ _))
        · -- combo10
          subst q
          have haBcA : aB ≠ cA := fun h => hcAB (h.symm.trans r)
          have hMac : ((ln aA).join (ln cA)).meet ((ln aB).join (ln cB)) = ln aB := by
            rw [join_ln_ln_ne p, ← r, join_ln_ln_self, meet_top_left]
          have hMcb : ((ln cA).join (ln cA)).meet ((ln cB).join (pt bw)) = ln cA := by
            rw [join_ln_ln_self, join_ln_pt_not s, meet_top_right]
          unfold HornConc
          rw [hMac, hMcb, join_ln_ln_ne haBcA]
          exact le_top _
      · exact topA_S_ac (by rw [join_ln_ln_ne p]; exact le_top _)
          (by rw [join_ln_ln_ne r]; exact le_top _)
    · exact topA_S_col2 (join_ln_ln_ne p) (join_ln_ln_ne q)

/-- cL leaf `(aPL, bLP)`.  No point-point joins, so all meets are meetPoints;
    the point entries are handled by `join_mono` against `incid`-as-`le`. -/
theorem cL_PLLP {av bw : P.Point} {aB bA : P.Line} (hcAB : cA ≠ cB)
    (hav : ¬ P.incid av aB) (hbw : ¬ P.incid bw bA) :
    HornConc (pt av) (ln aB) (ln bA) (pt bw) (ln cA) (ln cB) := by
  by_cases p : P.incid av cA
  · by_cases q : cA = bA
    · by_cases r : aB = cB
      · by_cases s : P.incid bw cB
        · -- TTTT
          subst q
          exact hornConc_of_le_ac (le_meet (meet_le_left _ _)
            (le_trans (meet_le_right _ _) (join_mono (le_refl (ln aB)) s)))
        · -- TTTF
          exact hornConc_of_le_cb (le_meet
            (le_trans (meet_le_left _ _) (join_mono p (le_refl _)))
            (by rw [join_ln_pt_not s]; exact le_top _))
      · by_cases s : P.incid bw cB
        · -- TTFT
          subst q
          exact hornConc_of_le_ac (le_meet (meet_le_left _ _)
            (by rw [join_ln_ln_ne r]; exact le_top _))
        · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_pt_not s)
    · by_cases r : aB = cB
      · by_cases s : P.incid bw cB
        · -- TFTT
          exact hornConc_of_le_cb (le_meet (by rw [join_ln_ln_ne q]; exact le_top _)
            (by rw [← r]; exact meet_le_right _ _))
        · exact topA_S_cb (by rw [join_ln_ln_ne q]; exact le_top _)
            (by rw [join_ln_pt_not s]; exact le_top _)
      · by_cases s : P.incid bw cB
        · -- TFFT
          have hMac : ((pt av).join (ln cA)).meet ((ln aB).join (ln cB)) = ln cA := by
            rw [join_pt_ln_incid p, join_ln_ln_ne r, meet_top_right]
          have hMcb : ((ln cA).join (ln bA)).meet ((ln cB).join (pt bw)) = ln cB := by
            rw [join_ln_ln_ne q, join_ln_pt_incid s, meet_top_left]
          unfold HornConc
          rw [hMac, hMcb, join_ln_ln_ne hcAB]
          exact le_top _
        · exact topA_S_row1 (join_ln_ln_ne r) (join_ln_pt_not s)
  · by_cases q : cA = bA
    · by_cases r : aB = cB
      · by_cases s : P.incid bw cB
        · -- FTTT
          have hbwaB : P.incid bw aB := by rw [r]; exact s
          exact hornConc_of_le_ac (le_meet (by rw [join_pt_ln_not p]; exact le_top _)
            (by rw [← r, join_ln_ln_self, join_ln_pt_incid hbwaB]; exact meet_le_right _ _))
        · -- FTTF
          subst q
          have haBcA : aB ≠ cA := fun h => hcAB (h.symm.trans r)
          have hMac : ((pt av).join (ln cA)).meet ((ln aB).join (ln cB)) = ln aB := by
            rw [join_pt_ln_not p, ← r, join_ln_ln_self, meet_top_left]
          have hMcb : ((ln cA).join (ln cA)).meet ((ln cB).join (pt bw)) = ln cA := by
            rw [join_ln_ln_self, join_ln_pt_not s, meet_top_right]
          unfold HornConc
          rw [hMac, hMcb, join_ln_ln_ne haBcA]
          exact le_top _
      · exact topA_S_ac (by rw [join_pt_ln_not p]; exact le_top _)
          (by rw [join_ln_ln_ne r]; exact le_top _)
    · exact topA_S_col2 (join_pt_ln_not p) (join_ln_ln_ne q)

/-- Dispatcher for a c-column `(ln cA, ln cB)` (`cA ≠ cB`). -/
theorem htA_cL (a₁ a₂ b₁ b₂ : PElem P) (hcAB : cA ≠ cB)
    (ha1 : a₁ ≠ top) (ha2 : a₂ ≠ top) (hb1 : b₁ ≠ top) (hb2 : b₂ ≠ top)
    (hKA : a₁.join a₂ = top) (hKB : b₁.join b₂ = top) :
    HornConc a₁ a₂ b₁ b₂ (ln cA) (ln cB) := by
  rcases bigPair_cases hKA ha1 ha2 with
      ⟨av, aB, rfl, rfl, hav⟩ | ⟨aA, aw, rfl, rfl, haw⟩ | ⟨aA, aB, rfl, rfl, haAB⟩ <;>
    rcases bigPair_cases hKB hb1 hb2 with
      ⟨bv, bB, rfl, rfl, hbv⟩ | ⟨bA, bw, rfl, rfl, hbw⟩ | ⟨bA, bB, rfl, rfl, hbAB⟩
  · exact cL_PLPL hcAB hav hbv
  · exact cL_PLLP hcAB hav hbw
  · exact HornConc.of_swap_ab (cL_LLPL hcAB hbAB hav)
  · exact HornConc.of_swap_ab (cL_PLLP hcAB hbv haw)
  · exact cL_LPLP hcAB haw hbw
  · exact HornConc.of_swap_ab (cL_LLLP hcAB hbAB haw)
  · exact cL_LLPL hcAB haAB hbv
  · exact cL_LLLP hcAB haAB hbw
  · exact cL_LLLL hcAB haAB hbAB

end cL

/-! ## Assembly: the `famA` family (`H = ⊤`) -/

/-- **§2.157 converse, `famA`**: the `H = ⊤` degeneracy of the lattice Horn
    sentence.  The hypothesis meet `⊤` forces both column joins — and, through
    the Horn hypothesis, the c-column join — to `⊤`.  After pruning `⊤`-entries
    with the §2.157b pruning lemmas, dispatch on the c-column shape. -/
theorem hornTop_famA : ∀ (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P),
    (a₁.join a₂).meet (b₁.join b₂) = top →
    HornHyp a₁ a₂ b₁ b₂ c₁ c₂ → HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  intro a₁ a₂ b₁ b₂ c₁ c₂ hH hHyp
  have hHyp' : ((a₁.join a₂).meet (b₁.join b₂)).le (c₁.join c₂) := hHyp
  have hKA : a₁.join a₂ = top := eq_top_of_top_le (hH ▸ meet_le_left _ _)
  have hKB : b₁.join b₂ = top := eq_top_of_top_le (hH ▸ meet_le_right _ _)
  have hKC : c₁.join c₂ = top := eq_top_of_top_le (hH ▸ hHyp')
  by_cases ht : a₁ = top
  · subst ht; exact horn_top_a₁ hHyp
  by_cases ht2 : a₂ = top
  · subst ht2; exact horn_top_a₂ hHyp
  by_cases ht3 : b₁ = top
  · subst ht3; exact horn_top_b₁ hHyp
  by_cases ht4 : b₂ = top
  · subst ht4; exact horn_top_b₂ hHyp
  by_cases ht5 : c₁ = top
  · subst ht5; exact hornConc_top_c₁ _ _ _ _ _
  by_cases ht6 : c₂ = top
  · subst ht6; exact hornConc_top_c₂ _ _ _ _ _
  rcases bigPair_cases hKC ht5 ht6 with
      ⟨cv, cB, hc1, hc2, hc⟩ | ⟨cA, cw, hc1, hc2, hc⟩ | ⟨cA, cB, hc1, hc2, hcAB⟩
  · subst hc1; subst hc2
    exact htA_cP a₁ a₂ b₁ b₂ hc ht ht2 ht3 ht4 hKA hKB
  · subst hc1; subst hc2
    exact HornConc.of_swap_idx (htA_cP a₂ a₁ b₂ b₁ hc ht2 ht ht4 ht3
      (by rw [join_comm]; exact hKA) (by rw [join_comm]; exact hKB))
  · subst hc1; subst hc2
    exact htA_cL a₁ a₂ b₁ b₂ hcAB ht ht2 ht3 ht4 hKA hKB

end PElem

end Freyd.Alg
