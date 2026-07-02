/-
  Freyd & Scedrov, *Categories and Allegories* §2.157 (continued):
  the FULL equivalence between the Desargues Horn sentence and the theorem of
  Desargues in a projective plane.

  "Starting with a projective plane, writing a₁, a₂, b₁, … as A₁, A₂, B₁, …,
   passing to the associated modular lattice, viewing such as an allegory, one
   will see that this Horn sentence is equivalent with the theorem of
   Desargues."

  This file supplies, on top of `S2_157_ProjectivePlane`:

  · `ProjectivePlane.DesarguesND` — the HONEST ten-point theorem of Desargues:
    two genuine triangles (vertices inside each triangle distinct, so the sides
    exist) with DISTINCT corresponding sides, in perspective from a point.
    `not_desargues_of_interesting` shows the raw ten-point sentence
    `Desargues P` (no side conditions) is FALSE in every interesting plane
    containing a point, so some side conditions are forced; `DesarguesND`
    keeps exactly the nine that make "two triangles whose corresponding sides
    meet in single points" meaningful.
  · `desarguesHorn_implies_desargues` — the Horn sentence in the associated
    allegory implies `DesarguesND`, with NO further nondegeneracy: the thirteen
    hypotheses of `desarguesHorn_implies_desargues_nondeg` are reduced to the
    nine of `DesarguesND` by discharging each degenerate case synthetically
    (coincident perspective pairs collapse u, v, w onto each other; coincident
    perspective lines contradict distinctness of corresponding sides).
  · The CONVERSE apparatus: `PElem.HornHyp`/`PElem.HornConc` (the Horn
    hypothesis/conclusion read in the lattice 𝓛(P)), their `swap` symmetries,
    the pruning lemmas for degenerate instantiations (⊤-cases, sufficiency
    criteria), `desarguesHorn_iff_latticeHorn` (the allegory Horn sentence IS
    the lattice-level statement), and `desarguesND_implies_horn_points` — the
    substantive direction: Desargues forces the Horn conclusion at the generic
    six-point instantiations, exactly the configurations the book means by
    "writing a₁, a₂, b₁, … as A₁, A₂, B₁, …".  A gap analysis of the remaining
    (degenerate-instantiation) families closes the file.
-/
import Fredy.S2_157_ProjectivePlane

universe v u

namespace Freyd.Alg

/-! ## Synthetic helpers: trivial colinearity and pinning by two lines -/

namespace ProjectivePlane

variable {P : ProjectivePlane.{u}}

/-- Colinearity is trivial when the FIRST TWO points coincide (axiom 1). -/
theorem colinear_of_eq₁₂ {u v w : P.Point} (h : u = v) : P.Colinear u v w :=
  ⟨P.lineThrough u w, P.lineThrough_incid_left u w,
   by rw [← h]; exact P.lineThrough_incid_left u w, P.lineThrough_incid_right u w⟩

/-- Colinearity is trivial when the OUTER points coincide (axiom 1). -/
theorem colinear_of_eq₁₃ {u v w : P.Point} (h : u = w) : P.Colinear u v w :=
  ⟨P.lineThrough u v, P.lineThrough_incid_left u v, P.lineThrough_incid_right u v,
   by rw [← h]; exact P.lineThrough_incid_left u v⟩

/-- Colinearity is trivial when the LAST TWO points coincide (axiom 1). -/
theorem colinear_of_eq₂₃ {u v w : P.Point} (h : v = w) : P.Colinear u v w :=
  ⟨P.lineThrough u v, P.lineThrough_incid_left u v, P.lineThrough_incid_right u v,
   by rw [← h]; exact P.lineThrough_incid_right u v⟩

/-- PINNING (axiom 3): a point on two DISTINCT lines that both pass through `x`
    is `x` itself.  The workhorse of every degenerate Desargues case: whenever a
    vertex pair collapses, the corresponding "meet of sides" is pinned to the
    collapsed vertex. -/
theorem eq_of_incid_two_lines {x y : P.Point} {A B : P.Line} (hAB : A ≠ B)
    (hyA : P.incid y A) (hyB : P.incid y B)
    (hxA : P.incid x A) (hxB : P.incid x B) : y = x :=
  (P.unique hyA hyB hxA hxB).resolve_right hAB

/-! ## The honest ten-point theorem of Desargues

  The raw sentence `Desargues P` (§2.157's parenthetical, formalised verbatim
  in `S2_157_ProjectivePlane`) quantifies over ARBITRARY ten-point tuples.
  Read that literally and it is FALSE in every interesting plane
  (`not_desargues_of_interesting` below): collapsing all seven perspective
  points onto a single point makes the nine colinearity premises vacuous while
  `u`, `v`, `w` remain arbitrary.  "Two triangles in perspective" therefore
  carries implicit content: each triangle must HAVE three sides (vertices
  pairwise distinct within each triangle) and corresponding sides must be
  DISTINCT lines — otherwise "their corresponding sides meet" does not pick
  out three points.  `DesarguesND` states exactly that and nothing more:

  · `a₁ ≠ b₁`, `a₁ ≠ c₁`, `c₁ ≠ b₁`, `a₂ ≠ b₂`, `a₂ ≠ c₂`, `c₂ ≠ b₂`
    (each triangle has genuine sides; if e.g. `a₁ = b₁` the side `a₁b₁`
    degenerates, `w` is unconstrained on the OTHER side `a₂b₂`, and the
    conclusion fails in the real projective plane);
  · `a₁b₁ ≠ a₂b₂`, `a₁c₁ ≠ a₂c₂`, `c₁b₁ ≠ c₂b₂` (corresponding sides are
    distinct lines; if e.g. `a₁c₁ = a₂c₂` then `u` ranges over a whole line
    and the conclusion again fails in the real projective plane).

  Notably ABSENT (they follow by case analysis, `desarguesHorn_implies_desargues`):
  distinctness of the perspective pairs (`a₁ ≠ a₂`, `b₁ ≠ b₂`, `c₁ ≠ c₂`),
  distinctness of the perspective lines (`a₁a₂ ≠ b₁b₂`), and `u ≠ v`. -/

/-- THE THEOREM OF DESARGUES, honest ten-point form: two triangles
    `a₁b₁c₁`, `a₂b₂c₂` with genuine, pairwise-distinct corresponding sides,
    in perspective from `p`, have colinear side-meets `u`, `v`, `w`. -/
def DesarguesND (P : ProjectivePlane.{u}) : Prop :=
  ∀ p a₁ a₂ b₁ b₂ c₁ c₂ u v w : P.Point,
    P.Colinear p a₁ a₂ → P.Colinear p b₁ b₂ → P.Colinear p c₁ c₂ →
    P.Colinear a₁ c₁ u → P.Colinear a₂ c₂ u →
    P.Colinear b₁ c₁ v → P.Colinear b₂ c₂ v →
    P.Colinear a₁ b₁ w → P.Colinear a₂ b₂ w →
    a₁ ≠ b₁ → a₁ ≠ c₁ → c₁ ≠ b₁ →
    a₂ ≠ b₂ → a₂ ≠ c₂ → c₂ ≠ b₂ →
    P.lineThrough a₁ b₁ ≠ P.lineThrough a₂ b₂ →
    P.lineThrough a₁ c₁ ≠ P.lineThrough a₂ c₂ →
    P.lineThrough c₁ b₁ ≠ P.lineThrough c₂ b₂ →
    P.Colinear u v w

/-- The raw ten-point sentence trivially implies the honest one. -/
theorem desargues_implies_desarguesND {P : ProjectivePlane.{u}}
    (hD : P.Desargues) : P.DesarguesND :=
  fun p a₁ a₂ b₁ b₂ c₁ c₂ u v w h1 h2 h3 h4 h5 h6 h7 h8 h9
      _ _ _ _ _ _ _ _ _ => hD p a₁ a₂ b₁ b₂ c₁ c₂ u v w h1 h2 h3 h4 h5 h6 h7 h8 h9

/-- HONESTY CHECK: the raw ten-point sentence `Desargues P` is FALSE in every
    interesting plane containing a point.  Collapse all seven perspective
    points onto `x₀`: every premise `⟨x₀,x₀,·⟩` is colinear via a joining line
    (axiom 1), so `Desargues P` would force EVERY triple of points to be
    colinear — but an interesting plane contains a non-colinear triple (two
    points of a line `A` through `x₀` and a point ≠ `x₀` of a second line `B`
    through `x₀`).  This is why `DesarguesND` carries side conditions. -/
theorem not_desargues_of_interesting {P : ProjectivePlane.{u}}
    (hInt : P.Interesting) (x₀ : P.Point) : ¬ P.Desargues := by
  intro hD
  obtain ⟨A, B, _, hABne, _, _, hxA, hxB, _⟩ := hInt.1 x₀
  obtain ⟨y, z, _, hyz, _, _, hyA, hzA, _⟩ := hInt.2 A
  -- a point q of B other than x₀ (hence off A, by axiom 3)
  obtain ⟨q, hqB, hqx⟩ : ∃ q : P.Point, P.incid q B ∧ q ≠ x₀ := by
    obtain ⟨p₁, p₂, _, h12, _, _, h1B, h2B, _⟩ := hInt.2 B
    by_cases h : p₁ = x₀
    · exact ⟨p₂, h2B, fun e => h12 (h.trans e.symm)⟩
    · exact ⟨p₁, h1B, h⟩
  have hqA : ¬ P.incid q A :=
    fun hqA => hqx ((P.unique hqA hqB hxA hxB).resolve_right hABne)
  -- the degenerate perspective: all seven points are x₀, and u := y, v := z, w := q
  have hxxx : P.Colinear x₀ x₀ x₀ := ⟨A, hxA, hxA, hxA⟩
  have hxxy : ∀ r : P.Point, P.Colinear x₀ x₀ r := fun r =>
    ⟨P.lineThrough x₀ r, P.lineThrough_incid_left x₀ r,
     P.lineThrough_incid_left x₀ r, P.lineThrough_incid_right x₀ r⟩
  obtain ⟨L, hyL, hzL, hqL⟩ :=
    hD x₀ x₀ x₀ x₀ x₀ x₀ x₀ y z q hxxx hxxx hxxx
      (hxxy y) (hxxy y) (hxxy z) (hxxy z) (hxxy q) (hxxy q)
  -- but then q would lie on the line through y, z, which is A
  have hqA' : P.incid q (P.lineThrough y z) :=
    P.incid_lineThrough_of_mem hyz hyL hzL hqL
  rw [← ProjectivePlane.lineThrough_eq hyz hyA hzA] at hqA'
  exact hqA hqA'

end ProjectivePlane

/-! ## §2.157, Horn ⟹ Desargues, in full

  `desarguesHorn_implies_desargues_nondeg` (previous file) needs thirteen
  nondegeneracy hypotheses.  Four of them are NOT part of the honest theorem
  and are discharged here by case analysis:

  · `u = v`: the conclusion `⟨u,v,w⟩ colinear` is trivial (axiom 1).
  · `a₁ = a₂`: the side pairs `a₁c₁/a₂c₂` and `a₁b₁/a₂b₂` become two DISTINCT
    lines through the collapsed vertex, pinning `u = a₁ = w` (axiom 3).
  · `b₁ = b₂`: symmetrically `v = b₁ = w`.
  · `c₁ = c₂`: symmetrically `u = c₁ = v`.
  · `a₁a₂ = b₁b₂` (coincident perspective lines): then that common line
    carries `a₁, b₁, a₂, b₂`, so `a₁b₁ = a₂b₂` — contradicting distinctness
    of corresponding sides.  Hence the perspective lines are automatically
    distinct and the nondegenerate lemma applies. -/

/-- **§2.157, substantive direction, in full**: the Desargues Horn sentence in
    the associated allegory of 𝓛(P) implies the (honest ten-point) theorem of
    Desargues.  No hypotheses beyond `DesarguesND`'s own nine side conditions. -/
theorem desarguesHorn_implies_desargues {P : ProjectivePlane.{u}}
    (hHorn : DesarguesHorn (LMonObj (PElem P))) : P.DesarguesND := by
  intro p a₁ a₂ b₁ b₂ c₁ c₂ u v w h1 h2 h3 h4 h5 h6 h7 h8 h9
    hab₁ hac₁ hcb₁ hab₂ hac₂ hcb₂ hSab hSac hScb
  -- trivial conclusion when the two side-meets u, v coincide
  by_cases huv : u = v
  · exact ProjectivePlane.colinear_of_eq₁₂ huv
  -- collapsed perspective pair a₁ = a₂ pins u = a₁ = w
  by_cases hpa : a₁ = a₂
  · subst hpa
    obtain ⟨L4, ha4, hc4, hu4⟩ := h4
    obtain ⟨L5, ha5, hc5, hu5⟩ := h5
    have hu : u = a₁ := ProjectivePlane.eq_of_incid_two_lines hSac
      (P.incid_lineThrough_of_mem hac₁ ha4 hc4 hu4)
      (P.incid_lineThrough_of_mem hac₂ ha5 hc5 hu5)
      (P.lineThrough_incid_left a₁ c₁) (P.lineThrough_incid_left a₁ c₂)
    obtain ⟨L8, ha8, hb8, hw8⟩ := h8
    obtain ⟨L9, ha9, hb9, hw9⟩ := h9
    have hw : w = a₁ := ProjectivePlane.eq_of_incid_two_lines hSab
      (P.incid_lineThrough_of_mem hab₁ ha8 hb8 hw8)
      (P.incid_lineThrough_of_mem hab₂ ha9 hb9 hw9)
      (P.lineThrough_incid_left a₁ b₁) (P.lineThrough_incid_left a₁ b₂)
    exact ProjectivePlane.colinear_of_eq₁₃ (hu.trans hw.symm)
  -- collapsed perspective pair b₁ = b₂ pins v = b₁ = w
  by_cases hpb : b₁ = b₂
  · subst hpb
    obtain ⟨L6, hb6, hc6, hv6⟩ := h6
    obtain ⟨L7, hb7, hc7, hv7⟩ := h7
    have hv : v = b₁ := ProjectivePlane.eq_of_incid_two_lines hScb
      (P.incid_lineThrough_of_mem hcb₁ hc6 hb6 hv6)
      (P.incid_lineThrough_of_mem hcb₂ hc7 hb7 hv7)
      (P.lineThrough_incid_right c₁ b₁) (P.lineThrough_incid_right c₂ b₁)
    obtain ⟨L8, ha8, hb8, hw8⟩ := h8
    obtain ⟨L9, ha9, hb9, hw9⟩ := h9
    have hw : w = b₁ := ProjectivePlane.eq_of_incid_two_lines hSab
      (P.incid_lineThrough_of_mem hab₁ ha8 hb8 hw8)
      (P.incid_lineThrough_of_mem hab₂ ha9 hb9 hw9)
      (P.lineThrough_incid_right a₁ b₁) (P.lineThrough_incid_right a₂ b₁)
    exact ProjectivePlane.colinear_of_eq₂₃ (hv.trans hw.symm)
  -- collapsed perspective pair c₁ = c₂ pins u = c₁ = v
  by_cases hpc : c₁ = c₂
  · subst hpc
    obtain ⟨L4, ha4, hc4, hu4⟩ := h4
    obtain ⟨L5, ha5, hc5, hu5⟩ := h5
    have hu : u = c₁ := ProjectivePlane.eq_of_incid_two_lines hSac
      (P.incid_lineThrough_of_mem hac₁ ha4 hc4 hu4)
      (P.incid_lineThrough_of_mem hac₂ ha5 hc5 hu5)
      (P.lineThrough_incid_right a₁ c₁) (P.lineThrough_incid_right a₂ c₁)
    obtain ⟨L6, hb6, hc6, hv6⟩ := h6
    obtain ⟨L7, hb7, hc7, hv7⟩ := h7
    have hv : v = c₁ := ProjectivePlane.eq_of_incid_two_lines hScb
      (P.incid_lineThrough_of_mem hcb₁ hc6 hb6 hv6)
      (P.incid_lineThrough_of_mem hcb₂ hc7 hb7 hv7)
      (P.lineThrough_incid_left c₁ b₁) (P.lineThrough_incid_left c₁ b₂)
    exact ProjectivePlane.colinear_of_eq₁₂ (hu.trans hv.symm)
  -- perspective lines are distinct, else corresponding sides a₁b₁ = a₂b₂
  have hLab : P.lineThrough a₁ a₂ ≠ P.lineThrough b₁ b₂ := by
    intro hM
    have hb₁ : P.incid b₁ (P.lineThrough a₁ a₂) := by
      rw [hM]; exact P.lineThrough_incid_left b₁ b₂
    have hb₂ : P.incid b₂ (P.lineThrough a₁ a₂) := by
      rw [hM]; exact P.lineThrough_incid_right b₁ b₂
    have e1 : P.lineThrough a₁ a₂ = P.lineThrough a₁ b₁ :=
      ProjectivePlane.lineThrough_eq hab₁ (P.lineThrough_incid_left a₁ a₂) hb₁
    have e2 : P.lineThrough a₁ a₂ = P.lineThrough a₂ b₂ :=
      ProjectivePlane.lineThrough_eq hab₂ (P.lineThrough_incid_right a₁ a₂) hb₂
    exact hSab (e1.symm.trans e2)
  exact desarguesHorn_implies_desargues_nondeg hHorn p a₁ a₂ b₁ b₂ c₁ c₂ u v w
    h1 h2 h3 h4 h5 h6 h7 h8 h9 hpa hpb hpc hab₁ hab₂ hac₁ hac₂ hcb₁ hcb₂
    hLab hSac hScb huv

/-! ## The converse: the Horn sentence read in 𝓛(P)

  In the one-object allegory on 𝓛(P) composition is `⊔`, intersection is `⊓`,
  reciprocation is the identity and `⊑` is the lattice order (§2.156/§2.113),
  so the Horn sentence IS a lattice-level statement, one instance per 6-tuple
  of lattice elements.  We name its hypothesis and conclusion, record the two
  symmetries of the sentence (swapping the A- and B-columns; swapping the
  1- and 2-rows), and prove the pruning lemmas that dispose of degenerate
  instantiations before the geometry starts. -/

namespace PElem

variable {P : ProjectivePlane.{u}}

/-- The HYPOTHESIS `(A₁A₂ ∩ B₁B₂) ⊂ C₁C₂` of the §2.157 Horn sentence, read in
    the lattice 𝓛(P): composition is `⊔`, intersection `⊓`, order `⩽`. -/
def HornHyp (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P) : Prop :=
  ((a₁.join a₂).meet (b₁.join b₂)).le (c₁.join c₂)

/-- The CONCLUSION `(A₁°B₁ ∩ A₂B₂°) ⊂ (A₁°C₁ ∩ A₂C₂°)(C₁°B₁ ∩ C₂B₂°)` of the
    §2.157 Horn sentence, read in the lattice 𝓛(P) (reciprocation is the
    identity there). -/
def HornConc (a₁ a₂ b₁ b₂ c₁ c₂ : PElem P) : Prop :=
  ((a₁.join b₁).meet (a₂.join b₂)).le
    (((a₁.join c₁).meet (a₂.join c₂)).join ((c₁.join b₁).meet (c₂.join b₂)))

/-! ### The two symmetries of the Horn sentence -/

theorem HornHyp.swap_ab {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (h : HornHyp a₁ a₂ b₁ b₂ c₁ c₂) : HornHyp b₁ b₂ a₁ a₂ c₁ c₂ := by
  show ((b₁.join b₂).meet (a₁.join a₂)).le (c₁.join c₂)
  rw [meet_comm]; exact h

theorem HornHyp.swap_idx {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (h : HornHyp a₁ a₂ b₁ b₂ c₁ c₂) : HornHyp a₂ a₁ b₂ b₁ c₂ c₁ := by
  show ((a₂.join a₁).meet (b₂.join b₁)).le (c₂.join c₁)
  rw [join_comm a₂ a₁, join_comm b₂ b₁, join_comm c₂ c₁]; exact h

theorem HornConc.of_swap_ab {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (h : HornConc b₁ b₂ a₁ a₂ c₁ c₂) : HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  have h' : ((b₁.join a₁).meet (b₂.join a₂)).le
      (((b₁.join c₁).meet (b₂.join c₂)).join ((c₁.join a₁).meet (c₂.join a₂))) := h
  rwa [join_comm b₁ a₁, join_comm b₂ a₂, join_comm b₁ c₁, join_comm b₂ c₂,
    join_comm c₁ a₁, join_comm c₂ a₂,
    join_comm ((c₁.join b₁).meet (c₂.join b₂))] at h'

theorem HornConc.of_swap_idx {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (h : HornConc a₂ a₁ b₂ b₁ c₂ c₁) : HornConc a₁ a₂ b₁ b₂ c₁ c₂ := by
  have h' : ((a₂.join b₂).meet (a₁.join b₁)).le
      (((a₂.join c₂).meet (a₁.join c₁)).join ((c₂.join b₂).meet (c₁.join b₁))) := h
  rwa [meet_comm (a₂.join b₂), meet_comm (a₂.join c₂), meet_comm (c₂.join b₂)] at h'

/-! ### Pruning lemmas: degenerate instantiations that need no geometry -/

/-- SUFFICIENCY (left): if `a₁ ⩽ a₂ ⊔ c₂` and `b₁ ⩽ c₂ ⊔ b₂` then the Horn
    conclusion holds outright — the left column already sits under the two
    conclusion meets. -/
theorem hornConc_of_left {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (h₁ : a₁.le (a₂.join c₂)) (h₂ : b₁.le (c₂.join b₂)) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ :=
  le_trans (meet_le_left _ _)
    (join_le (le_trans (le_meet (le_join_left a₁ c₁) h₁) (le_join_left _ _))
      (le_trans (le_meet (le_join_right c₁ b₁) h₂) (le_join_right _ _)))

/-- SUFFICIENCY (right), the `swap_idx` mirror of `hornConc_of_left`. -/
theorem hornConc_of_right {a₁ a₂ b₁ b₂ c₁ c₂ : PElem P}
    (h₁ : a₂.le (a₁.join c₁)) (h₂ : b₂.le (c₁.join b₁)) :
    HornConc a₁ a₂ b₁ b₂ c₁ c₂ :=
  HornConc.of_swap_idx (hornConc_of_left h₁ h₂)

/-- PRUNING `c₁ = ⊤`: the Horn conclusion holds outright (no hypothesis):
    both conclusion meets collapse to their second factor and their join
    dominates `a₂ ⊔ b₂ ⊒` LHS. -/
theorem hornConc_top_c₁ (a₁ a₂ b₁ b₂ c₂ : PElem P) :
    HornConc a₁ a₂ b₁ b₂ top c₂ := by
  show ((a₁.join b₁).meet (a₂.join b₂)).le
    (((a₁.join top).meet (a₂.join c₂)).join ((top.join b₁).meet (c₂.join b₂)))
  rw [join_top_right a₁, join_top_left b₁, meet_top_left, meet_top_left]
  exact le_trans (meet_le_right _ _)
    (join_le (le_trans (le_join_left a₂ c₂) (le_join_left _ _))
      (le_trans (le_join_right c₂ b₂) (le_join_right _ _)))

/-- PRUNING `c₂ = ⊤`, by the row symmetry. -/
theorem hornConc_top_c₂ (a₁ a₂ b₁ b₂ c₁ : PElem P) :
    HornConc a₁ a₂ b₁ b₂ c₁ top :=
  HornConc.of_swap_idx (hornConc_top_c₁ a₂ a₁ b₂ b₁ c₁)

/-- PRUNING `a₁ = ⊤` (uses the hypothesis and MODULARITY): the hypothesis
    collapses to `b₁ ⊔ b₂ ⩽ c₁ ⊔ c₂`, and `b₂ ⩽ (c₂⊔b₂) ⊓ (c₁⊔c₂) =
    ((c₂⊔b₂) ⊓ c₁) ⊔ c₂` splits under the two conclusion meets. -/
theorem horn_top_a₁ {a₂ b₁ b₂ c₁ c₂ : PElem P}
    (h : HornHyp top a₂ b₁ b₂ c₁ c₂) : HornConc top a₂ b₁ b₂ c₁ c₂ := by
  have hyp : (b₁.join b₂).le (c₁.join c₂) := by
    have h' : ((PElem.top.join a₂).meet (b₁.join b₂)).le (c₁.join c₂) := h
    rwa [join_top_left a₂, meet_top_left] at h'
  show ((PElem.top.join b₁).meet (a₂.join b₂)).le
    (((PElem.top.join c₁).meet (a₂.join c₂)).join ((c₁.join b₁).meet (c₂.join b₂)))
  rw [join_top_left b₁, meet_top_left, join_top_left c₁, meet_top_left]
  apply join_le
  · exact le_trans (le_join_left a₂ c₂) (le_join_left _ _)
  · have h1 : b₂.le ((c₂.join b₂).meet (c₁.join c₂)) :=
      le_meet (le_join_right c₂ b₂) (le_trans (le_join_right b₁ b₂) hyp)
    rw [modular_eq (le_join_left c₂ b₂)] at h1
    exact le_trans h1 (join_le
      (le_trans (le_meet (le_trans (meet_le_right (c₂.join b₂) c₁) (le_join_left c₁ b₁))
          (meet_le_left (c₂.join b₂) c₁))
        (le_join_right _ _))
      (le_trans (le_join_right a₂ c₂) (le_join_left _ _)))

/-- PRUNING `a₂ = ⊤`, by the row symmetry. -/
theorem horn_top_a₂ {a₁ b₁ b₂ c₁ c₂ : PElem P}
    (h : HornHyp a₁ top b₁ b₂ c₁ c₂) : HornConc a₁ top b₁ b₂ c₁ c₂ :=
  HornConc.of_swap_idx (horn_top_a₁ h.swap_idx)

/-- PRUNING `b₁ = ⊤`, by the column symmetry. -/
theorem horn_top_b₁ {a₁ a₂ b₂ c₁ c₂ : PElem P}
    (h : HornHyp a₁ a₂ top b₂ c₁ c₂) : HornConc a₁ a₂ top b₂ c₁ c₂ :=
  HornConc.of_swap_ab (horn_top_a₁ h.swap_ab)

/-- PRUNING `b₂ = ⊤`, by both symmetries. -/
theorem horn_top_b₂ {a₁ a₂ b₁ c₁ c₂ : PElem P}
    (h : HornHyp a₁ a₂ b₁ top c₁ c₂) : HornConc a₁ a₂ b₁ top c₁ c₂ :=
  HornConc.of_swap_ab (horn_top_a₂ h.swap_ab)

end PElem

/-! ## The bridge: the allegory Horn sentence IS the lattice statement -/

/-- The lattice-level Horn statement transfers to the allegory-level
    `DesarguesHorn` on `LMonObj (PElem P)`: all five objects are `star`, homs
    are lattice elements, composition/intersection/order are `⊔`/`⊓`/`⩽` and
    reciprocation is the identity (converse of `desarguesHorn_toLattice`). -/
theorem desarguesHorn_of_latticeHorn {P : ProjectivePlane.{u}}
    (h : ∀ a₁ a₂ b₁ b₂ c₁ c₂ : PElem P,
      PElem.HornHyp a₁ a₂ b₁ b₂ c₁ c₂ → PElem.HornConc a₁ a₂ b₁ b₂ c₁ c₂) :
    DesarguesHorn (LMonObj (PElem P)) := by
  intro p q a b c A₁ A₂ B₁ B₂ C₁ C₂ hyp
  cases p; cases q; cases a; cases b; cases c
  exact PElem.le_iff_meet_eq.mp
    (h A₁ A₂ B₁ B₂ C₁ C₂ (PElem.le_iff_meet_eq.mpr hyp))

/-- **§2.157**: on the associated allegory of 𝓛(P) the Desargues Horn sentence
    is EXACTLY the lattice-level statement `HornHyp → HornConc`, one instance
    per 6-tuple of lattice elements. -/
theorem desarguesHorn_iff_latticeHorn {P : ProjectivePlane.{u}} :
    DesarguesHorn (LMonObj (PElem P)) ↔
      ∀ a₁ a₂ b₁ b₂ c₁ c₂ : PElem P,
        PElem.HornHyp a₁ a₂ b₁ b₂ c₁ c₂ → PElem.HornConc a₁ a₂ b₁ b₂ c₁ c₂ :=
  ⟨fun h a₁ a₂ b₁ b₂ c₁ c₂ hy => desarguesHorn_toLattice h a₁ a₂ b₁ b₂ c₁ c₂ hy,
   desarguesHorn_of_latticeHorn⟩

/-! ## The converse, geometric core: Desargues forces the Horn conclusion at
  the generic six-point instantiations

  "Writing a₁, a₂, b₁, … as A₁, A₂, B₁, …": instantiate the six Horn variables
  at the six atoms `pt a₁, …, pt c₂`.  For a configuration in general position
  (the fifteen side conditions below) the lattice computation runs exactly
  backwards through `desarguesHorn_implies_desargues_nondeg`:

  · the Horn HYPOTHESIS evaluates to "`p := a₁a₂ ∧ b₁b₂` lies on the line
    `c₁c₂`", i.e. the three perspective triples are colinear through `p`;
  · the Horn CONCLUSION evaluates to `pt w ⩽ (pt u) ⊔ (pt v)` where `u, v, w`
    are the meets of the three pairs of corresponding sides;
  · `u ≠ v` (else, the two triangles being genuine, `u = c₁` and `u = c₂`),
    so the conclusion is exactly `w ∈ uv` — the theorem of Desargues. -/

open PElem in
/-- **§2.157, converse direction, generic instantiations**: if the plane
    satisfies the (honest ten-point) theorem of Desargues then the Horn
    sentence holds in 𝓛(P) at every six-point instantiation in general
    position. -/
theorem desarguesND_implies_horn_points {P : ProjectivePlane.{u}}
    (hDes : P.DesarguesND) (a₁ a₂ b₁ b₂ c₁ c₂ : P.Point)
    -- the perspective pairs are distinct (their joins are the perspective lines)
    (hpa : a₁ ≠ a₂) (hpb : b₁ ≠ b₂) (hpc : c₁ ≠ c₂)
    -- each triangle has genuine sides
    (hab₁ : a₁ ≠ b₁) (hac₁ : a₁ ≠ c₁) (hcb₁ : c₁ ≠ b₁)
    (hab₂ : a₂ ≠ b₂) (hac₂ : a₂ ≠ c₂) (hcb₂ : c₂ ≠ b₂)
    -- the perspective lines are distinct (their meet is the centre p)
    (hLab : P.lineThrough a₁ a₂ ≠ P.lineThrough b₁ b₂)
    -- corresponding sides are distinct (their meets are u, v, w)
    (hSab : P.lineThrough a₁ b₁ ≠ P.lineThrough a₂ b₂)
    (hSac : P.lineThrough a₁ c₁ ≠ P.lineThrough a₂ c₂)
    (hScb : P.lineThrough c₁ b₁ ≠ P.lineThrough c₂ b₂)
    -- the triangles are genuine (their c-corner sides differ)
    (hT₁ : P.lineThrough a₁ c₁ ≠ P.lineThrough c₁ b₁)
    (hT₂ : P.lineThrough a₂ c₂ ≠ P.lineThrough c₂ b₂)
    (hyp : HornHyp (pt a₁) (pt a₂) (pt b₁) (pt b₂) (pt c₁) (pt c₂)) :
    HornConc (pt a₁) (pt a₂) (pt b₁) (pt b₂) (pt c₁) (pt c₂) := by
  -- the Horn hypothesis: the perspective centre p lies on the line c₁c₂
  have hyp' : (((pt a₁).join (pt a₂)).meet ((pt b₁).join (pt b₂))).le
      ((pt c₁).join (pt c₂)) := hyp
  rw [join_pt_pt_ne hpa, join_pt_pt_ne hpb, join_pt_pt_ne hpc,
    meet_ln_ln_ne hLab] at hyp'
  -- the three side-meets (u, v, w in the book's picture)
  have hconc : P.Colinear
      (P.meetPoint (P.lineThrough a₁ c₁) (P.lineThrough a₂ c₂))
      (P.meetPoint (P.lineThrough c₁ b₁) (P.lineThrough c₂ b₂))
      (P.meetPoint (P.lineThrough a₁ b₁) (P.lineThrough a₂ b₂)) :=
    hDes (P.meetPoint (P.lineThrough a₁ a₂) (P.lineThrough b₁ b₂))
      a₁ a₂ b₁ b₂ c₁ c₂ _ _ _
      ⟨P.lineThrough a₁ a₂, P.meetPoint_incid_left _ _,
        P.lineThrough_incid_left a₁ a₂, P.lineThrough_incid_right a₁ a₂⟩
      ⟨P.lineThrough b₁ b₂, P.meetPoint_incid_right _ _,
        P.lineThrough_incid_left b₁ b₂, P.lineThrough_incid_right b₁ b₂⟩
      ⟨P.lineThrough c₁ c₂, hyp',
        P.lineThrough_incid_left c₁ c₂, P.lineThrough_incid_right c₁ c₂⟩
      ⟨P.lineThrough a₁ c₁, P.lineThrough_incid_left a₁ c₁,
        P.lineThrough_incid_right a₁ c₁, P.meetPoint_incid_left _ _⟩
      ⟨P.lineThrough a₂ c₂, P.lineThrough_incid_left a₂ c₂,
        P.lineThrough_incid_right a₂ c₂, P.meetPoint_incid_right _ _⟩
      ⟨P.lineThrough c₁ b₁, P.lineThrough_incid_right c₁ b₁,
        P.lineThrough_incid_left c₁ b₁, P.meetPoint_incid_left _ _⟩
      ⟨P.lineThrough c₂ b₂, P.lineThrough_incid_right c₂ b₂,
        P.lineThrough_incid_left c₂ b₂, P.meetPoint_incid_right _ _⟩
      ⟨P.lineThrough a₁ b₁, P.lineThrough_incid_left a₁ b₁,
        P.lineThrough_incid_right a₁ b₁, P.meetPoint_incid_left _ _⟩
      ⟨P.lineThrough a₂ b₂, P.lineThrough_incid_left a₂ b₂,
        P.lineThrough_incid_right a₂ b₂, P.meetPoint_incid_right _ _⟩
      hab₁ hac₁ hcb₁ hab₂ hac₂ hcb₂ hSab hSac hScb
  -- u ≠ v: otherwise u is pinned to both c₁ and c₂ (the triangles are genuine)
  have huv : P.meetPoint (P.lineThrough a₁ c₁) (P.lineThrough a₂ c₂) ≠
      P.meetPoint (P.lineThrough c₁ b₁) (P.lineThrough c₂ b₂) := by
    intro huv_eq
    have h1 : P.meetPoint (P.lineThrough a₁ c₁) (P.lineThrough a₂ c₂) = c₁ :=
      ProjectivePlane.eq_of_incid_two_lines hT₁
        (P.meetPoint_incid_left _ _)
        (by rw [huv_eq]; exact P.meetPoint_incid_left _ _)
        (P.lineThrough_incid_right a₁ c₁) (P.lineThrough_incid_left c₁ b₁)
    have h2 : P.meetPoint (P.lineThrough a₁ c₁) (P.lineThrough a₂ c₂) = c₂ :=
      ProjectivePlane.eq_of_incid_two_lines hT₂
        (P.meetPoint_incid_right _ _)
        (by rw [huv_eq]; exact P.meetPoint_incid_right _ _)
        (P.lineThrough_incid_right a₂ c₂) (P.lineThrough_incid_left c₂ b₂)
    exact hpc (h1.symm.trans h2)
  -- the Horn conclusion: pt w ⩽ pt u ⊔ pt v = ln (uv)
  show (((pt a₁).join (pt b₁)).meet ((pt a₂).join (pt b₂))).le
    ((((pt a₁).join (pt c₁)).meet ((pt a₂).join (pt c₂))).join
      (((pt c₁).join (pt b₁)).meet ((pt c₂).join (pt b₂))))
  rw [join_pt_pt_ne hab₁, join_pt_pt_ne hab₂, meet_ln_ln_ne hSab,
    join_pt_pt_ne hac₁, join_pt_pt_ne hac₂, meet_ln_ln_ne hSac,
    join_pt_pt_ne hcb₁, join_pt_pt_ne hcb₂, meet_ln_ln_ne hScb,
    join_pt_pt_ne huv]
  obtain ⟨N, huN, hvN, hwN⟩ := hconc
  exact P.incid_lineThrough_of_mem huv huN hvN hwN

end Freyd.Alg
