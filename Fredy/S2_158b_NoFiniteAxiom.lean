/-
  Freyd & Scedrov, *Categories and Allegories* §2.158, Target 3:
  **The equational theory of `Rel(S)` is NOT finitely axiomatizable.**

  The core §2.158 development (`Fredy/S2_158_GraphAllegory.lean`) gives the graph
  model of the free one-object representable allegory, the tautological Yoneda
  lemma `graph_yoneda`, and the decision procedure `decision`.  This file builds,
  on top of that core, the ingredients of Freyd's no-finite-axiomatizability
  metatheorem (last paragraphs of §2.158):

  * LAYER 2/3 (this file, Sorry-free): a semantic notion `HoldsInRel E₁ E₂`
    ("the containment `E₁ ⊆ E₂` is true in `Rel(S)` for every set `S` and every
    interpretation of the labels"), a term-substitution operation with its
    semantic soundness, the equational **derivation system** `Derives Ax` of an
    axiom set `Ax` (axiom-instances closed under reflexivity, transitivity, and
    the monotone congruences of `∩`, `;`, `°`), and the **soundness bridge**
    `Derives_sound`: every containment derivable from a *valid* axiom set is true
    in `Rel(S)`.

  * LAYER 1 (this file, Sorry-free): the **rhombus family** `rhL n ⊆ rhR n` and a
    proof that each member is valid in `Rel(S)` (`rhombus_holds`).

  * LAYER 4 (metatheorem): the counting argument is isolated as an explicit,
    precisely-stated combinatorial hypothesis `RhombusHard`, and the headline
    `no_finite_axiomatization` is proved *conditionally* on it (a faithful
    reduction — NO hole, no new axiom).  See the module report for why the
    remaining hypothesis is hard.

  STRICTLY MATHLIB-FREE.  Only Lean 4 core + `Fredy.*`.  Composition is in
  diagram order (`comp a b` = "first `a`, then `b`"), matching the core.
-/

import Fredy.S2_158_GraphAllegory

namespace Freyd.S2_158

variable {L : Type}

/-! ## Layer 2/3 — semantics of containments in `Rel(S)`

  A model of the labels `L` on a carrier `V` is an interpretation
  `ι : L → V → V → Prop` (each label a binary relation on `V`).  This is exactly
  an object of `Rel(S)` together with a chosen family of relations, i.e. Freyd's
  "set `S` with a family of binary relations `A, B, C, …`".  `eval ι E` is the
  relation that the allegorical term `E` denotes. -/

/-- The relation denoted by a term in the model `(V, ι)`.  Mirrors the core's
    `toRel` but over an arbitrary interpretation rather than a graph's edges. -/
def eval {V : Type} (ι : L → V → V → Prop) : Term L → V → V → Prop
  | .var A => ι A
  | .one => fun x y => x = y
  | .recip e => fun x y => eval ι e y x
  | .meet a b => fun x y => eval ι a x y ∧ eval ι b x y
  | .comp a b => fun x y => ∃ z, eval ι a x z ∧ eval ι b z y

/-- **"true for `Rel(S)`".**  The containment `E₁ ⊆ E₂` holds in every model. -/
def HoldsInRel (E₁ E₂ : Term L) : Prop :=
  ∀ {V : Type} (ι : L → V → V → Prop) (x y : V), eval ι E₁ x y → eval ι E₂ x y

theorem HoldsInRel.refl (E : Term L) : HoldsInRel E E := fun _ _ _ h => h

theorem HoldsInRel.trans {E₁ E₂ E₃ : Term L}
    (h₁ : HoldsInRel E₁ E₂) (h₂ : HoldsInRel E₂ E₃) : HoldsInRel E₁ E₃ :=
  fun ι x y h => h₂ ι x y (h₁ ι x y h)

/-! ### Monotone congruences of the operations

  `°`, `∩`, `;` are order-preserving in `Rel(S)`, so a valid containment stays
  valid under each of them.  These are the semantic content of the `recip`,
  `meet`, `comp` rules of `Derives`, isolated as reusable lemmas (they let a
  containment be transported inside a bigger term). -/

/-- Reciprocation is monotone: `E₁ ⊆ E₂ ⟹ E₁° ⊆ E₂°`. -/
theorem HoldsInRel.recip {E₁ E₂ : Term L} (h : HoldsInRel E₁ E₂) :
    HoldsInRel (.recip E₁) (.recip E₂) :=
  fun _ x y h1 => h _ y x h1

/-- Intersection is monotone in both arguments. -/
theorem HoldsInRel.meet {A A' B B' : Term L}
    (hA : HoldsInRel A A') (hB : HoldsInRel B B') :
    HoldsInRel (.meet A B) (.meet A' B') :=
  fun ι x y h => ⟨hA ι x y h.1, hB ι x y h.2⟩

/-- Composition is monotone in both arguments (diagram order). -/
theorem HoldsInRel.comp {A A' B B' : Term L}
    (hA : HoldsInRel A A') (hB : HoldsInRel B B') :
    HoldsInRel (.comp A B) (.comp A' B') := by
  intro V ι x y h
  obtain ⟨z, ha, hb⟩ := h
  exact ⟨z, hA ι x z ha, hB ι z y hb⟩

/-! ### Bridge to the core graph model

  A graph `H` is the model `(H.V, fun A a b => H.edge a b A)`, and under this
  interpretation `eval` is exactly the core's `toRel`; conversely every model
  arises from a graph.  Hence `HoldsInRel` coincides with the core's `Gle` on
  term-graphs, and (via `decision`) with the existence of a graph map — Freyd's
  "a containment holds in `Rel(S)` iff it holds in **G**". -/

/-- Under the graph interpretation `eval` reduces to the core's `toRel`. -/
theorem eval_graphInterp (H : LGraph L) (e : Term L) (x y : H.V) :
    eval (fun A a b => H.edge a b A) e x y ↔ toRel H e x y := by
  induction e generalizing x y with
  | var A => exact Iff.rfl
  | one => exact Iff.rfl
  | recip e ih => exact ih y x
  | meet a b iha ihb => exact and_congr (iha x y) (ihb x y)
  | comp a b iha ihb => exact exists_congr (fun z => and_congr (iha x z) (ihb z y))

/-- `HoldsInRel` is exactly the core's graph containment `Gle` on term-graphs. -/
theorem holdsInRel_iff_Gle (E₁ E₂ : Term L) :
    HoldsInRel E₁ E₂ ↔ Gle (toGraph E₁) (toGraph E₂) := by
  constructor
  · intro h H x y h1
    rw [← toRel_eq_Trel] at h1 ⊢
    exact (eval_graphInterp H E₂ x y).mp
      (h (fun A a b => H.edge a b A) x y ((eval_graphInterp H E₁ x y).mpr h1))
  · intro h V ι x y h1
    let H : LGraph L := ⟨V, fun a b A => ι A a b, x, x⟩
    have h1' : toRel H E₁ x y := (eval_graphInterp H E₁ x y).mp h1
    have h2' : Trel (toGraph E₁) H x y := (toRel_eq_Trel H E₁ x y).mp h1'
    have h3' : toRel H E₂ x y := (toRel_eq_Trel H E₂ x y).mpr (h H x y h2')
    exact (eval_graphInterp H E₂ x y).mpr h3'

/-- **Freyd's decision procedure, in the `HoldsInRel` phrasing.**  A containment
    is true in `Rel(S)` for every `S` iff there is a graph map between the two
    term-graphs.  (Reuses the core `decision`.) -/
theorem holdsInRel_iff_hom (E₁ E₂ : Term L) :
    HoldsInRel E₁ E₂ ↔ Nonempty (Hom (toGraph E₂) (toGraph E₁)) := by
  rw [holdsInRel_iff_Gle, Gle_iff_hom]

/-! ### Substitution

  An equational axiom is used at *instances*: to apply `A ⊆ B` we substitute a
  term for each variable.  `subst σ E` replaces each label `A` in `E` by `σ A`. -/

/-- Substitute a term `σ A` for each label `A` in a term. -/
def subst (σ : L → Term L) : Term L → Term L
  | .var A => σ A
  | .one => .one
  | .recip e => .recip (subst σ e)
  | .meet a b => .meet (subst σ a) (subst σ b)
  | .comp a b => .comp (subst σ a) (subst σ b)

/-- Evaluating a substituted term is evaluating the original under the
    reinterpreted labels `A ↦ eval ι (σ A)`. -/
theorem eval_subst {V : Type} (ι : L → V → V → Prop) (σ : L → Term L)
    (E : Term L) (x y : V) :
    eval ι (subst σ E) x y ↔ eval (fun A => eval ι (σ A)) E x y := by
  induction E generalizing x y with
  | var A => exact Iff.rfl
  | one => exact Iff.rfl
  | recip e ih => exact ih y x
  | meet a b iha ihb => exact and_congr (iha x y) (ihb x y)
  | comp a b iha ihb => exact exists_congr (fun z => and_congr (iha x z) (ihb z y))

/-- Validity is closed under substitution: an instance of a valid containment is
    valid.  This is the semantic content of the equational "axiom" rule. -/
theorem HoldsInRel.subst {E₁ E₂ : Term L} (h : HoldsInRel E₁ E₂) (σ : L → Term L) :
    HoldsInRel (subst σ E₁) (subst σ E₂) := by
  intro V ι x y h1
  rw [eval_subst] at h1 ⊢
  exact h (fun A => eval ι (σ A)) x y h1

/-! ## Layer 2 — the equational derivation system

  `Derives Ax E₁ E₂` : the containment `E₁ ⊆ E₂` is derivable from the axiom set
  `Ax` (a finite list of term-pairs) using the proof rules of the equational
  theory of allegories: substitution instances of the axioms, reflexivity,
  transitivity, and the monotone congruences of `°`, `∩`, `;`.  (`∩`, `;` and `°`
  are order-preserving in every allegory, so these congruences are sound.) -/

/-- Derivability of containments from an axiom set `Ax`. -/
inductive Derives (Ax : List (Term L × Term L)) : Term L → Term L → Prop
  | ax {E₁ E₂ : Term L} (σ : L → Term L) : (E₁, E₂) ∈ Ax →
      Derives Ax (subst σ E₁) (subst σ E₂)
  | refl (E : Term L) : Derives Ax E E
  | trans {E₁ E₂ E₃ : Term L} : Derives Ax E₁ E₂ → Derives Ax E₂ E₃ → Derives Ax E₁ E₃
  | recip {E₁ E₂ : Term L} : Derives Ax E₁ E₂ → Derives Ax (.recip E₁) (.recip E₂)
  | meet {E₁ E₁' E₂ E₂' : Term L} : Derives Ax E₁ E₁' → Derives Ax E₂ E₂' →
      Derives Ax (.meet E₁ E₂) (.meet E₁' E₂')
  | comp {E₁ E₁' E₂ E₂' : Term L} : Derives Ax E₁ E₁' → Derives Ax E₂ E₂' →
      Derives Ax (.comp E₁ E₂) (.comp E₁' E₂')

/-! ## Layer 3 — soundness

  Every containment derivable from a *valid* axiom set is true in `Rel(S)`. -/

/-- **Soundness of `Derives`.**  If every axiom of `Ax` is valid in `Rel(S)`,
    every containment derivable from `Ax` is valid in `Rel(S)`. -/
theorem Derives_sound {Ax : List (Term L × Term L)}
    (hAx : ∀ p ∈ Ax, HoldsInRel p.1 p.2) :
    ∀ {E₁ E₂ : Term L}, Derives Ax E₁ E₂ → HoldsInRel E₁ E₂ := by
  intro E₁ E₂ h
  induction h with
  | ax σ hmem => exact HoldsInRel.subst (hAx _ hmem) σ
  | refl E => exact HoldsInRel.refl E
  | trans _ _ ih1 ih2 => exact HoldsInRel.trans ih1 ih2
  | recip _ ih => intro V ι x y h1; exact ih ι y x h1
  | meet _ _ ih1 ih2 => intro V ι x y h1; exact ⟨ih1 ι x y h1.1, ih2 ι x y h1.2⟩
  | comp _ _ ih1 ih2 =>
      intro V ι x y h1; obtain ⟨z, ha, hb⟩ := h1; exact ⟨z, ih1 ι x z ha, ih2 ι z y hb⟩

/-! ### The derivation ⇒ graph-map bridge (Layer 4, ingredient (a) — endpoint form)

  Freyd's counting argument needs to turn a *derivation* into a *graph map*
  `[E₂] → [E₁]`.  The endpoint form is immediate from soundness composed with
  the decision bridge `holdsInRel_iff_hom`: any containment derivable from a
  valid axiom set is realised by an honest graph map on the term-graphs.  (The
  hard, still-open refinement is the *structural* version: unfolding the
  derivation into a CHAIN of graph maps `[E₂] → H₁ → ⋯ → [E₁]` with every
  intermediate `Hᵢ` in the series-parallel suballegory `Ḡ` and each single step
  the graphical interpretation of one axiom-instance — see the OPEN note.) -/

/-- **Derivation ⇒ collapse map.**  If `Ax` is valid and `E₁ ⊆ E₂` is derivable
    from `Ax`, then there is a graph map `[E₂] → [E₁]` — the collapse witnessing
    the containment.  (Soundness `Derives_sound` into the decision bridge.) -/
theorem Derives_hom {Ax : List (Term L × Term L)}
    (hAx : ∀ p ∈ Ax, HoldsInRel p.1 p.2) {E₁ E₂ : Term L}
    (h : Derives Ax E₁ E₂) : Nonempty (Hom (toGraph E₂) (toGraph E₁)) :=
  (holdsInRel_iff_hom E₁ E₂).mp (Derives_sound hAx h)

/-! ### The `B = 0` case of the counting obstruction (Layer 4, seed of (c))

  With NO axioms the derivation system is *pure* (reflexivity, transitivity, and
  the three congruences).  Such a derivation can identify **no** vertex-pair: its
  two sides are forced to be the SAME term.  This is exactly Freyd's "each step
  identifies at most `B(Ax)` pairs" at the extreme `B = 0`, and it already
  refutes completeness of the empty axiom set — the base instance of the
  no-finite-axiomatization phenomenon.  The general finite-`Ax` bound (ingredient
  (b), `B(Ax) > 0`) plus the "no proper partial collapse" heart (ingredient (c))
  are what remain open. -/

/-- **Purity of the axiom-free theory.**  `Derives []` proves a containment only
    between *syntactically equal* terms: it can collapse nothing.  (Induction on
    the derivation; the `ax` rule is unreachable since `_ ∈ []` is false.) -/
theorem Derives_nil_eq {E₁ E₂ : Term L} (h : Derives [] E₁ E₂) : E₁ = E₂ := by
  induction h with
  | ax σ hmem => nomatch hmem
  | refl E => rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | recip _ ih => exact congrArg Term.recip ih
  | meet _ _ ih1 ih2 => exact congr (congrArg Term.meet ih1) ih2
  | comp _ _ ih1 ih2 => exact congr (congrArg Term.comp ih1) ih2

/-! ## Layer 1 — the rhombus family and its validity

  Freyd's §2.158 first explicit example is the "single rhombus" containment
  obtained from the map that collapses the four-vertex square `G₁` onto `G₂` (`s`
  and `t` identified, the two top vertices identified, the two bottom vertices
  identified).  It is the SEPARATED containment

    `1 ∩ (R₁∩R₄°)(R₂∩R₃°)(S₂°∩S₃)(S₁°∩S₄) ⊆ (R₁R₂∩S₁S₂)(R₃R₄∩S₃S₄)`

  (each variable occurs once per side).  We prove it valid in `Rel(S)` directly
  from the semantics; the witnessing midpoint of the right side is the middle
  vertex `p₂` of the left side's four-step walk (with `x = y` supplying the two
  edges that cross the identified `s = t`).  This is the base member (`n = 1`) of
  Freyd's rhombus family. -/

/-- Left side of the single-rhombus containment (`G₂`, the collapsed square). -/
def rhombusLHS (r1 r2 r3 r4 s1 s2 s3 s4 : L) : Term L :=
  .meet .one
    (.comp (.comp (.meet (.var r1) (.recip (.var r4)))
                  (.meet (.var r2) (.recip (.var r3))))
           (.comp (.meet (.recip (.var s2)) (.var s3))
                  (.meet (.recip (.var s1)) (.var s4))))

/-- Right side of the single-rhombus containment (`G₁`, the four distinct
    vertices: two composed lenses `R₁R₂∩S₁S₂` and `R₃R₄∩S₃S₄`). -/
def rhombusRHS (r1 r2 r3 r4 s1 s2 s3 s4 : L) : Term L :=
  .comp (.meet (.comp (.var r1) (.var r2)) (.comp (.var s1) (.var s2)))
        (.meet (.comp (.var r3) (.var r4)) (.comp (.var s3) (.var s4)))

/-- **Layer 1 (base rhombus, `n = 1`).**  The single-rhombus separated
    containment is valid in `Rel(S)` for every `S`.  This is the first member of
    the family whose *infinite* extension defies finite axiomatization. -/
theorem rhombus1_holds (r1 r2 r3 r4 s1 s2 s3 s4 : L) :
    HoldsInRel (rhombusLHS r1 r2 r3 r4 s1 s2 s3 s4)
               (rhombusRHS r1 r2 r3 r4 s1 s2 s3 s4) := by
  intro V ι x y h
  obtain ⟨hxy, z, ⟨w, ⟨hr1, hr4⟩, hr2, hr3⟩, u, ⟨hs2, hs3⟩, hs1, hs4⟩ := h
  subst hxy
  exact ⟨z, ⟨⟨w, hr1, hr2⟩, ⟨u, hs1, hs2⟩⟩, ⟨w, hr3, hr4⟩, ⟨u, hs3, hs4⟩⟩

/-! ### An infinite family of valid separated containments (Layer 1, general `n`)

  We package `rhombus1_holds` into an explicit *infinite* family of valid
  separated containments over the concrete label set `ℕ`, obtained by putting
  `n+1` rhombi in series (`;`) with a fresh block of eight labels per rhombus
  (`8·b … 8·b+7`).  Each member is separated (every label occurs once on each
  side) and valid in `Rel(S)` for every `S`; validity for all `n` is proved by
  induction from the base rhombus and the composition congruence
  `HoldsInRel.comp`.  This realises Freyd's "there is no finite bound: the family
  of rhombus containments is infinite" at the level of *validity* (Layer 1).

  The genuine **hard** family of §2.158 — the single `n`-fold rhombus whose
  collapse map identifies `Θ(n)` vertex-pairs *simultaneously* and admits no
  proper partial collapse inside `Ḡ` — is a *connected, entangled* graph, not a
  series bouquet; only for it is `RhombusHard` true (the series family below is
  derivable rhombus-by-rhombus once one rhombus is, so it does NOT witness
  `RhombusHard`).  Reconstructing that entangled graph as an explicit `Term`
  requires the §2.158 figures (unavailable here); see the OPEN note at the end. -/

/-- The `i`-th of the eight labels in the `b`-th fresh block.  (Labels live in
    `Nat`; each rhombus gets a disjoint block, so the family is *separated*.) -/
def lbl (b i : Nat) : Nat := 8 * b + i

/-- The base rhombus LHS on the `b`-th fresh block of eight `Nat`-labels. -/
def rhL1 (b : Nat) : Term Nat :=
  rhombusLHS (lbl b 0) (lbl b 1) (lbl b 2) (lbl b 3)
             (lbl b 4) (lbl b 5) (lbl b 6) (lbl b 7)

/-- The base rhombus RHS on the `b`-th fresh block of eight `Nat`-labels. -/
def rhR1 (b : Nat) : Term Nat :=
  rhombusRHS (lbl b 0) (lbl b 1) (lbl b 2) (lbl b 3)
             (lbl b 4) (lbl b 5) (lbl b 6) (lbl b 7)

/-- Each single blocked rhombus is valid in `Rel(S)`. -/
theorem rhL1_holds (b : Nat) : HoldsInRel (rhL1 b) (rhR1 b) :=
  rhombus1_holds _ _ _ _ _ _ _ _

/-- LHS of the `n`-fold series rhombus: `n+1` collapsed rhombi composed in `;`. -/
def ladderL : Nat → Term Nat
  | 0 => rhL1 0
  | n+1 => .comp (ladderL n) (rhL1 (n+1))

/-- RHS of the `n`-fold series rhombus: `n+1` expanded rhombi composed in `;`. -/
def ladderR : Nat → Term Nat
  | 0 => rhR1 0
  | n+1 => .comp (ladderR n) (rhR1 (n+1))

/-- **Layer 1, all `n`.**  Every member of the infinite series-rhombus family is
    a valid separated containment in `Rel(S)`.  (Base = `rhombus1_holds`; step =
    `HoldsInRel.comp`.)  This supplies the `hvalid` hypothesis of
    `no_finite_axiomatization` for the family `ladderL, ladderR`. -/
theorem ladder_holds : ∀ n : Nat, HoldsInRel (ladderL n) (ladderR n) := by
  intro n
  induction n with
  | zero => exact rhL1_holds 0
  | succ m ih => exact HoldsInRel.comp ih (rhL1_holds (m+1))

/-! ## Layer 4 — the no-finite-axiomatization metatheorem (reduction)

  Freyd's argument: recast the allegory axioms as *separated* containments; then
  the infinite rhombus family is valid in `Rel(S)` but, by a counting argument on
  the graph maps that any derivation must factor through, no fixed finite axiom
  set entails all of it.  We isolate that counting argument as the explicit
  hypothesis `RhombusHard` and reduce the metatheorem to it — a faithful
  reduction, hole-free and axiom-clean.  See the module report for the exact
  remaining content of `RhombusHard` and why it is hard. -/

/-- An axiom set is **complete** for `Rel(S)` when every valid containment is
    derivable from it. -/
def Complete (Ax : List (Term L × Term L)) : Prop :=
  ∀ E₁ E₂ : Term L, HoldsInRel E₁ E₂ → Derives Ax E₁ E₂

/-- **The empty axiom set is not complete** — the fully-provable base instance of
    the metatheorem.  `E ∩ E ⊆ E` is valid in `Rel(S)` yet its two sides are
    distinct terms, so by `Derives_nil_eq` it is not derivable from no axioms.
    (This is `no_finite_axiomatization` for the finite valid set `∅`, proved
    unconditionally — the general finite set is the open `RhombusHard`.) -/
theorem not_complete_nil : ¬ Complete ([] : List (Term L × Term L)) := by
  intro hC
  have hvalid : HoldsInRel (Term.meet Term.one Term.one) (Term.one : Term L) := by
    intro V ι x y h; exact h.1
  have heq : (Term.meet Term.one Term.one : Term L) = Term.one :=
    Derives_nil_eq (hC _ _ hvalid)
  nomatch heq

/-- **Freyd's counting obstruction.**  For any finite axiom set of *valid*
    containments, some member of the rhombus family is NOT derivable from it.
    (The graph map collapsing the `n`-rhombus identifies unboundedly many vertex
    pairs, while each single defining/added containment, as a graph map, changes
    the vertex count by a fixed bounded amount — so for large `n` no derivation
    chain, all of whose intermediate graphs must lie in `Ḡ`, can reach it.) -/
def RhombusHard (rhL rhR : ℕ → Term L) : Prop :=
  ∀ Ax : List (Term L × Term L), (∀ p ∈ Ax, HoldsInRel p.1 p.2) →
    ∃ n, ¬ Derives Ax (rhL n) (rhR n)

/-- **§2.158 Target 3 — no finite axiomatization (reduction to the counting
    obstruction).**  Given a family `rhL n ⊆ rhR n` that is (i) valid in `Rel(S)`
    and (ii) satisfies Freyd's counting obstruction, NO finite set of equations
    true for `Rel(S)` accounts for all equations true for `Rel(S)`: no finite
    *valid* axiom set is complete.  (`rhombus1_holds` is the base case of (i);
    the full family and (ii) are the remaining Layer-1/Layer-4 content.) -/
theorem no_finite_axiomatization {rhL rhR : ℕ → Term L}
    (hvalid : ∀ n, HoldsInRel (rhL n) (rhR n))
    (hhard : RhombusHard rhL rhR) :
    ¬ ∃ Ax : List (Term L × Term L),
        (∀ p ∈ Ax, HoldsInRel p.1 p.2) ∧ Complete Ax := by
  rintro ⟨Ax, hAxValid, hComplete⟩
  obtain ⟨n, hn⟩ := hhard Ax hAxValid
  exact hn (hComplete (rhL n) (rhR n) (hvalid n))

/-! ## OPEN — the remaining content of `RhombusHard` (Freyd's counting heart)

  What is CLOSED here (all sorry-free):

  * **Layer 1 validity, all `n`** — `ladder_holds : ∀ n, HoldsInRel (ladderL n)
    (ladderR n)`, an explicit infinite family of valid separated containments.
  * **Ingredient (a), endpoint form** — `Derives_hom`: a derivation from a valid
    `Ax` yields a graph map `[E₂] → [E₁]`.
  * **Ingredient (c) at `B = 0`** — `Derives_nil_eq` + `not_complete_nil`: with
    no axioms nothing collapses, so `∅` is already incomplete.
  * The **reduction** `no_finite_axiomatization` (conditional on `RhombusHard`).

  What remains OPEN in `RhombusHard rhL rhR := ∀ Ax valid, ∃ n, ¬ Derives Ax
  (rhL n) (rhR n)`, for Freyd's genuine *entangled* family (NOT the series family
  `ladderL/ladderR` above, whose members are derivable rhombus-by-rhombus, so it
  does not witness `RhombusHard`):

  (a) **Structural chain refinement.**  Unfold `Derives Ax E₁ E₂` (through
      `trans`/congruences) into a CHAIN of graph maps `[E₂] → H₁ → ⋯ → [E₁]`
      with each `Hᵢ ∈ Ḡ` (series-parallel) and each single link the graphical
      interpretation of ONE axiom-instance.  (The endpoint map is `Derives_hom`;
      the per-step decomposition needs `Ḡ`/series-parallel structure that the
      core `S2_158_GraphAllegory` does not yet expose as a subtype.)

  (b) **Collapse invariant / bounded step.**  A `ℕ`-valued rank on graphs (Freyd:
      the number of vertices) that each single axiom-instance link changes by at
      most `B(Ax)`, a bound read off the finite `Ax`.  Constructively this is a
      cardinality on the `Quot`-built vertex types of `toGraph`, which the
      mathlib-free core lacks the finiteness infrastructure to count.

  (c) **The hard heart (no proper partial collapse).**  The `n`-rhombus needs
      `Θ(n)` identifications, but the series-parallel structure of `Ḡ` forbids
      any PROPER partial collapse: identifying a proper nonempty subset of its
      required vertex-pairs already leaves `Ḡ`.  Hence no chain of `⌊·/B(Ax)⌋`
      bounded links can reach it once `n > B(Ax)` — contradiction.  This is the
      genuinely combinatorial core of §2.158; it requires the explicit entangled
      `n`-rhombus graph of Freyd's figures (unavailable to this formalization) and
      a proof that its collapse lattice has no intermediate series-parallel
      element. -/

end Freyd.S2_158
