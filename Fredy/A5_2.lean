/-
  Bird & de Moor, *Algebra of Programming* §5.2  Relational products (book pp. 113-116).

  The relational product `a Π b` of two objects is a chosen tabulation of the maximal
  arrow `⊤ : a → b` (book p.114: "(outl, outr) tabulates Π").  Pairing `⟨R,S⟩`, the
  binary map-former `R×S`, and their laws (5.1)-(5.9) are built from this single choice.

  Diagram order throughout: `xy` means "first x then y" (`≫`), matching the book's own
  right-to-left composition after mirroring (`X·Y` there = `Y ≫ X` here).  Every
  statement below is already in the mirrored form; do not re-translate.

  Setting: a TABULAR UNITARY DIVISION ALLEGORY (`Fredy.S2_3`), which supplies `topMor`
  (the maximal arrow `⊤ : a → b`, via the unit projections) and full tabulation
  (`TabularAllegory.tabular`).

  Investigated `Fredy.S2_147_MapCat`'s `mapHasBinaryProducts` (binary products of
  `Map(𝒜)`, built as a pullback over the terminal/unit object): conceptually this is
  the SAME universal apex as tabulating `topMor a b` (pulling back the two unit maps
  `p_a, p_b` IS tabulating `p_a ≫ p_b° = topMor a b`), confirming `RelProd` needs no new
  axioms.  Not reused literally: that construction is expressed through the heavy
  `HasPullback`/`Cone`/`MapObj`/`@`-explicit categorical machinery (built for the
  `Map(𝒜)` CATEGORY, with objects packaged as `{f // Map f}` subtypes), whereas `RelProd`
  needs the raw `𝒜`-level legs directly.  Unwinding `Cone.π₁.val` etc. would be strictly
  more code than mirroring `S2_3.topTab`'s direct `TabularAllegory.tabular (topMor a b)`
  pattern, which is what `relProd` below does.
-/
import Fredy.S2_3
import Fredy.A4_2
import Fredy.A5_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [TabularUnitaryDivisionAllegory 𝒜]

/-! ## `topMor` is self-converse under swap (needed for (5.6)/(5.7)) -/

/-- `(⊤ : a → b)° = ⊤ : b → a`.  Immediate from `topMor`'s definition as `p_a ≫ p_b°`. -/
theorem recip_topMor (a b : 𝒜) : (topMor a b)° = topMor b a := by
  unfold topMor
  rw [Allegory.recip_comp, Allegory.recip_recip]

/-! ## §5.2  The relational product `RelProd a b` (book p.114)

  A RelProd is a CHOSEN tabulation of `⊤ : a → b`: an apex `p` with legs
  `outl : p ⟶ a`, `outr : p ⟶ b` that are MAPS, tabulating the maximal arrow. -/

/-- A **RELATIONAL PRODUCT** of `a`, `b` (B&dM §5.2, book p.114): a chosen tabulation
    of the maximal arrow `⊤ : a → b` by maps `outl : p → a`, `outr : p → b`. -/
structure RelProd (a b : 𝒜) where
  /-- The apex (the product object, `a Π b`). -/
  p : 𝒜
  /-- Left projection. -/
  outl : p ⟶ a
  /-- Right projection. -/
  outr : p ⟶ b
  /-- `(outl, outr)` tabulates the maximal arrow `⊤ : a → b`. -/
  tab : Tabulates outl outr (topMor a b)

variable {a b a' b' c : 𝒜}

theorem RelProd.outl_map (P : RelProd a b) : Map P.outl := P.tab.1

theorem RelProd.outr_map (P : RelProd a b) : Map P.outr := P.tab.2.1

/-- `outl° ≫ outr = ⊤` (the tabulation equation). -/
theorem RelProd.eq_topMor (P : RelProd a b) : P.outl° ≫ P.outr = topMor a b := P.tab.2.2.1.symm

/-- The joint-monic identity `outl≫outl° ∩ outr≫outr° = id_p`. -/
theorem RelProd.joint_id (P : RelProd a b) :
    P.outl ≫ P.outl° ∩ P.outr ≫ P.outr° = Cat.id P.p := P.tab.2.2.2

/-- `outr° ≫ outl = ⊤ : b → a` — the "other" cross term, obtained from `eq_topMor` by
    reciprocation plus `recip_topMor`. -/
theorem RelProd.outr_recip_outl (P : RelProd a b) : P.outr° ≫ P.outl = topMor b a := by
  have h := congrArg Allegory.recip P.eq_topMor
  rwa [Allegory.recip_comp, Allegory.recip_recip, recip_topMor] at h

/-- The canonical relational product, obtained by tabulating `⊤ : a → b` (mirrors
    `S2_3.topTab`'s choice pattern). -/
noncomputable def relProd (a b : 𝒜) : RelProd a b :=
  let t := TabularAllegory.tabular (topMor a b)
  { p := t.choose
    outl := t.choose_spec.choose
    outr := t.choose_spec.choose_spec.choose
    tab := t.choose_spec.choose_spec.choose_spec }

/-! ## Two generic `topMor`-cancellation facts, used repeatedly below -/

/-- `id_c ∩ (S ≫ ⊤) ⊑ dom S`, for `S : c ⟶ b`.
    (B&dM Ex 4.27-style fact, mirrored; the generic half of (5.6)/(5.7)'s proof.) -/
theorem id_inter_comp_topMor_le_dom {b c : 𝒜} (S : c ⟶ b) :
    Cat.id c ∩ (S ≫ topMor b c) ⊑ dom S := by
  show Cat.id c ∩ (S ≫ topMor b c) ⊑ Cat.id c ∩ (S ≫ S°)
  apply le_inter (inter_lb_left _ _)
  have hSle : S° ⊑ topMor b c := topMor_max S°
  have hcomm : topMor b c ∩ S° = S° := by rw [Allegory.inter_comm]; exact hSle
  have hmod : (S ≫ topMor b c) ∩ Cat.id c ⊑ S ≫ (topMor b c ∩ S° ≫ Cat.id c) :=
    modular_le_right S (topMor b c) (Cat.id c)
  rw [Cat.comp_id, hcomm] at hmod
  calc Cat.id c ∩ (S ≫ topMor b c) = (S ≫ topMor b c) ∩ Cat.id c := Allegory.inter_comm _ _
    _ ⊑ S ≫ S° := hmod

/-- **Key fact**: `R ∩ (S ≫ ⊤) = dom S ≫ R`, for `R : c ⟶ a`, `S : c ⟶ b`.  The generic
    engine behind (5.6)/(5.7): B&dM Exercise 4.27 mirrored. -/
theorem inter_comp_topMor_eq_dom_comp {a b c : 𝒜} (R : c ⟶ a) (S : c ⟶ b) :
    R ∩ (S ≫ topMor b a) = dom S ≫ R := by
  apply le_antisymm
  · have h1 : (Cat.id c ≫ R) ∩ (S ≫ topMor b a) ⊑
        (Cat.id c ∩ (S ≫ topMor b a) ≫ R°) ≫ R := modular_le (Cat.id c) R (S ≫ topMor b a)
    rw [Cat.id_comp] at h1
    have h2 : (S ≫ topMor b a) ≫ R° ⊑ S ≫ topMor b c :=
      by rw [Cat.assoc]; exact comp_mono_left S (topMor_max (topMor b a ≫ R°))
    have h3 : Cat.id c ∩ ((S ≫ topMor b a) ≫ R°) ⊑ Cat.id c ∩ (S ≫ topMor b c) :=
      le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) h2)
    exact le_trans h1 (comp_mono_right (le_trans h3 (id_inter_comp_topMor_le_dom S)) R)
  · apply le_inter
    · have h := comp_mono_right (dom_coreflexive S) R; rwa [Cat.id_comp] at h
    · have h1 : dom S ≫ R ⊑ (S ≫ S°) ≫ R :=
        comp_mono_right (inter_lb_right (Cat.id c) (S ≫ S°)) R
      have h2 : (S ≫ S°) ≫ R = S ≫ (S° ≫ R) := Cat.assoc S S° R
      have h3 : S ≫ (S° ≫ R) ⊑ S ≫ topMor b a := comp_mono_left S (topMor_max (S° ≫ R))
      rw [h2] at h1; exact le_trans h1 h3

/-! ## (5.1)  Pairing -/

/-- **(5.1)**: `⟨R,S⟩ = (outl°R) ∩ (outr°S)`, mirrored: `pair R S = (R≫outl°) ∩ (S≫outr°)`. -/
def RelProd.pair (P : RelProd a b) (R : c ⟶ a) (S : c ⟶ b) : c ⟶ P.p :=
  (R ≫ P.outl°) ∩ (S ≫ P.outr°)

/-! ## (5.2)  The binary map-former `R×S` -/

/-- **(5.2)**: `R×S = ⟨R·outl, S·outr⟩`, mirrored: `prodMap P Q R S = Q.pair (P.outl≫R) (P.outr≫S)`. -/
def prodMap (P : RelProd a b) (Q : RelProd a' b') (R : a ⟶ a') (S : b ⟶ b') : P.p ⟶ Q.p :=
  Q.pair (P.outl ≫ R) (P.outr ≫ S)

/-! ## Monotonicity -/

theorem RelProd.pair_mono {P : RelProd a b} {R R' : c ⟶ a} {S S' : c ⟶ b}
    (hR : R ⊑ R') (hS : S ⊑ S') : P.pair R S ⊑ P.pair R' S' :=
  le_inter (le_trans (inter_lb_left _ _) (comp_mono_right hR _))
    (le_trans (inter_lb_right _ _) (comp_mono_right hS _))

theorem prodMap_mono {P : RelProd a b} {Q : RelProd a' b'} {R R' : a ⟶ a'} {S S' : b ⟶ b'}
    (hR : R ⊑ R') (hS : S ⊑ S') : prodMap P Q R S ⊑ prodMap P Q R' S' :=
  Q.pair_mono (comp_mono_left P.outl hR) (comp_mono_left P.outr hS)

/-! ## (5.6)/(5.7)  Cancellation of pairing against `outl`/`outr` -/

/-- **(5.6)**: `⟨R,S⟩·outl = dom S · R`, mirrored: `pair R S ≫ outl = dom S ≫ R`. -/
theorem RelProd.pair_outl {P : RelProd a b} (R : c ⟶ a) (S : c ⟶ b) :
    P.pair R S ≫ P.outl = dom S ≫ R := by
  have step1 : P.pair R S = S ≫ P.outr° ∩ R ≫ P.outl° := by
    show (R ≫ P.outl° ∩ S ≫ P.outr°) = _; rw [Allegory.inter_comm]
  rw [step1, simple_modular_eq P.outl_map.2 (S ≫ P.outr°) R, Cat.assoc, P.outr_recip_outl,
    Allegory.inter_comm]
  exact inter_comp_topMor_eq_dom_comp R S

/-- **(5.7)**: `⟨R,S⟩·outr = dom R · S`, mirrored: `pair R S ≫ outr = dom R ≫ S`. -/
theorem RelProd.pair_outr {P : RelProd a b} (R : c ⟶ a) (S : c ⟶ b) :
    P.pair R S ≫ P.outr = dom R ≫ S := by
  show (R ≫ P.outl° ∩ S ≫ P.outr°) ≫ P.outr = dom R ≫ S
  rw [simple_modular_eq P.outr_map.2 (R ≫ P.outl°) S, Cat.assoc, P.eq_topMor, Allegory.inter_comm]
  exact inter_comp_topMor_eq_dom_comp S R

/-! ## The pairing Galois connection

  `Z ⊑ pair U V ↔ Z≫outl ⊑ U ∧ Z≫outr ⊑ V`: `pair U V` is the GREATEST morphism whose
  two projections are bounded by `U`, `V`.  The clean characterization behind most of
  the calculations below. -/

theorem RelProd.le_pair_iff {P : RelProd a b} {Z : c ⟶ P.p} {U : c ⟶ a} {V : c ⟶ b} :
    Z ⊑ P.pair U V ↔ Z ≫ P.outl ⊑ U ∧ Z ≫ P.outr ⊑ V := by
  constructor
  · intro h
    exact ⟨(map_shunt_right P.outl_map Z U).mpr (le_trans h (inter_lb_left _ _)),
      (map_shunt_right P.outr_map Z V).mpr (le_trans h (inter_lb_right _ _))⟩
  · rintro ⟨h1, h2⟩
    exact le_inter ((map_shunt_right P.outl_map Z U).mp h1) ((map_shunt_right P.outr_map Z V).mp h2)

/-- Any `Z : c ⟶ p` refines the pair of its own projections. -/
theorem RelProd.le_pair_proj {P : RelProd a b} (Z : c ⟶ P.p) :
    Z ⊑ P.pair (Z ≫ P.outl) (Z ≫ P.outr) :=
  RelProd.le_pair_iff.mpr ⟨le_refl _, le_refl _⟩

/-! ## `pair` of two maps is a map, and Ex 5.9

  The absorption law (5.3)/(5.4)/(5.5)/(5.8) genuinely need B&dM p.115's own chain
  ("meet-composed-with-meet" — semi-distributivity and the modular law only ever bound
  such a composite from ABOVE, never below, unless one full side is `Simple`); the book's
  own route hits the same wall from several angles (tracked in the final report, DROPPED
  here per the task's drop-and-report rule).  What DOES go through cleanly — because only
  one factor, not two, is a meet — is: pairing two MAPS is a map (via the tabulation UP),
  and pairing commutes with LEFT composition by a map (Ex 5.9, via `simple_dist_inter`). -/

/-- `pair f g` of two MAPS `f, g` is again a MAP: it is literally the mediating witness
    of the tabulation universal property (`tabulation_UP_forward_witness`) applied to
    `f°≫g ⊑ ⊤` (always true, `topMor_max`). -/
theorem RelProd.pair_map {P : RelProd a b} {f : c ⟶ a} {g : c ⟶ b}
    (hf : Map f) (hg : Map g) : Map (P.pair f g) :=
  (tabulation_UP_forward_witness P.tab hf hg (topMor_max (f° ≫ g))).1

/-- **Ex 5.9**: for a MAP `f : d ⟶ c`, `f ≫ ⟨R,S⟩ = ⟨f≫R, f≫S⟩`, mirrored:
    `f ≫ P.pair R S = P.pair (f≫R) (f≫S)`.  `f` being simple lets composition
    distribute exactly over the defining meet (`simple_dist_inter`). -/
theorem RelProd.map_comp_pair {P : RelProd a b} {d : 𝒜} {f : d ⟶ c} (hf : Map f)
    (R : c ⟶ a) (S : c ⟶ b) : f ≫ P.pair R S = P.pair (f ≫ R) (f ≫ S) := by
  show f ≫ (R ≫ P.outl° ∩ S ≫ P.outr°) = (f ≫ R) ≫ P.outl° ∩ (f ≫ S) ≫ P.outr°
  rw [simple_dist_inter hf.2, Cat.assoc, Cat.assoc]

/-! ## Ex 5.6:  functoriality shape of `prodMap` — identity and converse -/

/-- `prodMap` of the two identities is the identity, via the joint-monic identity. -/
theorem prodMap_id (P : RelProd a b) :
    prodMap P P (Cat.id a) (Cat.id b) = Cat.id P.p := by
  show P.pair (P.outl ≫ Cat.id a) (P.outr ≫ Cat.id b) = Cat.id P.p
  rw [Cat.comp_id, Cat.comp_id]
  show P.outl ≫ P.outl° ∩ P.outr ≫ P.outr° = Cat.id P.p
  exact P.joint_id

/-- `(R×S)° = S°×R°` reading the OTHER way round, mirrored: `(prodMap P Q R S)° =
    prodMap Q P R° S°` — a direct computation from the definitions via `recip_inter`/
    `recip_comp`, no absorption needed. -/
theorem prodMap_recip {P : RelProd a b} {Q : RelProd a' b'} (R : a ⟶ a') (S : b ⟶ b') :
    (prodMap P Q R S)° = prodMap Q P R° S° := by
  show ((P.outl ≫ R) ≫ Q.outl° ∩ (P.outr ≫ S) ≫ Q.outr°)° =
      (Q.outl ≫ R°) ≫ P.outl° ∩ (Q.outr ≫ S°) ≫ P.outr°
  rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp,
    Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, Allegory.recip_recip,
    Cat.assoc, Cat.assoc]

end Freyd.Alg
