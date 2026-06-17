/-
  Freyd & Scedrov, *Categories and Allegories* — §2.165–§2.169: tabular and
  effective universal properties of the split-idempotent completion `Spl 𝒜`.

  This continues `Fredy/S2_21.lean` (§2.164, the construction of `Spl 𝒜`).  Here we
  prove the *structural* results of §2.165–§2.169 about `Spl 𝒜`:

  §2.163  A coreflexive splits iff it is tabular; an equivalence relation splits iff
          it is effective.  In `Spl 𝒜` *every* symmetric idempotent splits, so in
          particular every coreflexive and every equivalence relation split.
  §2.165  If `𝒜` is pre-tabular then `Spl 𝒜` remains pre-tabular.
  §2.166  An allegory is tabular iff it is pre-tabular and all coreflexives split.
          The constructive core is `tabulation_of_pre_tabular`: from a containment
          `R ⊑ f°g` with `ff° ∩ gg° = 1` and a splitting of the coreflexive
          `A = 1 ∩ fRg°` one builds a tabulation `(hf, hg)` of `R`.
  §2.167  `Spl 𝒜` is tabular when `𝒜` is pre-tabular (pre-tabular + coreflexives
          split ⟹ tabular).  This is the tabular reflection.
  §2.169  An EFFECTIVE allegory is one in which all equivalence relations split.
          `Spl 𝒜` is effective.

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, intersection
  `R ∩ S`, order `R ⊑ S`.  Mathlib-free.
-/

import Fredy.S2_2
import Fredy.S2_21

universe v u

namespace Freyd.Alg

open Cat

variable {𝒜 : Type u} [Allegory 𝒜]

/-! ## §2.163  Splitting a symmetric idempotent *as a map*

  The book's notion of "split" for an EQUIVALENCE relation `E` (§2.163, §2.169) is:
  there is a map `f` with `f f° = E` and `f° f = 1`.  This is the "effective" form of
  splitting (legs are maps, not just morphisms).  We package it. -/

/-- `f : a ⟶ c` splits the endomorphism `E : a ⟶ a` *as a map* (§2.163): `f` is a map,
    `f ≫ f° = E`, and `f° ≫ f = 1_c`.  For a coreflexive this is §2.145 tabularity; for
    an equivalence relation this is §2.169 effectiveness. -/
def SplitsAsMap {a c : 𝒜} (f : a ⟶ c) (E : a ⟶ a) : Prop :=
  Map f ∧ f ≫ f° = E ∧ f° ≫ f = Cat.id c

/-- A symmetric idempotent `E` of `𝒜` that splits as a map is symmetric and idempotent —
    so the notion is only ever applied to symmetric idempotents. -/
theorem SplitsAsMap.symm {a c : 𝒜} {f : a ⟶ c} {E : a ⟶ a} (h : SplitsAsMap f E) :
    E° = E := by
  obtain ⟨_, hff, _⟩ := h
  rw [← hff, Allegory.recip_comp, Allegory.recip_recip]

/-! ## §2.163 / §2.169  Every symmetric idempotent splits *as a map* in `Spl 𝒜`

  An endomorphism of `Spl 𝒜` is a `SplHom E E` for an object `E = (a, e)`; its
  underlying morphism `R : a ⟶ a` satisfies `e ≫ R ≫ e = R`.  If moreover `R` is a
  symmetric idempotent of `Spl 𝒜` — i.e. `R° = R` and `R ≫ R = R` *as split-homs*,
  equivalently as morphisms of `𝒜` (recip and composition are inherited) — then `R`
  is itself a symmetric idempotent of `𝒜`, and the new object `(a, R)` together with
  the leg `R : E ⟶ (a,R)` exhibits a *map* splitting of `R` in `Spl 𝒜`.

  This is the central effectiveness fact: relevant idempotents (coreflexives §2.163,
  equivalence relations §2.169) all split this way. -/

/-- Given a symmetric idempotent `Φ : E ⟶ E` of `Spl 𝒜` (so `Φ.R° = Φ.R`,
    `Φ.R ≫ Φ.R = Φ.R`), its underlying morphism is a symmetric idempotent of `𝒜`. -/
def SplHom.toSymIdem {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) : SymIdem E.carrier :=
  ⟨Φ.R, hsym, hidem⟩

/-- The splitting object `(a, Φ)` for a symmetric idempotent `Φ : E ⟶ E` of `Spl 𝒜`. -/
def SplHom.splitObj {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) : SplObj 𝒜 :=
  ⟨E.carrier, Φ.toSymIdem hsym hidem⟩

/-- The splitting leg `E ⟶ (a, Φ)` of a symmetric idempotent `Φ : E ⟶ E`: underlying
    morphism `Φ.R`.  Fixed condition `e ≫ Φ.R ≫ Φ.R = Φ.R`. -/
def SplHom.splitLeg {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    SplHom E (Φ.splitObj hsym hidem) :=
  ⟨Φ.R, by
    show E.idem.e ≫ Φ.R ≫ Φ.R = Φ.R
    rw [hidem]; exact Φ.fixed_left⟩

/-- The reverse leg `(a, Φ) ⟶ E`: also underlying `Φ.R`. -/
def SplHom.splitLeg' {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    SplHom (Φ.splitObj hsym hidem) E :=
  ⟨Φ.R, by
    show Φ.R ≫ Φ.R ≫ E.idem.e = Φ.R
    rw [← Cat.assoc, hidem]; exact Φ.fixed_right⟩

/-- **§2.164 / §2.169**: every symmetric idempotent `Φ` of `Spl 𝒜` SPLITS — the leg
    `splitLeg` is a map (entire + simple) of `Spl 𝒜` with `leg ≫ leg° = Φ` and
    `leg° ≫ leg = 1_{(a,Φ)}`.  Compare `EffectiveAllegory.split_symmetric_idempotent`:
    here the split leg is `Φ.R` regarded as a map `E ⟶ (a, Φ)`. -/
theorem SplHom.split_symmetric_idempotent {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    let leg := Φ.splitLeg hsym hidem
    splComp leg (splRecip leg) = Φ ∧
    splComp (splRecip leg) leg = splId (Φ.splitObj hsym hidem) := by
  refine ⟨?_, ?_⟩
  · -- leg ≫ leg° = Φ.   underlying: Φ.R ≫ Φ.R° = Φ.R ≫ Φ.R = Φ.R.
    apply SplHom.ext
    show Φ.R ≫ Φ.R° = Φ.R
    rw [hsym, hidem]
  · -- leg° ≫ leg = 1_{(a,Φ)}.   underlying: Φ.R° ≫ Φ.R = Φ.R = id of (a,Φ).
    apply SplHom.ext
    show Φ.R° ≫ Φ.R = Φ.R
    rw [hsym, hidem]

/-! ## Composition of maps is a map (§2.13)

  Inlined from §2.13 (the repo's `S2_4.map_comp`) so this file depends only on `S2_21`
  rather than the whole §2.4 power-allegory tower. -/

/-- Composition of maps is a map (§2.13): simple `(fg)°(fg) = g°(f°f)g ⊑ g°g ⊑ 1`;
    entire `1 ⊑ ff° = f1f° ⊑ f(gg°)f° = (fg)(fg)°`. -/
theorem map_comp {a b c : 𝒜} {f : a ⟶ b} {g : b ⟶ c} (hf : Map f) (hg : Map g) :
    Map (f ≫ g) := by
  refine ⟨?_, ?_⟩
  · have hfe : Cat.id a ⊑ f ≫ f° := by
      have := hf.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
    have hge : Cat.id b ⊑ g ≫ g° := by
      have := hg.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
    have hstep : f ≫ f° ⊑ f ≫ (g ≫ g°) ≫ f° := by
      calc f ≫ f° = f ≫ Cat.id b ≫ f° := by rw [Cat.id_comp]
        _ ⊑ f ≫ (g ≫ g°) ≫ f° := comp_mono_left f (comp_mono_right hge f°)
    have heq : f ≫ (g ≫ g°) ≫ f° = (f ≫ g) ≫ (f ≫ g)° := by
      rw [Allegory.recip_comp]; simp [Cat.assoc]
    have hfin : Cat.id a ⊑ (f ≫ g) ≫ (f ≫ g)° := heq ▸ le_trans hfe hstep
    dsimp [Entire, dom]; exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hfin)
  · have hrw : (f ≫ g)° ≫ (f ≫ g) = g° ≫ (f° ≫ f) ≫ g := by
      rw [Allegory.recip_comp]; simp [Cat.assoc]
    have h1 : g° ≫ (f° ≫ f) ≫ g ⊑ g° ≫ g := by
      calc g° ≫ (f° ≫ f) ≫ g ⊑ g° ≫ Cat.id b ≫ g := comp_mono_left g° (comp_mono_right hf.2 g)
        _ = g° ≫ g := by rw [Cat.id_comp]
    dsimp [Simple]; rw [hrw]; exact le_trans h1 hg.2

/-! ## §2.166  Tabulation by splitting the apex coreflexive

  An allegory is TABULAR iff it is pre-tabular and all coreflexive morphisms split
  (§2.166).  The forward direction is immediate; the converse is the construction
  below.  Given a tabulation `(f, g)` of `U = f ≫ g°` and a containment `R ⊑ U`, the
  coreflexive `A := 1_c ∩ f° ≫ R ≫ g` on the apex `c` carries the "image of `R` on the
  apex".  Splitting `A` by a map `h : c ⟶ d` (`h ≫ h° = A`, `h° ≫ h = 1_d`) yields
  refined legs `(f ≫ h, g ≫ h)`, and

      `(f ≫ h) ≫ (g ≫ h)° = f ≫ (h ≫ h°) ≫ g° = f ≫ A ≫ g°`.

  So `(f ≫ h, g ≫ h)` tabulates `R` IFF `R = f ≫ A ≫ g°` — the APEX-SATURATION of `R`.
  This is genuinely necessary, *not* automatic: it fails for a non-difunctional
  `R ⊑ U` (Rel counterexample: apex `c = {∗}`, `a = b = {1,2}`, `f, g` the total maps;
  then `U = ⊤`, and for `R = {(1,1)}` one gets `A = 1_c`, `f ≫ A ≫ g° = ⊤ ≠ R`).  This
  is exactly the systemic / §2.226 gap documented in `S2_22.tab_transport_gap`.  So we
  record the honest content: for an apex-saturated `R`, splitting the apex coreflexive
  tabulates `R`.  (`R = U` and every difunctional `R ⊑ U` are saturated.)

  Conventions: repo `Tabulates f g R := Map f ∧ Map g ∧ R = f ≫ g° ∧ f°f ∩ g°g = 1`. -/

/-- The **apex coreflexive** `A = 1_c ∩ f° ≫ R ≫ g` of `R` relative to the tabulation
    `(f,g)` of `U = f ≫ g°` (§2.166): the image of `R` pushed onto the apex `c`. -/
def tabApex {a b c : 𝒜} (f : a ⟶ c) (g : b ⟶ c) (R : a ⟶ b) : c ⟶ c :=
  Cat.id c ∩ f° ≫ R ≫ g

/-- `tabApex` is coreflexive on the apex `c`. -/
theorem tabApex_coreflexive {a b c : 𝒜} (f : a ⟶ c) (g : b ⟶ c) (R : a ⟶ b) :
    Coreflexive (tabApex f g R) :=
  inter_lb_left _ _

/-- The apex coreflexive sits below each of `f° ≫ f` and `g° ≫ g`.  From `R ⊑ f g°`:
    `f° R g ⊑ f°(f g°)g = (f°f)(g°g)`; then `g°g ⊑ 1` (g simple) gives `⊑ f°f`, and
    `f°f ⊑ 1` (f simple) gives `⊑ g°g`. -/
theorem tabApex_le_legs {a b c : 𝒜} {f : a ⟶ c} {g : b ⟶ c} {R : a ⟶ b}
    (hf : Map f) (hg : Map g) (hRS : R ⊑ f ≫ g°) :
    tabApex f g R ⊑ f° ≫ f ∧ tabApex f g R ⊑ g° ≫ g := by
  have hfRg : f° ≫ R ≫ g ⊑ (f° ≫ f) ≫ (g° ≫ g) := by
    calc f° ≫ R ≫ g ⊑ f° ≫ (f ≫ g°) ≫ g := comp_mono_left f° (comp_mono_right hRS g)
      _ = (f° ≫ f) ≫ (g° ≫ g) := by simp [Cat.assoc]
  refine ⟨?_, ?_⟩
  · refine le_trans (inter_lb_right _ _) (le_trans hfRg ?_)
    calc (f° ≫ f) ≫ (g° ≫ g) ⊑ (f° ≫ f) ≫ Cat.id c := comp_mono_left _ hg.2
      _ = f° ≫ f := by rw [Cat.comp_id]
  · refine le_trans (inter_lb_right _ _) (le_trans hfRg ?_)
    calc (f° ≫ f) ≫ (g° ≫ g) ⊑ Cat.id c ≫ (g° ≫ g) := comp_mono_right hf.2 _
      _ = g° ≫ g := by rw [Cat.id_comp]

/-- If a map `h : c ⟶ d` splits a coreflexive `A` (`h ≫ h° = A`, `h° ≫ h = 1_d`) and
    `A ⊑ M`, then `1_d ⊑ h° ≫ M ≫ h`.  Proof:
    `1_d = h°h = h°(hh°)h ⊑ h° M h`, using `(hh°)h = h(h°h) = h`. -/
theorem id_le_split_conj {c d : 𝒜} {h : c ⟶ d} {A M : c ⟶ c}
    (hhA : h ≫ h° = A) (hh1 : h° ≫ h = Cat.id d) (hAM : A ⊑ M) :
    Cat.id d ⊑ h° ≫ M ≫ h := by
  have hmid : h° ≫ (h ≫ h°) ≫ h = h° ≫ h := by
    have e : (h ≫ h°) ≫ h = h := by rw [Cat.assoc, hh1, Cat.comp_id]
    rw [e]
  calc Cat.id d = h° ≫ h := hh1.symm
    _ = h° ≫ (h ≫ h°) ≫ h := hmid.symm
    _ ⊑ h° ≫ M ≫ h := by rw [hhA]; exact comp_mono_left h° (comp_mono_right hAM h)

/-- **§2.166 (apex-split tabulation).**  Let `(f,g)` tabulate `U = f ≫ g°` and let
    `R ⊑ U` be APEX-SATURATED (`R = f ≫ tabApex f g R ≫ g°`).  If a map `h : c ⟶ d`
    SPLITS the apex coreflexive — `h ≫ h° = tabApex f g R`, `h° ≫ h = 1_d` — then the
    refined legs `(f ≫ h, g ≫ h)` form a genuine tabulation of `R`.

    The saturation hypothesis `hsat` is non-vacuous and *necessary* (see the section
    note): the un-saturated form is false (`S2_22.tab_transport_gap`); `R = U` and every
    difunctional `R ⊑ U` are saturated.  `htab` is retained to certify that `(f,g)`
    tabulates `U` (it is not consumed: apex-saturation is the genuine content). -/
theorem tabulation_of_split_apex {a b c d : 𝒜}
    {f : a ⟶ c} {g : b ⟶ c} {R : a ⟶ b} {h : c ⟶ d}
    (hf : Map f) (hg : Map g) (hRS : R ⊑ f ≫ g°)
    (_htab : f° ≫ f ∩ g° ≫ g = Cat.id c)
    (hh : Map h) (hhA : h ≫ h° = tabApex f g R) (hh1 : h° ≫ h = Cat.id d)
    (hsat : R = f ≫ (tabApex f g R) ≫ g°) :
    Tabulates (f ≫ h) (g ≫ h) R := by
  have hFmap : Map (f ≫ h) := map_comp hf hh
  have hGmap : Map (g ≫ h) := map_comp hg hh
  obtain ⟨hAf, hAg⟩ := tabApex_le_legs hf hg hRS
  have hReq : R = (f ≫ h) ≫ (g ≫ h)° := by
    rw [Allegory.recip_comp]
    calc R = f ≫ (tabApex f g R) ≫ g° := hsat
      _ = f ≫ (h ≫ h°) ≫ g° := by rw [hhA]
      _ = (f ≫ h) ≫ h° ≫ g° := by simp [Cat.assoc]
  have hApex : (f ≫ h)° ≫ (f ≫ h) ∩ (g ≫ h)° ≫ (g ≫ h) = Cat.id d := by
    apply le_antisymm
    · exact le_trans (inter_lb_left _ _) hFmap.2
    · refine le_inter ?_ ?_
      · have hconj : Cat.id d ⊑ h° ≫ (f° ≫ f) ≫ h := id_le_split_conj hhA hh1 hAf
        have heq : h° ≫ (f° ≫ f) ≫ h = (f ≫ h)° ≫ (f ≫ h) := by
          rw [Allegory.recip_comp]; simp [Cat.assoc]
        rwa [heq] at hconj
      · have hconj : Cat.id d ⊑ h° ≫ (g° ≫ g) ≫ h := id_le_split_conj hhA hh1 hAg
        have heq : h° ≫ (g° ≫ g) ≫ h = (g ≫ h)° ≫ (g ≫ h) := by
          rw [Allegory.recip_comp]; simp [Cat.assoc]
        rwa [heq] at hconj
  exact ⟨hFmap, hGmap, hReq, hApex⟩

/-! ## §2.166  Tabular ⟺ pre-tabular and coreflexives split

  An allegory is tabular iff it is pre-tabular and all coreflexives split (§2.166).
  We package both directions as theorems *relative to the apex-saturation* that the
  general construction needs (see `tabulation_of_split_apex`).  Concretely:

  • FORWARD (tabular ⟹ coreflexives split): in a `TabularAllegory` every coreflexive
    splits — this is exactly `S2_2.coreflexive_splits` (re-exported here for §2.166).
  • CONVERSE: given a pre-tabular containment and a splitting of the apex coreflexive
    of an apex-saturated `R`, `R` is tabular (`tabulation_of_split_apex`). -/

/-- **§2.166 (forward)**: in a tabular allegory every coreflexive splits (§2.163).
    This is the §2.166 direction "tabular ⟹ all coreflexives split". -/
theorem tabular_coreflexives_split {𝒜 : Type u} [TabularAllegory 𝒜] {a : 𝒜}
    {A : a ⟶ a} (hcor : Coreflexive A) :
    ∃ (c : 𝒜) (g : a ⟶ c), SplitsAsMap g A := by
  obtain ⟨c, g, hg, hgg, hg1⟩ := coreflexive_splits hcor
  exact ⟨c, g, hg, hgg, hg1⟩

/-- **§2.166 (converse, apex-saturated form)**: a containment `R ⊑ U` whose apex
    coreflexive splits, and which is apex-saturated, is tabular. -/
theorem tabular_of_split_apex {a b c d : 𝒜}
    {f : a ⟶ c} {g : b ⟶ c} {R : a ⟶ b} {h : c ⟶ d}
    (hf : Map f) (hg : Map g) (hRS : R ⊑ f ≫ g°)
    (htab : f° ≫ f ∩ g° ≫ g = Cat.id c)
    (hh : Map h) (hhA : h ≫ h° = tabApex f g R) (hh1 : h° ≫ h = Cat.id d)
    (hsat : R = f ≫ (tabApex f g R) ≫ g°) :
    Tabular R :=
  ⟨d, f ≫ h, g ≫ h, tabulation_of_split_apex hf hg hRS htab hh hhA hh1 hsat⟩

/-! ## §2.169  Effective reflection: equivalence relations split in `Spl 𝒜`

  An EFFECTIVE allegory is one in which all equivalence relations split (§2.169); by
  §2.163 this is equivalent to effectiveness of its category of maps.  Since `Spl 𝒜`
  splits *every* symmetric idempotent (`SplHom.split_symmetric_idempotent`), and every
  equivalence relation is a symmetric idempotent, `Spl 𝒜` is effective. -/

/-- An EQUIVALENCE relation `E : a ⟶ a` (§2.12): reflexive, symmetric, transitive. -/
structure EquivRel (a : 𝒜) where
  /-- The underlying endomorphism. -/
  E : a ⟶ a
  /-- REFLEXIVE: `1_a ⊑ E`. -/
  refl : Reflexive E
  /-- SYMMETRIC: `E° ⊑ E`. -/
  sym : Symmetric E
  /-- TRANSITIVE: `E ≫ E ⊑ E`. -/
  trans : Transitive E

namespace EquivRel

variable {a : 𝒜}

/-- An equivalence relation is symmetric in the strong sense `E° = E`. -/
theorem recip_eq (E : EquivRel a) : E.E° = E.E :=
  le_antisymm E.sym (by have := recip_mono E.sym; rwa [Allegory.recip_recip] at this)

/-- An equivalence relation is idempotent `E ≫ E = E`: `⊑` by transitivity, `⊒` since
    `E = 1 ≫ E ⊑ E ≫ E` using reflexivity. -/
theorem idem (E : EquivRel a) : E.E ≫ E.E = E.E := by
  refine le_antisymm E.trans ?_
  calc E.E = Cat.id a ≫ E.E := by rw [Cat.id_comp]
    _ ⊑ E.E ≫ E.E := comp_mono_right E.refl E.E

/-- An equivalence relation is a symmetric idempotent (§2.12, §2.163). -/
def toSymIdem (E : EquivRel a) : SymIdem a :=
  ⟨E.E, E.recip_eq, E.idem⟩

end EquivRel

/-- **§2.169**: every equivalence relation of `Spl 𝒜` splits.  An equivalence relation
    on an object `E = (a,e)` of `Spl 𝒜` is a split-hom `Φ : E ⟶ E` that is reflexive
    (`1_{E} ⊑ Φ`), symmetric (`Φ.R° = Φ.R`) and transitive (`Φ.R ≫ Φ.R ⊑ Φ.R`); being
    symmetric + transitive over a reflexive carrier it is a symmetric idempotent, hence
    splits by `SplHom.split_symmetric_idempotent`.

    We state it for any `Φ` already known to be a symmetric idempotent (`hsym`,
    `hidem`) — which equivalence relations are — giving the splitting legs explicitly. -/
theorem spl_equivalence_splits {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    ∃ (G : SplObj 𝒜) (leg : SplHom E G),
      splComp leg (splRecip leg) = Φ ∧ splComp (splRecip leg) leg = splId G :=
  ⟨Φ.splitObj hsym hidem, Φ.splitLeg hsym hidem, Φ.split_symmetric_idempotent hsym hidem⟩

/-- **§2.163 / §2.169**: every coreflexive of `Spl 𝒜` splits (it is a symmetric
    idempotent), so `Spl 𝒜` is tabular at coreflexives — the §2.166 hypothesis that
    drives tabularity.  A coreflexive `Φ ⊑ 1_E` of `Spl 𝒜` with `Φ.R° = Φ.R`,
    `Φ.R ≫ Φ.R = Φ.R` splits. -/
theorem spl_coreflexive_splits {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    ∃ (G : SplObj 𝒜) (leg : SplHom E G),
      splComp leg (splRecip leg) = Φ ∧ splComp (splRecip leg) leg = splId G :=
  spl_equivalence_splits Φ hsym hidem

/-! ## §2.169  `Spl 𝒜` is effective in the `EffectiveAllegory` shape

  `EffectiveAllegory.split_symmetric_idempotent` asks: a symmetric idempotent `E`
  splits as `E = f ≫ f°` with `f` a MAP and `f° ≫ f = 1`.  For a general symmetric
  idempotent the leg is simple but not entire (entireness `1 ⊑ E` requires `E`
  REFLEXIVE).  Exactly the REFLEXIVE symmetric idempotents — the EQUIVALENCE relations
  — split with a *map* leg, which is the §2.169 effectiveness condition (equivalence
  relations split, the leg being a map).  We prove this map-shaped splitting in
  `Spl 𝒜`. -/

/-- **§2.169 (effective shape)**: a REFLEXIVE symmetric idempotent `Φ` of `Spl 𝒜` (an
    equivalence relation: `E.idem.e ⊑ Φ.R`, `Φ.R° = Φ.R`, `Φ.R ≫ Φ.R = Φ.R`) splits
    with a MAP leg, matching `EffectiveAllegory.split_symmetric_idempotent`:
    there is `G` and a `Map`-leg `f : E ⟶ G` with `f ≫ f° = Φ` and `f° ≫ f = 1_G`. -/
theorem spl_equivalence_splits_map {E : SplObj 𝒜} (Φ : SplHom E E)
    (hrefl : E.idem.e ⊑ Φ.R) (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    ∃ (G : SplObj 𝒜) (f : E ⟶ G),
      Map f ∧ f ≫ f° = Φ ∧ f° ≫ f = Cat.id G := by
  refine ⟨Φ.splitObj hsym hidem, Φ.splitLeg hsym hidem, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- Entire in `Spl 𝒜`: `dom f = id E`, i.e. `id E ∩ f ≫ f° = id E`.  Underlying:
    -- `e ∩ Φ.R ≫ Φ.R° = e`; with `Φ.R° = Φ.R`, `Φ.R ≫ Φ.R = Φ.R` this is `e ∩ Φ.R = e`,
    -- true since `e ⊑ Φ.R` (reflexivity).
    show dom (Φ.splitLeg hsym hidem) = Cat.id E
    apply SplHom.ext
    show E.idem.e ∩ Φ.R ≫ Φ.R° = E.idem.e
    rw [hsym, hidem]
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hrefl)
  · -- Simple in `Spl 𝒜`: `f° ≫ f ⊑ id G`.  Underlying `Φ.R° ≫ Φ.R = Φ.R = id G`.
    dsimp only [Simple]
    have he : (Φ.splitLeg hsym hidem)° ≫ (Φ.splitLeg hsym hidem) = Cat.id (Φ.splitObj hsym hidem) := by
      apply SplHom.ext; show Φ.R° ≫ Φ.R = Φ.R; rw [hsym, hidem]
    rw [he]; exact le_refl _
  · -- f ≫ f° = Φ.
    apply SplHom.ext; show Φ.R ≫ Φ.R° = Φ.R; rw [hsym, hidem]
  · -- f° ≫ f = id G.
    apply SplHom.ext; show Φ.R° ≫ Φ.R = Φ.R; rw [hsym, hidem]

end Freyd.Alg
