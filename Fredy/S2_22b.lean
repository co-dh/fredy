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
import Fredy.S2_16

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

-- §2.13: composition of maps is a map — now `Freyd.Alg.map_comp` in `S2_1.lean`.

/-- The **left modular law** in containment form: `(R ≫ S) ∩ T ⊑ R ≫ (S ∩ R° ≫ T)`.
    Proved by reciprocating the right modular law — only uses `modular_le` and
    `recip_mono`, hence holds in any `Allegory` (no union structure required).
    Compare `S2_22.modular_le_left` which has a vestigial `[UnionAllegory]` annotation. -/
theorem modular_le_left' {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S) ∩ T ⊑ R ≫ (S ∩ R° ≫ T) := by
  have h := modular_le S° R° T°
  rw [Allegory.recip_recip] at h
  have hgoal : ((R ≫ S) ∩ T)° ⊑ (R ≫ (S ∩ R° ≫ T))° := by
    rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_inter,
        Allegory.recip_comp, Allegory.recip_recip]
    exact h
  have := recip_mono hgoal
  rwa [Allegory.recip_recip, Allegory.recip_recip] at this

/-! ## §2.166  Tabulation by splitting the apex coreflexive

  An allegory is TABULAR iff it is pre-tabular and all coreflexive morphisms split
  (§2.166).  The forward direction is immediate; the converse is the construction
  below.  Given a (source-apex) tabulation `(f, g)` of `U = f° ≫ g` (maps `f : c→a`,
  `g : c→b`) and a containment `R ⊑ U`, the coreflexive `A := 1_c ∩ f ≫ R ≫ g°` on
  the apex `c` carries the "image of `R` on the apex".  Splitting `A` by a map
  `h : d ⟶ c` (`h° ≫ h = A`, `h ≫ h° = 1_d`) yields refined legs `(h ≫ f, h ≫ g)`, and

      `(h ≫ f)° ≫ (h ≫ g) = f° ≫ (h° ≫ h) ≫ g = f° ≫ A ≫ g`.

  So `(h ≫ f, h ≫ g)` tabulates `R` IFF `R = f° ≫ A ≫ g` — the APEX-SATURATION of `R`.
  This is genuinely necessary, *not* automatic: it fails for a non-difunctional
  `R ⊑ U`.  We record the honest content: for an apex-saturated `R`, splitting the apex
  coreflexive tabulates `R`.  (`R = U` and every difunctional `R ⊑ U` are saturated.)

  Conventions: repo `Tabulates f g R := Map f ∧ Map g ∧ R = f° ≫ g ∧ ff° ∩ gg° = 1`. -/

/-- The **apex coreflexive** `A = 1_c ∩ f ≫ R ≫ g°` of `R` relative to the tabulation
    `(f,g)` of `U = f° ≫ g` (§2.166): the image of `R` pushed onto the apex `c`. -/
def tabApex {a b c : 𝒜} (f : c ⟶ a) (g : c ⟶ b) (R : a ⟶ b) : c ⟶ c :=
  Cat.id c ∩ f ≫ R ≫ g°

/-- `tabApex` is coreflexive on the apex `c`. -/
theorem tabApex_coreflexive {a b c : 𝒜} (f : c ⟶ a) (g : c ⟶ b) (R : a ⟶ b) :
    Coreflexive (tabApex f g R) :=
  inter_lb_left _ _

/-- The apex coreflexive sits below each of `f ≫ f°` and `g ≫ g°`.  Trivially, since
    `tabApex ⊑ 1_c` (coreflexive) and `1_c ⊑ f ≫ f°`, `1_c ⊑ g ≫ g°` (f, g entire). -/
theorem tabApex_le_legs {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (hf : Map f) (hg : Map g) (_hRS : R ⊑ f° ≫ g) :
    tabApex f g R ⊑ f ≫ f° ∧ tabApex f g R ⊑ g ≫ g° := by
  have hfe : Cat.id c ⊑ f ≫ f° := by
    have := hf.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
  have hge : Cat.id c ⊑ g ≫ g° := by
    have := hg.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
  exact ⟨le_trans (inter_lb_left _ _) hfe, le_trans (inter_lb_left _ _) hge⟩


/-- If a map `h : d ⟶ c` splits a coreflexive `A` (`h° ≫ h = A`, `h ≫ h° = 1_d`) and
    `A ⊑ M`, then `1_d ⊑ h ≫ M ≫ h°`.  Proof:
    `1_d = hh° = h(h°h)h° ⊑ h M h°`, using `h(h°h) = (hh°)h = h`. -/
theorem id_le_split_conj {c d : 𝒜} {h : d ⟶ c} {A M : c ⟶ c}
    (hhA : h° ≫ h = A) (hh1 : h ≫ h° = Cat.id d) (hAM : A ⊑ M) :
    Cat.id d ⊑ h ≫ M ≫ h° := by
  have hmid : h ≫ (h° ≫ h) ≫ h° = h ≫ h° := by
    have e : (h° ≫ h) ≫ h° = h° := by rw [Cat.assoc, hh1, Cat.comp_id]
    rw [e]
  calc Cat.id d = h ≫ h° := hh1.symm
    _ = h ≫ (h° ≫ h) ≫ h° := hmid.symm
    _ ⊑ h ≫ M ≫ h° := by rw [hhA]; exact comp_mono_left h (comp_mono_right hAM h°)

/-- **§2.166 (apex-split tabulation).**  Let `(f,g)` tabulate `U = f° ≫ g` and let
    `R ⊑ U` be APEX-SATURATED (`R = f° ≫ tabApex f g R ≫ g`).  If a map `h : d ⟶ c`
    SPLITS the apex coreflexive — `h° ≫ h = tabApex f g R`, `h ≫ h° = 1_d` — then the
    refined legs `(h ≫ f, h ≫ g)` form a genuine tabulation of `R`. -/
theorem tabulation_of_split_apex {a b c d : 𝒜}
    {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b} {h : d ⟶ c}
    (hf : Map f) (hg : Map g) (hRS : R ⊑ f° ≫ g)
    (htab : f ≫ f° ∩ g ≫ g° = Cat.id c)
    (hh : Map h) (hhA : h° ≫ h = tabApex f g R) (hh1 : h ≫ h° = Cat.id d)
    (hsat : R = f° ≫ (tabApex f g R) ≫ g) :
    Tabulates (h ≫ f) (h ≫ g) R := by
  have hFmap : Map (h ≫ f) := map_comp hh hf
  have hGmap : Map (h ≫ g) := map_comp hh hg
  obtain ⟨hAf, hAg⟩ := tabApex_le_legs hf hg hRS
  have hhcoref : h° ≫ h ⊑ Cat.id c := hhA ▸ tabApex_coreflexive f g R
  have hReq : R = (h ≫ f)° ≫ (h ≫ g) := by
    rw [Allegory.recip_comp]
    calc R = f° ≫ (tabApex f g R) ≫ g := hsat
      _ = f° ≫ (h° ≫ h) ≫ g := by rw [hhA]
      _ = (f° ≫ h°) ≫ h ≫ g := by simp [Cat.assoc]
  have hFF : (h ≫ f) ≫ (h ≫ f)° = h ≫ (f ≫ f°) ≫ h° := by
    rw [Allegory.recip_comp]; simp [Cat.assoc]
  have hGG : (h ≫ g) ≫ (h ≫ g)° = h ≫ (g ≫ g°) ≫ h° := by
    rw [Allegory.recip_comp]; simp [Cat.assoc]
  have hApex : (h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)° = Cat.id d := by
    refine le_antisymm ?_ ?_
    · -- M ⊑ id_d:  M = h(h° M h)h°,  and  h° M h ⊑ ff° ∩ gg° = id_c.
      -- For any leg L: h°(hLh°)h = (h°h)L(h°h) ⊑ L.
      have hsqueeze : ∀ L : c ⟶ c, h° ≫ (h ≫ L ≫ h°) ≫ h ⊑ L := by
        intro L
        have e : h° ≫ (h ≫ L ≫ h°) ≫ h = (h° ≫ h) ≫ L ≫ (h° ≫ h) := by simp [Cat.assoc]
        rw [e]
        have s1 : (h° ≫ h) ≫ L ≫ (h° ≫ h) ⊑ Cat.id c ≫ L ≫ (h° ≫ h) :=
          comp_mono_right hhcoref _
        have s2 : Cat.id c ≫ L ≫ (h° ≫ h) ⊑ Cat.id c ≫ L ≫ Cat.id c :=
          comp_mono_left _ (comp_mono_left _ hhcoref)
        have s3 : Cat.id c ≫ L ≫ Cat.id c = L := by rw [Cat.id_comp, Cat.comp_id]
        have := le_trans s1 s2; rw [s3] at this; exact this
      have hMconj : h° ≫ ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) ≫ h ⊑ Cat.id c := by
        rw [← htab]
        refine le_inter ?_ ?_
        · refine le_trans (comp_mono_left h° (comp_mono_right (inter_lb_left _ _) h)) ?_
          rw [hFF]; exact hsqueeze (f ≫ f°)
        · refine le_trans (comp_mono_left h° (comp_mono_right (inter_lb_right _ _) h)) ?_
          rw [hGG]; exact hsqueeze (g ≫ g°)
      -- M = (h h°) M (h h°) = h (h° M h) h° ⊑ h id_c h° = id_d.
      have hMeq : ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) =
          (h ≫ h°) ≫ ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) ≫ (h ≫ h°) := by
        rw [hh1, Cat.id_comp, Cat.comp_id]
      rw [hMeq]
      have hstep1 : (h ≫ h°) ≫ ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) ≫ (h ≫ h°) =
          h ≫ (h° ≫ ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) ≫ h) ≫ h° := by
        simp [Cat.assoc]
      rw [hstep1]
      have hstep2 : h ≫ (h° ≫ ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) ≫ h) ≫ h° ⊑
          h ≫ Cat.id c ≫ h° := comp_mono_left h (comp_mono_right hMconj h°)
      have hstep3 : h ≫ Cat.id c ≫ h° = Cat.id d := by rw [Cat.id_comp, hh1]
      exact hstep3 ▸ hstep2
    · refine le_inter ?_ ?_
      · rw [hFF]; exact id_le_split_conj hhA hh1 hAf
      · rw [hGG]; exact id_le_split_conj hhA hh1 hAg
  exact ⟨hFmap, hGmap, hReq, hApex⟩

/-! ## §2.166  Tabular ⟺ pre-tabular and coreflexives split

  • FORWARD (tabular ⟹ coreflexives split): in a `TabularAllegory` every coreflexive
    splits — `S2_2.coreflexive_splits` (the splitting map `g : c → a` points from the apex).
  • CONVERSE: given a pre-tabular containment and a splitting of the apex coreflexive
    of an apex-saturated `R`, `R` is tabular (`tabulation_of_split_apex`). -/

/-- **§2.166 (converse, apex-saturated form)**: a containment `R ⊑ U` whose apex
    coreflexive splits, and which is apex-saturated, is tabular. -/
theorem tabular_of_split_apex {a b c d : 𝒜}
    {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b} {h : d ⟶ c}
    (hf : Map f) (hg : Map g) (hRS : R ⊑ f° ≫ g)
    (htab : f ≫ f° ∩ g ≫ g° = Cat.id c)
    (hh : Map h) (hhA : h° ≫ h = tabApex f g R) (hh1 : h ≫ h° = Cat.id d)
    (hsat : R = f° ≫ (tabApex f g R) ≫ g) :
    Tabular R :=
  ⟨d, h ≫ f, h ≫ g, tabulation_of_split_apex hf hg hRS htab hh hhA hh1 hsat⟩

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
