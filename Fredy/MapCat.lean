/-
  Freyd & Scedrov, *Categories and Allegories* §2.147  The category of maps Map(𝒜).

  §2.14   CATEGORY OF MAPS Map(𝒜): objects of 𝒜; morphisms a ⟶ b = maps of 𝒜.
  §2.147  If 𝒜 is a TABULAR allegory then Map(𝒜) has finite limits.
          Freyd's constructive recipes:
            • pullback of f, g : a → c   = tabulation of f ≫ g°
            • equalizer of f, g : a → b  = tabulation of dom (f ∩ g)
            • image of f : a → b         = tabulation of dom (f°)
            • g is a cover iff 1 ⊑ g° ≫ g (i.e. g° is entire)

  **Proved in this file** (all sorry-free):
  (A) Cat instance on MapObj 𝒜  (§2.14).
  (B) Helper lemmas: dom R ⊑ dom R ≫ R; dom(f∩g) ≫ f = f ∩ g for Map f.
  (C) Pullback cone equation π₁° ≫ f = π₂° ≫ g  (§2.147).
  (D) Equalizer cone equation e° ≫ f = e° ≫ g  (§2.147).
  (E) Cover characterization: g is a cover iff Entire g°  (§2.147).
  (F) §2.143 mediating map is entire + simple (building blocks for UMP).
  (G) §2.143 forward UMP (in `S2_1.lean`; no `Map(π°)` hypotheses — source-apex).
  (H) Pullback UMP in Map(𝒜)  (§2.147).
  (I) Equalizer UMP in Map(𝒜)  (§2.147).

  **Source-apex convention** (legs FROM the apex: π₁ : p→a, π₂ : p→b, R = π₁°≫π₂):
  the §2.143 forward direction's mediating map needs NO `Map(π°)` hypothesis — the legs
  are already maps the right way, and the old `Map(π₁°)` blocker is gone.  The §2.143
  universal property (`tabulation_UP_forward`/`tabulation_UP_unique`) lives in `S2_1.lean`.

  **§2.148** (sorry-free):
  (J) `tab_round_trip_rel`: Ψ∘Φ = id — from a tabulation (f,g) of R, f°≫g = R.
  (K) `span_self_tabulates`: a jointly-monic span (f,g) in Map(𝒜) self-tabulates f°≫g.
  (L) `tab_iso_unique_exists`: two tabulations of R are related by a UNIQUE isomorphism
      (now UNCONDITIONAL — §2.144 via `tabulation_unique_iso`; no `Map(f°)` needed).
  The allegory equivalence `RelMap 𝒜 ≅ 𝒜` is packaged below (`relMap_allegoryEquiv`).
-/

import Fredy.S2_1
import Fredy.S2_22b
import Fredy.S1_60

universe v u

open Freyd
open Freyd.Alg

namespace Freyd.Alg

/-! ## §2.14  The category of maps Map(𝒜) -/

/-- Objects of Map(𝒜) coincide with objects of 𝒜.
    An `abbrev` alias (not `def`) so Lean transparently unfolds it when
    constructing the Cat instance; a `def` would cause typeclass look-ups to
    fail when Lean's unifier encounters `MapObj 𝒜` vs `𝒜`. -/
abbrev MapObj (𝒜 : Type u) : Type u := 𝒜

variable {𝒜 : Type u} [Allegory 𝒜]

/-! ### Helper order lemmas -/

/-- R ⊑ dom R ≫ R  (§2.121). -/
theorem le_dom_comp {a b : 𝒜} (R : a ⟶ b) : R ⊑ dom R ≫ R := by
  have h := modular_le (Cat.id a) R R
  rw [Cat.id_comp, Allegory.inter_idem, ← dom] at h
  exact h

/-- dom R ≫ R = R. -/
theorem dom_comp_eq {a b : 𝒜} (R : a ⟶ b) : dom R ≫ R = R :=
  le_antisymm
    (by have := comp_mono_right (dom_coreflexive R) R; rwa [Cat.id_comp] at this)
    (le_dom_comp R)

/-- dom(f ∩ g) ≫ f = f ∩ g  for any Map f. -/
theorem dom_inter_comp {a b : 𝒜} {f g : a ⟶ b} (hf : Map f) : dom (f ∩ g) ≫ f = f ∩ g := by
  apply le_antisymm
  · have hf_le : dom (f ∩ g) ≫ f ⊑ f := by
      have := comp_mono_right (dom_coreflexive (f ∩ g)) f; rwa [Cat.id_comp] at this
    have hg_le : dom (f ∩ g) ≫ f ⊑ g := by
      rw [dom_inter]
      have h2 : (g ≫ f°) ≫ f ⊑ g := by
        rw [Cat.assoc]; have := comp_mono_left g hf.2; rwa [Cat.comp_id] at this
      exact le_trans (comp_mono_right (inter_lb_right _ _) f) h2
    exact le_inter hf_le hg_le
  · exact le_trans (le_dom_comp (f ∩ g)) (comp_mono_left _ (inter_lb_left f g))

/-- dom(f ∩ g) ≫ g = f ∩ g  for any Map g.  By symmetry. -/
theorem dom_inter_comp_right {a b : 𝒜} {f g : a ⟶ b} (hg : Map g) : dom (f ∩ g) ≫ g = f ∩ g := by
  have h : dom (g ∩ f) ≫ g = g ∩ f := dom_inter_comp hg
  have hdom : dom (f ∩ g) = dom (g ∩ f) := by congr 1; exact Allegory.inter_comm f g
  calc dom (f ∩ g) ≫ g = dom (g ∩ f) ≫ g := by rw [hdom]
    _ = g ∩ f := h
    _ = f ∩ g := Allegory.inter_comm g f

/-! ### Identity and composition in Map(𝒜) -/

private theorem id_is_map (a : 𝒜) : Map (Cat.id a) :=
  ⟨show Entire (Cat.id a) from by
        simp [Entire, dom, recip_id, Cat.comp_id, Allegory.inter_idem],
   show Simple (Cat.id a) from by
        simp [Simple, recip_id, Cat.id_comp]; exact le_refl _⟩

/-- **§2.14**: Map(𝒜) is a category. -/
instance (priority := 0) mapCat : Cat.{v} (MapObj 𝒜) where
  Hom   a b := { R : a ⟶ b // Map R }
  id    a   := ⟨Cat.id a, id_is_map a⟩
  comp  f g := ⟨f.val ≫ g.val, map_comp f.property g.property⟩
  id_comp f := Subtype.ext (Cat.id_comp f.val)
  comp_id f := Subtype.ext (Cat.comp_id f.val)
  assoc f g h := Subtype.ext (Cat.assoc f.val g.val h.val)

/-! ## §2.147  Finite limits in Map(𝒜) via tabulations

  In the source-apex convention the tabulation legs `f : c→a`, `g : c→b` are maps FROM
  the apex, so the pullback projections of `f g°` ARE maps (no `Map(π°)` hypotheses are
  needed — the old blocker vanishes). -/

section TabularLimits

variable [TabularAllegory 𝒜]

/-- id_c ⊑ f ≫ f° for first tabulation leg (the joint-monic equation). -/
theorem tab_ffo {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) : Cat.id c ⊑ f ≫ f° :=
  ht.2.2.2 ▸ inter_lb_left _ _

/-- id_c ⊑ g ≫ g° for second tabulation leg (the joint-monic equation). -/
theorem tab_gog {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) : Cat.id c ⊑ g ≫ g° :=
  ht.2.2.2 ▸ inter_lb_right _ _

/-! ### §2.147  Pullback cone equation -/

/-- **§2.147 pullback cone**: if (π₁, π₂) tabulate f ≫ g° (source-apex: π₁ : p→a,
    π₂ : p→b, π₁°≫π₂ = f≫g°) then π₁ ≫ f = π₂ ≫ g. -/
theorem tab_pullback_cone {a b c p : 𝒜} {f : a ⟶ c} {g : b ⟶ c}
    (hf : Map f) (hg : Map g)
    {π₁ : p ⟶ a} {π₂ : p ⟶ b}
    (hfg : π₁° ≫ π₂ = f ≫ g°)
    (hπ₁1 : π₁ ≫ π₁° = Cat.id p) (hπ₂1 : π₂ ≫ π₂° = Cat.id p) :
    π₁ ≫ f = π₂ ≫ g := by
  -- π₂≫g = (π₁π₁°)π₂g = π₁(π₁°π₂)g = π₁(fg°)g = π₁f(g°g) ⊑ π₁f, and symmetrically.
  have hrecip : π₂° ≫ π₁ = g ≫ f° := by
    have h : (π₁° ≫ π₂)° = (f ≫ g°)° := congrArg Allegory.recip hfg
    simpa [Allegory.recip_comp, Allegory.recip_recip] using h
  -- hA : π₁ ≫ f ≫ g° = π₂;  hB : π₂ ≫ g ≫ f° = π₁.
  have hA : π₁ ≫ f ≫ g° = π₂ := by
    rw [← hfg, ← Cat.assoc, hπ₁1, Cat.id_comp]
  have hB : π₂ ≫ g ≫ f° = π₁ := by
    rw [← hrecip, ← Cat.assoc, hπ₂1, Cat.id_comp]
  apply le_antisymm
  · -- π₁f = (π₂ g f°) f = π₂ g (f°f) ⊑ π₂ g.
    calc π₁ ≫ f = (π₂ ≫ g ≫ f°) ≫ f := by rw [hB]
      _ = π₂ ≫ g ≫ (f° ≫ f) := by simp [Cat.assoc]
      _ ⊑ π₂ ≫ g ≫ Cat.id c := comp_mono_left _ (comp_mono_left _ hf.2)
      _ = π₂ ≫ g := by rw [Cat.comp_id]
  · -- π₂g = (π₁ f g°) g = π₁ f (g°g) ⊑ π₁ f.
    calc π₂ ≫ g = (π₁ ≫ f ≫ g°) ≫ g := by rw [hA]
      _ = π₁ ≫ f ≫ (g° ≫ g) := by simp [Cat.assoc]
      _ ⊑ π₁ ≫ f ≫ Cat.id c := comp_mono_left _ (comp_mono_left _ hg.2)
      _ = π₁ ≫ f := by rw [Cat.comp_id]

/-! ### §2.147  Cover characterization -/

/-- **§2.147**: g : a → b is a cover iff Entire(g°). -/
theorem cover_iff_recip_entire {a b : 𝒜} (g : a ⟶ b) :
    Cat.id b ⊑ g° ≫ g ↔ Entire g° := by
  simp only [Entire, dom, Allegory.recip_recip]
  constructor
  · intro h; exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) h)
  · intro h
    calc Cat.id b = Cat.id b ∩ g° ≫ g := h.symm
      _ ⊑ g° ≫ g := inter_lb_right _ _

/-! ### §2.147  Pullback universal property in Map(𝒜)

  The §2.143 universal property of tabulations lives in `S2_1.lean`
  (`tabulation_UP_forward`/`tabulation_UP_unique`) — in the source-apex convention its
  mediating map needs NO `Map(π°)` hypothesis (the old blocker is gone). -/

/-- **§2.147 pullback UMP**: the tabulation of fg° gives the pullback of f and g in Map(𝒜).
    Given maps x : q→a, y : q→b with x≫f = y≫g, there is a unique h : q→p in Map(𝒜)
    with h≫π₁=x and h≫π₂=y. -/
theorem tab_pullback_UMP {a b c p q : 𝒜} {f : a ⟶ c} {g : b ⟶ c}
    (hf : Map f) (hg : Map g)
    {π₁ : p ⟶ a} {π₂ : p ⟶ b}
    (ht : Tabulates π₁ π₂ (f ≫ g°))
    {x : q ⟶ a} {y : q ⟶ b}
    (hx : Map x) (hy : Map y)
    (hcone : x ≫ f = y ≫ g) :
    ∃ (hm : q ⟶ p), Map hm ∧ hm ≫ π₁ = x ∧ hm ≫ π₂ = y ∧
      ∀ hm' : q ⟶ p, Map hm' → hm' ≫ π₁ = x → hm' ≫ π₂ = y → hm' = hm := by
  -- Derive x°y ⊑ fg° from cone equation.
  have hgg : Cat.id b ⊑ g ≫ g° := by
    have := hg.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have hxy : x° ≫ y ⊑ f ≫ g° := by
    have s1 : x° ≫ y ⊑ x° ≫ y ≫ g ≫ g° := by
      have h1 := comp_mono_left (x° ≫ y) hgg; rw [Cat.comp_id] at h1
      simp only [Cat.assoc] at h1 ⊢; exact h1
    have s2 : x° ≫ y ≫ g ≫ g° = (x° ≫ x) ≫ f ≫ g° := by
      have hh : x° ≫ (y ≫ g) ≫ g° = x° ≫ (x ≫ f) ≫ g° := by rw [hcone]
      simp only [Cat.assoc] at hh ⊢; exact hh
    have s3 : (x° ≫ x) ≫ f ≫ g° ⊑ f ≫ g° := by
      have h3 := comp_mono_right hx.2 (f ≫ g°)
      rw [Cat.id_comp] at h3; exact h3
    rw [s2] at s1; exact le_trans s1 s3
  obtain ⟨hm, hh_map, hhx, hhy⟩ := tabulation_UP_forward ht hx hy hxy
  refine ⟨hm, hh_map, hhx, hhy, fun hm' hh'_map hhx' hhy' => ?_⟩
  exact tabulation_UP_unique ht hh'_map hh_map (hhx'.trans hhx.symm) (hhy'.trans hhy.symm)

/-! ### §2.147  Equalizer cone + universal property in Map(𝒜)

  The equalizer of f, g : a→b is the splitting e : p→a of dom(f∩g):
  `e° ≫ e = dom(f∩g)`, `e ≫ e° = id_p` (`coreflexive_splits`, source-apex direction).
  The cone is `e ≫ f = e ≫ g`; the UMP factors any map killing the parallel pair. -/

/-- **§2.147 equalizer cone**: if e°≫e = dom(f∩g) and e≫e° = id_p then e ≫ f = e ≫ g. -/
theorem tab_equalizer_cone {a b p : 𝒜} {f g : a ⟶ b} {e : p ⟶ a}
    (hf : Map f) (hg : Map g)
    (hee : e° ≫ e = dom (f ∩ g))
    (he1 : e ≫ e° = Cat.id p) :
    e ≫ f = e ≫ g := by
  -- e≫f = e≫(dom(f∩g))≫? ; instead: e(f∩g) = ef ∩ eg and e°e = dom(f∩g) ⊑ (f∩g)(f∩g)°…
  -- Direct: e ≫ f = (e≫e°)≫e≫f = e≫(e°≫e)≫f = e≫dom(f∩g)≫f = e≫(f∩g) (dom_inter_comp),
  -- and likewise e≫g = e≫(f∩g); so e≫f = e≫g.
  have hef : e ≫ f = e ≫ (f ∩ g) := by
    calc e ≫ f = (e ≫ e°) ≫ e ≫ f := by rw [he1, Cat.id_comp]
      _ = e ≫ (e° ≫ e) ≫ f := by simp [Cat.assoc]
      _ = e ≫ dom (f ∩ g) ≫ f := by rw [hee]
      _ = e ≫ (f ∩ g) := by rw [dom_inter_comp hf]
  have heg : e ≫ g = e ≫ (f ∩ g) := by
    calc e ≫ g = (e ≫ e°) ≫ e ≫ g := by rw [he1, Cat.id_comp]
      _ = e ≫ (e° ≫ e) ≫ g := by simp [Cat.assoc]
      _ = e ≫ dom (f ∩ g) ≫ g := by rw [hee]
      _ = e ≫ (f ∩ g) := by rw [dom_inter_comp_right hg]
  rw [hef, heg]

/-- **§2.147 equalizer UMP**: given the splitting e of dom(f∩g) and a map h with h≫f=h≫g,
    there is a unique map k with k≫e=h. -/
theorem tab_equalizer_UMP {a b p q : 𝒜} {f g : a ⟶ b}
    (hf : Map f) (hg : Map g)
    {e : p ⟶ a}
    (he : Map e) (hee : e° ≫ e = dom (f ∩ g)) (he1 : e ≫ e° = Cat.id p)
    {h : q ⟶ a} (hh : Map h) (hcone : h ≫ f = h ≫ g) :
    ∃ (k : q ⟶ p), Map k ∧ k ≫ e = h ∧
      ∀ k' : q ⟶ p, Map k' → k' ≫ e = h → k' = k := by
  -- (e, e) tabulates e°≫e (= dom(f∩g)); we apply the §2.143 forward UP with x = y = h.
  have htab_e : Tabulates e e (e° ≫ e) := ⟨he, he, rfl, by rw [Allegory.inter_idem, he1]⟩
  -- h°≫h ⊑ e°≫e = dom(f∩g).
  -- First h≫(f∩g) = h≫f (h simple: h(f∩g) = hf ∩ hg = hf).
  have hfg_eq : h ≫ (f ∩ g) = h ≫ f := by
    have := simple_dist_inter hh.2 f g; rw [this, hcone, Allegory.inter_idem]
  have hmap_hf : Map (h ≫ f) := map_comp hh hf
  have hent : Cat.id q ⊑ (h ≫ (f ∩ g)) ≫ (h ≫ (f ∩ g))° := by
    have := (hfg_eq ▸ hmap_hf).1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have hdomfg : h° ≫ h ⊑ (f ∩ g) ≫ (f ∩ g)° := by
    have hA := hent
    have hexp : (h ≫ (f ∩ g)) ≫ (h ≫ (f ∩ g))° = h ≫ (f ∩ g) ≫ (f ∩ g)° ≫ h° := by
      rw [Allegory.recip_comp]; simp [Cat.assoc]
    rw [hexp] at hA
    have step : h° ≫ h ⊑ (h° ≫ h) ≫ (f ∩ g) ≫ (f ∩ g)° ≫ (h° ≫ h) := by
      have s1 := comp_mono_left h° hA; rw [Cat.comp_id] at s1
      have s2 := comp_mono_right s1 h
      simp only [Cat.assoc] at s2 ⊢; exact s2
    have sb : (h° ≫ h) ≫ (f ∩ g) ≫ (f ∩ g)° ≫ (h° ≫ h) ⊑ (f ∩ g) ≫ (f ∩ g)° := by
      have sr1 : (h° ≫ h) ≫ (f ∩ g) ≫ (f ∩ g)° ≫ (h° ≫ h) ⊑
               Cat.id a ≫ (f ∩ g) ≫ (f ∩ g)° ≫ (h° ≫ h) := comp_mono_right hh.2 _
      have sr2 : Cat.id a ≫ (f ∩ g) ≫ (f ∩ g)° ≫ (h° ≫ h) ⊑
               Cat.id a ≫ (f ∩ g) ≫ (f ∩ g)° ≫ Cat.id a :=
        comp_mono_left _ (comp_mono_left _ (comp_mono_left _ hh.2))
      have sr3 : Cat.id a ≫ (f ∩ g) ≫ (f ∩ g)° ≫ Cat.id a = (f ∩ g) ≫ (f ∩ g)° := by
        simp [Cat.id_comp, Cat.comp_id]
      exact sr3 ▸ le_trans sr1 sr2
    exact le_trans step sb
  have hdomfg2 : h° ≫ h ⊑ e° ≫ e := by
    rw [hee]; exact le_inter hh.2 hdomfg
  obtain ⟨k, hk_map, hke, _⟩ := tabulation_UP_forward htab_e hh hh hdomfg2
  exact ⟨k, hk_map, hke,
    fun k' hk'_map hk'e => tabulation_UP_unique htab_e hk'_map hk_map (hk'e.trans hke.symm)
      (hk'e.trans hke.symm)⟩

end TabularLimits

/-! ## §2.148  𝒜 ≅ Rel(Map 𝒜) for tabular 𝒜

  In Freyd's §2.148, a tabular allegory 𝒜 is isomorphic to Rel(Map 𝒜) — the
  allegory of relations in its own category of maps.  The comparison functors are:

    Φ : 𝒜 → Rel(Map 𝒜),  R ↦ [tabulation span of R] = [(f, g) with Tabulates f g R]
    Ψ : Rel(Map 𝒜) → 𝒜,  [(f : c→a, g : c→b)] ↦ f° ≫ g

  In the source-apex convention (f : c→a, g : c→b, R = f°≫g, f≫f° ∩ g≫g° = id_c):

    (i)  Ψ∘Φ = id: from Tabulates f g R one has f° ≫ g = R   [see tab_round_trip_rel]
    (ii) Φ∘Ψ on standard spans: (f,g) with f≫f° ∩ g≫g° = id_c self-tabulates
         f°≫g                                                    [see span_self_tabulates]
    (iii) Any two tabulations of the same R are related by a UNIQUE isomorphism
         (UNCONDITIONAL — §2.144, no `Map(f°)` needed)       [see tab_iso_unique_exists]

  A "jointly-monic span in Map(𝒜)" (an object of Rel(Map 𝒜)(a,b)) is exactly a
  `Tabulates`-triple (f,g,R) — the tabulation condition f≫f° ∩ g≫g° = id_c IS the
  §2.141 jointly-monic condition for the pair (f, g) of maps with common source c. -/

section Rel148

variable {𝒜 : Type u} [TabularAllegory 𝒜]

/-- **§2.148 (J) — forward round-trip** (Ψ∘Φ = id): from a tabulation (f,g) of R,
    applying the backward functor Ψ recovers R.  Trivial: Ψ(Φ(R)) = f° ≫ g = R. -/
theorem tab_round_trip_rel {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) : f° ≫ g = R :=
  ht.2.2.1.symm

/-- **§2.148 (K) — backward round-trip** (Φ∘Ψ identifies spans with tabulations):
    a span (f : c→a, g : c→b) of maps satisfying the jointly-monic condition
    f≫f° ∩ g≫g° = id_c is itself a tabulation of f°≫g. -/
theorem span_self_tabulates {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b}
    (hf : Map f) (hg : Map g) (hjoint : f ≫ f° ∩ g ≫ g° = Cat.id c) :
    Tabulates f g (f° ≫ g) :=
  ⟨hf, hg, rfl, hjoint⟩

/-- **§2.148 (L) — unique iso between tabulations** (§2.144, now UNCONDITIONAL): two
    tabulations of the same `R` are related by a unique isomorphism `u` with `f' = uf`,
    `g' = ug`.  No `Map(f°)` hypotheses are needed in the source-apex convention. -/
theorem tab_iso_unique_exists {a b c c' : 𝒜}
    {f : c ⟶ a} {g : c ⟶ b} {f' : c' ⟶ a} {g' : c' ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) (ht' : Tabulates f' g' R) :
    ∃ (u : c' ⟶ c), Map u ∧ Freyd.IsIso u ∧ f' = u ≫ f ∧ g' = u ≫ g :=
  tabulation_unique_iso ht ht'

/-! ## §2.148  RelMap 𝒜 — the allegory Rel(Map(𝒜))

  `RelMap 𝒜` is the allegory whose objects are those of 𝒜 and whose morphisms
  `a ⇸ b` are the TABULAR morphisms `R : a ⟶ b` in 𝒜.  In a `TabularAllegory`
  every morphism is tabular, so `RelMap 𝒜` has the SAME hom-sets as 𝒜 — the subtype
  `{R : a ⟶ b // Tabular R}` is in bijection with `a ⟶ b`.  The allegory operations
  (composition, reciprocation, intersection) on `RelMap 𝒜` are simply those of 𝒜,
  well-defined because tabular morphisms are closed under all three:

    • Closed under recip: if `(f,g)` tabulates `R` then `(g,f)` tabulates `R°`.
    • Closed under comp: if R and S are tabular then R ≫ S is tabular
      (every morphism of 𝒜 is tabular by `TabularAllegory.tabular`).
    • Closed under inter: same reason.

  These closures follow trivially from `TabularAllegory.tabular`, so the subtype
  `{R // Tabular R}` with operations inherited from 𝒜 forms an `Allegory` in a
  uniform way.  We record this and build the comparison functors. -/

/-- Tabularity is closed under reciprocation: if (f,g) tabulates R then (g,f) tabulates R°. -/
theorem tabular_recip {a b : 𝒜} {R : a ⟶ b} (hR : Tabular R) : Tabular R° := by
  obtain ⟨c, f, g, hf, hg, hR_eq, hjoint⟩ := hR
  refine ⟨c, g, f, hg, hf, ?_, by rw [Allegory.inter_comm]; exact hjoint⟩
  -- Goal: R° = g° ≫ f, from R = f° ≫ g.
  calc R° = (f° ≫ g)° := by rw [hR_eq]
    _ = g° ≫ f := by rw [Allegory.recip_comp, Allegory.recip_recip]

/-- Tabularity is closed under composition: both R and S tabular ⟹ R ≫ S tabular.
    In a `TabularAllegory` this is immediate from the axiom. -/
theorem tabular_comp {a b c : 𝒜} {R : a ⟶ b} {S : b ⟶ c}
    (_hR : Tabular R) (_hS : Tabular S) : Tabular (R ≫ S) :=
  TabularAllegory.tabular _

/-- Tabularity is closed under intersection. -/
theorem tabular_inter {a b : 𝒜} {R S : a ⟶ b}
    (_hR : Tabular R) (_hS : Tabular S) : Tabular (R ∩ S) :=
  TabularAllegory.tabular _

/-! ### Hom-set of RelMap 𝒜 and the bijection with 𝒜 homs

  `RelMap 𝒜` has the same objects as 𝒜 and hom-set `a ⇸ b := {R : a ⟶ b // Tabular R}`.
  In a `TabularAllegory` the bijection `Φ : (a ⟶ b) ≅ {R : a ⟶ b // Tabular R}` is
  trivial: `Φ(R) = ⟨R, tabular⟩`, `Ψ(⟨R,_⟩) = R`.

  We package the `Allegory` axioms directly on the subtype to show it forms an allegory
  isomorphic to 𝒜. The instance avoids `RelMapObj 𝒜 = 𝒜` (which would conflict with the
  existing `TabularAllegory` instance) by wrapping objects in a `WrapObj` newtype.  -/

/-- A wrapper newtype for the objects of `RelMap 𝒜`, avoiding instance collisions
    with the ambient `TabularAllegory 𝒜`. -/
structure RelMapObj (𝒜 : Type u) where
  /-- The underlying object. -/
  obj : 𝒜

/-- **§2.148 allegory instance**: `RelMap 𝒜` is an allegory.
    Objects = `RelMapObj 𝒜` (a wrapper for objects of 𝒜); morphisms from `⟨a⟩` to `⟨b⟩`
    are tabular morphisms `{R : a ⟶ b // Tabular R}`.  Operations pointwise from 𝒜. -/
instance relMapAllegory : Allegory.{v} (RelMapObj 𝒜) where
  Hom A B := { R : A.obj ⟶ B.obj // Tabular R }
  id  A   := ⟨Cat.id A.obj, TabularAllegory.tabular _⟩
  comp f g := ⟨f.val ≫ g.val, tabular_comp f.2 g.2⟩
  id_comp f := Subtype.ext (Cat.id_comp f.val)
  comp_id f := Subtype.ext (Cat.comp_id f.val)
  assoc f g h := Subtype.ext (Cat.assoc f.val g.val h.val)
  recip f := ⟨f.val°, tabular_recip f.2⟩
  inter f g := ⟨f.val ∩ g.val, tabular_inter f.2 g.2⟩
  recip_recip f     := Subtype.ext (Allegory.recip_recip f.val)
  recip_comp  f g   := Subtype.ext (Allegory.recip_comp f.val g.val)
  recip_inter f g   := Subtype.ext (Allegory.recip_inter f.val g.val)
  inter_idem  f     := Subtype.ext (Allegory.inter_idem f.val)
  inter_comm  f g   := Subtype.ext (Allegory.inter_comm f.val g.val)
  inter_assoc f g h := Subtype.ext (Allegory.inter_assoc f.val g.val h.val)
  semidistrib R S T := by exact Subtype.ext (Allegory.semidistrib R.val S.val T.val)
  modular R S T     := by exact Subtype.ext (Allegory.modular R.val S.val T.val)

/-! ### Comparison maps Φ and Ψ

  `Φ(R) = ⟨R, tabular⟩` and `Ψ(⟨R,_⟩) = R` are mutually inverse bijections on hom-sets.
  At the allegory level they preserve all operations. -/

/-- **§2.148 Φ** — sends `R : a ⟶ b` to `⟨R, tabular⟩` in RelMap 𝒜. -/
def relMap_Phi {a b : 𝒜} (R : a ⟶ b) : @Cat.Hom _ relMapAllegory.toCat ⟨a⟩ ⟨b⟩ :=
  ⟨R, TabularAllegory.tabular R⟩

/-- **§2.148 Ψ** — discards the tabularity certificate. -/
def relMap_Psi {a b : 𝒜} (R : @Cat.Hom _ relMapAllegory.toCat ⟨a⟩ ⟨b⟩) : a ⟶ b :=
  R.val

/-- **§2.148 (Ψ∘Φ = id)**. -/
@[simp] theorem relMap_Psi_Phi {a b : 𝒜} (R : a ⟶ b) :
    relMap_Psi (relMap_Phi R) = R := rfl

/-- **§2.148 (Φ∘Ψ = id)**. -/
@[simp] theorem relMap_Phi_Psi {a b : 𝒜} (R : @Cat.Hom _ relMapAllegory.toCat ⟨a⟩ ⟨b⟩) :
    relMap_Phi (relMap_Psi R) = R := by cases R; rfl

/-- **§2.148 — Φ preserves composition** (val-level). -/
theorem relMap_Phi_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    (relMap_Phi (R ≫ S)).val = (relMap_Phi R).val ≫ (relMap_Phi S).val := rfl

/-- **§2.148 — Φ preserves reciprocation** (val-level). -/
theorem relMap_Phi_recip {a b : 𝒜} (R : a ⟶ b) :
    (relMap_Phi R°).val = (relMap_Phi R).val° := rfl

/-- **§2.148 — Φ preserves intersection** (val-level). -/
theorem relMap_Phi_inter {a b : 𝒜} (R S : a ⟶ b) :
    (relMap_Phi (R ∩ S)).val = (relMap_Phi R).val ∩ (relMap_Phi S).val := rfl

end Rel148

/-! ## §2.148  AllegoryFunctor and AllegoryEquiv

  An allegory functor F : 𝒜 → ℬ is a functor on the underlying categories that also
  preserves reciprocation and intersection.  An allegory equivalence is a pair of
  allegory functors mutually inverse on objects and homs. -/

section AllegoryFunctorDef

/-- A functor between allegories preserving `≫`, `id`, `°`, `∩`. -/
structure AllegoryFunctor (𝒜 ℬ : Type u) [Allegory.{v} 𝒜] [Allegory.{v} ℬ] where
  /-- Object map. -/
  obj  : 𝒜 → ℬ
  /-- Hom map. -/
  map  : {a b : 𝒜} → (a ⟶ b) → (obj a ⟶ obj b)
  map_id   : ∀ (a : 𝒜), map (Cat.id a) = Cat.id (obj a)
  map_comp : ∀ {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c), map (R ≫ S) = map R ≫ map S
  map_recip : ∀ {a b : 𝒜} (R : a ⟶ b), map R° = (map R)°
  map_inter : ∀ {a b : 𝒜} (R S : a ⟶ b), map (R ∩ S) = map R ∩ map S

/-- A pair of allegory functors mutually inverse on objects and homs (using `HEq`
    for the hom round-trip conditions, since the hom-types differ by the object round-trip). -/
structure AllegoryEquiv (𝒜 ℬ : Type u) [Allegory.{v} 𝒜] [Allegory.{v} ℬ] where
  toFun   : AllegoryFunctor 𝒜 ℬ
  invFun  : AllegoryFunctor ℬ 𝒜
  left_inv_obj  : ∀ (a : 𝒜), invFun.obj (toFun.obj a) = a
  right_inv_obj : ∀ (b : ℬ), toFun.obj (invFun.obj b) = b
  /-- Round-trip on homs: `invFun.map (toFun.map R) ≅ R` (heterogeneously). -/
  left_inv_map  : ∀ {a b : 𝒜} (R : a ⟶ b),
    HEq (invFun.map (toFun.map R)) R
  /-- Round-trip on homs: `toFun.map (invFun.map S) ≅ S` (heterogeneously). -/
  right_inv_map : ∀ {a b : ℬ} (S : a ⟶ b),
    HEq (toFun.map (invFun.map S)) S

end AllegoryFunctorDef

/-! ## §2.148  The equivalence Rel(Map 𝒜) ≅ 𝒜

  We now package the comparison maps Φ, Ψ as an `AllegoryEquiv (RelMapObj 𝒜) 𝒜`. -/

section RelMapEquiv

variable {𝒜 : Type u} [TabularAllegory 𝒜]

/-! ### Allegory functor Ψ : RelMap 𝒜 → 𝒜 -/

/-- The hom-map of Ψ: forget the tabularity certificate, reindexed by `obj`-projections. -/
private def relMap_Psi_map {A B : RelMapObj 𝒜}
    (R : @Cat.Hom _ relMapAllegory.toCat A B) : A.obj ⟶ B.obj := R.val

/-- **§2.148 — Ψ is an allegory functor** RelMap 𝒜 → 𝒜. -/
def relMap_Psi_functor : AllegoryFunctor (RelMapObj 𝒜) 𝒜 where
  obj   := RelMapObj.obj
  map   := relMap_Psi_map
  map_id   A     := rfl
  map_comp R S   := rfl
  map_recip R    := rfl
  map_inter R S  := rfl

/-! ### Allegory functor Φ : 𝒜 → RelMap 𝒜 -/

/-- The hom-map of Φ: wrap with tabularity certificate. -/
private def relMap_Phi_map {a b : 𝒜} (R : a ⟶ b) :
    @Cat.Hom _ relMapAllegory.toCat ⟨a⟩ ⟨b⟩ :=
  ⟨R, TabularAllegory.tabular R⟩

/-- Φ preserves `≫` at the Subtype level. -/
private theorem relMap_Phi_map_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    relMap_Phi_map (R ≫ S) = relMap_Phi_map R ≫ relMap_Phi_map S :=
  Subtype.ext rfl

/-- Φ preserves `°` at the Subtype level. -/
private theorem relMap_Phi_map_recip {a b : 𝒜} (R : a ⟶ b) :
    relMap_Phi_map R° = (relMap_Phi_map R)° :=
  Subtype.ext rfl

/-- Φ preserves `∩` at the Subtype level. -/
private theorem relMap_Phi_map_inter {a b : 𝒜} (R S : a ⟶ b) :
    relMap_Phi_map (R ∩ S) = relMap_Phi_map R ∩ relMap_Phi_map S :=
  Subtype.ext rfl

/-- **§2.148 — Φ is an allegory functor** 𝒜 → RelMap 𝒜. -/
def relMap_Phi_functor : AllegoryFunctor 𝒜 (RelMapObj 𝒜) where
  obj   := fun a => ⟨a⟩
  map   := relMap_Phi_map
  map_id   a     := Subtype.ext rfl
  map_comp R S   := relMap_Phi_map_comp R S
  map_recip R    := relMap_Phi_map_recip R
  map_inter R S  := relMap_Phi_map_inter R S

/-! ### Mutual-inverse conditions -/

-- In the equivalence below: toFun = Ψ (RelMapObj 𝒜 → 𝒜), invFun = Φ (𝒜 → RelMapObj 𝒜).
-- left_inv_obj requires invFun.obj (toFun.obj A) = A, i.e. Φ(Ψ(A)) = A.
-- right_inv_obj requires toFun.obj (invFun.obj a) = a, i.e. Ψ(Φ(a)) = a.

/-- Φ∘Ψ = id on objects: `⟨A.obj⟩ = A`. -/
private theorem relMap_PhiPsi_obj (A : RelMapObj 𝒜) :
    relMap_Phi_functor.obj (relMap_Psi_functor.obj A) = A := by cases A; rfl

/-- Ψ∘Φ = id on objects: `⟨a⟩.obj = a`. -/
private theorem relMap_PsiPhi_obj (a : 𝒜) :
    relMap_Psi_functor.obj (relMap_Phi_functor.obj a) = a := rfl

/-- Φ∘Ψ = id on homs (HEq): `Φ(Ψ(S)) ≅ S`. -/
private theorem relMap_PhiPsi_map {A B : RelMapObj 𝒜}
    (S : @Cat.Hom _ relMapAllegory.toCat A B) :
    HEq (relMap_Phi_functor.map (relMap_Psi_functor.map S)) S := by
  cases A; cases B; cases S; exact HEq.refl _

/-- Ψ∘Φ = id on homs (HEq): `Ψ(Φ(R)) ≅ R`. -/
private theorem relMap_PsiPhi_map {a b : 𝒜} (R : a ⟶ b) :
    HEq (relMap_Psi_functor.map (relMap_Phi_functor.map R)) R :=
  HEq.refl _

/-- **§2.148** — the allegory equivalence `RelMap 𝒜 ≅ 𝒜`.
    Ψ : RelMap 𝒜 → 𝒜 and Φ : 𝒜 → RelMap 𝒜 are mutually inverse allegory functors. -/
def relMap_allegoryEquiv : AllegoryEquiv (RelMapObj 𝒜) 𝒜 where
  toFun         := relMap_Psi_functor
  invFun        := relMap_Phi_functor
  left_inv_obj  := relMap_PhiPsi_obj      -- invFun.obj (toFun.obj A) = A
  right_inv_obj := relMap_PsiPhi_obj      -- toFun.obj (invFun.obj a) = a
  left_inv_map  := relMap_PhiPsi_map      -- HEq (invFun.map (toFun.map S)) S
  right_inv_map := relMap_PsiPhi_map      -- HEq (toFun.map (invFun.map R)) R

end RelMapEquiv


/-! ## §2.212  Map(𝒜) is a pre-logos for tabular unitary distributive 𝒜

    "§2.212: If 𝒜 is a tabular unitary distributive allegory, then Map(𝒜) is a pre-logos."

    PROVED: (1) HasTerminal.
    TODO: (2) HasImages minimality, (3) HasPullbacks, (4) HasBinaryProducts,
              (5) PullbacksTransferCovers, (6) HasSubobjectUnions, (7) PreLogos.
    With the source-apex `Tabulates` the §2.147 pullback/equalizer UMPs (`tab_pullback_UMP`,
    `tab_equalizer_UMP` above) now go through with the projections as genuine maps — the old
    `Map(π°)` blocker is gone.  What remains is purely the bureaucratic packaging of those
    UMPs into the `HasPullbacks`/`HasImages`/… typeclass instances on `MapObj A`. -/

section MapPreLogos

variable {A : Type u} [TabularAllegory A] [UnitaryAllegory A]


-- Subtype equality helper for mapCat homs
private theorem mapHom_ext {a b : MapObj A}
    {f g : @Cat.Hom _ (mapCat (𝒜 := A)) a b}
    (h : f.val = g.val) : f = g := Subtype.ext h

/-- Any two maps from a to unit_obj agree (allegory-level). -/
private theorem map_to_unit_unique_alg {a : A}
    {f g : a ⟶ UnitaryAllegory.unit_obj (𝒜 := A)}
    (hf : Map f) (hg : Map g) : f = g := by
  apply map_order_discrete hf hg
  obtain ⟨hPU, _⟩ := UnitaryAllegory.unit_prop (𝒜 := A)
  have hEntG : Cat.id a ⊑ g ≫ g° := by
    have := hg.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have h1 : f ⊑ (g ≫ g°) ≫ f := by
    have := comp_mono_right hEntG f; rwa [Cat.id_comp] at this
  have h2 : (g ≫ g°) ≫ f = g ≫ g° ≫ f := Cat.assoc g g° f
  have h3 : g ≫ g° ≫ f ⊑ g ≫ Cat.id (UnitaryAllegory.unit_obj (𝒜 := A)) :=
    comp_mono_left g (hPU (g° ≫ f))
  rw [Cat.comp_id] at h3
  exact le_trans h1 (h2 ▸ h3)

/-- §2.152: The unit object of 𝒜 is terminal in Map(𝒜). -/
noncomputable def mapHasTerminal : @HasTerminal (MapObj A) (mapCat (𝒜 := A)) :=
  @HasTerminal.mk (MapObj A) (mapCat (𝒜 := A))
    UnitaryAllegory.unit_obj
    (fun a =>
      let h := unit_proj_is_map (𝒜 := A) a
      (⟨h.choose, h.choose_spec⟩ :
        @Cat.Hom (MapObj A) (mapCat (𝒜 := A)) a (UnitaryAllegory.unit_obj (𝒜 := A))))
    (fun {a} f g =>
      mapHom_ext (map_to_unit_unique_alg f.property g.property))

-- BOOK §2.212 TODO: HasImages (MapObj A) — splitting dom(f°) gives the image; image leg is a
-- source-apex map, so minimality no longer needs `Map(S.arr.val°)`.  Remaining: package as instance.

-- BOOK §2.212 TODO: HasPullbacks (MapObj A) — `tab_pullback_UMP` (above) gives the pullback;
-- projections π₁ : p→a, π₂ : p→b are genuine maps (source-apex).  Remaining: package as instance.

-- BOOK §2.212 TODO: HasBinaryProducts, PullbacksTransferCovers, RegularCategory,
-- HasSubobjectUnions, PreLogos — all depend on HasPullbacks above.

end MapPreLogos

end Freyd.Alg
