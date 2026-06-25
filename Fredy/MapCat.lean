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
  (G) §2.143 forward UMP with Map(π₁°)/Map(π₂°) hypotheses.
  (H) Pullback UMP in Map(𝒜)  (§2.147).
  (I) Equalizer UMP in Map(𝒜)  (§2.147).

  **Note on Map(π₁°)**:
  In our common-TARGET convention (π₁ : a→p, π₂ : b→p, R = π₁≫π₂°),
  the §2.143 forward direction needs Simple(π₁°): π₁≫π₁° ⊑ id_a, which is NOT
  implied by `Tabulates` alone.  We add `Map π₁°` and `Map π₂°` as hypotheses.
  For the equalizer splitting e of dom(f∩g): e≫e°=dom(f∩g)⊑id_a and e°≫e=id_p,
  so Map(e°) holds (Entire: e°≫e=id_p; Simple: e≫e°⊑id_a from dom_coreflexive).

  **§2.148** (partial — sorry-free building blocks):
  (J) `tab_round_trip_rel`: Ψ∘Φ = id — from a tabulation (f,g) of R, f≫g° = R.
  (K) `span_self_tabulates`: a jointly-monic span (f,g) in Map(𝒜) self-tabulates.
  (L) `tab_iso_unique_exists`: two tabulations of R are related by a UNIQUE iso in
      Map(𝒜), given that all four recip-legs are maps.  Packages existence
      (`tabulation_UP_forward`) + uniqueness (`tabulation_UP_unique`).

  **§2.148 BOOK TODO** (allegory-equivalence packaging):
  The full 𝒜 ≅ Rel(Map 𝒜) equivalence requires:
    1. Building `Rel(Map 𝒜)` as an `Allegory` instance (spans with the §2.111
       allegory structure: composition via pullback + image; intersection;
       reciprocation by swapping legs).
    2. Showing Map(f°) holds for every tabulation leg f (so the §2.144 iso
       exists unconditionally).  In our common-TARGET convention this reduces to
       showing f≫f° ⊑ id — which holds when f is a SPLIT MONIC (f°≫f=id and
       ff° splits as a coreflexive).  A tabulation leg f satisfies f°≫f=id
       (from tab_fof), so f is a section; but ff° ⊑ id is NOT automatic.
    3. Packaging the comparison functors as genuine allegory functors.
  Deferred; the round-trip equations (J)–(L) are the algebraic core.
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

/-! ## §2.147  Finite limits in Map(𝒜) via tabulations -/

section TabularLimits

variable [TabularAllegory 𝒜]

/-- f° ≫ f = id_c for first tabulation leg. -/
theorem tab_fof {a b c : 𝒜} {f : a ⟶ c} {g : b ⟶ c} {R : a ⟶ b}
    (ht : Tabulates f g R) : f° ≫ f = Cat.id c :=
  le_antisymm ht.1.2 (ht.2.2.2 ▸ inter_lb_left _ _)

/-- g° ≫ g = id_c for second tabulation leg. -/
theorem tab_gog {a b c : 𝒜} {f : a ⟶ c} {g : b ⟶ c} {R : a ⟶ b}
    (ht : Tabulates f g R) : g° ≫ g = Cat.id c :=
  le_antisymm ht.2.1.2 (ht.2.2.2 ▸ inter_lb_right _ _)

/-! ### §2.147  Pullback cone equation -/

/-- **§2.147 pullback cone**: if (π₁, π₂) tabulate f ≫ g° then π₁° ≫ f = π₂° ≫ g. -/
theorem tab_pullback_cone {a b c p : 𝒜} {f : a ⟶ c} {g : b ⟶ c}
    (hf : Map f) (hg : Map g)
    {π₁ : a ⟶ p} {π₂ : b ⟶ p}
    (hfg : f ≫ g° = π₁ ≫ π₂°)
    (hπ₁1 : π₁° ≫ π₁ = Cat.id p) (hπ₂1 : π₂° ≫ π₂ = Cat.id p) :
    π₁° ≫ f = π₂° ≫ g := by
  have hπ₁fg : π₁° ≫ (f ≫ g°) = π₂° := by
    rw [hfg, ← Cat.assoc, hπ₁1, Cat.id_comp]
  have hrecip : g ≫ f° = π₂ ≫ π₁° := by
    have h : (f ≫ g°)° = (π₁ ≫ π₂°)° := congrArg Allegory.recip hfg
    simp [Allegory.recip_comp, Allegory.recip_recip] at h; exact h
  have hπ₂gf : π₂° ≫ (g ≫ f°) = π₁° := by
    rw [hrecip, ← Cat.assoc, hπ₂1, Cat.id_comp]
  apply le_antisymm
  · calc π₁° ≫ f
        = (π₂° ≫ g ≫ f°) ≫ f := by rw [hπ₂gf]
      _ = π₂° ≫ g ≫ (f° ≫ f) := by simp [Cat.assoc]
      _ ⊑ π₂° ≫ g ≫ Cat.id c  := comp_mono_left _ (comp_mono_left _ hf.2)
      _ = π₂° ≫ g              := by rw [Cat.comp_id]
  · calc π₂° ≫ g
        = (π₁° ≫ f ≫ g°) ≫ g := by rw [hπ₁fg]
      _ = π₁° ≫ f ≫ (g° ≫ g) := by simp [Cat.assoc]
      _ ⊑ π₁° ≫ f ≫ Cat.id c  := comp_mono_left _ (comp_mono_left _ hg.2)
      _ = π₁° ≫ f              := by rw [Cat.comp_id]

/-! ### §2.147  Equalizer cone equation -/

/-- **§2.147 equalizer cone**: if e≫e°=dom(f∩g) and e°e=id_p then e°≫f = e°≫g. -/
theorem tab_equalizer_cone {a b p : 𝒜} {f g : a ⟶ b} {e : a ⟶ p}
    (hf : Map f) (hg : Map g)
    (hee : e ≫ e° = dom (f ∩ g))
    (he1 : e° ≫ e = Cat.id p) :
    e° ≫ f = e° ≫ g := by
  have hef : e ≫ (e° ≫ f) = f ∩ g := by
    simp only [← Cat.assoc, hee, dom_inter_comp hf]
  have heg : e ≫ (e° ≫ g) = f ∩ g := by
    simp only [← Cat.assoc, hee, dom_inter_comp_right hg]
  have key := congrArg (e° ≫ ·) (hef.trans heg.symm)
  simp only [← Cat.assoc, he1, Cat.id_comp] at key
  exact key

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

/-! ### §2.143  Tabulation universal property

  In our common-TARGET convention (π₁ : a→p, π₂ : b→p, R = π₁≫π₂°),
  the mediating map for x : q→a, y : q→b with x°y ⊑ π₁π₂° is
  H = x≫π₁ ∩ y≫π₂ : q→p.  Book §2.143. -/

/-- **§2.143 entire**: H = x≫π₁ ∩ y≫π₂ is entire when x°y ⊑ π₁π₂°.
    1 ⊑ (xx°)(yy°) ⊑ x(x°y)y° ⊑ x(π₁π₂°)y° = (xπ₁)(yπ₂)° = dom H. -/
theorem tab_UP_H_entire {a b p q : 𝒜}
    {π₁ : a ⟶ p} {π₂ : b ⟶ p} {x : q ⟶ a} {y : q ⟶ b}
    (hx : Map x) (hy : Map y)
    (hxy : x° ≫ y ⊑ π₁ ≫ π₂°) :
    Entire (x ≫ π₁ ∩ y ≫ π₂) := by
  -- Swap inter args so dom_inter gives id ∩ (x≫π₁)(y≫π₂)° (the form the chain proves)
  rw [Entire, Allegory.inter_comm (x ≫ π₁) (y ≫ π₂), dom_inter]
  apply le_antisymm (inter_lb_left _ _)
  apply le_inter (le_refl _)
  -- Goal: id_q ⊑ (x≫π₁) ≫ (y≫π₂)° = x≫π₁≫π₂°≫y°
  have hxx : Cat.id q ⊑ x ≫ x° := by
    have := hx.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have hyy : Cat.id q ⊑ y ≫ y° := by
    have := hy.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  -- 1 ⊑ (xx°)(yy°) = x(x°y)y° ⊑ x(π₁π₂°)y° = (xπ₁)(yπ₂)°
  have step1 : Cat.id q ⊑ (x ≫ x°) ≫ (y ≫ y°) :=
    le_trans hxx (by have h := comp_mono_left (x ≫ x°) hyy; rwa [Cat.comp_id] at h)
  have step2 : (x ≫ x°) ≫ (y ≫ y°) = x ≫ (x° ≫ y) ≫ y° := by simp [Cat.assoc]
  have step3 : x ≫ (x° ≫ y) ≫ y° ⊑ x ≫ (π₁ ≫ π₂°) ≫ y° :=
    comp_mono_left x (comp_mono_right hxy y°)
  have step4 : x ≫ (π₁ ≫ π₂°) ≫ y° = (x ≫ π₁) ≫ (y ≫ π₂)° := by
    rw [Allegory.recip_comp]; simp [Cat.assoc]
  exact step4 ▸ le_trans step1 (step2.symm ▸ step3)

/-- **§2.143 simple**: H = x≫π₁ ∩ y≫π₂ is simple when π₁°π₁ ∩ π₂°π₂ = id_p.
    H°H ⊑ (π₁°x°xπ₁) ∩ (π₂°y°yπ₂) ⊑ π₁°π₁ ∩ π₂°π₂ = 1. -/
theorem tab_UP_H_simple {a b p q : 𝒜}
    {π₁ : a ⟶ p} {π₂ : b ⟶ p}
    (hπ₁ : Map π₁) (hπ₂ : Map π₂)
    (htab : π₁° ≫ π₁ ∩ π₂° ≫ π₂ = Cat.id p)
    {x : q ⟶ a} {y : q ⟶ b}
    (hx : Map x) (hy : Map y) :
    Simple (x ≫ π₁ ∩ y ≫ π₂) := by
  rw [Simple, show (x ≫ π₁ ∩ y ≫ π₂)° = π₁° ≫ x° ∩ π₂° ≫ y° from by
        rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp]]
  -- Goal: (π₁°x° ∩ π₂°y°)(xπ₁ ∩ yπ₂) ⊑ 1_p
  -- Step 1: distribute using inter_lb bounds
  have step1 : (π₁° ≫ x° ∩ π₂° ≫ y°) ≫ (x ≫ π₁ ∩ y ≫ π₂) ⊑
      (π₁° ≫ x°) ≫ (x ≫ π₁) ∩ (π₂° ≫ y°) ≫ (y ≫ π₂) :=
    le_inter
      (le_trans (comp_mono_right (inter_lb_left _ _) _) (comp_mono_left _ (inter_lb_left _ _)))
      (le_trans (comp_mono_right (inter_lb_right _ _) _) (comp_mono_left _ (inter_lb_right _ _)))
  -- Step 2: each component ⊑ π₁°π₁ ⊑ id_p using Simple π₁ (from Map π₁)
  have h_fst : (π₁° ≫ x°) ≫ (x ≫ π₁) ⊑ Cat.id p := by
    have eq1 : (π₁° ≫ x°) ≫ (x ≫ π₁) = π₁° ≫ (x° ≫ x) ≫ π₁ := by simp [Cat.assoc]
    rw [eq1]
    have hreduce : π₁° ≫ (x° ≫ x) ≫ π₁ ⊑ π₁° ≫ π₁ :=
      le_trans (comp_mono_left _ (comp_mono_right hx.2 _)) (by rw [Cat.id_comp]; exact le_refl _)
    exact le_trans hreduce hπ₁.2
  have h_snd : (π₂° ≫ y°) ≫ (y ≫ π₂) ⊑ Cat.id p := by
    have eq2 : (π₂° ≫ y°) ≫ (y ≫ π₂) = π₂° ≫ (y° ≫ y) ≫ π₂ := by simp [Cat.assoc]
    rw [eq2]
    have hreduce : π₂° ≫ (y° ≫ y) ≫ π₂ ⊑ π₂° ≫ π₂ :=
      le_trans (comp_mono_left _ (comp_mono_right hy.2 _)) (by rw [Cat.id_comp]; exact le_refl _)
    exact le_trans hreduce hπ₂.2
  -- A ∩ B ⊑ A ⊑ id_p, so LHS ⊑ A ∩ B ⊑ id_p
  exact le_trans step1 (le_trans (inter_lb_left _ _) h_fst)

/-- **§2.143 forward UMP** (§2.143, §2.147): given tabulation of R, maps x,y with x°y ⊑ R,
    there is a unique mediating map h with h≫π₁°=x and h≫π₂°=y.
    Hypothesis `Map π₁°` (i.e. π₁≫π₁° ⊑ id_a = Simple(π₁°)) is needed for H≫π₁°=x. -/
theorem tabulation_UP_forward {a b p q : 𝒜}
    {π₁ : a ⟶ p} {π₂ : b ⟶ p} {R : a ⟶ b}
    (ht : Tabulates π₁ π₂ R)
    (hπ₁r : Map π₁°) (hπ₂r : Map π₂°)
    {x : q ⟶ a} {y : q ⟶ b}
    (hx : Map x) (hy : Map y)
    (hxy : x° ≫ y ⊑ R) :
    ∃ (h : q ⟶ p), Map h ∧ h ≫ π₁° = x ∧ h ≫ π₂° = y := by
  obtain ⟨hπ₁map, hπ₂map, hR, htab⟩ := ht
  rw [hR] at hxy
  have hH : Map (x ≫ π₁ ∩ y ≫ π₂) :=
    ⟨tab_UP_H_entire hx hy hxy, tab_UP_H_simple hπ₁map hπ₂map htab hx hy⟩
  refine ⟨x ≫ π₁ ∩ y ≫ π₂, hH, ?_, ?_⟩
  · apply map_order_discrete (map_comp hH hπ₁r) hx
    have hπ₁simp : π₁ ≫ π₁° ⊑ Cat.id a := by
      have := hπ₁r.2; rw [Simple, Allegory.recip_recip] at this; exact this
    have h1 : (x ≫ π₁ ∩ y ≫ π₂) ≫ π₁° ⊑ x ≫ Cat.id a := by
      refine le_trans (comp_mono_right (inter_lb_left _ _) π₁°) ?_
      rw [Cat.assoc]; exact comp_mono_left x hπ₁simp
    rwa [Cat.comp_id] at h1
  · apply map_order_discrete (map_comp hH hπ₂r) hy
    have hπ₂simp : π₂ ≫ π₂° ⊑ Cat.id b := by
      have := hπ₂r.2; rw [Simple, Allegory.recip_recip] at this; exact this
    have h2 : (x ≫ π₁ ∩ y ≫ π₂) ≫ π₂° ⊑ y ≫ Cat.id b := by
      refine le_trans (comp_mono_right (inter_lb_right _ _) π₂°) ?_
      rw [Cat.assoc]; exact comp_mono_left y hπ₂simp
    rwa [Cat.comp_id] at h2

/-! ### §2.147  Pullback universal property in Map(𝒜) -/

/-- **§2.147 pullback UMP**: the tabulation of fg° gives the pullback of f and g in Map(𝒜).
    Given maps x : q→a, y : q→b with x≫f = y≫g, there is a unique h : q→p in Map(𝒜)
    with h≫π₁°=x and h≫π₂°=y.
    Hypotheses `Map π₁°` and `Map π₂°` express π₁≫π₁° ⊑ id_a and π₂≫π₂° ⊑ id_b. -/
theorem tab_pullback_UMP {a b c p q : 𝒜} {f : a ⟶ c} {g : b ⟶ c}
    (hf : Map f) (hg : Map g)
    {π₁ : a ⟶ p} {π₂ : b ⟶ p}
    (ht : Tabulates π₁ π₂ (f ≫ g°))
    (hπ₁r : Map π₁°) (hπ₂r : Map π₂°)
    {x : q ⟶ a} {y : q ⟶ b}
    (hx : Map x) (hy : Map y)
    (hcone : x ≫ f = y ≫ g) :
    ∃ (hm : q ⟶ p), Map hm ∧ hm ≫ π₁° = x ∧ hm ≫ π₂° = y ∧
      ∀ hm' : q ⟶ p, Map hm' → hm' ≫ π₁° = x → hm' = hm := by
  -- Derive x°y ⊑ fg° from cone equation
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
      have h3 := comp_mono_right hx.2 (f ≫ g°)  -- (x°≫x)≫(f≫g°) ⊑ id_a≫(f≫g°)
      rw [Cat.id_comp] at h3; exact h3
    rw [s2] at s1; exact le_trans s1 s3
  obtain ⟨hm, hh_map, hhx, hhy⟩ := tabulation_UP_forward ht hπ₁r hπ₂r hx hy hxy
  exact ⟨hm, hh_map, hhx, hhy,
    fun hm' hh'_map hhx' =>
      (tabulation_UP_unique ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩
        hh_map hh'_map hhx hhx').symm⟩

/-! ### §2.147  Equalizer universal property in Map(𝒜)

  The equalizer of f,g : a→b is the splitting e : a→p of dom(f∩g).
  From `coreflexive_splits`: Map e, e≫e° = dom(f∩g), e°≫e = id_p.
  Map(e°): Entire(e°): e°≫e = id_p ✓; Simple(e°): e≫e° ⊑ id_a (dom_coreflexive).

  Given h : q→a with h≫f = h≫g, we show h°h ⊑ dom(f∩g) = e≫e°, then
  apply the §2.143 forward UP with the "tabulation" (e, e) of e≫e°. -/

/-- Map(e°) from a coreflexive splitting: e is a map, e≫e°=A⊑id, e°≫e=id_p. -/
theorem split_recip_is_map {a p : 𝒜} {e : a ⟶ p} {A : a ⟶ a}
    (he : Map e) (heeA : e ≫ e° = A) (hAid : A ⊑ Cat.id a) (he1 : e° ≫ e = Cat.id p) :
    Map e° := by
  constructor
  · -- Entire(e°): dom(e°) = id_p. dom(e°) = id_p ∩ e°(e°)° = id_p ∩ e°e = id_p.
    rw [Entire, dom, Allegory.recip_recip, he1, Allegory.inter_idem]
  · -- Simple(e°): (e°)°≫e° = e≫e° = A ⊑ id_a.
    rw [Simple, Allegory.recip_recip, heeA]; exact hAid

/-- **§2.147 equalizer UMP**: given the splitting e of dom(f∩g) and a map h with h≫f=h≫g,
    there is a unique map k with k≫e°=h. -/
theorem tab_equalizer_UMP {a b p q : 𝒜} {f g : a ⟶ b}
    (hf : Map f) (hg : Map g)
    {e : a ⟶ p}
    (he : Map e) (hee : e ≫ e° = dom (f ∩ g)) (he1 : e° ≫ e = Cat.id p)
    {h : q ⟶ a} (hh : Map h) (hcone : h ≫ f = h ≫ g) :
    ∃ (k : q ⟶ p), Map k ∧ k ≫ e° = h ∧
      ∀ k' : q ⟶ p, Map k' → k' ≫ e° = h → k' = k := by
  -- Map(e°): Simple(e°) from dom_coreflexive
  have her : Map e° := split_recip_is_map he hee (dom_coreflexive _) he1
  -- h°h ⊑ dom(f∩g) = e≫e°
  -- Step 1: h≫(f∩g) = h≫f  (since h simple: h(f∩g) = hf ∩ hg = hf ∩ hf = hf)
  have hfg_eq : h ≫ (f ∩ g) = h ≫ f := by
    have := simple_dist_inter hh.2 f g; rw [this, hcone, Allegory.inter_idem]
  -- Step 2: Map(h≫(f∩g)) = Map(h≫f)
  have hmap_hf : Map (h ≫ f) := map_comp hh hf
  -- Step 3: Entire(h≫(f∩g)): gives id_q ⊑ (h(f∩g))(h(f∩g))°
  have hent : Cat.id q ⊑ (h ≫ (f ∩ g)) ≫ (h ≫ (f ∩ g))° := by
    have := (hfg_eq ▸ hmap_hf).1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  -- Step 4: h°h ⊑ (f∩g)(f∩g)° via 1_q ⊑ h(f∩g)(f∩g)°h° and simplicity
  have hdomfg : h° ≫ h ⊑ (f ∩ g) ≫ (f ∩ g)° := by
    -- 1_q ⊑ h≫A≫h° where A=(f∩g)(f∩g)°, so h°h ⊑ h°(hAh°)h = (h°h)A(h°h) ⊑ A.
    have hA := hent
    -- (h(f∩g))(h(f∩g))° = h≫(f∩g)≫(f∩g)°≫h°
    have hexp : (h ≫ (f ∩ g)) ≫ (h ≫ (f ∩ g))° = h ≫ (f ∩ g) ≫ (f ∩ g)° ≫ h° := by
      rw [Allegory.recip_comp]; simp [Cat.assoc]
    rw [hexp] at hA
    -- h°h ⊑ h°(h(f∩g)(f∩g)°h°)h = (h°h)(f∩g)(f∩g)°(h°h)
    have step : h° ≫ h ⊑ (h° ≫ h) ≫ (f ∩ g) ≫ (f ∩ g)° ≫ (h° ≫ h) := by
      have s1 := comp_mono_left h° hA  -- h°≫id_q ⊑ h°≫h≫(f∩g)≫(f∩g)°≫h°
      rw [Cat.comp_id] at s1
      have s2 := comp_mono_right s1 h  -- h°≫h ⊑ (h°≫h≫(f∩g)≫(f∩g)°≫h°)≫h
      simp only [Cat.assoc] at s2 ⊢
      exact s2
    -- Now (h°h)(f∩g)(f∩g)°(h°h) ⊑ 1(f∩g)(f∩g)°1 = (f∩g)(f∩g)°
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
  -- Step 5: h°h ⊑ e≫e° = dom(f∩g) = 1_a ∩ (f∩g)(f∩g)°
  have hdomfg2 : h° ≫ h ⊑ e ≫ e° := by
    rw [hee]
    exact le_inter hh.2 hdomfg
  -- Step 6: (e, e) tabulates e≫e°
  have htab_e : Tabulates e e (e ≫ e°) :=
    ⟨he, he, rfl, by rw [Allegory.inter_idem, he1]⟩
  -- Step 7: apply §2.143 forward UP (x = h°, y = h ... wait, we need x°y ⊑ ee°)
  -- The equalizer UP is a special case: h : q→a, e° : p→a is the inclusion.
  -- We need k : q→p with k≫e° = h. This is exactly the UP for the "tabulation (e,e) of ee°"
  -- with x = h and y = h (both same): h°h ⊑ ee°.
  obtain ⟨k, hk_map, hke, _⟩ := tabulation_UP_forward htab_e her her hh hh hdomfg2
  exact ⟨k, hk_map, hke,
    fun k' hk'_map hk'e =>
      (tabulation_UP_unique htab_e hk_map hk'_map hke hk'e).symm⟩

end TabularLimits

/-! ## §2.148  𝒜 ≅ Rel(Map 𝒜) for tabular 𝒜

  In Freyd's §2.148, a tabular allegory 𝒜 is isomorphic to Rel(Map 𝒜) — the
  allegory of relations in its own category of maps.  The comparison functors are:

    Φ : 𝒜 → Rel(Map 𝒜),  R ↦ [tabulation span of R] = [(f, g) with Tabulates f g R]
    Ψ : Rel(Map 𝒜) → 𝒜,  [(f : a→c, g : b→c)] ↦ f ≫ g°

  In the common-TARGET tabulation convention of this file (f : a→c, g : b→c,
  R = f≫g°, f°≫f ∩ g°≫g = id_c), the key facts are:

    (i)  Ψ∘Φ = id: from Tabulates f g R one has f ≫ g° = R   [see tab_round_trip_rel]
    (ii) Φ∘Ψ on standard spans: (f,g) with f°≫f ∩ g°≫g = id_c self-tabulates
         f≫g°                                                    [see span_self_tabulates]
    (iii) Any two tabulations of the same R are related by a UNIQUE iso h : c'→c
         in Map(𝒜), provided all four recip-legs Map(f°)/Map(g°)/Map(f'°)/Map(g'°)
         hold.                                              [see tab_iso_unique_exists]

  A "jointly-monic span in Map(𝒜)" (an object of Rel(Map 𝒜)(a,b)) is exactly a
  `Tabulates`-triple (f,g,R) — the tabulation condition f°≫f ∩ g°≫g = id_c IS the
  jointly-monic condition of §2.141 for the pair (f, g) of maps with common target c.

  Note on Map(f°): The full unconditional iso in (iii) requires Map(f°) for every
  tabulation leg f (§2.144).  Since f°≫f = id_c (from tab_fof), Entire(f°) is free;
  the gap is Simple(f°) : f≫f° ⊑ id_a.  This is NOT automatic from Tabulates alone
  (see the "Note on Map(π₁°)" in the file header); it requires f to be a split monic
  (equivalently, an isomorphism between its source and the apex).  The TODO below is
  to lift this to an unconditional statement via an alternative representation. -/

section Rel148

variable {𝒜 : Type u} [TabularAllegory 𝒜]

/-- **§2.148 (J) — forward round-trip** (Ψ∘Φ = id): from a tabulation (f,g) of R,
    applying the backward functor Ψ recovers R.
    This is the trivial direction: Ψ(Φ(R)) = f ≫ g° = R. -/
theorem tab_round_trip_rel {a b c : 𝒜} {f : a ⟶ c} {g : b ⟶ c} {R : a ⟶ b}
    (ht : Tabulates f g R) : f ≫ g° = R :=
  ht.2.2.1.symm

/-- **§2.148 (K) — backward round-trip** (Φ∘Ψ identifies spans with tabulations):
    a pair (f : a→c, g : b→c) of maps satisfying the jointly-monic condition
    f°≫f ∩ g°≫g = id_c is itself a tabulation of f≫g°.

    Structurally: the objects of Rel(Map 𝒜)(a,b) are exactly the `Tabulates`-triples
    (f,g,R) — the jointly-monic condition f°≫f ∩ g°≫g = id_c (the tabulation
    condition in our common-TARGET convention) is the §2.141 jointly-monic condition
    for the span (f, g) in Map(𝒜). -/
theorem span_self_tabulates {a b c : 𝒜} {f : a ⟶ c} {g : b ⟶ c}
    (hf : Map f) (hg : Map g) (hjoint : f° ≫ f ∩ g° ≫ g = Cat.id c) :
    Tabulates f g (f ≫ g°) :=
  ⟨hf, hg, rfl, hjoint⟩

/-- **§2.148 (L) — unique iso between tabulations** (§2.144 with Map(f°) hypothesis):
    given two tabulations (f,g) and (f',g') of the same relation R, if all four
    recip-legs Map(f°), Map(g°), Map(f'°), Map(g'°) hold, there exists a UNIQUE map
    h : c' → c in Map(𝒜) with h ≫ f° = f'° and h ≫ g° = g'°.

    Existence: `tabulation_UP_forward` (§2.143) applied with x = f'°, y = g'° and
    the fact x°≫y = f'°° ≫ g'° = f'≫g'° = R ⊑ R.
    Uniqueness: `tabulation_UP_unique` (§2.143). -/
theorem tab_iso_unique_exists {a b c c' : 𝒜}
    {f : a ⟶ c} {g : b ⟶ c} {f' : a ⟶ c'} {g' : b ⟶ c'} {R : a ⟶ b}
    (ht : Tabulates f g R) (ht' : Tabulates f' g' R)
    (hfr : Map f°) (hgr : Map g°) (hf'r : Map f'°) (hg'r : Map g'°) :
    ∃ (h : c' ⟶ c), Map h ∧ h ≫ f° = f'° ∧ h ≫ g° = g'° ∧
      ∀ h' : c' ⟶ c, Map h' → h' ≫ f° = f'° → h' = h := by
  -- Key: x = f'° : c'→a, y = g'° : c'→b, x°≫y = f'≫g'° = R
  have hxy : f'°° ≫ g'° ⊑ R := by
    rw [Allegory.recip_recip, ht'.2.2.1.symm]; exact le_refl _
  obtain ⟨h, hh, hhf, hhg⟩ := tabulation_UP_forward ht hfr hgr hf'r hg'r hxy
  exact ⟨h, hh, hhf, hhg,
    fun h' hh' hf'eq => (tabulation_UP_unique ht hh hh' hhf hf'eq).symm⟩

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
  -- Goal: R° = g ≫ f°
  have : R = f ≫ g° := hR_eq
  calc R° = (f ≫ g°)° := by rw [this]
    _ = g ≫ f° := by rw [Allegory.recip_comp, Allegory.recip_recip]

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
    BLOCKER for (2)–(7): `Tabulates` uses common-TARGET convention (legs π₁ : a→p go
    INTO the apex), so `Map(π₁ : a→p)` holds but `Map(π₁° : p→a)` is not derivable.
    The book's §2.147 works because its tabulation has maps FROM the apex (common-source).
    Fix needed: extend `Tabulates`/`TabularAllegory` to record `Map(π₁°)` alongside `Map(π₁)`. -/

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

-- BOOK §2.212 TODO: HasImages (MapObj A) — splitting dom(f°) gives the image.
-- The Allows direction (f = (f≫e)≫e° via simple_dist_inter) is provable.
-- The minimality direction (image ≤ S when S allows f) needs Map(S.arr.val°) which
-- requires Simple(S.arr.val°) = S.arr.val≫S.arr.val° ⊑ id; not derivable from Map(S.arr.val)
-- in our common-TARGET convention.

-- BOOK §2.212 TODO: HasPullbacks (MapObj A) — tabulation of f≫g° gives the pullback.
-- Blocked: the pullback projections are π₁° : p→a; Map(π₁°) requires π₁≫π₁° ⊑ id_a
-- (Simple of π₁°) which is NOT provable from Map(π₁ : a→p) alone in our convention.

-- BOOK §2.212 TODO: HasBinaryProducts, PullbacksTransferCovers, RegularCategory,
-- HasSubobjectUnions, PreLogos — all depend on HasPullbacks above.

end MapPreLogos

end Freyd.Alg
