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

  **BOOK §2.148 TODO**: 𝒜 ≅ Rel(Map 𝒜) for tabular 𝒜.  Needs a functor
  Map(𝒜) → 𝒜 sending (x : a → b in Map(𝒜)) to x (as a relation), and the
  inverse sending R : a → b to the tabulation — which requires constructing
  objects of Map(𝒜) from the tabulation apex.  Deferred: needs a universe-level
  packaging of `MapObj` as a category with the tabulation functor.
-/

import Fredy.S2_1
import Fredy.S2_22b

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

end Freyd.Alg
