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

  **TODO §2.143**: universal property of pullbacks/equalizers requires the
  "forward" direction of §2.143 (tabulation UP): given maps x : q → a and
  y : q → b with x° ≫ y ⊑ R = fg°, produce a unique map h : q → p with
  h ≫ π₁° = x and h ≫ π₂° = y.  This needs the tabulation legs to satisfy
  π₁ ≫ π₁° = id_a (left-split, not just right-split π₁° ≫ π₁ = id_p),
  which does not follow from the tabulation axiom alone.
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

/-- R ⊑ dom R ≫ R.
    Proof: modular_le(1_a, R, R) with 1_a ≫ R = R and R ∩ R = R  (§2.121). -/
theorem le_dom_comp {a b : 𝒜} (R : a ⟶ b) : R ⊑ dom R ≫ R := by
  have h := modular_le (Cat.id a) R R
  rw [Cat.id_comp, Allegory.inter_idem, ← dom] at h
  exact h

/-- dom R ≫ R = R.  Follows from le_dom_comp and dom_coreflexive. -/
theorem dom_comp_eq {a b : 𝒜} (R : a ⟶ b) : dom R ≫ R = R :=
  le_antisymm
    (by have := comp_mono_right (dom_coreflexive R) R; rwa [Cat.id_comp] at this)
    (le_dom_comp R)

/-- dom(f ∩ g) ≫ f = f ∩ g   for any Map f.
    This uses dom_inter: dom(f∩g) = id ∩ g≫f° to bound ≫ f ⊑ g. -/
theorem dom_inter_comp {a b : 𝒜} {f g : a ⟶ b} (hf : Map f) : dom (f ∩ g) ≫ f = f ∩ g := by
  apply le_antisymm
  · have hf_le : dom (f ∩ g) ≫ f ⊑ f := by
      have := comp_mono_right (dom_coreflexive (f ∩ g)) f; rwa [Cat.id_comp] at this
    have hg_le : dom (f ∩ g) ≫ f ⊑ g := by
      -- dom(f∩g) = id ∩ g≫f°, so dom(f∩g)≫f ⊑ (g≫f°)≫f = g≫(f°f) ⊑ g≫id = g.
      rw [dom_inter]
      have h2 : (g ≫ f°) ≫ f ⊑ g := by
        rw [Cat.assoc]; have := comp_mono_left g hf.2; rwa [Cat.comp_id] at this
      exact le_trans (comp_mono_right (inter_lb_right _ _) f) h2
    exact le_inter hf_le hg_le
  · exact le_trans (le_dom_comp (f ∩ g)) (comp_mono_left _ (inter_lb_left f g))

/-- dom(f ∩ g) ≫ g = f ∩ g   for any Map g.  By symmetry of ∩. -/
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

/-- **§2.14**: Map(𝒜) is a category.
    Priority 0 so it does not shadow `Allegory.toCat` when 𝒜 appears directly. -/
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

/-! ### Tabulation lemmas -/

/-- f° ≫ f = id_c (apex identity) for first leg of a tabulation. -/
theorem tab_fof {a b c : 𝒜} {f : a ⟶ c} {g : b ⟶ c} {R : a ⟶ b}
    (ht : Tabulates f g R) : f° ≫ f = Cat.id c :=
  le_antisymm ht.1.2 (ht.2.2.2 ▸ inter_lb_left _ _)

/-- g° ≫ g = id_c (apex identity) for second leg of a tabulation. -/
theorem tab_gog {a b c : 𝒜} {f : a ⟶ c} {g : b ⟶ c} {R : a ⟶ b}
    (ht : Tabulates f g R) : g° ≫ g = Cat.id c :=
  le_antisymm ht.2.1.2 (ht.2.2.2 ▸ inter_lb_right _ _)

/-! ### §2.147  Pullback cone equation

  The pullback of f : a → c, g : b → c is built by tabulating fg°:
  legs π₁ : a → p, π₂ : b → p with fg° = π₁≫π₂° and π₁°π₁ ∩ π₂°π₂ = 1_p.
  Projections are π₁° : p → a and π₂° : p → b.

  Proof of π₁°f = π₂°g:
  • Key: π₁°≫(f≫g°)=π₂° [fg°=π₁π₂°, π₁°π₁=1].
  • Key: π₂°≫(g≫f°)=π₁° [recip of above, π₂°π₂=1].
  • π₁°f = π₂°g(f°f) ⊑ π₂°g  [Simple f].
  • π₂°g = π₁°f(g°g) ⊑ π₁°f  [Simple g].
-/

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
  · -- π₁°f ⊑ π₂°g: π₁°f = π₂°gf°f ⊑ π₂°g (Simple f: f°f ⊑ id)
    calc π₁° ≫ f
        = (π₂° ≫ g ≫ f°) ≫ f := by rw [hπ₂gf]
      _ = π₂° ≫ g ≫ (f° ≫ f) := by simp [Cat.assoc]
      _ ⊑ π₂° ≫ g ≫ Cat.id c  := comp_mono_left _ (comp_mono_left _ hf.2)
      _ = π₂° ≫ g              := by rw [Cat.comp_id]
  · -- π₂°g ⊑ π₁°f: π₂°g = π₁°fg°g ⊑ π₁°f (Simple g: g°g ⊑ id)
    calc π₂° ≫ g
        = (π₁° ≫ f ≫ g°) ≫ g := by rw [hπ₁fg]
      _ = π₁° ≫ f ≫ (g° ≫ g) := by simp [Cat.assoc]
      _ ⊑ π₁° ≫ f ≫ Cat.id c  := comp_mono_left _ (comp_mono_left _ hg.2)
      _ = π₁° ≫ f              := by rw [Cat.comp_id]

-- BOOK §2.143 TODO: Pullback universal property.
-- Given maps x : q → a, y : q → b with x ≫ f = y ≫ g, the condition x° ≫ y ⊑ fg°
-- follows (since x°yg = x°xf ⊑ f from Simple x, then left-compose with g°).
-- Then §2.143 forward gives ∃! map h : q → p with h ≫ π₁° = x and h ≫ π₂° = y.
-- §2.143 forward requires π₁ ≫ π₁° = id_a (the legs to be "entire as maps"),
-- which is not provided by the tabulation axiom alone.

/-! ### §2.147  Equalizer cone equation

  The equalizer of f, g : a → b is built by splitting dom(f∩g) : a→a:
  coreflexive_splits gives a map e : a → p with
    e ≫ e° = dom(f ∩ g)   and   e° ≫ e = id_p.
  Equalizer inclusion: e° : p → a.

  Cone equation e°f = e°g:
  • e≫(e°≫f) = dom(f∩g)≫f = f∩g  [dom_inter_comp hf]
  • e≫(e°≫g) = dom(f∩g)≫g = f∩g  [dom_inter_comp_right hg]
  • So e≫(e°f) = e≫(e°g); cancel e via e°e=id_p.
-/

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
  -- Cancel e: pre-compose with e° and use e°e=id.
  have key := congrArg (e° ≫ ·) (hef.trans heg.symm)
  simp only [← Cat.assoc, he1, Cat.id_comp] at key
  exact key

-- BOOK §2.147 TODO: Equalizer universal property.
-- Given a map h : q → a with h ≫ f = h ≫ g, show h° ≫ h ⊑ dom(f∩g), then
-- §2.143 forward gives ∃! map k : q → p with k ≫ e° = h.

/-! ### §2.147  Cover characterization -/

/-- **§2.147**: In a tabular allegory, g : a → b is a cover iff Entire(g°).
    (g is a cover iff 1_b ⊑ g° ≫ g, which is exactly Entire(g°).) -/
theorem cover_iff_recip_entire {a b : 𝒜} (g : a ⟶ b) :
    Cat.id b ⊑ g° ≫ g ↔ Entire g° := by
  simp only [Entire, dom, Allegory.recip_recip]
  constructor
  · intro h
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) h)
  · intro h
    calc Cat.id b = Cat.id b ∩ g° ≫ g := h.symm
      _ ⊑ g° ≫ g := inter_lb_right _ _

end TabularLimits

end Freyd.Alg
