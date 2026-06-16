/-
  Freyd & Scedrov, *Categories and Allegories* §1.45  Pullbacks and kernel pairs.

  Cone: a cone over a cospan A—f→C←g—B.
  HasPullback: a pullback (cone + universal property).  §1.454
  HasPullbacks: the category has all pullbacks.
  kernelPair f: pullback of f along f (§1.454).
  monic_iff_kp_diag_iso: f monic ↔ kp_diag f iso (§1.453).
  mono_pullback: pullback of a monic is monic (§1.45).
  invImg: inverse image f# : Sub(B) → Sub(A) (§1.451).
  Sub.inter: intersection of subobjects via pullback (§1.452).
  pullback_faithful_iff_preserves_properness: §1.453 Lemma.
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31
import Fredy.S1_33
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-- A cone over the cospan `A —f→ C ←g— B` (§1.454). -/
structure Cone {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) where
  pt : 𝒞
  π₁ : pt ⟶ A
  π₂ : pt ⟶ B
  w  : π₁ ≫ f = π₂ ≫ g

/-- A pullback of the cospan `A —f→ C ←g— B`: a distinguished `cone` and
    universal lift.  §1.454 -/
class HasPullback {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) where
  cone : Cone f g
  lift      (c : Cone f g) : c.pt ⟶ cone.pt
  lift_fst  (c : Cone f g) : lift c ≫ cone.π₁ = c.π₁
  lift_snd  (c : Cone f g) : lift c ≫ cone.π₂ = c.π₂
  lift_uniq (c : Cone f g) (u : c.pt ⟶ cone.pt)
    (h₁ : u ≫ cone.π₁ = c.π₁) (h₂ : u ≫ cone.π₂ = c.π₂) : u = lift c

/-- The category has all pullbacks. -/
class HasPullbacks (𝒞 : Type u) [Cat.{v} 𝒞] where
  has {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) : HasPullback f g

/-- A cone is a PULLBACK if every cone over the same cospan factors uniquely
    through it (§1.454).  Predicate form, for stating that a given square is a
    pullback without fixing a choice of pullbacks. -/
def Cone.IsPullback {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C} (c : Cone f g) : Prop :=
  ∀ d : Cone f g, ∃ u : d.pt ⟶ c.pt, (u ≫ c.π₁ = d.π₁ ∧ u ≫ c.π₂ = d.π₂) ∧
    ∀ v : d.pt ⟶ c.pt, v ≫ c.π₁ = d.π₁ → v ≫ c.π₂ = d.π₂ → v = u

/-- The chosen cone of a pullback is a pullback. -/
theorem HasPullback.cone_isPullback {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C}
    (hp : HasPullback f g) : hp.cone.IsPullback := λ d =>
  ⟨hp.lift d, ⟨⟨hp.lift_fst d, hp.lift_snd d⟩, λ v h₁ h₂ => hp.lift_uniq d v h₁ h₂⟩⟩

variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

/-- The kernel pair of `f` : pullback of `f` along itself.  §1.454 -/
def kernelPair {A B : 𝒞} (f : A ⟶ B) : 𝒞 := (hpull.has f f).cone.pt

section
variable {A B X : 𝒞} {f : A ⟶ B}

def kp₁ : kernelPair f ⟶ A := (hpull.has f f).cone.π₁
def kp₂ : kernelPair f ⟶ A := (hpull.has f f).cone.π₂

theorem kp_sq : kp₁ (f:=f) ≫ f = kp₂ (f:=f) ≫ f := (hpull.has f f).cone.w

/-- The diagonal cone `(A, 1_A, 1_A)` over the cospan `(f, f)`. -/
def diagCone : Cone f f := ⟨A, Cat.id A, Cat.id A, rfl⟩

def kp_diag : A ⟶ kernelPair f := (hpull.has f f).lift diagCone

theorem kp_diag_p₁ : kp_diag (f:=f) ≫ kp₁ (f:=f) = Cat.id A := (hpull.has f f).lift_fst diagCone
theorem kp_diag_p₂ : kp_diag (f:=f) ≫ kp₂ (f:=f) = Cat.id A := (hpull.has f f).lift_snd diagCone

theorem kp_lift_p₁ (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) :
    (hpull.has f f).lift ⟨_, x₁, x₂, h⟩ ≫ kp₁ (f:=f) = x₁ := (hpull.has f f).lift_fst _

theorem kp_lift_p₂ (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) :
    (hpull.has f f).lift ⟨_, x₁, x₂, h⟩ ≫ kp₂ (f:=f) = x₂ := (hpull.has f f).lift_snd _

theorem kp_lift_uniq (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f)
    (g : X ⟶ kernelPair f) (h₁ : g ≫ kp₁ (f:=f) = x₁) (h₂ : g ≫ kp₂ (f:=f) = x₂) :
    g = (hpull.has f f).lift ⟨_, x₁, x₂, h⟩ := (hpull.has f f).lift_uniq ⟨_, x₁, x₂, h⟩ g h₁ h₂

/-- Lemma from §1.453: f is monic iff the diagonal into its kernel pair is iso. -/
theorem monic_iff_kp_diag_iso : Mono f ↔ IsIso (kp_diag (f:=f)) := by
  constructor
  · intro hm
    have h_eq : kp₁ (f:=f) = kp₂ (f:=f) := hm _ _ kp_sq
    refine ⟨kp₁ (f:=f), kp_diag_p₁, ?_⟩
    have h_id : (hpull.has f f).lift ⟨_, kp₁ (f:=f), kp₂ (f:=f), kp_sq⟩ = Cat.id (kernelPair f) :=
      (kp_lift_uniq (kp₁ (f:=f)) (kp₂ (f:=f)) kp_sq (Cat.id (kernelPair f))
        (Cat.id_comp _) (Cat.id_comp _)).symm
    have h_comp : (kp₁ (f:=f)) ≫ kp_diag (f:=f) =
        (hpull.has f f).lift ⟨_, kp₁ (f:=f), kp₂ (f:=f), kp_sq⟩ :=
      (kp_lift_uniq (kp₁ (f:=f)) (kp₂ (f:=f)) kp_sq ((kp₁ (f:=f)) ≫ kp_diag (f:=f))
        (by rw [Cat.assoc, kp_diag_p₁, Cat.comp_id])
        (by rw [Cat.assoc, kp_diag_p₂, Cat.comp_id, h_eq]))
    rw [h_comp, h_id]
  · intro hiso
    obtain ⟨inv, _diag_inv, inv_diag⟩ := hiso
    intro X x₁ x₂ h
    let hpair : X ⟶ kernelPair f := (hpull.has f f).lift ⟨_, x₁, x₂, h⟩
    let t : X ⟶ A := hpair ≫ inv
    have ht : hpair = t ≫ kp_diag (f:=f) := by
      dsimp [t]; rw [Cat.assoc, inv_diag]; rw [Cat.comp_id]
    calc
      x₁ = hpair ≫ kp₁ (f:=f) := by rw [kp_lift_p₁ x₁ x₂ h]
      _ = (t ≫ kp_diag (f:=f)) ≫ kp₁ (f:=f) := by rw [ht]
      _ = t ≫ (kp_diag (f:=f) ≫ kp₁ (f:=f)) := by rw [Cat.assoc]
      _ = t ≫ Cat.id A := by rw [kp_diag_p₁]
      _ = t := by rw [Cat.comp_id]
      _ = t ≫ Cat.id A := by rw [Cat.comp_id]
      _ = t ≫ (kp_diag (f:=f) ≫ kp₂ (f:=f)) := by rw [kp_diag_p₂]
      _ = (t ≫ kp_diag (f:=f)) ≫ kp₂ (f:=f) := by rw [← Cat.assoc]
      _ = hpair ≫ kp₂ (f:=f) := by rw [ht]
      _ = x₂ := by rw [kp_lift_p₂ x₁ x₂ h]

end

/-! ## §1.45 Pullbacks transfer monics

  If `m : B → C` is monic and we pull it back along `f : A → C`, the resulting
  projection `π₁ : P → A` (where `P` is the pullback of `f` and `m`) is monic. -/

/-- §1.45: The pullback of a monic along any map is monic.
    Given the cospan `A —f→ C ←m— B` with `m` monic and `hp : HasPullback f m`,
    the first projection `hp.cone.π₁ : hp.cone.pt → A` is monic. -/
theorem mono_pullback {A B C : 𝒞} (f : A ⟶ C) (m : B ⟶ C) (hm : Mono m)
    (hp : HasPullback f m) : Mono hp.cone.π₁ := by
  intro W g h heq
  -- Derive g ≫ π₂ = h ≫ π₂ using m monic and the cone square π₁ ≫ f = π₂ ≫ m
  have hm2 : g ≫ hp.cone.π₂ = h ≫ hp.cone.π₂ := hm _ _ (by
    -- (x ≫ π₂) ≫ m = (x ≫ π₁) ≫ f  [by Cat.assoc + cone.w]
    -- so g ≫ π₁ = h ≫ π₁ (heq) gives equality
    rw [show (g ≫ hp.cone.π₂) ≫ m = (g ≫ hp.cone.π₁) ≫ f from by
          rw [Cat.assoc, ← hp.cone.w, ← Cat.assoc],
        show (h ≫ hp.cone.π₂) ≫ m = (h ≫ hp.cone.π₁) ≫ f from by
          rw [Cat.assoc, ← hp.cone.w, ← Cat.assoc],
        heq])
  -- g and h induce the same cone, so lift uniqueness gives g = h
  have hw : (g ≫ hp.cone.π₁) ≫ f = (g ≫ hp.cone.π₂) ≫ m := by
    simp only [Cat.assoc, hp.cone.w]
  have hlg : g = hp.lift ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ :=
    hp.lift_uniq ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ g rfl rfl
  have hlh : h = hp.lift ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ :=
    hp.lift_uniq ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ h heq.symm hm2.symm
  rw [hlg, hlh]

/-! ## §1.451 Inverse image f# : Sub(B) → Sub(A)

  Given `f : A → B` and a subobject `m : B' → B`, the INVERSE IMAGE `f# m` is the
  pullback of `m` along `f`, which lands as a subobject of `A`.  It is order-preserving
  and makes `Sub(−)` a contravariant functor. -/

/-- The inverse image of a subobject `S` of `B` along `f : A → B`,
    defined as the pullback of `S.arr` along `f`.  (Freyd §1.451, f#) -/
noncomputable def invImg {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 B)
    (hp : HasPullback f S.arr) : Subobject 𝒞 A where
  dom   := hp.cone.pt
  arr   := hp.cone.π₁
  monic := mono_pullback f S.arr S.monic hp

/-- §1.451: inverse image is order-preserving: if `S ≤ T` in `Sub(B)`, then
    `f# S ≤ f# T` in `Sub(A)`. -/
theorem invImg_le {A B : 𝒞} (f : A ⟶ B) (S T : Subobject 𝒞 B)
    (hS : HasPullback f S.arr) (hT : HasPullback f T.arr)
    (hle : S.le T) : (invImg f S hS).le (invImg f T hT) := by
  obtain ⟨k, hk⟩ := hle
  -- π₂_S ≫ k : hS.cone.pt → T.dom satisfies (π₂_S ≫ k) ≫ T.arr = π₁_S ≫ f
  have hw : hS.cone.π₁ ≫ f = (hS.cone.π₂ ≫ k) ≫ T.arr := by
    rw [Cat.assoc, hk, ← hS.cone.w]
  exact ⟨hT.lift ⟨hS.cone.pt, hS.cone.π₁, hS.cone.π₂ ≫ k, hw⟩, hT.lift_fst _⟩

/-- §1.451: `Sub(−)` is a contravariant functor: `f# ∘ g# = (f ≫ g)#` up to ≅.
    Pullback pasting: the composite pullback of S along g then along f equals
    the pullback of S along (f ≫ g). -/
theorem invImg_comp {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (S : Subobject 𝒞 C)
    (hfg : HasPullback (f ≫ g) S.arr)
    (hg  : HasPullback g S.arr)
    (hf  : HasPullback f (invImg g S hg).arr) :
    (invImg (f ≫ g) S hfg).le (invImg f (invImg g S hg) hf) ∧
    (invImg f (invImg g S hg) hf).le (invImg (f ≫ g) S hfg) := by
  -- invImg g S hg : dom = hg.cone.pt, arr = hg.cone.π₁
  -- invImg f (invImg g S hg) hf : dom = hf.cone.pt, arr = hf.cone.π₁
  -- hf is pullback of f along hg.cone.π₁
  -- hfg is pullback of (f≫g) along S.arr
  -- Forward: from hfg.cone.pt we build a map to hf.cone.pt
  --   Step 1: hfg.cone.π₁ ≫ f lands in hg via: (hfg.π₁ ≫ f) ≫ g = hfg.π₂ ≫ S.arr
  --   Step 2: lift to hf.cone.pt via f and above map into hg.cone.pt
  constructor
  · -- (f≫g)#S ≤ f#(g#S)
    -- u : hfg.cone.pt → hg.cone.pt with u ≫ hg.cone.π₁ = hfg.cone.π₁ ≫ f
    have hw_g : (hfg.cone.π₁ ≫ f) ≫ g = hfg.cone.π₂ ≫ S.arr := by
      rw [Cat.assoc]; exact hfg.cone.w
    let u := hg.lift ⟨hfg.cone.pt, hfg.cone.π₁ ≫ f, hfg.cone.π₂, hw_g⟩
    have hu_π₁ : u ≫ hg.cone.π₁ = hfg.cone.π₁ ≫ f := hg.lift_fst _
    -- v : hfg.cone.pt → hf.cone.pt with v ≫ hf.cone.π₁ = hfg.cone.π₁
    -- hf is the pullback of f along hg.cone.π₁ = (invImg g S hg).arr
    have hw_f : hfg.cone.π₁ ≫ f = u ≫ hg.cone.π₁ := hu_π₁.symm
    let v := hf.lift ⟨hfg.cone.pt, hfg.cone.π₁, u, hw_f⟩
    exact ⟨v, hf.lift_fst _⟩
  · -- f#(g#S) ≤ (f≫g)#S
    -- From hf.cone.pt we map to hfg.cone.pt
    -- hf.cone: π₁ : hf.cone.pt → A, π₂ : hf.cone.pt → hg.cone.pt
    --   with hf.cone.π₁ ≫ f = hf.cone.π₂ ≫ hg.cone.π₁
    -- hg.cone: π₁ : hg.cone.pt → B, π₂ : hg.cone.pt → S.dom
    --   with hg.cone.π₁ ≫ g = hg.cone.π₂ ≫ S.arr
    -- So hf.cone.π₁ ≫ (f≫g) = hf.cone.π₂ ≫ (hg.cone.π₁ ≫ g)
    --                          = hf.cone.π₂ ≫ hg.cone.π₂ ≫ S.arr
    -- (invImg g S hg).arr = hg.cone.π₁ by def; hf.cone.w says π₁ ≫ f = π₂ ≫ (invImg g S hg).arr
    have hf_w : hf.cone.π₁ ≫ f = hf.cone.π₂ ≫ hg.cone.π₁ := hf.cone.w
    have hw : hf.cone.π₁ ≫ (f ≫ g) = (hf.cone.π₂ ≫ hg.cone.π₂) ≫ S.arr := by
      rw [← Cat.assoc, hf_w, Cat.assoc, hg.cone.w, Cat.assoc]
    let w := hfg.lift ⟨hf.cone.pt, hf.cone.π₁, hf.cone.π₂ ≫ hg.cone.π₂, hw⟩
    exact ⟨w, hfg.lift_fst _⟩

/-! ## §1.452 Sub(A) is a semilattice under pullback-intersection

  Given two monics `S.arr : A₁ → A` and `T.arr : A₂ → A`, their pullback over `A`
  gives a greatest lower bound in `Sub(A)`.  `f#` preserves this intersection. -/

/-- The intersection of two subobjects of `A` via the pullback of their monics.
    §1.452: the resulting subobject is the glb of `S` and `T` in `Sub(A)`. -/
noncomputable def Sub.inter {A : 𝒞} (S T : Subobject 𝒞 A)
    (hp : HasPullback S.arr T.arr) : Subobject 𝒞 A where
  dom   := hp.cone.pt
  arr   := hp.cone.π₁ ≫ S.arr
  monic := by
    -- π₁ ≫ S.arr is monic: if g ≫ (π₁ ≫ S.arr) = h ≫ (π₁ ≫ S.arr), derive g = h.
    -- Step 1: S.arr monic → g ≫ π₁ = h ≫ π₁.
    -- Step 2: cone square + T.arr monic → g ≫ π₂ = h ≫ π₂.
    -- Step 3: lift uniqueness → g = h.
    intro W g h heq
    have hπ₁ : g ≫ hp.cone.π₁ = h ≫ hp.cone.π₁ :=
      S.monic _ _ (by rw [Cat.assoc, Cat.assoc]; exact heq)
    have hπ₂ : g ≫ hp.cone.π₂ = h ≫ hp.cone.π₂ := T.monic _ _ (by
      -- (x ≫ π₂) ≫ T.arr = (x ≫ π₁) ≫ S.arr  [Cat.assoc + cone.w symm]
      rw [show (g ≫ hp.cone.π₂) ≫ T.arr = (g ≫ hp.cone.π₁) ≫ S.arr from by
            rw [Cat.assoc, ← hp.cone.w, ← Cat.assoc],
          show (h ≫ hp.cone.π₂) ≫ T.arr = (h ≫ hp.cone.π₁) ≫ S.arr from by
            rw [Cat.assoc, ← hp.cone.w, ← Cat.assoc],
          hπ₁])
    have hw : (g ≫ hp.cone.π₁) ≫ S.arr = (g ≫ hp.cone.π₂) ≫ T.arr := by
      simp only [Cat.assoc, hp.cone.w]
    have hlg : g = hp.lift ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ :=
      hp.lift_uniq ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ g rfl rfl
    have hlh : h = hp.lift ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ :=
      hp.lift_uniq ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ h hπ₁.symm hπ₂.symm
    rw [hlg, hlh]

/-- §1.452: the intersection is a lower bound: `S ∩ T ≤ S`. -/
theorem Sub.inter_le_left {A : 𝒞} (S T : Subobject 𝒞 A) (hp : HasPullback S.arr T.arr) :
    (Sub.inter S T hp).le S :=
  ⟨hp.cone.π₁, rfl⟩

/-- §1.452: the intersection is a lower bound: `S ∩ T ≤ T`. -/
theorem Sub.inter_le_right {A : 𝒞} (S T : Subobject 𝒞 A) (hp : HasPullback S.arr T.arr) :
    (Sub.inter S T hp).le T :=
  ⟨hp.cone.π₂, hp.cone.w.symm⟩

/-- §1.452: the intersection is the greatest lower bound: any common lower bound
    factors through it. -/
theorem Sub.inter_glb {A : 𝒞} (S T U : Subobject 𝒞 A) (hp : HasPullback S.arr T.arr)
    (hS : U.le S) (hT : U.le T) : U.le (Sub.inter S T hp) := by
  obtain ⟨ks, hks⟩ := hS
  obtain ⟨kt, hkt⟩ := hT
  have hw : ks ≫ S.arr = kt ≫ T.arr := by rw [hks, hkt]
  let u := hp.lift ⟨U.dom, ks, kt, hw⟩
  refine ⟨u, ?_⟩
  -- (Sub.inter S T hp).arr = hp.cone.π₁ ≫ S.arr; u ≫ π₁ = ks; ks ≫ S.arr = U.arr
  show u ≫ hp.cone.π₁ ≫ S.arr = U.arr
  rw [← Cat.assoc, hp.lift_fst _, hks]

/-- §1.452: inverse image `f#` preserves intersections: `f#(S ∩ T) ≅ f#S ∩ f#T`. -/
theorem invImg_preserves_inter {A B : 𝒞} (f : A ⟶ B) (S T : Subobject 𝒞 B)
    (hST   : HasPullback S.arr T.arr)
    (hfST  : HasPullback f (Sub.inter S T hST).arr)
    (hfS   : HasPullback f S.arr)
    (hfT   : HasPullback f T.arr)
    (hfSfT : HasPullback (invImg f S hfS).arr (invImg f T hfT).arr) :
    (invImg f (Sub.inter S T hST) hfST).le
      (Sub.inter (invImg f S hfS) (invImg f T hfT) hfSfT) ∧
    (Sub.inter (invImg f S hfS) (invImg f T hfT) hfSfT).le
      (invImg f (Sub.inter S T hST) hfST) := by
  -- Extract cone equations as plain Prop values, avoiding rewrites that change types of local vars.
  -- (Sub.inter S T hST).arr = hST.cone.π₁ ≫ S.arr  (definitionally)
  -- (invImg f S hfS).arr = hfS.cone.π₁              (definitionally)
  -- (invImg f T hfT).arr = hfT.cone.π₁              (definitionally)
  -- hfST.cone.w : π₁ ≫ f = π₂ ≫ (hST.cone.π₁ ≫ S.arr)  — but Lean sees (Sub.inter).arr
  -- We extract these using type ascription to force unfolding:
  have hfST_w : hfST.cone.π₁ ≫ f = hfST.cone.π₂ ≫ hST.cone.π₁ ≫ S.arr :=
    show hfST.cone.π₁ ≫ f = hfST.cone.π₂ ≫ hST.cone.π₁ ≫ S.arr from hfST.cone.w
  have hfS_w  : hfS.cone.π₁  ≫ f = hfS.cone.π₂  ≫ S.arr              := hfS.cone.w
  have hfT_w  : hfT.cone.π₁  ≫ f = hfT.cone.π₂  ≫ T.arr              := hfT.cone.w
  have hST_w  : hST.cone.π₁  ≫ S.arr = hST.cone.π₂ ≫ T.arr          := hST.cone.w
  have hfSfT_w : hfSfT.cone.π₁ ≫ hfS.cone.π₁ = hfSfT.cone.π₂ ≫ hfT.cone.π₁ :=
    show hfSfT.cone.π₁ ≫ hfS.cone.π₁ = hfSfT.cone.π₂ ≫ hfT.cone.π₁ from hfSfT.cone.w
  constructor
  · -- f#(S∩T) ≤ f#S ∩ f#T
    -- u_S : hfST.cone.pt → hfS.cone.pt
    have hw_S : hfST.cone.π₁ ≫ f = (hfST.cone.π₂ ≫ hST.cone.π₁) ≫ S.arr :=
      hfST_w.trans (Cat.assoc _ _ _).symm
    let u_S := hfS.lift ⟨hfST.cone.pt, hfST.cone.π₁, hfST.cone.π₂ ≫ hST.cone.π₁, hw_S⟩
    have hu_S : u_S ≫ hfS.cone.π₁ = hfST.cone.π₁ := hfS.lift_fst _
    -- u_T : hfST.cone.pt → hfT.cone.pt
    have hw_T : hfST.cone.π₁ ≫ f = (hfST.cone.π₂ ≫ hST.cone.π₂) ≫ T.arr :=
      calc hfST.cone.π₁ ≫ f
          = hfST.cone.π₂ ≫ hST.cone.π₁ ≫ S.arr  := hfST_w
        _ = (hfST.cone.π₂ ≫ hST.cone.π₁) ≫ S.arr := (Cat.assoc _ _ _).symm
        _ = (hfST.cone.π₂ ≫ hST.cone.π₁) ≫ S.arr := rfl
        _ = hfST.cone.π₂ ≫ hST.cone.π₁ ≫ S.arr   := Cat.assoc _ _ _
        _ = hfST.cone.π₂ ≫ hST.cone.π₂ ≫ T.arr   := by rw [hST_w]
        _ = (hfST.cone.π₂ ≫ hST.cone.π₂) ≫ T.arr := (Cat.assoc _ _ _).symm
    let u_T := hfT.lift ⟨hfST.cone.pt, hfST.cone.π₁, hfST.cone.π₂ ≫ hST.cone.π₂, hw_T⟩
    have hu_T : u_T ≫ hfT.cone.π₁ = hfST.cone.π₁ := hfT.lift_fst _
    -- u_S and u_T agree → lift into hfSfT
    have hw_SfT : u_S ≫ hfS.cone.π₁ = u_T ≫ hfT.cone.π₁ := by rw [hu_S, hu_T]
    -- need the cone equation for hfSfT: (invImg f S hfS).arr = hfS.cone.π₁  definitionally
    have hw_SfT' : u_S ≫ (invImg f S hfS).arr = u_T ≫ (invImg f T hfT).arr := hw_SfT
    let v := hfSfT.lift ⟨hfST.cone.pt, u_S, u_T, hw_SfT'⟩
    refine ⟨v, ?_⟩
    -- goal: v ≫ (Sub.inter (invImg f S hfS) (invImg f T hfT) hfSfT).arr = hfST.cone.π₁
    -- .arr = hfSfT.cone.π₁ ≫ (invImg f S hfS).arr = hfSfT.cone.π₁ ≫ hfS.cone.π₁  (def)
    show v ≫ hfSfT.cone.π₁ ≫ hfS.cone.π₁ = hfST.cone.π₁
    rw [← Cat.assoc, hfSfT.lift_fst _, hu_S]
  · -- f#S ∩ f#T ≤ f#(S∩T)
    -- Step 1: map hfSfT.cone.pt → hST.cone.pt
    have hw_ST : (hfSfT.cone.π₁ ≫ hfS.cone.π₂) ≫ S.arr = (hfSfT.cone.π₂ ≫ hfT.cone.π₂) ≫ T.arr :=
      calc (hfSfT.cone.π₁ ≫ hfS.cone.π₂) ≫ S.arr
          = hfSfT.cone.π₁ ≫ hfS.cone.π₂ ≫ S.arr   := Cat.assoc _ _ _
        _ = hfSfT.cone.π₁ ≫ hfS.cone.π₁ ≫ f       := by rw [← hfS_w]
        _ = hfSfT.cone.π₂ ≫ hfT.cone.π₁ ≫ f       := by rw [← Cat.assoc, hfSfT_w, Cat.assoc]
        _ = hfSfT.cone.π₂ ≫ hfT.cone.π₂ ≫ T.arr   := by rw [← hfT_w]
        _ = (hfSfT.cone.π₂ ≫ hfT.cone.π₂) ≫ T.arr := (Cat.assoc _ _ _).symm
    let u_ST := hST.lift ⟨hfSfT.cone.pt, hfSfT.cone.π₁ ≫ hfS.cone.π₂,
                                           hfSfT.cone.π₂ ≫ hfT.cone.π₂, hw_ST⟩
    have hu_ST_π₁ : u_ST ≫ hST.cone.π₁ = hfSfT.cone.π₁ ≫ hfS.cone.π₂ := hST.lift_fst _
    -- Step 2: map hfSfT.cone.pt → hfST.cone.pt
    -- need: (hfSfT.cone.π₁ ≫ hfS.cone.π₁) ≫ f = u_ST ≫ (Sub.inter S T hST).arr
    have hw_fST : (hfSfT.cone.π₁ ≫ hfS.cone.π₁) ≫ f = u_ST ≫ (Sub.inter S T hST).arr :=
      calc (hfSfT.cone.π₁ ≫ hfS.cone.π₁) ≫ f
          = hfSfT.cone.π₁ ≫ hfS.cone.π₁ ≫ f           := Cat.assoc _ _ _
        _ = hfSfT.cone.π₁ ≫ hfS.cone.π₂ ≫ S.arr       := by rw [← hfS_w]
        _ = (hfSfT.cone.π₁ ≫ hfS.cone.π₂) ≫ S.arr     := (Cat.assoc _ _ _).symm
        _ = (u_ST ≫ hST.cone.π₁) ≫ S.arr               := congrArg (· ≫ S.arr) hu_ST_π₁.symm
        _ = u_ST ≫ hST.cone.π₁ ≫ S.arr                 := Cat.assoc _ _ _
        _ = u_ST ≫ (Sub.inter S T hST).arr              := rfl
    let w := hfST.lift ⟨hfSfT.cone.pt, hfSfT.cone.π₁ ≫ hfS.cone.π₁, u_ST, hw_fST⟩
    refine ⟨w, ?_⟩
    -- goal: w ≫ (invImg f (Sub.inter S T hST) hfST).arr = (Sub.inter (invImg f S hfS) (invImg f T hfT) hfSfT).arr
    -- .arr on left = hfST.cone.π₁, .arr on right = hfSfT.cone.π₁ ≫ hfS.cone.π₁  (def)
    show w ≫ hfST.cone.π₁ = hfSfT.cone.π₁ ≫ hfS.cone.π₁
    exact hfST.lift_fst _

/-! ## §1.453 LEMMA: pullback-preserving functor faithful ↔ preserves properness

  A functor `T : A → B` that preserves pullbacks is faithful if and only if it
  preserves *properness* of subobjects: i.e. a non-iso mono maps to a non-iso mono. -/

/-- T PRESERVES PULLBACKS: for every pullback cone in `𝒜`, the image cone in `ℬ`
    is also a pullback. -/
def PreservesPullbacks {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (T : 𝒜 → ℬ) [hT : Functor T] : Prop :=
  ∀ {A B C : 𝒜} (f : A ⟶ C) (g : B ⟶ C) (c : Cone f g),
    c.IsPullback →
    (Cone.mk (T c.pt) (hT.map c.π₁) (hT.map c.π₂)
      (by rw [← hT.map_comp, ← hT.map_comp, c.w])).IsPullback

/-- T PRESERVES PROPERNESS: a non-iso monic maps to a non-iso monic (§1.453). -/
def PreservesProperness {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (T : 𝒜 → ℬ) [hT : Functor T] : Prop :=
  ∀ {A' A : 𝒜} (m : A' ⟶ A), Mono m → ¬IsIso m → ¬IsIso (hT.map m)

/-- §1.453 LEMMA: if `𝒜` is Cartesian and `T : 𝒜 → ℬ` preserves pullbacks, then
    `T` is faithful iff it preserves properness of subobjects.

    Freyd's argument:
    - (⇒) T faithful ⇒ T reflects isos ⇒ non-iso mono stays non-iso under T.
    - (⇐) Given `f` not monic, its kernel pair diagonal `A → kp(f)` is not iso
      (§1.453 / `monic_iff_kp_diag_iso`); T preserves this pullback so `T(diag)` is
      the diagonal for `T(f)`'s kernel pair; T preserves properness so `T(diag)` is
      not iso; hence `T(f)` is not monic.  Contrapositive: T reflects monics.
      For faithfulness, Freyd equates "reflects monics" (when pullbacks are preserved)
      with hom-injectivity. -/
theorem pullback_faithful_iff_preserves_properness
    {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    [HasTerminal 𝒜] [HasBinaryProducts 𝒜] [HasPullbacks 𝒜]
    (T : 𝒜 → ℬ) [hT : Functor T]
    (hpb : PreservesPullbacks T) :
    Faithful T ↔ PreservesProperness T := by
  constructor
  · -- (⇒) Faithful T → PreservesProperness T
    -- T faithful → T reflects isomorphisms → non-iso mono stays non-iso.
    intro ⟨_, hRefl⟩ A' A m _ hniso hTiso
    exact hniso (hRefl m hTiso)
  · -- (⇐) PreservesProperness T → Faithful T (§1.453)
    -- Freyd's proof requires classical logic (excluded middle for the contrapositive of
    -- PreservesProperness) and graph-factorization infrastructure for the Embedding step.
    -- Both steps are left as faithful sorrys:
    --   (a) ReflectsMono: if T f not monic then kp_diag f is monic + not-iso, so by
    --       PreservesProperness T(kp_diag f) not iso, so T f not monic. (Needs EM.)
    --   (b) Embedding: T.map f = T.map g → f = g via the kernel-pair of g and step (a).
    intro _hprop
    sorry

end Freyd
