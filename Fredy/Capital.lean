/-
  Freyd & Scedrov, *Categories and Allegories* §1.525.

  "A pre-regular category is CAPITAL if every well-supported object is well-pointed.
   In a capital pre-regular category the terminator is projective."

  Projectivity of 1 (§1.524) means the representable functor Hom(1,−) preserves
  covers.  The elementary consequence: every well-supported A has a global
  element 1 → A.

-/

set_option linter.unusedSectionVars false

universe v u

class Cat.{w, z} (𝒞 : Type z) : Type (max z (w + 1)) where
  Hom     : 𝒞 → 𝒞 → Type w
  id      : (X : 𝒞) → Hom X X
  comp    : {X Y Z : 𝒞} → Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y : 𝒞} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : 𝒞} (f : Hom X Y), comp f (id Y) = f
  assoc   : ∀ {W X Y Z : 𝒞} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
              comp (comp f g) h = comp f (comp g h)

infixr:25 " ⟶ "  => Cat.Hom
infixr:80 " ≫ "  => Cat.comp

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

def Mono {X Y : 𝒞} (m : X ⟶ Y) : Prop :=
  ∀ {W : 𝒞} (g h : W ⟶ X), g ≫ m = h ≫ m → g = h

def IsIso {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, f ≫ g = Cat.id X ∧ g ≫ f = Cat.id Y

def Cover {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∀ {C : 𝒞} (m : C ⟶ Y) (g : X ⟶ C), Mono m → g ≫ m = f → IsIso m

theorem monic_cover_iso {X Y : 𝒞} (f : X ⟶ Y) (hc : Cover f) (hm : Mono f) : IsIso f :=
  hc f (Cat.id X) hm (Cat.id_comp f)

/-- Isomorphisms are closed under composition; the inverse is `g⁻¹ ≫ f⁻¹`. -/
theorem isIso_comp {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsIso f) (hg : IsIso g) :
    IsIso (f ≫ g) := by
  obtain ⟨f', hf1, hf2⟩ := hf
  obtain ⟨g', hg1, hg2⟩ := hg
  exact ⟨g' ≫ f',
    by rw [Cat.assoc, ← Cat.assoc g, hg1, Cat.id_comp, hf1],
    by rw [Cat.assoc, ← Cat.assoc f', hf2, Cat.id_comp, hg2]⟩

class HasTerminal (𝒞 : Type u) [Cat.{v} 𝒞] where
  one   : 𝒞
  trm   : (X : 𝒞) → X ⟶ one
  uniq  : ∀ {X : 𝒞} (f g : X ⟶ one), f = g

variable [ht : HasTerminal 𝒞]

def one : 𝒞 := ht.one
def term (X : 𝒞) : X ⟶ one := ht.trm X

theorem term_uniq {X : 𝒞} (f g : X ⟶ one) : f = g := ht.uniq f g

class HasBinaryProducts (𝒞 : Type u) [Cat.{v} 𝒞] where
  prod  : 𝒞 → 𝒞 → 𝒞
  fst   : {A B : 𝒞} → prod A B ⟶ A
  snd   : {A B : 𝒞} → prod A B ⟶ B
  pair  : {X A B : 𝒞} → (X ⟶ A) → (X ⟶ B) → (X ⟶ prod A B)
  fst_pair : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B), pair f g ≫ fst = f
  snd_pair : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B), pair f g ≫ snd = g
  pair_uniq : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) (h : X ⟶ prod A B),
    h ≫ fst = f → h ≫ snd = g → h = pair f g

variable [hp : HasBinaryProducts 𝒞]

def prod (A B : 𝒞) : 𝒞 := hp.prod A B
def fst  {A B : 𝒞} : prod A B ⟶ A := hp.fst
def snd  {A B : 𝒞} : prod A B ⟶ B := hp.snd
def pair {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) : X ⟶ prod A B := hp.pair f g

@[simp]
theorem fst_pair {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) : pair f g ≫ fst = f :=
  hp.fst_pair f g

@[simp]
theorem snd_pair {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) : pair f g ≫ snd = g :=
  hp.snd_pair f g

theorem pair_uniq {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) (h : X ⟶ prod A B)
    (h₁ : h ≫ fst = f) (h₂ : h ≫ snd = g) : h = pair f g :=
  hp.pair_uniq f g h h₁ h₂

def diag (A : 𝒞) : A ⟶ prod A A := pair (Cat.id A) (Cat.id A)

theorem diag_fst (A : 𝒞) : diag A ≫ fst = Cat.id A := fst_pair _ _
theorem diag_snd (A : 𝒞) : diag A ≫ snd = Cat.id A := snd_pair _ _

theorem diag_mono (A : 𝒞) : Mono (diag A) := by
  intro W f g h
  -- h: f ≫ diag A = g ≫ diag A.  Need f = g.
  -- Since ≫ is right-assoc, f ≫ diag A ≫ fst = f ≫ (diag A ≫ fst).
  -- Compose h with fst on the right:
  have hfst : f ≫ (diag A ≫ fst) = g ≫ (diag A ≫ fst) := by
    rw [← Cat.assoc, ← Cat.assoc, h]
  rw [diag_fst, Cat.comp_id, Cat.comp_id] at hfst
  exact hfst

/-! ## Pullbacks and kernel pairs (§1.453–1.454) -/

/-- A pullback of the cospan `A —f→ C ←g— B`.  Making the cospan `f, g` (and its
    objects `A B C`) parameters of the *class* states them once, instead of
    re-binding `{A B C} {f} {g}` on every field. -/
class HasPullback {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) where
  obj  : 𝒞
  fst  : obj ⟶ A
  snd  : obj ⟶ B
  sq   : fst ≫ f = snd ≫ g
  lift {X : 𝒞} (h : X ⟶ A) (k : X ⟶ B) (e : h ≫ f = k ≫ g) : X ⟶ obj
  lift_fst {X : 𝒞} {h : X ⟶ A} {k : X ⟶ B} {e : h ≫ f = k ≫ g} : lift h k e ≫ fst = h
  lift_snd {X : 𝒞} {h : X ⟶ A} {k : X ⟶ B} {e : h ≫ f = k ≫ g} : lift h k e ≫ snd = k
  lift_uniq {X : 𝒞} {h : X ⟶ A} {k : X ⟶ B} {e : h ≫ f = k ≫ g}
    (u : X ⟶ obj) (h₁ : u ≫ fst = h) (h₂ : u ≫ snd = k) : u = lift h k e

/-- The category has all pullbacks: a `HasPullback` for every cospan. -/
class HasPullbacks (𝒞 : Type u) [Cat.{v} 𝒞] where
  has {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) : HasPullback f g

variable [hpull : HasPullbacks 𝒞]

/-- The kernel pair of f : pullback of f along f.  §1.454 -/
def kernelPair {A B : 𝒞} (f : A ⟶ B) : 𝒞 := (hpull.has f f).obj

def kp₁ {A B : 𝒞} {f : A ⟶ B} : kernelPair f ⟶ A := (hpull.has f f).fst
def kp₂ {A B : 𝒞} {f : A ⟶ B} : kernelPair f ⟶ A := (hpull.has f f).snd

theorem kp_sq {A B : 𝒞} {f : A ⟶ B} : (kp₁ (f:=f)) ≫ f = (kp₂ (f:=f)) ≫ f := (hpull.has f f).sq

def kp_diag {A B : 𝒞} {f : A ⟶ B} : A ⟶ kernelPair f :=
  (hpull.has f f).lift (Cat.id A) (Cat.id A) (rfl)

theorem kp_diag_p₁ {A B : 𝒞} {f : A ⟶ B} : kp_diag (f:=f) ≫ kp₁ (f:=f) = Cat.id A := (hpull.has f f).lift_fst
theorem kp_diag_p₂ {A B : 𝒞} {f : A ⟶ B} : kp_diag (f:=f) ≫ kp₂ (f:=f) = Cat.id A := (hpull.has f f).lift_snd

theorem kp_lift_p₁ {A B X : 𝒞} {f : A ⟶ B} (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) :
    (hpull.has f f).lift x₁ x₂ h ≫ kp₁ (f:=f) = x₁ := (hpull.has f f).lift_fst

theorem kp_lift_p₂ {A B X : 𝒞} {f : A ⟶ B} (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) :
    (hpull.has f f).lift x₁ x₂ h ≫ kp₂ (f:=f) = x₂ := (hpull.has f f).lift_snd

theorem kp_lift_uniq {A B X : 𝒞} {f : A ⟶ B} (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f)
    (g : X ⟶ kernelPair f) (h₁ : g ≫ kp₁ (f:=f) = x₁) (h₂ : g ≫ kp₂ (f:=f) = x₂) :
    g = (hpull.has f f).lift x₁ x₂ h := (hpull.has f f).lift_uniq g h₁ h₂

/-- Lemma from 1.453: f is monic iff the diagonal into its kernel pair is iso. -/
theorem monic_iff_kp_diag_iso {A B : 𝒞} {f : A ⟶ B} :
    Mono f ↔ IsIso (kp_diag (f:=f)) := by
  constructor
  · intro hm
    have h_eq : kp₁ (f:=f) = kp₂ (f:=f) := hm _ _ kp_sq
    refine ⟨kp₁ (f:=f), kp_diag_p₁, ?_⟩
    have h_id : (hpull.has f f).lift (kp₁ (f:=f)) (kp₂ (f:=f)) kp_sq = Cat.id (kernelPair f) :=
      (kp_lift_uniq (kp₁ (f:=f)) (kp₂ (f:=f)) kp_sq (Cat.id (kernelPair f))
        (Cat.id_comp _) (Cat.id_comp _)).symm
    have h_comp : (kp₁ (f:=f)) ≫ kp_diag (f:=f) =
        (hpull.has f f).lift (kp₁ (f:=f)) (kp₂ (f:=f)) kp_sq :=
      (kp_lift_uniq (kp₁ (f:=f)) (kp₂ (f:=f)) kp_sq ((kp₁ (f:=f)) ≫ kp_diag (f:=f))
        (by rw [Cat.assoc, kp_diag_p₁, Cat.comp_id])
        (by rw [Cat.assoc, kp_diag_p₂, Cat.comp_id, h_eq]))
    rw [h_comp, h_id]
  · intro hiso
    obtain ⟨inv, _diag_inv, inv_diag⟩ := hiso
    intro X x₁ x₂ h
    let hpair : X ⟶ kernelPair f := (hpull.has f f).lift x₁ x₂ h
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

/-! ## Bridging kernelPair(term A) to A×A -/

/-- kpProdIso : kernelPair(term A) → A×A constructed via the product universal
    property, and kpProdInv in the reverse direction via the pullback lift. -/
def kpProdIso (A : 𝒞) : kernelPair (term A) ⟶ prod A A :=
  pair (kp₁ (f:=term A)) (kp₂ (f:=term A))

def kpProdInv (A : 𝒞) : prod A A ⟶ kernelPair (term A) :=
  (hpull.has (term A) (term A)).lift fst snd (term_uniq _ _)

@[simp] theorem kpProdIso_fst (A : 𝒞) : kpProdIso A ≫ fst = kp₁ (f:=term A) := fst_pair _ _
@[simp] theorem kpProdIso_snd (A : 𝒞) : kpProdIso A ≫ snd = kp₂ (f:=term A) := snd_pair _ _
@[simp] theorem kpProdInv_fst (A : 𝒞) : kpProdInv A ≫ kp₁ (f:=term A) = fst := (hpull.has (term A) (term A)).lift_fst
@[simp] theorem kpProdInv_snd (A : 𝒞) : kpProdInv A ≫ kp₂ (f:=term A) = snd := (hpull.has (term A) (term A)).lift_snd

theorem kpProdIso_inv (A : 𝒞) : kpProdIso A ≫ kpProdInv A = Cat.id (kernelPair (term A)) := by
  let u := kpProdIso A ≫ kpProdInv A
  have hu_fst : u ≫ kp₁ (f:=term A) = kp₁ (f:=term A) := by
    dsimp [u]; rw [Cat.assoc, kpProdInv_fst, kpProdIso_fst]
  have hu_snd : u ≫ kp₂ (f:=term A) = kp₂ (f:=term A) := by
    dsimp [u]; rw [Cat.assoc, kpProdInv_snd, kpProdIso_snd]
  have h_id_lift : (hpull.has (term A) (term A)).lift (kp₁ (f:=term A)) (kp₂ (f:=term A)) kp_sq =
      Cat.id (kernelPair (term A)) :=
    ((hpull.has (term A) (term A)).lift_uniq (Cat.id _) (Cat.id_comp _) (Cat.id_comp _)).symm
  calc
    u = (hpull.has (term A) (term A)).lift (kp₁ (f:=term A)) (kp₂ (f:=term A)) kp_sq :=
      (hpull.has (term A) (term A)).lift_uniq u hu_fst hu_snd
    _ = Cat.id (kernelPair (term A)) := h_id_lift

theorem kpProdInv_iso (A : 𝒞) : kpProdInv A ≫ kpProdIso A = Cat.id (prod A A) := by
  have h := pair_uniq fst snd (kpProdInv A ≫ kpProdIso A)
    (by rw [Cat.assoc, kpProdIso_fst, kpProdInv_fst])
    (by rw [Cat.assoc, kpProdIso_snd, kpProdInv_snd])
  have hid : pair fst snd = Cat.id (prod A A) :=
    (pair_uniq fst snd (Cat.id (prod A A)) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])).symm
  rw [h, hid]

theorem kpProdIso_isIso (A : 𝒞) : IsIso (kpProdIso A) :=
  ⟨kpProdInv A, kpProdIso_inv A, kpProdInv_iso A⟩

theorem kpProdInv_isIso (A : 𝒞) : IsIso (kpProdInv A) :=
  ⟨kpProdIso A, kpProdInv_iso A, kpProdIso_inv A⟩

theorem kp_diag_prod (A : 𝒞) : kp_diag (f:=term A) ≫ kpProdIso A = diag A := by
  let h := kp_diag (f:=term A) ≫ kpProdIso A
  have hfst : h ≫ fst = Cat.id A := by
    dsimp [h]; rw [Cat.assoc, kpProdIso_fst, kp_diag_p₁]
  have hsnd : h ≫ snd = Cat.id A := by
    dsimp [h]; rw [Cat.assoc, kpProdIso_snd, kp_diag_p₂]
  have h_eq := pair_uniq (Cat.id A) (Cat.id A) h hfst hsnd
  simpa [h, diag] using h_eq

def WellSupported (A : 𝒞) : Prop := Cover (term A)

/-- A is well-pointed: the global elements 1 → A jointly cover A (§1.523).
    Elementary: for every proper monic m: B → A, there exists a global
    element 1 → A that does NOT factor through m. -/
def WellPointed (A : 𝒞) : Prop :=
  ∀ {B : 𝒞} (m : B ⟶ A), Mono m → ¬ IsIso m → ∃ (x : one ⟶ A), ¬ ∃ (y : one ⟶ B), y ≫ m = x

/-- Capital: every well-supported object is well-pointed.  §1.525 -/
def Capital : Prop := ∀ (A : 𝒞), WellSupported A → WellPointed A

theorem wellSupported_prod_self (A : 𝒞) (hws : WellSupported A) : WellSupported (prod A A) := by
  intro C m g hm hgm
  -- g ≫ m = term (A × A)
  have h_diag_term : diag A ≫ term (prod A A) = term A := term_uniq _ _
  have h_factor : (diag A ≫ g) ≫ m = term A := by
    rw [Cat.assoc, hgm, h_diag_term]
  exact hws m (diag A ≫ g) hm h_factor

-- §1.525
theorem capital_implies_one_projective
    (hcap : ∀ (A : 𝒞), WellSupported A → WellPointed A)
    (A : 𝒞) (hws : WellSupported A) :
    ∃ (_ : one ⟶ A), True := by
  -- 1. If A → 1 is iso, use the inverse.
  by_cases hiso : IsIso (term A)
  · obtain ⟨inv, _, _⟩ := hiso
    exact ⟨inv, trivial⟩
  · -- 2. A → 1 is a cover but not iso.  By monic-cover-iso (1.512), it is not monic.
    have h_not_monic : ¬ Mono (term A) := by
      intro hm
      apply hiso
      exact monic_cover_iso (term A) hws hm
    -- 3. Hence kp_diag(term A) is not iso (1.453: monic_iff_kp_diag_iso).
    --    Via kpProdIso, diag A is also not iso — a proper monic.
    have h_not_iso_kp : ¬ IsIso (kp_diag (f:=term A)) :=
      mt ((monic_iff_kp_diag_iso (f:=term A)).mpr) h_not_monic
    have h_not_iso_diag : ¬ IsIso (diag A) := by
      intro hiso_diag; apply h_not_iso_kp
      have hkp : kp_diag (f:=term A) = diag A ≫ kpProdInv A := by
        rw [← kp_diag_prod A, Cat.assoc, kpProdIso_inv A, Cat.comp_id]
      rw [hkp]
      exact isIso_comp hiso_diag (kpProdInv_isIso A)
    have hm_diag : Mono (diag A) := diag_mono A
    -- 4. A×A is well-supported — via the diagonal, no pullbacks needed.
    have hwsAA : WellSupported (prod A A) := wellSupported_prod_self A hws
    -- 5. By capital, A×A is well-pointed.
    have hwpAA : WellPointed (prod A A) := hcap (prod A A) hwsAA
    -- 6. Apply well-pointed to the proper monic Δ : ∃ x:1→A×A.
    obtain ⟨x, _⟩ := hwpAA (diag A) hm_diag h_not_iso_diag
    -- 7. Compose x with π₁ : 1 → A.
    exact ⟨x ≫ fst, trivial⟩

end Freyd
