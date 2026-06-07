/-
  Freyd & Scedrov, *Categories and Allegories* §1.525.

  "A pre-regular category is CAPITAL if every well-supported object is well-pointed.
   In a capital pre-regular category the terminator is projective."

  Projectivity of 1 (§1.524) means the representable functor Hom(1,−) preserves
  covers.  The elementary consequence: every well-supported A has a global
  element 1 → A.

  Self-contained (mathlib-free), defining minimal Cat, HasTerminal,
  HasBinaryProducts classes.

  ## Definitions
  - Cat, Mono, IsIso, Cover — self-contained category theory
  - HasTerminal, HasBinaryProducts — Cartesian structure
  - diag A : A → A×A — the diagonal
  - WellSupported A — A → 1 is a cover (§1.522)
  - WellPointed A — every proper monic into A misses some global element
    (§1.523)
  - Capital — every well-supported object is well-pointed (§1.525)

  ## Key lemmas
  - monic_cover_iso — monic + cover ⇒ iso (1.512)
  - diag_mono — the diagonal is always monic
  - monic_iff_diag_kp_iso — f is monic iff the diagonal into its kernel
    pair is an iso (§1.453), proved via the general KernelPair structure;
    instantiated at f = term A to get step 3 of the main proof
  - wellSupported_prod_self — WellSupported A ⇒ WellSupported (A×A)
    (via the diagonal, no pullbacks needed)

  ## Main theorem (capital_implies_one_projective)
  In a capital category, every well-supported object has a point 1 → A.
  This proves §1.525's claim that the terminator is projective.

  Proof outline (following the book):
    1. If A → 1 is iso, use the inverse.
    2. Otherwise A → 1 is a cover but not iso.  By monic-cover-iso (1.512),
       it is not monic.
    3. Hence Δ : A → A×A is a proper monic (1.453: monic_iff_diag_kp_iso).
    4. A×A is well-supported — proved using the diagonal, no pullbacks.
    5. By capital, A×A is well-pointed.
    6. Apply well-pointed to the proper monic Δ : ∃ x:1→A×A.
    7. Compose x with π₁ : 1 → A.
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

theorem fst_eq_snd_of_monic_term (A : 𝒞) (hm : Mono (term A)) : fst = snd (A:=A) (B:=A) := by
  apply hm
  exact term_uniq _ _

/-! ## Kernel pairs and the monic-vs-diagonal lemma (§1.453–1.454) -/

/-- The kernel pair (level) of f : A → B: an object K with two projections
    p₁, p₂ : K → A equalising f, plus the diagonal A → K and a universal
    property.  §1.454 -/
structure KernelPair {A B : 𝒞} (f : A ⟶ B) where
  K : 𝒞
  p₁ : K ⟶ A
  p₂ : K ⟶ A
  eq  : p₁ ≫ f = p₂ ≫ f
  diag : A ⟶ K
  diag_p₁ : diag ≫ p₁ = Cat.id A
  diag_p₂ : diag ≫ p₂ = Cat.id A
  lift {X : 𝒞} (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) : X ⟶ K
  lift_p₁ {X : 𝒞} (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) : lift x₁ x₂ h ≫ p₁ = x₁
  lift_p₂ {X : 𝒞} (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) : lift x₁ x₂ h ≫ p₂ = x₂
  lift_uniq {X : 𝒞} (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) (g : X ⟶ K)
    (h₁ : g ≫ p₁ = x₁) (h₂ : g ≫ p₂ = x₂) : g = lift x₁ x₂ h

/-- The kernel pair of the unique map A → 1 is the product A × A (§1.454). -/
def termKernelPair (A : 𝒞) : KernelPair (term A) where
  K      := prod A A
  p₁     := fst
  p₂     := snd
  eq     := term_uniq _ _
  diag   := diag A
  diag_p₁ := diag_fst A
  diag_p₂ := diag_snd A
  lift   := fun x₁ x₂ _ => pair x₁ x₂
  lift_p₁ := fun x₁ x₂ _ => fst_pair x₁ x₂
  lift_p₂ := fun x₁ x₂ _ => snd_pair x₁ x₂
  lift_uniq := fun x₁ x₂ h g h₁ h₂ => pair_uniq x₁ x₂ g h₁ h₂

/-- Lemma from 1.453: f is monic iff the diagonal into its kernel pair
    is an isomorphism.  This is the key fact that makes step 3 of 1.525
    work: if term A is not monic then diag A is not iso, hence Δ is a
    proper subobject. -/
theorem monic_iff_diag_kp_iso {A B : 𝒞} {f : A ⟶ B} (kp : KernelPair f) :
    Mono f ↔ IsIso kp.diag := by
  constructor
  · intro hm
    -- f monic ⇒ p₁ = p₂ (from kp.eq), then p₁ is an inverse of diag
    have h_eq : kp.p₁ = kp.p₂ := hm _ _ kp.eq
    refine ⟨kp.p₁, kp.diag_p₁, ?_⟩
    have h_id : kp.lift kp.p₁ kp.p₂ kp.eq = Cat.id kp.K :=
      (kp.lift_uniq kp.p₁ kp.p₂ kp.eq (Cat.id kp.K) (Cat.id_comp _) (Cat.id_comp _)).symm
    have h_comp : kp.p₁ ≫ kp.diag = kp.lift kp.p₁ kp.p₂ kp.eq :=
      (kp.lift_uniq kp.p₁ kp.p₂ kp.eq (kp.p₁ ≫ kp.diag)
        (by rw [Cat.assoc, kp.diag_p₁, Cat.comp_id])
        (by rw [Cat.assoc, kp.diag_p₂, Cat.comp_id, h_eq]))
    rw [h_comp, h_id]
  · intro hiso
    -- diag iso ⇒ f monic (1.453 proof)
    obtain ⟨inv, _diag_inv, inv_diag⟩ := hiso
    intro X x₁ x₂ h
    let hpair := kp.lift x₁ x₂ h
    let t : X ⟶ A := hpair ≫ inv
    have ht : hpair = t ≫ kp.diag := by
      rw [Cat.assoc, inv_diag, Cat.comp_id]
    calc
      x₁ = hpair ≫ kp.p₁ := by rw [kp.lift_p₁ x₁ x₂ h]
      _ = (t ≫ kp.diag) ≫ kp.p₁ := by rw [ht]
      _ = t ≫ (kp.diag ≫ kp.p₁) := by rw [Cat.assoc]
      _ = t ≫ Cat.id A := by rw [kp.diag_p₁]
      _ = t := by rw [Cat.comp_id]
      _ = t ≫ Cat.id A := by rw [Cat.comp_id]
      _ = t ≫ (kp.diag ≫ kp.p₂) := by rw [kp.diag_p₂]
      _ = (t ≫ kp.diag) ≫ kp.p₂ := by rw [← Cat.assoc]
      _ = hpair ≫ kp.p₂ := by rw [ht]
      _ = x₂ := by rw [kp.lift_p₂ x₁ x₂ h]

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
    -- 3. Hence Δ : A → A×A is a proper monic (1.453: term A not monic ⇒ diag not iso).
    have h_not_iso_diag : ¬ IsIso (diag A) :=
      mt ((monic_iff_diag_kp_iso (termKernelPair A)).mpr) h_not_monic
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
