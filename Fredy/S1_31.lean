/-
  Freyd & Scedrov, *Categories and Allegories* §1.31–§1.32
  Embedding, Full, Representative Image, Equivalence Functor,
  Strong equivalence.  Proofs assuming composed functor = compFunctor.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_27
import Fredy.S1_41


open Freyd

universe v u u₁ u₂

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.31 Embedding, Full, Representative Image, Equivalence Functor -/

def Embedding (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B), hF.map f = hF.map g → f = g

/-- The cross-universe form of `Embedding`: `T` SEPARATES MAPS if it is injective
    on each hom-set.  Same notion as `Embedding`, but with source and target in
    possibly different object universes — needed for representations `𝒞 → 𝒮^I`
    whose target lives one universe up (§1.55 Henkin-Lubkin). -/
def SeparatesMaps {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D]
    (T : C → D) [hT : Functor T] : Prop :=
  ∀ {A B : C} (f g : A ⟶ B), hT.map f = hT.map g → f = g

def Full (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  ∀ {A B : 𝒞} (h : F A ⟶ F B), ∃ f : A ⟶ B, hF.map f = h

def HasRepresentativeImage (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  ∀ B : 𝒟, ∃ A : 𝒞, ∃ (h : F A ⟶ B), IsIso h

def EquivalenceFunctor (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  Embedding F ∧ Full F ∧ HasRepresentativeImage F

/-! ## §1.32 Composition and cancellation

  Embedding ∘ embedding = embedding; full ∘ full = full.
  With `hGF := compFunctor hF hG`, these are definitional. -/

section Composition
variable {F : 𝒞 → 𝒟} [hF : Functor F] {ℰ : Type u} [Cat.{v} ℰ] {G : 𝒟 → ℰ} [hG : Functor G]

theorem embedding_comp (embF : Embedding F) (embG : Embedding G) : Embedding (G ∘ F) := by
  intro A B f g h
  -- h : (compFunctor.map : (G ∘ F) A → (G ∘ F) B) f = (compFunctor.map ...) g
  -- h reduces to hG.map (hF.map f) = hG.map (hF.map g)
  apply embF f g
  apply embG (hF.map f) (hF.map g)
  simpa using h

theorem full_comp (fullF : Full F) (fullG : Full G) : Full (G ∘ F) := by
  intro A B h
  rcases fullG h with ⟨g, hg⟩
  rcases fullF g with ⟨f, hf⟩
  have hgoal : (compFunctor (hf := hF) (hg := hG)).map f = h := by
    calc
      (compFunctor (hf := hF) (hg := hG)).map f = hG.map (hF.map f) := rfl
      _ = hG.map g := by rw [hf]
      _ = h := by rw [hg]
  exact ⟨f, hgoal⟩

end Composition

/-! ## §1.31 Full subcategory -/

/-- A FULL SUBCATEGORY is a subcategory whose inclusion functor is full (§1.31).
    We represent this as a `Prop` on the inclusion functor `I : 𝒜 → 𝒞`. -/
def IsFullSubcategory (I : 𝒞 → 𝒟) [Functor I] : Prop := Full I

/-! ## §1.32 Composition of representative image and cancellation principles -/

section CancellationAndComp
variable {𝒜 : Type u} [Cat.{v} 𝒜]
variable {F : 𝒞 → 𝒟} [hF : Functor F] {G : 𝒟 → 𝒜} [hG : Functor G]

/-- Composition preserves representative image (§1.32). -/
theorem hasRepresentativeImage_comp
    (hrF : HasRepresentativeImage F) (hrG : HasRepresentativeImage G) :
    HasRepresentativeImage (G ∘ F) := by
  intro C
  -- G has representative image: ∃ B : 𝒟, ∃ h : GB ⟶ C, IsIso h
  obtain ⟨B, h, hh⟩ := hrG C
  -- F has representative image: ∃ A : 𝒞, ∃ k : FA ⟶ B, IsIso k
  obtain ⟨A, k, hk⟩ := hrF B
  obtain ⟨k', hk1, hk2⟩ := hk
  -- k : FA ⟶ B in 𝒟, so G(k) : G(FA) ⟶ G(B) in 𝒜; compose with h : G(B) ⟶ C
  refine ⟨A, hG.map k ≫ h, isIso_comp ?_ hh⟩
  exact ⟨hG.map k', by rw [← hG.map_comp, hk1, hG.map_id]; rfl,
                      by rw [← hG.map_comp, hk2, hG.map_id]⟩

/-- If G∘F is an embedding then F is an embedding (§1.32). -/
theorem embedding_of_comp_embedding (emb : Embedding (G ∘ F)) : Embedding F := by
  intro A B f g hfg
  apply emb f g
  show hG.map (hF.map f) = hG.map (hF.map g)
  rw [hfg]

/-- If G∘F is full then G is full on F-images (§1.32).
    Freyd's full-cancellation principle: "if A→B→C is full then G is full" means
    that for every pair in the image of F, any map between G-images lifts through G. -/
theorem full_of_comp_full_on_image (fullGF : Full (G ∘ F)) (A B : 𝒞)
    (h : G (F A) ⟶ G (F B)) : ∃ f : F A ⟶ F B, hG.map f = h := by
  obtain ⟨a, ha⟩ := fullGF h
  exact ⟨hF.map a, ha⟩

/-- If G∘F has a representative image then G has a representative image (§1.32). -/
theorem hasRepresentativeImage_of_comp (hri : HasRepresentativeImage (G ∘ F)) :
    HasRepresentativeImage G := by
  intro C
  obtain ⟨A, h, hh⟩ := hri C
  exact ⟨F A, h, hh⟩

end CancellationAndComp

/-! ## Strong equivalence (§1.32) -/

structure NatIso (F G : 𝒞 → 𝒟) [hF : Functor F] [hG : Functor G] where
  nat : NaturalTransformation F G
  isIso : ∀ X : 𝒞, IsIso (nat.app X)

structure StrongEquivalence (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞)
    [hF : Functor F] [hG : Functor G] where
  unit : Nonempty (NatIso (G ∘ F) (λ X : 𝒞 => X))
  counit : Nonempty (NatIso (F ∘ G) (λ X : 𝒟 => X))

/-! ## §1.32 Conjugation invariance

  Each of Embedding / Full / HasRepresentativeImage is preserved under
  conjugation (natural isomorphism) of functors.  That is, if α : NatIso F G
  (F, G : 𝒞 → 𝒟 conjugate) then Embedding F ↔ Embedding G, etc.

  We prove the forward implication; the backward follows by symmetry
  (invert each component of α). -/

section Conjugation
variable {F G : 𝒞 → 𝒟} [hF : Functor F] [hG : Functor G]

/-- If F is an embedding and α : NatIso F G, then G is an embedding (§1.32 conjugation). -/
theorem embedding_of_natIso (α : NatIso F G) (emb : Embedding F) : Embedding G := by
  intro A B f g hfg
  obtain ⟨αB_inv, hαB1, _⟩ := α.isIso B
  have natF := α.nat.naturality f
  have natG := α.nat.naturality g
  -- hF.map f ≫ α_B = α_A ≫ hG.map f = α_A ≫ hG.map g = hF.map g ≫ α_B
  have h1 : hF.map f ≫ α.nat.app B = hF.map g ≫ α.nat.app B := by
    rw [natF, natG, hfg]
  -- cancel α_B on right: post-compose h1 with αB_inv using hαB1 : α_B ≫ αB_inv = id
  have h3 : hF.map f = hF.map g := by
    calc hF.map f
        = hF.map f ≫ Cat.id _ := (Cat.comp_id _).symm
      _ = hF.map f ≫ (α.nat.app B ≫ αB_inv) := by rw [hαB1]
      _ = (hF.map f ≫ α.nat.app B) ≫ αB_inv := (Cat.assoc _ _ _).symm
      _ = (hF.map g ≫ α.nat.app B) ≫ αB_inv := by rw [h1]
      _ = hF.map g ≫ (α.nat.app B ≫ αB_inv) := Cat.assoc _ _ _
      _ = hF.map g ≫ Cat.id _ := by rw [hαB1]
      _ = hF.map g := Cat.comp_id _
  exact emb f g h3

/-- If F is full and α : NatIso F G, then G is full (§1.32 conjugation). -/
theorem full_of_natIso (α : NatIso F G) (full : Full F) : Full G := by
  intro A B h
  obtain ⟨αB_inv, hαB1, hαB2⟩ := α.isIso B
  obtain ⟨αA_inv, hαA1, hαA2⟩ := α.isIso A
  -- lift α_A ≫ h ≫ α_B⁻¹ : FA ⟶ FB through fullness of F
  obtain ⟨f, hf⟩ := full (α.nat.app A ≫ h ≫ αB_inv)
  have nat := α.nat.naturality f
  -- nat : hF.map f ≫ α.nat.app B = α.nat.app A ≫ hG.map f
  -- Show hG.map f = h using:
  --   α_A ≫ hG.map f = hF.map f ≫ α_B        (naturality)
  --                   = (α_A ≫ h ≫ α_B⁻¹) ≫ α_B  (hf)
  --                   = α_A ≫ h ≫ (α_B⁻¹ ≫ α_B) = α_A ≫ h
  have key : α.nat.app A ≫ hG.map f = α.nat.app A ≫ h := by
    have : α.nat.app A ≫ hG.map f = hF.map f ≫ α.nat.app B := by rw [nat]
    rw [this, hf]
    simp only [Cat.assoc, hαB2, Cat.comp_id]
  -- left-cancel α.nat.app A from key: pre-compose with αA_inv using hαA2 : αA_inv ≫ α_A = id
  have : hG.map f = h := by
    calc hG.map f
        = Cat.id _ ≫ hG.map f := (Cat.id_comp _).symm
      _ = (αA_inv ≫ α.nat.app A) ≫ hG.map f := by rw [hαA2]
      _ = αA_inv ≫ (α.nat.app A ≫ hG.map f) := Cat.assoc _ _ _
      _ = αA_inv ≫ (α.nat.app A ≫ h) := by rw [key]
      _ = (αA_inv ≫ α.nat.app A) ≫ h := (Cat.assoc _ _ _).symm
      _ = Cat.id _ ≫ h := by rw [hαA2]
      _ = h := Cat.id_comp _
  exact ⟨f, this⟩

/-- If F has representative image and α : NatIso F G, then G has rep. image (§1.32 conjugation). -/
theorem hasRepresentativeImage_of_natIso (α : NatIso F G) (hri : HasRepresentativeImage F) :
    HasRepresentativeImage G := by
  intro B
  obtain ⟨A, h, hh⟩ := hri B
  obtain ⟨αA_inv, hαA1, hαA2⟩ := α.isIso A
  exact ⟨A, αA_inv ≫ h, isIso_comp ⟨α.nat.app A, hαA2, hαA1⟩ hh⟩

end Conjugation

end Freyd
