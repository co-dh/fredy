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

def HasRepresentativeImage (F : 𝒞 → 𝒟) [Functor F] : Prop :=
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

/-! ## §1.32 EquivalenceFunctor under conjugation and composition -/

/-- An equivalence functor is preserved under conjugation (§1.32). -/
theorem equivalenceFunctor_of_natIso {F G : 𝒞 → 𝒟} [hF : Functor F] [hG : Functor G]
    (α : NatIso F G) (eq : EquivalenceFunctor F) : EquivalenceFunctor G :=
  ⟨embedding_of_natIso α eq.1, full_of_natIso α eq.2.1, hasRepresentativeImage_of_natIso α eq.2.2⟩

section EquivComp
variable {𝒜 : Type u} [Cat.{v} 𝒜]
variable {F : 𝒞 → 𝒟} [hF : Functor F] {G : 𝒟 → 𝒜} [hG : Functor G]

/-- Composition of two equivalence functors is an equivalence functor (§1.32). -/
theorem equivalenceFunctor_comp (eF : EquivalenceFunctor F) (eG : EquivalenceFunctor G) :
    EquivalenceFunctor (G ∘ F) :=
  ⟨embedding_comp eF.1 eG.1, full_comp eF.2.1 eG.2.1, hasRepresentativeImage_comp eF.2.2 eG.2.2⟩

end EquivComp

/-! ## §1.32 Strong equivalence implies both functors are equivalence functors -/

section StrongEquivIsEquiv
variable {F : 𝒞 → 𝒟} {G : 𝒟 → 𝒞} [hF : Functor F] [hG : Functor G]

private theorem id_embedding : Embedding (λ X : 𝒞 => X) := fun _ _ h => h
private theorem id_full : Full (λ X : 𝒞 => X) := fun h => ⟨h, rfl⟩
private theorem id_hasRepresentativeImage : HasRepresentativeImage (λ X : 𝒞 => X) :=
  fun B => ⟨B, Cat.id B, Cat.id B, Cat.comp_id _, Cat.comp_id _⟩

-- GF has rep image: for each B : 𝒞, (G∘F)(B) ≅ B via η_B.
private theorem compGF_hasRepresentativeImage (η : NatIso (G ∘ F) (λ X : 𝒞 => X)) :
    HasRepresentativeImage (G ∘ F) :=
  fun B => ⟨B, η.nat.app B, η.isIso B⟩

private theorem compFG_hasRepresentativeImage (δ : NatIso (F ∘ G) (λ X : 𝒟 => X)) :
    HasRepresentativeImage (F ∘ G) :=
  fun D => ⟨D, δ.nat.app D, δ.isIso D⟩

-- GF is an embedding: if (G∘F)(f) = (G∘F)(g), naturality gives η_A ≫ f = η_A ≫ g
-- (both sides of nat use the same (G∘F).map, but RHS is id.map = identity), so f = g.
private theorem compGF_embedding (η : NatIso (G ∘ F) (λ X : 𝒞 => X)) : Embedding (G ∘ F) := by
  intro A B f g heq
  obtain ⟨ηA_inv, hηA1, hηA2⟩ := η.isIso A
  have natF := η.nat.naturality f  -- (G∘F)(f) ≫ η_B = η_A ≫ id.map f = η_A ≫ f
  have natG := η.nat.naturality g
  -- natF.symm.trans : η_A ≫ f = (G∘F)(f) ≫ η_B; rw heq; then natG gives η_A ≫ g
  have hfg : η.nat.app A ≫ f = η.nat.app A ≫ g :=
    natF.symm.trans (by rw [heq]) |>.trans natG
  calc f = Cat.id _ ≫ f := (Cat.id_comp _).symm
    _ = (ηA_inv ≫ η.nat.app A) ≫ f := by rw [hηA2]
    _ = ηA_inv ≫ (η.nat.app A ≫ f) := Cat.assoc _ _ _
    _ = ηA_inv ≫ (η.nat.app A ≫ g) := by rw [hfg]
    _ = (ηA_inv ≫ η.nat.app A) ≫ g := (Cat.assoc _ _ _).symm
    _ = Cat.id _ ≫ g := by rw [hηA2]
    _ = g := Cat.id_comp _

private theorem compFG_embedding (δ : NatIso (F ∘ G) (λ X : 𝒟 => X)) : Embedding (F ∘ G) := by
  intro A B f g heq
  obtain ⟨δA_inv, hδA1, hδA2⟩ := δ.isIso A
  have natF := δ.nat.naturality f
  have natG := δ.nat.naturality g
  have hfg : δ.nat.app A ≫ f = δ.nat.app A ≫ g :=
    natF.symm.trans (by rw [heq]) |>.trans natG
  calc f = Cat.id _ ≫ f := (Cat.id_comp _).symm
    _ = (δA_inv ≫ δ.nat.app A) ≫ f := by rw [hδA2]
    _ = δA_inv ≫ (δ.nat.app A ≫ f) := Cat.assoc _ _ _
    _ = δA_inv ≫ (δ.nat.app A ≫ g) := by rw [hfg]
    _ = (δA_inv ≫ δ.nat.app A) ≫ g := (Cat.assoc _ _ _).symm
    _ = Cat.id _ ≫ g := by rw [hδA2]
    _ = g := Cat.id_comp _

-- GF is full: for h : (G∘F)(A) ⟶ (G∘F)(B), the lift is ηA_inv ≫ h ≫ η_B : A ⟶ B.
-- Naturality: (G∘F)(f) ≫ η_B = η_A ≫ id.map(f) = η_A ≫ f.
-- So (G∘F)(ηA_inv ≫ h ≫ η_B) ≫ η_B = η_A ≫ (ηA_inv ≫ h ≫ η_B) = h ≫ η_B; cancel η_B.
private theorem compGF_full (η : NatIso (G ∘ F) (λ X : 𝒞 => X)) : Full (G ∘ F) := by
  intro A B h
  obtain ⟨ηA_inv, hηA1, hηA2⟩ := η.isIso A
  obtain ⟨ηB_inv, hηB1, hηB2⟩ := η.isIso B
  refine ⟨ηA_inv ≫ h ≫ η.nat.app B, ?_⟩
  have nat := η.nat.naturality (ηA_inv ≫ h ≫ η.nat.app B)
  -- key: (G∘F)(f) ≫ η_B = h ≫ η_B  (from nat + collapsing η_A ≫ ηA_inv = id)
  have key : (compFunctor (hf := hF) (hg := hG)).map (ηA_inv ≫ h ≫ η.nat.app B) ≫
      η.nat.app B = h ≫ η.nat.app B := by
    rw [nat]; show η.nat.app A ≫ (ηA_inv ≫ h ≫ η.nat.app B) = h ≫ η.nat.app B
    rw [← Cat.assoc, ← Cat.assoc, hηA1, Cat.id_comp]
  -- cancel η_B on right
  have := congrArg (· ≫ ηB_inv) key
  simp only [Cat.assoc, hηB1, Cat.comp_id] at this
  exact this

private theorem compFG_full (δ : NatIso (F ∘ G) (λ X : 𝒟 => X)) : Full (F ∘ G) := by
  intro A B h
  obtain ⟨δA_inv, hδA1, hδA2⟩ := δ.isIso A
  obtain ⟨δB_inv, hδB1, hδB2⟩ := δ.isIso B
  refine ⟨δA_inv ≫ h ≫ δ.nat.app B, ?_⟩
  have nat := δ.nat.naturality (δA_inv ≫ h ≫ δ.nat.app B)
  have key : (compFunctor (hf := hG) (hg := hF)).map (δA_inv ≫ h ≫ δ.nat.app B) ≫
      δ.nat.app B = h ≫ δ.nat.app B := by
    rw [nat]; show δ.nat.app A ≫ (δA_inv ≫ h ≫ δ.nat.app B) = h ≫ δ.nat.app B
    rw [← Cat.assoc, ← Cat.assoc, hδA1, Cat.id_comp]
  have := congrArg (· ≫ δB_inv) key
  simp only [Cat.assoc, hδB1, Cat.comp_id] at this
  exact this

private theorem compGF_equivalenceFunctor (η : NatIso (G ∘ F) (λ X : 𝒞 => X)) :
    EquivalenceFunctor (G ∘ F) :=
  ⟨compGF_embedding η, compGF_full η, compGF_hasRepresentativeImage η⟩

private theorem compFG_equivalenceFunctor (δ : NatIso (F ∘ G) (λ X : 𝒟 => X)) :
    EquivalenceFunctor (F ∘ G) :=
  ⟨compFG_embedding δ, compFG_full δ, compFG_hasRepresentativeImage δ⟩

/-- In a strong equivalence (F, G), F is an embedding (§1.32). -/
theorem strongEquivalence_embedding_fwd (se : StrongEquivalence F G) : Embedding F := by
  obtain ⟨⟨η⟩, _⟩ := se
  exact embedding_of_comp_embedding (compGF_equivalenceFunctor η).1

/-- In a strong equivalence (F, G), G is an embedding (§1.32). -/
theorem strongEquivalence_embedding_bwd (se : StrongEquivalence F G) : Embedding G := by
  obtain ⟨_, ⟨δ⟩⟩ := se
  exact embedding_of_comp_embedding (compFG_equivalenceFunctor δ).1

/-- In a strong equivalence (F, G), F has a representative image (§1.32).
    The counit δ gives F(G D) ≅ D for any D. -/
theorem strongEquivalence_hasRepresentativeImage_fwd (se : StrongEquivalence F G) :
    HasRepresentativeImage F := by
  obtain ⟨_, ⟨δ⟩⟩ := se
  exact fun D => ⟨G D, δ.nat.app D, δ.isIso D⟩

/-- In a strong equivalence (F, G), G has a representative image (§1.32).
    The unit η gives G(F A) ≅ A for any A. -/
theorem strongEquivalence_hasRepresentativeImage_bwd (se : StrongEquivalence F G) :
    HasRepresentativeImage G := by
  obtain ⟨⟨η⟩, _⟩ := se
  exact fun A => ⟨F A, η.nat.app A, η.isIso A⟩

/-- In a strong equivalence (F, G), F is full (§1.32).
    Proof: G∘F ≅ id implies G∘F is full.  For h : FA → FB, G(h) : G(FA) → G(FB) = (G∘F)(A) → (G∘F)(B).
    By fullness of G∘F there exists f : A → B with (G∘F)(f) = G(h), i.e. G(F(f)) = G(h).
    Since G is an embedding (FG ≅ id gives embedding), F(f) = h. -/
theorem strongEquivalence_full_fwd (se : StrongEquivalence F G) : Full F := by
  obtain ⟨⟨η⟩, ⟨δ⟩⟩ := se
  have embG : Embedding G := embedding_of_comp_embedding (compFG_equivalenceFunctor δ).1
  have fullGF : Full (G ∘ F) := compGF_full η
  intro A B h
  -- G(h) : G(FA) ⟶ G(FB) = (G∘F)(A) ⟶ (G∘F)(B)
  obtain ⟨f, hf⟩ := fullGF (hG.map h)
  -- hf : (G∘F).map f = G(h), i.e. G(F(f)) = G(h)
  refine ⟨f, embG (hF.map f) h ?_⟩
  -- need G(F(f)) = G(h); hf says (G∘F).map f = G(h) = hG.map(hF.map f) = hG.map h
  simpa using hf

/-- In a strong equivalence (F, G), G is full (§1.32).
    Symmetric: F∘G ≅ id gives F∘G full; for h : GA → GB, F(h) lifts to some g with F(G(g)) = F(h);
    F is an embedding (GF ≅ id), so G(g) = h. -/
theorem strongEquivalence_full_bwd (se : StrongEquivalence F G) : Full G := by
  obtain ⟨⟨η⟩, ⟨δ⟩⟩ := se
  have embF : Embedding F := embedding_of_comp_embedding (compGF_equivalenceFunctor η).1
  have fullFG : Full (F ∘ G) := compFG_full δ
  intro A B h
  obtain ⟨g, hg⟩ := fullFG (hF.map h)
  refine ⟨g, embF (hG.map g) h ?_⟩
  simpa using hg

/-- In a strong equivalence (F, G), F is an equivalence functor (§1.32). -/
theorem strongEquivalence_equivalenceFunctor_fwd (se : StrongEquivalence F G) :
    EquivalenceFunctor F :=
  ⟨strongEquivalence_embedding_fwd se,
   strongEquivalence_full_fwd se,
   strongEquivalence_hasRepresentativeImage_fwd se⟩

/-- In a strong equivalence (F, G), G is an equivalence functor (§1.32). -/
theorem strongEquivalence_equivalenceFunctor_bwd (se : StrongEquivalence F G) :
    EquivalenceFunctor G :=
  ⟨strongEquivalence_embedding_bwd se,
   strongEquivalence_full_bwd se,
   strongEquivalence_hasRepresentativeImage_bwd se⟩

end StrongEquivIsEquiv

end Freyd
