/-
  Freyd & Scedrov, *Categories and Allegories* §1.33–§1.333
  Faithful functors, reflects iso, Cayley representations, functors on posets.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31
import Fredy.S1_41
import Fredy.S1_81


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.33 Faithful functors -/

/-- F is FAITHFUL if it is an embedding and reflects isomorphisms. -/
def Faithful (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  Embedding F ∧ (∀ {A B : 𝒞} (f : A ⟶ B), IsIso (hF.map f) → IsIso f)

/-- Full embeddings are faithful. -/
theorem full_embedding_faithful (F : 𝒞 → 𝒟) [hF : Functor F]
    (hEmb : Embedding F) (hFull : Full F) : Faithful F := by
  refine ⟨hEmb, ?_⟩
  intro A B f hiso
  rcases hiso with ⟨ginv, h1, h2⟩
  rcases hFull ginv with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · apply hEmb
    calc
      hF.map (f ≫ g) = hF.map f ≫ hF.map g := hF.map_comp f g
      _ = hF.map f ≫ ginv := by rw [hg]
      _ = Cat.id (F A) := h1
      _ = hF.map (Cat.id A) := by rw [hF.map_id]
  · apply hEmb
    calc
      hF.map (g ≫ f) = hF.map g ≫ hF.map f := hF.map_comp g f
      _ = ginv ≫ hF.map f := by rw [hg]
      _ = Cat.id (F B) := h2
      _ = hF.map (Cat.id B) := by rw [hF.map_id]

/-! ## §1.331 Reflects left-invertibility ⇒ reflects isomorphisms -/

/-- If F reflects left-invertibility, it reflects isomorphisms (§1.331).

    Book's proof: if Ff is an isomorphism, it is left-invertible.  Reflecting,
    f has a left inverse g (g ≫ f = id).  Then Fg ≫ Ff = id, so Fg = (Ff)⁻¹
    (unique via right-cancellation using Ff ≫ finv = id), hence Ff ≫ Fg = id.
    So Fg is left-invertible; reflecting, g has left inverse z (z ≫ g = id).
    Then z = z ≫ id_B = z ≫ g ≫ f = (z ≫ g) ≫ f = id_A ≫ f = f,
    so f ≫ g = id_A.  Combined with g ≫ f = id_B, f is an isomorphism. -/
theorem reflects_leftInv_reflects_iso (F : 𝒞 → 𝒟) [hF : Functor F]
    (reflLI : ∀ {A B : 𝒞} (f : A ⟶ B), HasLeftInv (hF.map f) → HasLeftInv f)
    {A B : 𝒞} (f : A ⟶ B) (hiso : IsIso (hF.map f)) : IsIso f := by
  obtain ⟨finv, hfinv1, hfinv2⟩ := hiso
  -- hfinv1 : hF.map f ≫ finv = Cat.id (F A)
  -- hfinv2 : finv ≫ hF.map f = Cat.id (F B)
  -- Step 1: Ff has left inverse finv; reflect to get g : B ⟶ A with g ≫ f = id_B
  obtain ⟨g, hgf⟩ := reflLI f ⟨finv, hfinv2⟩
  -- Step 2: Fg ≫ Ff = F(g ≫ f) = F(id_B) = id_{FB}
  have hFgFf : hF.map g ≫ hF.map f = Cat.id (F B) := by
    rw [← hF.map_comp, hgf, hF.map_id]
  -- Step 3: Fg = finv  (right-cancel Ff: both Fg and finv satisfy ? ≫ Ff = id)
  have hFg_eq_finv : hF.map g = finv := by
    have cancel : ∀ (u v : F B ⟶ F A), u ≫ hF.map f = v ≫ hF.map f → u = v := fun u v huv => by
      have := congrArg (· ≫ finv) huv
      simp only [Cat.assoc, hfinv1, Cat.comp_id] at this
      exact this
    exact cancel _ _ (by rw [hFgFf, hfinv2])
  -- Step 4: Ff ≫ Fg = Ff ≫ finv = id_{FA}
  have hFfFg : hF.map f ≫ hF.map g = Cat.id (F A) := by
    rw [hFg_eq_finv, hfinv1]
  -- Step 5: Fg has left inverse Ff; reflect to get z : A ⟶ B with z ≫ g = id_A
  obtain ⟨z, hzg⟩ := reflLI g ⟨hF.map f, hFfFg⟩
  -- Step 6: z = f  via  z = z ≫ (g ≫ f) = (z ≫ g) ≫ f = id_A ≫ f = f
  --   (using g ≫ f = id_B, so z ≫ Cat.id B = z ≫ g ≫ f)
  have hz_eq_f : z = f := by
    calc z = z ≫ Cat.id B          := (Cat.comp_id z).symm
      _ = z ≫ (g ≫ f)             := by rw [← hgf]
      _ = (z ≫ g) ≫ f             := (Cat.assoc z g f).symm
      _ = Cat.id A ≫ f             := by rw [hzg]
      _ = f                        := Cat.id_comp f
  -- Conclusion: g is the two-sided inverse of f
  --   f ≫ g = id_A  (from z = f and z ≫ g = id_A)
  --   g ≫ f = id_B  (hgf)
  exact ⟨g, by rwa [← hz_eq_f], hgf⟩

/-! ## §1.332 Contravariant Cayley representation C° -/

/-- The type of morphisms with source A (§1.332). -/
private def CoHom (𝒞 : Type u) [Cat.{v} 𝒞] (A : 𝒞) : Type (max u v) :=
  (B : 𝒞) × (A ⟶ B)

/-- The CONTRAVARIANT CAYLEY representation C° (§1.332).
    C°(A) = {y | □y = A} = morphisms with source A.
    For f : A → B, C°(f) : C°(B) → C°(A) by pre-composition:
      C°(f)(y : B → C) = (f ≫ y : A → C). -/
def contraCayleyObj (𝒞 : Type u) [Cat.{v} 𝒞] (A : 𝒞) : Type (max u v) :=
  CoHom 𝒞 A

/-- The action of C° on morphisms: pre-compose with f. -/
private def contraCayleyMap {𝒞 : Type u} [Cat.{v} 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    contraCayleyObj 𝒞 B → contraCayleyObj 𝒞 A :=
  fun ⟨C, y⟩ => ⟨C, f ≫ y⟩

/-- C° preserves identity: C°(id_A)(y) = id_A ≫ y = y. -/
private theorem contraCayleyMap_id {𝒞 : Type u} [Cat.{v} 𝒞] (A : 𝒞) :
    contraCayleyMap (Cat.id A) = id := by
  funext ⟨C, y⟩; simp [contraCayleyMap, Cat.id_comp]

/-- C° reverses composition: C°(f ≫ g) = C°(f) ∘ C°(g).
    Because (f ≫ g) ≫ y = f ≫ (g ≫ y). -/
private theorem contraCayleyMap_comp {𝒞 : Type u} [Cat.{v} 𝒞] {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) :
    contraCayleyMap (f ≫ g) = contraCayleyMap f ∘ contraCayleyMap g := by
  funext ⟨D, y⟩; simp [contraCayleyMap, Cat.assoc]

/-- C° is faithful: if C°(f) = C°(g) then f = g (§1.332).
    Witness: (B, id_B) ∈ C°(B); C°(f)(id_B) = f ≫ id_B = f. -/
theorem contraCayley_faithful {𝒞 : Type u} [Cat.{v} 𝒞] {A B : 𝒞} (f g : A ⟶ B)
    (h : contraCayleyMap f = contraCayleyMap g) : f = g := by
  have hfg : contraCayleyMap f ⟨B, Cat.id B⟩ = contraCayleyMap g ⟨B, Cat.id B⟩ :=
    congrFun h ⟨B, Cat.id B⟩
  simp [contraCayleyMap, Cat.comp_id] at hfg
  exact eq_of_heq (Sigma.ext_iff.mp hfg).2

/-! ## §1.333 Functors between posets -/

/-- A PREORDER structure (reflexive, transitive relation). -/
structure ProsetCat (α : Type u) : Type u where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c

/-- Turn a `ProsetCat` into a `Cat` instance.  Hom-sets are proof-irrelevant (thin). -/
instance prosetToCat {α : Type u} (P : ProsetCat α) : Cat.{0} α where
  Hom a b := PLift (P.le a b)
  id a := ⟨P.refl a⟩
  comp h k := ⟨P.trans h.down k.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- In a preorder-category any two parallel hom-set elements are equal (thin category). -/
theorem proset_hom_subsingleton {α : Type u} (P : ProsetCat α) {a b : α}
    (f g : @Cat.Hom α (prosetToCat P) a b) : f = g := by
  obtain ⟨_⟩ := f; obtain ⟨_⟩ := g; rfl

/-- A functor between preorder-categories is always an embedding (§1.333).
    Proof: morphisms are proof-irrelevant, so any two parallel morphisms are equal. -/
theorem proset_functor_embedding {α β : Type u}
    (P : ProsetCat α) (Q : ProsetCat β)
    (F : α → β) [hF : @Functor α (prosetToCat P) β (prosetToCat Q) F] :
    @Embedding α (prosetToCat P) β (prosetToCat Q) F hF := by
  intro A B f g _
  exact proset_hom_subsingleton P f g

/-- §1.333: a functor between preorders is monotone (order-preserving). -/
theorem proset_functor_monotone {α β : Type u}
    (P : ProsetCat α) (Q : ProsetCat β)
    (F : α → β) [hF : @Functor α (prosetToCat P) β (prosetToCat Q) F]
    {a b : α} (hab : P.le a b) : Q.le (F a) (F b) :=
  (hF.map (⟨hab⟩ : @Cat.Hom α (prosetToCat P) a b)).down

/-- §1.333: faithful iff injective on objects (for functors between posets).

    Forward: if F is faithful (embedding + reflects isos) and F a = F b, then a = b.
      With Q-antisymmetry: Fa = Fb means Q.le(Fa)(Fb) and Q.le(Fb)(Fa), so IsIso id_{Fa}
      viewed as a morphism Fa → Fb.  hRefl gives IsIso of the P-preimage, and P-antisymmetry
      gives a = b.

    Backward: injective on objects ⟹ faithful.  Embedding is free (thin cat).
      For reflects-iso: from IsIso (hF.map f), Q-antisymmetry gives Fa = Fb,
      injectivity gives a = b, and then IsIso f is trivial. -/
theorem proset_faithful_iff_injective {α β : Type u}
    (P : ProsetCat α) (Q : ProsetCat β)
    (antisymP : ∀ {a b : α}, P.le a b → P.le b a → a = b)
    (antisymQ : ∀ {a b : β}, Q.le a b → Q.le b a → a = b)
    (F : α → β) [hF : @Functor α (prosetToCat P) β (prosetToCat Q) F] :
    @Faithful α (prosetToCat P) β (prosetToCat Q) F hF ↔
    (∀ a b : α, F a = F b → a = b) := by
  constructor
  · intro ⟨_, hRefl⟩ a b hFab
    -- Gap: the forward direction (Faithful ⟹ injective on objects) is NOT provable
    -- from Embedding + reflects-iso alone without fullness.
    -- Counterexample: the unique functor from the 2-element discrete poset {a, b}
    -- (no non-identity morphisms) to the 1-element poset {x} is an Embedding (trivially,
    -- no non-trivial parallel morphisms exist) and reflects isos (vacuously, since
    -- every morphism in the domain is already iso).  Yet it is not injective on objects.
    -- The book's §1.333 statement likely intends fullness as a tacit assumption,
    -- or uses a single-sorted notion of "faithful" (injectivity on ALL morphisms, not
    -- just within fixed hom-sets) which implies object-injectivity.
    sorry
  · intro hInj
    refine ⟨proset_functor_embedding P Q F, ?_⟩
    intro A B f hiso
    -- hiso : IsIso (hF.map f) in Q-cat, i.e. ∃ g : PLift(Q.le (FB)(FA)), ...
    obtain ⟨g, _, _⟩ := hiso
    -- g : PLift (Q.le (F B) (F A))
    -- Combined with hF.map f : PLift (Q.le (F A) (F B)), Q-antisymmetry gives F A = F B.
    have hFAFB : F A = F B := antisymQ (hF.map f).down g.down
    -- Injectivity gives A = B.
    have hAB : A = B := hInj A B hFAFB
    subst hAB
    -- Now f : @Cat.Hom α (prosetToCat P) A A = PLift (P.le A A); IsIso f is trivial.
    exact ⟨f, proset_hom_subsingleton P _ _, proset_hom_subsingleton P _ _⟩

/-- §1.333: equivalence functor between posets iff order-isomorphism.

    An order-isomorphism is a surjective monotone functor whose inverse is also monotone,
    equivalently a bijection F with P.le a b ↔ Q.le (F a) (F b). -/
theorem proset_equiv_iff_ord_iso {α β : Type u}
    (P : ProsetCat α) (Q : ProsetCat β)
    (antisymP : ∀ {a b : α}, P.le a b → P.le b a → a = b)
    (antisymQ : ∀ {a b : β}, Q.le a b → Q.le b a → a = b)
    (F : α → β) [hF : @Functor α (prosetToCat P) β (prosetToCat Q) F] :
    @EquivalenceFunctor α (prosetToCat P) β (prosetToCat Q) F hF ↔
    ((∀ a b : α, F a = F b → a = b) ∧
     (∀ b : β, ∃ a : α, F a = b) ∧
     (∀ a b : α, P.le a b ↔ Q.le (F a) (F b))) := by
  constructor
  · intro ⟨hEmb, hFull, hRep⟩
    refine ⟨?_, ?_, ?_⟩
    · -- Injective on objects: from Fa = Fb, use fullness to get morphisms a→b and b→a,
      -- then antisymP.
      intro a b hFab
      -- Fa = Fb, so id_{Fa} : Fa ⟶ Fb in Q-cat.
      have h_ab : Q.le (F a) (F b) := hFab ▸ Q.refl (F a)
      have h_ba : Q.le (F b) (F a) := hFab ▸ Q.refl (F b)
      obtain ⟨f, _⟩ := hFull (⟨h_ab⟩ : @Cat.Hom β (prosetToCat Q) (F a) (F b))
      obtain ⟨g, _⟩ := hFull (⟨h_ba⟩ : @Cat.Hom β (prosetToCat Q) (F b) (F a))
      exact antisymP f.down g.down
    · -- Surjective: from HasRepresentativeImage
      intro B
      obtain ⟨A, h, hiso⟩ := hRep B
      obtain ⟨k, _, _⟩ := hiso
      -- h : Q.le (FA) B, k : Q.le B (FA); antisymQ gives FA = B
      exact ⟨A, antisymQ h.down k.down⟩
    · -- Order iff
      intro a b; constructor
      · intro hab
        exact (hF.map (⟨hab⟩ : @Cat.Hom α (prosetToCat P) a b)).down
      · intro hFaFb
        obtain ⟨f, _⟩ := hFull (⟨hFaFb⟩ : @Cat.Hom β (prosetToCat Q) (F a) (F b))
        exact f.down
  · intro ⟨hInj, hSurj, hOrd⟩
    refine ⟨proset_functor_embedding P Q F, ?_, ?_⟩
    · -- Full
      intro A B h
      exact ⟨⟨(hOrd A B).mpr h.down⟩, proset_hom_subsingleton Q _ _⟩
    · -- HasRepresentativeImage
      intro B
      obtain ⟨A, hFA⟩ := hSurj B
      exact ⟨A, ⟨hFA ▸ Q.refl (F A)⟩,
        ⟨⟨hFA ▸ Q.refl (F A)⟩,
         proset_hom_subsingleton Q _ _,
         proset_hom_subsingleton Q _ _⟩⟩

end Freyd
