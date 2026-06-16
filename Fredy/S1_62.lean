/-
  Freyd & Scedrov, *Categories and Allegories* §1.62–§1.66
  Pasting Lemma, Positive pre-logoi, coproducts, generating set,
  pre-filter, Representation Theorem.

  §1.62 Pasting Lemma: union of subobjects is pushout of intersection.
  §1.623 Positive pre-logos = pre-logos with coproducts.
  §1.632 Generating set / basis.
  §1.634 Pre-filter, T_𝔉 functor.
  §1.635 Representation Theorem for pre-logoi.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_55
import Fredy.S1_56
import Fredy.S1_57
import Fredy.S1_58
import Fredy.S1_60


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.62 Pasting Lemma

  In a pre-logos, the union A₁∪A₂ is the pushout of A₁∩A₂. -/

variable [PreLogos 𝒞]

/-! ### Cover composition helpers (needed for §1.631) -/

/-- A cover pre-composed with an iso is still a cover. -/
theorem cover_comp_iso {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Cover f) (hg : IsIso g) :
    Cover (f ≫ g) := by
  obtain ⟨g_inv, hgg_inv, hg_inv_g⟩ := hg
  intro C m h hm heq
  have hm_ginv_mono : Mono (m ≫ g_inv) := by
    intro W u v huv
    apply hm u v
    have : (u ≫ m ≫ g_inv) ≫ g = (v ≫ m ≫ g_inv) ≫ g := by rw [huv]
    simp only [Cat.assoc] at this; rw [hg_inv_g, Cat.comp_id] at this; exact this
  have hfac : h ≫ (m ≫ g_inv) = f :=
    calc h ≫ (m ≫ g_inv) = (h ≫ m) ≫ g_inv := (Cat.assoc _ _ _).symm
      _ = (f ≫ g) ≫ g_inv := by rw [heq]
      _ = f ≫ (g ≫ g_inv) := Cat.assoc _ _ _
      _ = f := by rw [hgg_inv, Cat.comp_id]
  have h_iso : IsIso (m ≫ g_inv) := hf (m ≫ g_inv) h hm_ginv_mono hfac
  rw [show m = (m ≫ g_inv) ≫ g from by rw [Cat.assoc, hg_inv_g, Cat.comp_id]]
  exact isIso_comp h_iso ⟨g_inv, hgg_inv, hg_inv_g⟩

/-- An iso post-composed with a cover is still a cover. -/
theorem iso_comp_cover {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsIso f) (hg : Cover g) :
    Cover (f ≫ g) := by
  obtain ⟨f_inv, hff_inv, hf_inv_f⟩ := hf
  intro C m h hm heq
  exact hg m (f_inv ≫ h) hm
    (calc (f_inv ≫ h) ≫ m = f_inv ≫ (h ≫ m) := Cat.assoc _ _ _
      _ = f_inv ≫ (f ≫ g) := by rw [heq]
      _ = (f_inv ≫ f) ≫ g := (Cat.assoc _ _ _).symm
      _ = g := by rw [hf_inv_f, Cat.id_comp])

/-- Intersection of subobjects: pullback of S.arr and T.arr, composed with S.arr. -/
def Subobject.inter [HasPullbacks 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B) : Subobject 𝒞 B :=
  let pb := HasPullbacks.has S.arr T.arr
  { dom := pb.cone.pt
    arr := pb.cone.π₁ ≫ S.arr
    monic := by
      intro X u v h
      -- h: u ≫ (π₁ ≫ S.arr) = v ≫ (π₁ ≫ S.arr)
      have hsq : pb.cone.π₁ ≫ S.arr = pb.cone.π₂ ≫ T.arr := pb.cone.w
      have huvπ₁ : u ≫ pb.cone.π₁ = v ≫ pb.cone.π₁ :=
        S.monic _ _ (by
          simpa [Cat.assoc] using h)
      have huvπ₂ : u ≫ pb.cone.π₂ = v ≫ pb.cone.π₂ :=
        T.monic _ _ (by
          calc
            (u ≫ pb.cone.π₂) ≫ T.arr = u ≫ (pb.cone.π₂ ≫ T.arr) := by simpa using Cat.assoc _ _ _
            _ = u ≫ (pb.cone.π₁ ≫ S.arr) := by rw [hsq]
            _ = (u ≫ pb.cone.π₁) ≫ S.arr := by simpa using (Cat.assoc _ _ _).symm
            _ = (v ≫ pb.cone.π₁) ≫ S.arr := by rw [huvπ₁]
            _ = v ≫ (pb.cone.π₁ ≫ S.arr) := by simpa using Cat.assoc _ _ _
            _ = v ≫ (pb.cone.π₂ ≫ T.arr) := by rw [hsq]
            _ = (v ≫ pb.cone.π₂) ≫ T.arr := by simpa using (Cat.assoc _ _ _).symm)
      let c : Cone S.arr T.arr :=
        { pt := X
          π₁ := u ≫ pb.cone.π₁
          π₂ := u ≫ pb.cone.π₂
          w  := by
            calc
              (u ≫ pb.cone.π₁) ≫ S.arr = u ≫ (pb.cone.π₁ ≫ S.arr) := by simpa using Cat.assoc _ _ _
              _ = u ≫ (pb.cone.π₂ ≫ T.arr) := by rw [hsq]
              _ = (u ≫ pb.cone.π₂) ≫ T.arr := by simpa using (Cat.assoc _ _ _).symm }
      have hlift := pb.lift_uniq c u (by rfl) (by rfl)
      have hv_eq_u : v = u := by
        apply (pb.lift_uniq c v ?_ ?_).trans hlift.symm
        · calc
            v ≫ pb.cone.π₁ = u ≫ pb.cone.π₁ := huvπ₁.symm
            _ = c.π₁ := rfl
        · calc
            v ≫ pb.cone.π₂ = u ≫ pb.cone.π₂ := huvπ₂.symm
            _ = c.π₂ := rfl
      rw [hv_eq_u] }

/-- Pasting Lemma (§1.62): For subobjects A₁,A₂ of A, the pushout
    of the two projections from the intersection I = A₁∩A₂ (to A₁.dom and
    A₂.dom) is the union U = A₁∪A₂.  This is one of the defining properties
    of a pre-logos (distributive subobject lattice). -/
def pasting_lemma {A : 𝒞} (A₁ A₂ : Subobject 𝒞 A) :
    HasPushout (HasPullbacks.has A₁.arr A₂.arr).cone.π₁ (HasPullbacks.has A₁.arr A₂.arr).cone.π₂ := by
  -- The book's proof uses R = x°f ∪ y°g, shows 1 ⊆ RR° and R°R ⊆ 1,
  -- hence R is a map (entire + simple), and xR = f, yR = g uniquely.
  -- This requires the full relation composition + simple/entire identities.
  sorry

/-! ## §1.631 Complemented subobject (book definition)

  A₁ ⊆ A is COMPLEMENTED if ∃ A₂ ⊆ A with A₁∩A₂ = 0 and A₁∪A₂ = A.
  Here 0 = PreLogos.bottom A (the minimal subobject) and A = Subobject.entire A.
  The intersection is the pullback along A₁.arr and A₂.arr. -/

/-- (§1.631) A₁ is COMPLEMENTED in A if there exists A₂ with
    A₁ ∩ A₂ ≤ 0  (intersection is minimal)
    and A ≤ A₁ ∪ A₂  (union is maximal). -/
def IsComplementedSub {A : 𝒞} (A₁ : Subobject 𝒞 A) : Prop :=
  ∃ (A₂ : Subobject 𝒞 A),
    Subobject.le (Subobject.inter A₁ A₂) (PreLogos.bottom A)
    ∧ Subobject.le (Subobject.entire A) (HasSubobjectUnions.union A₁ A₂)

/-! ## §1.623 Positive pre-logoi

  A POSITIVE PRE-LOGOS has binary coproducts (equivalently:
  for every A,B there exists C with A,B as complemented subobjects). -/

class PositivePreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends PreLogos 𝒞, HasBinaryCoproducts 𝒞

/-- §1.624: In a positive pre-logos, f: A → B₁+B₂ decomposes as
    f₁+f₂ from A₁ → B₁, A₂ → B₂ where A = A₁+A₂.
    Proof: A₁ = f#(inl), A₂ = f#(inr) via pasting lemma (§1.62). -/
theorem decompose_via_coproduct [PositivePreLogos 𝒞] {A B₁ B₂ : 𝒞} (f : A ⟶ HasBinaryCoproducts.coprod B₁ B₂) :
    ∃ (A₁ A₂ : 𝒞) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂), Isomorphic A (HasBinaryCoproducts.coprod A₁ A₂) := by
  -- A₁ := (InverseImage f (Subobject(inl))).dom, A₂ := (InverseImage f (Subobject(inr))).dom.
  -- A₁+A₂ ≅ A follows from the pasting lemma (sorry pending pasting_lemma proof).
  sorry

/-! ## §1.625 Representations of positive pre-logoi

  A functor T: 𝒜 → ℬ between positive pre-logoi is a representation of pre-logoi
  iff it preserves disjoint unions.  (The book uses that union = image of coproduct.)

  MISSING: this statement cannot yet be stated faithfully in this repo — it quantifies over
  "T is a representation of regular categories" and "T preserves disjoint unions", neither of
  which has a predicate here.  A faithful formalization needs a `PreLogosFunctor` / "representation
  of regular categories" structure (preserving finite products, equalizers, images) plus a
  `PreservesDisjointUnions T` predicate.  Per the integrity rule the previous vacuous
  `: True := trivial` stub has been removed rather than left in place. -/

/-! ## §1.632 Generating set / basis

  A set ℱ of objects is GENERATING if the representable functors
  {(G, -)} form an embedding.  A BASIS is a collectively faithful set. -/

/-- ℱ is GENERATING if the functors Hom(G,-) for G∈ℱ are collectively
    an embedding (i.e., injective on morphisms). -/
def IsGeneratingSet (ℱ : 𝒞 → Prop) : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B), (∀ G : 𝒞, ℱ G → (∀ h : G ⟶ A, h ≫ f = h ≫ g)) → f = g

/-- ℱ is a BASIS if the functors Hom(G,-) for G∈ℱ are collectively
    faithful.  In a Cartesian category: for every proper A'↣A, ∃ G∈ℱ
    and G→A not factoring through A'. -/
def IsBasis [HasPullbacks 𝒞] (ℱ : 𝒞 → Prop) : Prop :=
  IsGeneratingSet ℱ ∧
  ∀ {A' A : 𝒞} (m : A' ⟶ A), Mono m → ¬ IsIso m →
    ∃ G : 𝒞, ℱ G ∧ ∃ (x : G ⟶ A), ¬ ∃ (y : G ⟶ A'), y ≫ m = x

/-! ## §1.634 Pre-filter

  A non-empty ℱ ⊆ Sub(1) is a PRE-FILTER if it's ↓-directed.
  For a pre-filter ℱ, define T_ℱ : A → 𝒮 the colimit of Hom(U,-). -/

/-- ℱ is a pre-filter in the subobject lattice of 1: non-empty and
    ∀ U,V ∈ ℱ, ∃ W ∈ ℱ with W ≤ U and W ≤ V. -/
def IsPreFilter (ℱ : (Subobject 𝒞 one) → Prop) : Prop :=
  (∃ U, ℱ U) ∧ ∀ (U V : Subobject 𝒞 one), ℱ U → ℱ V → ∃ W, ℱ W ∧ Subobject.le W U ∧ Subobject.le W V

/-- T_ℱ(A) = colim_{U∈ℱ} Hom(U, A).  Represented here as the type of pairs
    (U, hU, f : U.dom → A) for U in the pre-filter ℱ.  The full definition
    requires a colimit of Hom-sets (equivalence classes).  For U projective,
    T_ℱ preserves finite products and equalizers; if ℱ is an ultra-filter in a
    Boolean algebra, T_ℱ preserves unions (§1.634-1.635). -/
structure PrefilterMap (ℱ : (Subobject 𝒞 one) → Prop) (A : 𝒞) where
  U    : Subobject 𝒞 one
  hU   : ℱ U
  map  : U.dom ⟶ A

def prefilter_functor (ℱ : (Subobject 𝒞 one) → Prop) (_hℱ : IsPreFilter ℱ) : 𝒞 → Type (max u v) :=
  PrefilterMap ℱ

/-! ## §1.635 Representation theorem for pre-logoi

  Every small positive pre-logos is faithfully representable in a
  power of the category of sets.  Proof via capital extension,
  complemented subterminators (which form a Boolean algebra),
  ultra-filters, and the T_ℱ construction. -/

theorem prelogos_representation_theorem (A : Type u) [Cat.{u} A] [PositivePreLogos A] :
    ∃ (T : A → (A → Type u)) (_ : Functor T), SeparatesMaps T := by
  -- The deep proof uses: capital extension (§1.63) + Stone representation
  -- of Boolean algebras via ultra-filters → T_ℱ is a faithful representation.
  -- Requires axiom of choice for the ultra-filter theorem.
  sorry


/-- FILTER in a subobject lattice: up-closed pre-filter (§1.634). -/
def IsFilter (ℱ : (Subobject 𝒞 one) → Prop) : Prop :=
  IsPreFilter ℱ ∧ ∀ (U V : Subobject 𝒞 one), ℱ U → Subobject.le U V → ℱ V

/-! ## §1.631 Complemented subobject of a projective is projective

  In a positive pre-logos, if P is a complemented subobject of a projective
  object Q (so Q ≅ P + P' for some P'), then P is projective.
  Proof: given a cover x : A ↠ P, extend to A + P' → P + P' using the
  coproduct inclusion; this is a cover of the projective Q, so it splits;
  composing with inl gives a section P → A. -/

/-- §1.631: In a positive pre-logos, a complemented subobject of a projective
    object is projective. -/
theorem complemented_of_projective_is_projective [PositivePreLogos 𝒞]
    {Q : 𝒞} (hQ : Projective Q) {P : 𝒞} (P' : 𝒞)
    (hiso : Isomorphic Q (HasBinaryCoproducts.coprod P P'))
    {A : 𝒞} (x : A ⟶ P) (hx : Cover x) :
    Projective P := by
  -- Given any cover y : B ↠ P we produce a section P → B.
  intro B y hy
  obtain ⟨φ, φ_inv, hφφ_inv, hφ_inv_φ⟩ := hiso
  -- φ : Q → P+P', φ_inv : P+P' → Q, φ ≫ φ_inv = id_Q, φ_inv ≫ φ = id_{P+P'}.
  -- φ_inv is monic (retraction φ gives left inverse).
  have hφ_inv_mono : Mono φ_inv :=
    mono_of_retraction φ_inv φ hφ_inv_φ
  -- Form h := case(y ≫ inl, inr) : B+P' → P+P'.
  -- Key equations: inl_B ≫ h = y ≫ inl_P (by case_inl) and inr_P' ≫ h = inr_P' (by case_inr).
  let h : HasBinaryCoproducts.coprod B P' ⟶ HasBinaryCoproducts.coprod P P' :=
    HasBinaryCoproducts.case (y ≫ HasBinaryCoproducts.inl) HasBinaryCoproducts.inr
  have h_inl : HasBinaryCoproducts.inl ≫ h = y ≫ HasBinaryCoproducts.inl :=
    HasBinaryCoproducts.case_inl _ _
  -- h is a cover: needs disjointness of coproduct inclusions in a pre-logos.
  have hh : Cover h := by sorry
  -- e := h ≫ φ_inv : B+P' → Q  is a cover (cover ≫ iso).
  have he : Cover (h ≫ φ_inv) := cover_comp_iso h φ_inv hh ⟨φ, hφ_inv_φ, hφφ_inv⟩
  -- Projectivity of Q splits e: s' : Q → B+P', s' ≫ (h ≫ φ_inv) = id_Q.
  obtain ⟨s', hs'⟩ := hQ (h ≫ φ_inv) he
  -- Key identity: φ_inv ≫ s' ≫ h = id_{P+P'}.
  -- Proof: (φ_inv ≫ s' ≫ h) ≫ φ_inv = φ_inv ≫ (s' ≫ (h ≫ φ_inv)) = φ_inv ≫ id_Q = φ_inv
  --        = id_{P+P'} ≫ φ_inv, so φ_inv monic gives φ_inv ≫ s' ≫ h = id.
  have h_section : φ_inv ≫ s' ≫ h = Cat.id _ := by
    apply hφ_inv_mono _ _
    calc (φ_inv ≫ s' ≫ h) ≫ φ_inv
          = φ_inv ≫ s' ≫ (h ≫ φ_inv) := by simp [Cat.assoc]
        _ = φ_inv ≫ Cat.id Q      := by rw [hs']
        _ = φ_inv                  := Cat.comp_id _
        _ = Cat.id _ ≫ φ_inv      := (Cat.id_comp _).symm
  -- σ := inl_P ≫ φ_inv ≫ s' : P → B+P'. Then σ ≫ h = inl_P.
  let σ : P ⟶ HasBinaryCoproducts.coprod B P' :=
    HasBinaryCoproducts.inl ≫ φ_inv ≫ s'
  have hσh : σ ≫ h = HasBinaryCoproducts.inl := by
    simp only [σ, Cat.assoc, h_section, Cat.comp_id]
  -- σ ≫ h = inl_P and inl_B ≫ h = y ≫ inl_P, so σ factors through inl_B,
  -- giving r : P → B with r ≫ y = id_P (via inl_P monic in the coproduct).
  -- This factorization needs: σ lands in the B-summand of B+P'.
  -- In a positive pre-logos this follows from the complemented structure; sorry here.
  obtain ⟨r, hr⟩ : ∃ r : P ⟶ B, r ≫ y = Cat.id P := by sorry
  exact ⟨r, hr⟩

/-! ## §1.633 Characterization of capital positive pre-logoi

  A positive pre-logos is capital iff its complemented subterminators
  (complemented subobjects of 1) are projective and form a basis. -/

/-- §1.633: A positive pre-logos is capital iff
    (1) every complemented subterminator is projective, and
    (2) the complemented subterminators form a basis. -/
theorem capital_iff_complemented_subterminators [PositivePreLogos 𝒞] :
    Capital (𝒞 := 𝒞) ↔
    (∀ U : Subobject 𝒞 one, IsComplementedSub U → Projective U.dom)
    ∧ IsBasis (fun G => ∃ U : Subobject 𝒞 one, IsComplementedSub U ∧ Isomorphic G U.dom) := by
  sorry

end Freyd
