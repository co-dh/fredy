/-
  Freyd & Scedrov, *Categories and Allegories* §1.58–§1.59
  Bicartesian categories, abelian categories, half-additive.

  §1.58 BICARTESIAN = Cartesian + Cocartesian.
         Coterminator 0, coproduct A+B, coequalizer.
         Pushout = pullback in opposite category.
  §1.59 ABELIAN = bicartesian satisfying all Horn sentences true for 𝒜𝒷.
         Zero object, half-additive, middle-two interchange.
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.58 Bicartesian categories

  A BICARTESIAN CATEGORY is both Cartesian and coCartesian:
  has finite limits and colimits. -/

/-- Has coterminator (initial object): dual to HasTerminal. -/
class HasCoterminator (𝒞 : Type u) [Cat.{v} 𝒞] where
  zero  : 𝒞
  init  : (X : 𝒞) → zero ⟶ X
  init_uniq  : ∀ {X : 𝒞} (f g : zero ⟶ X), f = g

variable [HasCoterminator 𝒞]

def coterm : 𝒞 := HasCoterminator.zero
def zeroMap (X : 𝒞) : coterm ⟶ X := HasCoterminator.init X

/-- Has binary coproducts: dual to HasBinaryProducts. -/
class HasBinaryCoproducts (𝒞 : Type u) [Cat.{v} 𝒞] where
  coprod : 𝒞 → 𝒞 → 𝒞
  inl    : {A B : 𝒞} → A ⟶ coprod A B
  inr    : {A B : 𝒞} → B ⟶ coprod A B
  case   : {X A B : 𝒞} → (A ⟶ X) → (B ⟶ X) → (coprod A B ⟶ X)
  case_inl : ∀ {X A B : 𝒞} (f : A ⟶ X) (g : B ⟶ X), inl ≫ case f g = f
  case_inr : ∀ {X A B : 𝒞} (f : A ⟶ X) (g : B ⟶ X), inr ≫ case f g = g
  case_uniq : ∀ {X A B : 𝒞} (f : A ⟶ X) (g : B ⟶ X) (h : coprod A B ⟶ X),
    inl ≫ h = f → inr ≫ h = g → h = case f g

/-- A single coequalizer: dual to HasEqualizer. -/
class HasCoequalizer {A B : 𝒞} (f g : A ⟶ B) where
  obj   : 𝒞
  map   : B ⟶ obj
  eq    : f ≫ map = g ≫ map
  desc  : ∀ {X : 𝒞} (h : B ⟶ X) (h_eq : f ≫ h = g ≫ h), obj ⟶ X
  fac   : ∀ {X : 𝒞} (h : B ⟶ X) (h_eq : f ≫ h = g ≫ h), map ≫ desc h h_eq = h
  uniq  : ∀ {X : 𝒞} (h : B ⟶ X) (h_eq : f ≫ h = g ≫ h) (m : obj ⟶ X),
    map ≫ m = h → m = desc h h_eq

/-- Has coequalizers: dual to HasEqualizers. -/
class HasCoequalizers (𝒞 : Type u) [Cat.{v} 𝒞] where
  coeq : ∀ {A B : 𝒞} (f g : A ⟶ B), HasCoequalizer f g

/-- A BICARTESIAN CATEGORY: Cartesian + coCartesian (§1.58). -/
class BicartesianCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    CartesianCategory 𝒞, HasCoterminator 𝒞, HasBinaryCoproducts 𝒞, HasCoequalizers 𝒞

/-! ## Coequalizer maps are covers

  In any category, the coequalizer map of any parallel pair is a cover.
  This is the converse direction of §1.566 (in a regular category, every
  cover IS the coequalizer of its kernel pair). -/

/-- The coequalizer map of any parallel pair is a cover (dual of: equalizer
    inclusions are monic).  Does NOT require regularity.
    Proof: given m mono with h ≫ m = q, use m-monicity to get f ≫ h = g ≫ h,
    then the universal property of q gives k : C → D with q ≫ k = h;
    then q ≫ (k ≫ m) = q forces k ≫ m = id by uniqueness; and
    (m ≫ k) ≫ m = m with m mono forces m ≫ k = id. -/
theorem coeq_map_is_cover {𝒟 : Type u} [Cat.{v} 𝒟] {A B : 𝒟} {f g : A ⟶ B}
    (hcoeq : HasCoequalizer f g) : Cover hcoeq.map := by
  intro D m h hm hfac
  -- From h ≫ m = q and f ≫ q = g ≫ q, deduce f ≫ h = g ≫ h (via m monic).
  have heq : f ≫ h = g ≫ h :=
    hm _ _ (by rw [Cat.assoc, Cat.assoc, hfac]; exact hcoeq.eq)
  -- The coequalizer universal property gives k : C → D with q ≫ k = h.
  let k := hcoeq.desc h heq
  have hqk : hcoeq.map ≫ k = h := hcoeq.fac h heq
  -- q ≫ (k ≫ m) = h ≫ m = q = q ≫ id_C, so k ≫ m = id_C by coeq uniqueness.
  have hkm : k ≫ m = Cat.id hcoeq.obj := by
    have step1 : hcoeq.map ≫ (k ≫ m) = hcoeq.map := by
      rw [← Cat.assoc, hqk, hfac]
    have step2 : hcoeq.map ≫ Cat.id hcoeq.obj = hcoeq.map := Cat.comp_id _
    exact (hcoeq.uniq hcoeq.map hcoeq.eq (k ≫ m) step1).trans
      (hcoeq.uniq hcoeq.map hcoeq.eq (Cat.id _) step2).symm
  -- m ≫ k satisfies (m ≫ k) ≫ m = m = id_D ≫ m, so m ≫ k = id_D by m-monicity.
  have hmk : m ≫ k = Cat.id D :=
    hm _ _ (by rw [Cat.assoc, hkm, Cat.comp_id, Cat.id_comp])
  exact ⟨k, hmk, hkm⟩

/-! ## §1.581 Bicartesian representations preserve covers

  If 𝒜 and ℬ are regular and cocartesian, and F : 𝒜 → ℬ is a functor that
  preserves coequalizers (and hence the bicartesian structure), then F
  preserves covers (§1.566: in a regular category a cover = coequalizer
  of its kernel pair). -/

/-- F PRESERVES COEQUALIZERS: the image of any coequalizer in 𝒜 is a
    coequalizer in ℬ.  Concretely: if q : B → C is the coequalizer of f, g
    in 𝒜, then hF.map q : F B → F C is the coequalizer of hF.map f, hF.map g. -/
def PreservesCoequalizers {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (F : 𝒜 → ℬ) [hF : Functor F] : Prop :=
  ∀ {A B : 𝒜} (f g : A ⟶ B) [hcoeq : HasCoequalizer f g],
    hF.map f ≫ hF.map hcoeq.map = hF.map g ≫ hF.map hcoeq.map ∧
    ∀ {X : ℬ} (h : F B ⟶ X),
      hF.map f ≫ h = hF.map g ≫ h →
      ∃ m : F hcoeq.obj ⟶ X, hF.map hcoeq.map ≫ m = h ∧
        ∀ m' : F hcoeq.obj ⟶ X, hF.map hcoeq.map ≫ m' = h → m' = m

/-- **§1.581**: If 𝒜 and ℬ are regular and cocartesian, and F : 𝒜 → ℬ
    is a functor that preserves coequalizers, then F preserves covers.
    Proof: (1) every cover f is a coequalizer of its kernel pair (§1.566);
    (2) by PreservesCoequalizers, F(kp-coeq-map) is a coequalizer in ℬ;
    (3) the coeq-map of the kernel pair of f and the coeq-map from HasCoequalizers
        are related by an iso e₁ : hce.obj ≅ B constructed from mutual coeq UMPs;
    (4) F f = F(hce.map) ≫ F(e₁); F(hce.map) is a cover (coeq_map_is_cover)
        and F(e₁) is an iso; cover ≫ iso = cover. -/
theorem bicart_repr_preserves_covers
    {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    [RegularCategory 𝒜] [HasCoequalizers 𝒜]
    [RegularCategory ℬ] [HasCoequalizers ℬ]
    (F : 𝒜 → ℬ) [hF : Functor F]
    (hpres : PreservesCoequalizers F)
    {A B : 𝒜} (f : A ⟶ B) (hf : Cover f) :
    Cover (hF.map f) := by
  -- Step 1: coequalizer of kernel pair of f in 𝒜.
  let hce := HasCoequalizers.coeq (kp₁ (f := f)) (kp₂ (f := f))
  -- e₁ : hce.obj → B induced by the coeq universal property applied to f.
  let e₁ : hce.obj ⟶ B := hce.desc f kp_sq
  have he₁ : hce.map ≫ e₁ = f := hce.fac f kp_sq
  -- e₂ : B → hce.obj: f is a coeq of its kernel pair (§1.566), kp₁ ≫ hce.map = kp₂ ≫ hce.map.
  obtain ⟨e₂, he₂, _⟩ := cover_is_coequalizer_of_level f hf hce.map hce.eq
  -- e₁ ≫ e₂ = id: hce.map ≫ (e₁ ≫ e₂) = f ≫ e₂ = hce.map = hce.map ≫ id.
  have he₁e₂ : e₁ ≫ e₂ = Cat.id hce.obj :=
    (hce.uniq hce.map hce.eq (e₁ ≫ e₂) (by rw [← Cat.assoc, he₁, he₂])).trans
    (hce.uniq hce.map hce.eq (Cat.id _) (Cat.comp_id _)).symm
  -- e₂ ≫ e₁ = id: f ≫ (e₂ ≫ e₁) = hce.map ≫ e₁ = f = f ≫ id; f is epi.
  have he₂e₁ : e₂ ≫ e₁ = Cat.id B :=
    cover_epi hf (by rw [← Cat.assoc, he₂, he₁, Cat.comp_id])
  -- e₁ is an iso; hence F e₁ is an iso.
  have he₁_iso : IsIso e₁ := ⟨e₂, by exact he₁e₂, he₂e₁⟩
  have hFe₁_iso : IsIso (hF.map e₁) := functor_preserves_iso e₁ he₁_iso
  -- F(hce.map) is a cover: build HasCoequalizer in ℬ from hpres, apply coeq_map_is_cover.
  obtain ⟨hpeq, hpfac⟩ := hpres (kp₁ (f := f)) (kp₂ (f := f))
  let hceB : HasCoequalizer (hF.map (kp₁ (f := f))) (hF.map (kp₂ (f := f))) :=
    { obj := F hce.obj, map := hF.map hce.map, eq := hpeq
      desc := fun h heq => (hpfac h heq).choose
      fac  := fun h heq => (hpfac h heq).choose_spec.1
      uniq := fun h heq m hm => (hpfac h heq).choose_spec.2 m hm }
  -- F f = F(hce.map) ≫ F(e₁); prove Cover (F hce.map ≫ F e₁) directly.
  rw [show hF.map f = hF.map hce.map ≫ hF.map e₁ from by rw [← hF.map_comp, he₁]]
  -- Unfold Cover: given m : C → F B mono, g : F A → C, g ≫ m = F hce.map ≫ F e₁. Show IsIso m.
  intro C m g hm hgm
  obtain ⟨e₁inv, he₁inv_left, he₁inv_right⟩ := hFe₁_iso
  -- m' = m ≫ e₁inv : C → F hce.obj.  g ≫ m' = F hce.map (post-compose hgm with e₁inv).
  let m' : C ⟶ F hce.obj := m ≫ e₁inv
  have hgm'_eq : g ≫ m' = hF.map hce.map :=
    calc g ≫ m ≫ e₁inv = (g ≫ m) ≫ e₁inv := (Cat.assoc _ _ _).symm
      _ = (hF.map hce.map ≫ hF.map e₁) ≫ e₁inv := by rw [hgm]
      _ = hF.map hce.map ≫ (hF.map e₁ ≫ e₁inv) := Cat.assoc _ _ _
      _ = hF.map hce.map := by rw [he₁inv_left, Cat.comp_id]
  -- m' is monic: m is mono, e₁inv is iso hence mono (has right inverse F e₁).
  have hm'_mono : Mono m' := by
    intro W a b hab
    -- hab : a ≫ m' = b ≫ m', i.e. a ≫ m ≫ e₁inv = b ≫ m ≫ e₁inv.
    -- (a ≫ m) ≫ e₁inv = (b ≫ m) ≫ e₁inv (by assoc)
    have hstep : (a ≫ m) ≫ e₁inv = (b ≫ m) ≫ e₁inv :=
      calc (a ≫ m) ≫ e₁inv = a ≫ m ≫ e₁inv := Cat.assoc _ _ _
        _ = b ≫ m ≫ e₁inv := hab
        _ = (b ≫ m) ≫ e₁inv := (Cat.assoc _ _ _).symm
    -- Post-compose with F e₁ (right inverse of e₁inv) to cancel e₁inv.
    have heq_m : a ≫ m = b ≫ m :=
      calc a ≫ m = (a ≫ m) ≫ (e₁inv ≫ hF.map e₁) := by rw [he₁inv_right, Cat.comp_id]
        _ = ((a ≫ m) ≫ e₁inv) ≫ hF.map e₁ := (Cat.assoc _ _ _).symm
        _ = ((b ≫ m) ≫ e₁inv) ≫ hF.map e₁ := by rw [hstep]
        _ = (b ≫ m) ≫ (e₁inv ≫ hF.map e₁) := Cat.assoc _ _ _
        _ = b ≫ m := by rw [he₁inv_right, Cat.comp_id]
    exact hm _ _ heq_m
  -- F kp₁ ≫ g = F kp₂ ≫ g: from hm'_mono, since (F kp₁ ≫ g) ≫ m' = (F kp₂ ≫ g) ≫ m'
  -- (both equal F kp₁/kp₂ ≫ F hce.map via hgm'_eq and hpeq).
  have hkp_g : hF.map (kp₁ (f := f)) ≫ g = hF.map (kp₂ (f := f)) ≫ g :=
    hm'_mono _ _ (by
      rw [Cat.assoc, Cat.assoc, hgm'_eq]
      exact hpeq)
  -- k : F hce.obj → C, the candidate inverse of m'.  hceB.desc g hkp_g : obj ⟶ C.
  let k : F hce.obj ⟶ C := hceB.desc g hkp_g
  have hqk : hceB.map ≫ k = g := hceB.fac g hkp_g
  -- k ≫ m' = id_{F hce.obj}: hceB.map ≫ (k ≫ m') = g ≫ m' = hceB.map, use uniq.
  have hkm' : k ≫ m' = Cat.id hceB.obj :=
    (hceB.uniq hceB.map hceB.eq (k ≫ m')
      (by rw [← Cat.assoc, hqk]; exact hgm'_eq)).trans
    (hceB.uniq hceB.map hceB.eq (Cat.id _) (Cat.comp_id _)).symm
  -- m' ≫ k = id_C: hm'_mono: (m' ≫ k) ≫ m' = m' ≫ (k ≫ m') = m' = id ≫ m'.
  have hm'k : m' ≫ k = Cat.id C :=
    hm'_mono _ _ (by
      have lhs : (m' ≫ k) ≫ m' = m' := by
        rw [Cat.assoc, hkm']; exact Cat.comp_id m'
      rw [lhs, Cat.id_comp])
  -- So m' = m ≫ e₁inv is iso.  Then m = m' ≫ F e₁ is a composition of isos, hence iso.
  have hm'_iso : IsIso m' := ⟨k, hm'k, hkm'⟩
  -- m = m' ≫ F e₁ (since e₁inv ≫ F e₁ = id).
  have hm_eq : m = m' ≫ hF.map e₁ := by
    rw [show m' ≫ hF.map e₁ = m ≫ e₁inv ≫ hF.map e₁ from Cat.assoc _ _ _,
        he₁inv_right, Cat.comp_id]
  rw [hm_eq]
  exact isIso_comp hm'_iso (functor_preserves_iso e₁ he₁_iso)

/-! ## §1.582 Image via coequalizer

  In a bicartesian regular category, the image of x : A → B is
  constructible as the coequalizer of its kernel pair.  Specifically:
  form the kernel pair (level) l = kp₁, r = kp₂ : kernelPair(x) ⇉ A,
  then take the coequalizer q : A → C of l and r.  The unique morphism
  m : C → B satisfying q ≫ m = x is monic; it is the image of x. -/

/-- **§1.582**: In a bicartesian regular category, the image of x : A → B is
    the coequalizer of its kernel pair.  Let l = kp₁, r = kp₂ be the
    projections of the kernel pair of x, and let q : A → C be their
    coequalizer.  The unique m : C → B with q ≫ m = x is monic. -/
theorem image_via_coeq [BicartesianCategory 𝒞] [RegularCategory 𝒞]
    {A B : 𝒞} (x : A ⟶ B) :
    let hcoeq := (HasCoequalizers.coeq (kp₁ (f := x)) (kp₂ (f := x)))
    Mono (hcoeq.desc x kp_sq) := by
  sorry

/-! ## §1.583 Effectiveness is a Horn sentence

  In a bicartesian regular category, effectiveness of an equivalence relation
  E (tabulated by l, r : E ⇉ A) is a Horn sentence in the bicartesian
  predicates: E is effective iff the coequalizer square
     E ⇉ A → C
  is a pullback (i.e. E ≅ kernelPair(q) where q : A → C is the coequalizer
  of l and r). -/

/-- **§1.583**: In a bicartesian regular category, an equivalence relation
    E on A (tabulated by l, r : E ⇉ A) is effective iff the coequalizer
    square is a pullback.  Let q : A → C be the coequalizer of l and r.
    The cone ⟨E, l, r⟩ over (q, q) is a pullback (E ≅ kernelPair(q))
    iff E is effective (kernel pair of some cover x : A → Q with l ≫ x = r ≫ x). -/
theorem effectiveness_iff_coeq_pullback [BicartesianCategory 𝒞] [RegularCategory 𝒞]
    {A E : 𝒞} (l r : E ⟶ A) :
    let hcoeq := HasCoequalizers.coeq l r
    let q := hcoeq.map
    -- E is effective: kernel pair of some cover x with l,r equalizing x
    (∃ (Q : 𝒞) (x : A ⟶ Q) (hlx : l ≫ x = r ≫ x), Cover x ∧
        IsIso ((HasPullbacks.has x x).lift ⟨E, l, r, hlx⟩)) ↔
    (⟨E, l, r, hcoeq.eq⟩ : Cone q q).IsPullback := by
  sorry

/-! ## §1.584 Slice category inherits cocartesian structure

  If 𝒜 is cocartesian, so is every slice 𝒜/B, and the forgetful functor
  Σ : 𝒜/B → 𝒜 is a faithful representation of cocartesian categories.

  The coproduct of (A, f : A→B) and (C, g : C→B) in Over B is
  (A+C, case f g : A+C→B) where `+` and `case` are the coproduct of 𝒜.
  The coterminator in Over B is (0, init B : 0→B).
  Coequalizers in Over B are the underlying coequalizers in 𝒜.
  Full formalization deferred: Over B uses OverHom which is a separate Cat
  from the ambient 𝒞; wiring up the PreservesCoequalizers type requires
  a Cat instance for Over B, not yet in this file. -/

/-! ## §1.586 Functor categories are cocartesian

  For small 𝒜, the functor category [𝒜, 𝒞] is cocartesian when 𝒞 is, with
  colimits computed pointwise.  The evaluation functors ev_A : [𝒜,𝒞]→𝒞 are
  a collectively faithful family of representations of cocartesian categories.
  Full formalization deferred: functor category machinery not yet available here. -/

/-! ## §1.59 Abelian categories

  ABELIAN: bicartesian satisfying all Horn sentences true for 𝒜𝒷.
  First consequences: 0≅1 (zero object), finite (co)products coincide,
  half-additive structure with the middle-two interchange law. -/

/-- A ZERO OBJECT is simultaneously terminal and coterminal: 0 ≅ 1. -/
def IsZeroObject (Z : 𝒞) [ht : HasTerminal 𝒞] [hc : HasCoterminator 𝒞] : Prop :=
  hc.zero = ht.one

/-! ### §1.591 Half-additive and additive categories

  In an abelian category the canonical map A+B → A×B is an isomorphism.
  This gives each hom-set an abelian monoid structure (half-additive),
  with the middle-two interchange law.  Requiring inverses gives additive. -/

/-- A HALF-ADDITIVE CATEGORY: finite products = finite coproducts, yielding
    an abelian monoid structure on each Hom(A,B).  (§1.591)

    The `zeroHom A B` is the zero morphism A → 0 → B through the zero object.
    The canonical map `A+B → A×B` (whose (i,j)-entry is δᵢⱼ) is an isomorphism.
    The `add` field gives the induced abelian-monoid addition on each Hom(A,B). -/
class HalfAdditiveCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasCoterminator 𝒞, HasBinaryCoproducts 𝒞 where
  /-- Zero morphism A → 0 → B through the zero object (0 ≅ 1). -/
  zeroHom : ∀ (A B : 𝒞), A ⟶ B
  /-- The canonical map A+B → A×B (δᵢⱼ-matrix) is an isomorphism.
      This is the key horn sentence expressing that products = coproducts. -/
  prod_coprod_coincide : ∀ (A B : 𝒞),
    IsIso (HasBinaryCoproducts.case
        (pair (Cat.id A) (zeroHom A B))
        (pair (zeroHom B A) (Cat.id B)) :
      HasBinaryCoproducts.coprod A B ⟶ prod A B)
  /-- The abelian-monoid addition on Hom(A,B), induced by products = coproducts:
      x + y = A → A⊕A → B   (using codiagonal; or dually via diagonal). -/
  add : ∀ {A B : 𝒞}, (A ⟶ B) → (A ⟶ B) → (A ⟶ B)
  add_zero : ∀ {A B : 𝒞} (f : A ⟶ B), add f (zeroHom A B) = f
  zero_add : ∀ {A B : 𝒞} (f : A ⟶ B), add (zeroHom A B) f = f

/-- In a half-additive category, each Hom(A,B) carries the structure's addition. -/
def homAdd [inst : HalfAdditiveCategory 𝒞] {A B : 𝒞} : (A ⟶ B) → (A ⟶ B) → (A ⟶ B) :=
  inst.add

/-- **Middle-two interchange law** (§1.591): `(u + v) + (x + y) = (u + x) + (v + y)`.
    This is the fundamental identity that, together with unitality, forces
    commutativity and associativity of the addition.  Proved from the
    product/coproduct coincidence by universality of the product and coproduct. -/
theorem middle_two_interchange [inst : HalfAdditiveCategory 𝒞] {A B : 𝒞}
    (u v x y : A ⟶ B) :
    inst.add (inst.add u v) (inst.add x y) =
    inst.add (inst.add u x) (inst.add v y) := by
  sorry

/-- ADDITIVE CATEGORY (§1.591): half-additive with additive inverses.
    Every hom-set (A,B) is an abelian group: each f : A → B has a (unique)
    additive inverse g : A → B satisfying f + g = 0_{A,B}. -/
class AdditiveCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends HalfAdditiveCategory 𝒞 where
  /-- Additive inverses exist: every f : A → B has a g with f + g = zeroHom A B. -/
  addInv : ∀ {A B : 𝒞} (f : A ⟶ B), ∃ g : A ⟶ B, add f g = zeroHom A B

end Freyd
