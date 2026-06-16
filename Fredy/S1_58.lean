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
  intro hcoeq
  -- q : A → C is the coeq map, m : C → B the unique factorization.
  have hq : Cover hcoeq.map := coeq_map_is_cover hcoeq
  -- Image factorization of x: e cover, I.arr monic.
  have hi_mono : Mono (image x).arr := (image x).monic
  have he_cover : Cover (image.lift x) := image_lift_cover x
  -- kp₁(x) ≫ e = kp₂(x) ≫ e: kp_sq gives kp₁ ≫ x = kp₂ ≫ x; I.arr monic cancels.
  have hkp_e : kp₁ (f := x) ≫ image.lift x = kp₂ (f := x) ≫ image.lift x :=
    hi_mono _ _
      (calc (kp₁ (f:=x) ≫ image.lift x) ≫ (image x).arr
          = kp₁ (f:=x) ≫ x := by rw [Cat.assoc]; exact congrArg (kp₁ (f:=x) ≫ ·) (image.lift_fac x)
        _ = kp₂ (f:=x) ≫ x := kp_sq
        _ = (kp₂ (f:=x) ≫ image.lift x) ≫ (image x).arr := by rw [Cat.assoc]; exact (congrArg (kp₂ (f:=x) ≫ ·) (image.lift_fac x)).symm)
  -- φ : C → I.dom from coeq UMP applied to (image.lift x).
  have hqφ : hcoeq.map ≫ hcoeq.desc (image.lift x) hkp_e = image.lift x :=
    hcoeq.fac (image.lift x) hkp_e
  -- m = φ ≫ I.arr: q ≫ m = x = e ≫ I.arr = q ≫ φ ≫ I.arr, so cover_epi q.
  have hm_eq : hcoeq.desc x kp_sq =
      hcoeq.desc (image.lift x) hkp_e ≫ (image x).arr :=
    cover_epi hq (by
      rw [hcoeq.fac x kp_sq, ← Cat.assoc, hqφ, image.lift_fac])
  -- kp₁(e) ≫ q = kp₂(e) ≫ q: lift kp_sq(e) into kernelPair(x), then use hcoeq.eq.
  have hkp_eq_q : kp₁ (f := image.lift x) ≫ hcoeq.map = kp₂ (f := image.lift x) ≫ hcoeq.map := by
    -- kp₁(e) ≫ x = kp₂(e) ≫ x via kp_sq(e) and image factorization.
    have hke_x : kp₁ (f := image.lift x) ≫ x = kp₂ (f := image.lift x) ≫ x :=
      calc kp₁ (f:=image.lift x) ≫ x
          = kp₁ (f:=image.lift x) ≫ image.lift x ≫ (image x).arr := by rw [image.lift_fac]
        _ = (kp₁ (f:=image.lift x) ≫ image.lift x) ≫ (image x).arr := (Cat.assoc _ _ _).symm
        _ = (kp₂ (f:=image.lift x) ≫ image.lift x) ≫ (image x).arr := by
              exact congrArg (· ≫ _) kp_sq
        _ = kp₂ (f:=image.lift x) ≫ image.lift x ≫ (image x).arr := Cat.assoc _ _ _
        _ = kp₂ (f:=image.lift x) ≫ x := by rw [image.lift_fac]
    -- Lift l : kernelPair(e) → kernelPair(x) via the pullback.
    have hl₁ := kp_lift_p₁ (kp₁ (f:=image.lift x)) (kp₂ (f:=image.lift x)) hke_x
    have hl₂ := kp_lift_p₂ (kp₁ (f:=image.lift x)) (kp₂ (f:=image.lift x)) hke_x
    -- kp₁(e) ≫ q = l ≫ kp₁(x) ≫ q = l ≫ kp₂(x) ≫ q = kp₂(e) ≫ q.
    -- Naming l avoids repeated long expression; no rw to sidestep motive issues.
    let l := (HasPullbacks.has x x).lift
      ⟨_, kp₁ (f:=image.lift x), kp₂ (f:=image.lift x), hke_x⟩
    -- step1: kp₁(e) ≫ q = (l ≫ kp₁(x)) ≫ q  [from hl₁]
    -- step2: (l ≫ kp₁(x)) ≫ q = l ≫ (kp₁(x) ≫ q)  [assoc]
    -- step3: l ≫ (kp₁(x) ≫ q) = l ≫ (kp₂(x) ≫ q)  [hcoeq.eq]
    -- step4: l ≫ (kp₂(x) ≫ q) = (l ≫ kp₂(x)) ≫ q  [assoc.symm]
    -- step5: (l ≫ kp₂(x)) ≫ q = kp₂(e) ≫ q  [from hl₂]
    exact (congrArg (· ≫ hcoeq.map) hl₁.symm).trans
      ((Cat.assoc l _ _).trans
        ((congrArg (l ≫ ·) hcoeq.eq).trans
          ((Cat.assoc l _ _).symm.trans (congrArg (· ≫ hcoeq.map) hl₂))))
  -- ψ : I.dom → C from cover_is_coequalizer_of_level applied to (image.lift x).
  obtain ⟨ψ, heψ, _⟩ :=
    cover_is_coequalizer_of_level (image.lift x) he_cover hcoeq.map hkp_eq_q
  -- φ ≫ ψ = id_C (cover_epi hq) and ψ ≫ φ = id (cover_epi he_cover).
  have hφψ : hcoeq.desc (image.lift x) hkp_e ≫ ψ = Cat.id hcoeq.obj :=
    cover_epi hq (by rw [← Cat.assoc, hqφ, heψ, Cat.comp_id])
  -- Mono m: given u ≫ m = v ≫ m, rewrite via hm_eq to use φ,I.arr.
  intro W u v huv
  -- First get u ≫ φ ≫ I.arr = v ≫ φ ≫ I.arr from huv via hm_eq.
  have huv' : u ≫ hcoeq.desc (image.lift x) hkp_e ≫ (image x).arr =
               v ≫ hcoeq.desc (image.lift x) hkp_e ≫ (image x).arr := by
    rw [← hm_eq]; exact huv
  -- Cancel I.arr (monic) to get u ≫ φ = v ≫ φ.
  have hφ_eq : u ≫ hcoeq.desc (image.lift x) hkp_e = v ≫ hcoeq.desc (image.lift x) hkp_e :=
    hi_mono _ _ (by rw [Cat.assoc, Cat.assoc]; exact huv')
  -- Cancel φ using its right-inverse ψ.
  calc u = u ≫ (hcoeq.desc (image.lift x) hkp_e ≫ ψ) := by rw [hφψ, Cat.comp_id]
    _ = (u ≫ hcoeq.desc (image.lift x) hkp_e) ≫ ψ := (Cat.assoc _ _ _).symm
    _ = (v ≫ hcoeq.desc (image.lift x) hkp_e) ≫ ψ := by rw [hφ_eq]
    _ = v ≫ (hcoeq.desc (image.lift x) hkp_e ≫ ψ) := Cat.assoc _ _ _
    _ = v := by rw [hφψ, Cat.comp_id]

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
  intro hcoeq q
  constructor
  · -- Forward: effective ⇒ coeq square is a pullback.
    rintro ⟨Q, x, hlx, hx_cover, ⟨k_inv, hk_left, hk_right⟩⟩
    -- k : E → kernelPair(x), the chosen iso into the kernel pair of x.
    let k : E ⟶ kernelPair x := (HasPullbacks.has x x).lift ⟨E, l, r, hlx⟩
    have hk_p₁ : k ≫ kp₁ (f := x) = l := kp_lift_p₁ l r hlx
    have hk_p₂ : k ≫ kp₂ (f := x) = r := kp_lift_p₂ l r hlx
    -- m : C → Q with q ≫ m = x (coeq factorization of x through q).
    let m : hcoeq.obj ⟶ Q := hcoeq.desc x hlx
    have hqm : q ≫ m = x := hcoeq.fac x hlx
    -- k_inv ≫ l = kp₁(x), k_inv ≫ r = kp₂(x).
    have hkinv_l : k_inv ≫ l = kp₁ (f := x) :=
      calc k_inv ≫ l = k_inv ≫ (k ≫ kp₁ (f := x)) := by rw [hk_p₁]
        _ = (k_inv ≫ k) ≫ kp₁ (f := x) := (Cat.assoc _ _ _).symm
        _ = kp₁ (f := x) := by rw [hk_right, Cat.id_comp]
    have hkinv_r : k_inv ≫ r = kp₂ (f := x) :=
      calc k_inv ≫ r = k_inv ≫ (k ≫ kp₂ (f := x)) := by rw [hk_p₂]
        _ = (k_inv ≫ k) ≫ kp₂ (f := x) := (Cat.assoc _ _ _).symm
        _ = kp₂ (f := x) := by rw [hk_right, Cat.id_comp]
    intro d
    -- d.π₁ ≫ x = d.π₂ ≫ x (from d.w : d.π₁ ≫ q = d.π₂ ≫ q).
    have hdx : d.π₁ ≫ x = d.π₂ ≫ x := by
      rw [← hqm, ← Cat.assoc, ← Cat.assoc, d.w]
    -- kd : d.pt → kernelPair(x) lifting (d.π₁, d.π₂).
    let kd : d.pt ⟶ kernelPair x := (HasPullbacks.has x x).lift ⟨_, d.π₁, d.π₂, hdx⟩
    have hkd₁ : kd ≫ kp₁ (f := x) = d.π₁ := kp_lift_p₁ d.π₁ d.π₂ hdx
    have hkd₂ : kd ≫ kp₂ (f := x) = d.π₂ := kp_lift_p₂ d.π₁ d.π₂ hdx
    refine ⟨kd ≫ k_inv, ⟨?_, ?_⟩, ?_⟩
    · -- (kd ≫ k_inv) ≫ l = kd ≫ kp₁(x) = d.π₁.
      rw [Cat.assoc, hkinv_l, hkd₁]
    · rw [Cat.assoc, hkinv_r, hkd₂]
    · -- Uniqueness.
      intro v hv₁ hv₂
      -- v ≫ k = kd by pullback uniqueness on kernelPair(x).
      have hvk : v ≫ k = kd := by
        have e₁ : (v ≫ k) ≫ kp₁ (f := x) = d.π₁ := by
          rw [Cat.assoc, hk_p₁, hv₁]
        have e₂ : (v ≫ k) ≫ kp₂ (f := x) = d.π₂ := by
          rw [Cat.assoc, hk_p₂, hv₂]
        exact (kp_lift_uniq d.π₁ d.π₂ hdx (v ≫ k) e₁ e₂)
      calc v = v ≫ (k ≫ k_inv) := by rw [hk_left, Cat.comp_id]
        _ = (v ≫ k) ≫ k_inv := (Cat.assoc _ _ _).symm
        _ = kd ≫ k_inv := by rw [hvk]
  · -- Backward: coeq square is a pullback ⇒ effective (via x = q).
    intro h_pb
    -- k_q : E → kernelPair(q), the chosen lift of (l, r) into kernelPair(q).
    let k_q : E ⟶ kernelPair q := (HasPullbacks.has q q).lift ⟨E, l, r, hcoeq.eq⟩
    have hkq₁ : k_q ≫ kp₁ (f := q) = l := kp_lift_p₁ l r hcoeq.eq
    have hkq₂ : k_q ≫ kp₂ (f := q) = r := kp_lift_p₂ l r hcoeq.eq
    -- The kernel-pair projections give a cone over (q, q); apply the pullback h_pb.
    obtain ⟨u, ⟨hu₁, hu₂⟩, _⟩ :=
      h_pb ⟨kernelPair q, kp₁ (f := q), kp₂ (f := q), kp_sq⟩
    -- u : kernelPair(q) → E with u ≫ l = kp₁(q), u ≫ r = kp₂(q).
    -- Show k_q is iso with inverse u.
    refine ⟨hcoeq.obj, q, hcoeq.eq, coeq_map_is_cover hcoeq, ⟨u, ?_, ?_⟩⟩
    · -- k_q ≫ u = id_E.  Use that ⟨E,l,r⟩ is a pullback (h_pb): unique map E→E.
      -- Both id_E and k_q ≫ u send (l,r) to (l,r), so equal by uniqueness in h_pb.
      obtain ⟨w, _, huniq⟩ := h_pb ⟨E, l, r, hcoeq.eq⟩
      have hid : Cat.id E = w := huniq (Cat.id E) (Cat.id_comp _) (Cat.id_comp _)
      have hcomp : k_q ≫ u = w := by
        refine huniq (k_q ≫ u) ?_ ?_
        · rw [Cat.assoc, hu₁, hkq₁]
        · rw [Cat.assoc, hu₂, hkq₂]
      rw [hcomp, ← hid]
    · -- u ≫ k_q = id_{kernelPair(q)}.  By pullback uniqueness on kernelPair(q).
      have e₁ : (u ≫ k_q) ≫ kp₁ (f := q) = kp₁ (f := q) := by
        rw [Cat.assoc, hkq₁, hu₁]
      have e₂ : (u ≫ k_q) ≫ kp₂ (f := q) = kp₂ (f := q) := by
        rw [Cat.assoc, hkq₂, hu₂]
      have hide : (u ≫ k_q) = (HasPullbacks.has q q).lift ⟨_, kp₁ (f := q), kp₂ (f := q), kp_sq⟩ :=
        kp_lift_uniq (kp₁ (f := q)) (kp₂ (f := q)) kp_sq (u ≫ k_q) e₁ e₂
      have hidk : Cat.id (kernelPair q) =
          (HasPullbacks.has q q).lift ⟨_, kp₁ (f := q), kp₂ (f := q), kp_sq⟩ :=
        kp_lift_uniq (kp₁ (f := q)) (kp₂ (f := q)) kp_sq (Cat.id (kernelPair q))
          (Cat.id_comp _) (Cat.id_comp _)
      rw [hide, ← hidk]
      rfl

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

    Freyd's definition is *structural* — the addition is **defined**, not postulated.
    There is a zero object (`zeroHom`, the unique A→0→B), and the canonical δᵢⱼ-matrix
    `A+B → A×B` is an isomorphism (`prod_coprod_coincide`).  Freyd then writes the
    two coincident operations (§1.591, eqs. (1.1)/(1.1')):

        x +_L y = A --⟨⟩--> A+A --Φ⁻¹--> ... --[x,y]--> B   (codiagonal route)
        x +_R y = A --⟨x,y⟩--> B×B --Φ⁻¹--> B+B --∇--> B    (diagonal  route)

    Here `Φ⁻¹` is the inverse of the coincidence iso, `[x,y] = case x y`,
    `⟨⟩ = diag`, `⟨x,y⟩ = pair x y`, `∇ = case id id`.  The two formulas define the
    same map; we record `add` together with both defining equations
    (`add_eq_addL`, `add_eq_addR`).  From these the middle-two interchange,
    commutativity and associativity follow by Freyd's Eckmann–Hilton argument —
    none of it is postulated (see `middle_two_interchange` below). -/
class HalfAdditiveCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasCoterminator 𝒞, HasBinaryCoproducts 𝒞 where
  /-- Zero morphism A → 0 → B through the zero object (0 ≅ 1). -/
  zeroHom : ∀ (A B : 𝒞), A ⟶ B
  /-- The zero morphism is a two-sided absorbing ideal (it factors through 0):
      `f ≫ zeroHom = zeroHom` and `zeroHom ≫ g = zeroHom` (§1.591: "two-sided ideal"). -/
  zeroHom_comp_left  : ∀ {A B C : 𝒞} (f : A ⟶ B), f ≫ zeroHom B C = zeroHom A C
  zeroHom_comp_right : ∀ {A B C : 𝒞} (g : B ⟶ C), zeroHom A B ≫ g = zeroHom A C
  /-- The canonical map A+B → A×B (δᵢⱼ-matrix) is an isomorphism.
      This is the key horn sentence expressing that products = coproducts. -/
  prod_coprod_coincide : ∀ (A B : 𝒞),
    IsIso (HasBinaryCoproducts.case
        (pair (Cat.id A) (zeroHom A B))
        (pair (zeroHom B A) (Cat.id B)) :
      HasBinaryCoproducts.coprod A B ⟶ prod A B)
  /-- The abelian-monoid addition on Hom(A,B), induced by products = coproducts. -/
  add : ∀ {A B : 𝒞}, (A ⟶ B) → (A ⟶ B) → (A ⟶ B)
  /-- **Freyd eq. (1.1)**: `add` is the coproduct/codiagonal operation `+_L`,
      `x +_L y = diag ≫ Φ⁻¹ ≫ case x y`, with `Φ⁻¹` the inverse coincidence iso. -/
  add_eq_addL : ∀ {A B : 𝒞} (x y : A ⟶ B),
    add x y = diag A ≫ (prod_coprod_coincide A A).choose ≫
      HasBinaryCoproducts.case x y
  /-- **Freyd eq. (1.1')**: `add` is the product/diagonal operation `+_R`,
      `x +_R y = pair x y ≫ Φ⁻¹ ≫ ∇`, with `∇ = case id id`. -/
  add_eq_addR : ∀ {A B : 𝒞} (x y : A ⟶ B),
    add x y = pair x y ≫ (prod_coprod_coincide B B).choose ≫
      HasBinaryCoproducts.case (Cat.id B) (Cat.id B)

/-- In a half-additive category, each Hom(A,B) carries the structure's addition. -/
def homAdd [inst : HalfAdditiveCategory 𝒞] {A B : 𝒞} : (A ⟶ B) → (A ⟶ B) → (A ⟶ B) :=
  inst.add

namespace HalfAdditiveCategory

variable [inst : HalfAdditiveCategory 𝒞]

/-- The inverse `Φ⁻¹ : A×B → A+B` of the coincidence iso, chosen from
    `prod_coprod_coincide`. -/
private noncomputable def Φinv (A B : 𝒞) : prod A B ⟶ HasBinaryCoproducts.coprod A B :=
  (inst.prod_coprod_coincide A B).choose

/-- `add` in coproduct form (eq. 1.1), with the local name for `Φ⁻¹`. -/
private theorem add_addL {A B : 𝒞} (x y : A ⟶ B) :
    inst.add x y = diag A ≫ Φinv A A ≫ HasBinaryCoproducts.case x y :=
  inst.add_eq_addL x y

/-- `add` in product form (eq. 1.1'), with the local name for `Φ⁻¹`. -/
private theorem add_addR {A B : 𝒞} (x y : A ⟶ B) :
    inst.add x y = pair x y ≫ Φinv B B ≫ HasBinaryCoproducts.case (Cat.id B) (Cat.id B) :=
  inst.add_eq_addR x y

open HasBinaryCoproducts in
/-- Post-composition collapses a `case`: `case x y ≫ v = case (x≫v) (y≫v)`
    (coproduct functoriality). -/
private theorem case_comp {X Y A B : 𝒞} (x : A ⟶ X) (y : B ⟶ X) (v : X ⟶ Y) :
    case x y ≫ v = case (x ≫ v) (y ≫ v) :=
  case_uniq _ _ _ (by rw [← Cat.assoc, case_inl]) (by rw [← Cat.assoc, case_inr])

/-- Pre-composition collapses a `pair`: `w ≫ pair x y = pair (w≫x) (w≫y)`
    (product functoriality). -/
private theorem comp_pair {W X A B : 𝒞} (w : W ⟶ X) (x : X ⟶ A) (y : X ⟶ B) :
    w ≫ pair x y = pair (w ≫ x) (w ≫ y) :=
  pair_uniq (w ≫ x) (w ≫ y) (w ≫ pair x y)
    (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])

/-- **Matrix middle-four interchange** (pure (co)product universality, no iso):
    `case (pair a b) (pair c d) = pair (case a c) (case b d)` as maps `A+A → B×B`.
    This is the heart of Freyd's argument — the δ-matrix reads the same by rows or
    columns. -/
private theorem case_pair_swap {A B : 𝒞} (a b c d : A ⟶ B) :
    HasBinaryCoproducts.case (pair a b) (pair c d)
      = pair (HasBinaryCoproducts.case a c) (HasBinaryCoproducts.case b d) := by
  -- Determined by precomposition with inl, inr (joint epi for the coproduct).
  refine (HasBinaryCoproducts.case_uniq _ _ _ ?_ ?_).symm
  · -- inl ≫ pair (case a c) (case b d) = pair a b
    rw [comp_pair, HasBinaryCoproducts.case_inl, HasBinaryCoproducts.case_inl]
  · rw [comp_pair, HasBinaryCoproducts.case_inr, HasBinaryCoproducts.case_inr]

/-- `Φ ≫ Φ⁻¹ = id` on the coproduct (the δ-matrix iso), stated with the local name. -/
private theorem Φ_Φinv (A B : 𝒞) :
    HasBinaryCoproducts.case (pair (Cat.id A) (inst.zeroHom A B))
        (pair (inst.zeroHom B A) (Cat.id B)) ≫ Φinv A B
      = Cat.id (HasBinaryCoproducts.coprod A B) :=
  (inst.prod_coprod_coincide A B).choose_spec.1

/-- Right-associated cancellation `Φ ≫ Φ⁻¹ ≫ g = g`. -/
private theorem Φ_Φinv_comp {A B X : 𝒞}
    (g : HasBinaryCoproducts.coprod A B ⟶ X) :
    HasBinaryCoproducts.case (pair (Cat.id A) (inst.zeroHom A B))
        (pair (inst.zeroHom B A) (Cat.id B)) ≫ Φinv A B ≫ g = g := by
  rw [← Cat.assoc, Φ_Φinv, Cat.id_comp]

/-- Right unit `add f 0 = f` (eq. 1.1'): the second pair-slot is killed by `Φ⁻¹`. -/
theorem add_zero {A B : 𝒞} (f : A ⟶ B) : inst.add f (inst.zeroHom A B) = f := by
  rw [add_addR]
  -- pair f 0 = f ≫ inl ≫ Φ : factor through inl, whose Φ-image is pair id 0.
  have h1 : pair f (inst.zeroHom A B)
      = f ≫ HasBinaryCoproducts.inl ≫ HasBinaryCoproducts.case
          (pair (Cat.id B) (inst.zeroHom B B)) (pair (inst.zeroHom B B) (Cat.id B)) := by
    rw [HasBinaryCoproducts.case_inl, comp_pair, Cat.comp_id, inst.zeroHom_comp_left]
  rw [h1]
  simp only [Cat.assoc]
  rw [Φ_Φinv_comp, HasBinaryCoproducts.case_inl, Cat.comp_id]

/-- Left unit `add 0 f = f` (eq. 1.1'), dual to `add_zero`. -/
theorem zero_add {A B : 𝒞} (f : A ⟶ B) : inst.add (inst.zeroHom A B) f = f := by
  rw [add_addR]
  have h1 : pair (inst.zeroHom A B) f
      = f ≫ HasBinaryCoproducts.inr ≫ HasBinaryCoproducts.case
          (pair (Cat.id B) (inst.zeroHom B B)) (pair (inst.zeroHom B B) (Cat.id B)) := by
    rw [HasBinaryCoproducts.case_inr, comp_pair, Cat.comp_id, inst.zeroHom_comp_left]
  rw [h1]
  simp only [Cat.assoc]
  rw [Φ_Φinv_comp, HasBinaryCoproducts.case_inr, Cat.comp_id]

/-- **Middle-two interchange law** (§1.591): `(u + v) + (x + y) = (u + x) + (v + y)`.

    Freyd's Eckmann–Hilton argument.  `add` is simultaneously the coproduct
    operation `+_L` (eq. 1.1) and the product operation `+_R` (eq. 1.1').  Expand
    the *outer* add by `+_L` and the two *inner* adds by `+_R`; both sides become
    the single composite

        A --diag--> A×A --Φ⁻¹--> A+A --M--> B×B --Φ⁻¹--> B+B --∇--> B,

    where `M` is the δ-matrix.  The only place the two argument orders differ is in
    `M`, and `case_pair_swap` shows the two matrices are equal — that is the whole
    content.  Commutativity (`u=y=0`) and associativity (`u=0`) of `+` follow. -/
theorem middle_two_interchange {A B : 𝒞} (u v x y : A ⟶ B) :
    inst.add (inst.add u v) (inst.add x y) =
    inst.add (inst.add u x) (inst.add v y) := by
  -- The common δ-matrix composite both sides reduce to.
  let M : A ⟶ B :=
    diag A ≫ Φinv A A ≫ pair (HasBinaryCoproducts.case u x) (HasBinaryCoproducts.case v y)
      ≫ Φinv B B ≫ HasBinaryCoproducts.case (Cat.id B) (Cat.id B)
  -- LHS: outer +_L, inner +_R, then case_comp + case_pair_swap.
  have hLHS : inst.add (inst.add u v) (inst.add x y) = M := by
    show inst.add (inst.add u v) (inst.add x y) = _
    rw [add_addL (inst.add u v) (inst.add x y), add_addR u v, add_addR x y,
        ← case_comp (pair u v) (pair x y)
          (Φinv B B ≫ HasBinaryCoproducts.case (Cat.id B) (Cat.id B)),
        case_pair_swap u v x y]
  -- RHS: outer +_R, inner +_L, then comp_pair.
  have hRHS : inst.add (inst.add u x) (inst.add v y) = M := by
    show inst.add (inst.add u x) (inst.add v y) = _
    rw [add_addR (inst.add u x) (inst.add v y), add_addL u x, add_addL v y,
        ← Cat.assoc (diag A), ← Cat.assoc (diag A),
        ← comp_pair (diag A ≫ Φinv A A) (HasBinaryCoproducts.case u x)
          (HasBinaryCoproducts.case v y),
        Cat.assoc, Cat.assoc]
  rw [hLHS, hRHS]

end HalfAdditiveCategory

/-- ADDITIVE CATEGORY (§1.591): half-additive with additive inverses.
    Every hom-set (A,B) is an abelian group: each f : A → B has a (unique)
    additive inverse g : A → B satisfying f + g = 0_{A,B}. -/
class AdditiveCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends HalfAdditiveCategory 𝒞 where
  /-- Additive inverses exist: every f : A → B has a g with f + g = zeroHom A B. -/
  addInv : ∀ {A B : 𝒞} (f : A ⟶ B), ∃ g : A ⟶ B, add f g = zeroHom A B

end Freyd
