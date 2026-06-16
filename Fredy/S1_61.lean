import Fredy.S1_60 open Freyd
universe v u variable {𝒞 : Type u} [Cat.{v} 𝒞]
namespace Freyd

/-- **§1.61**: 0 is a coterminator (initial object). -/
noncomputable def minimal_subobject_of_one_is_coterminator (h : PreLogos 𝒞) : HasCoterminator 𝒞 :=
  let one : 𝒞 := h.toHasTerminal.one
  let zeroSub : Subobject 𝒞 one := h.bottom one
  let zeroObj : 𝒞 := zeroSub.dom
  let zeroMonic : zeroObj ⟶ one := zeroSub.arr
  let bot (A : 𝒞) : Subobject 𝒞 A := h.bottom A
  have bot_min {A : 𝒞} (S : Subobject 𝒞 A) : (bot A).le S := h.bottom_min S
  have bot_dom_iso (A : 𝒞) : Isomorphic (bot A).dom zeroObj := h.bottom_dom_iso A one
  have hzeroMonic_mono : Mono zeroMonic := (h.bottom one).monic
  -- coterminator maps
  have mk (A : 𝒞) : zeroObj ⟶ A :=
    let iso := bot_dom_iso A
    let inv : zeroObj ⟶ (bot A).dom := iso.choose_spec.choose
    inv ≫ (bot A).arr
  -- uniqueness: any two maps from 0 to A are equal
  have uniq {A : 𝒞} (f g : zeroObj ⟶ A) : f = g := by
    haveI : HasTerminal 𝒞 := h.toHasTerminal
    haveI : HasBinaryProducts 𝒞 := h.toHasBinaryProducts
    haveI : HasPullbacks 𝒞 := h.toHasPullbacks
    letI : HasEqualizers 𝒞 := products_pullbacks_implies_equalizers
    let eq := HasEqualizers.eq zeroObj A f g
    let e : eq.cone.dom ⟶ zeroObj := eq.cone.map
    have he_eq : e ≫ f = e ≫ g := eq.cone.eq
    have he_mono : Mono e := by
      intro W x y h
      let ec : EqualizerCone f g := ⟨W, x ≫ e, by
        calc (x ≫ e) ≫ f = x ≫ (e ≫ f) := Cat.assoc _ _ _
          _ = x ≫ (e ≫ g) := by rw [he_eq]
          _ = (x ≫ e) ≫ g := (Cat.assoc _ _ _).symm⟩
      have hx : x = eq.lift ec := eq.uniq ec x rfl
      have hy : y = eq.lift ec := eq.uniq ec y (by
        dsimp [ec]; rw [h])
      rw [hx, hy]
    have hez_mono : Mono (e ≫ zeroMonic) := by
      intro W x y hz
      apply he_mono x y
      apply hzeroMonic_mono (x ≫ e) (y ≫ e)
      calc (x ≫ e) ≫ zeroMonic = x ≫ (e ≫ zeroMonic) := Cat.assoc _ _ _
        _ = y ≫ (e ≫ zeroMonic) := by rw [hz]
        _ = (y ≫ e) ≫ zeroMonic := (Cat.assoc _ _ _).symm
    let S : Subobject 𝒞 one := ⟨eq.cone.dom, e ≫ zeroMonic, hez_mono⟩
    have hle : zeroSub.le S := bot_min S
    rcases hle with ⟨u, hu⟩
    have hue : u ≫ e = Cat.id zeroObj := by
      apply hzeroMonic_mono (u ≫ e) (Cat.id zeroObj)
      dsimp [S, zeroSub, zeroMonic] at hu
      calc (u ≫ e) ≫ zeroMonic = u ≫ (e ≫ zeroMonic) := Cat.assoc _ _ _
        _ = zeroMonic := by rw [hu]
        _ = (Cat.id zeroObj) ≫ zeroMonic := (Cat.id_comp _).symm
    have he_iso : IsIso e := by
      refine ⟨u, ?_, hue⟩
      apply he_mono (e ≫ u) (Cat.id eq.cone.dom)
      calc (e ≫ u) ≫ e = e ≫ (u ≫ e) := Cat.assoc _ _ _
        _ = e ≫ Cat.id zeroObj := by rw [hue]
        _ = e := Cat.comp_id _
        _ = (Cat.id eq.cone.dom) ≫ e := (Cat.id_comp _).symm
    rcases he_iso with ⟨_, _, h⟩
    calc f = (Cat.id zeroObj) ≫ f := (Cat.id_comp _).symm
      _ = (u ≫ e) ≫ f := by rw [hue]
      _ = u ≫ (e ≫ f) := Cat.assoc _ _ _
      _ = u ≫ (e ≫ g) := by rw [he_eq]
      _ = (u ≫ e) ≫ g := (Cat.assoc _ _ _).symm
      _ = (Cat.id zeroObj) ≫ g := by rw [hue]
      _ = g := Cat.id_comp _
  { zero := zeroObj
    init := mk
    init_uniq := uniq }

/-- **§1.61**: Any morphism to 0 is an isomorphism. -/
theorem any_map_to_zero_is_iso (h : PreLogos 𝒞) {A : 𝒞} (f : A ⟶ (minimal_subobject_of_one_is_coterminator h).zero) :
    IsIso f := by
  let zeroObj := (minimal_subobject_of_one_is_coterminator h).zero
  let one : 𝒞 := h.toHasTerminal.one
  have hzeroMonic_mono : Mono (h.bottom one).arr := (h.bottom one).monic
  letI : HasTerminal 𝒞 := h.toHasTerminal
  letI : HasPullbacks 𝒞 := h.toHasPullbacks
  letI : HasImages 𝒞 := h.toHasImages
  let p : A ⟶ one := h.toHasTerminal.trm A
  -- f·zeroMonic = p (both the unique map A → 1)
  have hp_eq : f ≫ (h.bottom one).arr = p := h.toHasTerminal.uniq _ _
  let pb := h.toHasPullbacks.has p (h.bottom one).arr
  let c : Cone p (h.bottom one).arr := ⟨A, Cat.id A, f, by
    calc Cat.id A ≫ p = p := Cat.id_comp _
      _ = f ≫ (h.bottom one).arr := hp_eq.symm⟩
  let u : A ⟶ pb.cone.pt := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = Cat.id A := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = f := pb.lift_snd c
  -- π₁ is monic (pullback of monic)
  have hπ₁_mono : Mono pb.cone.π₁ :=
    (InverseImage p (h.bottom one)).monic
  -- π₁ split epi + monic ⇒ iso
  have hπ₁_iso : IsIso pb.cone.π₁ :=
    ⟨u, hπ₁_mono (pb.cone.π₁ ≫ u) (Cat.id pb.cone.pt) (by
      calc (pb.cone.π₁ ≫ u) ≫ pb.cone.π₁ = pb.cone.π₁ ≫ (u ≫ pb.cone.π₁) := Cat.assoc _ _ _
        _ = pb.cone.π₁ ≫ Cat.id A := by rw [hu₁]
        _ = pb.cone.π₁ := Cat.comp_id _
        _ = (Cat.id pb.cone.pt) ≫ pb.cone.π₁ := (Cat.id_comp _).symm), hu₁⟩
  -- π₁ iso ⇒ its section u is iso (u = π₁⁻¹)
  have hu_iso : IsIso u := by
    rcases hπ₁_iso with ⟨inv, hπ₁_inv, hinv_π₁⟩
    -- hπ₁_inv: π₁ ≫ inv = id_pb,  hinv_π₁: inv ≫ π₁ = id_A
    -- hu₁: u ≫ π₁ = id_A.  Since π₁ is monic, u = inv.
    have hu_eq_inv : u = inv := hπ₁_mono u inv (by rw [hu₁, hinv_π₁])
    rw [hu_eq_inv]; exact ⟨pb.cone.π₁, hinv_π₁, hπ₁_inv⟩
  -- invImage_preserves_bottom + bottom_dom_iso: pb.cone.pt ≅ zeroObj
  have hinv : Isomorphic (InverseImage p (h.bottom one)).dom (h.bottom A).dom :=
    h.invImage_preserves_bottom p
  have hbot : Isomorphic (h.bottom A).dom zeroObj := h.bottom_dom_iso A one
  let φ : (InverseImage p (h.bottom one)).dom ⟶ (h.bottom A).dom := hinv.choose
  have hφ_iso : IsIso φ := hinv.choose_spec
  let ψ : (h.bottom A).dom ⟶ zeroObj := hbot.choose
  have hψ_iso : IsIso ψ := hbot.choose_spec
  -- π₂ = φ·ψ (both equal as maps to zeroObj, by monicity of zeroMonic)
  have hπ₂_eq : pb.cone.π₂ = φ ≫ ψ := by
    apply hzeroMonic_mono (pb.cone.π₂) (φ ≫ ψ)
    -- Both sides compose with zeroMonic to the unique map pb.cone.pt → 1
    have h₁ : pb.cone.π₂ ≫ (h.bottom one).arr = pb.cone.π₁ ≫ p := pb.cone.w.symm
    have h₂ : (φ ≫ ψ) ≫ (h.bottom one).arr = pb.cone.π₁ ≫ p :=
      h.toHasTerminal.uniq ((φ ≫ ψ) ≫ (h.bottom one).arr) (pb.cone.π₁ ≫ p)
    calc pb.cone.π₂ ≫ (h.bottom one).arr = pb.cone.π₁ ≫ p := h₁
      _ = (φ ≫ ψ) ≫ (h.bottom one).arr := by rw [h₂]
  have hπ₂_iso : IsIso pb.cone.π₂ := by rw [hπ₂_eq]; exact isIso_comp hφ_iso hψ_iso
  -- f = u·π₂, composition of isos
  rw [← hu₂]; exact isIso_comp hu_iso hπ₂_iso

/-- **§1.61**: Degenerate iff 0 ≅ 1. -/
theorem degenerate_iff_zero_iso_one (h : PreLogos 𝒞) :
    (Nonempty (h.toHasTerminal.one ⟶ (minimal_subobject_of_one_is_coterminator h).zero)) ↔
    Isomorphic (minimal_subobject_of_one_is_coterminator h).zero h.toHasTerminal.one := by
  constructor
  · rintro ⟨f⟩; have hf := any_map_to_zero_is_iso h f
    rcases hf with ⟨g, hfg, hgf⟩; exact ⟨g, ⟨f, hgf, hfg⟩⟩
  · rintro ⟨f, hf⟩; rcases hf with ⟨g, hfg, hgf⟩; exact ⟨g⟩

/-- **§1.611**: the book's *reduced* definition of a pre-logos — "a Cartesian category with
    images in which pullbacks transfer finite covers".  In this development that ambient
    structure is exactly `RegularCategory` (Cartesian + images + `PullbacksTransferCovers`).
    Adjoining the lattice data — binary subobject unions and a least subobject `bottom`
    for each object, with `bottom` minimal and stable up to iso — yields a `PreLogos`.

    The genuine *content* of §1.611 (and of the §1.6 "equivalent definition") is that, once
    pullbacks transfer finite covers, the inverse-image operation `f#` automatically preserves
    binary unions and the bottom; everything else (regular structure, the lattice axioms) is
    the supplied data.  That covers-transfer ⟹ union-preservation derivation is the one
    remaining obligation below.

    BLOCKER for the two `sorry`s: deriving `inverseImage_preserves_unions f` from
    `PullbacksTransferCovers` requires the §1.615 picture `S ∪ T = Im[case x_S x_T]` combined
    with the fact that a *cover* over the union pulls back, along `f`, to a cover over
    `f#(S) ∪ f#(T)` — i.e. the cover-transfer square of the union inclusion.  That argument
    needs binary coproducts (to form `case`) which a bare `RegularCategory` need not have,
    plus a pullback-of-image = image-of-pullback interchange (the §1.45 pullback-pasting law,
    itself still `sorry` in `S1_45`).  Without coproducts or that interchange the preservation
    facts are not derivable here; they hold in the book because its pre-logoi are positive
    (§1.623) or are reached via the capitalization that supplies coproducts (§1.63). -/
theorem cartesian_with_images_covers_implies_prelogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [hReg : RegularCategory 𝒞] [HasSubobjectUnions 𝒞]
    (hBottom : ∀ (A : 𝒞), Subobject 𝒞 A)
    (hBottom_min : ∀ {A : 𝒞} (S : Subobject 𝒞 A), (hBottom A).le S)
    (hBottom_dom_iso : ∀ (A B : 𝒞), Isomorphic (hBottom A).dom (hBottom B).dom) :
    Nonempty (PreLogos 𝒞) :=
  ⟨{ hReg with
      union := HasSubobjectUnions.union
      union_left := HasSubobjectUnions.union_left
      union_right := HasSubobjectUnions.union_right
      union_min := HasSubobjectUnions.union_min
      bottom := hBottom
      bottom_min := hBottom_min
      bottom_dom_iso := hBottom_dom_iso
      -- covers-transfer ⟹ f# preserves binary unions (see BLOCKER above)
      invImage_preserves_union := fun {_A _B} _f => sorry
      -- covers-transfer ⟹ f# preserves the bottom (same machinery)
      invImage_preserves_bottom := fun {_A _B} _f => sorry }⟩

/-- **§1.612**: For monic f : A ↣ B, f# : Sub(B) → Sub(A) preserves binary
    unions (for every monic f targeted at B) iff Sub(B) is a distributive lattice,
    i.e. for all subobjects A, S, T of B:
        A ∩ (S ∪ T) ≅ (A ∩ S) ∪ (A ∩ T)
    where A ∩ S := InverseImage A.arr S is the pullback of A.arr along S.arr. -/
theorem monic_inverseImage_iff_distributive [HasImages 𝒞] [HasSubobjectUnions 𝒞] [HasPullbacks 𝒞] {B : 𝒞} :
    (∀ {A : 𝒞} (f : A ⟶ B) (_hf : Mono f) (S T : Subobject 𝒞 B),
      Isomorphic (InverseImage f (HasSubobjectUnions.union S T)).dom
                 (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)).dom) ↔
    (∀ (A S T : Subobject 𝒞 B),
      Isomorphic (InverseImage A.arr (HasSubobjectUnions.union S T)).dom
                 (HasSubobjectUnions.union (InverseImage A.arr S) (InverseImage A.arr T)).dom) := by
  constructor
  · intro h A S T; exact h A.arr A.monic S T
  · intro _h _ _f _hf _S _T
    -- ← direction: a monic f : A ↣ B *is* a subobject ⟨A, f, hf⟩ of B, and
    -- InverseImage f S is by definition InverseImage ⟨A, f, hf⟩.arr S.  So the
    -- distributivity of Sub(B) applied to that very subobject is exactly the claim.
    exact _h ⟨_, _f, _hf⟩ _S _T

/-- **§1.614**: A REPRESENTATION OF PRE-LOGOI is a functor T : 𝒜 → ℬ between pre-logoi
    that preserves Cartesian structure, images, and finite unions (including empty unions).
    Preserving finite unions means: T carries binary unions to binary unions, and the
    bottom (empty union / initial subobject) to the bottom. -/
class PreLogosFunctor {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] [PreLogos 𝒜] [PreLogos ℬ]
    (T : 𝒜 → ℬ) [Functor T] (hpm : PreservesMono T) where
  /-- T maps the binary union of S,U in Sub(A) to the union of T(S), T(U) in Sub(T(A)). -/
  preserves_union : ∀ {A : 𝒜} (S U : Subobject 𝒜 A),
    Isomorphic (Subobject.map T hpm (HasSubobjectUnions.union S U)).dom
               (HasSubobjectUnions.union (Subobject.map T hpm S) (Subobject.map T hpm U)).dom
  /-- T maps the bottom (empty union) to the bottom. -/
  preserves_bottom : ∀ (A : 𝒜),
    Isomorphic (Subobject.map T hpm (PreLogos.bottom A)).dom (PreLogos.bottom (T A)).dom

/-- In a thin category (at most one morphism per hom-set), any pair of objects with
    morphisms going both ways are isomorphic: the round-trips are forced to be identities. -/
theorem thin_iso_of_maps (hThin : ∀ {A B : 𝒞} (f g : A ⟶ B), f = g)
    {X Y : 𝒞} (u : X ⟶ Y) (v : Y ⟶ X) : Isomorphic X Y :=
  ⟨u, v, hThin (u ≫ v) (Cat.id X), hThin (v ≫ u) (Cat.id Y)⟩

/-- **§1.613 (converse)**: A thin category (poset) with binary unions and intersections
    that is a distributive lattice is a pre-logos.  The thinness makes all morphism
    conditions automatic; distributivity makes invImage preserve unions. -/
/- Uses `def` not `theorem`: `PreLogos 𝒞` is a class/structure, not a proposition. -/
def distributive_poset_is_prelogos [hReg : RegularCategory 𝒞] [HasSubobjectUnions 𝒞]
    (hThin : ∀ {A B : 𝒞} (f g : A ⟶ B), f = g)
    -- In the thin (poset) case, distributivity is: for any A,S,T subobjects of B,
    -- A ∩ (S ∪ T) ≅ (A ∩ S) ∪ (A ∩ T), where A ∩ S = InverseImage A.arr S.
    -- `hReg` is an instance so its `HasPullbacks` is the canonical one `InverseImage`
    -- resolves against, in both `hDist` and the PreLogos fields below (no instance-coherence gap).
    (hDist : ∀ {B : 𝒞} (A S T : Subobject 𝒞 B),
      Isomorphic (InverseImage A.arr (HasSubobjectUnions.union S T)).dom
                 (HasSubobjectUnions.union (InverseImage A.arr S) (InverseImage A.arr T)).dom)
    (hBottom : ∀ (A : 𝒞), Subobject 𝒞 A)
    (hBottom_min : ∀ {A : 𝒞} (S : Subobject 𝒞 A), (hBottom A).le S)
    (hBottom_dom_iso : ∀ (A B : 𝒞), Isomorphic (hBottom A).dom (hBottom B).dom) :
    PreLogos 𝒞 :=
  { hReg with
    union        := HasSubobjectUnions.union
    union_left   := HasSubobjectUnions.union_left
    union_right  := HasSubobjectUnions.union_right
    union_min    := HasSubobjectUnions.union_min
    bottom                    := hBottom
    bottom_min                := hBottom_min
    bottom_dom_iso            := hBottom_dom_iso
    -- In the thin/poset case every morphism _f : _A → _B is automatically monic (hThin makes
    -- left-cancellation trivial), so ⟨_A, _f, _⟩ is a subobject of _B whose `.arr` is *definitionally*
    -- _f.  Then `hDist` on that subobject IS this goal: `InverseImage ⟨_A,_f,_⟩.arr = InverseImage _f`.
    invImage_preserves_union  := fun {_A _B} _f _S _T =>
      hDist ⟨_A, _f, fun {_} g h _ => hThin g h⟩ _S _T
    -- invImage_preserves_bottom: InverseImage f (⊥_B) ≅ ⊥_A.  In the thin case it suffices
    -- to exhibit maps both ways: ⊥_A ≤ InverseImage f ⊥_B (by minimality of ⊥_A), and
    -- InverseImage f ⊥_B → ⊥_B → ⊥_A via the pullback's π₂ and bottom_dom_iso.
    invImage_preserves_bottom := fun {_A _B} _f => by
      letI : HasPullbacks 𝒞 := hReg.toHasPullbacks
      refine thin_iso_of_maps hThin ?fwd (hBottom_min (InverseImage _f (hBottom _B))).choose
      case fwd =>
        exact (HasPullbacks.has _f (hBottom _B).arr).cone.π₂ ≫ (hBottom_dom_iso _B _A).choose }

/-- **§1.615**: In a bicartesian category with images, given x₁ : A₁ → A and
    x₂ : A₂ → A, their union (image of x₁ joined with image of x₂) equals the image of
    the coproduct map [x₁, x₂] = case x₁ x₂ : A₁ + A₂ → A. -/
theorem union_via_coproduct_image [HasImages 𝒞] [HasSubobjectUnions 𝒞] [HasBinaryCoproducts 𝒞]
    {A₁ A₂ A : 𝒞} (x₁ : A₁ ⟶ A) (x₂ : A₂ ⟶ A) :
    IsImage (HasBinaryCoproducts.case x₁ x₂) (HasSubobjectUnions.union (image x₁) (image x₂)) := by
  -- inclusions of the two image-pieces into the union
  obtain ⟨l₁, hl₁⟩ := HasSubobjectUnions.union_left (image x₁) (image x₂)
  obtain ⟨l₂, hl₂⟩ := HasSubobjectUnions.union_right (image x₁) (image x₂)
  refine ⟨⟨HasBinaryCoproducts.case (image.lift x₁ ≫ l₁) (image.lift x₂ ≫ l₂), ?_⟩, ?_⟩
  · -- Allows: the assembled map composed with U.arr equals `case x₁ x₂` (check on inl, inr).
    refine HasBinaryCoproducts.case_uniq x₁ x₂ _ ?_ ?_
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inl, Cat.assoc, hl₁, image.lift_fac]
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inr, Cat.assoc, hl₂, image.lift_fac]
  · -- Minimality: any subobject allowing `case x₁ x₂` allows both x₁ and x₂, hence ≥ both images.
    rintro S ⟨k, hk⟩
    refine HasSubobjectUnions.union_min _ _ _
      (image_min x₁ S ⟨HasBinaryCoproducts.inl ≫ k, ?_⟩)
      (image_min x₂ S ⟨HasBinaryCoproducts.inr ≫ k, ?_⟩)
    · rw [Cat.assoc, hk, HasBinaryCoproducts.case_inl]
    · rw [Cat.assoc, hk, HasBinaryCoproducts.case_inr]

/-! ## §1.616  Relations in a pre-logos form a distributive lattice

  Freyd §1.616 records that in a pre-logos the relations `B&(A,B)` (subobjects of the
  product `A × B`) inherit the distributive-lattice structure of the subobject lattices:
  for relations `R, S, T`,
      `R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)`  and  `R(S ∪ T) = RS ∪ RT`,
  the second being distributivity of relational composition over union.  The underlying
  fact is exactly `monic_inverseImage_iff_distributive` above together with the union
  preservation of inverse images packaged into `PreLogos`.  The *relational* (composition)
  half belongs to the allegory development (Chapter 2, `S2_*`), where relations and their
  composition `R ; S` are defined; it is formalized there rather than duplicated here so the
  single source of truth for relations stays in the allegory files. -/

/-- **§1.621**: If A₁ ∩ A₂ = 0 and A₁ ∪ A₂ = A (as subobjects of A in a pre-logos)
    then A is the binary coproduct of A₁.dom and A₂.dom via the inclusions A₁.arr, A₂.arr.
    Here A₁ ∩ A₂ is the subobject represented by the pullback of A₁.arr along A₂.arr;
    A₁ ∩ A₂ = 0 means its domain is isomorphic to (PreLogos.bottom A).dom. -/
theorem disjoint_cover_is_coproduct [PreLogos 𝒞]
    {A : 𝒞} (A₁ A₂ : Subobject 𝒞 A)
    -- A₁ ∩ A₂ = 0: the pullback I of A₁.arr and A₂.arr has I.dom ≅ (⊥ A).dom
    (hDisjoint : Isomorphic (HasPullbacks.has A₁.arr A₂.arr).cone.pt (PreLogos.bottom A).dom)
    -- A₁ ∪ A₂ = A: the union is entire
    (hCover    : (HasSubobjectUnions.union A₁ A₂).IsEntire) :
    ∀ {X : 𝒞} (f₁ : A₁.dom ⟶ X) (f₂ : A₂.dom ⟶ X),
      ∃ h : A ⟶ X, A₁.arr ≫ h = f₁ ∧ A₂.arr ≫ h = f₂ ∧
        ∀ h' : A ⟶ X, A₁.arr ≫ h' = f₁ → A₂.arr ≫ h' = f₂ → h' = h := by
  -- BLOCKER: §1.621 is the disjoint specialization of the §1.62 PASTING LEMMA
  -- (`Fredy.pasting_lemma` in `S1_62`, itself still `sorry`).  Both the existence of `h`
  -- and its uniqueness rest on Freyd's relational identities: with R = x°f ∪ y°g one shows
  -- 1 ⊆ RR° and R°R ⊆ 1 (so R is a map), xR = f, yR = g, and "x,y cover ⟹ R unique".
  -- Those `x°x ∪ y°y = 1` / composition-distributes-over-union facts are Chapter-2 allegory
  -- material (`S2_*`), not yet available to a bare `PreLogos`.  Equivalently, via §1.615 the
  -- union A₁∪A₂ is the image of `case A₁.arr A₂.arr : A₁.dom + A₂.dom → A`, so disjointness
  -- turns that cover into an iso and A becomes the coproduct — but this route needs binary
  -- COPRODUCTS, which a general pre-logos lacks (they exist only in a POSITIVE pre-logos,
  -- §1.623).  Hence §1.621 cannot be discharged at this layer; left as a faithful sorry.
  sorry

end Freyd
