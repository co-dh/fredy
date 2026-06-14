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

theorem cartesian_distributive_implies_prelogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasEqualizers 𝒞] [HasImages 𝒞]
    [HasSubobjectUnions 𝒞] (hdist : IsDistributiveLattice (𝒞 := 𝒞)) : Nonempty (PreLogos 𝒞) := sorry

theorem monic_inverseImage_iff_distributive {A B : 𝒞} [PreLogos 𝒞]
    (f : A ⟶ B) (hf : Mono f) : True := sorry

class PreLogosFunctor {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] [PreLogos 𝒜] [PreLogos ℬ]
    (T : 𝒜 → ℬ) [Functor T] where preserves_finite_unions : True

theorem union_via_coproduct_image {A₁ A₂ A : 𝒞}
    [PreLogos 𝒞] [HasBinaryCoproducts 𝒞] (x₁ : A₁ ⟶ A) (x₂ : A₂ ⟶ A) : True := sorry

end Freyd
