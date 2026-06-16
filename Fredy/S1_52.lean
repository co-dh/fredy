/-
  Freyd & Scedrov, *Categories and Allegories* §1.52  Regular categories,
  well-supported, well-pointed, capital.  §1.52–§1.525.

  RegularCategory: Cartesian + images + pullbacks transfer covers.
  PreRegular: Cartesian + pullbacks transfer covers (images optional).
  WellSupported (§1.522), WellPointed (§1.523), Capital (§1.525).
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_45
import Fredy.S1_51


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.52 Regular and pre-regular categories

  A REGULAR CATEGORY is Cartesian with images where pullbacks transfer
  covers.  A PRE-REGULAR CATEGORY drops the images requirement. -/

/-- Mixin (§1.52): pullbacks transfer covers — the closure condition shared by
    regular and pre-regular categories.  In a pullback square the map opposite
    a cover is a cover; the square must be a pullback, not just commutative
    (in **Set** an empty corner over a commutative square defeats transfer). -/
class PullbacksTransferCovers (𝒞 : Type u) [Cat.{v} 𝒞] where
  pullbacks_transfer_covers : ∀ {A B C : 𝒞} {f : A ⟶ B} {g : C ⟶ B}
    (c : Cone f g), c.IsPullback → Cover f → Cover c.π₂

/-- A regular category: Cartesian, has images, pullbacks transfer covers (§1.52). -/
class RegularCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasPullbacks 𝒞, HasImages 𝒞,
    PullbacksTransferCovers 𝒞

/-- A pre-regular category: Cartesian, pullbacks transfer covers (§1.52). -/
class PreRegularCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasPullbacks 𝒞,
    PullbacksTransferCovers 𝒞

/-- The chosen pullback of a cover along any map is a cover. -/
theorem cover_pullback [hpull : HasPullbacks 𝒞] [PullbacksTransferCovers 𝒞]
    {A B C : 𝒞} {f : A ⟶ B} (g : C ⟶ B) (hf : Cover f) :
    Cover (hpull.has f g).cone.π₂ :=
  PullbacksTransferCovers.pullbacks_transfer_covers _ (hpull.has f g).cone_isPullback hf

/-! ## §1.512 Covers are right-cancellable (epic) -/

/-- A cover `f` is **epic** (right-cancellable).  `f` factors through the
    equalizer of `a, b` — realized as the pullback `P` of the graphs
    `g₁ = ⟨id,a⟩`, `g₂ = ⟨id,b⟩ : Y → Y×Z` — whose projection `e : P → Y` is
    monic; a cover through a monic forces it iso (`Cover`), so `e` is iso and
    `a = b`.  Needs only finite products and pullbacks. -/
theorem cover_epi [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    {X Y : 𝒞} {f : X ⟶ Y} (hf : Cover f) {Z : 𝒞} {a b : Y ⟶ Z}
    (hab : f ≫ a = f ≫ b) : a = b := by
  let g₁ : Y ⟶ prod Y Z := pair (Cat.id Y) a
  let g₂ : Y ⟶ prod Y Z := pair (Cat.id Y) b
  have hg₁fst : g₁ ≫ fst = Cat.id Y := fst_pair _ _
  have hg₂fst : g₂ ≫ fst = Cat.id Y := fst_pair _ _
  have hg₂mono : Mono g₂ := mono_of_retraction g₂ fst hg₂fst
  have pb : HasPullback g₁ g₂ := HasPullbacks.has g₁ g₂
  have hw : pb.cone.π₁ ≫ g₁ = pb.cone.π₂ ≫ g₂ := pb.cone.w
  -- the two projections coincide (both legs are graphs, so `≫ fst = id`)
  have hee₂ : pb.cone.π₁ = pb.cone.π₂ := by
    calc pb.cone.π₁ = pb.cone.π₁ ≫ (g₁ ≫ fst) := by rw [hg₁fst, Cat.comp_id]
      _ = (pb.cone.π₁ ≫ g₁) ≫ fst := (Cat.assoc _ _ _).symm
      _ = (pb.cone.π₂ ≫ g₂) ≫ fst := by rw [hw]
      _ = pb.cone.π₂ ≫ (g₂ ≫ fst) := Cat.assoc _ _ _
      _ = pb.cone.π₂ := by rw [hg₂fst, Cat.comp_id]
  -- `e := π₁` equalizes `a` and `b`
  have heq : pb.cone.π₁ ≫ a = pb.cone.π₁ ≫ b := by
    calc pb.cone.π₁ ≫ a = pb.cone.π₁ ≫ (g₁ ≫ snd) := by rw [show g₁ ≫ snd = a from snd_pair _ _]
      _ = (pb.cone.π₁ ≫ g₁) ≫ snd := (Cat.assoc _ _ _).symm
      _ = (pb.cone.π₂ ≫ g₂) ≫ snd := by rw [hw]
      _ = pb.cone.π₂ ≫ (g₂ ≫ snd) := Cat.assoc _ _ _
      _ = pb.cone.π₂ ≫ b := by rw [show g₂ ≫ snd = b from snd_pair _ _]
      _ = pb.cone.π₁ ≫ b := by rw [hee₂]
  -- `e := π₁` is monic (pullback of the monic `g₂`)
  have he_mono : Mono pb.cone.π₁ := by
    intro W p q hpq
    have hpq2 : p ≫ pb.cone.π₂ = q ≫ pb.cone.π₂ := by
      apply hg₂mono
      calc (p ≫ pb.cone.π₂) ≫ g₂ = p ≫ (pb.cone.π₂ ≫ g₂) := Cat.assoc _ _ _
        _ = p ≫ (pb.cone.π₁ ≫ g₁) := by rw [hw]
        _ = (p ≫ pb.cone.π₁) ≫ g₁ := (Cat.assoc _ _ _).symm
        _ = (q ≫ pb.cone.π₁) ≫ g₁ := by rw [hpq]
        _ = q ≫ (pb.cone.π₁ ≫ g₁) := Cat.assoc _ _ _
        _ = q ≫ (pb.cone.π₂ ≫ g₂) := by rw [hw]
        _ = (q ≫ pb.cone.π₂) ≫ g₂ := (Cat.assoc _ _ _).symm
    have hcone : (p ≫ pb.cone.π₁) ≫ g₁ = (p ≫ pb.cone.π₂) ≫ g₂ := by
      rw [Cat.assoc, Cat.assoc, hw]
    have hp : p = pb.lift ⟨W, p ≫ pb.cone.π₁, p ≫ pb.cone.π₂, hcone⟩ :=
      pb.lift_uniq ⟨W, p ≫ pb.cone.π₁, p ≫ pb.cone.π₂, hcone⟩ p rfl rfl
    have hq : q = pb.lift ⟨W, p ≫ pb.cone.π₁, p ≫ pb.cone.π₂, hcone⟩ :=
      pb.lift_uniq ⟨W, p ≫ pb.cone.π₁, p ≫ pb.cone.π₂, hcone⟩ q hpq.symm hpq2.symm
    rw [hp, hq]
  -- `f` factors through `e`
  have hfd : f ≫ g₁ = f ≫ g₂ := by
    have e1 : (f ≫ g₁) ≫ fst = (f ≫ g₂) ≫ fst := by
      rw [Cat.assoc, Cat.assoc, hg₁fst, hg₂fst]
    have e2 : (f ≫ g₁) ≫ snd = (f ≫ g₂) ≫ snd := by
      rw [Cat.assoc, Cat.assoc, show g₁ ≫ snd = a from snd_pair _ _,
          show g₂ ≫ snd = b from snd_pair _ _, hab]
    rw [pair_uniq ((f ≫ g₁) ≫ fst) ((f ≫ g₁) ≫ snd) (f ≫ g₁) rfl rfl,
        pair_uniq ((f ≫ g₁) ≫ fst) ((f ≫ g₁) ≫ snd) (f ≫ g₂) e1.symm e2.symm]
  have hue : pb.lift ⟨X, f, f, hfd⟩ ≫ pb.cone.π₁ = f := pb.lift_fst ⟨X, f, f, hfd⟩
  -- a cover through the monic `e` makes `e` iso
  obtain ⟨einv, _, hinv⟩ := hf pb.cone.π₁ (pb.lift ⟨X, f, f, hfd⟩) he_mono hue
  calc a = (einv ≫ pb.cone.π₁) ≫ a := by rw [hinv, Cat.id_comp]
    _ = einv ≫ (pb.cone.π₁ ≫ a) := Cat.assoc _ _ _
    _ = einv ≫ (pb.cone.π₁ ≫ b) := by rw [heq]
    _ = (einv ≫ pb.cone.π₁) ≫ b := (Cat.assoc _ _ _).symm
    _ = b := by rw [hinv, Cat.id_comp]

variable [HasTerminal 𝒞]

/-- A is WELL-SUPPORTED if A → 1 is a cover (§1.522). -/
def WellSupported (A : 𝒞) : Prop := Cover (term A)

/-- When `B` is well-supported, the projection `fst : C×B → C` is a cover.
    `C×B` with `(snd, fst)` is the pullback of `term B : B → 1` along
    `term C : C → 1` (a product is a pullback over the terminal), and pullbacks
    transfer the cover `term B` to the opposite leg `fst`. -/
theorem prod_fst_cover [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [PullbacksTransferCovers 𝒞]
    {C B : 𝒞} (hws : WellSupported B) : Cover (fst : prod C B ⟶ C) := by
  have hpb : (⟨prod C B, snd, fst, term_uniq _ _⟩ : Cone (term B) (term C)).IsPullback := by
    intro d
    refine ⟨pair d.π₂ d.π₁, ⟨snd_pair _ _, fst_pair _ _⟩, ?_⟩
    intro v hv₁ hv₂
    exact pair_uniq d.π₂ d.π₁ v hv₂ hv₁
  intro D m g hm hgm
  exact PullbacksTransferCovers.pullbacks_transfer_covers _ hpb hws m g hm hgm

/-- The SUPPORT of A is the image of A → 1 (§1.522, requires HasImages). -/
def Support [HasImages 𝒞] (A : 𝒞) : Subobject 𝒞 one := image (term A)

/-- With images, A is well-supported iff its support is entire. -/
theorem wellSupported_iff_support_entire [HasImages 𝒞] (A : 𝒞) :
    WellSupported A ↔ Subobject.IsEntire (Support A) :=
  cover_iff_image_entire (term A)

/-- A is WELL-POINTED (§1.523): the collection 1 → A jointly covers A.
    Every proper monic into A misses some point 1 → A. -/
def WellPointed (A : 𝒞) : Prop :=
  ∀ {D : 𝒞} (m : D ⟶ A), Mono m → ¬ IsIso m → ∃ (x : one ⟶ A), ¬ ∃ (y : one ⟶ D), y ≫ m = x

/-- Capital (§1.525): every well-supported object is well-pointed. -/
def Capital : Prop := ∀ (A : 𝒞), WellSupported A → WellPointed A

/-! ## Kernel-pair lemmas (requires products and pullbacks too) -/

variable [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

section
variable (S : 𝒞)

private def _pb : HasPullback (term S) (term S) := hpull.has (term S) (term S)

def _kpCone : Cone (term S) (term S) := ⟨_, kp₁ (f:=term S), kp₂ (f:=term S), kp_sq⟩
def _prodCone : Cone (term S) (term S) := ⟨_, fst, snd, term_uniq _ _⟩

/-- kpProdIso : kernelPair(term S) → S×S via product universal property;
    kpProdInv in the other direction via pullback lift. -/
def kpProdIso : kernelPair (term S) ⟶ prod S S :=
  pair (kp₁ (f:=term S)) (kp₂ (f:=term S))

def kpProdInv : prod S S ⟶ kernelPair (term S) := (_pb S).lift (_prodCone S)

@[simp] theorem kpProdIso_fst : kpProdIso S ≫ fst = kp₁ (f:=term S) := fst_pair _ _
@[simp] theorem kpProdIso_snd : kpProdIso S ≫ snd = kp₂ (f:=term S) := snd_pair _ _
@[simp] theorem kpProdInv_fst : kpProdInv S ≫ kp₁ (f:=term S) = fst := (_pb S).lift_fst (_prodCone S)
@[simp] theorem kpProdInv_snd : kpProdInv S ≫ kp₂ (f:=term S) = snd := (_pb S).lift_snd (_prodCone S)

theorem kpProdIso_inv : kpProdIso S ≫ kpProdInv S = Cat.id (kernelPair (term S)) := by
  let u := kpProdIso S ≫ kpProdInv S
  have hu_fst : u ≫ kp₁ (f:=term S) = kp₁ (f:=term S) := by
    dsimp [u]; rw [Cat.assoc, kpProdInv_fst, kpProdIso_fst]
  have hu_snd : u ≫ kp₂ (f:=term S) = kp₂ (f:=term S) := by
    dsimp [u]; rw [Cat.assoc, kpProdInv_snd, kpProdIso_snd]
  have h_id_lift : (_pb S).lift (_kpCone S) = Cat.id (kernelPair (term S)) :=
    ((_pb S).lift_uniq (_kpCone S) (Cat.id _) (Cat.id_comp _) (Cat.id_comp _)).symm
  calc
    u = (_pb S).lift (_kpCone S) :=
      (_pb S).lift_uniq (_kpCone S) u hu_fst hu_snd
    _ = Cat.id (kernelPair (term S)) := h_id_lift

theorem kpProdInv_iso : kpProdInv S ≫ kpProdIso S = Cat.id (prod S S) := by
  have h := pair_uniq fst snd (kpProdInv S ≫ kpProdIso S)
    (by rw [Cat.assoc, kpProdIso_fst, kpProdInv_fst])
    (by rw [Cat.assoc, kpProdIso_snd, kpProdInv_snd])
  have hid : pair fst snd = Cat.id (prod S S) :=
    (pair_uniq fst snd (Cat.id (prod S S)) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])).symm
  rw [h, hid]

theorem kpProdIso_isIso : IsIso (kpProdIso S) :=
  ⟨kpProdInv S, kpProdIso_inv S, kpProdInv_iso S⟩

theorem kpProdInv_isIso : IsIso (kpProdInv S) :=
  ⟨kpProdIso S, kpProdInv_iso S, kpProdIso_inv S⟩

theorem kp_diag_prod : kp_diag (f:=term S) ≫ kpProdIso S = diag S := by
  let h := kp_diag (f:=term S) ≫ kpProdIso S
  have hfst : h ≫ fst = Cat.id S := by
    dsimp [h]; rw [Cat.assoc, kpProdIso_fst, kp_diag_p₁]
  have hsnd : h ≫ snd = Cat.id S := by
    dsimp [h]; rw [Cat.assoc, kpProdIso_snd, kp_diag_p₂]
  have h_eq := pair_uniq (Cat.id S) (Cat.id S) h hfst hsnd
  simpa [h, diag] using h_eq

theorem wellSupported_prod_self (S : 𝒞) (hws : WellSupported S) : WellSupported (prod S S) := by
  intro C m g hm hgm
  have h_diag_term : diag S ≫ term (prod S S) = term S := term_uniq _ _
  have h_factor : (diag S ≫ g) ≫ m = term S := by
    rw [Cat.assoc, hgm, h_diag_term]
  exact hws m (diag S ≫ g) hm h_factor

end

/-- §1.525: in a capital category the terminator is projective.
    Every well-supported A has a point 1 → A. -/
theorem capital_implies_one_projective
    (hcap : Capital (𝒞 := 𝒞)) (A : 𝒞) (hws : WellSupported A) :
    Nonempty (one ⟶ A) := by
  -- 1. If A → 1 is iso, use the inverse.
  by_cases hiso : IsIso (term A)
  · obtain ⟨inv, _, _⟩ := hiso
    exact Nonempty.intro inv
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
    exact Nonempty.intro (x ≫ fst)

/-! ## §1.524 Projective objects

  An object P is PROJECTIVE if the representable functor (P, -) preserves covers:
  every cover f : A ↠ P has a splitting s : P → A with s ≫ f = id_P.
  NOTE: `Projective` is formally defined in §1.57 (Fredy/S1_57.lean) together with
  the Choice–Projective equivalence.  We record the key consequence here. -/

/-- §1.524 + §1.525: in a capital pre-regular category the terminator 1 is projective
    — every cover `e : A ↠ 1` has a section.  Proof: `capital_implies_one_projective`
    gives `1 → A`; the equation holds by `term_uniq` since everything maps to 1 uniquely. -/
theorem capital_one_projective
    [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]
    (hcap : Capital (𝒞 := 𝒞))
    {A : 𝒞} {e : A ⟶ one} (he : Cover e) :
    ∃ (s : one ⟶ A), s ≫ e = Cat.id one := by
  have hterm : e = term A := term_uniq e _
  subst hterm
  obtain ⟨s⟩ := capital_implies_one_projective hcap A he
  exact ⟨s, term_uniq _ _⟩

/-! ## §1.52 Representation of pre-regular categories

  A REPRESENTATION OF PRE-REGULAR CATEGORIES is a functor that preserves
  finite products (terminal + binary products), equalizers, and covers (§1.52). -/

/-- A functor `F : 𝒞 → 𝒟` PRESERVES COVERS if it carries every cover to a cover. -/
def PreservesCovers {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F : 𝒞 → 𝒟) [hF : Functor F] : Prop :=
  ∀ {A B : 𝒞} (f : A ⟶ B), Cover f → Cover (hF.map f)

/-- **§1.52 REPRESENTATION OF PRE-REGULAR CATEGORIES**: a functor between
    pre-regular categories preserving finite products, equalizers, and covers.
    (This is the standard notion; a functor preserving these necessarily
    preserves whatever images may exist.) -/
structure RepOfPreReg {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    [CartesianCategory 𝒞] [CartesianCategory 𝒟]
    (F : 𝒞 → 𝒟) [hF : Functor F] : Prop where
  cartesian  : CartesianFunctor F
  pres_covers : PreservesCovers F

/-! ## §1.526 The points functor is a representation in a capital category

  In a capital pre-regular category the functor `Γ := (1 ⟶ -)` is a representation
  of pre-regular categories (§1.526).  We record its key preservation properties
  here as type-theoretic statements (Γ lands in Type, not back in 𝒞). -/

/-- §1.526 (terminal): `Γ(1) = (1 ⟶ 1)` is a singleton — has exactly one element. -/
theorem pts_terminal_unique [ht : HasTerminal 𝒞]
    (f g : one ⟶ (one : 𝒞)) : f = g :=
  term_uniq f g

/-- §1.526 (products): `Γ(A × B) → Γ(A) × Γ(B)` given by `x ↦ (x ≫ fst, x ≫ snd)` and
    `Γ(A) × Γ(B) → Γ(A × B)` given by `(a, b) ↦ pair a b` are mutually inverse. -/
theorem pts_prod_iso_left [hp : HasBinaryProducts 𝒞] {A B : 𝒞}
    (a : one ⟶ A) (b : one ⟶ B) :
    pair a b ≫ fst = a ∧ pair a b ≫ snd = b :=
  ⟨fst_pair a b, snd_pair a b⟩

theorem pts_prod_iso_right [hp : HasBinaryProducts 𝒞] {A B : 𝒞}
    (x : one ⟶ prod A B) :
    pair (x ≫ fst) (x ≫ snd) = x :=
  (pair_uniq (x ≫ fst) (x ≫ snd) x rfl rfl).symm

/-- §1.526 (covers): in a capital pre-regular category, `Γ = (1 ⟶ -)` preserves
    covers — if `f : X ↠ Y` is a cover then every point `y : 1 → Y` lifts to a
    point `x : 1 → X` with `x ≫ f = y`.  This is precisely that 1 is projective,
    which follows from capital (§1.525). -/
theorem pts_covers_of_capital
    [PullbacksTransferCovers 𝒞]
    (hcap : Capital (𝒞 := 𝒞))
    {X Y : 𝒞} {f : X ⟶ Y} (hf : Cover f) (y : one ⟶ Y) :
    ∃ (x : one ⟶ X), x ≫ f = y := by
  -- Pull f back along y.  The pullback leg π₂ : P → 1 is a cover (pullbacks transfer
  -- covers), and 1 is projective in a capital category, so π₂ splits.
  -- Then s ≫ π₁ : 1 → X is the desired lift.
  have hcov_π₂ : Cover (hpull.has f y).cone.π₂ := cover_pullback y hf
  obtain ⟨s, hs⟩ := capital_one_projective hcap hcov_π₂
  exact ⟨s ≫ (hpull.has f y).cone.π₁,
         by rw [Cat.assoc, (hpull.has f y).cone.w, ← Cat.assoc, hs, Cat.id_comp]⟩

/-! ## §1.521 The functor category 𝒮^A is regular

  For a small category A, the functor category 𝒮^A (presheaves on A, where 𝒮 = Set)
  is regular and the evaluation functors (ev_a : 𝒮^A → 𝒮 for a ∈ A) form a
  collectively faithful family of representations of regular categories.

  NOTE: This requires natural-transformation infrastructure (𝒮^A as a Cat instance,
  limits/colimits pointwise).  The codebase has no NatTrans type yet; this is
  recorded as MISSING in S1_52.md until that infrastructure exists. -/

end Freyd
