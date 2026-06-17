/-
  Freyd & Scedrov, *Categories and Allegories* §1.53 — the slice A/B is pre-regular.

  This file assembles `PreRegularCategory (Over B)` for a pre-regular base `A`.
  The four ingredients of `PreRegularCategory` are:

    * `HasTerminal (Over B)`        — already in `S1_44` (`overHasTerminal`):
      the distinguished terminator `⟨B, 1_B⟩`.
    * `HasPullbacks (Over B)`       — built here from the base pullback construction
      `overPullbackPt`/`overPullbackLift` of `S1_44` (§1.441: A/B is Cartesian).
    * `HasBinaryProducts (Over B)`  — built here: the product of `X = ⟨X,x⟩` and
      `Y = ⟨Y,y⟩` in A/B is the *base pullback* `X ×_B Y` of `x` and `y` (§1.441:
      the binary product in a slice is a pullback in the base).
    * `PullbacksTransferCovers (Over B)` — built here from the §1.531 *Slice Lemma*:
      `Σ : A/B → A` preserves pullbacks and the cover correspondence
      `Cover m ↔ Cover m.f` (a slice cover is exactly a base cover on the underlying
      arrow).  Transferring along a slice pullback reduces to transferring along its
      Σ-image base pullback, where `PullbacksTransferCovers A` applies.

  Together these give `PreRegularCategory (Over B)` (the §1.543 capitalization
  slice-successor step needs this; see `Fredy/Capitalization.lean`).

  Everything is constructive and uses only this repo's hand-built `Cat`.
-/

import Fredy.S1_1
import Fredy.S1_26
import Fredy.S1_42
import Fredy.S1_44
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_53


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

variable [hpull : HasPullbacks 𝒞]

/-! ## §1.441 `HasPullbacks (Over B)`

  Packages the explicit pullback construction of `S1_44` (`overPullbackPt`,
  `overPullbackπ₁/π₂`, `overPullbackLift`, …) as a `HasPullbacks` instance. -/

/-- The pullback cone in `A/B` of a slice cospan `m, n`. -/
def overPullbackCone {B : 𝒞} {X Y Z : Over B} (m : X ⟶ Z) (n : Y ⟶ Z) :
    Cone m n :=
  ⟨overPullbackPt m n, overPullbackπ₁ m n, overPullbackπ₂ m n, overPullback_sq m n⟩

/-- **§1.441**: `A/B` has all pullbacks (when `A` does). -/
instance overHasPullbacks (B : 𝒞) : HasPullbacks (Over B) where
  has {X Y Z} m n :=
    { cone := overPullbackCone m n
      lift := fun c => overPullbackLift m n c.π₁ c.π₂ c.w
      lift_fst := fun c => overPullbackLift_fst m n c.π₁ c.π₂ c.w
      lift_snd := fun c => overPullbackLift_snd m n c.π₁ c.π₂ c.w
      lift_uniq := fun c u h₁ h₂ => overPullbackLift_uniq m n c.π₁ c.π₂ c.w u h₁ h₂ }

/-! ## §1.441 `HasBinaryProducts (Over B)`

  The product of `X = ⟨X,x⟩` and `Y = ⟨Y,y⟩` in `A/B` is the base pullback
  `X ×_B Y` of `x : X → B` and `y : Y → B`, with structure map `π₁ ≫ x` to `B`.
  The slice projections are the base pullback projections (each an over-hom).
  Pairing of `a : W → X`, `b : W → Y` over `B` is the base pullback lift; the two
  legs agree over `B` because both equal `W.hom`, so the cospan square commutes. -/

section overProd

variable {B : 𝒞} (X Y : Over B)

/-- The base pullback of the two structure maps `X.hom`, `Y.hom`. -/
private def _prodPB : HasPullback X.hom Y.hom := hpull.has X.hom Y.hom

/-- The product object `X ×_B Y` in `A/B`: the base pullback point, with structure
    map `π₁ ≫ X.hom` (= `π₂ ≫ Y.hom`). -/
def overProdPt : Over B := ⟨(_prodPB X Y).cone.pt, (_prodPB X Y).cone.π₁ ≫ X.hom⟩

/-- First projection `X ×_B Y → X`. -/
def overProdFst : OverHom (overProdPt X Y) X := ⟨(_prodPB X Y).cone.π₁, rfl⟩

/-- Second projection `X ×_B Y → Y`.  Its over-hom law is the pullback square. -/
def overProdSnd : OverHom (overProdPt X Y) Y :=
  ⟨(_prodPB X Y).cone.π₂, ((_prodPB X Y).cone.w).symm⟩

variable {X Y}

/-- Pairing into `X ×_B Y`: given `a : W → X`, `b : W → Y` over `B`, the base lift of
    the cone `(a.f, b.f)` (which commutes over `B` since `a.f ≫ X.hom = W.hom = b.f ≫ Y.hom`). -/
def overProdPair {W : Over B} (a : OverHom W X) (b : OverHom W Y) :
    OverHom W (overProdPt X Y) :=
  let hbase : a.f ≫ X.hom = b.f ≫ Y.hom := by rw [a.w, b.w]
  let u := (_prodPB X Y).lift ⟨W.dom, a.f, b.f, hbase⟩
  ⟨u, by
    show u ≫ ((_prodPB X Y).cone.π₁ ≫ X.hom) = W.hom
    rw [← Cat.assoc, (_prodPB X Y).lift_fst _]; exact a.w⟩

theorem overProdPair_fst {W : Over B} (a : OverHom W X) (b : OverHom W Y) :
    overProdPair a b ⊚ overProdFst X Y = a :=
  OverHom.ext ((_prodPB X Y).lift_fst _)

theorem overProdPair_snd {W : Over B} (a : OverHom W X) (b : OverHom W Y) :
    overProdPair a b ⊚ overProdSnd X Y = b :=
  OverHom.ext ((_prodPB X Y).lift_snd _)

theorem overProdPair_uniq {W : Over B} (a : OverHom W X) (b : OverHom W Y)
    (h : OverHom W (overProdPt X Y))
    (h₁ : h ⊚ overProdFst X Y = a) (h₂ : h ⊚ overProdSnd X Y = b) :
    h = overProdPair a b := by
  apply OverHom.ext
  have hbase : a.f ≫ X.hom = b.f ≫ Y.hom := by rw [a.w, b.w]
  exact (_prodPB X Y).lift_uniq ⟨W.dom, a.f, b.f, hbase⟩ h.f
    (congrArg OverHom.f h₁) (congrArg OverHom.f h₂)

end overProd

/-- **§1.441**: `A/B` has binary products — the product is the base pullback over `B`. -/
instance overHasBinaryProducts (B : 𝒞) : HasBinaryProducts (Over B) where
  prod := overProdPt
  fst {X Y} := overProdFst X Y
  snd {X Y} := overProdSnd X Y
  pair {W X Y} a b := overProdPair a b
  fst_pair := fun a b => overProdPair_fst a b
  snd_pair := fun a b => overProdPair_snd a b
  pair_uniq := fun a b h h₁ h₂ => overProdPair_uniq a b h h₁ h₂

/-! ## §1.531 The cover correspondence: `Cover m ↔ Cover m.f`

  A slice morphism `m : OverHom X Y` is a cover in `A/B` iff its underlying arrow
  `m.f` is a cover in `A`.  Both directions are the §1.531 Slice Lemma: `Σ` preserves
  monos (`sigma_preserves_mono`) and reflects monos (`sigma_reflects_mono`), and an
  iso in `A/B` is exactly an iso on the underlying arrow (`overIso_underlying`,
  `overIso_of_underlying`). -/

/-- **§1.531 (⟸)**: if `m.f` is a cover in `A` then `m` is a cover in `A/B`.
    This is `sigma_reflects_cover` packaged as a `Cover` statement. -/
theorem cover_of_cover_f {B : 𝒞} {X Y : Over B} (m : OverHom X Y)
    (hm : Cover m.f) : Cover (𝒞 := Over B) m := by
  intro Z n g hn hgn
  -- `n` monic in A/B; `n.f` monic in A (Σ preserves monos); `g.f ≫ n.f = m.f`.
  have hnf : Mono n.f := sigma_preserves_mono n hn
  have hgnf : g.f ≫ n.f = m.f := congrArg OverHom.f hgn
  -- `m.f` cover ⇒ `n.f` iso in A ⇒ `n` iso in A/B.
  exact overIso_of_underlying n (hm n.f g.f hnf hgnf)

/-- **§1.531 (⟹)**: if `m` is a cover in `A/B` then `m.f` is a cover in `A`.
    A base monic `n : C → Y.dom` through which `m.f` factors is lifted to a slice
    monic into `Y` (over `n ≫ Y.hom`); `m`-as-cover forces it iso in `A/B`, hence
    iso in `A`. -/
theorem cover_f_of_cover {B : 𝒞} {X Y : Over B} (m : OverHom X Y)
    (hm : Cover (𝒞 := Over B) m) : Cover m.f := by
  intro C n g hn hgn
  -- lift `n` to a slice object `Z = ⟨C, n ≫ Y.hom⟩` and slice monic `Z → Y`.
  let Z : Over B := ⟨C, n ≫ Y.hom⟩
  let nO : OverHom Z Y := ⟨n, rfl⟩
  -- `g : X.dom → C` is an over-hom `X → Z`: `g ≫ (n ≫ Y.hom) = m.f ≫ Y.hom = X.hom`.
  have hgw : g ≫ (n ≫ Y.hom) = X.hom := by
    rw [← Cat.assoc, hgn, m.w]
  let gO : OverHom X Z := ⟨g, hgw⟩
  -- `nO` monic in A/B (Σ reflects monos); `gO ⊚ nO = m`.
  have hnOmono : OverMono nO := sigma_reflects_mono nO hn
  have hgmO : gO ⊚ nO = m := OverHom.ext hgn
  -- `m`-cover ⇒ `nO` iso in A/B ⇒ `n = nO.f` iso in A.
  exact overIso_underlying (hm nO gO hnOmono hgmO)

/-! ## Σ preserves pullbacks at the level of arbitrary pullback cones

  `S1_44` shows the *chosen* slice pullback projects to the chosen base pullback.
  For `PullbacksTransferCovers` we need: the `Σ`-image of *any* slice pullback cone
  is a base pullback cone.  Given a base cone `d` over `(m.f, n.f)`, we lift it to a
  slice cone over `(m, n)` (its apex carries `d.π₁ ≫ X.hom`, the legs are over-homs
  because `d` commutes and `m, n` are over `B`), apply the slice cone's universal
  property, and project the lift back down. -/

/-- The `Σ`-image base cone of a slice cone `c` over `(m, n)`. -/
def sliceConeForget {B : 𝒞} {X Y Z : Over B} {m : X ⟶ Z} {n : Y ⟶ Z}
    (c : Cone m n) : Cone m.f n.f :=
  ⟨c.pt.dom, c.π₁.f, c.π₂.f, congrArg OverHom.f c.w⟩

/-- **§1.441 / §1.531**: `Σ` takes a slice pullback cone to a base pullback cone. -/
theorem sliceForget_preserves_isPullback {B : 𝒞} {X Y Z : Over B}
    {m : X ⟶ Z} {n : Y ⟶ Z} (c : Cone m n) (hc : c.IsPullback) :
    (sliceConeForget c).IsPullback := by
  intro d
  -- assemble a slice cone over `(m, n)` from the base cone `d`.
  -- apex: ⟨d.pt, d.π₁ ≫ X.hom⟩; first leg `d.π₁` is over-hom by construction.
  have hdpt : d.π₁ ≫ X.hom = d.π₂ ≫ Y.hom := by
    -- d.π₁ ≫ X.hom = d.π₁ ≫ m.f ≫ Z.hom = d.π₂ ≫ n.f ≫ Z.hom = d.π₂ ≫ Y.hom
    rw [← m.w, ← Cat.assoc, d.w, Cat.assoc, n.w]
  let W : Over B := ⟨d.pt, d.π₁ ≫ X.hom⟩
  let a : OverHom W X := ⟨d.π₁, rfl⟩
  let b : OverHom W Y := ⟨d.π₂, hdpt.symm⟩
  have habw : a ⊚ m = b ⊚ n := OverHom.ext d.w
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc ⟨W, a, b, habw⟩
  refine ⟨u.f, ⟨congrArg OverHom.f hu₁, congrArg OverHom.f hu₂⟩, ?_⟩
  -- uniqueness: any base lift `v` of `d` is the underlying arrow of a slice lift.
  intro v hv₁ hv₂
  -- `v : d.pt → c.pt.dom` is an over-hom `W → c.pt`: `v ≫ c.pt.hom = W.hom`.
  -- `hv₁ : v ≫ (sliceConeForget c).π₁ = d.π₁`, and `(sliceConeForget c).π₁ = c.π₁.f`.
  have hv₁' : v ≫ c.π₁.f = d.π₁ := hv₁
  have hvw : v ≫ c.pt.hom = W.hom := by
    -- c.pt.hom = c.π₁.f ≫ X.hom (c.π₁ is an over-hom into X), and v ≫ c.π₁.f = d.π₁.
    show v ≫ c.pt.hom = d.π₁ ≫ X.hom
    rw [← c.π₁.w, ← Cat.assoc, hv₁']
  let vO : OverHom W c.pt := ⟨v, hvw⟩
  have := huniq vO (OverHom.ext hv₁) (OverHom.ext hv₂)
  exact congrArg OverHom.f this

/-! ## §1.52 `PullbacksTransferCovers (Over B)`

  In a slice pullback square with a slice cover `f`, the opposite projection is a
  slice cover.  Project the whole square down via `Σ`: the image is a base pullback
  square (`sliceForget_preserves_isPullback`) whose cover side `f.f` is a base cover
  (`cover_f_of_cover`); `PullbacksTransferCovers A` makes the opposite base projection
  a base cover, which lifts back to a slice cover (`cover_of_cover_f`). -/

instance overPullbacksTransferCovers (B : 𝒞)
    [PullbacksTransferCovers 𝒞] : PullbacksTransferCovers (Over B) where
  pullbacks_transfer_covers {A' B' C'} f g c hc hcov := by
    -- project the slice pullback square down to a base pullback square.
    have hcfBase : (sliceConeForget c).IsPullback := sliceForget_preserves_isPullback c hc
    have hcovBase : Cover f.f := cover_f_of_cover f hcov
    -- base `PullbacksTransferCovers`: the opposite base projection `c.π₂.f` is a cover.
    have hπ₂Base : Cover (c.π₂).f :=
      PullbacksTransferCovers.pullbacks_transfer_covers (sliceConeForget c) hcfBase hcovBase
    -- `(sliceConeForget c).π₂ = c.π₂.f`, so `c.π₂` is a slice cover.
    intro Z n h hn hgn
    exact cover_of_cover_f (B := B) (m := c.π₂) hπ₂Base n h hn hgn

/-! ## §1.53 `PreRegularCategory (Over B)`

  All four mixins are now instances on `Over B`: terminal (`overHasTerminal`,
  `S1_44`), binary products (`overHasBinaryProducts`), pullbacks
  (`overHasPullbacks`), and pullbacks-transfer-covers
  (`overPullbacksTransferCovers`).  Hence the slice `A/B` of a pre-regular `A` is
  pre-regular. -/

instance overPreRegular (B : 𝒞) [PreRegularCategory 𝒞] :
    PreRegularCategory (Over B) where

/-! ## §1.547 The slice base-change (pullback) functor `g* : A/D → A/C`

  Given a base arrow `g : C ⟶ D`, base-change sends an object `X = ⟨X, h : X → D⟩`
  of `A/D` to the pullback `X ×_D C` of `h` along `g`, with structure map the second
  projection `π₂ : X ×_D C → C`.  This is the slice→slice transition `A/(∏V) → A/(∏U)`
  used by the §1.547 capitalization inner CatSystem.

  On a morphism `m : ⟨X,h⟩ ⟶ ⟨Y,k⟩` of `A/D` (so `m.f ≫ k = h`), base-change is the
  induced map on pullbacks: the `X`-cone `(π₁ˣ ≫ m.f, π₂ˣ)` lands on the cospan
  `(k, g)` because
    `(π₁ˣ ≫ m.f) ≫ k = π₁ˣ ≫ h = π₂ˣ ≫ g`,
  and its `Y`-pullback lift preserves `π₂`, hence is an over-`C` arrow.  Functoriality
  (`map_id`, `map_comp`) is `lift_uniq` of the `Y`-pullback. -/

section baseChange

variable {C D : 𝒞} (g : C ⟶ D)

/-- The base pullback `HasPullback (X.hom) g` of an `A/D`-object along `g`. -/
private def _bcPB (X : Over D) : HasPullback X.hom g := hpull.has X.hom g

/-- Object part of base-change: `⟨X, h⟩ ↦ ⟨X ×_D C, π₂⟩`, the pullback of `h` along
    `g` with structure map the second projection to `C`. -/
def baseChangeObj (X : Over D) : Over C :=
  ⟨(_bcPB g X).cone.pt, (_bcPB g X).cone.π₂⟩

/-- The pullback square of `baseChangeObj g X`: `π₁ ≫ X.hom = π₂ ≫ g`. -/
private theorem _bc_w (X : Over D) :
    (_bcPB g X).cone.π₁ ≫ X.hom = (_bcPB g X).cone.π₂ ≫ g := (_bcPB g X).cone.w

/-- The `X`-pullback cone of `m : ⟨X,h⟩ ⟶ ⟨Y,k⟩`, viewed over the cospan `(k, g)`:
    legs `(π₁ˣ ≫ m.f, π₂ˣ)`, commuting since `(π₁ˣ ≫ m.f) ≫ k = π₁ˣ ≫ h = π₂ˣ ≫ g`. -/
def baseChangeCone {X Y : Over D} (m : OverHom X Y) : Cone Y.hom g :=
  ⟨(_bcPB g X).cone.pt, (_bcPB g X).cone.π₁ ≫ m.f, (_bcPB g X).cone.π₂, by
    rw [Cat.assoc, m.w]; exact _bc_w g X⟩

/-- Morphism part of base-change: the induced map on pullbacks.  For
    `m : ⟨X,h⟩ ⟶ ⟨Y,k⟩`, lift the `X`-cone `(π₁ˣ ≫ m.f, π₂ˣ)` through the
    `Y`-pullback; `π₂` is preserved, so the lift is an over-`C` arrow. -/
def baseChangeMap {X Y : Over D} (m : OverHom X Y) :
    OverHom (baseChangeObj g X) (baseChangeObj g Y) :=
  ⟨(_bcPB g Y).lift (baseChangeCone g m), (_bcPB g Y).lift_snd (baseChangeCone g m)⟩

/-- Base-change is a `Functor A/D → A/C`. -/
instance baseChangeFunctor : Functor (baseChangeObj g) where
  map m := baseChangeMap g m
  map_id X := by
    -- `lift_uniq` for the identity `X`-cone: `Cat.id` is the lift.
    apply OverHom.ext
    show (_bcPB g X).lift (baseChangeCone g (Cat.id X)) = (Cat.id (baseChangeObj g X)).f
    refine ((_bcPB g X).lift_uniq (baseChangeCone g (Cat.id X))
      (Cat.id (baseChangeObj g X)).f ?_ ?_).symm
    · show Cat.id _ ≫ (_bcPB g X).cone.π₁ = (_bcPB g X).cone.π₁ ≫ (Cat.id X).f
      rw [Cat.id_comp]; show _ = (_bcPB g X).cone.π₁ ≫ Cat.id _; rw [Cat.comp_id]
    · show Cat.id _ ≫ (_bcPB g X).cone.π₂ = (_bcPB g X).cone.π₂
      rw [Cat.id_comp]
  map_comp {X Y Z} m n := by
    -- `lift_uniq` for the composite: `baseChangeMap m ≫ baseChangeMap n` is the lift.
    apply OverHom.ext
    show (_bcPB g Z).lift (baseChangeCone g (m ⊚ n))
      = ((baseChangeMap g m) ⊚ (baseChangeMap g n)).f
    refine ((_bcPB g Z).lift_uniq (baseChangeCone g (m ⊚ n))
      ((baseChangeMap g m) ⊚ (baseChangeMap g n)).f ?_ ?_).symm
    · -- π₁: ((bm).f ≫ (bn).f) ≫ π₁ᶻ = π₁ˣ ≫ (m ⊚ n).f
      show ((_bcPB g Y).lift (baseChangeCone g m) ≫ (_bcPB g Z).lift (baseChangeCone g n))
          ≫ (_bcPB g Z).cone.π₁
        = (_bcPB g X).cone.π₁ ≫ (m.f ≫ n.f)
      rw [Cat.assoc, (_bcPB g Z).lift_fst (baseChangeCone g n)]
      show (_bcPB g Y).lift (baseChangeCone g m) ≫ ((_bcPB g Y).cone.π₁ ≫ n.f) = _
      rw [← Cat.assoc, (_bcPB g Y).lift_fst (baseChangeCone g m)]
      show ((_bcPB g X).cone.π₁ ≫ m.f) ≫ n.f = (_bcPB g X).cone.π₁ ≫ (m.f ≫ n.f)
      rw [Cat.assoc]
    · -- π₂: ((bm).f ≫ (bn).f) ≫ π₂ᶻ = π₂ˣ
      show ((_bcPB g Y).lift (baseChangeCone g m) ≫ (_bcPB g Z).lift (baseChangeCone g n))
          ≫ (_bcPB g Z).cone.π₂
        = (_bcPB g X).cone.π₂
      rw [Cat.assoc, (_bcPB g Z).lift_snd (baseChangeCone g n)]
      show (_bcPB g Y).lift (baseChangeCone g m) ≫ (_bcPB g Y).cone.π₂ = (_bcPB g X).cone.π₂
      exact (_bcPB g Y).lift_snd (baseChangeCone g m)

end baseChange

/-! ## Strict reindexing (the dependent-sum / Σ direction) — STRICTLY functorial

  Contrast with base-change (above), which is only pseudo-functorial.  Post-composition
  with a *fixed* base map `m : C ⟶ D` is the dependent-sum functor `Σ_m : A/C → A/D`,
  `⟨X, x⟩ ↦ ⟨X, x ≫ m⟩`, `⟨f, w⟩ ↦ ⟨f, …⟩` (the SAME underlying arrow `f`).  Because `≫`
  is strictly associative and unital, ALL of the following hold **on the nose** (no canonical
  iso, unlike base-change):

    * `reindexFunctor` is a `Functor` with `map_id`/`map_comp` proved by `OverHom.ext rfl`;
    * `reindexObj (Cat.id C) X = X`                     (object `F_refl`, by `Cat.comp_id`);
    * `reindexObj (m ≫ m') X = reindexObj m' (reindexObj m X)`  (object `F_trans`, by `Cat.assoc`).

  These three are exactly the `CatSystem.F_refl`/`F_trans` strict laws that base-change CANNOT
  satisfy.  So the strict direction EXISTS — but it post-composes the structure map and keeps the
  DOMAIN `X` fixed (`(reindexObj m X).dom = X.dom`, by `rfl`), and its variance is `A/C → A/D`
  along `m : C → D`.  In §1.547 the directed transition runs `A/(∏V) → A/(∏U)` for `V ⊆ U`, whose
  canonical base map is the PROJECTION `∏U → ∏V` (the wrong way for Σ), and the embedding needs the
  product to GROW `B×∏V ↝ B×∏U` (which only the pullback/base-change direction does — Σ keeps the
  domain fixed).  See `Freyd.innerCatSystem` (`RelativeCapitalization.lean`) for why this rules out
  route-1 strict reindexing as the inner-system transition. -/

section reindex

variable {C D E : 𝒞}

/-- Object part of strict reindexing along `m : C ⟶ D`: `⟨X, x⟩ ↦ ⟨X, x ≫ m⟩`. -/
def reindexObj (m : C ⟶ D) (X : Over C) : Over D := ⟨X.dom, X.hom ≫ m⟩

/-- The domain is UNCHANGED by reindexing (the structural reason Σ cannot grow `∏V ↝ ∏U`). -/
@[simp] theorem reindexObj_dom (m : C ⟶ D) (X : Over C) : (reindexObj m X).dom = X.dom := rfl

/-- Morphism part of strict reindexing: the SAME underlying arrow, re-typed over `D`. -/
def reindexMap (m : C ⟶ D) {X Y : Over C} (h : OverHom X Y) :
    OverHom (reindexObj m X) (reindexObj m Y) :=
  ⟨h.f, by show h.f ≫ (Y.hom ≫ m) = X.hom ≫ m; rw [← Cat.assoc, h.w]⟩

/-- **Strict reindexing is a `Functor A/C → A/D`** — and STRICTLY so: `map_id`/`map_comp` are
    `OverHom.ext rfl` because the underlying arrow is untouched. -/
instance reindexFunctor (m : C ⟶ D) : Functor (reindexObj m) where
  map h := reindexMap m h
  map_id _ := OverHom.ext rfl
  map_comp _ _ := OverHom.ext rfl

/-- **Strict `F_refl` (object level): `reindexObj (id) X = X` ON THE NOSE.**  The pseudo-functorial
    `baseChangeObj (id) X = X ×_C C` is only iso to `X`; Σ is equal. -/
@[simp] theorem reindexObj_id (X : Over C) : reindexObj (Cat.id C) X = X := by
  show (⟨X.dom, X.hom ≫ Cat.id C⟩ : Over C) = X; rw [Cat.comp_id]

/-- **Strict `F_trans` (object level): `reindexObj (m ≫ m') = reindexObj m' ∘ reindexObj m` ON THE
    NOSE** (by strict associativity of `≫`).  Base-change re-associates an iterated pullback, equal
    only up to canonical iso. -/
theorem reindexObj_comp (m : C ⟶ D) (m' : D ⟶ E) (X : Over C) :
    reindexObj (m ≫ m') X = reindexObj m' (reindexObj m X) := by
  show (⟨X.dom, X.hom ≫ (m ≫ m')⟩ : Over E) = ⟨X.dom, (X.hom ≫ m) ≫ m'⟩; rw [Cat.assoc]

end reindex

end Freyd
