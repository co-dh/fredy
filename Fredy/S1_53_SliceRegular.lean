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
      `Cover m ↔ Cover m.left` (a slice cover is exactly a base cover on the underlying
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

variable {𝒞 : Type u} [CategoryTheory.Category.{v} 𝒞]

namespace Freyd

open CategoryTheory

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
      lift_fst := fun c => CategoryTheory.Over.OverMorphism.ext ((hpull.has m.left n.left).lift_fst _)
      lift_snd := fun c => CategoryTheory.Over.OverMorphism.ext ((hpull.has m.left n.left).lift_snd _)
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
def overProdPt : Over B := CategoryTheory.Over.mk ((_prodPB X Y).cone.π₁ ≫ X.hom)

/-- First projection `X ×_B Y → X`. -/
def overProdFst : OverHom (overProdPt X Y) X :=
  CategoryTheory.Over.homMk ((_prodPB X Y).cone.π₁) rfl

/-- Second projection `X ×_B Y → Y`.  Its over-hom law is the pullback square. -/
def overProdSnd : OverHom (overProdPt X Y) Y :=
  CategoryTheory.Over.homMk ((_prodPB X Y).cone.π₂) ((_prodPB X Y).cone.w).symm

variable {X Y}

/-- Pairing into `X ×_B Y`: given `a : W → X`, `b : W → Y` over `B`, the base lift of
    the cone `(a.left, b.left)` (which commutes over `B` since `a.left ≫ X.hom = W.hom = b.left ≫ Y.hom`). -/
def overProdPair {W : Over B} (a : OverHom W X) (b : OverHom W Y) :
    OverHom W (overProdPt X Y) :=
  let hbase : a.left ≫ X.hom = b.left ≫ Y.hom := by
    rw [CategoryTheory.Over.w a, CategoryTheory.Over.w b]
  let u := (_prodPB X Y).lift ⟨W.left, a.left, b.left, hbase⟩
  CategoryTheory.Over.homMk u (by
    show u ≫ ((_prodPB X Y).cone.π₁ ≫ X.hom) = W.hom
    rw [← CategoryTheory.Category.assoc, (_prodPB X Y).lift_fst _]
    exact CategoryTheory.Over.w a)

theorem overProdPair_uniq {W : Over B} (a : OverHom W X) (b : OverHom W Y)
    (h : OverHom W (overProdPt X Y))
    (h₁ : h ⊚ overProdFst X Y = a) (h₂ : h ⊚ overProdSnd X Y = b) :
    h = overProdPair a b := by
  apply CategoryTheory.Over.OverMorphism.ext
  have hbase : a.left ≫ X.hom = b.left ≫ Y.hom := by
    rw [CategoryTheory.Over.w a, CategoryTheory.Over.w b]
  exact (_prodPB X Y).lift_uniq ⟨W.left, a.left, b.left, hbase⟩ h.left
    (congrArg CommaMorphism.left h₁) (congrArg CommaMorphism.left h₂)

end overProd

/-- **§1.441**: `A/B` has binary products — the product is the base pullback over `B`. -/
instance overHasBinaryProducts (B : 𝒞) : HasBinaryProducts (Over B) where
  prod := overProdPt
  fst {X Y} := overProdFst X Y
  snd {X Y} := overProdSnd X Y
  pair {W X Y} a b := overProdPair a b
  fst_pair {W X Y} a b := CategoryTheory.Over.OverMorphism.ext ((_prodPB X Y).lift_fst _)
  snd_pair {W X Y} a b := CategoryTheory.Over.OverMorphism.ext ((_prodPB X Y).lift_snd _)
  pair_uniq := fun a b h h₁ h₂ => overProdPair_uniq a b h h₁ h₂

/-! ## §1.531 The cover correspondence: `Cover m ↔ Cover m.left`

  A slice morphism `m : OverHom X Y` is a cover in `A/B` iff its underlying arrow
  `m.left` is a cover in `A`.  Both directions are the §1.531 Slice Lemma: `Σ` preserves
  monos (`sigma_preserves_mono`) and reflects monos (`sigma_reflects_mono`), and an
  iso in `A/B` is exactly an iso on the underlying arrow (`overIso_underlying`,
  `overIso_of_underlying`). -/

/-- **§1.531 (⟸)**: if `m.left` is a cover in `A` then `m` is a cover in `A/B`.
    This is `sigma_reflects_cover` packaged as a `Cover` statement. -/
theorem cover_of_cover_f {B : 𝒞} {X Y : Over B} (m : OverHom X Y)
    (hm : Cover m.left) : Cover (𝒞 := Over B) m := by
  intro Z n g hn hgn
  -- `n` monic in A/B; `n.left` monic in A (Σ preserves monos); `g.left ≫ n.left = m.left`.
  have hnf : Monic n.left := sigma_preserves_mono n hn
  have hgnf : g.left ≫ n.left = m.left := congrArg CommaMorphism.left hgn
  -- `m.left` cover ⇒ `n.left` iso in A ⇒ `n` iso in A/B.
  exact overIso_of_underlying n (hm n.left g.left hnf hgnf)

/-- **§1.531 (⟹)**: if `m` is a cover in `A/B` then `m.left` is a cover in `A`.
    A base monic `n : C → Y.left` through which `m.left` factors is lifted to a slice
    monic into `Y` (over `n ≫ Y.hom`); `m`-as-cover forces it iso in `A/B`, hence
    iso in `A`. -/
theorem cover_f_of_cover {B : 𝒞} {X Y : Over B} (m : OverHom X Y)
    (hm : Cover (𝒞 := Over B) m) : Cover m.left := by
  intro C n g hn hgn
  -- lift `n` to a slice object `Z = ⟨C, n ≫ Y.hom⟩` and slice monic `Z → Y`.
  let Z : Over B := CategoryTheory.Over.mk (n ≫ Y.hom)
  let nO : OverHom Z Y := CategoryTheory.Over.homMk n rfl
  -- `g : X.left → C` is an over-hom `X → Z`: `g ≫ (n ≫ Y.hom) = m.left ≫ Y.hom = X.hom`.
  have hgw : g ≫ (n ≫ Y.hom) = X.hom := by
    rw [← CategoryTheory.Category.assoc, hgn, CategoryTheory.Over.w m]
  let gO : OverHom X Z := CategoryTheory.Over.homMk g hgw
  -- `nO` monic in A/B (Σ reflects monos); `gO ⊚ nO = m`.
  have hnOmono : OverMono nO := sigma_reflects_mono nO hn
  have hgmO : gO ⊚ nO = m := CategoryTheory.Over.OverMorphism.ext hgn
  -- `m`-cover ⇒ `nO` iso in A/B ⇒ `n = nO.left` iso in A.
  exact overIso_underlying (hm nO gO hnOmono hgmO)

/-! ## Σ preserves pullbacks at the level of arbitrary pullback cones

  `S1_44` shows the *chosen* slice pullback projects to the chosen base pullback.
  For `PullbacksTransferCovers` we need: the `Σ`-image of *any* slice pullback cone
  is a base pullback cone.  Given a base cone `d` over `(m.left, n.left)`, we lift it to a
  slice cone over `(m, n)` (its apex carries `d.π₁ ≫ X.hom`, the legs are over-homs
  because `d` commutes and `m, n` are over `B`), apply the slice cone's universal
  property, and project the lift back down. -/

/-- The `Σ`-image base cone of a slice cone `c` over `(m, n)`. -/
def sliceConeForget {B : 𝒞} {X Y Z : Over B} {m : X ⟶ Z} {n : Y ⟶ Z}
    (c : Cone m n) : Cone m.left n.left :=
  ⟨c.pt.left, c.π₁.left, c.π₂.left, congrArg CommaMorphism.left c.w⟩

/-- **§1.441 / §1.531**: `Σ` takes a slice pullback cone to a base pullback cone. -/
theorem sliceForget_preserves_isPullback {B : 𝒞} {X Y Z : Over B}
    {m : X ⟶ Z} {n : Y ⟶ Z} (c : Cone m n) (hc : c.IsPullback) :
    (sliceConeForget c).IsPullback := by
  intro d
  -- assemble a slice cone over `(m, n)` from the base cone `d`.
  -- apex: ⟨d.pt, d.π₁ ≫ X.hom⟩; first leg `d.π₁` is over-hom by construction.
  have hdpt : d.π₁ ≫ X.hom = d.π₂ ≫ Y.hom := by
    -- d.π₁ ≫ X.hom = d.π₁ ≫ m.left ≫ Z.hom = d.π₂ ≫ n.left ≫ Z.hom = d.π₂ ≫ Y.hom
    rw [← CategoryTheory.Over.w m, ← CategoryTheory.Category.assoc, d.w,
      CategoryTheory.Category.assoc, CategoryTheory.Over.w n]
  let W : Over B := CategoryTheory.Over.mk (d.π₁ ≫ X.hom)
  let a : OverHom W X := CategoryTheory.Over.homMk d.π₁ rfl
  let b : OverHom W Y := CategoryTheory.Over.homMk d.π₂ hdpt.symm
  have habw : a ⊚ m = b ⊚ n := CategoryTheory.Over.OverMorphism.ext d.w
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc ⟨W, a, b, habw⟩
  refine ⟨u.left, ⟨congrArg CommaMorphism.left hu₁, congrArg CommaMorphism.left hu₂⟩, ?_⟩
  -- uniqueness: any base lift `v` of `d` is the underlying arrow of a slice lift.
  intro v hv₁ hv₂
  -- `v : d.pt → c.pt.left` is an over-hom `W → c.pt`: `v ≫ c.pt.hom = W.hom`.
  -- `hv₁ : v ≫ (sliceConeForget c).π₁ = d.π₁`, and `(sliceConeForget c).π₁ = c.π₁.left`.
  have hv₁' : v ≫ c.π₁.left = d.π₁ := hv₁
  have hvw : v ≫ c.pt.hom = W.hom := by
    -- c.pt.hom = c.π₁.left ≫ X.hom (c.π₁ is an over-hom into X), and v ≫ c.π₁.left = d.π₁.
    show v ≫ c.pt.hom = d.π₁ ≫ X.hom
    rw [← CategoryTheory.Over.w c.π₁, ← CategoryTheory.Category.assoc, hv₁']
  let vO : OverHom W c.pt := CategoryTheory.Over.homMk v hvw
  have := huniq vO (CategoryTheory.Over.OverMorphism.ext hv₁) (CategoryTheory.Over.OverMorphism.ext hv₂)
  exact congrArg CommaMorphism.left this

/-! ## Σ REFLECTS pullbacks over the terminal: `Over 1 ≃ A`

  When the slice base is the terminal `1`, `Σ : Over 1 → A` is an equivalence, so it also *reflects*
  pullbacks: a slice cone whose `Σ`-image (`sliceConeForget`) is a base pullback is itself a slice
  pullback.  Every base arrow into a `Over 1`-object is automatically an over-hom (its triangle is
  `term_uniq`), so the base lift wraps to a slice lift and the base uniqueness gives slice uniqueness. -/

/-- **`Σ` reflects pullbacks over the terminal.**  For `Over (one : A)`, a slice cone `c` over `(m, n)`
    whose `Σ`-image is a base pullback is a slice pullback.  (`Over 1 ≃ A`; over-hom triangles are free.) -/
theorem sliceForget_reflects_isPullback_terminal [HasTerminal 𝒞]
    {X Y Z : Over (HasTerminal.one : 𝒞)} {m : X ⟶ Z} {n : Y ⟶ Z}
    (c : Cone m n) (hc : (sliceConeForget c).IsPullback) : c.IsPullback := by
  intro d
  -- base cone of `d`: apex `d.pt.left`, legs `d.π₁.left`, `d.π₂.left`.
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc (sliceConeForget d)
  -- `u : d.pt.left → c.pt.left` is an over-hom `d.pt → c.pt` (triangle is `term_uniq`).
  let uO : OverHom d.pt c.pt := CategoryTheory.Over.homMk u (term_uniq _ _)
  refine ⟨uO, ⟨CategoryTheory.Over.OverMorphism.ext hu₁, CategoryTheory.Over.OverMorphism.ext hu₂⟩, ?_⟩
  intro v hv₁ hv₂
  exact CategoryTheory.Over.OverMorphism.ext (huniq v.left (congrArg CommaMorphism.left hv₁) (congrArg CommaMorphism.left hv₂))

/-! ## §1.52 `PullbacksTransferCovers (Over B)`

  In a slice pullback square with a slice cover `f`, the opposite projection is a
  slice cover.  Project the whole square down via `Σ`: the image is a base pullback
  square (`sliceForget_preserves_isPullback`) whose cover side `f.left` is a base cover
  (`cover_f_of_cover`); `PullbacksTransferCovers A` makes the opposite base projection
  a base cover, which lifts back to a slice cover (`cover_of_cover_f`). -/

instance overPullbacksTransferCovers (B : 𝒞)
    [PullbacksTransferCovers 𝒞] : PullbacksTransferCovers (Over B) where
  pullbacks_transfer_covers {A' B' C'} f g c hc hcov := by
    -- project the slice pullback square down to a base pullback square.
    have hcfBase : (sliceConeForget c).IsPullback := sliceForget_preserves_isPullback c hc
    have hcovBase : Cover f.left := cover_f_of_cover f hcov
    -- base `PullbacksTransferCovers`: the opposite base projection `c.π₂.left` is a cover.
    have hπ₂Base : Cover (c.π₂).left :=
      PullbacksTransferCovers.pullbacks_transfer_covers (sliceConeForget c) hcfBase hcovBase
    -- `(sliceConeForget c).π₂ = c.π₂.left`, so `c.π₂` is a slice cover.
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

/-! ## `HasEqualizers (Over B)` — slice equalizers are base equalizers

  The equalizer of two slice maps `f, g : X ⟶ Y` in `A/B` is the *base* equalizer `E ⟶ X.left` of the
  underlying `f.left, g.left`, with structure map `eqMap ≫ X.hom`.  The equalizer over-hom `⟨eqMap, rfl⟩` lies
  over `B` because its structure map is *defined* to be `eqMap ≫ X.hom`; it equalizes `f, g` since the
  base `eqMap` equalizes `f.left, g.left` (`CategoryTheory.Over.OverMorphism.ext`); the lift of a cone `c : W → X` equalizing `f, g` is
  the base lift `eqLift` (which is an over-hom because `eqLift ≫ eqMap = c.left`, so its structure map
  matches `W.hom`).  Needed for the §1.543 inner colimit's `he : ∀ i, HasEqualizers (Over (chain i))`. -/

instance overHasEqualizers (B : 𝒞) [HasEqualizers 𝒞] : HasEqualizers (Over B) where
  eq X Y f g :=
    { cone :=
        { dom := CategoryTheory.Over.mk (eqMap f.left g.left ≫ X.hom)
          map := CategoryTheory.Over.homMk (eqMap f.left g.left) rfl
          eq := CategoryTheory.Over.OverMorphism.ext (eqMap_eq f.left g.left) }
      lift := fun c =>
        CategoryTheory.Over.homMk
          (eqLift f.left g.left c.map.left (congrArg CommaMorphism.left c.eq)) (by
            show eqLift f.left g.left c.map.left _ ≫ (eqMap f.left g.left ≫ X.hom) = c.dom.hom
            rw [← CategoryTheory.Category.assoc, eqLift_fac]
            exact CategoryTheory.Over.w c.map)
      fac := fun c => CategoryTheory.Over.OverMorphism.ext (eqLift_fac f.left g.left c.map.left (congrArg CommaMorphism.left c.eq))
      uniq := fun c m hm => CategoryTheory.Over.OverMorphism.ext
        (eqLift_uniq f.left g.left c.map.left (congrArg CommaMorphism.left c.eq) m.left (congrArg CommaMorphism.left hm)) }

/-! ## §1.547 The slice base-change (pullback) functor `g* : A/D → A/C`

  Given a base arrow `g : C ⟶ D`, base-change sends an object `X = ⟨X, h : X → D⟩`
  of `A/D` to the pullback `X ×_D C` of `h` along `g`, with structure map the second
  projection `π₂ : X ×_D C → C`.  This is the slice→slice transition `A/(∏V) → A/(∏U)`
  used by the §1.547 capitalization inner CatSystem.

  On a morphism `m : ⟨X,h⟩ ⟶ ⟨Y,k⟩` of `A/D` (so `m.left ≫ k = h`), base-change is the
  induced map on pullbacks: the `X`-cone `(π₁ˣ ≫ m.left, π₂ˣ)` lands on the cospan
  `(k, g)` because
    `(π₁ˣ ≫ m.left) ≫ k = π₁ˣ ≫ h = π₂ˣ ≫ g`,
  and its `Y`-pullback lift preserves `π₂`, hence is an over-`C` arrow.  Functoriality
  (`map_id`, `map_comp`) is `lift_uniq` of the `Y`-pullback. -/

section baseChange

variable {C D : 𝒞} (g : C ⟶ D)

/-- The base pullback `HasPullback (X.hom) g` of an `A/D`-object along `g`. -/
private def _bcPB (X : Over D) : HasPullback X.hom g := hpull.has X.hom g

/-- Object part of base-change: `⟨X, h⟩ ↦ ⟨X ×_D C, π₂⟩`, the pullback of `h` along
    `g` with structure map the second projection to `C`. -/
def baseChangeObj (X : Over D) : Over C :=
  CategoryTheory.Over.mk ((_bcPB g X).cone.π₂)

/-- The pullback square of `baseChangeObj g X`: `π₁ ≫ X.hom = π₂ ≫ g`. -/
private theorem _bc_w (X : Over D) :
    (_bcPB g X).cone.π₁ ≫ X.hom = (_bcPB g X).cone.π₂ ≫ g := (_bcPB g X).cone.w

/-- The `X`-pullback cone of `m : ⟨X,h⟩ ⟶ ⟨Y,k⟩`, viewed over the cospan `(k, g)`:
    legs `(π₁ˣ ≫ m.left, π₂ˣ)`, commuting since `(π₁ˣ ≫ m.left) ≫ k = π₁ˣ ≫ h = π₂ˣ ≫ g`. -/
def baseChangeCone {X Y : Over D} (m : OverHom X Y) : Cone Y.hom g :=
  ⟨(_bcPB g X).cone.pt, (_bcPB g X).cone.π₁ ≫ m.left, (_bcPB g X).cone.π₂, by
    rw [CategoryTheory.Category.assoc, CategoryTheory.Over.w m]; exact _bc_w g X⟩

/-- Morphism part of base-change: the induced map on pullbacks.  For
    `m : ⟨X,h⟩ ⟶ ⟨Y,k⟩`, lift the `X`-cone `(π₁ˣ ≫ m.left, π₂ˣ)` through the
    `Y`-pullback; `π₂` is preserved, so the lift is an over-`C` arrow. -/
def baseChangeMap {X Y : Over D} (m : OverHom X Y) :
    OverHom (baseChangeObj g X) (baseChangeObj g Y) :=
  CategoryTheory.Over.homMk ((_bcPB g Y).lift (baseChangeCone g m))
    ((_bcPB g Y).lift_snd (baseChangeCone g m))

/-- Base-change is a `Functor A/D → A/C`. -/
instance baseChangeFunctor : Functor (baseChangeObj g) where
  map m := baseChangeMap g m
  map_id X := by
    -- `lift_uniq` for the identity `X`-cone: `Cat.id` is the lift.
    apply CategoryTheory.Over.OverMorphism.ext
    show (_bcPB g X).lift (baseChangeCone g (𝟙 X)) =
      (show OverHom (baseChangeObj g X) (baseChangeObj g X) from 𝟙 _).left
    refine ((_bcPB g X).lift_uniq (baseChangeCone g (𝟙 X))
      (show OverHom (baseChangeObj g X) (baseChangeObj g X) from 𝟙 _).left ?_ ?_).symm
    · show 𝟙 _ ≫ (_bcPB g X).cone.π₁ = (_bcPB g X).cone.π₁ ≫
        (show OverHom X X from 𝟙 X).left
      rw [CategoryTheory.Category.id_comp]; show _ = (_bcPB g X).cone.π₁ ≫ 𝟙 _; rw [CategoryTheory.Category.comp_id]
    · show 𝟙 _ ≫ (_bcPB g X).cone.π₂ = (_bcPB g X).cone.π₂
      rw [CategoryTheory.Category.id_comp]
  map_comp {X Y Z} m n := by
    -- `lift_uniq` for the composite: `baseChangeMap m ≫ baseChangeMap n` is the lift.
    apply CategoryTheory.Over.OverMorphism.ext
    show (_bcPB g Z).lift (baseChangeCone g (m ⊚ n))
      = ((baseChangeMap g m) ⊚ (baseChangeMap g n)).left
    refine ((_bcPB g Z).lift_uniq (baseChangeCone g (m ⊚ n))
      ((baseChangeMap g m) ⊚ (baseChangeMap g n)).left ?_ ?_).symm
    · -- π₁: ((bm).left ≫ (bn).left) ≫ π₁ᶻ = π₁ˣ ≫ (m ⊚ n).left
      show ((_bcPB g Y).lift (baseChangeCone g m) ≫ (_bcPB g Z).lift (baseChangeCone g n))
          ≫ (_bcPB g Z).cone.π₁
        = (_bcPB g X).cone.π₁ ≫ (m.left ≫ n.left)
      rw [CategoryTheory.Category.assoc, (_bcPB g Z).lift_fst (baseChangeCone g n)]
      show (_bcPB g Y).lift (baseChangeCone g m) ≫ ((_bcPB g Y).cone.π₁ ≫ n.left) = _
      rw [← CategoryTheory.Category.assoc, (_bcPB g Y).lift_fst (baseChangeCone g m)]
      show ((_bcPB g X).cone.π₁ ≫ m.left) ≫ n.left = (_bcPB g X).cone.π₁ ≫ (m.left ≫ n.left)
      rw [CategoryTheory.Category.assoc]
    · -- π₂: ((bm).left ≫ (bn).left) ≫ π₂ᶻ = π₂ˣ
      show ((_bcPB g Y).lift (baseChangeCone g m) ≫ (_bcPB g Z).lift (baseChangeCone g n))
          ≫ (_bcPB g Z).cone.π₂
        = (_bcPB g X).cone.π₂
      rw [CategoryTheory.Category.assoc, (_bcPB g Z).lift_snd (baseChangeCone g n)]
      show (_bcPB g Y).lift (baseChangeCone g m) ≫ (_bcPB g Y).cone.π₂ = (_bcPB g X).cone.π₂
      exact (_bcPB g Y).lift_snd (baseChangeCone g m)

end baseChange

/-! ## Strict reindexing (the dependent-sum / Σ direction) — STRICTLY functorial

  Contrast with base-change (above), which is only pseudo-functorial.  Post-composition
  with a *fixed* base map `m : C ⟶ D` is the dependent-sum functor `Σ_m : A/C → A/D`,
  `⟨X, x⟩ ↦ ⟨X, x ≫ m⟩`, `⟨f, w⟩ ↦ ⟨f, …⟩` (the SAME underlying arrow `f`).  Because `≫`
  is strictly associative and unital, ALL of the following hold **on the nose** (no canonical
  iso, unlike base-change):

    * `reindexFunctor` is a `Functor` with `map_id`/`map_comp` proved by `CategoryTheory.Over.OverMorphism.ext rfl`;
    * `reindexObj (𝟙 C) X = X`                     (object `F_refl`, by `CategoryTheory.Category.comp_id`);
    * `reindexObj (m ≫ m') X = reindexObj m' (reindexObj m X)`  (object `F_trans`, by `CategoryTheory.Category.assoc`).

  These three are exactly the `CatSystem.F_refl`/`F_trans` strict laws that base-change CANNOT
  satisfy.  So the strict direction EXISTS — but it post-composes the structure map and keeps the
  DOMAIN `X` fixed (`(reindexObj m X).left = X.left`, by `rfl`), and its variance is `A/C → A/D`
  along `m : C → D`.  In §1.547 the directed transition runs `A/(∏V) → A/(∏U)` for `V ⊆ U`, whose
  canonical base map is the PROJECTION `∏U → ∏V` (the wrong way for Σ), and the embedding needs the
  product to GROW `B×∏V ↝ B×∏U` (which only the pullback/base-change direction does — Σ keeps the
  domain fixed).  See `Freyd.innerCatSystem` (`RelativeCapitalization.lean`) for why this rules out
  route-1 strict reindexing as the inner-system transition. -/

section reindex

variable {C D E : 𝒞}

/-- Object part of strict reindexing along `m : C ⟶ D`: `⟨X, x⟩ ↦ ⟨X, x ≫ m⟩`. -/
def reindexObj (m : C ⟶ D) (X : Over C) : Over D :=
  CategoryTheory.Over.mk (X.hom ≫ m)

/-- The domain is UNCHANGED by reindexing (the structural reason Σ cannot grow `∏V ↝ ∏U`). -/
@[simp] theorem reindexObj_dom (m : C ⟶ D) (X : Over C) : (reindexObj m X).left = X.left := rfl

/-- Morphism part of strict reindexing: the SAME underlying arrow, re-typed over `D`. -/
def reindexMap (m : C ⟶ D) {X Y : Over C} (h : OverHom X Y) :
    OverHom (reindexObj m X) (reindexObj m Y) :=
  CategoryTheory.Over.homMk h.left (by
    show h.left ≫ (Y.hom ≫ m) = X.hom ≫ m
    rw [← CategoryTheory.Category.assoc, CategoryTheory.Over.w h])

/-- **Strict reindexing is a `Functor A/C → A/D`** — and STRICTLY so: `map_id`/`map_comp` are
    `CategoryTheory.Over.OverMorphism.ext rfl` because the underlying arrow is untouched. -/
instance reindexFunctor (m : C ⟶ D) : Functor (reindexObj m) where
  map h := reindexMap m h
  map_id _ := CategoryTheory.Over.OverMorphism.ext rfl
  map_comp _ _ := CategoryTheory.Over.OverMorphism.ext rfl

/-- **Strict `F_refl` (object level): `reindexObj (id) X = X` ON THE NOSE.**  The pseudo-functorial
    `baseChangeObj (id) X = X ×_C C` is only iso to `X`; Σ is equal. -/
@[simp] theorem reindexObj_id (X : Over C) : reindexObj (𝟙 C) X = X := by
  cases X with
  | mk left right hom =>
      cases right
      simp [reindexObj, CategoryTheory.Over.mk, CategoryTheory.CostructuredArrow.mk]

/-- **Strict `F_trans` (object level): `reindexObj (m ≫ m') = reindexObj m' ∘ reindexObj m` ON THE
    NOSE** (by strict associativity of `≫`).  Base-change re-associates an iterated pullback, equal
    only up to canonical iso. -/
theorem reindexObj_comp (m : C ⟶ D) (m' : D ⟶ E) (X : Over C) :
    reindexObj (m ≫ m') X = reindexObj m' (reindexObj m X) := by
  change CategoryTheory.Over.mk (X.hom ≫ (m ≫ m')) =
    CategoryTheory.Over.mk ((X.hom ≫ m) ≫ m')
  rw [CategoryTheory.Category.assoc]

end reindex

/-! ## §1.547  Finite product of a list of objects (`∏U`)

  Relocated here (from `RelativeCapitalization`) so that it sits UPSTREAM of `Capitalization`:
  the inflation/chain-slice machinery (`Fredy.Inflation`) needs `listProd` but must be importable
  by `Capitalization` to discharge `hwall_step`.  `listProd` only needs finite products and a
  terminator — no pullbacks — hence the dedicated section. -/
section listProd
variable {𝒞 : Type u} [CategoryTheory.Category.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]

/-- The product `∏U` of a finite list `U` of objects: right-folded binary product, with the
    empty product `∏[] = 1` (the terminator).  `∏(B :: U) = B × (∏U)`. -/
def listProd : List 𝒞 → 𝒞
  | [] => HasTerminal.one
  | B :: U => prod B (listProd U)

@[simp] theorem listProd_nil : listProd ([] : List 𝒞) = HasTerminal.one := rfl
@[simp] theorem listProd_cons (B : 𝒞) (U : List 𝒞) :
    listProd (B :: U) = prod B (listProd U) := rfl

end listProd

end Freyd
