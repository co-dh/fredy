/-
  Freyd & Scedrov, *Categories and Allegories* §1.931 —
  the DEPENDENT-PRODUCT functor `Π_f : Over A → Over B`, right adjoint to the
  pullback functor `f* : Over B → Over A` (`baseChangeObj f`).

  STRATEGY (slice-of-slice, strict).  For `f : A ⟶ B`, write `f̂ = ⟨A, f⟩ : Over B`.
  An object of `(Over B)/f̂` is `⟨Y, m⟩` with `Y = ⟨E, e⟩ : Over B` and
  `m : OverHom Y f̂`, i.e. `m.f : E ⟶ A` with `m.f ≫ f = e`.  The pair `(E, m.f)`
  is EXACTLY an object of `Over A`, with `e = m.f ≫ f` forced.  So

      Over A  ≅  (Over B) / f̂                                (ISO of categories)

  is an isomorphism on the nose (not merely an equivalence).  Under it the pullback
  functor `f* : Over B → Over A` becomes "product with `f̂`" in `Over B`, whose right
  adjoint is the exponential `(−)^f̂` (available: `Over B` is a topos, hence has
  exponentials).  Transporting that exponential adjunction back across the iso gives

      f*  ⊣  Π_f .

  This file builds `Π_f` and the adjunction hom-iso at the right altitude (a real
  `Adjunction (baseChangeObj f) Π_f`), reusing `Over B`'s `HasExponentials`.
-/
import Fredy.S1_93_SlicePower
import Fredy.S1_53_SliceRegular
import Fredy.S1_913_ToposCoversEpis

open Freyd

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

section SliceOfSlice
variable {A B : 𝒞} (f : A ⟶ B)

/-- `f̂ = ⟨A, f⟩ : Over B`, the object of `Over B` "named" by `f`.  Slicing `Over B`
    over `f̂` reproduces `Over A` on the nose (see `Phi`/`Psi`). -/
def fHat : Over B := ⟨A, f⟩

/-- **`Φ : Over A → (Over B)/f̂`** on objects.  An object `X = ⟨E, x : E ⟶ A⟩` of
    `Over A` becomes the `(Over B)`-object `⟨E, x ≫ f⟩` sliced over `f̂` by the
    triangle `x : ⟨E, x≫f⟩ ⟶ f̂` (which commutes definitionally: `x ≫ f = x ≫ f`). -/
def PhiObj (X : Over A) : Over (fHat f) :=
  ⟨⟨X.dom, X.hom ≫ f⟩, ⟨X.hom, rfl⟩⟩

/-- `Φ` on morphisms: the SAME underlying arrow `h.f : X.dom ⟶ Y.dom`, which is a
    map of `Over B`-triangles over `f̂`. -/
def PhiMap {X Y : Over A} (h : OverHom X Y) :
    OverHom (PhiObj f X) (PhiObj f Y) :=
  ⟨⟨h.f, by show h.f ≫ (Y.hom ≫ f) = X.hom ≫ f; rw [← Cat.assoc, h.w]⟩,
    by apply OverHom.ext; show h.f ≫ Y.hom = X.hom; exact h.w⟩

/-- **`Ψ : (Over B)/f̂ → Over A`** on objects (the inverse of `Φ`).  An object
    `Z = ⟨⟨E,e⟩, m : ⟨E,e⟩ ⟶ f̂⟩` of `(Over B)/f̂` has `m.f : E ⟶ A` with
    `m.f ≫ f = e`; forget `e` and keep `⟨E, m.f⟩ : Over A`. -/
def PsiObj (Z : Over (fHat f)) : Over A :=
  ⟨Z.dom.dom, Z.hom.f⟩

/-- `Ψ` on morphisms: the underlying arrow `h.f.f`. -/
def PsiMap {Z W : Over (fHat f)} (h : OverHom Z W) :
    OverHom (PsiObj f Z) (PsiObj f W) :=
  ⟨h.f.f, by
    show h.f.f ≫ W.hom.f = Z.hom.f
    exact congrArg OverHom.f h.w⟩

/-- `Ψ ∘ Φ = id` on objects, ON THE NOSE. -/
@[simp] theorem Psi_Phi_obj (X : Over A) : PsiObj f (PhiObj f X) = X := rfl

end SliceOfSlice

/-! ## The slice-of-slice hom bijection (the load-bearing core)

  `Φ` is fully faithful: a map `X ⟶ Y` in `Over A` is the SAME data as a map
  `Φ X ⟶ Φ Y` in `(Over B)/f̂` (both are an arrow `X.dom ⟶ Y.dom` commuting with the
  structure maps into `A`).  We package the two directions as `phiHom`/`phiInv`. -/
section SliceOfSliceHom
variable {A B : 𝒞} (f : A ⟶ B)

/-- `Φ` on homs, packaged as a function `(X ⟶ Y) → (Φ X ⟶ Φ Y)`. -/
def phiHom {X Y : Over A} (h : OverHom X Y) : OverHom (PhiObj f X) (PhiObj f Y) :=
  PhiMap f h

/-- `Ψ` on homs, the inverse direction `(Φ X ⟶ Φ Y) → (X ⟶ Y)`. -/
def phiInv {X Y : Over A} (k : OverHom (PhiObj f X) (PhiObj f Y)) : OverHom X Y :=
  ⟨k.f.f, congrArg OverHom.f k.w⟩

@[simp] theorem phiInv_phiHom {X Y : Over A} (h : OverHom X Y) :
    phiInv f (phiHom f h) = h := OverHom.ext rfl

@[simp] theorem phiHom_phiInv {X Y : Over A} (k : OverHom (PhiObj f X) (PhiObj f Y)) :
    phiHom f (phiInv f k) = k := OverHom.ext (OverHom.ext rfl)

end SliceOfSliceHom

/-! ## Generic exponential transpose helpers

  In any category with exponentials, the EVALUATION TRANSPOSE of `c : Y ⟶ E^^A` is
  `transp c := (A × c) ≫ eval : A × Y ⟶ E`.  It is the two-sided inverse of `curry`
  and intertwines `expCovMap` (post-composition) with ordinary composition. -/

section ExpTranspose
variable [HasExponentials 𝒞]

/-- The evaluation transpose of `c : Y ⟶ E^^A`. -/
def transp {A E Y : 𝒞} (c : Y ⟶ E ^^ A) : prod A Y ⟶ E :=
  prodMap A Y (E ^^ A) c ≫ eval_exp A E

@[simp] theorem curry_transp {A E Y : 𝒞} (c : Y ⟶ E ^^ A) : curry (transp c) = c :=
  (curry_unique_eq rfl).symm

@[simp] theorem transp_curry {A E Y : 𝒞} (k : prod A Y ⟶ E) : transp (curry k) = k :=
  curry_eval_eq k

theorem transp_inj {A E Y : 𝒞} {c₁ c₂ : Y ⟶ E ^^ A} (h : transp c₁ = transp c₂) : c₁ = c₂ := by
  rw [← curry_transp c₁, ← curry_transp c₂, h]

/-- `transp` turns post-composition with `expCovMap p` into post-composition with `p`. -/
theorem transp_expCovMap {A E E' Y : 𝒞} (c : Y ⟶ E ^^ A) (p : E ⟶ E') :
    transp (c ≫ expCovMap A p) = transp c ≫ p := by
  dsimp [transp]
  rw [prodMap_comp, Cat.assoc, expCovMap_eval, ← Cat.assoc]

/-- `transp` turns precomposition with `u : Y' ⟶ Y` into precomposition with `(A × u)`. -/
theorem transp_precomp {A E Y Y' : 𝒞} (u : Y' ⟶ Y) (c : Y ⟶ E ^^ A) :
    transp (u ≫ c) = prodMap A Y' Y u ≫ transp c := by
  dsimp [transp]; rw [prodMap_comp, Cat.assoc]

end ExpTranspose

/-! ## §1.931  The dependent-product functor `Π_f`

  We now build `Π_f : Over A → Over B` and the adjunction `f* ⊣ Π_f`.

  The construction lives in the slice TOPOS `Over B` (which has exponentials,
  equalizers, a terminal object and binary products — all from `Topos (Over B)`).

  For `X : Over A` write `Pb := ⟨X.dom, X.hom ≫ f⟩ : Over B` and let
  `px : Pb ⟶ f̂` be the structural arrow `⟨X.hom, rfl⟩` (so `px.f = X.hom`).
  In `Over B` the two exponential maps
        α := expCovMap f̂ px        :  Pb ^^ f̂  ⟶  f̂ ^^ f̂          (post-compose with px)
        β := ! ≫ ⌜id_{f̂}⌝          :  Pb ^^ f̂  ⟶  f̂ ^^ f̂          (constant "name of id")
  have an equalizer `Π_f X`.  A generalized element `c : Y ⟶ Pb^^f̂` equalizes `α,β`
  iff its exponential transpose `k : f̂ × Y ⟶ Pb` satisfies `k ≫ px = snd`, i.e. iff
  `k` is a section of `px` — exactly the data of a map `f* Y ⟶ X` in `Over A`. -/

noncomputable section PiForall
variable {A B : 𝒞} (f : A ⟶ B) [Topos 𝒞]

/-- The structural arrow `px : f*(X) ⟶ f̂`, underlying `X.hom`. -/
def pxHom (X : Over A) : (reindexObj f X : Over B) ⟶ fHat f := ⟨X.hom, rfl⟩

/-- The exponential `f*(X) ^^ f̂` in `Over B`. -/
abbrev expPb (X : Over A) : Over B := exp (fHat f) (reindexObj f X)

/-- The exponential `f̂ ^^ f̂` in `Over B`. -/
abbrev expHatHat : Over B := exp (fHat f) (fHat f)

/-- `α := expCovMap px : Pb^^f̂ ⟶ f̂^^f̂` (post-compose with `px`). -/
def piAlpha (X : Over A) : OverHom (expPb f X) (expHatHat f) :=
  expCovMap (fHat f) (pxHom f X)

/-- `⌜id_{f̂}⌝ : one ⟶ f̂^^f̂`, the name of the identity on `f̂`.
    `prod f̂ one ≅ f̂` via `fst`, so the identity is `curry fst`. -/
def nameId : OverHom (one : Over B) (expHatHat f) :=
  curry (fst : prod (fHat f) (one : Over B) ⟶ fHat f)

/-- `β := ! ≫ ⌜id⌝ : Pb^^f̂ ⟶ f̂^^f̂`, the constant map at the name of `id_{f̂}`. -/
def piBeta (X : Over A) : OverHom (expPb f X) (expHatHat f) :=
  term (expPb f X) ⊚ nameId f

/-- **`Π_f X`**: the dependent product of `X` along `f`, as the equalizer in `Over B`
    of `α` and `β`.  (`@[reducible]` so equalizer lemmas unify against it.) -/
@[reducible] def piForallObj (X : Over A) : Over B := eqObj (piAlpha f X) (piBeta f X)

/-- `reindexObj` on morphisms: `m : X ⟶ X'` in `Over A` gives `m.f : f*(X) ⟶ f*(X')` in `Over B`
    (the same underlying arrow; it commutes since `m.f ≫ X'.hom = X.hom`). -/
def PbMap {X X' : Over A} (m : X ⟶ X') : (reindexObj f X : Over B) ⟶ reindexObj f X' :=
  ⟨m.f, by show m.f ≫ (X'.hom ≫ f) = X.hom ≫ f; rw [← Cat.assoc, m.w]⟩

@[simp] theorem PbMap_px {X X' : Over A} (m : X ⟶ X') :
    PbMap f m ≫ pxHom f X' = pxHom f X := OverHom.ext (by show m.f ≫ X'.hom = X.hom; exact m.w)

theorem PbMap_id (X : Over A) : PbMap f (Cat.id X) = Cat.id (reindexObj f X) := OverHom.ext rfl

theorem PbMap_comp {X X' X'' : Over A} (m : X ⟶ X') (n : X' ⟶ X'') :
    PbMap f (m ≫ n) = PbMap f m ≫ PbMap f n := OverHom.ext rfl

/-! ### The equalizer-membership characterization

  A map `c : Y ⟶ Pb^^f̂` factors through the equalizer `Π_f X` iff its transpose
  `transp c : f̂ × Y ⟶ Pb` is a section of `px`, i.e. `transp c ⊚ px = fst`. -/

/-- `transp (c ≫ α) = transp c ≫ px`. -/
theorem transp_piAlpha {X : Over A} {Y : Over B} (c : Y ⟶ expPb f X) :
    transp (c ≫ piAlpha f X) = transp c ≫ pxHom f X :=
  transp_expCovMap c (pxHom f X)

/-- `transp (c ≫ β) = fst`. -/
theorem transp_piBeta {X : Over A} {Y : Over B} (c : Y ⟶ expPb f X) :
    transp (c ≫ piBeta f X) = (fst : prod (fHat f) Y ⟶ fHat f) := by
  show transp (c ≫ (term (expPb f X) ≫ nameId f)) = _
  -- c ≫ term = term Y  (term is terminal in Over B).
  have hterm : c ≫ (term (expPb f X) ≫ nameId f) = term Y ≫ nameId f := by
    rw [← Cat.assoc, term_uniq (c ≫ term (expPb f X)) (term Y)]
  rw [hterm, transp_precomp, show transp (nameId f) = (fst : prod (fHat f) (one : Over B) ⟶ fHat f) from
    transp_curry _, prodMap_fst]

/-- The defining equivalence: `c` equalizes `α,β` iff `transp c ≫ px = fst`. -/
theorem equalizes_iff {X : Over A} {Y : Over B} (c : Y ⟶ expPb f X) :
    c ≫ piAlpha f X = c ≫ piBeta f X ↔ transp c ≫ pxHom f X = fst := by
  constructor
  · intro h
    rw [← transp_piAlpha, h, transp_piBeta]
  · intro h
    apply transp_inj
    rw [transp_piAlpha, h, transp_piBeta]

/-! ### The pullback-swap bridge `pt ≅ pt'`

  `prod (f̂) Y` (in `Over B`) and `baseChangeObj f Y` (in `Over A`) are built from the
  two pullbacks of the SAME cospan with the legs swapped:
    * `prod` uses `pullback f Y.hom`,    legs `q₁ : Pdom ⟶ A`, `q₂ : Pdom ⟶ Y.dom`;
    * `baseChange` uses `pullback Y.hom f`, legs `p₁ : Bdom ⟶ Y.dom`, `p₂ : Bdom ⟶ A`.
  We give the canonical iso `Pdom ≅ Bdom` exchanging the legs. -/

/-- The chosen pullback behind `prod (f̂) Y`: cospan `f, Y.hom`. -/
private def _PB (Y : Over B) : HasPullback (fHat f).hom Y.hom := HasPullbacks.has (fHat f).hom Y.hom
/-- The chosen pullback behind `baseChangeObj f Y`: cospan `Y.hom, f`. -/
private def _BC (Y : Over B) : HasPullback Y.hom f := HasPullbacks.has Y.hom f

/-- `Pdom ⟶ Bdom`: lift the swapped cone `(q₂, q₁)` into the base-change pullback. -/
def prodToBc (Y : Over B) : (_PB f Y).cone.pt ⟶ (_BC f Y).cone.pt :=
  (_BC f Y).lift ⟨(_PB f Y).cone.pt, (_PB f Y).cone.π₂, (_PB f Y).cone.π₁, ((_PB f Y).cone.w).symm⟩

/-- `Bdom ⟶ Pdom`: lift the swapped cone `(p₂, p₁)` into the product pullback. -/
def bcToProd (Y : Over B) : (_BC f Y).cone.pt ⟶ (_PB f Y).cone.pt :=
  (_PB f Y).lift ⟨(_BC f Y).cone.pt, (_BC f Y).cone.π₂, (_BC f Y).cone.π₁, ((_BC f Y).cone.w).symm⟩

@[simp] theorem prodToBc_p₁ (Y : Over B) : prodToBc f Y ≫ (_BC f Y).cone.π₁ = (_PB f Y).cone.π₂ :=
  (_BC f Y).lift_fst _
@[simp] theorem prodToBc_p₂ (Y : Over B) : prodToBc f Y ≫ (_BC f Y).cone.π₂ = (_PB f Y).cone.π₁ :=
  (_BC f Y).lift_snd _
@[simp] theorem bcToProd_q₁ (Y : Over B) : bcToProd f Y ≫ (_PB f Y).cone.π₁ = (_BC f Y).cone.π₂ :=
  (_PB f Y).lift_fst _
@[simp] theorem bcToProd_q₂ (Y : Over B) : bcToProd f Y ≫ (_PB f Y).cone.π₂ = (_BC f Y).cone.π₁ :=
  (_PB f Y).lift_snd _

/-- Pullback self-map uniqueness for the product pullback: a map agreeing with `id`
    on both legs is `id`. -/
private theorem _PB_self_id (Y : Over B) (u : (_PB f Y).cone.pt ⟶ (_PB f Y).cone.pt)
    (h₁ : u ≫ (_PB f Y).cone.π₁ = (_PB f Y).cone.π₁)
    (h₂ : u ≫ (_PB f Y).cone.π₂ = (_PB f Y).cone.π₂) : u = Cat.id _ := by
  have e := (_PB f Y).lift_uniq ⟨_, (_PB f Y).cone.π₁, (_PB f Y).cone.π₂, (_PB f Y).cone.w⟩
  rw [e u h₁ h₂, ← e (Cat.id _) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])]

private theorem _BC_self_id (Y : Over B) (u : (_BC f Y).cone.pt ⟶ (_BC f Y).cone.pt)
    (h₁ : u ≫ (_BC f Y).cone.π₁ = (_BC f Y).cone.π₁)
    (h₂ : u ≫ (_BC f Y).cone.π₂ = (_BC f Y).cone.π₂) : u = Cat.id _ := by
  have e := (_BC f Y).lift_uniq ⟨_, (_BC f Y).cone.π₁, (_BC f Y).cone.π₂, (_BC f Y).cone.w⟩
  rw [e u h₁ h₂, ← e (Cat.id _) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])]

/-- `bcToProd ≫ prodToBc = id` on the base-change pullback. -/
theorem bcToProd_prodToBc (Y : Over B) : bcToProd f Y ≫ prodToBc f Y = Cat.id _ := by
  apply _BC_self_id
  · rw [Cat.assoc, prodToBc_p₁, bcToProd_q₂]
  · rw [Cat.assoc, prodToBc_p₂, bcToProd_q₁]

/-- `prodToBc ≫ bcToProd = id` on the product pullback. -/
theorem prodToBc_bcToProd (Y : Over B) : prodToBc f Y ≫ bcToProd f Y = Cat.id _ := by
  apply _PB_self_id
  · rw [Cat.assoc, bcToProd_q₁, prodToBc_p₂]
  · rw [Cat.assoc, bcToProd_q₂, prodToBc_p₁]

/-! ### The adjunction hom-bijection

  `OverHom (f* Y) X  ≅  OverHom Y (Π_f X)`, the data of `f* ⊣ Π_f`. -/

/-- `eqMap`-projection out of `Π_f X`: the equalizer arrow `Π_f X ⟶ Pb^^f̂`. -/
def piEqMap (X : Over A) : eqObj (piAlpha f X) (piBeta f X) ⟶ expPb f X :=
  @eqMap (Over B) _ _ (expPb f X) (expHatHat f) (piAlpha f X) (piBeta f X)

/-- From a section `c : Y ⟶ Pb^^f̂` (`transp c ≫ px = fst`) we get a map into the equalizer. -/
def piLift {X : Over A} {Y : Over B} (c : Y ⟶ expPb f X) (h : transp c ≫ pxHom f X = fst) :
    Y ⟶ piForallObj f X :=
  eqLift (piAlpha f X) (piBeta f X) c ((equalizes_iff f c).mpr h)

@[simp] theorem piLift_eqMap {X : Over A} {Y : Over B} (c : Y ⟶ expPb f X)
    (h : transp c ≫ pxHom f X = fst) : piLift f c h ≫ piEqMap f X = c := by
  show piLift f c h ≫ @eqMap (Over B) _ _ (expPb f X) (expHatHat f) (piAlpha f X) (piBeta f X) = c
  exact eqLift_fac (piAlpha f X) (piBeta f X) c ((equalizes_iff f c).mpr h)

/-- `k.f ≫ X.hom = π₁_PB`, the section identity for the transpose underlying `piPhi g`. -/
private theorem _piPhi_hk {X : Over A} {Y : Over B} (g : OverHom (baseChangeObj f Y) X) :
    (prodToBc f Y ≫ g.f) ≫ X.hom = (_PB f Y).cone.π₁ := by
  rw [Cat.assoc]
  have : g.f ≫ X.hom = (_BC f Y).cone.π₂ := g.w
  rw [this, prodToBc_p₂]

/-- The transpose `k : prod f̂ Y ⟶ f*(X)` underlying `piPhi g`. -/
def piPhiK {X : Over A} {Y : Over B} (g : OverHom (baseChangeObj f Y) X) :
    prod (fHat f) Y ⟶ reindexObj f X :=
  ⟨prodToBc f Y ≫ g.f, by
    show (prodToBc f Y ≫ g.f) ≫ (X.hom ≫ f) = (_PB f Y).cone.π₁ ≫ f
    rw [← Cat.assoc, _piPhi_hk]⟩

/-- **`φ`**: `OverHom (f* Y) X → OverHom Y (Π_f X)`. -/
def piPhi {X : Over A} {Y : Over B} (g : OverHom (baseChangeObj f Y) X) : Y ⟶ piForallObj f X :=
  piLift f (curry (piPhiK f g)) (by rw [transp_curry]; exact OverHom.ext (_piPhi_hk f g))

/-- **`ψ`**: `OverHom Y (Π_f X) → OverHom (f* Y) X`.  Uses `transp (d ≫ eqMap)` and the
    section condition forced by the equalizer. -/
def piPsi {X : Over A} {Y : Over B} (d : Y ⟶ piForallObj f X) : OverHom (baseChangeObj f Y) X :=
  let c := d ≫ piEqMap f X
  have hsec : transp c ≫ pxHom f X = fst :=
    (equalizes_iff f c).mp (by
      show (d ≫ piEqMap f X) ≫ piAlpha f X = (d ≫ piEqMap f X) ≫ piBeta f X
      rw [Cat.assoc, Cat.assoc]
      show d ≫ (@eqMap (Over B) _ _ (expPb f X) (expHatHat f) (piAlpha f X) (piBeta f X) ≫ piAlpha f X)
         = d ≫ (@eqMap (Over B) _ _ (expPb f X) (expHatHat f) (piAlpha f X) (piBeta f X) ≫ piBeta f X)
      rw [eqMap_eq])
  ⟨bcToProd f Y ≫ (transp c).f, by
    show (bcToProd f Y ≫ (transp c).f) ≫ X.hom = (baseChangeObj f Y).hom
    show (bcToProd f Y ≫ (transp c).f) ≫ X.hom = (_BC f Y).cone.π₂
    rw [Cat.assoc]
    -- (transp c).f ≫ X.hom = (transp c ≫ px).f = fst.f = π₁_PB
    have : (transp c).f ≫ X.hom = (_PB f Y).cone.π₁ := congrArg OverHom.f hsec
    rw [this, bcToProd_q₁]⟩

/-- `transp (d ≫ eqMap)` underlying arrow, for `d : Y ⟶ Π_f X`.  Used to unfold `piPsi`. -/
private theorem _piPsi_f {X : Over A} {Y : Over B} (d : Y ⟶ piForallObj f X) :
    (piPsi f d).f = bcToProd f Y ≫ (transp (d ≫ piEqMap f X)).f := rfl

/-- The transpose underlying `piPhi g` equals `piPhiK g`. -/
private theorem _piPhi_transp {X : Over A} {Y : Over B} (g : OverHom (baseChangeObj f Y) X) :
    transp (piPhi f g ≫ piEqMap f X) = piPhiK f g := by
  show transp (piLift f (curry (piPhiK f g)) _ ≫ piEqMap f X) = _
  rw [piLift_eqMap, transp_curry]

/-- **`φψ`** round-trip: `piPsi (piPhi g) = g`. -/
theorem piPsi_piPhi {X : Over A} {Y : Over B} (g : OverHom (baseChangeObj f Y) X) :
    piPsi f (piPhi f g) = g := by
  apply OverHom.ext
  rw [_piPsi_f, _piPhi_transp]
  show bcToProd f Y ≫ (prodToBc f Y ≫ g.f) = g.f
  rw [← Cat.assoc, bcToProd_prodToBc, Cat.id_comp]

/-- **`ψφ`** round-trip: `piPhi (piPsi d) = d`. -/
theorem piPhi_piPsi {X : Over A} {Y : Over B} (d : Y ⟶ piForallObj f X) :
    piPhi f (piPsi f d) = d := by
  -- both `piPhi (piPsi d)` and `d` satisfy `· ≫ eqMap = d ≫ eqMap`; conclude by eqLift_uniq.
  have hc : piPhi f (piPsi f d) ≫ piEqMap f X = d ≫ piEqMap f X := by
    apply transp_inj
    rw [_piPhi_transp]
    apply OverHom.ext
    show prodToBc f Y ≫ (piPsi f d).f = (transp (d ≫ piEqMap f X)).f
    rw [_piPsi_f, ← Cat.assoc, prodToBc_bcToProd, Cat.id_comp]
  -- eqLift uniqueness:  both equal `eqLift (...) (d ≫ eqMap) (...)`.
  have huniq := @eqLift_uniq (Over B) _ _ (expPb f X) (expHatHat f) Y
    (piAlpha f X) (piBeta f X) (d ≫ piEqMap f X)
    (by
      show (d ≫ piEqMap f X) ≫ piAlpha f X = (d ≫ piEqMap f X) ≫ piBeta f X
      rw [Cat.assoc, Cat.assoc]
      show d ≫ (@eqMap (Over B) _ _ (expPb f X) (expHatHat f) (piAlpha f X) (piBeta f X) ≫ piAlpha f X)
         = d ≫ (@eqMap (Over B) _ _ (expPb f X) (expHatHat f) (piAlpha f X) (piBeta f X) ≫ piBeta f X)
      rw [eqMap_eq])
  exact (huniq (piPhi f (piPsi f d)) hc).trans (huniq d rfl).symm

/-- The equalizer arrow `piEqMap` is itself a section: `transp (piEqMap) ≫ px = fst`. -/
theorem piEqMap_section (X : Over A) : transp (piEqMap f X) ≫ pxHom f X = fst :=
  (equalizes_iff f (piEqMap f X)).mp
    (by
      show piEqMap f X ≫ piAlpha f X = piEqMap f X ≫ piBeta f X
      show @eqMap (Over B) _ _ (expPb f X) (expHatHat f) (piAlpha f X) (piBeta f X) ≫ piAlpha f X
         = @eqMap (Over B) _ _ (expPb f X) (expHatHat f) (piAlpha f X) (piBeta f X) ≫ piBeta f X
      rw [eqMap_eq])

/-! ### The functor `Π_f` -/

/-- The section identity for `piEqMap X ≫ expCovMap (Pb m)`. -/
private theorem _piForallMap_sec {X X' : Over A} (m : X ⟶ X') :
    transp (piEqMap f X ≫ expCovMap (fHat f) (PbMap f m)) ≫ pxHom f X' = fst := by
  rw [transp_expCovMap, Cat.assoc, PbMap_px, piEqMap_section]

/-- `Π_f` on morphisms: `m : X ⟶ X'` in `Over A` post-composes the transpose with `Pb m`. -/
def piForallMap {X X' : Over A} (m : X ⟶ X') : piForallObj f X ⟶ piForallObj f X' :=
  piLift f (piEqMap f X ≫ expCovMap (fHat f) (PbMap f m)) (_piForallMap_sec f m)

@[simp] theorem piForallMap_eqMap {X X' : Over A} (m : X ⟶ X') :
    piForallMap f m ≫ piEqMap f X' = piEqMap f X ≫ expCovMap (fHat f) (PbMap f m) :=
  piLift_eqMap f _ _

/-- The equalizer arrow `piEqMap` is monic: maps into `Π_f X` agreeing after `≫ piEqMap` agree. -/
theorem piEqMap_mono {X : Over A} {Y : Over B} {u v : Y ⟶ piForallObj f X}
    (h : u ≫ piEqMap f X = v ≫ piEqMap f X) : u = v := by
  have huniq := @eqLift_uniq (Over B) _ _ (expPb f X) (expHatHat f) Y
    (piAlpha f X) (piBeta f X) (u ≫ piEqMap f X)
    (by
      show (u ≫ piEqMap f X) ≫ piAlpha f X = (u ≫ piEqMap f X) ≫ piBeta f X
      rw [Cat.assoc, Cat.assoc]
      show u ≫ (@eqMap (Over B) _ _ (expPb f X) (expHatHat f) (piAlpha f X) (piBeta f X) ≫ piAlpha f X)
         = u ≫ (@eqMap (Over B) _ _ (expPb f X) (expHatHat f) (piAlpha f X) (piBeta f X) ≫ piBeta f X)
      rw [eqMap_eq])
  exact (huniq u rfl).trans (huniq v h.symm).symm

/-- `Π_f` preserves identities. -/
theorem piForallMap_id (X : Over A) :
    piForallMap f (Cat.id X) = Cat.id (piForallObj f X) := by
  apply piEqMap_mono
  rw [piForallMap_eqMap, PbMap_id, expCovMap_id, Cat.comp_id, Cat.id_comp]

/-- `Π_f` preserves composition. -/
theorem piForallMap_comp {X X' X'' : Over A} (m : X ⟶ X') (n : X' ⟶ X'') :
    piForallMap f (m ≫ n) = piForallMap f m ≫ piForallMap f n := by
  apply piEqMap_mono
  rw [Cat.assoc]
  simp only [piForallMap_eqMap]
  rw [PbMap_comp, expCovMap_comp, ← Cat.assoc, ← Cat.assoc (piForallMap f m), piForallMap_eqMap,
      Cat.assoc]

/-- **`Π_f` is a functor `Over A → Over B`.** -/
instance piForallFunctor : Functor (piForallObj f) where
  map m := piForallMap f m
  map_id X := piForallMap_id f X
  map_comp m n := piForallMap_comp f m n

/-! ### Naturality of `φ = piPhi`

  `φ` is the composite `(f* Y ⟶ X) →[Φ-iso] (transpose section) →[curry] (Y ⟶ Π_f X)`.
  Both naturality squares reduce, after the (mono) equalizer arrow and the `transp`
  bijection, to underlying-arrow identities about the pullback-swap maps. -/

/-- **`φ_nat_right`**: `piPhi (g ≫ b) = piPhi g ≫ Π_f b`. -/
theorem piPhi_nat_right {Y : Over B} {X X' : Over A}
    (g : OverHom (baseChangeObj f Y) X) (b : X ⟶ X') :
    piPhi f (g ≫ b) = piPhi f g ≫ piForallMap f b := by
  apply piEqMap_mono
  apply transp_inj
  -- LHS: transp(piPhi(g≫b) ≫ eqMap) = piPhiK (g≫b)
  rw [_piPhi_transp]
  -- RHS: (piPhi g ≫ Π_f b) ≫ eqMap = piPhi g ≫ (eqMap ≫ expCovMap (PbMap b))
  rw [Cat.assoc, piForallMap_eqMap, ← Cat.assoc, transp_expCovMap, _piPhi_transp]
  -- piPhiK (g≫b) = piPhiK g ≫ PbMap b  (underlying arrows)
  apply OverHom.ext
  show prodToBc f Y ≫ (g ≫ b).f = (prodToBc f Y ≫ g.f) ≫ b.f
  show prodToBc f Y ≫ (g.f ≫ b.f) = (prodToBc f Y ≫ g.f) ≫ b.f
  rw [Cat.assoc]

/-- Underlying first projection of `prod (f̂) Y` in `Over B` is `π₁_PB`. -/
private theorem _fst_f (Y : Over B) :
    (fst : prod (fHat f) Y ⟶ fHat f).f = (_PB f Y).cone.π₁ := rfl
/-- Underlying second projection of `prod (f̂) Y` in `Over B` is `π₂_PB`. -/
private theorem _snd_f (Y : Over B) :
    (snd : prod (fHat f) Y ⟶ Y).f = (_PB f Y).cone.π₂ := rfl

/-- `prodMap`'s underlying first-projection law (in `Over B`). -/
private theorem _prodMap_fst_f {Y' Y : Over B} (a : Y' ⟶ Y) :
    (prodMap (fHat f) Y' Y a).f ≫ (_PB f Y).cone.π₁ = (_PB f Y').cone.π₁ :=
  congrArg OverHom.f (prodMap_fst (fHat f) Y' Y a)
/-- `prodMap`'s underlying second-projection law (in `Over B`). -/
private theorem _prodMap_snd_f {Y' Y : Over B} (a : Y' ⟶ Y) :
    (prodMap (fHat f) Y' Y a).f ≫ (_PB f Y).cone.π₂ = (_PB f Y').cone.π₂ ≫ a.f :=
  congrArg OverHom.f (prodMap_snd (fHat f) Y' Y a)

/-- baseChangeMap leg laws (with `g = f`): the lift through the `Y`-pullback. -/
private theorem _bcMap_π₁ {Y' Y : Over B} (a : Y' ⟶ Y) :
    (baseChangeMap f a).f ≫ (_BC f Y).cone.π₁ = (_BC f Y').cone.π₁ ≫ a.f :=
  (_BC f Y).lift_fst (baseChangeCone f a)
private theorem _bcMap_π₂ {Y' Y : Over B} (a : Y' ⟶ Y) :
    (baseChangeMap f a).f ≫ (_BC f Y).cone.π₂ = (_BC f Y').cone.π₂ :=
  (_BC f Y).lift_snd (baseChangeCone f a)

/-- Two maps into the base-change pullback agreeing on both legs are equal. -/
private theorem _BC_hom_ext {Y : Over B} {W : 𝒞} {u v : W ⟶ (_BC f Y).cone.pt}
    (h₁ : u ≫ (_BC f Y).cone.π₁ = v ≫ (_BC f Y).cone.π₁)
    (h₂ : u ≫ (_BC f Y).cone.π₂ = v ≫ (_BC f Y).cone.π₂) : u = v := by
  have hc : (_BC f Y).cone.π₁ ≫ Y.hom = (_BC f Y).cone.π₂ ≫ f := (_BC f Y).cone.w
  let c : Cone Y.hom f := ⟨W, u ≫ (_BC f Y).cone.π₁, u ≫ (_BC f Y).cone.π₂,
    by rw [Cat.assoc, Cat.assoc, hc]⟩
  exact ((_BC f Y).lift_uniq c u rfl rfl).trans ((_BC f Y).lift_uniq c v h₁.symm h₂.symm).symm

/-- **Bridge naturality**: the pullback-swap `prodToBc` intertwines `baseChangeMap` (the
    action of `f*`) and `prodMap` (the action of `prod f̂ −`). -/
theorem prodToBc_baseChangeMap {Y' Y : Over B} (a : Y' ⟶ Y) :
    prodToBc f Y' ≫ (baseChangeMap f a).f = (prodMap (fHat f) Y' Y a).f ≫ prodToBc f Y := by
  apply _BC_hom_ext
  · -- ≫ π₁_BC(Y):  both sides = π₂_PB(Y') ≫ a.f
    rw [Cat.assoc, _bcMap_π₁, ← Cat.assoc, prodToBc_p₁, Cat.assoc, prodToBc_p₁, _prodMap_snd_f]
  · -- ≫ π₂_BC(Y):  both sides = π₁_PB(Y')
    rw [Cat.assoc, _bcMap_π₂, prodToBc_p₂, Cat.assoc, prodToBc_p₂, _prodMap_fst_f]

/-- **`φ_nat_left`**: `piPhi (f* a ≫ g) = a ≫ piPhi g`, for `a : Y' ⟶ Y`. -/
theorem piPhi_nat_left {Y' Y : Over B} {X : Over A}
    (a : Y' ⟶ Y) (g : OverHom (baseChangeObj f Y) X) :
    piPhi f (Functor.map (F := baseChangeObj f) a ≫ g) = a ≫ piPhi f g := by
  apply piEqMap_mono
  apply transp_inj
  -- LHS: transp(piPhi(f*a ≫ g) ≫ eqMap) = piPhiK (f*a ≫ g),  .f = prodToBc Y' ≫ (f*a).f ≫ g.f
  rw [_piPhi_transp]
  -- RHS: (a ≫ piPhi g) ≫ eqMap = a ≫ (piPhi g ≫ eqMap);
  --   transp (a ≫ d) = prodMap f̂ Y' Y a ≫ transp d  (transp_precomp);
  --   transp (piPhi g ≫ eqMap) = piPhiK g.
  rw [Cat.assoc, transp_precomp, _piPhi_transp]
  apply OverHom.ext
  -- `Functor.map a = baseChangeMap f a`; reduce to the bridge identity, cancel `≫ g.f`.
  show prodToBc f Y' ≫ ((baseChangeMap f a).f ≫ g.f)
     = (prodMap (fHat f) Y' Y a).f ≫ prodToBc f Y ≫ g.f
  rw [← Cat.assoc, prodToBc_baseChangeMap, Cat.assoc]

/-! ### The adjunction `f* ⊣ Π_f` -/

/-- **§1.931**: the pullback functor `f* = baseChangeObj f : Over B → Over A` is LEFT
    ADJOINT to the dependent-product functor `Π_f = piForallObj f : Over A → Over B`.
    The hom-bijection `OverHom (f* Y) X ≅ OverHom Y (Π_f X)` is `piPsi`/`piPhi`, carved
    out of the slice-topos exponential adjunction by the equalizer `Π_f X`. -/
def sliceForallAdj : Adjunction (baseChangeObj f) (piForallObj f) where
  φ g := piPhi f g
  ψ c := piPsi f c
  φψ c := piPhi_piPsi f c
  ψφ g := piPsi_piPhi f g
  φ_nat_left a g := piPhi_nat_left f a g
  φ_nat_right g b := piPhi_nat_right f g b

end PiForall

/-! ## §1.933  `f*` preserves epis, hence covers (the regularity payload)

  A LEFT adjoint preserves epimorphisms (`leftAdjoint_preserves_epi`).  The pullback
  functor `f* = baseChangeObj f` IS a left adjoint (`sliceForallAdj`), so it preserves
  epis.  In the slice topos `Over B`, epis coincide with covers (`cover_iff_epi`, since
  `Over B` is a topos), so `f*` preserves covers.  This is precisely
  pullback-stability of covers — the `PullbacksTransferCovers` content.  See the file
  trailer for the exact wiring to `topos_is_regular_real`. -/

/-- **A LEFT adjoint preserves epimorphisms.**  If `F ⊣ G` and `e` is epic, then `F e`
    is epic.  Proof: `F e ≫ a = F e ≫ b` transposes (via `φ_nat_left`) to
    `e ≫ φ a = e ≫ φ b`; cancel the epi `e` to get `φ a = φ b`, then `φ` injective. -/
theorem leftAdjoint_preserves_epi {𝒟 : Type u} [Cat.{v} 𝒟]
    {F : 𝒞 → 𝒟} {G : 𝒟 → 𝒞} [Functor F] [Functor G] (adj : F ⊣ G)
    {X Y : 𝒞} {e : X ⟶ Y} (he : ∀ {Z : 𝒞} (a b : Y ⟶ Z), e ≫ a = e ≫ b → a = b)
    {W : 𝒟} (a b : F Y ⟶ W) (hab : Functor.map e ≫ a = Functor.map e ≫ b) : a = b := by
  apply φ_inj adj
  apply he (adj.φ a) (adj.φ b)
  rw [← adj.φ_nat_left, ← adj.φ_nat_left, hab]

section PullbackPreservesEpi
variable {A B : 𝒞} (f : A ⟶ B) [Topos 𝒞]

/-- **The pullback functor `f*` preserves epis** — instance of `leftAdjoint_preserves_epi`
    applied to `f* ⊣ Π_f` (`sliceForallAdj`).  `f* Y = baseChangeObj f Y`, the pullback of
    `Y` along `f` in the slice. -/
theorem baseChange_preserves_epi {X Y : Over B} {e : X ⟶ Y}
    (he : ∀ {Z : Over B} (a b : Y ⟶ Z), e ≫ a = e ≫ b → a = b)
    {W : Over A} (a b : baseChangeObj f Y ⟶ W)
    (hab : Functor.map (F := baseChangeObj f) e ≫ a = Functor.map (F := baseChangeObj f) e ≫ b) :
    a = b :=
  leftAdjoint_preserves_epi (sliceForallAdj f) he a b hab

/-- **The pullback functor `f*` preserves covers**, in the slice topos.  `Cover` in
    `Over B`/`Over A` coincides with epic (`cover_iff_epi`, both are toposes via `overTopos`),
    and `f*` preserves epis (`baseChange_preserves_epi`).  This is the slice form of
    pullback-stability of covers. -/
theorem baseChange_preserves_cover {X Y : Over B} {e : X ⟶ Y} (he : Cover e) :
    Cover (Functor.map (F := baseChangeObj f) e) := by
  -- Over B and Over A are toposes; use cover ⟺ epic on both sides.
  have heEpi : ∀ {Z : Over B} (a b : Y ⟶ Z), e ≫ a = e ≫ b → a = b :=
    fun {Z} a b h => (cover_iff_epi (𝒞 := Over B) e).mp he a b h
  have hFeEpi : ∀ {Z : Over A} (a b : baseChangeObj f Y ⟶ Z),
      Functor.map (F := baseChangeObj f) e ≫ a = Functor.map (F := baseChangeObj f) e ≫ b → a = b :=
    fun {Z} a b h => baseChange_preserves_epi f heEpi a b h
  rw [cover_iff_epi (𝒞 := Over A) (Functor.map (F := baseChangeObj f) e)]; exact hFeEpi

end PullbackPreservesEpi

/-! ## §1.945  `PullbacksTransferCovers` for a bare topos — closing `topos_is_regular_real`

  Given a topos `𝒞`, the pullback of a cover is a cover.  The non-circular route uses the
  right-adjoint payload `f*` PRESERVES covers (`baseChange_preserves_cover`), NOT the (still
  open) base `PullbacksTransferCovers 𝒞`.

  Plan, for `f : A ⟶ B` a cover and `g : C ⟶ B`:
    * In `Over B`, the terminal map `mf : f̂ = ⟨A,f⟩ ⟶ ⟨B, id_B⟩` has `mf.f = f`, hence is a slice
      cover (`cover_of_cover_f`).
    * `g* = baseChangeObj g` preserves it: `Cover (baseChangeMap g mf)` in `Over C`.
    * `cover_f_of_cover` makes its underlying base map a cover; that map is the lift into the chosen
      `g*⟨B,id⟩`-pullback, which equals `pf.cone.π₂` post-composed with the comparison into the
      `id_B`-pullback.  We instead read off `pf.cone.π₂` directly and bridge `c.π₂` by the
      universal-property comparison iso (`cover_precomp_iso`). -/

/-- **Cover post-composed with an iso is a cover** (the post-composition dual of
    `cover_precomp_iso`).  If `h` is a cover and `i` iso, then `h ≫ i` is a cover:
    a monic `m` factoring `h ≫ i` also factors `h` (via `g ≫ i⁻¹`), so `h`-cover
    forces `m` iso. -/
theorem cover_postcomp_iso {X Y Y' : 𝒞} {h : X ⟶ Y} (hc : Cover h) {i : Y ⟶ Y'}
    (hi : IsIso i) : Cover (h ≫ i) := by
  obtain ⟨i', hi1, hi2⟩ := hi
  intro C m c hm hcm
  -- `c ≫ m = h ≫ i`, so `(c ≫ (i' ≫ m … )) ` -- factor `h` through `m`? No: through a NEW monic.
  -- Instead push `i'` in: `h = (h ≫ i) ≫ i' = (c ≫ m) ≫ i' = c ≫ (m ≫ i')`.
  -- `m ≫ i'` is monic (m monic, i' iso ⇒ monic); `h`-cover forces it iso ⇒ `m` iso.
  have hmi'_mono : Monic (m ≫ i') := by
    intro W a b hab
    apply hm
    -- a ≫ m = b ≫ m from a ≫ (m ≫ i') = b ≫ (m ≫ i') and i iso.
    have : (a ≫ m) ≫ i' = (b ≫ m) ≫ i' := by rw [Cat.assoc, Cat.assoc]; exact hab
    -- cancel i' (post-compose i): right-cancel by composing with i.
    calc a ≫ m = (a ≫ m) ≫ Cat.id Y' := (Cat.comp_id _).symm
      _ = (a ≫ m) ≫ (i' ≫ i) := by rw [hi2]
      _ = ((a ≫ m) ≫ i') ≫ i := (Cat.assoc _ _ _).symm
      _ = ((b ≫ m) ≫ i') ≫ i := by rw [this]
      _ = (b ≫ m) ≫ (i' ≫ i) := Cat.assoc _ _ _
      _ = (b ≫ m) ≫ Cat.id Y' := by rw [hi2]
      _ = b ≫ m := Cat.comp_id _
  have hfac : c ≫ (m ≫ i') = h := by
    calc c ≫ (m ≫ i') = (c ≫ m) ≫ i' := (Cat.assoc _ _ _).symm
      _ = (h ≫ i) ≫ i' := by rw [hcm]
      _ = h ≫ (i ≫ i') := Cat.assoc _ _ _
      _ = h ≫ Cat.id Y := by rw [hi1]
      _ = h := Cat.comp_id _
  -- `m ≫ i'` iso; then `m = (m ≫ i') ≫ i` is iso (iso ∘ iso).
  have hmi'_iso : IsIso (m ≫ i') := hc (m ≫ i') c hmi'_mono hfac
  -- m = (m ≫ i') ≫ i.
  have hm_eq : m = (m ≫ i') ≫ i := by rw [Cat.assoc, hi2, Cat.comp_id]
  rw [hm_eq]; exact isIso_comp hmi'_iso ⟨i', hi1, hi2⟩

noncomputable section ToposTransfer
variable [Topos 𝒞]

/-- The terminal-shaped object `⟨B, id_B⟩ : Over B`.  (Used only as the codomain of the
    structure-map-as-slice-arrow.) -/
private def _idB (B : 𝒞) : Over B := ⟨B, Cat.id B⟩

/-- The slice terminal map `f̂ = ⟨A,f⟩ ⟶ ⟨B, id_B⟩`, underlying `f`. -/
private def _mfTerm {A B : 𝒞} (f : A ⟶ B) : OverHom (fHat f) (_idB B) :=
  ⟨f, by show f ≫ Cat.id B = f; exact Cat.comp_id f⟩

/-- The structure map of `g*(⟨B,id_B⟩)` — projection `π₂` of the pullback of `id_B`
    along `g` — is an iso.  Its inverse is the lift of the cone `(g, id_C)`. -/
private theorem _bcIdB_hom_iso {B C : 𝒞} (g : C ⟶ B) :
    IsIso (baseChangeObj g (_idB B)).hom := by
  -- `(baseChangeObj g (_idB B)).hom = (HasPullbacks.has (id_B) g).cone.π₂`.
  let pb := HasPullbacks.has (_idB B).hom g
  -- cone (g, id_C) over the cospan (id_B, g):  g ≫ id_B = id_C ≫ g.
  let cC : Cone (_idB B).hom g := ⟨C, g, Cat.id C, by
    show g ≫ Cat.id B = Cat.id C ≫ g; rw [Cat.comp_id, Cat.id_comp]⟩
  refine ⟨pb.lift cC, ?_, ?_⟩
  · -- π₂ ≫ lift cC = id_pt : both lift the chosen cone (π₁, π₂) into the pullback.
    show pb.cone.π₂ ≫ pb.lift cC = Cat.id pb.cone.pt
    have huniq := pb.lift_uniq pb.cone
    rw [huniq (Cat.id pb.cone.pt) (Cat.id_comp _) (Cat.id_comp _)]
    refine huniq (pb.cone.π₂ ≫ pb.lift cC) ?_ ?_
    · -- (π₂ ≫ lift) ≫ π₁ = π₁:  use π₁ = π₂ ≫ id_B  (cone.w with id_B) and lift_fst.
      rw [Cat.assoc, pb.lift_fst cC]
      show pb.cone.π₂ ≫ g = pb.cone.π₁
      -- cone.w : π₁ ≫ id_B = π₂ ≫ g, and π₁ ≫ id_B = π₁.
      have hw : pb.cone.π₁ ≫ (_idB B).hom = pb.cone.π₂ ≫ g := pb.cone.w
      have hw' : pb.cone.π₁ = pb.cone.π₂ ≫ g := by
        rw [← hw]; exact (Cat.comp_id pb.cone.π₁).symm
      exact hw'.symm
    · rw [Cat.assoc, pb.lift_snd cC]; show pb.cone.π₂ ≫ Cat.id C = pb.cone.π₂; rw [Cat.comp_id]
  · show pb.lift cC ≫ pb.cone.π₂ = Cat.id C; rw [pb.lift_snd cC]

/-- **The chosen pullback `π₂` of a cover is a cover.**  In `Over B`, `f̂ ⟶ ⟨B,id⟩` is a
    slice cover (underlying map `f`); `g*` preserves covers; its underlying base map is a
    cover, and the slice over-hom law identifies it as `π₂ ≫ (iso)`. -/
private theorem _chosenPi2_cover {A B C : 𝒞} (f : A ⟶ B) (g : C ⟶ B) (hf : Cover f) :
    Cover (HasPullbacks.has f g).cone.π₂ := by
  -- mf is a slice cover; g* preserves it; its underlying base map is a cover.
  have hmf : Cover (𝒞 := Over B) (_mfTerm f) := cover_of_cover_f (_mfTerm f) hf
  have hbc : Cover (Functor.map (F := baseChangeObj g) (_mfTerm f)) :=
    baseChange_preserves_cover g hmf
  have hbcf : Cover (Functor.map (F := baseChangeObj g) (_mfTerm f)).f :=
    cover_f_of_cover (Functor.map (F := baseChangeObj g) (_mfTerm f)) hbc
  -- The over-hom law: `(g* mf).f ≫ (g*⟨B,id⟩).hom = (g* f̂).hom`.
  -- `(g* f̂).hom = (HasPullbacks.has f g).cone.π₂`  (since `(fHat f).hom = f`).
  -- `(g*⟨B,id⟩).hom` is an iso (`_bcIdB_hom_iso`), so `π₂ = cover ≫ iso` is a cover.
  have hw : (Functor.map (F := baseChangeObj g) (_mfTerm f)).f ≫ (baseChangeObj g (_idB B)).hom
      = (baseChangeObj g (fHat f)).hom :=
    (Functor.map (F := baseChangeObj g) (_mfTerm f)).w
  have hπ₂ : (baseChangeObj g (fHat f)).hom = (HasPullbacks.has f g).cone.π₂ := rfl
  rw [← hπ₂, ← hw]
  -- unfold `Cover` by hand to dodge the `Cover`-def `{C}`-binder clash with section `C`.
  intro D m gg hm hgm
  exact cover_postcomp_iso hbcf (_bcIdB_hom_iso g) m gg hm hgm

/-- **§1.945 — for a bare topos, the pullback of a cover is a cover.**  Closes the residual
    behind `topos_is_regular_real`.  Non-circular: the cover-stability of `f*` comes from the
    right-adjoint `Π_f` (`baseChange_preserves_cover`), not from any assumed base
    `PullbacksTransferCovers 𝒞`.  An arbitrary pullback cone `c` of `(f,g)` is iso to the chosen
    pullback; `cover_precomp_iso` transports `Cover (chosen π₂)` to `Cover c.π₂`. -/
instance toposPullbacksTransferCovers : PullbacksTransferCovers 𝒞 where
  pullbacks_transfer_covers {A₁ B₁ C₁} f g c hc hf := by
    -- The chosen pullback π₂ is a cover.
    have hchosen : Cover (HasPullbacks.has f g).cone.π₂ := _chosenPi2_cover f g hf
    -- Comparison iso `j : c.pt ≅ chosen.pt` with `j ≫ chosen.π₂ = c.π₂`.
    let pf := HasPullbacks.has f g
    -- `c` is a pullback, so it lifts the chosen cone; `pf.cone` is a pullback, so it lifts `c`.
    obtain ⟨j, ⟨_hj₁, hj₂⟩, _⟩ := hc pf.cone           -- j : pf.cone.pt ⟶ c.pt
    have hcj := pf.cone_isPullback c                    -- lift of c into chosen
    obtain ⟨k, ⟨hk₁, hk₂⟩, kuniq⟩ := hcj                -- k : c.pt ⟶ pf.cone.pt
    -- k is a two-sided inverse of j (both pullback self-maps that fix the legs are id).
    have hkj_id : k ≫ j = Cat.id c.pt := by
      -- c.IsPullback self-uniqueness:  k ≫ j and id both lift c into c.
      obtain ⟨_, _, cuniq⟩ := hc c
      rw [cuniq (k ≫ j) (by rw [Cat.assoc, _hj₁, hk₁]) (by rw [Cat.assoc, hj₂, hk₂]),
          cuniq (Cat.id c.pt) (Cat.id_comp _) (Cat.id_comp _)]
    have hjk_id : j ≫ k = Cat.id pf.cone.pt := by
      -- self-uniqueness of the CHOSEN pullback `pf.cone`: both `j ≫ k` and `id` lift `pf.cone`.
      have puniq := pf.lift_uniq pf.cone
      rw [puniq (j ≫ k) (by rw [Cat.assoc, hk₁, _hj₁]) (by rw [Cat.assoc, hk₂, hj₂]),
          puniq (Cat.id pf.cone.pt) (Cat.id_comp _) (Cat.id_comp _)]
    -- `c.π₂ = k ≫ pf.cone.π₂`, and `k` is iso, so `cover_precomp_iso`.
    have hkiso : IsIso k := ⟨j, hkj_id, hjk_id⟩
    rw [← hk₂]
    -- unfold `Cover` by hand to dodge the `Cover`-def `{C}`-binder clash with section `C₁`.
    intro D m gg hm hgm
    exact cover_precomp_iso hkiso hchosen m gg hm hgm

end ToposTransfer

end Freyd
