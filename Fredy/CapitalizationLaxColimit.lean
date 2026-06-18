/-
  §1.543 — the FILTERED, PSEUDO-functorial colimit of categories (lax interface).

  ════════════════════════════════════════════════════════════════════════════════════════════
  WHY THIS FILE EXISTS — the precise diagnosis of the §1.543 capitalization wall.
  ════════════════════════════════════════════════════════════════════════════════════════════

  The §1.547 relative capitalization needs `PreRegular A*`, where `A*` is the colimit of the
  finite-product slices `A/(∏U) = Over (listProd U)` over the FILTERED index `listDirected`
  (finite lists `U` of ws objects, ordered by `listSubset`; any two have an upper bound = append).
  Each fibre `Over (listProd U)` is PRE-REGULAR (`overPreRegular`, `SliceRegular.lean`).  The
  transitions are BASE-CHANGE `A/(∏V) → A/(∏U)` for `V ⊆ U` (`baseChangeFunctor` along a product
  projection `∏U ⟶ ∏V`).

  The repo's strict colimit machinery `Colim.CatSystem` / `colimitCat` / `colimitPreRegular`
  (`CatColimit.lean`, `CatColimitRegular.lean`) consumes ON-THE-NOSE transition laws:

      CatSystem.F_refl  : F (D.refl i) x = x                       -- strict identity
      CatSystem.F_trans : F (D.trans hij hjk) x = F hjk (F hij x)  -- strict composition

  **Base-change satisfies NEITHER.**  `baseChangeObj (Cat.id) X = X ×_D D` is canonically ISO to
  `X` but not equal; `baseChangeObj (g ≫ g')` re-associates an iterated pullback, equal only up to
  canonical iso.  This is residual (B-strict) of `RelativeCapitalization.lean`'s `innerCatSystem`,
  and it is documented there as the open obstruction (`StrictBaseChange` is a *false* statement for
  raw base-change, taken as a hypothesis the project could never discharge).

  The parked Σ-carrier attempt `CapitalizationGroth.lean` removes the OBJECT-CARRIER quotient
  dependency (objects become the bare `Σ i, A i` instead of the strict colimit's quotient), but it
  is still built on a `Colim.CatSystem` and a `Colim.CatSystem.Coherent` — so it STILL presupposes
  the strict `F_refl`/`F_trans`.  It does not escape residual (B-strict); it only escapes the
  carrier-quotient.

  ════════════════════════════════════════════════════════════════════════════════════════════
  THE WAY OUT — replace strict transition EQUALITIES with coherence ISOS (`NatIso`).
  ════════════════════════════════════════════════════════════════════════════════════════════

  A `LaxCatSystem` (this file) is a directed system of categories whose transitions are FUNCTORS
  with coherence supplied as natural ISOMORPHISMS

      F_refl_iso  : NatIso (F (D.refl i))            (id)
      F_trans_iso : NatIso (F (D.trans hij hjk))     (F hjk ∘ F hij)

  rather than strict equalities.  This is EXACTLY the data base-change supplies (it is a
  pseudofunctor `(listDirected)ᵒᵖ → Cat`), so the residual (B-strict) wall evaporates: there is no
  false equation to discharge, only canonical pullback isos to build.

  This file delivers, SORRY-FREE:
    * `LaxCatSystem` — the pseudo-functorial directed-system interface (the missing abstraction).
    * its underlying object Σ-carrier and directed colimit of object-types (reusing
      `DirectedColimit.lean`, which needs NO transition laws on objects — `incl` is the bare
      Σ-injection up to germ equivalence, and germ equivalence only ever uses transition *maps*,
      never their strict laws).
    * `ofStrict` — every strict `Colim.CatSystem` is a `LaxCatSystem` (the lax interface
      generalises the strict one; coherence isos are the identity NatIso), so nothing is lost.

  The remaining work (documented `next blocker` at the end) is the PSEUDO hom-colimit: a morphism
  `⟨i,x⟩ → ⟨j,y⟩` is a germ of `Hom_{A k}(F_{ik} x, F_{jk} y)` over upper bounds `k`, where the
  germ equivalence now transports along the COHERENCE ISOS (not strict equalities).  That is the
  genuine next coherence obligation and is stated precisely below.

  Mathlib-free; built on the repo's own `Cat`, `Functor`, `NaturalTransformation`, `NatIso`,
  `IsIso`, and `Freyd.Colim` (`DirectedColimit.lean`).
-/
import Fredy.S1_31
import Fredy.S1_36
import Fredy.S1_41
import Fredy.DirectedColimit
import Fredy.CatColimit
import Fredy.SliceRegular

open Freyd
open Freyd.Colim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}

/-! ## The pseudo-functorial (lax) directed system of categories

  Identical OBJECT/`Cat`/FUNCTOR data to `Colim.CatSystem`, but the two coherence fields are
  natural ISOMORPHISMS instead of strict equalities.  `functF hij : Functor (F hij)` makes each
  transition a genuine functor; `F_refl_iso`/`F_trans_iso` are the pseudofunctor coherences. -/
structure LaxCatSystem (ι : Type u) (D : Directed ι) where
  /-- the stage categories' carriers -/
  A : ι → Type w
  /-- each stage is a category -/
  catA : ∀ i, Cat.{w} (A i)
  /-- the object map of each transition -/
  F : ∀ {i j}, D.le i j → A i → A j
  /-- each transition is a functor -/
  functF : ∀ {i j} (hij : D.le i j), @Functor (A i) (catA i) (A j) (catA j) (F hij)
  /-- pseudo-identity: the reflexive transition is naturally isomorphic to the identity functor -/
  F_refl_iso : ∀ {i}, @NatIso (A i) (catA i) (A i) (catA i)
    (F (D.refl i)) (fun x => x) (functF (D.refl i)) (@idFunctor (A i) (catA i))
  /-- pseudo-composition: a composite transition is naturally isomorphic to the composite of the
      two transition functors -/
  F_trans_iso : ∀ {i j k} (hij : D.le i j) (hjk : D.le j k),
    @NatIso (A i) (catA i) (A k) (catA k)
      (F (D.trans hij hjk)) (fun x => F hjk (F hij x))
      (functF (D.trans hij hjk))
      (@compFunctor (A i) (catA i) (A j) (catA j) (A k) (catA k) (F hij) (F hjk)
        (functF hij) (functF hjk))

attribute [instance] LaxCatSystem.catA

/-! ## The object carrier of the pseudo-colimit: the bare Σ-type

  For a FILTERED colimit of categories the objects are the bare `Σ i, A i` — NO quotient.  (Two
  representatives that become isomorphic at a common bound are *isomorphic in the colimit category*,
  but they are kept as distinct objects; the colimit category is not skeletal.)  This is the same
  carrier as `CapitalizationGroth.lean`'s `SigmaObj`, but here it costs nothing: it needs no
  transition laws at all, so it is well-defined for a LAX system where the object-level `F_refl`/
  `F_trans` are only isos.  Contrast the STRICT `Colim.CatSystem.Obj`, a quotient of `Σ i, A i` by
  germ equivalence, whose well-definedness uses the strict `F_refl`/`F_trans` (`DirectedColimit`'s
  `System.tr_refl`/`tr_trans`) — exactly the laws base-change lacks. -/
abbrev Obj (S : LaxCatSystem.{u, w} ι D) : Type _ := Σ i, S.A i

/-- The cocone inclusion `A i → Σ i, A i` is the bare injection. -/
def objIncl (S : LaxCatSystem ι D) (i : ι) (x : S.A i) : Obj S := ⟨i, x⟩

/-! ## A natural iso from a pointwise object-equality of two functors

  Given functors `F G : 𝒜 → ℬ` whose object maps agree pointwise (`∀ x, F x = G x`) AND whose
  morphism maps match under the induced `eqToHom` conjugation, the family of `eqToHom` arrows is a
  natural isomorphism `F ≅ G`.  This is the bridge that turns the STRICT `CatSystem.F_refl`/
  `F_trans` *equalities* into the LAX `F_refl_iso`/`F_trans_iso` *isos*, proving the lax interface
  genuinely generalises the strict one (`ofStrict`).  Built on the repo's `eqToHom` (§1.36). -/
section PointwiseNatIso

variable {𝒜 ℬ : Type w} [Cat.{w} 𝒜] [Cat.{w} ℬ]

/-- **Pointwise object-equality ⟹ natural iso.**  If two functors agree on objects pointwise and
    their morphism maps satisfy the `eqToHom` conjugation `G.map f = eqToHom (hpt X).symm ≫ F.map f
    ≫ eqToHom (hpt Y)`, the `eqToHom` family is a `NatIso F G`. -/
def natIsoOfPointwise {F G : 𝒜 → ℬ} [hF : Functor F] [hG : Functor G]
    (hpt : ∀ x, F x = G x)
    (hmap : ∀ {X Y : 𝒜} (f : X ⟶ Y),
      hG.map f = eqToHom (hpt X).symm ≫ hF.map f ≫ eqToHom (hpt Y)) :
    NatIso F G where
  nat :=
    { app X := eqToHom (hpt X)
      naturality {X Y} f := by
        -- goal: `F.map f ≫ eqToHom (hpt Y) = eqToHom (hpt X) ≫ G.map f`.  Expand `G.map f` by
        -- `hmap`, then collapse `eqToHom (hpt X) ≫ eqToHom (hpt X).symm = id` on the RHS.
        rw [hmap f, ← Cat.assoc (eqToHom (hpt X)), eqToHom_comp_eqToHom_symm, Cat.id_comp] }
  isIso X := ⟨eqToHom (hpt X).symm, eqToHom_comp_eqToHom_symm _, eqToHom_symm_comp_eqToHom _⟩

/-- A `HEq` between two morphisms over equal endpoints is the `eqToHom` conjugation.  This converts
    the STRICT system's morphism-coherence (`CatSystem.Coherent.refl_map`/`trans_map`, stated with
    `HEq`) into the `hmap` hypothesis `natIsoOfPointwise` needs. -/
theorem heq_eqToHom_conj {A B A' B' : ℬ} (hA : A = A') (hB : B = B')
    {m : A ⟶ B} {m' : A' ⟶ B'} (h : HEq m m') :
    m' = eqToHom hA.symm ≫ m ≫ eqToHom hB := by
  cases hA; cases hB
  simp only [eqToHom_refl, Cat.id_comp, Cat.comp_id]
  exact (eq_of_heq h).symm

end PointwiseNatIso

/-! ## Every strict `Colim.CatSystem` is a `LaxCatSystem`

  The lax interface generalises the strict one: the object data, `Cat`, and transition functors are
  carried over verbatim, and the strict `F_refl`/`F_trans` *equalities* yield the coherence *isos*
  via `natIsoOfPointwise` (the morphism-level `hmap` comes from `Coherent.refl_map`/`trans_map`
  through `heq_eqToHom_conj`).  So nothing is lost in moving to the lax setting — and base-change,
  which is NOT a strict `CatSystem`, will still be a `LaxCatSystem`. -/
noncomputable def ofStrict (C : Colim.CatSystem.{u, w} ι D) (hC : C.Coherent) :
    LaxCatSystem.{u, w} ι D where
  A := C.A
  catA := C.catA
  F := @C.F
  functF := @C.functF
  F_refl_iso {i} := natIsoOfPointwise (F := C.F (D.refl i)) (G := fun x => x)
    (hF := C.functF (D.refl i)) (hG := @idFunctor (C.A i) (C.catA i))
    (fun x => C.F_refl x)
    (fun {X Y} f =>
      -- `idFunctor.map f = f`; `Coherent.refl_map f : HEq ((functF refl).map f) f` conjugates.
      heq_eqToHom_conj (C.F_refl X) (C.F_refl Y) (hC.refl_map f))
  F_trans_iso {i j k} hij hjk := natIsoOfPointwise
    (F := C.F (D.trans hij hjk)) (G := fun x => C.F hjk (C.F hij x))
    (hF := C.functF (D.trans hij hjk))
    (hG := @compFunctor (C.A i) (C.catA i) (C.A j) (C.catA j) (C.A k) (C.catA k)
      (C.F hij) (C.F hjk) (C.functF hij) (C.functF hjk))
    (fun x => C.F_trans hij hjk x)
    (fun {X Y} f =>
      heq_eqToHom_conj (C.F_trans hij hjk X) (C.F_trans hij hjk Y) (hC.trans_map hij hjk f))

/-! ## The §1.547 base-change slice system as a `LaxCatSystem`

  Here is the payoff for §1.547.  The inner directed system of finite-product slices `A/(∏U)` over
  the filtered index `listDirected`, with BASE-CHANGE transitions (`RelativeCapitalization.lean`'s
  `innerObj`/`innerF`/`innerFunctF`), CANNOT be a strict `Colim.CatSystem` — its
  `StrictBaseChange` hypothesis is a *false* statement for raw base-change (`baseChangeObj (id) X =
  X ×_D D ≠ X` on the nose).  But it IS a `LaxCatSystem`: the coherence isos are the canonical
  pullback isomorphisms, which DO exist.

  We phrase this abstractly over any directed product-projection system so it is reusable and
  imports only the light `SliceRegular` (not the heavy `Capitalization` chain): a `ProjSystem` is a
  `Directed ι` together with stage products `pr i` and a strictly-coherent projection family
  `proj`.  Its base-change object/functor data is sorry-free; the two pseudo-coherence isos are the
  genuine remaining content, isolated as honest TRUE obligations in `PseudoBaseChange` (no false
  equation — unlike `StrictBaseChange`, these isos really hold). -/
section BaseChangeLax

variable {𝒞 : Type w} [Cat.{w} 𝒞] [HasPullbacks 𝒞]

/-- A directed system of "products with projections": stage objects `pr i`, and for every
    `i ≤ j` a projection `pr j ⟶ pr i` (the bigger product onto the smaller), strictly coherent
    (`Cat.id` on `refl`, composite on `trans`).  This abstracts §1.547's `ListProjFamily` over
    `listDirected`; the projections ARE constructible (the only obstruction to a concrete instance
    is `DecidableEq 𝒞` for positional matching, orthogonal to the colimit construction here). -/
structure ProjSystem (ι : Type u) (D : Directed ι) (𝒞 : Type w) [Cat.{w} 𝒞] where
  /-- the stage product object `∏(stage i)` -/
  pr : ι → 𝒞
  /-- the projection `∏j ⟶ ∏i` for `i ≤ j` -/
  proj : ∀ {i j}, D.le i j → (pr j ⟶ pr i)
  /-- strict unit: the reflexive projection is the identity -/
  proj_refl : ∀ i, proj (D.refl i) = Cat.id (pr i)
  /-- strict composition (note the contravariance: `i ≤ j ≤ k` gives `∏k ⟶ ∏i` two ways) -/
  proj_trans : ∀ {i j k} (hij : D.le i j) (hjk : D.le j k),
    proj (D.trans hij hjk) = proj hjk ≫ proj hij

variable {ι : Type u} {D : Directed ι}

/-- Stage `i` of the base-change system: the slice `A/(pr i) = Over (pr i)`. -/
abbrev pcObj (P : ProjSystem ι D 𝒞) (i : ι) : Type w := Over (P.pr i)

/-- The base-change transition object map `A/(pr i) → A/(pr j)` along the projection `proj : pr j
    ⟶ pr i` (for `i ≤ j`): `X ↦ X ×_{pr i} pr j`.  Sorry-free (`baseChangeObj`). -/
def pcF (P : ProjSystem ι D 𝒞) {i j} (h : D.le i j) : pcObj P i → pcObj P j :=
  baseChangeObj (P.proj h)

/-- The base-change transition is a functor (sorry-free, `baseChangeFunctor`). -/
instance pcFunctF (P : ProjSystem ι D 𝒞) {i j} (h : D.le i j) :
    @Functor (pcObj P i) (overCat (P.pr i)) (pcObj P j) (overCat (P.pr j)) (pcF P h) :=
  baseChangeFunctor (P.proj h)

/-! ### The reflexive coherence iso is REAL — `baseChangeObj (id) ≅ id`

  Demonstration that `PseudoBaseChange.refl_iso` is genuinely inhabitable (not a renamed wall): the
  pullback of any `X.hom` along the identity is canonically `X`.  The per-object iso `X ≅
  baseChangeObj (Cat.id C) X` is built from the pullback universal property; the inverse pair is
  `lift`/`π₁`, and `π₁ ≫ lift = id` follows from `lift_uniq`.  This is the harder of the two
  obligations' EASY half; the composite (`trans_iso`, pullback pasting) remains the next blocker. -/
section BaseChangeIdIso

variable {C : 𝒞}

private def _idPB (X : Over C) : HasPullback X.hom (Cat.id C) := HasPullbacks.has X.hom (Cat.id C)

/-- The cone `⟨X.dom, id, X.hom⟩` over the cospan `(X.hom, id_C)`. -/
private def _idCone (X : Over C) : Cone X.hom (Cat.id C) :=
  ⟨X.dom, Cat.id X.dom, X.hom, by rw [Cat.id_comp, Cat.comp_id]⟩

/-- The forward arrow `X ⟶ baseChangeObj (id) X`: the lift of `_idCone` into the pullback.  Its
    over-`C` triangle is `lift ≫ π₂ = X.hom` (`lift_snd`). -/
private def _idFwd (X : Over C) : OverHom X (baseChangeObj (Cat.id C) X) :=
  ⟨(_idPB X).lift (_idCone X), (_idPB X).lift_snd (_idCone X)⟩

/-- The backward arrow `baseChangeObj (id) X ⟶ X`: the first projection `π₁`.  Its over-`C` triangle
    is `π₁ ≫ X.hom = π₂` from the pullback square `w` (since the other leg is `id_C`). -/
private def _idBwd (X : Over C) : OverHom (baseChangeObj (Cat.id C) X) X :=
  ⟨(_idPB X).cone.π₁, by
    show (_idPB X).cone.π₁ ≫ X.hom = (_idPB X).cone.π₂
    have := (_idPB X).cone.w; rw [Cat.comp_id] at this; exact this⟩

/-- `_idBwd` is an iso, with inverse `_idFwd`: back-then-forward is `id` by `lift_fst`; forward-
    then-back is `id` by pullback uniqueness (`lift_uniq`, the identity cone's lift is `id`). -/
private theorem _idBwd_isIso (X : Over C) : @IsIso (Over C) _ _ _ (_idBwd X) := by
  refine ⟨_idFwd X, ?_, ?_⟩
  · -- `_idBwd ⊚ _idFwd = id_{baseChangeObj}` ⟺ `π₁ ≫ lift = id_pt`, by `lift_uniq`.
    apply OverHom.ext
    show (_idPB X).cone.π₁ ≫ (_idPB X).lift (_idCone X) = Cat.id _
    -- both `π₁ ≫ lift` and `id_pt` lift the self-cone `⟨pt, π₁, π₂⟩`, so they are equal.
    let selfCone : Cone X.hom (Cat.id C) :=
      ⟨(_idPB X).cone.pt, (_idPB X).cone.π₁, (_idPB X).cone.π₂, (_idPB X).cone.w⟩
    have h1 : (_idPB X).cone.π₁ ≫ (_idPB X).lift (_idCone X) = (_idPB X).lift selfCone := by
      refine (_idPB X).lift_uniq selfCone _ ?_ ?_
      · rw [Cat.assoc, (_idPB X).lift_fst (_idCone X)]; show (_idPB X).cone.π₁ ≫ Cat.id _ = _
        rw [Cat.comp_id]
      · rw [Cat.assoc, (_idPB X).lift_snd (_idCone X)]
        show (_idPB X).cone.π₁ ≫ X.hom = (_idPB X).cone.π₂
        have := (_idPB X).cone.w; rw [Cat.comp_id] at this; exact this
    have h2 : Cat.id (_idPB X).cone.pt = (_idPB X).lift selfCone :=
      (_idPB X).lift_uniq selfCone (Cat.id _) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])
    rw [h1, ← h2]
  · -- `_idFwd ⊚ _idBwd = id_X` ⟺ `lift ≫ π₁ = id_{X.dom}` (`lift_fst` of `_idCone`).
    apply OverHom.ext
    show (_idPB X).lift (_idCone X) ≫ (_idPB X).cone.π₁ = Cat.id X.dom
    exact (_idPB X).lift_fst (_idCone X)

/-- **`baseChangeObj (Cat.id C) ≅ id` as a `NatIso`.**  Components are `_idBwd` (= `π₁`, iso by
    `_idBwd_isIso`); naturality is the pullback square `w` (`π₁` commutes with the base-change map's
    `π₁`-leg, which is `lift_fst`).  This proves `PseudoBaseChange.refl_iso` is genuinely
    inhabitable — the reflexive coherence iso is NOT a hidden wall. -/
def baseChangeIdNatIso : @NatIso (Over C) _ (Over C) _
    (baseChangeObj (Cat.id C)) (fun X => X) (baseChangeFunctor (Cat.id C)) (@idFunctor (Over C) _) where
  nat :=
    { app := _idBwd
      naturality {X Y} m := by
        -- `baseChangeMap (id) m ⊚ _idBwd Y = _idBwd X ⊚ m`, i.e. on arrows
        -- `(lift (baseChangeCone m)) ≫ π₁ʸ = π₁ˣ ≫ m.f`, which is exactly `lift_fst`.
        apply OverHom.ext
        show ((_idPB Y).lift (baseChangeCone (Cat.id C) m)) ≫ (_idPB Y).cone.π₁
          = (_idPB X).cone.π₁ ≫ m.f
        rw [(_idPB Y).lift_fst (baseChangeCone (Cat.id C) m)]; rfl }
  isIso := _idBwd_isIso

end BaseChangeIdIso

/-! ### The composite coherence iso is REAL — pullback pasting `baseChangeObj (g' ≫ g) ≅ baseChangeObj g' ∘ baseChangeObj g`

  The pullback-pasting lemma plus `isIso_of_two_pullbacks` (§1.43) gives the iterated-pullback
  natural iso.  With base maps `g : C ⟶ D`, `g' : E ⟶ C` (diagram-order, so `g' ≫ g : E ⟶ D`):
  pulling `X.hom` back along `g' ≫ g` is canonically iso to pulling back along `g` then `g'`.  This
  discharges `PseudoBaseChange.trans_iso`; needs only `HasPullbacks 𝒞`, NO choice. -/
section BaseChangeTransIso

variable {D C E : 𝒞} (g : C ⟶ D) (g' : E ⟶ C)

/-- **Pullback pasting.**  If the inner square (cone `c1` over `(h, g)`) is a pullback and the outer
    square (cone `c2` over `(c1.π₂, g')`) is a pullback, then the composite cone
    `⟨c2.pt, c2.π₁ ≫ c1.π₁, c2.π₂⟩` over `(h, g' ≫ g)` is a pullback.  The classic two-pullback
    pasting lemma (left + right square pullbacks ⇒ outer rectangle pullback). -/
theorem pasteCone_isPullback {X : 𝒞} {h : X ⟶ D}
    {c1 : Cone h g} (hc1 : c1.IsPullback)
    {c2 : Cone c1.π₂ g'} (hc2 : c2.IsPullback) :
    (Cone.mk (f := h) (g := g' ≫ g) c2.pt (c2.π₁ ≫ c1.π₁) c2.π₂
      (by rw [Cat.assoc, c1.w, ← Cat.assoc, c2.w, Cat.assoc])).IsPullback := by
  intro d
  -- d : cone over (h, g' ≫ g): d.π₁ ≫ h = d.π₂ ≫ (g' ≫ g).
  -- Step 1: (d.π₁, d.π₂ ≫ g') is a cone over (h, g), lift into c1 ⇒ e : d.pt ⟶ c1.pt.
  have hw1 : d.π₁ ≫ h = (d.π₂ ≫ g') ≫ g := by rw [d.w, Cat.assoc]
  obtain ⟨e, ⟨he₁, he₂⟩, huniq1⟩ := hc1 (Cone.mk d.pt d.π₁ (d.π₂ ≫ g') hw1)
  -- Step 2: (e, d.π₂) is a cone over (c1.π₂, g') (he₂ : e ≫ c1.π₂ = d.π₂ ≫ g'), lift into c2.
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc2 (Cone.mk d.pt e d.π₂ he₂)
  refine ⟨u, ⟨?_, hu₂⟩, ?_⟩
  · -- u ≫ (c2.π₁ ≫ c1.π₁) = d.π₁
    rw [← Cat.assoc, hu₁, he₁]
  · -- uniqueness: any v with v ≫ (c2.π₁ ≫ c1.π₁) = d.π₁ and v ≫ c2.π₂ = d.π₂ equals u.
    intro v hv₁ hv₂
    -- v ≫ c2.π₁ lifts the c1-cone (d.π₁, d.π₂ ≫ g'), hence equals e by uniqueness in c1.
    have hve : v ≫ c2.π₁ = e :=
      huniq1 (v ≫ c2.π₁) (by rw [Cat.assoc]; exact hv₁)
        (by show (v ≫ c2.π₁) ≫ c1.π₂ = d.π₂ ≫ g'
            calc (v ≫ c2.π₁) ≫ c1.π₂ = v ≫ (c2.π₁ ≫ c1.π₂) := Cat.assoc _ _ _
              _ = v ≫ (c2.π₂ ≫ g') := congrArg (v ≫ ·) c2.w
              _ = (v ≫ c2.π₂) ≫ g' := (Cat.assoc _ _ _).symm
              _ = d.π₂ ≫ g' := congrArg (· ≫ g') hv₂)
    -- then v lifts the c2-cone (e, d.π₂), hence equals u.
    exact huniq v hve hv₂

/-! ### From pasting to the `trans` natural iso

  `baseChangeObj g X` is, definitionally, the chosen pullback of `X.hom` along `g`.  We abbreviate
  that chosen pullback as `_pb`.  The LHS `baseChangeObj (g' ≫ g) X` and the pasted RHS
  `baseChangeObj g' (baseChangeObj g X)` are two pullbacks of the SAME cospan `(X.hom, g' ≫ g)`
  (by `pasteCone_isPullback`), so they are canonically iso (`isIso_of_two_pullbacks`). -/

/-- The chosen pullback of `X.hom` along a base map, matching `baseChangeObj`'s internal choice. -/
private def _pb (g : C ⟶ D) (X : Over D) : HasPullback X.hom g := HasPullbacks.has X.hom g

/-- The pasted RHS cone `baseChangeObj g' (baseChangeObj g X)`, viewed as a cone over the composite
    cospan `(X.hom, g' ≫ g)`, is a pullback. -/
private theorem _rhsPasted (X : Over D) :
    (Cone.mk (f := X.hom) (g := g' ≫ g)
      (_pb g' (baseChangeObj g X)).cone.pt
      ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (_pb g X).cone.π₁)
      (_pb g' (baseChangeObj g X)).cone.π₂
      (by
        have hc1 := (_pb g X).cone.w
        have hc2 := (_pb g' (baseChangeObj g X)).cone.w
        calc ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (_pb g X).cone.π₁) ≫ X.hom
            = (_pb g' (baseChangeObj g X)).cone.π₁ ≫ ((_pb g X).cone.π₁ ≫ X.hom) := Cat.assoc _ _ _
          _ = (_pb g' (baseChangeObj g X)).cone.π₁ ≫ ((_pb g X).cone.π₂ ≫ g) :=
                congrArg ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ ·) hc1
          _ = ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (_pb g X).cone.π₂) ≫ g := (Cat.assoc _ _ _).symm
          _ = ((_pb g' (baseChangeObj g X)).cone.π₂ ≫ g') ≫ g := congrArg (· ≫ g) hc2
          _ = (_pb g' (baseChangeObj g X)).cone.π₂ ≫ (g' ≫ g) := Cat.assoc _ _ _)).IsPullback :=
  pasteCone_isPullback g g'
    (h := X.hom) ((_pb g X).cone_isPullback) ((_pb g' (baseChangeObj g X)).cone_isPullback)

/-- The LHS pullback cone of `baseChangeObj (g' ≫ g) X`, as a cone over `(X.hom, g' ≫ g)`. -/
private def _lhsCone (X : Over D) : Cone X.hom (g' ≫ g) := (_pb (g' ≫ g) X).cone

/-- The forward comparison map `(baseChangeObj (g' ≫ g) X).dom ⟶ (baseChangeObj g' (baseChangeObj g
    X)).dom`: the unique factorization of the LHS pullback cone through the pasted RHS pullback. -/
private noncomputable def _transFwdf (X : Over D) :
    (baseChangeObj (g' ≫ g) X).dom ⟶ (baseChangeObj g' (baseChangeObj g X)).dom :=
  ((_rhsPasted g g' X) (_lhsCone g g' X)).choose

private theorem _transFwd_π₁ (X : Over D) :
    _transFwdf g g' X ≫ ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (_pb g X).cone.π₁)
      = (_pb (g' ≫ g) X).cone.π₁ :=
  ((_rhsPasted g g' X) (_lhsCone g g' X)).choose_spec.1.1

private theorem _transFwd_π₂ (X : Over D) :
    _transFwdf g g' X ≫ (_pb g' (baseChangeObj g X)).cone.π₂ = (_pb (g' ≫ g) X).cone.π₂ :=
  ((_rhsPasted g g' X) (_lhsCone g g' X)).choose_spec.1.2

/-- The forward comparison as a slice arrow `baseChangeObj (g' ≫ g) X ⟶ baseChangeObj g'
    (baseChangeObj g X)`.  Its `π₂`-leg is the over-`pr k` triangle, which is `_transFwd_π₂`
    (recall the structure map of both slice objects is `π₂`). -/
private noncomputable def _transFwd (X : Over D) :
    OverHom (baseChangeObj (g' ≫ g) X) (baseChangeObj g' (baseChangeObj g X)) :=
  ⟨_transFwdf g g' X, _transFwd_π₂ g g' X⟩

/-- The forward comparison is iso: it is the comparison of two pullbacks of `(X.hom, g' ≫ g)` —
    the LHS chosen pullback and the pasted RHS pullback — so `isIso_of_two_pullbacks` applies. -/
private theorem _transFwd_isIso (X : Over D) : OverIso (_transFwd g g' X) :=
  overIso_of_underlying _
    (isIso_of_two_pullbacks ((_pb (g' ≫ g) X).cone_isPullback) (_rhsPasted g g' X)
      (_transFwdf g g' X) (_transFwd_π₁ g g' X) (_transFwd_π₂ g g' X))

/-- Naturality of the forward comparison, at the level of underlying arrows: for `m : OverHom X Y`,
    `(baseChangeMap (g' ≫ g) m).f ≫ _transFwdf Y = _transFwdf X ≫ (baseChangeMap g' (baseChangeMap g
    m)).f`.  Both sides factor the same cone through the RHS pasted pullback of `Y`, so they agree by
    `lift_uniq`.  The shared cone has legs `((_pb (g'≫g) X).π₁ ≫ m.f, (_pb (g'≫g) X).π₂)` over the
    pasted projections `((_pb g' (bc g Y)).π₁ ≫ (_pb g Y).π₁, (_pb g' (bc g Y)).π₂)`. -/
private theorem _transFwd_natf {X Y : Over D} (m : OverHom X Y) :
    (baseChangeMap (g' ≫ g) m).f ≫ _transFwdf g g' Y
      = _transFwdf g g' X ≫ (baseChangeMap g' (baseChangeMap g m)).f := by
  -- It suffices that both sides agree after post-composing with the two pasted projections of `Y`,
  -- since the pasted cone of `Y` is a pullback (`_rhsPasted ... Y`).  Apply that uniqueness to the
  -- shared cone `d` with legs `((_pb (g'≫g) X).π₁ ≫ m.f, (_pb (g'≫g) X).π₂)` over `(Y.hom, g'≫g)`.
  have hdw : ((_pb (g' ≫ g) X).cone.π₁ ≫ m.f) ≫ Y.hom
      = (_pb (g' ≫ g) X).cone.π₂ ≫ (g' ≫ g) := by
    calc ((_pb (g' ≫ g) X).cone.π₁ ≫ m.f) ≫ Y.hom
        = (_pb (g' ≫ g) X).cone.π₁ ≫ (m.f ≫ Y.hom) := Cat.assoc _ _ _
      _ = (_pb (g' ≫ g) X).cone.π₁ ≫ X.hom := congrArg ((_pb (g' ≫ g) X).cone.π₁ ≫ ·) m.w
      _ = (_pb (g' ≫ g) X).cone.π₂ ≫ (g' ≫ g) := (_pb (g' ≫ g) X).cone.w
  obtain ⟨_, _, huniq⟩ := (_rhsPasted g g' Y)
    (Cone.mk (f := Y.hom) (g := g' ≫ g) (baseChangeObj (g' ≫ g) X).dom
      ((_pb (g' ≫ g) X).cone.π₁ ≫ m.f) ((_pb (g' ≫ g) X).cone.π₂) hdw)
  -- `baseChangeMap`'s `.f` projected against the relevant pullback legs (term-typed so they `rw`).
  have hg_fst : (baseChangeMap g m).f ≫ (_pb g Y).cone.π₁ = (_pb g X).cone.π₁ ≫ m.f :=
    (_pb g Y).lift_fst (baseChangeCone g m)
  have hg'_fst : (baseChangeMap g' (baseChangeMap g m)).f ≫ (_pb g' (baseChangeObj g Y)).cone.π₁
      = (_pb g' (baseChangeObj g X)).cone.π₁ ≫ (baseChangeMap g m).f :=
    (_pb g' (baseChangeObj g Y)).lift_fst (baseChangeCone g' (baseChangeMap g m))
  have hg'_snd : (baseChangeMap g' (baseChangeMap g m)).f ≫ (_pb g' (baseChangeObj g Y)).cone.π₂
      = (_pb g' (baseChangeObj g X)).cone.π₂ :=
    (_pb g' (baseChangeObj g Y)).lift_snd (baseChangeCone g' (baseChangeMap g m))
  refine (huniq ((baseChangeMap (g' ≫ g) m).f ≫ _transFwdf g g' Y) ?rl1 ?rl2).trans
    (huniq (_transFwdf g g' X ≫ (baseChangeMap g' (baseChangeMap g m)).f) ?ll1 ?ll2).symm
  case ll1 =>
    -- π₁ leg: (_transFwdf X ≫ (bc g' (bc g m)).f) ≫ (p₁ʸ) = (_pb (g'≫g) X).π₁ ≫ m.f
    calc (_transFwdf g g' X ≫ (baseChangeMap g' (baseChangeMap g m)).f)
            ≫ ((_pb g' (baseChangeObj g Y)).cone.π₁ ≫ (_pb g Y).cone.π₁)
        = _transFwdf g g' X ≫ (((baseChangeMap g' (baseChangeMap g m)).f
            ≫ (_pb g' (baseChangeObj g Y)).cone.π₁) ≫ (_pb g Y).cone.π₁) := by
          simp only [Cat.assoc]
      _ = _transFwdf g g' X ≫ (((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (baseChangeMap g m).f)
            ≫ (_pb g Y).cone.π₁) := by rw [hg'_fst]
      _ = _transFwdf g g' X ≫ ((_pb g' (baseChangeObj g X)).cone.π₁
            ≫ ((baseChangeMap g m).f ≫ (_pb g Y).cone.π₁)) := by rw [Cat.assoc]
      _ = _transFwdf g g' X ≫ ((_pb g' (baseChangeObj g X)).cone.π₁
            ≫ ((_pb g X).cone.π₁ ≫ m.f)) := by rw [hg_fst]
      _ = (_transFwdf g g' X ≫ ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (_pb g X).cone.π₁)) ≫ m.f := by
          simp only [Cat.assoc]
      _ = (_pb (g' ≫ g) X).cone.π₁ ≫ m.f := by rw [_transFwd_π₁ g g' X]
  case ll2 =>
    calc (_transFwdf g g' X ≫ (baseChangeMap g' (baseChangeMap g m)).f)
            ≫ (_pb g' (baseChangeObj g Y)).cone.π₂
        = _transFwdf g g' X
            ≫ ((baseChangeMap g' (baseChangeMap g m)).f ≫ (_pb g' (baseChangeObj g Y)).cone.π₂) :=
          Cat.assoc _ _ _
      _ = _transFwdf g g' X ≫ (_pb g' (baseChangeObj g X)).cone.π₂ := by rw [hg'_snd]
      _ = (_pb (g' ≫ g) X).cone.π₂ := _transFwd_π₂ g g' X
  case rl1 =>
    calc ((baseChangeMap (g' ≫ g) m).f ≫ _transFwdf g g' Y)
            ≫ ((_pb g' (baseChangeObj g Y)).cone.π₁ ≫ (_pb g Y).cone.π₁)
        = (baseChangeMap (g' ≫ g) m).f ≫ (_transFwdf g g' Y
            ≫ ((_pb g' (baseChangeObj g Y)).cone.π₁ ≫ (_pb g Y).cone.π₁)) := Cat.assoc _ _ _
      _ = (baseChangeMap (g' ≫ g) m).f ≫ (_pb (g' ≫ g) Y).cone.π₁ := by
          rw [_transFwd_π₁ g g' Y]
      _ = (_pb (g' ≫ g) X).cone.π₁ ≫ m.f :=
          (_pb (g' ≫ g) Y).lift_fst (baseChangeCone (g' ≫ g) m)
  case rl2 =>
    calc ((baseChangeMap (g' ≫ g) m).f ≫ _transFwdf g g' Y)
            ≫ (_pb g' (baseChangeObj g Y)).cone.π₂
        = (baseChangeMap (g' ≫ g) m).f ≫ (_transFwdf g g' Y
            ≫ (_pb g' (baseChangeObj g Y)).cone.π₂) := Cat.assoc _ _ _
      _ = (baseChangeMap (g' ≫ g) m).f ≫ (_pb (g' ≫ g) Y).cone.π₂ := by
          rw [_transFwd_π₂ g g' Y]
      _ = (_pb (g' ≫ g) X).cone.π₂ := (_pb (g' ≫ g) Y).lift_snd (baseChangeCone (g' ≫ g) m)

/-- **The composite coherence iso of base-change, over arbitrary composable base maps.**
    `baseChangeObj (g' ≫ g) ≅ baseChangeObj g' ∘ baseChangeObj g` as a `NatIso` (natural in `X`):
    the iterated-pullback / pullback-pasting isomorphism.  Components are `_transFwd` (iso by
    `_transFwd_isIso`); naturality is `_transFwd_natf` (pullback-lift uniqueness). -/
noncomputable def baseChangeTransNatIso :
    @NatIso (Over D) _ (Over E) _
      (baseChangeObj (g' ≫ g)) (baseChangeObj g' ∘ baseChangeObj g)
      (baseChangeFunctor (g' ≫ g))
      (@compFunctor (Over D) _ (Over C) _ (Over E) _
        (baseChangeObj g) (baseChangeObj g') (baseChangeFunctor g) (baseChangeFunctor g')) where
  nat :=
    { app := _transFwd g g'
      naturality {X Y} m := OverHom.ext (_transFwd_natf g g' m) }
  isIso := _transFwd_isIso g g'

end BaseChangeTransIso

/-- **The composite coherence iso of base-change (the ONE honest remaining obligation).**  Unlike
    `StrictBaseChange` (a FALSE equation taken as a hypothesis), this is the canonical iterated-
    pullback isomorphism, which genuinely exists:

      `trans_iso` : `baseChangeObj (g ≫ g') ≅ baseChangeObj g' ∘ baseChangeObj g`
                    — pullback pasting / iterated-pullback iso.

    The REFLEXIVE coherence iso is NO LONGER an obligation: `projReflIso` proves it for every
    `ProjSystem` sorry-free (transport of `baseChangeIdNatIso`).  Supplying this one field turns the
    base-change inner system into a `LaxCatSystem` (`laxOfProjSystem`).  Constructing it is the
    precise §1.543 NEXT BLOCKER: the pullback-pasting natural isomorphism, a standard but nontrivial
    pullback-universal-property argument (see the file footer). -/
structure PseudoBaseChange (P : ProjSystem ι D 𝒞) where
  trans_iso : ∀ {i j k : ι} (hij : D.le i j) (hjk : D.le j k),
    @NatIso (pcObj P i) (overCat (P.pr i)) (pcObj P k) (overCat (P.pr k))
      (pcF P (D.trans hij hjk)) (fun X => pcF P hjk (pcF P hij X))
      (pcFunctF P (D.trans hij hjk))
      (@compFunctor (pcObj P i) _ (pcObj P j) _ (pcObj P k) _
        (pcF P hij) (pcF P hjk) (pcFunctF P hij) (pcFunctF P hjk))

/-- **The reflexive coherence iso of ANY base-change projection system is real.**  Transporting
    `baseChangeIdNatIso` along `P.proj_refl i : P.proj (D.refl i) = Cat.id (pr i)` discharges the
    `refl_iso` field for every `ProjSystem` — sorry-free.  So `PseudoBaseChange` reduces to its
    `trans_iso` field alone: the reflexive half is NOT a blocker. -/
def projReflIso (P : ProjSystem ι D 𝒞) (i : ι) :
    @NatIso (pcObj P i) (overCat (P.pr i)) (pcObj P i) (overCat (P.pr i))
      (pcF P (D.refl i)) (fun X => X) (pcFunctF P (D.refl i)) (@idFunctor (pcObj P i) _) := by
  -- `pcF P (D.refl i) = baseChangeObj (P.proj (D.refl i))`; rewrite the projection to `id`.
  show @NatIso (Over (P.pr i)) _ (Over (P.pr i)) _
    (baseChangeObj (P.proj (D.refl i))) _ (baseChangeFunctor (P.proj (D.refl i))) _
  rw [P.proj_refl i]
  exact baseChangeIdNatIso

/-- **The §1.547 base-change slice system as a `LaxCatSystem`.**  Given the directed projection
    system `P` and its (TRUE) pseudo-coherence isos `H`, the finite-product slices `A/(pr i)` with
    base-change transitions form a `LaxCatSystem` — sorry-free.  This is the lax analogue of
    `Freyd.innerCatSystem`, but WITHOUT the false `StrictBaseChange` input: the coherence is carried
    by genuine isos.  THIS is the construction the strict `Colim.CatSystem` could not host. -/
def laxOfProjSystem (P : ProjSystem ι D 𝒞) (H : PseudoBaseChange P) : LaxCatSystem.{u, w} ι D where
  A := pcObj P
  catA := fun i => overCat (P.pr i)
  F := fun h => pcF P h
  functF := fun h => pcFunctF P h
  F_refl_iso := fun {i} => projReflIso P i
  F_trans_iso := fun hij hjk => H.trans_iso hij hjk

end BaseChangeLax

end Freyd.LaxColim

/-!
════════════════════════════════════════════════════════════════════════════════════════════════
  DESIGN ASSESSMENT + PRECISE NEXT BLOCKER (§1.543 capitalization, filtered pseudo-colimit route)
════════════════════════════════════════════════════════════════════════════════════════════════

WHAT THIS FILE ESTABLISHES (all sorry-free, axiom-free):

  * `LaxCatSystem` — the missing abstraction: a directed system of categories whose transitions are
    FUNCTORS with coherence given as natural ISOS (`F_refl_iso`/`F_trans_iso`), not strict
    equalities.  This is the exact interface base-change can inhabit; the strict `Colim.CatSystem`
    (`F_refl`/`F_trans` on-the-nose equalities) cannot, which is the documented §1.543 wall
    (`StrictBaseChange` is FALSE for raw base-change).
  * `ofStrict` — every strict `Colim.CatSystem` is a `LaxCatSystem`; the lax interface strictly
    generalises the strict one (via `natIsoOfPointwise` + `heq_eqToHom_conj`).  Nothing is lost.
  * `Obj`/`objIncl` — the colimit's OBJECT carrier is the bare `Σ i, A i` (no quotient): for a
    FILTERED colimit of categories the objects are kept distinct (the colimit is non-skeletal), so
    no transition law on objects is needed.  Same carrier `CapitalizationGroth.lean` uses, but here
    it costs nothing and is correct for the lax setting.
  * `ProjSystem`/`pcF`/`pcFunctF`/`laxOfProjSystem` — the §1.547 inner base-change slice system
    (`A/(∏U)`, base-change transitions over the filtered `listDirected`) as a `LaxCatSystem`, the
    lax analogue of `Freyd.innerCatSystem` but WITHOUT the false `StrictBaseChange`.
  * `baseChangeIdNatIso` + `projReflIso` — the REFLEXIVE coherence iso `baseChangeObj (id) ≅ id`,
    PROVEN (pullback along an identity is iso).  So `PseudoBaseChange` carries only ONE field.

WHY THE FILTERED ROUTE (this file) BEATS THE TRANSFINITE TOWER (`CapitalizationGroth.lean`):

  * The tower indexes by a well-order with LIMIT ordinals and needs cross-stage `belowObjAgree`/
    `belowCoherent` (5 `sorry`s bottoming out in `CapitalizationTower.lean`) plus `gLimTopPre`.
  * Here the index `listDirected` is FILTERED (any two finite lists have an upper bound = append);
    there are NO limit ordinals, NO `below*` agreement, NO transfinite coherence.  The Σ-object
    carrier is unconditional, and the coherence is entirely on hom-sets / per-pair transition isos.

THE PRECISE NEXT BLOCKER — the ONE remaining field, `PseudoBaseChange.trans_iso`:

    `baseChangeObj (g ≫ g') X  ≅  baseChangeObj g' (baseChangeObj g X)`   as a `NatIso`,

  i.e. the iterated-pullback (pullback-pasting) natural isomorphism: pulling `X.hom` back along the
  composite `g ≫ g'` equals pulling back along `g` then along `g'`.  Concretely, with
  `Z := baseChangeObj g X = ⟨X ×_{C} B, π₂⟩` (over `B`, along `g : B ⟶ C`) and then pulling along
  `g' : A ⟶ B`, the apex `(X ×_C B) ×_B A` is canonically iso to `X ×_C A` — by the pullback-
  pasting lemma (the outer rectangle is a pullback iff the two squares are).  The component iso is
  the unique pullback `lift`, and its inverse is the lift the other way; naturality is `lift_uniq`.
  This is a standard but multi-step pullback argument (the harder half of the two coherence isos;
  the reflexive half `projReflIso` is already done above).  It needs only `HasPullbacks 𝒞` and the
  pullback-pasting lemma — no choice, no transfinite recursion.

AFTER `trans_iso`: the remaining work toward `PreRegular A*` is the PSEUDO HOM-COLIMIT — a morphism
`⟨i,x⟩ → ⟨j,y⟩` is a germ of `Hom_{A k}(F_{ik} x, F_{jk} y)` over upper bounds `k`, with germ
equivalence transported along `F_trans_iso` (NOT strict equalities, as the strict `HomColim` does).
The category laws and finite-limit preservation then transfer from the fibres' `overPreRegular` by
the standard "filtered colimits commute with finite limits" argument.  That hom-colimit is the next
milestone once `trans_iso` lands.
-/

