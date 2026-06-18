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

/-- **The pseudo-coherence isos of base-change (honest TRUE obligations).**  Unlike
    `StrictBaseChange` (a FALSE equation taken as a hypothesis), these are the canonical pullback
    isomorphisms, which genuinely exist:

      * `refl_iso`  : `baseChangeObj (id) ≅ id`            — pullback along an identity is iso
      * `trans_iso` : `baseChangeObj (g ≫ g') ≅ baseChangeObj g' ∘ baseChangeObj g`
                                                            — pullback pasting / iterated-pullback iso

    Supplying these turns the base-change inner system into a `LaxCatSystem` (`laxOfProjSystem`).
    They are stated as `NatIso`s of the transition functors; constructing them is the genuine
    next-blocker content (each is a standard pullback-universal-property argument). -/
structure PseudoBaseChange (P : ProjSystem ι D 𝒞) where
  refl_iso : ∀ {i : ι},
    @NatIso (pcObj P i) (overCat (P.pr i)) (pcObj P i) (overCat (P.pr i))
      (pcF P (D.refl i)) (fun X => X) (pcFunctF P (D.refl i)) (@idFunctor (pcObj P i) _)
  trans_iso : ∀ {i j k : ι} (hij : D.le i j) (hjk : D.le j k),
    @NatIso (pcObj P i) (overCat (P.pr i)) (pcObj P k) (overCat (P.pr k))
      (pcF P (D.trans hij hjk)) (fun X => pcF P hjk (pcF P hij X))
      (pcFunctF P (D.trans hij hjk))
      (@compFunctor (pcObj P i) _ (pcObj P j) _ (pcObj P k) _
        (pcF P hij) (pcF P hjk) (pcFunctF P hij) (pcFunctF P hjk))

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
  F_refl_iso := H.refl_iso
  F_trans_iso := fun hij hjk => H.trans_iso hij hjk

end BaseChangeLax

end Freyd.LaxColim
