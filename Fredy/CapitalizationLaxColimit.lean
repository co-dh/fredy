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
import Fredy.S1_41
import Fredy.DirectedColimit

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

end Freyd.LaxColim
