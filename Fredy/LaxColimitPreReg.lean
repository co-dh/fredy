/-
  §1.543 — PRE-REGULARITY of the FILTERED lax colimit `ratCapCat P` (the §1.547 relative
  capitalization `A*`).

  ════════════════════════════════════════════════════════════════════════════════════════════
  GOAL.  `CapitalizationLaxColimit.lean` builds, sorry-free, the §1.547 relative capitalization
  `A* = ratCapCat P : Cat (Obj (laxOfProjSystem' P))` — the FILTERED lax colimit of the slices
  `A/(∏U) = Over (listProd U)` over the filtered index of finite ws-lists, with BASE-CHANGE
  transitions (a pseudofunctor, coherence supplied as natural isos `F_refl_iso`/`F_trans_iso`,
  never strict equalities).  Each fibre `Over (listProd U)` is `PreRegularCategory`
  (`overPreRegular`, `SliceRegular.lean`).

  This file transfers PRE-REGULARITY to the colimit:  `PreRegularCategory (ratCapCat P)`.  The
  principle is "FILTERED colimits commute with FINITE limits": a finite diagram in the colimit,
  pushed along transitions to a COMMON upper stage (filtered: any finite index set has a bound),
  lives in a single fibre, where the fibre's finite limit is computed and then included.

  It MIRRORS the STRICT analogue `Colim.colimitPreRegular` (`CatColimitRegular.lean:2450`), which
  proves exactly this for the STRICT colimit, replacing strict `castHom`/object-equalities with the
  lax `pushHom`/coherence-isos.  The crucial SIMPLIFICATION over the strict file: the lax colimit's
  objects are the bare `Σ i, A i` (`Obj L`), so every object is LITERALLY `objIncl i x = ⟨i,x⟩` —
  there is NO `colimOut`/`Quotient.out` representative-section to fight (the strict file's pervasive
  `colimOut`/`colimOut_spec` machinery simply vanishes).

  ADAPTATION PLAN from `colimitPreRegular` (the strict assembly takes per-fibre limit existence
  PLUS the transitions' finite-limit PRESERVATION; the lax version takes the same):

    * `HasTerminal`  — strict `colimitHasTerminal` needs `ht i` + `hpres : F hij one = one`
      (strict).  Lax: the pushed terminal `F hij (ht i).one` is again TERMINAL (true for
      base-change: `g* ⟨pr i, id⟩ ≅ ⟨pr j, id⟩`); state that as the preservation hypothesis and the
      whole proof goes through with `homInclL`/`pushHom` in place of `homIncl`/`castHom`.  DONE here.
    * `HasBinaryProducts`/`HasEqualizers`/`HasPullbacks` — push the two/one objects to a common
      stage, take the fibre limit, include; universal property via the germ colimit + the fibres'
      limit-preservation across transitions.  (Mirrors `colimitHasBinaryProducts`/`…Equalizers`/
      `…Pullbacks`.)  NEXT.
    * `PullbacksTransferCovers` — a colimit cover + pullback align to a common fibre where the
      fibre's PTC applies; transfer back (mirrors `colimitPullbacksTransferCovers`).
    * assemble `PreRegularCategory (ratCapCat P)` (mirrors `colimitPreRegular`).

  Mathlib-free; built on the repo's own `Cat` + `Freyd.LaxColim` (`CapitalizationLaxColimit.lean`).
-/
import Fredy.CapitalizationLaxColimit

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}

/-! ## §M3a (lax) — the terminal object of the lax colimit category

  Mirrors `Colim.colimitHasTerminal`.  Pick any stage `i₀` (filtered ⇒ nonempty needed) and let the
  colimit terminal be `objIncl i₀ (ht i₀).one`.  Unlike the strict version there is NO `colimOut`:
  the terminal IS literally `⟨i₀, (ht i₀).one⟩`.

  The preservation hypothesis is the LAX analogue of the strict `hpres : F hij one = one`.  In the
  lax world `F hij (ht i).one` is only ISO to `(ht j).one`, so the strict equation is false; instead
  we ask that the pushed terminal is again a TERMINAL OBJECT (its own `HasTerminal`-witness in
  `L.A j`).  This is exactly what base-change supplies (`g*` of the slice terminal is the slice
  terminal up to iso, and an isomorph of a terminal is terminal), and it is all the proof needs. -/
section LaxTerminal

variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L)

/-- LAX terminal-preservation: each fibre has a terminal `ht i`, and the pushed terminal
    `L.F hij (ht i).one` is again terminal in the target fibre `L.A j` (an isomorph of `(ht j).one`).
    For base-change this holds: `g*` carries the slice terminal `⟨pr i, id⟩` to `⟨pr j, id⟩` up to
    iso, and any isomorph of a terminal is terminal. -/
structure LaxTerminalData where
  /-- each fibre has a terminal -/
  ht : ∀ i, HasTerminal (L.A i)
  /-- the unique map of any object to the pushed terminal -/
  pushTrm : ∀ {i j} (hij : D.le i j) (X : L.A j), X ⟶ L.F hij (ht i).one
  /-- pushed terminal is terminal: maps into it are unique -/
  pushUniq : ∀ {i j} (hij : D.le i j) {X : L.A j}
    (f g : X ⟶ L.F hij (ht i).one), f = g

/-- **§M3a (lax): the lax colimit category has a terminal.**  The terminal is `objIncl i₀ one` for a
    chosen stage `i₀`.  The unique map from `⟨jX, xX⟩` pushes both to a common bound `k`, mapping
    `xX` to the pushed terminal via `pushTrm`; uniqueness is `pushUniq` after pushing two germ
    representatives to a common bound (and absorbing the level shift by `pushHom`/germ equivalence). -/
noncomputable def laxColimHasTerminal [hne : Nonempty ι] (T : LaxTerminalData L) :
    @HasTerminal (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  let i₀ : ι := Classical.choice hne
  let one : Obj L := objIncl L i₀ (T.ht i₀).one
  refine @HasTerminal.mk (Obj L) (laxColimCat L hL) one ?_ ?_
  · -- trm: a morphism `⟨jX, xX⟩ ⟶ one` for every object `X`.
    intro X
    obtain ⟨jX, xX⟩ := X
    -- common bound `k` of `jX` and `i₀` (chosen by `D.bound`; `trm` returns a `Type`, so `choose`).
    let bd := D.bound jX i₀
    let k := Classical.choose bd
    have hk : D.le jX k ∧ D.le i₀ k := Classical.choose_spec bd
    -- the germ of `pushTrm : F (jX≤k) xX ⟶ F (i₀≤k) one` at the upper bound `⟨k, hk.1, hk.2⟩`.
    exact homInclL L hL xX (T.ht i₀).one ⟨k, hk.1, hk.2⟩ (T.pushTrm hk.2 (L.F hk.1 xX))
  · -- uniq: any two germs `⟨jX,xX⟩ ⟶ one` are equal.
    intro X f g
    obtain ⟨jX, xX⟩ := X
    refine Quotient.inductionOn f (fun ⟨a, fa⟩ => ?_)
    refine Quotient.inductionOn g (fun ⟨b, gb⟩ => ?_)
    -- push both representatives to a common bound `k'` of `a.1`, `b.1`; there the targets are the
    -- pushed terminal `F (trans a.2.2 …) one`, so `pushUniq` equates them.
    apply Quotient.sound
    obtain ⟨k', hak', hbk'⟩ := D.bound a.1 b.1
    -- witness the germ relation at the upper bound `⟨k', …⟩` of `⟨jX, xX⟩, ⟨i₀, one⟩`.
    refine ⟨⟨k', D.trans a.2.1 hak', D.trans a.2.2 hak'⟩, hak', hbk', ?_⟩
    -- both `pushHom … fa` and `pushHom … gb` are arrows into the pushed terminal
    -- `F (D.trans a.2.2 hak') one = F (D.trans b.2.2 hbk') one` (proof-irrelevant `D.le i₀ k'`).
    exact T.pushUniq (D.trans a.2.2 hak') _ _

end LaxTerminal

/-! ## The reflexive coherence component `reflApp` (lax analogue of `transApp`)

  `transApp` (in `CapitalizationLaxColimit.lean`) extracts the forward component of `F_trans_iso`.
  Its UNIT counterpart `reflApp` extracts the forward component of `F_refl_iso`: at an object `x` of
  `L.A i` it is the canonical iso `L.F (D.refl i) x ⟶ x` (base-change of the identity onto `x`).
  This is the conjugator that turns a STAGE morphism `f : x ⟶ y` in `L.A i` into a single-stage germ
  representative `reflApp x ≫ f ≫ inv (reflApp y) : L.F (refl i) x ⟶ L.F (refl i) y`, the building
  block of the stage-inclusion functor and of every finite-limit cone in the colimit. -/
section ReflApp

variable (L : LaxCatSystem.{u, w} ι D)

/-- The forward component of the reflexive coherence iso `F_refl_iso` at an object `x : L.A i`:
    the canonical iso `L.F (D.refl i) x ⟶ x`. -/
def reflApp {i : ι} (x : L.A i) : L.F (D.refl i) x ⟶ x :=
  @NaturalTransformation.app (L.A i) (L.catA i) (L.A i) (L.catA i)
    (L.F (D.refl i)) (fun z => z) (L.functF (D.refl i)) (@idFunctor (L.A i) (L.catA i))
    (@NatIso.nat (L.A i) (L.catA i) (L.A i) (L.catA i)
      (L.F (D.refl i)) (fun z => z) (L.functF (D.refl i)) (@idFunctor (L.A i) (L.catA i))
      L.F_refl_iso) x

/-- `reflApp` is an isomorphism (it is a component of the natural iso `F_refl_iso`). -/
theorem reflApp_isIso {i : ι} (x : L.A i) : IsIso (reflApp L x) :=
  @NatIso.isIso (L.A i) (L.catA i) (L.A i) (L.catA i)
    (L.F (D.refl i)) (fun z => z) (L.functF (D.refl i)) (@idFunctor (L.A i) (L.catA i))
    L.F_refl_iso x

/-- **Naturality of `reflApp`.**  `reflApp` is the component of the natural iso `F_refl_iso`, so for
    any `f : x ⟶ y` in `L.A i` it intertwines the reflexive transition `F (refl i)` with the
    identity functor: `(F (refl i)).map f ≫ reflApp y = reflApp x ≫ f`. -/
theorem reflApp_natural {i : ι} {x y : L.A i} (f : x ⟶ y) :
    @Functor.map (L.A i) (L.catA i) (L.A i) (L.catA i) (L.F (D.refl i)) (L.functF (D.refl i)) x y f
        ≫ reflApp L y
      = reflApp L x ≫ f :=
  @NaturalTransformation.naturality (L.A i) (L.catA i) (L.A i) (L.catA i)
    (L.F (D.refl i)) (fun z => z) (L.functF (D.refl i)) (@idFunctor (L.A i) (L.catA i))
    (@NatIso.nat (L.A i) (L.catA i) (L.A i) (L.catA i)
      (L.F (D.refl i)) (fun z => z) (L.functF (D.refl i)) (@idFunctor (L.A i) (L.catA i))
      L.F_refl_iso) x y f

end ReflApp

/-! ## A stage iso includes to a colimit iso (lax `colimHom_isIso_of_rep`)

  If a germ representative `f₀ : L.F a.2.1 x ⟶ L.F a.2.2 y` at a common bound `a` has a two-sided
  stage inverse `g₀`, then its inclusion `homInclL … a f₀` is an ISO in `laxColimCat L hL`.  The
  inverse is the germ of `g₀` at the swapped bound; both round-trips reduce — at the same stage `a.1`
  via `homCompRawL_eq_compAtL` + `push_refl` + `pushHom_id` — to the included stage identity, which
  is the colimit identity by `homInclL_compat`.  Mirrors the strict `colimHom_isIso_of_rep`, but the
  bare-sigma objects remove all `colimOut` transport. -/
theorem homInclL_isIso_of_rep (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L)
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    (f₀ : L.F a.2.1 x ⟶ L.F a.2.2 y) (g₀ : L.F a.2.2 y ⟶ L.F a.2.1 x)
    (h1 : f₀ ≫ g₀ = Cat.id (L.F a.2.1 x)) (h2 : g₀ ≫ f₀ = Cat.id (L.F a.2.2 y)) :
    @IsIso (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨j, y⟩
      (homInclL L hL x y a f₀) := by
  letI : Cat (Obj L) := laxColimCat L hL
  obtain ⟨av, ah1, ah2⟩ := a
  refine ⟨homInclL L hL y x ⟨av, ah2, ah1⟩ g₀, ?_, ?_⟩
  · -- f₀ ⊚ g₀ = id at level `av`: reduce to the stage composite `f₀ ≫ g₀ = id`, then `homInclL_compat`.
    show homCompRawL L hL x y x ⟨av, ah1, ah2⟩ f₀ ⟨av, ah2, ah1⟩ g₀ = idL L hL ⟨i, x⟩
    rw [homCompRawL_eq_compAtL L hL x y x ⟨av, ah1, ah2⟩ f₀ ⟨av, ah2, ah1⟩ g₀ av (D.refl av) (D.refl av)]
    unfold compAtL
    rw [hL.push_refl x y ah1 ah2 f₀, hL.push_refl y x ah2 ah1 g₀, h1]
    show homInclL L hL x x ⟨av, ah1, ah1⟩ (Cat.id (L.F ah1 x)) = idL L hL ⟨i, x⟩
    rw [show (idL L hL ⟨i, x⟩ : homL L hL ⟨i,x⟩ ⟨i,x⟩) = homIdL L hL x from rfl, homIdL,
        ← pushHom_id L x (D.refl i) ah1]
    exact homInclL_compat L hL x x (a := ⟨i, D.refl i, D.refl i⟩) (b := ⟨av, ah1, ah1⟩) ah1 (Cat.id _)
  · show homCompRawL L hL y x y ⟨av, ah2, ah1⟩ g₀ ⟨av, ah1, ah2⟩ f₀ = idL L hL ⟨j, y⟩
    rw [homCompRawL_eq_compAtL L hL y x y ⟨av, ah2, ah1⟩ g₀ ⟨av, ah1, ah2⟩ f₀ av (D.refl av) (D.refl av)]
    unfold compAtL
    rw [hL.push_refl y x ah2 ah1 g₀, hL.push_refl x y ah1 ah2 f₀, h2]
    show homInclL L hL y y ⟨av, ah2, ah2⟩ (Cat.id (L.F ah2 y)) = idL L hL ⟨j, y⟩
    rw [show (idL L hL ⟨j, y⟩ : homL L hL ⟨j,y⟩ ⟨j,y⟩) = homIdL L hL y from rfl, homIdL,
        ← pushHom_id L y (D.refl j) ah2]
    exact homInclL_compat L hL y y (a := ⟨j, D.refl j, D.refl j⟩) (b := ⟨av, ah2, ah2⟩) ah2 (Cat.id _)

/-! ## Interface bundles for the remaining finite limits (products, equalizers, pullbacks, PTC)

  These mirror the STRICT `colimitPreRegular`'s hypothesis tuples (`CatColimitRegular.lean:2450`):
  per-fibre limit existence PLUS the transitions' finite-limit PRESERVATION, packaged as one
  structure each.  In the STRICT setting preservation is phrased with `C.functF hij`; here the same
  shape applies verbatim with `L.functF hij` (each `L.F hij` is a genuine `Functor`).  For
  base-change these hypotheses are TRUE (the pullback functor `g*` preserves all finite limits —
  it is a right adjoint), so each bundle is inhabitable; discharging them for `laxOfProjSystem' P`
  is downstream work.

  The universal-property assembly (turning a bundle into a `HasBinaryProducts`/… instance on
  `laxColimCat L hL`) is the germ-algebra mirror of `colimitHasBinaryProducts`/`…Equalizers`/
  `…Pullbacks`; it is the precise NEXT BLOCKER (see the end of this file). -/

/-- LAX binary-product preservation bundle (mirrors `colimitHasBinaryProducts`'s `hp`/`hpres`/
    `hpres_pair`).  `hp` gives per-fibre products; `pres` is joint-monic preservation under a
    transition; `presPair` is pairing preservation under a transition. -/
structure LaxProductData (L : LaxCatSystem.{u, w} ι D) where
  hp : ∀ i, HasBinaryProducts (L.A i)
  pres : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
      (u v : z ⟶ L.F hij ((hp i).prod a b)),
      u ≫ (L.functF hij).map (hp i).fst = v ≫ (L.functF hij).map (hp i).fst →
      u ≫ (L.functF hij).map (hp i).snd = v ≫ (L.functF hij).map (hp i).snd → u = v
  presPair : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
      (p : z ⟶ L.F hij a) (q : z ⟶ L.F hij b),
      ∃ r : z ⟶ L.F hij ((hp i).prod a b),
        r ≫ (L.functF hij).map (hp i).fst = p ∧ r ≫ (L.functF hij).map (hp i).snd = q

/-- LAX equalizer-preservation bundle (mirrors `colimitHasEqualizers`'s `he`/`hepres`/`hepres_lift`). -/
structure LaxEqualizerData (L : LaxCatSystem.{u, w} ι D) where
  he : ∀ i, HasEqualizers (L.A i)
  pres : ∀ {i j} (hij : D.le i j) {A B : L.A i} (f g : A ⟶ B) (z : L.A j)
      (u v : z ⟶ L.F hij (eqObj f g)),
      u ≫ (L.functF hij).map (eqMap f g) = v ≫ (L.functF hij).map (eqMap f g) → u = v
  presLift : ∀ {i j} (hij : D.le i j) {A B : L.A i} (f g : A ⟶ B) (z : L.A j)
      (k : z ⟶ L.F hij A)
      (hk : k ≫ (L.functF hij).map f = k ≫ (L.functF hij).map g),
      ∃ r : z ⟶ L.F hij (eqObj f g), r ≫ (L.functF hij).map (eqMap f g) = k

/-! ## §M3b (lax) — binary products of the lax colimit category

  Mirrors `Colim.colimitHasBinaryProducts`.  For `⟨i,x⟩ × ⟨j,y⟩` pick a common bound `k` (filtered);
  the product object is the bare `⟨k, (hp k).prod (F x) (F y)⟩`.  Projections are SINGLE-STAGE germs
  `reflApp ≫ (hp k).fst|snd` at the trivial bound `⟨k, refl k, hik⟩` — no `colimOut`/`kp` transport,
  because the product object lives literally at stage `k`.  `pair` mediates via `presPair` at a common
  competitor stage; the laws push competitors to a common stage and apply `pres`. -/
section LaxProduct

variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L) (data : LaxProductData L)

/-- Common product bound of `i,j`. -/
private noncomputable def prK (D : Directed ι) (i j : ι) : ι := Classical.choose (D.bound i j)
private theorem prK_le (D : Directed ι) (i j : ι) : D.le i (prK D i j) ∧ D.le j (prK D i j) :=
  Classical.choose_spec (D.bound i j)

/-- The product object `⟨k, (hp k).prod (F x) (F y)⟩` in `Obj L`. -/
private noncomputable def prObj {i j : ι} (x : L.A i) (y : L.A j) : Obj L :=
  ⟨prK D i j, (data.hp (prK D i j)).prod (L.F (prK_le D i j).1 x) (L.F (prK_le D i j).2 y)⟩

/-- The `fst` projection germ: `reflApp ≫ (hp k).fst` at bound `⟨k, refl k, hik⟩`. -/
private noncomputable def prFst {i j : ι} (x : L.A i) (y : L.A j) :
    homL L hL (prObj L data x y) ⟨i, x⟩ :=
  homInclL L hL ((data.hp (prK D i j)).prod (L.F (prK_le D i j).1 x) (L.F (prK_le D i j).2 y)) x
    ⟨prK D i j, D.refl (prK D i j), (prK_le D i j).1⟩
    (reflApp L _ ≫ (data.hp (prK D i j)).fst)

/-- The `snd` projection germ. -/
private noncomputable def prSnd {i j : ι} (x : L.A i) (y : L.A j) :
    homL L hL (prObj L data x y) ⟨j, y⟩ :=
  homInclL L hL ((data.hp (prK D i j)).prod (L.F (prK_le D i j).1 x) (L.F (prK_le D i j).2 y)) y
    ⟨prK D i j, D.refl (prK D i j), (prK_le D i j).2⟩
    (reflApp L _ ≫ (data.hp (prK D i j)).snd)

end LaxProduct

end Freyd.LaxColim

/-!
════════════════════════════════════════════════════════════════════════════════════════════════
  STATUS + PRECISE NEXT BLOCKER (§1.543 — pre-regularity of the filtered lax colimit `ratCapCat P`)
════════════════════════════════════════════════════════════════════════════════════════════════

DONE here (all sorry-free; `#print axioms` = `Classical.choice`, `Quot.sound`; `reflApp_natural` = none):

  * `laxColimHasTerminal` — `HasTerminal (laxColimCat L hL)` from a `LaxTerminalData L` (per-fibre
    terminal + the pushed terminal is again terminal — the LAX analogue of the strict
    `hpres : F hij one = one`, which is FALSE in the lax setting since `F hij one ≅ one` only).
    Mirrors `Colim.colimitHasTerminal`; the bare-sigma carrier removes all `colimOut`.
  * `reflApp` / `reflApp_isIso` / `reflApp_natural` — the UNIT coherence component (forward of
    `F_refl_iso`), the lax companion of `transApp`.  The conjugator for single-stage germ reps.
  * `homInclL_isIso_of_rep` — a stage iso includes to a colimit iso (lax `colimHom_isIso_of_rep`).
    The workhorse for showing an included stage limit-cone is universal (via `isIso_of_product_up`).
  * `LaxProductData` / `LaxEqualizerData` — the per-fibre-limit + transition-preservation hypothesis
    bundles (the exact shapes the strict `colimitPreRegular` consumes, re-expressed with `L.functF`).
    TRUE for base-change (`g*` is a right adjoint ⇒ preserves finite limits); inhabiting them for
    `laxOfProjSystem' P` is downstream.

PRECISE NEXT BLOCKER — `HasBinaryProducts (laxColimCat L hL)` from a `LaxProductData L` (then the
analogous `HasEqualizers`/`HasPullbacks`, then `PullbacksTransferCovers`, then assemble
`PreRegularCategory`).  This is the germ-algebra mirror of `Colim.colimitHasBinaryProducts`
(`CatColimitRegular.lean:104`), the largest single block of the strict assembly (~300 lines of
`castHom` algebra).  The lax version replaces:

    strict `castHom` (transport along the strict object-eqs `F_refl`/`F_trans`)
  ⟶ lax     `pushHom` / `reflApp` / `transApp` (conjugation by the coherence iso COMPONENTS),

and otherwise follows the same plan: for `⟨i,x⟩ × ⟨j,y⟩`, choose a common bound `k` (filtered),
set the product object to `objIncl k ((data.hp k).prod (F x) (F y)) = ⟨k, …⟩`, take projections as
single-stage germs `reflApp ≫ (data.hp k).fst|snd` at `⟨k, refl, …⟩`, define `pair` by the mediating
germ from `data.presPair` at a common stage of the two competitor germs, and prove `fst_pair`/
`snd_pair`/`pair_uniq` by pushing competitors to a common stage and applying `data.pres` (the
joint-monic preservation) — the lax mirror of `objIncl_preserves_products` /
`colimHom_monicPair_of_rep`.  The mechanical risk is entirely the `pushHom`/`reflApp` conjugation
bookkeeping (the strict proof's `castHom_castHom`/`map_castHom`/`castHom_comp` chains become
`pushHom_comp` + `reflApp_natural`/`transApp_natural` + iso-cancellation chains).  Once products,
equalizers and pullbacks land, `PullbacksTransferCovers` aligns a colimit cover+pullback to a common
fibre (each fibre is `overPreRegular`, so has PTC) and transfers back, and `PreRegularCategory
(ratCapCat P)` assembles exactly as `Colim.colimitPreRegular`.
-/
