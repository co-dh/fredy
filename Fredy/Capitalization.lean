/-
  Freyd & Scedrov, *Categories and Allegories* §1.543  The CAPITALIZATION LEMMA.

  Every small pre-regular category `A` admits a FAITHFUL functor into a CAPITAL
  pre-regular category `Ā`.

  This file assembles the transfinite iteration from the pieces already built in
  the repo:

    * `S1_54.lean §1.544`  — one slice step `A → A/B` separates morphisms when `B`
      is well-supported (`slice_embedding_separates`).
    * `CatColimit.lean`    — directed colimit of categories (`CatSystem`, `Coherent`,
      `colimitCat`, `objIncl`, `homInclObj`).
    * `CatColimitRegular.lean` — the colimit of a coherent system of pre-regular
      categories is pre-regular (`colimitPreRegular`), faithfulness of the stage
      inclusion (`homInclObj_injective`), and cover reflection
      (`homInclObj_cover_reflects`, `colimHom_cover_reflects`).

  The construction is organised around the abstract successor-step interface
  `CapStep` (§1.545 relative capitalization, packaged), the directed system it
  generates (§1.543 iteration), the colimit (`colimitPreRegular`), and the capital
  closure argument (§1.543 fixpoint).

  CATEGORY THEORY stays on this repo's own `Cat`.  We deliberately do NOT import
  mathlib: the directed-colimit machinery in `CatColimit*` already supplies a
  `Directed`-indexed colimit, so the iteration is expressed over a hand-built
  directed index rather than mathlib ordinals.  (The §1.543 mathlib exception in
  CLAUDE.md is *available*, but mathlib is not a dependency of this repo and the
  colimit machinery is `Directed`-indexed, not ordinal-indexed, so importing it
  would buy nothing here.)

  STATUS.  The whole categorical assembly is now proved sorry-free:

    * `faithful_comp`           — faithful functors compose to faithful functors.
    * `stageInclFaithful`       — the colimit stage-inclusion `A i → Ā` is faithful,
      given that every transition functor is faithful (via `homInclObj_injective`
      and `homInclObj_isIso_reflects`).
    * the ω-tower `CatSystem` itself: `towerSystem` (objects `towerObj`, transitions
      `towerF`/`towerFunctF`, with `F_refl`/`F_trans` the difference-cast bookkeeping)
      and its coherence `towerCoherent` — both `propext`/`Quot.sound`-only (constructive,
      no `Classical.choice`).  The Nat-difference casts are handled by the helpers
      `stageCast`/`stageCastHom`, `transN_add`, `transNFun_map_add`, and the carrier-equal
      congruence lemmas.
    * `capData_of_tower` — assembles a full `CapData A` from the tower plus the
      `colimitPreRegular` preservation package and the capital closure: `base = id`
      (stage 0 is `A`), `hfaith`/`hcons` from `transNFaithful` via `towerHfaith`/`towerHcons`.

  `capData_exists` is thereby reduced to the two genuine §1.543 walls, now SPLIT into two
  separately-stated, separately-attackable `sorry`s with their dependency exposed:
    (1) `hwall_step` — the uniform pre-regular-preserving successor `nextStep` (§1.544/§1.545
        slice successor `A ↦ A*`, buildable from `overPreRegular`) together with the per-`i≤j`
        tower preservation package; and
    (2) `hwall_cap` — the capital closure of the colimit (§1.543 fixpoint via
        `colimHom_cover_reflects`), stated *over* the colimit pre-regular structure that (1)
        supplies, so it genuinely consumes (1).
  No other gap remains.
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31
import Fredy.S1_33
import Fredy.S1_52
import Fredy.SliceRegular
import Fredy.CatColimit
import Fredy.CatColimitRegular

open Freyd
open Freyd.Colim

universe v u

namespace Freyd

/-! ## Glue lemma: faithful functors compose

  `Faithful = Embedding ∧ reflects-iso` (§1.33).  Both properties compose, so a
  composite of faithful functors is faithful.  This is needed to thread the
  faithfulness of `A = A₀ → Ā` through the (finitely or transfinitely many)
  successor steps and the final colimit inclusion. -/

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟] {ℰ : Type u} [Cat.{v} ℰ]

/-- Faithful functors compose.  `embedding_comp` (§1.31) gives the embedding half;
    iso-reflection composes directly (`G` reflects iso, then `F` reflects iso). -/
theorem faithful_comp {F : 𝒞 → 𝒟} {G : 𝒟 → ℰ} [hF : Functor F] [hG : Functor G]
    (fF : Faithful F) (fG : Faithful G) : Faithful (G ∘ F) := by
  refine ⟨embedding_comp fF.1 fG.1, ?_⟩
  intro A B f hiso
  -- `(G∘F).map f` iso ⟹ `F.map f` iso (G reflects) ⟹ `f` iso (F reflects).
  exact fF.2 f (fG.2 (hF.map f) hiso)

end Freyd

/-! ## The colimit stage-inclusion is faithful

  This is the §1.543 step-5 ingredient: each injection `A i → Ā` of a stage into the
  transfinite colimit is faithful.  We work entirely with the existing
  `CatColimitRegular` API:

    * object part is `C.objIncl i`,
    * morphism part is `homInclObj C hC`,
    * functoriality is `homInclObj_comp`,
    * embedding (injectivity on homs) is `homInclObj_injective`,
    * iso-reflection is `homInclObj_consIso`.

  Both injectivity and iso-reflection are *conditional on the transitions being
  faithful* (`hfaith`) and `hcons`/`hmono`; those hypotheses hold in our iteration
  because every successor step is a faithful pre-regular embedding. -/

namespace Freyd.Colim

universe w

variable {ι : Type u} {D : Directed ι}

/-- The object part of the stage-`i` inclusion `A i → Ā`. -/
abbrev stageInclObj (C : CatSystem ι D) (i : ι) : C.A i → C.Obj := C.objIncl i

/-- **The stage inclusion sends identities to identities.**  Needed to package the
    stage inclusion `(objIncl i, homInclObj)` as an honest `Functor`.  Compute
    `homInclObj (Cat.id x)` at the canonical witness via `homInclObj_eq`; the germ is
    a `castHom` of `functF.map (Cat.id x) = Cat.id (...)`, which is the identity germ
    `colimId` of `objIncl i x` after absorbing the cast and transition. -/
theorem homInclObj_id (C : CatSystem ι D) (hC : C.Coherent) {i : ι} (x : C.A i) :
    homInclObj C hC (Cat.id x) = colimId C hC (C.objIncl i x) := by
  let w := hioWitness C hC x x
  -- compute `homInclObj (id)` at the witness `w`; its germ is the identity at stage `w.K`.
  rw [homInclObj_eq C hC (Cat.id x) w]
  have hgerm : w.germ (Cat.id x) = Cat.id (C.F w.hpx (colimOut C (C.objIncl i x)).2) := by
    unfold HioWitness.germ
    rw [(C.functF w.hix).map_id]
    exact castHom_of_heq _ _ (by rw [w.hgx])
  rw [hgerm]
  -- both sides are identity germs of the SAME hom-colimit `HomColim … (out).2 (out).2`;
  -- `colimId` is the id germ at the trivial bound `(out).1`, and `homIncl_compat` +
  -- `homTr_id` push it up to the bound `w.K`.
  unfold colimId homClassId
  have key := homIncl_compat C hC (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i x)).2
    (a := ⟨(colimOut C (C.objIncl i x)).1, D.refl _, D.refl _⟩)
    (b := ⟨w.K, w.hpx, w.hpx⟩) w.hpx (Cat.id _)
  rw [homTr_id] at key
  -- `key` is exactly the goal: the witness bound `⟨w.K, w.hpx, w.hpy⟩` and `⟨w.K, w.hpx, w.hpx⟩`
  -- coincide proof-irrelevantly, and the trivial bound `⟨(out).1, refl, refl⟩` is `colimId`.
  exact key

/-- **§1.543 step 5 (faithfulness of a stage inclusion), embedding half.**
    The stage inclusion `A i → Ā` separates morphisms, provided every transition
    functor is faithful on morphisms (`hfaith`).  This is exactly
    `homInclObj_injective` rephrased as `Embedding`-style injectivity on the
    stage `i`.  (We state it as injectivity of `homInclObj` rather than via the
    `Embedding` typeclass because the stage-inclusion's object map `objIncl i` and
    its hom map `homInclObj` are packaged separately in `CatColimitRegular`, not as
    a single `Functor (objIncl i)` instance.) -/
theorem stageIncl_separates (C : CatSystem ι D) (hC : C.Coherent)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    {i : ι} {x y : C.A i} (g g' : x ⟶ y)
    (h : homInclObj C hC g = homInclObj C hC g') : g = g' :=
  homInclObj_injective C hC hfaith g g' h

/-- **§1.543 step 5 (faithfulness of a stage inclusion), reflects-iso half.**
    If `homInclObj g` is iso in `Ā` then `g` is iso in `A i`, provided transitions
    are conservative (`hcons`).  This is `homInclObj_isIso_reflects`. -/
theorem stageIncl_reflectsIso (C : CatSystem ι D) (hC : C.Coherent)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso ((C.functF hij).map φ) → IsIso φ)
    {i : ι} {x y : C.A i} (g : x ⟶ y)
    (hiso : @IsIso C.Obj (colimitCat C hC) (C.objIncl i x) (C.objIncl i y) (homInclObj C hC g)) :
    IsIso g :=
  homInclObj_isIso_reflects C hC hcons g hiso

/-- **The stage inclusion `A i → Ā` is an honest `Functor`.**  Object part `objIncl i`,
    morphism part `homInclObj`, identity by `homInclObj_id`, composition by
    `homInclObj_comp`.  (The `colimitCat` instance on `C.Obj` is supplied via `letI`.) -/
noncomputable def stageInclFunctor (C : CatSystem ι D) (hC : C.Coherent) (i : ι) :
    letI : Cat C.Obj := colimitCat C hC
    @Functor (C.A i) (C.catA i) C.Obj (colimitCat C hC) (C.objIncl i) :=
  letI : Cat C.Obj := colimitCat C hC
  { map := fun {_ _} g => homInclObj C hC g
    map_id := fun x => homInclObj_id C hC x
    map_comp := fun {_ _ _} g g' => homInclObj_comp C hC g g' }

/-- **§1.543 step 5 — the stage inclusion `A i → Ā` is FAITHFUL.**  Embedding half is
    `homInclObj_injective` (needs transitions faithful, `hfaith`); reflects-iso half is
    `homInclObj_isIso_reflects` (needs transitions conservative, `hcons`).  This is the
    fact that the colimit injection of a stage is faithful — directly usable for the
    composite `A = A₀ → Ā`. -/
theorem stageInclFaithful (C : CatSystem ι D) (hC : C.Coherent)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso ((C.functF hij).map φ) → IsIso φ)
    (i : ι) :
    letI : Cat C.Obj := colimitCat C hC
    @Faithful (C.A i) (C.catA i) C.Obj (colimitCat C hC) (C.objIncl i) (stageInclFunctor C hC i) := by
  letI : Cat C.Obj := colimitCat C hC
  refine ⟨?_, ?_⟩
  · intro x y g g' h
    exact homInclObj_injective C hC hfaith g g' h
  · intro x y g hiso
    exact homInclObj_isIso_reflects C hC hcons g hiso

end Freyd.Colim

/-! ## §1.543 The capitalization data, and the reduction to it

  We isolate everything the transfinite §1.543 construction must produce into a single
  structure `CapData A`.  It bundles a directed system of pre-regular categories whose
  colimit is the capitalization `Ā` of `A`:

    * the directed index and `CatSystem` `C`, its coherence `hC`, and nonemptiness;
    * a base index `i₀` and a faithful functor `base : A → A_{i₀}` (the start of the tower);
    * the full `colimitPreRegular` preservation package (terminal / products / equalizers /
      pullback-covers preserved by every transition) so the colimit is pre-regular;
    * the faithfulness data of the transitions (`hfaith`, `hcons`) so each stage injects
      faithfully into the colimit;
    * the capital proof for the colimit (`capital` — every well-supported object of `Ā`
      is well-pointed); this is the §1.543 fixpoint/closure conclusion.

  Given a `CapData A`, the capitalization lemma is immediate:
    * `Ā = C.Obj` with the `colimitCat` instance;
    * pre-regular by `colimitPreRegular`;
    * capital by the bundled proof;
    * the faithful functor `A → Ā` is `objIncl i₀ ∘ base`, faithful by `faithful_comp`
      of `base` (bundled faithful) with `stageInclFunctor i₀` (faithful by
      `stageInclFaithful`).

  What remains for a sorry-free §1.543 is exactly `capData_exists : ∀ A, CapData A` — the
  transfinite recursion building the tower and proving the capital closure.  That is the
  genuine wall (a type-level ordinal recursion whose limit stages are the colimits of their
  predecessors, plus the fixpoint argument).  `capitalization_lemma` below is reduced to it. -/

namespace Freyd

open Freyd.Colim

/-- The data the §1.543 transfinite construction produces: a directed system of pre-regular
    categories, faithful in its transitions, whose colimit is capital, with a faithful base
    embedding of `A`.  See the module docstring for the field-by-field meaning. -/
structure CapData (A : Type u) [Cat.{u} A] [PreRegularCategory A] where
  /-- directed index of the tower -/
  ι : Type u
  D : Directed ι
  /-- the tower itself as a coherent system of categories.  Objects and morphisms share the
      universe `u`: the directed-colimit machinery (`CatSystem`/`colimitCat`) requires the
      object and morphism universes to coincide (`catA : Cat.{u} (A i)` with `A i : Type u`),
      so the §1.543 capitalization is built for *small* categories with `Cat.{u}` on `Type u`. -/
  C : CatSystem.{u, u} ι D
  hC : C.Coherent
  hne : Nonempty ι
  /-- the base stage and the faithful start `A → A_{i₀}` -/
  i₀ : ι
  base : A → C.A i₀
  baseFun : @Functor A _ (C.A i₀) (C.catA i₀) base
  baseFaithful : @Faithful A _ (C.A i₀) (C.catA i₀) base baseFun
  /-- every transition is faithful on morphisms and conservative — so stages inject faithfully -/
  hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
    (C.functF hij).map p = (C.functF hij).map q → p = q
  hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
    IsIso ((C.functF hij).map φ) → IsIso φ
  /-- the `colimitPreRegular` preservation package -/
  ht : ∀ i, HasTerminal (C.A i)
  htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one
  hp : ∀ i, HasBinaryProducts (C.A i)
  hppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
    (u v : z ⟶ C.F hij ((hp i).prod a b)),
    u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
    u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v
  hppres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
    (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
    ∃ r : z ⟶ C.F hij ((hp i).prod a b),
      r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q
  he : ∀ i, HasEqualizers (C.A i)
  hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
    (u v : z ⟶ C.F hij (eqObj f g)),
    u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v
  hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
    (k : z ⟶ C.F hij A)
    (_hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
    ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k
  hcanon : letI : Cat C.Obj := colimitCat C hC
      letI : HasPullbacks C.Obj :=
        colimitHasPullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
    ∀ {A B Z : C.Obj} (f : A ⟶ Z) (g : B ⟶ Z),
        Cover f → Cover (HasPullbacks.has f g).cone.π₂
  /-- the §1.543 capital-closure conclusion for the colimit -/
  capital : letI : Cat C.Obj := colimitCat C hC
      letI : PreRegularCategory C.Obj :=
        colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
    Capital (𝒞 := C.Obj)

/-- **§1.543 reduction.**  From the capitalization data, assemble the capital pre-regular
    target `Ā = C.Obj` and the faithful representation `A → Ā = objIncl i₀ ∘ base`. -/
theorem capitalization_of_capData {A : Type u} [Cat.{u} A] [PreRegularCategory A]
    (cd : CapData.{u} A) :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hP : PreRegularCategory Ā),
      @Capital.{u, u} Ā hC (hP.toHasTerminal) ∧
      ∃ (F : A → Ā) (hF : Functor F), @Faithful.{u, u} A _ Ā hC F hF := by
  haveI := cd.hne
  letI : Cat cd.C.Obj := colimitCat cd.C cd.hC
  letI hPre : PreRegularCategory cd.C.Obj :=
    colimitPreRegular cd.C cd.hC cd.ht cd.htpres cd.hp cd.hppres cd.hppres_pair
      cd.he cd.hepres cd.hepres_lift cd.hcanon
  refine ⟨cd.C.Obj, _, hPre, cd.capital, ?_⟩
  -- the faithful representation is `objIncl i₀ ∘ base`
  letI := cd.baseFun
  letI : @Functor (cd.C.A cd.i₀) (cd.C.catA cd.i₀) cd.C.Obj _ (cd.C.objIncl cd.i₀) :=
    stageInclFunctor cd.C cd.hC cd.i₀
  refine ⟨cd.C.objIncl cd.i₀ ∘ cd.base, inferInstance, ?_⟩
  exact faithful_comp cd.baseFaithful
    (stageInclFaithful cd.C cd.hC cd.hfaith cd.hcons cd.i₀)

/-! ## §1.543 The ω-tower scaffolding for the transfinite recursion

  The transfinite recursion `A₀ = A`, `A_{α+1} = (A_α)*`, `A_λ = colim_{β<λ}` is, at the
  *successor* level, an ω-indexed tower: a sequence of stages `S : ℕ → Type u` with
  faithful pre-regular-preserving transitions `S n → S (n+1)`.  We make the directed
  index, the per-step interface, and the reduction of `CapData` to "a tower whose colimit
  is capital" explicit.  This isolates the two genuine walls — (i) building the step
  sequence (needs `PreRegularCategory (Over B)` for the slice successor; a parallel
  obligation) and (ii) the capital-closure of the colimit — from the directed-colimit
  bookkeeping, which is already in hand. -/

namespace Colim

/-- `ℕ` with its usual order is a directed preorder: reflexive, transitive, and any two
    naturals have a common upper bound (their max).  This is the index of the ω-tower. -/
def natDirected : Directed Nat where
  le := Nat.le
  refl := Nat.le_refl
  trans := Nat.le_trans
  bound i j := ⟨Nat.max i j, Nat.le_max_left i j, Nat.le_max_right i j⟩

end Colim

/-! ### The single successor-step interface `CapStep`

  One rung of the tower: a faithful, pre-regular-preserving functor `S → T` between two
  *small* pre-regular categories.  This is exactly Freyd's `A_α → A_{α+1} = (A_α)*`
  (§1.545 relative capitalization, §1.544 faithful slice embedding).  We carry the *single-step*
  versions of every hypothesis `colimitPreRegular` consumes (terminal / products / equalizers
  preserved by the one functor `step`), so that an ω-sequence of `CapStep`s, once its transitions
  are iterated, supplies the whole `colimitPreRegular` preservation package.

  Producing the `step` from `S` is the parallel obligation that needs `PreRegularCategory (Over B)`
  for the slice successor; here `CapStep` is the *interface*, so the construction below is
  decoupled from that open sub-step. -/
structure CapStep (S : Type u) [Cat.{u} S] [PreRegularCategory S] where
  /-- the next stage `T = S*` -/
  T : Type u
  catT : Cat.{u} T
  preT : @PreRegularCategory T catT
  /-- the successor functor `S → T` and its functoriality -/
  step : S → T
  stepFun : @Functor S _ T catT step
  /-- §1.544: the step is faithful (separates morphisms; conservative) -/
  stepFaithful : @Faithful S _ T catT step stepFun

/-! ### The ω-tower of stages generated by a uniform successor functor

  Freyd's relative capitalization `(-)*` is a *uniform* construction: it sends any small
  pre-regular category to a faithful pre-regular extension.  We model this as a single
  polymorphic `nextStep : ∀ S, CapStep S`, and iterate it.  `stageBundle A nextStep n`
  is the `n`-th stage as a bundled `(Type u, Cat, PreRegular)`; `stageTy`/`stageCat`/`stagePre`
  project the pieces. -/

/-- A bundled small pre-regular category: carrier, `Cat` instance, `PreRegularCategory` instance.
    Used to carry the dependent stages of the ω-tower through `Nat.rec`. -/
structure PreRegBundle where
  carrier : Type u
  cat : Cat.{u} carrier
  pre : @PreRegularCategory carrier cat

attribute [instance] PreRegBundle.cat PreRegBundle.pre

variable {A : Type u} [Cat.{u} A] [PreRegularCategory A]

/-- The `n`-th stage of the ω-tower, as a bundle.  `stage 0 = A`; `stage (n+1)` is the
    successor `(stage n)*` chosen by `nextStep`. -/
def stageBundle (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) :
    PreRegBundle.{u} → Nat → PreRegBundle.{u}
  | b, 0 => b
  | b, (n+1) =>
    let s := nextStep (stageBundle nextStep b n)
    ⟨s.T, s.catT, s.preT⟩

/-- The single-step functor from stage `n` to stage `n+1`. -/
def stageStep (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (b : PreRegBundle.{u})
    (n : Nat) : (stageBundle nextStep b n).carrier → (stageBundle nextStep b (n+1)).carrier :=
  (nextStep (stageBundle nextStep b n)).step

/-- The iterated transition `stage n → stage (n+d)`, by recursion on the difference `d`:
    compose `d` consecutive `stageStep`s.  This is the object map of the tower's transition
    functor; expressing transitions by *difference* (rather than by a `≤`-proof) keeps the
    recursion mathlib-free (`Nat.leRec` is not in core). -/
def transN (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (b : PreRegBundle.{u}) (n : Nat) :
    ∀ d : Nat, (stageBundle nextStep b n).carrier → (stageBundle nextStep b (n+d)).carrier
  | 0 => id
  | (d+1) => fun x => stageStep nextStep b (n+d) (transN nextStep b n d x)

@[simp] theorem transN_zero (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n : Nat) (x : (stageBundle nextStep b n).carrier) :
    transN nextStep b n 0 x = x := rfl

@[simp] theorem transN_succ (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n d : Nat) (x : (stageBundle nextStep b n).carrier) :
    transN nextStep b n (d+1) x = stageStep nextStep b (n+d) (transN nextStep b n d x) := rfl

/-- One rung `stageStep n` is a functor (it is the bundled `CapStep.step`). -/
instance stageStepFun (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n : Nat) :
    @Functor _ (stageBundle nextStep b n).cat _ (stageBundle nextStep b (n+1)).cat
      (stageStep nextStep b n) :=
  (nextStep (stageBundle nextStep b n)).stepFun

/-- One rung `stageStep n` is faithful (§1.544). -/
theorem stageStepFaithful (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n : Nat) :
    @Faithful _ (stageBundle nextStep b n).cat _ (stageBundle nextStep b (n+1)).cat
      (stageStep nextStep b n) (stageStepFun nextStep b n) :=
  (nextStep (stageBundle nextStep b n)).stepFaithful

/-- The rung functor `stageStep`'s `.map` respects heterogeneous equality of arguments at
    carrier-equal stages.  (Both objects and morphisms transport along the stage equality `m = n`.) -/
theorem stageStepFun_map_congr_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (hmn : m = n) {x y : (stageBundle nextStep b m).carrier} {x' y' : (stageBundle nextStep b n).carrier}
    (hx : HEq x x') (hy : HEq y y') {g : x ⟶ y} {g' : x' ⟶ y'} (hg : HEq g g') :
    HEq ((stageStepFun nextStep b m).map g) ((stageStepFun nextStep b n).map g') := by
  subst hmn
  -- same stage now; the endpoints coincide, so `g ≈ g'` forces `g = g'`
  cases eq_of_heq hx; cases eq_of_heq hy; cases eq_of_heq hg; rfl

/-- The iterated transition `transN n d` is a functor: a composite of the `d` rung functors. -/
def transNFun (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n : Nat) :
    ∀ d, @Functor _ (stageBundle nextStep b n).cat _ (stageBundle nextStep b (n+d)).cat
      (transN nextStep b n d)
  | 0 => { map := fun f => f, map_id := fun _ => rfl, map_comp := fun _ _ => rfl }
  | (d+1) =>
    letI hF := transNFun nextStep b n d
    letI hG := stageStepFun nextStep b (n+d)
    -- `transN n (d+1) x = stageStep (n+d) (transN n d x)`, so map is `hG.map ∘ hF.map`
    { map := fun f => hG.map (hF.map f)
      map_id := fun x => by rw [hF.map_id, hG.map_id]; rfl
      map_comp := fun f g => by rw [hF.map_comp, hG.map_comp] }

/-- The iterated transition `transN n d` is faithful: a composite of faithful rungs. -/
theorem transNFaithful (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n : Nat) :
    ∀ d, @Faithful _ (stageBundle nextStep b n).cat _ (stageBundle nextStep b (n+d)).cat
      (transN nextStep b n d) (transNFun nextStep b n d)
  | 0 => ⟨fun _ _ h => h, fun _ h => h⟩
  | (d+1) => by
    refine ⟨fun f g h => ?_, fun f hiso => ?_⟩
    · -- embedding: hG (hF f) = hG (hF g) ⟹ (faithful hG) hF f = hF g ⟹ (faithful hF) f = g
      exact (transNFaithful nextStep b n d).1 f g
        ((stageStepFaithful nextStep b (n+d)).1 _ _ h)
    · exact (transNFaithful nextStep b n d).2 f
        ((stageStepFaithful nextStep b (n+d)).2 _ hiso)

/-! ### The ω-tower as a `CatSystem` over `ULift Nat`, and the reduction of `capData_exists`

  The colimit machinery indexes by `ι : Type u`, so the ω-tower's index is `ULift.{u} Nat`
  (carrying `Nat`'s order).  From a uniform successor functor `nextStep`, the stages
  `stageBundle` and iterated transitions `transN` provide the object/morphism data; what
  remains to turn them into a `CatSystem` is the *cast-coherence* of expressing the
  difference-recursion transition `transN n (j-i)` as a `≤`-indexed `F i j`, and lifting the
  single-step preservation in `CapStep` to arbitrary `i ≤ j`.  These — together with the
  §1.543 capital-closure of the resulting colimit — are the residual sub-obligations,
  isolated as the explicit hypotheses of `capData_of_nextStep`. -/

/-- `ULift.{u} Nat` with `Nat`'s order is a directed preorder: the `Type u` index of the
    ω-tower (the colimit machinery requires `ι : Type u`). -/
def uliftNatDirected : Directed (ULift.{u} Nat) where
  le a b := a.down ≤ b.down
  refl a := Nat.le_refl a.down
  trans h h' := Nat.le_trans h h'
  bound a b := ⟨⟨Nat.max a.down b.down⟩, Nat.le_max_left _ _, Nat.le_max_right _ _⟩

variable (b : PreRegBundle.{u})

/-- The object family of the ω-tower `CatSystem`: stage `i` is `(stageBundle b i.down).carrier`. -/
def towerObj (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (i : ULift.{u} Nat) :
    Type u := (stageBundle nextStep b i.down).carrier

/-- The `≤`-indexed transition `towerObj i → towerObj j` for `i ≤ j`: run the difference
    recursion `transN i.down (j.down - i.down)` and cast its codomain `stage (i.down+(j.down-i.down))`
    to `stage j.down` along `i.down + (j.down - i.down) = j.down` (from `i.down ≤ j.down`). -/
def towerF (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : i.down ≤ j.down) :
    towerObj b nextStep i → towerObj b nextStep j :=
  fun x => (Nat.add_sub_cancel' hij ▸ transN nextStep b i.down (j.down - i.down) x :
    (stageBundle nextStep b j.down).carrier)

/-! ### Cast helpers for the difference recursion

  Two ingredients turn the difference-recursion `transN` into a `≤`-indexed `CatSystem.F`:

    * `stageCast` / `stageCastHom` — transport an object / morphism across the *Nat*-equality
      `m = n` between stage carriers `stage m = stage n`.  (The carriers are literally equal as
      types once `m = n`, so this is `Eq.rec`; `stageCastHom` is the morphism version, and
      `stageCastHom_heq` exposes it as `HEq`-to-the-original for the coherence proofs.)
    * `transN_add` — the iterated transition splits additively, `transN n (d+e) = transN (n+d) e ∘
      transN n d`, modulo the carrier identification `(n+d)+e = n+(d+e)`.  This is the object-level
      content of `CatSystem.F_trans`.

  All `Coherent` content reduces to these plus `transNFun`'s functoriality (already proven). -/

/-- Transport an object across the stage-carrier equality induced by `m = n : Nat`. -/
def stageCast (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat} (h : m = n)
    (x : (stageBundle nextStep b m).carrier) : (stageBundle nextStep b n).carrier := h ▸ x

@[simp] theorem stageCast_rfl (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m : Nat}
    (x : (stageBundle nextStep b m).carrier) : stageCast b nextStep (rfl : m = m) x = x := rfl

/-- The object transport is heterogeneously the original object. -/
theorem stageCast_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) (x : (stageBundle nextStep b m).carrier) :
    HEq (stageCast b nextStep h x) x := by subst h; rfl

/-- Transport a *morphism* across the stage-carrier equality induced by `m = n : Nat`. -/
def stageCastHom (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat} (h : m = n)
    {x y : (stageBundle nextStep b m).carrier} (g : x ⟶ y) :
    stageCast b nextStep h x ⟶ stageCast b nextStep h y := by
  subst h; exact g

/-- The morphism transport is heterogeneously the original morphism. -/
theorem stageCastHom_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) {x y : (stageBundle nextStep b m).carrier} (g : x ⟶ y) :
    HEq (stageCastHom b nextStep h g) g := by subst h; rfl

/-- The morphism transport preserves identities. -/
theorem stageCastHom_id (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) (x : (stageBundle nextStep b m).carrier) :
    stageCastHom b nextStep h (Cat.id x) = Cat.id (stageCast b nextStep h x) := by subst h; rfl

/-- The morphism transport distributes over composition. -/
theorem stageCastHom_comp (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) {x y z : (stageBundle nextStep b m).carrier} (f : x ⟶ y) (g : y ⟶ z) :
    stageCastHom b nextStep h (f ≫ g) =
      stageCastHom b nextStep h f ≫ stageCastHom b nextStep h g := by subst h; rfl

/-- `stageStep` commutes with the stage-cast: applying the successor rung after a cast equals
    casting after the successor rung (the carriers `stage m`, `stage n` agree once `m = n`). -/
theorem stageStep_stageCast (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) (x : (stageBundle nextStep b m).carrier) :
    stageStep nextStep b n (stageCast b nextStep h x) =
      stageCast b nextStep (by omega : m + 1 = n + 1) (stageStep nextStep b m x) := by
  subst h; rfl

/-- The iterated transition splits additively (object level).  `transN n (d+e)` first runs
    `transN n d` to stage `n+d`, then `transN (n+d) e` to stage `(n+d)+e`, which is `stage (n+(d+e))`
    after the carrier identification `(n+d)+e = n+(d+e)`. -/
theorem transN_add (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (n d : Nat) :
    ∀ (e : Nat) (x : (stageBundle nextStep b n).carrier),
      transN nextStep b n (d + e) x =
        stageCast b nextStep (by omega)
          (transN nextStep b (n + d) e (transN nextStep b n d x))
  | 0, x => by simp [transN, stageCast]
  | (e+1), x => by
    -- LHS: `transN n (d+(e+1)) = stageStep (n+(d+e)) (transN n (d+e) x)`
    show stageStep nextStep b (n + (d + e)) (transN nextStep b n (d + e) x) = _
    rw [transN_add nextStep n d e x, stageStep_stageCast]
    -- both sides are a `stageCast` (= `Eq.rec`) of the SAME underlying object
    -- `stageStep (n+d+e) (transN (n+d) e (transN n d x))`, over carrier-equal Nat indices, hence
    -- equal after dropping both casts via `eqRec_heq`.
    apply eq_of_heq
    refine (stageCast_heq b nextStep _ _).trans ?_
    show HEq (stageStep nextStep b (n + d + e) _) _
    rw [transN_succ]
    exact (stageCast_heq b nextStep _ _).symm

/-- Object additivity of the difference recursion, HEq form (drops the `stageCast` from
    `transN_add`). -/
theorem transN_add_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (n d e : Nat)
    (x : (stageBundle nextStep b n).carrier) :
    HEq (transN nextStep b n (d + e) x)
      (transN nextStep b (n + d) e (transN nextStep b n d x)) := by
  rw [transN_add b nextStep n d e x]; exact stageCast_heq b nextStep _ _

/-- `transN _ d` respects heterogeneous equality of base objects at carrier-equal stages. -/
theorem transN_congr_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (hmn : m = n) (d : Nat) {x : (stageBundle nextStep b m).carrier}
    {y : (stageBundle nextStep b n).carrier} (hxy : HEq x y) :
    HEq (transN nextStep b m d x) (transN nextStep b n d y) := by subst hmn; rw [eq_of_heq hxy]

/-- `transNFun _ d`'s `.map` respects heterogeneous equality of base morphisms at carrier-equal
    stages (endpoints HEq, morphism HEq). -/
theorem transNFun_map_congr_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (hmn : m = n) {x y : (stageBundle nextStep b m).carrier}
    {x' y' : (stageBundle nextStep b n).carrier} (hx : HEq x x') (hy : HEq y y')
    {d : Nat} {g : x ⟶ y} {g' : x' ⟶ y'} (hg : HEq g g') :
    HEq ((transNFun nextStep b m d).map g) ((transNFun nextStep b n d).map g') := by
  subst hmn; cases eq_of_heq hx; cases eq_of_heq hy; cases eq_of_heq hg; rfl

/-- The morphism map of the `≤`-indexed transition `towerF hij`: map `g` by the difference
    functor `transNFun i.down (j.down-i.down)`, then transport along the carrier equality. -/
def towerFmap (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : i.down ≤ j.down)
    {x y : towerObj b nextStep i} (g : @Cat.Hom _ (stageBundle nextStep b i.down).cat x y) :
    @Cat.Hom _ (stageBundle nextStep b j.down).cat (towerF b nextStep hij x) (towerF b nextStep hij y) :=
  stageCastHom b nextStep (Nat.add_sub_cancel' hij)
    ((transNFun nextStep b i.down (j.down - i.down)).map g)

/-- `towerF hij` is a functor (object map `towerF`, morphism map `towerFmap`): a stage-cast of the
    difference functor `transNFun`, which is itself a functor; the cast `stageCastHom` is
    functorial (`subst` reduces it to identity). -/
def towerFunctF (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : i.down ≤ j.down) :
    @Functor _ ((stageBundle nextStep b i.down).cat) _ ((stageBundle nextStep b j.down).cat)
      (towerF b nextStep hij) where
  map g := towerFmap b nextStep hij g
  map_id x := by
    unfold towerFmap
    rw [(transNFun nextStep b i.down (j.down - i.down)).map_id, stageCastHom_id]; rfl
  map_comp g g' := by
    unfold towerFmap
    rw [(transNFun nextStep b i.down (j.down - i.down)).map_comp, stageCastHom_comp]

/-- **The ω-tower as a `CatSystem`** over `ULift.{u} Nat`.  Objects `towerObj`, transitions
    `towerF`/`towerFunctF`; the object coherence `F_refl`/`F_trans` is exactly the difference-cast
    bookkeeping (`transN_zero`/`transN_add`). -/
def towerSystem (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) :
    CatSystem.{u, u} (ULift.{u} Nat) uliftNatDirected where
  A i := towerObj b nextStep i
  catA i := (stageBundle nextStep b i.down).cat
  F hij := towerF b nextStep hij
  functF hij := towerFunctF b nextStep hij
  F_refl {i} x := by
    -- `j = i`, so the difference is `0`, `transN 0 = id`, cast over `i+0=i`.
    show stageCast b nextStep _ (transN nextStep b i.down (i.down - i.down) _) = x
    apply eq_of_heq
    refine (stageCast_heq b nextStep _ _).trans ?_
    rw [Nat.sub_self]; rfl
  F_trans {i j k} hij hjk x := by
    have hij' : i.down ≤ j.down := hij
    have hjk' : j.down ≤ k.down := hjk
    -- `transN i.down (k.down-i.down) = transN (i.down+(j.down-i.down)) (k.down-j.down) ∘ transN …`
    -- with `(j.down-i.down)+(k.down-j.down) = k.down-i.down`.
    show stageCast b nextStep _ (transN nextStep b i.down (k.down - i.down) x) =
      stageCast b nextStep _ (transN nextStep b j.down (k.down - j.down)
        (stageCast b nextStep _ (transN nextStep b i.down (j.down - i.down) x)))
    apply eq_of_heq
    refine (stageCast_heq b nextStep _ _).trans ?_
    -- split the difference additively and discharge casts heterogeneously
    have hsplit : k.down - i.down = (j.down - i.down) + (k.down - j.down) := by omega
    rw [hsplit, transN_add b nextStep i.down (j.down - i.down) (k.down - j.down) x]
    refine (stageCast_heq b nextStep _ _).trans ?_
    -- now match: both run `transN j.down (k.down-j.down)` on transported `transN i.down …`; the
    -- inner `i.down+(j.down-i.down) = j.down`, so the inner cast is heterogeneously transparent.
    refine HEq.symm ((stageCast_heq b nextStep _ _).trans ?_)
    -- congruence under `transN _ (k.down-j.down)` for HEq-equal arguments at carrier-eq stages
    -- (`j.down = i.down + (j.down - i.down)`); the inner cast is HEq-transparent.
    exact transN_congr_heq b nextStep (by omega : j.down = i.down + (j.down - i.down))
      (k.down - j.down) (stageCast_heq b nextStep _ _)

/-- Morphism-level additivity of the difference functor, HEq form.  `(transNFun n (d+e)).map g`
    equals `(transNFun (n+d) e).map ((transNFun n d).map g)` heterogeneously (carriers agree once
    `(n+d)+e = n+(d+e)`).  Proven by induction on `e` from `transN_add`/functoriality. -/
theorem transNFun_map_add (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (n d : Nat) :
    ∀ (e : Nat) {x y : (stageBundle nextStep b n).carrier} (g : x ⟶ y),
      HEq ((transNFun nextStep b n (d + e)).map g)
        ((transNFun nextStep b (n + d) e).map ((transNFun nextStep b n d).map g))
  | 0, x, y, g => by
    -- `transNFun (n+d) 0 = id` functor, `d+0 = d`
    simp only [Nat.add_zero]
    refine HEq.symm ?_
    show HEq ((transNFun nextStep b n d).map g) _
    rfl
  | (e+1), x, y, g => by
    -- `transNFun n (d+(e+1))).map = stageStep-rung.map ∘ (transNFun n (d+e)).map`
    show HEq ((stageStepFun nextStep b (n + (d + e))).map ((transNFun nextStep b n (d + e)).map g)) _
    -- and RHS `transNFun (n+d) (e+1)).map = rung.map ∘ (transNFun (n+d) e).map`
    refine HEq.symm ?_
    show HEq ((stageStepFun nextStep b (n + d + e)).map
      ((transNFun nextStep b (n + d) e).map ((transNFun nextStep b n d).map g))) _
    -- the two rungs are at carrier-equal indices `n+d+e = n+(d+e)`; their `.map` agree on
    -- HEq-equal arguments (`transNFun_map_add` at `e`), with endpoints related by `transN_add_heq`.
    refine (stageStepFun_map_congr_heq nextStep (by omega : n + (d + e) = n + d + e)
      (transN_add_heq b nextStep n d e x) (transN_add_heq b nextStep n d e y)
      (transNFun_map_add nextStep n d e g)).symm

/-- The ω-tower system is `Coherent`: identity transition acts as identity on morphisms,
    composite transitions compose — both via the `stageCastHom`-is-`HEq`-the-original principle
    and the functoriality `transNFun`/`transN_add`. -/
theorem towerCoherent (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) :
    (towerSystem b nextStep).Coherent where
  refl_map {i x x'} g := by
    -- `(functF (refl)).map g = towerFmap (refl) g = stageCastHom (transNFun (i-i)).map g`; with
    -- `i-i=0`, `transNFun 0 = id`, and the cast is `HEq`-trivial.
    show HEq (towerFmap b nextStep _ g) g
    unfold towerFmap
    refine (stageCastHom_heq b nextStep _ _).trans ?_
    rw [Nat.sub_self]; rfl
  trans_map {i j k} hij hjk x x' g := by
    have hij' : i.down ≤ j.down := hij
    have hjk' : j.down ≤ k.down := hjk
    show HEq (towerFmap b nextStep (uliftNatDirected.trans hij hjk) g)
      ((towerFunctF b nextStep hjk).map ((towerFunctF b nextStep hij).map g))
    -- LHS underlying = `(transNFun (k-i)).map g`; RHS underlying =
    -- `(transNFun (k-j)).map ((transNFun (j-i)).map g)`.  Both casts drop via `stageCastHom_heq`.
    unfold towerFmap towerFunctF
    refine (stageCastHom_heq b nextStep _ _).trans ?_
    show HEq ((transNFun nextStep b i.down (k.down - i.down)).map g) _
    refine HEq.symm ((stageCastHom_heq b nextStep _ _).trans ?_)
    show HEq ((transNFun nextStep b j.down (k.down - j.down)).map
      (stageCastHom b nextStep _ ((transNFun nextStep b i.down (j.down - i.down)).map g))) _
    -- the inner `stageCastHom` is `HEq`-transparent; then additivity `(j-i)+(k-j)=k-i`.
    refine HEq.symm ?_
    have hadd : (j.down - i.down) + (k.down - j.down) = k.down - i.down := by omega
    -- rewrite the LHS difference via additivity (carrier `i + (j-i) = j`)
    have key := transNFun_map_add b nextStep i.down (j.down - i.down) (k.down - j.down) g
    rw [hadd] at key
    refine key.trans ?_
    -- now match `(transNFun (i+(j-i)) (k-j)).map ((transNFun (j-i)).map g)` against the RHS, whose
    -- rung is at stage `j.down`; carriers agree (`i+(j-i)=j`) and inner arg is HEq-transparent.
    refine transNFun_map_congr_heq b nextStep (by omega) ?_ ?_ ?_
    · exact (stageCast_heq b nextStep _ _).symm
    · exact (stageCast_heq b nextStep _ _).symm
    · exact (stageCastHom_heq b nextStep _ _).symm

/-- The morphism transport `stageCastHom h` is injective (it is `Eq.rec`, hence an isomorphism). -/
theorem stageCastHom_injective (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) {x y : (stageBundle nextStep b m).carrier} (g g' : x ⟶ y)
    (heq : stageCastHom b nextStep h g = stageCastHom b nextStep h g') : g = g' := by
  subst h; exact heq

/-- The morphism transport `stageCastHom h` reflects isos (it is itself an iso). -/
theorem stageCastHom_isIso_reflects (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) {x y : (stageBundle nextStep b m).carrier} (g : x ⟶ y)
    (hiso : @IsIso _ (stageBundle nextStep b n).cat _ _ (stageCastHom b nextStep h g)) :
    @IsIso _ (stageBundle nextStep b m).cat _ _ g := by subst h; exact hiso

/-- The tower transition `towerFunctF hij` is faithful on morphisms: drop the cast
    (`stageCastHom_injective`), then the iterated functor is faithful (`transNFaithful`). -/
theorem towerHfaith (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    {x y : (towerSystem b nextStep).A i} (p q : x ⟶ y)
    (h : ((towerSystem b nextStep).functF hij).map p = ((towerSystem b nextStep).functF hij).map q) :
    p = q :=
  (transNFaithful nextStep b i.down (j.down - i.down)).1 p q
    (stageCastHom_injective b nextStep _ _ _ h)

/-- The tower transition `towerFunctF hij` is conservative: drop the cast, then the iterated
    functor reflects isos (`transNFaithful`). -/
theorem towerHcons (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    {x y : (towerSystem b nextStep).A i} (φ : x ⟶ y)
    (hiso : @IsIso _ ((towerSystem b nextStep).catA j) _ _ (((towerSystem b nextStep).functF hij).map φ)) :
    @IsIso _ ((towerSystem b nextStep).catA i) _ _ φ :=
  (transNFaithful nextStep b i.down (j.down - i.down)).2 φ
    (stageCastHom_isIso_reflects b nextStep _ _ hiso)

/-- **§1.543 assembly from the tower.**  Given a uniform successor functor `nextStep` (the slice
    successor `(-)*`) and the full `colimitPreRegular` preservation package for the tower it
    generates, *plus* the capital-closure of the tower's colimit, the `CapData A` is assembled
    entirely from the now-built `towerSystem`/`towerCoherent`:
      * `base = id` (stage 0 is `A`), faithful by `idFunctor`/`Faithful.id`;
      * `hfaith`/`hcons` are `towerHfaith`/`towerHcons` (cast-drop + `transNFaithful`);
      * the preservation package and `capital` are passed through verbatim.
    This isolates the two genuine §1.543 walls — the successor `nextStep` and the capital closure
    `hcap` — as the *only* inputs; everything categorical (cast-coherence, faithfulness, colimit
    pre-regularity) is discharged. -/
noncomputable def capData_of_tower (A : Type u) [Cat.{u} A] [PreRegularCategory A]
    (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (hb : b = ⟨A, inferInstance, inferInstance⟩)
    (ht : ∀ i, HasTerminal ((towerSystem b nextStep).A i))
    (htpres : ∀ {i j} (hij : uliftNatDirected.le i j),
      (towerSystem b nextStep).F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts ((towerSystem b nextStep).A i))
    (hppres : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b nextStep).A i)
      (z : (towerSystem b nextStep).A j)
      (uu vv : z ⟶ (towerSystem b nextStep).F hij ((hp i).prod a c)),
      uu ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst =
        vv ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst →
      uu ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd =
        vv ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd → uu = vv)
    (hppres_pair : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b nextStep).A i)
      (z : (towerSystem b nextStep).A j)
      (p : z ⟶ (towerSystem b nextStep).F hij a) (q : z ⟶ (towerSystem b nextStep).F hij c),
      ∃ r : z ⟶ (towerSystem b nextStep).F hij ((hp i).prod a c),
        r ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst = p ∧
        r ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers ((towerSystem b nextStep).A i))
    (hepres : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b nextStep).A i}
      (f g : X ⟶ Y) (z : (towerSystem b nextStep).A j)
      (uu vv : z ⟶ (towerSystem b nextStep).F hij (eqObj f g)),
      uu ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) =
        vv ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) → uu = vv)
    (hepres_lift : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b nextStep).A i}
      (f g : X ⟶ Y) (z : (towerSystem b nextStep).A j) (k : z ⟶ (towerSystem b nextStep).F hij X)
      (_hk : k ≫ ((towerSystem b nextStep).functF hij).map f =
        k ≫ ((towerSystem b nextStep).functF hij).map g),
      ∃ r : z ⟶ (towerSystem b nextStep).F hij (eqObj f g),
        r ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) = k)
    (hcanon : letI : Cat (towerSystem b nextStep).Obj := colimitCat _ (towerCoherent b nextStep)
        letI : HasPullbacks (towerSystem b nextStep).Obj :=
          colimitHasPullbacks _ (towerCoherent b nextStep) ht htpres hp hppres hppres_pair he
            hepres hepres_lift
      ∀ {X Y Z : (towerSystem b nextStep).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
          Cover f → Cover (HasPullbacks.has f g).cone.π₂)
    (hcap : letI : Cat (towerSystem b nextStep).Obj := colimitCat _ (towerCoherent b nextStep)
        letI : PreRegularCategory (towerSystem b nextStep).Obj :=
          colimitPreRegular _ (towerCoherent b nextStep) ht htpres hp hppres hppres_pair he
            hepres hepres_lift hcanon
      Capital (𝒞 := (towerSystem b nextStep).Obj)) :
    CapData.{u} A := by
  -- stage 0 of the tower is `A` (since `b.carrier = A`), so the base embedding is the identity.
  subst hb
  exact
    { ι := ULift.{u} Nat
      D := uliftNatDirected
      C := towerSystem _ nextStep
      hC := towerCoherent _ nextStep
      hne := ⟨⟨0⟩⟩
      i₀ := ⟨0⟩
      base := id
      baseFun := idFunctor
      baseFaithful := ⟨fun _ _ h => h, fun _ h => h⟩
      hfaith := fun {i j} hij {x y} p q h => towerHfaith _ nextStep hij p q h
      hcons := fun {i j} hij {x y} φ hiso => towerHcons _ nextStep hij φ hiso
      ht := ht, htpres := htpres, hp := hp, hppres := hppres, hppres_pair := hppres_pair
      he := he, hepres := hepres, hepres_lift := hepres_lift, hcanon := hcanon, capital := hcap }

/-- **§1.543 — THE REMAINING WALL** (reduced to two sharp sub-obligations).  Every small
    pre-regular category `A` admits capitalization data `CapData A`.

    The categorical assembly is now *complete and sorry-free* (`capData_of_tower`, `towerSystem`,
    `towerCoherent`, the cast-coherence and the faithful-stage packaging).  `capData_exists` is
    reduced to producing the two genuine §1.543 inputs `capData_of_tower` consumes:

      1. `hstep`  — a *uniform pre-regular-preserving successor* `nextStep : ∀ S, CapStep S` whose
         generated tower carries the full `colimitPreRegular` preservation package
         (`ht`/`htpres`/`hp`/`hppres`/…/`hcanon`).  This is the §1.544/§1.545 slice successor
         `A ↦ A/B`, now buildable from `overPreRegular` (slice pre-regularity) + the §1.544
         separation; lifting its single-step preservation to arbitrary `i ≤ j` (composing rungs)
         supplies the package.
      2. `hcap`   — the colimit of that tower is **capital** (§1.543 fixpoint: every
         well-supported object appears at a finite stage `n`, gets a point at `n+1`, and the point
         survives by cover reflection `colimHom_cover_reflects`/`homInclObj_cover_reflects`).

    These two are the *only* residue, and are now SPLIT into two separately-stated `sorry`s with
    their dependency exposed: `hwall_step` (the successor + full preservation package) and, after
    `obtain`ing it and introducing the colimit's pre-regular instance, `hcap` (the capital closure
    stated *over* that instance — it genuinely consumes `hwall_step`, hence the nesting). -/
theorem capData_exists (A : Type u) [Cat.{u} A] [PreRegularCategory A] :
    Nonempty (CapData.{u} A) := by
  -- The two genuine §1.543 walls, now SEPARATED into two named sub-obligations with the
  -- dependency between them made explicit (the capital closure is stated *over* the colimit
  -- pre-regular structure that the successor's preservation package supplies):
  --
  --   WALL 1  `hwall_step` — the uniform pre-regular-preserving SUCCESSOR.  Produces a
  --     `nextStep : ∀ S, CapStep S.carrier` (Freyd's relative capitalization `A ↦ A*`, the
  --     gluing/colimit of slices `A/B` over well-supported `B`, which ADDS a point per
  --     well-supported object) *together with* the full `colimitPreRegular` preservation
  --     package for the ω-tower it generates (terminal / products / equalizers / pullback-covers
  --     preserved, lifted from the single-step preservation by rung composition).
  --
  --   WALL 2  `hwall_cap` — the CAPITAL CLOSURE (§1.543 fixpoint).  *Given* the successor and
  --     its package (so the colimit `Ā` is a concrete pre-regular category), every well-supported
  --     object of `Ā` is well-pointed.  Proved by: each well-supported object appears at a finite
  --     stage `n`, the successor `nextStep` puts a point on it at stage `n+1`, and the point
  --     survives the colimit by cover reflection (`colimHom_cover_reflects` /
  --     `homInclObj_cover_reflects`).  This OBLIGATION CONSUMES the package from WALL 1 — it is
  --     not independent of it, which is why both walls were originally bundled into one `sorry`.
  --
  -- `hwall` re-bundles the two for `capData_of_tower`; the split below is the real reduction.
  have hwall_step :
      ∃ (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
        (b : PreRegBundle.{u}) (hb : b = ⟨A, inferInstance, inferInstance⟩)
        (ht : ∀ i, HasTerminal ((towerSystem b nextStep).A i))
        (htpres : ∀ {i j} (hij : uliftNatDirected.le i j),
          (towerSystem b nextStep).F hij (ht i).one = (ht j).one)
        (hp : ∀ i, HasBinaryProducts ((towerSystem b nextStep).A i))
        (hppres : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b nextStep).A i)
          (z : (towerSystem b nextStep).A j)
          (uu vv : z ⟶ (towerSystem b nextStep).F hij ((hp i).prod a c)),
          uu ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst =
            vv ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst →
          uu ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd =
            vv ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd → uu = vv)
        (hppres_pair : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b nextStep).A i)
          (z : (towerSystem b nextStep).A j)
          (p : z ⟶ (towerSystem b nextStep).F hij a) (q : z ⟶ (towerSystem b nextStep).F hij c),
          ∃ r : z ⟶ (towerSystem b nextStep).F hij ((hp i).prod a c),
            r ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst = p ∧
            r ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd = q)
        (he : ∀ i, HasEqualizers ((towerSystem b nextStep).A i))
        (hepres : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b nextStep).A i}
          (f g : X ⟶ Y) (z : (towerSystem b nextStep).A j)
          (uu vv : z ⟶ (towerSystem b nextStep).F hij (eqObj f g)),
          uu ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) =
            vv ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) → uu = vv)
        (hepres_lift : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b nextStep).A i}
          (f g : X ⟶ Y) (z : (towerSystem b nextStep).A j) (k : z ⟶ (towerSystem b nextStep).F hij X)
          (_hk : k ≫ ((towerSystem b nextStep).functF hij).map f =
            k ≫ ((towerSystem b nextStep).functF hij).map g),
          ∃ r : z ⟶ (towerSystem b nextStep).F hij (eqObj f g),
            r ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) = k),
        letI : Cat (towerSystem b nextStep).Obj := colimitCat _ (towerCoherent b nextStep)
        letI : HasPullbacks (towerSystem b nextStep).Obj :=
          colimitHasPullbacks _ (towerCoherent b nextStep) ht htpres hp hppres hppres_pair he
            hepres hepres_lift
        ∀ {X Y Z : (towerSystem b nextStep).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
            Cover f → Cover (HasPullbacks.has f g).cone.π₂ := by
    -- WALL 1.  Build the uniform pre-regular-preserving successor `nextStep : ∀ S, CapStep S.carrier`
    -- (Freyd's `A ↦ A*`: glue the slices `A/B` over well-supported `B`, adding a point per
    -- well-supported object) and supply the ω-tower's preservation package by rung-composing the
    -- single-step preservation.
    --
    -- THE PER-`B` SLICE RUNG IS NOW BUILT, sorry-free, in `Fredy.RelativeCapitalization`
    -- (§1.544/§1.545): `Freyd.sliceCapStep B hws : CapStep S` is the faithful pre-regular embedding
    -- `S → S/B` for a single well-supported `B` (`overPreRegular` gives `S/B` pre-regular;
    -- `sliceEmbedFaithful` proves faithfulness — embedding via `slice_embedding_separates`,
    -- reflects-iso via `f×B` iso ⟹ `f` mono+cover ⟹ iso), and `sliceAcquiresPoint` exhibits the
    -- §1.546 generic point `1 → S(B)` that this rung adds.
    --
    -- RESIDUAL (the genuine wall): the successor `nextStep` must be UNIFORM over `S` and add a point
    -- for *every* well-supported `B` of `S` in ONE category `S*` (Freyd's §1.547 rational category /
    -- the directed union of the per-`B` slice rungs `sliceCapStep`), *plus* the lift of the per-rung
    -- preservation to the iterated `colimitPreRegular` package.  Picking a single `B` here would not
    -- satisfy WALL 2 (capital closure needs a point for *all* well-supported objects), so this is left
    -- as the honest residual rather than reduced via an arbitrary `sliceCapStep B`.
    --
    -- §1.547 CONSTRUCTION (the path the residual must follow — *not* reducible to `sliceCapStep B`).
    -- The per-`S` inner directed system is indexed by FINITE SETS `U` of well-supported objects of
    -- `S`, ordered by inclusion.  This index is NOW BUILT, sorry-free, in `Fredy.RelativeCapitalization`:
    --   * `Freyd.listDirected     : Directed (List S)`  — finite sets = `List S`, `⊆` order, bound = `++`.
    --   * `Freyd.listProd U       : S`                  — the product `∏U` (right-folded `prod`, `∏[]=1`).
    --   * `Freyd.listProdProj U k : ∏U ⟶ U.get k`       — the projection onto the factor at index `k`
    --       (FORCED to be `Fin`-indexed, not `B ∈ U`-indexed: `B ∈ U : Prop`, and a *morphism*
    --        `∏U → B` cannot be large-eliminated out of a `Prop`).
    --   * `Freyd.listProdSliceAcquiresEveryFactor U k`  — the §1.547 payoff: `S/(∏U)` acquires a point
    --       of EVERY factor `U.get k` at once (one rung points all of `U`); a direct instance of
    --       `sliceAcquiresFactorPoint` along `listProdProj` (`prodSliceAcquiresBothFactors` = 2-factor).
    -- The rung at `U` is the slice `S/(∏U)` (pre-regular by `overPreRegular`).  `S*` is the colimit
    -- `CatSystem.Obj` of this inner system, pre-regular by `colimitPreRegular`, faithful over `S`.
    --
    -- PROGRESS (this session): the base-change TRANSITION FUNCTOR now EXISTS and the inner
    -- finite-product-slice `CatSystem` SKELETON is assembled in `Fredy.RelativeCapitalization`:
    --   * `Freyd.baseChangeFunctor (g : C ⟶ D) : Functor (Over D → Over C)` (SliceRegular.lean) —
    --     the genuine slice→slice transition `S/(∏V) → S/(∏U)` by pullback along `∏U → ∏V`.
    --   * `Freyd.innerObj U = Over (listProd U)`, `Freyd.innerCat`, `Freyd.innerF`/`innerFunctF`,
    --     and `Freyd.innerCatSystem (P : ListProjFamily) : CatSystem (List S) listDirected` —
    --     the inner system over `listDirected`, objects/Cat/transition-object-map/per-rung
    --     functoriality all sorry-free; only the two strict `CatSystem` fields remain (below).
    --
    -- WHY STILL A SORRY — now reduced to THREE sharp, isolated residuals (the index, objects,
    -- transition functor, and per-rung points are all DONE sorry-free):
    --   (A)  THE CHOICE-FREE TRANSITION BASE MORPHISM — the data of `Freyd.ListProjFamily`:
    --        a projection `listProd U ⟶ listProd V` per `V ⊆ U`, strictly coherent.  Not yet
    --        constructible: `listSubset V U = ∀ x∈V, x∈U` is a `Prop`, so a positional
    --        factor-match cannot be large-eliminated into a morphism without `DecidableEq S`
    --        (same wall that forced `listProdProj` to be `Fin`-indexed).  Abstracted as data;
    --        one constructive instance closes (A).
    --   (B-strict)  BASE-CHANGE IS ONLY PSEUDO-FUNCTORIAL — `Freyd.StrictBaseChange` (the strict
    --        `F_refl`/`F_trans` for `innerCatSystem`).  `baseChangeObj (Cat.id) X = X` and the
    --        composite law hold only up to canonical pullback iso, never on the nose (probed), so the
    --        strict `CatSystem` laws need base-change strictification.
    --        ROUTE-1 (strict reindexing) — SETTLED NEGATIVELY (see `Freyd.strictReindexSystem` /
    --        `Freyd.reindexFunctor`): the strict Σ / post-composition transition `A/C → A/D` along a
    --        fixed `m : C → D` IS strictly functorial and discharges `F_refl`/`F_trans` ON THE NOSE
    --        (`reindexObj_id`/`reindexObj_comp`, axiom-free), giving a genuine hypothesis-free
    --        `CatSystem`.  But it has the WRONG variance for §1.547 (needs `∏V → ∏U` for `V ⊆ U`, not
    --        choice-free — it would manufacture the new factors' points) AND keeps the slice domain
    --        FIXED (`B×∏V`), so it cannot connect the stage embeddings whose domain must GROW to
    --        `B×∏U`.  Only base-change grows the domain, hence is irreducibly pseudo-functorial.  So
    --        route 1 does NOT close this; the residual stays base-change strictification (or a literal
    --        directed-union-of-full-subcategories rational-category model with strict inclusions).
    --   (B-package)  THE INNER `colimitPreRegular` PACKAGE — `Coherent` plus the 9 preservation
    --        hypotheses and `hcanon` for `innerCatSystem`, mirroring `towerCoherent`/
    --        `capData_of_tower`; a full second copy of the outer assembly over `listDirected`.
    --   (B-import)  THE ASSEMBLY CANNOT LIVE HERE — `RelativeCapitalization` imports
    --        `Capitalization` (for `CapStep`), so `innerCatSystem`/`listDirected`/… are downstream
    --        of this `sorry`.  Discharging `hwall_step` in place needs the inner-system ingredients
    --        moved up into a file `Capitalization` imports (e.g. `SliceRegular`), or `capData_exists`
    --        relocated downstream.  Hence `hwall_step` stays a documented `sorry` pointing at the
    --        `Freyd.innerCatSystem` block; the residual is (A)+(B-strict)+(B-package)+(B-import).
    sorry
  -- Unpack the successor and its full preservation package (the §1.543 "directed-tower" data).
  obtain ⟨nextStep, b, hb, ht, htpres, hp, hppres, hppres_pair, he, hepres, hepres_lift,
    hcanon⟩ := hwall_step
  -- Now the colimit `Ā = (towerSystem b nextStep).Obj` is a concrete pre-regular category
  -- (instances below are exactly the ones `colimitPreRegular` / `capData_of_tower` use).
  letI : Cat (towerSystem b nextStep).Obj := colimitCat _ (towerCoherent b nextStep)
  letI : PreRegularCategory (towerSystem b nextStep).Obj :=
    colimitPreRegular _ (towerCoherent b nextStep) ht htpres hp hppres hppres_pair he
      hepres hepres_lift hcanon
  -- WALL 2.  CAPITAL CLOSURE of the colimit, consuming the package above.  Every well-supported
  -- object of `Ā` is well-pointed: it appears at a finite stage `n`, the successor `nextStep`
  -- (WALL 1) puts a point on it at stage `n+1`, and the point survives to the colimit because
  -- the stage inclusion REFLECTS covers (`colimHom_cover_reflects` / `homInclObj_cover_reflects`,
  -- both available).  RESIDUAL: the fixpoint argument that the finite-stage point witnesses
  -- well-pointedness in `Ā`.  This depends essentially on WALL 1's successor, hence the nesting.
  have hcap : Capital (𝒞 := (towerSystem b nextStep).Obj) := by
    sorry
  exact ⟨capData_of_tower A nextStep b hb ht htpres hp hppres hppres_pair he hepres hepres_lift
    hcanon hcap⟩

/-- **§1.543 Capitalization Lemma** (small case, object universe = morphism universe).
    Every small pre-regular category `A` admits a faithful representation into a capital
    pre-regular category `Ā`.  Reduced to `capData_exists` (the transfinite construction)
    via `capitalization_of_capData` (the colimit packaging, proven above). -/
theorem capitalization_lemma_small (A : Type u) [Cat.{u} A] [PreRegularCategory A] :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hP : PreRegularCategory Ā),
      @Capital.{u, u} Ā hC (hP.toHasTerminal) ∧
      ∃ (F : A → Ā) (hF : Functor F), @Faithful.{u, u} A _ Ā hC F hF :=
  (capData_exists A).elim (fun cd => capitalization_of_capData cd)

end Freyd
