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

  STATUS.  The glue that is genuinely derivable from the existing machinery is
  proved sorry-free:

    * `faithful_comp`           — faithful functors compose to faithful functors.
    * `colimInclFaithful`       — the colimit stage-inclusion `A i → Ā` is faithful,
      given that every transition functor is faithful (via `homInclObj_injective`
      and `homInclObj_consIso`).

  The remaining content — building the ordinal-indexed `CatSystem` whose limit
  stages are the colimits of their predecessors, and the capital fixpoint argument
  — is isolated into the *sharp* sorries documented at `capitalization_system` and
  `capitalization_lemma`.  Each blocker is named with its precise missing
  ingredient.
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

/-- **§1.543 — THE REMAINING WALL.**  Every small pre-regular category `A` admits
    capitalization data `CapData A`.

    *Scaffolding now in hand* (all sorry-free, above): the directed index `uliftNatDirected`;
    the single-step interface `CapStep`; the stage recursion `stageBundle`; the iterated
    transition `transN` with its functoriality `transNFun` and **faithfulness** `transNFaithful`
    (so `hfaith`/`hcons` of `CapData` are discharged once the system is assembled).

    *Residual* (the genuine transfinite construction):
      1. assemble `stageBundle`/`transN` into a `CatSystem (ULift Nat) uliftNatDirected` — the
         cast-coherence turning the difference-recursion transition into a `≤`-indexed `F`, plus
         `Coherent` (`refl_map`/`trans_map`);
      2. lift the single-step preservation carried by each `CapStep` (terminal/products/
         equalizers/cover-pullbacks) to arbitrary `i ≤ j`, supplying the `colimitPreRegular`
         package;
      3. the §1.543 capital-closure of the colimit — every well-supported object appears at a
         finite stage `n`, gets a point at `n+1`, and the point survives by cover reflection
         (`colimHom_cover_reflects`, `homInclObj_cover_reflects`, already proven in
         `CatColimitRegular`); plus the start `nextStep` itself, whose existence needs
         `PreRegularCategory (Over B)` for the slice successor (a parallel obligation).

    None of (1)–(3) is a one-lemma gap.  The colimit-side packaging (`capitalization_of_capData`,
    `stageInclFaithful`) is already in hand. -/
theorem capData_exists (A : Type u) [Cat.{u} A] [PreRegularCategory A] :
    Nonempty (CapData.{u} A) := by
  sorry

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
