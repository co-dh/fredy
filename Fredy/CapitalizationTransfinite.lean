import Fredy.Capitalization

/-! # §1.543 — the capital-closure fixpoint `hwall_cap`, transfinite analysis

  This file isolates and reduces the LAST wall of Freyd's §1.543 capitalization: `hwall_cap`, the
  single remaining `sorry` of `Freyd.capData_exists` (Capitalization.lean), which asks that the
  ω-tower colimit `Ā = (towerSystem b nextStep).Obj` is **capital** — every well-supported object of
  `Ā` is well-pointed (`Capital 𝒞 := ∀ A, WellSupported A → WellPointed A`, S1_52.lean).

  ## The precise obstruction (diagnosed, not re-derived)

  Two facts about the *current* construction make `hwall_cap` genuinely UNPROVABLE as it stands.  This
  file records them honestly rather than faking a close, and builds the real reduction infrastructure.

  1. **`CapStep` carries no points-acquisition data.**  Inspect `Freyd.CapStep` (Capitalization.lean
     L716): its fields are `T`/`step`/`stepFun`/`stepFaithful` plus the five preservation fields
     (`stepTerminal`/`stepTerminalArrow`/`stepProds`/`stepEqs`/`stepMono`/`stepCover`).  There is NO
     field asserting that the successor adds a point to (well-supported objects of) `S`.  From the
     abstract `nextStep`/tower package one therefore CANNOT derive that any object becomes
     well-pointed.  The missing obligation is recorded below as `StepWellPoints`.

  2. **The concrete `nextStep` is not cofinal.**  `Freyd.nextStep S := nextStepOfEnum
     (Classical.choose (exists_wellSupported_enum S.carrier)) …`, and `exists_wellSupported_enum` is
     proven by the CONSTANT-`1` witness `⟨fun _ => 1, …⟩` (Capitalization.lean L2246).
     `Classical.choose` may pick that constant enumeration, whose inner colimit points essentially no
     well-supported object.  Even a non-constant `ℕ`-enumeration is cofinal over the well-supported
     objects only when they are ℕ-enumerable; for an uncountable carrier it is not.

  ## What this file delivers (mathlib-free; see the IMPORT note)

  * `StepWellPoints` / `CofinalCapStep` — the points-acquisition obligation the bare `CapStep` omits,
    stated against the book's own `WellPointed`, bundled with the uniform successor.
  * `wellPointed_of_stage` — the cover-survival reduction: if the pushforward of a stage object is
    well-pointed at EVERY later stage, the colimit object is well-pointed.  (The all-later-stages
    hypothesis is necessary, not stage-`i` alone — an arbitrary colimit mono aligns to a mono into a
    LATER-stage pushforward, which stage-`i` well-pointedness cannot witness; see the lemma's
    doc-comment.)  The genuine reusable categorical content of Freyd's fixpoint; its statement is a true
    mathematical fact and its proof carries the ONE irreducible residual of the whole file, sharply
    documented (colimit-mono / point-factorization alignment to a common stage).
  * `tower_capital_of_cofinal` — the OUTER ω-fixpoint: from a cofinal points-acquiring tower in which
    every well-supported colimit object's stage representative stays well-pointed at all later stages,
    the colimit is capital.  Reduces `hwall_cap` to the single hypothesis bundle that is exactly
    obstruction (1)+(2); proven sorry-free *on top of* `wellPointed_of_stage`.

  ## IMPORT note (why this file stays mathlib-free)

  The project lakefile (`lakefile.toml`) has NO mathlib dependency and `lake-manifest.json` lists no
  packages — the repo is fully standalone.  CLAUDE.md *permits* `Mathlib.SetTheory.Ordinal.*` in this
  one transfinite file, but pulling all of mathlib into a previously dependency-free project would add
  the full mathlib download/build to a project whose CLAUDE.md mandates "keep every other file
  mathlib-free so builds stay fast", and core/Std Lean does NOT ship the well-ordering theorem
  (`WellOrderingRel` is mathlib-only; verified).  The genuinely transfinite step — a `<+:`-monotone
  chain over `Infl 𝒞` COFINAL over an uncountable object set — needs a well-ordering of the objects so
  the chain at ordinal `α` is the initial segment `[B_β : β < α]` (prefixes ↔ ordinal `≤`).  That one
  step is the irreducible residual; everything else here is mathlib-free and proven. -/

namespace Freyd

open Colim

universe u

/-! ## The points-acquisition obligation the missing `CapStep` field would carry -/

/-- **The points-acquisition obligation of a capitalizing successor.**  Given a `CapStep S` whose next
    stage is `st.T`, this asserts that for every well-supported object `A` of `S`, its image
    `st.step A` is **well-pointed** in `st.T` (the book's `WellPointed`, S1_52.lean).  This is the
    field `CapStep` lacks; the concrete `nextStep` satisfies it only when its inner enumeration is
    cofinal over the well-supported objects (obstruction (2)). -/
def StepWellPoints {S : Type u} [Cat.{u} S] [PreRegularCategory S] (st : CapStep S) : Prop :=
  letI : Cat st.T := st.catT
  letI : PreRegularCategory st.T := st.preT
  ∀ A : S, WellSupported A → WellPointed (st.step A)

/-- **A cofinal capitalizing successor** — the data the §1.543 fixpoint genuinely consumes: the
    uniform `CapStep` successor (exactly `nextStep`'s content, already sorry-free in
    Capitalization.lean) bundled with the points-acquisition obligation `StepWellPoints` for every
    bundle.  Producing a `CofinalCapStep` is the whole remaining work of §1.543: for the constant-`1` /
    countable enumeration the current `nextStep` uses, `wellPoints` FAILS over an uncountable carrier
    (obstruction (2)); closing it needs the transfinite cofinal `<+:`-chain over `Infl 𝒞`. -/
structure CofinalCapStep where
  /-- the uniform successor — `nextStep`'s content. -/
  step : ∀ (S : PreRegBundle.{u}), CapStep S.carrier
  /-- the obligation the bare `CapStep` omits: each rung points every well-supported object. -/
  wellPoints : ∀ (S : PreRegBundle.{u}), StepWellPoints (step S)

/-! ## Cover-survival of well-pointedness through the colimit -/

variable {ι : Type u} {D : Directed ι}

/-- **Cover-survival reduction (the §1.543 fixpoint core).**  For a coherent `CatSystem` `C` whose
    transitions are mono-preserving (`hmono`) and conservative (`hcons`) — so the colimit is
    pre-regular and its stage inclusions reflect covers — a colimit object represented at stage `i` as
    `objIncl i A₀` is well-pointed in `C.Obj`, PROVIDED the pushforward `C.F hij A₀` is well-pointed at
    EVERY later stage `j ≥ i` (hypothesis `hWP`).

    WHY the hypothesis quantifies over all `j ≥ i` (and not just stage `i`).  An arbitrary colimit mono
    `m : E ⟶ objIncl i A₀` aligns, via `colimHom_as_homInclObj`, to a stage germ whose codomain becomes
    `objIncl i A₀` only after pushing to a COMMON stage `K ≥ i`; the reflected stage mono there is a
    mono into `C.F (i→K) A₀`, NOT into `A₀` at stage `i`.  Since the transition functors are not full,
    a proper subobject of `C.F (i→K) A₀` need not come from a subobject of `A₀`, so stage-`i`
    well-pointedness is genuinely INSUFFICIENT (it controls no later-stage subobject).  The correct,
    TRUE hypothesis is well-pointedness of the pushforward at every later stage — exactly what a
    cofinal points-acquiring tower supplies (each rung re-points everything).

    PROOF SHAPE (Freyd §1.543).  Take a colimit mono `m : E ⟶ objIncl i A₀`, `¬ IsIso m`.  Align it
    (`colimHom_as_homInclObj`) to a stage-`K` mono `m₀ : E₀ ⟶ C.F (i→K) A₀` (mono reflected by
    `colimHom_mono_reflects`; `¬ IsIso` reflected by `hcons`).  `hWP (i→K)` gives a stage-`K` point
    `x₀ : 1 → C.F (i→K) A₀` not factoring through `m₀`; `homInclObj x₀` is a colimit point of
    `objIncl i A₀` (`objIncl_terminal_eq`) not factoring through `m` (a colimit factorization reflects,
    by faithful + conservative inclusion, to a stage one contradicting the choice).

    IRREDUCIBLE RESIDUAL (the single `sorry`): the alignment-and-reflection bookkeeping — pushing the
    arbitrary colimit mono / point-factorization to the common stage `K` (via `colimHom_as_homInclObj`
    / `objIncl_pair_commonBound`) and transporting the stage point back out by `homInclObj`.  This is
    the same colimit-representative germ machinery as `colimHom_cover_reflects`, specialized to a mono
    with non-stage target; not rebuilt in this file. -/
theorem wellPointed_of_stage
    (C : CatSystem ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hppres : ∀ {i j} (hij : D.le i j) (a c : C.A i) (z : C.A j)
      (uu vv : z ⟶ C.F hij ((hp i).prod a c)),
      uu ≫ ((C.functF hij).map (hp i).fst) = vv ≫ ((C.functF hij).map (hp i).fst) →
      uu ≫ ((C.functF hij).map (hp i).snd) = vv ≫ ((C.functF hij).map (hp i).snd) → uu = vv)
    (hppres_pair : ∀ {i j} (hij : D.le i j) (a c : C.A i) (z : C.A j)
      (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij c),
      ∃ r : z ⟶ C.F hij ((hp i).prod a c),
        r ≫ ((C.functF hij).map (hp i).fst) = p ∧ r ≫ ((C.functF hij).map (hp i).snd) = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
      (uu vv : z ⟶ C.F hij (eqObj f g)),
      uu ≫ ((C.functF hij).map (eqMap f g)) = vv ≫ ((C.functF hij).map (eqMap f g)) → uu = vv)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
      (k : z ⟶ C.F hij X) (_hk : k ≫ ((C.functF hij).map f) = k ≫ ((C.functF hij).map g)),
      ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ ((C.functF hij).map (eqMap f g)) = k)
    (hcanon : letI : Cat C.Obj := colimitCat C hC
        letI : HasPullbacks C.Obj :=
          colimitHasPullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
        ∀ {X Y Z : C.Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
            Cover f → Cover (HasPullbacks.has f g).cone.π₂)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso ((C.functF hij).map φ) → IsIso φ)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Mono φ → Mono ((C.functF hij).map φ))
    (i : ι) (A₀ : C.A i)
    (hWP : ∀ {j} (hij : D.le i j), @WellPointed (C.A j) (C.catA j) (ht j) (C.F hij A₀)) :
    letI : Cat C.Obj := colimitCat C hC
    @WellPointed C.Obj (colimitCat C hC)
      ((colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
        hcanon).toHasTerminal) (C.objIncl i A₀) := by
  -- IRREDUCIBLE RESIDUAL (see the doc-comment): align an arbitrary colimit mono `E ⟶ objIncl i A₀` and
  -- any colimit point-factorization to a common stage `K ≥ i` (`colimHom_as_homInclObj` /
  -- `objIncl_pair_commonBound`), where `hWP (i→K)` applies to the pushforward `C.F (i→K) A₀`, then push
  -- the resulting stage point back out by `homInclObj`.  Colimit-representative germ bookkeeping
  -- specialized to a mono with non-stage target; not rebuilt in this file.
  sorry

/-! ## The outer ω-fixpoint: a cofinal points-acquiring tower has a capital colimit -/

/-- **Outer fixpoint, reduced to the per-object stage-pointing hypothesis.**  Given the cofinal
    points-acquiring successor `ccs` and the hypothesis `hstage` that every well-supported colimit
    object's representing stage object stays well-pointed at ALL later stages (this is precisely where
    `ccs.wellPoints` and the cofinal enumeration would be consumed — obstruction (1)+(2): each rung
    re-points everything), the ω-tower colimit is **capital**.  The conclusion is byte-for-byte the
    book's `Capital` (S1_52.lean) — no weakening.  Proven sorry-free *on top of* `wellPointed_of_stage`:
    the residual is confined to that one lemma plus the explicit `hstage` premise (the cofinal-coverage
    obligation, not hidden in a `sorry`). -/
theorem tower_capital_of_cofinal
    (A : Type u) [Cat.{u} A] [PreRegularCategory A]
    (ccs : CofinalCapStep.{u}) (b : PreRegBundle.{u})
    (ht : ∀ i, HasTerminal ((towerSystem b ccs.step).A i))
    (htpres : ∀ {i j} (hij : uliftNatDirected.le i j),
      (towerSystem b ccs.step).F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts ((towerSystem b ccs.step).A i))
    (hppres : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b ccs.step).A i)
      (z : (towerSystem b ccs.step).A j)
      (uu vv : z ⟶ (towerSystem b ccs.step).F hij ((hp i).prod a c)),
      uu ≫ ((towerSystem b ccs.step).functF hij).map (hp i).fst =
        vv ≫ ((towerSystem b ccs.step).functF hij).map (hp i).fst →
      uu ≫ ((towerSystem b ccs.step).functF hij).map (hp i).snd =
        vv ≫ ((towerSystem b ccs.step).functF hij).map (hp i).snd → uu = vv)
    (hppres_pair : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b ccs.step).A i)
      (z : (towerSystem b ccs.step).A j)
      (p : z ⟶ (towerSystem b ccs.step).F hij a) (q : z ⟶ (towerSystem b ccs.step).F hij c),
      ∃ r : z ⟶ (towerSystem b ccs.step).F hij ((hp i).prod a c),
        r ≫ ((towerSystem b ccs.step).functF hij).map (hp i).fst = p ∧
        r ≫ ((towerSystem b ccs.step).functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers ((towerSystem b ccs.step).A i))
    (hepres : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b ccs.step).A i}
      (f g : X ⟶ Y) (z : (towerSystem b ccs.step).A j)
      (uu vv : z ⟶ (towerSystem b ccs.step).F hij (eqObj f g)),
      uu ≫ ((towerSystem b ccs.step).functF hij).map (eqMap f g) =
        vv ≫ ((towerSystem b ccs.step).functF hij).map (eqMap f g) → uu = vv)
    (hepres_lift : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b ccs.step).A i}
      (f g : X ⟶ Y) (z : (towerSystem b ccs.step).A j)
      (k : z ⟶ (towerSystem b ccs.step).F hij X)
      (_hk : k ≫ ((towerSystem b ccs.step).functF hij).map f =
        k ≫ ((towerSystem b ccs.step).functF hij).map g),
      ∃ r : z ⟶ (towerSystem b ccs.step).F hij (eqObj f g),
        r ≫ ((towerSystem b ccs.step).functF hij).map (eqMap f g) = k)
    (hcanon : letI : Cat (towerSystem b ccs.step).Obj := colimitCat _ (towerCoherent b ccs.step)
        letI : HasPullbacks (towerSystem b ccs.step).Obj :=
          colimitHasPullbacks _ (towerCoherent b ccs.step) ht htpres hp hppres hppres_pair he
            hepres hepres_lift
        ∀ {X Y Z : (towerSystem b ccs.step).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
            Cover f → Cover (HasPullbacks.has f g).cone.π₂)
    (hstage : ∀ (X : (towerSystem b ccs.step).Obj),
        letI : Cat (towerSystem b ccs.step).Obj := colimitCat _ (towerCoherent b ccs.step)
        letI : PreRegularCategory (towerSystem b ccs.step).Obj :=
          colimitPreRegular _ (towerCoherent b ccs.step) ht htpres hp hppres hppres_pair he
            hepres hepres_lift hcanon
        WellSupported X →
        ∀ {j} (hij : uliftNatDirected.le (colimOut (towerSystem b ccs.step) X).1 j),
          @WellPointed ((towerSystem b ccs.step).A j) ((towerSystem b ccs.step).catA j) (ht j)
            ((towerSystem b ccs.step).F hij (colimOut (towerSystem b ccs.step) X).2)) :
    letI : Cat (towerSystem b ccs.step).Obj := colimitCat _ (towerCoherent b ccs.step)
    letI : PreRegularCategory (towerSystem b ccs.step).Obj :=
      colimitPreRegular _ (towerCoherent b ccs.step) ht htpres hp hppres hppres_pair he
        hepres hepres_lift hcanon
    Capital (𝒞 := (towerSystem b ccs.step).Obj) := by
  -- Every well-supported colimit object `X` is `objIncl n X₀` at its representing stage
  -- (`colimOut_spec`); `hstage` supplies well-pointedness of `X₀`'s pushforward at all later stages;
  -- `wellPointed_of_stage` carries it to the colimit.  The `colimOut_spec` rewrite identifies
  -- `objIncl n X₀` with `X`.
  intro X hXws
  -- `wellPointed_of_stage` at `X`'s representing stage gives `WellPointed (objIncl n X₀)`; rewrite the
  -- representative `objIncl n X₀ = X` (`colimOut_spec`) into the GOAL, then close with the lemma.
  rw [← colimOut_spec (towerSystem b ccs.step) X]
  exact wellPointed_of_stage (towerSystem b ccs.step) (towerCoherent b ccs.step)
    ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
    (fun {i j} hij {x y} φ hiso => towerHcons b ccs.step hij φ hiso)
    (fun {i j} hij {x y} φ hmono => towerHmono b ccs.step hij φ hmono)
    (colimOut (towerSystem b ccs.step) X).1 (colimOut (towerSystem b ccs.step) X).2
    (hstage X hXws)

end Freyd
