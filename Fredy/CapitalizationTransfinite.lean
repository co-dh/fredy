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

/-- **A map factors through a mono iff the pullback leg over it is an isomorphism.**
    Pure category theory.  For a pullback cone `c` of the cospan `(f : A ⟶ C, g : B ⟶ C)` with
    `f` MONIC, `g` factors through `f` (`∃ y, y ≫ f = g`) iff `c.π₂` (the leg over `g`) is an
    isomorphism.  Forward: a factor `y` makes `(y, 1_B) : B → c.pt` a section of `c.π₂`, and since
    `f` mono forces `c.π₂` mono (pullback of a mono is mono), a split-mono section makes `c.π₂` iso.
    Backward: `y := c.π₂⁻¹ ≫ c.π₁` factors `g` (using the square `c.w` and `π₂⁻¹ ≫ π₂ = 1`). -/
theorem factor_iff_pullback_π₂_iso {𝒞 : Type u} [Cat.{u} 𝒞] {A B C : 𝒞}
    {f : A ⟶ C} {g : B ⟶ C} (hf : Mono f) (c : Cone f g) (hpb : c.IsPullback) :
    (∃ y : B ⟶ A, y ≫ f = g) ↔ IsIso c.π₂ := by
  constructor
  · rintro ⟨y, hy⟩
    -- `(y, 1_B)` is a cone over `(f, g)`; its lift `s : B → c.pt` is a section of `c.π₂`.
    obtain ⟨s, ⟨hs₁, hs₂⟩, _⟩ := hpb ⟨B, y, Cat.id B, by rw [hy, Cat.id_comp]⟩
    -- `c.π₂` is monic: pullback of the mono `f`.  `u ≫ π₂ = v ≫ π₂` and the square give
    -- `u ≫ π₁ = v ≫ π₁` (cancel `f`), so `u = v` by the pullback's uniqueness.
    have hπ₂mono : Mono c.π₂ := by
      intro W u v huv
      have h₁ : u ≫ c.π₁ = v ≫ c.π₁ := by
        apply hf
        rw [Cat.assoc, c.w, ← Cat.assoc, huv, Cat.assoc, ← c.w, Cat.assoc]
      obtain ⟨_, _, huniq⟩ := hpb ⟨W, u ≫ c.π₁, u ≫ c.π₂, by rw [Cat.assoc, c.w, Cat.assoc]⟩
      rw [huniq u rfl rfl, huniq v h₁.symm huv.symm]
    -- `s ≫ c.π₂ = 1_B` (`hs₂`), so `c.π₂` is split mono; a monic split mono is iso.
    refine ⟨s, ?_, hs₂⟩
    -- `c.π₂ ≫ s = 1` from `(c.π₂ ≫ s) ≫ c.π₂ = c.π₂ = 1 ≫ c.π₂` and `c.π₂` mono.
    exact hπ₂mono _ _ (by rw [Cat.assoc, hs₂, Cat.comp_id, Cat.id_comp])
  · rintro ⟨inv, hinv₁, hinv₂⟩
    -- `y := inv ≫ c.π₁` factors `g`: `y ≫ f = inv ≫ (π₁ ≫ f) = inv ≫ (π₂ ≫ g) = (inv ≫ π₂) ≫ g = g`.
    exact ⟨inv ≫ c.π₁, by rw [Cat.assoc, c.w, ← Cat.assoc, hinv₂, Cat.id_comp]⟩

variable {ι : Type u} {D : Directed ι}

/-- **The stage inclusion reflects monos** (conservativity route, no faithfulness needed).  If
    `homInclObj g` is monic in the colimit and transitions are conservative (`hcons`), then `g` is
    monic at its stage.  `g` monic ⟺ the diagonal into a kernel-pair level is iso
    (`mono_iff_level_diag_iso`).  The stage kernel-pair pullback of `(g, g)` is preserved by the stage
    inclusion (`objIncl_preserves_pullbacks`), so its `homInclObj`-image is a level of `homInclObj g`
    whose diagonal is `homInclObj kp_diag`.  `homInclObj g` monic forces that colimit diagonal iso;
    iso-reflection (`homInclObj_isIso_reflects`, via `hcons`) brings it back to the stage diagonal. -/
theorem homInclObj_mono_reflects (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hppres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
        (k : z ⟶ C.F hij X)
        (_hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso ((C.functF hij).map φ) → IsIso φ)
    {K : ι} {x y : C.A K} (g : x ⟶ y)
    (hm : @Mono C.Obj (colimitCat C hC) (C.objIncl K x) (C.objIncl K y) (homInclObj C hC g)) :
    @Mono (C.A K) (C.catA K) x y g := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasTerminal (C.A K) := ht K
  letI : HasBinaryProducts (C.A K) := hp K
  letI : HasEqualizers (C.A K) := he K
  letI : HasPullbacks (C.A K) := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
  -- the chosen kernel-pair pullback of `(g, g)` (matches `objIncl_preserves_pullbacks`'s `P`)
  let P := products_equalizers_implies_pullbacks g g
  -- stage kernel-pair level of `g`, built directly on `P.cone` (so `Ls.c.pt` is `P.cone.pt`
  -- syntactically, matching the colimit cone below)
  let Ls : Level g :=
    { c := P.cone, hpb := P.cone_isPullback, δ := P.lift diagCone,
      δ₁ := P.lift_fst diagCone, δ₂ := P.lift_snd diagCone }
  -- the colimit cone (the `homInclObj`-image of `P.cone`); its cospan is inferred from the legs
  let cc := Cone.mk (f := homInclObj C hC g) (g := homInclObj C hC g)
      (C.objIncl K P.cone.pt) (homInclObj C hC P.cone.π₁) (homInclObj C hC P.cone.π₂)
      (show colimComp C hC (homInclObj C hC P.cone.π₁) (homInclObj C hC g)
          = colimComp C hC (homInclObj C hC P.cone.π₂) (homInclObj C hC g) by
        rw [← homInclObj_comp C hC P.cone.π₁ g, ← homInclObj_comp C hC P.cone.π₂ g, P.cone.w])
  have hcc_pb : cc.IsPullback :=
    objIncl_preserves_pullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift K g g
  -- the two collapse equations of the colimit diagonal `homInclObj Ls.δ` against `cc`
  have e₁ : Ls.δ ≫ P.cone.π₁ = Cat.id x := Ls.δ₁
  have e₂ : Ls.δ ≫ P.cone.π₂ = Cat.id x := Ls.δ₂
  have hδ₁ : homInclObj C hC Ls.δ ≫ cc.π₁ = Cat.id (C.objIncl K x) := by
    show colimComp C hC (homInclObj C hC Ls.δ) (homInclObj C hC P.cone.π₁) = _
    rw [← homInclObj_comp C hC Ls.δ P.cone.π₁, e₁]; exact homInclObj_id C hC x
  have hδ₂ : homInclObj C hC Ls.δ ≫ cc.π₂ = Cat.id (C.objIncl K x) := by
    show colimComp C hC (homInclObj C hC Ls.δ) (homInclObj C hC P.cone.π₂) = _
    rw [← homInclObj_comp C hC Ls.δ P.cone.π₂, e₂]; exact homInclObj_id C hC x
  -- `homInclObj g` mono ⇒ colimit level diagonal `homInclObj Ls.δ` iso (`mono_iff_level_diag_iso`)
  -- `homInclObj g` mono ⇒ the colimit diagonal `homInclObj Ls.δ` is iso, with inverse `cc.π₁`.
  -- (forward direction of `mono_iff_level_diag_iso`, inlined to dodge the `Level` elaboration of a
  -- non-stage hom whose `⟶`-codomain is not syntactically exposed).
  have hLcδ : @IsIso C.Obj (colimitCat C hC) (C.objIncl K x) (C.objIncl K Ls.c.pt)
      (homInclObj C hC Ls.δ) := by
    refine ⟨cc.π₁, hδ₁, ?_⟩
    -- `cc.π₁ ≫ homInclObj Ls.δ = id`: both are the unique self-lift of the pullback cone `cc`.
    have hπ : cc.π₁ = cc.π₂ := hm _ _ cc.w
    obtain ⟨_, _, huniq⟩ := hcc_pb cc
    have hid : Cat.id cc.pt = _ := huniq (Cat.id cc.pt) (Cat.id_comp _) (Cat.id_comp _)
    have hcomp : cc.π₁ ≫ homInclObj C hC Ls.δ = _ := huniq (cc.π₁ ≫ homInclObj C hC Ls.δ)
      (by rw [Cat.assoc, hδ₁, Cat.comp_id])
      (by rw [Cat.assoc, hδ₂, Cat.comp_id, hπ])
    rw [hcomp, ← hid]
  -- iso-reflection (`hcons`) brings it to the stage diagonal; `Ls.δ` iso ⇒ `g` mono
  have hLsδ : IsIso Ls.δ := homInclObj_isIso_reflects C hC hcons Ls.δ hLcδ
  intro W u v huv
  exact (mono_iff_level_diag_iso Ls).2 hLsδ u v huv

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
    (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
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
  letI : Cat C.Obj := colimitCat C hC
  intro E m hm hniso
  -- align the colimit mono `m : E ⟶ objIncl i A₀` to a stage-`N` germ `mN : xE ⟶ xA`
  obtain ⟨N, xE, xA, mN, eE, eA, hHEq⟩ := colimHom_as_homInclObj C hC m
  subst eE
  -- common stage `K ≥ N, i` where the codomain rep `xA` agrees with the pushforward `F (i→K) A₀`
  obtain ⟨K, hNK, hiK, hAeq⟩ := Quotient.exact eA
  dsimp only [CatSystem.objSystem] at hAeq
  -- push `mN` to stage `K`; `m` is its stage-`K` inclusion (transported by the object equalities)
  let mNK := (C.functF hNK).map mN
  have hcodXE : C.objIncl K (C.F hNK xE) = C.objIncl N xE := C.objIncl_compat hNK xE
  have hcodXA : C.objIncl K (C.F hNK xA) = C.objIncl i A₀ := (C.objIncl_compat hNK xA).trans eA
  have hmeq : castHom hcodXE hcodXA (homInclObj C hC mNK) = m :=
    castHom_of_heq hcodXE hcodXA ((homInclObj_push_heq C hC hNK mN).trans hHEq)
  -- `homInclObj mNK` inherits `Mono` and `¬IsIso` from `m` (cast along the object equalities)
  have hmNK_eq : homInclObj C hC mNK = castHom hcodXE.symm hcodXA.symm m := by
    rw [← hmeq, castHom_castHom, castHom_rfl]
  have hm' : @Mono C.Obj (colimitCat C hC) (C.objIncl K (C.F hNK xE)) (C.objIncl K (C.F hNK xA))
      (homInclObj C hC mNK) := by
    rw [hmNK_eq]; exact mono_castHom hcodXE.symm hcodXA.symm m hm
  have hniso' : ¬ @IsIso C.Obj (colimitCat C hC) (C.objIncl K (C.F hNK xE)) (C.objIncl K (C.F hNK xA))
      (homInclObj C hC mNK) := by
    rw [hmNK_eq]; exact fun h => hniso (isIso_of_castHom hcodXE.symm hcodXA.symm m h)
  -- reflect `Mono`/`¬IsIso` to the stage germ `mNK`
  have hmNK_mono : @Mono (C.A K) (C.catA K) (C.F hNK xE) (C.F hNK xA) mNK :=
    homInclObj_mono_reflects C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcons
      (K := K) (x := C.F hNK xE) (y := C.F hNK xA) mNK hm'
  have hmNK_niso : ¬ @IsIso (C.A K) (C.catA K) _ _ mNK := fun h => by
    obtain ⟨g', hg1, hg2⟩ := h
    exact hniso' (homInclObj_isIso_of_stage C hC mNK g' hg1 hg2)
  -- `hWP (i→K)` at the codomain `F hNK xA` (rewriting `hAeq`); apply to the stage mono `mNK`
  have hWP_K : @WellPointed (C.A K) (C.catA K) (ht K) (C.F hNK xA) := hAeq ▸ hWP hiK
  obtain ⟨x₀, hx₀⟩ := hWP_K mNK hmNK_mono hmNK_niso
  -- the colimit terminal `one` is `objIncl K (ht K).one` (`objIncl_terminal_eq`)
  have hone : C.objIncl K (ht K).one
      = @HasTerminal.one C.Obj (colimitCat C hC)
          (colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
            hcanon).toHasTerminal :=
    objIncl_terminal_eq C hC ht htpres K (Classical.choice hne)
  -- the colimit point: `homInclObj x₀`, transported to `one ⟶ objIncl i A₀`
  refine ⟨castHom hone hcodXA (homInclObj C hC x₀), ?_⟩
  -- a colimit factorization of the point through `m` reflects, via the pullback of `(mNK, x₀)`
  -- (preserved by the stage inclusion) and `homInclObj_isIso_reflects`, to a stage factorization of
  -- `x₀` through `mNK` — contradicting `hx₀`.
  rintro ⟨y, hy⟩
  -- pullback of `(mNK, x₀)` at stage `K`; its `homInclObj`-image is a colimit pullback of `(m, point)`
  let P' := products_equalizers_implies_pullbacks mNK x₀
  have hP'_colim := objIncl_preserves_pullbacks C hC ht htpres hp hppres hppres_pair he hepres
    hepres_lift K mNK x₀
  -- the stage factorization, obtained by reflecting `IsIso (homInclObj P'.cone.π₂)` to the stage
  apply hx₀
  -- transport the colimit factorization `y ≫ m = point` to `y' ≫ homInclObj mNK = homInclObj x₀`
  have hyt : castHom hone.symm hcodXE.symm y ≫ homInclObj C hC mNK = homInclObj C hC x₀ := by
    rw [← hmeq] at hy
    -- `y ≫ castHom hcodXE hcodXA (homInclObj mNK) = castHom hone hcodXA (homInclObj x₀)`
    have : castHom hone.symm hcodXE.symm y ≫ homInclObj C hC mNK
        = castHom hone.symm hcodXA.symm (y ≫ castHom hcodXE hcodXA (homInclObj C hC mNK)) := by
      rw [← castHom_comp hone.symm hcodXE.symm hcodXA.symm y
        (castHom hcodXE hcodXA (homInclObj C hC mNK)), castHom_castHom, castHom_rfl]
    rw [this, hy, castHom_castHom, castHom_rfl]
  -- `homInclObj mNK` mono + the colimit pullback ⇒ factorization ⇒ `IsIso (homInclObj P'.cone.π₂)`
  have hcolim_iso : @IsIso C.Obj (colimitCat C hC) _ _ (homInclObj C hC P'.cone.π₂) :=
    (factor_iff_pullback_π₂_iso hm'
      (Cone.mk (f := homInclObj C hC mNK) (g := homInclObj C hC x₀)
        (C.objIncl K P'.cone.pt) (homInclObj C hC P'.cone.π₁) (homInclObj C hC P'.cone.π₂)
        (by
          show colimComp C hC (homInclObj C hC P'.cone.π₁) (homInclObj C hC mNK)
            = colimComp C hC (homInclObj C hC P'.cone.π₂) (homInclObj C hC x₀)
          rw [← homInclObj_comp C hC P'.cone.π₁ mNK, ← homInclObj_comp C hC P'.cone.π₂ x₀,
            P'.cone.w]))
      hP'_colim).1 ⟨castHom hone.symm hcodXE.symm y, hyt⟩
  -- reflect to the stage `IsIso P'.cone.π₂`, then the stage factor_iff gives the stage factorization
  have hstage_iso : IsIso P'.cone.π₂ := homInclObj_isIso_reflects C hC hcons P'.cone.π₂ hcolim_iso
  exact (factor_iff_pullback_π₂_iso hmNK_mono P'.cone P'.cone_isPullback).2 hstage_iso

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

/-! ## Generic wiring: any cofinal directed system has a capital colimit

  The two declarations below are the verbatim generalizations of `tower_capital_of_cofinal` and
  `capData_of_tower` from the concrete ℕ `towerSystem` to an ARBITRARY coherent `CatSystem`.  They
  carry no new proof obligation beyond `wellPointed_of_stage` (already proven generically) plus the
  explicit `hstage` premise.  Their purpose is to isolate the single residual of §1.543 to one
  honest task — **exhibit a cofinal directed system** (an `ι`, `D`, `C`, base embedding, and the
  per-object stage-pointing witness `hstage`) — with no `sorry` hidden in the colimit bookkeeping. -/

/-- **Generic outer fixpoint.**  For any coherent `CatSystem C` with the full `colimitPreRegular`
    preservation package and the two reflection hypotheses (`hcons`/`hmono`), if every well-supported
    colimit object's representing stage object stays well-pointed at all later stages (`hstage` — the
    cofinal-coverage obligation), the colimit category is **capital**.  Verbatim generalization of
    `tower_capital_of_cofinal`; the residual is confined to `wellPointed_of_stage` and the explicit
    `hstage` premise, isolating §1.543's gap to "construct a cofinal system". -/
theorem capital_of_cofinalSystem {ι : Type u} {D : Colim.Directed ι}
    (C : Colim.CatSystem.{u, u} ι D) (hC : C.Coherent) [Nonempty ι]
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
    (hstage : ∀ (X : C.Obj),
        letI : Cat C.Obj := colimitCat C hC
        letI : PreRegularCategory C.Obj :=
          colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
        WellSupported X →
        ∀ {j} (hij : D.le (colimOut C X).1 j),
          @WellPointed (C.A j) (C.catA j) (ht j) (C.F hij (colimOut C X).2)) :
    letI : Cat C.Obj := colimitCat C hC
    letI : PreRegularCategory C.Obj :=
      colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
    Capital (𝒞 := C.Obj) := by
  intro X hXws
  rw [← colimOut_spec C X]
  exact wellPointed_of_stage C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
    hcons hmono (colimOut C X).1 (colimOut C X).2 (hstage X hXws)

/-- **Generic `CapData` assembly.**  Packages a base stage `i₀`, a faithful start `A → C.A i₀`, the
    transition faithfulness/conservativity, the preservation package, and the generic capital colimit
    (`capital_of_cofinalSystem`) into the `CapData A` the §1.543 reduction
    (`capitalization_of_capData`) consumes.  Verbatim generalization of `capData_of_tower` to an
    arbitrary cofinal directed system; the only remaining input is exhibiting such a system together
    with its stage-pointing witness `hstage`. -/
theorem capData_of_cofinalSystem (A : Type u) [Cat.{u} A] [PreRegularCategory A]
    {ι : Type u} {D : Colim.Directed ι} (C : Colim.CatSystem.{u, u} ι D) (hC : C.Coherent)
    [hne : Nonempty ι] (i₀ : ι) (base : A → C.A i₀)
    (baseFun : @Functor A _ (C.A i₀) (C.catA i₀) base)
    (baseFaithful : @Faithful A _ (C.A i₀) (C.catA i₀) base baseFun)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
      (C.functF hij).map p = (C.functF hij).map q → p = q)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso ((C.functF hij).map φ) → IsIso φ)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Mono φ → Mono ((C.functF hij).map φ))
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
    (hstage : ∀ (X : C.Obj),
        letI : Cat C.Obj := colimitCat C hC
        letI : PreRegularCategory C.Obj :=
          colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
        WellSupported X →
        ∀ {j} (hij : D.le (colimOut C X).1 j),
          @WellPointed (C.A j) (C.catA j) (ht j) (C.F hij (colimOut C X).2)) :
    Nonempty (CapData.{u} A) :=
  ⟨{ ι := ι, D := D, C := C, hC := hC, hne := hne, i₀ := i₀
     base := base, baseFun := baseFun, baseFaithful := baseFaithful
     hfaith := hfaith, hcons := hcons
     ht := ht, htpres := htpres, hp := hp, hppres := hppres, hppres_pair := hppres_pair
     he := he, hepres := hepres, hepres_lift := hepres_lift, hcanon := hcanon
     capital := capital_of_cofinalSystem C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
       hcanon hcons hmono hstage }⟩

end Freyd
