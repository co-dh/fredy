/-
  LeetCode 322 (Coin Change) — correctness RE-DERIVED from the abstract ∞-completed
  dynamic-programming theorem `Fredy.A9_2.dynamic_programming_inf`.

  `Fredy.L322` proves `coinSpec coins amount (solveFn coins amount)` by a monolithic fuel
  induction, and its closing comment diagnoses WHY B&dM Theorem 9.1 cannot be instantiated
  instead: the Egli–Milner `powerRel` empties the recursion body on dead sub-amounts.  This
  file closes that gap using `dynamic_programming_inf`: the target lattice `Option Nat`
  (`none = ∞`) is already the ∞-completion the abstract theorem asks for, with

  * value order   `Rle y x ↔ ole x y`   (`ole` = `≤` on `Option Nat` with `none` the TOP),
  * refold algebra `hAlg = graph hFn`   (`inl _ ↦ some 0`, `inr (c, x) ↦ osucc x` — STRICT
    at ∞: `osucc none = none`, which is exactly what discharges `hstrict`),
  * amount coalgebra-converse `TCo`     (`inl _ ↦ 0`; `inr (c, v') ↦ v' + c` for coins `c`),
  * fallback `tauR = graph (fun _ => none)` (the constant-∞ map; `R`-top by `tauR_top`).

  Structure of the re-derivation:
  1. hypothesis discharges for `dynamic_programming_inf` (pointwise, §"Abstract-side"),
     with the hylomorphism `H` identified as `Achievable` via `specH_iff`;
  2. the EXECUTABLE-SIDE BRIDGE `dp_mem_mu`: the fueled `dp` lands inside `μ(dpBodyInf)` —
     an induction on the amount that only ever uses the RECURSION SHAPE of `dp` (the
    `coinFold` fold computes an `ole`-minimum of the one-step candidates plus ∞), never the
     spec: minimality/achievability now come from the abstract theorem;
  3. `spec_pointwise`: the abstract specification `min Rle · Λ(H ∪ τ)` reads back as
     `coinSpec`;
  4. `solve_correct_inf` — the same statement as `Fredy.L322.solve_correct`, re-proved.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.L322
import Fredy.A6_ConsList
import Fredy.A9_2

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC322

open Freyd Freyd.Alg.RelSet.SL

/-! ## Pointwise (`Rel(Set)`) readings of the power-allegory operations

  `powerRel`, `minRel`, `leftDiv` and `∋` all unfold definitionally in `Rel(Set)`; `A` does
  not (it is a symmetric division), so its content is extracted through `A_eps_eq'` +
  `A_is_map'` instead. -/

theorem powerRel_pt {α β : RelSet.{0}} (g : α ⟶ β) (P : (pow α).carrier)
    (Q : (pow β).carrier) :
    powerRel g P Q ↔
      (∀ t, P t → ∃ u, g t u ∧ Q u) ∧ (∀ u, Q u → ∃ t, P t ∧ g t u) :=
  Iff.rfl

theorem minRel_pt {α : RelSet.{0}} (R : α ⟶ α) (P : (pow α).carrier) (x : α.carrier) :
    minRel R P x ↔ P x ∧ ∀ z, P z → R z x :=
  Iff.rfl

theorem lb_pt {α : RelSet.{0}} (R : α ⟶ α) (P : (pow α).carrier) (x : α.carrier) :
    leftDiv ((∋ α)°) R P x ↔ ∀ z, P z → R z x :=
  Iff.rfl

/-- The set a transpose `A S` points `x` at contains exactly the `S`-successors of `x`. -/
theorem A_pt {α β : RelSet.{0}} (S : α ⟶ β) {x : α.carrier} {P : (pow β).carrier}
    (hP : A S x P) (y : β.carrier) : P y ↔ S x y := by
  constructor
  · intro hy
    have h1 : (A S ≫ ∋ β) x y := ⟨P, hP, hy⟩
    rw [A_eps_eq'] at h1
    exact h1
  · intro hS
    have h1 : (A S ≫ ∋ β) x y := by rw [A_eps_eq']; exact hS
    obtain ⟨P', hP', hy⟩ := h1
    have hPP : P' = P := simple_uniq (A_is_map' S).2 hP' hP
    rw [← hPP]
    exact hy

/-! ## The instantiation data: `Option Nat` with `none = ∞` -/

/-- The object of amounts. -/
abbrev dAmt : RelSet.{0} := ⟨Nat⟩

/-- `ole x y` — `x ≤ y` on `Option Nat` with `none = ∞` the TOP (`ole x none` always). -/
def ole (x y : Option Nat) : Prop :=
  match y with
  | none => True
  | some n => match x with
    | some m => m ≤ n
    | none => False

theorem ole_trans {x y z : Option Nat} (hxy : ole x y) (hyz : ole y z) : ole x z := by
  match z, hyz with
  | none, _ => trivial
  | some n, hyz =>
    match y, hxy, hyz with
    | none, hxy, hyz => exact hyz.elim
    | some k, hxy, hyz =>
      match x, hxy with
      | none, hxy => exact hxy.elim
      | some m, hxy => exact Nat.le_trans hxy hyz

theorem ole_osucc {x y : Option Nat} (h : ole x y) : ole (osucc x) (osucc y) := by
  match y, h with
  | none, _ => trivial
  | some n, h =>
    match x, h with
    | none, h => exact h.elim
    | some m, h => exact Nat.succ_le_succ h

/-- The value order as a `Rel(Set)` morphism: `Rle y x` when `x` is `ole`-below `y` —
    Fredy's `minRel` convention (`(∋)° ≫ minRel R ⊑ R`: the min is `R`-related FROM every
    member). -/
def Rle : dAns ⟶ dAns := fun y x => ole x y

/-- The refold-algebra function: count one more coin, strictly (`osucc none = none`). -/
def hFn : (CL.Fobj Unit Nat dAns).carrier → Option Nat
  | Sum.inl _ => some 0
  | Sum.inr p => osucc p.2

/-- The refold algebra as a map. -/
def hAlg : CL.Fobj Unit Nat dAns ⟶ dAns := graph hFn

/-- The amount coalgebra-converse: `inl _ ↦ 0` (base), `inr (c, v') ↦ v' + c` for each valid
    denomination `c` (a partial map — dead amounts have NO decomposition through the `inr`
    branch, which is exactly what breaks B&dM Theorem 9.1 and what `tauR` repairs). -/
def TCo (coins : SnocList Nat Nat) : CL.Fobj Unit Nat dAmt ⟶ dAmt := fun u v =>
  match u with
  | Sum.inl _ => v = 0
  | Sum.inr p => mem coins p.1 ∧ 1 ≤ p.1 ∧ v = p.2 + p.1

/-- The fallback: the constant-∞ map. -/
def tauR : dAmt ⟶ dAns := graph fun _ => none

/-! ## Abstract-side hypotheses of `dynamic_programming_inf` -/

theorem Rle_trans : Rle ≫ Rle ⊑ Rle := by
  apply le_iff.mpr
  intro y x h
  obtain ⟨z, hzy, hxz⟩ := h
  exact ole_trans hxz hzy

theorem hAlg_monotonic : MonotonicAlg (F := CL.F Unit Nat) hAlg Rle := by
  show (CL.F Unit Nat).map Rle ≫ hAlg ⊑ hAlg ≫ Rle
  apply le_iff.mpr
  intro u x h
  obtain ⟨w, hFw, hx⟩ := h
  refine ⟨hFn u, rfl, ?_⟩
  cases u with
  | inl d =>
    cases w with
    | inl d' =>
      have hx0 : x = some 0 := hx
      rw [hx0]
      exact Nat.le_refl 0
    | inr q => exact hFw.elim
  | inr p =>
    obtain ⟨c, y⟩ := p
    cases w with
    | inl d' => exact hFw.elim
    | inr q =>
      obtain ⟨c', y'⟩ := q
      obtain ⟨hcc, hyy⟩ := hFw
      have hx' : x = osucc y' := hx
      rw [hx']
      exact ole_osucc hyy

/-- The fallback is top-valued: everything is `Rle`-below `none`. -/
theorem tauR_top : tauR° ≫ topHom dAmt dAns ⊑ Rle := by
  apply le_iff.mpr
  intro k x h
  obtain ⟨v, hkv, -⟩ := h
  have hk : k = none := hkv
  rw [hk]
  exact trivial

/-! ## Identifying the hylomorphism: `H = Achievable`, ∞-embedded -/

/-- The B&dM optimisation-problem relation `H = ⦇hAlg⦈·⦇TCo⦈°` for the coin instance. -/
def specH (coins : SnocList Nat Nat) : dAmt ⟶ dAns :=
  (relCata (CL.initial Unit Nat) (TCo coins))° ≫ relCata (CL.initial Unit Nat) hAlg

/-- Number of coins in a decomposition. -/
def clen : CL.ConsList Unit Nat → Nat
  | CL.ConsList.wrap _ => 0
  | CL.ConsList.cons _ t => clen t + 1

/-- The refold fold always counts: `⦇hAlg⦈` relates every coin sequence to `some` its
    length (never to `∞` — leaves start at `some 0` and `osucc` preserves `some`). -/
theorem cataFold_hAlg_pt : ∀ (ℓ : CL.ConsList Unit Nat) (x : Option Nat),
    CL.cataFold hAlg ℓ x ↔ x = some (clen ℓ)
  | CL.ConsList.wrap d, x => Iff.rfl
  | CL.ConsList.cons c t, x => by
    show (∃ r', CL.cataFold hAlg t r' ∧ hAlg (Sum.inr (c, r')) x) ↔ x = some (clen t + 1)
    constructor
    · rintro ⟨r', hr', hx⟩
      rw [(cataFold_hAlg_pt t r').mp hr'] at hx
      exact hx
    · intro hx
      exact ⟨some (clen t), (cataFold_hAlg_pt t _).mpr rfl, hx⟩

/-- The unfold fold is achievability, one direction: a `TCo`-decomposition of `v` with `n`
    coins witnesses `Achievable coins n v`. -/
theorem cataFold_TCo_achievable (coins : SnocList Nat Nat) :
    ∀ (ℓ : CL.ConsList Unit Nat) (v : Nat),
      CL.cataFold (TCo coins) ℓ v → Achievable coins (clen ℓ) v
  | CL.ConsList.wrap _, v, h => by
    have h0 : v = 0 := h
    rw [h0]
    exact Achievable.zero
  | CL.ConsList.cons c t, v, h => by
    obtain ⟨v', hv', hmem, hpos, hveq⟩ := h
    rw [hveq]
    exact Achievable.succ (cataFold_TCo_achievable coins t v' hv') hmem hpos

/-- ... and conversely: every achievability derivation is a `TCo`-decomposition. -/
theorem achievable_cataFold_TCo (coins : SnocList Nat Nat) {n v : Nat}
    (h : Achievable coins n v) : ∃ ℓ, CL.cataFold (TCo coins) ℓ v ∧ clen ℓ = n := by
  induction h with
  | zero => exact ⟨CL.ConsList.wrap (), rfl, rfl⟩
  | succ h hmem hpos ih =>
    obtain ⟨ℓ, hℓ, hlen⟩ := ih
    exact ⟨CL.ConsList.cons _ ℓ, ⟨_, hℓ, hmem, hpos, rfl⟩,
      show clen ℓ + 1 = _ + 1 by rw [hlen]⟩

/-- **The hylomorphism identified**: `H v x ↔ x = some n` for `n` an achievable coin count.
    (`H` never takes the value `∞` — `tauR` alone supplies the fallback in `H ∪ τ`.) -/
theorem specH_pt (coins : SnocList Nat Nat) (v : Nat) (x : Option Nat) :
    specH coins v x ↔ ∃ n, x = some n ∧ Achievable coins n v := by
  show ((relCata (CL.initial Unit Nat) (TCo coins))° ≫ relCata (CL.initial Unit Nat) hAlg) v x
      ↔ _
  rw [← CL.cataR_eq_relCata, ← CL.cataR_eq_relCata]
  constructor
  · rintro ⟨ℓ, hT, hh⟩
    exact ⟨clen ℓ, (cataFold_hAlg_pt ℓ x).mp hh, cataFold_TCo_achievable coins ℓ v hT⟩
  · rintro ⟨n, hx, hach⟩
    obtain ⟨ℓ, hℓ, hlen⟩ := achievable_cataFold_TCo coins hach
    exact ⟨ℓ, hℓ, (cataFold_hAlg_pt ℓ x).mpr (by rw [hx, hlen])⟩

/-- **The `hstrict` hypothesis**: the ∞-extended answer relation `H ∪ τ` absorbs one
    decompose-solve-fold step.  The all-`H` slots case re-runs one `Achievable.succ`; a
    fallback slot survives because `hFn` is STRICT at ∞ (`osucc none = none`). -/
theorem hstrict_coins (coins : SnocList Nat Nat) :
    (TCo coins)° ≫ (CL.F Unit Nat).map (specH coins ∪ tauR) ≫ hAlg
      ⊑ specH coins ∪ tauR := by
  apply le_iff.mpr
  intro v x hcomp
  obtain ⟨t, hT, w, hFw, hx⟩ := hcomp
  have hTt : TCo coins t v := hT
  cases t with
  | inl d =>
    have hv : v = 0 := hTt
    cases w with
    | inl d' =>
      have hx0 : x = some 0 := hx
      exact Or.inl ((specH_pt coins v x).mpr ⟨0, hx0, by rw [hv]; exact Achievable.zero⟩)
    | inr q => exact hFw.elim
  | inr p =>
    obtain ⟨c, v'⟩ := p
    obtain ⟨hmem, hpos, hveq⟩ := hTt
    cases w with
    | inl d' => exact hFw.elim
    | inr q =>
      obtain ⟨c', y⟩ := q
      obtain ⟨hcc, hSy⟩ := hFw
      have hSy' : specH coins v' y ∨ tauR v' y := hSy
      cases hSy' with
      | inl hH =>
        obtain ⟨n, hy, hach⟩ := (specH_pt coins v' y).mp hH
        refine Or.inl ((specH_pt coins v x).mpr ⟨n + 1, ?_, ?_⟩)
        · rw [(hx : x = hFn (Sum.inr (c', y))), hy]
          rfl
        · rw [hveq]
          exact Achievable.succ hach hmem hpos
      | inr hτ =>
        refine Or.inr ?_
        show x = none
        rw [(hx : x = hFn (Sum.inr (c', y))), (hτ : y = none)]
        rfl

/-! ## The executable-side bridge: `dp ⊑ μ(dpBodyInf)`

  Only the RECURSION SHAPE of the fueled `dp` is used here — `dpFuel` is fuel-irrelevant
  (`dpFuel_congr`), one level of `dp` is a `coinFold`, and the `omin`-fold computes an
  `ole`-minimum of the one-step candidates together with ∞.  No spec reasoning: minimality
  and achievability are the abstract theorem's business. -/

theorem contrib_congr {step step' : Nat → Option Nat} {t c : Nat}
    (h : 1 ≤ c → c ≤ t → step (t - c) = step' (t - c)) :
    contrib step t c = contrib step' t c := by
  unfold contrib
  by_cases hb : 1 ≤ c ∧ c ≤ t
  · rw [if_pos hb, if_pos hb, h hb.1 hb.2]
  · rw [if_neg hb, if_neg hb]

theorem coinFold_congr {step step' : Nat → Option Nat} {t : Nat} :
    ∀ cs : SnocList Nat Nat,
      (∀ c, mem cs c → 1 ≤ c → c ≤ t → step (t - c) = step' (t - c)) →
      coinFold step t cs = coinFold step' t cs
  | SnocList.wrap c₀, h => contrib_congr (h c₀ rfl)
  | SnocList.snoc cs c₁, h => by
    show omin (coinFold step t cs) (contrib step t c₁)
        = omin (coinFold step' t cs) (contrib step' t c₁)
    rw [coinFold_congr cs (fun c hm => h c (Or.inl hm)), contrib_congr (h c₁ (Or.inr rfl))]

/-- Fuel irrelevance: any sufficient fuel computes the same value. -/
theorem dpFuel_congr (coins : SnocList Nat Nat) :
    ∀ f f' v, v ≤ f → v ≤ f' → dpFuel coins f v = dpFuel coins f' v := by
  intro f
  induction f with
  | zero =>
    intro f' v hv hv'
    have h0 : v = 0 := Nat.le_zero.mp hv
    subst h0
    cases f' with
    | zero => rfl
    | succ f'' => rfl
  | succ fn ih =>
    intro f' v hv hv'
    match v, hv, hv' with
    | 0, _, _ =>
      cases f' with
      | zero => rfl
      | succ f'' => rfl
    | v' + 1, hv, hv' =>
      cases f' with
      | zero => exact absurd hv' (by omega)
      | succ f'' =>
        show coinFold (dpFuel coins fn) (v' + 1) coins
            = coinFold (dpFuel coins f'') (v' + 1) coins
        apply coinFold_congr
        intro c hm hpos hle
        exact ih f'' (v' + 1 - c) (by omega) (by omega)

/-- The executable one-step function on decompositions (`dp` on the sub-amount, `osucc`ed;
    `some 0` on the base) — its image is the canonical Egli–Milner candidate set. -/
def stepFn (coins : SnocList Nat Nat) : (CL.Fobj Unit Nat dAmt).carrier → Option Nat
  | Sum.inl _ => some 0
  | Sum.inr p => osucc (dp coins p.2)

/-- **One unfolding of the bridge**: `dp`'s value at `v` inhabits the ∞-DP body at any `X`
    that already contains `dp`'s graph on smaller amounts. -/
theorem dp_mem_body (coins : SnocList Nat Nat) {X : dAmt ⟶ dAns} (v : Nat)
    (hsub : ∀ w, w < v → X w (dp coins w)) :
    dpBodyInf (CL.F Unit Nat) (TCo coins) hAlg Rle tauR X v (dp coins v) := by
  -- the decomposition set and its content
  obtain ⟨P, hP⟩ := entire_total (A_is_map' ((TCo coins)°)).1 v
  have hPmem : ∀ t, P t ↔ TCo coins t v := fun t => A_pt ((TCo coins)°) hP t
  -- every decomposition's executable value is a genuine `h·FX` candidate
  have hg : ∀ t, P t → ((CL.F Unit Nat).map X ≫ hAlg) t (stepFn coins t) := by
    intro t hPt
    have hTt : TCo coins t v := (hPmem t).mp hPt
    cases t with
    | inl d => exact ⟨Sum.inl d, rfl, rfl⟩
    | inr p =>
      obtain ⟨c, w⟩ := p
      have hTt' : mem coins c ∧ 1 ≤ c ∧ v = w + c := hTt
      obtain ⟨hmem, hpos, hveq⟩ := hTt'
      exact ⟨Sum.inr (c, dp coins w), ⟨rfl, hsub w (by omega)⟩, rfl⟩
  have hpow : powerRel ((CL.F Unit Nat).map X ≫ hAlg) P
      (fun x => ∃ t, P t ∧ x = stepFn coins t) :=
    (powerRel_pt _ _ _).mpr
      ⟨fun t hPt => ⟨stepFn coins t, hg t hPt, t, hPt, rfl⟩,
       fun u hu => by obtain ⟨t, hPt, hut⟩ := hu; exact ⟨t, hPt, hut ▸ hg t hPt⟩⟩
  cases v with
  | zero =>
    -- `dp coins 0 = some 0`, the value of the sole decomposition `inl ()`
    refine Or.inl ⟨P, hP, (fun x => ∃ t, P t ∧ x = stepFn coins t), hpow,
      (minRel_pt Rle _ _).mpr ⟨⟨Sum.inl (), (hPmem _).mpr rfl, rfl⟩, ?_⟩⟩
    intro z hz
    obtain ⟨t, hPt, hzt⟩ := hz
    have hTt := (hPmem t).mp hPt
    cases t with
    | inl d =>
      rw [hzt]
      exact Nat.le_refl 0
    | inr p =>
      obtain ⟨c, w⟩ := p
      have hTt' : mem coins c ∧ 1 ≤ c ∧ (0 : Nat) = w + c := hTt
      obtain ⟨hmem, hpos, hveq⟩ := hTt'
      exact absurd hveq (by omega)
  | succ v' =>
    have hdp : dp coins (v' + 1) = coinFold (dpFuel coins v') (v' + 1) coins := rfl
    have hbr : ∀ c, 1 ≤ c → c ≤ v' + 1 →
        dpFuel coins v' (v' + 1 - c) = dp coins (v' + 1 - c) :=
      fun c hpos hle => dpFuel_congr coins v' (v' + 1 - c) (v' + 1 - c) (by omega)
        (Nat.le_refl _)
    rcases hres : coinFold (dpFuel coins v') (v' + 1) coins with _ | m
    · -- every branch dead → the fold is ∞ → the FALLBACK disjunct of the body
      refine Or.inr ⟨show dp coins (v' + 1) = none by rw [hdp]; exact hres,
        P, hP, (fun x => ∃ t, P t ∧ x = stepFn coins t), hpow, (lb_pt Rle _ _).mpr ?_⟩
      intro z hz
      obtain ⟨t, hPt, hzt⟩ := hz
      have hTt := (hPmem t).mp hPt
      cases t with
      | inl d => exact absurd (show v' + 1 = 0 from hTt) (by omega)
      | inr p =>
        obtain ⟨c, w⟩ := p
        have hTt' : mem coins c ∧ 1 ≤ c ∧ v' + 1 = w + c := hTt
        obtain ⟨hmem, hpos, hveq⟩ := hTt'
        have hw2 : v' + 1 - c = w := by omega
        have hzn : z = none := by
          rw [hzt]
          show osucc (dp coins w) = none
          rw [← hw2, ← hbr c hpos (by omega),
            (coinFold_none_iff coins).mp hres c hmem hpos (by omega)]
          rfl
        rw [hzn]
        exact trivial
    · -- the fold found a finite minimum → the MIN disjunct of the body
      obtain ⟨c, mv, hmem, hpos, hle, hstep, hm⟩ := coinFold_achieves coins hres
      have hdpv : dp coins (v' + 1) = some m := by rw [hdp]; exact hres
      refine Or.inl ⟨P, hP, (fun x => ∃ t, P t ∧ x = stepFn coins t), hpow,
        (minRel_pt Rle _ _).mpr ⟨⟨Sum.inr (c, v' + 1 - c), (hPmem _).mpr
          (show mem coins c ∧ 1 ≤ c ∧ v' + 1 = (v' + 1 - c) + c from
            ⟨hmem, hpos, by omega⟩), ?_⟩, ?_⟩⟩
      · -- the fold's value IS the candidate of the winning decomposition
        show dp coins (v' + 1) = osucc (dp coins (v' + 1 - c))
        rw [hdpv, ← hbr c hpos hle, hstep, hm]
        rfl
      · -- ... and it `ole`-lower-bounds every candidate (`coinFold_dominates`)
        intro z hz
        obtain ⟨t, hPt, hzt⟩ := hz
        have hTt := (hPmem t).mp hPt
        cases t with
        | inl d => exact absurd (show v' + 1 = 0 from hTt) (by omega)
        | inr p =>
          obtain ⟨c', w'⟩ := p
          have hTt' : mem coins c' ∧ 1 ≤ c' ∧ v' + 1 = w' + c' := hTt
          obtain ⟨hmem', hpos', hveq'⟩ := hTt'
          have hw2' : v' + 1 - c' = w' := by omega
          have hz2 : z = osucc (dpFuel coins v' (v' + 1 - c')) := by
            rw [hzt]
            show osucc (dp coins w') = osucc (dpFuel coins v' (v' + 1 - c'))
            rw [← hw2', hbr c' hpos' (by omega)]
          rcases hstep' : dpFuel coins v' (v' + 1 - c') with _ | mv'
          · rw [hz2, hstep']
            exact trivial
          · obtain ⟨m₀, hm₀, hm₀le⟩ := coinFold_dominates (step := dpFuel coins v')
              (t := v' + 1) coins hmem' hpos' (by omega) hstep'
            rw [hres] at hm₀
            have hmm₀ : m = m₀ := Option.some.inj hm₀
            rw [hz2, hstep', hdpv]
            show m ≤ mv' + 1
            omega

/-- **The executable-side bridge**: `dp`'s graph is inside the least fixed point of the
    ∞-DP body — by induction on the amount (through an explicit fuel bound), one
    `mu_fixed`-unfolding per level, `dp_mem_body` doing each level. -/
theorem dp_mem_mu (coins : SnocList Nat Nat) (v : Nat) :
    mu (dpBodyInf (CL.F Unit Nat) (TCo coins) hAlg Rle tauR) v (dp coins v) := by
  have haux : ∀ f v : Nat, v ≤ f →
      mu (dpBodyInf (CL.F Unit Nat) (TCo coins) hAlg Rle tauR) v (dp coins v) := by
    intro f
    induction f with
    | zero =>
      intro v hv
      have h0 : v = 0 := Nat.le_zero.mp hv
      subst h0
      rw [← mu_fixed (dpBodyInf_monotonic (CL.F Unit Nat) (TCo coins) hAlg Rle tauR)]
      exact dp_mem_body coins 0 (fun w hw => absurd hw (Nat.not_lt_zero w))
    | succ fn ih =>
      intro v hv
      rw [← mu_fixed (dpBodyInf_monotonic (CL.F Unit Nat) (TCo coins) hAlg Rle tauR)]
      exact dp_mem_body coins v (fun w hw => ih w (by omega))
  exact haux v v (Nat.le_refl v)

/-! ## Reading the abstract specification back as `coinSpec` -/

/-- The ∞-extended abstract specification `min Rle · Λ(H ∪ τ)` is pointwise exactly
    `coinSpec`: a finite value is a minimal achievable count, `∞` means nothing is
    achievable. -/
theorem spec_pointwise (coins : SnocList Nat Nat) (v : Nat) (k : Option Nat)
    (h : (A (specH coins ∪ tauR) ≫ minRel Rle) v k) : coinSpec coins v k := by
  rw [A_comp_minRel] at h
  obtain ⟨hmem, hlb⟩ := h
  match k, hmem with
  | some n, hmem =>
    have hach : Achievable coins n v := by
      have hm : specH coins v (some n) ∨ tauR v (some n) := hmem
      cases hm with
      | inl hH =>
        obtain ⟨n', hn', hach⟩ := (specH_pt coins v (some n)).mp hH
        have hnn : n = n' := Option.some.inj hn'
        rw [hnn]
        exact hach
      | inr hτ =>
        have hx : (some n : Option Nat) = none := hτ
        nomatch hx
    refine ⟨hach, fun n' hach' => ?_⟩
    exact hlb (some n')
      (Or.inl ((specH_pt coins v (some n')).mpr ⟨n', rfl, hach'⟩))
  | none, hmem =>
    show ∀ n, ¬ Achievable coins n v
    intro n hach
    exact (hlb (some n)
      (Or.inl ((specH_pt coins v (some n)).mpr ⟨n, rfl, hach⟩)) : False)

/-! ## The headline: L322 correctness as an instance of the abstract ∞-DP theorem -/

/-- **`Fredy.L322.solve_correct`, re-derived**: `solveFn` computes the `≤`-extremum of the
    achievable coin-count spec — obtained from `Freyd.Alg.dynamic_programming_inf` (the
    abstract ∞-completed dynamic-programming theorem) instantiated at the `Option Nat`
    ∞-lattice, plus the executable-side bridge `dp_mem_mu`.  This is the derivation that
    B&dM Theorem 9.1 provably cannot supply (see the closing comment of `Fredy.L322`). -/
theorem solve_correct_inf (coins : SnocList Nat Nat) (amount : Nat) :
    coinSpec coins amount (solveFn coins amount) := by
  have habs := dynamic_programming_inf (F := CL.F Unit Nat) (CL.F_preservesRecip Unit Nat)
    (CL.initial Unit Nat) (graph_map hFn) hAlg_monotonic Rle_trans (hstrict_coins coins)
    tauR_top
  exact spec_pointwise coins amount _ (le_iff.mp habs amount _ (dp_mem_mu coins amount))

/-- The exact obstruction instance from `Fredy.L322`'s analysis: coins {2,3}, amount 3.
    B&dM Theorem 9.1's body is EMPTY here (`μ(body) 3 = 𝟘` — the dead `c = 2` branch leaves
    the unsolvable amount 1 and Egli–Milner term₁ kills the candidate set), yet
    `solve_correct_inf` certifies the executable's `some 1` — the fallback disjunct of
    `dpBodyInf` carries `∞` through the dead branch instead. -/
example : coinSpec (ofList 2 [3]) 3 (some 1) := by
  have h := solve_correct_inf (ofList 2 [3]) 3
  rwa [show solveFn (ofList 2 [3]) 3 = some 1 by decide] at h

end Freyd.Alg.RelSet.LC322
