/-
  A GENUINE calculational Algebra-of-Programming derivation, in the style of Bird & de Moor.

  The point of this file is METHODOLOGICAL: a functional program is CALCULATED from a
  relational/algebraic SPEC, so that the program EMERGES as the endpoint of a chain of
  allegory-law steps — it is NOT written first and verified afterwards.  Two kinds of
  derivation are demonstrated over snoc-lists `SnocList Unit Int` (the base engine is
  `AOP.A6_SnocList`), answering "does AoP derivation extend beyond the three optimisation
  theorems (greedy / thinning / dynamic-programming)?":

  ## Part 1 — the PROGRAM emerges from the homomorphism spec (universal property)
  The Horner value function `value` is SPECIFIED, not defined, as: "the unique relation `h`
  making the square `α ≫ h = F h ≫ φ` commute" (an `F`-algebra homomorphism from the initial
  algebra to the target algebra `φ`).  The Eilenberg–Wright universal property `relCata_UP`
  (A5_5) pins `h = relCata φ`; the SnocList bridge `cataR_eq_relCata` (A6_SnocList) rewrites
  that to the structural fold `cataR φ = cataFold φ`; and `cataFold`'s two defining equations
  then DELIVER the recursive program
      value (wrap _)      = 0
      value (snoc xs d)   = base * value xs + d           -- Horner's rule
  as theorems `value_wrap` / `value_snoc`, not as a definition.  (The target algebra `φ` was
  given in the spec; what emerges is the runnable recursion.)

  ## Part 2 — a reusable FOLD-FUSION law, derived purely from the universal property
  `cata_fusion` : `φ ≫ h = F h ≫ ψ  →  cata φ ≫ h = cata ψ`.  Proved abstractly from
  `relCata_cancel` + functoriality — one `calc` chain, each step one named allegory law.

  ## Part 3 — the ALGEBRA emerges by SOLVING the fusion equation
  Post-composing `value` with "multiply by `k`" and SOLVING the fusion condition
  `φ_val ≫ (k·) = F(k·) ≫ ψ` for `ψ` yields a NEW algebra
      ψ = [ _ ↦ 0 ,  (a,d) ↦ base * a + k * d ]                     -- a multiply-accumulate
  (the digit weight `k` is pushed onto the *new* digit, not onto the whole running value).
  Feeding that `ψ` back through the universal property gives a fresh program `scaleValue`.
  Here it is the ALGEBRA, not merely the recursion, that is the OUTPUT of the calculation.

  Mathlib-free.  Axioms ⊆ {propext, Classical.choice, Quot.sound}; `Classical.choice` is
  inherited from `relCata`'s universal property (the same honest price A6_6/A7_4 pay).
-/
import AOP.A6_SnocList

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.Deriv

open Freyd Freyd.Alg.RelSet.SL

/-! ############################################################################
    ## Part 1 — Horner's `value` derived from its homomorphism spec
    ############################################################################ -/

/-- The TARGET algebra of the specification, as an ordinary function
    `F Int → Int` (`F X = Unit + X × Int`): the empty list denotes `0`, and pushing a digit
    `d` onto a running value `a` denotes `base * a + d`.  This is the only thing "posited";
    the program is calculated from it. -/
def valAlg (base : Int) : (Fobj Unit Int (⟨Int⟩ : RelSet.{0})).carrier → Int
  | Sum.inl _ => 0
  | Sum.inr p => base * p.1 + p.2

/-- **The SPEC.**  `h` is a *value-homomorphism* at `base` when the initial-algebra square
    commutes: `α ≫ h = F h ≫ graph (valAlg base)`, i.e. `h` is an `F`-algebra homomorphism
    from the initial algebra `α = [wrap, snoc]` to the algebra `valAlg base`.  Nothing here
    says `h` is a fold. -/
def IsValueHom (base : Int) (h : dSL Unit Int ⟶ (⟨Int⟩ : RelSet.{0})) : Prop :=
  (initial Unit Int).α ≫ h = (F Unit Int).map h ≫ graph (valAlg base)

/-- **Derivation step (universal property).**  Being a value-homomorphism is EQUIVALENT to
    being the catamorphism of `valAlg base`.  Proof = the Eilenberg–Wright universal property
    `relCata_UP` (A5_5) followed by the SnocList bridge `cataR_eq_relCata` (A6_SnocList).  No
    induction, no guessing: the fold is FORCED by the spec. -/
theorem value_is_unique_hom (base : Int) (h : dSL Unit Int ⟶ (⟨Int⟩ : RelSet.{0})) :
    IsValueHom base h ↔ h = cataR (graph (valAlg base)) := by
  unfold IsValueHom
  rw [relCata_UP (initial Unit Int) (graph (valAlg base)) h, cataR_eq_relCata]

/-- **Program emerges (base case).**  `cataFold`'s `wrap` equation instantiated at `valAlg`:
    the value of the empty list is `0`.  Holds definitionally. -/
theorem value_wrap (base : Int) (u : Unit) (r : Int) :
    cataR (graph (valAlg base)) (SnocList.wrap u) r ↔ r = 0 := Iff.rfl

/-- **Program emerges (step case).**  `cataFold`'s `snoc` equation instantiated at `valAlg`:
    pushing a digit `d` multiplies the running value by `base` and adds `d` — Horner's rule.
    Holds definitionally. -/
theorem value_snoc (base : Int) (xs : SnocList Unit Int) (d : Int) (r : Int) :
    cataR (graph (valAlg base)) (SnocList.snoc xs d) r
      ↔ ∃ r', cataR (graph (valAlg base)) xs r' ∧ r = base * r' + d := Iff.rfl

/-- The runnable functional PROGRAM that the derivation produced (its recursion equations are
    exactly `value_wrap` / `value_snoc`). -/
def value (base : Int) : SnocList Unit Int → Int
  | SnocList.wrap _ => 0
  | SnocList.snoc xs d => base * value base xs + d

/-- The relational catamorphism pinned by the spec relates each list to exactly `value base`
    of it: the derived fold IS the function `value`. -/
theorem cataR_value (base : Int) :
    ∀ (xs : SnocList Unit Int) (r : Int),
      cataR (graph (valAlg base)) xs r ↔ r = value base xs
  | SnocList.wrap u, r => value_wrap base u r
  | SnocList.snoc xs d, r => by
      rw [value_snoc]
      constructor
      · rintro ⟨r', hr', hr⟩
        rw [(cataR_value base xs r').mp hr'] at hr
        exact hr
      · intro hr
        exact ⟨value base xs, (cataR_value base xs (value base xs)).mpr rfl, hr⟩

/-- The derived fold equals the graph of `value base`. -/
theorem cataR_eq_graph_value (base : Int) :
    cataR (graph (valAlg base))
      = (graph (value base) : dSL Unit Int ⟶ (⟨Int⟩ : RelSet.{0})) :=
  hom_ext fun xs r => cataR_value base xs r

/-- **The derivation, packaged.**  The unique value-homomorphism at `base` is exactly the
    graph of the calculated program `value base`.  Read left-to-right: the abstract spec
    "commuting square" is met by one and only one relation, and it is the Horner program. -/
theorem value_hom_iff_graph (base : Int) (h : dSL Unit Int ⟶ (⟨Int⟩ : RelSet.{0})) :
    IsValueHom base h ↔ h = (graph (value base) : dSL Unit Int ⟶ (⟨Int⟩ : RelSet.{0})) := by
  rw [value_is_unique_hom, cataR_eq_graph_value]

/-! ############################################################################
    ## Part 2 — fold fusion, derived from the universal property
    ############################################################################ -/

section Fusion
universe u
variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜] {F : Relator 𝒜 𝒜}

/-- **Fold fusion (5.x).**  If a map `h` turns the algebra `φ` into `ψ` — the fusion
    condition `φ ≫ h = F h ≫ ψ` — then post-composing `h` after the catamorphism of `φ` is
    itself the catamorphism of `ψ`: `cata φ ≫ h = cata ψ`.  Derived from `relCata_cancel`
    (the catamorphism's own defining equation) and functoriality (`F.map_comp`), each `calc`
    line justified by exactly ONE law; then closed by the universal property `relCata_UP`. -/
theorem cata_fusion (I : InitialAlgebra F) {c d : 𝒜}
    (φ : F.obj c ⟶ c) (h : c ⟶ d) (ψ : F.obj d ⟶ d)
    (hcond : φ ≫ h = F.map h ≫ ψ) :
    relCata I φ ≫ h = relCata I ψ :=
  (relCata_UP I ψ (relCata I φ ≫ h)).mp <| by
    calc I.α ≫ (relCata I φ ≫ h)
        = (I.α ≫ relCata I φ) ≫ h := by rw [← Cat.assoc]
      _ = (F.map (relCata I φ) ≫ φ) ≫ h := by rw [relCata_cancel]
      _ = F.map (relCata I φ) ≫ (φ ≫ h) := by rw [Cat.assoc]
      _ = F.map (relCata I φ) ≫ (F.map h ≫ ψ) := by rw [hcond]
      _ = (F.map (relCata I φ) ≫ F.map h) ≫ ψ := by rw [← Cat.assoc]
      _ = F.map (relCata I φ ≫ h) ≫ ψ := by rw [← F.map_comp]

end Fusion

/-- Fold fusion specialised to SnocLists over `Unit`/`Int` and to the structural fold `cataR`
    (via `cataR_eq_relCata`), ready for the concrete Part-3 calculation. -/
theorem cataR_fusion {c d : RelSet.{0}} (φ : Fobj Unit Int c ⟶ c) (h : c ⟶ d)
    (ψ : Fobj Unit Int d ⟶ d) (hcond : φ ≫ h = (F Unit Int).map h ≫ ψ) :
    cataR φ ≫ h = cataR ψ := by
  rw [cataR_eq_relCata, cataR_eq_relCata]
  exact cata_fusion (initial Unit Int) φ h ψ hcond

/-! ############################################################################
    ## Part 3 — a new ALGEBRA emerges by solving the fusion equation
    ############################################################################ -/

/-- The post-map to fuse in: "multiply the running value by `k`". -/
def mulK (k : Int) : Int → Int := fun x => k * x

/-- The bifunctor action `F f` on the polynomial `F X = Unit + X × Int`, as an ordinary
    function on `F Int` (identity on the leaf, `f` on the recursive component).  Used only to
    state `Fmap_graph`. -/
def Fbimap (f : Int → Int) :
    (Fobj Unit Int (⟨Int⟩ : RelSet.{0})).carrier → (Fobj Unit Int (⟨Int⟩ : RelSet.{0})).carrier
  | Sum.inl u => Sum.inl u
  | Sum.inr p => Sum.inr (f p.1, p.2)

/-- `F` on a graph is the graph of the corresponding function action `Fbimap`. -/
theorem Fmap_graph (f : Int → Int) :
    (F Unit Int).map (graph f) = graph (Fbimap f) := by
  apply hom_ext; intro u v
  cases u with
  | inl u0 => cases v with
    | inl v0 =>
      constructor
      · intro _; exact congrArg Sum.inl (by cases u0; cases v0; rfl)
      · intro _; cases u0; cases v0; rfl
    | inr q => exact ⟨fun h => (h : False).elim, fun h => nomatch h⟩
  | inr p => cases v with
    | inl v0 => exact ⟨fun h => (h : False).elim, fun h => nomatch h⟩
    | inr q =>
      constructor
      · rintro ⟨h1, h2⟩
        have hq : q = (f p.1, p.2) := Prod.ext_iff.mpr ⟨h1, h2.symm⟩
        subst hq; rfl
      · intro h
        have hq : q = (f p.1, p.2) := Sum.inr.inj h
        subst hq; exact ⟨rfl, rfl⟩

/-- Diagram-order composition of two graphs is the graph of the composite function. -/
theorem graph_comp {a b c : RelSet.{0}} (f : a.carrier → b.carrier) (g : b.carrier → c.carrier) :
    graph f ≫ graph g = graph (fun x => g (f x)) :=
  hom_ext fun x z => ⟨fun ⟨y, hy, hz⟩ => hz.trans (congrArg g hy), fun hz => ⟨f x, rfl, hz⟩⟩

/-- **The emerged algebra.**  `scaleAlg base k` is the closed-form SOLUTION `ψ` of the fusion
    equation `valAlg base ≫ (k·) = F(k·) ≫ ψ`, obtained by solving that equation pointwise:
    on the `snoc` component the equation reads `ψ (k·a, d) = k·(base·a + d) = base·(k·a) + k·d`,
    whose only closed form (in the free variable `k·a`) is `(a', d) ↦ base·a' + k·d`; on `wrap`,
    `ψ _ = k·0 = 0`.  `scale_fusion_cond` below is the machine-checked verification that this
    `ψ` really solves the equation (so fold fusion fires) — the derivation content is the SOLVING,
    Lean confirms the solution.  Note the weight `k` lands on the *new* digit `d`, not on the
    whole running value: the algebra genuinely differs from `valAlg`. -/
def scaleAlg (base k : Int) : (Fobj Unit Int (⟨Int⟩ : RelSet.{0})).carrier → Int
  | Sum.inl _ => 0
  | Sum.inr p => base * p.1 + k * p.2

/-- **Solving the fusion equation.**  The fusion condition
    `graph (valAlg base) ≫ graph (mulK k) = F (graph (mulK k)) ≫ graph (scaleAlg base k)`
    holds — this is exactly the calculation that DERIVES `scaleAlg` (the only `ψ` in closed
    form making both sides agree pointwise).  Reduces, via `graph_comp`/`Fmap_graph`, to the
    scalar identity `k·(base·a + d) = base·(k·a) + k·d`. -/
theorem scale_fusion_cond (base k : Int) :
    graph (valAlg base) ≫ graph (mulK k)
      = (F Unit Int).map (graph (mulK k)) ≫ graph (scaleAlg base k) := by
  rw [graph_comp, Fmap_graph, graph_comp]
  have hfun : (fun u => mulK k (valAlg base u))
      = (fun u => scaleAlg base k (Fbimap (mulK k) u)) := by
    funext u
    cases u with
    | inl u0 => show k * 0 = 0; exact Int.mul_zero k
    | inr p =>
        show k * (base * p.1 + p.2) = base * (k * p.1) + k * p.2
        rw [Int.mul_add]
        congr 1
        calc k * (base * p.1) = (k * base) * p.1 := (Int.mul_assoc k base p.1).symm
          _ = (base * k) * p.1 := by rw [Int.mul_comm k base]
          _ = base * (k * p.1) := Int.mul_assoc base k p.1
  exact congrArg graph hfun

/-- **The derivation's payoff.**  Post-scaling the Horner fold by `k` IS the catamorphism of
    the emerged algebra `scaleAlg base k` — obtained by fold fusion, no induction:
    `value ≫ (k·) = cata (scaleAlg base k)`. -/
theorem scale_value_eq_cata (base k : Int) :
    cataR (graph (valAlg base)) ≫ graph (mulK k) = cataR (graph (scaleAlg base k)) :=
  cataR_fusion (graph (valAlg base)) (graph (mulK k)) (graph (scaleAlg base k))
    (scale_fusion_cond base k)

/-- The emerged program in point form: `scaleValue base k` is a multiply-accumulate whose
    step weights the NEW digit by `k`.  Its recursion equations are `cataFold`'s two
    equations at the derived algebra `scaleAlg base k` (`Iff.rfl`, below). -/
def scaleValue (base k : Int) : SnocList Unit Int → Int
  | SnocList.wrap _ => 0
  | SnocList.snoc xs d => base * scaleValue base k xs + k * d

theorem scaleValue_wrap (base k : Int) (u : Unit) (r : Int) :
    cataR (graph (scaleAlg base k)) (SnocList.wrap u) r ↔ r = 0 := Iff.rfl

theorem scaleValue_snoc (base k : Int) (xs : SnocList Unit Int) (d r : Int) :
    cataR (graph (scaleAlg base k)) (SnocList.snoc xs d) r
      ↔ ∃ r', cataR (graph (scaleAlg base k)) xs r' ∧ r = base * r' + k * d := Iff.rfl

theorem cataR_scaleValue (base k : Int) :
    ∀ (xs : SnocList Unit Int) (r : Int),
      cataR (graph (scaleAlg base k)) xs r ↔ r = scaleValue base k xs
  | SnocList.wrap u, r => scaleValue_wrap base k u r
  | SnocList.snoc xs d, r => by
      rw [scaleValue_snoc]
      constructor
      · rintro ⟨r', hr', hr⟩
        rw [(cataR_scaleValue base k xs r').mp hr'] at hr
        exact hr
      · intro hr
        exact ⟨scaleValue base k xs, (cataR_scaleValue base k xs _).mpr rfl, hr⟩

/-- **End-to-end sanity of the emerged program.**  `scaleValue base k xs = k * value base xs`:
    the fused program computes exactly the composite it was derived from.  This is a
    consequence (achieved by fusion, `scale_value_eq_cata`), NOT the definition of anything. -/
theorem scaleValue_correct (base k : Int) (xs : SnocList Unit Int) :
    scaleValue base k xs = k * value base xs := by
  have h : (graph (value base) ≫ graph (mulK k)) xs (scaleValue base k xs) := by
    rw [← cataR_eq_graph_value, scale_value_eq_cata]
    exact (cataR_scaleValue base k xs _).mpr rfl
  obtain ⟨m, hm, hr⟩ := h
  have hm' : m = value base xs := hm
  have hr' : scaleValue base k xs = k * m := hr
  rw [hr', hm']

end Freyd.Alg.RelSet.Deriv
