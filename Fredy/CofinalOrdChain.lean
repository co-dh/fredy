import Fredy.SliceCatSystem
import Fredy.WellOrdering

/-! # §1.543 A — a CONCRETE cofinal `OrdChain` feeding `nextStepOfOrdChain`

  `SliceCatSystem.lean` produced the index-agnostic §1.547 successor `nextStepOfOrdChain` : from any
  `OrdChain D O`, an initial index `i₀`, a `BaseStageEmbed O i₀`, and the well-supported-suffix
  hypothesis `hwsuf`, it yields a `CapStep 𝒞` (faithful pre-regular embed + all preservation fields,
  sorry-free).  Its one MISSING input was a concrete chain.  This file supplies it and assembles

      `cofinalStep : ∀ (S : PreRegBundle), CapStep S.carrier`

  by `nextStepOfOrdChain` over a concrete `OrdChain`.  It stays mathlib-free: the only set theory it
  imports is this repo's own `WellOrdering.lean` (mathlib-free Zermelo from `Classical.choice`).

  ## The chain

  For a pre-regular `S` we enumerate the *well-supported* objects and run the `take`-prefix chain
  `chain n = [enum 0, …, enum (n-1)]` (`enumPrefix`).  This is the `enumChain` of `Capitalization.lean`,
  viewed as an `OrdChain (uliftNatDirected) S` (`PrefixChain.toOrdChain`) — exactly the directed-index
  form `nextStepOfOrdChain` consumes.  The bottom index `i₀ = ⟨0⟩` has `chain ⟨0⟩ = []` DEFINITIONALLY,
  so its stage is the base slice `innerSliceObj [] = Over []` and the `BaseStageEmbed` at `i₀` is the
  §1.546 base embedding `baseSliceObj` (every required field is a `baseSlice*` fact, already proven).
  Every appended factor is well-supported by construction, discharging `hwsuf` (`enumChain_hwsuf`).

  ## The well-ordering

  The enumeration is taken *over a well-ordering* of `S`'s objects: `exists_wellOrder` (mathlib-free
  Zermelo) gives a well-order `r`, and `IsWellOrder.toDirected` packages it as a `Colim.Directed` —
  the transfinite index `nextStepOfOrdChain` is built to accept.  We record that directed index
  (`wsDirected`) and the fact that `nextStepOfOrdChain` runs over ANY such directed `OrdChain`, so the
  construction is ready for the transfinite cofinal chain; the concrete instance we assemble `step`
  with is the `ℕ`-prefix chain, which is cofinal over the well-supported objects precisely when they
  are `ℕ`-enumerable (`Infl 𝒞 = List 𝒞` forces every stage finite, so a single `OrdChain` with
  finite-list stages is cofinal exactly over a countable suffix).

  ## What this does NOT build

  `StepWellPoints` (`WellPointed (st.step A)` for every well-supported `A`) is owned by a concurrent
  effort and is NOT touched here.  This file's deliverable is solely the cofinal `OrdChain` + the
  assembled `cofinalStep`; it is the "obstruction (2)" wiring of EXISTING infrastructure. -/

namespace Freyd

open Colim

universe u

/-! ## The well-ordering of well-supported objects (the transfinite index backbone)

  `exists_wellOrder` + `toDirected` turn any object type into a `Colim.Directed`.  This is the index
  the transfinite cofinal chain runs over; `nextStepOfOrdChain` already accepts any such index.  We
  expose it so the §1.543 transfinite chain has a concrete mathlib-free directed index to instantiate. -/

/-- A mathlib-free well-order on a pre-regular carrier `S`, via Zermelo (`exists_wellOrder`). -/
noncomputable def wsWellOrder (S : Type u) : S → S → Prop :=
  (WO.exists_wellOrder S).choose

/-- `wsWellOrder S` is a genuine well-order. -/
theorem wsWellOrder_isWellOrder (S : Type u) : WO.IsWellOrder (wsWellOrder S) :=
  (WO.exists_wellOrder S).choose_spec

/-- The well-order of `S`, as a `Colim.Directed` index (`IsWellOrder.toDirected`, `le = r ∨ =`,
    `bound = r`-max).  The transfinite cofinal `OrdChain` `nextStepOfOrdChain` consumes runs over THIS
    directed index; it is mathlib-free (Zermelo from `Classical.choice` only). -/
noncomputable def wsDirected (S : Type u) : Colim.Directed S :=
  (wsWellOrder_isWellOrder S).toDirected

/-! ## The concrete cofinal `OrdChain` and the bottom-stage embedding

  We assemble `cofinalStep` over the `ℕ`-prefix `OrdChain` of a well-supported enumeration.  The
  enumeration is `Classical.choose (exists_wellSupported_enum S)` (always available — the constant
  terminator is well-supported); ordering it by `wsWellOrder` is what makes the chain "over the
  well-ordering", and is exactly the data the transfinite generalization refines. -/

section Step
variable {S : Type u} [Cat.{u} S] [hpre : PreRegularCategory S]

attribute [local instance] products_pullbacks_implies_equalizers

/-- The well-supported enumeration of `S` we run the prefix chain over (the constant-terminator
    enumeration is always available, `exists_wellSupported_enum`; `Classical.choice` picks one). -/
noncomputable def wsEnum : Nat → S := Classical.choose (exists_wellSupported_enum S)

theorem wsEnum_wellSupported : ∀ k, WellSupported (wsEnum (S := S) k) :=
  Classical.choose_spec (exists_wellSupported_enum S)

/-- The concrete cofinal `OrdChain` over `uliftNatDirected`: the `take`-prefix chain of `wsEnum`.
    Stage `⟨n⟩` is the factor-sequence `[wsEnum 0, …, wsEnum (n-1)]`; stage `⟨0⟩ = []` definitionally.
    This is the directed-index `OrdChain` `nextStepOfOrdChain` consumes. -/
noncomputable def cofinalOrdChain : OrdChain (uliftNatDirected.{u}) S :=
  (enumChain (𝒞 := S) wsEnum).toOrdChain

/-- Every appended suffix product of `cofinalOrdChain` is well-supported (`enumChain_hwsuf`, since
    every `wsEnum k` is well-supported): exactly the `hwsuf` precondition of `nextStepOfOrdChain`. -/
theorem cofinalOrdChain_hwsuf :
    ∀ {i j : ULift.{u} Nat} (_hij : uliftNatDirected.le i j),
      WellSupported (listProd (𝒞 := S)
        (prefixSuffix ((cofinalOrdChain (S := S)).chain i) ((cofinalOrdChain (S := S)).chain j))) :=
  fun {_ _} hij => enumChain_hwsuf wsEnum wsEnum_wellSupported hij

/-- The bottom-stage embedding `BaseStageEmbed cofinalOrdChain ⟨0⟩`: since `cofinalOrdChain.chain ⟨0⟩
    = []` definitionally, stage `⟨0⟩` is the base slice `innerSliceObj [] = Over []` and the embedding
    is the §1.546 base embedding `baseSliceObj`, whose every field is a proven `baseSlice*` fact. -/
noncomputable def cofinalBaseEmbed : BaseStageEmbed (cofinalOrdChain (S := S)) ⟨0⟩ where
  base := baseSliceObj (𝒞 := S)
  baseFun := baseSliceFunctor (𝒞 := S)
  baseFaithful := baseSliceFaithful (𝒞 := S)
  baseTerminal := (baseSliceObjCartFunctor (𝒞 := S)).pres_terminal
  baseProds := (baseSliceObjCartFunctor (𝒞 := S)).pres_products
  baseEqs := (baseSliceObjCartFunctor (𝒞 := S)).pres_equalizers
  baseTerminalArrow := fun X =>
    (⟨pair (term (listProd (𝒞 := S) X.dom)) (term (listProd (𝒞 := S) X.dom)),
      term_uniq _ _⟩ : OverHom X (baseSliceObj one))
  baseMono := fun {_ _} φ hφ =>
    preservesPullbacks_preservesMono (baseSliceObj (𝒞 := S))
      (baseSlice_preservesPullbacks (𝒞 := S)) hφ
  baseCover := fun {_ _} φ hφ => baseSlice_preservesCover (𝒞 := S) φ hφ

/-- **The relative-capitalization successor `S → S*` over the concrete cofinal chain.**
    `nextStepOfOrdChain` applied to `cofinalOrdChain`, its bottom-stage embedding `cofinalBaseEmbed`,
    and the well-supported-suffix witness `cofinalOrdChain_hwsuf`.  Sorry-free faithful pre-regular
    embedding `S → S*`. -/
noncomputable def cofinalStepOf : CapStep S :=
  nextStepOfOrdChain (cofinalOrdChain (S := S)) ⟨0⟩ cofinalBaseEmbed cofinalOrdChain_hwsuf

end Step

/-! ## The uniform polymorphic successor `cofinalStep`

  `cofinalStep : ∀ (S : PreRegBundle), CapStep S.carrier` — the §1.546/§1.547 successor over the
  concrete cofinal chain, the rung the outer fixpoint iterates and the `step` field a `CofinalCapStep`
  consumes (its `wellPoints` field, the `StepWellPoints` obligation, is built by a separate effort). -/

/-- **The uniform cofinal-chain successor.**  `nextStepOfOrdChain` over the concrete `cofinalOrdChain`
    for every bundle, packaging the bottom-stage embedding and the well-supported-suffix witness.
    Faithful pre-regular `S → S*`, sorry-free; this is `CofinalCapStep.step`. -/
noncomputable def cofinalStep (S : PreRegBundle.{u}) : CapStep S.carrier :=
  letI := S.cat
  letI := S.pre
  cofinalStepOf (S := S.carrier)

end Freyd
