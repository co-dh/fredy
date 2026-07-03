/-
  Freyd & Scedrov, *Categories and Allegories* — §2.153 / §2.16(13): the category of
  ASSEMBLIES over a RECURSIVE modulus system is NOT effective, hence its effective
  reflection (§2.16(14)) is NOT an allegory of choice (AC).

  Book §2.153: "The category of assemblies is not effective."  "Rel(A) is a unitary
  tabular allegory, but not all equivalence relations split (as idempotents)."  Book
  §2.16(13): "if C is not effective then Ĉ is not AC."

  This is EXACTLY the assembly analogue of the recursive category R:
  `Fredy/S2_16_Recursive.lean` proves `Freyd.RecEff.reflection_not_ac`
  (`¬ CoversSplit (Spl(Eq (Rel ExtNat)))`) by feeding §1.572b's halting equivalence
  relation `ERel` (`ERel_not_effective`, ultimately `K_not_recursive`) into the general
  reflection theorem `not_coversSplit_of_not_effective` (§2.16c).

  ## What this file proves (Sorry-free)

  The REDUCTION `asmReflection_not_ac_of_nonsplitting`: the §2.16(13) machinery of
  `Fredy/S2_16c.lean` (`not_coversSplit_of_not_effective`), specialised to the tabular
  allegory `AsmRel K = Rel(Assembly K)` (tabular by §2.111 `relTabularAllegory`, since
  `Assembly K` is regular, §2.153 `asmRegular`).  It says: as soon as SOME assembly `A`
  over `K` carries an equivalence relation `I : A → A` in `Rel(A)` that does not split
  as a map, the effective reflection `E = Spl(Eq (Rel A))` of §2.16(14)
  (`AsmEffReflection K`, S2_16d) fails AC — covers do not all split there.

  This is the book's §2.153 non-effectiveness reduced to its combinatorial core: the
  single non-splitting equivalence relation.  It is the direct assembly mirror of
  `Freyd.RecEff.reflection_not_ac`, parameterised over the halting-relation witness.

  ## The remaining gap (NOT closed here) — and why

  To DISCHARGE the hypothesis of the reduction we would need a concrete non-splitting
  equivalence relation on a concrete assembly, i.e. the assembly analogue of `ERel`.
  Freyd's §2.153 obstruction is the halting problem, and it fires ONLY for the
  RECURSIVE modulus system: the representative-choosing section of the halting relation
  would be a K-tracked (hence recursive) function deciding the halting set, contradicting
  §1.572b `K_not_recursive`.

  The repo's ONLY concrete `ModulusSystem` is `ModulusSystem.allPartial` (§2.153), whose
  `mem` is `True` — ALL partial endofunctions, not just the recursive ones.  Over
  `allPartial` the obstruction VANISHES: the halting set's characteristic function is a
  total partial-endofunction, so it lies in `allPartial`, the representative choice is
  trackable, and `Rel(Assembly allPartial)` is in fact effective (its reflection is AC).
  This is the same phenomenon the module docstring of `S2_153_Assemblies` flags for the
  functor `∇` ("Over `allPartial` … the failure disappears").  Hence the literal target
  `¬ CoversSplit (AsmEffReflection allPartial)` is EXPECTED FALSE, and the honest headline
  must quantify over a RECURSIVE modulus system.

  A recursive `ModulusSystem` does not exist in the repo and cannot be built cheaply:
  `ModulusSystem` demands closure of `mem` under composition, pairing (`pairC`) and
  definition-by-cases (`casesC`) of PARTIAL functions, i.e. the closure theory of the
  PARTIAL recursive functions (dovetailing / s-m-n).  `Fredy/S1_572_Recursive.lean`
  provides only TOTAL recursive closure (`Recursive1.comp`, …) plus the μ-operator and
  the `acceptN` halting-witness checker (`Fredy/S1_572b_NotEffective.lean`); it has no
  closed class of partial-recursive graphs.  A total-recursive modulus system does not
  help either: the halting relation `ERel` is r.e. but not recursive, so its Rel(A)
  moduli are genuinely partial and it is not even NAMEABLE over a total-only `K`.

  Building the partial-recursive `ModulusSystem` (a multi-hundred-line computability
  development) is the exact missing piece; with it, `ERel` transports to an assembly
  relation and `asmReflection_not_ac_of_nonsplitting` closes §2.153 outright.

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, order `R ⊑ S`.
  Mathlib-free.
-/
import Fredy.S2_16d

universe u

namespace Freyd.Alg

open Cat

section AsmNonEffective

variable {K : ModulusSystem}

/-- **§2.153 / §2.16(13) for assemblies — the reduction.**
    If some assembly `A` over `K` carries an equivalence relation `I : A → A` in
    `Rel(A)` (reflexive, symmetric, transitive, in the book's §2.12 relational sense)
    that does NOT split as a map, then the effective reflection `E = Spl(Eq (Rel A))`
    of §2.16(14) is NOT an allegory of choice: covers do not all split in `E`.

    This is `not_coversSplit_of_not_effective` (§2.16c, the book's "hence if C is not
    effective then Ĉ is not AC") instantiated at the tabular allegory
    `AsmRel K = Rel(Assembly K)`.  It is the direct assembly analogue of
    `Freyd.RecEff.reflection_not_ac`, awaiting the halting-relation witness `I`
    (see the module docstring for why that witness needs the recursive modulus system). -/
theorem asmReflection_not_ac_of_nonsplitting {A : Assembly.{u} K}
    (I : (⟨A⟩ : AsmRel K) ⟶ ⟨A⟩)
    (hrefl : Reflexive I) (hsym : Symmetric I) (htrans : Transitive I)
    (hno : ∀ (d : AsmRel K) (f : (⟨A⟩ : AsmRel K) ⟶ d), ¬ SplitsAsMap f I) :
    ¬ CoversSplit (AsmEffReflection.{u} K) := by
  -- Pre-compute each hypothesis so its universes pin to `I` (letting `𝒜 = AsmRel K`
  -- be inferred, not annotated).  `Reflexive I` is defeq `Cat.id ⟨A⟩ ⊑ I`.
  have hr : Cat.id (⟨A⟩ : AsmRel K) ⊑ I := hrefl
  have hs : I° = I := symmetric_eq hsym
  have hidem : I ≫ I = I := reflexive_transitive_idempotent hrefl htrans
  exact not_coversSplit_of_not_effective (𝒜 := AsmRel.{u} K) I hr hs hidem hno

/-- **§2.153 non-effectiveness (packaged existential).**  The reflection `E` of
    `Rel(Assembly K)` fails AC as soon as `Rel(Assembly K)` is not effective, witnessed
    by ANY non-splitting equivalence relation on some assembly over `K`.  The hypothesis
    is exactly "`Rel(A)` has an equivalence relation that is not the level of a cover"
    (§2.153: "not all equivalence relations split as idempotents"). -/
theorem asmReflection_not_ac_of_notEffective
    (hne : ∃ (A : Assembly.{u} K) (I : (⟨A⟩ : AsmRel K) ⟶ ⟨A⟩),
      Reflexive I ∧ Symmetric I ∧ Transitive I ∧
      ∀ (d : AsmRel K) (f : (⟨A⟩ : AsmRel K) ⟶ d), ¬ SplitsAsMap f I) :
    ¬ CoversSplit (AsmEffReflection.{u} K) := by
  obtain ⟨A, I, hrefl, hsym, htrans, hno⟩ := hne
  exact asmReflection_not_ac_of_nonsplitting I hrefl hsym htrans hno

end AsmNonEffective

end Freyd.Alg
