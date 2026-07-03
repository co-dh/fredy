import Fredy.S1_1
import Fredy.S1_24
import Fredy.S1_39
import Fredy.S1_8
import Fredy.S1_9
import Fredy.S1_18
import Fredy.S1_81
import Fredy.S1_85
import Fredy.S1_97_ToposDistributive
import Fredy.S1_91
import Fredy.S1_92
import Fredy.S1_934_PartialMapClassifier
import Fredy.S1_94
import Fredy.S1_97
import Fredy.S1_26
import Fredy.S1_27
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_44
import Fredy.S1_438_FunctorReflects
import Fredy.S1_45
import Fredy.S1_47
import Fredy.S1_444_Horn
import Fredy.S1_421_Initial
import Fredy.S1_51
import Fredy.S1_513_CoveringFamily
import Fredy.S1_52
import Fredy.S1_53
import Fredy.S1_53_SliceRegular
import Fredy.S1_93_SliceTopos
import Fredy.S1_93_SlicePower
import Fredy.S1_931_SlicePi
import Fredy.S1_532_SliceDeltaCartesian
import Fredy.S1_53_BaseChangeDescent
import Fredy.S1_55
import Fredy.S1_36
import Fredy.S1_54
import Fredy.S1_58
import Fredy.S1_59
import Fredy.S1_595_AbCategory
import Fredy.S1_594_AbAbelian
import Fredy.S1_595_AbRegular
import Fredy.S1_596_AbFunctorCategory
import Fredy.S1_59_ExactRepresentation
import Fredy.S1_60
import Fredy.S1_70
import Fredy.S1_59_10_Frobenius
import Fredy.S1_56
import Fredy.S1_568_Quot
import Fredy.S1_57
import Fredy.S1_572_Recursive
import Fredy.S1_572b_NotEffective
import Fredy.S1_573_PrimRec
import Fredy.S1_62
import Fredy.S1_64
import Fredy.S1_65
import Fredy.S1_662_Diaconescu
import Fredy.S1_72
import Fredy.S1_14
import Fredy.S1_74
import Fredy.S1_75
import Fredy.S1_77
import Fredy.S1_82
import Fredy.S1_84
import Fredy.S1_95
import Fredy.S1_943_ToposRTC
import Fredy.S1_95_ToposColimits
import Fredy.S1_967_ToposIndexedJoins
import Fredy.S1_967_ToposExists
import Fredy.S1_967_ToposCopowers
import Fredy.S1_543_DirectedColimit
import Fredy.S1_543_WellOrdering
import Fredy.S1_543_CatColimit
import Fredy.S1_543_CatColimitRegular
import Fredy.S1_543_Capitalization
import Fredy.S1_543_CapitalizationTransfinite
import Fredy.S1_541_RelativeCapitalization
-- §1.543 capitalization: the FULL sorry-free closure of `Freyd.capData_exists`.  `CapDataWiring`
-- discharges `∀ A, Nonempty (CapData A)` by the §1.547 uniform cofinal successor (`uniformStep`) plus
-- the §1.546 fibre-density obligation, and transitively imports the whole cofinal-route stack:
--   UniformCapStep → UniformWellPoints → FibreDensityProof → CapDataWiring (all sorry-free).
-- `capData_exists`/`capitalization_lemma` are LIVE here; `#print axioms` = [propext, Classical.choice,
-- Quot.sound].  (The alternative §1.547 `PairObj` route — `RationalCapitalization`/`SliceWellPointed` —
-- is NOT imported; it carried isolated sorries and is unreachable from this chain.)
import Fredy.S1_543_CapitalizationLaxColimit
import Fredy.S1_543_LaxColimitPreReg
import Fredy.S1_543_CofinalHstage
import Fredy.S1_543_RatCapPreReg
import Fredy.S1_543_RatCapHcanon
import Fredy.S1_543_RatCapStagePTC
import Fredy.S1_547_CofinalProjSystem
import Fredy.S1_547_UniformCapStep
import Fredy.S1_543_UniformWellPoints
import Fredy.S1_546_FibreDensityProof
import Fredy.S1_543_CapDataWiring
import Fredy.S1_543_LaxColimitImages
import Fredy.S1_543_LaxColimitCoproduct
import Fredy.S1_543_LaxGermProducts
import Fredy.S1_543_LaxGermImages
import Fredy.S1_543_LaxGermEqualizers
import Fredy.S1_543_LaxGermPullbacks
import Fredy.S1_543_LaxGermCoproduct
import Fredy.S1_61_LaxStrictInitial
import Fredy.S1_63_LaxInvImageUnion
import Fredy.S1_621_LaxDisjoint
import Fredy.S1_63_LaxColimitPositive
import Fredy.S2_218_RatCapPositive
import Fredy.S2_218_CapDataPositive
import Fredy.S1_547_UniformStepCoproduct
import Fredy.S2_218_CapDataPositiveTower
import Fredy.S1_543_RatCapImages
import Fredy.S1_543_CapDataRegular
import Fredy.S2_218_PowerAllegoryFamily
import Fredy.S1_635_StalkFamily
import Fredy.S1_635_StalkDetect
import Fredy.S1_634_TstarRegular
import Fredy.S1_635_TstarConservative
import Fredy.S1_635_StalkRepr
import Fredy.S1_543_UnionFromCoproduct
import Fredy.S1_621_ColimitPositive
import Fredy.S1_543_ColimitCoproductGerm
import Fredy.S1_63_ColimitInvImageUnion
import Fredy.S2_218_ColimitPreLogos
import Fredy.S1_544_Inflation
import Fredy.S2_1
import Fredy.S2_16
import Fredy.S2_2
import Fredy.S2_22
import Fredy.S2_16b
import Fredy.S2_16c
import Fredy.S2_55
import Fredy.S2_43
import Fredy.S2_433_SplEqInstance2
import Fredy.S2_42
import Fredy.S2_3
import Fredy.S2_31
import Fredy.S2_11
import Fredy.S2_4
import Fredy.S2_44
import Fredy.S2_417_Generator
import Fredy.S2_417b_NotPower
import Fredy.S2_441_StraightJoin
import Fredy.S2_5
import Fredy.S2_51
import Fredy.S2_53
import Fredy.S2_54
import Fredy.S2_52
import Fredy.S2_34
import Fredy.S1_38b
import Fredy.S1_637_FiniteSeparation
import Fredy.S1_646_Representation
import Fredy.S1_13
import Fredy.S1_10
import Fredy.S1_422_FunctorCategory
import Fredy.S2_147_MapCat
import Fredy.S2_165_Spl
import Fredy.S2_216_MatrixAllegory
import Fredy.S1_723_Locale
import Fredy.S2_168_ValuedSetsTabular
import Fredy.S2_111_RelCat
import Fredy.S2_154_CategoriesIso
import Fredy.S2_41
import Fredy.S2_41b
import Fredy.S2_424_ConnectedPowerTopos
import Fredy.S2_21
import Fredy.S2_21b
import Fredy.S2_21c
import Fredy.S1_526_StalkConservative
import Fredy.S2_153_Assemblies
import Fredy.S2_16d
import Fredy.S2_16e_TwoPresentations
import Fredy.S2_16_Recursive
import Fredy.S2_153_NonEffective
import Fredy.S2_153b_RecursiveModulus
import Fredy.S2_153c_ConcreteNonEffective
import Fredy.S2_155_BiEntire
import Fredy.S2_156_PartitionRep
import Fredy.S2_157_ProjectivePlane
import Fredy.S2_157b_Desargues
import Fredy.S2_157c_Converse
import Fredy.S2_157d_HornTop
import Fredy.S2_157e_HornCenter
import Fredy.S2_157f_HornLine
import Fredy.S2_157g_ConverseHeadline
import Fredy.S2_158_GraphAllegory
import Fredy.S2_158b_NoFiniteAxiom
import Fredy.S2_33
import Fredy.S1_631_CapitalProjective
-- Bird & de Moor, Algebra of Programming, ch. 4 (only material not already in Freyd S2_*)
import Fredy.A4_1
import Fredy.A4_2
import Fredy.A4_3
import Fredy.A4_4
import Fredy.A4_5
import Fredy.A4_6
-- Bird & de Moor ch. 5: relators and datatypes in allegories
import Fredy.A5_1
import Fredy.A5_2
import Fredy.A5_3
import Fredy.A5_4
import Fredy.A5_5
import Fredy.A5_6
import Fredy.A5_7
-- Bird & de Moor ch. 6: recursive programs (fixed points, hylomorphisms, closure)
import Fredy.A6_2
import Fredy.A6_3
import Fredy.A6_5
import Fredy.A6_7
-- Bird & de Moor ch. 7: optimisation problems (min/max, monotonic algebras, greedy theorem)
import Fredy.A7_1
import Fredy.A7_2
-- Bird & de Moor ch. 8: thinning algorithms (thin, thinning theorem)
import Fredy.A8_1
-- Bird & de Moor ch. 9: dynamic programming (principle of optimality, DP + thinning theorems)
import Fredy.A9_1
-- Bird & de Moor ch. 10: greedy algorithms (Theorem 10.1 — greedy as extreme dynamic programming)
import Fredy.A10_1
-- Concrete model Rel(Set) for the AoP case studies (objects = types, morphisms = relations):
-- the full allegory stack (power/LCDA/tabular/unitary) in which the §6.1+ programs actually run.
import Fredy.A6_1_RelSet
-- Bird & de Moor §6.1: Digits of a number — Decimal as an initial algebra of `F A = Digit⁺ + A×Digit`,
-- the reading catamorphism `val`, and the recursive equation for `val°` (first worked AoP program).
import Fredy.A6_1_Digits
-- Generic snoc-list datatype `SnocList L E = L + (·)×E` as an initial algebra (reusable engine).
import Fredy.A6_SnocList
-- Bird & de Moor §6.4: fast exponentiation/modulus — `exp`/`mod` as hylomorphisms over the binary
-- datatype `Bin = SnocList Unit Bit`, giving the O(log) divide-and-conquer least fixed point.
import Fredy.A6_4_FastExp
-- Generic cons-list `ConsList L E = L + E×(·)` (head/tail) as an initial algebra; `list A = ConsList Unit A`.
import Fredy.A6_ConsList
-- Bird & de Moor §6.6: sorting by selection — `sort = ⦇[nil, select°]⦈°` (converse of a catamorphism)
-- with its recursion; correctness `sort ⊆ ordered·perm` by fusion (given the select proviso).
import Fredy.A6_6_Sort
-- Bird & de Moor §7.3: planning a company party — `choose` monotonicity + party planning solved by
-- the greedy theorem (`greedy_max`); the rose-tree datatype `tree A = node(A, list(tree A))` deferred.
import Fredy.A7_3_Party
-- Bird & de Moor §5.6: combinatorial list relations — perm/prefix/subseq/inlist over `list A = ConsList
-- Unit A`, with reflexivity/symmetry/transitivity (the coalgebra/spec layer for the case studies).
import Fredy.A5_6_ListCombinators
-- Bird & de Moor §6.6 FULLY CONCRETE: selection sort correctness with NO hypotheses — concrete
-- `select`/ordered algebra + the fusion proviso discharged via the §5.6 `perm`/`inlist`.
import Fredy.A6_6b_SortConcrete
-- Bird & de Moor §10.2: detab-entab — the tupled catamorphism `(detab, col·detab) = ⦇[base,step]⦈`
-- over snoc-lists of chars, with its loop recursion (base/step case).
import Fredy.A10_2_Detab
-- Bird & de Moor §8.4: the knapsack problem — binary thinning; `knapsack_thinning` = the thinning
-- theorem `thinning_min` instantiated (selections=subsequences, order by value, thin by weight).
import Fredy.A8_4_Knapsack
-- Bird & de Moor case studies §7.4–§10.4 (each = the relevant abstract optimisation theorem —
-- greedy/thinning/DP — instantiated for the problem; concrete problem-specific data deferred).
import Fredy.A7_4_Cylinder
import Fredy.A7_5_SecurityVan
import Fredy.A8_2_LayeredNetwork
import Fredy.A8_3_ImplementingThin
import Fredy.A8_5_Paragraph
import Fredy.A8_6_Bitonic
import Fredy.A9_2_StringEdit
import Fredy.A9_3_Bracketing
import Fredy.A9_4_Compression
import Fredy.A10_3_Tardiness
import Fredy.A10_4_TeX
-- LeetCode 121 (Best Time to Buy and Sell Stock) — programmed in the allegory Rel(Set): the O(n)
-- scan as a snoc-list catamorphism, proven equal to max(≤)·Λspec.  Uses the copied `exacts` tactic.
import Fredy.Exacts
import Fredy.L121
