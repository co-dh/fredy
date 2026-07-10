/-
  LeetCode 617 — Merge Two Binary Trees — DERIVED from the GENERAL-CARRIER TREE FOLD LAW.

  `leet/L617.lean` WRITES the two-input recursion `mergeT : Tree Int → Tree Int → Tree Int` by hand
  and verifies it against the position-lookup spec (`merge_correct`).  HERE the single catamorphism
  EMERGES instead: we view `mergeT` as a fold over the FIRST tree whose carrier is the STRUCTURAL-
  OUTPUT function type `C := Tree Int → Tree Int` — a residual tree-transformer awaiting the second
  tree.  This is the two-input / higher-order carrier shape that the PRODUCT tupling laws
  (`A6_9_TreeTupling`) cannot express, but that `TB.treeFold_unique` (`A6_GenFold`, generic over the
  carrier `C`) handles directly.

  The base `g` and step `step` are READ OFF `LC617.mergeT`'s three defining clauses, curried:
    * `g := mergeT nil = fun t => t` — merging `nil` with `t` returns `t` verbatim; and
    * `step fl a fr` is the transformer `mergeT (node l a r)` expressed through `fl = mergeT l`,
      `fr = mergeT r`: on `nil` it keeps the lone node `node (fl nil) a (fr nil)` (= `node l a r`),
      on `node l' a' r'` it overlays `node (fl l') (a+a') (fr r')`.
  `mergeT` obeys the structural recursion `mergeT nil = g`, `mergeT (node l a r) = step (mergeT l) a
  (mergeT r)` (`hnil`, `hnode`; `hnode`'s `nil` case needs only `mergeT t nil = t`).  The general
  fold law `TB.treeFold_unique g step mergeT hnil hnode` then PRODUCES the single catamorphism
  `cataR (treeScalarAlg g step)` and identifies it with `graph mergeT` (`merge_emerges`) — the
  tree-transformer fold was never re-written by hand.  `merge_derived_correct` bundles this with
  `LC617.merge_correct` (reused, not re-proved): whatever transformer `f` the EMERGENT fold relates
  a tree `t1` to, `f = mergeT t1`, so `getPath (f t2) p = combine (getPath t1 p) (getPath t2 p)` at
  every position — the honest overlay semantics, on the derived program.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataTreeFold` /
  `treeFold_unique` only, never the `cataR_eq_relCata` bridge (which pulls `Classical.choice`).
-/
import AOP.A6_GenFold
import leet.L617

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC617D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC617

/-! ## The base and step, READ OFF `LC617.mergeT` (curried; carrier `Tree Int → Tree Int`) -/

/-- The base of the emergent algebra: `mergeT nil = fun t => t` — merging `nil` with any `t` returns
    `t` verbatim (`mergeT`'s first clause). -/
def g : Tree Int → Tree Int := fun t => t

/-- The step of the emergent algebra: the residual tree-transformer `mergeT (node l a r)` expressed
    through `fl = mergeT l`, `fr = mergeT r`.  Against `nil` it keeps the lone node (which is
    `node (mergeT l nil) a (mergeT r nil) = node l a r`); against `node l' a' r'` it overlays
    componentwise, summing the roots — exactly `mergeT`'s second/third clauses. -/
def step : (Tree Int → Tree Int) → Int → (Tree Int → Tree Int) → (Tree Int → Tree Int) :=
  fun fl a fr t => match t with
    | Tree.nil => Tree.node (fl Tree.nil) a (fr Tree.nil)
    | Tree.node l' a' r' => Tree.node (fl l') (a + a') (fr r')

/-! ## The FORCED structural recursion of `mergeT` -/

/-- `mergeT t nil = t` — `mergeT`'s second clause, needed as a lemma because the first argument is a
    variable (the `match` cannot reduce until it is known `nil`/`node`). -/
theorem mergeT_nil_right (t : Tree Int) : LC617.mergeT t Tree.nil = t := by
  cases t <;> rfl

/-- The base condition: `mergeT nil = g` (`= fun t => t`). -/
theorem hnil : LC617.mergeT Tree.nil = g := rfl

/-- The step condition: `mergeT (node l a r) = step (mergeT l) a (mergeT r)` — the problem's
    structural recurrence over the first tree, proved not defined.  On `node` inputs it is the raw
    third clause (`rfl`); on `nil` it needs `mergeT_nil_right` to fold `mergeT l nil`/`mergeT r nil`
    back to `l`/`r`. -/
theorem hnode (l a r : _) :
    LC617.mergeT (Tree.node l a r) = step (LC617.mergeT l) a (LC617.mergeT r) := by
  funext t
  cases t with
  | nil =>
      show Tree.node l a r
          = Tree.node (LC617.mergeT l Tree.nil) a (LC617.mergeT r Tree.nil)
      rw [mergeT_nil_right l, mergeT_nil_right r]
  | node l' a' r' => rfl

/-! ## The tree-transformer fold EMERGES via the general-carrier law -/

/-- **The two-input recursion EMERGES as a single catamorphism.**  `graph mergeT` — with carrier the
    structural-output function type `Tree Int → Tree Int` — equals the catamorphism of the emergent
    algebra `treeScalarAlg g step = [ nil ↦ (fun t => t), (fl,a,fr) ↦ step fl a fr ]`, PRODUCED by
    the general-carrier fold law from the forced base `g` and step `step`.  The residual
    tree-transformer fold was never written by hand. -/
theorem merge_emerges :
    (graph LC617.mergeT : dTree Int ⟶ ⟨Tree Int → Tree Int⟩) = cataR (treeScalarAlg g step) :=
  TB.treeFold_unique g step LC617.mergeT hnil hnode

/-! ## Correctness of the derived program, transported from `LC617.merge_correct` -/

/-- **The headline theorem.**  Correctness of the DERIVED program, bundling the emergence with the
    reused position-lookup correctness `LC617.merge_correct`.  Whatever tree-transformer `f` the
    EMERGENT fold relates a first tree `t1` to, `merge_emerges` pins `f = mergeT t1`; hence at every
    position `p` and for every second tree `t2`, `getPath (f t2) p = combine (getPath t1 p)
    (getPath t2 p)` — the honest overlay semantics, holding of the fold that emerged, not of a
    hand-written program. -/
theorem merge_derived_correct (t1 : Tree Int) (f : Tree Int → Tree Int)
    (hf : cataTreeFold (treeScalarAlg g step) t1 f) :
    ∀ (t2 : Tree Int) (p : List Bool),
      getPath (f t2) p = combine (getPath t1 p) (getPath t2 p) := by
  have hgr : (graph LC617.mergeT : dTree Int ⟶ ⟨Tree Int → Tree Int⟩) t1 f := by
    rw [merge_emerges]; exact hf
  have hfeq : f = LC617.mergeT t1 := hgr
  subst hfeq
  exact fun t2 p => LC617.merge_correct t1 t2 p

/-! ## Running / cross-checking the emergent fold against `leet/L617.lean`

  As in `L124_derived`, the relational catamorphism `cataTreeFold (treeScalarAlg …)` is not
  `decide`-computable (its `node` case is an existential over the function carrier), so we `decide`
  the extensionally-equal computable witness `mergeT` (equal by `merge_emerges`) applied to the
  second tree, on `L617`'s own example trees, and separately PROVE the fold relates a tree to its
  transformer.  `DecidableEq (Tree Int)` is the instance `L617` derives (imported). -/

/-- The emergent transformer `mergeT ex1`, applied to `ex2`, is `L617`'s stated example answer. -/
example : (LC617.mergeT LC617.ex1) LC617.ex2 = LC617.exMerged := by decide

/-- The `nil` base transformer is the identity on `ex2`. -/
example : (LC617.mergeT (Tree.nil : Tree Int)) LC617.ex2 = LC617.ex2 := by decide

/-- The emergent fold genuinely relates `ex1` to its tree-transformer `mergeT ex1` (which sends
    `ex2` to `exMerged`, the merged tree). -/
example : cataTreeFold (treeScalarAlg g step) LC617.ex1 (LC617.mergeT LC617.ex1) := by
  have h : (graph LC617.mergeT : dTree Int ⟶ ⟨Tree Int → Tree Int⟩)
      LC617.ex1 (LC617.mergeT LC617.ex1) := rfl
  rw [merge_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC617D
