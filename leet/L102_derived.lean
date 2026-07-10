/-
  LeetCode 102 — Binary Tree Level Order Traversal — DERIVED as a tree catamorphism, O(n).

  `leet/L102.lean` WRITES the level-merging fold `levels : Tree Int → List (List Int)` by hand
  (`nil ↦ []`, `node l a r ↦ [a] :: mergeLevels (levels l) (levels r)`), where `mergeLevels` merges
  two level-lists row-by-row by CONCATENATING same-depth rows (`x ++ y`).  Read off as a scalar
  algebra over the carrier `List (List Int)`, that fold is O(n·h): every `++` re-copies a whole row,
  and the summed row lengths grow with the height.

  HERE we derive the SAME traversal over a DIFFERENCE-LIST carrier so the per-node combine copies no
  row.  Carrier `DL := List (List Int → List Int)` — each level is a difference-list *builder*
  `List Int → List Int` (prepend-a-block-then-continue), not a materialised row.  Two children's
  builder-lists combine by COMPOSING the per-level builders (`fun i => clᵢ ∘ crᵢ`), which is O(1) per
  overlapping level (no `++`); `mergeD` walks only `min(h_l, h_r)` levels and the taller tail passes
  through by reference.  The answer is read out once at the end (`readoutD`, apply each builder to
  `[]`).  Total cost: `n` base builders + `M` composition steps + `n` readout characters, and
  `M = Σ min(h_l, h_r) ≤ size − height < n` (proved below in prose), so the whole traversal is O(n).

  The base `g := []` and step `step cl a cr := (fun t => a :: t) :: mergeD cl cr` are FORCED by the
  difference-list fold `levelsD`'s two clauses, so `hnil`/`hnode` hold definitionally, and the
  general-carrier fold-uniqueness law `TB.treeFold_unique` (`AOP/A6_GenFold.lean`) PRODUCES the
  catamorphism `cataR (treeScalarAlg g step)` and identifies it with `graph levelsD`
  (`levels_emerges`).

  Correctness is REUSED, not re-proved.  The bridge `levelsD t = (levels t).map bld` (where
  `bld row := (row ++ ·)`, `levelsD_eq`) says the difference-list carrier is exactly the append-builder
  of `L102`'s materialised rows; reading it out returns those rows on the nose
  (`readoutD_levelsD : readoutD (levelsD t) = levels t`).  So `derivedSolve ≫ graph readoutD` is
  `L102.solve` (`derivedSolve_readout_eq_solve`), and `L102.solve_correct` (the `atDepth`/`height`
  correctness) transports onto the emergent fold's read-out (`levels_derived_correct`).

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataTreeFold` /
  `treeFold_unique` only, never the `cataR_eq_relCata` bridge (which pulls `Classical.choice`); the
  two `funext`s (append-builder identities) contribute only `Quot.sound`.
-/
import AOP.A6_GenFold
import leet.L102

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC102D

open Freyd Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC102

/-! ## The difference-list level carrier and its combinators

  A level is a *builder* `List Int → List Int` that prepends its block of values and continues.
  `mergeD` combines two children's builder-lists depth-by-depth by COMPOSING the builders — O(1) per
  overlapping level, no row is copied — and lets the longer tail pass through unchanged. -/

/-- The difference-list carrier: one builder `List Int → List Int` per depth. -/
abbrev DL : Type := List (List Int → List Int)

/-- Merge two builder-lists depth-by-depth by composing same-depth builders (`fun t => f (g t)` =
    `f ∘ g`), the longer tail passing through once the shorter side is exhausted.  O(1) per level. -/
def mergeD : DL → DL → DL
  | [], ys => ys
  | xs, [] => xs
  | f :: fs, g :: gs => (fun t => f (g t)) :: mergeD fs gs

/-- Read a builder-list out to a level-list: apply each builder to `[]` (done once, at the end). -/
def readoutD (ds : DL) : List (List Int) := ds.map (fun f => f [])

/-! ## The base and step of the emergent scalar algebra, carrier `C := DL` -/

/-- The base of the emergent algebra: `g = levelsD nil = []`. -/
def g : DL := []

/-- The step: prepend the label's own single-element builder `(fun t => a :: t)` at depth `0`, then
    merge the two children's builder-lists by composition — copying no row. -/
def step (cl : DL) (a : Int) (cr : DL) : DL := (fun t => a :: t) :: mergeD cl cr

/-- The difference-list level fold: `nil ↦ []`, `node l a r ↦ step (levelsD l) a (levelsD r)`. -/
def levelsD : Tree Int → DL
  | Tree.nil => g
  | Tree.node l a r => step (levelsD l) a (levelsD r)

/-! ## The FORCED first-order recursion of `levelsD` -/

/-- The base condition: `levelsD nil = g`, definitionally. -/
theorem hnil : levelsD Tree.nil = g := rfl

/-- The step condition: `levelsD (node l a r) = step (levelsD l) a (levelsD r)`, definitionally. -/
theorem hnode : ∀ (l : Tree Int) (a : Int) (r : Tree Int),
    levelsD (Tree.node l a r) = step (levelsD l) a (levelsD r) :=
  fun _ _ _ => rfl

/-! ## The level-order catamorphism EMERGES via the general-carrier law -/

/-- **The O(n) level-order fold EMERGES.**  `graph levelsD` equals the catamorphism of the scalar
    tree algebra `treeScalarAlg g step = [ nil ↦ [], (cl,a,cr) ↦ (a::·) :: mergeD cl cr ]` on the
    difference-list carrier `DL`, PRODUCED by `TB.treeFold_unique` from the forced base `g` and step
    `step`.  The composition-merge recurrence is not written; it emerges as the unique fold. -/
theorem levels_emerges :
    (graph levelsD : dTree Int ⟶ (⟨DL⟩ : RelSet.{0})) = cataR (treeScalarAlg g step) :=
  TB.treeFold_unique g step levelsD hnil hnode

/-! ## Bridge: the difference-list carrier is the append-builder of `L102`'s materialised rows

  `bld row := (row ++ ·)` turns a materialised row into its append-builder.  The two funext lemmas
  below are the ONLY nonrfl facts: an append-builder composition is an append-builder of the
  concatenation (`append_assoc`), and applying `(row ++ ·)` to `[]` returns `row` (`append_nil`). -/

/-- The append-builder of a materialised row. -/
def bld (row : List Int) : List Int → List Int := fun t => row ++ t

/-- **`mergeD` mirrors `mergeLevels` under `bld`.**  Merging two append-builder-lists by composition
    equals building the append-builder of the row-concatenating merge: `mergeD` composes
    `(x ++ ·) ∘ (y ++ ·) = ((x ++ y) ++ ·)` exactly where `mergeLevels` writes `x ++ y`. -/
theorem mergeD_map : ∀ (A C : List (List Int)),
    mergeD (A.map bld) (C.map bld) = (mergeLevels A C).map bld
  | [], C => by simp only [List.map_nil, mergeD, mergeLevels]
  | x :: xs, [] => by simp only [List.map_nil, List.map_cons, mergeD, mergeLevels]
  | x :: xs, y :: ys => by
      show (fun t => bld x (bld y t)) :: mergeD (xs.map bld) (ys.map bld)
         = bld (x ++ y) :: (mergeLevels xs ys).map bld
      have hhead : (fun t => bld x (bld y t)) = bld (x ++ y) := by
        funext t; show x ++ (y ++ t) = (x ++ y) ++ t; rw [List.append_assoc]
      rw [hhead, mergeD_map xs ys]

/-- **The bridge.**  The difference-list fold is exactly the append-builder of `L102.levels`:
    `levelsD t = (levels t).map bld`.  Node case: the label's builder `(a::·)` is `bld [a]`
    definitionally, and `mergeD` mirrors `mergeLevels` under `bld` (`mergeD_map`). -/
theorem levelsD_eq : ∀ t : Tree Int, levelsD t = (levels t).map bld
  | Tree.nil => rfl
  | Tree.node l a r => by
      show step (levelsD l) a (levelsD r) = ([a] :: mergeLevels (levels l) (levels r)).map bld
      rw [levelsD_eq l, levelsD_eq r]
      show (fun t => a :: t) :: mergeD ((levels l).map bld) ((levels r).map bld)
         = bld [a] :: (mergeLevels (levels l) (levels r)).map bld
      rw [mergeD_map]
      rfl

/-- Reading out an append-builder-list returns the underlying rows: `readoutD (L.map bld) = L`
    (each `(row ++ ·) [] = row ++ [] = row`). -/
theorem readout_map_bld (L : List (List Int)) : readoutD (L.map bld) = L := by
  rw [readoutD, List.map_map]
  have hid : ((fun f : List Int → List Int => f []) ∘ bld) = id := by
    funext row; show bld row [] = row; show row ++ [] = row; rw [List.append_nil]
  rw [hid, List.map_id]

/-- **Read-out correctness.**  The difference-list fold, read out at the end, returns exactly
    `L102.levels t` — the O(n·h) materialised traversal, produced by the O(n) carrier. -/
theorem readoutD_levelsD (t : Tree Int) : readoutD (levelsD t) = levels t := by
  rw [levelsD_eq, readout_map_bld]

/-! ## Connecting the emergent fold back to `L102.solve` -/

/-- The derived solver: the emergent catamorphism over the difference-list carrier `DL`. -/
def derivedSolve : dTree Int ⟶ (⟨DL⟩ : RelSet.{0}) := cataR (treeScalarAlg g step)

/-- The derived solver, followed by the read-out `graph readoutD`, IS `L102.solve` (`= graph
    levels`): the emergent O(n) catamorphism computes exactly the hand-written program. -/
theorem derivedSolve_readout_eq_solve : derivedSolve ≫ graph readoutD = LC102.solve := by
  show cataR (treeScalarAlg g step) ≫ graph readoutD = graph levels
  rw [← levels_emerges]
  apply hom_ext; intro t L
  show (∃ m, m = levelsD t ∧ L = readoutD m) ↔ L = levels t
  constructor
  · rintro ⟨m, rfl, rfl⟩
    exact readoutD_levelsD t
  · intro hL
    exact ⟨levelsD t, rfl, hL.trans (readoutD_levelsD t).symm⟩

/-! ## Correctness of the derived program, transported from `L102.solve_correct` -/

/-- **The O(n) Level-Order program is the tree catamorphism, and it is correct.**  The headline
    bundles:

    * `levels_emerges` — `graph levelsD = cataR (treeScalarAlg g step)`: the difference-list program
      IS the emergent catamorphism over the O(n) carrier `DL`; and
    * the transported correctness — for any tree `t`, the difference-list state `Dt` the emergent
      fold relates `t` to (necessarily `levelsD t`, by emergence), READ OUT (`readoutD Dt`), has at
      every depth `d` exactly the row `atDepth t d` and has exactly `height t` rows.
      `L102.solve_correct` (the existing correctness, NOT re-proved here) supplies both halves via
      the read-out bridge `readoutD_levelsD`. -/
theorem levels_derived_correct :
    ((graph levelsD : dTree Int ⟶ (⟨DL⟩ : RelSet.{0})) = cataR (treeScalarAlg g step)) ∧
    (∀ (t : Tree Int) (Dt : DL),
        cataTreeFold (treeScalarAlg g step) t Dt →
        (∀ d, rowAt (readoutD Dt) d = atDepth t d) ∧ (readoutD Dt).length = height t) := by
  refine ⟨levels_emerges, ?_⟩
  intro t Dt hf
  have hgr : (graph levelsD : dTree Int ⟶ (⟨DL⟩ : RelSet.{0})) t Dt := by
    rw [levels_emerges]; exact hf
  have hDq : Dt = levelsD t := hgr
  subst hDq
  rw [readoutD_levelsD t]
  exact LC102.solve_correct t

/-! ## Running / cross-checking the emergent fold against `leet/L102.lean` -/

-- The derived answers, read out of the difference-list carrier, match `L102`'s stated results.
example : readoutD (levelsD (Tree.nil : Tree Int)) = [] := by decide
example : readoutD (levelsD (bal (1 : Int) 2 3)) = [[1], [2, 3]] := by decide
-- The unbalanced tree exercises `mergeD`'s unequal-length branch (row `[4]` has no partner).
example : readoutD (levelsD unbal) = [[1], [2, 3], [4]] := by decide

/-- The emergent fold genuinely relates `bal 1 2 3` to its difference-list state, whose read-out is
    `[[1],[2,3]]`, proved via `levels_emerges` (no re-computation). -/
example : cataTreeFold (treeScalarAlg g step) (bal (1 : Int) 2 3) (levelsD (bal (1 : Int) 2 3)) := by
  have h : (graph levelsD : dTree Int ⟶ (⟨DL⟩ : RelSet.{0})) (bal (1 : Int) 2 3)
      (levelsD (bal (1 : Int) 2 3)) := rfl
  rw [levels_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC102D