/-
  LeetCodeRunTree — TREE-shaped LeetCode problems RUN in the relation-algebra interpreter.

  `Fredy.RelInterp`'s `ProgEval` fragment (ground maps `fn`, diagram-order `comp`, recursion
  schemes) now has a binary-tree former `cataT`, evaluated by the structural fold `foldTB` —
  the tree counterpart of `cata`/`foldSL`.  Here every tree L-file's solution is re-wired as a
  `Prog` TERM whose recursion lives in `cataT` (the algebras are the L-files' own, transcribed
  to the uncurried `C → A → C → C` shape), and RUN by `evalP` on the L-files' own examples.

  HONEST FRAMING: this runs the existing tree programs (≈ `#eval`); the value is that the
  interpreter's applicative fragment now covers the tree functor, not just snoc-lists.

  Wired (14): L104 depth, L111 min-depth (sentinel fold), L110 balanced, L543 diameter,
  L124 max path sum, L226 invert, L100 same tree, L101 symmetric (banana-split + `mirror t t`),
  L112 path sum (nil-flag carrier), L572 subtree (needle-parameterised, calls the L100 term),
  L617 merge (banana-split, zip shape), L98 validate BST (bounds-function carrier),
  L102 level order, L297 serialize.

  Not expressible, and why:
  * L297 `deserialize` — a fuelled UNFOLD (anamorphism); the term language has `cata`/`cataT`
    only (`hyloF` is SL-functor-specific), so only the serialize half runs as a term.
  * `Prog` has no pairing/Δ former, so a term can never use its input twice.  Two-input
    problems (L100/L617, L572's needle) therefore run CURRIED — the fold's carrier is a
    function, applied to the second tree at the call site — and L101's "apply the mirror fold
    to the tree's own two children" is reshaped through the standard banana-split tupling
    (rebuild the input inside the carrier) plus `isSymmetric t = mirror t t`.
-/
import rel.RelInterp
import leet.L98
import leet.L100
import leet.L101
import leet.L102
import leet.L104
import leet.L110
import leet.L111
import leet.L112
import leet.L124
import leet.L226
import leet.L297
import leet.L543
import leet.L572
import leet.L617

namespace Freyd.Alg.FinRel.RunTree

open Freyd.Alg.FinRel.ProgEval
-- `Freyd.Alg.RelSet.TB` is the tree-infra NAMESPACE (`Tree` lives there); the interpreter
-- carrier `TB` is a TYPE (`ProgEval.TB`) — same surface name, no clash (only one is a constant).
open Freyd.Alg.RelSet Freyd.Alg.RelSet.TB

-- Derived here (not in `RelInterp`, which stays demo-free about `TB`) so the `decide` checks
-- below can compare tree-valued answers (L226, L617, L297 round-trip).
deriving instance DecidableEq for TB

/-- Transport an `A6_TreeBin` tree (the L-files' datatype, living in `Rel(Set)`) onto the
    interpreter carrier `TB` — lets every demo reuse the L-files' own example trees. -/
def ofTree {A : Type} : Tree A → TB A
  | Tree.nil        => .nil
  | Tree.node l a r => .node (ofTree l) a (ofTree r)

/-! ## L104 — maximum depth: the plain depth fold -/

/-- LC 104 as a term: `LC104.algFn`'s algebra, `nil ↦ 0`, `node ↦ 1 + max`. -/
def prog104 {A : Type} : Prog (TB A) Nat :=
  .cataT 0 fun dl _ dr => 1 + LC104.imax dl dr

example : evalP prog104 (ofTree (LC104.leaf (5 : Nat))) = 1 := by decide
example : evalP prog104 (ofTree (LC104.bal (1 : Nat) 2 3)) = 2 := by decide
example : evalP prog104 (ofTree (Tree.nil : Tree Nat)) = 0 := by decide
example : evalP prog104 (ofTree (Tree.node (LC104.leaf (1 : Nat)) 2 Tree.nil)) = 2 := by decide

/-! ## L111 — minimum depth: a SENTINEL structural fold

  `LC111.minDepthFn`'s own recursion branches four ways on the children's constructors, so it
  is not literally an algebra of the tree functor.  But `minDepthFn t = 0` iff `t = nil`
  (a non-`nil` tree's min-depth is ≥ 1), so the child depths themselves encode "child absent":
  the same function IS a structural fold with `0` read as the nil sentinel. -/

/-- LC 111 as a term: `nil ↦ 0`; at a node skip an absent (`= 0`) child, `min` over present ones. -/
def prog111 : Prog (TB Int) Nat :=
  .cataT 0 fun dl _ dr =>
    1 + (if dl = 0 then dr else if dr = 0 then dl else LC111.imin dl dr)

example : evalP prog111 (ofTree (Tree.nil : Tree Int)) = 0 := by decide
example : evalP prog111 (ofTree (Tree.node (LC111.leaf 2) 1 (LC111.leaf 3))) = 2 := by decide
-- the one-child trap: `node (leaf 2) 1 nil` has min-depth 2 (the lone child is NOT skipped to 1)
example : evalP prog111 (ofTree (Tree.node (LC111.leaf 2) 1 Tree.nil)) = 2 := by decide

/-! ## L110 — balanced: the tupled `(height, balanced)` fold, project the flag -/

/-- LC 110 as a term: `LC110.foldFn`'s algebra, then `Prod.snd`. -/
def prog110 : Prog (TB Int) Bool :=
  .comp
    (.cataT ((0, true) : Nat × Bool) fun cl _ cr =>
      (1 + LC110.imax cl.1 cr.1,
       cl.2 && cr.2 && decide (LC110.imax cl.1 cr.1 - LC110.imin cl.1 cr.1 ≤ 1)))
    (.fn Prod.snd)

example : evalP prog110 (ofTree (Tree.node (LC110.leaf 1) 2 (LC110.leaf 3))) = true := by decide
example : evalP prog110
    (ofTree (Tree.node (Tree.node (LC110.leaf 1) 2 Tree.nil) 3 Tree.nil)) = false := by decide
example : evalP prog110 (ofTree (Tree.nil : Tree Int)) = true := by decide

/-! ## L543 — diameter: the tupled `(height, diam)` fold, project the diameter -/

/-- LC 543 as a term: `LC543.foldFn`'s algebra, then `Prod.snd`. -/
def prog543 : Prog (TB Int) Nat :=
  .comp
    (.cataT ((0, 0) : Nat × Nat) fun cl _ cr =>
      (1 + LC543.imax cl.1 cr.1, LC543.imax (LC543.imax cl.2 cr.2) (cl.1 + cr.1)))
    (.fn Prod.snd)

example : evalP prog543
    (ofTree (Tree.node (Tree.node (LC543.leaf 4) 2 (LC543.leaf 5)) 1 (LC543.leaf 3))) = 3 := by
  decide
example : evalP prog543 (ofTree (LC543.leaf 1)) = 0 := by decide
example : evalP prog543 (ofTree (Tree.node (LC543.leaf 1) 2 Tree.nil)) = 1 := by decide

/-! ## L124 — maximum path sum: the tupled `(best, gain)` fold, project the best -/

/-- LC 124 as a term: `LC124.foldFn`'s algebra, then `Prod.fst`. -/
def prog124 : Prog (TB Int) (Option Int) :=
  .comp
    (.cataT ((none, 0) : Option Int × Int) fun cl a cr =>
      (LC124.omax (LC124.omax cl.1 cr.1)
         (some (a + LC124.imax 0 cl.2 + LC124.imax 0 cr.2)),
       a + LC124.imax 0 (LC124.imax cl.2 cr.2)))
    (.fn Prod.fst)

example : evalP prog124 (ofTree (Tree.node (LC124.leaf 1) 2 (LC124.leaf 3))) = some 6 := by decide
example : evalP prog124
    (ofTree (Tree.node (LC124.leaf (-10)) 2 (Tree.node (LC124.leaf 9) 20 (LC124.leaf 7))))
    = some 36 := by decide
example : evalP prog124 (ofTree (LC124.leaf (-3))) = some (-3) := by decide
example : evalP prog124 (ofTree (Tree.nil : Tree Int)) = none := by decide

/-! ## L226 — invert: the swap fold, tree-valued carrier -/

/-- LC 226 as a term: `LC226.algFn`'s swap algebra, `nil ↦ nil`, `(l,a,r) ↦ node r a l`. -/
def prog226 {A : Type} : Prog (TB A) (TB A) :=
  .cataT .nil fun l a r => .node r a l

example : evalP prog226 (ofTree LC226.asym) = ofTree LC226.asymMirror := by decide
example : evalP prog226 (evalP prog226 (ofTree LC226.asym)) = ofTree LC226.asym := by decide

/-! ## L100 — same tree: a function-carrier fold, run CURRIED

  `LC100.sameFn` recurses on both trees in lockstep.  As a term it is a fold over the FIRST
  tree whose carrier is `TB Int → Bool` (what to answer against any second tree); the second
  tree is applied at the call site — `Prog` has no pairing former, see the header. -/

/-- LC 100 as a term: fold the first tree to its structural-equality test. -/
def prog100 : Prog (TB Int) (TB Int → Bool) :=
  .cataT (fun s => match s with | .nil => true | _ => false)
    (fun fl a fr s => match s with
      | .nil => false
      | .node sl b sr => decide (a = b) && fl sl && fr sr)

example : evalP prog100 (ofTree (LC100.leaf 1)) (ofTree (LC100.leaf 1)) = true := by decide
example : evalP prog100 (ofTree (Tree.node (LC100.leaf 1) 2 (LC100.leaf 3)))
    (ofTree (Tree.node (LC100.leaf 1) 2 (LC100.leaf 4))) = false := by decide
example : evalP prog100 (ofTree (Tree.node (LC100.leaf 1) 2 Tree.nil))
    (ofTree (Tree.node (LC100.leaf 1) 2 (LC100.leaf 3))) = false := by decide

/-! ## L101 — symmetric: the crosswise-mirror fold, closed by banana-split

  The mirror check `LC101.mirrorFn` folds like L100 but CROSSWISE (left against right).  The
  L-file's wrapper applies it to the root's own children — input reuse `Prog` cannot express
  directly.  Reshape: a tree is symmetric iff it mirrors ITSELF (`mirrorFn t t`), and `t` is
  recoverable inside the fold by the banana-split tupling (second carrier component rebuilds
  the input), so the whole check IS one term. -/

/-- The crosswise-mirror fold, curried like `prog100`. -/
def progMirror : Prog (TB Int) (TB Int → Bool) :=
  .cataT (fun s => match s with | .nil => true | _ => false)
    (fun fl a fr s => match s with
      | .nil => false
      | .node sl b sr => decide (a = b) && fl sr && fr sl)

/-- LC 101 as a single-input term: banana-split `(mirror-test, rebuilt input)`, then self-apply. -/
def prog101 : Prog (TB Int) Bool :=
  .comp
    (.cataT (((fun s => match s with | .nil => true | _ => false), .nil) :
        (TB Int → Bool) × TB Int)
      (fun cl a cr =>
        ((fun s => match s with
            | .nil => false
            | .node sl b sr => decide (a = b) && cl.1 sr && cr.1 sl),
         .node cl.2 a cr.2)))
    (.fn fun p => p.1 p.2)

example : evalP prog101 (ofTree LC101.symTree) = true := by decide
example : evalP prog101 (ofTree LC101.asymTree) = false := by decide
-- the curried mirror fold agrees on the same instances, applied to the root's children
example : evalP progMirror (ofTree (Tree.node (LC101.leaf 3) 2 (LC101.leaf 4)))
    (ofTree (Tree.node (LC101.leaf 4) 2 (LC101.leaf 3))) = true := by decide

/-! ## L112 — path sum: a nil-flag carrier

  `LC112.hasPathSumFn` must tell an ABSENT child from a present one (a node with one `nil`
  child is not a leaf), so the carrier tuples an is-`nil` flag with the target test:
  when both flags are set the node is a leaf (`a = target`), otherwise recurse into the
  children — an absent child's test is constantly `false`, so it drops out of the `||`. -/

/-- LC 112 as a term: fold to `(is-nil, target ↦ has-path-sum)`, project the test. -/
def prog112 : Prog (TB Int) (Int → Bool) :=
  .comp
    (.cataT ((true, fun _ => false) : Bool × (Int → Bool))
      (fun cl a cr =>
        (false, fun target =>
          if cl.1 && cr.1 then decide (a = target)
          else cl.2 (target - a) || cr.2 (target - a))))
    (.fn Prod.snd)

-- the lone-child trap: the only root-to-leaf path of `node (node (leaf 3) 2 nil) 1 nil`
-- is `1→2→3`, summing to 6 (the root is NOT a leaf although its right child is `nil`)
example : evalP prog112
    (ofTree (Tree.node (Tree.node (LC112.leaf 3) 2 Tree.nil) 1 Tree.nil)) 6 = true := by decide
example : evalP prog112 (ofTree (Tree.node (LC112.leaf 1) 2 Tree.nil)) 1 = false := by decide

/-! ## L572 — subtree of another tree: a fold that calls the L100 term at every node

  `LC572.subFn` folds over the haystack and at every node runs the independent same-tree
  check.  The term mirrors that literally: banana-split rebuilds the current subtree, and the
  algebra's ground maps RUN the `prog100` term against the needle `t` (a term parameter). -/

/-- LC 572 as a term (needle `t` fixed): fold the haystack to `(rebuilt subtree, found)`. -/
def prog572 (t : TB Int) : Prog (TB Int) Bool :=
  .comp
    (.cataT ((.nil, evalP prog100 .nil t) : TB Int × Bool)
      (fun cl a cr =>
        ((.node cl.1 a cr.1 : TB Int),
         evalP prog100 (.node cl.1 a cr.1) t || cl.2 || cr.2)))
    (.fn Prod.snd)

example : evalP (prog572 (ofTree (Tree.node (LC572.leaf 4) 5 (LC572.leaf 6))))
    (ofTree (Tree.node (LC572.leaf 1) 2 (Tree.node (LC572.leaf 4) 5 (LC572.leaf 6))))
    = true := by decide
example : evalP (prog572 (ofTree (Tree.node (LC572.leaf 4) 5 (LC572.leaf 7))))
    (ofTree (Tree.node (LC572.leaf 1) 2 (Tree.node (LC572.leaf 4) 5 (LC572.leaf 6))))
    = false := by decide
example : evalP (prog572 (ofTree (Tree.nil : Tree Int))) (ofTree (Tree.nil : Tree Int))
    = true := by decide

/-! ## L617 — merge two trees: `zipWith`'s shape, run CURRIED via banana-split

  `LC617.mergeT` recurses on the first tree with the second matched inside — when the second
  runs out the FIRST subtree passes through verbatim, so the carrier tuples the rebuilt
  subtree with the merge function (banana-split again). -/

/-- LC 617 as a term: fold the first tree to `(rebuilt subtree, merge-with)`, project. -/
def prog617 : Prog (TB Int) (TB Int → TB Int) :=
  .comp
    (.cataT ((.nil, fun s => s) : TB Int × (TB Int → TB Int))
      (fun cl a cr =>
        ((.node cl.1 a cr.1 : TB Int), fun s =>
          match s with
          | .nil => .node cl.1 a cr.1
          | .node sl b sr => .node (cl.2 sl) (a + b) (cr.2 sr))))
    (.fn Prod.snd)

example : evalP prog617 (ofTree LC617.ex1) (ofTree LC617.ex2) = ofTree LC617.exMerged := by
  decide
example : evalP prog617 (ofTree (Tree.nil : Tree Int)) (ofTree LC617.ex2) = ofTree LC617.ex2 := by
  decide
example : evalP prog617 (ofTree LC617.ex1) (ofTree (Tree.nil : Tree Int)) = ofTree LC617.ex1 := by
  decide

/-! ## L98 — validate BST: a bounds-function carrier, closed by the initial bounds -/

/-- LC 98 as a term: fold to `lo hi ↦ within-bounds`, apply the unconstrained bounds
    (`LC98.within` with the accumulator turned into the fold's carrier). -/
def prog98 : Prog (TB Int) Bool :=
  .comp
    (.cataT ((fun _ _ => true) : Option Int → Option Int → Bool)
      (fun fl a fr lo hi =>
        (match lo with | none => true | some x => decide (x < a)) &&
        (match hi with | none => true | some y => decide (a < y)) &&
        fl lo (some a) && fr (some a) hi))
    (.fn fun f => f none none)

example : evalP prog98 (ofTree (Tree.node (LC98.leaf 1) 2 (LC98.leaf 3))) = true := by decide
example : evalP prog98 (ofTree (Tree.node (LC98.leaf 3) 2 (LC98.leaf 1))) = false := by decide
-- the grandparent trap: `4` under the right subtree violates the ROOT's lower bound `5`
example : evalP prog98
    (ofTree (Tree.node (LC98.leaf 1) 5 (Tree.node (LC98.leaf 4) 6 (LC98.leaf 7))))
    = false := by decide

/-! ## L102 — level order: the level fold -/

/-- LC 102 as a term: `nil ↦ []`, `node ↦ [a] :: mergeLevels`. -/
def prog102 : Prog (TB Int) (List (List Int)) :=
  .cataT [] fun Ll a Lr => [a] :: LC102.mergeLevels Ll Lr

example : evalP prog102 (ofTree (Tree.nil : Tree Int)) = [] := by decide
example : evalP prog102 (ofTree (LC102.bal 1 2 3)) = [[1], [2, 3]] := by decide
example : evalP prog102 (ofTree LC102.unbal) = [[1], [2, 3], [4]] := by decide

/-! ## L297 — serialize (the fold half; deserialize is an unfold, see the header) -/

/-- LC 297's serializer as a term: the preorder token listing. -/
def prog297 : Prog (TB Int) (List LC297.Tok) :=
  .cataT [none] fun sl a sr => some a :: (sl ++ sr)

example : evalP prog297 (ofTree (LC297.leaf 5)) = [some 5, none, none] := by decide
-- round-trip: the L-file's own (unfold) deserializer parses the term's output back
example : LC297.deserializeFn (evalP prog297 (ofTree (LC297.bal 1 2 3)))
    = some (LC297.bal 1 2 3) := by decide

end Freyd.Alg.FinRel.RunTree
