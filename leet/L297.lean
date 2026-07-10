/-
  LeetCode 297 — Serialize and Deserialize Binary Tree — as an ALLEGORY PROGRAM, the
  SECTION–RETRACTION case.

  Problem: serialize a binary tree to a flat token list and deserialize it back, so that
  deserializing the serialization of any tree recovers that tree.

  This is the cleanest ALLEGORY framing of the Tree block: `serialize` is a `Map` (a function
  `dTree Int ⟶ dTokens` in `Rel(Set)`, `AOP.A6_1_RelSet`), `deserialize` a retraction of it, and
  the headline theorem is a SECTION–RETRACTION identity — `graph serialize ≫ graph deserialize =
  graph Option.some` on `dTree Int` — i.e. `deserialize` recovers exactly the tree that was
  serialized.

  1. **Tokens.** `Tok := Option Int` (`none` = null marker, `some a` = a node's label).
     `serialize` is the preorder listing `nil ↦ [none]`, `node l a r ↦ some a :: (serialize l ++
     serialize r)` — a plain structural fold (a catamorphism over `A6_TreeBin`'s `Tree`).

  2. **Parser.** `deserialize` inverts it by a preorder PARSE, but its SECOND recursive call (the
     right subtree) starts on the LEFTOVER of the first call (the left subtree's parse), not on a
     structural subterm of the token list — genuine well-founded recursion.  Tamed with a FUEL
     parameter `parseFuel : Nat → List Tok → Option (Tree Int × List Tok)` (the S13 trick): it
     recurses structurally on `fuel` alone, so it stays kernel-reducible and `decide` works.

  3. **Correctness (the real content).** The generalized round-trip lemma `parseFuel_serialize`:
     for ANY trailing tokens `rest` and any fuel bound `(serialize t).length ≤ fuel`, `parseFuel`
     applied to `serialize t ++ rest` reconstructs `t` exactly and returns `rest` untouched — "the
     parser inverts the printer with any trailing tokens", proved by structural induction on `t`.
     The `node` case chains the lemma TWICE: at `l` fed with `rest := serialize r ++ rest` (the
     right subtree's tokens are exactly `l`'s trailing tokens), then at `r` fed with the original
     `rest`.  Specializing `rest := []` gives `round_trip : deserializeFn (serialize t) = some t`,
     which `section_retraction` restates as the `Rel(Set)` identity above.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_TreeBin
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC297

open Freyd Freyd.Alg.RelSet.TB

-- Derived after the fact (not in `A6_TreeBin`, which stays `Rel(Set)`-only) so the `decide`
-- checks below have `DecidableEq (Tree Int)`.
deriving instance DecidableEq for Tree

/-! ## Tokens: `none` = null marker, `some a` = a node's label -/

abbrev Tok := Option Int

/-! ## The program, part 1: `serialize` — a preorder listing, a plain structural fold -/

/-- The preorder token listing: `nil ↦ [none]`, `node l a r ↦ some a :: (serialize l ++
    serialize r)`.  A plain structural recursion (a catamorphism over `A6_TreeBin`'s `Tree`). -/
def serialize : Tree Int → List Tok
  | Tree.nil => [none]
  | Tree.node l a r => some a :: (serialize l ++ serialize r)

/-! ## The program, part 2: `deserialize` — a preorder parse, needs FUEL (S13)

  The right subtree's parse starts on the LEFTOVER of the left subtree's parse, not a structural
  subterm of the token list — genuine well-founded recursion.  `parseFuel` tames it with an
  explicit fuel bound, recursing structurally on `fuel` alone so it stays kernel-reducible. -/

/-- `parseFuel fuel ts` — parse one tree off the front of `ts`, returning it together with the
    leftover tokens; `none` on malformed input or exhausted fuel.  `fuel` bounds the number of
    tokens the parse is allowed to consume. -/
def parseFuel : Nat → List Tok → Option (Tree Int × List Tok)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, none :: rest => some (Tree.nil, rest)
  | fuel + 1, some a :: rest =>
    match parseFuel fuel rest with
    | none => none
    | some (l, rest1) =>
      match parseFuel fuel rest1 with
      | none => none
      | some (r, rest2) => some (Tree.node l a r, rest2)

/-- **The allegory program's second half**: parse a whole token list, fuelled by its own length
    (always sufficient for a token list that came from `serialize` — `round_trip` below). -/
def deserializeFn (ts : List Tok) : Option (Tree Int) := (parseFuel ts.length ts).map Prod.fst

/-! ## Correctness: the parser inverts the printer, with ANY trailing tokens -/

/-- **The generalized round-trip lemma**: given fuel at least `(serialize t).length` and ANY
    trailing tokens `rest`, `parseFuel` applied to `serialize t ++ rest` reconstructs `t` exactly
    and returns `rest` untouched.  The `node` case chains this lemma TWICE: at `l` fed with
    `rest := serialize r ++ rest` (the right subtree's tokens are exactly `l`'s trailing tokens),
    then at `r` fed with the original `rest`. -/
theorem parseFuel_serialize : ∀ (t : Tree Int) (rest : List Tok) (fuel : Nat),
    (serialize t).length ≤ fuel → parseFuel fuel (serialize t ++ rest) = some (t, rest)
  | Tree.nil, rest, fuel, hf => by
    cases fuel with
    | zero => simp only [serialize, List.length_cons, List.length_nil] at hf; omega
    | succ fuel' => rfl
  | Tree.node l a r, rest, fuel, hf => by
    have hlen : (serialize (Tree.node l a r)).length
        = 1 + (serialize l).length + (serialize r).length := by
      show (some a :: (serialize l ++ serialize r)).length = _
      simp only [List.length_cons, List.length_append]; omega
    cases fuel with
    | zero => omega
    | succ fuel' =>
      have hl : (serialize l).length ≤ fuel' := by omega
      have hr : (serialize r).length ≤ fuel' := by omega
      have heq : serialize (Tree.node l a r) ++ rest
          = some a :: (serialize l ++ (serialize r ++ rest)) := by
        show (some a :: (serialize l ++ serialize r)) ++ rest = _
        rw [List.cons_append, List.append_assoc]
      rw [heq]
      simp only [parseFuel, parseFuel_serialize l (serialize r ++ rest) fuel' hl,
        parseFuel_serialize r rest fuel' hr]

/-- **The headline theorem**: deserializing the serialization of ANY tree recovers that tree
    exactly.  Specializes `parseFuel_serialize` at `rest := []`, fuelled by `(serialize t).length`
    (which `deserializeFn` always uses). -/
theorem round_trip (t : Tree Int) : deserializeFn (serialize t) = some t := by
  show (parseFuel (serialize t).length (serialize t)).map Prod.fst = some t
  have h : parseFuel (serialize t).length (serialize t ++ ([] : List Tok)) = some (t, []) :=
    parseFuel_serialize t [] (serialize t).length (Nat.le_refl _)
  rw [List.append_nil] at h
  rw [h]; rfl

/-! ## `Rel(Set)` framing: `serialize` is a section, `deserialize` its retraction -/

abbrev dTokens : RelSet.{0} := ⟨List Tok⟩
abbrev dOTree : RelSet.{0} := ⟨Option (Tree Int)⟩

/-- **The allegory program's first half**: `serialize` as a `Map` `dTree Int ⟶ dTokens`. -/
def solveSer : dTree Int ⟶ dTokens := graph serialize
/-- `solveSer` is a `Map` (it is the graph of a function). -/
theorem solveSer_map : Map solveSer := graph_map serialize

/-- **The allegory program's second half**: `deserialize` as a `Map` `dTokens ⟶ dOTree`. -/
def solveDes : dTokens ⟶ dOTree := graph deserializeFn
/-- `solveDes` is a `Map` (it is the graph of a function). -/
theorem solveDes_map : Map solveDes := graph_map deserializeFn

/-- **Section–retraction identity**: composing `serialize` then `deserialize` is exactly
    `some : Tree Int → Option (Tree Int)` — `deserialize` recovers exactly the tree that was
    serialized, no more, no less.  The `Rel(Set)` restatement of `round_trip`. -/
theorem section_retraction : solveSer ≫ solveDes = graph (fun t => some t) := by
  apply hom_ext; intro t ot
  show (∃ ts, ts = serialize t ∧ ot = deserializeFn ts) ↔ ot = some t
  constructor
  · rintro ⟨ts, rfl, rfl⟩; exact round_trip t
  · rintro rfl; exact ⟨serialize t, rfl, (round_trip t).symm⟩

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil
/-- A balanced height-2 tree: root `a` with leaf children `b`, `c`. -/
def bal (a b c : Int) : Tree Int := Tree.node (leaf b) a (leaf c)

example : serialize (leaf (5 : Int)) = [some 5, none, none] := by decide
example : deserializeFn (serialize (bal (1 : Int) 2 3)) = some (bal 1 2 3) := by decide
example : deserializeFn (serialize (Tree.nil : Tree Int)) = some Tree.nil := by decide
example : deserializeFn (serialize (Tree.node (leaf (1 : Int)) 2 Tree.nil)) =
    some (Tree.node (leaf (1 : Int)) 2 Tree.nil) := by decide

end Freyd.Alg.RelSet.LC297
