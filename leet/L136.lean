/-
  LeetCode 136 — Single Number — as an ALLEGORY PROGRAM: an XOR-CANCELLATION fold.

  Problem: given a non-empty list of `Nat`s in which every value appears exactly twice except one,
  which appears exactly once, return that one value.

  This reuses the `L191` recipe (count-catamorphism, state-is-answer, no trailing projection) but
  swaps the fold's monoid: instead of `Nat`-addition counting `true` bits, `xorFn` XORs (`^^^`)
  every element together. `Nat.xor` makes `(Nat, ^^^, 0)` a commutative group in which every
  element is its own inverse (`x ^^^ x = 0`, `Nat.xor_self`), so a value paired with itself cancels
  to `0` regardless of what else is folded around it (`Nat.xor_assoc`) — the running fold "forgets"
  every value that occurs an even number of times and keeps exactly the odd one out.

  1. **Data** — a list is `Nums := dSL Nat Nat` (`A6_SnocList`'s engine, leaf type = element type =
     `Nat`; `wrap x` a singleton, `snoc xs p` appends one more value).

  2. **Program** — `xorFn` folds `Nat.xor` over every element by structural recursion, packaged as
     `solve : Nums ⟶ dNat := graph solveFn` and proved equal to `cataR alg` (`solve_eq_cata`), as in
     `L191`: the fold's running state IS the answer, no trailing projection.

  3. **Specification with precondition** — `PairedExceptOne xs m` (inductive): `xs` is built from a
     `wrap m` base by repeatedly appending a matched pair (`snoc (snoc xs p) p`), i.e. `xs`'s
     multiset is `m` plus some elements each occurring an even number of times, and `m` is the
     unique odd-count element. `solve_correct` shows `solveFn xs = m` under this hypothesis.

     SCOPE NOTE (the task's sanctioned fallback, taken here): `PairedExceptOne` builds `xs` with
     `m` as the very FIRST element and every pair appended immediately (adjacently) after it; it
     does NOT allow the paired elements and the singleton `m` to be freely interleaved in an
     arbitrary order — that would need a hand-rolled multiset/permutation theory (no
     `Multiset`/`List.Perm`, mathlib-free) to convert an arbitrary count-parity hypothesis into
     canonical form, which is the genuinely heavy part of this problem. `Nat.xor` itself IS already
     order-independent (commutative + associative, see `xorFn_pair_cancel`); only the SPEC's shape
     — not the algorithm or the cancellation algebra — is scoped down.

  4. **Correctness** — `solve_correct : PairedExceptOne xs m → solveFn xs = m`, by induction on the
     `PairedExceptOne` derivation; the `pair` case is exactly the cancellation lemma
     `xorFn_pair_cancel`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC136

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: a non-empty list of `Nat`s as a snoc-list -/

/-- The object of `Nat`-lists in `Rel(Set)` (`wrap x` = singleton, `snoc xs p` = `xs` with one more
    value appended). -/
abbrev Nums : RelSet.{0} := dSL Nat Nat
/-- The object of `Nat` answers in `Rel(Set)`. -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## The program: the XOR fold, packaged as a catamorphism -/

/-- The fold algebra `[ x ↦ x, (n,p) ↦ n ^^^ p ] : F(ℕ) → ℕ`. -/
def algFn : (Fobj Nat Nat (dNat : RelSet.{0})).carrier → Nat
  | Sum.inl x => x
  | Sum.inr (n, p) => n ^^^ p

/-- The algebra as a morphism (a `Map`) `F(ℕ) ⟶ ℕ` in `Rel(Set)`. -/
def alg : Fobj Nat Nat (dNat : RelSet.{0}) ⟶ dNat := graph algFn

/-- The concrete fold (structural recursion): XOR every element together. -/
def xorFn : SnocList Nat Nat → Nat
  | SnocList.wrap x => x
  | SnocList.snoc xs p => xorFn xs ^^^ p

/-- The answer IS the fold's state — no projection needed (as `L191`, contrast `L121`'s pair). -/
def solveFn : SnocList Nat Nat → Nat := xorFn

/-- **The allegory program**: LeetCode 136's solution as a morphism `Nums ⟶ ℕ` in `Rel(Set)`. -/
def solve : Nums ⟶ dNat := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree. -/
theorem cataFold_alg : ∀ (xs : SnocList Nat Nat) (r : Nat),
    cataFold alg xs r ↔ r = xorFn xs := by
  intro xs; induction xs with
  | wrap x => intro r; exact Iff.rfl
  | snoc xs p ih =>
    intro r
    simp only [cataFold_snoc]
    constructor
    · rintro ⟨r', hr', hfr⟩
      rw [ih r'] at hr'; subst hr'; exact hfr
    · intro h; exact ⟨xorFn xs, (ih (xorFn xs)).mpr rfl, h⟩

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈`, with NO trailing projection — the
    fold's running state already IS the answer (contrast L121's `≫ snd`). -/
theorem solve_eq_cata : solve = cataR alg := by
  apply hom_ext; intro xs v
  show v = solveFn xs ↔ cataFold alg xs v
  exact (cataFold_alg xs v).symm

/-! ## The XOR-cancellation core lemma -/

/-- **The core algebraic fact**: appending a matched pair to a fold leaves it unchanged — `x ^^^ x
    = 0` (`Nat.xor_self`) cancels the pair via associativity, regardless of what the fold had
    accumulated so far. -/
theorem xorFn_pair_cancel (xs : SnocList Nat Nat) (p : Nat) :
    xorFn (SnocList.snoc (SnocList.snoc xs p) p) = xorFn xs := by
  show (xorFn xs ^^^ p) ^^^ p = xorFn xs
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-! ## Spec: everyone pairs off except the one, `m` -/

/-- **`PairedExceptOne xs m`** — `xs`'s multiset is `m` plus some elements each occurring an even
    number of times: built from a `wrap m` base (`base`) by repeatedly appending a matched pair
    (`pair`). `m` is the unique odd-count element (SCOPE: `m` sits first, pairs are appended after
    it — see the file docstring). -/
inductive PairedExceptOne : SnocList Nat Nat → Nat → Prop
  | base (m : Nat) : PairedExceptOne (SnocList.wrap m) m
  | pair {xs : SnocList Nat Nat} {m p : Nat} (h : PairedExceptOne xs m) :
      PairedExceptOne (SnocList.snoc (SnocList.snoc xs p) p) m

/-- **Correctness of the allegory program**: under `PairedExceptOne`, the XOR fold recovers the
    unique unpaired value `m` — every paired value cancels (`xorFn_pair_cancel`), leaving `m`. -/
theorem solve_correct {xs : SnocList Nat Nat} {m : Nat} (h : PairedExceptOne xs m) :
    solveFn xs = m := by
  induction h with
  | base m => rfl
  | pair h ih =>
    show xorFn (SnocList.snoc (SnocList.snoc _ _) _) = _
    rw [xorFn_pair_cancel]; exact ih

/-! ## Running the program -/

/-- Build a `Nat`-list from a first value and the rest, in order. -/
def ofList (first : Nat) (rest : List Nat) : SnocList Nat Nat :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 2 [2, 1]) = 1 := by decide
example : solveFn (ofList 4 [1, 2, 1, 2]) = 4 := by decide
example : solveFn (ofList 7 []) = 7 := by decide

/-- A canonical-shaped instance (`m` first, pairs appended adjacently) exercising both the spec and
    `solve_correct` end-to-end. -/
example : PairedExceptOne (ofList 4 [2, 2, 1, 1]) 4 :=
  PairedExceptOne.pair (p := 1) (PairedExceptOne.pair (p := 2) (PairedExceptOne.base 4))

example : solveFn (ofList 4 [2, 2, 1, 1]) = 4 :=
  solve_correct (PairedExceptOne.pair (p := 1) (PairedExceptOne.pair (p := 2) (PairedExceptOne.base 4)))

end Freyd.Alg.RelSet.LC136
