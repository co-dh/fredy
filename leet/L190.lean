/-
  LeetCode 190 — Reverse Bits — as an ALLEGORY PROGRAM, the STRUCTURAL-OUTPUT case.

  Problem: reverse the bit order of a `w`-bit word (LeetCode: a 32-bit unsigned integer).

  Model a `w`-bit word as a `List Bool` (`true` = a `1`-bit), **LSB-first**: position `i` in the
  list holds bit `i` (weight `2^i`), so `head = bit 0` (least significant), the last entry is the
  most significant bit. Reversing the LIST then swaps position `i` with position `w-1-i` — exactly
  the required swap of bit `i` with bit `w-1-i` — so `List.reverse` on the LSB-first list already IS
  the bit-reversal (the convention is self-dual: the identical statement holds MSB-first).

  Same shape as `L206` (list reversal) and `L226` (`S15`, tree inversion): the answer object is the
  SAME object as the input (`List Bool ⟶ List Bool`, an ENDOMORPHISM), so there is no order to
  refine into — correctness is a direct structural fact plus the natural STRUCTURAL-OUTPUT extra
  laws: involutivity (`rev_rev`) and length preservation (`rev_length`), exactly `L206`'s pair.

  New here (vs `L206`'s `List Int`): the element type is `Bool`, so the list carries a VALUE view
  as a bit-string — `bitsToNat`/`natToBits`, an LSB-first `List Bool ↔ Nat` correspondence — giving
  a value-level sanity check for the structural definition (`natToBits_bitsToNat`, a round trip),
  though the structural + involutive laws already suffice for correctness (`S8`/`S15` precedent).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC190

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: the answer object is again a `List Bool` — a STRUCTURAL-OUTPUT endomorphism -/

/-- The object of bit-words in `Rel(Set)` — reuses `SL`'s generic wrapper `dL` for a plain type,
    `List Bool`, LSB-first (`bs[i]` = bit `i`, `true` = a `1`-bit). -/
abbrev dBits : RelSet.{0} := dL (List Bool)

/-! ## The program: `List.reverse` on the bit-list -/

/-- The concrete program: reverse the bit order. `List.reverse` on the LSB-first list swaps
    position `i` with position `w-1-i`, exactly the required bit swap. -/
def revBits : List Bool → List Bool := fun bs => bs.reverse

/-- **The allegory program**: LeetCode 190's solution as an ENDOMORPHISM `dBits ⟶ dBits` in
    `Rel(Set)` — the STRUCTURAL-OUTPUT case, source and target the SAME object (cf. `L206`,
    `L226`/`S15`). -/
def solve : dBits ⟶ dBits := graph revBits

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map revBits

/-! ## Correctness: `solve` reverses, and reversing twice is the identity -/

/-- **Correctness of the allegory program**: `revBits` computes `List.reverse`. -/
theorem solve_correct (bs : List Bool) : revBits bs = bs.reverse := rfl

/-- **Involutivity**: reversing bits twice is the identity — same-object extra law (cf. `L206`'s
    `rev_rev`, `L226`'s `invert_invert`). -/
theorem rev_rev (bs : List Bool) : revBits (revBits bs) = bs := by
  show bs.reverse.reverse = bs
  exact List.reverse_reverse bs

/-- **Length (width) preservation**: bit-reversal does not change the word width. -/
theorem rev_length (bs : List Bool) : (revBits bs).length = bs.length := by
  show bs.reverse.length = bs.length
  exact List.length_reverse

/-! ## Value view: an LSB-first `List Bool ↔ Nat` correspondence -/

/-- A bit's numeric weight contribution: `1` for `true`, `0` for `false`. -/
def b2n (b : Bool) : Nat := if b then 1 else 0

/-- The natural number an LSB-first bit-list denotes: `bs[0]` has weight `1`, `bs[1]` weight `2`, … -/
def bitsToNat : List Bool → Nat
  | [] => 0
  | b :: rest => b2n b + 2 * bitsToNat rest

/-- The `w`-bit LSB-first encoding of `n` (i.e. `n` truncated/zero-padded to width `w`). -/
def natToBits : Nat → Nat → List Bool
  | _, 0 => []
  | n, w + 1 => decide (n % 2 = 1) :: natToBits (n / 2) w

/-- `natToBits` always produces a word of the requested width. -/
theorem natToBits_length (n w : Nat) : (natToBits n w).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => show (natToBits (n / 2) w).length + 1 = w + 1; rw [ih]

/-- **Round trip**: decoding a bit-list to its value and re-encoding at the same width recovers the
    original list — the value view is faithful to the structural one. -/
theorem natToBits_bitsToNat (bs : List Bool) : natToBits (bitsToNat bs) bs.length = bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    show natToBits (b2n b + 2 * bitsToNat rest) (rest.length + 1) = b :: rest
    cases b with
    | true =>
      have hq : (b2n true + 2 * bitsToNat rest) / 2 = bitsToNat rest := by
        show (1 + 2 * bitsToNat rest) / 2 = bitsToNat rest; omega
      have hm : (b2n true + 2 * bitsToNat rest) % 2 = 1 := by
        show (1 + 2 * bitsToNat rest) % 2 = 1; omega
      show decide ((b2n true + 2 * bitsToNat rest) % 2 = 1) ::
          natToBits ((b2n true + 2 * bitsToNat rest) / 2) rest.length = true :: rest
      rw [hq, hm]; simp [ih]
    | false =>
      have hq : (b2n false + 2 * bitsToNat rest) / 2 = bitsToNat rest := by
        show (0 + 2 * bitsToNat rest) / 2 = bitsToNat rest; omega
      have hm : (b2n false + 2 * bitsToNat rest) % 2 = 0 := by
        show (0 + 2 * bitsToNat rest) % 2 = 0; omega
      show decide ((b2n false + 2 * bitsToNat rest) % 2 = 1) ::
          natToBits ((b2n false + 2 * bitsToNat rest) / 2) rest.length = false :: rest
      rw [hq, hm]; simp [ih]

/-! ## Running the program -/

example : revBits [true, false, false, false] = [false, false, false, true] := by decide
example : revBits ([] : List Bool) = [] := by decide
example : revBits [true] = [true] := by decide
example : revBits (revBits [true, false, true]) = [true, false, true] := by decide

end Freyd.Alg.RelSet.LC190
