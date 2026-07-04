/-
  LeetCode 763 — Partition Labels — as an ALLEGORY PROGRAM.

  Problem: partition a string into as many pieces as possible so that each character appears in
  at most one piece; return the list of piece sizes.

  Same recipe as `Fredy/L53.lean`/`Fredy/L20.lean` (`Fredy/leetcode.md`, skill S0), for a greedy
  scan whose invariant references the WHOLE input, not just the scanned prefix:

  1. **Data** — the string is the initial algebra `SnocList ℤ ℤ` of `F X = ℤ + X × ℤ`
     (`Fredy.A6_SnocList`), characters coded as `Int`; `wrap x` is a single character, `snoc xs c`
     appends one.

  2. **Program** — a two-pass greedy: pass 1 (`lastPos whole c : Nat`) is the LAST index at which
     `c` occurs anywhere in the fixed whole string; pass 2 (`scanFn whole`) is a left-to-right fold
     with state `(reach, curSize, doneParts)`, `reach = nmax` (a mathlib-free `Nat` max, the `imax`
     technique of `L53` applied to `Nat` since positions are never negative) of `lastPos whole c`
     over every character `c` seen in the CURRENT (still open) piece. At index `i`, once
     `i = reach` the piece closes (its size is recorded, the running size resets).
     `solveFn xs := (scanFn xs xs).2.2.reverse`.

  3. **Specification** — `IsValidPartition xs parts`: `parts` are consecutive, non-empty pieces
     covering `xs`, each one SELF-CONTAINED (no character of a piece occurs anywhere outside it).
     Defined by structural recursion on `List Int` (via `take`/`drop`), independent of `solveFn`.

  4. **Correctness** — SOUNDNESS is proved in full: `solve_valid : IsValidPartition (toList xs)
     (solveFn xs)`, i.e. `solveFn`'s own output is always a valid partition (self-contained pieces,
     covering the whole string, positive part sizes). MAXIMALITY (no valid partition has strictly
     more pieces) is NOT attempted — see the note at the bottom of the file for the precise gap.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import Fredy.A6_SnocList
import Fredy.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC763

open Freyd Freyd.Alg.RelSet.SL

/-! ## `Nat` `max` (mathlib-free; the `imax` TECHNIQUE of `L53`, instantiated at `Nat` since every
    quantity here — a string position — is never negative; `omega`-backed, not `Nat.max`, so the
    rewrite set stays under our control). -/

def nmax (a b : Nat) : Nat := if a ≤ b then b else a

theorem nmax_ge_left  (a b : Nat) : a ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_ge_right (a b : Nat) : b ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_eq_or (a b : Nat) : nmax a b = a ∨ nmax a b = b := by
  unfold nmax; split; exacts [Or.inr rfl, Or.inl rfl]

/-! ## Data: strings as a non-empty snoc-list of characters (`Int`-coded) -/

/-- The object of strings in `Rel(Set)` — `SnocList ℤ ℤ` (`wrap x` = a single character,
    `snoc xs c` = `xs` with one more character appended). -/
abbrev Arr : RelSet.{0} := dSL Int Int
/-- The object of answers (piece-size lists) in `Rel(Set)`. -/
abbrev dParts : RelSet.{0} := ⟨List Nat⟩

/-! ## The program: pass 1 (last occurrence) then pass 2 (a close-on-reach scan) -/

/-- `topIdx xs` — the 0-based index of the LAST element of `xs`. -/
def topIdx : SnocList Int Int → Nat
  | .wrap _ => 0
  | .snoc xs _ => topIdx xs + 1

/-- **Pass 1.** `lastPos whole c` — the index of the LAST occurrence of `c` anywhere in `whole`
    (checking the rightmost element FIRST, so a match there wins over an earlier one), or `0` if
    `c` does not occur in `whole` at all (a harmless default — `wrap`'s only position IS `0`
    anyway, and pass 2 never consults this value for a `c` absent from `whole`). -/
def lastPos : SnocList Int Int → Int → Nat
  | .wrap _, _ => 0
  | .snoc xs p, c => if p = c then topIdx xs + 1 else lastPos xs c

/-- `lastPos` never overshoots the valid index range of `whole` — a fact about `lastPos` alone,
    needed to show the scan's `reach` stays sane and (at the top level) that the final piece
    always closes. -/
theorem lastPos_le_topIdx : ∀ (whole : SnocList Int Int) (c : Int), lastPos whole c ≤ topIdx whole
  | .wrap _, _ => Nat.le_refl 0
  | .snoc xs p, c => by
      show (if p = c then topIdx xs + 1 else lastPos xs c) ≤ topIdx xs + 1
      split
      · exact Nat.le_refl _
      · have := lastPos_le_topIdx xs c; omega

/-- **Pass 2.** The left-to-right scan over `xs`, w.r.t. the FIXED whole string `whole`: state
    `(reach, curSize, doneParts)`. `reach` is the `nmax` of `lastPos whole c` over every character
    `c` seen so far in the current (open) piece; once the current index reaches it, the piece
    closes (`curSize` is pushed onto `doneParts` and reset to `0`). `doneParts` accumulates in
    REVERSE (closing) order — `solveFn` reverses it back. -/
def scanFn (whole : SnocList Int Int) : SnocList Int Int → (Nat × Nat × List Nat)
  | .wrap x =>
      let r := lastPos whole x
      if r = 0 then (r, 0, [1]) else (r, 1, [])
  | .snoc xs p =>
      let (r, sz, rp) := scanFn whole xs
      let r' := nmax r (lastPos whole p)
      if topIdx xs + 1 = r' then (r', 0, (sz + 1) :: rp) else (r', sz + 1, rp)

@[simp] theorem scanFn_wrap (whole : SnocList Int Int) (x : Int) :
    scanFn whole (.wrap x) =
      (let r := lastPos whole x; if r = 0 then (r, 0, [1]) else (r, 1, [])) := rfl
@[simp] theorem scanFn_snoc (whole xs : SnocList Int Int) (p : Int) :
    scanFn whole (.snoc xs p) =
      (let (r, sz, rp) := scanFn whole xs
       let r' := nmax r (lastPos whole p)
       if topIdx xs + 1 = r' then (r', 0, (sz + 1) :: rp) else (r', sz + 1, rp)) := rfl

/-- The scan's `reach` never overshoots `whole`'s own range, for ANY `xs` fed into it (no relation
    between `xs` and `whole` needed) — `reach` is always built from `lastPos whole` values, each
    bounded by `lastPos_le_topIdx`. -/
theorem scanFn_reach_le_topIdx (whole : SnocList Int Int) :
    ∀ xs, (scanFn whole xs).1 ≤ topIdx whole
  | .wrap x => by
      show (let r := lastPos whole x; if r = 0 then (r,0,[1]) else (r,1,[])).1 ≤ topIdx whole
      dsimp only; split <;> exact lastPos_le_topIdx whole x
  | .snoc xs p => by
      show (let (r, sz, rp) := scanFn whole xs
            let r' := nmax r (lastPos whole p)
            if topIdx xs + 1 = r' then (r', 0, (sz+1) :: rp) else (r', sz+1, rp)).1 ≤ topIdx whole
      have h1 := scanFn_reach_le_topIdx whole xs
      have h2 := lastPos_le_topIdx whole p
      rcases hh : scanFn whole xs with ⟨r, sz, rp⟩
      rw [hh] at h1
      dsimp only
      split <;> (unfold nmax; split <;> omega)

/-- **The last character of `whole` always closes the final piece.** At the top-level call
    (`xs = whole`), the running size is always `0` — every character ends up in some piece. -/
theorem sz_top_eq_zero : ∀ xs, (scanFn xs xs).2.1 = 0
  | .wrap x => rfl
  | .snoc xs p => by
      show (let (r, sz, rp) := scanFn (.snoc xs p) xs
            let r' := nmax r (lastPos (.snoc xs p) p)
            if topIdx xs + 1 = r' then (r', 0, (sz+1) :: rp) else (r', sz+1, rp)).2.1 = 0
      have hself : lastPos (SnocList.snoc xs p) p = topIdx xs + 1 := if_pos rfl
      rcases hh : scanFn (SnocList.snoc xs p) xs with ⟨r, sz, rp⟩
      have hbound : r ≤ topIdx xs + 1 := by
        have h := scanFn_reach_le_topIdx (SnocList.snoc xs p) xs
        rw [hh] at h; exact h
      rw [hself]
      have hclose : topIdx xs + 1 = nmax r (topIdx xs + 1) := by unfold nmax; split <;> omega
      dsimp only
      rw [if_pos hclose]

/-! ## `IsPrefix`: `xs` is an ANCESTOR of `whole` in its own `snoc`-chain -/

/-- `IsPrefix xs whole` — `xs` occurs somewhere along the chain of `snoc`s that builds up `whole`
    (including `whole` itself). This is exactly the relationship between the scan's shrinking
    recursion argument and the FIXED `whole` it queries `lastPos` against — needed to know that a
    character processed partway through the scan really does sit at that ABSOLUTE position within
    `whole` (not some unrelated string). -/
def IsPrefix : SnocList Int Int → SnocList Int Int → Prop
  | xs, .wrap y => xs = SnocList.wrap y
  | xs, .snoc ys q => xs = SnocList.snoc ys q ∨ IsPrefix xs ys

theorem IsPrefix_refl : ∀ xs : SnocList Int Int, IsPrefix xs xs
  | .wrap _ => rfl
  | .snoc _ _ => Or.inl rfl

/-- Shrinking `xs` by peeling its own last element preserves being a prefix of `whole`. -/
theorem IsPrefix_shrink {xs : SnocList Int Int} {p : Int} {whole : SnocList Int Int}
    (h : IsPrefix (SnocList.snoc xs p) whole) : IsPrefix xs whole := by
  induction whole with
  | wrap y => exact absurd h (fun h => nomatch (h : SnocList.snoc xs p = SnocList.wrap y))
  | snoc ys q ih =>
    rcases h with h | h
    · obtain ⟨hxy, _⟩ := SnocList.snoc.inj h
      exact hxy ▸ Or.inr (IsPrefix_refl xs)
    · exact Or.inr (ih h)

/-- `topIdx` is monotone along the prefix relation. -/
theorem topIdx_le_of_prefix : ∀ {a whole : SnocList Int Int}, IsPrefix a whole → topIdx a ≤ topIdx whole
  | a, .wrap y, h => by have : a = SnocList.wrap y := h; rw [this]; exact Nat.le_refl _
  | a, .snoc ys q, h => by
      rcases h with h | h
      · have : a = SnocList.snoc ys q := h; rw [this]; exact Nat.le_refl _
      · have := topIdx_le_of_prefix h; show topIdx a ≤ topIdx ys + 1; omega

/-- **The crucial position fact**: if `snoc xs p` is a prefix of `whole` (i.e. `p` genuinely occurs
    at the ABSOLUTE position `topIdx xs + 1` within `whole`), then `p`'s LAST occurrence in `whole`
    is at least that position — `lastPos` can never place `p`'s last occurrence BEFORE an actual
    occurrence of `p`. -/
theorem lastPos_ge_of_prefix {xs : SnocList Int Int} {p : Int} {whole : SnocList Int Int}
    (h : IsPrefix (SnocList.snoc xs p) whole) : topIdx xs + 1 ≤ lastPos whole p := by
  induction whole with
  | wrap y => exact absurd h (fun h => nomatch (h : SnocList.snoc xs p = SnocList.wrap y))
  | snoc ys q ih =>
    rcases h with h | h
    · obtain ⟨hxy, hpq⟩ := SnocList.snoc.inj h
      show topIdx xs + 1 ≤ lastPos (SnocList.snoc ys q) p
      rw [hxy, hpq]
      show topIdx ys + 1 ≤ (if q = q then topIdx ys + 1 else lastPos ys q)
      rw [if_pos rfl]; exact Nat.le_refl _
    · have hrec := ih h
      have hbnd : topIdx xs + 1 ≤ topIdx ys := topIdx_le_of_prefix h
      show topIdx xs + 1 ≤ (if q = p then topIdx ys + 1 else lastPos ys p)
      split
      · omega
      · exact hrec

/-! ## The specification: `IsValidPartition` (a `List`-level relation, independent of `solveFn`) -/

/-- The string as a plain `List Int`, in left-to-right order (a bridge for the spec, which reads
    naturally as `take`/`drop` on lists). -/
def toList : SnocList Int Int → List Int
  | .wrap x => [x]
  | .snoc xs p => toList xs ++ [p]

theorem toList_length : ∀ xs, (toList xs).length = topIdx xs + 1
  | .wrap _ => rfl
  | .snoc xs _ => by simp [toList, topIdx, toList_length xs]

/-- `IsValidPartition xs parts` — `parts` are consecutive, non-empty pieces that COVER `xs`
    (`take`/`drop` chunk it up completely), each one SELF-CONTAINED: no character of a piece occurs
    anywhere in the REST of the string (`NoSpan`, checked against `xs.drop p`, which recursively
    includes every later piece — catching a shared character between ANY two pieces, since if it
    were shared, it would show up in whichever piece's `NoSpan` check comes first). -/
def IsValidPartition : List Int → List Nat → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | xs, (p :: ps) =>
      0 < p ∧ p ≤ xs.length ∧ (∀ c ∈ xs.take p, c ∉ xs.drop p) ∧ IsValidPartition (xs.drop p) ps

/-- **`IsValidPartition` is closed under appending one more self-contained final piece**: if `l` is
    already validly partitioned by `parts`, and NONE of `l`'s characters occur in `extra` (a
    non-empty new final piece), then `l ++ extra` is validly partitioned by `parts ++ [extra
    .length]`. This is the one-step "the greedy scan just closed a new piece" lemma. -/
theorem IsValidPartition_snoc :
    ∀ (parts : List Nat) (l : List Int) (extra : List Int),
      IsValidPartition l parts → 0 < extra.length → (∀ c ∈ l, c ∉ extra) →
      IsValidPartition (l ++ extra) (parts ++ [extra.length]) := by
  intro parts
  induction parts with
  | nil =>
    intro l extra hip hlen hout
    cases l with
    | nil =>
      rcases extra with _ | ⟨e, es⟩
      · simp at hlen
      · show 0 < (e :: es).length ∧ (e :: es).length ≤ (e :: es).length ∧
          (∀ c ∈ (e :: es).take (e :: es).length, c ∉ (e :: es).drop (e :: es).length) ∧
          IsValidPartition ((e :: es).drop (e :: es).length) []
        refine ⟨hlen, Nat.le_refl _, ?_, ?_⟩ <;> simp [IsValidPartition]
    | cons a as => exact hip.elim
  | cons p ps ih =>
    intro l extra hip hlen hout
    cases l with
    | nil => exact hip.elim
    | cons a as =>
      obtain ⟨hp0, hple, hns, hrest⟩ := hip
      have hple' : p ≤ ((a :: as) ++ extra).length := by
        have : (a :: as).length ≤ ((a :: as) ++ extra).length := by simp
        omega
      have htake : ((a :: as) ++ extra).take p = (a :: as).take p :=
        List.take_append_of_le_length hple
      have hdrop : ((a :: as) ++ extra).drop p = (a :: as).drop p ++ extra :=
        List.drop_append_of_le_length hple
      show 0 < p ∧ p ≤ ((a :: as) ++ extra).length ∧
        (∀ c ∈ ((a :: as) ++ extra).take p, c ∉ ((a :: as) ++ extra).drop p) ∧
        IsValidPartition (((a :: as) ++ extra).drop p) (ps ++ [extra.length])
      refine ⟨hp0, hple', ?_, ?_⟩
      · rw [htake, hdrop]
        intro c hc hmem
        rcases List.mem_append.mp hmem with hmem' | hmem'
        · exact hns c hc hmem'
        · exact hout c (List.mem_of_mem_take hc) hmem'
      · rw [hdrop]
        exact ih ((a :: as).drop p) extra hrest hlen
          (fun c hc => hout c (List.mem_of_mem_drop hc))

/-! ## The main invariant: `scanFn` always produces a valid (self-contained) partial partition -/

/-- **The scan's main invariant.** Fix `whole`; for any prefix `xs` of it (`IsPrefix xs whole`),
    write `(r, sz, rp) := scanFn whole xs`, `n := (toList xs).length`, `k := n - sz` (the boundary
    between the CLOSED prefix and the still-open run). Then: `sz ≤ n`; the closed prefix is already
    validly partitioned by `rp.reverse` (`C`); every closed character's true last occurrence in
    `whole` is strictly before `k` (`D` — it will never be seen again); the closed prefix is
    disjoint from the open run (`D2`); and every open-run character's last occurrence is bounded by
    the current `reach` (`E`). -/
theorem scan_inv (whole : SnocList Int Int) :
    ∀ xs, IsPrefix xs whole →
      let (r, sz, rp) := scanFn whole xs
      let n := (toList xs).length
      let k := n - sz
      sz ≤ n ∧
      IsValidPartition ((toList xs).take k) rp.reverse ∧
      (∀ c ∈ (toList xs).take k, lastPos whole c < k) ∧
      (∀ c ∈ (toList xs).take k, c ∉ (toList xs).drop k) ∧
      (∀ c ∈ (toList xs).drop k, lastPos whole c ≤ r) := by
  intro xs
  induction xs with
  | wrap x =>
    intro _
    rw [scanFn_wrap]; dsimp only
    split <;> constructor <;> simp_all [toList, IsValidPartition]
  | snoc xs p ih =>
    intro hpre
    have hpre' := IsPrefix_shrink hpre
    rcases hh : scanFn whole xs with ⟨r₀, sz₀, rp₀⟩
    have hih := ih hpre'
    rw [hh] at hih
    obtain ⟨hA, hC, hD, hD2, hE⟩ := hih
    rw [scanFn_snoc, hh]
    dsimp only
    have hlen0 : (toList xs).length = topIdx xs + 1 := toList_length xs
    have htoList : toList (SnocList.snoc xs p) = toList xs ++ [p] := rfl
    have hpge : topIdx xs + 1 ≤ lastPos whole p := lastPos_ge_of_prefix hpre
    have hk₀len : (toList xs).length - sz₀ ≤ topIdx xs + 1 := by omega
    -- the character just processed, `p`, cannot equal any already-closed character
    have hne_of_closed : ∀ c ∈ (toList xs).take ((toList xs).length - sz₀), c ≠ p := by
      intro c hc hcp
      have hcltk : lastPos whole c < (toList xs).length - sz₀ := hD c hc
      rw [hcp] at hcltk
      omega
    split
    case isTrue hclose =>
      dsimp only
      have hlen : (toList (xs.snoc p)).length = (toList xs).length + 1 := by rw [htoList]; simp
      have hfull0 : (toList (xs.snoc p)).length - 0 = (toList (xs.snoc p)).length := Nat.sub_zero _
      rw [hfull0, List.take_length, List.drop_length]
      have hr0r' : r₀ ≤ nmax r₀ (lastPos whole p) := nmax_ge_left _ _
      have hpr' : lastPos whole p ≤ nmax r₀ (lastPos whole p) := nmax_ge_right _ _
      refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_⟩
      · rw [htoList]
        have hrev : ((sz₀ + 1) :: rp₀).reverse = rp₀.reverse ++ [sz₀ + 1] := by simp
        rw [hrev]
        have hextra_len :
            ((toList xs).drop ((toList xs).length - sz₀) ++ [p]).length = sz₀ + 1 := by
          have hdl : ((toList xs).drop ((toList xs).length - sz₀)).length = sz₀ := by
            rw [List.length_drop]; omega
          simp [hdl]
        have hkey := IsValidPartition_snoc rp₀.reverse ((toList xs).take ((toList xs).length - sz₀))
          ((toList xs).drop ((toList xs).length - sz₀) ++ [p]) hC (by omega) (by
            intro c hc hmem
            rw [List.mem_append] at hmem
            rcases hmem with hmem | hmem
            · exact hD2 c hc hmem
            · exact hne_of_closed c hc (List.mem_singleton.mp hmem))
        rw [hextra_len] at hkey
        have heq : (toList xs).take ((toList xs).length - sz₀) ++
              ((toList xs).drop ((toList xs).length - sz₀) ++ [p]) = toList xs ++ [p] := by
          rw [← List.append_assoc, List.take_append_drop]
        rwa [heq] at hkey
      · intro c hc
        rw [htoList, List.mem_append] at hc
        rcases hc with hc | hc
        · rw [← List.take_append_drop ((toList xs).length - sz₀) (toList xs), List.mem_append] at hc
          rcases hc with hc | hc
          · have := hD c hc; omega
          · have := hE c hc; omega
        · have : c = p := List.mem_singleton.mp hc
          rw [this]; omega
      · intro c _; simp
      · intro c hc; simp at hc
    case isFalse hclose =>
      dsimp only
      have hlen : (toList (xs.snoc p)).length = (toList xs).length + 1 := by rw [htoList]; simp
      have hkeq : (toList (xs.snoc p)).length - (sz₀ + 1) = (toList xs).length - sz₀ := by omega
      rw [hkeq]
      have htake : (toList (xs.snoc p)).take ((toList xs).length - sz₀) =
          (toList xs).take ((toList xs).length - sz₀) := by
        rw [htoList, List.take_append_of_le_length (by omega)]
      have hdrop : (toList (xs.snoc p)).drop ((toList xs).length - sz₀) =
          (toList xs).drop ((toList xs).length - sz₀) ++ [p] := by
        rw [htoList, List.drop_append_of_le_length (by omega)]
      rw [htake, hdrop]
      have hr0r' : r₀ ≤ nmax r₀ (lastPos whole p) := nmax_ge_left _ _
      have hpr' : lastPos whole p ≤ nmax r₀ (lastPos whole p) := nmax_ge_right _ _
      refine ⟨by omega, hC, hD, ?_, ?_⟩
      · intro c hc hmem
        rw [List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · exact hD2 c hc hmem
        · exact hne_of_closed c hc (List.mem_singleton.mp hmem)
      · intro c hc
        rw [List.mem_append] at hc
        rcases hc with hc | hc
        · have := hE c hc; omega
        · have : c = p := List.mem_singleton.mp hc
          rw [this]; omega

/-- **The answer**: the piece sizes, in left-to-right order. -/
def solveFn (xs : SnocList Int Int) : List Nat := (scanFn xs xs).2.2.reverse

/-- **SOUNDNESS (in full): `solveFn`'s own output is always a valid partition** — its pieces are
    consecutive, non-empty, cover the whole string, and each is SELF-CONTAINED (no character of a
    piece occurs anywhere outside it). Follows `scan_inv` at `xs = whole` (`IsPrefix_refl`),
    combined with `sz_top_eq_zero` (the running size is always fully closed at the top level, so
    the "closed prefix" IS the whole string, not a proper part of it). -/
theorem solve_valid (xs : SnocList Int Int) : IsValidPartition (toList xs) (solveFn xs) := by
  have hinv := scan_inv xs xs (IsPrefix_refl xs)
  have hsz := sz_top_eq_zero xs
  rcases hh : scanFn xs xs with ⟨r, sz, rp⟩
  rw [hh] at hinv hsz
  dsimp only at hsz
  obtain ⟨hA, hC, hD, hD2, hE⟩ := hinv
  subst hsz
  simp only [Nat.sub_zero, List.take_length] at hC
  show IsValidPartition (toList xs) (scanFn xs xs).2.2.reverse
  rw [hh]; dsimp only
  exact hC

/-- **The allegory program**: LeetCode 763's solution as a morphism `Arr ⟶ dParts` in `Rel(Set)`. -/
def solve : Arr ⟶ dParts := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## Running the program -/

/-- Build a string from a first character and the rest, in order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

-- "ababcbacadefegdehijhklij" (the classic LeetCode example); the code list ends `…105, 106`
-- (i, j) to spell "…hijhkl-ij", REUSING i/j's earlier codes, not fresh letters.
example :
    solveFn (ofList 97 [98, 97, 98, 99, 98, 97, 99, 97, 100, 101, 102, 101, 103, 100, 101, 104,
      105, 106, 104, 107, 108, 105, 106]) = [9, 7, 8] := by decide
example : solveFn (ofList 101 [105, 106, 101]) = [4] := by decide
example : solveFn (ofList 101 []) = [1] := by decide

/-! ## The maximality gap (NOT attempted)

`solve_valid` proves `solveFn` always returns SOME valid partition (self-contained pieces,
covering the whole string). LeetCode 763 additionally asks for the FINEST such partition — the one
with the MOST pieces, equivalently: `∀ parts, IsValidPartition (toList xs) parts → parts.length ≤
(solveFn xs).length`.

That direction is not proved here. The informal argument is: any valid partition's cut points must
each be ≥ every `lastPos whole c` of a character seen since the previous cut (else a later
occurrence of some character straddles the cut) — i.e. every valid partition's cut points are a
SUBSET of the `reach`-triggered closing points `scanFn` finds, which are its EARLIEST possible legal
cuts. Formalizing "any valid partition's cuts are a superset-of-positions of the greedy ones" needs
an induction comparing an ARBITRARY `parts` against `scanFn`'s own trace — the same "which piece is
position `i` in" bookkeeping this file avoided (see the file header, S1/S3 note in
`Fredy/leetcode.md`) by routing everything through the incremental `scan_inv` invariant instead of a
prefix-sum piece-index. Reach for that indexing (or a "greedy cuts are a subset of any valid cuts"
lemma by simultaneous induction on `parts` and the scan) if resuming this file. -/

end Freyd.Alg.RelSet.LC763
