/-
  UnixPipe — the shell pipeline `ls -l | grep | sort` as relation-algebra terms in the
  executable finite allegory `FinRel` (`rel.RelInterp`), grounded in real Linux syscalls.

  A case study (like `AOP.A6_1_Digits`), NOT a book section.  It replays the spec↔program
  pattern of `RelInterp`'s LC 121 demos for a Unix pipeline:

    * each stage of `ls | grep | sort` is a term of the relation-algebra AST `RE`;
    * a fixed COMMITTED SNAPSHOT of n = 5 directory entries lets every per-snapshot fact be
      settled by kernel `decide` (the power object `[Entry]` has only `2^5 = 32` rows);
    * the payoff theorems are the reason to do this in an allegory: pipeline-rewrite laws
      (grep-fusion, grep idempotence, grep-only-removes, filter/sort commutation, and the
      spec↔program HEAD bridge) fall out of the ABSTRACT Chapter-2 allegory theorems applied
      to the executable terms, not out of re-proving anything by hand.

  HONEST SCOPE (what this is and is NOT).
    * SNAPSHOT, not streaming.  The algebra models one fixed directory listing; a real pipe is
      a stream.  We commit the 5-entry snapshot as the fixture.
    * Per-snapshot facts (`sort_head_bridge`, `grep_sort_commute`, `leqE_via_rank`) are proved
      by `decide` on the fixture.  UNIVERSAL laws (`grep_fusion`, `grep_idem`,
      `grep_only_removes`) come from the abstract allegory instances and hold for every atom.
    * The algebra never inspects a string or a byte.  Regex matching (`isTxt`, "name ends in
      .txt") and byte-size comparison (`leqE`) are INJECTED as ground Boolean atoms; the terms
      only compose/converse/meet/divide them.  A `#eval` cross-checks the `isTxt` table against
      the real `String.endsWith ".txt"` so the fixture is not fiction — but no `String` op ever
      enters a `decide` or a theorem.
    * `sort` has no total order inside `FinRel`, so the fully sorted SEQUENCE is not an `RE`
      term.  We give sort TWO sides: the SPEC side (`eval`, exponential) computes the survivor
      SET as a power-object point and its `≤`-least member (the sorted output's HEAD) with
      `minRelE`; the PROGRAM side (`evalP`-style, polynomial) is a filter+insertion-sort FOLD
      over a plain `List (Fin 5)`.  `sort_head_bridge` connects the two on the fixture.
    * `ls -l` line formatting and the full lexicographic sort are out of scope; `main` prints a
      `-l`-style line but the algebra only sees the size key.
    * The `main` glue is the "grounded in Linux syscalls" part: it `readDir`s a real directory
      and reads each entry's `metadata.byteSize` (both Lean core, mathlib-free), builds runtime
      atoms over the live arrays, runs `eval`/`evalP`, and prints the pipeline laws' Boolean on
      the LIVE snapshot.  No compile-time IO is embedded in any `def`, so the build never
      depends on the builder's filesystem.

  Abstract warrant for `sort` (cited, not re-proved): `Freyd.Alg.RelSet.Sort.selection_sort_correct`
  formalises Bird–de Moor §6.6 `sort ⊆ ordered · perm`; our program side is one concrete
  refinement (insertion sort by the size key) of that specification.

  STRICTLY mathlib-free / Std-free; imports are `Fredy.*` + Lean core only.
  Sorry-free; every theorem's `#print axioms` ⊆ {propext, Quot.sound}.  Never `native_decide`.
-/
import rel.RelInterp
import Fredy.S2_1
import AOP.A4_2
import AOP.A6_6_Sort

set_option linter.unusedVariables false

namespace Freyd.Alg.FinRel.UnixPipe

open Freyd Freyd.Alg

/-! ## The committed directory SNAPSHOT (fixture): 5 entries -/

/-- The one directory (`ls`'s single input). -/
abbrev Dir : FinObj := ⟨1⟩
/-- The 5 directory entries (`ls`'s output). -/
abbrev Entry : FinObj := ⟨5⟩

/-- Hard-coded entry names, in directory order. -/
def nameOf : Fin 5 → String := fun i =>
  match i.val with
  | 0 => "readme.txt" | 1 => "data.csv" | 2 => "notes.txt" | 3 => "img.png" | _ => "todo.txt"

/-- Hard-coded byte sizes (the `-l` key), all distinct. -/
def sizeOf : Fin 5 → Nat := fun i =>
  match i.val with
  | 0 => 100 | 1 => 250 | 2 => 40 | 3 => 900 | _ => 175

/-- Hard-coded `grep`-match table: does the name end in `.txt`?  Injected as an atom — the
    algebra never runs a regex.  Kept in sync with `nameOf` by the `#eval` cross-check below. -/
def isTxt : Fin 5 → Bool := fun i =>
  match i.val with
  | 0 => true | 1 => false | 2 => true | 3 => false | _ => true

-- CROSS-CHECK the hard-coded `isTxt` table against the REAL `String.endsWith ".txt"` on the real
-- names, so the fixture is not fiction.  `String` ops live only here, never in a `decide`/theorem.
-- Prints `true`.
#eval (List.ofFn fun i : Fin 5 => isTxt i == (nameOf i).endsWith ".txt").all (fun b => b)

/-- The size comparison `e ≤ f` (by byte size) — the key `sort` orders on. -/
def leSize (e f : Fin 5) : Bool := decide (sizeOf e ≤ sizeOf f)

/-! ## Stage 1 — `ls -l` : `Dir ⟶ Entry`, a genuine one-to-many relation

  `containsFn` relates the one directory to ALL 5 entries: `ls` is NOT a function (one input,
  five outputs), so this atom is a genuine non-functional relation, not a `Map`. -/

/-- `ls`: the single directory contains all 5 entries. -/
def containsFn : Dir ⟶ Entry := fun _ _ => true
/-- `ls -l` as a term. -/
def lsE : RE Dir Entry := .atom containsFn

/-- The `-l` size key as a comparison relation on entries (compare `sizeOf`). -/
def leqE : RE Entry Entry := .atom leSize

/-! ### The `stat(2)` size attribute as a `Map` atom (functional relation)

  Sizes are unbounded `Nat`s, so we encode the `-l` size as a finite RANK in `[0,5)` (ascending
  by size).  `statSize` is the GRAPH of that rank function, hence a `Map` (single-valued and
  entire) by `graphB_map` — the functional "stat lookup".  `leqE_via_rank` below shows the size
  comparison FACTORS through this Map (`leqE = statSize ≫ (≤ on ranks) ≫ statSize°`), the exact
  sense in which the `-l` attribute flows through the pipe; that factorisation is exact ONLY
  because `statSize` is functional, so it doubles as the verification that `statSize` is a Map. -/

/-- Size ranks `[0,5)` in ascending byte-size order (`40,100,175,250,900` ↦ entries `2,0,4,1,3`). -/
abbrev SizeRank : FinObj := ⟨5⟩
/-- The ascending-size rank of each entry (`sizeOf = [100,250,40,900,175]`). -/
def rankOf : Fin 5 → Fin 5 := fun i =>
  match i.val with
  | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 4 | _ => 2
/-- `stat`'s size lookup as a `Map` atom: the graph of `rankOf` (a functional relation). -/
def statSize : RE Entry SizeRank := .atom (graphB rankOf)
/-- The `≤` order on ranks. -/
def leqRankE : RE SizeRank SizeRank := .atom (fun r r' => decide (r.val ≤ r'.val))

/-! ## Stage 2 — `grep p` : a COREFLEXIVE filter `Entry ⟶ Entry`

  `grep p = id ∩ ⟨e ↦ (e=e ∧ p e)⟩`, the sub-diagonal keeping exactly the matching entries.
  Coreflexive (`⊑ id`), so composing greps is intersecting predicates (§2.121). -/

/-- The match-diagonal atom for predicate `p`: `pDiag p e f = (e = f) ∧ p e`. -/
def pDiag (p : Fin 5 → Bool) : Entry ⟶ Entry := fun e f => decide (e = f) && p e

/-- `grep p` as a term: `meet id (match-diagonal of p)`. -/
def grepE (p : Fin 5 → Bool) : RE Entry Entry := .meet (.id Entry) (.atom (pDiag p))

/-- **`grep p` evaluates to a COREFLEXIVE** (`⊑ id`) — required deliverable: it is a filter, a
    sub-diagonal.  Immediate from `id ∩ _ ⊑ id`. -/
theorem grepE_coref (p : Fin 5 → Bool) : Coreflexive (eval (grepE p)) :=
  inter_lb_left (Cat.id Entry) (pDiag p)

/-! ## Payoff 1 — grep FUSION and idempotence via the abstract §2.121 theorem

  `S2_1.coreflexive_comp_eq_inter` (§2.121, `A ≫ B = A ∩ B` for coreflexives) is applied to the
  EXECUTABLE grep terms to fuse two greps into one — a real reuse of an abstract Chapter-2
  theorem: the composition→intersection step is the ALGEBRA, not a `decide` over the matrix. -/

/-- **grep FUSION**: `grep p ≫ grep q = grep (p ∧ q)`.  The composition collapses to an
    intersection by the ABSTRACT §2.121 law `coreflexive_comp_eq_inter` (no `decide`); only the
    residual predicate-lattice identity is pointwise Boolean (`cases` on the three Bools). -/
theorem grep_fusion (p q : Fin 5 → Bool) :
    eval (RE.comp (grepE p) (grepE q)) = eval (grepE (fun x => p x && q x)) := by
  show eval (grepE p) ≫ eval (grepE q) = eval (grepE (fun x => p x && q x))
  rw [coreflexive_comp_eq_inter (grepE_coref p) (grepE_coref q)]
  funext e f
  simp only [grepE, eval, inter_apply, id_apply, pDiag]
  cases decide (e = f) <;> cases p e <;> cases q e <;> rfl

/-- **grep IDEMPOTENCE**: `grep p ≫ grep p = grep p` — a corollary of fusion (`p ∧ p = p`). -/
theorem grep_idem (p : Fin 5 → Bool) :
    eval (RE.comp (grepE p) (grepE p)) = eval (grepE p) := by
  have hpp : (fun x => p x && p x) = p := funext fun x => Bool.and_self (p x)
  rw [grep_fusion p p, hpp]

/-- **grep ONLY REMOVES**: `ls ≫ grep p ⊑ ls` — a filter can only drop entries, never add.
    Coreflexivity of grep + monotonicity of composition. -/
theorem grep_only_removes (p : Fin 5 → Bool) :
    eval (RE.comp lsE (grepE p)) ⊑ eval lsE := by
  have h : eval lsE ≫ eval (grepE p) ⊑ eval lsE ≫ Cat.id Entry :=
    comp_mono_left (eval lsE) (grepE_coref p)
  rw [Cat.comp_id] at h
  exact h

/-! ## Stage 3 — `sort`, SPEC side (`eval`, exponential): survivor SET + its `≤`-least HEAD

  `FinRel` has no order object, so the sorted SEQUENCE is not an `RE` term.  What IS a term:
  the survivor SET as a power-object point `Λ(ls ≫ grep)` and its size-least member via `min`
  (Bird–de Moor §7.1 `minRelE`).  Runs on `eval`, brute-forcing all `2^5 = 32` subset codes. -/

/-- The survivor SET (txt files) as a power-object point `Λ(ls ≫ grep .txt) : Dir ⟶ [Entry]`. -/
def pipeSet : RE Dir (pow Entry) := AE (RE.comp lsE (grepE isTxt))
/-- The HEAD of the ascending sorted output: the smallest-size survivor.  In B&dM's `min R = ∋ ∩
    (∋°\R)` the selected element is the one ABOVE all of the set in `R`, so the size-MINIMUM is
    `max` of the size order `leqE` (`maxRelE R = minRelE R°`), matching the `#eval` below. -/
def headE : RE Dir Entry := RE.comp pipeSet (maxRelE leqE)

/-! ## Stage 3 — `sort`, PROGRAM side (polynomial): filter+insertion-sort FOLD over a plain List

  The efficient program: a fused filter+insertion-sort FOLD over a plain `List (Fin 5)` (NOT the
  non-empty `SL` of `Prog.cata`, because `grep` can empty the list).  `step acc e = if p e then
  linsert e acc else acc`, `base = []` — the `leet.L56_derived` fold shape.  Generic in the
  keep-predicate and order so the fixture and the live `main` share one definition (DRY). -/

/-- Insertion into an ascending (by `le`) list — `leet.L56`'s `linsert`, generic in the order. -/
def linsertBy {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: linsertBy le x ys

/-- The fused `grep|sort` program: fold keeping matches and insertion-sorting them by `le`. -/
def pipeFoldBy {α : Type} (keep : α → Bool) (le : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc e => if keep e then linsertBy le e acc else acc) []

/-- Insertion sort of an already-filtered list (the `sort` stage, separated from `grep`). -/
def isortBy {α : Type} (le : α → α → Bool) (xs : List α) : List α := xs.foldr (linsertBy le) []

/-- The 5 entries in directory order. -/
def entriesList : List (Fin 5) := [0, 1, 2, 3, 4]

-- The program's sorted txt output `[notes.txt(40), readme.txt(100), todo.txt(175)] = [2,0,4]`.
#eval pipeFoldBy isTxt leSize entriesList
-- The spec HEAD column over the 5 entries: `true` only at entry 2 (notes.txt, size 40).
#eval List.ofFn fun e : Fin 5 => eval headE 0 e

/-! ## Payoff 2 — the SPEC↔PROGRAM head bridge, and pipeline commutation (per-snapshot, `decide`) -/

/-- **SPEC↔PROGRAM HEAD BRIDGE** (`eval` vs the program fold): the entry the exponential SPEC
    term `Λ(ls ≫ grep) ≫ max(≤)` (size-least survivor) relates `Dir` to IS the head the polynomial
    filter+isort program emits — checked column-wise by `decide` on the fixture.  The §6.6
    spec↔program agreement of `leet.L121`, now for a pipeline. -/
theorem sort_head_bridge :
    (List.ofFn fun e : Fin 5 => eval headE 0 e)
      = (List.ofFn fun e : Fin 5 => decide ((pipeFoldBy isTxt leSize entriesList).head? = some e)) := by
  decide

/-- **grep/sort COMMUTE** (`ls|grep|sort ≡ ls|sort|grep` at the list level): filtering then
    sorting equals sorting then filtering, since insertion sort is stable and `filter` preserves
    order.  `decide` on the fixture, for the concrete predicate `isTxt`. -/
theorem grep_sort_commute :
    (isortBy leSize entriesList).filter isTxt = isortBy leSize (entriesList.filter isTxt) := by
  decide

/-- **The `-l` size key FACTORS through the `stat` Map**: `leqE = statSize ≫ (≤ on ranks) ≫
    statSize°`, i.e. comparing byte sizes is comparing size-ranks looked up through the functional
    `statSize`.  Checked as a `5×5` Boolean matrix by `decide`; being exact it also witnesses that
    `statSize` is single-valued (a `Map`). -/
theorem leqE_via_rank :
    (List.ofFn fun e : Fin 5 => List.ofFn fun f : Fin 5 => eval leqE e f)
      = (List.ofFn fun e : Fin 5 => List.ofFn fun f : Fin 5 =>
          eval (RE.comp (RE.comp statSize leqRankE) (RE.conv statSize)) e f) := by
  decide

end Freyd.Alg.FinRel.UnixPipe

open Freyd.Alg.FinRel Freyd.Alg.FinRel.UnixPipe

/-! ## Live kernel glue — real `readDir` + `metadata.byteSize` (the Linux-syscall grounding)

  `main` reads a real directory, reads each entry's byte size via `System.FilePath.metadata`
  (Lean core, mathlib-free — mirrors `scripts/ExtractGraph.lean`'s `readDir` idiom), builds
  RUNTIME atoms over the live arrays, runs `eval` for the sorted HEAD (capped at ≤ 5 entries so
  the `2^k` power object stays small) and the polynomial fold `pipeFoldBy` for the full pipe,
  prints `-l`-style lines, and prints the Boolean of grep-fusion + grep/sort-commutation ON THE
  LIVE SNAPSHOT.  Self-contained: no compile-time IO, so the build is filesystem-independent. -/

/-- Flatten a `Fin k` Boolean matrix so two of them can be compared with `==` at runtime
    (function values have no `BEq`). -/
def matToList (k : Nat) (R : Fin k → Fin k → Bool) : List (List Bool) :=
  List.ofFn fun i : Fin k => List.ofFn fun j : Fin k => R i j

def main : IO Unit := do
  let dir : System.FilePath := "."
  let dents ← dir.readDir
  let names : Array String := dents.map (·.fileName)
  let mut sizes : Array Nat := #[]
  for d in dents do
    let md ← d.path.metadata
    sizes := sizes.push md.byteSize.toNat
  let n := dents.size
  IO.println s!"# ls -l  ({n} entries in {dir})"
  for i in List.range n do
    let nm := names[i]!
    let tag := if nm.endsWith ".txt" then "txt" else "   "
    IO.println s!"  {sizes[i]!}\t{tag}\t{nm}"

  -- Runtime predicates over the live snapshot (real regex + real byte size).
  let liveList : List (Fin n) := List.ofFn (fun i => i)
  let keepTxt : Fin n → Bool := fun i => (names[i.val]!).endsWith ".txt"
  let leLive  : Fin n → Fin n → Bool := fun i j => decide (sizes[i.val]! ≤ sizes[j.val]!)

  -- PROGRAM side (polynomial fold, `evalP`-style) on ALL live entries: filter+insertion-sort.
  let sortedTxt := pipeFoldBy keepTxt leLive liveList
  IO.println s!"\n# ls | grep .txt | sort   (evalP-style fold, {sortedTxt.length} survivors, by size)"
  for e in sortedTxt do
    IO.println s!"  {sizes[e.val]!}\t{names[e.val]!}"

  -- SPEC side (matrix `eval`) on a ≤5-entry cap so the power object 2^k stays small.
  let k := min n 5
  let Ent : FinObj := ⟨k⟩
  let Dr  : FinObj := ⟨1⟩
  let keepCap : Fin k → Bool := fun e => (names[e.val]!).endsWith ".txt"
  let bigCap  : Fin k → Bool := fun e => decide (sizes[e.val]! ≥ 100)
  let leCap   : Fin k → Fin k → Bool := fun e f => decide (sizes[e.val]! ≤ sizes[f.val]!)
  let grepCap : (Fin k → Bool) → RE Ent Ent :=
    fun p => .meet (.id Ent) (.atom (fun e f => decide (e = f) && p e))
  let lsRT   : RE Dr Ent := .atom (fun _ _ => true)
  let headRT : RE Dr Ent := .comp (AE (.comp lsRT (grepCap keepCap))) (maxRelE (.atom leCap))
  let headCol : List Bool := List.ofFn (fun e : Fin k => eval headRT 0 e)
  let heads := (List.ofFn (fun e : Fin k => e)).filter (fun e => headCol[e.val]!)
  IO.println s!"\n# sorted HEAD via  Λ(ls ≫ grep) ≫ max(≤)   (size-least, matrix eval, first {k} entries)"
  for e in heads do
    IO.println s!"  smallest txt: {names[e.val]!} ({sizes[e.val]!} bytes)"

  -- Pipeline LAWS on the LIVE snapshot (runtime Booleans, computed by RUNNING `eval`/the fold).
  -- grep-fusion: run `eval` of the COMPOSED greps vs `eval` of the single fused grep.
  let grepFuse :=
    matToList k (eval (RE.comp (grepCap keepCap) (grepCap bigCap)))
      == matToList k (eval (grepCap (fun e => keepCap e && bigCap e)))
  -- commutation: filter∘sort vs sort∘filter over the live list.
  let commute :=
    (isortBy leLive liveList).filter keepTxt == isortBy leLive (liveList.filter keepTxt)
  IO.println s!"\n# pipeline laws on THIS directory:"
  IO.println s!"  grep .txt ≫ grep ≥100  ==  grep (.txt ∧ ≥100)   : {grepFuse}"
  IO.println s!"  filter ∘ sort  ==  sort ∘ filter                : {commute}"
