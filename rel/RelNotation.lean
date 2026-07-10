/-
  Embedded surface notation `rel⟦ … ⟧` for the `RE` relation-algebra GADT (`rel.RelInterp`).

  This is the PROVABLE counterpart to the external `.ralg` interpreter (`rel.RelParse`): there a
  program is a text file parsed at runtime, so nothing about it can be a theorem; here a program is
  a `rel⟦ … ⟧` quotation that ELABORATES to an `RE a b` Lean value, so every tool the GADT has —
  `eval`, `by decide`, the proven `Allegory`/`PowerAllegory` laws — applies to it.

  Two structural wins over the `.ralg` parser, both from Lean's elaborator:
  * the dependent object indices `{a b c}` of `RE` are inferred and CHECKED at compile time — a
    dimension mismatch is a type error with a source location, replacing `RelCore`'s runtime
    `Except`-wrapped dimension checks;
  * atoms are `!(term)` splices — any Lean term of type `RE a b` — so an atom can be COMPUTED from
    instance data and proven faithful, instead of the hand-baked answer tables the `.ralg` encodings
    were forced into (e.g. Two Sum's `compl : v ↦ target-v`).

  Surface grammar mirrors `.ralg`: `;` comp, `&` meet, `|` join, `/` div, `\` left-div (all ONE
  precedence level, left-associative — the flat left fold), postfix `~` converse (binds tightest),
  and call-style keywords `id(o)`, `eps(o)`, `Lambda(e)` (= Λ), `min(e)`, `max(e)`.  Keywords are
  call-style so they do not reserve the tokens `id`/`min`/`max` as global keywords (checked at the
  bottom).  The examples below are the point: each is a theorem no `.ralg` file can state.
-/
import rel.RelInterp

namespace Freyd.Alg.FinRel

/-! ## The `rel⟦ … ⟧` quotation: `.ralg` surface syntax as a Lean syntax category -/

declare_syntax_cat ralg

-- primaries
syntax ident                      : ralg  -- an atom: a Lean constant of type `RE a b`
syntax ident "(" ralg ")"         : ralg  -- call-style prefix: Lambda(e), min(e), max(e), id(a), eps(a)
syntax "(" ralg ")"               : ralg
syntax "!(" term ")"              : ralg  -- splice: any Lean term of type `RE a b`
-- postfix converse, binds tightest
syntax:100 ralg:100 "~"           : ralg
-- the five binops: ONE precedence level, left-associative — .ralg's flat left fold
syntax:60 ralg:60 " ; "  ralg:61  : ralg
syntax:60 ralg:60 " & "  ralg:61  : ralg
syntax:60 ralg:60 " | "  ralg:61  : ralg
syntax:60 ralg:60 " / "  ralg:61  : ralg
syntax:60 ralg:60 " \\ " ralg:61  : ralg

syntax "rel⟦" ralg "⟧" : term

macro_rules
  | `(rel⟦ $x:ident ⟧)           => `(($x : RE _ _))
  | `(rel⟦ !($t:term) ⟧)         => `(($t : RE _ _))
  | `(rel⟦ ($a:ralg) ⟧)          => `(rel⟦ $a ⟧)
  | `(rel⟦ $a:ralg ~ ⟧)          => `(RE.conv rel⟦ $a ⟧)
  | `(rel⟦ id($o:ident) ⟧)       => `(RE.id $o)
  | `(rel⟦ eps($o:ident) ⟧)      => `(RE.eps $o)
  | `(rel⟦ Lambda($a:ralg) ⟧)    => `(AE rel⟦ $a ⟧)
  | `(rel⟦ min($a:ralg) ⟧)       => `(minRelE rel⟦ $a ⟧)
  | `(rel⟦ max($a:ralg) ⟧)       => `(maxRelE rel⟦ $a ⟧)
  | `(rel⟦ $a:ralg ; $b:ralg ⟧)  => `(RE.comp rel⟦ $a ⟧ rel⟦ $b ⟧)
  | `(rel⟦ $a:ralg & $b:ralg ⟧)  => `(RE.meet rel⟦ $a ⟧ rel⟦ $b ⟧)
  | `(rel⟦ $a:ralg | $b:ralg ⟧)  => `(RE.join rel⟦ $a ⟧ rel⟦ $b ⟧)
  | `(rel⟦ $a:ralg / $b:ralg ⟧)  => `(RE.div rel⟦ $a ⟧ rel⟦ $b ⟧)
  | `(rel⟦ $a:ralg \ $b:ralg ⟧)  => `(leftDivE rel⟦ $a ⟧ rel⟦ $b ⟧)

/-! ## Proofs `.ralg` files can never state -/

-- (1) Kernel-checked instance run: the division query, in surface syntax, by `decide`.
open DemoDivision in
example : (List.ofFn fun s : Fin 4 => eval rel⟦ solvedE / solvedE ⟧ s 0)
    = [true, true, false, true] := by decide

-- (2) Two programs EQUAL, generic over atoms — an allegory-law proof, no instance data.
example {a b c : FinObj} (e : RE a b) (f : RE b c) :
    eval rel⟦ (!(e) ; !(f))~ ⟧ = eval rel⟦ !(f)~ ; !(e)~ ⟧ :=
  Allegory.recip_comp (eval e) (eval f)

-- (3) Program-refines-spec via the division universal property — generic, structural.
example {a b c : FinObj} (t : RE a b) (r : RE a c) (s : RE b c) :
    eval rel⟦ !(t) ⟧ ⊑ eval rel⟦ !(r) / !(s) ⟧ ↔ eval rel⟦ !(t) ; !(s) ⟧ ⊑ eval rel⟦ !(r) ⟧ :=
  le_div_iff (eval t) (eval r) (eval s)

-- (4) The LC121 spec shape in surface syntax = the existing certified term, definitionally.
open Demo121 in
example {n M : Nat} (price : Fin n → Int) :
    eval rel⟦ Lambda(!(RE.atom (specFn n M price))) ; max(!(RE.atom (geFn M))) ⟧
      = eval (solveE n M price) := rfl

-- (5) Equal-precedence left fold parses as in .ralg: `a ; b & c` = `(a ; b) & c`.
example {a : FinObj} (e f g : RE a a) :
    eval rel⟦ !(e) ; !(f) & !(g) ⟧ = eval rel⟦ (!(e) ; !(f)) & !(g) ⟧ := rfl

-- (5b) id/eps in surface syntax; the object is a named Lean constant.
open DemoDivision in
example : eval rel⟦ eps(Student) ⟧ = epsB Student := rfl
open Demo207 in
example : eval rel⟦ !(reachE (.atom (edgeFn [(0,1)])) 3) & id(Course) ⟧
    = eval (.meet (reachE (.atom (edgeFn [(0,1)])) 3) (.id Course)) := rfl

-- (6) A verified TERM-LEVEL optimizer step: double-converse elimination preserves `eval`
--     — a theorem ABOUT programs, by cases on the AST. Unstatable for an external .ralg file.
def unconv2 : {a b : FinObj} → RE a b → RE a b
  | _, _, .conv (.conv e) => e
  | _, _, e => e

theorem eval_unconv2 {a b : FinObj} (e : RE a b) : eval (unconv2 e) = eval e := by
  match e with
  | .conv (.conv e) => exact (Allegory.recip_recip (eval e)).symm
  | .atom _ | .id _ | .comp _ _ | .conv (.atom _) | .conv (.id _) | .conv (.comp _ _)
  | .conv (.meet _ _) | .conv (.join _ _) | .conv (.bot _ _) | .conv (.top _ _)
  | .conv (.div _ _) | .conv (.eps _) | .meet _ _ | .join _ _ | .bot _ _ | .top _ _
  | .div _ _ | .eps _ => rfl

-- Regression: the call-style keywords must NOT reserve `id`/`min`/`max` as global tokens.
example : id 3 = 3 := rfl
example : min 1 2 = 1 := rfl
example : max 1 2 = 2 := rfl

end Freyd.Alg.FinRel
