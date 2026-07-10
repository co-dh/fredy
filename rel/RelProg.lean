/-
  RelProg — the FOLD sub-language of the `.ralg` interpreter (Stage 2).

  `rel.RelParse` runs RELATION terms (comp / conv / meet / join / div / power object) as Boolean
  matrices.  A catamorphism, though, has no finite matrix — it is a FOLD, evaluated at a concrete
  input by structural recursion (polynomial; contrast the exponential `Λ spec ; max D` powerset
  route in `RelParse`).  So this file adds a SECOND expression kind, split at the DECLARATION
  level: program terms (`prog`) and relation terms never mix inside one expression.

  New decl heads, on top of `RelParse`'s `obj`/`rel`/`let`/`print`:
    `prog <name> = <progExpr>`        — bind a program (catamorphism / point map / composite);
    `run  <name> [ <int>,* ]`         — apply a bound program to a non-empty Int list, print it.

  Grammar (v1, Int-only — the honest minimum for `sum` / running-max / LC121):
    progExpr := progAtom (';' progAtom)*                     (comp, left fold)
    progAtom := ident | 'cata' lam1 lam2 | 'fn' lam1 | '(' progExpr ')'
    lam1     := '(' ident '=>' vexpr ')'
    lam2     := '(' ident ident '=>' vexpr ')'
    vexpr    := vterm (('+'|'-') vterm)*                     (equal priority, left fold)
    vterm    := nat | '-' nat | ident | '(' vexpr ',' vexpr ')' | '(' vexpr ')'
              | 'fst' vterm | 'snd' vterm | 'min' vterm vterm | 'max' vterm vterm

  Everything is structural: `evalProg` recurses on the term and `List.foldlM`s the input for
  `cata` (no `partial`, no fuel), so hand-built ASTs are `by decide`-checkable.  `varP` (a
  program reference) is inlined away at declaration time by `resolveP`, so the stored term is
  CLOSED and the evaluator never meets an unbound name.

  Mathlib-free: Lean 4 core only, reusing `RelCore`'s tokenizer, `Tok`, and `parseDecl1`.
-/
import rel.RelCore

namespace Freyd.Alg.RAlg

/-! ## Runtime values and the two expression kinds -/

/-- A runtime value: an integer, a pair, or a list (the fold input). -/
inductive Val where
  | int  (n : Int)
  | pair (a b : Val)
  | list (vs : List Val)
  deriving Repr, BEq

/-- A VALUE expression `vexpr`: the point-level arithmetic inside a `fn`/`cata` lambda. -/
inductive VExpr where
  | lit  (n : Int)
  | var  (x : String)
  | add  (a b : VExpr)
  | sub  (a b : VExpr)
  | minV (a b : VExpr)
  | maxV (a b : VExpr)
  | pairE (a b : VExpr)
  | fstE (a : VExpr)
  | sndE (a : VExpr)
  deriving Repr, Inhabited

/-- A PROGRAM expression `progExpr`: a point map (`fn`), a catamorphism (`cata`), diagram-order
    composition (`compP`), or a reference to an earlier `prog` (`varP`, inlined by `resolveP`). -/
inductive PExpr where
  | fnP   (x : String) (body : VExpr)
  | cataP (bx : String) (base : VExpr) (acc el : String) (step : VExpr)
  | compP (p q : PExpr)
  | varP  (name : String)
  deriving Repr, Inhabited

-- Render a value for error messages: `int` bare, `pair` as `(a,b)`, `list` as `[a,b,…]`.
mutual
  /-- Render a value as a string for runtime error messages. -/
  def Val.show : Val → String
    | .int n    => toString n
    | .pair a b => "(" ++ Val.show a ++ "," ++ Val.show b ++ ")"
    | .list vs  => "[" ++ Val.showList vs ++ "]"
  def Val.showList : List Val → String
    | []      => ""
    | [v]     => Val.show v
    | v :: vs => Val.show v ++ "," ++ Val.showList vs
end

/-! ## The value evaluator `evalV` (runtime-typed; type errors reported) -/

/-- A binary integer operation, with a runtime type error naming the offending operands. -/
def evalIntBin (name : String) (f : Int → Int → Int) : Val → Val → Except String Val
  | .int m, .int n => .ok (.int (f m n))
  | va, vb => .error s!"{name}: int operands expected, got {va.show} and {vb.show}"

/-- Evaluate a value expression under a binding environment. -/
def evalV (env : List (String × Val)) : VExpr → Except String Val
  | .lit n => .ok (.int n)
  | .var x =>
      match env.find? (fun p => p.1 == x) with
      | some p => .ok p.2
      | none => .error s!"unbound value variable '{x}'"
  | .add a b  => do evalIntBin "+"   (· + ·) (← evalV env a) (← evalV env b)
  | .sub a b  => do evalIntBin "-"   (· - ·) (← evalV env a) (← evalV env b)
  | .minV a b => do evalIntBin "min" (fun m n => if m ≤ n then m else n) (← evalV env a) (← evalV env b)
  | .maxV a b => do evalIntBin "max" (fun m n => if m ≤ n then n else m) (← evalV env a) (← evalV env b)
  | .pairE a b => do .ok (.pair (← evalV env a) (← evalV env b))
  | .fstE a => do
      match (← evalV env a) with
      | .pair x _ => .ok x
      | v => .error s!"fst: pair expected, got {v.show}"
  | .sndE a => do
      match (← evalV env a) with
      | .pair _ y => .ok y
      | v => .error s!"snd: pair expected, got {v.show}"

/-! ## Resolution: inline earlier progs + scope-check binders (so the stored term is CLOSED) -/

/-- Check that every free value-variable of a `vexpr` is one of the `allowed` binders. -/
def checkVars (allowed : List String) : VExpr → Except String Unit
  | .lit _ => .ok ()
  | .var x => if allowed.contains x then .ok ()
              else .error s!"unbound value variable '{x}' (in scope: {allowed})"
  | .add a b | .sub a b | .minV a b | .maxV a b | .pairE a b => do
      checkVars allowed a; checkVars allowed b
  | .fstE a | .sndE a => checkVars allowed a

/-- Resolve a program term against the earlier (already-resolved) `progs`: inline every `varP`
    to its definition and scope-check each lambda body, yielding a CLOSED term. -/
def resolveP (progs : List (String × PExpr)) : PExpr → Except String PExpr
  | .fnP x body => do checkVars [x] body; .ok (.fnP x body)
  | .cataP bx base acc el step => do
      checkVars [bx] base
      checkVars [acc, el] step
      .ok (.cataP bx base acc el step)
  | .compP p q => do .ok (.compP (← resolveP progs p) (← resolveP progs q))
  | .varP name =>
      match progs.find? (fun p => p.1 == name) with
      | some p => .ok p.2
      | none => .error s!"unknown program '{name}'"

/-! ## The program evaluator `evalProg` — STRUCTURAL: term recursion + `List.foldlM` for `cata` -/

/-- Run a CLOSED program term at an input value.  `cata` folds a non-empty snoc-list: `base` on
    the head, then `List.foldlM` of `step` over the tail (empty input is an error). -/
def evalProg : PExpr → Val → Except String Val
  | .fnP x body, v => evalV [(x, v)] body
  | .cataP bx base acc el step, v =>
      match v with
      | .list (v0 :: rest) => do
          let init ← evalV [(bx, v0)] base
          rest.foldlM (fun c e => evalV [(acc, c), (el, e)] step) init
      | .list [] => .error "cata: empty input"
      | other => .error s!"cata: list input expected, got {other.show}"
  | .compP p q, v => do evalProg q (← evalProg p v)
  | .varP name, _ => .error s!"internal error: unresolved program reference '{name}'"

/-! ## Parser for `vexpr` / `progExpr` (over `RelParse`'s extended `Tok` stream) -/

mutual
  /-- `vexpr` — a vterm, then a left fold of `('+'|'-') vterm`. -/
  partial def parseVExpr (toks : List Tok) : Except String (VExpr × List Tok) := do
    let (t, rest) ← parseVTerm toks
    parseVTail t rest

  /-- The `(('+'|'-') vterm)*` tail; equal priority, one flat left fold. -/
  partial def parseVTail (acc : VExpr) : List Tok → Except String (VExpr × List Tok)
    | .plus  :: r => do let (t, r2) ← parseVTerm r; parseVTail (.add acc t) r2
    | .minus :: r => do let (t, r2) ← parseVTerm r; parseVTail (.sub acc t) r2
    | toks => .ok (acc, toks)

  /-- `vterm` — a literal, negation, variable, pair/parenthesised, or a prefix operator. -/
  partial def parseVTerm : List Tok → Except String (VExpr × List Tok)
    | .nat n :: rest => .ok (.lit (Int.ofNat n), rest)
    | .minus :: .nat n :: rest => .ok (.lit (-(Int.ofNat n)), rest)
    | .ident "fst" :: rest => do let (t, r) ← parseVTerm rest; .ok (.fstE t, r)
    | .ident "snd" :: rest => do let (t, r) ← parseVTerm rest; .ok (.sndE t, r)
    | .ident "min" :: rest => do
        let (a, r1) ← parseVTerm rest; let (b, r2) ← parseVTerm r1; .ok (.minV a b, r2)
    | .ident "max" :: rest => do
        let (a, r1) ← parseVTerm rest; let (b, r2) ← parseVTerm r1; .ok (.maxV a b, r2)
    | .ident x :: rest => .ok (.var x, rest)
    | .lparen :: rest => do
        let (a, r1) ← parseVExpr rest
        match r1 with
        | .comma :: r2 => do
            let (b, r3) ← parseVExpr r2
            match r3 with
            | .rparen :: r4 => .ok (.pairE a b, r4)
            | t :: _ => .error s!"expected ')' to close a pair, found {t.describe}"
            | [] => .error "expected ')' to close a pair, reached end of input"
        | .rparen :: r2 => .ok (a, r2)
        | t :: _ => .error s!"expected ',' or ')' in a value term, found {t.describe}"
        | [] => .error "expected ',' or ')' in a value term, reached end of input"
    | t :: _ => .error s!"unexpected token {t.describe} in a value expression"
    | [] => .error "expected a value term, reached end of input"
end

/-- `lam1 := '(' ident '=>' vexpr ')'`. -/
def parseLam1 : List Tok → Except String (String × VExpr × List Tok)
  | .lparen :: .ident x :: .darrow :: rest => do
      let (v, r1) ← parseVExpr rest
      match r1 with
      | .rparen :: r2 => .ok (x, v, r2)
      | t :: _ => .error s!"expected ')' to close a lambda, found {t.describe}"
      | [] => .error "expected ')' to close a lambda, reached end of input"
  | _ => .error "expected a lambda '( <ident> => <vexpr> )'"

/-- `lam2 := '(' ident ident '=>' vexpr ')'`. -/
def parseLam2 : List Tok → Except String (String × String × VExpr × List Tok)
  | .lparen :: .ident x :: .ident y :: .darrow :: rest => do
      let (v, r1) ← parseVExpr rest
      match r1 with
      | .rparen :: r2 => .ok (x, y, v, r2)
      | t :: _ => .error s!"expected ')' to close a lambda, found {t.describe}"
      | [] => .error "expected ')' to close a lambda, reached end of input"
  | _ => .error "expected a two-argument lambda '( <ident> <ident> => <vexpr> )'"

mutual
  /-- `progExpr` — a progAtom, then a left fold of `';' progAtom`. -/
  partial def parseProgExpr (toks : List Tok) : Except String (PExpr × List Tok) := do
    let (a, rest) ← parseProgAtom toks
    parseProgTail a rest

  /-- The `(';' progAtom)*` tail (diagram-order composition). -/
  partial def parseProgTail (acc : PExpr) : List Tok → Except String (PExpr × List Tok)
    | .semi :: r => do let (a, r2) ← parseProgAtom r; parseProgTail (.compP acc a) r2
    | toks => .ok (acc, toks)

  /-- `progAtom` — `cata`, `fn`, a reference, or a parenthesised progExpr. -/
  partial def parseProgAtom : List Tok → Except String (PExpr × List Tok)
    | .ident "cata" :: rest => do
        let (bx, base, r1) ← parseLam1 rest
        let (acc, el, step, r2) ← parseLam2 r1
        .ok (.cataP bx base acc el step, r2)
    | .ident "fn" :: rest => do
        let (x, body, r1) ← parseLam1 rest
        .ok (.fnP x body, r1)
    | .ident name :: rest => .ok (.varP name, rest)
    | .lparen :: rest => do
        let (p, r1) ← parseProgExpr rest
        match r1 with
        | .rparen :: r2 => .ok (p, r2)
        | t :: _ => .error s!"expected ')' after a program expression, found {t.describe}"
        | [] => .error "expected ')' after a program expression, reached end of input"
    | t :: _ => .error s!"unexpected token {t.describe} in a program atom"
    | [] => .error "expected a program atom, reached end of input"
end

/-- One integer literal, possibly negated. -/
def parseInt1 : List Tok → Except String (Int × List Tok)
  | .nat n :: rest => .ok (Int.ofNat n, rest)
  | .minus :: .nat n :: rest => .ok (-(Int.ofNat n), rest)
  | t :: _ => .error s!"expected an integer, found {t.describe}"
  | [] => .error "expected an integer, reached end of input"

/-- A `run` input list: the tokens AFTER `[`, comma-separated ints up to `]`. -/
partial def parseInts : List Tok → Except String (List Int × List Tok)
  | .rbracket :: rest => .ok ([], rest)
  | toks => do
      let (n, r1) ← parseInt1 toks
      match r1 with
      | .comma :: r2 => do let (more, r3) ← parseInts r2; .ok (n :: more, r3)
      | .rbracket :: r2 => .ok ([n], r2)
      | t :: _ => .error s!"expected ',' or ']' in a run list, found {t.describe}"
      | [] => .error "unterminated run list (expected ']')"

/-! ## The full-language declaration stream: `prog`/`run` + fallback to `RelParse.parseDecl1` -/

/-- A full-language declaration: a relation-level one (`RelParse.Decl`), a program binding, or a
    program run. -/
inductive PDecl where
  | rel   (d : Decl)
  | progD (name : String) (p : PExpr)
  | runD  (name : String) (input : List Int)
  deriving Inhabited

/-- Parse the whole declaration stream, dispatching `prog`/`run` first, else `parseDecl1`. -/
partial def parsePDecls : List Tok → Except String (List PDecl)
  | [] => .ok []
  | .ident "prog" :: .ident name :: .eq :: rest => do
      let (p, r1) ← parseProgExpr rest
      let ds ← parsePDecls r1
      .ok (.progD name p :: ds)
  | .ident "prog" :: _ => .error "malformed 'prog' (expected: prog <name> = <progExpr>)"
  | .ident "run" :: .ident name :: .lbracket :: rest => do
      let (input, r1) ← parseInts rest
      let ds ← parsePDecls r1
      .ok (.runD name input :: ds)
  | .ident "run" :: _ => .error "malformed 'run' (expected: run <name> [ <ints> ])"
  | toks => do
      let (d, rest) ← parseDecl1 toks
      let ds ← parsePDecls rest
      .ok (.rel d :: ds)

/-- Parse a full-language `.ralg` source string. -/
def parseProgProgram (src : String) : Except String (List PDecl) := do
  parsePDecls (← tokenize src.toList)

/-! ## Running the full language: thread the relation `Env` and the resolved program table -/

/-- Extract a printable `Int` result from a program run (used by the `run` step and the checks). -/
def progResult : Except String Val → Option Int
  | .ok (.int n) => some n
  | _ => none

/-- Run the declaration stream: relation decls go through `stepDecl` (exact `RelParse` semantics),
    `prog` decls are resolved and stored, `run` decls apply a program and print the value. -/
def runPDecls (env : Env) (progs : List (String × PExpr)) : List PDecl → IO Unit
  | [] => pure ()
  | .rel d :: ds => do let env' ← stepDecl env d; runPDecls env' progs ds
  | .progD name p :: ds => do
      match resolveP progs p with
      | .ok rp => runPDecls env (progs ++ [(name, rp)]) ds
      | .error msg => IO.eprintln s!"error in `prog {name}`: {msg}"; runPDecls env progs ds
  | .runD name input :: ds => do
      match progs.find? (fun q => q.1 == name) with
      | some q =>
        match evalProg q.2 (.list (input.map Val.int)) with
        | .ok v => IO.println v.show; runPDecls env progs ds
        | .error msg => IO.eprintln s!"error in `run {name}`: {msg}"; runPDecls env progs ds
      | none => IO.eprintln s!"unknown program '{name}'"; runPDecls env progs ds

/-- Parse and run a full-language `.ralg` source string. -/
def runProgSource (src : String) : IO Unit :=
  match parseProgProgram src with
  | .ok decls => runPDecls emptyEnv [] decls
  | .error msg => IO.eprintln s!"parse error: {msg}"

/-! ## Self-verifying demos

  The fold fixture inline (`#eval` at build time), then `by decide` checks on hand-built ASTs
  (parser-free, kernel-checked, no `native_decide`).  `progResult` reduces the `Except String Val`
  result to `Option Int`, whose `DecidableEq` `decide` can use. -/

-- The shipped fold fixture, inline: prints `14`, `5`, `5`.
#eval runProgSource
  "prog sum    = cata (x => x) (acc x => acc + x)\n\
   run sum [3, 1, 4, 1, 5]\n\
   prog runmax = cata (x => x) (m x => max m x)\n\
   run runmax [3, 1, 4, 1, 5]\n\
   prog best = cata (p => (p, 0)) (s p => (min (fst s) p, max (snd s) (p - fst s))) ; fn (s => snd s)\n\
   run best [7, 1, 5, 3, 6, 4]"

/-- `sum = cata (x => x) (acc x => acc + x)`. -/
def sumAST : PExpr := .cataP "x" (.var "x") "acc" "x" (.add (.var "acc") (.var "x"))

/-- `runmax = cata (x => x) (m x => max m x)`. -/
def runmaxAST : PExpr := .cataP "x" (.var "x") "m" "x" (.maxV (.var "m") (.var "x"))

/-- `best = cata (p => (p, 0)) (s p => (min (fst s) p, max (snd s) (p - fst s))) ; fn (s => snd s)`. -/
def bestAST : PExpr :=
  .compP
    (.cataP "p" (.pairE (.var "p") (.lit 0))
       "s" "p" (.pairE (.minV (.fstE (.var "s")) (.var "p"))
                       (.maxV (.sndE (.var "s")) (.sub (.var "p") (.fstE (.var "s"))))))
    (.fnP "s" (.sndE (.var "s")))

/-- Build a `Val.list` of ints (parser-free, so `by decide` can reduce it). -/
def intList (ns : List Int) : Val := .list (ns.map Val.int)

-- Sum, running-max, and LC121's best profit, all by structural fold, kernel-checked:
example : progResult (evalProg sumAST    (intList [3, 1, 4, 1, 5]))    = some 14 := by decide
example : progResult (evalProg runmaxAST (intList [3, 1, 4, 1, 5]))    = some 5  := by decide
example : progResult (evalProg bestAST   (intList [7, 1, 5, 3, 6, 4])) = some 5  := by decide

-- Empty input is an error; a non-list input is an error.
example : progResult (evalProg sumAST (.list []))     = none := by decide
example : progResult (evalProg sumAST (.int 3))       = none := by decide

end Freyd.Alg.RAlg

/-- Entry point for the FULL language (relation decls + `prog`/`run`): read a `.ralg` file and
    run it.  Defaults to the fold fixture. -/
def main (args : List String) : IO Unit := do
  let path := args.getD 0 "rel/examples/fold.ralg"
  let src ← IO.FS.readFile path
  Freyd.Alg.RAlg.runProgSource src
