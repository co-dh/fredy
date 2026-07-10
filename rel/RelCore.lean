/-
  RelCore — the shared CORE of the `.ralg` relation-algebra interpreter (no `main`).

  RelInterp (`rel.RelInterp`) runs relation-algebra terms that are hand-built as Lean values
  (its `DemoDivision` hardcodes `solvedFn` and evaluates a division query in Lean).  This module
  makes the SAME kind of query expressible as an EXTERNAL text file: a `.ralg` program is
  parsed and evaluated at runtime.

  It is deliberately self-contained.  Rather than route through RelInterp's dependently-typed
  `FinRel`/`eval` (objects `Fin n`, morphisms `Fin m → Fin n → Bool`), it carries its own plain
  Boolean-matrix type `Mat` and computes each operation directly, with the dimension agreements
  (that `FinRel` gets for free from the types) checked at runtime via `Except String`.  The
  semantics MIRROR `FinRel` exactly: comp / conv / meet / join / div / id / top / bot, plus the
  §2.41 power object (`eps`/`Lambda`/`min`/`max`, subsets coded as the bits of a `Nat`).

  Three parts:
    * the `.ralg` language          — objects, ground relations (edge lists), `let`, `print`;
    * a hand-rolled tokenizer + recursive-descent parser over `List Char` / `List Tok`;
    * a direct Boolean-matrix evaluator with runtime dimension checks.

  The expression grammar has NO precedence hierarchy: `;` (comp), `&` (meet), `|` (join),
  `/` (right division), `\` (left division) all have EQUAL priority and fold LEFT-associatively,
  so `a ; b & c` means `(a ; b) & c`.  Postfix `~` (converse) binds tighter, as part of a primary;
  the power prefixes `eps`/`Lambda`/`min`/`max` bind tighter than the binops too.

  This module carries NO root `main`, so BOTH the relation-language CLI (`rel.RelParse`) and the
  full-language CLI (`rel.RelProg`) can import it and each declare their own runnable `main`
  without a redeclaration clash (Lean forbids two `_root_.main` in one import closure).

  Mathlib-free: Lean 4 core only (`IO.FS.readFile`, `List`, `String`, `Char`, `Nat.testBit`).
  The `#eval`/`example` demos at the bottom are self-verifying at build time; their
  `#print axioms` are ⊆ {propext, Quot.sound} (the matrix ops are ordinary structural defs).
-/

namespace Freyd.Alg.RAlg

/-! ## Boolean matrices — the executable morphisms

  A `Mat` is a Boolean matrix with its own row/column dimensions.  `get i j` for out-of-range
  `i`/`j` is unconstrained (callers only ever read `i < r`, `j < c`); keeping `get` a bare
  function makes every operation a one-liner and lets `by decide` reduce it. -/

/-- A Boolean matrix: `r` rows, `c` columns, entries `get i j : Bool`. -/
structure Mat where
  r : Nat
  c : Nat
  get : Nat → Nat → Bool

/-- Ground relation from an edge list `edges : List (src → tgt)`, sized `src × tgt`. -/
def mkRel (src tgt : Nat) (edges : List (Nat × Nat)) : Mat :=
  ⟨src, tgt, fun i j => edges.any (fun e => e.1 == i && e.2 == j)⟩

/-- Identity `id o`: the `o × o` diagonal. -/
def idMat (o : Nat) : Mat := ⟨o, o, fun i j => i == j⟩

/-- `top s t` / `bot s t`: the all-true / all-false `s × t` matrix. -/
def topMat (s t : Nat) : Mat := ⟨s, t, fun _ _ => true⟩
def botMat (s t : Nat) : Mat := ⟨s, t, fun _ _ => false⟩

/-- Converse `a~`: transpose (a `c × r` matrix reading `get j i`). -/
def Mat.conv (a : Mat) : Mat := ⟨a.c, a.r, fun i j => a.get j i⟩

/-- Composition `a ; b` (diagram order): needs `a.c = b.r`; result `a.r × b.c`,
    `get i j = ∃ k < a.c, a k && b k j`. -/
def compMat (a b : Mat) : Except String Mat :=
  if a.c == b.r then
    .ok ⟨a.r, b.c, fun i j => (List.range a.c).any (fun k => a.get i k && b.get k j)⟩
  else .error s!"comp (;): dimension mismatch, left has {a.c} columns but right has {b.r} rows"

/-- Meet `a & b` (∩): needs equal dims; pointwise `&&`. -/
def meetMat (a b : Mat) : Except String Mat :=
  if a.r == b.r && a.c == b.c then .ok ⟨a.r, a.c, fun i j => a.get i j && b.get i j⟩
  else .error s!"meet (&): dimension mismatch, {a.r}x{a.c} vs {b.r}x{b.c}"

/-- Join `a | b` (∪): needs equal dims; pointwise `||`. -/
def joinMat (a b : Mat) : Except String Mat :=
  if a.r == b.r && a.c == b.c then .ok ⟨a.r, a.c, fun i j => a.get i j || b.get i j⟩
  else .error s!"join (|): dimension mismatch, {a.r}x{a.c} vs {b.r}x{b.c}"

/-- Right division `a / b` = `R/S` with `R = a : X → Z`, `S = b : Y → Z`: needs `a.c = b.c`;
    result `a.r × b.r`, `get i j = ∀ k < a.c, b j k → a i k` (i.e. `b`'s row `j` ⊆ `a`'s row `i`). -/
def divMat (a b : Mat) : Except String Mat :=
  if a.c == b.c then
    .ok ⟨a.r, b.r, fun i j => (List.range a.c).all (fun k => !b.get j k || a.get i k)⟩
  else .error s!"div (/): dimension mismatch, both operands need equal column counts ({a.c} vs {b.c})"

/-! ## Power object + the §2.41 power-transpose operators

  A subset of an `n`-element object is coded little-endian by a `Nat` `P < 2^n`: element `y`
  is a member iff `Nat.testBit P y`.  So the power object `[a]` of an `n`-element `a` has `2^n`
  elements.  `powCard` is the single size guard: `2^n` is refused past `n = 16` (65536 codes),
  well before the matrix ops become unusable.  The four operators are the BOOK definitions
  verbatim, reusing `divMat`/`meetMat`/`.conv`:
    `∋ : [a] ⟶ a`     — membership,          `epsMat n = ⟨2^n, n, testBit⟩`
    `Λ R = (R/∋) ∩ (∋/R)°`                    — power transpose (§2.331/§2.41)
    `S\R = (R°/S°)°`                          — left division (§2.312)
    `min R = ∋ ∩ (∋°\R)`, `max R = min R°`    — B&dM §7.1 extrema. -/

/-- The one size guard for power objects: `card [a] = 2^(card a)`, refused past `2^16`. -/
def powCard (n : Nat) : Except String Nat :=
  if n ≤ 16 then .ok (2^n) else .error s!"pow: card {n} > 16 blows up (2^{n} codes)"

/-- Membership `∋ : [a] ⟶ a` — a `2^n × n` matrix, entry `(P,y) = (y ∈ code P)`.  Callers
    guard the `2^n` size via `powCard` before building this. -/
def epsMat (n : Nat) : Mat := ⟨2^n, n, fun P y => Nat.testBit P y⟩

/-- Power transpose `Λ R = (R/∋) ∩ (∋/R)°` (§2.41): relates `x` to the bit-code of `x`'s image. -/
def lambdaMat (m : Mat) : Except String Mat := do
  let _ ← powCard m.c
  let e := epsMat m.c
  meetMat (← divMat m e) (← divMat e m).conv

/-- Left division `S\R = (R°/S°)°` (§2.312). -/
def leftDivMat (s r : Mat) : Except String Mat := (·.conv) <$> divMat r.conv s.conv

/-- `min R = ∋ ∩ (∋°\R)` (B&dM §7.1): the `≤`-least member of each subset under `R`.  Needs `R`
    square (it is an endorelation on `a`). -/
def minMat (m : Mat) : Except String Mat := do
  if m.r == m.c then
    let _ ← powCard m.r
    let e := epsMat m.r
    meetMat e (← leftDivMat e.conv m)
  else .error s!"min: needs a square relation, got {m.r}x{m.c}"

/-- `max R = min R°` (B&dM §7.1). -/
def maxMat (m : Mat) : Except String Mat := minMat m.conv

/-! ## The `.ralg` language: tokens, expression AST, declarations -/

/-- A lexical token. -/
inductive Tok where
  | ident (s : String)   -- identifier / keyword (obj, rel, let, print, id, top, bot, names)
  | nat (n : Nat)        -- a natural-number literal
  | semi                 -- ;  composition
  | amp                  -- &  meet
  | bar                  -- |  join
  | slash                -- /  right division
  | backslash            -- \  left division
  | tilde                -- ~  converse (postfix)
  | lparen | rparen      -- ( )
  | arrow                -- ->
  | colon                -- :
  | eq                   -- =
  -- Stage-2 (fold sub-language) additions; backward-compatible (each was a lex error before).
  | plus                 -- +
  | minus                -- -   (a bare '-', not a '--' comment nor a '->' arrow)
  | comma                -- ,
  | lbracket | rbracket  -- [ ]
  | darrow               -- =>  (checked before '=')
  deriving Repr, Inhabited

/-- Human-readable token, for error messages. -/
def Tok.describe : Tok → String
  | .ident s   => s!"'{s}'"
  | .nat n     => s!"'{n}'"
  | .semi      => "';'"
  | .amp       => "'&'"
  | .bar       => "'|'"
  | .slash     => "'/'"
  | .backslash => "'\\'"
  | .tilde     => "'~'"
  | .lparen    => "'('"
  | .rparen    => "')'"
  | .arrow     => "'->'"
  | .colon     => "':'"
  | .eq        => "'='"
  | .plus      => "'+'"
  | .minus     => "'-'"
  | .comma     => "','"
  | .lbracket  => "'['"
  | .rbracket  => "']'"
  | .darrow    => "'=>'"

inductive BinOp where
  | comp | meet | join | div | ldiv
  deriving Repr, Inhabited

/-- Object EXPRESSIONS: an object name, or the power object `pow o` (`card (pow o) = 2^(card o)`). -/
inductive ObjE where
  | name (s : String)
  | pow  (o : ObjE)
  deriving Repr, Inhabited

/-- A relation-algebra expression (untyped; objects resolved at evaluation). -/
inductive Expr where
  | var    (name : String)       -- an atom or a let-bound name
  | idE    (obj : ObjE)          -- id <objExpr>
  | topE   (s t : ObjE)          -- top <objExpr> <objExpr>
  | botE   (s t : ObjE)          -- bot <objExpr> <objExpr>
  | epsE   (o : ObjE)            -- eps <objExpr>          — membership ∋ : [o] ⟶ o
  | lambdaE (e : Expr)           -- Lambda <postfix>       — power transpose Λ
  | minE   (e : Expr)            -- min <postfix>          — B&dM min R
  | maxE   (e : Expr)            -- max <postfix>          — B&dM max R
  | conv   (e : Expr)            -- e~
  | bin    (op : BinOp) (l r : Expr)
  deriving Repr, Inhabited

/-- A top-level declaration. -/
inductive Decl where
  | obj   (name : String) (card : Nat)
  | rel   (name : String) (src tgt : ObjE) (edges : List (Nat × Nat))
  | letD  (name : String) (e : Expr)
  | printD (e : Expr)
  deriving Repr, Inhabited

/-! ## Tokenizer over `List Char` -/

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentChar  (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Longest prefix satisfying `p`, and the remainder. -/
def spanChars (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if p c then let (a, b) := spanChars p cs; (c :: a, b) else ([], c :: cs)

/-- Drop everything up to and including the next newline (a `--` line comment). -/
def dropLine : List Char → List Char
  | [] => []
  | '\n' :: cs => cs
  | _ :: cs => dropLine cs

/-- Digits (base 10) to a `Nat`. -/
def natOfDigits (ds : List Char) : Nat :=
  ds.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0

/-- Lex the whole source into tokens.  `partial` (the recursion consumes a variable-length
    prefix per step); only ever run from the compiled evaluator, never from a `by decide`. -/
partial def tokenize : List Char → Except String (List Tok)
  | [] => .ok []
  | c :: cs =>
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then tokenize cs
    else if c == '-' then
      match cs with
      | '-' :: rest => tokenize (dropLine rest)          -- '--' line comment
      | '>' :: rest => (.arrow :: ·) <$> tokenize rest   -- '->' arrow
      | _ => (.minus :: ·) <$> tokenize cs               -- a bare '-'
    else if c == ';' then (.semi     :: ·) <$> tokenize cs
    else if c == '&' then (.amp      :: ·) <$> tokenize cs
    else if c == '|' then (.bar      :: ·) <$> tokenize cs
    else if c == '/' then (.slash    :: ·) <$> tokenize cs
    else if c == '\\' then (.backslash :: ·) <$> tokenize cs
    else if c == '~' then (.tilde    :: ·) <$> tokenize cs
    else if c == '(' then (.lparen   :: ·) <$> tokenize cs
    else if c == ')' then (.rparen   :: ·) <$> tokenize cs
    else if c == ':' then (.colon    :: ·) <$> tokenize cs
    else if c == '=' then
      match cs with
      | '>' :: rest => (.darrow :: ·) <$> tokenize rest  -- '=>' checked before '='
      | _ => (.eq :: ·) <$> tokenize cs
    else if c == '+' then (.plus     :: ·) <$> tokenize cs
    else if c == ',' then (.comma    :: ·) <$> tokenize cs
    else if c == '[' then (.lbracket :: ·) <$> tokenize cs
    else if c == ']' then (.rbracket :: ·) <$> tokenize cs
    else if c.isDigit then
      let (ds, rest) := spanChars Char.isDigit (c :: cs)
      (.nat (natOfDigits ds) :: ·) <$> tokenize rest
    else if isIdentStart c then
      let (name, rest) := spanChars isIdentChar (c :: cs)
      (.ident (String.ofList name) :: ·) <$> tokenize rest
    else .error s!"unexpected character '{c}'"

/-! ## Recursive-descent parser

  Grammar (flat, equal-precedence, left-associative):
    expr    := postfix ( (';'|'&'|'|'|'/'|'\') postfix )*  -- left fold, NO precedence climbing
    postfix := primary ( '~' )*
    primary := ident | 'id' objExpr | 'top' objExpr objExpr | 'bot' objExpr objExpr
             | 'eps' objExpr | 'Lambda' postfix | 'min' postfix | 'max' postfix | '(' expr ')'
    objExpr := ident | 'pow' objExpr
  The four power primaries are PREFIX keywords over ONE postfix operand, so they bind tighter
  than the binops: `Lambda spec ; max ge` = `(Lambda spec) ; (max ge)`; parenthesise a compound
  operand — `Lambda (f ; g)`.
-/

/-- `objExpr` — an object name or a `pow` tower. -/
partial def parseObjE : List Tok → Except String (ObjE × List Tok)
  | .ident "pow" :: rest => do let (o, r) ← parseObjE rest; .ok (.pow o, r)
  | .ident s :: rest => .ok (.name s, rest)
  | t :: _ => .error s!"expected an object expression, found {t.describe}"
  | [] => .error "expected an object expression, reached end of input"

/-- Fold trailing `~` tokens into stacked converses. -/
def applyTildes (e : Expr) : List Tok → Expr × List Tok
  | .tilde :: rest => applyTildes (.conv e) rest
  | toks => (e, toks)

mutual
  /-- `expr` — parse a postfix, then greedily fold `(binop postfix)` left-to-right. -/
  partial def parseExpr (toks : List Tok) : Except String (Expr × List Tok) := do
    let (e, rest) ← parsePostfix toks
    parseBinTail e rest

  /-- The `( binop postfix )*` tail; equal precedence, so one flat left fold. -/
  partial def parseBinTail (acc : Expr) : List Tok → Except String (Expr × List Tok)
    | .semi      :: r => do let (e, r2) ← parsePostfix r; parseBinTail (.bin .comp acc e) r2
    | .amp       :: r => do let (e, r2) ← parsePostfix r; parseBinTail (.bin .meet acc e) r2
    | .bar       :: r => do let (e, r2) ← parsePostfix r; parseBinTail (.bin .join acc e) r2
    | .slash     :: r => do let (e, r2) ← parsePostfix r; parseBinTail (.bin .div  acc e) r2
    | .backslash :: r => do let (e, r2) ← parsePostfix r; parseBinTail (.bin .ldiv acc e) r2
    | toks => .ok (acc, toks)

  /-- `postfix` — a primary with any number of trailing `~`. -/
  partial def parsePostfix (toks : List Tok) : Except String (Expr × List Tok) := do
    let (e, rest) ← parsePrimary toks
    .ok (applyTildes e rest)

  /-- `primary` — a name, an `id`/`top`/`bot`/`eps`/`Lambda`/`min`/`max` form, or a `( expr )`. -/
  partial def parsePrimary : List Tok → Except String (Expr × List Tok)
    | .ident s :: rest =>
      if s == "id" then do
        let (o, r2) ← parseObjE rest; .ok (.idE o, r2)
      else if s == "top" then do
        let (a, r2) ← parseObjE rest; let (b, r3) ← parseObjE r2; .ok (.topE a b, r3)
      else if s == "bot" then do
        let (a, r2) ← parseObjE rest; let (b, r3) ← parseObjE r2; .ok (.botE a b, r3)
      else if s == "eps" then do
        let (o, r2) ← parseObjE rest; .ok (.epsE o, r2)
      else if s == "Lambda" then do
        let (e, r2) ← parsePostfix rest; .ok (.lambdaE e, r2)
      else if s == "min" then do
        let (e, r2) ← parsePostfix rest; .ok (.minE e, r2)
      else if s == "max" then do
        let (e, r2) ← parsePostfix rest; .ok (.maxE e, r2)
      else .ok (.var s, rest)
    | .lparen :: rest => do
      let (e, r2) ← parseExpr rest
      match r2 with
      | .rparen :: r3 => .ok (e, r3)
      | t :: _ => .error s!"expected ')' but found {t.describe}"
      | [] => .error "expected ')' but reached end of input"
    | t :: _ => .error s!"unexpected token {t.describe}, expected an expression"
    | [] => .error "unexpected end of input, expected an expression"
end

/-- The edge list of a `rel`: consume `<nat> -> <nat>` triples greedily; stop at the next
    non-numeric token (the following declaration head, or end of input). -/
def parseEdges : List Tok → List (Nat × Nat) × List Tok
  | .nat i :: .arrow :: .nat j :: rest => let (es, r) := parseEdges rest; ((i, j) :: es, r)
  | toks => ([], toks)

/-- Parse ONE relation-level declaration (`obj`/`rel`/`let`/`print`), returning the remaining
    tokens.  Exposed so the Stage-2 driver (`rel.RelProg`) can loop over it, matching its own
    `prog`/`run` heads first and falling back here. -/
def parseDecl1 : List Tok → Except String (Decl × List Tok)
  | .ident "obj" :: .ident name :: .nat card :: rest => .ok (.obj name card, rest)
  | .ident "obj" :: _ => .error "malformed 'obj' (expected: obj <name> <nat>)"
  | .ident "rel" :: .ident name :: .colon :: rest => do
    let (src, r1) ← parseObjE rest
    match r1 with
    | .arrow :: r2 =>
      let (tgt, r3) ← parseObjE r2
      match r3 with
      | .eq :: r4 => let (edges, r5) := parseEdges r4; .ok (.rel name src tgt edges, r5)
      | _ => .error "malformed 'rel' (expected '=' before the edge list)"
    | _ => .error "malformed 'rel' (expected '->' between the two objects)"
  | .ident "rel" :: _ => .error "malformed 'rel' (expected: rel <name> : <obj> -> <obj> = <edges>)"
  | .ident "let" :: .ident name :: .eq :: rest => do
    let (e, rest2) ← parseExpr rest; .ok (.letD name e, rest2)
  | .ident "let" :: _ => .error "malformed 'let' (expected: let <name> = <expr>)"
  | .ident "print" :: rest => do
    let (e, rest2) ← parseExpr rest; .ok (.printD e, rest2)
  | t :: _ => .error s!"unexpected token {t.describe} at top level (expected obj/rel/let/print)"
  | [] => .error "expected a declaration, reached end of input"

/-- Parse a whole program: a sequence of declarations, looping `parseDecl1`. -/
partial def parseDecls : List Tok → Except String (List Decl)
  | [] => .ok []
  | toks => do
    let (d, rest) ← parseDecl1 toks
    let ds ← parseDecls rest
    .ok (d :: ds)

/-- Parse a `.ralg` source string. -/
def parseProgram (src : String) : Except String (List Decl) := do
  parseDecls (← tokenize src.toList)

/-! ## Evaluation environment and the expression evaluator -/

/-- Objects (name → cardinality), ground relations (name → src/tgt cards + matrix), and
    `let`-bindings (name → matrix). -/
structure Env where
  objs : List (String × Nat)
  rels : List (String × Nat × Nat × Mat)
  lets : List (String × Mat)

def emptyEnv : Env := ⟨[], [], []⟩

def Env.lookupObj (env : Env) (n : String) : Except String Nat :=
  match env.objs.find? (fun p => p.1 == n) with
  | some p => .ok p.2
  | none => .error s!"unknown object '{n}'"

/-- Evaluate an object expression to a cardinality: a name is looked up, `pow o` is `2^(card o)`
    (guarded by `powCard`). -/
def Env.evalObj (env : Env) : ObjE → Except String Nat
  | .name s => env.lookupObj s
  | .pow o  => do powCard (← env.evalObj o)

/-- Resolve a name to a matrix: `let`-bindings first, then ground relations. -/
def Env.lookupVar (env : Env) (n : String) : Except String Mat :=
  match env.lets.find? (fun p => p.1 == n) with
  | some p => .ok p.2
  | none =>
    match env.rels.find? (fun p => p.1 == n) with
    | some p => .ok p.2.2.2
    | none => .error s!"unknown relation or binding '{n}'"

/-- Evaluate an expression to a matrix, checking dimension agreements at each step. -/
def evalExpr (env : Env) : Expr → Except String Mat
  | .var n     => env.lookupVar n
  | .idE o     => do pure (idMat (← env.evalObj o))
  | .topE s t  => do pure (topMat (← env.evalObj s) (← env.evalObj t))
  | .botE s t  => do pure (botMat (← env.evalObj s) (← env.evalObj t))
  | .epsE o    => do let n ← env.evalObj o; let _ ← powCard n; pure (epsMat n)
  | .lambdaE e => do lambdaMat (← evalExpr env e)
  | .minE e    => do minMat (← evalExpr env e)
  | .maxE e    => do maxMat (← evalExpr env e)
  | .conv e    => do pure (← evalExpr env e).conv
  | .bin op l r => do
    let a ← evalExpr env l
    let b ← evalExpr env r
    match op with
    | .comp => compMat a b
    | .meet => meetMat a b
    | .join => joinMat a b
    | .div  => divMat a b
    | .ldiv => leftDivMat a b

/-! ## Rendering + running -/

/-- Render a matrix as rows of `0`/`1`. -/
def matRows (m : Mat) : List String :=
  (List.range m.r).map fun i =>
    String.ofList <| (List.range m.c).map fun j => if m.get i j then '1' else '0'

/-- Print a matrix: a `[r x c]` header, then its rows. -/
def printMat (m : Mat) : IO Unit := do
  IO.println s!"[{m.r} x {m.c}]"
  for row in matRows m do IO.println row

/-- Process ONE declaration: extend the environment, or (on `print`) evaluate and print; on an
    error, report it and return the environment unchanged.  Exposed so the Stage-2 driver
    (`rel.RelProg`) reuses the exact relation-level semantics while it interleaves its own
    `prog`/`run` steps. -/
def stepDecl (env : Env) : Decl → IO Env
  | .obj name card => pure { env with objs := env.objs ++ [(name, card)] }
  | .rel name src tgt edges => do
    match (do pure (← env.evalObj src, ← env.evalObj tgt)) with
    | .ok (cs, ct) => pure { env with rels := env.rels ++ [(name, cs, ct, mkRel cs ct edges)] }
    | .error msg => IO.eprintln s!"error in `rel {name}`: {msg}"; pure env
  | .letD name e => do
    match evalExpr env e with
    | .ok m => pure { env with lets := env.lets ++ [(name, m)] }
    | .error msg => IO.eprintln s!"error in `let {name}`: {msg}"; pure env
  | .printD e => do
    match evalExpr env e with
    | .ok m => printMat m; pure env
    | .error msg => IO.eprintln s!"error in `print`: {msg}"; pure env

/-- Run a program: fold the declarations through `stepDecl`, threading the environment. -/
def runDecls (env : Env) : List Decl → IO Unit
  | [] => pure ()
  | d :: ds => do runDecls (← stepDecl env d) ds

/-- Parse and run a `.ralg` source string. -/
def runSource (src : String) : IO Unit :=
  match parseProgram src with
  | .ok decls => runDecls emptyEnv decls
  | .error msg => IO.eprintln s!"parse error: {msg}"

/-! ## Self-verifying demos

  `#eval`s exercise the whole pipeline (tokenize → parse → evaluate → print) on inline
  `.ralg` strings; the `example … := by decide` checks pin the matrix ops on the division
  fixture (kernel-checked, no parser, no `native_decide`). -/

/-- The division fixture's ground relation, built directly (not via the parser) so `decide`
    can reduce it. -/
def solvedMat : Mat := mkRel 4 4 [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,3)]

/-- Read entry `(i,j)` of an `Except`-wrapped matrix (`false` on an error result) — lets the
    `by decide` checks compare `List Bool` (which has `DecidableEq`) instead of `Except`. -/
def matBit : Except String Mat → Nat → Nat → Bool
  | .ok m, i, j => m.get i j
  | .error _, _, _ => false

-- Run the two shipped fixtures inline:
#eval runSource
  "obj student 4\nobj problem 4\n\
   rel solved : student -> problem = 0->0 0->1 1->0 1->1 1->2 2->1 3->0 3->1 3->3\n\
   print solved / solved"

-- Reachability (comp + join), the reach.ralg body:
#eval runSource
  "obj node 4\nrel edge : node -> node = 0->1 1->2 2->3\nprint edge ; edge | edge"

-- A `let` binding and a converse: `r` is the 2-cycle swap; `r~` is its transpose (itself);
-- `s ; s` where `s = r` is the identity.
#eval runSource
  "obj a 2\nrel r : a -> a = 0->1 1->0\nlet s = r~\nprint s ; s"

-- Equal-precedence left fold: `top a a & id a | bot a a` parses as
-- `((top & id) | bot)` = `id` (meet with top is a no-op, join with bot is a no-op).
#eval runSource "obj a 3\nprint top a a & id a | bot a a"

-- A dimension-mismatch error is reported clearly (composing a 2x3 with a 2x3):
#eval runSource
  "obj a 2\nobj b 3\nrel r : a -> b = 0->0 1->2\nprint r ; r"

-- `by decide` sanity checks on the matrix ops (division fixture), no parser involved.
-- Row 0 of `solved / solved` is `1 0 1 0`: student 0 solved {0,1}, a superset of the sets
-- of students 0 ({0,1}) and 2 ({1}) but not of 1 ({0,1,2}) or 3 ({0,1,3}).
example :
    (List.range 4).map (fun j => matBit (divMat solvedMat solvedMat) 0 j)
      = [true, false, true, false] := by decide

-- Column 0 (Alice, {0,1}) selects students 0,1,3: rows 0,1,3 have a 1, row 2 has a 0.
example :
    (List.range 4).map (fun i => matBit (divMat solvedMat solvedMat) i 0)
      = [true, true, false, true] := by decide

-- Composition + join (reachability): with `edge = 0->1->2->3`, row 0 of `edge ; edge | edge`
-- is `0 1 1 0` — node 0 reaches 1 (one step) and 2 (two steps), but not 3 (three) or itself.
def reachEx : Except String Mat := do
  let e := mkRel 4 4 [(0,1),(1,2),(2,3)]
  joinMat (← compMat e e) e

example :
    (List.range 4).map (fun j => matBit reachEx 0 j) = [false, true, true, false] := by decide

/-! ### Power-object demos (Stage 1): `eps`, `Lambda`, `min`, `max`, `pow`

  The LC121 spec fixture, run through the full pipeline and pinned by parser-free `by decide`
  checks on the matrix ops. `spec : one → val` sends the single point to profit-codes `{1,2}`;
  `ge : val → val` is `z ≤ w`.  `Lambda spec` is a `1 × 8` row selecting code `6 = {1,2}`;
  `Lambda spec ; max ge` is a `1 × 3` row selecting code `2` (the `≤`-greatest achievable
  profit), agreeing with `RelInterp.Demo121`. -/

-- The LC121 spec fixture inline (prices [1,2], M=1): prints `Lambda spec` then `Lambda spec ; max ge`.
#eval runSource
  "obj one 1\nobj val 3\n\
   rel spec : one -> val = 0->1 0->2\n\
   rel ge   : val -> val = 0->0 1->0 1->1 2->0 2->1 2->2\n\
   print Lambda spec\nprint Lambda spec ; max ge"

-- `eps val` is membership ∋ : [val] ⟶ val, an `8 × 3` matrix; `pow` in an object expression:
#eval runSource "obj val 3\nprint eps val"
#eval runSource "obj two 2\nprint id pow two"     -- identity on [two] = [pow two]: a 4×4 diagonal

-- The fixture's two ground relations, built directly (no parser) so `by decide` can reduce them.
def specMat : Mat := mkRel 1 3 [(0,1),(0,2)]
def geMat   : Mat := mkRel 3 3 [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2)]

-- `Lambda spec` is `1 × 8`, row 0 = code 6 = {1,2} only:  `00000010`.
example :
    (List.range 8).map (fun j => matBit (lambdaMat specMat) 0 j)
      = [false,false,false,false,false,false,true,false] := by decide

-- `max ge` (`8 × 3`) at code 6 = {1,2} picks the ≤-greatest member, `2`:
example :
    (List.range 3).map (fun j => matBit (maxMat geMat) 6 j) = [false, false, true] := by decide

-- `Lambda spec ; max ge` is `1 × 3`, row 0 = code 2 (best profit +1):  `001`.
def lc121Mat : Except String Mat := do compMat (← lambdaMat specMat) (← maxMat geMat)
example :
    (List.range 3).map (fun j => matBit lc121Mat 0 j) = [false, false, true] := by decide

-- `eps 3` is the membership matrix `∋ : [·] ⟶ ·`: code `P`'s row is its bit pattern.
-- Row 6 = {1,2} reads `0 1 1` (bit 0 clear, bits 1,2 set):
example :
    (List.range 3).map (fun j => epsMat 3 |>.get 6 j) = [false, true, true] := by decide

end Freyd.Alg.RAlg
