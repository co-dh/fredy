/-
  Compile a Freyd Q-sequence SENTENCE to its diagram, IN LEAN.

  Freyd draws a Q-sequence as a left-to-right run of growing finitely-presented diagrams
  (PANELS) separated by tall VERTICAL BARS, each bar carrying its quantifier (∀ / ∃ / !) ON
  TOP (book §1.39/§1.41/§1.395).  The picture must be DERIVED from the logic, not hand-placed
  from the book's figure.  So the input is a `Sentence`: a telescope of quantifier `SStep`s,
  each binding new objects and typed `SArr`s, plus `SPred`s (monic, jointCover).  `compile`
  computes the layout — objects LAYERED by longest-path over the arrows (target below source),
  x by parent barycentre with collision spread, edges spanning ≥2 layers bent around the
  vertices, joint covers drawn as ONE arc — and `render` emits Typst + fletcher.

  Universal properties use a `∃` step then a `!` step (Freyd's at-most-one bar) — never a
  combined `∃!`.  Book sentences provided: §1.39 left-invertible, §1.41 monic, §1.412
  sub-terminator, §1.421 terminator, §1.423 binary product, §1.428 equalizer, §1.431
  pullback, §1.611 empty/binary union + cover-transfer.  See `bookSentences`.

  Run:  lake env lean --run Fredy/tool/QSeqRender.lean   (writes Fredy/tool/out/*.typ)
-/

namespace QSeqRender

structure Node where
  label : String
  x : Int
  y : Int

structure Edge where
  x1 : Int
  y1 : Int
  x2 : Int
  y2 : Int
  label : String
  mark  : String := "->"   -- "->" plain, ">->" monic, "->>" cover, "-" headless line
  shift : Int := 0         -- pt offset, for parallel pairs
  side  : String := ""     -- label-side: "left" (above) / "right" (below)
  bend  : Int := 0         -- curve, in degrees (for the joint-cover arc)

structure Panel where
  nodes : List Node
  edges : List Edge

/-- A diagram-sequence item: a panel, or a quantifier bar (`forall`/`exists`/`!`). -/
inductive Item
  | panel (p : Panel)
  | bar (q : String)

structure QDiagram where
  title   : String
  meaning : String
  items   : List Item

/-! ## Typst emission -/

private def I (n : Int) : String := toString n

private def nodeLine (n : Node) : String :=
  "node((" ++ I n.x ++ ", " ++ I n.y ++ "), $" ++ n.label ++ "$)"

private def edgeLine (e : Edge) : String :=
  let lbl := if e.label == "" then "" else "$" ++ e.label ++ "$, "
  let sh  := if e.shift == 0 then "" else ", shift: " ++ I e.shift ++ "pt"
  let sd  := if e.side  == "" then "" else ", label-side: " ++ e.side
  let bd  := if e.bend == 0 then "" else ", bend: " ++ I e.bend ++ "deg"
  "edge((" ++ I e.x1 ++ ", " ++ I e.y1 ++ "), (" ++ I e.x2 ++ ", " ++ I e.y2 ++ "), "
    ++ lbl ++ "\"" ++ e.mark ++ "\"" ++ sh ++ sd ++ bd ++ ")"

/-- A panel becomes a fletcher `diagram(...)` (a grid-cell, so bare — no leading `#`). -/
private def panelStr (p : Panel) : String :=
  let parts := (p.nodes.map nodeLine) ++ (p.edges.map edgeLine)
  "diagram(spacing: (13mm, 12mm), node-stroke: none, " ++ String.intercalate ", " parts ++ ")"

/-- Map a quantifier token to its Typst math (`exists!` → ∃!). -/
private def barSym : String → String
  | "exists!" => "exists #h(1pt) !"
  | q         => q

/-- A bar is a fixed-height box: quantifier on top (§1.39), a tall vertical line below. -/
private def barStr (q : String) : String :=
  "box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$"
    ++ barSym q ++ "$]], line(length: 28mm, angle: 90deg))]"

private def itemStr : Item → String
  | .panel p => panelStr p
  | .bar q   => barStr q

def render (d : QDiagram) : String :=
  let items := d.items.map itemStr
  let grid := "#grid(columns: " ++ toString items.length
    ++ ", align: horizon, column-gutter: 7mm,\n  " ++ String.intercalate ",\n  " items ++ "\n)"
  String.intercalate "\n"
    [ "#import \"@preview/fletcher:0.5.8\" as fletcher: diagram, node, edge",
      "#set page(width: auto, height: auto, margin: 9mm)",
      "#set text(size: 11pt, font: \"New Computer Modern\")", "",
      "#align(center)[#text(13pt, weight: \"bold\")[" ++ d.title ++ "]]", "",
      "#align(center)[", grid, "]", "",
      "#align(center)[#text(9pt, style: \"italic\")[" ++ d.meaning ++ "]]", "" ]

/-! ## Book examples -/

private def nd (l : String) (x y : Int) : Node := { label := l, x := x, y := y }
private def pnc (x y : Int) : Node := { label := "div", x := x, y := y }   -- puncture mark ÷
private def eg (x1 y1 x2 y2 : Int) (l : String) : Edge :=
  { x1 := x1, y1 := y1, x2 := x2, y2 := y2, label := l }
private def egc (x1 y1 x2 y2 : Int) (l : String) : Edge :=     -- cover (hollow head ↠)
  { x1 := x1, y1 := y1, x2 := x2, y2 := y2, label := l, mark := "->>" }
private def egp (x1 y1 x2 y2 : Int) (l : String) (sh : Int) : Edge :=   -- parallel-pair member
  { x1 := x1, y1 := y1, x2 := x2, y2 := y2, label := l, shift := sh,
    side := if sh > 0 then "left" else "right" }   -- + above, − below
private def egm (x1 y1 x2 y2 : Int) (l : String) : Edge :=    -- monic (tailed ↣)
  { x1 := x1, y1 := y1, x2 := x2, y2 := y2, label := l, mark := ">->" }
/-- The §1.39 JOINT-COVER arc: a headless curve bracketing the middles of the two family
    arrows, marking `{f₁,f₂}` as *jointly* covering (NOT each fᵢ a cover).  Coords are the
    arrow midpoints (layouts below are scaled ×2 so midpoints land on integer grid lines). -/
private def arc (x1 y1 x2 y2 : Int) (bendDeg : Int) : Edge :=
  { x1 := x1, y1 := y1, x2 := x2, y2 := y2, label := "", mark := "-", bend := bendDeg }
private def pan (ns : List Node) (es : List Edge) : Item := .panel { nodes := ns, edges := es }

/-- §1.39 LEFT-INVERTIBLE:  [A→B]  ∣∃∣  [B↓A (g), A→B (f), B→B diag (1)]. -/
def leftInvertible : QDiagram :=
  { title := "Left-invertible (§1.39)"
    meaning := "∃ the back-arrow making the triangle commute (g; f = 1)"
    items :=
      [ pan [nd "A" 0 1, nd "B" 1 1] [eg 0 1 1 1 "f"],
        .bar "exists",
        pan [nd "B" 0 0, nd "A" 0 1, nd "B" 1 1]
            [eg 0 0 0 1 "g", eg 0 1 1 1 "f", eg 0 0 1 1 "1"] ] }

/-- §1.41 SINGLE MONIC:  [A→B (m)]  ∣∀∣  [T→B (w), A→B (m)]  ∣!∣  [T↓A (u), T→B (w), A→B (m)]. -/
def monic : QDiagram :=
  { title := "A single morphism is monic (§1.41)"
    meaning := "∀ w factoring through m, ! (at most one) lift u with u; m = w"
    items :=
      [ pan [nd "A" 0 1, nd "B" 1 1] [eg 0 1 1 1 "m"],
        .bar "forall",
        pan [nd "T" 0 0, nd "A" 0 1, nd "B" 1 1] [eg 0 0 1 1 "w", eg 0 1 1 1 "m"],
        .bar "!",
        pan [nd "T" 0 0, nd "A" 0 1, nd "B" 1 1]
            [eg 0 0 0 1 "u", eg 0 0 1 1 "w", eg 0 1 1 1 "m"] ] }

/-- §1.428 EQUALIZER diagram:  [E→A⇉B (÷)]  ∣∀∣  [+T→A (z)]  ∣∃!∣  [+T→E diag (u)].
    `÷` is the puncture mark on the parallel pair x,y : A⇉B (removes the x=y equation). -/
def equalizer : QDiagram :=
  let p0 : List Edge := [eg 0 2 2 2 "", egp 2 2 4 2 "x" 8, egp 2 2 4 2 "y" (-8)]
  { title := "An EQUALIZER diagram (§1.428)"
    meaning := "∀ z with z x = z y, ∃! u : T→E with u; (E→A) = z"
    items :=
      [ pan [nd "E" 0 2, nd "A" 2 2, nd "B" 4 2, pnc 3 2] p0,
        .bar "forall",
        pan [nd "E" 0 2, nd "A" 2 2, nd "B" 4 2, nd "T" 2 0, pnc 3 2]
            (eg 2 0 2 2 "z" :: p0),
        .bar "exists!",
        pan [nd "E" 0 2, nd "A" 2 2, nd "B" 4 2, nd "T" 2 0, pnc 3 2]
            (eg 2 0 0 2 "u" :: eg 2 0 2 2 "z" :: p0) ] }

/-- §1.524 PROJECTIVE:  [P]  ∣∀∣  [P↓B, A↠B (cover)]  ∣∃∣  [+P→A diag (lift)]. -/
def projective : QDiagram :=
  let p1 : List Edge := [egc 0 2 2 2 "", eg 2 0 2 2 ""]
  { title := "P is PROJECTIVE (§1.524)"
    meaning := "∀ cover A↠B and P→B, ∃ a lift P→A"
    items :=
      [ pan [nd "P" 1 0] [],
        .bar "forall",
        pan [nd "P" 2 0, nd "A" 0 2, nd "B" 2 2] p1,
        .bar "exists",
        pan [nd "P" 2 0, nd "A" 0 2, nd "B" 2 2] (eg 2 0 0 2 "" :: p1) ] }

/-! ## A formal Q-sequence SENTENCE, and the layout COMPILER

  A diagram must be DERIVED from the logic, not hand-placed from a picture.  A `Sentence` is
  a telescope of quantifier `Step`s; each step binds new objects and typed arrows.  `compile`
  computes the picture: objects are LAYERED by a longest-path over the arrows (target below
  source; back-arrows of a cycle, e.g. an inverse, are drawn but excluded from layering), the
  x-coordinate is the barycentre of an object's parents, and quantifier bars separate the
  cumulative panels.  Predicates set style: `monic` ↣ tailed, `jointCover` one arc across the
  family (so NO single arrow is itself a cover). -/

/-- A typed arrow `name : src ⟶ tgt`.  `name` is an id (referenced by predicates); `disp` is
    the optional label drawn on the arrow ("" = unlabelled, as Freyd draws §1.611). -/
structure SArr where
  name : String
  src  : String
  tgt  : String
  disp : String := ""
  deriving Inhabited

/-- A predicate over the declared arrows — drives STYLE only, introduces nothing. -/
inductive SPred
  | monic      (arr : String)        -- draw `arr` tailed ↣
  | jointCover (arrs : List String)  -- `arrs` JOINTLY cover their common target (one arc)

/-- One quantifier step of the telescope: a quantifier binding new objects and arrows. -/
structure SStep where
  quant : String                     -- "exists" | "forall" | "exists!" | "!"
  objs  : List String := []
  arrs  : List SArr := []
  deriving Inhabited

/-- A Q-sequence sentence.  `disp` overrides an object id's drawn label (e.g. `"T1" ↦ "1"`
    for the terminator).  A step whose `quant` is `""` is a leading CONTEXT panel (the "given"
    data) drawn with no bar. -/
structure Sentence where
  title   : String
  meaning : String
  steps   : List SStep
  preds   : List SPred := []
  disp    : List (String × String) := []

private def Sentence.objsAll  (s : Sentence) : List String := s.steps.flatMap (·.objs)
private def Sentence.arrsAll  (s : Sentence) : List SArr   := s.steps.flatMap (·.arrs)

/-- Does `a` reach `b` along `es` (fuel-bounded, so structurally recursive — no `partial`)? -/
private def reachesF : Nat → List SArr → String → String → Bool
  | 0,      _,  _, _ => false
  | fuel+1, es, a, b =>
      a == b || (es.filter (fun e => e.src == a)).any (fun e => reachesF fuel es e.tgt b)

/-- The acyclic subset of arrows used for LAYERING: keep an arrow unless it would close a
    cycle (its target already reaches its source).  Drops self-loops and cycle back-edges. -/
private def Sentence.layoutEdges (s : Sentence) : List SArr :=
  let n := s.objsAll.length + 1
  s.arrsAll.foldl (fun kept a =>
    if a.src == a.tgt || reachesF n kept a.tgt a.src then kept else kept ++ [a]) []

private def iterate {α} : Nat → (α → α) → α → α
  | 0,    _, x => x
  | n+1,  f, x => iterate n f (f x)

/-- Layer of each object = longest path of layout-edges ending at it (sources on top). -/
private def Sentence.layerMap (s : Sentence) : List (String × Int) :=
  let objs := s.objsAll
  let le   := s.layoutEdges
  let step (cur : List (String × Int)) : List (String × Int) :=
    objs.map (fun o =>
      (o, (le.filter (fun e => e.tgt == o)).foldl
            (fun m e => max m (((cur.lookup e.src).getD 0) + 1)) (0 : Int)))
  iterate objs.length step (objs.map (fun o => (o, (0 : Int))))

/-- x-coordinate of each object: barycentre of its (already-placed, higher) parents; roots
    are spread left-to-right within their layer.  Processed layer by layer, top down. -/
private def Sentence.xMap (s : Sentence) (lm : List (String × Int)) : List (String × Int) :=
  let objs := s.objsAll
  let le   := s.layoutEdges
  let maxL := lm.foldl (fun m p => max m p.2) 0
  let place (acc : List (String × Int)) (layer : Int) : List (String × Int) :=
    (objs.filter (fun o => (lm.lookup o).getD 0 == layer)).foldl (fun acc o =>
      let parents := (le.filter (fun e => e.tgt == o)).filterMap (fun e => acc.lookup e.src)
      let here    := acc.filter (fun p => (lm.lookup p.1).getD 0 == layer) |>.map (·.2)
      let want    := if parents.isEmpty then 2 * Int.ofNat here.length
                     else parents.foldl (· + ·) 0 / Int.ofNat parents.length
      -- resolve collisions: if `want` is taken in this layer, slide right by 2
      let x := iterate (here.length + 1) (fun c => if here.contains c then c + 2 else c) want
      acc ++ [(o, x)]) acc
  (List.range (maxL.toNat + 1)).foldl (fun acc i => place acc (Int.ofNat i)) []

/-- Compile a sentence to a `QDiagram`.  Coordinates are doubled so every arrow midpoint (the
    arc endpoints) lands on an integer grid line. -/
def compile (s : Sentence) : QDiagram :=
  let lm  := s.layerMap
  let xs  := s.xMap lm
  let pos : String → Int × Int := fun o =>
    (2 * (xs.lookup o).getD 0, 2 * (lm.lookup o).getD 0)
  let allA := s.arrsAll
  let mono := s.preds.filterMap (fun | .monic n => some n | _ => none)
  let covs := s.preds.filterMap (fun | .jointCover ns => some ns | _ => none)
  let mid  := fun (a : SArr) =>
    let (sx, sy) := pos a.src; let (tx, ty) := pos a.tgt; ((sx + tx) / 2, (sy + ty) / 2)
  let label : String → String := fun o => (s.disp.lookup o).getD o
  let mkPanel (i : Nat) : Item :=
    let pre   := s.steps.take (i + 1)
    let pObjs := pre.flatMap (·.objs)
    let pArrs := pre.flatMap (·.arrs)
    let nodes := pObjs.map (fun o => let (x, y) := pos o; nd (label o) x y)
    let edges := pArrs.map (fun a =>
      let (sx, sy) := pos a.src; let (tx, ty) := pos a.tgt
      let grp := allA.filter (fun b => (b.src == a.src && b.tgt == a.tgt)
                                    || (b.src == a.tgt && b.tgt == a.src))  -- parallel partners
      let sh  := if grp.length ≥ 2 then (if grp.findIdx (·.name == a.name) == 0 then 6 else -6) else 0
      -- an edge spanning ≥2 layers is bent to route AROUND the intermediate vertices
      let dl  := ((lm.lookup a.tgt).getD 0) - ((lm.lookup a.src).getD 0)
      let bnd := if grp.length ≥ 2 || (dl < 2 && dl > -2) then 0
                 else if tx < sx then -22 else 22
      { x1 := sx, y1 := sy, x2 := tx, y2 := ty, label := a.disp,
        mark := if mono.contains a.name then ">->" else "->", shift := sh,
        side := if sh > 0 then "left" else if sh < 0 then "right" else "", bend := bnd })
    let ys   := nodes.map (·.y)
    let midY := (ys.foldl (fun a b => if a < b then a else b) (ys.headD 0)
                 + ys.foldl (fun a b => if a < b then b else a) (ys.headD 0)) / 2
    let arcs := covs.filterMap (fun ns =>
      if ns.all (fun nm => pArrs.any (·.name == nm)) then
        match ns.filterMap (fun nm => allA.find? (·.name == nm)) with
        | a1 :: a2 :: _ =>
          let (mx1, my1) := mid a1; let (mx2, my2) := mid a2
          let bend := if my1 < midY then 35 else -35    -- bulge away from the diagram body
          some (if mx1 ≤ mx2 then arc mx1 my1 mx2 my2 bend else arc mx2 my2 mx1 my1 bend)
        | _ => none
      else none)
    pan nodes (edges ++ arcs)
  { title := s.title, meaning := s.meaning,
    items := (List.range s.steps.length).flatMap (fun i =>
      let q := s.steps[i]!.quant
      if q == "" then [mkPanel i] else [Item.bar q, mkPanel i]) }

/-! ## §1.611  The three sentences DEFINING a pre-logos (Cartesian + images + …)

  Each is a Horn/Q-sequence sentence; `compile` derives the book's p. 99 picture from it.
  They are exactly the `bottom`, `union`, and `invImage_preserves_union/_bottom` fields of
  `PreLogos` (S1_60). -/

/-- §1.611 (i) EMPTY UNION / minimal subobject:  ∃ A, ∀ (f : B → A), ∃ (g : A → B) inverse to
    f — every morphism to A is an isomorphism, so A has no proper subobjects (the empty join). -/
def sEmptyUnion : Sentence :=
  { title := "Empty union: the minimal subobject (§1.611)"
    meaning := "∃ A, ∀ (f : B → A), ∃ (g : A → B) inverse to f — every map to A is iso (A = the least subobject)"
    steps :=
      [ { quant := "exists", objs := ["A"] },
        { quant := "forall", objs := ["B"], arrs := [{ name := "f", src := "B", tgt := "A" }] },
        { quant := "exists",                arrs := [{ name := "g", src := "A", tgt := "B" }] } ] }

/-- §1.611 (ii) BINARY UNION:  ∀ subobjects B₁, B₂ ↣ B, ∃ their union U with B₁, B₂ jointly
    covering U (so neither alone covers it) and U ↣ B monic. -/
def sBinaryUnion : Sentence :=
  { title := "Binary union of two subobjects (§1.611)"
    meaning := "∀ subobjects B₁, B₂ ↣ B, ∃ U = B₁∪B₂ with B₁, B₂ JOINTLY covering U and U ↣ B monic"
    steps :=
      [ { quant := "forall", objs := ["B_1", "B_2", "B"],
          arrs := [{ name := "m1", src := "B_1", tgt := "B" }, { name := "m2", src := "B_2", tgt := "B" }] },
        { quant := "exists", objs := ["U"],
          arrs := [{ name := "c1", src := "B_1", tgt := "U" }, { name := "c2", src := "B_2", tgt := "U" },
                   { name := "u", src := "U", tgt := "B" }] } ]
    preds := [ .monic "m1", .monic "m2", .monic "u", .jointCover ["c1", "c2"] ] }

/-- §1.611 (iii) COVER-TRANSFER:  ∀ a cover {B₁, B₂} of B (jointly) and a map A → B, ∃
    pullbacks {A₁, A₂} jointly covering A.  Pullbacks transfer finite covers. -/
def sCoverTransfer : Sentence :=
  { title := "Pullbacks transfer finite covers (§1.611)"
    meaning := "∀ a cover {B₁, B₂} of B (jointly) and a map A → B, ∃ pullbacks {A₁, A₂} jointly covering A"
    steps :=
      [ { quant := "forall", objs := ["A", "B_1", "B", "B_2"],
          arrs := [{ name := "a", src := "A", tgt := "B" }, { name := "p1", src := "B_1", tgt := "B" },
                   { name := "p2", src := "B_2", tgt := "B" }] },
        { quant := "exists", objs := ["A_1", "A_2"],
          arrs := [{ name := "q1", src := "A_1", tgt := "A" }, { name := "q2", src := "A_2", tgt := "A" },
                   { name := "r1", src := "A_1", tgt := "B_1" }, { name := "r2", src := "A_2", tgt := "B_2" }] } ]
    preds := [ .jointCover ["p1", "p2"], .jointCover ["q1", "q2"] ] }

/-! ## More book Q-sequences as sentences.  Universal properties use a `∃` step for the
  mediating map then a `!` step for its uniqueness — never a combined `∃!` (Freyd's
  at-most-one bar `!`).  A leading `""` step is the "given" context (drawn with no bar). -/

/-- §1.39 LEFT-INVERTIBLE:  given f : A → B, ∃ g : B → A with f g = 1_A. -/
def sLeftInvertible : Sentence :=
  { title := "Left-invertible (§1.39)"
    meaning := "given f : A → B, ∃ g : B → A with f g = 1_A"
    steps :=
      [ { quant := "", objs := ["A", "B"], arrs := [{ name := "f", src := "A", tgt := "B", disp := "f" }] },
        { quant := "exists", arrs := [{ name := "g", src := "B", tgt := "A", disp := "g" }] } ] }

/-- §1.41 SINGLE MONIC:  given m : A → B, ∀ w : T → B there is at most one (`!`) u : T → A
    with u m = w.  (Uniqueness of the lift — no existence claimed — defines monic.) -/
def sMonic : Sentence :=
  { title := "A single morphism is monic (§1.41)"
    meaning := "given m : A → B, ∀ w : T → B, ! (at most one) u : T → A with u m = w"
    steps :=
      [ { quant := "", objs := ["A", "B"], arrs := [{ name := "m", src := "A", tgt := "B", disp := "m" }] },
        { quant := "forall", objs := ["T"], arrs := [{ name := "w", src := "T", tgt := "B", disp := "w" }] },
        { quant := "!", arrs := [{ name := "u", src := "T", tgt := "A", disp := "u" }] } ]
    preds := [ .monic "m" ] }

/-- §1.412 SUB-TERMINATOR:  A is a subterminator — ∀ X there is at most one (`!`) map X → A. -/
def sSubterminator : Sentence :=
  { title := "A is a sub-terminator (§1.412)"
    meaning := "∀ X, ! (at most one) map X → A"
    steps :=
      [ { quant := "", objs := ["A"] },
        { quant := "forall", objs := ["X"] },
        { quant := "!", arrs := [{ name := "h", src := "X", tgt := "A", disp := "h" }] } ] }

/-- §1.421 TERMINATOR (the category HAS one):  ∃ 1, ∀ A, ∃ (A → 1), and it is unique (`!`). -/
def sTerminator : Sentence :=
  { title := "The category has a terminator (§1.421)"
    meaning := "∃ 1 such that ∀ A, ∃ (A → 1) which is unique (!)"
    steps :=
      [ { quant := "exists", objs := ["T1"] },
        { quant := "forall", objs := ["A"] },
        { quant := "exists", arrs := [{ name := "t", src := "A", tgt := "T1", disp := "" }] },
        { quant := "!" } ]
    disp := [("T1", "1")] }

/-- §1.423 BINARY PRODUCT (the category HAS them):  ∀ A, B, ∃ P with projections p, q, such
    that ∀ (f : T → A, g : T → B) ∃ a mediating m : T → P (p m = f, q m = g), unique (`!`). -/
def sBinaryProduct : Sentence :=
  { title := "The category has binary products (§1.423)"
    meaning := "∀ A, B, ∃ P with p : P→A, q : P→B such that ∀ (f : T→A, g : T→B), ∃ unique m : T→P with p m = f, q m = g"
    steps :=
      [ { quant := "forall", objs := ["A", "B"] },
        { quant := "exists", objs := ["P"],
          arrs := [{ name := "p", src := "P", tgt := "A", disp := "p" }, { name := "q", src := "P", tgt := "B", disp := "q" }] },
        { quant := "forall", objs := ["T"],
          arrs := [{ name := "f", src := "T", tgt := "A", disp := "f" }, { name := "g", src := "T", tgt := "B", disp := "g" }] },
        { quant := "exists", arrs := [{ name := "m", src := "T", tgt := "P", disp := "m" }] },
        { quant := "!" } ] }

/-- §1.428 EQUALIZER (the category HAS them):  ∀ parallel f, g : A → B, ∃ e : E → A with
    e f = e g, such that ∀ (z : Z → A with z f = z g) ∃ a unique (`!`) m : Z → E with m e = z. -/
def sEqualizer : Sentence :=
  { title := "The category has equalizers (§1.428)"
    meaning := "∀ parallel f, g : A→B, ∃ e : E→A (e f = e g) such that ∀ (z : Z→A, z f = z g), ∃ unique m : Z→E with m e = z"
    steps :=
      [ { quant := "forall", objs := ["A", "B"],
          arrs := [{ name := "f", src := "A", tgt := "B", disp := "f" }, { name := "g", src := "A", tgt := "B", disp := "g" }] },
        { quant := "exists", objs := ["E"], arrs := [{ name := "e", src := "E", tgt := "A", disp := "e" }] },
        { quant := "forall", objs := ["Z"], arrs := [{ name := "z", src := "Z", tgt := "A", disp := "z" }] },
        { quant := "exists", arrs := [{ name := "m", src := "Z", tgt := "E", disp := "m" }] },
        { quant := "!" } ] }

/-- §1.431 PULLBACK (the category HAS them):  ∀ a cospan A → C ← B, ∃ P with p : P→A, q : P→B
    (a p = b q), such that ∀ (x : T→A, y : T→B cone) ∃ a unique (`!`) m : T→P. -/
def sPullback : Sentence :=
  { title := "The category has pullbacks (§1.431)"
    meaning := "∀ a cospan A→C←B, ∃ P with p:P→A, q:P→B (a p = b q) such that ∀ a cone (x:T→A, y:T→B), ∃ unique m : T→P"
    steps :=
      [ { quant := "forall", objs := ["A", "C", "B"],
          arrs := [{ name := "a", src := "A", tgt := "C", disp := "a" }, { name := "b", src := "B", tgt := "C", disp := "b" }] },
        { quant := "exists", objs := ["P"],
          arrs := [{ name := "p", src := "P", tgt := "A", disp := "p" }, { name := "q", src := "P", tgt := "B", disp := "q" }] },
        { quant := "forall", objs := ["T"],
          arrs := [{ name := "x", src := "T", tgt := "A", disp := "x" }, { name := "y", src := "T", tgt := "B", disp := "y" }] },
        { quant := "exists", arrs := [{ name := "m", src := "T", tgt := "P", disp := "m" }] },
        { quant := "!" } ] }

/-- Every §1.611 + book Q-sequence, as a (name, sentence) pair compiled by `compile`. -/
def bookSentences : List (String × Sentence) :=
  [ ("leftInvertible_139", sLeftInvertible), ("monic_141", sMonic),
    ("subterminator_1412", sSubterminator), ("terminator_1421", sTerminator),
    ("binaryProduct_1423", sBinaryProduct), ("equalizer_1428", sEqualizer),
    ("pullback_1431", sPullback),
    ("emptyUnion_1611", sEmptyUnion), ("binaryUnion_1611", sBinaryUnion),
    ("coverTransfer_1611", sCoverTransfer) ]

def main : IO Unit := do
  IO.FS.createDirAll "Fredy/tool/out"
  -- every diagram is COMPILED from its formal sentence (layout derived, not hand-placed)
  for (nm, s) in bookSentences do
    IO.FS.writeFile ("Fredy/tool/out/" ++ nm ++ ".typ") (render (compile s))
    IO.println ("wrote Fredy/tool/out/" ++ nm ++ ".typ")

end QSeqRender

def main : IO Unit := QSeqRender.main
