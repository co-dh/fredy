/-
  Render a §1.39 Q-sequence in Freyd's notation, IN LEAN.

  Freyd draws a Q-sequence as a left-to-right sequence of growing finitely-presented
  diagrams (PANELS) separated by tall VERTICAL BARS, each bar carrying its quantifier
  (∀ / ∃ / !) ON TOP (book §1.39/§1.41, §1.395).  This Lean program builds the panels and
  bars and emits Typst+fletcher; `typst` compiles the picture.

  Matches the book: left-invertible (§1.39) = [A→B] ∣∃∣ [triangle with g, 1];
  single monic (§1.41) = [A→B] ∣∀∣ [w, m] ∣!∣ [u, w, m].

  Run:  lake env lean --run Fredy/QSeqRender.lean
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
  mark  : String := "->"   -- "->" plain, ">->" monic, "->>" cover
  shift : Int := 0         -- pt offset, for parallel pairs
  side  : String := ""     -- label-side: "left" (above) / "right" (below)

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
  "edge((" ++ I e.x1 ++ ", " ++ I e.y1 ++ "), (" ++ I e.x2 ++ ", " ++ I e.y2 ++ "), "
    ++ lbl ++ "\"" ++ e.mark ++ "\"" ++ sh ++ sd ++ ")"

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

def main : IO Unit := do
  IO.FS.createDirAll "tools/out"
  for (nm, d) in [("li_lean", leftInvertible), ("monic_lean", monic),
                  ("equalizer_lean", equalizer), ("projective_lean", projective)] do
    IO.FS.writeFile ("tools/out/" ++ nm ++ ".typ") (render d)
    IO.println ("wrote tools/out/" ++ nm ++ ".typ")

end QSeqRender

def main : IO Unit := QSeqRender.main
