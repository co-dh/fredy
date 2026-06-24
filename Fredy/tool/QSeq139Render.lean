/-
  A GENERIC renderer for §1.395 Q-sequences (`QSeq139` from `QSeq139.lean`).

  `render : QSeq139 → String` emits a Typst+fletcher picture: a left-to-right run of CUMULATIVE
  panels (objects never move — §1.391) separated by tall vertical bars carrying the bare
  quantifier `∀`/`∃` (§1.395: the symbol alone sits on the bar; the bound arrows appear in the
  panel after it).  Layout is DERIVED from the arrows (objects layered by longest path, sources
  on top).  The three book-faithful drawing rules the user asked for:
    • a `parallel` bundle (e.g. a, b : W ⇉ T) is drawn as STRAIGHT arrows offset by `shift:`
      (fletcher), exactly like the §1.41 monic-pair picture — never curved;
    • a `puncture`d equation (an `a = b` not imposed) is marked with a `+` at the bundle's
      midpoint (Freyd's puncture mark), and DISAPPEARS in the first panel that imposes it;
    • a long edge (spanning ≥ 2 layers) is bent around the intervening vertices.

  Run:  lake env lean --run Fredy/tool/QSeq139Render.lean   (writes Fredy/tool/out/<title>.typ)
-/

import Fredy.tool.QSeq139

namespace Freyd
namespace QSeq139
namespace Render

/-! ## Layout (longest-path layering, derived from the full arrow set) -/

private def reaches : Nat → List Arr → String → String → Bool
  | 0,      _,  _, _ => false
  | fuel+1, es, a, b => a == b || (es.filter (·.src == a)).any (fun e => reaches fuel es e.tgt b)

/-- Acyclic layout edges: drop self-loops and back-edges that would close a cycle. -/
private def layoutEdges (arrs : List Arr) : List Arr :=
  let n := arrs.length + 1
  arrs.foldl (fun kept a =>
    if a.src == a.tgt || reaches n kept a.tgt a.src then kept else kept ++ [a]) []

private def iter {α} : Nat → (α → α) → α → α
  | 0,    _, x => x
  | n+1,  f, x => iter n f (f x)

/-- Layer of each object = longest path of layout-edges ending at it (sources on top). -/
private def layerMap (objs : List String) (le : List Arr) : List (String × Int) :=
  let step (cur : List (String × Int)) : List (String × Int) :=
    objs.map (fun o => (o, (le.filter (·.tgt == o)).foldl
      (fun m e => max m (((cur.lookup e.src).getD 0) + 1)) (0 : Int)))
  iter objs.length step (objs.map (fun o => (o, (0 : Int))))

/-- x of each object = 4 × its index among objects sharing its layer (left-to-right by first
    appearance).  Coordinates are doubled in y so every arrow midpoint lands on a grid line. -/
private def positions (objs : List String) (arrs : List Arr) : List (String × (Int × Int)) :=
  let lm := layerMap objs (layoutEdges arrs)
  objs.map (fun o =>
    let ly := (lm.lookup o).getD 0
    let peers := objs.filter (fun p => (lm.lookup p).getD 0 == ly)
    let ix := (Int.ofNat (peers.findIdx (· == o)))
    (o, (4 * ix, 2 * ly)))

private def layerOf (objs : List String) (arrs : List Arr) (o : String) : Int :=
  ((layerMap objs (layoutEdges arrs)).lookup o).getD 0

/-! ## Typst emission -/

private def I (n : Int) : String := toString n

/-- Drawn label for an object id (e.g. the product reads `A × B`). -/
private def disp (o : String) : String :=
  if o == "AxB" then "A times B" else o

private def nodeStr (o : String) (p : Int × Int) : String :=
  "node((" ++ I p.1 ++ ", " ++ I p.2 ++ "), $" ++ disp o ++ "$)"

/-- Shift (pt) for an arrow inside a straight parallel bundle: spread members symmetrically. -/
private def shiftOf (bundles : List (List String)) (name : String) : Int :=
  match bundles.find? (·.contains name) with
  | none => 0
  | some grp => (6 : Int) - 12 * (Int.ofNat (grp.findIdx (· == name)))   -- 2 members → +6, −6

private def edgeStr (pos : List (String × (Int × Int))) (objs : List String) (arrs : List Arr)
    (bundles : List (List String)) (a : Arr) : String :=
  let s := (pos.lookup a.src).getD (0, 0)
  let t := (pos.lookup a.tgt).getD (0, 0)
  let span := (layerOf objs arrs a.tgt - layerOf objs arrs a.src).natAbs
  let sh := shiftOf bundles a.name
  let bend := if sh != 0 then "" else if span ≥ 2 then ", bend: 24deg" else ""
  let shift := if sh == 0 then "" else ", shift: " ++ I sh ++ "pt"
  let side := if sh == 0 then "" else if sh > 0 then ", label-side: left" else ", label-side: right"
  "edge((" ++ I s.1 ++ ", " ++ I s.2 ++ "), (" ++ I t.1 ++ ", " ++ I t.2 ++ "), $"
    ++ a.name ++ "$, \"->\"" ++ shift ++ side ++ bend ++ ")"

/-- The `+` puncture mark at the midpoint of a punctured `a = b` bundle (uses arrow `lhs[0]`). -/
private def punctureStr (pos : List (String × (Int × Int))) (arrs : List Arr) (e : Eqn) : String :=
  match e.lhs.head?.bind (fun nm => arrs.find? (·.name == nm)) with
  | none => ""
  | some a =>
    let s := (pos.lookup a.src).getD (0, 0)
    let t := (pos.lookup a.tgt).getD (0, 0)
    "node(((" ++ I s.1 ++ "+" ++ I t.1 ++ ")/2, (" ++ I s.2 ++ "+" ++ I t.2
      ++ ")/2), text(13pt)[$plus$])"

/-! ## Cumulative panels -/

private def Panel.merge (p q : Panel) : Panel :=
  { objs := p.objs ++ q.objs, arrs := p.arrs ++ q.arrs,
    impose := p.impose ++ q.impose, puncture := p.puncture ++ q.puncture,
    parallel := p.parallel ++ q.parallel }

/-- The `i`-th cumulative panel: root plus the panels of the first `i` bars. -/
private def cumulative (s : QSeq139) (i : Nat) : Panel :=
  (s.bars.take i).foldl (fun acc bp => Panel.merge acc bp.2) s.root

/-- Equations still PUNCTURED in cumulative panel `i` (punctured by some earlier bar, not yet
    imposed) — these get a `+`; once a later bar imposes them the mark is gone. -/
private def activePunctures (p : Panel) : List Eqn :=
  p.puncture.filter (fun e => ¬ p.impose.contains e)

private def diagramStr (s : QSeq139) (allObjs : List String) (allArrs : List Arr) (i : Nat) : String :=
  let p := cumulative s i
  let pos := positions allObjs allArrs
  let nodes := p.objs.map (fun o => nodeStr o ((pos.lookup o).getD (0, 0)))
  let edges := p.arrs.map (edgeStr pos allObjs allArrs p.parallel)
  let puncs := (activePunctures p).map (punctureStr pos p.arrs)
  let body := String.intercalate ", " (nodes ++ edges ++ puncs.filter (· != ""))
  "diagram(spacing: (12mm, 11mm), node-stroke: none, " ++ body ++ ")"

private def barStr : Bar → String
  | .all => "$forall$"
  | .ex  => "$exists$"

private def barBox (b : Bar) : String :=
  "box(height: 40mm)[#stack(dir: ttb, spacing: 3mm, align(center)[#text(13pt)[" ++ barStr b
    ++ "]], line(length: 32mm, angle: 90deg))]"

/-- Render a whole §1.395 Q-sequence to a standalone Typst document. -/
def render (s : QSeq139) : String :=
  let allObjs := (cumulative s s.bars.length).objs.eraseDups
  let allArrs := (cumulative s s.bars.length).arrs
  -- columns: panel0, bar0, panel1, bar1, panel2, …
  let cols := (List.range (s.bars.length + 1)).foldl (fun acc i =>
    let panel := diagramStr s allObjs allArrs i
    match s.bars[i]? with
    | some (b, _) => acc ++ [panel, barBox b]
    | none        => acc ++ [panel]) []
  let ncol := cols.length
  let grid := "#grid(columns: " ++ toString ncol ++ ", align: horizon, column-gutter: 6mm,\n  "
    ++ String.intercalate ",\n  " cols ++ "\n)"
  "#import \"@preview/fletcher:0.5.8\" as fletcher: diagram, node, edge\n"
    ++ "#set page(width: auto, height: auto, margin: 9mm)\n"
    ++ "#set text(size: 11pt, font: \"New Computer Modern\")\n\n"
    ++ "#align(center)[#text(13pt, weight: \"bold\")[" ++ s.title ++ "]]\n\n"
    ++ "#align(center)[\n" ++ grid ++ "\n]\n"

def main : IO Unit := do
  IO.FS.createDirAll "Fredy/tool/out"
  let s := monicPairQSeq
  IO.FS.writeFile "Fredy/tool/out/qseq139_monicPair.typ" (render s)
  IO.println "wrote Fredy/tool/out/qseq139_monicPair.typ"

end Render
end QSeq139
end Freyd

def main : IO Unit := Freyd.QSeq139.Render.main
