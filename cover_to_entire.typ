#import "@preview/fletcher:0.5.8" as fletcher: node, edge

#set page(width: auto, height: auto, margin: 1.5cm)
#set text(size: 11pt)
#set par(leading: 0.5em, justify: false)
#set align(center)

// ── color palette ───────────────────────────────────────────────────
#let cT  = rgb("ffe0b2")  // orange  — T
#let cP  = rgb("c8e6c9")  // green   — pullback vertex
#let cI  = rgb("f8bbd0")  // magenta — image
#let cA  = rgb("e1bee7")  // purple  — A
#let cB  = rgb("bbdefb")  // blue    — B
#let cAA = rgb("b2dfdb")  // teal    — A×A
#let cJ  = rgb("d7ccc8")  // brown   — J
#let cl  = rgb("43a047")  // l/r green
#let cy  = rgb("1565c0")  // y blue
#let cx  = rgb("e65100")  // x orange
#let cj  = rgb("f9a825")  // j gold
#let cwit = rgb("1a6fd4") // witness blue

// ── reusable diagram fragments ──────────────────────────────────────

// Pullback corner: two segments from points s-of-the-way along
// the projection legs, meeting at the parallelogram point.
#let pb-corner(p, l, r, s: 0.3, stroke: 0.9pt + rgb("333")) = {
  let v1 = (l.at(0) - p.at(0), l.at(1) - p.at(1))
  let v2 = (r.at(0) - p.at(0), r.at(1) - p.at(1))
  let p1 = (p.at(0) + s * v1.at(0), p.at(1) + s * v1.at(1))
  let p2 = (p.at(0) + s * v2.at(0), p.at(1) + s * v2.at(1))
  let m  = (p.at(0) + s * (v1.at(0) + v2.at(0)), p.at(1) + s * (v1.at(1) + v2.at(1)))
  (edge(p1, m, "-", stroke: stroke), edge(p2, m, "-", stroke: stroke))
}

// Pullback square: p —l→ L —f→ C ←g— R ←r— p.
#let pullback-sq(p-pos: (1,1), l-pos: (0,2), r-pos: (2,2), c-pos: (1,3),
                  f: [$f$], g: [$g$], l: [$p_1$], r: [$p_2$],
                  p-name: [$P$], l-name: [$L$], r-name: [$R$], c-name: [$C$],
                  p-fill: none, l-fill: none, r-fill: none, c-fill: none,
                  l-stroke: black, r-stroke: black,
                  f-stroke: black, g-stroke: black) = {
  (
    pb-corner(p-pos, l-pos, r-pos),
    node(p-pos, p-name, fill: p-fill),
    node(l-pos, l-name, fill: l-fill),
    node(r-pos, r-name, fill: r-fill),
    node(c-pos, c-name, fill: c-fill),
    edge(p-pos, l-pos, "->", label: l, stroke: l-stroke),
    edge(p-pos, r-pos, "->", label: r, stroke: r-stroke),
    edge(l-pos, c-pos, "->", label: f, stroke: f-stroke),
    edge(r-pos, c-pos, "->", label: g, stroke: g-stroke),
  )
}

#let cover-edge(from, to, label: none, stroke: black) = {
  edge(from, to, "->>", label: label, stroke: stroke)
}
#let monic-edge(from, to, label: none, stroke: black) = {
  edge(from, to, ">->", label: label, stroke: stroke)
}
#let iso-edge(from, to, label: none) = {
  edge(from, to, "<->", label: label)
}
#let lift-edge(from, to, label: none) = {
  edge(from, to, "->", dash: "dashed", label: label)
}
#let witness-edge(from, to, label: none) = {
  edge(from, to, "->", dash: "dashed", label: label, stroke: cwit + 1.2pt)
}

// ── document ────────────────────────────────────────────────────────

#text(size: 13pt, weight: "bold")[§1.564  x is a cover ⇒ R entire — tabulated_is_entire_iff_left_cover]

#v(0.8em)

// ============ Panel 0: construction of d ============
#text(size: 9pt, fill: gray)[Panel 0 — pullback of (y,y): pair ⟨1_T,1_T⟩ over y induces unique lift d:T→P with d≫l=1, d≫r=1.]

#figure(
  fletcher.diagram(
    spacing: 3em,
    node((1,-1), [$T$], fill: cT),
    pullback-sq(
      p-pos: (1,0), l-pos: (0,1), r-pos: (2,1), c-pos: (1,2),
      f: [$y$], g: [$y$], l: [$l$], r: [$r$],
      l-name: [$T$], r-name: [$T$], c-name: [$B$],
      p-fill: cP, l-fill: cT, r-fill: cT, c-fill: cB,
      l-stroke: cl, r-stroke: cl, f-stroke: cy, g-stroke: cy,
    ),
    lift-edge((1,-1), (1,0), label: [$d$]),
    edge((1,-1), (0,1), "->", label: [$1$], stroke: gray + 1pt),
    edge((1,-1), (2,1), "->", label: [$1$], stroke: gray + 1pt),
  ),
  caption: [hd₁: d≫l = 1_T,  hd₂: d≫r = 1_T,  pullback condition: l≫y = r≫y],
)

#v(1em)

// ============ Panel 1: composition RR° ============
#text(size: 9pt, fill: gray)[Panel 1 — composition RR°: pullback of (y,y), image of ⟨l≫x,r≫x⟩ into A×A.  RR° = (I; i≫fst, i≫snd).]

#figure(
  fletcher.diagram(
    spacing: 3em,
    node((2,0), [$A×A$], fill: cAA),
    node((2,1), [$I$], fill: cI),
    node((2,2), [$P$], fill: cP),
    node((1,3), [$T$], fill: cT),
    node((3,3), [$T$], fill: cT),
    node((0,4), [$A$], fill: cA),
    node((2,4), [$B$], fill: cB),
    node((4,4), [$A$], fill: cA),

    monic-edge((2,1), (2,0), label: [$i$]),
    cover-edge((2,2), (2,1), label: [$c$]),
    edge((2,2), (1,3), "->", label: [$l$], stroke: cl),
    edge((2,2), (3,3), "->", label: [$r$], stroke: cl),

    cover-edge((1,3), (0,4), label: [$x$], stroke: cx),
    edge((1,3), (2,4), "->", label: [$y$], stroke: cy),
    edge((3,3), (2,4), "->", label: [$y$], stroke: cy),
    cover-edge((3,3), (4,4), label: [$x$], stroke: cx),

    edge((2,1), (0,4), "->", bend: 18deg, label: [$i ≫ "fst"$]),
    edge((2,1), (4,4), "->", bend: -18deg, label: [$i ≫ "snd"$]),

    pb-corner((2,2), (1,3), (3,3)),
  ),
  caption: [],
)

#v(1em)

// ============ Panel 2: pullback J, k iso, witness ============
#text(size: 9pt, fill: gray)[Panel 2 — J := pullback of (Δ,i).  t lifts ⟨x,d≫c⟩.  x=t≫k cover, k monic ⇒ k iso (§1.363).  k⁻¹≫j: A→I witnesses 1⊑RR°.]

#figure(
  fletcher.diagram(
    spacing: 3.2em,
    node((1,0), [$T$], fill: cT),
    node((2,1), [$J$], fill: cJ),
    node((4,1), [$I$], fill: cI),
    node((2,3), [$A$], fill: cA),
    node((4,3), [$A×A$], fill: cAA),

    edge((1,0), (4,1), "->", label: [$d ≫ c$]),
    cover-edge((1,0), (2,3), label: [$x$], stroke: cx),
    lift-edge((1,0), (2,1), label: [$t$]),
    edge((2,1), (4,1), "->", label: [$j$], stroke: cj),
    iso-edge((2,1), (2,3), label: [$k$]),
    monic-edge((4,1), (4,3), label: [$i$]),
    monic-edge((2,3), (4,3), label: [$Δ$]),

    witness-edge((2,3), (4,1), label: [$k^(-1) ≫ j$]),

    pb-corner((2,1), (4,1), (2,3), s: 0.15),
  ),
  caption: [hdl: (d≫c)≫i = x≫Δ,  t:=pbJ.lift⟨T,x,d≫c⟩,  ht: t≫k=x.  k monic, x=cover ⇒ k iso.] + [  h := k⁻¹≫j satisfies pf₁: h≫(i≫fst)=1, pf₂: h≫(i≫snd)=1.],
)

#v(0.3em)

#text(size: 8pt, fill: gray)[
  Legend:  ->> hollow head = cover,  >-> tailed = monic,  <-> double arrow = iso,
  dashed = induced / witness,  blue = witness,  ⌝ = pullback corner.
]
