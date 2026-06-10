#import "@preview/fletcher:0.5.8" as fletcher: node, edge

#set page(width: auto, height: auto, margin: 1.5cm)
#set text(size: 11pt)
#set par(leading: 0.5em, justify: false)
#set align(center)

// ── reusable diagram fragments ──────────────────────────────────────

// Corner mark for a pullback node at grid position `pos`.
// `offset` (in grid cells) points toward the square's interior;
// `angle` rotates the ⌟ glyph so its arms parallel the two legs:
// 0deg for legs going right+down, 45deg for legs going down-left+down-right.
#let pb-corner(pos, offset: (0.3, 0.3), angle: 0deg, size: 17pt) = {
  node((pos.at(0) + offset.at(0), pos.at(1) + offset.at(1)),
       rotate(angle, origin: center, text(size: size, fill: rgb("333"), [$⌟$])),
       inset: 0pt, fill: none, stroke: none)
}

// A pullback square: f: L→C←R: g.
#let pullback-sq(f-name: [$f$], g-name: [$g$],
                  l-name: [$p_1$], r-name: [$p_2$],
                  p-pos: (1,1), l-pos: (0,2), r-pos: (2,2), c-pos: (1,3),
                  f-fill: none, g-fill: none, p-fill: none, c-fill: none,
                  l-stroke: black, r-stroke: black,
                  f-stroke: black, g-stroke: black,
                  name: "") = {
  let p-name = if name != "" { [$name$] } else { [$P$] }
  (
    // legs run down-left and down-right: corner sits on the bisector below P
    pb-corner(p-pos, offset: (0, 0.4), angle: 45deg),
    node(p-pos, p-name, fill: p-fill),
    node(l-pos, [$T$], fill: f-fill),
    node(r-pos, [$T$], fill: f-fill),
    node(c-pos, [$B$], fill: c-fill),
    edge(p-pos, l-pos, "->", label: l-name, stroke: l-stroke),
    edge(p-pos, r-pos, "->", label: r-name, stroke: r-stroke),
    edge(l-pos, c-pos, "->", label: f-name, stroke: f-stroke),
    edge(r-pos, c-pos, "->", label: g-name, stroke: g-stroke),
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
  edge(from, to, "->", dash: "dashed", label: label, stroke: rgb("1a6fd4") + 1.2pt)
}

// ── document ────────────────────────────────────────────────────────

#text(size: 13pt, weight: "bold")[§1.564  x is a cover ⇒ R entire — tabulated_is_entire_iff_left_cover]

#v(0.8em)

// ============ Panel 0: construction of d ============
#text(size: 9pt, fill: gray)[Panel 0 — pullback of (y,y): pair ⟨1_T,1_T⟩ over y induces unique lift d:T→P with d≫l=1, d≫r=1.]

#figure(
  fletcher.diagram(
    spacing: 3em,
    node((1,-1), [$T$], fill: rgb("#ffe0b2")),
    pullback-sq(
      f-name: [$y$], g-name: [$y$],
      l-name: [$l$], r-name: [$r$],
      p-pos: (1,0), l-pos: (0,1), r-pos: (2,1), c-pos: (1,2),
      p-fill: rgb("#c8e6c9"), f-fill: rgb("#ffe0b2"), c-fill: rgb("#bbdefb"),
      l-stroke: rgb("#43a047"), r-stroke: rgb("#43a047"),
      f-stroke: rgb("#1565c0"), g-stroke: rgb("#1565c0"),
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
    node((2,0), [$A×A$], fill: rgb("#b2dfdb")),
    node((2,1), [$I$], fill: rgb("#f8bbd0")),
    node((2,2), [$P$], fill: rgb("#c8e6c9")),
    node((1,3), [$T$], fill: rgb("#ffe0b2")),
    node((3,3), [$T$], fill: rgb("#ffe0b2")),
    node((0,4), [$A$], fill: rgb("#e1bee7")),
    node((2,4), [$B$], fill: rgb("#bbdefb")),
    node((4,4), [$A$], fill: rgb("#e1bee7")),

    monic-edge((2,1), (2,0), label: [$i$]),
    cover-edge((2,2), (2,1), label: [$c$]),
    edge((2,2), (1,3), "->", label: [$l$], stroke: rgb("#43a047")),
    edge((2,2), (3,3), "->", label: [$r$], stroke: rgb("#43a047")),

    cover-edge((1,3), (0,4), label: [$x$], stroke: rgb("#e65100")),
    edge((1,3), (2,4), "->", label: [$y$], stroke: rgb("#1565c0")),
    edge((3,3), (2,4), "->", label: [$y$], stroke: rgb("#1565c0")),
    cover-edge((3,3), (4,4), label: [$x$], stroke: rgb("#e65100")),

    // diagonal legs — minimal bend to avoid crossing nodes
    edge((2,1), (0,4), "->", bend: 18deg, label: [$i ≫ "fst"$]),
    edge((2,1), (4,4), "->", bend: -18deg, label: [$i ≫ "snd"$]),

    pb-corner((2,2), offset: (0, 0.4), angle: 45deg),
  ),
  caption: [],
)

#v(1em)

// ============ Panel 2: pullback J, k iso, witness ============
#text(size: 9pt, fill: gray)[Panel 2 — J := pullback of (Δ,i).  t lifts ⟨x,d≫c⟩.  x=t≫k cover, k monic ⇒ k iso (§1.363).  k⁻¹≫j: A→I witnesses 1⊑RR°.]

#figure(
  fletcher.diagram(
    spacing: 3.2em,
    node((1,0), [$T$], fill: rgb("#ffe0b2")),
    node((2,1), [$J$], fill: rgb("#d7ccc8")),
    node((4,1), [$I$], fill: rgb("#f8bbd0")),
    node((2,3), [$A$], fill: rgb("#e1bee7")),
    node((4,3), [$A×A$], fill: rgb("#b2dfdb")),

    edge((1,0), (4,1), "->", label: [$d ≫ c$]),
    cover-edge((1,0), (2,3), label: [$x$], stroke: rgb("#e65100")),
    lift-edge((1,0), (2,1), label: [$t$]),
    edge((2,1), (4,1), "->", label: [$j$], stroke: rgb("#f9a825")),
    iso-edge((2,1), (2,3), label: [$k$]),
    monic-edge((4,1), (4,3), label: [$i$]),
    monic-edge((2,3), (4,3), label: [$Δ$]),

    witness-edge((2,3), (4,1), label: [$k^(-1) ≫ j$]),

    pb-corner((2,1), offset: (0.22, 0.22)),
  ),
  caption: [hdl: (d≫c)≫i = x≫Δ,  t:=pbJ.lift⟨T,x,d≫c⟩,  ht: t≫k=x.  k monic, x=cover ⇒ k iso.] + [  h := k⁻¹≫j satisfies pf₁: h≫(i≫fst)=1, pf₂: h≫(i≫snd)=1.],
)

#v(0.3em)

#text(size: 8pt, fill: gray)[
  Legend:  ->> hollow head = cover,  >-> tailed = monic,  <-> double arrow = iso,
  dashed = induced / witness,  blue = witness,  ⌟ = pullback corner.
]
