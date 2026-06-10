#import "@preview/fletcher:0.5.8" as fletcher: node, edge

#set page(width: auto, height: auto, margin: 1.5cm)
#set text(size: 15pt)
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

#let pb-corner(p, l, r, s: 0.3, stroke: 0.9pt + rgb("333")) = {
  let v1 = (l.at(0) - p.at(0), l.at(1) - p.at(1))
  let v2 = (r.at(0) - p.at(0), r.at(1) - p.at(1))
  let p1 = (p.at(0) + s * v1.at(0), p.at(1) + s * v1.at(1))
  let p2 = (p.at(0) + s * v2.at(0), p.at(1) + s * v2.at(1))
  let m  = (p.at(0) + s * (v1.at(0) + v2.at(0)), p.at(1) + s * (v1.at(1) + v2.at(1)))
  (edge(p1, m, "-", stroke: stroke), edge(p2, m, "-", stroke: stroke))
}

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

#text(size: 18pt, weight: "bold")[§1.564  tabulated_is_entire_iff_left_cover]

#v(2em)

// ============ Figure 1: construction of d ============

#figure(
  fletcher.diagram(
    spacing: 7em,
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
  caption: [Pullback of $(y, y)$.  The pair $⟨1_T, 1_T⟩$ lifts uniquely to $d: T → P$.],
)

#text(size: 13pt)[$d$ unique: $d l = 1_T$, \ $d r = 1_T$ \ with $l y = r y$]

#v(2.5em)

// ============ Figure 2: composition RR° ============

#figure(
  fletcher.diagram(
    spacing: 7em,
    node((2,0), [$A×A$], fill: cAA),
    node((2,1), [$I$], fill: cI),
    node((2,2), [$P$], fill: cP),
    node((1,3), [$T$], fill: cT),
    node((3,3), [$T$], fill: cT),
    node((0,4), [$A$], fill: cA),
    node((2,4), [$B$], fill: cB),
    node((4,4), [$A$], fill: cA),

    monic-edge((2,1), (2,0), label: [$i$]),
    edge((2,2), (2,1), "->>", dash: "dashed", label: [$c$], stroke: cx),
    edge((2,2), (1,3), "->", label: [$l$], stroke: cl),
    edge((2,2), (3,3), "->", label: [$r$], stroke: cl),

    cover-edge((1,3), (0,4), label: [$x$], stroke: cx),
    edge((1,3), (2,4), "->", label: [$y$], stroke: cy),
    edge((3,3), (2,4), "->", label: [$y$], stroke: cy),
    cover-edge((3,3), (4,4), label: [$x$], stroke: cx),

    edge((2,1), (0,4), "->", label: [$i pi_1$]),
    edge((2,1), (4,4), "->", label: [$i pi_2$]),

    pb-corner((2,2), (1,3), (3,3)),
  ),
  caption: [Composition $RR°$: pullback of $(y,y)$ then image into $A×A$.],
)

#text(size: 13pt)[$s := ⟨l x, r x⟩ : P → A×A$ (unique product pairing) \ $c i = s$, $c$ cover (unique: $i$ monic), $i$ monic]

#v(2.5em)

// ============ Figure 3: pullback J, k iso, witness ============

#figure(
  fletcher.diagram(
    spacing: 7.5em,
    node((1,0), [$T$], fill: cT),
    node((2,1), [$J$], fill: cJ),
    node((4,1), [$I$], fill: cI),
    node((2,3), [$A$], fill: cA),
    node((4,3), [$A×A$], fill: cAA),

    edge((1,0), (4,1), "->", label: [$d c$]),
    cover-edge((1,0), (2,3), label: [$x$], stroke: cx),
    lift-edge((1,0), (2,1), label: [$t$]),
    edge((2,1), (4,1), "->", label: [$j$], stroke: cj),
    iso-edge((2,1), (2,3), label: [$k$]),
    monic-edge((4,1), (4,3), label: [$i$]),
    monic-edge((2,3), (4,3), label: [$Δ$]),

    edge((2,3), (4,1), "->", label: [$k^(-1) j$], stroke: cwit + 1.2pt),

    pb-corner((2,1), (4,1), (2,3), s: 0.15),
  ),
  caption: [Pullback $J$ of $(Δ, i)$.  $x = t k$ cover with $k$ monic ⇒ $k$ iso (§1.363).  $h := k⁻¹ j$ witnesses $1 ≤ RR°$.],
)

#text(size: 13pt)[$J := "pullback of "(Δ, i)$, \ $t$ unique: $t k = x$, $t j = d c$ \ $(d c) i = x Δ$ \ $h (i π_1) = 1$, \ $h (i π_2) = 1$]

#v(2.5em)

// ============ Figure 4: entire ⇒ cover step 1 ============

#figure(
  fletcher.diagram(
    spacing: 7em,

    node((2.5, -0.8), [$A$],      fill: cA),
    node((2.5, 0),   [$A×A$],    fill: cAA),
    node((2.5, 1),   [$I$],      fill: cI),
    node((2.5, 2),   [$P$],      fill: cP),

    node((1, 3),     [$T$],      fill: cT),
    node((4, 3),     [$T$],      fill: cT),

    // C between A and B on row 4
    node((0, 4),     [$A$],      fill: cA),
    node((1.25, 4),  [$C$],      fill: none),
    node((2.5, 4),   [$B$],      fill: cB),
    node((3.75, 4),  [$C$],      fill: none),
    node((5, 4),     [$A$],      fill: cA),

    // ── Entire condition ──
    edge((2.5, -0.8), (0, 4), "->", label: [$1$], stroke: gray + 1.2pt),
    edge((2.5, -0.8), (5, 4), "->", label: [$1$], stroke: gray + 1.2pt),
    edge((2.5, -0.8), (2.5, 1), "->", bend: 20deg,
      label: [#text(fill: cwit)[$h$]], stroke: cwit + 1.2pt),

    // ── Composition RR° ──
    monic-edge((2.5, 1), (2.5, 0), label: [$i$]),
    edge((2.5, 2), (2.5, 1), "->>", dash: "dashed", label: [$c$], stroke: cx),
    edge((2.5, 2), (2.5, 0), "->", dash: "dashed", bend: 22deg, label: [$s$]),

    // ── Pullback legs ──
    edge((2.5, 2), (1, 3), "->", label: [$l$], stroke: cl),
    edge((2.5, 2), (4, 3), "->", label: [$r$], stroke: cl),

    // ── Tabulation ──
    edge((1, 3), (0, 4), "->", label: [$x$], stroke: cx),
    edge((1, 3), (2.5, 4), "->", label: [$y$], stroke: cy),
    edge((4, 3), (2.5, 4), "->", label: [$y$], stroke: cy),
    edge((4, 3), (5, 4), "->", label: [$x$], stroke: cx),

    // ── Factorization x = g m ──
    edge((1, 3), (1.25, 4), "->", label: [$g$]),
    edge((4, 3), (3.75, 4), "->", label: [$g$]),
    monic-edge((1.25, 4), (0, 4), label: [$m$]),
    monic-edge((3.75, 4), (5, 4), label: [$m$]),

    // ── Projections ──
    edge((2.5, 0), (0, 4), "->", label: [$pi_1$]),
    edge((2.5, 0), (5, 4), "->", label: [$pi_2$]),

    pb-corner((2.5, 2), (1, 3), (4, 3)),
  ),
  caption: [Entire condition $1_A ≤ RR°$ and factorization $x = g m$ with $m$ monic.],
)

#text(size: 13pt)[$1_A ≤ RR°$: $h (i π_1) = 1_A$, \ $h (i π_2) = 1_A$, \ $h i = Δ = ⟨1,1⟩$ \ $s := ⟨l x, r x⟩$ (unique), \ $c i = s$ ($c$ unique: $i$ monic) \ $x = g m$, \ $m: C → A$ monic]

#v(2.5em)

// ============ Figure 5: entire ⇒ cover step 2 — image minimality ============

#figure(
  fletcher.diagram(
    spacing: 7em,

    node((2.5, -0.8), [$A$],      fill: cA),
    node((2.5, 0),   [$A×A$],    fill: cAA),
    node((2.5, 1),   [$I$],      fill: cI),
    node((2.5, 2),   [$P$],      fill: cP),

    // C×C at same y as P, left side
    node((0.5, 2),   [$C×C$],    fill: none),

    // A target of π₁, right of P
    node((4, 1.5),   [$A$],      fill: cA),

    // ── Entire condition ──
    edge((2.5, -0.8), (2.5, 1), "->", bend: 25deg,
      label: [#text(fill: cwit)[$h$]], stroke: cwit + 1.2pt),
    edge((2.5, -0.8), (4, 1.5), "->", label: [$1$], stroke: gray + 1.2pt),

    // ── Central column ──
    edge((2.5, 1), (2.5, 0), ">->", bend: -18deg, label: [$i$]),
    edge((2.5, 2), (2.5, 0), "->", dash: "dashed", bend: 18deg,  label: [$s$]),

    // ── Projection ──
    edge((2.5, 0), (4, 1.5), "->", label: [$pi_1$]),

    // ── Image minimality ──
    edge((2.5, 2), (0.5, 2), "->", label: [$w$]),
    edge((2.5, 1), (0.5, 2), "->", dash: "dashed",
      label: [#text(fill: cwit)[$e$]], stroke: cwit + 1.2pt),
    edge((0.5, 2), (2.5, 0), ">->", label: [$m×m$]),
  ),
  caption: [Image minimality lifts $I$ into $C×C$, producing $e$ with $e(m×m)=i$.  Then $(h e)π_1$ left-inverts $m$.],
)

#text(size: 13pt)[
  $w := ⟨l g, r g⟩$, $w (m×m) = s$, $m×m$ monic \
  $I$ = smallest monic subobject $s$ factors through \
  ⇒ $∃! e: I → C×C$ with $e (m×m) = i$ \

  #v(0.5em)
  $((h e) π_1) m = (h e)(π_1 m) = (h e)((m×m) π_1) = (h i) π_1 = 1_A$ \
  (① $π_1 m = (m×m) π_1$; \ ② $e(m×m)=i$; \ ③ $h i π_1 = 1_A$) \
  $m$ monic + left inverse ⇒ iso ⇒ $x = g m$ cover
]

#v(0.8em)

#text(size: 11pt, fill: gray)[
  Legend: \ ->> hollow head = cover, \ >-> tailed = monic, \ <-> double arrow = iso, \
  dashed = induced / witness, \ blue = witness, \ ⌝ = pullback corner.
]
