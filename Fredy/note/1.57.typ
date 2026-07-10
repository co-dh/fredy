#import "@preview/fletcher:0.5.8" as fletcher: node, edge

#set page(width: auto, height: auto, margin: 1.5cm)
#set text(size: 14pt)
#set par(leading: 0.5em, justify: false)
#set align(center)

#let cSrc  = rgb("fff3e0")  // amber  — T
#let cA    = rgb("e8eaf6")  // indigo — A (source)
#let cB    = rgb("c8e6c9")  // green  — B (target, choice object)
#let cc    = rgb("e65100")  // orange — cover
#let cw    = rgb("1a6fd4")  // blue   — witness

#let cover-edge(from, to, label: none) = {
  edge(from, to, "->>", label: label, stroke: cc + 1.2pt)
}
#let col-edge(from, to, label: none) = {
  edge(from, to, "->", label: label, stroke: gray + 1.2pt)
}
#let witness-edge(from, to, label: none) = {
  edge(from, to, "->", dash: "dashed", label: label, stroke: cw + 1.8pt)
}

// =====================================================================
//  §1.56(11) vs §1.57 — source-projective vs target-choice
// =====================================================================

#text(size: 18pt, weight: "bold")[§1.56(11)  projective (source)  vs  §1.57  choice (target)]

#v(2em)

// ── §1.56(11) ────────────────────────────────────────────────────────

#text(size: 15pt, weight: "bold")[§1.56(11):  A projective ⇔ every entire relation *from* A contains a map]

#v(1em)

#figure(
  fletcher.diagram(
    spacing: 8em,
    label-sep: 1pt,

    // R tabulation
    node((4, 0),   [$T$], fill: cSrc),
    node((3, 2),   [$A$], fill: cA),     // ← A is the PROJECTIVE object, source of R
    node((5, 2),   [$B$], fill: rgb("f5f5f5")),

    // graph source
    node((4, 3.5), [$A$], fill: cA),

    cover-edge((4, 0), (3, 2),   label: [$x$]),
    col-edge((4, 0),   (5, 2),   label: [$y$]),
    col-edge((4, 3.5), (3, 2),   label: [$1_A$]),
    col-edge((4, 3.5), (5, 2),   label: [$z · y$]),
    witness-edge((4, 3.5), (4, 0), label: [$z$]),
  ),
  caption: [
    R is entire *from* A.  The left leg $x$ is a cover *to* A. \
    A projective ⇒ $x$ splits: $z · x = 1_A$.  \
    $z$ witnesses $op("graph")(z · y) ⊂ R$ — the map $z · y : A → B$ is contained in R. \
    *The projective object A is the* **source** *of the entire relation.*
  ],
)

#v(2em)

// ── §1.57 ───────────────────────────────────────────────────────────

#text(size: 15pt, weight: "bold")[§1.57:  B choice ⇔ every entire relation *to* B contains a map]

#v(1em)

#figure(
  fletcher.diagram(
    spacing: 8em,
    label-sep: 1pt,

    // R tabulation
    node((4, 0),   [$T$], fill: cSrc),
    node((3, 2),   [$A$], fill: rgb("f5f5f5")),
    node((5, 2),   [$B$], fill: cB),     // ← B is the CHOICE object, target of R

    // graph source
    node((4, 3.5), [$A$], fill: rgb("f5f5f5")),

    col-edge((4, 0),   (3, 2),   label: [$a$]),
    cover-edge((4, 0), (5, 2),   label: [$b$]),     // right leg is a cover!
    col-edge((4, 3.5), (3, 2),   label: [$1_A$]),
    col-edge((4, 3.5), (5, 2),   label: [$w · b$]),
    witness-edge((4, 3.5), (4, 0), label: [$w$]),
  ),
  caption: [
    R is entire *to* B.  For a relation *targeted at* B, "entire" means the
    *right* leg is a cover (via reciprocal: $R$ entire to B ⇔ $R°$ entire from B). \
    B choice ⇒ the right leg $b$ splits: $w · b = 1_B$ (but $w : A → T$, so
    the map is $w$ composed with the left leg...). \
    *The choice object B is the* **target** *of the entire relation.*
  ],
)

#v(2em)

// ── Comparison table ─────────────────────────────────────────────────

#text(size: 14pt, weight: "bold")[Comparison]

#table(
  columns: (auto, auto, auto),
  stroke: none,
  inset: 8pt,
  align: horizon,
  table.hline(),
  [$op("§")1.56(11)$ *projective*],  [$op("§")1.57$ *choice*],     [],
  table.hline(),
  [quantifies over *source* of R],    [quantifies over *target* of R], [],
  [$R : A → B$ entire],              [$R : A → C$ entire],           [],
  [left leg $x$ is cover, splits],    [right leg $y$ is cover, splits (via $R°$)], [],
  [map $z · y : A → B$],             [map $z' · x : A → C$],         [],
  table.hline(),
  [*dual* — same proof, swap columns], [], [],
  table.hline(),
)
