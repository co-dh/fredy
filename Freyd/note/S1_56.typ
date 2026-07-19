#import "@preview/fletcher:0.5.8" as fletcher: node, edge

#set page(width: auto, height: auto, margin: 1.5cm)
#set text(size: 14pt)
#set par(leading: 0.5em, justify: false)
#set align(center)

// ── colour palette ──────────────────────────────────────────────────
#let cA   = rgb("e8eaf6")  // indigo light — A (feet)
#let cB   = rgb("e0f2f1")  // teal light  — B (feet)
#let cT   = rgb("fff3e0")  // amber light — T (top of R)
#let cGA  = rgb("fce4ec")  // pink light  — A (source of graph)
#let cw   = rgb("1a6fd4")  // blue        — witness z
#let cc   = rgb("e65100")  // orange      — cover x
#let cm   = rgb("2e7d32")  // green       — monic witness

// ── reusable edge styles ────────────────────────────────────────────
#let cover-edge(from, to, label: none) = {
  edge(from, to, "->>", label: label, stroke: cc)
}
#let col-edge(from, to, label: none) = {
  edge(from, to, "->", label: label, stroke: gray + 1.2pt)
}
#let witness-edge(from, to, label: none, bend: 0deg) = {
  edge(from, to, "->", dash: "dashed", label: label, bend: bend, stroke: cw + 1.8pt)
}

// =====================================================================
//  §1.56(11) — Projective ⇒ entire relation contains a map
// =====================================================================

#text(size: 18pt, weight: "bold")[§1.56(11):  projective ⇒ entire relation contains a map]

#v(1em)

#text(size: 12pt, fill: gray)[
  R is an entire relation from A, tabulated as #emph[⟨T; x: T → A, y: T → B⟩].
  \
  A is projective: the cover x has a left inverse z : A → T with z · x = 1#sub[A].
  \
  Then z is the §1.413 containment witness:  *graph(z · y) ⊂ R*.
]

#v(2em)

// ============== main diagram =========================================

#figure(
  fletcher.diagram(
    spacing: 8em,
    label-sep: 1pt,

    // ── objects ─────────────────────────────────────────────────
    // Right column: feet
    node((3, 1.5), [$A$], fill: cA),   // left foot
    node((5, 1.5), [$B$], fill: cB),   // right foot

    // Top: T — source of relation R
    node((4, 0),   [$T$], fill: cT),

    // Bottom: A — source of graph
    node((4, 3),   [$A$], fill: cGA),

    // ── edges from T (the relation R) ────────────────────────────
    cover-edge((4, 0), (3, 1.5), label: [$x$]),
    col-edge((4, 0),  (5, 1.5), label: [$y$]),

    // ── edges from A (the graph) ─────────────────────────────────
    edge((4, 3), (3, 1.5), "->", label: [$1_A$], stroke: gray + 1.2pt),
    col-edge((4, 3),  (5, 1.5), label: [$z · y$]),

    // ── witness z (the containment arrow) ────────────────────────
    witness-edge((4, 3), (4, 0), label: [$z$]),

    // ── monic-pair bracket on (x, y) ─────────────────────────────
  ),
  caption: [
    *§1.413 containment:* the dashed arrow $z$ is the (unique, monic) witness
    #sym.arrow.r  $z · x = 1_A$ and $z · y = z · y$ \
    #sym.arrow.r  $z · x = 1_A$ makes $z$ a *split monic* \
    #sym.arrow.r  so $z$ is monic, matching §1.413's "necessarily monic" \
    *Left:* columns of the tabulated relation $R$. \
    *Right:* columns of the contained graph $op("graph")(z · y)$.
  ],
)

#v(1.5em)

// =====================================================================
//  §1.413 detail — containment witness is unique & monic
// =====================================================================

#text(size: 15pt, weight: "bold")[§1.413:  containment witness]

#v(0.5em)

#figure(
  fletcher.diagram(
    spacing: 8em,
    label-sep: 1pt,

    node((2, 2),   [$R_"src"$], fill: rgb("fff3e0")),  // T (contained)
    node((4, 2),   [$S_"src"$], fill: rgb("e8f5e9")),  // S.src (containing)

    node((2, 4),   [$A_1$], fill: rgb("f3e5f5")),
    node((3, 4),   [$A_2$], fill: rgb("f3e5f5")),

    // columns
    col-edge((2, 2), (2, 4), label: [$x_1$]),
    col-edge((2, 2), (3, 4), label: [$x_2$]),
    col-edge((4, 2), (2, 4), label: [$x'_1$]),
    col-edge((4, 2), (3, 4), label: [$x'_2$]),

    // witness
    edge((2, 2), (4, 2), ">->", label: [$z$], stroke: cm + 1.4pt),
  ),
  caption: [
    General definition:  $(T; x_i) ⊂ (T'; x'_i)$ \
    $⇔ ∃ z: T → T'$ with $z · x'_i = x_i$ for all $i$. \
    $z$ is *unique* (because the $x'_i$ are a monic family) and *necessarily monic*
    (because $z = z'$ when post-composed with a monic family).
  ],
)

// =====================================================================
//  §1.56(11) in Lean  (the exact theorems)
// =====================================================================

#v(2em)
#text(size: 15pt, weight: "bold")[Formalized in  `Freyd/S1_56.lean`]

#v(0.5em)

#text(size: 12pt)[
  `projective_entire_contains_map`  (⇒) \
  `entire_contains_map_projective`  (⇐) \
  `RelHom_unique`  — witness is unique \
  `RelHom_monic`   — witness is monic
]
