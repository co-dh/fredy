#import "@preview/fletcher:0.5.8" as fletcher: node, edge

#set page(width: auto, height: auto, margin: 1.5cm)
#set text(size: 15pt)
#set par(leading: 0.5em, justify: false)
#set align(center)

// ── color palette (same as cover_to_entire.typ) ─────────────────────
#let cP  = rgb("c8e6c9")  // green   — pullback vertex
#let cA  = rgb("e1bee7")  // purple  — A
#let cB  = rgb("bbdefb")  // blue    — B
#let cC  = rgb("ffe0b2")  // orange  — C
#let cQ  = rgb("d7ccc8")  // brown   — Q (cocone target)
#let cu  = rgb("e65100")  // u orange
#let cv  = rgb("1565c0")  // v blue
#let cwit = rgb("1a6fd4") // witness blue

// ── reusable fragments ──────────────────────────────────────────────

#let pb-corner(p, l, r, s: 0.3, stroke: 0.9pt + rgb("333")) = {
  let v1 = (l.at(0) - p.at(0), l.at(1) - p.at(1))
  let v2 = (r.at(0) - p.at(0), r.at(1) - p.at(1))
  let p1 = (p.at(0) + s * v1.at(0), p.at(1) + s * v1.at(1))
  let p2 = (p.at(0) + s * v2.at(0), p.at(1) + s * v2.at(1))
  let m  = (p.at(0) + s * (v1.at(0) + v2.at(0)), p.at(1) + s * (v1.at(1) + v2.at(1)))
  (edge(p1, m, "-", stroke: stroke), edge(p2, m, "-", stroke: stroke))
}

#let cover-edge(from, to, label: none, stroke: black) = {
  edge(from, to, "->>", label: label, stroke: stroke)
}
#let lift-edge(from, to, label: none) = {
  edge(from, to, "->", dash: "dashed", label: label)
}
#let witness-edge(from, to, label: none, bend: 0deg) = {
  edge(from, to, "->", dash: "dashed", label: label, bend: bend, stroke: cwit + 1.2pt)
}

// ── document ────────────────────────────────────────────────────────

#text(size: 18pt, weight: "bold")[§1.565  pullback_of_surjective_is_pushout_Set]

#v(2em)

// ============ Figure 1: the statement ============

#figure(
  fletcher.diagram(
    spacing: 7em,
    label-sep: 1pt,
    node((1,0), [$P$], fill: cP),
    node((0,1), [$A$], fill: cA),
    node((2,1), [$C$], fill: cC),
    node((1,2), [$B$], fill: cB),
    node((1,3), [$Q$], fill: cQ),

    edge((1,0), (0,1), "->", label: [$p_1$]),
    edge((1,0), (2,1), "->", label: [$p_2$]),
    cover-edge((0,1), (1,2), label: [$u$], stroke: cu),
    cover-edge((2,1), (1,2), label: [$v$], stroke: cv),

    edge((0,1), (1,3), "->", bend: -25deg, label: [$a$]),
    edge((2,1), (1,3), "->", bend: 25deg, label: [$b$]),
    witness-edge((1,2), (1,3), label: [$h$]),

    pb-corner((1,0), (0,1), (2,1)),
  ),
  caption: [Pullback of surjections $u$, $v$ (covers in *Set*) is a pushout: \
    given $a$, $b$ with $p_1 a = p_2 b$, a unique $h$ has $u h = a$, $v h = b$.],
)

#v(2.5em)

// ============ Figure 2: key lemma h_ab via the one-point lift ============

#figure(
  fletcher.diagram(
    spacing: 7em,
    label-sep: 1pt,
    node((1,-1), [$bold(1)$]),
    node((1,0), [$P$], fill: cP),
    node((0,1), [$A$], fill: cA),
    node((2,1), [$C$], fill: cC),
    node((1,2), [$B$], fill: cB),
    node((1,3), [$Q$], fill: cQ),

    edge((1,-1), (0,1), "->", label: [$x$], stroke: gray + 1pt),
    edge((1,-1), (2,1), "->", label: [$z$], stroke: gray + 1pt),
    lift-edge((1,-1), (1,0), label: [$k$]),

    edge((1,0), (0,1), "->", label: [$p_1$]),
    edge((1,0), (2,1), "->", label: [$p_2$]),
    cover-edge((0,1), (1,2), label: [$u$], stroke: cu),
    cover-edge((2,1), (1,2), label: [$v$], stroke: cv),

    edge((0,1), (1,3), "->", bend: -25deg, label: [$a$]),
    edge((2,1), (1,3), "->", bend: 25deg, label: [$b$]),

    pb-corner((1,0), (0,1), (2,1)),
  ),
  caption: [Key lemma: $u(x) = v(z) ⇒ a(x) = b(z)$.  The cone $⟨x, z⟩ : bold(1) → A×C$ \
    lifts uniquely to $k : bold(1) → P$ with $p_1 k = x$, $p_2 k = z$.],
)

#text(size: 13pt)[$a(x) = a(p_1(k med ast.basic)) = b(p_2(k med ast.basic)) = b(z)$ \
  (middle step: the cocone condition $p_1 a = p_2 b$)]

#v(2.5em)

// ============ Figure 3: defining h fiberwise ============

#figure(
  fletcher.diagram(
    spacing: 6em,
    label-sep: 1pt,
    node((0,-0.8), text(fill: gray)[$A$]),
    node((1.5,-0.8), text(fill: gray)[$B$]),
    node((3,-0.8), text(fill: gray)[$C$]),

    node((0,0), [$x$]),
    node((0,1), [$x_0$]),
    node((1.5,0.5), [$y$]),
    node((3,0.5), [$z_0$]),
    node((1.5,1.8), [$h(y) := a(x_0)$]),

    edge((0,0), (1.5,0.5), "|->", label: [$u$], stroke: cu),
    edge((0,1), (1.5,0.5), "|->", label: [$u$], stroke: cu),
    edge((3,0.5), (1.5,0.5), "|->", label: [$v$], stroke: cv),
    witness-edge((1.5,0.5), (1.5,1.8), label: [$h$]),
  ),
  caption: [Defining $h$: for $y ∈ B$ pick $x_0 ∈ u^(-1)(y)$ ($u$ surjective) and set $h(y) := a(x_0)$. \
    Well-defined: any $x ∈ u^(-1)(y)$ gives the same value, via $z_0 ∈ v^(-1)(y)$ ($v$ surjective).],
)

#text(size: 13pt)[$u(x) = y = v(z_0) ⇒ a(x) = b(z_0)$ (key lemma), \
  $u(x_0) = y = v(z_0) ⇒ a(x_0) = b(z_0)$ \
  hence $a(x) = a(x_0)$ — independent of the chosen $x$. \
  #v(0.5em)
  $h(u(x)) = a(x)$ by construction; \
  $h(v(y)) = a(x) = b(y)$ for any $x ∈ u^(-1)(v(y))$ (key lemma); \
  uniqueness: $u$ surjective, so $h'(u(x)) = a(x)$ already determines $h'$.]

#v(0.8em)

#text(size: 11pt, fill: gray)[
  Legend: \ ->> hollow head = cover (surjection in *Set*), \ |-> = element assignment, \
  dashed = induced / witness, \ blue = witness, \ ⌝ = pullback corner.
]
