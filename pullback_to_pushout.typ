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
#let cx  = rgb("e65100")  // x orange
#let cy  = rgb("1565c0")  // y blue
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
#let rel-edge(from, to, label: none) = {
  edge(from, to, "->", dash: "dashed", label: label, stroke: gray + 1.2pt)
}
#let witness-edge(from, to, label: none, bend: 0deg) = {
  edge(from, to, "->", dash: "dashed", label: label, bend: bend, stroke: cwit + 1.2pt)
}

// ── document ────────────────────────────────────────────────────────

#text(size: 18pt, weight: "bold")[§1.565  pullback_of_surjective_is_pushout_Set]

#v(2em)

// ============ Figure 1: the relation R ============

#figure(
  fletcher.diagram(
    spacing: 7em,
    label-sep: 1pt,
    node((1,0), [$P$], fill: cP),
    node((0,1), [$A$], fill: cA),
    node((2,1), [$C$], fill: cC),
    node((1,2), [$B$], fill: cB),
    node((1,3), [$Q$], fill: cQ),

    cover-edge((1,0), (0,1), label: [$p_1$]),
    cover-edge((1,0), (2,1), label: [$p_2$]),
    cover-edge((0,1), (1,2), label: [$x$], stroke: cx),
    cover-edge((2,1), (1,2), label: [$y$], stroke: cy),

    edge((0,1), (1,3), "->", bend: -25deg, label: [$u$]),
    edge((2,1), (1,3), "->", bend: 25deg, label: [$v$]),
    rel-edge((1,2), (1,3), label: [$R$]),

    pb-corner((1,0), (0,1), (2,1)),
  ),
  caption: [Pullback of covers $x$, $y$ (surjections in *Set*); $p_1$, $p_2$ are covers too \
    (pullbacks transfer covers).  Given a cocone $u$, $v$ with $p_1 u = p_2 v$, \
    define the *relation* $R := x°u ∩ y°v : B arrow.r.not Q$ — to be shown a map.],
)

#text(size: 13pt)[In *Set*: $b R q ⟺ (∃ a. thin x(a) = b ∧ u(a) = q) ∧ (∃ c. thin y(c) = b ∧ v(c) = q)$]

#v(2.5em)

// ============ Figure 2: key lemma via the one-point lift ============

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

    edge((1,-1), (0,1), "->", label: [$a$], stroke: gray + 1pt),
    edge((1,-1), (2,1), "->", label: [$c$], stroke: gray + 1pt),
    lift-edge((1,-1), (1,0), label: [$k$]),

    cover-edge((1,0), (0,1), label: [$p_1$]),
    cover-edge((1,0), (2,1), label: [$p_2$]),
    cover-edge((0,1), (1,2), label: [$x$], stroke: cx),
    cover-edge((2,1), (1,2), label: [$y$], stroke: cy),

    edge((0,1), (1,3), "->", bend: -25deg, label: [$u$]),
    edge((2,1), (1,3), "->", bend: 25deg, label: [$v$]),

    pb-corner((1,0), (0,1), (2,1)),
  ),
  caption: [Key lemma: $x(a) = y(c) ⇒ u(a) = v(c)$.  The cone $⟨a, c⟩ : bold(1) → A×C$ \
    lifts uniquely to $k : bold(1) → P$ with $p_1 k = a$, $p_2 k = c$.],
)

#text(size: 13pt)[$u(a) = u(p_1(k med ast.basic)) = v(p_2(k med ast.basic)) = v(c)$ \
  (middle step: the cocone condition $p_1 u = p_2 v$)]

#v(2.5em)

// ============ Figure 3: R is a map; xR = u, yR = v ============

#figure(
  fletcher.diagram(
    spacing: 6em,
    label-sep: 1pt,
    node((0,-0.7), text(fill: gray)[$A$]),
    node((1,-0.7), text(fill: gray)[$B$]),
    node((2,-0.7), text(fill: gray)[$C$]),

    node((0,0), [$a$]),
    node((1,0.4), [$b$]),
    node((2,0), [$c$]),
    node((1,1.7), [$u(a) = v(c) =: h(b)$]),

    edge((0,0), (1,0.4), "|->", label: [$x$], stroke: cx),
    edge((2,0), (1,0.4), "|->", label: [$y$], stroke: cy),
    edge((0,0), (1,1.7), "|->", bend: -15deg, label: [$u$]),
    edge((2,0), (1,1.7), "|->", bend: 15deg, label: [$v$]),
    witness-edge((1,0.4), (1,1.7), label: [$h$]),
  ),
  caption: [$R$ is a map — call it $h$: every $b$ has $a ∈ x^(-1)(b)$, $c ∈ y^(-1)(b)$ (covers), \
    and the key lemma makes all candidate values agree, so $h(b) := u(a)$ is forced.],
)

#text(size: 13pt)[
  entire: $b thin R thin u(a)$ — witnesses $a$, $c$, with $v(c) = u(a)$ by the key lemma \
  simple: $b R q$, $b R q'$ $⇒$ $q = u(a) = v(c') = q'$ — the key lemma *crosses* the two halves of $R$ \
  #v(0.5em)
  $x R = u$: $(x(a)) thin R thin (u(a))$ holds, so $h(x(a)) = u(a)$ by simplicity; likewise $y R = v$ \
  uniqueness: $x$ cover $⇒$ epi: $h'(x(a)) = u(a)$ already determines $h'$
]

#v(0.8em)

#text(size: 11pt, fill: gray)[
  Legend: \ ->> hollow head = cover (surjection in *Set*), \ |-> = element assignment, \
  dashed gray = relation, \ dashed blue = the resulting map, \ ⌝ = pullback corner.
]
