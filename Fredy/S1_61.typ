#import "@preview/dvdtyp:1.0.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let subc  = rgb("#1457a6")  // a map y / first factor (blue)
#let imgc  = rgb("#c0392b")  // the relation S / image (red)
#let prec  = rgb("#0a7d3f")  // the pullback / inverse image f# (green)
#let dot(c) = box(circle(radius: 2pt, fill: c, stroke: none))
#let punch(body) = block(width: 100%, fill: rgb("#fdecea"), inset: 11pt,
  radius: (right: 5pt), stroke: (left: 3pt + imgc),
  [#text(weight: "bold", fill: imgc)[★ Punchline]#v(3pt)#body])

#show: dvdtyp.with(
  title: $y S = (y times 1)^(#text(0.55em)[\#])(S)$,
  accent: rgb("#c0392b"),
  abstract: [
    #text(12.5pt, fill: rgb("#c0392b"), style: "italic")[
      §1.616 — pre-composing a relation by a map is an inverse image
    ]
  ],
)

For a *map* $y : C -> A$ and a *relation* $S : A -> B$, the composite $y S : C -> B$, as a subobject of
$C times B$, is the inverse image of $S$ along $y times 1$:

#align(center)[ #text(15pt)[$ y S quad = quad (y times 1)^(#text(0.55em)[\#])(S) $] ]

where $y times 1 = y times 1_B : C times B -> A times B, thick (c, b) |-> (y(c), b)$. As a pullback:

#align(center)[
  #diagram(spacing: (40mm, 15mm), node-stroke: none, node-inset: 4pt,
    node((0,0), $C times B$),
    node((1,0), $A times B$),
    node((0,1), text(fill: prec)[$y S$]),
    node((1,1), text(fill: imgc)[$S$]),
    edge((0,0), (1,0), text()[$y times 1$], "->", stroke: 0.8pt),
    edge((0,1), (0,0), ">->", stroke: 0.9pt + prec),
    edge((1,1), (1,0), ">->", stroke: 0.9pt + imgc),
    edge((1,1), (0,1), text(fill: prec)[$(y times 1)^(#text(0.55em)[\#])$], "->", stroke: 0.7pt + prec),
  )
]

== In #smallcaps[Set]

#align(center)[
  #diagram(spacing: (26mm, 9mm), node-inset: 2pt, node-stroke: none,
    node((0,0), [$c_1$ #h(3pt) #dot(subc)]),
    node((0,1), [$c_2$ #h(3pt) #dot(subc)]),
    node(enclose: ((0,0),(0,1)), stroke: 0.6pt + gray, inset: 10pt),
    node((1,0), [#dot(black) #h(3pt) $a_1$]),
    node((1,1), [#dot(black) #h(3pt) $a_2$]),
    node(enclose: ((1,0),(1,1)), stroke: 0.6pt + gray, inset: 10pt),
    node((2,0), [#dot(imgc) #h(3pt) $b_1$]),
    node((2,1), [#dot(black) #h(3pt) $b_2$]),
    node(enclose: ((2,0),(2,1)), stroke: 0.6pt + gray, inset: 10pt),
    edge((0,0), (1,0), "->", stroke: 0.8pt + subc),
    edge((0,1), (1,0), "->", stroke: 0.8pt + subc),
    edge((1,0), (2,0), "->", stroke: 0.8pt + imgc),
    edge((1,1), (2,1), "->", stroke: 0.8pt + imgc),
    node((0.5, 1.55), text(8pt, fill: subc)[$y$]),
    node((1.5, 1.55), text(8pt, fill: imgc)[$S$]),
  )
]

*As a composite:* $c thick (y S) thick b <==> (y(c), b) in S$. Both $c_1, c_2 |-> a_1$ and $a_1 thick S thick b_1$, so
$ y S = {(c_1, b_1), (c_2, b_1)} quad (c_2 -> a_1 -> b_1). $

*As an inverse image:* $y times 1$ sends $(c,b) |-> (a_1, b)$, so the preimage of $S$ is
$ (y times 1)^(#text(0.55em)[\#])(S) = { (c,b) : (y(c), b) in S } = {(c_1, b_1), (c_2, b_1)}. $

Same subset of $C times B$.

#punch[
  Pre-composing $S$ by the map $y$ is pulling $S$ back along $y times 1$. So inverse images preserving
  unions gives, for free, $y(S union T) = y S union y T$.
]
