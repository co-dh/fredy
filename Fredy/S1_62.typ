#import "@preview/dvdtyp:1.0.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let subc = rgb("#1457a6")
#let imgc = rgb("#c0392b")
#let prec = rgb("#0a7d3f")
#let dot(c) = box(circle(radius: 2pt, fill: c, stroke: none))
#let punch(body) = block(width: 100%, fill: rgb("#fdecea"), inset: 11pt,
  radius: (right: 5pt), stroke: (left: 3pt + imgc),
  [#text(weight: "bold", fill: imgc)[★ Punchline]#v(3pt)#body])

#show: dvdtyp.with(
  title: "The Pasting Lemma (§1.62)",
  accent: rgb("#c0392b"),
  abstract: [
    #text(12.5pt, fill: rgb("#c0392b"), style: "italic")[
      §1.62 — the intersection → union square of two subobjects is a pushout
    ]
  ],
)

In a pre-logos, for subobjects $A_1, A_2 arrow.r.hook A$ with intersection $A_1 inter A_2$ and union
$A_1 union A_2$, this square of monics is a *pushout*:

#align(center)[
  #diagram(spacing: (34mm, 15mm), node-stroke: none, node-inset: 4pt,
    node((0,0), $A_1 inter A_2$),
    node((1,0), $A_1$),
    node((0,1), $A_2$),
    node((1,1), $A_1 union A_2$),
    edge((0,0), (1,0), text(8pt)[$overline(x)$], ">->", stroke: 0.8pt),
    edge((0,0), (0,1), text(8pt)[$overline(y)$], ">->", stroke: 0.8pt),
    edge((1,0), (1,1), text(8pt)[$x$], ">->", stroke: 0.8pt),
    edge((0,1), (1,1), text(8pt)[$y$], ">->", stroke: 0.8pt),
    node((0.78,0.78), text(9pt, fill: prec)[⌐]),
  )
]

Pushout means: a function out of $A_1$ and one out of $A_2$ that *agree on the overlap* glue to a
unique function on $A_1 union A_2$. In #smallcaps[Set] with $A_1 = {1,2,3}$, $A_2 = {2,3,4}$, overlap
$A_1 inter A_2 = {2,3}$, union $A_1 union A_2 = {1,2,3,4}$: given $f$ on $A_1$ and $g$ on $A_2$ with
$f = g$ on ${2,3}$, the glued map sends $1$ by $f$, $4$ by $g$, and $2,3$ by either (they agree).

= Why it is a pushout: $R = x^(circle.small) f union y^(circle.small) g$ is a map

A relation is a *map* iff $1 subset.eq R R^(circle.small)$ (*entire*) and $R^(circle.small) R subset.eq
1$ (*simple*) — §1.564. Given $f : A_1 -> Q$, $g : A_2 -> Q$ agreeing on the overlap
($overline(x) f = overline(y) g$), set $R = x^(circle.small) f union y^(circle.small) g : A -> Q$.
Four relational facts close it (diagram order; checked in #smallcaps[Set]):

#block(width: 100%, fill: prec.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + prec))[
  + $x x^(circle.small) = 1$ #h(1fr) — $x$ is *monic*
  + $1 subset.eq f f^(circle.small)$ #h(1fr) — $f$ is a *map* (entire)
  + $x^(circle.small) x union y^(circle.small) y = 1$ #h(1fr) — $x, y$ *cover* $A$ (pre-logos: the two image-coreflexives fill $A$)
  + $(overline(x) f)^(circle.small) (overline(x) f) subset.eq 1$ #h(1fr) — $overline(x) f$ is a *map* (simple)
]

*Entire.* By (3) then (2): #h(3pt) $1 = x^(circle.small) x union y^(circle.small) y subset.eq
x^(circle.small) f f^(circle.small) x union y^(circle.small) g g^(circle.small) y subset.eq R R^(circle.small)$.

*Simple.* $R^(circle.small) R$ expands to four terms; the diagonal ones reduce by (1) to
$f^(circle.small) f, g^(circle.small) g subset.eq 1$, and the cross terms reduce — via the tabulation
$x y^(circle.small) = overline(x)^(circle.small) overline(y)$ of the intersection and the agreement
$overline(x) f = overline(y) g$ — to $(overline(x) f)^(circle.small)(overline(x) f) subset.eq 1$ by (4).
So $R^(circle.small) R subset.eq 1$.

Hence $R$ is a map. Then $x R = x x^(circle.small) f union x y^(circle.small) g = f$ (by (1), the second
term absorbed), similarly $y R = g$, and $R$ is *unique* because $x, y$ cover.

#punch[
  The mediating map is forced by the relational calculus: $R = x^(circle.small) f union y^(circle.small) g$
  is entire because the inclusions cover, simple because everything in sight is a map, and unique because
  the inclusions are jointly epic. The one pre-logos-only input is that *union distributes over
  composition* (§1.616) — which is why the lemma fails in a bare regular category.
]

= §1.565 vs §1.62 — same method, different square

Both build a mediating map as a union/intersection of relations and check it is a map. They differ in
*which* arrows and *which* category:

#grid(columns: (1fr, 1fr), gutter: 18pt,
  [
    #align(center)[*§1.62 — monics, pre-logos*]
    #align(center)[
      #diagram(spacing: (16mm, 9mm), node-stroke: none, node-inset: 3pt,
        node((0,0), text(8pt)[$A_1 inter A_2$]),
        node((1,0), text(8pt)[$A_1$]),
        node((0,1), text(8pt)[$A_2$]),
        node((1,1), text(8pt)[$A_1 union A_2$]),
        edge((0,0),(1,0), ">->", stroke: 0.7pt),
        edge((0,0),(0,1), ">->", stroke: 0.7pt),
        edge((1,0),(1,1), ">->", stroke: 0.7pt),
        edge((0,1),(1,1), ">->", stroke: 0.7pt),
      )
    ]
    Mediator $R = x^(circle.small) f union y^(circle.small) g$. Needs §1.616 (union over composition).
  ],
  [
    #align(center)[*§1.565 — covers, regular*]
    #align(center)[
      #diagram(spacing: (16mm, 9mm), node-stroke: none, node-inset: 3pt,
        node((0,0), text(8pt)[$P$]),
        node((1,0), text(8pt)[$B$]),
        node((0,1), text(8pt)[$C$]),
        node((1,1), text(8pt)[$D$]),
        edge((0,0),(1,0), "->>", stroke: 0.7pt),
        edge((0,0),(0,1), "->>", stroke: 0.7pt),
        edge((1,0),(1,1), "->>", stroke: 0.7pt),
        edge((0,1),(1,1), "->>", stroke: 0.7pt),
      )
    ]
    Mediator $R = (x^(circle.small) u) inter (y^(circle.small) u)$. Holds in any regular category.
  ],
)

One glues monics (subobjects) into their union; the other glues a pullback of covers (epis). Dual sides
of the factorization — and only the monic side needs the extra pre-logos axiom.
