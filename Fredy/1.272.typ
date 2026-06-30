#import "@preview/dvdtyp:1.0.1": *
#import "@preview/cetz:0.3.4"

#let subc = rgb("#1457a6")   // blue
#let imgc = rgb("#c0392b")   // red
#let prec = rgb("#0a7d3f")   // green
#let callout(c, body) = block(width: 100%, fill: c.lighten(94%), inset: 10pt, radius: 5pt,
  stroke: (left: 3pt + c), body)
#let punch(body) = block(width: 100%, fill: rgb("#fdecea"), inset: 11pt,
  radius: (right: 5pt), stroke: (left: 3pt + imgc),
  [#text(weight: "bold", fill: imgc)[★ Punchline]#v(3pt)#body])
#let yes = text(fill: prec, weight: "bold")[#sym.checkmark]
#let no  = text(fill: imgc, weight: "bold")[#sym.crossmark]

#set table(inset: 5pt, align: left + horizon, stroke: 0.4pt + luma(200))
#show raw.where(block: false): box.with(fill: luma(240), inset: (x: 2pt), outset: (y: 3pt), radius: 1.5pt)

#show: dvdtyp.with(
  title: "§1.272 — the Cayley representation, and how it relates to the slice A/B",
  subtitle: "Freyd & Scedrov, §1.272",
  author: none,
  accent: subc,
  abstract: [
    #text(11pt, fill: subc, style: "italic")[
      The reader's question: "the Cayley representation seems the same as a slice category."
      Answer: they coincide at the level of *objects* only. §1.272 packages those objects
      into a functor $A -> bold(S)$ by forgetting the slice's triangles and keeping only
      the right-action of postcomposition — the *regular representation* — which is what
      embeds $A$ faithfully into $bold(S)$.
    ]
  ],
)

= §1.272 recap: the Cayley representation

A small category $A$ is automatically a right $A$-set. The *Cayley representation* is a functor
$C : A -> bold(S)$ (where $bold(S)$ is the category of sets) that sends an object $B$ to the *set*
$ C(B) = { y : P -> B mid(|) "any source " P } = "all morphisms with target " B . $
On a morphism $x : A -> B$ it acts by *postcomposition*:
$ C(x) : C(A) -> C(B), quad y arrow.r.bar y x $
(diagram order: first $y : P -> A$, then $x : A -> B$, giving $y x : P -> B$).

= The coincidence: $C(B) = $ objects of $A\/B$

#callout(subc)[
  The slice category $A\/B$ has as its *objects* exactly the arrows into $B$ — every morphism
  $y : P -> B$ (for any source $P$) is an object of $A\/B$. So
  $ C(B) = "the set of objects of " A\/B . $
  That overlap is real and not accidental.
]

= The difference: category vs bare set

The two gadgets share the same underlying collection of objects, but they are different kinds
of things.

- *$A\/B$ is a category.* Besides the arrows-into-$B$ (its objects) it keeps the *triangles*
  between them: a morphism $(y : P -> B) -> (y' : P' -> B)$ in $A\/B$ is a map $t : P -> P'$
  with $t y' = y$ (diagram order: first $t$, then $y'$). Those triangles are the point of a
  slice.

- *$C(B)$ is a bare set.* $C$ forgets the triangles and remembers only the set of arrows
  into $B$ together with how postcomposition $y arrow.r.bar y x$ moves it. That action is the
  "representation."

So: $C(B) = $ objects of $A\/B$, with the slice's morphisms *forgotten*, repackaged as a
$bold(S)$-valued functor.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let nodefill = rgb("#eef3fb")
    // nodes: P, P', B
    let P  = (0.0, 2.5)
    let Pp = (3.5, 2.5)
    let B  = (1.75, 0.0)
    // draw a node (circle with label)
    let node(pos, lbl) = {
      circle(pos, radius: 0.38, fill: nodefill, stroke: 0.8pt + subc)
      content(pos, text(10pt)[#lbl])
    }
    // draw a trimmed arrow between two node centers
    let arr(p, q, col, lbl, loff) = {
      let dx = q.at(0) - p.at(0)
      let dy = q.at(1) - p.at(1)
      let L  = calc.sqrt(dx*dx + dy*dy)
      let ux = dx / L;  let uy = dy / L
      let s  = (p.at(0) + 0.44*ux, p.at(1) + 0.44*uy)
      let e  = (q.at(0) - 0.44*ux, q.at(1) - 0.44*uy)
      line(s, e, stroke: 1pt + col, mark: (end: ">"))
      let mx = (s.at(0) + e.at(0)) / 2
      let my = (s.at(1) + e.at(1)) / 2
      content((mx + loff.at(0), my + loff.at(1)), text(9pt, fill: col)[#lbl])
    }
    node(P,  [$P$])
    node(Pp, [$P'$])
    node(B,  [$B$])
    // t : P → P' (blue — the slice morphism)
    arr(P,  Pp, subc, [$t$],  (0.0, 0.30))
    // y : P → B (red)
    arr(P,  B,  imgc, [$y$],  (-0.38, 0.05))
    // y' : P' → B (green)
    arr(Pp, B,  prec, [$y'$], ( 0.40, 0.05))
    // commutativity label below
    content((1.75, -0.70), text(8pt, fill: luma(90))[$t y' = y$ #h(0.3em) (diagram order)])
  }),
  caption: [
    A morphism in $A\/B$ from the object $(y : P -> B)$ to the object $(y' : P' -> B)$:
    a map $t : P -> P'$ making the triangle commute ($t y' = y$, diagram order).
    *$C(B)$ forgets $t$ entirely* — it keeps only the set $\{y, y', ...\}$ of vertices
    together with the right-action of postcomposition.
  ],
)

= Two sharper framings

*1. $C$ is the regular representation, not a single representable.*

$ C(B) = product.co_(P in A) "Hom"(P, B) $
— the coproduct of *all* covariant representables $"Hom"(P, -)$ over every object $P$ of $A$.
(Contrast $"Hom"(P, -)$, which fixes one source $P$.) Summing over all sources is exactly
"$A$ acting on its own morphisms," i.e. $A$ as a right $A$-set.

*2. The monoid case makes it vivid.*

Take $A$ to be one object $ast$ (a monoid $M$). Then:
- $C(ast) = "all morphisms" = M$ itself, a set with right-multiplication $y arrow.r.bar y x$ —
  the classical *right regular representation*.
- $A\/ast$ is instead a *category*: its object-set is $M$, but it also has triangles $t$ with
  $t x = y$; for a group those make it a contractible groupoid (a torsor).

Same object-set $M$; different gadget once you look at morphisms.

#punch[
  The objects of $A\/B$ *are* the Cayley set $C(B)$. The Cayley representation then *forgets
  the triangles* and keeps only the right-action, turning that object-set into a functor
  $A -> bold(S)$. That is what embeds $A$ faithfully into $bold(S)$ (§1.272: every small
  category is isomorphic to a concrete category): postcomposition $y arrow.r.bar y x$ on $C$
  is injective — two distinct morphisms $x, x' : A -> B$ act differently on some element of
  $C(A)$ — giving a faithful functor.
]
