#import "@preview/dvdtyp:1.0.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/cetz:0.3.4"

#let subc = rgb("#1457a6")
#let imgc = rgb("#c0392b")
#let prec = rgb("#0a7d3f")
#let punch(body) = block(width: 100%, fill: rgb("#fdecea"), inset: 11pt,
  radius: (right: 5pt), stroke: (left: 3pt + imgc),
  [#text(weight: "bold", fill: imgc)[★ Punchline]#v(3pt)#body])

#show: dvdtyp.with(
  title: "The Pasting Lemma (§1.62)",
  accent: rgb("#c0392b"),
  abstract: [
    #text(12.5pt, fill: rgb("#c0392b"), style: "italic")[
      §1.62 — the intersection → union square of two subobjects is a pushout,
      with a concrete Set example and Freyd's relational proof that $R$ is a map
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
    edge((0,0), (1,0), text(8pt)[$overline(y)$], ">->", stroke: 0.8pt),
    edge((0,0), (0,1), text(8pt)[$overline(x)$], ">->", stroke: 0.8pt),
    edge((1,0), (1,1), text(8pt)[$x$], ">->", stroke: 0.8pt),
    edge((0,1), (1,1), text(8pt)[$y$], ">->", stroke: 0.8pt),
    node((0.78,0.78), text(9pt, fill: prec)[⌐]),
  )
]

Pushout means: a map $f : A_1 -> Q$ *from* $A_1$ and a map $g : A_2 -> Q$ *from* $A_2$ that *agree on
the overlap* — i.e. their two restrictions to $A_1 inter A_2$ coincide, $overline(y) f = overline(x) g$
(the top square commutes) — glue to a *unique* $R : A_1 union A_2 -> Q$ with $x R = f$ and $y R = g$.

Concretely in #smallcaps[Set]: $A_1 = {1,2,3}$, $A_2 = {2,3,4}$, overlap $A_1 inter A_2 = {2,3}$, union
${1,2,3,4}$, and $Q = {p,q,r,s}$. Take $f : 1 |-> p, #h(2pt) 2 |-> q, #h(2pt) 3 |-> r$ and
$g : 2 |-> q, #h(2pt) 3 |-> r, #h(2pt) 4 |-> s$. The agreement is the commuting condition: on the
overlap $f$ and $g$ *both* send $2 |-> q$ and $3 |-> r$ (the converging arrows below), so the four
arrows form one well-defined $R : {1,2,3,4} -> Q$. Had they disagreed at $2$ or $3$, no single $R$
could exist — that is the whole force of "agree on the overlap".

#align(center)[
  #cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let fcol = rgb("#1457a6"); let gcol = rgb("#0a7d3f"); let ov = rgb("#c0392b")
    circle((-0.7, 0), radius: (1.4, 0.95), stroke: 0.8pt + fcol, fill: fcol.lighten(93%))
    circle(( 0.7, 0), radius: (1.4, 0.95), stroke: 0.8pt + gcol, fill: gcol.lighten(93%))
    content((-1.7, 1.18), text(8pt, fill: fcol)[$A_1$])
    content(( 1.7, 1.18), text(8pt, fill: gcol)[$A_2$])
    content((0, 1.34), text(7pt, fill: ov)[overlap $A_1 inter A_2$])
    let edot(p, l) = { circle(p, radius: 1.7pt, fill: black); content((p.at(0), p.at(1)+0.27), text(7pt)[#l]) }
    edot((-1.45, 0), $1$); edot((0, 0.45), $2$); edot((0, -0.45), $3$); edot((1.45, 0), $4$)
    let qx = 4.6
    rect((qx - 0.5, -1.55), (qx + 0.5, 1.55), radius: 0.18, stroke: 0.7pt + gray)
    content((qx, 1.82), text(8pt)[$Q$])
    let qd(y, l) = { circle((qx, y), radius: 1.7pt, fill: black); content((qx + 0.34, y), text(7pt)[#l]) }
    qd(1.2, $p$); qd(0.4, $q$); qd(-0.4, $r$); qd(-1.2, $s$)
    let ae = qx - 0.55
    line((-1.28, 0.08), (ae, 1.16), mark: (end: ">"), stroke: 0.8pt + fcol)
    line((0.22, 0.52), (ae, 0.5), mark: (end: ">"), stroke: 0.8pt + fcol)
    line((0.22, -0.52), (ae, -0.3), mark: (end: ">"), stroke: 0.8pt + fcol)
    line((0.28, 0.34), (ae, 0.32), mark: (end: ">"), stroke: (dash: "dashed", paint: gcol, thickness: 0.8pt))
    line((0.28, -0.34), (ae, -0.5), mark: (end: ">"), stroke: (dash: "dashed", paint: gcol, thickness: 0.8pt))
    line((1.6, -0.1), (ae, -1.16), mark: (end: ">"), stroke: (dash: "dashed", paint: gcol, thickness: 0.8pt))
    content((2.5, 1.18), text(8pt, fill: fcol)[$f$]); content((2.7, -1.05), text(8pt, fill: gcol)[$g$])
  })
]

The pasted map $R = f union g$ is just *all six arrows together*; it is a well-defined function exactly
because the blue ($f$) and green ($g$) arrows *coincide* on the overlap ${2,3}$.

= The figure the book actually draws

Freyd's proof is purely *relational* (it never names elements). The picture below is the one in the
book on p.101: the pullback square on top, the two subobjects $x,y$ landing in the union $A$, a test
object $Q$ with the agreeing pair $f,g$, and the mediator $R : A -> Q$ to be constructed. Bars name the
*pullback legs* — $overline(y)$ is the copy of $y$ pulled back over $A_1$, $overline(x)$ the copy of
$x$ over $A_2$ — so $overline(y) : A_1 inter A_2 -> A_1$ and $overline(x) : A_1 inter A_2 -> A_2$.

#align(center)[
  #diagram(spacing: (20mm, 15mm), node-stroke: none, node-inset: 3pt,
    node((1,0), $A_1 inter A_2$, name: <cap>),
    node((0,1), $A_1$, name: <a1>),
    node((2,1), $A_2$, name: <a2>),
    node((1,2), $A$, name: <a>),
    node((1,3.05), $Q$, name: <q>),
    edge(<cap>, <a1>, $overline(y)$, ">->", label-side: left, stroke: 0.8pt),
    edge(<cap>, <a2>, $overline(x)$, ">->", label-side: right, stroke: 0.8pt),
    edge(<a1>, <a>, $x$, ">->", label-side: right, stroke: 0.8pt),
    edge(<a2>, <a>, $y$, ">->", label-side: left, stroke: 0.8pt),
    edge(<a1>, <q>, $f$, "->", bend: -30deg, label-side: left, stroke: 0.8pt),
    edge(<a2>, <q>, $g$, "->", bend: 30deg, label-side: right, stroke: 0.8pt),
    edge(<a>, <q>, $R$, "-->", label-side: left, stroke: 0.9pt),
    node((0.9,0.28), text(8pt, fill: prec)[⌐]),
  )
]

Everything is forced by ten relational facts, exactly the list the book writes down (composition in
diagram order, $R^(circle.small)$ = converse). The first eight are *generic regular-category* facts;
only the cover identity needs the pre-logos.

#block(width: 100%, fill: prec.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + prec))[
  #grid(columns: (1fr, 1fr), row-gutter: 7pt, column-gutter: 10pt,
    [(1) #h(3pt) $x x^(circle.small) = 1, #h(2pt) y y^(circle.small) = 1$ #h(1fr) — $x, y$ *monic*],
    [(2) #h(3pt) $x y^(circle.small) = overline(y)^(circle.small) overline(x)$ #h(1fr) — pullback *tabulates* overlap],
    [(3) #h(3pt) $1 subset.eq f f^(circle.small), #h(2pt) 1 subset.eq g g^(circle.small)$ #h(1fr) — $f, g$ *entire*],
    [(4) #h(3pt) $f^(circle.small) f subset.eq 1, #h(2pt) g^(circle.small) g subset.eq 1$ #h(1fr) — $f, g$ *simple*],
    [(5) #h(3pt) $overline(x) g = overline(y) f$ #h(1fr) — *agree on overlap*],
    [(6) #h(3pt) $(overline(y) f)^(circle.small) (overline(y) f) subset.eq 1$ #h(1fr) — $overline(y) f$ *simple* #text(fill: imgc)[(★)]],
  )
  #v(3pt)
  #line(length: 100%, stroke: 0.4pt + prec.lighten(50%))
  #v(2pt)
  *Cover* (the one pre-logos input): #h(4pt) $x^(circle.small) x union y^(circle.small) y = 1$. #h(1fr)
  A monic $z$ contains $"Im"(x), "Im"(y)$ iff $x^(circle.small)x subset.eq z^(circle.small)z$ and
  $y^(circle.small)y subset.eq z^(circle.small)z$; in a pre-logos the union $A_1 union A_2$ is least,
  so its coreflexive is $1$.
]

#block(width: 100%, fill: imgc.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + imgc))[
  *Why is (6) true? The book states it without a word.* #h(3pt) Because $overline(y) f$ is a
  *composite of maps*: $overline(y) : A_1 inter A_2 arrow.r.hook A_1$ is monic (hence a map) and
  $f : A_1 -> Q$ is a map, and maps are closed under composition [§1.561]. Every map is *simple*
  [§1.564], i.e. satisfies $h^(circle.small) h subset.eq 1$ — so $(overline(y) f)^(circle.small)
  (overline(y) f) subset.eq 1$. That is the *entire content* of the unexplained line; the same
  remark gives $f^(circle.small) f, g^(circle.small) g subset.eq 1$ in (4).
]

#block(width: 100%, fill: prec.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + prec))[
  *Why the cover $x^(circle.small) x union y^(circle.small) y = 1$?* #h(3pt) For a subobject
  $x : A_1 arrow.r.hook A$, the relation $x^(circle.small) x : A -> A$ is the *coreflexive*
  (sub-identity) cutting out $"Im"(x) = A_1$: in #smallcaps[Set], $x^(circle.small) x = {(a,a) : a in A_1}$,
  the diagonal on $A_1 subset.eq A$. Likewise $y^(circle.small) y$ is the diagonal on $A_2$, and their
  union is the diagonal on $A_1 union A_2$. A monic $z$ contains both images iff $x^(circle.small) x
  subset.eq z^(circle.small) z$ *and* $y^(circle.small) y subset.eq z^(circle.small) z$, i.e. iff
  $x^(circle.small) x union y^(circle.small) y subset.eq z^(circle.small) z$ — so $x^(circle.small) x
  union y^(circle.small) y$ is the coreflexive of the *least* subobject containing $A_1$ and $A_2$,
  their union $A_1 union A_2$. The proof's object $A$ *is* that union (the pushout corner, where $x, y$
  land — as in the figure above), so its coreflexive is the whole identity $1_A$. It is the *pre-logos*
  that makes the union of subobjects exist and be computed by this relational $union$.
]

#block(width: 100%, fill: subc.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + subc))[
  *Why $x y^(circle.small) = overline(y)^(circle.small) overline(x)$ (fact (2))?* #h(3pt) It is the
  *tabulation* of the composite — *by construction*, not a universal-property argument. Relational
  composition $x #h(1pt) ; #h(1pt) y^(circle.small)$ is *defined* by pulling back the cospan
  $A_1 attach(->, t: x) A attach(<-, t: y) A_2$; that pullback *is* the intersection $A_1 inter A_2$, and
  its two projections *are* the legs $overline(y), overline(x)$. Reading the relation off that
  jointly-monic span gives the equality $x y^(circle.small) = overline(y)^(circle.small) overline(x)$
  (likewise $y x^(circle.small) = overline(x)^(circle.small) overline(y)$). #h(3pt) Lean's `inter_lemma`
  records only the containment $x y^(circle.small) subset.eq overline(y)^(circle.small) overline(x)$ —
  all the monotone chain needs — because it forms the intersection over the object $A_1, A_2$ are
  subobjects of rather than over their union, so it compares two pullbacks by a map and lands on
  $subset.eq$; over the union (the figure's $A$) it is the equality above.
]

= The proof that $R$ is a map (Freyd, p.101)

Do not build a function and verify "well-defined + agrees". Instead write down a single *relation*
$ R = x^(circle.small) f union y^(circle.small) g #h(6pt) : #h(4pt) A -> Q $
and prove it is a *map*. By §1.564 a relation is a map iff it is *entire* ($1 subset.eq R R^(circle.small)$,
total) and *simple* ($R^(circle.small) R subset.eq 1$, single-valued). Both fall out of the facts above —
totality from the cover, single-valuedness from the agreement — with the only pre-logos input being the
cover and §1.616 (union distributes over composition, used to multiply out the unions).

*Entire.* Pump each cover-branch up with the totality of $f, g$ (fact (3)), then factor:
$ 1 #h(2pt) &subset.eq #h(2pt) x^(circle.small) 1 x union y^(circle.small) 1 y
  #h(4pt) subset.eq #h(4pt) x^(circle.small) f f^(circle.small) x union y^(circle.small) g g^(circle.small) y \
  &subset.eq #h(2pt) (x^(circle.small) f union y^(circle.small) g)(f^(circle.small) x union g^(circle.small) y)
  #h(4pt) subset.eq #h(4pt) R R^(circle.small) . $

*Simple.* Multiply out (§1.616), kill the diagonal monic loops by (1), reroute the cross terms by the
tabulation (2), and fold them together by the agreement (5):
$ R^(circle.small) R #h(2pt) &subset.eq #h(2pt) (f^(circle.small) x union g^(circle.small) y)(x^(circle.small) f union y^(circle.small) g) \
  &subset.eq #h(2pt) f^(circle.small) x x^(circle.small) f #h(2pt) union #h(2pt) f^(circle.small) x y^(circle.small) g #h(2pt) union #h(2pt) g^(circle.small) y x^(circle.small) f #h(2pt) union #h(2pt) g^(circle.small) y y^(circle.small) g \
  &subset.eq #h(2pt) f^(circle.small) f #h(2pt) union #h(2pt) f^(circle.small) overline(y)^(circle.small) overline(x) g #h(2pt) union #h(2pt) g^(circle.small) overline(x)^(circle.small) overline(y) f #h(2pt) union #h(2pt) g^(circle.small) g \
  &subset.eq #h(2pt) 1 #h(2pt) union #h(2pt) (overline(y) f)^(circle.small) overline(x) g #h(2pt) union #h(2pt) (overline(x) g)^(circle.small) overline(y) f #h(2pt) union #h(2pt) 1 \
  &subset.eq #h(2pt) 1 #h(2pt) union #h(2pt) (overline(y) f)^(circle.small) overline(y) f #h(2pt) union #h(2pt) (overline(y) f)^(circle.small) overline(y) f #h(4pt) subset.eq #h(4pt) 1 . $

Since $1 subset.eq R R^(circle.small)$ and $R^(circle.small) R subset.eq 1$, *$R$ is a map* [§1.564]. It is
the mediator: by (1), (2), (5),
$ x R = x(x^(circle.small) f union y^(circle.small) g) = x x^(circle.small) f union x y^(circle.small) g
  = f union overline(y)^(circle.small) overline(x) g = f union overline(y)^(circle.small) overline(y) f
  = (1 union overline(y)^(circle.small) overline(y)) f = f , $
and symmetrically $y R = g$. Uniqueness of $R$ is the cover once more: $x, y$ are jointly epic.

#punch[
  The mediating map is forced by the relational calculus: $R = x^(circle.small) f union y^(circle.small)
  g$ is *entire* because the cover splits $1_A$ and the totality of $f, g$ pushes each branch into
  $R R^(circle.small)$; *simple* because $R^(circle.small) R$ multiplies out into four terms that each
  reduce to $subset.eq 1_Q$ (the diagonals by the monic $x x^(circle.small) = 1$ and the map-cap
  $f^(circle.small) f subset.eq 1$; the cross terms by the tabulation $x y^(circle.small) =
  overline(y)^(circle.small) overline(x)$, the agreement (5), and the map-cap of $overline(y) f$); and
  *unique* because $x, y$ are jointly epic. The one step that needs the pre-logos is $union$ distributing
  over composition (§1.616) — which is why the lemma fails additively (1.622: it breaks for groups).
]

= §1.622 — when pasting can fail

The §1.62 proof has one non-formal input: $union$ distributes over composition (§1.616). Where that
fails, so can the lemma. §1.622 records two faces of this.

*Abelian categories — still a pushout, but for a different reason.* There $A_1 union A_2 = A_1 + A_2$,
and the intersection→union square is *bicartesian* (pullback $=$ pushout) straight from the additive
structure (the second isomorphism theorem). Freyd's relational proof does *not* apply: unions of
relations do not distribute over composition in any non-degenerate additive regular category.

*Groups — not a pushout.* $S_3$ is the group of all *six* rearrangements of three corners $0, 1, 2$
(the symmetries of a triangle): three rotations $0 1 2$ (do nothing), $1 2 0$, $2 0 1$, and three swaps
$1 0 2$, $0 2 1$, $2 1 0$ (each list records where corners $0, 1, 2$ go). Inside it sit two subgroups:

- $A_1 = ZZ_2 = {0 1 2, #h(4pt) s}$, the identity and the swap $s = 1 0 2$ — order $2$, since $s$ twice is the identity;
- $A_2 = ZZ_3 = {0 1 2, #h(4pt) r, #h(4pt) r^2}$, the identity and the rotation $r = 1 2 0$ — order $3$.

*The meet $A_1 inter A_2 = 1$.* An intersection of subgroups is a subgroup of each, so by Lagrange its
size divides both $2$ and $3$ — the only common divisor is $1$, leaving just the identity $0 1 2$ (the
one list in both). Coprime orders force a trivial overlap.

*The union $A_1 union A_2 = S_3$ — and this is the crux.* The lattice "union" is *not* set-union:
${0 1 2, #h(2pt) 1 0 2, #h(2pt) 1 2 0, #h(2pt) 2 0 1}$ is not even a subgroup, since composing $s$ with
$r$ gives $0 2 1$, outside the list. The *join* is the *smallest subgroup containing both* — the subgroup
*generated* by $s$ and $r$ (close that set under composition). A swap and a rotation generate everything,
so $chevron.l s, r chevron.r = S_3$ (its order is divisible by $2$ and $3$, hence by $6 = |S_3|$).

This closing-under-composition is exactly where groups depart from #smallcaps[Set]: there the join of two
*subsets* simply *is* their set-union, with nothing to close — so pasting always works. §1.62 would make
the square below a pushout — it is not.

#align(center)[
  #diagram(spacing: (25mm, 14mm), node-stroke: none, node-inset: 3pt,
    node((0,0), $1 = {e}$, name: <one>),
    node((1,0), $ZZ_2$, name: <z2>),
    node((0,1), $ZZ_3$, name: <z3>),
    node((1,1), $S_3$, name: <s3>),
    node((2.3,1), $ZZ_2 * ZZ_3$, name: <P>),
    edge(<one>, <z2>, ">->", stroke: 0.8pt),
    edge(<one>, <z3>, ">->", stroke: 0.8pt),
    edge(<z2>, <s3>, ">->", stroke: 0.8pt),
    edge(<z3>, <s3>, ">->", stroke: 0.8pt),
    edge(<z2>, <P>, "-->", bend: 30deg, stroke: 0.7pt),
    edge(<z3>, <P>, "-->", bend: -38deg, stroke: 0.7pt),
    edge(<P>, <s3>, text(7pt, fill: imgc)[onto, not 1-1], "->>", stroke: 0.9pt + imgc),
  )
]

The true pushout of $ZZ_2 <- 1 -> ZZ_3$ in #smallcaps[Grp] is the *free product* $ZZ_2 * ZZ_3$ — the
*infinite* modular group $"PSL"_2(ZZ)$. The comparison $ZZ_2 * ZZ_3 ->> S_3$ is onto but far from
injective: $S_3$ is the proper quotient that imposes the dihedral relation $s r s = r^2$ (a swap
conjugates the rotation to its inverse), which the free product never sees. A finite group is not the gluing; the
genuine gluing is infinite.

#block(width: 100%, fill: subc.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + subc))[
  *Pasting literally fails here.* #h(3pt) Put $Q = ZZ_2 * ZZ_3$ and let $f : ZZ_2 -> Q$ and
  $g : ZZ_3 -> Q$ be the two inclusions. They *agree on the overlap* $1$ (both fix $e$) — yet *no*
  homomorphism $R : S_3 -> Q$ extends them: its image would be a *finite* subgroup of $Q$ containing
  both factors, but those two already generate the *infinite* $Q$. Two maps agreeing on the overlap with
  nothing to glue them onto: exactly the failure of "paste". In #smallcaps[Set] (or any pre-logos) this
  cannot happen — §1.616 guarantees the gluing exists and is the union.
]

= §1.623 — positive pre-logos: sums are tagged unions

A *positive pre-logos* is a pre-logos in which every pair of objects $A, B$ embeds *disjointly* into
some common object. The book's whole definition is one square:

#align(center)[
  #diagram(spacing: (24mm, 13mm), node-stroke: none, node-inset: 4pt,
    node((0,0), $0$),
    node((1,0), $B$),
    node((0,1), $A$),
    node((1,1), $C$),
    edge((0,0), (1,0), "->", stroke: 0.8pt),
    edge((0,0), (0,1), "->", stroke: 0.8pt),
    edge((0,1), (1,1), ">->", stroke: 0.8pt),
    edge((1,0), (1,1), ">->", stroke: 0.8pt),
    node((0.22,0.3), text(9pt, fill: prec)[⌐]),
  )
]

*Reading the square.* The corner mark at $0$ makes it a *pullback*, and the pullback of two monos
$A arrow.r.hook C arrow.l.hook B$ is by definition their intersection in $"Sub"(C)$. So the diagram
says: $A inter B = 0$ inside $C$ — the two embedded copies are disjoint.

#block(width: 100%, fill: subc.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + subc))[
  *The quantifier is $exists$, not $forall$.* It does *not* say every pair of subobjects of every $C$
  meets in $0$ — that is false in any interesting category (take $A = B = C$: the pullback is $A$
  itself). It says: for every pair of *objects* there *exists some* host $C$ into which they embed
  disjointly. Choosing the least such host, $A union B = C$, gives the coproduct — hence a positive
  pre-logos has coproducts.
]

*This is Haskell's* `Either a b = Left a | Right b`. In #smallcaps[Set] the host is the tagged union
$C = ({0} times A) union ({1} times B)$: the tag is what forces the pullback to be empty even when
$A = B$, since $(0, a)$ never equals $(1, a)$. And it is exactly why "has coproducts" is *weaker* than
"positive": a lattice has no tags, so its join collapses the overlap $A and B$ instead of separating it
— §1.626 below works this out on a concrete lattice.

*§1.624 is pattern matching.* Given $f : X -> B_1 + B_2$, set $X_i = f^(\#)(B_i)$ — "the inputs that
hit `Left`" and "the inputs that hit `Right`":

#align(center)[
  #diagram(spacing: (20mm, 14mm), node-stroke: none, node-inset: 3pt,
    node((0,0), $X_1$),
    node((1,0), $X$),
    node((2,0), $X_2$),
    node((0,1), $B_1$),
    node((1,1), $B_1 + B_2$),
    node((2,1), $B_2$),
    edge((0,0), (1,0), ">->", stroke: 0.8pt),
    edge((2,0), (1,0), ">->", stroke: 0.8pt),
    edge((0,0), (0,1), $f_1$, "->", label-side: left, stroke: 0.8pt),
    edge((1,0), (1,1), $f$, "->", stroke: 0.8pt),
    edge((2,0), (2,1), $f_2$, "->", label-side: right, stroke: 0.8pt),
    edge((0,1), (1,1), ">->", stroke: 0.8pt),
    edge((2,1), (1,1), ">->", stroke: 0.8pt),
  )
]

Then $X = X_1 + X_2$ and $f = f_1 + f_2$: every map into a sum factors through a case analysis of its
source. The case split is *exhaustive* because $f^(\#)$ preserves unions (the pre-logos axiom):
$X_1 union X_2 = f^(\#)(B_1 union B_2) = f^(\#)(B_1 + B_2) = X$. It is *exclusive* — no input matches
both branches — by the §1.61 toolkit: $f^(\#)$ preserves $inter$ for free (pullbacks commute), and
$f^(\#)(0) = 0$ is the nullary-union axiom, so
$X_1 inter X_2 = f^(\#)(B_1 inter B_2) = f^(\#)(0) = 0$. Finally, disjoint ($inter = 0$) $+$ covering
($union = X$) subobjects form a coproduct — that is the corollary of the pasting lemma quoted in
§1.622 above.

#punch[
  Positivity is disjunction *with tags*: landing in $A + B$ tells you which summand you are in. A
  pre-logos interprets the positive fragment of first-order logic ($top, and, bot, or, exists$ — no
  $not$, $=>$, $forall$) on its subobject lattices; a *positive* pre-logos realizes that fragment's
  $or$ at the object level, as `Either` — disjoint, stable, pattern-matchable sums, the way #smallcaps[Set]
  has them and a lattice of truth values does not.
]

= §1.625 — a regular representation is a pre-logos one iff it preserves disjoint unions

#quote(block: true)[
  Suppose A and B are positive pre-logoi and that $T : bold(A) -> bold(B)$ is a representation of
  regular categories. Then T is a representation of pre-logoi iff it preserves disjoint unions.
]

A *representation of regular categories* preserves finite limits and images (covers). A *representation
of pre-logoi* must preserve one more thing: the pre-logos structure — the finite *unions* of subobjects
$A_1 union A_2$ (and the empty union $0$). #h(3pt) (One trap: "$union$ is stable under inverse image" is
an *axiom of the category* $bold(A)$; it is *not* a condition on $T$. What $T$ has to preserve is the
*operation* $union$ itself.) So the entire gap between the two notions is one question: *does $T$
preserve $union$?*

*Freyd's one-line "because": a union is the image of a coproduct.*
$ A_1 union A_2 = "Im"([i_1, i_2] : A_1 + A_2 -> A) . $
The copairing $[i_1, i_2]$ lands both summands in $A$; its image — the least subobject containing both —
is their union. It factors as cover-then-mono:

#align(center)[
  #diagram(spacing: (26mm, 12mm), node-stroke: none, node-inset: 3pt,
    node((0,0), $A_1 + A_2$, name: <sum>),
    node((2,0), $A$, name: <A>),
    node((1,1), $A_1 union A_2$, name: <un>),
    edge(<sum>, <A>, text(8pt)[$[i_1, i_2]$], "->", stroke: 0.8pt),
    edge(<sum>, <un>, text(7pt)[cover], "->>", label-side: left, stroke: 0.8pt),
    edge(<un>, <A>, ">->", stroke: 0.8pt),
  )
]

In #smallcaps[Set], with $A_1 = {1,2,3}$ and $A_2 = {3,4,5}$ inside $A = {1,2,3,4,5}$: the coproduct
$A_1 + A_2$ is the *6-element tagged* union, the copairing *fuses* the two copies of $3$, and the *image*
of that fusing is exactly $A_1 union A_2 = {1,2,3,4,5}$ (5 elements). Coproduct, then image, gives union.

#block(width: 100%, fill: subc.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + subc))[
  *The union is embedding-dependent; the coproduct is not.* #h(3pt) The ambient $A$ is only a
  *container* — it need not be disjoint, nor even equal $A_1 union A_2$ ($A$ may be far bigger; the image
  still carves the union out). What varies is the *overlap* $A_1 inter A_2$ inside $A$: the copairing is
  *monic $<==>$ $A_1 inter A_2 = 0$* (in #smallcaps[Set] the only collisions are shared elements). So a
  union is *the coproduct with that overlap fused in* — a disjoint embedding fuses nothing, and there
  $union = +$ (§1.621). The *same* two sets get *different* unions under different embeddings, while the
  coproduct never moves:
  #v(5pt)
  #align(center)[
    #table(columns: 3, align: (left, center, left), inset: 6pt, stroke: 0.4pt + subc.lighten(45%),
      table.header([$A_1 = {1,2,3}$, and $B$ in $A$], [$A_1 union B$], [vs. coproduct]),
      [$B = {a, b}$ #h(4pt) (disjoint)], [${1,2,3,a,b}$ (5)], [$=$ coproduct],
      [$B = {3, 4}$ #h(4pt) (share $3$)], [${1,2,3,4}$ (4)], [$<$ coproduct],
      [$B = {2, 3}$ #h(4pt) ($B subset.eq A_1$)], [${1,2,3}$ (3)], [$<$ coproduct],
    )
  ]
  #v(3pt)
  The coproduct is always the 5-element ${1,2,3} + B$; the union slides between $max(|A_1|, |B|)$ and
  $|A_1| + |B|$ as the overlap shrinks. $"Im"(A_1 + A_2 -> A)$ is the coproduct pushed through the chosen
  embedding.
]

*Why this settles the "iff".* $T$ already preserves images, so
$ T(A_1 union A_2) = T("Im"(A_1 + A_2 -> A)) = "Im"(T(A_1 + A_2) -> T A) . $
- If $T$ preserves the *coproduct*, i.e. $T(A_1 + A_2) = T A_1 + T A_2$, the right side is
  $"Im"(T A_1 + T A_2 -> T A) = T A_1 union T A_2$: *preserves disjoint unions $=>$ preserves unions*.
- Conversely $T$ preserves pullbacks and $0$, so $A_1 inter A_2 = 0$ forces $T A_1 inter T A_2 = 0$; with
  union-preservation, $T(A_1 + A_2) = T A_1 union T A_2$ is then a *disjoint* union $= T A_1 + T A_2$:
  *preserves unions $=>$ preserves disjoint unions*.

*Concrete example.* The evaluation functor $"ev"_a : cal(S)^bold(A) -> cal(S)$ ($cal(S) = $
#smallcaps[Set], so $cal(S)^bold(A)$ is the functor category $bold(A) -> #smallcaps[Set]$), $F |-> F(a)$,
is a representation of regular categories — limits, covers and images in $cal(S)^bold(A)$ are all
computed pointwise. It preserves disjoint unions, $"ev"_a (F + G) = (F + G)(a) = F(a) + G(a)$, so by
§1.625 it is a representation of pre-logoi; and indeed $(F union G)(a) = F(a) union G(a)$ — the
coproduct-then-image at $a$ is exactly the coproduct-then-image in $cal(S)$.

#punch[
  You never check union-preservation directly. A regular representation already carries images, and
  *every union is the image of a coproduct*, so union-preservation collapses to the one cheaper condition
  "$T$ preserves disjoint unions". The condition has teeth: §1.626 (below) notes that the canonical
  embedding of a pre-logos into a positive one [2.217] is a regular representation that is *not* a
  pre-logos one — precisely because it fails to preserve coproducts.
]

= §1.626 — coproducts without positivity

#quote(block: true)[
  Coproducts can exist without positivity. Any distributive lattice, viewed as a category is a
  pre-logos with coproducts. It is positive iff it is degenerate.
]

The point is that "coproduct" is a *universal property* — a map $A + B -> Q$ is exactly a pair
$A -> Q$, $B -> Q$ — which *never mentions disjointness*. So $A + B$ can exist while the two injections
are *not* disjoint. Positivity is that missing extra: $A inter B = 0$ (injections monic and jointly
covering). A category can have every coproduct and still fail it.

*Witness.* Any distributive lattice, viewed as a thin category (one arrow $a -> b$ iff $a subset.eq b$),
has products $= inter$ and coproducts $= or$: the least upper bound $a or b$ genuinely satisfies the
coproduct universal property. So coproducts exist — but never disjointly:
$ {1,2} + {1,2} = {1,2} or {1,2} = {1,2}, quad "hence" quad {1,2} inter {1,2} = {1,2} eq.not 0 . $
Both copies collapse onto one; contrast #smallcaps[Set], where $1 + 1 = 2$ keeps them tagged apart.

*Positive iff degenerate.* Taking $b = a$, positivity would force $a inter a = a = 0$ for *every* object
$a$ — collapsing the whole lattice to a single point $0 = 1$.

#punch[
  This is exactly why the Lean class `DisjointBinaryCoproduct` (`Fredy/S1_62.lean`, §1.62) carries axioms
  *beyond* `HasBinaryCoproducts`: the lattice satisfies `HasBinaryCoproducts` — its join is a coproduct —
  yet violates `inl ∩ inr ⊆ ⊥` (`inl_inter_inr`). Positivity is the "not-a-mere-lattice" content:
  disjoint, tagged sums, the way #smallcaps[Set] has them and a lattice of truth values does not.
]
