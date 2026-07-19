#import "@preview/dvdtyp:1.0.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/cetz:0.3.4"

#let subc = rgb("#1457a6")   // blue  — inverse image π# / f#
#let imgc = rgb("#c0392b")   // red   — direct image (∃)
#let prec = rgb("#0a7d3f")   // green — right adjoint (∀)
#let callout(c, body) = block(width: 100%, fill: c.lighten(94%), inset: 10pt, radius: 5pt,
  stroke: (left: 3pt + c), body)
#let gloss(body) = text(9pt, fill: luma(110), style: "italic", body)

#show raw.where(block: false): box.with(fill: luma(240), inset: (x: 2pt), outset: (y: 3pt), radius: 1.5pt)

#show: dvdtyp.with(
  title: "§1.7 — the two adjoints of f#: why “existential” and “universal”",
  subtitle: "Freyd & Scedrov, §1.7 (opening definition)",
  author: none,
  accent: subc,
  abstract: [
    #text(11pt, fill: subc, style: "italic")[
      The reader's question: "in §1.7 the logos makes $f^\#$ a *left* adjoint? Isn't it already
      a *right* adjoint in pre-logoi?" Answer: both, on opposite sides — the chain is
      $f tack.l f^\# tack.l f^(\#\#)$, and the two outer functors are the quantifiers $exists$
      and $forall$. Lean: `Fredy/S1_70.lean` (`Logos`, `HasRightAdjointImage`,
      `DirectImage` = `existsAlong`).
    ]
  ],
)

= The picture: who passed what

$B = "Students" = {"Ann", "Bob", "Cid"}$, $C = "Courses" = {"Alg", "Top"}$, and the predicate
$P subset.eq B times C$ records who passed what: $P(s, c) =$ "student $s$ passed course $c$".

#figure(
  cetz.canvas({
    import cetz.draw: *
    let pass(p) = circle(p, radius: 0.14, fill: imgc, stroke: none)
    let fail(p) = circle(p, radius: 0.14, fill: white, stroke: gray + 0.8pt)

    // the ambient set B×C
    rect((0.3, 0.5), (6.7, 3.1), stroke: luma(160) + 0.6pt, fill: luma(250))
    content((6.9, 2.9), text(10pt)[$B times C$], anchor: "west")
    content((6.9, 2.35), text(9pt, fill: imgc)[$P$ = filled dots], anchor: "west")

    // one fiber highlighted: the column over Bob
    rect((2.6, 0.62), (4.0, 2.98), stroke: (paint: subc, dash: "dashed", thickness: 0.8pt))
    content((3.3, 3.4), text(8.5pt, fill: subc)[fiber $pi^(-1) ("Bob") = {"Bob"} times C tilde.equiv C$])

    // C on the left
    content((-0.15, 1.2), text(10pt)[Alg], anchor: "east")
    content((-0.15, 2.4), text(10pt)[Top], anchor: "east")
    content((-1.0, 1.8), text(10pt)[$C$], anchor: "east")

    // the pairs: columns Ann, Bob, Cid × rows Alg, Top
    pass((1.3, 1.2)); pass((1.3, 2.4))   // Ann passed both
    pass((3.3, 1.2)); fail((3.3, 2.4))   // Bob passed Alg only
    fail((5.3, 1.2)); fail((5.3, 2.4))   // Cid passed none

    // projection down to B
    line((6.9, 0.5), (6.9, -0.5), mark: (end: ">"), stroke: 1pt)
    content((7.1, 0.0), text(10pt)[$pi$], anchor: "west")
    content((1.3, -0.75), text(10pt)[Ann])
    content((3.3, -0.75), text(10pt)[Bob])
    content((5.3, -0.75), text(10pt)[Cid])
    content((-0.15, -0.75), text(10pt)[$B$], anchor: "east")

    // the two outputs, as subsets of B
    line((0.8, -1.25), (3.8, -1.25), stroke: imgc + 1.2pt)
    content((4.0, -1.25), text(9pt, fill: imgc)[$exists_pi P$ — column *meets* $P$], anchor: "west")
    line((0.8, -1.85), (1.8, -1.85), stroke: prec + 1.2pt)
    content((4.0, -1.85), text(9pt, fill: prec)[$forall_pi P$ — column *all in* $P$], anchor: "west")
  }),
  caption: [
    Each column is a fiber of $pi$, a copy of $C$. Ann's column is all filled → in $forall$;
    Bob's contains a filled dot → in $exists$ only; Cid's contains none → in neither.
  ],
)

Squashing $P$ down along the projection $pi : B times C -> B$ gives two predicates on students:

$ #text(fill: imgc)[$exists_pi P$] &= { s : exists c. thin P(s, c) } &&= {"Ann", "Bob"} #h(1.2em) & #gloss[\/\/ $s$ passed *some* course] \
  #text(fill: prec)[$forall_pi P$] &= { s : forall c. thin P(s, c) } &&= {"Ann"} & #gloss[\/\/ $s$ passed *every* course] $

= Quantifiers are the adjoints of weakening

Three functions run between $"Sub"(B)$ and $"Sub"(B times C)$. *Weakening*
$#text(fill: subc)[$pi^\#$] : "Sub"(B) -> "Sub"(B times C)$ sends $S' subset.eq B$ to
${ (s, c) : s in S' }$ #gloss[\/\/ the students $S'$, paired with every course]. $exists_pi$ and
$forall_pi$ go the other way: input a whole predicate $P$ (a set of pairs), output a predicate
on students — the course variable $c$ comes out *bound*. Binding a free variable is exactly
what a quantifier does, and these two are the left and right adjoints of weakening:

$ #text(fill: imgc)[$exists_pi P$] subset.eq S' "iff" P subset.eq pi^\# (S'), quad quad
  pi^\# (S') subset.eq P "iff" S' subset.eq #text(fill: prec)[$forall_pi P$]. $

Read the right-hand law on the picture: "every pair $(s, c)$ with $s in S'$ is a pass" iff
"every student in $S'$ passed every course" — the same sentence parsed two ways; that is all
the adjunction says.

= Any map, not just projections: quantify over the fiber

For an arbitrary map $f : A -> B$ in Set the same two adjoints of $f^\#$ exist; they quantify
over the fibers $f^(-1) (s)$:

$ #text(fill: imgc)[$f(A')$] &= { s : exists a in f^(-1) (s). thin a in A' } #h(1.2em) & #gloss[\/\/ the fiber meets $A'$] \
  #text(fill: prec)[$f^(\#\#) (A')$] &= { s : f^(-1) (s) subset.eq A' } & #gloss[\/\/ the fiber is inside $A'$] $

For $f = pi$ the fiber over $s$ is the column ${s} times C$ — the *same* copy of $C$ for every
$s$ — so "quantify over the fiber" becomes a bound variable $c$ with fixed range, the literal
first-order syntax $exists c. thin P(s, c)$; the direct image $pi$ *is* $exists_pi$ and
$pi^(\#\#)$ *is* $forall_pi$.

= §1.7: a pre-logos has ∃, a logos adds ∀

#align(center)[
  #diagram(
    spacing: (30mm, 7mm),
    node-stroke: none,
    node((0, 0), $"Sub"(A)$),
    node((1, 0), $"Sub"(B)$),
    edge((0, 0), (1, 0), text(fill: imgc)[$f "(direct image, " exists ")"$], "->", bend: 35deg,
      stroke: imgc),
    edge((1, 0), (0, 0), text(fill: subc)[$f^\#$], "->", stroke: subc),
    edge((0, 0), (1, 0), text(fill: prec)[$f^(\#\#) "(" forall ")"$], "->", bend: -35deg,
      stroke: prec),
  )
]

In any regular category the direct image is already *left* adjoint to $f^\#$ (§1.51), so every
pre-logos has $exists$. A #smallcaps[logos] (§1.7) requires each $"Sub"(A)$ to be a lattice
and $f^\#$ to have a *right* adjoint $f^(\#\#)$ — it adds $forall$. Not redundant: the old
adjunction makes $f^\#$ a right adjoint (preserves intersections), the new one makes it also a
left adjoint (preserves unions) — which is §1.711's proof that a logos is a pre-logos.

#callout(prec)[
  Pre-logos = regular logic ($exists$ only); logos = full first-order logic — and $f^(\#\#)$
  along monics gives Heyting implication in each $"Sub"(A)$ (§1.712).
]
