#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set page(width: 18cm, height: auto, margin: 1.6cm)
#set text(size: 10.5pt, font: "New Computer Modern")
#set par(justify: true)
#show raw.where(block: false): box.with(fill: luma(240), inset: (x: 2pt), outset: (y: 2pt), radius: 1pt)

#align(center)[
  #text(15pt, weight: "bold")[§1.571 — AC regular via idempotent splitting]
]

Reading of Freyd & Scedrov, _Categories and Allegories_ §1.571, with the construction drawn out.
Composition in *diagram order*: `xy` means first `x` then `y`. Companion to the Lean proof
`ac_factorization_via_idempotent` in `Freyd/S1_57.lean`, and to the pullback/equalizer background in
`Freyd/S1_57.md`.

= The claim

§1.571 gives a sufficient condition for a Cartesian category to be *AC regular* — using the
alternative definition from §1.57: _every morphism factors as a left-invertible followed by a monic_.

*Hypothesis.* For every $x : A -> B$ there is an idempotent $e : A -> A$ with

- $e^2 = e$,
- $e x = x$ #h(0.4em) (`e` fixes `x`: first `e`, then `x`), and
- *$e$ and $x$ have the same level.*

== What "level" means

The _level_ of $x$ is its *kernel pair*: the pullback of $x$ against itself. Its elements are the
pairs $(a, a')$ that $x$ merges.

#align(center)[
  #diagram(
    spacing: (14mm, 11mm),
    node-stroke: none,
    node((0, 0), $ker(x)$),
    node((2, 0), $A$),
    node((0, 1), $A$),
    node((2, 1), $B$),
    node((0.42, 0.42), text(8pt)[⌟]),                  // pullback corner
    edge((0, 0), (2, 0), $k_2$, "->"),
    edge((0, 0), (0, 1), $k_1$, "->", label-side: right),
    edge((2, 0), (2, 1), $x$, "->"),
    edge((0, 1), (2, 1), $x$, "->"),
  )
]
#align(center)[#text(9pt, style: "italic")[
  $ker(x) = {(a, a') : x a = x a'} subset.eq A times A$ — the pairs $x$ identifies.
]]

"$e$ and $x$ have the *same level*" means $ker(e) = ker(x)$ as subobjects of $A times A$: $e$ merges a
pair iff $x$ does. This is an *assumption* (Lean: both inclusions `kernelPairRel e ⊂ kernelPairRel x`
and back); the construction below _uses_ it.

= Decoding the paragraph

#quote(block: true)[
  Let $C -> A$ be an equalizer of $1, e$. Let $(A -> C -> A) = e$. Then $x = (A -> C -> A -> B)$.
  $A -> C$ has a left-inverse $(C -> A)$ and $C -> A -> B$ is monic.
]

Let $m : C -> A$ be the equalizer of $1_A$ and $e$.

== Step 1–3: split the idempotent through the equalizer

Since $e ; e = e = e ; 1$, the map $e$ _equalizes_ the parallel pair $1, e$, so it factors *uniquely*
through the equalizer $m$: there is a unique $p : A -> C$ with $p ; m = e$ (unique because $m$ is
monic).

#align(center)[
  #diagram(
    spacing: (14mm, 13mm),
    node-stroke: none,
    node((0, 0), $C$),
    node((2, 0), $A$),
    node((4, 0), $A$),
    node((2, 1), $A$),
    edge((0, 0), (2, 0), $m$, ">->"),                  // equalizer leg, monic
    node((3, 0), $+$),                                  // two distinct maps, not 1 = e
    edge((2, 0), (4, 0), $1$, "->", shift: 4pt),
    edge((2, 0), (4, 0), $e$, "->", shift: -4pt, label-side: right),
    edge((2, 1), (2, 0), $e$, "->"),                   // cone leg, vertical
    edge((2, 1), (0, 0), $p$, "-->", label-side: left),// unique mediator, dashed
  )
]
#align(center)[#text(9pt, style: "italic")[
  The apex $A$ is a cone over $1, e$ (since $e ; 1 = e = e ; e$); it factors uniquely through the
  equalizer $m$ by the dashed $p$, with $p ; m = e$.
]]

This *splits the idempotent* $e = p ; m$. Moreover $m ; p = 1_C$ — because $m ; p ; m = m ; e = m =
1 ; m$ and $m$ is monic. So *$m$ is a left-inverse of $p$* ("$A -> C$ has a left-inverse $C -> A$"),
making $p$ left-invertible (a cover). Equalizer maps are always monic (`eqMap_mono`), so $m$ is monic.

=== Left-invertible vs cover vs epic

These three "surjective-like" notions are distinct; left-invertible is the strongest, and it is the one
§1.57 demands (which is the choice content).

#align(center)[
  #table(
    columns: 4,
    align: (left, left, center, left),
    stroke: 0.5pt + luma(180),
    inset: 5pt,
    table.header([*Notion*], [*Meaning* (diagram order)], [*Splits?*], [*This, but not the next-stronger*]),
    [Epic], [$p u = p v ==> u = v$], [—], [$ZZ -> QQ$ in *Ring*: epic, yet not onto (not a cover)],
    [Cover (regular epi)], [coequalizer of its kernel pair; pullback-stable], [no], [$ZZ ->> ZZ slash 2$ in *Grp*: onto, but no section],
    [Left-invertible #linebreak() (split epi)], [has a section $m$ with $m ; p = 1$], [yes], [$A times B ->> A$ ($B$ nonempty): section $a |-> (a, b_0)$],
  )
]
#align(center)[#text(9pt, style: "italic")[
  Bottom $==>$ top: split epi $==>$ cover $==>$ epic; each implication is strict (the examples show why).
  In *Set* with choice all three coincide — that is exactly why Set is AC regular.
]]

== Step 4–5: factor $x$, and show the second leg is monic

From $e x = x$ and $e = p ; m$ we get $x = e x = p ; (m ; x)$. Set $n := m ; x$. Then $x = p ; n$ — the
required left-invertible-then-monic factorization:

#align(center)[
  #diagram(
    spacing: (16mm, 12mm),
    node-stroke: none,
    node((0, 0), $A$),
    node((2, 0), $C$),
    node((4, 0), $B$),
    edge((0, 0), (2, 0), $p$, "->>"),                       // cover / left-invertible
    edge((2, 0), (4, 0), $n = m x$, ">->"),                 // monic
    edge((0, 0), (4, 0), $x$, "->", bend: -32deg),          // composite on top
  )
]
#align(center)[#text(9pt, style: "italic")[
  $x = p ; n$ with $p$ left-invertible (a cover) and $n = m x$ monic.
]]


*Why $n = m x$ is monic* — the *only* step using "same level". First, $C$ is the *fixed points* of
$e$: as the equalizer of $1, e$ it satisfies $m ; 1 = m ; e$, i.e. *$m e = m$*.

#align(center)[
  #diagram(
    spacing: (14mm, 11mm),
    node-stroke: none,
    node((0, 0), $C$),
    node((2, 0), $A$),
    node((4, 0), $A$),
    edge((0, 0), (2, 0), $m$, ">->"),
    edge((2, 0), (4, 0), $1$, "->", shift: 4pt),
    edge((2, 0), (4, 0), $e$, "->", shift: -4pt, label-side: right),
  )
]
#align(center)[#text(9pt, style: "italic")[
  $m ; 1 = m ; e$, so $m e = m$: $e$ fixes everything in $C$.
]]

Now test $n$ against any pair $u, v : W arrows.rr C$. Since $ker(x) = ker(e)$, "$x$ merges" $=$ "$e$
merges", and $m e = m$ then strips the $e$ back off:

#align(center)[
  $ u n = v n
    &==> u m x = v m x && quad ("def. " n = m x) \
    &==> u m e = v m e && quad (ker(x) = ker(e)) \
    &==> u m = v m && quad (m e = m) \
    &==> u = v && quad (m "monic") $
]

With both legs in hand — $p$ left-invertible, $n$ monic — the category is AC regular.

