#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set page(width: 18cm, height: auto, margin: 1.6cm)
#set text(size: 10.5pt, font: "New Computer Modern")
#set par(justify: true)
#show raw.where(block: false): box.with(fill: luma(240), inset: (x: 2pt), outset: (y: 2pt), radius: 1pt)

#align(center)[
  #text(15pt, weight: "bold")[§1.28 — proto-morphisms and the idempotent-splitting category]
]

Notes on Freyd & Scedrov, _Categories and Allegories_ §1.28. Composition in *diagram order*:
`Ax` means first `A` then `x`.

= What a proto-morphism is (general, §1.2)

A category can be presented by a *two-sorted theory*: one sort for *objects*, one sort for
*proto-morphisms*. A proto-morphism is a _raw arrow-datum_ — a candidate arrow that does not yet have
a fixed source/target.

What turns a proto-morphism into an actual morphism is the *source-target predicate* (a.k.a. arrow
predicate) $A arrow.r^x B$, read "$x$ may be construed as going from $A$ to $B$". The _same_
proto-morphism $x$ may satisfy that predicate for several object pairs, or for none.

The category one actually obtains (§1.22) has as its *morphisms* the _instances_ of the predicate —
triples $(A, x, B)$, not the bare $x$.

#quote(block: true)[
  proto-morphism = the underlying arrow data; morphism = that data together with a chosen source and
  target.
]

Convention: upper-case variables for objects, lower-case for proto-morphisms.

= In §1.28 (the idempotent-splitting / Karoubi category)

§1.28 builds a category out of a class $E$ of idempotents in a category $A$, presented via the
§1.2–1.22 machinery:

- *objects* = the idempotents in $E$,
- *proto-morphisms* = the morphisms of the original category $A$ (reused as raw arrows),
- *source-target predicate*: for idempotents $A, B$ (upper-case = idempotents) and a proto-morphism
  $x$,
  $ A arrow.r^x B quad <==> quad A x = x = x B. $
  In diagram order: $A ; x = x$ and $x ; B = x$ — $x$ is absorbed by $A$ on the left and by $B$ on
  the right.

So the proto-morphisms here are just *the arrows of $A$*, and the predicate $A x = x = x B$ selects
which of them count as morphisms between two idempotent-objects.

== Consequences noted in the text

- The *identity* on an object $A$ (an idempotent) is $A$ _itself_: $A dot A = A = A dot A$ makes
  $A arrow.r^A A$ hold, and $A$ acts as the identity. This is why the forgetful map back to $A$ is
  *not* generally a functor — when the idempotents are not all identities ($E subset.not |A|$) it
  fails to preserve identities.
- Each idempotent $e in E$ *splits* canonically in this category (§1.281): $e = x y$, $y x = 1$. That
  is the whole point — the Karoubi / idempotent-completion construction. (§1.282: any two splittings
  of the same idempotent are canonically isomorphic.)

= Which side is the fixed point?

It is *$x$* that is the fixed point; $A$ and $B$ are the idempotents acting _on_ it. Read
$A x = x = x B$ as two fixed-point conditions on $x$:

- $A x = x$ — $x$ is fixed by $A$ acting *on the left* (pre-composition). $A$ behaves like an identity
  for $x$ on the *source* side.
- $x B = x$ — $x$ is fixed by $B$ acting *on the right* (post-composition). $B$ behaves like an
  identity for $x$ on the *target* side.

So $x$ is a fixed point of _both_ operators "left-multiply by $A$" and "right-multiply by $B$". The
idempotents $A, B$ are the would-be identities; $x$ is the arrow they fix from either side — which is
exactly what makes $A$ the left identity (source) and $B$ the right identity (target) of $x$ in the
new category. (Saying "$A$ is $x$'s fixed point" reverses the roles: $A$ is the operator, $x$ is what
is held fixed.)

= Why this is element-free, and why that matters

The presentation is *arrows-only*: $A$ and $x$ live in the _same_ sort (proto-morphisms), so both
$A x$ and $x B$ are just composition — you can multiply on the *left* and on the *right*. If $x$ were
an _element_ of a set and $A$ a function, you would only have one-sided application $x(A)$, and there
would be no way to say "fix $x$ from the right." The two-sided absorption is only expressible because
everything is an arrow.

This is exactly why categories generalize monoids, and why objects can be *identified with their
identity arrows*: an identity is characterized purely equationally by $1 x = x = x 1$, with no
reference to what $x$ "does" to anything. Source and target are recovered as _the_ left/right
absorbing idempotents — no elements, no application.

§1.28 is the payoff of taking that seriously: since objects are just two-sided identities, any
idempotent that _acts_ like a two-sided identity ($A x = x = x B$) is allowed to _be_ an object. Drop
the requirement that identities be "the real" ones and let every idempotent in $E$ serve as an object.
The element-free formulation is what makes that move even expressible.

= Does every idempotent split? (and is splitting an AC property?)

Idempotent splitting is *not* automatic, and it has *nothing to do with AC regularity*.

An idempotent $e : A -> A$ _splits_ if there are $x : A -> B$, $y : B -> A$ with $x y = e$ and
$y x = 1_B$. A category in which all idempotents split is called *idempotent-complete*
(a.k.a. Cauchy / Karoubi complete) — a special property, not something a general category has.

The $"Split"(E)$ construction of §1.28 is exactly the device that _forces_ splitting: adjoin the
idempotents as objects, and each $e in E$ then splits canonically (§1.281). If $E$ = all idempotents,
all idempotents split in the completed category. (§1.573 does precisely this for the
primitive-recursive functions: that category lacks equalizers, so idempotents are split by hand to
build $P$.)

== But in a Cartesian category they split for free — no AC needed

*Any category with equalizers splits all of its idempotents*, and a Cartesian category has equalizers.
The construction is the one used in `ac_factorization_via_idempotent` (§1.571):

Given an idempotent $e : A -> A$, let $m : C -> A$ be the equalizer of $1_A$ and $e$. Since
$e ; e = e = e ; 1$, the map $e$ _equalizes_ the parallel pair $1, e$, hence factors *uniquely*
through the equalizer: there is a unique $p : A -> C$ with $p ; m = e$ (unique because $m$ is monic).

#align(center)[
  #diagram(
    spacing: (14mm, 13mm),
    node-stroke: none,
    node((0, 0), $C$),
    node((2, 0), $A$),
    node((4, 0), $A$),
    node((2, 1), $A$),
    // equalizer leg m : C >-> A  (monic, tailed arrow per Freyd convention)
    edge((0, 0), (2, 0), $m$, ">->"),
    // parallel pair 1, e : A => A  (straight parallel arrows, NOT curved —
    // curves would read as 1 = e; the + marks them as two distinct maps)
    node((3, 0), $+$),
    edge((2, 0), (4, 0), $1$, "->", shift: 4pt),
    edge((2, 0), (4, 0), $e$, "->", shift: -4pt, label-side: right),
    // cone leg e : A -> A  (vertical, perpendicular to m)
    edge((2, 1), (2, 0), $e$, "->"),
    // unique mediating map p (dashed)
    edge((2, 1), (0, 0), $p$, "-->", label-side: left),
  )
]

#align(center)[
  #text(9pt, style: "italic")[
    The apex $A$ is a cone over $1, e$ via the vertical leg $e$ (since $e ; 1 = e = e ; e$); it factors
    uniquely through the equalizer $m$ by the dashed $p$, with $p ; m = e$.
  ]
]

Then

- $m ; p = 1_C$ #h(0.5em) (because $m ; p ; m = m ; e = m = 1 ; m$ and $m$ is monic), and
- $p ; m = e$.

So $e$ splits as $(p, m)$, with $p$ left-invertible. *This uses only the equalizer, i.e.
Cartesianness — no AC, no "same level".* And an equalizer _is a limit_ (of the parallel-pair diagram
$A arrows.rr A$), so this comes packaged with the finite-limit structure of a Cartesian category.

== Where AC actually comes in

Splitting alone gives the _left-invertible_ leg $p$. Being *AC regular* (§1.57) is stronger: _every_
morphism must factor as left-invertible $;$ *monic*. The §1.571 hypothesis (an idempotent $e$ with
$e x = x$ _and the same level as $x$_) is what upgrades "idempotents split" to "AC regular": the
splitting handles $p$, and the same-level condition is the extra ingredient forcing the second leg
$n = m ; x$ to be *monic* (see `Freyd/S1_57.md`).

#table(
  columns: 2,
  stroke: 0.5pt + luma(180),
  inset: 6pt,
  table.header([*Property*], [*What it needs*]),
  [Every idempotent splits], [equalizers ($arrow.l.double$ Cartesian), or do §1.28's $"Split"(E)$ by hand],
  [AC regular], [the above *plus* §1.571's same-level idempotents (the AC content)],
)
