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
  title: "Slicing Keeps the Subobjects (§1.63)",
  accent: rgb("#c0392b"),
  abstract: [
    #text(12.5pt, fill: rgb("#c0392b"), style: "italic")[
      §1.63 — $Sigma : bold(A)\/B -> bold(A)$ identifies every subobject poset of the slice
      with one of $bold(A)$'s, compatibly with inverse images — so "pre-logos" passes to slices for free
    ]
  ],
)

The book's statement: for any category $bold(A)$ and object $B in bold(A)$, the forgetful functor
$Sigma : bold(A)\/B -> bold(A)$ (send a structure map $X -> B$ to plain $X$) yields an isomorphism

$ "Sub"_(bold(A)\/B)(-) #h(4pt) tilde.equiv #h(4pt) "Sub"_(bold(A))(Sigma(-)) . $

If $bold(A)$ has pullbacks, these isomorphisms respect inverse images. If $bold(A)$ has unions, so does
$bold(A)\/B$. Hence if $bold(A)$ is a pre-logos so is $bold(A)\/B$, and $Delta : bold(A) -> bold(A)\/B$
($A |-> (B times A -> B)$) is a representation of pre-logoi.

= One category, two presentations — one $Delta$, two readings (§1.544)

$bold(A)\/B$ has *one definition*: objects are *all* arrows $X -> B$, morphisms are commuting
triangles over $B$. The book presents it twice:

- *(a) plain slice* of $bold(A)$ — the form in use from §1.414 on;
- *(b) the §1.544 re-presentation*, in force from §1.544 onward — so also here in §1.63. Build the
  slice over the *inflation* $bold(A)'$ (objects are finite sequences of $bold(A)$-objects, the
  forgetful functor picks a product $A_1 times dots.c times A_n$ for each, binary product $=$
  *concatenation*), which upgrades product cancellation to strict equality:
  $B times A = B times A' => A = A'$. Then rename the image of $Delta$ to $bold(A)$ itself.

The two presentations are equivalent categories; everything true in one is true in the other — the
§1.63 iso and the concrete $#smallcaps[Set]\/B$ computation below are the same either way. The gain of
(b) is the one Freyd states in §1.544: it lets us "consider $bold(A)$ to be a *subcategory* of
$bold(A)\/B$" — the renaming makes $Delta$ injective on objects, so each $bold(A)$-object *is* an
$bold(A)\/B$-object, rather than $bold(A)$ merely mapping into $bold(A)\/B$ by a faithful functor.
(§1.545–1.546 need this: the capitalization tower is a union of subcategories.) The embedded copy
consists of the objects $Delta(A) = (B times A -> B)$ — renamed, in (b), to $A$ itself.

Likewise $Delta$ is *one functor* — $A |-> (B times A -> B)$, $f |-> 1 times f$: the diagonal of
§1.44, the right half of $(B times -) = Sigma compose Delta$ — with two readings: in (a) it is a
functor between different categories; in (b), after the renaming, the *same* functor is the
subcategory inclusion — $Delta(A)$ *is* $A$.

Neither presentation shrinks the object class: a general object of $bold(A)\/B$ is an *arbitrary*
arrow $p : X -> B$ — e.g. a proper subobject $B' arrow.r.hook B$ is a slice object whose domain is no
product $B times A$. The objects $B times A -> B$ are merely the embedded copy of $bold(A)$; the
slice is strictly larger (that properness is the engine of capitalization). The §1.63 iso quantifies
over *all* slice objects — it must, since concluding "$bold(A)\/B$ is a pre-logos" requires *every*
$"Sub"_(bold(A)\/B)(p)$ to be a lattice — which is why §§2–4 below work with a general $(X, p)$. What
presentation (b) changes is how two things must be read:

#block(width: 100%, fill: imgc.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + imgc))[
  *Reading $Delta$ correctly.* #h(3pt) $Delta$ is *not* "$X |-> (X -> B)$": it is
  $Delta(A) = (B times A -> B)$, with $Sigma(Delta(A)) = B times A$. So on the embedded copy of
  $bold(A)$ the §1.63 iso reads
  $ "Sub"_(bold(A)\/B)(Delta A) #h(4pt) tilde.equiv #h(4pt) "Sub"_(bold(A))(B times A) $
  — subobjects of $B times A$, *not* of $A$. Under this identification $Delta$ acts on subobjects by
  $A' |-> B times A'$, which is exactly $pi^(\#)$ for the projection $pi : B times A -> A$; the claim
  "$Delta$ is a representation of pre-logoi" therefore says $B times -$ preserves the lattice
  operations — $B times (A_1 union A_2) = (B times A_1) union (B times A_2)$, $B times 0 = 0$ — an
  instance of the pre-logos axiom "$f^(\#)$ is a lattice homomorphism" applied to $pi$.

  *Why the subcategory inclusion matters.* #h(3pt) §1.63 ends with: any (positive) pre-logos is
  faithfully representable in a *capital* one. That is the §1.545–1.546 ladder — iterate $Delta$ into a
  tower $bold(A) subset bold(A)^* subset bold(A)^(**) subset dots.c$ and take its *union*. A union of
  subcategories only makes sense when each rung really is a subcategory (injective on objects);
  presentation (b) is what makes it one.
]

#block(width: 100%, fill: subc.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + subc))[
  *Name clash: two "diagonals".* #h(3pt) The diagonal *functor* $Delta : bold(A) -> bold(A)\/B$ is not
  the diagonal *morphism* $chevron.l 1, 1 chevron.r : A -> A times A$ (the one §1.61 uses). They are
  related — the generic point that slicing adjoins is $chevron.l 1, 1 chevron.r : B -> B times B$
  viewed as a slice map $1 -> Delta(B)$ — but they are different things. Freyd flags the clash himself
  in §1.535: $Delta$ is only *conjugate* to the standard diagonal functor under the equivalence
  $#smallcaps[Set]\/B tilde.eq #smallcaps[Set]^B$.
]

#block(width: 100%, fill: prec.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + prec))[
  *Rule.*
  + $bold(A)\/B$ always means the full slice: objects are *all* arrows $X -> B$ — never only the
    $B times A -> B$.
  + $Delta$ is the one functor $A |-> (B times A -> B)$. From §1.544 on, read $Delta(A)$ as $A$
    itself, so that $bold(A) subset bold(A)\/B$ is a subcategory — required wherever $bold(A)$ must
    sit inside $bold(A)\/B$ (capitalization towers and their unions).
  + On subobjects: $"Sub"_(bold(A)\/B)(Delta A) = "Sub"_(bold(A))(B times A)$, and $Delta$ acts by
    $A' |-> B times A'$.
  + $Delta$ (the diagonal *functor*) is not $chevron.l 1, 1 chevron.r$ (the diagonal *morphism*).
]

= The two functors — and why the "$(-)$"

Both sides are *families of posets*, one for each object of the slice:

- $"Sub"_(bold(A)\/B)(-)$ : plug in a slice object $p : X -> B$, get the poset of its subobjects
  *computed in the slice category*;
- $"Sub"_(bold(A))(Sigma(-))$ : plug in the *same* slice object, apply $Sigma$ (throw away $p$, keep
  $X$), get the poset of subobjects of plain $X$ *computed in $bold(A)$*.

#block(width: 100%, fill: subc.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + subc))[
  *Why the placeholder $(-)$ instead of just $"Sub"_(bold(A)\/B)$?* #h(3pt) Because the isomorphism is
  between *functors*, and the two subobject functors have different domains: $"Sub"_(bold(A)\/B)$ lives
  on $bold(A)\/B$, $"Sub"_(bold(A))$ lives on $bold(A)$ — "$"Sub"_(bold(A)\/B) tilde.equiv
  "Sub"_(bold(A))$" would be ill-typed. The right-hand side is really the *composite*
  $"Sub"_(bold(A)) compose Sigma$, and $"Sub"_(bold(A))(Sigma(-))$ is how the book writes that
  composite: the $(-)$ marks where the common argument goes, with $Sigma$ inserted on one side only.
  The notation also matches how the claim unfolds: first an isomorphism of posets *at each object*
  (no pullbacks needed), then — when $bold(A)$ has pullbacks — the next sentence upgrades it to a
  *natural* isomorphism ("respect inverse images" $=$ naturality in the argument).
]

= The isomorphism, concretely

Take $bold(A) = #smallcaps[Set]$, $B = {0, 1}$. In either presentation an object of
$#smallcaps[Set]\/B$ is an arrow into $B$ — a set with a $B$-coloring: $p : X -> B$ paints every
element color $0$ or color $1$ (presentation (b) additionally embeds #smallcaps[Set] inside as the
objects $B times A -> B$). Say

#align(center)[
  #cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let c0 = subc; let c1 = prec
    let dot(p, l, col, dy) = {
      circle(p, radius: 2pt, fill: col, stroke: none)
      content((p.at(0), p.at(1) + dy), text(9pt, fill: col)[#l])
    }
    dot((-1.4, 1.5), $a$, c0, 0.32); dot((0, 1.5), $b$, c0, 0.32); dot((1.4, 1.5), $c$, c1, 0.32)
    dot((-0.7, -0.7), $0$, c0, -0.34); dot((1.4, -0.7), $1$, c1, -0.34)
    line((-1.32, 1.35), (-0.76, -0.52), mark: (end: ">"), stroke: 0.7pt + c0)
    line((-0.08, 1.35), (-0.64, -0.52), mark: (end: ">"), stroke: 0.7pt + c0)
    line((1.4, 1.35), (1.4, -0.52), mark: (end: ">"), stroke: 0.7pt + c1)
    content((3.3, 1.5), text(9pt)[$X = {a, b, c}$])
    content((3.3, -0.7), text(9pt)[$B = {0, 1}$])
    content((0.05, 0.4), text(8.5pt)[$p$])
    circle((-1.4, 1.5), radius: 5pt, stroke: (dash: "dashed", paint: imgc, thickness: 0.7pt))
    circle((1.4, 1.5), radius: 5pt, stroke: (dash: "dashed", paint: imgc, thickness: 0.7pt))
    content((0, 2.35), text(8.5pt, fill: imgc)[a subobject $X' = {a, c}$ (dashed) — coloring inherited])
  })
]

*What is a subobject of $(X, p)$ in the slice?* A monic over $B$, i.e. a commuting triangle:

#align(center)[
  #diagram(spacing: (20mm, 13mm), node-stroke: none, node-inset: 4pt,
    node((0,0), $X'$),
    node((1,0), $X$),
    node((1,1), $B$),
    edge((0,0), (1,0), ">->", stroke: 0.8pt),
    edge((1,0), (1,1), $p$, "->", label-side: left, stroke: 0.8pt),
    edge((0,0), (1,1), text(8pt, fill: imgc)[forced], "->", label-side: right, stroke: 0.8pt),
  )
]

Here is the whole point: the structure map $X' -> B$ has *no freedom* — commutativity forces it to be
the restriction of $p$ along the inclusion. So a subobject of $(X, p)$ is *just a subset of $X$*
wearing its inherited coloring — e.g. $X' = {a, c}$ with $a$ colored $0$, $c$ colored $1$:

$ "Sub"_(#smallcaps[Set]\/B)((X, p)) #h(4pt) = #h(4pt) "all" 8 "subsets of" {a, b, c} #h(4pt) =
  #h(4pt) "Sub"_(#smallcaps[Set])(X) . $

Same elements, same inclusion order — that is the isomorphism. (Behind it: a slice morphism is monic
in $bold(A)\/B$ iff its underlying $bold(A)$-map is monic, and every mono into $X$ acquires a unique
over-$B$ structure.)

#block(width: 100%, fill: subc.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + subc))[
  *What the iso does #underline[not] say.* #h(3pt) Hom-sets *do* shrink in the slice: maps
  $(X, p) -> (Y, q)$ must preserve colors, so there are far fewer of them than maps $X -> Y$. But the
  *subobjects* do not shrink at all. Slicing changes the maps, not the subobject lattices.
]

= "Respects inverse images" — naturality, concretely

For a slice morphism $f : (X, p) -> (Y, q)$ the claim is that the square

#align(center)[
  #diagram(spacing: (38mm, 13mm), node-stroke: none, node-inset: 4pt,
    node((0,0), $"Sub"_(bold(A)\/B)((Y, q))$),
    node((1,0), $"Sub"_(bold(A))(Y)$),
    node((0,1), $"Sub"_(bold(A)\/B)((X, p))$),
    node((1,1), $"Sub"_(bold(A))(X)$),
    edge((0,0), (1,0), $tilde.equiv$, "->", stroke: 0.8pt),
    edge((0,0), (0,1), text(8pt)[$f^(\#) "in" bold(A)\/B$], "->", label-side: left, stroke: 0.8pt),
    edge((1,0), (1,1), text(8pt)[$f^(\#) "in" bold(A)$], "->", label-side: right, stroke: 0.8pt),
    edge((0,1), (1,1), $tilde.equiv$, "->", stroke: 0.8pt),
  )
]

commutes. In the example: let $Y = {u, v}$ with $q : u |-> 0, v |-> 1$, and let $f$ be the
color-preserving map $a, b |-> u$, $c |-> v$. Take the subobject ${v} subset.eq Y$. Computed in the
slice or in #smallcaps[Set], $f^(\#)({v}) = {c}$ — preimage is preimage, the coloring just tags along.
Pullbacks in $bold(A)\/B$ are computed on underlying objects in $bold(A)$, so $f^(\#)$ on the two
sides of the iso is *literally the same operation*.

= Why Freyd wants this

Every axiom of "pre-logos" is a statement about subobject posets and $f^(\#)$: $"Sub"$ is a lattice,
finite unions exist, $f^(\#)$ is a lattice homomorphism. The iso says the slice has *the same*
subobject posets and *the same* $f^(\#)$ as $bold(A)$. So all those properties transfer wholesale —
$bold(A)$ pre-logos $=>$ $bold(A)\/B$ pre-logos, no new proof needed — and the diagonal
$Delta : bold(A) -> bold(A)\/B$, $A |-> (B times A -> B)$, is a representation of pre-logoi (its
subobject action $A' |-> B times A'$ is $pi^(\#)$ — see the §1.544 box above). The same transfer gives
the positive case: if $bold(A)$ is a positive pre-logos, so is $bold(A)\/B$.

It also generalizes §1.414, which was the special case "subobjects of the terminator": the terminator
of $#smallcaps[Set]\/B$ is $"id"_B$, so $"Sub"_(#smallcaps[Set]\/B)(1) = "Sub"_(#smallcaps[Set])(B)$ —
the four subsets of ${0, 1}$ are the *truth values* of $#smallcaps[Set]\/B$. One reason slices behave
like "sets varying over $B$": slicing moves $"Sub"_bold(A)(B)$ into the terminator position.

#punch[
  $Sigma$ is an isomorphism on every subobject poset, commuting with inverse images: slicing rescales
  the *maps* (color-preserving only), never the *subobject lattices*. Any property expressed purely in
  $("Sub", f^(\#))$ — lattice, finite unions, distributivity: the pre-logos axioms — therefore holds
  in $bold(A)\/B$ the moment it holds in $bold(A)$. The $(-)$ in
  $"Sub"_(bold(A)\/B)(-) tilde.equiv "Sub"_(bold(A))(Sigma(-))$ is the placeholder that makes this a
  statement about *functors* ($"Sub"_bold(A) compose Sigma$ on the right), not a single bijection.
]

= §1.631 — complemented subobjects: the complement is unique

§1.63 made every $"Sub"_(bold(A))(A)$ a *distributive* lattice, and transported that to slices. §1.631
cashes the distributivity in immediately. Call $A_1 arrow.r.hook A$ a *complemented subobject* if some
$A_2 arrow.r.hook A$ satisfies
$ A_1 inter A_2 = 0 quad "and" quad A_1 union A_2 = A . $
Freyd's remark: *the distributivity of $"Sub"(A)$ makes $A_2$, when it exists, unique.*

*Why distributivity forces it.* Suppose $A_2$ and $A_2'$ both complement $A_1$. Then
$ A_2 &= A_2 inter A = A_2 inter (A_1 union A_2') \
      &= (A_2 inter A_1) union (A_2 inter A_2') quad (star) \
      &= 0 union (A_2 inter A_2') = A_2 inter A_2' #h(3pt) subset.eq #h(3pt) A_2' , $
where $(star)$ is the distributive law $inter$-over-$union$ — the *only* nontrivial step. By symmetry
$A_2' subset.eq A_2$, so $A_2 = A_2'$. Everything rides on that one move.

*Unique, concretely.* In the Boolean algebra of subsets of ${1,2,3}$, take $A = {1,2,3}$ and
$A_1 = {1,2}$. A complement needs $A_1 inter A_2 = emptyset$ and $A_1 union A_2 = {1,2,3}$: anything
containing $1$ or $2$ overlaps $A_1$, and anything missing $3$ fails to cover — so $A_2 = {3}$ is
*forced*.

*Fails without distributivity.* The smallest non-distributive lattice is the diamond $M_3$:

#align(center)[
  #diagram(spacing: (13mm, 11mm), node-stroke: none, node-inset: 3pt,
    node((1,0), $1$, name: <one>),
    node((0,1), $a$, name: <da>),
    node((1,1), $b$, name: <db>),
    node((2,1), $c$, name: <dc>),
    node((1,2), $0$, name: <zero>),
    edge(<da>, <one>, "-", stroke: 0.7pt),
    edge(<db>, <one>, "-", stroke: 0.7pt),
    edge(<dc>, <one>, "-", stroke: 0.7pt),
    edge(<zero>, <da>, "-", stroke: 0.7pt),
    edge(<zero>, <db>, "-", stroke: 0.7pt),
    edge(<zero>, <dc>, "-", stroke: 0.7pt),
  )
]

The three middle elements are pairwise incomparable; each pair meets at $0$ and joins at $1$. So
$a inter b = 0$ and $a union b = 1$ — $b$ complements $a$ — but equally $a inter c = 0$ and
$a union c = 1$, so $c$ complements $a$ too. *$a$ has two complements.* The break is exactly the
distributive step: $a inter (b union c) = a inter 1 = a$, whereas
$(a inter b) union (a inter c) = 0 union 0 = 0$.

#block(width: 100%, fill: subc.lighten(94%), inset: 10pt, radius: 5pt, stroke: (left: 3pt + subc))[
  *No pre-logos looks like $M_3$.* #h(3pt) §1.63 (via §1.616) makes $"Sub"(A)$ *distributive* in every
  pre-logos — and, by the slice iso above, in every slice too. So the $M_3$ pathology cannot occur, and
  complements are always unique. The diamond is precisely the witness that "distributive" is
  load-bearing in §1.631, not decoration.
]

#punch[
  Uniqueness of the complement is pure lattice distributivity — no categorical input beyond
  "$"Sub"(A)$ is distributive", which §1.63 already transported to every slice. It is formalized as
  `Freyd.complement_unique` (`Fredy/S1_62.lean`), *axiom-free*: two complements of $A_1$ are shown
  mutually $subset.eq$ (hence isomorphic), from the $subset.eq$-half `complement_le_other` applied both
  ways. $M_3$ is the witness that the distributivity hypothesis does real work.
]
