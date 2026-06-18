#import "@preview/dvdtyp:1.0.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let idc = rgb("#0a7d3f")   // identity entries / injections ι (green)
#let zec = rgb("#c0641b")   // zero morphisms (amber)
#let proj = rgb("#1457a6")  // projections π (blue)
#let vcol = rgb("#c0392b")  // the map v (red)
#let id(x) = text(fill: idc, $#x$)
#let ze(x) = text(fill: zec, $#x$)
#let caution(body) = block(width: 100%, fill: rgb("#fff6ec"), inset: 11pt,
  radius: (right: 5pt), stroke: (left: 3pt + zec),
  [#text(weight: "bold", fill: zec)[△ Zero morphism]#v(3pt)#body])

#show: dvdtyp.with(
  title: "Why A ⊕ B is a Biproduct",
  author: "notes on Freyd & Scedrov, Categories · Allegories",
  accent: rgb("#1457a6"),
  abstract: [
    #text(12.5pt, fill: rgb("#1457a6"), style: "italic")[
      §1.591 — finite products and coproducts coincide in an abelian category
    ]
    #v(10pt)
    In any *bicartesian* category a map from a coproduct to a product is a $2 times 2$ matrix of
    hom-set elements. In an *abelian* category the canonical comparison map $u : A + B -> A times B$
    becomes an *isomorphism*. Its inverse is *not* a matrix — it must be built from the addition on
    hom-sets, $v = pi_A iota_A + pi_B iota_B$. We construct $v$, verify $u v = 1$ and $v u = 1$, and
    watch the whole thing degenerate in #smallcaps[Set].
  ],
)

#remark("Conventions (Freyd)")[
  Coproduct injections $iota_A : A -> A+B$, $iota_B : B -> A+B$; product
  projections $pi_A : A times B -> A$, $pi_B : A times B -> B$. The hom-set
  $(A,B) = {"morphisms " A -> B}$.
]

= The 2×2 matrix

A morphism *out of a coproduct* is one map per summand; a morphism *into a product* is one map per
factor. Stacking the two universal properties, a single morphism is determined by four free
morphisms.

#definition("Matrix of a map sum → product")[
  In any bicartesian category a morphism $f : A_1 + A_2 -> B_1 times B_2$ is *uniquely* described by
  $ f quad "is" quad mat(f_(1 1), f_(1 2); f_(2 1), f_(2 2)), wide
    f_(i j) = iota_i thin f thin pi_j thick in thick (A_i, B_j). $
  The four entries are *unconstrained* hom-set elements. This much holds in #smallcaps[Set] too.
]

= The canonical comparison map

Specialise to $A_1 = B_1 = A$ and $A_2 = B_2 = B$. The *canonical map* $u : A + B -> A times B$ is
the one carrying the identity pattern:
$ u quad "is" quad mat(1_A, 0; 0, 1_B), $
that is, the four equations
$ iota_A u pi_A = 1_A, & wide iota_A u pi_B = 0, \
  iota_B u pi_A = 0,   & wide iota_B u pi_B = 1_B. $

#caution[
  The off-diagonal #ze($0$) is the *zero morphism* — the unique map through the zero object,
  $0_(A,B) : A -> 0 -> B$.   
]

= The inverse is not a matrix

The matrix trick described maps *sum $->$ product*. The inverse runs the other way,
$v : A times B -> A + B$ — *out of a product, into a sum* — and *neither* direction has a
componentwise universal property. So $v$ cannot be read off a matrix; it must be *built*, using the
*addition on hom-sets* that an abelian category provides.

#definition("The inverse, built with +")[
  $ v := pi_A iota_A + pi_B iota_B quad in quad (A times B, thin A + B). $
  Here $pi_A iota_A$ and $pi_B iota_B$ are two morphisms $A times B -> A+B$, summed in the abelian
  group $(A times B, A+B)$. *This step is impossible in #smallcaps[Set]* — functions don't add.
]

#align(center)[
  #diagram(
    spacing: (24mm, 13mm),
    node-stroke: none,
    node-inset: 4pt,
    node((0, 0), $A times B$),
    node((1, -1), $A$),
    node((1, 1), $B$),
    node((2, 0), $A + B$),
    edge((0, 0), (1, -1), text(fill: proj)[$pi_A$], "->", stroke: 0.8pt + proj),
    edge((0, 0), (1, 1),  text(fill: proj)[$pi_B$], "->", stroke: 0.8pt + proj, label-side: right),
    edge((1, -1), (2, 0), text(fill: idc)[$iota_A$], "->", stroke: 0.8pt + idc),
    edge((1, 1), (2, 0),  text(fill: idc)[$iota_B$], "->", stroke: 0.8pt + idc, label-side: left),
    edge((0, 0), (2, 0), text(fill: vcol, weight: "bold")[$v$], "-->",
      stroke: 1.1pt + vcol, label-sep: 2pt),
  )
  #v(1mm)
  #text(9.5pt, fill: vcol)[
    $ v thick = thick underbrace(pi_A iota_A, "top path") thick + thick underbrace(pi_B iota_B, "bottom path") $
  ]
]

Each summand is one corner trip — out along a projection $pi$ (blue), in along an injection
$iota$ (green) — and the two trips are *added* (red) in the hom-group.

= u is an isomorphism

#theorem("Biproduct")[
  In an abelian category the canonical map $u : A + B -> A times B$ is an isomorphism, with inverse
  $v = pi_A iota_A + pi_B iota_B$. Hence finite products and coproducts coincide.
]

Both round trips collapse on *one* picture: the biproduct diamond carrying both $u$ and $v$.
Composition is bilinear, and the corner relations $iota_i u pi_j = 1$ if $i=j$, else $0$ (the matrix
of $u$) do all the work. We draw it twice — each time with the composite's *start* object on the left.

*Proof that $u v = 1_(A+B)$* — out of $A+B$, restrict along the injections $iota_A, iota_B$.
#v(1mm)
#align(center)[
  #diagram(spacing: (26mm, 14mm), node-stroke: none, node-inset: 4pt,
    node((0, 0), $A + B$), node((2, 0), $A times B$), node((1, -1), $A$), node((1, 1), $B$),
    edge((0, 0), (2, 0), text(fill: vcol, weight: "bold")[$u$], "->", stroke: 1pt + vcol, shift: 6pt),
    edge((2, 0), (0, 0), text(fill: vcol, weight: "bold")[$v$], "->", stroke: 1pt + vcol, shift: 6pt),
    edge((1, -1), (0, 0), text(fill: idc)[$iota_A$], "->", stroke: 0.7pt + idc),
    edge((1, 1), (0, 0),  text(fill: idc)[$iota_B$], "->", stroke: 0.7pt + idc, label-side: right),
    edge((2, 0), (1, -1), text(fill: proj)[$pi_A$], "->", stroke: 0.7pt + proj),
    edge((2, 0), (1, 1),  text(fill: proj)[$pi_B$], "->", stroke: 0.7pt + proj, label-side: left),
  )
]
#v(0.5mm)
Going $iota_A -> u$ lands in $A times B$ with coordinates $iota_A u pi_A = 1_A$ (top loop) and
$iota_A u pi_B = 0$ (crossing); then $v = pi_A iota_A + pi_B iota_B$ reassembles them:
$ iota_A u v = (iota_A u pi_A) iota_A + (iota_A u pi_B) iota_B = 1_A thin iota_A + 0 = iota_A, $
and likewise $iota_B u v = iota_B$. A map out of $A+B$ agreeing with $1$ on both injections *is* $1$.

*Proof that $v u = 1_(A times B)$* — into $A times B$, read coordinates along $pi_A, pi_B$.
The same diamond, now $A times B$ on the left so the trip $v -> u$ starts there:
#v(1mm)
#align(center)[
  #diagram(spacing: (26mm, 14mm), node-stroke: none, node-inset: 4pt,
    node((0, 0), $A times B$), node((2, 0), $A + B$), node((1, -1), $A$), node((1, 1), $B$),
    edge((0, 0), (2, 0), text(fill: vcol, weight: "bold")[$v$], "->", stroke: 1pt + vcol, shift: 6pt),
    edge((2, 0), (0, 0), text(fill: vcol, weight: "bold")[$u$], "->", stroke: 1pt + vcol, shift: 6pt),
    edge((0, 0), (1, -1), text(fill: proj)[$pi_A$], "->", stroke: 0.7pt + proj),
    edge((0, 0), (1, 1),  text(fill: proj)[$pi_B$], "->", stroke: 0.7pt + proj, label-side: right),
    edge((1, -1), (2, 0), text(fill: idc)[$iota_A$], "->", stroke: 0.7pt + idc),
    edge((1, 1), (2, 0),  text(fill: idc)[$iota_B$], "->", stroke: 0.7pt + idc, label-side: left),
  )
]
#v(0.5mm)
Expanding $v = pi_A iota_A + pi_B iota_B$ and using $iota_i u pi_j in {1, 0}$:
$ v u pi_A = pi_A (iota_A u pi_A) + pi_B (iota_B u pi_A) = pi_A thin 1_A + pi_B thin 0 = pi_A, $
and likewise $v u pi_B = pi_B$. A map into $A times B$ agreeing with $1$ on both projections *is* $1$.
Hence $u$ is an isomorphism. #h(1fr) $square$

= Concrete picture in Ab

#example[
  In abelian groups both $A+B$ and $A times B$ have the same underlying set
  $A plus.o B = {(a,b)}$, with
  $ iota_A : a |-> (a, 0_B), wide iota_B : b |-> (0_A, b), wide
    pi_A : (a,b) |-> a, wide pi_B : (a,b) |-> b. $
  The inverse *reassembles* a pair by adding its two one-sided pieces:
  $ v(a,b) = underbrace((pi_A iota_A)(a,b), iota_A (a)) + underbrace((pi_B iota_B)(a,b), iota_B (b))
           = (a, 0_B) + (0_A, b) = (a,b). $
  That single $+$ is the *group operation* of $A plus.o B$ — the abelian structure doing the work
  the universal properties cannot.

  The map $0 -> B$ sends the one element of the trivial group $0 = {0}$ to $B$'s identity $0_B$
  (homomorphisms preserve identities), so the zero morphism $A -> 0 -> B$ is the constant map
  $a |-> 0_B$.
]

= Why the coproduct lands on the same set

The product $A times B = {(a,b)}$ is the usual Set product. The surprise is that the *coproduct* is
the *same* set. By definition $A+B$ is a coproduct iff for every pair of homomorphisms $f : A -> C$,
$g : B -> C$ there is a *unique* $h : A+B -> C$ with $h iota_A = f$ and $h iota_B = g$:

#v(1mm)
#align(center)[
  #diagram(spacing: (22mm, 15mm), node-stroke: none, node-inset: 4pt,
    node((0, 0), $A$), node((2, 0), $B$), node((1, 1), $A + B$), node((1, 2.3), $C$),
    edge((0, 0), (1, 1), text(fill: idc)[$iota_A$], "->", stroke: 0.8pt + idc),
    edge((2, 0), (1, 1), text(fill: idc)[$iota_B$], "->", stroke: 0.8pt + idc, label-side: left),
    edge((1, 1), (1, 2.3), text(fill: vcol, weight: "bold")[$h$ (unique)], "-->", stroke: 1pt + vcol),
    edge((0, 0), (1, 2.3), $f$, "->", bend: -38deg),
    edge((2, 0), (1, 2.3), $g$, "->", bend: 38deg),
  )
]
#v(0.5mm)

*$h$ is forced.* Since $(a,b) = iota_A (a) + iota_B (b) = (a,0) + (0,b)$, any such $h$ obeys
$ h(a,b) = h iota_A (a) + h iota_B (b) = f(a) + g(b). $
*$h$ is a homomorphism — but only because $C$ is abelian.* Respecting $+$ means
$ h((a,b)+(a',b')) = f(a+a') + g(b+b') = f(a) + f(a') + g(b) + g(b') $
must equal $h(a,b) + h(a',b') = f(a) + g(b) + f(a') + g(b')$ — and it does *only* after swapping
$g(b)$ past $f(a')$, i.e. using commutativity of $C$. In a non-abelian target this fails and the
coproduct balloons into the free product $A * B$; abelianness is exactly what collapses $A+B$ back
onto the product set ${(a,b)}$, with $iota_A (a) = (a, 0_B)$, $iota_B (b) = (0_A, b)$.

#theorem("Punchline")[
  In #smallcaps[Set] you cannot add $(a, 0_B)$ to $(0_A, b)$, there is no zero object, and
  $ |A+B| = |A| + |B| quad eq.not quad |A| dot |B| = |A times B|. $
  Sums and products genuinely differ. In an abelian category the hom-sets are abelian groups, the
  inverse $v = pi_A iota_A + pi_B iota_B$ exists, and $A + B tilde.equiv A times B$: the *biproduct*
  $A plus.o B$.
]
