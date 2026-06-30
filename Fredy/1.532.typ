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
  title: "§1.532 — why B×A₁ is the pullback of x along the projection",
  subtitle: "Freyd & Scedrov, §1.532 — and why (B×−) preserves covers",
  author: none,
  accent: subc,
  abstract: [
    #text(11pt, fill: subc, style: "italic")[
      §1.532 needs the functor $B times (-)$ to preserve covers. The key: the square
      $B times A_1 -> B times A_2 -> A_2 <- A_1$ is a pullback in any category with binary
      products, and in a pre-regular category covers are stable under pullback. So a cover
      $x$ pulls back to the cover $1 times x$.
    ]
  ],
)

= The pullback square

The following square commutes and is a pullback in any category with binary products.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    // nodes: top-left B×A₁, top-right B×A₂, bottom-left A₁, bottom-right A₂
    content((0.3, 2.8), $B times A_1$)
    content((5.7, 2.8), $B times A_2$)
    content((0.3, 0),   $A_1$)
    content((5.7, 0),   $A_2$)
    // top arrow: 1×x
    line((1.4, 2.8), (4.5, 2.8), mark: (end: ">"), stroke: 1pt)
    content((2.95, 3.13), text(9pt)[$1 times x$])
    // bottom arrow: x
    line((0.65, 0), (5.35, 0), mark: (end: ">"), stroke: 1pt)
    content((2.95, 0.30), text(9pt)[$x$])
    // left vertical: π
    line((0.3, 2.50), (0.3, 0.30), mark: (end: ">"), stroke: 1pt)
    content((-0.25, 1.40), text(9pt)[$pi$])
    // right vertical: π
    line((5.7, 2.50), (5.7, 0.30), mark: (end: ">"), stroke: 1pt)
    content((6.20, 1.40), text(9pt)[$pi$])
  }),
  caption: [
    The pullback square. $pi$ is the projection onto the $A$-factor (i.e. `fst`, dropping $B$).
    Commutativity in diagram order: $(1 times x) pi = pi x$ — both extract the $A$-component
    and then apply $x$.
  ],
)

The cospan whose pullback this computes — the two arrows into the shared corner $A_2$:
$ A_1 arrow.r^x A_2 arrow.l^(pi) B times A_2 . $

= Why $B times A_1$ is the pullback, not just a product

A pullback in $bold("Set")$ is a subset of a product cut out by an equation. At first glance
$B times A_1$ looks like a plain product with no equation in sight. The resolution: *it is* that
subset — the equation just happens to determine one coordinate completely, so the constrained
set collapses back to a product.

Concretely, the pullback of the cospan above is:
$ P = { (a_1, (b, a_2)) in A_1 times (B times A_2) mid(|) x(a_1) = a_2 } . $

The equation $x(a_1) = a_2$ *determines* $a_2$ from $a_1$: once $a_1$ is chosen, $a_2$ is
forced to be $x(a_1)$, carrying no extra information. The genuinely free data is the pair
$(b, a_1)$. Hence
$ P ≅ B times A_1 , $
via the bijection $(a_1, (b, a_2)) arrow.r.bar (b, a_1)$, with inverse
$(b, a_1) arrow.r.bar (a_1, (b, x(a_1)))$.

So $B times A_1$ is not "a product *instead of* a pullback" — it *is* the pullback, written
without the now-redundant coordinate $a_2$.

#callout(subc)[
  *Slogan.* Pulling back along a projection just carries the constant factor through.
  $B times A_2$ is $B$ base-changed from $1$ up to $A_2$; base-changing once more along
  $x : A_1 -> A_2$ gives $B$ over $A_1$, i.e. $B times A_1$. Pasting those two pullbacks
  produces this square.
]

= $(B times -)$ preserves covers

#punch[
  In a pre-regular category, covers are stable under pullback. The square above exhibits
  $1 times x$ as the pullback of $x$ along $pi$. Therefore: if $x : A_1 -> A_2$ is a cover,
  then $1 times x : B times A_1 -> B times A_2$ is a cover (it is the pullback of a cover).
  So the functor $(B times -)$ preserves covers, and hence `Δ : A → A/B`, defined by
  $X arrow.r.bar (X times B arrow.r^"snd" B)$, preserves covers too.
]
