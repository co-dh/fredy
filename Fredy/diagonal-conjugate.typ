#import "@preview/cetz:0.3.4"
#set page(width: 18cm, height: auto, margin: 18pt, fill: white)
#set text(font: "New Computer Modern", size: 11pt)

#let red  = rgb("#c0392b")
#let blue = rgb("#1457a6")
#let grn  = rgb("#0a7d3f")

// inline shapes for the elements, so prose/cells match the drawn figure exactly
#let RD = box(baseline: 1.5pt, circle(radius: 2.6pt, fill: red,  stroke: none))   // a ∈ A
#let BT = box(baseline: 0.5pt, polygon.regular(size: 7pt, vertices: 3, fill: blue, stroke: none)) // a' ∈ A
#let GS = box(baseline: 1pt,   rect(width: 4.8pt, height: 4.8pt, fill: grn, stroke: none))        // ∈ A'

// the same shapes inside a cetz canvas
#let rdot(x, y) = cetz.draw.circle((x, y), radius: 0.12, fill: red, stroke: none)
#let btri(x, y) = cetz.draw.line((x - 0.14, y - 0.10), (x + 0.14, y - 0.10),
                                 (x, y + 0.17), close: true, fill: blue, stroke: none)

#align(center, text(14pt, weight: "bold")[
  Why Freyd's #math.Delta is *conjugate* to the standard diagonal
])
#align(center, text(10.5pt)[
  A set #box[$B = {1, 2, 3}$], and a set #box[$A$] with two elements #RD and #BT.
])

#v(6pt)

#align(center, cetz.canvas(length: 1cm, {
  import cetz.draw: *

  // one "copy of A" box : header + the two elements (no base)
  let copybox(cx, header, hfill) = {
    rect((cx - 0.42, 1.15), (cx + 0.42, 2.75), radius: 4pt, stroke: 0.7pt + luma(130))
    content((cx, 3.02), text(8.5pt, fill: hfill)[#header])
    rdot(cx, 2.18)
    btri(cx, 1.55)
  }

  // ===== GROUP 1 : the slice object  B×A → B  (a bundle over B) =====
  let g1 = (0, 0.95, 1.9)
  for (i, cx) in g1.enumerate() {
    copybox(cx, [{#(i + 1)}×A], red)            // fiber over i+1  =  {i+1}×A
    circle((cx, 0), radius: 0.05, fill: black)  // base point i+1
    content((cx, -0.34), text(9pt)[#(i + 1)])
    line((cx, 1.05), (cx, 0.18), mark: (end: ">"), stroke: 0.6pt)   // projection π
  }
  content((0.62, 0.6), text(8pt)[#math.pi])
  content((0.95, -0.85), text(10pt)[base $B$])
  content((0.95, 3.42), text(9pt, fill: red)[the bundle $B times A -> B$])

  // arrow 1 :  canonical equivalence  S/B ≃ S^B  (read off the fibers)
  line((2.55, 1.95), (3.65, 1.95), mark: (end: ">"), stroke: 0.8pt)
  content((3.1, 2.35), text(8.5pt)[take fibers])
  content((3.1, 1.55), text(8.5pt)[$cal(S)\/B tilde.equiv cal(S)^B$])

  // ===== GROUP 2 : the tuple of fibers — TAGGED copies =====
  let g2 = (4.1, 5.05, 6.0)
  for (i, cx) in g2.enumerate() { copybox(cx, [{#(i + 1)}×A], red) }
  content((5.05, 0.4), text(9pt, fill: red)[({1}×A,#h(2pt) {2}×A,#h(2pt) {3}×A)])
  content((5.05, -0.05), text(8pt, fill: red)[copies of $A$, each *tagged* by $i$])

  // arrow 2 :  the natural iso η = forget the tag   (b,x) ↦ x
  line((6.7, 1.95), (8.0, 1.95), mark: (end: ">"), stroke: 1pt + grn)
  content((7.35, 2.45), text(9pt, fill: grn, weight: "bold")[$eta$: forget tag])
  content((7.35, 1.5), text(8.5pt, fill: grn)[$(b, x) |-> x$])

  // ===== GROUP 3 : the standard diagonal — UNTAGGED =====
  let g3 = (8.7, 9.65, 10.6)
  for (i, cx) in g3.enumerate() { copybox(cx, [A], grn) }
  content((9.65, 0.4), text(9pt, fill: grn)[($A$,#h(2pt) $A$,#h(2pt) $A$)])
  content((9.65, -0.05), text(8pt, fill: grn)[bare copies of $A$, *no tag*])
  content((9.65, 3.42), text(9pt, fill: grn)[standard diagonal $D(A)$])
}))

#v(2pt)
#align(center, box(width: 88%, text(10pt)[
  Groups 2 and 3 are the *same picture* — three copies of $A$ — differing only by the header tag.
  The bijection that forgets the tag, #box[$(b,x) |-> x$], is the isomorphism. That is all "#text(grn)[conjugate]"
  means here: Freyd's #math.Delta lands on $A$ *labelled by its base point*, the standard diagonal lands on
  $A$ *plain*, and stripping the label is an iso.
]))

#v(10pt)
#line(length: 88%, stroke: 0.4pt + luma(200))
#v(4pt)

#align(center, text(11pt, weight: "bold")[…and the iso is *natural* — so it really is conjugate])
#align(center, text(10pt)[
  Zoom into the fiber over $1$. Hit $A$ with any map #box[$g: A -> A'$], say #box[$A' = {#GS}$], #box[$g$] collapsing both #RD #BT to #GS.
])

#v(6pt)

#align(center, cetz.canvas(length: 1cm, {
  import cetz.draw: *
  let cell(cx, cy, body) = {
    rect((cx - 1.15, cy - 0.42), (cx + 1.15, cy + 0.42), radius: 3pt, stroke: 0.6pt + luma(150))
    content((cx, cy), text(9.5pt)[#body])
  }
  cell(0,   2, [{(1,#RD), (1,#BT)}])     // {1}×A
  cell(4.6, 2, [{#RD, #BT} = $A$])       // A
  cell(0,   0, [{(1,#GS)}])              // {1}×A'
  cell(4.6, 0, [{#GS} = $A'$])           // A'
  // top / bottom : η = forget tag
  line((1.2, 2), (3.45, 2), mark: (end: ">"), stroke: 1pt + grn)
  content((2.3, 2.34), text(8.5pt, fill: grn)[$(1,x) |-> x$])
  line((1.2, 0), (3.45, 0), mark: (end: ">"), stroke: 1pt + grn)
  content((2.3, 0.34), text(8.5pt, fill: grn)[$(1,x) |-> x$])
  // left : Δ(g) = 1×g     right : D(g) = g
  line((0, 1.55), (0, 0.45), mark: (end: ">"), stroke: 0.8pt)
  content((0.12, 1), text(8.5pt)[$1 times g$], anchor: "west")
  line((4.6, 1.55), (4.6, 0.45), mark: (end: ">"), stroke: 0.8pt)
  content((4.72, 1), text(8.5pt)[$g$], anchor: "west")
  content((2.3, 1), text(15pt, fill: grn)[#sym.checkmark])
}))

#v(4pt)
#align(center, box(width: 88%, text(10pt)[
  Both ways around send #box[$(1, x) |-> g x$]: #math.Delta acts *inside* the fiber and never touches the
  tag $1$, the diagonal acts in the slot — so forgetting-the-tag commutes with $g$. The same square holds
  over every base point. A tag-forgetting bijection that commutes with all maps *is* a natural isomorphism —
  i.e. Freyd's #math.Delta is conjugate to the standard diagonal.
]))

#pagebreak()

#align(center, text(14pt, weight: "bold")[The four functors, precisely])
#v(1pt)
#align(center, text(10pt, fill: luma(90))[running example: $B = {1, 2, 3}$, and $A$ any set])
#v(7pt)

#align(center, table(
  columns: (1.7fr, 2.1fr, 2.1fr),
  inset: 8pt,
  align: (left + horizon, left + horizon, left + horizon),
  stroke: 0.4pt + luma(205),
  fill: (_, row) => if row == 0 { luma(236) },
  table.header(
    text(10.5pt)[*functor*], text(10.5pt)[*sends an object to*], text(10.5pt)[*sends a map $g: A -> A'$ to*]),

  [#text(grn, weight: "bold")[$D$] : standard diagonal \ $cal(S) -> cal(S)^B$],
  [the constant family $(A)_(b in B)$ \ i.e. $(A, #h(1pt) A, #h(1pt) A)$],
  [the same $g$ in every slot \ $(g)_(b in B)$, i.e. $(g, #h(1pt) g, #h(1pt) g)$],

  [#text(red, weight: "bold")[$Delta$] : Freyd's diagonal \ $cal(S) -> cal(S)\/B$],
  [the projection \ $pi : B times A -> B$],
  [$1_B times g$ \ #text(9pt)[(a map $B times A -> B times A'$ over $B$)]],

  [#text(blue, weight: "bold")[$E$] : take fibers \ $cal(S)\/B -> cal(S)^B$ \ #text(8.5pt, fill: luma(90))[the canonical equivalence]],
  [$(f : X -> B) |-> (f^(-1)(b))_(b in B)$ \ the tuple of fibers],
  [restrict $h : X -> X'$ to each fiber],

  [#text(blue, weight: "bold")[$F$] : glue \ $cal(S)^B -> cal(S)\/B$ \ #text(8.5pt, fill: luma(90))[the inverse of $E$]],
  [$(X_b)_(b in B) |-> (product.co_b X_b -> B)$ \ disjoint union over $B$],
  [act on each piece of the $product.co$],
))

#v(9pt)
#align(center, box(width: 92%, fill: rgb("#fff8e6"), inset: 10pt, radius: 5pt, stroke: (left: 3pt + rgb("#d4a017")), text(10.5pt)[
  #text(weight: "bold")[Watch the types.] #h(2pt) $D$ and $Delta$ #emph[both start at] $cal(S)$
  — $D: cal(S) -> cal(S)^B$ and $Delta: cal(S) -> cal(S)\/B$. They run in #emph[parallel]; they are not a
  forward/back pair. So #emph[neither] $D compose Delta$ #emph[nor] $Delta compose D$ is defined (each
  needs the other's target as its source, and both targets differ from $cal(S)$). The single fact relating
  them is #h(3pt) #box[$E compose Delta #h(2pt) tilde.equiv #h(2pt) D$] #h(3pt) — that is the entire top row of page 1.
]))

#v(12pt)
#line(length: 92%, stroke: 0.5pt + luma(185))
#v(3pt)
#align(center, text(13.5pt, weight: "bold")[The two composites that #emph[are] Id (up to iso)])
#align(center, text(10.5pt)[
  These are the round-trips of the equivalence $cal(S)\/B tilde.equiv cal(S)^B$ — between #text(blue)[$E$] and
  #text(blue)[$F$], #emph[not] between $D$ and $Delta$. Here a #emph[general] bundle (fibers of sizes $2,1,3$):
])
#v(6pt)

#align(center, cetz.canvas(length: 0.95cm, {
  import cetz.draw: *
  let sizes = (2, 1, 3)
  // one "bundle / family" slab of three fibers; base+π optional
  let slab(ox, withbase, hdr, hcol) = {
    for (i, n) in sizes.enumerate() {
      let cx = ox + i * 0.85
      rect((cx - 0.3, 0.8), (cx + 0.3, 2.5), radius: 3pt, stroke: 0.6pt + luma(150))
      for k in range(n) { circle((cx, 1.12 + 0.38 * k), radius: 0.082, fill: black, stroke: none) }
      if withbase {
        circle((cx, 0.05), radius: 0.045, fill: black)
        content((cx, -0.24), text(8pt)[#(i + 1)])
        line((cx, 0.72), (cx, 0.22), mark: (end: ">"), stroke: 0.5pt)
      }
    }
    content((ox + 0.85, 2.82), text(8.5pt, fill: hcol)[#hdr])
  }
  slab(0, true, [$X -> B$ #h(2pt) (object of $cal(S)\/B$)], black)
  // E : fibers
  line((2.35, 1.45), (3.25, 1.45), mark: (end: ">"), stroke: 0.9pt + blue)
  content((2.8, 1.78), text(8pt, fill: blue)[$E$: cut])
  // family in S^B (no base)
  slab(3.7, false, [$(X_1, X_2, X_3)$], red)
  // F : glue
  line((6.05, 1.45), (6.95, 1.45), mark: (end: ">"), stroke: 0.9pt + blue)
  content((6.5, 1.78), text(8pt, fill: blue)[$F$: glue])
  content((6.5, 1.12), text(9pt, fill: blue)[$product.co$])
  // glued back
  slab(7.4, true, [$product.co_b X_b -> B$], black)
  content((9.9, 1.45), text(12pt)[$tilde.equiv space X$])
}))

#v(6pt)
#align(center, box(width: 92%, text(10pt)[
  #text(grn, weight: "bold")[$F compose E tilde.equiv$ Id] on $cal(S)\/B$ #emph[(drawn)]: cut a bundle
  $X -> B$ into its fibers, then glue them back by disjoint union — you get $X -> B$ again. #linebreak()
  #text(grn, weight: "bold")[$E compose F tilde.equiv$ Id] on $cal(S)^B$: glue a family $(X_b)$ into a
  total space, then re-cut into fibers — you get $(X_b)$ again. #linebreak()
  Each round-trip is the identity #emph[only up to] the same tag-forgetting iso $(b, x) |-> x$: the glued
  set $product.co_b f^(-1)(b)$ is the set of #emph[pairs] $(b, x)$, isomorphic but not equal to $X$. That
  "up to iso, not on the nose" is exactly why $cal(S)\/B$ and $cal(S)^B$ are #text(weight: "bold")[equivalent]
  but not #text(weight: "bold")[isomorphic] categories — and #math.Delta becoming $D$ on page 1 is the same
  bookkeeping, restricted to the special bundles $B times A -> B$.
]))
