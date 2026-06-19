#import "@preview/dvdtyp:1.0.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let subc  = rgb("#1457a6")  // a chosen subset S (blue)
#let imgc  = rgb("#c0392b")  // the image / ∃_f (red)
#let prec  = rgb("#0a7d3f")  // the preimage / f# (green)
#let dot(c) = box(circle(radius: 2pt, fill: c, stroke: none))
#let S(x)  = text(fill: subc, $#x$)
#let Im(x) = text(fill: imgc, $#x$)
#let xarrow(t) = math.attach(math.arrow.r.long, t: t)
#let punch(body) = block(width: 100%, fill: rgb("#fdecea"), inset: 11pt,
  radius: (right: 5pt), stroke: (left: 3pt + imgc),
  [#text(weight: "bold", fill: imgc)[★ Punchline]#v(3pt)#body])

#show: dvdtyp.with(
  title: "∃ is the Image",
  author: "notes on Freyd & Scedrov, Categories · Allegories",
  accent: rgb("#c0392b"),
  abstract: [
    #text(12.5pt, fill: rgb("#c0392b"), style: "italic")[
      The existential quantifier as direct image — §1.451 (inverse image), §1.6 (pre-logos)
    ]
    #v(10pt)
    Fix a map $f : A -> B$. It carries subsets *forward* (direct image $exists_f$) and *backward*
    (inverse image $f^\#$); the forward one *is* the existential quantifier. We watch this in
    #smallcaps[Set] element by element, see why projection gives $exists y$, and read off the
    adjunction $exists_f tack.r.double f^\#$.
  ],
)

#remark("Setup")[
  $f : A -> B$ a map. A *subset* $S subset.eq A$ is a unary predicate on $A$. Composition is written
  in *diagram order*: $S arrow.r.hook A xarrow(f) B$ means "first include $S$, then apply $f$".
  In #smallcaps[Set] the operative element rule is: apply $f$ to each element.
]

= Direct image, element by element

#definition([Direct image $exists_f$])[
  For $S subset.eq A$,
  $ exists_f (S) quad = quad f(S) quad = quad { thin b in B thick | thick exists a in S. thin f(a) = b thin }. $
  The "$exists a$" is *literally in the definition*: one element of $S$ landing on $b$ is enough.
]

$b$ lies in $exists_f (S)$ iff its *fibre* $f^(-1)(b)$ *meets* $S$. Below, $S = $ #text(fill: subc, $\{a_1, a_2\}$) is the blue circle.

#align(center)[
  #diagram(spacing: (42mm, 8.5mm), node-inset: 2pt, node-stroke: none,
    // domain A — label sits right beside its dot (dot faces B)
    node((0,0), [$a_1$ #h(3pt) #dot(subc)]),
    node((0,1), [$a_2$ #h(3pt) #dot(subc)]),
    node((0,2), [$a_3$ #h(3pt) #dot(black)]),
    node((0,3), [$a_4$ #h(3pt) #dot(black)]),
    // S = circle around a1, a2 only
    node(enclose: ((0,0),(0,1)), stroke: 1pt + subc, inset: 6pt, corner-radius: 18pt,
      fill: subc.lighten(90%)),
    node((0.02, -0.62), text(9pt, fill: subc, weight: "bold")[$S$]),
    // A = box around the whole domain
    node(enclose: ((0,0),(0,1),(0,2),(0,3)), stroke: 0.6pt + gray, inset: 12pt),
    node((-0.46, -0.66), text(9pt, weight: "bold")[$A$]),
    // codomain B — dot then label
    node((1,0.8), [#dot(imgc) #h(3pt) $b_1$]),
    node((1,3),   [#dot(black) #h(3pt) $b_2$]),
    node(enclose: ((1,0.8),(1,3)), stroke: 0.6pt + gray, inset: 12pt),
    node((1.42, 0.0), text(9pt, weight: "bold")[$B$]),
    // f : a1, a2, a4 ↦ b1 ;  a3 ↦ b2
    edge((0,0), (1,0.8), "->", stroke: 0.7pt + subc),
    edge((0,1), (1,0.8), "->", stroke: 0.7pt + subc),
    edge((0,2), (1,0.8), "->", stroke: 0.7pt + gray),
    edge((0,3), (1,3),   "->", stroke: 0.7pt + gray),
    node((0.5, 3.75), text(9pt)[$f$ (apply to each element)]),
  )
]

#punch[
  *Meets, not contains.* The fibre over $b_1$ is $\{a_1, a_2, a_3\}$ — it only *overlaps* $S$ (the
  witness $a_3 in.not S$), yet $b_1 in exists_f (S)$: one witness in $S$ is enough. The fibre over
  $b_2$ is $\{a_4\}$ and misses $S$ entirely, so $b_2 in.not exists_f (S)$. Requiring the *whole*
  fibre $subset.eq S$ would instead give the universal image $forall_f (S)$ — the $forall$ quantifier
  of the last section, a strictly different, dual construction.
]

= The categorical picture: image factorization

In #smallcaps[Set] the composite $S arrow.r.hook A xarrow(f) B$ splits in two — collapse equal
values, then include. With $S = {a_1, a_2}$, both sent to $b_1$:

#align(center)[
  #diagram(spacing: (24mm, 9mm), node-inset: 2pt, node-stroke: none,
    node((0,0), [$a_1$ #h(3pt) #dot(subc)]),
    node((0,1), [$a_2$ #h(3pt) #dot(subc)]),
    node(enclose: ((0,0),(0,1)), stroke: 1pt + subc, inset: 6pt, corner-radius: 16pt, fill: subc.lighten(90%)),
    node((0,-0.72), text(9pt, fill: subc, weight: "bold")[$S$]),
    node((1,0.5), dot(imgc)),
    node(enclose: ((1,0.5),), stroke: 1pt + imgc, inset: 6pt, corner-radius: 16pt, fill: imgc.lighten(90%)),
    node((1,-0.3), text(9pt, fill: imgc, weight: "bold")[$exists_f (S)$]),
    node((2,0.5), [#dot(imgc) #h(3pt) $b_1$]),
    node((2,1.5), [#dot(black) #h(3pt) $b_2$]),
    node(enclose: ((2,0.5),(2,1.5)), stroke: 0.6pt + gray, inset: 11pt),
    node((2.42,-0.1), text(9pt, weight: "bold")[$B$]),
    edge((0,0),(1,0.5), "->>", stroke: 0.8pt + gray),
    edge((0,1),(1,0.5), text(fill: gray, 8pt)[cover], "->>", stroke: 0.8pt + gray),
    edge((1,0.5),(2,0.5), text(fill: imgc, 8pt)[monic], ">->", stroke: 0.9pt + imgc),
  )
]

The *cover* fuses $a_1, a_2$ onto one point; the *monic* includes that point into $B$ as the
subobject $exists_f (S)$. A general category has no elements, but this same factorization of
$S arrow.r.hook A xarrow(f) B$ — cover then monic — *is* the definition:

#align(center)[
  #diagram(spacing: (26mm, 14mm), node-stroke: none, node-inset: 4pt,
    node((0,0), $S$),
    node((1,0), $A$),
    node((1,1), $B$),
    node((0,1), Im($exists_f (S)$)),
    edge((0,0), (1,0), text(fill: subc)[$arrow.r.hook$ #h(-3pt) $m_S$], "->", stroke: 0.8pt + subc),
    edge((1,0), (1,1), text()[$f$], "->", stroke: 0.8pt),
    edge((0,0), (0,1), text(fill: gray)[cover], "->>", stroke: 0.8pt + gray),
    edge((0,1), (1,1), text(fill: imgc)[$m$ #h(-2pt) $arrow.r.hook$], "->", stroke: 0.9pt + imgc),
    edge((0,0), (1,1), text(fill: gray, 8pt)[$m_S thin f$], "->", stroke: 0.5pt + gray, label-side: right),
  )
]

#definition([In the repo (`Fredy/S1_60.lean`)])[
  The diagram's monic is $m_S = $ `S.arr` (the inclusion $S arrow.r.hook A$), so
  $ exists_f (S) quad := quad "image"(m_S thin f), $
  the subobject $exists_f (S) arrow.r.hook B$ drawn above. In Lean:
  #raw("existsAlong f S := image (S.arr ≫ f)") (generic signature `existsAlong g U`). The adjunction
  (next section) is `existsAlong_le_iff`. Needs only a *regular* category, not the full pre-logos.
]

= Why projection gives $exists y$

Take $f = pi_X : X times Y -> X$, the projection that *forgets* $Y$. A subset
$P subset.eq X times Y$ is a *two-place* predicate $p(x, y)$. Push it forward:
$ exists_(pi_X) (P) = { thin x in X thick | thick exists (x', y) in P. thin x' = x thin }
  = { thin x thick | thick exists y. thin p(x, y) thin }. $
So $exists_(pi_X)$ along the projection that drops $Y$ *is* the quantifier $exists y$ — the source of the name.

#align(center)[
  #diagram(spacing: (30mm, 12mm), node-stroke: none, node-inset: 4pt,
    node((0,0), $X times Y$),
    node((1,0), $X$),
    edge((0,0), (1,0), text()[$pi_X$ (drop $y$)], "->", stroke: 0.8pt),
    node((0,1), text(fill: subc, 10pt)[$p(x,y)$]),
    node((1,1), text(fill: imgc, 10pt)[$exists y. thin p(x,y)$]),
    edge((0,1), (1,1), text(fill: imgc)[$exists_(pi_X)$], "|->", stroke: 0.8pt + imgc),
    edge((0,0), (0,1), "->", stroke: 0.3pt + gray, label-side: left),
    edge((1,0), (1,1), "->", stroke: 0.3pt + gray),
  )
]

= The adjunction $exists_f tack.r.double f^\#$

Forward image is *left adjoint* to backward image — a *Galois connection* between the subset lattices:
$ #h(2cm) exists_f (S) subset.eq T quad <==> quad S subset.eq f^\#(T) #h(1cm) (S subset.eq A, thick T subset.eq B). $
Both sides say "$S$ maps into $T$"; in #smallcaps[Set], `all (∈ T) (map f S)` = `all (λa. f a ∈ T) S`.

#align(center)[
  #diagram(spacing: (40mm, 16mm), node-stroke: none, node-inset: 5pt,
    node((0,0), $cal(S)"ub"(A)$),
    node((1,0), $cal(S)"ub"(B)$),
    edge((0,0), (1,0), text(fill: imgc)[$exists_f$ #h(2pt) (image)], "->", stroke: 0.9pt + imgc, bend: 28deg),
    edge((1,0), (0,0), text(fill: prec)[$f^\#$ #h(2pt) (preimage)], "->", stroke: 0.9pt + prec, bend: 28deg),
    node((0.5, 0), text(9pt)[$tack.r.double$]),
  )
]

#remark("The whole hierarchy in one line")[
  $f^\#$ is the substitution in the middle of $#Im($exists_f$) thick tack.r.double thick f^\# thick tack.r.double thick forall_f$.
  - $exists_f tack.r.double f^\#$ — a *regular* category. Gives $exists$ (and that $f^\#$ preserves $inter$, "for free", as a right adjoint).
  - $f^\# tack.r.double forall_f$ — a *Heyting* category (Freyd's *logos*). Gives $forall$.
  The *pre-logos* (coherent) layer in between is exactly: $f^\#$ *also* preserves unions $union$ —
  the one preservation that is *not* free, and the content behind the §1.616 proofs in `S1_60.lean`.
]

= The third definition: "pullbacks transfer finite covers"

Freyd gives a *third*, equivalent definition of pre-logos (§1.611) that never mentions lattices:

#block(width: 100%, fill: prec.lighten(92%), inset: 11pt, radius: 5pt, stroke: (left: 3pt + prec))[
  A *Cartesian category with images* in which *pullbacks transfer finite covers*: given a cover
  ${ B_i ->> B }$ and any map $A -> B$, the pullbacks $A_i = A times_B B_i$ form a cover ${ A_i ->> A }$.
]

Unpacked in #smallcaps[Set]: a *cover* is a surjection, and a finite family ${ B_i ->> B }$ is a cover
when it is *jointly surjective* — every $b in B$ is hit by some $B_i$, i.e. as subobjects $union_i B_i = B$.
Pulling back along $f$ is taking the *preimage*. The claim: preimage of a jointly-surjective family is
jointly surjective.

== A concrete instance

#align(center)[
  #diagram(spacing: (40mm, 7mm), node-inset: 2pt, node-stroke: none,
    // domain A
    node((0,0), [$x$ #h(3pt) #dot(subc)]),
    node((0,1), [$y$ #h(3pt) #dot(black)]),
    node((0,2), [$z$ #h(3pt) #dot(imgc)]),
    node((0,3), [$w$ #h(3pt) #dot(black)]),
    node(enclose: ((0,0),(0,1),(0,2),(0,3)), stroke: 0.6pt + gray, inset: 12pt),
    node((-0.42, -0.62), text(9pt, weight: "bold")[$A$]),
    // A1 = preimage of B1 = {x,y,w}
    node(enclose: ((0,0),(0,1)), stroke: 1pt + subc, inset: 5pt, corner-radius: 14pt, fill: subc.lighten(92%)),
    node((-0.30, 0.5), text(8pt, fill: subc, weight: "bold")[$A_1$]),
    // A2 = preimage of B2 = {y,z,w}
    node(enclose: ((0,2),(0,3)), stroke: 1pt + imgc, inset: 5pt, corner-radius: 14pt, fill: imgc.lighten(92%)),
    node((-0.30, 2.5), text(8pt, fill: imgc, weight: "bold")[$A_2$]),
    // y and w are in both — mark with dashed overlay band
    node((0,1), [$y$ #h(3pt) #dot(black)]),
    // codomain B
    node((1,0.5), [#dot(subc) #h(3pt) $1$]),
    node((1,1.5), [#dot(black) #h(3pt) $2$]),
    node((1,2.5), [#dot(imgc) #h(3pt) $3$]),
    node(enclose: ((1,0.5),(1,2.5)), stroke: 0.6pt + gray, inset: 12pt),
    node((1.42, -0.1), text(9pt, weight: "bold")[$B$]),
    node(enclose: ((1,0.5),(1,1.5)), stroke: 1pt + subc, inset: 4pt, corner-radius: 13pt, fill: subc.lighten(94%)),
    node((1.72, 0.5), text(8pt, fill: subc, weight: "bold")[$B_1$]),
    node(enclose: ((1,1.5),(1,2.5)), stroke: 1pt + imgc, inset: 4pt, corner-radius: 13pt, fill: imgc.lighten(94%)),
    node((1.72, 2.5), text(8pt, fill: imgc, weight: "bold")[$B_2$]),
    // f
    edge((0,0), (1,0.5), "->", stroke: 0.7pt + gray),
    edge((0,1), (1,1.5), "->", stroke: 0.7pt + gray),
    edge((0,2), (1,2.5), "->", stroke: 0.7pt + gray),
    edge((0,3), (1,1.5), "->", stroke: 0.7pt + gray),
    node((0.5, 3.7), text(9pt)[$f$: #h(2pt) $x|->1, thick y|->2, thick z|->3, thick w|->2$]),
  )
]

The cover of $B$ is $B_1 = {1,2}$, $B_2 = {2,3}$ (jointly $= B$). Their preimages
$ A_1 = f^\#(B_1) = {x, y, w}, quad A_2 = f^\#(B_2) = {y, z, w} $
satisfy $A_1 union A_2 = {x,y,z,w} = A$ — so ${A_1, A_2}$ covers $A$. The cover *transferred down the
pullback*. (Note $y, w$ land in *both* $A_i$ because $2 in B_1 inter B_2$; overlap is fine.)

== Why this is the same axiom, covering-side-up

A cover *is* the equation $B_1 union B_2 = B$ (the union is the top $top_B$). "Transfers" then says
$ f^\#(B_1 union B_2) = f^\#(B_1) union f^\#(B_2) #h(1.5cm) (= top_A), $
which is just $f^\#$ *preserving unions* — Definition 2 — in the special case where the union is the
whole object. Relativizing $top$ to an arbitrary subobject recovers the general statement. So
Definitions 2 and 3 are the *same* condition, stated bottom-up (subobjects) vs. top-down (covers).

#punch[
  *In #smallcaps[Set] it is automatic; in general it is a real axiom.* The one-line proof: for $a in A$,
  $f(a)$ is hit by some $B_i$, so $a in f^\#(B_i)$ — preimage of jointly-surjective is jointly-surjective.
  This works because #smallcaps[Set] has *extensive coproducts* ($f^(-1)$ commutes with disjoint
  union), i.e. it is *positive* (§1.623). In a bare regular category the pullback squares always
  *exist*, but the forward inclusion $f^\#(B_1 union B_2) thick lt.eq thick f^\#(B_1) union f^\#(B_2)$
  can fail — which is exactly why Freyd states "transfer finite covers" as a *hypothesis*, and exactly
  the extensivity wall behind the `sorry`s in `S1_60.lean`.
]
