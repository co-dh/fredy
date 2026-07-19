#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set page(width: 18cm, height: auto, margin: 1.6cm)
#set text(size: 10.5pt, font: "New Computer Modern")
#set par(justify: true)
#show raw.where(block: false): box.with(fill: luma(240), inset: (x: 2pt), outset: (y: 2pt), radius: 1pt)

// Visible right-angle corner marks (Freyd style): ┌ for pullback (top-left object),
// ┘ for pushout (bottom-right object).
#let pbcorner = box(width: 8pt, height: 8pt, stroke: (top: 0.9pt, left: 0.9pt))
#let pocorner = box(width: 8pt, height: 8pt, stroke: (bottom: 0.9pt, right: 0.9pt))

#align(center)[
  #text(15pt, weight: "bold")[§1.582 — regularity as a pair of Horn sentences]
]

Reading of Freyd & Scedrov, _Categories and Allegories_ §1.582. Composition in *diagram order*:
`xy` means first `x` then `y`. Companion to `Freyd/S1_58.lean` (`image_via_coeq`, §1.581
`bicart_repr_preserves_covers`, §1.583 `effectiveness_iff_coeq_pullback`).

= The claim

If `𝒜` is *bicartesian* (Cartesian #sym.plus coCartesian — has finite limits *and* colimits), then
the predicate "`𝒜` is regular" is a *pair of Horn sentences in the bicartesian predicates*.

The reason: in a bicartesian category the *image* of a map is *built by operations*, not merely
asserted to exist — so the existential quantifiers in "regular" disappear and what is left is purely
universal equational implications.

= The reason, in one diagram

Two nested diamonds sharing the apex $ker(x)$ and the two copies of $A$ — the level, its coequalizer,
and the induced $m$:

#align(center)[
  #diagram(
    spacing: (16mm, 11mm),
    node-stroke: none,
    node((2, 0), $ker(x)$),
    node((0, 2), $A$),
    node((4, 2), $A$),
    node((2, 3), $C$),
    node((2, 5), $B$),
    // outer diamond = level (kernel pair), a pullback:  l, r, x, x
    edge((2, 0), (0, 2), $l$, "->", label-side: left),
    edge((2, 0), (4, 2), $r$, "->", label-side: right),
    edge((0, 2), (2, 5), $x$, "->", label-side: left),
    edge((4, 2), (2, 5), $x$, "->", label-side: right),
    // inner diamond = coequalizer:  A ⇉ C by q  (so l;q = r;q)
    edge((0, 2), (2, 3), $q$, "->>"),
    edge((4, 2), (2, 3), $q$, "->>", label-side: right),
    // unique induced map (coequalizer universal property) — dashed
    edge((2, 3), (2, 5), $m$, "-->"),
  )
]
#align(center)[#text(9pt, style: "italic")[
  *Outer diamond* $ker(x), A, A, B$ — the *level* (kernel pair) of $x$, a pullback; it commutes, so
  $l ; x = r ; x$. #h(0.4em)
  *Inner diamond* $ker(x), A, A, C$ — the *coequalizer* $q$ of $l, r$ (a cover); $l ; q = r ; q$. #h(0.4em)
  Since $x$ collapses $l, r$ too, the coequalizer's universal property yields a *unique* $m : C -> B$
  with $q ; m = x$ — drawn *dashed*.
]]

Every piece is an *operation* (pullback, coequalizer), never an "there exists" — which is exactly what
lets regularity be *Horn*. (That $m$ is moreover *monic* is the first Horn sentence, below.)

== What "Horn sentence" means here

A *Horn sentence* is $forall dots, (e_1 and dots and e_k) ==> e_0$ — a conjunction of equations
implying one equation. The load-bearing feature is *no $exists$*: every witness is supplied by a
function symbol (the bicartesian operations). Stated naïvely, "regular" has existentials ("there
*exists* an image", "there *exists* a lift through a pullback"); Skolemizing them against the
operations turns each into Horn form.

= The pair of Horn sentences

== (H1) The induced $m$ is monic

The constructed factorization really is *cover-then-mono*, so images exist:

#align(center)[
  #diagram(
    spacing: (15mm, 11mm),
    node-stroke: none,
    node((0, 0), $W$),
    node((2, 0), $C$),
    node((4, 0), $B$),
    edge((0, 0), (2, 0), $u$, "->", shift: 4pt),
    edge((0, 0), (2, 0), $v$, "->", shift: -4pt, label-side: right),
    edge((2, 0), (4, 0), $m$, ">->"),
  )
]
#align(center)[#text(9pt, style: "italic")[
  $forall u med v, quad u ; m = v ; m ==> u = v.$ #h(0.8em)
  A single Horn sentence — `m` is the *operationally defined* map, so there is no $exists$.
]]

In a general bicartesian category `m` need *not* be monic, so requiring it is genuine content. This
is exactly `image_via_coeq` (`Freyd/S1_58.lean`): `Mono (hcoeq.desc x kp_sq)`.

== (H2) Covers are stable under pullback

The cover $q$, pulled back along *any* $h : D -> C$, is again a cover:

#align(center)[
  #diagram(
    spacing: (15mm, 12mm),
    node-stroke: none,
    node((0, 0), $P$),
    node((2, 0), $A$),
    node((0, 1), $D$),
    node((2, 1), $C$),
    node((0.33, 0.33), pbcorner),                        // pullback corner
    edge((0, 0), (2, 0), $$, "->"),
    edge((0, 0), (0, 1), $q'$, "->>", label-side: right),  // pulled-back cover
    edge((2, 0), (2, 1), $q$, "->>"),
    edge((0, 1), (2, 1), $h$, "->"),
  )
]
#align(center)[#text(9pt, style: "italic")[
  Form the *pullback* of $q$ along $h$ (an operation); assert the leg $q'$ is again a coequalizer
  (cover). Equational, hence Horn — no $exists$, the pullback is constructed.
]]

= Putting it together

(H1) #sym.plus (H2) are Barr's two conditions for a regular category — *image factorizations exist*
and *their cover-parts are pullback-stable* — now both phrased with operations instead of $exists$.
That is the "pair of Horn sentences in the bicartesian predicates".

Horn-ness is the payoff property: it travels along structure-preserving functors and into
products/substructures. Hence

- *§1.581* — a representation preserving the bicartesian operations automatically preserves
  regularity (`bicart_repr_preserves_covers`); and
- *§1.583* — effectiveness of an equivalence relation likewise collapses to one Horn condition,
  "the coequalizer square is a pullback" (`effectiveness_iff_coeq_pullback`).

= In the language of diagrams (§1.39)

Freyd's *language of diagrams* (§1.39) is a sequence of diagrams joined by $forall \/ exists$ — each
$exists$-step *extending* the previous with new vertices/arrows, commutativity assumed except at a
puncture mark, objects never identified (§1.391, so the expressible properties are exactly the
equivalence-invariant ones). With the *primitive predicates* "this diagram is a *pullback / equalizer /
product / terminator*" (§1.443–§1.444) it is moreover a genuine *deductive* system, and its *inference
rules are the universal properties*:

- *pullback* — a commuting cone yields a unique mediator;
- *equalizer* — a map that equalizes factors uniquely through it;
- *mono* — right-cancellation ($u m = v m ==> u = v$); dually *coequalizer \/ cover* — left-cancellation.

*Diagram chasing is derivation in this system.* (Soundness, §1.444: a Horn sentence over these
predicates true in *Set* holds in *every* Cartesian category — so such a goal may even be discharged by
chasing in *Set*.) So §1.582 is statable *and* provable here: below is (H1) as a $forall$-sentence,
then a chase each of whose steps is one of these rules.

== (H1) stated diagrammatically

"$m$ is monic" is the $forall$-sentence: for the commuting diagram on the left (the puncture lets
$u != v$), the two arrows must coincide —

#align(center)[
  $forall$ #h(1em)
  #box(baseline: 40%)[#diagram(
    spacing: (13mm, 7mm),
    node-stroke: none,
    node((0, 0), $W$),
    node((2, 0), $C$),
    node((4, 0), $B$),
    edge((0, 0), (2, 0), $u$, "->", shift: 3pt),
    edge((0, 0), (2, 0), $v$, "->", shift: -3pt, label-side: right),
    edge((2, 0), (4, 0), $m$, ">->"),
  )]
  #h(0.6em) with $u ; m = v ; m$ #h(1em) $==>$ #h(1em) $u = v$.
]

No $exists$, no new object — a pure Horn implication between equations.

== The chase: $m$ is monic because $C$ *is* the image of $x$

Factor $x$ through its *image* (regularity: cover $e$ then mono $i$). Two covers out of $A$ — $e$ and
$q$ — with monic / induced tails:

#align(center)[
  #diagram(
    spacing: (17mm, 11mm),
    node-stroke: none,
    node((0, 0), $A$),
    node((2, 0), $I$),
    node((4, 0), $B$),
    node((2, 1.4), $C$),
    edge((0, 0), (2, 0), $e$, "->>"),                    // image cover
    edge((2, 0), (4, 0), $i$, ">->"),                    // image mono
    edge((0, 0), (2, 1.4), $q$, "->>", label-side: right), // coequalizer cover
    edge((2, 1.4), (4, 0), $m$, "-->", label-side: right), // induced map
    edge((2, 0), (2, 1.4), $tilde.eq$, "<->"),           // C ≅ I
  )
]

#set enum(numbering: "1.")
+ $l ; x = r ; x$, and $i$ monic *right-cancels* [mono rule] to give $l ; e = r ; e$; so $e$ coequalizes
  $l, r$, and the *coequalizer UMP* of $q$ [coequalizer rule] yields a unique $phi : C -> I$ with
  $q ; phi = e$.
+ The image cover $e$ has kernel pair $ker(x)$ ($i$ monic) and *is* the coequalizer of it; so $l, r$
  coequalize through $e$, and the *coequalizer UMP* of $e$ [coequalizer rule] yields a unique
  $psi : I -> C$ with $e ; psi = q$.
+ $q ; (phi ; psi) = e ; psi = q = q ; 1$, and $q$ a cover is *epic*, so it *left-cancels* [cover rule]:
  $phi ; psi = 1$; symmetrically $psi ; phi = 1$. So $C tilde.eq I$.
+ Under that iso $m$ *is* the image mono $i$ (both are the unique tail with $q ; (-) = x = e ; i$);
  iso $;$ mono is mono [composition]. So *$m$ is monic*. $qed$

Every step is a rule of the diagram language — mono/cover cancellation and the coequalizer universal
property. The two *regular* facts it stands on (an image factorization exists; a cover is the
coequalizer of its kernel pair) are the standing predicates the rules act on. So this is a *derivation*,
not an informal picture — and by §1.444 the same Horn goal could instead be checked in *Set* (where
$C$ is literally the set-image of $x$) and transported. In Lean it is `image_via_coeq`
(`Freyd/S1_58.lean`), whose proof runs exactly these steps (`image.lift`,
`cover_is_coequalizer_of_level`, `cover_epi`).
