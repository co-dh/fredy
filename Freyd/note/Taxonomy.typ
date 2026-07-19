// Freyd–Scedrov "Categories, Allegories" — taxonomy cheatsheet (1 page).
// The two towers (category classes / allegory classes), the Rel ⇄ Map bridge,
// reflections & completions, representation theorems.  Composition by JUXTAPOSITION
// in diagram order: RS = first R then S.  Section pointers refer to the book.
#import "@preview/dvdtyp:1.0.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set page(margin: (x: 1.0cm, y: 1.1cm))
#show: dvdtyp.with(
  title: "Categories & Allegories — the taxonomy",
  subtitle: [the two towers, the $"Rel" arrows.rl "Map"$ bridge, representation theorems],
  author: none,
  accent: colors.at(6),
)

#set text(size: 8pt)
#set par(leading: 0.52em, spacing: 0.85em)
#show heading: set text(size: 9pt)
#show heading: set block(above: 0.9em, below: 0.5em, sticky: true)
#show table: set text(size: 7.7pt)

// name | fact table, one fact per row
#let laws(..rows) = table(
  columns: (auto, 1fr),
  stroke: 0.3pt + luma(205),
  inset: (x: 3.5pt, y: 2.0pt),
  align: (left + horizon, left + horizon),
  ..rows,
)
// membership ∋ with operand (not relation) spacing
#let eps = math.class("normal", sym.in.rev)

#align(center)[#text(size: 7.5pt)[
#diagram(node-inset: 2.5pt, spacing: (26mm, 5.8mm),
  // category tower (diamond at logos / pre-topos)
  node((0.5,4), [cartesian]),
  node((0.5,3), [*regular*]),
  node((0.5,2), [*pre-logos*]),
  node((0,1),   [*pre-topos*]),
  node((1,1),   [*logos*]),
  node((0.5,0), [*topos*]),
  // allegory tower
  node((2.4,3), [*allegory*]),
  node((2.4,2), [*distributive*]),
  node((2.4,1), [*division*]),
  node((2.4,0), [*power*]),
  // category-side steps
  edge((0.5,4), (0.5,3), [\+ images, stable covers], "->", label-side: left),
  edge((0.5,3), (0.5,2), [\+ stable finite $union$ in $"Sub"$], "->", label-side: left),
  edge((0.5,2), (0,1),   [\+ positive, effective], "->", label-side: left),
  edge((0.5,2), (1,1),   [$+ f^\# tack.l f^(\#\#)$], "->", label-side: right, label-pos: 0.35),
  edge((0,1),   (0.5,0), "->"),
  edge((1,1),   (0.5,0), [\+ power-objects], "->", label-side: right),
  // allegory-side steps
  edge((2.4,3), (2.4,2), [$+ thin 0, union$], "->", label-side: right),
  edge((2.4,2), (2.4,1), [$+ thin dot.c S tack.l dot.c slash S$], "->", label-side: right),
  edge((2.4,1), (2.4,0), [$+ thin eps$ thick, straight], "->", label-side: right),
  // the bridge
  edge((0.5,3), (2.4,3), $"Rel"$, "->", shift: 3pt, label-side: left, label-pos: 0.22),
  edge((2.4,3), (0.5,3), $"Map"$, "->", shift: 3pt, label-side: left, label-pos: 0.22),
  edge((0.5,2), (2.4,2), $"Rel"$, "->", shift: 3pt, label-side: left, label-pos: 0.22),
  edge((2.4,2), (0.5,2), $"Map"$, "->", shift: 3pt, label-side: left, label-pos: 0.22),
  edge((1,1),   (2.4,1), $"Rel"$, "->", shift: 3pt, label-side: left, label-pos: 0.3),
  edge((2.4,1), (1,1),   $"Map"$, "->", shift: 3pt, label-side: left, label-pos: 0.3),
  edge((0.5,0), (2.4,0), $"Rel"$, "->", shift: 3pt, label-side: left, label-pos: 0.22),
  edge((2.4,0), (0.5,0), $"Map"$, "->", shift: 3pt, label-side: left, label-pos: 0.22),
)]]

#align(center)[#text(size: 7.5pt)[
Rightward: $"Rel"(C)$ is always unitary tabular.  Leftward: for $A$ *unitary tabular*, each right-hand
property gives $"Map"(A)$ the matching left-hand one.  $R S$ = first $R$ then $S$; $R^degree$ converse;
$subset$ containment; $"Sub"(A)$ subobjects; $f^\#$ inverse image; $"Dom" R = 1 inter R R^degree$; $cal(S)$ = sets.
]]

#columns(2, gutter: 11pt)[

= Category tower #text(size: 7pt)[(§1.4–1.9)]
#laws(
  [cartesian], [finite products $+$ equalizers ($=$ all finite limits)],
  [regular], [cartesian $+$ images; pullbacks transfer covers],
  [pre-logos], [regular; each $"Sub"(A)$ a lattice, each $f^\#: "Sub"(B) -> "Sub"(A)$ a lattice map],
  [logos], [regular; each $"Sub"(A)$ a lattice; $f^\#$ has a right adjoint: $f^\# B' subset A' <==> B' subset f^(\#\#) A'$],
  [pre-topos], [$eq.delta$ effective positive pre-logos],
  [topos], [cartesian; every object has a power-object ($eps subset [C] times C$ universal). Thm: topos $=$ positive effective transitive logos],
)

= Category adjectives #text(size: 7pt)[(§1.5–1.7)]
#laws(
  [well-supported $A$], [$"Spt"(A) eq.delta "im"(A -> 1) = 1$],
  [capital], [every well-supported object covered by its points; then $1$ is projective],
  [positive], [disjoint complemented $A arrow.r.hook C arrow.l.hook B$ $==>$ finite coproducts],
  [effective], [every equivalence relation is the level (kernel pair) of a map],
  [boolean], [every $"Sub"(A)$ boolean; boolean pre-topos $<==>$ all diagonals complemented],
  [AC], [every entire relation contains a map $<==>$ every object projective],
  [transitive], [every endo-relation has a transitive closure $R^dagger$],
)

= Allegory tower #text(size: 7pt)[(§2.1–2.4)]
#laws(
  [allegory], [category $+ thin R^degree, inter$: $(R S)^degree = S^degree R^degree$, $R(S inter T) subset R S inter R T$, modular law $R S inter T subset (R inter T S^degree) S$],
  [distributive], [$+ thin 0, union$: $R thin 0 = 0$, $R(S union T) = R S union R T$, $R inter (S union T) = (R inter S) union (R inter T)$],
  [division], [$+ thin R slash S$: $T S subset R <==> T subset R slash S$],
  [power], [division $+ thin eps$: thick $1 subset (R slash eps)(eps slash R)$, straight $(eps slash eps) inter (eps slash eps)^degree subset 1$],
  [derived], [$Lambda(R) eq.delta (R slash eps) inter (eps slash R)^degree$ is the unique map with $Lambda(R) thin eps = R$; power-object $[alpha]$ = source of $eps_alpha$; $0, union$ become definable],
)

= Allegory adjectives #text(size: 7pt)[(§2.1–2.2)]
#laws(
  [unitary], [has a unit $lambda$: $1_lambda$ its maximal endo, entire morphisms into $lambda$ from everywhere; $lambda$ = terminator of $"Map"$],
  [tabular], [every $R = f^degree g$ with $f f^degree inter g g^degree = 1$ ($f, g$ maps) $<==>$ pre-tabular $+$ coreflexives split],
  [pre-tabular], [every $R subset$ some tabular morphism],
  [effective], [equivalence relations split ($E = f f^degree$, $f^degree f = 1$) $<==> "Map"$ effective],
  [positive], [distributive $+$ finite coproducts ($<==>$ products; self-dual via $degree$)],
  [semi-simple], [every $R = F^degree G$ with $F, G$ simple $<==>$ splitting all symmetric idempotents is tabular],
  [complete], [locally: homs complete lattices, $R(union.big_i S_i) = union.big_i R S_i$; globally: $+$ disjoint unions of object families. Locally complete distributive $==>$ division: $R slash S = union.big {T : T S subset R}$],
)

= The bridge #text(size: 7pt)[(§1.56, §2.1)]
#laws(
  [$"Rel"(C)$], [objects of $C$; $(alpha, beta) = "Sub"(alpha times beta)$; composition = pullback-then-image; $C$ regular $==>$ associative $+$ modular; $C arrow.r.hook "Rel"(C)$ by graphs],
  [$"Map"(A)$], [subcategory of maps = entire ($1 subset R R^degree$) $+$ simple ($R^degree R subset 1$); on maps $subset$ is $=$],
  [roundtrip], [$C tilde.equiv "Map"("Rel" thin C)$ ($C$ regular); $A tilde.equiv "Rel"("Map" thin A)$ ($A$ tabular)],
  [regular data], [pullback of $f, g$ tabulates $f g^degree$; equalizer tabulates $"Dom"(f inter g)$; image of $f$ tabulates $"Dom"(f^degree)$; $g$ cover $<==> 1 subset g^degree g$],
  [headline], [small regular categories $tilde.equiv$ small unitary tabular allegories],
)

#colbreak()
= Dictionary #text(size: 7pt)[(§2.1–2.4; $A$ unitary tabular)]
#laws(
  [*$C$ is*], [*$<==>$ $"Rel"(C)$ is*],
  [regular], [allegory],
  [pre-logos], [distributive],
  [positive pre-logos], [positive],
  [logos], [division],
  [topos], [power],
  [effective], [effective],
  [pre-topos], [distributive, positive, effective],
)

= Reflections, completions #text(size: 7pt)[(§2.16–2.5, §1.54)]
All faithful representations; full where noted.
#laws(
  [$"Sid"(cal(E))$], [split symmetric idempotents $cal(E)$; full $+$ faithful when all identities $in cal(E)$],
  [tabular refl.], [$"Sid"("Cor")$ of a pre-tabular allegory is tabular],
  [effective refl.], [$"Sid"("Eq")$ of a tabular allegory; of a pre-power allegory: a *power* allegory],
  [positive refl.], [$A^+$ = finite matrices; full; preserves tabular, division],
  [completions], [ideals: any distributive allegory $arrow.r.hook$ locally complete; $A^Sigma$ (infinite matrices): globally complete; systemic $eq.delta "Sid"(A^Sigma)$ — of a small locally complete distributive allegory: a power allegory],
  [pre-topos refl.], [pre-logos $C arrow.r.bar "Map"("Sid"("Eq")(("Rel" thin C)^+))$; same recipe: logos $arrow.r.hook$ positive effective logos (full)],
  [amenable quot.], [congruence respecting $union$, classes have maxima $R^+$; $overline(R) subset overline(S) <==> R^+ subset S^+$; preserves division, effective power, completeness],
  [boolean quot.], [identify $R, S$ disjoint from the same things; of a tabular unitary division allegory: $"Map"$ = a boolean logos; every topos $arrow.r.hook$ a boolean topos],
  [capitalization], [(category side) every small (pre-)regular category $arrow.r.hook$ a capital one],
)

= Representation theorems #text(size: 7pt)[(§1.55, §2.15–2.33)]
#laws(
  [Henkin–Lubkin], [every small pre-regular category $arrow.r.hook$ a power of $cal(S)$; so Horn sentences true in $cal(S)$ hold in every regular category],
  [allegories], [every small unitary tabular allegory $arrow.r.hook$ a power of $"Rel"(cal(S))$ ($eq.delta$ representable)],
  [distributive], [small unitary distributive, pre-tabular *or* semi-simple $arrow.r.hook$ a power of $"Rel"(cal(S))$],
  [division], [tabular unitary division $arrow.r.hook$ $cal(V)$-valued sets, $cal(V)$ = opens of a Stone space; countable: $arrow.r.hook$ a countable power of $cal(O)(X)$-valued sets, $X$ metrizable without isolated points],
  [logoi], [countable logos $arrow.r.hook$ a countable power of $"Sh"(X)$; with a coprime terminator: $arrow.r.hook "Sh"(X)$],
)

= Boundaries #text(size: 7pt)[(§2.15, §2.4)]
#laws(
  [modular law], [entire-or-empty relations satisfy every axiom *except* the modular law, and are tabular — the law is independent],
  [Desargues], [Veblen–Wedderburn plane: a one-object allegory (184 morphisms) representable in *no* power of $"Rel"(cal(S))$],
  [no finite base], [no finite equation set true in $"Rel"(cal(S))$ yields all equations of $"Rel"(cal(S))$; graph containments are decidable],
  [effectivity], [assemblies over partial recursive functions: a positive pre-logos, *not* effective; its effective reflection = the realizability topos],
)

]
