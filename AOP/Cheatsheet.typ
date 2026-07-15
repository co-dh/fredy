// Allegory / Algebra-of-Programming cheatsheet.
// Conventions: Freyd–Scedrov ("Categories, Allegories").  Composition is written by
// JUXTAPOSITION in diagram order: RS means "first R, then S" (the repo's R ≫ S).
// Gray monospace tags = Lean names in this repo (all sorry-free, axioms ⊆ {propext, Quot.sound}).
#import "@preview/dvdtyp:1.0.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set page(margin: (x: 1.0cm, y: 1.1cm))
#show: dvdtyp.with(
  title: "Allegories & Algebra of Programming",
  subtitle: [cheatsheet — Freyd conventions, B&dM laws, `fredy` Lean names],
  author: none,
  accent: colors.at(6),
)

#set text(size: 8pt)
#set par(leading: 0.45em, spacing: 0.65em)
#show heading: set text(size: 9pt)
#show heading: set block(above: 0.9em, below: 0.5em)
#show figure.where(kind: "thmenv"): set block(breakable: false)

// Lean-name tag, right-aligned
#let ln(s) = {h(1fr); text(size: 5.8pt, fill: luma(110), font: "DejaVu Sans Mono", s)}
// one law per line
#let law(m, tag) = block(spacing: 0.42em, width: 100%)[#m#ln(tag)]

#columns(2, gutter: 11pt)[

= Conventions
Objects $alpha, beta, gamma$; morphisms (relations) $R,S,T,Q$; *maps* $f,g,h$;
coreflexives $C,D subset 1$. $R S$ = "first $R$, then $S$" (diagram order); $R^degree$ converse;
$subset$ containment; $inter$, $union$ meet/join; $1 = 1_alpha$ identity.
$[alpha]$ power-object, $in.rev : [alpha] -> alpha$ membership ("epsiloff"),
$Lambda$ power transpose. $F$ relator; $mu F$ initial algebra, structure map
$sans("in") : F(mu F) -> mu F$; catamorphism $⦇S⦈$. Points: $x thin R thin y$.
*B&dM dictionary:* their $S dot.c R$ = our $R S$; their $∈$ = our $in.rev$;
their $R\/S, thin R backslash S$ swap accordingly; lowercase $f$ = map, both books.

= Allegory #text(size: 7pt)[(Freyd 2.11)]
#law([$(R^degree)^degree = R, quad (R S)^degree = S^degree R^degree, quad (R inter S)^degree = R^degree inter S^degree$], "recip_*")
#law([$R subset R', thin S subset S' ==> R S subset R' S', quad R(S union T) = R S union R T$], "comp_mono, comp_dist")
#law([*modular law:* $thin R S inter T subset (R inter T S^degree) thin S$ #h(0.5em) (mirror: $subset R (S inter R^degree T)$)], "modular_le")
#law([$R subset R R^degree R$], "le_comp_recip_comp")

= Kinds of morphisms #text(size: 7pt)[(2.12–2.16)]
#law([entire: $1 subset R R^degree$; #h(0.5em) simple: $R^degree R subset 1$; #h(0.5em) map = both], "Entire, Simple, Map")
#law([reflexive: $1 subset R$; #h(0.5em) transitive: $R R subset R$; #h(0.5em) coreflexive: $C subset 1$], "S2_1")
#law([$"dom" R eq.delta 1 inter R R^degree, quad R = ("dom" R) R, quad C D = C inter D = D C$], "Dom, dom_comp")
#law([$R$ simple $==> R(S inter T) = R S inter R T$], "simple_dist_inter")
#law([shunting ($f$ a map): $thin f^degree R subset S <==> R subset f S, quad R f subset S <==> R subset S f^degree$], "map_shunt*")
#law([$f subset g ==> f = g$ #h(0.4em) (maps)], "map_le_antisym")
#law([tabulation of $R$: maps $f,g$ with $f^degree g = R, thin f f^degree inter g g^degree = 1$ #text(size: 7pt)[(2.14)]], "TabularAllegory")

= Division #text(size: 7pt)[(2.31–2.35, B&dM §4.6)]
#law([$T S subset U <==> S subset T backslash U, quad x thin (T backslash U) thin y <==> forall w. thin w T x => w U y$], "le_leftDiv_iff")
#law([$S T subset U <==> S subset U slash T$ #h(0.5em) (right division, mirror)], "le_rightDiv_iff")
#law([cancellation: $thin T (T backslash U) subset U, quad (U slash T) thin T subset U$], "leftDiv_comp_le")
#law([$(T U) backslash V = U backslash (T backslash V)$], "leftDiv_comp")
#law([symmetric division #text(size: 7pt)[(2.35)]: $thin (R slash S) inter (S slash R)^degree$, #h(0.4em) $x |-> y$ iff $forall c. thin x R c <-> y S c$], "symDiv")

= Power #text(size: 7pt)[(2.41–2.42; B&dM ch. 4, 7)]
#law([$Lambda(R) : gamma -> [alpha]$ for $R : gamma -> alpha$ — the unique *map* with $Lambda(R) thin in.rev = R$], "A, A_eps_eq', A_UP")
#law([$f = Lambda(f in.rev), quad Lambda(in.rev) = 1, quad Lambda$ injective], "A_eps_reflection")
#law([$Lambda(f R) = f Lambda(R)$ #h(0.4em) ($f$ a map)], "A_fusion")
#law([$E R eq.delta Lambda(in.rev R)$ — existential image; Freyd's covariant $[dot]$ (1.922)], "existsImage")
#law([absorption: $thin Lambda(S) thin E(R) = Lambda(S R)$], "A_absorption")
#law([$tau eq.delta Lambda(1)$ singleton map, monic #text(size: 7pt)[(2.415)]], "singletonRel")

#v(2pt)
*Selectors on $[alpha]$* (B&dM p. 166): $min R, max R : [alpha] -> alpha$; $thin "thin" Q : [alpha] -> [alpha]$
#law([$min R eq.delta in.rev inter (in.rev^degree backslash R), quad max R eq.delta min R^degree$], "minRel, maxRel")
#law([$X subset min R <==> X subset in.rev and in.rev^degree X subset R$], "le_minRel_iff")
#law([*(7.5)*: $thin Lambda(S)(min R) = S inter (S^degree backslash R)$], "A_comp_minRel")
#law([UP of (7.5): $thin X subset Lambda(S)(min R) <==> X subset S and S^degree X subset R$], "le_A_comp_minRel_iff")
#law([$S harpoon.tr R eq.delta S inter (S^degree backslash R) = Lambda(S)(min R)$ — AoPA *shrink* is exactly (7.5)], "shrink_eq_A_comp_minRel")
#law([$"thin" Q eq.delta (subset.eq) inter (in.rev^degree backslash (Q in.rev^degree)), quad ("thin" Q) thin in.rev thin subset thin in.rev$], "thinRel")

= Products #text(size: 7pt)[(B&dM §4.4)]
#law([$angle.l R, S angle.r eq.delta R pi^degree inter S pi'^degree, quad R times S eq.delta angle.l pi R, thin pi' S angle.r$], "rprodMap")
#law([$angle.l R, S angle.r pi subset R$ #h(0.4em) ($=$ if $S$ entire); #h(0.5em) $angle.l f, g angle.r$ is a map], "")
#law([$(R times S)(T times U) subset R T times S U$ — $times$ is lax on relations], "")

= Relational folds #text(size: 7pt)[(B&dM ch. 5–6)]
#grid(columns: (1fr, 1fr), align: center + horizon,
  diagram(node-inset: 3pt, spacing: (11mm, 8mm),
    node((0,0), $F(mu F)$), node((1,0), $F alpha$),
    node((0,1), $mu F$),    node((1,1), $alpha$),
    edge((0,0), (1,0), $F ⦇S⦈$, "->"),
    edge((0,0), (0,1), $sans("in")$, "->", label-side: right),
    edge((1,0), (1,1), $S$, "->"),
    edge((0,1), (1,1), $⦇S⦈$, "->", label-side: right)),
  diagram(node-inset: 3pt, spacing: (11mm, 8mm),
    node((0,0), $gamma$), node((1,0), $[alpha]$),
    node((1,1), $alpha$),
    edge((0,0), (1,0), $Lambda(R)$, "->"),
    edge((0,0), (1,1), $R$, "->", label-side: right),
    edge((1,0), (1,1), $in.rev$, "->")))
#law([Eilenberg–Wright UP, over *all* $X$ #text(size: 7pt)[(5.12)]: $quad sans("in") thin X = (F X) thin S <==> X = ⦇S⦈$], "relCata_UP")
#law([computation: $sans("in") ⦇S⦈ = (F ⦇S⦈) thin S$; #h(0.5em) reflection: $⦇sans("in")⦈ = 1$], "relCata_cancel, _alpha")
#law([fusion #text(size: 7pt)[(6.2)]: $thin (F S) thin T subset R S ==> ⦇T⦈ subset ⦇R⦈ S$], "relCata_le_comp")
#law([$S subset T ==> ⦇S⦈ subset ⦇T⦈; quad S$ a map $==> ⦇S⦈$ a map], "relCata_mono, _map")
#law([power-set fold: $thin Lambda ⦇S⦈ = ⦇Lambda((F in.rev) S)⦈$], "A_relCata")
#law([banana-split / tupling: $thin angle.l ⦇S⦈, ⦇T⦈ angle.r = ⦇ angle.l (F pi) S, thin (F pi') T angle.r ⦈$], "tupling, tupling_banana")
#law([hylomorphism #text(size: 7pt)[(6.4)]: $thin ⦇T⦈^degree ⦇S⦈ = mu (X |-> T^degree (F X) S)$], "hylo_eq_mu, hylo_fixed")
#law([$T^degree (F X) thin S subset X ==> ⦇T⦈^degree ⦇S⦈ subset X$], "hylo_le_of_prefixed")

= Galois connections & fixed points
#law([$f(x) prec.eq y <==> x lt.tri.eq g(y)$ #h(0.4em) point-free (orders as relations $R, S$): $R thin f^degree = g thin S$], "galois_iff (A4_7)")
#law([shunting = the archetype; division: $(dash.en) T tack.l (dash.en) slash T$, $quad T (dash.en) tack.l T backslash (dash.en)$], "S2_313")
#law([$mu phi eq.delta inter.big {X : phi X subset X}; quad phi "monotone" ==> phi(mu phi) = mu phi$], "mu, mu_fixed")
#law([induction: $phi X subset X ==> mu phi subset X; quad (forall X. thin phi X subset psi X) ==> mu phi subset mu psi$], "mu_le_mu")

= Optimization theorems #text(size: 7pt)[(B&dM ch. 7–10)]
#law([$S$ *monotonic on* $R quad eq.delta quad (F R) thin S subset S R$], "MonotonicAlg")

#theorem("Greedy — B&dM 7.2", numbering: none)[
  $R$ transitive, $S$ monotonic on $R^degree$:
  $ ⦇Lambda(S)(min R)⦈ thin subset thin Lambda(⦇S⦈)(min R) $
  Max form ($S$ monotonic on $R$): $⦇Lambda(S)(max R)⦈ subset Lambda(⦇S⦈)(max R)$.#ln("greedy, greedy_max")
]
#theorem("Thinning — B&dM 8.1", numbering: none)[
  $Q$ transitive, $S$ monotonic on $Q^degree$:
  $ ⦇Lambda((F in.rev) S)("thin" Q)⦈ thin subset thin Lambda(⦇S⦈)("thin" Q) $
  With $1 subset Q subset R$, $R$ transitive: postcomposing $min R$ refines
  $Lambda(⦇S⦈)(min R)$ — build a Pareto front, pick the optimum at the end.#ln("thinning, thinning_min")
]
#theorem("Dynamic programming — B&dM 9.1", numbering: none)[
  $h$ a map, monotonic on transitive $R$:
  $ mu (X |-> Lambda(T^degree) thin E((F X) h) thin (min R)) thin subset thin Lambda(⦇T⦈^degree ⦇h⦈)(min R) $
  Decompose all ways ($Lambda T^degree$), solve subproblems ($E((F X)h)$), keep an optimum
  of partial results. 9.2 adds a $"thin" Q$ stage after $Lambda T^degree$.#ln("dynamic_programming(_thin)")
]
#law([Greedy-from-DP (B&dM ch. 10, p. 246): bifunctor conditions collapse the DP recursion to a greedy sweep.], "greedy_dp, greedy_dp_of_birelator")

= Rel(Set) working set #text(size: 7pt)[(`leet/` entry points)]
#text(size: 7pt)[
Derivation idiom: `spec : dIn ⟶ dOut` relation, then
`solve = A spec ≫ maxRel D` pinned by #text(font: "DejaVu Sans Mono", size: 6.5pt)[eq_A_comp_maxRel] (antisymmetric $D$!).
Fold emergence: #text(font: "DejaVu Sans Mono", size: 6.5pt)[SL.snocFold_unique · CL.consFold_unique · TB.treeFold_unique · SL.tupling]; WF/divide-and-conquer:
#text(font: "DejaVu Sans Mono", size: 6.5pt)[hyloFold_unique · TreeHylo.treeHyloFold_unique].
Generic functor layer: #text(font: "DejaVu Sans Mono", size: 6.5pt)[Poly.foldR_universal/fusion, Poly.hylo_fixed].
All of the above: sorry-free, axioms $subset.eq$ {propext, Quot.sound}, mathlib-free.]
]
