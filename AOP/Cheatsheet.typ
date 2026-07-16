// Allegory / Algebra-of-Programming cheatsheet (2 pages).
// Conventions: Freyd–Scedrov ("Categories, Allegories").  Composition is written by
// JUXTAPOSITION in diagram order: RS means "first R, then S" (B&dM's S·R).
// Sources: Bird & de Moor, "Algebra of Programming", chs. 2–9, mirrored into diagram order;
// division slashes flip under the mirror (see Conventions).
#import "@preview/dvdtyp:1.0.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set page(margin: (x: 1.0cm, y: 1.1cm))
#show: dvdtyp.with(
  title: "Allegories & Algebra of Programming",
  subtitle: [cheatsheet — Freyd conventions; the B&dM laws in diagram order],
  author: none,
  accent: colors.at(6),
)

#set text(size: 8pt)
#set par(leading: 0.52em, spacing: 0.85em)
#show heading: set text(size: 9pt)
#show heading: set block(above: 0.9em, below: 0.5em)
#show figure.where(kind: "thmenv"): set block(breakable: false)
#show table: set text(size: 7.7pt)

// one law per line
#let law(m) = block(spacing: 0.55em, width: 100%)[#m]
// name | law table, one law per row
#let laws(..rows) = table(
  columns: (auto, 1fr),
  stroke: 0.3pt + luma(205),
  inset: (x: 3.5pt, y: 2.2pt),
  align: (left + horizon, left + horizon),
  ..rows,
)
// membership ∋ with operand (not relation) spacing, so `X eps subset S` sets cleanly
#let eps = math.class("normal", sym.in.rev)

#columns(2, gutter: 11pt)[

= Conventions
Objects $alpha, beta, gamma$; relations $Q,R,S,T,U,V$; *maps* $f,g,h,k,m$; coreflexives
$C,D subset 1$. $R S$ = "first $R$, then $S$" (diagram order); $R^degree$ converse; $subset$
containment; $inter, union$ meet/join; $nothing$ empty; $Pi$ largest; $1$ identity.
$[alpha]$ power-object, $eps : [alpha] -> alpha$ membership ("epsiloff"), $Lambda$ power
transpose, $tau eq.delta Lambda(1)$ singleton. $F, G$ relators; $mu F$ initial algebra with
structure map $sans("in") : F(mu F) -> mu F$; catamorphism $⦇S⦈$. Points: $x thin R thin y$.
*B&dM dictionary:* their $S dot.c R$ = our $R S$; their $∈$ = our $eps$ (their $eps$ =
our $eps^degree$); slashes flip keeping numerator/denominator roles: their $T backslash U$ =
our $U slash T$, their $U slash T$ = our $T backslash U$; their $(|R|)$ = our $⦇R⦈$; their
$alpha$ = our $sans("in")$.

= Adjunctions
Each row is a Galois connection $L tack.l lr(U): thin L X subset Y <==> X subset U Y$;
$dot.c$ marks the argument slot.
Every $L$ preserves $union$, every $U$ preserves $inter$, both are monotone.
#laws(
  [$dot.c^degree tack.l dot.c^degree$], [$R^degree subset S <==> R subset S^degree$ #h(1fr) (self-adjoint order-iso)],
  [$dot.c inter R tack.l R => dot.c$], [$X inter R subset S <==> X subset (R => S)$],
  [$T dot.c tack.l T backslash dot.c$], [$T X subset U <==> X subset T backslash U$],
  [$dot.c thin T tack.l dot.c slash T$], [$X T subset U <==> X subset U slash T$],
  [$dot.c minus S tack.l S union dot.c$], [$R minus S subset X <==> R subset S union X$],
  [$f^degree dot.c tack.l f dot.c$], [shunting: $f^degree R subset S <==> R subset f S$],
  [$dot.c thin f tack.l dot.c thin f^degree$], [shunting: $R f subset S <==> R subset S f^degree$],
  [$"dom" tack.l dot.c thin Pi$], [$"dom" R subset C <==> R subset C Pi$ #h(1fr) (dually $"ran" tack.l Pi dot.c$)],
  [$dot.c^* tack.l$ incl.], [$R^* subset X <==> R subset X$ for preorders $X$ #h(1fr) (reflection)],
  [$Lambda$ iso], [$f = Lambda(R) <==> f eps = R$: relations $gamma -> alpha$ $tilde.equiv$ maps $gamma -> [alpha]$],
)

= What preserves what
#table(
  columns: (auto, auto, auto, auto, 1fr),
  stroke: 0.3pt + luma(205),
  inset: (x: 3.5pt, y: 2.2pt),
  align: left + horizon,
  [*op*], [$subset$], [$inter$], [$union$], [*notes*],
  [$dot.c^degree$], [$=$], [$=$], [$=$], [involution; $(R S)^degree = S^degree R^degree$],
  [$S dot.c$], [mono], [$subset$; $=$ if $S$ simple], [$=$], [$S nothing = nothing$],
  [$dot.c thin S$], [mono], [$subset$; $=$ if $S S^degree subset 1$], [$=$], [],
  [relator $F$], [mono], [$subset$; $=$ on corefl.], [$supset$], [$(F R)^degree = F(R^degree)$; maps $|->$ maps; $F("dom" R) = "dom"(F R)$],
  [$T backslash dot.c$], [mono], [$=$], [$supset$], [antitone in $T$: $(R union S) backslash T = (R backslash T) inter (S backslash T)$],
  [$"dom", "ran"$], [mono], [], [$=$], [],
  [$min$], [mono], [$=$], [], [$min R$ simple $<==>$ $R$ antisymmetric],
  [$"thin"$], [mono], [], [], [preorder if the argument is],
  [$mu$], [mono], [], [], [$(forall X. thin phi X subset psi X) ==> mu phi subset mu psi$],
)

= Maps: products, sums, folds #text(size: 7pt)[(B&dM ch. 2)]
#laws(
  [UP $times$], [$h = angle.l f, g angle.r <==> h pi = f and h pi' = g$],
  [cancel, reflect], [$angle.l f,g angle.r pi = f, quad angle.l f,g angle.r pi' = g, quad angle.l pi, pi' angle.r = 1$],
  [fuse], [$m angle.l h,k angle.r = angle.l m h, m k angle.r$],
  [functor], [$f times g eq.delta angle.l pi f, pi' g angle.r, quad (f times g)(h times k) = f h times g k$],
  [absorb], [$angle.l p,q angle.r (f times g) = angle.l p f, q g angle.r$],
  [UP $+$], [$h = [f,g] <==> iota h = f and iota' h = g$],
  [cancel, reflect], [$iota [f,g] = f, quad iota' [f,g] = g, quad [iota, iota'] = 1$],
  [fuse], [$[h,k] m = [h m, k m], quad (h+k)[f,g] = [h f, k g]$],
  [functor], [$f + g eq.delta [f iota, g iota']$],
  [exchange], [$angle.l [f,g], [h,k] angle.r = [angle.l f,h angle.r, angle.l g,k angle.r]$],
  [UP $⦇dot⦈$], [$h = ⦇f⦈ <==> sans("in") thin h = (F h) f$],
  [reflect], [$⦇sans("in")⦈ = 1$],
  [fuse], [$f h = (F h) g ==> ⦇f⦈ h = ⦇g⦈$],
  [shift], [$⦇g f⦈ = ⦇(F f) g⦈ f$],
  [Lambek], [$sans("in")$ iso, $quad sans("in")^(-1) = ⦇F sans("in")⦈$],
  [type functor], [$sans("T") f eq.delta ⦇F(f,1) thin sans("in")⦈$ (lists: map), $quad sans("in") (sans("T") f) = F(f, sans("T") f) thin sans("in")$],
  [map fusion], [$(sans("T") g) ⦇h⦈ = ⦇F(g,1) thin h⦈$],
)

= Program calculus #text(size: 7pt)[(B&dM ch. 3)]
#laws(
  [banana-split], [$angle.l ⦇h⦈, ⦇k⦈ angle.r = ⦇ angle.l (F pi) h, (F pi') k angle.r ⦈$],
  [mutual rec.], [$sans("in") f = (F angle.l f,g angle.r) h and sans("in") g = (F angle.l f,g angle.r) k <==> angle.l f,g angle.r = ⦇angle.l h,k angle.r⦈$],
  [paramorphism], [$sans("in") f = (F angle.l f, ⦇h⦈ angle.r) g ==> f = ⦇angle.l g, (F pi') h angle.r⦈ pi$],
  [triangle], [$"tri" f eq.delta ⦇F(1, sans("T") f) thin sans("in")⦈$],
  [Horner], [$g f = F(f,f) g ==> ("tri" f) ⦇g⦈ = ⦇F(1,f) g⦈$],
  [conditional], [$(p -> f, g) eq.delta p? thin [f,g]$; $quad (p -> f, f) = f$],
  [pre, post], [$(p -> f,g) h = (p -> f h, g h), quad h (p -> f, g) = (h p -> h f, h g)$],
  [filter], [$(sans("T") f)("filter" p) = ("filter"(f p))(sans("T") f)$],
  [UP curry], [$g = "curry" f <==> (g times 1) "apply" = f$],
  [cancel, reflect], [$("curry" f times 1) "apply" = f, quad "curry"("apply") = 1$],
  [fuse], [$g ("curry" f) = "curry"((g times 1) f)$],
)
#law([structural recursion: if $phi (G(h times 1)) = (F h times 1) phi$ then
  $(sans("in") times 1) f = phi (G f) h$ has the unique solution $f = (⦇"curry"(phi (G "apply") h)⦈ times 1) "apply"$])

= Allegory #text(size: 7pt)[(B&dM 4.1–4.2)]
#laws(
  [converse], [$(R^degree)^degree = R, quad (R S)^degree = S^degree R^degree, quad (R inter S)^degree = R^degree inter S^degree$],
  [modular law], [$R S inter T subset (R inter T S^degree) S subset (R inter T S^degree)(S inter R^degree T)$],
  [modular identity], [$R inter T S = R inter (T inter R S^degree) S$],
  [], [$R subset R R^degree R$; $quad S$ simple $==> S = S S^degree S$],
  [indirect equality], [$R = S <==> (forall X. thin X subset R <=> X subset S)$],
  [dom, ran], [$"dom" R eq.delta 1 inter R R^degree, quad "ran" R eq.delta 1 inter R^degree R$],
  [restrict], [$R = ("dom" R) R = R ("ran" R)$],
  [ran laws], [$"ran"(S R) = "ran"(("ran" S) R), quad "ran"(R inter S) = 1 inter S^degree R$],
  [], [$"dom" S = 1 inter S Pi, quad "ran"(R C) = C inter "ran" R$],
  [coreflexives], [$C D = C inter D = D C, quad (R C) inter S = (R inter S) C$],
  [entire], [$1 subset R R^degree$; $quad R inter S$ entire $<==> 1 subset R S^degree$],
  [simple], [$R^degree R subset 1$; #h(0.6em) map = entire + simple, $quad f subset g ==> f = g$],
  [simple dist.], [$S$ simple: $thin R S inter T = (R inter T S^degree) S, quad S(R inter T) = S R inter S T$],
  [converse-free maps], [$S R subset 1 and 1 subset R S ==> S = R^degree$ and $R$ a map],
  [orders], [sym $and$ trans $<==> R = R^degree R$; #h(0.6em) preorder $<==> R = R slash R <==> R = f S f^degree$, $S$ an order],
)

= Tabulations, unit #text(size: 7pt)[(B&dM 4.3)]
#laws(
  [tabulation], [maps $f,g$ with $f^degree g = R, quad f f^degree inter g g^degree = 1$ (jointly monic)],
  [factorisation], [$h^degree k subset R <==> exists!$ map $m$: $h = m f and k = m g$],
  [monic, cover], [$m m^degree = 1$; $quad c^degree c = 1$; $quad$ every map $f = c m$],
  [legs], [$R$ simple $==> f$ monic; $thin R$ entire $==> f$ cover; $thin R$ a map $==> f$ iso],
  [unit], [$R : U -> U ==> R subset 1$; entire map $!_alpha : alpha -> U$; $quad Pi eq.delta ! thin !^degree$],
)
#law([*Horn meta-theorem*: a Horn sentence over $inter, degree$, composition, tabulations, unit holds in
  all unitary tabular allegories $<==>$ it holds in $sans("Rel")$])

= Division, negation #text(size: 7pt)[(B&dM 4.4–4.5)]
#laws(
  [pointwise], [$x thin (T backslash U) thin y <==> forall w. thin w T x => w U y$; #h(0.6em) $slash$ dual],
  [cancel], [$T(T backslash U) subset U, quad (U slash T) thin T subset U$],
  [associate], [$(T U) backslash V = U backslash (T backslash V), quad V slash (U T) = (V slash T) slash U$],
  [maps], [$f(S slash R) = (f S) slash R, quad (S slash R) f^degree = S slash (f R)$; #h(0.6em) $degree$-duals for $backslash$],
  [symmetric div.], [$(R slash S) inter (S slash R)^degree$; $quad Lambda(S) Lambda(R)^degree = (S slash R) inter (R slash S)^degree$],
  [negation], [$not R eq.delta (R => nothing)$; $quad not(R union S) = not R inter not S$],
  [boolean], [$<==> not not R = R <==> R union not R = Pi$ #h(1fr) ($sans("Rel")$ is boolean)],
  [Schröder], [$S R subset T <==> S^degree (not T) subset not R <==> (not T) R^degree subset not S$],
  [neg. division], [$T backslash (not U) = not(T^degree U)$ (always); $quad$ boolean: $T backslash U = not(T^degree (not U))$],
  [lexical], [$R semi S eq.delta R inter (R^degree => S)$ — preorders closed, unit $Pi$],
  [strict part], [$abs(R) eq.delta R inter not R^degree$],
  [Galois, point-free], [orders as $R, S$: $thin f(x) prec.eq y <==> x lt.tri.eq g(y)$ is $R f^degree = g S$],
)

= Power #text(size: 7pt)[(B&dM 4.6)]
#laws(
  [cancel], [$Lambda(R) eps = R$; $quad Lambda(R)$ is the *unique* map with this property],
  [fuse, reflect], [$Lambda(f R) = f Lambda(R), quad Lambda(eps) = 1$],
  [tabular], [$Lambda(R) = (R slash eps) inter (eps slash R)^degree$],
  [existential image], [$E R eq.delta Lambda(eps R)$ #h(1fr) (Freyd's covariant $[dot]$, §1.922); $E 1 = 1$],
  [absorb], [$Lambda(S) (E R) = Lambda(S R)$; $quad$ hence $(E T)(E R) = E(T R)$],
  [naturality], [$(E R) eps = eps R$],
  [power functor], [$P eq.delta E$ on maps; $quad tau$ monic, $Lambda(f) = f tau, quad tau (P f) = f tau$],
  [monad], [$union.big eq.delta E eps : [[alpha]] -> [alpha]$; $quad tau union.big = 1 = (P tau) union.big, quad union.big union.big = (P union.big) union.big$],
  [decompose], [$Lambda(R) = tau (E R), quad E R = (P Lambda R) union.big$],
  [$eps$-cancel], [$(eps slash R) backslash eps = R$],
  [inclusion], [$eps slash eps : [alpha] -> [alpha]$, $x |->$ subsets of $x$; preorder, antisymmetric iff extensional],
)

= Datatypes in allegories #text(size: 7pt)[(B&dM ch. 5)]
#laws(
  [relator], [monotone functor $<==>$ preserves $degree$; relators agreeing on maps are equal],
  [pairing], [$angle.l R, S angle.r eq.delta R pi^degree inter S pi'^degree, quad R times S eq.delta angle.l pi R, pi' S angle.r$],
  [absorb], [$angle.l X,Y angle.r (R times S) = angle.l X R, Y S angle.r$; $quad f angle.l R,S angle.r = angle.l f R, f S angle.r$ ($f$ a map)],
  [projections], [$angle.l R,S angle.r pi = ("dom" S) R, quad angle.l R,S angle.r pi' = ("dom" R) S$ — $times$ is *not* a product],
  [cancel], [$angle.l X,Y angle.r angle.l R,S angle.r^degree = X R^degree inter Y S^degree$],
  [junc], [$[R,S] eq.delta iota^degree R union iota'^degree S = [Lambda R, Lambda S] eps$ — a genuine coproduct],
  [cancel], [$iota [R,S] = R, quad [U,V]^degree [R,S] = U^degree R union V^degree S$],
  [functors], [$(R times S)(U times V) = R U times S V, quad (R + S)(U + V) = R U + S V$],
  [guard], [$tilde.op C$: $thin C inter tilde.op C = nothing, thin C union tilde.op C = 1$; $quad "guard" C eq.delta [C, tilde.op C]^degree$ a map],
  [conditional], [$(C -> R, S) eq.delta ("guard" C)(R + S)$],
  [UP], [$R subset (C -> S,T) <==> C R subset S and (tilde.op C) R subset T$],
  [power relator], [$P R eq.delta ((eps R) slash eps) inter (eps^degree backslash (R eps^degree))$; on maps $P = E$],
  [lax naturality], [$phi : F arrow.hook G eq.delta phi(F R) supset (G R) phi$; $thin <==>$ natural on maps.  E.g. $(P R) eps subset eps R$],
  [Eilenberg–Wright], [$sans("in") thin X = (F X) S <==> X = ⦇S⦈$; $quad Lambda ⦇S⦈ = ⦇Lambda((F eps) S)⦈$],
  [type relators], [$sans("in")(sans("T") R) = F(R, sans("T") R) thin sans("in"), quad (sans("T") R)^degree = sans("T")(R^degree)$; $thin ⦇R⦈$ entire/a map if $R$ is],
  [transposes], [$"cp"(F) eq.delta Lambda(F eps)$; $quad Lambda(R union S) = angle.l Lambda R, Lambda S angle.r "cup"$, same for $inter slash$"cap", $times slash$"cross"],
  [vocabulary], [$"subseq" = ⦇[sans("nil"), sans("cons") union pi']⦈$, $"prefix" = sans("cat")^degree pi$, $"perm" = "bagify" thin "bagify"^degree$, $"partition" = "concat"^degree$],
)

= Recursion, fixed points, closure #text(size: 7pt)[(B&dM ch. 6)]
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
    edge((1,0), (1,1), $eps$, "->")))
#laws(
  [Knaster–Tarski], [$phi$ monotone: least solutions of $phi X subset X$ and $phi X = X$ coincide ($mu phi$); greatest dually],
  [computation], [$phi(mu phi) = mu phi$; $quad mu phi = inter.big {X : phi X subset X}$],
  [induction], [$phi X subset X ==> mu phi subset X$; $quad phi$ continuous: $mu phi = union.big_n phi^n nothing$],
  [cata], [$⦇R⦈$ = the unique $X$ with $X = sans("in")^degree (F X) R$],
  [least, greatest], [$sans("in")^degree (F X) R subset X ==> ⦇R⦈ subset X$, and dually],
  [fuse], [$(F S) T subset R S ==> ⦇T⦈ subset ⦇R⦈ S$],
  [fuse (dual)], [$R S subset (F S) T ==> ⦇R⦈ S subset ⦇T⦈$],
  [compare], [$(F ⦇S⦈) R subset (F ⦇S⦈) S ==> ⦇R⦈ subset ⦇S⦈$],
  [rolling], [$mu(X |-> phi(psi X)) = phi(mu(X |-> psi(phi X)))$],
  [diagonal], [$mu(X |-> mu(Y |-> phi(X,Y))) = mu(X |-> phi(X,X))$],
  [inductive], [$R$ inductive $eq.delta forall X. thin X slash R subset X ==> Pi subset X$],
  [], [$S$ inductive and ($R subset S$ or $R R subset S R$) $==> R$ inductive; $quad S <==> S^+$; meets too],
  [well-founded], [$forall X. thin X subset R X ==> X = nothing$; inductive $==>$ wf, conversely in boolean; $f R f^degree$ wf if $R$ wf],
  [membership], [$"mem" sans("Id") = 1, thin "mem" K_beta = nothing, thin "mem"(F + G) = ["mem" F, "mem" G]$],
  [], [$"mem"(F times G) = pi("mem" F) union pi'("mem" G)$, $thin$ for $F(G dot)$: $("mem" F)("mem" G)$, $thin "mem" [dot] = eps$],
  [largest lax], [$(F R)("mem" F) subset ("mem" F) R$; $quad sans("in")^degree ("mem" F)$ inductive (immediate subterm)],
  [unique fixpoint], [$S ("mem" F)$ inductive $==> X = S (F X) R$ has a unique solution; entire if $R, S$ entire],
  [functional], [$g("mem" F)$ inductive $==>$ the unique solution of $X = g (F X) f$ is a map],
  [converse cata], [$"ran" R = 1$ and $R f subset (F f) sans("in") ==> f^degree = ⦇R⦈$],
  [closure], [$R^* = mu(X |-> 1 union R X) = mu(X |-> 1 union X R)$; unique fixed point iff $R$ inductive],
  [], [$S R^* = mu(X |-> S union X R), quad (R union S)^* = (R^* S)^* R^*, quad R^* = ⦇[1,1]⦈^degree ⦇[1,R]⦈$],
  [sorting], [$"sort" subset "perm"("ordered" R)$, $R$ a connected preorder ($R union R^degree = Pi$)],
  [], [$("ordered" R)("ordered" S) = "ordered"(R inter S)$; sorts emerge by cata-fusion + hylo],
)
#theorem("Hylomorphism", numbering: none)[
  $ ⦇S⦈^degree ⦇R⦈ = mu (X |-> S^degree (F X) R) $
  Divide ($S^degree$), conquer ($F X$), combine ($R$); the virtual data structure is $mu F$.
  Coproduct split ($F = G + H$): $mu(X |-> S_1^degree (G X) R_1 union S_2^degree (H X) R_2)$.
  Hylos of simple parts are simple.
]

= Optimisation: min & max #text(size: 7pt)[(B&dM 7.1)]
#laws(
  [definition], [$min R eq.delta eps inter (eps^degree backslash R) : [alpha] -> alpha, quad max R eq.delta min R^degree$],
  [UP], [$X subset min R <==> X subset eps and eps^degree X subset R$],
  [divide by $eps$], [$tau (eps^degree backslash R) = R, quad Lambda(S)(eps^degree backslash R) = S^degree backslash R, quad union.big (eps^degree backslash R) = eps^degree backslash (eps^degree backslash R)$],
  [singleton], [$tau (min R) = 1 inter R$],
  [transpose], [$Lambda(S)(min R) = S inter (S^degree backslash R)$ #h(1fr) (= AoPA shrink $S harpoon.tr R$)],
  [UP], [$X subset Lambda(S)(min R) <==> X subset S and S^degree X subset R$],
  [context], [$Lambda(S)(min R) = Lambda(S)(min (R inter S^degree S))$],
  [image], [$(E S)(min R) = eps S inter ((eps S)^degree backslash R)$],
  [maps], [$(P f)(min R) = (min(f R f^degree)) f$],
  [relations], [$(P S)(min R) subset eps S inter (eps^degree backslash (S R))$, $thin =$ if $R$ reflexive],
  [union], [$R$ preorder: $(P(min R))(min R) subset union.big (min R) = (P("dom" min R)) union.big (min R)$],
  [meet], [$min(R inter S) = min R inter min S$],
  [reflexive], [$R = eps^degree (min R)$; $quad min R subset min S <==> R subset S$ ($S$ reflexive too)],
  [preorder], [$min R = eps inter (min R) R, quad Lambda(R)(max R) = R inter R^degree$],
  [pairs], [$angle.l S(min R), T(min R) angle.r subset Lambda angle.l S,T angle.r (min(R times R))$],
  [lexical], [$R$ reflexive, $S$ preorder: $thin Lambda(min S)(min R) = min(S semi R)$],
  [minimal elts.], [$"mnl" R eq.delta min(R^degree => R)$; $quad min R subset "mnl" R$, $=$ iff $R$ connected preorder],
  [well-bounded], [$"dom" eps = "dom"(min R) <==> abs(R)$ wf $<==> eps subset (min R) R^degree$],
)

= Greedy #text(size: 7pt)[(B&dM 7.2)]
#laws(
  [monotonic], [$S$ *monotonic on* $R eq.delta (F R) S subset S R$],
  [for maps], [$<==> f^degree (F R) f subset R <==> F R subset f R f^degree$; $quad$ on $R <==>$ on $R^degree$ (maps only)],
  [distributivity], [$f$ monotonic on $R <==> (F(min R)) f subset Lambda((F eps) f)(min R)$],
)
#theorem("Greedy", numbering: none)[
  $R$ a preorder, $S$ monotonic on $R^degree$:
  $ ⦇Lambda(S)(min R)⦈ thin subset thin Lambda(⦇S⦈)(min R) $
  Max form ($S$ monotonic on $R$): $⦇Lambda(S)(max R)⦈ subset Lambda(⦇S⦈)(max R)$. Context: monotonicity
  on $R^degree inter ⦇S⦈ ⦇S⦈^degree$ suffices. Variant: $f$ monotonic on $R$, $f subset Lambda(S)(min R)
  ==> ⦇f⦈ subset Lambda(⦇S⦈)(min R)$.
]
#law([optimal substeps: $S$ monotonic on $R^degree ==> (min(F R)) Lambda(S)(min R) subset (E S)(min R)$])

= Thinning #text(size: 7pt)[(B&dM 8.1, 8.3)]
#laws(
  [definition], [$"thin" Q eq.delta (eps slash eps) inter (eps^degree backslash (Q eps^degree)) : [alpha] -> [alpha]$],
  [], [shrink a set, keeping a $Q$-bound for each dropped element],
  [UP], [$X subset Lambda(S)("thin" Q) <==> X eps subset S and S^degree X subset Q eps^degree$],
  [order], [$1 subset "thin" Q$; $quad "thin" 1 = 1$],
  [introduction], [$Q subset R$ (preorders) $==> min R = ("thin" Q)(min R)$],
  [elimination], [$(min Q) tau subset "thin" Q$; $quad R inter S^degree S subset Q ==> Lambda(S)(min R) tau subset Lambda(S)("thin" Q)$],
  [singleton], [$min R = ("thin" R) tau^degree$],
  [context], [$Lambda(S)("thin" Q) = Lambda(S)("thin"(Q inter S^degree S))$],
  [union], [$(P("thin" Q)) union.big subset union.big ("thin" Q)$],
  [minimal elts.], [$Q$ well-supported $==> Lambda("mnl" Q) subset "thin" Q$],
)
#theorem("Thinning", numbering: none)[
  $Q$ a preorder, $S$ monotonic on $Q^degree$:
  $ ⦇Lambda((F eps) S)("thin" Q)⦈ thin subset thin Lambda(⦇S⦈)("thin" Q) $
  With $Q subset R$, postcompose $min R$: $⦇Lambda((F eps) S)("thin" Q)⦈(min R) subset Lambda(⦇S⦈)(min R)$
  — keep a Pareto front of partial solutions, pick the optimum at the end.
]
#laws(
  [sorted lists], [$"sort" P eq.delta "setify"^degree ("ordered" P)$; $quad ("sort" P)("thinlist" Q) subset ("thin" Q)("sort" P)$],
  [merge], [$(("sort" P) times ("sort" P))("merge" P) subset "cup"("sort" P)$],
  [connected $Q$], [$"thinlist" Q thin x = ["minlist" Q thin x]$],
)
#law([binary thinning: $S = f_1 p_1 union f_2 p_2$ ($p_i$ coreflexive, $f_i p_i$ monotonic on $Q^degree$, $f_i$
  monotonic on a connected preorder $P$, $Q subset R$): fold "apply both steps to sorted lists, merge by $P$,
  bump-thin by $Q$", finish with minlist $R$ — refines $Lambda(⦇S⦈)(min R)$ on lists])

= Dynamic programming #text(size: 7pt)[(B&dM 9.1)]
#theorem("Dynamic programming", numbering: none)[
  $h$ a map monotonic on preorder $R$; $thin cal(H) eq.delta ⦇T⦈^degree ⦇h⦈$:
  $ mu (X |-> Lambda(T^degree) thin P((F X) h) thin (min R)) thin subset thin Lambda(cal(H))(min R) $
  With thinning: insert $"thin" Q$ after $Lambda(T^degree)$, provided $Q$ is a preorder with
  $Q^degree (F cal(H)) h subset (F cal(H)) h R^degree$. Decompose all ways, solve subproblems, thin, keep an optimum.
]
#laws(
  [uniqueness], [the fixed point is unique if $T^degree ("mem" F)$ is inductive; entire (an implementable recursion) if $Lambda(T^degree)$ yields finite non-empty sets and $R$ is a connected preorder],
  [cost], [$R = "cost" med "leq" med "cost"^degree$, $thin h med "cost" = (F "cost") k$, $thin (F "leq") k subset k med "leq" ==> h$ monotonic on $R$],
  [finding $Q$], [preorders $U, V$ with $F(U,R) h subset h R$ and $V^degree cal(H) subset cal(H) R^degree ==> Q = F(U,V)$ works (often $U = Pi$)],
  [greedy from DP], [bifunctor conditions collapse the DP recursion to a greedy sweep (B&dM ch. 10)],
)
]
