// Allegory / Algebra-of-Programming cheatsheet (2 pages).
// Conventions: Freyd–Scedrov ("Categories, Allegories").  Composition is written by
// JUXTAPOSITION in diagram order: RS means "first R, then S" (B&dM's S·R).
// Sources: Bird & de Moor, "Algebra of Programming", chs. 2–9 (laws, theorems, exercises),
// mirrored into diagram order; division slashes flip under the mirror (see Conventions).
#import "@preview/dvdtyp:1.0.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set page(margin: (x: 1.0cm, y: 1.1cm))
#show: dvdtyp.with(
  title: "Allegories & Algebra of Programming",
  subtitle: [cheatsheet — Freyd conventions; B&dM chs. 2–9: laws, theorems, exercises],
  author: none,
  accent: colors.at(6),
)

#set text(size: 8pt)
#set par(leading: 0.52em, spacing: 0.85em)
#show heading: set text(size: 9pt)
#show heading: set block(above: 1.05em, below: 0.6em)
#show figure.where(kind: "thmenv"): set block(breakable: false)

// one law per line
#let law(m) = block(spacing: 0.6em, width: 100%)[#m]
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

= Maps: products, sums, folds #text(size: 7pt)[(ch. 2)]
#law([terminal $bold(1)$: $thin ! : alpha -> bold(1)$ the unique map; fusion $f! = thin!$])
#law([product UP *(2.4)*: $h = angle.l f, g angle.r <==> h pi = f and h pi' = g$])
#law([cancel $angle.l f,g angle.r pi = f$, $angle.l f,g angle.r pi' = g$; #h(0.4em) reflect $angle.l pi, pi' angle.r = 1$; #h(0.4em) fuse $m angle.l h,k angle.r = angle.l m h, m k angle.r$])
#law([$f times g eq.delta angle.l pi f, pi' g angle.r$, $quad (f times g)(h times k) = f h times g k$, $quad$ absorb $angle.l p,q angle.r (f times g) = angle.l p f, q g angle.r$])
#law([coproduct UP *(2.9)*: $h = [f,g] <==> iota h = f and iota' h = g$; $quad iota [f,g] = f$, $[iota, iota'] = 1$])
#law([fuse $[h,k] m = [h m, k m]$; $quad f+g eq.delta [f iota, g iota']$; $quad (h+k)[f,g] = [h f, k g]$])
#law([exchange (Ex 2.27): $angle.l [f,g], [h,k] angle.r = [angle.l f,h angle.r, angle.l g,k angle.r]$])
#law([cata UP *(2.10)*: $h = ⦇f⦈ <==> sans("in") thin h = (F h) f$; $quad$ reflect *(2.11)*: $⦇sans("in")⦈ = 1$])
#law([cata fusion *(2.12)*: $f h = (F h) g ==> ⦇f⦈ h = ⦇g⦈$; $quad$ Ex 2.35: $⦇g f⦈ = ⦇(F f) g⦈ f$])
#law([Lambek: $sans("in")$ is iso, $sans("in")^(-1) = ⦇F sans("in")⦈$])
#law([type functor *(2.13)*: $sans("T") f eq.delta ⦇F(f,1) thin sans("in")⦈$ (lists: map); $quad sans("in") (sans("T") f) = F(f, sans("T") f) thin sans("in")$])
#law([map fusion *(2.14)*: $(sans("T") g) ⦇h⦈ = ⦇F(g,1) thin h⦈$])

= Program calculus #text(size: 7pt)[(ch. 3)]
#law([banana-split: $angle.l ⦇h⦈, ⦇k⦈ angle.r = ⦇ angle.l (F pi) h, (F pi') k angle.r ⦈$])
#law([Fokkinga (Ex 3.8): $sans("in") f = (F angle.l f,g angle.r) h and sans("in") g = (F angle.l f,g angle.r) k <==> angle.l f,g angle.r = ⦇angle.l h,k angle.r⦈$])
#law([paramorphism (Ex 3.4): $sans("in") f = (F angle.l f, ⦇h⦈ angle.r) g ==> f = ⦇angle.l g, (F pi') h angle.r⦈ pi$])
#law([triangle $"tri" f eq.delta ⦇F(1, sans("T") f) thin sans("in")⦈$; Horner: $g f = F(f,f) g ==> ("tri" f) ⦇g⦈ = ⦇F(1,f) g⦈$])
#law([conditional *(3.2–3.5)*: $(p -> f, g) eq.delta p? thin [f,g]$; $quad (p -> f,g) h = (p -> f h, g h)$])
#law([$h (p -> f, g) = (h p -> h f, h g), quad (p -> f, f) = f$])
#law([filter (Ex 3.30): $(sans("T") f)("filter" p) = ("filter"(f p))(sans("T") f)$])
#law([curry UP: $g = "curry" f <==> (g times 1) "apply" = f$; cancel $("curry" f times 1) "apply" = f$])
#law([reflect $"curry"("apply") = 1$; $quad$ fuse $g ("curry" f) = "curry"((g times 1) f)$])
#law([structural recursion (Thm 3.1): if $phi (G(h times 1)) = (F h times 1) phi$ then
  $(sans("in") times 1) f = phi (G f) h$ has the unique solution $f = (⦇"curry"(phi (G "apply") h)⦈ times 1) "apply"$])

= Allegory #text(size: 7pt)[(4.1–4.2; Freyd 2.11–2.16)]
#law([$(R^degree)^degree = R, quad (R S)^degree = S^degree R^degree, quad (R inter S)^degree = R^degree inter S^degree, quad R subset S <==> R^degree subset S^degree$])
#law([$R subset R', thin S subset S' ==> R S subset R' S'$; $quad R(S inter T) subset R S inter R T$])
#law([*modular law (4.6–4.8)*: $thin R S inter T subset (R inter T S^degree) S subset (R inter T S^degree)(S inter R^degree T)$])
#law([modular identity (Ex 4.5): $R inter T S = R inter (T inter R S^degree) S$; $quad R subset R R^degree R$ *(4.10)*])
#law([indirect equality: $R = S <==> (forall X. thin X subset R <=> X subset S)$])
#law([$"dom" R eq.delta 1 inter R R^degree$, $"ran" R eq.delta 1 inter R^degree R$; $quad R = ("dom" R) R = R ("ran" R)$])
#law([UP *(4.11)*: $"ran" R subset C <==> R subset R C$; $quad "ran"(S R) = "ran"(("ran" S) R)$ *(4.14)*])
#law([$"ran"(R inter S) = 1 inter S^degree R$ *(4.15)*; $quad "dom" S = 1 inter S Pi$ (Ex 4.27); $"ran"(R C) = C inter "ran" R$])
#law([coreflexives: $C D = C inter D = D C$; $quad (R C) inter S = (R inter S) C$ (Ex 4.10)])
#law([entire: $1 subset R R^degree$; simple: $R^degree R subset 1$; map = both; $quad R inter S$ entire $<==> 1 subset R S^degree$ *(4.18)*])
#law([$S$ simple: $R S inter T = (R inter T S^degree) S$ *(4.16)*, $thin S(R inter T) = S R inter S T$ *(4.17)*, $thin S = S S^degree S$])
#law([shunting *(4.19–20)*: $thin f^degree R subset S <==> R subset f S, quad R f subset S <==> R subset S f^degree$; $quad f subset g => f = g$])
#law([Prop 4.1: $S R subset 1 and 1 subset R S ==> S = R^degree$ and $R$ a map])
#law([sym $and$ trans $<==> R = R^degree R$ (Ex 4.14); $quad$ preorder $<==> R = R slash R <==> R = f S f^degree$, $S$ an order (Ex 4.49)])

= Tabulations, unit #text(size: 7pt)[(4.3; Freyd 2.14–2.16)]
#law([tabulation of $R$: maps $f,g$ with $f^degree g = R, thin f f^degree inter g g^degree = 1$ (jointly monic)])
#law([Prop 4.2: $h^degree k subset R <==> exists!$ map $m$: $h = m f and k = m g$ — spans factor through tabulations])
#law([monic map: $m m^degree = 1$; cover: $c^degree c = 1$; every map $f = c m$ (Ex 4.20)])
#law([$R$ simple $==> f$ monic; $R$ entire $==> f$ cover; $R$ a map $==> f$ iso (Ex 4.21–23)])
#law([unit $U$: $R : U -> U ==> R subset 1$; entire $!_alpha : alpha -> U$; $quad Pi eq.delta ! thin !^degree$ largest])
#law([Ex 4.24: $k^degree h subset S R <==> exists$ entire $Q$: $k^degree Q subset S and Q^degree h subset R$])
#law([*Horn meta-theorem*: a Horn sentence over $inter, degree$, composition, tabulations, unit holds in
  all unitary tabular allegories $<==>$ it holds in $sans("Rel")$])

= Joins, division, negation #text(size: 7pt)[(4.4–4.5; Freyd 2.31–2.35)]
#law([join UP: $union.big H subset X <==> forall R in H. thin R subset X$; $quad$ composition, meet, $degree$ distribute over $union.big$])
#law([$nothing R = nothing = R nothing$; $quad R(S union T) = R S union R T, quad R inter (S union T) = (R inter S) union (R inter T)$])
#law([implication UP: $X subset (R => S) <==> X inter R subset S$; $quad R inter (R => S) = R inter S$])
#law([$(R => (S => T)) = ((R inter S) => T), quad (R => (S inter T)) = (R => S) inter (R => T)$])
#law([$g (R => S) f^degree = (g R f^degree) => (g S f^degree)$ (Ex 4.33)])
#law([left UP: $T X subset U <==> X subset T backslash U, quad x thin (T backslash U) thin y <==> forall w. thin w T x => w U y$])
#law([right UP: $X T subset U <==> X subset U slash T$; $quad$ cancel: $T(T backslash U) subset U, thin (U slash T) T subset U$])
#law([$(T U) backslash V = U backslash (T backslash V), quad V slash (U T) = (V slash T) slash U$])
#law([$(R union S) backslash T = (R backslash T) inter (S backslash T), quad R backslash (S inter T) = (R backslash S) inter (R backslash T)$])
#law([maps (Ex 4.35): $f(S slash R) = (f S) slash R, quad (S slash R) f^degree = S slash (f R)$; $degree$-duals for $backslash$])
#law([symmetric division: $(R slash S) inter (S slash R)^degree$; $quad Lambda(S) Lambda(R)^degree = (S slash R) inter (R slash S)^degree$ (Ex 4.48)])
#law([subtraction (Ex 4.30): $R minus S subset X <==> R subset S union X$; $thin R union S = R union (S minus R)$])
#law([$R minus (S union T) = (R minus S) minus T, quad (R union S) minus T = (R minus T) union (S minus T)$])
#law([lexical: $R semi S eq.delta R inter (R^degree => S)$ — preorders closed, unit $Pi$; strict part $abs(R) eq.delta R inter not R^degree$])
#law([$not R eq.delta (R => nothing)$; De Morgan $not(R union S) = not R inter not S$; boolean $<==> not not R = R <==> R union not R = Pi$])
#law([*Schröder* (Ex 4.43): $S R subset T <==> S^degree (not T) subset not R <==> (not T) R^degree subset not S$])
#law([$T backslash (not U) = not(T^degree U)$ (always); boolean: $T backslash U = not(T^degree (not U))$ *(4.21–22)*])
#law([Galois: $f(x) prec.eq y <==> x lt.tri.eq g(y)$; point-free (orders as $R,S$): $R f^degree = g S$.
  Division, $=>$, $minus$ are the archetypes])

= Power #text(size: 7pt)[(4.6; Freyd 2.41–2.42)]
#law([UP: for $R : gamma -> alpha$, $Lambda(R) : gamma -> [alpha]$ is the unique map with $Lambda(R) thin eps = R$])
#law([fusion: $Lambda(f R) = f Lambda(R)$; $quad$ reflect $Lambda(eps) = 1$; $quad$ tabular: $Lambda(R) = (R slash eps) inter (eps slash R)^degree$])
#law([$E R eq.delta Lambda(eps R)$ existential image (Freyd's covariant $[dot]$, 1.922); $E 1 = 1$])
#law([absorption: $Lambda(S) (E R) = Lambda(S R)$; hence $(E T)(E R) = E(T R)$; $quad (E R) eps = eps R$])
#law([$P eq.delta E$ on maps ($P f$ = image map); $quad tau$ monic, $Lambda(f) = f tau$, $tau (P f) = f tau$])
#law([$union.big eq.delta E eps : [[alpha]] -> [alpha]$; $quad tau union.big = 1 = (P tau) union.big$, $union.big union.big = (P union.big) union.big$ — $([dot], tau, union.big)$ a monad])
#law([Ex 4.47: $Lambda(R) = tau (E R)$, $thin E R = (P Lambda R) union.big$; $quad$ Ex 4.50: $(eps slash R) backslash eps = R$])
#law([$eps slash eps : [alpha] -> [alpha]$, $x |-> y subset.eq x$ (its converse $eps^degree backslash eps^degree$: supersets); preorder;
  antisymmetric in a unitary tabular allegory (extensionality)])
#law([wlp $R eq.delta Lambda(eps slash R)$; $quad$ wlp$(S R) = ("wlp" R)("wlp" S)$ (Ex 4.52)])

= Datatypes in allegories #text(size: 7pt)[(ch. 5)]
#law([relator = monotone functor $<==>$ preserves $degree$: $(F R)^degree = F(R^degree)$ (Thm 5.1); $F f$ a map])
#law([relators agreeing on maps are equal (Cor 5.1); $quad F("dom" R) = "dom"(F R)$, $F(C inter D) = F C inter F D$])
#law([$angle.l R, S angle.r eq.delta R pi^degree inter S pi'^degree, quad R times S eq.delta angle.l pi R, pi' S angle.r$; $quad (R times S)(U times V) = R U times S V$])
#law([absorb *(5.3)*: $angle.l X,Y angle.r (R times S) = angle.l X R, Y S angle.r$; $quad f angle.l R,S angle.r = angle.l f R, f S angle.r$ ($f$ a map, Ex 5.9)])
#law([*(5.6–7)*: $angle.l R,S angle.r pi = ("dom" S) R, thin angle.l R,S angle.r pi' = ("dom" R) S$ — $times$ is *not* a categorical product])
#law([cancel *(5.8)*: $angle.l X,Y angle.r angle.l R,S angle.r^degree = X R^degree inter Y S^degree$; $quad angle.l R,S angle.r^degree angle.l P,Q angle.r subset R^degree P times S^degree Q$ (Ex 5.7)])
#law([$[R,S] eq.delta iota^degree R union iota'^degree S = [Lambda R, Lambda S] eps$; $quad R + S eq.delta [R iota, S iota']$ — a genuine coproduct])
#law([$iota [R,S] = R$; $quad (R+S)(U+V) = R U + S V$; $quad$ cancel *(5.11)*: $[U,V]^degree [R,S] = U^degree R union V^degree S$])
#law([conditionals (Ex 5.17): $tilde.op C$ complement ($C inter tilde.op C = nothing$, $C union tilde.op C = 1$); $"guard" C eq.delta [C, tilde.op C]^degree$ a map])
#law([$(C -> R, S) eq.delta ("guard" C)(R + S)$; $quad R subset (C -> S,T) <==> C R subset S and (tilde.op C) R subset T$])
#law([power relator: $P R eq.delta ((eps R) slash eps) inter (eps^degree backslash (R eps^degree))$; on maps $P = E$; $(P("dom" R))(E R) subset P R$])
#law([$eps$ lax natural: $(P R) eps subset eps R$; $quad$ lax $phi : F arrow.hook G$: $phi(F R) supset (G R) phi$ $<==>$ natural on maps (Thm 5.2)])
#law([*Eilenberg–Wright (5.12)*: $sans("in") thin X = (F X) S <==> X = ⦇S⦈$; $quad Lambda ⦇S⦈ = ⦇Lambda((F eps) S)⦈$])
#law([type relators: $sans("in")(sans("T") R) = F(R, sans("T") R) thin sans("in")$, $(sans("T") R)^degree = sans("T")(R^degree)$; $⦇R⦈$ entire/a map if $R$ is])
#law([combinatorics: $"cp"(F) eq.delta Lambda(F eps)$; $Lambda(R union S) = angle.l Lambda R, Lambda S angle.r "cup"$, same for $inter$/"cap", $times$/"cross"])
#law([$"subseq" = ⦇[sans("nil"), sans("cons") union pi']⦈$, $"prefix" = sans("cat")^degree pi$, $"perm" = "bagify" thin "bagify"^degree$, $"partition" = "concat"^degree$;
  E–W turns each $Lambda(dot)$ into an executable fold (inits, tails, splits, perms, …)])

= Recursion, fixed points, closure #text(size: 7pt)[(ch. 6)]
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
#law([Knaster–Tarski (Thm 6.1): $phi$ monotone $==>$ least solutions of $phi X subset X$ and $phi X = X$
  coincide ($mu phi$); greatest dually. $mu phi = inter.big {X : phi X subset X}$; $phi(mu phi) = mu phi$])
#law([induction: $phi X subset X ==> mu phi subset X$; $quad (forall X. thin phi X subset psi X) ==> mu phi subset mu psi$])
#law([Kleene (Ex 6.3): $phi$ continuous $==> mu phi = union.big_n phi^n nothing$])
#law([$⦇R⦈$ = the unique $X$ with $X = sans("in")^degree (F X) R$; *(6.2–3)*: $sans("in")^degree (F X) R subset X => ⦇R⦈ subset X$, and dually])
#law([cata fusion *(6.4–5)*: $(F S) T subset R S ==> ⦇T⦈ subset ⦇R⦈ S$; $quad R S subset (F S) T ==> ⦇R⦈ S subset ⦇T⦈$])
#law([Ex 6.7: $(F ⦇S⦈) R subset (F ⦇S⦈) S ==> ⦇R⦈ subset ⦇S⦈$])
#law([rolling: $mu(X |-> phi(psi X)) = phi(mu(X |-> psi(phi X)))$; diagonal: $mu(X |-> mu(Y |-> phi(X,Y))) = mu(X |-> phi(X,X))$])
#law([inductive $R$: $forall X. thin X slash R subset X ==> Pi subset X$; $quad S$ inductive, $R subset S ==> R$ inductive; $S <==> S^+$])
#law([$S$ inductive, $R R subset S R ==> R$ inductive (Ex 6.13); meets of inductives are inductive (Ex 6.15)])
#law([well-founded (boolean): $forall X. thin X subset R X ==> X = nothing$; inductive $==>$ wf (conversely in boolean); $R$ wf $==> f R f^degree$ wf])
#law([membership $"mem" F : F alpha -> alpha$: $"mem" sans("Id") = 1$, $"mem" K_beta = nothing$, $"mem"(F + G) = ["mem" F, "mem" G]$,
  $"mem"(F times G) = pi("mem" F) union pi'("mem" G)$, composite $F(G dot)$: $("mem" F)("mem" G)$, $"mem" [dot] = eps$])
#law([mem = largest lax natural $F arrow.hook sans("Id")$: $(F R)("mem" F) subset ("mem" F) R$; $quad sans("in")^degree ("mem" F)$ inductive (immediate subterm)])
#law([unique fixed points (Thm 6.3): $S ("mem" F)$ inductive $==> X = S (F X) R$ has a unique solution; entire if $R, S$ entire])
#law([Cor 6.2: $g("mem" F)$ inductive $==>$ the unique solution of $X = g (F X) f$ is a map])
#law([Thm 6.4: $"ran" R = 1$ and $R f subset (F f) sans("in") ==> f^degree = ⦇R⦈$ (partition-style converses)])
#law([closure UP: $R subset X <==> R^* subset X$ ($X$ preorders); $R^* = mu(X |-> 1 union R X) = mu(X |-> 1 union X R)$])
#law([$S R^* = mu(X |-> S union X R)$; unique fixed point iff $R$ inductive; $(R union S)^* = (R^* S)^* R^*$ (Ex 6.36)])
#law([$R^* = ⦇[1,1]⦈^degree ⦇[1,R]⦈$ (Ex 6.33); $quad C$ coreflexive, $R C = C ==> R^* = (R(tilde.op C))^*$ (Ex 6.37)])
#law([sorting spec *(6.6)*: $"sort" subset "perm"("ordered" R)$, $R$ a connected preorder ($R union R^degree = Pi$);
  $("ordered" R)("ordered" S) = "ordered"(R inter S)$ (Ex 6.24); insertion/selection/quicksort emerge by
  cata-fusion + the hylomorphism theorem])

#theorem("Hylomorphism — B&dM 6.2", numbering: none)[
  $ ⦇S⦈^degree ⦇R⦈ = mu (X |-> S^degree (F X) R) $
  Divide ($S^degree$), conquer ($F X$), combine ($R$); the virtual data structure is $mu F$.
  Coproduct split (Cor 6.1, $F = G + H$): $mu(X |-> S_1^degree (G X) R_1 union S_2^degree (H X) R_2)$.
  Hylos of simple parts are simple (Ex 6.10).
]

= Optimisation: min & max #text(size: 7pt)[(7.1)]
#law([$min R eq.delta eps inter (eps^degree backslash R) : [alpha] -> alpha, quad max R eq.delta min R^degree$])
#law([UP: $X subset min R <==> X subset eps and eps^degree X subset R$])
#law([divide by $eps$ *(7.1–3)*: $tau (eps^degree backslash R) = R$, $thin Lambda(S)(eps^degree backslash R) = S^degree backslash R$, $thin union.big (eps^degree backslash R) = eps^degree backslash (eps^degree backslash R)$])
#law([singleton *(7.4)*: $tau (min R) = 1 inter R$; $quad$ *(7.5)*: $Lambda(S)(min R) = S inter (S^degree backslash R)$])
#law([UP of (7.5): $thin X subset Lambda(S)(min R) <==> X subset S and S^degree X subset R$; AoPA shrink $S harpoon.tr R$ is exactly (7.5)])
#law([context *(7.6)*: $Lambda(S)(min R) = Lambda(S)(min (R inter S^degree S))$; $quad (E S)(min R) = eps S inter ((eps S)^degree backslash R)$ *(7.7)*])
#law([maps *(7.8)*: $(P f)(min R) = (min(f R f^degree)) f$; $quad$ *(7.10)*: $(P S)(min R) subset eps S inter (eps^degree backslash (S R))$, `=` if $R$ reflexive *(7.9)*])
#law([union *(7.11–12)*: $R$ preorder: $(P(min R))(min R) subset union.big (min R)$; $= (P("dom" min R)) union.big (min R)$])
#law([$min(R inter S) = min R inter min S$ (Ex 7.6); $quad R$ reflexive: $R = eps^degree (min R)$ (Ex 7.9)])
#law([$R, S$ reflexive: $min R subset min S <==> R subset S$ (Ex 7.10); $quad min R$ simple $<==> R$ antisymmetric (Ex 7.11)])
#law([$R$ preorder: $min R = eps inter (min R) R$ (Ex 7.12); $quad Lambda(R)(max R) = R inter R^degree$ (Ex 7.14)])
#law([pairs (Ex 7.15): $angle.l S(min R), T(min R) angle.r subset Lambda angle.l S,T angle.r (min(R times R))$])
#law([lexical (Ex 7.16): $R$ reflexive, $S$ preorder: $Lambda(min S)(min R) = min(S semi R)$])
#law([minimal elements: $"mnl" R eq.delta min(R^degree => R)$; $min R subset "mnl" R$, `=` iff $R$ connected preorder (Ex 7.19–20)])
#law([well-bounded $R$: $"dom" eps = "dom"(min R)$ $<==> abs(R)$ wf (Ex 7.26) $<==> eps subset (min R) R^degree$ (Ex 7.28)])

= Greedy #text(size: 7pt)[(7.2)]
#law([$S$ *monotonic on* $R eq.delta (F R) S subset S R$; for a map $f$: $<==> f^degree (F R) f subset R <==> F R subset f R f^degree$; on $R <==>$ on $R^degree$ (maps only)])
#law([Thm 7.1: $f$ monotonic on $R <==> f$ distributes: $(F(min R)) f subset Lambda((F eps) f)(min R)$])
#theorem("Greedy — B&dM 7.2", numbering: none)[
  $R$ a preorder, $S$ monotonic on $R^degree$:
  $ ⦇Lambda(S)(min R)⦈ thin subset thin Lambda(⦇S⦈)(min R) $
  Max form ($S$ monotonic on $R$): $⦇Lambda(S)(max R)⦈ subset Lambda(⦇S⦈)(max R)$. Context: monotonicity
  on $R^degree inter ⦇S⦈ ⦇S⦈^degree$ suffices. Variant (Ex 7.37): $f$ monotonic on $R$, $f subset Lambda(S)(min R)
  ==> ⦇f⦈ subset Lambda(⦇S⦈)(min R)$.
]
#law([Ex 7.38: $S$ monotonic on $R^degree$: $(min(F R)) Lambda(S)(min R) subset (E S)(min R)$])
#law([initial algebra *(7.13)*: $sans("in")$ monotonic on $R ==> F(1, min R) thin sans("in") subset "cp"(P sans("in"))(min R)$; forces $R$ reflexive (Ex 7.34)])

= Thinning #text(size: 7pt)[(8.1, 8.3)]
#law([$"thin" Q eq.delta (eps slash eps) inter (eps^degree backslash (Q eps^degree)) : [alpha] -> [alpha]$ *(8.1)* — shrink, keeping a $Q$-bound for each dropped element])
#law([UP: $X subset Lambda(S)("thin" Q) <==> X eps subset S and S^degree X subset Q eps^degree$])
#law([$1 subset "thin" Q$; preorder if $Q$ is; $Q subset R ==> "thin" Q subset "thin" R$; $"thin" 1 = 1$ (Ex 8.1)])
#law([introduction: $Q subset R$ (preorders) $==> min R = ("thin" Q)(min R)$])
#law([elimination *(8.2–3)*: $(min Q) tau subset "thin" Q$; $thin R inter S^degree S subset Q ==> Lambda(S)(min R) tau subset Lambda(S)("thin" Q)$])
#law([$min R = ("thin" R) tau^degree$ (Ex 8.5); $quad$ context: $Lambda(S)("thin" Q) = Lambda(S)("thin"(Q inter S^degree S))$ (Ex 8.6)])
#law([union *(8.4)*: $(P("thin" Q)) union.big subset union.big ("thin" Q)$; $quad Q$ well-supported: $Lambda("mnl" Q) subset "thin" Q$ (Ex 8.9)])
#theorem("Thinning — B&dM 8.1", numbering: none)[
  $Q$ a preorder, $S$ monotonic on $Q^degree$:
  $ ⦇Lambda((F eps) S)("thin" Q)⦈ thin subset thin Lambda(⦇S⦈)("thin" Q) $
  Cor 8.1 ($Q subset R$): postcompose $min R$: $⦇Lambda((F eps) S)("thin" Q)⦈(min R) subset Lambda(⦇S⦈)(min R)$
  — keep a Pareto front of partial solutions, pick the optimum at the end.
]
#law([lists: $"sort" P eq.delta "setify"^degree ("ordered" P)$; $("sort" P)("thinlist" Q) subset ("thin" Q)("sort" P)$ *(8.6)*])
#law([$(("sort" P) times ("sort" P))("merge" P) subset "cup"("sort" P)$ *(8.10)*; connected $Q$: $"thinlist" Q thin x = ["minlist" Q thin x]$ *(8.5)*])
#law([binary thinning (Thm 8.2): $S = f_1 p_1 union f_2 p_2$ ($p_i$ coreflexive, $f_i p_i$ monotonic on $Q^degree$, $f_i$
  monotonic on a connected preorder $P$, $Q subset R$): fold "apply both steps to sorted lists, merge by $P$,
  bump-thin by $Q$", finish with minlist $R$ — refines $Lambda(⦇S⦈)(min R)$ on lists])

= Dynamic programming #text(size: 7pt)[(9.1)]
#theorem("Dynamic programming — B&dM 9.1/9.2", numbering: none)[
  $h$ a map monotonic on preorder $R$; $thin cal(H) eq.delta ⦇T⦈^degree ⦇h⦈$:
  $ mu (X |-> Lambda(T^degree) thin P((F X) h) thin (min R)) thin subset thin Lambda(cal(H))(min R) $
  With thinning (9.2): insert $"thin" Q$ after $Lambda(T^degree)$, provided $Q$ is a preorder with
  $Q^degree (F cal(H)) h subset (F cal(H)) h R^degree$. Decompose all ways, solve subproblems, thin, keep an optimum.
]
#law([the fixed point is unique if $T^degree ("mem" F)$ is inductive (Thm 6.3); entire (an implementable
  recursion) if $Lambda(T^degree)$ yields finite non-empty sets and $R$ is a connected preorder])
#law([case split (Prop 9.1): $V_2 V_1^degree = nothing ==> Lambda([V_1,V_2]^degree)("thin"(Q_1+Q_2))(P[U_1,U_2])(min R)
  = ("ran" V_1 -> W_1, W_2)$, $thin W_i = Lambda(V_i^degree)("thin" Q_i)(P U_i)(min R)$])
#law([monotonicity via cost (Prop 9.2): $R = "cost" med "leq" med "cost"^degree$, $h med "cost" = (F "cost") k$,
  $(F "leq") k subset k med "leq" ==> h$ monotonic on $R$])
#law([finding $Q$ (Prop 9.4): preorders $U, V$ with $F(U,R) h subset h R$ and $V^degree cal(H) subset cal(H) R^degree ==>
  Q = F(U,V)$ works (often $U = Pi$)])
#law([greedy-from-DP (ch. 10): bifunctor conditions collapse the DP recursion to a greedy sweep])
]
