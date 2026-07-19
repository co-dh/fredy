#import "@preview/dvdtyp:1.0.1": *
#import "@preview/cetz:0.3.4"

#let basec = rgb("#1457a6")   // blue  — base 𝐀
#let inflc = rgb("#0a7d3f")   // green — inflation 𝐀′ / forgetful
#let secc  = rgb("#c0392b")   // red   — the cross-section

#show: dvdtyp.with(
  title: "The cross-section  𝐀 → 𝐀′  (§1.544)",
  subtitle: "Freyd & Scedrov, §1.544 — the inflation and its section",
  author: none,
)

A *cross-section* of the forgetful functor `listProd : 𝐀′ → 𝐀` is a functor going the other
way, `𝐀 → 𝐀′`, that `listProd` undoes. The forgetful functor is *many-to-one*: it sends a list
`s` to its product `∏s`, and many different lists have the same product (up to isomorphism), so
many lists sit over each object `A`. The cross-section chooses one of them — the one-element list `[A]`.

#figure(
  cetz.canvas({
    import cetz.draw: *
    let dot(p, c: black, r: 0.075) = circle(p, radius: r, fill: c, stroke: none)

    // ── inflation region (the fiber over A) ──
    rect((3.4, 0.0), (8.6, 4.3), stroke: (paint: inflc, dash: "dashed", thickness: 0.7pt),
         fill: inflc.lighten(95%))
    content((6.0, 4.7), text(10pt, fill: inflc)[*𝐀′ = List 𝒞* — objects are lists, product = concatenation])
    content((6.0, 0.30), text(8.5pt, fill: inflc)[lists $s$ with $product s ≅ A$ — all sent to $A$])

    // fiber dots (lists whose product ≅ A)
    dot((4.2, 1.0)); content((4.45, 1.0), text(10pt)[$[1, A]$], anchor: "west")
    dot((4.2, 1.9), c: secc); content((4.45, 1.9), text(10pt, fill: secc)[$[A]$ #h(3pt) #text(8pt)[← chosen]], anchor: "west")
    dot((4.2, 2.8)); content((4.45, 2.8), text(10pt)[$[A, 1]$], anchor: "west")
    dot((4.2, 3.6)); content((4.45, 3.6), text(10pt)[$[A_1, A_2], #h(2pt) A_1 times A_2 ≅ A$], anchor: "west")

    // ── base point A ──
    dot((0, 1.9), c: basec); content((-0.25, 1.9), text(12pt, fill: basec)[$A$], anchor: "east")
    content((0, 1.0), text(10pt, fill: basec)[*𝐀* (base)])

    // forgetful: whole fiber ↦ A   (right → left)
    line((4.0, 2.35), (0.30, 2.05), mark: (end: ">"), stroke: inflc + 1pt)
    content((2.1, 2.65), text(9pt, fill: inflc)[`listProd`: #h(2pt) $s arrow.r.bar product s$])

    // cross-section: A ↦ [A]   (left → right)
    line((0.30, 1.65), (4.0, 1.85), mark: (end: ">"), stroke: (paint: secc, thickness: 1.3pt))
    content((2.1, 1.30), text(9pt, fill: secc)[*section*: #h(2pt) $A arrow.r.bar [A]$])
  }),
  caption: [
    `listProd` (green) sends every list over `A` down to `A` (it is many-to-one). The cross-section
    (red) lifts `A` back up to the *single* list `[A]`. It is a *section* because going up then down returns to `A`:
    #h(3pt) $A #h(1pt) arrow.r.bar #h(1pt) [A] #h(1pt) arrow.r.bar #h(1pt) product [A] = A$, #h(2pt)
    i.e. `listProd ∘ section = id`.
  ],
)

#v(6pt)

That round trip is the defining property — drawn as a triangle:

#figure(
  cetz.canvas({
    import cetz.draw: *
    content((0, 0), text(12pt, fill: basec)[$bold(A)$])
    content((3, 1.7), text(12pt, fill: inflc)[$bold(A)'$])
    content((6, 0), text(12pt, fill: basec)[$bold(A)$])
    // A → A′  (section)
    line((0.4, 0.25), (2.6, 1.55), mark: (end: ">"), stroke: (paint: secc, thickness: 1.2pt))
    content((1.1, 1.25), text(9pt, fill: secc)[`section`#h(2pt)$A arrow.r.bar [A]$])
    // A′ → A  (listProd)
    line((3.4, 1.55), (5.6, 0.25), mark: (end: ">"), stroke: inflc + 1pt)
    content((5.1, 1.25), text(9pt, fill: inflc)[`listProd`])
    // A → A  (identity, the composite)
    line((0.5, 0), (5.5, 0), mark: (end: ">"), stroke: (paint: basec, dash: "dashed"))
    content((3, -0.35), text(9pt, fill: basec)[$"id"_(bold(A))$])
  }),
  caption: [`listProd ∘ section = id`: the cross-section is a one-sided (right) inverse of the forgetful functor.],
)

#v(4pt)

*Why §1.544 wants it.* The slice inclusion `𝐀 → 𝐀/B` is split into two strict steps:
$ bold(A) #h(4pt) -->^(A arrow.r.bar [A]) #h(4pt) bold(A)' #h(4pt) -->^(s arrow.r.bar s #h(2pt) + + #h(2pt) [B]) #h(4pt) bold(A)' \/ B $
The cross-section is the first arrow — it relabels each object `A` of `𝐀` as the singleton list
`[A]`, so the second step (`appendFunctor B`, "multiply by `B`" done as list concatenation) has
lists to append to.

#v(8pt)

= Δ separates objects

$Delta : bold(A) -> bold(A)"/"B$ is the diagonal functor sending each object $A$ to the pair $(A times B, "snd" : A times B -> B)$, an object over $B$. Recall the factorization $(-times B) = Sigma compose Delta$, where $Sigma : bold(A)"/"B -> bold(A)$ is the forgetful functor.

*"Δ separates objects"* means $Delta$ is injective on objects: $Delta(A) = Delta(A') ==> A = A'$ (an equality of objects, not merely an isomorphism).

*Why it holds under the §1.544 interpretation* (the inflation $bold(A)'$ whose product is list concatenation): the object $A times B$ is the literal concatenated list, an equality-carrying object. A slice object is its structure arrow, so $Delta(A) = Delta(A')$ forces equal domains $A times B = A' times B$ as lists, and lists cancel (`B::s = B::t ⟹ s = t`, the strict cancellation `strict_cancel` = `List.cons.inj`). Hence $A = A'$.

*Why it fails in the ordinary interpretation* (product only defined up to isomorphism): there you only ever get $A times B tilde.eq A' times B$, and an isomorphism never forces $A = A'$. Set example with $B = NN$: $NN times {ast} tilde.eq NN tilde.eq NN times NN$, yet ${ast} eq.not NN$. So the plain diagonal is full and faithful but not injective on objects.

*Why Freyd wants this:* §1.544 wants $bold(A)$ to be a genuine subcategory of $bold(A)"/"B$, and a subcategory inclusion must be injective on objects. The inflation upgrades "$tilde.eq$ (up to iso)" to "$=$ (literally equal)", converting the full-faithful $Delta$ into an honest inclusion $bold(A) subset bold(A)"/"B$.

= Δ separates morphisms (when $B$ is well-supported)

*Important distinction* (this is the point of the section):
- $Delta(f)$ is a morphism in the slice $bold(A)"/"B$: the over-morphism $(chevron.l A times B, "snd" chevron.r) -> (chevron.l A' times B, "snd" chevron.r)$, i.e. the arrow together with the proof that it commutes with the structure maps $"snd"$.
- The underlying arrow in $bold(A)$ is $f times B = "pair"("fst" compose f, "snd") : A times B -> A' times B$. This equals $(-times B)(f) = Sigma(Delta(f))$ — that is, $Delta(f)$ with the over-structure forgotten. Do not call the bare arrow $f times B$ "$Delta(f)$"; it is $Sigma(Delta(f))$.

*"Δ separates morphisms"* means $Delta$ is faithful: $Delta(f) = Delta(g) ==> f = g$.

*Reduction:* the forgetful $Sigma : bold(A)"/"B -> bold(A)$ is faithful — an over-morphism is determined by its underlying arrow (`OverHom.ext`). So
$ Delta(f) = Delta(g) quad arrow.l.r.double quad Sigma(Delta(f)) = Sigma(Delta(g)) quad arrow.l.r.double quad f times B = g times B, $
and "$Delta$ faithful" is equivalent to "$(- times B)$ faithful".

*Why $(- times B)$ is faithful when $B$ is well-supported:* from $f times B = g times B$, compose with the projection $"fst" : A' times B -> A'$. Since $(f times B) compose "fst" = "fst" compose f$ (`fst_pair`), we get $"fst" compose f = "fst" compose g$, where $"fst" : A times B -> A$. Now $B$ well-supported means $B -> 1$ is a cover (epimorphism onto the terminator); $"fst" : A times B -> A$ is the pullback of $B -> 1$ along $A -> 1$, and covers are stable under pullback, so $"fst"$ is a cover, hence epic. An epimorphism cancels on the right, so $f = g$. (In Lean: `slice_embedding_separates` in `S1_54.lean`, using `prod_fst_cover` and `cover_epi`; the wrapper `sliceEmbedFaithful` in `S1_541_RelativeCapitalization.lean` passes through `congrArg OverHom.f`, which is the $Sigma$-faithfulness step.)

#figure(
  cetz.canvas({
    import cetz.draw: *
    content((-3.2, 1.8), text(12pt)[$A times B$])
    content((3.2, 1.8), text(12pt)[$A' times B$])
    content((0.0, 0.0), text(12pt)[$B$])
    line((-2.5, 1.8), (2.5, 1.8), mark: (end: ">"), stroke: (paint: basec, thickness: 1.2pt))
    content((0.0, 2.3), text(9pt, fill: basec)[$Sigma(Delta(f)) = f times B = (-times B)(f)$])
    line((-2.9, 1.5), (-0.3, 0.3), mark: (end: ">"), stroke: black + 1pt)
    content((-2.0, 0.75), text(9pt)[$"snd"$])
    line((2.9, 1.5), (0.3, 0.3), mark: (end: ">"), stroke: black + 1pt)
    content((2.0, 0.75), text(9pt)[$"snd"$])
  }),
  caption: [
    The whole triangle (arrow + commuting legs over $B$) is $Delta(f)$, a morphism in $bold(A)"/"B$;
    forgetting the two legs down to $B$ (applying $Sigma$) leaves only the top arrow $f times B$ in
    $bold(A)$. $Delta$ is faithful (separates morphisms) iff this forgetting loses no information
    beyond what $f$ already determines — which holds exactly when the projection $A times B -> A$ is
    epic, i.e. when $B$ is well-supported.
  ],
)

*Set example.* The underlying arrow of $Delta(f)$ is $f times B : A times B -> A' times B$, $(a, b) |-> (f(a), b)$.
- $B$ nonempty (= well-supported in Set): to recover $f$ from $f times B$, evaluate at $(a, b)$: $(f(a), b)$, so $f(a) = g(a)$ for every $a$ — this works because some $b in B$ exists to pair with $a$. Equivalently, $"fst" : A times B -> A$, $(a, b) |-> a$, is surjective iff $B eq.not emptyset$, and surjections cancel on the right.
- $B = emptyset$: then $A times B = emptyset$, so $f times emptyset$ and $g times emptyset$ are both the unique empty map $emptyset -> emptyset$ — equal for all $f$, $g$. $Delta$ collapses every parallel pair. Concretely $A = {a}$, $A' = {0, 1}$, $f equiv 0$, $g equiv 1$: $f eq.not g$ but $f times emptyset = g times emptyset$. This is exactly why the hypothesis "$B$ well-supported" is needed.

*Where the "terminator is projective" idea belongs:* $1_B : B -> B$ genuinely is the terminator of $bold(A)"/"B$, and "the terminator is projective" is a real Freyd result (§1.525), but that concerns the category being well-pointed and is used later in the capitalization argument (§1.55). It is not what makes $Delta$ faithful — faithfulness needs only that the projection $A times B -> A$ is epic, which is precisely "$B$ well-supported".

= Why $bold(A) subset bold(A)"/"B$ is a proper inclusion (the new point)

After the final reinterpretation of §1.544, $Delta : bold(A) -> bold(A)"/"B$ is a literal subcategory inclusion. It is a _proper_ inclusion: $bold(A)"/"B$ is strictly larger — it contains points that $bold(A)$ does not. This properness is the entire engine of capitalization (§1.545–1.546): each slice step adjoins a new point.

*Note.* The inclusion is $Delta$. The forgetful functor $Sigma : bold(A)"/"B -> bold(A)$ goes the other way; the composite $Sigma compose Delta = (- times B)$ is the round trip $bold(A) -> bold(A)$, not the inclusion.

#v(4pt)

== The generic point of $B$

In the slice $bold(A)"/"B$ the terminator is $1_(bold(A)"/"B) = (B -->^("id"_B) B)$, and $Delta(B) = (B times B -->^("snd") B)$.

A _point_ of $Delta(B)$ (a global element in the slice) is a morphism $1_(bold(A)"/"B) -> Delta(B)$, i.e. an over-morphism from $(B -->^"id" B)$ to $(B times B -->^"snd" B)$. Its underlying arrow is a map $x : B -> B times B$ satisfying $x compose "snd" = "id"_B$ (it commutes over $B$); such an $x$ is a section of $"snd"$, of the form $x = chevron.l h, "id"_B chevron.r$ for some $h : B -> B$.

The *generic point* is the diagonal $delta = chevron.l "id"_B, "id"_B chevron.r : B -> B times B$ (it satisfies $delta compose "snd" = "id"_B$). It is a global point of $Delta(B)$ in $bold(A)"/"B$.

This $delta$ generally does not come from $bold(A)$. A point of $B$ "in $bold(A)$" is a global element $1_(bold(A)) -> B$ (from $bold(A)$'s own terminator). A well-supported $B$ (the map $B -> 1$ is an epimorphism) need not have any such point $1 -> B$. When $B$ has no point in $bold(A)$, $delta$ is a genuinely new point, present in $bold(A)"/"B$ but not in $bold(A)$.

This also shows $Delta$ is faithful but not full: $delta$ is a slice morphism between two objects that are in the image of $Delta$ (namely $1_(bold(A)"/"B) = Delta(1_(bold(A)))$ and $Delta(B)$), yet $delta$ itself is not $Delta$ of any $bold(A)$-morphism.

#figure(
  cetz.canvas({
    import cetz.draw: *
    content((-3.2, 1.8), text(12pt, fill: basec)[$B$])
    content((3.2, 1.8), text(12pt, fill: basec)[$B times B$])
    content((0.0, 0.0), text(12pt, fill: basec)[$B$])
    // top arrow: δ (red) — the generic point
    line((-2.9, 1.8), (2.4, 1.8), mark: (end: ">"), stroke: (paint: secc, thickness: 1.3pt))
    content((0.0, 2.3), text(9pt, fill: secc)[$delta = chevron.l "id"_B, "id"_B chevron.r$])
    // left leg: id_B — structure map of the slice terminator 1_{𝐀/B}
    line((-3.1, 1.5), (-0.2, 0.3), mark: (end: ">"), stroke: black + 1pt)
    content((-2.1, 0.75), text(9pt)[$"id"_B$])
    // right leg: snd — structure map of Δ(B)
    line((2.9, 1.5), (0.2, 0.3), mark: (end: ">"), stroke: black + 1pt)
    content((2.1, 0.75), text(9pt)[$"snd"$])
  }),
  caption: [
    $delta$ is the generic point of $B$, living in $bold(A)"/"B$ but not in $bold(A)$. In the
    $ZZ slash 2$-set example ($B = \{0, 1\}$ with swap $0 arrow.l.r 1$), $B$ has no point
    $1 -> B$ in $bold(A)$ because the swap has no fixed element, yet the diagonal $delta$ is
    such a point in $bold(A)"/"B$ — the proper part of the inclusion.
  ],
)

== Concrete witness: a two-element swap set

Let $bold(A)$ be the category of $ZZ slash 2$-sets: a $ZZ slash 2$-set is a set equipped with an involution — a self-map that is its own inverse, a "swap". A morphism of $ZZ slash 2$-sets is a function that commutes with the swaps. (This is a small pre-regular category; in fact a topos.)

Let $B = \{0, 1\}$ with the swap $0 arrow.l.r 1$.

*$B$ is well-supported.* $B$ is nonempty, so the unique map $B -> 1$ is onto (an epimorphism).

*$B$ has no global point in $bold(A)$.* A point $1 -> B$ is a morphism from the one-point trivial $ZZ slash 2$-set (the singleton with the identity swap), i.e. an element of $B$ fixed by the swap. The swap $0 arrow.l.r 1$ has no fixed element, so there is no point $1 -> B$ in $bold(A)$.

*Pass to $bold(A)"/"B$.* The diagonal $delta = chevron.l "id", "id" chevron.r : B -> B times B$ sends $b arrow.r.bar (b, b)$; it commutes with the swap (so it is a legitimate $ZZ slash 2$-set morphism) and is a section of $"snd"$. So $delta$ is a point of $Delta(B)$ in $bold(A)"/"B$.

*Conclusion.* $delta$ is a point in the target $bold(A)"/"B$ that is not in $bold(A)$. It is exactly the generic point of $B$ that §1.546 uses to capitalize $B$. The inclusion $bold(A) subset bold(A)"/"B$ is therefore proper.

#v(4pt)

More points also live in $bold(A)"/"B$ that do not come from $bold(A)$: for instance, every object $(X -->^pi B)$ whose domain $X$ is not a product $B times A$, such as a proper subobject $B' arrow.r.tail B$. But the point that matters for capitalization is the generic point $delta$ above: slicing over $B$ freely adjoins a global point to $B$.

= From $bold(A)$ to $underline(bold(A))$: what capitalization gains

The capitalization lemma (§1.543) gives, for every $bold(A) in cal(E)$, a capital $underline(bold(A)) in cal(E)$ and a faithful representation $bold(A) -> underline(bold(A))$ in $cal(E)$. The single thing gained is enough global points. Recall the two definitions this rests on:

- (§1.523) An object $A$ is *well-pointed* if its global points $1 -> A$ cover $A$ — equivalently, every proper subobject $A' arrow.r.tail A$ is missed by some point $1 -> A$ (there are enough points to detect every subobject).
- (§1.525) A pre-regular category is *capital* if every well-supported object is well-pointed.

== The three gains

1. *Points separate and detect.* In $underline(bold(A))$, for every well-supported $X$ the points $1 -> X$ jointly cover it, and every proper subobject is missed by some point. In $bold(A)$ this can fail — the category may be point-poor. (Concrete case from the earlier section: in the category of $ZZ slash 2$-sets, $B = {0, 1}$ with swap $0 arrow.l.r 1$ is well-supported but has no point $1 -> B$, so points saw nothing.)

2. *The terminator becomes projective* (§1.525): points lift along covers — given a cover $Y arrow.r.twohead X$ and a point $1 -> X$, it lifts to a point $1 -> Y$. Covers are surjective on points.

3. *The global-sections functor* $Gamma = "Hom"(1, -) : underline(bold(A)) -> cal(S)$ ($cal(S) = "Set"$) is a representation of pre-regular categories (§1.526): it preserves finite products, pullbacks, covers, and images. On $bold(A)$ alone $Gamma$ was not even faithful — it collapsed the pointless $B$ above to the empty set $emptyset$.

== The payoff

Compose the embedding with global sections:
$ bold(A) arrow.r.hook underline(bold(A)) -->^Gamma cal(S) $
is a faithful, structure-preserving representation into Set (§1.55). This is the engine of Freyd's embedding theorem: every small pre-regular (or regular) category faithfully represents into a power of Set. In one phrase: a category is capital exactly when it has enough points to see itself in Set through its own global-sections functor $Gamma = "Hom"(1, -)$.

#figure(
  cetz.canvas({
    import cetz.draw: *
    content((-4.5, 0), text(13pt, fill: basec)[$bold(A)$])
    content((0.0, 0), text(13pt, fill: basec)[$underline(bold(A))$])
    content((5.0, 0), text(13pt)[$cal(S)$ (= Set)])
    // Arrow 𝐀 → 𝐀̲  (green, faithful; adds points)
    line((-4.1, 0), (-1.0, 0), mark: (end: ">"), stroke: (paint: inflc, thickness: 1.2pt))
    content((-2.5, 0.55), text(9pt, fill: inflc)[faithful; adds points])
    // Arrow 𝐀̲ → 𝒮  (red, Γ = Hom(1,−))
    line((1.0, 0), (3.8, 0), mark: (end: ">"), stroke: (paint: secc, thickness: 1.2pt))
    content((2.4, 0.55), text(9pt, fill: secc)[$Gamma = "Hom"(1, -)$])
    // Label below: composite is faithful
    content((0.0, -0.9), text(9pt)[composite $bold(A) -> cal(S)$ is faithful (§1.55)])
  }),
  caption: [
    Capitalization inserts $underline(bold(A))$ so that the global-sections functor $Gamma$ becomes
    faithful on the enlarged category; the composite embeds $bold(A)$ into Set. In the
    $ZZ slash 2$-set example, $Gamma(B) = "Hom"(1, B)$ = the swap-fixed elements of $B$, which is
    empty in $bold(A)$ — capitalization adds the points that make $Gamma$ faithful.
  ],
)

== The cost

Nothing structural is lost. The embedding $bold(A) -> underline(bold(A))$ is faithful and lies in $cal(E)$, so it preserves the pre-regular structure (finite products, covers, pullbacks, images). $bold(A)$ sits inside $underline(bold(A))$ intact — capitalization only adds points; it never identifies or discards anything of $bold(A)$.

From $bold(A)$ to $underline(bold(A))$ we gain enough global points to turn $Gamma = "Hom"(1, -)$ into a faithful representation into Set — converting an abstract pre-regular category into a concrete category of sets-with-structure.

= §1.547: choice-free, but not a terminating program

Freyd gives capitalization twice. The §1.546 construction well-orders the objects of $bold(A)$ and does
transfinite recursion — slice over the first well-supported object not yet capitalized; take unions at
limits. This uses the axiom of choice. The §1.547 construction is choice-free: it uses the theory of
rational categories [1.48]. A natural question arises: does choice-free mean we can write code that
performs capitalization? The careful answer is that choice-free removes the one genuinely non-algorithmic
step and makes the construction canonical and definable as data, but "choice-free" is not the same as "a
terminating program that returns a finite answer". Two things are being conflated.

== What §1.547 removes

Well-ordering an arbitrary small category is exactly the step with no algorithm — there is no procedure
that well-orders a general set. §1.547 replaces it with a definite construction: the rational category
[1.48] built on pairs $chevron.l A, F chevron.r$, where $A in bold(A)$ and $F$ is a finite set of maps
from $A$ to distinct well-supported targets. It is shown to be a relative capitalization because it is a
directed union of slices. Now every object and morphism is a concrete finite description of $bold(A)$'s
own data, with no arbitrary choices. That is the content of "choice-free": the result is canonical, hence
in principle writable as data.

== Why that is still not runnable code

Two gaps remain between §1.547 and an executable program.

1. *The output is infinite.* $underline(bold(A))$ is an $omega$-tower of relative capitalizations, each
   itself a directed union of slices, and each slice step adjoins new points. Even if $bold(A)$ is
   finitely presented, $underline(bold(A))$ has infinitely many objects and morphisms. So there is no
   finite object to compute and halt with. What you _can_ write is a lazy presentation: given decidable
   equality, hom-membership, and composition on $bold(A)$, the choice-free construction yields decidable
   equality, hom, and composition on $underline(bold(A))$ together with an enumeration of its objects — a
   program that answers any question about $underline(bold(A))$ on demand, not one that outputs the whole
   category.

2. *The input must be constructive.* The construction quantifies over predicates like "$B$ is
   well-supported", "$B' arrow.r.tail B$ is proper", "these maps form a product diagram". To run, these
   must be decidable on the presentation of $bold(A)$. If they are decidable, §1.547 is genuinely
   computable; if not, choice-freeness alone gives no algorithm. Freyd's argument is classical logic minus
   choice, which is weaker than "extracts a program" — the latter also needs decidability (or a fully
   constructive metatheory).

*Precise statement.* §1.547 makes capitalization a computable presentation of the infinite
$underline(bold(A))$, provided $bold(A)$ is presented with decidable operations. It is not, and cannot
be, a function returning a finite category. Choice-free means "canonical and definable as data", not
"finite" or "terminating".

== This repo's status

This is exactly the constructive-in-a-proof-assistant question, and the repo has not yet realized Freyd's
choice-free version. The live `capitalization_lemma` is sorry-free, but per `Freyd.lean`'s own header its
axioms are `[propext, Classical.choice, Quot.sound]` — it still uses `Classical.choice` (it went through
a well-ordering / uniform-successor route with Zermelo built from `Classical.choice`, in
`WellOrdering.lean`). Genuinely eliminating `Classical.choice` here — implementing the §1.547
rational-category route as pure data — is precisely what would turn the Lean development into code you
could compute with. That is an open task in the codebase, not something already done.

#figure(
  table(
    columns: (auto, auto, auto),
    align: left,
    [*aspect*], [*§1.546 (choice)*], [*§1.547 (choice-free)*],
    [key step],
    [well-order the objects; transfinite recursion],
    [rational category on pairs $chevron.l A, F chevron.r$; directed union of slices],
    [uses AC?], [yes (well-ordering)], [no],
    [canonical?],
    [no (depends on the chosen well-ordering)],
    [yes (determined by $bold(A)$'s data)],
    [length],
    [transfinite (not, in general, countable)],
    [$omega$-tower of directed unions],
    [code?],
    [no algorithm (cannot well-order a general set)],
    [computable lazy presentation if $bold(A)$'s operations are decidable],
  ),
  caption: [The choice-free §1.547 route is what could, in principle, be turned into code; the §1.546
    route cannot, because well-ordering a general set is not algorithmic.],
)

#figure(
  cetz.canvas({
    import cetz.draw: *
    // Node 1: choice-free / canonical (§1.547)
    rect((0.0, 0.2), (3.0, 1.2), stroke: basec + 0.7pt, fill: basec.lighten(93%))
    content((1.5, 0.95), text(8pt, fill: basec)[choice-free])
    content((1.5, 0.50), text(8pt, fill: basec)[canonical (§1.547)])
    // Arrow 1 → 2, labelled "+ decidable input" (green)
    line((3.0, 0.7), (3.9, 0.7), mark: (end: ">"), stroke: inflc + 1pt)
    content((3.45, 1.1), text(7pt, fill: inflc)[+ decidable input])
    // Node 2: computable lazy presentation
    rect((3.9, 0.2), (7.2, 1.2), stroke: inflc + 0.7pt, fill: inflc.lighten(93%))
    content((5.55, 0.95), text(8pt, fill: inflc)[computable])
    content((5.55, 0.50), text(8pt, fill: inflc)[lazy presentation])
    // Arrow 2 → 3: red dashed, labelled "✗ 𝐀̲ infinite"
    line((7.2, 0.7), (8.1, 0.7), mark: (end: ">"),
         stroke: (paint: secc, dash: "dashed", thickness: 1pt))
    content((7.65, 1.1), text(7pt, fill: secc)[✗ $underline(bold(A))$ infinite])
    // Node 3: finite / terminating output
    rect((8.1, 0.2), (11.4, 1.2), stroke: secc + 0.7pt, fill: secc.lighten(93%))
    content((9.75, 0.95), text(8pt, fill: secc)[finite /])
    content((9.75, 0.50), text(8pt, fill: secc)[terminating output])
  }),
  caption: [Choice-free gives a canonical construction; adding decidable operations on $bold(A)$
    upgrades it to a computable, on-demand presentation of $underline(bold(A))$; but it never
    becomes a finite or terminating output, because $underline(bold(A))$ is infinite.],
)
