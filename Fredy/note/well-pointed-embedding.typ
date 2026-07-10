#import "@preview/dvdtyp:1.0.1": *
#import "@preview/cetz:0.3.4"

// Palette (matches the other §1.6x notes in this folder).
#let subc = rgb("#1457a6")   // blue  — subobjects / well-pointed
#let imgc = rgb("#c0392b")   // red   — support / the collapse
#let prec = rgb("#0a7d3f")   // green — capitalization / exactness
#let callout(c, body) = block(width: 100%, fill: c.lighten(94%), inset: 10pt, radius: 5pt,
  stroke: (left: 3pt + c), body)
#let punch(body) = block(width: 100%, fill: rgb("#fdecea"), inset: 11pt,
  radius: (right: 5pt), stroke: (left: 3pt + imgc),
  [#text(weight: "bold", fill: imgc)[★ Punchline]#v(3pt)#body])
#let yes = text(fill: prec, weight: "bold")[#sym.checkmark]
#let no = text(fill: imgc, weight: "bold")[#sym.crossmark]

#set table(inset: 5pt, align: left + horizon, stroke: 0.4pt + luma(200))
#show raw.where(block: false): box.with(fill: luma(240), inset: (x: 2pt), outset: (y: 3pt), radius: 1.5pt)

#show: dvdtyp.with(
  title: "Well-pointed objects, capitalization, and why Yoneda isn't enough",
  subtitle: "Freyd & Scedrov, §1.522–§1.547",
  author: none,
  accent: subc,
  abstract: [
    #text(11pt, fill: subc, style: "italic")[
      From support (§1.522) and well-pointedness (§1.523) up through the §1.54 capitalization, with the
      comparison to the Yoneda embedding: when point-wise reasoning is valid, why "just embed into Set"
      is a theorem not a freebie, and why slicing (a pullback) stays exact where Yoneda (a hom) does not.
      Q&A distilled from a discussion, with #smallcaps[Set]`/I` fiber-product pictures.
    ]
  ],
)

= Projectives, and a group as a one-object category #h(0.4em) (§1.524)

A warm-up: projectivity (§1.524) — where #smallcaps[Set] is special and structure breaks it — and the
"a group is a one-object category" view. Both recur below.

#definition("Projective (§1.524)")[
  An object `P` is *projective* — three equivalent forms:
  + *Lifting.* Every cover `e : A ↠ B` and every map `f : P → B` admit a *lift* `g : P → A` with
    `g e = f` (diagram order: first `g`, then `e`).
  + *`Hom(P,−)` preserves covers.* It carries every cover (surjection) to a surjection — so `P` survives
    quotients without losing information.
  + *Covers onto `P` split.* Every cover `e : A ↠ P` has a section `s : P → A` (`s e = id_P`).
]

(Why "projective": `P` is projective ⟺ `P` is a *direct summand of a free object* (`F ≅ P ⊕ Q`), i.e. the
*image of a projection* — an idempotent `e : F → F`, `e e = e`. Take a free `q : F ↠ P`; lifting `id_P`
along `q` gives a section, so `P` is a retract of `F`. Named as the dual of *injective* (Cartan–Eilenberg).)

In #smallcaps[Set] *every* object is projective: a cover is a surjection, so pick one preimage in each
fiber (choice). That picked function is *automatically* a morphism — in #smallcaps[Set] a morphism *is*
just a function. It stops being free the moment morphisms carry structure.

*Counterexample — `ℤ/2` in `Ab`.* Covers in `Ab` are the surjective homomorphisms. Take the cover
`q : ℤ/4 ↠ ℤ/2` (`1 ↦ 1`) and `f = id : ℤ/2 → ℤ/2`. A lift would be a *homomorphism* `g : ℤ/2 → ℤ/4`
with `g q = id`:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let P = (0, 0); let B = (3.4, 0); let A = (3.4, 2.1)
    content(P, text(10pt)[$ZZ\/2$]); content((0, -0.42), text(7pt, fill: luma(110))[(`P`, want projective)])
    content(B, text(10pt)[$ZZ\/2$])
    content(A, text(10pt)[$ZZ\/4$])
    // f : P → B  (the map to lift)  = id
    line((0.55, 0), (2.85, 0), mark: (end: ">"), stroke: 1pt)
    content((1.7, 0.27), text(8.5pt)[$f = $ id])
    // q : A → B  (the cover)
    line((3.4, 1.65), (3.4, 0.32), mark: (end: ">"), stroke: 1pt)
    content((4.15, 1.0), text(8.5pt)[$q$ (cover)])
    // g : P → A  (the lift that does not exist)
    line((0.5, 0.28), (2.95, 1.85), mark: (end: ">"),
      stroke: (paint: imgc, dash: "dashed", thickness: 0.9pt))
    content((1.15, 1.3), text(9pt, fill: imgc)[$g$ ?])
    content((2.35, 0.92), text(8pt, fill: imgc)[no such hom])
  }),
  caption: [Lifting test for `P = ℤ/2`. The cover `q : ℤ/4 ↠ ℤ/2` and `f = id` admit no homomorphism
  `g` with `g q = id`.],
)

A homomorphism `ℤ/2 → ℤ/4` must send the generator to an element of order dividing `2`, i.e. to `0` or
`2`; either way `q` sends it to `0 ≠ 1`. So `g q` kills the generator and cannot be `id`: `ℤ/2` is *not
projective*.

#punch[
  The #smallcaps[Set] "pick a preimage" still works *set-theoretically* (`1↦1, 0↦0`), but that function
  is *not a homomorphism* (`1+1=0` in `ℤ/2`, yet `1+1=2≠0` in `ℤ/4`). Projectivity needs the lift to be a
  *morphism* of the category; choice only hands you a bare function — that gap *is* "not projective." The
  projectives of `Ab` are exactly the *free* abelian groups, and `ℤ/2` is not free.
]

== A group is a one-object category (a groupoid)

`ℤ/2`, `ℤ/3` are also interesting *as whole categories* — a different role from being objects of `Ab`.
Any group `G` is a category with *one object* `∗`; *morphisms* `∗→∗` = the group elements;
*composition* = the group operation; *identity* = the unit. Every morphism is invertible, so it is a
*groupoid*, and its composition table *is* the group's Cayley table. For `ℤ/2` that is: one object `∗`,
the identity, and a single non-identity iso `r` with `r r = id` (so `r⁻¹ = r`); for `ℤ/3`: the identity
and a mutually-inverse pair `r, r²` (`r⁻¹ = r²`).

The relations live in the geometry once you *unroll* the self-loops into a walk: every node is the *same*
object `∗`, tagged by which power of `r` has acted, and a walk that returns to the start *is* the
identity. So `r r = id` is a closed 2-cycle and `r r r = id` a closed triangle (the group's Cayley
graph).

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let nodefill = rgb("#eef3fb")
    // a node = a copy of the single object ∗, tagged by the group element reached
    let node(p, lbl) = {
      circle(p, radius: 0.40, fill: nodefill, stroke: 0.8pt + subc)
      content(p, text(9.5pt)[#lbl])
    }
    // straight arrow trimmed off both node rims
    let arr(p, q, col, lbl, loff) = {
      let dx = q.at(0) - p.at(0); let dy = q.at(1) - p.at(1)
      let L = calc.sqrt(dx*dx + dy*dy)
      let ux = dx / L; let uy = dy / L
      let s = (p.at(0) + 0.46*ux, p.at(1) + 0.46*uy)
      let e = (q.at(0) - 0.46*ux, q.at(1) - 0.46*uy)
      line(s, e, stroke: 1pt + col, mark: (end: ">"))
      let mx = (s.at(0) + e.at(0)) / 2; let my = (s.at(1) + e.at(1)) / 2
      content((mx + loff.at(0), my + loff.at(1)), text(9pt, fill: col)[#lbl])
    }
    // Z/2 : the bigon — two r-steps return to start
    content((0, 2.35), text(12pt, weight: "bold", fill: subc)[$ZZ\/2$])
    bezier((-0.80, 0.16), (0.80, 0.16), (-0.5, 1.05), (0.5, 1.05), stroke: 1pt + imgc, mark: (end: ">"))
    content((0, 1.25), text(9pt, fill: imgc)[$r$])
    bezier((0.80, -0.16), (-0.80, -0.16), (0.5, -1.05), (-0.5, -1.05), stroke: 1pt + imgc, mark: (end: ">"))
    content((0, -1.28), text(9pt, fill: imgc)[$r$])
    node((-1.15, 0), [id]); node((1.15, 0), [$r$])
    content((0, -2.0), text(8.5pt, fill: imgc)[$r r = $ id])
    // Z/3 : the triangle — three r-steps return to start
    let cx = 6.6
    content((cx, 2.35), text(12pt, weight: "bold", fill: subc)[$ZZ\/3$])
    let t = (cx, 1.45); let br = (cx + 1.35, -0.75); let bl = (cx - 1.35, -0.75)
    arr(t,  br, imgc, [$r$], (0.30, 0.18))
    arr(br, bl, imgc, [$r$], (0.0, -0.32))
    arr(bl, t,  imgc, [$r$], (-0.34, 0.18))
    node(t, [id]); node(br, [$r$]); node(bl, [$r^2$])
    content((cx, -2.0), text(8.5pt, fill: imgc)[$r r = r^2$, #h(0.4em) $r r r = $ id])
  }),
  caption: [The relation read off the diagram: a closed walk of `r`'s `= id`. `ℤ/2` closes in two steps
  (`r r = id`); `ℤ/3` in three (`r r = r²`, `r r r = id`). Each node is the *same* object `∗`, tagged by
  which power of `r` has acted; collapsing all nodes back to one `∗` gives the one-object groupoid.],
)

= Support: the image of $A -> 1$ #h(0.4em) (§1.522)

#definition("Support, well-supported")[
  In a regular category the *support* `𝒮pt(A)` is the *image of the unique map* $A -> 1$ — always a
  *subobject of* $1$. `A` is *well-supported* if `𝒮pt(A) = 1`; equivalently (pre-regular) $A -> 1$ is a
  *cover*. So `A` is _not_ well-supported #h(0.2em) ⟺ #h(0.2em) $A -> 1$ factors through a _proper_
  subobject `U ⊊ 1` #h(0.2em) (§1.534: `A → U ↣ 1`).
]

Support lives among the *subobjects of* $1$ (the "truth values" / support lattice). How many there are
controls how interesting the notion is.

#table(
  columns: (auto, auto, auto, auto, auto),
  table.header(
    table.cell(fill: subc.lighten(86%))[*Category*], table.cell(fill: subc.lighten(86%))[*Subobjects of $1$*],
    table.cell(fill: subc.lighten(86%))[*`𝒮pt(A)`*], table.cell(fill: subc.lighten(86%))[*Not well-supported ⟺*],
    table.cell(fill: subc.lighten(86%))[*Example*]),
  [#smallcaps[Set]], [just `∅`, `{∗}`], [`1` if `A≠∅`, else `∅`], [`A = ∅`],
    [#text(fill: imgc)[*`∅`*] — unique in Set],
  [`Set/I`], [subsets of `I`], [image `p(A) ⊆ I` of `p:A→I`], [`p` misses some `i∈I` (empty fiber)],
    [`I={0,1}`, `{∗}↦0`: `{0}⊊I`],
  [`Sh(X)`], [open sets of `X`], [open set where sheaf ≠ ∅], [sheaf on proper open `U⊊X`],
    [extend-by-∅ off `U`],
)

*Set picture* ($1 = \{∗\}$ has only two subobjects): $A ≠ ∅$ gives $A->1$ surjective, image $= 1$,
*well-supported*; $A = ∅$ gives image $∅ ⊊ 1$, *not* well-supported. So `∅` — also the _initial_ object
— is the unique not-well-supported object of #smallcaps[Set]. (No zero object is involved: in Set initial
`∅ ≠ {∗}` terminal.)

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let bundle(ox, lbl, f0, f1) = {
      line((ox - 0.45, 0), (ox + 1.45, 0), stroke: 0.5pt + luma(150))
      circle((ox, 0), radius: 0.045, fill: luma(120), stroke: none)
      circle((ox + 1, 0), radius: 0.045, fill: luma(120), stroke: none)
      content((ox, -0.33), text(7pt, fill: luma(110))[0])
      content((ox + 1, -0.33), text(7pt, fill: luma(110))[1])
      if f0 { line((ox, 1.04), (ox, 0.07), stroke: 0.4pt + luma(120)); circle((ox, 1.1), radius: 0.1, fill: subc, stroke: none) }
      if f1 { line((ox + 1, 1.04), (ox + 1, 0.07), stroke: 0.4pt + luma(120)); circle((ox + 1, 1.1), radius: 0.1, fill: subc, stroke: none) }
      content((ox + 0.5, 1.78), lbl)
    }
    bundle(0, text(9pt)[$1$ (terminal)], true, true)
    bundle(3.4, text(9pt, fill: imgc)[$U = \{0\}$], true, false)
    bundle(6.1, text(9pt, fill: imgc)[$B$], true, false)
  }),
  caption: [Objects of `Set/I` as dots fibered over the base $I = \{0,1\}$. The terminal $1$ occupies
  _both_ fibers; the proper subobject `U={0}` and the not-well-supported `B` (#text(fill: imgc)[red])
  occupy _only_ fiber `0`. `B`'s image in `I` is `{0} ⊊ I`.],
)

The consequence (§1.533–§1.534) is that slicing over a *not*-well-supported `B` throws information away,
so capitalization slices only over *well-supported* `B` (also the hypothesis of _capital_, §1.525 — see
the next section). Here is the reason, once, in the scene above.

== Why slicing over a not-well-supported `B` collapses (§1.533–§1.534)

*The product is a fiber product.* `B×U` is the product _in the ambient category_; in `Set/I` that is the
*fiber product over `I`* (a *pullback*), computed as the *ordinary product inside each fiber*:
$ (B times_I U)_i = B_i times U_i . $
(In plain `Set` it would be the ordinary Cartesian product — but there `1` has only `∅, {∗}`, so the sole
proper `U` is `∅` and §1.534 is degenerate; the slice is what gives `1` many subobjects, the subsets of `I`.)

#figure(
  scale(x: 115%, y: 115%, reflow: true, cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let bundle2(ox, title, f0, f1) = {
      line((ox - 0.45, 0), (ox + 1.45, 0), stroke: 0.5pt + luma(150))
      circle((ox, 0), radius: 0.04, fill: luma(120), stroke: none)
      circle((ox + 1, 0), radius: 0.04, fill: luma(120), stroke: none)
      content((ox, -0.32), text(6.5pt, fill: luma(110))[0])
      content((ox + 1, -0.32), text(6.5pt, fill: luma(110))[1])
      for (i, lbl) in f0.enumerate() {
        let y = 0.8 + i * 0.62
        line((ox, y - 0.18), (ox, 0.06), stroke: 0.35pt + luma(150))
        circle((ox, y), radius: 0.2, fill: subc.lighten(80%), stroke: 0.5pt + subc)
        content((ox, y), text(6pt)[#lbl])
      }
      for (i, lbl) in f1.enumerate() {
        let y = 0.8 + i * 0.62
        line((ox + 1, y - 0.18), (ox + 1, 0.06), stroke: 0.35pt + luma(150))
        circle((ox + 1, y), radius: 0.2, fill: subc.lighten(80%), stroke: 0.5pt + subc)
        content((ox + 1, y), text(6pt)[#lbl])
      }
      content((ox + 0.5, 2.2), text(9pt)[#title])
    }
    bundle2(0, $B$, ($b_1$, $b_2$), ())
    content((2.05, 0.95), text(12pt)[$times_I$])
    bundle2(2.6, $U$, ($ast$,), ())
    content((4.4, 0.95), text(12pt)[$=$])
    bundle2(4.9, $B times_I U$, ($b_1$, $b_2$), ())
  })),
  caption: [Fiber product `B ×_I U` over $I = \{0,1\}$. `B` lives only over `0`
  ($B_0 = \{b_1, b_2\}$, $B_1 = nothing$); the subterminal `U = {0} ↣ 1` is a single point over `0`
  ($U_0 = \{ast\}$, $U_1 = nothing$). Fiberwise $(B times_I U)_i = B_i times U_i$: over $0$,
  $\{b_1, b_2\} times \{ast\} = \{b_1, b_2\}$ (a fiber `×` a point is unchanged); over $1$,
  $nothing times nothing = nothing$. So `B ×_I U ≅ B`.],
)

*Why the map is an isomorphism.* `U` is a single point `{∗}` over its support and `∅` elsewhere, so `×U`
*restricts to `U`'s support*: a fiber `× {∗}` is unchanged, a fiber `× ∅` is emptied. `B` already lives
over `0` (not well-supported, `𝒮pt(B) = {0} ⊆ U`), so nothing is dropped — which is §1.534:

#callout(imgc)[
  *§1.534 (verbatim).* Suppose that `B` is not well-supported, that is, there exists `B → U ↣ 1` where
  `U` is a proper subobject of `1`. Then `B × U → B × 1` is an isomorphism and hence `Δ(U) → Δ(1)` is an
  isomorphism. That is, `Δ` is not faithful.
]

*Why this collapses Δ.* `Δ(X) = (X×B → B)` shows `X` only through `B`'s support (fiber `0`); it is blind
to fiber `1`. So two sections of a `Y` that agree over `0` but differ over `1` become indistinguishable:

#figure(
  scale(x: 130%, y: 130%, reflow: true, cetz.canvas(length: 1cm, {
    import cetz.draw: *
    rect((-0.6, -0.5), (0.6, 2.35), fill: imgc.lighten(90%),
      stroke: (paint: imgc, dash: "dashed", thickness: 0.5pt))
    content((0, 2.62), text(7pt, fill: imgc)[Δ sees only this (`B`'s support)])
    line((-0.7, 0), (3.1, 0), stroke: 0.5pt + luma(150))
    content((0, -0.34), text(7pt, fill: luma(110))[0])
    content((2.4, -0.34), text(7pt, fill: luma(110))[1])
    let yd(x, y, lbl) = { circle((x, y), radius: 0.1, fill: white, stroke: 0.6pt + black); content((x, y), text(7pt)[#lbl]) }
    line((0, 0.9), (2.4, 0.9), stroke: 1.1pt + prec)
    line((0, 0.9), (2.4, 1.7), stroke: 1.1pt + rgb("#dd6b20"))
    yd(0, 0.9, [a]); yd(0, 1.7, [b])
    yd(2.4, 0.9, [a]); yd(2.4, 1.7, [b])
    content((1.15, 0.66), text(7pt, fill: prec)[$f:#h(0.2em) 0↦a,#h(0.3em) 1↦a$])
    content((1.7, 1.48), text(7pt, fill: rgb("#dd6b20"))[$g:#h(0.2em) 0↦a,#h(0.3em) 1↦b$])
  })),
  caption: [`Y` has fibers `{a,b}` over each point. Sections `f` (#text(fill: prec)[green]) and `g`
  (#text(fill: rgb("#dd6b20"))[orange]) _agree_ over `0` (both pick `a`) and _differ_ over `1`. Slicing
  over `B` looks through the shaded column (`B`'s support) only, so Δ records just `f(0)=g(0)=a`:
  `Δf = Δg` though `f ≠ g`. So Δ is *not faithful* exactly when `B` is not well-supported.],
)

#punch[
  Slicing over `B` = "looking at the whole category through `B`." If `B` exists only over part of the
  world, everything outside `B`'s support is invisible — distinct subobjects (`U` vs `1`) and distinct
  maps (`f` vs `g`) that differ only out there get identified. That is why capitalization slices only
  over *well-supported* `B` (`B→1` a cover, `B` touches _every_ point): only then does Δ's "look through
  `B`" miss nothing, and the embedding loses no morphism.
]

= Well-pointed #h(0.4em) (§1.523)

#definition("Well-pointed")[
  `A` is *well-pointed* if the global points `1 → A` *jointly cover* `A`: the only subobject containing
  every point `1 → A` is `A` itself. Elementary form: a mono `A′ ↣ A` through which _every_ point
  `1 → A` factors must be an isomorphism.
]

Set intuition: "`A` is covered by its elements" — nothing in `A` is invisible to the points. (Distinct
from but cousin to "1 is a separator" = `Hom(1,−)` faithful.)

= Which categories are well-pointed

#table(
  columns: (auto, auto, auto, 1fr),
  table.header(
    table.cell(fill: subc.lighten(86%))[*Category*], table.cell(fill: subc.lighten(86%))[*WP?*],
    table.cell(fill: subc.lighten(86%))[*A point `1 → A` is…*], table.cell(fill: subc.lighten(86%))[*Why / witness*]),
  [#smallcaps[Set], FinSet], [#yes all], [an element],
    [a subset with every element _is_ `A`. The canonical well-pointed topos.],
  [Grp], [#no], [hom from trivial group ⇒ identity only],
    [zero object (`1≅0`); point lands in trivial subgroup. `ℤ/2`: only point hits `0`.],
  [Ab, Vect#sub[k], R-Mod, Mon], [#no], [the zero/identity element], [zero object ⇒ point blind to all but `0`.],
  [Set#sub[\*] (pointed sets)], [#no], [the basepoint], [zero object = basepoint.],
  [Ring/CRing (unital)], [#no], [hom from zero ring ⇒ forces `1=0`], [nontrivial rings have *no points at all*.],
  [G-Set], [#no], [a *fixed point* (`g·a=a` ∀g)], [`A^G` rarely covers; free action has none. _A topos, yet not WP._],
  [Presheaves `Set^{Cᵒᵖ}`], [#no], [a *global section*], [global sections miss local data.],
  [Sheaves `Sh(X)`], [#no], [a global section], [non-constant sheaf's stalks unreached.],
)

*Three ways to fail, one to succeed:*
+ *Zero object* (`1≅0`) → only point is identity/zero (Grp, Ab, Vect, Mod, Mon, Set\*).
+ *Terminal forces triviality* → nontrivial objects have _no_ points (Ring).
+ *Points = invariant/global data* missing local structure (G-Set fixed points, sheaf/presheaf global sections).

Succeeds when points _are_ the elements and elements separate everything: *Set* + well-pointed topoi.

= Well-supported vs well-pointed: capital #h(0.4em) (§1.525)

§3–§4 are about *well-pointed* objects. The opposite gap — objects that are *well-supported* yet *not*
well-pointed — is what capitalization repairs, and naming the categories without that gap is §1.525.

#definition("Capital (§1.525)")[
  A pre-regular category is *capital* if *every well-supported object is well-pointed*. Equivalently
  (§1.526), the *terminator $1$ is projective* — and then `Γ = Hom(1,−)` is a representation of
  pre-regular categories.
]

*Is "capital" standard terminology?* No. It is Freyd & Scedrov's own coinage, like _logos_, _allegory_,
_tabular_, _terminator_; it is not used with this meaning elsewhere. The standard names for the same
property are "$1$ is (regular-)projective", "$1$ is a projective generator", or "`Γ = Hom(1,−)` preserves
covers". Read the word as *rich in points*: `Γ` is the points / global-sections functor, and a category
is *capital* when every supported object is reached by its points. (Freyd writes the capitalization with
an underline, `A̲`; the name attaches to the process of enriching `A` with points, not to capital letters.)

== Two `ℤ/2`'s — and each *as a category*

The `ℤ/2` that is _not projective_ in `Ab` (a *group*) and the `ℤ/2`-_set_ that is _not well-pointed_ in
`G`-Set (a *set with an action*) share the carrier `{0,1}`, but they are different objects — and, viewed as
categories, different categories. Write the two elements of `ℤ/2` as `id` and `σ` (`σ` the generator,
`σσ = id`; additively `id = 0`, `σ = 1`).

A `ℤ/2`-set is not _itself_ a category — it is a set with an action, equivalently a functor from the one-object category of `ℤ/2` to `Set`.
To turn either `ℤ/2` _into_ a category:

#table(
  columns: (auto, auto, 1fr),
  table.header(
    table.cell(fill: subc.lighten(86%))[*view*], table.cell(fill: subc.lighten(86%))[*objects*],
    table.cell(fill: subc.lighten(86%))[*morphisms*]),
  [the *group* `ℤ/2` as a one-object category], [*one*, `∗`], [`{id, σ}`; `σ` is a *self*-iso `∗→∗`, `σσ = id`],
  [the *swap set* as action groupoid `{0,1}//ℤ/2`], [*two*, `0` and `1`],
    [`id₀, id₁`, and an iso `σ : 0 → 1`, `σ : 1 → 0` (`σ` swaps), `σσ = id`],
)

In the action groupoid a morphism `a → b` is a group element `g` with `g·a = b`; since `σ` swaps `0↔1` it
gives the iso `0 ≅ 1`, while each object's only endomorphism is its identity. (The swap is translation by
`σ` — `ℤ/2` acting on its _own_ underlying set, the regular action — which is why this groupoid is a
torsor.)

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let idc = luma(120)
    let loop(c, ang, col, lbl) = {
      let a = ang * 1deg
      let dx = calc.cos(a); let dy = calc.sin(a)
      let px = -dy;         let py = dx
      let cx = c.at(0);     let cy = c.at(1)
      let bx = cx + 0.10*dx; let by = cy + 0.10*dy
      let s  = (bx + 0.13*px, by + 0.13*py)
      let e  = (bx - 0.13*px, by - 0.13*py)
      let c1 = (cx + 1.4*dx + 0.55*px, cy + 1.4*dy + 0.55*py)
      let c2 = (cx + 1.4*dx - 0.55*px, cy + 1.4*dy - 0.55*py)
      bezier(s, e, c1, c2, stroke: 1pt + col, mark: (end: ">"))
      content((cx + 1.85*dx, cy + 1.85*dy), text(9.5pt, fill: col)[#lbl])
    }
    let node(p, lbl) = {
      circle(p, radius: 0.38, fill: rgb("#eef3fb"), stroke: 0.8pt + subc)
      content(p, text(9.5pt)[#lbl])
    }
    // LEFT: the group ℤ/2 as one-object category — one object, a self-iso σ
    content((0, 2.7), text(10pt, weight: "bold", fill: subc)[the GROUP $ZZ\/2$ #h(0.2em) (one object)])
    let O = (0, 0)
    loop(O, 90,  idc,  [id])
    loop(O, 270, imgc, [$sigma$])
    circle(O, radius: 0.12, fill: black)
    content((0, -0.5), text(9.5pt)[$ast$])
    content((0, -1.95), text(8pt)[*one* object, a *self*-iso ($sigma sigma = $ id)])
    content((0, -2.45), text(7.5pt, fill: luma(95))[not contractible])
    // divider
    line((3.3, -2.6), (3.3, 2.6), stroke: (paint: luma(190), dash: "dashed", thickness: 0.5pt))
    // RIGHT: the swap set as action groupoid — two objects, an iso between them
    let cx = 6.8
    content((cx, 2.7), text(10pt, weight: "bold", fill: subc)[the swap $ZZ\/2$-SET (action groupoid)])
    bezier((cx - 0.76, 0.15), (cx + 0.76, 0.15), (cx - 0.5, 0.95), (cx + 0.5, 0.95),
           stroke: 1pt + imgc, mark: (end: ">"))
    content((cx, 1.12), text(9pt, fill: imgc)[$sigma$])
    bezier((cx + 0.76, -0.15), (cx - 0.76, -0.15), (cx + 0.5, -0.95), (cx - 0.5, -0.95),
           stroke: 1pt + imgc, mark: (end: ">"))
    content((cx, -1.18), text(9pt, fill: imgc)[$sigma$])
    node((cx - 1.12, 0), [$0$]); node((cx + 1.12, 0), [$1$])
    content((cx, -1.95), text(8pt)[*two* objects, an iso $0 tilde.equiv 1$])
    content((cx, -2.45), text(7.5pt, fill: luma(95))[contractible ($tilde.equiv$ a point); a torsor])
  }),
  caption: [Each `ℤ/2` _as a category_. *Left:* the group `ℤ/2` as a one-object category — *one* object `∗` with a *self*-iso
  `σ` (`σσ = id`); a self-loop encodes a group element, so it is not contractible. *Right:* the swap
  `ℤ/2`-set as its action groupoid `{0,1}//ℤ/2` — *two* objects `0, 1` with an iso `σ` *between* them; an iso
  between distinct objects only makes them isomorphic, so it collapses to a point. _(This depicts the
  category, not a commutative diagram: `σ ≠ id`, though both run `∗ → ∗`.)_],
)

*One object or two? Two.* "One object with a self-iso" is the _group_ as a one-object category, a different
category: a self-loop `σ : ∗ → ∗` encodes a group element, so the object's automorphism group is `ℤ/2`, and
it is not contractible (its single object has a nontrivial automorphism). An iso `0 → 1` between _distinct_
objects only says they are isomorphic, and
that groupoid collapses to a point.

*Used in the next subsections.* A fixed point of the action is an object with a nontrivial *self*-iso (`g·a = a`). The
swap has none, so no object of its action groupoid carries a self-iso — exactly why it is *two* objects, not
one. (And in `Ab` the group `ℤ/2` has its single point trapped at `id = 0`; in `G`-Set the swap set has no
point at all.)

== A well-supported object that is *not* well-pointed

Recall *well-supported* = `A → 1` is a cover, and *well-pointed* = the points `1 → A` jointly cover `A`. A
*non*-capital category has an object with the first but not the second. Three witnesses:

#callout(imgc)[
  *Finite witness — a $ZZ\/2$-set with no fixed point.* In `G`-Set with `G = ℤ/2 = {e, σ}`, take
  `A = {0,1}` with `σ` acting by *swap* (`σ·0 = 1`, `σ·1 = 0`); the terminal `1 = {∗}` carries the trivial
  action.
  - *Well-supported:* `A → 1` is surjective, hence a cover. #h(0.3em) #yes
  - *Not well-pointed:* a point `1 → A` is equivariant, so its value must be a *fixed point* of `A`; the
    swap has none, so `Hom(1, A) = ∅`. With no points, the smallest subobject containing every point is
    `∅ ⊊ A`. #h(0.3em) #no
  So `A` surjects onto `1`, yet its points see nothing of it. `G`-Set is a topos, *yet not capital*.
]

*Why can't you just pick `0` or `1`?* You _can_ pick an element of the underlying set — but the result is a
bare function `∗ ↦ 0`, not a `G`-set morphism. A point `1 → A` must be *equivariant* (`f(g·x) = g·f(x)`),
and the terminal `1 = {∗}` carries the *trivial* action (`σ·∗ = ∗`). So equivariance forces `f(∗) = σ·f(∗)`
— the chosen element must be *fixed*. Take `f(∗) = 0`: then `f(σ·∗) = f(∗) = 0`, but `σ·f(∗) = σ·0 = 1`, so
it would need `0 = 1`. Picking `1` fails the same way; the swap fixes nothing, so no choice is equivariant
and `Hom(1, A) = ∅` — exactly the `Ab` pattern, where a bare element-choice fails to be a homomorphism.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let idc = luma(140)
    let nodefill = rgb("#eef3fb")
    // object 1 = {∗}, σ acts trivially
    content((0, 1.55), text(8pt, fill: luma(80))[object $1$ (one point $ast$), #h(0.2em) $sigma$ trivial])
    let st = (0, 0)
    circle(st, radius: 0.09, fill: black)
    content((-0.4, 0), text(9pt)[$ast$])
    bezier((-0.12, 0.07), (0.12, 0.07), (-0.45, 0.9), (0.45, 0.9), stroke: 0.7pt + idc, mark: (end: ">"))
    content((0, 1.05), text(7.5pt, fill: idc)[$sigma$])
    // object A = swap set, σ swaps 0 ↔ 1
    content((4, 1.55), text(8pt, fill: luma(80))[object $A$: points $0, 1$, #h(0.2em) $sigma$ swaps])
    let n0 = (4, 0.7); let n1 = (4, -0.7)
    circle(n0, radius: 0.32, fill: nodefill, stroke: 0.7pt + subc); content(n0, text(9pt)[$0$])
    circle(n1, radius: 0.32, fill: nodefill, stroke: 0.7pt + subc); content(n1, text(9pt)[$1$])
    bezier((4.30, 0.52), (4.30, -0.52), (4.95, 0.42), (4.95, -0.42), stroke: 1pt + imgc, mark: (end: ">"))
    bezier((3.70, -0.52), (3.70, 0.52), (3.05, -0.42), (3.05, 0.42), stroke: 1pt + imgc, mark: (end: ">"))
    content((5.18, 0), text(8pt, fill: imgc)[$sigma$])
    content((2.82, 0), text(8pt, fill: imgc)[$sigma$])
    // candidate point f : ∗ ↦ 0
    line((0.22, 0.06), (3.66, 0.62), stroke: 1pt + subc, mark: (end: ">"))
    content((1.78, 0.62), text(8.5pt, fill: subc)[$f : ast arrow.r.bar 0$])
    // the clash
    content((2.0, -1.8),
      text(8.5pt)[equivariance needs $f(sigma dot ast) = sigma dot f(ast)$, #h(0.3em) i.e. $0 = 1$ #h(0.3em) #no])
  }),
  caption: [Why no element is a point of the swap set. The candidate `f : ∗ ↦ 0` is a function but not a
  `G`-map: `1 = {∗}` has the trivial action (`σ·∗ = ∗`), so `f(σ·∗) = f(∗) = 0`, whereas `σ·f(∗) = σ·0 = 1`;
  equivariance would force `0 = 1`. Picking `1` fails identically — the swap fixes nothing, so `Hom(1,A)=∅`.],
)

Two more, one line each:
- *`Ab` / `Grp`:* any nonzero object, e.g. `ℤ/2`. It surjects onto the terminal (the zero group), so it is
  *well-supported*; but the only point `1 → ℤ/2` is `0`, and `{0} ⊊ ℤ/2` already holds every point — *not*
  well-pointed. (Here `1 ≅ 0`: the zero object traps the point.)
- *Sheaves:* a nontrivial `ℤ/2`-torsor on the circle (the connected double cover) is locally inhabited, so
  `F → 1` is a cover (*well-supported*), but it has *no global section at all* — *not* well-pointed. The
  geometric face of the same phenomenon.

#punch[
  Capitalization adjoins the missing points: for each well-supported `A` that is not well-pointed it adds a
  point `1 → A` in a larger `A*` (the slice over `A`, §1.546), repeating until *every* well-supported object
  is well-pointed — i.e. until the category is *capital*. That is the §1.54 machine the rest of these notes
  build toward.
]

== Is the terminator `1` always projective? No

A natural guess: `1` is always projective, since a cover `A ↠ 1` ought to split. It does in `Ab` — your
`ℤ/2 → 1` splits by the zero map `0 → ℤ/2` — but that is special, not general.

#definition("When 1 is projective")[
  `1` is *projective* ⟺ every cover `A ↠ 1` has a section `1 → A` ⟺ *every well-supported object has a
  point*. Capital (§1.525) supplies this (`capital_implies_one_projective` in `S1_52.lean`). It is *not*
  automatic.
]

#table(
  columns: (auto, auto, 1fr),
  table.header(
    table.cell(fill: subc.lighten(86%))[*Category*], table.cell(fill: subc.lighten(86%))[*`1` projective?*],
    table.cell(fill: subc.lighten(86%))[*Why*]),
  [`Ab`, `Grp`], [#yes], [zero object: the canonical point `0 → A` (your `0 → ℤ/2`) splits `A → 1`.],
  [#smallcaps[Set]], [#yes], [`A → 1` a cover ⟹ `A` nonempty ⟹ a point to choose (#smallcaps[ac]).],
  [`Ring`, `CRing`], [#no], [terminal `1 =` zero ring (no zero _object_); a nontrivial `R` is well-supported but
    `Hom(1, R) = ∅` — a hom out of the zero ring forces `1 = 0`.],
  [`G`-Set], [#no], [the swap `ℤ/2`-set is well-supported but has no fixed point ⟹ no point `1 → A`.],
  [Sheaves], [#no], [a torsor with no global section: well-supported, but `Γ = ∅`.],
)

#punch[
  If `1` were _always_ projective, capitalization would do nothing. Its whole job (§1.54) is to enlarge a
  non-capital category until every well-supported object acquires a point — i.e. until `1` becomes
  projective. Your `Ab` example works only because the terminal there is a _zero_ object.
]

= "Set-like, and structure breaks it" — sharpened

The instinct (WP = Set-like; add structure, lose it) is right, with one correction: it's not _any_
structure — it's structure that *constrains maps out of* `1` so points stop reaching every element. In
Set, `1` is a _bare_ point (maps anywhere). Structure replaces `1` with a _specific_ one-element object
whose maps out are constrained:
- *a marked element* (identity/zero/basepoint) traps the point;
- *operations/morphisms tying elements together* (action, topology, restriction maps, an arrow) ⇒
  points = the globally-coherent/invariant part, missing local structure.

But *parallel* structure (no binding operation) stays WP:

```text
Set × Set:  point of (A,B) is (a,b) ∈ A×B            → covers.             ✓ WP
Set^→ (one arrow f:X→Y): point is x∈X (f(x) forced)  → misses Y∖im(f).    ✗ not WP
```

Same two sets — adding _a morphism between them_ breaks it. Breaker = *binding* structure.

#callout(subc)[
  *Clean statement.* WP ⟺ `1` is a bare point hitting every element (`1` is a generator/separator by
  covers). Programmer view: an object is WP iff `obj.points()` exposes everything; binding structure
  adds *hidden state* (a forced identity, a fixed-point requirement, local data) points can't see.
]

= Is it useful / does modern math have it?

It's a *characterization*, not a property you hope for — it pins down _when point-wise reasoning is
valid_. Its narrowness (as stated, *`1` alone* generates) is informative: it's the boundary of
"Set-like." Weaken to "*some* family generates" and it's ubiquitous:

#table(
  columns: (auto, auto, 1fr),
  table.header(
    table.cell(fill: subc.lighten(86%))[*Modern name*], table.cell(fill: subc.lighten(86%))[*Where*],
    table.cell(fill: subc.lighten(86%))[*Meaning*]),
  [*Well-pointed topos*], [Lawvere *ETCS*, categorical set theory], [`1` generator + 2-valued + nontrivial ⇒ a model of set theory],
  [*Generator / separator*], [module/abelian/Grothendieck categories], [`Hom(G,−)` faithful; Grothendieck cats _defined_ by having one],
  [*Enough points*], [topos/locale theory], [points detect everything; some topoi have *none*],
  [*Enough global sections*], [algebraic geometry], [ampleness/affineness — `Γ=Hom(1,−)` sees the sheaf],
  [*Concretizable*], [general cat theory], [faithful functor to Set; Freyd: `Ho(Top)` is *not*],
)

= "Just embed into Set" — three problems

+ *Sometimes impossible*: Freyd, _"Homotopy is not concrete"_ — `Ho(Top)` has no faithful functor to Set.
+ *Faithful isn't enough*: transporting a proof needs the functor to *preserve* the structure chased
  (finite limits, monos, images, exactness = *exact/regular*) _and_ *reflect* it (*conservative*). Bare
  faithfulness gives neither.
+ *Building such a functor is the theorem*: Freyd–Mitchell (abelian → R-Mod → Set), Barr (regular →
  Set). Capitalization is the machine that builds it. Not free.

*Concrete vs abstract.* `Grp` _comes with_ a forgetful `U:Grp→Set` that is faithful, limit-preserving,
conservative — so element-chasing in groups is free. The problem is *abstract* categories (abstract
abelian/regular/topos) with *no* underlying-set functor; you must construct one.

*Yoneda alternative.* `A ↪ [Aᵒᵖ,Set]` always, fully faithfully — but into *presheaves* (not WP), giving
*generalized* elements (maps from representables, the functor-of-points), not honest points.

= Why Yoneda isn't enough

Two reasons, one shallow, one deep:
- *Shallow*: target is presheaves, not well-pointed ⇒ generalized elements, not points from `1`.
- *Deep*: Yoneda is *continuous* (preserves & reflects limits) but *destroys colimits/exactness*. In
  `Ab`: `ℤ ↠ ℤ/2` is epi, but `Hom(−,ℤ) → Hom(−,ℤ/2)` is *not* epi in presheaves (a map `X→ℤ/2` needn't
  lift to `X→ℤ`). So an exact sequence need not stay exact ⇒ a chase in presheaves proves nothing about
  `A`. Yoneda is only _half_-exact.

#table(
  columns: (1fr, auto, auto, auto, auto),
  table.header(
    table.cell(fill: subc.lighten(86%))[], table.cell(fill: subc.lighten(86%))[*full+faithful*],
    table.cell(fill: subc.lighten(86%))[*limits*], table.cell(fill: subc.lighten(86%))[*covers/colimits*],
    table.cell(fill: subc.lighten(86%))[*into well-pointed Set*]),
  [Yoneda (free)], [#yes], [#yes], [#no], [#no (presheaves)],
  [Freyd–Mitchell / Barr (theorem)], [#yes], [#yes], [#yes], [#yes],
)

The two checkmarks Yoneda lacks — preserving covers, reaching honest points — are exactly the embedding
theorems' content.

= Why capitalization preserves exactness when Yoneda doesn't

The difference is *how points are added*.
- *Yoneda probes by mapping into objects* (`a ↦ Hom(−,a)`). `Hom(X,−)` is intrinsically
  limit-preserving / colimit-destroying ⇒ left-exact only; and it *leaves* the regular world for presheaves.
- *Capitalization stays inside the regular world and adds points by slicing*: each rung is the pullback
  functor `Δ : A → A/B`, `X ↦ (X×B → B)` (base change along `B→1`).

#callout(prec)[
  The decisive fact is the *defining axiom of a regular category* (§1.52): *"pullbacks transfer covers"*
  — covers are stable under pullback. So the slice functor, _being a pullback_, *automatically preserves
  covers*, and (being a pullback) preserves finite limits. Finite-limits + covers = a *representation of
  regular categories* ⇒ preserves images and *exactness*. Faithful when `B` is well-supported (§1.532).
]

Capitalization is a transfinite tower `A → A/B → (A/B)/B′ → ⋯` of such rungs, each exact + faithful, with
colimit `A ⊂ A*` an *exact faithful* embedding that makes well-supported objects well-pointed. Exactness
is *inherited from pullback-stability of covers* — the very axiom that makes `A` regular.

#punch[
  Yoneda probes with `Hom` (left-exact, leaves the world); capitalization enlarges with *pullback*
  (cover-stable by the regularity axiom, fully exact, stays in the world). "Covers pull back" is exactly
  what Hom-based Yoneda never uses and what makes slice-based point-adding exact.
]

#text(9pt)[(Repo: `Slice.lean` Σ reflects covers; `SliceRegular.lean` slice is pre-regular;
`RelativeCapitalization.lean` the per-`B` rung `A→A/B` as a faithful, point-acquiring CapStep.)]

= The construction concretely: Δ, rungs, "different B", faithful-not-full

How capitalization actually adds the points (§1.525–§1.547), with the Set pictures.

== Two stacked indexings — "rung" vs "layer"
- *Rung* = one slice step `Aα ──Δ──▶ Aα/B`. Inside one _relative capitalization_ (§1.546) you take a
  transfinite ascending union of rungs `A = A₀ ⊂ A₁ ⊂ ⋯`, where each rung slices over *the first
  well-supported object `B` not yet pointed* (first w.r.t. a fixed well-order on objects). *B changes
  every rung.* When the layer closes, every well-supported object of the _original_ `A` has its points.
- *Layer* = one relative capitalization. The outer tower `A ⊂ A* ⊂ A** ⊂ ⋯` (§1.545) stacks layers,
  because `A*` has *new* well-supported objects (built from the new points) that themselves need points.
  The union `A̲` of the ω-tower is *capital* (every well-supported object is well-pointed).

You do *not* iterate `A/B → (A/B)/B` on one fixed `B`; and nothing shrinks — every step is a faithful
_enlargement_, the towers are ascending unions climbing up to the richest category `A̲`.

== What Δ is (§1.546 names the functor `A →^Δ A/B`)
`Δ : A → A/B`, `X ↦ (X×B ──snd──▶ B)` = *base change along `B→1`*: since `A = A/1`, pulling the object
`X` (i.e. `X→1`) back along the unique `B→1` gives `X×B→B`. Repo: `RelativeCapitalization.lean`
`sliceEmbedObj B C := ⟨prod C B, snd⟩` is exactly `ΔC` (named `sliceEmbed*`, not `Δ`).

In #smallcaps[Hask] (the `Set` model, `B` a fixed type) `Δ` is two one-liners — a slice object over `b`
is a carrier with a structure map `c -> b`, and `Δ` produces the carrier `(x, b)` with `snd`:

```haskell
-- Δ : Set → Set/B   (base change along B → 1; the slice embedding A → A/B)
deltaObj :: (x, b) -> b                      -- on objects:   X ↦ (X×B, snd);  carrier is (x, b)
deltaObj = snd
deltaMor :: (x -> y) -> (x, b) -> (y, b)     -- on morphisms: f ↦ f × id_B,  a map over B
deltaMor f (x, b) = (f x, b)
```

It is a functor (`deltaMor id = id`, `deltaMor (g . f) = deltaMor g . deltaMor f`), *faithful* iff `b` is
inhabited (`B` well-supported), and the generic point of `ΔB` is the diagonal `\b -> (b, b)`.

*Why it adds a point:* in `A/B` the terminal is `(B ═id═▶ B)`; a point of `ΔB = (B×B ─snd→ B)` is a
section of `snd`, and the *diagonal* `δ = ⟨id,id⟩` is one (`δ≫snd = id`). Through `fst`, `δ` _is_ the
identity element of `B` — a "generic point of `B`" that didn't exist in `A`. Base-change functors
preserve finite limits and (regular axiom) covers ⇒ Δ is an exact representation (§1.543).

== Two `A/B`'s: the slice (§1.26) vs the redefinition (§1.544)

#callout(subc)[
  *`X×B` is not in the definition of `A/B`.* §1.26 defines `A/B` as *all arrows into `B`* — in `Set`
  (§1.261) the general object is a `B`-indexed family of fibers `{A_i}`, fibers arbitrary. The bundle
  `ΔX = X×B→B` is just the *constant* family (every fiber `= X`), a thin sub-population of `A/B` produced
  by the *functor* `Δ` — nothing the slice's definition mentions.
]

For capitalization the book *redefines* `A/B` so that `A` is a literal subcategory (§1.544), via the
*inflation* `A′` — products strictified into lists (the free-monoid trick):
- objects of `A′` = finite *lists* `⟨A₁,…,Aₙ⟩` of `A`-objects ("formal products"); the forgetful `A′→A`
  sends a list to a chosen product `A₁×⋯×Aₙ` (`⟨⟩ ↦ 1`). Hom-sets are `A`'s, so `A′ ≃ A`.
- product in `A′` = *list concatenation* — strictly associative, with *strict cancellation*
  `B×A = B×A′ ⟹ A = A′` (drop the prefix).

Then `Δ(X) = ⟨X, B⟩` (append `B`), and the book finally *relabels `Δ`'s image `⟨X,B⟩` as `X` itself*, so
`A ⊆ A/B` on the nose. The lists force injectivity: even when `B` is not well-supported and `B×U ≅ B×1`
*collapses in `A`* (§1.534), the lists `⟨U,B⟩ ≠ ⟨1,B⟩` stay distinct — so `Δ` *separates objects* always,
and *separates morphisms* (is faithful) only when `B` is well-supported.

Pictorially, "inflation" is the general §1.36 move, an instance of the §1.243 *founding* construction —
take a *class* of labels with an *underlying function* to the base, and *borrow the morphisms* from the
base (formalized as `FoundingData` / `inflation` in `S1_35.lean`):

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let gr = luma(140)
    content((-2.7, 2.6), text(11pt, weight: "bold", fill: subc)[\[T\]])
    content((-2.7, 0), text(11pt, weight: "bold")[A])
    // base category A
    let X = (0, 0); let Y = (5, 0)
    circle(X, radius: 0.07, fill: black); content((0, -0.42), text(9pt)[$X$])
    circle(Y, radius: 0.07, fill: black); content((5, -0.42), text(9pt)[$Y$])
    line((0.2, 0), (4.8, 0), mark: (end: ">"), stroke: 1pt)
    content((2.5, 0.3), text(9pt)[$f$])
    // [T]: two labels over X, one over Y
    let X1 = (-0.55, 2.6); let X2 = (0.55, 2.6); let Y1 = (5, 2.6)
    circle(X1, radius: 0.07, fill: subc); content((-0.55, 2.95), text(8.5pt, fill: subc)[$X_1$])
    circle(X2, radius: 0.07, fill: subc); content((0.55, 2.95), text(8.5pt, fill: subc)[$X_2$])
    circle(Y1, radius: 0.07, fill: subc); content((5, 2.95), text(8.5pt, fill: subc)[$Y_1$])
    // u : 𝒞 → |A| (underlying function), dashed, pointing down to each label's base object
    line(X1, (-0.06, 0.18), mark: (end: ">"), stroke: (paint: gr, dash: "dashed", thickness: 0.6pt))
    line(X2, (0.06, 0.18), mark: (end: ">"), stroke: (paint: gr, dash: "dashed", thickness: 0.6pt))
    line(Y1, (5, 0.2), mark: (end: ">"), stroke: (paint: gr, dash: "dashed", thickness: 0.6pt))
    content((1.05, 1.35), text(8pt, fill: luma(95))[$u$])
    content((5.28, 1.3), text(8pt, fill: luma(95))[$u$])
    // a morphism of [T] is BORROWED from A
    line(X1, Y1, mark: (end: ">"), stroke: 0.9pt + subc)
    content((2.5, 2.82), text(8pt, fill: subc)[$f$])
  }),
  caption: [The §1.36 *inflation* `[T]` of `A` — the §1.243 founding with the *most inclusive* predicate
  (`Hom' = ` all proto-morphisms). Objects are *labels* (the class `𝒞 = {X₁, X₂, Y₁}`); the *underlying
  function* `u : 𝒞 → |A|` (dashed) sends each label to its base object — `u X₁ = u X₂ = X`, `u Y₁ = Y`. A
  morphism is *borrowed from `A`*: `Hom_[T](Xᵢ, Y₁) = Hom_A(X, Y) = {f}`, so the *one* arrow `f` serves
  both `X₁→Y₁` and `X₂→Y₁`. Forgetting the labels (`u`) gives back `A`, so `[T] ≃ A`. (In §1.544 the
  labels are lists `⟨A₁,…,Aₙ⟩` and `u` multiplies them out to products.)],
)

== Δ is faithful, *not full* — and that _is_ "slicing adds points"
Set picture, `B = {0,1}` so `Set/B ≅ Set×Set`, `Δ : X ↦ (X,X)`, `f ↦ (f,f)`:
- *Faithful* (loses no morphism): `f ↦ (f,f)` is injective — provided `B` is well-supported
  (`Hom(X,Y) ↪ Hom(X×B,Y)`, `f↦f∘fst`, injective iff `fst` epi iff `B→1` a cover; that's _why_ you only
  slice over well-supported `B`, never over `∅`).
- *Not full* (the slice is strictly bigger): `Hom_{Set/B}(ΔX,ΔY) = Hom(X,Y)^{|B|}`, and `Δ` hits only the
  *diagonal* `Hom(X,Y) ↪ Hom(X,Y)^{|B|}`. Full ⟺ `B ≅ 1`. Capitalization slices over `B ≇ 1`, so Δ is
  _never_ full there.

Minimal witness `Δ1 → ΔY`, `Y={0,1}` — a map over `B` = a section of `ΔY` = one `Y`-value per fiber,
*independently*:

```text
ΔY = (Y×B → B),  fibers  Y | Y          maps Δ1→ΔY :  (0,0) (1,1) | (0,1) (1,0)   = Y² = 4
                       over0  over1                    └ Δ's image ┘ └ NOT in image ┘
                                                     "same both fibers"  "differs per fiber"
```

The 2 off-diagonal maps are *not* `Δh` for any point `h:1→Y` — _and_ they are exactly the *new points* of
`ΔY` (`Y` had 2 points in Set; `ΔY` has `2²=4` in `Set/B`). So "Δ not full" ≡ "slicing added points". *No
zero object is involved* — Set has none (`∅ ≠ {∗}`); the extra freedom is per-fiber independence, not
anything mapping to `0`.

== Different B's "jointly prove something" (§1.547, §1.526)
One `B` gives `B` points; ranging over *all* `B` gives every object points; the union assembles the
capital `A̲`, where `Γ = Hom(1,−) : A̲ → Set` is *exact* (capital ⇒ `1` projective, §1.526). Faithful is
_joint_: the family `T_B : A →^Δ A/B → A̲/B →^Γ Set` (one per `B`) together separates morphisms and
detects every proper subobject — no single `B` suffices. That faithful exact `A ↪ A̲ ─Γ→ Set` is the
representation Yoneda couldn't give. The outer embedding `A ↪ A̲` is itself only *faithful*, not full
(book claims faithful, §1.544) — same faithful-not-full pattern as each rung.
