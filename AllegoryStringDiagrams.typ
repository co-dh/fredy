#import "@preview/cetz:0.3.4"
#let d = cetz.draw

// ==========================================================================
//  String diagrams for Freyd allegories  (Bonchi–Pavlović–Sobociński calculus)
//  Cartesian bicategory of relations = the graphical syntax of an allegory.
// ==========================================================================

#set page(width: 21cm, height: auto, margin: 2cm)
#set text(size: 10.5pt, font: "New Computer Modern")
#set par(justify: true)
#show heading: set text(size: 12pt)

// ---- drawing primitives ---------------------------------------------------
#let W = 1.1pt                       // wire thickness
#let R = 0.075                       // node radius
#let stylize = d.set-style(stroke: (thickness: W))

#let wire(a, b) = d.line(a, b, stroke: (thickness: W))
#let dot(p) = d.circle(p, radius: R, fill: black, stroke: none)

// generator box  m -> n
#let gbox(p, label, w: 1.0, h: 0.7) = {
  let (x, y) = p
  d.rect((x, y - h/2), (x + w, y + h/2), fill: white, stroke: (thickness: W))
  d.content((x + w/2, y), label)
}

// comultiplication / copy  Δ : 1 -> 2   (dot at p, wire in from left, fork right)
#let copy(p, li: 0.7, lo: 0.7, sp: 0.5) = {
  let (x, y) = p
  wire((x - li, y), (x, y))
  d.bezier((x, y), (x + lo, y + sp), (x + lo*0.6, y), (x + lo*0.6, y + sp), stroke: (thickness: W))
  d.bezier((x, y), (x + lo, y - sp), (x + lo*0.6, y), (x + lo*0.6, y - sp), stroke: (thickness: W))
  dot(p)
}
// multiplication / merge  ∇ : 2 -> 1   (mirror of copy)
#let merge(p, li: 0.7, lo: 0.7, sp: 0.5) = {
  let (x, y) = p
  wire((x, y), (x + lo, y))
  d.bezier((x - li, y + sp), (x, y), (x - li*0.6, y + sp), (x - li*0.6, y), stroke: (thickness: W))
  d.bezier((x - li, y - sp), (x, y), (x - li*0.6, y - sp), (x - li*0.6, y), stroke: (thickness: W))
  dot(p)
}
// counit / discard  ! : 1 -> 0
#let discard(p, li: 0.7) = { let (x, y) = p; wire((x - li, y), p); dot(p) }
// unit  ? : 0 -> 1
#let unit(p, lo: 0.7) = { let (x, y) = p; wire(p, (x + lo, y)); dot(p) }

// ==========================================================================
#align(center)[
  #text(15pt)[*String diagrams for Freyd allegories*] \
  #text(9pt)[the graphical calculus of a cartesian bicategory of relations \
  (Bonchi–Pavlović–Sobociński, _Functorial Semantics for Relational Theories_)]
]

#v(2pt)

A string diagram is an arrow of a symmetric monoidal category drawn as a circuit: boxes are
generators, wires carry objects, *left-to-right* juxtaposition is composition `;` and *vertical*
stacking is the monoidal product `⊕`. This is the same reading order as the book's diagram-order
composition `x y` = "first `x` then `y`". An allegory's operations — composition, converse `°`, meet
`∩`, top `⊤` — are all recovered from *one* extra piece of structure on top of the plain monoidal
wires: a *special Frobenius* (co)monoid on every object. Below, black dots are that Frobenius
structure; white boxes are relation generators.

= 1. The generators: the Frobenius structure

Four nodes, all drawn with the same black dot because they form *one* special Frobenius algebra
(the "spider"): any connected diagram of dots collapses to a single node fixed only by its
input/output count.

#align(center, cetz.canvas({
  // copy
  copy((0.7, 0))
  d.content((0.75, -1.15), text(9pt)[copy \ $Delta: 1 -> 2$])
  // discard
  discard((4.2, 0))
  d.content((3.9, -1.15), text(9pt)[discard \ $thin ! : 1 -> 0$])
  // merge
  merge((7.2, 0))
  d.content((7.0, -1.15), text(9pt)[merge \ $nabla: 2 -> 1$])
  // unit
  unit((10.4, 0))
  d.content((10.5, -1.15), text(9pt)[unit \ $? : 0 -> 1$])
}))

In *Rel* these are the *diagonal* relations: `copy` is $x ↦ (x,x)$, `discard` is $x ↦ ✓$ (the map
to a point), `merge = copy°`, `unit = discard°`. `(Δ, !)` is a cocommutative comonoid, `(∇, ?)` a
commutative monoid, and together they satisfy the Frobenius law and the *special* law
`Δ;∇ = id`:

#align(center, cetz.canvas({
  // Frobenius:  merge;copy  =  (id⊕unit… )  spider — draw  ∇ then Δ  = Δ⊕id ; id⊕∇ style
  // left: merge then copy
  merge((1.0, 0), lo: 0.55)
  copy((1.55, 0), li: 0.0, lo: 0.55)
  d.content((2.9, 0), $=$)
  // middle: the through-spider (2->2)
  wire((3.5, 0.5), (3.9, 0.5)); wire((3.5, -0.5), (3.9, -0.5))
  d.bezier((3.9, 0.5), (4.4, 0), (4.2, 0.5), (4.2, 0), stroke: (thickness: W))
  d.bezier((3.9, -0.5), (4.4, 0), (4.2, -0.5), (4.2, 0), stroke: (thickness: W))
  dot((4.4, 0))
  d.bezier((4.4, 0), (4.9, 0.5), (4.6, 0), (4.6, 0.5), stroke: (thickness: W))
  d.bezier((4.4, 0), (4.9, -0.5), (4.6, 0), (4.6, -0.5), stroke: (thickness: W))
  wire((4.9, 0.5), (5.3, 0.5)); wire((4.9, -0.5), (5.3, -0.5))
  d.content((6.0, 0), $=$)
  // right: copy then merge
  copy((6.6, 0), li: 0.55, lo: 0.0)
  merge((7.15, 0), li: 0.55)
  // special law
  d.content((9.2, 0), $ #text(9pt)[special:] $)
  copy((10.2, 0), li: 0.45, lo: 0.0, sp: 0.45)
  merge((10.65, 0), lo: 0.45, sp: 0.45)
  d.content((11.5, 0), $=$)
  wire((11.8, 0), (12.7, 0))
}))

= 2. Identity, composition, monoidal product

A relation `R : m → n` is a labelled box. The identity is a bare wire; `R ; S` (first `R` then `S`)
is horizontal juxtaposition; `R ⊕ S` is vertical stacking.

#align(center, cetz.canvas({
  // identity
  wire((0,0),(1.2,0)); d.content((0.6,-0.7), text(9pt)[$id = " "$ bare wire])
  // R;S
  wire((3,0),(3.5,0)); gbox((3.5,0), $R$, w: 0.8); wire((4.3,0),(4.8,0)); gbox((4.8,0), $S$, w: 0.8); wire((5.6,0),(6.1,0))
  d.content((4.55,-0.7), text(9pt)[$R semi S$])
  // R⊕S
  wire((8,0.5),(8.4,0.5)); gbox((8.4,0.5), $R$, w: 0.8); wire((9.2,0.5),(9.6,0.5))
  wire((8,-0.5),(8.4,-0.5)); gbox((8.4,-0.5), $S$, w: 0.8); wire((9.2,-0.5),(9.6,-0.5))
  d.content((8.8,-1.15), text(9pt)[$R plus.o S$])
}))

= 3. Converse `R°` — bending the wire

The Frobenius structure makes the category *compact closed*: every wire can be bent back with a
`cup` (`? ; Δ`, an "unfork") and a `cap` (`∇ ; !`). Converse is then *free* — you just bend both of
`R`'s wires around, so what was an input is read as an output:

#align(center, cetz.canvas({
  d.content((-1.6, 0), $R^degree :=$)
  // input wire bottom-left
  wire((-0.8, -0.7), (0.2, -0.7))
  // cap on left: bend from (0.2,-0.7) up to R's left port (1.0, 0.7)
  d.bezier((0.2, -0.7), (1.0, 0.7), (0.9, -0.7), (0.4, 0.7), stroke: (thickness: W))
  gbox((1.0, 0.7), $R$, w: 0.9)
  // cup on right: bend from R's right port (1.9,0.7) down to (2.7,-0.7)
  d.bezier((1.9, 0.7), (2.7, -0.7), (2.5, 0.7), (2.0, -0.7), stroke: (thickness: W))
  wire((2.7, -0.7), (3.7, -0.7))
  // in Rel:  x R° y  <=>  y R x
  d.content((6.0, 0), text(9pt)[in *Rel*: #h(3pt) $x thin R^degree thin y #h(2pt) <==> #h(2pt) y thin R thin x$])
}))

= 4. Meet `R ∩ S` — the convolution (copy · pair · merge)

Intersection is *not* a new generator: it is `Δ ; (R ⊕ S) ; ∇`. Copy the input, run `R` and `S` on
the two copies, then merge — the merge forces the two outputs to *coincide*, i.e. demands both
`x R y` *and* `x S y`. This is why "everything in parallel is conjunction": a signal flows through
*all* vertical branches at once (a *wave*).

#align(center, cetz.canvas({
  d.content((-1.5, 0), $R inter S :=$)
  copy((0.2, 0), li: 0.5, lo: 0.6, sp: 0.6)
  gbox((0.8, 0.6), $R$, w: 0.9); gbox((0.8, -0.6), $S$, w: 0.9)
  wire((1.7, 0.6), (2.1, 0.6)); wire((1.7, -0.6), (2.1, -0.6))
  merge((2.7, 0), li: 0.6, lo: 0.5, sp: 0.6)
}))

The unit of `∩` is the *top* relation `⊤ = ! ; ?` (discard everything, then create everything —
the all-pairs relation):

#align(center, cetz.canvas({
  d.content((-1.2, 0), $top :=$)
  discard((0.4, 0), li: 0.6)
  unit((1.4, 0), lo: 0.6)
}))

With `;`, `°`, `∩`, `⊤` in hand, the *modular law* `R S ∩ T ≤ R(S ∩ R°T)` is a *derivable*
theorem of this calculus — so a plain string diagram over these generators is exactly a term of a
(unitary, tabular) *allegory*.

= 5. When is a relation a map? — the defining inequations

Every relation is only a *lax* comonoid homomorphism: copying then applying is ≥ applying then
copying. Equality on the two laws below says precisely *single-valued* and *total* — i.e. `R` is
the graph of a function (a `map`, the arrows the book calls covers/maps).

#align(center, cetz.canvas({
  // single-valued:  R;Δ  ≤  Δ;(R⊕R)
  wire((0,0),(0.4,0)); gbox((0.4,0), $R$, w: 0.8); copy((1.2,0), li: 0.0, lo: 0.6, sp: 0.45)
  d.content((2.3,0), $lt.eq.slant$)
  copy((3.1,0), li: 0.4, lo: 0.5, sp: 0.55)
  gbox((3.6,0.55), $R$, w: 0.8); gbox((3.6,-0.55), $R$, w: 0.8)
  wire((4.4,0.55),(4.8,0.55)); wire((4.4,-0.55),(4.8,-0.55))
  d.content((2.4,-1.3), text(9pt)[single-valued (= at equality)])
  // total:  R;!  ≤  !
  wire((7,0),(7.4,0)); gbox((7.4,0), $R$, w: 0.8); discard((8.7,0), li: 0.5)
  d.content((9.4,0), $lt.eq.slant$)
  discard((10.3,0), li: 0.9)
  d.content((8.8,-1.3), text(9pt)[total (= at equality)])
}))

= 6. What *cannot* be drawn: union `∪` and empty `⊥`

Tarski's calculus of relations has *two* families of operations:

#align(center, text(9pt)[
  #box(inset: 6pt, stroke: 0.5pt)[
    conjunctive (drawable): #h(4pt) $R semi S quad R^degree quad R inter S quad top quad id$ \
    #v(2pt)
    disjunctive (*not* drawable): #h(4pt) $R union S quad bot$
  ]
])

Intersection sneaks in through the Frobenius structure because it reuses the *same* monoidal
product `⊕` (copy on one product, merge on the same one). Union is a *genuinely second* monoidal
product: in *Rel* it is the *biproduct* `⊕` (disjoint union of objects, block-diagonal on arrows),
over which `;` distributes — making *Rel* a *rig category* with two tensors. A string diagram is
the language of *one* monoidal category, so it has no room to express the second product. Formally,
each hom of a cartesian bicategory of relations is only a *meet-semilattice* — there is provably no
`∪` and no `⊥`.

The intuition: inside a circuit a signal is a *wave*, passing through *all* vertical branches
simultaneously → conjunction. Union needs a signal that is a *particle*, taking *one* branch →
choice. You cannot have both on one sheet. The fix (Bonchi–Di Giorgio–Santamaria, *tape diagrams*)
is a second layer — "string diagrams of string diagrams": whole circuits `R`, `S` are wrapped in a
*tape* that forks, and a particle flows through exactly one:

#align(center, cetz.canvas({
  d.content((-1.5, 0), $R union S :=$)
  // left fork ▷ of the tape
  let tapeCol = rgb("#f4c9c9")
  // upper tape segment holding R
  d.rect((0.6, 0.25), (2.4, 1.05), radius: 0.12, fill: tapeCol, stroke: (thickness: 0.8pt, paint: rgb("#c25b5b")))
  gbox((1.15, 0.65), $R$, w: 0.7, h: 0.45)
  // lower tape segment holding S
  d.rect((0.6, -1.05), (2.4, -0.25), radius: 0.12, fill: tapeCol, stroke: (thickness: 0.8pt, paint: rgb("#c25b5b")))
  gbox((1.15, -0.65), $S$, w: 0.7, h: 0.45)
  // fork wires (single wire in, splits to the two tapes) ▷
  wire((-0.6, 0), (0.1, 0))
  d.bezier((0.1, 0), (0.6, 0.65), (0.45, 0), (0.45, 0.65), stroke: (thickness: W))
  d.bezier((0.1, 0), (0.6, -0.65), (0.45, 0), (0.45, -0.65), stroke: (thickness: W))
  // join wires ◁ on the right
  d.bezier((2.4, 0.65), (2.9, 0), (2.55, 0.65), (2.55, 0), stroke: (thickness: W))
  d.bezier((2.4, -0.65), (2.9, 0), (2.55, -0.65), (2.55, 0), stroke: (thickness: W))
  wire((2.9, 0), (3.6, 0))
  d.content((6.2, 0), text(9pt)[a *tape*: the particle takes \ the $R$ branch #underline[or] the $S$ branch])
}))

Everything above the pink tapes is an ordinary allegory (an `∩`-calculus, drawable). Adding the
tapes gives a *distributive* allegory (`∪`, `⊥`). Higher still — *division* allegories (residuals
`R\\S`, right adjoints to `;`) and *power* allegories (the `Λ` power-object transpose) — are not
finite string-diagram terms at all: they are adjoints / closed structure, not composites of the
generators.
