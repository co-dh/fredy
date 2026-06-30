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
